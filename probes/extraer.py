"""Extracción de activaciones para el piloto de adecuación (faithfulness) NL ↔ Lean 4.

Para cada fila de CriticLeanBench corre hasta cuatro prompts por el modelo congelado:
  - «completo»:         enunciado NL + Lean + pregunta
  - «solo_lean»:        Lean + pregunta (sin el enunciado NL)
  - «solo_nl»:          enunciado NL + pregunta (sin el bloque de Lean)
  - «nl_desemparejado»: el Lean de la fila con el NL de otra fila (desarreglo con semilla 0
                        dentro de quintiles de longitud del NL; ninguna fila recibe su propio NL
                        ni un NL textualmente igual). El manifiesto guarda qué NL recibió cada fila.
y guarda el residual stream de todas las capas (embeddings + cada bloque) en dos posiciones:
  - «ultimo»:     último token del prompt (justo antes de la respuesta)
  - «media_lean»: promedio sobre los tokens del bloque Lean
                  (en «solo_nl», que no tiene Lean, la segunda posición es «media_nl»:
                  promedio sobre los tokens del enunciado NL)
Además guarda P(«Yes») y P(«No») del siguiente token en el último lugar.

Salida en <salida>/:
  manifiesto.jsonl                      una línea por ejemplo (idx, id, etiqueta, grupo, ...)
  acts_<variante>_<posicion>.npy        float16, forma (N, n_capas+1, d_modelo)
                                        (acts_solo_nl_media_nl.npy en lugar de *_media_lean)
  pyes_<variante>.npy                   float32, forma (N, 8):
                                        [0:4] p_yes, p_no, logit_yes, logit_no en el último token
                                        del prompt («Yes»/«No» sin espacio). Qwen3 casi nunca
                                        empieza así (abre con «**Answer: No**»): masa baja.
                                        [4:8] lo mismo tras el prefijo forzado PREFIJO_RESPUESTA
                                        («**Answer:»), con « Yes»/« No»; masa ≈ 1. Es un segundo
                                        pase que solo lee logits: no cambia las activaciones.
  hecho_<variante>.npy                  bool, forma (N,): qué filas ya están (permite reanudar)
  meta.json                             modelo, revisión, versiones, plantilla; «corridas»
                                        guarda tiempo y memoria de cada sesión

Uso (de punta a punta probado el 4 nov 2026 con --limite 5):
  biblioteca/.venv/bin/python -I probes/extraer.py --salida probes/activaciones/qwen3_4b
  ... --variantes solo_nl nl_desemparejado   (solo esas, sobre una salida existente)
"""

import argparse
import datetime as dt
import hashlib
import json
import os
import platform
import sys
import time
import unicodedata

import numpy as np
import pyarrow.parquet as pq
import torch
import transformers
from transformers import AutoModelForCausalLM, AutoTokenizer

RAIZ = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATOS = os.path.join(RAIZ, "probes", "datos", "criticleanbench_test.parquet")
BITACORA = os.path.join(RAIZ, "probes", "BITACORA.md")

PREFIJO_RESPUESTA = "**Answer:"
PREGUNTA = "Is this formalization faithful? Answer Yes or No."
PLANTILLA_COMPLETO = (
    "Natural-language statement:\n{nl}\n\n"
    "Lean 4 formalization:\n```lean\n{lean}\n```\n\n" + PREGUNTA
)
PLANTILLA_SOLO_LEAN = "Lean 4 formalization:\n```lean\n{lean}\n```\n\n" + PREGUNTA
PLANTILLA_SOLO_NL = "Natural-language statement:\n{nl}\n\n" + PREGUNTA
VARIANTES = ("completo", "solo_lean", "solo_nl", "nl_desemparejado")
SEMILLA_DESARREGLO = 0
N_BANDAS = 5  # quintiles de longitud (caracteres) del NL


def posiciones(variante):
    return ("ultimo", "media_nl") if variante == "solo_nl" else ("ultimo", "media_lean")


def ahora():
    return dt.datetime.now().astimezone().strftime("%Y-%m-%d %H:%M %Z")


def anotar(msg, bitacora):
    print(msg, flush=True)
    if bitacora:
        with open(BITACORA, "a", encoding="utf-8") as f:
            f.write(f"- [{ahora()}] extraer.py: {msg}\n")


def grupo_de(nl):
    """Grupo por problema: enunciado NL normalizado (espacios y mayúsculas)."""
    t = unicodedata.normalize("NFKC", nl).lower()
    t = " ".join(t.split())
    return hashlib.sha256(t.encode()).hexdigest()[:12]


def desarreglo(filas, semilla=SEMILLA_DESARREGLO, n_bandas=N_BANDAS):
    """Para cada fila, el índice de la fila cuyo NL recibe en «nl_desemparejado».

    Se calcula siempre sobre el dataset completo (no depende de --idx ni --limite).
    Bandas: las filas ordenadas por longitud del NL (caracteres, desempate por índice) se
    cortan en n_bandas trozos casi iguales. Dentro de cada banda, permutación al azar con la
    semilla, repetida hasta que ninguna fila quede con su propio NL ni con uno del mismo grupo.

    Returns:
        (donante, banda): dos listas de enteros, de largo len(filas).
    """
    rng = np.random.default_rng(semilla)
    largo = [len(f["refined_statement"].strip()) for f in filas]
    grupos = [grupo_de(f["refined_statement"]) for f in filas]
    orden = sorted(range(len(filas)), key=lambda j: (largo[j], j))
    donante, banda = [None] * len(filas), [None] * len(filas)
    for b, trozo in enumerate(np.array_split(np.array(orden), n_bandas)):
        trozo = trozo.tolist()
        for _ in range(10000):
            perm = rng.permutation(trozo).tolist()
            if all(grupos[j] != grupos[k] for j, k in zip(trozo, perm)):
                break
        else:
            raise SystemExit(f"No encontré desarreglo en la banda {b}")
        for j, k in zip(trozo, perm):
            donante[j], banda[j] = k, b
    return donante, banda


def construir_prompt(tok, fila, variante, chat, nl_ajeno=None):
    """Devuelve el prompt y el intervalo de caracteres del bloque que se promedia
    (el Lean, o el NL en «solo_nl»)."""
    lean = fila["autoformalization"].strip()
    nl = fila["refined_statement"].strip()
    if variante == "completo":
        texto = PLANTILLA_COMPLETO.format(nl=nl, lean=lean)
    elif variante == "solo_lean":
        texto = PLANTILLA_SOLO_LEAN.format(lean=lean)
    elif variante == "solo_nl":
        texto = PLANTILLA_SOLO_NL.format(nl=nl)
    elif variante == "nl_desemparejado":
        texto = PLANTILLA_COMPLETO.format(nl=nl_ajeno.strip(), lean=lean)
    else:
        raise ValueError(variante)
    if chat:
        kw = {"enable_thinking": False}  # Qwen3: sin bloque de razonamiento
        prompt = tok.apply_chat_template(
            [{"role": "user", "content": texto}], tokenize=False,
            add_generation_prompt=True, **kw)
    else:
        prompt = texto + "\n"
    if variante == "solo_nl":
        ini = prompt.index("Natural-language statement:\n") + len("Natural-language statement:\n")
        return prompt, (ini, ini + len(nl))
    ini = prompt.index("```lean\n") + len("```lean\n")
    return prompt, (ini, ini + len(lean))


def ids_si_no(tok):
    """Ids de un solo token para «Yes» y «No» (sin espacio inicial, como empieza la respuesta)."""
    res = {}
    for w in ("Yes", "No"):
        ids = tok.encode(w, add_special_tokens=False)
        if len(ids) != 1:
            raise SystemExit(f"«{w}» no es un solo token: {ids}")
        res[w] = ids[0]
    for w in (" Yes", " No"):
        ids = tok.encode(w, add_special_tokens=False)
        if len(ids) != 1:
            raise SystemExit(f"«{w}» no es un solo token: {ids}")
        res[w] = ids[0]
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--modelo", default="Qwen/Qwen3-4B")
    ap.add_argument("--revision", default="1cfa9a7208912126459214e8b04321603b3df60c")
    ap.add_argument("--salida", required=True)
    ap.add_argument("--limite", type=int, default=None, help="solo las primeras N filas")
    ap.add_argument("--idx", type=int, nargs="+", default=None,
                    help="solo estas filas (pruebas de humo); el manifiesto guarda el idx original")
    ap.add_argument("--variantes", nargs="+", default=list(VARIANTES), choices=list(VARIANTES))
    ap.add_argument("--dtype", default="bfloat16", choices=["bfloat16", "float16", "float32"])
    ap.add_argument("--max_tokens", type=int, default=4096, help="se trunca y se marca si se pasa")
    ap.add_argument("--sin_chat", action="store_true", help="no usar plantilla de chat")
    ap.add_argument("--bitacora", action="store_true", help="registrar avance en probes/BITACORA.md")
    ap.add_argument("--cada", type=int, default=50, help="frecuencia del registro de avance")
    # Prerregistro v2 (4 nov 2026, 22:29): control de pesos aleatorios y modelos con config anidada.
    ap.add_argument("--pesos_aleatorios", type=int, default=None, metavar="SEMILLA",
                    help="control: misma arquitectura y tokenizador, pesos iniciales aleatorios (torch.manual_seed)")
    ap.add_argument("--dtype_acts", default="float16", choices=["float16", "float32"],
                    help="tipo de las activaciones guardadas (float32 si un modelo desborda fp16)")
    a = ap.parse_args()

    os.makedirs(a.salida, exist_ok=True)
    filas = pq.read_table(DATOS).to_pylist()
    todas = filas
    donante, banda = desarreglo(todas)
    orig = list(range(len(filas)))
    if a.idx:
        orig = a.idx
        filas = [filas[j] for j in orig]
    if a.limite:
        filas, orig = filas[: a.limite], orig[: a.limite]
    N = len(filas)

    dispositivo = "mps" if torch.backends.mps.is_available() else "cpu"
    tok = AutoTokenizer.from_pretrained(a.modelo, revision=a.revision)
    t0 = time.time()
    if a.pesos_aleatorios is None:
        modelo = AutoModelForCausalLM.from_pretrained(
            a.modelo, revision=a.revision, dtype=getattr(torch, a.dtype)).to(dispositivo).eval()
    else:
        from transformers import AutoConfig
        torch.manual_seed(a.pesos_aleatorios)
        cfg0 = AutoConfig.from_pretrained(a.modelo, revision=a.revision)
        modelo = AutoModelForCausalLM.from_config(cfg0, dtype=getattr(torch, a.dtype)).to(dispositivo).eval()
    t_carga = time.time() - t0
    cfg = modelo.config
    cfg_txt = getattr(cfg, "text_config", None) or cfg  # Gemma 3: la config de texto va anidada
    L1, D = cfg_txt.num_hidden_layers + 1, cfg_txt.hidden_size
    ACT_DT = np.float16 if a.dtype_acts == "float16" else np.float32
    chat = (not a.sin_chat) and tok.chat_template is not None
    si_no = ids_si_no(tok)

    # Manifiesto (se reescribe idéntico en cada arranque; no depende del modelo salvo n_tokens)
    ruta_man = os.path.join(a.salida, "manifiesto.jsonl")
    man = []
    for i, f in enumerate(filas):
        man.append({
            "idx": orig[i], "id": int(f["id"]), "source": f["source"], "tag": f["tag"],
            "etiqueta": int(f["tag"] == "compile_right_is_right"),  # 1 = adecuada (etiqueta humana)
            "compila": int(f["tag"] != "compile_false"),
            "grupo": grupo_de(f["refined_statement"]),
            "nl_desemparejado_idx": donante[orig[i]],
            "nl_desemparejado_id": int(todas[donante[orig[i]]]["id"]),
            "nl_desemparejado_banda": banda[orig[i]],
        })
    VAR = a.variantes

    arrs, pyes, hecho = {}, {}, {}
    for v in VAR:
        for p in posiciones(v):
            ruta = os.path.join(a.salida, f"acts_{v}_{p}.npy")
            modo = "r+" if os.path.exists(ruta) else "w+"
            arrs[v, p] = np.lib.format.open_memmap(ruta, mode=modo, dtype=ACT_DT, shape=(N, L1, D))
        ruta = os.path.join(a.salida, f"pyes_{v}.npy")
        pyes[v] = np.lib.format.open_memmap(
            ruta, mode="r+" if os.path.exists(ruta) else "w+", dtype=np.float32, shape=(N, 8))
        ruta = os.path.join(a.salida, f"hecho_{v}.npy")
        hecho[v] = np.load(ruta) if os.path.exists(ruta) else np.zeros(N, dtype=bool)
    for x in list(arrs.values()) + list(pyes.values()) + list(hecho.values()):
        if x.shape[0] != N:
            raise SystemExit(f"La salida existente tiene {x.shape[0]} filas y esta corrida {N}: "
                             "usa otra carpeta de salida para --limite distinto.")

    pendientes = sum(int((~hecho[v]).sum()) for v in VAR)
    anotar(f"inicio {a.modelo}@{a.revision[:8]} en {dispositivo} ({a.dtype}); "
           f"{N} filas, variantes {', '.join(VAR)}, {pendientes} pases pendientes; salida {os.path.relpath(a.salida, RAIZ)}",
           a.bitacora)

    tiempos, pico = [], 0.0
    hechos_sesion = 0
    for i, f in enumerate(filas):
        for v in VAR:
            if hecho[v][i]:
                continue
            nl_ajeno = todas[donante[orig[i]]]["refined_statement"]
            prompt, (c0, c1) = construir_prompt(tok, f, v, chat, nl_ajeno)
            enc = tok(prompt, return_offsets_mapping=True, add_special_tokens=False,
                      return_tensors="pt")
            off = enc.pop("offset_mapping")[0]
            n = enc["input_ids"].shape[1]
            truncado = n > a.max_tokens
            if truncado:
                enc = {k: x[:, : a.max_tokens] for k, x in enc.items()}
                off = off[: a.max_tokens]
                n = a.max_tokens
            mascara = (off[:, 0] >= c0) & (off[:, 1] <= c1) & (off[:, 1] > off[:, 0])
            # Desviación del 5 nov 2026 (02:3x, prerregistro v2): algunos tokenizadores rápidos
            # (DeepSeek-Prover-V2) dan offsets incoherentes y la máscara sale vacía o recortada.
            # Si su tamaño difiere en más de 3 tokens del que da tokenizar el prefijo, se usa la
            # máscara por prefijo [len(tok(prompt[:c0])), len(tok(prompt[:c1]))).
            n0 = len(tok(prompt[:c0], add_special_tokens=False)["input_ids"])
            n1 = len(tok(prompt[:c1], add_special_tokens=False)["input_ids"])
            por_prefijo = abs(int(mascara.sum()) - (n1 - n0)) > 3
            if por_prefijo:
                mascara = torch.zeros(n, dtype=torch.bool)
                mascara[min(n0, n):min(n1, n)] = True
            ti = time.time()
            with torch.no_grad():
                out = modelo(**{k: x.to(dispositivo) for k, x in enc.items()},
                             output_hidden_states=True, use_cache=False, logits_to_keep=1)
            # Capa por capa, sin apilar todo el residual (ahorra memoria en los modelos de 7–8B)
            m_lean = mascara.to(dispositivo)
            ult = torch.stack([h[0, -1] for h in out.hidden_states]).float()  # (L1, D)
            med = torch.stack([h[0, m_lean].float().mean(0) for h in out.hidden_states])
            lg = out.logits[0, -1].float()
            del out
            pr = torch.softmax(lg, -1)
            pre = tok(PREFIJO_RESPUESTA, add_special_tokens=False, return_tensors="pt")["input_ids"]
            with torch.no_grad():
                ids2 = torch.cat([enc["input_ids"], pre], 1)
                lg2 = modelo(input_ids=ids2.to(dispositivo), use_cache=False,
                             logits_to_keep=1).logits[0, -1].float()
            pr2 = torch.softmax(lg2, -1)
            fila_p = torch.stack([pr[si_no["Yes"]], pr[si_no["No"]], lg[si_no["Yes"]], lg[si_no["No"]],
                                  pr2[si_no[" Yes"]], pr2[si_no[" No"]],
                                  lg2[si_no[" Yes"]], lg2[si_no[" No"]]])
            if dispositivo == "mps":
                torch.mps.synchronize()
            tiempos.append(time.time() - ti)
            if dispositivo == "mps":
                pico = max(pico, torch.mps.driver_allocated_memory() / 2**30)
            for nombre, x in zip(posiciones(v), (ult, med)):
                if not torch.isfinite(x).all() or (ACT_DT == np.float16 and x.abs().max() > 65000):
                    anotar(f"AVISO fila {i} {v} {nombre}: valores fuera de rango fp16", a.bitacora)
                arrs[v, nombre][i] = x.cpu().numpy().astype(ACT_DT)
            pyes[v][i] = fila_p.cpu().numpy()
            man[i][f"n_tokens_{v}"] = int(n)
            man[i][f"n_tokens_{'nl' if v == 'solo_nl' else 'lean'}_{v}"] = int(mascara.sum())
            man[i][f"truncado_{v}"] = bool(truncado)
            man[i][f"mascara_por_prefijo_{v}"] = bool(por_prefijo)
            hecho[v][i] = True
            hechos_sesion += 1
            if hechos_sesion % a.cada == 0:
                for vv in VAR:
                    np.save(os.path.join(a.salida, f"hecho_{vv}.npy"), hecho[vv])
                    pyes[vv].flush()
                for x in arrs.values():
                    x.flush()
                faltan = sum(int((~hecho[vv]).sum()) for vv in VAR)
                anotar(f"avance: {hechos_sesion} pases en esta sesión, faltan {faltan}; "
                       f"{np.mean(tiempos):.2f} s/pase", a.bitacora)

    for v in VAR:
        np.save(os.path.join(a.salida, f"hecho_{v}.npy"), hecho[v])
        pyes[v].flush()
    for x in arrs.values():
        x.flush()

    # Conservar n_tokens de corridas previas si esta sesión no tocó la fila
    if os.path.exists(ruta_man):
        with open(ruta_man, encoding="utf-8") as fh:
            viejo = {json.loads(l)["idx"]: json.loads(l) for l in fh}
        for m in man:
            for k, x in viejo.get(m["idx"], {}).items():
                m.setdefault(k, x)
    with open(ruta_man, "w", encoding="utf-8") as fh:
        for m in man:
            fh.write(json.dumps(m, ensure_ascii=False) + "\n")

    ruta_meta = os.path.join(a.salida, "meta.json")
    previo = json.load(open(ruta_meta, encoding="utf-8")) if os.path.exists(ruta_meta) else {}
    corridas = previo.get("corridas", [])
    if not corridas and previo.get("segundos_por_pase_media") is not None:
        corridas.append({"fecha": previo.get("fecha"), "variantes": previo.get("variantes"),
                         "segundos_por_pase_media": previo.get("segundos_por_pase_media"),
                         "memoria_driver_mps_gib_pico": previo.get("memoria_driver_mps_gib_pico")})
    corridas.append({"fecha": ahora(), "variantes": VAR, "pases": hechos_sesion,
                     "segundos_carga": round(t_carga, 1),
                     "segundos_por_pase_media": round(float(np.mean(tiempos)), 3) if tiempos else None,
                     "segundos_totales_pases": round(float(np.sum(tiempos)), 1) if tiempos else 0.0,
                     "memoria_driver_mps_gib_pico": round(pico, 2) if pico else None})
    hechas = [v for v in VARIANTES
              if os.path.exists(os.path.join(a.salida, f"hecho_{v}.npy"))
              and np.load(os.path.join(a.salida, f"hecho_{v}.npy")).all()]
    meta = {
        "fecha": ahora(), "modelo": a.modelo, "revision": a.revision, "dtype_modelo": a.dtype,
        "dtype_activaciones": a.dtype_acts, "dispositivo": dispositivo, "n_filas": N,
        "pesos_aleatorios_semilla": a.pesos_aleatorios,
        "n_capas_mas_embeddings": L1, "d_modelo": D, "plantilla_chat": chat,
        "enable_thinking": False if chat else None,
        "plantilla_completo": PLANTILLA_COMPLETO, "plantilla_solo_lean": PLANTILLA_SOLO_LEAN,
        "plantilla_solo_nl": PLANTILLA_SOLO_NL,
        "nl_desemparejado": {"semilla": SEMILLA_DESARREGLO, "bandas": N_BANDAS,
                             "criterio": "quintiles de longitud del NL en caracteres; desarreglo "
                                         "dentro de cada banda; nunca el mismo grupo (NL normalizado)"},
        "ids_yes_no": si_no, "prefijo_respuesta": PREFIJO_RESPUESTA,
        "columnas_pyes": ["p_yes", "p_no", "logit_yes", "logit_no", "p_yes_prefijo",
                          "p_no_prefijo", "logit_yes_prefijo", "logit_no_prefijo"],
        "posiciones": {v: list(posiciones(v)) for v in VARIANTES}, "variantes_completas": hechas,
        "etiqueta": "1 = compile_right_is_right (adecuada, etiqueta humana de CriticLeanBench); 0 = resto",
        "dataset": "m-a-p/CriticLeanBench@6225522bce304f62d4907aedb9642255f9417bf0",
        "dataset_sha256": "baf3e43bcfe0c476114e744b7cde098fe02292a5ab9b0b0fa84dc279f1e203d3",
        "versiones": {"python": sys.version.split()[0], "torch": torch.__version__,
                      "transformers": transformers.__version__, "numpy": np.__version__,
                      "macos": platform.mac_ver()[0]},
        "corridas": corridas,
    }
    with open(ruta_meta, "w", encoding="utf-8") as fh:
        json.dump(meta, fh, ensure_ascii=False, indent=2)
    faltan = sum(int((~hecho[v]).sum()) for v in VAR)
    anotar(f"fin: {hechos_sesion} pases en esta sesión, faltan {faltan}; "
           f"{np.mean(tiempos) if tiempos else 0:.2f} s/pase, pico MPS {pico:.2f} GiB; "
           f"meta en {os.path.relpath(ruta_meta, RAIZ)}", a.bitacora)


if __name__ == "__main__":
    main()
