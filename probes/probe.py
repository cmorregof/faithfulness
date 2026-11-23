"""Probes lineales por capa para el piloto de adecuación NL <-> Lean 4."""

import json
from datetime import date
from pathlib import Path

import numpy as np
from scipy.sparse import csr_matrix, hstack
from sklearn.feature_extraction.text import CountVectorizer
from sklearn.linear_model import LogisticRegression
from sklearn.metrics import roc_auc_score
from sklearn.model_selection import StratifiedGroupKFold
from sklearn.preprocessing import MaxAbsScaler, StandardScaler

CARPETA = Path(__file__).parent / "activaciones" / "qwen3_4b"
PARQUET = Path(__file__).parent / "datos" / "criticleanbench_test.parquet"
SEMILLA = 0
SEMILLAS = (0, 1, 2, 3, 4)


def cargar(carpeta, variante, posicion):
    """Devuelve X (N, capas, dim) en float32, y (N,), grupos (N,) y el manifiesto."""
    carpeta = Path(carpeta)
    with open(carpeta / "manifiesto.jsonl", encoding="utf-8") as f:
        manifiesto = [json.loads(linea) for linea in f if linea.strip()]
    manifiesto.sort(key=lambda fila: fila["idx"])
    if [fila["idx"] for fila in manifiesto] != list(range(len(manifiesto))):
        raise ValueError("Los idx del manifiesto no son 0, 1, 2, ... sin huecos.")

    y = np.array([fila["etiqueta"] for fila in manifiesto], dtype=int)
    grupos = np.array([fila["grupo"] for fila in manifiesto])
    X = np.load(carpeta / f"acts_{variante}_{posicion}.npy").astype(np.float32)

    if not (len(X) == len(y) == len(grupos)):
        raise ValueError(f"Filas distintas: X={len(X)}, y={len(y)}, grupos={len(grupos)}.")
    if not np.isfinite(X).all():
        raise ValueError("Hay NaN o infinitos en las activaciones.")
    return X, y, grupos, manifiesto


def subconjunto(manifiesto, excluir_no_compila):
    """Índices a usar; con excluir_no_compila se quitan las filas que no compilan."""
    return np.array(
        [f["idx"] for f in manifiesto if not (excluir_no_compila and f["compila"] == 0)],
        dtype=int,
    )


def particiones_agrupadas(y, grupos, k=5, semilla=0):
    """k particiones (entrenamiento, prueba) estratificadas y sin grupos compartidos."""
    separador = StratifiedGroupKFold(n_splits=k, shuffle=True, random_state=semilla)
    particiones = list(separador.split(np.zeros(len(y)), y, grupos))
    for entrenamiento, prueba in particiones:
        if set(grupos[entrenamiento]) & set(grupos[prueba]):
            raise RuntimeError("Un grupo quedó en entrenamiento y en prueba.")
    return particiones


def auroc(y, puntajes):
    """Área bajo la curva ROC."""
    return float(roc_auc_score(y, puntajes))


def _ajustar_y_puntuar(X_ent, y_ent, X_pru, C=1.0):
    escalador = StandardScaler().fit(X_ent)
    modelo = LogisticRegression(C=C, max_iter=2000)
    modelo.fit(escalador.transform(X_ent), y_ent)
    return modelo.predict_proba(escalador.transform(X_pru))[:, 1]


def probe_por_capa(X_capa, y, particiones, C=1.0):
    """Regresión logística sobre una capa; puntajes fuera de partición."""
    puntajes = np.full(len(y), np.nan)
    for entrenamiento, prueba in particiones:
        puntajes[prueba] = _ajustar_y_puntuar(
            X_capa[entrenamiento], y[entrenamiento], X_capa[prueba], C
        )
    return puntajes


def curva_por_capa(X, y, grupos, k=5, semilla=0, n_boot=2000, verboso=True, semillas=None):
    """probe_por_capa en todas las capas, con puntajes promediados sobre las semillas."""
    semillas = (semilla,) if semillas is None else tuple(semillas)
    particiones = [particiones_agrupadas(y, grupos, k, s) for s in semillas]
    n_capas = X.shape[1]
    aurocs = np.zeros(n_capas)
    ics = np.full((n_capas, 2), np.nan)
    puntajes = np.zeros((n_capas, len(y)))
    for c in range(n_capas):
        puntajes[c] = np.mean([probe_por_capa(X[:, c, :], y, p) for p in particiones], axis=0)
        aurocs[c], ics[c, 0], ics[c, 1] = ic_bootstrap(
            y, puntajes[c], grupos, n=n_boot, semilla=semillas[0]
        )
        if verboso:
            print(f"  capa {c:2d}  AUROC {aurocs[c]:.3f}  [{ics[c, 0]:.3f}, {ics[c, 1]:.3f}]")
    return {"auroc": aurocs, "ic": ics, "puntajes": puntajes}


def _sorteos_de_grupos(y, grupos, n, semilla):
    _, inverso = np.unique(grupos, return_inverse=True)
    orden = np.argsort(inverso, kind="stable")
    filas = np.split(orden, np.cumsum(np.bincount(inverso))[:-1])
    media = np.array([y[f].mean() for f in filas])
    estrato = np.where(media == 0, 0, np.where(media == 1, 1, 2))
    estratos = [np.flatnonzero(estrato == e) for e in np.unique(estrato)]
    rng = np.random.default_rng(semilla)
    for _ in range(n):
        elegidos = np.concatenate([rng.choice(e, size=len(e)) for e in estratos])
        yield np.concatenate([filas[g] for g in elegidos])


def ic_bootstrap(y, puntajes, grupos, n=2000, semilla=0, alfa=0.05):
    """(AUROC, inferior, superior) remuestreando grupos, estratificado por clase."""
    punto = auroc(y, puntajes)
    muestras = []
    for filas in _sorteos_de_grupos(y, grupos, n, semilla):
        if len(np.unique(y[filas])) == 2:
            muestras.append(auroc(y[filas], puntajes[filas]))
    if not muestras:
        return punto, np.nan, np.nan
    inferior, superior = np.quantile(muestras, [alfa / 2, 1 - alfa / 2])
    return punto, float(inferior), float(superior)


def diferencia_pareada(y, puntajes_a, puntajes_b, grupos, n=2000, semilla=0, alfa=0.05):
    """AUROC(a) - AUROC(b) con IC, usando los mismos sorteos para a y b."""
    punto = auroc(y, puntajes_a) - auroc(y, puntajes_b)
    muestras = []
    for filas in _sorteos_de_grupos(y, grupos, n, semilla):
        if len(np.unique(y[filas])) == 2:
            muestras.append(auroc(y[filas], puntajes_a[filas]) - auroc(y[filas], puntajes_b[filas]))
    inferior, superior = np.quantile(muestras, [alfa / 2, 1 - alfa / 2])
    return punto, float(inferior), float(superior)


def elegir_capa_anidada(X, y, grupos, k=5, semilla=0, k_interno=5):
    """Elige la capa dentro de cada entrenamiento externo. Devuelve puntajes y capas."""
    puntajes = np.full(len(y), np.nan)
    capas = []
    for entrenamiento, prueba in particiones_agrupadas(y, grupos, k, semilla):
        y_ent = y[entrenamiento]
        internas = particiones_agrupadas(y_ent, grupos[entrenamiento], k_interno, semilla)
        aurocs = [
            auroc(y_ent, probe_por_capa(X[entrenamiento, c, :], y_ent, internas))
            for c in range(X.shape[1])
        ]
        mejor = int(np.argmax(aurocs))
        capas.append(mejor)
        puntajes[prueba] = _ajustar_y_puntuar(X[entrenamiento, mejor, :], y_ent, X[prueba, mejor, :])
    return puntajes, capas


def control_barajadas(X, y, grupos, n_barajes=5, semilla=0):
    """Curva por capa con etiquetas barajadas: media y desviación de la AUROC."""
    rng = np.random.default_rng(semilla)
    todas = np.array([
        curva_por_capa(X, rng.permutation(y), grupos, semilla=semilla, n_boot=0, verboso=False)["auroc"]
        for _ in range(n_barajes)
    ])
    return {"auroc": todas.mean(axis=0), "std": todas.std(axis=0), "todas": todas}


def linea_base_superficie(textos_lean, y, grupos, k=5, semilla=0, semillas=None):
    """Regresión logística sobre unigramas y bigramas del Lean y su longitud."""
    semillas = (semilla,) if semillas is None else tuple(semillas)
    textos = np.array(textos_lean, dtype=object)
    log_largo = np.log1p(np.array([len(t) for t in textos], dtype=float)).reshape(-1, 1)
    corridas = []
    for s in semillas:
        puntajes = np.full(len(y), np.nan)
        for entrenamiento, prueba in particiones_agrupadas(y, grupos, k, s):
            vectorizador = CountVectorizer(token_pattern=r"\S+", lowercase=False, ngram_range=(1, 2))
            conteos_ent = vectorizador.fit_transform(textos[entrenamiento])
            conteos_pru = vectorizador.transform(textos[prueba])
            escala_conteos = MaxAbsScaler().fit(conteos_ent)
            escala_largo = StandardScaler().fit(log_largo[entrenamiento])
            A_ent = hstack([
                escala_conteos.transform(conteos_ent),
                csr_matrix(escala_largo.transform(log_largo[entrenamiento])),
            ]).tocsr()
            A_pru = hstack([
                escala_conteos.transform(conteos_pru),
                csr_matrix(escala_largo.transform(log_largo[prueba])),
            ]).tocsr()
            modelo = LogisticRegression(C=1.0, max_iter=2000).fit(A_ent, y[entrenamiento])
            puntajes[prueba] = modelo.predict_proba(A_pru)[:, 1]
        corridas.append(puntajes)
    puntajes = np.mean(corridas, axis=0)
    punto, inferior, superior = ic_bootstrap(y, puntajes, grupos, semilla=semillas[0])
    return {"auroc": punto, "ic": (inferior, superior), "puntajes": puntajes}


def auroc_pyes(pyes, y, grupos):
    """AUROC de p_yes / (p_yes + p_no) con las columnas 4 y 5."""
    p_si, p_no = pyes[:, 4].astype(float), pyes[:, 5].astype(float)
    masa = p_si + p_no
    puntajes = p_si / np.maximum(masa, 1e-12)
    punto, inferior, superior = ic_bootstrap(y, puntajes, grupos)
    return {
        "auroc": punto,
        "ic": (inferior, superior),
        "masa_media": float(masa.mean()),
        "puntajes": puntajes,
    }


def figura_auroc_por_capa(curvas, ruta, titulo="", superficie=None):
    """AUROC por capa con bandas; una curva por condición."""
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, ax = plt.subplots(figsize=(9, 5))
    for nombre, curva in curvas.items():
        capas = np.arange(len(curva["auroc"]))
        (linea,) = ax.plot(capas, curva["auroc"], label=nombre, linewidth=1.8)
        if "ic" in curva:
            bajo, alto = curva["ic"][:, 0], curva["ic"][:, 1]
        else:
            bajo, alto = curva["auroc"] - curva["std"], curva["auroc"] + curva["std"]
        ax.fill_between(capas, bajo, alto, color=linea.get_color(), alpha=0.18, linewidth=0)
    ax.axhline(0.5, color="gray", linestyle=":", linewidth=1, label="azar (0,5)")
    if superficie is not None:
        ax.axhline(superficie, color="black", linestyle="--", linewidth=1,
                   label=f"superficie ({superficie:.2f})")
    ax.set_xlabel("capa (0 = embeddings)")
    ax.set_ylabel("AUROC fuera de partición")
    ax.set_title(titulo)
    ax.set_ylim(0.3, 1.0)
    ax.legend(loc="lower right", frameon=False)
    fig.tight_layout()
    fig.savefig(ruta, dpi=160)
    plt.close(fig)


def _leer_lean(parquet, manifiesto, en_orden=False):
    import pyarrow.parquet as pq

    tabla = pq.read_table(parquet).to_pydict()
    n = len(manifiesto)
    if "idx" in tabla:
        posicion = {idx: p for p, idx in enumerate(tabla["idx"])}
        faltan = [i for i in range(n) if i not in posicion]
        if faltan:
            raise ValueError(f"Al parquet le faltan {len(faltan)} idx del manifiesto, p. ej. {faltan[:5]}.")
        posiciones = [posicion[i] for i in range(n)]
    elif en_orden and len(tabla["autoformalization"]) == n:
        posiciones = list(range(n))
    else:
        raise ValueError(
            "El parquet no trae columna idx, así que no se puede comprobar que sus filas "
            "coincidan con el manifiesto. Si el orden es el mismo y tiene las mismas "
            f"{n} filas, llama a main(..., parquet_en_orden=True)."
        )
    for clave in (set(manifiesto[0]) & set(tabla)) - {"idx"}:
        if not isinstance(manifiesto[0][clave], (str, int)):
            continue
        distintas = sum(tabla[clave][p] != fila[clave] for p, fila in zip(posiciones, manifiesto))
        if distintas:
            raise ValueError(f"Parquet y manifiesto difieren en '{clave}' en {distintas} filas.")
    return [tabla["autoformalization"][p] for p in posiciones]


def _verificar_conteos(y, excluir):
    conteos = (len(y), int((y == 1).sum()), int((y == 0).sum()))
    if excluir and conteos != (450, 250, 200):
        raise ValueError(f"Se esperaban 450 filas (250 vs 200) y hay {conteos}.")
    if not excluir and conteos[0] != 500:
        raise ValueError(f"Se esperaban 500 filas y hay {conteos[0]}.")


def _anidada_promediada(X, y, grupos):
    corridas = [elegir_capa_anidada(X, y, grupos, semilla=s) for s in SEMILLAS]
    return np.mean([p for p, _ in corridas], axis=0), [capas for _, capas in corridas]


def _fmt(punto, inferior, superior):
    return f"{punto:.3f} [{inferior:.3f}, {superior:.3f}]"


def main(carpeta=CARPETA, parquet=PARQUET, salida=None, parquet_en_orden=False):
    """Corre todo y escribe probes/resultados_AAAA-MM-DD.md.

    REGLA DE DECISIÓN (cópiala a la bitácora ANTES de correr):
      - Análisis principal: 450 filas que compilan; posición «ultimo». Lo demás es secundario.
      - Capa: elegida por validación cruzada anidada (o el rango fijado en la bitácora).
      - «Separa más allá del Lean» si diferencia_pareada(completo, solo_lean) tiene su IC
        del 95 % entero por encima de 0. Si no, se reporta como nulo, con la misma tabla.

    En «ultimo» la capa se elige por validación anidada (lectura i). En «media_lean» se usa
    la capa fija ⌊2L/3⌋, sin elegir (lectura ii).
    """
    carpeta = Path(carpeta)
    fecha = date.today().isoformat()
    salida = Path(salida) if salida else Path(__file__).parent / f"resultados_{fecha}.md"

    meta = {}
    if (carpeta / "meta.json").exists():
        meta = json.loads((carpeta / "meta.json").read_text(encoding="utf-8"))

    lineas = [
        f"# Resultados de probes lineales ({fecha})",
        "",
        f"Semillas: {list(SEMILLAS)} (puntajes fuera de partición promediados). "
        f"Bootstrap: 2000 remuestreos estratificados por clase. Carpeta: `{carpeta.name}`.",
        "",
        "```json",
        json.dumps(meta, ensure_ascii=False, indent=2),
        "```",
        "",
    ]

    textos_todos = None
    for excluir in (True, False):
        for posicion in ("ultimo", "media_lean"):
            X_comp, y, grupos, manifiesto = cargar(carpeta, "completo", posicion)
            X_lean, _, _, _ = cargar(carpeta, "solo_lean", posicion)
            if textos_todos is None:
                textos_todos = _leer_lean(parquet, manifiesto, parquet_en_orden)
            filas = subconjunto(manifiesto, excluir)
            textos = [textos_todos[i] for i in filas]
            pyes = {v: np.load(carpeta / f"pyes_{v}.npy")[filas] for v in ("completo", "solo_lean")}
            X_comp, X_lean, y, grupos = X_comp[filas], X_lean[filas], y[filas], grupos[filas]
            _verificar_conteos(y, excluir)

            principal = excluir and posicion == "ultimo"
            nombre = f"{len(filas)} filas, posición {posicion}"
            print(f"\n== {nombre} ==")

            print("completo")
            curva_comp = curva_por_capa(X_comp, y, grupos, semillas=SEMILLAS)
            print("solo_lean")
            curva_lean = curva_por_capa(X_lean, y, grupos, semillas=SEMILLAS)
            print("barajadas")
            barajadas = control_barajadas(X_comp, y, grupos, semilla=SEMILLA)

            if posicion == "ultimo":
                print("capa anidada")
                lectura = "lectura (i), capa anidada"
                p_comp, capas_comp = _anidada_promediada(X_comp, y, grupos)
                p_lean, capas_lean = _anidada_promediada(X_lean, y, grupos)
                nota_comp = f"capas elegidas por semilla: {capas_comp}"
                nota_lean = f"capas elegidas por semilla: {capas_lean}"
            else:
                capa = (2 * (X_comp.shape[1] - 1)) // 3
                lectura = f"lectura (ii), capa fija {capa}"
                p_comp, p_lean = curva_comp["puntajes"][capa], curva_lean["puntajes"][capa]
                nota_comp = nota_lean = "sin selección"
            ic_comp = ic_bootstrap(y, p_comp, grupos, semilla=SEMILLA)
            ic_lean = ic_bootstrap(y, p_lean, grupos, semilla=SEMILLA)
            diferencia = diferencia_pareada(y, p_comp, p_lean, grupos, semilla=SEMILLA)

            superficie = linea_base_superficie(textos, y, grupos, semillas=SEMILLAS)
            dice = {v: auroc_pyes(pyes[v], y, grupos) for v in pyes}

            ruta_figura = salida.parent / f"auroc_por_capa_{posicion}_{len(filas)}_{fecha}.png"
            figura_auroc_por_capa(
                {"completo": curva_comp, "solo_lean": curva_lean, "barajadas": barajadas},
                ruta_figura,
                titulo=f"{carpeta.name}: {nombre}",
                superficie=superficie["auroc"],
            )

            c_comp, c_lean = int(curva_comp["auroc"].argmax()), int(curva_lean["auroc"].argmax())
            if diferencia[1] > 0:
                veredicto = "El probe con el prompt completo separa más allá del Lean (IC del 95 % sobre 0)."
            else:
                veredicto = "Nulo: el IC del 95 % de la diferencia incluye 0 o queda por debajo."

            lineas += [
                f"## {nombre} ({'análisis principal' if principal else 'secundario'}; {lectura})",
                "",
                "| Medida | AUROC [IC 95 %] | Nota |",
                "|---|---|---|",
                f"| Probe completo | {_fmt(*ic_comp)} | {nota_comp} |",
                f"| Probe solo_lean | {_fmt(*ic_lean)} | {nota_lean} |",
                f"| Diferencia pareada (completo - solo_lean) | {_fmt(*diferencia)} | prueba central |",
                f"| Superficie (unigramas y bigramas + longitud) | {_fmt(superficie['auroc'], *superficie['ic'])} | sin activaciones |",
                f"| P(Yes) completo | {_fmt(dice['completo']['auroc'], *dice['completo']['ic'])} | masa media {dice['completo']['masa_media']:.3f} |",
                f"| P(Yes) solo_lean | {_fmt(dice['solo_lean']['auroc'], *dice['solo_lean']['ic'])} | masa media {dice['solo_lean']['masa_media']:.3f} |",
                f"| Barajadas, máximo entre capas | {barajadas['auroc'].max():.3f} | debe rondar 0,5 |",
                f"| Mejor capa completo (descriptivo) | {_fmt(curva_comp['auroc'][c_comp], *curva_comp['ic'][c_comp])} | capa {c_comp}; optimista |",
                f"| Mejor capa solo_lean (descriptivo) | {_fmt(curva_lean['auroc'][c_lean], *curva_lean['ic'][c_lean])} | capa {c_lean}; optimista |",
                "",
                veredicto,
                "",
                f"![AUROC por capa]({ruta_figura.name})",
                "",
            ]

    salida.write_text("\n".join(lineas), encoding="utf-8")
    print(f"\nEscrito: {salida}")


if __name__ == "__main__":
    main()
