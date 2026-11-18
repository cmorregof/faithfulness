#!/usr/bin/env python3
"""aplica_v5.py — construye v5_causal/main_en.tex y main_es.tex a partir de v4_voz/ (13 nov 2026).

Aplica solo los pasajes que Carlos aprobó el 13 de noviembre. Lee siempre de ../v4_voz/, así que se puede
correr las veces que haga falta. Las filas de las dos tablas nuevas salen de
probes/intervencion/resultados_s5/tablas_nivel_b.json; ninguna se escribe a mano.

Uso (desde paper_adecuacion/v5_causal):  python3 aplica_v5.py
"""
import json
import os
import re
import textwrap

AQUI = os.path.dirname(os.path.abspath(__file__))
import sys; sys.path.insert(0, AQUI)
from ejemplos_nivel_b import filas_tex as filas_ejemplos   # décima tanda: pares de ejemplo del Nivel B
V4 = os.path.join(AQUI, "..", "v4_voz")
T = json.load(open(os.path.join(AQUI, "..", "..", "probes", "intervencion", "resultados_s5", "tablas_nivel_b.json"),
                   encoding="utf-8"))
T6 = json.load(open(os.path.join(AQUI, "..", "..", "probes", "intervencion", "resultados_s5", "s6_masa.json"), encoding="utf-8"))
PROBES = os.path.join(AQUI, "..", "..", "probes")
ORDEN_A = ("olmo2_7b", "gemma3_4b", "llama31_8b", "dsprover2_7b")          # el orden de tab:a
VA = {m: json.load(open(os.path.join(PROBES, "referencia", f"v2_resultados_{m}.json"), encoding="utf-8"))["lecturas"]["ii_media_lean_capa_fija"]
      for m in ORDEN_A}
EXC = json.load(open(os.path.join(PROBES, "nivel_b", "datos", "exclusiones_nivel_b.json"), encoding="utf-8"))
_ob, _eq = set(EXC["excluir_obligatorio"]["pares"]), set(EXC["excluir_del_principal_reportar_aparte"]["pares"])
N_OB, N_EQ, N_EXC = len(_ob), len(_eq), len(_ob | _eq)
M4 = ("qwen3_4b", "olmo2_7b", "llama31_8b", "gemma3_4b")                    # el orden de tab:b
ARCH = [json.load(open(os.path.join(PROBES, "nivel_b", "resultados", f"nivel_b_{m}_principal.json"), encoding="utf-8"))
        for m in M4]
assert all(a["n_archivos"] == 189 for a in ARCH)
SP = [json.load(open(os.path.join(PROBES, "sin_pregunta", "resultados", f"s2a_{m}.json"), encoding="utf-8"))["sin_pregunta"]["delta_sp"]
      for m in M4]


def ic3(t):
    return f"{f3(t[0], True)} \\ic{{{f3(t[1])}}}{{{f3(t[2])}}}"


def lista_ic(ts, y):
    v = [ic3(t) for t in ts]
    return ", ".join(v[:-1]) + f" {y} " + v[-1]


SENS = [VA[m]["sensibilidad_sin_dudosas"] for m in ORDEN_A]
assert all(e["n"] == 406 for e in SENS)
N_FILAS_DS = sum(1 for _ in open(os.path.join(PROBES, "activaciones", "dsprover2_7b", "manifiesto.jsonl"), encoding="utf-8"))
assert N_FILAS_DS * 4 == 2000


def lista_sens(y):
    return lista_ic([[e["delta_sobre_puntajes_del_primario"], *e["ic"]] for e in SENS], y)


CS = json.load(open(os.path.join(PROBES, "nivel_b", "datos", "compuerta_superficie_certificados.json"), encoding="utf-8"))
assert CS["criterio"] == "firma" and not CS["pasa"] and CS["exceso_firma"] > CS["umbral_firma"]
assert len(_ob & _eq) == 1 and N_EXC == EXC["pares_totales"] - EXC["pares_analisis_principal"]


def lista_a(clave, y):
    v = [f3(VA[m][clave]) for m in ORDEN_A]
    return ", ".join(v[:-1]) + f" {y} " + v[-1]


MODELOS = [("qwen3_4b", "Qwen3-4B"), ("olmo2_7b", "OLMo-2-7B"), ("llama31_8b", "Llama-3.1-8B"), ("gemma3_4b", "Gemma-3-4B")]
MENOS = "−"


def f3(x, signo=False):
    t = f"{abs(x):.3f}"
    neg = x < 0 and float(t) != 0
    return (MENOS if neg else ("+" if signo else "")) + t


def tri(t):
    return f"{f3(t[0], True)} [{f3(t[1], True)}, {f3(t[2], True)}]"


def filas_s3():
    out = []
    for m, n in MODELOS:
        p = T["s3"][m]["principal"]
        out.append(f"{n:13s}& {f3(p['auroc']['full_media'][0])} & "
                   + " & ".join(tri(p["media_menos"][k]) for k in ("ngramas", "cruzada", "p_yes", "combinada")) + r"\\")
    return "\n".join(out)


def filas_s5(de):
    out = []
    for m, n in MODELOS:
        d = T["s5"][m]; p = d["f2"]
        out.append(f"{n:13s}& {f3(d['base'][0])} & {f3(p['auroc'])} & {tri(p['caida'])} & {f3(p['azar_media'], True)}; "
                   f"{f3(p['azar_max'], True)} & {tri(p['menos_azar'])} & {p['n_azar_iguales_o_mayores']} {de} {p['n_azar']} & "
                   f"{f3(d['f4']['auroc'])} & {f3(d['f8']['auroc'])}" + r"\\")
    return "\n".join(out)


def filas_sec(si, no):
    out = []
    for m, n in MODELOS:
        d = T["s5"][m]
        dosis = si if (d["f4"]["supera_a_todas"] and d["f8"]["supera_a_todas"]) else no
        out.append(f"{n:13s}& {f3(d['placebo'])} & {tri(d['pareja']['menos_azar'])} & {tri(d['borrar']['menos_azar'])} & "
                   f"{tri(d['sonda_menos_solo_lean_f2'])} & {dosis} & {f3(T6[m]['base'][0])}; {f3(T6[m]['f2']['sonda'][0])}" + r"\\")
    return "\n".join(out)


def prosa(s):
    """Párrafos separados por línea en blanco, cada uno plegado a 118 columnas como el resto del .tex."""
    return "\n\n".join(textwrap.fill(" ".join(p.split()), 118, break_long_words=False, break_on_hyphens=False)
                       for p in s.strip().split("\n\n"))


BLOQUE_PROMPT = r'''\begin{verbatim}
Natural-language statement:
{statement}

Lean 4 formalization:
```lean
{formalization}
```

Is this formalization faithful? Answer Yes or No.
\end{verbatim}
'''


S7 = json.load(open(os.path.join(PROBES, "intervencion", "resultados_s5", "s7_sin_c2.json"), encoding="utf-8"))
_h = [f3(S7["holm"]["p_holm"][m]) for m in M4]
assert S7["holm"]["n_bajo_0.05"] == 1 and _h[0] < "0.050" and len(set(_h[1:])) == 1
H_QWEN, H_RESTO = _h[0], _h[1]
_s = {m: S7["sin_C2"][m]["sin_C2"] for m in M4}
assert [_s[m]["lectura"] for m in M4] == ["cumple sin C2", "cumple sin C2", "no cumple sin C2", "no cumple sin C2"]
assert not any(_s[m]["sin_senal_de_partida"] for m in M4) and all(_s[m]["n_pares"] == 309 for m in M4)
assert _s["llama31_8b"]["f2"]["n_azar_iguales_o_mayores"] == 1 and T["s5"]["llama31_8b"]["f2"]["n_azar_iguales_o_mayores"] == 2
assert _s["gemma3_4b"]["f2"]["n_azar_iguales_o_mayores"] == T["s5"]["gemma3_4b"]["f2"]["n_azar_iguales_o_mayores"]


def filas_sinc2(de):
    out = []
    for m, n in MODELOS:
        d = _s[m]; p = d["f2"]
        out.append(f"{n:13s}& {f3(d['base'][0])} & {f3(p['auroc'])} & {tri(p['menos_azar'])} & "
                   f"{p['n_azar_iguales_o_mayores']} {de} {p['n_azar']}" + r"\\")
    return "\n".join(out)


class Doc:
    def __init__(self, ruta):
        self.t = open(ruta, encoding="utf-8").read()
        self.n = 0

    def _pat(self, viejo):
        return re.compile(r"\s+".join(re.escape(x) for x in viejo.split()))

    def _uno(self, pat, viejo):
        k = len(pat.findall(self.t))
        assert k == 1, (k, viejo[:70])
        self.n += 1

    def cambia(self, viejo, nuevo):
        pat = self._pat(viejo); self._uno(pat, viejo)
        self.t = pat.sub(lambda m: nuevo, self.t)

    def tras(self, viejo, anadido, sep="\n"):
        pat = self._pat(viejo); self._uno(pat, viejo)
        self.t = pat.sub(lambda m: m.group(0) + sep + anadido, self.t)

    def antes(self, viejo, anadido):
        pat = self._pat(viejo); self._uno(pat, viejo)
        self.t = pat.sub(lambda m: anadido + m.group(0), self.t)

    def antes_re(self, patron, anadido):
        pat = re.compile(patron); self._uno(pat, patron)
        self.t = pat.sub(lambda m: anadido + m.group(0), self.t)

    def quita_re(self, patron):
        pat = re.compile(patron, re.S); self._uno(pat, patron)
        self.t = pat.sub("", self.t)

    def todas(self, viejo, nuevo):
        """Sustituye todas las apariciones (al menos una). Devuelve cuántas."""
        pat = self._pat(viejo)                     # tolera saltos de línea dentro de la expresión
        k = len(pat.findall(self.t))
        assert k >= 1, viejo
        self.t = pat.sub(lambda m: nuevo, self.t)
        self.n += 1
        return k

    def todas_re(self, patron, nuevo):
        pat = re.compile(patron)
        k = len(pat.findall(self.t))
        assert k >= 1, patron
        self.t = pat.sub(nuevo, self.t)
        self.n += 1
        return k

    def mueve_item(self, cabeza, antes_de, abre_viejo, abre_nuevo):
        """Mueve un \\item de una lista (el que empieza con «cabeza») para dejarlo justo antes de «antes_de»,
        y cambia su arranque. Cada uno debe aparecer una sola vez."""
        i = self.t.index(cabeza); assert self.t.count(cabeza) == 1
        j = self.t.index("\\item[", i + 1)
        bloque = self.t[i:j]
        assert bloque.count(abre_viejo) == 1, abre_viejo
        resto = self.t[:i] + self.t[j:]
        assert resto.count(antes_de) == 1, antes_de
        k = resto.index(antes_de)
        self.t = resto[:k] + bloque.replace(abre_viejo, abre_nuevo) + resto[k:]
        self.n += 1

    def quita(self, viejo):
        pat = re.compile(self._pat(viejo).pattern + r"\s*"); self._uno(pat, viejo)
        self.t = pat.sub("", self.t)


# ------------------------------------------------------------------ inglés
def ingles():
    d = Doc(os.path.join(V4, "main_en.tex"))
    # resumen
    d.tras("only one keeps a margin whose interval excludes zero.",
           "At that level, shifting activations along the separating axis changes the model's answer more than random\n"
           "directions do in two of four models, one of them in a post hoc run.")
    d.quita("The numbers are preliminary until they are compared with an independent hand-written implementation.")
    d.cambia("We read this as a small signal with known confounds, and outline", "We outline")
    # contribuciones
    d.tras("They show where the label is linearly readable with and without the statement.",
           prosa(r"""\item An intervention at Level~B that shifts the mean over Lean tokens along the difference of class
           means. It changes the model's answer more than random directions do in Qwen3-4B, where the run is post hoc,
           and in OLMo-2, under a rule fixed in advance. Under the same rule it does not meet the criterion in
           Llama-3.1 or in Gemma-3."""))
    # 2.1
    d.cambia("We read our own results under the warning in their title and make no causal claim.",
             prosa(r"""We read our probing results under the warning in their title. The only causal evidence in this
             paper is the intervention at Level~B, which meets its criterion in two of four models, one of them post hoc."""))
    # S1 en Readouts
    d.tras(r"Readout~(ii) takes the mean over the Lean tokens at a layer fixed in advance, $\lfloor 2L/3 \rfloor$.",
           prosa(r"""In the prompt the question comes after the Lean block, so readout~(ii) cannot depend on it. We
           checked this by extracting the activations again without the question; the cosine with the original ones is
           at least 0.9993 in every model and at both levels."""))
    # tab:controles
    d.tras(r"(a numeral, a relation)\\",
           r"Combined: one classifier on the n-gram and cross-surface features & separation available to the two surface feature sets together\\")
    # 2.2
    d.cambia("Every control at Level~B was computed against the last-token probe only, and none was computed for the second readout.",
             "The controls above were computed against the last-token probe.")
    # bloques nuevos del Nivel B
    nuevo = prosa(r"""\paragraph{Controls at the second readout.}
    After the analyses above we computed the same controls for the second readout, under a rule written before running
    them. The analysis is exploratory and post hoc. At the mean over Lean tokens, \vr{full} exceeds the n-gram control,
    the cross-surface control and the model's own P(Yes) in all four models, with every interval above zero
    (Table~\ref{tab:bcontroles2}). Over P(Yes) the margin is +0.105 \ic{0.070}{0.142} in Qwen3-4B, +0.134
    \ic{0.086}{0.187} in OLMo-2, +0.174 \ic{0.129}{0.218} in Llama-3.1 and +0.335 \ic{0.275}{0.392} in Gemma-3.

    We also trained a single classifier on the n-gram and cross-surface features together. On its own it reaches 0.787,
    and \vr{full} at the second readout stays above it in the four models; the smallest margin is +0.072
    \ic{0.023}{0.123}, in OLMo-2. At the last token, in contrast, \vr{full} cannot be told apart from this combined
    control in three models, and in Gemma-3 the control is ahead (−0.104 \ic{−0.164}{−0.045}). The second-readout
    margins hold on the 309 pairs without the numeral edits.""") + r"""

\begin{table}[h]
\centering
\caption{Level B controls at the second readout (mean over Lean tokens), 377 pairs. The n-gram, cross-surface and combined classifiers reach 0.729, 0.688 and 0.787 on their own. Exploratory and post hoc.}
\label{tab:bcontroles2}
\vspace{2pt}
{\footnotesize\setlength{\tabcolsep}{2pt}
\begin{tabular}{@{}lccccc@{}}
\toprule
\vr{full} minus & AUROC & n-grams & cross-surface & P(Yes) & combined\\
\midrule
""" + filas_s3() + r"""
\bottomrule
\end{tabular}}
\end{table}

""" + prosa(r"""\paragraph{Shifting the mean along the separating axis.}
    A decodable label need not be used \citep{elazar2021amnesic}. We therefore intervened, first in Qwen3-4B as an exploratory analysis and then
    in the other three models under a rule fixed before running them. At every layer but the last we take the
    difference between the class means of the second readout, estimated out of fold. We then shift all Lean tokens
    along that direction, so that their mean coordinate travels toward the opposite class by the full distance between
    the class means, and we read P(Yes). The control applies the same shift along 20 random directions. A model meets
    the criterion if the drop in the paired AUROC of P(Yes) exceeds the mean random drop with a 95\% interval above
    zero, and also exceeds each of the 20 random drops. The class means are estimated on the training rows of five folds grouped by source file. The sign of the shift comes from the label of each row, so the intervention uses the labels of the rows it is evaluated on. The hooks act on the embeddings and on the output of every block but the last, in the same forward pass. The target is set layer by layer, so the shift does not accumulate. The random directions are Gaussian vectors scaled to unit length, drawn separately for each layer, and they receive a shift of the same size and sign. P(Yes) is the probability of Yes divided by that of Yes plus No, and the intervals resample the 256 origins. Adding a difference of means to the activations is the basis of contrastive activation addition \citep{rimsky2024steering}, and the comparison with random directions follows the control of \citet{elazar2021amnesic}.

    Qwen3-4B meets it. The AUROC of P(Yes) falls from 0.838 to 0.688, a drop of +0.145 \ic{0.112}{0.177} over the
    random mean, and no random direction reaches it. That run was designed after an earlier null, described below, so
    it is post hoc. Of the three models tested under the rule fixed in advance, OLMo-2 meets the criterion (0.717 to
    0.432; +0.270 \ic{0.233}{0.309}), and Llama-3.1 and Gemma-3 do not. In both, the drop exceeds the random mean
    (+0.102 \ic{0.072}{0.132} and +0.115 \ic{0.077}{0.153}), but 2 and 6 of the 20 random directions lower the AUROC as
    much or more. In Gemma-3 the model's own P(Yes) barely separates the pairs to begin with (0.590), and the rule had
    flagged that case in advance. In Llama-3.1 the direction built from \vr{lean\_only} moves the answer as much as the
    one built from \vr{full} (difference +0.015 \ic{−0.029}{0.057}), so there the effect cannot be attributed to the
    statement. A shift four times larger takes the AUROC below 0.5 in the four models (Table~\ref{tab:bintervencion}
    and Figure~\ref{fig:bintervencion}).

    An earlier intervention gave a null. In Qwen3-4B we fixed, on the Lean tokens and at every layer, the coordinate
    along the logistic-probe direction of the fixed layer at its mean. P(Yes) did not change more than with a random
    direction (−0.009 \ic{−0.026}{0.008}). That operation is a one-direction relative of linear concept erasure \citep{ravfogel2020null,belrose2023leace}. The two interventions differ in the direction and in the operation, so the null cannot be attributed to the direction alone. In a
    related setting, \citet{geometry} report that difference-of-means directions are more causally implicated than
    those of logistic probes in most of their conditions, in two LLaMA-2 models and with additive shifts.""") + r"""

\begin{figure}[!ht]
\centering
\includegraphics[width=\linewidth]{figuras_v5/intervencion_nivel_b.pdf}
\caption{Level B intervention. Top: drop in the paired AUROC of P(Yes) when the mean over Lean tokens is shifted toward the opposite class by the full distance between class means. Each grey tick is one of 20 random directions given the same shift, the diamond is the direction built from \vr{lean\_only}, and the coloured marker is the difference-of-means direction with its 95\% interval. The criterion asks for an interval above zero in the first column and for no tick at or to the right of the coloured marker. Bottom: paired AUROC of P(Yes) as the shift grows, for the difference-of-means direction (colour) and for five random directions (grey). Filled markers are models run under a rule fixed in advance; the open markers are Qwen3-4B, which is post hoc.}
\label{fig:bintervencion}
\end{figure}

\begin{table}[h]
\centering
\caption{Level B intervention, 377 pairs. Paired AUROC of P(Yes) with no intervention and after shifting the mean over Lean tokens toward the opposite class by the full distance between class means, along the difference-of-means direction at every layer but the last. ``Random'' is the same shift along 20 random directions (mean; maximum of the drop). The criterion asks for an interval above zero in the sixth column and for no random direction with an equal or larger drop. The last two columns give the AUROC after shifts two and four times larger. Qwen3-4B is post hoc; the other three models were run under a rule fixed in advance. The base differs slightly from the stored P(Yes) of Table~\ref{tab:controlesnivel} (0.839, 0.726, 0.729, 0.560), because the intervention runs in batches and bfloat16 arithmetic is not reproducible to the last digit.}
\label{tab:bintervencion}
\vspace{2pt}
{\footnotesize\setlength{\tabcolsep}{3pt}
\resizebox{\linewidth}{!}{\begin{tabular}{@{}lcccccccc@{}}
\toprule
 & base & shifted & drop & random & drop minus random mean & random $\geq$ probe & $\times 2$ & $\times 4$\\
\midrule
""" + filas_s5("of") + r"""
\bottomrule
\end{tabular}}}
\end{table}

"""
    d.antes(r"\paragraph{The effect concentrates in family C", nuevo)
    # tab:conjunta
    d.cambia("n-grams of both texts, which only Qwen3-4B exceeds;", "at the last token, n-grams of both texts, which only Qwen3-4B exceeds;")
    # frase de lectura
    d.tras("but it is a development batch and part of its effect is surface.",
           prosa(r"""In two of four models, one of them under a rule fixed in advance, a shift along the axis on which
           the second readout separates the classes changes the answer more than the same shift along random directions. This does not show what the model computes, and it
           does not hold in the other two. A shift can also change the output through a pathway other than the one it targets \citep{makelov2024subspace}."""))
    # 2.3
    d.cambia("The probes are linear and the evidence is correlational.", "The probes are linear and their evidence is correlational.")
    d.cambia("We have not intervened on any direction.",
             prosa(r"""We intervened on one family of directions, at Level~B only. The intervention meets its criterion
             in two of four models, and the run in Qwen3-4B is post hoc."""))
    # decisiones a posteriori
    d.antes("They are labelled as such where they appear.",
            "The controls at the second readout and the two interventions at Level~B came later still, between 11 and 13\nNovember. ")
    # 2.4
    d.tras("probing cannot answer and an intervention along the probe direction could.",
           prosa(r"""At Level~B we ran such an intervention on a related direction, the difference of class means at
           each layer. It changes the answer more than random directions do in two of four models, one of them in a post hoc run."""))
    # apéndice
    d.tras("The hypothesis of the draft protocol was changed to require both surface controls.",
           prosa(r"""\item[11 Nov] The Level~B controls at the second readout, a check that the mean over Lean tokens
           does not depend on the question, and the ablation of one direction in Qwen3-4B were run under a rule written
           and approved that day, before running them. They are exploratory and post hoc.""") + "\n" +
           prosa(r"""\item[12 Nov] Under the same rule, the last-token gap was recomputed, as an exploratory analysis,
           on activations extracted without the question. At Level~A the gap is not established without the question in
           any of the four models. At Level~B it does not require the question in any of them.""") + "\n" +
           prosa(r"""\item[11--12 Nov] The shift intervention was run in Qwen3-4B. Its rule was written after the
           controls and the null of the ablation had been seen, so the run is post hoc.""") + "\n" +
           prosa(r"""\item[12--13 Nov] The same intervention was run in OLMo-2, Llama-3.1 and Gemma-3 with the same
           script and the same criterion. The rule was written after the Qwen3-4B result had been seen and before
           anything was computed in those models. It is not part of the preregistration.""") + "\n" +
           prosa(r"""\item[13 Nov] The probability mass on Yes and No under the intervention was computed from the stored
           outputs of the intervention runs, under a rule written after their results and before computing it. No
           model was run. It is exploratory and post hoc."""))
    # sexta tanda (13 nov): P1 y P4 de la revisión ciega
    d.tras("so condition~(b) is largely met.",
           prosa(rf"""At that readout, however, the stacked control does not reach \vr{{lean\_only}} on its own. Its AUROC is
           {lista_a("apilado", "and")} in the order of Table~\ref{{tab:a}}, against {lista_a("auroc_solo_lean", "and")}.
           The stacker is a logistic regression on the inner out-of-fold scores of the two probes, and there
           \vr{{nl\_only}} is read as the mean over the statement tokens at the same fixed layer
           ({lista_a("auroc_solo_nl", "and")}). Condition~(b) is therefore no stricter than a positive gap at
           readout~(ii)."""))
    d.tras("which serves as a check of the pipeline.",
           prosa(r"""Certification compares each edit with its original and never tries to prove the theorem. A faithful
           edit is certified when Lean proves that the edited hypothesis or conclusion is equivalent to the original one,
           with structural tactics only. An unfaithful edit is certified by a witness, that is, concrete values that
           separate the two formulas and that Lean checks. Witnesses are searched only when every variable involved is a
           natural, integer, rational or real number."""), sep="\n\n")
    d.cambia("""A review by a language model, not by a human, then found originals that were themselves not faithful to
             their statement and edits that were equivalent in fact, and those 31 pairs were removed.""",
             prosa(rf"""A review by a language model, not by a human, then removed {N_EXC} pairs. In {N_OB} the original
             was itself not faithful to its statement. In {N_EQ}, all of family~A, the witness separates the formulas but
             the edit only adds a case in which the conclusion holds trivially, so the two statements say the same. One
             pair is in both groups."""))
    # séptima tanda (13 nov): compuerta de superficie, criterio «firma»
    d.tras("and the pairs were declared a development batch.",
           prosa(rf"""A surface check fixed in advance also failed. On the {CS["n_pares"]} certified pairs, a logistic
           regression on unigrams and bigrams of the Lean alone reaches a paired AUROC of
           {f3(CS["auroc_pareada_solo_lean"])}, an excess of {f3(CS["exceso_firma"])} over an unsupervised baseline,
           against a limit of {CS["umbral_firma"]:.2f}."""))
    # citas verificadas (13 nov, tercera tanda)
    d.cambia("in five open-weight models and then test", "in five open-weight models and, in three of them, test")
    # secundarios de la intervención (13 nov, segunda tanda)
    d.tras("so there the effect cannot be attributed to the statement.",
           prosa(r"""In Gemma-3 the interval of the same difference also includes zero (+0.049 \ic{−0.003}{0.100}). The
           secondary analyses are in Appendix~\ref{app:intervencion}."""))
    d.antes_re(r"\\section\{[^}]*\}\\label\{app:protocolo\}",
               r"\section{Secondary results of the Level~B intervention}\label{app:intervencion}" + "\n\n" +
               prosa(r"""Table~\ref{tab:bsecundarios} gives the secondary analyses of the intervention. The placebo runs
               the hooks with the clean coordinate as target, and its AUROC stays within 0.02 of the base in every model.
               Moving the coordinate to the common mean lowers the AUROC more than random directions do in the four
               models. Swapping it with the coordinate of the twin does so in three, and in Gemma-3 the interval includes
               zero. The direction built from \vr{full} moves the answer more than the one built from \vr{lean\_only} in
               Qwen3-4B and OLMo-2, and in Llama-3.1 and Gemma-3 that interval includes zero. With shifts two and four
               times larger, the direction exceeds its five random directions in every model except Gemma-3.

               The probability mass on Yes and No at the answer position is at least 0.982 without intervention, and the shift changes it by less than 0.001 in every model, along the difference of means and along the random directions. The model therefore keeps answering yes or no under the shift. This measure is near its ceiling, so it rules out only that kind of damage. It was computed on 13 November under a rule written before looking at it.""") + r"""

\begin{table}[h]
\centering
\caption{Level B intervention, secondary analyses, 377 pairs. Placebo: paired AUROC of P(Yes) with the hooks active and the clean coordinate as target. The next three columns are differences in the drop of that AUROC, with 95\% intervals. The last column is the probability on Yes plus No at the answer position, without intervention and with the shift. Post hoc in Qwen3-4B; under a rule fixed in advance in the other three models.}
\label{tab:bsecundarios}
\vspace{2pt}
{\footnotesize\setlength{\tabcolsep}{3pt}
\resizebox{\linewidth}{!}{\begin{tabular}{@{}lcccccc@{}}
\toprule
 & placebo & swap with twin, minus random & common mean, minus random & \vr{full} minus \vr{lean\_only} direction & larger shifts exceed their 5 random & Yes/No mass, base; shifted\\
\midrule
""" + filas_sec("yes", "no") + r"""
\bottomrule
\end{tabular}}}
\end{table}

""")
    # octava tanda (lector Residency, aprobada el 13 nov): A1, la conclusión del resumen sube; A2, remisión a tab:conjunta
    d.cambia("Exploratory maps place the separation over the Lean tokens, in the upper layers. No level alone supports "
             "the claim that faithfulness is linearly decodable from frozen models beyond the Lean alone.",
             "Exploratory maps place the separation over the Lean tokens, in the upper layers.")
    d.tras("between a linear probe reading the statement with the formalization and one reading the formalization alone.",
           "No level alone supports the claim that faithfulness is linearly decodable from frozen models beyond the Lean alone.")
    d.tras(r"Llama-3.1 or in Gemma-3. \end{enumerate}",
           r"Table~\ref{tab:conjunta} gives the status of the evidence at each level.", sep="\n\n")
    # novena tanda (13 nov): P5, P6 y P8 de la revisión ciega
    d.antes("By the rule, the first three rows",
            "The rule decides on the interval of the five-seed estimate. The permutation $p$ is reported beside it and is not corrected across the four models. ")
    d.antes(r"\begin{table}[h] \centering \caption{Level B, 377 pairs. Top:",
            prosa(rf"""Folds are grouped by source file, whereas the paired AUROC and the bootstrap take the origin as their
            unit. With the 189 source files as the unit instead, the gap is
            {lista_ic([x["secundarios"]["central_bootstrap_por_archivo"]["diferencia"] for x in ARCH], "and")}, in the
            order of Table~\ref{{tab:b}}.""") + "\n\n")
    d.cambia("in any of the four models. At Level~B it does not require",
             prosa(rf"""in any of the four models. The models are Qwen3-4B, OLMo-2, Llama-3.1 and Gemma-3, and the gaps
             are {lista_ic(SP, "and")}. At Level~B it does not require"""))
    # décima tanda (lector Residency, aprobada el 13 nov): A3, tabla de pares de ejemplo, armada desde ejemplos_nivel_b.json
    d.tras("Within C, C2 changes a numeral and C3 changes something else.",
           r"""Table~\ref{tab:bejemplos} shows one pair from each.

\begin{table}[h]
\centering
\caption{Level B, one pair per family of edit, chosen by a fixed rule: the pair with the fewest edited tokens in its two members and, among ties, the first in the index. Only the edited fragment of each Lean statement is shown. The unfaithful member carries the faithful edit as well. The statement of the C2 pair is cut after its first sentence.}
\label{tab:bejemplos}
\vspace{2pt}
{\footnotesize
\begin{tabularx}{\linewidth}{@{}lX>{\raggedright\arraybackslash}p{0.2\linewidth}>{\raggedright\arraybackslash}p{0.2\linewidth}>{\raggedright\arraybackslash}p{0.2\linewidth}@{}}
\toprule
 & Statement & Original & Faithful edit & Unfaithful edit\\
\midrule
""" + filas_ejemplos() + r"""
\bottomrule
\end{tabularx}}
\end{table}""")
    # undécima tanda (13 nov): P7 de la revisión ciega (sin P7.5)
    d.tras("pairs the Lean with the statement of a different problem of similar length.",
           "Each variant has its own probe, so the \\vr{nl\\_mismatched} probe is trained and scored on the mismatched prompts.")
    d.tras("in 1972 of its 2000 prompts.",
           f"The extraction covers the {N_FILAS_DS} rows of the benchmark in the four variants, and the analysis keeps the 450 that\ncompile.")
    d.cambia("with gaps of +0.046, +0.060, +0.060 and +0.030 \\ic{−0.006}{0.065} in the order of",
             prosa(f"with gaps of {lista_sens('and')} in the order of"))
    d.antes("In both models the label is linearly decodable from the \\vr{full} activations",
            "The rule of this level calls the result positive if the interval of $\\D$, from a bootstrap over statements, lies\nentirely above zero. ")
    d.cambia("gives +0.15354 \\ic{0.12102}{0.18714}.", "gives $\\D$ = +0.15354 \\ic{0.12102}{0.18714} in Qwen3-4B.")
    d.cambia("since \\vr{nl\\_only} probes reach 0.61 to 0.74.", "since \\vr{nl\\_only} probes reach 0.61 to 0.74 in the four replication models.")
    # duodécima tanda (lector Residency, aprobada el 13 nov): A5, encabezados de tab:bsecundarios en varias líneas
    # para que \resizebox no encoja la tabla; mismas palabras, mismas celdas
    d.cambia(r"""& placebo & swap with twin, minus random & common mean, minus random & \vr{full} minus \vr{lean\_only} direction & larger shifts exceed their 5 random & Yes/No mass, base; shifted\\""",
             r"""& placebo & \shortstack{swap with twin,\\minus random} & \shortstack{common mean,\\minus random} & \shortstack{\vr{full} minus\\\vr{lean\_only} direction} & \shortstack{larger shifts exceed\\their 5 random} & \shortstack{Yes/No mass,\\base; shifted}\\""")
    # decimotercera tanda (13 nov): apéndice de prompts y controles (observación 9 de la revisión ciega)
    d.tras("\\usepackage{url}", "\\usepackage{upquote}   % acentos graves rectos en el bloque verbatim del prompt")
    d.tras("so the \\vr{nl\\_mismatched} probe is trained and scored on the mismatched prompts.",
           "The exact prompts and the definitions of the controls are in Appendix~\\ref{app:definiciones}.")
    d.antes_re(r"\\section\{[^}]*\}\\label\{app:protocolo\}",
               r"\section{Prompts and controls}\label{app:definiciones}" + "\n\n" +
               prosa(r"""\paragraph{Prompts.}
               The \vr{full} prompt is the text below, with the statement and the formalization in place of the
               braces.""") + "\n" + BLOQUE_PROMPT +
               prosa(r"""\vr{lean\_only} omits the first block and \vr{nl\_only} omits the second. The text goes into
               each model's chat template as a single user turn, with the generation prompt added. Thinking is disabled
               in the templates that offer that switch, those of Qwen3 and Goedel-Prover-V2. The Lean tokens of
               readout~(ii) are those whose characters fall inside the code block. The three levels use the same
               templates.

               \paragraph{Mismatched statement.}
               The rows are sorted by the length of their statement and cut into five bands. Within each band the
               statements are permuted at random with a fixed seed, until no row keeps its own statement or one of the
               same group. At Level~C, where the groups are large, the permutation is completed with swaps under the
               same criterion.

               \paragraph{P(Yes).}
               We append \vr{**Answer:} to the prompt and read the probabilities of Yes and of No for the next token.
               P(Yes) is the first divided by their sum.

               \paragraph{Surface controls.}
               The n-gram control is a logistic regression ($C = 1$) on binary unigrams and bigrams of the Lean and of
               the statement, kept when they occur in at least two training rows. It also receives the log length of
               each text, in characters and in tokens. At Level~A it reads the Lean alone.

               The cross-surface control is a logistic regression on standardised features that relate the two texts.
               Three of them count numerals: those of the Lean statement that are absent from the natural-language
               statement, those that are present, and those of the statement that the Lean lacks. A second group
               crosses each order relation of the Lean, and $\neq$, with the presence in the statement of relation
               words such as ``at most'' or ``positive''. The rest are the single-letter identifiers of the Lean that
               the statement lacks, the overlap between the single-letter identifiers of the two texts, and the counts
               of subscripts, primes and negations in the Lean.

               The combined control puts the two feature sets into one logistic regression. All three controls use the
               folds and seeds of the probes.""") + "\n\n")
    # decimocuarta tanda (lector Residency, aprobada el 13 nov): fig:escaner rehecha para leerse mejor, a página propia.
    # Mismos mapas (reconstruidos y comprobados, ver figuras_v5/mapas_desde_escaner.py) y mismo pie.
    d.cambia(r"\begin{figure}[t] \centering \includegraphics[width=\linewidth]{figuras_v3/escaner2d_modelos.pdf}",
             "\\begin{figure}[p]\n\\centering\n\\includegraphics[width=\\linewidth]{figuras_v5/escaner2d_modelos_v5.pdf}")
    # decimoquinta tanda (13 nov): S7, Holm e intervención sin C2 (regla_S7_holm_sin_C2.md)
    d.tras("The secondary analyses are in Appendix~\\ref{app:intervencion}.",
           prosa(r"""A natural worry is that the shift only moves a surface feature, because the numeral edits can be
           told apart without any model. The worry does not hold. When those pairs are set aside, the effect in Qwen3-4B
           and OLMo-2 is about the same as before, and Llama-3.1 and Gemma-3 still fall short of the criterion
           (Appendix~\ref{app:intervencion}). The directions were estimated with the numeral pairs among the training
           rows, however, so the result is narrower than it sounds. It shows that the shift changes the answer on pairs
           that alter no numeral, and it leaves open how much of the direction those pairs shaped."""))
    d.cambia("The permutation $p$ is reported beside it and is not corrected across the four models.",
             f"The permutation $p$ is reported beside it. Once corrected across the four models by Holm's method, only that of Qwen3-4B stays below 0.05, at {H_QWEN}; the other three rise to {H_RESTO}.")
    d.antes_re(r"\\section\{[^}]*\}\\label\{app:definiciones\}",
               prosa(r"""\paragraph{Without the numeral pairs.}
               We asked whether the intervention owes its effect to the one family that surface features already
               separate. We repeated the analysis on the 309 pairs that remain when the numeral edits are removed, from
               the stored outputs and with no new run. The reading does not change in any model
               (Table~\ref{tab:bsinc2}). In Qwen3-4B and OLMo-2 the drop still exceeds every random direction, and its
               margin over the random mean is about the same. Llama-3.1 comes closer than it did, since a single random
               direction now matches it where two did before, but one is enough to fail the criterion. Gemma-3 stays
               where it was. The analysis is exploratory and post hoc. Its rule was written on 13 November, after the
               results on all pairs were known and before this split was computed.""") + r"""

\begin{table}[h]
\centering
\caption{Level B intervention on the 309 pairs without numeral edits. Columns as in Table~\ref{tab:bintervencion}. Exploratory and post hoc.}
\label{tab:bsinc2}
\vspace{2pt}
{\footnotesize
\begin{tabular}{@{}lcccc@{}}
\toprule
 & base & shifted & drop minus random mean & random $\geq$ probe\\
\midrule
""" + filas_sinc2("of") + r"""
\bottomrule
\end{tabular}}
\end{table}

""")
    d.tras("No model was run. It is exploratory and post hoc.",
           prosa(r"""\item[13 Nov] The permutation $p$-values of Level~B were corrected by Holm's method, and the
           intervention was re-read on the pairs without numeral edits, from the stored outputs. The rule was written
           after the results on all pairs and before the split was computed. The Holm values were already known when it
           was written, because they follow from the printed $p$-values. Both are exploratory and post hoc."""))
    # ---- decimosexta tanda (13 nov, 13:42): introducción que explica el experimento, Xena y Bastounis, «Lean code alone»
    d.tras("errors of this kind can hide wherever a statement compiles and is not the one intended.",
           prosa(r"""The gap is now visible at scale. Of some 290 Lean-bearing papers in a recent batch of AI-generated
           mathematics, about 38 do not state the paper's main theorem \citep{xena2026checked}, and a proof checked in
           Lean need not match the written argument it accompanies \citep{bastounis2026lost}."""))
    d.antes("Most work measures faithfulness from the outside.",
            prosa(r"""The experiment is simple to state. We show a frozen language model a natural-language statement and
            a Lean~4 formalization of it, and ask: ``Is this formalization faithful? Answer Yes or No.'' We keep its
            answer as a control. What we study is its activations, on which we train a linear probe to separate faithful
            from unfaithful formalizations. We then repeat the run with the statement removed, so that the model sees
            only the Lean code and the same question. That second question has no answer, because nothing in the prompt
            says what the code was meant to capture. The probe trained there therefore measures something else, namely
            whatever the Lean code gives away on its own through style, length or vocabulary. For that reason we never
            report the AUROC of one probe taken on its own. Every result is a gap, the AUROC of the probe that reads the
            statement with the Lean code minus that of the probe that reads the Lean code alone. A positive gap is
            evidence that the representation carries information about the \emph{relation} between the two texts.""") + "\n\n")
    d.quita_re(r"The difficulty is that the Lean text alone is informative\..*?\\emph\{relation\} between\s+the two texts\.\s*")
    d.sustituciones = [d.todas("the Lean Alone", "the Lean Code Alone"), d.todas("the Lean alone", "the Lean code alone"),
                       d.todas("Lean text alone", "Lean code alone")]
    assert not re.search(r"Lean\s+alone\b", d.t, re.I), re.findall(r".{40}Lean\s+alone\b.{20}", d.t, re.S | re.I)
    # ---- decimoséptima tanda (13 nov, 13:48): cinco correcciones de texto aprobadas por Carlos
    d.cambia(r"The base differs slightly from the stored P(Yes) of Table~\ref{tab:controlesnivel} (0.839, 0.726, 0.729, 0.560), because the intervention runs in batches and bfloat16 arithmetic is not reproducible to the last digit.",
             r"The base was recomputed in the intervention run and differs from the stored P(Yes) of Table~\ref{tab:controlesnivel} (0.839, 0.726, 0.729, 0.560) by up to 0.030, in Gemma-3.")
    d.cambia(r"``Is this formalization faithful?''. \vr{lean\_only}", r"``Is this formalization faithful? Answer Yes or No.'' \vr{lean\_only}")
    d.cambia("Neither produces it.",
             "Neither produces a positive gap. Under readout~(ii) with random weights and on the embeddings the gap is\nnegative, with intervals below zero.")
    d.tras("models, and the run in Qwen3-4B is post hoc.",
           prosa(r"""One control was not run. Directions built as differences of means from shuffled labels would show how
           much of the effect comes from fitting a direction to these activations at all."""))
    d.cambia("We outline a confirmatory test on Lean statements written", "We outline a confirmatory test on statements written")
    # ---- decimoctava tanda (13 nov, 14:06): lo que salió de la lectura completa de la v5
    d.cambia("The gap is now visible at scale.", "The problem is now visible at scale.")       # «gap» es el término técnico
    d.cambia("Qwen3-4B meets it.", "Qwen3-4B meets the criterion.")
    d.tras("readout or in both, and we record them as a deviation.",
           "Both clauses were already in the document signed on 4 November.")
    d.cambia(r"gives $\D$ = +0.15354 \ic{0.12102}{0.18714} in Qwen3-4B.", r"gives $\D$ = +0.154 \ic{0.121}{0.187} in Qwen3-4B.")
    d.cambia("keep a positive margin and Gemma does not.", "keep a positive margin and Gemma-3 does not.")
    # «the Lean» como sustantivo suelto pasa a «the Lean code», para que el texto diga lo mismo que el título
    d.sustituciones.append(d.todas_re(r"\bthe Lean\b(?!~)(?!\s+(?:code|tokens|text|statements?|formalization|block)\b)", "the Lean code"))
    # ---- decimonovena tanda (13 nov, tarde): repositorio publicado; «Code and data» en presente, con URL y commit
    # La sustitución anterior duplicó «code» en el título («the Lean code Code Alone»): se corrige aquí (comentario y \title).
    assert d.todas("the Lean code Code Alone", "the Lean Code Alone") == 2
    d.cambia(r"The repository will be released with the preprint at \url{https://github.com/cmorregof}. It will contain the decision rules with their hashes and times, the certified pairs, the cross-surface features, and every result file cited here.",
             "The repository is at \\url{https://github.com/cmorregof/faithfullness}, and the numbers reported here correspond to\n"
             "commit \\vr{ea66bad}. It contains the decision rules with their hashes and times, the certified pairs, the\n"
             "cross-surface features, every result file cited here and the project log. It does not contain the extracted\n"
             "activations or the CriticLeanBench texts.")
    d.cambia("which will be released with the repository, and nothing here replaces it.",
             r"which is in the repository (\vr{probes/BITACORA.md}), and nothing here replaces it.")
    # ---- vigésima tanda (13 nov, tarde): figuras con los rótulos «Lean code alone». Mismos datos y mismo dibujo
    # (figuras_v5/figuras_v5.py, copia de figuras_v3.py con los rótulos nuevos); fig:escaner y fig:bintervencion se
    # regeneraron con el mismo nombre de archivo. Los pies no cambian.
    for f in ("curvas_por_modelo", "forest_nivel_a", "nivel_b"):
        d.cambia(r"\includegraphics[width=\linewidth]{figuras_v3/%s.pdf}" % f, r"\includegraphics[width=\linewidth]{figuras_v5/%s.pdf}" % f)
    # ---- vigesimoprimera tanda (13 nov, tarde): «Contamination» fecha también el Nivel A. arXiv:2507.06181 v1 es del
    # 8 jul 2025; su sección 3.1.2 nombra las fuentes de los enunciados y dice que los enunciados en Lean salen de un
    # conjunto público. Fechas de los modelos: paper_adecuacion/fuentes/verificacion_fechas_formal_conjectures.md.
    d.tras("where the problems were known and their formalizations were not.",
           "At Level~A, CriticLeanBench was posted on 8 July 2025, after the release of seven of the eight models and a week\n"
           "before Goedel-Prover-V2-8B. Its labels are new in that release. Its problems, in contrast, come from earlier\n"
           "collections such as Omni-MATH, AIME and U-MATH, and its authors report taking the Lean statements from a public\n"
           "dataset, so both may be older than the labels.")
    # ---- vigesimosegunda tanda (13 nov, 15:33): lectura final cruzada (dos lectores independientes y el chat).
    # Detalle y origen de cada cambio: revisiones/lectura_final_2026-11-13.md
    # A. contradicciones
    d.cambia("They are most of those of the last-token readout at Level~A, where Llama-3.1 is negative, and that of Gemma-3 at the last token at Level~B.",
             prosa(r"""They include most of those of the last-token readout at Level~A, where Llama-3.1 is negative, that
             of DeepSeek-Prover-V2 at the fixed layer, and that of Gemma-3 at the last token at Level~B."""))
    d.cambia("the fixed-layer direction separates the classes. Whether the model uses that direction is a causal question",
             "each layer's probe direction separates the classes. Whether the model uses such a direction is a causal question")
    d.cambia("the runs on Qwen3-8B and on Llama at Level~C", "the runs on Qwen3-8B at Level~A and on Llama-3.1 at Level~C")
    d.cambia("Neither produces a positive gap.", "Neither produces a gap whose interval lies above zero.")
    d.cambia("and neither null control shows a positive gap.", "and neither null control shows a gap whose interval lies above zero.")
    # B. imprecisiones y prosa rota
    d.cambia("We intervened on one family of directions, at Level~B only. The intervention meets its criterion in two of four models, and the run in Qwen3-4B is post hoc.",
             prosa(r"""We intervened along two directions, at Level~B only. The shift along the difference of means meets
             its criterion in two of four models, and the run in Qwen3-4B is post hoc. The ablation along the probe
             direction gave a null."""))
    d.tras("It changes the answer more than random directions do in two of four models, one of them in a post hoc run.",
           "An earlier intervention along the logistic-probe direction, in Qwen3-4B, gave a null.")
    d.cambia("In Qwen3-4B at Level~B the model's own answer separates as well as the probe.",
             "In Qwen3-4B at Level~B, at the last token, the model's own answer separates as well as the probe.")
    d.cambia("It does not yet address a P(Yes) that matches the probe.", "It does not yet address a P(Yes) that matches the probe at the last token.")
    d.cambia(r"\item Dating of every Level~B origin against", r"\item Dating of the Level~B origins against")
    d.cambia("were run next under the same early rule", "were run next under an early version of the rule")
    d.cambia("the third version written that day", "the third version written on 4 November")
    d.cambia("is at least 0.9993 in every model and at both levels.", "is at least 0.9993 in each of the four models checked, at Levels~A and~B.")
    d.cambia("was measured at both, and it also depends on the readout.", "was measured at both readouts, and it depends on the readout.")
    d.quita(r"A shift four times larger takes the AUROC below 0.5 in the four models (Table~\ref{tab:bintervencion} and Figure~\ref{fig:bintervencion}).")
    d.tras(r"In Gemma-3 the interval of the same difference also includes zero (+0.049 \ic{−0.003}{0.100}).",
           prosa(r"""A shift four times larger takes the AUROC below 0.5 in the four models
           (Table~\ref{tab:bintervencion} and Figure~\ref{fig:bintervencion})."""))
    d.cambia(r"On average it lies between 0.49 and 0.52 there, and the one exception is Qwen3-8B, at 0.521 \ic{0.501}{0.543}.",
             prosa(r"""On average it lies between 0.49 and 0.52 there, and only in Qwen3-8B does the interval exclude 0.5
             (0.521 \ic{0.501}{0.543})."""))
    d.cambia(r"(Figure~\ref{fig:b}, bottom) shows why.", r"(Figure~\ref{fig:b}, bottom) looks inside family C.")
    d.cambia("The worry does not hold.", "The stored outputs do not bear it out.")
    d.cambia(r"\vr{nl\_only} reaches 0.61 to 0.74 in the four replication models", r"\vr{nl\_only} reaches 0.61 to 0.74 at the last token in the four replication models")
    d.cambia(r"\vr{nl\_only} probes reach 0.61 to 0.74 in the four replication models", r"\vr{nl\_only} probes reach 0.61 to 0.74 at the last token in the four replication models")
    d.cambia("in any of the four models. The models are Qwen3-4B, OLMo-2, Llama-3.1 and Gemma-3, and the gaps are",
             "in any of the four models checked (Qwen3-4B, OLMo-2, Llama-3.1 and Gemma-3). The gaps are")
    d.quita("Both clauses were already in the document signed on 4 November.")
    d.tras("and the other is that the global claim is read within a single readout.",
           "Both clauses were already in the document signed on 4 November.")
    d.cambia("first in Qwen3-4B as an exploratory analysis and then", "first in Qwen3-4B, post hoc, and then")
    d.cambia("In two of four models, one of them under a rule fixed in advance, a shift",
             "In two of four models, one of them under a rule fixed in advance and the other post hoc, a shift")
    d.cambia("It leaves readout~(ii) unchanged, with gaps of", "It leaves the reading of readout~(ii) unchanged, with gaps of")
    d.cambia(r"Table~\ref{tab:bejemplos} shows one pair from each.", r"Table~\ref{tab:bejemplos} shows one pair from each of A, B, C2 and C3.")
    d.mueve_item(r"\item[12 Nov] Under the same rule,", r"\item[12--13 Nov] The same intervention", "Under the same rule,", "Under the rule of 11 November,")
    d.tras("and the permutation test swaps roles within each pair.", r"The controls are listed in Table~\ref{tab:controles}.")
    d.cambia(r"under~(ii) and +0.029 \ic{−0.000}{0.058} under~(i). Its estimand", r"under~(ii) and +0.029 \ic{−0.000}{0.058} under~(i) (Figure~\ref{fig:forest}). Its estimand")
    d.cambia("lies entirely above zero. In both models the label", r"lies entirely above zero (Table~\ref{tab:c}). In both models the label")
    # C. efectos de las sustituciones de «Lean code» y cosméticos
    d.cambia("the Lean code-only probe", "the Lean-only probe")
    d.cambia("as well as against the Lean code. The statements", "as well as against the Lean code alone. The statements")
    d.cambia("0.729, 0.688 and 0.787 on their own. Exploratory and post hoc.", r"0.729, 0.688 and 0.787 on their own. The AUROC column is that of \vr{full}. Exploratory and post hoc.")
    for viejo, nuevo in (("standardised", "standardized"), ("normalised", "normalized"), ("generalise", "generalize"), ("memorisation", "memorization")):
        d.todas(viejo, nuevo)
    # E. decididos por Carlos («aplica todo eso»)
    d.cambia("the numeral edits inside C are a surface effect.}", "the numeral edits inside C are matched by a surface control.}")
    d.cambia("and are reported as a failed first attempt.", "and are reported as discovery runs with no confirmatory weight.")
    d.cambia("``Not run'' means the control does not exist for that level.", "``Not run'' means there is no result for that level.")
    # ---- vigesimotercera tanda (14 nov): segunda lectura cruzada (dos lectores independientes). Aprobada por Carlos (secciones 1 y 3).
    d.todas(r"Where a control was run, it is reported as \vr{full} minus the control; not every", r"Where a control was run, it is reported as its own AUROC or as \vr{full} minus the control; not every")
    d.todas("we never report the AUROC of one probe taken on its own. Every result is a gap,", "we never interpret the AUROC of one probe taken on its own. Every headline result is a gap,")
    d.todas("A positive gap is evidence that", r"A positive gap that survives the controls of Table~\ref{tab:controles} is evidence that")
    d.todas("changes the model's answer more than random directions do in two of four models", "changes the model's answer more than any of 20 random directions does in two of four models")
    d.todas("the model's answer more than random directions do in Qwen3-4B", "the model's answer more than any of 20 random directions does in Qwen3-4B")
    d.todas("the answer more than random directions do in two of four models", "the answer more than any of 20 random directions does in two of four models")
    d.todas("No model, however, survives", "Even so, no model survives")
    d.todas("which leaves 406 rows. It leaves the reading of readout~(ii) unchanged, with gaps of", "which leaves 406 rows. The reading of readout~(ii) does not change, with gaps of")
    d.cambia("direction those pairs shaped. An earlier intervention gave a null.", "direction those pairs shaped.\n\nAn earlier intervention gave a null.")
    d.todas("families A and B are not distinguishable from zero", "the margin in families A and B is not distinguishable from zero")
    d.todas("include zero. They include most of those", "include zero. Among them are most of those")
    d.todas("those of the Lean statement that are absent from the natural-language statement", "those of the Lean code that are absent from the natural-language statement")
    # ---- vigesimocuarta tanda (14 nov): historia del lote del Nivel B (bitácora, D-2) y cifras del Nivel B sin la pregunta (s2b). Aprobada por Carlos.
    d.todas("No certifiable batch of triplets could be built, and the pairs were declared a development batch. A surface check fixed in advance also failed.",
            "On 4 November, after a provisional surface check had failed, the pairs were declared its development batch. No certifiable batch of triplets could then be built, so the pairs are the only evidence at this level. The surface check fixed in advance also failed on the certified pairs.")
    d.todas("did not pass (0.706 on the certified pairs), and the batch was declared exploratory.",
            "did not pass (0.706 on the certified pairs). The batch had been declared a development batch on 4 November.")
    d.todas("At Level~B it does not require the question in any of them.",
            r"At Level~B the last-token gap without the question is positive in the four models. The gaps are +0.176 \ic{0.113}{0.236}, +0.113 \ic{0.061}{0.166}, +0.128 \ic{0.067}{0.189} and +0.102 \ic{0.047}{0.156}, in the same order.")
    # ---- vigesimoquinta tanda (14 nov): observaciones del profesor Riaño (cómo leer AUROC y figuras, orden del resumen, trabajo futuro). Aprobada por Carlos.
    d.tras(r"reported with a 95\% bootstrap interval over groups \citep{efron}.",
           prosa(r"""The AUROC is the probability that a probe scores a faithful formalization above an unfaithful one. It is 0.5
           for a probe that guesses and 1 for one that never errs, and it summarizes sensitivity and specificity over every
           decision threshold. A gap of +0.05 therefore means that adding the statement raises that probability by five points."""))
    d.todas(r"\caption{Layer by layer. AUROC of a linear probe", r"\caption{Layer by layer. How to read it: where the coloured curve runs above the grey one, the statement adds to what the Lean code alone gives away at that layer. AUROC of a linear probe")
    d.todas(r"\caption{Level A, readout (ii). Filled points", r"\caption{Level A, readout (ii). How to read it: a point to the right of zero is a positive gap, and it counts as established only if its whole interval lies to the right. Filled points")
    d.todas("in the five general-purpose models. Each cell is", "in the five general-purpose models. How to read it: darker cells are positions and layers where the classes separate better, and the right panel is darker where the statement adds. Each cell is")
    d.todas(r"\caption{Level B intervention. Top: drop", r"\caption{Level B intervention. How to read it: a drop to the right of zero means the shift made P(Yes) separate the pairs worse, and a model meets the criterion when its coloured marker lies to the right of every grey tick. Top: drop")
    d.todas(r"\caption{Level B. Top: paired AUROC of the probe", r"\caption{Level B. How to read it: the length of the bar between the grey marker and the coloured one is the gap of that model. Top: paired AUROC of the probe")
    d.todas("No level alone supports the claim that faithfulness is linearly decodable from frozen models beyond the Lean code alone. On 450 CriticLeanBench", "On 450 CriticLeanBench")
    d.todas("in the upper layers. We outline a confirmatory test", "in the upper layers. No level alone supports the claim that faithfulness is linearly decodable from frozen models beyond the Lean code alone. We outline a confirmatory test")
    d.tras("An earlier intervention along the logistic-probe direction, in Qwen3-4B, gave a null.",
           "\n" + prosa(r"""Three things remain to be done. The confirmatory test of Appendix~\ref{app:protocolo} needs statements written
           after the models and after this pilot. The intervention was run at Level~B only, and Levels~A and~C still lack
           one. The maps rest on a single seed."""))
    # ---- vigesimosexta tanda (17 nov): cabos que esperaban a las figuras nuevas (rótulos, pie del escáner) y la composición de los pares.
    d.todas(r"random $\geq$ probe", r"random $\geq$ direction")
    d.todas("Left: the prompt with statement and Lean.", "Left: the prompt with statement and Lean code.")
    d.todas("the size of single-cell noise by a normal approximation, and for the difference", "the size of single-cell noise by a normal approximation to the null of permuted labels, and for the difference")
    d.tras("Lean certifies the other as not equivalent, and it is the unfaithful member.",
           "The unfaithful edit is applied on top of the faithful one, so the two members differ only in the unfaithful edit.")
    return d


# ------------------------------------------------------------------ español
def espanol():
    d = Doc(os.path.join(V4, "main_es.tex"))
    d.tras("solo uno conserva un margen cuyo intervalo excluye el cero.",
           "Allí, desplazar las activaciones por el eje que separa las clases cambia la respuesta del modelo más que\n"
           "direcciones al azar en dos de cuatro modelos, uno post hoc.")
    d.quita("Las cifras son preliminares hasta compararlas con una implementación independiente escrita a mano.")
    d.cambia("Lo leemos como una señal pequeña con factores de confusión conocidos, y esbozamos", "Esbozamos")
    d.tras("Muestran dónde la etiqueta es legible linealmente con el enunciado y sin él.",
           prosa(r"""\item Una intervención en el Nivel~B que desplaza la media sobre los tokens de Lean a lo largo de la
           diferencia de medias de clase. Cambia la respuesta del modelo más que las direcciones al azar en Qwen3-4B,
           donde la corrida es post hoc, y en OLMo-2, con una regla fijada de antemano. Con esa misma regla no cumple
           el criterio en Llama-3.1 ni en Gemma-3."""))
    d.cambia("Leemos nuestros propios resultados bajo la advertencia de su título y no hacemos ninguna afirmación causal.",
             prosa(r"""Leemos nuestros resultados de sondeo bajo la advertencia de su título. La única evidencia causal
             de este artículo es la intervención del Nivel~B, que cumple su criterio en dos de los cuatro modelos, uno de ellos post hoc."""))
    d.tras(r"La lectura~(ii) toma la media sobre los tokens de Lean en una capa fijada de antemano, $\lfloor 2L/3 \rfloor$.",
           prosa(r"""En el prompt la pregunta va después del bloque de Lean, así que la lectura~(ii) no puede depender
           de ella. Lo comprobamos extrayendo de nuevo las activaciones sin la pregunta; el coseno con las originales es
           de al menos 0.9993 en todos los modelos y en los dos niveles."""))
    d.tras(r"(un numeral, una relación)\\",
           r"Combinado: un solo clasificador con los rasgos de n-gramas y de superficie cruzada & separación al alcance de los dos conjuntos de rasgos de superficie juntos\\")
    d.cambia("Todos los controles del Nivel~B se calcularon solo frente a la sonda del último token, y ninguno se calculó para la segunda lectura.",
             "Los controles anteriores se calcularon frente a la sonda del último token.")
    nuevo = prosa(r"""\paragraph{Controles en la segunda lectura.}
    Después de los análisis anteriores calculamos los mismos controles para la segunda lectura, con una regla escrita
    antes de correrlos. El análisis es exploratorio y post hoc. En la media sobre los tokens de Lean, \vr{full} supera
    al control de n-gramas, al de superficie cruzada y al P(Yes) del propio modelo en los cuatro modelos, con todos los
    intervalos por encima de cero (Tabla~\ref{tab:bcontroles2}). Sobre P(Yes) el margen es de +0.105 \ic{0.070}{0.142}
    en Qwen3-4B, +0.134 \ic{0.086}{0.187} en OLMo-2, +0.174 \ic{0.129}{0.218} en Llama-3.1 y +0.335 \ic{0.275}{0.392}
    en Gemma-3.

    También entrenamos un solo clasificador con los rasgos de n-gramas y los de superficie cruzada juntos. Por sí solo
    llega a 0.787, y \vr{full} en la segunda lectura queda por encima de él en los cuatro modelos; el margen menor es
    de +0.072 \ic{0.023}{0.123}, en OLMo-2. En el último token, en cambio, \vr{full} no se distingue de ese control
    combinado en tres modelos, y en Gemma-3 el control va por delante (−0.104 \ic{−0.164}{−0.045}). Los márgenes de la
    segunda lectura se mantienen en los 309 pares sin las ediciones de numeral.""") + r"""

\begin{table}[h]
\centering
\caption{Controles del Nivel B en la segunda lectura (media sobre los tokens de Lean), 377 pares. Los clasificadores de n-gramas, de superficie cruzada y combinado llegan por sí solos a 0.729, 0.688 y 0.787. Exploratorio y post hoc.}
\label{tab:bcontroles2}
\vspace{2pt}
{\footnotesize\setlength{\tabcolsep}{2pt}
\begin{tabular}{@{}lccccc@{}}
\toprule
\vr{full} menos & AUROC & n-gramas & superficie cruzada & P(Yes) & combinado\\
\midrule
""" + filas_s3() + r"""
\bottomrule
\end{tabular}}
\end{table}

""" + prosa(r"""\paragraph{Desplazar la media a lo largo del eje que separa.}
    Que una etiqueta sea decodificable no implica que el modelo la use \citep{elazar2021amnesic}. Por eso intervinimos, primero en Qwen3-4B como
    análisis exploratorio y después en los otros tres modelos con una regla fijada antes de correr. En cada capa menos
    la última tomamos la diferencia entre las medias de clase de la segunda lectura, estimada fuera de partición. Luego
    desplazamos todos los tokens de Lean a lo largo de esa dirección, de modo que su coordenada media recorra hacia la
    clase contraria la distancia completa entre las medias de clase, y leemos P(Yes). El control aplica el mismo
    desplazamiento a lo largo de 20 direcciones al azar. Un modelo cumple el criterio si la caída de la AUROC pareada
    de P(Yes) supera a la media de las caídas al azar con un intervalo del 95\% por encima de cero, y supera además a
    cada una de las 20. Las medias de clase se estiman con las filas de entrenamiento de cinco particiones agrupadas por archivo fuente. El signo del desplazamiento sale de la etiqueta de cada fila, así que la intervención usa las etiquetas de las filas sobre las que se evalúa. Los ganchos actúan sobre los embeddings y sobre la salida de cada bloque menos el último, en la misma pasada. El objetivo se fija capa por capa, así que el desplazamiento no se acumula. Las direcciones al azar son vectores gaussianos llevados a norma uno, sorteados aparte para cada capa, y reciben un desplazamiento del mismo tamaño y signo. P(Yes) es la probabilidad de Yes dividida por la de Yes más No, y los intervalos remuestrean los 256 orígenes. Sumar una diferencia de medias a las activaciones es la base de la adición de activaciones por contraste \citep{rimsky2024steering}, y la comparación con direcciones al azar sigue el control de \citet{elazar2021amnesic}.

    Qwen3-4B lo cumple. La AUROC de P(Yes) baja de 0.838 a 0.688, una caída de +0.145 \ic{0.112}{0.177} sobre la media
    al azar, y ninguna dirección al azar la alcanza. Esa corrida se diseñó después de un nulo anterior, que se describe
    abajo, así que es post hoc. De los tres modelos probados con la regla fijada de antemano, OLMo-2 cumple el criterio
    (de 0.717 a 0.432; +0.270 \ic{0.233}{0.309}), y Llama-3.1 y Gemma-3 no. En los dos la caída supera a la media al
    azar (+0.102 \ic{0.072}{0.132} y +0.115 \ic{0.077}{0.153}), pero 2 y 6 de las 20 direcciones al azar bajan la AUROC
    tanto o más. En Gemma-3 el P(Yes) del modelo apenas separa los pares de partida (0.590), y la regla había señalado
    ese caso de antemano. En Llama-3.1 la dirección construida con \vr{lean\_only} mueve la respuesta tanto como la
    construida con \vr{full} (diferencia de +0.015 \ic{−0.029}{0.057}), así que allí el efecto no puede atribuirse al
    enunciado. Con un desplazamiento cuatro veces mayor la AUROC queda por debajo de 0.5 en los cuatro modelos
    (Tabla~\ref{tab:bintervencion} y Figura~\ref{fig:bintervencion}).

    Una intervención anterior dio un nulo. En Qwen3-4B fijamos en su media, sobre los tokens de Lean y en todas las
    capas, la coordenada a lo largo de la dirección de la sonda logística de la capa fija. P(Yes) no cambió más que con
    una dirección al azar (−0.009 \ic{−0.026}{0.008}). Esa operación es pariente, con una sola dirección, del borrado lineal de conceptos \citep{ravfogel2020null,belrose2023leace}. Las dos intervenciones difieren en la dirección y en la operación, así que el nulo no puede atribuirse solo a la dirección. En un problema afín, \citet{geometry} informan que las direcciones de diferencia de medias están más
    implicadas causalmente que las de las sondas logísticas en la mayoría de sus condiciones, en dos modelos LLaMA-2 y con desplazamientos aditivos.""") + r"""

\begin{figure}[!ht]
\centering
\includegraphics[width=\linewidth]{figuras_v5/intervencion_nivel_b_es.pdf}
\caption{Intervención del Nivel B. Arriba: caída de la AUROC pareada de P(Yes) cuando la media sobre los tokens de Lean se desplaza hacia la clase contraria, la distancia completa entre las medias de clase. Cada marca gris es una de 20 direcciones al azar con el mismo desplazamiento, el rombo es la dirección construida con \vr{lean\_only} y el marcador de color es la dirección de diferencia de medias con su intervalo del 95\%. El criterio pide un intervalo por encima de cero en la primera columna y ninguna marca a la altura del marcador de color o a su derecha. Abajo: AUROC pareada de P(Yes) a medida que crece el desplazamiento, para la dirección de diferencia de medias (color) y para cinco direcciones al azar (gris). Los marcadores llenos son modelos corridos con una regla fijada de antemano; los huecos son de Qwen3-4B, que es post hoc.}
\label{fig:bintervencion}
\end{figure}

\begin{table}[h]
\centering
\caption{Intervención del Nivel B, 377 pares. AUROC pareada de P(Yes) sin intervenir y tras desplazar la media sobre los tokens de Lean hacia la clase contraria, la distancia completa entre las medias de clase, a lo largo de la dirección de diferencia de medias en cada capa menos la última. «Al azar» es el mismo desplazamiento a lo largo de 20 direcciones al azar (media; máximo de la caída). El criterio pide un intervalo por encima de cero en la sexta columna y ninguna dirección al azar con una caída igual o mayor. Las dos últimas columnas dan la AUROC con desplazamientos dos y cuatro veces mayores. Qwen3-4B es post hoc; los otros tres modelos se corrieron con una regla fijada de antemano. La base difiere un poco del P(Yes) guardado de la Tabla~\ref{tab:controlesnivel} (0.839, 0.726, 0.729, 0.560), porque la intervención corre en lotes y la aritmética en bfloat16 no se reproduce hasta el último dígito.}
\label{tab:bintervencion}
\vspace{2pt}
{\footnotesize\setlength{\tabcolsep}{3pt}
\resizebox{\linewidth}{!}{\begin{tabular}{@{}lcccccccc@{}}
\toprule
 & base & desplazada & caída & al azar & caída menos media al azar & al azar $\geq$ sonda & $\times 2$ & $\times 4$\\
\midrule
""" + filas_s5("de") + r"""
\bottomrule
\end{tabular}}}
\end{table}

"""
    d.antes(r"\paragraph{El efecto se concentra en la familia C", nuevo)
    d.cambia("n-gramas de ambos textos, que solo Qwen3-4B supera;", "en el último token, n-gramas de ambos textos, que solo Qwen3-4B supera;")
    d.tras("pero es un lote de desarrollo y parte de su efecto es de superficie.",
           prosa(r"""En dos de los cuatro modelos, uno de ellos con la regla fijada de antemano, un desplazamiento por
           el eje en el que la segunda lectura separa las clases cambia la respuesta más que el mismo desplazamiento por direcciones al azar. Esto no muestra qué calcula el modelo, y no se
           sostiene en los otros dos. Un desplazamiento también puede cambiar la salida por una vía distinta de la que se quiere tocar \citep{makelov2024subspace}."""))
    d.cambia("Las sondas son lineales y la evidencia es correlacional.", "Las sondas son lineales y su evidencia es correlacional.")
    d.cambia("No hemos intervenido sobre ninguna dirección.",
             prosa(r"""Intervinimos sobre una sola familia de direcciones, y solo en el Nivel~B. La intervención cumple su
             criterio en dos de los cuatro modelos, y la corrida en Qwen3-4B es post hoc."""))
    d.antes("Están rotulados como tales donde aparecen.",
            "Los controles en la segunda lectura y las dos intervenciones del Nivel~B llegaron después, entre el 11 y el 13\nde noviembre. ")
    d.tras("que el sondeo no puede responder y que una intervención a lo largo de la dirección de la sonda sí podría.",
           prosa(r"""En el Nivel~B hicimos una intervención de ese tipo sobre una dirección afín, la diferencia de medias
           de clase en cada capa. Cambia la respuesta más que las direcciones al azar en dos de los cuatro modelos, uno de ellos en una corrida post hoc."""))
    d.tras("La hipótesis del borrador de protocolo pasó a exigir los dos controles de superficie.",
           prosa(r"""\item[11 nov] Los controles del Nivel~B en la segunda lectura, una comprobación de que la media
           sobre los tokens de Lean no depende de la pregunta y la ablación de una dirección en Qwen3-4B se corrieron
           con una regla escrita y aprobada ese mismo día, antes de correrlos. Son exploratorios y post hoc.""") + "\n" +
           prosa(r"""\item[12 nov] Con la misma regla se recalculó, como análisis exploratorio, la brecha del último
           token con activaciones extraídas sin la pregunta. En el Nivel~A la brecha no se establece sin la pregunta en
           ninguno de los cuatro modelos. En el Nivel~B no requiere la pregunta en ninguno.""") + "\n" +
           prosa(r"""\item[11--12 nov] La intervención de desplazamiento se corrió en Qwen3-4B. Su regla se escribió
           después de ver los controles y el nulo de la ablación, así que la corrida es post hoc.""") + "\n" +
           prosa(r"""\item[12--13 nov] La misma intervención se corrió en OLMo-2, Llama-3.1 y Gemma-3 con el mismo
           guion y el mismo criterio. La regla se escribió después de ver el resultado de Qwen3-4B y antes de calcular
           nada en esos modelos. No forma parte del prerregistro.""") + "\n" +
           prosa(r"""\item[13 nov] La masa de probabilidad en Yes y No bajo la intervención se calculó con las salidas
           guardadas de las corridas de la intervención, con una regla escrita después de sus resultados y antes de
           calcularla. No se corrió ningún modelo. Es exploratoria y post hoc."""))
    d.tras("de modo que la condición~(b) se cumple en gran medida.",
           prosa(rf"""En esa lectura, sin embargo, el control apilado no alcanza a \vr{{lean\_only}} por sí solo. Su AUROC
           es {lista_a("apilado", "y")} en el orden de la Tabla~\ref{{tab:a}}, frente a {lista_a("auroc_solo_lean", "y")}.
           El apilado es una regresión logística sobre los puntajes internos fuera de partición de las dos sondas, y
           allí \vr{{nl\_only}} se lee como la media sobre los tokens del enunciado en la misma capa fija
           ({lista_a("auroc_solo_nl", "y")}). La condición~(b), por tanto, no es más estricta que una brecha positiva
           en la lectura~(ii)."""))
    d.tras("lo que sirve de comprobación del pipeline.",
           prosa(r"""La certificación compara cada edición con su original y nunca intenta probar el teorema. Una edición
           adecuada queda certificada cuando Lean prueba que la hipótesis o la conclusión editada equivale a la original,
           solo con tácticas estructurales. Una edición inadecuada queda certificada por un testigo, es decir, valores
           concretos que separan las dos fórmulas y que Lean comprueba. Los testigos se buscan solo cuando todas las
           variables que intervienen son números naturales, enteros, racionales o reales."""), sep="\n\n")
    d.cambia("""Una revisión hecha por un modelo de lenguaje, no por una persona, encontró después originales que no eran
             adecuados a su enunciado y ediciones que eran equivalentes de hecho, y esos 31 pares se retiraron.""",
             prosa(rf"""Una revisión hecha por un modelo de lenguaje, no por una persona, retiró después {N_EXC} pares. En
             {N_OB} el original no era adecuado a su enunciado. En {N_EQ}, todos de la familia~A, el testigo separa las
             fórmulas, pero la edición solo añade un caso en el que la conclusión se cumple trivialmente, así que los dos
             enunciados dicen lo mismo. Un par está en los dos grupos."""))
    d.tras("y los pares se declararon lote de desarrollo.",
           prosa(rf"""Tampoco pasó una comprobación de superficie fijada de antemano. En los {CS["n_pares"]} pares
           certificados, una regresión logística sobre unigramas y bigramas del Lean solo alcanza una AUROC pareada de
           {f3(CS["auroc_pareada_solo_lean"])}, un exceso de {f3(CS["exceso_firma"])} sobre una línea base no
           supervisada, frente a un límite de {CS["umbral_firma"]:.2f}."""))
    d.cambia("en cinco modelos de pesos abiertos y luego ponen a prueba si", "en cinco modelos de pesos abiertos y, en tres de ellos, ponen a prueba si")
    d.tras("así que allí el efecto no puede atribuirse al enunciado.",
           prosa(r"""En Gemma-3 el intervalo de esa misma diferencia también incluye el cero (+0.049
           \ic{−0.003}{0.100}). Los análisis secundarios están en el Apéndice~\ref{app:intervencion}."""))
    d.antes_re(r"\\section\{[^}]*\}\\label\{app:protocolo\}",
               r"\section{Resultados secundarios de la intervención del Nivel~B}\label{app:intervencion}" + "\n\n" +
               prosa(r"""La Tabla~\ref{tab:bsecundarios} da los análisis secundarios de la intervención. El placebo hace
               trabajar los ganchos con la coordenada limpia como objetivo, y su AUROC queda a menos de 0.02 de la base
               en todos los modelos. Llevar la coordenada a la media común baja la AUROC más que las direcciones al azar
               en los cuatro modelos. Intercambiarla con la de la pareja lo hace en tres, y en Gemma-3 el intervalo
               incluye el cero. La dirección construida con \vr{full} mueve la respuesta más que la construida con
               \vr{lean\_only} en Qwen3-4B y en OLMo-2, y en Llama-3.1 y Gemma-3 ese intervalo incluye el cero. Con
               desplazamientos dos y cuatro veces mayores, la dirección supera a sus cinco direcciones al azar en todos
               los modelos menos en Gemma-3.

               La masa de probabilidad en Yes y No en la posición de la respuesta es de al menos 0.982 sin intervenir, y el desplazamiento la cambia en menos de 0.001 en todos los modelos, tanto a lo largo de la diferencia de medias como de las direcciones al azar. El modelo, por tanto, sigue respondiendo sí o no bajo el desplazamiento. Esta medida está cerca de su techo, así que solo descarta ese tipo de daño. Se calculó el 13 de noviembre con una regla escrita antes de mirarla.""") + r"""

\begin{table}[h]
\centering
\caption{Intervención del Nivel B, análisis secundarios, 377 pares. Placebo: AUROC pareada de P(Yes) con los ganchos activos y la coordenada limpia como objetivo. Las tres columnas siguientes son diferencias en la caída de esa AUROC, con intervalos del 95\%. La última columna es la probabilidad de Yes más la de No en la posición de la respuesta, sin intervenir y con el desplazamiento. Post hoc en Qwen3-4B; con una regla fijada de antemano en los otros tres modelos.}
\label{tab:bsecundarios}
\vspace{2pt}
{\footnotesize\setlength{\tabcolsep}{3pt}
\resizebox{\linewidth}{!}{\begin{tabular}{@{}lcccccc@{}}
\toprule
 & placebo & intercambio con la pareja, menos azar & media común, menos azar & dirección \vr{full} menos \vr{lean\_only} & desplazamientos mayores superan a sus 5 al azar & masa en Yes/No, base; desplazada\\
\midrule
""" + filas_sec("sí", "no") + r"""
\bottomrule
\end{tabular}}}
\end{table}

""")
    # octava tanda (lector Residency, aprobada el 13 nov): A1, la conclusión del resumen sube; A2, remisión a tab:conjunta
    d.cambia("Unos mapas exploratorios sitúan la separación sobre los tokens de Lean, en las capas superiores. Ningún nivel "
             "sostiene por sí solo la afirmación de que la adecuación es decodificable linealmente en modelos congelados "
             "más allá del Lean solo.",
             "Unos mapas exploratorios sitúan la separación sobre los tokens de Lean, en las capas superiores.")
    d.tras("entre una sonda lineal que lee enunciado y formalización y otra que lee solo la formalización.",
           "Ningún nivel sostiene por sí solo la afirmación de que la adecuación es decodificable linealmente en modelos\n"
           "congelados más allá del Lean solo.")
    d.tras(r"Llama-3.1 ni en Gemma-3. \end{enumerate}",
           r"La Tabla~\ref{tab:conjunta} recoge el estado de la evidencia en cada nivel.", sep="\n\n")
    # novena tanda (13 nov): P5, P6 y P8 de la revisión ciega
    d.antes("Por la regla, las tres primeras filas",
            "La regla decide por el intervalo de la estimación con cinco semillas. El valor $p$ de la permutación se reporta al lado y no está corregido entre los cuatro modelos. ")
    d.antes(r"\begin{table}[h] \centering \caption{Nivel B, 377 pares. Arriba:",
            prosa(rf"""Las particiones se agrupan por archivo fuente, mientras que la AUROC pareada y el bootstrap toman el
            origen como unidad. Con los 189 archivos fuente como unidad, la brecha es
            {lista_ic([x["secundarios"]["central_bootstrap_por_archivo"]["diferencia"] for x in ARCH], "y")}, en el
            orden de la Tabla~\ref{{tab:b}}.""") + "\n\n")
    d.cambia("en ninguno de los cuatro modelos. En el Nivel~B no requiere",
             prosa(rf"""en ninguno de los cuatro modelos. Los modelos son Qwen3-4B, OLMo-2, Llama-3.1 y Gemma-3, y las
             brechas son {lista_ic(SP, "y")}. En el Nivel~B no requiere"""))
    # décima tanda (lector Residency, aprobada el 13 nov): A3, tabla de pares de ejemplo, armada desde ejemplos_nivel_b.json
    d.tras("Dentro de C, C2 cambia un numeral y C3 cambia otra cosa.",
           r"""La Tabla~\ref{tab:bejemplos} muestra un par de cada una.

\begin{table}[h]
\centering
\caption{Nivel B, un par por familia de edición, elegido con una regla fija: el par con menos tokens editados entre sus dos miembros y, en caso de empate, el primero del índice. Solo se muestra el fragmento editado de cada enunciado en Lean. El miembro inadecuado lleva también la edición adecuada. El enunciado del par de C2 se corta tras su primera frase. Los enunciados van en su inglés original.}
\label{tab:bejemplos}
\vspace{2pt}
{\footnotesize
\begin{tabularx}{\linewidth}{@{}lX>{\raggedright\arraybackslash}p{0.2\linewidth}>{\raggedright\arraybackslash}p{0.2\linewidth}>{\raggedright\arraybackslash}p{0.2\linewidth}@{}}
\toprule
 & Enunciado & Original & Edición adecuada & Edición inadecuada\\
\midrule
""" + filas_ejemplos() + r"""
\bottomrule
\end{tabularx}}
\end{table}""")
    # undécima tanda (13 nov): P7 de la revisión ciega (sin P7.5)
    d.tras("empareja el Lean con el enunciado de otro problema de longitud similar.",
           "Cada variante tiene su propia sonda, así que la de \\vr{nl\\_mismatched} se entrena y se evalúa sobre los prompts desemparejados.")
    d.tras("en 1972 de sus 2000 prompts.",
           f"La extracción cubre las {N_FILAS_DS} filas del benchmark en las cuatro variantes, y el análisis se queda con las 450 que\ncompilan.")
    d.cambia("con brechas de +0.046, +0.060, +0.060 y +0.030 \\ic{−0.006}{0.065}, en el orden de",
             prosa(f"con brechas de {lista_sens('y')}, en el orden de"))
    d.antes("En ambos modelos la etiqueta es decodificable linealmente de las activaciones de \\vr{full}",
            "La regla de este nivel llama positivo al resultado si el intervalo de $\\D$, con bootstrap sobre enunciados, queda\npor completo por encima de cero. ")
    d.cambia("da +0.15354 \\ic{0.12102}{0.18714}.", "da $\\D$ = +0.15354 \\ic{0.12102}{0.18714} en Qwen3-4B.")
    d.cambia("\\vr{nl\\_only} alcanzan de 0.61 a 0.74.", "\\vr{nl\\_only} alcanzan de 0.61 a 0.74 en los cuatro modelos de réplica.")
    # duodécima tanda (lector Residency, aprobada el 13 nov): A5, encabezados de tab:bsecundarios en varias líneas
    # para que \resizebox no encoja la tabla; mismas palabras, mismas celdas
    d.cambia(r"""& placebo & intercambio con la pareja, menos azar & media común, menos azar & dirección \vr{full} menos \vr{lean\_only} & desplazamientos mayores superan a sus 5 al azar & masa en Yes/No, base; desplazada\\""",
             r"""& placebo & \shortstack{intercambio con la\\pareja, menos azar} & \shortstack{media común,\\menos azar} & \shortstack{dirección \vr{full}\\menos \vr{lean\_only}} & \shortstack{desplazamientos mayores\\superan a sus 5 al azar} & \shortstack{masa en Yes/No,\\base; desplazada}\\""")
    # decimotercera tanda (13 nov): apéndice de prompts y controles (observación 9 de la revisión ciega)
    d.tras("\\usepackage{url}", "\\usepackage{upquote}   % acentos graves rectos en el bloque verbatim del prompt")
    d.tras("así que la de \\vr{nl\\_mismatched} se entrena y se evalúa sobre los prompts desemparejados.",
           "Los prompts exactos y las definiciones de los controles están en el Apéndice~\\ref{app:definiciones}.")
    d.antes_re(r"\\section\{[^}]*\}\\label\{app:protocolo\}",
               r"\section{Prompts y controles}\label{app:definiciones}" + "\n\n" +
               prosa(r"""\paragraph{Prompts.}
               El prompt \vr{full} es el texto de abajo, con el enunciado y la formalización en el lugar de las
               llaves.""") + "\n" + BLOQUE_PROMPT +
               prosa(r"""\vr{lean\_only} omite el primer bloque y \vr{nl\_only} omite el segundo. El texto entra en la
               plantilla de chat de cada modelo como un solo turno de usuario, con el prompt de generación añadido. El
               razonamiento se desactiva en las plantillas que ofrecen ese interruptor, las de Qwen3 y
               Goedel-Prover-V2. Los tokens de Lean de la lectura~(ii) son aquellos cuyos caracteres caen dentro del
               bloque de código. Los tres niveles usan las mismas plantillas.

               \paragraph{Enunciado desemparejado.}
               Las filas se ordenan por la longitud de su enunciado y se cortan en cinco bandas. Dentro de cada banda
               los enunciados se permutan al azar con una semilla fija, hasta que ninguna fila conserve su propio
               enunciado ni uno del mismo grupo. En el Nivel~C, donde los grupos son grandes, la permutación se
               completa con intercambios bajo el mismo criterio.

               \paragraph{P(Yes).}
               Añadimos \vr{**Answer:} al prompt y leemos las probabilidades de Yes y de No para el token siguiente.
               P(Yes) es la primera dividida por la suma de las dos.

               \paragraph{Controles de superficie.}
               El control de n-gramas es una regresión logística ($C = 1$) sobre unigramas y bigramas binarios del
               Lean y del enunciado, que se conservan cuando aparecen en al menos dos filas de entrenamiento. Recibe
               además el logaritmo de la longitud de cada texto, en caracteres y en tokens. En el Nivel~A lee solo el
               Lean.

               El control de superficie cruzada es una regresión logística sobre rasgos estandarizados que relacionan
               los dos textos. Tres de ellos cuentan numerales: los del enunciado en Lean que faltan en el enunciado
               en lenguaje natural, los que están presentes y los del enunciado que el Lean no tiene. Un segundo grupo
               cruza cada relación de orden del Lean, y $\neq$, con la presencia en el enunciado de palabras de
               relación como «at most» o «positive». Los demás son los identificadores de una letra del Lean que el
               enunciado no tiene, el solapamiento entre los identificadores de una letra de los dos textos, y los
               conteos de subíndices, primas y negaciones en el Lean.

               El control combinado reúne los dos conjuntos de rasgos en una sola regresión logística. Los tres
               controles usan las particiones y las semillas de las sondas.""") + "\n\n")
    # decimocuarta tanda (lector Residency, aprobada el 13 nov): fig:escaner rehecha para leerse mejor, a página propia.
    # Mismos mapas (reconstruidos y comprobados, ver figuras_v5/mapas_desde_escaner.py) y mismo pie.
    d.cambia(r"\begin{figure}[t] \centering \includegraphics[width=\linewidth]{figuras_v3/escaner2d_modelos_es.pdf}",
             "\\begin{figure}[p]\n\\centering\n\\includegraphics[width=\\linewidth]{figuras_v5/escaner2d_modelos_v5_es.pdf}")
    # decimoquinta tanda (13 nov): S7, Holm e intervención sin C2 (regla_S7_holm_sin_C2.md)
    d.tras("Los análisis secundarios están en el Apéndice~\\ref{app:intervencion}.",
           prosa(r"""Una preocupación natural es que el desplazamiento solo mueva un rasgo de superficie, porque las
           ediciones de numeral se distinguen sin ningún modelo. La preocupación no se sostiene. Cuando se apartan esos
           pares, el efecto en Qwen3-4B y en OLMo-2 es más o menos el mismo que antes, y Llama-3.1 y Gemma-3 siguen sin
           cumplir el criterio (Apéndice~\ref{app:intervencion}). Las direcciones, sin embargo, se estimaron con los
           pares de numeral entre las filas de entrenamiento, así que el resultado es más estrecho de lo que parece.
           Muestra que el desplazamiento cambia la respuesta en pares que no alteran ningún numeral, y deja abierto
           cuánto de la dirección moldearon esos pares."""))
    d.cambia("El valor $p$ de la permutación se reporta al lado y no está corregido entre los cuatro modelos.",
             f"El valor $p$ de la permutación se reporta al lado. Una vez corregido entre los cuatro modelos con el método de Holm, solo el de Qwen3-4B queda por debajo de 0.05, en {H_QWEN}; los otros tres suben a {H_RESTO}.")
    d.antes_re(r"\\section\{[^}]*\}\\label\{app:definiciones\}",
               prosa(r"""\paragraph{Sin los pares de numeral.}
               Preguntamos si la intervención le debe su efecto a la única familia que los rasgos de superficie ya
               separan. Repetimos el análisis en los 309 pares que quedan al quitar las ediciones de numeral, con las
               salidas guardadas y sin ninguna corrida nueva. La lectura no cambia en ningún modelo
               (Tabla~\ref{tab:bsinc2}). En Qwen3-4B y en OLMo-2 la caída sigue superando a todas las direcciones al
               azar, y su margen sobre la media al azar es más o menos el mismo. Llama-3.1 queda más cerca que antes,
               porque ahora la iguala una sola dirección al azar donde antes eran dos, pero una basta para incumplir el
               criterio. Gemma-3 sigue donde estaba. El análisis es exploratorio y post hoc. Su regla se escribió el 13
               de noviembre, después de conocer los resultados con todos los pares y antes de calcular esta
               división.""") + r"""

\begin{table}[h]
\centering
\caption{Intervención del Nivel B en los 309 pares sin ediciones de numeral. Columnas como en la Tabla~\ref{tab:bintervencion}. Exploratorio y post hoc.}
\label{tab:bsinc2}
\vspace{2pt}
{\footnotesize
\begin{tabular}{@{}lcccc@{}}
\toprule
 & base & desplazada & caída menos media al azar & al azar $\geq$ sonda\\
\midrule
""" + filas_sinc2("de") + r"""
\bottomrule
\end{tabular}}
\end{table}

""")
    d.tras("No se corrió ningún modelo. Es exploratoria y post hoc.",
           prosa(r"""\item[13 nov] Los valores $p$ de permutación del Nivel~B se corrigieron con el método de Holm, y la
           intervención se releyó en los pares sin ediciones de numeral, con las salidas guardadas. La regla se escribió
           después de los resultados con todos los pares y antes de calcular la división. Los valores de Holm ya se
           conocían al escribirla, porque se siguen de los valores $p$ impresos. Los dos análisis son exploratorios y
           post hoc."""))
    # ---- decimosexta tanda (13 nov, 13:42): introducción que explica el experimento, Xena y Bastounis, «código de Lean»
    d.tras("pueden esconderse allí donde un enunciado compila y no es el que se quería.",
           prosa(r"""La brecha ya se ve a escala. De unos 290 artículos con Lean en un lote reciente de matemática generada
           por IA, cerca de 38 no enuncian el teorema principal del artículo \citep{xena2026checked}, y una prueba
           comprobada en Lean no tiene por qué coincidir con el argumento escrito al que acompaña
           \citep{bastounis2026lost}."""))
    d.antes("La mayor parte de los trabajos mide la adecuación",
            prosa(r"""El experimento se enuncia en pocas líneas. Le mostramos a un modelo de lenguaje congelado un
            enunciado en lenguaje natural y una formalización suya en Lean~4, y le preguntamos: «Is this formalization
            faithful? Answer Yes or No.» Su respuesta la guardamos como control. Lo que estudiamos son sus activaciones,
            sobre las que entrenamos una sonda lineal que separe las formalizaciones adecuadas de las inadecuadas.
            Después repetimos la corrida sin el enunciado, de modo que el modelo ve solo el código de Lean y la misma
            pregunta. Esa segunda pregunta no tiene respuesta, porque nada en el prompt dice qué debía capturar el
            código. La sonda entrenada allí mide entonces otra cosa, a saber, lo que el código de Lean delata por sí
            solo en su estilo, su longitud o su vocabulario. Por esa razón nunca reportamos la AUROC de una sonda tomada
            aisladamente. Cada resultado es una brecha, la AUROC de la sonda que lee el enunciado junto con el código de
            Lean menos la de la sonda que lee solo el código de Lean. Una brecha positiva es evidencia de que la
            representación lleva información sobre la \emph{relación} entre los dos textos.""") + "\n\n")
    d.quita_re(r"La dificultad está en que el texto en Lean es informativo por sí solo\..*?\\emph\{relación\} entre\s+los dos textos\.\s*")
    # resumen: está en el máximo de 250 palabras, así que aquí «código de Lean» va sin «solo» y sale «en Lean» del cierre
    d.cambia(r"\emph{más allá de lo que delata el Lean solo}", r"\emph{más allá de lo que delata el código de Lean}")
    d.cambia("en modelos congelados más allá del Lean solo.", "en modelos congelados más allá del código de Lean.")
    d.cambia("con enunciados en Lean posteriores a los modelos y a este piloto", "con enunciados posteriores a los modelos y a este piloto")
    # «del Lean solo» contiene «el Lean solo»; «al Lean solo» no
    d.sustituciones = [d.todas("el Lean solo", "el código de Lean solo"), d.todas("al Lean solo", "al código de Lean solo")]
    assert not re.search(r"(?<!código de )Lean\s+solo\b", d.t), re.findall(r".{40}(?<!código de )Lean\s+solo\b.{20}", d.t, re.S)
    # ---- decimoséptima tanda (13 nov, 13:48): cinco correcciones de texto aprobadas por Carlos
    d.cambia(r"La base difiere un poco del P(Yes) guardado de la Tabla~\ref{tab:controlesnivel} (0.839, 0.726, 0.729, 0.560), porque la intervención corre en lotes y la aritmética en bfloat16 no se reproduce hasta el último dígito.",
             r"La base se recalculó en la corrida de la intervención y difiere del P(Yes) guardado de la Tabla~\ref{tab:controlesnivel} (0.839, 0.726, 0.729, 0.560) en hasta 0.030, en Gemma-3.")
    d.cambia(r"«Is this formalization faithful?». \vr{lean\_only}", r"«Is this formalization faithful? Answer Yes or No.» \vr{lean\_only}")
    d.cambia("Ninguno de los dos la produce.",
             "Ninguno de los dos produce una brecha positiva. Con la lectura~(ii) y pesos aleatorios, y sobre los embeddings,\nla brecha es negativa, con intervalos por debajo de cero.")
    d.tras("los cuatro modelos, y la corrida en Qwen3-4B es post hoc.",
           prosa(r"""Un control no se corrió. Direcciones construidas como diferencias de medias con etiquetas barajadas
           mostrarían cuánto del efecto se debe al solo hecho de ajustar una dirección a estas activaciones."""))
    # ---- decimoctava tanda (13 nov, 14:06): lo que salió de la lectura completa de la v5
    d.cambia("La brecha ya se ve a escala.", "El problema ya se ve a escala.")                 # «brecha» es el término técnico
    d.cambia("Qwen3-4B lo cumple.", "Qwen3-4B cumple el criterio.")
    d.tras("un modelo debe pasar en una lectura o en las dos, y las registramos como una desviación.",
           "Las dos cláusulas ya estaban en el documento firmado el 4 de noviembre.")
    d.cambia(r"da $\D$ = +0.15354 \ic{0.12102}{0.18714} en Qwen3-4B.", r"da $\D$ = +0.154 \ic{0.121}{0.187} en Qwen3-4B.")
    d.cambia("conservan un margen positivo y Gemma no.", "conservan un margen positivo y Gemma-3 no.")
    # «el Lean» como sustantivo suelto pasa a «el código de Lean» (también «del» y «al»)
    d.sustituciones.append(d.todas_re(r"\b([Ee]l|del|al) Lean\b(?!~)", r"\1 código de Lean"))
    # ---- decimonovena tanda (13 nov, tarde): repositorio publicado; «Código y datos» en presente, con URL y commit
    d.cambia(r"El repositorio se publicará con el preprint en \url{https://github.com/cmorregof}. Contendrá las reglas de decisión con sus hashes y horas, los pares certificados, los rasgos de superficie cruzada y todos los archivos de resultados citados aquí.",
             "El repositorio está en \\url{https://github.com/cmorregof/faithfullness}, y las cifras reportadas aquí corresponden\n"
             "al commit \\vr{ea66bad}. Contiene las reglas de decisión con sus hashes y horas, los pares certificados, los\n"
             "rasgos de superficie cruzada, todos los archivos de resultados citados aquí y la bitácora del proyecto. No\n"
             "contiene las activaciones extraídas ni los textos de CriticLeanBench.")
    d.cambia("que se publicará con el repositorio, y nada de lo que hay aquí la reemplaza.",
             r"que está en el repositorio (\vr{probes/BITACORA.md}), y nada de lo que hay aquí la reemplaza.")
    # ---- vigésima tanda (13 nov, tarde): figuras con los rótulos «código de Lean solo». Mismos datos y mismo dibujo
    for f in ("curvas_por_modelo", "forest_nivel_a", "nivel_b"):
        d.cambia(r"\includegraphics[width=\linewidth]{figuras_v3/%s_es.pdf}" % f, r"\includegraphics[width=\linewidth]{figuras_v5/%s_es.pdf}" % f)
    # ---- vigesimoprimera tanda (13 nov, tarde): «Contaminación» fecha también el Nivel A
    d.tras("donde los problemas eran conocidos y sus formalizaciones no.",
           "En el Nivel~A, CriticLeanBench se publicó el 8 de julio de 2025, después del lanzamiento de siete de los ocho\n"
           "modelos y una semana antes de Goedel-Prover-V2-8B. Sus etiquetas son nuevas en esa publicación. Sus problemas, en\n"
           "cambio, vienen de colecciones anteriores como Omni-MATH, AIME y U-MATH, y sus autores dicen haber tomado los\n"
           "enunciados en Lean de un conjunto público, así que ambos pueden ser más antiguos que las etiquetas.")
    # ---- vigesimosegunda tanda (13 nov, 15:33): lectura final cruzada. Detalle: revisiones/lectura_final_2026-11-13.md
    d.cambia("Son la mayoría de los de la lectura en el último token en el Nivel~A, donde Llama-3.1 es negativo, y el de Gemma-3 en el último token en el Nivel~B.",
             prosa(r"""Entre ellos están la mayoría de los de la lectura en el último token en el Nivel~A, donde Llama-3.1
             es negativo, el de DeepSeek-Prover-V2 en la capa fija y el de Gemma-3 en el último token en el Nivel~B."""))
    d.cambia("la dirección de capa fija separa las clases. Si el modelo usa esa dirección es una pregunta causal",
             "la dirección de la sonda de cada capa separa las clases. Si el modelo usa una dirección así es una pregunta causal")
    d.cambia("las corridas en Qwen3-8B y en Llama en el Nivel~C", "las corridas en Qwen3-8B en el Nivel~A y en Llama-3.1 en el Nivel~C")
    d.cambia("Ninguno de los dos produce una brecha positiva.", "Ninguno de los dos produce una brecha cuyo intervalo quede por encima de cero.")
    d.cambia("y ninguno de los dos controles nulos muestra una brecha positiva.",
             "y ninguno de los dos controles nulos muestra una brecha cuyo intervalo quede por encima de cero.")
    d.cambia("Intervinimos sobre una sola familia de direcciones, y solo en el Nivel~B. La intervención cumple su criterio en dos de los cuatro modelos, y la corrida en Qwen3-4B es post hoc.",
             prosa(r"""Intervinimos a lo largo de dos direcciones, y solo en el Nivel~B. El desplazamiento por la diferencia
             de medias cumple su criterio en dos de los cuatro modelos, y la corrida en Qwen3-4B es post hoc. La ablación
             a lo largo de la dirección de la sonda dio un nulo."""))
    d.tras("Cambia la respuesta más que las direcciones al azar en dos de los cuatro modelos, uno de ellos en una corrida post hoc.",
           "Una intervención anterior a lo largo de la dirección de la sonda logística, en Qwen3-4B, dio un nulo.")
    d.cambia("En Qwen3-4B, en el Nivel~B, la propia respuesta del modelo separa tan bien como la sonda.",
             "En Qwen3-4B, en el Nivel~B y en el último token, la propia respuesta del modelo separa tan bien como la sonda.")
    d.cambia("Todavía no se ocupa de un P(Yes) que iguala a la sonda.", "Todavía no se ocupa de un P(Yes) que iguala a la sonda en el último token.")
    d.cambia(r"\item La datación de cada origen del Nivel~B frente", r"\item La datación de los orígenes del Nivel~B frente")
    d.cambia("se corrieron después bajo la misma regla temprana", "se corrieron después bajo una versión temprana de la regla")
    d.cambia("la tercera versión escrita ese día", "la tercera versión escrita el 4 de noviembre")
    d.cambia("es de al menos 0.9993 en todos los modelos y en los dos niveles.", "es de al menos 0.9993 en los cuatro modelos comprobados, en los Niveles~A y~B.")
    d.cambia("La brecha sobre el código de Lean solo sí se midió en ambas, y depende también de la lectura.",
             "La brecha sobre el código de Lean solo, en cambio, se midió en las dos lecturas, y depende de la lectura.")
    d.quita(r"Con un desplazamiento cuatro veces mayor la AUROC queda por debajo de 0.5 en los cuatro modelos (Tabla~\ref{tab:bintervencion} y Figura~\ref{fig:bintervencion}).")
    d.tras(r"En Gemma-3 el intervalo de esa misma diferencia también incluye el cero (+0.049 \ic{−0.003}{0.100}).",
           prosa(r"""Con un desplazamiento cuatro veces mayor la AUROC queda por debajo de 0.5 en los cuatro modelos
           (Tabla~\ref{tab:bintervencion} y Figura~\ref{fig:bintervencion})."""))
    d.cambia(r"En promedio queda allí entre 0.49 y 0.52, y la única excepción es Qwen3-8B, con 0.521 \ic{0.501}{0.543}.",
             prosa(r"""En promedio queda allí entre 0.49 y 0.52, y solo en Qwen3-8B el intervalo excluye 0.5 (0.521
             \ic{0.501}{0.543})."""))
    d.cambia(r"(Figura~\ref{fig:b}, abajo) muestra por qué.", r"(Figura~\ref{fig:b}, abajo) mira dentro de la familia C.")
    d.cambia("La preocupación no se sostiene.", "Las salidas guardadas no la confirman.")
    d.cambia(r"\vr{nl\_only} alcanza de 0.61 a 0.74 en los cuatro modelos de réplica", r"\vr{nl\_only} alcanza de 0.61 a 0.74 en el último token en los cuatro modelos de réplica")
    d.cambia(r"\vr{nl\_only} alcanzan de 0.61 a 0.74 en los cuatro modelos de réplica", r"\vr{nl\_only} alcanzan de 0.61 a 0.74 en el último token en los cuatro modelos de réplica")
    d.cambia("en ninguno de los cuatro modelos. Los modelos son Qwen3-4B, OLMo-2, Llama-3.1 y Gemma-3, y las brechas son",
             "en ninguno de los cuatro modelos comprobados (Qwen3-4B, OLMo-2, Llama-3.1 y Gemma-3). Las brechas son")
    d.quita("Las dos cláusulas ya estaban en el documento firmado el 4 de noviembre.")
    d.tras("y la otra, que la afirmación global se lea dentro de una sola lectura.",
           "Las dos cláusulas ya estaban en el documento firmado el 4 de noviembre.")
    d.cambia("primero en Qwen3-4B como análisis exploratorio y después", "primero en Qwen3-4B, post hoc, y después")
    d.cambia("En dos de los cuatro modelos, uno de ellos con la regla fijada de antemano, un desplazamiento",
             "En dos de los cuatro modelos, uno de ellos con la regla fijada de antemano y el otro post hoc, un desplazamiento")
    d.cambia("Deja igual la lectura~(ii), con brechas de", "No cambia la lectura de~(ii), con brechas de")
    d.cambia(r"La Tabla~\ref{tab:bejemplos} muestra un par de cada una.", r"La Tabla~\ref{tab:bejemplos} muestra un par de A, B, C2 y C3.")
    d.mueve_item(r"\item[12 nov] Con la misma regla se recalculó,", r"\item[12--13 nov] La misma intervención", "Con la misma regla se recalculó,", "Con la regla del 11 de noviembre se recalculó,")
    d.tras("la prueba de permutación intercambia los papeles dentro de cada par.", r"Los controles se listan en la Tabla~\ref{tab:controles}.")
    d.cambia(r"con~(ii) y en +0.029 \ic{−0.000}{0.058} con~(i). Lo que estima", r"con~(ii) y en +0.029 \ic{−0.000}{0.058} con~(i) (Figura~\ref{fig:forest}). Lo que estima")
    d.cambia("por completo por encima de cero. En ambos modelos la etiqueta", r"por completo por encima de cero (Tabla~\ref{tab:c}). En ambos modelos la etiqueta")
    # C. efectos de la sustitución «código de Lean [solo]» y cosméticos
    d.cambia("bigramas del código de Lean solo alcanza una AUROC", "bigramas del código de Lean por sí solo alcanza una AUROC")
    d.cambia("así que el código de Lean solo delata más", "así que el código de Lean por sí solo delata más")
    d.cambia("brecha sobre el código de Lean solo se mantiene en Qwen3-4B", "brecha sobre el código de Lean por sí solo se mantiene en Qwen3-4B")
    d.cambia("además de con el código de Lean. Los enunciados", "además de con el código de Lean solo. Los enunciados")
    d.cambia("% Beyond the Lean Alone", "% Beyond the Lean Code Alone")
    d.cambia("se desplaza hacia la clase contraria, la distancia completa entre las medias de clase", "se desplaza hacia la clase contraria en la distancia completa entre las medias de clase")
    d.cambia("hacia la clase contraria, la distancia completa entre las medias de clase, a lo largo", "hacia la clase contraria en la distancia completa entre las medias de clase, a lo largo")
    d.cambia("0.729, 0.688 y 0.787. Exploratorio y post hoc.", r"0.729, 0.688 y 0.787. La columna AUROC es la de \vr{full}. Exploratorio y post hoc.")
    # E. decididos por Carlos
    d.cambia("las ediciones de numeral dentro de C son un efecto de superficie.}", "las ediciones de numeral dentro de C las iguala un control de superficie.}")
    d.cambia("y se reportan como un primer intento fallido.", "y se reportan como corridas de descubrimiento sin peso confirmatorio.")
    d.cambia("«No corrido» significa que el control no existe para ese nivel.", "«No corrido» significa que no hay resultado para ese nivel.")
    # D. resumen: vuelve «solo» a las dos frases que limitan la evidencia y la frase de ProofNetVerif recupera su sujeto; 249 palabras
    d.cambia(r"\emph{más allá de lo que delata el código de Lean}", r"\emph{más allá de lo que delata el código de Lean solo}")
    d.cambia("en modelos congelados más allá del código de Lean.", "en modelos congelados más allá del código de Lean solo.")
    d.cambia("En ProofNetVerif fue positiva en dos modelos", "En ProofNetVerif la brecha fue positiva en dos modelos")
    d.cambia("cumplió el criterio por modelo. Un bootstrap", "cumplió su criterio. Un bootstrap")
    d.cambia("Unos mapas exploratorios sitúan", "Mapas exploratorios sitúan")
    d.cambia("cambia la respuesta del modelo más que direcciones al azar en dos de cuatro modelos", "cambia la respuesta más que direcciones al azar en dos de cuatro modelos")
    # ---- vigesimotercera tanda (14 nov): segunda lectura cruzada (dos lectores independientes). Aprobada por Carlos (secciones 1 y 3).
    d.todas(r"Donde un control se corrió, se reporta como \vr{full} menos el control; no todos", r"Donde un control se corrió, se reporta su AUROC o \vr{full} menos el control; no todos")
    d.todas("nunca reportamos la AUROC de una sonda tomada aisladamente. Cada resultado es una brecha,", "nunca interpretamos la AUROC de una sonda tomada aisladamente. Cada resultado central es una brecha,")
    d.todas("Una brecha positiva es evidencia de que", r"Una brecha positiva que sobrevive a los controles de la Tabla~\ref{tab:controles} es evidencia de que")
    d.todas("por el eje que separa las clases cambia la respuesta más que direcciones al azar en dos", "por el eje separador cambia la respuesta más que cualquiera de 20 direcciones al azar en dos")
    d.todas("Cambia la respuesta del modelo más que las direcciones al azar en Qwen3-4B", "Cambia la respuesta del modelo más que cualquiera de 20 direcciones al azar en Qwen3-4B")
    d.todas("Cambia la respuesta más que las direcciones al azar en dos de los cuatro modelos", "Cambia la respuesta más que cualquiera de 20 direcciones al azar en dos de los cuatro modelos")
    d.todas("cumplió su criterio. Un bootstrap", "cumplió el criterio por modelo. Un bootstrap")
    d.todas("decodificable linealmente en modelos congelados más allá", "decodificable linealmente de modelos congelados más allá")
    d.todas("en las capas superiores. Esbozamos", "en capas superiores. Esbozamos")
    d.todas("posteriores a los modelos y a este piloto.", "posteriores a los modelos y al piloto.")
    d.todas("Ningún modelo, sin embargo, sobrevive", "Aun así, ningún modelo sobrevive")
    d.cambia("moldearon esos pares. Una intervención anterior dio un nulo.", "moldearon esos pares.\n\nUna intervención anterior dio un nulo.")
    d.todas("las familias A y B no se distinguen de cero", "en las familias A y B el margen no se distingue de cero")
    d.todas("los del enunciado en Lean que faltan", "los del código de Lean que faltan")
    d.todas("quedan a menos de 0.023 del cero", "quedan a no más de 0.023 del cero")
    d.todas("con una regla fijada antes de correr. En cada capa", "con una regla fijada antes de correrlos. En cada capa")
    d.todas("muestra un par de A, B, C2 y C3.", "muestra un par de cada una de A, B, C2 y C3.")
    d.todas("de la pareja lo hace en tres", "del gemelo lo hace en tres")
    d.todas(r"intercambio con la\\pareja, menos azar", r"intercambio con el\\gemelo, menos azar")
    d.todas("recoge el estado de la evidencia", "recoge el estatus de la evidencia")
    d.todas("En Gemma-3 el P(Yes) del modelo apenas separa los pares de partida (0.590)", "En Gemma-3, de entrada, el P(Yes) del modelo apenas separa los pares (0.590)")
    d.todas("además de con el código de Lean solo", "y también con el código de Lean solo")
    # ---- vigesimocuarta tanda (14 nov): historia del lote del Nivel B (bitácora, D-2) y cifras del Nivel B sin la pregunta (s2b). Aprobada por Carlos.
    d.todas("No se pudo construir un lote certificable de tripletas, y los pares se declararon lote de desarrollo. Tampoco pasó una comprobación de superficie fijada de antemano.",
            "El 4 de noviembre, después de que fallara una comprobación de superficie provisional, los pares se declararon su lote de desarrollo. Luego no se pudo construir un lote certificable de tripletas, así que los pares son la única evidencia de este nivel. La comprobación de superficie fijada de antemano tampoco pasó en los pares certificados.")
    d.todas("no pasó (0.706 en los pares certificados), y el lote se declaró exploratorio.",
            "no pasó (0.706 en los pares certificados). El lote se había declarado de desarrollo el 4 de noviembre.")
    d.todas("En el Nivel~B no requiere la pregunta en ninguno.",
            r"En el Nivel~B la brecha en el último token sin la pregunta es positiva en los cuatro modelos. Las brechas son +0.176 \ic{0.113}{0.236}, +0.113 \ic{0.061}{0.166}, +0.128 \ic{0.067}{0.189} y +0.102 \ic{0.047}{0.156}, en el mismo orden.")
    # ---- vigesimoquinta tanda (14 nov): observaciones del profesor Riaño (cómo leer AUROC y figuras, orden del resumen, trabajo futuro). Aprobada por Carlos.
    d.tras(r"que reportamos con un intervalo bootstrap del 95\% sobre grupos \citep{efron}.",
           prosa(r"""La AUROC es la probabilidad de que una sonda puntúe una formalización adecuada por encima de una inadecuada.
           Vale 0.5 para una sonda que adivina y 1 para una que nunca se equivoca, y resume la sensibilidad y la especificidad
           en todos los umbrales de decisión. Una brecha de +0.05 significa entonces que añadir el enunciado sube esa
           probabilidad en cinco puntos."""))
    d.todas(r"\caption{Capa por capa. AUROC de una sonda lineal", r"\caption{Capa por capa. Cómo leerla: donde la curva de color va por encima de la gris, el enunciado añade a lo que el código de Lean delata por sí solo en esa capa. AUROC de una sonda lineal")
    d.todas(r"\caption{Nivel A, lectura (ii). Puntos llenos", r"\caption{Nivel A, lectura (ii). Cómo leerla: un punto a la derecha del cero es una brecha positiva, y cuenta como establecida solo si todo su intervalo queda a la derecha. Puntos llenos")
    d.todas("en los cinco modelos de propósito general. Cada celda es", "en los cinco modelos de propósito general. Cómo leerla: las celdas más oscuras son posiciones y capas donde las clases se separan mejor, y el panel derecho es más oscuro donde el enunciado añade. Cada celda es")
    d.todas(r"\caption{Intervención del Nivel B. Arriba: caída", r"\caption{Intervención del Nivel B. Cómo leerla: una caída a la derecha del cero significa que el desplazamiento hizo que P(Yes) separara peor los pares, y un modelo cumple el criterio cuando su marcador de color queda a la derecha de todas las marcas grises. Arriba: caída")
    d.todas(r"\caption{Nivel B. Arriba: AUROC pareada", r"\caption{Nivel B. Cómo leerla: la longitud de la barra entre el marcador gris y el de color es la brecha de ese modelo. Arriba: AUROC pareada")
    d.todas("Ningún nivel sostiene por sí solo la afirmación de que la adecuación es decodificable linealmente de modelos congelados más allá del código de Lean solo. En 450 formalizaciones", "En 450 formalizaciones")
    d.todas("en capas superiores. Esbozamos una prueba confirmatoria", "en capas superiores. Ningún nivel sostiene por sí solo la afirmación de que la adecuación es decodificable linealmente de modelos congelados más allá del código de Lean solo. Esbozamos una prueba confirmatoria")
    d.tras("Una intervención anterior a lo largo de la dirección de la sonda logística, en Qwen3-4B, dio un nulo.",
           "\n" + prosa(r"""Quedan tres cosas por hacer. La prueba confirmatoria del Apéndice~\ref{app:protocolo} necesita enunciados
           escritos después de los modelos y de este piloto. La intervención se corrió solo en el Nivel~B, y a los Niveles~A
           y~C todavía les falta una. Los mapas descansan en una sola semilla."""))
    # ---- vigesimosexta tanda (17 nov): cabos que esperaban a las figuras nuevas (rótulos, pie del escáner) y la composición de los pares.
    d.todas(r"al azar $\geq$ sonda", r"al azar $\geq$ dirección")
    d.todas("Izquierda: el prompt con enunciado y Lean.", "Izquierda: el prompt con enunciado y código de Lean.")
    d.todas("el tamaño del ruido de una sola celda por una aproximación normal y, para la diferencia,", "el tamaño del ruido de una sola celda por una aproximación normal a la nula de etiquetas permutadas y, para la diferencia,")
    d.tras("Certifica la otra como no equivalente, y esa es el miembro inadecuado.",
           "La edición infiel se aplica sobre la fiel, así que los dos miembros difieren solo en la edición infiel.")
    return d


if __name__ == "__main__":
    for nombre, f in (("main_en.tex", ingles), ("main_es.tex", espanol)):
        d = f()
        open(os.path.join(AQUI, nombre), "w", encoding="utf-8").write(d.t)
        print(nombre, "pasajes aplicados:", d.n, "| sustituciones de «Lean alone/solo»:", d.sustituciones)
