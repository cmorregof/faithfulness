# It Compiles, but Is It What We Meant?

Code, decision rules, data and result files for the preprint

> **It Compiles, but Is It What We Meant? Linear Probes for the Faithfulness of Lean 4 Formalizations**
> Carlos Manuel Orrego-Franco, Juan Carlos Riaño-Rojas, Fabián Fernando Serrano-Suárez.
> Universidad Nacional de Colombia, Manizales.

The paper is in [`paper_adecuacion/v5_causal/main_en.pdf`](paper_adecuacion/v5_causal/main_en.pdf). A Spanish version is in [`main_es.pdf`](paper_adecuacion/v5_causal/main_es.pdf).

![Layer-by-position relief of the probe direction in five models](paper_adecuacion/v5_causal/figuras_v5/readme/relieve_cinco_modelos.png)

*Exploratory maps, one seed. Height and colour show the out-of-fold AUROC of each layer's probe direction, token by token, on the 450 CriticLeanBench formalizations. The dark line is the Lean code alone.*

## Status: preliminary, with one contrast cross-checked

Every number in the paper and in this repository comes from the reference implementation, which was written with AI coding assistants under rules set by the first author. By the rule of the project, these numbers become findings only after they are compared with an implementation the first author writes by hand ([`probes/probe.py`](probes/probe.py)).

That comparison has been run for the Level A contrast in Qwen3-4B. In both readouts the two AUROCs and the gap agree with the reference within 0.005, and the 95% interval of the gap lies above zero in both implementations.

| Readout | Quantity | `probe.py` | Reference |
|---|---|---|---|
| (i) last token, nested layer choice | AUROC, statement with Lean code | 0.811 | 0.814 |
| (i) | AUROC, Lean code alone | 0.723 | 0.723 |
| (i) | Gap | +0.088 [0.042, 0.136] | +0.091 [0.043, 0.137] |
| (ii) mean over Lean tokens, fixed layer 24 | AUROC, statement with Lean code | 0.751 | 0.751 |
| (ii) | AUROC, Lean code alone | 0.655 | 0.656 |
| (ii) | Gap | +0.096 [0.055, 0.135] | +0.095 [0.057, 0.134] |

An AI assistant executed `probe.py`, unchanged. The decision rule was written to the project log before the run, and the reference results were opened only after the `probe.py` results were on disk. The report, with the three deviations from the planned procedure and the row-by-row comparison, is in [`probes/resultados_probe_2026-11-21.md`](probes/resultados_probe_2026-11-21.md) (in Spanish). `probe.py` runs no permutation test and no stacked control, so this check does not reproduce the pass-or-fail verdict of the preregistration.

The other models of Level A and Levels B and C have not been compared yet, and their numbers remain preliminary.

Two more items are pending. A blind human review of 80 items is in progress, and the protocol for the confirmatory test is an unsigned draft. Neither is published here.

## The question

A Lean formalization can compile and still say something other than the statement it was meant to capture. We ask whether the activations of frozen language models linearly separate faithful from unfaithful Lean 4 formalizations beyond what the Lean code alone gives away. At three levels we measure the AUROC gap between a linear probe that reads the statement with the formalization and one that reads the formalization alone.

No level alone supports the claim that faithfulness is linearly decodable from frozen models beyond the Lean code alone.

- **Level A, CriticLeanBench.** On 450 formalizations a preregistered replication did not pass, because none of its four models met the per-model criterion. A post hoc bootstrap puts their mean gap at +0.045 (95% CI [0.021, 0.069]) at a fixed layer, whereas at the last token the interval includes zero.
- **Level B, minimal pairs.** On 377 pairs certified by Lean, exploratory runs gave a positive gap in three of four models at the last token. Against the stronger of two surface controls, only one keeps a margin whose interval excludes zero. Shifting activations along the separating axis changes the model's answer more than random directions do in two of four models, one of them in a post hoc run.
- **Level C, ProofNetVerif.** The gap was positive in two models, one of them exploratory.

"Preregistered" here means a written decision rule with a recorded SHA-256 and approval time, kept in the project log. These rules are internal files. They are not entries in a public registry.

## What is here

| Path | Contents |
|---|---|
| `paper_adecuacion/v5_causal/` | LaTeX sources and PDFs in English and Spanish, figures and the scripts that draw them, and the change report `reporte_v5.md` |
| `paper_adecuacion/v4_voz/` | The previous version of the text, which `aplica_v5.py` takes as its starting point |
| `paper_adecuacion/fuentes/`, `paper_adecuacion/figuras/datos/` | Result files read by the figure scripts |
| `probes/prerregistro_v2.md`, `probes/prerregistros/` | Level A preregistration and its hashed copy |
| `probes/*/APROBADO_*`, `probes/*/regla_*.md` | Decision rules of each level with their hashes and approval times, unedited |
| `probes/referencia/` | Reference implementation of Level A and its results |
| `probes/probe.py`, `probes/resultados_probe_2026-11-21.md`, `probes/corrida_probe_2026-11-21/` | The first author's implementation of the Level A probes, the report of its comparison with the reference in Qwen3-4B, and the scripts, logs and scores of that run |
| `probes/nivel_b/` | Generator, Lean certification, the certified pairs (`datos/`, `certificacion/`), surface controls and results of Level B |
| `probes/intervencion/` | Intervention rules, code and results |
| `probes/nivel_c/` | Level C code, data and results, including the second, independent implementation |
| `probes/sin_pregunta/` | Code and results of the prompt-without-question control |
| `probes/BITACORA.md` | The project log, with the numbered list of deviations and late decisions |

Most working files are in Spanish. The paths `/Users/cmorregof/...` that appear in logs and in some rules are those of the machine where the runs were made. They were left as they are because the signed rules are not edited.

## What is not here

- **Activations.** The extracted residual-stream activations take about 37 GB and are not published. Without them the probes cannot be refitted. `probes/extraer.py` and the per-level extraction scripts regenerate them from the pinned model revisions listed in the paper's appendix.
- **Probe directions of the intervention** (`direcciones.npz`, about 200 MB).
- **CriticLeanBench.** The benchmark is not redistributed. It is available from its authors at <https://huggingface.co/datasets/m-a-p/CriticLeanBench>.
- **Intermediate candidate files** of the Level B generator, and working material that the paper does not cite.

## Checking the text against the result files

The paper is built by a script, and a second script checks that each number in the edited passages comes from a result file. From a clean clone, with Python 3 and no extra packages:

```bash
cd paper_adecuacion/v5_causal
python3 aplica_v5.py
python3 verifica_v5.py
python3 coteja_en_es.py main_en.tex main_es.tex
```

The two passages on the `probe.py` comparison (22 November) were edited directly in `main_en.tex` and `main_es.tex`. They are not yet in `aplica_v5.py`, so rerunning it reverts them.

`latexmk -pdf main_en.tex` and `latexmk -pdf main_es.tex` compile the two PDFs. `ejemplos_nivel_b.py` also needs `pyarrow`.

The figure scripts in `figuras_v5/` need `numpy`, `matplotlib`, `tueplots` and `colorspacious`. `figuras_v5.py` and `fig_intervencion.py` also need LaTeX with `lmodern` and `cm-super`.

## Licenses and sources

The code is under the MIT License ([`LICENSE`](LICENSE)). The data, the result files and the text are under CC BY 4.0 ([`LICENSE-DATA.md`](LICENSE-DATA.md)). [`NOTICE.md`](NOTICE.md) lists the sources of the derived data and their licenses.

## Contact

Carlos Manuel Orrego-Franco, Universidad Nacional de Colombia, Manizales.
