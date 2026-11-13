# Sources and licenses

The code of this repository is under the MIT License (`LICENSE`) and its data and text under CC BY 4.0 (`LICENSE-DATA.md`). This file lists what each upstream source states, as read on 13 November 2026.

This repository contains material derived from the following sources. Each derived file keeps the identifier of its origin.

## formal-conjectures (Google DeepMind)

- Source: <https://github.com/google-deepmind/formal-conjectures>
- Stated license: Apache License 2.0 for software, Creative Commons Attribution 4.0 International for all other materials.
- The upstream README notes that some content is based on third-party sources with their own terms, among them Wikipedia, MathOverflow and OEIS (CC BY-SA 4.0).
- Used in: Level B. The files under `probes/nivel_b/certificacion/lean/` and the pairs in `probes/nivel_b/datos/` whose origin starts with `formal_conjectures_` are modified versions of upstream statements. The modifications are described in `probes/nivel_b/reglas_generador.md`.

## FormalMATH-Lite (Sphere-AI-Lab)

- Source: <https://github.com/Sphere-AI-Lab/FormalMATH-Bench> and <https://huggingface.co/datasets/SphereLab/FormalMATH-Lite>
- Stated license: Apache License 2.0 on GitHub, MIT on the Hugging Face dataset card.
- Used in: Level B, as the second source of original statements. The derived pairs are modified versions.

## ProofNetVerif

- Source: <https://huggingface.co/datasets/PAug/ProofNetVerif>, built on ProofNet (<https://github.com/zhangir-azerbayev/ProofNet>) and ProofNet#.
- Stated license: MIT.
- Used in: Level C. `probes/nivel_c/datos/proofnetverif/` is an unmodified copy of the dataset files, and `probes/nivel_c/datos_proc/` is a processed version.

## CriticLeanBench

- Source: <https://huggingface.co/datasets/m-a-p/CriticLeanBench> (arXiv:2507.06181).
- Not redistributed here. Only identifiers, labels' aggregate statistics and result files computed on it are included.
