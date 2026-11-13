---
dataset_info:
  features:
  - name: id
    dtype: string
  - name: nl_statement
    dtype: string
  - name: lean4_src_header
    dtype: string
  - name: lean4_formalization
    dtype: string
  - name: lean4_prediction
    dtype: string
  - name: correct
    dtype: bool
  splits:
  - name: valid
    num_bytes: 1288852.6918976547
    num_examples: 2300
  - name: test
    num_bytes: 813658.3081023454
    num_examples: 1452
  download_size: 406549
  dataset_size: 2102511
configs:
- config_name: default
  data_files:
  - split: valid
    path: data/valid-*
  - split: test
    path: data/test-*
license: mit
task_categories:
- text-generation
- translation
language:
- en
tags:
- code
pretty_name: ProofNetVerif
size_categories:
- 1K<n<10K
---

# ProofNetVerif

ProofNetVerif is a benchmark to evaluate both reference-based and reference-free metrics for statement autoformalization introduced in 
[Improving Autoformalization using Type Checking](https://arxiv.org/abs/2406.07222). This benchmark is compatible with Lean v4.8.0.

## Tasks

- **Reference-based metric evaluation:**
  - Input: `lean4_formalization`, `lean4_prediction`
  - Output: `correct`
- **Reference-free metric evaluation:**
  - Input: `nl_statement`, `lean4_prediction`
  - Output: `correct`

*Note:* Developing an accurate reference-free metric on this benchmark should yield an accurate verifier to filter wrong formalization attempts.

## Data Fields

- `id`: Identifier for the problem from the ProofNet benchmark.
- `nl_statement`: Natural language theorem statement.
- `lean4_src_header`: File header including imports, namespaces, and locales required for the formal statement.
- `lean4_formalization`: Reference formal theorem statement in Lean 4.
- `lean4_prediction`: Formalization predicted by a model.
- `correct`: Label indicating if `lean4_prediction` is semantically equivalent to `nl_statement` (and `lean4_formalization`).

## Citation

```bibtex
@misc{poiroux2024improvingautoformalizationusingtype,
    title={Improving Autoformalization using Type Checking}, 
    author={Auguste Poiroux and Gail Weiss and Viktor Kunčak and Antoine Bosselut},
    year={2024},
    eprint={2406.07222},
    archivePrefix={arXiv},
    primaryClass={cs.CL},
    url={https://arxiv.org/abs/2406.07222}, 
}
```