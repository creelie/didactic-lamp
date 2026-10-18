# Partitioning {1, ..., n} into parts of size at most three whose sums are powers of three

Deep Bhattacharjee (corresponding author; Formerly, Electro-Gravitational
Space Propulsion Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India, and
Formerly, University of Calcutta, Senate House, 87/1 College Street, Kolkata
700073, West Bengal, India; itsdeep@live.com, d.bhattacharjee@erl-forschung.de; ORCID 0000-0003-0466-750X)
and Ushashi Bhattacharya (Formerly, National Taiwan University, Taipei 106319,
Taiwan; rai.bhattacharya.in@gmail.com; ORCID 0009-0002-2254-3914).

- Paper: [`preprintGurvichNaumovaConjecture/GurvichNaumovaConjecture.pdf`](preprintGurvichNaumovaConjecture/GurvichNaumovaConjecture.pdf)
- Lean 4 formalization on Zenodo: doi:[10.5281/zenodo.23384809](https://doi.org/10.5281/zenodo.23384809) (release v2.0.0; all versions: doi:[10.5281/zenodo.23316376](https://doi.org/10.5281/zenodo.23316376))
- Master zip: [`MasterGurvichNaumovaConjecture_masterzipfinal2.zip`](https://github.com/creelie/didactic-lamp/raw/main/MasterGurvichNaumovaConjecture_masterzipfinal2.zip)
- Target journal: Discrete Mathematics (`journal/JOURNAL.md`)
- MSC 2020: Primary 05A18; Secondary 11B75, 68V15

This repository proves Conjecture 1 of Gurvich and Naumova
([arXiv:2508.00946](https://arxiv.org/abs/2508.00946)):

> For every n >= 1 the set [n] = {1, ..., n} has a partition into parts of at
> most three elements, the sum of each part being a power of 3.

Before this proof the conjecture was known for n <= 844. Version 3 of the
preprint (July 2026) still lists it as a conjecture; this was checked again on
15 October 2026 against arXiv and the web, and no other proof was found.

## Result

**Theorem.** For every n >= 1 the set [n] has a 3-good partition.

**Corollary.** Let m >= 2. Every set [n] has an m-good partition (parts of at
most m elements, every sum a power of m) if and only if m is 2 or 3.

The partition is given by a recursion. Let T = 3^t <= n < 3T and j = n - T.

- n = T: take [T - 1] and {T}.
- 2n >= 3T + 1: take [3T - 1 - n] and the pairs {x, 3T - x}.
- 2n <= 3T and j not congruent to 2 mod 3: take [T - j - 1] and the interval
  T + [-j, j], which splits into {T} and triples with sum 3T.
- 2n <= 3T and j congruent to 2 mod 3: the proof shows that [n] minus the
  triple W_n = {n - 1, n, T - 2j + 1}, whose sum is 3T, has a 3-good partition.
  This passes from j to n by a reflection argument, except when j lies in the
  upper half of [3^u, 3^(u+1)); there a fixed-point-free involution of
  {1, ..., 2N - 2} with distinct pair sums, N = j - (3^(u+1) - 1)/2, supplies
  the missing triples.

Example: n = 35, the least case left open by Theorem 1 of Gurvich and Naumova:
{5, 7, 15}, {9}, {27}, {18, 30, 33}, {20, 29, 32}, {22, 28, 31}, {12, 34, 35}
and the pairs {x, 27 - x} for x in {1, 2, 3, 4, 6, 8, 10, 11, 13}.

## Contents

| Path | Contents |
|---|---|
| `paper/` | LaTeX source (`main.tex` with an inline bibliography, the Elsevier `elsarticle` class, `figures/` as PNG) |
| `figures/` | TikZ sources of the four figures and `make_figures.sh`, which writes them to `paper/figures/` |
| `lean/` | Lean 4 + Mathlib formalization (7 files, 1073 lines); `GurvichNaumova/Main.lean` holds `GN.gurvich_naumova` |
| `checks/python/` | Python check of the construction, of H(n), of Lemma 2.1 and of Lemma 3.2 |
| `checks/julia/`, `checks/c/`, `checks/cpp/` | the same construction in Julia, C and C++, each checked on its own range of n |
| `run_all.sh` | runs the Lean build, the axiom check and all programs |
| `scripts/build_paper.sh` | builds `dist/`, the preprint folder and the master zip |
| `journal/JOURNAL.md` | target journal, format rules and AI policy |
| `dist/` | `GurvichNaumovaConjecture_final2.pdf`, `GurvichNaumovaConjecture_final2-tex.zip` (source with PNG figures) and `GurvichNaumovaConjecture_final2-arxiv.tar.gz` |
| `preprintGurvichNaumovaConjecture/` | the paper as a PDF, and nothing else |
| `MasterGurvichNaumovaConjecture_masterzipfinal2.zip` | every tracked file of the repository with `dist/` |

## Lean statement

```lean
theorem gurvich_naumova (n : ℕ) :
    ∃ P : Finpartition (Finset.Icc 1 n),
      ∀ s ∈ P.parts, s.card ≤ 3 ∧ ∃ k : ℕ, ∑ x ∈ s, x = 3 ^ k
```

`Finpartition (Finset.Icc 1 n)` is the type of partitions of {1, ..., n} into
nonempty parts. `#print axioms GN.gurvich_naumova` reports `[propext,
Classical.choice, Quot.sound]`; there is no `sorry`, `admit`, `native_decide`
or added axiom.

## Running the checks

Requirements: elan (Lean 4.34.1, fetched from `lean/lean-toolchain`),
python3, julia, a C compiler and a C++17 compiler.

    ./run_all.sh            # Lean build (with the Mathlib cache), axiom check, all programs
    ./run_all.sh --no-lean  # programs only

The programs check every n <= 30000 (C), 20000 (Julia), 10000 (C++) and 3000
(Python), and larger n up to 64570081. Each takes an optional bound, for
example `python3 checks/python/check.py 5000`.

To build the paper and the release files: `scripts/build_paper.sh` (needs
latexmk, zip and tar; `figures/make_figures.sh` redraws the figures).

## Archive

| Release | Zenodo DOI |
|---|---|
| v2.0.0 (two authors, journal format) | [10.5281/zenodo.23384809](https://doi.org/10.5281/zenodo.23384809) |
| v1.0.1 | [10.5281/zenodo.23316427](https://doi.org/10.5281/zenodo.23316427) |
| v1.0.0 | [10.5281/zenodo.23316377](https://doi.org/10.5281/zenodo.23316377) |
| all versions | [10.5281/zenodo.23316376](https://doi.org/10.5281/zenodo.23316376) |
