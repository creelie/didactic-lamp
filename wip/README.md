# Work in progress: Gurvich–Naumova Conjecture 1

Conjecture (arXiv:2508.00946): for every n, {1, ..., n} has a partition into parts
of at most three elements whose sums are powers of 3.

- `python/construct.py`: the recursive construction and a checker
  (`python3 construct.py 20000` reports `bad count 0`).
- `lean/GN/`: Lean 4 formalization (Lean v4.34.1, Mathlib v4.34.1), place under a
  Lake project as `LeanLab/GN/`.
  - `Basic.lean`, `Gadget.lean`, `Assembly.lean`, `CaseA2.lean`: compiled, no `sorry`.
  - `Main.lean`: main induction; not yet compiled. Still to add: the transfer
    from `Good (Icc 1 n)` to a `Finpartition` of `Finset.Icc 1 n` in ℕ.

Status: paused. Not released.
