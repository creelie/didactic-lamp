**Partitioning {1,...,n} into parts of size at most three whose sums are powers of three**, by Deep Bhattacharjee (corresponding author) and Ushashi Bhattacharya.

We prove the conjecture of Gurvich and Naumova ([arXiv:2508.00946](https://arxiv.org/abs/2508.00946), Conjecture 1) that for every n ≥ 1 the set {1,...,n} can be partitioned into parts of at most three elements whose sums are powers of 3. The partition is given by an explicit recursion.

Version 2.0.0 adds the second author and the journal format for Discrete Mathematics: MSC 2020 codes (Primary 05A18; Secondary 11B75, 68V15), four schematic figures, and the data availability, competing interests and funding statements. The mathematics is that of v1.0.0.

| Step | Content |
|---|---|
| Lemmas 2.1–2.3 | The intervals [−ℓ, ℓ], ℓ ≢ 2 (mod 3), split into {0} and triples with sum 0; images 3^q + sZ; symmetric sets split into pairs with sum 3^q |
| Lemma 3.1 | Reflection: [1, T+j] minus W is good when F and R are good |
| Lemma 3.2 | A fixed-point-free involution of {1,...,2N−2} with distinct pair sums, N ≡ 1 (mod 3) |
| Proposition 4.1 | [n] minus the triple {n−1, n, T−2j+1} is good for j ≡ 2 (mod 3), 2j < T |
| Theorem 1.2 | Every [n] has a 3-good partition |

The proof is formalized in Lean 4 with Mathlib: `GN.gurvich_naumova` depends only on the axioms propext, Classical.choice and Quot.sound. The release workflow builds the Lean project and runs the independent checks in C (every n ≤ 30000), Julia (n ≤ 20000), C++ (n ≤ 10000) and Python (n ≤ 3000), with further values of n up to 64570081, before publishing.

Files:
- `GurvichNaumovaConjecture_final2.pdf`: the paper
- `GurvichNaumovaConjecture_final2-tex.zip`: LaTeX source with the figures as PNG
- `GurvichNaumovaConjecture_final2-arxiv.tar.gz`: the same source, ready for arXiv

The repository also holds `preprintGurvichNaumovaConjecture/GurvichNaumovaConjecture.pdf` and `MasterGurvichNaumovaConjecture_masterzipfinal2.zip` with every file.
