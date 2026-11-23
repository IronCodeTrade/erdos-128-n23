# Erdős problem #128: no counterexample on at most 23 vertices

**Author:** Krzysztof Michalak (with an AI assistant, see [Authorship and AI use](#authorship-and-ai-use)).
**Licence:** CC0 1.0 (`LICENSE`).

[Erdős problem #128](https://www.erdosproblems.com/128) (Erdős–Rousseau, \$250) asks:

> Let G be a graph with n vertices such that every induced subgraph on ≥ ⌊n/2⌋ vertices has more than n²/50 edges. Must G contain a triangle?

**This repository does not solve the problem.** It shows that **there is no counterexample with n ≤ 23 vertices**.
The prize is for the statement for all n, and it remains open.

## Result

**Claim.** For every n ≤ 23, every graph on n vertices in which every induced subgraph on ≥ ⌊n/2⌋ vertices
has more than n²/50 edges contains a triangle.

To our knowledge (forum thread https://www.erdosproblems.com/forum/thread/128, checked 23 Nov 2026), the largest
*exhaustive* search reported publicly was smaller; heuristic searches (simulated annealing,
https://github.com/cormundus/erdos-128-census) went up to n = 26 but are not exhaustive.

## How the claim is established

The argument has three parts. Each part is labelled with the kind of evidence behind it.

| Step | Statement | Evidence |
| --- | --- | --- |
| 1 | If a counterexample on n vertices exists, then a **maximal triangle-free** (MTF) counterexample on the same n vertices exists (adding edges keeps the density hypothesis). | **Lean 4 + Mathlib, kernel-checked**: `E128.reduction` in `E128/N23.lean`. Axioms: `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`. |
| 2 | For each n = 3..22, **no** MTF graph on n vertices satisfies the hypothesis. | **Exhaustive computer search** (not a Lean proof). All MTF graphs were generated with `triangleramsey` 1.1 (J. Goedgebeur with G. Brinkmann, https://caagt.ugent.be/triangleramsey/); for each graph `search/c128.c` computes the minimum number of edges over induced subsets of size ⌊n/2⌋. The number of graphs generated agrees with OEIS [A216783](https://oeis.org/A216783) for every n, including **58 919 069 858** graphs for n = 22. |
| 3 | No counterexample on 22 vertices ⇒ none on 23 vertices. | **Lean 4 + Mathlib, kernel-checked**: `E128.n23_of_n22` in `E128/N23.lean` (assumes the conclusion of step 2 for n = 22 as a hypothesis). The general version (2m+1 ⇒ 2m, for every m) is `R7E128.no_odd_of_no_even` in `E128/Odd.lean`. Same three axioms. |

For n ≤ 2 the statement is trivial (the empty set has 0 edges, and for n = 2 a single vertex has 0 edges).

Why step 3 works: delete any vertex of a putative counterexample on 2m+1 vertices. ⌊(2m+1)/2⌋ = ⌊2m/2⌋ = m,
so the set sizes stay the same, while the threshold drops from (2m+1)²/50 to (2m)²/50.
The same trick does **not** give n = 24 from n = 23 (⌊24/2⌋ = 12 ≠ 11).

### What exactly is computer-checked and what is not

- The Lean files are kernel-checked. They prove steps 1 and 3 and use the result of step 2 as an explicit hypothesis
  (`h22`). They do **not** prove step 2.
- Step 2 relies on the correctness and completeness of `triangleramsey` and on the correctness of `search/c128.c`.
  Completeness is supported by the exact agreement of the graph counts with OEIS A216783 for every n ≤ 22.
  Correctness of `c128.c` was cross-checked against a brute-force Python program (`search/chk.py`) for all n ≤ 14.
- `c128.c` first finds an upper bound for the minimum by a greedy + 1-swap heuristic. If the heuristic value is
  ≥ ⌊n²/50⌋ it runs an exact branch-and-bound. A graph is a counterexample iff the exact minimum m satisfies 50·m > n².
  Because the heuristic only produces real subsets, an upper bound below the threshold already proves that the graph
  is not a counterexample.

## Data (n = 22)

The run was split into 5 parts (`triangleramsey 22 mod r 5`, r = 0..4). Output lines (`results/res22_*.txt`):

```
n=22 graphs=11697637334 maxHeur=10 exactRuns=9  maxExact=8 bound(n^2/50)=9.68 counterexamples=0
n=22 graphs=11692773460 maxHeur=10 exactRuns=4  maxExact=6 bound(n^2/50)=9.68 counterexamples=0
n=22 graphs=11968695633 maxHeur=9  exactRuns=6  maxExact=7 bound(n^2/50)=9.68 counterexamples=0
n=22 graphs=11715817467 maxHeur=9  exactRuns=10 maxExact=8 bound(n^2/50)=9.68 counterexamples=0
n=22 graphs=11844145964 maxHeur=10 exactRuns=12 maxExact=9 bound(n^2/50)=9.68 counterexamples=0
```

Total 58 919 069 858 graphs (= A216783(22)). The largest value of "minimum number of edges in an induced
11-vertex subgraph" over all MTF graphs on 22 vertices is **9**; a counterexample would need **10**.

Other n: `results/res_3_18.txt`, `results/res_19_21.txt` (n = 21: 2 911 304 940 graphs, = A216783(21)).
The extremal value n²/50 is reached exactly (but not exceeded) for n = 10 and n = 20 (blow-ups of C5).
Checksums: `results/SHA256SUMS`.

## Reproducing

### Lean (steps 1 and 3)

Requires [elan](https://github.com/leanprover/elan). Toolchain `leanprover/lean4:v4.36.0`, Mathlib `v4.36.0`.

```bash
lake exe cache get      # downloads compiled Mathlib
lake build              # builds E128.N23 and E128.Odd and prints the axioms
```

### Search (step 2)

```bash
cd search
curl -LO https://caagt.ugent.be/triangleramsey/triangleramsey-1.1.zip
unzip triangleramsey-1.1.zip
# triangleramsey needs nauty >= 2.5 (we used nauty 2.8.9 from https://pallini.di.uniroma1.it/ or
# https://users.cecs.anu.edu.au/~bdm/nauty/). Copy naugraph.c nautil.c nauty.c nauty.h naurng.c naurng.h
# schreier.c schreier.h sorttemplates.c from the configured nauty directory into triangleramsey-1.1/, then:
(cd triangleramsey-1.1 && make) && cp triangleramsey-1.1/triangleramsey .
./run.sh 20          # about 7 minutes on one core
./run.sh 22 5        # n = 22 in 5 parallel parts; several hours on 5 cores of a 2026 Xeon
python3 chk.py       # brute-force cross-check for n = 5..14 (needs triangleramsey-1.1/ next to it)
```

SHA-256 of the `triangleramsey-1.1.zip` we used: `6d16c21bcdb7a9adf24160cffacb08f880faa0db184d091a9814c1467c5f548a`.
`triangleramsey` is distributed under the GPL by its authors and is **not** included here.

## What would be next

- n = 23 does not need a search because of step 3 (a direct search would mean A216783(23) = 1 474 647 067 521 graphs).
- n = 24 needs all A216783(24) = 45 599 075 629 687 MTF graphs on 24 vertices, about 770 times the n = 22 work.
  We did not attempt it.
- A proof for all n needs new mathematics; computation alone cannot give it.

## Authorship and AI use

The searches, the Lean proofs and this text were produced by Krzysztof Michalak working with an AI assistant
(Grok Bot). The AI assistant wrote most of the code and Lean proofs; all numbers are taken from the actual runs
in `results/`. Please treat the computational step as a computation, not as a formal proof.

## Contact

Krzysztof Michalak — krzysztof.michalak.biz@gmail.com
