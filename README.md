# STLC & UTLC in Coq

Formalizations of the **Untyped Lambda Calculus (UTLC)** and **Simply Typed Lambda Calculus (STLC)** with a tiny maps library, all in Coq.

## Files

* **`Maps.v`** — Total/partial maps (à la *Software Foundations*): `total_map`, `partial_map`, `t_update`, `update`, and basic lemmas/notations.
* **`UTLC.v`** — UTLC syntax, substitution, small-step and multi-step semantics, Church numerals, `iszero`, and proofs for **Q1–Q3**.
* **`STLC.v`** — STLC syntax and typing rules, contexts via partial maps, and proofs for **Q4–Q6** (including weakening).

## Build

Compile from the repo root using a logical path `HW4`:

```bash
coqc -Q . HW4 Maps.v
coqc -Q . HW4 STLC.v
coqc -Q . HW4 UTLC.v
```

Or create a `_CoqProject` with:

```
-Q . HW4
```

then:

```bash
coq_makefile -f _CoqProject -o Makefile
make
```

## Quick use (REPL)

```bash
coqtop -Q . HW4
```

```coq
Require Import HW4.Maps HW4.UTLC HW4.STLC.
```

## Highlights

* Convenient notations: `x |-> v ; Γ` for context/map updates, `\x:T, e`, `e1 e2`, `if … then … else …`.
* Example results:

  * `UTLC`: existence of a step for a compound term (Q1), `iszero` on Church numerals (Q2), and a substitution derivation (Q3).
  * `STLC`: non-typability of `(\x. x x)` at any type (Q4), weakening (Q5), and a typed higher-order function (Q6).

> Coq standard library only; no external deps. Tested with recent Coq versions.

