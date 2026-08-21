import MechDesigAdjointfunctor.Lean.Basic

/-!
# MechDesigAdjointfunctor — Root Import

A Lean 4 formalisation of the categorical unification of Myerson's Revenue
Equivalence Theorem and the Mirrlees Taxation Principle as instances of a single
Master Theorem about the adjunction Q ⊣ T.

## Module structure

| File | Contents |
|------|----------|
| `Framework` | Stage 1 — categories Mech, Alloc; functor Q; Lemmas 1.7–1.8 |
| `MyersonSetting` | Stage 2 — Myerson auction; SC; Lemma 2.1 |
| `MirrleesSetting` | Stage 3 — Mirrlees taxation; SC-M; Lemma 3.1 |
| `MasterTheorem` | Stage 4 — Transfer Functor T; adjunction Q ⊣ T; Theorem 4.5 |
| `Corollaries` | Stage 5 — Revenue Equivalence; Taxation Principle |
-/
