# MechDesigAdjointfunctor — Palomar Template Adaptation

Formalization of the categorical unification of Myerson's Revenue Equivalence Theorem and Mirrlees Taxation Principle via adjunction Q ⊣ T. This establishes a deep connection between auction theory and optimal taxation through category theory.

**Repository**: Adapted from [MechDesigAdjointfunctor.lean](https://github.com/sanderrenes/MechDesigAdjointfunctor.lean)

**Commit SHA**: `1e1fe1874e3e1fd0c2ead4ccb3df869c5e365cc8`

**Status**: ✅ All verifications passed. Ready for Palomar submission.

---

## Mathematical Significance

This formalization provides a categorical foundation for mechanism design theory:

1. **Unifying Disparate Results**: Shows that Myerson's Revenue Equivalence (auction theory) and Mirrlees Taxation Principle (optimal taxation) are both corollaries of a single Master Theorem

2. **Categorical Insight**: The adjunction Q ⊣ T reveals that the relationship between mechanisms and allocations is fundamentally categorical, not merely analytical

3. **General Framework**: The Master Theorem provides existence, uniqueness, and characterization for BIC-IR mechanisms that subsumes both classical results

4. **Transfer Invariance**: Mechanisms with the same allocation rule and boundary conditions must have the same transfers, regardless of implementation

This work bridges auction theory and optimal taxation through category theory, providing a unifying perspective on mechanism design.

---

## Repository Structure

```
MechDesigAdjointfunctor/
├── Lean/
│   ├── Framework.lean      # Category theory framework (Mech, Alloc)
│   ├── MasterTheorem.lean  # Main adjunction T ⊣ Q + Master Theorem (4.3, 4.5)
│   ├── MyersonSetting.lean # Myerson auction environment
│   ├── MirrleesSetting.lean # Mirrlees taxation environment
│   └── Corollaries.lean    # Revenue Equivalence & Taxation Principle
├── Basic.lean             # Re-exports all modules
Challenge.lean              # Statement surface with sorry
Solution.lean               # Proofs referencing library
comparator.json            # Comparator configuration
formalization.yaml         # Metadata
```

---

## Main Results

The formalization proves that Myerson's Revenue Equivalence Theorem and Mirrlees Taxation Principle are both instances of a single Master Theorem about the adjunction Q ⊣ T:

1. **`adj_T_Q`**: The adjunction T ⊣ Q between categories Mech and Alloc (Theorem 4.3)
2. **`masterTheorem_existence`**: For any monotone allocation, there exists a unique BIC-IR mechanism (Theorem 4.5(i))
3. **`masterTheorem_isomorphism`**: Every BIC-IR mechanism with given allocation is isomorphic to T(r) (Theorem 4.5(ii))
4. **`masterTheorem_transferInvariance`**: Mechanisms with same allocation and boundary rent have same transfers (Theorem 4.5(iii))
5. **`revenueEquivalence`**: Myerson's Revenue Equivalence Theorem
6. **`taxationPrinciple`**: Mirrlees Taxation Principle

---

## Implementation Summary

### Phase 1: Setup
- Renamed package from PalomarTemplate to MechDesigAdjointfunctor
- Updated directory structure
- Configured lakefile.toml with correct dependencies

### Phase 2: Content Migration
- Copied source content to library directory
- Organized into logical modules (Framework, MasterTheorem, MyersonSetting, MirrleesSetting, Corollaries)
- Ensured all imports resolve correctly

### Phase 3: Challenge & Solution Files
- **Challenge.lean**: Statement-only surface with `sorry` for all 6 main theorems
- **Solution.lean**: Proofs referencing `_impl` versions from library
- All docstrings preserved with mathematical precision

### Phase 4: Metadata
- **comparator.json**: List all 5 theorems + 1 definition
- **formalization.yaml**: Complete metadata, no TEMPLATE values

### Phase 5: Verification
- `lake build Challenge Solution`: ✅ PASS
- `ruby scripts/validate-formalization.rb`: ✅ PASS (no TEMPLATE values)
- `./scripts/verify-comparator.sh`: ✅ PASS ("Your solution is okay!")

---

## Verification Commands

```bash
# Build the project
lake build Challenge Solution

# Validate metadata
ruby scripts/validate-formalization.rb

# Run comparator
./scripts/verify-comparator.sh
```

---

## Submission

The repository is ready for submission to Palomar:

1. Go to: https://submit.palomar-registry.org/
2. Enter commit SHA: `1e1fe1874e3e1fd0c2ead4ccb3df869c5e365cc8`
3. Fill in submission details

---

## Technical Notes

- **Namespace**: `MechDesign`
- **Lean Version**: 4.30.0
- **Mathlib Revision**: c5ea00351c28e24afc9f0f84379aa41082b1188f
- **Permitted Axioms**: propext, Quot.sound, Classical.choice
- **License**: Apache-2.0
