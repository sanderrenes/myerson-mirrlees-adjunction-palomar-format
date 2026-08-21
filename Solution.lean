import MechDesigAdjointfunctor.Basic

/-!
# Proved solution

This module may import the full proof development. Comparator checks that the
declaration below has exactly the same statement as its counterpart in
`Challenge.lean` and uses only the permitted axioms.
-/

namespace MechDesign

open CategoryTheory MeasureTheory

-- The adjunction T ⊣ Q
noncomputable def adj_T_Q {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} (θ_min : ℝ)
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D)
    (hD : ∀ θ, θ ∈ D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c)
    (hint : ∀ (r : MonotoneAlloc A) a b,
      IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b)
    (L : NNReal)
    (hvLip : ∀ (m : ICIRMechanism A v θ_min) (θ' : ℝ),
        LipschitzOnWith L (v (m.mech.q θ')) (Set.Ici θ_min))
    (hW : ∀ (m : ICIRMechanism A v θ_min) (θ : ℝ), θ_min ≤ θ →
        ContinuousWithinAt (fun p : ℝ × ℝ => deriv (v (m.mech.q p.1)) p.2)
            (Set.Ici θ ×ˢ Set.Ici θ) (θ, θ)) :
    T (θ_min := θ_min) hθ_pos hSC hD_Ioi hdiff hintC hint ⊣ Q (θ_min := θ_min) hSC hD :=
  adj_T_Q_impl θ_min hθ_pos hSC hD hD_Ioi hdiff hintC hint L hvLip hW

-- Theorem 4.5(i) — Existence
theorem masterTheorem_existence {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (r : MonotoneAlloc A)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hint : ∀ a b, IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b)
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c) :
    ∃! (m : ICIRMechanism A v θ_min),
      m ∈ MechWithAlloc r ∧
      ∀ θ, m.mech.t θ = transferFormula v θ_min (typeDerivAlongAlloc v r) r.q θ :=
  masterTheorem_existence_impl hθ_pos hSC hD_Ioi r hdiff hint hintC

-- Theorem 4.5(ii) — Isomorphism
theorem masterTheorem_isomorphism {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (r : MonotoneAlloc A)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hint : ∀ a b, IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b)
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c)
    (m : ICIRMechanism A v θ_min) (hm : m ∈ MechWithAlloc r)
    (L : NNReal)
    (hvLip : ∀ θ' : ℝ, LipschitzOnWith L (v (m.mech.q θ')) (Set.Ici θ_min))
    (hW : ∀ θ, θ_min ≤ θ →
      ContinuousWithinAt (fun p : ℝ × ℝ => deriv (v (r.q p.1)) p.2)
        (Set.Ici θ ×ˢ Set.Ici θ) (θ, θ))
    (hBC : v (m.mech.q θ_min) θ_min = m.mech.t θ_min) :
    Nonempty (m ≅ Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC) :=
  masterTheorem_isomorphism_impl hθ_pos hSC hD_Ioi r hdiff hint hintC m hm L hvLip hW hBC

-- Theorem 4.5(iii) — Transfer Invariance
theorem masterTheorem_transferInvariance {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    (hθ_pos : 0 < θ_min)
    (r : MonotoneAlloc A)
    (hint : ∀ a b, IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b)
    (hdiff : ∀ a : A, DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (m₁ m₂ : ICIRMechanism A v θ_min)
    (hm₁ : m₁ ∈ MechWithAlloc r) (hm₂ : m₂ ∈ MechWithAlloc r)
    (L₁ : NNReal)
    (hvLip₁ : ∀ θ' : ℝ, LipschitzOnWith L₁ (v (m₁.mech.q θ')) (Set.Ici θ_min))
    (L₂ : NNReal)
    (hvLip₂ : ∀ θ' : ℝ, LipschitzOnWith L₂ (v (m₂.mech.q θ')) (Set.Ici θ_min))
    (hW : ∀ θ, θ_min ≤ θ →
      ContinuousWithinAt (fun p : ℝ × ℝ => deriv (v (r.q p.1)) p.2)
        (Set.Ici θ ×ˢ Set.Ici θ) (θ, θ))
    (hV₀ : surplus m₁ θ_min = surplus m₂ θ_min)
    (μ : MeasureTheory.Measure ℝ) [IsFiniteMeasure μ] :
    ∫ θ in Set.Ici θ_min, m₁.mech.t θ ∂μ = ∫ θ in Set.Ici θ_min, m₂.mech.t θ ∂μ :=
  masterTheorem_transferInvariance_impl hθ_pos r hint hdiff m₁ m₂ hm₁ hm₂ L₁ hvLip₁ L₂ hvLip₂ hW hV₀ μ

-- Revenue Equivalence Theorem
theorem revenueEquivalence
    (θ_min : ℝ) (hθ_pos : 0 < θ_min)
    (q₀ : MonotoneAlloc Myerson.MyersonAlloc)
    (m₁ m₂ : ICIRMechanism Myerson.MyersonAlloc Myerson.myersonValue θ_min)
    (hm₁_alloc : m₁ ∈ MechWithAlloc q₀)
    (hm₂_alloc : m₂ ∈ MechWithAlloc q₀)
    (hint : ∀ a b, IntervalIntegrable
      (typeDerivAlongAlloc Myerson.myersonValue q₀)
      MeasureTheory.volume a b)
    (L₁ : NNReal)
    (hvLip₁ : ∀ θ' : ℝ,
      LipschitzOnWith L₁ (Myerson.myersonValue (m₁.mech.q θ')) (Set.Ici θ_min))
    (L₂ : NNReal)
    (hvLip₂ : ∀ θ' : ℝ,
      LipschitzOnWith L₂ (Myerson.myersonValue (m₂.mech.q θ')) (Set.Ici θ_min))
    (hW : ∀ θ, θ_min ≤ θ →
      ContinuousWithinAt (fun p : ℝ × ℝ => deriv (Myerson.myersonValue (q₀.q p.1)) p.2)
        (Set.Ici θ ×ˢ Set.Ici θ) (θ, θ))
    (hV₀ : surplus m₁ θ_min = surplus m₂ θ_min)
    (μ : MeasureTheory.Measure ℝ) [IsFiniteMeasure μ] :
    ∫ θ in Set.Ici θ_min, m₁.mech.t θ ∂μ = ∫ θ in Set.Ici θ_min, m₂.mech.t θ ∂μ :=
  Corollaries.revenueEquivalence_impl θ_min hθ_pos q₀ m₁ m₂ hm₁_alloc hm₂_alloc hint L₁ hvLip₁ L₂ hvLip₂ hW hV₀ μ

-- Mirrlees Taxation Principle
theorem taxationPrinciple
    (h g : ℝ → ℝ) (hh : Differentiable ℝ h) (hg : Differentiable ℝ g)
    (θ_min : ℝ) (hθ_pos : 0 < θ_min)
    (q₀ : MonotoneAlloc ℝ)
    (m₁ m₂ : ICIRMechanism ℝ (Mirrlees.mirrleesValue h g) θ_min)
    (hm₁_alloc : ∀ θ, m₁.mech.q θ = q₀.q θ)
    (hm₂_alloc : ∀ θ, m₂.mech.q θ = q₀.q θ)
    (hint : ∀ a b, IntervalIntegrable
      (typeDerivAlongAlloc (Mirrlees.mirrleesValue h g) q₀)
      MeasureTheory.volume a b)
    (L₁ : NNReal)
    (hvLip₁ : ∀ θ' : ℝ,
      LipschitzOnWith L₁ (Mirrlees.mirrleesValue h g (m₁.mech.q θ')) (Set.Ici θ_min))
    (L₂ : NNReal)
    (hvLip₂ : ∀ θ' : ℝ,
      LipschitzOnWith L₂ (Mirrlees.mirrleesValue h g (m₂.mech.q θ')) (Set.Ici θ_min))
    (hW : ∀ θ, θ_min ≤ θ →
      ContinuousWithinAt (fun p : ℝ × ℝ => deriv (Mirrlees.mirrleesValue h g (q₀.q p.1)) p.2)
        (Set.Ici θ ×ˢ Set.Ici θ) (θ, θ))
    (hV₀ : surplus m₁ θ_min = surplus m₂ θ_min)
    (μ : MeasureTheory.Measure ℝ) [IsFiniteMeasure μ] :
    ∫ θ in Set.Ici θ_min, m₁.mech.t θ ∂μ = ∫ θ in Set.Ici θ_min, m₂.mech.t θ ∂μ :=
  Corollaries.taxationPrinciple_impl h g hh hg θ_min hθ_pos q₀ m₁ m₂ hm₁_alloc hm₂_alloc hint L₁ hvLip₁ L₂ hvLip₂ hW hV₀ μ

end MechDesign
