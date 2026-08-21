import MechDesigAdjointfunctor.Lean.Framework
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Perfect
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Stage 4: The Master Theorem — Adjunction Q ⊣ T

Proves the abstract categorical Master Theorem: the allocation functor
**Q : Mech → Alloc** has a right adjoint **T : Alloc → Mech**, and the right
adjoint is unique up to natural isomorphism.  Every IC-IR mechanism with a given
allocation rule is isomorphic to `T(q)`.

## Main declarations

* `MechDesign.transferFormula` — the abstract envelope transfer formula
* `MechDesign.typeDerivAlongAlloc` — the type-partial derivative along an allocation rule
* `MechDesign.T_wellDefined` — `T(q)` is BIC-IR for any monotone `q` (Lemma 4.2)
* `MechDesign.Tmech` — the mechanism object `T(r)`
* `MechDesign.T` — the Transfer Functor `T : Alloc → Mech` (Definition 4.1)
* `MechDesign.Tmech_surplus_mono` — `T` is monotone on surpluses (single crossing alone)
* `MechDesign.adj_T_Q` — the adjunction `T ⊣ Q` (Theorem 4.3); `T` is the **left** adjoint
* `MechDesign.T_initial` — `T(q)` is **initial** in **Mech_q** (Corollary 4.4)
* `MechDesign.surplus_split` — the envelope theorem in surplus form; the fiber structure
* `MechDesign.envelope_transfer_le` — any BIC-IR transfer is dominated by `t*`
* `MechDesign.envelope_transfer_shift` — `m.t θ = t*(θ) - V_m(θ_min)` (no boundary cond.)
* `MechDesign.envelope_transfer_unique` — with `V(θ_min) = 0`, that transfer *is* `t*`
* `MechDesign.transfer_eq_of_iso` — an iso in **Mech** forces equal transfers
* `MechDesign.Mech₀`, `MechDesign.equivAllocMech₀` — `Alloc ≌ Mech₀` (Taxation Principle)
* `MechDesign.masterTheorem_existence` — existence and uniqueness (Thm 4.5 i)
* `MechDesign.masterTheorem_isomorphism_impl — every BIC mechanism ≅ `T(q)` (Thm 4.5 ii)
* `MechDesign.masterTheorem_transferInvariance` — transfer invariance (Thm 4.5 iii)

## References

* Mac Lane (1978), *Categories for the Working Mathematician*, Chapter IV
* Myerson (1981), *Optimal Auction Design*, Theorem 2
* Hammond (1979), *Straightforward Incentive Compatibility*, Theorem 1
* Rochet (1985), *The Taxation Principle*, Proposition 1
-/

open CategoryTheory CategoryTheory.Limits MeasureTheory Filter

namespace MechDesign

/-! ### 4.1 The Transfer Functor **T : Alloc → Mech** (Definition 4.1) -/

/-- **The abstract envelope transfer formula** (Definition 4.1):
given the type-partial derivative `vθ_partial s = (∂v/∂s)(q(s), s)`, the unique
BIC transfer with boundary condition `V(θ_min) = 0` is

  `t*(θ) = v(q(θ), θ) - ∫_{θ_min}^θ (∂v/∂s)(q(s), s) ds`

*Reference*: Definition 4.1; Lemmas 2.1, 3.1. -/
noncomputable def transferFormula {A : Type*} (v : A → ℝ → ℝ) (θ_min : ℝ)
    (vθ_partial : ℝ → ℝ) -- s ↦ (∂v/∂s)(q(s), s), the type-derivative along q
    (q : ℝ → A) (θ : ℝ) : ℝ :=
  v (q θ) θ - ∫ s in θ_min..θ, vθ_partial s

/-- The type-partial derivative `s ↦ (∂v/∂s)(q(s), s)` induced by a monotone
allocation rule `q`.  Used as input to `transferFormula`. -/
noncomputable def typeDerivAlongAlloc {A : Type*} [Preorder A]
    (v : A → ℝ → ℝ) (q : MonotoneAlloc A) : ℝ → ℝ :=
  fun s => deriv (v (q.q s)) s

/-- **Lemma 4.2**: For any monotone allocation rule `r`, the mechanism
`T(r) = (r.q, transferFormula(...))` is BIC and IR.
Proof uses the if-direction of Lemmas 2.1 and 3.1: the envelope formula produces
an IC mechanism whenever `q` is non-decreasing under SC.
*Reference*: Lemma 4.2. -/
lemma T_wellDefined {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (r : MonotoneAlloc A)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hint : ∀ a b, IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b)
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c) :
    IsIC v θ_min ⟨r.q, transferFormula v θ_min (typeDerivAlongAlloc v r) r.q⟩ ∧
    IsIR v θ_min ⟨r.q, transferFormula v θ_min (typeDerivAlongAlloc v r) r.q⟩ := by
  refine ⟨?_, ?_⟩
  · -- IsIC: V(θ) ≥ U(θ, θ') for all physical θ, θ' (θ_min ≤ θ, θ_min ≤ θ').
    -- Since θ_min > 0, both θ > 0 and θ' > 0 always, so FTC + SC + integral_mono apply.
    intro θ θ' hθ hθ'
    have hθ'_pos : 0 < θ' := lt_of_lt_of_le hθ_pos hθ'
    have hθ_pos' : 0 < θ := lt_of_lt_of_le hθ_pos hθ
    -- Unfold to integral inequality form.
    change v (r.q θ) θ - transferFormula v θ_min (typeDerivAlongAlloc v r) r.q θ ≥
        v (r.q θ') θ - transferFormula v θ_min (typeDerivAlongAlloc v r) r.q θ'
    simp only [transferFormula]
    -- After simp, need:
    --   v(qθ,θ) - (v(qθ,θ) - I θ) ≥ v(qθ',θ) - (v(qθ',θ') - I θ')
    -- where I x = ∫_{θ_min}^x typeDerivAlongAlloc v r s.
    -- Equivalent: I θ - I θ' ≥ v(qθ',θ) - v(qθ',θ').
    -- Using interval split (hint): I θ - I θ' = ∫_{θ'}^θ D.
    set Iθ : ℝ := ∫ s in θ_min..θ, typeDerivAlongAlloc v r s with hIθ_def
    set Iθ' : ℝ := ∫ s in θ_min..θ', typeDerivAlongAlloc v r s with hIθ'_def
    set Iθ'_θ : ℝ := ∫ s in θ'..θ, typeDerivAlongAlloc v r s with hIθ'θ_def
    -- Interval split: I θ_min..θ' + ∫_{θ'}^θ = ∫_{θ_min}^θ
    have hsplit : Iθ' + Iθ'_θ = Iθ := by
      rw [hIθ_def, hIθ'_def, hIθ'θ_def]
      exact intervalIntegral.integral_add_adjacent_intervals (hint θ_min θ') (hint θ' θ)
    -- Reduce the goal to: Iθ'_θ ≥ v(qθ', θ) - v(qθ', θ')
    suffices h : Iθ'_θ ≥ v (r.q θ') θ - v (r.q θ') θ' by linarith
    -- Physical case: both θ, θ' > 0 (from θ_min > 0 and IsIC restriction).
    · -- FTC: ∫_{θ'}^θ deriv(v(qθ')) s = v(qθ', θ) - v(qθ', θ')
      have hFTC : (∫ s in θ'..θ, deriv (v (r.q θ')) s) = v (r.q θ') θ - v (r.q θ') θ' := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        · intro s hs
          have hs_pos : 0 < s := by
            rcases le_total θ' θ with hle | hle
            · rw [Set.uIcc_of_le hle] at hs; exact lt_of_lt_of_le hθ'_pos hs.1
            · rw [Set.uIcc_of_ge hle] at hs; exact lt_of_lt_of_le hθ_pos' hs.1
          exact ((hdiff (r.q θ')) s hs_pos).differentiableAt
            (IsOpen.mem_nhds isOpen_Ioi hs_pos) |>.hasDerivAt
        · exact hintC (r.q θ') θ' θ
      -- Now: Iθ'_θ ≥ ∫_{θ'}^θ deriv(v(qθ')) s.
      -- This holds by integral_mono via SC + monotonicity of r.q.
      rw [← hFTC]
      -- Goal: ∫_{θ'}^θ typeDerivAlongAlloc v r s ≥ ∫_{θ'}^θ deriv (v (r.q θ')) s
      -- Pointwise: typeDerivAlongAlloc v r s = deriv (v (r.q s)) s ≥ deriv (v (r.q θ')) s
      -- when r.q s ≥ r.q θ'.
      rcases le_total θ' θ with hle | hle
      · -- θ' ≤ θ: integration interval is [θ', θ]. For s ∈ [θ', θ], s ≥ θ', so r.q s ≥ r.q θ'.
        -- Goal: ∫ D ≥ ∫ D' = ∫ D' ≤ ∫ D, so hintC (for D') is the first arg, hint (for D) second.
        rw [hIθ'θ_def]
        apply intervalIntegral.integral_mono_on hle (hintC (r.q θ') θ' θ) (hint θ' θ)
        intro s hs
        -- hs : s ∈ Icc θ' θ; need deriv (v (r.q θ')) s ≤ typeDerivAlongAlloc v r s
        unfold typeDerivAlongAlloc
        have hqle : r.q θ' ≤ r.q s := r.hMono hs.1
        rcases lt_or_eq_of_le hqle with hqlt | hqeq
        · have hSCq := hSC (r.q s) (r.q θ') hqlt
          have hs_pos : 0 < s := lt_of_lt_of_le hθ'_pos hs.1
          have hd1 : DifferentiableAt ℝ (v (r.q s)) s :=
            ((hdiff (r.q s)) s hs_pos).differentiableAt
              (IsOpen.mem_nhds isOpen_Ioi hs_pos)
          have hd2 : DifferentiableAt ℝ (v (r.q θ')) s :=
            ((hdiff (r.q θ')) s hs_pos).differentiableAt
              (IsOpen.mem_nhds isOpen_Ioi hs_pos)
          have hhas : HasDerivAt (fun x => v (r.q s) x - v (r.q θ') x)
              (deriv (v (r.q s)) s - deriv (v (r.q θ')) s) s :=
            HasDerivAt.sub hd1.hasDerivAt hd2.hasDerivAt
          have hacc : AccPt s (𝓟 D) := by
            rw [accPt_principal_iff_nhdsWithin]
            exact (right_nhdsWithin_Ioo_neBot hs_pos).mono
              (nhdsWithin_mono _ (fun x hx => ⟨hD_Ioi (Set.mem_Ioi.mpr hx.1), hx.2.ne⟩))
          linarith [hhas.hasDerivWithinAt.nonneg_of_monotoneOn hacc hSCq.monotoneOn]
        · rw [← hqeq]
      · -- θ ≤ θ': backwards integral case — reduce to forward by integral_symm.
        -- Key: ∫_{θ}^{θ'} typeDerivAlongAlloc ≤ ∫_{θ}^{θ'} deriv(v(r.q θ'))
        -- pointwise: r.q s ≤ r.q θ' for s ∈ [θ,θ'], so SC gives deriv(v(r.q s)) ≤ deriv(v(r.q θ')).
        have key : ∫ s in θ..θ', typeDerivAlongAlloc v r s ≤
                   ∫ s in θ..θ', deriv (v (r.q θ')) s :=
          intervalIntegral.integral_mono_on hle (hint θ θ') (hintC (r.q θ') θ θ') (by
            intro s hs
            unfold typeDerivAlongAlloc
            have hqle : r.q s ≤ r.q θ' := r.hMono hs.2
            rcases lt_or_eq_of_le hqle with hqlt | hqeq
            · have hSCq := hSC (r.q θ') (r.q s) hqlt
              have hs_pos : 0 < s := lt_of_lt_of_le hθ_pos' hs.1
              have hd1 : DifferentiableAt ℝ (v (r.q s)) s :=
                ((hdiff (r.q s)) s hs_pos).differentiableAt
                  (IsOpen.mem_nhds isOpen_Ioi hs_pos)
              have hd2 : DifferentiableAt ℝ (v (r.q θ')) s :=
                ((hdiff (r.q θ')) s hs_pos).differentiableAt
                  (IsOpen.mem_nhds isOpen_Ioi hs_pos)
              -- HasDerivAt for the difference function, then use nonneg_of_monotoneOn
              have hhas : HasDerivAt (fun x => v (r.q θ') x - v (r.q s) x)
                  (deriv (v (r.q θ')) s - deriv (v (r.q s)) s) s :=
                HasDerivAt.sub hd2.hasDerivAt hd1.hasDerivAt
              have hacc : AccPt s (𝓟 D) := by
                rw [accPt_principal_iff_nhdsWithin]
                exact (right_nhdsWithin_Ioo_neBot hs_pos).mono
                  (nhdsWithin_mono _ (fun x hx => ⟨hD_Ioi (Set.mem_Ioi.mpr hx.1), hx.2.ne⟩))
              linarith [hhas.hasDerivWithinAt.nonneg_of_monotoneOn hacc hSCq.monotoneOn]
            · rw [← hqeq])
        -- integral_symm θ θ' : ∫ x in θ'..θ, f x = -∫ x in θ..θ', f x
        have h1 : ∫ s in θ'..θ, typeDerivAlongAlloc v r s =
                  -∫ s in θ..θ', typeDerivAlongAlloc v r s :=
          intervalIntegral.integral_symm θ θ'
        have h2 : ∫ s in θ'..θ, deriv (v (r.q θ')) s =
                  -∫ s in θ..θ', deriv (v (r.q θ')) s :=
          intervalIntegral.integral_symm θ θ'
        rw [hIθ'θ_def, h1]
        linarith [h2]
  · -- IsIR: v(r.q θ_min, θ_min) - t*(θ_min) ≥ 0
    -- t*(θ_min) = v(r.q θ_min, θ_min) - ∫_{θ_min}^{θ_min} D = v(...) - 0
    change v (r.q θ_min) θ_min -
        transferFormula v θ_min (typeDerivAlongAlloc v r) r.q θ_min ≥ 0
    simp only [transferFormula, intervalIntegral.integral_same, sub_zero]
    linarith

/-- The BIC-IR mechanism `T(r) = (r.q, t*)` as an element of `ICIRMechanism`. -/
noncomputable def Tmech {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (r : MonotoneAlloc A)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hint : ∀ a b, IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b)
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c) :
    ICIRMechanism A v θ_min :=
  { mech := ⟨r.q, transferFormula v θ_min (typeDerivAlongAlloc v r) r.q⟩
    hMono := r.hMono
    hIC   := (T_wellDefined hθ_pos hSC hD_Ioi r hdiff hint hintC).1
    hIR   := (T_wellDefined hθ_pos hSC hD_Ioi r hdiff hint hintC).2 }

/-- **Single crossing, pointwise on integrands.**  If one allocation rule dominates
another at a physical type `s`, its envelope integrand dominates there too.

This is the SC step of `T_wellDefined`, lifted out for reuse: it is the only ingredient
`T.map` needs.  No convexity or affinity of `v` in the allocation is required. -/
lemma typeDeriv_mono_of_alloc_le {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {D : Set ℝ}
    (hSC : SingleCrossing v D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (r r' : MonotoneAlloc A) (hle : ∀ θ, r.q θ ≤ r'.q θ)
    {s : ℝ} (hs_pos : 0 < s) :
    typeDerivAlongAlloc v r s ≤ typeDerivAlongAlloc v r' s := by
  unfold typeDerivAlongAlloc
  rcases lt_or_eq_of_le (hle s) with hqlt | hqeq
  · have hSCq := hSC (r'.q s) (r.q s) hqlt
    have hd1 : DifferentiableAt ℝ (v (r.q s)) s :=
      ((hdiff (r.q s)) s hs_pos).differentiableAt (IsOpen.mem_nhds isOpen_Ioi hs_pos)
    have hd2 : DifferentiableAt ℝ (v (r'.q s)) s :=
      ((hdiff (r'.q s)) s hs_pos).differentiableAt (IsOpen.mem_nhds isOpen_Ioi hs_pos)
    have hhas : HasDerivAt (fun x => v (r'.q s) x - v (r.q s) x)
        (deriv (v (r'.q s)) s - deriv (v (r.q s)) s) s :=
      HasDerivAt.sub hd2.hasDerivAt hd1.hasDerivAt
    have hacc : AccPt s (𝓟 D) := by
      rw [accPt_principal_iff_nhdsWithin]
      exact (right_nhdsWithin_Ioo_neBot hs_pos).mono
        (nhdsWithin_mono _ (fun x hx => ⟨hD_Ioi (Set.mem_Ioi.mpr hx.1), hx.2.ne⟩))
    linarith [hhas.hasDerivWithinAt.nonneg_of_monotoneOn hacc hSCq.monotoneOn]
  · rw [hqeq]

/-- The surplus of `T(r)` collapses to the bare envelope integral: the `v (q θ) θ` term
in the transfer formula cancels against the one in `V = v (q θ) θ - t θ`.  This
cancellation is quasilinearity doing its work. -/
lemma surplus_Tmech {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (r : MonotoneAlloc A)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hint : ∀ a b, IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b)
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c)
    (θ : ℝ) :
    surplus (Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC) θ =
      ∫ s in θ_min..θ, typeDerivAlongAlloc v r s := by
  simp [surplus, Tmech, transferFormula]

/-- **`T` is monotone on surpluses** — the field `T.map` must supply.
`r.q ≤ r'.q` pointwise implies `V_{T(r)} ≤ V_{T(r')}` on `[θ_min, ∞)`.

Proved from **single crossing alone**, via `typeDeriv_mono_of_alloc_le` and
`integral_mono_on`.  This is what fails for a transfer-ordered `MechHom`, and it is why
**Mech** is ordered by surplus. -/
theorem Tmech_surplus_mono {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (r r' : MonotoneAlloc A) (hle : ∀ θ, r.q θ ≤ r'.q θ)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hint : ∀ a b, IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b)
    (hint' : ∀ a b, IntervalIntegrable (typeDerivAlongAlloc v r') MeasureTheory.volume a b)
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c) :
    ∀ θ : ℝ, θ_min ≤ θ →
      surplus (Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC) θ ≤
      surplus (Tmech hθ_pos hSC hD_Ioi r' hdiff hint' hintC) θ := by
  intro θ hθ
  rw [surplus_Tmech, surplus_Tmech]
  apply intervalIntegral.integral_mono_on hθ (hint θ_min θ) (hint' θ_min θ)
  intro s hs
  exact typeDeriv_mono_of_alloc_le hSC hD_Ioi hdiff r r' hle (lt_of_lt_of_le hθ_pos hs.1)

/-- **T : Alloc → Mech** — the Transfer Functor (Definition 4.1).
- On objects: `T(r) = (r.q, t*)` where `t*` is the envelope transfer formula.
- On morphisms: `T(φ) = φ` — the same type transformation on the allocation, with the
  surplus condition supplied by `Tmech_surplus_mono`.

Functoriality rests on **single crossing** and nothing else.  Under the surplus order on
**Mech** (see the design note on `MechHom`), `T` is a genuine functor for every value
function the framework admits — in particular for both `myersonValue` and
`mirrleesValue`.

*Reference*: Definition 4.1. -/
noncomputable def T {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c)
    (hint : ∀ (r : MonotoneAlloc A) a b,
      IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b) :
    MonotoneAlloc A ⥤ ICIRMechanism A v θ_min where
  obj r     := Tmech hθ_pos hSC hD_Ioi r hdiff (hint r) hintC
  map {r r'} f :=
    { hAlloc := f.h
      hSurp  := Tmech_surplus_mono hθ_pos hSC hD_Ioi r r' f.h hdiff
                  (hint r) (hint r') hintC }
  map_id _     := by apply @Subsingleton.elim _ mechHom_subsingleton
  map_comp _ _ := by apply @Subsingleton.elim _ mechHom_subsingleton

/-- The set of all BIC-IR mechanisms with allocation rule equal to `r.q` pointwise. -/
def MechWithAlloc {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    (r : MonotoneAlloc A) : Set (ICIRMechanism A v θ_min) :=
  {m | ∀ θ, m.mech.q θ = r.q θ}

/-! #### The IC sandwich, and continuity of the surplus

The first place incentive compatibility does any work.  `hIC` alone — no analysis — bounds
the change in surplus between two types, on both sides, by the change in value along a
*fixed* allocation. -/

/-- **The IC sandwich.**  For any two physical types, using each one's report as the other's
deviation:

  `v(q θ₁, θ₂) − v(q θ₁, θ₁)  ≤  V(θ₂) − V(θ₁)  ≤  v(q θ₂, θ₂) − v(q θ₂, θ₁)`

Both bounds move the *type* while holding the *allocation* fixed, which is what makes them
usable: they are increments of `v(a, ·)` for a single `a`.  Pure `hIC`; no differentiability,
no single crossing, no IR.  The order of `θ₁` and `θ₂` is irrelevant. -/
theorem surplus_ic_sandwich {A : Type*} [Preorder A] {v : A → ℝ → ℝ} {θ_min : ℝ}
    (m : ICIRMechanism A v θ_min) {θ₁ θ₂ : ℝ} (h₁ : θ_min ≤ θ₁) (h₂ : θ_min ≤ θ₂) :
    v (m.mech.q θ₁) θ₂ - v (m.mech.q θ₁) θ₁ ≤ surplus m θ₂ - surplus m θ₁ ∧
    surplus m θ₂ - surplus m θ₁ ≤ v (m.mech.q θ₂) θ₂ - v (m.mech.q θ₂) θ₁ := by
  -- type θ₂ does not want to report θ₁, and type θ₁ does not want to report θ₂
  have hA := m.hIC θ₂ θ₁ h₂ h₁
  have hB := m.hIC θ₁ θ₂ h₁ h₂
  simp only [surplus]
  constructor <;> linarith

/-- **The surplus is Lipschitz — derived from IC.**

If the value function is `L`-Lipschitz in the *type* along every allocation the mechanism
actually uses, then the surplus is `L`-Lipschitz on the physical domain.  Immediate from
`surplus_ic_sandwich`: both sides of the sandwich are increments of some `v(a, ·)`, and each
is bounded by `L·|Δθ|`.

The hypothesis quantifies over the allocations `m` uses (`v (m.mech.q θ')`), not over all of
`A` — a uniform bound over *all* allocations would be false for `MyersonAlloc = ℝ`. -/
theorem surplus_lipschitzOn {A : Type*} [Preorder A] {v : A → ℝ → ℝ} {θ_min : ℝ}
    (m : ICIRMechanism A v θ_min) (L : NNReal)
    (hvLip : ∀ θ' : ℝ, LipschitzOnWith L (v (m.mech.q θ')) (Set.Ici θ_min)) :
    LipschitzOnWith L (surplus m) (Set.Ici θ_min) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  obtain ⟨hlow, hhigh⟩ := surplus_ic_sandwich m (Set.mem_Ici.mp hy) (Set.mem_Ici.mp hx)
  -- the two sandwich bounds are increments of `v (q y, ·)` and `v (q x, ·)` respectively
  have hy' := (hvLip y).dist_le_mul x hx y hy
  have hx' := (hvLip x).dist_le_mul x hx y hy
  rw [Real.dist_eq, Real.dist_eq] at hy' hx' ⊢
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy'
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx'
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The surplus is continuous on the physical domain — **a consequence of IC**, not an
assumption.  This is what `surplus_split` needs, and it is why `hIC` is load-bearing. -/
theorem surplus_continuousOn {A : Type*} [Preorder A] {v : A → ℝ → ℝ} {θ_min : ℝ}
    (m : ICIRMechanism A v θ_min) (L : NNReal)
    (hvLip : ∀ θ' : ℝ, LipschitzOnWith L (v (m.mech.q θ')) (Set.Ici θ_min)) :
    ContinuousOn (surplus m) (Set.Ici θ_min) :=
  (surplus_lipschitzOn m L hvLip).continuousOn

/-- **The envelope theorem (only-if direction), from IC — Milgrom–Segal.**

The surplus has a **right derivative** equal to the envelope integrand at every physical
type.  This is `hEnv`, no longer assumed but *proved*, and it is what closes the bridge from
incentive compatibility to the envelope condition.

*Proof.*  Divide the IC sandwich by `y - θ > 0`:

```
(v(q θ, y) − v(q θ, θ))/(y−θ)  ≤  slope V  ≤  (v(q y, y) − v(q y, θ))/(y−θ)
```

The **lower** bound is a slope of `v(q θ, ·)` at `θ`, so it tends to `∂_θ v(q θ, θ) = D θ`.
The **upper** bound is a slope of `v(q y, ·)`, which the mean value theorem turns into
`∂_θ v(q y, ξ)` for some `ξ ∈ (θ, y)`; as `y ↓ θ` both `y` and `ξ` collapse to `θ`, so `hW`
sends it to `D θ` as well.  Squeeze.

**On `hW`.**  The framework's allocation space `A` carries no topology, so we cannot state
"`q` is right-continuous" directly.  `hW` instead asks the *composite*
`(s, u) ↦ ∂_θ v(q s, u)` to be continuous at `(θ, θ)` from the upper-right quadrant — which
is exactly what the squeeze needs, and is strictly weaker than joint continuity plus
right-continuity of `q`.  In the Myerson setting `∂_θ v(a, u) = a`, so `hW` *is* precisely
right-continuity of `q` — and the posted price satisfies it (`q` jumps *up* at the reserve,
and `q p = 1`), which is why reserve prices survive.  See `PostedPrice.postedPrice_hW`. -/
theorem surplus_hasDerivWithinAt {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ} (hθ_pos : 0 < θ_min)
    (r : MonotoneAlloc A)
    (hdiff : ∀ a : A, DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (m : ICIRMechanism A v θ_min) (hm : m ∈ MechWithAlloc r)
    {θ : ℝ} (hθ : θ_min ≤ θ)
    (hW : ContinuousWithinAt (fun p : ℝ × ℝ => deriv (v (r.q p.1)) p.2)
            (Set.Ici θ ×ˢ Set.Ici θ) (θ, θ)) :
    HasDerivWithinAt (surplus m) (typeDerivAlongAlloc v r θ) (Set.Ioi θ) θ := by
  have hθ0 : 0 < θ := lt_of_lt_of_le hθ_pos hθ
  have hDθ : typeDerivAlongAlloc v r θ = deriv (v (r.q θ)) θ := rfl
  rw [hasDerivWithinAt_iff_tendsto_slope, Set.diff_singleton_eq_self (by simp), hDθ]
  -- LOWER BOUND: a slope of `v (q θ, ·)` at θ, so it tends to `D θ` by differentiability.
  have hdA : DifferentiableAt ℝ (v (r.q θ)) θ :=
    ((hdiff (r.q θ)) θ hθ0).differentiableAt (IsOpen.mem_nhds isOpen_Ioi hθ0)
  have hlow : Filter.Tendsto (slope (v (r.q θ)) θ) (nhdsWithin θ (Set.Ioi θ))
      (nhds (deriv (v (r.q θ)) θ)) :=
    (hasDerivAt_iff_tendsto_slope.mp hdA.hasDerivAt).mono_left
      (nhdsWithin_mono θ (fun x hx => ne_of_gt hx))
  -- UPPER BOUND: MVT turns it into `∂_θ v(q y, ξ)`, and `hW` collapses that to `D θ`.
  have hup : Filter.Tendsto (fun y => (v (r.q y) y - v (r.q y) θ) / (y - θ))
      (nhdsWithin θ (Set.Ioi θ)) (nhds (deriv (v (r.q θ)) θ)) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousWithinAt_iff.mp hW ε hε
    refine ⟨δ, hδpos, fun {y} hy hyd => ?_⟩
    have hθy : θ < y := hy
    have hsub : Set.Icc θ y ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le hθ0 hx.1
    have hcont : ContinuousOn (v (r.q y)) (Set.Icc θ y) :=
      ((hdiff (r.q y)).mono hsub).continuousOn
    have hdon : DifferentiableOn ℝ (v (r.q y)) (Set.Ioo θ y) :=
      (hdiff (r.q y)).mono (fun x hx => lt_of_lt_of_le hθ0 (le_of_lt hx.1))
    obtain ⟨c, hc, hceq⟩ := exists_deriv_eq_slope (v (r.q y)) hθy hcont hdon
    rw [← hceq]
    have hmem : ((y, c) : ℝ × ℝ) ∈ Set.Ici θ ×ˢ Set.Ici θ :=
      Set.mem_prod.mpr ⟨Set.mem_Ici.mpr (le_of_lt hθy), Set.mem_Ici.mpr (le_of_lt hc.1)⟩
    have h1 : dist y θ < δ := hyd
    have hy1 : y - θ < δ := by rwa [Real.dist_eq, abs_of_pos (sub_pos.mpr hθy)] at h1
    have h2 : dist c θ < δ := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hc.1)]
      linarith [hc.2]
    have hdist : dist ((y, c) : ℝ × ℝ) (θ, θ) < δ := by
      rw [Prod.dist_eq]; exact max_lt h1 h2
    exact hδ hmem hdist
  -- SQUEEZE
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with y hy
    have hθy : θ < y := hy
    have hpos : (0:ℝ) < y - θ := sub_pos.mpr hθy
    have hs := (surplus_ic_sandwich m hθ (le_of_lt (lt_of_le_of_lt hθ hθy))).1
    rw [hm θ] at hs
    rw [slope_def_field, slope_def_field]
    gcongr
  · filter_upwards [self_mem_nhdsWithin] with y hy
    have hθy : θ < y := hy
    have hpos : (0:ℝ) < y - θ := sub_pos.mpr hθy
    have hs := (surplus_ic_sandwich m hθ (le_of_lt (lt_of_le_of_lt hθ hθy))).2
    rw [hm y] at hs
    rw [slope_def_field]
    gcongr

/-- **The envelope theorem, in surplus form.**  For any BIC-IR mechanism with allocation
`r.q`, the surplus at a physical type is its boundary rent plus the envelope integral:

  `V_m(θ) = V_m(θ_min) + ∫_{θ_min}^θ (∂v/∂s)(r.q s, s) ds`.

Everything downstream is a reading of this one identity.  The fiber of `Q` over `r` is a
one-parameter family indexed by the boundary rent `V_m(θ_min)`; `T(r)` is the member with
rent `0`; IR says the rent is `≥ 0`; and revenue equivalence says the transfer depends on
the mechanism only through the rent.

**The envelope hypothesis is one-sided, and it has to be.**  `hEnv` asks only for a *right*
derivative of the surplus (`HasDerivWithinAt … (Set.Ioi θ) θ`), together with continuity.
A two-sided `HasDerivAt` would be **false** for the mechanisms that matter: a posted price
with reserve `p` (`q θ = 1{p ≤ θ}`, monotone, IC, IR) has surplus `V θ = max (θ - p) 0`,
which has a *kink* at `p` and no derivative there.  The right derivative survives the kink —
at `p` it is `1 = q p = D p` — so the envelope identity holds while two-sidedness does not.
Mathlib's `integral_eq_sub_of_hasDeriv_right` needs exactly this much.

Demanding `HasDerivAt` would exclude every auction with a reserve price and every allocation
with a bunching region.  See `postedPrice_hasEnvelope` for the mechanism that forces the
issue. -/
theorem surplus_split {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ} (hθ_pos : 0 < θ_min)
    (r : MonotoneAlloc A)
    (hint : ∀ a b, IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b)
    (hdiff : ∀ a : A, DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (m : ICIRMechanism A v θ_min) (hm : m ∈ MechWithAlloc r)
    (L : NNReal)
    (hvLip : ∀ θ' : ℝ, LipschitzOnWith L (v (m.mech.q θ')) (Set.Ici θ_min))
    (hW : ∀ θ, θ_min ≤ θ →
      ContinuousWithinAt (fun p : ℝ × ℝ => deriv (v (r.q p.1)) p.2)
        (Set.Ici θ ×ˢ Set.Ici θ) (θ, θ)) :
    ∀ θ, θ_min ≤ θ →
      surplus m θ = surplus m θ_min + ∫ s in θ_min..θ, typeDerivAlongAlloc v r s := by
  intro θ hθ
  -- NOTHING about the surplus is assumed here.  Continuity comes from IC via the sandwich,
  -- and the envelope derivative comes from IC via Milgrom–Segal.
  have heq : (fun s => v (r.q s) s - m.mech.t s) = surplus m := by
    funext s; simp only [surplus]; rw [hm s]
  have hVcont : ContinuousOn (fun s => v (r.q s) s - m.mech.t s) (Set.Ici θ_min) := by
    rw [heq]; exact surplus_continuousOn m L hvLip
  have hEnv : ∀ x, θ_min ≤ x → HasDerivWithinAt (fun s => v (r.q s) s - m.mech.t s)
      (typeDerivAlongAlloc v r x) (Set.Ioi x) x := by
    intro x hx
    rw [heq]
    exact surplus_hasDerivWithinAt hθ_pos r hdiff m hm hx (hW x hx)
  -- The integration range sits in the physical domain `[θ_min, ∞)`.
  have hsub : Set.uIcc θ_min θ ⊆ Set.Ici θ_min := by
    rw [Set.uIcc_of_le hθ]; exact Set.Icc_subset_Ici_self
  have hFTC : ∫ s in θ_min..θ, typeDerivAlongAlloc v r s =
          (v (r.q θ) θ - m.mech.t θ) - (v (r.q θ_min) θ_min - m.mech.t θ_min) := by
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right (hVcont.mono hsub)
    · intro s hs
      have hs1 : θ_min < s := lt_of_le_of_lt (le_min (le_refl θ_min) hθ) hs.1
      exact hEnv s (le_of_lt hs1)
    · exact hint θ_min θ
  simp only [surplus]
  rw [hm θ, hm θ_min]
  linarith

/-- **`T` is faithful** — immediate, since **Alloc** hom-sets are subsingletons. -/
instance T_faithful {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c)
    (hint : ∀ (r : MonotoneAlloc A) a b,
      IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b) :
    (T hθ_pos hSC hD_Ioi hdiff hintC hint).Faithful where
  map_injective := fun _ => @Subsingleton.elim _ allocHom_subsingleton _ _

/-- **`T` is full**: a `MechHom (T r) (T r')` yields an `AllocHom r r'` by forgetting the
surplus component.

The surplus component was never an extra constraint: `Tmech_surplus_mono` *derives* it
from the allocation inequality via single crossing.  So `T` imposes nothing that **Alloc**
did not already record — which is exactly what fullness says. -/
instance T_full {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c)
    (hint : ∀ (r : MonotoneAlloc A) a b,
      IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b) :
    (T hθ_pos hSC hD_Ioi hdiff hintC hint).Full where
  map_surjective := fun f =>
    ⟨{ h := f.hAlloc }, @Subsingleton.elim _ mechHom_subsingleton _ _⟩

/-! ### 4.2 The Adjunction **T ⊣ Q** (Theorem 4.3) -/

/-- **Theorem 4.3: T ⊣ Q** — the transfer functor `T` is **left** adjoint to the
allocation functor `Q`:

  `Hom_Mech(T(r), m) ≅ Hom_Alloc(r, Q(m))`  naturally in `r` and `m`.

*Proof sketch*.  Both categories are thin, so the adjunction is an order-theoretic
Galois connection and reduces to the two implications
`T(r) ≤ m  ⟺  r ≤ Q(m)`, with naturality and the triangle identities discharged by
`Subsingleton.elim` on hom-sets.
- *unit* `η_r : r ⟶ Q(T(r))`: `Q(T(r)).q = r.q` definitionally, so this is `le_refl`.
- *counit* `ε_m : T(Q(m)) ⟶ m`: allocations agree definitionally, and on surpluses
  `V_{T(Q(m))}(θ) = ∫_{θ_min}^θ D_{m.q} ≤ V_m(θ_min) + ∫_{θ_min}^θ D_{m.q} = V_m(θ)`,
  which is `surplus_split` together with **individual rationality** `V_m(θ_min) ≥ 0`.

**Variance.**  The adjunction runs `T ⊣ Q`, not `Q ⊣ T`.  Under the surplus order,
`T(r)` is the *minimal-rent* mechanism with allocation `r.q` — every other BIC-IR
mechanism in the fiber leaves the lowest type a non-negative rent and therefore sits
*above* `T(r)`.  So `T(r)` is initial in the fiber, not terminal, and `T` is the left
adjoint.  IR is exactly what pins the direction: it is used, essentially, in the counit.

*Reference*: Theorem 4.3; Mac Lane (1978), Chapter IV. -/
-- `Adjunction` is a structure (Type), not a Prop, so we use `def` not `theorem`.
noncomputable def adj_T_Q_impl {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} (θ_min : ℝ)
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D)
    (hD : ∀ θ, θ ∈ D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c)
    (hint : ∀ (r : MonotoneAlloc A) a b,
      IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b)
    -- Only-if envelope condition: every BIC-IR mechanism has the envelope derivative.
    (L : NNReal)
    (hvLip : ∀ (m : ICIRMechanism A v θ_min) (θ' : ℝ),
        LipschitzOnWith L (v (m.mech.q θ')) (Set.Ici θ_min))
    (hW : ∀ (m : ICIRMechanism A v θ_min) (θ : ℝ), θ_min ≤ θ →
        ContinuousWithinAt (fun p : ℝ × ℝ => deriv (v (m.mech.q p.1)) p.2)
            (Set.Ici θ ×ˢ Set.Ici θ) (θ, θ)) :
    T (θ_min := θ_min) hθ_pos hSC hD_Ioi hdiff hintC hint ⊣ Q (θ_min := θ_min) hSC hD :=
  Adjunction.mkOfUnitCounit {
    unit := {
      -- η_r : r ⟶ Q(T(r)); Q(T(r)).q = r.q definitionally.
      app := fun _ => { h := fun _ => le_refl _ }
      naturality := fun _ _ _ => @Subsingleton.elim _ allocHom_subsingleton _ _
    }
    counit := {
      -- ε_m : T(Q(m)) ⟶ m; allocations agree, surpluses ordered by IR.
      app := fun m =>
        { hAlloc := fun _ => le_refl _
          hSurp  := by
            intro θ hθ
            have hθ_pos' : 0 < θ := lt_of_lt_of_le hθ_pos hθ
            -- Unfold the composite `(Q ⋙ T).obj m` to `T(Q(m)) = Tmech ⟨m.q, _⟩`.
            change surplus (Tmech hθ_pos hSC hD_Ioi ⟨m.mech.q, m.hMono⟩ hdiff
                  (hint ⟨m.mech.q, m.hMono⟩) hintC) θ ≤ surplus m θ
            -- V_{T(Q(m))}(θ) is the bare envelope integral.
            rw [surplus_Tmech]
            -- V_m(θ) = V_m(θ_min) + ∫ D, by the envelope theorem.
            have hsplit := surplus_split hθ_pos ⟨m.mech.q, m.hMono⟩ (hint _) hdiff m
              (fun _ => rfl) L (hvLip m) (fun θ' hθ' => hW m θ' hθ') θ hθ
            -- IR: the boundary rent is non-negative.
            have hIR : (0 : ℝ) ≤ surplus m θ_min := m.hIR
            rw [hsplit]
            linarith }
      naturality := fun _ _ _ => @Subsingleton.elim _ mechHom_subsingleton _ _
    }
    left_triangle := by ext; exact @Subsingleton.elim _ mechHom_subsingleton _ _
    right_triangle := by ext; exact @Subsingleton.elim _ allocHom_subsingleton _ _
  }

/-- **Lemma 1.8 (proved)**: `T` preserves all small colimits, being a left adjoint.
(In the previous formulation this was claimed for `Q`; under the surplus order the
variance is `T ⊣ Q`, so it is `T` that preserves colimits and `Q` that preserves
limits — see `Q_preservesLimits`.) -/
noncomputable instance T_preservesColimits {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ}
    (θ_min : ℝ) (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D)
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
    PreservesColimits (T (θ_min := θ_min) hθ_pos hSC hD_Ioi hdiff hintC hint) :=
  (adj_T_Q_impl θ_min hθ_pos hSC hD hD_Ioi hdiff hintC hint L hvLip hW).leftAdjoint_preservesColimits

/-- `Q`, as the **right** adjoint, preserves all small limits. -/
noncomputable instance Q_preservesLimits {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ}
    (θ_min : ℝ) (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D)
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
    PreservesLimits (Q (θ_min := θ_min) hSC hD) :=
  (adj_T_Q_impl θ_min hθ_pos hSC hD hD_Ioi hdiff hintC hint L hvLip hW).rightAdjoint_preservesLimits

/-! ### 4.3 Initiality of T(q) in **Mech_q** (Corollary 4.4) -/

/-- **`T(r)` has the least surplus in its fiber.**  Any BIC-IR mechanism `m` with
allocation `r.q` satisfies `V_{T(r)} ≤ V_m` on `[θ_min, ∞)`: by `surplus_split` the two
surpluses differ exactly by `m`'s boundary rent, and IR says that rent is `≥ 0`.

Economically: `T(r)` is the rent-extracting mechanism.  Categorically: this is the
`hSurp` field of the morphism `T(r) ⟶ m`, i.e. the initiality of `T(r)`. -/
theorem Tmech_surplus_le {A : Type*} [LinearOrder A]
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
        (Set.Ici θ ×ˢ Set.Ici θ) (θ, θ)) :
    ∀ θ : ℝ, θ_min ≤ θ →
      surplus (Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC) θ ≤ surplus m θ := by
  intro θ hθ
  have hθ_pos' : 0 < θ := lt_of_lt_of_le hθ_pos hθ
  rw [surplus_Tmech, surplus_split hθ_pos r hint hdiff m hm L hvLip hW θ hθ]
  have hIR : (0 : ℝ) ≤ surplus m θ_min := m.hIR
  linarith

/-- **Envelope bound (only-if direction)**, in transfer coordinates: any BIC-IR mechanism
with allocation `r.q` has transfers **dominated** by the envelope transfer `t*`.
Immediate from `Tmech_surplus_le`, since the two mechanisms share the allocation and the
`v (q θ) θ` term cancels. -/
theorem envelope_transfer_le {A : Type*} [LinearOrder A]
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
        (Set.Ici θ ×ˢ Set.Ici θ) (θ, θ)) :
    ∀ θ : ℝ, θ_min ≤ θ →
      m.mech.t θ ≤ (Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC).mech.t θ := by
  intro θ hθ
  have h := Tmech_surplus_le hθ_pos hSC hD_Ioi r hdiff hint hintC m hm L hvLip hW θ hθ
  simp only [surplus] at h
  have hq : v (m.mech.q θ) θ = v (r.q θ) θ := by rw [hm θ]
  have hTq : (Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC).mech.q θ = r.q θ := rfl
  rw [hq, hTq] at h
  linarith

/-- **Envelope shift (general form)**: with **no** boundary condition, the transfer of any
BIC-IR mechanism with allocation `r.q` is the envelope transfer shifted down by that
mechanism's boundary rent:

  `m.t θ = t*(θ) - V_m(θ_min)`.

`envelope_transfer_unique` is the `V_m(θ_min) = 0` case; `envelope_transfer_le` is the
`V_m(θ_min) ≥ 0` (IR) case.  This is the sharp statement: the fiber over `r` is a
one-parameter family, indexed by boundary rent. -/
theorem envelope_transfer_shift {A : Type*} [LinearOrder A]
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
        (Set.Ici θ ×ˢ Set.Ici θ) (θ, θ)) :
    ∀ θ, θ_min ≤ θ → m.mech.t θ =
      (Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC).mech.t θ - surplus m θ_min := by
  intro θ hθ
  have h := surplus_split hθ_pos r hint hdiff m hm L hvLip hW θ hθ
  have hT := surplus_Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC θ
  have hTq : (Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC).mech.q θ = r.q θ := rfl
  simp only [surplus] at h hT ⊢
  rw [hm θ] at h
  rw [hTq] at hT
  linarith

/-- **Envelope uniqueness (Revenue Equivalence, pointwise form)**: with `V(θ_min) = 0` the
transfer of any BIC-IR mechanism with allocation `r.q` *is* the envelope transfer `t*`. -/
theorem envelope_transfer_unique {A : Type*} [LinearOrder A]
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
    ∀ θ, θ_min ≤ θ → m.mech.t θ = (Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC).mech.t θ := by
  intro θ hθ
  have h := envelope_transfer_shift hθ_pos hSC hD_Ioi r hdiff hint hintC m hm L hvLip hW θ hθ
  have h0 : surplus m θ_min = 0 := by simp only [surplus]; linarith [hBC]
  rw [h, h0, sub_zero]

/-- **Corollary 4.4 (revised): `T(r)` is INITIAL, not terminal**, in the full subcategory
`MechWithAlloc r`: it has a unique morphism *to* every BIC-IR mechanism with allocation
`r.q`.

The variance flip is forced by IR.  Under the surplus order, `T(r)` is the minimal-rent
mechanism in its fiber (`Tmech_surplus_le`), so the arrows run **out of** `T(r)`, not into
it.  This is consistent with `T` being the *left* adjoint in `adj_T_Q`: left adjoints
send objects to initial objects of the relevant comma categories.

- *Existence*: allocations agree pointwise (`hm`); surpluses are ordered by
  `Tmech_surplus_le`.
- *Uniqueness*: hom-sets in **Mech** are subsingletons.
*Reference*: Corollary 4.4; Mac Lane (1978), Section IV.1. -/
theorem T_initial {A : Type*} [LinearOrder A]
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
        (Set.Ici θ ×ˢ Set.Ici θ) (θ, θ)) :
    Nonempty (Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC ⟶ m) ∧
    ∀ (f g : Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC ⟶ m), f = g := by
  refine ⟨⟨⟨fun θ => le_of_eq (hm θ).symm,
      Tmech_surplus_le hθ_pos hSC hD_Ioi r hdiff hint hintC m hm L hvLip hW⟩⟩, ?_⟩
  intro f g
  exact @Subsingleton.elim _ mechHom_subsingleton _ _

/-! ### 4.4 The Master Theorem (Theorem 4.5) -/

/-- **Theorem 4.5(i) — Existence and Uniqueness**: For any monotone allocation rule `r`
and boundary condition `V(θ_min) = 0`, there exists a **unique** BIC-IR mechanism
with allocation `r.q`.  It is the explicit mechanism `T(r)`.

Uniqueness: terminal objects are unique up to unique isomorphism (Mac Lane, Sec. III.1).
*Reference*: Theorem 4.5(i). -/
theorem masterTheorem_existence_impl {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (r : MonotoneAlloc A)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hint : ∀ a b, IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b)
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c) :
    ∃! (m : ICIRMechanism A v θ_min),
      m ∈ MechWithAlloc r ∧
      ∀ θ, m.mech.t θ = transferFormula v θ_min (typeDerivAlongAlloc v r) r.q θ := by
  refine ⟨Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC, ⟨?_, ?_⟩, ?_⟩
  · intro θ; rfl
  · intro θ; rfl
  · -- Uniqueness: requires the only-if envelope theorem (terminality of Tmech).
    rintro m ⟨hm_alloc, hm_t⟩
    obtain ⟨⟨mq, mt⟩, mIC, mIR⟩ := m
    simp only [MechWithAlloc, Set.mem_setOf_eq] at hm_alloc
    have hq : mq = r.q := funext hm_alloc
    have ht : mt = transferFormula v θ_min (typeDerivAlongAlloc v r) r.q := funext hm_t
    subst hq; subst ht
    simp only [Tmech]

/-- **An isomorphism in Mech forces equal transfers.**

This is the payoff of the surplus order.  A `MechHom` both ways gives `q₁ = q₂` (by
antisymmetry on allocations) *and* `V₁ = V₂` (by antisymmetry on surpluses); since
`t = v (q θ) θ - V θ`, the transfers coincide.  Under the old transfer order this
implication was unavailable, and under an allocation-only order it was false.

So `m₁ ≅ m₂` in **Mech** is *exactly* the statement "same allocation, same transfers" —
the categorical isomorphism now carries the economics. -/
theorem transfer_eq_of_iso {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    {m₁ m₂ : ICIRMechanism A v θ_min} (i : m₁ ≅ m₂) :
    ∀ θ : ℝ, θ_min ≤ θ → m₁.mech.t θ = m₂.mech.t θ := by
  intro θ hθ
  have hq : m₁.mech.q θ = m₂.mech.q θ :=
    le_antisymm (i.hom.hAlloc θ) (i.inv.hAlloc θ)
  have hV : surplus m₁ θ = surplus m₂ θ :=
    le_antisymm (i.hom.hSurp θ hθ) (i.inv.hSurp θ hθ)
  simp only [surplus] at hV
  rw [hq] at hV
  linarith

/-- **Mechanisms with the same allocation and the same boundary rent are isomorphic.**

By `surplus_split` their surpluses differ only through the boundary rent, so equal rent
gives equal surplus on all of `[θ_min, ∞)`; allocations agree by hypothesis.  Both
`MechHom`s are then built from `le_of_eq`, and the round-trips are `Subsingleton.elim`. -/
def mechIso_of_sameAlloc_sameRent {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ} (hθ_pos : 0 < θ_min)
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
    (hV₀ : surplus m₁ θ_min = surplus m₂ θ_min) :
    m₁ ≅ m₂ :=
  have hVeq : ∀ θ : ℝ, θ_min ≤ θ → surplus m₁ θ = surplus m₂ θ := by
    intro θ hθ
    have hθ_pos' : 0 < θ := lt_of_lt_of_le hθ_pos hθ
    rw [surplus_split hθ_pos r hint hdiff m₁ hm₁ L₁ hvLip₁ hW θ hθ,
        surplus_split hθ_pos r hint hdiff m₂ hm₂ L₂ hvLip₂ hW θ hθ, hV₀]
  have hqeq : ∀ θ, m₁.mech.q θ = m₂.mech.q θ := fun θ => by rw [hm₁ θ, hm₂ θ]
  { hom := ⟨fun θ => le_of_eq (hqeq θ), fun θ hθ => le_of_eq (hVeq θ hθ)⟩
    inv := ⟨fun θ => le_of_eq (hqeq θ).symm, fun θ hθ => le_of_eq (hVeq θ hθ).symm⟩
    hom_inv_id := @Subsingleton.elim _ mechHom_subsingleton _ _
    inv_hom_id := @Subsingleton.elim _ mechHom_subsingleton _ _ }

/-- `Nonempty` form of `mechIso_of_sameAlloc_sameRent`. -/
theorem mech_iso_of_sameAlloc_sameRent {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ} (hθ_pos : 0 < θ_min)
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
    (hV₀ : surplus m₁ θ_min = surplus m₂ θ_min) :
    Nonempty (m₁ ≅ m₂) :=
  ⟨mechIso_of_sameAlloc_sameRent hθ_pos r hint hdiff m₁ m₂ hm₁ hm₂ L₁ hvLip₁ L₂ hvLip₂ hW hV₀⟩

/-- **Theorem 4.5(ii) — Isomorphism**: every BIC-IR mechanism with allocation `r.q` and
`V(θ_min) = 0` is isomorphic to `T(r)` in **Mech**.

Under the surplus order this single statement now carries the whole content: by
`transfer_eq_of_iso`, an iso in **Mech** already says the transfers agree.  No second
conjunct is needed.
*Reference*: Theorem 4.5(ii). -/
theorem masterTheorem_isomorphism_impl {A : Type*} [LinearOrder A]
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
    -- Boundary condition V(θ_min) = 0: normalises the surplus at the lowest type.
    (hBC : v (m.mech.q θ_min) θ_min = m.mech.t θ_min) :
    Nonempty (m ≅ Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC) := by
  -- Transfers agree (revenue equivalence); allocations agree (hm); hence surpluses agree.
  have ht := envelope_transfer_unique hθ_pos hSC hD_Ioi r hdiff hint hintC m hm L hvLip hW hBC
  have hqeq : ∀ θ, m.mech.q θ = (Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC).mech.q θ :=
    fun θ => hm θ
  have hVeq : ∀ θ : ℝ, θ_min ≤ θ →
      surplus m θ = surplus (Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC) θ := by
    intro θ hθ
    have hθ_pos' : 0 < θ := lt_of_lt_of_le hθ_pos hθ
    simp only [surplus]
    rw [hqeq θ, ht θ hθ]
  exact ⟨{
    hom := ⟨fun θ => le_of_eq (hqeq θ), fun θ hθ => le_of_eq (hVeq θ hθ)⟩
    inv := ⟨fun θ => le_of_eq (hqeq θ).symm, fun θ hθ => le_of_eq (hVeq θ hθ).symm⟩
    hom_inv_id := @Subsingleton.elim _ mechHom_subsingleton _ _
    inv_hom_id := @Subsingleton.elim _ mechHom_subsingleton _ _ }⟩

/-- **Theorem 4.5(iii) — Transfer Invariance**, via the categorical route.

Any two BIC-IR mechanisms with the same allocation rule and the **same boundary rent**
generate the same expected transfer on `[θ_min, ∞)`.

*Proof*: they are isomorphic in **Mech** (`mech_iso_of_sameAlloc_sameRent`), and an
isomorphism in **Mech** forces equal transfers (`transfer_eq_of_iso`).  The adjunction's
category is doing the work here — this is not a restatement of the analytic argument.

Note the hypothesis is `V₁(θ_min) = V₂(θ_min)`, not `= 0`: revenue equivalence needs
*equal* rent, never *zero* rent.  (This matches `mirrlees_unique_from_IC`, which already
quantified over a common `V₀`.)
*Reference*: Theorem 4.5(iii); Myerson (1981), Theorem 2. -/
theorem masterTheorem_transferInvariance_impl {A : Type*} [LinearOrder A]
   
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
    -- RELAXED: equal boundary rent, not zero boundary rent.
    (hV₀ : surplus m₁ θ_min = surplus m₂ θ_min)
    (μ : MeasureTheory.Measure ℝ) [IsFiniteMeasure μ] :
    ∫ θ in Set.Ici θ_min, m₁.mech.t θ ∂μ = ∫ θ in Set.Ici θ_min, m₂.mech.t θ ∂μ := by
  obtain ⟨i⟩ := mech_iso_of_sameAlloc_sameRent hθ_pos r hint hdiff m₁ m₂ hm₁ hm₂
    L₁ hvLip₁ L₂ hvLip₂ hW hV₀
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ici
    fun θ hθ => transfer_eq_of_iso i θ hθ

/-- **Transfer invariance, routed through `T`** — the categorical derivation.

For *normalised* mechanisms (zero rent), this proves Theorem 4.5(iii) by going through the
transfer functor: each mechanism is isomorphic to `T(r)` (`masterTheorem_isomorphism_impl), so
they are isomorphic to each other, and an isomorphism in **Mech** forces equal transfers
(`transfer_eq_of_iso`).

`masterTheorem_transferInvariance` proves the *more general* equal-rent statement directly,
without `T`.  This variant exists to demonstrate that the categorical route is genuinely
available — `T` and the isomorphism are not decorative — and to give
`masterTheorem_isomorphism_impl a consumer. -/
theorem transferInvariance_via_T {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (r : MonotoneAlloc A)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hint : ∀ a b, IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b)
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c)
    (m₁ m₂ : ICIRMechanism A v θ_min)
    (hm₁ : m₁ ∈ MechWithAlloc r) (hm₂ : m₂ ∈ MechWithAlloc r)
    (L₁ : NNReal)
    (hvLip₁ : ∀ θ' : ℝ, LipschitzOnWith L₁ (v (m₁.mech.q θ')) (Set.Ici θ_min))
    (L₂ : NNReal)
    (hvLip₂ : ∀ θ' : ℝ, LipschitzOnWith L₂ (v (m₂.mech.q θ')) (Set.Ici θ_min))
    (hW : ∀ θ, θ_min ≤ θ →
      ContinuousWithinAt (fun p : ℝ × ℝ => deriv (v (r.q p.1)) p.2)
        (Set.Ici θ ×ˢ Set.Ici θ) (θ, θ))
    -- Both mechanisms are normalised: zero rent at the lowest type.
    (hBC₁ : v (m₁.mech.q θ_min) θ_min = m₁.mech.t θ_min)
    (hBC₂ : v (m₂.mech.q θ_min) θ_min = m₂.mech.t θ_min)
    (μ : MeasureTheory.Measure ℝ) [IsFiniteMeasure μ] :
    ∫ θ in Set.Ici θ_min, m₁.mech.t θ ∂μ = ∫ θ in Set.Ici θ_min, m₂.mech.t θ ∂μ := by
  obtain ⟨i₁⟩ := masterTheorem_isomorphism_impl hθ_pos hSC hD_Ioi r hdiff hint hintC m₁ hm₁
    L₁ hvLip₁ hW hBC₁
  obtain ⟨i₂⟩ := masterTheorem_isomorphism_impl hθ_pos hSC hD_Ioi r hdiff hint hintC m₂ hm₂
    L₂ hvLip₂ hW hBC₂
  -- m₁ ≅ T(r) ≅ m₂
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ici
    fun θ hθ => transfer_eq_of_iso (i₁ ≪≫ i₂.symm) θ hθ

/-! ### 4.6 The normalized subcategory **Mech₀** and the equivalence `Alloc ≃ Mech₀`

The three-move architecture of the Master Theorem:

* **Move 1 (general).**  `T ⊣ Q` on all of **Mech** (`adj_T_Q`).  `T` is fully faithful
  (`T_full`, `T_faithful`), and `T(r)` is *initial* in its fiber (`T_initial`): it is the
  rent-extracting mechanism.  The fiber of `Q` over `r` is a one-parameter family indexed
  by the boundary rent `V(θ_min) ≥ 0` (`surplus_split`).

* **Move 2 (the comonad).**  `T ∘ Q` strips the rent: `surplus (T (Q m)) θ_min = 0`
  (`zeroRent_TQ`).  Its counit `ε_m : T(Q(m)) ⟶ m` is the "remove the lowest type's rent"
  map, and is an isomorphism exactly on the zero-rent objects.

* **Move 3 (normalized).**  On the full subcategory `Mech₀` of zero-rent mechanisms, the
  counit is an isomorphism, so `T ⊣ Q` upgrades to an **adjoint equivalence**
  `Alloc ≌ Mech₀` (`equivAllocMech₀`) — adjoint in *both* directions.  This is the
  Taxation Principle: normalized mechanisms *are* allocations.

Note the division of labour.  The content lives in Move 1 (that `T` exists at all —
`T_wellDefined`) and Move 2 (that the counit is iso precisely at zero rent).  Once those
are in place the equivalence of Move 3 is cheap, as equivalences always are. -/

/-- The **zero-rent** property: the lowest type is left no surplus, `V(θ_min) = 0`.
This is the normalisation the informal statement of `IsIR` always intended (`IsIR` itself
only asserts `V(θ_min) ≥ 0`). -/
def ZeroRent {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ} : ObjectProperty (ICIRMechanism A v θ_min) :=
  fun m => surplus m θ_min = 0

/-- **Mech₀** — the full subcategory of BIC-IR mechanisms that leave the lowest type no
rent.  This is the essential image of `T`. -/
abbrev Mech₀ (A : Type*) [LinearOrder A]
    (v : A → ℝ → ℝ) (θ_min : ℝ) : Type _ :=
  ObjectProperty.FullSubcategory (ZeroRent (A := A) (v := v) (θ_min := θ_min))

/-- `T(r)` has zero rent: at `θ_min` the envelope integral is empty. -/
lemma zeroRent_Tmech {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (r : MonotoneAlloc A)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hint : ∀ a b, IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b)
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c) :
    ZeroRent (Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC) := by
  change surplus (Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC) θ_min = 0
  rw [surplus_Tmech]; simp

/-- **Move 2**: the comonad `T ∘ Q` strips the rent — `T(Q(m))` always has zero rent,
whatever rent `m` had. -/
lemma zeroRent_TQ {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c)
    (hint : ∀ (r : MonotoneAlloc A) a b,
      IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b)
    (hD : ∀ θ, θ ∈ D) (m : ICIRMechanism A v θ_min) :
    ZeroRent ((Q (θ_min := θ_min) hSC hD ⋙ T hθ_pos hSC hD_Ioi hdiff hintC hint).obj m) :=
  zeroRent_Tmech hθ_pos hSC hD_Ioi ⟨m.mech.q, m.hMono⟩ hdiff
    (hint ⟨m.mech.q, m.hMono⟩) hintC

/-- **`T` corestricted to `Mech₀`**: `T₀ : Alloc ⥤ Mech₀`. -/
noncomputable def T₀ {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c)
    (hint : ∀ (r : MonotoneAlloc A) a b,
      IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b) :
    MonotoneAlloc A ⥤ Mech₀ A v θ_min where
  obj r := ⟨Tmech hθ_pos hSC hD_Ioi r hdiff (hint r) hintC,
            zeroRent_Tmech hθ_pos hSC hD_Ioi r hdiff (hint r) hintC⟩
  map f := ObjectProperty.homMk ((T hθ_pos hSC hD_Ioi hdiff hintC hint).map f)
  map_id _ := by ext; apply @Subsingleton.elim _ mechHom_subsingleton
  map_comp _ _ := by ext; apply @Subsingleton.elim _ mechHom_subsingleton

/-- **`Q` restricted to `Mech₀`**: `Q₀ : Mech₀ ⥤ Alloc` (forget the rent condition, then
forget the transfer). -/
noncomputable def Q₀ {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ} {D : Set ℝ} (hSC : SingleCrossing v D) (hD : ∀ θ, θ ∈ D) :
    Mech₀ A v θ_min ⥤ MonotoneAlloc A :=
  (ZeroRent (A := A) (v := v) (θ_min := θ_min)).ι ⋙ Q (θ_min := θ_min) hSC hD

/-- **Move 3 — the Taxation Principle as an equivalence of categories.**

`Alloc ≌ Mech₀`: monotone allocation rules and zero-rent BIC-IR mechanisms are the same
thing, up to natural isomorphism.  Consequently `T₀ ⊣ Q₀` *and* `Q₀ ⊣ T₀` — the two
functors are adjoint in both directions, which is exactly what an adjoint equivalence
gives.

- The unit `𝟭 Alloc ≅ Q₀ ∘ T₀` is the identity: `Q(T(r)).q = r.q` definitionally.
- The counit `T₀ ∘ Q₀ ≅ 𝟭 Mech₀` is where the work is: for a *zero-rent* `m`, stripping
  the rent changes nothing, so `T(Q(m)) ≅ m` by `mechIso_of_sameAlloc_sameRent` (same
  allocation by construction, same rent — both zero, one by `zeroRent_Tmech` and one by
  membership in `Mech₀`).

On all of **Mech** this fails: the counit is only a *morphism* `T(Q(m)) ⟶ m`, and it is
invertible precisely when `m` has zero rent.  That is the content of the normalisation.

*Reference*: Hammond (1979), Theorem 1; Rochet (1985), Proposition 1. -/
noncomputable def equivAllocMech₀ {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
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
    MonotoneAlloc A ≌ Mech₀ A v θ_min where
  functor := T₀ hθ_pos hSC hD_Ioi hdiff hintC hint
  inverse := Q₀ hSC hD
  unitIso := NatIso.ofComponents
    (fun _ => Iso.refl _)
    (fun _ => @Subsingleton.elim _ allocHom_subsingleton _ _)
  counitIso := NatIso.ofComponents
    (fun m => by
      -- Strip-the-rent is the identity on a zero-rent mechanism.
      refine ObjectProperty.isoMk _ (mechIso_of_sameAlloc_sameRent hθ_pos
        ⟨m.obj.mech.q, m.obj.hMono⟩ (hint _) hdiff
        (Tmech hθ_pos hSC hD_Ioi ⟨m.obj.mech.q, m.obj.hMono⟩ hdiff
          (hint _) hintC) m.obj
        (fun _ => rfl) (fun _ => rfl)
        L (hvLip (Tmech hθ_pos hSC hD_Ioi ⟨m.obj.mech.q, m.obj.hMono⟩ hdiff (hint _) hintC))
        L (hvLip m.obj)
        (fun θ hθ => hW m.obj θ hθ) ?_)
      -- both rents are zero: T(Q(m)) by construction, m by membership in Mech₀
      rw [zeroRent_Tmech hθ_pos hSC hD_Ioi ⟨m.obj.mech.q, m.obj.hMono⟩ hdiff (hint _) hintC,
        m.property])
    (fun _ => by ext; apply @Subsingleton.elim _ mechHom_subsingleton)
  functor_unitIso_comp _ := by ext; apply @Subsingleton.elim _ mechHom_subsingleton

end MechDesign
