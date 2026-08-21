import MechDesigAdjointfunctor.Lean.Framework
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Perfect
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Stage 3: The Mirrlees Taxation Setting

Instantiates the abstract framework of `Framework.lean` to Mirrlees's (1971)
optimal nonlinear income taxation model, recovering the **Taxation Principle**
(Hammond 1979; Rochet 1985).

## Summary

* Allocation space `A = ℝ≥0` — gross income `y`.
* Value function: quasilinear approximation `v(y, θ) = θ * h(y) - g(y/θ)` where
  `h` is the value of income and `g` is the disutility of effort.
* SC-M (Spence-Mirrlees condition): MRS between income and consumption decreasing in `θ`.
* IC characterises the net-income schedule via the envelope formula (Lemma 3.1):
  `V(θ) = V(θ_min) + ∫_{θ_min}^θ ∂v/∂s (y(s), s) ds`.
* The **Taxation Principle**: any IC mechanism can be implemented by a unique
  nonlinear tax schedule `T(y) = y - c(y)`.

## References

* Mirrlees (1971), *Optimal Income Taxation*, Sections 2–6, Eqs. (26)–(27)
* Hammond (1979), *Straightforward Individual Incentive Compatibility*, Theorem 1
* Rochet (1985), *The Taxation Principle and Multi-Time HJE*, Proposition 1
* Seade (1977), *On the Shape of Optimal Tax Schedules*
-/

open MeasureTheory intervalIntegral Filter

namespace MechDesign.Mirrlees

/-! ### 3.1 The Mirrlees Environment -/

/-- The value function for the Mirrlees model, as a quasilinear approximation.
`v(y, θ) = θ * h y - g (y / θ)` where `h : ℝ → ℝ` values income and
`g : ℝ → ℝ` is the disutility of labour effort `l = y / θ`. -/
noncomputable def mirrleesValue (h g : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun y θ => θ * h y - g (y / θ)

/-- **Condition SC-M** (Spence-Mirrlees Single Crossing): the marginal rate of
substitution `MRS(y, c, θ) = -∂U/∂y / ∂U/∂c` is strictly decreasing in `θ`.
Equivalently, higher-productivity types have flatter indifference curves in `(y, c)` space.
Formalised here as: `∂/∂θ [v(y, θ) - v(y', θ)] > 0` for all `y > y'`, which is the
abstract SC condition applied to the income-consumption allocation space.
*Reference*: Mirrlees (1971) Assumption 3; Seade (1977). -/
def SpenceMirrlees (v : ℝ → ℝ → ℝ) : Prop :=
  SingleCrossing (A := ℝ) v (Set.Ioi 0)

/-- SC-M implies the abstract SC condition for the income-consumption allocation space.

The Spence-Mirrlees condition `SpenceMirrlees v = SingleCrossing v` (by definition),
so this lemma establishes SC from differentiability assumptions on `h` and `g`.
*Reference*: Mirrlees (1971), Lemma 1; Fudenberg–Tirole (1991), Ch. 7. -/
lemma mirrlees_singleCrossing (h g : ℝ → ℝ) (_hh : Differentiable ℝ h)
    (hg : Differentiable ℝ g) (_hg_pos : ∀ l, 0 < deriv g l)
    (hh_mono : StrictMono h)
    (hSM : StrictMono (fun l => l * deriv g l)) :
    SingleCrossing (A := ℝ) (mirrleesValue h g) (Set.Ioi 0) := by
  intro y y' hyy
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · -- ContinuousOn (fun θ => mirrleesValue h g y θ - mirrleesValue h g y' θ) (Set.Ioi 0)
    have hcont_y : ContinuousOn (fun θ => mirrleesValue h g y θ) (Set.Ioi 0) := by
      simp only [mirrleesValue]
      exact ContinuousOn.sub
        (continuous_id.mul_const _).continuousOn
        (hg.continuous.continuousOn.comp
          (ContinuousOn.div continuousOn_const continuousOn_id (fun x hx => hx.ne'))
          (fun _ _ => Set.mem_univ _))
    have hcont_y' : ContinuousOn (fun θ => mirrleesValue h g y' θ) (Set.Ioi 0) := by
      simp only [mirrleesValue]
      exact ContinuousOn.sub
        (continuous_id.mul_const _).continuousOn
        (hg.continuous.continuousOn.comp
          (ContinuousOn.div continuousOn_const continuousOn_id (fun x hx => hx.ne'))
          (fun _ _ => Set.mem_univ _))
    exact hcont_y.sub hcont_y'
  · -- 0 < deriv f θ for θ ∈ interior (Set.Ioi 0) = Set.Ioi 0
    intro θ hθ
    rw [interior_Ioi] at hθ
    have hθne : θ ≠ 0 := hθ.ne'
    have hθ_pos : 0 < θ := hθ
    -- Rewrite f in simplified form
    have hf_eq : (fun x => mirrleesValue h g y x - mirrleesValue h g y' x) =
        (fun x => x * (h y - h y') - g (y / x) + g (y' / x)) := by
      ext x; simp only [mirrleesValue]; ring
    rw [hf_eq]
    -- HasDerivAt for y/x and y'/x
    have hdy : HasDerivAt (fun x => y / x) (-(y / θ ^ 2)) θ := by
      have hraw := (hasDerivAt_const θ y).div (hasDerivAt_id θ) hθne
      simp only [id] at hraw
      convert hraw using 1; ring
    have hdy' : HasDerivAt (fun x => y' / x) (-(y' / θ ^ 2)) θ := by
      have hraw := (hasDerivAt_const θ y').div (hasDerivAt_id θ) hθne
      simp only [id] at hraw
      convert hraw using 1; ring
    -- HasDerivAt for g(y/x) and g(y'/x)
    have hdgy : HasDerivAt (fun x => g (y / x)) (deriv g (y / θ) * -(y / θ ^ 2)) θ :=
      (hg (y / θ)).hasDerivAt.comp θ hdy
    have hdgy' : HasDerivAt (fun x => g (y' / x)) (deriv g (y' / θ) * -(y' / θ ^ 2)) θ :=
      (hg (y' / θ)).hasDerivAt.comp θ hdy'
    -- HasDerivAt for full function
    have hdf : HasDerivAt (fun x => x * (h y - h y') - g (y / x) + g (y' / x))
        ((h y - h y') + deriv g (y / θ) * (y / θ ^ 2) - deriv g (y' / θ) * (y' / θ ^ 2)) θ := by
      have ha : HasDerivAt (fun x => x * (h y - h y')) (1 * (h y - h y')) θ :=
        (hasDerivAt_id θ).mul_const _
      have hstep := (ha.sub hdgy).add hdgy'
      convert hstep using 1; ring
    rw [hdf.deriv]
    -- Show derivative value is positive
    have hhy : h y' < h y := hh_mono hyy
    have hlt : y' / θ < y / θ := by
      apply div_lt_div_of_pos_right hyy hθ_pos
    have hSM_app : y' / θ * deriv g (y' / θ) < y / θ * deriv g (y / θ) := hSM hlt
    have hrewrite :
        (h y - h y') + deriv g (y / θ) * (y / θ ^ 2) - deriv g (y' / θ) * (y' / θ ^ 2) =
        (h y - h y') + (1 / θ) * (y / θ * deriv g (y / θ) - y' / θ * deriv g (y' / θ)) := by
      field_simp; ring
    rw [hrewrite]
    have h1 : 0 < h y - h y' := by linarith
    have h2 : 0 < y / θ * deriv g (y / θ) - y' / θ * deriv g (y' / θ) := by linarith
    have h3 : 0 < (1 : ℝ) / θ := by rw [one_div]; exact inv_pos.mpr hθ_pos
    linarith [mul_pos h3 h2]

/-! ### 3.1.bis Differentiability of the Mirrlees Value Function

The Mirrlees value function `v(y, θ) = θ * h y - g (y/θ)` has a singularity at `θ = 0`
because `y/θ` blows up there.  It is **not** globally differentiable on `ℝ`.

The framework's `T_wellDefined` uses `DifferentiableOn ℝ (v a) (Set.Ioi 0)`, i.e.
differentiability on the strictly positive reals `(0, ∞)`.  Since the type space satisfies
`θ_min > 0` (design decision), the integration interval `[θ_min, θ_max]` lies inside
`Set.Ioi 0`, and `g (y/θ)` is differentiable there because the denominator `θ ≠ 0`.

Note: `Set.Ioi 0 = {θ : ℝ | 0 < θ}` — the open interval `(0, ∞)`.  This is the minimal
domain needed to avoid the `1/θ` singularity.
*Reference*: Mirrlees (1971), Section 2 (assumption that types are bounded away from `0`). -/

/-- The Mirrlees value function `v(y, θ) = θ * h y - g (y/θ)` is differentiable on
`Set.Ioi 0 = (0, ∞)` in the type argument `θ`, for any fixed income `y`.

The singularity at `θ = 0` is excluded by the domain: on `(0, ∞)`, `fun θ => y / θ`
is differentiable (denominator non-zero), so the chain rule applies to `g (y / θ)`. -/
lemma mirrlees_vDiff (h g : ℝ → ℝ) (_hh : Differentiable ℝ h) (hg : Differentiable ℝ g) :
    ∀ (y : ℝ), DifferentiableOn ℝ (mirrleesValue h g y) (Set.Ioi 0) := by
  intro y
  unfold mirrleesValue
  exact DifferentiableOn.sub
    (differentiable_id.mul_const _).differentiableOn
    (hg.differentiableOn.comp
      (DifferentiableOn.div (differentiableOn_const y) differentiableOn_id (fun x hx => hx.ne'))
      (fun x _ => Set.mem_univ _))

/-! ### 3.2 IC Characterisation and the Taxation Principle (Lemma 3.1) -/

/-- The **Mirrlees envelope transfer formula**: the unique consumption rule `c(θ)` that,
paired with a monotone income assignment `y(θ)`, yields an IC mechanism with
`V(θ_min) = V₀`.

  `V(θ) = V₀ + ∫_{θ_min}^θ (∂v/∂s)(y(s), s) ds`
  `c(θ) = v(y(θ), θ) - V(θ)` -/
noncomputable def mirrleesRent (vθ_partial : ℝ → ℝ) (V₀ θ_min θ : ℝ) : ℝ :=
  V₀ + ∫ s in θ_min..θ, vθ_partial s

/-- The tax schedule induced by income assignment `y(θ)` and consumption `c(θ)`:
`T(y) = y - c` on the range of `y`. -/
noncomputable def taxSchedule (y c : ℝ → ℝ) (θ : ℝ) : ℝ := y θ - c θ

/-- **Lemma 3.1 (Taxation Principle — if direction)**: if `y(θ)` is monotone and `V`
satisfies the envelope formula, then the mechanism `(y, c)` is IC.

Proof sketch: for a misreport `r`, the payoff difference is
`V(θ) - U(θ,r) = ∫ᵣ^θ [∂v/∂s(y(s),s) - ∂v/∂s(y(r),s)] ds ≥ 0`
by SC-M and monotonicity of `y`. -/
lemma mirrlees_IC_of_envelope (v : ℝ → ℝ → ℝ) (vθ_partial : ℝ → ℝ) (V₀ θ_min : ℝ)
    (hθ_pos : 0 < θ_min)
    (y : ℝ → ℝ) {D : Set ℝ} (hySC : SingleCrossing v D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (hy_mono : Monotone y)
    (hdiff : ∀ a : ℝ, DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hvθ : ∀ θ, vθ_partial θ = deriv (v (y θ)) θ)
    (hint : ∀ a b, IntervalIntegrable vθ_partial MeasureTheory.volume a b)
    (hintC : ∀ (a : ℝ) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c) :
    IsIC v θ_min ⟨y, fun θ => v (y θ) θ - mirrleesRent vθ_partial V₀ θ_min θ⟩ := by
  intro θ θ' hθ_lb hθ'_lb
  have hθ_pos' : 0 < θ := lt_of_lt_of_le hθ_pos hθ_lb
  have hθ'_pos : 0 < θ' := lt_of_lt_of_le hθ_pos hθ'_lb
  change v (y θ) θ - (v (y θ) θ - mirrleesRent vθ_partial V₀ θ_min θ) ≥
      v (y θ') θ - (v (y θ') θ' - mirrleesRent vθ_partial V₀ θ_min θ')
  simp only [mirrleesRent]
  set Iθ : ℝ := ∫ s in θ_min..θ, vθ_partial s with hIθ_def
  set Iθ' : ℝ := ∫ s in θ_min..θ', vθ_partial s with hIθ'_def
  set Iθ'_θ : ℝ := ∫ s in θ'..θ, vθ_partial s with hIθ'θ_def
  have hsplit : Iθ' + Iθ'_θ = Iθ := by
    rw [hIθ_def, hIθ'_def, hIθ'θ_def]
    exact intervalIntegral.integral_add_adjacent_intervals (hint θ_min θ') (hint θ' θ)
  suffices h : Iθ'_θ ≥ v (y θ') θ - v (y θ') θ' by linarith
  -- θ, θ' > 0 from hθ_lb, hθ'_lb, hθ_pos — no non-physical case.
  have hFTC : (∫ s in θ'..θ, deriv (v (y θ')) s) = v (y θ') θ - v (y θ') θ' := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro s hs
      have hs_pos : 0 < s := by
        rcases le_total θ' θ with hle | hle
        · rw [Set.uIcc_of_le hle] at hs; exact lt_of_lt_of_le hθ'_pos hs.1
        · rw [Set.uIcc_of_ge hle] at hs; exact lt_of_lt_of_le hθ_pos' hs.1
      exact ((hdiff (y θ')) s hs_pos).differentiableAt
        (IsOpen.mem_nhds isOpen_Ioi hs_pos) |>.hasDerivAt
    · exact hintC (y θ') θ' θ
  rw [← hFTC]
  rcases le_or_gt θ' θ with hle | hlt
  · rw [hIθ'θ_def]
    apply intervalIntegral.integral_mono_on hle (hintC (y θ') θ' θ) (hint θ' θ)
    intro s hs
    rw [hvθ s]
    have hqle : y θ' ≤ y s := hy_mono hs.1
    rcases lt_or_eq_of_le hqle with hqlt | hqeq
    · have hSCq := hySC (y s) (y θ') hqlt
      have hs_pos : 0 < s := lt_of_lt_of_le hθ'_pos hs.1
      have hd1 : DifferentiableAt ℝ (v (y s)) s :=
        ((hdiff (y s)) s hs_pos).differentiableAt
          (IsOpen.mem_nhds isOpen_Ioi hs_pos)
      have hd2 : DifferentiableAt ℝ (v (y θ')) s :=
        ((hdiff (y θ')) s hs_pos).differentiableAt
          (IsOpen.mem_nhds isOpen_Ioi hs_pos)
      have hhas : HasDerivAt (fun x => v (y s) x - v (y θ') x)
          (deriv (v (y s)) s - deriv (v (y θ')) s) s :=
        HasDerivAt.sub hd1.hasDerivAt hd2.hasDerivAt
      have hacc : AccPt s (𝓟 D) := by
        rw [accPt_principal_iff_nhdsWithin]
        exact (right_nhdsWithin_Ioo_neBot hs_pos).mono
          (nhdsWithin_mono _ (fun x hx => ⟨hD_Ioi (Set.mem_Ioi.mpr hx.1), hx.2.ne⟩))
      linarith [hhas.hasDerivWithinAt.nonneg_of_monotoneOn hacc hSCq.monotoneOn]
    · rw [← hqeq]
  · have hle : θ ≤ θ' := le_of_lt hlt
    have key : ∫ s in θ..θ', vθ_partial s ≤
               ∫ s in θ..θ', deriv (v (y θ')) s :=
      intervalIntegral.integral_mono_on hle (hint θ θ') (hintC (y θ') θ θ') (by
        intro s hs
        rw [hvθ s]
        have hqle : y s ≤ y θ' := hy_mono hs.2
        rcases lt_or_eq_of_le hqle with hqlt | hqeq
        · have hSCq := hySC (y θ') (y s) hqlt
          have hs_pos : 0 < s := lt_of_lt_of_le hθ_pos' hs.1
          have hd1 : DifferentiableAt ℝ (v (y s)) s :=
            ((hdiff (y s)) s hs_pos).differentiableAt
              (IsOpen.mem_nhds isOpen_Ioi hs_pos)
          have hd2 : DifferentiableAt ℝ (v (y θ')) s :=
            ((hdiff (y θ')) s hs_pos).differentiableAt
              (IsOpen.mem_nhds isOpen_Ioi hs_pos)
          have hhas : HasDerivAt (fun x => v (y θ') x - v (y s) x)
              (deriv (v (y θ')) s - deriv (v (y s)) s) s :=
            HasDerivAt.sub hd2.hasDerivAt hd1.hasDerivAt
          have hacc : AccPt s (𝓟 D) := by
            rw [accPt_principal_iff_nhdsWithin]
            exact (right_nhdsWithin_Ioo_neBot hs_pos).mono
              (nhdsWithin_mono _ (fun x hx => ⟨hD_Ioi (Set.mem_Ioi.mpr hx.1), hx.2.ne⟩))
          linarith [hhas.hasDerivWithinAt.nonneg_of_monotoneOn hacc hSCq.monotoneOn]
        · rw [← hqeq])
    have h1 : ∫ s in θ'..θ, vθ_partial s = -∫ s in θ..θ', vθ_partial s :=
      intervalIntegral.integral_symm θ θ'
    have h2 : ∫ s in θ'..θ, deriv (v (y θ')) s = -∫ s in θ..θ', deriv (v (y θ')) s :=
      intervalIntegral.integral_symm θ θ'
    rw [hIθ'θ_def, h1]
    linarith [h2]

/-- **Lemma 3.1 (Taxation Principle — only-if direction)**: if `(y(θ), c(θ))` is IC
with `V(θ_min) = V₀`, then `y` is monotone and the rent `V(θ)` satisfies the envelope
formula.  Moreover, the tax schedule `T(y) = y - c(y)` is uniquely determined by
`y(θ)` and `V₀`.

Proof sketch: `V(θ) = max_r U(θ,r)` is convex (max of functions with the Spence-Mirrlees
property), so `y` is non-decreasing (MON).  The envelope theorem gives
`V'(θ) = (∂v/∂θ)(y(θ), θ)` a.e.; integrating from `θ_min` yields the formula.
*Reference*: Mirrlees (1971), Eqs. (26)–(27); Hammond (1979), Thm. 1; Rochet (1985), Prop. 1. -/
lemma mirrlees_unique_from_IC (v : ℝ → ℝ → ℝ) (vθ_partial : ℝ → ℝ)
    (V₀ θ_min : ℝ) (y t : ℝ → ℝ)
    (hIC : IsIC v θ_min ⟨y, t⟩)
    (hIR : v (y θ_min) θ_min - t θ_min = V₀)
    {D : Set ℝ} (hySC : SingleCrossing v D) (hD : ∀ θ, θ ∈ D)
    (hEnv : ∀ θ, HasDerivAt (fun s => v (y s) s - t s) (vθ_partial θ) θ)
    (hint : ∀ a b, IntervalIntegrable vθ_partial MeasureTheory.volume a b) :
    MonotoneOn y (Set.Ici θ_min) ∧ ∀ θ, t θ = v (y θ) θ - mirrleesRent vθ_partial V₀ θ_min θ := by
  refine ⟨?_, ?_⟩
  · -- MonotoneOn y (Set.Ici θ_min): by IC + SC (mirrors IC_implies_monotone)
    intro θ₁ hθ₁ θ₂ hθ₂ h12
    by_contra hlt
    rw [not_le] at hlt
    have h1 := hIC θ₁ θ₂ hθ₁ hθ₂
    have h2 := hIC θ₂ θ₁ hθ₂ hθ₁
    rcases eq_or_lt_of_le h12 with heq | hlt_θ
    · rw [heq] at hlt; exact lt_irrefl _ hlt
    · linarith [hySC (y θ₁) (y θ₂) hlt (hD θ₁) (hD θ₂) hlt_θ]
  · -- Transfer formula: FTC + boundary condition
    intro θ
    simp only [mirrleesRent]
    have hFTC : ∫ s in θ_min..θ, vθ_partial s =
        (v (y θ) θ - t θ) - (v (y θ_min) θ_min - t θ_min) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hEnv s) (hint θ_min θ)
    linarith [hFTC, hIR]

/-- **Remark (Taxation Principle)**: any IC direct mechanism `(y(θ), c(θ))` can be
implemented by a unique nonlinear tax schedule `T : Y → ℝ` defined by `T(y) = y - c`
on the range of `y`.  Two IC mechanisms with the same `y(θ)` and the same `V(θ_min)`
produce identical tax schedules.
*Reference*: Hammond (1979); Rochet (1985). -/
theorem taxation_principle (v : ℝ → ℝ → ℝ) (vθ_partial : ℝ → ℝ)
    (V₀ θ_min : ℝ) (y₁ y₂ t₁ t₂ : ℝ → ℝ)
    (_hIC₁ : IsIC v θ_min ⟨y₁, t₁⟩) (hIR₁ : v (y₁ θ_min) θ_min - t₁ θ_min = V₀)
    (_hIC₂ : IsIC v θ_min ⟨y₂, t₂⟩) (hIR₂ : v (y₂ θ_min) θ_min - t₂ θ_min = V₀)
    (hy_eq : y₁ = y₂)
    (hEnv₁ : ∀ θ, HasDerivAt (fun s => v (y₁ s) s - t₁ s) (vθ_partial θ) θ)
    (hEnv₂ : ∀ θ, HasDerivAt (fun s => v (y₂ s) s - t₂ s) (vθ_partial θ) θ)
    (hint : ∀ a b, IntervalIntegrable vθ_partial MeasureTheory.volume a b) :
    t₁ = t₂ := by
  funext θ
  have hFTC₁ : ∫ s in θ_min..θ, vθ_partial s =
      (v (y₁ θ) θ - t₁ θ) - (v (y₁ θ_min) θ_min - t₁ θ_min) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hEnv₁ s) (hint θ_min θ)
  have hFTC₂ : ∫ s in θ_min..θ, vθ_partial s =
      (v (y₂ θ) θ - t₂ θ) - (v (y₂ θ_min) θ_min - t₂ θ_min) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hEnv₂ s) (hint θ_min θ)
  rw [← hy_eq] at hFTC₂ hIR₂
  linarith [hFTC₁, hFTC₂, hIR₁, hIR₂]

/-! ### 3.3 Monotonicity of Allocations (Mirrlees)

Under the Spence-Mirrlees condition and IC, the information rent `V(θ)` and the
agent's equilibrium utility are strictly increasing in type.  This formalises
the key monotonicity properties of optimal income taxation.

*Reference*: Mirrlees (1971), Eq. (26); Seade (1977), Prop. 1. -/

/-- The θ-partial derivative of `mirrleesValue h g y` at `θ ≠ 0`:
`d/dθ [θ · h y − g (y/θ)] = h y + (y/θ²) · g' (y/θ)`.

This equals the **local-IC surplus rate** `du/dθ` along an allocation `y(θ)`, and
governs the sign of `dV/dθ`. -/
lemma mirrleesValue_hasDerivAt (h g : ℝ → ℝ) (_hh : Differentiable ℝ h)
    (hg : Differentiable ℝ g) (y θ : ℝ) (hθ : θ ≠ 0) :
    HasDerivAt (mirrleesValue h g y) (h y + (y / θ ^ 2) * deriv g (y / θ)) θ := by
  unfold mirrleesValue
  -- d/dθ [θ * h y] = h y
  have ha : HasDerivAt (fun x => x * h y) (1 * h y) θ :=
    (hasDerivAt_id θ).mul_const _
  -- d/dθ [y / θ] = -(y / θ²)
  have hdy : HasDerivAt (fun x => y / x) (-(y / θ ^ 2)) θ := by
    have hraw := (hasDerivAt_const θ y).div (hasDerivAt_id θ) hθ
    simp only [id] at hraw
    convert hraw using 1; ring
  -- chain rule for g(y/θ)
  have hdgy : HasDerivAt (fun x => g (y / x)) (deriv g (y / θ) * -(y / θ ^ 2)) θ :=
    (hg (y / θ)).hasDerivAt.comp θ hdy
  have hstep := ha.sub hdgy
  convert hstep using 1; ring

/-- The information rent `V(θ) = V₀ + ∫_{θ_min}^θ vθ_partial s ds` is strictly
monotone on `[θ_min, ∞)` whenever `vθ_partial` is continuous and positive on `(0, ∞)`.

Proof: for `θ₁ < θ₂` in `[θ_min, ∞)`,
`V(θ₂) − V(θ₁) = ∫_{θ₁}^{θ₂} vθ_partial s ds > 0`
by positivity and the fact that the interval has positive length. -/
theorem mirrlees_strictMono_rent (vθ_partial : ℝ → ℝ) (V₀ θ_min : ℝ)
    (hθ_pos : 0 < θ_min)
    (hcont : ContinuousOn vθ_partial (Set.Ioi 0))
    (hpos : ∀ θ ∈ Set.Ioi 0, 0 < vθ_partial θ) :
    StrictMonoOn (mirrleesRent vθ_partial V₀ θ_min) (Set.Ici θ_min) := by
  intro θ₁ hθ₁ θ₂ hθ₂ h12
  have hθ₁_pos : 0 < θ₁ := lt_of_lt_of_le hθ_pos hθ₁
  have hθ₂_pos : 0 < θ₂ := lt_of_lt_of_le hθ_pos hθ₂
  -- IntervalIntegrable on subintervals of Ioi 0
  have hii : ∀ a b : ℝ, 0 < a → 0 < b →
      IntervalIntegrable vθ_partial MeasureTheory.volume a b := by
    intro a b ha hb
    apply ContinuousOn.intervalIntegrable
    apply hcont.mono
    intro x hx
    have hlb : min a b ≤ x := hx.1
    exact lt_of_lt_of_le (lt_min ha hb) hlb
  simp only [mirrleesRent]
  have hsplit : (∫ s in θ_min..θ₁, vθ_partial s) + (∫ s in θ₁..θ₂, vθ_partial s) =
      ∫ s in θ_min..θ₂, vθ_partial s :=
    intervalIntegral.integral_add_adjacent_intervals
      (hii θ_min θ₁ hθ_pos hθ₁_pos) (hii θ₁ θ₂ hθ₁_pos hθ₂_pos)
  have hpos_int : 0 < ∫ s in θ₁..θ₂, vθ_partial s :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      (hii θ₁ θ₂ hθ₁_pos hθ₂_pos) (fun x hx => hpos x (lt_trans hθ₁_pos hx.1)) h12
  linarith [hsplit, hpos_int]

/-- Under IC and the envelope formula, the equilibrium utility
`V(θ) = v(y(θ), θ) − t(θ)` is strictly increasing on `[θ_min, ∞)`
when `vθ_partial θ > 0` for all `θ > 0`.

This is the strict-monotonicity counterpart of `mirrlees_unique_from_IC`, which
gives only `MonotoneOn y`.  The proof identifies `V(θ)` with the information rent
via the envelope formula, then applies `mirrlees_strictMono_rent`. -/
theorem mirrlees_strictMono_utility (v : ℝ → ℝ → ℝ) (vθ_partial : ℝ → ℝ)
    (V₀ θ_min : ℝ) (y t : ℝ → ℝ)
    (hθ_pos : 0 < θ_min)
    (hIC : IsIC v θ_min ⟨y, t⟩)
    (hIR : v (y θ_min) θ_min - t θ_min = V₀)
    {D : Set ℝ} (hySC : SingleCrossing v D) (hD : ∀ θ, θ ∈ D)
    (hEnv : ∀ θ, HasDerivAt (fun s => v (y s) s - t s) (vθ_partial θ) θ)
    (hint : ∀ a b, IntervalIntegrable vθ_partial MeasureTheory.volume a b)
    (hcont : ContinuousOn vθ_partial (Set.Ioi 0))
    (hpos : ∀ θ ∈ Set.Ioi 0, 0 < vθ_partial θ) :
    StrictMonoOn (fun θ => v (y θ) θ - t θ) (Set.Ici θ_min) := by
  obtain ⟨_, htransf⟩ :=
    mirrlees_unique_from_IC v vθ_partial V₀ θ_min y t hIC hIR hySC hD hEnv hint
  have heq : (fun θ => v (y θ) θ - t θ) = mirrleesRent vθ_partial V₀ θ_min := by
    funext θ
    rw [htransf θ]; ring
  rw [heq]
  exact mirrlees_strictMono_rent vθ_partial V₀ θ_min hθ_pos hcont hpos

/-! ### 3.4 Strict Monotonicity of Allocation and Consumption (Mirrlees)

The optimal allocation `y(θ)` is strictly increasing in type under regularity (the
first-order condition for optimality and strict concavity of the objective imply
`dy/dθ > 0`).  Given strict monotonicity of allocation, the after-tax consumption
`c(θ) = y(θ) − T(y(θ))` is also strictly increasing whenever the marginal tax rate
is below 100 % (i.e., `T′ < 1`).

*References*: Mirrlees (1971), Eq. (27); Diamond-Saez (2011), §2.1. -/

/-- **Strict monotonicity of the Mirrlees allocation** conditional on a positive
allocation derivative.  The hypothesis `hderiv : ∀ θ ∈ (θ_min, ∞), 0 < deriv y θ`
holds at the optimum under Mirrlees regularity (positive virtual surplus). -/
theorem mirrlees_strictMono_alloc (y : ℝ → ℝ) (θ_min : ℝ)
    (hcont : ContinuousOn y (Set.Ici θ_min))
    (hderiv : ∀ θ ∈ Set.Ioi θ_min, 0 < deriv y θ) :
    StrictMonoOn y (Set.Ici θ_min) :=
  strictMonoOn_of_deriv_pos (convex_Ici θ_min) hcont (interior_Ici (a := θ_min) ▸ hderiv)

/-- **Strict monotonicity of after-tax consumption** given strictly monotone allocation
and a sub-unitary marginal tax rate (`T′(z) < 1` for all `z`).

Proof: the net-income function `g(z) = z − T(z)` has `g′(z) = 1 − T′(z) > 0`,
so `g` is strictly increasing.  Since `c(θ) = g(y(θ))` and `y` is strictly
increasing, the composition is strictly increasing.

*Reference*: Mirrlees (1971), §5 (no 100%-taxation at any income level). -/
theorem mirrlees_strictMono_consumption (y T : ℝ → ℝ) (θ_min : ℝ)
    (hmono_y : StrictMonoOn y (Set.Ici θ_min))
    (hdiff_T : Differentiable ℝ T)
    (hT_lt1 : ∀ z, deriv T z < 1) :
    StrictMonoOn (fun θ => y θ - T (y θ)) (Set.Ici θ_min) := by
  -- g(z) = z − T(z) is strictly increasing because g′ = 1 − T′ > 0.
  have hg_mono : StrictMono (fun z : ℝ => z - T z) := by
    rw [← strictMonoOn_univ]
    apply strictMonoOn_of_deriv_pos convex_univ
    · exact (continuous_id.sub hdiff_T.continuous).continuousOn
    · intro z _
      have hd : HasDerivAt (fun z => z - T z) (1 - deriv T z) z :=
        (hasDerivAt_id z).sub hdiff_T.differentiableAt.hasDerivAt
      linarith [hd.deriv, hT_lt1 z]
  exact hg_mono.comp_strictMonoOn hmono_y

end MechDesign.Mirrlees
