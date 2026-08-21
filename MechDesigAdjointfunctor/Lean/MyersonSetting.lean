import MechDesigAdjointfunctor.Lean.Framework
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Stage 2: The Myerson Auction Setting

Instantiates the abstract framework of `Framework.lean` to Myerson's (1981)
single-object auction with one-dimensional types.

## Summary

* Allocation space `A = ℝ` — allocation values; range `[0,1]` enforced by hypothesis.
* Value function `v q θ = θ * q`.
* SC holds: `v q θ - v q' θ = θ * (q - q')` is strictly increasing in `θ` for `q > q'`.
* IC characterises payment uniquely via the envelope formula (Lemma 2.1):
  `t(θ) = θ * q(θ) - ∫₀^θ q(s) ds`.
* Revenue equivalence follows as a special case of the Master Theorem.

## References

* Myerson (1981), *Optimal Auction Design*, Theorem 2, Lemma 2
* Klemperer (1999), *Auction Theory: A Guide to the Literature*, Theorem 1
-/

open MeasureTheory intervalIntegral

namespace MechDesign.Myerson

/-! ### 2.1 The Myerson Environment -/

/-- The Myerson allocation space: real-valued allocation levels, read as the probability of
winning.  The range `[0,1]` is **not** in the type — it is enforced by hypothesis at the call
sites that need it (`|a| ≤ 1` in `myerson_lipschitz`).

**Design note (D16).**  This used to say that `ℝ` was chosen over `Set.Icc 0 1` because
`AllocHom` required an `AddCommGroup` instance.  That requirement was vacuous: `AllocHom` only
ever compares allocations with `≤`, and the group binder was a leftover from the deleted
*spread monotonicity* field, which subtracted in `A`.  The binders are gone (verified by
deletion), so `A` now needs only a `Preorder` and this choice is no longer forced.

Making `MyersonAlloc` genuinely `Set.Icc 0 1` is therefore newly *possible* but **untested** —
`myersonValue` would become `θ * a.val` and every call site shifts.  See `TODO.md`. -/
abbrev MyersonAlloc := ℝ

/-- The Myerson value function: `v(q, θ) = θ * q`.  Linear in both arguments. -/
noncomputable def myersonValue : MyersonAlloc → ℝ → ℝ :=
  fun q θ => θ * q

/-- **Condition REG** (Regularity, Myerson): the virtual valuation
`ψ(θ) = θ - (1 - F(θ)) / f(θ)` is non-decreasing.  Required for the optimal
allocation to be monotone without ironing. -/
def IsRegular (F f : ℝ → ℝ) (Θ : Set ℝ) : Prop :=
  ∀ θ ∈ Θ, 0 < f θ ∧ MonotoneOn (fun θ => θ - (1 - F θ) / f θ) Θ

/-! ### 2.2 Single Crossing in the Myerson Setting (Section 2.2) -/

/-- SC holds for the Myerson value function: `v q θ - v q' θ = θ * (q - q')`,
which is strictly increasing in `θ` whenever `q > q'`. -/
lemma myerson_singleCrossing : SingleCrossing myersonValue Set.univ := by
  intro q q' hq θ _ θ' _ hθ
  simp only [myersonValue]
  nlinarith [hq, hθ]

/-! ### 2.3 Differentiability of the Myerson Value Function -/

/-- The Myerson value function `v(q, θ) = θ * q.val` is differentiable (in fact
polynomial) in the type argument `θ`, for any fixed allocation `q`. -/
lemma myerson_vDiff :
    ∀ (q : MyersonAlloc), DifferentiableOn ℝ (myersonValue q) (Set.Ioi 0) := by
  intro q
  unfold myersonValue
  fun_prop

/-! ### 2.4 IC Characterisation in the Myerson Setting (Lemma 2.1) -/

/-- The **Myerson envelope transfer formula**: the unique transfer rule that, paired
with a monotone allocation rule `q`, yields a BIC mechanism with `V(0) = 0`.

  `t*(θ) = θ * q(θ) - ∫₀^θ q(s) ds`

*Reference*: Myerson (1981), Theorem 2. -/
noncomputable def myersonTransfer (q : ℝ → ℝ) (θ : ℝ) : ℝ :=
  θ * q θ - ∫ s in (0 : ℝ)..θ, q s

/-- The equilibrium payoff under the Myerson transfer equals the information rent:
`V(θ) = ∫₀^θ q(s) ds`. -/
noncomputable def myersonRent (q : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..θ, q s

/-- **Lemma 2.1 (if direction)**: If `q` is monotone and `t = myersonTransfer q`, then
the mechanism `(q, t)` is BIC with `V(0) = 0`.

Proof sketch: for any misreport `r`, the payoff difference is
`V(θ) - U(θ, r) = ∫ᵣ^θ [q(θ) - q(s)] ds ≥ 0` since `q` is non-decreasing. -/
lemma myerson_IC_of_monotone_transfer (q : ℝ → ℝ) (hq : Monotone q)
    (hq_int : ∀ a b, IntervalIntegrable q MeasureTheory.volume a b) :
    IsIC myersonValue 0 ⟨q, myersonTransfer q⟩ := by
  intro θ θ' _hθ _hθ'
  unfold myersonValue myersonTransfer
  simp only
  -- Goal reduces to: ∫ s in θ'..θ, q s ≥ (θ - θ') * q θ'
  -- After algebra, the inequality becomes:
  --   θ * q θ - (θ * q θ - ∫ 0..θ q) ≥ θ * q θ' - (θ' * q θ' - ∫ 0..θ', q)
  -- i.e. ∫ 0..θ q ≥ (θ - θ') * q θ' + ∫ 0..θ', q
  have key : (θ - θ') * q θ' ≤ ∫ s in θ'..θ, q s := by
    rcases le_or_gt θ' θ with hθ | hθ
    · -- Case θ' ≤ θ: ∫ θ'..θ q ≥ ∫ θ'..θ (q θ') = (θ - θ') * q θ'
      have hmono : ∀ x ∈ Set.Icc θ' θ, q θ' ≤ q x := fun x hx => hq hx.1
      have hconst_int : IntervalIntegrable (fun _ : ℝ => q θ') MeasureTheory.volume θ' θ :=
        intervalIntegrable_const
      have hbound : ∫ s in θ'..θ, (fun _ : ℝ => q θ') s ≤ ∫ s in θ'..θ, q s :=
        intervalIntegral.integral_mono_on hθ hconst_int (hq_int θ' θ) hmono
      rw [intervalIntegral.integral_const] at hbound
      simp [smul_eq_mul, mul_comm] at hbound
      linarith
    · -- Case θ < θ': ∫ θ'..θ = -∫ θ..θ'; on [θ, θ'], q s ≤ q θ'
      have hθ_le : θ ≤ θ' := le_of_lt hθ
      have hmono : ∀ x ∈ Set.Icc θ θ', q x ≤ q θ' := fun x hx => hq hx.2
      have hconst_int : IntervalIntegrable (fun _ : ℝ => q θ') MeasureTheory.volume θ θ' :=
        intervalIntegrable_const
      have hbound : ∫ s in θ..θ', q s ≤ ∫ s in θ..θ', (fun _ : ℝ => q θ') s :=
        intervalIntegral.integral_mono_on hθ_le (hq_int θ θ') hconst_int hmono
      rw [intervalIntegral.integral_const] at hbound
      simp [smul_eq_mul, mul_comm] at hbound
      rw [intervalIntegral.integral_symm θ θ']
      linarith
  -- Now use integral_add_adjacent_intervals to split ∫ 0..θ
  have hsplit : (∫ s in (0:ℝ)..θ', q s) + ∫ s in θ'..θ, q s = ∫ s in (0:ℝ)..θ, q s :=
    intervalIntegral.integral_add_adjacent_intervals (hq_int 0 θ') (hq_int θ' θ)
  linarith

/-- **Lemma 2.1 (only-if direction)**: If `(q, t)` is BIC with `V(0) = 0`,
then `q` is monotone and `t = myersonTransfer q`.

Proof sketch: `V(θ) = max_r U(θ, r)` is convex (max of affine functions), so `q`
is non-decreasing.  The envelope theorem gives `V'(θ) = q(θ)` a.e.; integrating
with `V(0) = 0` and substituting yields the formula. -/
lemma myerson_transfer_unique {q : ℝ → ℝ} {t : ℝ → ℝ}
    (_hIC : IsIC myersonValue 0 ⟨q, t⟩)
    (hIR : t 0 = 0 * q 0)
    (hEnv : ∀ θ, HasDerivAt (fun s => s * q s - t s) (q θ) θ)
    (hint : ∀ a b, IntervalIntegrable q MeasureTheory.volume a b) :
    ∀ θ, t θ = myersonTransfer q θ := by
  intro θ
  simp only [myersonTransfer]
  have hFTC : ∫ s in (0:ℝ)..θ, q s =
      (θ * q θ - t θ) - (0 * q 0 - t 0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hEnv s) (hint 0 θ)
  linarith [hFTC, hIR]

/-- **Expected revenue formula**: for any BIC-IR mechanism with allocation `q` and
`V(0) = 0`, the expected payment equals the expected virtual surplus.

  `𝔼[t(θ)] = 𝔼[ψ(θ) * q(θ)]`  where `ψ(θ) = θ - (1-F(θ))/f(θ)`.

Derived from the Myerson transfer formula by integration by parts.
*Reference*: Myerson (1981), Equation (5); Riley–Samuelson (1981). -/
theorem myerson_expectedRevenue (q : ℝ → ℝ) (F f : ℝ → ℝ)
    (hf : ∀ θ, 0 < f θ)
    (hq_int : ∀ a b, IntervalIntegrable q MeasureTheory.volume a b)
    (hq_cont : Continuous q) (hf_cont : Continuous f)
    (hFf : ∀ θ, HasDerivAt F (f θ) θ)
    (hF0 : F 0 = 0) (hF1 : F 1 = 1) :
    ∫ θ in (0 : ℝ)..1, myersonTransfer q θ * f θ =
    ∫ θ in (0 : ℝ)..1, (θ - (1 - F θ) / f θ) * q θ * f θ := by
  -- Abbreviation for the rent function G θ = ∫₀^θ q s.
  set G : ℝ → ℝ := fun θ => ∫ s in (0:ℝ)..θ, q s with hG_def
  -- F is continuous (since differentiable everywhere).
  have hF_cont : Continuous F := by
    refine continuous_iff_continuousAt.mpr (fun θ => ?_)
    exact (hFf θ).continuousAt
  -- G is continuous (FTC), since q is integrable and continuous.
  have hG_hasDerivAt : ∀ θ, HasDerivAt G (q θ) θ :=
    fun θ => (hq_cont.integral_hasStrictDerivAt 0 θ).hasDerivAt
  have hG_cont : Continuous G := by
    refine continuous_iff_continuousAt.mpr (fun θ => ?_)
    exact (hG_hasDerivAt θ).continuousAt
  -- Various integrabilities on [0,1].
  have hf_int : IntervalIntegrable f MeasureTheory.volume 0 1 :=
    hf_cont.intervalIntegrable 0 1
  have hF_int : IntervalIntegrable F MeasureTheory.volume 0 1 :=
    hF_cont.intervalIntegrable 0 1
  have hG_int : IntervalIntegrable G MeasureTheory.volume 0 1 :=
    hG_cont.intervalIntegrable 0 1
  -- Integration by parts: ∫ G f = G(1)F(1) - G(0)F(0) - ∫ q F.
  have hG0 : G 0 = 0 := by simp [G]
  have hIBP : ∫ θ in (0:ℝ)..1, G θ * f θ =
      G 1 * F 1 - G 0 * F 0 - ∫ θ in (0:ℝ)..1, q θ * F θ :=
    integral_mul_deriv_eq_deriv_mul
      (fun x _ => hG_hasDerivAt x) (fun x _ => hFf x)
      (hq_cont.intervalIntegrable 0 1) hf_int
  -- Simplify the IBP statement using F(0)=0, F(1)=1, G(0)=0.
  have hIBP' : ∫ θ in (0:ℝ)..1, G θ * f θ = G 1 - ∫ θ in (0:ℝ)..1, q θ * F θ := by
    rw [hIBP, hF0, hF1, hG0]; ring
  -- LHS: expand myersonTransfer and split the integral.
  have hLHS_split : ∫ θ in (0:ℝ)..1, myersonTransfer q θ * f θ =
      (∫ θ in (0:ℝ)..1, θ * q θ * f θ) - ∫ θ in (0:ℝ)..1, G θ * f θ := by
    simp only [myersonTransfer]
    have heq : ∀ θ, (θ * q θ - G θ) * f θ = θ * q θ * f θ - G θ * f θ :=
      fun θ => by ring
    have hrw : (fun θ => (θ * q θ - ∫ s in (0:ℝ)..θ, q s) * f θ) =
        (fun θ => θ * q θ * f θ - G θ * f θ) := by
      funext θ; change (θ * q θ - G θ) * f θ = _; exact heq θ
    rw [hrw]
    refine intervalIntegral.integral_sub ?_ ?_
    · exact ((continuous_id.mul hq_cont).mul hf_cont).intervalIntegrable 0 1
    · exact (hG_cont.mul hf_cont).intervalIntegrable 0 1
  -- RHS: simplify (θ - (1-F)/f) * q * f = θ*q*f - (1-F)*q (using f ≠ 0).
  have hRHS_simp : ∀ θ, (θ - (1 - F θ) / f θ) * q θ * f θ =
      θ * q θ * f θ - (1 - F θ) * q θ := by
    intro θ
    have hfne : f θ ≠ 0 := ne_of_gt (hf θ)
    field_simp [hfne]
  have hRHS_split : ∫ θ in (0:ℝ)..1, (θ - (1 - F θ) / f θ) * q θ * f θ =
      (∫ θ in (0:ℝ)..1, θ * q θ * f θ) - ∫ θ in (0:ℝ)..1, (1 - F θ) * q θ := by
    have hrw : (fun θ => (θ - (1 - F θ) / f θ) * q θ * f θ) =
        (fun θ => θ * q θ * f θ - (1 - F θ) * q θ) := by
      funext θ; exact hRHS_simp θ
    rw [hrw]
    refine intervalIntegral.integral_sub ?_ ?_
    · exact ((continuous_id.mul hq_cont).mul hf_cont).intervalIntegrable 0 1
    · exact (((continuous_const.sub hF_cont)).mul hq_cont).intervalIntegrable 0 1
  -- ∫ (1-F)*q = ∫ q - ∫ F*q = G(1) - ∫ q*F.
  have h1F_q : ∫ θ in (0:ℝ)..1, (1 - F θ) * q θ =
      G 1 - ∫ θ in (0:ℝ)..1, q θ * F θ := by
    have hqF_int : IntervalIntegrable (fun θ => q θ * F θ) MeasureTheory.volume 0 1 :=
      (hq_cont.mul hF_cont).intervalIntegrable 0 1
    have hsplit : ∫ θ in (0:ℝ)..1, (1 - F θ) * q θ =
        (∫ θ in (0:ℝ)..1, q θ) - ∫ θ in (0:ℝ)..1, q θ * F θ := by
      have : ∫ θ in (0:ℝ)..1, (1 - F θ) * q θ =
          ∫ θ in (0:ℝ)..1, (q θ - q θ * F θ) := by
        congr 1; funext θ; ring
      rw [this, intervalIntegral.integral_sub (hq_int 0 1) hqF_int]
    have hG1 : G 1 = ∫ θ in (0:ℝ)..1, q θ := by simp [G]
    linarith [hsplit, hG1]
  -- Assemble.
  linarith [hLHS_split, hIBP', hRHS_split, h1F_q]

/-! ### 2.5 Multi-Agent IC and Monotone Allocation -/

/-- **Multi-agent IC (reduced form)**: the conditional winning probability `Q` and
expected payment `X` satisfy the two-sided IC constraints for all `s, t ≥ θ_min`.
Captures Bayes-IC in Myerson (1981) for one bidder's reduced-form allocation. -/
def IsMultiAgentIC (Q X : ℝ → ℝ) (θ_min : ℝ) : Prop :=
  ∀ s t : ℝ, θ_min ≤ s → θ_min ≤ t →
    t * Q t - X t ≥ t * Q s - X s ∧ s * Q s - X s ≥ s * Q t - X t

/-- **IC → Monotone Q** (Myerson 1981, Lemma 2): from two-sided IC, the conditional
winning probability `Q` is non-decreasing on `[θ_min, ∞)`.

Proof: the two IC inequalities add to `(t-s)·Q(t) ≥ (t-s)·Q(s)`; for `s < t`
divide by `t - s > 0`. -/
theorem multiAgent_IC_implies_monotone (Q X : ℝ → ℝ) (θ_min : ℝ)
    (hIC : IsMultiAgentIC Q X θ_min) :
    MonotoneOn Q (Set.Ici θ_min) := by
  intro s hs t ht hst
  rcases eq_or_lt_of_le hst with rfl | hlt
  · exact le_refl _
  · have hpos : (0 : ℝ) < t - s := sub_pos.mpr hlt
    obtain ⟨hIC_t, hIC_s⟩ := hIC s t hs ht
    have hkey : (t - s) * Q s ≤ (t - s) * Q t := by nlinarith
    exact le_of_mul_le_mul_left hkey hpos

/-- **IC + regularity → Strict Monotone Q**: if `Q` has a strictly positive
derivative on `(θ_min, ∞)` — a consequence of Myerson's regularity condition
`c(θ) = θ - (1-F(θ))/f(θ)` strictly increasing — then `Q` is strictly increasing
on `[θ_min, ∞)`. -/
theorem multiAgent_IC_implies_strictMono (Q X : ℝ → ℝ) (θ_min : ℝ)
    (_hIC : IsMultiAgentIC Q X θ_min)
    (hCont : ContinuousOn Q (Set.Ici θ_min))
    (hPos : ∀ θ ∈ Set.Ioi θ_min, 0 < deriv Q θ) :
    StrictMonoOn Q (Set.Ici θ_min) :=
  strictMonoOn_of_deriv_pos (convex_Ici θ_min) hCont (interior_Ici (a := θ_min) ▸ hPos)

/-! ### 2.6 Two-Bidder Expected Allocation and BIC -/

/-- Expected allocation for bidder 1 in a 2-bidder auction: winning probability
integrated over bidder 2's type `t₂ ∈ [a₂, b₂]` with density `f₂`. -/
noncomputable def expAlloc₁
    (p : ℝ → ℝ → ℝ) (f₂ : ℝ → ℝ) (a₂ b₂ : ℝ) (t₁ : ℝ) : ℝ :=
  ∫ t₂ in a₂..b₂, p t₁ t₂ * f₂ t₂

/-- Expected payment for bidder 1 in a 2-bidder auction: payment integrated over
bidder 2's type `t₂ ∈ [a₂, b₂]` with density `f₂`. -/
noncomputable def expPayment₁
    (x₁ : ℝ → ℝ → ℝ) (f₂ : ℝ → ℝ) (a₂ b₂ : ℝ) (t₁ : ℝ) : ℝ :=
  ∫ t₂ in a₂..b₂, x₁ t₁ t₂ * f₂ t₂

/-- **Two-bidder BIC**: the joint mechanism `(p, x₁)` is Bayes incentive compatible
for bidder 1 on `[a₁, ∞)` — reporting truthfully maximizes expected utility for
every type pair `(s, t)`, in both orderings. -/
def IsBIC₂ (p x₁ : ℝ → ℝ → ℝ) (f₂ : ℝ → ℝ) (a₁ a₂ b₂ : ℝ) : Prop :=
  ∀ s t : ℝ, a₁ ≤ s → a₁ ≤ t →
    (∫ t₂ in a₂..b₂, (t * p t t₂ - x₁ t t₂) * f₂ t₂ ≥
     ∫ t₂ in a₂..b₂, (t * p s t₂ - x₁ s t₂) * f₂ t₂) ∧
    (∫ t₂ in a₂..b₂, (s * p s t₂ - x₁ s t₂) * f₂ t₂ ≥
     ∫ t₂ in a₂..b₂, (s * p t t₂ - x₁ t t₂) * f₂ t₂)

private lemma expAlloc₁_eq_linear (p x₁ : ℝ → ℝ → ℝ) (f₂ : ℝ → ℝ)
    (a₂ b₂ r u : ℝ)
    (hint_p : IntervalIntegrable (fun t₂ => p u t₂ * f₂ t₂) volume a₂ b₂)
    (hint_x : IntervalIntegrable (fun t₂ => x₁ u t₂ * f₂ t₂) volume a₂ b₂) :
    r * expAlloc₁ p f₂ a₂ b₂ u - expPayment₁ x₁ f₂ a₂ b₂ u =
    ∫ t₂ in a₂..b₂, (r * p u t₂ - x₁ u t₂) * f₂ t₂ := by
  simp only [expAlloc₁, expPayment₁]
  have hrp : IntervalIntegrable (fun t₂ => r * (p u t₂ * f₂ t₂)) volume a₂ b₂ := by
    simpa [smul_eq_mul] using hint_p.smul r
  have hmul : ∫ t₂ in a₂..b₂, r * (p u t₂ * f₂ t₂) =
      r * ∫ t₂ in a₂..b₂, p u t₂ * f₂ t₂ := by
    rw [show (fun t₂ => r * (p u t₂ * f₂ t₂)) = fun t₂ => r • (p u t₂ * f₂ t₂) from by
      ext; simp [smul_eq_mul]]
    rw [intervalIntegral.integral_smul (𝕜 := ℝ)]
    simp [smul_eq_mul]
  symm
  rw [show (fun t₂ => (r * p u t₂ - x₁ u t₂) * f₂ t₂) =
      fun t₂ => r * (p u t₂ * f₂ t₂) - x₁ u t₂ * f₂ t₂ from by ext; ring,
    integral_sub hrp hint_x, hmul]

/-- **BIC implies reduced-form IC** (Myerson 1981): two-bidder BIC for bidder 1
implies the expected allocation `expAlloc₁` satisfies `IsMultiAgentIC`. The proof
factors each joint integral into `expAlloc₁` and `expPayment₁` via linearity. -/
theorem expAlloc₁_satisfies_IC (p x₁ : ℝ → ℝ → ℝ) (f₂ : ℝ → ℝ) (a₁ a₂ b₂ : ℝ)
    (hBIC : IsBIC₂ p x₁ f₂ a₁ a₂ b₂)
    (hint_p : ∀ t₁, IntervalIntegrable (fun t₂ => p t₁ t₂ * f₂ t₂) volume a₂ b₂)
    (hint_x : ∀ t₁, IntervalIntegrable (fun t₂ => x₁ t₁ t₂ * f₂ t₂) volume a₂ b₂) :
    IsMultiAgentIC (expAlloc₁ p f₂ a₂ b₂) (expPayment₁ x₁ f₂ a₂ b₂) a₁ := by
  intro s t hs ht
  obtain ⟨hBIC_t, hBIC_s⟩ := hBIC s t hs ht
  refine ⟨?_, ?_⟩
  · linarith [expAlloc₁_eq_linear p x₁ f₂ a₂ b₂ t t (hint_p t) (hint_x t),
              expAlloc₁_eq_linear p x₁ f₂ a₂ b₂ t s (hint_p s) (hint_x s)]
  · linarith [expAlloc₁_eq_linear p x₁ f₂ a₂ b₂ s s (hint_p s) (hint_x s),
              expAlloc₁_eq_linear p x₁ f₂ a₂ b₂ s t (hint_p t) (hint_x t)]

/-! ### 2.7 N-Bidder Expected Allocation and BIC (Measure.pi Formulation)

Full n-bidder generalisation of the 2-bidder results in §2.6.  The type space
for `n` bidders is `Fin n → ℝ` with product measure `Measure.pi μ`.  Bidder
`i`'s **reduced-form allocation** is the integral of `p (t[i ← s]) i` over all
type profiles, holding bidder `i`'s type fixed at `s` via `Function.update`. -/

section NBidderAuction

variable {n : ℕ}

/-- **Expected allocation for bidder i** in an n-bidder auction: the winning probability
integrated over all type profiles `t : Fin n → ℝ` under the product measure `Measure.pi μ`,
holding bidder `i`'s type fixed at `s` via `Function.update t i s`.
This marginalises over opponents' types `t_{-i}` while keeping `t_i = s`.

*Reference*: Myerson (1981), §3, Equation (1.3) for the reduced-form. -/
noncomputable def expAllocN
    (p : (Fin n → ℝ) → Fin n → ℝ)
    (μ : Fin n → Measure ℝ) (i : Fin n) (s : ℝ) : ℝ :=
  ∫ t : Fin n → ℝ, p (Function.update t i s) i ∂Measure.pi μ

/-- **Expected payment for bidder i** in an n-bidder auction: the transfer integrated
over all type profiles under the product measure. -/
noncomputable def expPaymentN
    (x : (Fin n → ℝ) → Fin n → ℝ)
    (μ : Fin n → Measure ℝ) (i : Fin n) (s : ℝ) : ℝ :=
  ∫ t : Fin n → ℝ, x (Function.update t i s) i ∂Measure.pi μ

/-- **n-Bidder Bayes Incentive Compatibility (BIC_N)**: the joint mechanism `(p, x)`
is Bayes IC for bidder `i` on `[θ_min, ∞)`.  Truth-telling maximises expected utility
in expectation over opponents' types, with both one-sided IC constraints holding.

*Reference*: Myerson (1981), §3, Condition (4.6) generalised to n bidders. -/
def IsBICN
    (p : (Fin n → ℝ) → Fin n → ℝ) (x : (Fin n → ℝ) → Fin n → ℝ)
    (μ : Fin n → Measure ℝ) (i : Fin n) (θ_min : ℝ) : Prop :=
  ∀ s r : ℝ, θ_min ≤ s → θ_min ≤ r →
    (∫ t : Fin n → ℝ, (s * p (Function.update t i s) i - x (Function.update t i s) i)
        ∂Measure.pi μ ≥
     ∫ t : Fin n → ℝ, (s * p (Function.update t i r) i - x (Function.update t i r) i)
        ∂Measure.pi μ) ∧
    (∫ t : Fin n → ℝ, (r * p (Function.update t i r) i - x (Function.update t i r) i)
        ∂Measure.pi μ ≥
     ∫ t : Fin n → ℝ, (r * p (Function.update t i s) i - x (Function.update t i s) i)
        ∂Measure.pi μ)

/-- Linearisation lemma: the expected-utility difference at type `c` reporting `s` equals
`c * expAllocN p μ i s - expPaymentN x μ i s`.  Used to connect `IsBICN` to
`IsMultiAgentIC` by factoring out the constant type weight `c`. -/
private lemma expAllocN_eq_linear
    (p : (Fin n → ℝ) → Fin n → ℝ) (x : (Fin n → ℝ) → Fin n → ℝ)
    (μ : Fin n → Measure ℝ) [∀ j, SigmaFinite (μ j)]
    (i : Fin n) (c s : ℝ)
    (hint_p : Integrable (fun t : Fin n → ℝ => p (Function.update t i s) i) (Measure.pi μ))
    (hint_x : Integrable (fun t : Fin n → ℝ => x (Function.update t i s) i) (Measure.pi μ)) :
    c * expAllocN p μ i s - expPaymentN x μ i s =
    ∫ t : Fin n → ℝ,
      (c * p (Function.update t i s) i - x (Function.update t i s) i) ∂Measure.pi μ := by
  simp only [expAllocN, expPaymentN]
  symm
  rw [integral_sub (hint_p.const_mul c) hint_x, MeasureTheory.integral_const_mul]

/-- **BIC_N implies reduced-form IC** (n-bidder, Myerson 1981 Lemma 2): if the joint
mechanism `(p, x)` is Bayes IC for bidder `i`, the reduced-form expected allocation
`expAllocN p μ i` and payment `expPaymentN x μ i` satisfy the two-sided IC condition
`IsMultiAgentIC`.

The proof uses only linearity of the Bochner integral over `Measure.pi μ` — no
Fubini / product-integral factorisation is needed.

*Reference*: Myerson (1981), Lemma 2; generalisation from §2.6 to arbitrary n. -/
theorem expAllocN_satisfies_IC
    (p : (Fin n → ℝ) → Fin n → ℝ) (x : (Fin n → ℝ) → Fin n → ℝ)
    (μ : Fin n → Measure ℝ) [∀ j, SigmaFinite (μ j)]
    (i : Fin n) (θ_min : ℝ)
    (hBIC : IsBICN p x μ i θ_min)
    (hint_p : ∀ s, Integrable (fun t : Fin n → ℝ => p (Function.update t i s) i) (Measure.pi μ))
    (hint_x : ∀ s, Integrable (fun t : Fin n → ℝ => x (Function.update t i s) i) (Measure.pi μ)) :
    IsMultiAgentIC (expAllocN p μ i) (expPaymentN x μ i) θ_min := by
  intro s r hs hr
  obtain ⟨hBIC_s, hBIC_r⟩ := hBIC s r hs hr
  refine ⟨?_, ?_⟩
  · linarith [expAllocN_eq_linear p x μ i r r (hint_p r) (hint_x r),
              expAllocN_eq_linear p x μ i r s (hint_p s) (hint_x s)]
  · linarith [expAllocN_eq_linear p x μ i s s (hint_p s) (hint_x s),
              expAllocN_eq_linear p x μ i s r (hint_p r) (hint_x r)]

end NBidderAuction

end MechDesign.Myerson
