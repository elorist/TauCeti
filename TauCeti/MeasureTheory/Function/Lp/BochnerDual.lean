/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import TauCeti.MeasureTheory.Function.Holder
import TauCeti.MeasureTheory.Function.Lp.Duality

/-!
# The integral pairing of Bochner spaces

For Hölder conjugate exponents `1 / p + 1 / q = 1`, the integral pairing
`⟨f, g⟩ = ∫ g x (f x) dμ` of `f ∈ Lᵖ(μ; X)` with `g ∈ L^q(μ; X⋆)`, `X⋆ = StrongDual 𝕜 X`, gives
the canonical map `MeasureTheory.Lp.bochnerDualMap 𝕜 X μ p q : L^q(μ; X⋆) →L[𝕜] Lᵖ(μ; X)⋆`.
It is Mathlib's `ContinuousLinearMap.lpPairing` for the identity of `X⋆`, and Hölder's inequality
makes it a contraction. This file proves that it is an isometry, and that its range norms
`Lᵖ(μ; X)`:

* the isometry holds on an arbitrary measure when `q < ∞`, on a semifinite measure when `q = ∞`,
  and hence on a σ-finite measure for all exponents;
* the norming property holds on an arbitrary measure when `p < ∞`, and on a σ-finite measure for
  all exponents.

Some hypothesis on the measure is needed at the exponent `∞`: when `μ` is a single atom of
infinite measure, every integrable function vanishes, so the pairing of `L^∞(μ; X⋆)` with
`L¹(μ; X)` is zero, while `L^∞(μ; X⋆)` is not zero for `X ≠ 0`.

All these statements are instances of one fact about the pairing `∫ B (h x) (k x) dμ` induced by
a continuous bilinear form `B : E →L[𝕜] F →L[𝕜] 𝕜`: if `B` is pointwise isometric, `‖B e‖ = ‖e‖`
for every `e : E`, then `h ↦ B.lpPairing μ r r' h` is isometric on `L^r(μ; E)` under the same
conditions on `r` and `μ`. Take `B` the identity of `X⋆` for the isometry, and the canonical
embedding of `X` into its bidual for the norming property.

For finite `r` the proof reduces, by density of simple functions in `L^r`, to a simple function
`h`. Fix `a < 1`. For each of the finitely many values `e` of `h` choose `u e` in the unit ball of
`F` with `a ‖e‖ ≤ ‖B e (u e)‖`. The scalar simple function `c x = B (h x) (u (h x))` then has
`L^r` norm at least `a ‖h‖_r`, and pairing it with a scalar simple test function `φ ∈ L^{r'}` is
the pairing of `h` with `φ • (u ∘ h)`, whose `L^{r'}` norm is at most `‖φ‖_{r'}`. The scalar
duality bound for `L^r` against simple test functions gives `‖c‖_r ≤ ‖B.lpPairing μ r r' h‖`.

For `r = ∞`, given `a < ‖h‖_∞`, choose a set `t` of finite positive measure on which `‖h‖ > a`.
The restriction of `h` to `t` lies in `L¹(μ|_t; E)` with norm at least `a μ(t)`, the case `r = 1`
on `μ|_t` norms it by `L^∞(μ|_t; F)` tests, and their extensions by zero lie in `L¹(μ; F)` with
norm at most `μ(t)` times their `L^∞` norm.

## Main declarations

* `ContinuousLinearMap.norm_lpPairing_apply`, `ContinuousLinearMap.norm_lpPairing_apply_top`,
  `ContinuousLinearMap.norm_lpPairing_apply_of_sigmaFinite`: a pointwise isometric bilinear form
  induces an isometric pairing for `r < ∞`, for `r = ∞` on a semifinite measure, and for every `r`
  on a σ-finite measure.
* `MeasureTheory.Lp.bochnerDualMap`: the integral pairing `L^q(μ; X⋆) →L[𝕜] Lᵖ(μ; X)⋆`.
* `MeasureTheory.Lp.norm_bochnerDualMap_of_one_lt`, `MeasureTheory.Lp.norm_bochnerDualMap_one`,
  `MeasureTheory.Lp.norm_bochnerDualMap`: the pairing is isometric for `1 < p` on any measure, for
  `p = 1` on a semifinite measure, and for all exponents on a σ-finite measure.
* `MeasureTheory.Lp.norm_bochnerDualMap_flip_apply_of_ne_top`,
  `MeasureTheory.Lp.norm_bochnerDualMap_flip_apply`,
  `MeasureTheory.Lp.norm_le_of_dual_pairing_bound`: the functionals `f ↦ ∫ g x (f x) dμ` with
  `‖g‖_q ≤ 1` norm `Lᵖ(μ; X)`, for `p < ∞` on any measure and for all exponents on a σ-finite
  measure.
* `MeasureTheory.Lp.bochnerDualMap_compLp`: naturality of the pairing for a bounded linear map
  `T : X →L[𝕜] Y` and its adjoint `y⋆ ↦ y⋆ ∘ T`.

## References

* T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces*, Vol. I,
  Springer, 2016, Proposition 1.3.1.
* J. Diestel, J. J. Uhl, *Vector Measures*, Mathematical Surveys 15, AMS, 1977, Chapter IV, §1.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ContinuousLinearMap

variable {α 𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {mα : MeasurableSpace α} {μ : Measure α}
  {r r' : ℝ≥0∞} [Fact (1 ≤ r)] [Fact (1 ≤ r')] [r.HolderConjugate r']

/-- A bilinear form `B` with `‖e‖ ≤ ‖B e‖` almost attains the norm of `e` on the unit ball: for
`a < 1` some `x` with `‖x‖ ≤ 1` has `a ‖e‖ ≤ ‖B e x‖`. -/
private theorem exists_norm_le_one_mul_enorm_le (B : E →L[𝕜] F →L[𝕜] 𝕜)
    (hB : ∀ e, ‖e‖ ≤ ‖B e‖) {a : ℝ≥0∞} (ha : a < 1) (e : E) :
    ∃ x : F, ‖x‖ ≤ 1 ∧ a * ‖e‖ₑ ≤ ‖B e x‖ₑ := by
  rcases eq_or_ne e 0 with rfl | he
  · exact ⟨0, by simp, by simp⟩
  have ha' : a.toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal ha.ne_top ENNReal.one_ne_top).2 ha
  obtain ⟨x, hx, hlt⟩ := (B e).exists_lt_apply_of_lt_opNorm
    ((mul_lt_of_lt_one_left (norm_pos_iff.2 he) ha').trans_le (hB e))
  refine ⟨x, hx.le, ?_⟩
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_toReal ha.ne_top,
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_le_ofReal hlt.le

/-- The lower bound `a ‖h‖_r ≤ ‖B.lpPairing μ r r' h‖` for a simple function `h` and `a < 1`. -/
private theorem mul_enorm_le_enorm_lpPairing_simpleFunc (B : E →L[𝕜] F →L[𝕜] 𝕜)
    (hB : ∀ e, ‖e‖ ≤ ‖B e‖) (hr : r ≠ ∞) (h : Lp.simpleFunc E r μ) {a : ℝ≥0∞} (ha : a < 1) :
    a * ‖(h : Lp E r μ)‖ₑ ≤ ‖B.lpPairing μ r r' h‖ₑ := by
  rcases eq_or_ne a 0 with rfl | ha₀
  · simp
  choose u hu_norm hu using exists_norm_le_one_mul_enorm_le B hB ha
  set g := Lp.simpleFunc.toSimpleFunc h
  have hg : MemLp g r μ := Lp.simpleFunc.memLp h
  have hgh : g =ᵐ[μ] h := Lp.simpleFunc.toSimpleFunc_eq_toFun h
  -- The scalar function `c x = B (g x) (u (g x))` almost attains the norm of `g` pointwise.
  set c : SimpleFunc α 𝕜 := g.map fun e ↦ B e (u e)
  have hc_le (x : α) : ‖c x‖ ≤ ‖B‖ * ‖g x‖ := by
    simp only [c, SimpleFunc.map_apply]
    calc ‖B (g x) (u (g x))‖ ≤ ‖B (g x)‖ * ‖u (g x)‖ := le_opNorm _ _
      _ ≤ ‖B‖ * ‖g x‖ * 1 := by gcongr; exacts [le_opNorm _ _, hu_norm _]
      _ = ‖B‖ * ‖g x‖ := mul_one _
  have hc : MemLp c r μ := hg.of_le_mul c.aestronglyMeasurable (ae_of_all _ hc_le)
  have hgc : eLpNorm g r μ ≤ a⁻¹ * eLpNorm c r μ :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' r g.aestronglyMeasurable <| ae_of_all _ fun x ↦ by
      rw [← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (.inl ha₀) (.inl ha.ne_top),
        mul_comm]
      simpa [c] using hu (g x)
  -- The pairing of `c` with a scalar simple test function `φ` is a pairing of `h`.
  have hcB : eLpNorm c r μ ≤ ‖B.lpPairing μ r r' h‖ₑ := by
    refine hc.eLpNorm_le_of_forall_enorm_integral_mul_le_of_ne_top (q' := r') hr
      fun φ hφ ↦ ?_
    set k : SimpleFunc α F := (φ.pair g).map fun z ↦ z.1 • u z.2
    have hk_le (x : α) : ‖k x‖ ≤ ‖φ x‖ := by
      simpa [k, norm_smul] using mul_le_of_le_one_right (norm_nonneg _) (hu_norm (g x))
    have hk : MemLp k r' μ := hφ.of_le k.aestronglyMeasurable (ae_of_all _ hk_le)
    have hpair : B.lpPairing μ r r' h (hk.toLp k) = ∫ x, c x * φ x ∂μ := by
      rw [lpPairing_eq_integral]
      refine integral_congr_ae ?_
      filter_upwards [hgh, hk.coeFn_toLp] with x hgx hkx
      rw [hkx, ← hgx]
      simp [k, c, mul_comm]
    calc ‖∫ x, c x * φ x ∂μ‖ₑ = ‖B.lpPairing μ r r' h (hk.toLp k)‖ₑ := by rw [hpair]
      _ ≤ ‖B.lpPairing μ r r' h‖ₑ * ‖hk.toLp k‖ₑ := le_opENorm _ _
      _ ≤ ‖B.lpPairing μ r r' h‖ₑ * eLpNorm φ r' μ := by
        rw [Lp.eNorm_toLp]
        gcongr
        exact eLpNorm_mono k.aestronglyMeasurable hk_le
  calc a * ‖(h : Lp E r μ)‖ₑ = a * eLpNorm g r μ := by
        rw [Lp.eNorm_def, eLpNorm_congr_ae hgh]
    _ ≤ a * (a⁻¹ * eLpNorm c r μ) := by gcongr
    _ = eLpNorm c r μ := by rw [← mul_assoc, ENNReal.mul_inv_cancel ha₀ ha.ne_top, one_mul]
    _ ≤ ‖B.lpPairing μ r r' h‖ₑ := hcB

/-- Hölder's inequality for a pointwise isometric bilinear form, which has norm at most one. -/
private theorem norm_lpPairing_apply_le (B : E →L[𝕜] F →L[𝕜] 𝕜) (hB : ∀ e, ‖B e‖ = ‖e‖)
    (h : Lp E r μ) : ‖B.lpPairing μ r r' h‖ ≤ ‖h‖ :=
  (le_opNorm _ _).trans <| mul_le_of_le_one_left (norm_nonneg h) <| (norm_lpPairing_le B).trans <|
    opNorm_le_bound _ zero_le_one fun e ↦ by rw [hB, one_mul]

/-- **Isometry of the integral pairing.** If a bilinear form `B : E →L[𝕜] F →L[𝕜] 𝕜` is pointwise
isometric, `‖B e‖ = ‖e‖`, then for a finite exponent `r` and its Hölder conjugate `r'` the
functional `k ↦ ∫ B (h x) (k x) dμ` on `L^{r'}(μ; F)` has norm `‖h‖_r` for every `h ∈ L^r(μ; E)`.
No assumption is made on the measure. -/
theorem norm_lpPairing_apply (B : E →L[𝕜] F →L[𝕜] 𝕜) (hB : ∀ e, ‖B e‖ = ‖e‖) (hr : r ≠ ∞)
    (h : Lp E r μ) : ‖B.lpPairing μ r r' h‖ = ‖h‖ := by
  refine le_antisymm (norm_lpPairing_apply_le B hB h) ?_
  -- The set where the bound holds is closed, and contains the dense set of simple functions.
  refine (Lp.simpleFunc.denseRange hr).induction_on h
    (isClosed_le continuous_norm (continuous_norm.comp (B.lpPairing μ r r').continuous))
    fun h ↦ ?_
  rw [← toReal_eNorm, ← toReal_eNorm]
  exact ENNReal.toReal_mono eNorm_ne_top <| ENNReal.le_of_forall_lt_one_mul_le fun a ha ↦
    mul_enorm_le_enorm_lpPairing_simpleFunc B (fun e ↦ (hB e).ge) hr h ha

/-- Pairing the restriction of `h ∈ L^∞(μ; E)` to a set `t` of finite measure with `L^∞` tests on
`t` is pairing `h` with their extensions by zero, whose `L¹(μ)` norm is at most `μ(t)` times
their `L^∞` norm. -/
private theorem norm_lpPairing_restrict_le (B : E →L[𝕜] F →L[𝕜] 𝕜) {t : Set α}
    (ht : MeasurableSet t) (ht_top : μ t < ∞) (h : Lp E ∞ μ) (hh₁ : MemLp h 1 (μ.restrict t)) :
    ‖B.lpPairing (μ.restrict t) 1 ∞ (hh₁.toLp h)‖ ≤ ‖B.lpPairing μ ∞ 1 h‖ * μ.real t := by
  have : IsFiniteMeasure (μ.restrict t) := isFiniteMeasure_restrict.2 ht_top.ne
  refine opNorm_le_bound _ (by positivity) fun k ↦ ?_
  have hK : MemLp (t.indicator k) 1 μ := (memLp_indicator_iff_restrict ht.nullMeasurableSet).2
    ((Lp.memLp k).mono_exponent le_top)
  have hpair : B.lpPairing (μ.restrict t) 1 ∞ (hh₁.toLp h) k =
      B.lpPairing μ ∞ 1 h (hK.toLp _) := by
    simp only [lpPairing_eq_integral]
    calc ∫ x, B (hh₁.toLp h x) (k x) ∂μ.restrict t = ∫ x in t, B (h x) (k x) ∂μ :=
          integral_congr_ae (hh₁.coeFn_toLp.mono fun x hx ↦ by simp only [hx])
      _ = ∫ x, t.indicator (fun x ↦ B (h x) (k x)) x ∂μ := (integral_indicator ht).symm
      _ = ∫ x, B (h x) (hK.toLp _ x) ∂μ := integral_congr_ae <| hK.coeFn_toLp.mono fun x hx ↦ by
          simp only [hx]
          by_cases hxt : x ∈ t <;> simp [hxt]
  have hKnorm : ‖hK.toLp (t.indicator k)‖ ≤ μ.real t * ‖k‖ := by
    rw [Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict ht.nullMeasurableSet, Lp.norm_def,
      measureReal_def, ← ENNReal.toReal_mul, mul_comm]
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.memLp k).eLpNorm_ne_top ht_top.ne) ?_
    simpa using eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) le_top
      (Lp.aestronglyMeasurable k) (μ := μ.restrict t)
  rw [hpair, mul_assoc]
  exact (le_opNorm _ _).trans (by gcongr)

/-- **Isometry of the integral pairing at the exponent `∞`.** On a semifinite measure space, in
which every measurable set of positive measure contains a measurable subset of finite positive
measure, a pointwise isometric bilinear form `B : E →L[𝕜] F →L[𝕜] 𝕜` gives
`‖k ↦ ∫ B (h x) (k x) dμ‖ = ‖h‖_∞` on `L¹(μ; F)` for every `h ∈ L^∞(μ; E)`. -/
theorem norm_lpPairing_apply_top (B : E →L[𝕜] F →L[𝕜] 𝕜) (hB : ∀ e, ‖B e‖ = ‖e‖)
    (hμ : ∀ s, MeasurableSet s → μ s ≠ 0 → ∃ t ⊆ s, MeasurableSet t ∧ μ t ≠ 0 ∧ μ t < ∞)
    (h : Lp E ∞ μ) : ‖B.lpPairing μ ∞ 1 h‖ = ‖h‖ := by
  refine le_antisymm (norm_lpPairing_apply_le B hB h)
    (le_of_forall_lt_imp_le_of_dense fun a ha ↦ ?_)
  rcases lt_or_ge a 0 with ha₀ | ha₀
  · exact ha₀.le.trans (norm_nonneg _)
  -- `‖h‖ > a` on a set of positive measure, which contains a set `t` of finite positive measure.
  set s := {x | a < ‖h x‖}
  have hs : MeasurableSet s :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable h).norm.measurable
  have hs₀ : μ s ≠ 0 := fun h₀ ↦ ha.not_ge <| Lp.norm_le_of_ae_bound_top ha₀ <| by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h₀] with x hx
    simpa [s] using hx
  obtain ⟨t, hts, ht, ht₀, ht_top⟩ := hμ s hs hs₀
  have : IsFiniteMeasure (μ.restrict t) := isFiniteMeasure_restrict.2 ht_top.ne
  -- On `t`, the class of `h` in `L¹` has norm at least `a μ(t)`, and it is normed by `L^∞` tests.
  have hh₁ : MemLp h 1 (μ.restrict t) := ((Lp.memLp h).restrict t).mono_exponent le_top
  have hlow : a * μ.real t ≤ ‖hh₁.toLp h‖ := by
    have hlint : ENNReal.ofReal a * μ t ≤ eLpNorm h 1 (μ.restrict t) := by
      rw [eLpNorm_one_eq_lintegral_eNorm hh₁.aestronglyMeasurable]
      calc ENNReal.ofReal a * μ t = ∫⁻ _, ENNReal.ofReal a ∂μ.restrict t := by
            rw [lintegral_const, Measure.restrict_apply_univ]
        _ ≤ ∫⁻ x, ‖h x‖ₑ ∂μ.restrict t := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_restrict_mem ht] with x hx
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hts hx).le
    rw [Lp.norm_toLp, measureReal_def, ← ENNReal.toReal_ofReal ha₀, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono hh₁.eLpNorm_ne_top hlint
  have hiso := B.norm_lpPairing_apply hB ENNReal.one_ne_top (hh₁.toLp h) (r' := ∞)
  exact le_of_mul_le_mul_right
    (hlow.trans (hiso.symm.le.trans (norm_lpPairing_restrict_le B ht ht_top h hh₁)))
    (ENNReal.toReal_pos ht₀ ht_top.ne)

/-- **Isometry of the integral pairing on a σ-finite measure space.** A pointwise isometric
bilinear form `B : E →L[𝕜] F →L[𝕜] 𝕜` gives `‖k ↦ ∫ B (h x) (k x) dμ‖ = ‖h‖_r` on `L^{r'}(μ; F)`
for every `h ∈ L^r(μ; E)` and every pair of Hölder conjugate exponents `r, r'`. -/
theorem norm_lpPairing_apply_of_sigmaFinite [SigmaFinite μ] (B : E →L[𝕜] F →L[𝕜] 𝕜)
    (hB : ∀ e, ‖B e‖ = ‖e‖) (h : Lp E r μ) : ‖B.lpPairing μ r r' h‖ = ‖h‖ := by
  rcases eq_or_ne r ∞ with rfl | hr
  · obtain rfl := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ r').1 rfl
    refine B.norm_lpPairing_apply_top hB (fun s hs hs₀ ↦ ?_) h
    obtain ⟨t, ht, hts, ht₀, ht_top⟩ :=
      Measure.exists_subset_measure_lt_top hs (pos_iff_ne_zero.2 hs₀)
    exact ⟨t, hts, ht, ht₀.ne', ht_top⟩
  · exact B.norm_lpPairing_apply hB hr h

end ContinuousLinearMap

namespace MeasureTheory.Lp

variable {α 𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {mα : MeasurableSpace α} {μ : Measure α}
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

variable (𝕜 X μ p q) in
/-- The integral pairing of Bochner spaces: `g ∈ L^q(μ; X⋆)` acts on `f ∈ Lᵖ(μ; X)` by
`∫ g x (f x) dμ`. It is Mathlib's `ContinuousLinearMap.lpPairing` for the identity of
`X⋆ = StrongDual 𝕜 X`, with the dual-valued argument first. -/
def bochnerDualMap : Lp (StrongDual 𝕜 X) q μ →L[𝕜] StrongDual 𝕜 (Lp X p μ) :=
  (ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 X)).lpPairing μ q p

/-- The integral pairing of Bochner spaces is the `lpPairing` of the identity of `X⋆`. -/
theorem bochnerDualMap_def :
    bochnerDualMap 𝕜 X μ p q = (ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 X)).lpPairing μ q p :=
  (rfl)

/-- The value of the integral pairing of `g ∈ L^q(μ; X⋆)` at `f ∈ Lᵖ(μ; X)`. -/
@[simp]
theorem bochnerDualMap_apply (g : Lp (StrongDual 𝕜 X) q μ) (f : Lp X p μ) :
    bochnerDualMap 𝕜 X μ p q g f = ∫ x, g x (f x) ∂μ := by
  simp [bochnerDualMap_def, ContinuousLinearMap.lpPairing_eq_integral]

/-- **Hölder's inequality** for the integral pairing of Bochner spaces. -/
theorem norm_bochnerDualMap_le (g : Lp (StrongDual 𝕜 X) q μ) :
    ‖bochnerDualMap 𝕜 X μ p q g‖ ≤ ‖g‖ :=
  ((bochnerDualMap 𝕜 X μ p q).le_opNorm g).trans <| mul_le_of_le_one_left (norm_nonneg g) <|
    (ContinuousLinearMap.norm_lpPairing_le _).trans ContinuousLinearMap.norm_id_le

/-- **Isometry of the integral pairing of Bochner spaces.** For `1 < p`, so that the conjugate
exponent `q` is finite, the functional `f ↦ ∫ g x (f x) dμ` on `Lᵖ(μ; X)` has norm `‖g‖_q` for
every `g ∈ L^q(μ; X⋆)`. The measure is arbitrary. -/
theorem norm_bochnerDualMap_of_one_lt (hp : 1 < p) (g : Lp (StrongDual 𝕜 X) q μ) :
    ‖bochnerDualMap 𝕜 X μ p q g‖ = ‖g‖ :=
  (ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 X)).norm_lpPairing_apply (fun _ ↦ rfl)
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).2 hp).ne g

/-- **Isometry of the integral pairing at `p = 1`.** On a semifinite measure space, in which every
measurable set of positive measure contains a measurable subset of finite positive measure, the
functional `f ↦ ∫ g x (f x) dμ` on `L¹(μ; X)` has norm `‖g‖_∞` for every `g ∈ L^∞(μ; X⋆)`. -/
theorem norm_bochnerDualMap_one
    (hμ : ∀ s, MeasurableSet s → μ s ≠ 0 → ∃ t ⊆ s, MeasurableSet t ∧ μ t ≠ 0 ∧ μ t < ∞)
    (g : Lp (StrongDual 𝕜 X) ∞ μ) : ‖bochnerDualMap 𝕜 X μ 1 ∞ g‖ = ‖g‖ :=
  (ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 X)).norm_lpPairing_apply_top (fun _ ↦ rfl) hμ g

/-- **Isometry of the integral pairing of Bochner spaces on a σ-finite measure space.** For every
pair of Hölder conjugate exponents, including `p = 1, q = ∞` and `p = ∞, q = 1`, the functional
`f ↦ ∫ g x (f x) dμ` on `Lᵖ(μ; X)` has norm `‖g‖_q` for every `g ∈ L^q(μ; X⋆)`. -/
theorem norm_bochnerDualMap [SigmaFinite μ] (g : Lp (StrongDual 𝕜 X) q μ) :
    ‖bochnerDualMap 𝕜 X μ p q g‖ = ‖g‖ :=
  (ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 X)).norm_lpPairing_apply_of_sigmaFinite (fun _ ↦ rfl) g

/-- The flipped pairing `f ↦ (g ↦ ∫ g x (f x) dμ)` is the pairing induced by the canonical
embedding of `X` into its bidual. -/
private theorem bochnerDualMap_flip_apply (f : Lp X p μ) :
    (bochnerDualMap 𝕜 X μ p q).flip f =
      (NormedSpace.inclusionInDoubleDual 𝕜 X).lpPairing μ p q f := by
  ext g
  simp [ContinuousLinearMap.lpPairing_eq_integral]

/-- **The integral pairing norms `Lᵖ(μ; X)`.** For `p < ∞`, the norm of `f ∈ Lᵖ(μ; X)` is the
supremum of `‖∫ g x (f x) dμ‖` over the `g ∈ L^q(μ; X⋆)` with `‖g‖_q ≤ 1`. The measure is
arbitrary. -/
theorem norm_bochnerDualMap_flip_apply_of_ne_top (hp : p ≠ ∞) (f : Lp X p μ) :
    ‖(bochnerDualMap 𝕜 X μ p q).flip f‖ = ‖f‖ := by
  rw [bochnerDualMap_flip_apply]
  exact (NormedSpace.inclusionInDoubleDual 𝕜 X).norm_lpPairing_apply
    (NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map hp f

/-- **The integral pairing norms `Lᵖ(μ; X)` on a σ-finite measure space.** For every pair of
Hölder conjugate exponents, the norm of `f ∈ Lᵖ(μ; X)` is the supremum of `‖∫ g x (f x) dμ‖` over
the `g ∈ L^q(μ; X⋆)` with `‖g‖_q ≤ 1`. -/
theorem norm_bochnerDualMap_flip_apply [SigmaFinite μ] (f : Lp X p μ) :
    ‖(bochnerDualMap 𝕜 X μ p q).flip f‖ = ‖f‖ := by
  rw [bochnerDualMap_flip_apply]
  exact (NormedSpace.inclusionInDoubleDual 𝕜 X).norm_lpPairing_apply_of_sigmaFinite
    (NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map f

/-- **Norming by the integral pairing.** On a σ-finite measure space, if
`‖∫ g x (f x) dμ‖ ≤ C ‖g‖_q` for every `g ∈ L^q(μ; X⋆)`, then `‖f‖_p ≤ C`. -/
theorem norm_le_of_dual_pairing_bound [SigmaFinite μ] (f : Lp X p μ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ g : Lp (StrongDual 𝕜 X) q μ, ‖bochnerDualMap 𝕜 X μ p q g f‖ ≤ C * ‖g‖) :
    ‖f‖ ≤ C :=
  norm_bochnerDualMap_flip_apply (𝕜 := 𝕜) (q := q) f ▸
    ContinuousLinearMap.opNorm_le_bound _ hC hbound

/-- **Naturality of the integral pairing.** For a bounded linear map `T : X →L[𝕜] Y`, pairing
`f ∈ Lᵖ(μ; X)` with the pullback `y⋆ ∘ T` of `g ∈ L^q(μ; Y⋆)` is pairing `T ∘ f` with `g`. -/
theorem bochnerDualMap_compLp {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : X →L[𝕜] Y) (g : Lp (StrongDual 𝕜 Y) q μ) (f : Lp X p μ) :
    bochnerDualMap 𝕜 X μ p q (((ContinuousLinearMap.compL 𝕜 X Y 𝕜).flip T).compLp g) f =
      bochnerDualMap 𝕜 Y μ p q g (T.compLp f) := by
  simp only [bochnerDualMap_apply]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousLinearMap.coeFn_compLp ((ContinuousLinearMap.compL 𝕜 X Y 𝕜).flip T) g,
    T.coeFn_compLp f] with x hg hf
  simp [hg, hf]

end MeasureTheory.Lp
