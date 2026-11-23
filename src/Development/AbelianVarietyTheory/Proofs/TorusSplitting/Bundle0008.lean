module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsRunBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RunParametersBound

theorem real_bounds (f r m ρ w q : ℝ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hm : 1 ≤ m) (hmf : m ≤ f)
    (hf2 : f ^ 2 ≤ ρ) (hρ : 16 ≤ ρ) (hw0 : 0 ≤ w) (hw : w ≤ f ^ 2)
    (hq : 135 * (f * r) * (ρ ^ 7) ^ 4 * (r + 1) ≤ q) :
    (2 * f * m) ^ 2 * (2 * w * ρ) * (f * (135 * (f * r)) * (ρ ^ 7) ^ 3) < q ∧
    2 ≤ q / (135 * (f * r) * (ρ ^ 7) ^ 4) ∧
    90 * m ^ 2 * (2 * f * m) ^ 2 * ρ ≤ q / 2 ∧
    4 * (7 + Real.log q) + 2 * f * m + 1 ≤ q * 2 ∧
    f * r * Real.log 2 + 2 * (2 * f * m) + 3 + (1 + 1) * (r * Real.log r + 3 * r + 3) ≤ q := by
  have hρ1 : (1 : ℝ) ≤ ρ := by linarith
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hN : r ≤ f * r := by nlinarith
  have hN1 : 1 ≤ f * r := by linarith
  have hfρ : f ≤ ρ := by nlinarith
  have hfm : f * m ≤ ρ := by nlinarith
  have hm2 : m ^ 2 ≤ ρ := by nlinarith
  have hd0 : 0 ≤ 2 * f * m := by positivity
  have hd : 2 * f * m ≤ 2 * ρ := by linarith
  have hd2 : (2 * f * m) ^ 2 ≤ (2 * ρ) ^ 2 := by gcongr
  have hB : 0 < 135 * (f * r) * (ρ ^ 7) ^ 4 := by positivity
  have h2B : 135 * (f * r) * (ρ ^ 7) ^ 4 * 2 ≤ q :=
    le_trans (mul_le_mul_of_nonneg_left (by linarith) hB.le) hq
  have hT : ρ ^ 5 ≤ (ρ ^ 7) ^ 4 := by
    rw [← pow_mul]; exact pow_le_pow_right₀ hρ1 (by norm_num)
  have hT4 : 16 * ρ ^ 4 ≤ ρ ^ 5 := by
    rw [pow_succ' ρ 4]; gcongr
  have hT1 : ρ ≤ ρ ^ 4 := le_self_pow₀ hρ1 (by norm_num)
  have hqT : 270 * (ρ ^ 7) ^ 4 ≤ q := by
    have : 135 * 1 * (ρ ^ 7) ^ 4 * 2 ≤ 135 * (f * r) * (ρ ^ 7) ^ 4 * 2 := by gcongr
    linarith
  have hq0 : 0 < q := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h1 : (2 * f * m) ^ 2 * (2 * w * ρ) * (f * (135 * (f * r)) * (ρ ^ 7) ^ 3) ≤
        (2 * ρ) ^ 2 * (2 * ρ * ρ) * (ρ * (135 * (f * r)) * (ρ ^ 7) ^ 3) := by
      have hwρ : w ≤ ρ := hw.trans hf2
      gcongr
    have h2 : (2 * ρ) ^ 2 * (2 * ρ * ρ) * (ρ * (135 * (f * r)) * (ρ ^ 7) ^ 3) =
        8 * (135 * (f * r) * ρ ^ 26) := by ring
    have h3 : 135 * (f * r) * (ρ ^ 7) ^ 4 = ρ ^ 2 * (135 * (f * r) * ρ ^ 26) := by ring
    have h4 : 0 < 135 * (f * r) * ρ ^ 26 := by positivity
    have h5 : 8 * (135 * (f * r) * ρ ^ 26) ≤ ρ ^ 2 * (135 * (f * r) * ρ ^ 26) :=
      mul_le_mul_of_nonneg_right (by nlinarith) h4.le
    linarith
  · rw [le_div_iff₀ hB]; linarith
  · have h1 : 90 * m ^ 2 * (2 * f * m) ^ 2 * ρ ≤ 90 * ρ * (2 * ρ) ^ 2 * ρ := by gcongr
    have h2 : 90 * ρ * (2 * ρ) ^ 2 * ρ = 360 * ρ ^ 4 := by ring
    linarith
  · have h1 : Real.log q = Real.log (q / 4) + Real.log 4 := by
      rw [Real.log_div hq0.ne' (by norm_num)]; ring
    have h2 : Real.log (q / 4) ≤ q / 4 - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h3 : Real.log 4 ≤ 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  · have h1 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have h2 : Real.log r ≤ r := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < r by linarith); linarith
    have h3 : f * r * Real.log 2 ≤ f * r * 1 := by gcongr
    have h2' : 0 ≤ Real.log r := Real.log_nonneg hr
    have h4 : r * Real.log r ≤ (f * r) * r := by gcongr
    have h5 : 135 * (f * r) * ρ * (r + 1) ≤ 135 * (f * r) * (ρ ^ 7) ^ 4 * (r + 1) := by
      have : ρ ≤ (ρ ^ 7) ^ 4 := by linarith
      gcongr
    have h6 : (f * r) * 1 * r ≤ (f * r) * ρ * r := by gcongr
    have h7 : 1 * ρ ≤ (f * r) * ρ := by gcongr
    have h8 : (f * r) * 16 ≤ (f * r) * ρ := by gcongr
    have h9 : 0 ≤ (f * r) * r := by positivity
    nlinarith

theorem exists_run_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r m : ℕ), 2 ≤ I2.PT.f E * r → 1 ≤ m → m ^ 4 ≤ I2.PT.f E → (I2.PT.f E : ℝ) ^ 2 ≤ I2.PT.rd E → 16 ≤ I2.PT.rd E → ∃ (q : ℕ) (R0 : ℝ), 1 ≤ q ∧ Real.log q ≤ 28 * Real.log (I2.PT.rd E) + 2 * Real.log (I2.PT.f E * r) + 7 ∧ RunOK E r 1 q R0 m := by
  intro E _ _ _ r m hfr hm1 hmf hf2 hrd
  have hf : 1 ≤ I2.PT.f E := by
    rcases Nat.eq_zero_or_pos (I2.PT.f E) with h | h
    · rw [h] at hfr; omega
    · exact h
  have hr : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h] at hfr; omega
    · exact h
  have hmf' : m ≤ I2.PT.f E := (Nat.le_self_pow (by norm_num) m).trans hmf
  have hfR : (1 : ℝ) ≤ I2.PT.f E := by exact_mod_cast hf
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hmfR : (m : ℝ) ≤ I2.PT.f E := by exact_mod_cast hmf'
  have hfrR : (2 : ℝ) ≤ I2.PT.f E * r := by exact_mod_cast hfr
  have hfrd : (I2.PT.f E : ℝ) ≤ I2.PT.rd E := by nlinarith
  have hw : (I2.PT.f E : ℝ) ^ ((3 : ℝ) / 2) ≤ (I2.PT.f E : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hfR (by norm_num)
  have hρ0 : 0 < I2.PT.rd E := by linarith
  set S : ℝ := 135 * ((I2.PT.f E : ℝ) * r) with hS
  have hS0 : 0 < S := by positivity
  have hsq : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS0.le
  set B : ℝ := S * (I2.PT.rd E ^ 7) ^ 4 with hB
  have hB1 : 1 ≤ B := by
    have h1 : (1 : ℝ) ≤ (I2.PT.rd E ^ 7) ^ 4 := one_le_pow₀ (one_le_pow₀ (by linarith))
    have h2 : (1 : ℝ) ≤ S := by linarith
    exact one_le_mul_of_one_le_of_one_le h2 h1
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = ⌈B⌉₊ * (r + 1) := ⟨_, rfl⟩
  have hqR : (q : ℝ) = (⌈B⌉₊ : ℝ) * (r + 1) := by rw [hq]; push_cast; ring
  have hlo : B * (r + 1) ≤ q := by
    rw [hqR]; gcongr; exact Nat.le_ceil B
  have hqR1 : (1 : ℝ) ≤ q := by nlinarith
  have hq1 : 1 ≤ q := by exact_mod_cast hqR1
  have hq0 : (0 : ℝ) < q := by linarith
  have hhi : (q : ℝ) ≤ I2.PT.rd E ^ 28 * ((I2.PT.f E : ℝ) * r) ^ 2 * 540 := by
    have h1 : (⌈B⌉₊ : ℝ) ≤ 2 * B := by
      have := Nat.ceil_lt_add_one (show 0 ≤ B by linarith); linarith
    have h2 : (r : ℝ) + 1 ≤ 2 * ((I2.PT.f E : ℝ) * r) := by nlinarith
    calc (q : ℝ) = (⌈B⌉₊ : ℝ) * (r + 1) := hqR
      _ ≤ (2 * B) * (2 * ((I2.PT.f E : ℝ) * r)) := by gcongr
      _ = _ := by rw [hB, hS]; ring
  obtain ⟨c1, c2, c3, c5, c6⟩ := real_bounds (I2.PT.f E) r m (I2.PT.rd E) _ q hfR hrR hmR hmfR hf2 hrd
    (by positivity) hw hlo
  have hb0 : 2 ≤ I2.b0 (E := E) q (Real.sqrt S) := by
    unfold I2.b0 I2.RR; rw [hsq]; exact c2
  have ht0 : (q : ℝ) * 2 ≤ I2.t0 (E := E) q (Real.sqrt S) := by
    unfold I2.t0; gcongr
  have hd : (I2.dstar (E := E) m : ℝ) = 2 * I2.PT.f E * m := by unfold I2.dstar; push_cast; ring
  refine ⟨q, Real.sqrt S, hq1, ?_, ?_⟩
  · have h7 : Real.log 540 ≤ 7 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have h1 : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
      have h2 : (2.7 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) Real.exp_one_gt_d9.le
      have h3 : (2.7 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 := by gcongr
      rw [h1]; exact le_trans (by norm_num) h3
    have h1 := Real.log_le_log hq0 hhi
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow] at h1
    push_cast at h1
    linarith
  · intro X hX hdim
    subst hX
    refine ⟨⟨q, Real.sqrt S, m, hq1, le_rfl, hfr, hdim, hm1, hmf, hfrd, hf2, hrd, ?_, ?_, by linarith, ?_,
      hq1, ?_, ?_⟩, rfl, rfl, rfl⟩
    · rw [hsq, hS]
      unfold I2.PT.gA
      push_cast
      constructor <;> linarith
    · unfold I2.th I2.omStar I2.RR
      rw [Real.sq_sqrt (by positivity), ← mul_div_assoc, div_lt_one hq0, hsq, hd]
      exact c1
    · unfold I2.M1
      rw [hd]; exact c3
    · rw [Nat.cast_one, _root_.mul_one, _root_.mul_one, hd]
      linarith
    · unfold I2.PT.gA
      rw [Nat.cast_one, hd]
      push_cast
      linarith

end GlobalTheory.RunParametersBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.NormGenEqConstMul
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConstNorm

theorem exists_entire {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {e : W → (Sp ℂ ⟶ X)} (he : IsHolTo Set.univ e)
    {c : V → (Sp ℂ ⟶ Y)} (hc : IsHolTo Set.univ c) {fr : L.ι → W → ℂ}
    (hd : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ e z ⁻¹ᵁ L.U j})
    (hne : ∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.U j → fr j z ≠ 0)
    (hcomp : ∀ j j' z, ⊤ ≤ e z ⁻¹ᵁ (L.U j ⊓ L.U j') →
      fr j z = valAt' (e z) (L.U j ⊓ L.U j') (L.g j j').val * fr j' z)
    {K : Type} [Fintype K] {m : K → (Y ⟶ X)} {ε : K → ℤ} {w : K → V → W} (hwd : ∀ k, Differentiable ℂ (w k))
    (hw : ∀ k z, c z ≫ m k = e (w k z)) (α : LB.Gen (LB.LinComb L m ε)) (hα : α.IsGen) :
    ∃ r : V → ℂ, Differentiable ℂ r ∧ (∀ z, r z ≠ 0) ∧ ∀ z (j : K → L.ι), (∀ k, ⊤ ≤ e (w k z) ⁻¹ᵁ L.U (j k)) →
      valAt' (c z) (LB.wchart L m j) (α.s j).val = r z * ∏ k, fr (j k) (w k z) ^ ε k := by
  classical
  have hv : CubeValues.ValueRules := valAt'_rules
  have hch : ∀ y : W, ∃ i, ⊤ ≤ e y ⁻¹ᵁ L.U i := fun y => by
    have h : e y (default : PrimeSpectrum ℂ) ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    exact ⟨i, (top_le_preimage_iff_mem _ _).2 hi⟩
  choose ch hch using hch
  have hiff : ∀ z (j : K → L.ι), ⊤ ≤ c z ⁻¹ᵁ LB.wchart L m j ↔ ∀ k, ⊤ ≤ e (w k z) ⁻¹ᵁ L.U (j k) := fun z j => by
    simp only [CubeValues.le_preimage_wchart, hw]
  let R : (K → L.ι) → V → ℂ := fun j z =>
    valAt' (c z) (LB.wchart L m j) (α.s j).val * ∏ k, fr (j k) (w k z) ^ (-ε k)
  let r : V → ℂ := fun z => R (fun k => ch (w k z)) z
  have hc0 : ∀ z, ⊤ ≤ c z ⁻¹ᵁ LB.wchart L m (fun k => ch (w k z)) := fun z => (hiff z _).2 fun k => hch _
  have hrR : ∀ z (j : K → L.ι), (∀ k, ⊤ ≤ e (w k z) ⁻¹ᵁ L.U (j k)) → r z = R j z := fun z j hj => by
    have hj' := (hiff z j).2 hj
    have e1 := (CubeValues.val_gen _ hv α hα _ j (hc0 z) hj').trans (congrArg (· * _)
      (CubeValues.val_linComb (c z) hv L _ _ _ j (hc0 z) hj'))
    simp only [hw] at e1
    refine (congrArg (fun t => t * _) e1).trans ?_
    rw [mul_right_comm, _root_.mul_comm, ← Finset.prod_mul_distrib]
    refine congrArg (_ * ·) (Finset.prod_congr rfl fun k _ => ?_)
    have k0 := (CubeValues.le_preimage_inf _ _ _).2 ⟨hch (w k z), hj k⟩
    have n0 := zpow_ne_zero (ε k) (CubeValues.val_unit_ne_zero _ hv k0 (L.g _ _))
    rw [hcomp _ _ _ k0, mul_zpow, zpow_neg, mul_inv_cancel_left₀ n0]
  have hopen : ∀ i, IsOpen {z | ⊤ ≤ e z ⁻¹ᵁ L.U i} := fun i => by simpa using (he (L.U i) 0).1
  refine ⟨r, fun z => ?_, fun z => ?_, fun z j hj => ?_⟩
  · set j : K → L.ι := fun k => ch (w k z)
    obtain ⟨ho, hd'⟩ := hc _ (α.s j).val
    have hn := ho.mem_nhds ⟨Set.mem_univ z, hc0 z⟩
    have d1 : ∀ k, DifferentiableAt ℂ (fun y => fr (j k) (w k y) ^ (-ε k)) z := fun k =>
      (((hd _).differentiableAt ((hopen _).mem_nhds (hch (w k z)))).comp z (hwd k z)).zpow
        (Or.inl (hne _ _ (hch (w k z))))
    have hq : DifferentiableAt ℂ (R j) z :=
      (hd'.differentiableAt hn).mul (HasFDerivAt.finsetProd fun k _ => (d1 k).hasFDerivAt).differentiableAt
    refine hq.congr_of_eventuallyEq ?_
    filter_upwards [hn] with y hy
    exact hrR y j ((hiff y j).1 hy.2)
  · exact mul_ne_zero (CubeValues.val_unit_ne_zero _ hv (hc0 z) _)
      (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hne _ _ (hch _)))
  · rw [hrR z j hj]
    simp only [R]
    rw [_root_.mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_eq_one, _root_.mul_one]
    intro k _
    rw [← zpow_add₀ (hne _ _ (hj k)), neg_add_cancel, zpow_zero]


open AppellHumbertTrivial in
theorem norm_mul_exp_add {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) {x y χ : ℂ} {z l : Fin g → ℂ}
    (hχ : ‖χ‖ = 1) (h : x = χ * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) * y) :
    ‖y‖ * Real.exp (Real.pi / 2 * (hermForm Hm (z + l) (z + l)).re) =
      ‖x‖ * Real.exp (Real.pi / 2 * (hermForm Hm z z).re) := by
  rw [h, norm_mul, norm_mul, hχ, _root_.one_mul, Complex.norm_exp, _root_.mul_comm _ ‖y‖, _root_.mul_assoc,
    ← Real.exp_add, re_hermForm_add_self hH]
  have e : ((Real.pi : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  congr 2
  ring


open AppellHumbertTrivial in
theorem exists_entire_weight {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) {K : Type} [Fintype K]
    (ε n : K → ℤ) (a : K → Fin g → ℂ) (h0 : ∑ k, ε k * n k ^ 2 = 0) :
    ∃ φ : (Fin g → ℂ) → ℂ, Differentiable ℂ φ ∧ ∀ z, Real.exp (φ z).re =
      ∏ k, Real.exp (Real.pi / 2 * (hermForm Hm ((n k : ℂ) • z + a k) ((n k : ℂ) • z + a k)).re) ^ ε k := by
  refine ⟨fun z => ∑ k, (((ε k * n k * Real.pi : ℝ) : ℂ) * hermForm Hm z (a k) +
    ((ε k * (Real.pi / 2) : ℝ) : ℂ) * hermForm Hm (a k) (a k)), ?_, fun z => ?_⟩
  · unfold hermForm dotProduct
    fun_prop
  · have hz : ∀ (t : ℝ) (s : ℤ), Real.exp t ^ s = Real.exp (s * t) := fun t s => by
      rw [← Real.rpow_intCast, ← Real.exp_mul, _root_.mul_comm]
    simp only [hz]
    rw [← Real.exp_sum, Complex.re_sum]
    congr 1
    have h1 : ∑ k, ((ε k * n k ^ 2 : ℤ) : ℝ) * (Real.pi / 2 * (hermForm Hm z z).re) = 0 := by
      rw [← Finset.sum_mul, ← Int.cast_sum, h0, Int.cast_zero, zero_mul]
    rw [← add_zero (∑ k, _), ← h1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [re_hermForm_add_self hH, hermForm_smul_left, hermForm_smul_left, hermForm_smul_right]
    simp only [Complex.add_re, Complex.re_ofReal_mul, star_intCast]
    rw [← Complex.ofReal_intCast, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    push_cast
    ring

theorem isHolTo_ptSecT {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}} (G : Over X)
    (y : Sp ℂ ⟶ X) (e : V → (Over.mk y ⟶ G)) (he : IsHolTo Set.univ fun z => (e z).left) :
    IsHolTo Set.univ fun z => (Out.ptSecT G (e z)).left := by
  have h1 : ∀ z, (Out.ptSecT G (e z)).left ≫ (fst (Over.mk y) G).left = 𝟙 _ := fun z => by
    rw [← Over.comp_left, Out.ptSecT, lift_fst, Over.id_left]
  have h2 : ∀ z, (Out.ptSecT G (e z)).left ≫ (snd (Over.mk y) G).left = (e z).left := fun z => by
    rw [← Over.comp_left, Out.ptSecT, lift_snd]
  refine HolFibre.isHolTo_of_isPullback (Z := (Over.mk y ⊗ G).left) (p := (fst (Over.mk y) G).left)
    (q := (snd (Over.mk y) G).left) (s := (Over.mk y).hom) (t := G.hom)
    (IsPullback.of_hasPullback (Over.mk y).hom G.hom) ?_ ?_
  · exact (funext h1).symm ▸ HolFibre.isHolTo_const isOpen_univ _
  · exact (funext h2).symm ▸ he

theorem isHolTo_slice {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    {X : Scheme.{0}} {e : V × W → (Sp ℂ ⟶ X)} (he : IsHolTo (Set.univ ×ˢ Set.univ) e) (v : V) :
    IsHolTo Set.univ fun w => e (v, w) := fun U f => by
  obtain ⟨ho, hf⟩ := he U f
  have hι : Differentiable ℂ (fun w : W => (v, w)) := by fun_prop
  refine ⟨?_, hf.comp hι.differentiableOn fun z hz => ⟨⟨trivial, trivial⟩, hz.2⟩⟩
  have h := ho.preimage hι.continuous
  simp only [Set.univ_prod_univ] at h
  exact h

theorem norm_gen_eq_const_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ), IsPeriod (Fu.Di i) ty Pm → AHFrame Fu i Pm Hm χl fr → ∀ (K : Type) [Fintype K] (m : K → (Gx (Fu.u i Pm) ⟶ Xo.univ.t.G.left)) (ε n : K → ℤ) (a : K → Fin g → ℂ) (α : LB.Gen (LB.LinComb Xo.univ.t.PP.L m ε)), α.IsGen → ∑ k, ε k * n k ^ 2 = 0 → (∀ k z, (Out.ptSecT Xo.univ.t.G (Fu.ex i Pm z)).left ≫ m k = (Fu.ex i Pm ((n k : ℂ) • z + a k)).left) → ∃ C : ℝ, 0 < C ∧ ∀ (z : Fin g → ℂ) (j : K → Xo.univ.t.PP.L.ι), (∀ k, ⊤ ≤ (Fu.ex i Pm ((n k : ℂ) • z + a k)).left ⁻¹ᵁ Xo.univ.t.PP.L.U (j k)) → ‖valAt' (Out.ptSecT Xo.univ.t.G (Fu.ex i Pm z)).left ((LB.LinComb Xo.univ.t.PP.L m ε).U j) (α.s j).val‖ = C * ∏ k, (‖fr (j k) ((n k : ℂ) • z + a k)‖ * Real.exp (Real.pi / 2 * (hermForm Hm ((n k : ℂ) • z + a k) ((n k : ℂ) • z + a k)).re)) ^ ε k := by
  intro E _ _ _ H Dw l Xo σ g ty Fu i Pm Hm χl fr hP hF K _ m ε n a α hα h0 hm
  obtain ⟨hH, -, -, hd, hne, hcomp, -, hAH⟩ := hF
  have he : IsHolTo Set.univ (fun z => (Fu.ex i Pm z).left) :=
    isHolTo_slice (Fu.hol i 0 Set.univ (fun _ => Pm) isOpen_univ
      ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2 0
  have hc := isHolTo_ptSecT Xo.univ.t.G _ _ he
  have hper : ∀ z b, Fu.ex i Pm (z + Pm b) = Fu.ex i Pm z := fun z b => by
    rw [Fu.ex_add i Pm hP, (Fu.ex_ker i Pm hP _).2 ⟨b, rfl⟩, _root_.mul_one]
  have hL : Xo.univ.t.PP.L.IsLB := Xo.univ.t.PP.isLB
  obtain ⟨r, hrd, hr0, hr⟩ := exists_entire hL he hc hd hne hcomp (w := fun k z => (n k : ℂ) • z + a k)
    (fun k => by fun_prop) hm α hα
  obtain ⟨φ, hφd, hφ⟩ := exists_entire_weight hH ε n a h0
  let F : (Fin g → ℂ) → ℂ := fun z => r z * Complex.exp (-φ z)
  have hFd : Differentiable ℂ F := hrd.mul hφd.neg.cexp
  have key : ∀ (z : Fin g → ℂ) (j : K → Xo.univ.t.PP.L.ι),
      (∀ k, ⊤ ≤ (Fu.ex i Pm ((n k : ℂ) • z + a k)).left ⁻¹ᵁ Xo.univ.t.PP.L.U (j k)) →
      ‖valAt' (Out.ptSecT Xo.univ.t.G (Fu.ex i Pm z)).left ((LB.LinComb Xo.univ.t.PP.L m ε).U j) (α.s j).val‖ =
        ‖F z‖ * ∏ k, (‖fr (j k) ((n k : ℂ) • z + a k)‖ * Real.exp (Real.pi / 2 *
          (hermForm Hm ((n k : ℂ) • z + a k) ((n k : ℂ) • z + a k)).re)) ^ ε k := fun z j hj => by
    refine (congrArg norm (hr z j hj)).trans ?_
    simp only [F, mul_zpow, Finset.prod_mul_distrib, ← hφ, norm_mul, norm_prod, norm_zpow, Complex.norm_exp,
      Complex.neg_re, Real.exp_neg]
    field_simp
  have hFp : ∀ b z, ‖F (z + Pm b)‖ = ‖F z‖ := fun b z => by
    have hch : ∀ k, ∃ j, ⊤ ≤ (Fu.ex i Pm ((n k : ℂ) • z + a k)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun k => by
      have h : (Fu.ex i Pm ((n k : ℂ) • z + a k)).left (default : PrimeSpectrum ℂ) ∈
          (⨆ j, Xo.univ.t.PP.L.U j) := by rw [hL.cover]; trivial
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
      exact ⟨j, (top_le_preimage_iff_mem _ _).2 hj⟩
    choose j hj using hch
    have hs : ∀ k, (n k : ℂ) • (z + Pm b) + a k = (n k : ℂ) • z + a k + Pm (n k • b) := fun k => by
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ, smul_add]
      abel
    have e1 := key z j hj
    have e2 := key (z + Pm b) j fun k => by rw [hs, hper]; exact hj k
    rw [hper, e1] at e2
    simp only [hs] at e2
    rw [Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k)
      (norm_mul_exp_add hH (hAH (n k • b) (j k) ((n k : ℂ) • z + a k)).1 ((hAH (n k • b) (j k) _).2 (hj k)))] at e2
    exact (mul_right_cancel₀ (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _
      (mul_ne_zero (norm_ne_zero_iff.2 (hne _ _ (hj k))) (Real.exp_ne_zero _))) e2).symm
  haveI : DiscreteTopology (AddSubgroup.toIntSubmodule Pm.range) := hP.2.2.1
  have hb : Bornology.IsBounded (Set.range F) := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1
      (AppellHumbertTrivial.exists_bound_of_periodic (AddSubgroup.toIntSubmodule Pm.range) hP.2.2.2.1
        (fun z => ‖F z‖) hFd.continuous.norm (by rintro ⟨_, b, rfl⟩ z; exact hFp b z))
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C, ?_⟩
    rintro _ ⟨z, rfl⟩
    simpa using hC _ ⟨z, rfl⟩
  refine ⟨‖F 0‖, norm_pos_iff.2 (mul_ne_zero (hr0 0) (Complex.exp_ne_zero _)), fun z j hj => ?_⟩
  rw [key z j hj, hFd.apply_eq_apply_of_bounded hb z 0]

end GlobalTheory.ConstNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.PeriodTorusIsTorusAtFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodTorus

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (x : Frame X.Ψ r)

theorem perFr_add (v w : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    Formalism.L2.PjFree.perFr X x (v + w) τ i = Formalism.L2.PjFree.perFr X x v τ i + Formalism.L2.PjFree.perFr X x w τ i := by
  have h : ∀ ρ : E →+* ℂ, Data.emb ρ (v + w) = Data.emb ρ v + Data.emb ρ w := fun ρ => by
    ext a; simp [Data.emb]
  unfold Formalism.L2.PjFree.perFr
  simp only [h]
  split_ifs
  · simp [Matrix.mulVec_add]
  · simp
  · simp [hermC, mul_add, Finset.sum_add_distrib]
  · simp
  · simp

theorem perFr_smul (α : E) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    Formalism.L2.PjFree.perFr X x (α • v) τ i = τ α * Formalism.L2.PjFree.perFr X x v τ i := by
  have h : ∀ ρ : E →+* ℂ, Data.emb ρ (α • v) = ρ α • Data.emb ρ v := fun ρ => by
    ext a; simp [Data.emb]
  unfold Formalism.L2.PjFree.perFr
  simp only [h]
  split_ifs
  · simp [Matrix.mulVec_smul]
  · simp
  · simp only [hermC, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have : starRingEnd ℂ (conjEmb τ α) = τ α := by simp [conjEmb]
    rw [this]; ring
  · simp
  · simp

theorem norm_sq_eq_Hf {J : Type} [Fintype J] (v : EuclideanSpace ℂ J) : ‖v‖ ^ 2 = (I2.Hf v v).re := by
  rw [EuclideanSpace.norm_sq_eq, I2.Hf, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

end

theorem isTorusAt_of_isTorusOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ (Uw : UnfWit U) (k : U.Comp) (x : (U.X k).dom) (Hm : Matrix (Fin Uw.g) (Fin Uw.g) ℂ) (T : I2.PT E) (ψ : (Fin Uw.g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim), IsRiem Uw.F (Uw.ik k) (Uw.Pm k x) Hm → IsTorusOf (Uw.F.Di (Uw.ik k)) (fun j => relab c σ (Uw.e j).1) (Uw.Pm k x) Hm T ψ → I2.IsTorusAt (U.X k) x.1 T ∧ T.r = r ∧ (∀ th, T.ph th = I2.phiFD (U.X k) th x.1) ∧ ∀ m, (Dw.p ≤ m ∨ Dw.q ≤ m) → ∃ τ, T.dim τ ≤ m := by
  intro E _ _ _ H Dw l Xo c σ r U hG hU Uw k x Hm T ψ hR hT
  obtain ⟨hr, hdim, hH, hL, hact, -⟩ := hT
  obtain ⟨hmaj, -, -⟩ := GlobalTheory.RiemMaj.riemann_eq_majorant E H Dw l Xo c σ r U Uw k x Hm hG hU hR
  let P : (Fin r → E) →+ (Fin Uw.g → ℂ) := AddMonoidHom.mk'
    (fun v j => perFr (U.X k) x.1 v (relab c σ (Uw.e j).1) (Uw.e j).2)
    (fun v w => funext fun j => perFr_add _ _ _ _ _ _)
  have hP : ∀ a, P (Uw.φ k a : Fin r → E) = Uw.Pm k x a := fun a => funext fun j => (Uw.Pm_eq k x a j).symm
  have hΛ : ∀ v ∈ (U.X k).Λ, ∃ a, (Uw.φ k a : Fin r → E) = v := fun v hv =>
    ⟨(Uw.φ k).symm ⟨v, hv⟩, by simp⟩
  have hAt : I2.IsTorusAt (U.X k) x.1 T := by
    refine ⟨ψ.toLinearMap.toAddMonoidHom.comp P, -1, Or.inr rfl, fun y => ?_, fun α v => ?_, fun v hv => ?_,
      fun u hu v hv => ?_⟩
    · rw [hL]
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨_, (Uw.φ k a).2, congrArg ψ (hP a)⟩
      · rintro ⟨v, hv, rfl⟩
        obtain ⟨a, rfl⟩ := hΛ v hv
        exact ⟨a, congrArg ψ (hP a).symm⟩
    · change ψ (P ((α : E) • v)) = I2.act α (ψ (P v))
      rw [← hact]
      exact congrArg ψ (funext fun j => perFr_smul _ _ _ _ _ _)
    · obtain ⟨a, rfl⟩ := hΛ v hv
      change ‖ψ (P _)‖ ^ 2 = _
      rw [hP, norm_sq_eq_Hf, hH, hmaj]
    · obtain ⟨a, rfl⟩ := hΛ u hu
      obtain ⟨b, rfl⟩ := hΛ v hv
      change (I2.Hf (ψ (P _)) (ψ (P _))).im = _
      have h := congrArg (fun t : ℚ => (t : ℝ)) (Uw.iso k a b)
      simp only [neg_mul, map_neg, Rat.cast_neg, Rat.cast_intCast] at h
      rw [hP, hP, hH, hR.2.2, h]
      ring
  obtain ⟨hp, hq⟩ := Uw.F.sig (Uw.ik k)
  refine ⟨hAt, by rw [hr, hp, hq, hU.1], (I2.TorusAtPf.torusAtLa1_holds E r _ x.1 x.2 T hAt).2, fun m hm => ?_⟩
  obtain ⟨-, hty⟩ := hU.2.1 k
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ (U.X k).Ψ := by
    obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases h0 : τ0 ∈ (U.X k).Ψ
    · exact ⟨_, h0⟩
    · by_contra hn
      exact h0 (((U.X k).cmType τ0).2 fun h' => hn ⟨_, h'⟩)
  have h1 : T.dim τ = Dw.p := by
    rw [hdim]; unfold Datum.mult; rw [if_pos ((hty τ).1 hτ), hp]
  have h2 := T.dim_conj τ
  rcases hm with hm | hm
  · exact ⟨τ, by omega⟩
  · exact ⟨ComplexEmbedding.conjugate τ, by omega⟩

end GlobalTheory.PeriodTorus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.RelabellingGoodEmbeddingIsTypeFn
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaAn

theorem relab_isTypeFn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ), GoodEmb c σ → Function.Bijective (relab c σ) ∧ (∀ τ, Dw.mult (relab c σ τ) = Dw.mult τ) ∧ ∀ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) := by
  intro E _ _ _ H Dw l _ c σ hσ
  obtain ⟨hbij, hrt, -, hty⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  refine ⟨hbij, fun τ => ?_, fun g e => hty Dw g e⟩
  unfold Datum.mult
  exact if_congr (hrt τ) rfl rfl

end GlobalTheory.EtaAn
end

