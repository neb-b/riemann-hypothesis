module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt
public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.ClsProp
section
open UpperHalfPlane hiding I
open scoped MatrixGroups

namespace UpperTheory.V.Af.Rs

private theorem cls_rep (hR : RowRep) (L : ℕ) [NeZero L] (v : Fin 2 → ZMod L) :
    ∃ (n : ℕ) (γ : SL(2, ℤ)), v = cls L ((n : ℤ) • row γ) := by
  obtain ⟨n, γ, h⟩ := hR (fun i => ((v i).val : ℤ))
  refine ⟨n, γ, ?_⟩
  rw [← h]
  funext i
  simp [cls]

private theorem cls_smul (L : ℕ) (m n : ℕ) (x : Fin 2 → ℤ) :
    (m : ZMod L) • cls L ((n : ℤ) • x) = cls L (((m * n : ℕ) : ℤ) • x) := by
  funext i
  simp only [cls, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

private theorem norm_char_le {L : ℕ} [NeZero L] (ψ : DirichletCharacter ℂ L) (a : ZMod L) : ‖ψ a‖ ≤ 1 :=
  ψ.norm_le_one a

end UpperTheory.V.Af.Rs

theorem UpperTheory.V.Af.Rs.clsProp :
    UpperTheory.V.Af.Rs.RowRep → UpperTheory.V.Af.Rs.ClsProp := by
  intro hR L _ ψ F G hG
  have hscale : ∀ (a : ZMod L) (v : Fin 2 → ZMod L) (z : ℍ), G (a • v) z = ψ a * G v z := by
    intro a v z
    obtain ⟨n, γ, rfl⟩ := cls_rep hR L v
    rw [← ZMod.natCast_zmod_val a, cls_smul, hG, hG]
    push_cast
    rw [map_mul]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hFc, C, hC⟩
    refine ⟨?_, C, ?_⟩
    · intro v
      obtain ⟨n, γ, rfl⟩ := cls_rep hR L v
      have hγ : Continuous (fun z : ℍ => γ • z) :=
        continuous_const_smul (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ))
      have : (fun z => G (cls L ((n : ℤ) • row γ)) z) = fun z => ψ n * F (γ • z) := by
        funext z; exact hG n γ z
      change Continuous (fun z => G (cls L ((n : ℤ) • row γ)) z)
      rw [this]
      exact continuous_const.mul (hFc.comp hγ)
    · intro v z hz
      obtain ⟨n, γ, rfl⟩ := cls_rep hR L v
      rw [hG, norm_mul, mul_assoc]
      have h1 := hC γ z hz
      have h0 : 0 ≤ ‖F (γ • z)‖ * z.im ^ 3 := by
        have : 0 < z.im := z.im_pos
        positivity
      exact (mul_le_of_le_one_left h0 (norm_char_le ψ _)).trans h1
  · intro hψ z
    obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp hψ
    let e : (Fin 2 → ZMod L) ≃ (Fin 2 → ZMod L) :=
      { toFun := fun v => (u : ZMod L) • v
        invFun := fun v => ((u⁻¹ : (ZMod L)ˣ) : ZMod L) • v
        left_inv := fun v => by simp [smul_smul]
        right_inv := fun v => by simp [smul_smul] }
    have hs : ∑ v, G v z = ∑ v, G ((u : ZMod L) • v) z :=
      Fintype.sum_equiv e.symm _ _ (fun v => by simp [e, smul_smul])
    have hs2 : ∑ v, G v z = ψ u * ∑ v, G v z := by
      rw [Finset.mul_sum]
      conv_lhs => rw [hs]
      exact Finset.sum_congr rfl (fun v _ => hscale _ v z)
    have hne : (1 : ℂ) - ψ u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
    have : ((1 : ℂ) - ψ u) * ∑ v, G v z = 0 := by rw [sub_mul, one_mul, ← hs2, sub_self]
    exact (mul_eq_zero.mp this).resolve_left hne
  · intro hψ hF0 hFpos
    have hval : ∀ n : ℕ, ψ n = 0 ∨ ψ n = 1 := by
      intro n
      subst hψ
      by_cases h : IsUnit (n : ZMod L)
      · exact Or.inr (MulChar.one_apply h)
      · exact Or.inl (MulChar.map_nonunit _ h)
    refine ⟨?_, ?_⟩
    · intro v z
      obtain ⟨n, γ, rfl⟩ := cls_rep hR L v
      rw [hG]
      rcases hval n with h | h <;> simp [h, hF0]
    · obtain ⟨z0, hz0⟩ := hFpos
      obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z0
      refine ⟨cls L (((1 : ℕ) : ℤ) • row g⁻¹), g • z0, hg, ?_⟩
      rw [hG, inv_smul_smul]
      subst hψ
      simpa using hz0
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.FdNull
section
open MeasureTheory Set in
private theorem UpperTheory.V.Af.Rs.line_null (c : ℝ) : volume {z : ℂ | z.re = c} = 0 := by
  have h : {z : ℂ | z.re = c} = Complex.measurableEquivRealProd ⁻¹' (({c} : Set ℝ) ×ˢ (univ : Set ℝ)) := by
    ext z
    simp
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv, Measure.volume_eq_prod,
    Measure.prod_prod]
  simp

open MeasureTheory Set in
theorem UpperTheory.V.Af.Rs.fdNull :
    UpperTheory.V.Af.Rs.VolMap → UpperTheory.V.Af.Rs.FdNull := by
  intro _
  unfold UpperTheory.V.Af.Rs.FdNull
  rw [UpperHalfPlane.volume_eq_lintegral]
  apply setLIntegral_measure_zero
  have h0 : volume (Metric.sphere (0 : ℂ) 1 ∪ ({z : ℂ | z.re = 1 / 2} ∪ {z : ℂ | z.re = -(1 / 2)})) = 0 :=
    measure_union_null (Measure.addHaar_sphere _ _ _)
      (measure_union_null (UpperTheory.V.Af.Rs.line_null _) (UpperTheory.V.Af.Rs.line_null _))
  refine measure_mono_null ?_ h0
  rintro _ ⟨z, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
  by_cases hs : 1 < Complex.normSq (z : ℂ)
  · right
    have h4 : ¬ |z.re| < 1 / 2 := fun h => h3 ⟨hs, h⟩
    have h5 : |z.re| = 1 / 2 := le_antisymm h2 (not_lt.mp h4)
    exact (abs_eq (by norm_num)).mp h5
  · left
    have h5 : Complex.normSq (z : ℂ) = 1 := le_antisymm (not_lt.mp hs) h1
    rw [Complex.normSq_eq_norm_sq] at h5
    rw [mem_sphere_zero_iff_norm]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h5
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.GcdSum
section
open UpperTheory.V.Af.Rs in
private lemma gcdSum_inj :
    Function.Injective (fun p : ℕ × Cop => (((p.1 + 1 : ℕ) : ℤ)) • p.2.1) := by
  rintro ⟨n, a, ha⟩ ⟨m, b, hb⟩ h
  simp only at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Pi.smul_apply, smul_eq_mul] at h0 h1
  have ga : (a 0).gcd (a 1) = 1 := Int.isCoprime_iff_gcd_eq_one.mp ha
  have gb : (b 0).gcd (b 1) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hb
  have hk : (((n + 1 : ℕ) : ℤ) * a 0).gcd (((n + 1 : ℕ) : ℤ) * a 1)
      = (((m + 1 : ℕ) : ℤ) * b 0).gcd (((m + 1 : ℕ) : ℤ) * b 1) := by
    rw [h0, h1]
  rw [Int.gcd_mul_left, Int.gcd_mul_left, ga, gb] at hk
  simp only [Int.natAbs_natCast, mul_one] at hk
  have hnm : n = m := by omega
  subst hnm
  have hpos : ((n + 1 : ℕ) : ℤ) ≠ 0 := by positivity
  have e0 : a 0 = b 0 := mul_left_cancel₀ hpos h0
  have e1 : a 1 = b 1 := mul_left_cancel₀ hpos h1
  have hab : a = b := by
    funext i
    fin_cases i
    · exact e0
    · exact e1
  subst hab
  rfl

open UpperTheory.V.Af.Rs in
private lemma gcdSum_surj (v : Fin 2 → ℤ) (hv : v ≠ 0) :
    v ∈ Set.range (fun p : ℕ × Cop => (((p.1 + 1 : ℕ) : ℤ)) • p.2.1) := by
  set g := (v 0).gcd (v 1) with hg
  have hpos : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | h
    · exfalso
      obtain ⟨a0, a1⟩ := Int.gcd_eq_zero_iff.mp h0
      apply hv
      funext i
      fin_cases i
      · exact a0
      · exact a1
    · exact h
  have hc : IsCoprime ((fun i => v i / (g : ℤ)) 0) ((fun i => v i / (g : ℤ)) 1) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd hpos)
  refine ⟨(g - 1, ⟨fun i => v i / (g : ℤ), hc⟩), ?_⟩
  have hg1 : g - 1 + 1 = g := Nat.sub_add_cancel hpos
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, hg1]
  fin_cases i
  · exact Int.mul_ediv_cancel' (Int.gcd_dvd_left (v 0) (v 1))
  · exact Int.mul_ediv_cancel' (Int.gcd_dvd_right (v 0) (v 1))

theorem UpperTheory.V.Af.Rs.gcdSum :
    UpperTheory.V.Af.Rs.GcdSum := by
  intro u c hu hc hu0 hc0 hmul
  have hsupp : Function.support u ⊆
      Set.range (fun p : ℕ × UpperTheory.V.Af.Rs.Cop => (((p.1 + 1 : ℕ) : ℤ)) • p.2.1) := by
    intro v hv
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hv hu0
    exact gcdSum_surj v hv0
  rw [← gcdSum_inj.tsum_eq hsupp]
  have hterm : ∀ p : ℕ × UpperTheory.V.Af.Rs.Cop,
      u ((((p.1 + 1 : ℕ) : ℤ)) • p.2.1) = c (p.1 + 1) * u p.2.1 := fun p => hmul (p.1 + 1) p.2
  have hprod : Summable fun p : ℕ × UpperTheory.V.Af.Rs.Cop => c (p.1 + 1) * u p.2.1 := by
    have := hu.comp_injective gcdSum_inj
    refine this.congr fun p => ?_
    exact hterm p
  simp only [hterm]
  rw [hc.tsum_eq_zero_add, hc0, zero_add]
  exact ((hc.comp_injective (add_left_injective 1)).tsum_mul_tsum
    (hu.comp_injective Subtype.val_injective) hprod).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.HalfLeIm
section
open MeasureTheory Set
open UpperHalfPlane hiding I

namespace UpperTheory.V.Af.Rs

private theorem half_le_im {z : ℍ} (hz : z ∈ ModularGroup.fd) : 1 / 2 ≤ z.im := by
  have h := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have := z.im_pos
  nlinarith

private theorem norm_G_cls_mul_ker_le_of_mem_fd {L : ℕ} (G : (Fin 2 → ZMod L) → ℍ → ℂ) (C s : ℝ)
    (hC : ∀ (v : Fin 2 → ZMod L) (z : ℍ), 1 / 2 ≤ z.im → ‖G v z‖ * z.im ^ 3 ≤ C)
    (hk : ∀ (x : Fin 2 → ℤ), ∀ z ∈ ModularGroup.fd, ker s x z ≤ 4 * z.im ^ 2 * ‖x‖ ^ (-(2 * s)))
    (h0 : ∀ (x : Fin 2 → ℤ) (z : ℍ), 0 ≤ ker s x z) (x : Fin 2 → ℤ) (z : ℍ)
    (hz : z ∈ ModularGroup.fd) :
    ‖G (cls L x) z * (ker s x z : ℂ)‖ ≤ 8 * C * ‖x‖ ^ (-(2 * s)) := by
  have him := half_le_im hz
  have hw : 0 ≤ ‖x‖ ^ (-(2 * s)) := Real.rpow_nonneg (norm_nonneg _) _
  have hG := hC (cls L x) z him
  have hn : 0 ≤ ‖G (cls L x) z‖ := norm_nonneg _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 x z)]
  have h2 : ‖G (cls L x) z‖ * z.im ^ 2 ≤ 2 * C := by
    nlinarith [mul_nonneg (mul_nonneg hn (sq_nonneg z.im)) (sub_nonneg.2 him)]
  calc ‖G (cls L x) z‖ * ker s x z
      ≤ ‖G (cls L x) z‖ * (4 * z.im ^ 2 * ‖x‖ ^ (-(2 * s))) :=
        mul_le_mul_of_nonneg_left (hk x z hz) hn
    _ = 4 * (‖G (cls L x) z‖ * z.im ^ 2) * ‖x‖ ^ (-(2 * s)) := by ring
    _ ≤ 4 * (2 * C) * ‖x‖ ^ (-(2 * s)) := by gcongr
    _ = 8 * C * ‖x‖ ^ (-(2 * s)) := by ring

private theorem sum_cls (L : ℕ) [NeZero L] (g : (Fin 2 → ZMod L) → ℂ) (s : ℝ) (z : ℍ)
    (hs : Summable fun x => ker s x z) :
    ∑' x : Fin 2 → ℤ, g (cls L x) * (ker s x z : ℂ) = ∑ v, g v * (Zc L v s z : ℂ) := by
  have hc : ∀ v, Summable fun x : Fin 2 → ℤ => if cls L x = v then g v * (ker s x z : ℂ) else 0 := by
    intro v
    have := ((Complex.ofRealCLM.summable hs).mul_left (g v)).indicator {x | cls L x = v}
    refine this.congr (fun x => ?_)
    simp [Set.indicator_apply]
  calc ∑' x : Fin 2 → ℤ, g (cls L x) * (ker s x z : ℂ)
      = ∑' x : Fin 2 → ℤ, ∑ v, if cls L x = v then g v * (ker s x z : ℂ) else 0 := by
        refine tsum_congr (fun x => ?_)
        rw [Finset.sum_ite_eq]
        simp
    _ = ∑ v, ∑' x : Fin 2 → ℤ, if cls L x = v then g v * (ker s x z : ℂ) else 0 :=
        Summable.tsum_finsetSum (fun v _ => hc v)
    _ = ∑ v, g v * (Zc L v s z : ℂ) := by
        refine Finset.sum_congr rfl (fun v _ => ?_)
        rw [Zc, Complex.ofReal_tsum, ← tsum_mul_left]
        refine tsum_congr (fun x => ?_)
        split_ifs <;> simp

end UpperTheory.V.Af.Rs

open UpperTheory.V.Af.Rs in
theorem UpperTheory.V.Af.Rs.swap :
    UpperTheory.V.Af.Rs.FdFin → UpperTheory.V.Af.Rs.KerBd → UpperTheory.V.Af.Rs.WTop → UpperTheory.V.Af.Rs.Swap := by
  intro hfd hkb hw L _ G hG s hs
  obtain ⟨hGc, C, hC⟩ := hG
  have hs' : s ∈ Icc (1:ℝ) 2 := ⟨hs.1.le, hs.2⟩
  obtain ⟨hkc, hk0, -, -, -, hkb'⟩ := hkb s hs'
  have hsum : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * s)) := hw.1 (2 * s) (by linarith [hs.1])
  have hbd : ∀ x : Fin 2 → ℤ, ∀ z ∈ ModularGroup.fd,
      ‖G (cls L x) z * (ker s x z : ℂ)‖ ≤ 8 * C * ‖x‖ ^ (-(2 * s)) :=
    fun x z hz => norm_G_cls_mul_ker_le_of_mem_fd G C s hC hkb' hk0 x z hz
  have hint : ∀ x : Fin 2 → ℤ,
      IntegrableOn (fun z => G (cls L x) z * (ker s x z : ℂ)) ModularGroup.fd volume := by
    intro x
    exact Measure.integrableOn_of_bounded hfd.2.ne
      ((hGc _).mul (Complex.continuous_ofReal.comp (hkc x))).aestronglyMeasurable
      ((ae_restrict_iff' hfd.1).2 (Filter.Eventually.of_forall (hbd x)))
  refine ⟨hint, ?_⟩
  have hnorm : Summable fun x : Fin 2 → ℤ =>
      ∫ z in ModularGroup.fd, ‖G (cls L x) z * (ker s x z : ℂ)‖ := by
    refine Summable.of_nonneg_of_le (fun x => integral_nonneg (fun _ => norm_nonneg _))
      (fun x => ?_) ((hsum.mul_left (8 * C)).mul_right (volume.real ModularGroup.fd))
    calc ∫ z in ModularGroup.fd, ‖G (cls L x) z * (ker s x z : ℂ)‖
        ≤ ∫ z in ModularGroup.fd, 8 * C * ‖x‖ ^ (-(2 * s)) :=
          setIntegral_mono_on (hint x).norm (integrableOn_const hfd.2.ne) hfd.1 (hbd x)
      _ = 8 * C * ‖x‖ ^ (-(2 * s)) * volume.real ModularGroup.fd := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]
  have h := hasSum_integral_of_summable_integral_norm hint hnorm
  have e : TT L G s = ∫ z in ModularGroup.fd, ∑' x : Fin 2 → ℤ, G (cls L x) z * (ker s x z : ℂ) := by
    unfold TT
    refine setIntegral_congr_fun hfd.1 (fun z hz => ?_)
    have hsz : Summable fun x : Fin 2 → ℤ => ker s x z :=
      Summable.of_nonneg_of_le (fun x => hk0 x z) (fun x => hkb' x z hz) (hsum.mul_left _)
    exact (sum_cls L (fun v => G v z) s z hsz).symm
  rw [e]
  exact h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.Imports
section
open Set UpperTheory.V.Af UpperTheory.V.Sd
open scoped ComplexConjugate

theorem UpperTheory.V.Af.Rs.cmp :
    UpperTheory.V.Af.Rs.RankSum → UpperTheory.V.Af.Rs.Rankin → UpperTheory.V.Af.Rs.ArFact → UpperTheory.V.Af.Rs.ArSum → UpperTheory.V.Af.Rs.Cmp := by
  intro hRS hR hAF hAS k L _ hk χ ψ g h hap hχ s hs
  have hrec1 : Rs.Rec (fun p => χ (p : ZMod L) * (p:ℂ)^(k-1)) (coef g.f) :=
    ⟨g.one, fun p hp n hn => g.eig p hp n hn⟩
  have hrec2 : Rs.Rec (fun p => ψ (p : ZMod L) * (p:ℂ)^(k-1)) (coef h.f) :=
    ⟨h.one, fun p hp n hn => h.eig p hp n hn⟩
  have hba : ∀ p, Nat.Prime p → coef h.f p = coef g.f p := fun p hp => hap p hp
  have hz : ∀ p, Nat.Prime p → χ (p : ZMod L) * (p:ℂ)^(k-1) ≠ ψ (p : ZMod L) * (p:ℂ)^(k-1) →
      coef g.f p = 0 := by
    intro p hp hne
    apply hχ p hp
    intro heq
    apply hne
    rw [heq]
  have hbd : ∀ p, Nat.Prime p → ‖χ (p : ZMod L) * (p:ℂ)^(k-1)‖ ≤ (p:ℝ)^(k-1) ∧
      ‖ψ (p : ZMod L) * (p:ℂ)^(k-1)‖ ≤ (p:ℝ)^(k-1) := by
    intro p hp
    constructor <;>
    · rw [norm_mul, norm_pow, Complex.norm_natCast]
      exact mul_le_of_le_one_left (by positivity) (DirichletCharacter.norm_le_one _ _)
  obtain ⟨P, hPb, hP⟩ := hAF (k-1) _ _ (coef g.f) (coef h.f) hrec1 hrec2 hba hz hbd
  have hkt : ((k-1 : ℕ) : ℝ) + 1 ≤ (k:ℝ) + s - 1 := by
    rw [Nat.cast_sub hk]
    push_cast
    linarith [hs.1]
  have key := hAS (k-1) ((k:ℝ) + s - 1) (coef g.f) (coef h.f) P hkt hPb hP (hRS k L g.f s hs)
  rw [hR k L g.f g.f s hs, hR k L g.f h.f s hs, norm_mul, norm_mul]
  have hconv : (∑' n : ℕ, (starRingEnd ℂ) (coef g.f n) * coef g.f n / (((n:ℝ) ^ ((k:ℝ) + s - 1) : ℝ) : ℂ))
      = ((∑' n : ℕ, ‖coef g.f n‖ ^ 2 / (n:ℝ) ^ ((k:ℝ) + s - 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    congr 1
    funext n
    rw [Complex.conj_mul']
    push_cast
    ring
  have hnn : 0 ≤ ∑' n : ℕ, ‖coef g.f n‖ ^ 2 / (n:ℝ) ^ ((k:ℝ) + s - 1) :=
    tsum_nonneg fun n => div_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  rw [hconv, Complex.norm_of_nonneg hnn]
  have hre := Complex.re_le_norm (∑' n : ℕ, (starRingEnd ℂ) (coef h.f n) * coef g.f n /
    (((n:ℝ) ^ ((k:ℝ) + s - 1) : ℝ) : ℂ))
  have hg := norm_nonneg ((Rs.gam ((k:ℝ) + s - 1) : ℝ) : ℂ)
  calc _ ≤ ‖((Rs.gam ((k:ℝ) + s - 1) : ℝ) : ℂ)‖ * (7 * ‖∑' n : ℕ, (starRingEnd ℂ) (coef h.f n) * coef g.f n /
        (((n:ℝ) ^ ((k:ℝ) + s - 1) : ℝ) : ℂ)‖) :=
        mul_le_mul_of_nonneg_left (by linarith) hg
    _ = _ := by ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.KerLow
section
noncomputable section

open MeasureTheory Set
open UpperHalfPlane hiding I

namespace UpperTheory.V.Af.Rs

theorem kerLow : KerLow := by
  intro s hs x z hz
  obtain ⟨hs1, hs2⟩ := hs
  unfold ker
  have hy : 0 < z.im := z.im_pos
  have hy2 : 3 ≤ 4 * z.im ^ 2 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  set r : ℝ := ‖(z : ℂ)‖ with hr
  set n : ℝ := ‖x‖ with hn
  have hr0 : 0 ≤ r := norm_nonneg _
  have hn0 : 0 ≤ n := norm_nonneg _
  have hyr : z.im ≤ r := by
    have := Complex.abs_im_le_norm (z : ℂ)
    simp only [UpperHalfPlane.coe_im] at this
    exact le_trans (le_abs_self _) this
  by_cases hx0 : x = 0
  · subst hx0
    have hn' : n = 0 := by simp [hn]
    have hs0 : -(2 * s) ≠ 0 := by linarith
    rw [hn', Real.zero_rpow hs0, mul_zero]
    exact Real.rpow_nonneg (div_nonneg hy.le (Complex.normSq_nonneg _)) _
  have hxi : ∀ i, |((x i : ℤ) : ℝ)| ≤ n := by
    intro i
    have := norm_le_pi_norm x i
    rwa [Int.norm_eq_abs] at this
  have hn1 : 1 ≤ n := by
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx0 (funext h)
    have h1 : (1 : ℝ) ≤ |((x i : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hi
    exact h1.trans (hxi i)
  set w : ℂ := (x 0 : ℂ) * (z : ℂ) + (x 1 : ℂ) with hw
  have hwle : ‖w‖ ≤ n * (r + 1) := by
    calc ‖w‖ ≤ ‖(x 0 : ℂ)‖ * r + ‖(x 1 : ℂ)‖ := by
          rw [hw]
          exact (norm_add_le _ _).trans (by rw [norm_mul])
      _ ≤ n * r + n := by
          rw [Complex.norm_intCast, Complex.norm_intCast]
          have := hxi 0
          have := hxi 1
          nlinarith
      _ = n * (r + 1) := by ring
  have hwne : w ≠ 0 := by
    intro h0
    have him : (w).im = 0 := by rw [h0]; simp
    have hre : (w).re = 0 := by rw [h0]; simp
    simp [hw] at him hre
    rcases him with h | h
    · have h1 : x 1 = 0 := by simpa [h] using hre
      exact hx0 (by ext i; fin_cases i <;> simp [h, h1])
    · exact absurd h hy.ne'
  have hwpos : 0 < Complex.normSq w := Complex.normSq_pos.mpr hwne
  have hnsq : Complex.normSq w ≤ n ^ 2 * (r + 1) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    have := norm_nonneg w
    nlinarith
  set q : ℝ := z.im / (r + 1) ^ 2 with hq
  have hr1 : 0 < (r + 1) ^ 2 := by positivity
  have hq0 : 0 < q := div_pos hy hr1
  have hq1 : q ≤ 1 := by
    rw [div_le_one hr1]
    nlinarith
  have hbase : q / n ^ 2 ≤ z.im / Complex.normSq w := by
    rw [hq, div_div]
    apply div_le_div_of_nonneg_left hy.le hwpos
    nlinarith
  have hqn0 : 0 ≤ q / n ^ 2 := by positivity
  have hstep : (q / n ^ 2) ^ s ≤ (z.im / Complex.normSq w) ^ s :=
    Real.rpow_le_rpow hqn0 hbase (by linarith)
  have hsplit : (q / n ^ 2) ^ s = q ^ s * n ^ (-(2 * s)) := by
    rw [Real.div_rpow hq0.le (by positivity), div_eq_mul_inv, Real.rpow_neg hn0,
      Real.rpow_mul hn0]
    norm_num
  have hq2 : q ^ (2 : ℝ) ≤ q ^ s := Real.rpow_le_rpow_of_exponent_ge hq0 hq1 hs2
  have hq2' : 1 / 2 / (r + 1) ^ 4 ≤ q ^ (2 : ℝ) := by
    rw [Real.rpow_two, hq, div_pow, ← pow_mul]
    norm_num
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have hnpos : 0 ≤ n ^ (-(2 * s)) := Real.rpow_nonneg hn0 _
  calc 1 / 2 / (r + 1) ^ 4 * n ^ (-(2 * s)) ≤ q ^ s * n ^ (-(2 * s)) :=
        mul_le_mul_of_nonneg_right (hq2'.trans hq2) hnpos
    _ = (q / n ^ 2) ^ s := hsplit.symm
    _ ≤ _ := hstep

end UpperTheory.V.Af.Rs
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.TBdd
section
open MeasureTheory in
theorem UpperTheory.V.Af.Rs.tBdd :
    UpperTheory.V.Af.Rs.FdFin → UpperTheory.V.Af.Rs.ZDiff → UpperTheory.V.Af.Rs.ZInt → UpperTheory.V.Af.Rs.TBdd := by
  intro hF hD _ L _ G hG h0
  obtain ⟨C, hC⟩ := hD L
  obtain ⟨-, D, hD⟩ := hG
  refine ⟨(∑ _v : Fin 2 → ZMod L, |C| * D) * (volume : Measure UpperHalfPlane).real ModularGroup.fd, fun s hs => ?_⟩
  unfold UpperTheory.V.Af.Rs.TT
  refine norm_setIntegral_le_of_norm_le_const hF.2 fun z hz => ?_
  have hy : 0 < z.im := z.im_pos
  have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have hy2 : 1 / 2 ≤ z.im := by nlinarith
  have he : ∑ v, G v z * (UpperTheory.V.Af.Rs.Zc L v s z : ℂ) =
      ∑ v, G v z * ((UpperTheory.V.Af.Rs.Zc L v s z - UpperTheory.V.Af.Rs.Zc L 0 s z : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h0 z, zero_mul, sub_zero]
  rw [he]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := hC v 0 s hs z hz
  have h2 := hD v z hy2
  have h4 : C * z.im ^ 3 ≤ |C| * z.im ^ 3 := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  calc _ ≤ ‖G v z‖ * (|C| * z.im ^ 3) := mul_le_mul_of_nonneg_left (h1.trans h4) (norm_nonneg _)
    _ = |C| * (‖G v z‖ * z.im ^ 3) := by ring
    _ ≤ |C| * D := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
end

