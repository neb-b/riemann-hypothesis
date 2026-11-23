module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PHomogeneousDifferenceLinear
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0312
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0329

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootCancelPowEqSelfAcrisGaussNorm
section
noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

theorem rootCancel_radius (l : ℕ) [Fact l.Prime] {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (l : ℝ)⁻¹ ≤ (l : ℝ) ^ (-r) ∧ (l : ℝ) ^ (-r) < 1 := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  constructor
  · rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hl.le (by linarith)
  · exact Real.rpow_lt_one_of_one_lt_of_neg hl (by linarith)

theorem vr_iterate_φc (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l) (hx : x ≠ 0) :
    ∀ k : ℕ, ∀ r ∈ Set.Ioc (0 : ℝ) 1,
      (φc l)^[k] x ≠ 0 ∧ vr l r ((φc l)^[k] x) = (l : ℝ) ^ k * vr l (r / (l : ℝ) ^ k) x := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  intro k
  induction k with
  | zero => intro r _; simp [hx]
  | succ k ih =>
    intro r hr
    have hrl : r / l ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨div_pos hr.1 (by linarith), (div_le_one (by linarith)).2 (by linarith [hr.2])⟩
    obtain ⟨h1, h2⟩ := ih (r / l) hrl
    have V := (_root_.GlobalTheory.PMon.Gauss.vr_laws l r hr.1 hr.2).2.1 _ h1
    refine ⟨by rw [Function.iterate_succ_apply']; exact V.1, ?_⟩
    rw [Function.iterate_succ_apply', V.2, h2, div_div, pow_succ, mul_comm ((l : ℝ) ^ k) (l : ℝ)]
    ring

theorem vr_prod_range (l : ℕ) [Fact l.Prime] (x : ℕ → Formalism.Per.Acris l) (hx : ∀ i, x i ≠ 0)
    (h10 : (1 : Formalism.Per.Acris l) ≠ 0) :
    ∀ n : ℕ, (∏ i ∈ Finset.range n, x i) ≠ 0 ∧
      ∀ r ∈ Set.Ioc (0 : ℝ) 1, vr l r (∏ i ∈ Finset.range n, x i) = ∑ i ∈ Finset.range n, vr l r (x i) := by
  intro n
  induction n with
  | zero =>
    refine ⟨by simpa using h10, fun r hr => ?_⟩
    have hρ := rootCancel_radius l hr.1 hr.2
    simp [vr, (gC_basic_values l _ hρ.1 hρ.2).1]
  | succ n ih =>
    have hne : (∏ i ∈ Finset.range (n + 1), x i) ≠ 0 := by
      rw [Finset.prod_range_succ]
      intro h0
      rcases _root_.GlobalTheory.PMon.Gauss.acris_mul_eq_zero l _ _ h0 with h | h
      · exact ih.1 h
      · exact hx n h
    refine ⟨hne, fun r hr => ?_⟩
    rw [Finset.prod_range_succ, Finset.sum_range_succ, (_root_.GlobalTheory.PMon.Gauss.vr_laws l r hr.1 hr.2).1 _ _ ih.1 (hx n),
      ih.2 r hr]

theorem root_cancel_pow_eq_self : ∀ (l : ℕ) [Fact l.Prime] (h s : ℕ), s < h → ∀ (w w' : Formalism.Per.Acris l) (ζ : Formalism.Per.Fl l) (o : ℕ) (ρ₀ : ℝ), (φc l)^[h] w' = (l : Formalism.Per.Acris l) ^ s * w' → w' ≠ 0 → φc l w * w' = w * φc l w' → (∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = gC l ρ w') → 0 < o → ζ ^ (l ^ o) = ζ → ζ ≠ 0 → (l : ℝ)⁻¹ ≤ ρ₀ → ρ₀ < 1 → gC l ρ₀ (w - tc l ζ * w') < gC l ρ₀ w' → ζ ^ l = ζ := by
  intro l _ h s hsh w w' ζ o ρ₀ hh hw' hφ hnorm ho hζo hζ0 hρ₀1 hρ₀2 hlt
  classical
  have hlN : 1 < l := (Fact.out : l.Prime).one_lt
  have hl : (1 : ℝ) < l := by exact_mod_cast hlN
  have hl0 : (0 : ℝ) < l := by linarith
  set F : Formalism.Per.Fl l → Formalism.Per.Fl l := fun y => y ^ l with hF
  have hFit : ∀ i, F^[i] ζ = ζ ^ (l ^ i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [Function.iterate_succ_apply', ih, hF, pow_succ, pow_mul]
  have hper : Function.IsPeriodicPt F o ζ := by
    show F^[o] ζ = ζ
    rw [hFit]; exact hζo
  set o' := Function.minimalPeriod F ζ with ho'
  have ho'pos : 0 < o' := Function.IsPeriodicPt.minimalPeriod_pos ho hper
  have hz_eq : ∀ i j, F^[i] ζ = F^[j] ζ → i % o' = j % o' := by
    intro i j hij
    rw [← Function.iterate_mod_minimalPeriod_eq (n := i), ← Function.iterate_mod_minimalPeriod_eq (n := j)] at hij
    exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod (Nat.mod_lt _ ho'pos) (Nat.mod_lt _ ho'pos)).1 hij
  have hmod1 : ∀ i, (i + 1) % o' = i % o' → o' = 1 := by
    intro i hi
    have hmod : (i + 1) % o' = (i + 0) % o' := by rw [add_zero]; exact hi
    have h10 : 1 ≡ 0 [MOD o'] := Nat.ModEq.add_left_cancel' i hmod
    exact Nat.dvd_one.mp (Nat.modEq_zero_iff_dvd.mp h10)
  suffices hsuff : o' = 1 by
    have := Function.iterate_minimalPeriod (f := F) (x := ζ)
    rw [← ho', hsuff] at this
    simpa [hF] using this

  have hz0 : ∀ i, F^[i] ζ ≠ 0 := fun i => by rw [hFit]; exact pow_ne_zero _ hζ0
  have hzfix : ∀ i, (F^[i] ζ) ^ (l ^ o) = F^[i] ζ := by
    intro i
    rw [hFit, ← pow_mul, mul_comm, pow_mul, hζo]
  have hzsucc : ∀ i, F^[i + 1] ζ = (F^[i] ζ) ^ l := fun i => Function.iterate_succ_apply' _ _ _
  have hzper : F^[o'] ζ = F^[0] ζ := Function.iterate_minimalPeriod

  have hG : ∀ ρ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → IsGauss l ρ (gC l ρ) := fun ρ h0 h1 => isGauss_gC_target l ρ h0 h1
  have htc1 : ∀ ρ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → ∀ i, gC l ρ (tc l (F^[i] ζ)) = 1 := by
    intro ρ h0 h1 i
    rw [(gC_basic_values l ρ h0 h1).2.2.2.1]
    have h00 : (0 : Formalism.Per.Fl l) ^ (l ^ o) = 0 := zero_pow (pow_ne_zero _ (by omega))
    have := GlobalTheory.TiltAbs.norm_untilt_sub_eq_one_of_pow_fixed l o _ 0 ho (hzfix i) h00 (hz0 i)
    simpa using this
  set x : ℕ → Formalism.Per.Acris l := fun i => w - tc l (F^[i] ζ) * w' with hx
  have hfrob : ∀ i, φc l (x i) * w' = x (i + 1) * φc l w' := by
    intro i
    simp only [hx, map_sub, map_mul, frob_teich, hzsucc]
    linear_combination hφ

  by_cases hA : ∃ i, x i = 0
  · obtain ⟨i, hi⟩ := hA
    have hwi : w = tc l (F^[i] ζ) * w' := sub_eq_zero.1 hi
    rw [hwi] at hφ
    have hfix := _root_.GlobalTheory.PMon.Gauss.teich_eq_of_phi_ratio l w' (F^[i] ζ) hw' hφ
    apply hmod1 i
    apply hz_eq
    rw [hzsucc]; exact hfix
  push_neg at hA

  have h10 : (1 : Formalism.Per.Acris l) ≠ 0 := fun h1 => hw' (by rw [← one_mul w', h1, zero_mul])
  have hrad := fun r (hr : r ∈ Set.Ioc (0 : ℝ) 1) => rootCancel_radius l hr.1 hr.2
  have hpos : ∀ y : Formalism.Per.Acris l, y ≠ 0 → ∀ r ∈ Set.Ioc (0 : ℝ) 1, 0 < gC l ((l : ℝ) ^ (-r)) y :=
    fun y hy r hr => _root_.GlobalTheory.PMon.Gauss.gC_pos_target l y hy _ (hrad r hr).1 (hrad r hr).2
  have hmulw : ∀ r ∈ Set.Ioc (0 : ℝ) 1, ∀ i,
      gC l ((l : ℝ) ^ (-r)) (tc l (F^[i] ζ) * w') = gC l ((l : ℝ) ^ (-r)) w' := by
    intro r hr i
    rw [(hG _ (hrad r hr).1 (hrad r hr).2).2.2.2.1, htc1 _ (hrad r hr).1 (hrad r hr).2, one_mul]
  have hxle : ∀ r ∈ Set.Ioc (0 : ℝ) 1, ∀ i, gC l ((l : ℝ) ^ (-r)) (x i) ≤ gC l ((l : ℝ) ^ (-r)) w' := by
    intro r hr i
    have hGr := hG _ (hrad r hr).1 (hrad r hr).2
    have := hGr.2.1 w (-(tc l (F^[i] ζ) * w'))
    rw [← sub_eq_add_neg, hGr.2.2.1, hmulw r hr i, hnorm _ (hrad r hr).1 (hrad r hr).2, max_self] at this
    exact this
  set fv : ℕ → ℝ → ℝ := fun i r => vr l r (x i) - vr l r w' with hfv
  have hfv_pos : ∀ r ∈ Set.Ioc (0 : ℝ) 1, ∀ i,
      0 < fv i r ↔ gC l ((l : ℝ) ^ (-r)) (x i) < gC l ((l : ℝ) ^ (-r)) w' := by
    intro r hr i
    simp only [hfv, vr, sub_pos, neg_lt_neg_iff]
    exact Real.logb_lt_logb_iff hl (hpos _ (hA i) r hr) (hpos _ hw' r hr)
  have hfv_nonneg : ∀ i, ∀ r ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ fv i r := by
    intro i r hr
    simp only [hfv, vr, sub_nonneg, neg_le_neg_iff]
    exact Real.logb_le_logb_of_le hl (hpos _ (hA i) r hr) (hxle r hr i)
  have hfv_cont : ∀ i, ContinuousOn (fv i) (Set.Ioc 0 1) := fun i =>
    ((_root_.GlobalTheory.PMon.Gauss.vr_concave_cont_rightSlope l _ (hA i)).2.1).sub (_root_.GlobalTheory.PMon.Gauss.vr_concave_cont_rightSlope l _ hw').2.1
  have hfv_class : ∀ i j, ∀ r ∈ Set.Ioc (0 : ℝ) 1, 0 < fv i r → 0 < fv j r → i % o' = j % o' := by
    intro i j r hr hi hj
    by_cases hzz : F^[i] ζ = F^[j] ζ
    · exact hz_eq _ _ hzz
    exfalso
    have hGr := hG _ (hrad r hr).1 (hrad r hr).2
    have hd : x j - x i = (tc l (F^[i] ζ) - tc l (F^[j] ζ)) * w' := by simp only [hx]; ring
    have hsep := GlobalTheory.TiltAbs.norm_untilt_sub_eq_one_of_pow_fixed l o _ _ ho (hzfix i) (hzfix j) hzz
    have h1 := _root_.GlobalTheory.PMon.Gauss.gC_teich_sub_eq_one l _ _ hsep _ (hrad r hr).1 (hrad r hr).2
    have hle := hGr.2.1 (x j) (-(x i))
    rw [← sub_eq_add_neg, hGr.2.2.1, hd, hGr.2.2.2.1, h1, one_mul] at hle
    have := (hfv_pos r hr i).1 hi
    have := (hfv_pos r hr j).1 hj
    have := le_max_iff.1 hle
    rcases this with h | h <;> linarith
  have hfv_shift : ∀ i r, 0 < r → r ≤ 1 / (l : ℝ) → fv (i + 1) ((l : ℝ) * r) = (l : ℝ) * fv i r := by
    intro i r hr0 hr1
    have hlr : (l : ℝ) * r ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨by positivity, by rw [le_div_iff₀ hl0] at hr1; linarith⟩
    have V := _root_.GlobalTheory.PMon.Gauss.vr_laws l _ hlr.1 hlr.2
    have hrr : (l : ℝ) * r / l = r := by field_simp
    have e := congrArg (vr l ((l : ℝ) * r)) (hfrob i)
    rw [V.1 _ _ (V.2.1 _ (hA i)).1 hw', V.1 _ _ (hA (i + 1)) (V.2.1 _ hw').1, (V.2.1 _ (hA i)).2,
      (V.2.1 _ hw').2, hrr] at e
    simp only [hfv]
    linarith

  have hper_x : x o' = x 0 := by simp only [hx, hzper]
  obtain ⟨hWne, hWvr⟩ := vr_prod_range l x hA h10 o'
  set W := ∏ i ∈ Finset.range o', x i with hW
  have hsum : ∀ r ∈ Set.Ioc (0 : ℝ) 1, vr l r W - (o' : ℝ) * vr l r w' = ∑ i ∈ Finset.range o', fv i r := by
    intro r hr
    simp only [hfv, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hWvr r hr]
  have hB : ∀ r ∈ Set.Ioc (0 : ℝ) 1, (l : ℝ) ^ h * vr l (r / (l : ℝ) ^ h) w' = vr l r w' + s * r := by
    intro r hr
    have e := (vr_iterate_φc l w' hw' h r hr).2
    rw [hh, (_root_.GlobalTheory.PMon.Gauss.vr_laws l r hr.1 hr.2).2.2.1 w' s hw'] at e
    linarith
  have hAB : ∀ r ∈ Set.Ioc (0 : ℝ) (1 / l), vr l ((l : ℝ) * r) W - (o' : ℝ) * vr l ((l : ℝ) * r) w' =
      (l : ℝ) * (vr l r W - (o' : ℝ) * vr l r w') := by
    intro r hr
    have hr1 : r ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨hr.1, hr.2.trans (by rw [div_le_one hl0]; exact hl.le)⟩
    have hlr : (l : ℝ) * r ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨mul_pos hl0 hr.1, by have := hr.2; rw [le_div_iff₀ hl0] at this; linarith⟩
    rw [hsum _ hlr, hsum _ hr1, Finset.mul_sum]
    have hcyc : ∑ i ∈ Finset.range o', fv i ((l : ℝ) * r) = ∑ i ∈ Finset.range o', fv (i + 1) ((l : ℝ) * r) := by
      have e1 := Finset.sum_range_succ (fun i => fv i ((l : ℝ) * r)) o'
      have e2 := Finset.sum_range_succ' (fun i => fv i ((l : ℝ) * r)) o'
      have e3 : fv o' ((l : ℝ) * r) = fv 0 ((l : ℝ) * r) := by simp only [hfv, hper_x]
      linarith
    rw [hcyc]
    exact Finset.sum_congr rfl (fun i _ => hfv_shift i r hr.1 hr.2)
  obtain ⟨n, hn⟩ := _root_.GlobalTheory.PHomCalc.p_homogeneous_difference_linear l h s o' hlN hsh ho'pos (fun r => vr l r W) (fun r => vr l r w')
    (_root_.GlobalTheory.PMon.Gauss.vr_concave_cont_rightSlope l _ hWne).1 (_root_.GlobalTheory.PMon.Gauss.vr_concave_cont_rightSlope l _ hw').1 (_root_.GlobalTheory.PMon.Gauss.vr_concave_cont_rightSlope l _ hWne).2.1 (_root_.GlobalTheory.PMon.Gauss.vr_concave_cont_rightSlope l _ hw').2.1
    (_root_.GlobalTheory.PMon.Gauss.vr_concave_cont_rightSlope l _ hWne).2.2 (_root_.GlobalTheory.PMon.Gauss.vr_concave_cont_rightSlope l _ hw').2.2 hB hAB

  set r₀ := -Real.logb l ρ₀ with hr₀
  have hρ₀pos : 0 < ρ₀ := lt_of_lt_of_le (inv_pos.2 hl0) hρ₀1
  have hr₀ρ : (l : ℝ) ^ (-r₀) = ρ₀ := by rw [hr₀, neg_neg, Real.rpow_logb hl0 hl.ne' hρ₀pos]
  have hr₀mem : r₀ ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor
    · rw [hr₀, neg_pos]; exact Real.logb_neg hl hρ₀pos hρ₀2
    · rw [hr₀, neg_le]
      have := Real.logb_le_logb_of_le hl (inv_pos.2 hl0) hρ₀1
      rwa [Real.logb_inv, Real.logb_self_eq_one hl] at this
  have hf0 : 0 < fv 0 r₀ := by
    rw [hfv_pos r₀ hr₀mem 0, hr₀ρ]
    simpa [hx] using hlt
  have hnpos : (0 : ℝ) < n := by
    have hs := hsum r₀ hr₀mem
    rw [hn r₀ hr₀mem] at hs
    have : fv 0 r₀ ≤ ∑ i ∈ Finset.range o', fv i r₀ :=
      Finset.single_le_sum (fun i _ => hfv_nonneg i r₀ hr₀mem) (Finset.mem_range.2 ho'pos)
    nlinarith [hr₀mem.1]
  have hcover : ∀ r ∈ Set.Ioc (0 : ℝ) 1, ∃ i, 0 < fv i r := by
    intro r hr
    by_contra H
    push_neg at H
    have hs := hsum r hr
    rw [hn r hr] at hs
    have : ∑ i ∈ Finset.range o', fv i r ≤ 0 := Finset.sum_nonpos (fun i _ => H i)
    nlinarith [hr.1]
  exact GlobalTheory.orbit_class_trivial o' (l : ℝ) fv ho'pos hl hfv_cont hfv_nonneg hfv_class hcover
    (fun i r hr0 hr1 hi => by rw [hfv_shift i r hr0 hr1]; positivity)

end GlobalTheory.PMon.Gauss

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelAllEquivSel
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

noncomputable section

open Pointwise

namespace GlobalTheory.SelInf

section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem conj_Ine {A : ValuationSubring Ω} {g σ : G F Ω} (hσ : σ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Ine (F := F) A := by
  have m : ∀ y : Ω, y ∈ g • A ↔ (g⁻¹ : G F Ω) y ∈ A := fun y => by
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  have m' : ∀ y : Ω, (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : G F Ω) y) < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', m, m, map_inv₀,
      map_eq_zero_iff _ (g⁻¹ : G F Ω).injective]
  have c : ∀ x : Ω, (g⁻¹ : G F Ω) (g x) = x := fun x => by
    show (g⁻¹ * g) x = x
    simp
  refine ⟨?_, fun x hx => ?_⟩
  · have h : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h, inv_smul_smul]
  · have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff, m, c]
      exact (A.valuation_le_one_iff x).1 hx
    have h := (m' _).1 (hσ.2 _ hx')
    rw [map_sub, c] at h
    exact h

variable {R R' : Type} [CommRing R] [CommRing R'] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [DiscreteTopology M] {M' : Type} [AddCommGroup M'] [Module R' M'] [TopologicalSpace M'] [DiscreteTopology M']
  {S : Set (HeightOneSpectrum (𝓞 F))} {ρ : Representation R (G F Ω) M} {ρS : Representation R' (GS Ω S) M'}
  (e : M ≃+ M') (he : ∀ g m, e (ρ g m) = ρS (toGS Ω S g) (e m))


include he in
theorem triv_of_mem {σ : G F Ω} (hσ : σ ∈ NS Ω S) (m : M) : ρ σ m = m := by
  apply e.injective
  have : toGS Ω S σ = 1 := (QuotientGroup.eq_one_iff σ).2 hσ
  rw [he, this, map_one]
  rfl

def infZ (z : Z1 ρS) : Z1 ρ :=
  ⟨fun g => e.symm (z.1 (toGS Ω S g)),
    (continuous_of_discreteTopology (f := e.symm)).comp (z.2.1.comp (continuous_toGS Ω S)), fun g h => by
      apply e.injective
      beta_reduce
      rw [map_add (f := _), he, map_mul, z.2.2]
      simp⟩

theorem infZ_apply (z : Z1 ρS) (g : G F Ω) : (infZ e he z).1 g = e.symm (z.1 (toGS Ω S g)) := rfl

theorem mk_infZ_eq_iff (z z' : Z1 ρS) :
    (Submodule.Quotient.mk (infZ e he z) : H1 ρ) = Submodule.Quotient.mk (infZ e he z') ↔
      (Submodule.Quotient.mk z : H1 ρS) = Submodule.Quotient.mk z' := by
  rw [Submodule.Quotient.eq, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.mem_comap, mem_coboundaries1, mem_coboundaries1]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨e m, fun g => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g', toGS Ω S g' = g := QuotientGroup.mk'_surjective _ g
    have h1 : e.symm (z.1 (toGS Ω S g)) - e.symm (z'.1 (toGS Ω S g)) = ρ g m - m := hm g
    have h2 := congrArg e h1
    rw [map_sub, map_sub, he, e.apply_symm_apply, e.apply_symm_apply] at h2
    exact h2
  · rintro ⟨m, hm⟩
    refine ⟨e.symm m, fun g => ?_⟩
    have h1 : z.1 (toGS Ω S g) - z'.1 (toGS Ω S g) = ρS (toGS Ω S g) m - m := hm (toGS Ω S g)
    change e.symm (z.1 (toGS Ω S g)) - e.symm (z'.1 (toGS Ω S g)) = _
    apply e.injective
    rw [map_sub, map_sub, he, e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply]
    exact h1

def infH : H1 ρS → H1 ρ := fun x => Submodule.Quotient.mk (infZ e he x.out)

theorem infH_mk (z : Z1 ρS) : infH e he (Submodule.Quotient.mk z) = Submodule.Quotient.mk (infZ e he z) :=
  (mk_infZ_eq_iff e he _ _).2 (Quotient.out_eq' _)

theorem infH_injective : Function.Injective (infH e he) := by
  intro x y h
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [infH_mk, infH_mk] at h
  exact (mk_infZ_eq_iff e he _ _).1 h

theorem Ine_le_NS {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) {A : ValuationSubring Ω} (hA : IsPlaceOver A v)
    {σ : G F Ω} (hσ : σ ∈ Ine (F := F) A) : σ ∈ NS Ω S := by
  apply Subgroup.le_topologicalClosure
  apply Subgroup.subset_normalClosure
  simp only [Set.mem_iUnion]
  exact ⟨v, hv, A, hA, hσ⟩

theorem z_one {Γ : Type} [Group Γ] [TopologicalSpace Γ] {π : Representation R Γ M} (z : Z1 π) : z.1 1 = 0 := by
  have := z.2.2 1 1
  simpa using this


include he in
theorem mem_unrAt_iff {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) {A : ValuationSubring Ω} (hA : IsPlaceOver A v)
    (z : Z1 ρ) :
    resH1 ρ (Dec (F := F) A).subtype continuous_subtype_val (Submodule.Quotient.mk z) ∈ Formalism.GaloisCohomology.unrAt ρ A ↔
      ∀ σ ∈ Ine (F := F) A, z.1 σ = 0 := by
  have h0 : resH1 ρ (Dec (F := F) A).subtype continuous_subtype_val (Submodule.Quotient.mk z) ∈ Formalism.GaloisCohomology.unrAt ρ A ↔
      (Submodule.Quotient.mk (restrictCocycles1 _ ((Ine (F := F) A).subgroupOf (Dec (F := F) A)).subtype continuous_subtype_val
        (restrictCocycles1 ρ (Dec (F := F) A).subtype continuous_subtype_val z)) : H1 _) = 0 := Iff.rfl
  rw [h0, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, mem_coboundaries1]
  constructor
  · rintro ⟨m, hm⟩ σ hσ
    have h1 : z.1 σ = ρ σ m - m := hm ⟨⟨σ, Ine_le_Dec A hσ⟩, hσ⟩
    rw [h1, triv_of_mem e he (Ine_le_NS hv hA hσ), sub_self]
  · intro h
    refine ⟨0, fun g => ?_⟩
    rw [map_zero, sub_zero]
    exact h g.1.1 g.2


include he in
theorem vanish_NS [IsAlgClosure F Ω] (A : Formalism.GaloisCohomology.Places F Ω) (z : Z1 ρ)
    (h : ∀ v ∉ S, ∀ σ ∈ Ine (F := F) (A.1 v), z.1 σ = 0) : ∀ σ ∈ NS Ω S, z.1 σ = 0 := by
  have hz := z.2.2
  have hinv : ∀ g, z.1 g + ρ g (z.1 g⁻¹) = 0 := fun g => by
    rw [← hz, mul_inv_cancel, z_one]
  let K : Subgroup (G F Ω) :=
    { carrier := {g | g ∈ NS Ω S ∧ z.1 g = 0}
      one_mem' := ⟨one_mem _, z_one z⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        exact ⟨mul_mem ha hb, by rw [hz, ha', hb', map_zero, add_zero]⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, ?_⟩
        have := hinv a
        rwa [ha', zero_add, triv_of_mem e he ha] at this }
  have hK : K.Normal := ⟨by
    rintro a ⟨ha, ha'⟩ g
    refine ⟨(normal_NS S).conj_mem a ha g, ?_⟩
    rw [mul_assoc, hz, hz, ha', zero_add, triv_of_mem e he ha, hinv]⟩
  have hc : IsClosed (K : Set (G F Ω)) :=
    (isClosed_NS Ω S).inter ((isClosed_discrete {(0 : M)}).preimage z.2.1)
  have hle : Subgroup.normalClosure
      (⋃ v ∈ Sᶜ, ⋃ A ∈ {A : ValuationSubring (Ω) | IsPlaceOver A v}, Inertia (F := F) A) ≤ K := by
    apply Subgroup.normalClosure_le_normal
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ
    obtain ⟨v, hv, B, hB, hτ⟩ := hτ
    obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) (A.2 v) hB
    have h1 := conj_Ine (F := F) hτ
    have h2 : g⁻¹ * τ * g ∈ K := ⟨Ine_le_NS hv (A.2 v) h1, h v hv _ h1⟩
    have h3 := hK.conj_mem _ h2 g
    have h4 : g * (g⁻¹ * τ * g) * g⁻¹ = τ := by group
    rwa [h4] at h3
  intro σ hσ
  exact (Subgroup.topologicalClosure_minimal _ hle hc hσ).2

theorem exists_infZ (z : Z1 ρ) (h : ∀ σ ∈ NS Ω S, z.1 σ = 0) : ∃ z', infZ e he z' = z := by
  have hz := z.2.2
  have hw : ∀ a b : G F Ω, (QuotientGroup.leftRel (NS Ω S)) a b → e (z.1 a) = e (z.1 b) := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    have : z.1 (a * (a⁻¹ * b)) = z.1 a := by rw [hz, h _ hab, map_zero, add_zero]
    rw [← this, mul_inv_cancel_left]
  refine ⟨⟨Quotient.lift (fun g => e (z.1 g)) hw,
    Continuous.quotient_lift ((continuous_of_discreteTopology (f := e)).comp z.2.1) hw, fun g g' => ?_⟩, ?_⟩
  · obtain ⟨g, rfl⟩ : ∃ g', toGS Ω S g' = g := QuotientGroup.mk'_surjective _ g
    obtain ⟨g', rfl⟩ : ∃ g'', toGS Ω S g'' = g' := QuotientGroup.mk'_surjective _ g'
    rw [← map_mul]
    change e (z.1 (g * g')) = e (z.1 g) + ρS (toGS Ω S g) (e (z.1 g'))
    rw [hz, map_add (f := _), he]
  · exact Subtype.ext (funext fun g => e.symm_apply_apply (z.1 g))

end

theorem selAll_equiv_sel : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (R R' : Type) [CommRing R] [CommRing R'] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (M' : Type) [AddCommGroup M'] [Module R' M'] [TopologicalSpace M'] [DiscreteTopology M'] (S : Finset (HeightOneSpectrum (𝓞 F))) (A : Formalism.GaloisCohomology.Places F Ω) (ρ : Representation R (G F Ω) M) (ρS : Representation R' (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M') (e : M ≃+ M'), ContAction ρ → (∀ g m, e (ρ g m) = ρS (toGS Ω _ g) (e m)) → ∀ (L : ∀ v, Submodule R (H1 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) (LS : LocCond ρS (locFam S (fun v => A.1 v.1))), (∀ v ∉ S, L v = Formalism.GaloisCohomology.unrAt ρ (A.1 v)) → (∀ (v : S) (z : Z1 (ρ.comp (Dec (F := F) (A.1 v.1)).subtype)) (z' : Z1 (ρS.comp (locFam S (fun v => A.1 v.1) v))), (∀ g, z'.1 g = e (z.1 g)) → (Submodule.Quotient.mk z ∈ L v.1 ↔ Submodule.Quotient.mk z' ∈ LS v)) → Nonempty (Formalism.GaloisCohomology.SelAll ρ A L ≃ Sel ρS (locFam S (fun v => A.1 v.1)) (continuous_locFam S _) LS) := by
  intro F Ω _ _ _ _ _ R R' _ _ M _ _ _ _ M' _ _ _ _ S A ρ ρS e _ he L LS hL hLS
  have key : ∀ (z : Z1 ρS) (v : S),
      resH1 ρ (Dec (F := F) (A.1 v.1)).subtype continuous_subtype_val (Submodule.Quotient.mk (infZ e he z)) ∈ L v.1 ↔
      resH1 ρS (locFam S (fun v => A.1 v.1) v) (continuous_locFam S _ v) (Submodule.Quotient.mk z) ∈ LS v :=
    fun z v => hLS v (restrictCocycles1 ρ (Dec (F := F) (A.1 v.1)).subtype continuous_subtype_val (infZ e he z))
      (restrictCocycles1 ρS (locFam S (fun v => A.1 v.1) v) (continuous_locFam S _ v) z)
      (fun g => (e.apply_symm_apply _).symm)
  have hall : ∀ y : H1 ρ, y ∈ Formalism.GaloisCohomology.SelAll ρ A L ↔
      ∀ v, resH1 ρ (Dec (F := F) (A.1 v)).subtype continuous_subtype_val y ∈ L v :=
    fun y => mem_Sel ρ (fun v => (Dec (F := F) (A.1 v)).subtype) (fun _ => continuous_subtype_val) L y
  have hmem : ∀ x : H1 ρS, x ∈ Sel ρS (locFam S (fun v => A.1 v.1)) (continuous_locFam S _) LS ↔
      infH e he x ∈ Formalism.GaloisCohomology.SelAll ρ A L := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [infH_mk, hall, mem_Sel]
    constructor
    · intro h v
      by_cases hv : v ∈ S
      · exact (key z ⟨v, hv⟩).2 (h ⟨v, hv⟩)
      · rw [hL v hv, mem_unrAt_iff e he (by simpa using hv) (A.2 v)]
        intro σ hσ
        have : toGS Ω (S : Set (HeightOneSpectrum (𝓞 F))) σ = 1 :=
          (QuotientGroup.eq_one_iff σ).2 (Ine_le_NS (by simpa using hv) (A.2 v) hσ)
        rw [infZ_apply, this, z_one, map_zero]
    · intro h v
      exact (key z v).1 (h v.1)
  refine ⟨(Equiv.ofBijective (fun x : Sel ρS (locFam S (fun v => A.1 v.1)) (continuous_locFam S _) LS =>
    (⟨infH e he x.1, (hmem _).1 x.2⟩ : Formalism.GaloisCohomology.SelAll ρ A L)) ⟨?_, ?_⟩).symm⟩
  · intro x y h
    exact Subtype.ext (infH_injective e he (congrArg Subtype.val h))
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hy' := (hall _).1 hy
    obtain ⟨z', rfl⟩ := exists_infZ e he z (vanish_NS e he A z fun v hv => by
      have hv' : v ∉ S := by simpa using hv
      have := hy' v
      rwa [hL v hv', mem_unrAt_iff e he hv (A.2 v)] at this)
    exact ⟨⟨Submodule.Quotient.mk z', (hmem _).2 (by rw [infH_mk]; exact hy)⟩, Subtype.ext (infH_mk e he z')⟩

end GlobalTheory.SelInf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiedTateFilQuot
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TateFilQuotTied

theorem tied_tate_fil_quot : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∀ K : FinExt l, Formalism.MainNotions.LocalSituation.TateFilteredInvariants (P.PD K) := by
  intro l _ P AI TT K LL _ _ _ O _ _ hO A hA a b z hz hg
  haveI := hO.2.1
  exact GlobalTheory.TateFilQuot.tied_invariant_mod l P AI TT K LL A.V A.ρ hA a b z hz hg

end GlobalTheory.TateFilQuotTied
end

