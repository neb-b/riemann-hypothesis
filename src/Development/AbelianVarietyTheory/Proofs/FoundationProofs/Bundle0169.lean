module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReducesOfDetEvMEqZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0154

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddWeightModularCuspDimensionLowerBound
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem neg_one_not_mem_Gamma1 {N : ℕ} (hN : 5 ≤ N) : (-1 : SL(2, ℤ)) ∉ CongruenceSubgroup.Gamma1 N := by
  intro h
  rw [CongruenceSubgroup.Gamma1_mem] at h
  have h1 : ((2 : ℕ) : ZMod N) = 0 := by
    have := h.1
    simp at this
    push_cast
    linear_combination -this
  rw [ZMod.natCast_eq_zero_iff] at h1
  have := Nat.le_of_dvd (by norm_num) h1
  omega

theorem neg_one_mem_Gamma {M : ℕ} (h0 : 0 < M) (hM : M < 3) : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem]
  interval_cases M <;> simp <;> decide

theorem exists_frame (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (hM : 0 < M) (hΓ : CongruenceSubgroup.Gamma M ≤ Γ)
    (h1 : (-1 : SL(2, ℤ)) ∉ Γ) {r : ℕ} {s : Fin r → SL(2, ℤ)} (hs : IsReps Γ s) :
    ∃ (w : Fin r → ℤ) (F G : Fin r → ℍ → ℂ), (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) ∧
      (∀ τ, (evM s w F τ).det ≠ 0) ∧ (∀ j, IsCF Γ (12 - w j) (G j)) ∧
      ∀ τ, (evM s (fun j => 12 - w j) G τ).det ≠ 0 := by
  have hfi := finiteIndex_of_Gamma_le hM hΓ
  have hM3 : 3 ≤ M := by
    by_contra h
    exact h1 (hΓ (neg_one_mem_Gamma hM (by omega)))
  obtain ⟨τ₀, hτ₀⟩ := _root_.GlobalTheory.CosetEval.evals_independent M hM (_root_.GlobalTheory.EisSep.exists_isMF_slash_ne M hM3)
  obtain ⟨w₀, F₀, hF₀, hd₀⟩ := GlobalTheory.T.exists_odd_weight_frame_det_ne_zero M Γ r s τ₀ hM hΓ h1 hs hτ₀
  obtain ⟨w, F, hF, -, hred⟩ := _root_.GlobalTheory.OddFrame.descent Γ r s w₀ F₀ hfi hF₀ ⟨τ₀, hd₀⟩
  have hdet : ∀ τ, (evM s w F τ).det ≠ 0 := fun τ h => hred (_root_.GlobalTheory.OddFrame.reduces_of_det_evM_eq_zero Γ r s w F τ hs hF h)
  have hlead : (leadM M s w F).det ≠ 0 := fun h => hred (_root_.GlobalTheory.OddFrame.reduces_of_det_leadM_eq_zero M Γ r s w F hM hΓ hs hF h)
  obtain ⟨U, hU1, hU2⟩ := GlobalTheory.T.exists_tendsto_slashEvaluationMatrix_mul M Γ r s w F hM hΓ hs hF hlead
  obtain ⟨G, hG, hGd⟩ := GlobalTheory.T.exists_dual_oddFrame_cuspForms Γ r s w F h1 hs hF hdet (GlobalTheory.T.tendsto_smul_inv_of_mul_tendsto_invertible_matrix r _ U _ _ hlead hU1 hU2)
  exact ⟨w, F, G, hF, hdet, hG, hGd⟩

theorem levelOne_pair (k j : ℤ) (hk : Odd k) (hj : Odd j) :
    2 * k - 2 + 4 * (if k % 3 = 0 then 1 else if k % 3 = 2 then -1 else 0) * (3 * (if (3 : ℤ) ∣ j then 1 else 0) - 1)
      ≤ 12 * ((Module.finrank ℂ (ModularForm 𝒮ℒ (k - j)) : ℤ) +
        (Module.finrank ℂ (ModularForm 𝒮ℒ (k - (12 - j))) : ℤ)) := by
  have ha := _root_.GlobalTheory.OddFrame.levelOne_twelve_mul_finrank_lower_bound (k - j) (hk.sub_odd hj)
  have hb := _root_.GlobalTheory.OddFrame.levelOne_twelve_mul_finrank_lower_bound (k - (12 - j)) (hk.sub_odd (Even.sub_odd (by decide) hj))
  rw [Int.odd_iff] at hk hj
  generalize (Module.finrank ℂ (ModularForm 𝒮ℒ (k - j)) : ℤ) = a at *
  generalize (Module.finrank ℂ (ModularForm 𝒮ℒ (k - (12 - j))) : ℤ) = b at *
  have e4 : ((if (k - j) % 4 = 0 then 1 else -1) : ℤ) + (if (k - (12 - j)) % 4 = 0 then 1 else -1) = 0 := by
    split_ifs <;> omega
  have e3 : ((if (k - j) % 6 = 0 then 1 else if (k - j) % 6 = 2 then -1 else 0) : ℤ) +
      (if (k - (12 - j)) % 6 = 0 then 1 else if (k - (12 - j)) % 6 = 2 then -1 else 0) =
      (if k % 3 = 0 then 1 else if k % 3 = 2 then -1 else 0) * (3 * (if (3 : ℤ) ∣ j then 1 else 0) - 1) := by
    split_ifs <;> omega
  rw [mul_assoc, ← e3]
  linarith

theorem dim_lower_bound : ∀ (N M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 5 ≤ N → 0 < M →
    CongruenceSubgroup.Gamma M ≤ Γ → Γ ≤ CongruenceSubgroup.Gamma1 N → Odd k → 3 ≤ k →
    FiniteDimensional ℂ (ModularForm Γ (k : ℤ)) ∧ FiniteDimensional ℂ (CuspForm Γ (k : ℤ)) ∧
      (k - 1) * Γ.index ≤
        12 * (Module.finrank ℂ (ModularForm Γ (k : ℤ)) + Module.finrank ℂ (CuspForm Γ (k : ℤ))) := by
  intro N M Γ k hN hM hΓ hΓ1 hk hk3
  obtain ⟨hfM, hfS⟩ := _root_.GlobalTheory.OddFrame.finiteDimensional_of_Gamma_le M Γ k hM hΓ
  refine ⟨hfM, hfS, ?_⟩
  have hfi := finiteIndex_of_Gamma_le hM hΓ
  have h1 : (-1 : SL(2, ℤ)) ∉ Γ := fun h => neg_one_not_mem_Gamma1 hN (hΓ1 h)
  obtain ⟨r, s, hs, hr⟩ := _root_.GlobalTheory.OddFrame.reps_index Γ hfi h1
  obtain ⟨w, F, G, hF, hd, hG, hGd⟩ := exists_frame M Γ hM hΓ h1 hs
  have hcM := _root_.GlobalTheory.OddFrame.finrank_sum_le_of_frame Γ r s w F k hfi hfM (fun j => (hF j).2) hd
  have hcS := GlobalTheory.T.sum_finrank_levelOne_le_finrank_cuspForm_of_frame Γ r s (fun j => 12 - w j) G k hfi hfS hG hGd
  have h3 := GlobalTheory.T.three_mul_card_oddFrame_weights_dvd_three N Γ r s w F hN hΓ1 hs hF (hd _)
  have hkz : Odd (k : ℤ) := by exact_mod_cast hk
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun j _ => levelOne_pair k (w j) hkz (hF j).1
  have h3' : ∑ j, (3 * (if (3 : ℤ) ∣ w j then (1 : ℤ) else 0) - 1) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have : (3 : ℤ) * ((Finset.univ.filter fun j => (3 : ℤ) ∣ w j).card : ℤ) = r := by exact_mod_cast h3
    omega
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, h3', ← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_zero, add_zero] at hsum
  have hcM' : ∑ j, (Module.finrank ℂ (ModularForm 𝒮ℒ ((k : ℤ) - w j)) : ℤ) ≤
      Module.finrank ℂ (ModularForm Γ (k : ℤ)) := by exact_mod_cast hcM
  have hcS' : ∑ j, (Module.finrank ℂ (ModularForm 𝒮ℒ ((k : ℤ) - (12 - w j))) : ℤ) ≤
      Module.finrank ℂ (CuspForm Γ (k : ℤ)) := by exact_mod_cast hcS
  rw [← hr]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  zify
  simp only [Nat.add_sub_cancel]
  push_cast at hsum hcM' hcS' ⊢
  nlinarith

end GlobalTheory.OddFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumSelfPosGamma1InterGamma
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem petersson_self_eq (k : ℤ) (f : ℍ → ℂ) (z : ℍ) :
    petersson k f f z = ((‖f z‖ ^ 2 * z.im ^ k : ℝ) : ℂ) := by
  rw [petersson, mul_comm (starRingEnd ℂ (f z)), Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

end GlobalTheory.Hk

namespace GlobalTheory.Hk

theorem pet_self_pos (N l : ℕ) (k : ℤ) (hN : 0 < N) (hl : 0 < l) (f : CuspForm (lev N l) k)
    (hf : f ≠ 0) :
    0 < (pet (lev N l) k ⇑f ⇑f).re ∧ (pet (lev N l) k ⇑f ⇑f).im = 0 := by
  haveI := lev_finiteIndex N l hN hl
  haveI : Finite (SL(2, ℤ) ⧸ lev N l) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (SL(2, ℤ) ⧸ lev N l) := Fintype.ofFinite _
  set r : ℍ → ℝ := fun z => ‖f z‖ ^ 2 * z.im ^ k with hr_def
  have hr0 : ∀ z, 0 ≤ r z := fun z => mul_nonneg (sq_nonneg _) (zpow_nonneg z.im_pos.le _)
  have hrc : Continuous r := by
    refine (f.holo'.continuous.norm.pow 2).mul ?_
    exact (continuous_im).zpow₀ k fun z => Or.inl z.im_ne_zero
  have hrp : ∀ z, petersson k f f z = (r z : ℂ) := fun z => petersson_self_eq k f z

  set I : SL(2, ℤ) ⧸ lev N l → ℝ := fun q => ∫ z in ModularGroup.fd, r (q.out⁻¹ • z) with hI
  have hpet : pet (lev N l) k ⇑f ⇑f = ((∑ q, I q : ℝ) : ℂ) := by
    rw [pet, finsum_eq_sum_of_fintype, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [hrp, hI]
    exact integral_ofReal
  have hI0 : ∀ q, 0 ≤ I q := fun q => integral_nonneg fun z => hr0 _

  obtain ⟨z₀, hz₀⟩ : ∃ z, f z ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (CuspForm.ext h)
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z₀
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (lev N l) g
  have hinv : ∀ z, r (((h⁻¹ : lev N l) : SL(2, ℤ)) • z) = r z := by
    intro z
    have e := SlashInvariantFormClass.norm_petersson_smul (f := f) (f' := f) (τ := z)
      (Γ := (lev N l : Subgroup (GL (Fin 2) ℝ)))
      (g := (((h⁻¹ : lev N l) : SL(2, ℤ)) : GL (Fin 2) ℝ)) ⟨_, (h⁻¹).2, rfl⟩
    rw [hrp, hrp, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (hr0 _),
      Real.norm_of_nonneg (hr0 _)] at e
    exact e
  have hpt : (((g : SL(2, ℤ) ⧸ lev N l)).out⁻¹ • (g • z₀)) = ((h⁻¹ : lev N l) : SL(2, ℤ)) • z₀ := by
    rw [hh, smul_smul, mul_inv_rev, inv_mul_cancel_right]
    rfl
  have hIpos : 0 < I (g : SL(2, ℤ) ⧸ lev N l) := by
    have hpos : 0 < r ((g : SL(2, ℤ) ⧸ lev N l).out⁻¹ • (g • z₀)) := by
      rw [hpt, hinv]
      exact mul_pos (pow_pos (norm_pos_iff.2 hz₀) 2) (zpow_pos z₀.im_pos _)
    have hc : Continuous fun z : ℍ => r ((g : SL(2, ℤ) ⧸ lev N l).out⁻¹ • z) :=
      hrc.comp (continuous_const_smul (((g : SL(2, ℤ) ⧸ lev N l).out⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ))
    have hint : IntegrableOn (fun z : ℍ => r ((g : SL(2, ℤ) ⧸ lev N l).out⁻¹ • z)) ModularGroup.fd := by
      obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k (lev N l : Subgroup (GL (Fin 2) ℝ)) f f
      have fin := UpperTheory.V.Af.Rs.fdFin (UpperTheory.V.Af.Rs.stripIm UpperTheory.V.Af.Rs.volMap) UpperTheory.V.Af.Rs.volMap
      refine Measure.integrableOn_of_bounded (M := C) fin.2.ne hc.aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => ?_)
      have := hC ((g : SL(2, ℤ) ⧸ lev N l).out⁻¹ • z)
      rw [hrp, Complex.norm_real] at this
      exact this
    exact UpperTheory.V.Af.Rs.fdPos UpperTheory.V.Af.Rs.volMap _ hc (fun z => hr0 _) hint _ hg hpos
  rw [hpet, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨Finset.sum_pos' (fun q _ => hI0 q) ⟨_, Finset.mem_univ _, hIpos⟩, rfl⟩

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinDirichletSeriesIdentityHecke
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem rankin_dirichlet_identity : ∀ (e : ℕ) (χ ψ θ g : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ m n, ψ (m * n) = ψ m * ψ n) → (∀ m n, θ (m * n) = θ m * θ n) → (∀ n, ‖χ n‖ ≤ 1 ∧ ‖ψ n‖ ≤ 1 ∧ ‖θ n‖ ≤ 1) → (∀ m n : ℕ, 0 < m → 0 < n → g m * g n = ∑ δ ∈ (Nat.gcd m n).divisors, χ δ * (δ : ℂ) ^ (2 * e) * g (m * n / δ ^ 2)) → (∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)) → ∀ b : ℕ → ℂ, (∀ n, n ≠ 0 → b n = ∑ p ∈ n.divisorsAntidiagonal, ψ p.1 * (p.1 : ℂ) ^ (e - 1) * θ p.2) → LSeriesSummable (fun n => g n * b n) ((2 * (e : ℝ) + s : ℝ) : ℂ) ∧ LSeries (fun n => χ n * ψ n * θ n) ((e + 1 : ℕ) + 2 * s) * LSeries (fun n => g n * b n) ((2 * (e : ℝ) + s : ℝ) : ℂ) = LSeries (fun n => ψ n * g n) ((e + 1 : ℝ) + s : ℝ) * LSeries (fun n => θ n * g n) ((2 * (e : ℝ) + s : ℝ) : ℂ) := by
  intro e χ ψ θ g s he hs hψ hθ hn hg hsum b hb
  have hGB := _root_.GlobalTheory.DivConvSum.lSeriesSummable_mul_divisorSum e ψ θ g b s he hs (fun n => ⟨(hn n).2.1, (hn n).2.2⟩) hsum hb
  have hU := _root_.GlobalTheory.lseriesSummable_twist_pow_of_sq_summable e ψ g s he hs (fun n => (hn n).2.1) hsum
  have hV := _root_.GlobalTheory.lSeriesSummable_bounded_mul_of_summable_normSq e θ g s he hs (fun n => (hn n).2.2) hsum
  have hz := _root_.GlobalTheory.lseriesSquares_eq e χ ψ θ s he hs hn
  refine ⟨hGB, ?_⟩
  rw [← hz.2, ← LSeries_convolution' hz.1 hGB, ← GlobalTheory.T.lSeries_twist_natPow_eq_shift e ψ g s he, ← LSeries_convolution' hU hV]
  exact LSeries_congr (fun {n} hn0 => (_root_.GlobalTheory.rankin_convolution_coeff e χ ψ θ g b hψ hθ hg hb n hn0).symm) _

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinMeanSquareCuspForm
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.MeanSquareEstimates

theorem key (k L : ℕ) (χ : ℤ → ℂ) (h : ℕ → ℂ) (hc : CF k L χ h) (C : ℝ)
    (hC : ∀ τ : ℍ, ‖qs h τ‖ ^ 2 * τ.im ^ k ≤ C) (y : ℝ) (hy : 0 < y) :
    Summable (fun n : ℕ => ‖h n‖ ^ 2 * Real.exp (-4 * π * n * y)) ∧
      ∑' n : ℕ, ‖h n‖ ^ 2 * Real.exp (-4 * π * n * y) ≤ C / y ^ k := by
  have hp := _root_.GlobalTheory.EisM.parseval_line h h y hc.1.1 hc.1.1 hy
  set I := ∫ x in (0 : ℝ)..1, conj (qs h (ofComplex (x + y * Complex.I))) * qs h (ofComplex (x + y * Complex.I))
  have hr := Complex.hasSum_re hp
  have e : (fun n : ℕ => (conj (h n) * h n * ((Real.exp (-4 * π * n * y) : ℝ) : ℂ)).re) =
      fun n : ℕ => ‖h n‖ ^ 2 * Real.exp (-4 * π * n * y) := by
    funext n
    rw [Complex.conj_mul']
    norm_cast
  rw [e] at hr
  refine ⟨hr.summable, ?_⟩
  rw [hr.tsum_eq]
  have hb : ∀ x ∈ Set.uIoc (0 : ℝ) 1, ‖conj (qs h (ofComplex (x + y * Complex.I))) * qs h (ofComplex (x + y * Complex.I))‖ ≤ C / y ^ k := by
    intro x _
    have him : 0 < ((x : ℂ) + y * Complex.I).im := by simpa using hy
    rw [ofComplex_apply_of_im_pos him, Complex.conj_mul']
    have h1 := hC ⟨(x : ℂ) + y * Complex.I, him⟩
    have h2 : (⟨(x : ℂ) + y * Complex.I, him⟩ : ℍ).im = y := by simp [UpperHalfPlane.im]
    rw [h2] at h1
    rw [le_div_iff₀ (by positivity)]
    simpa using h1
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  calc I.re ≤ ‖I‖ := Complex.re_le_norm I
    _ ≤ C / y ^ k * |1 - 0| := this
    _ = C / y ^ k := by simp

theorem key2 (k L : ℕ) (χ : ℤ → ℂ) (h : ℕ → ℂ) (hc : CF k L χ h) (C : ℝ)
    (hC : ∀ τ : ℍ, ‖qs h τ‖ ^ 2 * τ.im ^ k ≤ C) (t : ℝ) (ht : 0 < t) (N : ℕ) :
    ∑ n ∈ Finset.range N, ‖h n‖ ^ 2 * Real.exp (-(n : ℝ) * t) ≤ C * (4 * π) ^ k / t ^ k := by
  have hy : 0 < t / (4 * π) := by positivity
  obtain ⟨hs, hb⟩ := key k L χ h hc C hC _ hy
  have e : ∀ n : ℕ, -4 * π * n * (t / (4 * π)) = -(n : ℝ) * t := fun n => by field_simp
  simp only [e] at hs hb
  have e2 : C / (t / (4 * π)) ^ k = C * (4 * π) ^ k / t ^ k := by rw [div_pow]; field_simp
  rw [e2] at hb
  exact (hs.sum_le_tsum _ (fun n _ => by positivity)).trans hb

theorem blk (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (a0 : a 0 = 0) (k : ℕ) (D : ℝ)
    (hD : ∀ t : ℝ, 0 < t → ∀ N : ℕ, ∑ n ∈ Finset.range N, a n * Real.exp (-(n : ℝ) * t) ≤ D / t ^ k)
    (s : ℝ) (hs : 0 < s) (N : ℕ) :
    ∑ n ∈ Finset.range N, a n / (n : ℝ) ^ ((k : ℝ) + s) ≤ Real.exp 2 * D / (1 - (2 : ℝ) ^ (-s)) := by
  set x : ℝ := (2 : ℝ) ^ (-s) with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hD0 : 0 ≤ D := by
    have := hD 1 one_pos 0
    simpa using this
  set G : ℕ → ℕ → ℝ := fun j n => Real.exp 2 * (x ^ j / ((2 : ℝ) ^ j) ^ k) * (a n * Real.exp (-(n : ℝ) * ((2 : ℝ) ^ j)⁻¹)) with hG
  have G0 : ∀ j n, 0 ≤ G j n := fun j n => by have := ha n; positivity
  have pt : ∀ n ∈ Finset.range N, a n / (n : ℝ) ^ ((k : ℝ) + s) ≤ ∑ j ∈ Finset.range N, G j n := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · rw [a0, zero_div]; exact Finset.sum_nonneg fun j _ => G0 j 0
    set j := Nat.log 2 n
    have hj1 : 2 ^ j ≤ n := Nat.pow_log_le_self 2 hn0.ne'
    have hj2 : n < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    have hjN : j < N := by
      have : j < 2 ^ j := Nat.lt_two_pow_self
      have := Finset.mem_range.mp hn
      omega
    refine le_trans ?_ (Finset.single_le_sum (fun i _ => G0 i n) (Finset.mem_range.mpr hjN))
    have npos : (0 : ℝ) < n := by exact_mod_cast hn0
    have h2j : ((2 : ℝ) ^ j) ≤ n := by exact_mod_cast hj1
    have h2j' : (n : ℝ) ≤ 2 * (2 : ℝ) ^ j := by
      have : (n : ℝ) < ((2 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast hj2
      push_cast at this; rw [pow_succ] at this; linarith
    have P : ((2 : ℝ) ^ j) ^ k * ((2 : ℝ) ^ j) ^ s ≤ (n : ℝ) ^ k * (n : ℝ) ^ s := by gcongr
    have E : 1 ≤ Real.exp 2 * Real.exp (-(n : ℝ) * ((2 : ℝ) ^ j)⁻¹) := by
      rw [← Real.exp_add]; apply Real.one_le_exp
      have : (n : ℝ) * ((2 : ℝ) ^ j)⁻¹ ≤ 2 := by
        rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]; linarith
      linarith
    have hxj : x ^ j = (((2 : ℝ) ^ j) ^ s)⁻¹ := by
      rw [hxdef, Real.rpow_neg (by norm_num), inv_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm]
    have L : (n : ℝ) ^ ((k : ℝ) + s) = (n : ℝ) ^ k * (n : ℝ) ^ s := by
      rw [Real.rpow_add npos, Real.rpow_natCast]
    have R : G j n = a n * (Real.exp 2 * Real.exp (-(n : ℝ) * ((2 : ℝ) ^ j)⁻¹)) / (((2 : ℝ) ^ j) ^ k * ((2 : ℝ) ^ j) ^ s) := by
      rw [hG]; dsimp only; rw [hxj]; field_simp
    rw [L, R]
    have an := ha n
    calc a n / ((n : ℝ) ^ k * (n : ℝ) ^ s) ≤ a n / (((2 : ℝ) ^ j) ^ k * ((2 : ℝ) ^ j) ^ s) := by
          gcongr
      _ ≤ _ := by gcongr; exact le_mul_of_one_le_right an E
  calc ∑ n ∈ Finset.range N, a n / (n : ℝ) ^ ((k : ℝ) + s) ≤ ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range N, G j n :=
        Finset.sum_le_sum pt
    _ = ∑ j ∈ Finset.range N, ∑ n ∈ Finset.range N, G j n := Finset.sum_comm
    _ = ∑ j ∈ Finset.range N, Real.exp 2 * (x ^ j / ((2 : ℝ) ^ j) ^ k) *
          ∑ n ∈ Finset.range N, a n * Real.exp (-(n : ℝ) * ((2 : ℝ) ^ j)⁻¹) := by
        simp only [hG, Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range N, Real.exp 2 * (x ^ j / ((2 : ℝ) ^ j) ^ k) * (D / (((2 : ℝ) ^ j)⁻¹) ^ k) := by
        gcongr with j _
        exact hD _ (by positivity) N
    _ = ∑ j ∈ Finset.range N, Real.exp 2 * D * x ^ j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [inv_pow]; field_simp
    _ = Real.exp 2 * D * ∑ j ∈ Finset.range N, x ^ j := by rw [Finset.mul_sum]
    _ ≤ Real.exp 2 * D * (x ^ 0 / (1 - x)) := by
        gcongr
        rw [Finset.range_eq_Ico]; exact geom_sum_Ico_le_of_lt_one hx0 hx1
    _ = Real.exp 2 * D / (1 - x) := by rw [pow_zero]; ring

theorem geo (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) : s / 3 ≤ 1 - (2 : ℝ) ^ (-s) := by
  have L := Real.log_two_gt_d9
  have h1 : 1 + s * Real.log 2 ≤ (2 : ℝ) ^ s := by
    rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
    linarith [Real.add_one_le_exp (Real.log 2 * s)]
  have hp : 0 < 1 + s * Real.log 2 := by nlinarith
  have h2 : (2 : ℝ) ^ (-s) ≤ 1 / (1 + s * Real.log 2) := by
    rw [Real.rpow_neg (by norm_num), one_div]
    exact inv_anti₀ hp h1
  have h3 : 1 / (1 + s * Real.log 2) ≤ 1 - s / 3 := by
    rw [div_le_iff₀ hp]
    have q : 0 ≤ Real.log 2 - 1 / 3 - s * Real.log 2 / 3 := by nlinarith
    nlinarith [mul_nonneg hs.le q]
  linarith

end GlobalTheory.MeanSquareEstimates

namespace GlobalTheory


open GlobalTheory.MeanSquareEstimates in
theorem rankin_mean_square : ∀ (k L : ℕ) (χ : ℤ → ℂ) (h : ℕ → ℂ), 1 ≤ k → CF k L χ h → h 0 = 0 ∧ (∃ C : ℝ, ∀ n : ℕ, ‖h n‖ ^ 2 ≤ C * (n : ℝ) ^ k) ∧ (∀ s : ℝ, 0 < s → Summable fun n : ℕ => ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s)) ∧ ∃ C : ℝ, ∀ s : ℝ, 0 < s → s ≤ 1 → s * ∑' n : ℕ, ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s) ≤ C := by
  intro k L χ h hk hc
  obtain ⟨C, hC⟩ := hc.2
  have C0 : 0 ≤ C := le_trans (by positivity) (hC UpperHalfPlane.I)
  set D := C * (4 * π) ^ k with hDdef
  have D0 : 0 ≤ D := by positivity
  have K := key2 k L χ h hc C hC
  have K1 : ∀ t : ℝ, 0 < t → ∀ n : ℕ, ‖h n‖ ^ 2 * Real.exp (-(n : ℝ) * t) ≤ D / t ^ k := by
    intro t ht n
    refine le_trans ?_ (K t ht (n + 1))
    exact Finset.single_le_sum (f := fun m : ℕ => ‖h m‖ ^ 2 * Real.exp (-(m : ℝ) * t)) (fun m _ => by positivity)
      (Finset.mem_range.mpr (Nat.lt_succ_self n))
  have h0 : h 0 = 0 := by
    have lim : Tendsto (fun t : ℝ => D / t ^ k) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by omega))
    have b : ‖h 0‖ ^ 2 ≤ 0 := by
      refine ge_of_tendsto lim ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      simpa using K1 t ht 0
    have : ‖h 0‖ = 0 := by nlinarith [norm_nonneg (h 0)]
    exact norm_eq_zero.mp this
  have B : ∀ s : ℝ, 0 < s → ∀ N : ℕ, ∑ n ∈ Finset.range N, ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s) ≤ Real.exp 2 * D / (1 - (2 : ℝ) ^ (-s)) :=
    fun s hs N => blk (fun n => ‖h n‖ ^ 2) (fun n => by positivity) (by simp [h0]) k D K s hs N
  have nn : ∀ s : ℝ, ∀ n : ℕ, 0 ≤ ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s) := fun s n => by positivity
  refine ⟨h0, ⟨D * Real.exp 1, fun n => ?_⟩, fun s hs => summable_of_sum_range_le (nn s) (B s hs), ⟨3 * (Real.exp 2 * D), fun s hs hs1 => ?_⟩⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [h0, zero_pow (by omega : k ≠ 0)]
    have npos : (0 : ℝ) < n := by exact_mod_cast hn
    have := K1 (n : ℝ)⁻¹ (by positivity) n
    rw [neg_mul, mul_inv_cancel₀ npos.ne', inv_pow, div_inv_eq_mul] at this
    have e : ‖h n‖ ^ 2 = ‖h n‖ ^ 2 * Real.exp (-1) * Real.exp 1 := by
      rw [mul_assoc, ← Real.exp_add]; simp
    rw [e]
    calc ‖h n‖ ^ 2 * Real.exp (-1) * Real.exp 1 ≤ D * (n : ℝ) ^ k * Real.exp 1 := by gcongr
      _ = D * Real.exp 1 * (n : ℝ) ^ k := by ring
  · have T := Real.tsum_le_of_sum_range_le (nn s) (B s hs)
    have g := geo s hs hs1
    have pos : 0 < 1 - (2 : ℝ) ^ (-s) := by linarith
    calc s * ∑' n : ℕ, ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s) ≤ s * (Real.exp 2 * D / (1 - (2 : ℝ) ^ (-s))) := by gcongr
      _ ≤ 3 * (Real.exp 2 * D) := by
        rw [mul_div_assoc', div_le_iff₀ pos]
        have : 0 ≤ Real.exp 2 * D := by positivity
        nlinarith

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumDilate
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM Filter Topology
open scoped MatrixGroups Real ComplexConjugate

namespace GlobalTheory.EisM

theorem dif_comp_add (L : ℕ) (ι : ℤ × ℤ → ℤ × ℤ) (hι : ∀ x v : ℤ × ℤ, ∀ r : ℤ, ι (x + r • v) = ι x + r • ι v)
    (v : ℤ × ℤ) (F : ℤ × ℤ → ℂ) :
    dif L v (fun y => F (ι y)) = fun x => dif L (ι v) F (ι x) := by
  funext x
  simp only [dif, hι]

theorem lat_dilate : ∀ (j L N : ℕ) (v : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ τ' : ℍ), 0 < N → (τ' : ℂ) = N * τ →
    lat j 0 L v Φ τ' = lat j 0 L ((N : ℤ) * v.1, v.2) (fun y => if (N : ℤ) ∣ y.1 then Φ (y.1 / N, y.2) else 0) τ := by
  intro j L N v Φ τ τ' hN hτ
  set ι : ℤ × ℤ → ℤ × ℤ := fun x => ((N : ℤ) * x.1, x.2) with hιdef
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hinj : Function.Injective ι := by
    intro a b h
    simp only [hιdef, Prod.mk.injEq] at h
    exact Prod.ext (mul_left_cancel₀ hN' h.1) h.2
  have hι : ∀ x v : ℤ × ℤ, ∀ r : ℤ, ι (x + r • v) = ι x + r • ι v := by
    intro x v r
    simp only [hιdef, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.mk_add_mk,
      Prod.smul_mk]
    ext <;> simp only <;> ring
  set T : ℤ × ℤ → ℂ := fun y => trm j 0 ((y.1 : ℂ) * τ + y.2) with hT
  have hG : (fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * (τ' : ℂ) + y.2)) = fun y => T (ι y) := by
    funext y
    simp only [hT, hιdef, hτ]
    congr 1
    push_cast
    ring
  have hvι : ι v = ((N : ℤ) * v.1, v.2) := rfl
  have hdd : ∀ x, dif L v (dif L v fun y => trm j 0 ((y.1 : ℂ) * (τ' : ℂ) + y.2)) x =
      dif L (ι v) (dif L (ι v) T) (ι x) := by
    intro x
    rw [hG, dif_comp_add L ι hι, dif_comp_add L ι hι]
  set Ψ : ℤ × ℤ → ℂ := fun y => if (N : ℤ) ∣ y.1 then Φ (y.1 / N, y.2) else 0 with hΨ
  have hΨι : ∀ x, Ψ (ι x) = Φ x := by
    intro x
    simp only [hΨ, hιdef, dvd_mul_right, if_true, Int.mul_ediv_cancel_left _ hN']
  unfold lat
  rw [← hvι]
  simp_rw [hdd]
  set D := dif L (ι v) (dif L (ι v) T) with hD
  have key : (fun x => Φ x * D (ι x)) = fun x => (fun y => Ψ y * D y) (ι x) := by
    funext x; simp only [hΨι]
  rw [key]
  refine hinj.tsum_eq (f := fun y => Ψ y * D y) ?_
  intro y hy
  simp only [Function.mem_support] at hy
  by_cases h : (N : ℤ) ∣ y.1
  · obtain ⟨c, hc⟩ := h
    exact ⟨(c, y.2), by simp only [hιdef]; exact Prod.ext hc.symm rfl⟩
  · exact absurd (by simp only [hΨ, h, if_false, zero_mul]) hy

end GlobalTheory.EisM
end

