module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashToGLSmul
section
noncomputable section

open UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

def wOld (N l : ℕ) (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![(l : ℤ), a; (N : ℤ) * l, (l : ℤ) * b]

def gaOld (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (j : ℕ) : SL(2, ℤ) :=
  ⟨!![1, (j : ℤ) + a; (N : ℤ), (N : ℤ) * j + l * b], by
    rw [Matrix.det_fin_two_of]; linear_combination h⟩

def trOld (k : ℤ) (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (G : ℍ → ℂ) : ℍ → ℂ :=
  G + ∑ j ∈ Finset.range l, G ∣[k] gaOld N l a b h j

def ChiInv (k : ℤ) (N M : ℕ) (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M → G ∣[k] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • G

def CuspAll (k : ℤ) (G : ℍ → ℂ) : Prop :=
  MDiff G ∧ ∀ c : OnePoint ℝ, IsCusp c 𝒮ℒ → c.IsZeroAt G k

end GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.HeckeFamilyMatrices

lemma toGL_val (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) :
    ((toGL g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (Int.castRingHom ℝ).mapMatrix g := by
  unfold toGL
  rw [dite_eq_right hg]
  rfl

lemma toGL_det (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) :
    ((toGL g).det : ℝ) = (g.det : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, toGL_val g hg, ← RingHom.map_det]
  simp

lemma toGL_mul (g h : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) (hh : h.det ≠ 0) :
    toGL (g * h) = toGL g * toGL h := by
  have hgh : (g * h).det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero hg hh
  apply Units.ext
  rw [Units.val_mul, toGL_val _ hgh, toGL_val _ hg, toGL_val _ hh]
  exact map_mul (Int.castRingHom ℝ).mapMatrix g h

lemma slash_SL_eq (k : ℤ) (γ : SL(2, ℤ)) (G : ℍ → ℂ) : G ∣[k] γ = G ∣[k] toGL (mat γ) := by
  rw [ModularForm.SL_slash]
  congr 1
  apply Units.ext
  rw [toGL_val _ (by simp [mat])]
  ext i j
  simp [mat]

end GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.HeckeFamilyMatrices

lemma sigma_pos {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (z : ℂ) : σ g z = z := by
  rw [σ, if_pos hg]
  rfl

lemma slash_scalar (k : ℤ) (c : ℝ) (hc : 0 < c) (G : ℍ → ℂ) :
    G ∣[k] (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc.ne')) = ((c : ℂ) ^ (k - 2)) • G := by
  ext τ
  have hdet : (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc.ne')).det.val = c ^ 2 := by
    simp [Matrix.GeneralLinearGroup.det_scalar]
  have hpos : 0 < (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc.ne')).det.val := by
    rw [hdet]; positivity
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [ModularForm.slash_apply, sigma_pos hpos, hdet, abs_of_pos (by positivity),
    UpperHalfPlane.glScalar_smul, UpperHalfPlane.denom_scalar]
  simp only [Units.val_mk0, Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [← zpow_natCast, ← zpow_mul]
  have he : (c : ℂ) ^ (k - 2) = (c : ℂ) ^ (((2 : ℕ) : ℤ) * (k - 1)) * (c : ℂ) ^ (-k) := by
    rw [← zpow_add₀ hc']
    congr 1
    push_cast
    ring
  rw [he]
  ring

end GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.HeckeFamilyMatrices

lemma toGL_det_pos (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : 0 < g.det) : 0 < (toGL g).det.val := by
  rw [toGL_det g hg.ne']
  exact_mod_cast hg

lemma smul_slash_toGL (k : ℤ) (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0 < M.det) (c : ℂ) (G : ℍ → ℂ) :
    (c • G) ∣[k] toGL M = c • (G ∣[k] toGL M) := by
  rw [ModularForm.smul_slash, sigma_pos (toGL_det_pos M hM)]

lemma toGL_smul (c : ℕ) (hc : 0 < c) (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) :
    toGL ((c : ℤ) • g) = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (c : ℝ) (by positivity)) * toGL g := by
  have h1 : ((c : ℤ) • g).det ≠ 0 := by
    rw [Matrix.det_smul]
    simp [hg, hc.ne']
  apply Units.ext
  rw [Units.val_mul, toGL_val _ h1, toGL_val _ hg, Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_mul,
    Units.val_mk0, Matrix.smul_apply, smul_eq_mul]
  simp

lemma slash_toGL_smul (k : ℤ) (c : ℕ) (hc : 0 < c) (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : 0 < g.det)
    (G : ℍ → ℂ) : G ∣[k] toGL ((c : ℤ) • g) = ((c : ℂ) ^ (k - 2)) • (G ∣[k] toGL g) := by
  rw [toGL_smul c hc g hg.ne', SlashAction.slash_mul, slash_scalar k (c : ℝ) (by positivity),
    smul_slash_toGL k g hg, Complex.ofReal_natCast]

lemma ulFam_det (l : ℕ) (hl : 0 < l) (j : Fin l) : 0 < (ulFam l j).det := by
  simp [ulFam, Matrix.det_fin_two_of]
  exact_mod_cast hl

lemma ulF_add (k : ℤ) (l : ℕ) (F G : ℍ → ℂ) : UlF k l (F + G) = UlF k l F + UlF k l G := by
  simp only [UlF, hkF, SlashAction.add_slash, Finset.sum_add_distrib]

lemma ulF_smul (k : ℤ) (l : ℕ) (hl : 0 < l) (c : ℂ) (F : ℍ → ℂ) : UlF k l (c • F) = c • UlF k l F := by
  simp only [UlF, hkF, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => smul_slash_toGL k _ (ulFam_det l hl j) c F

lemma ulF_sub (k : ℤ) (l : ℕ) (hl : 0 < l) (F G : ℍ → ℂ) : UlF k l (F - G) = UlF k l F - UlF k l G := by
  have h := ulF_smul k l hl (-1) G
  rw [sub_eq_add_neg, ulF_add, sub_eq_add_neg]
  congr 1
  simpa using h

end GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.HeckeFamilyMatrices
open CongruenceSubgroup

lemma chiInv_add {k : ℤ} {N M : ℕ} {χ : DirichletCharacter ℂ N} {F G : ℍ → ℂ} (hF : ChiInv k N M χ F)
    (hG : ChiInv k N M χ G) : ChiInv k N M χ (F + G) := by
  intro γ hγ
  rw [SlashAction.add_slash, hF γ hγ, hG γ hγ, smul_add]

lemma chiInv_smul {k : ℤ} {N M : ℕ} {χ : DirichletCharacter ℂ N} {F : ℍ → ℂ} (c : ℂ) (hF : ChiInv k N M χ F) :
    ChiInv k N M χ (c • F) := by
  intro γ hγ
  rw [ModularForm.SL_smul_slash, hF γ hγ, smul_comm]

lemma cuspAll_add {k : ℤ} {F G : ℍ → ℂ} (hF : CuspAll k F) (hG : CuspAll k G) : CuspAll k (F + G) := ⟨hF.1.add hG.1, fun c hc => (hF.2 c hc).add (hG.2 c hc)⟩

lemma cuspAll_smul {k : ℤ} {F : ℍ → ℂ} (c : ℂ) (hF : CuspAll k F) : CuspAll k (c • F) := by
  refine ⟨hF.1.const_smul c, fun p hp g hg => ?_⟩
  rw [ModularForm.smul_slash]
  exact Filter.ZeroAtFilter.smul _ (hF.2 p hp g hg)

end GlobalTheory.HeckeFamilyMatrices
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedEisensteinFxCoefficientSeqOneMemSubring
section
open Finset

namespace GlobalTheory.KummerEisensteinGalois


open Finset in
theorem _root_.GlobalTheory.KummerEisensteinGalois.smF_one_mem_subring : ∀ (K : Type) [Field K] [CharZero K]
    (R : Subring K) (c M : ℕ) (ζ : K) (a b : ℤ),
    0 < M → Nat.Coprime c M → ¬ (M : ℤ) ∣ a → ζ ^ b ∈ R → ζ ^ (-b) ∈ R →
    ∀ n : ℕ, _root_.GlobalTheory.KummerEisensteinGalois.smF (c : ℤ) 1 M ζ a b n ∈ R := by
  intro K _ _ R c M ζ a b hM hcop ha hb hbneg n
  have hca : ¬ (M : ℤ) ∣ (c : ℤ) * a := by
    intro h
    apply ha
    refine Int.dvd_of_dvd_mul_right_of_gcd_one h ?_
    rw [Int.gcd_natCast_natCast]
    exact Nat.Coprime.symm hcop
  have hpow : ∀ m : ℕ, ζ ^ (b * (m : ℤ)) ∈ R ∧ ζ ^ (-(b * (m : ℤ))) ∈ R := by
    intro m
    refine ⟨?_, ?_⟩
    · rw [zpow_mul, zpow_natCast]; exact R.pow_mem hb m
    · rw [← neg_mul, zpow_mul, zpow_natCast]; exact R.pow_mem hbneg m
  have hpow' : ∀ m : ℕ, ζ ^ ((c : ℤ) * b * (m : ℤ)) ∈ R ∧ ζ ^ (-((c : ℤ) * b * (m : ℤ))) ∈ R := by
    intro m
    have h := hpow (c * m)
    rwa [show (c : ℤ) * b * (m : ℤ) = b * ((c * m : ℕ) : ℤ) by push_cast; ring]
  unfold _root_.GlobalTheory.KummerEisensteinGalois.smF _root_.GlobalTheory.KummerEisensteinGalois.eisF
  split_ifs with hn
  · unfold _root_.GlobalTheory.KummerEisensteinGalois.const0
    simp only [if_true, if_neg ha, if_neg hca]
    have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
    have key : (c : ℚ) ^ 2 * (1 / 2 - _root_.GlobalTheory.KummerEisensteinGalois.frc M a) -
        c * (1 / 2 - _root_.GlobalTheory.KummerEisensteinGalois.frc M (c * a)) =
        (((c.choose 2 : ℕ) : ℤ) - ((c : ℤ) * ((c : ℤ) * a / M) - (c : ℤ) ^ 2 * (a / M)) : ℤ) := by
      unfold _root_.GlobalTheory.KummerEisensteinGalois.frc
      rw [Int.emod_def, Int.emod_def]
      push_cast
      rw [Nat.cast_choose_two]
      field_simp
      ring
    convert intCast_mem R (((c.choose 2 : ℕ) : ℤ) - ((c : ℤ) * ((c : ℤ) * a / M) -
      (c : ℤ) ^ 2 * (a / M))) using 1
    have hK := congrArg (fun q : ℚ => (q : K)) key
    simp only [Rat.cast_intCast] at hK
    rw [← hK]
    push_cast
    norm_num
  · unfold _root_.GlobalTheory.KummerEisensteinGalois.coefPos
    refine R.sub_mem (R.mul_mem (R.pow_mem (intCast_mem R _) 2) (R.sum_mem fun d _ => ?_))
      (R.mul_mem ?_ (R.sum_mem fun d _ => ?_))
    · simp only [Nat.sub_self, pow_zero, one_mul]
      refine R.sub_mem ?_ ?_ <;> split_ifs
      · exact (hpow d).1
      · exact R.zero_mem
      · exact (hpow d).2
      · exact R.zero_mem
    · norm_num
    · simp only [Nat.sub_self, pow_zero, one_mul]
      refine R.sub_mem ?_ ?_ <;> split_ifs
      · exact (hpow' d).1
      · exact R.zero_mem
      · exact (hpow' d).2
      · exact R.zero_mem

end GlobalTheory.KummerEisensteinGalois
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.StripEvalPolynomialDecayMulImRpow
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

open Filter Topology

private lemma norm_eval_add_C_le_of_coeff_le (w : ℕ) (a z : ℂ) (p : ℂ[X]) (K e : ℝ) (hK : 0 ≤ K)
    (he : 0 ≤ e) (hp : p ∈ degreeLT ℂ (w + 1))
    (hc : ∀ j ≤ w, ‖p.coeff j‖ ≤ K * e * (1 + ‖z‖) ^ w) :
    ‖(p + C a).eval z‖ ≤ ‖a‖ + (w + 1) * (K * e * (1 + ‖z‖) ^ (2 * w)) := by
  have hdeg : p.natDegree < w + 1 := by
    by_cases h0 : p = 0
    · simp [h0]
    · exact (natDegree_lt_iff_degree_lt h0).2 (mem_degreeLT.1 hp)
  rw [eval_add, eval_C, eval_eq_sum_range' hdeg]
  have hz1 : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  have hterm : ∀ j ∈ Finset.range (w + 1),
      ‖p.coeff j * z ^ j‖ ≤ K * e * (1 + ‖z‖) ^ (2 * w) := by
    intro j hj
    have hjw : j ≤ w := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [norm_mul, norm_pow]
    have h1 : ‖z‖ ^ j ≤ (1 + ‖z‖) ^ w :=
      (pow_le_pow_left₀ (norm_nonneg z) (by linarith) j).trans (pow_le_pow_right₀ hz1 hjw)
    calc ‖p.coeff j‖ * ‖z‖ ^ j ≤ (K * e * (1 + ‖z‖) ^ w) * (1 + ‖z‖) ^ w :=
          mul_le_mul (hc j hjw) h1 (by positivity) (by positivity)
      _ = K * e * (1 + ‖z‖) ^ (2 * w) := by ring
  calc ‖∑ j ∈ Finset.range (w + 1), p.coeff j * z ^ j + a‖
      ≤ ‖∑ j ∈ Finset.range (w + 1), p.coeff j * z ^ j‖ + ‖a‖ := norm_add_le _ _
    _ ≤ ∑ j ∈ Finset.range (w + 1), ‖p.coeff j * z ^ j‖ + ‖a‖ := by
        gcongr; exact norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (w + 1), K * e * (1 + ‖z‖) ^ (2 * w) + ‖a‖ := by
        gcongr with j hj; exact hterm j hj
    _ = ‖a‖ + (w + 1) * (K * e * (1 + ‖z‖) ^ (2 * w)) := by simp; ring

theorem strip_eval_decay : ∀ (w n : ℕ) (a : ℂ) (V : ℍ → ℂ[X]) (C' c : ℝ), 1 ≤ w → 0 < c →
    (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) →
    (∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(V τ - C a).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w) →
    ∀ ε > 0, ∃ A : ℝ, ∀ τ : ℍ, A ≤ τ.im → 0 ≤ τ.re → τ.re ≤ n →
      ‖(V τ).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2) < ε := by
  intro w n a V C' c hw hc hV hcoef ε hε
  set K := max C' 0 with hKdef
  have hK : 0 ≤ K := le_max_right _ _
  have hwpos : (0 : ℝ) < (w : ℝ) / 2 := by
    have : (1 : ℝ) ≤ w := by exact_mod_cast hw
    linarith
  have h1 : Tendsto (fun y : ℝ => ‖a‖ * y ^ (-(w : ℝ) / 2)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop hwpos).const_mul ‖a‖
    rw [mul_zero] at this
    refine this.congr' (Eventually.of_forall fun y => ?_)
    simp only [neg_div]
  have h2 : Tendsto (fun y : ℝ => (w + 1) * (K * 4 ^ w) * (y ^ (2 * w) / Real.exp (c * y)))
      atTop (𝓝 0) := by
    have := ((isLittleO_pow_exp_pos_mul_atTop (2 * w) hc).tendsto_div_nhds_zero).const_mul
      ((w + 1) * (K * 4 ^ w))
    rwa [mul_zero] at this
  have e1 := h1.eventually (gt_mem_nhds (half_pos hε))
  have e2 := h2.eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨A0, hA0⟩ := eventually_atTop.1 (e1.and e2)
  refine ⟨max A0 (1 + n), fun τ hA hre hren => ?_⟩
  have hpos : 0 < τ.im := τ.im_pos
  have hy0 : A0 ≤ τ.im := le_trans (le_max_left _ _) hA
  have hyn : 1 + (n : ℝ) ≤ τ.im := le_trans (le_max_right _ _) hA
  have hy1 : 1 ≤ τ.im := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  obtain ⟨hf1, hf2⟩ := hA0 τ.im hy0
  have hz : ‖(τ : ℂ)‖ ≤ n + τ.im := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have hr : |(τ : ℂ).re| ≤ n := by
      rw [UpperHalfPlane.coe_re, abs_of_nonneg hre]; exact hren
    have hi : |(τ : ℂ).im| = τ.im := by
      rw [UpperHalfPlane.coe_im, abs_of_pos hpos]
    linarith
  have hcb : ∀ j ≤ w, ‖(V τ - C a).coeff j‖ ≤ K * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w := by
    intro j hj
    refine (hcoef τ hy1 j hj).trans ?_
    gcongr
    exact le_max_left _ _
  have hmem : V τ - C a ∈ degreeLT ℂ (w + 1) :=
    Submodule.sub_mem _ (hV τ)
      (mem_degreeLT.2 (lt_of_le_of_lt degree_C_le (by exact_mod_cast Nat.succ_pos w)))
  have hmain := norm_eval_add_C_le_of_coeff_le w a (τ : ℂ) (V τ - C a) K (Real.exp (-c * τ.im)) hK
    (Real.exp_pos _).le hmem hcb
  rw [sub_add_cancel] at hmain
  have hnz : 1 + ‖(τ : ℂ)‖ ≤ 2 * τ.im := by linarith
  have hpow : (1 + ‖(τ : ℂ)‖) ^ (2 * w) ≤ 4 ^ w * τ.im ^ (2 * w) := by
    calc (1 + ‖(τ : ℂ)‖) ^ (2 * w) ≤ (2 * τ.im) ^ (2 * w) :=
          pow_le_pow_left₀ (by positivity) hnz _
      _ = 4 ^ w * τ.im ^ (2 * w) := by rw [mul_pow, pow_mul]; norm_num
  have hT : (w + 1) * (K * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ (2 * w))
      ≤ (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im)) := by
    rw [neg_mul, Real.exp_neg]
    calc (w + 1) * (K * (Real.exp (c * τ.im))⁻¹ * (1 + ‖(τ : ℂ)‖) ^ (2 * w))
        ≤ (w + 1) * (K * (Real.exp (c * τ.im))⁻¹ * (4 ^ w * τ.im ^ (2 * w))) := by gcongr
      _ = (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im)) := by
        rw [div_eq_mul_inv]; ring
  have hT0 : 0 ≤ (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im)) := by positivity
  have hr0 : 0 ≤ τ.im ^ (-(w : ℝ) / 2) := Real.rpow_nonneg hpos.le _
  have hr1 : τ.im ^ (-(w : ℝ) / 2) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos hy1 ?_
    have : (0 : ℝ) ≤ w := Nat.cast_nonneg w
    linarith
  calc ‖(V τ).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2)
      ≤ (‖a‖ + (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im)))
          * τ.im ^ (-(w : ℝ) / 2) := by gcongr; linarith
    _ = ‖a‖ * τ.im ^ (-(w : ℝ) / 2)
          + (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im))
            * τ.im ^ (-(w : ℝ) / 2) := by ring
    _ ≤ ‖a‖ * τ.im ^ (-(w : ℝ) / 2)
          + (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im)) := by
        exact add_le_add le_rfl (mul_le_of_le_one_right hT0 hr1)
    _ < ε / 2 + ε / 2 := add_lt_add hf1 hf2
    _ = ε := add_halves ε

end GlobalTheory.HeckeFamilyMatrices
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumFinrankLevelOneLeFinrankCuspFormOfFrame
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section
namespace GlobalTheory.OddFrame

theorem levelOne_mul_slash {k w : ℤ} (g : ModularForm 𝒮ℒ (k - w)) (F : ℍ → ℂ) (x : SL(2, ℤ)) :
    ((⇑g) * F) ∣[k] x = (⇑g) * (F ∣[w] x) := by
  have h := ModularForm.mul_slash_SL2 (k - w) w x (⇑g) F
  rw [sub_add_cancel] at h
  rw [h, (isMF_coe_top g).slash_top x]

theorem sum_finrank_le_finrank_cuspForm (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ)
    (F : Fin r → ℍ → ℂ) (k : ℤ) (hΓ : Γ.FiniteIndex) (hfin : FiniteDimensional ℂ (CuspForm Γ k))
    (hF : ∀ j, IsCF Γ (w j) (F j)) (hdet : ∀ τ, (evM s w F τ).det ≠ 0) :
    ∑ j, Module.finrank ℂ (ModularForm 𝒮ℒ (k - w j)) ≤ Module.finrank ℂ (CuspForm Γ k) := by
  have hcf : ∀ (j : Fin r) (g : ModularForm 𝒮ℒ (k - w j)), IsCF Γ k ((⇑g) * F j) := fun j g =>
    ((isMF_coe_top g).mono le_top).mul_isCF (hF j) (by ring)
  have happ : ∀ (c : Fin r → CuspForm Γ k) (τ : ℍ), (∑ j, c j) τ = ∑ j, c j τ := by
    intro c τ
    induction (Finset.univ : Finset (Fin r)) using Finset.induction_on with
    | empty => simp
    | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, CuspForm.add_apply, ih]
  let L : (Π j, ModularForm 𝒮ℒ (k - w j)) →ₗ[ℂ] CuspForm Γ k :=
    { toFun := fun g => ∑ j, (hcf j (g j)).toCF
      map_add' := by
        intro a b; ext τ
        simp only [CuspForm.add_apply, happ, IsCF.coe_toCF, Pi.mul_apply, Pi.add_apply, ModularForm.add_apply,
          add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a; ext τ
        simp only [CuspForm.smul_apply, happ, IsCF.coe_toCF, Pi.mul_apply, Pi.smul_apply, ModularForm.smul_apply,
          RingHom.id_apply, smul_eq_mul, Finset.mul_sum, mul_assoc] }
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    have h0 : ∀ τ, ∑ j, g j τ * F j τ = 0 := by
      intro τ
      have := congrArg (fun f : CuspForm Γ k => f τ) hg
      simpa [L, happ] using this
    have hfun : (∑ j, (⇑(g j)) * F j) = 0 := by
      ext τ; simpa [Finset.sum_apply] using h0 τ
    have hvec : ∀ τ, Matrix.mulVec (evM s w F τ) (fun j => g j τ) = 0 := by
      intro τ; ext i
      have h1 := congrArg (fun f => (f ∣[k] s i) τ) hfun
      simp only [SlashAction.zero_slash, Pi.zero_apply] at h1
      rw [SlashAction.sum_slash] at h1
      simp only [levelOne_mul_slash, Finset.sum_apply, Pi.mul_apply] at h1
      simp only [Matrix.mulVec, dotProduct, evM, Matrix.of_apply, Pi.zero_apply]
      rw [← h1]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    funext j; ext τ
    have := Matrix.eq_zero_of_mulVec_eq_zero (hdet τ) (hvec τ)
    exact congrFun this j
  haveI : FiniteDimensional ℂ (Π j, ModularForm 𝒮ℒ (k - w j)) := inferInstance
  calc ∑ j, Module.finrank ℂ (ModularForm 𝒮ℒ (k - w j))
      = Module.finrank ℂ (Π j, ModularForm 𝒮ℒ (k - w j)) := (Module.finrank_pi_fintype ℂ).symm
    _ ≤ Module.finrank ℂ (CuspForm Γ k) := LinearMap.finrank_le_finrank_of_injective hinj

end GlobalTheory.OddFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumMulCosetRepresentativeTraceEq
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem sum_mul_cosetTrace_eq (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G]
    [MulSemiringAction G L] (N : Subgroup G) [Fintype (G ⧸ N)] (n : ℕ) (a b : Fin n → L) (c : L)
    (h : IsSep v N a b c) : ∀ x ∈ Fix L N, ∑ i, a i * cosetTrace N (b i * x) = c * x := by
  classical
  intro x hx
  have hmem : ∀ q : G ⧸ N, q.out ∈ N ↔ q = ((1 : G) : G ⧸ N) := by
    intro q
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [QuotientGroup.eq, mul_one, inv_mem_iff]
  have key : ∀ q : G ⧸ N, (∑ i, a i * q.out • b i) * q.out • x
      = if ((1 : G) : G ⧸ N) = q then c * x else 0 := by
    intro q
    by_cases hq : q.out ∈ N
    · rw [if_pos ((hmem q).mp hq).symm, h.sum_in _ hq]
      congr 1
      exact hx ⟨_, hq⟩
    · rw [if_neg (fun h1 => hq ((hmem q).mpr h1.symm)), h.sum_out _ hq, zero_mul]
  calc ∑ i, a i * cosetTrace N (b i * x)
      = ∑ q : G ⧸ N, (∑ i, a i * q.out • b i) * q.out • x := by
        simp only [cosetTrace, smul_mul', Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = c * x := by rw [Finset.sum_congr rfl fun q _ => key q]; simp

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedIntegersAdicComplete
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5

theorem o0_isAdicComplete_span_p : ∀ (p : ℕ) [Fact p.Prime], IsAdicComplete (Ideal.span {(p : O0 p)}) (O0 p) := by
  intro p _
  have hfg : (pI p).FG := ⟨{(p : Lau p)}, by simp⟩
  have h : IsAdicComplete (pI p) (O0 p) := AdicCompletion.isAdicComplete hfg
  have hmap : (pI p).map (algebraMap (Lau p) (O0 p)) = Ideal.span {(p : O0 p)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [← hmap]
  exact { toIsHausdorff := IsHausdorff.map_algebraMap_iff.2 h.toIsHausdorff
          toIsPrecomplete := IsPrecomplete.map_algebraMap_iff.2 h.toIsPrecomplete }

end GlobalTheory.K5
end

