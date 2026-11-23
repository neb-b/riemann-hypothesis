module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CanonicalThetaExponentSymplecticInvariant
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW

theorem isUnit_det_im_of_mem_siegel {ι : Type} [Fintype ι] [DecidableEq ι] {τ : Matrix ι ι ℂ}
    (hτ : τ ∈ Siegel ι) : IsUnit (τ.map fun z => (z.im : ℂ)).det := by
  have h : (τ.map fun z => (z.im : ℂ)) = Complex.ofRealHom.mapMatrix (τ.map Complex.im) := by
    ext i j; simp
  rw [h, ← RingHom.map_det]
  exact (hτ.2.det_pos.ne'.isUnit).map _

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_add' {α β : Type} (M N : Matrix α β ℚ) :
    _root_.GlobalTheory.SW.qm (M + N) = _root_.GlobalTheory.SW.qm M + _root_.GlobalTheory.SW.qm N := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_neg' {α β : Type} (M : Matrix α β ℚ) :
    _root_.GlobalTheory.SW.qm (-M) = -_root_.GlobalTheory.SW.qm M := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_mul_siegel_theta_transformation {α β γ : Type} [Fintype β] (M : Matrix α β ℚ) (N : Matrix β γ ℚ) :
    _root_.GlobalTheory.SW.qm (M * N) = _root_.GlobalTheory.SW.qm M * _root_.GlobalTheory.SW.qm N := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm, Matrix.mul_apply]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_transpose' {α β : Type} (M : Matrix α β ℚ) :
    _root_.GlobalTheory.SW.qm Mᵀ = (_root_.GlobalTheory.SW.qm M)ᵀ := rfl

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_zero' {α β : Type} : _root_.GlobalTheory.SW.qm (0 : Matrix α β ℚ) = 0 := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_one' : _root_.GlobalTheory.SW.qm (1 : Matrix ι ι ℚ) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [_root_.GlobalTheory.SW.qm, Matrix.one_apply, h]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma sub_conjTranspose_of_isSymm (τ : Matrix ι ι ℂ) (hτ : τ.IsSymm) :
    τ - τᴴ = (2 * I) • τ.map fun z => (z.im : ℂ) := by
  ext i j
  have h := hτ.apply i j
  simp only [Matrix.sub_apply, conjTranspose_apply, Matrix.smul_apply, map_apply, smul_eq_mul, h]
  rw [show star (τ i j) = conj (τ i j) from rfl, Complex.sub_conj]
  push_cast
  ring

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_conjTranspose_eq_transpose {α β : Type} (M : Matrix α β ℚ) :
    (_root_.GlobalTheory.SW.qm M)ᴴ = (_root_.GlobalTheory.SW.qm M)ᵀ := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm, conjTranspose_apply]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma re_star_dotProduct_ofReal_mulVec (Y : Matrix ι ι ℝ) (v : ι → ℂ) :
    (star v ⬝ᵥ (Y.map (fun t => (t : ℂ)) *ᵥ v)).re =
      (fun i => (v i).re) ⬝ᵥ (Y *ᵥ fun i => (v i).re) + (fun i => (v i).im) ⬝ᵥ (Y *ᵥ fun i => (v i).im) := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Complex.re_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.mul_re, Complex.mul_im]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma dotProduct_transpose_mulVec_self (N : Matrix ι ι ℂ) (ζ : ι → ℂ) :
    ζ ⬝ᵥ (Nᵀ *ᵥ ζ) = ζ ⬝ᵥ (N *ᵥ ζ) := by
  rw [mulVec_transpose, dotProduct_comm, dotProduct_mulVec]


open Matrix Complex in
open scoped ComplexConjugate Real in
theorem _root_.GlobalTheory.SW.canon_exponent_invariant : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → ∀ τ ∈ _root_.GlobalTheory.SW.Siegel ι, ∀ ζ : ι → ℂ, (ζ ᵥ* (_root_.GlobalTheory.SW.spDen σ τ)⁻¹) ⬝ᵥ ((_root_.GlobalTheory.SW.spAct σ τ).map fun z => (z.im : ℂ))⁻¹ *ᵥ (ζ ᵥ* (_root_.GlobalTheory.SW.spDen σ τ)⁻¹) + 2 * I * (ζ ⬝ᵥ ((_root_.GlobalTheory.SW.spDen σ τ)⁻¹ * _root_.GlobalTheory.SW.qm σ.toBlocks₂₁) *ᵥ ζ) = ζ ⬝ᵥ (τ.map fun z => (z.im : ℂ))⁻¹ *ᵥ ζ := by
  intro ι _ _ σ hσ τ hτ ζ
  obtain ⟨hsym, hpos⟩ := hτ
  have h2 := SymplecticGroup.mem_iff'.mp hσ
  rw [← fromBlocks_toBlocks σ] at h2
  simp [Matrix.J, fromBlocks_transpose, fromBlocks_multiply] at h2
  obtain ⟨r1, r2, r3, r4⟩ := h2
  replace r1 := congrArg _root_.GlobalTheory.SW.qm r1
  replace r2 := congrArg _root_.GlobalTheory.SW.qm r2
  replace r3 := congrArg _root_.GlobalTheory.SW.qm r3
  replace r4 := congrArg _root_.GlobalTheory.SW.qm r4
  simp only [qm_add', qm_neg', qm_mul_siegel_theta_transformation, qm_transpose',
    qm_zero', qm_one'] at r1 r2 r3 r4
  set A := _root_.GlobalTheory.SW.qm σ.toBlocks₁₁ with hA
  set B := _root_.GlobalTheory.SW.qm σ.toBlocks₁₂ with hB
  set C := _root_.GlobalTheory.SW.qm σ.toBlocks₂₁ with hC
  set D := _root_.GlobalTheory.SW.qm σ.toBlocks₂₂ with hD
  set J := _root_.GlobalTheory.SW.spDen σ τ with hJdef
  have hJ : J = C * τ + D := rfl
  set M := A * τ + B with hM
  have hact : _root_.GlobalTheory.SW.spAct σ τ = M * J⁻¹ := rfl
  set Y := τ.map fun z => (z.im : ℂ) with hYdef
  have hY : τ - τᴴ = (2 * I) • Y := sub_conjTranspose_of_isSymm τ hsym
  have hτt : τᵀ = τ := hsym
  have hCh : Cᴴ = Cᵀ := qm_conjTranspose_eq_transpose _
  have hDh : Dᴴ = Dᵀ := qm_conjTranspose_eq_transpose _
  have hAh : Aᴴ = Aᵀ := qm_conjTranspose_eq_transpose _
  have hBh : Bᴴ = Bᵀ := qm_conjTranspose_eq_transpose _
  have hI1 : Jᴴ * M - Mᴴ * J = τ - τᴴ := by
    rw [hJ, hM, conjTranspose_add, conjTranspose_add, conjTranspose_mul, conjTranspose_mul, hCh, hDh, hAh, hBh]
    have hE : (τᴴ * Cᵀ + Dᵀ) * (A * τ + B) - (τᴴ * Aᵀ + Bᵀ) * (C * τ + D) =
        τᴴ * (Cᵀ * A + -(Aᵀ * C)) * τ + τᴴ * (Cᵀ * B + -(Aᵀ * D)) + (Dᵀ * A + -(Bᵀ * C)) * τ +
          (Dᵀ * B + -(Bᵀ * D)) := by noncomm_ring
    rw [hE, r1, r2, r3, r4]
    noncomm_ring
  have hI2 : Mᵀ * J = Jᵀ * M := by
    rw [hJ, hM, transpose_add, transpose_add, transpose_mul, transpose_mul, hτt]
    have hE : (τ * Aᵀ + Bᵀ) * (C * τ + D) - (τ * Cᵀ + Dᵀ) * (A * τ + B) =
        -(τ * (Cᵀ * A + -(Aᵀ * C)) * τ) - τ * (Cᵀ * B + -(Aᵀ * D)) - (Dᵀ * A + -(Bᵀ * C)) * τ -
          (Dᵀ * B + -(Bᵀ * D)) := by noncomm_ring
    rw [r1, r2, r3, r4] at hE
    rw [← sub_eq_zero, hE]
    noncomm_ring
  have hYr : Y = (τ.map Complex.im).map (fun t => (t : ℂ)) := rfl
  have hdetY : Y.det ≠ 0 := by
    have : Y.det = ((τ.map Complex.im).det : ℂ) := by
      rw [hYr]
      exact (RingHom.map_det Complex.ofRealHom _).symm
    rw [this, Complex.ofReal_ne_zero]
    exact hpos.det_pos.ne'
  have h2I : (2 * I : ℂ) ≠ 0 := by simp
  have hdetJ : J.det ≠ 0 := by
    intro hdet
    obtain ⟨v, hv, hJv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have h0 : star v ⬝ᵥ ((Jᴴ * M - Mᴴ * J) *ᵥ v) = 0 := by
      rw [sub_mulVec, dotProduct_sub, ← mulVec_mulVec, ← mulVec_mulVec, hJv, mulVec_zero,
        dotProduct_zero, dotProduct_mulVec, ← star_mulVec, hJv, star_zero, zero_dotProduct, sub_zero]
    rw [hI1, hY, smul_mulVec, dotProduct_smul, smul_eq_mul, mul_eq_zero] at h0
    have h1 := congrArg Complex.re (h0.resolve_left h2I)
    rw [hYr, re_star_dotProduct_ofReal_mulVec, Complex.zero_re] at h1
    have hna := hpos.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i).re)
    have hnb := hpos.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i).im)
    simp only [star_trivial] at hna hnb
    have ha : (fun i => (v i).re) = 0 := by
      by_contra h
      have := hpos.dotProduct_mulVec_pos h
      simp only [star_trivial] at this
      linarith
    have hb : (fun i => (v i).im) = 0 := by
      by_contra h
      have := hpos.dotProduct_mulVec_pos h
      simp only [star_trivial] at this
      linarith
    apply hv
    funext i
    apply Complex.ext
    · simpa using congrFun ha i
    · simpa using congrFun hb i
  have hJu : IsUnit J.det := isUnit_iff_ne_zero.mpr hdetJ
  have hYu : IsUnit Y.det := isUnit_iff_ne_zero.mpr hdetY
  have hJJ : J * J⁻¹ = 1 := mul_nonsing_inv J hJu
  have hJJ' : J⁻¹ * J = 1 := nonsing_inv_mul J hJu
  have hYY : Y⁻¹ * Y = 1 := nonsing_inv_mul Y hYu
  have hτ'sym : (M * J⁻¹).IsSymm := by
    have hJtu : IsUnit Jᵀ.det := by rwa [det_transpose]
    unfold Matrix.IsSymm
    rw [transpose_mul, transpose_nonsing_inv]
    calc (Jᵀ)⁻¹ * Mᵀ = (Jᵀ)⁻¹ * (Mᵀ * J) * J⁻¹ := by simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = M * J⁻¹ := by rw [hI2, ← Matrix.mul_assoc (Jᵀ)⁻¹, nonsing_inv_mul _ hJtu, Matrix.one_mul]
  set Y' := (_root_.GlobalTheory.SW.spAct σ τ).map fun z => (z.im : ℂ) with hY'def
  have hY' : (2 * I) • Y' = M * J⁻¹ - (M * J⁻¹)ᴴ := by
    rw [hY'def, hact]
    exact (sub_conjTranspose_of_isSymm _ hτ'sym).symm
  have hkey : Jᴴ * Y' * J = Y := by
    apply smul_right_injective _ h2I
    calc (2 * I) • (Jᴴ * Y' * J) = Jᴴ * ((2 * I) • Y') * J := by rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = Jᴴ * (M * J⁻¹ - (M * J⁻¹)ᴴ) * J := by rw [hY']
      _ = Jᴴ * M - Mᴴ * J := by
        rw [conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul]
        congr 1
        · simp only [Matrix.mul_assoc, hJJ', Matrix.mul_one]
        · rw [← Matrix.mul_assoc Jᴴ, ← conjTranspose_mul, hJJ', conjTranspose_one, Matrix.one_mul]
      _ = (2 * I) • Y := by rw [hI1, hY]
  have hY'inv : Y'⁻¹ = J * Y⁻¹ * Jᴴ := by
    apply Matrix.inv_eq_left_inv
    calc J * Y⁻¹ * Jᴴ * Y' = J * Y⁻¹ * (Jᴴ * Y' * J) * J⁻¹ := by
          simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = 1 := by rw [hkey, Matrix.mul_assoc J, hYY, Matrix.mul_one, hJJ]
  have hJh : Jᴴ = Jᵀ - (2 * I) • (Y * Cᵀ) := by
    have hτh : τᴴ = τ - (2 * I) • Y := by rw [← hY]; abel
    rw [hJ, conjTranspose_add, conjTranspose_mul, transpose_add, transpose_mul, hCh, hDh, hτt, hτh,
      Matrix.sub_mul, Matrix.smul_mul]
    abel
  have hJt : Jᵀ * (J⁻¹)ᵀ = 1 := by rw [← transpose_mul, hJJ', transpose_one]
  have hmat : J⁻¹ * (J * Y⁻¹ * Jᴴ) * (J⁻¹)ᵀ = Y⁻¹ - (2 * I) • (J⁻¹ * C)ᵀ := by
    rw [hJh, transpose_mul]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hJJ',
      Matrix.one_mul]
    rw [Matrix.mul_assoc Y⁻¹ Jᵀ, hJt, Matrix.mul_one, hYY, Matrix.one_mul]
  rw [hY'inv, ← dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, mulVec_mulVec, hmat, sub_mulVec,
    dotProduct_sub, smul_mulVec, dotProduct_smul, dotProduct_transpose_mulVec_self, smul_eq_mul]
  ring

end GlobalTheory.SW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ComplexPhaseCalculusRootOfUnity
section
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase.Calc

theorem ph_mul {a b : ℂ} (ha : Ph a) (hb : Ph b) : Ph (a * b) := by
  obtain ⟨m, hm, ha⟩ := ha
  obtain ⟨n, hn, hb⟩ := hb
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  rw [norm_mul, Complex.ofReal_mul, mul_pow, mul_pow, pow_mul a, ha, ← pow_mul, mul_comm m n,
    pow_mul b, hb, ← pow_mul]

theorem ph_inv {a : ℂ} (ha : Ph a) : Ph a⁻¹ := by
  obtain ⟨m, hm, ha⟩ := ha
  refine ⟨m, hm, ?_⟩
  rw [inv_pow, ha, norm_inv, Complex.ofReal_inv, inv_pow]

theorem isMu_of_ph {a : ℂ} (ha : Ph a) (h : ‖a‖ = 1) : IsMu a := by
  obtain ⟨m, hm, ha⟩ := ha
  exact ⟨m, hm, by rw [ha, h]; simp⟩

theorem ph_cancel {a b : ℂ} (hb0 : b ≠ 0) (hb : Ph b) (hab : Ph (a * b)) : Ph a := by
  have h := ph_mul hab (ph_inv hb)
  rwa [mul_assoc, mul_inv_cancel₀ hb0, mul_one] at h


open Matrix Complex in
open scoped ComplexConjugate Real in
theorem _root_.GlobalTheory.Phase.Calc.calculus : (∀ a b : ℂ, _root_.GlobalTheory.Phase.Ph a → _root_.GlobalTheory.Phase.Ph b → _root_.GlobalTheory.Phase.Ph (a * b)) ∧ (∀ a : ℂ, _root_.GlobalTheory.Phase.Ph a → _root_.GlobalTheory.Phase.Ph (conj a) ∧ _root_.GlobalTheory.Phase.Ph a⁻¹) ∧
    (∀ t : ℝ, _root_.GlobalTheory.Phase.Ph (t : ℂ)) ∧ (∀ a : ℂ, _root_.GlobalTheory.Phase.IsMu a → _root_.GlobalTheory.Phase.Ph a ∧ ‖a‖ = 1) ∧ (∀ a : ℂ, _root_.GlobalTheory.Phase.Ph a → ‖a‖ = 1 → _root_.GlobalTheory.Phase.IsMu a) ∧
    (∀ a b : ℂ, _root_.GlobalTheory.Phase.IsMu a → _root_.GlobalTheory.Phase.IsMu b → _root_.GlobalTheory.Phase.IsMu (a * b) ∧ _root_.GlobalTheory.Phase.IsMu a⁻¹ ∧ _root_.GlobalTheory.Phase.IsMu (conj a)) ∧
    (∀ (a : ℂ) (k : ℕ), 0 < k → (_root_.GlobalTheory.Phase.IsMu (a ^ k) → _root_.GlobalTheory.Phase.IsMu a) ∧ (_root_.GlobalTheory.Phase.Ph (a ^ k) → _root_.GlobalTheory.Phase.Ph a)) ∧
    (∀ q : ℚ, _root_.GlobalTheory.Phase.IsMu (cexp (π * I * (q : ℂ)))) ∧ ∀ a b : ℂ, b ≠ 0 → _root_.GlobalTheory.Phase.Ph b → _root_.GlobalTheory.Phase.Ph (a * b) → _root_.GlobalTheory.Phase.Ph a := by
  refine ⟨fun a b ha hb => ha.mul hb, fun a ha => ⟨?_, ha.inv⟩, fun t => ?_, fun a ha => ?_,
    fun a ha h1 => ?_, fun a b ha hb => ⟨?_, ?_, ?_⟩, fun a k hk => ⟨?_, ?_⟩, fun q => ?_,
    fun a b hb0 hb hab => ?_⟩
  · obtain ⟨m, hm, h⟩ := ha
    refine ⟨m, hm, ?_⟩
    rw [← map_pow, h, Complex.norm_conj, map_pow, Complex.conj_ofReal]
  · refine ⟨2, two_pos, ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs, ← ofReal_pow, ← ofReal_pow, sq_abs]
  · obtain ⟨m, hm, h⟩ := ha
    have hn : ‖a‖ = 1 := by
      have h' : ‖a‖ ^ m = 1 := by rw [← norm_pow, h, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg a) hm.ne').1 h'
    exact ⟨⟨m, hm, by rw [h, hn, ofReal_one, one_pow]⟩, hn⟩
  · obtain ⟨m, hm, h⟩ := ha
    exact ⟨m, hm, by rw [h, h1, ofReal_one, one_pow]⟩
  · obtain ⟨m, hm, h⟩ := ha
    obtain ⟨n, hn, h'⟩ := hb
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [mul_pow, pow_mul, h, pow_mul', h', one_pow, one_pow, one_mul]
  · obtain ⟨m, hm, h⟩ := ha
    exact ⟨m, hm, by rw [inv_pow, h, inv_one]⟩
  · obtain ⟨m, hm, h⟩ := ha
    exact ⟨m, hm, by rw [← map_pow, h, map_one]⟩
  · rintro ⟨m, hm, h⟩
    exact ⟨k * m, Nat.mul_pos hk hm, by rw [pow_mul, h]⟩
  · rintro ⟨m, hm, h⟩
    refine ⟨k * m, Nat.mul_pos hk hm, ?_⟩
    rw [pow_mul, h, norm_pow, ofReal_pow, ← pow_mul]
  · refine ⟨2 * q.den, by positivity, ?_⟩
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨q.num, ?_⟩
    have hq : (q : ℂ) = q.num / q.den := by exact_mod_cast (Rat.num_div_den q).symm
    have hd : (q.den : ℂ) ≠ 0 := by exact_mod_cast q.den_nz
    rw [hq]
    field_simp
    push_cast
    ring
  · have := hab.mul hb.inv
    rwa [mul_inv_cancel_right₀ hb0] at this

end GlobalTheory.Phase.Calc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EqOfSiegelThetaSeriesRationalEq
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW

theorem exists_int_div_of_intM {κ ι : Type} (R S : ℕ) (hR : 0 < R) (hS : 0 < S)
    (x : Matrix κ ι ℚ) (h : IntM ((R : ℚ) • x)) :
    ∃ s : κ × ι → ℤ, (Matrix.of fun k i => (s (k, i) : ℚ) / ((R * S : ℕ) : ℚ)) = x := by
  have h' : ∀ p : κ × ι, ∃ n : ℤ, (n : ℚ) = (R : ℚ) * x p.1 p.2 := by
    intro p
    have := h p.1 p.2
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
    exact ⟨n, by simpa using hn⟩
  choose n hn using h'
  refine ⟨fun p => n p * S, ?_⟩
  ext k i
  have hR' : (R : ℚ) ≠ 0 := by exact_mod_cast hR.ne'
  have hS' : (S : ℚ) ≠ 0 := by exact_mod_cast hS.ne'
  simp only [Matrix.of_apply]
  push_cast
  rw [hn (k, i)]
  field_simp

theorem eq_of_thS_eq : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (φ ψ : Matrix κ ι ℚ → ℂ), IsSB φ → IsSB ψ → ∀ τ ∈ Siegel ι, (∀ ζ, thS φ τ ζ = thS ψ τ ζ) → φ = ψ := by
  intro κ ι _ _ _ φ ψ hφ hψ τ hτ h
  obtain ⟨R, hR, hRφ, -⟩ := id hφ
  obtain ⟨S, hS, hSψ, -⟩ := id hψ
  have hN : (((R * S : ℕ) : ℚ)) ≠ 0 := by exact_mod_cast (Nat.mul_pos hR hS).ne'
  have hNC : (((R * S : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast (Nat.mul_pos hR hS).ne'
  let e : (κ × ι → ℤ) → Matrix κ ι ℚ := fun s =>
    Matrix.of fun k i => (s (k, i) : ℚ) / ((R * S : ℕ) : ℚ)
  have he : Function.Injective e := by
    intro s t hst
    funext p
    have := congrFun (congrFun hst p.1) p.2
    simp only [e, Matrix.of_apply] at this
    have := (div_left_inj' hN).1 this
    exact_mod_cast this
  have hrange : ∀ x, φ x - ψ x ≠ 0 → x ∈ Set.range e := by
    intro x hx
    by_cases h1 : φ x = 0
    · have h2 : ψ x ≠ 0 := by
        intro h2; exact hx (by rw [h1, h2, sub_zero])
      obtain ⟨s, hs⟩ := exists_int_div_of_intM S R hS hR x (hSψ x h2)
      exact ⟨s, by rw [← hs, Nat.mul_comm S R]⟩
    · exact exists_int_div_of_intM R S hR hS x (hRφ x h1)
  let E : (κ → ι → ℂ) → Matrix κ ι ℚ → ℂ := fun ζ x =>
    cexp (π * I * ∑ k, (qv (x k) ⬝ᵥ τ *ᵥ qv (x k) + 2 * (qv (x k) ⬝ᵥ ζ k)))
  have hsφ : ∀ ζ, Summable fun x => φ x * E ζ x := fun ζ =>
    (GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm κ ι φ hφ τ hτ ζ).of_norm
  have hsψ : ∀ ζ, Summable fun x => ψ x * E ζ x := fun ζ =>
    (GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm κ ι ψ hψ τ hτ ζ).of_norm
  have hs : ∀ ζ, Summable fun x => (φ x - ψ x) * E ζ x := fun ζ => by
    simpa only [sub_mul] using (hsφ ζ).sub (hsψ ζ)
  have hz : ∀ ζ, ∑' x, (φ x - ψ x) * E ζ x = 0 := fun ζ => by
    simp only [sub_mul]
    rw [(hsφ ζ).tsum_sub (hsψ ζ)]
    exact sub_eq_zero.2 (h ζ)
  have key := GlobalTheory.coeff_eq_zero_of_fourier_series_eq_zero (κ × ι)
    (fun s => (φ (e s) - ψ (e s)) * E 0 (e s))
    (((hs 0).comp_injective he).norm) (by
      intro y
      have h0 := hz (fun k i => ((R * S : ℕ) : ℂ) * (y (k, i) : ℂ))
      rw [← he.tsum_eq (f := fun x => (φ x - ψ x) * E (fun k i => ((R * S : ℕ) : ℂ) * (y (k, i) : ℂ)) x)
        (by
          intro x hx
          exact hrange x (left_ne_zero_of_mul hx))] at h0
      rw [← h0]
      refine tsum_congr fun s => ?_
      rw [mul_assoc]
      congr 1
      simp only [E]
      rw [← Complex.exp_add]
      congr 1
      have : ∀ k, qv (e s k) ⬝ᵥ (fun i => ((R * S : ℕ) : ℂ) * (y (k, i) : ℂ)) =
          ∑ i, (s (k, i) : ℂ) * (y (k, i) : ℂ) := by
        intro k
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [qv, e, Matrix.of_apply, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
        field_simp
      simp only [this, Pi.zero_apply, dotProduct_zero, mul_zero, add_zero, Finset.sum_add_distrib,
        ← Finset.mul_sum, Fintype.sum_prod_type]
      ring)
  funext x
  by_contra hx
  obtain ⟨s, rfl⟩ := hrange x (sub_ne_zero.2 hx)
  have := key s
  rcases mul_eq_zero.1 this with h1 | h1
  · exact hx (sub_eq_zero.1 h1)
  · exact Complex.exp_ne_zero _ h1

end GlobalTheory.SW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplecticActionOfPeriodLatticeMapStatement
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplectic_action_of_period_lattice_map : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ((ι → ℚ) × (ι → ℚ)) →ₗ[ℚ] ((ι → ℚ) × (ι → ℚ))), (∀ u v, (F u).1 ⬝ᵥ (F v).2 - (F u).2 ⬝ᵥ (F v).1 = u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1) → ∃ σ ∈ Matrix.symplecticGroup ι ℚ, ∀ τ ∈ Siegel ι, ∀ τ' M : Matrix ι ι ℂ, τ'.IsSymm → (∀ u, M *ᵥ (qv u.1 + τ *ᵥ qv u.2) = qv (F u).1 + τ' *ᵥ qv (F u).2) → τ' = spAct σ τ ∧ M = ((spDen σ τ)⁻¹)ᵀ := by
  first | exact @GlobalTheory.SymplecticPeriods.exists_symplectic_action | exact GlobalTheory.SymplecticPeriods.exists_symplectic_action | (intros; apply GlobalTheory.SymplecticPeriods.exists_symplectic_action <;> assumption)
end

