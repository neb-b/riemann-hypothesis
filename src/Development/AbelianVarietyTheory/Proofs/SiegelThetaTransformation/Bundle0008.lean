module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelThetaMulConjEqBlockTheta
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.ThetaProd

theorem hasLevel_mul {κ ι : Type} [Fintype κ] [Fintype ι] {R : ℕ} (S : ℕ)
    {φ : Matrix κ ι ℚ → ℂ} (h : HasLevel R φ) : HasLevel (S * R) φ := by
  refine ⟨fun x hx k i => ?_, fun x y hy => ?_⟩
  · have := (h.1 x hx k i).nsmul S
    simpa [mul_assoc] using this
  · have := h.2 x ((S : ℚ) • y) fun k i => by simpa using (hy k i).nsmul S
    rw [← this, smul_smul, Nat.cast_mul, mul_comm]

theorem isSB_prod {κ ι₁ ι₂ : Type} [Fintype κ] [Fintype ι₁] [Fintype ι₂]
    {φ₁ : Matrix κ ι₁ ℚ → ℂ} {φ₂ : Matrix κ ι₂ ℚ → ℂ} (h₁ : IsSB φ₁) (h₂ : IsSB φ₂) :
    IsSB (fun m : Matrix κ (ι₁ ⊕ ι₂) ℚ => φ₁ m.toCols₁ * conj (φ₂ (-m.toCols₂))) := by
  obtain ⟨R₁, hR₁, h₁⟩ := h₁
  obtain ⟨R₂, hR₂, h₂⟩ := h₂
  have g₁ := hasLevel_mul R₂ h₁
  have g₂ := hasLevel_mul R₁ h₂
  rw [mul_comm] at g₁
  refine ⟨R₁ * R₂, by positivity, fun x hx k i => ?_, fun x y hy => ?_⟩
  · have a₁ := g₁.1 _ (left_ne_zero_of_mul hx)
    have a₂ := g₂.1 _ ((map_ne_zero conj).1 (right_ne_zero_of_mul hx))
    rcases i with i | i
    · exact a₁ k i
    · have := (a₂ k i).neg
      simpa [toCols₂] using this
  · have a₁ := g₁.2 x.toCols₁ y.toCols₁ fun k i => hy k (Sum.inl i)
    have a₂ := g₂.2 (-x.toCols₂) (-y.toCols₂) fun k i => (hy k (Sum.inr i)).neg
    have e₁ : (x + ((R₁ * R₂ : ℕ) : ℚ) • y).toCols₁ =
      x.toCols₁ + ((R₁ * R₂ : ℕ) : ℚ) • y.toCols₁ := rfl
    have e₂ : -(x + ((R₁ * R₂ : ℕ) : ℚ) • y).toCols₂ =
      -x.toCols₂ + ((R₁ * R₂ : ℕ) : ℚ) • (-y.toCols₂) := by
      rw [smul_neg, ← neg_add]; rfl
    simp only [e₁, e₂, a₁, a₂]

theorem fromBlocks_mem_siegel {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {τ₁ : Matrix ι₁ ι₁ ℂ} {τ₂ : Matrix ι₂ ι₂ ℂ} (h₁ : τ₁ ∈ Siegel ι₁) (h₂ : τ₂ ∈ Siegel ι₂) :
    Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj)) ∈ Siegel (ι₁ ⊕ ι₂) := by
  refine ⟨Matrix.IsSymm.fromBlocks h₁.1 (by simp) (h₂.1.map _).neg, ?_⟩
  have e : (Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj))).map Complex.im =
      Matrix.fromBlocks (τ₁.map Complex.im) 0 0 (τ₂.map Complex.im) := by
    ext (i | i) (j | j) <;> simp
  rw [e]
  refine Matrix.posDef_iff_dotProduct_mulVec.2
    ⟨Matrix.IsHermitian.fromBlocks h₁.2.isHermitian (by simp) h₂.2.isHermitian, fun x hx => ?_⟩
  obtain ⟨u, v, rfl⟩ : ∃ u v, x = Sum.elim u v :=
    ⟨x ∘ Sum.inl, x ∘ Sum.inr, (Sum.elim_comp_inl_inr x).symm⟩
  rw [star_trivial, fromBlocks_mulVec, sumElim_dotProduct_sumElim]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, add_zero, zero_add]
  have a := h₁.2.posSemidef.dotProduct_mulVec_nonneg u
  have b := h₂.2.posSemidef.dotProduct_mulVec_nonneg v
  rw [star_trivial] at a b
  by_cases hu : u = 0
  · have hv : v ≠ 0 := by
      rintro rfl
      apply hx
      rw [hu]
      ext (i | i) <;> rfl
    have := h₂.2.dotProduct_mulVec_pos hv
    rw [star_trivial] at this
    linarith
  · have := h₁.2.dotProduct_mulVec_pos hu
    rw [star_trivial] at this
    linarith

def colsEquiv (κ ι₁ ι₂ : Type) : Matrix κ (ι₁ ⊕ ι₂) ℚ ≃ Matrix κ ι₁ ℚ × Matrix κ ι₂ ℚ where
  toFun m := (m.toCols₁, -m.toCols₂)
  invFun p := fromCols p.1 (-p.2)
  left_inv m := by simp
  right_inv p := by simp

theorem row_exponent {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (τ₁ : Matrix ι₁ ι₁ ℂ) (τ₂ : Matrix ι₂ ι₂ ℂ) (ζ₁ : ι₁ → ℂ) (ζ₂ : ι₂ → ℂ) (v : ι₁ ⊕ ι₂ → ℚ) :
    qv v ⬝ᵥ Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj)) *ᵥ qv v +
        2 * (qv v ⬝ᵥ Sum.elim ζ₁ (star ζ₂)) =
      (qv (fun i => v (Sum.inl i)) ⬝ᵥ τ₁ *ᵥ qv (fun i => v (Sum.inl i)) +
        2 * (qv (fun i => v (Sum.inl i)) ⬝ᵥ ζ₁)) -
      conj (qv (fun i => -v (Sum.inr i)) ⬝ᵥ τ₂ *ᵥ qv (fun i => -v (Sum.inr i)) +
        2 * (qv (fun i => -v (Sum.inr i)) ⬝ᵥ ζ₂)) := by
  have h2 : conj (2 : ℂ) = 2 := map_ofNat _ 2
  simp [dotProduct, mulVec, qv, Fintype.sum_sum_type, h2]
  ring

theorem thS_mul_conj_thS : ∀ (κ ι₁ ι₂ : Type) [Fintype κ] [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] (φ₁ : Matrix κ ι₁ ℚ → ℂ) (φ₂ : Matrix κ ι₂ ℚ → ℂ), IsSB φ₁ → IsSB φ₂ → IsSB (fun m : Matrix κ (ι₁ ⊕ ι₂) ℚ => φ₁ m.toCols₁ * conj (φ₂ (-m.toCols₂))) ∧ ∀ τ₁ ∈ Siegel ι₁, ∀ τ₂ ∈ Siegel ι₂, Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj)) ∈ Siegel (ι₁ ⊕ ι₂) ∧ ∀ (ζ₁ : κ → ι₁ → ℂ) (ζ₂ : κ → ι₂ → ℂ), thS φ₁ τ₁ ζ₁ * conj (thS φ₂ τ₂ ζ₂) = thS (fun m : Matrix κ (ι₁ ⊕ ι₂) ℚ => φ₁ m.toCols₁ * conj (φ₂ (-m.toCols₂))) (Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj))) (fun k => Sum.elim (ζ₁ k) (star (ζ₂ k))) := by
  intro κ ι₁ ι₂ _ _ _ _ _ φ₁ φ₂ h₁ h₂
  refine ⟨isSB_prod h₁ h₂, fun τ₁ t₁ τ₂ t₂ => ⟨fromBlocks_mem_siegel t₁ t₂, fun ζ₁ ζ₂ => ?_⟩⟩
  have s₁ := SiegelSum.summable_norm_thetaTerm κ ι₁ φ₁ h₁ τ₁ t₁ ζ₁
  have s₂ := SiegelSum.summable_norm_thetaTerm κ ι₂ φ₂ h₂ τ₂ t₂ ζ₂
  unfold thS
  rw [Complex.conj_tsum, tsum_mul_tsum_of_summable_norm s₁
    (by simpa only [Complex.norm_conj] using s₂), ← (colsEquiv κ ι₁ ι₂).tsum_eq]
  refine tsum_congr fun m => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [row_exponent, Finset.sum_sub_distrib, mul_sub, ← map_sum]
  rw [map_mul, ← Complex.exp_conj, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I,
    sub_eq_add_neg, Complex.exp_add, mul_mul_mul_comm, mul_neg, neg_mul]
  rfl

end GlobalTheory.SW.ThetaProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelThetaTransformationLawMul
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.TransComp

theorem qm_mul {α β γ : Type} [Fintype β] (A : Matrix α β ℚ) (B : Matrix β γ ℚ) :
    qm (A * B) = qm A * qm B := by
  ext i j
  simp [qm, Matrix.mul_apply]

theorem qm_add {α β : Type} (A B : Matrix α β ℚ) : qm (A + B) = qm A + qm B := by
  ext i j
  simp [qm]

theorem qm_sub {α β : Type} (A B : Matrix α β ℚ) : qm (A - B) = qm A - qm B := by
  ext i j
  simp [qm]

theorem qm_transpose {α β : Type} (A : Matrix α β ℚ) : qm Aᵀ = (qm A)ᵀ := rfl

theorem qm_zero {α β : Type} : qm (0 : Matrix α β ℚ) = 0 := by
  ext i j
  simp [qm]

theorem qm_one {α : Type} [DecidableEq α] : qm (1 : Matrix α α ℚ) = 1 := by
  ext i j
  by_cases hij : i = j <;> simp [qm, Matrix.one_apply, hij]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem blocks {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (h : σ ∈ Matrix.symplecticGroup ι ℚ) :
    σ.toBlocks₂₁ᵀ * σ.toBlocks₁₁ - σ.toBlocks₁₁ᵀ * σ.toBlocks₂₁ = 0 ∧
      σ.toBlocks₂₂ᵀ * σ.toBlocks₁₁ - σ.toBlocks₁₂ᵀ * σ.toBlocks₂₁ = 1 := by
  have h' := h
  rw [← Matrix.fromBlocks_toBlocks σ] at h'
  obtain ⟨h1, -, h3⟩ := SymplecticGroup.fromBlocks_mem_iff.1 h'
  refine ⟨sub_eq_zero.2 h1.symm, ?_⟩

  have h4 := congrArg Matrix.transpose h3
  simpa [Matrix.transpose_sub, Matrix.transpose_mul] using h4

theorem mul_block (σ σ' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) :
    (σ' * σ).toBlocks₂₁ = σ'.toBlocks₂₁ * σ.toBlocks₁₁ + σ'.toBlocks₂₂ * σ.toBlocks₂₁ := by
  ext i j
  simp [Matrix.toBlocks₂₁, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.mul_apply,
    Fintype.sum_sum_type]

theorem key {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (h : σ ∈ Matrix.symplecticGroup ι ℚ)
    {τ : Matrix ι ι ℂ} (hτ : τ.IsSymm) (hd : (spDen σ τ).det ≠ 0) (hs : (spAct σ τ).IsSymm) :
    qm σ.toBlocks₁₁ = spAct σ τ * qm σ.toBlocks₂₁ + ((spDen σ τ)⁻¹)ᵀ := by
  have hu : IsUnit (spDen σ τ).det := isUnit_iff_ne_zero.mpr hd

  have h1 : (spDen σ τ)ᵀ * spAct σ τ = (qm σ.toBlocks₁₁ * τ + qm σ.toBlocks₁₂)ᵀ := by
    have hs' : (spAct σ τ)ᵀ = spAct σ τ := hs
    rw [← hs']
    unfold spAct
    rw [Matrix.transpose_mul, ← Matrix.mul_assoc, ← Matrix.transpose_mul,
      Matrix.nonsing_inv_mul _ hu, Matrix.transpose_one, Matrix.one_mul]
  have hτ' : τᵀ = τ := hτ
  obtain ⟨b1, b2⟩ := blocks h
  have e1 := congrArg qm b1
  have e2 := congrArg qm b2
  rw [qm_sub, qm_mul, qm_mul, qm_transpose, qm_transpose, qm_zero] at e1
  rw [qm_sub, qm_mul, qm_mul, qm_transpose, qm_transpose, qm_one] at e2
  have h2 : (spDen σ τ)ᵀ * (qm σ.toBlocks₁₁ - spAct σ τ * qm σ.toBlocks₂₁) = 1 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h1]
    unfold spDen
    rw [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
      hτ']
    calc (τ * (qm σ.toBlocks₂₁)ᵀ + (qm σ.toBlocks₂₂)ᵀ) * qm σ.toBlocks₁₁ -
          (τ * (qm σ.toBlocks₁₁)ᵀ + (qm σ.toBlocks₁₂)ᵀ) * qm σ.toBlocks₂₁
        = τ * ((qm σ.toBlocks₂₁)ᵀ * qm σ.toBlocks₁₁ - (qm σ.toBlocks₁₁)ᵀ * qm σ.toBlocks₂₁) +
          ((qm σ.toBlocks₂₂)ᵀ * qm σ.toBlocks₁₁ - (qm σ.toBlocks₁₂)ᵀ * qm σ.toBlocks₂₁) := by
          noncomm_ring
      _ = 1 := by rw [e1, e2, Matrix.mul_zero, zero_add]
  rw [Matrix.transpose_nonsing_inv, Matrix.inv_eq_right_inv h2]
  abel

end GlobalTheory.SW.TransComp


open GlobalTheory.SW.TransComp in
theorem GlobalTheory.SW.transS_comp : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (σ σ' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → σ' ∈ Matrix.symplecticGroup ι ℚ → ∀ φ ψ χ : Matrix κ ι ℚ → ℂ, TransS σ φ ψ → TransS σ' ψ χ → TransS (σ' * σ) φ χ := by
  intro κ ι _ _ _ σ σ' hσ hσ' φ ψ χ h1 h2 τ hτ ζ
  obtain ⟨hd, hmem, -, -, hcomp⟩ := _root_.GlobalTheory.SiegelAction.symplectic_action ι σ hσ τ hτ
  obtain ⟨hden, hact⟩ := hcomp σ' hσ'
  have hd' := (_root_.GlobalTheory.SiegelAction.symplectic_action ι σ' hσ' _ hmem).1
  rw [hden, hact]

  have hk := key hσ hτ.1 hd hmem.1
  have hD' : qm σ'.toBlocks₂₂ = spDen σ' (spAct σ τ) - qm σ'.toBlocks₂₁ * spAct σ τ := by
    rw [spDen, add_sub_cancel_left]
  have hinv' : (spDen σ' (spAct σ τ))⁻¹ * spDen σ' (spAct σ τ) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd')

  have hM : (spDen σ τ)⁻¹ * ((spDen σ' (spAct σ τ))⁻¹ * qm σ'.toBlocks₂₁) * ((spDen σ τ)⁻¹)ᵀ +
      (spDen σ τ)⁻¹ * qm σ.toBlocks₂₁ =
      (spDen σ' (spAct σ τ) * spDen σ τ)⁻¹ * qm (σ' * σ).toBlocks₂₁ := by
    rw [mul_block, qm_add, qm_mul, qm_mul, hk, hD', Matrix.mul_inv_rev]
    have inner : qm σ'.toBlocks₂₁ * (spAct σ τ * qm σ.toBlocks₂₁ + ((spDen σ τ)⁻¹)ᵀ) +
        (spDen σ' (spAct σ τ) - qm σ'.toBlocks₂₁ * spAct σ τ) * qm σ.toBlocks₂₁ =
        qm σ'.toBlocks₂₁ * ((spDen σ τ)⁻¹)ᵀ + spDen σ' (spAct σ τ) * qm σ.toBlocks₂₁ := by
      noncomm_ring
    rw [inner, Matrix.mul_add, Matrix.mul_assoc (spDen σ τ)⁻¹ (spDen σ' (spAct σ τ))⁻¹,
      Matrix.mul_assoc (spDen σ τ)⁻¹ (spDen σ' (spAct σ τ))⁻¹, ← Matrix.mul_assoc
      (spDen σ' (spAct σ τ))⁻¹ (spDen σ' (spAct σ τ)), hinv', Matrix.one_mul]
    simp only [Matrix.mul_assoc]
  have hq : ∀ v : ι → ℂ, v ⬝ᵥ ((spDen σ' (spAct σ τ) * spDen σ τ)⁻¹ * qm (σ' * σ).toBlocks₂₁) *ᵥ v =
      (v ᵥ* (spDen σ τ)⁻¹) ⬝ᵥ ((spDen σ' (spAct σ τ))⁻¹ * qm σ'.toBlocks₂₁) *ᵥ (v ᵥ* (spDen σ τ)⁻¹) +
        v ⬝ᵥ ((spDen σ τ)⁻¹ * qm σ.toBlocks₂₁) *ᵥ v := by
    intro v
    rw [← hM, Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  have hfun : (fun k => ζ k ᵥ* (spDen σ' (spAct σ τ) * spDen σ τ)⁻¹) =
      fun k => (ζ k ᵥ* (spDen σ τ)⁻¹) ᵥ* (spDen σ' (spAct σ τ))⁻¹ := by
    funext k
    rw [Matrix.mul_inv_rev, Matrix.vecMul_vecMul]
  rw [hfun, h2 _ hmem, h1 τ hτ ζ, Matrix.det_mul, mul_pow]
  simp only [hq, Finset.sum_add_distrib, mul_add, Complex.exp_add]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TsumSchwartzBruhatLevelEqSumResidueCosets
section
open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.FourierJ

open Matrix Complex in
open scoped ComplexConjugate Real in
private theorem rep_eq_of_neg_rep_add_rep_eq_smul_zm {κ ι : Type} {R : ℕ} (hR : 0 < R)
    {n n' : κ → ι → Fin (R * R)} (m : κ → ι → ℤ)
    (hm : -_root_.GlobalTheory.SW.FourierJ.rep R n + _root_.GlobalTheory.SW.FourierJ.rep R n' =
      R • _root_.GlobalTheory.SW.FourierJ.zm m) : n = n' := by
    funext k i
    have hk := congrFun (congrFun hm k) i
    simp only [_root_.GlobalTheory.SW.FourierJ.rep, Matrix.add_apply, Matrix.neg_apply,
      Matrix.of_apply, Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, nsmul_eq_mul] at hk
    have hRq : (R : ℚ) ≠ 0 := by positivity
    rw [neg_add_eq_sub, ← sub_div, div_eq_iff hRq] at hk
    have hzq : ((n' k i : ℕ) : ℚ) - (n k i : ℕ) = (R : ℚ) * R * m k i := by
      linear_combination hk
    have hz : ((n' k i : ℕ) : ℤ) - (n k i : ℕ) = (R : ℤ) * R * m k i := by
      exact_mod_cast hzq
    have hb : ((n' k i : ℕ) : ℤ) < (R : ℤ) * R := by exact_mod_cast (n' k i).isLt
    have ha : ((n k i : ℕ) : ℤ) < (R : ℤ) * R := by exact_mod_cast (n k i).isLt
    have h0 : ((n' k i : ℕ) : ℤ) - (n k i : ℕ) = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd ⟨m k i, hz⟩
      rw [abs_lt]
      constructor <;>
        linarith [Int.natCast_nonneg (n k i : ℕ), Int.natCast_nonneg (n' k i : ℕ)]
    exact Fin.ext (by omega)

open Matrix Complex in
open scoped ComplexConjugate Real in
private theorem exists_rep_add_natCast_smul_zm_of_intM_smul {κ ι : Type} [Fintype κ] [Fintype ι] {R : ℕ}
    (hR : 0 < R) (x : Matrix κ ι ℚ) (hx : _root_.GlobalTheory.SW.IntM (R • x)) :
    ∃ (n : κ → ι → Fin (R * R)) (m : κ → ι → ℤ),
      x = _root_.GlobalTheory.SW.FourierJ.rep R n + R • _root_.GlobalTheory.SW.FourierJ.zm m := by
  obtain ⟨M, hM⟩ := (_root_.GlobalTheory.SW.FourierJ.intM_iff _).mp hx
  have hRR : (0 : ℤ) < (R : ℤ) * R := by positivity
  have hRq : (R : ℚ) ≠ 0 := by positivity
  refine ⟨fun k i => ⟨(M k i % ((R : ℤ) * R)).toNat, ?_⟩, fun k i => M k i / ((R : ℤ) * R), ?_⟩
  · have h1 := Int.emod_nonneg (M k i) hRR.ne'
    have h2 := Int.emod_lt_of_pos (M k i) hRR
    have h3 : ((M k i % ((R : ℤ) * R)).toNat : ℤ) < (R : ℤ) * R := by
      rw [Int.toNat_of_nonneg h1]; exact h2
    exact_mod_cast h3
  · ext k i
    have hk := congrFun (congrFun hM k) i
    simp only [Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, Matrix.of_apply, nsmul_eq_mul] at hk
    simp only [_root_.GlobalTheory.SW.FourierJ.rep, Matrix.add_apply, Matrix.smul_apply,
      Matrix.of_apply, _root_.GlobalTheory.SW.FourierJ.zm, nsmul_eq_mul]
    have h1 := Int.emod_nonneg (M k i) hRR.ne'
    have hn : (((M k i % ((R : ℤ) * R)).toNat : ℕ) : ℚ) = ((M k i % ((R : ℤ) * R) : ℤ) : ℚ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h1]
    have hq : ((M k i % ((R : ℤ) * R) : ℤ) : ℚ) + (R : ℚ) * R * ((M k i / ((R : ℤ) * R) : ℤ) : ℚ)
        = (M k i : ℚ) := by
      have := Int.mul_ediv_add_emod (M k i) ((R : ℤ) * R)
      have h' : (R : ℚ) * R * ((M k i / ((R : ℤ) * R) : ℤ) : ℚ) +
          ((M k i % ((R : ℤ) * R) : ℤ) : ℚ) = (M k i : ℚ) := by
        exact_mod_cast this
      linear_combination h'
    have hx' : x k i = (M k i : ℚ) / R := by
      rw [eq_div_iff hRq]
      linear_combination hk
    rw [hx', hn, ← hq, add_div]
    congr 1
    rw [mul_assoc, mul_div_cancel_left₀ _ hRq]


open Matrix Complex in
open scoped ComplexConjugate Real in
theorem _root_.GlobalTheory.SW.FourierJ.tsum_level_eq_sum_cosets : ∀ (κ ι : Type) [Fintype κ] [Fintype ι]
    [DecidableEq κ]
    [DecidableEq ι] (R : ℕ) (φ F : Matrix κ ι ℚ → ℂ), 0 < R → _root_.GlobalTheory.SW.HasLevel R φ →
    Summable (fun x => φ x * F x) → ∑' x, φ x * F x =
      ∑ n : κ → ι → Fin (R * R), φ (_root_.GlobalTheory.SW.FourierJ.rep R n) *
        ∑' m : κ → ι → ℤ, F (_root_.GlobalTheory.SW.FourierJ.rep R n +
          (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zm m) := by
  intro κ ι _ _ _ _ R φ F hR hφ hsum
  have hRq : (R : ℚ) ≠ 0 := by positivity
  have hsmul : ∀ m : κ → ι → ℤ, (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zm m = R • _root_.GlobalTheory.SW.FourierJ.zm m :=
    fun m => Nat.cast_smul_eq_nsmul ℚ R _
  let e : (κ → ι → Fin (R * R)) × (κ → ι → ℤ) → Matrix κ ι ℚ := fun p =>
    _root_.GlobalTheory.SW.FourierJ.rep R p.1 + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zm p.2
  have he : Function.Injective e := by
    rintro ⟨n, m⟩ ⟨n', m'⟩ h
    simp only [e] at h
    have hn : n = n' := by
      apply rep_eq_of_neg_rep_add_rep_eq_smul_zm hR (m - m')
      ext k i
      have hk := congrFun (congrFun h k) i
      simp only [_root_.GlobalTheory.SW.FourierJ.rep, Matrix.add_apply, Matrix.neg_apply,
        Matrix.of_apply, Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, nsmul_eq_mul, smul_eq_mul,
        Pi.sub_apply] at hk ⊢
      push_cast
      linear_combination -hk
    subst hn
    have hm : m = m' := by
      funext k i
      have hk := congrFun (congrFun h k) i
      simp only [Matrix.add_apply, Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, Matrix.of_apply,
        smul_eq_mul, add_right_inj] at hk
      exact_mod_cast mul_left_cancel₀ hRq hk
    rw [hm]
  have hsupp : Function.support (fun x => φ x * F x) ⊆ Set.range e := by
    intro x hx
    have hφx : φ x ≠ 0 := left_ne_zero_of_mul (Function.mem_support.mp hx)
    obtain ⟨n, m, hnm⟩ := exists_rep_add_natCast_smul_zm_of_intM_smul hR x (hφ.1 x hφx)
    exact ⟨(n, m), by simp only [e, hsmul]; exact hnm.symm⟩
  rw [← he.tsum_eq hsupp]
  have hs2 : Summable fun p => φ (e p) * F (e p) := hsum.comp_injective he
  rw [hs2.tsum_prod' (fun n => hs2.comp_injective (by intro m m' h; simpa using h)),
    tsum_fintype]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  simp only [e]
  rw [hφ.2 _ _ ((_root_.GlobalTheory.SW.FourierJ.intM_iff _).mpr ⟨m, rfl⟩)]

end GlobalTheory.SW.FourierJ
end

