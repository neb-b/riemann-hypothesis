module

public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.Bundle0006
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.Bundle0005

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.AreaCmLNe
section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

theorem area_cmL_ne (a₀ : ℕ) (b₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0) :
    area (cmL a₀ b₀ dK ha hdK lam hlam) ≠ 0 := by
  unfold area cmL scalePair cmPair
  simp only
  have e : conj (lam * (a₀ : ℂ)) * (lam * cmTheta b₀ dK) =
      (((a₀ : ℝ) * Complex.normSq lam : ℝ) : ℂ) * cmTheta b₀ dK := by
    rw [map_mul, Complex.conj_natCast]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  have hth : (cmTheta b₀ dK).im = Real.sqrt dK / 2 := by
    simp [cmTheta]
  rw [e, Complex.im_ofReal_mul, hth]
  have h1 : (0 : ℝ) < a₀ := by exact_mod_cast ha
  have h2 : 0 < Complex.normSq lam := Complex.normSq_pos.mpr hlam
  have h3 : 0 < Real.sqrt dK := Real.sqrt_pos.mpr (by exact_mod_cast hdK)
  exact abs_ne_zero.mpr (by positivity)

theorem gram_G (L : PeriodPair) {n : Type} [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
    (g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (hIso : IsIsom (matH (blk4 h)) (stdH L (Fin 4 × n)) (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))) :
    (gmat g₁).transpose * bd4 h * (gmat g₁).map conj = (((area L : ℝ) : ℂ)⁻¹) • (1 : Matrix _ _ ℂ) := by
  ext u w
  have h1 := hIso (g₁.symm (Pi.single u 1)) (g₁.symm (Pi.single w 1))
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, stdH_apply] at h1
  have hl : ∑ i, (Pi.single u (1 : ℂ) : Fin 4 × n → ℂ) i * ((area L : ℝ) : ℂ)⁻¹ *
      conj ((Pi.single w (1 : ℂ) : Fin 4 × n → ℂ) i) =
      (((area L : ℝ) : ℂ)⁻¹ • (1 : Matrix (Fin 4 × n) (Fin 4 × n) ℂ)) u w := by
    by_cases huw : u = w
    · subst huw
      simp [Pi.single_apply, Matrix.one_apply]
    · simp [Pi.single_apply, Matrix.one_apply, huw]
      intro hi
      exact absurd hi.symm huw
  rw [hl] at h1
  rw [h1]
  simp only [matH, LinearMap.mk₂'ₛₗ_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, gmat, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem ratStep : RatStep := by
  intro a₀ b₀ c₀ dK ha hdK lam hlam hCm l _ hl5 hld hin n _ _ h Λ g₀ g₁ hLat hIso hIdx
  have hΛ : IsSelfDual (matH h) Λ := hLat.2.1
  set L := cmL a₀ b₀ dK ha hdK lam hlam with hL
  set G := gmat g₁ with hGdef
  set Gi : Matrix (Fin 4 × n) (Fin 4 × n) ℂ :=
    LinearMap.toMatrix' (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) with hGidef
  have hGGi : G * Gi = 1 := by
    rw [hGdef, hGidef, gmat_eq, ← LinearMap.toMatrix'_comp]
    have : ((g₁.symm : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ∘ₗ (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)))
        = LinearMap.id := by ext x; simp
    rw [this, LinearMap.toMatrix'_id]
  have hGiG : Gi * G = 1 := by
    rw [hGdef, hGidef, gmat_eq, ← LinearMap.toMatrix'_comp]
    have : ((g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ∘ₗ (g₁.symm : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)))
        = LinearMap.id := by ext x; simp
    rw [this, LinearMap.toMatrix'_id]
  have hint : ∀ T : Matrix (Fin 4 × n) (Fin 4 × n) ℂ, (∀ y ∈ pow4 Λ, Matrix.toLin' T y ∈ pow4 Λ) →
      ∀ x w, ∃ q₁ q₂ : ℚ, padicNorm l q₁ ≤ 1 ∧ padicNorm l q₂ ≤ 1 ∧ (Gi * T * G) x w = q₁ + q₂ * sq dK := by
    intro T hT x w
    rw [hGidef, hGdef, conj_matrix_apply]
    exact conj_entry_int hCm l hl5 hin h Λ hΛ g₁ hIso hIdx _ hT x w
  obtain ⟨w, hPu⟩ := exists_cols G Gi hGGi
  set P : Matrix n n ℂ := Matrix.of fun i j => G (0, i) (w j) with hP
  have hdetP : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  set Pinv := P⁻¹ with hPinv
  have hPP : P * Pinv = 1 := Matrix.mul_nonsing_inv P hdetP
  have hPP' : Pinv * P = 1 := Matrix.nonsing_inv_mul P hdetP
  set S : Matrix (Fin 4 × n) (Fin 4 × n) ℂ :=
    Matrix.of fun x (y : Fin 4 × n) => (Gi * (mv y.1 : Matrix (Fin 4 × n) (Fin 4 × n) ℂ) * G) x (w y.2) with hS
  clear_value S
  have hGS : G * S = bd4 P := by
    ext z ⟨a, j⟩
    have e := congrFun (congrFun (show G * (Gi * (mv a : Matrix (Fin 4 × n) (Fin 4 × n) ℂ) * G) =
      (mv a : Matrix (Fin 4 × n) (Fin 4 × n) ℂ) * G by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGGi, Matrix.one_mul]) z) (w j)
    rw [mv_mul_apply, Matrix.mul_apply] at e
    rw [Matrix.mul_apply]
    simp only [hS, Matrix.of_apply]
    rw [e]
    simp only [bd4, hP, Matrix.of_apply]
  have hSdef : S = Gi * bd4 P := by rw [← hGS, ← Matrix.mul_assoc, hGiG, Matrix.one_mul]
  set M := bd4 Pinv * G with hM
  clear_value M
  have hSM : S * M = 1 := by
    rw [hSdef, hM, Matrix.mul_assoc, ← Matrix.mul_assoc (bd4 P), bd4_mul, hPP, bd4_one, Matrix.one_mul, hGiG]
  have hMS : M * S = 1 := by
    rw [hSdef, hM, Matrix.mul_assoc, ← Matrix.mul_assoc G, hGGi, Matrix.one_mul, bd4_mul, hPP', bd4_one]
  have hSK : ∀ x y, S x y ∈ Kc dK hdK := fun x y => by
    obtain ⟨q₁, q₂, -, -, e⟩ := hint (mv y.1) (mv_pres Λ y.1) x (w y.2)
    exact ⟨q₁, q₂, by rw [hS]; exact e⟩
  have hMK : ∀ x y, M x y ∈ Kc dK hdK := by
    set S' : Matrix (Fin 4 × n) (Fin 4 × n) (Kc dK hdK) := Matrix.of fun x y => ⟨S x y, hSK x y⟩ with hS'
    have hS'map : S'.map (Kc dK hdK).subtype = S := by ext x y; rfl
    have hdetS : IsUnit S.det := by
      have e := congrArg Matrix.det hSM
      rw [Matrix.det_mul, Matrix.det_one] at e
      exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one e)
    have hdet : IsUnit S'.det := by
      have e : (Kc dK hdK).subtype S'.det = S.det := by rw [RingHom.map_det]; rfl
      refine isUnit_iff_ne_zero.mpr fun h0 => ?_
      rw [h0, map_zero] at e
      exact not_isUnit_zero (e ▸ hdetS)
    have hinv : S * (S'⁻¹).map (Kc dK hdK).subtype = 1 := by
      rw [← hS'map, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have e : M = (S'⁻¹).map (Kc dK hdK).subtype := by
      calc M = M * (S * (S'⁻¹).map (Kc dK hdK).subtype) := by rw [hinv, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, hMS, Matrix.one_mul]
    intro x y
    rw [e]
    exact (S'⁻¹ x y).2
  have hA : ((area L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast area_cmL_ne a₀ b₀ dK ha hdK lam hlam
  have hgram := gram_G L h g₁ hIso
  have hGi : Gi.transpose * Gi.map conj = ((area L : ℝ) : ℂ) • bd4 h := by
    have e1 : Gi.transpose * (G.transpose * bd4 h * G.map conj) * Gi.map conj = bd4 h := by
      have : Gi.transpose * (G.transpose * bd4 h * G.map conj) * Gi.map conj
          = (G * Gi).transpose * bd4 h * (G * Gi).map (starRingEnd ℂ) := by
        rw [Matrix.transpose_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
      rw [this, hGGi]; simp
    rw [hGdef] at e1
    rw [hgram, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at e1
    rw [← e1, smul_smul, mul_inv_cancel₀ hA, one_smul]
  set R : Matrix n n ℂ := ((area L : ℝ) : ℂ) • (P.transpose * h * P.map conj) with hR
  clear_value R
  have hbdR : bd4 R = S.transpose * S.map conj := by
    rw [hSdef, Matrix.transpose_mul, Matrix.map_mul, bd4_transpose, bd4_map _ (map_zero _),
      show bd4 P.transpose * Gi.transpose * (Gi.map (starRingEnd ℂ) * bd4 (P.map (starRingEnd ℂ)))
        = bd4 P.transpose * (Gi.transpose * Gi.map (starRingEnd ℂ)) * bd4 (P.map (starRingEnd ℂ)) by
          simp only [Matrix.mul_assoc],
      hGi, Matrix.mul_smul, Matrix.smul_mul, bd4_mul, bd4_mul, hR, bd4_smul]
  have hRK : ∀ i j, R i j ∈ Kc dK hdK := by
    intro i j
    have e : R i j = (S.transpose * S.map conj) (0, i) (0, j) := by rw [← hbdR]; simp [bd4]
    rw [e, Matrix.mul_apply]
    exact Subfield.sum_mem _ fun x _ => Subfield.mul_mem _ (hSK x (0, i)) (conj_mem_Kc (hSK x (0, j)))
  have hGramM : M.transpose * bd4 R * M.map conj = 1 := by
    rw [hbdR]
    calc M.transpose * (S.transpose * S.map conj) * M.map conj
        = (S * M).transpose * (S * M).map (starRingEnd ℂ) := by
          rw [Matrix.transpose_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hSM]; simp
  have hUeq : ∀ k : Fin 4, (bmv0 k : Matrix _ _ ℂ) * M = M * (Gi * bmv0 k * G) := by
    intro k
    calc (bmv0 k : Matrix _ _ ℂ) * M = bmv0 k * bd4 Pinv * G := by rw [hM, Matrix.mul_assoc]
      _ = bd4 Pinv * bmv0 k * G := by rw [blockDiag_mul_blockShift]
      _ = bd4 Pinv * (G * Gi) * bmv0 k * G := by rw [hGGi, Matrix.mul_one]
      _ = M * (Gi * bmv0 k * G) := by rw [hM]; simp only [Matrix.mul_assoc]
  have hMK' : ∀ x y, ∃ q₁ q₂ : ℚ, M x y = q₁ + q₂ * sq dK := hMK
  have hRK' : ∀ i j, ∃ q₁ q₂ : ℚ, R i j = q₁ + q₂ * sq dK := hRK
  choose M₁ M₂ hMd using hMK'
  choose R₁ R₂ hRd using hRK'
  have hkM : kmat dK (Matrix.of M₁) (Matrix.of M₂) = M := by
    ext x y; simp [kmat, hMd x y, mul_comm]
  have hkMc : kmat dK (Matrix.of M₁) (-Matrix.of M₂) = M.map conj := by
    ext x y; simp [kmat, hMd x y, sq_conj, mul_comm]
  have hkR : kmat dK (Matrix.of R₁) (Matrix.of R₂) = R := by
    ext x y; simp [kmat, hRd x y, mul_comm]
  refine ⟨lam • P, Matrix.of M₁, Matrix.of M₂, Matrix.of R₁, Matrix.of R₂, 1, padicNorm.one, ?_, ?_, ?_⟩
  · rw [hkM, bd4_smul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hlam, one_smul, hM, ← Matrix.mul_assoc,
      bd4_mul, hPP, bd4_one, Matrix.one_mul]
  · rw [hkM, hkR, hkMc, hGramM]; simp
  · intro k
    have := hint (bmv0 k) (blockShift_mapsTo Λ k)
    choose U₁ U₂ hU₁ hU₂ hUe using this
    refine ⟨Matrix.of U₁, Matrix.of U₂, fun x y => ⟨hU₁ x y, hU₂ x y⟩, ?_⟩
    rw [hkM, hUeq k]
    congr 1
    ext x y; simp [kmat, hUe x y, mul_comm]

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.LocMain
section
noncomputable section
open scoped BigOperators
open Matrix

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
open Formalism.L2.Th1.Top.FrP Jac

set_option maxHeartbeats 400000 in
theorem local_core' : LocCore := by
  intro l _ dK σ δ h5 hld hin hσ hδ hσδ n _ _ M₁ M₂ R₁ R₂ c hc hGram hmv
  set S := setup h5 dK hld hin σ hσ δ hδ hσδ with hS
  have hSσ : S.σ = σ := rfl
  set M := lmat δ M₁ M₂ with hM
  set Mb := lmat δ M₁ (-M₂) with hMb
  have hMσ : M.map σ = Mb := lmat_map_σ σ δ hσδ M₁ M₂
  have hMbσ : Mb.map σ = M := by rw [hMb, lmat_map_σ σ δ hσδ, neg_neg]
  have hc0 : (c : MaximalUnramifiedExtension l) ≠ 0 := by
    have : c ≠ 0 := by rintro rfl; simp at hc
    exact_mod_cast this
  set H₀ : Matrix n n (MaximalUnramifiedExtension l) := (c : MaximalUnramifiedExtension l)⁻¹ • (lmat δ R₁ R₂).map σ with hH₀

  have hE : Mbᵀ * bd4 H₀ * M = 1 := by
    have h1 := congrArg (fun X => X.map σ) hGram
    simp only [Matrix.map_mul, transpose_map, blockDiag_map', hMσ, hMbσ] at h1
    have h1' : ((c : MaximalUnramifiedExtension l) • (1 : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l))).map σ = (c : MaximalUnramifiedExtension l) • 1 := by
      refine Matrix.ext fun x y => ?_
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp
    rw [h1'] at h1
    rw [hH₀, bd4_smul, Matrix.mul_smul, Matrix.smul_mul, h1, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hE2 : Mbᵀ * bd4 (H₀.map σ)ᵀ * M = 1 := by
    have h1 := congrArg (fun X => (X.map σ)ᵀ) hE
    simp only [Matrix.map_mul, transpose_map, blockDiag_map', hMσ, hMbσ, transpose_mul, transpose_transpose,
      Matrix.map_one σ (map_zero σ) (map_one σ), transpose_one, bd4_transpose] at h1
    simpa [Matrix.mul_assoc] using h1

  set Z : Matrix n (Fin 4 × n) (MaximalUnramifiedExtension l) := what₂ M 0 with hZ
  set Zb : Matrix n (Fin 4 × n) (MaximalUnramifiedExtension l) := what₂ Mb 0 with hZb'
  have hZb : Z.map σ = Zb := Matrix.ext fun i w => congrFun (congrFun hMσ (0, i)) w
  have hZbσ : Zb.map σ = Z := Matrix.ext fun i w => congrFun (congrFun hMbσ (0, i)) w
  have hZZ : Z * (Zbᵀ * H₀) = 1 := by
    have h1 : M * (Mbᵀ * bd4 H₀) = 1 := mul_eq_one_comm.mp hE
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun h1 (0, i)) (0, j)
    rw [← Matrix.mul_assoc, mul_bd4_apply] at this
    rw [← Matrix.mul_assoc, Matrix.mul_apply]
    simp only [Matrix.one_apply, Prod.mk.injEq, true_and] at this
    rw [Matrix.one_apply]
    simpa [Matrix.mul_apply, hZ, hZb', what₂] using this
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l), Γ = Zbᵀ * H₀ * Z := ⟨_, rfl⟩

  choose U₁ U₂ hUint hUeq using hmv
  set U : Fin 4 → Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l) := fun b => lmat δ (U₁ b) (U₂ b) with hU
  have hUO : ∀ b x y, U b x y ∈ S.O := fun b x y => lmat_mem (dK := dK) (hδ := hδ) (U₁ b) (U₂ b) (hUint b) x y
  have hZc : ∀ b, what₂ M b = Z * U b := by
    intro b; refine Matrix.ext fun i w => ?_
    have := congrFun (congrFun (hUeq b) (0, i)) w
    rw [blockShift_mul_apply, if_pos rfl] at this
    exact this
  have hrowsN : ∀ b, what₂ (M * U 0) b = if b = 0 then Z else 0 := by
    intro b; refine Matrix.ext fun i w => ?_
    have := congrFun (congrFun (hUeq 0) (b, i)) w
    rw [blockShift_mul_apply] at this
    rw [what₂, ← this]
    split_ifs <;> rfl
  have hΓU : Γ = ((U 0).map σ)ᵀ * U 0 := by
    have hN : ((M * U 0).map σ)ᵀ * bd4 H₀ * (M * U 0) = ((U 0).map σ)ᵀ * U 0 := by
      rw [Matrix.map_mul, hMσ, transpose_mul]
      calc ((U 0).map σ)ᵀ * Mbᵀ * bd4 H₀ * (M * U 0) = ((U 0).map σ)ᵀ * (Mbᵀ * bd4 H₀ * M) * U 0 := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hE, Matrix.mul_one]
    rw [← hN, transpose_mul_blockDiag_mul, Fin.sum_univ_four]
    have hr : ∀ b, what₂ ((M * U 0).map σ) b = (what₂ (M * U 0) b).map σ := fun b => rfl
    simp only [hr, hrowsN]
    simp [hZb, hΓ]
  have hΓI : S.IntM Γ := by
    intro w w'
    rw [hΓU, Matrix.mul_apply]
    exact S.O.sum_mem fun k _ => S.O.mul_mem (S.hσO _ (hUO 0 k w)) (hUO 0 k w')
  have hΓH : S.Herm Γ := by
    intro w w'
    rw [hΓU]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hSσ, Matrix.mul_apply, transpose_apply, Matrix.map_apply, map_sum, map_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := S.hσσ _ (hUO 0 k w)
    rw [hSσ] at h
    rw [h]
    ring
  have hidem : Γ * Γ = Γ := by
    calc Γ * Γ = Zbᵀ * H₀ * (Z * (Zbᵀ * H₀)) * Z := by simp only [hΓ, Matrix.mul_assoc]
      _ = Γ := by rw [hZZ, Matrix.mul_one, hΓ]
  have hΓUM : S.UM Γ := by
    intro x hx hNU
    choose y hyO hy using hNU
    refine ⟨y, hyO, ?_⟩
    have hΓx : Γ *ᵥ x = S.p • y := funext fun i => by rw [hy i]; rfl
    have h2 : Γ *ᵥ (Γ *ᵥ x) = Γ *ᵥ x := by rw [mulVec_mulVec, hidem]
    rw [hΓx, mulVec_smul] at h2
    rw [hΓx, h2]
  obtain ⟨k, v, hvI, hvo, hvs⟩ := S.jac Γ hΓI hΓH hΓUM
  clear_value Z Zb H₀ M Mb

  set A : Matrix (Fin 4 × n) (Fin k) (MaximalUnramifiedExtension l) := Matrix.of fun w c => v c w with hA
  have hAO : ∀ w c, A w c ∈ S.O := fun w c => hvI c w
  have hAo : (A.map σ)ᵀ * Γ * A = 1 := by
    refine Matrix.ext fun c c' => ?_
    rw [Matrix.one_apply, ← hvo c c']
    simp only [JSetup.hf, JSetup.cv, hSσ, dotProduct, mulVec, Matrix.mul_apply, transpose_apply,
      Matrix.map_apply, hA, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hAs : Γ * A * ((A.map σ)ᵀ * Γ) = Γ := by
    conv_rhs => rw [← hvs]
    refine Matrix.ext fun w w' => ?_
    rw [Matrix.mul_apply, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [vecMulVec_apply, Matrix.mul_apply, mulVec, dotProduct, vecMul, JSetup.cv, hSσ, transpose_apply,
      Matrix.map_apply, hA, Matrix.of_apply]
  obtain ⟨V, hV⟩ : ∃ V : Matrix n (Fin k) (MaximalUnramifiedExtension l), V = Z * A := ⟨_, rfl⟩
  obtain ⟨Ti₀, hTi₀⟩ : ∃ Ti₀ : Matrix (Fin k) n (MaximalUnramifiedExtension l), Ti₀ = (V.map σ)ᵀ * H₀ := ⟨_, rfl⟩
  have hVσ : V.map σ = Zb * A.map σ := by rw [hV, Matrix.map_mul, hZb]
  have hTZ : Ti₀ * Z = (A.map σ)ᵀ * Γ := by
    rw [hTi₀, hVσ, transpose_mul, hΓ]; simp only [Matrix.mul_assoc]
  have hTV : Ti₀ * V = 1 := by
    rw [hV, ← Matrix.mul_assoc, hTZ, hAo]
  have hZΓ : Z * Γ = Z := by
    calc Z * Γ = Z * (Zbᵀ * H₀) * Z := by simp only [hΓ, Matrix.mul_assoc]
      _ = Z := by rw [hZZ, Matrix.one_mul]
  have hGZ : Zbᵀ * H₀ = Γ * (Zbᵀ * H₀) := by
    calc Zbᵀ * H₀ = Zbᵀ * H₀ * (Z * (Zbᵀ * H₀)) := by rw [hZZ, Matrix.mul_one]
      _ = Γ * (Zbᵀ * H₀) := by simp only [hΓ, Matrix.mul_assoc]
  have hTi₀' : Ti₀ = (A.map σ)ᵀ * (Zbᵀ * H₀) := by rw [hTi₀, hVσ, transpose_mul, Matrix.mul_assoc]
  have hVT : V * Ti₀ = 1 := by
    have s1 : V * Ti₀ = Z * A * ((A.map σ)ᵀ * (Zbᵀ * H₀)) := by rw [hV, hTi₀']
    have s2 : Z * A * ((A.map σ)ᵀ * (Zbᵀ * H₀)) = Z * Γ * A * ((A.map σ)ᵀ * (Γ * (Zbᵀ * H₀))) :=
      (congrArg (fun X => Z * A * ((A.map σ)ᵀ * X)) hGZ).trans
        (congrArg (fun X => X * A * ((A.map σ)ᵀ * (Γ * (Zbᵀ * H₀)))) hZΓ.symm)
    have s3 : Z * Γ * A * ((A.map σ)ᵀ * (Γ * (Zbᵀ * H₀))) = Z * (Γ * A * ((A.map σ)ᵀ * Γ)) * (Zbᵀ * H₀) := by
      simp only [Matrix.mul_assoc]
    have s4 : Z * (Γ * A * ((A.map σ)ᵀ * Γ)) * (Zbᵀ * H₀) = 1 := by rw [hAs, hZΓ, hZZ]
    exact s1.trans (s2.trans (s3.trans s4))

  have hk : Fintype.card n = k := card_eq_of_mul_eq_one V Ti₀ hVT hTV
  set e : Fin k ≃ n := (Fintype.equivFinOfCardEq hk).symm with he
  set T : Matrix n n (MaximalUnramifiedExtension l) := V.submatrix id e.symm with hT
  set Ti : Matrix n n (MaximalUnramifiedExtension l) := Ti₀.submatrix e.symm id with hTi
  have hTTi : T * Ti = 1 := by
    refine Matrix.ext fun i j => ?_
    have h1 := congrFun (congrFun hVT i) j
    rw [Matrix.mul_apply] at h1
    rw [← h1, Matrix.mul_apply]
    simp only [hT, hTi, submatrix_apply, id_eq]
    exact Equiv.sum_comp e.symm (fun c => V i c * Ti₀ c j)

  have hAσσ : (A.map σ).map σ = A := Matrix.ext fun w c => by
    have h := S.hσσ _ (hAO w c)
    rw [hSσ] at h
    simpa using h
  have hVσσ : (V.map σ).map σ = V := by rw [hVσ, Matrix.map_mul, hZbσ, hAσσ, hV]
  have hTi₀σ : (Ti₀.map σ)ᵀ * Ti₀ = (H₀.map σ)ᵀ := by
    have h1 : (Ti₀.map σ)ᵀ = (H₀.map σ)ᵀ * V := by
      rw [hTi₀, Matrix.map_mul, transpose_mul, transpose_map, transpose_transpose, hVσσ]
    rw [h1, Matrix.mul_assoc, hVT, Matrix.mul_one]
  have hTiσ : (Ti.map σ)ᵀ * Ti = (H₀.map σ)ᵀ := by
    rw [← hTi₀σ]
    refine Matrix.ext fun i j => ?_
    simp only [hTi, Matrix.mul_apply, transpose_apply, Matrix.map_apply, submatrix_apply, id_eq]
    exact Equiv.sum_comp e.symm (fun c => σ (Ti₀ c i) * Ti₀ c j)
  have hU1 : ((bd4 Ti * M).map σ)ᵀ * (bd4 Ti * M) = 1 := by
    rw [Matrix.map_mul, blockDiag_map', hMσ, transpose_mul, bd4_transpose]
    calc Mbᵀ * bd4 (Ti.map σ)ᵀ * (bd4 Ti * M) = Mbᵀ * (bd4 (Ti.map σ)ᵀ * bd4 Ti) * M := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [blockDiag_mul', hTiσ]; exact hE2

  have hγ : ∀ b i w, (bd4 Ti * M) (b, i) w = ((A.map σ)ᵀ * Γ * U b) (e.symm i) w := by
    intro b i w
    rw [blockDiag_mul_apply']
    have h1 : (Ti * what₂ M b) i w = ∑ j, Ti i j * M (b, j) w := rfl
    rw [← h1, hZc b, ← Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun w' _ => ?_
    congr 1
    show (Ti₀ * Z) (e.symm i) w' = _
    rw [hTZ]
  have hγO : ∀ x y, (bd4 Ti * M) x y ∈ S.O := by
    rintro ⟨b, i⟩ w
    rw [hγ, Matrix.mul_apply]
    refine S.O.sum_mem fun w' _ => S.O.mul_mem ?_ (hUO b w' w)
    rw [Matrix.mul_apply]
    refine S.O.sum_mem fun x _ => S.O.mul_mem ?_ (hΓI x w')
    have h := S.hσO _ (hAO x (e.symm i))
    rw [hSσ] at h
    simpa using h
  refine ⟨T, Ti, hTTi, ?_⟩
  unfold IsUnitaryK
  refine ⟨fun a b => ⟨norm_le_one_of_mem (dK := dK) (hδ := hδ) (hγO a b), ?_⟩, fun a b => ?_⟩
  · have h := S.hσσ _ (hγO a b)
    rwa [hSσ] at h
  · have h := congrFun (congrFun hU1 a) b
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simp only [transpose_apply, Matrix.map_apply] at h
    exact h

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
end
end

