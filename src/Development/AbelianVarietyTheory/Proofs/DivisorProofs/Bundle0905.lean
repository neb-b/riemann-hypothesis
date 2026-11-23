module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ColumnDataLaws
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VacuumCharacterDeterminant
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfIsONFr
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0883
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0853
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DsumEqZeroOfFibreSums
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0864
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockConj
section
open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdTh
open GlobalTheory.SW hiding Level
open GlobalTheory.IndefiniteRowSideFullHecke.VacuumCharacterDeterminant (detPos detNeg vacChar)
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameEquiv.CompactMove

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
  (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)

theorem thR_of_perC (x x' : Frame X.Ψ r) (M : Matrix (Fin g) (Fin g) ℂ) (hM : IsUnit M.det)
    (h : ∀ u, (fun j => perC X x' u (idx j)) = M *ᵥ fun j => perC X x u (idx j))
    (φ : TF n g) (v : WR X n) :
    thR X bas idx φ x' v = (M.det⁻¹) ^ (n / 2) * thR X bas idx φ x v := by
  have hP : ∀ s, perMat X bas idx s x' = M * perMat X bas idx s x := by
    intro s
    ext i k
    exact congrFun (h fun (τ : X.Ψ) => Data.emb τ.1 (bas (Pi.single (s k) 1))) i
  have hH : hMat X bas idx x' = hMat X bas idx x * M⁻¹ := by
    rw [hMat, hP, Matrix.mul_inv_rev, hMat]
  have hT : tauMat X bas idx x' = tauMat X bas idx x := by
    rw [tauMat, hH, hP, Matrix.mul_assoc, ← Matrix.mul_assoc M⁻¹, nonsing_inv_mul _ hM, Matrix.one_mul, tauMat]
  have hI : imInv X bas idx x' = imInv X bas idx x := by rw [imInv, imInv, hT]
  have hz : ∀ b, hMat X bas idx x' *ᵥ zR X idx x' v b = hMat X bas idx x *ᵥ zR X idx x v b := by
    intro b
    have : zR X idx x' v b = M *ᵥ zR X idx x v b := h fun τ => v τ b
    rw [this, hH, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hM, Matrix.mul_one]
  simp only [thR, gaussR, GlobalTheory.Dict.hx, thA, hz, hT, hI]
  rw [hH, det_mul, det_nonsing_inv, Ring.inverse_eq_inv', mul_pow]
  ring

theorem thR_block (x x' : Frame X.Ψ r) (b : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (hb : ∀ τ, IsUnit (b τ).det)
    (hxb : ∀ τ, mat x' τ = mat x τ * b τ) (hc : ∀ τ, b τ * prFst r X.p0 = prFst r X.p0 * b τ)
    (φ : TF n g) (v : WR X n) :
    thR X bas idx φ x' v = (∏ τ, (((1 - prFst r X.p0) * b τ + prFst r X.p0).det /
      (prFst r X.p0 * b τ + (1 - prFst r X.p0)).det) ^ (n / 2)) * thR X bas idx φ x v := by
  classical
  set P := prFst r X.p0 with hP
  let N : X.Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => P * (b τ)ᵀ + (1 - P) * (b τ)⁻¹
  have hN : ∀ τ, (N τ).det ≠ 0 ∧ (N τ).det = (P * b τ + (1 - P)).det / ((1 - P) * b τ + P).det := fun τ =>
    det_tr_inv_block P (1 - P) (b τ) (hb τ) (by abel) (by
      rw [hP, prFst, diagonal_mul_diagonal]; congr 1; funext a; split_ifs <;> simp) (hc τ) (by
      rw [hP, prFst, diagonal_transpose])
  let e : Fin g ≃ Fin r × X.Ψ := idx.trans (Equiv.prodComm _ _)
  have hdet : ((blockDiagonal N).submatrix e e).det = ∏ τ, (N τ).det := by
    rw [det_submatrix_equiv_self, det_blockDiagonal]
  have main := thR_of_perC X bas idx x x' ((blockDiagonal N).submatrix e e)
    (by rw [hdet]; exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun τ _ => (hN τ).1)) (fun u => by
      funext j
      have h1 : ((blockDiagonal N).submatrix e e *ᵥ fun j => perC X x u (idx j)) j =
          ∑ p : Fin r × X.Ψ, blockDiagonal N (e j) p * perC X x u p.swap := by
        rw [← e.sum_comp]
        rfl
      rw [h1, Fintype.sum_prod_type]
      refine (perC_block X x x' (idx j).1 (b _) (hb _) (hxb _) (hc _) u (idx j).2).trans ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_eq_single (idx j).1]
      · exact congrArg (· * _) (blockDiagonal_apply_eq N (idx j).2 c (idx j).1).symm
      · intro τ _ hτ
        have : blockDiagonal N (e j) (c, τ) = 0 := blockDiagonal_apply_ne N (idx j).2 c hτ.symm
        rw [this, zero_mul]
      · simp) φ v
  rw [main, hdet, Finset.prod_pow, ← Finset.prod_inv_distrib]
  congr 2
  exact Finset.prod_congr rfl fun τ _ => by rw [(hN τ).2, inv_div]

end Classical

theorem det_block_conj {r : ℕ} (P m : Matrix (Fin r) (Fin r) ℂ) (hPP : P * P = P) (hP : Pᴴ = P)
    (hP' : P.map conj = P) (hc : m * P = P * m) (hm : mᴴ * m = 1) :
    (P * m.map conj + (1 - P)).det = (P * m + (1 - P)).det⁻¹ := by
  have h1 : (P * m + (1 - P))ᴴ * (P * m + (1 - P)) = 1 := by
    have a1 : mᴴ * (P * m) = P := by rw [← hc, ← Matrix.mul_assoc, hm, Matrix.one_mul]
    have a2 : ∀ y : Matrix (Fin r) (Fin r) ℂ, P * (P * y) = P * y := fun y => by rw [← Matrix.mul_assoc, hPP]
    simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hP,
      Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc, a1, a2, hPP]
    abel
  have h2 : P * m.map conj + (1 - P) = (starRingEnd ℂ).mapMatrix (P * m + (1 - P)) := by
    rw [map_add (f := _), map_mul, map_sub, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hP']
  have h3 := congrArg det h1
  rw [det_mul, det_conjTranspose, det_one] at h3
  rw [h2, ← RingHom.map_det]
  exact eq_inv_of_mul_eq_one_left h3

theorem blocks {r p : ℕ} (G B k : Matrix (Fin r) (Fin r) ℂ) (S : Matrix (Fin r) (Fin r) ℂ)
    (hS : S = (2 : ℂ) • prFst r p - 1) (hSS : S * S = 1) (hB : Bᴴ * G * B = S) (hk : kᴴ * G * k = G)
    (hc : k * (B * S * B⁻¹) = B * S * B⁻¹ * k) :
    ∃ m : Matrix (Fin r) (Fin r) ℂ, IsUnit (m.map conj).det ∧ k * B = B * m ∧
      m.map conj * prFst r p = prFst r p * m.map conj ∧
      ((1 - prFst r p) * m.map conj + prFst r p).det / (prFst r p * m.map conj + (1 - prFst r p)).det =
        detPos (B * S * B⁻¹) k * (detNeg (B * S * B⁻¹) k)⁻¹ := by
  have hu := GlobalTheory.Ker.ONBasis.isUnit_det hSS hB
  have hPP : prFst r p * prFst r p = prFst r p := by
    rw [prFst, diagonal_mul_diagonal]; congr 1; funext a; split_ifs <;> simp
  have hPc : (prFst r p).map conj = prFst r p := by
    ext a c
    simp only [prFst, map_apply, diagonal_apply]
    split_ifs <;> simp
  have hPH : (prFst r p)ᴴ = prFst r p := by
    rw [prFst, diagonal_conjTranspose]; congr 1; funext a; simp only [Pi.star_apply]; split_ifs <;> simp
  generalize prFst r p = P at *
  have e0 : B * S * B⁻¹ * B = B * S := by rw [Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]
  generalize B * S * B⁻¹ = s at *
  obtain ⟨h1, h2, h3⟩ := block_of_inv P B k (-s) hu (by rw [Matrix.neg_mul, e0, hS])
    (by rw [Matrix.neg_mul, ← Matrix.mul_assoc, ← hc, Matrix.mul_assoc, e0, hS, Matrix.mul_assoc])
  have hkB : k * B = B * (B⁻¹ * (k * B)) := (mul_nonsing_inv_cancel_left _ _ hu).symm
  generalize B⁻¹ * (k * B) = m at *
  have hmS : m * S = S * m := by
    rw [hS, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, h1, Matrix.mul_one, Matrix.one_mul]
  have hm1 : mᴴ * S * m = S := by
    calc mᴴ * S * m = (B * m)ᴴ * G * (B * m) := by
          rw [← hB, conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Bᴴ * (kᴴ * G * k) * B := by rw [← hkB, conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = S := by rw [hk, hB]
  have hm : mᴴ * m = 1 := by
    calc mᴴ * m = mᴴ * S * m * S := by
          rw [Matrix.mul_assoc, hmS, Matrix.mul_assoc, ← Matrix.mul_assoc S, hSS, Matrix.one_mul]
      _ = 1 := by rw [hm1, hSS]
  have d1 := det_block_conj P m hPP hPH hPc h1 hm
  have d2 := det_block_conj (1 - P) m
    (by rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hPP]; abel)
    (by rw [conjTranspose_sub, conjTranspose_one, hPH])
    (by
      change (starRingEnd ℂ).mapMatrix (1 - P) = _
      rw [map_sub, map_one, RingHom.mapMatrix_apply, hPc])
    (by rw [Matrix.mul_sub, Matrix.sub_mul, h1, Matrix.mul_one, Matrix.one_mul]) hm
  rw [sub_sub_cancel] at d2
  refine ⟨m, ?_, hkB, ?_, ?_⟩
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (Matrix.isUnit_det_of_left_inverse hm).map _
  · rw [← hPc, ← Matrix.map_mul, ← Matrix.map_mul, h1]
  · rw [d1, d2, ← h2, ← h3, detNeg, detPos, detPos]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_neg,
      Matrix.neg_mul, Matrix.mul_one, Matrix.one_mul, hc, sub_neg_eq_add, ← sub_eq_add_neg]
    rw [div_eq_mul_inv, inv_inv, mul_comm]

theorem Th_mvB (D : D7) (S T : HSp D) (C : GlobalTheory.Ker.Ctx S T) (B : C.Bas) (hB : C.IsB B) (k : GA D T)
    (_hk : k ∈ GinfC T)
    (hc : ∀ τ, compAt C.θ τ (Formalism.L2.Theta.mt T k) * C.sB B τ = C.sB B τ * compAt C.θ τ (Formalism.L2.Theta.mt T k))
    (φ : TF S.rank C.g) (hφ : GlobalTheory.SW.IsSB φ) :
    C.Th (C.xB (C.mvB k B)) φ = vacChar C.θ T (C.sB B) S.rank (fun _ => 0) k • C.Th (C.xB B) φ := by
  have hdom : ∀ A, C.IsB A → C.xB A ∈ C.X.dom := fun A hA =>
    GlobalTheory.Ker.ONBasis.mem_dom C.X (GlobalTheory.Ker.ONBasis.isONFr_xB C hA)
  have z1 := (GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ (hdom _ hB) φ hφ).1
  have z2 := (GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ (hdom _ (GlobalTheory.Ker.ONBasis.isB_mvB C hB k)) φ hφ).1
  obtain ⟨-, l1, l2⟩ := GlobalTheory.ThetaSpace.theta_space_laws D S T C
  refine (l1 _ _ z2.1 ((l2 _ z1.1).1 _)).2 fun w hw => ?_
  choose m m1 m2 m3 m4 using fun τ => blocks (p := C.X.p0) (gramAt D T τ) (B τ)
    (compAt C.θ τ (Formalism.L2.Theta.mt T k)) (sgnM C.X) (sgnM_eq C.X) (GlobalTheory.Ker.ONBasis.sgnM_sq C.X) (hB τ)
    (GlobalTheory.Ker.ONBasis.compAt_unitary C τ k) (hc τ)
  rw [z2.2 w hw, Pi.smul_apply, z1.2 w hw, smul_eq_mul,
    thR_block C.X C.bas C.idx (C.xB B) (C.xB (C.mvB k B)) (fun σ => (m (C.m.e.symm σ)).map conj)
      (fun σ => m1 _) (fun σ => ?_) (fun σ => m3 _)]
  · congr 1
    rw [← C.m.e.prod_comp, vacChar]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Equiv.symm_apply_apply, m4, zero_add, zero_sub, _root_.zpow_neg, zpow_natCast, zpow_natCast, mul_pow, inv_pow]
    rfl
  · obtain ⟨τ, rfl⟩ := C.m.e.surjective σ
    rw [GlobalTheory.Ker.ONBasis.mat_xB, GlobalTheory.Ker.ONBasis.mat_xB, Equiv.symm_apply_apply, ← Matrix.map_mul, ← m2]
    rfl

end GlobalTheory.FrameEquiv.CompactMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalSignOfPositiveEigenvectorOnePositive
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem diag_sign_of_pos_eigenvector : ∀ {n : ℕ} (A h g : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (W Z : GL (Fin n) ℂ) (lam : Fin n → ℂ) (d : Fin n → ℝ), A.det ≠ 0 → sigPosH hA = 1 → h = (W : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * (W : Matrix (Fin n) (Fin n) ℂ) → (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * (Z : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun i => (d i : ℂ)) → Function.Injective lam → g * (Z : Matrix (Fin n) (Fin n) ℂ) = (Z : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal lam → ∀ (i₀ : Fin n) (x : Fin n → ℂ), g *ᵥ x = lam i₀ • x → 0 < (star x ⬝ᵥ (h *ᵥ x)).re → 0 < d i₀ ∧ ∀ i, i ≠ i₀ → d i < 0 := by
  intro n A h g hA W Z lam d hdet hsig hh hZ hlam hg i₀ x hx hxpos
  have key : ∀ (N B : Matrix (Fin n) (Fin n) ℂ) (u u' : Fin n → ℂ),
      star (N *ᵥ u) ⬝ᵥ B *ᵥ (N *ᵥ u') = star u ⬝ᵥ (Nᴴ * B * N) *ᵥ u' := by
    intro N B u u'
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  set M : Matrix (Fin n) (Fin n) ℂ := (W : Matrix (Fin n) (Fin n) ℂ) * (Z : Matrix (Fin n) (Fin n) ℂ) with hM
  have hMd : Mᴴ * A * M = diagonal (fun i => (d i : ℂ)) := by
    rw [← hZ, hh, hM, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  obtain ⟨y, rfl⟩ : ∃ y, x = (Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ y :=
    ⟨(↑Z⁻¹ : Matrix (Fin n) (Fin n) ℂ) *ᵥ x, by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]⟩
  have hy : ∀ i, i ≠ i₀ → y i = 0 := by
    have h1 : (Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ (diagonal lam *ᵥ y)
        = (Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ (lam i₀ • y) := by
      rw [mulVec_mulVec, ← hg, ← mulVec_mulVec, hx, mulVec_smul]
    have h2 : diagonal lam *ᵥ y = lam i₀ • y := by
      have := congrArg (fun v => (↑Z⁻¹ : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) h1
      simpa only [mulVec_mulVec, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, one_mulVec] using this
    intro i hi
    have h3 := congrFun h2 i
    rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h3
    have h4 : (lam i - lam i₀) * y i = 0 := by rw [sub_mul, h3, sub_self]
    rcases mul_eq_zero.mp h4 with h5 | h5
    · exact absurd (hlam (sub_eq_zero.mp h5)) hi
    · exact h5
  have hform : star ((Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ y) ⬝ᵥ h *ᵥ ((Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ y)
      = ((d i₀ * Complex.normSq (y i₀) : ℝ) : ℂ) := by
    rw [key, hZ]
    simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
    rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hy i hi]) (by simp)]
    rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
    simp only [RCLike.star_def]
    ring
  rw [hform, Complex.ofReal_re] at hxpos
  have hd0 : 0 < d i₀ := by
    by_contra hc
    push_neg at hc
    nlinarith [Complex.normSq_nonneg (y i₀)]
  refine ⟨hd0, fun i hi => ?_⟩
  have hNM : ((↑Z⁻¹ : Matrix (Fin n) (Fin n) ℂ) * (↑W⁻¹ : Matrix (Fin n) (Fin n) ℂ)) * M = 1 := by
    rw [hM, Matrix.mul_assoc, ← Matrix.mul_assoc (↑W⁻¹ : Matrix (Fin n) (Fin n) ℂ), Units.inv_mul,
      Matrix.one_mul, Units.inv_mul]
  have hval : ∀ j k : Fin n, star (M *ᵥ Pi.single j 1) ⬝ᵥ A *ᵥ (M *ᵥ Pi.single k 1)
      = if j = k then (d j : ℂ) else 0 := by
    intro j k
    rw [key, hMd]
    by_cases hjk : j = k
    · subst hjk; simp [dotProduct, mulVec_diagonal, Pi.single_apply]
    · simp [dotProduct, mulVec_diagonal, Pi.single_apply, hjk]
      intro hkj; exact absurd hkj.symm hjk
  have hne : M *ᵥ Pi.single i (1 : ℂ) ≠ 0 := by
    intro h0
    have := congrArg (fun v => ((↑Z⁻¹ : Matrix (Fin n) (Fin n) ℂ) * (↑W⁻¹ : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) h0
    simp only [mulVec_mulVec, hNM, one_mulVec, mulVec_zero] at this
    have := congrFun this i
    simp at this
  have hneg := re_form_neg_of_orth_of_sigPosH_eq_one A hA hdet hsig (M *ᵥ Pi.single i₀ 1)
    (M *ᵥ Pi.single i 1) (by rw [hval]; simpa using hd0) (by rw [hval, if_neg (Ne.symm hi)]) hne
  rw [hval, if_pos rfl, Complex.ofReal_re] at hneg
  exact hneg

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorIndicatorMemHecke
section
noncomputable section

open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep

namespace GlobalTheory.SphGal

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem hasDiv_mul_mul {O : Subring L} {d : List ℤ} {g : GL (Fin n) L} (h : HasDiv O d g) {a b : GL (Fin n) L}
    (ha : a ∈ GLint (Fin n) O) (hb : b ∈ GLint (Fin n) O) : HasDiv O d (a * g * b) := by
  obtain ⟨ϖ, hϖ, a', ha', b', hb', e⟩ := h
  refine ⟨ϖ, hϖ, a * a', mul_mem ha ha', b' * b, mul_mem hb' hb, ?_⟩
  simp only [Units.val_mul, e, Matrix.mul_assoc]

theorem HasDiv.exists_eq_mul_mul {O : Subring L} (hO : ∀ x : L, Valued.v x ≤ 1 → x ∈ O) {d : List ℤ}
    {g s : GL (Fin n) L} (hg : HasDiv O d g) (hs : HasDiv O d s) :
    ∃ a b : GLint (Fin n) O, g = a * s * b := by
  first
  | exact @_root_.GlobalTheory.DoubleCosetDivisors.main
  | exact _root_.GlobalTheory.DoubleCosetDivisors.main
  | (apply _root_.GlobalTheory.DoubleCosetDivisors.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.DoubleCosetDivisors.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DoubleCosetDivisors.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DoubleCosetDivisors.main ..)

end Local

end GlobalTheory.SphGal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DsumEqZeroOfFibreSumsStatement
section
open MeasureTheory Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dsum_eq_zero_of_fibre_sums' : ∀ (H : Type) [Group H] (T P N L U : Subgroup H) (Ψ : H → ℂ), T ≤ P → N ≤ P → L ≤ P →
  (∀ p ∈ P, ∀ n ∈ N, p * n * p⁻¹ ∈ N) → (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) →
  (∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x) → (∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x) → (∀ x, x ∉ P → Ψ x = 0) →
  (∀ x ∈ P, (T ⊓ L.map (MulAut.conj x).toMonoidHom).relIndex (T ⊓ (L ⊔ N).map (MulAut.conj x).toMonoidHom) ≠ 0) →
  (∀ m ∈ P, ∑ᶠ q : H ⧸ (N ⊓ L), (if Quotient.out q ∈ N then Ψ (m * Quotient.out q) else 0) = 0) →
  GlobalTheory.OrbDesc.dsum T L U Ψ = 0 := by
  first | (exact @GlobalTheory.OrbDesc.dsum_eq_zero_of_fibre_sums) | (exact GlobalTheory.OrbDesc.dsum_eq_zero_of_fibre_sums) | (intros; apply GlobalTheory.OrbDesc.dsum_eq_zero_of_fibre_sums  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueNormSqOfSimilitudeHermitianSignature
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.EigenvalueNormSignature

theorem form_mulVec {n : ℕ} (M A : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    star (M *ᵥ x) ⬝ᵥ A *ᵥ (M *ᵥ y) = star x ⬝ᵥ (Mᴴ * A * M) *ᵥ y := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem det_ne_zero_of_sig {n : ℕ} {h : Matrix (Fin n) (Fin n) ℂ} (hh : h.IsHermitian)
    (hs : sigPosH hh + sigNegH hh = n) : h.det ≠ 0 := by
  intro hd
  rw [hh.det_eq_prod_eigenvalues] at hd
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hd
  have hi0 : hh.eigenvalues i = 0 := by simpa using hi
  unfold sigPosH sigNegH at hs
  have hdis : Disjoint (fun j : Fin n => 0 < hh.eigenvalues j) (fun j => hh.eigenvalues j < 0) := by
    rw [Pi.disjoint_iff]; intro j
    simp only [Prop.disjoint_iff]
    rintro ⟨h1, h2⟩; linarith
  rw [← Fintype.card_subtype_or_disjoint _ _ hdis] at hs
  have hlt : Fintype.card {j : Fin n // 0 < hh.eigenvalues j ∨ hh.eigenvalues j < 0} < Fintype.card (Fin n) :=
    Fintype.card_subtype_lt (p := fun j => 0 < hh.eigenvalues j ∨ hh.eigenvalues j < 0) (x := i)
      (by rw [hi0]; simp)
  rw [Fintype.card_fin] at hlt
  omega

end GlobalTheory.EigenvalueNormSignature

namespace GlobalTheory


open GlobalTheory.EigenvalueNormSignature in
theorem eig_norm_sq_of_similitude : ∀ (n : ℕ) (h Q Γ : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (Z : GL (Fin n) ℂ) (c : ℝ),
    sigPosH hh ≤ 1 → sigPosH hh + sigNegH hh = n → Q = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * Z → c ≠ 0 →
    Γᴴ * Q * Γ = (c : ℂ) • Q →
    (sigPosH hh = 0 ∨ ∃ (μ : ℂ) (x₀ : Fin n → ℂ), Γ *ᵥ x₀ = μ • x₀ ∧ 0 < (star x₀ ⬝ᵥ (Q *ᵥ x₀)).re) →
    ∀ (w : ℂ) (x : Fin n → ℂ), x ≠ 0 → Γ *ᵥ x = w • x → ‖w‖ ^ 2 = c := by
  intro n h Q Γ hh Z c hle hs hQ hc hΓ hcase w x hx hw
  have hdet := det_ne_zero_of_sig hh hs
  set Zm : Matrix (Fin n) (Fin n) ℂ := (Z : Matrix (Fin n) (Fin n) ℂ) with hZm
  have hZinj : ∀ v : Fin n → ℂ, v ≠ 0 → Zm *ᵥ v ≠ 0 := by
    intro v hv h0
    apply hv
    have : ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ (Zm *ᵥ v) = v := by
      rw [mulVec_mulVec, hZm, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one, one_mulVec]
    rw [← this, h0, mulVec_zero]
  have hB : ∀ u v : Fin n → ℂ, star u ⬝ᵥ Q *ᵥ v = star (Zm *ᵥ u) ⬝ᵥ h *ᵥ (Zm *ᵥ v) := by
    intro u v; rw [form_mulVec, hQ]

  have hsim : ∀ (a b : ℂ) (u v : Fin n → ℂ), Γ *ᵥ u = a • u → Γ *ᵥ v = b • v →
      (star a * b - c) * (star u ⬝ᵥ Q *ᵥ v) = 0 := by
    intro a b u v hu hv
    have e := form_mulVec Γ Q u v
    rw [hΓ, hu, hv] at e
    simp only [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_mulVec] at e
    rw [RCLike.star_def] at e ⊢
    linear_combination e
  have hnorm : ∀ a : ℂ, star a * a = (c : ℂ) → ‖a‖ ^ 2 = c := by
    intro a ha
    have : ((‖a‖ ^ 2 : ℝ) : ℂ) = c := by
      rw [← ha, RCLike.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact_mod_cast this
  by_cases hq : star x ⬝ᵥ Q *ᵥ x = 0
  · rcases hcase with h0 | ⟨μ, x₀, hμ, hpos⟩
    · have := herm_negDef_of_sigPosH_eq_zero h hh hdet h0 (Zm *ᵥ x) (hZinj x hx)
      rw [← hB, hq] at this; simp at this
    · have h1 : sigPosH hh = 1 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
        · have hx₀ : x₀ ≠ 0 := by rintro rfl; simp at hpos
          have := herm_negDef_of_sigPosH_eq_zero h hh hdet h0 (Zm *ᵥ x₀) (hZinj x₀ hx₀)
          rw [← hB] at this; linarith
        · exact h1
      have hμμ := hsim μ μ x₀ x₀ hμ hμ
      have hq0 : star x₀ ⬝ᵥ Q *ᵥ x₀ ≠ 0 := fun e => by rw [e] at hpos; simp at hpos
      have hμc : star μ * μ = (c : ℂ) := sub_eq_zero.mp ((mul_eq_zero.mp hμμ).resolve_right hq0)
      by_cases hb : star x₀ ⬝ᵥ Q *ᵥ x = 0
      · have := re_form_neg_of_orth_of_sigPosH_eq_one h hh hdet h1 (Zm *ᵥ x₀) (Zm *ᵥ x)
          (by rw [← hB]; exact hpos) (by rw [← hB]; exact hb) (hZinj x hx)
        rw [← hB, hq] at this; simp at this
      · have hμw := sub_eq_zero.mp ((mul_eq_zero.mp (hsim μ w x₀ x hμ hw)).resolve_right hb)
        have hμ0 : star μ ≠ 0 := by
          intro e; rw [e, zero_mul] at hμc; exact hc (by exact_mod_cast hμc.symm)
        have hwμ : w = μ := mul_left_cancel₀ hμ0 (hμw.trans hμc.symm)
        rw [hwμ]; exact hnorm μ hμc
  · exact hnorm w (sub_eq_zero.mp ((mul_eq_zero.mp (hsim w w x x hw hw)).resolve_right hq))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOnDoubleCosetOfEqOnArchimedeanSliceStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_on_doubleCoset_of_eq_on_archimedeanSlice : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b W : GA E (m + 1) → ℂ) (V : Subgroup (GL (Fin (m + 1)) (Af E))) (q : GA E (m + 1)), q ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) → GeneralLinearGroup.map (pInf E) q = 1 → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ V, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ u ∈ V, ∀ g, W (g * finGL E (m + 1) u) = W g) → (∀ y : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) → W (q * infGL E (m + 1) y) = b (q * infGL E (m + 1) y)) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), p ∈ GlobalTheory.JSW.MirPatch.cell V q → W p = b p := by
  first | exact @GlobalTheory.JSW.MirPatch.eq_on_cell_of_eq_on_slice | exact GlobalTheory.JSW.MirPatch.eq_on_cell_of_eq_on_slice | (intros; apply GlobalTheory.JSW.MirPatch.eq_on_cell_of_eq_on_slice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyLocalToGlobalAffineIndEtale
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.LocGlobIndEt

theorem eqv_of_comp_iso {R : Type} [CommRing R] {E E' E'' : Spc} (g : E ⟶ E') (e : E' ⟶ E'') [IsIso e] (F : Shv R)
    (h : Eqv R (g ≫ e) F) : Eqv R g F := by
  intro n
  have he : Function.Bijective (pull R e F n) := by
    refine Function.bijective_iff_has_inverse.2 ⟨pull R (inv e) F n, fun x => ?_, fun x => ?_⟩
    · rw [← pull_comp, IsIso.inv_hom_id, pull_id]
    · rw [← pull_comp, IsIso.hom_inv_id, pull_id]
  refine (Function.Bijective.of_comp_iff (pull R g F n) he).1 ?_
  have : (⇑(pull R g F n) ∘ ⇑(pull R e F n)) = ⇑(pull R (g ≫ e) F n) := funext fun x => (pull_comp R g e F n x).symm
  rw [this]
  exact h n

theorem main : ∀ (q : ℕ) (B : Type) [CommRing B] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of B)) [QuasiCompact f]
    [QuasiSeparated f], IsUnit (q : B) → ∀ i : ℤ, (∀ (A : Type) [CommRing A] [Algebra B A], SH A → IndEt B A →
      Eqv _ (sch.map (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap B A))))) (tw q i)) →
    Eqv _ (sch.map f) (tw q i) := by
  intro q B _ Y f _ _ _ i hyp
  refine GlobalTheory.T.etaleEquivalence_scheme_of_strictlyHenselian_stalks (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) Y (Spec (CommRingCat.of B)) (Spec (CommRingCat.of B)) f
    (𝟙 _) ?_
  intro O _ s hs
  obtain ⟨inst, hSH, hind, rfl⟩ := isStalk_affine B O s hs
  have key := @hyp O _ inst hSH hind
  refine eqv_of_comp_iso _ (sch.map (pullback.snd (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap B O))))) _ ?_
  rw [← sch.map_comp, pullback.lift_snd, Category.comp_id]
  generalize hf : f ≫ 𝟙 _ = f'
  rw [Category.comp_id] at hf
  subst hf
  exact key

end GlobalTheory.LocGlobIndEt
end
end

