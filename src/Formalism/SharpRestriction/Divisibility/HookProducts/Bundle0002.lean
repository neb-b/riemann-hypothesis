module

public import Mathlib
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.LocalRingCardinality.DataArith
public import Formalism.SharpRestriction.Divisibility.HookProducts.Bundle0001

@[expose] public section

-- bundled from Formalism.SharpRestriction.Divisibility.HookProducts.NormAtEqSqrtMajAt
section
open Module NumberField

noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts.FunSharp

variable {K : Type} [Field K] [NumberField K] [StarRing K]

private theorem norm_realize_sq_eq_sum_majAt_re {ι V : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module K V]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V) :
    ‖Formalism.HermitianLatticesTheory.realize b X x‖ ^ 2 = ∑ v, (Formalism.HermitianLatticesTheory.majAt b X v x x).re := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_prod_type, Formalism.HermitianLatticesTheory.majAt, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two]
  simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw, Complex.mul_re]
  ring

private theorem slope_map_eq_of_norm_eq {G E F : Type} [AddCommGroup G]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (α : G →+ E) (β : G →+ F) (hn : ∀ g, ‖β g‖ = ‖α g‖) (H : AddSubgroup G) :
    Formalism.F.slope (H.map β).toIntSubmodule = Formalism.F.slope (H.map α).toIntSubmodule := by
  have hz : ∀ g, β g = 0 ↔ α g = 0 := fun g => by rw [← norm_eq_zero, hn g, norm_eq_zero]
  have key : ∀ {E₁ E₂ : Type} [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
      (α₁ : G →+ E₁) (α₂ : G →+ E₂), (∀ g, ‖α₂ g‖ = ‖α₁ g‖) →
      DiscreteTopology (H.map α₁).toIntSubmodule → DiscreteTopology (H.map α₂).toIntSubmodule := by
    intro E₁ E₂ _ _ α₁ α₂ hn' hd
    rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff] at hd ⊢
    obtain ⟨ε, hε, h⟩ := hd
    refine ⟨ε, hε, fun y hy => ?_⟩
    obtain ⟨w, hw⟩ := y
    have hw' : w ∈ H.map α₂ := hw
    obtain ⟨g, hg, rfl⟩ := AddSubgroup.mem_map.1 hw'
    have hmem : α₁ g ∈ (H.map α₁).toIntSubmodule := AddSubgroup.mem_map_of_mem α₁ hg
    have h1 := h ⟨α₁ g, hmem⟩ (by
      have hy' := hy
      simp only [Subtype.dist_eq, ZeroMemClass.coe_zero, dist_zero_right] at hy' ⊢
      change ‖α₂ g‖ < ε at hy'
      change ‖α₁ g‖ < ε
      rw [← hn']
      exact hy')
    have h2 : α₁ g = 0 := congrArg Subtype.val h1
    have h3 : α₂ g = 0 := by rw [← norm_eq_zero, hn', h2, norm_zero]
    exact Subtype.ext h3
  have hd : DiscreteTopology (H.map β).toIntSubmodule ↔ DiscreteTopology (H.map α).toIntSubmodule :=
    ⟨key β α (fun g => (hn g).symm), key α β hn⟩
  by_cases hα : DiscreteTopology (H.map α).toIntSubmodule
  · obtain ⟨hc, hr⟩ := Formalism.HN.Rerealization.covol_rk_eq α β hn H hα (hd.2 hα)
    unfold Formalism.F.slope Formalism.F.deg
    rw [hc, hr]
  · have hβ : ¬ DiscreteTopology (H.map β).toIntSubmodule := fun h => hα (hd.1 h)
    unfold Formalism.F.slope Formalism.F.deg Formalism.F.covol
    rw [dite_eq_right hα, dite_eq_right hβ]
    simp

theorem muMax_tie (A : Formalism.BasicNotions.HLat K) {n : ℕ} (L : Submodule (𝓞 K) (Fin n → K))
    (XE : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (e : (Fin n → K) ≃ₗ[K] A.V)
    (hlat : A.L = L.map ((e : (Fin n → K) →ₗ[K] A.V).restrictScalars (𝓞 K)))
    (hmet : ∀ v x y, Formalism.HermitianLatticesTheory.majAt A.b A.X v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) XE v x y) :
    Formalism.HN.muMaxDef (Pi.basisFun K (Fin n)) XE L = A.muMax := by
  set f : (Fin n → K) →ₗ[𝓞 K] A.V := (e : (Fin n → K) →ₗ[K] A.V).restrictScalars (𝓞 K) with hf
  set g : A.V →ₗ[𝓞 K] (Fin n → K) := (e.symm : A.V →ₗ[K] (Fin n → K)).restrictScalars (𝓞 K) with hg
  have hgf : ∀ N : Submodule (𝓞 K) (Fin n → K), (N.map f).map g = N := by
    intro N
    rw [← Submodule.map_comp]
    have : g.comp f = LinearMap.id := by
      ext x; simp [hf, hg]
    rw [this, Submodule.map_id]
  have hfg : ∀ N : Submodule (𝓞 K) A.V, (N.map g).map f = N := by
    intro N
    rw [← Submodule.map_comp]
    have : f.comp g = LinearMap.id := by
      ext x; simp [hf, hg]
    rw [this, Submodule.map_id]
  have hn : ∀ x, ‖(Formalism.HermitianLatticesTheory.realize A.b A.X).comp f.toAddMonoidHom x‖ =
      ‖Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) XE x‖ := by
    intro x
    have h1 := norm_realize_sq_eq_sum_majAt_re A.b A.X (e x)
    have h2 := norm_realize_sq_eq_sum_majAt_re (Pi.basisFun K (Fin n)) XE x
    simp_rw [hmet] at h1
    show ‖Formalism.HermitianLatticesTheory.realize A.b A.X (e x)‖ = _
    rw [← Real.sqrt_sq (norm_nonneg (Formalism.HermitianLatticesTheory.realize A.b A.X (e x))),
      ← Real.sqrt_sq (norm_nonneg (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) XE x)), h1, h2]
  have hslope : ∀ N : Submodule (𝓞 K) (Fin n → K),
      Formalism.HN.slope (Formalism.HermitianLatticesTheory.realize A.b A.X) (N.map f) =
        Formalism.HN.slope (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) XE) N := by
    intro N
    unfold Formalism.HN.slope Formalism.HN.zl
    rw [Submodule.map_toAddSubgroup, AddSubgroup.map_map]
    exact slope_map_eq_of_norm_eq _ _ hn N.toAddSubgroup
  have hne : ∀ N : Submodule (𝓞 K) (Fin n → K), N ≠ ⊥ → N.map f ≠ ⊥ := by
    intro N hN h
    apply hN
    rw [← hgf N, h, Submodule.map_bot]
  have hne' : ∀ N : Submodule (𝓞 K) A.V, N ≠ ⊥ → N.map g ≠ ⊥ := by
    intro N hN h
    apply hN
    rw [← hfg N, h, Submodule.map_bot]
  have hmu : Formalism.HN.muMax (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) XE) L =
      Formalism.HN.muMax (Formalism.HermitianLatticesTheory.realize A.b A.X) A.L := by
    unfold Formalism.HN.muMax
    congr 1
    ext t
    constructor
    · rintro ⟨N, hNL, hN0, hs⟩
      refine ⟨N.map f, ?_, hne N hN0, (hslope N).trans hs⟩
      rw [hlat]; exact Submodule.map_mono hNL
    · rintro ⟨N, hNL, hN0, hs⟩
      refine ⟨N.map g, ?_, hne' N hN0, ?_⟩
      · rw [← hgf L]
        apply Submodule.map_mono
        rw [← hlat]; exact hNL
      · rw [← hslope, hfg]; exact hs
  unfold Formalism.BasicNotions.HLat.muMax Formalism.HN.muMaxDef
  rw [hmu]

end Formalism.MainNotions.DIV.HookProducts.FunSharp
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.HookProducts.RBTieOp
section
open Matrix NumberField Module

noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts.RBTie

section Op

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {VN VR : Type} [AddCommGroup VN] [Module K VN] [AddCommGroup VR] [Module K VR]
  {ιN ιR : Type} [Fintype ιN] [DecidableEq ιN] [Fintype ιR] [DecidableEq ιR] {d n : ℕ}

theorem dualFrame_inv {ι : Type} [Fintype ι] [DecidableEq ι] (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (hX : IsUnit (X v).det) : (Formalism.HN.dualFrame X v)⁻¹ = (X v)ᵀ := by
  show ((X v)ᵀ)⁻¹⁻¹ = (X v)ᵀ
  exact Matrix.nonsing_inv_nonsing_inv _ (by rw [Matrix.det_transpose]; exact hX)

theorem transpose_isom {ι κ : Type} [Fintype ι] [Fintype κ] (U : Matrix ι κ ℂ) : (Uᵀ)ᴴ * Uᵀ = (U * Uᴴ)ᵀ := by
  rw [Matrix.transpose_mul]
  rfl

theorem conjT_transpose_isom {ι κ : Type} [Fintype ι] [Fintype κ] (U : Matrix ι κ ℂ) : ((Uᴴ)ᵀ)ᴴ * (Uᴴ)ᵀ = (Uᴴ * U)ᵀ := by
  rw [Matrix.transpose_mul]
  congr 1
  ext i j
  simp

private theorem toMatrix_eq_transpose_mul_mul_of_comp (bN : Basis ιN K VN) (bR : Basis ιR K VR) (eN : (Fin d → K) ≃ₗ[K] VN)
    (eR : (Fin n → K) ≃ₗ[K] VR) (Bk : VN →ₗ[K] Module.Dual K VR)
    (B : (Fin d → K) →ₗ[K] Module.Dual K (Fin n → K)) (hB : ∀ x y, Bk (eN x) (eR y) = B x y) :
    LinearMap.toMatrix (Pi.basisFun K (Fin d)) (Pi.basisFun K (Fin n)).dualBasis B =
      (LinearMap.toMatrix (Pi.basisFun K (Fin n)) bR eR.toLinearMap)ᵀ *
        LinearMap.toMatrix bN bR.dualBasis Bk *
          LinearMap.toMatrix (Pi.basisFun K (Fin d)) bN eN.toLinearMap := by
  ext a b
  simp only [LinearMap.toMatrix_apply, Basis.dualBasis_repr, Matrix.mul_apply, Matrix.transpose_apply,
    LinearEquiv.coe_coe, Finset.sum_mul]
  rw [← hB]
  conv_lhs => rw [← bN.sum_repr (eN (Pi.basisFun K (Fin d) b)), ← bR.sum_repr (eR (Pi.basisFun K (Fin n) a))]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private theorem toMatrix_map_embedding_eq_cP_mul (bN : Basis ιN K VN) (bR : Basis ιR K VR) (eN : (Fin d → K) ≃ₗ[K] VN)
    (eR : (Fin n → K) ≃ₗ[K] VR) (Bk : VN →ₗ[K] Module.Dual K VR)
    (B : (Fin d → K) →ₗ[K] Module.Dual K (Fin n → K)) (hB : ∀ x y, Bk (eN x) (eR y) = B x y)
    (v : InfinitePlace K) :
    (LinearMap.toMatrix (Pi.basisFun K (Fin d)) (Pi.basisFun K (Fin n)).dualBasis B).map v.embedding =
      (cP bR eR v)ᵀ * (LinearMap.toMatrix bN bR.dualBasis Bk).map v.embedding * cP bN eN v := by
  rw [toMatrix_eq_transpose_mul_mul_of_comp bN bR eN eR Bk B hB, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  rfl

private theorem opNorm_toEuclideanLin_mul_le {l m o : Type} [Fintype l] [Fintype m] [Fintype o] [DecidableEq l]
    [DecidableEq m] [DecidableEq o] (A : Matrix l m ℂ) (B : Matrix m o ℂ) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (A * B))‖ ≤
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖ *
        ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin B)‖ := by
  have h := Matrix.l2_opNorm_mul A B
  simpa only [Matrix.l2_opNorm_def, LinearEquiv.trans_apply] using h

private theorem opNorm_toEuclideanLin_le_one_of_isometry {l m : Type} [Fintype l] [Fintype m] [DecidableEq l] [DecidableEq m]
    (W : Matrix l m ℂ) (hW : Wᴴ * W = 1) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin W)‖ ≤ 1 := by
  have h1 := Matrix.l2_opNorm_conjTranspose_mul_self W
  have h2 := Matrix.l2_opNorm_conjTranspose_mul_self (1 : Matrix m m ℂ)
  rw [hW] at h1
  rw [Matrix.conjTranspose_one, Matrix.one_mul] at h2
  simp only [Matrix.l2_opNorm_def, LinearEquiv.trans_apply] at h1 h2
  have hs := norm_nonneg (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin W))
  have ht := norm_nonneg (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (1 : Matrix m m ℂ)))
  have ht1 : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (1 : Matrix m m ℂ))‖ ≤ 1 := by
    nlinarith
  nlinarith

private theorem opNorm_toEuclideanLin_unitary_mul_mul_eq {a b c e : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype e]
    [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq e]
    (M : Matrix a b ℂ) (L : Matrix c a ℂ) (R : Matrix b e ℂ) (L' : Matrix a c ℂ) (R' : Matrix e b ℂ)
    (hL : Lᴴ * L = 1) (hR : Rᴴ * R = 1) (hL' : L'ᴴ * L' = 1) (hR' : R'ᴴ * R' = 1)
    (hLL : L' * L = 1) (hRR : R * R' = 1) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (L * M * R))‖ =
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖ := by
  apply le_antisymm
  · calc _ ≤ ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (L * M))‖ *
            ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin R)‖ := opNorm_toEuclideanLin_mul_le _ _
      _ ≤ (‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin L)‖ *
            ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖) *
            ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin R)‖ := by
          gcongr; exact opNorm_toEuclideanLin_mul_le _ _
      _ ≤ (1 * ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖) * 1 := by
          gcongr
          · exact opNorm_toEuclideanLin_le_one_of_isometry _ hL
          · exact opNorm_toEuclideanLin_le_one_of_isometry _ hR
      _ = _ := by ring
  · have hM : M = L' * (L * M * R) * R' := by
      calc M = (L' * L) * M * (R * R') := by rw [hLL, hRR, Matrix.one_mul, Matrix.mul_one]
        _ = L' * (L * M * R) * R' := by simp only [Matrix.mul_assoc]
    conv_lhs => rw [hM]
    calc _ ≤ ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (L' * (L * M * R)))‖ *
            ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin R')‖ := opNorm_toEuclideanLin_mul_le _ _
      _ ≤ (‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin L')‖ *
            ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (L * M * R))‖) *
            ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin R')‖ := by
          gcongr; exact opNorm_toEuclideanLin_mul_le _ _
      _ ≤ (1 * ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (L * M * R))‖) * 1 := by
          gcongr
          · exact opNorm_toEuclideanLin_le_one_of_isometry _ hL'
          · exact opNorm_toEuclideanLin_le_one_of_isometry _ hR'
      _ = _ := by ring

theorem opNormAt_tie (bN : Basis ιN K VN) (XN : InfinitePlace K → Matrix ιN ιN ℂ) (bR : Basis ιR K VR)
    (XR : InfinitePlace K → Matrix ιR ιR ℂ) (Xc : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (XE : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (eN : (Fin d → K) ≃ₗ[K] VN) (eR : (Fin n → K) ≃ₗ[K] VR)
    (hN : ∀ v x y, Formalism.HermitianLatticesTheory.majAt bN XN v (eN x) (eN y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) Xc v x y)
    (hR : ∀ v x y, Formalism.HermitianLatticesTheory.majAt bR XR v (eR x) (eR y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) XE v x y)
    (hXN : ∀ v, IsUnit (XN v).det) (hXR : ∀ v, IsUnit (XR v).det) (hXc : ∀ v, IsUnit (Xc v).det)
    (hXE : ∀ v, IsUnit (XE v).det)
    (Bk : VN →ₗ[K] Module.Dual K VR) (B : (Fin d → K) →ₗ[K] Module.Dual K (Fin n → K))
    (hB : ∀ x y, Bk (eN x) (eR y) = B x y) (v : InfinitePlace K) :
    Formalism.HN.opNormAt bN XN bR.dualBasis (Formalism.HN.dualFrame XR) v Bk =
      Formalism.HN.opNormAt (Pi.basisFun K (Fin d)) Xc (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame XE) v B := by
  have key : (Formalism.HN.dualFrame XE v)⁻¹ *
        (LinearMap.toMatrix (Pi.basisFun K (Fin d)) (Pi.basisFun K (Fin n)).dualBasis B).map v.embedding *
          Xc v =
      (cU bR XR XE eR v)ᵀ * ((Formalism.HN.dualFrame XR v)⁻¹ *
        (LinearMap.toMatrix bN bR.dualBasis Bk).map v.embedding * XN v) * cU bN XN Xc eN v := by
    have h1 := basisChange_mul_X (b := bR) (e := eR) (X := XE) (XA := XR) (v := v) (hXR v)
    have h2 := basisChange_mul_X (b := bN) (e := eN) (X := Xc) (XA := XN) (v := v) (hXN v)
    rw [dualFrame_inv XE v (hXE v), dualFrame_inv XR v (hXR v), toMatrix_map_embedding_eq_cP_mul bN bR eN eR Bk B hB v]
    simp only [Matrix.mul_assoc]
    rw [h2, ← Matrix.mul_assoc (XE v)ᵀ, ← Matrix.transpose_mul, h1, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  unfold Formalism.HN.opNormAt
  rw [key]
  symm
  refine opNorm_toEuclideanLin_unitary_mul_mul_eq _ _ _ ((cU bR XR XE eR v)ᴴ)ᵀ (cU bN XN Xc eN v)ᴴ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [transpose_isom, cU_mul_conj (h := hR) (hXA := hXR v) (hX := hXE v), Matrix.transpose_one]
  · exact cU_conj_mul (h := hN) (hX := hXc v)
  · rw [conjT_transpose_isom, cU_conj_mul (h := hR) (hX := hXE v), Matrix.transpose_one]
  · rw [Matrix.conjTranspose_conjTranspose]
    exact cU_mul_conj (h := hN) (hXA := hXN v) (hX := hXc v)
  · rw [← Matrix.transpose_mul, cU_mul_conj (h := hR) (hXA := hXR v) (hX := hXE v), Matrix.transpose_one]
  · exact cU_mul_conj (h := hN) (hXA := hXN v) (hX := hXc v)

theorem htMap_tie (bN : Basis ιN K VN) (XN : InfinitePlace K → Matrix ιN ιN ℂ) (bR : Basis ιR K VR)
    (XR : InfinitePlace K → Matrix ιR ιR ℂ) (Xc : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (XE : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (eN : (Fin d → K) ≃ₗ[K] VN) (eR : (Fin n → K) ≃ₗ[K] VR)
    (hN : ∀ v x y, Formalism.HermitianLatticesTheory.majAt bN XN v (eN x) (eN y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) Xc v x y)
    (hR : ∀ v x y, Formalism.HermitianLatticesTheory.majAt bR XR v (eR x) (eR y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) XE v x y)
    (hXN : ∀ v, IsUnit (XN v).det) (hXR : ∀ v, IsUnit (XR v).det) (hXc : ∀ v, IsUnit (Xc v).det)
    (hXE : ∀ v, IsUnit (XE v).det)
    (Bk : VN →ₗ[K] Module.Dual K VR) (B : (Fin d → K) →ₗ[K] Module.Dual K (Fin n → K))
    (hB : ∀ x y, Bk (eN x) (eR y) = B x y) :
    Formalism.HN.htMap bN XN bR.dualBasis (Formalism.HN.dualFrame XR) Bk =
      Formalism.HN.htMap (Pi.basisFun K (Fin d)) Xc (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame XE) B := by
  unfold Formalism.HN.htMap
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [opNormAt_tie bN XN bR XR Xc XE eN eR hN hR hXN hXR hXc hXE Bk B hB v]

end Op

end Formalism.MainNotions.DIV.HookProducts.RBTie
end
end

