module

public import Mathlib
public import Formalism.HarderNarasimhan.ShiftInvariance

@[expose] public section

-- bundled from Formalism.SharpRestriction.Divisibility.HookProducts.RBTieFrame
section
open Matrix NumberField Module

noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts.RBTie

section Vec

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem vecAt_map (b : Basis ι K V) (b' : Basis κ K W) (v : InfinitePlace K) (u : V →ₗ[K] W) (x : V) :
    Formalism.HermitianLatticesTheory.vecAt b' v (u x) = (LinearMap.toMatrix b b' u).map v.embedding *ᵥ Formalism.HermitianLatticesTheory.vecAt b v x := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.HermitianLatticesTheory.vecAt, ← LinearMap.toMatrix_mulVec_repr b b' u x, Matrix.mulVec, dotProduct,
    Matrix.map_apply, map_sum, map_mul]

theorem vecAt_std {d : ℕ} (v : InfinitePlace K) (x : Fin d → K) :
    Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin d)) v x = fun l => v.embedding (x l) := by
  funext l
  simp [Formalism.HermitianLatticesTheory.vecAt]

end Vec

theorem sum_star_mulVec_single {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (C : Matrix m n ℂ) (i j : n) :
    ∑ k, star ((C *ᵥ Pi.single i 1) k) * (C *ᵥ Pi.single j 1) k = (Cᴴ * C) i j := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct, Pi.single_apply]

section Comparison₂

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}

def cP (b : Basis ι K V) (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K) : Matrix ι (Fin d) ℂ :=
  (LinearMap.toMatrix (Pi.basisFun K (Fin d)) b e.toLinearMap).map v.embedding

def cQ (b : Basis ι K V) (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K) : Matrix (Fin d) ι ℂ :=
  (LinearMap.toMatrix b (Pi.basisFun K (Fin d)) e.symm.toLinearMap).map v.embedding

theorem basisChange_mul_basisChangeInv (b : Basis ι K V) (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K) : cP b e v * cQ b e v = 1 := by
  unfold cP cQ
  rw [← Matrix.map_mul, ← LinearMap.toMatrix_comp]
  simp

theorem cQ_mul_cP (b : Basis ι K V) (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K) : cQ b e v * cP b e v = 1 := by
  unfold cP cQ
  rw [← Matrix.map_mul, ← LinearMap.toMatrix_comp]
  simp

theorem fcoord_e (b : Basis ι K V) (XA : InfinitePlace K → Matrix ι ι ℂ) (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K)
    (y : Fin d → K) :
    Formalism.HermitianLatticesTheory.fcoord b XA v (e y) = ((XA v)⁻¹ * cP b e v) *ᵥ (fun l => v.embedding (y l)) := by
  show (XA v)⁻¹ *ᵥ Formalism.HermitianLatticesTheory.vecAt b v (e y) = _
  rw [← Matrix.mulVec_mulVec]
  congr 1
  rw [show e y = e.toLinearMap y from rfl, vecAt_map (Pi.basisFun K (Fin d)) b v e.toLinearMap y, vecAt_std]
  rfl

theorem fcoord_std (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K) (y : Fin d → K) :
    Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin d)) X v y = (X v)⁻¹ *ᵥ (fun l => v.embedding (y l)) := by
  show (X v)⁻¹ *ᵥ Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin d)) v y = _
  rw [vecAt_std]

theorem emb_single (v : InfinitePlace K) (k : Fin d) :
    (fun l => v.embedding ((Pi.single k (1 : K) : Fin d → K) l)) = Pi.single k (1 : ℂ) := by
  funext l
  by_cases h : l = k
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem gram_tie (b : Basis ι K V) (XA : InfinitePlace K → Matrix ι ι ℂ) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (e : (Fin d → K) ≃ₗ[K] V)
    (h : ∀ v x y, Formalism.HermitianLatticesTheory.majAt b XA v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y)
    (v : InfinitePlace K) :
    ((XA v)⁻¹ * cP b e v)ᴴ * ((XA v)⁻¹ * cP b e v) = ((X v)⁻¹)ᴴ * (X v)⁻¹ := by
  ext k l
  have h1 := h v (Pi.single k (1 : K) : Fin d → K) (Pi.single l (1 : K) : Fin d → K)
  unfold Formalism.HermitianLatticesTheory.majAt at h1
  rw [fcoord_e, fcoord_e, fcoord_std, fcoord_std, emb_single, emb_single] at h1
  rw [← sum_star_mulVec_single, ← sum_star_mulVec_single]
  exact h1

def cU (b : Basis ι K V) (XA : InfinitePlace K → Matrix ι ι ℂ) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K) : Matrix ι (Fin d) ℂ :=
  (XA v)⁻¹ * cP b e v * X v

def cV (b : Basis ι K V) (XA : InfinitePlace K → Matrix ι ι ℂ) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K) : Matrix (Fin d) ι ℂ :=
  (X v)⁻¹ * cQ b e v * XA v

variable (b : Basis ι K V) (XA : InfinitePlace K → Matrix ι ι ℂ) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
  (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K)

theorem cU_conj_mul (h : ∀ v x y, Formalism.HermitianLatticesTheory.majAt b XA v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y)
    (hX : IsUnit (X v).det) : (cU b XA X e v)ᴴ * cU b XA X e v = 1 := by
  have hg := gram_tie b XA X e h v
  have hinv : (X v)⁻¹ * X v = 1 := Matrix.nonsing_inv_mul _ hX
  calc (cU b XA X e v)ᴴ * cU b XA X e v
      = (X v)ᴴ * (((XA v)⁻¹ * cP b e v)ᴴ * ((XA v)⁻¹ * cP b e v)) * X v := by
        simp only [cU, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (X v)ᴴ * (((X v)⁻¹)ᴴ * (X v)⁻¹) * X v := by rw [hg]
    _ = ((X v)⁻¹ * X v)ᴴ * ((X v)⁻¹ * X v) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hinv, Matrix.conjTranspose_one, Matrix.mul_one]

theorem cU_mul_cV (hXA : IsUnit (XA v).det) (hX : IsUnit (X v).det) : cU b XA X e v * cV b XA X e v = 1 := by
  calc cU b XA X e v * cV b XA X e v
      = (XA v)⁻¹ * (cP b e v * (X v * (X v)⁻¹) * cQ b e v) * XA v := by
        simp only [cU, cV, Matrix.mul_assoc]
    _ = (XA v)⁻¹ * XA v := by
        rw [Matrix.mul_nonsing_inv _ hX, Matrix.mul_one, basisChange_mul_basisChangeInv, Matrix.mul_one]
    _ = 1 := Matrix.nonsing_inv_mul _ hXA

theorem cU_conj_eq (h : ∀ v x y, Formalism.HermitianLatticesTheory.majAt b XA v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y)
    (hXA : IsUnit (XA v).det) (hX : IsUnit (X v).det) : (cU b XA X e v)ᴴ = cV b XA X e v := by
  calc (cU b XA X e v)ᴴ = (cU b XA X e v)ᴴ * (cU b XA X e v * cV b XA X e v) := by
        rw [cU_mul_cV b XA X e v hXA hX, Matrix.mul_one]
    _ = ((cU b XA X e v)ᴴ * cU b XA X e v) * cV b XA X e v := (Matrix.mul_assoc _ _ _).symm
    _ = cV b XA X e v := by rw [cU_conj_mul b XA X e v h hX, Matrix.one_mul]

theorem cU_mul_conj (h : ∀ v x y, Formalism.HermitianLatticesTheory.majAt b XA v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y)
    (hXA : IsUnit (XA v).det) (hX : IsUnit (X v).det) : cU b XA X e v * (cU b XA X e v)ᴴ = 1 := by
  rw [cU_conj_eq b XA X e v h hXA hX, cU_mul_cV b XA X e v hXA hX]

theorem basisChange_mul_X (hXA : IsUnit (XA v).det) : cP b e v * X v = XA v * cU b XA X e v := by
  unfold cU
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hXA, Matrix.one_mul]

theorem cQ_mul_XA (h : ∀ v x y, Formalism.HermitianLatticesTheory.majAt b XA v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y)
    (hXA : IsUnit (XA v).det) (hX : IsUnit (X v).det) : cQ b e v * XA v = X v * (cU b XA X e v)ᴴ := by
  rw [cU_conj_eq b XA X e v h hXA hX]
  unfold cV
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hX, Matrix.one_mul]

theorem frame_unit_of_tie (h : ∀ v x y, Formalism.HermitianLatticesTheory.majAt b XA v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y)
    (hXA : IsUnit (XA v).det) : IsUnit (X v).det := by
  by_contra hX
  have hinv : (X v)⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit _ hX
  have hg := gram_tie b XA X e h v
  rw [hinv, Matrix.conjTranspose_zero, Matrix.zero_mul] at hg
  have hM : (XA v)⁻¹ * cP b e v = 0 := by
    open scoped ComplexOrder in exact Matrix.conjTranspose_mul_self_eq_zero.mp hg
  have hP : cP b e v = 0 := by
    have h2 := congrArg (fun M => XA v * M) hM
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hXA, Matrix.one_mul, Matrix.mul_zero] at h2
    exact h2
  have h1 := cQ_mul_cP b e v
  rw [hP, Matrix.mul_zero] at h1
  obtain rfl | hd := Nat.eq_zero_or_pos d
  · exact hX (by simp)
  · have h3 := congrFun (congrFun h1 ⟨0, hd⟩) ⟨0, hd⟩
    simp at h3

end Comparison₂

section Norm

end Norm

end Formalism.MainNotions.DIV.HookProducts.RBTie
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.HookProducts.RBTieSlope
section
open Module

noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts.RBTie

theorem slope_eq_of_norm_eq {R V E F : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (ρ : V →+ E) (ρ₂ : V →+ F) (hn : ∀ x, ‖ρ₂ x‖ = ‖ρ x‖) (N : Submodule R V) :
    Formalism.HN.slope ρ₂ N = Formalism.HN.slope ρ N := by
  classical
  have memL : ∀ y : E, y ∈ Formalism.HN.zl ρ N ↔ ∃ x ∈ N.toAddSubgroup, ρ x = y := by
    intro y
    show y ∈ (N.toAddSubgroup.map ρ) ↔ _
    exact AddSubgroup.mem_map
  have memM : ∀ y : F, y ∈ Formalism.HN.zl ρ₂ N ↔ ∃ x ∈ N.toAddSubgroup, ρ₂ x = y := by
    intro y
    show y ∈ (N.toAddSubgroup.map ρ₂) ↔ _
    exact AddSubgroup.mem_map
  let pre : Formalism.HN.zl ρ N → V := fun y => Classical.choose ((memL y).1 y.2)
  have pre_mem : ∀ y, pre y ∈ N.toAddSubgroup := fun y =>
    (Classical.choose_spec ((memL y).1 y.2)).1
  have pre_eq : ∀ y, ρ (pre y) = y := fun y => (Classical.choose_spec ((memL y).1 y.2)).2
  let f0 : Formalism.HN.zl ρ N →+ Formalism.HN.zl ρ₂ N :=
    AddMonoidHom.mk' (fun y => ⟨ρ₂ (pre y), (memM _).2 ⟨pre y, pre_mem y, rfl⟩⟩) (by
      intro y z
      apply Subtype.ext
      show ρ₂ (pre (y + z)) = ρ₂ (pre y) + ρ₂ (pre z)
      rw [← map_add (f := _)]
      apply Formalism.HN.Rerealization.eq_of_eq ρ ρ₂ hn
      rw [map_add (f := _), pre_eq, pre_eq, pre_eq]
      rfl)
  have f0_apply : ∀ y, ((f0 y : Formalism.HN.zl ρ₂ N) : F) = ρ₂ (pre y) := fun y => rfl
  have f0_norm : ∀ y, ‖((f0 y : Formalism.HN.zl ρ₂ N) : F)‖ = ‖(y : E)‖ := by
    intro y
    rw [f0_apply, hn, pre_eq]
  have hinj : Function.Injective f0 := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    have h0 : ‖(y : E)‖ = 0 := by
      rw [← f0_norm, hy]
      simp
    exact Subtype.ext (norm_eq_zero.1 h0)
  have hsurj : Function.Surjective f0 := by
    rintro ⟨z, hz⟩
    obtain ⟨x, hx, rfl⟩ := (memM z).1 hz
    refine ⟨⟨ρ x, (memL _).2 ⟨x, hx, rfl⟩⟩, Subtype.ext ?_⟩
    rw [f0_apply]
    exact Formalism.HN.Rerealization.eq_of_eq ρ ρ₂ hn (pre_eq _)
  let e : Formalism.HN.zl ρ N ≃+ Formalism.HN.zl ρ₂ N := AddEquiv.ofBijective f0 ⟨hinj, hsurj⟩
  have e_norm : ∀ y, ‖e y‖ = ‖y‖ := fun y => f0_norm y
  have e_symm_norm : ∀ z, ‖e.symm z‖ = ‖z‖ := by
    intro z
    rw [← e_norm (e.symm z), e.apply_symm_apply]
  have iso : Isometry e := AddMonoidHomClass.isometry_of_norm e e_norm
  have iso_symm : Isometry e.symm := AddMonoidHomClass.isometry_of_norm e.symm e_symm_norm
  have hiff : DiscreteTopology (Formalism.HN.zl ρ N) ↔ DiscreteTopology (Formalism.HN.zl ρ₂ N) := by
    constructor
    · intro h
      exact iso_symm.isEmbedding.discreteTopology
    · intro h
      exact iso.isEmbedding.discreteTopology
  have hrk : Formalism.F.rk (Formalism.HN.zl ρ₂ N) = Formalism.F.rk (Formalism.HN.zl ρ N) := by
    unfold Formalism.F.rk
    exact e.toIntLinearEquiv.finrank_eq.symm
  have hcov : Formalism.F.covol (Formalism.HN.zl ρ₂ N) = Formalism.F.covol (Formalism.HN.zl ρ N) := by
    by_cases h : DiscreteTopology (Formalism.HN.zl ρ N)
    · exact (Formalism.HN.Rerealization.covol_rk_eq ρ ρ₂ hn N.toAddSubgroup h (hiff.1 h)).1
    · have h' : ¬ DiscreteTopology (Formalism.HN.zl ρ₂ N) := fun h' => h (hiff.2 h')
      unfold Formalism.F.covol
      rw [dite_eq_right h, dite_eq_right h']
  unfold Formalism.HN.slope Formalism.F.slope Formalism.F.deg
  rw [hcov, hrk]

end Formalism.MainNotions.DIV.HookProducts.RBTie
end
end

