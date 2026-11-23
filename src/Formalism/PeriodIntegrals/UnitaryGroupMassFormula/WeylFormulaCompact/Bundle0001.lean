module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.FormulaStep

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.Blocks
section
noncomputable section

namespace PI.WeylForKWork

open PI PI.UpqRep Matrix

variable {N : ℕ}

abbrev blR (ε : Fin N → Bool) :
    Matrix (Fin (nPl ε) ⊕ Fin (nMi ε)) (Fin (nPl ε) ⊕ Fin (nMi ε)) ℂ ≃ₐ[ℂ] Matrix (Fin N) (Fin N) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (blk ε)

lemma blR_apply (ε : Fin N → Bool) (M : Matrix (Fin (nPl ε) ⊕ Fin (nMi ε)) (Fin (nPl ε) ⊕ Fin (nMi ε)) ℂ) :
    blR ε M = M.submatrix (blk ε).symm (blk ε).symm := rfl

lemma plusBlock_eq_blockReindex (ε : Fin N → Bool) (h : Matrix (Fin (nPl ε)) (Fin (nPl ε)) ℂ) :
    iPl ε h = blR ε (fromBlocks h 0 0 1) := rfl

lemma minusBlock_eq_blockReindex (ε : Fin N → Bool) (h : Matrix (Fin (nMi ε)) (Fin (nMi ε)) ℂ) :
    iMi ε h = blR ε (fromBlocks 1 0 0 h) := rfl

lemma sign_blockEquiv_inl (ε : Fin N → Bool) (i : Fin (nPl ε)) : ε (blk ε (Sum.inl i)) = true := by
  exact Subtype.prop (p := fun a => ε a = true) _

lemma sign_blockEquiv_inr (ε : Fin N → Bool) (j : Fin (nMi ε)) : ε (blk ε (Sum.inr j)) = false := by
  exact Bool.eq_false_iff.2 (Subtype.prop (p := fun a => ¬ ε a = true) _)

lemma signatureMatrix_eq_blockReindex (ε : Fin N → Bool) : Jm ε = blR ε (fromBlocks 1 0 0 (-1)) := by
  rw [blR_apply]
  ext a c
  obtain ⟨x, rfl⟩ := (blk ε).surjective a
  obtain ⟨y, rfl⟩ := (blk ε).surjective c
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, Jm, Matrix.diagonal_apply,
    (blk ε).injective.eq_iff]
  rcases x with i | j <;> rcases y with i' | j'
  · by_cases h : i = i' <;> simp [h, Matrix.one_apply, sign_blockEquiv_inl]
  · simp
  · simp
  · by_cases h : j = j' <;> simp [h, Matrix.one_apply, sign_blockEquiv_inr]

lemma signatureMatrix_allPos_eq_one (n : ℕ) : Jm (allPos n) = 1 := by
  simp [Jm, allPos]

lemma star_blockReindex (ε : Fin N → Bool) (M : Matrix (Fin (nPl ε) ⊕ Fin (nMi ε)) (Fin (nPl ε) ⊕ Fin (nMi ε)) ℂ) :
    star (blR ε M) = blR ε (star M) := by
  simp only [blR_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix]

lemma blockReindex_mem_unitaryGroup_iff (ε : Fin N → Bool) (M : Matrix (Fin (nPl ε) ⊕ Fin (nMi ε)) (Fin (nPl ε) ⊕ Fin (nMi ε)) ℂ) :
    blR ε M ∈ unitaryGroup (Fin N) ℂ ↔ M ∈ unitaryGroup _ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.mem_unitaryGroup_iff, star_blockReindex, ← map_mul,
    ← map_one (blR ε), (blR ε).injective.eq_iff]

lemma blockReindex_mem_unitaryCentralizer_iff (ε : Fin N → Bool) (M : Matrix (Fin (nPl ε) ⊕ Fin (nMi ε)) (Fin (nPl ε) ⊕ Fin (nMi ε)) ℂ) :
    blR ε M ∈ Kset ε ↔ M ∈ unitaryGroup _ ℂ ∧ M * fromBlocks 1 0 0 (-1) = fromBlocks 1 0 0 (-1) * M := by
  show blR ε M ∈ unitaryGroup _ ℂ ∧ blR ε M * Jm ε = Jm ε * blR ε M ↔ _
  rw [blockReindex_mem_unitaryGroup_iff, signatureMatrix_eq_blockReindex, ← map_mul, ← map_mul, (blR ε).injective.eq_iff]

lemma mem_unitaryCentralizer_allPos_iff (n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) : h ∈ Kset (allPos n) ↔ h ∈ unitaryGroup _ ℂ := by
  show h ∈ unitaryGroup _ ℂ ∧ h * Jm (allPos n) = Jm (allPos n) * h ↔ _
  rw [signatureMatrix_allPos_eq_one]
  simp

section blocks

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

lemma fromBlocks_diagonal_mem_unitaryGroup_iff (A : Matrix m m ℂ) (D : Matrix n n ℂ) :
    fromBlocks A 0 0 D ∈ unitaryGroup (m ⊕ n) ℂ ↔ A ∈ unitaryGroup m ℂ ∧ D ∈ unitaryGroup n ℂ := by
  have h1 : (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ) = fromBlocks 1 0 0 1 := Matrix.fromBlocks_one.symm
  simp only [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, h1, Matrix.fromBlocks_inj]
  simp

lemma fromBlocks_diagonal_mul_signature_comm (A : Matrix m m ℂ) (D : Matrix n n ℂ) :
    fromBlocks A 0 0 D * fromBlocks 1 0 0 (-1) = fromBlocks 1 0 0 (-1) * fromBlocks A 0 0 D := by
  simp [Matrix.fromBlocks_multiply]

end blocks

lemma plusBlock_one (ε : Fin N → Bool) : iPl ε 1 = 1 := by
  rw [plusBlock_eq_blockReindex, Matrix.fromBlocks_one, map_one]

lemma minusBlock_one (ε : Fin N → Bool) : iMi ε 1 = 1 := by
  rw [minusBlock_eq_blockReindex, Matrix.fromBlocks_one, map_one]

lemma plusBlock_mul (ε : Fin N → Bool) (a b : Matrix (Fin (nPl ε)) (Fin (nPl ε)) ℂ) :
    iPl ε (a * b) = iPl ε a * iPl ε b := by
  rw [plusBlock_eq_blockReindex, plusBlock_eq_blockReindex, plusBlock_eq_blockReindex, ← map_mul, Matrix.fromBlocks_multiply]
  simp

lemma minusBlock_mul (ε : Fin N → Bool) (a b : Matrix (Fin (nMi ε)) (Fin (nMi ε)) ℂ) :
    iMi ε (a * b) = iMi ε a * iMi ε b := by
  rw [minusBlock_eq_blockReindex, minusBlock_eq_blockReindex, minusBlock_eq_blockReindex, ← map_mul, Matrix.fromBlocks_multiply]
  simp

lemma continuous_plusBlock (ε : Fin N → Bool) : Continuous (iPl ε) := by
  unfold iPl
  exact (continuous_id.matrix_fromBlocks continuous_const continuous_const
    continuous_const).matrix_submatrix _ _

lemma continuous_minusBlock (ε : Fin N → Bool) : Continuous (iMi ε) := by
  unfold iMi
  exact (continuous_const.matrix_fromBlocks continuous_const continuous_const
    continuous_id).matrix_submatrix _ _

lemma plusBlock_mem_unitaryCentralizer (ε : Fin N → Bool) (h : Matrix (Fin (nPl ε)) (Fin (nPl ε)) ℂ)
    (hh : h ∈ Kset (allPos (nPl ε))) : iPl ε h ∈ Kset ε := by
  rw [mem_unitaryCentralizer_allPos_iff] at hh
  rw [plusBlock_eq_blockReindex, blockReindex_mem_unitaryCentralizer_iff]
  exact ⟨(fromBlocks_diagonal_mem_unitaryGroup_iff _ _).2 ⟨hh, one_mem _⟩, fromBlocks_diagonal_mul_signature_comm _ _⟩

lemma minusBlock_mem_unitaryCentralizer (ε : Fin N → Bool) (h : Matrix (Fin (nMi ε)) (Fin (nMi ε)) ℂ)
    (hh : h ∈ Kset (allPos (nMi ε))) : iMi ε h ∈ Kset ε := by
  rw [mem_unitaryCentralizer_allPos_iff] at hh
  rw [minusBlock_eq_blockReindex, blockReindex_mem_unitaryCentralizer_iff]
  exact ⟨(fromBlocks_diagonal_mem_unitaryGroup_iff _ _).2 ⟨one_mem _, hh⟩, fromBlocks_diagonal_mul_signature_comm _ _⟩

lemma isUnitaryRepOn_comp {n : ℕ} (ε : Fin N → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (ι : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin N) (Fin N) ℂ)
    (h1 : ι 1 = 1) (hmul : ∀ a b, ι (a * b) = ι a * ι b) (hmem : ∀ h ∈ Kset (allPos n), ι h ∈ Kset ε)
    (hcont : Continuous ι) (hσ : IsURepOn (Kset ε) σ) : IsURepOn (Kset (allPos n)) (fun h => σ (ι h)) := by
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => hσ.2.1 (ι g) (hmem g hg) v, fun v => ?_⟩
  · show σ (ι 1) = 1
    rw [h1]
    exact hσ.1.1
  · show σ (ι (a * b)) = (σ (ι a)).comp (σ (ι b))
    rw [hmul]
    exact hσ.1.2 _ (hmem a ha) _ (hmem b hb)
  · exact (hσ.2.2 v).comp hcont.continuousOn hmem

theorem block_reindex_holds : Blocks := by
  intro N ε
  refine ⟨fun h hh => plusBlock_mem_unitaryCentralizer ε h hh, fun h hh => minusBlock_mem_unitaryCentralizer ε h hh, fun h h' => ?_,
    fun g hg => ?_, fun H _ _ σ hσ => ?_⟩
  · rw [plusBlock_eq_blockReindex, minusBlock_eq_blockReindex, ← map_mul, ← map_mul, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp
  · obtain ⟨M, rfl⟩ := (blR ε).surjective g
    rw [blockReindex_mem_unitaryCentralizer_iff] at hg
    obtain ⟨hU, hC⟩ := hg
    have hM := Matrix.fromBlocks_toBlocks M
    set A := M.toBlocks₁₁
    set B := M.toBlocks₁₂
    set C := M.toBlocks₂₁
    set D := M.toBlocks₂₂
    rw [← hM, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at hC
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.mul_neg, Matrix.neg_mul] at hC
    have hB : B = 0 := by
      ext i j
      have h := congr_fun (congr_fun hC.2.1 i) j
      simp only [Matrix.neg_apply] at h
      simp only [Matrix.zero_apply]
      linear_combination (-1 / 2 : ℂ) * h
    have hC0 : C = 0 := by
      ext i j
      have h := congr_fun (congr_fun hC.2.2.1 i) j
      simp only [Matrix.neg_apply] at h
      simp only [Matrix.zero_apply]
      linear_combination (1 / 2 : ℂ) * h
    rw [← hM, hB, hC0, fromBlocks_diagonal_mem_unitaryGroup_iff] at hU
    refine ⟨A, (mem_unitaryCentralizer_allPos_iff _ A).2 hU.1, D, (mem_unitaryCentralizer_allPos_iff _ D).2 hU.2, ?_⟩
    rw [plusBlock_eq_blockReindex, minusBlock_eq_blockReindex, ← map_mul, Matrix.fromBlocks_multiply, ← hM, hB, hC0]
    congr 1
    simp
  · exact ⟨isUnitaryRepOn_comp ε σ (iPl ε) (plusBlock_one ε) (plusBlock_mul ε) (plusBlock_mem_unitaryCentralizer ε) (continuous_plusBlock ε) hσ,
      isUnitaryRepOn_comp ε σ (iMi ε) (minusBlock_one ε) (minusBlock_mul ε) (minusBlock_mem_unitaryCentralizer ε) (continuous_minusBlock ε) hσ⟩

theorem block_diagonal_torus_holds : BlockDiag := by
  intro N ε
  refine ⟨fun f => ?_, fun θ => ?_, fun θ => ?_⟩
  · rw [← Equiv.sum_comp (blk ε), Fintype.sum_sum_type]
    rfl
  · refine ⟨fun a => Sum.elim θ 0 ((blk ε).symm a), fun i => by simp [ePl], fun j => by simp [eMi], ?_⟩
    unfold iPl
    rw [← Matrix.diagonal_one, Matrix.fromBlocks_diagonal, Matrix.submatrix_diagonal_equiv]
    congr 1
    funext a
    rcases h : (blk ε).symm a with i | j <;> simp [h]
  · refine ⟨fun a => Sum.elim 0 θ ((blk ε).symm a), fun i => by simp [ePl], fun j => by simp [eMi], ?_⟩
    unfold iMi
    rw [← Matrix.diagonal_one, Matrix.fromBlocks_diagonal, Matrix.submatrix_diagonal_equiv]
    congr 1
    funext a
    rcases h : (blk ε).symm a with i | j <;> simp [h]

end PI.WeylForKWork
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.DimStepA
section
noncomputable section

namespace PI.WeylForKWork.DimensionInduction

open scoped InnerProductSpace
open Module

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι κ : Type*}

def Stab (ρ : ι → H →L[ℂ] H) (W : Submodule ℂ H) : Prop := ∀ i, ∀ v ∈ W, ρ i v ∈ W

def Irr (ρ : ι → H →L[ℂ] H) (W : Submodule ℂ H) : Prop :=
  ∀ W' : Submodule ℂ H, W' ≤ W → Stab ρ W' → W' = ⊥ ∨ W' = W

structure Good (ρ : ι → H →L[ℂ] H) : Prop where
  isom : ∀ i v, ‖ρ i v‖ = ‖v‖
  inv : ∀ i, ∃ j, ∀ v, ρ i (ρ j v) = v
  mul : ∀ i i', ∃ k, ∀ v, ρ i (ρ i' v) = ρ k v
  one : ∃ i, ∀ v, ρ i v = v

def Comm (ρ : ι → H →L[ℂ] H) (c : H →ₗ[ℂ] H) : Prop := ∀ i v, c (ρ i v) = ρ i (c v)

def commSub (ρ : ι → H →L[ℂ] H) : Submodule ℂ (H →ₗ[ℂ] H) where
  carrier := {c | Comm ρ c}
  add_mem' := by
    intro c d hc hd
    have hc : Comm ρ c := hc
    have hd : Comm ρ d := hd
    show Comm ρ (c + d)
    intro i v
    simp only [LinearMap.add_apply, map_add (f := _), hc i v, hd i v]
  zero_mem' := by
    show Comm ρ 0
    intro i v
    simp
  smul_mem' := by
    intro a c hc
    have hc : Comm ρ c := hc
    show Comm ρ (a • c)
    intro i v
    simp only [LinearMap.smul_apply, map_smul, hc i v]

def slice (ρ : ι → H →L[ℂ] H) (x₀ : H) : Submodule ℂ H where
  carrier := {v | ∃ c : H →ₗ[ℂ] H, Comm ρ c ∧ c x₀ = v}
  add_mem' := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    exact ⟨c + d, (commSub ρ).add_mem hc hd, rfl⟩
  zero_mem' := ⟨0, (commSub ρ).zero_mem, rfl⟩
  smul_mem' := by
    rintro a _ ⟨c, hc, rfl⟩
    exact ⟨a • c, (commSub ρ).smul_mem a hc, rfl⟩

variable {ρ : ι → H →L[ℂ] H} {ρ' : κ → H →L[ℂ] H}

lemma Good.inner (hρ : Good ρ) (i : ι) (x y : H) : ⟪ρ i x, ρ i y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let L : H →ₗᵢ[ℂ] H := ⟨(ρ i : H →ₗ[ℂ] H), hρ.isom i⟩
  exact L.inner_map_map x y

lemma stab_orth (hρ : Good ρ) {W : Submodule ℂ H} (hW : Stab ρ W) : Stab ρ Wᗮ := by
  intro i v hv
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro w hw
  obtain ⟨j, hj⟩ := hρ.inv i
  rw [← hj w, hρ.inner i]
  exact hv _ (hW j w hw)

lemma stab_inf {W W' : Submodule ℂ H} (h : Stab ρ W) (h' : Stab ρ W') : Stab ρ (W ⊓ W') := by
  intro i v hv
  exact ⟨h i v hv.1, h' i v hv.2⟩

lemma proj_comm (hρ : Good ρ) {W : Submodule ℂ H} [FiniteDimensional ℂ W] (hW : Stab ρ W) :
    Comm ρ (W.starProjection : H →ₗ[ℂ] H) := by
  intro i v
  have hWo := stab_orth hρ hW
  show W.starProjection (ρ i v) = ρ i (W.starProjection v)
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hW i _ (W.orthogonalProjection v).2
  · intro w hw
    rw [← map_sub]
    exact (Submodule.mem_orthogonal' W _).1 (hWo i _ (W.sub_starProjection_mem_orthogonal v)) w hw

lemma comm_comp {c d : H →ₗ[ℂ] H} (hc : Comm ρ c) (hd : Comm ρ d) : Comm ρ (c ∘ₗ d) := by
  intro i v
  show c (d (ρ i v)) = ρ i (c (d v))
  rw [hd i v, hc i (d v)]

lemma kill {c : H →ₗ[ℂ] H} (hc : Comm ρ c) {X : Submodule ℂ H} (hXs : Stab ρ X) (hXi : Irr ρ X)
    {x₁ : H} (hx₁ : x₁ ∈ X) (h0 : x₁ ≠ 0) (hk : c x₁ = 0) : ∀ x ∈ X, c x = 0 := by
  have hst : Stab ρ (LinearMap.ker c ⊓ X) := by
    intro i v hv
    refine ⟨?_, hXs i v hv.2⟩
    show c (ρ i v) = 0
    rw [hc i v, LinearMap.mem_ker.1 hv.1, map_zero]
  rcases hXi _ inf_le_right hst with h | h
  · exfalso
    have hm : x₁ ∈ LinearMap.ker c ⊓ X := ⟨LinearMap.mem_ker.2 hk, hx₁⟩
    rw [h] at hm
    exact h0 ((Submodule.mem_bot ℂ).1 hm)
  · intro x hx
    rw [← h] at hx
    exact LinearMap.mem_ker.1 hx.1

lemma into (hρ : Good ρ) {c : H →ₗ[ℂ] H} (hc : Comm ρ c) {X W : Submodule ℂ H} [FiniteDimensional ℂ W]
    (hW : Stab ρ W) (hXs : Stab ρ X) (hXi : Irr ρ X) {x₁ : H} (hx₁ : x₁ ∈ X) (h0 : x₁ ≠ 0)
    (hin : c x₁ ∈ W) : ∀ x ∈ X, c x ∈ W := by
  set P : H →ₗ[ℂ] H := (W.starProjection : H →ₗ[ℂ] H) with hP
  have hd : Comm ρ (c - P ∘ₗ c) :=
    (commSub ρ).sub_mem hc (comm_comp (proj_comm hρ hW) hc)
  have h1 : (c - P ∘ₗ c) x₁ = 0 := by
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, hP, ContinuousLinearMap.coe_coe,
      Submodule.starProjection_eq_self_iff.2 hin, sub_self]
  intro x hx
  have h2 := kill hd hXs hXi hx₁ h0 h1 x hx
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, hP, ContinuousLinearMap.coe_coe,
    sub_eq_zero] at h2
  rw [h2]
  exact (W.orthogonalProjection (c x)).2

lemma stab_map {c : H →ₗ[ℂ] H} (hc : Comm ρ c) {X : Submodule ℂ H} (hX : Stab ρ X) :
    Stab ρ (X.map c) := by
  rintro i _ ⟨x, hx, rfl⟩
  exact ⟨ρ i x, hX i x hx, hc i x⟩

lemma stab_iSup {ν : Sort*} {F : ν → Submodule ℂ H} (hF : ∀ k, Stab ρ (F k)) :
    Stab ρ (⨆ k, F k) := by
  intro i v hv
  have hle : (⨆ k, F k) ≤ (⨆ k, F k).comap (ρ i : H →ₗ[ℂ] H) :=
    iSup_le fun k x hx => Submodule.mem_iSup_of_mem k (hF k i x hx)
  exact hle hv

theorem exists_hit (hρ : Good ρ) (hρ' : Good ρ') (hcomm : ∀ i j v, ρ i (ρ' j v) = ρ' j (ρ i v))
    {S X W : Submodule ℂ H} (hSρ' : Stab ρ' S)
    (hSirr : ∀ S' : Submodule ℂ H, S' ≤ S → Stab ρ S' → Stab ρ' S' → S' = ⊥ ∨ S' = S)
    (hXS : X ≤ S) (hXs : Stab ρ X) (hXi : Irr ρ X) {x₀ : H} (hx₀ : x₀ ∈ X) (h0 : x₀ ≠ 0)
    [FiniteDimensional ℂ W] (hWS : W ≤ S) (hW0 : W ≠ ⊥) (hWs : Stab ρ W) :
    ∃ c : H →ₗ[ℂ] H, Comm ρ c ∧ c x₀ ∈ W ∧ c x₀ ≠ 0 := by
  set P : H →ₗ[ℂ] H := (W.starProjection : H →ₗ[ℂ] H) with hP
  have hPc : Comm ρ P := proj_comm hρ hWs
  have hρ'c : ∀ j, Comm ρ (ρ' j : H →ₗ[ℂ] H) := fun j i v => (hcomm i j v).symm
  by_contra hne
  push_neg at hne
  have hzero : ∀ j, ∀ x ∈ X, P (ρ' j x) = 0 := by
    intro j
    have hcj : Comm ρ (P ∘ₗ (ρ' j : H →ₗ[ℂ] H)) := comm_comp hPc (hρ'c j)
    have hk : (P ∘ₗ (ρ' j : H →ₗ[ℂ] H)) x₀ = 0 := by
      refine hne _ hcj ?_
      simp only [LinearMap.comp_apply, hP, ContinuousLinearMap.coe_coe]
      exact (W.orthogonalProjection _).2
    exact kill hcj hXs hXi hx₀ h0 hk
  set T : Submodule ℂ H := ⨆ j, X.map (ρ' j : H →ₗ[ℂ] H) with hT
  have hTρ : Stab ρ T := stab_iSup fun j => stab_map (hρ'c j) hXs
  have hTρ' : Stab ρ' T := by
    intro j' v hv
    have hle : T ≤ T.comap (ρ' j' : H →ₗ[ℂ] H) := by
      refine iSup_le fun j => ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨k, hk⟩ := hρ'.mul j' j
      show ρ' j' (ρ' j x) ∈ T
      rw [hk x]
      exact Submodule.mem_iSup_of_mem k ⟨x, hx, rfl⟩
    exact hle hv
  have hTS : T ≤ S := by
    refine iSup_le fun j => ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hSρ' j x (hXS hx)
  have hx₀T : x₀ ∈ T := by
    obtain ⟨o, ho⟩ := hρ'.one
    have hm : ρ' o x₀ ∈ T := Submodule.mem_iSup_of_mem o ⟨x₀, hx₀, rfl⟩
    rwa [ho] at hm
  rcases hSirr T hTS hTρ hTρ' with h | h
  · rw [h] at hx₀T
    exact h0 ((Submodule.mem_bot ℂ).1 hx₀T)
  · have hle : T ≤ LinearMap.ker P := by
      refine iSup_le fun j => ?_
      rintro _ ⟨x, hx, rfl⟩
      exact LinearMap.mem_ker.2 (hzero j x hx)
    apply hW0
    rw [eq_bot_iff]
    intro w hw
    have hwT : w ∈ T := by
      rw [h]
      exact hWS hw
    have h1 : P w = 0 := LinearMap.mem_ker.1 (hle hwT)
    have h2 : P w = w := by
      simp only [hP, ContinuousLinearMap.coe_coe]
      exact Submodule.starProjection_eq_self_iff.2 hw
    refine (Submodule.mem_bot ℂ).2 ?_
    rw [← h2]
    exact h1

theorem schur2 (hρ : Good ρ) {X W : Submodule ℂ H} [FiniteDimensional ℂ X] [FiniteDimensional ℂ W]
    (hXs : Stab ρ X) (hXi : Irr ρ X) (hWs : Stab ρ W) (hWi : Irr ρ W) {x₀ : H} (hx₀ : x₀ ∈ X)
    (h0 : x₀ ≠ 0) {c c' : H →ₗ[ℂ] H} (hc : Comm ρ c) (hc' : Comm ρ c') (hcW : c x₀ ∈ W)
    (hc0 : c x₀ ≠ 0) (hc'W : c' x₀ ∈ W) :
    finrank ℂ X = finrank ℂ W ∧ ∃ μ : ℂ, c' x₀ = μ • c x₀ := by
  have hAW : ∀ x : X, c x ∈ W := fun x => into hρ hc hWs hXs hXi hx₀ h0 hcW x x.2
  have hBW : ∀ x : X, c' x ∈ W := fun x => into hρ hc' hWs hXs hXi hx₀ h0 hc'W x x.2
  have hinj : Function.Injective (c.domRestrict X) := by
    intro a b hab
    by_contra hne
    rw [LinearMap.domRestrict_apply, LinearMap.domRestrict_apply] at hab
    have hab' : c ((a : H) - b) = 0 := by rw [map_sub, hab, sub_self]
    have hne' : (a : H) - b ≠ 0 := fun h => hne (Subtype.ext (sub_eq_zero.1 h))
    exact hc0 (kill hc hXs hXi (X.sub_mem a.2 b.2) hne' hab' x₀ hx₀)
  have hmapW : X.map c = W := by
    rcases hWi _ (by rintro _ ⟨x, hx, rfl⟩; exact hAW ⟨x, hx⟩) (stab_map hc hXs) with h | h
    · exfalso
      have hm : c x₀ ∈ X.map c := ⟨x₀, hx₀, rfl⟩
      rw [h] at hm
      exact hc0 ((Submodule.mem_bot ℂ).1 hm)
    · exact h
  have hrank : finrank ℂ X = finrank ℂ W := by
    rw [← hmapW, ← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj]
  refine ⟨hrank, ?_⟩
  let A : X →ₗ[ℂ] W := (c.domRestrict X).codRestrict W hAW
  let B : X →ₗ[ℂ] W := (c'.domRestrict X).codRestrict W hBW
  have hAinj : Function.Injective A := fun a b hab => hinj (congrArg Subtype.val hab)
  have hAsurj : Function.Surjective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hAinj
  let e : X ≃ₗ[ℂ] W := LinearEquiv.ofBijective A ⟨hAinj, hAsurj⟩
  let T : Module.End ℂ X := e.symm.toLinearMap ∘ₗ B
  haveI : Nontrivial X := ⟨⟨⟨x₀, hx₀⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hTv : T v = μ • v := hv.apply_eq_smul
  have hBv : B v = μ • A v :=
    calc B v = e (T v) := (e.apply_symm_apply (B v)).symm
      _ = e (μ • v) := by rw [hTv]
      _ = μ • e v := map_smul e μ v
      _ = μ • A v := rfl
  have hcv : c' v = μ • c v := congrArg Subtype.val hBv
  have hd : Comm ρ (c' - μ • c) := (commSub ρ).sub_mem hc' ((commSub ρ).smul_mem μ hc)
  have hdv : (c' - μ • c) v = 0 := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, hcv, sub_self]
  have hv0 : (v : H) ≠ 0 := fun h => hv.2 (Subtype.ext h)
  have hfin := kill hd hXs hXi v.2 hv0 hdv x₀ hx₀
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero] at hfin
  exact ⟨μ, hfin⟩

end PI.WeylForKWork.DimensionInduction
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.WeylForKOfSteps
section
noncomputable section

namespace PI.WeylForKWork

open PI PI.UpqRep Matrix

theorem weylForK_of_steps (hB : Blocks) (hTP : TypePl) (hTM : TypeMi) (hD : DimStep)
    (hF : FormulaStep) (hU : PI.WeylForU) : PI.WeylForK := by
  intro N ε Λ H _ _ σ S hσ hS
  obtain ⟨hB1, hB2, hB3, hB4, hB5⟩ := hB N ε
  obtain ⟨hσP, hσM⟩ := hB5 H σ hσ
  obtain ⟨X, hXS, hX⟩ := hTP N ε Λ H σ S hσ hS
  obtain ⟨Y, hYS, hY⟩ := hTM N ε Λ H σ S hσ hS
  have hmul : ∀ g ∈ Kset ε, ∀ g' ∈ Kset ε, σ (g * g') = (σ g).comp (σ g') := hσ.1.2
  have hSst : IsKStableOn ε σ S := hS.2.1
  have hcomm : ∀ h ∈ Kset (allPos (nPl ε)), ∀ h' ∈ Kset (allPos (nMi ε)),
      (sPl ε σ h).comp (sMi ε σ h') = (sMi ε σ h').comp (sPl ε σ h) := by
    intro h hh h' hh'
    show (σ (iPl ε h)).comp (σ (iMi ε h')) = (σ (iMi ε h')).comp (σ (iPl ε h))
    rw [← hmul _ (hB1 h hh) _ (hB2 h' hh'), ← hmul _ (hB2 h' hh') _ (hB1 h hh), hB3]
  have hstP : IsKStableOn (allPos (nPl ε)) (sPl ε σ) S := fun h hh v hv => hSst _ (hB1 h hh) v hv
  have hstM : IsKStableOn (allPos (nMi ε)) (sMi ε σ) S := fun h hh v hv => hSst _ (hB2 h hh) v hv
  have hirr : ∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn (allPos (nPl ε)) (sPl ε σ) S' →
      IsKStableOn (allPos (nMi ε)) (sMi ε σ) S' → S' = ⊥ ∨ S' = S := by
    intro S' hS' h1 h2
    refine hS.2.2.1 S' hS' (fun g hg v hv => ?_)
    obtain ⟨h, hh, h', hh', rfl⟩ := hB4 g hg
    rw [hmul _ (hB1 h hh) _ (hB2 h' hh')]
    exact h1 h hh _ (h2 h' hh' v hv)
  have hX0 : X ≠ ⊥ := by
    obtain ⟨v, hv, hv0, _⟩ := hX.2.2.2.1
    intro hbot
    rw [hbot] at hv
    exact hv0 ((Submodule.mem_bot ℂ).1 hv)
  have hY0 : Y ≠ ⊥ := by
    obtain ⟨v, hv, hv0, _⟩ := hY.2.2.2.1
    intro hbot
    rw [hbot] at hv
    exact hv0 ((Submodule.mem_bot ℂ).1 hv)
  have hdim := hD (nPl ε) (nMi ε) H (sPl ε σ) (sMi ε σ) S X Y hσP hσM hcomm hS.1 hstP hstM hirr
    hXS hX0 hX.2.1 hX.2.2.1 hYS hY0 hY.2.1 hY.2.2.1
  have hwX := hU (nPl ε) (fun i => Λ (ePl ε i)) H (sPl ε σ) X hσP hX
  have hwY := hU (nMi ε) (fun j => Λ (eMi ε j)) H (sMi ε σ) Y hσM hY
  rw [hF N ε Λ, hdim, Nat.cast_mul, hwX, hwY]
  rfl

end PI.WeylForKWork
end
end

