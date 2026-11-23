module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlkConjTranspose
section
open Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.AdmGL

variable {ι : Type} [Fintype ι] [DecidableEq ι] {a n : ℕ}

def atPlace (M : Matrix (Fin a) (Fin a) (ι → ℂ)) (w : ι) : Matrix (Fin a) (Fin a) ℂ :=
  M.map fun x => x w

def blk (e : Fin a × ι ≃ Fin n) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.reindex e e (blockDiagonal (atPlace M))

def unblk (e : Fin a × ι ≃ Fin n) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin a) (Fin a) (ι → ℂ) :=
  Matrix.of fun p q w => g (e (p, w)) (e (q, w))

def blkG (e : Fin a × ι ≃ Fin n) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  blk e '' {M | IsUnit M}

theorem blk_apply (e : Fin a × ι ≃ Fin n) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) (i j : Fin n) :
    blk e M i j = if (e.symm i).2 = (e.symm j).2 then M (e.symm i).1 (e.symm j).1 (e.symm i).2 else 0 := by
  rw [GlobalTheory.CompanionTheory.AdmGL.blk, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.blockDiagonal_apply,
    GlobalTheory.CompanionTheory.AdmGL.atPlace, Matrix.map_apply]

@[simp] theorem unblk_blk (e : Fin a × ι ≃ Fin n) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    unblk e (blk e M) = M := by
  ext p q w
  simp [unblk, blk_apply]

theorem blk_injective (e : Fin a × ι ≃ Fin n) : Function.Injective (blk e) := by
  intro M N h
  rw [← GlobalTheory.CompanionTheory.AdmGL.unblk_blk e M, h, GlobalTheory.CompanionTheory.AdmGL.unblk_blk]

@[simp] theorem blk_one (e : Fin a × ι ≃ Fin n) : blk e 1 = 1 := by
  ext i j
  rw [GlobalTheory.CompanionTheory.AdmGL.blk_apply]
  by_cases h : i = j
  · subst h
    simp
  · have h' : e.symm i ≠ e.symm j := fun h'' => h (e.symm.injective h'')
    rw [Matrix.one_apply_ne h]
    by_cases h2 : (e.symm i).2 = (e.symm j).2
    · have h1 : (e.symm i).1 ≠ (e.symm j).1 := fun h1 => h' (Prod.ext h1 h2)
      rw [if_pos h2, Matrix.one_apply_ne h1, Pi.zero_apply]
    · rw [if_neg h2]

theorem atPlace_mul (M N : Matrix (Fin a) (Fin a) (ι → ℂ)) (w : ι) :
    atPlace (M * N) w = atPlace M w * atPlace N w := by
  ext p q
  simp [atPlace, Matrix.mul_apply, Finset.sum_apply]

@[simp] theorem blk_mul (e : Fin a × ι ≃ Fin n) (M N : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    blk e (M * N) = blk e M * blk e N := by
  have h : GlobalTheory.CompanionTheory.AdmGL.atPlace (M * N) = fun w => GlobalTheory.CompanionTheory.AdmGL.atPlace M w * GlobalTheory.CompanionTheory.AdmGL.atPlace N w :=
    funext (GlobalTheory.CompanionTheory.AdmGL.atPlace_mul M N)
  simp only [GlobalTheory.CompanionTheory.AdmGL.blk, Matrix.reindex_apply]
  rw [h, Matrix.blockDiagonal_mul]
  exact (Matrix.submatrix_mul_equiv _ _ _ e.symm _).symm

@[simp] theorem blk_add (e : Fin a × ι ≃ Fin n) (M N : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    blk e (M + N) = blk e M + blk e N := by
  ext i j
  rw [Matrix.add_apply, GlobalTheory.CompanionTheory.AdmGL.blk_apply, GlobalTheory.CompanionTheory.AdmGL.blk_apply,
    GlobalTheory.CompanionTheory.AdmGL.blk_apply]
  split_ifs <;> simp

@[simp] theorem blk_smul (e : Fin a × ι ≃ Fin n) (c : ℂ) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    blk e (c • M) = c • blk e M := by
  ext i j
  rw [Matrix.smul_apply, GlobalTheory.CompanionTheory.AdmGL.blk_apply, GlobalTheory.CompanionTheory.AdmGL.blk_apply]
  split_ifs <;> simp

@[simp] theorem blk_conjTranspose (e : Fin a × ι ≃ Fin n) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    blk e Mᴴ = (blk e M)ᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply, GlobalTheory.CompanionTheory.AdmGL.blk_apply, GlobalTheory.CompanionTheory.AdmGL.blk_apply]
  by_cases h : (e.symm i).2 = (e.symm j).2
  · rw [if_pos h, if_pos h.symm, Matrix.conjTranspose_apply, Pi.star_apply, h]
  · rw [if_neg h, if_neg (Ne.symm h), star_zero]

theorem continuous_blk (e : Fin a × ι ≃ Fin n) : Continuous (blk e) := by
  apply continuous_matrix
  intro i j
  simp only [GlobalTheory.CompanionTheory.AdmGL.blk_apply]
  by_cases h : (e.symm i).2 = (e.symm j).2
  · simp only [if_pos h]
    exact (continuous_apply _).comp (continuous_id.matrix_elem _ _)
  · simp only [if_neg h]
    exact continuous_const

theorem continuous_unblk (e : Fin a × ι ≃ Fin n) : Continuous (unblk e) := by
  apply continuous_matrix
  intro p q
  apply continuous_pi
  intro w
  simp only [GlobalTheory.CompanionTheory.AdmGL.unblk, Matrix.of_apply]
  exact continuous_id.matrix_elem _ _

theorem det_apply_place (M : Matrix (Fin a) (Fin a) (ι → ℂ)) (w : ι) : M.det w = (atPlace M w).det :=
  RingHom.map_det (Pi.evalRingHom (fun _ : ι => ℂ) w) M

theorem det_blk (e : Fin a × ι ≃ Fin n) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    (blk e M).det = ∏ w, (atPlace M w).det := by
  rw [blk, Matrix.det_reindex_self, Matrix.det_blockDiagonal]

theorem isUnit_blk_iff (e : Fin a × ι ≃ Fin n) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    IsUnit (blk e M) ↔ IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det, GlobalTheory.CompanionTheory.AdmGL.det_blk, Pi.isUnit_iff]
  simp [isUnit_iff_ne_zero, GlobalTheory.CompanionTheory.AdmGL.det_apply_place, Finset.prod_ne_zero_iff]

theorem mem_blkG_iff (e : Fin a × ι ≃ Fin n) {g : Matrix (Fin n) (Fin n) ℂ} :
    g ∈ blkG e ↔ IsUnit g ∧ blk e (unblk e g) = g := by
  constructor
  · rintro ⟨M, hM, rfl⟩
    exact ⟨(GlobalTheory.CompanionTheory.AdmGL.isUnit_blk_iff e M).2 hM, by rw [GlobalTheory.CompanionTheory.AdmGL.unblk_blk]⟩
  · rintro ⟨hg, hg'⟩
    refine ⟨GlobalTheory.CompanionTheory.AdmGL.unblk e g, ?_, hg'⟩
    rw [← hg'] at hg
    exact (GlobalTheory.CompanionTheory.AdmGL.isUnit_blk_iff e _).1 hg

end GlobalTheory.CompanionTheory.AdmGL

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardCosetRepsEqRelIndex
section
open Matrix

namespace GlobalTheory.CompanionTheory.Transversal

theorem card_eq_relIndex (X : Type) [AddCommGroup X] (A L : AddSubgroup X) (T : Finset X)
    (_hLA : L ≤ A) (hT : ∀ t ∈ T, t ∈ A) (hu : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ L) :
    T.card = L.relIndex A := by
  classical
  let f : T → A ⧸ L.addSubgroupOf A := fun t => QuotientAddGroup.mk ⟨t.1, hT t.1 t.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨t, ht⟩ ⟨t', ht'⟩ h
      have h' : -(⟨t, hT t ht⟩ : A) + ⟨t', hT t' ht'⟩ ∈ L.addSubgroupOf A := QuotientAddGroup.eq.mp h
      rw [AddSubgroup.mem_addSubgroupOf] at h'
      have hL : t - t' ∈ L := by
        have h2 := L.neg_mem h'
        convert h2 using 1
        push_cast
        abel
      obtain ⟨u, _, hu'⟩ := hu t (hT t ht)
      have e1 : t = u := hu' t ⟨ht, by simp⟩
      have e2 : t' = u := hu' t' ⟨ht', hL⟩
      exact Subtype.ext (e1.trans e2.symm)
    · intro q
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
      obtain ⟨t, ⟨ht, hat⟩, _⟩ := hu a.1 a.2
      refine ⟨⟨t, ht⟩, QuotientAddGroup.eq.mpr ?_⟩
      rw [AddSubgroup.mem_addSubgroupOf]
      have e : ((-(⟨t, hT t ht⟩ : A) + a : A) : X) = a.1 - t := by
        push_cast
        abel
      rw [e]
      exact hat
  calc T.card = Nat.card T := (Nat.card_eq_finsetCard T).symm
    _ = Nat.card (A ⧸ L.addSubgroupOf A) := Nat.card_congr (Equiv.ofBijective f hf)
    _ = L.relIndex A := by simp only [AddSubgroup.relIndex, AddSubgroup.index]

end GlobalTheory.CompanionTheory.Transversal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardEqCardKerMulCardRange
section
namespace GlobalTheory.CompanionTheory.Counting

theorem card_eq_card_ker_mul_card_range (R A B : Type) [Ring R] [AddCommGroup A] [Module R A] [Finite A]
    [AddCommGroup B] [Module R B] (f : A →ₗ[R] B) :
    Nat.card A = Nat.card ↥(LinearMap.ker f) * Nat.card ↥(LinearMap.range f) := by
  have h1 : Nat.card (A ⧸ LinearMap.ker f) = Nat.card ↥(LinearMap.range f) :=
    Nat.card_congr f.quotKerEquivRange.toEquiv
  have h2 : Nat.card A = Nat.card (A ⧸ (LinearMap.ker f).toAddSubgroup) * Nat.card (LinearMap.ker f).toAddSubgroup :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  have h3 : Nat.card (A ⧸ (LinearMap.ker f).toAddSubgroup) = Nat.card (A ⧸ LinearMap.ker f) := rfl
  have h4 : Nat.card (LinearMap.ker f).toAddSubgroup = Nat.card ↥(LinearMap.ker f) := rfl
  rw [h2, h3, h4, h1, Nat.mul_comm]

end GlobalTheory.CompanionTheory.Counting
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CartanDecompositionLieAlgebra
section
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.IwasawaGen

theorem skew_add_upper {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ)
    (hanti : Antitone h)
    (hf : ∀ (f : ℝ → ℝ), ∀ X ∈ 𝔤, (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) ∈ 𝔤)
    (hstar : ∀ X ∈ 𝔤, Xᴴ ∈ 𝔤)
    (hreg : ∀ Y ∈ 𝔤, Yᴴ = Y → Matrix.diagonal (fun i => (h i : ℂ)) * Y =
      Y * Matrix.diagonal (fun i => (h i : ℂ)) → Y.IsDiag) :
    ∀ X ∈ 𝔤, ∃ A ∈ 𝔤, ∃ B ∈ 𝔤, X = A + B ∧ Aᴴ = -A ∧ B.BlockTriangular id := by
  intro X hX
  obtain ⟨P, hP, P_ent⟩ : ∃ P ∈ 𝔤, ∀ i j, P i j = if h j < h i then X i j else 0 := by
    refine ⟨_, hf (fun t => if 0 < t then 1 else 0) X hX, fun i j => ?_⟩
    by_cases hij : h j < h i
    · simp [hij]
    · simp [hij]
  obtain ⟨Z, hZ, Z_ent⟩ : ∃ Z ∈ 𝔤, ∀ i j, Z i j = if h i = h j then X i j else 0 := by
    refine ⟨_, hf (fun t => if t = 0 then 1 else 0) X hX, fun i j => ?_⟩
    by_cases hij : h i = h j
    · simp [hij]
    · simp [hij, sub_eq_zero]
  obtain ⟨M, hM, M_ent⟩ : ∃ M ∈ 𝔤, ∀ i j, M i j = if h i < h j then X i j else 0 := by
    refine ⟨_, hf (fun t => if t < 0 then 1 else 0) X hX, fun i j => ?_⟩
    by_cases hij : h i < h j
    · simp [hij]
    · simp [hij]
  have hsum : X = P + Z + M := by
    ext i j
    simp only [Matrix.add_apply, P_ent, Z_ent, M_ent]
    rcases lt_trichotomy (h i) (h j) with hij | hij | hij
    · simp [hij, hij.ne, not_lt.2 hij.le]
    · simp [hij]
    · simp [hij, hij.ne', not_lt.2 hij.le]
  set Y : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℝ) • (Z + Zᴴ) with hYdef
  have hY : Y ∈ 𝔤 := 𝔤.smul_mem _ (𝔤.add_mem hZ (hstar Z hZ))
  have Y_herm : Yᴴ = Y := by
    ext i j
    simp [hYdef, Matrix.conjTranspose_apply, add_comm]
  have Y_ent : ∀ i j, h i ≠ h j → Y i j = 0 := by
    intro i j hij
    simp [hYdef, Matrix.conjTranspose_apply, Z_ent, hij, hij.symm]
  have Y_comm : Matrix.diagonal (fun i => (h i : ℂ)) * Y =
      Y * Matrix.diagonal (fun i => (h i : ℂ)) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : h i = h j
    · rw [hij, mul_comm]
    · rw [Y_ent i j hij]; simp
  have Y_diag : Y.IsDiag := hreg Y hY Y_herm Y_comm
  refine ⟨(1 / 2 : ℝ) • (Z - Zᴴ) + M - Mᴴ, ?_, P + Y + Mᴴ, ?_, ?_, ?_, ?_⟩
  · exact 𝔤.sub_mem (𝔤.add_mem (𝔤.smul_mem _ (𝔤.sub_mem hZ (hstar Z hZ))) hM) (hstar M hM)
  · exact 𝔤.add_mem (𝔤.add_mem hP hY) (hstar M hM)
  · have hZsplit : Z = (1 / 2 : ℝ) • (Z - Zᴴ) + Y := by
      rw [hYdef, ← smul_add]
      have : Z - Zᴴ + (Z + Zᴴ) = (2 : ℝ) • Z := by
        rw [two_smul]; abel
      rw [this, smul_smul]; norm_num
    calc X = P + Z + M := hsum
      _ = P + ((1 / 2 : ℝ) • (Z - Zᴴ) + Y) + M := by rw [← hZsplit]
      _ = (1 / 2 : ℝ) • (Z - Zᴴ) + M - Mᴴ + (P + Y + Mᴴ) := by abel
  · simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_conjTranspose, star_trivial]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply]
    simp only [smul_eq_mul, Complex.real_smul, smul_sub]
    ring
  · intro i j hji
    have hji' : j < i := hji
    have hle : h i ≤ h j := hanti hji'.le
    have h1 : P i j = 0 := by
      rw [P_ent, if_neg (not_lt.2 hle)]
    have h2 : Y i j = 0 := Y_diag hji'.ne'
    have h3 : Mᴴ i j = 0 := by
      rw [Matrix.conjTranspose_apply, M_ent, if_neg (not_lt.2 hle)]; simp
    simp only [Matrix.add_apply, h1, h2, h3, add_zero]

end GlobalTheory.CompanionTheory.IwasawaGen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralizerRegularCommutes
section
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.MatrixComm

theorem commute_diagonal_of_dominated {n : ℕ} (d e : Fin n → ℂ)
    (Z : Matrix (Fin n) (Fin n) ℂ) (hZ : Matrix.diagonal d * Z = Z * Matrix.diagonal d)
    (hde : ∀ i j, d i = d j → e i = e j) :
    Z * Matrix.diagonal e = Matrix.diagonal e * Z := by
  ext i j
  have hij := congrFun (congrFun hZ i) j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hij
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hz : Z i j = 0
  · simp [hz]
  · have hd : d i = d j := by
      have : Z i j * d i = Z i j * d j := by rw [mul_comm (Z i j) (d i)]; exact hij
      exact mul_left_cancel₀ hz this
    rw [hde i j hd, mul_comm]

theorem commute_of_dominated_diag {n : ℕ} (U H A Y : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hH : (Uᴴ * H * U).IsDiag) (hA : (Uᴴ * A * U).IsDiag)
    (hdom : ∀ i j, (Uᴴ * H * U) i i = (Uᴴ * H * U) j j → (Uᴴ * A * U) i i = (Uᴴ * A * U) j j)
    (hHY : H * Y = Y * H) : Y * A = A * Y := by
  have h2 : U * Uᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hU
    simpa [Matrix.star_eq_conjTranspose] using this
  have conj_mul : ∀ P Q : Matrix (Fin n) (Fin n) ℂ,
      (Uᴴ * P * U) * (Uᴴ * Q * U) = Uᴴ * (P * Q) * U := by
    intro P Q
    calc (Uᴴ * P * U) * (Uᴴ * Q * U) = Uᴴ * P * (U * Uᴴ) * Q * U := by
          simp only [Matrix.mul_assoc]
      _ = Uᴴ * (P * Q) * U := by
          rw [h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have back : ∀ P : Matrix (Fin n) (Fin n) ℂ, U * (Uᴴ * P * U) * Uᴴ = P := by
    intro P
    calc U * (Uᴴ * P * U) * Uᴴ = (U * Uᴴ) * P * (U * Uᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = P := by rw [h2]; simp
  have hcomm : (Uᴴ * H * U) * (Uᴴ * Y * U) = (Uᴴ * Y * U) * (Uᴴ * H * U) := by
    rw [conj_mul, conj_mul, hHY]
  have hdH : Matrix.diagonal (fun i => (Uᴴ * H * U) i i) = Uᴴ * H * U := hH.diagonal_diag
  have hdA : Matrix.diagonal (fun i => (Uᴴ * A * U) i i) = Uᴴ * A * U := hA.diagonal_diag
  have key := commute_diagonal_of_dominated (fun i => (Uᴴ * H * U) i i)
    (fun i => (Uᴴ * A * U) i i) (Uᴴ * Y * U) (by rw [hdH]; exact hcomm) hdom
  rw [hdA, conj_mul, conj_mul] at key
  have := congrArg (fun M => U * M * Uᴴ) key
  simpa only [back] using this

end GlobalTheory.CompanionTheory.MatrixComm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComapMulVecCompactOpen
section
open Matrix

namespace GlobalTheory.CompanionTheory.Dblock.ComapLat

theorem comap_mulVec_compact_open : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (g : Matrix (Fin n) (Fin n) k), IsUnit g → ∀ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → IsCompact ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) ∧ IsOpen ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) := by
  intro k _ _ _ _ n g hg A hc ho
  haveI : IsTopologicalRing k := inferInstance
  have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hg
  have hcont : ∀ m : Matrix (Fin n) (Fin n) k, Continuous (fun x : Fin n → k => m.mulVec x) :=
    fun m => continuous_const.matrix_mulVec continuous_id
  have hset : ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k))
      = (fun x : Fin n → k => g.mulVec x) ⁻¹' (A : Set (Fin n → k)) := rfl
  rw [hset]
  refine ⟨?_, ho.preimage (hcont g)⟩
  have himg : (fun x : Fin n → k => g.mulVec x) ⁻¹' (A : Set (Fin n → k))
      = (fun x : Fin n → k => g⁻¹.mulVec x) '' (A : Set (Fin n → k)) := by
    ext x
    constructor
    · intro hx
      refine ⟨g.mulVec x, hx, ?_⟩
      simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g hdet, Matrix.one_mulVec]
    · rintro ⟨y, hy, rfl⟩
      simp only [Set.mem_preimage, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv g hdet,
        Matrix.one_mulVec]
      exact hy
  rw [himg]
  exact hc.image (hcont g⁻¹)

end GlobalTheory.CompanionTheory.Dblock.ComapLat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactScaledIntoNhds
section
open ValuativeRel MeasureTheory Matrix
open Filter Topology

namespace GlobalTheory.CompanionTheory.CompactScaling

theorem exists_pow_smul_mem : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (K : Set (Fin n → k)), IsCompact K → ∀ U ∈ nhds (0 : Fin n → k), ∀ ϖ : k, valuation k ϖ < 1 → ∃ l : ℕ, ∀ x ∈ K, ϖ ^ l • x ∈ U := by
  intro k _ _ _ _ n K hK U hU ϖ hϖ
  have hpow : Tendsto (fun l : ℕ => ϖ ^ l) atTop (𝓝 (0 : k)) := by
    rw [(IsValuativeTopology.hasBasis_nhds_zero k).tendsto_right_iff]
    intro γ _
    obtain ⟨m, hm⟩ := exists_pow_lt₀ hϖ γ
    rw [eventually_atTop]
    refine ⟨m, fun l hl => ?_⟩
    simp only [Set.mem_ofPred_eq, map_pow]
    exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hϖ.le hl) hm
  have hnear : ∀ᶠ c in 𝓝 (0 : k), ∀ x ∈ K, c • x ∈ U := by
    refine hK.eventually_forall_of_forall_eventually (fun x _ => ?_)
    have hcont : Continuous (fun p : k × (Fin n → k) => p.1 • p.2) :=
      continuous_fst.smul continuous_snd
    have hlim : Tendsto (fun p : k × (Fin n → k) => p.1 • p.2) (𝓝 (0, x)) (𝓝 0) := by
      simpa using hcont.tendsto (0, x)
    exact hlim hU
  exact (hpow.eventually hnear).exists

end GlobalTheory.CompanionTheory.CompactScaling
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactSetFiniteCosetRepresentatives
section
open scoped Topology

namespace GlobalTheory.CompanionTheory.OpenSubgroupCosets

theorem exists_finset_unique_coset_reps :
    ∀ {E : Type} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
      (D : AddSubgroup E), IsOpen (D : Set E) → ∀ (R : Set E), IsCompact R →
      ∃ S : Finset E, (∀ s ∈ S, s ∈ R) ∧ ∀ x ∈ R, ∃! s, s ∈ S ∧ x - s ∈ D := by
  intro E _ _ _ D hD R hR
  classical
  obtain ⟨t, ht⟩ := hR.elim_finite_subcover (fun x : E => (fun y => y - x) ⁻¹' (D : Set E))
    (fun x => hD.preimage (continuous_sub_right x))
    (fun r _ => Set.mem_iUnion.2 ⟨r, by simp⟩)
  set π : E → E ⧸ D := QuotientAddGroup.mk with hπ
  have hfin : (π '' R).Finite := by
    apply (t.finite_toSet.image π).subset
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨x, hx, hrx⟩ : ∃ x ∈ t, r - x ∈ D := by simpa using ht hr
    refine ⟨x, hx, ?_⟩
    apply QuotientAddGroup.eq_iff_sub_mem.2
    rw [← neg_sub]
    exact D.neg_mem hrx
  have hrep : ∀ c ∈ π '' R, ∃ r, r ∈ R ∧ π r = c := by
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨r, hr, rfl⟩
  choose! f hfR hfπ using hrep
  refine ⟨hfin.toFinset.image f, ?_, ?_⟩
  · intro s hs
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hs
    exact hfR c (hfin.mem_toFinset.1 hc)
  · intro x hx
    have hxc : π x ∈ π '' R := ⟨x, hx, rfl⟩
    refine ⟨f (π x), ⟨Finset.mem_image.2 ⟨π x, hfin.mem_toFinset.2 hxc, rfl⟩, ?_⟩, ?_⟩
    · exact QuotientAddGroup.eq_iff_sub_mem.1 (hfπ (π x) hxc).symm
    · rintro s ⟨hs, hxs⟩
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hs
      have hc' := hfin.mem_toFinset.1 hc
      have h1 : π x = c := by
        rw [← hfπ c hc']
        exact QuotientAddGroup.eq_iff_sub_mem.2 hxs
      rw [h1]

end GlobalTheory.CompanionTheory.OpenSubgroupCosets
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoreR
section
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Inf0

open scoped Matrix

variable {P ι : Type}

def qR0 [Fintype ι] (A : P → Matrix ι ι ℝ) (x : P → ι → ℝ) : P → ℝ :=
  fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (A w *ᵥ x w))

def gaussR [Fintype P] [Fintype ι] (Pm : P → Matrix ι ι ℝ) (x : P → ι → ℝ) : ℝ :=
  Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w))

def boxR [Fintype ι] (t : P → ℝ) : Set (P → ι → ℝ) :=
  {x | ∀ w, ‖x w‖ ≤ t w}

def coreR [Fintype ι] (δ R : ℝ) : Set (P → ι → ℝ) :=
  {x | ∀ w, δ ≤ ‖x w‖ ∧ ‖x w‖ ≤ R}

end GlobalTheory.CompanionTheory.WeilSiegel.Inf0
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFractionRingInteger
section
namespace GlobalTheory.CompanionTheory.LocalFieldValuationRing

theorem isFractionRing_integer (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : IsFractionRing (ValuativeRel.valuation k).integer k :=
  (Valuation.integer.integers (ValuativeRel.valuation k)).isFractionRing

end GlobalTheory.CompanionTheory.LocalFieldValuationRing
end

