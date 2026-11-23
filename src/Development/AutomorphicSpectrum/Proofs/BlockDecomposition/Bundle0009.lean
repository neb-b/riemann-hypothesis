module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrincipalCongruence
section
open Matrix

namespace GlobalTheory.CompanionTheory.PrincipalCongruence

variable {k Γ : Type*} [Field k] [LinearOrderedCommGroupWithZero Γ]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem entry_mul_le (v : Valuation k Γ) {r s : Γ} (hs : s ≤ 1)
    {A B : Matrix n n k} (hA : ∀ i j, v (A i j) ≤ r) (hB : ∀ i j, v (B i j) ≤ s) (i j : n) :
    v ((A * B) i j) ≤ r := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le v fun l _ => ?_
  rw [map_mul]
  calc v (A i l) * v (B l j) ≤ r * s := mul_le_mul' (hA i l) (hB l j)
    _ ≤ r * 1 := mul_le_mul' le_rfl hs
    _ = r := mul_one r

theorem inv_entry_le_one (v : Valuation k Γ) {r : Γ} (hr : r < 1)
    {A B : Matrix n n k} (hBA : B * (1 + A) = 1) (hA : ∀ i j, v (A i j) ≤ r) (i j : n) :
    v (B i j) ≤ 1 := by
  haveI : Nonempty (n × n) := ⟨(i, j)⟩
  obtain ⟨⟨a, b⟩, hmax⟩ := Finite.exists_max (fun p : n × n => v (B p.1 p.2))
  have hM : ∀ i j, v (B i j) ≤ v (B a b) := fun i j => hmax (i, j)
  refine (hM i j).trans ?_
  by_contra hlt
  have hgt : 1 < v (B a b) := not_le.mp hlt
  have hpos : 0 < v (B a b) := zero_lt_one.trans hgt
  have hB : B = 1 - B * A := by
    have : B + B * A = 1 := by rw [← hBA, mul_add, mul_one]
    exact eq_sub_of_add_eq this
  have hprod : v ((B * A) a b) ≤ v (B a b) * r := by
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_le v fun l _ => ?_
    rw [map_mul]
    exact mul_le_mul' (hM a l) (hA l b)
  have hlt' : v (B a b) * r < v (B a b) := by
    calc v (B a b) * r < v (B a b) * 1 := by
          exact mul_lt_mul_of_pos_left hr hpos
      _ = v (B a b) := mul_one _
  have hone : v ((1 : Matrix n n k) a b) ≤ 1 := by
    by_cases h : a = b
    · rw [h, Matrix.one_apply_eq, map_one]
    · rw [Matrix.one_apply_ne h, map_zero]
      exact zero_le_one
  have hentry : B a b = (1 : Matrix n n k) a b - (B * A) a b := by
    conv_lhs => rw [hB]
    rfl
  have hle : v (B a b) ≤ max (v ((1 : Matrix n n k) a b)) (v ((B * A) a b)) := by
    rw [hentry]
    exact Valuation.map_sub v _ _
  rcases le_max_iff.mp hle with h | h
  · exact absurd (h.trans hone) (not_le.mpr hgt)
  · exact absurd (h.trans hprod) (not_le.mpr hlt')

def principalCongruence (v : Valuation k Γ) (r : Γ) (hr : r < 1) :
    Subgroup (GL n k) where
  carrier := {g | ∀ i j, v ((g : Matrix n n k) i j - (1 : Matrix n n k) i j) ≤ r}
  one_mem' := by
    intro i j
    simp
  mul_mem' := by
    intro g h hg hh i j
    have hg' : ∀ i j, v (((g : Matrix n n k) - 1) i j) ≤ r := hg
    have hh' : ∀ i j, v (((h : Matrix n n k) - 1) i j) ≤ r := hh
    have key : ((g * h : GL n k) : Matrix n n k) - 1 =
        ((g : Matrix n n k) - 1) * ((h : Matrix n n k) - 1) +
          (((g : Matrix n n k) - 1) + ((h : Matrix n n k) - 1)) := by
      rw [Units.val_mul]
      noncomm_ring
    have key' : ((g * h : GL n k) : Matrix n n k) i j - (1 : Matrix n n k) i j =
        (((g : Matrix n n k) - 1) * ((h : Matrix n n k) - 1)) i j +
          ((((g : Matrix n n k) - 1) i j) + (((h : Matrix n n k) - 1) i j)) := by
      rw [← Matrix.sub_apply, key]
      rfl
    rw [key']
    exact Valuation.map_add_le v (entry_mul_le v hr.le hg' hh' i j)
      (Valuation.map_add_le v (hg' i j) (hh' i j))
  inv_mem' := by
    intro g hg i j
    have hg' : ∀ i j, v (((g : Matrix n n k) - 1) i j) ≤ r := hg
    have hBA : ((g⁻¹ : GL n k) : Matrix n n k) * (1 + ((g : Matrix n n k) - 1)) = 1 := by
      rw [add_sub_cancel, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hint := inv_entry_le_one v hr hBA hg'
    have key : ((g⁻¹ : GL n k) : Matrix n n k) - 1 =
        -(((g⁻¹ : GL n k) : Matrix n n k) * ((g : Matrix n n k) - 1)) := by
      rw [mul_sub, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
      abel
    have key' : ((g⁻¹ : GL n k) : Matrix n n k) i j - (1 : Matrix n n k) i j =
        -((((g⁻¹ : GL n k) : Matrix n n k) * ((g : Matrix n n k) - 1)) i j) := by
      rw [← Matrix.sub_apply, key]
      rfl
    rw [key', Valuation.map_neg, Matrix.mul_apply]
    refine Valuation.map_sum_le v fun l _ => ?_
    rw [map_mul]
    calc v (((g⁻¹ : GL n k) : Matrix n n k) i l) * v (((g : Matrix n n k) - 1) l j)
        ≤ 1 * r := mul_le_mul' (hint i l) (hg' l j)
      _ = r := one_mul r

theorem exists_principalCongruence :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N : ℕ) (t : k), t ≠ 0 → ValuativeRel.valuation k (t) < 1 →
      ∃ H : Subgroup (GL (Fin N) k), (H : Set (GL (Fin N) k)) =
        {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
          ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
            ValuativeRel.valuation k (t)} := by
  intro k _ _ _ _ N t _ ht
  exact ⟨principalCongruence (ValuativeRel.valuation k) _ ht, rfl⟩

end GlobalTheory.CompanionTheory.PrincipalCongruence
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRegularElementAbelian
section
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.IwaGen

theorem exists_regular_point : ∀ {n : ℕ} (𝔞 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (U : Matrix (Fin n) (Fin n) ℂ), ∃ H ∈ 𝔞, ∀ i j, (Uᴴ * H * U) i i = (Uᴴ * H * U) j j →
      ∀ A ∈ 𝔞, (Uᴴ * A * U) i i = (Uᴴ * A * U) j j := by
  classical
  intro n 𝔞 U
  let L : Fin n × Fin n → (↥𝔞 →ₗ[ℝ] ℂ) := fun p =>
    { toFun := fun A => (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.1 p.1
        - (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.2 p.2
      map_add' := by
        intro A B
        simp only [Submodule.coe_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
        ring
      map_smul' := by
        intro c A
        simp only [Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
          RingHom.id_apply, smul_sub] }
  have hL : ∀ (p : Fin n × Fin n) (A : ↥𝔞), L p A =
      (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.1 p.1
        - (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.2 p.2 := fun _ _ => rfl
  let s : Finset (Submodule ℝ ↥𝔞) :=
    (Finset.univ.image fun p => LinearMap.ker (L p)).erase ⊤
  have hs : (⊤ : Submodule ℝ ↥𝔞) ∉ s := Finset.notMem_erase _ _
  obtain ⟨H, hH⟩ := (Set.ne_univ_iff_exists_notMem _).1
    (Subspace.biUnion_ne_univ_of_top_notMem hs)
  refine ⟨H, H.2, fun i j hij A hA => ?_⟩
  have hker : H ∈ LinearMap.ker (L (i, j)) := by
    rw [LinearMap.mem_ker, hL]
    exact sub_eq_zero.2 hij
  have htop : LinearMap.ker (L (i, j)) = ⊤ := by
    by_contra hne
    apply hH
    refine Set.mem_biUnion (x := LinearMap.ker (L (i, j))) ?_ hker
    exact Finset.mem_coe.2 (Finset.mem_erase.2
      ⟨hne, Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩⟩)
  have hA' : (⟨A, hA⟩ : ↥𝔞) ∈ LinearMap.ker (L (i, j)) := by
    rw [htop]
    exact Submodule.mem_top
  rw [LinearMap.mem_ker, hL] at hA'
  exact sub_eq_zero.1 hA'

end GlobalTheory.CompanionTheory.IwaGen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmulEqOnFinset
section
namespace GlobalTheory.CompanionTheory.SimpleDensity

theorem exists_smul_eq_on_finset {R ι : Type} [Ring R] [Fintype ι] (M : ι → Type)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, IsSimpleModule R (M i)]
    (hne : ∀ i j, i ≠ j → ∀ φ : M i →ₗ[R] M j, φ = 0)
    (f : ∀ i, M i →+ M i)
    (hf : ∀ i (φ : M i →ₗ[R] M i) x, f i (φ x) = φ (f i x))
    (s : Finset (∀ i, M i)) :
    ∃ r : R, ∀ m ∈ s, ∀ i, f i (m i) = r • m i := by
  classical
  have key : ∀ (φ : Module.End R (∀ i, M i)) (m : ∀ i, M i) (i : ι),
      φ m i = ((LinearMap.proj i) ∘ₗ φ ∘ₗ LinearMap.single R M i) (m i) := by
    intro φ m i
    have hm : m = ∑ j, Pi.single j (m j) := (Finset.univ_sum_single m).symm
    conv_lhs => rw [hm]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply, Finset.sum_eq_single i]
    · rfl
    · intro j _ hj
      have := hne j i hj ((LinearMap.proj i) ∘ₗ φ ∘ₗ LinearMap.single R M j)
      exact LinearMap.congr_fun this (m j)
    · simp
  let F : Module.End (Module.End R (∀ i, M i)) (∀ i, M i) :=
    { toFun := fun m i => f i (m i)
      map_add' := fun a b => by ext i; simp
      map_smul' := fun φ m => by
        ext i
        simp only [Module.End.smul_def, RingHom.id_apply]
        rw [key φ m i, key φ _ i, hf] }
  obtain ⟨r, hr⟩ := jacobson_density F s
  exact ⟨r, fun m hm i => congrFun (hr m hm) i⟩

theorem exists_scalar_of_simple {A N : Type} [Ring A] [Algebra ℂ A] [AddCommGroup N] [Module ℂ N] [Module A N]
    [IsScalarTower ℂ A N] [FiniteDimensional ℂ N] [IsSimpleModule A N] (φ : N →ₗ[A] N) :
    ∃ c : ℂ, ∀ x, φ x = c • x := by
  haveI : Nontrivial N := IsSimpleModule.nontrivial A N
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (φ.restrictScalars ℂ : Module.End ℂ N)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  refine ⟨c, ?_⟩
  have hw1 : φ w = c • w := hw.apply_eq_smul
  let ψ : N →ₗ[A] N := φ - c • LinearMap.id
  rcases LinearMap.injective_or_eq_zero ψ with hi | h0
  · exfalso
    have hz : ψ w = 0 := by simp [ψ, hw1]
    exact hw.2 (hi (by rw [hz, map_zero]))
  · intro x
    have := LinearMap.congr_fun h0 x
    simpa [ψ, sub_eq_zero] using this

theorem exists_smul_eq_end : ∀ (A : Type) [Ring A] [Algebra ℂ A] (J : Type) [Fintype J] (M : J → Type)
    [∀ j, AddCommGroup (M j)] [∀ j, Module ℂ (M j)] [∀ j, Module A (M j)] [∀ j, IsScalarTower ℂ A (M j)]
    [∀ j, FiniteDimensional ℂ (M j)] [∀ j, IsSimpleModule A (M j)],
    (∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j) →
      ∀ f : ∀ j, Module.End ℂ (M j), ∃ a : A, ∀ j (x : M j), a • x = f j x := by
  intro A _ _ J _ M _ _ _ _ _ _ hiso f
  classical
  have hne : ∀ i j, i ≠ j → ∀ φ : M i →ₗ[A] M j, φ = 0 := by
    intro i j hij φ
    by_contra h
    exact hij (hiso i j ⟨LinearEquiv.ofBijective φ (LinearMap.bijective_of_ne_zero h)⟩)
  have hf : ∀ i (φ : M i →ₗ[A] M i) x,
      (f i).toAddMonoidHom (φ x) = φ ((f i).toAddMonoidHom x) := by
    intro i φ x
    obtain ⟨c, hc⟩ := exists_scalar_of_simple φ
    simp [hc]
  let b : ∀ j, Module.Basis (Module.Free.ChooseBasisIndex ℂ (M j)) ℂ (M j) := fun j => Module.Free.chooseBasis ℂ (M j)
  haveI : ∀ j, Fintype (Module.Free.ChooseBasisIndex ℂ (M j)) := fun j => inferInstance
  let s : Finset (∀ j, M j) :=
    Finset.univ.biUnion fun j => Finset.univ.image fun k => (Pi.single j (b j k) : ∀ j, M j)
  obtain ⟨r, hr⟩ := exists_smul_eq_on_finset M hne (fun j => (f j).toAddMonoidHom) hf s
  refine ⟨r, fun j x => ?_⟩
  have hlin : (Algebra.lsmul ℂ ℂ (M j) r : Module.End ℂ (M j)) = f j := by
    refine (b j).ext fun k => ?_
    have hm : (Pi.single j (b j k) : ∀ j, M j) ∈ s :=
      Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩⟩
    have := hr _ hm j
    simpa using this.symm
  exact LinearMap.congr_fun hlin x

end GlobalTheory.CompanionTheory.SimpleDensity
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUdlOfIsUnit
section
namespace GlobalTheory.CompanionTheory.IwahoriUDL

open Matrix

variable {R : Type*} [CommRing R]

def ex (n : ℕ) : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv

theorem ex_inl {n : ℕ} (i : Fin n) : ex n (Sum.inl i) = i.castSucc := rfl

theorem ex_inr {n : ℕ} (k : Fin 1) : ex n (Sum.inr k) = Fin.last n := by
  have hk : k = 0 := Subsingleton.elim _ _
  subst hk
  ext
  simp [ex]

theorem one_ex {n : ℕ} (i j : Fin n ⊕ Fin 1) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (ex n i) (ex n j) =
      fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 (1 : Matrix (Fin 1) (Fin 1) R) i j := by
  rw [fromBlocks_one]
  simp [Matrix.one_apply]

def IsUp (I : Ideal R) {n : ℕ} (u : Matrix (Fin n) (Fin n) R) : Prop :=
  (∀ i j, u i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I) ∧ (∀ i j, j < i → u i j = 0) ∧
    ∀ i, u i i = 1

def IsLo (I : Ideal R) {n : ℕ} (l : Matrix (Fin n) (Fin n) R) : Prop :=
  (∀ i j, l i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I) ∧ (∀ i j, i < j → l i j = 0) ∧
    ∀ i, l i i = 1

def IsDi (I : Ideal R) {n : ℕ} (d : Matrix (Fin n) (Fin n) R) : Prop :=
  (∀ i j, d i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I) ∧ ∀ i j, i ≠ j → d i j = 0

theorem up_step {I : Ideal R} {n : ℕ} {u : Matrix (Fin n) (Fin n) R} (hu : IsUp I u)
    {x : Matrix (Fin n) (Fin 1) R} (hx : ∀ i k, x i k ∈ I) :
    IsUp I ((fromBlocks u x 0 1).submatrix (ex n).symm (ex n).symm) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    obtain ⟨j, rfl⟩ := (ex n).surjective j
    rw [one_ex, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · simpa using hu.1 i j
    · simpa using hx i j
    · simp
    · simp
  · intro i j hij
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    obtain ⟨j, rfl⟩ := (ex n).surjective j
    rw [submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · simp only [ex_inl, Fin.castSucc_lt_castSucc_iff] at hij
      simpa using hu.2.1 i j hij
    · simp only [ex_inl, ex_inr] at hij
      exact absurd hij (not_lt.mpr (Fin.le_last _))
    · simp
    · simp only [ex_inr, lt_self_iff_false] at hij
  · intro i
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    rw [submatrix_apply, Equiv.symm_apply_apply]
    rcases i with i | i
    · simpa using hu.2.2 i
    · simp

theorem lo_step {I : Ideal R} {n : ℕ} {l : Matrix (Fin n) (Fin n) R} (hl : IsLo I l)
    {y : Matrix (Fin 1) (Fin n) R} (hy : ∀ k j, y k j ∈ I) :
    IsLo I ((fromBlocks l 0 y 1).submatrix (ex n).symm (ex n).symm) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    obtain ⟨j, rfl⟩ := (ex n).surjective j
    rw [one_ex, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · simpa using hl.1 i j
    · simp
    · simpa using hy i j
    · simp
  · intro i j hij
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    obtain ⟨j, rfl⟩ := (ex n).surjective j
    rw [submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · simp only [ex_inl, Fin.castSucc_lt_castSucc_iff] at hij
      simpa using hl.2.1 i j hij
    · simp
    · simp only [ex_inl, ex_inr] at hij
      exact absurd hij (not_lt.mpr (Fin.le_last _))
    · simp only [ex_inr, lt_self_iff_false] at hij
  · intro i
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    rw [submatrix_apply, Equiv.symm_apply_apply]
    rcases i with i | i
    · simpa using hl.2.2 i
    · simp

theorem di_step {I : Ideal R} {n : ℕ} {d : Matrix (Fin n) (Fin n) R} (hd : IsDi I d)
    {a : Matrix (Fin 1) (Fin 1) R} (ha : ∀ k k', a k k' - (1 : Matrix (Fin 1) (Fin 1) R) k k' ∈ I) :
    IsDi I ((fromBlocks d 0 0 a).submatrix (ex n).symm (ex n).symm) := by
  refine ⟨?_, ?_⟩
  · intro i j
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    obtain ⟨j, rfl⟩ := (ex n).surjective j
    rw [one_ex, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · simpa using hd.1 i j
    · simp
    · simp
    · simpa using ha i j
  · intro i j hij
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    obtain ⟨j, rfl⟩ := (ex n).surjective j
    rw [submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · have : i ≠ j := fun h => hij (by rw [h])
      simpa using hd.2 i j this
    · simp
    · simp
    · exact absurd (by rw [Subsingleton.elim i j]) hij

theorem fromBlocks_udl {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (c : Matrix (Fin n) (Fin 1) R)
    (r : Matrix (Fin 1) (Fin n) R) (a b : Matrix (Fin 1) (Fin 1) R) (hab : a * b = 1)
    (hba : b * a = 1) (u d l : Matrix (Fin n) (Fin n) R) (h : A - c * b * r = u * d * l) :
    fromBlocks A c r a =
      fromBlocks u (c * b) 0 1 * fromBlocks d 0 0 a * fromBlocks l 0 (b * r) 1 := by
  have h' : A = u * d * l + c * b * r := by rw [← h]; abel
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.one_mul]
  rw [Matrix.mul_assoc c b a, hba, Matrix.mul_one, ← Matrix.mul_assoc a b r, hab, Matrix.one_mul]
  rw [h', Matrix.mul_assoc c b r]

theorem exists_udl_of_isUnit (I : Ideal R) (hI : ∀ x ∈ I, IsUnit (1 + x)) (n : ℕ) :
    ∀ g : Matrix (Fin n) (Fin n) R,
      (∀ i j, g i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I) →
        ∃ u d l : Matrix (Fin n) (Fin n) R, IsUp I u ∧ IsDi I d ∧ IsLo I l ∧ g = u * d * l := by
  induction n with
  | zero =>
    intro g _
    exact ⟨1, 1, 1, ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩,
      ⟨fun i => i.elim0, fun i => i.elim0⟩, ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩,
      Subsingleton.elim _ _⟩
  | succ n ih =>
    intro g hg
    set A : Matrix (Fin n) (Fin n) R := fun i j => g i.castSucc j.castSucc with hA
    set c : Matrix (Fin n) (Fin 1) R := fun i _ => g i.castSucc (Fin.last n) with hc
    set r : Matrix (Fin 1) (Fin n) R := fun _ j => g (Fin.last n) j.castSucc with hr
    set s : R := g (Fin.last n) (Fin.last n) with hs
    have hs1 : s - 1 ∈ I := by simpa [hs] using hg (Fin.last n) (Fin.last n)
    have hsu : IsUnit s := by simpa using hI _ hs1
    obtain ⟨t, hst⟩ := hsu.exists_right_inv
    have hts : t * s = 1 := by rw [mul_comm]; exact hst
    have hcI : ∀ i k, c i k ∈ I := fun i k => by
      have := hg i.castSucc (Fin.last n)
      rw [Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne, sub_zero] at this
      exact this
    have hrI : ∀ k j, r k j ∈ I := fun k j => by
      have := hg (Fin.last n) j.castSucc
      rw [Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne', sub_zero] at this
      exact this
    set a : Matrix (Fin 1) (Fin 1) R := fun _ _ => s with ha
    set b : Matrix (Fin 1) (Fin 1) R := fun _ _ => t with hb
    have hab : a * b = 1 := by
      ext i j
      rw [Subsingleton.elim i j, Matrix.mul_apply, Matrix.one_apply_eq]
      simp only [Finset.univ_unique, Finset.sum_singleton]
      exact hst
    have hba : b * a = 1 := by
      ext i j
      rw [Subsingleton.elim i j, Matrix.mul_apply, Matrix.one_apply_eq]
      simp only [Finset.univ_unique, Finset.sum_singleton]
      exact hts
    have hS : ∀ i j, (A - c * b * r) i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I := by
      intro i j
      have h1 : A i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I := by
        have := hg i.castSucc j.castSucc
        simpa [hA, Matrix.one_apply] using this
      have h2 : (c * b * r) i j ∈ I := by
        simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton]
        exact I.mul_mem_right _ (I.mul_mem_right _ (hcI i default))
      have h3 : (A - c * b * r) i j - (1 : Matrix (Fin n) (Fin n) R) i j =
          (A i j - (1 : Matrix (Fin n) (Fin n) R) i j) - (c * b * r) i j := by
        simp only [Matrix.sub_apply]
        ring
      rw [h3]
      exact I.sub_mem h1 h2
    obtain ⟨u, d, l, hu, hd, hl, hudl⟩ := ih _ hS
    have hcb : ∀ i k, (c * b) i k ∈ I := fun i k => by
      simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton]
      exact I.mul_mem_right _ (hcI i default)
    have hbr : ∀ k j, (b * r) k j ∈ I := fun k j => by
      simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton]
      exact I.mul_mem_left _ (hrI default j)
    have haI : ∀ k k', a k k' - (1 : Matrix (Fin 1) (Fin 1) R) k k' ∈ I := fun k k' => by
      simpa [ha, Matrix.one_apply, Subsingleton.elim k k'] using hs1
    refine ⟨_, _, _, up_step hu hcb, di_step hd haI, lo_step hl hbr, ?_⟩
    have hblock : g.submatrix (ex n) (ex n) = fromBlocks A c r a := by
      ext i j
      rcases i with i | i <;> rcases j with j | j
      · rw [submatrix_apply, ex_inl, ex_inl]; rfl
      · rw [submatrix_apply, ex_inl, ex_inr]; rfl
      · rw [submatrix_apply, ex_inr, ex_inl]; rfl
      · rw [submatrix_apply, ex_inr, ex_inr]; rfl
    have hg' : g = (fromBlocks A c r a).submatrix (ex n).symm (ex n).symm := by
      rw [← hblock]
      simp
    rw [hg', fromBlocks_udl A c r a b hab hba u d l hudl]
    simp only [Matrix.submatrix_mul_equiv]

theorem iwahori_udl : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (n : ℕ)
    (ϖ : R) (m : ℕ), Irreducible ϖ → 1 ≤ m → ∀ g : Matrix (Fin n) (Fin n) R,
    (∀ i j, g i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) →
    ∃ (u d l : Matrix (Fin n) (Fin n) R),
      (∀ i j, u i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) ∧
      (∀ i j, d i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) ∧
      (∀ i j, l i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) ∧
      (∀ i j, j < i → u i j = 0) ∧ (∀ i, u i i = 1) ∧ (∀ i j, i ≠ j → d i j = 0) ∧
      (∀ i j, i < j → l i j = 0) ∧ (∀ i, l i i = 1) ∧ g = u * d * l := by
  intro R _ _ _ n ϖ m hϖ hm g hg
  have hmem : ϖ ^ m ∈ IsLocalRing.maximalIdeal R :=
    Ideal.pow_mem_of_mem _ ((IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit) m (by omega)
  have hle : Ideal.span {ϖ ^ m} ≤ IsLocalRing.maximalIdeal R :=
    (Ideal.span_singleton_le_iff_mem _).mpr hmem
  have hI : ∀ x ∈ Ideal.span {ϖ ^ m}, IsUnit (1 + x) := by
    intro x hx
    by_contra hnu
    have h1 : 1 + x ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h2 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
      simpa using Ideal.sub_mem _ h1 (hle hx)
    exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal R).ne_top h2
  obtain ⟨u, d, l, hu, hd, hl, h⟩ := exists_udl_of_isUnit _ hI n g hg
  exact ⟨u, d, l, hu.1, hd.1, hl.1, hu.2.1, hu.2.2, hd.2, hl.2.1, hl.2.2, h⟩

end GlobalTheory.CompanionTheory.IwahoriUDL
end

