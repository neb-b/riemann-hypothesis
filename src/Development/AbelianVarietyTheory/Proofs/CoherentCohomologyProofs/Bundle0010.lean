module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexAcyclicIffQuasiIsoCechAug
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.XSmulMemWeightedHomogeneousSubmodule

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsXPowSmulEqZeroOfEqXSubOneSmul
section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

noncomputable section

namespace GlobalTheory

open GradedHilbert

section

variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι)

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in
private lemma decompose_X_smul_add_one (y : M) (m : ℤ) :
    (decompose ℳ ((X i : MvPolynomial ι R) • y) (m + 1) : M) =
      (X i : MvPolynomial ι R) • (decompose ℳ y m : M) := by
  classical
  have key : ∀ j, (decompose ℳ ((X i : MvPolynomial ι R) • (decompose ℳ y j : M)) (m + 1) : M)
      = if j = m then (X i : MvPolynomial ι R) • (decompose ℳ y m : M) else 0 := by
    intro j
    have hmem := _root_.GlobalTheory.X_smul_mem_gr ℳ i j _ (decompose ℳ y j).2
    split_ifs with hj
    · subst hj; exact decompose_of_mem_same ℳ hmem
    · exact decompose_of_mem_ne ℳ hmem (by omega)
  conv_lhs => rw [← sum_support_decompose ℳ y]
  rw [Finset.smul_sum, decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum]
  simp only [key]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [DFinsupp.notMem_support_iff.1 h]; simp

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in
private lemma decompose_X_sub_one_smul_add_one (w : M) (m : ℤ) :
    (decompose ℳ ((X i - 1 : MvPolynomial ι R) • w) (m + 1) : M) =
      (X i : MvPolynomial ι R) • (decompose ℳ w m : M) - (decompose ℳ w (m + 1) : M) := by
  rw [sub_smul, one_smul, decompose_sub, DirectSum.sub_apply, Submodule.coe_sub,
    decompose_X_smul_add_one]

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in
private lemma exists_decompose_eq_zero_of_lt (y : M) :
    ∃ N : ℤ, ∀ j < N, (decompose ℳ y j : M) = 0 := by
  classical
  obtain ⟨N, hN⟩ := (decompose ℳ y).support.bddBelow
  refine ⟨N, fun j hj => ?_⟩
  have : j ∉ (decompose ℳ y).support := fun h => by have := hN h; omega
  simp [DFinsupp.notMem_support_iff.1 this]

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in
private lemma exists_decompose_eq_zero_of_gt (y : M) :
    ∃ N : ℤ, ∀ j > N, (decompose ℳ y j : M) = 0 := by
  classical
  obtain ⟨N, hN⟩ := (decompose ℳ y).support.bddAbove
  refine ⟨N, fun j hj => ?_⟩
  have : j ∉ (decompose ℳ y).support := fun h => by have := hN h; omega
  simp [DFinsupp.notMem_support_iff.1 this]

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in
private lemma eq_zero_of_X_smul_recurrence_of_vanish_below {g : ℤ → M} {N c : ℤ} (hN : ∀ j < N, g j = 0)
    (hrec : ∀ m < c, g (m + 1) = (X i : MvPolynomial ι R) • g m) : g c = 0 := by
  have key : ∀ k : ℕ, g c = (X i : MvPolynomial ι R) ^ k • g (c - k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : c - (k : ℤ) = c - ((k + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
      rw [ih, e, hrec _ (by omega), ← mul_smul, ← pow_succ]
  rw [key (c - N + 1).toNat, hN _ (by omega), smul_zero]

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in
private lemma exists_X_pow_smul_eq_zero_of_vanish_above {g : ℤ → M} {N c : ℤ}
    (hN : ∀ j > N, g j = 0) (hrec : ∀ m ≥ c, g (m + 1) = (X i : MvPolynomial ι R) • g m) :
    ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • g c = 0 := by
  have key : ∀ k : ℕ, g (c + k) = (X i : MvPolynomial ι R) ^ k • g c := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ, ← add_assoc, hrec _ (by omega), ih, ← mul_smul, ← pow_succ']
  exact ⟨(N - c + 1).toNat, by rw [← key, hN _ (by omega)]⟩


open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in
theorem _root_.GlobalTheory.exists_X_pow_smul_eq_zero_of_eq_X_sub_one_smul {n : ℤ} {z w : M} (hz : z ∈ ℳ n)
    (h : z = (X i - 1 : MvPolynomial ι R) • w) :
    ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z = 0 := by
  have hcomp : ∀ m, (decompose ℳ z (m + 1) : M) =
      (X i : MvPolynomial ι R) • (decompose ℳ w m : M) - (decompose ℳ w (m + 1) : M) := by
    intro m; rw [h]; exact decompose_X_sub_one_smul_add_one ℳ i w m
  have hne : ∀ m, m + 1 ≠ n →
      (decompose ℳ w (m + 1) : M) = (X i : MvPolynomial ι R) • (decompose ℳ w m : M) := by
    intro m hm
    have := hcomp m
    rw [decompose_of_mem_ne ℳ hz (Ne.symm hm)] at this
    exact (sub_eq_zero.1 this.symm).symm
  obtain ⟨N₁, hN₁⟩ := exists_decompose_eq_zero_of_lt ℳ w
  obtain ⟨N₂, hN₂⟩ := exists_decompose_eq_zero_of_gt ℳ w
  have h1 : (decompose ℳ w (n - 1) : M) = 0 :=
    eq_zero_of_X_smul_recurrence_of_vanish_below i (g := fun m => (decompose ℳ w m : M)) hN₁
      (fun m hm => hne m (by omega))
  have hzn : z = -(decompose ℳ w n : M) := by
    have := hcomp (n - 1)
    rw [sub_add_cancel, decompose_of_mem_same ℳ hz, h1, smul_zero, zero_sub] at this
    exact this
  obtain ⟨k, hk⟩ := exists_X_pow_smul_eq_zero_of_vanish_above i
    (g := fun m => (decompose ℳ w m : M)) (c := n) hN₂ (fun m hm => hne m (by omega))
  exact ⟨k, by rw [hzn, smul_neg, hk, neg_zero]⟩

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in
private lemma X_pow_smul_mem_add_of_mem {j : ℤ} {v : M} (hv : v ∈ ℳ j) (k : ℕ) :
    (X i : MvPolynomial ι R) ^ k • v ∈ ℳ (j + k) := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    have := _root_.GlobalTheory.X_smul_mem_gr ℳ i (j + k) _ ih
    rw [pow_succ', mul_smul]
    convert this using 2
    push_cast; ring

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in
private lemma exists_mem_add_X_sub_one_smul_of_mem_of_le {j n : ℤ} {v : M} (hv : v ∈ ℳ j) (hn : j ≤ n) :
    ∃ y' ∈ ℳ n, ∃ w : M, v = y' + (X i - 1 : MvPolynomial ι R) • w := by
  have hmem := X_pow_smul_mem_add_of_mem ℳ i hv (n - j).toNat
  have e : j + ((n - j).toNat : ℤ) = n := by omega
  rw [e] at hmem
  refine ⟨_, hmem, -(∑ l ∈ Finset.range (n - j).toNat, (X i : MvPolynomial ι R) ^ l) • v, ?_⟩
  rw [neg_smul, smul_neg, smul_smul, mul_geom_sum, sub_smul, one_smul]
  abel


open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in
theorem _root_.GlobalTheory.exists_homogeneous_add_X_sub_one_smul (y : M) :
    ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∃ y' ∈ ℳ n, ∃ w : M, y = y' + (X i - 1 : MvPolynomial ι R) • w := by
  classical
  have hsum : ∀ S : Finset ℤ, ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∃ y' ∈ ℳ n, ∃ w : M,
      ∑ j ∈ S, (decompose ℳ y j : M) = y' + (X i - 1 : MvPolynomial ι R) • w := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨0, fun n _ => ⟨0, zero_mem _, 0, by simp⟩⟩
    | insert a S ha ih =>
      obtain ⟨n₁, hn₁⟩ := ih
      refine ⟨max a n₁, fun n hn => ?_⟩
      obtain ⟨y₁, hy₁, w₁, e₁⟩ :=
        exists_mem_add_X_sub_one_smul_of_mem_of_le ℳ i (decompose ℳ y a).2 (le_of_max_le_left hn)
      obtain ⟨y₂, hy₂, w₂, e₂⟩ := hn₁ n (le_of_max_le_right hn)
      refine ⟨y₁ + y₂, add_mem hy₁ hy₂, w₁ + w₂, ?_⟩
      rw [Finset.sum_insert ha, e₁, e₂, smul_add]
      abel
  obtain ⟨n₀, hn₀⟩ := hsum (decompose ℳ y).support
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨y', hy', w, e⟩ := hn₀ n hn
  exact ⟨y', hy', w, by rw [← e, sum_support_decompose]⟩

end

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in
include ℳ in
private lemma eq_zero_of_X_sub_one_smul_eq_zero {y : M}
    (hy : (X i - 1 : MvPolynomial ι R) • y = 0) : y = 0 := by
  classical
  have hrec : ∀ m, (decompose ℳ y (m + 1) : M) = (X i : MvPolynomial ι R) • (decompose ℳ y m : M) := by
    intro m
    have := decompose_X_sub_one_smul_add_one ℳ i y m
    rw [hy, decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero] at this
    exact (sub_eq_zero.1 this.symm).symm
  obtain ⟨N, hN⟩ := exists_decompose_eq_zero_of_lt ℳ y
  have hall : ∀ c, (decompose ℳ y c : M) = 0 := fun c =>
    eq_zero_of_X_smul_recurrence_of_vanish_below i (g := fun m => (decompose ℳ y m : M)) hN (fun m _ => hrec m)
  rw [← sum_support_decompose ℳ y]
  exact Finset.sum_eq_zero (fun j _ => hall j)


open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
theorem _root_.GlobalTheory.X_sub_one_smul_graded : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι), (∀ y : M, (X i - 1 : MvPolynomial ι R) • y = 0 → y = 0) ∧ (∀ (n : ℤ) (z w : M), z ∈ ℳ n → z = (X i - 1 : MvPolynomial ι R) • w → ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z = 0) ∧ (∀ y : M, ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∃ y' ∈ ℳ n, ∃ w : M, y = y' + (X i - 1 : MvPolynomial ι R) • w) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ i
  exact ⟨fun y hy => eq_zero_of_X_sub_one_smul_eq_zero ℳ i hy,
    fun n z w hz h => _root_.GlobalTheory.exists_X_pow_smul_eq_zero_of_eq_X_sub_one_smul ℳ i hz h,
    fun y => _root_.GlobalTheory.exists_homogeneous_add_X_sub_one_smul ℳ i y⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteCechHomologyOfFiniteCubeHomology
section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem finite_cycles_of_finite_homology {R : Type} [Ring R] {α : Type} {c : ComplexShape α}
    (K : HomologicalComplex (ModuleCat.{0} R) c) (i j : α) (hij : c.prev j = i)
    [Module.Finite R (K.X i)] [Module.Finite R (K.homology j)] :
    Module.Finite R (K.cycles j) := by
  have hex : (ShortComplex.mk (K.toCycles i j) (K.homologyπ j)
      (K.toCycles_comp_homologyπ i j)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel i j hij)
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hex
  exact Module.Finite.of_exact hex
    ((ModuleCat.epi_iff_surjective (K.homologyπ j)).1 inferInstance)

theorem finite_cechHomology_of_finite_cubeHomology (ι : Type) [LinearOrder ι] (R : Type)
    [CommRing R] [IsNoetherianRing R] (A : Cube.{0} ι R) (h₀ : Module.Finite R (A.obj ∅))
    (h : ∀ p, Module.Finite R ((cubeComplex A).homology p)) (p : ℕ) :
    Module.Finite R ((cechComplex A).homology p) := by
  cases p with
  | zero =>
    have h1 := h 1
    have h2 : Module.Finite R ((cubeComplex A).X 0) :=
      Module.Finite.equiv (Cube.termZeroEquiv A).symm
    have h3 := finite_cycles_of_finite_homology (cubeComplex A) 0 1 (by simp)
    exact Module.Finite.equiv
      (cubeCyclesIso A 1 ≪≫ (cechHomologyZeroIso A).symm).toLinearEquiv
  | succ p =>
    have h1 := h (p + 2)
    exact Module.Finite.equiv (cechHomologySuccIso A p).symm.toLinearEquiv

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FinitePieceOfPolyGradedSMul
section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem finite_piece_of_polyGradedSMul : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
    [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M → ∀ n, Module.Finite R (ℳ n) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ _ n
  refine GradedHilbert.finite_piece (ι := ι) ℳ (fun i k m hm => ?_) n
  have := grSMul_mem ℳ (X_mem_polyGrading i) hm
  first
    | exact this
    | exact add_comm k 1 ▸ this
    | simpa [add_comm] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FlatHomLocOfFlatHomLocSingleton
section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

private theorem flat_loc_over_algebra {A S M N : Type} [CommRing A] [CommRing S] [Algebra A S]
    [AddCommGroup M] [Module A M] [Module S M] [IsScalarTower A S M] [AddCommGroup N] [Module A N]
    [Module S N] [IsScalarTower A S N] (T : Submonoid S) (f : M →ₗ[S] N) [IsLocalizedModule T f]
    (h : Module.Flat A M) : Module.Flat A N := by
  rw [Module.Flat.iff_lTensor_injectiveₛ] at h ⊢
  intro P _ _ Q
  have := IsLocalizedModule.map_injective T (AlgebraTensorModule.rTensor A Q f)
    (AlgebraTensorModule.rTensor A P f) (AlgebraTensorModule.lTensor S M Q.subtype) (h Q)
  rw [IsLocalizedModule.map_lTensor] at this
  exact this

private theorem flat_iff_forall_piece {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (ℳ : ℤ → Submodule R M) [Decomposition ℳ] :
    Module.Flat R M ↔ ∀ n, Module.Flat R (ℳ n) :=
  (Module.Flat.equiv_iff (decomposeLinearEquiv ℳ)).trans Module.Flat.directSum_iff

theorem flat_homLoc_of_flat_homLoc_singleton :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M]
      [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
      (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) (s : Finset ι)
      (n : ℤ), i ∈ s → Module.Flat R (homLoc ℳ {i} 0) → Module.Flat R (homLoc ℳ s n) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ i s n hi h0
  have step (t : ℤ) : Module.Flat R (homLoc ℳ {i} t) ↔ Module.Flat R (homLoc ℳ {i} (t + 1)) :=
    Module.Flat.equiv_iff (LinearEquiv.ofBijective _
      (homLocSMul_X_bijective ℳ (Finset.mem_singleton_self i) t))
  have hall (t : ℤ) : Module.Flat R (homLoc ℳ {i} t) := by
    induction t using Int.induction_on with
    | zero => exact h0
    | succ k ih => exact (step _).1 ih
    | pred k ih => exact (step _).2 (by rwa [sub_add_cancel])
  have h1 := (flat_iff_forall_piece (homLoc ℳ {i})).2 hall
  have hsub : ({i} : Finset ι) ⊆ s := Finset.singleton_subset_iff.2 hi
  have hc : xProd R s = xProd R (s \ {i}) * xProd R {i} := (Finset.prod_sdiff hsub).symm
  have h2 : IsLocalizedModule.Away (xProd R (s \ {i}) * xProd R {i})
      (locRes X M hsub ∘ₗ LocalizedModule.mkLinearMap (.powers (xProd R {i})) M) := by
    rw [locRes_comp_mkLinearMap, ← hc]
    exact localizedModuleIsLocalizedModule _
  have h3 : IsLocalizedModule.Away (xProd R (s \ {i})) (locRes X M hsub) :=
    isLocalizedModule_away_of_comp (b := xProd R {i})
      (LocalizedModule.mkLinearMap (.powers (xProd R {i})) M) _
  have h4 := flat_loc_over_algebra (A := R) (.powers (xProd R (s \ {i}))) (locRes X M hsub) h1
  exact (flat_iff_forall_piece (homLoc ℳ s)).1 h4 n

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FlatQuotSMulTopCokerOfMatrixWitnesses
section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

open scoped Pointwise

namespace GlobalTheory

theorem flat_quotSMulTop_coker_of_matrix_witnesses :
    ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (r a b : ℕ) (g : Fin r → S) (u : S) (Φ : Matrix (Fin a) (Fin b) S), Module.Flat R (S ⧸ Ideal.span (Set.range g)) → (∃ c : Fin r → S, u = ∑ k, c k * g k) → (∀ k, ∃ (C : Matrix (Fin b) (Fin a) S) (C' : Matrix (Fin a) (Fin a) S), g k • (1 : Matrix (Fin a) (Fin a) S) = Φ * C + u • C') → (∃ (Ψ : Matrix (Fin b) (Fin a) S) (E : Fin r → Matrix (Fin a) (Fin b) S), Φ * Ψ * Φ = Φ + ∑ k, g k • E k) → Module.Flat R (QuotSMulTop u ((Fin a → S) ⧸ LinearMap.range Φ.mulVecLin)) := by
  intro R S _ _ _ r a b g u Φ hflat hu hker hreg
  obtain ⟨c, hc⟩ := hu
  obtain ⟨Ψ, E, hΨ⟩ := hreg
  let I : Ideal S := Ideal.span (Set.range g)
  have hgI : ∀ k, g k ∈ I := fun k => Ideal.subset_span ⟨k, rfl⟩
  have huI : u ∈ I := by
    rw [hc]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hgI k)
  have hmv : ∀ {m : ℕ} (A : Matrix (Fin a) (Fin m) S), (∀ j i, A j i ∈ I) →
      ∀ y j, (Matrix.mulVec A y) j ∈ I := by
    intro m A hA y j
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hA j i)
  let K := LinearMap.range Φ.mulVecLin
  let M := (Fin a → S) ⧸ K
  let T : Submodule S M := u • (⊤ : Submodule S M)
  let pr : (Fin a → S) →ₗ[S] QuotSMulTop u M := T.mkQ ∘ₗ K.mkQ
  have hK : ∀ y, pr (Matrix.mulVec Φ y) = 0 := by
    intro y
    simp only [pr, LinearMap.comp_apply, Submodule.mkQ_apply]
    have hy : K.mkQ (Matrix.mulVec Φ y) = 0 := (Submodule.Quotient.mk_eq_zero K).2 ⟨y, rfl⟩
    rw [hy, Submodule.Quotient.mk_zero]
  have hU : ∀ z, pr (u • z) = 0 := by
    intro z
    simp only [pr, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [map_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  have hG : ∀ k x, g k • pr x = 0 := by
    intro k x
    obtain ⟨C, C', h⟩ := hker k
    have hx : g k • x = Matrix.mulVec Φ (Matrix.mulVec C x) + u • Matrix.mulVec C' x := by
      have := congrArg (fun A => Matrix.mulVec A x) h
      simp only [Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.add_mulVec,
        ← Matrix.mulVec_mulVec] at this
      exact this
    rw [← map_smul, hx, map_add (f := _), hK, hU, add_zero]
  have hI : ∀ s ∈ I, ∀ x, s • pr x = 0 := by
    intro s hs x
    obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 hs
    simp only [Finset.sum_smul, smul_eq_mul, mul_smul, hG, smul_zero, Finset.sum_const_zero]
  let q : (Fin a → S) →ₗ[S] (Fin a → S ⧸ I) :=
    LinearMap.pi fun j => (Submodule.mkQ I) ∘ₗ LinearMap.proj j
  have hq : ∀ v, (∀ j, v j ∈ I) → q v = 0 := by
    intro v hv
    funext j
    exact (Submodule.Quotient.mk_eq_zero I).2 (hv j)
  have hqI : ∀ s ∈ I, ∀ w : Fin a → S ⧸ I, s • w = 0 := by
    intro s hs w
    funext j
    obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective I (w j)
    rw [Pi.smul_apply, ← ht, ← Submodule.Quotient.mk_smul, Pi.zero_apply,
      Submodule.Quotient.mk_eq_zero, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hs
  have hE : ∀ j i, (∑ k, g k • E k) j i ∈ I := by
    intro j i
    rw [Matrix.sum_apply]
    exact Ideal.sum_mem _ fun k _ => by
      rw [Matrix.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (hgI k)
  let f0 : (Fin a → S) →ₗ[S] (Fin a → S ⧸ I) := q ∘ₗ (LinearMap.id - (Φ * Ψ).mulVecLin)
  have h1 : K ≤ LinearMap.ker f0 := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    simp only [f0, LinearMap.comp_apply]
    apply hq
    intro j
    have hy : Φ.mulVecLin y - (Φ * Ψ).mulVecLin (Φ.mulVecLin y) = -(Matrix.mulVec (∑ k, g k • E k) y) := by
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hΨ, Matrix.add_mulVec]
      abel
    rw [LinearMap.sub_apply, LinearMap.id_apply, hy, Pi.neg_apply]
    exact Submodule.neg_mem _ (hmv _ hE y j)
  let f1 : M →ₗ[S] (Fin a → S ⧸ I) := K.liftQ f0 h1
  have h2 : T ≤ LinearMap.ker f1 := by
    intro m hm
    obtain ⟨m', -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hm
    rw [LinearMap.mem_ker, map_smul]
    exact hqI u huI _
  let i : QuotSMulTop u M →ₗ[S] (Fin a → S ⧸ I) := T.liftQ f1 h2
  let p : (Fin a → S ⧸ I) →ₗ[S] QuotSMulTop u M :=
    ∑ j, (Submodule.liftQ I (LinearMap.toSpanSingleton S _ (pr (Pi.single j 1)))
      (fun s hs => by
        rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
        exact hI s hs _)) ∘ₗ LinearMap.proj j
  have hpq : ∀ v, p (q v) = pr v := by
    intro v
    simp only [p, q, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, LinearMap.pi_apply, Submodule.mkQ_apply, Submodule.liftQ_apply,
      LinearMap.toSpanSingleton_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← Finset.univ_sum_single v, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← map_smul]
    refine congrArg pr ?_
    funext k
    by_cases h : k = j <;> simp [h]
  have hpi : p ∘ₗ i = LinearMap.id := by
    refine LinearMap.ext fun n => ?_
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective T n
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective K m
    show p (q (x - (Φ * Ψ).mulVecLin x)) = pr x
    rw [hpq, map_sub, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, hK, sub_zero]
  have := hflat
  have : Module.Flat R (Fin a → S ⧸ I) :=
    Module.Flat.of_linearEquiv
      (DFinsupp.linearEquivFunOnFintype (R := R) (M := fun _ : Fin a => S ⧸ I)).symm
  exact Module.Flat.of_retract (i.restrictScalars R) (p.restrictScalars R)
    (LinearMap.ext fun n => LinearMap.congr_fun hpi n)

end GlobalTheory
end

