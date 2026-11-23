module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0099
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0102

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdClassGroupMk0EqOfLinearEquivPiStatement
section
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_classGroup_mk0_eq_of_linearEquiv_pi : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (ι : Type) [Fintype ι] (I J : ι → (Ideal R)⁰), Nonempty (((i : ι) → (I i : Ideal R)) ≃ₗ[R] ((i : ι) → (J i : Ideal R))) → ∏ i, ClassGroup.mk0 (I i) = ∏ i, ClassGroup.mk0 (J i) := by
  first | exact @GlobalTheory.prod_classGroup_mk0_eq_of_pi_linearEquiv | exact GlobalTheory.prod_classGroup_mk0_eq_of_pi_linearEquiv | (intros; apply GlobalTheory.prod_classGroup_mk0_eq_of_pi_linearEquiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdFourMapsEqOneStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_four_maps_lam_pow_eq_one : ∀ (U : Type) [CommGroup U] {r : ℕ} (W A : Matrix (Fin r) (Fin r) ℤ) (lam : Fin r → Fin r → U), (∀ k l, lam k l = lam l k) → W = (W + W.transpose) * A → ∏ a : Fin 4, ∏ i, ∏ j, (∏ k, ∏ l, lam k l ^ ((![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a i k * (![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a j l)) ^ ((![1, -2, -1, 2] : Fin 4 → ℤ) a * W i j) = 1 := by
  first | exact @GlobalTheory.SymmProd.prod_four_maps_eq_one | exact GlobalTheory.SymmProd.prod_four_maps_eq_one | (intros; apply GlobalTheory.SymmProd.prod_four_maps_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBaseChangeOfPresentationMatrixSplitStatement
section
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_baseChange_of_presentation_matrix_split : ∀ (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module R M] (n m : ℕ) (π : (Fin n → R) →ₗ[R] M), Function.Surjective π →
    ∀ (r : Fin m → Fin n → R), Submodule.span R (Set.range r) = LinearMap.ker π →
    ∀ (v : Fin n → Fin n → B) (w : Fin n → Fin m → B),
    (∀ b l, ∑ a, algebraMap R B (r b a) * v a l = 0) →
    (∀ a l, v a l = (if a = l then 1 else 0) + ∑ b, w a b * algebraMap R B (r b l)) →
    Module.Projective B (B ⊗[R] M) := by
  first | (exact @GlobalTheory.projective_baseChange_of_presentation_split) | (exact GlobalTheory.projective_baseChange_of_presentation_split) | (intros; apply GlobalTheory.projective_baseChange_of_presentation_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSquareSectionsGlueOfBasis
section
open CategoryTheory AlgebraicGeometry TopologicalSpace

set_option autoImplicit false

namespace GlobalTheory.PinchLift

theorem app_res {X Y : Scheme.{0}} (f : Y ⟶ X) {W W' : X.Opens} (h : W' ≤ W) (s : Γ(X, W)) :
    (f.app W').hom ((X.presheaf.map (homOfLE h).op).hom s) =
      (Y.presheaf.map ((Opens.map f.base).map (homOfLE h)).op).hom ((f.app W).hom s) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.naturality]
  rfl

theorem compat_res {X X' Z Z' : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z)
    {W W' : X.Opens} (h : W' ≤ W) (a : Γ(X', p ⁻¹ᵁ W)) (b : Γ(Z, i ⁻¹ᵁ W))
    (hab : (i'.appLE (p ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_left).hom a =
      (p'.appLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_right).hom b) :
    (i'.appLE (p ⁻¹ᵁ W') (i' ⁻¹ᵁ (p ⁻¹ᵁ W') ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W')) inf_le_left).hom
        ((X'.presheaf.map ((Opens.map p.base).map (homOfLE h)).op).hom a) =
      (p'.appLE (i ⁻¹ᵁ W') (i' ⁻¹ᵁ (p ⁻¹ᵁ W') ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W')) inf_le_right).hom
        ((Z.presheaf.map ((Opens.map i.base).map (homOfLE h)).op).hom b) := by
  have hV : i' ⁻¹ᵁ (p ⁻¹ᵁ W') ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W') ≤ i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W) :=
    fun x hx => ⟨h hx.1, h hx.2⟩
  have := congrArg (Z'.presheaf.map (homOfLE hV).op).hom hab
  simp only [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE] at this ⊢
  exact this

theorem unique_of_basis {X X' Z Z' : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z)
    (B : Set X.Opens) (hbasis : ∀ (W : X.Opens) (x : X), x ∈ W → ∃ W' ∈ B, x ∈ W' ∧ W' ≤ W)
    (hB : ∀ W ∈ B, ∀ (a : Γ(X', p ⁻¹ᵁ W)) (b : Γ(Z, i ⁻¹ᵁ W)),
      (i'.appLE (p ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_left).hom a =
        (p'.appLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_right).hom b →
      ∃! s : Γ(X, W), (p.app W).hom s = a ∧ (i.app W).hom s = b)
    (W : X.Opens) (a : Γ(X', p ⁻¹ᵁ W)) (b : Γ(Z, i ⁻¹ᵁ W))
    (hab : (i'.appLE (p ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_left).hom a =
      (p'.appLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_right).hom b)
    (s s' : Γ(X, W)) (hs : (p.app W).hom s = a ∧ (i.app W).hom s = b)
    (hs' : (p.app W).hom s' = a ∧ (i.app W).hom s' = b) : s = s' := by
  have hcover : W ≤ ⨆ j : {W' : X.Opens // W' ∈ B ∧ W' ≤ W}, j.1 := by
    intro x hx
    obtain ⟨W', hW'B, hxW', hle⟩ := hbasis W x hx
    exact Opens.mem_iSup.2 ⟨⟨W', hW'B, hle⟩, hxW'⟩
  refine X.sheaf.eq_of_locally_eq' (fun j : {W' : X.Opens // W' ∈ B ∧ W' ≤ W} => j.1) W
    (fun j => homOfLE j.2.2) hcover s s' fun j => ?_
  have hc := compat_res p i i' p' j.2.2 a b hab
  refine (hB j.1 j.2.1 _ _ hc).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · exact (app_res p j.2.2 s).trans (congrArg _ hs.1)
  · exact (app_res i j.2.2 s).trans (congrArg _ hs.2)
  · exact (app_res p j.2.2 s').trans (congrArg _ hs'.1)
  · exact (app_res i j.2.2 s').trans (congrArg _ hs'.2)

theorem glues_of_basis : ∀ {X X' Z Z' : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z)
    (B : Set X.Opens), (∀ (W : X.Opens) (x : X), x ∈ W → ∃ W' ∈ B, x ∈ W' ∧ W' ≤ W) →
    (∀ W ∈ B, ∀ (a : Γ(X', p ⁻¹ᵁ W)) (b : Γ(Z, i ⁻¹ᵁ W)),
      (i'.appLE (p ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_left).hom a =
        (p'.appLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_right).hom b →
      ∃! s : Γ(X, W), (p.app W).hom s = a ∧ (i.app W).hom s = b) → GlobalTheory.PinchLift.Glues p i i' p' := by
  intro X X' Z Z' p i i' p' B hbasis hB W a b hab
  let I := {W' : X.Opens // W' ∈ B ∧ W' ≤ W}
  have hcover : W ≤ ⨆ j : I, j.1 := by
    intro x hx
    obtain ⟨W', hW'B, hxW', hle⟩ := hbasis W x hx
    exact Opens.mem_iSup.2 ⟨⟨W', hW'B, hle⟩, hxW'⟩
  choose t ht using fun j : I => (hB j.1 j.2.1 _ _ (compat_res p i i' p' j.2.2 a b hab)).exists
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun j : I => j.1) t := by
    intro j k
    have hjk : j.1 ⊓ k.1 ≤ W := inf_le_left.trans j.2.2
    refine unique_of_basis p i i' p' B hbasis hB (j.1 ⊓ k.1) _ _ (compat_res p i i' p' hjk a b hab) _ _
      ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · refine (app_res p inf_le_left (t j)).trans ?_
      rw [(ht j).1, ← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
    · refine (app_res i inf_le_left (t j)).trans ?_
      rw [(ht j).2, ← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
    · refine (app_res p inf_le_right (t k)).trans ?_
      rw [(ht k).1, ← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
    · refine (app_res i inf_le_right (t k)).trans ?_
      rw [(ht k).2, ← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun j : I => j.1) W (fun j => homOfLE j.2.2)
    hcover t hcompat
  have key : (p.app W).hom s = a ∧ (i.app W).hom s = b := by
    constructor
    · have hcov' : p ⁻¹ᵁ W ≤ ⨆ j : I, p ⁻¹ᵁ j.1 := by
        intro x hx
        obtain ⟨W', hW'B, hxW', hle⟩ := hbasis W (p.base x) hx
        exact Opens.mem_iSup.2 ⟨⟨W', hW'B, hle⟩, hxW'⟩
      refine X'.sheaf.eq_of_locally_eq' (fun j : I => p ⁻¹ᵁ j.1) (p ⁻¹ᵁ W)
        (fun j => (Opens.map p.base).map (homOfLE j.2.2)) hcov' _ _ fun j => ?_
      refine (app_res p j.2.2 s).symm.trans ?_
      rw [show (X.presheaf.map (homOfLE j.2.2).op).hom s = t j from hs j]
      exact (ht j).1
    · have hcov' : i ⁻¹ᵁ W ≤ ⨆ j : I, i ⁻¹ᵁ j.1 := by
        intro x hx
        obtain ⟨W', hW'B, hxW', hle⟩ := hbasis W (i.base x) hx
        exact Opens.mem_iSup.2 ⟨⟨W', hW'B, hle⟩, hxW'⟩
      refine Z.sheaf.eq_of_locally_eq' (fun j : I => i ⁻¹ᵁ j.1) (i ⁻¹ᵁ W)
        (fun j => (Opens.map i.base).map (homOfLE j.2.2)) hcov' _ _ fun j => ?_
      refine (app_res i j.2.2 s).symm.trans ?_
      rw [show (X.presheaf.map (homOfLE j.2.2).op).hom s = t j from hs j]
      exact (ht j).2
  exact ⟨s, key, fun s' hs' => unique_of_basis p i i' p' B hbasis hB W a b hab s' s hs' key⟩

end GlobalTheory.PinchLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionCoeffsInSubringRingClosed
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam.QAllSubring

variable {R : Subring ℂ} {N : ℕ}

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.const {c : ℂ} (hc : c ∈ R) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun _ => c := by
  refine ⟨fun n => if n = 0 then c else 0, ?_, fun n => ?_⟩
  · rw [_root_.GlobalTheory.QFam.hasQ_iff]
    intro τ
    have h := hasSum_single (f := fun n : ℕ =>
      (if n = 0 then c else 0) * Complex.exp (2 * ↑Real.pi * Complex.I * ↑τ / ↑N) ^ n) 0
      (fun m hm => by simp [hm])
    simpa using h
  · show (if n = 0 then c else 0) ∈ R
    split_ifs
    · exact hc
    · exact R.zero_mem

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.add {f g : ℍ → ℂ} (hf : _root_.GlobalTheory.QFam.QAll (· ∈ R) N f)
    (hg : _root_.GlobalTheory.QFam.QAll (· ∈ R) N g) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ + g τ := by
  obtain ⟨a, ha, haR⟩ := hf
  obtain ⟨b, hb, hbR⟩ := hg
  refine ⟨fun n => a n + b n, ?_, fun n => R.add_mem (haR n) (hbR n)⟩
  rw [_root_.GlobalTheory.QFam.hasQ_iff] at ha hb ⊢
  intro τ
  simpa [add_mul] using (ha τ).add (hb τ)

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.sub {f g : ℍ → ℂ} (hf : _root_.GlobalTheory.QFam.QAll (· ∈ R) N f)
    (hg : _root_.GlobalTheory.QFam.QAll (· ∈ R) N g) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ - g τ := by
  obtain ⟨a, ha, haR⟩ := hf
  obtain ⟨b, hb, hbR⟩ := hg
  refine ⟨fun n => a n - b n, ?_, fun n => R.sub_mem (haR n) (hbR n)⟩
  rw [_root_.GlobalTheory.QFam.hasQ_iff] at ha hb ⊢
  intro τ
  simpa [sub_mul] using (ha τ).sub (hb τ)

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.mul {f g : ℍ → ℂ} (hf : _root_.GlobalTheory.QFam.QAll (· ∈ R) N f)
    (hg : _root_.GlobalTheory.QFam.QAll (· ∈ R) N g) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ * g τ := by
  obtain ⟨a, ha, haR⟩ := hf
  obtain ⟨b, hb, hbR⟩ := hg
  refine ⟨fun n => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, a kl.1 * b kl.2, ?_,
    fun n => R.sum_mem fun kl _ => R.mul_mem (haR kl.1) (hbR kl.2)⟩
  rw [_root_.GlobalTheory.QFam.hasQ_iff] at ha hb ⊢
  intro τ
  set q := Complex.exp (2 * ↑Real.pi * Complex.I * ↑τ / ↑N)
  have hsa : Summable fun n => ‖a n * q ^ n‖ := summable_norm_iff.mpr (ha τ).summable
  have hsb : Summable fun n => ‖b n * q ^ n‖ := summable_norm_iff.mpr (hb τ).summable
  have hterm : ∀ n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      a kl.1 * q ^ kl.1 * (b kl.2 * q ^ kl.2) =
      (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, a kl.1 * b kl.2) * q ^ n := by
    intro n
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hkl, pow_add]
    ring
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm hsa hsb
  have heq := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hsa hsb
  rw [(ha τ).tsum_eq, (hb τ).tsum_eq] at heq
  rw [heq]
  simp only [hterm] at hs ⊢
  exact (summable_norm_iff.mp hs).hasSum

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.pow {f : ℍ → ℂ} (k : ℕ)
    (hf : _root_.GlobalTheory.QFam.QAll (· ∈ R) N f) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ ^ k := by
  induction k with
  | zero => simpa using _root_.GlobalTheory.QFam.QAllSubring.const (N := N) R.one_mem
  | succ k ih => simpa [pow_succ] using _root_.GlobalTheory.QFam.QAllSubring.mul ih hf

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.sum {κ : Type} (s : Finset κ) {f : κ → ℍ → ℂ}
    (hf : ∀ k ∈ s, _root_.GlobalTheory.QFam.QAll (· ∈ R) N (f k)) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => ∑ k ∈ s, f k τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using _root_.GlobalTheory.QFam.QAllSubring.const (N := N) R.zero_mem
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact _root_.GlobalTheory.QFam.QAllSubring.add (hf i (Finset.mem_insert_self i s))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.prod {κ : Type} (s : Finset κ) {f : κ → ℍ → ℂ}
    (hf : ∀ k ∈ s, _root_.GlobalTheory.QFam.QAll (· ∈ R) N (f k)) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => ∏ k ∈ s, f k τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using _root_.GlobalTheory.QFam.QAllSubring.const (N := N) R.one_mem
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact _root_.GlobalTheory.QFam.QAllSubring.mul (hf i (Finset.mem_insert_self i s))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.ring_closed : ∀ (R : Subring ℂ) (N : ℕ), 0 < N →
    (∀ c ∈ R, _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun _ => c) ∧
    (∀ f g, _root_.GlobalTheory.QFam.QAll (· ∈ R) N f → _root_.GlobalTheory.QFam.QAll (· ∈ R) N g →
      _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ + g τ) ∧
    (∀ f g, _root_.GlobalTheory.QFam.QAll (· ∈ R) N f → _root_.GlobalTheory.QFam.QAll (· ∈ R) N g →
      _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ - g τ) ∧
    (∀ f g, _root_.GlobalTheory.QFam.QAll (· ∈ R) N f → _root_.GlobalTheory.QFam.QAll (· ∈ R) N g →
      _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ * g τ) ∧
    (∀ f (k : ℕ), _root_.GlobalTheory.QFam.QAll (· ∈ R) N f →
      _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ ^ k) ∧
    (∀ (κ : Type) (s : Finset κ) (f : κ → ℍ → ℂ),
      (∀ k ∈ s, _root_.GlobalTheory.QFam.QAll (· ∈ R) N (f k)) →
      (_root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => ∑ k ∈ s, f k τ) ∧
        _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => ∏ k ∈ s, f k τ) := by
  intro R N _
  exact ⟨fun c hc => _root_.GlobalTheory.QFam.QAllSubring.const hc,
    fun f g hf hg => _root_.GlobalTheory.QFam.QAllSubring.add hf hg,
    fun f g hf hg => _root_.GlobalTheory.QFam.QAllSubring.sub hf hg,
    fun f g hf hg => _root_.GlobalTheory.QFam.QAllSubring.mul hf hg,
    fun f k hf => _root_.GlobalTheory.QFam.QAllSubring.pow k hf,
    fun κ s f hf => ⟨_root_.GlobalTheory.QFam.QAllSubring.sum s hf,
      _root_.GlobalTheory.QFam.QAllSubring.prod s hf⟩⟩

end GlobalTheory.QFam.QAllSubring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RadicalEltMovingDualToMajorantStatement
section
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_fixing_mulVec_conj_eq_of_majorant : ∀ (n p : ℕ) (J θ : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J → θ * θ = 1 → (J * θ).PosDef →
    ∀ (X₂ Y₂ : Matrix (Fin n) (Fin p) ℂ), X₂.conjTranspose * J * X₂ = 0 → Y₂.conjTranspose * J * Y₂ = 0 →
      X₂.conjTranspose * J * Y₂ = 1 →
    ∃ u₁ : GL (Fin n) ℂ, (u₁.1).conjTranspose * J * u₁.1 = J ∧ u₁.1 * X₂ = X₂ ∧
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₂.conjTranspose * J) v = 0 → ∃ w : Fin p → ℂ, Matrix.mulVec u₁.1 v - v = Matrix.mulVec X₂ w) ∧
      θ * X₂ = u₁.1 * Y₂ * (X₂.conjTranspose * (J * θ) * X₂) := by
  first | exact @GlobalTheory.radical_elt_moving_dual_to_majorant | exact GlobalTheory.radical_elt_moving_dual_to_majorant | (intros; apply GlobalTheory.radical_elt_moving_dual_to_majorant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationIdxDvdOfGaloisDegreeDvdUnitDvrStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramificationIdx_dvd_of_galois_degree_dvd_unit_dvr : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Field K] [Algebra S K]
    [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [IsGalois K L] (q : ℕ), 0 < q → IsUnit (q : S) →
    Module.finrank K L ∣ q →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ q) ∧
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) := by
  first | (exact @GlobalTheory.RamGalDVR.ramGal) | (exact GlobalTheory.RamGalDVR.ramGal) | (intros; apply GlobalTheory.RamGalDVR.ramGal  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatFiniteAdelesSplitAwayFromPrimePadic
section
open IsDedekindDomain

noncomputable section

namespace GlobalTheory.AdeleSplitP

open GlobalTheory.LKTrip Rat.HeightOneSpectrum

local instance (q : Nat.Primes) : Fact q.1.Prime := ⟨q.2⟩

def placeP (p : ℕ) [hp : Fact p.Prime] : HeightOneSpectrum ℤ where
  asIdeal := Ideal.span {(p : ℤ)}
  isPrime := (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).2
    (Nat.prime_iff_prime_int.mp hp.out)
  ne_bot := by simpa using hp.out.ne_zero

theorem primesEquiv_placeP (p : ℕ) [hp : Fact p.Prime] :
    primesEquiv (placeP p) = (⟨p, hp.out⟩ : Nat.Primes) := by
  apply Subtype.ext
  change natGenerator (placeP p) = p
  have h1 := span_natGenerator (placeP p)
  have he : Rat.IsIntegralClosure.intEquiv ℤ = RingEquiv.refl ℤ :=
    RingEquiv.ext fun x ↦ by simpa using eq_intCast (Rat.IsIntegralClosure.intEquiv ℤ) x
  have h2 : (placeP p).asIdeal.map (Rat.IsIntegralClosure.intEquiv ℤ) = (placeP p).asIdeal := by
    rw [he]
    exact Ideal.map_id _
  rw [h2] at h1
  change Ideal.span {((natGenerator (placeP p) : ℕ) : ℤ)} = Ideal.span {(p : ℤ)} at h1
  rw [Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs] at h1
  simpa using h1

def compP (p : ℕ) [hp : Fact p.Prime] : FiniteAdeleRing ℤ ℚ →+* ℚ_[p] :=
  ((ContinuousAlgEquiv.cast (R := ℚ) (A := fun q : Nat.Primes ↦ ℚ_[q]) (primesEquiv_placeP p)).toRingEquiv.toRingHom.comp
    (adicCompletion.padicEquiv (placeP p)).toRingEquiv.toRingHom).comp
    (RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum ℤ ↦ v.adicCompletion ℚ) (placeP p))

theorem compP_apply (p : ℕ) [Fact p.Prime] (a : FiniteAdeleRing ℤ ℚ) :
    compP p a = ContinuousAlgEquiv.cast (R := ℚ) (A := fun q : Nat.Primes ↦ ℚ_[q]) (primesEquiv_placeP p)
      (adicCompletion.padicEquiv (placeP p) (a (placeP p))) := rfl

theorem continuous_compP (p : ℕ) [Fact p.Prime] : Continuous (compP p) :=
  show Continuous (fun a ↦ compP p a) from (ContinuousAlgEquiv.cast (R := ℚ) (A := fun q : Nat.Primes ↦ ℚ_[q]) (primesEquiv_placeP p)).continuous.comp
    ((adicCompletion.padicEquiv (placeP p)).continuous.comp (RestrictedProduct.continuous_eval _))

theorem restr_eval (p : ℕ) (a : FiniteAdeleRing ℤ ℚ) (w : AwayP p) :
    AfP.eval w (AfP.restr p a) = a w.1 := rfl

theorem finiteAdeleRingAway_ext {p : ℕ} {b c : AfP p} (h : ∀ w, AfP.eval w b = AfP.eval w c) : b = c :=
  Subtype.ext (funext fun w ↦ h w)

theorem eq_placeP {p : ℕ} [Fact p.Prime] {v : HeightOneSpectrum ℤ}
    (hv : v.asIdeal = Ideal.span {(p : ℤ)}) : v = placeP p :=
  HeightOneSpectrum.ext hv

theorem finiteAdele_split (p : ℕ) [Fact p.Prime] :
    ∃ π : FiniteAdeleRing ℤ ℚ →ₐ[ℚ] ℚ_[p], Continuous π ∧
      Function.Bijective (fun a ↦ (GlobalTheory.LKTrip.AfP.restr p a, π a)) := by
  refine ⟨(compP p).toRatAlgHom, continuous_compP p, ?_, ?_⟩
  · intro a b hab
    simp only [Prod.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    refine FiniteAdeleRing.ext _ fun v ↦ ?_
    by_cases hv : v.asIdeal = Ideal.span {(p : ℤ)}
    · obtain rfl := eq_placeP hv
      have h2' : compP p a = compP p b := h2
      rw [compP_apply, compP_apply] at h2'
      exact (adicCompletion.padicEquiv (placeP p)).injective
        ((ContinuousAlgEquiv.cast (R := ℚ) (A := fun q : Nat.Primes ↦ ℚ_[q]) (primesEquiv_placeP p)).injective h2')
    · exact congrArg (AfP.eval ⟨v, hv⟩) h1
  · rintro ⟨b, y⟩
    classical
    let x0 : (placeP p).adicCompletion ℚ := (adicCompletion.padicEquiv (placeP p)).symm
      ((ContinuousAlgEquiv.cast (R := ℚ) (A := fun q : Nat.Primes ↦ ℚ_[q]) (primesEquiv_placeP p)).symm y)
    let g0 : ∀ v : HeightOneSpectrum ℤ, v.adicCompletion ℚ := fun v ↦
      if h : v.asIdeal = Ideal.span {(p : ℤ)} then 0 else AfP.eval ⟨v, h⟩ b
    let g : ∀ v : HeightOneSpectrum ℤ, v.adicCompletion ℚ := Function.update g0 (placeP p) x0
    have hg : ∀ v (hv : v.asIdeal ≠ Ideal.span {(p : ℤ)}), g v = AfP.eval ⟨v, hv⟩ b := by
      intro v hv
      have hv0 : v ≠ placeP p := fun h ↦ hv (h ▸ rfl)
      simp only [g, g0, Function.update_of_ne hv0, dif_neg hv]
    have hS : {w : AwayP p | ¬ AfP.eval w b ∈ w.1.adicCompletionIntegers ℚ}.Finite :=
      Filter.eventually_cofinite.1 b.2
    have hfin : {v : HeightOneSpectrum ℤ | ¬ g v ∈ v.adicCompletionIntegers ℚ}.Finite := by
      refine ((hS.image Subtype.val).insert (placeP p)).subset fun v hv ↦ ?_
      by_cases hv0 : v = placeP p
      · exact Or.inl hv0
      · have hv' : v.asIdeal ≠ Ideal.span {(p : ℤ)} := fun h ↦ hv0 (eq_placeP h)
        refine Or.inr ⟨⟨v, hv'⟩, ?_, rfl⟩
        have hv2 : ¬ g v ∈ v.adicCompletionIntegers ℚ := hv
        rw [hg v hv'] at hv2
        exact hv2
    let A : FiniteAdeleRing ℤ ℚ := ⟨g, Filter.eventually_cofinite.2 hfin⟩
    refine ⟨A, Prod.ext ?_ ?_⟩
    · show AfP.restr p A = b
      refine finiteAdeleRingAway_ext fun w ↦ ?_
      rw [restr_eval]
      exact hg w.1 w.2
    · show compP p A = y
      change ContinuousAlgEquiv.cast (R := ℚ) (A := fun q : Nat.Primes ↦ ℚ_[q]) (primesEquiv_placeP p)
        (adicCompletion.padicEquiv (placeP p) (g (placeP p))) = y
      simp only [g, Function.update_self, x0, ContinuousAlgEquiv.apply_symm_apply]

end GlobalTheory.AdeleSplitP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatrixIdentityTransferToComplexMapStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_matrix_identity_transfer_to_complex_map : ∀ (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Tq : Matrix (Fin n) (Fin n) ℚ),
    Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ) →
    ∀ (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ),
    (1 : Matrix (Fin n) (Fin n) ℚ) = c₀ • Tq + ∑ i, c i • ((Polynomial.aeval Tq (p i)) ^ 2 * Tq) →
    (1 : Module.End ℂ (Fin g → ℂ)) = c₀ • γ + ∑ i, c i • ((Polynomial.aeval γ (p i)) ^ 2 * γ) := by
  first | exact @GlobalTheory.matrix_identity_transfer | exact GlobalTheory.matrix_identity_transfer | (intros; apply GlobalTheory.matrix_identity_transfer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedFibresAlmostAllOfSeparableDedekindCurveStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduced_fibres_almost_all_of_separable_dedekind_curve : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] (y : A), (Polynomial.aeval (R := k) y).Finite → Function.Injective (Polynomial.aeval (R := k) y) → Algebra.IsSeparable (IntermediateField.adjoin k {algebraMap A (FractionRing A) y}) (FractionRing A) → ∃ δ : k[X], δ ≠ 0 ∧ ∀ α : k, δ.eval α ≠ 0 → ∀ Q : Ideal A, Q.IsMaximal → y - algebraMap k A α ∉ Q ^ 2 := by
  first | (exact @GlobalTheory.reduced_fibres_almost_all_sep) | (exact GlobalTheory.reduced_fibres_almost_all_sep) | (intros; apply GlobalTheory.reduced_fibres_almost_all_sep  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularHeightOneLocalization
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_height_one_localization : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
    (QA : Ideal EA) [QA.IsPrime] (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
    (P.comap (algebraMap A (Localization.AtPrime QA))).height ≤ 1 →
    IsRegularLocalRing (Localization.AtPrime P) := by
  first | (exact @GlobalTheory.EtaleSpreadReg.isRegularLocalRing_atPrime) | (exact GlobalTheory.EtaleSpreadReg.isRegularLocalRing_atPrime) | (intros; apply GlobalTheory.EtaleSpreadReg.isRegularLocalRing_atPrime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepTraceEqMulTraceStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_ringHom_eq_mul_algebraTrace : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (s : ℕ), r = s * Module.finrank ℚ E → ∀ a : 𝓞 E, (ρ a).trace = s * Algebra.trace ℤ (𝓞 E) a := by
  first | exact @GlobalTheory.repTrace_eq_mul_trace | exact GlobalTheory.repTrace_eq_mul_trace | (intros; apply GlobalTheory.repTrace_eq_mul_trace <;> assumption)
end

