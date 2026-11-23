module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.QuasiReflectionEqMulTransvectionsOfHyperbolicPla
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.UTrans.PlaneRefl

variable {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R)

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
private lemma transvection_zero' {E : Type} [Field E] {n : ℕ} (σ : E →+* E)
    (G : Matrix (Fin n) (Fin n) E) (w : Fin n → E) : _root_.GlobalTheory.UTrans.tv σ G w 0 = 1 := by
  unfold _root_.GlobalTheory.UTrans.tv
  ext i j
  simp

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
private lemma quasiReflection_eq_transvectionGen_mul_shifted {E : Type} [Field E] [CharZero E] {n : ℕ} (σ : E →+* E)
    (G : Matrix (Fin n) (Fin n) E) (hinv : ∀ a, σ (σ a) = a) (hG : ∀ a b, σ (G a b) = G b a)
    (x z : Fin n → E) (a u : E) (hzz : _root_.GlobalTheory.UTrans.hf σ G z z = 0)
    (hxz : _root_.GlobalTheory.UTrans.hf σ G x z ≠ 0) (hxx : _root_.GlobalTheory.UTrans.hf σ G x x ≠ 0)
    (hyy : _root_.GlobalTheory.UTrans.hf σ G (x + a • z) (x + a • z) ≠ 0) (hu : u * σ u = 1)
    (hu1 : u ≠ 1)
    (hD : u * σ a * _root_.GlobalTheory.UTrans.hf σ G x z + a * σ (_root_.GlobalTheory.UTrans.hf σ G x z) ≠ 0) :
    ∃ m ∈ _root_.GlobalTheory.UTrans.TvGen σ G,
      _root_.GlobalTheory.UTrans.tv σ G x ((u - 1) / _root_.GlobalTheory.UTrans.hf σ G x x) =
        m * _root_.GlobalTheory.UTrans.tv σ G (x + a • z)
          ((u - 1) / _root_.GlobalTheory.UTrans.hf σ G (x + a • z) (x + a • z)) := by
  set β := _root_.GlobalTheory.UTrans.hf σ G x z with hβ
  set α := _root_.GlobalTheory.UTrans.hf σ G x x with hα
  have hzx : _root_.GlobalTheory.UTrans.hf σ G z x = σ β := by
    rw [hβ, _root_.GlobalTheory.UTrans.Model.hf_conj σ G hinv hG]
  have hαr : σ α = α := by rw [hα, _root_.GlobalTheory.UTrans.Model.hf_conj σ G hinv hG]
  have hα' : _root_.GlobalTheory.UTrans.hf σ G (x + a • z) (x + a • z) = α + σ a * β + a * σ β := by
    rw [_root_.GlobalTheory.UTrans.Model.hf_add_smul_left, _root_.GlobalTheory.UTrans.Model.hf_add_smul_right,
      _root_.GlobalTheory.UTrans.Model.hf_add_smul_right, hzz, hzx]
    ring
  rw [hα'] at hyy ⊢
  clear_value α β
  have hu0 : u ≠ 0 := left_ne_zero_of_mul_eq_one hu
  have hsu : σ u = u⁻¹ := eq_inv_of_mul_eq_one_right hu
  have hu1' : u - 1 ≠ 0 := sub_ne_zero.2 hu1
  have hsβ : σ β ≠ 0 := fun h => hxz (by rw [← hinv β, h, map_zero])
  obtain ⟨D, hDdef⟩ : ∃ D, D = u * σ a * β + a * σ β := ⟨_, rfl⟩
  rw [← hDdef] at hD
  obtain ⟨N, hN⟩ : ∃ N, N = β * σ β := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = -(σ a * β + a * σ β) * u * α / (D * (u - 1) * N) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = (u * α * (σ a * β + a * σ β) - (u - 1) ^ 2 * (σ a * β) * (a * σ β)) /
      (D * (u - 1) * N) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = -(D * α / ((α + σ a * β + a * σ β) * (u - 1) * N)) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = (u - 1) / α := ⟨_, rfl⟩
  have hσc : σ c = (u⁻¹ - 1) / α := by rw [hc, map_div₀, map_sub, map_one, hsu, hαr]
  have hyy2 : α + a * σ β + σ a * β ≠ 0 := by rw [add_assoc, add_comm (a * σ β), ← add_assoc]; exact hyy
  have hN0 : N ≠ 0 := by rw [hN]; exact mul_ne_zero hxz hsβ
  have hσD : σ D = D / u := by
    rw [hDdef]
    simp only [map_add (f := _), map_mul, hinv, hsu]
    field_simp
    ring
  have hσN : σ N = N := by rw [hN]; simp only [map_mul, hinv]; ring
  have trA : A + σ A = 0 := by
    rw [hA]
    simp only [map_div₀, map_mul, map_neg, map_sub, map_one, map_add (f := _), map_pow, hinv, hsu, hαr, hσD, hσN]
    field_simp
    ring
  have trB : B + σ B = 0 := by
    rw [hB]
    simp only [map_div₀, map_mul, map_neg, map_sub, map_one, map_add (f := _), map_pow, hinv, hsu, hαr, hσD, hσN]
    field_simp
    ring
  have trR : R + σ R = 0 := by
    rw [hR]
    simp only [map_div₀, map_mul, map_neg, map_sub, map_one, map_add (f := _), map_pow, hinv, hsu, hαr, hσD, hσN]
    field_simp
    ring
  obtain ⟨w, hw⟩ : ∃ w, w = z + (c * σ β) • x := ⟨_, rfl⟩
  have hww : _root_.GlobalTheory.UTrans.hf σ G w w = 0 := by
    rw [hw, _root_.GlobalTheory.UTrans.Model.hf_add_smul_left, _root_.GlobalTheory.UTrans.Model.hf_add_smul_right,
      _root_.GlobalTheory.UTrans.Model.hf_add_smul_right, hzz, hzx, map_mul, hσc, hinv, ← hβ, ← hα]
    rw [hc]
    field_simp
    ring
  refine ⟨_root_.GlobalTheory.UTrans.tv σ G z A * _root_.GlobalTheory.UTrans.tv σ G w R *
      _root_.GlobalTheory.UTrans.tv σ G z B, ?_, ?_⟩
  · unfold _root_.GlobalTheory.UTrans.TvGen
    refine mul_mem (mul_mem ?_ ?_) ?_
    · exact Submonoid.subset_closure ⟨z, A, hzz, trA, rfl⟩
    · exact Submonoid.subset_closure ⟨w, R, hww, trR, rfl⟩
    · exact Submonoid.subset_closure ⟨z, B, hzz, trB, rfl⟩
  rw [← hc]
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  simp only [Matrix.toLin'_apply]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [_root_.GlobalTheory.UTrans.Model.tv_mulVec]
  subst hw
  simp only [_root_.GlobalTheory.UTrans.Model.hf_add_smul_left, _root_.GlobalTheory.UTrans.Model.hf_add_smul_right]
  simp only [hzz, hzx, ← hβ, ← hα]
  simp only [map_mul, hσc, hinv]
  generalize _root_.GlobalTheory.UTrans.hf σ G v x = p at *
  generalize _root_.GlobalTheory.UTrans.hf σ G v z = q at *
  subst hA hB hR hc hDdef hN
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
private lemma transvection_isometry {E : Type} [Field E] {n : ℕ} (σ : E →+* E)
    (G : Matrix (Fin n) (Fin n) E) (hinv : ∀ a, σ (σ a) = a) (hG : ∀ a b, σ (G a b) = G b a)
    (w : Fin n → E) (t : E)
    (ht : t + σ t + t * σ t * _root_.GlobalTheory.UTrans.hf σ G w w = 0) (v v' : Fin n → E) :
    _root_.GlobalTheory.UTrans.hf σ G ((_root_.GlobalTheory.UTrans.tv σ G w t).mulVec v)
      ((_root_.GlobalTheory.UTrans.tv σ G w t).mulVec v') = _root_.GlobalTheory.UTrans.hf σ G v v' := by
  simp only [_root_.GlobalTheory.UTrans.Model.tv_mulVec, _root_.GlobalTheory.UTrans.Model.hf_add_smul_left,
    _root_.GlobalTheory.UTrans.Model.hf_add_smul_right, map_mul]
  rw [_root_.GlobalTheory.UTrans.Model.hf_conj σ G hinv hG v' w]
  linear_combination (_root_.GlobalTheory.UTrans.hf σ G v w * _root_.GlobalTheory.UTrans.hf σ G w v') * ht

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
private lemma isometry_mul_transvection {E : Type} [Field E] {n : ℕ} (σ : E →+* E)
    (G : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) E)
    (hg : ∀ v w, _root_.GlobalTheory.UTrans.hf σ G (g.mulVec v) (g.mulVec w) =
      _root_.GlobalTheory.UTrans.hf σ G v w) (w : Fin n → E) (t : E) :
    g * _root_.GlobalTheory.UTrans.tv σ G w t = _root_.GlobalTheory.UTrans.tv σ G (g.mulVec w) t * g := by
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, _root_.GlobalTheory.UTrans.Model.tv_mulVec, hg,
    Matrix.mulVec_add, Matrix.mulVec_smul]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
private lemma transvection_mul_isotropic {E : Type} [Field E] {n : ℕ} (σ : E →+* E)
    (G : Matrix (Fin n) (Fin n) E) (w : Fin n → E) (hw : _root_.GlobalTheory.UTrans.hf σ G w w = 0)
    (s t : E) : _root_.GlobalTheory.UTrans.tv σ G w s * _root_.GlobalTheory.UTrans.tv σ G w t =
      _root_.GlobalTheory.UTrans.tv σ G w (s + t) := by
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, _root_.GlobalTheory.UTrans.Model.tv_mulVec,
    _root_.GlobalTheory.UTrans.Model.hf_add_smul_left, hw]
  rw [add_assoc, ← add_smul]
  congr 2
  ring


open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) in
theorem _root_.GlobalTheory.UTrans.PlaneRefl.quasiRefl_eq_mul_of_plane : ∀ (E : Type) [Field E] [CharZero E]
    (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), _root_.GlobalTheory.UTrans.IsHerm σ G →
    ∀ (x z : Fin n → E) (a u : E), _root_.GlobalTheory.UTrans.hf σ G z z = 0 →
    _root_.GlobalTheory.UTrans.hf σ G x z ≠ 0 → _root_.GlobalTheory.UTrans.hf σ G x x ≠ 0 →
    _root_.GlobalTheory.UTrans.hf σ G (x + a • z) (x + a • z) ≠ 0 → u * σ u = 1 →
    ∃ m ∈ _root_.GlobalTheory.UTrans.TvGen σ G,
      _root_.GlobalTheory.UTrans.tv σ G x ((u - 1) / _root_.GlobalTheory.UTrans.hf σ G x x) =
        m * _root_.GlobalTheory.UTrans.tv σ G (x + a • z)
          ((u - 1) / _root_.GlobalTheory.UTrans.hf σ G (x + a • z) (x + a • z)) := by
  intro E _ _ n σ G hH x z a u hzz hxz hxx hyy hu
  obtain ⟨hinv, hne, hG, -⟩ := hH
  by_cases hu1 : u = 1
  · subst hu1
    refine ⟨1, one_mem _, ?_⟩
    simp only [sub_self, zero_div, transvection_zero', one_mul]
  by_cases hD : u * σ a * _root_.GlobalTheory.UTrans.hf σ G x z +
      a * σ (_root_.GlobalTheory.UTrans.hf σ G x z) ≠ 0
  · exact quasiReflection_eq_transvectionGen_mul_shifted σ G hinv hG x z a u hzz hxz hxx hyy hu hu1 hD
  push_neg at hD
  obtain ⟨e, he⟩ := hne
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = e - σ e := ⟨_, rfl⟩
  have hσω : σ ω = -ω := by rw [hωdef, map_sub, hinv]; ring
  have hω0 : ω ≠ 0 := by rw [hωdef]; exact sub_ne_zero.2 (Ne.symm he)
  set β := _root_.GlobalTheory.UTrans.hf σ G x z with hβ
  set y := x + a • z with hy
  set E₁ := _root_.GlobalTheory.UTrans.tv σ G z ω with hE₁
  set E₂ := _root_.GlobalTheory.UTrans.tv σ G z (-ω) with hE₂
  have hEiso : ∀ v w, _root_.GlobalTheory.UTrans.hf σ G (E₁.mulVec v) (E₁.mulVec w) =
      _root_.GlobalTheory.UTrans.hf σ G v w :=
    transvection_isometry σ G hinv hG z ω (by rw [hσω, hzz]; ring)
  have hy1 : E₁.mulVec y = x + (a + ω * β) • z := by
    rw [hE₁, _root_.GlobalTheory.UTrans.Model.tv_mulVec, hy, _root_.GlobalTheory.UTrans.Model.hf_add_smul_left, hzz,
      ← hβ, add_smul, add_assoc]
    congr 2
    ring_nf
  have hnorm : _root_.GlobalTheory.UTrans.hf σ G (x + (a + ω * β) • z) (x + (a + ω * β) • z) =
      _root_.GlobalTheory.UTrans.hf σ G y y := by rw [← hy1, hEiso]
  have hD1 : u * σ (a + ω * β) * β + (a + ω * β) * σ β ≠ 0 := by
    have e1 : u * σ (a + ω * β) * β + (a + ω * β) * σ β = ω * β * σ β * (1 - u) := by
      rw [map_add (f := _), map_mul, hσω]
      linear_combination hD
    rw [e1]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero hω0 hxz) ?_) (sub_ne_zero.2 (Ne.symm hu1))
    intro h; exact hxz (by rw [← hinv β, h, map_zero])
  obtain ⟨m₁, hm₁, h₁⟩ := quasiReflection_eq_transvectionGen_mul_shifted σ G hinv hG x z (a + ω * β) u hzz hxz hxx
    (by rw [hnorm]; exact hyy) hu hu1 hD1
  rw [hnorm] at h₁
  set c' := (u - 1) / _root_.GlobalTheory.UTrans.hf σ G y y with hc'
  have hyr : σ (_root_.GlobalTheory.UTrans.hf σ G y y) = _root_.GlobalTheory.UTrans.hf σ G y y :=
    _root_.GlobalTheory.UTrans.Model.hf_conj σ G hinv hG y y
  have hτiso : ∀ v w, _root_.GlobalTheory.UTrans.hf σ G
      ((_root_.GlobalTheory.UTrans.tv σ G y c').mulVec v) ((_root_.GlobalTheory.UTrans.tv σ G y c').mulVec w) =
      _root_.GlobalTheory.UTrans.hf σ G v w := by
    refine transvection_isometry σ G hinv hG y c' ?_
    rw [hc', map_div₀, map_sub, map_one, hyr]
    field_simp
    linear_combination hu
  have hc1 : E₁ * _root_.GlobalTheory.UTrans.tv σ G y c' = _root_.GlobalTheory.UTrans.tv σ G (x + (a + ω * β) • z) c' * E₁ := by
    rw [isometry_mul_transvection σ G E₁ hEiso, hy1]
  have hEE : E₁ * E₂ = 1 := by
    rw [hE₁, hE₂, transvection_mul_isotropic σ G z hzz, add_neg_cancel, transvection_zero']
  have hc2 : _root_.GlobalTheory.UTrans.tv σ G y c' * E₂ =
      _root_.GlobalTheory.UTrans.tv σ G ((_root_.GlobalTheory.UTrans.tv σ G y c').mulVec z) (-ω) *
        _root_.GlobalTheory.UTrans.tv σ G y c' := by
    rw [hE₂, isometry_mul_transvection σ G _ hτiso]
  refine ⟨m₁ * E₁ * _root_.GlobalTheory.UTrans.tv σ G ((_root_.GlobalTheory.UTrans.tv σ G y c').mulVec z) (-ω), ?_, ?_⟩
  · refine mul_mem (mul_mem hm₁ ?_) ?_
    · unfold _root_.GlobalTheory.UTrans.TvGen
      exact Submonoid.subset_closure ⟨z, ω, hzz, by rw [hσω]; ring, rfl⟩
    · unfold _root_.GlobalTheory.UTrans.TvGen
      exact Submonoid.subset_closure ⟨_, -ω, by rw [hτiso, hzz], by rw [map_neg, hσω]; ring, rfl⟩
  · have key : _root_.GlobalTheory.UTrans.tv σ G (x + (a + ω * β) • z) c' =
        E₁ * _root_.GlobalTheory.UTrans.tv σ G y c' * E₂ := by
      rw [hc1, mul_assoc, hEE, mul_one]
    rw [h₁, key, mul_assoc E₁, hc2]
    simp only [mul_assoc]

end GlobalTheory.UTrans.PlaneRefl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SpecialLinearClassNumberOneAdelic
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_matrix_span_of_smul_mem {ι : Type} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℤ)) (N : ℤ)
    (hN : N ≠ 0) (hL : ∀ v : ι → ℤ, N • v ∈ L) :
    ∃ H : Matrix ι ι ℤ, (∀ j, (fun i => H i j) ∈ L) ∧ ∀ v ∈ L, ∃ c : ι → ℤ, v = H *ᵥ c := by
  have hr : Module.finrank ℤ L = Fintype.card ι := by
    apply le_antisymm
    · simpa using Submodule.finrank_le L
    · let f : (ι → ℤ) →ₗ[ℤ] L := LinearMap.codRestrict L (N • LinearMap.id) hL
      have hf : Function.Injective f := by
        intro a b hab
        have : N • a = N • b := congrArg Subtype.val hab
        exact smul_right_injective _ hN this
      simpa using LinearMap.finrank_le_finrank_of_injective hf
  let b : Module.Basis ι ℤ L := (Module.finBasisOfFinrankEq ℤ L hr).reindex (Fintype.equivFin ι).symm
  refine ⟨Matrix.of fun i j => (b j : ι → ℤ) i, fun j => (b j).2, fun v hv => ⟨b.repr ⟨v, hv⟩, ?_⟩⟩
  have := congrArg Subtype.val (b.sum_repr ⟨v, hv⟩)
  funext i
  have h2 := congrFun this i
  simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul] at h2
  rw [← h2]
  simp [Matrix.mulVec, dotProduct, mul_comm]

theorem exists_matrix_basis_of_lattice {ι : Type} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℚ)) (M : ℕ)
    (hM : 0 < M) (h1 : ∀ v ∈ L, ∀ i, ∃ z : ℤ, (M : ℚ) * v i = z)
    (h2 : ∀ z : ι → ℤ, (fun i => (M : ℚ) * z i) ∈ L) :
    ∃ h g : Matrix ι ι ℚ, h * g = 1 ∧ (∀ j, (fun i => h i j) ∈ L) ∧ ∀ v ∈ L, ∀ i, ∃ z : ℤ, (g *ᵥ v) i = z := by
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  let φ : (ι → ℤ) →ₗ[ℤ] (ι → ℚ) :=
    { toFun := fun z i => (M : ℚ)⁻¹ * z i
      map_add' := fun a b => by funext i; simp [mul_add]
      map_smul' := fun a b => by funext i; simp; ring }
  obtain ⟨H, hH, hc⟩ := exists_matrix_span_of_smul_mem (L.comap φ) ((M : ℤ) * M)
    (by have := hM.ne'; positivity) (fun v => by
      have : φ (((M : ℤ) * M) • v) = fun i => (M : ℚ) * v i := by
        funext i
        simp [φ]
        field_simp
      simp only [Submodule.mem_comap, this]
      exact h2 v)
  let h : Matrix ι ι ℚ := Matrix.of fun i j => (M : ℚ)⁻¹ * H i j
  have key : ∀ v ∈ L, ∃ c : ι → ℤ, v = h *ᵥ fun i => (c i : ℚ) := by
    intro v hv
    choose z hz using h1 v hv
    have hφ : φ z = v := by
      funext i
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, ← hz]
      field_simp
    obtain ⟨c, hc'⟩ := hc z (by simpa [hφ] using hv)
    refine ⟨c, ?_⟩
    rw [← hφ, hc']
    funext i
    simp [φ, h, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  choose C hC using fun j => key _ (h2 (Pi.single j 1))
  let g : Matrix ι ι ℚ := Matrix.of fun i j => (M : ℚ)⁻¹ * C j i
  have hg : h * g = 1 := by
    ext i j
    have := congrFun (hC j) i
    simp only [Matrix.mulVec, dotProduct] at this
    have e : (h * g) i j = (M : ℚ)⁻¹ * ∑ k, h i k * (C j k : ℚ) := by
      simp only [Matrix.mul_apply, g, Matrix.of_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e, ← this]
    by_cases hij : i = j
    · subst hij; simp [hM']
    · simp [hij]
  refine ⟨h, g, hg, fun j => hH j, fun v hv i => ?_⟩
  obtain ⟨c, rfl⟩ := key v hv
  refine ⟨c i, ?_⟩
  rw [Matrix.mulVec_mulVec, mul_eq_one_comm.mp hg, Matrix.one_mulVec]

theorem det_mem_subring_of_entries {ι : Type} [Fintype ι] [DecidableEq ι] {R : Type} [CommRing R] (R₀ : Subring R)
    (k : Matrix ι ι R) (hk : ∀ i j, k i j ∈ R₀) : k.det ∈ R₀ := by
  rw [Matrix.det_apply']
  exact R₀.sum_mem fun σ _ => R₀.mul_mem (intCast_mem R₀ _) (R₀.prod_mem fun i _ => hk _ _)

theorem sl_class_number_one : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), AdelicPair R R₀ → ∀ x : Matrix ι ι R, x.det = 1 → ∃ (h : Matrix ι ι ℚ) (k : Matrix ι ι R), h.det = 1 ∧ k.det = 1 ∧ (∀ i j, k i j ∈ R₀) ∧ x = h.map (algebraMap ℚ R) * k := by
  intro ι _ _ R _ _ R₀ hp x hx
  obtain ⟨-, hden, hinj⟩ := adelicPair_elementary R R₀ hp
  set y := x.adjugate with hy
  have hxy : x * y = 1 := by rw [hy, Matrix.mul_adjugate, hx, one_smul]
  have hyx : y * x = 1 := mul_eq_one_comm.mp hxy
  obtain ⟨M, hM, hMr⟩ := hden ((ι × ι) ⊕ (ι × ι)) (Sum.elim (fun p => x p.1 p.2) (fun p => y p.1 p.2))
  have hMx : ∀ i j, (M : R) * x i j ∈ R₀ := fun i j => hMr (Sum.inl (i, j))
  have hMy : ∀ i j, (M : R) * y i j ∈ R₀ := fun i j => hMr (Sum.inr (i, j))
  let L : Submodule ℤ (ι → ℚ) := AddSubgroup.toIntSubmodule
    { carrier := {v | ∀ i, ∑ k, y i k * algebraMap ℚ R (v k) ∈ R₀}
      add_mem' := fun {a b} ha hb i => by
        simpa [mul_add, Finset.sum_add_distrib] using R₀.add_mem (ha i) (hb i)
      zero_mem' := fun i => by simp
      neg_mem' := fun {a} ha i => by simpa using R₀.neg_mem (ha i) }
  have hLm : ∀ v, v ∈ L ↔ ∀ i, ∑ k, y i k * algebraMap ℚ R (v k) ∈ R₀ := fun v => Iff.rfl
  have h2 : ∀ z : ι → ℤ, (fun i => (M : ℚ) * z i) ∈ L := by
    intro z
    rw [hLm]
    intro i
    refine R₀.sum_mem fun k _ => ?_
    have : y i k * algebraMap ℚ R ((M : ℚ) * z k) = (M : R) * y i k * z k := by simp; ring
    rw [this]
    exact R₀.mul_mem (hMy _ _) (intCast_mem R₀ _)
  have h1 : ∀ v ∈ L, ∀ i, ∃ z : ℤ, (M : ℚ) * v i = z := by
    intro v hv i
    apply hp.int_of_mem
    have e : (fun k => algebraMap ℚ R (v k)) = x *ᵥ (y *ᵥ fun k => algebraMap ℚ R (v k)) := by
      rw [Matrix.mulVec_mulVec, hxy, Matrix.one_mulVec]
    have e' := congrFun e i
    rw [map_mul, map_natCast, e']
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
    refine R₀.sum_mem fun k _ => ?_
    rw [← mul_assoc]
    exact R₀.mul_mem (hMx _ _) ((hLm v).1 hv k)
  obtain ⟨h, g, hg, hh, hgL⟩ := exists_matrix_basis_of_lattice L M hM h1 h2
  have hMg : ∀ i j, (M : R) * algebraMap ℚ R (g i j) ∈ R₀ := by
    intro i j
    obtain ⟨z, hz⟩ := hgL _ (h2 (Pi.single j 1)) i
    have : (M : ℚ) * g i j = z := by
      rw [← hz]
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single j]
      · simp [mul_comm]
      · intro b _ hb; simp [hb]
      · simp
    have e : (M : R) * algebraMap ℚ R (g i j) = (z : R) := by
      rw [← map_natCast (algebraMap ℚ R), ← map_mul, this, map_intCast]
    rw [e]
    exact intCast_mem R₀ _
  have hk : ∀ i j, (g.map (algebraMap ℚ R) * x) i j ∈ R₀ := by
    intro i j
    choose q a ha hqa using fun k => hp.approx M hM (x k j)
    have hq : q ∈ L := by
      rw [hLm]
      intro l
      have e : ∑ k, y l k * algebraMap ℚ R (q k) = (y * x) l j - ∑ k, (M : R) * y l k * a k := by
        rw [Matrix.mul_apply, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by rw [hqa k]; ring
      rw [e, hyx]
      refine R₀.sub_mem ?_ (R₀.sum_mem fun k _ => R₀.mul_mem (hMy _ _) (ha k))
      rw [Matrix.one_apply]
      split_ifs
      exacts [R₀.one_mem, R₀.zero_mem]
    obtain ⟨z, hz⟩ := hgL q hq i
    have e : (g.map (algebraMap ℚ R) * x) i j =
        algebraMap ℚ R ((g *ᵥ q) i) + ∑ k, (M : R) * algebraMap ℚ R (g i k) * a k := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply, map_mul]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [hqa k]; ring
    rw [e, hz, map_intCast]
    exact R₀.add_mem (intCast_mem R₀ _) (R₀.sum_mem fun k _ => R₀.mul_mem (hMg _ _) (ha k))
  have hk' : ∀ i j, (y * h.map (algebraMap ℚ R)) i j ∈ R₀ := fun i j => (hLm _).1 (hh j) i
  have hmd : ∀ t : Matrix ι ι ℚ, (t.map (algebraMap ℚ R)).det = algebraMap ℚ R t.det := fun t =>
    ((algebraMap ℚ R).map_det t).symm
  have hdy : y.det = 1 := by
    have := congrArg Matrix.det hxy
    rwa [Matrix.det_mul, hx, one_mul, Matrix.det_one] at this
  obtain ⟨zg, hzg⟩ := hp.int_of_mem g.det (by
    have := det_mem_subring_of_entries R₀ _ hk
    rwa [Matrix.det_mul, hx, mul_one, hmd] at this)
  obtain ⟨zh, hzh⟩ := hp.int_of_mem h.det (by
    have := det_mem_subring_of_entries R₀ _ hk'
    rwa [Matrix.det_mul, hdy, one_mul, hmd] at this)
  have hdd : h.det * g.det = 1 := by rw [← Matrix.det_mul, hg, Matrix.det_one]
  have hz : zh * zg = 1 := by
    rw [hzg, hzh] at hdd
    exact_mod_cast hdd
  have hxe : x = h.map (algebraMap ℚ R) * (g.map (algebraMap ℚ R) * x) := by
    rw [← Matrix.mul_assoc, ← Matrix.map_mul, hg]
    simp
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hz with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · refine ⟨h, _, by simp [hzh, e1], ?_, hk, hxe⟩
    rw [Matrix.det_mul, hx, hmd, hzg, e2]
    simp
  · rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
    · rw [Matrix.det_isEmpty, e1] at hzh
      norm_num at hzh
    · let d : ι → ℚ := fun i => if i = i₀ then -1 else 1
      have hd : (Matrix.diagonal d).det = -1 := by simp [d]
      have hdd2 : Matrix.diagonal d * Matrix.diagonal d = 1 := by
        rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext i
        by_cases hi : i = i₀ <;> simp [d, hi]
      refine ⟨h * Matrix.diagonal d, (Matrix.diagonal d).map (algebraMap ℚ R) * (g.map (algebraMap ℚ R) * x),
        ?_, ?_, ?_, ?_⟩
      · rw [Matrix.det_mul, hd, hzh, e1]
        simp
      · rw [Matrix.det_mul, Matrix.det_mul, hx, hmd, hmd, hd, hzg, e2]
        simp
      · intro i j
        rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul]
        refine R₀.mul_mem ?_ (hk i j)
        by_cases hi : i = i₀
        · simpa [d, hi] using R₀.neg_mem R₀.one_mem
        · simpa [d, hi] using R₀.one_mem
      · rw [← Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_assoc h, hdd2, Matrix.mul_one]
        exact hxe

end GlobalTheory.ClassFin
end

