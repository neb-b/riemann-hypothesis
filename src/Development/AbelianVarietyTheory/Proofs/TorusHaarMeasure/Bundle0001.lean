module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsBasisAdaptedTwoSubspaces
section
namespace GlobalTheory

theorem exists_relCompl_submodule {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {U W : Submodule K V} (h : U ≤ W) : ∃ C : Submodule K V, Disjoint U C ∧ U ⊔ C = W := by
  obtain ⟨C, hC⟩ := U.exists_isCompl
  refine ⟨C ⊓ W, hC.disjoint.mono_right inf_le_left, ?_⟩
  rw [← sup_inf_assoc_of_le C h, hC.sup_eq_top, top_inf_eq]

theorem exists_fin_independent_span_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : Submodule K V) :
    ∃ (n : ℕ) (v : Fin n → V), LinearIndependent K v ∧ Submodule.span K (Set.range v) = S := by
  let b := Module.finBasis K S
  refine ⟨_, S.subtype ∘ b, b.linearIndependent.map' S.subtype (Submodule.ker_subtype S), ?_⟩
  rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]

theorem exists_basis_adapted_two_subspaces (K V : Type) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W₁ W₂ : Submodule K V) :
    ∃ (a b c : ℕ) (w : Fin a ⊕ Fin b ⊕ Fin c → V), LinearIndependent K w ∧
      Submodule.span K (Set.range (w ∘ Sum.inl)) = W₁ ⊓ W₂ ∧
      Submodule.span K (Set.range (w ∘ Sum.map id Sum.inl)) = W₁ ∧
      Submodule.span K (Set.range (w ∘ Sum.map id Sum.inr)) = W₂ ∧
      Submodule.span K (Set.range w) = W₁ ⊔ W₂ := by
  obtain ⟨C₁, hd₁, hs₁⟩ := exists_relCompl_submodule (inf_le_left : W₁ ⊓ W₂ ≤ W₁)
  obtain ⟨C₂, hd₂, hs₂⟩ := exists_relCompl_submodule (inf_le_right : W₁ ⊓ W₂ ≤ W₂)
  obtain ⟨a, u, hu, hus⟩ := exists_fin_independent_span_eq (W₁ ⊓ W₂)
  obtain ⟨b, v₁, hv₁, hvs₁⟩ := exists_fin_independent_span_eq C₁
  obtain ⟨c, v₂, hv₂, hvs₂⟩ := exists_fin_independent_span_eq C₂
  have hC₁ : C₁ ≤ W₁ := hs₁ ▸ le_sup_right
  have hC₂ : C₂ ≤ W₂ := hs₂ ▸ le_sup_right
  have h12 : Disjoint C₁ C₂ := by
    rw [Submodule.disjoint_def]
    intro x hx₁ hx₂
    exact (Submodule.disjoint_def.1 hd₁) x ⟨hC₁ hx₁, hC₂ hx₂⟩ hx₁
  have hU : Disjoint (W₁ ⊓ W₂) (C₁ ⊔ C₂) := by
    rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
    have hz1 : z ∈ W₁ := by
      have := W₁.sub_mem hx.1 (hC₁ hy)
      simpa using this
    have hz0 : z = 0 := (Submodule.disjoint_def.1 hd₂) z ⟨hz1, hC₂ hz⟩ hz
    subst hz0
    rw [add_zero] at hx ⊢
    exact (Submodule.disjoint_def.1 hd₁) y hx hy
  have hv : LinearIndependent K (Sum.elim v₁ v₂) :=
    hv₁.sum_type hv₂ (by rw [hvs₁, hvs₂]; exact h12)
  have hvs : Submodule.span K (Set.range (Sum.elim v₁ v₂)) = C₁ ⊔ C₂ := by
    rw [Set.Sum.elim_range, Submodule.span_union, hvs₁, hvs₂]
  refine ⟨a, b, c, Sum.elim u (Sum.elim v₁ v₂),
    hu.sum_type hv (by rw [hus, hvs]; exact hU), ?_, ?_, ?_, ?_⟩
  · rw [Sum.elim_comp_inl, hus]
  · have : Sum.elim u (Sum.elim v₁ v₂) ∘ Sum.map id Sum.inl = Sum.elim u v₁ := by
      funext x; cases x <;> rfl
    rw [this, Set.Sum.elim_range, Submodule.span_union, hus, hvs₁, hs₁]
  · have : Sum.elim u (Sum.elim v₁ v₂) ∘ Sum.map id Sum.inr = Sum.elim u v₂ := by
      funext x; cases x <;> rfl
    rw [this, Set.Sum.elim_range, Submodule.span_union, hus, hvs₂, hs₂]
  · rw [Set.Sum.elim_range, Submodule.span_union, hus, hvs, sup_sup_distrib_left, hs₁, hs₂]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsFiniteSymmetricIrreducibleRotations
section
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory
namespace HypRot

variable {r : ℕ}

noncomputable def offN (j k : Fin r) (u : ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.single j k u + Matrix.single k j (star u)

noncomputable def projP (j k : Fin r) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.single j j 1 + Matrix.single k k 1

noncomputable def rot (j k : Fin r) (u : ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  1 + (1 / 4 : ℂ) • projP j k + (3 / 4 : ℂ) • offN j k u

lemma offN_neg (j k : Fin r) (u : ℂ) : offN j k (-u) = - offN j k u := by
  simp only [offN, star_neg, Matrix.single_neg, neg_add]

lemma offN_sq {j k : Fin r} (h : j ≠ k) {u : ℂ} (hu : u * star u = 1) :
    offN j k u * offN j k u = projP j k := by
  have hu' : star u * u = 1 := by rw [mul_comm]; exact hu
  simp only [offN, projP, add_mul, mul_add, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, h, h.symm, ne_eq, not_false_eq_true, hu, hu',
    zero_add, add_zero]
  exact add_comm _ _

lemma projP_offN {j k : Fin r} (h : j ≠ k) (u : ℂ) :
    projP j k * offN j k u = offN j k u := by
  simp only [offN, projP, add_mul, mul_add, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, h, h.symm, ne_eq, not_false_eq_true, one_mul,
    zero_add, add_zero]

lemma offN_projP {j k : Fin r} (h : j ≠ k) (u : ℂ) :
    offN j k u * projP j k = offN j k u := by
  simp only [offN, projP, add_mul, mul_add, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, h, h.symm, ne_eq, not_false_eq_true,
    mul_one, zero_add, add_zero]
  exact add_comm _ _

lemma projP_sq {j k : Fin r} (h : j ≠ k) : projP j k * projP j k = projP j k := by
  simp only [projP, add_mul, mul_add, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, h, h.symm, ne_eq, not_false_eq_true, one_mul,
    zero_add, add_zero]

lemma rot_mul_neg {j k : Fin r} (h : j ≠ k) {u : ℂ} (hu : u * star u = 1) :
    rot j k u * rot j k (-u) = 1 := by
  have hPP := projP_sq h
  have hPN := projP_offN h u
  have hNP := offN_projP h u
  have hNN := offN_sq h hu
  simp only [rot, offN_neg, smul_neg, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, mul_neg, hPP, hPN, hNP, hNN]
  module

lemma rot_sq_sub {j k : Fin r} (h : j ≠ k) {u : ℂ} (hu : u * star u = 1) :
    offN j k u = (4 / 15 : ℂ) • (rot j k u * rot j k u - rot j k (-u) * rot j k (-u)) := by
  have hPP := projP_sq h
  have hPN := projP_offN h u
  have hNP := offN_projP h u
  have hNN := offN_sq h hu
  simp only [rot, offN_neg, smul_neg, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, mul_neg, neg_mul, hPP, hPN, hNP, hNN]
  module

lemma rot_inv {j k : Fin r} (h : j ≠ k) {u : ℂ} (hu : u * star u = 1) :
    (rot j k u)⁻¹ = rot j k (-u) := Matrix.inv_eq_right_inv (rot_mul_neg h hu)

lemma rot_det {j k : Fin r} (h : j ≠ k) {u : ℂ} (hu : u * star u = 1) :
    (rot j k u).det ≠ 0 := (Matrix.isUnit_det_of_right_inverse (rot_mul_neg h hu)).ne_zero

lemma rot_herm (j k : Fin r) (u : ℂ) : (rot j k u).IsHermitian := by
  unfold Matrix.IsHermitian
  simp only [rot, offN, projP, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, Matrix.conjTranspose_single, star_star, star_one, smul_add]
  have h4 : star (1 / 4 : ℂ) = 1 / 4 := by simp
  have h34 : star (3 / 4 : ℂ) = 3 / 4 := by simp
  rw [h4, h34]
  abel

private lemma diagonal_mul_single (d : Fin r → ℂ) (i j : Fin r) (c : ℂ) :
    Matrix.diagonal d * Matrix.single i j c = Matrix.single i j (d i * c) := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.single_apply, Matrix.single_apply]
  by_cases h1 : i = a <;> by_cases h2 : j = b <;> simp [h1, h2]

private lemma single_mul_diagonal (d : Fin r → ℂ) (i j : Fin r) (c : ℂ) :
    Matrix.single i j c * Matrix.diagonal d = Matrix.single i j (c * d j) := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.single_apply, Matrix.single_apply]
  by_cases h1 : i = a <;> by_cases h2 : j = b <;> simp [h1, h2]

lemma diag_rot {j k : Fin r} (d : Fin r → ℂ) (hd : d j = - d k) (u : ℂ) :
    Matrix.diagonal d * rot j k u = rot j k (-u) * Matrix.diagonal d := by
  simp only [rot, offN, projP, mul_add, add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul, diagonal_mul_single, single_mul_diagonal, star_neg, hd]
  simp only [mul_one, one_mul, neg_mul, mul_neg, neg_neg, mul_comm u (d k), mul_comm (star u) (d k)]

lemma rot_unitary {j k : Fin r} (h : j ≠ k) {u : ℂ} (hu : u * star u = 1)
    (d : Fin r → ℂ) (hd : d j = - d k) :
    (rot j k u)ᵀ * Matrix.diagonal d * (rot j k u).map (starRingEnd ℂ) = Matrix.diagonal d := by
  have hT : (rot j k u)ᵀ = rot j k (star u) := by
    simp only [rot, offN, projP, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one,
      Matrix.transpose_single, star_star, smul_add]
    abel
  have hC : (rot j k u).map (starRingEnd ℂ) = (rot j k u)ᵀ := by
    ext a b
    simp only [Matrix.map_apply, Matrix.transpose_apply, starRingEnd_apply]
    exact (rot_herm j k u).apply b a
  have hu' : star u * star (star u) = 1 := by rw [star_star, mul_comm]; exact hu
  rw [hC, hT, Matrix.mul_assoc, diag_rot d hd, ← Matrix.mul_assoc, rot_mul_neg h hu',
    Matrix.one_mul]

end HypRot


open HypRot in
theorem exists_finite_symmetric_irreducible_rotations :
    (∀ (r p : ℕ), 0 < p → p < r → ∀ W : Submodule ℂ (Fin r → ℂ), (∀ j k : Fin r, (j : ℕ) < p → p ≤ (k : ℕ) → ∀ v ∈ W, (Matrix.single j k (1 : ℂ)).mulVec v ∈ W ∧ (Matrix.single k j (1 : ℂ)).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → (∀ (r p : ℕ), 0 < p → p < r → ∃ S : Finset (Matrix (Fin r) (Fin r) ℂ), S.Nonempty ∧ (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) ∧ (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) ∧ ∀ a ∈ S, (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) ∧ ∃ s : Matrix (Fin r) (Fin r) ℂ, (s)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) * (s).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) ∧ s * a = a⁻¹ * s) := by
  intro H r p hp hpr
  classical
  have hne : ∀ j k : Fin r, (j : ℕ) < p → p ≤ (k : ℕ) → j ≠ k := by
    intro j k hj hk e
    have := congrArg Fin.val e
    omega
  have hUs : ∀ u ∈ ({1, -1, Complex.I, -Complex.I} : Finset ℂ),
      u * star u = 1 ∧ -u ∈ ({1, -1, Complex.I, -Complex.I} : Finset ℂ) := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl <;>
      simp [Complex.ext_iff]
  refine ⟨((Finset.univ.filter fun jk : Fin r × Fin r => (jk.1 : ℕ) < p ∧ p ≤ (jk.2 : ℕ)) ×ˢ
      ({1, -1, Complex.I, -Complex.I} : Finset ℂ)).image (fun x => rot x.1.1 x.1.2 x.2),
      ?_, ?_, ?_, ?_⟩
  · refine ⟨rot ⟨0, by omega⟩ ⟨p, hpr⟩ 1, Finset.mem_image.mpr ⟨((⟨0, by omega⟩, ⟨p, hpr⟩), 1), ?_, rfl⟩⟩
    simp [hp]
  · intro a ha
    obtain ⟨⟨⟨j, k⟩, u⟩, hx, rfl⟩ := Finset.mem_image.mp ha
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨⟨hj, hk⟩, hu⟩ := hx
    refine ⟨rot_herm j k u, rot_det (hne j k hj hk) (hUs u hu).1, ?_⟩
    rw [rot_inv (hne j k hj hk) (hUs u hu).1]
    exact Finset.mem_image.mpr ⟨((j, k), -u), by simp [hj, hk, (hUs u hu).2], rfl⟩
  · intro W hW
    apply H r p hp hpr W
    intro j k hj hk v hv
    have hjk := hne j k hj hk
    have hmem : ∀ u ∈ ({1, -1, Complex.I, -Complex.I} : Finset ℂ), rot j k u ∈
        ((Finset.univ.filter fun jk : Fin r × Fin r => (jk.1 : ℕ) < p ∧ p ≤ (jk.2 : ℕ)) ×ˢ
        ({1, -1, Complex.I, -Complex.I} : Finset ℂ)).image (fun x => rot x.1.1 x.1.2 x.2) := by
      intro u hu
      exact Finset.mem_image.mpr ⟨((j, k), u), by simp [hj, hk, hu], rfl⟩
    have hN : ∀ u ∈ ({1, -1, Complex.I, -Complex.I} : Finset ℂ), (offN j k u).mulVec v ∈ W := by
      intro u hu
      rw [rot_sq_sub hjk (hUs u hu).1, Matrix.smul_mulVec, Matrix.sub_mulVec]
      exact W.smul_mem _ (W.sub_mem (hW _ (hmem u hu) v hv) (hW _ (hmem _ (hUs u hu).2) v hv))
    have h1 : (1 : ℂ) ∈ ({1, -1, Complex.I, -Complex.I} : Finset ℂ) := by simp
    have hI : Complex.I ∈ ({1, -1, Complex.I, -Complex.I} : Finset ℂ) := by simp
    have hII : Complex.I * star Complex.I = 1 := by
      rw [Complex.star_def, Complex.conj_I, mul_neg, Complex.I_mul_I, neg_neg]
    have hsI : Complex.I • offN j k Complex.I = -Matrix.single j k (1 : ℂ) + Matrix.single k j 1 := by
      rw [offN, smul_add, Matrix.smul_single, Matrix.smul_single, smul_eq_mul, smul_eq_mul,
        Complex.I_mul_I, hII, Matrix.single_neg]
    have h1' : offN j k (1 : ℂ) = Matrix.single j k 1 + Matrix.single k j 1 := by
      rw [offN, star_one]
    have e1 : Matrix.single j k (1 : ℂ) = (1 / 2 : ℂ) • (offN j k 1 - Complex.I • offN j k Complex.I) := by
      rw [hsI, h1']
      module
    have e2 : Matrix.single k j (1 : ℂ) = (1 / 2 : ℂ) • (offN j k 1 + Complex.I • offN j k Complex.I) := by
      rw [hsI, h1']
      module
    constructor
    · rw [e1, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec]
      exact W.smul_mem _ (W.sub_mem (hN 1 h1) (W.smul_mem _ (hN _ hI)))
    · rw [e2, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec]
      exact W.smul_mem _ (W.add_mem (hN 1 h1) (W.smul_mem _ (hN _ hI)))
  · intro a ha
    obtain ⟨⟨⟨j, k⟩, u⟩, hx, rfl⟩ := Finset.mem_image.mp ha
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨⟨hj, hk⟩, hu⟩ := hx
    have hjk := hne j k hj hk
    have hd : (fun i : Fin r => if (i : ℕ) < p then (1 : ℂ) else -1) j =
        -(fun i : Fin r => if (i : ℕ) < p then (1 : ℂ) else -1) k := by
      simp [hj, not_lt.mpr hk]
    refine ⟨rot_unitary hjk (hUs u hu).1 _ hd, Matrix.diagonal fun i : Fin r => if (i : ℕ) < p then (1 : ℂ) else -1, ?_, ?_⟩
    · rw [Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      split_ifs <;> simp
    · rw [rot_inv hjk (hUs u hu).1]
      exact diag_rot _ hd u

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIntMulMem
section
namespace GlobalTheory.IntegralMultiples

theorem exists_int_smul_mem {E : Type} [Field E] [NumberField E] {r : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin r → E))
    (hΛ : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (v : Fin r → E) :
    ∃ k : ℤ, k ≠ 0 ∧ k • v ∈ Λ := by
  classical
  have hv : v ∈ Submodule.span E (Λ : Set (Fin r → E)) := by
    rw [hΛ]
    exact Submodule.mem_top
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.mp hv
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image f)
  refine ⟨y, hy0, ?_⟩
  rw [← hfg, Finset.smul_sum]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  have hi := hy (f i) (Finset.mem_image_of_mem f (Finset.mem_univ i))
  let o : NumberField.RingOfIntegers E := ⟨y • f i, hi⟩
  have e : y • f i • (g i : Fin r → E) = o • (g i : Fin r → E) := by
    rw [← smul_assoc, ← algebraMap_smul E o]
    rfl
  rw [e]
  exact Λ.smul_mem o (g i).2

theorem main : ∀ {E : Type} [inst : Field E] [NumberField E] {r : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin r → E)),
    Submodule.span E (↑Λ : Set (Fin r → E)) = ⊤ →
      ∀ (v : Fin r → E), ∃ (k : ℤ), k ≠ (0 : ℤ) ∧ k • v ∈ Λ := by
  intro E _ _ r Λ hΛ v
  exact exists_int_smul_mem Λ hΛ v

end GlobalTheory.IntegralMultiples
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsRpowNegSumLeOfSumLog
section
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem rpow_neg_le_one_sub_log_add_sq {ω δ t : ℝ} (hω : 1 ≤ ω) (hδ : 0 < δ)
    (hδL : δ * Real.log ω ≤ 1) (h1 : ω⁻¹ ≤ t) (h2 : t ≤ ω) :
    t ^ (-δ) ≤ 1 - δ * Real.log t + (δ * Real.log ω) ^ 2 := by
  have hω0 : 0 < ω := by linarith
  have ht : 0 < t := lt_of_lt_of_le (inv_pos.mpr hω0) h1
  have hu : Real.log t ≤ Real.log ω := Real.log_le_log ht h2
  have hl : -Real.log ω ≤ Real.log t := by
    rw [← Real.log_inv]; exact Real.log_le_log (inv_pos.mpr hω0) h1
  have habs : |Real.log t * (-δ)| ≤ δ * Real.log ω := by
    rw [abs_le]; constructor <;> nlinarith
  have h := Real.abs_exp_sub_one_sub_id_le (habs.trans hδL)
  have h' := (abs_le.mp h).2
  have hsq : (Real.log t * (-δ)) ^ 2 ≤ (δ * Real.log ω) ^ 2 := by
    rw [← sq_abs (Real.log t * (-δ))]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  rw [Real.rpow_def_of_pos ht]
  linarith

theorem exists_rpow_neg_sum_le_of_sum_log :
    (∀ (N : ℕ) (ω η : ℝ), 1 ≤ ω → 0 < η → ∃ δ c : ℝ, 0 < δ ∧ 0 ≤ c ∧ c < 1 ∧ ∀ (σ : Type) (S : Finset σ) (t : σ → ℝ), S.card = N → (∀ s ∈ S, ω⁻¹ ≤ t s ∧ t s ≤ ω) → η ≤ ∑ s ∈ S, Real.log (t s) → ∑ s ∈ S, t s ^ (-δ) ≤ N * c) := by
  intro N ω η hω hη
  have hL : 0 ≤ Real.log ω := Real.log_nonneg hω
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  obtain ⟨δ, hδ, hδL, hδη⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * Real.log ω ≤ 1 ∧
      δ * (N * Real.log ω ^ 2) ≤ η / 2 := by
    refine ⟨min (1 / (Real.log ω + 1)) (η / 2 / (N * Real.log ω ^ 2 + 1)),
      lt_min (by positivity) (by positivity), ?_, ?_⟩
    · have h := min_le_left (1 / (Real.log ω + 1)) (η / 2 / (N * Real.log ω ^ 2 + 1))
      have hp : 0 < min (1 / (Real.log ω + 1)) (η / 2 / (N * Real.log ω ^ 2 + 1)) :=
        lt_min (by positivity) (by positivity)
      rw [le_div_iff₀ (by positivity)] at h
      nlinarith
    · have h := min_le_right (1 / (Real.log ω + 1)) (η / 2 / (N * Real.log ω ^ 2 + 1))
      have hp : 0 < min (1 / (Real.log ω + 1)) (η / 2 / (N * Real.log ω ^ 2 + 1)) :=
        lt_min (by positivity) (by positivity)
      rw [le_div_iff₀ (by positivity)] at h
      nlinarith
  have he : 0 < δ * η / (2 * (N + 1)) := by positivity
  refine ⟨δ, max 0 (1 - δ * η / (2 * (N + 1))), hδ, le_max_left _ _,
    max_lt one_pos (by linarith), ?_⟩
  intro σ S t hS ht hsum
  have h1 : ∑ s ∈ S, t s ^ (-δ) ≤
      ∑ s ∈ S, (1 - δ * Real.log (t s) + (δ * Real.log ω) ^ 2) :=
    Finset.sum_le_sum fun s hs =>
      rpow_neg_le_one_sub_log_add_sq hω hδ hδL (ht s hs).1 (ht s hs).2
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h1
  simp only [Finset.sum_const, hS, nsmul_eq_mul, mul_one] at h1
  have h2 : δ * η ≤ δ * ∑ s ∈ S, Real.log (t s) := mul_le_mul_of_nonneg_left hsum hδ.le
  have h3 : δ * (δ * (N * Real.log ω ^ 2)) ≤ δ * (η / 2) := mul_le_mul_of_nonneg_left hδη hδ.le
  have h4 : (N : ℝ) * (1 - δ * η / (2 * (N + 1))) ≤ N * max 0 (1 - δ * η / (2 * (N + 1))) :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hN
  have h5 : (N + 1 : ℝ) * (δ * η / (2 * (N + 1))) = δ * η / 2 := by field_simp
  nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsScalarSubPosSemidef
section
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory


open scoped Matrix.Norms.L2Operator MatrixOrder in
open scoped MatrixOrder Matrix.Norms.L2Operator in
theorem exists_scalar_sub_posSemidef {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (hA : A.IsHermitian) :
    ∃ c : ℝ, 1 ≤ c ∧ ((c : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - A).PosSemidef := by
  have h1 : (‖A‖ • (1 : Matrix (Fin r) (Fin r) ℂ) - A).PosSemidef := by
    have h := IsSelfAdjoint.le_algebraMap_norm_self (a := A) hA
    rw [Algebra.algebraMap_eq_smul_one] at h
    exact Matrix.le_iff.1 h
  refine ⟨1 + ‖A‖, by linarith [norm_nonneg A], ?_⟩
  have e : ((1 + ‖A‖ : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - A =
      1 + (‖A‖ • (1 : Matrix (Fin r) (Fin r) ℂ) - A) := by
    rw [Complex.coe_smul, add_smul, one_smul, add_sub_assoc]
  rw [e]
  exact Matrix.PosSemidef.one.add h1

theorem gram_det_eq_zero_of_lt_card {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : Matrix (Fin r) ι ℂ) (h : r < Fintype.card ι) : (Nᴴ * N).det = 0 := by
  by_contra hd
  have hu : IsUnit (Nᴴ * N) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hd)
  have h1 := Matrix.rank_of_isUnit _ hu
  have h2 := (Matrix.rank_mul_le_right Nᴴ N).trans (Matrix.rank_le_card_height N)
  rw [h1, Fintype.card_fin] at h2
  omega

theorem gram_det_mul_le :
    (∀ (n : Type) [Fintype n] [DecidableEq n] (P Q : Matrix n n ℂ), P.PosSemidef → Q.PosSemidef → 0 ≤ P.det.re ∧ P.det.re ≤ (P + Q).det.re ∧ (P.det ≠ 0 → (P + Q).det.re ≤ P.det.re → Q = 0)) → (∀ (r : ℕ) (a : Matrix (Fin r) (Fin r) ℂ), ∃ ω : ℝ, 1 ≤ ω ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix (Fin r) ι ℂ), (((a * M)ᴴ * (a * M)).det.re) ≤ ω * (((M)ᴴ * (M)).det.re)) := by
  intro H r a
  obtain ⟨c, hc1, hc⟩ := exists_scalar_sub_posSemidef (aᴴ * a) (Matrix.isHermitian_conjTranspose_mul_self a)
  refine ⟨c ^ r, one_le_pow₀ hc1, ?_⟩
  intro ι _ _ M
  by_cases hι : r < Fintype.card ι
  · rw [gram_det_eq_zero_of_lt_card (a * M) hι, gram_det_eq_zero_of_lt_card M hι]
    simp
  · push Not at hι
    have hP : (Mᴴ * (aᴴ * a) * M).PosSemidef :=
      (Matrix.posSemidef_conjTranspose_mul_self a).conjTranspose_mul_mul_same M
    have hQ : (Mᴴ * ((c : ℂ) • 1 - aᴴ * a) * M).PosSemidef := hc.conjTranspose_mul_mul_same M
    obtain ⟨-, hle, -⟩ := H ι _ _ hP hQ
    have hM0 : 0 ≤ (Mᴴ * M).det.re :=
      (H ι _ _ (Matrix.posSemidef_conjTranspose_mul_self M) (Matrix.posSemidef_conjTranspose_mul_self M)).1
    have e1 : (a * M)ᴴ * (a * M) = Mᴴ * (aᴴ * a) * M := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    have e2 : Mᴴ * (aᴴ * a) * M + Mᴴ * ((c : ℂ) • 1 - aᴴ * a) * M = (c : ℂ) • (Mᴴ * M) := by
      rw [← Matrix.add_mul, ← Matrix.mul_add, add_sub_cancel, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    rw [e1]
    refine hle.trans ?_
    rw [e2, Matrix.det_smul, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc1 hι) hM0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FiniteCovolumeOfDriftFunction
section
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem finite_covolume_of_drift_function :
    (∀ (Y σ : Type) [MeasurableSpace Y] [Fintype σ] [Nonempty σ] (μ : Measure Y) (R : Y → Y → Prop) (t : σ → Y → Y) (f : Y → ℝ) (c b : ℝ), (∀ s, Measurable (t s)) → (∀ s y y', R y y' → R (t s y) (t s y')) → (∀ φ : Y → ℝ≥0∞, Measurable φ → (∀ y y', R y y' → φ y = φ y') → ∀ s, ∫⁻ y, φ (t s y) ∂μ = ∫⁻ y, φ y ∂μ) → Measurable f → (∀ y, 0 ≤ f y) → (∀ y y', R y y' → f y = f y') → 0 ≤ c → c < 1 → 0 ≤ b → (∀ y, ∑ s, f (t s y) ≤ Fintype.card σ * (c * f y + b)) → ∃ M : ℝ, μ Set.univ ≤ 2 * μ {y | f y ≤ M}) → (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G), (∃ U ∈ 𝓝 (1 : G), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → Countable Γ ∧ ∃ F : Set G, MeasurableSet F ∧ ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ F) → (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (h k : G), k * h = h⁻¹ * k → ν.map (fun g => g * h) = ν) → (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] (F : Set G), MeasurableSet F → (∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ F) → (∀ h : G, ν.map (fun g => g * h) = ν → ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) → ∫⁻ g in F, φ (g * h) ∂ν = ∫⁻ g in F, φ g ∂ν) ∧ ∀ K : Set G, MeasurableSet K → ν (F ∩ {g | ∃ γ ∈ Γ, ∃ k ∈ K, g = γ * k}) ≤ ν K) → (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (Γ : Subgroup G) (σ : Type) [Fintype σ] [Nonempty σ] (h : σ → G) (f : G → ℝ) (c b : ℝ), (∃ U ∈ 𝓝 (1 : G), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → (∀ s, ∃ k : G, k * h s = (h s)⁻¹ * k) → Measurable f → (∀ g, 0 ≤ f g) → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → 0 ≤ c → c < 1 → 0 ≤ b → (∀ g, ∑ s, f (g * h s) ≤ Fintype.card σ * (c * f g + b)) → (∀ M : ℝ, ∃ K : Set G, IsCompact K ∧ ∀ g, f g ≤ M → ∃ γ ∈ Γ, ∃ k ∈ K, g = γ * k) → ∃ Ω : Set G, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : G, ∃ γ ∈ Γ, ∃ w ∈ Ω, g = γ * w) := by
  intro h₁ h₂ h₃ h₄ G _ _ _ _ _ _ _ _ ν _ Γ σ _ _ h f c b hΓ hh hf hf0 hfΓ hc0 hc1 hb hd hK
  obtain ⟨hcount, F, hF, hFu⟩ := h₂ G Γ hΓ
  obtain ⟨hinv, hle⟩ := h₄ G ν Γ F hF hFu
  obtain ⟨M, hM⟩ := h₁ G σ (ν.restrict F) (fun y y' => ∃ γ ∈ Γ, y' = γ * y)
    (fun s g => g * h s) f c b (fun s => measurable_mul_const (h s))
    (by
      rintro s y y' ⟨γ, hγ, rfl⟩
      exact ⟨γ, hγ, mul_assoc _ _ _⟩)
    (by
      intro φ hφ hR s
      obtain ⟨k, hk⟩ := hh s
      exact hinv (h s) (h₃ G ν (h s) k hk) φ hφ
        (fun γ hγ g => (hR g (γ * g) ⟨γ, hγ, rfl⟩).symm))
    hf hf0
    (by
      rintro y y' ⟨γ, hγ, rfl⟩
      exact (hfΓ γ hγ y).symm)
    hc0 hc1 hb hd
  obtain ⟨K, hKc, hKf⟩ := hK M
  refine ⟨F, hF, ?_, ?_⟩
  · rw [Measure.restrict_apply_univ, Measure.restrict_apply' hF] at hM
    have h5 : ν ({y | f y ≤ M} ∩ F) ≤ ν K := by
      refine le_trans (measure_mono ?_) (hle K hKc.measurableSet)
      rintro g ⟨hg, hgF⟩
      exact ⟨hgF, hKf g hg⟩
    refine lt_of_le_of_lt hM (ENNReal.mul_lt_top (by simp) ?_)
    exact lt_of_le_of_lt h5 hKc.measure_lt_top
  · intro g
    obtain ⟨γ, hγ, -⟩ := hFu g
    exact ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, γ * g, hγ, by group⟩

end GlobalTheory
end

