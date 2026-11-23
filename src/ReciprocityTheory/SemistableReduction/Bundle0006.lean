module

public import ReciprocityTheory.SemistableReduction.Bundle0002
public import ReciprocityTheory.SemistableReduction.Bundle0001
public import Mathlib
public import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom

@[expose] public section

-- bundled from ReciprocityTheory.SemistableReduction.BWPolyC
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Polynomial

theorem bwp_eval_smul_of_isHomogeneous {σ : Type*} {φ : MvPolynomial σ ℂ} {d : ℕ}
    (hφ : φ.IsHomogeneous d) (t : ℂ) (z : σ → ℂ) :
    MvPolynomial.eval (t • z) φ = t ^ d * MvPolynomial.eval z φ := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i ∈ m.support, m i = d := by
    have h := hφ (MvPolynomial.mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  simp_rw [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    hdeg]
  ring

def bwpMat {p : ℕ} (z : Fin p × Fin p → ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  Matrix.of fun i j => z (i, j)

def bwpId (p : ℕ) : Fin p × Fin p → ℂ := fun ij => if ij.1 = ij.2 then 1 else 0

theorem bwp_det_line_poly {p : ℕ} (z v : Fin p × Fin p → ℂ) :
    ∃ Λ : ℂ[X], ∀ t : ℂ, Λ.eval t = (bwpMat (z + t • v)).det := by
  refine ⟨(Matrix.of fun i j => Polynomial.C (z (i, j)) + Polynomial.C (v (i, j)) * Polynomial.X).det,
    fun t => ?_⟩
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, bwpMat, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  ring

theorem bwp_finite_det_line {p : ℕ} (z v : Fin p × Fin p → ℂ) (hz : (bwpMat z).det ≠ 0) :
    {t : ℂ | (bwpMat (z + t • v)).det = 0}.Finite := by
  obtain ⟨Λ, hΛ⟩ := bwp_det_line_poly z v
  have hΛ0 : Λ ≠ 0 := by
    intro h
    apply hz
    have h0 := hΛ 0
    rw [h, Polynomial.eval_zero] at h0
    simpa using h0.symm
  refine (bwp_finite_eval_eq_zero hΛ0).subset fun t ht => ?_
  simp only [Set.mem_setOf_eq] at ht ⊢
  rw [hΛ]
  exact ht

theorem bwp_finite_det_id_line {p : ℕ} (z : Fin p × Fin p → ℂ) :
    {s : ℂ | (bwpMat (z + s • bwpId p)).det = 0}.Finite := by
  have hne : (-bwpMat z).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  refine (bwp_finite_eval_eq_zero hne).subset fun s hs => ?_
  simp only [Set.mem_setOf_eq] at hs ⊢
  rw [Matrix.charpoly, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  convert hs using 2
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.charmatrix_apply, bwpMat, bwpId, Matrix.diagonal_apply]
    ring
  · simp [Matrix.charmatrix_apply, bwpMat, bwpId, Matrix.diagonal_apply, h]

theorem bwp_continuous_of_matrix {p : ℕ} :
    Continuous (fun y : Fin p → Fin p → ℂ => Matrix.of y) := by
  first
    | exact continuous_id
    | exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp (continuous_apply i)

theorem bwp_exists_bound_unitary {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ → ℂ) (hP : IsHoloGL P) :
    ∃ C : ℝ, ∀ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ‖P U‖ ≤ C := by
  set S : Set (Fin p → Fin p → ℂ) := {y | Matrix.conjTranspose (Matrix.of y) * Matrix.of y = 1} with hS
  have hcl : IsClosed S :=
    isClosed_eq (bwp_continuous_of_matrix.matrix_conjTranspose.matrix_mul bwp_continuous_of_matrix)
      continuous_const
  have hbd : Bornology.IsBounded S := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun y hy => ?_⟩
    have hU : Matrix.of y ∈ Matrix.unitaryGroup (Fin p) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
      exact hy
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i =>
      (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
    first
      | exact entry_norm_bound_of_unitary hU i j
      | exact Matrix.UnitaryGroup.entry_norm_bound hU i j
      | exact Matrix.norm_entry_le_one_of_unitary hU i j
  have hK : IsCompact S := Metric.isCompact_of_isClosed_isBounded hcl hbd
  have hsub : S ⊆ {y | (Matrix.of y).det ≠ 0} := fun y hy => by
    have h := congrArg Matrix.det (show Matrix.conjTranspose (Matrix.of y) * Matrix.of y = 1 from hy)
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact right_ne_zero_of_mul_eq_one h
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (DifferentiableOn.continuousOn hP |>.mono hsub)
  refine ⟨C, fun U hU => ?_⟩
  have hU' : U ∈ S := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU
    exact hU
  exact hC U hU'

theorem bwp_line_poly (hH : LemmaHStatement) (hO : OnePolyGrowthStatement) {p : ℕ} (a : Fin p → ℕ)
    (P : Matrix (Fin p) (Fin p) ℂ → ℂ) (hP : IsHoloGL P) (hT : IsTriEquivariant a P)
    (z v : Fin p × Fin p → ℂ) (hB : {t : ℂ | (bwpMat (z + t • v)).det = 0}.Finite) :
    ∃ Q : ℂ[X], Q.natDegree ≤ ∑ i, a i ∧
      ∀ t, (bwpMat (z + t • v)).det ≠ 0 → P (bwpMat (z + t • v)) = Q.eval t := by
  classical
  obtain ⟨C, hC⟩ := bwp_exists_bound_unitary P hP
  set M : ℝ := ∑ i, ∑ j, (‖z (i, j)‖ + ‖v (i, j)‖) with hMdef
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  have hMj : ∀ j, ∑ i, (‖z (i, j)‖ + ‖v (i, j)‖) ≤ M := fun j =>
    Finset.sum_le_sum fun i _ => Finset.single_le_sum (f := fun j' => ‖z (i, j')‖ + ‖v (i, j')‖)
      (fun j' _ => by positivity) (Finset.mem_univ j)
  have hbound : ∀ t ∉ {t : ℂ | (bwpMat (z + t • v)).det = 0},
      ‖P (bwpMat (z + t • v))‖ ≤ (C * M ^ (∑ i, a i)) * (1 + ‖t‖) ^ (∑ i, a i) := by
    intro t ht
    have hdet : (bwpMat (z + t • v)).det ≠ 0 := ht
    have hcol : ∀ j, colNormSq (bwpMat (z + t • v)) j ≤ (M * (1 + ‖t‖)) ^ 2 := by
      intro j
      have hz : ∑ i, ‖z (i, j)‖ ≤ M :=
        le_trans (Finset.sum_le_sum fun i _ => le_add_of_nonneg_right (norm_nonneg _)) (hMj j)
      have hv : ∑ i, ‖v (i, j)‖ ≤ M :=
        le_trans (Finset.sum_le_sum fun i _ => le_add_of_nonneg_left (norm_nonneg _)) (hMj j)
      set e : Fin p → ℝ := fun i => ‖bwpMat (z + t • v) i j‖ with he_def
      have he0 : ∀ i, 0 ≤ e i := fun i => norm_nonneg _
      have he : ∑ i, e i ≤ M * (1 + ‖t‖) := by
        calc ∑ i, e i ≤ ∑ i, (‖z (i, j)‖ + ‖t‖ * ‖v (i, j)‖) := by
              refine Finset.sum_le_sum fun i _ => ?_
              simp only [he_def, bwpMat, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              exact (norm_add_le _ _).trans (by rw [norm_mul])
          _ = ∑ i, ‖z (i, j)‖ + ‖t‖ * ∑ i, ‖v (i, j)‖ := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
          _ ≤ M * (1 + ‖t‖) := by nlinarith [norm_nonneg t]
      have hsq : ∑ i, e i ^ 2 ≤ (∑ i, e i) ^ 2 := by
        calc ∑ i, e i ^ 2 = ∑ i, e i * e i := Finset.sum_congr rfl fun i _ => sq (e i)
          _ ≤ ∑ i, e i * ∑ j', e j' := Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left
                (Finset.single_le_sum (fun j' _ => he0 j') (Finset.mem_univ i)) (he0 i)
          _ = (∑ i, e i) ^ 2 := by rw [← Finset.sum_mul, sq]
      calc colNormSq (bwpMat (z + t • v)) j = ∑ i, e i ^ 2 := rfl
        _ ≤ (∑ i, e i) ^ 2 := hsq
        _ ≤ (M * (1 + ‖t‖)) ^ 2 :=
            pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => he0 i) he 2
    have hR : 0 ≤ M * (1 + ‖t‖) := mul_nonneg hM0 (by positivity)
    have h := hH Unit (fun _ => p) (fun _ => a) (fun x => P (x ())) C (M * (1 + ‖t‖))
      (by
        intro x s b hx hb htri
        cases s
        first
          | simp only [Function.update_self]
          | simp only [Function.update_same]
        exact hT (x ()) b (hx ()) hb htri)
      (fun k hk => hC (k ()) (hk ())) hR (fun _ => bwpMat (z + t • v)) (fun _ => hdet)
      (fun _ j => hcol j)
    simp only [Finset.univ_unique, Finset.sum_singleton] at h
    calc ‖P (bwpMat (z + t • v))‖ ≤ C * (M * (1 + ‖t‖)) ^ ∑ i, a i := h
      _ = (C * M ^ (∑ i, a i)) * (1 + ‖t‖) ^ (∑ i, a i) := by rw [mul_pow]; ring
  have hdiff : DifferentiableOn ℂ (fun t => P (bwpMat (z + t • v)))
      {t : ℂ | (bwpMat (z + t • v)).det = 0}ᶜ := by
    have hL : Differentiable ℂ (fun t : ℂ => (fun i j => (z + t • v) (i, j) : Fin p → Fin p → ℂ)) := by
      rw [differentiable_pi]
      intro i
      rw [differentiable_pi]
      intro j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      fun_prop
    have hc : DifferentiableOn ℂ ((fun y : Fin p → Fin p → ℂ => P (Matrix.of y)) ∘
        (fun t : ℂ => (fun i j => (z + t • v) (i, j) : Fin p → Fin p → ℂ)))
        {t : ℂ | (bwpMat (z + t • v)).det = 0}ᶜ :=
      DifferentiableOn.comp hP hL.differentiableOn (fun t ht => ht)
    exact hc
  obtain ⟨Q, hQdeg, hQ⟩ := hO (fun t => P (bwpMat (z + t • v))) _ (C * M ^ (∑ i, a i)) (∑ i, a i) hB
    hdiff hbound
  exact ⟨Q, hQdeg, fun t ht => hQ t ht⟩

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.ExistsDualDerivations
section
namespace ReciprocityTheory.MultiplicativeHeights

namespace DerivationAlgebraicIndependence

open MvPolynomial

section CoeffDer

variable {K Ω σ : Type*} [CommRing K] [CommRing Ω] [Algebra K Ω]

noncomputable def coeffMap (δ : Derivation K Ω Ω) (P : MvPolynomial σ Ω) : MvPolynomial σ Ω :=
  ∑ n ∈ P.support, monomial n (δ (AddMonoidAlgebra.coeff P n))

theorem coeff_coeffMap (δ : Derivation K Ω Ω) (P : MvPolynomial σ Ω) (n : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (coeffMap δ P) n = δ (AddMonoidAlgebra.coeff P n) := by
  classical
  unfold coeffMap
  rw [coeff_sum]
  by_cases h : n ∈ P.support
  · rw [Finset.sum_eq_single n]
    · rw [coeff_monomial, if_pos rfl]
    · intro b _ hb
      rw [coeff_monomial, if_neg hb]
    · intro hn
      exact absurd h hn
  · have h0 : AddMonoidAlgebra.coeff P n = 0 := by
      by_contra hc
      exact h (mem_support_iff.mpr hc)
    rw [h0, map_zero]
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [coeff_monomial, if_neg]
    rintro rfl
    exact h hb

theorem coeffMap_monomial (δ : Derivation K Ω Ω) (n : σ →₀ ℕ) (a : Ω) :
    coeffMap δ (monomial n a) = monomial n (δ a) := by
  classical
  ext m
  rw [coeff_coeffMap, coeff_monomial, coeff_monomial]
  split_ifs <;> simp

theorem coeffMap_add (δ : Derivation K Ω Ω) (P Q : MvPolynomial σ Ω) :
    coeffMap δ (P + Q) = coeffMap δ P + coeffMap δ Q := by
  ext m
  simp only [MvPolynomial.coeff_add, coeff_coeffMap, map_add (f := _)]

theorem coeffMap_smul (δ : Derivation K Ω Ω) (k : K) (P : MvPolynomial σ Ω) :
    coeffMap δ (k • P) = k • coeffMap δ P := by
  ext m
  rw [coeff_coeffMap, coeff_smul, coeff_smul, coeff_coeffMap,
    Derivation.map_smul]

theorem coeffMap_mul (δ : Derivation K Ω Ω) (P Q : MvPolynomial σ Ω) :
    coeffMap δ (P * Q) = P * coeffMap δ Q + Q * coeffMap δ P := by
  induction P using MvPolynomial.induction_on'
  · rename_i u a
    induction Q using MvPolynomial.induction_on'
    · rename_i v b
      rw [monomial_mul, coeffMap_monomial, coeffMap_monomial,
        coeffMap_monomial, monomial_mul, monomial_mul, Derivation.leibniz, smul_eq_mul,
        smul_eq_mul, map_add, add_comm v u]
    · rename_i p q hp hq
      simp only [mul_add, add_mul, coeffMap_add, hp, hq]
      ring
  · rename_i p q hp hq
    simp only [add_mul, mul_add, coeffMap_add, hp, hq]
    ring

noncomputable def coeffDer (δ : Derivation K Ω Ω) :
    Derivation K (MvPolynomial σ Ω) (MvPolynomial σ Ω) :=
  Derivation.mk' { toFun := coeffMap δ, map_add' := coeffMap_add δ, map_smul' := coeffMap_smul δ }
    (fun P Q => by simp only [LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]; exact coeffMap_mul δ P Q)

theorem coeffDer_apply (δ : Derivation K Ω Ω) (P : MvPolynomial σ Ω) :
    coeffDer δ P = coeffMap δ P := rfl

theorem coeffDer_C (δ : Derivation K Ω Ω) (a : Ω) :
    coeffDer (σ := σ) δ (C a) = C (δ a) := by
  simp only [coeffDer_apply, C_apply, coeffMap_monomial]

theorem coeffDer_X (δ : Derivation K Ω Ω) (v : σ) : coeffDer δ (X v : MvPolynomial σ Ω) = 0 := by
  rw [coeffDer_apply]
  show coeffMap δ (monomial (Finsupp.single v 1) 1) = 0
  rw [coeffMap_monomial, Derivation.map_one_eq_zero, map_zero]

end CoeffDer

private theorem exists_linearMap_dual_of_linearIndependent {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V]
    {D : ℕ} (v : Fin D → V) (hli : LinearIndependent Ω v) (a : Fin D) :
    ∃ g : V →ₗ[Ω] Ω, ∀ b, g (v b) = if a = b then 1 else 0 := by
  open Module in
  classical
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Basis.span hli).coord a)
  refine ⟨g, fun b => ?_⟩
  have hmem : v b ∈ Submodule.span Ω (Set.range v) := Submodule.subset_span ⟨b, rfl⟩
  have h1 : g (v b) = (Basis.span hli).coord a ⟨v b, hmem⟩ := LinearMap.congr_fun hg ⟨v b, hmem⟩
  have h2 : (⟨v b, hmem⟩ : Submodule.span Ω (Set.range v)) = Basis.span hli b :=
    Subtype.ext (by rw [Basis.span_apply])
  rw [h1, h2, Basis.coord_apply, Basis.repr_self]
  by_cases h : a = b
  · subst h
    simp
  · simp [h]

theorem exists_dual_derivations {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}
    (x : Fin m → Ω) (J : Fin D → Fin m)
    (hli : LinearIndependent Ω fun a => KaehlerDifferential.D K Ω (x (J a))) :
    ∃ δ : Fin D → Derivation K Ω Ω, ∀ a b, δ a (x (J b)) = if a = b then 1 else 0 := by
  choose g hg using exists_linearMap_dual_of_linearIndependent (fun a => KaehlerDifferential.D K Ω (x (J a))) hli
  exact ⟨fun a => (g a).compDer (KaehlerDifferential.D K Ω), fun a b => hg a b⟩

noncomputable def yPoly {Ω : Type*} [CommRing Ω] {D m : ℕ} (x : Fin m → Ω) (b : Fin D) :
    MvPolynomial (SVars D m) Ω :=
  -∑ k, X (Sum.inr (b.succ, k)) * C (x k)

noncomputable def gFam {Ω : Type*} [CommRing Ω] {D m : ℕ} (x : Fin m → Ω) :
    SVars D m ⊕ Fin D → MvPolynomial (SVars D m) Ω :=
  Sum.elim X (yPoly x)

private theorem coeffDer_linearCombinationPoly_apply {K Ω : Type*} [CommRing K] [CommRing Ω]
    [Algebra K Ω] {D m : ℕ} (δ : Derivation K Ω Ω) (x : Fin m → Ω) (b : Fin D) :
    coeffDer (σ := ReciprocityTheory.MultiplicativeHeights.SVars D m) δ (yPoly x b) =
      -∑ k, X (Sum.inr (b.succ, k)) * C (δ (x k)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [yPoly, map_neg, map_sum, Derivation.leibniz, coeffDer_X,
    coeffDer_C, smul_eq_mul, mul_zero, add_zero]

private theorem restrictScalars_pderiv_apply {K Ω σ : Type*} [CommRing K] [CommRing Ω]
    [Algebra K Ω] (w : σ) (f : MvPolynomial σ Ω) :
    ((pderiv w : Derivation Ω (MvPolynomial σ Ω) (MvPolynomial σ Ω)).restrictScalars K) f =
      pderiv w f := by
  exact congrFun (Derivation.coe_restrictScalars K _) f


set_option maxHeartbeats 800000 in
private theorem det_sum_X_mul_C_ne_zero_of_dual_family {Ω : Type*} [Field Ω] {D m : ℕ} (y : Fin D → Fin m → Ω)
    (J : Fin D → Fin m) (hy : ∀ a b, y a (J b) = if a = b then 1 else 0) :
    (Matrix.of fun a b : Fin D =>
      ∑ k, (X (Sum.inr (b.succ, k)) : MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω) * C (y a k)).det ≠ 0 := by
  classical
  obtain ⟨p, hp⟩ : ∃ p : ReciprocityTheory.MultiplicativeHeights.SVars D m → Ω, ∀ (b : Fin D) (k : Fin m),
      p (Sum.inr (b.succ, k)) = if k = J b then 1 else 0 :=
    ⟨Sum.elim (fun _ => 0)
      (fun q => Fin.cases (motive := fun _ => Ω) 0 (fun b => if q.2 = J b then 1 else 0) q.1),
      fun b k => by simp⟩
  intro h0
  have hmap : (eval p).mapMatrix (Matrix.of fun a b : Fin D =>
      ∑ k, (X (Sum.inr (b.succ, k)) : MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω) * C (y a k)) = 1 := by
    ext a b
    simp [RingHom.mapMatrix_apply, hp, hy, Matrix.one_apply]
  have h1 := RingHom.map_det (eval p) (Matrix.of fun a b : Fin D =>
      ∑ k, (X (Sum.inr (b.succ, k)) : MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω) * C (y a k))
  rw [h0, map_zero, hmap, Matrix.det_one] at h1
  exact zero_ne_one h1


set_option maxHeartbeats 800000 in
theorem gFam_indep {K Ω : Type*} [Field K] [CharZero K] [Field Ω] [Algebra K Ω] {D m : ℕ}
    (x : Fin m → Ω) (J : Fin D → Fin m) (δ : Fin D → Derivation K Ω Ω)
    (hδ : ∀ a b, δ a (x (J b)) = if a = b then 1 else 0) :
    AlgebraicIndependent K (gFam (D := D) x) := by
  classical
  have hz_inl : ∀ w, gFam (D := D) x (Sum.inl w) = X w := fun _ => rfl
  have hz_inr : ∀ b, gFam (D := D) x (Sum.inr b) = yPoly x b :=
    fun _ => rfl
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin D) (Fin D) (MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω),
      N = Matrix.of fun a b : Fin D =>
        ∑ k, (X (Sum.inr (b.succ, k)) : MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω) * C (δ a (x k)) :=
    ⟨_, rfl⟩
  have hNe : ∀ a b, N a b =
      ∑ k, (X (Sum.inr (b.succ, k)) : MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω) * C (δ a (x k)) := by
    intro a b
    rw [hN]
    rfl
  have hcd : ∀ a b, coeffDer (σ := ReciprocityTheory.MultiplicativeHeights.SVars D m) (δ a) (yPoly x b) =
      -N a b := by
    intro a b
    rw [hNe, coeffDer_linearCombinationPoly_apply]
  have hdet : N.det ≠ 0 := by
    rw [hN]
    exact det_sum_X_mul_C_ne_zero_of_dual_family (fun a k => δ a (x k)) J hδ
  refine algebraicIndependent_of_derivations (gFam (D := D) x)
    (Sum.elim (fun w : ReciprocityTheory.MultiplicativeHeights.SVars D m => (pderiv w : Derivation Ω (MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω)
        (MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω)).restrictScalars K)
      (fun a : Fin D => coeffDer (σ := ReciprocityTheory.MultiplicativeHeights.SVars D m) (δ a))) ?_
  intro c hc
  have hmv : Matrix.mulVec N (fun b => c (Sum.inr b)) = 0 := by
    funext a
    have h1 := hc (Sum.inr a)
    simp only [Sum.elim_inr, Fintype.sum_sum_type, hz_inl, hz_inr, coeffDer_X, mul_zero,
      Finset.sum_const_zero, zero_add, hcd, mul_neg, Finset.sum_neg_distrib, neg_eq_zero] at h1
    show ∑ b, N a b * c (Sum.inr b) = 0
    exact (Finset.sum_congr rfl fun b _ => mul_comm (N a b) (c (Sum.inr b))).trans h1
  have hinr : ∀ b, c (Sum.inr b) = 0 := fun b =>
    congr_fun (Matrix.eq_zero_of_mulVec_eq_zero hdet hmv) b
  intro i
  rcases i with w | b
  · have h2 := hc (Sum.inl w)
    rw [Fintype.sum_sum_type] at h2
    simp only [Sum.elim_inl, hinr, zero_mul, Finset.sum_const_zero, add_zero,
      restrictScalars_pderiv_apply, hz_inl] at h2
    rw [Finset.sum_eq_single w] at h2
    · rw [pderiv_X_self, mul_one] at h2
      exact h2
    · intro w' _ hw'
      rw [pderiv_X_of_ne hw', mul_zero]
    · intro h
      exact absurd (Finset.mem_univ w) h
  · exact hinr b

def eIdx (D m : ℕ) (p : Fin (D + 1) × Fin (m + 1)) : SVars D m ⊕ Fin D :=
  Fin.cases (motive := fun _ => SVars D m ⊕ Fin D)
    (Fin.cases (motive := fun _ => SVars D m ⊕ Fin D) (Sum.inl (Sum.inl ())) Sum.inr p.1)
    (fun j => Sum.inl (Sum.inr (p.1, j))) p.2

theorem eIdx_injective (D m : ℕ) : Function.Injective (eIdx D m) := by
  rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
  induction j₁ using Fin.cases <;> induction j₂ using Fin.cases <;>
    induction i₁ using Fin.cases <;> induction i₂ using Fin.cases <;>
    simp_all [eIdx]

theorem sImage_eq {Ω : Type} [Field Ω] {D m : ℕ} (x : Fin m → Ω) (p : Fin (D + 1) × Fin (m + 1)) :
    sImage (D := D) x p =
      algebraMap (MvPolynomial (SVars D m) Ω) (SField Ω D m) (gFam x (eIdx D m p)) := by
  rcases p with ⟨i, j⟩
  induction j using Fin.cases <;> induction i using Fin.cases <;>
    simp [ReciprocityTheory.MultiplicativeHeights.sImage, eIdx, gFam, yPoly]

end DerivationAlgebraicIndependence

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.GaussValExists
section
namespace ReciprocityTheory.MultiplicativeHeights

open MvPolynomial

noncomputable def gaussRed {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (V : ValuationSubring U) (p : MvPolynomial σ Ω)
    (hc : ∀ α, p.coeff α ∈ V.comap (algebraMap Ω U)) :
    MvPolynomial σ (IsLocalRing.ResidueField (V.comap (algebraMap Ω U))) :=
  ∑ α ∈ p.support, monomial α (IsLocalRing.residue _ ⟨p.coeff α, hc α⟩)

theorem gaussRed_coeff {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (V : ValuationSubring U) (p : MvPolynomial σ Ω)
    (hc : ∀ α, p.coeff α ∈ V.comap (algebraMap Ω U)) (α : σ →₀ ℕ) :
    (gaussRed V p hc).coeff α = IsLocalRing.residue _ ⟨p.coeff α, hc α⟩ := by
  classical
  unfold gaussRed
  rw [MvPolynomial.coeff_sum]
  by_cases h : α ∈ p.support
  · rw [Finset.sum_eq_single α]
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
    · intro b _ hb
      rw [MvPolynomial.coeff_monomial, if_neg hb]
    · intro h'
      exact absurd h h'
  · have h0 : p.coeff α = 0 := by simpa [MvPolynomial.mem_support_iff] using h
    have hz : (⟨p.coeff α, hc α⟩ : V.comap (algebraMap Ω U)) = 0 := Subtype.ext h0
    rw [Finset.sum_eq_zero, hz, map_zero]
    intro b hb
    rw [MvPolynomial.coeff_monomial, if_neg]
    rintro rfl
    exact h hb

theorem gaussRed_eval {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (t : σ → U) (V : ValuationSubring U) (ht : ∀ s, t s ∈ V) (p : MvPolynomial σ Ω)
    (hc : ∀ α, p.coeff α ∈ V.comap (algebraMap Ω U)) :
    letI := residueAlgebra V (algebraMap Ω U)
    ∃ h : aeval t p ∈ V, IsLocalRing.residue V ⟨aeval t p, h⟩ =
      aeval (fun s => IsLocalRing.residue V ⟨t s, ht s⟩) (gaussRed V p hc) := by
  try dsimp only
  letI := residueAlgebra V (algebraMap Ω U)
  classical
  obtain ⟨y, hydef⟩ : ∃ y : V, y = ∑ α ∈ p.support,
      comapInclusion V (algebraMap Ω U) ⟨p.coeff α, hc α⟩ *
        ∏ s ∈ α.support, (⟨t s, ht s⟩ : V) ^ α s := ⟨_, rfl⟩
  have hy : (y : U) = aeval t p := by
    change V.subtype y = _
    rw [hydef, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_prod, map_pow]
    rfl
  have hmem : aeval t p ∈ V := by
    rw [← hy]
    exact y.2
  refine ⟨hmem, ?_⟩
  have hyy : (⟨aeval t p, hmem⟩ : V) = y := Subtype.ext hy.symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hyy, hydef, map_sum]
  unfold gaussRed
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.aeval_monomial]
  simp only [map_mul, map_prod, map_pow]
  congr 1

end ReciprocityTheory.MultiplicativeHeights
end

