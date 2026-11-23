module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTensorOrderAlgEquivMatrixCharZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0098

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitEqPositiveSquaresTimesSelfAdjoint
section
open Matrix Polynomial

namespace GlobalTheory.Desc.SqLin

section Alg
variable {A : Type} [CommRing A] [Algebra ℚ A] [Module.Finite ℚ A]

theorem exists_casimir (τ : A →ₗ[ℚ] ℚ) (y : A) (hy : ∀ a, a ≠ 0 → 0 < τ (y * a ^ 2)) :
    ∃ (r : ℕ) (c : Fin r → ℚ) (e : Fin r → A), (∀ i, 0 < c i) ∧
      (∀ a, (∀ i, e i * a = 0) → a = 0) ∧
      ∀ a, τ (y * (∑ i, c i • e i ^ 2) * a) = LinearMap.trace ℚ A (LinearMap.mulLeft ℚ a) := by
  classical
  let β : LinearMap.BilinForm ℚ A := ((LinearMap.mul ℚ A).compr₂ (τ ∘ₗ LinearMap.mulLeft ℚ y))
  have hβ : ∀ a b, β a b = τ (y * (a * b)) := fun a b => rfl
  have hs : β.IsSymm := ⟨fun a b => by simp only [hβ, mul_comm a b, RingHom.id_apply]⟩
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (K := ℚ) (V := A) (B := β) ⟨hs.eq⟩
  have hpos : ∀ i, 0 < β (v i) (v i) := fun i => by
    rw [hβ, ← sq]; exact hy _ (v.ne_zero i)
  have hco : ∀ a i, β a (v i) = v.repr a i * β (v i) (v i) := by
    intro a i
    conv_lhs => rw [← v.sum_repr a]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      have : β (v j) (v i) = 0 := hv hj
      simp [this]
    · simp
  refine ⟨_, fun i => (β (v i) (v i))⁻¹, v, fun i => inv_pos.2 (hpos i), ?_, ?_⟩
  · intro a ha
    have : (1 : A) * a = 0 := by
      rw [← v.sum_repr 1, Finset.sum_mul]
      simp [ha]
    simpa using this
  · intro a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.trace_eq_matrix_trace ℚ v, Matrix.trace, Finset.mul_sum, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := hco (a * v i) i
    rw [hβ] at h1
    have h2 : y * (β (v i) (v i))⁻¹ • v i ^ 2 * a = (β (v i) (v i))⁻¹ • (y * (a * v i * v i)) := by
      rw [mul_smul_comm, smul_mul_assoc]; congr 1; ring
    rw [h2, map_smul, h1, smul_eq_mul, Matrix.diag_apply, LinearMap.toMatrix_apply]
    have := (hpos i).ne'
    simp only [LinearMap.mulLeft_apply]
    field_simp

theorem exists_inv (y : A) (hy : ∀ a, y * a = 0 → a = 0) : ∃ u, y * u = 1 := by
  have hinj : Function.Injective (LinearMap.mulLeft ℚ y) := by
    rw [injective_iff_map_eq_zero]; exact hy
  exact (LinearMap.injective_iff_surjective.1 hinj) 1

theorem exists_sum_sq (τ : A →ₗ[ℚ] ℚ) (h1 : ∀ a, a ≠ 0 → 0 < τ (a ^ 2)) (y : A)
    (hy : ∀ a, a ≠ 0 → 0 < τ (y * a ^ 2)) :
    ∃ (r : ℕ) (c : Fin r → ℚ) (e : Fin r → A), (∀ i, 0 < c i) ∧ y = ∑ i, c i • e i ^ 2 := by
  classical
  obtain ⟨r, c, e, hc, he, hK⟩ := exists_casimir τ y hy
  obtain ⟨s, d, f, hd, -, hL⟩ := exists_casimir τ 1 (by simpa using h1)
  have hnn : ∀ a, 0 ≤ τ (a ^ 2) := fun a => by
    by_cases h : a = 0
    · simp [h]
    · exact (h1 a h).le
  have hz : ∀ a, τ (a ^ 2) = 0 → a = 0 := fun a h => by
    by_contra h'
    exact (h1 a h').ne' h
  set K := ∑ i, c i • e i ^ 2 with hKd
  set L := ∑ i, d i • f i ^ 2 with hLd
  have hKL : y * K = L := by
    have := hK (y * K - L)
    rw [← hL, one_mul] at this
    refine sub_eq_zero.1 (hz _ ?_)
    rw [sq, sub_mul, map_sub, this, sub_self]
  obtain ⟨u, hu⟩ := exists_inv K (by
    intro a ha
    refine he a fun i => hz _ ?_
    have h0 : ∑ i, c i * τ ((e i * a) ^ 2) = 0 := by
      have : τ (K * a * a) = 0 := by rw [ha]; simp
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← this, hKd, Finset.sum_mul, Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_mul_assoc, smul_mul_assoc, map_smul, smul_eq_mul]
      congr 2; ring
    rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hc i).le (hnn _)] at h0
    exact (mul_eq_zero.1 (h0 i (Finset.mem_univ _))).resolve_left (hc i).ne')
  refine ⟨r * s, fun k => c (finProdFinEquiv.symm k).1 * d (finProdFinEquiv.symm k).2,
    fun k => e (finProdFinEquiv.symm k).1 * f (finProdFinEquiv.symm k).2 * u,
    fun k => mul_pos (hc _) (hd _), ?_⟩
  rw [Equiv.sum_comp finProdFinEquiv.symm
    (fun k : Fin r × Fin s => (c k.1 * d k.2) • (e k.1 * f k.2 * u) ^ 2), Fintype.sum_prod_type]
  have : y = K * L * u ^ 2 := by
    rw [← hKL]; linear_combination (-y * (K * u + 1)) * hu
  rw [this, hKd, hLd, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Algebra.smul_def, map_mul]
  ring

end Alg


open scoped MatrixOrder in
theorem exists_diag {n : ℕ} (T B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosDef)
    (hT : (B * T).PosDef) :
    ∃ (P Q : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ), P * Q = 1 ∧ Q * P = 1 ∧ (∀ i, 0 < d i) ∧
      T = P * diagonal d * Q := by
  obtain ⟨C, hC, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hB.isStrictlyPositive
  obtain ⟨C, rfl⟩ := hC
  have hH : (star (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ) * (star (C : Matrix (Fin n) (Fin n) ℝ) * C * T) *
      (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ)).PosDef :=
    (Matrix.IsUnit.posDef_star_left_conjugate_iff (Units.isUnit _)).2 hT
  have e : star (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ) * (star (C : Matrix (Fin n) (Fin n) ℝ) * C * T) *
      (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ) = C * T * (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ) := by
    rw [mul_assoc (star (C : Matrix (Fin n) (Fin n) ℝ)), ← mul_assoc (star _), ← star_mul,
      Units.mul_inv, star_one, one_mul]
  rw [e] at hH
  have hs := hH.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  set U := hH.1.eigenvectorUnitary
  have h1 : (U : Matrix (Fin n) (Fin n) ℝ) * star (U : Matrix (Fin n) (Fin n) ℝ) = 1 := U.2.2
  have h2 : star (U : Matrix (Fin n) (Fin n) ℝ) * (U : Matrix (Fin n) (Fin n) ℝ) = 1 := U.2.1
  refine ⟨(↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ) * U, star (U : Matrix (Fin n) (Fin n) ℝ) * C,
    hH.1.eigenvalues, ?_, ?_, hH.eigenvalues_pos, ?_⟩
  · rw [mul_assoc, ← mul_assoc (U : Matrix (Fin n) (Fin n) ℝ), h1, one_mul, Units.inv_mul]
  · rw [mul_assoc, ← mul_assoc (C : Matrix (Fin n) (Fin n) ℝ), Units.mul_inv, one_mul, h2]
  · have : T = (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ) * (C * T * (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ)) * C := by
      simp [mul_assoc]
    refine this.trans ?_
    conv_lhs => rw [hs]
    simp [mul_assoc]

theorem aeval_map_eq {n : ℕ} (T : Matrix (Fin n) (Fin n) ℚ) (P Q : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (h1 : P * Q = 1) (h2 : Q * P = 1)
    (hT : T.map (Rat.cast : ℚ → ℝ) = P * diagonal d * Q) (p : ℚ[X]) :
    (aeval T p).map (Rat.cast : ℚ → ℝ) = P * diagonal (fun k => aeval (d k) p) * Q := by
  have hm : ∀ M : Matrix (Fin n) (Fin n) ℚ,
      M.map (Rat.cast : ℚ → ℝ) = (Rat.castHom ℝ).mapMatrix M := fun M => rfl
  induction p using Polynomial.induction_on with
  | C a =>
    have : (diagonal fun _ : Fin n => (a : ℝ)) = (a : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j; by_cases h : i = j <;> simp [h, one_apply]
    simp only [aeval_C, eq_ratCast, this, Matrix.mul_smul, Matrix.smul_mul, mul_one, h1]
    ext i j; by_cases h : i = j <;> simp [h, one_apply, Matrix.algebraMap_matrix_apply]
  | add p q hp hq =>
    simp only [map_add (f := _)]
    rw [hm, map_add (f := _), ← hm, ← hm, hp, hq, ← diagonal_add, mul_add, add_mul]
  | monomial m a h =>
    rw [pow_succ, ← mul_assoc, map_mul, hm, map_mul, ← hm, ← hm, h, aeval_X, hT]
    have : ∀ D E : Matrix (Fin n) (Fin n) ℝ, P * D * Q * (P * E * Q) = P * (D * E) * Q := by
      intro D E
      calc P * D * Q * (P * E * Q) = P * D * (Q * P) * E * Q := by simp only [mul_assoc]
        _ = _ := by rw [h2]; simp only [mul_assoc, one_mul]
    rw [this, diagonal_mul_diagonal]
    simp [mul_assoc]

theorem main (n : ℕ) (Tm : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.PosDef) (hT : (B * Tm.map (Rat.cast : ℚ → ℝ)).PosDef) :
    ∃ (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ), 0 < c₀ ∧ (∀ i, 0 < c i) ∧
      (1 : Matrix (Fin n) (Fin n) ℚ) =
        c₀ • Tm + ∑ i, c i • ((Polynomial.aeval Tm (p i)) ^ 2 * Tm) := by
  classical
  obtain ⟨P, Q, d, h1, h2, hd, hD⟩ := exists_diag _ B hB hT
  have key := aeval_map_eq Tm P Q d h1 h2 hD
  let f : ℚ[X] →ₐ[ℚ] Matrix (Fin n) (Fin n) ℚ := aeval Tm
  let ι := Ideal.kerLiftAlg f
  have hι : Function.Injective ι := Ideal.kerLiftAlg_injective f
  have hιm : ∀ p, ι (Ideal.Quotient.mk _ p) = aeval Tm p := Ideal.kerLiftAlg_mk f
  haveI : Module.Finite ℚ (ℚ[X] ⧸ RingHom.ker f) := Module.Finite.of_injective ι.toLinearMap hι
  let τ : (ℚ[X] ⧸ RingHom.ker f) →ₗ[ℚ] ℚ := Matrix.traceLinearMap (Fin n) ℚ ℚ ∘ₗ ι.toLinearMap
  have hτ : ∀ p, ((τ (Ideal.Quotient.mk _ p) : ℚ) : ℝ) = ∑ k, aeval (d k) p := by
    intro p
    have : τ (Ideal.Quotient.mk _ p) = (aeval Tm p).trace := by rw [← hιm]; rfl
    have h3 : (((aeval Tm p).trace : ℚ) : ℝ) = ((aeval Tm p).map (Rat.cast : ℚ → ℝ)).trace := by
      simp [Matrix.trace]
    rw [this, h3, key, trace_mul_comm, ← mul_assoc, h2, one_mul, trace_diagonal]
  have hpos : ∀ q : ℚ[X], (∀ k, 0 < aeval (d k) q) → ∀ a : ℚ[X] ⧸ RingHom.ker f, a ≠ 0 →
      0 < τ (Ideal.Quotient.mk _ q * a ^ 2) := by
    intro q hq a ha
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [← map_pow, ← map_mul, ← Rat.cast_pos (K := ℝ), hτ]
    have : ∃ k, aeval (d k) p ≠ 0 := by
      by_contra h
      push Not at h
      apply ha
      apply hι
      rw [hιm, map_zero]
      have := key p
      simp only [h, diagonal_zero, mul_zero, zero_mul] at this
      ext i j
      simpa using congrFun (congrFun this i) j
    obtain ⟨k, hk⟩ := this
    refine Finset.sum_pos' (fun i _ => ?_) ⟨k, Finset.mem_univ _, ?_⟩
    · rw [map_mul, map_pow]; exact mul_nonneg (hq i).le (sq_nonneg _)
    · rw [map_mul, map_pow]; exact mul_pos (hq k) (by positivity)
  obtain ⟨N, hN⟩ := exists_rat_gt (∑ k, d k)
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (Finset.sum_nonneg fun i _ => (hd i).le) hN
  have hN0' : 0 < N := by exact_mod_cast hN0
  have hNk : ∀ k, d k < N := fun k =>
    lt_of_le_of_lt (Finset.single_le_sum (fun i _ => (hd i).le) (Finset.mem_univ k)) hN
  set x : ℚ[X] ⧸ RingHom.ker f := Ideal.Quotient.mk _ X with hx
  obtain ⟨u, hu⟩ := exists_inv x (by
    intro a ha
    by_contra h
    have := hpos X (by simpa using hd) a h
    rw [sq, ← mul_assoc, ← hx, ha] at this
    simp at this)
  obtain ⟨r, c, e, hc, he⟩ := exists_sum_sq τ (by simpa using hpos 1 (by simp)) _
    (hpos ((C N - X) * X) (fun k => by
      simpa using mul_pos (sub_pos.2 (hNk k)) (hd k)))
  choose p hp using fun i => Ideal.Quotient.mk_surjective (e i * u)
  refine ⟨N⁻¹, r, fun i => N⁻¹ * c i, p, inv_pos.2 hN0', fun i => mul_pos (inv_pos.2 hN0') (hc i), ?_⟩
  have hmain : (1 : ℚ[X] ⧸ RingHom.ker f) =
      N⁻¹ • x + ∑ i, (N⁻¹ * c i) • ((Ideal.Quotient.mk _ (p i)) ^ 2 * x) := by
    have e1 : ∑ i, (N⁻¹ * c i) • ((Ideal.Quotient.mk (RingHom.ker f) (p i)) ^ 2 * x) =
        N⁻¹ • ((∑ i, c i • e i ^ 2) * (u ^ 2 * x)) := by
      rw [Finset.sum_mul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hp, mul_smul, smul_mul_assoc, mul_pow, mul_assoc]
    have e2 : Ideal.Quotient.mk (RingHom.ker f) (C N) = algebraMap ℚ _ N := rfl
    rw [e1, ← he, map_mul, map_sub, e2, ← hx, ← smul_add]
    have e3 : x + (algebraMap ℚ _ N - x) * x * (u ^ 2 * x) = algebraMap ℚ _ N := by
      linear_combination ((algebraMap ℚ _ N - x) * (x * u + 1)) * hu
    rw [e3, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hN0'.ne', map_one]
  have := congrArg ι hmain
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_one, map_add (f := _), map_smul, map_sum, map_mul, map_pow, hx, hιm, aeval_X] using this

end GlobalTheory.Desc.SqLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitLiftClosedSubschemeNearFibre
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem unit_lift_near_fibre : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsFinite p → IsClosedImmersion i → ∀ (W : X.Opens) (x : X), x ∈ W → ∀ u : Γ(Z', i' ⁻¹ᵁ (p ⁻¹ᵁ W))ˣ, ∃ (W' : X.Opens) (u' : Γ(X', p ⁻¹ᵁ W')ˣ), W' ≤ W ∧ x ∈ W' ∧ ∀ z : Z', p (i' z) ∈ W' → gm i' z (p ⁻¹ᵁ W') u' = gm (𝟙 Z') z (i' ⁻¹ᵁ (p ⁻¹ᵁ W)) u := by
  intro X X' Z Z' p i i' p' h hp hi W x hx u
  have hi' : IsClosedImmersion i' := MorphismProperty.of_isPullback h.flip hi
  have hw : ∀ z : Z', p (i' z) = i (p' z) := fun z => by
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
  by_cases hxr : x ∈ Set.range i
  swap
  · refine ⟨W ⊓ ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩, 1, inf_le_left, ⟨hx, hxr⟩,
      fun z hz => ?_⟩
    exact absurd ⟨p' z, (hw z).symm⟩ hz.2
  obtain ⟨z0, hz0⟩ := hxr
  obtain ⟨W₀, hW₀, hxW₀, hW₀W⟩ := exists_isAffineOpen_mem_and_subset hx
  have hle0 : W₀ ≤ W := hW₀W
  have hA : IsAffineOpen (p ⁻¹ᵁ W₀) := IsAffineHom.isAffine_preimage _ hW₀
  let u0 : Γ(Z', i' ⁻¹ᵁ (p ⁻¹ᵁ W₀)) :=
    (Z'.presheaf.map (homOfLE (i'.preimage_mono (p.preimage_mono hle0))).op).hom u.val
  have hu0 : IsUnit u0 := (Units.isUnit u).map _
  obtain ⟨t, ht⟩ := Scheme.Hom.app_surjective i' (p ⁻¹ᵁ W₀) hA u0
  have hC : IsClosed ((X'.basicOpen t : Set X')ᶜ) := (X'.basicOpen t).isOpen.isClosed_compl
  let W' : X.Opens := W₀ ⊓ ⟨(p '' (X'.basicOpen t : Set X')ᶜ)ᶜ, (p.isClosedMap _ hC).isOpen_compl⟩
  have hsub : p ⁻¹ᵁ W' ≤ X'.basicOpen t := fun y hy => by
    by_contra hc
    exact hy.2 ⟨y, hc, rfl⟩
  have hx' : x ∈ W' := by
    refine ⟨hxW₀, ?_⟩
    rintro ⟨y, hyC, hy⟩
    obtain ⟨z', hz'1, -⟩ := Scheme.exists_preimage_of_isPullback h y z0 (hy.trans hz0.symm)
    apply hyC
    have hz'W : z' ∈ i' ⁻¹ᵁ (p ⁻¹ᵁ W₀) := by
      show p (i' z') ∈ W₀
      rw [hz'1, hy]; exact hxW₀
    have : z' ∈ i' ⁻¹ᵁ X'.basicOpen t := by
      rw [Scheme.preimage_basicOpen, ht, Scheme.basicOpen_of_isUnit _ hu0]
      exact hz'W
    rw [← hz'1]; exact this
  have hle' : p ⁻¹ᵁ W' ≤ p ⁻¹ᵁ W₀ := hsub.trans (X'.basicOpen_le t)
  have hunit : IsUnit ((X'.presheaf.map (homOfLE hle').op).hom t) := by
    have := (X'.toRingedSpace.isUnit_res_basicOpen t).map (X'.presheaf.map (homOfLE hsub).op).hom
    convert this using 1
    change _ = (X'.presheaf.map (homOfLE (X'.basicOpen_le t)).op ≫ X'.presheaf.map (homOfLE hsub).op).hom t
    rw [← Functor.map_comp]
    rfl
  refine ⟨W', hunit.unit, inf_le_left.trans hle0, hx', fun z hz => ?_⟩
  have hle2 : i' ⁻¹ᵁ (p ⁻¹ᵁ W') ≤ i' ⁻¹ᵁ (p ⁻¹ᵁ W) :=
    i'.preimage_mono (p.preimage_mono (inf_le_left.trans hle0))
  rw [← gm_id_pull i' z (p ⁻¹ᵁ W') hz, ← gm_res (𝟙 Z') z hle2 hz]
  congr 1
  apply Units.ext
  show (i'.app (p ⁻¹ᵁ W')).hom ((X'.presheaf.map (homOfLE hle').op).hom t) =
    (Z'.presheaf.map (homOfLE hle2).op).hom u.val
  have e := congrArg (fun φ => φ.hom t) (i'.naturality (homOfLE hle').op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [e, ht]
  show (Z'.presheaf.map _).hom ((Z'.presheaf.map _).hom u.val) = _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end GlobalTheory.Pinch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitRatioLocalGeneratorsCommonPullback
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

theorem commGroup_mul_eq_mul_mul_div {G : Type*} [CommGroup G] (g h w b a : G) :
    g * b * (g * h⁻¹ * w * (h * a))⁻¹ = b * (w * a)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem comm_aux₂ {G : Type*} [CommGroup G] (w b a : G) : b = w * (b * (w * a)⁻¹ * a) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem locGen_gm {Y T : Scheme.{0}} {L : LB Y} {V : Y.Opens} {a : ∀ k, Γ(Y, V ⊓ L.U k)ˣ} (h : LocGen L V a)
    (f : T ⟶ Y) (t : T) (k k' : L.ι) (hv : f t ∈ V) (hk : f t ∈ L.U k) (hk' : f t ∈ L.U k') :
    gm f t (V ⊓ L.U k) (a k) = gm f t (L.U k ⊓ L.U k') (L.g k k') * gm f t (V ⊓ L.U k') (a k') := by
  have e : res (inf_le_left : V ⊓ L.U k ⊓ L.U k' ≤ V ⊓ L.U k) (a k) =
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : V ⊓ L.U k ⊓ L.U k' ≤ L.U k ⊓ L.U k') (L.g k k') *
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : V ⊓ L.U k ⊓ L.U k' ≤ V ⊓ L.U k') (a k') := by
    apply unit_ext
    intro y hy
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy]
    exact h y k k' hy.1.1 hy.1.2 hy.2
  have hm : f t ∈ V ⊓ L.U k ⊓ L.U k' := ⟨⟨hv, hk⟩, hk'⟩
  have := congrArg (gm f t (V ⊓ L.U k ⊓ L.U k')) e
  rwa [map_mul, gm_res _ _ _ hm, gm_res _ _ _ hm, gm_res _ _ _ hm] at this

theorem iso_gm {X' Z Z' : Scheme.{0}} {i' : Z' ⟶ X'} {p' : Z' ⟶ Z} {L' : LB X'} {N : LB Z}
    {w : LB.Iso (L'.pull i') (N.pull p')} (hw : w.IsGen) (x : Z') (k k' : L'.ι) (l l' : N.ι)
    (hk : i' x ∈ L'.U k) (hk' : i' x ∈ L'.U k') (hl : p' x ∈ N.U l) (hl' : p' x ∈ N.U l') :
    gm (𝟙 Z') x ((N.pull p').U (fun _ ↦ l) ⊓ (L'.pull i').U (fun _ ↦ k)) (w.s (fun _ ↦ l, fun _ ↦ k)) =
      gm p' x (N.U l ⊓ N.U l') (N.g l l') * (gm i' x (L'.U k ⊓ L'.U k') (L'.g k k'))⁻¹ *
        gm (𝟙 Z') x ((N.pull p').U (fun _ ↦ l') ⊓ (L'.pull i').U (fun _ ↦ k')) (w.s (fun _ ↦ l', fun _ ↦ k')) := by
  have hp : x ∈ (N.pull p').U (fun _ ↦ l) ⊓ (L'.pull i').U (fun _ ↦ k) := ⟨mem_pull.2 hl, mem_pull.2 hk⟩
  have hq : x ∈ (N.pull p').U (fun _ ↦ l') ⊓ (L'.pull i').U (fun _ ↦ k') := ⟨mem_pull.2 hl', mem_pull.2 hk'⟩
  have e := (isGen_iff_germ w).1 hw x (fun _ ↦ l, fun _ ↦ k) (fun _ ↦ l', fun _ ↦ k') hp hq
  have d := gm_div' (N.pull p') (L'.pull i') (𝟙 Z') x (fun _ ↦ l, fun _ ↦ k) (fun _ ↦ l', fun _ ↦ k') hp hq
  have g1 := gm_pull_g N p' (𝟙 Z') x (fun _ ↦ l) (fun _ ↦ l') hp.1 hq.1
  have g2 := gm_pull_g L' i' (𝟙 Z') x (fun _ ↦ k) (fun _ ↦ k') hp.2 hq.2
  rw [Category.id_comp] at g1 g2
  rw [d, g1, g2] at e
  exact e

theorem exists_ratio_unit : ∀ (X' Z Z' : Scheme.{0}) (i' : Z' ⟶ X') (p' : Z' ⟶ Z) (L' : LB X') (N : LB Z), L'.IsLB → N.IsLB → ∀ (w : LB.Iso (L'.pull i') (N.pull p')), w.IsGen → ∀ (V' : X'.Opens) (V : Z.Opens) (a : ∀ k, Γ(X', V' ⊓ L'.U k)ˣ) (b : ∀ l, Γ(Z, V ⊓ N.U l)ˣ), GlobalTheory.Pinch.LocGen L' V' a → GlobalTheory.Pinch.LocGen N V b → ∀ O : Z'.Opens, O ≤ i' ⁻¹ᵁ V' → O ≤ p' ⁻¹ᵁ V → ∃ u : Γ(Z', O)ˣ, ∀ (z : Z') (k : L'.ι) (l : N.ι), z ∈ O → i' z ∈ L'.U k → p' z ∈ N.U l → gm p' z (V ⊓ N.U l) (b l) = gm (𝟙 Z') z ((N.pull p').U (fun _ ↦ l) ⊓ (L'.pull i').U (fun _ ↦ k)) (w.s (fun _ ↦ l, fun _ ↦ k)) * (gm (𝟙 Z') z O u * gm i' z (V' ⊓ L'.U k) (a k)) := by
  intro X' Z Z' i' p' L' N hL' hN w hw V' V a b ha hb O hO hO'
  let W : L'.ι × N.ι → Z'.Opens := fun q ↦ O ⊓ (i' ⁻¹ᵁ (V' ⊓ L'.U q.1) ⊓ p' ⁻¹ᵁ (V ⊓ N.U q.2))
  have hW : ∀ q, W q ≤ O := fun q ↦ inf_le_left
  have hWw : ∀ q, W q ≤ (N.pull p').U (fun _ ↦ q.2) ⊓ (L'.pull i').U (fun _ ↦ q.1) := fun q x hx ↦
    ⟨mem_pull.2 hx.2.2.2, mem_pull.2 hx.2.1.2⟩
  have hWb : ∀ q, W q ≤ p' ⁻¹ᵁ (V ⊓ N.U q.2) := fun q x hx ↦ hx.2.2
  have hWa : ∀ q, W q ≤ i' ⁻¹ᵁ (V' ⊓ L'.U q.1) := fun q x hx ↦ hx.2.1
  let u : ∀ q, Γ(Z', W q)ˣ := fun q ↦ res (hWb q) (pullU p' _ (b q.2)) *
    (res (hWw q) (w.s (fun _ ↦ q.2, fun _ ↦ q.1)) * res (hWa q) (pullU i' _ (a q.1)))⁻¹
  have gu : ∀ q, ∀ x ∈ W q, gm (𝟙 Z') x (W q) (u q) = gm p' x _ (b q.2) *
      (gm (𝟙 Z') x ((N.pull p').U (fun _ ↦ q.2) ⊓ (L'.pull i').U (fun _ ↦ q.1)) (w.s (fun _ ↦ q.2, fun _ ↦ q.1)) *
        gm i' x _ (a q.1))⁻¹ := by
    intro q x hx
    simp only [u, map_mul, map_inv]
    rw [gm_rp₁ p' x _ _ (hWb q) hx, gm_rp₁ i' x _ _ (hWa q) hx]
    exact congrArg (fun t ↦ _ * (t * _)⁻¹) (gm_res (𝟙 Z') x (hWw q) hx _)
  have cover : O ≤ iSup W := by
    intro x hx
    obtain ⟨k, hk⟩ := exists_chart hL' (i' x)
    obtain ⟨l, hl⟩ := exists_chart hN (p' x)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(k, l), hx, ⟨hO hx, hk⟩, ⟨hO' hx, hl⟩⟩
  obtain ⟨s, hs⟩ := glue_unit O W hW cover u (by
    rintro ⟨k, l⟩ ⟨k', l'⟩ x hx
    rw [gu _ x hx.1, gu _ x hx.2]
    have hx1 := hx.1
    have hx2 := hx.2
    rw [locGen_gm hb p' x l l' hx1.2.2.1 hx1.2.2.2 hx2.2.2.2, locGen_gm ha i' x k k' hx1.2.1.1 hx1.2.1.2 hx2.2.1.2,
      iso_gm hw x k k' l l' hx1.2.1.2 hx2.2.1.2 hx1.2.2.2 hx2.2.2.2]
    exact commGroup_mul_eq_mul_mul_div _ _ _ _ _)
  refine ⟨s, fun z k l hz hk hl ↦ ?_⟩
  have hzW : z ∈ W (k, l) := ⟨hz, ⟨hO hz, hk⟩, ⟨hO' hz, hl⟩⟩
  have e := gu (k, l) z hzW
  rw [← hs (k, l), gm_res _ z _ hzW] at e
  rw [e]
  exact comm_aux₂ _ _ _

end GlobalTheory.Pinch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVertOfMem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem exists_vert_of_mem (S : Type) [CommRing S] [IsDomain S] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Sp S) [IsDominant p] (f : S) (hf : f ≠ 0) (hx : ∃ x : X, f ∈ (p x).asIdeal) : ∃ z : X, Vert p f z := by
  obtain ⟨x, hfx⟩ := hx
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨x, hx⟩⟩
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hU.fromSpec ≫ p)
  have key : ∀ q : PrimeSpectrum Γ(X, U), f ∈ (p (hU.fromSpec q)).asIdeal ↔ φ.hom f ∈ q.asIdeal := by
    intro q
    have h : p (hU.fromSpec q) = (Spec.map φ) q := by
      rw [hφ]; rfl
    rw [h]; rfl
  have key' : ∀ y : U, f ∈ (p y.1).asIdeal ↔ φ.hom f ∈ (hU.primeIdealOf y).asIdeal := by
    intro y
    rw [← key, hU.fromSpec_primeIdealOf]
  have ha : φ.hom f ≠ 0 := by
    intro h0
    have hO : IsOpen ((PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum S)) : Set (PrimeSpectrum S)) :=
      (PrimeSpectrum.basicOpen f).isOpen
    have hne : ((PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum S)) : Set (PrimeSpectrum S)).Nonempty :=
      ⟨⟨⊥, Ideal.isPrime_bot⟩, by simpa using hf⟩
    obtain ⟨y, hy⟩ := p.denseRange.exists_mem_open hO hne
    obtain ⟨w, hwU, hw⟩ := nonempty_preirreducible_inter U.isOpen (hO.preimage p.continuous) ⟨x, hx⟩ ⟨y, hy⟩
    have : f ∈ (p w).asIdeal := (key' ⟨w, hwU⟩).2 (h0 ▸ Ideal.zero_mem _)
    exact hw this
  have hle : Ideal.span {φ.hom f} ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).2 ((key' ⟨x, hx⟩).1 hfx)
  obtain ⟨Q, hQ, -⟩ := Ideal.exists_minimalPrimes_le hle
  haveI hQp : Q.IsPrime := hQ.1.1
  have haQ : φ.hom f ∈ Q := hQ.1.2 (Ideal.mem_span_singleton_self _)
  have h1 : Q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQ
  have h0 : Q.height ≠ 0 := by
    intro h
    rw [Ideal.height_eq_zero_iff_eq_bot] at h
    exact ha (by simpa [h] using haQ)
  have hQ1 : Q.height = 1 := le_antisymm h1 (Order.one_le_iff_ne_zero.2 h0)
  let P : PrimeSpectrum Γ(X, U) := ⟨Q, hQp⟩
  have hz : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  let z : U := ⟨hU.fromSpec P, hz⟩
  have hP : hU.primeIdealOf z = P :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf z)
  clear_value z
  letI := X.presheaf.algebra_section_stalk z
  haveI := hU.isLocalization_stalk z
  refine ⟨z.1, ?_, (key' z).2 (by rw [hP]; exact haQ)⟩
  have := IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf z).asIdeal
    (X.presheaf.stalk (z : X))
  rw [this, hP]
  change ((Q.height : ℕ∞) : WithBot ℕ∞) = 1
  rw [hQ1]; rfl

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTensorOrderAlgEquivMatrixCharZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_tensor_order_algEquiv_matrix_charZero : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] [Algebra (𝓞 D.F) k], Nonempty ((k ⊗[𝓞 D.F] D.O) ≃ₐ[k] Matrix (Fin D.m) (Fin D.m) k) := by
  first | (exact @GlobalTheory.UPel.HT.MoritaChar0.tensor_order_algEquiv_matrix) | (exact GlobalTheory.UPel.HT.MoritaChar0.tensor_order_algEquiv_matrix) | (intros; apply GlobalTheory.UPel.HT.MoritaChar0.tensor_order_algEquiv_matrix <;> assumption)
end

