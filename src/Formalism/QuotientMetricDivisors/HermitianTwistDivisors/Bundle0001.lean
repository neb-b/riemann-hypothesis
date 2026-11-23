module

public import Mathlib
public import Formalism.QuotientMetricDivisors.Bundle0001

@[expose] public section

-- bundled from Formalism.QuotientMetricDivisors.HermitianTwistDivisors.BoundsSum
section
open Finset

noncomputable section

namespace Formalism.DivisionValues

theorem divisor_bounds_sum : BoundsSum := by
  intro Pl J _ S D hD lcvR logκ LG E3 lcvM L E1 E2 l ell vG g I Ic jT F err Jx η hl h0 hvG hLG hL
    hI hjT hE1 hE2 hE3
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have h1 : ∑ j, lcvM j ≤ (D : ℝ) * ∑ j, L j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by
      have := (div_le_iff₀ hDr).1 (hL j)
      linarith
  have h2 : ∑ w ∈ S, l w * vG w ≤ (D : ℝ) * LG := by
    calc ∑ w ∈ S, l w * vG w ≤ ∑ w ∈ S, (D : ℝ) * (l w * g w) :=
          Finset.sum_le_sum fun w hw => by
            have := mul_le_mul_of_nonneg_left (hvG w hw) (hl w)
            linarith
      _ = (D : ℝ) * ∑ w ∈ S, l w * g w := by rw [Finset.mul_sum]
      _ ≤ (D : ℝ) * LG := mul_le_mul_of_nonneg_left hLG hDr.le
  have f1 : ∑ w ∈ S, l w * (vG w + ∑ j, (I w j + Ic w j + jT w j)) =
      ∑ w ∈ S, l w * vG w + ∑ w ∈ S, l w * ∑ j, (I w j + Ic w j) +
        ∑ w ∈ S, l w * ∑ j, jT w j := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_add_distrib]
    ring
  have f4 : ∑ w ∈ S, l w * ∑ j, (I w j + Ic w j) ≤
      (D : ℝ) * 2 * ∑ w ∈ S, l w * ∑ j, F w j + (D : ℝ) * ∑ w ∈ S, l w * ∑ j, err w j +
        (D : ℝ) * ∑ w ∈ S, l w * (2 / ell w ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun w hw => ?_
    have h := mul_le_mul_of_nonneg_left (hI w hw) (hl w)
    have e : ∑ j, (2 * F w j + err w j) = 2 * ∑ j, F w j + ∑ j, err w j := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    rw [e] at h
    linarith
  have f6 : ∑ w ∈ S, l w * ∑ j, jT w j ≤
      (D : ℝ) * ∑ w ∈ S, l w * ∑ j, Jx w j + ∑ w ∈ S, l w * ∑ j, η w j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun w hw => ?_
    have h : ∑ j, jT w j ≤ (D : ℝ) * ∑ j, Jx w j + ∑ j, η w j := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun j _ => by have := hjT w hw j; linarith
    have := mul_le_mul_of_nonneg_left h (hl w)
    linarith
  have eswap : ∀ f : Pl → J → ℝ, ∑ j, ∑ w ∈ S, l w * f w j = ∑ w ∈ S, l w * ∑ j, f w j := by
    intro f
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  have f8 : ∑ w ∈ S, l w * ∑ j, err w j + ∑ w ∈ S, l w * ∑ j, Jx w j ≤ ∑ j, E1 j := by
    rw [← eswap, ← eswap, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => by
      refine le_trans (le_of_eq ?_) (hE1 j)
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun w _ => by ring
  have f9 : ∑ w ∈ S, l w * ∑ j, η w j ≤ (D : ℝ) * ∑ j, E2 j := by
    rw [← eswap, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by
      have h := hE2 j
      rw [← Finset.sum_div] at h
      have := (div_le_iff₀ hDr).1 h
      linarith
  have f10 : (D : ℝ) * ∑ w ∈ S, l w * (2 / ell w ^ 2) ≤ (D : ℝ) * E3 :=
    mul_le_mul_of_nonneg_left hE3 hDr.le
  have f11 : ∑ j, (E1 j + E2 j) = ∑ j, E1 j + ∑ j, E2 j := Finset.sum_add_distrib
  have eF := eswap F
  rw [div_le_iff₀ hDr]
  have hD0 : (0 : ℝ) ≤ D := hDr.le
  nlinarith [h0, h1, h2, f1, f4, f6, f8, f9, f10, f11, eF, mul_le_mul_of_nonneg_left f8 hD0]

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ConjTransposeEqOfPosDef
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

namespace R0

variable {K : Type} [Field K] [StarRing K]

theorem map_inv_field {F : Type} [Field F] (f : K →+* F) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) : A⁻¹.map f = (A.map f)⁻¹ := by
  have hdet : (A.map f).det = f A.det := (RingHom.map_det f A).symm
  by_cases h : IsUnit A.det
  · symm
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ h, Matrix.map_one _ f.map_zero f.map_one]
  · have h' : ¬ IsUnit (A.map f).det := by
      rw [hdet, isUnit_iff_ne_zero, map_ne_zero f]
      rw [isUnit_iff_ne_zero] at h
      exact h
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h',
      Matrix.map_zero _ f.map_zero]

theorem conjTranspose_map (σ : K →+* ℂ) (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a))
    {m n : Type} (A : Matrix m n K) : Aᴴ.map σ = (A.map σ)ᴴ := by
  ext i j
  rw [Matrix.map_apply, Matrix.conjTranspose_apply, Matrix.conjTranspose_apply, Matrix.map_apply, hσ]
  rfl

theorem conjTranspose_eq_of_posDef [NumberField K] (v0 : InfinitePlace K) (hv0 : IsConjAt v0)
    {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (hH : (H.map v0.embedding).PosDef) : Hᴴ = H := by
  have h1 := conjTranspose_map v0.embedding hv0 H
  have h2 : (H.map v0.embedding)ᴴ = H.map v0.embedding := hH.isHermitian
  ext i j
  have h3 := congrFun (congrFun (h1.trans h2) i) j
  simp only [Matrix.map_apply] at h3
  exact v0.embedding.injective h3

theorem gramMat_conjTranspose {D m : ℕ} (Γ : Matrix (Fin D) (Fin D) K) (hΓ : Γᴴ = Γ)
    (e : Fin m → Fin D → K) :
    (Matrix.of fun a b => star (e a) ⬝ᵥ Γ.mulVec (e b))ᴴ =
      Matrix.of fun a b => star (e a) ⬝ᵥ Γ.mulVec (e b) := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
  have h1 : star (star (e j) ⬝ᵥ Γ.mulVec (e i)) = star (e i) ⬝ᵥ Γᴴ.mulVec (e j) := by
    simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', star_star, Matrix.conjTranspose_apply,
      Finset.mul_sum, Pi.star_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    ring
  rw [h1, hΓ]

end R0

open R0 in
theorem gram_determinant_quotient_metric : GramDeterminantQuotientMetric := by
  intro K _ _ _ _ K0 hCM v0 hv0 n D H hK0 hpos P hsurj XQ hQ e
  have hH : Hᴴ = H := conjTranspose_eq_of_posDef v0 hv0 H (hpos v0)
  have hΓ : (quotGram P H)ᴴ = quotGram P H := by
    unfold quotGram
    rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_nonsing_inv, hH, Matrix.mul_assoc]
  have hΓmap : (quotGram P H).map v0.embedding = ((XQ v0)⁻¹)ᴴ * (XQ v0)⁻¹ := by
    rw [(hQ v0).2]
    unfold quotGram
    rw [map_inv_field, Matrix.map_mul, Matrix.map_mul, map_inv_field, conjTranspose_map v0.embedding hv0]
  refine ⟨?_, ?_⟩
  · unfold gramR
    rw [← Matrix.det_conjTranspose, gramMat_conjTranspose _ hΓ e]
  · unfold gramR gram Formalism.HN.gramPl
    rw [RingHom.map_det]
    congr 1
    ext a c
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Formalism.HermitianLatticesTheory.majAt,
      Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, Pi.basisFun_repr]
    have hY : ∀ (Y : Matrix (Fin D) (Fin D) ℂ) (x y : Fin D → ℂ),
        ∑ i, star ((Y *ᵥ x) i) * (Y *ᵥ y) i = ∑ i, star (x i) * ((Yᴴ * Y) *ᵥ y) i := by
      intro Y x y
      have e1 : ∑ i, star ((Y *ᵥ x) i) * (Y *ᵥ y) i = star (Y *ᵥ x) ⬝ᵥ (Y *ᵥ y) := rfl
      have e2 : ∑ i, star (x i) * ((Yᴴ * Y) *ᵥ y) i = star x ⬝ᵥ ((Yᴴ * Y) *ᵥ y) := rfl
      rw [e1, e2, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
    rw [hY, ← hΓmap]
    have hv0' : ∀ a : K, v0.embedding (star a) = starRingEnd ℂ (v0.embedding a) := hv0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Pi.star_apply, Matrix.map_apply, hv0']
    rfl

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DeterminantCauchySchwarz
section
open Matrix
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Formalism.DivisionValues

lemma one_le_det_one_add {m : Type*} [Fintype m] [DecidableEq m] {Z : Matrix m m ℂ}
    (hZ : Z.PosSemidef) : (1 : ℂ) ≤ (1 + Z).det := by
  have hspec := hZ.1.spectral_theorem
  have hUU : (hZ.1.eigenvectorUnitary : Matrix m m ℂ) * star (hZ.1.eigenvectorUnitary : Matrix m m ℂ) = 1 := by
    simp
  have hdet : ∀ x : Matrix m m ℂ, ((hZ.1.eigenvectorUnitary : Matrix m m ℂ) * x *
      star (hZ.1.eigenvectorUnitary : Matrix m m ℂ)).det = x.det := by
    intro x
    rw [det_mul, det_mul, mul_comm (det (hZ.1.eigenvectorUnitary : Matrix m m ℂ)), mul_assoc, ← det_mul, hUU,
      det_one, mul_one]
  have key : 1 + Z = (Unitary.conjStarAlgAut ℂ (Matrix m m ℂ) hZ.1.eigenvectorUnitary)
      (1 + diagonal (RCLike.ofReal ∘ hZ.1.eigenvalues)) := by
    rw [map_add (f := _), map_one, ← hspec]
  rw [key, Unitary.conjStarAlgAut_apply, hdet, ← diagonal_one, diagonal_add, det_diagonal]
  have hev := hZ.eigenvalues_nonneg
  have hprod : ∏ i, ((1 : ℂ) + (RCLike.ofReal ∘ hZ.1.eigenvalues) i) =
      ((∏ i, (1 + hZ.1.eigenvalues i) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hprod, ← Complex.ofReal_one, Complex.real_le_real]
  calc (1 : ℝ) = ∏ _i : m, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun i _ => by linarith [hev i])

lemma det_le_det_add {m : Type*} [Fintype m] [DecidableEq m] {X Y : Matrix m m ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) : X.det ≤ (X + Y).det := by
  by_cases hXu : IsUnit X
  · have hX0 : (0 : Matrix m m ℂ) ≤ X := Matrix.nonneg_iff_posSemidef.mpr hX
    have hSS : CFC.sqrt X * CFC.sqrt X = X := CFC.sqrt_mul_sqrt_self X hX0
    have hS0 : (0 : Matrix m m ℂ) ≤ CFC.sqrt X := CFC.sqrt_nonneg X
    set S := CFC.sqrt X with hSdef
    have hSpsd : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hS0
    have hSh : Sᴴ = S := hSpsd.1
    have hSu : IsUnit S := isUnit_of_mul_isUnit_left (hSS ▸ hXu)
    have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSu
    have h1 : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hSdet
    have h2 : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hSdet
    have hTh : (S⁻¹)ᴴ = S⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hSh]
    have hZ : ((S⁻¹)ᴴ * Y * S⁻¹).PosSemidef := hY.conjTranspose_mul_mul_same _
    have hmid : S * (S⁻¹ * Y * S⁻¹) * S = Y := by
      rw [← mul_assoc, ← mul_assoc, h1, one_mul, mul_assoc, h2, mul_one]
    have hsum : X + Y = S * (1 + (S⁻¹)ᴴ * Y * S⁻¹) * S := by
      rw [hTh, mul_add, add_mul, mul_one, hSS, hmid]
    have hdX : X.det = S.det * S.det := by rw [← hSS, det_mul]
    rw [hsum, det_mul, det_mul]
    have e : S.det * (1 + (S⁻¹)ᴴ * Y * S⁻¹).det * S.det = X.det * (1 + (S⁻¹)ᴴ * Y * S⁻¹).det := by
      rw [hdX]; ring
    rw [e]
    have hone := one_le_det_one_add hZ
    have hXd : 0 ≤ X.det := hX.det_nonneg
    have := mul_le_mul_of_nonneg_left hone hXd
    simpa using this
  · have hd : X.det = 0 := by
      by_contra h
      exact hXu ((Matrix.isUnit_iff_isUnit_det X).mpr (isUnit_iff_ne_zero.mpr h))
    rw [hd]
    exact (hX.add hY).det_nonneg

theorem determinant_cauchy_schwarz : DetCS := by
  intro n D Hc hHc A B
  have hHh : Hcᴴ = Hc := hHc.1
  have hPpsd : (A * Hc * Aᴴ).PosSemidef := hHc.posSemidef.mul_mul_conjTranspose_same A
  set P := A * Hc * Aᴴ with hP
  set Q := A * Hc * Bᴴ with hQ
  set R := B * Hc * Bᴴ with hR
  by_cases hPu : IsUnit P
  · have hPpd : P.PosDef := (hPpsd.posDef_iff_isUnit).mpr hPu
    have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
    have hPinv : (P⁻¹).PosSemidef := hPpd.inv.posSemidef
    have hPih : (P⁻¹)ᴴ = P⁻¹ := hPinv.1
    have hQh : Qᴴ = B * Hc * Aᴴ := by
      rw [hQ, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hHh, Matrix.mul_assoc]
    set K := B - Qᴴ * P⁻¹ * A with hK
    have hKpsd : (K * Hc * Kᴴ).PosSemidef := hHc.posSemidef.mul_mul_conjTranspose_same K
    have hXpsd : (Qᴴ * P⁻¹ * Q).PosSemidef := hPinv.conjTranspose_mul_mul_same Q
    have hKh : Kᴴ = Bᴴ - Aᴴ * P⁻¹ * Q := by
      rw [hK, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hPih]
      simp only [Matrix.mul_assoc]
    have r1 : B * (Hc * Bᴴ) = R := by rw [hR, Matrix.mul_assoc]
    have r2 : ∀ X : Matrix (Fin D) (Fin D) ℂ, B * (Hc * (Aᴴ * X)) = Qᴴ * X := by
      intro X; rw [hQh]; simp only [Matrix.mul_assoc]
    have r3 : A * (Hc * Bᴴ) = Q := by rw [hQ, Matrix.mul_assoc]
    have r4 : ∀ X : Matrix (Fin D) (Fin D) ℂ, A * (Hc * (Aᴴ * X)) = P * X := by
      intro X; rw [hP]; simp only [Matrix.mul_assoc]
    have r5 : ∀ X : Matrix (Fin D) (Fin D) ℂ, P⁻¹ * (P * X) = X := by
      intro X; rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hPdet, one_mul]
    have hKK : K * Hc * Kᴴ = R - Qᴴ * P⁻¹ * Q := by
      rw [hKh, hK]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
      rw [r2, r3, r4, r5, r1]
      abel
    have hsplit : R = Qᴴ * P⁻¹ * Q + K * Hc * Kᴴ := by rw [hKK]; abel
    have hle := det_le_det_add hXpsd hKpsd
    rw [← hsplit, det_mul, det_mul, det_conjTranspose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at hle
    obtain ⟨hpre, hpim⟩ := Complex.lt_def.mp hPpd.det_pos
    have key : ∀ pr : ℝ, star Q.det * (pr : ℂ)⁻¹ * Q.det = ((‖Q.det‖ ^ 2 / pr : ℝ) : ℂ) := by
      intro pr
      rw [mul_right_comm, Complex.star_def, Complex.conj_mul']
      push_cast
      ring
    have hpeq : P.det = ((P.det.re : ℝ) : ℂ) :=
      Complex.ext (by rw [Complex.ofReal_re]) (by rw [Complex.ofReal_im]; simpa using hpim.symm)
    rw [hpeq, key] at hle
    have h2 := (Complex.le_def.mp hle).1
    rw [Complex.ofReal_re] at h2
    have hpre' : 0 < P.det.re := by simpa using hpre
    rw [div_le_iff₀ hpre'] at h2
    rw [mul_comm]
    exact h2
  · have hd : P.det = 0 := by
      by_contra h
      exact hPu ((Matrix.isUnit_iff_isUnit_det P).mpr (isUnit_iff_ne_zero.mpr h))
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hd
    have hw : v ᵥ* A = 0 := by
      by_contra hw
      have hsw : star (v ᵥ* A) ≠ 0 := star_ne_zero.mpr hw
      have hpos := hHc.dotProduct_mulVec_pos hsw
      have h0 : star (star (v ᵥ* A)) ⬝ᵥ (Hc *ᵥ star (v ᵥ* A)) = 0 := by
        rw [star_star]
        have h00 : (v ᵥ* P) ⬝ᵥ star v = 0 := by rw [hv, zero_dotProduct]
        rw [hP, ← vecMul_vecMul, ← vecMul_vecMul, ← dotProduct_mulVec, mulVec_conjTranspose, star_star,
          ← dotProduct_mulVec] at h00
        exact h00
      rw [h0] at hpos
      exact lt_irrefl _ hpos
    have hq : Q.det = 0 := by
      apply Matrix.exists_vecMul_eq_zero_iff.mp
      refine ⟨v, hv0, ?_⟩
      rw [hQ, ← vecMul_vecMul, ← vecMul_vecMul, hw, zero_vecMul, zero_vecMul]
    rw [hq, hd]
    simp

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.HermitianTwistDivisors.LocBasis
section
open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.DivisionValues

namespace SemilocalBasisHermitianTwistDivisors

variable {K : Type} [Field K] [NumberField K] [StarRing K]

lemma mem_loc_iff' (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (M : Submodule (𝓞 K) (Fin d → K))
    (x : Fin d → K) :
    x ∈ Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal M ↔
      ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal, s • x ∈ M :=
  Iff.rfl

lemma mem_hcompl (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (h1 : x ∉ w.asIdeal)
    (h2 : x ∉ (conjPl w).asIdeal) : x ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal := by
  apply Submonoid.subset_closure
  refine ⟨h1, fun t ht htw => h2 ?_⟩
  have hct : cO K t = x := by
    apply RingOfIntegers.ext
    change star (t : K) = (x : K)
    have ht' : (t : K) = star (x : K) := ht
    rw [ht', star_star]
  rw [← hct]
  exact Ideal.mem_map_of_mem _ htw

lemma hcompl_le (w : HeightOneSpectrum (𝓞 K)) :
    Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal ≤ nonZeroDivisors (𝓞 K) := by
  apply Submonoid.closure_le.mpr
  intro s hs
  apply mem_nonZeroDivisors_of_ne_zero
  rintro rfl
  exact hs.1 w.asIdeal.zero_mem

abbrev A (w : HeightOneSpectrum (𝓞 K)) : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K (Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal) (hcompl_le w)

lemma mem_A (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ A w ↔ ∃ (a s : 𝓞 K) (_ : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal),
      x = algebraMap (𝓞 K) K a * (algebraMap (𝓞 K) K s)⁻¹ :=
  Iff.rfl

lemma algebraMap_ne_zero (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K}
    (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal) : algebraMap (𝓞 K) K s ≠ 0 :=
  IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hcompl_le w hs)

lemma primes_finite (w : HeightOneSpectrum (𝓞 K)) :
    {P : Ideal (A w) | P.IsPrime}.Finite := by
  apply ((({⊥, w.asIdeal, (conjPl w).asIdeal} : Set (Ideal (𝓞 K))).toFinite.image
    (Ideal.map (algebraMap (𝓞 K) (A w))))).subset
  intro P hP
  have hP' : P.IsPrime := hP
  obtain ⟨hQ, hdisj⟩ :=
    (IsLocalization.isPrime_iff_isPrime_disjoint (Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal) (A w) P).mp hP'
  refine ⟨P.comap (algebraMap (𝓞 K) (A w)), ?_,
    IsLocalization.map_under (Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal) (A w) P⟩
  set Q := P.comap (algebraMap (𝓞 K) (A w))
  have hsub : (Q : Set (𝓞 K)) ⊆ (w.asIdeal : Set (𝓞 K)) ∪ ((conjPl w).asIdeal : Set (𝓞 K)) := by
    intro x hx
    by_contra hn
    simp only [Set.mem_union, SetLike.mem_coe, not_or] at hn
    exact Set.disjoint_left.mp hdisj (mem_hcompl w x hn.1 hn.2) hx
  by_cases hb : Q = ⊥
  · exact Or.inl hb
  have hmax : Q.IsMaximal := hQ.isMaximal hb
  rcases Ideal.subset_union.mp hsub with h | h
  · exact Or.inr (Or.inl (hmax.eq_of_le w.isPrime.ne_top h))
  · exact Or.inr (Or.inr (hmax.eq_of_le (conjPl w).isPrime.ne_top h))

lemma mem_loc_iff_span (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (M : Submodule (𝓞 K) (Fin d → K))
    (x : Fin d → K) :
    x ∈ Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal M ↔ x ∈ Submodule.span (A w) (M : Set (Fin d → K)) := by
  constructor
  · rintro ⟨s, hs, hsx⟩
    have hs0 := algebraMap_ne_zero w hs
    have hu : (algebraMap (𝓞 K) K s)⁻¹ ∈ A w := (mem_A w _).mpr ⟨1, s, hs, by simp⟩
    have hx : x = (⟨_, hu⟩ : A w) • (s • x) := by
      rw [Subalgebra.smul_def, ← algebraMap_smul K s x, smul_smul]
      simp [hs0]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hsx)
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact (mem_loc_iff' w M y).mpr ⟨1, one_mem _, by simpa using hy⟩
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul a y _ hy =>
      obtain ⟨s, hs, hsy⟩ := (mem_loc_iff' w M y).mp hy
      obtain ⟨r, t, ht, hat⟩ := (mem_A w a).mp a.2
      refine (mem_loc_iff' w M _).mpr ⟨t * s, mul_mem ht hs, ?_⟩
      have ht0 := algebraMap_ne_zero w ht
      have he : (t * s) • (a • y) = r • (s • y) := by
        rw [Subalgebra.smul_def, hat, ← algebraMap_smul K (t * s), ← algebraMap_smul K r,
          ← algebraMap_smul K s, smul_smul, smul_smul]
        congr 1
        rw [map_mul]
        field_simp
      rw [he]
      exact M.smul_mem r hsy

end SemilocalBasisHermitianTwistDivisors


open SemilocalBasisHermitianTwistDivisors in
theorem semilocal_basis_exists :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ)
      (L : Submodule (𝓞 K) (Fin d → K)), Submodule.IsFullLattice K L →
      ∀ w : HeightOneSpectrum (𝓞 K), ∃ f : Fin d → Fin d → K, IsLocBasis L w f := by
  intro K _ _ _ d L hL w
  have : IsDedekindDomain (A w) :=
    IsLocalization.isDedekindDomain (𝓞 K) (hcompl_le w) (A w)
  have : IsPrincipalIdealRing (A w) := IsPrincipalIdealRing.of_finite_primes (primes_finite w)
  set N : Submodule (A w) (Fin d → K) := Submodule.span (A w) (L : Set (Fin d → K)) with hN
  have : Module.Finite (A w) N := by
    obtain ⟨s, hs⟩ := hL.fg
    rw [Module.Finite.iff_fg]
    refine ⟨s, ?_⟩
    rw [hN, ← hs, Submodule.span_span_of_tower]
  have : Module.IsTorsionFree (A w) N := inferInstance
  let b := Module.Free.chooseBasis (A w) N
  let v : Module.Free.ChooseBasisIndex (A w) N → Fin d → K := fun i => (b i : Fin d → K)
  have hliA : LinearIndependent (A w) v := b.linearIndependent.map' N.subtype N.ker_subtype
  have hli : LinearIndependent K v := (LinearIndependent.iff_fractionRing (A w) K).mp hliA
  have hspanA : Submodule.span (A w) (Set.range v) = N := by
    have : Set.range v = N.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspan : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← hL.span_eq_top, Submodule.span_le]
    intro x hx
    have hxN : x ∈ Submodule.span (A w) (Set.range v) := by
      rw [hspanA]; exact Submodule.subset_span hx
    exact Submodule.span_le_restrictScalars (A w) K _ hxN
  let bK : Basis _ K (Fin d → K) := Basis.mk hli hspan
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex (A w) N) = d := by
    rw [← Module.finrank_eq_card_basis bK, Module.finrank_fin_fun]
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨v ∘ e.symm, hli.comp _ e.symm.injective, ?_⟩
  ext x
  rw [mem_loc_iff_span, mem_loc_iff_span, Submodule.span_span_of_tower, EquivLike.range_comp,
    hspanA]

end Formalism.DivisionValues
end
end

