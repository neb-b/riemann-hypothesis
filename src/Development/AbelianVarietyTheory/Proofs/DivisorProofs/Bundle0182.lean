module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigCellFactorisationDoubledUnitaryGroup
section
open GlobalTheory.WeilM
open scoped Matrix
open Matrix

namespace GlobalTheory.BigCell

variable {R : Type} [CommRing R] {β : Type} [Fintype β] [DecidableEq β]

theorem e1 : (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R) * (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R) = 0 := by
  simp [fromCols_mul_fromRows]

theorem e2 : (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R) * (fromCols (1 : Matrix β β R) 1 : Matrix β (β ⊕ β) R) +
    (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R) * (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R) =
    (2 : R) • (1 : Matrix (β ⊕ β) (β ⊕ β) R) := by
  rw [fromRows_mul_fromCols, fromRows_mul_fromCols, fromBlocks_add, ← fromBlocks_one, fromBlocks_smul]
  congr 1 <;> simp [two_smul]

theorem e3 (J : Matrix β β R) : (fromCols (1 : Matrix β β R) 1 : Matrix β (β ⊕ β) R) * dbl J =
    J * (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R) := by
  simp [dbl, fromCols_mul_fromBlocks, mul_fromCols]

theorem e4 (J : Matrix β β R) : dbl J * (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R) =
    (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R) * J := by
  simp [dbl, fromBlocks_mul_fromRows, fromRows_mul]

theorem e6 (J : Matrix β β R) : (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R) * J * (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R) +
    (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R) * J * (fromCols (1 : Matrix β β R) 1 : Matrix β (β ⊕ β) R) =
    (2 : R) • dbl J := by
  simp only [Matrix.mul_assoc, fromRows_mul, mul_fromCols, fromRows_fromCols_eq_fromBlocks, dbl, fromBlocks_smul]
  simp
  rw [fromBlocks_add]
  congr 1 <;> ext i j <;> simp <;> ring

theorem e7 (J : Matrix β β R) : (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R) * dbl J * (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R) = 0 := by
  simp [dbl, fromCols_mul_fromBlocks, fromCols_mul_fromRows]

theorem e5 (J : Matrix β β R) : (fromCols (1 : Matrix β β R) 1 : Matrix β (β ⊕ β) R) * dbl J * (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R) = 0 := by
  simp [dbl, fromCols_mul_fromBlocks, fromCols_mul_fromRows]

variable [Invertible (2 : R)]

theorem map_half (f : R →+* R) : f (⅟(2 : R)) = ⅟2 := by
  have e : f (⅟(2 : R)) * 2 = 1 := by
    have h := congrArg f (invOf_mul_self (2 : R))
    rwa [map_mul, map_ofNat, map_one] at h
  linear_combination (⅟(2 : R)) * e - f (⅟(2 : R)) * (invOf_mul_self (2 : R))

section Abstract

variable (f : R →+* R) (J : Matrix β β R) (K G : Matrix (β ⊕ β) (β ⊕ β) R) (Δ N : Matrix (β ⊕ β) β R)
  (Δt Nt : Matrix β (β ⊕ β) R) (D' : Matrix β β R)

theorem skew (hG : Gᵀ * K * G.map f = K) (hΔT : Δᵀ = Δt) (hNT : Nᵀ = Nt) (hΔtf : Δt.map f = Δt) (hNf : N.map f = N)
    (hNtf : Nt.map f = Nt) (e6 : Δ * J * Nt + N * J * Δt = (2 : R) • K) (e7 : Nt * K * N = 0)
    (hD : (Nt * G * N) * D' = 1) :
    (Δt * G * N * D')ᵀ * J + J * (Δt * G * N * D').map f = 0 := by
  have hΔtT : Δtᵀ = Δ := by rw [← hΔT, transpose_transpose]
  have hNtT : Ntᵀ = N := by rw [← hNT, transpose_transpose]
  have hDf : Nt * (G.map f * (N * D'.map f)) = 1 := by
    have := congrArg (Matrix.map · f) hD
    simp only [Matrix.map_mul, hNtf, hNf, Matrix.map_one f (map_zero f) (map_one f)] at this
    simpa only [Matrix.mul_assoc] using this
  have hDt : ∀ {γ : Type} (X : Matrix β γ R), D'ᵀ * (Nt * (Gᵀ * (N * X))) = X := by
    intro γ X
    have := congrArg transpose hD
    rw [transpose_mul, transpose_mul, transpose_mul, hNT, hNtT, transpose_one] at this
    calc D'ᵀ * (Nt * (Gᵀ * (N * X))) = (D'ᵀ * (Nt * (Gᵀ * N))) * X := by simp only [Matrix.mul_assoc]
      _ = X := by rw [this, Matrix.one_mul]
  have hxT : (Δt * G * N * D')ᵀ = D'ᵀ * (Nt * (Gᵀ * Δ)) := by
    simp only [transpose_mul, hNT, hΔtT, Matrix.mul_assoc]
  have hxf : (Δt * G * N * D').map f = Δt * (G.map f * (N * D'.map f)) := by
    simp only [Matrix.map_mul, hΔtf, hNf, Matrix.mul_assoc]
  have hY : Nt * (Gᵀ * ((Δ * J * Nt + N * J * Δt) * (G.map f * (N * D'.map f)))) = 0 := by
    rw [e6, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
      show Gᵀ * (K * (G.map f * (N * D'.map f))) = K * N * D'.map f by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hG, Matrix.mul_assoc],
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, e7, Matrix.zero_mul, smul_zero]
  calc (Δt * G * N * D')ᵀ * J + J * (Δt * G * N * D').map f
      = D'ᵀ * (Nt * (Gᵀ * ((Δ * J * Nt + N * J * Δt) * (G.map f * (N * D'.map f))))) := by
        rw [hxT, hxf]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hDf, hDt, Matrix.mul_one]
    _ = 0 := by rw [hY, Matrix.mul_zero]

end Abstract

section Abstract2

variable (f : R →+* R) (J : Matrix β β R) (K G : Matrix (β ⊕ β) (β ⊕ β) R) (Δ N : Matrix (β ⊕ β) β R)
  (Δt Nt : Matrix β (β ⊕ β) R) (D' : Matrix β β R)

theorem mem_unitary (hG : Gᵀ * K * G.map f = K) (hΔT : Δᵀ = Δt) (hNT : Nᵀ = Nt) (hΔf : Δ.map f = Δ)
    (hΔtf : Δt.map f = Δt) (hNf : N.map f = N) (hNtf : Nt.map f = Nt)
    (e3 : Δt * K = J * Nt) (e4 : K * Δ = N * J) (e5 : Δt * K * Δ = 0)
    (e6 : Δ * J * Nt + N * J * Δt = (2 : R) • K) (e7 : Nt * K * N = 0) (hD : (Nt * G * N) * D' = 1) :
    (1 + ⅟(2 : R) • (Δ * (Δt * G * N * D') * Nt))ᵀ * K * (1 + ⅟(2 : R) • (Δ * (Δt * G * N * D') * Nt)).map f = K := by
  have hZ := skew f J K G Δ N Δt Nt D' hG hΔT hNT hΔtf hNf hNtf e6 e7 hD
  have hNtT : Ntᵀ = N := by rw [← hNT, transpose_transpose]
  set x := Δt * G * N * D' with hx
  have hMT : (Δ * x * Nt)ᵀ = N * (xᵀ * Δt) := by simp only [transpose_mul, hNtT, hΔT, Matrix.mul_assoc]
  have hMf : (Δ * x * Nt).map f = Δ * (x.map f * Nt) := by simp only [Matrix.map_mul, hΔf, hNtf, Matrix.mul_assoc]
  have hPT : (1 + ⅟(2 : R) • (Δ * x * Nt))ᵀ = 1 + ⅟(2 : R) • (N * (xᵀ * Δt)) := by
    rw [transpose_add, transpose_one, transpose_smul, hMT]
  have hPf : (1 + ⅟(2 : R) • (Δ * x * Nt)).map f = 1 + ⅟(2 : R) • (Δ * (x.map f * Nt)) := by
    rw [Matrix.map_add f (map_add f), Matrix.map_one f (map_zero f) (map_one f), Matrix.map_smul' _ _ _ (map_mul f),
      map_half, hMf]
  have A1 : N * (xᵀ * Δt) * K * (Δ * (x.map f * Nt)) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [show Δt * (K * (Δ * (x.map f * Nt))) = 0 by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e5, Matrix.zero_mul]]
    simp
  have A2 : N * (xᵀ * Δt) * K + K * (Δ * (x.map f * Nt)) = 0 := by
    calc _ = N * ((xᵀ * J + J * x.map f) * Nt) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, e3, ← Matrix.mul_assoc K Δ, e4]
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
      _ = 0 := by rw [hZ]; simp
  have expand : ∀ U V : Matrix (β ⊕ β) (β ⊕ β) R, (1 + ⅟(2 : R) • U) * K * (1 + ⅟(2 : R) • V) =
      K + ⅟(2 : R) • (U * K + K * V) + (⅟(2 : R) * ⅟(2 : R)) • (U * K * V) := by
    intro U V
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      smul_add, smul_smul]
    abel
  rw [hPT, hPf, expand, A2, A1]
  simp

theorem mul_inv_eq (hNtΔ : Nt * Δ = 0) (x : Matrix β β R) :
    (1 + ⅟(2 : R) • (Δ * x * Nt)) * (1 - ⅟(2 : R) • (Δ * x * Nt)) = 1 ∧
    (1 - ⅟(2 : R) • (Δ * x * Nt)) * (1 + ⅟(2 : R) • (Δ * x * Nt)) = 1 := by
  have hM : (Δ * x * Nt) * (Δ * x * Nt) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [show Nt * (Δ * (x * Nt)) = 0 by rw [← Matrix.mul_assoc, hNtΔ, Matrix.zero_mul]]
    simp
  constructor
  · simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hM, smul_zero]
    abel
  · simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hM, smul_zero]
    abel

theorem q_col (h2 : Δ * Δt + N * Nt = (2 : R) • 1) (hD' : D' * (Nt * G * N) = 1) :
    (1 - ⅟(2 : R) • (Δ * (Δt * G * N * D') * Nt)) * G * N = N * (⅟(2 : R) • (Nt * G * N)) := by
  have hNN : N * Nt = (2 : R) • 1 - Δ * Δt := by rw [← h2]; abel
  have hD'r : D' * (Nt * (G * N)) = 1 := by rw [← hD']; simp only [Matrix.mul_assoc]
  calc (1 - ⅟(2 : R) • (Δ * (Δt * G * N * D') * Nt)) * G * N = G * N - ⅟(2 : R) • (Δ * (Δt * (G * N))) := by
        simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc, hD'r, Matrix.mul_one]
    _ = N * (⅟(2 : R) • (Nt * G * N)) := by
        rw [Matrix.mul_smul, show N * (Nt * G * N) = N * Nt * G * N by simp only [Matrix.mul_assoc], hNN]
        simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, smul_sub, smul_smul, invOf_mul_self, one_smul,
          Matrix.mul_assoc]

end Abstract2

theorem bigCell_factor : ∀ (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (c : R →ₐ[A] R) [Invertible (2 : R)]
    (β : Type) [Fintype β] [DecidableEq β] (J : Matrix β β R) (g : UG c (dbl J)),
    IsUnit (Matrix.fromCols (1 : Matrix β β R) (-1 : Matrix β β R) * ((g : GL (β ⊕ β) R) : Matrix (β ⊕ β) (β ⊕ β) R) *
      Matrix.fromRows (1 : Matrix β β R) (-1 : Matrix β β R)).det →
    ∃ (p q : UG c (dbl J)) (t s : GL β R),
      ((p : GL (β ⊕ β) R) : Matrix (β ⊕ β) (β ⊕ β) R) * Matrix.fromRows (1 : Matrix β β R) (1 : Matrix β β R) =
        Matrix.fromRows (1 : Matrix β β R) (1 : Matrix β β R) * (t : Matrix β β R) ∧
      ((q : GL (β ⊕ β) R) : Matrix (β ⊕ β) (β ⊕ β) R) * Matrix.fromRows (1 : Matrix β β R) (-1 : Matrix β β R) =
        Matrix.fromRows (1 : Matrix β β R) (-1 : Matrix β β R) * (s : Matrix β β R) ∧ g = p * q := by
  intro A R _ _ _ c _ β _ _ J g hdet
  set G : Matrix (β ⊕ β) (β ⊕ β) R := ((g : GL (β ⊕ β) R) : Matrix (β ⊕ β) (β ⊕ β) R) with hGdef
  set f : R →+* R := (c : R →+* R) with hf
  have hG : Gᵀ * dbl J * G.map f = dbl J := g.2
  have h1 : (1 : Matrix β β R).map f = 1 := Matrix.map_one f (map_zero f) (map_one f)
  have hm1 : (-1 : Matrix β β R).map f = -1 := by rw [Matrix.map_neg _ (map_neg f), h1]
  have hΔT : (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R)ᵀ = fromCols 1 1 := by
    rw [transpose_fromRows, transpose_one]
  have hNT : (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R)ᵀ = fromCols 1 (-1) := by
    rw [transpose_fromRows, transpose_one, transpose_neg, transpose_one]
  have hΔf : (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R).map f = fromRows 1 1 := by rw [fromRows_map, h1]
  have hNf : (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R).map f = fromRows 1 (-1) := by
    rw [fromRows_map, h1, hm1]
  have hΔtf : (fromCols (1 : Matrix β β R) 1 : Matrix β (β ⊕ β) R).map f = fromCols 1 1 := by rw [fromCols_map, h1]
  have hNtf : (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R).map f = fromCols 1 (-1) := by
    rw [fromCols_map, h1, hm1]
  set D : Matrix β β R := (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R) * G *
    (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R) with hDdef
  have hD : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hD' : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul _ hdet
  set M : Matrix (β ⊕ β) (β ⊕ β) R := (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R) *
    ((fromCols (1 : Matrix β β R) 1 : Matrix β (β ⊕ β) R) * G * (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R) *
      D⁻¹) * (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R) with hMdef
  have hinv := mul_inv_eq (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R)
    (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R) e1
    ((fromCols (1 : Matrix β β R) 1 : Matrix β (β ⊕ β) R) * G * (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R) * D⁻¹)
  have hmem := mem_unitary f J (dbl J) G _ _ _ _ D⁻¹ hG hΔT hNT hΔf hΔtf hNf hNtf (e3 J) (e4 J) (e5 J) (e6 J) (e7 J) hD
  let P : GL (β ⊕ β) R := ⟨1 + ⅟(2 : R) • M, 1 - ⅟(2 : R) • M, hinv.1, hinv.2⟩
  let p : UG c (dbl J) := ⟨P, hmem⟩
  have hdetS : IsUnit (⅟(2 : R) • D).det := by
    rw [det_smul]
    exact ((isUnit_of_invertible (⅟(2 : R))).pow _).mul hdet
  let s : GL β R := ((Matrix.isUnit_iff_isUnit_det _).mpr hdetS).unit
  refine ⟨p, p⁻¹ * g, 1, s, ?_, ?_, (mul_inv_cancel_left p g).symm⟩
  · show (1 + ⅟(2 : R) • M) * (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R) = _
    rw [Units.val_one, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hMdef, Matrix.mul_assoc _ _
      (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R), e1, Matrix.mul_zero, smul_zero, add_zero]
  · show (1 - ⅟(2 : R) • M) * G * (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R) = _
    rw [IsUnit.unit_spec]
    exact q_col G _ _ _ _ D⁻¹ (e2) hD'

end GlobalTheory.BigCell
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedOfIsIntegral
section
open NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.LocBounded

theorem isIntegral_mul_of_commute {R A : Type} [CommRing R] [Ring A] [Algebra R A] {x y : A}
    (hc : Commute x y) (hx : IsIntegral R x) (hy : IsIntegral R y) : IsIntegral R (x * y) := by
  let S := Algebra.adjoin R ({x, y} : Set A)
  letI : IsMulCommutative S :=
    Algebra.isMulCommutative_adjoin R (Set.pairwise_pair.2 fun _ => ⟨hc, hc.symm⟩)
  have hx' : x ∈ S := Algebra.subset_adjoin (by simp)
  have hy' : y ∈ S := Algebra.subset_adjoin (by simp)
  have h1 : IsIntegral R (⟨x, hx'⟩ : S) :=
    (isIntegral_algHom_iff S.val Subtype.val_injective).1 hx
  have h2 : IsIntegral R (⟨y, hy'⟩ : S) :=
    (isIntegral_algHom_iff S.val Subtype.val_injective).1 hy
  exact open scoped IsMulCommutative in (h1.mul h2).map S.val

theorem isIntegral_trace_of_isIntegral {R K : Type} [CommRing R] [Field K] [Algebra R K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (hM : IsIntegral R M) : IsIntegral R M.trace := by
  let L := AlgebraicClosure K
  let φ : Matrix (Fin n) (Fin n) K →ₐ[R] Matrix (Fin n) (Fin n) L :=
    (IsScalarTower.toAlgHom R K L).mapMatrix
  have hM' : IsIntegral R (φ M) := hM.map φ
  have htr : algebraMap K L M.trace = (φ M).trace := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, Matrix.diag, map_sum]
    rfl
  rw [← isIntegral_algebraMap_iff (A := K) (B := L) , htr,
    Matrix.trace_eq_sum_roots_charpoly]
  refine IsIntegral.multiset_sum fun μ hμ => ?_
  have hroot : IsRoot (φ M).charpoly μ := (mem_roots'.1 hμ).2
  have hspec : μ ∈ spectrum L (φ M) := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  obtain ⟨p, hp, hp0⟩ := hM'
  refine ⟨p, hp, ?_⟩
  have h1 := spectrum.subset_polynomial_aeval (φ M) (p.map (algebraMap R L)) ⟨μ, hspec, rfl⟩
  have h2 : aeval (φ M) (p.map (algebraMap R L)) = 0 := by
    rw [aeval_map_algebraMap]; simpa [aeval_def] using hp0
  have : Nontrivial (Matrix (Fin n) (Fin n) L) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [spectrum.of_subsingleton] at hspec
    exact hspec
  rw [h2, spectrum.zero_eq, Set.mem_singleton_iff] at h1
  simpa [eval_map] using h1

theorem exists_coeffs_of_mem_adjoin {K : Type} [Field K] {n : ℕ} (N : Matrix (Fin n) (Fin n) K)
    {g : Matrix (Fin n) (Fin n) K} (hg : g ∈ Algebra.adjoin K {N}) :
    ∃ c : Fin n → K, g = ∑ k, c k • N ^ (k : ℕ) := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hg
  obtain ⟨p, rfl⟩ := hg
  have hmon := N.charpoly_monic
  have e : aeval N p = aeval N (p %ₘ N.charpoly) := by
    conv_lhs => rw [← modByMonic_add_div p N.charpoly]
    simp [Matrix.aeval_self_charpoly]
  change ∃ c : Fin n → K, aeval N p = _
  rw [e]
  by_cases h0 : p %ₘ N.charpoly = 0
  · exact ⟨0, by simp [h0]⟩
  refine ⟨fun k => (p %ₘ N.charpoly).coeff k, ?_⟩
  have hdeg : (p %ₘ N.charpoly).natDegree < n := by
    rw [natDegree_lt_iff_degree_lt h0]
    have := degree_modByMonic_lt p hmon
    rwa [Matrix.charpoly_degree_eq_dim, Fintype.card_fin] at this
  rw [aeval_eq_sum_range' hdeg, Finset.sum_range (fun i => (p %ₘ N.charpoly).coeff i • N ^ i)]

theorem det_hankel_trace_ne_zero (K : Type) [Field K] (n : ℕ) (N : Matrix (Fin n) (Fin n) K)
    (h : N.charpoly.Separable) :
    (Matrix.of fun j k : Fin n => (N ^ ((j : ℕ) + (k : ℕ))).trace).det ≠ 0 := by
  classical
  let L := AlgebraicClosure K
  let f : K →+* L := algebraMap K L
  set M := N.map f with hM
  have hcp : M.charpoly = N.charpoly.map f := Matrix.charpoly_map N f
  have hsepM : M.charpoly.Separable := hcp ▸ h.map
  have hnd : M.charpoly.roots.Nodup := nodup_roots hsepM
  have hcard : Multiset.card M.charpoly.roots = n := GlobalTheory.CharpolyPow.card_roots_charpoly M
  set s := M.charpoly.roots.toFinset with hsdef
  have hs : s.card = n := by rw [Multiset.toFinset_card_of_nodup hnd, hcard]
  have hsval : s.val = M.charpoly.roots := by
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnd]
  let e : Fin n ≃ s := (s.equivFin.trans (finCongr hs)).symm
  let lam : Fin n → L := fun i => (e i : L)
  have hinj : Function.Injective lam := Subtype.val_injective.comp e.injective
  have htr : ∀ m : ℕ, (M ^ m).trace = ∑ i, lam i ^ m := by
    intro m
    rw [Matrix.trace_eq_sum_roots_charpoly, GlobalTheory.CharpolyPow.roots_charpoly_pow, ← hsval,
      ← Finset.sum_eq_multiset_sum, ← Finset.sum_coe_sort s (fun x => x ^ m)]
    exact (Equiv.sum_comp e (fun x : s => (x : L) ^ m)).symm
  have hV : (Matrix.of fun j k : Fin n => (M ^ ((j : ℕ) + (k : ℕ))).trace) =
      (Matrix.vandermonde lam).transpose * Matrix.vandermonde lam := by
    ext j k
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.vandermonde_apply]
    rw [htr]
    simp only [pow_add]
  have hmap : f.mapMatrix (Matrix.of fun j k : Fin n => (N ^ ((j : ℕ) + (k : ℕ))).trace) =
      Matrix.of fun j k : Fin n => (M ^ ((j : ℕ) + (k : ℕ))).trace := by
    ext j k
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hM, ← Matrix.map_pow]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.trace, map_sum]
  intro h0
  have h1 : f (Matrix.of fun j k : Fin n => (N ^ ((j : ℕ) + (k : ℕ))).trace).det = 0 := by
    rw [h0, map_zero]
  rw [RingHom.map_det, hmap, hV, Matrix.det_mul, Matrix.det_transpose] at h1
  exact Matrix.det_vandermonde_ne_zero_iff.2 hinj (mul_self_eq_zero.1 h1)

theorem bounded_of_isIntegral_general {K Γ O : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [CommRing O] [Algebra O K]
    (hOv : ∀ y : O, v (algebraMap O K y) ≤ 1)
    (hvO : ∀ x : K, v x ≤ 1 → ∃ y : O, algebraMap O K y = x)
    (hint : ∀ x : K, IsIntegral O x → v x ≤ 1)
    {n : ℕ} (N : Matrix (Fin n) (Fin n) K) (hsep : N.charpoly.Separable) :
    ∃ c : Γ, ∀ g ∈ Algebra.adjoin K {N}, IsIntegral O g → ∀ i j, v (g i j) ≤ c := by
  classical
  obtain ⟨a, ha0, haN⟩ : ∃ a : K, a ≠ 0 ∧ ∀ i j, v (a * N i j) ≤ 1 := by
    by_cases h : ∀ i j, v (N i j) ≤ 1
    · exact ⟨1, one_ne_zero, fun i j => by simpa using h i j⟩
    · push_neg at h
      obtain ⟨i0, j0, h0⟩ := h
      obtain ⟨p, -, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
        (fun p => v (N p.1 p.2)) ⟨(i0, j0), Finset.mem_univ _⟩
      have hpos : 1 < v (N p.1 p.2) := lt_of_lt_of_le h0 (hp (i0, j0) (Finset.mem_univ _))
      have hne : N p.1 p.2 ≠ 0 := fun h => by
        rw [h, map_zero] at hpos; exact absurd hpos (not_lt.2 zero_le')
      refine ⟨(N p.1 p.2)⁻¹, inv_ne_zero hne, fun i j => ?_⟩
      rw [map_mul, map_inv₀, inv_mul_le_iff₀ (zero_lt_one.trans hpos), mul_one]
      exact hp (i, j) (Finset.mem_univ _)
  let N0 : Matrix (Fin n) (Fin n) O := fun i j => (hvO _ (haN i j)).choose
  let φ : Matrix (Fin n) (Fin n) O →ₐ[O] Matrix (Fin n) (Fin n) K := (Algebra.ofId O K).mapMatrix
  have hφN : φ N0 = a • N := by
    ext i j
    exact (hvO _ (haN i j)).choose_spec
  let B : ℕ → Matrix (Fin n) (Fin n) K := fun k => (a • N) ^ k
  have hBφ : ∀ k, B k = φ (N0 ^ k) := fun k => by simp only [B, map_pow, hφN]
  have hBent : ∀ k i j, v (B k i j) ≤ 1 := by
    intro k i j
    rw [hBφ k]
    exact hOv _
  have hBint : ∀ k, IsIntegral O (B k) := fun k => by
    rw [hBφ k]; exact (Algebra.IsIntegral.isIntegral (N0 ^ k)).map φ
  have hBpow : ∀ k, B k = a ^ k • N ^ k := fun k => _root_.smul_pow a N k
  set T : Matrix (Fin n) (Fin n) K := Matrix.of fun j k : Fin n => (B j * B k).trace
  have hT : T.det ≠ 0 := by
    have hS := det_hankel_trace_ne_zero K n N hsep
    have e : T = Matrix.of fun j k : Fin n => a ^ (j : ℕ) * (Matrix.of fun j k : Fin n =>
        a ^ (k : ℕ) * (Matrix.of fun j k : Fin n => (N ^ ((j : ℕ) + (k : ℕ))).trace) j k) j k := by
      ext j k
      simp only [T, Matrix.of_apply, hBpow, smul_mul_smul_comm, ← pow_add, Matrix.trace_smul,
        smul_eq_mul]
      ring
    rw [e, Matrix.det_mul_column, Matrix.det_mul_row]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun _ _ => pow_ne_zero _ ha0)
      (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun _ _ => pow_ne_zero _ ha0) hS)
  refine ⟨Finset.univ.sup fun p : Fin n × Fin n => v (T⁻¹ p.1 p.2), ?_⟩
  intro g hg hgi
  obtain ⟨c0, hc0⟩ := exists_coeffs_of_mem_adjoin N hg
  set c : Fin n → K := fun k => c0 k / a ^ (k : ℕ)
  have hgc : g = ∑ k, c k • B k := by
    rw [hc0]; refine Finset.sum_congr rfl fun k _ => ?_
    rw [hBpow, smul_smul, div_mul_cancel₀ _ (pow_ne_zero _ ha0)]
  have hcomm : ∀ k, Commute g (B k) := by
    intro k
    rw [hc0, hBpow]
    refine Commute.sum_left _ _ _ fun l _ => ?_
    exact ((Commute.pow_pow_self N l k).smul_left _).smul_right _
  have ht : ∀ j, v ((g * B j).trace) ≤ 1 := fun j =>
    hint _ (isIntegral_trace_of_isIntegral (g * B j)
      (isIntegral_mul_of_commute (hcomm j) hgi (hBint j)))
  have hTc : T.mulVec c = fun j : Fin n => (g * B j).trace := by
    ext j
    simp only [Matrix.mulVec, dotProduct, T, Matrix.of_apply]
    rw [hgc, Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_mul_assoc, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm (B k) (B j), mul_comm]
  have hc : c = T⁻¹.mulVec fun j => (g * B j).trace := by
    rw [← hTc, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hT),
      Matrix.one_mulVec]
  have hcv : ∀ k, v (c k) ≤ Finset.univ.sup fun p : Fin n × Fin n => v (T⁻¹ p.1 p.2) := by
    intro k
    rw [hc]
    simp only [Matrix.mulVec, dotProduct]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul, ← mul_one (Finset.univ.sup _)]
    exact mul_le_mul' (Finset.le_sup (f := fun p : Fin n × Fin n => v (T⁻¹ p.1 p.2))
      (Finset.mem_univ (k, l))) (ht l)
  intro i j
  rw [hgc, Matrix.sum_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, map_mul, ← mul_one (Finset.univ.sup _)]
  exact mul_le_mul' (hcv k) (hBent k i j)

theorem bounded_of_isIntegral : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (N : Matrix (Fin n) (Fin n) (w.adicCompletion E)), N.charpoly.Separable → ∃ c : WithZero (Multiplicative ℤ), ∀ g ∈ Algebra.adjoin (w.adicCompletion E) {N}, IsIntegral (w.adicCompletionIntegers E) g → ∀ i j, Valued.v (g i j) ≤ c := by
  intro E _ _ w n N hsep
  refine bounded_of_isIntegral_general (O := w.adicCompletionIntegers E) Valued.v
    (fun y => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 y.2)
    (fun x hx => ⟨⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx⟩, rfl⟩)
    (fun x hx => ?_) N hsep
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 y.2

end GlobalTheory.LocBounded
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAntisymmetrizedCupProductLeadingTerm
section
open GlobalTheory GlobalTheory.DI

set_option autoImplicit false

namespace GlobalTheory.DI.PhiLead
variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι]

theorem prodL_single (f : ι → V →+ V) (h : ι → ι → V →+ K) (j : ι) (vs : List V) :
    prodL f h vs {j} = ((-1 : ℤ) ^ vs.length) • (vs.map (fun v => ExteriorAlgebra.ι K (f j v))).prod := by
  induction vs with
  | nil => simp [prodL, oneC]
  | cons v vs ih =>
    have e : prodL f h (v :: vs) = Lop f h v (prodL f h vs) := rfl
    rw [e]
    simp only [Lop, Finset.singleton_nonempty, dite_true, Finset.min'_singleton, Finset.erase_singleton,
      Finset.not_nonempty_empty, dite_false, add_zero, Finset.card_singleton, ih, List.length_cons,
      List.map_cons, List.prod_cons, pow_succ]
    rw [mul_smul_comm, smul_smul]
    ring_nf

theorem alt_single (f : ι → V →+ V) (h : ι → ι → V →+ K) (a : ℕ) (v : Fin a → V) (j : ι) :
    alt f h a v {j} = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • ExteriorAlgebra.ιMulti K a (fun k => f j (v k)) := by
  have key : ∀ σ : Equiv.Perm (Fin a), prodL f h (List.ofFn (v ∘ σ)) {j} =
      ((-1 : ℤ) ^ a * ((Equiv.Perm.sign σ : ℤˣ) : ℤ)) • ExteriorAlgebra.ιMulti K a (fun k => f j (v k)) := by
    intro σ
    rw [prodL_single, List.length_ofFn, List.map_ofFn]
    have h1 : (List.ofFn ((fun v => ExteriorAlgebra.ι K (f j v)) ∘ v ∘ σ)).prod =
        ExteriorAlgebra.ιMulti K a ((fun k => f j (v k)) ∘ σ) := by
      rw [ExteriorAlgebra.ιMulti_apply]; rfl
    rw [h1, AlternatingMap.map_perm, mul_smul]
    simp [Units.smul_def]
  simp only [alt, Finset.sum_apply, Pi.smul_apply, key, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  have hs : ∀ σ : Equiv.Perm (Fin a), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) * ((-1 : ℤ) ^ a * ((Equiv.Perm.sign σ : ℤˣ) : ℤ)) = (-1 : ℤ) ^ a := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ <;> simp [hσ]
  simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

theorem gamma_iMulti (p : ℕ) (g : V →+ V) (γ : ExteriorAlgebra K V →+* ExteriorAlgebra K V)
    (hγ : IsGamma p g γ) (a : ℕ) (v : Fin a → V) :
    γ (ExteriorAlgebra.ιMulti K a v) = ExteriorAlgebra.ιMulti K a (fun k => g (v k)) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 1
  exact List.ofFn_inj.mpr (funext fun k => hγ.2 (v k))

theorem leading_term : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K), (∀ (a : ℕ) (v : Fin a → V) (j : ι), alt f h a v {j} = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • ExteriorAlgebra.ιMulti K a (fun k => f j (v k))) ∧ ∀ (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)) (j : ι) (γ : ExteriorAlgebra K V →+* ExteriorAlgebra K V), IsPhi p f h Φ → IsGamma p (f j) γ → ∀ a, ∀ x ∈ forms (Set.univ : Set K) (Set.univ : Set V) a, Φ x {j} = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • γ x := by
  intro K _ V _ _ ι _ p f h
  refine ⟨fun a v j => alt_single f h a v j, ?_⟩
  intro Φ j γ hΦ hγ a x hx
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, -, v, -, rfl⟩ := hx
    have hg : γ (b • ExteriorAlgebra.ιMulti K a v) = b ^ p • ExteriorAlgebra.ιMulti K a (fun k => f j (v k)) := by
      rw [Algebra.smul_def, map_mul, hγ.1, gamma_iMulti p (f j) γ hγ, ← Algebra.smul_def]
    rw [hΦ, Pi.smul_apply, alt_single, hg, smul_comm]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy, smul_add]
  | neg x _ hx => simp [hx, smul_neg]
end GlobalTheory.DI.PhiLead
end

