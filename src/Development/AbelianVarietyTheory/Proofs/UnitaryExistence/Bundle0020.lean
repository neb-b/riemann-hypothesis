module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0018
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaSqLawOfZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TwoDvdMultiplierOfThetaZActEqUnitMul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionSelfDualOfSelfDualLattice
section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat

theorem hermA_add_left {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → RA F E) :
    hermA c G (x + x') y = hermA c G x y + hermA c G x' y := by
  simp only [hermA, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem hermA_neg_left {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → RA F E) :
    hermA c G (-x) y = - hermA c G x y := by
  simp only [hermA, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem hermA_tmul_fv {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (t : FiniteAdeleRing (𝓞 F) F) (x y : Fin n → E) :
    hermA c G (fun i => t ⊗ₜ[F] x i) (fv F y) = t ⊗ₜ[F] (∑ a, ∑ b, x a * G a b * c (y b)) := by
  simp only [hermA, fv, sg, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    TensorProduct.tmul_sum, map_one, mul_one]
  rfl

theorem hat_selfDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (J : FractionalIdeal (𝓞 E)⁰ E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ x, c (c x) = x) → (∀ a b, c (G a b) = G b a) → G.det ≠ 0 → J ≠ 0 → (∀ v : Fin n → E, (∀ y ∈ L, (∑ a, ∑ b, v a * G a b * c (y b)) ∈ J) ↔ v ∈ L) → ∀ z : Fin n → RA F E, (∀ y ∈ L, hermA c G z (fv F y) ∈ hat1 F (J : Set E)) ↔ z ∈ (hat F (L : Set (Fin n → E))) := by
  intro F E _ _ _ _ _ n L c G J hfg hspan _ _ _ _ hL z
  have back : ∀ w ∈ hat F (L : Set (Fin n → E)), ∀ y ∈ L,
      hermA c G w (fv F y) ∈ hat1 F (J : Set E) := by
    intro w hw y hy
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨t, ht, x, hx, rfl⟩ := hw
      rw [hermA_tmul_fv]
      exact AddSubgroup.subset_closure ⟨t, ht, _, (hL x).2 hx y hy, rfl⟩
    | zero =>
      have : hermA c G 0 (fv F y) = 0 := by simp [hermA]
      rw [this]; exact zero_mem _
    | add w w' _ _ h h' => rw [hermA_add_left]; exact add_mem h h'
    | neg w _ h => rw [hermA_neg_left]; exact neg_mem h
  refine ⟨fun hz => ?_, fun hz => back z hz⟩
  obtain ⟨h1, -, h3, -⟩ := _root_.GlobalTheory.AdLat.hat_rational_points_and_approx F E n L hfg hspan
  obtain ⟨x, hx⟩ := h3 z
  have hxL : x ∈ L := by
    refine (hL x).1 fun y hy => ?_
    have h := sub_mem (hz y hy) (back _ hx y hy)
    have e : hermA c G z (fv F y) - hermA c G (z - fv F x) (fv F y)
        = hermA c G (fv F x) (fv F y) := by
      rw [sub_eq_add_neg z, hermA_add_left, hermA_neg_left]; ring
    rw [e] at h
    have e2 := hermA_tmul_fv c G (1 : FiniteAdeleRing (𝓞 F) F) x y
    exact ((_root_.GlobalTheory.AdLat.adelicCompletion_fractionalIdeal_properties F E).2.1 J _).1 (e2 ▸ h)
  have := add_mem hx ((h1 x).2 hxL)
  simpa using this

end GlobalTheory.AdLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.BoundedPowOfTriangularIsometry
section
namespace GlobalTheory.TriangularIsometryBoundedPowers

open Matrix

lemma det_block_ne {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ i : Fin (n + 1), ReciprocityTheory.ChartRestriction.G.FD.lminor B i ≠ 0) (j : Fin n) :
    (B.submatrix (Subtype.val : {c : Fin n // c < j} → Fin n)
      (Subtype.val : {c : Fin n // c < j} → Fin n)).det ≠ 0 := by
  have h := hB (Fin.castSucc j)
  unfold ReciprocityTheory.ChartRestriction.G.FD.lminor at h
  let e : Fin ((Fin.castSucc j : Fin (n + 1)) : ℕ) ≃ {c : Fin n // c < j} :=
    { toFun := fun k => ⟨Fin.castLE (Nat.le_of_lt_succ (Fin.castSucc j).isLt) k, by
        rw [Fin.lt_def]
        exact k.isLt⟩
      invFun := fun c => ⟨c.1.val, c.2⟩
      left_inv := fun k => Fin.ext rfl
      right_inv := fun c => Subtype.ext (Fin.ext rfl) }
  have e2 : (B.submatrix (Subtype.val : {c : Fin n // c < j} → Fin n)
      (Subtype.val : {c : Fin n // c < j} → Fin n)).submatrix e e =
      B.submatrix (Fin.castLE (Nat.le_of_lt_succ (Fin.castSucc j).isLt))
        (Fin.castLE (Nat.le_of_lt_succ (Fin.castSucc j).isLt)) := rfl
  rw [← Matrix.det_submatrix_equiv_self e, e2]
  exact h

lemma exists_col {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ i : Fin (n + 1), ReciprocityTheory.ChartRestriction.G.FD.lminor B i ≠ 0) (j : Fin n) :
    ∃ y : Fin n → ℂ, y j = 1 ∧ (∀ c, j < c → y c = 0) ∧
      ∀ a, a < j → ∑ c, B a c * y c = 0 := by
  classical
  set S := B.submatrix (Subtype.val : {c : Fin n // c < j} → Fin n)
      (Subtype.val : {c : Fin n // c < j} → Fin n) with hS
  have hdet : IsUnit S.det := isUnit_iff_ne_zero.mpr (det_block_ne B hB j)
  obtain ⟨w, hw⟩ : ∃ w : {c : Fin n // c < j} → ℂ, S *ᵥ w = fun p => -B p.1 j :=
    ⟨S⁻¹ *ᵥ fun p => -B p.1 j, by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]⟩
  refine ⟨fun c => if h : c < j then w ⟨c, h⟩ else if c = j then 1 else 0, by simp, ?_, ?_⟩
  · intro c hc
    simp [not_lt.mpr hc.le, hc.ne']
  · intro a ha
    rw [← Fintype.sum_subtype_add_sum_subtype (fun c => c < j)]
    have h1 : ∑ c : {c : Fin n // c < j}, B a c.1 *
        (if h : c.1 < j then w ⟨c.1, h⟩ else if c.1 = j then 1 else 0) = -B a j := by
      have := congrFun hw ⟨a, ha⟩
      simp only [Matrix.mulVec, dotProduct, hS, Matrix.submatrix_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [dite_eq_left c.2]
    have h2 : ∑ c : {c : Fin n // ¬ c < j}, B a c.1 *
        (if h : c.1 < j then w ⟨c.1, h⟩ else if c.1 = j then 1 else 0) = B a j := by
      rw [Finset.sum_eq_single (⟨j, lt_irrefl j⟩ : {c : Fin n // ¬ c < j})]
      · simp
      · intro c _ hc
        have : c.1 ≠ j := fun h => hc (Subtype.ext h)
        rw [dite_eq_right c.2, if_neg this, mul_zero]
      · simp
    rw [h1, h2]
    ring

lemma exists_diag {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (hH : B.IsHermitian)
    (hB : ∀ i : Fin (n + 1), ReciprocityTheory.ChartRestriction.G.FD.lminor B i ≠ 0) :
    ∃ (F : Matrix (Fin n) (Fin n) ℂ) (μ : Fin n → ℂ), F.BlockTriangular id ∧ F.det = 1 ∧
      (∀ i, μ i ≠ 0) ∧ Fᴴ * B * F = diagonal μ := by
  choose y hy1 hy0 hyB using exists_col B hB
  let F : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun c j => y j c
  have hFt : F.BlockTriangular id := fun c j h => hy0 j c h
  have hFd : F.det = 1 := by
    rw [Matrix.det_of_upperTriangular hFt]
    exact Finset.prod_eq_one fun i _ => hy1 i
  have hup : ∀ i j, i < j → (Fᴴ * B * F) i j = 0 := by
    intro i j hij
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun a _ => ?_
    rcases lt_or_ge i a with h | h
    · have : F a i = 0 := hy0 i a h
      rw [Matrix.conjTranspose_apply, this, star_zero, zero_mul]
    · have : (B * F) a j = 0 := by
        rw [Matrix.mul_apply]
        exact hyB j a (lt_of_le_of_lt h hij)
      rw [this, mul_zero]
  have hherm : (Fᴴ * B * F)ᴴ = Fᴴ * B * F := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hH.eq, Matrix.mul_assoc]
  have hD : Fᴴ * B * F = diagonal fun i => (Fᴴ * B * F) i i := by
    ext i j
    rcases lt_trichotomy i j with h | h | h
    · rw [hup i j h, Matrix.diagonal_apply_ne _ h.ne]
    · subst h; rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ h.ne', ← hherm, Matrix.conjTranspose_apply, hup j i h,
        star_zero]
  have hBd : B.det ≠ 0 := hB (Fin.last n)
  refine ⟨F, _, hFt, hFd, ?_, hD⟩
  have : (diagonal fun i => (Fᴴ * B * F) i i).det ≠ 0 := by
    rw [← hD, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hFd]
    simpa using hBd
  rw [Matrix.det_diagonal] at this
  exact fun i => Finset.prod_ne_zero_iff.mp this i (Finset.mem_univ i)

lemma diag_of_isometry {n : ℕ} (d : Matrix (Fin n) (Fin n) ℂ) (μ : Fin n → ℂ)
    (hd : d.BlockTriangular id) (hμ : ∀ i, μ i ≠ 0)
    (h : dᴴ * diagonal μ * d = diagonal μ) :
    ∃ l : Fin n → ℂ, d = diagonal l ∧ ∀ i, ‖l i‖ = 1 := by
  have hμd : (diagonal μ).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hμ i
  have hdet : (dᴴ).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_mul, h0, zero_mul, zero_mul] at this
    exact hμd this.symm
  have hu : IsUnit (dᴴ).det := isUnit_iff_ne_zero.mpr hdet
  have hlow : (dᴴ).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have : d j i = 0 := hd (show i < j from hij)
    rw [Matrix.conjTranspose_apply, this, star_zero]
  haveI := Matrix.invertibleOfIsUnitDet _ hu
  have hlow' := Matrix.blockTriangular_inv_of_blockTriangular hlow
  have h2 : diagonal μ * d = (dᴴ)⁻¹ * diagonal μ := by
    conv_rhs => rw [← h]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have hdiag : d = diagonal fun i => d i i := by
    ext i j
    rcases lt_trichotomy i j with hij | hij | hij
    · have h3 := congrFun (congrFun h2 i) j
      have h4 : (dᴴ)⁻¹ i j = 0 := hlow' (show OrderDual.toDual j < OrderDual.toDual i from hij)
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal, h4, zero_mul] at h3
      rw [Matrix.diagonal_apply_ne _ hij.ne]
      exact (mul_eq_zero.mp h3).resolve_left (hμ i)
    · subst hij; rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij.ne']
      exact hd hij
  refine ⟨_, hdiag, fun i => ?_⟩
  rw [hdiag, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal] at h
  have h5 := congrFun (congrFun h i) i
  simp only [Matrix.diagonal_apply_eq, Pi.star_apply] at h5
  have h6 := congrArg norm h5
  rw [norm_mul, norm_mul, norm_star] at h6
  have h7 : ‖μ i‖ ≠ 0 := norm_ne_zero_iff.mpr (hμ i)
  have h8 : ‖d i i‖ * ‖d i i‖ = 1 := by
    apply mul_right_cancel₀ h7
    linarith
  have h9 := norm_nonneg (d i i)
  nlinarith

lemma bounded_pow {n : ℕ} (g P : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℂ) (hP : P.det ≠ 0)
    (hl : ∀ i, ‖l i‖ = 1) (h : g * P = P * diagonal l) :
    ∃ R : ℝ, ∀ (k : ℕ) (i j : Fin n), ‖(g ^ k) i j‖ ≤ R := by
  have hPinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.2 hP)
  have hPinv' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.2 hP)
  have hg : g = P * diagonal l * P⁻¹ := by
    calc g = g * P * P⁻¹ := by rw [Matrix.mul_assoc, hPinv, Matrix.mul_one]
      _ = P * diagonal l * P⁻¹ := by rw [h]
  have hk : ∀ k : ℕ, g ^ k = P * diagonal (l ^ k) * P⁻¹ := by
    intro k
    induction k with
    | zero => simp [hPinv]
    | succ k ih =>
      have hd : diagonal (l ^ k * l) = diagonal (l ^ k) * diagonal l := (Matrix.diagonal_mul_diagonal _ _).symm
      rw [pow_succ, ih, hg, pow_succ, hd]
      calc P * diagonal (l ^ k) * P⁻¹ * (P * diagonal l * P⁻¹)
          = P * diagonal (l ^ k) * (P⁻¹ * P) * diagonal l * P⁻¹ := by simp only [Matrix.mul_assoc]
        _ = P * (diagonal (l ^ k) * diagonal l) * P⁻¹ := by rw [hPinv', Matrix.mul_one]; simp only [Matrix.mul_assoc]
  refine ⟨∑ i, ∑ j, ∑ a, ‖P i a‖ * ‖P⁻¹ a j‖, fun k i j => ?_⟩
  rw [hk, Matrix.mul_apply]
  have hterm : ∀ a, ‖(P * diagonal (l ^ k)) i a * P⁻¹ a j‖ = ‖P i a‖ * ‖P⁻¹ a j‖ := fun a => by
    rw [Matrix.mul_diagonal, norm_mul, norm_mul, Pi.pow_apply, norm_pow, hl, one_pow, mul_one]
  calc ‖∑ a, (P * diagonal (l ^ k)) i a * P⁻¹ a j‖ ≤ ∑ a, ‖(P * diagonal (l ^ k)) i a * P⁻¹ a j‖ := norm_sum_le _ _
    _ = ∑ a, ‖P i a‖ * ‖P⁻¹ a j‖ := Finset.sum_congr rfl fun a _ => hterm a
    _ ≤ ∑ j', ∑ a, ‖P i a‖ * ‖P⁻¹ a j'‖ :=
        Finset.single_le_sum (f := fun j' => ∑ a, ‖P i a‖ * ‖P⁻¹ a j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ∑ a, ‖P i' a‖ * ‖P⁻¹ a j'‖ :=
        Finset.single_le_sum (f := fun i' => ∑ j', ∑ a, ‖P i' a‖ * ‖P⁻¹ a j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)

theorem bounded_pow_of_triangular_isometry {n : ℕ} (g x b A : Matrix (Fin n) (Fin n) ℂ)
    (hx : Matrix.det x ≠ (0 : ℂ)) (hb : Matrix.BlockTriangular b id) (hA : Matrix.IsHermitian A)
    (hm : ∀ i : Fin (n + 1), ReciprocityTheory.ChartRestriction.G.FD.lminor A i ≠ (0 : ℂ)) (hg : g * x = x * b)
    (hiso : Matrix.transpose b * A * Matrix.map b (⇑(starRingEnd ℂ) : ℂ → ℂ) = A) :
    ∃ R : ℝ, ∀ (k : ℕ) (i j : Fin n), ‖(g ^ k) i j‖ ≤ R := by
  have hm' : ∀ i : Fin (n + 1), ReciprocityTheory.ChartRestriction.G.FD.lminor Aᵀ i ≠ 0 := by
    intro i
    have := hm i
    unfold ReciprocityTheory.ChartRestriction.G.FD.lminor at this ⊢
    rwa [← Matrix.transpose_submatrix, Matrix.det_transpose]
  have hiso' : bᴴ * Aᵀ * b = Aᵀ := by
    have := congrArg Matrix.transpose hiso
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      ← Matrix.mul_assoc] at this
    exact this
  obtain ⟨F, μ, hFt, hFd, hμ, hD⟩ := exists_diag Aᵀ hA.transpose hm'
  have hu : IsUnit F.det := by rw [hFd]; exact isUnit_one
  haveI := Matrix.invertibleOfIsUnitDet _ hu
  have hFd' : F * (F⁻¹ * b * F) = b * F := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  obtain ⟨l, hl, hl1⟩ := diag_of_isometry (F⁻¹ * b * F) μ
    (((Matrix.blockTriangular_inv_of_blockTriangular hFt).mul hb).mul hFt) hμ (by
      calc (F⁻¹ * b * F)ᴴ * diagonal μ * (F⁻¹ * b * F)
          = (F * (F⁻¹ * b * F))ᴴ * Aᵀ * (F * (F⁻¹ * b * F)) := by
            rw [← hD, Matrix.conjTranspose_mul F]
            simp only [Matrix.mul_assoc]
        _ = Fᴴ * (bᴴ * Aᵀ * b) * F := by
            rw [hFd', Matrix.conjTranspose_mul]
            simp only [Matrix.mul_assoc]
        _ = diagonal μ := by rw [hiso', hD])
  refine bounded_pow g (x * F) l ?_ hl1 ?_
  · rw [Matrix.det_mul, hFd, mul_one]; exact hx
  · rw [← hl, Matrix.mul_assoc x, hFd', ← Matrix.mul_assoc, hg, Matrix.mul_assoc]

end GlobalTheory.TriangularIsometryBoundedPowers
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCompatibleNormTowerProfinite
section
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.NormTower

theorem exists_eventually_dvd_sub {E : Type} [Field E] [NumberField E] (U : Ultrafilter ℕ) (s : ℕ → 𝓞 E)
    (n : ℕ) (hn : 0 < n) : ∃ t : 𝓞 E, ∀ᶠ j in (U : Filter ℕ), (n : 𝓞 E) ∣ s j - t := by
  have hI : Ideal.span {(n : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn.ne'
  haveI : Finite (𝓞 E ⧸ Ideal.span {(n : 𝓞 E)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  obtain ⟨c, hc⟩ := Ultrafilter.eq_pure_of_finite
    (U.map fun j => Ideal.Quotient.mk (Ideal.span {(n : 𝓞 E)}) (s j))
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨t, ?_⟩
  have h : {Ideal.Quotient.mk (Ideal.span {(n : 𝓞 E)}) t} ∈
      U.map fun j => Ideal.Quotient.mk (Ideal.span {(n : 𝓞 E)}) (s j) := by
    rw [hc]; exact Ultrafilter.mem_pure.2 rfl
  rw [Ultrafilter.mem_map] at h
  filter_upwards [h] with j hj
  exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hj)

theorem exists_norm_tower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (ν : ℕ → ℤ), (∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ)) → (∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n) → ∃ t : ℕ → 𝓞 E, (∀ n : ℕ, 0 < n → (n : 𝓞 E) ∣ t n * H.bar (t n) - (ν n : 𝓞 E)) ∧ (∀ n m : ℕ, 0 < n → 0 < m → (n : 𝓞 E) ∣ t (n * m) - t n) ∧ t l.M - 1 ∈ l.Mb := by
  intro E _ _ _ H l ν hcop hcomp
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hs : ∀ j : ℕ, ∃ t : 𝓞 E, ((j.factorial : ℕ) : 𝓞 E) ∣ t * H.bar t - (ν j.factorial : 𝓞 E) ∧
      (l.M ∣ j.factorial → t - 1 ∈ l.Mb) := fun j =>
    GlobalTheory.T.exists_hostNorm_mod_coprime_level_half E H l j.factorial (ν j.factorial) j.factorial_pos (hcop _ j.factorial_pos)
  choose s hs1 hs2 using hs
  let U : Ultrafilter ℕ := Filter.hyperfilter ℕ
  have hU : ∀ n : ℕ, 0 < n → ∀ᶠ j in (U : Filter ℕ), n ∣ j.factorial := by
    intro n hn
    have h : ∀ᶠ j : ℕ in Filter.cofinite, n ∣ j.factorial := by
      rw [Nat.cofinite_eq_atTop]
      filter_upwards [Filter.eventually_ge_atTop n] with j hj
      exact Nat.dvd_factorial hn hj
    exact h.filter_mono Filter.hyperfilter_le_cofinite
  have ht : ∀ n : ℕ, ∃ t : 𝓞 E, 0 < n → ∀ᶠ j in (U : Filter ℕ), (n : 𝓞 E) ∣ s j - t := by
    intro n
    by_cases hn : 0 < n
    · obtain ⟨t, h⟩ := exists_eventually_dvd_sub U s n hn
      exact ⟨t, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose t ht using ht
  refine ⟨t, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨j, ⟨a, ha⟩, m, hm⟩ := ((ht n hn).and (hU n hn)).exists
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · exact absurd (by rw [hm, h, mul_zero]) j.factorial_ne_zero
      · exact h
    obtain ⟨b, hb⟩ := hs1 j
    obtain ⟨c, hc⟩ := hcomp n m hn hm0
    rw [hm] at hb
    have hc' : ((ν (n * m) : ℤ) : 𝓞 E) - (ν n : 𝓞 E) = (n : 𝓞 E) * (c : 𝓞 E) := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hc
    have hsj : s j = t n + n * a := by rw [← ha]; ring
    rw [hsj, map_add (f := _), map_mul, map_natCast] at hb
    push_cast at hb
    exact ⟨m * b + c - (a * H.bar (t n) + t n * H.bar a + n * a * H.bar a), by linear_combination hb + hc'⟩
  · intro n m hn hm
    obtain ⟨j, h1, h2⟩ := ((ht n hn).and (ht (n * m) (Nat.mul_pos hn hm))).exists
    have h3 : (n : 𝓞 E) ∣ s j - t (n * m) := dvd_trans ⟨(m : 𝓞 E), by push_cast; rfl⟩ h2
    have := dvd_sub h1 h3
    convert this using 1
    ring
  · obtain ⟨j, ⟨a, ha⟩, h2⟩ := ((ht l.M hM).and (hU l.M hM)).exists
    have hMb : (l.M : 𝓞 E) ∈ l.Mb := by
      have : (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)} := Ideal.mem_span_singleton_self _
      rw [← l.prod] at this
      exact Ideal.mul_le_left this
    have h3 : (l.M : 𝓞 E) * a ∈ l.Mb := Ideal.mul_mem_right a _ hMb
    have h4 : t l.M - 1 = (s j - 1) - (l.M : 𝓞 E) * a := by rw [← ha]; ring
    rw [h4]
    exact Ideal.sub_mem _ (hs2 j h2) h3

end GlobalTheory.NormTower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelActionOverlapLeSourceChart
section
noncomputable section

namespace GlobalTheory.LevActCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem levelAction_overlap_le_source_chart {S : Type} [CommRing S] (φ : Xo.univ.t.G.left ⟶ Xo.univ.t.G.left) (x : Sp S ⟶ Xo.X)
    (i j : Xo.univ.t.PP.L.ι) :
    (snd (Over.mk x) Xo.univ.t.G).left ⁻¹ᵁ ((LB.div (Xo.univ.t.PP.L.pull φ) Xo.univ.t.PP.L).U ((fun _ => i), j)) ≤
      (PPx x).U (fun _ => j) :=
  fun _ hz => Set.mem_iInter.2 fun _ => hz.2

theorem overlap_le_tgt {S : Type} [CommRing S] (φ : Xo.univ.t.G.left ⟶ Xo.univ.t.G.left) {x x' : Sp S ⟶ Xo.X}
    (pm : Gx x ⟶ Gx x')
    (hp : pm ≫ (snd (Over.mk x') Xo.univ.t.G).left = (snd (Over.mk x) Xo.univ.t.G).left ≫ φ)
    (i j : Xo.univ.t.PP.L.ι) :
    (snd (Over.mk x) Xo.univ.t.G).left ⁻¹ᵁ ((LB.div (Xo.univ.t.PP.L.pull φ) Xo.univ.t.PP.L).U ((fun _ => i), j)) ≤
      pm ⁻¹ᵁ (PPx x').U (fun _ => i) := by
  intro z hz
  have h1 : ((snd (Over.mk x) Xo.univ.t.G).left ≫ φ).base z ∈ (Xo.univ.t.PP.L.U i : Set _) :=
    Set.mem_iInter.1 hz.1 PUnit.unit
  rw [← hp] at h1
  exact Set.mem_iInter.2 fun _ => h1

end GlobalTheory.LevActCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RatioSqEqDetJAut
section
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.ThetaRatio

theorem thetaChar_ofRealVec {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ)
    (z : Fin g → ℂ) : thetaChar τ (ofRealVec a) (ofRealVec b) z = theta a b z τ := by
  refine tsum_congr fun l => ?_
  have e : ((fun i => (l i : ℂ)) + ofRealVec a) = shiftVec a l := rfl
  rw [e, thetaTerm, eC]
  congr 1
  ring

theorem exists_eq_halfVec {g : ℕ} {c : Fin g → ℂ} (h : ∀ k, c k = 0 ∨ c k = 1 / 2) :
    ∃ n : Fin g → ℤ, c = ofRealVec (halfVec n) := by
  have : ∀ k, ∃ m : ℤ, c k = (((m : ℝ) / 2 : ℝ) : ℂ) := fun k => by
    rcases h k with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  choose n hn using this
  exact ⟨n, funext hn⟩

theorem ratio_sq_eq_det_jAut : ∀ (g : ℕ) (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ), γ ∈ Matrix.symplecticGroup (Fin g) ℤ → (∀ i j, (8 : ℤ) ∣ γ (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ γ (Sum.inr i) (Sum.inl j)) → (∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ, theta (halfVec 0) (halfVec 0) (zAct γ τ z) (spAct γ τ) ^ 2 = 1 * (jAut γ τ).det * eC (expArg γ τ z) * theta (halfVec 0) (halfVec 0) z τ ^ 2) → ∀ (c₁ c₂ : Fin g → ℂ), (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) → (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) → ∀ τ ∈ SiegelH (Fin g), ∀ (ρ : (Fin g → ℂ) → ℂ) (κ : ℂ), Differentiable ℂ ρ → (∀ z, ρ z ≠ 0) → ρ 0 = 1 → κ ≠ 0 → (∀ z, thetaChar (spAct γ τ) c₁ c₂ (zAct γ τ z) * ρ z = κ * thetaChar τ c₁ c₂ z) → κ ^ 2 = (jAut γ τ).det := by
  intro g γ hγ h8 h0 c₁ c₂ h₁ h₂ τ hτ ρ κ hρ hρ0 hρ1 hκ h
  obtain ⟨n, rfl⟩ := exists_eq_halfVec h₁
  obtain ⟨n', rfl⟩ := exists_eq_halfVec h₂
  simp only [thetaChar_ofRealVec] at h
  have hfix := halfChar_fixed_of_theta_transform_unit g γ hγ h8 1 n n' one_ne_zero h0 τ hτ
    (fun z => κ / ρ z) (by simpa only [div_eq_mul_inv] using (hρ.fun_inv hρ0).const_mul κ) (fun z => div_ne_zero hκ (hρ0 z))
    (fun z => by rw [div_mul_eq_mul_div, ← h z, mul_div_cancel_right₀ _ (hρ0 z)])
  have hlaw := ThetaCharMult.theta_sq_law_of_zero g γ hγ h8 1 n n' h0 hfix τ hτ
  have hE : Differentiable ℂ fun z => eC (expArg γ τ z) := by
    simp only [eC, expArg, dotProduct, mulVec]
    fun_prop
  have hθ : (fun z => theta (halfVec n) (halfVec n') z τ ^ 2) ≠ 0 := fun hz =>
    theta_ne_zero hτ (halfVec n) (halfVec n')
      (funext fun z => pow_eq_zero_iff (two_ne_zero) |>.1 (congrFun hz z))
  have key := entire_eq_zero_of_mul_continuous_eq_zero
    (f := fun z => (jAut γ τ).det * eC (expArg γ τ z) * ρ z ^ 2 - κ ^ 2)
    (((hE.const_mul _).mul (hρ.pow 2)).sub_const _)
    ((differentiable_theta hτ (halfVec n) (halfVec n')).continuous.pow 2) hθ
    (fun z => by
      have h1 := hlaw z
      have h2 : (theta (halfVec n) (halfVec n') (zAct γ τ z) (spAct γ τ) * ρ z) ^ 2 =
          (κ * theta (halfVec n) (halfVec n') z τ) ^ 2 := by rw [h z]
      show _ * theta (halfVec n) (halfVec n') z τ ^ 2 = 0
      linear_combination h2 - ρ z ^ 2 * h1) 0
  have e0 : eC (expArg γ τ 0) = 1 := by simp [expArg, eC]
  simp only [e0, hρ1] at key
  linear_combination -key

end GlobalTheory.ThetaRatio
end
end

