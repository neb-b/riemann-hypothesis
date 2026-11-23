module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvrOrderExistsUnitEqUnitMulZpowIff
section
namespace GlobalTheory.CompanionTheory.Ar.Flat

section
variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

private theorem mul_zpow_mul_inv_pow_mul_zpow_lemma {G : Type*} [CommGroup G] (x y g : G) (k j a : ℤ)
    (M : ℕ) :
    (x * g ^ k) ^ a * ((y * g ^ j) ^ M)⁻¹ = x ^ a * (y ^ M)⁻¹ * g ^ (k * a - j * M) := by
  rw [mul_zpow, ← zpow_mul, mul_pow, ← zpow_natCast (g ^ j), ← zpow_mul, zpow_sub, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

theorem dvrOrder_exists_eq_unit_mul_zpow_iff {t : R} (ht : Irreducible t) (v : Rˣ) (e : ℤ) :
    (∃ r : R, algebraMap R K r = algebraMap R K v * algebraMap R K t ^ e) ↔ 0 ≤ e := by
  have ht0 : algebraMap R K t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 ht.ne_zero
  constructor
  · rintro ⟨r, hr⟩
    by_contra he
    obtain ⟨n, hn⟩ : ∃ n : ℕ, e = -((n + 1 : ℕ) : ℤ) := ⟨(-e - 1).toNat, by omega⟩
    have key : algebraMap R K (r * t ^ (n + 1)) = algebraMap R K v := by
      rw [map_mul, map_pow, hr, hn, zpow_neg, zpow_natCast, mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero _ ht0), mul_one]
    have hu : IsUnit (r * t ^ (n + 1)) := by
      rw [IsFractionRing.injective R K key]
      exact v.isUnit
    rw [pow_succ] at hu
    exact ht.1 (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hu))
  · intro he
    lift e to ℕ using he
    exact ⟨v * t ^ e, by rw [map_mul, map_pow, zpow_natCast]⟩

theorem dvrOrder_exists_unit_eq_unit_mul_zpow_iff {t : R} (ht : Irreducible t) (v : Rˣ) (e : ℤ) :
    (∃ r : Rˣ, algebraMap R K r = algebraMap R K v * algebraMap R K t ^ e) ↔ e = 0 := by
  constructor
  · rintro ⟨r, hr⟩
    have ht0 : algebraMap R K t ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 ht.ne_zero
    have h1 : 0 ≤ e := (GlobalTheory.CompanionTheory.Ar.Flat.dvrOrder_exists_eq_unit_mul_zpow_iff (K := K) ht v e).1 ⟨r, hr⟩
    have h2 : 0 ≤ -e := by
      refine (GlobalTheory.CompanionTheory.Ar.Flat.dvrOrder_exists_eq_unit_mul_zpow_iff (K := K) ht r (-e)).1 ⟨v, ?_⟩
      rw [hr, zpow_neg, mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ ht0), mul_one]
    omega
  · rintro rfl
    exact ⟨v, by rw [zpow_zero, mul_one]⟩

end

theorem dvr_order_integral_unit_iff : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (ϖ : R) (s : K), ϖ ≠ 0 → ¬ IsUnit ϖ → s ≠ 0 → ∃ (m : ℕ) (n : ℤ), 0 < m ∧ ∀ (M : ℕ) (a : ℤ), ((∃ r : R, algebraMap R K r * s ^ M = algebraMap R K ϖ ^ a) ↔ (M : ℤ) * n ≤ a * m) ∧ ((∃ r : Rˣ, algebraMap R K r * s ^ M = algebraMap R K ϖ ^ a) ↔ (M : ℤ) * n = a * m) := by
  intro R K _ _ _ _ _ _ ϖ s hϖ hϖu hs
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hπ0 : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ hinj).2 hπ.ne_zero
  obtain ⟨φ, hφ⟩ : ∃ φ : Rˣ →* Kˣ, ∀ x : Rˣ, ((φ x : Kˣ) : K) = algebraMap R K x :=
    ⟨Units.map (algebraMap R K).toMonoidHom, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Kˣ, (g : K) = algebraMap R K π := ⟨Units.mk0 _ hπ0, rfl⟩
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hϖ hπ
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso
      apply hϖu
      rw [hu, h, pow_zero, mul_one]
      exact u.isUnit
    · exact h
  have hϖK : algebraMap R K ϖ = algebraMap R K u * algebraMap R K π ^ (k : ℤ) := by
    rw [hu, map_mul, map_pow, zpow_natCast]
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := R) s
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply hs
    rw [← hxy, map_zero, zero_div]
  obtain ⟨i, w₁, hx⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ
  obtain ⟨l, w₂, hy'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hπ
  obtain ⟨w, hw⟩ : ∃ w : Rˣ, w = w₁ * w₂⁻¹ := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j : ℤ, j = (i : ℤ) - l := ⟨_, rfl⟩
  have hsK : s = algebraMap R K w * algebraMap R K π ^ j := by
    rw [← hxy, hx, hy', hw, hj]
    simp only [Units.val_mul, map_mul, map_units_inv, map_pow, zpow_sub₀ hπ0, zpow_natCast]
    ring
  refine ⟨k, j, hk, fun M a => ?_⟩
  obtain ⟨v, hv⟩ : ∃ v : Rˣ, v = u ^ a * (w ^ M)⁻¹ := ⟨_, rfl⟩
  have hU : (φ u * g ^ (k : ℤ)) ^ a * ((φ w * g ^ j) ^ M)⁻¹ =
      φ v * g ^ ((k : ℤ) * a - j * M) := by
    rw [mul_zpow_mul_inv_pow_mul_zpow_lemma, hv, map_mul, map_zpow, map_inv, map_pow]
  have hU' := congrArg (fun z : Kˣ => (z : K)) hU
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val,
    Units.val_pow_eq_pow_val, hφ, hg] at hU'
  have hX : ∀ r : K, r * s ^ M = algebraMap R K ϖ ^ a ↔
      r = algebraMap R K v * algebraMap R K π ^ ((k : ℤ) * a - j * M) := by
    intro r
    rw [← hU', ← hϖK, ← hsK, ← div_eq_mul_inv, eq_div_iff (pow_ne_zero _ hs)]
  constructor
  · rw [exists_congr fun r : R => hX (algebraMap R K r),
      GlobalTheory.CompanionTheory.Ar.Flat.dvrOrder_exists_eq_unit_mul_zpow_iff (K := K) hπ v ((k : ℤ) * a - j * M)]
    constructor <;> intro h <;> linarith
  · rw [exists_congr fun r : Rˣ => hX (algebraMap R K r),
      GlobalTheory.CompanionTheory.Ar.Flat.dvrOrder_exists_unit_eq_unit_mul_zpow_iff (K := K) hπ v ((k : ℤ) * a - j * M)]
    constructor <;> intro h <;> linarith

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsAdaptedUnimodular
section
open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.ToricBasis

private theorem transpose_mul_mul_apply_eq_dot_product_mul_vec {m n R : Type*} [Fintype m]
    [CommSemiring R] (P : Matrix m n R) (A : Matrix m m R) (x y : n) :
    (Pᵀ * A * P) x y = Pᵀ x ⬝ᵥ A *ᵥ Pᵀ y := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem exists_isCompl_ker {g : ℕ} (f : (Fin g → ℤ) →ₗ[ℤ] (Fin g → ℤ)) :
    ∃ M : Submodule ℤ (Fin g → ℤ), IsCompl M (LinearMap.ker f) := by
  haveI : Module.Free ℤ (LinearMap.range f) := Module.free_of_finite_type_torsion_free'
  obtain ⟨t, ht⟩ :=
    LinearMap.exists_rightInverse_of_surjective f.rangeRestrict (LinearMap.range_rangeRestrict f)
  have hft : ∀ y : LinearMap.range f, f (t y) = y := fun y =>
    congrArg Subtype.val (LinearMap.congr_fun ht y)
  refine ⟨LinearMap.range t, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro x ⟨y, rfl⟩ hy
    rw [LinearMap.mem_ker] at hy
    have hy0 : y = 0 := Subtype.ext ((hft y).symm.trans hy)
    rw [hy0, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    rw [Submodule.mem_sup]
    refine ⟨t (f.rangeRestrict x), LinearMap.mem_range_self _ _, x - t (f.rangeRestrict x), ?_,
      by abel⟩
    rw [LinearMap.mem_ker, map_sub, hft, sub_eq_zero]
    rfl

theorem exists_adapted_basis {g : ℕ} (f : (Fin g → ℤ) →ₗ[ℤ] (Fin g → ℤ)) :
    ∃ (r s : ℕ) (b : Module.Basis (Fin r ⊕ Fin s) ℤ (Fin g → ℤ)),
      (∀ k, f (b (Sum.inr k)) = 0) ∧
      ∀ x : Fin r → ℤ, f (∑ a, x a • b (Sum.inl a)) = 0 → x = 0 := by
  obtain ⟨M, hM⟩ := GlobalTheory.CompanionTheory.ToricBasis.exists_isCompl_ker f
  haveI : Module.Free ℤ M := Module.free_of_finite_type_torsion_free'
  haveI : Module.Free ℤ (LinearMap.ker f) := Module.free_of_finite_type_torsion_free'
  obtain ⟨bM⟩ : Nonempty (Module.Basis (Fin (Module.finrank ℤ M)) ℤ M) :=
    ⟨Module.finBasis ℤ M⟩
  obtain ⟨bK⟩ : Nonempty (Module.Basis (Fin (Module.finrank ℤ (LinearMap.ker f))) ℤ
      (LinearMap.ker f)) := ⟨Module.finBasis ℤ (LinearMap.ker f)⟩
  have hb : ∀ i, (bM.prod bK).map (Submodule.prodEquivOfIsCompl M (LinearMap.ker f) hM) i =
      ((bM.prod bK i).1 : Fin g → ℤ) + ((bM.prod bK i).2 : Fin g → ℤ) := fun i => by
    rw [Module.Basis.map_apply, Submodule.coe_prodEquivOfIsCompl']
  refine ⟨_, _, (bM.prod bK).map (Submodule.prodEquivOfIsCompl M (LinearMap.ker f) hM), ?_, ?_⟩
  · intro k
    rw [hb, Module.Basis.prod_apply]
    simp only [Sum.elim_inr, Function.comp_apply, LinearMap.inr_apply, ZeroMemClass.coe_zero,
      zero_add]
    exact LinearMap.mem_ker.mp (bK k).2
  · intro x hx
    have hinl : ∀ a, (bM.prod bK).map (Submodule.prodEquivOfIsCompl M (LinearMap.ker f) hM)
        (Sum.inl a) = (bM a : Fin g → ℤ) := fun a => by
      rw [hb, Module.Basis.prod_apply]
      simp only [Sum.elim_inl, Function.comp_apply, LinearMap.inl_apply, ZeroMemClass.coe_zero,
        add_zero]
    simp only [hinl] at hx
    have hmem : (∑ a, x a • (bM a : Fin g → ℤ)) ∈ M :=
      Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (bM a).2
    have h0 := Submodule.disjoint_def.mp hM.disjoint _ hmem (LinearMap.mem_ker.mpr hx)
    have h0' : ∑ a, x a • bM a = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simpa only [Submodule.coe_smul, ZeroMemClass.coe_zero] using h0
    funext a
    exact Fintype.linearIndependent_iff.mp bM.linearIndependent x h0' a

theorem cast_quad {g : ℕ} (A : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ) :
    star (fun i => (v i : ℝ)) ⬝ᵥ (A.map (fun x : ℤ => (x : ℝ))) *ᵥ (fun i => (v i : ℝ))
      = ((v ⬝ᵥ A *ᵥ v : ℤ) : ℝ) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, star_trivial,
    Int.cast_sum, Int.cast_mul]

theorem quad_nonneg {g : ℕ} {A : Matrix (Fin g) (Fin g) ℤ}
    (hA : (A.map (fun x : ℤ => (x : ℝ))).PosSemidef) (v : Fin g → ℤ) : 0 ≤ v ⬝ᵥ A *ᵥ v := by
  have h := hA.dotProduct_mulVec_nonneg (fun i => (v i : ℝ))
  rw [GlobalTheory.CompanionTheory.ToricBasis.cast_quad] at h
  exact_mod_cast h

theorem mulVec_eq_zero_of_quad {g : ℕ} {A : Matrix (Fin g) (Fin g) ℤ}
    (hA : (A.map (fun x : ℤ => (x : ℝ))).PosSemidef) (v : Fin g → ℤ) (h : v ⬝ᵥ A *ᵥ v = 0) :
    A *ᵥ v = 0 := by
  have h1 : star (fun i => (v i : ℝ)) ⬝ᵥ (A.map (fun x : ℤ => (x : ℝ))) *ᵥ
      (fun i => (v i : ℝ)) = 0 := by
    rw [GlobalTheory.CompanionTheory.ToricBasis.cast_quad, h, Int.cast_zero]
  have h2 := hA.dotProduct_mulVec_zero_iff.mp h1
  funext i
  have h3 := congrFun h2 i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at h3 ⊢
  exact_mod_cast h3

theorem symm_of_posSemidef {g : ℕ} {A : Matrix (Fin g) (Fin g) ℤ}
    (hA : (A.map (fun x : ℤ => (x : ℝ))).PosSemidef) : Aᵀ = A := by
  ext i j
  have h := hA.isHermitian.apply i j
  simp only [Matrix.map_apply, star_trivial] at h
  rw [Matrix.transpose_apply]
  exact_mod_cast h

theorem exists_adapted_unimodular :
    ∀ (g : ℕ) (J : Type) [Fintype J] (B : J → Matrix (Fin g) (Fin g) ℤ), (∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef) → ∃ (r s : ℕ) (e : Fin r ⊕ Fin s ≃ Fin g) (Q : Matrix (Fin g) (Fin g) ℤ), IsUnit Q.det ∧ (∀ j k l, ((Qᵀ * B j * Q).submatrix e e) (Sum.inr k) l = 0 ∧ ((Qᵀ * B j * Q).submatrix e e) l (Sum.inr k) = 0) ∧ ((((Qᵀ * (∑ j, B j) * Q).submatrix e e).toBlocks₁₁).map (fun x : ℤ => (x : ℝ))).PosDef := by
  intro g J _ B hB
  obtain ⟨S, hSdef⟩ : ∃ S : Matrix (Fin g) (Fin g) ℤ, S = ∑ j, B j := ⟨_, rfl⟩
  rw [← hSdef]
  have hSpsd : (S.map (fun x : ℤ => (x : ℝ))).PosSemidef := by
    have hmap : S.map (fun x : ℤ => (x : ℝ)) = ∑ j, (B j).map (fun x : ℤ => (x : ℝ)) := by
      ext i i'
      simp only [hSdef, Matrix.map_apply, Matrix.sum_apply, Int.cast_sum]
    rw [hmap]
    exact Matrix.posSemidef_sum Finset.univ fun j _ => hB j
  obtain ⟨r, s, b, hker, hinj⟩ := GlobalTheory.CompanionTheory.ToricBasis.exists_adapted_basis (Matrix.mulVecLin S)
  have hcard : g = r + s := by
    have h := Module.finrank_eq_card_basis b
    rwa [Module.finrank_fin_fun ℤ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h
  obtain ⟨e⟩ : Nonempty (Fin r ⊕ Fin s ≃ Fin g) := ⟨finSumFinEquiv.trans (finCongr hcard.symm)⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix (Fin g) (Fin g) ℤ,
      Q = (Pi.basisFun ℤ (Fin g)).toMatrix (b.reindex e) := ⟨_, rfl⟩
  have hQ : ∀ i m, Q i m = b (e.symm m) i := by
    intro i m
    rw [hQdef, Module.Basis.toMatrix_apply, Pi.basisFun_repr, Module.Basis.reindex_apply]
  have hunit : IsUnit Q.det := by
    rw [hQdef]
    letI := Module.Basis.invertibleToMatrix (Pi.basisFun ℤ (Fin g)) (b.reindex e)
    exact Matrix.isUnit_det_of_invertible _
  have hcol : ∀ α, Qᵀ (e α) = b α := fun α => funext fun i => by
    rw [Matrix.transpose_apply, hQ, e.symm_apply_apply]
  have hentry : ∀ (X : Matrix (Fin g) (Fin g) ℤ) (α β : Fin r ⊕ Fin s),
      ((Qᵀ * X * Q).submatrix e e) α β = b α ⬝ᵥ X *ᵥ b β := by
    intro X α β
    rw [Matrix.submatrix_apply, transpose_mul_mul_apply_eq_dot_product_mul_vec, hcol, hcol]
  have hBk : ∀ j k, B j *ᵥ b (Sum.inr k) = 0 := by
    intro j k
    have hSk : S *ᵥ b (Sum.inr k) = 0 := by
      have h := hker k
      rwa [Matrix.mulVecLin_apply] at h
    have hsum : ∑ i, b (Sum.inr k) ⬝ᵥ B i *ᵥ b (Sum.inr k) = 0 := by
      rw [← dotProduct_sum, ← Matrix.sum_mulVec, ← hSdef, hSk, dotProduct_zero]
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      GlobalTheory.CompanionTheory.ToricBasis.quad_nonneg (hB i) _)).mp hsum j
        (Finset.mem_univ _)
    exact GlobalTheory.CompanionTheory.ToricBasis.mulVec_eq_zero_of_quad (hB j) _ hj
  refine ⟨r, s, e, Q, hunit, ?_, ?_⟩
  · intro j k l
    refine ⟨?_, ?_⟩
    · rw [hentry, Matrix.dotProduct_mulVec,
        ← GlobalTheory.CompanionTheory.ToricBasis.symm_of_posSemidef (hB j), Matrix.vecMul_transpose, hBk,
        zero_dotProduct]
    · rw [hentry, hBk, dotProduct_zero]
  · obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin g) (Fin r) ℤ, ∀ i a, C i a = b (Sum.inl a) i :=
      ⟨Matrix.of fun i a => b (Sum.inl a) i, fun _ _ => rfl⟩
    have hCt : ∀ a, Cᵀ a = b (Sum.inl a) := fun a => funext fun i => by
      rw [Matrix.transpose_apply, hC]
    have hMC : ((Qᵀ * S * Q).submatrix e e).toBlocks₁₁ = Cᵀ * S * C := by
      ext a a'
      rw [transpose_mul_mul_apply_eq_dot_product_mul_vec, hCt, hCt, ← hentry]
      rfl
    rw [hMC]
    have hN : (Cᵀ * S * C).map (fun x : ℤ => (x : ℝ)) =
        (C.map (fun x : ℤ => (x : ℝ)))ᴴ * S.map (fun x : ℤ => (x : ℝ)) *
          C.map (fun x : ℤ => (x : ℝ)) := by
      ext a a'
      simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.transpose_apply, star_trivial, Int.cast_sum, Int.cast_mul]
    have hNpsd : ((Cᵀ * S * C).map (fun x : ℤ => (x : ℝ))).PosSemidef := by
      rw [hN]
      exact hSpsd.conjTranspose_mul_mul_same _
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hNpsd.isHermitian ?_
    intro x hx
    refine lt_of_le_of_ne (hNpsd.dotProduct_mulVec_nonneg x) fun h0 => ?_
    have hNx := hNpsd.dotProduct_mulVec_zero_iff.mp h0.symm
    have hdetN : ((Cᵀ * S * C).map (fun x : ℤ => (x : ℝ))).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, hNx⟩
    have hdetZ : (Cᵀ * S * C).det = 0 := by
      have h1 : (((Cᵀ * S * C).det : ℤ) : ℝ) = 0 := by
        rw [← hdetN]
        have h2 := RingHom.map_det (Int.castRingHom ℝ) (Cᵀ * S * C)
        rw [RingHom.mapMatrix_apply] at h2
        exact h2
      exact_mod_cast h1
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetZ
    have hquad : (C *ᵥ v) ⬝ᵥ S *ᵥ (C *ᵥ v) = 0 := by
      have h3 : v ⬝ᵥ (Cᵀ * S * C) *ᵥ v = (C *ᵥ v) ⬝ᵥ S *ᵥ (C *ᵥ v) := by
        rw [← Matrix.mulVec_mulVec v (Cᵀ * S) C, ← Matrix.mulVec_mulVec (C *ᵥ v) Cᵀ S,
          Matrix.dotProduct_mulVec v Cᵀ, Matrix.vecMul_transpose C v]
      rw [← h3, hv0, dotProduct_zero]
    have hSw := GlobalTheory.CompanionTheory.ToricBasis.mulVec_eq_zero_of_quad hSpsd
      (C *ᵥ v) hquad
    have hCv : C *ᵥ v = ∑ a, v a • b (Sum.inl a) := by
      ext i
      rw [Finset.sum_apply]
      simp only [Matrix.mulVec, dotProduct, hC, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    exact hv (hinj v (by rw [Matrix.mulVecLin_apply, ← hCv]; exact hSw))

end GlobalTheory.CompanionTheory.ToricBasis
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsSurjectiveZmodOfNeZero
section
open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.QuotPrime

theorem exists_surjective_zmod_of_ne_top (X : Type*) [AddCommGroup X] [Module.Finite ℤ X]
    (Y : AddSubgroup X) (hY : Y ≠ ⊤) :
    ∃ (l : ℕ) (_ : l.Prime) (ψ : X →+ ZMod l), Function.Surjective ψ ∧ ∀ y ∈ Y, ψ y = 0 := by
  have hY' : Y.toIntSubmodule ≠ ⊤ := by
    intro h
    apply hY
    rw [eq_top_iff]
    intro x _
    have : x ∈ Y.toIntSubmodule := by rw [h]; trivial
    exact this
  obtain ⟨M, hM, hYM⟩ := (eq_top_or_exists_le_coatom Y.toIntSubmodule).resolve_left hY'
  have hs : IsSimpleModule ℤ (X ⧸ M) := isSimpleModule_iff_isCoatom.2 hM
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hs
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, I = Ideal.span {p} := ⟨_, (Ideal.span_singleton_generator I).symm⟩
  have hp0 : p ≠ 0 := by
    rintro rfl
    have h : (⊥ : Ideal ℤ).IsMaximal := by simpa using hI
    exact Int.not_isField (Ring.isField_iff_maximal_bot.2 h)
  have hp : Prime p := (Ideal.span_singleton_prime hp0).1 hI.isPrime
  refine ⟨p.natAbs, Int.prime_iff_natAbs_prime.1 hp,
    ((Int.quotientSpanEquivZMod p).toAddEquiv.toAddMonoidHom.comp
      e.toAddEquiv.toAddMonoidHom).comp M.mkQ.toAddMonoidHom, ?_, ?_⟩
  · exact ((Int.quotientSpanEquivZMod p).surjective.comp e.surjective).comp M.mkQ_surjective
  · intro y hy
    have h0 : M.mkQ y = 0 := (Submodule.Quotient.mk_eq_zero M).2 (hYM hy)
    change (Int.quotientSpanEquivZMod p) (e (M.mkQ y)) = 0
    rw [h0, map_zero, map_zero]

theorem exists_surjective_zmod_of_ne_zero :
    ∀ (k X : Type) [Field k] [AddCommGroup X] [Module.Finite ℤ X] (Y : AddSubgroup X)
      (δ : X →+ k), δ ≠ 0 → (∀ y ∈ Y, δ y = 0) →
      ∃ (l : ℕ) (_ : l.Prime) (ψ : X →+ ZMod l), Function.Surjective ψ ∧ ∀ y ∈ Y, ψ y = 0 := by
  intro k X _ _ _ Y δ hδ hY
  refine exists_surjective_zmod_of_ne_top X Y ?_
  rintro rfl
  exact hδ (AddMonoidHom.ext fun x => hY x trivial)

end GlobalTheory.CompanionTheory.QuotPrime
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FcIndepDetNeZeroOfRank
section
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem fcIndep_det_ne_zero_of_rank {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (h : B.rank = n) :
    B.det ≠ 0 := by
  have hs : Function.Surjective B.mulVecLin := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    simpa [Matrix.rank] using h
  have hu : IsUnit B := Matrix.mulVec_surjective_iff_isUnit.mp hs
  exact ((Matrix.isUnit_iff_isUnit_det B).mp hu).ne_zero

theorem fcIndep : ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin q ⊕ Fin p) ℂ) (Φ : Matrix (Fin q ⊕ Fin p) (Fin q) ℂ), A * Φ = 0 → A.rank = p → Φ.rank = q → (Φᴴ * Φ).det ≠ 0 ∧ (fromRows Φᴴ A).det ≠ 0 ∧ ∀ N : Matrix (Fin q) (Fin q ⊕ Fin p) ℂ, (fromRows N A).det * (Φᴴ * Φ).det = (fromRows Φᴴ A).det * (N * Φ).det := by
  intro p q A Φ h0 hA hΦ
  have h1 : (Φᴴ * Φ).det ≠ 0 := by
    apply fcIndep_det_ne_zero_of_rank
    open ComplexOrder in rw [Matrix.rank_conjTranspose_mul_self, hΦ]
  have h2 : (A * Aᴴ).det ≠ 0 := by
    apply fcIndep_det_ne_zero_of_rank
    open ComplexOrder in rw [Matrix.rank_self_mul_conjTranspose, hA]
  have key : ∀ N : Matrix (Fin q) (Fin q ⊕ Fin p) ℂ,
      (fromRows N A).det * (fromCols Φ Aᴴ).det = (N * Φ).det * (A * Aᴴ).det := by
    intro N
    rw [← Matrix.det_mul, Matrix.fromRows_mul_fromCols, h0, Matrix.det_fromBlocks_zero₂₁]
  have h3 : (fromRows Φᴴ A).det * (fromCols Φ Aᴴ).det ≠ 0 := by
    rw [key]; exact mul_ne_zero h1 h2
  refine ⟨h1, left_ne_zero_of_mul h3, fun N => ?_⟩
  apply mul_right_cancel₀ (right_ne_zero_of_mul h3)
  have a := key N
  have b := key Φᴴ
  linear_combination (Φᴴ * Φ).det * a - (N * Φ).det * b

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFreeHom
section
noncomputable section
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd

def FiniteFreeHom {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) : Prop :=
  letI := φ.toAlgebra
  Module.Free A B ∧ Module.Finite A B

end GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FromRowsMulFromColsSplit
section
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem fromRows_mul_fromCols_split {R : Type} [CommRing R] {p q : ℕ}
    (J : Matrix (Fin p ⊕ Fin q) (Fin p) R) (S : Matrix (Fin q) (Fin p ⊕ Fin q) R)
    (J' : Matrix (Fin p) (Fin p ⊕ Fin q) R) (S' : Matrix (Fin p ⊕ Fin q) (Fin q) R)
    (h0 : S * J = 0) (hJ : J' * J = 1) (hS : S * S' = 1) :
    Matrix.fromRows (J' * (1 - S' * S)) S * Matrix.fromCols J S' = 1 := by
  rw [Matrix.fromRows_mul_fromCols]
  have e1 : J' * (1 - S' * S) * J = 1 := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc,
      h0, Matrix.mul_zero, sub_zero, hJ]
  have e2 : J' * (1 - S' * S) * S' = 0 := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc,
      hS, Matrix.mul_zero, sub_self]
  rw [e1, e2, h0, hS, Matrix.fromBlocks_one]

theorem splitExact_of_rank : ∀ (R : Type) [CommRing R] (p q : ℕ) (J : Matrix (Fin p ⊕ Fin q) (Fin p) R) (S : Matrix (Fin q) (Fin p ⊕ Fin q) R), S * J = 0 → (∃ J' : Matrix (Fin p) (Fin p ⊕ Fin q) R, J' * J = 1) → (∃ S' : Matrix (Fin p ⊕ Fin q) (Fin q) R, S * S' = 1) → (∀ S' : Matrix (Fin p ⊕ Fin q) (Fin q) R, S * S' = 1 → IsUnit (Matrix.fromCols J S').det) ∧ ∀ v, S.mulVec v = 0 ↔ ∃ w, J.mulVec w = v := by
  rintro R inst p q J S h0 ⟨J', hJ⟩ ⟨S₀, hS₀⟩
  refine ⟨fun S' hS => ?_, fun v => ⟨fun hv => ?_, ?_⟩⟩
  · exact Matrix.isUnit_det_of_left_inverse (fromRows_mul_fromCols_split J S J' S' h0 hJ hS)
  · have hMN := fromRows_mul_fromCols_split J S J' S₀ h0 hJ hS₀
    have hNM : Matrix.fromCols J S₀ * Matrix.fromRows (J' * (1 - S₀ * S)) S = 1 := by
      first
      | exact mul_eq_one_comm.mp hMN
      | (rw [← Matrix.inv_eq_left_inv hMN]
         exact Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse hMN))
    rw [Matrix.fromCols_mul_fromRows] at hNM
    refine ⟨(J' * (1 - S₀ * S)).mulVec v, ?_⟩
    calc J.mulVec ((J' * (1 - S₀ * S)).mulVec v)
        = J.mulVec ((J' * (1 - S₀ * S)).mulVec v) + S₀.mulVec (S.mulVec v) := by
          rw [hv, Matrix.mulVec_zero, add_zero]
      _ = (J * (J' * (1 - S₀ * S)) + S₀ * S).mulVec v := by
          rw [Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = v := by rw [hNM, Matrix.one_mulVec]
  · rintro ⟨w, rfl⟩
    rw [Matrix.mulVec_mulVec, h0, Matrix.zero_mulVec]

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormalNoethLocalDimOneIsDVR
section
open AlgebraicGeometry CategoryTheory Limits
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem normal_noeth_local_dim_one_isDVR : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R], ringKrullDim R = 1 → IsDiscreteValuationRing R := by
  intro R _ _ _ _ _ h1
  have hnf : ¬ IsField R := (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mp h1).1
  have hdim : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by simp [h1])
  have h4 : IsIntegrallyClosed R ∧ ∃! P : Ideal R, P ≠ ⊥ ∧ P.IsPrime := by
    refine ⟨inferInstance, IsLocalRing.maximalIdeal R,
      ⟨fun h => hnf (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h), inferInstance⟩, ?_⟩
    rintro P ⟨hP, hPp⟩
    exact IsLocalRing.eq_maximalIdeal (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hdim P hP hPp)
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 1 4).mpr h4

end GlobalTheory.CompanionTheory.Ar.Flat
end

