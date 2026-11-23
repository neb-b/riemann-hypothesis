module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenOfNorm
section
namespace UpperTheory.V.Z.Sym.Loc

open IsLocalRing Polynomial QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ : K}

theorem IsLoc.char_ne (L : IsLoc O Δ) : ringChar (ResidueField O) ≠ 2 := by
  intro h
  have hu : IsUnit (2 : ResidueField O) := by
    have h2 := L.two.map (residue O)
    rwa [map_ofNat] at h2
  have h2 : ((ringChar (ResidueField O) : ℕ) : ResidueField O) = 0 := ringChar.Nat.cast_ringChar
  rw [h] at h2
  exact hu.ne_zero (by exact_mod_cast h2)

theorem IsLoc.nm_unit (L : IsLoc O Δ) (ε u : Oˣ) : ∃ a b : O, a ^ 2 - ε * b ^ 2 = u := by
  haveI := L.fin
  letI := Fintype.ofFinite (ResidueField O)
  have hodd : Fintype.card (ResidueField O) % 2 = 1 := by
    have h2 := L.char_ne
    rw [Ne, FiniteField.even_card_iff_char_two] at h2
    omega
  have hε0 : residue O (ε : O) ≠ 0 := (ε.isUnit.map (residue O)).ne_zero
  have hu0 : residue O (u : O) ≠ 0 := (u.isUnit.map (residue O)).ne_zero
  obtain ⟨a', b', hroot⟩ := FiniteField.exists_root_sum_quadratic
    (f := X ^ 2 - C (residue O (u : O))) (g := C (-residue O (ε : O)) * X ^ 2)
    (degree_X_pow_sub_C (by norm_num) _) (degree_C_mul_X_pow 2 (neg_ne_zero.2 hε0)) hodd
  obtain ⟨a0, rfl⟩ := residue_surjective a'
  obtain ⟨b0, rfl⟩ := residue_surjective b'
  have hab : residue O (a0 ^ 2 - u - ε * b0 ^ 2) = 0 := by
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C, map_sub, map_mul, map_pow] at hroot ⊢
    linear_combination hroot
  by_cases ha : residue O a0 = 0
  · have hb : IsUnit b0 := by
      rw [← residue_ne_zero_iff_isUnit]
      intro hb
      apply hu0
      simp only [map_sub, map_mul, map_pow, ha, hb] at hab
      linear_combination -hab
    obtain ⟨r, hr, -⟩ := sqrtO O K Δ L ((a0 ^ 2 - u) * ↑ε⁻¹) b0 hb (by
      rw [← residue_eq_zero_iff]
      have e1 : (a0 ^ 2 - u) * ↑ε⁻¹ - b0 ^ 2 = (a0 ^ 2 - u - ε * b0 ^ 2) * ↑ε⁻¹ := by
        have := ε.mul_inv
        linear_combination b0 ^ 2 * this
      rw [e1, map_mul, hab, zero_mul])
    refine ⟨a0, r, ?_⟩
    rw [hr]
    have := ε.mul_inv
    linear_combination (-(a0 ^ 2 - u)) * this
  · have ha' : IsUnit a0 := (residue_ne_zero_iff_isUnit a0).1 ha
    obtain ⟨r, hr, -⟩ := sqrtO O K Δ L (u + ε * b0 ^ 2) a0 ha' (by
      rw [← residue_eq_zero_iff]
      have e1 : (u : O) + ε * b0 ^ 2 - a0 ^ 2 = -(a0 ^ 2 - u - ε * b0 ^ 2) := by ring
      rw [e1, map_neg, hab, neg_zero])
    exact ⟨r, b0, by rw [hr]; ring⟩

omit [IsDomain O] [IsDiscreteValuationRing O] [Algebra O K] in
theorem nm_symm {x y : K} (hx : x ≠ 0) (h2 : (2 : K) ≠ 0) (h : ∃ a b : K, a ^ 2 - x * b ^ 2 = y) (hy : y ≠ 0) : ∃ a b : K, a ^ 2 - y * b ^ 2 = x := by
  obtain ⟨a, b, hab⟩ := h
  by_cases hb : b = 0
  · subst hb
    have ha : a ≠ 0 := by
      rintro rfl
      apply hy
      rw [← hab]
      ring
    refine ⟨(x + 1) / 2, (x - 1) / (2 * a), ?_⟩
    rw [← hab]
    field_simp
    ring
  · refine ⟨a / b, 1 / b, ?_⟩
    rw [← hab]
    field_simp
    ring

private theorem isUnit_sq_sub_mul_sq_of_not_isSquare_residue (ε : O) (hε : ¬ IsSquare (residue O ε)) (x y : O)
    (h : IsUnit x ∨ IsUnit y) : IsUnit (x ^ 2 - ε * y ^ 2) := by
  rw [← residue_ne_zero_iff_isUnit]
  intro h0
  simp only [map_sub, map_mul, map_pow] at h0
  by_cases hy : residue O y = 0
  · have hx : residue O x = 0 := by
      rw [hy] at h0
      have : residue O x ^ 2 = 0 := by linear_combination h0
      exact pow_eq_zero_iff (by norm_num) |>.1 this
    rcases h with h | h
    · exact (residue_ne_zero_iff_isUnit x).2 h hx
    · exact (residue_ne_zero_iff_isUnit y).2 h hy
  · apply hε
    refine ⟨residue O x / residue O y, ?_⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hy hy)]
    linear_combination -h0

private theorem exists_common_pow_factor_coprime_units {π : O} (hπ : Irreducible π) (x y : O) (h : x ≠ 0 ∨ y ≠ 0) :
    ∃ (k : ℕ) (x' y' : O), x = π ^ k * x' ∧ y = π ^ k * y' ∧ (IsUnit x' ∨ IsUnit y') := by
  by_cases hx : x = 0
  · have hy : y ≠ 0 := by tauto
    obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hπ
    exact ⟨n, 0, v, by simp [hx], by ring, Or.inr v.isUnit⟩
  by_cases hy : y = 0
  · obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
    exact ⟨m, u, 0, by ring, by simp [hy], Or.inl u.isUnit⟩
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hπ
  rcases le_total m n with hmn | hnm
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact ⟨m, u, v * π ^ d, by ring, by ring, Or.inl u.isUnit⟩
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    exact ⟨n, u * π ^ d, v, by ring, by ring, Or.inr v.isUnit⟩

private theorem not_isSquare_residue_of_not_isSquare (L : IsLoc O Δ) (ε : Oˣ) (hε : ¬ IsSquare (algebraMap O K ε)) :
    ¬ IsSquare (residue O (ε : O)) := by
  rintro ⟨c, hc⟩
  obtain ⟨r₀, rfl⟩ := residue_surjective c
  have hε0 : residue O (ε : O) ≠ 0 := (ε.isUnit.map (residue O)).ne_zero
  have hr₀ : IsUnit r₀ := by
    rw [← residue_ne_zero_iff_isUnit]
    intro h0
    rw [h0, mul_zero] at hc
    exact hε0 hc
  obtain ⟨r, hr, -⟩ := sqrtO O K Δ L ε r₀ hr₀ (by
    rw [← residue_eq_zero_iff, map_sub, map_pow, hc, sq, sub_self])
  apply hε
  exact ⟨algebraMap O K r, by rw [← map_mul, ← sq, hr]⟩

theorem IsLoc.even_of_norm (L : IsLoc O Δ) (ε : Oˣ) (hε : ¬ IsSquare (algebraMap O K ε)) {a b : K}
    (h : a ^ 2 - algebraMap O K ε * b ^ 2 ≠ 0) : EvenVal O (a ^ 2 - algebraMap O K ε * b ^ 2) := by
  haveI := L.frac
  have hres := not_isSquare_residue_of_not_isSquare L ε hε
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨x1, z1, hz1, rfl⟩ := IsFractionRing.div_surjective (A := O) a
  obtain ⟨y1, z2, hz2, rfl⟩ := IsFractionRing.div_surjective (A := O) b
  have hz1' : algebraMap O K z1 ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hz1
  have hz2' : algebraMap O K z2 ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hz2
  have heq : (algebraMap O K x1 / algebraMap O K z1) ^ 2
      - algebraMap O K ε * (algebraMap O K y1 / algebraMap O K z2) ^ 2
      = algebraMap O K ((x1 * z2) ^ 2 - ε * (y1 * z1) ^ 2) / (algebraMap O K (z1 * z2)) ^ 2 := by
    simp only [map_sub, map_mul, map_pow]
    field_simp
  rw [heq] at h ⊢
  have hnz : x1 * z2 ≠ 0 ∨ y1 * z1 ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply h
    rw [hc.1, hc.2]
    simp
  obtain ⟨k, x', y', hx, hy, hu⟩ := exists_common_pow_factor_coprime_units hπ _ _ hnz
  have hw := isUnit_sq_sub_mul_sq_of_not_isSquare_residue (ε : O) hres x' y' hu
  have hπ0 : algebraMap O K π ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective O K)]
    exact hπ.ne_zero
  have hzz : algebraMap O K (z1 * z2) ≠ 0 := by
    rw [map_mul]
    exact mul_ne_zero hz1' hz2'
  refine ⟨hw.unit, algebraMap O K π ^ k / algebraMap O K (z1 * z2),
    div_ne_zero (pow_ne_zero _ hπ0) hzz, ?_⟩
  rw [hx, hy, IsUnit.unit_spec]
  simp only [map_sub, map_mul, map_pow]
  field_simp

theorem IsLoc.not_even (L : IsLoc O Δ) {p : O} (hp : Irreducible p) : ¬ EvenVal O (algebraMap O K p) := by
  haveI := L.frac
  rintro ⟨u, s, hs, he⟩
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := O) s
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyK : algebraMap O K y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hs
  have key : p * y ^ 2 = (u : O) * x ^ 2 := by
    apply IsFractionRing.injective O K
    simp only [map_mul, map_pow]
    rw [he]
    field_simp
  obtain ⟨m, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hp
  obtain ⟨n, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hp
  have e2 : ((w ^ 2 : Oˣ) : O) * p ^ (2 * n + 1) = ((u * v ^ 2 : Oˣ) : O) * p ^ (2 * m) := by
    push_cast
    linear_combination key
  have := IsDiscreteValuationRing.unit_mul_pow_congr_pow hp hp _ _ _ _ e2
  omega

theorem IsLoc.exists_nonsq (L : IsLoc O Δ) : ∃ ε : Oˣ, ¬ IsSquare (algebraMap O K ε) := by
  haveI := L.frac
  haveI := L.fin
  letI := Fintype.ofFinite (ResidueField O)
  obtain ⟨c, hc⟩ := FiniteField.exists_nonsquare L.char_ne
  obtain ⟨e, rfl⟩ := residue_surjective c
  have he : IsUnit e := by
    rw [← residue_ne_zero_iff_isUnit]
    intro h0
    apply hc
    rw [h0]
    exact ⟨0, by simp⟩
  refine ⟨he.unit, ?_⟩
  rintro ⟨t, ht⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨x, z, hz, rfl⟩ := IsFractionRing.div_surjective (A := O) t
  have hz0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
  have hz' : algebraMap O K z ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hz
  rw [IsUnit.unit_spec] at ht
  have h0 : x ^ 2 - e * z ^ 2 = 0 := by
    apply IsFractionRing.injective O K
    simp only [map_sub, map_mul, map_pow, map_zero, ht]
    field_simp
    ring
  obtain ⟨k, x', z', hx, hz2, hu⟩ := exists_common_pow_factor_coprime_units hπ x z (Or.inr hz0)
  have hw := isUnit_sq_sub_mul_sq_of_not_isSquare_residue e hc x' z' hu
  have e3 : π ^ (2 * k) * (x' ^ 2 - e * z' ^ 2) = 0 := by
    rw [← h0, hx, hz2]
    ring
  rcases mul_eq_zero.1 e3 with h | h
  · exact pow_ne_zero _ hπ.ne_zero h
  · exact hw.ne_zero h

end UpperTheory.V.Z.Sym.Loc
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsOfGOrbNe
section
namespace UpperTheory.V.Z.Sym.Loc

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K}

theorem j_apply (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) (x : Etau K τ) : j x = x.re • (1 : Matrix (Fin 2) (Fin 2) K) + x.im • j ω := by
  conv_lhs => rw [show x = algebraMap K (Etau K τ) x.re + x.im • ω by ext <;> simp]
  rw [map_add (f := _), map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]

theorem j_sq (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) : j ω * j ω = τ • j ω - 1 := by
  rw [← map_mul, QuadraticAlgebra.omega_mul_omega_eq_add, map_add (f := _), map_smul, map_smul, map_one,
    neg_smul, one_smul]
  abel

theorem j_det_omega (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) (hj : (j ω).trace = τ) : (j ω).det = 1 := by
  have h := congrFun (congrFun (j_sq j) 0) 0
  rw [Matrix.trace_fin_two] at hj
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h
  rw [Matrix.det_fin_two]
  linear_combination (j ω 0 0) * hj - h

theorem j_trace (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) (hj : (j ω).trace = τ) (x : Etau K τ) : (j x).trace = QuadraticAlgebra.trace x := by
  rw [j_apply, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hj, QuadraticAlgebra.trace_def]
  simp; ring

theorem j_det (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) (hj : (j ω).trace = τ) (x : Etau K τ) : (j x).det = QuadraticAlgebra.norm x := by
  have h := j_det_omega j hj
  rw [Matrix.det_fin_two] at h
  rw [Matrix.trace_fin_two] at hj
  rw [j_apply, Matrix.det_fin_two, QuadraticAlgebra.norm_def]
  simp
  linear_combination (x.re * x.im) * hj + x.im ^ 2 * h

theorem mem_ZK {g : GL (Fin 2) K} : g ∈ ZK O K ↔ ∃ (z : Kˣ) (k : GL (Fin 2) O),
    g = Matrix.GeneralLinearGroup.scalar (Fin 2) z * Matrix.GeneralLinearGroup.map (algebraMap O K) k := by
  haveI hN : ((Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ →* GL (Fin 2) K).range).Normal := by
    rw [← Matrix.GeneralLinearGroup.center_eq_range_scalar]
    infer_instance
  rw [ZK, ← SetLike.mem_coe, Subgroup.normal_mul, KG]
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, _, ⟨k, rfl⟩, rfl⟩
    exact ⟨z, k, rfl⟩
  · rintro ⟨z, k, rfl⟩
    exact ⟨_, ⟨z, rfl⟩, _, ⟨k, rfl⟩, rfl⟩

theorem exists_of_gOrb_ne {j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K} (hj : (j ω).trace = τ) {χ : Kˣ →* ℂˣ} {z : (Etau K τ)ˣ} (h : gOrb O j χ z ≠ 0) :
    ∃ (s : Kˣ) (u : Oˣ) (t : O), QuadraticAlgebra.norm (z : Etau K τ) = algebraMap O K u * (s : K) ^ 2 ∧
      QuadraticAlgebra.trace (z : Etau K τ) = s * algebraMap O K t := by
  have core : ∀ (g : GL (Fin 2) K) (w : Kˣ),
      (Matrix.GeneralLinearGroup.scalar (Fin 2) w)⁻¹ * (g⁻¹ * jU j z * g) ∈ KG O K →
      ∃ (s : Kˣ) (u : Oˣ) (t : O), QuadraticAlgebra.norm (z : Etau K τ) = algebraMap O K u * (s : K) ^ 2 ∧
        QuadraticAlgebra.trace (z : Etau K τ) = s * algebraMap O K t := by
    intro g w hw
    obtain ⟨k, hk⟩ := hw
    have hM : g⁻¹ * jU j z * g
        = Matrix.GeneralLinearGroup.scalar (Fin 2) w * Matrix.GeneralLinearGroup.map (algebraMap O K) k := by
      rw [hk, mul_inv_cancel_left]
    have hMat := congrArg Units.val hM
    simp only [jU, Units.val_mul, Units.coe_map, MonoidHom.coe_coe,
      AlgHom.coe_toRingHom, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.GeneralLinearGroup.val_map_apply] at hMat
    have htr : (j z).trace = (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j z * (g : Matrix (Fin 2) (Fin 2) K)).trace := by
      rw [Matrix.trace_mul_comm, ← mul_assoc, Units.mul_inv, one_mul]
    have hdt : (j z).det = (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j z * (g : Matrix (Fin 2) (Fin 2) K)).det := by
      rw [Matrix.det_mul, Matrix.det_mul, mul_comm (Matrix.det ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)),
        mul_assoc, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one, mul_one]
    refine ⟨w, Matrix.GeneralLinearGroup.det k, (k : Matrix (Fin 2) (Fin 2) O).trace, ?_, ?_⟩
    · rw [← j_det j hj, hdt, hMat]
      simp [Matrix.det_fin_two, Matrix.diagonal_mul, Matrix.GeneralLinearGroup.val_det_apply] <;> ring
    · rw [← j_trace j hj, htr, hMat]
      simp [Matrix.trace_fin_two, Matrix.diagonal_mul] <;> ring
  by_contra hcon
  apply h
  unfold gOrb orb wcount
  apply finsum_eq_zero_of_forall_eq_zero
  intro o
  apply mul_eq_zero_of_right
  unfold fZK
  dsimp only
  rw [dite_eq_right]
  rintro ⟨w, hw⟩
  exact hcon (core _ w hw)

end UpperTheory.V.Z.Sym.Loc
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IsFixMapIff
section
namespace UpperTheory.V.Z.Sym.Loc

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {Δ τ : K}

theorem sigL_mul (x y : EL Δ τ) : sigL (x * y) = sigL x * sigL y := by ext <;> simp [sigL] <;> ring

theorem sigL_sigL (x : EL Δ τ) : sigL (sigL x) = x := by ext <;> simp [sigL]

theorem sigL_one : sigL (1 : EL Δ τ) = 1 := by ext <;> simp [sigL, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem sigL_star (x : EL Δ τ) : sigL (star x) = star (sigL x) := by ext <;> simp [sigL]

theorem sigL_ofE (x : Etau K τ) : sigL (ofE Δ x) = ofE Δ x := by ext <;> simp [sigL, ofE]

theorem ofE_mul (x y : Etau K τ) : ofE Δ (x * y) = ofE Δ x * ofE Δ y := by ext <;> simp [ofE]

theorem ofE_one : ofE Δ (1 : Etau K τ) = 1 := by ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem ofE_star (x : Etau K τ) : ofE Δ (star x) = star (ofE Δ x) := by ext <;> simp [ofE]

theorem quo_mul_star (z : (Etau K τ)ˣ) : quo z * star (quo z) = 1 := by
  rw [quo, star_mul', star_star]
  calc _ = ((z : Etau K τ) * ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) * star ((z : Etau K τ) * ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) := by
        rw [star_mul']; ring
    _ = 1 := by simp


variable (O) in
def mulE (y : (EL Δ τ)ˣ) : Sp Δ τ ≃ₗ[O] Sp Δ τ where
  toFun x := (x.1, y * x.2)
  invFun x := (x.1, (y⁻¹ : (EL Δ τ)ˣ) * x.2)
  map_add' a b := by simp [mul_add]
  map_smul' a b := by
    refine Prod.ext rfl ?_
    change (y : EL Δ τ) * (a • b.2) = a • ((y : EL Δ τ) * b.2)
    rw [← algebraMap_smul K a b.2, ← algebraMap_smul K a, mul_smul_comm]
  left_inv x := by simp
  right_inv x := by simp

theorem isFix_map {c : K} {d m d' m' : EL Δ τ} (ψ : Sp Δ τ ≃ₗ[O] Sp Δ τ) (h1 : ∀ x y, herm c m (ψ x) (ψ y) = herm c m' x y)
    (h2 : ∀ x, semi d (ψ x) = ψ (semi d' x)) {S : Set (Sp Δ τ)} (h : IsFix O c d' m' S) : IsFix O c d m (ψ '' S) := by
  classical
  refine ⟨?_, fun y => ?_, ?_⟩
  · obtain ⟨s, rfl⟩ := h.fg
    refine ⟨s.image ψ, ?_⟩
    rw [Finset.coe_image, ← LinearEquiv.coe_coe, Submodule.span_image, Submodule.map_coe]
  · obtain ⟨y, rfl⟩ := ψ.surjective y
    rw [ψ.injective.mem_set_image, h.dual, Set.forall_mem_image]
    simp only [h1]
  · rw [← Set.image_comp]
    conv_rhs => rw [← h.stab, ← Set.image_comp]
    exact congrArg (· '' S) (funext h2)

theorem isFix_map_iff {c : K} {d m d' m' : EL Δ τ} (ψ : Sp Δ τ ≃ₗ[O] Sp Δ τ) (h1 : ∀ x y, herm c m (ψ x) (ψ y) = herm c m' x y)
    (h2 : ∀ x, semi d (ψ x) = ψ (semi d' x)) (S : Set (Sp Δ τ)) : IsFix O c d m (ψ '' S) ↔ IsFix O c d' m' S := by
  refine ⟨fun h => ?_, isFix_map ψ h1 h2⟩
  have := isFix_map (d := d') (m := m') ψ.symm (fun x y => by rw [← h1]; simp) (fun x => ψ.injective (by rw [← h2]; simp)) h
  rwa [← Set.image_comp, show (ψ.symm ∘ ψ : Sp Δ τ → Sp Δ τ) = id from funext ψ.symm_apply_apply, Set.image_id] at this

theorem isFix_mulE (c : K) (d m : EL Δ τ) (y : (EL Δ τ)ˣ) (S : Set (Sp Δ τ)) : IsFix O c d m ((mulE (O := O) y) '' S) ↔
    IsFix O c (d * sigL (y : EL Δ τ) * ((y⁻¹ : (EL Δ τ)ˣ) : EL Δ τ)) (m * (y : EL Δ τ) * star (sigL (y : EL Δ τ))) S := by
  refine isFix_map_iff _ (fun a b => ?_) (fun a => Prod.ext rfl ?_) S
  · change herm c m (a.1, (y : EL Δ τ) * a.2) (b.1, (y : EL Δ τ) * b.2) = _
    simp only [herm, sigL_mul, star_mul']
    congr 2
    ring
  · change d * sigL ((y : EL Δ τ) * a.2) = (y : EL Δ τ) * (d * sigL (y : EL Δ τ) * ((y⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * sigL a.2)
    rw [sigL_mul]
    linear_combination (-d * sigL (y : EL Δ τ) * sigL a.2) * y.mul_inv

theorem isFix_tor (c : K) (d m : EL Δ τ) (z : (Etau K τ)ˣ) (S : Set (Sp Δ τ)) : IsFix O c d m (tor Δ z '' S) ↔ IsFix O c d m S := by
  have h : ofE Δ (quo z) * star (ofE Δ (quo z)) = 1 := by rw [← ofE_star, ← ofE_mul, quo_mul_star, ofE_one]
  let Y : (EL Δ τ)ˣ := Units.mkOfMulEqOne _ _ h
  have := isFix_mulE (O := O) c d m Y S
  rw [show sigL (Y : EL Δ τ) = Y from sigL_ofE _, mul_assoc d, Units.mul_inv, mul_one, mul_assoc m,
    show (Y : EL Δ τ) * star (Y : EL Δ τ) = 1 from h, mul_one] at this
  exact this

end UpperTheory.V.Z.Sym.Loc
end

