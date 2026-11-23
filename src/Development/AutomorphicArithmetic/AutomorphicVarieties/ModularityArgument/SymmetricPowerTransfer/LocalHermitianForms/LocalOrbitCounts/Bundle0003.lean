module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatForm
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem two_ne {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ : K} (L : IsLoc O Δ) : (2 : K) ≠ 0 := by
  have h := (L.two).map (algebraMap O K)
  rw [map_ofNat] at h
  exact h.ne_zero

theorem UpperTheory.V.Z.Sym.Loc.datForm : UpperTheory.V.Z.Sym.Loc.DatForm := by
  intro O K _ _ _ _ _ Δ τ hL c lam hn z hz m hD
  have h2 : (2 : K) ≠ 0 := two_ne hL
  have h1 := datLam K Δ τ c hD.reg hD.c_ne lam hn z hz
  have hs1 : sigL (1 : EL Δ τ) = 1 := by
    simp [sigL]
  have hdd := h1.m_sig
  rw [hs1, one_mul] at hdd
  have hsm := hD.m_sig
  rw [mul_assoc, ← hdd, mul_one] at hsm
  have hst := hD.m_star
  rw [hsm] at hst
  have him : m.im = 0 := by
    have e := congrArg QuadraticAlgebra.im hst
    simp only [QuadraticAlgebra.im_star] at e
    have e2 : (2 : K) • m.im = 0 := by
      rw [two_smul]
      linear_combination -e
    exact (smul_eq_zero.mp e2).resolve_left h2
  have hre : m.re.im = 0 := by
    have e := congrArg (fun x : EL Δ τ => x.re.im) hsm
    simp only [sigL, QuadraticAlgebra.im_star] at e
    have e2 : (2 : K) * m.re.im = 0 := by
      linear_combination -e
    exact (mul_eq_zero.mp e2).resolve_left h2
  have ht : m.re.re ≠ 0 := by
    intro h0
    apply hD.m_unit.ne_zero
    ext <;> simp [h0, hre, him]
  refine ⟨Units.mk0 m.re.re ht, ?_⟩
  ext <;> simp [hre, him]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FzdLaw
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem isIntegral_entry_zero_zero_of_mem_kd {O K : Type} [CommRing O] [Field K] [Algebra O K] {Δ : K} {t : DX Δ}
    (ht : t ∈ KD Δ O) :
    IsIntegral O (((t : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 0) := by
  rw [KD, Subgroup.mem_subgroupOf, MonoidHom.mem_range] at ht
  obtain ⟨N, hN⟩ := ht
  rw [← hN, Matrix.GeneralLinearGroup.map_apply]
  exact (N.1 0 0).2

private theorem inv_mul_scal_entry_zero_zero_eq {K : Type} [Field K] {Δ : K} {z z' : Kˣ} {s s' : DX Δ}
    (hs : IsScal z s) (hs' : IsScal z' s') :
    (((s'⁻¹ * s : DX Δ) : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 0
      = algebraMap K (Lsq K Δ) ((z' : K)⁻¹ * z) := by
  have e : s = s' * (s'⁻¹ * s) := by group
  have hmat : Glob.mt s = Glob.mt s' * Glob.mt (s'⁻¹ * s) := by
    conv_lhs => rw [e]
    rfl
  unfold IsScal at hs hs'
  rw [hs, hs'] at hmat
  have e2 := congrFun (congrFun hmat 0) 0
  simp only [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.diagonal_apply_eq] at e2
  show Glob.mt (s'⁻¹ * s) 0 0 = _
  set M := Glob.mt (s'⁻¹ * s) 0 0
  have h1 : algebraMap K (Lsq K Δ) (z' : K)⁻¹ * algebraMap K (Lsq K Δ) (z' : K) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ z'.ne_zero, map_one]
  rw [map_mul]
  linear_combination (-(algebraMap K (Lsq K Δ) (z' : K)⁻¹)) * e2 + (-M) * h1

theorem UpperTheory.V.Z.Sym.Loc.fzdLaw : UpperTheory.V.Z.Sym.Loc.FzdLaw := by
  intro O K _ _ _ _ _ Δ hL χ hχ
  haveI := hL.frac
  refine ⟨?_, ?_⟩
  · intro g hg
    rw [fZD, dite_eq_right]
    rintro ⟨z, s, hs, hk⟩
    apply hg
    have hsZ : s ∈ ZD Δ := by
      rw [ZD, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
      refine ⟨z, Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
      have h := congrFun (congrFun hs i) j
      rw [show (((s : DX Δ) : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) i j
        = Glob.mt s i j from rfl, h]
      simp [Matrix.scalar_apply]
    have e : g = s * (s⁻¹ * g) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hsZ hk
  · intro z s k hs hk
    have hex : ∃ z s', IsScal z s' ∧ s'⁻¹ * (s * k) ∈ KD Δ O :=
      ⟨z, s, hs, by rwa [inv_mul_cancel_left]⟩
    rw [fZD, dite_eq_left hex]
    obtain ⟨hs', hk'⟩ := hex.choose_spec.choose_spec
    set z' := hex.choose
    set s' := hex.choose_spec.choose
    have ht : s'⁻¹ * s ∈ KD Δ O := by
      have e : s'⁻¹ * s = (s'⁻¹ * (s * k)) * k⁻¹ := by group
      rw [e]
      exact mul_mem hk' (inv_mem hk)
    have ht' : s⁻¹ * s' ∈ KD Δ O := by
      have e : s⁻¹ * s' = (s'⁻¹ * s)⁻¹ := by group
      rw [e]
      exact inv_mem ht
    have i1 := isIntegral_entry_zero_zero_of_mem_kd ht
    rw [inv_mul_scal_entry_zero_zero_eq hs hs'] at i1
    have i2 := isIntegral_entry_zero_zero_of_mem_kd ht'
    rw [inv_mul_scal_entry_zero_zero_eq hs' hs] at i2
    let f : K →ₐ[O] Lsq K Δ := IsScalarTower.toAlgHom O K (Lsq K Δ)
    have hf : Function.Injective f := (algebraMap K (Lsq K Δ)).injective
    rw [show algebraMap K (Lsq K Δ) ((z' : K)⁻¹ * z) = f ((z' : K)⁻¹ * z) from rfl,
      isIntegral_algHom_iff f hf, IsIntegrallyClosed.isIntegral_iff (K := K)] at i1
    rw [show algebraMap K (Lsq K Δ) ((z : K)⁻¹ * z') = f ((z : K)⁻¹ * z') from rfl,
      isIntegral_algHom_iff f hf, IsIntegrallyClosed.isIntegral_iff (K := K)] at i2
    obtain ⟨a, ha⟩ := i1
    obtain ⟨b, hb⟩ := i2
    have hab : a * b = 1 := by
      apply IsFractionRing.injective O K
      rw [map_mul, ha, hb, map_one]
      field_simp
    have hu := hχ ⟨a, b, hab, by rw [mul_comm]; exact hab⟩
    have hmap : (Units.map (algebraMap O K : O →* K)) ⟨a, b, hab, by rw [mul_comm]; exact hab⟩
        = z'⁻¹ * z := Units.ext (by simp [ha])
    rw [hmap, map_mul, map_inv, inv_mul_eq_one] at hu
    rw [hu]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.RootEx
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.rootEx : UpperTheory.V.Z.Sym.Loc.RootEx := by
  intro O K _ _ _ _ _ Δ τ hL τ₀ e hτ hm
  subst hτ
  have h2 : IsUnit (2 : O) := hL.two
  have eZ : ((e : ℤ)) * (e : ℤ) = 1 := by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  have he : ((e : ℤ) : O) * ((e : ℤ) : O) = 1 := by
    exact_mod_cast congrArg (fun n : ℤ => (n : O)) eZ
  have eK : ((e : ℤ) : K) * ((e : ℤ) : K) = 1 := by
    exact_mod_cast congrArg (fun n : ℤ => (n : K)) eZ
  obtain ⟨s, hs, hs2⟩ := sqrtO O K Δ hL (((e : ℤ) : O) * (τ₀ + 2 * ((e : ℤ) : O))) 2 h2 (by
    have hrw : ((e : ℤ) : O) * (τ₀ + 2 * ((e : ℤ) : O)) - 2 ^ 2
        = ((e : ℤ) : O) * (τ₀ - 2 * ((e : ℤ) : O)) := by
      linear_combination (4 : O) * he
    rw [hrw]
    exact Ideal.mul_mem_left _ _ hm)
  have hsu : IsUnit s := by
    by_contra hn
    have hsm : s ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal s).2 ((mem_nonunits_iff).2 hn)
    have h2m : (2 : O) ∈ IsLocalRing.maximalIdeal O := by
      have := Ideal.sub_mem _ hsm hs2
      rwa [sub_sub_cancel] at this
    exact ((mem_nonunits_iff).1 ((IsLocalRing.mem_maximalIdeal _).1 h2m)) h2
  set y : O := ((hsu.unit⁻¹ : Oˣ) : O) with hydef
  have hy : s * y = 1 := hsu.mul_val_inv
  have key : (τ₀ + 2 * ((e : ℤ) : O)) * y ^ 2 = ((e : ℤ) : O) := by
    linear_combination (-(τ₀ + 2 * ((e : ℤ) : O)) * y ^ 2) * he
      + (-((e : ℤ) : O) * y ^ 2) * hs + ((e : ℤ) : O) * (s * y + 1) * hy
  have kK : ((algebraMap O K) τ₀ + 2 * ((e : ℤ) : K)) * ((algebraMap O K) y) ^ 2
      = ((e : ℤ) : K) := by
    have := congrArg (algebraMap O K) key
    simpa [map_mul, map_add (f := _), map_pow, map_intCast, map_ofNat] using this
  refine ⟨((e : ℤ) : O) * y, y, Units.isUnit _, ?_, ?_⟩
  · rw [sq]
    ext
    · simp [map_mul, map_intCast]
      linear_combination ((algebraMap O K) y) ^ 2 * eK
    · simp [map_mul, map_intCast]
      linear_combination kK
  · rw [QuadraticAlgebra.norm_def]
    simp only [map_mul, map_intCast]
    linear_combination ((e : ℤ) : K) * kK + (1 - ((algebraMap O K) y) ^ 2) * eK
end

