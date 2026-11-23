module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatFormM
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem two_ne {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ : K} (L : IsLoc O Δ) : (2 : K) ≠ 0 := by
  have h := L.two.map (algebraMap O K)
  rw [map_ofNat] at h
  exact h.ne_zero

theorem UpperTheory.V.Z.Sym.Loc.datFormM : UpperTheory.V.Z.Sym.Loc.DatFormM := by
  intro O K _ _ _ _ _ Δ τ hL c u hu2 hnu ν hν s hs
  have h2 : (2 : K) ≠ 0 := two_ne hL
  have ofE_sm : ∀ (r : K) (y : Etau K τ),
      ofE Δ (algebraMap K (Etau K τ) r * y) = (algebraMap K (Lsq K Δ) r) • ofE Δ y := by
    intro r y
    ext <;> simp [ofE]
  have ofE_mul : ∀ x y : Etau K τ, ofE Δ (x * y) = ofE Δ x * ofE Δ y := by
    intro x y
    ext <;> simp [ofE] <;> ring
  have sig_ofE : ∀ y : Etau K τ, sigL (ofE Δ y) = ofE Δ y := by
    intro y
    ext <;> simp [sigL, ofE]
  have star_ofE : ∀ y : Etau K τ, star (ofE Δ y) = ofE Δ (star y) := by
    intro y
    ext <;> simp [ofE]
  have sig_sm : ∀ (a : Lsq K Δ) (y : EL Δ τ), sigL (a • y) = star a • sigL y := by
    intro a y
    ext <;> simp [sigL]
  have star_sm : ∀ (a : Lsq K Δ) (y : EL Δ τ), star (a • y) = a • star y := by
    intro a y
    ext <;> simp <;> ring
  have hν' : ν * star ν = algebraMap K (Lsq K Δ) (-1) := by
    rw [← algebraMap_norm_eq_mul_star, hν]
  have hus : u * star u = algebraMap K (Etau K τ) 1 := by
    rw [← algebraMap_norm_eq_mul_star, hnu]
  refine ⟨?_, ?_⟩
  · rw [sig_sm, sig_ofE, smul_mul_smul_comm, hν', ← ofE_mul, ← ofE_sm, ← sq, hu2]
    congr 1
    rw [map_neg, map_one]
    ring
  · intro m hm
    have hd : ν • ofE Δ u * star (sigL (ν • ofE Δ u)) = -1 := by
      rw [sig_sm, sig_ofE, star_sm, star_ofE, smul_mul_smul_comm, hν', ← ofE_mul, ← ofE_sm, hus]
      ext <;> simp [ofE]
    have hsig : sigL m = -m := by
      rw [hm.m_sig, mul_assoc, hd, mul_neg_one]
    have hst : star m = -m := by
      have h := hm.m_star
      rw [hsig, star_neg] at h
      exact neg_eq_iff_eq_neg.mp h
    have e1 : m.re.re = 0 := by
      have h := congrArg (fun y : EL Δ τ => y.re.re) hsig
      simp [sigL] at h
      have h' : 2 * m.re.re = 0 := by linear_combination h
      exact (mul_eq_zero.mp h').resolve_left h2
    have e2 : m.im.re = 0 := by
      have h := congrArg (fun y : EL Δ τ => y.im.re) hsig
      simp [sigL] at h
      have h' : 2 * m.im.re = 0 := by linear_combination h
      exact (mul_eq_zero.mp h').resolve_left h2
    have e3 : 2 * m.re.im = -τ * m.im.im := by
      have h := congrArg (fun y : EL Δ τ => y.re.im) hst
      simp at h
      linear_combination h
    have hq : m.im.im ≠ 0 := by
      intro hq0
      have e4 : m.re.im = 0 := by
        have h' : 2 * m.re.im = 0 := by rw [e3, hq0, mul_zero]
        exact (mul_eq_zero.mp h').resolve_left h2
      have hm0 : m = 0 := by
        ext
        · exact e1
        · exact e4
        · exact e2
        · exact hq0
      exact not_isUnit_zero (hm0 ▸ hm.m_unit)
    refine ⟨Units.mk0 (m.im.im / (2 * s)) (div_ne_zero hq (mul_ne_zero h2 hs)), ?_⟩
    ext
    · simp [ofE, e1]
    · simp [ofE]
      field_simp
      linear_combination e3
    · simp [ofE, e2]
    · simp [ofE]
      field_simp
      norm_num
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatLam
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem ofE_mul {K : Type} [Field K] (Δ τ : K) (x y : Etau K τ) : ofE Δ (x * y) = ofE Δ x * ofE Δ y := by
  ext <;> simp [ofE]

theorem UpperTheory.V.Z.Sym.Loc.datLam : UpperTheory.V.Z.Sym.Loc.DatLam := by
  intro K _ Δ τ c hreg hc lam hlam z hz
  show IsDat c (lam • ofE Δ (star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ))) 1
  have hzu : (z : Etau K τ) * ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) = 1 := z.mul_inv
  have hsz : star (z : Etau K τ) * star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) = 1 := by
    rw [← star_mul, mul_comm _ (z : Etau K τ), hzu, star_one]
  generalize star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) = w at hsz ⊢
  have hN : (z : Etau K τ) * star (z : Etau K τ) = algebraMap K (Etau K τ) (2 + τ) := by
    rw [hz]
    ext <;> simp <;> ring
  have hzz : (z : Etau K τ) * (z : Etau K τ) = algebraMap K (Etau K τ) (2 + τ) * ω := by
    rw [hz]
    ext <;> simp <;> ring
  have hzw : (z : Etau K τ) = algebraMap K (Etau K τ) (2 + τ) * w := by
    rw [← hN, mul_assoc, hsz, mul_one]
  have hNu : IsUnit (algebraMap K (Etau K τ) (2 + τ)) :=
    isUnit_of_mul_isUnit_left (hzw ▸ z.isUnit)
  have ha : algebraMap K (Etau K τ) (2 + τ) * (w * w) = ω := by
    apply hNu.mul_left_cancel
    calc algebraMap K (Etau K τ) (2 + τ) * (algebraMap K (Etau K τ) (2 + τ) * (w * w))
        = (algebraMap K (Etau K τ) (2 + τ) * w) * (algebraMap K (Etau K τ) (2 + τ) * w) := by ring
      _ = (z : Etau K τ) * (z : Etau K τ) := by rw [← hzw]
      _ = algebraMap K (Etau K τ) (2 + τ) * ω := hzz
  have hstarN : star (algebraMap K (Etau K τ) (2 + τ)) = algebraMap K (Etau K τ) (2 + τ) := by
    ext <;> simp
  have hs' : star (z : Etau K τ) = algebraMap K (Etau K τ) (2 + τ) * star w := by
    conv_lhs => rw [hzw]
    rw [star_mul', hstarN]
  have hb : algebraMap K (Etau K τ) (2 + τ) * (w * star w) = 1 := by
    calc algebraMap K (Etau K τ) (2 + τ) * (w * star w)
        = w * (algebraMap K (Etau K τ) (2 + τ) * star w) := by ring
      _ = w * star (z : Etau K τ) := by rw [hs']
      _ = 1 := by rw [mul_comm, hsz]
  have ofE_one : ofE Δ (1 : Etau K τ) = 1 := by
    ext <;> simp [ofE]
  have ofE_sm : ∀ (r : K) (y : Etau K τ),
      ofE Δ (algebraMap K (Etau K τ) r * y) = (algebraMap K (Lsq K Δ) r) • ofE Δ y := by
    intro r y
    ext <;> simp [ofE]
  have sig_ofE : ∀ y : Etau K τ, sigL (ofE Δ y) = ofE Δ y := by
    intro y
    ext <;> simp [sigL, ofE]
  have star_ofE : ∀ y : Etau K τ, star (ofE Δ y) = ofE Δ (star y) := by
    intro y
    ext <;> simp [ofE]
  have sig_sm : ∀ (a : Lsq K Δ) (y : EL Δ τ), sigL (a • y) = star a • sigL y := by
    intro a y
    ext <;> simp [sigL]
  have star_sm : ∀ (a : Lsq K Δ) (y : EL Δ τ), star (a • y) = a • star y := by
    intro a y
    ext <;> simp <;> ring
  have sig_one : sigL (1 : EL Δ τ) = 1 := by
    ext <;> simp [sigL]
  have hlam' : lam * star lam = algebraMap K (Lsq K Δ) (2 + τ) := by
    rw [← algebraMap_norm_eq_mul_star, hlam]
  refine ⟨hreg, hc, ?_, isUnit_one, ?_, ?_⟩
  · rw [sig_sm, sig_ofE, smul_mul_smul_comm, hlam', ← ofE_mul, ← ofE_sm, ha]
  · rw [sig_one, star_one]
  · rw [sig_one, one_mul, sig_sm, sig_ofE, star_sm, star_ofE, smul_mul_smul_comm, hlam',
      ← ofE_mul, ← ofE_sm, hb, ofE_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatSmul
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.datSmul : UpperTheory.V.Z.Sym.Loc.DatSmul := by
  intro K _ Δ τ c d m h t
  have hsig : sigL ((t : K) • m) = (t : K) • sigL m := by
    ext <;> simp [sigL]
  have hst : ∀ z : EL Δ τ, star ((t : K) • z) = (t : K) • star z := by
    intro z
    ext <;> simp <;> ring
  refine ⟨h.reg, h.c_ne, h.d_norm, ?_, ?_, ?_⟩
  · rw [Algebra.smul_def]
    exact (t.isUnit.map (algebraMap K (EL Δ τ))).mul h.m_unit
  · rw [hsig, hst, h.m_star]
  · rw [hsig, h.m_sig, smul_mul_assoc, smul_mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Descent
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.descent :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ : K), IsLoc O Δ → ∀ (s : K) (ε : Oˣ), Δ * s ^ 2 = algebraMap O K ε →
    ∀ x : Lsq K Δ, (IsInt O x ↔ x.re ∈ (algebraMap O K).range ∧ ∃ b : O, x.im = s * algebraMap O K b) ∧ (IsInt O x → IsInt O (star x)) := by
  intro O K _ _ _ _ _ Δ hL s ε hs x
  haveI := hL.frac
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hstar : ∀ y : Lsq K Δ, IsIntegral O y → IsIntegral O (star y) := by
    intro y hy
    let f : Lsq K Δ →ₐ[O] Lsq K Δ :=
      { starRingEnd (Lsq K Δ) with
        commutes' := fun r => by
          show star (algebraMap O (Lsq K Δ) r) = algebraMap O (Lsq K Δ) r
          rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ)]
          ext <;> simp }
    exact hy.map f
  have hdown : ∀ c : K, IsIntegral O (algebraMap K (Lsq K Δ) c) → c ∈ (algebraMap O K).range := by
    intro c hc
    have hc' : IsIntegral O c :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom O K (Lsq K Δ))
        (algebraMap K (Lsq K Δ)).injective).mp hc
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hc'
    exact ⟨y, hy⟩
  have hεne : algebraMap O K (ε : O) ≠ 0 := (map_ne_zero_iff _ hinj).mpr ε.ne_zero
  have hΔs : Δ * s ^ 2 ≠ 0 := by rw [hs]; exact hεne
  have hΔ : Δ ≠ 0 := left_ne_zero_of_mul hΔs
  have hs0 : s ≠ 0 := fun h => hΔs (by simp [h])
  have hfwd : IsIntegral O x →
      x.re ∈ (algebraMap O K).range ∧ ∃ b : O, x.im = s * algebraMap O K b := by
    intro hxi
    have hsx := hstar x hxi
    have htr : x + star x = algebraMap K (Lsq K Δ) (2 * x.re) := by
      ext <;> simp <;> ring
    have hnm : x * star x = algebraMap K (Lsq K Δ) (x.re * x.re - Δ * x.im * x.im) := by
      ext <;> simp <;> ring
    obtain ⟨t, ht⟩ := hdown _ (htr ▸ hxi.add hsx)
    obtain ⟨n, hn⟩ := hdown _ (hnm ▸ hxi.mul hsx)
    obtain ⟨u, hu⟩ := hL.two.exists_left_inv
    have hu2 : algebraMap O K u * 2 = 1 := by
      have := congrArg (algebraMap O K) hu
      rwa [map_mul, map_ofNat, map_one] at this
    have hre : algebraMap O K (u * t) = x.re := by
      rw [map_mul, ht, ← mul_assoc, hu2, one_mul]
    refine ⟨⟨u * t, hre⟩, ?_⟩
    have hεK : algebraMap O K ((ε⁻¹ : Oˣ) : O) * algebraMap O K (ε : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have he' : algebraMap O K ((ε⁻¹ : Oˣ) : O) = (Δ * s ^ 2)⁻¹ := by
      rw [hs]; exact eq_inv_of_mul_eq_one_left hεK
    have hb2 : (x.im / s) ^ 2 =
        algebraMap O K (((ε⁻¹ : Oˣ) : O) * ((u * t) * (u * t) - n)) := by
      rw [map_mul, map_sub, map_mul, he', hre, hn]
      field_simp
      ring
    have hbi : IsIntegral O (x.im / s) := by
      refine IsIntegral.of_pow two_pos ?_
      rw [hb2]
      exact isIntegral_algebraMap
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hbi
    refine ⟨b, ?_⟩
    rw [hb]
    field_simp
  have hbwd : (x.re ∈ (algebraMap O K).range ∧ ∃ b : O, x.im = s * algebraMap O K b) →
      IsIntegral O x := by
    rintro ⟨⟨a, ha⟩, b, hb⟩
    have hω : IsIntegral O (algebraMap K (Lsq K Δ) s * ω) := by
      refine IsIntegral.of_pow two_pos ?_
      have hsq : (algebraMap K (Lsq K Δ) s * ω) ^ 2 = algebraMap O (Lsq K Δ) ε := by
        rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ), ← hs, sq]
        ext
        · simp only [re_mul, im_mul, algebraMap_re, algebraMap_im, omega_re, omega_im]
          ring
        · simp only [re_mul, im_mul, algebraMap_re, algebraMap_im, omega_re, omega_im]
          ring
      rw [hsq]
      exact isIntegral_algebraMap
    have hxe : x = algebraMap O (Lsq K Δ) a +
        algebraMap O (Lsq K Δ) b * (algebraMap K (Lsq K Δ) s * ω) := by
      rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ) a,
        IsScalarTower.algebraMap_apply O K (Lsq K Δ) b, ha]
      ext <;> simp [hb] <;> ring
    rw [hxe]
    exact isIntegral_algebraMap.add (isIntegral_algebraMap.mul hω)
  exact ⟨⟨hfwd, hbwd⟩, hstar x⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FzkLaw
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.fzkLaw : UpperTheory.V.Z.Sym.Loc.FzkLaw := by
  intro O K _ _ _ _ _ Δ hL χ hχ
  have inj : Function.Injective (algebraMap O K) := by
    haveI := hL.frac
    exact IsFractionRing.injective O K
  have ent : ∀ b : Kˣ, ((Matrix.GeneralLinearGroup.scalar (Fin 2) b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 = b := by
    intro b
    simp
  have key : ∀ a : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ KG O K → χ a = 1 := by
    rintro a ⟨M, hM⟩
    have a1 : algebraMap O K ((M : Matrix (Fin 2) (Fin 2) O) 0 0) = (a : K) := by
      have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) hM
      exact this.trans (ent a)
    have hM' : Matrix.GeneralLinearGroup.map (algebraMap O K) M⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ := by
      rw [map_inv, hM, map_inv]
    have a2 : algebraMap O K (((M⁻¹ : GL (Fin 2) O) : Matrix (Fin 2) (Fin 2) O) 0 0) = ((a⁻¹ : Kˣ) : K) := by
      have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) hM'
      exact this.trans (ent a⁻¹)
    have hp : (M : Matrix (Fin 2) (Fin 2) O) 0 0 * ((M⁻¹ : GL (Fin 2) O) : Matrix (Fin 2) (Fin 2) O) 0 0 = 1 := by
      apply inj
      rw [map_mul, a1, a2, Units.mul_inv, map_one]
    have hu : Units.map (algebraMap O K : O →* K) (Units.mkOfMulEqOne _ _ hp) = a := by
      ext
      simpa using a1
    rw [← hu]
    exact hχ _
  refine ⟨fun g hg => ?_, fun z k hk => ?_⟩
  · unfold fZK
    rw [dite_eq_right]
    rintro ⟨z, hz⟩
    apply hg
    rw [← mul_inv_cancel_left (Matrix.GeneralLinearGroup.scalar (Fin 2) z) g]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨z, rfl⟩) (Subgroup.mem_sup_right hz)
  · have hex : ∃ w, (Matrix.GeneralLinearGroup.scalar (Fin 2) w)⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 2) z * k) ∈ KG O K :=
      ⟨z, by rw [inv_mul_cancel_left]; exact hk⟩
    unfold fZK
    rw [dite_eq_left hex]
    have hw := hex.choose_spec
    have hs : Matrix.GeneralLinearGroup.scalar (Fin 2) (hex.choose⁻¹ * z) ∈ KG O K := by
      have e : Matrix.GeneralLinearGroup.scalar (Fin 2) (hex.choose⁻¹ * z) = (Matrix.GeneralLinearGroup.scalar (Fin 2) hex.choose)⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 2) z * k) * k⁻¹ := by
        rw [map_mul, map_inv]
        simp [mul_assoc]
      rw [e]
      exact Subgroup.mul_mem _ hw (Subgroup.inv_mem _ hk)
    have h1 := key _ hs
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    rw [h1]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.HsNE
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.hsNE : UpperTheory.V.Z.Sym.Loc.HsNE := by
  intro O K _ _ _ _ _ Δ τ hL _ t
  have h2 : (2 : K) ≠ 0 := by
    have h := hL.two.map (algebraMap O K)
    rw [map_ofNat] at h
    exact h.ne_zero
  have hiff : hs (τ ^ 2 - 4) (t : K) = 1 ↔ ∃ a b : K, a ^ 2 - (τ ^ 2 - 4) * b ^ 2 = t := by
    unfold hs
    split_ifs with h
    · simp [h]
    · simp only [h, iff_false]
      norm_num
  rw [hiff]
  constructor
  · rintro ⟨z, hz⟩
    have hz' : QuadraticAlgebra.norm (z : QuadraticAlgebra K (-1) τ) = (t : K) := by
      have h := congrArg Units.val hz
      rwa [Units.coe_map] at h
    refine ⟨((z : QuadraticAlgebra K (-1) τ).re * 2 + τ * (z : QuadraticAlgebra K (-1) τ).im) / 2,
      (z : QuadraticAlgebra K (-1) τ).im / 2, ?_⟩
    rw [← hz', norm_def]
    field_simp
    ring
  · rintro ⟨a, b, hab⟩
    have hw : QuadraticAlgebra.norm (⟨a - τ * b, 2 * b⟩ : QuadraticAlgebra K (-1) τ) = (t : K) := by
      rw [← hab, norm_def]
      ring
    have hu : IsUnit (⟨a - τ * b, 2 * b⟩ : QuadraticAlgebra K (-1) τ) := by
      rw [isUnit_iff_norm_isUnit, hw]
      exact t.isUnit
    refine ⟨hu.unit, ?_⟩
    ext
    rw [Units.coe_map, IsUnit.unit_spec]
    exact hw
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SqrtO
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.sqrtO : UpperTheory.V.Z.Sym.Loc.SqrtO := by
  intro O K _ _ _ _ _ Δ hL x r₀ hr hx
  haveI := hL.compl
  haveI := IsAdicComplete.henselianRing O (IsLocalRing.maximalIdeal O)
  have hmon : (Polynomial.X ^ 2 - Polynomial.C x : Polynomial O).Monic :=
    Polynomial.monic_X_pow_sub_C x two_ne_zero
  have h0 : Polynomial.eval r₀ (Polynomial.X ^ 2 - Polynomial.C x) ∈ IsLocalRing.maximalIdeal O := by
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    have h := (IsLocalRing.maximalIdeal O).neg_mem hx
    rwa [neg_sub] at h
  have h1 : IsUnit ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal O))
      (Polynomial.eval r₀ (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C x)))) := by
    apply IsUnit.map
    simp
    exact ⟨by simpa [one_add_one_eq_two] using hL.two, hr⟩
  obtain ⟨a, ha, ha'⟩ := HenselianRing.is_henselian _ hmon r₀ h0 h1
  refine ⟨a, ?_, ha'⟩
  have h := ha.eq_zero
  rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at h
  exact sub_eq_zero.mp h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.WCard
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.wCard :
    ∀ (T Y : Type) [CommGroup T] [MulAction T Y] (C : Subgroup T) (P F : Set Y), (∀ (t : T) y, y ∈ P → t • y ∈ P) → F ⊆ P → F.Finite →
    (∀ c ∈ C, ∀ y ∈ F, c • y ∈ F) → (∀ y ∈ P, ∃ t : T, t • y ∈ F) → (∀ (t : T), ∀ y ∈ F, t • y ∈ F → ∃ c ∈ C, c • y = t • y) →
    wcount C (P.indicator fun _ => (1 : ℂ)) = (F.ncard : ℂ) := by
  intro T Y _ _ C P F hP hFP hF hCF hPF hU
  classical
  let q : Y → MulAction.orbitRel.Quotient T Y := fun y => Quotient.mk _ y
  have hq : ∀ a b : Y, q a = q b ↔ a ∈ MulAction.orbit T b := by
    intro a b
    rw [← MulAction.orbitRel_apply]
    exact Quotient.eq
  have hstab : ∀ (t : T) (y : Y), MulAction.stabilizer T (t • y) = MulAction.stabilizer T y := by
    intro t y
    ext g
    simp only [MulAction.mem_stabilizer_iff]
    rw [smul_smul, mul_comm, ← smul_smul]
    exact (MulAction.injective t).eq_iff
  have hstab' : ∀ a b : Y, a ∈ MulAction.orbit T b →
      MulAction.stabilizer T a = MulAction.stabilizer T b := by
    rintro a b ⟨s, rfl⟩
    exact hstab s b
  have hrel : ∀ z : Y, (MulAction.stabilizer T z).relIndex C = (MulAction.orbit C z).ncard := by
    intro z
    rw [← MulAction.index_stabilizer, Subgroup.relIndex]
    congr 1
  have hfib : ∀ z ∈ F, {y | y ∈ F ∧ q y = q z} = MulAction.orbit C z := by
    intro z hz
    ext y
    constructor
    · rintro ⟨hy, hyq⟩
      obtain ⟨s, rfl⟩ := (hq _ _).1 hyq
      obtain ⟨c, hc, hcs⟩ := hU s z hz hy
      exact ⟨⟨c, hc⟩, hcs⟩
    · rintro ⟨c, rfl⟩
      refine ⟨hCF c c.2 z hz, ?_⟩
      exact (hq _ _).2 ⟨(c : T), rfl⟩
  have hsupp : (Function.support fun o : MulAction.orbitRel.Quotient T Y =>
      ((MulAction.stabilizer T (Quotient.out o)).relIndex C : ℂ) *
        P.indicator (fun _ => (1 : ℂ)) (Quotient.out o)) ⊆ ↑(hF.toFinset.image q) := by
    intro o ho
    have hmem : Quotient.out o ∈ P := by
      by_contra h
      exact ho (by simp [Set.indicator_of_notMem h])
    obtain ⟨t, ht⟩ := hPF _ hmem
    simp only [Finset.coe_image, Set.Finite.coe_toFinset, Set.mem_image]
    refine ⟨t • Quotient.out o, ht, ?_⟩
    change q (t • Quotient.out o) = o
    conv_rhs => rw [← Quotient.out_eq o]
    exact (hq _ _).2 ⟨t, rfl⟩
  unfold wcount
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  rw [Finset.sum_congr rfl (g := fun o => (({y ∈ hF.toFinset | q y = o}).card : ℂ))]
  · rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_image, Set.ncard_eq_toFinset_card _ hF]
  · intro o ho
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 ho
    rw [Set.Finite.mem_toFinset] at hz
    have hzo : Quotient.out (q z) ∈ MulAction.orbit T z := (hq _ _).1 (Quotient.out_eq _)
    have hP' : Quotient.out (q z) ∈ P := by
      obtain ⟨s, hs⟩ := hzo
      rw [← hs]
      exact hP s z (hFP hz)
    rw [Set.indicator_of_mem hP', mul_one, hstab' _ _ hzo, hrel z, ← hfib z hz]
    congr 1
    rw [← Set.ncard_coe_finset]
    congr 1
    ext y
    simp
end

