module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsResQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsDecompositionElementAtLXiPowFourNeOne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open UpperTheory.V

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

private theorem dirG_pow {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) (k : ℕ) (g : G ℚ Ω) :
    Chr.dirG ℚ Ω (χ ^ k) g = Chr.dirG ℚ Ω χ g ^ k := Units.ext (MulChar.pow_apply_coe χ k _)

private theorem dirG_one {O : Type} [CommRing O] {N : ℕ} [NeZero N] (g : G ℚ Ω) :
    Chr.dirG ℚ Ω (1 : DirichletCharacter O N) g = 1 := Units.ext (MulChar.one_apply_coe _)

private theorem dirG_frob {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) {A : ValuationSubring Ω} {v : ℕ}
    (hv : v.Prime) (hA : A.valuation (v : Ω) < 1) (hN : ¬ v ∣ N) {σ : G ℚ Ω} (h : IsFrob (F := ℚ) A v σ) :
    (Chr.dirG ℚ Ω χ σ : O) = χ v := by
  have h1 := (ML.placeBasic Ω).2.2.2.2.2.2.1 A v N σ h
    ((ML.placeBasic Ω).2.2.2.1 A v N ((Nat.Prime.coprime_iff_not_dvd hv).2 hN) hA)
  have h2 := (Chr.clsFacts ℚ Ω N).2.2.1 σ (ZMod.unitOfCoprime v ((Nat.Prime.coprime_iff_not_dvd hv).2 hN)) fun ζ hζ => by
    rw [h1 ζ hζ, ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod v hζ]
  rw [Chr.dirG, MonoidHom.comp_apply, h2, MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime]

private theorem pow_cond {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) {k : ℕ}
    (h : χ.conductor = 2 ^ k) : χ ^ 2 ^ k = 1 := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have h1 : χ.primitiveCharacter ^ Nat.totient χ.conductor = 1 := by
    ext u
    rw [MulChar.pow_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, map_one,
      MulChar.one_apply_coe]
  have h2 : Nat.totient χ.conductor ∣ 2 ^ k := by
    rw [h]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [Nat.totient_prime_pow Nat.prime_two hk]
      simpa using pow_dvd_pow 2 (Nat.sub_le k 1)
  obtain ⟨j, hj⟩ := h2
  rw [← χ.changeLevel_primitiveCharacter, ← map_pow, hj, pow_mul, h1, one_pow, map_one]

private theorem psi_exp (h : Host) {O : Type} [CommRing O] [IsDomain O] (ψ : DirichletCharacter O h.N) (hψ : h.IsChar ψ)
    {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) :
    ∃ a u : ℕ, Odd u ∧ ψ ^ (2 ^ a * u) = 1 ∧ l ^ 2 * 2 ^ (a + 2) ≤ 2 ^ h.nII l ψ := by
  have hq : 0 < h.q := NeZero.pos _
  have ho : 0 < h.o := orderOf_pos _
  obtain ⟨tψ, ⟨s, hs⟩, -⟩ := X.th1Facts O h.N ψ l hl hl2
  obtain ⟨-, -, t3, -⟩ := hostTh1 h O ψ hψ l hl hl2
  obtain ⟨-, b2⟩ := max_le_iff.1 (Nat.le_pow_clog one_lt_two _ : _ ≤ 2 ^ h.nII l ψ)
  refine ⟨c2 ψ + 1 + h.o.factorization 2, ordCompl[2] h.o * l ^ s, ?_, ?_, ?_⟩
  · exact (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 (Nat.not_dvd_ordCompl Nat.prime_two ho.ne'))).mul (hl.odd_of_ne_two hl2).pow
  · have e1 : 2 ^ (c2 ψ + 1 + h.o.factorization 2) * (ordCompl[2] h.o * l ^ s) = 2 ^ c2 ψ * (2 * h.o) * l ^ s := by
      conv_rhs => rw [← Nat.ordProj_mul_ordCompl_eq_self h.o 2]
      ring
    have p1 := pow_cond (psi2 ψ) (compCond O h.N ψ 2 Nat.prime_two).2.2.2.1.symm
    have p2 := orderOf_dvd_iff_pow_eq_one.1 t3
    rw [e1]
    generalize c2 ψ = k at p1 ⊢
    have p3 : (psi2 ψ * th1 l ψ * kap l ψ) ^ (2 ^ k * (2 * h.o) * l ^ s) = 1 := by
      rw [mul_pow, mul_pow, mul_assoc (2 ^ k), pow_mul, p1, one_pow, one_mul, mul_left_comm, pow_mul, p2, one_pow, one_mul,
        ← mul_assoc, mul_comm, pow_mul, hs, one_pow]
    rwa [← tψ] at p3
  · have v2 : 2 ^ h.o.factorization 2 ≤ h.o := Nat.ordProj_le 2 ho.ne'
    refine le_trans ?_ b2
    calc l ^ 2 * 2 ^ (c2 ψ + 1 + h.o.factorization 2 + 2) = 2 ^ (c2 ψ + 3) * 2 ^ h.o.factorization 2 * l ^ 2 * 1 := by ring
      _ ≤ 2 ^ (c2 ψ + 6) * h.o * l ^ 3 * h.q ^ 2 := by
        have hp : 2 ^ (c2 ψ + 3) ≤ 2 ^ (c2 ψ + 6) := by
          gcongr <;> omega
        have hlpow : l ^ 2 ≤ l ^ 3 := by
          gcongr <;> first | exact hl.pos | omega
        exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hp v2) hlpow)
          (Nat.one_le_pow _ _ hq)

end SlopeTestRemainingChoices

theorem UpperTheory.V.Ws.exists_decomposition_element_at_l_xi_pow_four_ne_one :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx2 D → ∀ (κ : G ℚ Ω →* c.Oˣ) (j : ℕ), κ ^ l ^ j = 1 → ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ g ∈ Dec (F := ℚ) A, Raw.bar D.Psi g = 1 ∧ κ g = 1 ∧ Raw.bar D.ξ g ^ 4 ≠ 1 := by
  intro Ω _ _ _ l hl c D ⟨hD, h, t, e, ψ, _, _, _, hmem, _, hO⟩ κ j hκ A hA
  have hlp : l.Prime := hl.out
  have hl2 := hD.l_odd
  obtain ⟨a, u, hu, hψ, hb⟩ := psi_exp h ψ (h.mem_X.1 hmem).1 hlp hl2
  obtain ⟨_, ξ, ξ₀, hξ, -, h0, dξ⟩ := hO.xi
  rw [orderOf_eq_one_iff] at h0
  have hT : l ∈ D.T := Finset.mem_insert_self _ _
  have hfr := hD.sg_frob l hT
  obtain ⟨w, hw, -⟩ := (Chr.placesQ Ω).2.2 l _ A hlp (hD.pl_over l hlp) hA
  have conj : ∀ (γ : G ℚ Ω →* c.Oˣ) (x : G ℚ Ω) (k : ℕ), γ (w⁻¹ * x ^ k * w) = γ x ^ k := fun γ x k => by
    rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul, map_pow]
  generalize h.nII l ψ = n at hb ξ hξ dξ
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : 0 < l ^ 2 * 2 ^ a := by have := hlp.pos; positivity
      rw [pow_add, ← mul_assoc] at hb
      omega
    · exact hn
  have h2 : ¬ l ∣ 2 := fun hd => hl2 ((Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).1 hd)
  refine ⟨_, hw _ (pow_mem hfr.1 (2 ^ a * u * l ^ j)), ?_, ?_, fun hx => ?_⟩
  · have : D.Psi (D.sg l) = Chr.dirG ℚ Ω ψ (D.sg l) := by
      rw [Raw.Psi, Chr.Psi, zpow_natCast, MonoidHom.mul_apply, MonoidHom.pow_apply, chiO, MonoidHom.comp_apply, hD.sg_cyc,
        map_one, one_pow, one_mul, hO.psi]
    rw [Raw.bar, conj, this, pow_mul, ← dirG_pow, hψ, dirG_one, one_pow, Units.val_one, map_one]
  · rw [conj, mul_comm, pow_mul, ← MonoidHom.pow_apply, hκ, MonoidHom.one_apply, one_pow]
  · have e1 : 2 ^ a * u * l ^ j * 4 = 2 ^ (a + 2) * (u * l ^ j) := by ring
    rw [Raw.bar, conj, ← map_pow, ← Units.val_pow_eq_pow_val, ← pow_mul, e1, dξ, MonoidHom.mul_apply, h0, dirG_one,
      one_mul] at hx
    have r4 : Chr.dirG ℚ Ω ξ (D.sg l) ^ (2 ^ (a + 2) * (u * l ^ j)) = 1 := by
      refine (congrFacts Ω l c).2.2.2.1 _ _ (Nat.totient (2 ^ n)) ?_ ?_ (one_pow _)
        (Ideal.Quotient.eq.1 (hx.trans (map_one (residue c.O)).symm))
      · rw [Nat.totient_prime_pow Nat.prime_two hn]
        exact fun hd => h2 (hlp.dvd_of_dvd_pow (by simpa using hd))
      · rw [← pow_mul, mul_comm, pow_mul, Chr.dirG, MonoidHom.comp_apply, ← map_pow, ZMod.pow_totient, map_one, one_pow]
    have r5 := congrArg Units.val r4
    rw [Units.val_pow_eq_pow_val, dirG_frob ξ hlp (hD.pl_over l hlp) (fun hd => h2 (hlp.dvd_of_dvd_pow hd)) hfr] at r5
    exact (UpperTheory.two_pow_lt_sq_mul_of_primitive_char_pow_eq_one c.O n ξ hξ l (a + 2) _ (hlp.odd_of_ne_two hl2) hlp.one_lt
      (hu.mul (hlp.odd_of_ne_two hl2).pow) r5).not_ge hb
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.FixAb
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.fixAb :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (H : Subgroup (G ℚ Ω)), IsOpen (H : Set (G ℚ Ω)) → commutator (G ℚ Ω) ≤ H → ∃ (F : IntermediateField ℚ Ω) (_ : NumberField F) (_ : IsAbelianGalois ℚ F), F.fixingSubgroup = H ∧ Module.finrank ℚ F = H.index := by
  intro Ω _ _ hc V hV hcomm
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hcl : IsClosed (V : Set (Ω ≃ₐ[ℚ] Ω)) := Subgroup.isClosed_of_isOpen V hV
  set L : IntermediateField ℚ Ω := IntermediateField.fixedField (V : Subgroup (Ω ≃ₐ[ℚ] Ω)) with hL
  have hfix : L.fixingSubgroup = V := InfiniteGalois.fixingSubgroup_fixedField ⟨V, hcl⟩
  have hnorm : V.Normal := ⟨fun n hn g => by
    have h : g * n * g⁻¹ * n⁻¹ ∈ V :=
      hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    have := mul_mem h hn
    rwa [inv_mul_cancel_right] at this⟩
  haveI hfin : FiniteDimensional ℚ L := (InfiniteGalois.isOpen_iff_finite L).1 (by rw [hfix]; exact hV)
  haveI hgal : IsGalois ℚ L := (InfiniteGalois.normal_iff_isGalois L).1 (by rw [hfix]; exact hnorm)
  have hsurj : Function.Surjective (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Ω) L) :=
    AlgEquiv.restrictNormalHom_surjective Ω
  have hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Ω) L).ker = V :=
    (@IntermediateField.restrictNormalHom_ker ℚ Ω _ _ _ L hgal.to_normal).trans hfix
  have hab : IsAbelianGalois ℚ L :=
    { is_comm := ⟨fun a b => by
        obtain ⟨a, rfl⟩ := hsurj a
        obtain ⟨b, rfl⟩ := hsurj b
        have h : a * b * a⁻¹ * b⁻¹ ∈ V :=
          hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
        rw [← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
          mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
        exact h⟩ }
  have hnf : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := hfin }
  refine ⟨L, hnf, hab, hfix, ?_⟩
  exact (IntermediateField.finrank_eq_fixingSubgroup_index Ω L).trans (congrArg Subgroup.index hfix)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.FixInf
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem ext_cc {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω)
    (φ : F →+* ℂ) :
    ∃ (σ : G ℚ Ω) (j : Ω →+* ℂ), (∀ x, j (σ x) = starRingEnd ℂ (j x)) ∧ ∀ x : F, j x = φ x := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  haveI : Module.IsTorsionFree F Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsGalois ℚ Ω := {}
  obtain ⟨j, hj⟩ : ∃ j : Ω →+* ℂ, ∀ x : F, j x = φ x := by
    letI : Algebra F ℂ := φ.toAlgebra
    let j : Ω →ₐ[F] ℂ := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    exact ⟨j.toRingHom, fun x => j.commutes x⟩
  letI : Algebra Ω ℂ := j.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.toRatAlgHom.commutes x).symm
  let cj : Ω →ₐ[ℚ] ℂ := ((starRingEnd ℂ).comp j).toRatAlgHom
  exact ⟨cj.restrictNormal' Ω, j, fun x => AlgHom.restrictNormal_commutes cj Ω x, hj⟩

theorem UpperTheory.V.Ws.fixInf :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F], ((∀ σ : G ℚ Ω, IsCC σ → σ ∈ F.fixingSubgroup) → IsTotallyReal F) ∧ ((∀ σ : G ℚ Ω, IsCC σ → σ ∉ F.fixingSubgroup) → Module.finrank ℚ F = 2 → IsCMField F) := by
  intro Ω _ _ _ F _
  refine ⟨fun h => ⟨fun w => ?_⟩, fun h h2 => ?_⟩
  · obtain ⟨σ, j, hσ, hj⟩ := ext_cc F w.embedding
    have hm := (F.mem_fixingSubgroup_iff σ).1 (h σ ⟨j, hσ⟩)
    refine InfinitePlace.isReal_iff.2 (RingHom.ext fun x => ?_)
    show starRingEnd ℂ (w.embedding x) = w.embedding x
    rw [← hj, ← hσ, hm x.1 x.2]
  · haveI : IsTotallyComplex F := ⟨fun w => by
      rw [← InfinitePlace.not_isReal_iff_isComplex]
      intro hw
      obtain ⟨σ, j, hσ, hj⟩ := ext_cc F w.embedding
      refine h σ ⟨j, hσ⟩ ((F.mem_fixingSubgroup_iff σ).2 fun x hx => j.injective ?_)
      have e : starRingEnd ℂ (w.embedding ⟨x, hx⟩) = w.embedding ⟨x, hx⟩ :=
        RingHom.congr_fun (InfinitePlace.isReal_iff.1 hw) ⟨x, hx⟩
      rw [← hj] at e
      rw [hσ]; exact e⟩
    haveI : Algebra.IsQuadraticExtension ℚ F := ⟨h2⟩
    exact IsCMField.ofCMExtension ℚ F
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.KxKapL
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open UpperTheory.V

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime]

private theorem kx_cls (n : ℕ) {s : G ℚ Ω} (h : cycZ ℚ Ω l s = 1) : Chr.cls ℚ Ω (l ^ n) s = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.out.ne_zero⟩
  refine (Chr.clsFacts ℚ Ω (l ^ n)).2.2.1 s _ fun ζ hζ => ?_
  have h1 := cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ] Ω) Ω s) ζ hζ
  have h2 : cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ] Ω) Ω s) = 1 := h
  rw [h2, Units.val_one, map_one] at h1
  exact h1

variable {O : Type} [CommRing O] [IsDomain O] {N : ℕ} [NeZero N]

private theorem kx_kapL (ψ : DirichletCharacter O N) {s : G ℚ Ω} (h : cycZ ℚ Ω l s = 1) :
    kapL l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) = 1 := by
  haveI : NeZero (ordProj[l] N) := ⟨(Nat.ordProj_pos N l).ne'⟩
  have h3 : proj l N (Chr.cls ℚ Ω N s) = 1 := by
    rw [← MonoidHom.mem_ker, (projFacts N l hl.out).2.2.2.2.2.2.1, MonoidHom.mem_ker, ← MonoidHom.comp_apply,
      (Chr.clsFacts ℚ Ω N).2.1]
    exact kx_cls _ h
  have h4 : (kapL l ψ).toUnitHom (Chr.cls ℚ Ω N s) = 1 := by rw [kapL, (compAlg O N l hl.out).1, h3, map_one]
  exact congrArg Units.val h4

private theorem kx_pow (ψ : DirichletCharacter O N) {s : G ℚ Ω} (h : cycZ ℚ Ω l s = 1)
    (hk : Chr.dirG ℚ Ω (kapB l ψ) s = 1) : Chr.dirG ℚ Ω ψ s ^ orderOf (th0 l ψ) = 1 := by
  ext1
  show ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) ^ _ = 1
  have a1 : kapB l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) = 1 := congrArg Units.val hk
  have a3 : ψ = th0 l ψ * (kapB l ψ * kapL l ψ) := by rw [kapB, inv_mul_cancel_right, dirichletPrimeToLPart_mul_lPowerPart]
  have a4 : ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) = th0 l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) := by
    conv_lhs => rw [a3]
    rw [MulChar.mul_apply, MulChar.mul_apply, a1, kx_kapL ψ h, one_mul, mul_one]
  rw [a4, ← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe]

private theorem kx_unr (ψ : DirichletCharacter O N) {s : G ℚ Ω} (h : cycZ ℚ Ω l s = 1)
    (hψ : Chr.dirG ℚ Ω ψ s = 1) : Chr.dirG ℚ Ω (kapB l ψ) s = 1 := by
  ext1
  show kapB l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) = 1
  have a1 : ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) = 1 := congrArg Units.val hψ
  have a2 : kap l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) = 1 := by
    rw [kap, lPart, MulChar.pow_apply_coe, a1, one_pow]
  have a3 : kap l ψ = kapB l ψ * kapL l ψ := by rw [kapB, inv_mul_cancel_right]
  rwa [a3, MulChar.mul_apply, kx_kapL ψ h, mul_one] at a2

private theorem kx_ord (ψ : DirichletCharacter O N) :
    Chr.dirG ℚ Ω (kapB l ψ) ^ l ^ (orderOf ψ).factorization l = 1 := by
  have h1 : kap l ψ ^ l ^ (orderOf ψ).factorization l = 1 := by
    rw [← (partOrd _ l hl.out ψ ψ.orderOf_pos).1]
    exact pow_orderOf_eq_one _
  obtain ⟨-, -, hone, -, hpow, -⟩ := compAlg O N l hl.out
  have h2 : kapB l ψ ^ l ^ (orderOf ψ).factorization l = 1 := by
    rw [kapB, kapL, mul_pow, inv_pow, ← hpow, h1, hone, inv_one, one_mul]
  refine MonoidHom.ext fun s => Units.ext ?_
  show kapB l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) ^ _ = 1
  rw [← MulChar.pow_apply_coe, h2, MulChar.one_apply_coe]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Ws.kapEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (N : ℕ) [NeZero N] (ψ : DirichletCharacter c.O N), D.ψ = Chr.dirG ℚ Ω ψ → ∃ κ, Kap D κ := by
  intro Ω _ _ _ l hl c D hD N _ ψ hψ
  have hnd : ¬ l ∣ orderOf (th0 l ψ) := (partOrd _ l hl.out ψ ψ.orderOf_pos).2.2.1
  refine ⟨Chr.dirG ℚ Ω (kapB l ψ), ?_, ⟨_, kx_ord ψ⟩, fun A hA g hg => ?_, fun A hA => ?_, fun A hA g hg hb hk => ?_,
    orderOf (th0 l ψ), (Nat.Prime.coprime_iff_not_dvd hl.out).2 hnd, fun g hg hk => hψ ▸ kx_pow ψ hg hk⟩
  · refine Subgroup.isOpen_mono (fun s hs => ?_) (Chr.clsFacts ℚ Ω N).1
    rw [MonoidHom.mem_ker] at hs ⊢
    rw [Chr.dirG, MonoidHom.comp_apply, hs, map_one]
  · exact kx_unr ψ ((places ℚ Ω l A).2.2.2 (hA l hD.l_mem) hg) (hψ ▸ hD.psi_unr A hA hg)
  · refine ((compIne Ω N l hl.out A hA).2 c.O _).2.2 ?_
    obtain ⟨-, hmul, -, hinv, -, h6, -⟩ := compAlg c.O N l hl.out
    rw [kapB, kapL, hmul, hinv, (h6 _).1, mul_inv_cancel]
  · have h1 : cycZ ℚ Ω l g = 1 := (places ℚ Ω l A).2.2.2 (hA l (Finset.mem_singleton_self l)) hg
    have h2 : chiO ℚ Ω l c.O g = 1 := by rw [chiO, MonoidHom.comp_apply, h1, map_one]
    have h3 : D.Psi g = D.ψ g := by
      rw [Raw.Psi, Chr.Psi, MonoidHom.mul_apply, zpow_natCast, MonoidHom.pow_apply, h2, one_pow, one_mul]
    refine (congrFacts Ω l c).2.2.2.1 _ 1 _ hnd (hψ ▸ kx_pow ψ h1 hk) (one_pow _) ?_
    rw [← residue_eq_zero_iff, map_sub, Units.val_one, map_one, sub_eq_zero, ← h3]
    exact hb
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.QuadEx
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem quadEx_jac (p q : ℕ) (s : ℤˣ) (hq : q.Prime) (h8 : (p : ℤ) ≡ s [ZMOD 8]) (hpq : (p : ℤ) ≡ s [ZMOD q]) :
    jacobiSym q p = 1 := by
  have hp : Odd p := by
    rw [Nat.odd_iff]
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp only [Int.ModEq, Units.val_one, Units.val_neg] at h8 <;> omega
  rcases hq.eq_two_or_odd' with rfl | hq2
  · rw [Nat.cast_ofNat, jacobiSym.at_two hp, ZMod.χ₈_nat_eq_if_mod_eight]
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp only [Int.ModEq, Units.val_one, Units.val_neg] at h8
    · rw [if_neg (by omega), if_pos (by omega)]
    · rw [if_neg (by omega), if_pos (by omega)]
  · have e : jacobiSym p q = jacobiSym s q := jacobiSym.mod_left' hpq
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp only [Int.ModEq, Units.val_one, Units.val_neg] at h8 e
    · rw [jacobiSym.quadratic_reciprocity_one_mod_four' hq2 (by omega), e, jacobiSym.one_left]
    · have hq' := Nat.odd_iff.1 hq2
      rcases (by omega : q % 4 = 1 ∨ q % 4 = 3) with h | h
      · rw [jacobiSym.quadratic_reciprocity_one_mod_four h hp, e, jacobiSym.at_neg_one hq2, ZMod.χ₄_nat_one_mod_four h]
      · rw [jacobiSym.quadratic_reciprocity_three_mod_four h (by omega), e, jacobiSym.at_neg_one hq2,
          ZMod.χ₄_nat_three_mod_four h, neg_neg]

private theorem quadEx_prime (s : ℤˣ) (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) :
    ∃ (p : ℕ) (_ : Fact p.Prime), p ∉ S ∧ p ≠ 2 ∧ quadraticChar (ZMod p) (-1) = s ∧
      ∀ q ∈ S, quadraticChar (ZMod p) (q : ZMod p) = 1 := by
  have h0 : 8 * ∏ q ∈ S, q ≠ 0 := mul_ne_zero (by norm_num) (Finset.prod_ne_zero_iff.2 fun q hq => (hS q hq).ne_zero)
  have hc : IsCoprime (s : ℤ) ((8 * ∏ q ∈ S, q : ℕ) : ℤ) := ⟨(s⁻¹ : ℤˣ), 0, by simp⟩
  obtain ⟨p, hpn, hp, hps⟩ := Nat.forall_exists_prime_gt_and_zmodEq (S.sup id) h0 hc
  have h8 : (p : ℤ) ≡ s [ZMOD 8] := hps.of_dvd (by exact_mod_cast Int.natCast_dvd_natCast.2 (dvd_mul_right 8 _))
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : p ≠ 2 := by
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp only [Int.ModEq, Units.val_one, Units.val_neg] at h8 <;> omega
  refine ⟨p, inferInstance, fun h => absurd (Finset.le_sup (f := id) h) (not_le.2 hpn), h2, ?_, fun q hq => ?_⟩
  · have e := legendreSym.at_neg_one h2
    rw [legendreSym, Int.cast_neg, Int.cast_one] at e
    rw [e]
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp only [Int.ModEq, Units.val_one, Units.val_neg] at h8 ⊢
    · exact ZMod.χ₄_nat_one_mod_four (by omega)
    · exact ZMod.χ₄_nat_three_mod_four (by omega)
  · have e := quadEx_jac p q s (hS q hq) h8
      (hps.of_dvd (Int.natCast_dvd_natCast.2 ((Finset.dvd_prod_of_mem _ hq).mul_left 8)))
    rwa [← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast] at e

private theorem quadEx_cls {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (p q : ℕ) [hp : Fact p.Prime] (γ : G ℚ Ω)
    (h : ((cycZ ℚ Ω p γ : ℤ_[p]ˣ) : ℤ_[p]) = (q : ℤ_[p])) (u : (ZMod p)ˣ) (hu : (u : ZMod p) = q) : UpperTheory.V.Chr.cls ℚ Ω p γ = u := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero ((p : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩
  refine (UpperTheory.V.Chr.clsFacts ℚ Ω p).2.2.1 γ u fun ζ hζ => ?_
  have hζ' : ζ ^ p ^ 1 = 1 := by rwa [pow_one]
  have h1 := cyclotomicCharacter.spec p (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ] Ω) Ω γ) ζ hζ'
  have h2 : ((cyclotomicCharacter Ω p (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ] Ω) Ω γ) : ℤ_[p]ˣ) : ℤ_[p]) = (q : ℤ_[p]) := h
  rw [h2, map_natCast, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ'] at h1
  rw [hu, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ]
  exact h1

private theorem quadEx_val {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p q : ℕ} (h : p.Coprime q)
    (hq : A.valuation (q : Ω) < 1) : ¬ A.valuation (p : Ω) < 1 := fun hp => by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have hv : ∀ n : ℤ, A.valuation (n : Ω) ≤ 1 := fun n => (A.valuation_le_one_iff _).mpr (intCast_mem A n)
  have h1 : A.valuation ((a : Ω) * (p : Ω) + (b : Ω) * (q : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv a)) hp
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv b)) hq
  have h2 : (a : Ω) * (p : Ω) + (b : Ω) * (q : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  rw [h2, map_one] at h1
  exact lt_irrefl _ h1

theorem UpperTheory.V.Ws.quadEx :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (s : ℤˣ) (S : Finset ℕ), (∀ q ∈ S, q.Prime) → ∃ (p : ℕ) (η : G ℚ Ω →* ℤˣ), QuadAt p s S η := by
  intro Ω _ _ _ s S hS
  obtain ⟨p, hp, hpS, h2, hs, hq⟩ := quadEx_prime s S hS
  obtain ⟨hopen, -, -, hcc, hine⟩ := Chr.clsFacts ℚ Ω p
  let χ : DirichletCharacter ℤ p := quadraticChar (ZMod p)
  have hval : ∀ g : G ℚ Ω, ((Chr.dirG ℚ Ω χ g : ℤˣ) : ℤ) = quadraticChar (ZMod p) (Chr.cls ℚ Ω p g : (ZMod p)ˣ) := fun g => rfl
  have hle : (Chr.cls ℚ Ω p).ker ≤ (Chr.dirG ℚ Ω χ).ker := fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [Chr.dirG, MonoidHom.comp_apply, hg, map_one]
  have hopn : IsOpen ((Chr.dirG ℚ Ω χ).ker : Set (G ℚ Ω)) := Subgroup.isOpen_mono hle hopen
  obtain ⟨u, hu⟩ : ∃ u : (ZMod p)ˣ, quadraticChar (ZMod p) u = -1 := by
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
    have h0 : a ≠ 0 := by
      rintro rfl
      simp at ha
    exact ⟨Units.mk0 a h0, ha⟩
  refine ⟨p, Chr.dirG ℚ Ω χ, hp.out, hpS, hopn, ?_, fun A hA => (hine A hA).trans hle, fun A hA => ?_, fun σ hσ => ?_,
    fun q hqS A hA => ?_⟩
  · obtain ⟨g, hg⟩ := (Chr.clsOnto Ω p).1 u
    have ht : (Chr.dirG ℚ Ω χ).range = ⊤ := by
      refine eq_top_iff.2 fun t _ => ?_
      rcases Int.units_eq_one_or t with rfl | rfl
      · exact one_mem _
      · exact ⟨g, Units.ext (by rw [hval, hg, hu]; rfl)⟩
    rw [Subgroup.index_ker, ht, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]
  · have hm : u ∈ (proj p p).range := by
      rw [(projFacts p p hp.out).2.2.2.2.2.1, MonoidHom.mem_ker]
      have h1 : ordCompl[p] p = 1 := by
        rw [hp.out.factorization_self, pow_one, Nat.div_self hp.out.pos]
      have : Subsingleton (ZMod (ordCompl[p] p)) := by rw [h1]; infer_instance
      exact Units.ext (Subsingleton.elim _ _)
    rw [← (compIne Ω p p hp.out A hA).1] at hm
    obtain ⟨g, hg, hgu⟩ := hm
    exact ⟨g, hg, Units.ext (by rw [hval, hgu, hu]; rfl)⟩
  · exact Units.ext (by rw [hval, hcc σ hσ, Units.val_neg, Units.val_one, hs])
  · have hne : p ≠ q := fun h => hpS (h ▸ hqS)
    have hc : p.Coprime q := (Nat.coprime_primes hp.out (hS q hqS)).2 hne
    obtain ⟨-, -, γ, -, hD, hγ⟩ := Chr.decCyc Ω q A (hS q hqS) hA
    refine hD.trans (Subgroup.topologicalClosure_minimal _ (sup_le ?_ ((hine A (quadEx_val A hc hA)).trans hle))
      (Subgroup.isClosed_of_isOpen _ hopn))
    rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
    refine Units.ext ?_
    rw [hval, quadEx_cls p q γ (hγ p hne) (ZMod.unitOfCoprime q hc.symm) rfl, ZMod.coe_unitOfCoprime, hq q hqS, Units.val_one]
end

