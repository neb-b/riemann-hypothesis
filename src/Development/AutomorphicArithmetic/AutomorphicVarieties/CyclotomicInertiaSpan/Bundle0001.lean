module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CyclotomicInertiaSpan.OnePrimeOfTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CyclotomicInertiaSpan.CycCompat
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.B1

private theorem exists_primitiveRoot_algClosure_numberField (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (M : ℕ) [NeZero M] : ∃ ζ : Ω, IsPrimitiveRoot ζ M := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω M

private theorem cycN_apply_primitiveRoot_eq_pow (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (N : ℕ) [NeZero N] (g : G F Ω) {ζ : Ω} (hζ : IsPrimitiveRoot ζ N) :
    g ζ = ζ ^ ((cycN F Ω N g : (ZMod N)ˣ) : ZMod N).val := by
  have hu := (hζ.isUnit_unit NeZero.out).mem_rootsOfUnity
  have := modularCyclotomicCharacter.spec Ω (natCard_roots F Ω N)
    (MulSemiringAction.toRingAut (G F Ω) Ω g) hu
  simpa [cycN] using this

private theorem zmod_eq_intCast_of_primitiveRoot_pow_eq {Ω : Type} [Field Ω] {N : ℕ} [NeZero N] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ N) (a : ZMod N) (k : ℤ) (h : ζ ^ a.val = ζ ^ k) :
    a = (k : ZMod N) := by
  have h0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne N)
  have h1 : ζ ^ ((a.val : ℤ) - k) = 1 := by
    rw [zpow_sub₀ h0, zpow_natCast, h, div_self (zpow_ne_zero _ h0)]
  have h2 := (hζ.zpow_eq_one_iff_dvd _).mp h1
  have h3 : (((a.val : ℤ) - k : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h2
  push_cast at h3
  rw [ZMod.natCast_zmod_val] at h3
  exact sub_eq_zero.mp h3

theorem UpperTheory.V.B1.cycCompat :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (N : ℕ) [NeZero N], IsOpen ((cycN F Ω N).ker : Set (G F Ω)) ∧
    (∀ (M : ℕ) [NeZero M] (h : M ∣ N) (g : G F Ω), ZMod.unitsMap h (cycN F Ω N g) = cycN F Ω M g) ∧
    ∀ c : G F Ω, IsConjOm c.toRingEquiv → cycN F Ω N c = -1 := by
  intro F Ω _ _ _ _ _ N _
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_algClosure_numberField F Ω N
  refine ⟨?_, ?_, ?_⟩
  · haveI : FiniteDimensional F (IntermediateField.adjoin F {ζ}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic ζ).isIntegral
    refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin F {ζ}).fixingSubgroup) ?_
      (IntermediateField.fixingSubgroup_isOpen _)
    intro g hg
    have hgz : g ζ = ζ := by
      have := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg ζ
        (IntermediateField.mem_adjoin_simple_self F ζ)
      simpa [AlgEquiv.smul_def] using this
    rw [MonoidHom.mem_ker]
    apply Units.ext
    have := zmod_eq_intCast_of_primitiveRoot_pow_eq hζ _ 1 (by rw [← cycN_apply_primitiveRoot_eq_pow F Ω N g hζ, hgz, zpow_one])
    simpa using this
  · intro M _ h g
    obtain ⟨d, hd⟩ := id h
    have hη := hζ.pow (NeZero.pos N) (show N = d * M by rw [hd, mul_comm])
    have e1 : g (ζ ^ d) = (ζ ^ d) ^ ((cycN F Ω N g : (ZMod N)ˣ) : ZMod N).val := by
      rw [map_pow, cycN_apply_primitiveRoot_eq_pow F Ω N g hζ, ← pow_mul, ← pow_mul, mul_comm]
    have e2 := cycN_apply_primitiveRoot_eq_pow F Ω M g hη
    have key := zmod_eq_intCast_of_primitiveRoot_pow_eq hη _ (((cycN F Ω N g : (ZMod N)ˣ) : ZMod N).val : ℤ)
      (by rw [← e2, e1, zpow_natCast])
    apply Units.ext
    rw [key, Int.cast_natCast, ← ZMod.cast_eq_val, ZMod.unitsMap_def]
    rfl
  · intro c hc
    obtain ⟨j, hj⟩ := hc
    apply Units.ext
    have hN : ζ ^ N = 1 := hζ.pow_eq_one
    have hcz : c ζ = ζ⁻¹ := by
      apply j.injective
      have := hj ζ
      simp only [AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_ringEquiv] at this
      rw [this, map_inv₀]
      have hn : ‖j ζ‖ = 1 :=
        Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hN, map_one]) (NeZero.ne N)
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
      simp
    have := zmod_eq_intCast_of_primitiveRoot_pow_eq hζ _ (-1) (by rw [← cycN_apply_primitiveRoot_eq_pow F Ω N c hζ, hcz, zpow_neg_one])
    simpa using this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CyclotomicInertiaSpan.DecComm
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.B1

private theorem ringEquiv_eq_frobenius_pow_of_algebraic_over_zmod {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) k]
    [Algebra.IsAlgebraic (ZMod p) k] (ψ : k ≃+* k) (y : k) : ∃ n : ℕ, ψ y = y ^ (p ^ n) := by
  have hy : IsIntegral (ZMod p) y := (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  let L := IntermediateField.adjoin (ZMod p) ({y} : Set k)
  haveI : FiniteDimensional (ZMod p) L := IntermediateField.adjoin.finiteDimensional hy
  haveI : Finite L := Module.finite_of_finite (ZMod p)
  letI : Fintype L := Fintype.ofFinite L
  haveI : Normal (ZMod p) L := inferInstance
  let ψ' : k ≃ₐ[ZMod p] k := AlgEquiv.ofRingEquiv (f := ψ) (fun x => by
    have h := congrArg (fun g : ZMod p →+* k => g x)
      (Subsingleton.elim (ψ.toRingHom.comp (algebraMap (ZMod p) k)) (algebraMap (ZMod p) k))
    simpa using h)
  obtain ⟨i, hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) L).2 (ψ'.restrictNormal L)
  refine ⟨i.1, ?_⟩
  have hyL : y ∈ L := IntermediateField.mem_adjoin_simple_self _ _
  have h1 := AlgEquiv.restrictNormal_commutes ψ' L ⟨y, hyL⟩
  rw [← hi] at h1
  simp only [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card] at h1
  simp at h1
  exact h1.symm

private theorem ringEquiv_comm_of_algebraic_over_zmod {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) k]
    [Algebra.IsAlgebraic (ZMod p) k] (ψ χ : k ≃+* k) (y : k) : ψ (χ y) = χ (ψ y) := by
  obtain ⟨a, ha⟩ := ringEquiv_eq_frobenius_pow_of_algebraic_over_zmod p ψ y
  obtain ⟨b, hb⟩ := ringEquiv_eq_frobenius_pow_of_algebraic_over_zmod p χ y
  rw [ha, hb, map_pow, map_pow, ha, hb, ← pow_mul, ← pow_mul, mul_comm]

theorem UpperTheory.V.B1.decComm :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (p : ℕ) [Fact p.Prime] (B : ValuationSubring Ω), B.valuation (p : Ω) < 1 →
    ⁅Dec (F := F) B, Dec (F := F) B⁆ ≤ Ine (F := F) B := by
  intro F Ω _ _ _ _ _ p _ B hp
  rw [Subgroup.commutator_le]
  intro σ hσ τ hτ
  let D := ValuationSubring.decompositionSubgroup F B
  let k := IsLocalRing.ResidueField B
  have hpk : ((p : ℕ) : k) = 0 := by
    have : ((p : B) : Ω) = (p : Ω) := by simp
    have hm : (p : B) ∈ IsLocalRing.maximalIdeal B := by
      rw [ValuationSubring.valuation_lt_one_iff, this]; exact hp
    have := (IsLocalRing.residue_eq_zero_iff (p : B)).2 hm
    simpa using this
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 hpk
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  haveI : Algebra.IsAlgebraic (ZMod p) k := by
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
    haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
    haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
    refine ⟨fun y => ?_⟩
    obtain ⟨xb, rfl⟩ := IsLocalRing.residue_surjective y
    have hZ : IsAlgebraic ℤ (xb : Ω) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic _)
    obtain ⟨P, hP0, hPx⟩ := hZ
    have hQ : P.primPart.IsPrimitive := P.isPrimitive_primPart
    have hQx : Polynomial.aeval (xb : Ω) P.primPart = 0 := by
      have hc : P.content ≠ 0 := by
        rwa [Ne, Polynomial.content_eq_zero_iff]
      have h2 := hPx
      rw [Polynomial.eq_C_content_mul_primPart P, map_mul, Polynomial.aeval_C] at h2
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exfalso
        simp at h3
        exact hc h3
      · exact h3
    have hQmap : P.primPart.map (Int.castRingHom (ZMod p)) ≠ 0 := by
      intro h0
      have hd : Polynomial.C (p : ℤ) ∣ P.primPart := by
        rw [Polynomial.C_dvd_iff_dvd_coeff]
        intro i
        have h4 := congrArg (fun f => f.coeff i) h0
        simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at h4
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h4
      have hu := hQ (p : ℤ) hd
      rw [Int.isUnit_iff] at hu
      have := (Fact.out : p.Prime).two_le
      omega
    refine ⟨P.primPart.map (Int.castRingHom (ZMod p)), hQmap, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have e1 : (algebraMap (ZMod p) k).comp (Int.castRingHom (ZMod p)) =
        (IsLocalRing.residue B).comp (Int.castRingHom B) := Subsingleton.elim _ _
    rw [e1, ← Polynomial.hom_eval₂]
    have e2 : P.primPart.eval₂ (Int.castRingHom B) xb = 0 := by
      apply Subtype.val_injective
      have e3 := Polynomial.hom_eval₂ P.primPart (Int.castRingHom B) B.subtype xb
      have e4 : B.subtype.comp (Int.castRingHom B) = algebraMap ℤ Ω := Subsingleton.elim _ _
      rw [e4] at e3
      change B.subtype _ = _
      rw [e3]
      simpa [Polynomial.aeval_def] using hQx
    rw [e2, map_zero]
  have hcomm : ∀ (g h : D) (y : k), g • h • y = h • g • y := fun g h y =>
    ringEquiv_comm_of_algebraic_over_zmod p (MulSemiringAction.toRingEquiv D k g) (MulSemiringAction.toRingEquiv D k h) y
  let g : D := ⟨σ, hσ⟩
  let h : D := ⟨τ, hτ⟩
  refine ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    exact D.mul_mem (D.mul_mem (D.mul_mem hσ hτ) (D.inv_mem hσ)) (D.inv_mem hτ)
  · intro x hx
    have hxB : x ∈ B := (ValuationSubring.valuation_le_one_iff B x).1 hx
    let xb : B := ⟨x, hxB⟩
    have key : IsLocalRing.residue B ((g * h * g⁻¹ * h⁻¹) • xb) = IsLocalRing.residue B xb := by
      rw [IsLocalRing.ResidueField.residue_smul, mul_smul, mul_smul, mul_smul,
        hcomm g h, smul_inv_smul, smul_inv_smul]
    have hmem : (g * h * g⁻¹ * h⁻¹) • xb - xb ∈ IsLocalRing.maximalIdeal B := by
      rwa [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    rw [ValuationSubring.valuation_lt_one_iff] at hmem
    convert hmem using 2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CyclotomicInertiaSpan.IneSpan
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.B1

theorem UpperTheory.V.B1.ineSpan :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N : Subgroup (G ℚ Ω)) (S : Finset ℕ) (B : ℕ → ValuationSubring Ω), IsOpen (N : Set (G ℚ Ω)) → commutator (G ℚ Ω) ≤ N →
    (∀ p ∈ S, p.Prime ∧ (B p).valuation (p : Ω) < 1) →
    (∀ B' : ValuationSubring Ω, (∀ p ∈ S, ¬ B'.valuation (p : Ω) < 1) → Ine (F := ℚ) B' ≤ N) → N ⊔ (⨆ p ∈ S, Ine (F := ℚ) (B p)) = ⊤ := by
  intro Ω _ _ _ N S B ho hc hB hI
  have hle : ∀ p ∈ S, Ine (F := ℚ) (B p) ≤ N ⊔ (⨆ p ∈ S, Ine (F := ℚ) (B p)) := fun p hp =>
    (le_iSup₂ (f := fun p (_ : p ∈ S) => Ine (F := ℚ) (B p)) p hp).trans le_sup_right
  have hN : N ≤ N ⊔ (⨆ p ∈ S, Ine (F := ℚ) (B p)) := le_sup_left
  generalize N ⊔ (⨆ p ∈ S, Ine (F := ℚ) (B p)) = M at hle hN
  have hn : M.Normal := Subgroup.Normal.of_commutator_le _ (hc.trans hN)
  refine B3.minkowski Ω M hn (Subgroup.isOpen_mono hN ho) fun B' => ?_
  by_cases h : ∀ p ∈ S, ¬ B'.valuation (p : Ω) < 1
  · exact (hI B' h).trans hN
  · push Not at h
    obtain ⟨p, hp, hv⟩ := h
    obtain ⟨g, hg⟩ := (B3.placesQ Ω).2.2 p (B p) B' (hB p hp).1 (hB p hp).2 hv
    intro x hx
    have := hn.conj_mem _ (hle p hp (hg x hx)) g
    simpa [mul_assoc] using this
end

