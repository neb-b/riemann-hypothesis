module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0009
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0132
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoCardLen
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private theorem card_simple (O : Type) [CommRing O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M]
    [h : IsSimpleModule O M] : Nat.card M = Nat.card (ResidueField O) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp h
  obtain rfl : I = maximalIdeal O := IsLocalRing.eq_maximalIdeal hI
  exact Nat.card_congr e.toEquiv

private theorem card_of_finiteLength (O : Type) [CommRing O] [IsLocalRing O] (M : Type) [AddCommGroup M]
    [Module O M] (h : IsFiniteLength O M) :
    ∃ k : ℕ, Module.length O M = k ∧ Nat.card M = Nat.card (ResidueField O) ^ k := by
  induction h with
  | of_subsingleton =>
    refine ⟨0, Module.length_eq_zero, ?_⟩
    rw [pow_zero]
    exact Nat.card_of_subsingleton 0
  | @of_simple_quotient M _ _ N _ hS ih =>
    obtain ⟨k, hk, hc⟩ := ih
    refine ⟨k + 1, ?_, ?_⟩
    · rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N), hk, Module.length_eq_one]
      norm_cast
    · have hq : Nat.card (M ⧸ N) = Nat.card (ResidueField O) := card_simple O (M ⧸ N)
      have hsplit := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup
      change Nat.card M = Nat.card (M ⧸ N) * Nat.card N at hsplit
      rw [hsplit, hq, hc, pow_succ, mul_comm]

theorem UpperTheory.V.X.So.cardLen :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O], 1 < Nat.card (ResidueField O) ∧ ∀ (N : Type) [AddCommGroup N] [Module O N], (Module.length O N ≠ ⊤ ↔ Finite N) ∧ (Finite N → Nat.card N = Nat.card (ResidueField O) ^ (Module.length O N).toNat) := by
  intro l _ O _ _ _ _ _
  have : CharZero O := charZero_of_injective_algebraMap (UpperTheory.V.Base.dvrFacts l O).1
  have hres : Finite (ResidueField O) := (UpperTheory.V.abelian₂.dvr_finite l O).2.1
  have h1 : 1 < Nat.card (ResidueField O) := Finite.one_lt_card
  refine ⟨h1, fun N _ _ => ?_⟩
  have hfl : Finite N → IsFiniteLength O N := fun _ =>
    isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩
  refine ⟨⟨fun h => ?_, fun h => Module.length_ne_top_iff.2 (hfl h)⟩, fun h => ?_⟩
  · obtain ⟨k, -, hk⟩ := card_of_finiteLength O N (Module.length_ne_top_iff.1 h)
    exact Nat.finite_of_card_ne_zero (hk ▸ pow_ne_zero k (by omega))
  · obtain ⟨k, hk1, hk⟩ := card_of_finiteLength O N (hfl h)
    rw [hk, hk1, ENat.toNat_coe]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoCobIndex
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

theorem UpperTheory.V.X.So.cobIndex :
    ∀ (O Γ : Type) [CommRing O] [IsDomain O] [CharZero O] [Group Γ] (θ : Γ →* Oˣ) (z : Γ → O), Coc θ z → ∀ U D : Subgroup Γ, U.relIndex D ≠ 0 → CobOn θ z (U ⊓ D) → CobOn θ z D := by
  intro O Γ _ _ _ _ θ z hz U D hUD hcob
  obtain ⟨a, ha, m, hm⟩ := hcob
  haveI : (U.subgroupOf D).FiniteIndex := ⟨hUD⟩
  haveI : Fintype (D ⧸ U.subgroupOf D) := Fintype.ofFinite _
  let T : D ⧸ U.subgroupOf D → O := fun q => a * z ((q.out : D) : Γ) - (θ ((q.out : D) : Γ) : O) * m
  have key : ∀ (g : D) (q : D ⧸ U.subgroupOf D), T (g • q) = a * z (g : Γ) + (θ (g : Γ) : O) * T q := by
    intro g q
    have e1 : g • q = (QuotientGroup.mk (g * q.out) : D ⧸ U.subgroupOf D) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf D) (g * q.out)
    have hhU : ((h : D) : Γ) ∈ U ⊓ D := ⟨Subgroup.mem_subgroupOf.1 h.2, (h : D).2⟩
    have hmh := hm _ hhU
    simp only [T]
    rw [e1, hh]
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul]
    rw [hz, hz]
    simp only [map_mul, Units.val_mul]
    linear_combination (θ (g : Γ) : O) * (θ ((q.out : D) : Γ) : O) * hmh
  have hn : (Fintype.card (D ⧸ U.subgroupOf D) : O) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Fintype.card_ne_zero
  refine ⟨(Fintype.card (D ⧸ U.subgroupOf D) : O) * a, mul_ne_zero hn ha, -(∑ q, T q), ?_⟩
  intro g hg
  have hs : ∑ q, T ((MulAction.toPerm (⟨g, hg⟩ : D)) q) = ∑ q, T q := Equiv.sum_comp _ T
  simp only [MulAction.toPerm_apply, key, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hs
  linear_combination hs
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoCobLim
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private theorem cont_lev {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Γ : Type} [TopologicalSpace Γ]
    (a : O) (ha : a ≠ 0) (z : Γ → O) (hz : Alg.AdicCont (maximalIdeal O) z) :
    Continuous fun g => Lev.mk a (z g) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hle : ∀ x, x ∈ maximalIdeal O ^ n → a ∣ x := by
    intro x hx
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hx
    rw [hu, Units.mul_left_dvd]
    exact hx
  have hlc := (IsLocallyConstant.iff_eventually_eq _).1 (hz n)
  refine ((IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_).continuous
  filter_upwards [hlc x] with y hy
  rw [Ideal.Quotient.eq] at hy
  rw [← sub_eq_zero, ← map_sub, Lev.mk_eq_zero]
  exact hle _ hy

private theorem lev_kill {O : Type} [CommRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ] (θ : Γ →* Oˣ) (a : O) (B : ℕ)
    (hf : Finite (H1 (scalRep (Lev a) θ))) (hB : Nat.card (H1 (scalRep (Lev a) θ)) ≤ B) (z : Γ → O) (hz : Coc θ z)
    (hc : Continuous fun g => Lev.mk a (z g)) :
    ∃ m : O, ∀ g, a ∣ (B.factorial : O) * z g - ((θ g : O) * m - m) := by
  set ρ := scalRep (Lev a) θ with hρ
  have hρg : ∀ g (x : Lev a), ρ g x = (θ g : O) • x := fun _ _ => rfl
  have hmem : (fun g => Lev.mk a (z g)) ∈ Z1 ρ := by
    rw [mem_Z1_iff_cocycle]
    refine ⟨hc, fun g h => ?_⟩
    rw [hz, hρg, map_add (f := _), ← smul_eq_mul, map_smul]
  let ζ : Z1 ρ := ⟨_, hmem⟩
  let q : H1 ρ := Submodule.Quotient.mk ζ
  have hpos : 0 < Nat.card (H1 ρ) := Nat.card_pos
  have hq : B.factorial • q = 0 := by
    obtain ⟨k, hk⟩ := Nat.dvd_factorial hpos hB
    rw [hk, mul_comm, mul_nsmul, card_nsmul_eq_zero']
  have hq2 : (Submodule.Quotient.mk (B.factorial • ζ) : H1 ρ) = 0 := by
    rw [Submodule.Quotient.mk_smul]
    exact hq
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hq2
  obtain ⟨mb, hmb⟩ := (mem_coboundaries1 ρ _).1 hq2
  obtain ⟨m, rfl⟩ := Lev.mk_surjective a mb
  refine ⟨m, fun g => ?_⟩
  rw [← Lev.mk_eq_zero]
  have := hmb g
  simp only [Submodule.subtype_apply, Submodule.coe_smul_of_tower, Pi.smul_apply] at this
  rw [map_sub, map_sub, ← nsmul_eq_mul, map_nsmul, this, hρg, ← smul_eq_mul, map_smul, sub_self]

theorem UpperTheory.V.X.So.cobLim :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (θ : Γ →* Oˣ) (p : O) (B : ℕ), p ≠ 0 → p ∈ maximalIdeal O → (∃ g, θ g ≠ 1) → (∀ r : ℕ, Finite (H1 (scalRep (Lev (p ^ r)) θ)) ∧ Nat.card (H1 (scalRep (Lev (p ^ r)) θ)) ≤ B) → ∀ z : Γ → O, Coc θ z → Alg.AdicCont (maximalIdeal O) z → CobOn θ z ⊤ := by
  intro O _ _ _ _ Γ _ _ θ p B hp0 hpm hθ hfin z hz hcont
  obtain ⟨g0, hg0⟩ := hθ
  have hcl : ∀ r : ℕ, ∃ m : O, ∀ g, p ^ r ∣ (B.factorial : O) * z g - ((θ g : O) * m - m) := fun r =>
    lev_kill θ (p ^ r) B (hfin r).1 (hfin r).2 z hz (cont_lev (p ^ r) (pow_ne_zero r hp0) z hcont)
  have hpu : ¬IsUnit p := (IsLocalRing.mem_maximalIdeal p).1 hpm
  have hkey : ∀ g, ((θ g0 : O) - 1) * ((B.factorial : O) * z g) = ((θ g : O) - 1) * ((B.factorial : O) * z g0) := by
    intro g
    by_contra hne
    obtain ⟨n, hn⟩ := FiniteMultiplicity.of_not_isUnit hpu (sub_ne_zero.2 hne)
    apply hn
    obtain ⟨m, hm⟩ := hcl (n + 1)
    have e : ((θ g0 : O) - 1) * ((B.factorial : O) * z g) - ((θ g : O) - 1) * ((B.factorial : O) * z g0)
        = ((θ g0 : O) - 1) * ((B.factorial : O) * z g - ((θ g : O) * m - m))
          - ((θ g : O) - 1) * ((B.factorial : O) * z g0 - ((θ g0 : O) * m - m)) := by ring
    rw [e]
    exact dvd_sub (dvd_mul_of_dvd_right (hm g) _) (dvd_mul_of_dvd_right (hm g0) _)
  refine ⟨((θ g0 : O) - 1) * (B.factorial : O), ?_, (B.factorial : O) * z g0, ?_⟩
  · refine mul_ne_zero (sub_ne_zero.2 fun h => hg0 (Units.val_eq_one.1 h)) ?_
    exact Nat.cast_ne_zero.2 (Nat.factorial_ne_zero B)
  · intro g _
    rw [mul_assoc, hkey g]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoCobPlace
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X
open scoped Pointwise

theorem UpperTheory.V.X.So.cobPlace :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (O : Type) [CommRing O] (θ : G k Ω →* Oˣ) (z : G k Ω → O), Coc θ z → ∀ (v : HeightOneSpectrum (𝓞 k)) (A A' : ValuationSubring Ω), IsPlaceOver A v → IsPlaceOver A' v → CobOn θ z (Dec (F := k) A) → CobOn θ z (Dec (F := k) A') := by
  intro k Ω _ _ _ _ _ O _ θ z hz v A A' hA hA' hcob
  obtain ⟨a, ha, m, hm⟩ := hcob
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_over hA hA'
  refine ⟨a, ha, (θ g : O) * m - a * z g, ?_⟩
  intro h hh
  obtain ⟨h0, hh0, rfl⟩ : ∃ h0 ∈ Dec (F := k) A, h = g * h0 * g⁻¹ := by
    refine ⟨g⁻¹ * h * g, ?_, by group⟩
    rw [mem_Dec] at hh ⊢
    rw [mul_smul, mul_smul, hh, inv_smul_smul]
  have e := hm h0 hh0
  have hz1 : z 1 = 0 := by
    have h11 := hz 1 1
    rw [one_mul, map_one, Units.val_one, one_mul] at h11
    linear_combination -h11
  have hinv : (θ g : O) * z g⁻¹ = - z g := by
    have h2 := hz g g⁻¹
    rw [mul_inv_cancel, hz1] at h2
    linear_combination -h2
  have hθ : θ (g * h0 * g⁻¹) = θ h0 := by
    rw [map_mul, map_mul, map_inv, mul_comm (θ g), mul_inv_cancel_right]
  rw [hθ, hz (g * h0) g⁻¹, hz g h0, map_mul, Units.val_mul]
  linear_combination (θ g : O) * e + a * (θ h0 : O) * hinv
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoCoefOf
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private theorem int_iff_norm {l : ℕ} [Fact l.Prime] {K : Type} [Field K]
    [Algebra ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
    (φ : K →ₐ[ℚ_[l]] PadicAlgCl l) (x : K) : IsIntegral ℤ_[l] x ↔ ‖φ x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖φ x‖ = spectralValue (minpoly ℚ_[l] (φ x)) := rfl
  rw [h0, minpoly.algHom_eq φ φ.injective, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by
      rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

theorem UpperTheory.V.X.So.coefOf :
    ∀ (l : ℕ) [Fact l.Prime] (E : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] E], ∃ c : HV.Coef l, ∀ x : PadicAlgCl l, x ∈ c.O ↔ x ∈ E ∧ ‖x‖ ≤ 1 := by
  intro l _ K _
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l K
  let f : K →ₐ[ℤ_[l]] PadicAlgCl l := K.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
  refine ⟨⟨(integralClosure ℤ_[l] K).map f, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e,
    Module.Finite.equiv e.toLinearEquiv⟩, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, (int_iff_norm K.val y).1 hy⟩
  · rintro ⟨hx, hn⟩
    exact ⟨⟨x, hx⟩, (int_iff_norm K.val ⟨x, hx⟩).2 hn, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoContLev
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private theorem locConst {Γ A : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group A] (ψ : Γ →* A)
    (h : IsOpen (ψ.ker : Set Γ)) : IsLocallyConstant ψ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantMaps.locConst ψ h

private theorem dvd_pow_l (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (a : O) (ha : a ≠ 0) : ∃ N : ℕ, a ∣ (l : O) ^ N := by
  obtain ⟨-, -, -, -, -, h0, -, hval, -⟩ := dvrFacts l O
  rw [hval, Ne, IsDiscreteValuationRing.addVal_eq_zero_iff] at h0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨N, hN⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
  have hl : ϖ ∣ (l : O) := by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
    exact h0
  exact ⟨N, hN.dvd.trans (pow_dvd_pow_of_dvd hl N)⟩

private theorem locConst_smul (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (M : Type)
    [AddCommGroup M] [Module O M] (N : ℕ) (m : M) (hm : (l : O) ^ N • m = 0) :
    IsLocallyConstant fun c : ℤ_[l] => algebraMap ℤ_[l] O c • m := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro c
  have hp : (0 : ℝ) < (l : ℝ) ^ (-(N : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds c hp] with x hx
  rw [Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton'] at hx
  obtain ⟨t, ht⟩ := hx
  rw [← sub_eq_zero, ← sub_smul, ← map_sub, ← ht, map_mul, map_pow, map_natCast, mul_smul, hm, smul_zero]

theorem UpperTheory.V.X.So.contLev :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (ψ : G k Ω →* Oˣ) (n : ℤ), IsOpen (ψ.ker : Set (G k Ω)) → ∀ (a : O) (M : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation O (G k Ω) M), IsLev a (ψ * chiO k Ω l O ^ n) ρ → ContAction ρ := by
  intro k Ω _ _ _ _ _ l _ O _ _ _ _ _ ψ n hψ a M _ _ _ _ ρ h
  have hc := (contTw k Ω l).1
  obtain ⟨N, b, hb⟩ := dvd_pow_l l O a h.ne
  obtain ⟨e⟩ := h.cyc
  refine continuous_prod_of_discrete_right.2 fun m => ?_
  have hm : (l : O) ^ N • m = 0 := by
    apply e.injective
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e m)
    rw [map_smul, map_zero, ← hx]
    show Ideal.Quotient.mk _ ((l : O) ^ N * x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, hb, mul_assoc]
    exact dvd_mul_right _ _
  have h1 := (locConst_smul l O M N m hm).comp_continuous
    (f := fun g => ((cycZ k Ω l g ^ n : ℤ_[l]ˣ) : ℤ_[l])) (Units.continuous_val.comp (hc.zpow n))
  have h2 := ((locConst ψ hψ).prodMk h1).comp fun p : Oˣ × M => (p.1 : O) • p.2
  refine h2.continuous.congr fun g => ?_
  show (ψ g : O) • (algebraMap ℤ_[l] O ((cycZ k Ω l g ^ n : ℤ_[l]ˣ) : ℤ_[l]) • m) = ρ g m
  have e' : chiO k Ω l O g ^ n = Units.map (algebraMap ℤ_[l] O).toMonoidHom (cycZ k Ω l g ^ n) :=
    (map_zpow (Units.map (algebraMap ℤ_[l] O).toMonoidHom) (cycZ k Ω l g) n).symm
  rw [h.act]
  show _ = ((ψ g * chiO k Ω l O g ^ n : Oˣ) : O) • m
  rw [Units.val_mul, mul_smul, e']
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDecNe
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private theorem one_lt_normV {k : Type} [Field k] [NumberField k] (v : HeightOneSpectrum (𝓞 k)) : 1 < normV v := by
  have h : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  rw [h]
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h1 => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h1)
  omega

private theorem cyc_ne (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ)
    [Fact l.Prime] (v : HeightOneSpectrum (𝓞 k)) (A : ValuationSubring Ω) (hA : IsPlaceOver A v) (n : ℤ) (hn : n ≠ 0) :
    ∃ g : G k Ω, g ∈ Dec (F := k) A ∧ cycZ k Ω l g ^ n ≠ 1 := by
  by_cases hl : ((l : ℕ) : 𝓞 k) ∈ v.asIdeal
  · exact GlobalTheory.T.exists_decompositionGroup_cyclotomicCharacter_zpow_ne_one k Ω l v A hl hA n hn
  · obtain ⟨γ, hγ⟩ := exists_isFrob hA
    refine ⟨γ, hγ.1, fun h => ?_⟩
    have hc := cycZ_of_isFrob hl hA hγ
    have h2 : cycZ k Ω l γ ^ n.natAbs = 1 := by
      rcases Int.natAbs_eq n with e | e
      · rw [← zpow_natCast, ← e, h]
      · rw [e, zpow_neg, inv_eq_one, zpow_natCast] at h; exact h
    have h3 := congrArg (Units.val : ℤ_[l]ˣ → ℤ_[l]) h2
    rw [Units.val_pow_eq_pow_val, hc, Units.val_one] at h3
    have h4 : normV v ^ n.natAbs = 1 := by exact_mod_cast h3
    exact (Nat.one_lt_pow (Int.natAbs_ne_zero.2 hn) (one_lt_normV v)).ne' h4

theorem UpperTheory.V.X.So.decNe :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (ψ : G k Ω →* Oˣ), IsOpen (ψ.ker : Set (G k Ω)) → ∀ n : ℤ, n ≠ 0 → ∀ (v : HeightOneSpectrum (𝓞 k)) (A : ValuationSubring Ω), IsPlaceOver A v → ∃ g ∈ Dec (F := k) A, (ψ * chiO k Ω l O ^ n) g ≠ 1 := by
  intro k Ω _ _ _ _ _ l _ O _ _ _ _ _ ψ hψ n hn v A hA
  haveI : IsGalois k Ω := {}
  haveI : Finite (G k Ω ⧸ ψ.ker) := Subgroup.quotient_finite_of_isOpen _ hψ
  have hm : ψ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain ⟨g, hg, hne⟩ := cyc_ne k Ω l v A hA (n * (ψ.ker.index : ℤ)) (mul_ne_zero hn (Int.natCast_ne_zero.2 hm))
  refine ⟨g, hg, fun h => hne ?_⟩
  have hinj := (dvrFacts l O).1
  have h1 : ψ g ^ ψ.ker.index = 1 := by
    rw [← map_pow]; exact ψ.ker.pow_index_mem g
  have h2 : ψ g * chiO k Ω l O g ^ n = 1 := h
  have h3 : chiO k Ω l O g ^ (n * (ψ.ker.index : ℤ)) = 1 := by
    have := congrArg (· ^ ψ.ker.index) h2
    simp only [mul_pow, h1, one_mul, one_pow] at this
    rw [zpow_mul, zpow_natCast, this]
  apply Units.map_injective (f := (algebraMap ℤ_[l] O).toMonoidHom) hinj
  rw [map_zpow, map_one]
  exact h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLine
section
noncomputable section

open IsLocalRing UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.X

variable {O : Type} [CommRing O] [IsLocalRing O] {G Γ : Type} [Group G] [Group Γ] {ι : Type} (F : Frame O G Γ ι)

def etaO : Γ →* Oˣ := (Units.map (Int.castRingHom O).toMonoidHom).comp F.η

def lineChar (j : ℤ) (s : ℕ) : Γ →* Oˣ := F.Ψ ^ j * etaO F ^ s

def LineVan [TopologicalSpace Γ] (j : ℤ) (θ : Γ →* Oˣ) : Prop :=
  ∀ z : Γ → O, Coc θ z → Alg.AdicCont (maximalIdeal O) z →
    (∀ v ∉ F.Tb, ∀ s ∈ F.Nv v, z (F.loc v s) = 0) →
    (j = 0 → ∀ v ∈ F.Tb, ∀ s ∈ F.Iv v, z (F.loc v s) = 0) →
    (j < 0 → ∃ y : O, ∀ g : F.D F.vl, F.ηv F.vl g = 1 → z (F.loc _ g) = (θ (F.loc _ g) : O) * y - y) →
    CobOn θ z ⊤

end UpperTheory.V.X

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoScal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private def subEq {R R' X : Type} [CommRing R] [CommRing R'] [AddCommGroup X] [Module R X] [Module R' X]
    (Z : Submodule R X) (Z' : Submodule R' X) (hZ : ∀ x, x ∈ Z ↔ x ∈ Z') : Z ≃+ Z' where
  toFun x := ⟨x.1, (hZ _).1 x.2⟩
  invFun x := ⟨x.1, (hZ _).2 x.2⟩
  map_add' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

private theorem quotEq {R R' X : Type} [CommRing R] [CommRing R'] [AddCommGroup X] [Module R X] [Module R' X]
    (Z B : Submodule R X) (Z' B' : Submodule R' X)
    (hZ : ∀ x, x ∈ Z ↔ x ∈ Z') (hB : ∀ x, x ∈ B ↔ x ∈ B') :
    Nonempty ((Z ⧸ B.comap Z.subtype) ≃+ (Z' ⧸ B'.comap Z'.subtype)) := by
  refine ⟨QuotientAddGroup.congr (B.comap Z.subtype).toAddSubgroup (B'.comap Z'.subtype).toAddSubgroup (subEq Z Z' hZ) ?_⟩
  ext x
  simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hB _).1 hy
  · intro hx
    exact ⟨⟨x.1, (hZ _).2 x.2⟩, (hB _).2 hx, rfl⟩

theorem UpperTheory.V.X.So.scal :
    ∀ (R R' : Type) [CommRing R] [CommRing R'] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (M : Type) [AddCommGroup M] [Module R M] [Module R' M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M) (ρ' : Representation R' Γ M), (∀ g m, ρ g m = ρ' g m) → Nonempty (H0 ρ ≃+ H0 ρ') ∧ Nonempty (H1 ρ ≃+ H1 ρ') ∧ Nonempty (H2 ρ ≃+ H2 ρ') := by
  intro R R' _ _ Γ _ _ M _ _ _ _ _ ρ ρ' h
  have hd : ∀ c, d1 ρ c = d1 ρ' c := by
    intro c
    funext p
    obtain ⟨g, k⟩ := p
    rw [d1_apply, d1_apply, h]
  refine ⟨⟨subEq _ _ fun x => ?_⟩, quotEq _ _ _ _ (fun x => ?_) (fun x => ?_),
    quotEq _ _ _ _ (fun x => ?_) (fun x => ?_)⟩
  · simp only [mem_riemannRochSpace_iff_regularAt_everywhere, h]
  · simp only [mem_Z1_iff_cocycle, h]
  · simp only [mem_coboundaries1, h]
  · simp only [mem_cocycles2, h]
  · simp only [separated_dvr_second_cohomology_mem, hd]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.UnramifiedCocycleIsCoboundaryOfBernoulliUnit
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.Base UpperTheory.V.ML UpperTheory.V.Bern

namespace UpperTheory.V.X

def prodX {R : Type} [CommRing R] {f n : ℕ} (φ : DirichletCharacter R f) (ξ : DirichletCharacter R (2 ^ n)) :
    DirichletCharacter R (f * 2 ^ n) :=
  DirichletCharacter.changeLevel (dvd_mul_right f (2 ^ n)) φ * DirichletCharacter.changeLevel (dvd_mul_left (2 ^ n) f) ξ

structure XData (l d : ℕ) {R : Type} [CommRing R] {f n : ℕ} (φ : DirichletCharacter R f) (ξ : DirichletCharacter R (2 ^ n)) : Prop where
  d_pos : 0 < d
  four : 4 ∣ l ^ d - 1
  f_odd : Odd f
  prim : φ.IsPrimitive
  ord : orderOf φ ∣ l ^ d - 1
  prim2 : ξ.IsPrimitive
  big : f * 4 ^ (l ^ d - 1).factorization 2 ≤ 2 ^ n
  odd : φ (-1) * ξ (-1) = -1

def LemmaX : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (d f n : ℕ) (φ : DirichletCharacter (PadicAlgCl l) f) (ξ : DirichletCharacter (PadicAlgCl l) (2 ^ n)),
    XData l d φ ξ → ‖genB 1 (prodX φ ξ : ZMod (f * 2 ^ n) → PadicAlgCl l)‖ = 1

section

variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

def redChar {O k : Type} [CommRing O] [Field k] (red : O →+* k) {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) : G ℚ Ω →* kˣ :=
  (Units.map red.toMonoidHom).comp (Chr.dirG ℚ Ω χ)

variable {Ω}

def UnrEv (l : ℕ) {k : Type} [Field k] (γ : G ℚ Ω →* kˣ) (c : G ℚ Ω → k) : Prop :=
  ∀ A : ValuationSubring Ω, ∃ H : Subgroup (G ℚ Ω), ¬ l ∣ H.relIndex (Ine (F := ℚ) A ⊓ γ.ker) ∧
    ∀ g ∈ H, g ∈ Ine (F := ℚ) A → γ g = 1 → c g = 0

end

def UnramifiedCocycleIsCoboundaryOfBernoulliUnit : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (c : HV.Coef l) (k : Type) [Field k] [CharP k l]
    (red : c.O →+* k) (N : ℕ) [NeZero N] (χ : DirichletCharacter c.O N), χ ≠ 1 → ¬ l ∣ orderOf χ →
    (∃ g : G ℚ Ω, (redChar Ω red χ g : k) ≠ red (chiO (k := ℚ) (Ω := Ω) l c.O g : c.O)) →
    ‖genB 1 (χ⁻¹.ringHomComp c.O.val.toRingHom : ZMod N → PadicAlgCl l)‖ = 1 →
    ∀ z : G ℚ Ω → k, IsCoc (redChar Ω red χ) z → UnrEv l (redChar Ω red χ) z → ∃ m : k, ∀ g, z g = (redChar Ω red χ g : k) * m - m

def CorX : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : HV.Coef l) (k : Type) [Field k] [CharP k l]
    (red : c.O →+* k) (d f n : ℕ) [NeZero (f * 2 ^ n)] (φ : DirichletCharacter c.O f) (ξ : DirichletCharacter c.O (2 ^ n)), XData l d φ ξ →
    ∀ γ : G ℚ Ω →* kˣ, (γ = redChar Ω red (prodX φ ξ) ∨ γ = (redChar Ω red (prodX φ ξ))⁻¹) →
    ∀ z : G ℚ Ω → k, IsCoc γ z → UnrEv l γ z → ∃ m : k, ∀ g, z g = (γ g : k) * m - m

end UpperTheory.V.X

end
end

