module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0288
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0043
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.TameGen

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScStrip
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem valuation_not_lt_one_of_coprime {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {l N : ℕ} (h : Nat.Coprime l N)
    (hl : B.valuation (l : Ω) < 1) : ¬ B.valuation (N : Ω) < 1 := by
  intro hN
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have e : (a : Ω) * (l : Ω) + (b : Ω) * (N : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have key : ∀ (c : ℤ) (x : Ω), B.valuation x < 1 → B.valuation ((c : Ω) * x) < 1 := by
    intro c x hx
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((B.valuation_le_one_iff _).2 (intCast_mem B c))) hx
  have := B.valuation.map_add_lt (key a _ hl) (key b _ hN)
  rw [e, map_one] at this
  exact lt_irrefl _ this

private theorem eq_idempotent_mul_add_of_mul_sub_eq {Ω : Type} [Field Ω] {a b : ℕ} (h : Nat.Coprime a b) {x y : Ω} (hy : y ≠ 0)
    (ha : x ^ a = y ^ a) (hb : x ^ b = y ^ b) : x = y := by
  have h1 : (x / y) ^ a = 1 := by rw [div_pow, ha, div_self (pow_ne_zero _ hy)]
  have h2 : (x / y) ^ b = 1 := by rw [div_pow, hb, div_self (pow_ne_zero _ hy)]
  have h3 : (x / y) ^ (Nat.gcd a b) = 1 := pow_gcd_eq_one.2 ⟨h1, h2⟩
  rw [h.gcd_eq_one, pow_one] at h3
  exact (div_eq_one_iff_eq hy).1 h3

theorem UpperTheory.V.Fr.sc_strip :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (C : Type) [Group C] (χ : G ℚ Ω →* C) (r N : ℕ), N ≠ 0 → ¬ l ∣ N → Af.KillsMu (l ^ r * N) χ → ∀ B : ValuationSubring Ω, B.valuation (l : Ω) < 1 → Ine (F := ℚ) B ≤ χ.ker → Af.KillsMu N χ := by
  intro Ω _ _ _ l hl C _ χ r N hN hlN hχ B hB hI s hs
  haveI : NeZero N := ⟨hN⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by
    haveI : NeZero ((l ^ i : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (pow_ne_zero _ hl.out.ne_zero)⟩
    infer_instance
  have hcop : Nat.Coprime l N := (Nat.Prime.coprime_iff_not_dvd hl.out).2 hlN
  obtain ⟨σ, hσ, hc⟩ := GlobalTheory.T.cyclotomicChar_inertia_surjective Ω l B hB (cycZ ℚ Ω l s)
  have hker := (UpperTheory.V.Chr.clsFacts ℚ Ω N).2.2.2.2 B (valuation_not_lt_one_of_coprime B hcop hB) hσ
  have hone := (UpperTheory.V.Chr.clsFacts ℚ Ω N).2.2.2.2 B (valuation_not_lt_one_of_coprime B hcop hB) (Ine (F := ℚ) B).one_mem
  have hσN : ∀ ζ : Ω, ζ ^ N = 1 → σ ζ = ζ := by
    intro ζ hζ
    have h1 := UpperTheory.V.Chr.cls_spec (k := ℚ) N σ ζ hζ
    have h2 := UpperTheory.V.Chr.cls_spec (k := ℚ) N 1 ζ hζ
    rw [MonoidHom.mem_ker] at hker hone
    rw [hker] at h1
    rw [hone] at h2
    rw [h1, ← h2]
    rfl
  have hσl : ∀ ζ : Ω, ζ ^ l ^ r = 1 → s ζ = σ ζ := by
    intro ζ hζ
    have h1 : s ζ = ζ ^ ((cycZ ℚ Ω l s).val.toZModPow r).val :=
      cyclotomicCharacter.spec l s.toRingEquiv ζ hζ
    have h2 : σ ζ = ζ ^ ((cycZ ℚ Ω l σ).val.toZModPow r).val :=
      cyclotomicCharacter.spec l σ.toRingEquiv ζ hζ
    rw [h1, h2, hc]
  have h1 : χ (σ⁻¹ * s) = 1 := by
    refine hχ _ fun ζ hζ => ?_
    have h0 : ζ ≠ 0 := by
      rintro rfl
      rw [zero_pow (mul_ne_zero (pow_ne_zero _ hl.out.ne_zero) hN)] at hζ
      exact zero_ne_one hζ
    have e : s ζ = σ ζ := by
      refine eq_idempotent_mul_add_of_mul_sub_eq (Nat.Coprime.pow_left r hcop) ((map_ne_zero σ).2 h0) ?_ ?_
      · have hz : (ζ ^ l ^ r) ^ N = 1 := by rw [← pow_mul, hζ]
        rw [← map_pow, ← map_pow, hs _ hz, hσN _ hz]
      · have hz : (ζ ^ N) ^ l ^ r = 1 := by rw [← pow_mul, mul_comm, hζ]
        rw [← map_pow, ← map_pow, hσl _ hz]
    rw [AlgEquiv.mul_apply, e, ← AlgEquiv.mul_apply, inv_mul_cancel]
    rfl
  have h2 : χ σ = 1 := hI hσ
  rw [map_mul, map_inv, h2, inv_one, one_mul] at h1
  exact h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StCount
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem card_bot' {R N : Type} [Ring R] [AddCommGroup N] [Module R N] :
    Nat.card (⊥ : Submodule R N) = 1 := by
  exact Nat.card_unique

theorem UpperTheory.V.Fr.st_count :
    GlobalFiniteness → GreenbergWiles → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ρ : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M), ContainsAbove S l → ContAction ρ → ∀ μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) →* (ZMod (l ^ 1))ˣ, μ.comp (toGS Ω _) = cycMod ℚ Ω l 1 → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) → ∀ σ : G ℚ Ω, IsCC σ → (∀ m, ρ (toGS Ω _ σ) m = m → m = 0) → H0 (twDual μ ρ) = ⊥ → ∀ v₀ : S, (∀ v, v ≠ v₀ → H0 (ρ.comp (locFam S Av v)) = ⊥) → Nat.card (H0 (ρ.comp (locFam S Av v₀))) < Nat.card (H1 (ρ.comp (locFam S Av v₀))) → ∃ z ∈ Z1 ρ, z ∉ B1 ρ ∧ ∀ v, v ≠ v₀ → ∃ m, ∀ g ∈ Dec (F := ℚ) (Av v), z (toGS Ω _ g) = ρ (toGS Ω _ g) m - m := by
  intro hGF hGW Ω _ _ _ l _ hl2 M _ _ _ _ _ S ρ hS hρ μ hμ Av hAv σ hσ hfix hdual v₀ hloc hlt
  classical
  have hH0 : H0 ρ = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    change m ∈ ρ.invariants at hm
    exact (Submodule.mem_bot _).2 (hfix m ((Representation.mem_invariants ρ m).1 hm _))
  obtain ⟨L, hL⟩ : ∃ L : LocCond ρ (locFam S Av), ∀ v, L v = if v = v₀ then ⊤ else ⊥ :=
    ⟨fun v => if v = v₀ then ⊤ else ⊥, fun _ => rfl⟩
  have hcc : ∀ w : InfinitePlace ℚ, w.IsReal → IsCCAt w ((fun _ => σ) w) := by
    intro w _
    obtain ⟨j, hj⟩ := hσ
    exact ⟨j, hj, Subsingleton.elim _ _⟩
  have hgw := hGW ℚ Ω l 1 M S ρ one_pos hl2 hS hρ μ hμ Av hAv (fun _ => σ) hcc L
  obtain ⟨_, hfin1, _, _⟩ := hGF ℚ Ω l 1 M S ρ one_pos hS hρ
  have e1 : Nat.card (H0 (twDual μ ρ)) = 1 := by
    rw [hdual]
    exact card_bot'
  have e2 : ∏ v, Nat.card (H0 (ρ.comp (locFam S Av v))) = Nat.card (H0 (ρ.comp (locFam S Av v₀))) := by
    refine Finset.prod_eq_single v₀ (fun v _ hv => ?_) (fun h => absurd (Finset.mem_univ _) h)
    rw [hloc v hv]
    exact card_bot'
  have e3 : archH0Card S ρ (fun _ => σ) = 1 := by
    unfold archH0Card
    rw [InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ), pow_zero, mul_one]
    apply Finset.prod_eq_one
    intro w _
    exact Nat.card_eq_one_iff_unique.2
      ⟨⟨fun a b => Subtype.ext ((hfix _ a.2).trans (hfix _ b.2).symm)⟩, ⟨⟨0, map_zero _⟩⟩⟩
  have e4 : Nat.card (H0 ρ) = 1 := by
    rw [hH0]
    exact card_bot'
  have e5 : ∏ v, Nat.card (L v) = Nat.card (H1 (ρ.comp (locFam S Av v₀))) := by
    rw [Finset.prod_eq_single v₀ (fun v _ hv => by rw [hL, if_neg hv]; exact card_bot')
      (fun h => absurd (Finset.mem_univ _) h)]
    rw [hL, if_pos rfl]
    exact Nat.card_congr Submodule.topEquiv.toEquiv
  rw [e1, e2, e3, e4, e5] at hgw
  have hapos : 0 < Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) := Nat.card_pos
  have hcpos : 0 < Nat.card (H0 (ρ.comp (locFam S Av v₀))) := Nat.card_pos
  have key : ∀ a b c d : ℕ, a * 1 * c * 1 = b * 1 * d → c < d → 0 < a → 0 < c → 1 < a := by
    intro a b c d h hcd ha hc
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp at h
      omega
    · by_contra hle
      have ha1 : a = 1 := by omega
      subst ha1
      nlinarith
  have h2 := key _ _ _ _ hgw hlt hapos hcpos
  haveI := Finite.one_lt_card_iff_nontrivial.1 h2
  obtain ⟨x, hx⟩ := exists_ne (0 : Sel ρ (locFam S Av) (continuous_locFam S Av) L)
  obtain ⟨z', hz'⟩ := Submodule.Quotient.mk_surjective _ x.1
  refine ⟨z'.1, z'.2, ?_, ?_⟩
  · intro hz
    apply hx
    apply Subtype.ext
    rw [Submodule.coe_zero, ← hz']
    exact (Submodule.Quotient.mk_eq_zero _).2 hz
  · intro v hv
    have hm := (mem_Sel ρ (locFam S Av) (continuous_locFam S Av) L x.1).1 x.2 v
    rw [hL, if_neg hv, Submodule.mem_bot, ← hz'] at hm
    simp only [resH1, Submodule.mapQ_apply] at hm
    obtain ⟨m, hm'⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hm)
    exact ⟨m, fun g hg => hm' ⟨g, hg⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StDesc
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem sd_locConst {Γ A : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group A] (ψ : Γ →* A)
    (h : IsOpen (ψ.ker : Set Γ)) : IsLocallyConstant ψ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker ψ h

theorem UpperTheory.V.Fr.st_desc :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (S : Set (HeightOneSpectrum (𝓞 ℚ))) (C : Type) [Group C] (κ : G ℚ Ω →* C), IsOpen (κ.ker : Set (G ℚ Ω)) → (∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v → Ine (F := ℚ) A ≤ κ.ker) → ∃ κS : GS Ω S →* C, κS.comp (toGS Ω S) = κ ∧ IsLocallyConstant κS := by
  intro Ω _ _ _ S C _ κ ho hI
  have hN : NS Ω S ≤ κ.ker := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_)
      (Subgroup.isClosed_of_isOpen _ ho)
    intro s hs
    simp only [Set.mem_iUnion] at hs
    obtain ⟨v, hv, A, hA, hs⟩ := hs
    exact hI v hv A hA hs
  refine ⟨QuotientGroup.lift (NS Ω S) κ hN, MonoidHom.ext fun _ => rfl, fun T => ?_⟩
  rw [← (QuotientGroup.isQuotientMap_mk (NS Ω S)).isOpen_preimage]
  exact sd_locConst κ ho T
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StDual
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.st_dual :
    ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [Module (ZMod (l ^ 1)) k] (Γ : Type) [Group Γ] (μ : Γ →* (ZMod (l ^ 1))ˣ) (ρ : Representation (ZMod (l ^ 1)) Γ k) (g : Γ) (c : k), (∀ m, ρ g m = c * m) → c ≠ ZMod.castHom (dvd_pow_self l one_ne_zero) k (μ g) → H0 (twDual μ ρ) = ⊥ := by
  intro l _ k _ _ _ Γ _ μ ρ g c hc hne
  set a : k := ZMod.castHom (dvd_pow_self l one_ne_zero) k (μ g) with ha
  rw [eq_bot_iff]
  intro φ hφ
  rw [Submodule.mem_bot]
  have h : twDual μ ρ g φ = φ := hφ g
  have hne' : c - a ≠ 0 := sub_ne_zero.mpr hne
  have hsmul : ∀ m : k, a * m = ((μ g : ZMod (l ^ 1))) • m := by
    intro m
    rw [ha, ZMod.castHom_apply, ZMod.cast_eq_val, ← nsmul_eq_mul,
      ← Nat.cast_smul_eq_nsmul (ZMod (l ^ 1)), ZMod.natCast_zmod_val]
  have hinv : ∀ m : k, ρ g⁻¹ (ρ g m) = m := by
    intro m
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  let ψ : k →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1) := φ
  have key : ∀ m : k, ψ ((c - a) * m) = 0 := by
    intro m
    have h1 : (twDual μ ρ g φ) (ρ g m) = φ (ρ g m) := by rw [h]
    rw [twDual_apply, hinv, hc] at h1
    change (μ g : ZMod (l ^ 1)) * ψ m = ψ (c * m) at h1
    rw [sub_mul, map_sub, hsmul, map_smul, ← h1, smul_eq_mul, sub_self]
  apply LinearMap.ext
  intro x
  have hx : x = (c - a) * ((c - a)⁻¹ * x) := by
    rw [← mul_assoc, mul_inv_cancel₀ hne', one_mul]
  change ψ x = 0
  rw [hx, key]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StEta
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.st_eta :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (η : G ℚ Ω →* ℤˣ) (D : ℕ) (δ : Ω), 0 < D → δ ^ 2 = -(D : Ω) → (∀ s : G ℚ Ω, s δ = (η s : ℤ) • δ) → ∀ σ : G ℚ Ω, IsCC σ → η σ = -1 := by
  intro Ω _ _ _ η D δ hD hδ hs σ hσ
  obtain ⟨j, hj⟩ := hσ
  rcases Int.units_eq_one_or (η σ) with h | h
  · exfalso
    have h1 : σ δ = δ := by rw [hs σ, h]; simp
    have h2 : j δ = starRingEnd ℂ (j δ) := by
      have := hj δ
      rw [← this]
      exact congrArg j h1.symm
    have h3 : (j δ) ^ 2 = -(D : ℂ) := by
      rw [← map_pow, hδ]; simp
    have him : (j δ).im = 0 := Complex.conj_eq_iff_im.mp h2.symm
    have h4 := congrArg Complex.re h3
    simp [sq, him] at h4
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    nlinarith [mul_self_nonneg (j δ).re]
  · exact h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StMu
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.st_mu :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (M a : ℕ), M ≠ 0 → ∀ (C : Type) [Group C] (χ : G ℚ Ω →* C), Af.KillsMu (M ^ a) χ → IsOpen (χ.ker : Set (G ℚ Ω)) ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → Ine (F := ℚ) A ≤ χ.ker := by
  intro Ω _ _ _ M a hM C _ χ hk
  haveI : NeZero (M ^ a) := ⟨pow_ne_zero _ hM⟩
  obtain ⟨hopen, -, -, -, hine⟩ := UpperTheory.V.Chr.clsFacts ℚ Ω (M ^ a)
  have hle : (UpperTheory.V.Chr.cls ℚ Ω (M ^ a)).ker ≤ χ.ker := by
    intro s hs
    rw [MonoidHom.mem_ker] at hs ⊢
    apply hk s
    intro ζ hζ
    rw [UpperTheory.V.Chr.cls_spec (M ^ a) s ζ hζ, hs, Units.val_one, ZMod.val_one_eq_one_mod,
      ← pow_eq_pow_mod 1 hζ, pow_one]
  refine ⟨Subgroup.isOpen_mono hle hopen, ?_⟩
  intro A hA
  refine le_trans (hine A ?_) hle
  rw [Nat.cast_pow, map_pow, not_lt]
  exact one_le_pow₀ (not_lt.mp hA)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StRes
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.st_res :
    ∀ (Γ k : Type) [Group Γ] [Field k] (κ : Γ →* kˣ) (U : Subgroup Γ), commutator Γ ≤ U → (∃ u ∈ U, κ u ≠ 1) → ∀ y : Γ → k, (∀ s t, y (s * t) = y s + κ s * y t) → (∃ b, ∀ s ∈ U, y s = κ s * b - b) → ∃ b, ∀ s, y s = κ s * b - b := by
  intro Γ k _ _ κ U hU hu y hy hb
  obtain ⟨u, huU, hu1⟩ := hu
  obtain ⟨b, hb⟩ := hb
  refine ⟨b, fun s => ?_⟩
  have hc : s * u * s⁻¹ * u⁻¹ ∈ U := by
    apply hU
    have := Subgroup.commutator_mem_commutator (Subgroup.mem_top s) (Subgroup.mem_top u)
    rw [commutatorElement_def] at this
    exact this
  have hv : s * u * s⁻¹ ∈ U := by
    have := U.mul_mem hc huU
    simpa using this
  have hκ : κ (s * u * s⁻¹) = κ u := by
    rw [map_mul, map_mul, map_inv, mul_comm (κ s) (κ u), mul_inv_cancel_right]
  have h1 := hy s u
  have h2 := hy (s * u * s⁻¹) s
  rw [inv_mul_cancel_right, hb _ hv, hκ] at h2
  rw [hb u huU] at h1
  have hne : ((κ u : k) - 1) ≠ 0 := by
    intro h
    apply hu1
    ext
    simpa using sub_eq_zero.mp h
  apply mul_left_cancel₀ hne
  linear_combination h1 - h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StTame
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem exists_char_of_index {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (l : ℕ) [Fact l.Prime] (H : Subgroup Γ) (ho : IsOpen (H : Set Γ)) (hc : commutator Γ ≤ H)
    (hi : H.index = l) :
    ∃ φ : Γ → ZMod l, IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ a, φ a = 0 ↔ a ∈ H := by
  have hN : H.Normal := by
    refine ⟨fun a ha g => ?_⟩
    have hc' : g * a * g⁻¹ * a⁻¹ ∈ H :=
      hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top a))
    have h2 := H.mul_mem hc' ha
    simpa using h2
  have hQ : Nat.card (Γ ⧸ H) = l := hi
  have hM : Nat.card (Multiplicative (ZMod l)) = l := by
    rw [Nat.card_eq_fintype_card]
    simp
  haveI : IsCyclic (Γ ⧸ H) := isCyclic_of_prime_card hQ
  haveI : IsCyclic (Multiplicative (ZMod l)) := isCyclic_of_prime_card hM
  let e : (Γ ⧸ H) ≃* Multiplicative (ZMod l) := mulEquivOfCyclicCardEq (hQ.trans hM.symm)
  let f : Γ →* Multiplicative (ZMod l) := (e : (Γ ⧸ H) →* Multiplicative (ZMod l)).comp (QuotientGroup.mk' H)
  have hadd : ∀ a b, Multiplicative.toAdd (f (a * b)) = Multiplicative.toAdd (f a) + Multiplicative.toAdd (f b) := by
    intro a b
    rw [map_mul, toAdd_mul]
  have hker : ∀ a, Multiplicative.toAdd (f a) = 0 ↔ a ∈ H := by
    intro a
    have h1 : Multiplicative.toAdd (f a) = 0 ↔ f a = 1 := by
      constructor
      · intro h
        exact Multiplicative.toAdd.injective (by simpa using h)
      · intro h
        rw [h]
        rfl
    rw [h1]
    simp only [f, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply, MonoidHom.coe_coe,
      MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  refine ⟨fun a => Multiplicative.toAdd (f a), ?_, hadd, hker⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun h => x * h) '' (H : Set Γ), isOpenMap_mul_left x _ ho, ⟨1, H.one_mem, mul_one x⟩, ?_⟩
  rintro _ ⟨h, hh, rfl⟩
  show Multiplicative.toAdd (f (x * h)) = Multiplicative.toAdd (f x)
  rw [hadd, (hker h).2 hh, add_zero]

theorem UpperTheory.V.Fr.st_tame :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (A : ValuationSubring Ω), ¬ A.valuation (l : Ω) < 1 → ∀ H : Subgroup (G ℚ Ω), IsOpen (H : Set (G ℚ Ω)) → commutator (G ℚ Ω) ≤ H → H.index = l → ¬ Ine (F := ℚ) A ≤ H → ∀ y : G ℚ Ω → k, IsLocallyConstant y → (∀ s ∈ Ine (F := ℚ) A, ∀ t ∈ Ine (F := ℚ) A, y (s * t) = y s + y t) → ∀ s ∈ Ine (F := ℚ) A ⊓ H, y s = 0 := by
  intro Ω _ _ _ l _ k _ _ A hA H ho hc hi hIH y hy hyadd s hs
  obtain ⟨φ, hφc, hφa, hφk⟩ := exists_char_of_index l H ho hc hi
  obtain ⟨γ, hγ⟩ := UpperTheory.V.Two.tameGen ℚ Ω l A hA
  let φI : ↥(Ine (F := ℚ) A) → ZMod l := fun σ => φ σ
  have hφIc : IsLocallyConstant φI := hφc.comp_continuous continuous_subtype_val
  have hφIa : ∀ a b : ↥(Ine (F := ℚ) A), φI (a * b) = φI a + φI b := fun a b => hφa _ _
  have hγne : φI γ ≠ 0 := by
    intro h0
    apply hIH
    intro σ hσ
    exact (hφk σ).1 (hγ φI hφIc hφIa h0 ⟨σ, hσ⟩)
  letI : Algebra (ZMod l) k := ZMod.algebra k l
  rw [← Module.forall_dual_apply_eq_zero_iff (ZMod l)]
  intro μ
  let c : ZMod l := μ (y γ) / φI γ
  let ψ : ↥(Ine (F := ℚ) A) → ZMod l := fun σ => μ (y σ) - c * φI σ
  have hyI : IsLocallyConstant (fun σ : ↥(Ine (F := ℚ) A) => y σ) := hy.comp_continuous continuous_subtype_val
  have hψc : IsLocallyConstant ψ := IsLocallyConstant.comp₂ hyI hφIc (fun u v => μ u - c * v)
  have hψa : ∀ a b : ↥(Ine (F := ℚ) A), ψ (a * b) = ψ a + ψ b := by
    intro a b
    simp only [ψ]
    rw [hφIa, Subgroup.coe_mul, hyadd _ a.2 _ b.2, map_add (f := _)]
    ring
  have hψγ : ψ γ = 0 := by
    simp only [ψ, c]
    rw [div_mul_cancel₀ _ hγne, sub_self]
  have h := hγ ψ hψc hψa hψγ ⟨s, hs.1⟩
  have h0 : φI ⟨s, hs.1⟩ = 0 := (hφk s).2 hs.2
  simp only [ψ] at h
  rw [h0, mul_zero, sub_zero] at h
  exact h
end

