module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ReflMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FinChar
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem exists_valuationSubring_isPlaceOver (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (v : HeightOneSpectrum (𝓞 K)) : ∃ A : ValuationSubring Ω, IsPlaceOver A v := by
  let f : 𝓞 K →+* Ω := (algebraMap K Ω).comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f :=
    (algebraMap K Ω).injective.comp (IsFractionRing.injective (𝓞 K) K)
  let e : 𝓞 K ≃+* f.range := RingEquiv.ofBijective f.rangeRestrict
    ⟨fun x y h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  let I : Ideal f.range := v.asIdeal.map e
  have hI : I ≠ ⊤ := by
    haveI : (v.asIdeal.map e).IsPrime := Ideal.map_isPrime_of_equiv e
    exact Ideal.IsPrime.ne_top this
  obtain ⟨V, hRV, hV⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have hlt : ∀ y ∈ v.asIdeal, V.valuation (f y) < 1 := by
    intro y hy
    have h1 : f y ∈ V.nonunits := hV ⟨e y, Ideal.mem_map_of_mem e hy, rfl⟩
    exact (ValuationSubring.mem_nonunits_iff V).1 h1
  have hle : ∀ y : 𝓞 K, V.valuation (f y) ≤ 1 := by
    intro y
    exact (ValuationSubring.valuation_le_one_iff V _).2 (hRV (RingHom.mem_range_self f y))
  refine ⟨V, fun x => ⟨fun hx => ?_, fun hx => hlt x hx⟩⟩
  by_contra hxv
  obtain ⟨r, y, hy, hry⟩ := v.isMaximal.exists_inv hxv
  have h2 : V.valuation (f (r * x)) < 1 := by
    rw [map_mul, Valuation.map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle r)) hx
  have h3 : V.valuation (f (r * x + y)) < 1 := by
    rw [map_add (f := _)]
    exact Valuation.map_add_lt _ h2 (hlt y hy)
  rw [hry, map_one, Valuation.map_one] at h3
  exact lt_irrefl _ h3

private theorem finite_above_of_ne_zero (K : Type) [Field K] [NumberField K] (N : ℕ) (hN : N ≠ 0) :
    (Above K N).Finite := by
  have h0 : Ideal.span {((N : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine (Ideal.finite_factors h0).subset ?_
  intro v hv
  exact Ideal.dvd_span_singleton.2 hv

theorem UpperTheory.V.Kum.finChar :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (n N : ℕ) (ζ : K), n ≠ 0 → N ≠ 0 → IsPrimitiveRoot ζ n → {φ : G K Ω → ZMod n | IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → ∀ g ∈ Ine (F := K) A, φ g = 0}.Finite := by
  intro K Ω _ _ _ _ _ n N ζ hn hN hζ
  haveI : NeZero n := ⟨hn⟩
  let ζΩ := algebraMap K Ω ζ
  have hζΩ : IsPrimitiveRoot ζΩ n := hζ.map_of_injective (algebraMap K Ω).injective
  have hfix : ∀ (g : G K Ω) (x : K), g (algebraMap K Ω x) = algebraMap K Ω x :=
    fun g x => AlgEquiv.commutes g x
  have hη : ∀ g : G K Ω, g ζΩ = ζΩ ^ ((fun _ => (1 : ZMod n)) g).val := by
    intro g
    rw [hfix g ζ]
    rcases Nat.lt_or_ge 1 n with h1 | h1
    · rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt h1, pow_one]
    · have hn1 : n = 1 := by omega
      subst hn1
      have : ζΩ = 1 := IsPrimitiveRoot.one_right_iff.1 hζΩ
      show ζΩ = ζΩ ^ _
      rw [this, one_pow]
  have key : ∀ φ ∈ {φ : G K Ω → ZMod n | IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧
      ∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → ∀ g ∈ Ine (F := K) A, φ g = 0},
      ∃ β : Ω, ∃ a : Kˣ, a ∈ SelK (Above K N) n ∧ β ^ n = algebraMap K Ω a ∧
        ∀ g : G K Ω, g β = ζΩ ^ (φ g).val * β := by
    rintro φ ⟨hlc, hadd, hine⟩
    obtain ⟨β, a, hβ, hg⟩ := radExists K Ω n ζΩ (fun _ => 1) φ hζΩ hη hlc
      (fun g h => by rw [hadd, one_mul])
    refine ⟨β, a, ?_, hβ, hg⟩
    intro v hv
    obtain ⟨A, hA⟩ := exists_valuationSubring_isPlaceOver K Ω v
    have hnot : ¬ A.valuation (N : Ω) < 1 := fun h => hv (((placeDict K Ω).2.2.2 A v N hA).1 h)
    exact dvdOfIne K Ω n A v β a hA hβ
      (fun g hg' => by rw [hg, hine A hnot g hg', ZMod.val_zero, pow_zero, one_mul])
  choose! β a ha hβ hg using key
  haveI hQ : Finite (↥(SelK (Above K N) n) ⧸ (powK K n).subgroupOf (SelK (Above K N) n)) := by
    apply Nat.finite_of_card_ne_zero
    rw [cardSel K _ n hn, cardSUnit K _ n (finite_above_of_ne_zero K N hN)]
    have h1 : Nat.card ↥(rootsOfUnity n K) ≠ 0 := Nat.card_pos.ne'
    have h2 : Nat.card {c : ClS (Above K N) // c ^ n = 1} ≠ 0 := by
      haveI : Nonempty {c : ClS (Above K N) // c ^ n = 1} := ⟨⟨1, one_pow _⟩⟩
      exact Nat.card_pos.ne'
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hn) h1) h2
  rw [← Set.finite_coe_iff]
  refine Finite.of_injective (β := ↥(SelK (Above K N) n) ⧸ (powK K n).subgroupOf (SelK (Above K N) n))
    (fun φ => QuotientGroup.mk ⟨a φ.1, ha φ.1 φ.2⟩) ?_
  rintro ⟨φ, hφ⟩ ⟨ψ, hψ⟩ h
  simp only at h
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  obtain ⟨c, hc⟩ := h
  simp only [powMonoidHom_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hc
  have hcu : a φ * c ^ n = a ψ := by rw [hc, mul_inv_cancel_left]
  have hne : ∀ θ ∈ _, β θ ≠ 0 := fun θ hθ h0 => by
    have := hβ θ hθ
    rw [h0, zero_pow hn] at this
    exact (Units.ne_zero (a θ)) ((algebraMap K Ω).injective (this.symm.trans (map_zero _).symm))
  refine Subtype.ext (funext fun g => ?_)
  have hφ0 := hne φ hφ
  have hcΩ : algebraMap K Ω (c : K) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact c.ne_zero
  set ω := β ψ / (β φ * algebraMap K Ω (c : K)) with hωdef
  have hωn : ω ^ n = 1 := by
    rw [hωdef, div_pow, mul_pow, hβ ψ hψ, hβ φ hφ, ← map_pow, ← map_mul, ← hcu]
    push_cast
    exact div_self (by simp)
  obtain ⟨i, -, hi⟩ := hζΩ.eq_pow_of_pow_eq_one hωn
  have hψeq : β ψ = ω * (β φ * algebraMap K Ω (c : K)) := by
    rw [hωdef, div_mul_cancel₀ _ (mul_ne_zero hφ0 hcΩ)]
  have hgω : g ω = ω := by
    rw [← hi, map_pow]
    exact congrArg (· ^ i) (hfix g ζ)
  have hω0 : ω ≠ 0 := by
    rw [← hi]
    exact pow_ne_zero _ (hζΩ.ne_zero hn)
  have e1 := hg ψ hψ g
  rw [hψeq, map_mul, map_mul, hgω, hg φ hφ g, hfix] at e1
  have e2 : ζΩ ^ (φ g).val = ζΩ ^ (ψ g).val := by
    have h3 := mul_ne_zero hω0 (mul_ne_zero hφ0 hcΩ)
    apply mul_right_cancel₀ h3
    linear_combination e1
  exact ZMod.val_injective _ (hζΩ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e2)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Reflect
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem reflect_card {A B S T : Type} [AddCommGroup A] [AddCommGroup B] [Finite S] [Finite T] (f : A →+ B)
    (i : f.ker → S) (hi : Function.Injective i) (j : f.range → T) (hj : Function.Injective j) :
    Nat.card A ≤ Nat.card S * Nat.card T := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv, mul_comm]
  exact Nat.mul_le_mul (Nat.card_le_card_of_injective i hi) (Nat.card_le_card_of_injective j hj)

private theorem reflect_conj {K : Type} [Field K] [NumberField K] [IsCMField K] {n : ℕ} (hn : n ≠ 0) {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) : cE K ζ = ζ⁻¹ := by
  obtain ⟨j⟩ : Nonempty (K →+* ℂ) := inferInstance
  apply j.injective
  have h1 : ‖j ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζ.pow_eq_one, map_one]) hn
  have h2 : j (cE K ζ) = starRingEnd ℂ (j ζ) := IsCMField.complexEmbedding_complexConj K j ζ
  rw [h2, map_inv₀]
  apply eq_inv_of_mul_eq_one_left
  rw [Complex.conj_mul', h1]
  simp

private theorem reflect_tors {K : Type} [Field K] [NumberField K] [IsCMField K] {n : ℕ} (hn : Odd n) (a : Kˣ)
    (ha : a ∈ SelK (∅ : Set (HeightOneSpectrum (𝓞 K))) n) (h1 : radCl n a = 1)
    (hc : a * Units.map (cE K).toMonoidHom a ∈ powK K n) :
    ∃ t b : Kˣ, IsOfFinOrder t ∧ a = t * b ^ n := by
  have hn0 : n ≠ 0 := hn.pos.ne'
  have h2 := (UpperTheory.V.Kum.radClKer K ∅ n hn0 a ha).1 (h1 ▸ one_mem _)
  obtain ⟨u, hu, p, ⟨b, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 h2
  have hb : powMonoidHom n b * Units.map (cE K).toMonoidHom (powMonoidHom n b) ∈ powK K n :=
    ⟨b * Units.map (cE K).toMonoidHom b, by simp only [powMonoidHom_apply, mul_pow, map_pow]⟩
  have hu' : u * Units.map (cE K).toMonoidHom u ∈ powK K n := by
    rw [map_mul, mul_mul_mul_comm] at hc
    exact (Subgroup.mul_mem_cancel_right _ hb).1 hc
  obtain ⟨t, ht, q, ⟨d, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 ((UpperTheory.V.Kum.unitMinus K n u hu hu').2 hn)
  exact ⟨t, d * b, ht, by simp only [powMonoidHom_apply, mul_pow, mul_assoc]⟩

theorem UpperTheory.V.Kum.reflect :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (n : ℕ) [NeZero n] (N : ℕ) (ζ : K) [Normal F K] [IsCMField K] (χ ψ : G F Ω →* (ZMod n)ˣ) (σ : Ω ≃+* Ω), U = galOf F K Ω → Odd n → IsPrimitiveRoot ζ n → (∀ g : G F Ω, g (algebraMap K Ω ζ) = (algebraMap K Ω ζ) ^ (χ g : ZMod n).val) → IsConjOm σ →
    Nat.card (EqEig N U (scalRep (ZMod n) ψ) σ 1) ≤ Nat.card (scalRep (ZMod n) ψ).invariants * Nat.card (ClTw K n (χ * ψ⁻¹) ⊓ ClMinus (cE K) : Subgroup (ClassGroup (𝓞 K))) := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ U n _ N ζ _ _ χ ψ σ hU hn hζ hχ hσ
  have hn0 : n ≠ 0 := NeZero.ne n
  obtain ⟨κ, hκ, -⟩ := UpperTheory.V.Kum.reflMap F Ω K U n N ζ hU hζ
  obtain ⟨hR, hfin⟩ := UpperTheory.V.Kum.reflRoot F Ω K U n N ζ ψ hU hζ
  have hX := (UpperTheory.V.Kum.radXDual F Ω K U n N ζ hU hζ).1
  have hle : EqEig N U (scalRep (ZMod n) ψ) σ 1 ≤ XDual N U (ZMod n) (ZMod n) := fun φ h => h.1.1
  let f : EqEig N U (scalRep (ZMod n) ψ) σ 1 →+ Additive (ClassGroup (𝓞 K)) :=
    κ.comp (Submodule.inclusion hle).toAddMonoidHom
  have key : ∀ φ : EqEig N U (scalRep (ZMod n) ψ) σ 1, ∃ (β : Ω) (a : Kˣ), IsRad (algebraMap K Ω ζ) U φ.1 β ∧
      β ^ n = algebraMap K Ω a ∧ a ∈ SelK (∅ : Set (HeightOneSpectrum (𝓞 K))) n ∧ f φ = Additive.ofMul (radCl n a) ∧
      a * Units.map (cE K).toMonoidHom a ∈ powK K n ∧ radCl n a ∈ ClTw K n (χ * ψ⁻¹) ⊓ ClMinus (cE K) := by
    intro φ
    obtain ⟨β, a, h1, h2, h3⟩ := hX φ.1 (hle φ.2)
    obtain ⟨h4, h5⟩ := UpperTheory.V.Kum.reflTw F Ω K U n N ζ χ ψ φ.1 β a hU hζ hχ φ.2.1 h1 h2
    obtain ⟨h6, h7⟩ := h5 (cE K) σ hσ.isLift (reflect_conj hn0 hζ) φ.2.2
    exact ⟨β, a, h1, h2, h3, hκ ⟨φ.1, hle φ.2⟩ β a h1 h2, h6, h4, h7⟩
  have hker : ∀ φ : f.ker, ∃ (β : Ω) (a : Kˣ), IsRad (algebraMap K Ω ζ) U φ.1.1 β ∧ β ^ n = algebraMap K Ω a ∧
      IsOfFinOrder β := by
    intro φ
    obtain ⟨β, a, h1, h2, h3, h4, h5, -⟩ := key φ.1
    have h0 : radCl n a = 1 := Additive.ofMul.injective (h4.symm.trans φ.2)
    obtain ⟨t, b, ht, rfl⟩ := reflect_tors hn a h3 h0 h5
    have hb : algebraMap K Ω b ≠ 0 := (map_ne_zero _).2 b.ne_zero
    have hp : (β / algebraMap K Ω b) ^ n = algebraMap K Ω t := by
      rw [div_pow, h2, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, mul_div_cancel_right₀ _ (pow_ne_zero _ hb)]
    refine ⟨β / algebraMap K Ω b, t, ⟨div_ne_zero h1.1 hb, fun u => ?_⟩, hp, ?_⟩
    · have hu : u.1 ∈ galOf F K Ω := hU ▸ u.2
      rw [map_div₀, h1.2 u, hu (b : K), mul_div_assoc]
    · refine IsOfFinOrder.of_pow ?_ hn0
      rw [hp]
      exact ((algebraMap K Ω).toMonoidHom.comp (Units.coeHom K)).isOfFinOrder ht
  have hran : ∀ c : f.range, Additive.toMul c.1 ∈ ClTw K n (χ * ψ⁻¹) ⊓ ClMinus (cE K) := by
    rintro ⟨c, φ, rfl⟩
    obtain ⟨β, a, -, -, -, h4, -, h6⟩ := key φ
    show Additive.toMul (f φ) ∈ _
    rw [h4]
    exact h6
  refine le_trans (reflect_card f (fun φ => (⟨φ.1.1, φ.1.2.1, hker φ⟩ : {φ : U → ZMod n // φ ∈ EqHom N U (scalRep (ZMod n) ψ) ∧ ∃ (β : Ω) (a : Kˣ), IsRad (algebraMap K Ω ζ) U φ β ∧ β ^ n = algebraMap K Ω a ∧ IsOfFinOrder β})) ?_
    (fun c => (⟨Additive.toMul c.1, hran c⟩ : (ClTw K n (χ * ψ⁻¹) ⊓ ClMinus (cE K) : Subgroup (ClassGroup (𝓞 K))))) ?_)
    (Nat.mul_le_mul_right _ hR)
  · intro x y h
    exact Subtype.ext (Subtype.ext (Subtype.mk.inj h))
  · intro x y h
    exact Subtype.ext (Additive.toMul.injective (Subtype.mk.inj h))
end

