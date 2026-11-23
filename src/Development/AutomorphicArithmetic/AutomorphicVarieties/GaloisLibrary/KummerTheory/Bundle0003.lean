module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem val_top {Ω : Type} [Field Ω] {x : Ω} (h : (⊤ : ValuationSubring Ω).valuation x < 1) : x = 0 := by
  by_contra hx
  have h1 : (⊤ : ValuationSubring Ω).valuation x⁻¹ ≤ 1 :=
    (ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _)
  have h2 := mul_lt_one_of_nonneg_of_lt_one_left zero_le h h1
  rw [← map_mul, mul_inv_cancel₀ hx, map_one] at h2
  exact lt_irrefl _ h2

private theorem int_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {b : Ω} (hb : IsIntegral ℤ b) :
    A.valuation b ≤ 1 := by
  have h : IsIntegral A b := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [A.valuation_le_one_iff, ← hy]
  exact y.2

private theorem exists_place (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (A : ValuationSubring Ω) (hA : A ≠ ⊤) : ∃ v : HeightOneSpectrum (𝓞 K),
      ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ v.asIdeal := by
  have hm : ∀ x : 𝓞 K, algebraMap K Ω (x : K) ∈ A := fun x =>
    (A.valuation_le_one_iff _).1 (int_le A (x.isIntegral_coe.map (algebraMap K Ω).toIntAlgHom))
  let f : 𝓞 K →+* A := ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)).codRestrict A hm
  let P : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  refine ⟨⟨P, inferInstance, fun h0 => hA ?_⟩, hP⟩
  rw [eq_top_iff]
  intro x _
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have h1 : Algebra.IsAlgebraic ℤ K := (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := K)).2 inferInstance
  have h2 : Algebra.IsAlgebraic ℤ Ω := Algebra.IsAlgebraic.trans ℤ K Ω
  obtain ⟨n, hn, hi⟩ := (h2.isAlgebraic x).exists_integral_multiple
  have h3 : ¬ A.valuation (algebraMap K Ω ((n : 𝓞 K) : K)) < 1 := by
    rw [hP, h0, Ideal.mem_bot]
    exact Int.cast_ne_zero.2 hn
  have h4 : A.valuation (n : Ω) = 1 :=
    le_antisymm (int_le A (isIntegral_algebraMap (R := ℤ) (x := n))) (by simpa using h3)
  have h5 := int_le A hi
  rw [zsmul_eq_mul, map_mul, h4, one_mul] at h5
  exact (A.valuation_le_one_iff x).1 h5

theorem UpperTheory.V.Kum.placeDict :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω], Ine (F := K) (⊤ : ValuationSubring Ω) = ⊥ ∧ (∀ A : ValuationSubring Ω, A ≠ ⊤ → ∃ v : HeightOneSpectrum (𝓞 K), IsPlaceOver A v) ∧
    (∀ (A : ValuationSubring Ω) (N : ℕ), N ≠ 0 → A.valuation (N : Ω) < 1 → A ≠ ⊤) ∧
    ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (N : ℕ), IsPlaceOver A v →
      (A.valuation (N : Ω) < 1 ↔ v ∈ Formalism.GaloisCohomology.Above (F := K) N) := by
  intro K Ω _ _ _ _ _
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    ext x
    have h := hg.2 x ((ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _))
    exact sub_eq_zero.1 (val_top h)
  · intro A hA
    exact exists_place K Ω A hA
  · rintro A N hN h rfl
    exact hN (Nat.cast_eq_zero.1 (val_top h))
  · intro A v N hv
    have h := hv (N : 𝓞 K)
    have e : algebraMap K Ω ((N : 𝓞 K) : K) = (N : Ω) := by simp
    rw [← e]
    exact h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.QzBasic
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem qzB_smul_mk (l : ℕ) [Fact l.Prime] (x : ℤ_[l]) (q : ℚ_[l]) :
    x • QZ.mk l q = QZ.mk l ((x : ℚ_[l]) * q) := rfl

private theorem qzB_mk_eq_zero (l : ℕ) [Fact l.Prime] (q : ℚ_[l]) :
    QZ.mk l q = 0 ↔ ∃ z : ℤ_[l], (z : ℚ_[l]) = q :=
  Submodule.Quotient.mk_eq_zero (ZlSub l)

private theorem qzB_mk_surj (l : ℕ) [Fact l.Prime] (a : QZ l) : ∃ q, QZ.mk l q = a :=
  Submodule.Quotient.mk_surjective (ZlSub l) a

theorem UpperTheory.V.Kum.qzBasic :
    ∀ (l : ℕ) [Fact l.Prime], (∀ u : ℤ_[l], u ≠ 0 → Function.Surjective fun x : QZ l => u • x) ∧ (∀ x : QZ l, ∃ k : ℕ, l ^ k • x = 0) ∧ (l ≠ 2 → ∀ x : QZ l, 2 • x = 0 → x = 0) := by
  intro l _
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have tors : ∀ x : QZ l, ∃ k : ℕ, l ^ k • x = 0 := by
    intro x
    obtain ⟨q, rfl⟩ := qzB_mk_surj l x
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖q‖ hl1
    refine ⟨k, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l], qzB_smul_mk, qzB_mk_eq_zero]
    have hpos : (0 : ℝ) < (l : ℝ) ^ k := pow_pos (by linarith) k
    refine ⟨⟨_, ?_⟩, rfl⟩
    rw [PadicInt.mem_subring_iff]
    push_cast
    rw [norm_mul, Padic.norm_p_pow, zpow_neg, zpow_natCast, inv_mul_le_iff₀ hpos, mul_one]
    exact hk.le
  refine ⟨?_, tors, ?_⟩
  · intro u hu a
    obtain ⟨q, rfl⟩ := qzB_mk_surj l a
    have hu' : (u : ℚ_[l]) ≠ 0 := PadicInt.coe_ne_zero.2 hu
    refine ⟨QZ.mk l (q / u), ?_⟩
    show u • QZ.mk l (q / u) = QZ.mk l q
    rw [qzB_smul_mk, mul_div_cancel₀ q hu']
  · intro h2 x hx
    obtain ⟨k, hk⟩ := tors x
    have hc : IsCoprime (2 : ℤ) ((l ^ k : ℕ) : ℤ) := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, Nat.isCoprime_iff_coprime]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hl).2 (Ne.symm h2))
    obtain ⟨a, b, hab⟩ := hc
    calc x = (1 : ℤ) • x := (one_smul ℤ x).symm
      _ = (a * 2 + b * ((l ^ k : ℕ) : ℤ)) • x := by rw [hab]
      _ = a • ((2 : ℕ) • x) + b • ((l ^ k) • x) := by
        rw [add_smul, mul_smul, mul_smul]
        norm_cast
      _ = 0 := by rw [hx, hk, smul_zero, smul_zero, add_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ReflRoot
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem exp_tors (K : Type) [Field K] [NumberField K] :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ a : K, IsOfFinOrder a → a ^ m = 1 := by
  refine ⟨Units.torsionOrder K, Units.torsionOrder_ne_zero K, fun a ha => ?_⟩
  obtain ⟨k, hk, hak⟩ := isOfFinOrder_iff_pow_eq_one.1 ha
  have hi : IsIntegral ℤ a := IsIntegral.of_pow hk (by rw [hak]; exact isIntegral_one)
  let x : 𝓞 K := ⟨a, hi⟩
  have hx : x ^ k = 1 := by
    apply RingOfIntegers.coe_injective
    rw [map_pow, map_one]
    exact hak
  let y : (𝓞 K)ˣ := Units.ofPowEqOne x k hx hk.ne'
  have hy : y ∈ Units.torsion K :=
    (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, Units.ext (by simpa [y] using hx)⟩)
  rw [← Units.rootsOfUnity_eq_torsion, mem_rootsOfUnity] at hy
  have h2 := congrArg (fun z : (𝓞 K)ˣ => algebraMap (𝓞 K) K z) hy
  simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at h2
  exact h2

private theorem conj_root {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (g u : Ω ≃ₐ[F] Ω) (β : Ω)
    (hβ : IsOfFinOrder β) : g (u (g.symm β)) = u β := by
  have hp := IsPrimitiveRoot.orderOf β
  haveI : NeZero (orderOf β) := ⟨hβ.orderOf_pos.ne'⟩
  have key : ∀ s : Ω ≃ₐ[F] Ω, ∃ i : ℕ, β ^ i = s β := fun s => by
    obtain ⟨i, -, hi⟩ := hp.eq_pow_of_pow_eq_one (ξ := s β) (by rw [← map_pow, pow_orderOf_eq_one, map_one])
    exact ⟨i, hi⟩
  obtain ⟨i, hi⟩ := key g.symm
  obtain ⟨j, hj⟩ := key u
  rw [← hi, map_pow, ← hj, ← pow_mul, mul_comm, pow_mul, hi, map_pow, g.apply_symm_apply]

private theorem exists_gen (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (n : ℕ) [NeZero n] :
    ∃ (ξ : Ωˣ) (b : K), (ξ : Ω) ^ n = algebraMap K Ω b ∧
      ∀ (β : Ω) (a : Kˣ), β ^ n = algebraMap K Ω a → IsOfFinOrder β → ∃ j : ℤ, (ξ : Ω) ^ j = β := by
  obtain ⟨m, hm, hK⟩ := exp_tors K
  haveI : NeZero (n * m) := ⟨mul_ne_zero (NeZero.ne n) hm⟩
  let T : Subgroup Ωˣ := rootsOfUnity (n * m) Ω ⊓
    ((Units.map (algebraMap K Ω).toMonoidHom).range).comap (powMonoidHom n)
  haveI : Finite T := Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left : T ≤ _))
  obtain ⟨⟨ξ, hξ⟩, hg⟩ := (isCyclic_subgroup_units T).exists_generator
  obtain ⟨b, hb⟩ := hξ.2
  refine ⟨ξ, b, ?_, fun β a h hβ => ?_⟩
  · have := congrArg Units.val hb
    simpa using this.symm
  · have h0 : β ≠ 0 := by
      rintro rfl
      rw [zero_pow (NeZero.ne n)] at h
      exact a.ne_zero ((map_eq_zero _).1 h.symm)
    have ha : IsOfFinOrder (a : K) := by
      have := hβ.pow (n := n)
      rw [h] at this
      obtain ⟨k, hk, hak⟩ := isOfFinOrder_iff_pow_eq_one.1 this
      exact isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, (algebraMap K Ω).injective (by rw [map_pow, hak, map_one])⟩
    have hT : Units.mk0 β h0 ∈ T := by
      refine ⟨(mem_rootsOfUnity _ _).2 (Units.ext ?_), a, Units.ext (by simpa using h.symm)⟩
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      rw [pow_mul, h, ← map_pow, hK a ha, map_one]
    obtain ⟨j, hj⟩ := hg ⟨_, hT⟩
    refine ⟨j, ?_⟩
    have := congrArg (fun z : T => ((z : Ωˣ) : Ω)) hj
    simpa using this

private theorem exists_generator_kummer_cocycle {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (U : Subgroup (Ω ≃ₐ[F] Ω)) (n : ℕ) [NeZero n]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ n) (hU : ∀ u : U, u.1 ζ = ζ) (ξ : Ωˣ) (hξ : ∀ u : U, u.1 (ξ ^ n) = ξ ^ n) :
    ∃ u0 : U, ∀ u : U, ∃ k : ℤ, u.1 ξ / ξ = (u0.1 ξ / ξ) ^ k := by
  have h1 : ∀ u : U, (u.1 ξ / ξ) ^ n = 1 := fun u => by
    rw [div_pow, ← map_pow, hξ, div_self (pow_ne_zero _ ξ.ne_zero)]
  have h2 : ∀ u v : U, u.1 (v.1 ξ / ξ) = v.1 ξ / ξ := fun u v => by
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (h1 v)
    rw [← hi, map_pow, hU]
  have h3 : ∀ u : U, u.1 ξ ≠ 0 := fun u => (map_ne_zero _).2 ξ.ne_zero
  let f : U →* Ωˣ := MonoidHom.mk' (fun u => Units.mk0 (u.1 ξ / ξ) (div_ne_zero (h3 u) ξ.ne_zero)) fun u v => by
    apply Units.ext
    have := h2 u v
    rw [map_div₀, div_eq_iff (h3 u)] at this
    simp only [Units.val_mk0, Units.val_mul, Subgroup.coe_mul, AlgEquiv.mul_apply, this]
    ring
  have hle : f.range ≤ rootsOfUnity n Ω := by
    rintro _ ⟨u, rfl⟩
    exact (mem_rootsOfUnity _ _).2 (Units.ext (by simpa [f] using h1 u))
  haveI : Finite f.range := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  obtain ⟨⟨_, u0, rfl⟩, hg⟩ := (isCyclic_subgroup_units f.range).exists_generator
  refine ⟨u0, fun u => ?_⟩
  obtain ⟨k, hk⟩ := hg ⟨f u, u, rfl⟩
  refine ⟨k, ?_⟩
  have := congrArg (fun z : f.range => ((z : Ωˣ) : Ω)) hk
  simpa [f] using this.symm

theorem UpperTheory.V.Kum.reflRoot :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (n : ℕ) [NeZero n] (N : ℕ) (ζ : K) [Normal F K] (ψ : G F Ω →* (ZMod n)ˣ), U = galOf F K Ω → IsPrimitiveRoot ζ n →
    Nat.card {φ : U → ZMod n // φ ∈ EqHom N U (scalRep (ZMod n) ψ) ∧ ∃ (β : Ω) (a : Kˣ), IsRad (algebraMap K Ω ζ) U φ β ∧ β ^ n = algebraMap K Ω a ∧ IsOfFinOrder β} ≤ Nat.card (scalRep (ZMod n) ψ).invariants ∧
    Finite {φ : U → ZMod n // φ ∈ EqHom N U (scalRep (ZMod n) ψ) ∧ ∃ (β : Ω) (a : Kˣ), IsRad (algebraMap K Ω ζ) U φ β ∧ β ^ n = algebraMap K Ω a ∧ IsOfFinOrder β} := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ U n _ N ζ _ ψ hU hζ
  subst hU
  have hζ' : IsPrimitiveRoot (algebraMap K Ω ζ) n := hζ.map_of_injective (algebraMap K Ω).injective
  have hinj : ∀ x y : ZMod n, algebraMap K Ω ζ ^ x.val = algebraMap K Ω ζ ^ y.val → x = y := fun x y h =>
    ZMod.val_injective n (hζ'.pow_inj (ZMod.val_lt x) (ZMod.val_lt y) h)
  obtain ⟨ξ, b, hb, hξ⟩ := exists_gen K Ω n
  obtain ⟨u0, hu0⟩ := exists_generator_kummer_cocycle (galOf F K Ω) n _ hζ' (fun u => u.2 ζ) ξ (fun u => by rw [hb]; exact u.2 b)
  have hinv : ∀ φ : galOf F K Ω → ZMod n, φ ∈ EqHom N (galOf F K Ω) (scalRep (ZMod n) ψ) → ∀ β : Ω,
      IsRad (algebraMap K Ω ζ) _ φ β → IsOfFinOrder β → φ u0 ∈ (scalRep (ZMod n) ψ).invariants := by
    intro φ hφ β hr hβ g
    let u' : galOf F K Ω := ⟨g * u0.1 * g⁻¹, (galOf_normal F K Ω).conj_mem _ u0.2 g⟩
    have h1 : φ u' = scalRep (ZMod n) ψ g (φ u0) :=
      (Submodule.mem_iInf _).1 hφ.2 g u0 u' fun x => by
        show g (u0.1 (g.symm (g x))) = g (u0.1 x)
        rw [g.symm_apply_apply]
    rw [← h1]
    apply hinj
    have h2 : u'.1 β = u0.1 β := conj_root g u0.1 β hβ
    rw [hr.2, hr.2] at h2
    exact mul_right_cancel₀ hr.1 h2
  have hval : ∀ (φ : galOf F K Ω → ZMod n) (j : ℤ), IsRad (algebraMap K Ω ζ) _ φ ((ξ : Ω) ^ j) →
      ∀ u, algebraMap K Ω ζ ^ (φ u).val = (u.1 ξ / ξ) ^ j := fun φ j hr u => by
    rw [div_zpow, ← map_zpow₀, hr.2, mul_div_cancel_right₀ _ hr.1]
  let e : {φ : galOf F K Ω → ZMod n // φ ∈ EqHom N _ (scalRep (ZMod n) ψ) ∧ ∃ (β : Ω) (a : Kˣ),
      IsRad (algebraMap K Ω ζ) _ φ β ∧ β ^ n = algebraMap K Ω a ∧ IsOfFinOrder β} →
      (scalRep (ZMod n) ψ).invariants := fun φ => ⟨φ.1 u0, by
    obtain ⟨h, β, a, hr, -, hβ⟩ := φ.2
    exact hinv _ h β hr hβ⟩
  have he : Function.Injective e := by
    rintro ⟨φ, hφ, β, a, hr, ha, hβ⟩ ⟨φ', hφ', β', a', hr', ha', hβ'⟩ h
    have h0 : φ u0 = φ' u0 := congrArg Subtype.val h
    obtain ⟨j, rfl⟩ := hξ β a ha hβ
    obtain ⟨j', rfl⟩ := hξ β' a' ha' hβ'
    refine Subtype.ext (funext fun u => hinj _ _ ?_)
    obtain ⟨k, hk⟩ := hu0 u
    show algebraMap K Ω ζ ^ (φ u).val = algebraMap K Ω ζ ^ (φ' u).val
    rw [hval φ j hr, hval φ' j' hr', hk, ← zpow_mul, ← zpow_mul, mul_comm k, mul_comm k, zpow_mul, zpow_mul,
      ← hval φ j hr, ← hval φ' j' hr', h0]
  exact ⟨Nat.card_le_card_of_injective e he, Finite.of_injective e he⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RestrMem
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.restrMem :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (N : ℕ) (U V : Subgroup (G F Ω)) (h : U ≤ V) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (ρ : Representation R (G F Ω) M), (XDual N V R M).map (restr R M h) ≤ XDual N U R M ∧ (EqHom N V ρ).map (restr R M h) ≤ EqHom N U ρ ∧ ∀ (σ : Ω ≃+* Ω) (s : R), (EqEig N V ρ σ s).map (restr R M h) ≤ EqEig N U ρ σ s := by
  intro F Ω _ _ _ _ _ N U V h R M _ _ _ ρ
  have hX : ∀ φ ∈ XDual N V R M, restr R M h φ ∈ XDual N U R M := by
    intro φ hφ
    obtain ⟨h1, h2, h3, h4⟩ := hφ
    refine ⟨h1.comp_continuous (f := Subgroup.inclusion h) (continuous_inclusion h), fun a b => ?_, fun A u hu => ?_,
      fun A hA u hu => ?_⟩
    · exact h2 (Subgroup.inclusion h a) (Subgroup.inclusion h b)
    · exact h3 A (Subgroup.inclusion h u) hu
    · exact h4 A hA (Subgroup.inclusion h u) hu
  have hC : ∀ (σ : Ω ≃+* Ω) (T : M →ₗ[R] M), ∀ φ ∈ conjCond V σ T, restr R M h φ ∈ conjCond U σ T := by
    intro σ T φ hφ u u' hu
    exact hφ (Subgroup.inclusion h u) (Subgroup.inclusion h u') hu
  have hE : ∀ φ ∈ EqHom N V ρ, restr R M h φ ∈ EqHom N U ρ := by
    intro φ hφ
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hφ
    refine Submodule.mem_inf.2 ⟨hX φ h1, (Submodule.mem_iInf _).2 fun g => ?_⟩
    exact hC _ _ φ ((Submodule.mem_iInf _).1 h2 g)
  refine ⟨?_, ?_, fun σ s => ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    exact hX φ hφ
  · rintro _ ⟨φ, hφ, rfl⟩
    exact hE φ hφ
  · rintro _ ⟨φ, hφ, rfl⟩
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hφ
    exact Submodule.mem_inf.2 ⟨hE φ h1, hC _ _ φ h2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ToGalDict
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum
open scoped Pointwise

theorem UpperTheory.V.Kum.toGalDict :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (hU : U ≤ galOf F K Ω),
    (∀ (A : ValuationSubring Ω) (u : U), toGal K hU u ∈ Dec (F := K) A ↔ u.1 ∈ Dec (F := F) A) ∧
    (∀ (A : ValuationSubring Ω) (u : U), toGal K hU u ∈ Ine (F := K) A ↔ u.1 ∈ Ine (F := F) A) ∧
    Continuous (toGal K hU) ∧ (galOf F K Ω ≤ U → IsHomeomorph (toGal K hU) ∧ IsOpen (U : Set (G F Ω))) := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ U hU
  obtain ⟨hE, hO, -⟩ := galEmbTop F K Ω
  have hD : ∀ (A : ValuationSubring Ω) (u : U), toGal K hU u ∈ Dec (F := K) A ↔ u.1 ∈ Dec (F := F) A := by
    intro A u
    rw [mem_Dec, mem_Dec]
    have e : toGal K hU u • A = u.1 • A := by
      ext x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      exact Iff.rfl
    rw [e]
  have hcomp : galEmb F K Ω ∘ toGal K hU = Subtype.val := funext fun u => AlgEquiv.ext fun x => rfl
  have hc : Continuous (toGal K hU) := by
    rw [hE.isInducing.continuous_iff, hcomp]
    exact continuous_subtype_val
  refine ⟨hD, fun A u => ?_, hc, fun h => ⟨?_, ?_⟩⟩
  · exact ⟨fun h => ⟨(hD A u).1 h.1, h.2⟩, fun h => ⟨(hD A u).2 h.1, h.2⟩⟩
  · rw [isHomeomorph_iff_exists_inverse]
    refine ⟨hc, fun σ => ⟨galEmb F K Ω σ, h (galEmb_mem F K Ω σ)⟩, fun u => Subtype.ext (AlgEquiv.ext fun x => rfl),
      fun σ => AlgEquiv.ext fun x => rfl, hE.continuous.subtype_mk _⟩
  · rw [le_antisymm hU h]
    exact hO
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.UnitMinus
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.unitMinus :
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ) (a : Kˣ),
      a ∈ (∅ : Set (HeightOneSpectrum (𝓞 K))).unit K →
      a * Units.map (UpperTheory.V.cE (E := K)).toMonoidHom a ∈ powK (K := K) n →
      a ^ 2 ∈ CommGroup.torsion Kˣ ⊔ powK (K := K) n ∧
        (Odd n → a ∈ CommGroup.torsion Kˣ ⊔ powK (K := K) n) := by
  intro K _ _ _ n a ha hc
  obtain ⟨x, hx⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K (a : K)
    (fun v => (ha v (Set.notMem_empty v)).le)
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K ((a⁻¹ : Kˣ) : K)
    (fun v => ((Subgroup.inv_mem _ ha) v (Set.notMem_empty v)).le)
  have hxy : x * y = 1 := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [map_mul, hx, hy, map_one, Units.mul_inv]
  let u : (𝓞 K)ˣ := Units.mkOfMulEqOne x y hxy
  let f : (𝓞 K)ˣ →* Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom
  have hu : f u = a := Units.ext hx
  have hcu : f (IsCMField.unitsComplexConj K u) = Units.map (UpperTheory.V.cE (E := K)).toMonoidHom a := by
    rw [← hu]
    exact Units.ext rfl
  have hfin : IsOfFinOrder (u * (IsCMField.unitsComplexConj K u)⁻¹) :=
    (IsCMField.unitsMulComplexConjInv K u).2
  have htor : a * (Units.map (UpperTheory.V.cE (E := K)).toMonoidHom a)⁻¹ ∈ CommGroup.torsion Kˣ := by
    have := f.isOfFinOrder hfin
    rw [map_mul, map_inv, hu, hcu] at this
    exact this
  have h2 : a ^ 2 ∈ CommGroup.torsion Kˣ ⊔ powK (K := K) n := by
    have e : a ^ 2 = (a * (Units.map (UpperTheory.V.cE (E := K)).toMonoidHom a)⁻¹) *
        (a * Units.map (UpperTheory.V.cE (E := K)).toMonoidHom a) := by
      rw [mul_mul_mul_comm, inv_mul_cancel, mul_one, pow_two]
    rw [e]
    exact Subgroup.mul_mem_sup htor hc
  refine ⟨h2, ?_⟩
  rintro ⟨k, rfl⟩
  have hn : a ^ (2 * k + 1) ∈ CommGroup.torsion Kˣ ⊔ powK (K := K) (2 * k + 1) :=
    Subgroup.mem_sup_right ⟨a, rfl⟩
  rw [pow_succ, pow_mul] at hn
  exact (Subgroup.mul_mem_cancel_left _ (Subgroup.pow_mem _ h2 k)).1 hn
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ZmodToQZ
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.zmodToQZ :
    ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), ∃ ι : ZMod (l ^ r) →+ QZ l, Function.Injective ι ∧ (∀ x, x ∈ Set.range ι ↔ (l : ℤ_[l]) ^ r • x = 0) ∧
    ∀ (z : ℤ_[l]) (a : ZMod (l ^ r)), ι (PadicInt.toZModPow r z * a) = z • ι a := by
  intro l _ r
  have hl : l.Prime := Fact.out
  have hlr0 : ((l : ℚ_[l]) ^ r) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hl.ne_zero)
  have zsm : ∀ (k : ℤ) (q : ℚ_[l]), k • QZ.mk l q = QZ.mk l ((k : ℚ_[l]) * q) := by
    intro k q
    rw [← Int.cast_smul_eq_zsmul ℤ_[l]]
    show QZ.mk l (((k : ℤ_[l]) : ℚ_[l]) * q) = _
    rw [PadicInt.coe_intCast]
  have hker : ((l ^ r : ℕ) : ℤ) • QZ.mk l (((l : ℚ_[l]) ^ r)⁻¹) = 0 := by
    rw [zsm]
    refine (Submodule.Quotient.mk_eq_zero (ZlSub l)).2 ⟨1, ?_⟩
    push_cast
    exact (mul_inv_cancel₀ hlr0).symm
  let ι : ZMod (l ^ r) →+ QZ l :=
    ZMod.lift (l ^ r) ⟨zmultiplesHom (QZ l) (QZ.mk l (((l : ℚ_[l]) ^ r)⁻¹)), by
      rw [zmultiplesHom_apply]
      exact hker⟩
  have hι : ∀ k : ℤ, ι (k : ZMod (l ^ r)) = QZ.mk l ((k : ℚ_[l]) * ((l : ℚ_[l]) ^ r)⁻¹) := by
    intro k
    simp only [ι, ZMod.lift_coe, zmultiplesHom_apply]
    exact zsm k _
  have hkill : ∀ a : ZMod (l ^ r), (l ^ r : ℕ) • ι a = 0 := by
    intro a
    rw [← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero]
  have h3 : ∀ (z : ℤ_[l]) (a : ZMod (l ^ r)), ι (PadicInt.toZModPow r z * a) = z • ι a := by
    intro z a
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec r z)
    have hz : PadicInt.toZModPow r z = ((z.appr r : ℕ) : ZMod (l ^ r)) := rfl
    rw [hz, ← nsmul_eq_mul, map_nsmul]
    have hzw : z = ((z.appr r : ℕ) : ℤ_[l]) + w * ((l ^ r : ℕ) : ℤ_[l]) := by
      push_cast
      rw [hw]
      ring
    conv_rhs => rw [hzw]
    rw [add_smul, Nat.cast_smul_eq_nsmul, mul_smul, Nat.cast_smul_eq_nsmul, hkill, smul_zero, add_zero]
  refine ⟨ι, ?_, ?_, h3⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective a
    rw [hι] at ha
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero (ZlSub l)).1 ha
    have hy' : (y : ℚ_[l]) = (k : ℚ_[l]) * ((l : ℚ_[l]) ^ r)⁻¹ := hy
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hky : (k : ℤ_[l]) = y * (l : ℤ_[l]) ^ r := by
      apply PadicInt.ext
      push_cast
      rw [hy', mul_assoc, inv_mul_cancel₀ hlr0, mul_one]
    have hn : ‖(k : ℤ_[l])‖ ≤ (l : ℝ) ^ (-(r : ℤ)) := by
      rw [hky, norm_mul, PadicInt.norm_p_pow]
      exact mul_le_of_le_one_left (by positivity) (PadicInt.norm_le_one y)
    have hd := PadicInt.norm_int_le_pow_iff_dvd.1 hn
    exact_mod_cast hd
  · intro x
    constructor
    · rintro ⟨a, rfl⟩
      have h := h3 ((l : ℤ_[l]) ^ r) a
      rw [map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_mul, map_zero] at h
      exact h.symm
    · intro hx
      obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) x
      have hx' : QZ.mk l ((((l : ℤ_[l]) ^ r : ℤ_[l]) : ℚ_[l]) * q) = 0 := hx
      obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero (ZlSub l)).1 hx'
      have hz' : (z : ℚ_[l]) = (((l : ℤ_[l]) ^ r : ℤ_[l]) : ℚ_[l]) * q := hz
      push_cast at hz'
      refine ⟨PadicInt.toZModPow r z, ?_⟩
      rw [← mul_one (PadicInt.toZModPow r z), h3, show (1 : ZMod (l ^ r)) = ((1 : ℤ) : ZMod (l ^ r)) by simp, hι]
      show QZ.mk l ((z : ℚ_[l]) * (((1 : ℤ) : ℚ_[l]) * ((l : ℚ_[l]) ^ r)⁻¹)) = Submodule.Quotient.mk q
      congr 1
      rw [hz']
      push_cast
      field_simp
end

