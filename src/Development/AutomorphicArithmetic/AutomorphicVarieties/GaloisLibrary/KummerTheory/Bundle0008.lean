module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CardSel
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem card_parity_sign_length_of_eq {G C : Type} [CommGroup G] [Group C] (A U P : Subgroup G) (hU : U ≤ A) (hP : P ≤ A)
    (f : A →* C) (hf : f.ker = (U ⊔ P).subgroupOf A) :
    Nat.card (A ⧸ P.subgroupOf A) = Nat.card (U ⧸ P.subgroupOf U) * Nat.card f.range := by
  have hQ : U ⊔ P ≤ A := sup_le hU hP
  have hPQ : P.subgroupOf A ≤ (U ⊔ P).subgroupOf A := fun x hx => (le_sup_right : P ≤ U ⊔ P) hx
  change (P.subgroupOf A).index = (P.subgroupOf U).index * _
  rw [← Subgroup.relIndex_mul_index hPQ, Subgroup.relIndex_subgroupOf hQ, Subgroup.relIndex_sup_right, ← hf]
  congr 1
  exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv

theorem UpperTheory.V.Kum.cardSel :
    ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ), n ≠ 0 → Nat.card (SelK S n ⧸ (powK (K := K) n).subgroupOf (SelK S n)) = Nat.card (S.unit K ⧸ (powK (K := K) n).subgroupOf (S.unit K)) * Nat.card {c : ClS S // c ^ n = 1} := by
  intro K _ _ S n hn
  obtain ⟨hmul, hpow, -⟩ := radClMul K S n hn
  let f : SelK S n →* ClS S :=
    MonoidHom.mk' (fun a => (QuotientGroup.mk (radCl n a.1) : ClS S)) fun a b => hmul a.1 a.2 b.1 b.2
  have hU : S.unit K ≤ SelK S n := by
    intro a ha v hv
    have h : v.valuation K (a : K) = 1 := ha v hv
    have h' : v.valuationOfNeZero a = 1 := by
      rw [← HeightOneSpectrum.valuationOfNeZero_eq] at h
      exact_mod_cast h
    simp [ordv, h']
  have hP : powK (K := K) n ≤ SelK S n := by
    rintro _ ⟨b, rfl⟩ v _
    simp [ordv]
  have hf : f.ker = (S.unit K ⊔ powK (K := K) n).subgroupOf (SelK S n) := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change (QuotientGroup.mk (radCl n a.1) : ClS S) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    have mem_unit_iff (u : Kˣ) : u ∈ S.unit K ↔ ∀ v ∉ S, ordv v u = 0 := by
      change (∀ v ∉ S, v.valuation K (u : K) = 1) ↔ _
      refine forall₂_congr fun v _ => ?_
      rw [← HeightOneSpectrum.valuationOfNeZero_eq, ← WithZero.coe_one, WithZero.coe_inj,
        ordv, neg_eq_zero, toAdd_eq_zero]
    constructor
    · intro ha
      classical
      have finite_add {d e : HeightOneSpectrum (𝓞 K) → ℤ}
          (hd : {v | d v ≠ 0}.Finite) (he : {v | e v ≠ 0}.Finite) :
          {v | d v + e v ≠ 0}.Finite := by
        refine (hd.union he).subset ?_
        intro v hv
        by_contra h
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
        exact hv (by rw [h.1, h.2, add_zero])
      have prod_add {d e : HeightOneSpectrum (𝓞 K) → ℤ}
          (hd : {v | d v ≠ 0}.Finite) (he : {v | e v ≠ 0}.Finite) :
          ∏ᶠ v, primeCl v ^ (d v + e v) = (∏ᶠ v, primeCl v ^ d v) * ∏ᶠ v, primeCl v ^ e v := by
        rw [← finprod_mul_distrib]
        · exact finprod_congr fun v => zpow_add _ _ _
        · exact hd.subset fun v hv h => hv (by simp [h])
        · exact he.subset fun v hv h => hv (by simp [h])
      have supported {c : ClassGroup (𝓞 K)} (hc : c ∈ clSub S) :
          ∃ g : HeightOneSpectrum (𝓞 K) → ℤ, {v | g v ≠ 0}.Finite ∧ (∀ v ∉ S, g v = 0) ∧
            c = ∏ᶠ v, primeCl v ^ g v := by
        induction hc using Subgroup.closure_induction with
        | mem x hx =>
          obtain ⟨w, hw, rfl⟩ := hx
          refine ⟨fun v => if v = w then 1 else 0, (Set.finite_singleton w).subset ?_,
            fun v hv => if_neg fun (h : v = w) => hv (h ▸ hw), ?_⟩
          · intro v hv
            by_contra h
            exact hv (if_neg h)
          · rw [finprod_eq_single _ w fun v hv => by simp [hv]]
            simp
        | one => exact ⟨fun _ => 0, by simp, by simp, by simp⟩
        | mul x y _ _ hx hy =>
          obtain ⟨d, hd, hdS, rfl⟩ := hx
          obtain ⟨e, he, heS, rfl⟩ := hy
          exact ⟨fun v => d v + e v, finite_add hd he, fun v hv => by simp [hdS v hv, heS v hv],
            (prod_add hd he).symm⟩
        | inv x _ hx =>
          obtain ⟨d, hd, hdS, rfl⟩ := hx
          refine ⟨fun v => -d v, by simpa using hd, fun v hv => by simp [hdS v hv], ?_⟩
          rw [← finprod_inv_distrib]
          exact finprod_congr fun v => (zpow_neg _ _).symm
      obtain ⟨g, hg, hgS, hclass⟩ := supported (inv_mem ha)
      obtain ⟨mk_eq_prod, count_eq_ordv, finite_ordv, _⟩ := clProd K
      have hdiv : {v | ordv v a.1 / (n : ℤ) ≠ 0}.Finite :=
        (finite_ordv a.1).subset fun v hv h => hv (by simp [h])
      let d (v : HeightOneSpectrum (𝓞 K)) : ℤ := ordv v a.1 / n + g v
      have hd : {v | d v ≠ 0}.Finite := finite_add hdiv hg
      have hdClass : ∏ᶠ v, primeCl v ^ d v = 1 := by
        change (∏ᶠ v, primeCl v ^ (ordv v a.1 / (n : ℤ) + g v)) = 1
        rw [prod_add hdiv hg, ← hclass]
        exact mul_inv_cancel _
      let I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
        ∏ᶠ v : HeightOneSpectrum (𝓞 K), (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ d v
      have hI0 : I ≠ 0 := by
        refine finprod_induction (fun J => J ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) fun v => ?_
        exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot)
      have hcount (v : HeightOneSpectrum (𝓞 K)) : FractionalIdeal.count K v I = d v :=
        FractionalIdeal.count_finprod K v d (by simpa [Filter.eventually_cofinite] using hd)
      have hIClass : ClassGroup.mk K (Units.mk0 I hI0) = 1 := by
        rw [mk_eq_prod, ← hdClass]
        exact finprod_congr fun v => by rw [Units.val_mk0, hcount]
      obtain ⟨b, hb⟩ := (FractionalIdeal.isPrincipal_iff _).1 (ClassGroup.mk_eq_one_iff.1 hIClass)
      rw [Units.val_mk0] at hb
      have hb0 : b ≠ 0 := by
        rintro rfl
        exact hI0 (by rw [hb, FractionalIdeal.spanSingleton_zero])
      let u := Units.mk0 b hb0
      have hu (v : HeightOneSpectrum (𝓞 K)) : ordv v u = d v := by
        rw [← count_eq_ordv, show (u : K) = b from rfl, ← hb, hcount]
      refine Subgroup.mem_sup.2 ⟨a.1 * (u ^ n)⁻¹, (mem_unit_iff _).2 fun v hv => ?_,
        u ^ n, ⟨u, rfl⟩, by simp⟩
      have hpow_v : ordv v (u ^ n) = n * ordv v u := by simp [ordv]
      rw [ordv_mul, ordv_inv, hpow_v, hu, show d v = ordv v a.1 / n + g v from rfl,
        hgS v hv, add_zero, Int.mul_ediv_cancel' (a.2 v hv), add_neg_cancel]
    · intro ha
      obtain ⟨u, hu, _, ⟨b, rfl⟩, hab⟩ := Subgroup.mem_sup.1 ha
      rw [← hab, powMonoidHom_apply, (radClMul K S n hn).2.2]
      refine finprod_induction (fun c => c ∈ clSub S) (one_mem _) (fun _ _ => mul_mem) fun v => ?_
      by_cases hv : v ∈ S
      · have hmem : primeCl v ∈ clSub S :=
          Subgroup.subset_closure (show primeCl v ∈ primeCl '' S from ⟨v, hv, rfl⟩)
        exact zpow_mem hmem _
      · rw [(mem_unit_iff u).1 hu v hv]
        simp
  rw [card_parity_sign_length_of_eq _ _ _ hU hP f hf]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ⟨?_, fun hc => ?_⟩)
  · rintro ⟨a, rfl⟩
    exact hpow a.1 a.2
  · obtain ⟨a, ha, h⟩ := radClSurj K S n hn c hc
    exact ⟨⟨a, ha⟩, h⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ReflTw
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem reflTw_empty {K : Type} [Field K] [NumberField K] {c d : ClassGroup (𝓞 K)}
    (h : (QuotientGroup.mk c : ClS (∅ : Set (HeightOneSpectrum (𝓞 K)))) = QuotientGroup.mk d) : c = d := by
  rw [QuotientGroup.eq] at h
  have e : clSub (∅ : Set (HeightOneSpectrum (𝓞 K))) = ⊥ := by simp [clSub]
  rw [e, Subgroup.mem_bot] at h
  exact inv_mul_eq_one.1 h

private theorem reflTw_one {K : Type} [Field K] [NumberField K] (n : ℕ) : radCl n (1 : Kˣ) = 1 := by
  simp [radCl, ordv_one]

private theorem reflTw_pow {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : n ≠ 0) {a : Kˣ}
    (ha : a ∈ SelK (∅ : Set (HeightOneSpectrum (𝓞 K))) n) (m : ℕ) : radCl n (a ^ m) = radCl n a ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, reflTw_one]
  | succ m ih =>
    rw [pow_succ, pow_succ, ← ih]
    apply reflTw_empty
    rw [QuotientGroup.mk_mul]
    exact (radClMul K ∅ n hn).1 _ (pow_mem ha m) _ ha

private theorem reflTw_pow_eq {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : n ≠ 0) {a : Kˣ}
    (ha : a ∈ SelK (∅ : Set (HeightOneSpectrum (𝓞 K))) n) : radCl n a ^ n = 1 := by
  apply reflTw_empty
  rw [QuotientGroup.mk_pow, QuotientGroup.mk_one]
  exact (radClMul K ∅ n hn).2.1 _ ha

private theorem reflTw_dvd (n : ℕ) [NeZero n] : n ∣ (-1 : ZMod n).val + 1 := by
  rw [← ZMod.natCast_eq_zero_iff]
  simp

private theorem reflTw_radPow {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {U : Subgroup (G F Ω)} {n : ℕ} [NeZero n]
    {ζ β : Ω} (hζ : ζ ^ n = 1) {φ : U → ZMod n} (h : ∀ u : U, u.1 β = ζ ^ (φ u).val * β) (m : ZMod n) (u : U) :
    u.1 (β ^ m.val) = ζ ^ (m * φ u).val * β ^ m.val := by
  rw [map_pow, h, mul_pow, ← pow_mul, ZMod.val_mul, ← pow_eq_pow_mod _ hζ, mul_comm m.val]

private theorem reflTw_key {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {K : Type}
    [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω]
    {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) {φ : galOf F K Ω → ZMod n} {β : Ω} {a : Kˣ}
    (hβ : IsRad (algebraMap K Ω ζ) (galOf F K Ω) φ β) (ha : β ^ n = algebraMap K Ω a)
    {τ : K ≃+* K} {σ : Ω ≃+* Ω} (hl : IsLift τ σ) (k s : ZMod n)
    (hk : σ (algebraMap K Ω ζ) = algebraMap K Ω ζ ^ k.val)
    (hs : ∀ u u' : galOf F K Ω, (∀ x, u'.1 (σ x) = σ (u.1 x)) → φ u = s * φ u') :
    ∃ c : Kˣ, Units.map τ.toMonoidHom a = a ^ (k * s).val * c ^ n := by
  have hz : algebraMap K Ω ζ ^ n = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have h1 : IsRad (algebraMap K Ω ζ) (galOf F K Ω) (fun u => k * s * φ u) (σ β) := by
    refine radConj F Ω _ n _ β σ k φ _ hz hk hβ fun u' => ?_
    have hK : ∀ x : K, ((σ.trans u'.1.toRingEquiv).trans σ.symm) (algebraMap K Ω x) = algebraMap K Ω x := fun x => by
      show σ.symm (u'.1 (σ (algebraMap K Ω x))) = _
      rw [hl x, u'.2, ← hl x, σ.symm_apply_apply]
    let u : galOf F K Ω := ⟨AlgEquiv.ofRingEquiv (f := (σ.trans u'.1.toRingEquiv).trans σ.symm) fun x => by
      rw [IsScalarTower.algebraMap_apply F K Ω, hK], hK⟩
    have hu : ∀ x, u'.1 (σ x) = σ (u.1 x) := fun x => (σ.apply_symm_apply _).symm
    exact ⟨u, hu, by rw [hs u u' hu, mul_assoc]⟩
  have h2 : IsRad (algebraMap K Ω ζ) (galOf F K Ω) (fun u => k * s * φ u) (β ^ (k * s).val) :=
    ⟨pow_ne_zero _ hβ.1, reflTw_radPow hz hβ.2 _⟩
  obtain ⟨c, hc⟩ := (radXDual F Ω K _ n 1 ζ rfl hζ).2 _ _ _ h2 h1
  refine ⟨c, Units.ext ((algebraMap K Ω).injective ?_)⟩
  show algebraMap K Ω (τ a) = _
  rw [← hl, ← ha, map_pow, hc, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_mul, map_pow,
    map_pow, ← ha]
  ring

theorem UpperTheory.V.Kum.reflTw :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (n : ℕ) [NeZero n] (N : ℕ) (ζ : K) [Normal F K] (χ ψ : G F Ω →* (ZMod n)ˣ) (φ : U → ZMod n) (β : Ω) (a : Kˣ), U = galOf F K Ω → IsPrimitiveRoot ζ n → (∀ g : G F Ω, g (algebraMap K Ω ζ) = (algebraMap K Ω ζ) ^ (χ g : ZMod n).val) → φ ∈ EqHom N U (scalRep (ZMod n) ψ) → IsRad (algebraMap K Ω ζ) U φ β → β ^ n = algebraMap K Ω a →
    radCl n a ∈ ClTw K n (χ * ψ⁻¹) ∧ ∀ (τ : K ≃+* K) (σ : Ω ≃+* Ω), IsLift τ σ → τ ζ = ζ⁻¹ → φ ∈ conjCond U σ ((1 : ZMod n) • (LinearMap.id : ZMod n →ₗ[ZMod n] ZMod n)) → a * Units.map τ.toMonoidHom a ∈ powK K n ∧ radCl n a ∈ ClMinus τ := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ U n _ N ζ _ χ ψ φ β a hU hζ hχ hφ hβ ha
  subst hU
  have hn : n ≠ 0 := NeZero.ne n
  have hS : a ∈ SelK (∅ : Set (HeightOneSpectrum (𝓞 K))) n := by
    obtain ⟨β₀, a₀, h₀, ha₀, hS₀⟩ := (radXDual F Ω K _ n N ζ rfl hζ).1 φ hφ.1
    obtain ⟨c, hc⟩ := (radXDual F Ω K _ n N ζ rfl hζ).2 _ _ _ h₀ hβ
    have e : a = a₀ * c ^ n := Units.ext ((algebraMap K Ω).injective (by
      rw [← ha, hc, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, ← ha₀]; ring))
    rw [e]
    refine mul_mem hS₀ fun v _ => ?_
    refine ⟨ordv v c, ?_⟩
    simp [ordv]
  have h1 := reflTw_pow_eq hn hS
  have hmap : ∀ (τ : K ≃+* K) (m : ℕ) (c : Kˣ), Units.map τ.toMonoidHom a = a ^ m * c ^ n →
      clMap τ (radCl n a) = radCl n a ^ m := fun τ m c h => by
    rw [radClMap, h, (radClMul K ∅ n hn).2.2, reflTw_pow hn hS]
  refine ⟨⟨h1, fun g τ hl => ?_⟩, fun τ σ hl hτ hc => ?_⟩
  · have hg : φ ∈ conjCond (galOf F K Ω) g.toRingEquiv (scalRep (ZMod n) ψ g) := (Submodule.mem_iInf _).1 hφ.2 g
    obtain ⟨c, hc⟩ := reflTw_key hζ hβ ha hl (χ g) ((ψ g)⁻¹ : (ZMod n)ˣ) (hχ g) fun u u' h => by
      rw [hg u u' h, scalRep_apply]
      simp
    refine hmap τ _ c ?_
    rw [hc]
    simp
  · obtain ⟨j, hj⟩ := reflTw_dvd n
    have hk : σ (algebraMap K Ω ζ) = algebraMap K Ω ζ ^ (-1 : ZMod n).val := by
      rw [hl, hτ, ← map_pow]
      congr 1
      refine inv_eq_of_mul_eq_one_left ?_
      rw [← pow_succ, hj, pow_mul, hζ.pow_eq_one, one_pow]
    obtain ⟨c, hc⟩ := reflTw_key hζ hβ ha hl (-1) 1 hk fun u u' h => by
      rw [hc u u' h]
      simp
    rw [mul_one] at hc
    refine ⟨⟨a ^ j * c, ?_⟩, ?_⟩
    · rw [hc, ← mul_assoc, ← pow_succ', hj, powMonoidHom_apply, mul_pow, ← pow_mul, mul_comm j]
    · show clMap τ (radCl n a) * radCl n a = 1
      rw [hmap τ _ c hc, ← pow_succ, hj, pow_mul, h1, one_pow]
end

