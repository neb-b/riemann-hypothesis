module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadClKer
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

section

variable {K : Type} [Field K] [NumberField K]

private theorem prod_add (f g : HeightOneSpectrum (𝓞 K) → ℤ) (hf : {v | f v ≠ 0}.Finite)
    (hg : {v | g v ≠ 0}.Finite) :
    ∏ᶠ v, primeCl v ^ (f v + g v) = (∏ᶠ v, primeCl v ^ f v) * ∏ᶠ v, primeCl v ^ g v := by
  rw [← finprod_mul_distrib]
  · exact finprod_congr fun v => zpow_add _ _ _
  · exact hf.subset fun v hv h => hv (by simp [h])
  · exact hg.subset fun v hv h => hv (by simp [h])

private theorem fin_add {f g : HeightOneSpectrum (𝓞 K) → ℤ} (hf : {v | f v ≠ 0}.Finite)
    (hg : {v | g v ≠ 0}.Finite) : {v | f v + g v ≠ 0}.Finite :=
  (hf.union hg).subset fun v hv => by
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
    exact hv (by rw [h.1, h.2, add_zero])

private theorem mem_clSub {S : Set (HeightOneSpectrum (𝓞 K))} {c : ClassGroup (𝓞 K)} (hc : c ∈ clSub S) :
    ∃ g : HeightOneSpectrum (𝓞 K) → ℤ, {v | g v ≠ 0}.Finite ∧ (∀ v ∉ S, g v = 0) ∧
      c = ∏ᶠ v, primeCl v ^ g v := by
  classical
  induction hc using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    refine ⟨fun v => if v = w then 1 else 0, (Set.finite_singleton w).subset fun v hv => ?_,
      fun v hv => if_neg fun (h : v = w) => hv (h ▸ hw), ?_⟩
    · by_contra h
      exact hv (if_neg h)
    · rw [finprod_eq_single _ w fun v hv => by simp [hv]]
      simp
  | one => exact ⟨fun _ => 0, by simp, by simp, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨f, hf, hf', rfl⟩ := hx
    obtain ⟨g, hg, hg', rfl⟩ := hy
    exact ⟨fun v => f v + g v, fin_add hf hg, fun v hv => by simp [hf' v hv, hg' v hv],
      (prod_add f g hf hg).symm⟩
  | inv x _ hx =>
    obtain ⟨f, hf, hf', rfl⟩ := hx
    refine ⟨fun v => -f v, by simpa using hf, fun v hv => by simp [hf' v hv], ?_⟩
    rw [← finprod_inv_distrib]
    exact finprod_congr fun v => (zpow_neg _ _).symm

private theorem exists_ordv (f : HeightOneSpectrum (𝓞 K) → ℤ) (hf : {v | f v ≠ 0}.Finite)
    (h : ∏ᶠ v, primeCl v ^ f v = 1) : ∃ b : Kˣ, ∀ v, ordv v b = f v := by
  obtain ⟨h1, h2, -, -⟩ := clProd K
  set I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ f v with hI
  have hI0 : I ≠ 0 := by
    rw [hI]
    refine finprod_induction (fun J => J ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) fun v => ?_
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot)
  have hc : ∀ v, FractionalIdeal.count K v I = f v := fun v =>
    FractionalIdeal.count_finprod K v f (by simpa [Filter.eventually_cofinite] using hf)
  have h3 : ClassGroup.mk K (Units.mk0 I hI0) = 1 := by
    rw [h1, ← h]
    exact finprod_congr fun v => by rw [Units.val_mk0, hc]
  obtain ⟨b, hb⟩ := (FractionalIdeal.isPrincipal_iff _).1 (ClassGroup.mk_eq_one_iff.1 h3)
  rw [Units.val_mk0] at hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hI0 (by rw [hb, FractionalIdeal.spanSingleton_zero])
  exact ⟨Units.mk0 b hb0, fun v => by rw [← h2, Units.val_mk0, ← hb, hc]⟩

private theorem mem_unit {S : Set (HeightOneSpectrum (𝓞 K))} {u : Kˣ} :
    u ∈ S.unit K ↔ ∀ v ∉ S, ordv v u = 0 := by
  change (∀ v ∉ S, v.valuation K (u : K) = 1) ↔ _
  refine forall₂_congr fun v _ => ?_
  rw [← HeightOneSpectrum.valuationOfNeZero_eq, ← WithZero.coe_one, WithZero.coe_inj, ordv, neg_eq_zero,
    toAdd_eq_zero]

private theorem ordv_pow (v : HeightOneSpectrum (𝓞 K)) (b : Kˣ) (n : ℕ) : ordv v (b ^ n) = n * ordv v b := by
  simp [ordv]

end

theorem UpperTheory.V.Kum.radClKer :
    ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ), n ≠ 0 → ∀ a ∈ SelK S n, (radCl n a ∈ clSub S ↔ a ∈ S.unit K ⊔ powK (K := K) n) := by
  intro K _ _ S n hn a ha
  constructor
  · intro h
    obtain ⟨g, hg, hg', hc⟩ := mem_clSub (inv_mem h)
    have hf : {v | ordv v a / n ≠ 0}.Finite :=
      ((clProd K).2.2.1 a).subset fun v hv h => hv (by simp [h])
    obtain ⟨b, hb⟩ := exists_ordv (fun v => ordv v a / n + g v) (fin_add hf hg) (by
      rw [prod_add _ _ hf hg, ← hc]
      exact mul_inv_cancel _)
    refine Subgroup.mem_sup.2 ⟨a * (b ^ n)⁻¹, mem_unit.2 fun v hv => ?_, b ^ n, ⟨b, rfl⟩, by simp⟩
    rw [ordv_mul, ordv_inv, ordv_pow, hb, hg' v hv, add_zero, Int.mul_ediv_cancel' (ha v hv), add_neg_cancel]
  · intro h
    obtain ⟨u, hu, _, ⟨b, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 h
    rw [powMonoidHom_apply, (radClMul K S n hn).2.2]
    refine finprod_induction (fun c => c ∈ clSub S) (one_mem _) (fun _ _ => mul_mem) fun v => ?_
    by_cases hv : v ∈ S
    · have h0 : primeCl v ∈ clSub S := Subgroup.subset_closure ⟨v, hv, rfl⟩
      exact zpow_mem h0 _
    · rw [mem_unit.1 hu v hv]
      simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadXDual
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.radXDual :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (n : ℕ) [NeZero n] (N : ℕ) (ζ : K), U = galOf F K Ω → IsPrimitiveRoot ζ n → (∀ φ ∈ XDual N U (ZMod n) (ZMod n), ∃ (β : Ω) (a : Kˣ), IsRad (algebraMap K Ω ζ) U φ β ∧ β ^ n = algebraMap K Ω a ∧ a ∈ SelK (∅ : Set (HeightOneSpectrum (𝓞 K))) n) ∧
    ∀ (φ : U → ZMod n) (β β' : Ω), IsRad (algebraMap K Ω ζ) U φ β → IsRad (algebraMap K Ω ζ) U φ β' → ∃ c : Kˣ, β' = algebraMap K Ω c * β := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ U n _ N ζ hU hζ
  subst hU
  have hζ' : IsPrimitiveRoot (algebraMap K Ω ζ) n := hζ.map_of_injective (algebraMap K Ω).injective
  obtain ⟨-, hI, -, hH⟩ := toGalDict F Ω K (galOf F K Ω) le_rfl
  obtain ⟨hH, -⟩ := hH le_rfl
  let s : G K Ω → galOf F K Ω := fun σ => ⟨galEmb F K Ω σ, galEmb_mem F K Ω σ⟩
  have hs : ∀ σ, toGal K le_rfl (s σ) = σ := fun σ => AlgEquiv.ext fun x => rfl
  have hs' : ∀ u, s (toGal K le_rfl u) = u := fun u => Subtype.ext (AlgEquiv.ext fun x => rfl)
  have hsm : ∀ σ τ, s (σ * τ) = s σ * s τ := fun σ τ => Subtype.ext (map_mul (galEmb F K Ω) σ τ)
  have hsc : Continuous s := by
    have e : s = hH.homeomorph.symm := funext fun σ => by
      rw [eq_comm, Homeomorph.symm_apply_eq]
      exact (hs σ).symm
    rw [e]
    exact hH.homeomorph.symm.continuous
  refine ⟨fun φ hφ => ?_, fun φ β β' hβ hβ' => ?_⟩
  · obtain ⟨hlc, hadd, hine, -⟩ := hφ
    obtain ⟨β, a, hβa, hβ⟩ := radExists K Ω n (algebraMap K Ω ζ) (fun _ => 1) (fun σ => φ (s σ)) hζ'
      (fun g => by
        rw [g.commutes, ZMod.val_one_eq_one_mod, hζ'.eq_orderOf, pow_mod_orderOf, pow_one])
      (hlc.comp_continuous hsc) (fun g h => by rw [hsm, hadd, one_mul])
    refine ⟨β, a, ⟨?_, fun u => ?_⟩, hβa, fun v _ => ?_⟩
    · rintro rfl
      rw [zero_pow (NeZero.ne n), eq_comm, map_eq_zero] at hβa
      exact a.ne_zero hβa
    · have := hβ (toGal K le_rfl u)
      rw [hs'] at this
      exact this
    · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
      refine dvdOfIne K Ω n A v β a hA hβa fun g hg => ?_
      have h0 : φ (s g) = 0 := hine A (s g) ((hI A (s g)).1 (by rw [hs]; exact hg))
      rw [hβ g, h0, ZMod.val_zero, pow_zero, one_mul]
  · have hz : algebraMap K Ω ζ ≠ 0 := hζ'.ne_zero (NeZero.ne n)
    haveI : IsGalois K Ω := IsAlgClosure.isGalois K Ω
    have hfix : ∀ g : G K Ω, g (β' / β) = β' / β := fun g => by
      have e1 : g β = _ := hβ.2 (s g)
      have e2 : g β' = _ := hβ'.2 (s g)
      rw [map_div₀, e1, e2, mul_div_mul_left _ _ (pow_ne_zero _ hz)]
    obtain ⟨c, hc⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (β' / β)).2 hfix
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero, eq_comm] at hc
      exact div_ne_zero hβ'.1 hβ.1 hc
    refine ⟨Units.mk0 c hc0, ?_⟩
    rw [Units.val_mk0, hc, div_mul_cancel₀ _ hβ.1]
end

