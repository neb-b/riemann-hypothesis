module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import GroundTheory.GlobalFields.ClassFieldConsequences.RayClassField
public import GroundTheory.GlobalFields.Artin.OneDim
public import CompanionTheory.AutomorphicTheory.PlaceSeparation.ArtinA

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusDensity.ExtIdeal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem UpperTheory.V.Ws.Tw.extIdeal_inj {H G : Type} [CommGroup H] [CommGroup G] {k : Type} [Field k] [IsAlgClosed k]
    (i : H →* G) (hi : Function.Injective i) (g : H →* kˣ) : ∃ F : G →* kˣ, ∀ x, F (i x) = g x := by
  have hdiv : ∀ {n : ℤ}, n ≠ 0 → Function.Surjective (fun a : Additive kˣ => n • a) := by
    intro n hn y
    have hpos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq ((Additive.toMul y : kˣ) : k) hpos
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow hpos.ne'] at hx
      exact (Additive.toMul y).ne_zero hx.symm
    have hu : Units.mk0 x hx0 ^ n.natAbs = Additive.toMul y := by
      ext
      simp [hx]
    rcases Int.natAbs_eq n with h | h
    · refine ⟨Additive.ofMul (Units.mk0 x hx0), ?_⟩
      apply Additive.toMul.injective
      simp only [toMul_zsmul, toMul_ofMul]
      rw [h, zpow_natCast, hu]
    · refine ⟨Additive.ofMul (Units.mk0 x hx0)⁻¹, ?_⟩
      apply Additive.toMul.injective
      simp only [toMul_zsmul, toMul_ofMul]
      rw [h, zpow_neg, zpow_natCast, inv_pow, inv_inv, hu]
  letI : DivisibleBy (Additive kˣ) ℤ := divisibleByOfSMulRightSurj _ _ hdiv
  obtain ⟨F, hF⟩ := (Module.Baer.of_divisible (Additive kˣ)).extension_property_addMonoidHom
    (MonoidHom.toAdditive i) hi (MonoidHom.toAdditive g)
  refine ⟨MonoidHom.toAdditive.symm F, fun x => ?_⟩
  exact congrArg Additive.toMul (DFunLike.congr_fun hF (Additive.ofMul x))

private theorem UpperTheory.V.Ws.Tw.extIdeal_mon {S G : Type} [CommMonoid S] [CommGroup G] {k : Type} [Field k] [IsAlgClosed k]
    (φ : S →* G) (g : S →* kˣ) (h : ∀ a b, φ a = φ b → g a = g b) : ∃ F : G →* kˣ, ∀ x, F (φ x) = g x := by
  classical
  have key : ∀ a b c d, φ a / φ b = φ c / φ d → g a / g b = g c / g d := by
    intro a b c d e
    rw [div_eq_div_iff_mul_eq_mul] at e ⊢
    have := h (a * d) (c * b) (by rw [map_mul, map_mul, e])
    rwa [map_mul, map_mul] at this
  let Hs : Subgroup G :=
    { carrier := {x | ∃ a b, φ a / φ b = x}
      mul_mem' := by
        rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
        exact ⟨a * c, b * d, by rw [map_mul, map_mul, div_mul_div_comm]⟩
      one_mem' := ⟨1, 1, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, b, rfl⟩
        exact ⟨b, a, by rw [inv_div]⟩ }
  have hmem : ∀ x : Hs, ∃ a b, φ a / φ b = (x : G) := fun x => x.2
  choose A B hAB using hmem
  let hh : Hs →* kˣ :=
    { toFun := fun x => g (A x) / g (B x)
      map_one' := by
        have := key (A 1) (B 1) 1 1 (by rw [hAB]; simp)
        simpa using this
      map_mul' := by
        intro x y
        have := key (A (x * y)) (B (x * y)) (A x * A y) (B x * B y)
          (by rw [hAB, map_mul, map_mul, ← div_mul_div_comm, hAB, hAB]; rfl)
        show g (A (x * y)) / g (B (x * y)) = g (A x) / g (B x) * (g (A y) / g (B y))
        rw [this, map_mul, map_mul, div_mul_div_comm] }
  obtain ⟨F, hF⟩ := UpperTheory.V.Ws.Tw.extIdeal_inj Hs.subtype Subtype.val_injective hh
  refine ⟨F, fun x => ?_⟩
  let y : Hs := ⟨φ x, x, 1, by simp⟩
  have e1 : F (φ x) = hh y := hF y
  rw [e1]
  have := key (A y) (B y) x 1 (by rw [hAB]; simp [y])
  simpa [hh] using this

theorem UpperTheory.V.Ws.Tw.extIdeal :
    ∀ (K : Type) [Field K] [NumberField K] (𝔪 : Ideal (𝓞 K)), 𝔪 ≠ ⊥ → ∀ (k : Type) [Field k] [IsAlgClosed k] (g : 𝓞 K → kˣ), (∀ a b, a ≠ 0 → b ≠ 0 → IsCoprime (Ideal.span {a}) 𝔪 → IsCoprime (Ideal.span {b}) 𝔪 → g (a * b) = g a * g b) → (∀ u : (𝓞 K)ˣ, g u = 1) → ∃ f : Ideal (𝓞 K) → kˣ, (∀ I J, I ≠ ⊥ → J ≠ ⊥ → IsCoprime I 𝔪 → IsCoprime J 𝔪 → f (I * J) = f I * f J) ∧ ∀ a, a ≠ 0 → IsCoprime (Ideal.span {a}) 𝔪 → f (Ideal.span {a}) = g a := by
  intro K _ _ 𝔪 _ k _ _ g hg hu
  classical
  let ι : Ideal (𝓞 K) → (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ := fun I =>
    if hI : I = ⊥ then 1
    else Units.mk0 (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (FractionalIdeal.coeIdeal_ne_zero.mpr hI)
  have hιv : ∀ I : Ideal (𝓞 K), I ≠ ⊥ → ((ι I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) = I := by
    intro I hI
    simp only [ι, dif_neg hI, Units.val_mk0]
  have hι : ∀ I J : Ideal (𝓞 K), I ≠ ⊥ → J ≠ ⊥ → ι (I * J) = ι I * ι J := by
    intro I J hI hJ
    have hIJ : I * J ≠ ⊥ := fun h => (Ideal.mul_eq_bot.mp h).elim hI hJ
    apply Units.ext
    rw [Units.val_mul, hιv _ hIJ, hιv _ hI, hιv _ hJ, FractionalIdeal.coeIdeal_mul]
  have hspan : ∀ a : 𝓞 K, a ≠ 0 → Ideal.span {a} ≠ ⊥ :=
    fun a ha h => ha (Ideal.span_singleton_eq_bot.mp h)
  have hcopU : ∀ u : (𝓞 K)ˣ, IsCoprime (Ideal.span {(u : 𝓞 K)}) 𝔪 := by
    intro u
    rw [Ideal.span_singleton_eq_top.mpr u.isUnit, ← Ideal.one_eq_top]
    exact isCoprime_one_left
  let S : Submonoid (𝓞 K) :=
    { carrier := {a | a ≠ 0 ∧ IsCoprime (Ideal.span {a}) 𝔪}
      mul_mem' := by
        rintro a b ⟨ha, ca⟩ ⟨hb, cb⟩
        refine ⟨mul_ne_zero ha hb, ?_⟩
        rw [← Ideal.span_singleton_mul_span_singleton]
        exact ca.mul_left cb
      one_mem' := ⟨one_ne_zero, by
        rw [Ideal.span_singleton_one, ← Ideal.one_eq_top]
        exact isCoprime_one_left⟩ }
  let φ : S →* (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ :=
    { toFun := fun a => ι (Ideal.span {(a : 𝓞 K)})
      map_one' := by
        apply Units.ext
        show ((ι (Ideal.span {(1 : 𝓞 K)}) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) = 1
        rw [hιv _ (hspan 1 one_ne_zero), Ideal.span_singleton_one, FractionalIdeal.coeIdeal_top]
      map_mul' := by
        intro a b
        show ι (Ideal.span {(a : 𝓞 K) * b}) = ι (Ideal.span {(a : 𝓞 K)}) * ι (Ideal.span {(b : 𝓞 K)})
        rw [← Ideal.span_singleton_mul_span_singleton]
        exact hι _ _ (hspan _ a.2.1) (hspan _ b.2.1) }
  let g' : S →* kˣ :=
    { toFun := fun a => g a
      map_one' := by simpa using hu 1
      map_mul' := fun a b => hg a b a.2.1 b.2.1 a.2.2 b.2.2 }
  have hcompat : ∀ a b : S, φ a = φ b → g' a = g' b := by
    intro a b e
    have e2 : ((ι (Ideal.span {(a : 𝓞 K)}) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))
        = ((ι (Ideal.span {(b : 𝓞 K)}) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) := congrArg Units.val e
    rw [hιv _ (hspan _ a.2.1), hιv _ (hspan _ b.2.1)] at e2
    obtain ⟨u, hu'⟩ := Ideal.span_singleton_eq_span_singleton.mp (FractionalIdeal.coeIdeal_injective e2)
    show g a = g b
    rw [← hu', hg _ _ a.2.1 u.ne_zero a.2.2 (hcopU u), hu u, mul_one]
  obtain ⟨F, hF⟩ := UpperTheory.V.Ws.Tw.extIdeal_mon φ g' hcompat
  refine ⟨fun I => F (ι I), ?_, ?_⟩
  · intro I J hI hJ _ _
    show F (ι (I * J)) = F (ι I) * F (ι J)
    rw [hι I J hI hJ, map_mul]
  · intro a ha hca
    exact hF ⟨a, ha, hca⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusDensity.FrobDense
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Tw.frobDense :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (𝔪 : Ideal (𝓞 K)), 𝔪 ≠ ⊥ → Dense {σ : G K Ω | ∃ (w : HeightOneSpectrum (𝓞 K)) (A : ValuationSubring Ω), ¬ w.asIdeal ∣ 𝔪 ∧ IsPlaceOver A w ∧ IsFrob A (normV w) σ} := by
  intro K Ω _ _ _ _ _ 𝔪 h𝔪
  have hS : {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔪}.Finite := Ideal.finite_factors h𝔪
  refine (GlobalTheory.Published.ChebotarevDegreeOne.dense (F := K) (Ω := Ω)
    GlobalTheory.Published.chebotarevDegreeOne' hS).mono ?_
  rintro σ ⟨v, hv, _, B, hB, hσ⟩
  exact ⟨v, B, hv, hB, hσ⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusDensity.RayChar
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.Tw

open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] {C : Type} [CommGroup C]

private noncomputable def rcExt (f : Ideal (𝓞 K) → C) (I : FractionalIdeal (𝓞 K)⁰ K) : C :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), f v.asIdeal ^ FractionalIdeal.count K v I

private theorem rcExt_fin (f : Ideal (𝓞 K) → C) (I : FractionalIdeal (𝓞 K)⁰ K) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => f v.asIdeal ^ FractionalIdeal.count K v I).Finite := by
  have h := FractionalIdeal.finite_factors (K := K) I
  rw [Filter.eventually_cofinite] at h
  refine h.subset fun v hv h0 => hv ?_
  simp only [h0, zpow_zero]

private theorem rcExt_mul (f : Ideal (𝓞 K) → C) {I J : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    rcExt f (I * J) = rcExt f I * rcExt f J := by
  unfold rcExt
  rw [← finprod_mul_distrib (rcExt_fin f I) (rcExt_fin f J)]
  refine finprod_congr fun v => ?_
  rw [FractionalIdeal.count_mul K v hI hJ, zpow_add]

private theorem rcExt_one (f : Ideal (𝓞 K) → C) : rcExt f 1 = 1 := by
  unfold rcExt
  simp only [FractionalIdeal.count_one, zpow_zero, finprod_one]

private theorem rcExt_prime (f : Ideal (𝓞 K) → C) (w : HeightOneSpectrum (𝓞 K)) :
    rcExt f (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) = f w.asIdeal := by
  unfold rcExt
  rw [finprod_eq_single _ w]
  · rw [FractionalIdeal.count_self, zpow_one]
  · intro v hv
    rw [FractionalIdeal.count_maximal_coprime K v hv.symm, zpow_zero]

private theorem rcExt_coe (𝔪 : Ideal (𝓞 K)) (f : Ideal (𝓞 K) → C)
    (hm : ∀ I J, I ≠ ⊥ → J ≠ ⊥ → IsCoprime I 𝔪 → IsCoprime J 𝔪 → f (I * J) = f I * f J)
    (J : Ideal (𝓞 K)) : J ≠ ⊥ → IsCoprime J 𝔪 → rcExt f (J : FractionalIdeal (𝓞 K)⁰ K) = f J := by
  have h1 : f 1 = 1 := by
    have := hm 1 1 one_ne_zero one_ne_zero isCoprime_one_left isCoprime_one_left
    rw [mul_one] at this
    exact left_eq_mul.1 this
  refine UniqueFactorizationMonoid.induction_on_prime J (fun h => absurd rfl h) ?_ ?_
  · intro x hx _ _
    rw [isUnit_iff_eq_one.1 hx, h1, Ideal.one_eq_top, FractionalIdeal.coeIdeal_top, rcExt_one]
  · intro a p ha hp ih _ hc
    have hp0 : p ≠ ⊥ := hp.ne_zero
    rw [FractionalIdeal.coeIdeal_mul, rcExt_mul f (FractionalIdeal.coeIdeal_ne_zero.2 hp0)
      (FractionalIdeal.coeIdeal_ne_zero.2 ha), ih ha hc.of_mul_left_right,
      hm p a hp0 ha hc.of_mul_left_left hc.of_mul_left_right]
    congr 1
    exact rcExt_prime f ⟨p, Ideal.isPrime_of_prime hp, hp0⟩

private theorem rc_frac (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥) (x : K)
    (hx : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪 →
      v.valuation K x ≤ WithZero.exp (-(multiplicity v.asIdeal 𝔪 : ℤ))) :
    ∃ c d : 𝓞 K, c ≠ 0 ∧ c - 1 ∈ 𝔪 ∧ d ∈ 𝔪 ∧ x * algebraMap (𝓞 K) K c = algebraMap (𝓞 K) K d := by
  let D : Ideal (𝓞 K) :=
    { carrier := {c | ∃ d : 𝓞 K, x * algebraMap (𝓞 K) K c = algebraMap (𝓞 K) K d}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro a b ⟨d, hd⟩ ⟨e, he⟩
        exact ⟨d + e, by rw [map_add (f := _), mul_add, hd, he, map_add (f := _)]⟩
      smul_mem' := by
        rintro r a ⟨d, hd⟩
        exact ⟨r * d, by rw [smul_eq_mul, map_mul, map_mul, ← hd]; ring⟩ }
  have hsup : D ⊔ 𝔪 = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hM0 : M ≠ ⊥ := fun h => h𝔪 (le_bot_iff.1 (h ▸ le_sup_right.trans hle))
    let v : HeightOneSpectrum (𝓞 K) := ⟨M, hM.isPrime, hM0⟩
    have hv : v.asIdeal ∣ 𝔪 := Ideal.dvd_iff_le.2 (le_sup_right.trans hle)
    have h1 : v.valuation K x ≤ 1 := (hx v hv).trans (by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
    obtain ⟨n, d, hd⟩ := v.exists_primeCompl_mul_eq_of_integer x h1
    exact d.2 (hle (Ideal.mem_sup_left (show (d : 𝓞 K) ∈ D from ⟨n, hd⟩)))
  obtain ⟨c, hc, hc0, hc1⟩ : ∃ c ∈ D, c ≠ 0 ∧ c - 1 ∈ 𝔪 := by
    obtain ⟨c, hc, m, hm, e⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : 𝓞 K) ∈ D ⊔ 𝔪)
    have h1 : c - 1 ∈ 𝔪 := by
      rw [← e, sub_add_cancel_left]; exact 𝔪.neg_mem hm
    by_cases h0 : c = 0
    · obtain ⟨n, d, hd, e'⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
      have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
      refine ⟨d, ⟨n, ?_⟩, hd0, ?_⟩
      · rw [← e', div_mul_cancel₀]
        exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hd0
      · have : 𝔪 = ⊤ := by
          rw [h0, zero_add] at e
          exact (Ideal.eq_top_iff_one _).2 (e ▸ hm)
        rw [this]; trivial
    · exact ⟨c, hc, h0, h1⟩
  obtain ⟨d, hd⟩ := hc
  refine ⟨c, d, hc0, hc1, ?_, hd⟩
  rw [← Ideal.iInf_maxPowDividing_eq h𝔪, Submodule.mem_iInf]
  intro v
  rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity h𝔪]
  by_cases hv : v.asIdeal ∣ 𝔪
  · rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := K)]
    change v.valuation K (algebraMap (𝓞 K) K d) ≤ _
    rw [← hd, map_mul]
    exact (mul_le_of_le_one_right' (v.valuation_le_one c)).trans (hx v hv)
  · rw [multiplicity_eq_zero_of_not_dvd hv, pow_zero, Ideal.one_eq_top]; trivial

private theorem rc_cop {𝔪 : Ideal (𝓞 K)} {a : 𝓞 K} (h : a - 1 ∈ 𝔪) : IsCoprime (Ideal.span {a}) 𝔪 := by
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
  have : (1 : 𝓞 K) = a - (a - 1) := by ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)) (Ideal.mem_sup_right h)

private theorem rc_hom (𝔪 : GroundTheory.Global.Modulus K) (f : Ideal (𝓞 K) → C)
    (hm : ∀ I J, I ≠ ⊥ → J ≠ ⊥ → IsCoprime I 𝔪.ideal → IsCoprime J 𝔪.ideal → f (I * J) = f I * f J)
    (h1 : ∀ a : 𝓞 K, a ≠ 0 → a - 1 ∈ 𝔪.ideal → f (Ideal.span {a}) = 1) :
    ∃ F : 𝔪.IdealRayClassGroup →* C, ∀ (w : HeightOneSpectrum (𝓞 K)) (hw : ¬ w.asIdeal ∣ 𝔪.ideal),
      F (𝔪.primeClass hw) = f w.asIdeal := by
  let F₀ : 𝔪.coprimeIdeals →* C :=
    { toFun := fun I => rcExt f ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      map_one' := rcExt_one f
      map_mul' := fun I J => rcExt_mul f (Units.ne_zero _) (Units.ne_zero _) }
  have key : ∀ a : 𝓞 K, a ≠ 0 → a - 1 ∈ 𝔪.ideal →
      rcExt f (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a)) = 1 := fun a ha ha1 => by
    rw [← FractionalIdeal.coeIdeal_span_singleton, rcExt_coe 𝔪.ideal f hm _
      (by rwa [Ne, Ideal.span_singleton_eq_bot]) (rc_cop ha1), h1 a ha ha1]
  refine ⟨QuotientGroup.lift _ F₀ ?_, fun w hw => rcExt_prime f w⟩
  intro I hI
  obtain ⟨a, ha, e⟩ := 𝔪.mem_principalRay.1 hI
  have hval : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.ideal →
      v.valuation K ((a : K) - 1) ≤ WithZero.exp (-(multiplicity v.asIdeal 𝔪.ideal : ℤ)) := by
    intro v hv
    simpa [GroundTheory.Global.Modulus.exponent,
      FiniteMultiplicity.of_prime_left v.prime 𝔪.ideal_ne_bot] using (𝔪.mem_rayUnits.1 ha).1 v hv
  obtain ⟨c, d, hc0, hc1, hd, hcd⟩ := rc_frac 𝔪.ideal 𝔪.ideal_ne_bot ((a : K) - 1) hval
  have hcK : algebraMap (𝓞 K) K c ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hc0
  have e2 : (a : K) * algebraMap (𝓞 K) K c = algebraMap (𝓞 K) K (c + d) := by
    rw [map_add (f := _), ← hcd]; ring
  have hb0 : c + d ≠ 0 := fun h => by
    rw [h, map_zero] at e2
    exact mul_ne_zero a.ne_zero hcK e2
  have hb1 : c + d - 1 ∈ 𝔪.ideal := by
    rw [add_sub_right_comm]; exact Ideal.add_mem _ hc1 hd
  have h3 := key _ hb0 hb1
  rw [← e2, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    rcExt_mul f (FractionalIdeal.spanSingleton_ne_zero_iff.2 a.ne_zero)
      (FractionalIdeal.spanSingleton_ne_zero_iff.2 hcK), key c hc0 hc1, mul_one] at h3
  change rcExt f ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = 1
  rw [← e, coe_toPrincipalIdeal]
  exact h3

end UpperTheory.V.Ws.Tw

theorem UpperTheory.V.Ws.Tw.rayChar :
    ∀ (K Ω : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (𝔪 : Ideal (𝓞 K)), 𝔪 ≠ ⊥ → ∀ (C : Type) [CommGroup C] (f : Ideal (𝓞 K) → C), (∀ I J, I ≠ ⊥ → J ≠ ⊥ → IsCoprime I 𝔪 → IsCoprime J 𝔪 → f (I * J) = f I * f J) → (∀ a : 𝓞 K, a ≠ 0 → a - 1 ∈ 𝔪 → f (Ideal.span {a}) = 1) → ∃ κ : G K Ω →* C, IsOpen (κ.ker : Set (G K Ω)) ∧ ∀ w : HeightOneSpectrum (𝓞 K), ¬ w.asIdeal ∣ 𝔪 → ∀ A : ValuationSubring Ω, IsPlaceOver A w → Ine (F := K) A ≤ κ.ker ∧ ∀ σ : G K Ω, IsFrob A (normV w) σ → κ σ = f w.asIdeal := by
  intro K Ω _ _ _ _ _ _ 𝔪 h𝔪 C _ f hm h1
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  let M : GroundTheory.Global.Modulus K := ⟨𝔪, h𝔪, ∅⟩
  obtain ⟨F, hF⟩ := rc_hom M f hm h1
  haveI : NumberField (M.rayClassField Ω) := NumberField.of_module_finite K _
  haveI : Algebra.IsAlgebraic (M.rayClassField Ω) Ω := Algebra.IsAlgebraic.tower_top (K := K) _
  haveI : IsAlgClosure (M.rayClassField Ω) Ω := ⟨inferInstance, inferInstance⟩
  let r : G K Ω →* (M.rayClassField Ω ≃ₐ[K] M.rayClassField Ω) := AlgEquiv.restrictNormalHom (M.rayClassField Ω)
  let κ : G K Ω →* C := (F.comp (M.rayClassArtinEquiv Ω).symm.toMonoidHom).comp r
  have hker : r.ker ≤ κ.ker := fun σ hσ => by
    change F ((M.rayClassArtinEquiv Ω).symm (r σ)) = 1
    rw [MonoidHom.mem_ker.1 hσ, map_one, map_one]
  refine ⟨κ, ?_, fun w hw A hA => ?_⟩
  · refine Subgroup.isOpen_mono hker ?_
    have : r.ker = (M.rayClassField Ω).fixingSubgroup := IntermediateField.restrictNormalHom_ker _
    rw [this]
    exact IntermediateField.fixingSubgroup_isOpen _
  · obtain ⟨u, hu, hl⟩ := CompanionTheory.FamInh.exists_place_between (L := M.rayClassField Ω) hA
    have hI : u.asIdeal.inertia (M.rayClassField Ω ≃ₐ[K] M.rayClassField Ω) = ⊥ :=
      (CompanionTheory.FamInh.inertia_eq_bot_iff w u).2 (M.ramificationIdx_rayClassField_eq_one Ω hw u)
    refine ⟨fun σ hσ => hker ?_, fun σ hσ => ?_⟩
    · have := CompanionTheory.FamInh.res_mem_inertia hu hσ
      rw [hI] at this
      exact this
    · haveI : Finite (𝓞 (M.rayClassField Ω) ⧸ u.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ u.ne_bot
      have e : r σ = M.rayClassArtinEquiv Ω (M.primeClass hw) := by
        rw [M.rayClassArtinEquiv_primeClass Ω hw u]
        exact GroundTheory.Global.IsArithFrobAt.eq_of_inertia_eq_bot (R := 𝓞 K) hI
          (CompanionTheory.FamInh.res_isArithFrobAt hu hσ) (_root_.IsArithFrobAt.arithFrobAt _ _ _)
      change F ((M.rayClassArtinEquiv Ω).symm (r σ)) = _
      rw [e, MulEquiv.symm_apply_apply, hF]
end

