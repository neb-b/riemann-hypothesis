module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.TendstoUnderCofinite
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.ComplDefY
section
namespace KStar.Ram

open NumberField IsDedekindDomain IsLocalRing

variable {E : Type*} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

private theorem cdy_val (a : 𝓞 E) :
    Valued.v ((algebraMap (𝓞 E) (w.adicCompletionIntegers E) a : w.adicCompletionIntegers E) :
      w.adicCompletion E) = w.intValuation a := by
  rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact w.valuation_of_algebraMap a

private theorem cdy_max {π : 𝓞 E} (hπ : w.intValuation π = WithZero.exp (-1 : ℤ)) :
    maximalIdeal (w.adicCompletionIntegers E) =
      Ideal.span {algebraMap (𝓞 E) (w.adicCompletionIntegers E) π} := by
  ext y
  rw [Ideal.mem_span_singleton,
    (HeightOneSpectrum.adicCompletionIntegers.integers E w).dvd_iff_le, mem_maximalIdeal,
    mem_nonunits_iff, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  change ¬ Valued.v (y : w.adicCompletion E) = 1 ↔ Valued.v (y : w.adicCompletion E) ≤
    Valued.v ((algebraMap (𝓞 E) (w.adicCompletionIntegers E) π : w.adicCompletionIntegers E) :
      w.adicCompletion E)
  rw [cdy_val, hπ]
  have hy : Valued.v (y : w.adicCompletion E) ≤ 1 := y.2
  generalize Valued.v (y : w.adicCompletion E) = t at hy
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · rw [← WithZero.exp_log ht, ← WithZero.exp_zero, WithZero.exp_le_exp] at hy
    rw [← WithZero.exp_log ht, ← WithZero.exp_zero, WithZero.exp_le_exp, WithZero.exp_inj]
    omega

private theorem cdy_pow (π : 𝓞 E) (hπ : w.intValuation π = WithZero.exp (-1 : ℤ)) (n : ℕ) :
    w.intValuation (π ^ n) = WithZero.exp (-(n : ℤ)) := by
  rw [map_pow, hπ, ← WithZero.exp_nsmul]
  simp

private theorem cdy_mem (n : ℕ) (y : w.adicCompletionIntegers E) :
    y ∈ maximalIdeal (w.adicCompletionIntegers E) ^ n ↔
      Valued.v (y : w.adicCompletion E) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  rw [cdy_max w hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    (HeightOneSpectrum.adicCompletionIntegers.integers E w).dvd_iff_le, ← map_pow,
    ← cdy_pow w π hπ n, ← cdy_val]
  rfl

private theorem cdy_comap (n : ℕ) : (maximalIdeal (w.adicCompletionIntegers E) ^ n).comap
    (algebraMap (𝓞 E) (w.adicCompletionIntegers E)) = w.asIdeal ^ n := by
  ext a
  rw [Ideal.mem_comap, cdy_mem, cdy_val, w.intValuation_le_pow_iff_mem]

private theorem cdy_ball (n : ℕ) : ∃ r : ℝ, 0 < r ∧ ∀ x : w.adicCompletion E,
    Valued.v x ≤ WithZero.exp (-(n : ℤ)) ↔ ‖x‖ ≤ r := by
  obtain ⟨p, hp⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w
    (WithZero.exp (-(n : ℤ)))
  refine ⟨‖p‖, norm_pos_iff.2 ?_, fun x => by rw [Valued.toNormedField.norm_le_iff, hp]⟩
  rintro rfl
  rw [map_zero] at hp
  exact WithZero.exp_ne_zero hp.symm

theorem complIntegers_quotient (n : ℕ) :
    (w.asIdeal ^ n).map (algebraMap (𝓞 E) (w.adicCompletionIntegers E)) =
        maximalIdeal (w.adicCompletionIntegers E) ^ n ∧
      (maximalIdeal (w.adicCompletionIntegers E) ^ n).comap
        (algebraMap (𝓞 E) (w.adicCompletionIntegers E)) = w.asIdeal ^ n ∧
      (∀ y : w.adicCompletionIntegers E, ∃ x : 𝓞 E,
        y - algebraMap (𝓞 E) _ x ∈ maximalIdeal (w.adicCompletionIntegers E) ^ n) := by
  refine ⟨?_, cdy_comap w n, fun y => ?_⟩
  · refine le_antisymm (Ideal.map_le_iff_le_comap.2 (cdy_comap w n).ge) ?_
    obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
    rw [cdy_max w hπ, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem, ← map_pow]
    refine Ideal.mem_map_of_mem _ ?_
    rw [← w.intValuation_le_pow_iff_mem, cdy_pow w π hπ]
  · obtain ⟨r, hr, h⟩ := cdy_ball w n
    obtain ⟨t, ht⟩ := (HeightOneSpectrum.denseRange_algebraMap E w).exists_dist_lt
      (y : w.adicCompletion E) hr
    rw [dist_eq_norm] at ht
    have ht' := (h _).2 ht.le
    have hv : ∀ a : E, Valued.v (algebraMap E (w.adicCompletion E) a) = w.valuation E a :=
      fun a => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w a
    have hn : WithZero.exp (-(n : ℤ)) ≤ 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    have ht1 : w.valuation E t ≤ 1 := by
      rw [← hv, ← sub_sub_cancel (y : w.adicCompletion E) (algebraMap E (w.adicCompletion E) t)]
      exact Valuation.map_sub_le _ y.2 (ht'.trans hn)
    obtain ⟨a, ha⟩ := w.exists_valuation_sub_lt_of_integer ht1
      (Units.mk0 (WithZero.exp (-(n : ℤ))) WithZero.exp_ne_zero)
    refine ⟨a, ?_⟩
    rw [cdy_mem]
    have e : ((y - algebraMap (𝓞 E) (w.adicCompletionIntegers E) a : w.adicCompletionIntegers E) :
        w.adicCompletion E) = ((y : w.adicCompletion E) - algebraMap E (w.adicCompletion E) t) -
        algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E a - t) := by
      rw [map_sub, sub_sub, add_sub_cancel]
      rfl
    rw [e]
    refine Valuation.map_sub_le _ ht' ?_
    rw [hv]
    exact ha.le

variable (l : ℕ) [Fact l.Prime] [w.asIdeal.LiesOver (Ideal.span {(l : ℤ)})]

theorem existsUnique_padic_hom :
    ∃ (f : ℤ_[l] →+* w.adicCompletionIntegers E) (F : ℚ_[l] →+* w.adicCompletion E),
      Function.Injective f ∧ Continuous F ∧ (∀ x : ℤ_[l], F x = f x) ∧ (∀ f', f' = f) ∧
        ∀ F' : ℚ_[l] →+* w.adicCompletion E, Continuous F' → F' = F := by
  let p : Nat.Primes := ⟨l, Fact.out⟩
  let u : HeightOneSpectrum (𝓞 ℚ) := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p
  have hl : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    have : (l : ℤ) ∈ Ideal.span {(l : ℤ)} := Ideal.mem_span_singleton_self _
    rw [Ideal.mem_of_liesOver w.asIdeal] at this
    simpa using this
  have hu : u.asIdeal = Ideal.span {((l : ℕ) : 𝓞 ℚ)} := by
    change (Ideal.span {(l : ℤ)}).map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm = _
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have : w.asIdeal.LiesOver u.asIdeal := by
    refine ⟨u.isMaximal.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) ?_⟩
    rw [hu, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hl
  let F : ℚ_[l] →+* w.adicCompletion E :=
    (KStar.Choice.complMap u w).comp (Padic.adicCompletionEquiv (𝓞 ℚ) p).toRingEquiv.toRingHom
  have hF : Continuous F :=
    (KStar.Choice.continuous_complMap u w).comp (Padic.adicCompletionEquiv (𝓞 ℚ) p).continuous
  have hm : ∀ x : ℤ_[l], F.comp PadicInt.Coe.ringHom x ∈ w.adicCompletionIntegers E := by
    intro x
    refine KStar.Choice.complMap_mem u w ?_
    have := (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) p x).2
    rw [PadicInt.coe_adicCompletionIntegersEquiv_apply] at this
    exact this
  let f : ℤ_[l] →+* w.adicCompletionIntegers E :=
    (F.comp PadicInt.Coe.ringHom).codRestrict (w.adicCompletionIntegers E) hm
  refine ⟨f, F, fun x y h => ?_, hF, fun x => rfl, fun f' => ?_, fun F' hF' => ?_⟩
  · exact Subtype.ext (F.injective (congrArg Subtype.val h))
  · have hlm : ((l : ℕ) : w.adicCompletionIntegers E) ∈
        maximalIdeal (w.adicCompletionIntegers E) := by
      have h1 := cdy_comap w 1
      rw [pow_one, pow_one] at h1
      rw [← h1, Ideal.mem_comap, map_natCast] at hl
      exact hl
    refine RingHom.ext fun x => ?_
    rw [← sub_eq_zero, ← Ideal.mem_bot,
      ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (w.adicCompletionIntegers E))
        (maximalIdeal.isMaximal _).ne_top, Ideal.mem_iInf]
    intro k
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec k x)
    have hx : x = (x.appr k : ℤ_[l]) + (l : ℤ_[l]) ^ k * z := by rw [← hz]; ring
    have : f' x - f x = (l : w.adicCompletionIntegers E) ^ k * (f' z - f z) := by
      conv_lhs => rw [hx]
      simp only [map_add (f := _), map_mul, map_pow, map_natCast]
      ring
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlm k)
  · refine DFunLike.coe_injective ((Padic.denseRange_ratCast l).equalizer hF' hF ?_)
    funext q
    simp only [Function.comp_apply, map_ratCast]

end KStar.Ram
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.ConductorLocalPartDvdIff
section
namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N] (l : ℕ) [Fact l.Prime]

private lemma unitsMap_eq_one_iff_modEq {d : ℕ} (h : d ∣ N) (x : (ZMod N)ˣ) :
    ZMod.unitsMap h x = 1 ↔ (x : ZMod N).val ≡ 1 [MOD d] := by
  rw [← Units.val_inj, ZMod.unitsMap_val, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val]
  simp

private lemma crt_fst (x : ZMod N) :
    (crtEquiv N l x).1 = ZMod.castHom (Nat.ordProj_dvd N l) (ZMod (ordProj[l] N)) x :=
  RingHom.congr_fun (RingHom.ext_zmod
    ((RingHom.fst _ _).comp (crtEquiv N l).toRingHom)
    (ZMod.castHom (Nat.ordProj_dvd N l) (ZMod (ordProj[l] N)))) x

private lemma crt_snd (x : ZMod N) :
    (crtEquiv N l x).2 = ZMod.castHom (Nat.ordCompl_dvd N l) (ZMod (ordCompl[l] N)) x :=
  RingHom.congr_fun (RingHom.ext_zmod
    ((RingHom.snd _ _).comp (crtEquiv N l).toRingHom)
    (ZMod.castHom (Nat.ordCompl_dvd N l) (ZMod (ordCompl[l] N)))) x

private lemma localUnits_val (u : (ZMod (ordProj[l] N))ˣ) :
    ((localUnits N l u : (ZMod N)ˣ) : ZMod N) =
      (crtEquiv N l).symm ((u : ZMod (ordProj[l] N)), 1) := rfl

private lemma proj_localUnits (u : (ZMod (ordProj[l] N))ˣ) :
    ZMod.unitsMap (Nat.ordProj_dvd N l) (localUnits N l u) = u := by
  apply Units.ext
  have h := crt_fst l ((localUnits N l u : (ZMod N)ˣ) : ZMod N)
  rw [localUnits_val, RingEquiv.apply_symm_apply] at h
  exact h.symm

private lemma compl_localUnits (u : (ZMod (ordProj[l] N))ˣ) :
    ZMod.unitsMap (Nat.ordCompl_dvd N l) (localUnits N l u) = 1 := by
  apply Units.ext
  have h := crt_snd l ((localUnits N l u : (ZMod N)ˣ) : ZMod N)
  rw [localUnits_val, RingEquiv.apply_symm_apply] at h
  exact h.symm

private lemma localUnits_proj (x : (ZMod N)ˣ)
    (hx : ZMod.unitsMap (Nat.ordCompl_dvd N l) x = 1) :
    localUnits N l (ZMod.unitsMap (Nat.ordProj_dvd N l) x) = x := by
  apply Units.ext
  rw [localUnits_val, RingEquiv.symm_apply_eq]
  apply Prod.ext
  · rw [crt_fst]; rfl
  · rw [crt_snd]; exact (congrArg Units.val hx).symm

theorem localUnits_spec :
    Function.Injective (localUnits N l) ∧ (localUnits N l).range = inertiaUnits N l ∧
      ∀ u, ZMod.unitsMap (Nat.ordProj_dvd N l) (localUnits N l u) = u := by
  refine ⟨Function.LeftInverse.injective (proj_localUnits l), ?_, proj_localUnits l⟩
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact compl_localUnits l u
  · intro hx
    exact ⟨_, localUnits_proj l x hx⟩

private lemma localPart_toUnitHom (ψ : DirichletCharacter ℂ N) :
    MulChar.toUnitHom (localPart N l ψ) = (MulChar.toUnitHom ψ).comp (localUnits N l) := by
  ext u
  simp [localPart]

private lemma unitsMap_trans {a b c : ℕ} (hab : a ∣ b) (hbc : b ∣ c) (x : (ZMod c)ˣ) :
    ZMod.unitsMap hab (ZMod.unitsMap hbc x) = ZMod.unitsMap (hab.trans hbc) x := by
  rw [← ZMod.unitsMap_comp hab hbc]; rfl

private lemma conductor_localPart_dvd_iff (ψ : DirichletCharacter ℂ N) (t : ℕ)
    (ht : t ≤ N.factorization l) :
    (localPart N l ψ).conductor ∣ l ^ t ↔ condExp l ψ ≤ t := by
  have hl : l.Prime := Fact.out
  have hN : N ≠ 0 := NeZero.ne N
  have : NeZero (ordProj[l] N) := ⟨(Nat.ordProj_pos N l).ne'⟩
  have h1 : l ^ t ∣ ordProj[l] N := pow_dvd_pow l ht
  have h2 : l ^ t * ordCompl[l] N ∣ N := by
    conv_rhs => rw [← Nat.ordProj_mul_ordCompl_eq_self N l]
    exact Nat.mul_dvd_mul_right h1 _
  have hcop : (l ^ t).Coprime (ordCompl[l] N) :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl hN)
  have hker : ∀ x : (ZMod N)ˣ, ZMod.unitsMap h2 x = 1 ↔
      ZMod.unitsMap (h1.trans (Nat.ordProj_dvd N l)) x = 1 ∧
        ZMod.unitsMap (Nat.ordCompl_dvd N l) x = 1 := by
    intro x
    simp only [unitsMap_eq_one_iff_modEq]
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).symm
  have key : (localPart N l ψ).conductor ∣ l ^ t ↔ ψ.conductor ∣ l ^ t * ordCompl[l] N := by
    rw [← mem_conductorSet_iff_conductor_dvd _ h1, ← mem_conductorSet_iff_conductor_dvd _ h2,
      mem_conductorSet_iff, mem_conductorSet_iff, factorsThrough_iff_ker_unitsMap h1,
      factorsThrough_iff_ker_unitsMap h2, localPart_toUnitHom]
    constructor
    · intro h x hx
      rw [MonoidHom.mem_ker, hker] at hx
      have := h (x := ZMod.unitsMap (Nat.ordProj_dvd N l) x)
        (by rw [MonoidHom.mem_ker, unitsMap_trans]; exact hx.1)
      rwa [MonoidHom.mem_ker, MonoidHom.comp_apply, localUnits_proj l x hx.2] at this
    · intro h u hu
      rw [MonoidHom.mem_ker] at hu
      refine h (x := localUnits N l u) ?_
      rw [MonoidHom.mem_ker, hker]
      refine ⟨?_, compl_localUnits l u⟩
      rw [← unitsMap_trans h1 (Nat.ordProj_dvd N l), proj_localUnits, hu]
  rw [key, condExp]
  have hc : ψ.conductor ≠ 0 := conductor_ne_zero ψ
  have hcN : ψ.conductor ∣ N := conductor_dvd_level ψ
  have hN' : ordCompl[l] N ≠ 0 := (Nat.ordCompl_pos l hN).ne'
  have hlt : l ^ t ≠ 0 := pow_ne_zero _ hl.ne_zero
  constructor
  · intro h
    have := (Nat.factorization_le_iff_dvd hc (mul_ne_zero hlt hN')).2 h l
    rw [Nat.factorization_mul hlt hN', Nat.factorization_ordCompl, hl.factorization_pow] at this
    simpa using this
  · intro h
    rw [← Nat.ordProj_mul_ordCompl_eq_self ψ.conductor l]
    exact Nat.mul_dvd_mul (pow_dvd_pow l h) (Nat.ordCompl_dvd_ordCompl_of_dvd hcN l)

theorem localPart_eq_one_iff (ψ : DirichletCharacter ℂ N) :
    (localPart N l ψ = 1 ↔ ∀ u ∈ inertiaUnits N l, ψ (u : ZMod N) = 1) ∧
      (localPart N l ψ = 1 ↔ ¬ l ∣ ψ.conductor) := by
  have hl : l.Prime := Fact.out
  have : NeZero (ordProj[l] N) := ⟨(Nat.ordProj_pos N l).ne'⟩
  constructor
  · rw [← (localUnits_spec l).2.1]
    constructor
    · rintro h _ ⟨u, rfl⟩
      have := congrArg (fun χ : DirichletCharacter ℂ (ordProj[l] N) =>
        χ (u : ZMod (ordProj[l] N))) h
      simpa [localPart] using this
    · intro h
      ext u
      simpa [localPart] using h _ ⟨u, rfl⟩
  · have := conductor_localPart_dvd_iff l ψ 0 (Nat.zero_le _)
    rw [pow_zero, Nat.dvd_one, Nat.le_zero] at this
    rw [eq_one_iff_conductor_eq_one, this, condExp,
      hl.dvd_iff_one_le_factorization (conductor_ne_zero ψ)]
    omega

end KStar.Ram
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.IsImagQuad
section
namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ}

def IsImagQuad (ψ : DirichletCharacter ℂ N) (d : ℕ) : Prop :=
  ψ ^ 2 = 1 ∧ ψ.Odd ∧ ψ.conductor = d

end KStar.Ram
end

