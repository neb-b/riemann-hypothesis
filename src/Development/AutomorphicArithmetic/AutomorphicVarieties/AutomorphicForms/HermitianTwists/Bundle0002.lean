module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.RepNewformOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0013
public import Mathlib.NumberTheory.ModularForms.NormTrace

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.CuspZero
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd
  UpperTheory.V.Br CongruenceSubgroup

private theorem cusp_zero (N : ℕ) [NeZero N] (f : CuspForm (Gamma1 N) ((0 : ℕ) : ℤ)) : f = 0 := by
  obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero (𝒢 := (Gamma1 N : Subgroup (GL (Fin 2) ℝ)))
    { toFun := f, holo' := f.holo', slash_action_eq' := f.slash_action_eq',
      bdd_at_cusps' := fun hc g hg => (f.zero_at_cusps' hc g hg).isBoundedAtImInfty }
  have hc' : (f : UpperHalfPlane → ℂ) = Function.const UpperHalfPlane c := hc
  have hz : UpperHalfPlane.IsZeroAtImInfty (f : UpperHalfPlane → ℂ) := CuspFormClass.zero_at_infty f
  rw [hc'] at hz
  have h0 : c = 0 := tendsto_nhds_unique tendsto_const_nhds hz
  ext z
  rw [hc', h0]
  rfl

theorem UpperTheory.V.Af.Rn.noLow :
    UpperTheory.V.Sd.Wc.CentChar → UpperTheory.V.Af.Rn.NoLow := by
  intro hC π hπ
  obtain ⟨N, ψ, ν, hN, hν, φ, hφ, h0, hlow, hfix⟩ := levelVec 0 π hπ
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨ω, hω, -⟩ := hC ℚ (π.twist ν)
  have hc := fun z g => hω z φ hφ g
  obtain ⟨χ, hχ⟩ := charOf N hN ω φ h0 hlow.one hfix hc
  have hcusp := (π.twist ν).cusp φ hφ
  obtain ⟨f, -, hL⟩ := deadel 0 N hN χ ω hχ φ hcusp hlow hfix hc
  obtain rfl := cusp_zero N f
  refine h0 (Subtype.ext (funext fun g => ?_))
  obtain ⟨γ, h, u, hu, rfl⟩ := decomp N hN g
  rw [hL γ h u hu]
  simp [nsl]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.EigOfLow
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd
  UpperTheory.V.Br CongruenceSubgroup

theorem UpperTheory.V.Af.Rn.eigOfLow :
    UpperTheory.V.Sd.Wc.CentChar → UpperTheory.V.Af.Rn.EigOfLow := by
  intro hCC k hk1 π hlw
  obtain ⟨N, ψ, ν, hN, hν, φ, hφ, h0, hlow, hfix⟩ := levelVec k π hlw
  have : NeZero N := ⟨by omega⟩
  obtain ⟨ω, hω, -⟩ := hCC ℚ (π.twist ν)
  have hc := fun z g => hω z φ hφ g
  obtain ⟨χ, hχ⟩ := charOf N hN ω φ h0 hlow.one hfix hc
  have hcusp := (π.twist ν).cusp φ hφ
  obtain ⟨f, hf, hL⟩ := deadel k N hN χ ω hχ φ hcusp hlow hfix hc
  have hf0 : f ≠ 0 := by
    rintro rfl
    refine h0 (Subtype.ext (funext fun g => ?_))
    obtain ⟨γ, h, u, hu, rfl⟩ := decomp N hN g
    rw [hL γ h u hu]
    simp [nsl]
  have hhol : IsHol k (lev N) ω φ := ⟨hcusp.1, fun w u hu => hfix _ (kLocal N hN w u hu), hc, hlow.wt, hlow.low⟩
  obtain ⟨g, hg⟩ := eigEx N k hk1 χ f hf hf0 fun p => Classical.epsilon (IsEigAt k χ f p)
  have : NeZero (N * N) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne N)⟩
  have huntwist :
      ∃ (χ' : DirichletCharacter ℂ (N * N)) (g' : Eigenform k (N * N) χ'),
        ∀ p : ℕ, p.Prime → ¬ p ∣ N →
          g'.a p * ψ (p : ZMod N) = g.a p ∧
            χ' (p : ZMod (N * N)) * ψ (p : ZMod N) ^ 2 = χ (p : ZMod N) := by
    obtain ⟨h, hc, hn⟩ := clTwist N k χ ψ⁻¹ g.f g.char
    have ht0 : h ≠ 0 := by
      rintro rfl
      have := hn 1
      rw [g.one, Nat.cast_one, map_one, mul_one] at this
      simp [coef, UpperHalfPlane.qExpansion_zero] at this
    obtain ⟨g', hg'⟩ := eigEx (N * N) k hk1 _ h hc ht0 fun p => ψ⁻¹ (p : ZMod N) * g.a p
    refine ⟨_, g', fun p hp hd => ?_⟩
    have hu : IsUnit (p : ZMod (N * N)) :=
      (ZMod.isUnit_prime_iff_not_dvd hp).2 fun e => hd ((hp.dvd_mul.1 e).elim id id)
    have hu' : IsUnit (p : ZMod N) := (ZMod.isUnit_prime_iff_not_dvd hp).2 hd
    have e : DirichletCharacter.changeLevel (dvd_mul_right N N) (χ * ψ⁻¹ ^ 2) (p : ZMod (N * N)) =
        χ (p : ZMod N) * ψ⁻¹ (p : ZMod N) ^ 2 := by
      have := DirichletCharacter.changeLevel_eq_cast_of_dvd (χ * ψ⁻¹ ^ 2) (dvd_mul_right N N) hu.unit
      rw [IsUnit.unit_spec, ZMod.cast_natCast (dvd_mul_right N N)] at this
      rw [this, MulChar.mul_apply, MulChar.pow_apply' _ two_ne_zero]
    have e1 : ψ⁻¹ (p : ZMod N) * ψ (p : ZMod N) = 1 := by
      rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply hu']
    constructor
    · rw [hg' p hp fun n h1 => ?_]
      · linear_combination g.a p * e1
      have := g.eig p hp n h1
      rw [e, hn, hn n, Nat.cast_mul, map_mul, Eigenform.a]
      by_cases hpn : p ∣ n
      · obtain ⟨m, rfl⟩ := hpn
        rw [ite_eq_left (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hp.pos] at this ⊢
        rw [hn, Nat.cast_mul, map_mul]
        linear_combination ψ⁻¹ (p : ZMod N) * (ψ⁻¹ (p : ZMod N) * ψ⁻¹ (m : ZMod N)) * this
      · rw [ite_eq_right hpn] at this ⊢
        linear_combination ψ⁻¹ (p : ZMod N) * ψ⁻¹ (n : ZMod N) * this
    · rw [e]
      linear_combination χ (p : ZMod N) * (ψ⁻¹ (p : ZMod N) * ψ (p : ZMod N) + 1) * e1
  obtain ⟨χ', g', hg'⟩ := huntwist
  have hndvd : ∀ᶠ w : Pl ℚ in Filter.cofinite, ¬ normV w ∣ N := by
    have hspan : Ideal.span {(N : 𝓞 ℚ)} ≠ 0 := by simpa using NeZero.ne N
    refine Filter.eventually_cofinite.2 ((Ideal.finite_factors hspan).subset fun w hw => ?_)
    obtain ⟨c, rfl⟩ := not_not.1 hw
    refine Ideal.dvd_span_singleton.2 ?_
    rw [Nat.cast_mul, (places w).2.1]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  refine ⟨N * N, inferInstance, χ', g', ?_⟩
  filter_upwards [Gk.satAE ℚ 2 π, hndvd,
    Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.unr_ae_and_level ℚ ν).1] with w ⟨B, hB⟩ hw hu
  obtain ⟨α, β, rfl⟩ := Multiset.card_eq_two.1 (TR.CuspSub.HasSat.card hB)
  refine ⟨α, β, hB, ?_⟩
  have hT := TR.CuspSub.HasSat.twist hB hu
  have hp := (places w).1
  have hlevel : K1 w 0 = GlobalTheory.LFun.KGL w (n := 2) := by
    ext x
    refine ⟨fun ⟨u, _, e⟩ => ⟨u, e⟩, fun ⟨u, e⟩ => ⟨u, ?_, e⟩⟩
    have : Subsingleton (w.adicCompletionIntegers ℚ ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers ℚ) ^ 0) :=
      Ideal.Quotient.subsingleton_iff.2 (by simp)
    exact Subsingleton.elim _ _
  have hv : GlobalTheory.LFun.IsSatVecGL w (locSm ℚ w) φ {α * ν.val w, β * ν.val w} :=
    (hT.2 ⟨φ, hφ⟩ (GlobalTheory.LGrp.mem_fixed.2 fun u hu => Subtype.ext (hfix _ (kLocal N hN w u (by
      rwa [(places w).2.2.2 N hN hw, hlevel])))) fun e => h0 (congrArg Subtype.val e)).map
      (π.twist ν).V.subtype (fun _ _ => rfl) h0
  obtain ⟨h1, h2⟩ := eigOf k N hk1 hN χ ω hχ f φ hL hhol w _ _ hw hv
  have h3 := Classical.epsilon_spec (p := IsEigAt k χ f (normV w)) ⟨_, h1⟩
  have heig {a b : ℂ} (ha : IsEigAt k χ f (normV w) a) (hb : IsEigAt k χ f (normV w) b) : a = b := by
    by_contra h
    exact hf0 ((finDim N k).2 f fun n hn =>
      (mul_eq_zero.1 (show (a - b) * coef f n = 0 by linear_combination hb n hn - ha n hn)).resolve_left
        (sub_ne_zero.2 h))
  have h4 := (hg _ hp h3).trans (heig h3 h1)
  obtain ⟨h5, h6⟩ := hg' _ hp hw
  have h7 := (charVal N hN ψ ν hν).2 w hw
  have h8 : ψ (normV w : ZMod N) ≠ 0 := h7 ▸ Units.ne_zero _
  simp only [Units.val_mul, h7] at h2 h4 ⊢
  constructor
  · refine mul_right_cancel₀ h8 ?_
    rw [h5, h4]; ring
  · refine mul_right_cancel₀ (pow_ne_zero 2 h8) ?_
    rw [h6, ← h2]; ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.EvPl
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V.Af UpperTheory.V.Af.Nf in
theorem UpperTheory.V.Af.Rn.evPl :
    UpperTheory.V.Af.Rn.EvPl := by
  have hinj : Function.Injective fun w : HeightOneSpectrum (𝓞 ℚ) => normV w := fun v w h =>
    HeightOneSpectrum.ext (by rw [(places v).2.1, (places w).2.1, show normV v = normV w from h])
  refine ⟨fun P => ⟨fun h => ?_, fun h => ?_⟩, fun M hM => ?_⟩
  · refine Filter.eventually_cofinite.2
      (((Filter.eventually_cofinite.1 h).image fun w => normV w).subset fun p hp => ?_)
    obtain ⟨hp, hne⟩ := Classical.not_imp.1 hp
    have hex : ∃ w : HeightOneSpectrum (𝓞 ℚ), normV w = p := by
      have hprime : Prime (p : 𝓞 ℚ) := by
        have e : (p : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (p : ℤ) := by simp
        rw [e]
        exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr
          (Nat.prime_iff_prime_int.mp hp)
      let w : HeightOneSpectrum (𝓞 ℚ) :=
        ⟨Ideal.span {(p : 𝓞 ℚ)}, (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime,
          by rw [Ne, Ideal.span_singleton_eq_bot]; exact hprime.ne_zero⟩
      refine ⟨w, (places w).2.2.1.symm.trans ?_⟩
      change Ideal.absNorm (Ideal.span {(p : 𝓞 ℚ)}) = p
      rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank]
      simp
    obtain ⟨w, rfl⟩ := hex
    exact ⟨w, hne, rfl⟩
  · filter_upwards [hinj.tendsto_cofinite.eventually h] with w hw
    exact hw (places w).1
  · filter_upwards [hinj.tendsto_cofinite.eventually (Set.finite_le_nat M).eventually_cofinite_notMem] with w hw
    exact fun h => hw (Nat.le_of_dvd hM h)
end

