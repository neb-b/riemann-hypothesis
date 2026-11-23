module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0153
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0173
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.SerEqZmOfParity

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ChiQuad
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open UpperTheory.V.Z.Kato.Joint Polynomial

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem cont_of_apply [IsAlgClosure ℚ Ω] {Y : Type} [TopologicalSpace Y] (ζ : Ω) (f : G ℚ Ω → Y)
    (h : ∀ s t : G ℚ Ω, s ζ = t ζ → f s = f t) : Continuous f := by
  have halg : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral ℚ ζ := (Algebra.IsAlgebraic.isAlgebraic ζ).isIntegral
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ}) := IntermediateField.adjoin.finiteDimensional hint
  have hopen : IsOpen ((IntermediateField.adjoin ℚ {ζ}).fixingSubgroup : Set (Ω ≃ₐ[ℚ] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_eventually_eq]
  intro s
  have hc : Continuous fun y : Ω ≃ₐ[ℚ] Ω => s⁻¹ * y := continuous_const.mul continuous_id
  have hmem : s⁻¹ * s ∈ ((IntermediateField.adjoin ℚ {ζ}).fixingSubgroup : Set (Ω ≃ₐ[ℚ] Ω)) := by
    simp only [inv_mul_cancel]
    exact Subgroup.one_mem _
  filter_upwards [hc.continuousAt.preimage_mem_nhds (hopen.mem_nhds hmem)] with y hy
  apply h
  have hz : (s⁻¹ * y) ζ = ζ := by
    have := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hy ζ (IntermediateField.mem_adjoin_simple_self ℚ ζ)
    exact this
  have : s ((s⁻¹ * y) ζ) = s ζ := by rw [hz]
  simpa using this

private theorem root_pow {M n : ℕ} (hM : M ≠ 0) {B : ValuationSubring Ω} {v : Pl} (hB : IsPlaceOver B v)
    (hv : ((M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) {s : G ℚ Ω} {ζ : Ω} (hζ : ζ ^ M = 1)
    (hs : ∀ x, B.valuation x ≤ 1 → B.valuation (s x - x ^ n) < 1) : s ζ = ζ ^ n := by
  have hN : ¬ B.valuation (M : Ω) < 1 := fun h => hv ((hB _).1 (by simpa using h))
  refine eq_of_pow_eq_one B hN ?_ ?_ (hs ζ (valuation_eq_one_of_pow_eq_one B hM hζ).le)
  · rw [← map_pow, hζ, map_one]
  · rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]

private theorem expo_eq {M a b : ℕ} [NeZero M] {ζ : Ω} (hζ : IsPrimitiveRoot ζ M) (h : ζ ^ a = ζ ^ b) :
    (a : ZMod M) = b := by
  obtain ⟨u, rfl⟩ := hζ.isUnit (NeZero.ne M)
  rw [ZMod.natCast_eq_natCast_iff, hζ.eq_orderOf, orderOf_units]
  apply pow_eq_pow_iff_modEq.mp
  exact Units.ext (by simpa using h)

private theorem det_of_charpoly {K : Type} [Field K] (ι : K ≃+* ℂ) {A : Matrix (Fin 2) (Fin 2) K} {a d : ℂ}
    (h : A.charpoly.map ι.toRingHom = X ^ 2 - C a * X + C d) : ι A.det = d := by
  have h0 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p 0) h
  simp only [Polynomial.coeff_map] at h0
  rw [Matrix.det_eq_sign_charpoly_coeff]
  simp at h0 ⊢
  exact h0

private theorem exists_aut_pow [IsAlgClosure ℚ Ω] {n c : ℕ} (hn : n ≠ 0) (hc : c.Coprime n) :
    ∃ s : G ℚ Ω, ∀ z : Ω, z ^ n = 1 → s z = z ^ c := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).mp inferInstance
  haveI : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.mpr hn⟩
  haveI : NeZero n := ⟨hn⟩
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic n Ω) (by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr hpos).ne')
  have hprim : IsPrimitiveRoot ζ n := Polynomial.isRoot_cyclotomic_iff.mp hζ
  have hprim' : IsPrimitiveRoot (ζ ^ c) n := hprim.pow_of_coprime c hc
  have hev : ∀ μ : Ω, IsPrimitiveRoot μ n → Polynomial.aeval μ (Polynomial.cyclotomic n ℚ) = 0 := by
    intro μ hμ
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
    exact hμ.isRoot_cyclotomic hpos
  have hmin : Polynomial.cyclotomic n ℚ = minpoly ℚ ζ :=
    minpoly.eq_of_irreducible_of_monic (Polynomial.cyclotomic.irreducible_rat hpos) (hev ζ hprim)
      (Polynomial.cyclotomic.monic n ℚ)
  have halg : IsAlgebraic ℚ ζ := ⟨_, Polynomial.cyclotomic_ne_zero n ℚ, hev ζ hprim⟩
  have hroot : Polynomial.aeval (ζ ^ c) (minpoly ℚ ζ) = 0 := by
    rw [← hmin]
    exact hev _ hprim'
  obtain ⟨s, hs⟩ := minpoly.exists_algEquiv_of_root' halg hroot
  refine ⟨s, fun z hz => ?_⟩
  obtain ⟨i, -, rfl⟩ := hprim.eq_pow_of_pow_eq_one hz
  rw [map_pow, hs, ← pow_mul, ← pow_mul, mul_comm]

end

theorem UpperTheory.V.Z.Kato.Joint.chiQuad :
    UpperTheory.V.Z.Kato.Joint.ChiQuad := by
  unfold UpperTheory.V.Z.Kato.Joint.ChiQuad
  intro l _ Ω _ _ _ ι e S A W g χ hN hK hl hAtt d hd
  have hlp : Nat.Prime l := Fact.out
  have hM0 : g.M ≠ 0 := g.pos.ne'
  have hN0 : l * g.M ≠ 0 := mul_ne_zero hlp.ne_zero hM0
  haveI : NeZero g.M := ⟨hM0⟩
  haveI : NeZero (l * g.M) := ⟨hN0⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ (l * g.M) := by
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).mp inferInstance
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (l * g.M) Ω) (by
      rw [Polynomial.degree_cyclotomic]
      exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN0)).ne')
    exact ⟨z, Polynomial.isRoot_cyclotomic_iff.mp hz⟩
  have hζM : IsPrimitiveRoot (ζ ^ l) g.M := hζ.pow (Nat.pos_of_ne_zero hN0) rfl
  have hζMN : (ζ ^ l) ^ (l * g.M) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hroot : ∀ s : G ℚ Ω, ∃ i : ℕ, s (ζ ^ l) = (ζ ^ l) ^ i := by
    intro s
    have h1 : (s (ζ ^ l)) ^ g.M = 1 := by rw [← map_pow, hζM.pow_eq_one, map_one]
    obtain ⟨i, -, hi⟩ := hζM.eq_pow_of_pow_eq_one h1
    exact ⟨i, hi.symm⟩
  choose u hu using hroot
  have hsame : ∀ s t : G ℚ Ω, s ζ = t ζ → ∀ z : Ω, z ^ (l * g.M) = 1 → s z = t z := by
    intro s t hst z hz
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
    rw [map_pow, map_pow, hst]
  have hχ : ∀ s t : G ℚ Ω, s ζ = t ζ → χ s = χ t := by
    intro s t hst
    have h1 : χ (t⁻¹ * s) = 1 := by
      apply hK
      intro z hz
      have h2 := hsame s t hst z (by rw [pow_mul, hz, one_pow])
      rw [AlgEquiv.mul_apply, h2]
      exact t.symm_apply_apply z
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  have hu_eq : ∀ s t : G ℚ Ω, s ζ = t ζ → (u s : ZMod g.M) = u t := by
    intro s t hst
    apply expo_eq hζM
    rw [← hu, ← hu]
    exact hsame s t hst _ hζMN
  let f : G ℚ Ω → ℂ := fun s => ι (χ s : Qbar l) ^ 4 * g.χ (u s : ZMod g.M) ^ 2
  have hf : Continuous f := cont_of_apply ζ f (fun s t h => by simp only [f, hχ s t h, hu_eq s t h])
  have hcof : ∀ᶠ w : Pl in Filter.cofinite, ((l * g.M : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
    rw [Filter.eventually_cofinite]
    refine (Ideal.finite_factors (I := Ideal.span {((l * g.M : ℕ) : 𝓞 ℚ)}) ?_).subset ?_
    · rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hN0
    · intro w hw
      simp only [Set.mem_setOf_eq, not_not] at hw ⊢
      exact Ideal.dvd_span_singleton.mpr hw
  have hev := hcof.and hAtt.2
  have hfeq : f = fun _ => 1 := by
    refine GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob GlobalTheory.Published.chebotarevDegreeOne'
      (Filter.eventually_cofinite.mp hev) hf continuous_const ?_
    intro v hv _ B hB σ hσ
    obtain ⟨hvN, hvA⟩ := not_not.mp hv
    have hvM : ((g.M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hvN (by push_cast; exact Ideal.mul_mem_left _ _ h)
    have hvl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hvN (by push_cast; exact Ideal.mul_mem_right _ _ h)
    have hcp := (hvA B hB).2 σ hσ
    have hdet := det_of_charpoly (a := g.a (normV v)) (d := g.χ (normV v) * (normV v : ℂ) ^ (2 * e + 1 - 1)) ι hcp
    have hfr : σ (ζ ^ l) = (ζ ^ l) ^ normV v := root_pow hM0 hB hvM hζM.pow_eq_one hσ.2
    have hus : (u σ : ZMod g.M) = normV v := expo_eq hζM (by rw [← hu, hfr])
    have hcz := cycZ_of_isFrob hvl hB hσ
    have hcyc : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV v : Qbar l) := by
      simp [cycBar, hcz]
    have hd2 : (dt W σ) ^ 2 = 1 := by
      have := congrArg (fun φ => φ σ) hN.det2
      simpa using this
    rw [tw_val, Matrix.det_smul] at hdet
    simp only [Fintype.card_fin, map_inv, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.zpow_apply] at hdet
    have hw : ((↑((W σ)⁻¹) : Matrix (Fin 2) (Fin 2) (Qbar l))).det = (((dt W σ)⁻¹ : (Qbar l)ˣ) : Qbar l) := by
      change ((Matrix.GeneralLinearGroup.det ((W σ)⁻¹) : (Qbar l)ˣ) : Qbar l) = _
      rw [map_inv]
      rfl
    rw [hw] at hdet
    simp only [mul_inv_rev, inv_inv, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val,
      Units.val_inv_eq_inv_val, map_mul, map_pow, map_inv₀, map_zpow₀, hcyc, map_natCast] at hdet
    set a := ι ((χ σ : (Qbar l)ˣ) : Qbar l) with ha_def
    set δ := ι ((dt W σ : (Qbar l)ˣ) : Qbar l) with hδ_def
    have ha : a ≠ 0 := (map_ne_zero ι).mpr (χ σ).ne_zero
    have hδ : δ ^ 2 = 1 := by
      have := congrArg (fun x : (Qbar l)ˣ => ι (x : Qbar l)) hd2
      simpa [hδ_def] using this
    have hδ0 : δ ≠ 0 := (map_ne_zero ι).mpr (dt W σ).ne_zero
    have hp : ((normV v : ℕ) : ℂ) ≠ 0 := by
      have h1 : ι ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) ≠ 0 := (map_ne_zero ι).mpr (cycBar ℚ Ω l σ).ne_zero
      rwa [hcyc, map_natCast] at h1
    rw [Nat.add_sub_cancel, zpow_neg, inv_inv, zpow_natCast] at hdet
    have hχp : g.χ (normV v : ZMod g.M) = δ * a⁻¹ ^ 2 := by
      apply mul_right_cancel₀ (pow_ne_zero (2 * e) hp)
      rw [← hdet]
      field_simp
      try ring
    show a ^ 4 * g.χ (u σ : ZMod g.M) ^ 2 = 1
    rw [hus, hχp, mul_pow, hδ]
    field_simp
    try ring
  obtain ⟨c, hc1, hcd⟩ := Nat.chineseRemainder ((Nat.Prime.coprime_iff_not_dvd hlp).mpr hl) 1 d
  have hcop : c.Coprime (l * g.M) := by
    apply Nat.Coprime.mul_right
    · have := hc1.gcd_eq
      rw [Nat.gcd_one_left] at this
      exact this
    · have := hcd.gcd_eq
      show c.gcd g.M = 1
      rw [this]
      exact hd
  obtain ⟨s, hs⟩ := exists_aut_pow (Ω := Ω) hN0 hcop
  have hχs : χ s = 1 := by
    apply hK
    intro z hz
    rw [hs z (by rw [pow_mul, hz, one_pow])]
    rw [← Nat.div_add_mod c l, pow_add, pow_mul, hz, one_pow, one_mul,
      show c % l = 1 % l from hc1, Nat.mod_eq_of_lt hlp.one_lt, pow_one]
  have hus : (u s : ZMod g.M) = d :=
    (expo_eq hζM ((hu s).symm.trans (hs _ hζMN))).trans ((ZMod.natCast_eq_natCast_iff _ _ _).mpr hcd)
  have h1 := congrFun hfeq s
  simp only [f, hχs, hus, Units.val_one, map_one, one_pow, one_mul] at h1
  rw [sq] at h1
  exact mul_self_eq_one_iff.mp h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.FormPLamSmul
section
open UpperTheory.V.Z.Kato.Joint

private theorem formP_lam_add (B : ℕ) (cc a b : ℕ → ℂ) :
    GlobalTheory.EisM.lam B cc (a + b) = GlobalTheory.EisM.lam B cc a + GlobalTheory.EisM.lam B cc b := by
  unfold GlobalTheory.EisM.lam
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem formP_lam_smul (B : ℕ) (cc a : ℕ → ℂ) (r : ℂ) :
    GlobalTheory.EisM.lam B cc (r • a) = r * GlobalTheory.EisM.lam B cc a := by
  unfold GlobalTheory.EisM.lam
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

theorem UpperTheory.V.Z.Kato.Joint.LocFacts₂ :
    UpperTheory.V.Z.Kato.Joint.FormP := by
  unfold UpperTheory.V.Z.Kato.Joint.FormP
  intro l _ ι k N χ t α B cc χE ev hk hE hχE hT hU hD P hP
  have hℓ : Nat.Prime l := Fact.out
  suffices key : ∀ a : ℕ → Formalism.ConjugateSelfDual.Qbar l,
      GlobalTheory.EisM.MF k (N * l) (GlobalTheory.EisM.ch χ) (fun i => ι (a i)) →
      GlobalTheory.EisM.MF k (N * l) (GlobalTheory.EisM.ch χ)
                   (fun i => ι ((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) P a i)) ∧
        (GlobalTheory.EisM.lam B cc fun i => ι ((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) P a i)) =
          ι ((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) ev) P) * GlobalTheory.EisM.lam B cc fun i => ι (a i) from
    fun a ha => (key a ha).2
  unfold GlobalTheory.KZ.admissibleLettersSubalgebra at hP
  induction hP using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    intro a ha
    simp only [FreeAlgebra.lift_ι_apply]
    cases x with
    | T q =>
      obtain ⟨hq, hqn⟩ : Nat.Prime q ∧ ¬q ∣ N * l := hx
      have hcop : q.Coprime N :=
        Nat.Coprime.coprime_dvd_right (dvd_mul_right N l) ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqn)
      have hχq : ι (χE q) = GlobalTheory.EisM.ch χ (q : ℤ) := by
        rw [hχE q hcop]
        simp [GlobalTheory.EisM.ch]
      have hf : (fop k l χE (GlobalTheory.KZ.Letter.T q)) a = GlobalTheory.EisM.To k (χE q) q a := rfl
      have hcomm : (fun i => ι (GlobalTheory.EisM.To k (χE q) q a i)) =
          GlobalTheory.EisM.To k (GlobalTheory.EisM.ch χ (q : ℤ)) q (fun i => ι (a i)) := by
        funext m
        simp only [GlobalTheory.EisM.To, GlobalTheory.EisM.Vo, map_add (f := _), map_mul, map_pow, map_natCast, hχq]
        split_ifs <;> simp
      rw [hf, hcomm]
      refine ⟨_root_.GlobalTheory.EisM.To_MF k (N * l) N q χ _ hk (dvd_mul_right N l) hq hqn ha, ?_⟩
      rw [hE.T _ ha q hq hqn, hT q hq hqn]
    | U =>
      have hf : (fop k l χE GlobalTheory.KZ.Letter.U) a = GlobalTheory.EisM.Uo l a := rfl
      have hcomm : (fun i => ι (GlobalTheory.EisM.Uo l a i)) = GlobalTheory.EisM.Uo l (fun i => ι (a i)) := rfl
      rw [hf, hcomm]
      refine ⟨(_root_.GlobalTheory.depletion_mf k (N * l) l _ (fun i => ι (a i)) hk hℓ (dvd_mul_left l N) ?_ ha).1, ?_⟩
      · intro d
        simp [GlobalTheory.EisM.ch]
      · rw [hE.U _ ha, hU]
    | D d =>
      have hd : d.Coprime N := hx
      have hf : (fop k l χE (GlobalTheory.KZ.Letter.D d)) a = χE d • a := rfl
      have hcomm : (fun i => ι ((χE d • a) i)) = ι (χE d) • fun i => ι (a i) := by
        funext i
        simp
      rw [hf, hcomm, formP_lam_smul, hD d hd]
      exact ⟨((_root_.GlobalTheory.EisM.mf_linear k (N * l) _).2.2.1 _ _ ha).1, rfl⟩
  | algebraMap r =>
    intro a ha
    have hf : (FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) (algebraMap (Formalism.ConjugateSelfDual.Qbar l) _ r) a = r • a := by
      simp [Algebra.algebraMap_eq_smul_one]
    have hcomm : (fun i => ι ((r • a) i)) = ι r • fun i => ι (a i) := by
      funext i
      simp
    rw [hf, hcomm, formP_lam_smul, AlgHom.commutes]
    exact ⟨((_root_.GlobalTheory.EisM.mf_linear k (N * l) _).2.2.1 _ _ ha).1, rfl⟩
  | add x y _ _ hx hy =>
    intro a ha
    obtain ⟨h1, h2⟩ := hx a ha
    obtain ⟨h3, h4⟩ := hy a ha
    have hcomm : (fun i => ι ((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE) (x + y)) a i)) =
        (fun i => ι (((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) x) a i)) +
          (fun i => ι (((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) y) a i)) := by
      funext i
      simp
    rw [hcomm, formP_lam_add, h2, h4, map_add (f := _), map_add (f := _), add_mul]
    exact ⟨((_root_.GlobalTheory.EisM.mf_linear k (N * l) _).2.1 _ _ h1 h3).1, rfl⟩
  | mul x y _ _ hx hy =>
    intro a ha
    obtain ⟨h3, h4⟩ := hy a ha
    obtain ⟨h1, h2⟩ := hx _ h3
    simp only [map_mul, Module.End.mul_apply]
    refine ⟨h1, ?_⟩
    rw [h2, h4, mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.IndSum
section
open UpperTheory.V.Z.Kato.Joint GlobalTheory.EisM GlobalTheory.KummerEisensteinGalois

private theorem pm_one {R : Type*} [CommRing R] {K : Type*} [Field K] (χ : MulChar R K) : χ (-1) * χ (-1) = 1 := by
  rw [← map_mul]; simp

private theorem ind_sum {N : ℕ} [NeZero N] (ν : DirichletCharacter ℂ N) (v : (ZMod N)ˣ) (B : ZMod N) :
    ∑ u : (ZMod N)ˣ, ν u * (if B = (u : ZMod N) * v then 1 else 0) = ν⁻¹ v * ν B := by
  by_cases hB : IsUnit B
  · obtain ⟨w, rfl⟩ := hB
    have h : ∀ u : (ZMod N)ˣ, ((w : ZMod N) = (u : ZMod N) * v) ↔ w * v⁻¹ = u := fun u => by
      rw [← Units.val_mul, Units.val_inj, mul_inv_eq_iff_eq_mul]
    simp only [h, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Units.val_mul, map_mul]
    rw [mul_comm, MulChar.inv_apply_eq_inv']
    congr 1
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← map_mul]; simp
  · rw [MulChar.map_nonunit _ hB, mul_zero]
    refine Finset.sum_eq_zero fun u _ => ?_
    rw [if_neg, mul_zero]
    rintro rfl
    exact hB (u * v).isUnit

private theorem twb_sum {N : ℕ} [NeZero N] (θ χ : DirichletCharacter ℂ N) (hχ : χ (-1) = -1) (b : ℤ) (hb : IsCoprime b N) (B : ℤ) :
    ∑ u : (ZMod N)ˣ, (θ * χ) u * twb N (θ (-1)) (((u : ZMod N).val : ℤ) * b) B =
      2 * (θ * χ)⁻¹ (b : ZMod N) * ch (θ * χ) B := by
  obtain ⟨v, hv⟩ : IsUnit (b : ZMod N) := (ZMod.coe_int_isUnit_iff_isCoprime b N).mpr hb.symm
  have h1 := ind_sum (θ * χ) v B
  have h2 := ind_sum (θ * χ) v (-B)
  have h3 : (θ * χ) (-(B : ZMod N)) = -θ (-1) * (θ * χ) B := by
    rw [← neg_one_mul (B : ZMod N), map_mul, MulChar.mul_apply θ χ (-1), hχ]; ring
  simp only [neg_eq_iff_eq_neg] at h2
  simp only [twb, ch, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val, ← hv, mul_sub, Finset.sum_sub_distrib,
    mul_left_comm _ (θ (-1)), ← Finset.mul_sum]
  rw [h1, h2, h3]
  linear_combination ((θ * χ)⁻¹ v * (θ * χ) B) * pm_one θ

private theorem Zm_sum {ι : Type*} (S : Finset ι) (k l : ℕ) (u : ℤ → ℂ) (c : ι → ℂ) (v : ι → ℤ → ℂ) (e : ℂ) (w : ℤ → ℂ)
    (F : ℕ → ℕ → ℂ) (h : ∀ B, ∑ j ∈ S, c j * v j B = e * w B) (n : ℕ) :
    ∑ j ∈ S, c j * Zm k l u (v j) F n = e * Zm k l u w F n := by
  simp only [Zm, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs
  · simp
  · calc _ = (x.1 : ℂ) ^ (k - 2) * u x.1 * F x.1 y.2 * ∑ j ∈ S, c j * v j y.1 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = _ := by rw [h]; ring

theorem UpperTheory.V.Z.Kato.Joint.avgEq :
    UpperTheory.V.Z.Kato.Joint.AvgEq := by
  intro l _ ι N _ θ χ m k ψ a b _ _ hk ho hχ ha hb
  refine ⟨fun hne => ?_, fun a' b' haa hbb => ?_, fun hs i => ?_⟩
  · funext i
    apply ι.injective
    have h1 : ι (ψ (-1)) * ι (ψ (-1)) = 1 := by rw [← map_mul, pm_one, map_one]
    have h2 := pm_one θ
    have h3 : ι (ψ (-1)) + θ (-1) = 0 := by
      refine (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hne)
      linear_combination h1 - h2
    have h4 : 1 + ι (ψ (-1)) * θ (-1) = 0 := by linear_combination θ (-1) * h3 - h2
    rw [ser_eq_Zm ι N θ m k ψ a b hk ho ha, h4]
    simp
  · have e1 : (a : ZMod N) = a' := (ZMod.intCast_eq_intCast_iff _ _ _).mpr haa
    have e2 : (b : ZMod N) = b' := (ZMod.intCast_eq_intCast_iff _ _ _).mpr hbb
    have ha' : IsCoprime a' N := by
      refine ((ZMod.coe_int_isUnit_iff_isCoprime a' N).mp ?_).symm
      rw [← e1]
      exact (ZMod.coe_int_isUnit_iff_isCoprime a N).mpr ha.symm
    have e3 : twb N (ι (ψ (-1))) b = twb N (ι (ψ (-1))) b' := by
      funext B; simp only [twb, e2]
    funext i
    apply ι.injective
    rw [ser_eq_Zm ι N θ m k ψ a b hk ho ha, ser_eq_Zm ι N θ m k ψ a' b' hk ho ha', e1, e3]
  · have hu : ∀ u : (ZMod N)ˣ, IsCoprime (((u : ZMod N).val : ℤ) * a) N := fun u =>
      IsCoprime.mul_left (Nat.isCoprime_iff_coprime.mpr (ZMod.val_coe_unit_coprime u)) ha
    have key := Zm_sum Finset.univ k l (hat θ) _ _ _ _
      (fun A d => ι (ψ ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹))) (twb_sum θ χ hχ b hb) (l ^ m * i)
    simp only [ser_eq_Zm_of_parity ι N θ m k ψ _ _ hk ho (hu _) hs, frm, Uo_iterate]
    calc _ = θ (a : ZMod N) * ∑ u : (ZMod N)ˣ, (θ * χ) u * Zm k l (hat θ) (twb N (θ (-1)) (((u : ZMod N).val : ℤ) * b))
            (fun A d => ι (ψ ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹))) (l ^ m * i) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val, map_mul θ, MulChar.mul_apply]
          ring
      _ = _ := by rw [key]; ring
end

