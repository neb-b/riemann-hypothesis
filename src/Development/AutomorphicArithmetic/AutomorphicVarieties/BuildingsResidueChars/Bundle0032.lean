module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0824
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0053

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsPlaceOverLLocDegMulCardEq
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open scoped Pointwise

private theorem td_move {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A B : ValuationSubring Ω}
    (g : G F Ω) (hg : ∀ x, g x ∈ A ↔ x ∈ B) {w : HeightOneSpectrum (𝓞 F)} (hw : IsPlaceOver A w) :
    IsPlaceOver B w := by
  intro x
  rw [← hw x, valuation_lt_one_iff', valuation_lt_one_iff']
  have hy : g (algebraMap F Ω x) = algebraMap F Ω x := g.commutes _
  have hyi : g (algebraMap F Ω x)⁻¹ = (algebraMap F Ω x)⁻¹ := by rw [map_inv₀, hy]
  rw [← hg (algebraMap F Ω x), hy, ← hg (algebraMap F Ω x)⁻¹, hyi]

private theorem td_count (l : ℕ) [hl : Fact l.Prime] (F : Type) [Field F] [NumberField F] [IsGalois ℚ F] {V : Type}
    (pl : V → HeightOneSpectrum (𝓞 F)) (hi : Function.Injective pl) (hm : ∀ v, ((l : ℕ) : 𝓞 F) ∈ (pl v).asIdeal)
    (hs : ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ v, pl v = w) (v : V) :
    locDeg (pl v) * Nat.card V = Module.finrank ℚ F := by
  classical
  let p : Ideal ℤ := Ideal.span {((l : ℕ) : ℤ)}
  have hpp : p.IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hl.out.ne_zero)).2 (Nat.prime_iff_prime_int.1 hl.out)
  haveI hpmax : p.IsMaximal :=
    hpp.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hl.out.ne_zero)
  have hlo : ∀ P : Ideal (𝓞 F), P.IsPrime → ((l : ℕ) : 𝓞 F) ∈ P → P.LiesOver p := by
    intro P hP hlP
    constructor
    apply hpmax.eq_of_le (Ideal.comap_ne_top _ hP.ne_top)
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 F) ((l : ℕ) : ℤ) ∈ P
    rwa [map_natCast]
  let f : V → p.primesOver (𝓞 F) := fun u =>
    ⟨(pl u).asIdeal, (pl u).isPrime, hlo _ (pl u).isPrime (hm u)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      apply hi
      exact HeightOneSpectrum.ext (congrArg Subtype.val h)
    · rintro ⟨P, hP, hPl⟩
      have hlP : ((l : ℕ) : 𝓞 F) ∈ P := by
        have hm' : ((l : ℕ) : ℤ) ∈ p := Ideal.subset_span (Set.mem_singleton _)
        rw [hPl.over] at hm'
        have hm'' := Ideal.mem_comap.1 hm'
        rwa [map_natCast] at hm''
      have hne : P ≠ ⊥ := by
        intro h
        rw [h, Ideal.mem_bot] at hlP
        exact hl.out.ne_zero (by exact_mod_cast hlP)
      obtain ⟨u, hu⟩ := hs ⟨P, hP, hne⟩ hlP
      exact ⟨u, Subtype.ext (congrArg HeightOneSpectrum.asIdeal hu)⟩
  have key : (p.primesOver (𝓞 F)).ncard = Nat.card V := by
    rw [← Nat.card_coe_set_eq]
    exact (Nat.card_eq_of_bijective f hf).symm
  have hG := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p (𝓞 F) (F ≃ₐ[ℚ] F)
  haveI := hlo _ (pl v).isPrime (hm v)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p (pl v).asIdeal (F ≃ₐ[ℚ] F),
    Ideal.inertiaDegIn_eq_inertiaDeg p (pl v).asIdeal (F ≃ₐ[ℚ] F), key,
    IsGalois.card_aut_eq_finrank] at hG
  rw [← hG, mul_comm]
  rfl

theorem UpperTheory.exists_place_over_l_locDeg_mul_card_eq :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (v : T.ι), ∃ w : HeightOneSpectrum (𝓞 T.F), IsPlaceOver (T.pl v) w ∧ ((l : ℕ) : 𝓞 T.F) ∈ w.asIdeal ∧ locDeg w * Nat.card T.ι = T.d := by
  intro Ω _ _ _ l _ c D T v
  haveI := T.nF
  haveI := T.abF
  haveI hac : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  have hlt : ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 T.F)), IsPlaceOver A w →
      (A.valuation (l : Ω) < 1 ↔ ((l : ℕ) : 𝓞 T.F) ∈ w.asIdeal) := by
    intro A w hA
    rw [← hA]
    simp
  choose P hPS hP using fun u => GlobalTheory.DecLocal.exists_place_below (p := l) (F := T.F) (T.pl u) (T.ovl u)
  have hPl : ∀ u, ((l : ℕ) : 𝓞 T.F) ∈ (P u).asIdeal := fun u => hPS u
  refine ⟨P v, hP v, hPl v, td_count l T.F P ?_ hPl ?_ v⟩
  · intro u u' h
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (hP u) (by rw [h]; exact hP u')
    obtain ⟨v0, -, huniq⟩ := T.cover (T.pl u) (T.ovl u)
    have e1 := huniq u ⟨1, fun x => by simp⟩
    have e2 := huniq u' ⟨σ⁻¹, fun x => by
      rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]⟩
    exact e1.trans e2.symm
  · intro w hw
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨u, ⟨g, hg⟩, -⟩ := T.cover A ((hlt A w hA).2 hw)
    exact ⟨u, eq_of_isPlaceOver (hP u) (td_move g hg hA)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsQuadraticSignCharacter
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

private theorem int_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {b : Ω} (hb : IsIntegral ℤ b) :
    A.valuation b ≤ 1 := by
  have h : IsIntegral A b := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [A.valuation_le_one_iff, ← hy]
  exact y.2

private theorem exists_gen (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (h : Module.finrank F E = 2) :
    ∃ (d : 𝓞 F) (t : E), d ≠ 0 ∧ t * t = algebraMap F E d ∧ (∀ c : F, algebraMap F E c ≠ t) ∧
      ∀ x : E, ∃ a b : F, x = algebraMap F E a + algebraMap F E b * t := by
  haveI : Algebra.IsQuadraticExtension F E := ⟨h⟩
  obtain ⟨δ, e, hδ, h0, h1⟩ := GlobalTheory.QuadSymbol.AlmostNorm.exists_basis_sq F E
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) δ
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb1 : algebraMap (𝓞 F) F b ≠ 0 := by simpa using hb0
  have hb2 : algebraMap F E (algebraMap (𝓞 F) F b) ≠ 0 := by simpa using hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hδ (by simp)
  refine ⟨a * b, algebraMap F E (algebraMap (𝓞 F) F b) * e 1, mul_ne_zero ha0 hb0, ?_, fun c hc => ?_, fun x => ?_⟩
  · rw [mul_mul_mul_comm, h1, ← map_mul, ← map_mul]
    congr 1
    show _ = algebraMap (𝓞 F) F (a * b)
    rw [map_mul]
    field_simp
  · apply hδ
    refine ⟨c / algebraMap (𝓞 F) F b, (algebraMap F E).injective ?_⟩
    rw [← h1, map_mul, map_div₀, hc]
    field_simp
  · refine ⟨e.repr x 0, e.repr x 1 / algebraMap (𝓞 F) F b, ?_⟩
    conv_lhs => rw [← e.sum_repr x]
    rw [Fin.sum_univ_two, h0, map_div₀, Algebra.smul_def, Algebra.smul_def]
    field_simp

theorem UpperTheory.exists_quadratic_sign_character :
    UpperTheory.V.Af.Bc.SignEx := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ l _ h
  classical
  obtain ⟨d, t, hd, ht, hn, hx⟩ := exists_gen F E h
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.trans F E Ω
  haveI : IsAlgClosure F Ω := ⟨inferInstance, inferInstance⟩
  set θ : Ω := algebraMap E Ω t with hθ
  have hθ2 : θ * θ = algebraMap F Ω d := by
    rw [hθ, ← map_mul, ht, ← IsScalarTower.algebraMap_apply]
  have hd' : algebraMap F Ω d ≠ 0 := by simpa using hd
  have hθ0 : θ ≠ 0 := fun h0 => hd' (by rw [← hθ2, h0, zero_mul])
  have hne : -θ ≠ θ := fun h0 => hθ0 (by linear_combination (-1 / 2 : Ω) * h0)
  have hpm : ∀ s : G F Ω, s θ = θ ∨ s θ = -θ := fun s => by
    apply mul_self_eq_mul_self_iff.1
    rw [← map_mul, hθ2, AlgEquiv.commutes]
  have hm1 : (-1 : (Qbar l)ˣ) ≠ 1 := fun h0 => by
    have := congrArg Units.val h0
    simp only [Units.val_neg, Units.val_one] at this
    exact absurd this (by norm_num)
  let δ : G F Ω →* (Qbar l)ˣ := MonoidHom.mk' (fun s => if s θ = θ then 1 else -1) fun a b => by
    rcases hpm a with ha | ha <;> rcases hpm b with hb | hb <;>
      simp [AlgEquiv.mul_apply, ha, hb, hne]
  have hδ : ∀ s, δ s = 1 ↔ s θ = θ := fun s => by
    show (if s θ = θ then (1 : (Qbar l)ˣ) else -1) = 1 ↔ _
    split_ifs with h0 <;> simp [h0, hm1]
  refine ⟨δ, continuous_of_isOpen_ker' δ ?_, fun h1 => ?_, ⟨fun s => ?_, fun s => ?_⟩, ?_⟩
  · have e : δ.ker = MulAction.stabilizer (G F Ω) θ := Subgroup.ext fun s => hδ s
    rw [e]
    exact stabilizer_isOpen_of_isIntegral θ
  · have hfix : θ ∈ (⊥ : IntermediateField F Ω) := by
      rw [← InfiniteGalois.fixedField_bot]
      intro s
      exact (hδ s.1).1 (by rw [h1]; rfl)
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 hfix
    refine hn c ((algebraMap E Ω).injective ?_)
    rw [← IsScalarTower.algebraMap_apply, hc]
  · rw [hδ]
    constructor
    · intro hs
      refine ⟨AlgEquiv.ofRingEquiv (f := s.toRingEquiv) fun x => ?_, rfl⟩
      obtain ⟨a, b, rfl⟩ := hx x
      show s _ = _
      rw [map_add (f := _), map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, map_add (f := _), map_mul,
        AlgEquiv.commutes, AlgEquiv.commutes, ← hθ, hs]
    · rintro ⟨u, rfl⟩
      exact u.commutes t
  · show (if s θ = θ then (1 : (Qbar l)ˣ) else -1) = 1 ∨ (if s θ = θ then (1 : (Qbar l)ˣ) else -1) = -1
    split_ifs <;> simp
  · have h4 : Ideal.span {(4 * d : 𝓞 F)} ≠ 0 := by simpa using hd
    refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h4).subset fun v hv => ?_)
    by_contra hv'
    apply hv
    intro A hA s hs
    rw [hδ]
    refine (hpm s).resolve_right fun h0 => hv' ?_
    have hle : A.valuation θ ≤ 1 := by
      have h1 : A.valuation (θ * θ) ≤ 1 := by
        rw [hθ2]
        exact int_le A (map_isIntegral_int (algebraMap F Ω) d.isIntegral_coe)
      rw [map_mul] at h1
      by_contra h2
      exact absurd h1 (not_le.2 (one_lt_mul'' (not_le.1 h2) (not_le.1 h2)))
    have hlt := hs.2 θ hle
    rw [h0] at hlt
    show v.asIdeal ∣ _
    rw [Ideal.dvd_span_singleton, ← hA]
    have e : algebraMap F Ω ((4 * d : 𝓞 F) : F) = (-θ - θ) * (-θ - θ) := by
      have : ((4 * d : 𝓞 F) : F) = 4 * (d : F) := by
        show algebraMap (𝓞 F) F (4 * d) = _
        rw [map_mul, map_ofNat]
      rw [this, map_mul, ← hθ2, map_ofNat]
      ring
    rw [e, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hlt hlt.le
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExpCharIntegralityCriterion
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ValuativeRel IsLocalRing UpperTheory.V
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ec_intIff {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

private theorem ec_le {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime] {w : W.Plc L} (j : W.Emb l w)
    (x : 𝒪[w.adicCompletion L]) : ‖j.1 (x : w.adicCompletion L)‖ ≤ 1 := by
  have hc : Continuous fun y : 𝒪[w.adicCompletion L] => ‖j.1 (y : w.adicCompletion L)‖ :=
    (j.2.comp continuous_subtype_val).norm
  obtain ⟨B, hB⟩ := (isCompact_range hc).bddAbove
  by_contra hx
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B (not_le.1 hx)
  have h := hB ⟨x ^ n, rfl⟩
  simp only [SubmonoidClass.coe_pow, map_pow, norm_pow] at h
  exact absurd h (not_le.2 hn)

private theorem ec_lt {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime] {w : W.Plc L} (j : W.Emb l w)
    (x : 𝒪[w.adicCompletion L]) (hx : x ∈ maximalIdeal 𝒪[w.adicCompletion L]) :
    ‖j.1 (x : w.adicCompletion L)‖ < 1 := by
  haveI : (Valued.v : Valuation (w.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have h1 : valuation (w.adicCompletion L) (x : w.adicCompletion L) < 1 :=
    Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hx
  have h2 : Valued.v (x : w.adicCompletion L) < 1 :=
    (ValuativeRel.isEquiv (valuation (w.adicCompletion L))
      (Valued.v : Valuation (w.adicCompletion L) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one.1 h1
  have ht : Filter.Tendsto (fun k : ℕ => (x : w.adicCompletion L) ^ k) Filter.atTop (nhds 0) :=
    Valued.tendsto_zero_pow_of_v_lt_one h2
  have ht2 := (j.2.tendsto 0).comp ht
  rw [map_zero] at ht2
  refine tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 (ht2.congr fun k => ?_)
  simp

private theorem ec_field {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime] {w : W.Plc L} (j : W.Emb l w) :
    ∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧ ∀ x, j.1 x ∈ K :=
  _root_.UpperTheory.Reformulated.B.Qh13.ec_field j

theorem UpperTheory.expChar_integrality_criterion :
    ∀ (L : Type) [Field L] [NumberField L] (l : ℕ) [Fact l.Prime] (w : W.Plc L) (j : W.Emb l w), (∀ c : Coef l, ∃ c' : Coef l, c.O ≤ c'.O ∧ ∀ x : 𝒪[w.adicCompletion L], j.1 (x : w.adicCompletion L) ∈ c'.O) ∧ ∀ (c' : Coef l), ∀ x ∈ maximalIdeal 𝒪[w.adicCompletion L], ∀ h : j.1 (x : w.adicCompletion L) ∈ c'.O, (⟨_, h⟩ : c'.O) ∈ maximalIdeal c'.O := by
  intro L _ _ l _ w j
  refine ⟨fun c => ?_, fun c' x hx h hu => ?_⟩
  · obtain ⟨K, hK, hj⟩ := ec_field j
    obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l K
    let f : K →ₐ[ℤ_[l]] PadicAlgCl l := K.val.restrictScalars ℤ_[l]
    have hf : Function.Injective f := Subtype.val_injective
    let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
    let d : Coef l := ⟨(integralClosure ℤ_[l] K).map f, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e,
      Module.Finite.equiv e.toLinearEquiv⟩
    obtain ⟨c', hc, hd⟩ := (HV.coefSup l).1 c d
    refine ⟨c', hc, fun x => hd ?_⟩
    exact ⟨⟨_, hj x⟩, (isIntegral_algHom_iff f hf).1 ((ec_intIff _).2 (ec_le j x)), rfl⟩
  · obtain ⟨y, hy⟩ := hu.exists_left_inv
    have hy' : (y : PadicAlgCl l) * j.1 (x : w.adicCompletion L) = 1 := congrArg Subtype.val hy
    have h1 : ‖(y : PadicAlgCl l)‖ ≤ 1 :=
      (ec_intIff _).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) y).map c'.O.val)
    have h2 := mul_lt_one_of_nonneg_of_lt_one_right h1 (norm_nonneg _) (ec_lt j x hx)
    rw [← norm_mul, hy', norm_one] at h2
    exact lt_irrefl _ h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FixesRootsOfUnityOfCyclotomicCharNearOne
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.fixes_roots_of_unity_of_cyclotomicChar_near_one :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (p : ℕ) [Fact p.Prime] (b : ℕ) (s : G F Ω),
    ‖((cycBar F Ω p s : (Qbar p)ˣ) : Qbar p) - 1‖ ≤ ‖((p ^ b : ℕ) : Qbar p)‖ → ∀ ζ : Ω, ζ ^ p ^ b = 1 → s ζ = ζ := by
  intro F Ω _ _ _ _ _ p _ b s h ζ hζ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (p ^ i) := fun i => inferInstance
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [pow_zero, pow_one] at hζ
    rw [hζ, map_one]
  set j : ℤ_[p] := ((cycZ F Ω p s : ℤ_[p]ˣ) : ℤ_[p]) with hj
  have hn : ∀ x : ℚ_[p], ‖algebraMap ℚ_[p] (PadicAlgCl p) x‖ = ‖x‖ := fun x => PadicAlgCl.norm_extends p x
  have e1 : ((cycBar F Ω p s : (Qbar p)ˣ) : Qbar p) - 1 = algebraMap ℚ_[p] (PadicAlgCl p) (((j - 1 : ℤ_[p])) : ℚ_[p]) := by
    rw [show ((cycBar F Ω p s : (Qbar p)ˣ) : Qbar p) = algebraMap ℚ_[p] (PadicAlgCl p) (j : ℚ_[p]) from rfl]
    simp
  have e2 : ((p ^ b : ℕ) : Qbar p) = algebraMap ℚ_[p] (PadicAlgCl p) ((((p : ℤ_[p]) ^ b : ℤ_[p])) : ℚ_[p]) := by
    simp
  rw [e1, e2, hn, hn] at h
  have h' : ‖j - 1‖ ≤ (p : ℝ) ^ (-(b : ℤ)) := by
    rw [← PadicInt.norm_p_pow]
    exact h
  have hmem := (PadicInt.norm_le_pow_iff_mem_span_pow (j - 1) b).mp h'
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hmem
  have hspec := cyclotomicCharacter.spec (L := Ω) p (MulSemiringAction.toRingAut (G F Ω) Ω s) ζ hζ
  have hone : (p ^ b : ℕ) ≠ 1 := by
    have := Nat.one_lt_pow hb.ne' (Fact.out : p.Prime).one_lt
    omega
  have hval : ((cyclotomicCharacter Ω p (MulSemiringAction.toRingAut (G F Ω) Ω s)).val.toZModPow b).val = 1 := by
    have hj' : (cyclotomicCharacter Ω p (MulSemiringAction.toRingAut (G F Ω) Ω s)).val = j := rfl
    rw [hj', hmem]
    exact ZMod.val_one'' hone
  rw [hval, pow_one] at hspec
  exact hspec
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusEigenvaluesDual
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

open scoped Matrix in
private theorem UpperTheory.V.Af.Bc.eig_dual {K : Type} [Field K] (φ : K →+* ℂ) {n : ℕ} (M P : GL (Fin n) K) (t : K)
    (hP : (M : Matrix (Fin n) (Fin n) K)ᵀ * (P : Matrix (Fin n) (Fin n) K) * (M : Matrix (Fin n) (Fin n) K) =
      t • (P : Matrix (Fin n) (Fin n) K)) (S : Multiset ℂ)
    (h : (M : Matrix (Fin n) (Fin n) K).charpoly.map φ = (S.map fun b => X - C b).prod) :
    S = S.map fun a => φ t * a⁻¹ := by
  have h0 : (M : Matrix (Fin n) (Fin n) K)ᵀ = (P : Matrix (Fin n) (Fin n) K) *
      (t • ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.mul_smul, ← Matrix.smul_mul, ← hP, Units.mul_inv_cancel_right, Units.mul_inv_cancel_right]
  have h1 : (M : Matrix (Fin n) (Fin n) K).charpoly =
      (t • ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).charpoly := by
    rw [← Matrix.charpoly_transpose, h0, Matrix.coe_units_inv P, Matrix.charpoly_units_conj]
  have h2 := h
  rw [← Matrix.charpoly_map] at h2
  have h3 := GlobalTheory.charpoly_smul_inv_of_charpoly_eq_prod n (Matrix.GeneralLinearGroup.map φ M) (φ t) _ h2
  have h4 : (t • ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).map φ =
      φ t • (((Matrix.GeneralLinearGroup.map φ M)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← map_inv]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    rfl
  rw [h1, ← Matrix.charpoly_map, h4, h3] at h
  have h5 := congrArg roots h
  rw [roots_multiset_prod_X_sub_C] at h5
  rw [← roots_multiset_prod_X_sub_C (S.map fun a => φ t * a⁻¹), Multiset.map_map]
  exact h5.symm

theorem UpperTheory.frobenius_eigenvalues_dual :
    UpperTheory.V.Af.Bc.FrobDual := by
  intro F Ω _ _ _ _ _ l _ ι n r θ ⟨P, hP⟩ w hw B z hB hz
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
  have h1 := UpperTheory.V.Af.Bc.eig_dual ι.toRingHom (r σ⁻¹) P _ (hP σ⁻¹) _ ((hB A hA).2 σ hσ)
  have h2 : ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
    change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
    rw [cycZ_of_isFrob hw hA hσ, map_natCast, map_natCast]
  have hq0 : normV w ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at h2
    exact Units.ne_zero _ h2
  have hqR : (0 : ℝ) < normV w := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have hqC : (normV w : ℂ) ≠ 0 := by exact_mod_cast hq0
  have h3 := (hz A hA).2 σ hσ
  rw [MonoidHom.mul_apply, MonoidHom.zpow_apply, Units.val_mul, map_mul, map_inv (cycBar F Ω l),
    Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h2, map_zpow₀, map_inv₀, map_natCast] at h3
  set c : ℂ := ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact_mod_cast (Real.rpow_pos_of_pos hqR _).ne'
  have hcc : c * c = (normV w : ℂ) ^ ((n : ℤ) - 1) := by
    rw [hc, ← Complex.ofReal_mul, ← Real.rpow_add hqR, add_halves,
      show ((n : ℝ) - 1) = (((n : ℤ) - 1 : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast]
    push_cast
    rfl
  have h4 : ι.toRingHom ((θ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = z * (c * c) := by
    rw [hcc, ← h3, inv_zpow, inv_mul_cancel_right₀ (zpow_ne_zero _ hqC)]
    rfl
  have hS : algSat n (normV w) B = B.map fun α : ℂˣ => c * (α : ℂ) := by
    simp only [algSat, ← hc, Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map,
      Function.comp_def]
  rw [h4, hS] at h1
  have h5 := congrArg (Multiset.map fun a : ℂ => c * a⁻¹) h1
  simp only [Multiset.map_map, Function.comp_def] at h5
  apply Multiset.map_injective (f := (Units.val : ℂˣ → ℂ)) Units.val_injective
  simp only [Multiset.map_map, Function.comp_def]
  refine (Multiset.map_congr rfl fun a _ => ?_).trans (h5.trans (Multiset.map_congr rfl fun a _ => ?_))
  · rw [Units.val_inv_eq_inv_val]
    have := a.ne_zero
    field_simp
  · rw [Units.val_mul, Units.val_inv_eq_inv_val]
    have := a.ne_zero
    have := z.ne_zero
    field_simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusEigenvaluesTwist
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

private theorem charpoly_smul_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (u : ℂ)
    (L : Multiset ℂ) (hM : M.charpoly = (L.map fun α => X - C α).prod) :
    (u • M).charpoly = ((L.map (· * u)).map fun α => X - C α).prod := by
  have hc : Multiset.card L = Fintype.card ι := by
    rw [← Matrix.charpoly_natDegree_eq_dim M, hM, natDegree_multiset_prod_X_sub_C_eq_card]
  rcases eq_or_ne u 0 with rfl | hu
  · simp [hc]
  · refine Polynomial.funext fun x => ?_
    have h1 := congrArg (eval (x / u)) hM
    rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map] at h1
    have e : Matrix.scalar ι x - u • M = u • (Matrix.scalar ι (x / u) - M) := by
      ext a b
      by_cases hab : a = b
      · subst hab
        simp
        field_simp
      · simp [Matrix.diagonal_apply_ne _ hab]
    rw [Matrix.eval_charpoly, e, Matrix.det_smul, h1, eval_multiset_prod, Multiset.map_map,
      Multiset.map_map, ← hc, ← Multiset.prod_replicate, ← Multiset.map_const, ← Multiset.prod_map_mul]
    refine congrArg _ (Multiset.map_congr rfl fun α _ => ?_)
    simp
    field_simp

theorem UpperTheory.frobenius_eigenvalues_twist :
    UpperTheory.V.Af.Bc.FrobTw := by
  intro F Ω _ _ _ _ l _ ι n r δ w B z hr hδ A hA
  obtain ⟨h1, h2⟩ := hr A hA
  obtain ⟨h3, h4⟩ := hδ A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · apply Units.ext
    rw [tw_val, h1 s hs, h3 s hs]
    simp
  · have e1 := h2 σ hσ
    have e2 := h4 σ hσ
    rw [← Matrix.charpoly_map] at e1 ⊢
    rw [← charpoly_smul_prod _ z B e1, tw_val, ← e2]
    congr 1
    ext i j
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SchurTwistHolds
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

theorem UpperTheory.schur_twist_holds :
    UpperTheory.V.Af.Bc.SchurTw :=
  _root_.UpperTheory.Reformulated.B.H13.schur_twist_holds
end

