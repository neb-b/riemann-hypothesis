module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Mathlib.NumberTheory.Padics.Hensel
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExQuad
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exists_valuationSubring_valuation_prime_lt_one (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) (hp : p.Prime) :
    ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 := by
  let R : Subring Ω := (Int.castRingHom Ω).range
  have hpR : (p : Ω) ∈ R := ⟨p, by simp⟩
  let x : R := ⟨p, hpR⟩
  have hI : Ideal.span {x} ≠ ⊤ := by
    intro h
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_singleton'] at h
    obtain ⟨⟨r, n, rfl⟩, hr⟩ := h
    have h1 : ((n * p : ℤ) : Ω) = 1 := by
      have := congrArg Subtype.val hr
      simpa [x] using this
    have h2 : n * (p : ℤ) = 1 := by exact_mod_cast h1
    have h3 : ((p : ℕ) : ℤ) ∣ ((1 : ℕ) : ℤ) := ⟨n, by push_cast; linarith⟩
    have h4 : p ∣ 1 := Int.natCast_dvd_natCast.mp h3
    exact hp.one_lt.ne' (Nat.dvd_one.mp h4)
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  exact ⟨B, (B.mem_nonunits_iff).mp (hB ⟨x, Ideal.subset_span rfl, rfl⟩)⟩

private theorem ringOfIntegers_rat_exists_int_eq (x : 𝓞 ℚ) : ∃ n : ℤ, x = (n : 𝓞 ℚ) := by
  refine ⟨Rat.ringOfIntegersEquiv x, ?_⟩
  have := eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) (Rat.ringOfIntegersEquiv x)
  exact (Rat.ringOfIntegersEquiv.symm_apply_apply x).symm.trans this

private theorem exists_isPlaceOver_natCast_mem_of_valuation_lt_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (p : ℕ)
    (hp0 : p ≠ 0) (h : A.valuation (p : Ω) < 1) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ), IsPlaceOver A v ∧ (p : 𝓞 ℚ) ∈ v.asIdeal := by
  have hmem : ∀ x : 𝓞 ℚ, ((algebraMap ℚ Ω).comp (algebraMap (𝓞 ℚ) ℚ)) x ∈ A := by
    intro x
    obtain ⟨n, rfl⟩ := ringOfIntegers_rat_exists_int_eq x
    simpa using A.intCast_mem n
  let f : 𝓞 ℚ →+* A := RingHom.codRestrict ((algebraMap ℚ Ω).comp (algebraMap (𝓞 ℚ) ℚ)) A hmem
  let I : Ideal (𝓞 ℚ) := Ideal.comap f (IsLocalRing.maximalIdeal A)
  have hI : ∀ x, x ∈ I ↔ A.valuation ((algebraMap ℚ Ω) (x : ℚ)) < 1 := fun x =>
    A.valuation_lt_one_iff (f x)
  have hpI : (p : 𝓞 ℚ) ∈ I := by
    rw [hI]
    simpa using h
  refine ⟨⟨I, Ideal.comap_isPrime f _, ?_⟩, fun x => (hI x).symm, hpI⟩
  intro hbot
  rw [hbot, Ideal.mem_bot] at hpI
  exact hp0 (by exact_mod_cast hpI)

private theorem false_of_distinct_primes_mem_asIdeal (v : HeightOneSpectrum (𝓞 ℚ)) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal) (hqv : (q : 𝓞 ℚ) ∈ v.asIdeal) : False := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have h1 : (p : ℤ) * p.gcdA q + (q : ℤ) * p.gcdB q = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one]
    rfl
  have h2 : (((p : ℤ) * p.gcdA q + (q : ℤ) * p.gcdB q : ℤ) : 𝓞 ℚ) = 1 := by
    rw [h1]
    simp
  have h3 : (1 : 𝓞 ℚ) ∈ v.asIdeal := by
    rw [← h2]
    push_cast
    exact add_mem (Ideal.mul_mem_right _ _ hpv) (Ideal.mul_mem_right _ _ hqv)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h3)

private theorem exists_padicInt_sq_eq_neg_of_dvd_one_add (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (p : ℕ) (hdiv : (l : ℤ) ∣ 1 + p) :
    ∃ s : ℤ_[l], s ^ 2 = -(p : ℤ_[l]) := by
  let F : Polynomial ℤ := X ^ 2 + C (p : ℤ)
  have h2 : ‖((2 : ℤ) : ℤ_[l])‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp ?_)
    rw [PadicInt.norm_int_lt_one_iff_dvd]
    intro hd
    have h' : l ∣ 2 := by exact_mod_cast hd
    exact hl ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h')
  have ha : (aeval (1 : ℤ_[l])) F = ((1 + p : ℤ) : ℤ_[l]) := by simp [F]
  have hd : (aeval (1 : ℤ_[l])) (derivative F) = ((2 : ℤ) : ℤ_[l]) := by
    simp [F]
    exact map_ofNat _ 2
  have hlt : ‖(aeval (1 : ℤ_[l])) F‖ < ‖(aeval (1 : ℤ_[l])) (derivative F)‖ ^ 2 := by
    rw [ha, hd, h2, one_pow, PadicInt.norm_int_lt_one_iff_dvd]
    exact hdiv
  obtain ⟨z, hz, -⟩ := hensels_lemma hlt
  refine ⟨z, ?_⟩
  have hz' : z ^ 2 + (p : ℤ_[l]) = 0 := by simpa [F] using hz
  linear_combination hz'

private theorem nonempty_ringHom_Kstar_of_sq_eq_neg (l : ℕ) [Fact l.Prime] (p : ℕ) (s : ℚ_[l]) (hs : s ^ 2 = -(p : ℚ_[l])) :
    Nonempty (Kstar p →+* ℚ_[l]) := by
  have hf : (map (algebraMap ℚ ℚ_[l]) (X ^ 2 + C (p : ℚ))) = (X - C s) * (X - C (-s)) := by
    have h' : C s ^ 2 = -C (p : ℚ_[l]) := by rw [← C_pow, hs, C_neg]
    rw [map_natCast] at h'
    simp only [Polynomial.map_add (f := _), Polynomial.map_pow, map_X, map_C, map_natCast, Polynomial.map_natCast, C_neg]
    linear_combination h'
  have hsp : (map (algebraMap ℚ ℚ_[l]) (X ^ 2 + C (p : ℚ))).Splits := by
    rw [hf]
    exact (Splits.X_sub_C s).mul (Splits.X_sub_C _)
  exact ⟨(SplittingField.lift _ hsp).toRingHom⟩

theorem UpperTheory.V.Af.Cq.exQuad :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (S : HeightOneSpectrum (𝓞 ℚ) → Prop), (∀ᶠ v in Filter.cofinite, S v) →
        ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K) (_ : Algebra K Ω) (_ : IsScalarTower ℚ K Ω) (_ : IsAlgClosure K Ω),
          Module.finrank ℚ K = 2 ∧ Nonempty (K →+* ℚ_[l]) ∧ ∃ (v : HeightOneSpectrum (𝓞 ℚ)) (A : ValuationSubring Ω), S v ∧ IsPlaceOver A v ∧
            ∃ s ∈ Ine (F := ℚ) A, s ∉ (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω).range := by
  intro Ω _ instA _ l hl hl2 S hS
  haveI hc : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have e : instA = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  subst e
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  let P : Set ℕ := {p | p.Prime ∧ 4 * l ∣ p + 1}
  haveI hl0 : NeZero (4 * l) := ⟨by have := hl.out.pos; omega⟩
  have hPinf : P.Infinite := by
    refine Set.infinite_of_forall_exists_gt fun n => ?_
    obtain ⟨p, hpn, hp, hpm⟩ :=
      Nat.forall_exists_prime_gt_and_eq_mod (q := 4 * l) (a := -1) isUnit_one.neg n
    refine ⟨p, ⟨hp, ?_⟩, hpn⟩
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [hpm]
    ring
  haveI : Infinite P := hPinf.to_subtype
  have hA : ∀ p : P, ∃ A : ValuationSubring Ω, A.valuation ((p : ℕ) : Ω) < 1 :=
    fun p => exists_valuationSubring_valuation_prime_lt_one Ω p p.2.1
  choose Af hAf using hA
  have hv : ∀ p : P, ∃ v : HeightOneSpectrum (𝓞 ℚ),
      IsPlaceOver (Af p) v ∧ ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal :=
    fun p => exists_isPlaceOver_natCast_mem_of_valuation_lt_one (Af p) p p.2.1.ne_zero (hAf p)
  choose vf hvf1 hvf2 using hv
  have hinj : Function.Injective vf := by
    intro p q hpq
    by_contra hne
    exact false_of_distinct_primes_mem_asIdeal (vf p) p q p.2.1 q.2.1 (fun h => hne (Subtype.ext h)) (hvf2 p) (hpq ▸ hvf2 q)
  have hfin : (vf ⁻¹' {v | ¬ S v}).Finite :=
    (Filter.eventually_cofinite.mp hS).preimage hinj.injOn
  obtain ⟨p, hpS⟩ := hfin.infinite_compl.nonempty
  have hSv : S (vf p) := by simpa using hpS
  obtain ⟨hp, hdvd⟩ := p.2
  have h4 : 4 ∣ (p : ℕ) + 1 := dvd_trans (Dvd.intro l rfl) hdvd
  have hp4 : (p : ℕ) % 4 = 3 := by omega
  have hl' : l ∣ (p : ℕ) + 1 := dvd_trans (Dvd.intro_left 4 rfl) hdvd
  have hdiv : (l : ℤ) ∣ 1 + ((p : ℕ) : ℤ) := by
    have := Int.natCast_dvd_natCast.mpr hl'
    push_cast at this
    rwa [add_comm] at this
  obtain ⟨s, hs⟩ := exists_padicInt_sq_eq_neg_of_dvd_one_add l hl2 p hdiv
  have hs' : (s : ℚ_[l]) ^ 2 = -((p : ℕ) : ℚ_[l]) := by
    have := congrArg (fun x : ℤ_[l] => (x : ℚ_[l])) hs
    push_cast at this
    exact this
  obtain ⟨ι⟩ := nonempty_ringHom_Kstar_of_sq_eq_neg l p s hs'
  obtain ⟨-, htc, hfr, -⟩ := HV.kstar p hp hp4
  let φ : Kstar p →ₐ[ℚ] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI alg : Algebra (Kstar p) Ω := φ.toRingHom.toAlgebra
  haveI tower : IsScalarTower ℚ (Kstar p) Ω :=
    IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)
  haveI : Algebra.IsAlgebraic (Kstar p) Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) (Kstar p)
  haveI hac : IsAlgClosure (Kstar p) Ω := ⟨inferInstance, inferInstance⟩
  haveI := htc
  haveI : Algebra.IsQuadraticExtension ℚ (Kstar p) := ⟨hfr⟩
  have hram := HV.kstarRam p hp hp4 Ω (Af p) (hAf p)
  obtain ⟨σ, hσI, hσG⟩ := SetLike.not_le_iff_exists.mp hram
  refine ⟨Kstar p, inferInstance, inferInstance, IsCMField.ofCMExtension ℚ (Kstar p), alg, tower, hac,
    hfr, ⟨ι⟩, vf p, Af p, hSv, hvf1 p, σ, hσI, ?_⟩
  rintro ⟨τ, rfl⟩
  apply hσG
  intro x
  exact τ.commutes x
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.WdRelRes
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem wdAt_of_model {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
    {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (B : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces B) {a : ℕ}
    (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (L₂ : FinExt l) (r₂ : ↥(Dec (F := E) A) →* GL (Fin a) ↥L₂.1)
    (hm₂ : IsModel B r L₂ r₂) (hV₂ : IsPst P (B.repE L₂ r₂)) :
    wdAt P ι B h hj r = wdPst P ι B h hj (B.repE L₂ r₂) := by
  obtain ⟨L₁, r₁, hm₁, hV₁, e₁⟩ := wdAt_of_isPstAt ι B h hj (r := r) ⟨L₂, r₂, hm₂, hV₂⟩
  have h₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have h₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have e : mapRep (IntermediateField.inclusion h₁).toRingHom r₁ =
      mapRep (IntermediateField.inclusion h₂).toRingHom r₂ := by
    ext g i j
    exact congrArg (fun f : ↥(Dec (F := E) A) →* GL (Fin a) (Om l) => (f g : Matrix (Fin a) (Fin a) (Om l)) i j)
      (hm₁.2.trans hm₂.2.symm)
  rw [e₁, BridgeParam.wdPst_enlarge P ι B h hj h₁ r₁ hV₁, BridgeParam.wdPst_enlarge P ι B h hj h₂ r₂ hV₂, e]

private theorem wdRel_of_frobSS {E Ω E' Ω' : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'} (φ : Ω ≃+* Ω')
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ρ : Weil h → Module.End ℂ V} {ρ' : Weil h' → Module.End ℂ V} {N : Module.End ℂ V}
    {a : WDRep h V} {b : WDRep h' V} (ha : IsFrobSS ρ N a) (hb : IsFrobSS ρ' N b)
    (hρ : ∀ σ σ', WeilRel φ σ σ' → ρ σ = ρ' σ') : WDRel φ (WD.mk a) (WD.mk b) := by
  let e := (Module.finBasis ℂ V).equivFun
  refine ⟨_, a.transport e, b.transport e, WD.sound (a.iso_transport e).symm, WD.sound (b.iso_transport e).symm,
    ?_, fun σ σ' hσ => ?_⟩
  · show e.conjAlgEquiv ℂ a.N = e.conjAlgEquiv ℂ b.N
    rw [ha.1, hb.1]
  · show e.conjAlgEquiv ℂ (a.ρ σ) = e.conjAlgEquiv ℂ (b.ρ σ')
    have h1 := hρ σ σ' hσ
    have h2 := hb.2 σ'
    rw [← h1] at h2
    rw [(Module.End.isNilpotent_isSemisimple_unique (ha.2 σ).2 (a.semisimple σ) h2.2 (b.semisimple σ')
      ((ha.2 σ).1.symm.sub_left (Commute.refl _)) (h2.1.symm.sub_left (Commute.refl _))
      (by simp)).2]

set_option maxHeartbeats 1000000 in
theorem UpperTheory.V.Af.Cq.wdRelRes :
    ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (Bw' : LocBridge l K Ω (Dec (F := K) A) O),
        Bw'.Kw = Bw.Kw → Bw'.j = Bw.j → Bw'.LL = Bw.LL → ∀ (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)), IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) →
        ∀ (ι : Qbar l ≃+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (h' : IsPlaceOver A w) (hj : Induces Bw) (hj' : Induces Bw')
          (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i →
          WDRel (RingEquiv.refl Ω) (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype))
            (wdAt (Loc.PP l) ι Bw' h' hj' ((r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)).comp (Dec (F := K) A).subtype)) := by
  intro F K Ω _ _ _ _ _ _ _ _ _ _ _ l _ A O _ _ _ Bw Bw' hK hJ hL n r hr ι v w h h' hj hj' i hP
  obtain ⟨Kw, j, j_E, j_dense, e, e_cont, e_symm_cont, e_comm, LL, LL_split, eO, eO_alg, eO_cont, eO_symm_cont⟩ := Bw'
  dsimp only at hK hJ hL
  subst hK hJ hL
  set Bw' : LocBridge l K Ω (Dec (F := K) A) O :=
    ⟨Bw.Kw, Bw.j, j_E, j_dense, e, e_cont, e_symm_cont, e_comm, Bw.LL, LL_split, eO, eO_alg, eO_cont, eO_symm_cont⟩
    with hB
  obtain ⟨L, r', hm, hV⟩ := hr
  have key : ∀ (g : ↥(Dec (F := K) A)) (x : Ω), ((Bw.e.symm (e g) : ↥(Dec (F := F) A)) : G F Ω) x = (g : G K Ω) x :=
    fun g x => Bw.j.injective (by rw [← Bw.e_comm, MulEquiv.apply_symm_apply, e_comm])
  let r'' : ↥(Dec (F := K) A) →* GL (Fin n) ↥L.1 := r'.comp (e.trans Bw.e.symm).toMonoidHom
  have hm' : IsModel Bw' ((r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)).comp (Dec (F := K) A).subtype)
      L r'' := by
    refine ⟨hm.1, MonoidHom.ext fun g => ?_⟩
    have h1 := DFunLike.congr_fun hm.2 (Bw.e.symm (e g))
    refine h1.trans (congrArg r (AlgEquiv.ext (key g)))
  have hrep : Bw'.repE L r'' = Bw.repE L r' := by
    refine MonoidHom.ext fun g => ?_
    have h1 : r'' (e.symm g) = r' (Bw.e.symm g) := by simp [r'']
    exact congrArg (fun m : GL (Fin n) ↥L.1 => Matrix.toLin' (m : Matrix (Fin n) (Fin n) ↥L.1)) h1
  have hV' : IsPst (Loc.PP l) (Bw'.repE L r'') := by rw [hrep]; exact hV
  rw [wdAt_of_model _ ι Bw h hj _ L r' hm hV, wdAt_of_model _ ι Bw' h' hj' _ L r'' hm' hV', hrep]
  generalize Bw.repE L r' = ρ at hV ⊢
  haveI := hV.finite
  rw [wdPst_of_isPst ι Bw h hj hV, wdPst_of_isPst ι Bw' h' hj' hV]
  obtain ⟨c, hc, hdeg, hq, -⟩ := _root_.GlobalTheory.WeilTransport.weil_equiv F Ω A v h K Ω A w h' _ _ i hP
  refine wdRel_of_frobSS _ (BridgeParam.isFrobSS_wdRep (Loc.PP l) ι Bw h hj ρ)
    (BridgeParam.isFrobSS_wdRep (Loc.PP l) ι Bw' h' hj' ρ) fun σ σ' hσ => ?_
  have h1 : weilToGK Bw h σ = weilToGK Bw' h' σ' := by
    have h2 : Subgroup.inclusion (Weil_le_Dec h) σ = Bw.e.symm (e (Subgroup.inclusion (Weil_le_Dec h') σ')) :=
      Subtype.ext (AlgEquiv.ext fun x => (hσ x).trans (key (Subgroup.inclusion (Weil_le_Dec h') σ') x).symm)
    exact (congrArg Bw.e h2).trans (Bw.e.apply_symm_apply _)
  have h3 : alpha l σ = alpha l σ' := by
    rw [alpha, alpha, ← (hc σ σ').1 hσ, hdeg, resDeg, resDeg, hq]
  have h4 : weilD Bw h (Loc.PP l) ρ σ = weilD Bw' h' (Loc.PP l) ρ σ' :=
    (weilD_apply Bw h (Loc.PP l) ρ σ).trans ((congrArg₂ (fun (g : ↥(GK Bw.Kw)) (m : ℤ) => actD (Loc.PP l) ρ g *
      Units.val (phiU (Loc.PP l) ρ ^ (-m)))
      h1 h3).trans (weilD_apply Bw' h' (Loc.PP l) ρ σ').symm)
  refine wd_ext _ ι ρ fun x => ?_
  exact (wdRho_mk (Loc.PP l) ι Bw h hj ρ σ x).trans
    ((congrArg (wdMk (Loc.PP l) ι ρ) (LinearMap.congr_fun h4 x)).trans (wdRho_mk (Loc.PP l) ι Bw' h' hj' ρ σ' x).symm)
end

