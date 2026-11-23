module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ExistsBaseRingOfConjugationFixedTensor
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0799
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0776
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsIdealsPrimeToEqSpan
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDataLevelForms
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0014
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0687
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0315
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0032

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameAtOfCongr
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TameConjPlace

open GlobalTheory.ExportSeries Formalism.L2.JoinChr

section Density

variable {E : Type} [Field E] [NumberField E]

theorem tameAt_of_congr (H : Formalism.L2.Host.HChar E) (PP : HeightOneSpectrum (𝓞 E))
    (hc : ∀ (a b : 𝓞 E) (ka kb : Eˣ), (ka : E) = (a : E) → (kb : E) = (b : E) → a ∉ PP.asIdeal →
      a - b ∈ PP.asIdeal → H.locK PP ka = H.locK PP kb) : H.TameAt PP := by
  have hone : ∀ k : Eˣ, PP.valuation E ((k : E) - 1) < 1 → H.locK PP k = 1 := by
    intro k hk
    have hv1 : PP.valuation E (k : E) = 1 := by
      have e : (k : E) = 1 + ((k : E) - 1) := by ring
      have h1 : PP.valuation E ((k : E) - 1) < PP.valuation E 1 := by rwa [map_one]
      rw [e]
      first
        | rw [Valuation.map_add_eq_of_lt_right _ h1, map_one]
        | rw [Valuation.map_add_eq_of_lt_left _ h1, map_one]
        | rw [add_comm, Valuation.map_add_eq_of_lt_right _ h1, map_one]
        | rw [add_comm, Valuation.map_add_eq_of_lt_left _ h1, map_one]
    obtain ⟨a, s, h⟩ := PP.exists_primeCompl_mul_eq_of_integer (k : E) hv1.le
    have hs : (s : 𝓞 E) ∉ PP.asIdeal := s.2
    have hsv := GlobalTheory.ChainOnto.TameRes.valuation_eq_one_of_not_mem PP _ hs
    have hav : PP.valuation E (algebraMap (𝓞 E) E a) = 1 := by
      rw [← h, map_mul, hv1, hsv, one_mul]
    have ha : a ∉ PP.asIdeal := by
      intro hm
      have hlt : PP.valuation E (algebraMap (𝓞 E) E a) < 1 :=
        (PP.valuation_lt_one_iff_mem (K := E) a).mpr hm
      exact absurd hav (ne_of_lt hlt)
    have hs0 : algebraMap (𝓞 E) E s ≠ 0 := fun h0 => by
      rw [h0, map_zero] at hsv; exact zero_ne_one hsv
    have ha0 : algebraMap (𝓞 E) E a ≠ 0 := fun h0 => by
      rw [h0, map_zero] at hav; exact zero_ne_one hav
    have hdiff : a - (s : 𝓞 E) ∈ PP.asIdeal := by
      apply (PP.valuation_lt_one_iff_mem (K := E) _).mp
      show PP.valuation E (algebraMap (𝓞 E) E (a - (s : 𝓞 E))) < 1
      rw [map_sub, ← h, ← sub_one_mul, map_mul, hsv, mul_one]
      exact hk
    let ka : Eˣ := Units.mk0 _ ha0
    let ks : Eˣ := Units.mk0 _ hs0
    have e1 : H.locK PP ka = H.locK PP ks := hc a (s : 𝓞 E) ka ks rfl rfl ha hdiff
    have hk' : k = ka * ks⁻¹ := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, ka, ks]
      rw [← h, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
    rw [hk', map_mul, map_inv, e1, mul_inv_cancel]
  unfold Formalism.L2.Host.HChar.TameAt Formalism.L2.Host.HChar.LevelLe
  intro x _ hx1
  by_contra hne
  have hcont : Continuous (H.loc PP) := H.2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele PP)
  have hW : IsOpen {y : (PP.adicCompletion E)ˣ | H.loc PP y ≠ 1} := isOpen_ne_fun hcont continuous_const
  obtain ⟨T, hT, hTe⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hW
  have hlt : WithZero.exp (-((1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by norm_num)
  have hxT : (x : PP.adicCompletion E) ∈ T ∩ {z | Valued.v (z - 1) < 1} := by
    refine ⟨?_, lt_of_le_of_lt hx1 hlt⟩
    have : x ∈ (Units.val ⁻¹' T : Set (PP.adicCompletion E)ˣ) := by rw [hTe]; exact hne
    exact this
  have hU : IsOpen (T ∩ {z : PP.adicCompletion E | Valued.v (z - 1) < 1}) :=
    hT.inter ((GlobalTheory.ChainOnto.TameRes.isOpen_ltOne PP).preimage (continuous_sub_right 1))
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap E PP).exists_mem_open hU ⟨_, hxT⟩
  have hk1 : PP.valuation E (k - 1) < 1 := by
    rw [← GlobalTheory.ChainOnto.TameRes.val_alg, map_sub, map_one]; exact hk.2
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk1
  have hloc := hone (Units.mk0 k hk0) hk1
  have hmem : Formalism.L2.Host.atFin PP (Units.mk0 k hk0) ∈ (Units.val ⁻¹' T : Set (PP.adicCompletion E)ˣ) := hk.1
  rw [hTe] at hmem
  exact hmem hloc

end Density

variable {D : D7}


set_option maxHeartbeats 800000 in
theorem chi_locE_congr (δ : Twist D Circle) (hδ : δ.Good) {PP : Pl D.host.E} (hPP : PP ∈ δ.Q) (a b : 𝓞 D.host.E)
    (ha : a ∉ PP.asIdeal) (hab : a - b ∈ PP.asIdeal) (x y : (AE D)ˣ)
    (hx : (x : AE D) = 1 + idemAt PP * (incA D (a : D.host.E) - 1))
    (hy : (y : AE D) = 1 + idemAt PP * (incA D (b : D.host.E) - 1)) : δ.chi x = δ.chi y := by
  have he := hδ.split.isIdemAt hPP
  have hee : idemAt PP * idemAt PP = idemAt PP := he.1.1
  obtain ⟨hi, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ PP he
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  have hma : (Ideal.Quotient.mk PP.asIdeal a : kP PP) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact ha
  let u : (kP PP)ˣ := Units.mk0 _ hma
  have key : ∀ (c : 𝓞 D.host.E) (z : (AE D)ˣ), (z : AE D) = 1 + idemAt PP * (incA D (c : D.host.E) - 1) →
      Ideal.Quotient.mk PP.asIdeal c = (u : kP PP) → δ.chi z = δ.res PP u := by
    intro c z hz hcu
    have hv : Formalism.IndefR.Datum.toEAf D (z : AE D) =
        ((1 + ⟨_, hi⟩ * (oToS D.host.F D.host.E c - 1) : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Datum.EAf D) := by
      have hb : Formalism.IndefR.Datum.toEAf D (incA D (c : D.host.E)) =
          ((oToS D.host.F D.host.E c : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Datum.EAf D) := rfl
      rw [hz, GlobalTheory.ConjTwist.map_loc, hb]
      rfl
    have hzi : Formalism.IndefR.Datum.toEAf D (z : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [hv]; exact Subtype.property _
    refine hδ.res PP hPP z ?_ hzi u ?_
    · rw [hz]; linear_combination (1 - incA D (c : D.host.E)) * hee
    · have e2 : (⟨_, hzi⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 1 + ⟨_, hi⟩ * (oToS D.host.F D.host.E c - 1) :=
        Subtype.ext hv
      rw [e2, GlobalTheory.ConjTwist.map_loc, h1, resS_oToS, hcu]
      ring
  have hb : Ideal.Quotient.mk PP.asIdeal b = (u : kP PP) := by
    show Ideal.Quotient.mk PP.asIdeal b = Ideal.Quotient.mk PP.asIdeal a
    exact (Ideal.Quotient.eq.mpr hab).symm
  rw [key a x hx rfl, key b y hy hb]


set_option maxHeartbeats 800000 in
theorem locK_congr_conj (δ : Twist D Circle) (hδ : δ.Good) (χ : Formalism.L2.Host.HChar D.host.E) (hc : ChrEq δ.chi χ)
    {P' : Pl D.host.E} (hP' : P' ∈ δ.Q) {P : Pl D.host.E} (hPP : Formalism.IndefR.Lev.IsConjPl P' P)
    (a b : 𝓞 D.host.E) (ka kb : D.host.Eˣ) (hka : (ka : D.host.E) = (a : D.host.E)) (hkb : (kb : D.host.E) = (b : D.host.E))
    (ha : a ∉ P.asIdeal) (hab : a - b ∈ P.asIdeal) : χ.locK P ka = χ.locK P kb := by
  have he' := hδ.split.isIdemAt hP'
  have he : Formalism.L2.NTheta.IsIdemAt (cA D (idemAt P')) P :=
    (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents D.sp.X').2.2.2 P' _ _ he' hPP
  have hee : cA D (idemAt P') * cA D (idemAt P') = cA D (idemAt P') := he.1.1
  have hcc : cA D (cA D (idemAt P')) = idemAt P' := GlobalTheory.MovedIdem.cA_cA _

  have step : ∀ (k : D.host.Eˣ) (c : 𝓞 D.host.E), (k : D.host.E) = star (c : D.host.E) →
      ∀ z : (AE D)ˣ, (z : AE D) = 1 + idemAt P' * (incA D (c : D.host.E) - 1) →
      ((χ.locK P k : ℂˣ) : ℂ) = ((δ.chi z : Circle) : ℂ)⁻¹ := by
    intro k c hk z hz
    let x := locU hee k
    have h1 : ((δ.chi x : Circle) : ℂ) = ((χ.locK P k : ℂˣ) : ℂ) :=
      hc.2 P _ (GlobalTheory.HeckeDetChar.isPlIdem he) k x (locU_val hee k)
    have hxz : cA D (x : AE D) = (z : AE D) := by
      rw [locU_val, locE, hz, RingHom.map_add (f := _), RingHom.map_one, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hcc,
        GlobalTheory.MovedIdem.cA_incA, hk, star_star]
    have hfix : cA D ((x * z : (AE D)ˣ) : AE D) = ((x * z : (AE D)ˣ) : AE D) := by
      rw [Units.val_mul, RingHom.map_mul, hxz, ← hxz, GlobalTheory.MovedIdem.cA_cA, mul_comm]
    obtain ⟨α, hα⟩ := (GlobalTheory.DetRootRows.fixed_iff_idF (x * z)).1 hfix
    have h2 : δ.chi x * δ.chi z = 1 := by rw [← map_mul, ← hα, hδ.real]
    rw [← h1]
    have h3 : ((δ.chi x : Circle) : ℂ) * ((δ.chi z : Circle) : ℂ) = 1 := by
      rw [← Circle.coe_mul, h2, Circle.coe_one]
    exact eq_inv_of_mul_eq_one_left h3
  have hsym := GlobalTheory.ParahoricLift.isConjPl_symm hPP

  have hca : Formalism.L2.Col.cO _ a ∉ P'.asIdeal := by
    intro hm
    obtain ⟨c', hc', hc'e⟩ := hPP _ hm
    apply ha
    have : c' = a := RingOfIntegers.ext (by rw [hc'e]; exact star_star (a : D.host.E))
    rwa [← this]
  have hcab : Formalism.L2.Col.cO _ a - Formalism.L2.Col.cO _ b ∈ P'.asIdeal := by
    obtain ⟨c', hc', hc'e⟩ := hsym _ hab
    have : c' = Formalism.L2.Col.cO _ a - Formalism.L2.Col.cO _ b := RingOfIntegers.ext (by
      rw [hc'e]
      show star (((a - b : 𝓞 D.host.E)) : D.host.E) = star (a : D.host.E) - star (b : D.host.E)
      push_cast
      exact star_sub _ _)
    rwa [← this]
  have hcne : ∀ c : 𝓞 D.host.E, c ∉ P'.asIdeal → (c : D.host.E) ≠ 0 := fun c hc0 h0 =>
    hc0 (by rw [show c = 0 from RingOfIntegers.ext h0]; exact zero_mem _)
  have hcb : Formalism.L2.Col.cO _ b ∉ P'.asIdeal := fun hm => hca (by
    have := add_mem hcab hm
    rwa [sub_add_cancel] at this)
  have he'e : idemAt P' * idemAt P' = idemAt P' := he'.1.1
  let za := locU he'e (Units.mk0 _ (hcne _ hca))
  let zb := locU he'e (Units.mk0 _ (hcne _ hcb))
  have hza := step ka (Formalism.L2.Col.cO _ a) (by rw [hka]; exact (star_star (a : D.host.E)).symm) za (locU_val he'e _)
  have hzb := step kb (Formalism.L2.Col.cO _ b) (by rw [hkb]; exact (star_star (b : D.host.E)).symm) zb (locU_val he'e _)
  have heq := chi_locE_congr δ hδ hP' _ _ hca hcab za zb (locU_val he'e _) (locU_val he'e _)
  apply Units.ext
  rw [hza, hzb, heq]

theorem tameAt_conj : ∀ (D : D7) (δ : GlobalTheory.ExportSeries.Twist D Circle), δ.Good → ∀ (χ : Formalism.L2.Host.HChar D.host.E),
    ChrEq δ.chi χ → ∀ P' ∈ δ.Q, ∀ P : Pl D.host.E, Formalism.IndefR.Lev.IsConjPl P' P → χ.TameAt P := by
  intro D δ hδ χ hc P' hP' P hPP
  exact tameAt_of_congr χ P fun a b ka kb hka hkb ha hab =>
    locK_congr_conj δ hδ χ hc hP' hPP a b ka kb hka hkb ha hab

end GlobalTheory.TameConjPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistCharacterEqGaloisOfLadicUnitaryHecke
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Neutral.B1 GlobalTheory.HeckeGal GlobalTheory.GalChar

noncomputable section

namespace GlobalTheory.HeckeRead

theorem read_of_isGal_side : ∀ {D : D7} {N : NData D.R D.host D.what₂} {T : TwR D.LL0 N} {art : Ideles D.host.E →* Gab D.host.E N.Om}, IsGlobalArtin art → ∀ {i : T.Tw} (κ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ), (∀ x : D.LL0, ι (κ (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL)) → ∀ (b : Bool) (embO : ↥D.LL0 →+* FractionRing (T.O i)), (∀ (x : ↥D.LL0) (y : T.O0 i), algebraMap (T.O0 i) (FractionRing (T.O0 i)) y = (if b then T.emb0 i else T.emb0b i) x → embO x = algebraMap (T.O i) (FractionRing (T.O i)) (algebraMap (T.O0 i) (T.O i) y)) → ∀ (χ : HChar D.host.E), χ.IsUnitary → ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.E))), (∀ P ∉ S, χ.UnrAt P ∧ ∃ y : ↥D.LL0, embLL0 D y = ((χ.val P : ℂˣ) : ℂ)) → ∀ (H : Formalism.L2.NC.HC D.host.E), (∀ x, H.χ x = χ.1 x) → ∀ {n : (D.host.E →+* ℂ) → ℤ} {r : G D.host.E N.Om →* (T.O0 i)ˣ}, IsGal art κ (sideIso ι b) χ n r → Formalism.L2.NC.Read N.plOm.1 ((Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom).comp r) (algebraMap (T.O i) (FractionRing (T.O i))) embO (Formalism.L2.NC.complexEmbeddingRestrictedToSubfield D) H 0 := by
  intro D N T art ha i κ ι hι b embO hO χ hχu S hS H hH n r hr
  classical
  have hfin := Formalism.L2.NC.finite_placesOver (E := D.host.E) (T.l i)
  refine ⟨hfin.toFinset ∪ S, fun P hP => ?_⟩
  simp only [Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hP
  obtain ⟨hu, y, hy⟩ := hS P hP.2
  have hAt := (GlobalTheory.HeckeUnifVal.at_val_and_unr_iff χ H (MonoidHom.ext hH) P).1 hu
  have hyC : D.what₂.embLL ((y : D.LL0) : D.what₂.LL) = ((χ.val P : ℂˣ) : ℂ) := hy
  have hyi : D.what₂.embLL ((y⁻¹ : D.LL0) : D.what₂.LL) = ((χ.val P : ℂˣ) : ℂ)⁻¹ := by
    rw [IntermediateField.coe_inv, map_inv₀, hyC]
  refine ⟨_, hAt, y⁻¹, ?_, fun σ hσ => ?_⟩
  · rw [zpow_zero, mul_one]
    exact hyi
  · have hl : ((T.l i : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hP.1
    have hf := hr.frob ha (Or.inl hl) hu (N.plOm.2 P) hσ
    have inj : Function.Injective (fun z : FractionRing (T.O0 i) => ι (κ z)) := ι.injective.comp κ.injective
    have hkey : algebraMap (T.O0 i) (FractionRing (T.O0 i)) ((r σ : (T.O0 i)ˣ) : T.O0 i) =
        (if b then T.emb0 i else T.emb0b i) y⁻¹ := by
      cases b
      · have hf' : ι (κ (algebraMap (T.O0 i) (FractionRing (T.O0 i)) ((r σ : (T.O0 i)ˣ) : T.O0 i))) =
            ((χ.val P : ℂˣ) : ℂ) := by
          have e1 : starRingEnd ℂ (ι (κ (algebraMap (T.O0 i) (FractionRing (T.O0 i)) ((r σ : (T.O0 i)ˣ) : T.O0 i)))) =
              ((χ.val P : ℂˣ) : ℂ)⁻¹ := hf
          have hn : ‖((χ.val P : ℂˣ) : ℂ)‖ = 1 := hχu _
          rw [Complex.inv_eq_conj hn] at e1
          have := congrArg (starRingEnd ℂ) e1
          simpa only [Complex.conj_conj] using this
        have hst : ((y : D.LL0) : D.what₂.LL) = star ((y⁻¹ : D.LL0) : D.what₂.LL) := by
          apply D.what₂.embLL.injective
          rw [D.starLL_cx, hyi, hyC]
          have hn : ‖((χ.val P : ℂˣ) : ℂ)‖ = 1 := hχu _
          rw [Complex.inv_eq_conj hn, Complex.conj_conj]
        show _ = T.emb0b i y⁻¹
        rw [T.restX_coefficientEmbedding_conj i y⁻¹ y hst]
        apply inj
        show ι (κ _) = ι (κ _)
        rw [hf', hι, hyC]
      · have hf' : ι (κ (algebraMap (T.O0 i) (FractionRing (T.O0 i)) ((r σ : (T.O0 i)ˣ) : T.O0 i))) =
            ((χ.val P : ℂˣ) : ℂ)⁻¹ := hf
        show _ = T.emb0 i y⁻¹
        apply inj
        show ι (κ _) = ι (κ _)
        rw [hf', hι, hyi]
    rw [hO y⁻¹ _ hkey]
    rfl

end GlobalTheory.HeckeRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistCharacterIsLadicOfFiniteOrderHecke
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Neutral.B1 GlobalTheory.HeckeGal GlobalTheory.GalChar

noncomputable section

namespace GlobalTheory.DeltaGal

theorem continuous_comp_of_isOpen_ker {Gp M Y : Type*} [Group Gp] [TopologicalSpace Gp] [IsTopologicalGroup Gp]
    [Group M] [TopologicalSpace Y] (f : Gp →* M) (h : IsOpen (f.ker : Set Gp)) (u : M → Y) :
    Continuous (fun g => u (f g)) := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hm : (fun x => g⁻¹ * x) ⁻¹' (f.ker : Set Gp) ∈ nhds g :=
    ((continuous_const.mul continuous_id).isOpen_preimage _ h).mem_nhds (by simp)
  refine (continuousAt_const (y := u (f g))).congr ?_
  filter_upwards [hm] with x hx
  simp only [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv] at hx
  rw [inv_mul_eq_one.1 hx]

theorem delta_isGal : GlobalTheory.Published.ChebotarevDegreeOne → ∀ {D : D7} {cf : CharFrame D} {b0 b1 : Big D} {Sx : Finset (PlE D.host)} {T : TwR D.LL0 D.nd} (Sp : RingSpec D cf b0 b1 Sx T) {art : Ideles D.host.E →* Gab D.host.E D.nd.Om}, IsGlobalArtin art → ∀ (i : T.Tw) (κ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ), (∀ x : D.LL0, ι (κ (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL)) → IsGal art κ ι (cf.delAt (T.l i)) 0 (T.delta i) := by
  intro _ D cf b0 b1 Sx T Sp art hart i κ ι hι
  set χ := cf.delAt (T.l i) with hχ
  have hfin : ∃ n, 0 < n ∧ χ.OrderDvd n := by
    rw [hχ]; unfold CharFrame.delAt; split_ifs
    exacts [cf.isDel'.fin, cf.isDel.fin]
  obtain ⟨n, hn, hord⟩ := hfin
  have hpos : IsAlgPos χ 0 := fun k _ => by
    rw [HChar.inf_eq_one_of_order hn hord k]; simp
  refine ⟨hpos, continuous_comp_of_isOpen_ker (T.delta i) (T.delta_open i) (fun u => (u : T.O0 i)), ?_⟩
  obtain ⟨r', hr'c, hr'⟩ := hart.exists_isLAdicOf ι hpos
  suffices h : inQ κ (T.delta i) = r' by rw [h]; exact hr'
  have hc : Continuous (inQ κ (T.delta i)) :=
    continuous_comp_of_isOpen_ker (T.delta i) (T.delta_open i) (Units.map (toQ κ : T.O0 i →* Qbar (T.l i)))
  have h0 : Ideal.span {((T.l i : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (T.lPrime i).out.ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 D.host.E) in Filter.cofinite, ((T.l i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have hS := Filter.eventually_cofinite.1 (hl.and (GlobalTheory.Mem.UnrAe.unr_ae_and_level _ χ).1)
  refine mul_inv_eq_one.1 (GlobalTheory.FrobDense.eq_one_of_frob _ _ art hart _ (inQ κ (T.delta i) * r'⁻¹)
    (hc.mul hr'c.inv) hS.toFinset fun v hv A hA σ hσ => ?_)
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one]
  apply Units.ext
  rw [hr'.frob_unr hart (Or.inr rfl) hv.2 hA hσ]
  obtain ⟨x, hx1, hx2⟩ := Sp.deltaRead i v hv.1 hv.2 A σ hA hσ
  show κ (algebraMap _ _ ((T.delta i σ : T.O0 i))) = _
  rw [hx2]
  apply ι.injective
  rw [hι, hx1, map_inv₀, RingEquiv.apply_symm_apply, Units.val_inv_eq_inv_val]

end GlobalTheory.DeltaGal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistSecondStepKeptWithLocalisations
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.FitTw

noncomputable section

namespace GlobalTheory.TwInputs.SideBLoc


set_option maxHeartbeats 8000000 in
theorem exists_sideB_withLoc : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ∀ (L : LocAll (lay0 D)) (ψ : (withLoc L).nd.Loc → NC.HC D.host.E), (∀ a, NC.ReadC (withLoc L).nd.plOm.1 ((withLoc L).ntw.psiL a) (NC.iotaC (withLoc L) a) (ψ a) 0) → ∃ Rw' : RowSide (withLoc L), HEq Rw'.locR Rw.locR ∧ ∃ Bs' : SideB (withLoc L) (cfL L cf) Rw' low Pq ({ S with } : RatDat (withLoc L).ntw) hL eig θ, HEq Bs'.rowS Bs.rowS := by
  intro D cf Rw low Pq S hL eig θ Bs L ψ hψ
  refine ⟨⟨Rw.locR, Rw.satR, Rw.lab_eq⟩, HEq.rfl, ?_⟩
  exact ⟨{ Bs with
    twF := twFL L Bs.twF
    tw := twTiedL L Bs.tw
    chiD := chiDL L Bs.chiD ψ
    chi := chiL L Bs.chi ψ hψ
    deltaRead := deltaReadL L Bs.deltaRead
    exp := expL L Bs.exp }, HEq.rfl⟩

end GlobalTheory.TwInputs.SideBLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnivSupOfXi
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwInputs

theorem univSup_of_xi : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), FullTie hρ rd → Laws hρ rd → XiType rd → XiBdd rd → ∀ E : IntegralHeckeForms.XD D, UnivSup D E := by
  intro D ρ hρ rd F L hT hB E i hi j hj b a _
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj1
  let j' : Fin D.R.m := ⟨n, hj2⟩
  have T := F.tie i j' b
  obtain ⟨c, hc⟩ := hB i hi j' b _ _ _ (T.dat a)
  refine ⟨c, fun Q M hs hcl hS hlev => ?_⟩
  have hQ : InRange D.ntw i Q := ⟨hs, hcl, hS⟩
  have hnp : ∀ v ∈ Q, ((normProd (T.supp a) : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal :=
    fun v hv h => Finset.disjoint_left.1 hlev hv ((T.lev_iff a v).2 h)
  obtain ⟨x, hx, he⟩ := T.thU_of_rat (L.rat i hi j' b).2.2 M hQ hlev
  classical
  refine ⟨∑ a', Finsupp.single (spread D.nexp i Q M (ρ.ch i) a') (x a'), ?_, fun δ => ?_⟩
  · rw [he, grpSum, ← Finsupp.sum_finsetSum_index (fun _ => by rw [TensorProduct.zero_tmul])
      (fun _ _ _ => by rw [TensorProduct.add_tmul])]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Finsupp.sum_single_index (by rw [TensorProduct.zero_tmul])]
  · have h0 : ∀ a', x a' ∈ Fm0 D.nexp i ((j' : ℕ) + 1) b :=
      fun a' => hT i hi j' b Q M hQ _ _ _ (T.dat a) hnp a' (x a') (hx a')
    have h1 : ∀ a', ((D.ntw.l i : D.ntw.O i) ^ c) • x a' ∈ D.nexp.Bsup i ((j' : ℕ) + 1) b :=
      fun a' => hc Q M hQ hnp a' (x a') (hx a')
    rw [Finsupp.finsetSum_apply]
    refine ⟨Submodule.sum_mem _ fun a' _ => ?_, ?_⟩
    · rw [Finsupp.single_apply]; split_ifs
      · exact h0 a'
      · exact zero_mem _
    · rw [Finset.smul_sum]
      refine Submodule.sum_mem _ fun a' _ => ?_
      rw [Finsupp.single_apply]; split_ifs
      · exact h1 a'
      · rw [smul_zero]; exact zero_mem _

end GlobalTheory.TwInputs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValCCuspOfSmul
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def embS {D : D7} (S : NX.RatDat D.ntw) {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool) :
    S.Ks →+* ℂ_[D.ntw.l i] :=
  iC.comp (NX.ιK S i b)

section Ball

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀) {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool)
  (j : Fin D.R.m)

theorem embC_eKs (a : S.Ks) : embC YS iC b (eKs YS a) = embS S iC b a := by
  simp only [embC, embS, RingHom.comp_apply, sideK_eKs]
  rfl

def locBall : Set (NX.FmK S ((j : ℕ) + 1)) :=
  {f | ∀ z : Pts YS iC b ((j : ℕ) + 1), ‖valC z.1 (cuspOf YS fw j f : T0.R ((j : ℕ) + 1))‖ ≤ 1}

variable {iC b} in
theorem valC_cuspOf_smul (z : FrC YS iC b ((j : ℕ) + 1)) (a : S.Ks) (f : NX.FmK S ((j : ℕ) + 1)) :
    valC z (cuspOf YS fw j (a • f) : T0.R ((j : ℕ) + 1)) = embS S iC b a * valC z (cuspOf YS fw j f : T0.R ((j : ℕ) + 1)) := by
  rw [cuspOf_smul, Submodule.coe_smul, valC_smul, embC_eKs]

end Ball

end GlobalTheory.GeoTie
end
end

