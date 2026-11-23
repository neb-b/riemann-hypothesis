module

public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0300
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SwOn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfCharOfCharOfHasInfQ
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0887
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0653
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0749
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0746
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0755
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0672
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0720
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1811
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1534
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ClsEqOfLocVEqG
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf GlobalTheory.PRep GlobalTheory.LocGL GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.One.M

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem good_contra {n : ℕ} (π π' : IrrRep (GL (Fin n) k)) (e : Nonempty (π'.ρ.Equiv (contra π.ρ))) (hg : Good (cls π)) :
    Good (cls π') := by
  obtain ⟨s, h1, h2⟩ := hg
  obtain ⟨φ⟩ := e
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have h3 : HasSupport π.ρ s := h1.of_equiv (equivRep π).symm
  have hdual : HasSupport (contra π.ρ) (s.map Zc.dualCl) := by
    have hsm := h3.isSmooth
    obtain ⟨m, x, hs, hirr, hcusp, P, hsub⟩ := h3
    have hcs : IsCuspSupport (contra π.ρ) (fun a => (x a).1) (fun a => contra (x a).rep) := by
      refine ⟨GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis k n)
        (hA k n π.V π.ρ hsm hirr) hirr, fun a => ?_, P, ?_⟩
      · have hc := (GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp hA (x a)
          ⟨(hcusp a).1, (hcusp a).2.2⟩).1
        rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA, IrrGL.isCusp_of] at hc
        exact ⟨(hcusp a).1, GlobalTheory.CompanionTheory.ContraProd.contra_rep_isIrreducible hA (x a), hc.2⟩
      · have hsub' := GlobalTheory.CompanionTheory.ContraSub.main k n _ _ π.ρ
          (parInd P (piTensor fun a => (x a).rep)) hsm (isSmooth_parInd P _) hsub
        obtain ⟨E⟩ := GlobalTheory.CompanionTheory.ContraProd.parInd_equiv_contra
          (σ := piTensor fun a => contra (x a).rep) (ρ := piTensor fun a => (x a).rep) P
          (isSmooth_piTensor fun a => (x a).2.rep.smooth)
          (GlobalTheory.CompanionTheory.ContraProd.contra_piTensor_rep hA x)
        exact hsub'.trans (IsSubquotient.of_surjective E.toIntertwiningMap E.toLinearEquiv.surjective)
    rw [← hs, Multiset.map_map]
    simpa only [Function.comp_apply, GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA] using
      hasSupport_of_isCuspSupport hcs
  refine ⟨s.map Zc.dualCl, (hdual.of_equiv φ.symm).of_equiv (equivRep π'), fun y hy => ?_⟩
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
  have hc := h2 z hz
  rcases hc with h | ⟨⟨p, hp, i, hi⟩, _⟩
  · apply Or.inl
    rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA z]
    exact h
  · let : CharZero k := charZero_of_injective_ringHom (f := i.toRingHom) i.injective
    have hd : DualCl z (Zc.dualCl z) :=
      ⟨z.1, z.2.rep, ⟨_, contra z.rep, isSmooth_contra z.rep,
        GlobalTheory.CompanionTheory.ZcDual.isIrreducible_contra hA _ z.2.rep.smooth z.2.rep.irr⟩,
        congrArg (Sigma.mk z.1) z.2.cl_rep.symm,
        GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA z, ⟨.refl _⟩⟩
    exact ((clBasic k z).2.2.2.2.2.2 _ hd).2.2.2.1.mpr (h2 z hz)

end

end UpperTheory.One.M
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ExistsCgTrueCharSide
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocGL GlobalTheory.HeightCounting GlobalTheory.HeightCounting.TrueSide UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.One.M

section Twist

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} [_root_.NumberField.IsTotallyComplex E]
  (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)



end Twist

namespace Old

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut}

theorem cgGood (s : Sw) (C : CGTrue hL D T) : ∀ a (π : D.naut.CG a), GoodAll (C.e a π) := s.elim

theorem cgSurj (C : CGTrue hL D T) : ∀ a, 0 < a → ∀ ρ : HostCGu D.host a, GoodAll ρ → ∃ π, C.e a π = ρ :=
  fun a h ρ _ => C.surj a h ρ

def cgMk (s : Sw) (e : ∀ a, D.naut.CG a ↪ HostCGu D.host a) (_good : ∀ a (π : D.naut.CG a), GoodAll (e a π))
    (_surj : ∀ a, 0 < a → ∀ ρ : HostCGu D.host a, GoodAll ρ → ∃ π, e a π = ρ) (_zero : IsEmpty (D.naut.CG 0))
    (_loc : ∀ a (π : D.naut.CG a) w, T.e w (D.naut.locG π w) = ParLaws.locG hL D.nd.plOm (e a π) w)
    (_tw : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a) (χ : D.naut.CG 1), e a (D.naut.tw π χ) = (e a π).tw (e 1 χ))
    (_inf : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a) τ, D.naut.infG π τ = (e a π).infChar τ)
    (_csd : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a), D.naut.csd π ↔ (e a π).IsCsd) : CGTrue hL D T := False.elim s

end Old

namespace New

variable {hL : RecTExists} {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut}

theorem cgGood (_ : TrivialCondition) (C : CGTrueT hL D T) : ∀ a (π : D.naut.CG a), GoodAll (C.e a π) := C.good

theorem cgSurj (C : CGTrueT hL D T) : ∀ a, 0 < a → ∀ ρ : HostCGu D.host a, GoodAll ρ → ∃ π, C.e a π = ρ := C.surj

def cgMk (_ : TrivialCondition) (e : ∀ a, D.naut.CG a ↪ HostCGu D.host a) (good : ∀ a (π : D.naut.CG a), GoodAll (e a π))
    (surj : ∀ a, 0 < a → ∀ ρ : HostCGu D.host a, GoodAll ρ → ∃ π, e a π = ρ) (zero : IsEmpty (D.naut.CG 0))
    (loc : ∀ a (π : D.naut.CG a) w, T.e w (D.naut.locG π w) = ParLawsT.locGT hL D.nd.plOm (e a π) w)
    (tw : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a) (χ : D.naut.CG 1), e a (D.naut.tw π χ) = (e a π).tw (e 1 χ))
    (inf : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a) τ, D.naut.infG π τ = (e a π).infChar τ)
    (csd : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a), D.naut.csd π ↔ (e a π).IsCsd) : CGTrueT hL D T :=
  ⟨e, good, surj, zero, loc, tw, inf, csd⟩

theorem locParT_unr_iff {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [_root_.NumberField.IsTotallyComplex E]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (hL : RecTExists) (χ : HChar E) (h : IsPlaceOver A w) :
    (ParLawsT.locParT hL (CG.ofChar χ) h).unr ↔ χ.UnrAt w := by
  obtain ⟨a, ha, H⟩ := ParLawsT.isRecT_locRecT hL h
  rw [ParLawsT.locParT_ofChar_eq, H.one, Test.unr_lpOfChar_iff ha (ParLaws.isSmoothChar_loc χ w)]
  refine forall_congr' fun x => imp_congr_left ?_
  have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
  rw [← ord_eq_zero_iff, SphCompletion.ord_completion, neg_eq_zero, IsUnitAt]
  constructor
  · intro hl
    rw [← WithZero.exp_log h0, hl, WithZero.exp_zero]
  · intro hv
    rw [hv, WithZero.log_one]


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_cgTrue_charSide : ∀ hL : RecTExists, GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (D : D7)
    (hE : IsEmpty D.nd.Loc) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (cf : CharFrame D), (∀ k v, cf.P.Div k (D.naut.plGw k v)) →
    ∃ K : CGK D.naut, Nonempty (CGTrueT hL (setCG D hE K) (wdCG hE K T)) ∧ Nonempty (CharSide (setCG D hE K) (cfCG hE K cf)) := by
  intro hL _ D hE T cf hP
  haveI := host_isCMField D.host
  obtain ⟨η, η', e1, e2, h1, h2, h3, h4⟩ := etaLawsT hL D cf.isEta
  refine ⟨trueKT hL D T η η' h1 h2 h3 h4, ⟨trueCGT hL D hE T η η' h1 h2 h3 h4⟩, ⟨
    { e1 := (Equiv.subtypeUnivEquiv (fun π => ⟨Nat.one_pos, goodAll_one π⟩)).trans (CGu.equivChar D.host.E)
      unr_iff := fun π w => ?_
      frob := fun π w hu => ?_
      tw := fun π χ => CGu.equivChar_tw π.1 χ.1
      infG := fun π a ha g => ?_
      csd := fun π => ?_
      etaT := ?_
      etaTinv := ?_
      plGw := hP }⟩⟩
  · obtain ⟨χ, h, e⟩ := exists_ofU π.1
    change D.naut.unr ((T.e w).symm (ParLawsT.locGT hL D.nd.plOm π.1 w)) ↔ (CGu.equivChar D.host.E π.1).1.UnrAt w
    rw [e, equivChar_ofU]
    exact (unr_symm T w _).trans (locParT_unr_iff hL χ (D.nd.plOm.2 w))
  · obtain ⟨χ, h, e⟩ := exists_ofU π.1
    change (CGu.equivChar D.host.E π.1).1.UnrAt w at hu
    change D.naut.frobEig ((T.e w).symm (ParLawsT.locGT hL D.nd.plOm π.1 w)) =
      {(((CGu.equivChar D.host.E π.1).1.val w)⁻¹ : ℂˣ).1}
    rw [e, equivChar_ofU] at *
    have h5 := locParT_unr hL χ (D.nd.plOm.2 w) hu
    exact (frob_symm T w _ h5.1).trans h5.2
  · obtain ⟨χ, h, e⟩ := exists_ofU π.1
    change (CGu.equivChar D.host.E π.1).1.HasInfQ (embPsi D.host) a at ha
    change π.1.1.infChar (embPsi D.host g) = {(a g : ℂ)} ∧
      π.1.1.infChar ((starRingEnd ℂ).comp (embPsi D.host g)) = {-(a g : ℂ)}
    rw [e, equivChar_ofU] at *
    exact infChar_ofChar_of_hasInfQ D.host χ a ha g
  · obtain ⟨χ, h, e⟩ := exists_ofU π.1
    change π.1.1.IsCsd ↔ IsCSD D.host (CGu.equivChar D.host.E π.1).1
    rw [e, equivChar_ofU]
    exact isCsd_ofChar_iff D.host χ
  · exact (congrArg CG.toChar e1).trans (CG.toChar_ofChar _)
  · exact (congrArg CG.toChar e2).trans (CG.toChar_ofChar _)

end New

end UpperTheory.One.M

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.FieldGT
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.LocLanglands.FieldCompat GlobalTheory.LocLanglands.TransportGL GlobalTheory.TheRecTransport GlobalTheory.TypeLawTransport

namespace UpperTheory.One.M.FieldTr

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
  {φ : Ω ≃+* Ω'} {j : E →+* E'} {i : w.adicCompletion E ≃+* w'.adicCompletion E'}

private theorem tame_fwd (P : PlaceIso A w A' w' φ j i) {y : WD h} {y' : WD h'} (hrel : WDRel φ y y')
    (hy : IsTameWD y) : IsTameWD y' := by
  obtain ⟨n, b, b', hb, hb', -, hρ⟩ := hrel
  obtain ⟨m, a, ha, hwild⟩ := hy
  obtain ⟨e, he, -⟩ := GlobalTheory.WeilDeligne.WD.mk_eq_mk.mp (ha.trans hb.symm)
  obtain ⟨c, hc, -⟩ := _root_.GlobalTheory.WeilTransport.weil_equiv E Ω A w h E' Ω' A' w' h' φ j i P
  refine ⟨n, b', hb', fun σ' hσ' => ?_⟩
  have hr : WeilRel φ (c.symm σ') σ' := (hc (c.symm σ') σ').mpr (by simp)
  have hm : ∀ z, φ.symm z ∈ A ↔ z ∈ A' := fun z => by
    rw [← P.mem, RingEquiv.apply_symm_apply]
  have hσ : Formalism.MainNotions.BlochKatoReduction.IsWild A ((c.symm σ' : Weil h) : G E Ω) :=
    GlobalTheory.TameTransport.isWild_of_rel (φ := φ.symm) hm (fun z => φ.injective (by
      rw [RingEquiv.apply_symm_apply, hr, RingEquiv.apply_symm_apply])) hσ'
  rw [← hρ _ σ' hr]
  refine LinearMap.ext fun v => ?_
  obtain ⟨u, rfl⟩ := e.surjective v
  rw [← he, hwild _ hσ]
  rfl


set_option maxHeartbeats 1000000 in
private theorem typeLaw_fwd (P : PlaceIso A w A' w' φ j i) (rc : IrrGL (k := w.adicCompletion E) → WD h)
    (rc' : IrrGL (k := w'.adicCompletion E') → WD h') (hrel : ∀ x x', RepRel i x x' → WDRel φ (rc x) (rc' x'))
    (hT : UpperTheory.Zero.LLC.TypeLaw h rc) : UpperTheory.Zero.LLC.TypeLaw h' rc' := by
  intro E'' _ _ _ _ _ _ g _ w'' h'' ii hii n hn hg hnorm a'' ha'' K _ _ red hred hker θ hθ τ hτ hτc σ' hσ'
  letI iE : Algebra E E'' := ((algebraMap E' E'').comp j).toAlgebra
  letI iΩ : Algebra E'' Ω := ((φ.symm : Ω' →+* Ω).comp (algebraMap E'' Ω')).toAlgebra
  haveI : IsScalarTower E E'' Ω := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap E Ω x = φ.symm (algebraMap E'' Ω' (algebraMap E' E'' (j x)))
    rw [← IsScalarTower.algebraMap_apply, ← P.ext, RingEquiv.symm_apply_apply]
  let ψ : Ω' ≃ₐ[E''] Ω := AlgEquiv.ofRingEquiv (f := φ.symm) fun _ => rfl
  haveI : Algebra.IsAlgebraic E'' Ω' := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure E'' Ω := ⟨IsAlgClosure.isAlgClosed E, ψ.isAlgebraic⟩
  have hm : ∀ z, φ.symm z ∈ A ↔ z ∈ A' := fun z => by
    rw [← P.mem, RingEquiv.apply_symm_apply]
  have h₃ : IsPlaceOver A w'' := fun x => by
    show A.valuation (φ.symm (algebraMap E'' Ω' (x : E''))) < 1 ↔ _
    rw [GlobalTheory.WeilTransport.val_lt_one_iff hm]
    exact h'' x
  haveI := charZero_compl w
  haveI := charZero_compl w'
  have hs : Continuous i.symm := (_root_.GlobalTheory.LocalFieldIso.continuous_iso_keeps_valuation _ _ i P.cont).1
  have hcont : Continuous (ii.trans i.symm) := hs.comp hii
  obtain ⟨T, hT1, -⟩ := GlobalTheory.transport_irrGL_bijective _ _ i.symm hs
  obtain ⟨σ₀, e, h2, he⟩ := exists_of_repRel σ' ((hT1 _ _).2 rfl)
  have hR' : RepRel i.symm (cls σ') (cls σ₀) := h2 ▸ (hT1 _ _).2 rfl
  have hR : RepRel i (cls σ₀) (cls σ') := repRel_symm hR'
  have W := hrel _ _ hR
  have hinf : GlobalTheory.SerSys.TameGen.Inflates (σ₀.ρ.comp (Matrix.GeneralLinearGroup.map (ii.trans i.symm).toRingHom)) τ := by
    obtain ⟨f, hf0, hf⟩ := hσ'
    refine ⟨e.toLinearMap ∘ₗ f, fun h0 => hf0 ?_, fun k v => ?_⟩
    · ext v
      have := congrArg (fun F => F v) h0
      simpa using this
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, MonoidHom.comp_apply] at hf ⊢
      rw [hf, he]
      rfl
  obtain ⟨a₃, ha₃⟩ := GlobalTheory.localArtinExists_holds E'' Ω A w'' h₃
  obtain ⟨hm0, hp⟩ := hT E'' g w'' h₃ (ii.trans i.symm) hcont n hn hg hnorm a₃ ha₃ K red hred hker θ hθ τ hτ hτc σ₀ hinf
  refine ⟨(monodromy_vanishing_iff_of_weil_deligne_rel W).1 hm0, fun t x z hxz hv => ?_⟩
  have hfix : ∀ y : E'', GlobalTheory.WeilTransport.conj φ.symm (t : G E'' Ω').toRingEquiv (algebraMap E'' Ω y) =
      algebraMap E'' Ω y := fun y => by
    show φ.symm ((t : G E'' Ω') (φ.symm.symm (φ.symm (algebraMap E'' Ω' y)))) = φ.symm (algebraMap E'' Ω' y)
    rw [RingEquiv.symm_apply_apply, AlgEquiv.commutes]
  let t₁ : G E'' Ω := GlobalTheory.WeilTransport.conjAlg φ.symm (t : G E'' Ω') hfix
  have hrt : ∀ z, φ.symm ((t : G E'' Ω') z) = t₁ (φ.symm z) := fun z => by
    rw [GlobalTheory.WeilTransport.conjAlg_apply, RingEquiv.symm_apply_apply]
  have ht₁ : t₁ ∈ Ine (F := E'') A := by
    rw [← actsAs_zero_iff (q := 1), GlobalTheory.WeilTransport.actsAs_iff hm hrt, actsAs_zero_iff]
    exact t.2
  have P'' : PlaceIso A' w'' A w'' φ.symm (RingHom.id E'') (RingEquiv.refl (w''.adicCompletion E'')) :=
    ⟨hm, fun _ => rfl, continuous_id, fun _ => rfl⟩
  have hart := GlobalTheory.LocLanglands.isLocalArtin_transport GlobalTheory.globalArtinReciprocity_holds
    GlobalTheory.Published.chevalleyUnits' E'' Ω' A' w'' h'' E'' Ω A w'' h₃ φ.symm (RingHom.id E'')
    (RingEquiv.refl _) P'' a'' a₃ ha'' ha₃ (ineIncl h'' t) (ineIncl h₃ ⟨t₁, ht₁⟩) hrt
  have hv' : Valued.v ((a₃ (ineIncl h₃ ⟨t₁, ht₁⟩) : w''.adicCompletion E'') -
      algebraMap E'' (w''.adicCompletion E'') (x : E'')) < 1 := by
    rw [hart]
    exact hv
  rw [← hp ⟨t₁, ht₁⟩ x z hxz hv']
  refine (inePol_transport P W fun z => ?_).symm
  have := hrt (φ z)
  rw [RingEquiv.symm_apply_apply] at this
  show φ (t₁ z) = (t : G E'' Ω') (φ z)
  rw [← this, RingEquiv.apply_symm_apply]


set_option maxHeartbeats 1000000 in
private theorem isRecT_fwd (P : PlaceIso A w A' w' φ j i) (rc : IrrGL (k := w.adicCompletion E) → WD h)
    (H : UpperTheory.Zero.LLC.IsRecT h rc) (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a') :
    ∃ rc' : IrrGL (k := w'.adicCompletion E') → WD h', UpperTheory.Zero.LLC.IsRecT h' rc' ∧
      ∀ x x', RepRel i x x' → WDRel φ (rc x) (rc' x') := by
  have h3 := P.cont
  have := charZero_compl w
  have := charZero_compl w'
  have hs : Continuous i.symm := (_root_.GlobalTheory.LocalFieldIso.continuous_iso_keeps_valuation _ _ i h3).1
  obtain ⟨T, hT, hTd⟩ := GlobalTheory.T.transportIrrGL_bijective_degree_charZero _ _ i h3
  obtain ⟨hcu, hch⟩ := GlobalTheory.T.transport_keeps_cuspidal_twists_characters _ _ i h3
  obtain ⟨S, hS, hSd, hS0, hSs, hSc, hSt, hSp, hSi, hSo⟩ := GlobalTheory.T.place_over_transport_ring_iso_symm E Ω A w h E' Ω' A' w' h' φ j i P
  obtain ⟨c, hc, -⟩ := _root_.GlobalTheory.WeilTransport.weil_equiv E Ω A w h E' Ω' A' w' h' φ j i P
  obtain ⟨a, ha, L⟩ := H
  have hart := _root_.GlobalTheory.LocLanglands.isLocalArtin_transport GlobalTheory.globalArtinReciprocity_holds GlobalTheory.Published.chevalleyUnits'
    E Ω A w h E' Ω' A' w' h' φ j i P a a' ha ha'
  obtain ⟨rc', key⟩ : ∃ rc' : IrrGL (k := w'.adicCompletion E') → WD h', ∀ x', rc' x' = S (rc (T.symm x')) :=
    ⟨_, fun _ => rfl⟩
  have hRS : ∀ x x', RepRel i x x' → rc' x' = S (rc x) := fun x x' r => by
    rw [key, ← (hT _ _).1 r, T.symm_apply_apply]
  have hR : ∀ x x', RepRel i x x' → WDRel φ (rc x) (rc' x') := fun x x' r => (hS _ _).2 (hRS x x' r).symm
  have hrel : ∀ x', RepRel i (T.symm x') x' := fun x' => (hT _ _).2 (T.apply_symm_apply x')
  have hcusp : ∀ x', (T.symm x').IsCusp ↔ x'.IsCusp := fun x' => (hcu _ _ (hrel x')).1
  have hG : ∀ x x', RepRel i x x' → (UpperTheory.Zero.LLC.Good x ↔ UpperTheory.Zero.LLC.Good x') := fun x x' hx =>
    ⟨GlobalTheory.T.good_irrGL_transport_along_fieldIso _ _ i h3 x x' hx, GlobalTheory.T.good_irrGL_transport_along_fieldIso _ _ i.symm hs x' x (repRel_symm hx)⟩
  have hwd : ∀ y, WDRel φ y (S y) := fun y => (hS _ _).2 rfl
  have hσ : ∀ σ', WeilRel φ (c.symm σ') σ' := fun σ' => (hc _ _).2 (c.apply_symm_apply σ')
  have hv : ∀ (ω : (w'.adicCompletion E')ˣ →* ℂˣ) (z : (w.adicCompletion E)ˣ),
      (ω.comp (Units.map i.symm.symm.toRingHom.toMonoidHom)) z = ω (Units.map i.toRingHom.toMonoidHom z) :=
    fun ω z => rfl
  have heig : ∀ x' σ', (rc' x').eig σ' = (rc (T.symm x')).eig (c.symm σ') := fun x' σ' => by
    rw [hRS _ _ (hrel x')]
    exact (GlobalTheory.LawsTTransport.eig_of_wdRel (hwd _) (hσ σ')).symm
  have hcent : ∀ (x' : IrrGL (k := w'.adicCompletion E')) ω, HasCentralChar x'.rep ω →
      HasCentralChar (T.symm x').rep (ω.comp (Units.map i.symm.symm.toRingHom.toMonoidHom)) :=
    fun x' ω hω => central_transport i.symm (repRel_symm (hrel x')) hω
  refine ⟨rc', ⟨a', ha', ⟨fun x' => ?_, fun χ' hχ' => ?_, fun l x' hx => ?_, fun x' hx => ?_, fun x' s => ?_,
    fun x' ω hω σ' => ?_, fun x' χ hχ hg => ?_, fun x' ω hg hω σ' => ?_, fun n π π' hg ⟨u₀⟩ => ?_,
    fun x' y' hg e => ?_, fun x' hg hf => ?_, typeLaw_fwd P rc rc' hR L.type⟩⟩, hR⟩
  · rw [key, hSd, L.dim, ← hTd, T.apply_symm_apply]
  · have hχ := isSmoothChar_comp i h3 hχ'
    have R := hch _ hχ χ' hχ' (fun _ => rfl)
    rw [key, ← (hT _ _).1 R, T.symm_apply_apply, L.one]
    refine hSo _ _ _ _ fun σ σ' hσ => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, hart σ σ' hσ]
  · let f : Segment (w'.adicCompletion E') → Segment (w.adicCompletion E) := fun Δ =>
      Segment.ofFirst (T.symm Δ.first) ((hcusp _).2 Δ.isCusp_first) Δ.len Δ.len_pos
    have hl := GlobalTheory.T.isLanglandsData_transport_localFieldIso _ _ i.symm hs l (l.map f) x' (T.symm x')
      (by rw [List.forall₂_map_right_iff, List.forall₂_same]; exact fun Δ _ => ⟨repRel_symm (hrel _), rfl⟩)
      (repRel_symm (hrel x')) hx
    rw [key, L.langlands _ _ hl]
    clear hl hx
    induction l with
    | nil => exact hS0
    | cons Δ l ih =>
      simp only [segSum, sumList, List.map_cons, List.foldr_cons] at ih ⊢
      rw [hSs, ih, hSc, hSt, hSp, show (f Δ).first = T.symm Δ.first from rfl,
        show (f Δ).len = Δ.len from rfl, ← key]
  · rw [key, hSi]
    exact L.cusp _ ((hcusp x').2 hx)
  · have R : RepRel i ((T.symm x').nu s) (x'.nu s) := (hcu _ _ (hrel x')).2 s
    rw [key, ← (hT _ _).1 R, T.symm_apply_apply, L.nu, hSt, ← key]
  · rw [heig, L.absCentral _ _ (hcent x' ω hω) (c.symm σ'), hart _ _ (hσ σ'), hv]
  · have hχ0 := isSmoothChar_comp i h3 hχ
    have htw : ∀ x x', RepRel i x x' → RepRel i (x.tw _ hχ0) (x'.tw χ hχ) := by
      rintro x x' ⟨n, π, π', e, rfl, rfl, he⟩
      exact repRel_tw i π π' e he _ hχ0 χ hχ (fun _ => rfl)
    rw [hRS _ _ (htw _ _ (hrel x')), L.twist _ _ _ ((hG _ _ (hrel x')).2 hg), hSc, ← hRS _ _ (hrel x'),
      ← hRS _ _ (hch _ hχ0 χ hχ (fun _ => rfl))]
  · rw [heig, L.central _ _ ((hG _ _ (hrel x')).2 hg) (hcent x' ω hω) (c.symm σ'), hart _ _ (hσ σ'), hv]
  · obtain ⟨π₀, e, h1, he⟩ := exists_of_repRel π (repRel_symm (hrel (cls π)))
    obtain ⟨π₀', u, h2, hu⟩ := exists_of_repRel π' (repRel_symm (hrel (cls π')))
    have r1 : RepRel i (cls π₀) (cls π) := h1 ▸ hrel (cls π)
    have r2 : RepRel i (cls π₀') (cls π') := h2 ▸ hrel (cls π')
    rw [hRS _ _ r2, hRS _ _ r1, ← equiv_lpDual P S hS,
      L.dual n π₀ π₀' ((hG _ _ r1).2 hg) (contra_transport i.symm hs h3 π π' π₀ π₀' e he u hu u₀)]
  · have e2 : rc (T.symm x') = rc (T.symm y') := by
      apply S.injective
      rw [← hRS _ _ (hrel x'), ← hRS _ _ (hrel y'), e]
    exact T.symm.injective (L.inj _ _ ((hG _ _ (hrel y')).2 hg) e2)
  · have hx' := repRel_symm (hrel x')
    exact tame_fwd P (hR _ _ (hrel x')) (L.depth _ (GlobalTheory.T.good_irrGL_transport_along_fieldIso _ _ i.symm hs _ _ hx' hg)
      (GlobalTheory.T.principalCongruence_fixedVectors_ne_bot_transport _ _ i.symm hs _ _ hx' hf))

end UpperTheory.One.M.FieldTr

open UpperTheory.One.M.FieldTr in
theorem UpperTheory.One.M.fieldGT :
    UpperTheory.One.M.FieldGT := by
  intro E Ω _ _ _ _ _ A w h E' Ω' _ _ _ _ _ A' w' h' rc rc' H H' φ j i h1 h2 h3 h4 n π π' e he hg
  have P : PlaceIso A w A' w' φ j i := ⟨h1, h2, h3, h4⟩
  have := charZero_compl w
  have := charZero_compl w'
  obtain ⟨a', ha', -⟩ := id H'
  obtain ⟨rc'', hrec, hR⟩ := isRecT_fwd P rc H a' ha'
  have hr : RepRel i (cls π) (cls π') := ⟨n, π, π', e, rfl, rfl, he⟩
  have hg' := GlobalTheory.T.good_irrGL_transport_along_fieldIso _ _ i h3 _ _ hr hg
  have W := hR _ _ hr
  rw [UpperTheory.Zero.LLC.recTUnique E' Ω' A' w' h' rc'' rc' hrec H' _ hg'] at W
  obtain ⟨a, ha, L⟩ := H
  exact exists_of_wdRel W (L.dim _)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Narrow
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.One.M

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {rc : IrrGL (k := w.adicCompletion E) → WD h}

theorem New.typeS (_s : TrivialCondition) (H : IsRecT h rc) : TypeLaw h rc := H.choose_spec.choose_spec.type

end UpperTheory.One.M
end
end

