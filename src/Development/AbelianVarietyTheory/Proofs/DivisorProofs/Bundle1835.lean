module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1826
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndMapRangeField
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0084
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LUnifOfRhoGeoEquivAll
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1821
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1798
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1815
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1818
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1822
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMoveEigenlatticeSlopeDefinite
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1824
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPhiOfFrameInjectiveShift
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameRead

theorem lift_nabStd_mem_latN : ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 K)) (e0 : K →+* PadicAlgCl l) (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (F : Frame l ι n) (Φ : VV K lam →ₛₗ[e0] NablaT (PadicAlgCl l) n lamW), AtPlace w e0 → Function.Injective F.emb → (∀ x : K, ‖e0 x‖ ≤ 1 → e0 x ∈ Set.range F.emb) → Shift lam lamW c → IsPhi e0 lam lamW Φ → ∀ v : VV K lam, (v : Pol K ι n) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) → Φ v ∈ F.latN lamW :=
  _root_.UpperTheory.Reformulated.B.Ga11.lift_nabStd_mem_latN

end GlobalTheory.FrameRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LUnifOfPins
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TiedUnif

theorem lUnif_of_pins : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), ∀ (F : Face D A) (fw : FWTie T R κ v₀), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → BarTie fw → (∀ i, OMPins T R κ v₀ O i) → RhoGeo fw O → EquivAll T R κ O → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → R.LUnif := by
  intro h1 h2 D G _ _ Pl0 T0 A T _ R κ v₀ O F fw hI hG hM hb hO hr ha hn
  have hT : TieIn T R κ v₀ := GlobalTheory.Div.tieIn_of_fwTie T R κ v₀ fw
  have hpb : T.pb = R.C.P.pb := GlobalTheory.PinsFixHalf.pb_eq_of_pins T R κ v₀ O hI fw.laws hO
  have hu : JUnif T R κ v₀ := (GlobalTheory.HolDict.jUnif_and_lUnif_of_tieIn h1 h2 D G Pl0 T0 A T R κ v₀ hI hM hT hpb hn).1
  exact lUnif_of_rhoGeo_equivAll fw hM hG hb hr ha (_root_.GlobalTheory.EquivConst.exists_equivariant_constants T R κ v₀ O hI hT hpb hO) hu

end GlobalTheory.TiedUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLinkOfSurvivingSimpleSubquotientStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeLink_of_surviving_simple_subquotient : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], GlobalTheory.Published.ChebotarevDegreeOne → ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (inc : ι → (E →+* PadicAlgCl l)) (fr : ℕ → ι → ι) (cjj : ℕ → ι → Bool) (P : Par) (W : Wts ι), (∀ mu : ι → ℕ → ℕ, Linked l P.Nr W.lam mu → BlockFor Ω inc P W mu → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ))) → ∀ (F : Frame l ι P.Nr), F.Ok → ∀ (Bk : (F.I → PadicAlgCl l) → Prop), GalSide Ω inc P W F Bk → ∀ (jK : F.K →* alg F.O P.Nr W.lam), F.IsJ W.lam jK → ∀ (ϖ : F.O), Irreducible ϖ → ϖ ∣ ((l : ℕ) : F.O) → (∀ τ, Antitone (res P.Nr (W.lam τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module F.O Gm] [Module (alg F.O P.Nr W.lam) Gm] [IsScalarTower F.O (alg F.O P.Nr W.lam) Gm] [Module F.T (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)], F.IsHecke W.lam jK Gm → IsSimpleModule (alg F.O P.Nr W.lam) Gm → SubQ F.O P.Nr W.lam ϖ Gm → ∀ (mu : ι → ℕ → ℕ), (∀ τ, Antitone (res P.Nr (mu τ)) ∧ ∑ a : Fin P.Nr, mu τ a = ∑ a : Fin P.Nr, W.lam τ a ∧ (∀ a : Fin P.Nr, W.lam τ (P.Nr - 1) ≤ mu τ a ∧ mu τ a ≤ W.lam τ 0)) → Embeds F.O P.Nr W.lam mu ϖ Gm → ∀ (m : Ideal F.T) [m.IsMaximal] (θ0 : F.I → PadicAlgCl l), F.IsEig W.lam θ0 → Bk θ0 → F.Over θ0 m → ¬ Subsingleton (LocalizedModule m.primeCompl (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)) → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ)) := by
  first | exact @GlobalTheory.ExpFrame.LinkQ.latticeLink_of_surviving | exact GlobalTheory.ExpFrame.LinkQ.latticeLink_of_surviving | (intros; apply GlobalTheory.ExpFrame.LinkQ.latticeLink_of_surviving <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LawsCore
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.LawsCore

theorem laws_core : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → FnAlgClosed (Xo := (T.Q.Xo j)) (c := T.Q.c) →
    Laws (T.U j) (xiR D) := by
  intro D T hT j hj hF
  have hg : ∀ p : ℕ, p.Prime → T.Q.l.GoodAt p :=
    goodAt_of_two_primes hT.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
  have hLaws : GlobalTheory.LevGeo.Laws D j (T.Q.Xo j) T.Q.c (T.U j) (GlobalTheory.LevGeo.coreDict T.toCore j) := by
    obtain ⟨hH, hL, _, hDat⟩ := hT.pins
    refine ⟨hj, hH, hDat j hj, hL.2, hT.unf j hj, hT.chiTriv j hj, ?_, ?_⟩
    · intro σ hσ
      obtain ⟨th, hr, hinf, hdu⟩ := hT.dictU j hj σ hσ
      obtain ⟨Kf', hr', h1, h2, h3⟩ := GlobalTheory.LevCore.dict_transport (hT.spaceW j hj σ hσ) (T.dict j σ) (GlobalTheory.LevGeo.coreDict T.toCore j σ)
        (fun g h' => by unfold GlobalTheory.LevGeo.coreDict; rw [dite_eq_left h']) (T.Kf j σ) th hr _
        (hL.1 ▸ hT.levelK j hj σ hσ) hdu (hT.muUnit j hj σ hσ).2.2.2
      exact ⟨Kf', th, hr', h1, hinf, h2, h3⟩
    · intro σ hσ
      have h := hT.modelW j hj σ hσ
      rw [hT.spaceW j hj σ hσ] at h
      exact h
  exact (GlobalTheory.LevLaws.laws_of_level D j _ _ _ (T.Q.Xo j) T.Q.c (T.U j) _
    hLaws hF hg).1

end GlobalTheory.LawsCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LawsT
section
open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SatakeFlip GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLawsT
open GlobalTheory.Mem.Chr hiding HChar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions GlobalTheory.CuspRep.ParLaws
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CuspRep.ParLawsT

theorem lawsT : ∀ (hT : UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {R : Ranks}
    (H : Formalism.BasicNotions.Host R) (Ω : Type) [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω] (pl : Formalism.GaloisCohomology.Places H.E Ω),
    haveI := host_isCMField H
    (∀ {a} (π : HostCGu H a) w, (locGT hT pl π w).lpDim = a) ∧
    (∀ {a} (π : HostCGu H a), ∀ᶠ w in Filter.cofinite, (locGT hT pl π w).unr) ∧
    (∀ {a} (π : HostCGu H a) (χ : HostCGu H 1) w,
      UpperTheory.Zero.LLC.Good (⟨a, ParLaws.toCl (π.1.loc w)⟩ : IrrGL (k := w.adicCompletion H.E)) → locGT hT pl (π.tw χ) w = (locGT hT pl π w).lpChar (locGT hT pl χ w)) ∧
    (∀ {a} (π : HostCGu H a) τ, Multiset.card (π.infChar τ) = a) ∧
    (∀ {a} (π : HostCGu H a), π.IsRegAlg ↔ ∀ τ, (π.infChar τ).Nodup ∧
      ∀ z ∈ π.infChar τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2) ∧
    (∀ {a} (π : HostCGu H a) (χ : HostCGu H 1) τ (s : ℂ), χ.infChar τ = {s} →
      (π.tw χ).infChar τ = (π.infChar τ).map (· + s)) ∧
    (∀ {a} (π : HostCGu H a) (χ : HostCGu H 1), χ.IsCsd → π.IsCsd → (π.tw χ).IsCsd) ∧
    (∀ {a} (π : HostCGu H a) w w', π.IsCsd → IsConjPl H w w' → (locGT hT pl π w).unr →
      (locGT hT pl π w').unr ∧ (locGT hT pl π w').frobEig = (locGT hT pl π w).frobEig.map (·⁻¹)) ∧
    (∀ (Q : Type) [Field Q] (ι : Q ≃+* ℂ) {a} (π : HostCGu H a) (τ : H.E →+* Q), π.IsRegAlg →
      (jumpsInf ι π τ).map (fun n : ℤ => (n : ℂ)) =
        (π.infChar (ι.toRingHom.comp τ)).map fun z => -z + ((a : ℂ) - 1) / 2) ∧
    ∀ (Q : Type) [Field Q] (ι : Q ≃+* ℂ) (n : ℕ) (wt : (H.E →+* ℂ) → Multiset ℂ) (τ : H.E →+* Q),
      ((jumpsWt ι n wt τ).map (fun n : ℤ => (n : ℂ)) =
        (wt (ι.toRingHom.comp τ)).map fun z => -z + ((n : ℂ) - 1) / 2) ↔
      ∀ z ∈ wt (ι.toRingHom.comp τ), ∃ m : ℤ, z = (m : ℂ) + ((n : ℂ) - 1) / 2 := by
  intro hT hF R H Ω _ _ _ pl
  have := host_isCMField H
  refine ⟨fun π w => lpDim_locParT hT _ _ _ _ _ π.1 _,
    fun π => (eventually_unrT hF hT _ Ω _ π.1).mono fun w hw => hw _ _,
    fun π χ w hg => ?_, fun π τ => π.1.card_infChar τ, fun π => GlobalTheory.CuspRep.CG.isRegAlg_iff _,
    fun π χ τ s => infChar_tw π.1 χ.1 τ s, fun π χ hχ hπ => CG.IsCsd.twist (χ.ofChar_equivChar.symm ▸ hχ) hπ,
    fun π w w' hπ hc => csd_unrT hT hF _ Ω _ π.1 hπ _ _
      ((conjPl_iff_mem _ _ _).2 fun x y e => hc x y (e.trans (host_complexConj H _))) _ _ _ _,
    fun Q _ ι a π τ h => map_jumps (h _).2, fun Q _ ι n wt τ => ⟨fun h => ((map_jumps_iff _).1 h).1, map_jumps⟩⟩
  show locParT hT (π.1.tw χ.1) _ = (locParT hT π.1 _).lpChar (locParT hT χ.1 _)
  rw [CG.tw, locParT_twist hF hT _ Ω _ _ _ π.1 _ _ hg, CG.ofChar_toChar]

end GlobalTheory.CuspRep.ParLawsT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionEquivariantAtFrameConstantsOfClausesStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelAction_equivariant_at_frameConstants_of_clauses : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc → ∀ u : ℂ, O.EquivAt (κ i) (u • cc) := by
  first | exact @GlobalTheory.FrameConstMoveCore.equivAt_of_ccIs_core | exact GlobalTheory.FrameConstMoveCore.equivAt_of_ccIs_core | (intros; apply GlobalTheory.FrameConstMoveCore.equivAt_of_ccIs_core <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelComponentTransportReadsCuspFormsConstMulStatement
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelComponentTransport_reads_cuspForms_const_mul : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E), IsTransp p r i v ψ γ k k' a → ∃ c : ℂˣ, ∀ (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) (x : Frame ((uAt r v i).X k).Ψ D.R.r), x ∈ ((uAt r v i).X k).dom → ∀ (h2 : ((uAt r v i).X k).Ψ = ((uAt r v i).X k').Ψ), rdU (uAt r v i) (actLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (levFull (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) γ F.1) k x = (c : ℂ) * rdU (uAt r v i) F.1 k' (castFrame h2 (lact a x)) := by
  first | exact @GlobalTheory.ShareOn.transp_reads_const_mul | exact GlobalTheory.ShareOn.transp_reads_const_mul | (intros; apply GlobalTheory.ShareOn.transp_reads_const_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMoveEigenlatticeSlopeDefiniteStatement
section
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.levelMove_eigenlattice_slope_definite : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (G : Type) [Group G] [Finite G] (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)) (χ : G →* (c.F)ˣ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (s : ℝ), DefCase U ξ → Finite (Comp Xo c) → Nonempty (Comp Xo c) → (∀ σ, GoodEmb c σ → ∀ g, (dict σ g).2 ∈ ((U σ).X (dict σ g).1).dom) → ActLev (Xo := Xo) c lev → FreePt Xo c lev → Dom a n → GoodW U ξ V dict (wtZ a n) → (∀ Z : Comp Xo c, FibreAt U ξ Z (wtZ a n) s) → eigLat U lev χ (wtZ a n) ≠ ⊥ ∧ s ≤ slope_sq (normW U ξ V dict (wtZ a n)) (eigLat U lev χ (wtZ a n)) / 2 := by
  exact @GlobalTheory.DefPt.OrbitGeo.eigLat_slope
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelLocalGoodPlaceStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_model_local_good_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
    ∀ (omd : UG (cA σ) (dbl (incM F G.V'.J)) →* Module.End ℂ (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd →
    ∀ (f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) → piW t f = 1 → piW (t.comp σ) f = -1 →
    ∀ w : UG (cA σ) (dbl (incM F G.V'.J)),
      ((w : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin a') (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) →
    ∃ c : ℂ, ∀ φ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ φ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
      ∀ ψ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ ψ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
      ι ψ₁ = (fun Y => starRingEnd ℂ (ι (fun y => starRingEnd ℂ (φ₂ y)) (-Y))) →
      ι (fun y => starRingEnd ℂ (ψ₂ y)) = (fun Y => starRingEnd ℂ (ι φ₁ (-Y))) →
      Acts (evFin F v) (omd w) (boxFun φ₁ φ₂) (c • boxFun ψ₁ ψ₂) := by
  first | exact @GlobalTheory.SwapActs.swap_acts_box | exact GlobalTheory.SwapActs.swap_acts_box | (intros; apply GlobalTheory.SwapActs.swap_acts_box <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryDeterminedBySplitImage
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UnitaryInjAtPlace

open GlobalTheory.EmbChart GlobalTheory.LeviAtPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compFin_cA (σ : E →ₐ[F] E) (v : Pl (F := F)) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    compFin F E v (cA σ x) = sigR (Fv F v) σ (compFin F E v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem compFin_inclR (v : Pl (F := F)) (x : E) :
    compFin F E v (inclR (F := F) (AF F) x) = inclR (Fv F v) x := by
  change evFin F v 1 ⊗ₜ[F] x = (1 : Fv F v) ⊗ₜ[F] x
  rw [map_one]

theorem eq_tensAt_of_at (v : Pl (F := F)) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hx : At (evFin F v) x) :
    x = tensAt E v (compFin F E v x) := by
  have h0 : evFin F v (1 - atPlace v 1) = 0 := by rw [map_sub, map_one, evFin_atPlace, sub_self]
  have h1 := hx _ h0
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  have h2 : tensAt E v 1 = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (atPlace v 1) := by
    rw [Algebra.TensorProduct.one_def, tensAt_tmul, Algebra.TensorProduct.algebraMap_apply]
    rfl
  rw [← one_mul (compFin F E v x), ← tensAt_mul_right, h2, ← Algebra.smul_def]
  exact h1

theorem mat_eq_zero_of_at {n : ℕ} (v : Pl (F := F)) (z : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (hz : At (evFin F v) z)
    (h0 : z.map (compFin F E v) = 0) : z = 0 := by
  ext i j
  have hij : At (evFin F v) (z i j) := fun u hu => by
    have := congrFun (congrFun (hz u hu) i) j
    simpa using this
  rw [eq_tensAt_of_at v _ hij]
  have := congrFun (congrFun h0 i) j
  simp only [Matrix.map_apply, Matrix.zero_apply] at this
  rw [this, map_zero, Matrix.zero_apply]

theorem unitary_at_components {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (v : Pl (F := F))
    (t : E →ₐ[F] Fv F v) (h : UA σ J) :
    ((mat h).map (piW t))ᵀ * J.map t * (mat h).map (piW (t.comp σ)) = J.map t := by
  have hm : (mat h)ᵀ * incM F J * (mat h).map (cA σ) = incM F J := h.2
  have h1 := congrArg (fun M => (M.map (compFin F E v)).map (splitProj t)) hm
  simp only [Matrix.map_mul, Matrix.transpose_map] at h1
  have e1 : ((incM F J).map (compFin F E v)).map (splitProj t) = J.map t := by
    ext i j
    simp only [incM, Matrix.map_apply]
    rw [compFin_inclR, splitProj_inclR]
  have e2 : (((mat h).map (cA σ)).map (compFin F E v)).map (splitProj t) = (mat h).map (piW (t.comp σ)) := by
    ext i j
    simp only [Matrix.map_apply]
    rw [compFin_cA, ← splitProj_comp]
    rfl
  have e3 : ((mat h)ᵀ.map (compFin F E v)).map (splitProj t) = ((mat h).map (piW t))ᵀ := by
    ext i j
    rfl
  rw [e1, e2] at h1
  rw [← e3]
  exact h1

theorem eq_of_piW_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v), ∀ h₁ ∈ UAt σ G.W (evFin F v), ∀ h₂ ∈ UAt σ G.W (evFin F v),
      (mat h₁).map (piW t) = (mat h₂).map (piW t) → h₁ = h₂ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v _ t h₁ hh₁ h₂ hh₂ heq
  have hcm := hTr.base.cm
  have hJ : IsUnit (G.W.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := det_ne_zero_of_sig (hTr.geo.hW.sig (InfinitePlace.mk φ))
    have h1 : G.W.J.det ≠ 0 := fun e => h0 (by
      rw [Matrix.det_smul, show G.W.J.map _ = RingHom.mapMatrix _ G.W.J from rfl, ← RingHom.map_det, e, map_zero,
        mul_zero])
    rw [show G.W.J.map t = (t : E →+* Fv F v).mapMatrix G.W.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  have u₁ := unitary_at_components v t h₁
  have u₂ := unitary_at_components v t h₂
  rw [heq] at u₁
  set A := ((mat h₂).map (piW t))ᵀ * G.W.J.map t with hA
  have hAu : IsUnit A.det := by
    have hd := congrArg Matrix.det u₂
    rw [Matrix.det_mul] at hd
    exact isUnit_of_mul_isUnit_left (hd ▸ hJ)
  have hQ : (mat h₁).map (piW (t.comp σ)) = (mat h₂).map (piW (t.comp σ)) := by
    rw [← Matrix.nonsing_inv_mul_cancel_left _ ((mat h₁).map (piW (t.comp σ))) hAu,
      ← Matrix.nonsing_inv_mul_cancel_left _ ((mat h₂).map (piW (t.comp σ))) hAu, u₁, u₂]
  have hpi : ∀ (h : UA σ G.W.J) (τ : E →ₐ[F] Fv F v),
      (mat h).map (piW τ) = ((mat h).map (compFin F E v)).map (splitProj τ) := by
    intro h τ; rw [Matrix.map_map]; rfl
  have hY : (mat h₁).map (compFin F E v) = (mat h₂).map (compFin F E v) := by
    refine mat_split_ext hcm t ?_ ?_
    · rw [← hpi, ← hpi, heq]
    · rw [← hpi, ← hpi, hQ]
  have hz : At (evFin F v) (mat h₁ - mat h₂) := by
    intro u hu
    have e : mat h₁ - mat h₂ = (mat h₁ - 1) - (mat h₂ - 1) := by abel
    rw [e, smul_sub, hh₁ u hu, hh₂ u hu, sub_zero]
  have h0 : (mat h₁ - mat h₂).map (compFin F E v) = 0 := by
    rw [Matrix.map_sub _ (fun x y => map_sub _ x y), hY, sub_self]
  have hm := mat_eq_zero_of_at v _ hz h0
  exact Subtype.ext (Units.ext (sub_eq_zero.1 hm))

end GlobalTheory.UnitaryInjAtPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryMatrixSurjectiveStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_unitary_matrix_surjective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d : ℕ)
    (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s → ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (c x : GL (Fin d) (Fv F v)),
    ∃ h ∈ UAt σ W (evFin F v), locMat t c h = x := by
  first | exact @GlobalTheory.SkewSplitSurj.exists_locMat_eq | exact GlobalTheory.SkewSplitSurj.exists_locMat_eq | (intros; apply GlobalTheory.SkewSplitSurj.exists_locMat_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsOfPrincipalLevelFieldOfDefinitionStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduliLaws_of_principalLevel_fieldOfDefinition : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, Formalism.L2.Theta.GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), GlobalTheory.LevGeo.Laws D j Xo c U dict → FnAlgClosed (Xo := Xo) (c := c) → (∀ p : ℕ, p.Prime → l.GoodAt p) → Laws U (xiR D) ∧ GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H := by
  first | exact @GlobalTheory.LevLaws.laws_of_level | exact GlobalTheory.LevLaws.laws_of_level | (intros; apply GlobalTheory.LevLaws.laws_of_level <;> assumption)
end

