module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1506
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.HasDSComp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.ExistsIrreducibleSubrepresentationBis
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.Bundle0001
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.AdmissibleRepresentationFactorisation
public import Mathlib.LinearAlgebra.Lagrange
public import CompanionTheory.AutomorphicTheory.PadicUnitaryWeights.UnitarySiegelSets.SiegelSetUnitaryHolds
public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.RegClassIntHolds
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2774
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankOfIsSecBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2827
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2816
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsSmoothFanInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2817
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2819
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllTraceOfMiddleX
section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestDataX NoFixed)
open GlobalTheory.TrMult GlobalTheory.TruncKer
open GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp GlobalTheory.ArchVanish
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.PsCo.Plug
open MainStatements.WeightKernel

set_option maxHeartbeats 1000000 in
theorem hyperX : CuspAny → ArchZero → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → HyperZeroX := by
  intro hCA hAZ hRS D V lam S M T U μa μf μ _ _ fa ff hTD γ hreg hirr hna
  obtain ⟨Φ, L, a, hgood⟩ := exists_isGood V
  obtain ⟨g, P, hpar, hne, hmem⟩ := _root_.GlobalTheory.ConjLevi.exists_conj_mem_levi hTD.1.pos hRS Φ γ hreg hirr hna
  refine GlobalTheory.SplitTorusZero.zeroClause_of_conj μ _ γ g ?_
  set γ0 := g * γ * g⁻¹ with hγ0
  have hreg0 : IsRegSS γ0.1.1 := by
    show IsRegSS ((g.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * γ.1.1 * ((g.1)⁻¹ : GL (Fin V.rank) D.host.E).1)
    unfold IsRegSS
    rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj]
    exact hreg
  obtain ⟨hodd, -, -, hNF, hRP, hA, hF⟩ := hTD
  have hff := hF.isFinFamily
  haveI : ∀ w, (μa w).IsHaarMeasure := hRP.haar_arch
  haveI : ∀ v, (μf v).IsHaarMeasure := hRP.haar_loc
  obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
  have hnc := (GlobalTheory.T.centralizer_regular_levi_commutative_noncompact D V Φ P hpar γ0 hreg0 hmem).2.2 (Finset.nonempty_iff_ne_empty.1 hne) w
  have hcm := isCMExt_host D
  have horb : ∀ (ds : Measure (cent (projArch D.sp.cm.sig V.gram w (rat V γ0)))) [ds.IsHaarMeasure]
      [ds.IsMulRightInvariant], HasOrbInt (μa w) (projArch D.sp.cm.sig V.gram w (rat V γ0)) ds (fa w) 0 := by
    obtain ⟨ρ, rfl⟩ := (placeOf_bijective D).2 w
    intro ds _ _
    haveI := (M.ds ρ).1
    have hs : IsRegSS (matAt V ρ (projArch D.sp.cm.sig V.gram (placeOf D ρ) (rat V γ0))) :=
      (isRegSS_archMat_iff hcm (embOverOf D ρ)).2 (isRegSS_projArch_ratEmb hreg0 _)
    exact (hA ρ).orb_noncompact _ hs hnc ds
  obtain ⟨ds, hds1, hds2⟩ : ∃ ds : Measure (cent (projArch D.sp.cm.sig V.gram w (rat V γ0))),
      ds.IsHaarMeasure ∧ ds.IsMulRightInvariant := by
    haveI : LocallyCompactSpace (cent (projArch D.sp.cm.sig V.gram w (rat V γ0))) :=
      (isClosed_cent _).locallyCompactSpace
    exact ⟨Measure.haar, inferInstance, isMulRightInvariant_cent
      (isMulCommutative_cent_projArch_ratEmb (σ := D.sp.cm.sig) (J := V.gram) hreg0 w) _⟩
  exact hAZ D V μ fa ff hA.mem hff
    (fun fa' hfa' => hCA D V hodd T U hNF μf hRP.haar_loc ff hF fa' hfa') γ0 hreg0 w (μa w) ds (horb ds)
end GlobalTheory.PsCo.Plug
end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestDataX NoFixed)
open GlobalTheory.TrMult GlobalTheory.TruncKer
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PsCo.Plug
open MainStatements.WeightKernel
theorem hyperZero_of_intX (hI : MainStatements.RegularCuspidalTrace.RegClassInt) (hRS : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple) : HyperZeroX :=
  hyperX cuspAny (archZero bumpOn (weight (weightDiag lagr shiftT boundT))
    (vanish (kerSwap (kerUnif smoothSum closedGraph)) identOne identTwo) fdRight archGroup archUnimod hI) hRS
end GlobalTheory.PsCo.Plug
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestDataX PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPartX TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
noncomputable section
namespace GlobalTheory.PsCo.Plug
open GlobalTheory.CompanionTheory.EllTrace
open GlobalTheory.TruncKer

theorem ellTrace_of_middleX : MainStatements.RegularCuspidalTrace.RegClassInt → MainStatements.RegularCuspidalTrace.RegClassFin → (∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.CuspidalOperators V μ) → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTermX → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.IwahoriEigenvalues → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.NonFieldTypeVanishingX → HyperZeroX → EllTraceX := by
  intro hInt hFinC hCO hPC hIw _hRS hNF hHZ D V lam S M T U μa μf μ _ _ fa ff hT
  have hT' := hT
  obtain ⟨hodd, -, -, hnf, hμ, harch, hfin⟩ := hT'
  have hμ' := hμ
  obtain ⟨hμa, hμf, -, -⟩ := hμ'
  set f := tensor D.sp.cm.sig V.gram fa ff with hfdef
  have hcc : f ∈ CcGA V := tensor_mem_ccAd harch.mem hfin.isFinFamily
  have hcs := continuous_of_mem_ccAd hcc
  obtain ⟨hH, -⟩ := GlobalTheory.T.typeHypothesis_forms_agree D V T hnf
  haveI := hμa
  haveI := hμf
  have hconst := hPC.2 D V hodd S M T hH U μa μf f ⟨fa, ff, harch, hfin, rfl⟩
  have hcusp : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.IsCuspidalOp V μ f :=
    hCO D V μ f hcc (fun 𝔉 h𝔉 ν hν x y => ((hconst 𝔉 h𝔉).1 ν x y).2)
      (fun 𝔉 h𝔉 ν hν x y => ((hconst 𝔉 h𝔉).2 ν x y).2)
  have hcuspFn : MainStatements.RegularCuspidalTrace.IsCuspFn f := fun 𝔉 h => (hconst 𝔉 h).1
  refine ⟨hcusp.traceClass, ?_⟩
  rw [hcusp.trace_eq_integral]
  haveI : Countable (GF V) := countable_GF V
  let ι := {𝔬 : Set (GF V) // ∃ γ : GF V, IsRegSS γ.1.1 ∧ 𝔬 = {δ | IsConj γ δ}}
  haveI : Countable ι := by
    have hs : Function.Surjective
        (fun γ : {γ : GF V // IsRegSS γ.1.1} => (⟨{δ | IsConj γ.1 δ}, γ.1, γ.2, rfl⟩ : ι)) := by
      rintro ⟨_, γ, hγ, rfl⟩
      exact ⟨⟨γ, hγ⟩, rfl⟩
    exact hs.countable
  let k : ι → GlobalTheory.AutomorphicL2Unitary.Quot (GQ V) → ℂ := fun i =>
    GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun x => ∑' δ : i.1, f (x⁻¹ * rat V δ * x))
  have hkint : ∀ i : ι, Integrable (k i) (autMeasure V μ) := by
    rintro ⟨_, γ, hγ, rfl⟩
    obtain ⟨hcl, -⟩ := (_root_.GlobalTheory.RegClass.main D V γ hγ).2 f
    have := hInt D V μ f hcc hcuspFn γ hγ
    rw [show GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f = fun x => ∑' δ : {δ | IsConj γ δ}, f (x⁻¹ * rat V δ * x)
      from funext hcl] at this
    exact this
  have hreg : ∀ (δ : GF V) (x : GA D V), f (x⁻¹ * rat V δ * x) ≠ 0 → IsRegSS δ.1.1 :=
    fun δ x h => _root_.GlobalTheory.RegSupp.isRegSS_of_tensor_ne_zero hIw D V T U μf ff hfin fa δ x h
  have hPc : ∀ a b : GF V, IsConj a b → Irreducible a.1.1.charpoly → Irreducible b.1.1.charpoly :=
    fun a b h ha => charpoly_eq_of_isConj h ▸ ha
  refine _root_.GlobalTheory.integral_hasSum_eq_integral_indicator_hasSum (autMeasure V μ) k hkint ?_
    {i : ι | ∀ δ ∈ i.1, Irreducible δ.1.1.charpoly} _ _ (fun q => ?_) (fun q => ?_) ?_
  · refine ((hFinC D V f hcc).preimage Subtype.val_injective.injOn).subset fun i hi => ⟨i.2, ?_⟩
    by_contra hno
    apply hi
    have hz : ∀ q, k i q = 0 := by
      intro q
      change (∑' δ : i.1, f (q.out⁻¹ * rat V δ * q.out)) = 0
      have : ∀ δ : i.1, f (q.out⁻¹ * rat V δ * q.out) = 0 := fun δ => by
        by_contra h
        exact hno ⟨q.out, δ.1, δ.2, h⟩
      simp [this]
    simp [hz]
  · obtain ⟨hsupp, hsum⟩ := kernel_diag_hasSum V hcc q.out
    have := (_root_.GlobalTheory.classSum_regroup _ hsupp (fun δ => IsRegSS δ.1.1) (fun δ => Irreducible δ.1.1.charpoly)
      (fun δ h => hreg δ _ h) hPc).1
    rw [hsum.tsum_eq] at this
    exact this
  · obtain ⟨hsupp, -⟩ := kernel_diag_hasSum V hcc q.out
    have := (_root_.GlobalTheory.classSum_regroup _ hsupp (fun δ => IsRegSS δ.1.1) (fun δ => Irreducible δ.1.1.charpoly)
      (fun δ h => hreg δ _ h) hPc).2
    have hfs : (Function.support fun δ : {δ : GF V // Irreducible δ.1.1.charpoly} =>
        f (q.out⁻¹ * rat V δ.1 * q.out)).Finite :=
      (hsupp.preimage Subtype.val_injective.injOn).subset fun δ hδ => hδ
    have e : GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (ellKernel V f) q =
        ∑' δ : {δ : GF V // Irreducible δ.1.1.charpoly}, f (q.out⁻¹ * rat V δ.1 * q.out) := by
      change ellKernel V f q.out = _
      rw [ellKernel, tsum_eq_finsum hfs]
    rw [e]
    exact this
  · rintro ⟨_, γ, hγ, rfl⟩ hi
    have hirr : ¬ Irreducible γ.1.1.charpoly := fun h =>
      hi fun δ hδ => hPc γ δ hδ h
    have hZ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ZeroClause μ f (ratEmb D.sp.cm.sig V.gram γ) := by
      by_cases hA : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1
      · exact hNF.zero hodd hH hμ ⟨fa, ff, harch, hfin, rfl⟩ hA
      · exact hHZ D V lam S M T U μa μf μ fa ff hT γ hγ hirr hA
    obtain ⟨hcl, hiff⟩ := (_root_.GlobalTheory.RegClass.main D V γ hγ).2 f
    have := ((hiff hcs.1 hcs.2 μ 0).1 hZ).2
    rw [show GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f = fun x => ∑' δ : {δ | IsConj γ δ}, f (x⁻¹ * rat V δ * x)
      from funext hcl] at this
    exact this
end GlobalTheory.PsCo.Plug
end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.PsCo.Plug.ellipticSideDirect : GlobalTheory.Published.CuspTraceClass → EllTraceX := fun tc =>
  GlobalTheory.PsCo.Plug.ellTrace_of_middleX MainStatements.WeightKernel.regClassInt_holds (_root_.GlobalTheory.CompanionTheory.CFin.regClassFin CompanionTheory.Prw.siegelCore_holds) (_root_.GlobalTheory.CuspidalOpAssembly.cuspidalOperators tc)
    GlobalTheory.PsCo.Plug.parabolicT GlobalTheory.IwahoriEigenObj.iwahoriEigenvalues _root_.GlobalTheory.RegSSObj.regularSemisimple GlobalTheory.PsCo.Plug.nonFieldT
    (GlobalTheory.PsCo.Plug.hyperZero_of_intX MainStatements.WeightKernel.regClassInt_holds _root_.GlobalTheory.RegSSObj.regularSemisimple)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenBaseChangeStableSectionBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.HomFixLocBasis

theorem isIso_compare : ∀ {S S' : Scheme.{0}} (u : S' ⟶ S) (A : Over S) (Ag : Over S') (φ : Ag.left ⟶ A.left), IsPullback φ Ag.hom A.hom u → ∀ (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S') (y : Spec (CommRingCat.of R) ⟶ S), x ≫ u = y → ∀ (h : (Over.mk x ⊗ Ag).left ⟶ (Over.mk y ⊗ A).left), h ≫ (snd (Over.mk y) A).left = (snd (Over.mk x) Ag).left ≫ φ → h ≫ (fst (Over.mk y) A).left = (fst (Over.mk x) Ag).left → IsIso h := by
  intro S S' u A Ag φ hφ R _ x y hxy h h1 h2
  subst hxy
  have P := (GlobalTheory.AbLaw.SecBC.isPullback_snd Ag (Over.mk x)).paste_horiz hφ
  have Q : IsPullback (snd (Over.mk (x ≫ u)) A).left (fst (Over.mk (x ≫ u)) A).left A.hom (x ≫ u) :=
    GlobalTheory.AbLaw.SecBC.isPullback_snd A (Over.mk (x ≫ u))
  have P' : IsPullback ((snd (Over.mk x) Ag).left ≫ φ) (fst (Over.mk x) Ag).left A.hom (x ≫ u) := P
  have e : h = (P'.isoIsPullback _ _ Q).hom :=
    Q.hom_ext (by rw [h1]; exact (IsPullback.isoIsPullback_hom_fst _ _ P' Q).symm) (by rw [h2]; exact (IsPullback.isoIsPullback_hom_snd _ _ P' Q).symm)
  rw [e]
  infer_instance

theorem exists_basicOpen_le {Rg : Type} [CommRing Rg] (V : (Sp Rg).Opens) (p : Sp Rg) (hpV : p ∈ V) :
    ∃ f : Rg, p ∈ PrimeSpectrum.basicOpen f ∧
      ((PrimeSpectrum.basicOpen f : Set (PrimeSpectrum Rg)) ⊆ (V : Set (Sp Rg))) := by
  have hVo : IsOpen (X := PrimeSpectrum Rg) (V : Set (Sp Rg)) := V.isOpen
  have hpV' : (p : PrimeSpectrum Rg) ∈ (V : Set (Sp Rg)) := hpV
  obtain ⟨W, ⟨f, rfl⟩, h1, h2⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens (R := Rg)).exists_subset_of_mem_open
    (a := (p : PrimeSpectrum Rg)) (u := ((V : Set (Sp Rg)) : Set (PrimeSpectrum Rg))) hpV' hVo
  exact ⟨f, h1, h2⟩

theorem exists_factor_away {Rg : Type} [CommRing Rg] (V : (Sp Rg).Opens) (f g : Rg)
    (hfV : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum Rg)) ⊆ (V : Set (Sp Rg)))
    (hg : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    ∃ uV : Sp (Localization.Away g) ⟶ V.toScheme, uV ≫ V.ι = spMap (algebraMap Rg (Localization.Away g)) := by
  have hu : Set.range (spMap (algebraMap Rg (Localization.Away g))) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have h1 : PrimeSpectrum.comap (algebraMap Rg (Localization.Away g)) x ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum Rg)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
      exact ⟨x, rfl⟩
    exact hfV (hg h1)
  exact ⟨_, IsOpenImmersion.lift_fac V.ι _ hu⟩

theorem secBasis_of_factor {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (hL : L.IsLB) (k : ℕ) (V : (Sp Rg).Opens) (m : ℕ)
    (b : Fin m → LB.Sec (LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) V)))
    (hb : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) V).left) (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))), (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤)
    {S' : Scheme.{0}} (u : S' ⟶ Sp Rg) (uV : S' ⟶ V.toScheme) (huV : uV ≫ V.ι = u)
    (Ag : Over S') [GrpObj Ag] (φ : Ag.left ⟶ A.left) (hφ : IsGrpPullback Ag A u φ) :
    ∃ (b : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (overRes (T := baseOver S') ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver S') ⊤).left) (b' : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (baseAt t))), (∀ i, IsPullSec Ag (L.pull φ) (k : ℤ) (homAt t ▷ Ag) (whiskerRight_snd (homAt t) Ag) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) = ⊤ := by
  have hAgw : φ ≫ A.hom = Ag.hom ≫ u := hφ.1.w
  have hw : ((snd (overRes (T := baseOver S') ⊤) Ag).left ≫ φ) ≫ A.hom =
      ((fst (overRes (T := baseOver S') ⊤) Ag).left ≫ (⊤ : S'.Opens).ι ≫ uV) ≫ (overRes (T := baseOver (Sp Rg)) V).hom := by
    have e := (GlobalTheory.AbLaw.SecBC.isPullback_snd Ag (overRes (T := baseOver S') ⊤)).w
    simp only [Category.assoc, hAgw]
    rw [← Category.assoc, e]
    simp [overRes, baseOver, huV]
  obtain ⟨H, hH1, hH2⟩ : ∃ H : (overRes (T := baseOver S') ⊤ ⊗ Ag).left ⟶ (overRes (T := baseOver (Sp Rg)) V ⊗ A).left,
      H ≫ (snd (overRes (T := baseOver (Sp Rg)) V) A).left = (snd (overRes (T := baseOver S') ⊤) Ag).left ≫ φ ∧
      H ≫ (fst (overRes (T := baseOver (Sp Rg)) V) A).left = (fst (overRes (T := baseOver S') ⊤) Ag).left ≫ (⊤ : S'.Opens).ι ≫ uV :=
    ⟨_, (GlobalTheory.AbLaw.SecBC.isPullback_snd A _).lift_fst _ _ hw, (GlobalTheory.AbLaw.SecBC.isPullback_snd A _).lift_snd _ _ hw⟩
  have hc : ∀ _ : Fin 1, (snd (overRes (T := baseOver S') ⊤) Ag).left ≫ φ = H ≫ (snd (overRes (T := baseOver (Sp Rg)) V) A).left :=
    fun _ => hH1.symm
  refine ⟨fun i => GlobalTheory.SecTwist.pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (overRes (T := baseOver S') ⊤) Ag).left)
    (fun _ : Fin 1 => (snd (overRes (T := baseOver (Sp Rg)) V) A).left) (fun _ => (k : ℤ)) H hc) (b i), ?_⟩
  intro R _ t b' hb'
  obtain ⟨t', ht'⟩ : ∃ t' : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) V).left, t' = t ≫ (⊤ : S'.Opens).ι ≫ uV := ⟨_, rfl⟩
  choose b'' hb'' using fun i => GlobalTheory.AbLaw.SecBC.exists_pullSec A L (k : ℤ) (homAt t') (b i)
  have hB := hb R t' b'' hb''
  have hxy : (t ≫ (overRes (T := baseOver S') ⊤).hom) ≫ u = t' ≫ (overRes (T := baseOver (Sp Rg)) V).hom := by
    rw [ht']
    simp [overRes, baseOver, huV]
  have hw2 : ((snd (baseAt t) Ag).left ≫ φ) ≫ A.hom = (fst (baseAt t) Ag).left ≫ (baseAt t').hom := by
    have e := (GlobalTheory.AbLaw.SecBC.isPullback_snd Ag (baseAt t)).w
    simp only [Category.assoc, hAgw]
    rw [← Category.assoc, e]
    simp [baseAt, overRes, baseOver, ht', huV]
  obtain ⟨h, hh1, hh2⟩ : ∃ h : (baseAt t ⊗ Ag).left ⟶ (baseAt t' ⊗ A).left,
      h ≫ (snd (baseAt t') A).left = (snd (baseAt t) Ag).left ≫ φ ∧
      h ≫ (fst (baseAt t') A).left = (fst (baseAt t) Ag).left :=
    ⟨_, (GlobalTheory.AbLaw.SecBC.isPullback_snd A _).lift_fst _ _ hw2, (GlobalTheory.AbLaw.SecBC.isPullback_snd A _).lift_snd _ _ hw2⟩
  have hc' : ∀ _ : Fin 1, (snd (baseAt t) Ag).left ≫ φ = h ≫ (snd (baseAt t') A).left := fun _ => hh1.symm
  refine GlobalTheory.T.sectionBases_transfer_totalSpaceIso A Ag φ L hL (k : ℤ) R _ _ h hc' (isIso_compare u A Ag φ hφ.1 R _ _ hxy h hh1 hh2) hh2 m b'' b' ?_ hB.1 hB.2
  have hcomp : (homAt t ▷ Ag).left ≫ H = h ≫ (homAt t' ▷ A).left := by
    apply (GlobalTheory.AbLaw.SecBC.isPullback_snd A (overRes (T := baseOver (Sp Rg)) V)).hom_ext
    · rw [Category.assoc, hH1, Category.assoc, ← GlobalTheory.AbLaw.SecBC.snd_eq, ← Category.assoc, ← GlobalTheory.AbLaw.SecBC.snd_eq, hh1]
    · have e1 := GlobalTheory.AbLaw.SecBC.fst_eq Ag (homAt t)
      have e2 := GlobalTheory.AbLaw.SecBC.fst_eq A (homAt t')
      calc ((homAt t ▷ Ag).left ≫ H) ≫ (fst (overRes (T := baseOver (Sp Rg)) V) A).left
            = ((homAt t ▷ Ag).left ≫ (fst (overRes (T := baseOver S') ⊤) Ag).left) ≫ (⊤ : S'.Opens).ι ≫ uV := by
              rw [Category.assoc, hH2, Category.assoc]
        _ = (fst (baseAt t) Ag).left ≫ t ≫ (⊤ : S'.Opens).ι ≫ uV := by
              rw [e1]
              try simp [homAt]
        _ = (h ≫ (homAt t' ▷ A).left) ≫ (fst (overRes (T := baseOver (Sp Rg)) V) A).left := by
              rw [Category.assoc, e2, reassoc_of% hh2, ht']
              try simp [homAt]
  intro i
  apply GlobalTheory.SecTwist.sec_ext_loc
  intro y
  obtain ⟨j, hj⟩ : ∃ j, y ∈ (LPow Ag (L.pull φ) (k : ℤ) (baseAt t)).U j :=
    exists_chart (LB.isLB_linComb (LB.isLB_pull hL φ) _ _ : (LPow Ag (L.pull φ) (k : ℤ) (baseAt t)).IsLB) y
  refine ⟨j, hj, ?_⟩
  have hj1 := chart_le_res Ag (L.pull φ) (homAt t ▷ Ag) (whiskerRight_snd _ _) (k : ℤ) j hj
  have hj2 : h y ∈ (LPow A L (k : ℤ) (baseAt t')).U (fun k => j k PUnit.unit) := by
    have := (chartPullLinComb L φ (fun _ : Fin 1 => (snd (baseAt t) Ag).left)
      (fun _ : Fin 1 => (snd (baseAt t') A).left) (fun _ => (k : ℤ)) h hc').le j hj
    exact this
  have lhs : gs (𝟙 _) y ((LPow Ag (L.pull φ) (k : ℤ) (baseAt t)).U j) ((b' i).f j) =
      gs ((homAt t ▷ Ag).left ≫ H) y ((LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) V)).U (fun k => j k PUnit.unit))
        ((b i).f (fun k => j k PUnit.unit)) := by
    rw [hb' i j, GlobalTheory.AbLaw.SecBC.gs_rp _ _ (𝟙 _) y hj, Category.id_comp]
    exact GlobalTheory.SecTwist.gs_pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (overRes (T := baseOver S') ⊤) Ag).left)
      (fun _ : Fin 1 => (snd (overRes (T := baseOver (Sp Rg)) V) A).left) (fun _ => (k : ℤ)) H hc) (b i) (homAt t ▷ Ag).left y j hj1
  have rhs : gs (𝟙 _) y ((LPow Ag (L.pull φ) (k : ℤ) (baseAt t)).U j)
      ((GlobalTheory.SecTwist.pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (baseAt t) Ag).left)
        (fun _ : Fin 1 => (snd (baseAt t') A).left) (fun _ => (k : ℤ)) h hc') (b'' i)).f j) =
      gs (h ≫ (homAt t' ▷ A).left) y ((LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) V)).U (fun k => j k PUnit.unit))
        ((b i).f (fun k => j k PUnit.unit)) := by
    have e1 := GlobalTheory.SecTwist.gs_pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (baseAt t) Ag).left)
        (fun _ : Fin 1 => (snd (baseAt t') A).left) (fun _ => (k : ℤ)) h hc') (b'' i) (𝟙 _) y j hj
    rw [Category.id_comp] at e1
    refine e1.trans ?_
    erw [hb'' i (fun k => j k PUnit.unit)]
    exact GlobalTheory.AbLaw.SecBC.gs_rp _ _ h y hj2 _
  rw [lhs, rhs, hcomp]

theorem exists_basicOpen_secBasis : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → Out.Rigidified A L → Out.RelAmple A L → ∀ k : ℕ, 1 ≤ k → ∀ p : Sp Rg, ∃ f : Rg, p ∈ PrimeSpectrum.basicOpen f ∧ ∀ g : Rg, PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f → ∀ (Ag : Over (Sp (Localization.Away g))) [GrpObj Ag] [IsCommMonObj Ag] (φ : Ag.left ⟶ A.left), IsGrpPullback Ag A (spMap (algebraMap Rg (Localization.Away g))) φ → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (overRes (T := baseOver (Sp (Localization.Away g))) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp (Localization.Away g))) ⊤).left) (b' : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (baseAt t))), (∀ i, IsPullSec Ag (L.pull φ) (k : ℤ) (homAt t ▷ Ag) (whiskerRight_snd (homAt t) Ag) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) = ⊤) := by
  intro Rg _ _ A _ _ L hAb hL hRig hAmp k hk p
  obtain ⟨V, hpV, m, b, hb⟩ := GlobalTheory.AmpleSecBC.secBaseChange_relAmple (Sp Rg) A L hAb hL hRig hAmp k hk p
  have hx := exists_basicOpen_le (Rg := Rg) V p hpV
  refine ⟨hx.choose, hx.choose_spec.1, fun g hg Ag _ _ φ hφ => ⟨m, ?_⟩⟩
  have hu := exists_factor_away V _ g hx.choose_spec.2 hg
  exact secBasis_of_factor A L hL k V m b hb _ hu.choose hu.choose_spec Ag φ hφ

end GlobalTheory.HomFixLocBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectExtendOfPIsogenyDvrStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harrisTaylorObject_extend_of_pIsogeny_dvr : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (c : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (v : Sp V ⟶ Sp R) (o : Obj b N v) (oK o₁ : Obj b N (spMap (algebraMap V K) ≫ v)) (m : ObjMap oK o (spMap (algebraMap V K))) (ψ : oK.A ⟶ o₁.A), IsPIsog c oK o₁ ψ → ∃ o' : Obj b N v, Nonempty (ObjMap o₁ o' (spMap (algebraMap V K))) := by
  first | (exact @GlobalTheory.UPel.HT.ES.IsogDVR.exists_obj_extend_of_isPIsog) | (exact GlobalTheory.UPel.HT.ES.IsogDVR.exists_obj_extend_of_isPIsog) | (intros; apply GlobalTheory.UPel.HT.ES.IsogDVR.exists_obj_extend_of_isPIsog  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantSmoothProjFanNoSelfIntersections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.PolDeg.exists_inv_smooth_fan_noSelfInt : ∀ g : ℕ, ∃ φ : InvFun ℤ, IsPolFan (id : ℤ → ℤ) g φ ∧ NoSelfInt (id : ℤ → ℤ) g φ :=
  GlobalTheory.CompanionTheory.Ar.Fan.exists_smooth_fan_int
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLieBasisOfIsLocalRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.LogKS GlobalTheory.LogDR
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieLocalBasis

theorem exists_isLieBasis_of_isLocalRing : ∀ (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B]
    [IsCommMonObj B], Smooth B.hom → ∃ (n : ℕ) (y : Fin n → (epsR R ⟶ B)), IsLieBasis y := by
  intro R _ _ B _ _ hs
  haveI := hs
  obtain ⟨C⟩ := ReciprocityTheory.ChartRestriction.G.Chart.exists_chart B
  obtain ⟨g, hg, n, v, hv⟩ := ReciprocityTheory.ChartRestriction.G.Chart.exists_lieBasis_away C (IsLocalRing.maximalIdeal R)
  have hu : IsUnit g := by
    by_contra h
    exact hg ((IsLocalRing.mem_maximalIdeal g).2 h)
  let L := Localization.Away g
  let f' : L →+* R := IsLocalization.Away.lift (g := RingHom.id R) g hu
  have hf' : f'.comp (algebraMap R L) = RingHom.id R := RingHom.ext fun r => IsLocalization.Away.lift_eq (g := RingHom.id R) g hu r
  let G' := ReciprocityTheory.ChartRestriction.G.Chart.Gs B g
  have hpb : IsGrpPullback G' B (ReciprocityTheory.ChartRestriction.G.Chart.fB R L) (pullback.fst B.hom _) :=
    isGrpPullback_pullback B _
  have hcomp : spMap f' ≫ ReciprocityTheory.ChartRestriction.G.Chart.fB R L = 𝟙 (Sp R) := by
    simp only [spMap, ReciprocityTheory.ChartRestriction.G.Chart.fB]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hf']
    exact Spec.map_id _
  let φ' : B.left ⟶ G'.left := pullback.lift (𝟙 _) (B.hom ≫ spMap f') (by rw [Category.assoc, hcomp]; simp)
  have hφ : φ' ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _
  have hw : φ' ≫ G'.hom = B.hom ≫ spMap f' := pullback.lift_snd _ _ _
  haveI : IsMonHom (Iso.refl B).hom := inferInstanceAs (IsMonHom (𝟙 B))
  have hid : IsGrpPullback B B (𝟙 (Sp R)) (𝟙 B.left) := (isGrpPullback_of_iso (Iso.refl B)).congr rfl rfl
  have hn : IsGrpPullback B B (spMap f' ≫ ReciprocityTheory.ChartRestriction.G.Chart.fB R L) (φ' ≫ pullback.fst _ _) :=
    hid.congr hcomp.symm hφ.symm
  have hB : IsGrpPullback B G' (spMap f') φ' := hpb.cancel hn hw
  have hs' : Smooth G'.hom := by
    show Smooth (pullback.snd B.hom _)
    infer_instance
  obtain ⟨v', hv', -⟩ := GlobalTheory.exists_isLieBasis_baseChange L R f' G' B φ' hB hs' n v hv
  exact ⟨n, v', hv'⟩

end GlobalTheory.LieLocalBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledUniformisedModelThetaSystemTraitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_labelled_uniformisedModel_thetaSystem_trait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (ε : Matrix (Fin 8) (Fin 8) ℤ → (ρ.P.A ⟶ ρ.P.A)) (u' : Sp S.R ⟶ F.X), IsDiagEnd F W ρ.P u' ε → ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (T : Trait F) (ι : FractionRing T.V →+* PadicAlgCl p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) → spMap y₀ ≫ u' = spMap ι ≫ T.y → (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∃ (u : ρ.UTest p y₀) (l : u.Lab) (j : u.D.toPre.X ≃+ (Fin 8 → T.D.toPre.X)), (∀ χ, l.q χ = -Real.log ‖ι (algebraMap T.V (FractionRing T.V) T.ϖ)‖ * ((qW W T.β (j χ) : ℤ) : ℝ)) ∧ ∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (E : Matrix (Fin 8) (Fin 8) ℤ), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left ≫ u.φ = x.left ≫ u.φ ≫ (ε E).left → CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b) := by
  first | exact @GlobalTheory.Poinc.traitLabels | exact GlobalTheory.Poinc.traitLabels | (intros; apply GlobalTheory.Poinc.traitLabels <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivLabelledLatticesUnitaryTraits
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.UPoinc.exists_linearEquiv_labelled_of_uIsLabW : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (wi : UWit X), IsProjOver X.M.s → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct ct' : UCTrait X p z) (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X) (yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) ct'.T.P.D.toPre.X), UIsLabW X wi ct yy → UIsLabW X wi ct' yy' → ∃ e : ct.T.P.D.toPre.X ≃ₗ[𝓞 E] ct'.T.P.D.toPre.X, ∀ a μ, yy a = QuotientAddGroup.mk μ → yy' a = QuotientAddGroup.mk (e μ) := by
  intro E _ _ _ H Dw hpq l Xo cf C X wi hproj p _ z ct ct' yy yy' hl hl'
  obtain ⟨Y, U₀, EE, G, q, hO, hE, hqp, hpt, hconn, hlift⟩ :=
    GlobalTheory.UPoinc.exists_zhModel_proper_over_uSetup E H Dw hpq l Xo cf C X hproj
  obtain ⟨y, hy⟩ := hlift p z ct
  obtain ⟨y', hy'⟩ := hlift p z ct'
  obtain ⟨θ, hθ, hsm⟩ := _root_.GlobalTheory.UPoinc.GFib.labelled_lattices_equiv E H Dw hpq l Xo cf C X wi Y U₀ EE G q hO hE hqp hpt p z (hconn z)
    ct ct' y y' hy hy' yy yy' hl hl'
  exact ⟨θ.toLinearEquiv hsm, hθ⟩
end

