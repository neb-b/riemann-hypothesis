module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasOrbIntTensorOfHasOrbInt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0406
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeightedOrbitalIntegralTypeTestVanish
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AnisotropicTorusFundamentalDomainFiniteMeasure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0186

@[expose] public section

open MeasureTheory Set Filter GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms (plusAlg genAlg)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH NoFixed radical)
open GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.NonFieldType

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}

theorem localClause {T : TypeDataG V} {U : AuxiliaryPlaceHermitianSpace V} {μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)}
    {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ} (hμf : ∀ v, (μf v).IsHaarMeasure) (hf : IsTestFin T U μf ff)
    {γ : GRat D.sp.cm.sig V.gram} (hγ : IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1) : LocalClause T μf ff γ := by
  intro k K _ _ e i
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.FactorSplit.factorIdem_orthSplit_rank _root_.GlobalTheory.RegSSObj.regularSemisimple D V γ hγ.1 k K e i hγ
  refine ⟨h1, h2, fun v hv dt hdt => ?_⟩
  obtain ⟨hee, -, -, hcomm, hpos, hlt⟩ := h1
  have hγε : γ.1.1 * factorIdem e i = factorIdem e i * γ.1.1 :=
    hcomm _ (Algebra.self_mem_adjoin_singleton _ _)
  have h := _root_.GlobalTheory.TwistLocal.weighted_orbital_vanish _root_.GlobalTheory.TypeConstTerm.typeConstTermVanish D V T U μf ff hf v (hμf v) γ (factorIdem e i) hγ.1 hee hγε hpos hlt hv 1
    continuous_const (fun _ _ _ => rfl) (fun _ _ _ => rfl) dt
  have e1 : (fun x => (1 : GLoc D.sp.cm.sig V.gram v → ℂ) x *
      ff v (x⁻¹ * proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ) * x)) = conjFn (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ)) (ff v) := by
    funext x; exact one_mul _
  rw [e1] at h
  exact h

theorem isMulCommutative_cent_ratEmb {γ : GRat D.sp.cm.sig V.gram} (hγ : IsRegSS γ.1.1) :
    IsMulCommutative (cent (ratEmb D.sp.cm.sig V.gram γ)) := by
  refine ⟨⟨fun x y => Subtype.ext (GAd_ext _ _ (fun w => ?_) fun v => ?_)⟩⟩
  · have h := (isMulCommutative_cent_HA (isRegSS_projArch_ratEmb hγ w)).is_comm.comm
      (centMap (projArch D.sp.cm.sig V.gram w) _ x) (centMap (projArch D.sp.cm.sig V.gram w) _ y)
    have h' := congrArg Subtype.val h
    simpa [centMap] using h'
  · have h := (isMulCommutative_cent_HA (isRegSS_proj_ratEmb hγ v)).is_comm.comm
      (centMap (proj D.sp.cm.sig V.gram v) _ x) (centMap (proj D.sp.cm.sig V.gram v) _ y)
    have h' := congrArg Subtype.val h
    simpa [centMap] using h'

theorem ratEmb_mem_GQ (γ : GRat D.sp.cm.sig V.gram) : ratEmb D.sp.cm.sig V.gram γ ∈ GQ V := by
  rw [GlobalTheory.AdelicU.GQ_eq, ← GlobalTheory.AdelicU.range_ratEmb]; exact ⟨γ, rfl⟩

theorem covol_lt_top {γ : GRat D.sp.cm.sig V.gram} (hγ : IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1)
    (dt : Measure (cent (ratEmb D.sp.cm.sig V.gram γ))) [dt.IsHaarMeasure] (𝓣 : Set (cent (ratEmb D.sp.cm.sig V.gram γ)))
    (h𝓣 : IsFundamentalDomain ((GQ V).subgroupOf (cent (ratEmb D.sp.cm.sig V.gram γ))) 𝓣 dt) : dt 𝓣 < ⊤ := by
  obtain ⟨hreg, k, K, iF, iA, he, -, hK⟩ := hγ
  exact _root_.GlobalTheory.AnisoCovol.covol_lt_top _root_.GlobalTheory.RegSSObj.regularSemisimple D V γ hreg k K he hK dt 𝓣 h𝓣


instance discreteTopology_subgroupOf_cent (γ : GA D V) : DiscreteTopology ((GQ V).subgroupOf (cent γ)) :=
  DiscreteTopology.of_continuous_injective (f := fun t : (GQ V).subgroupOf (cent γ) => (⟨t.1.1, t.2⟩ : GQ V))
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    (fun s t h => Subtype.ext (Subtype.ext (by have h' := congrArg Subtype.val h; exact h')))

set_option maxHeartbeats 4000000 in
theorem zeroClause {T : TypeDataG V} (hH : HypH (k := fun v : T.S => ResF v.1) T.τ)
    {μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)} {μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)}
    {μ : Measure (GA D V)} {fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ} {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}
    {γ : GRat D.sp.cm.sig V.gram} (hγ : IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1)
    (hL : LocalClause T μf ff γ) (hP : ProductClause μa μf μ fa ff (ratEmb D.sp.cm.sig V.gram γ)) :
    ZeroClause μ (tensor D.sp.cm.sig V.gram fa ff) (ratEmb D.sp.cm.sig V.gram γ) := by
  intro 𝓕 h𝓕
  haveI hla : ∀ w, LocallyCompactSpace (cent (projArch D.sp.cm.sig V.gram w (ratEmb D.sp.cm.sig V.gram γ))) :=
    fun _ => (isClosed_cent _).locallyCompactSpace
  haveI hlf : ∀ v, LocallyCompactSpace (cent (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ))) :=
    fun _ => (isClosed_cent _).locallyCompactSpace
  have hR := restrGroup_cent (frameLat V) (ratEmb D.sp.cm.sig V.gram γ)
  let K0 : ∀ v, TopologicalSpace.PositiveCompacts (cent (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ))) :=
    fun v => ⟨⟨_, hR.isCompact_K v⟩, by
      simp only [(hR.isOpen_K v).interior_eq]; exact ⟨1, one_mem _⟩⟩
  let dta : ∀ w, Measure (cent (projArch D.sp.cm.sig V.gram w (ratEmb D.sp.cm.sig V.gram γ))) := fun _ => Measure.haar
  let dtf : ∀ v, Measure (cent (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ))) :=
    fun v => Measure.haarMeasure (K0 v)
  haveI : ∀ w, (dta w).IsHaarMeasure := fun _ => inferInstance
  haveI : ∀ v, (dtf v).IsHaarMeasure := fun _ => inferInstance
  have h1 : ∀ᶠ v in cofinite, dtf v ((stabLoc D.sp.cm.sig V.gram (frameLat V) v).subgroupOf
      (cent (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ)))) = 1 :=
    .of_forall fun v => Measure.haarMeasure_self (K₀ := K0 v)
  obtain ⟨dt, hdt, -⟩ := existsUnique_isCentProd (L := frameLat V) (ratEmb D.sp.cm.sig V.gram γ) dta dtf h1
  have h𝓣 := isFundamentalDomain_stdDom ((GQ V).subgroupOf (cent (ratEmb D.sp.cm.sig V.gram γ))) dt
  obtain ⟨-, oa, ob, -, hob, hone, -, hcls⟩ := hP dta dtf dt hdt _ h𝓣
  obtain ⟨-, k, K, iF, iA, ⟨e⟩, hk, -⟩ := hγ
  obtain ⟨hsplit, -, hloc⟩ := hL k K e ⟨0, by omega⟩
  obtain ⟨v, hv⟩ := hH _ hsplit.2.2.2.2.1 hsplit.2.2.2.2.2
  have h0 := hloc v hv (dtf v.1) inferInstance
  have hob0 : ob v.1 = 0 := (hob v.1).2.symm.trans h0.2
  have hfp : ∏ᶠ v, ob v = 0 := finprod_eq_zero ob v.1 hob0 (Filter.eventually_cofinite.1 hone)
  have h := hcls 𝓕 h𝓕
  rwa [hfp, mul_zero, mul_zero] at h


end GlobalTheory.NonFieldType
