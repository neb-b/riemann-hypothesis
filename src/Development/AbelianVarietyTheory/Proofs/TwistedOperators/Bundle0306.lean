module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0292
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralIndicatorProjFinSmul
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

noncomputable section
namespace GlobalTheory.TrOpTensor

theorem exists_sum_indicator {X W : Type} [TopologicalSpace X] [T2Space X] [AddCommGroup W] [Module ℂ W]
    (F : X → W) (hF : IsLocallyConstant F) (hc : HasCompactSupport F) :
    ∃ s : Finset W, (∀ r ∈ s, IsOpen (F ⁻¹' {r}) ∧ IsCompact (closure (F ⁻¹' {r}))) ∧
      ∀ x, F x = ∑ r ∈ s, (F ⁻¹' {r}).indicator (fun _ => (1 : ℂ)) x • r := by
  classical
  have hfin : (Set.range F).Finite := by
    haveI : CompactSpace ↥(tsupport F) := isCompact_iff_compactSpace.1 hc
    have h1 : (Set.range (fun x : tsupport F => F x)).Finite :=
      (hF.comp_continuous continuous_subtype_val).range_finite
    refine (h1.union (Set.finite_singleton 0)).subset ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ tsupport F
    · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
    · exact Or.inr (image_eq_zero_of_notMem_tsupport hx)
  refine ⟨hfin.toFinset.filter (· ≠ 0), fun r hr => ?_, fun x => ?_⟩
  · have hr0 : r ≠ 0 := (Finset.mem_filter.1 hr).2
    refine ⟨hF.isOpen_fiber r, hc.of_isClosed_subset isClosed_closure
      (closure_minimal (fun x hx => subset_tsupport F ?_) (isClosed_tsupport F))⟩
    rw [Function.mem_support, show F x = r from hx]
    exact hr0
  · by_cases h0 : F x = 0
    · rw [h0]
      symm
      refine Finset.sum_eq_zero fun r hr => ?_
      have hx : x ∉ F ⁻¹' {r} := fun hx => (Finset.mem_filter.1 hr).2 ((show F x = r from hx).symm.trans h0)
      rw [Set.indicator_of_notMem hx, zero_smul]
    · rw [Finset.sum_eq_single (F x)]
      · rw [Set.indicator_of_mem (show x ∈ F ⁻¹' {F x} from rfl), one_smul]
      · intro r _ hne
        rw [Set.indicator_of_notMem (s := F ⁻¹' {r}) (fun hx => hne (show F x = r from hx).symm), zero_smul]
      · intro hn
        exact absurd (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ⟨x, rfl⟩, h0⟩) hn

theorem integralOp_eq_sum {G W : Type} [Group G] [MeasurableSpace G] [AddCommGroup W] [Module ℂ W]
    (ν : Measure G) (σ : Representation ℂ G W) (b : G → ℂ) (A : W →ₗ[ℂ] W)
    (hA : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ b A) (w : W) (s : Finset W)
    (hs : ∀ r ∈ s, MeasurableSet ((fun h => b h • σ h w) ⁻¹' {r}) ∧ ν ((fun h => b h • σ h w) ⁻¹' {r}) ≠ ⊤)
    (hsum : ∀ h, b h • σ h w = ∑ r ∈ s, ((fun h => b h • σ h w) ⁻¹' {r}).indicator (fun _ => (1 : ℂ)) h • r) :
    A w = ∑ r ∈ s, ((ν ((fun h => b h • σ h w) ⁻¹' {r})).toReal : ℂ) • r := by
  set F := fun h => b h • σ h w with hF
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  have hpt : ∀ h, b h * l (σ h w) = ∑ r ∈ s, (F ⁻¹' {r}).indicator (fun _ => l r) h := by
    intro h
    rw [← smul_eq_mul, ← map_smul]
    change l (b h • σ h w) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum h, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_smul, smul_eq_mul]
    by_cases hh : h ∈ F ⁻¹' {r}
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem hh, one_mul]
    · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem hh, zero_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, (hA w l).2, map_sum, integral_congr_ae (.of_forall hpt),
    integral_finsetSum _ fun r hr => (integrableOn_const (hs r hr).2).integrable_indicator (hs r hr).1,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun r hr => ?_
  rw [integral_indicator_const _ (hs r hr).1, map_smul, Measure.real, Complex.real_smul, smul_eq_mul, sub_self]

theorem measure_eq_of_isFinMeas {D : D7} (V : HSp D) {μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)}
    {νF : Measure (GFin D.sp.cm.sig V.gram)} (hF : IsRestrictedProdFin D.sp.cm.sig V.gram (frameLat V) μf νF)
    {ν : Measure (GfC V)} (hν : IsFinMeas V μf ν) (s : Set (GfC V)) (hs : IsCompact (closure s)) :
    ν s = νF ((finPtsEquiv D.sp.cm.sig V.gram) ⁻¹' s) := _root_.GlobalTheory.FinMeasEq.finMeas_eq D V μf νF hF ν hν s hs

theorem integral_indicator_projFin_smul {D : D7} (V : HSp D) {μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)}
    {μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)} {μ : Measure (GA D V)}
    (hμ : IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ)
    {νF : Measure (GFin D.sp.cm.sig V.gram)} (hF : IsRestrictedProdFin D.sp.cm.sig V.gram (frameLat V) μf νF)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (B : Set (GFin D.sp.cm.sig V.gram)) (hB : MeasurableSet B) (hB' : νF B ≠ ⊤)
    (a : (∀ w, GArch D.sp.cm.sig V.gram w) → E) (ha : Integrable a (Measure.pi μa)) :
    Integrable (fun g : GA D V => B.indicator (fun _ => (1 : ℂ)) (projFin D.sp.cm.sig V.gram g) •
        a fun w => projArch D.sp.cm.sig V.gram w g) μ ∧
    ∫ g, B.indicator (fun _ => (1 : ℂ)) (projFin D.sp.cm.sig V.gram g) •
        a (fun w => projArch D.sp.cm.sig V.gram w g) ∂μ = (νF B).toReal • ∫ x, a x ∂Measure.pi μa :=
  _root_.GlobalTheory.TrProdInt.integral_indicatorFin_smul_arch D V μa μf μ hμ νF hF E B hB hB' a ha


open scoped Classical in
theorem integral_pi_dsRep {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) [∀ w, SigmaFinite (μa w)]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Φ : ContinuousMultilinearMap ℂ M.H H) (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (y : ∀ τ, M.H τ)
    (hfa : ∀ τ, Integrable (fun z => fa (placeOf D τ) z • dsRep M τ z (y τ)) (μa (placeOf D τ))) :
    Integrable (fun x : ∀ w, GArch D.sp.cm.sig V.gram w =>
        (∏ w, fa w (x w)) • Φ (fun τ => dsRep M τ (x (placeOf D τ)) (y τ))) (Measure.pi μa) ∧
    ∫ x, (∏ w, fa w (x w)) • Φ (fun τ => dsRep M τ (x (placeOf D τ)) (y τ)) ∂Measure.pi μa =
      Φ fun τ => ∫ z, fa (placeOf D τ) z • dsRep M τ z (y τ) ∂μa (placeOf D τ) := by
  haveI : ∀ τ, CompleteSpace (M.H τ) := fun τ => (isIrrUnitary_dsRep M τ).complete
  have hgen := _root_.GlobalTheory.MultilinFubini.integral_multilinear_pi D.what₂.Tau (fun τ => GArch D.sp.cm.sig V.gram (placeOf D τ))
    (fun τ => μa (placeOf D τ)) M.H H Φ (fun τ z => fa (placeOf D τ) z • dsRep M τ z (y τ)) hfa
  obtain ⟨e, he⟩ : ∃ e : D.what₂.Tau ≃ InfinitePlace D.host.F, e = Equiv.ofBijective _ (placeOf_bijective D) := ⟨_, rfl⟩
  subst he
  have hP := measurePreserving_piCongrLeft μa (Equiv.ofBijective _ (placeOf_bijective D))
  set P := MeasurableEquiv.piCongrLeft (fun w => GArch D.sp.cm.sig V.gram w)
    (Equiv.ofBijective _ (placeOf_bijective D)) with hPdef
  have hcomp : ∀ x' : ∀ τ, GArch D.sp.cm.sig V.gram (placeOf D τ),
      (∏ w, fa w (P x' w)) • Φ (fun τ => dsRep M τ (P x' (placeOf D τ)) (y τ)) =
        Φ fun τ => fa (placeOf D τ) (x' τ) • dsRep M τ (x' τ) (y τ) := by
    intro x'
    have hx : ∀ τ, P x' (placeOf D τ) = x' τ := fun τ =>
      Equiv.piCongrLeft_apply_apply (fun w => GArch D.sp.cm.sig V.gram w)
        (Equiv.ofBijective _ (placeOf_bijective D)) x' τ
    rw [ContinuousMultilinearMap.map_smul_univ,
      ← Equiv.prod_comp (Equiv.ofBijective _ (placeOf_bijective D)) (fun w => fa w (P x' w))]
    refine congrArg₂ (· • ·) (Finset.prod_congr rfl fun τ _ => ?_) (congrArg Φ (funext fun τ => ?_))
    · exact congrArg (fa (placeOf D τ)) (hx τ)
    · exact congrArg (fun z => dsRep M τ z (y τ)) (hx τ)
  have hfun : ((fun x : ∀ w, GArch D.sp.cm.sig V.gram w =>
      (∏ w, fa w (x w)) • Φ (fun τ => dsRep M τ (x (placeOf D τ)) (y τ))) ∘ P) =
      fun x' => Φ fun τ => fa (placeOf D τ) (x' τ) • dsRep M τ (x' τ) (y τ) := funext hcomp
  refine ⟨?_, ?_⟩
  · rw [← hP.integrable_comp_emb P.measurableEmbedding, hfun]
    exact hgen.1
  · rw [← hP.integral_comp' (fun x : ∀ w, GArch D.sp.cm.sig V.gram w =>
      (∏ w, fa w (x w)) • Φ (fun τ => dsRep M τ (x (placeOf D τ)) (y τ))), ← hgen.2]
    exact integral_congr_ae (.of_forall hcomp)


open scoped Classical in
theorem apply_homFinDS {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {W : Type} [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ (GfC V) W} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {π : GA D V →* (H →L[ℂ] H)} {T : W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H H}
    (hT : T ∈ homFinDS σ M π ⊤) (g : GA D V) (w : W) (y : ∀ τ, M.H τ) :
    π g (T w y) = T (σ (toFin V g) w) fun τ => dsRep M τ (projArch D.sp.cm.sig V.gram (placeOf D τ) g) (y τ) := by
  have h := mem_homTensorPi.1 hT
  have e := _root_.GlobalTheory.TrAct.toInf_apply_homDS D V S M H π ⊤ (T (σ (toFin V g) w)) (hT.1 _) g y
  calc π g (T w y) = π (toInf V g : GA D V) (π (toFin V g : GA D V) (T w y)) := by
        conv_lhs => rw [← toInf_mul_toFin g]
        rw [map_mul]; rfl
    _ = π (toInf V g : GA D V) (T (σ (toFin V g) w) y) := by rw [h.2.1]; rfl
    _ = _ := e

end GlobalTheory.TrOpTensor

namespace GlobalTheory.TrOpTensor

theorem locallyConstant_smul {D : D7} (V : HSp D) {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}
    (hff : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff) {W : Type} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GfC V) W} (hσ : GlobalTheory.PRep.IsSmooth σ) (w : W) :
    IsLocallyConstant (fun h => finFn V ff h • σ h w) ∧ HasCompactSupport (fun h => finFn V ff h • σ h w) := by
  obtain ⟨hlc, hcs⟩ := GlobalTheory.FinTrace.finFn_mem_SB V hff
  have h2 : IsLocallyConstant fun h : GfC V => σ h w := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun x => ⟨(fun h => x⁻¹ * h) ⁻¹' {g | σ g w = w},
      (hσ w).preimage (continuous_const.mul continuous_id), by simp, fun x' hx' => ?_⟩
    have e : x' = x * (x⁻¹ * x') := by group
    rw [e, map_mul, Module.End.mul_apply, show σ (x⁻¹ * x') w = w from hx']
  exact ⟨hlc.comp₂ h2 (fun a b => a • b), hcs.smul_right⟩

theorem finFn_toFin {D : D7} (V : HSp D) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) (g : GA D V) :
    finFn V ff (toFin V g) = ∏ᶠ v, ff v (proj D.sp.cm.sig V.gram v g) := by
  unfold finFn
  refine finprod_congr fun v => congrArg (ff v) ?_
  change proj D.sp.cm.sig V.gram v (ofFin D.sp.cm.sig V.gram (projFin D.sp.cm.sig V.gram g)) = _
  rw [proj_ofFin, projFinLoc_projFin]

theorem opTensor : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)), IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ → ∀ ν, IsFinMeas V μf ν → ∀ fa ff, (∀ w, fa w ∈ CcArch D.sp.cm.sig V.gram w) → IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsUnitaryRep π → ∀ T ∈ homFinDS σ M π ⊤, ∀ A, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V ff) A → ∀ w y, repOp π μ (tensor D.sp.cm.sig V.gram fa ff) (T w y) = T (A w) fun τ => repOp (dsRep M τ) (μa (placeOf D τ)) (fa (placeOf D τ)) (y τ) := by
  intro D V S M μa μf μ hμ ν hν fa ff hfa hff W _ _ σ hσ H _ _ _ π hπ T hT A hA w y
  have := hμ.haar
  have := hμ.haar_arch
  have := hμ.haar_loc
  have hfc : ∀ w', Continuous (fa w') := fun w' =>
    continuous_of_mem_ccSmooth (continuous_archCoord _ _ w') (hfa w')
  have hfs : ∀ w', HasCompactSupport (fa w') := fun w' => (hfa w').1
  have hD := fun τ => (isUnitaryRep_dsRep M τ).isRepOp (μ := μa (placeOf D τ)) (hfc (placeOf D τ)) (hfs (placeOf D τ))
  obtain ⟨hcf, hcs⟩ := continuous_of_mem_ccAd (tensor_mem_ccAd hfa hff)
  have hR := hπ.isRepOp (μ := μ) hcf hcs
  obtain ⟨hlc, hcF⟩ := locallyConstant_smul V hff hσ w
  obtain ⟨s, hs, hsum⟩ := exists_sum_indicator _ hlc hcF
  obtain ⟨νF, hνF⟩ := (existsUnique_isRestrictedProdFin D.sp.cm.sig V.gram (frameLat V) μf
    hμ.eventually_eq_one).exists
  have := hν.1
  set F : GfC V → W := fun h => finFn V ff h • σ h w with hF
  have hfin : ∀ r ∈ s, ν (F ⁻¹' {r}) ≠ ⊤ := fun r hr =>
    ((measure_mono subset_closure).trans_lt (hs r hr).2.measure_lt_top).ne
  have hAw := integralOp_eq_sum ν σ (finFn V ff) A hA w s
    (fun r hr => ⟨(hs r hr).1.measurableSet, hfin r hr⟩) hsum
  set a : W → (∀ w', GArch D.sp.cm.sig V.gram w') → H := fun r x =>
    (∏ w', fa w' (x w')) • T r (fun τ => dsRep M τ (x (placeOf D τ)) (y τ)) with ha
  have hsf : ∀ w', SigmaFinite (μa w') := fun w' => inferInstance
  have hpi := fun r => integral_pi_dsRep M μa (T r) fa y fun τ => (hD τ (y τ)).1
  set B : W → Set (GFin D.sp.cm.sig V.gram) := fun r => (finPtsEquiv D.sp.cm.sig V.gram) ⁻¹' (F ⁻¹' {r}) with hB
  have hBm : ∀ r ∈ s, MeasurableSet (B r) := fun r hr =>
    ((hs r hr).1.preimage (finPtsEquiv D.sp.cm.sig V.gram).continuous).measurableSet
  have hνB : ∀ r ∈ s, νF (B r) = ν (F ⁻¹' {r}) := fun r hr =>
    (measure_eq_of_isFinMeas V hνF hν _ (hs r hr).2).symm
  have hBf : ∀ r ∈ s, νF (B r) ≠ ⊤ := fun r hr => by rw [hνB r hr]; exact hfin r hr
  have hL := fun r (hr : r ∈ s) => integral_indicator_projFin_smul V hμ hνF (B r) (hBm r hr) (hBf r hr) (a r) (hpi r).1
  have hpt : ∀ g : GA D V, tensor D.sp.cm.sig V.gram fa ff g • π g (T w y) =
      ∑ r ∈ s, (B r).indicator (fun _ => (1 : ℂ)) (projFin D.sp.cm.sig V.gram g) •
        a r (fun w' => projArch D.sp.cm.sig V.gram w' g) := by
    intro g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [apply_homFinDS hT, tensor, ← finFn_toFin, mul_smul, ← ContinuousMultilinearMap.smul_apply,
      ← LinearMap.map_smul, hsum, map_sum, ContinuousMultilinearMap.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_smul, ContinuousMultilinearMap.smul_apply, smul_comm]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [(hR (T w y)).2, integral_congr_ae (.of_forall hpt), integral_finsetSum _ fun r hr => (hL r hr).1,
    hAw, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [(hL r hr).2, (hpi r).2, map_smul, ContinuousMultilinearMap.smul_apply, hνB r hr, Complex.coe_smul]
  congr 2
  funext τ
  exact ((hD τ (y τ)).2).symm

end GlobalTheory.TrOpTensor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsWeilDatumCompGroupSwappingSymplecticEquiv
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SwapWeil

variable {D : D7}

theorem symplOH_of {A B C E : HSp D} (e : WO A B → WO C E) (h : ∀ x y, symplO C E (e x) (e y) = symplO A B x y)
    (x y : WO A B) : symplOH C E (e x) (e y) = symplOH A B x y := by
  simp only [symplOH, h]

theorem theta_pull {ψ : AddChar (AF D.host.F) ℂ} {A B C E : HSp D} (e : WO A B ≃ₗ[AE D] WO C E) (hc : Continuous e)
    (hrat : ∀ x, x ∈ ratL B A → e x ∈ ratL E C) (hs : ∀ x y, symplO C E (e x) (e y) = symplO A B x y)
    (hinf : ∀ x : WO A B, x.map (infPart D) = 0 → (e x).map (infPart D) = 0)
    (hfin : ∀ x : WO A B, x.map (finPart D) = 0 → (e x).map (finPart D) = 0)
    {f : WO C E → ℂ} (hf : IsThetaFunO ψ C E f) : IsThetaFunO ψ A B (fun w => f (e w)) := {
  quasi γ w := by
    obtain ⟨γ', hγ'⟩ := hrat (ratW B A γ) ⟨γ, rfl⟩
    have e1 : e (ratW B A γ) = ratW E C γ' := hγ'.symm
    show f (e (ratW B A γ + w)) = _
    rw [map_add (f := _), e1, hf.quasi, ← e1, symplOH_of (⇑e) hs]
  level := by
    obtain ⟨U, hU, k⟩ := hf.level
    refine ⟨U.comap (e : WO A B →+ WO C E), hU.preimage hc, fun u hu h0 => ?_⟩
    funext w
    have := congrFun (k (e u) hu (hinf u h0)) (e w)
    simp only [heisO] at this ⊢
    rw [map_add (f := _), ← symplOH_of (⇑e) hs]
    exact this
  cont := hf.cont.comp hc
  smooth k L hL h0 w := by
    have := hf.smooth k ((e : WO A B →+ WO C E).comp L) (hc.comp hL) (fun t => hfin _ (h0 t)) (e w)
    simpa only [AddMonoidHom.comp_apply, AddMonoidHom.coe_coe, map_add (f := _)] using this }

theorem isDetAt_inv {e : AE D} (he : e * e = e) {V V₂ : HSp D} {g : GA D V} {k : GA D V₂} {x : (AE D)ˣ}
    (hx : IsDetAt e V g x) (hk : (mt V₂ k).det = (mt V g⁻¹).det) : IsDetAt e V₂ k x⁻¹ := by
  unfold IsDetAt at hx
  have hd : (mt V g⁻¹).det * (mt V g).det = 1 := by
    have hm : mt V g⁻¹ * mt V g = 1 := by simp [Formalism.L2.Theta.mt]
    rw [← Matrix.det_mul, hm, Matrix.det_one]
  show ((x⁻¹ : (AE D)ˣ) : AE D) = e * (mt V₂ k).det + (1 - e)
  rw [hk]
  apply Units.inv_eq_of_mul_eq_one_left
  rw [hx]
  linear_combination e * hd + ((mt V g⁻¹).det * (mt V g).det - (mt V g⁻¹).det - (mt V g).det + 1) * he

def swapOm {S T S' T' : HSp D} (L : WO S' T' ≃ₗ[AE D] WO S T) (φ : GA D S' →* GA D T) (φ' : GA D T' →* GA D S)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ) where
  toFun p :=
    { toFun := fun F w => om (φ' p.2, φ p.1) (fun x => F (L.symm x)) (L w)
      map_add' := fun F G => by
        funext w
        have e : (fun x => (F + G) (L.symm x)) = (fun x => F (L.symm x)) + fun x => G (L.symm x) := rfl
        show om _ (fun x => (F + G) _) _ = om _ (fun x => F _) _ + om _ (fun x => G _) _
        rw [e, map_add (f := _)]; rfl
      map_smul' := fun c F => by
        funext w
        have e : (fun x => (c • F) (L.symm x)) = c • fun x => F (L.symm x) := rfl
        show om _ (fun x => (c • F) _) _ = c • om _ (fun x => F _) _
        rw [e, map_smul]; rfl }
  map_one' := by
    refine LinearMap.ext fun F => funext fun w => ?_
    have e : ((φ' (1 : GA D S' × GA D T').2, φ (1 : GA D S' × GA D T').1) : GA D S × GA D T) = 1 := by
      simp
    simp only [LinearMap.coe_mk, AddHom.coe_mk, e, map_one, Module.End.one_apply, LinearEquiv.symm_apply_apply]
  map_mul' p q := by
    refine LinearMap.ext fun F => funext fun w => ?_
    have e : ((φ' (p * q).2, φ (p * q).1) : GA D S × GA D T) = (φ' p.2, φ p.1) * (φ' q.2, φ q.1) := by
      simp
    simp only [LinearMap.coe_mk, AddHom.coe_mk, e, map_mul, Module.End.mul_apply, LinearEquiv.apply_symm_apply]

theorem swapOm_apply {S T S' T' : HSp D} (L : WO S' T' ≃ₗ[AE D] WO S T) (φ : GA D S' →* GA D T)
    (φ' : GA D T' →* GA D S) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S') (h : GA D T')
    (F : WO S' T' → ℂ) : swapOm L φ φ' om (g, h) F = fun w => om (φ' h, φ g) (fun x => F (L.symm x)) (L w) :=
  rfl

end GlobalTheory.SwapWeil


set_option maxHeartbeats 1600000 in
open GlobalTheory.SwapWeil in
theorem GlobalTheory.SwapWeil.isWeilDatumO_swap : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T S' T' : HSp D), S'.rank = T.rank → T'.rank = S.rank →
    ∀ (L : WO S' T' ≃ₗ[AE D] WO S T) (φ : GA D S' →* GA D T) (φ' : GA D T' →* GA D S),
    Continuous L → Continuous L.symm → (∀ x, L x ∈ ratL T S ↔ x ∈ ratL T' S') →
    (∀ x y, symplO S T (L x) (L y) = symplO S' T' x y) →
    (∀ x, (L x).map (infPart D) = 0 ↔ x.map (infPart D) = 0) → (∀ x, (L x).map (finPart D) = 0 ↔ x.map (finPart D) = 0) →
    Continuous φ → Continuous φ' → (∀ γ ∈ GQ S', φ γ ∈ GQ T) → (∀ γ ∈ GQ T', φ' γ ∈ GQ S) →
    (∀ g h x, L (actO S' T' g h x) = actO S T (φ' h) (φ g) (L x)) →
    (∀ e g, SuppAt e S' g → SuppAt e T (φ g)) → (∀ e h, SuppAt e T' h → SuppAt e S (φ' h)) →
    (∀ g, (Formalism.L2.Theta.mt T (φ g)).det = (Formalism.L2.Theta.mt S' g⁻¹).det) → (∀ h, (Formalism.L2.Theta.mt S (φ' h)).det = (Formalism.L2.Theta.mt T' h⁻¹).det) →
    ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT ω →
      ∃ ω' : GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ), IsWeilDatumO ψ S' T' χT χS ω' ∧
        ∀ g h (f : WO S T → ℂ), ω' (g, h) (fun u => f (L u)) = fun u => ω (φ' h, φ g) f (L u) := by
  intro D ψ S T S' T' hST hTS L φ φ' hLc hLsc hrat hs hinf hfin hφ hφ' hGQ hGQ' hact hsupp hsupp' hdet hdet' χS χT om H
  have hs' : ∀ x y, symplO S' T' (L.symm x) (L.symm y) = symplO S T x y := fun x y => by
    rw [← hs, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have thL : ∀ G : WO S T → ℂ, IsThetaFunO ψ S T G → IsThetaFunO ψ S' T' (fun w => G (L w)) := fun G hG =>
    theta_pull L hLc (fun x hx => (hrat x).2 hx) hs (fun x hx => (hinf x).2 hx) (fun x hx => (hfin x).2 hx) hG
  have thLs : ∀ F : WO S' T' → ℂ, IsThetaFunO ψ S' T' F → IsThetaFunO ψ S T (fun x => F (L.symm x)) := fun F hF =>
    theta_pull L.symm hLsc (fun x hx => (hrat (L.symm x)).1 (by rwa [LinearEquiv.apply_symm_apply])) hs'
      (fun x hx => (hinf (L.symm x)).1 (by rwa [LinearEquiv.apply_symm_apply]))
      (fun x hx => (hfin (L.symm x)).1 (by rwa [LinearEquiv.apply_symm_apply])) hF
  have hratS : ∀ x, L.symm.toAddEquiv x ∈ ratL T' S' ↔ x ∈ ratL T S := fun x => by
    show L.symm x ∈ ratL T' S' ↔ x ∈ ratL T S
    rw [← hrat, LinearEquiv.apply_symm_apply]
  refine ⟨swapOm L φ φ' om, ⟨H.std, H.hecT, H.hecS, by rw [hST]; exact H.resT, by rw [hTS]; exact H.resS,
    fun p F hF => ?_, fun g h w₀ F hF => ?_, fun γ hγ γ' hγ' F hF => ?_, fun F hF w => ?_,
    fun μ 𝓕 hμ h𝓕 p F hF => ?_, fun e he g h hg hh x y hx hy => ?_⟩, fun g h f => ?_⟩
  · obtain ⟨g, h⟩ := p
    exact thL _ (H.om_pres _ _ (thLs F hF))
  · have e1 : (fun x => heisO ψ S' T' w₀ F (L.symm x)) = heisO ψ S T (L w₀) (fun x => F (L.symm x)) := by
      funext x
      simp only [heisO]
      rw [← symplOH_of (⇑L) hs (L.symm x) w₀, LinearEquiv.apply_symm_apply, map_add (f := _), LinearEquiv.symm_apply_apply]
    funext w
    show om (φ' h, φ g) (fun x => heisO ψ S' T' w₀ F (L.symm x)) (L w) =
      heisO ψ S' T' (actO S' T' g h w₀) (swapOm L φ φ' om (g, h) F) w
    rw [e1, H.om_heis _ _ _ _ (thLs F hF), ← hact]
    simp only [heisO, swapOm_apply, map_add (f := _), symplOH_of (⇑L) hs]
  · show om (φ' γ', φ γ) (fun x => F (L.symm x)) (L 0) = F 0
    rw [L.map_zero, H.om_aut _ (hGQ' γ' hγ') _ (hGQ γ hγ) _ (thLs F hF)]
    exact congrArg F L.symm.map_zero
  · exact (H.om_cont _ (thLs F hF) (L w)).comp ((hφ'.comp continuous_snd).prodMk (hφ.comp continuous_fst))
  · haveI : BorelSpace (WO S T) := ⟨rfl⟩
    haveI : BorelSpace (WO S' T') := ⟨rfl⟩
    obtain ⟨ν, hν, h𝓖, hu⟩ := GlobalTheory.WeilSrc.haar_pull L.symm.toAddEquiv hLsc hLc (ratL T S) (ratL T' S') hratS μ 𝓕 hμ h𝓕
    have e1 := hu fun w => ‖swapOm L φ φ' om p F w‖ₑ ^ 2
    have e2 := hu fun w => ‖F w‖ₑ ^ 2
    have e3 : ∀ x, swapOm L φ φ' om p F (L.symm.toAddEquiv x) = om (φ' p.2, φ p.1) (fun x => F (L.symm x)) x :=
      fun x => by
        show om _ _ (L (L.symm x)) = _
        rw [LinearEquiv.apply_symm_apply]
    simp only [e3] at e1
    rw [← e1, ← e2]
    exact H.om_unit ν _ hν h𝓖 _ _ (thLs F hF)
  · obtain ⟨r, hr, Hs⟩ := H.om_split e he (φ' h) (φ g) (hsupp' e h hh) (hsupp e g hg) y⁻¹ x⁻¹
      (isDetAt_inv he.1 hy (hdet' h)) (isDetAt_inv he.1 hx (hdet g))
    refine ⟨r, hr, fun ℓ hℓ F hF => ?_⟩
    let ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ := ℓ ∘ₗ LinearMap.funLeft ℂ ℂ L
    have hinv : ∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ G, IsThetaFunO ψ S T G →
        ℓ' (heisO ψ S T u G) = ℓ' G := by
      intro u hu G hG
      show ℓ (fun w => heisO ψ S T u G (L w)) = ℓ (fun w => G (L w))
      have e1 : (fun w => heisO ψ S T u G (L w)) = heisO ψ S' T' (L.symm u) (fun w => G (L w)) := by
        funext w
        simp only [heisO]
        rw [← symplOH_of (⇑L) hs w (L.symm u), map_add (f := _), LinearEquiv.apply_symm_apply]
      rw [e1]
      refine hℓ _ ?_ _ (thL G hG)
      have hu' : cA D e • u = u := by
        ext i j
        exact hu i j
      intro i j
      have k := congrArg (fun M : WO S' T' => M i j) (congrArg L.symm hu')
      simpa only [LinearEquiv.map_smul, Matrix.smul_apply, smul_eq_mul] using k
    have main := Hs ℓ' hinv _ (thLs F hF)
    have e1 : ℓ' (fun x => F (L.symm x)) = ℓ F := by
      show ℓ (fun w => F (L.symm (L w))) = ℓ F
      simp only [LinearEquiv.symm_apply_apply]
    have hfac : splitFacO χS χT y⁻¹ x⁻¹ = splitFacO χT χS x y := by
      unfold splitFacO
      rw [map_inv, map_inv, inv_inv, mul_comm]
    rw [e1, hfac] at main
    exact main
  · funext u
    show om _ (fun x => f (L (L.symm x))) _ = _
    simp only [LinearEquiv.apply_symm_apply]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityValuesContinuousBoundedHeckeConj
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenOnto.ConjVal

theorem values_conj_hecke : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ForStage D fun c _ s => (∀ (u : s.CC c) v, Continuous (PiLocalization₂.val u v) ∧ (∃ C : ℝ, ∀ g, ‖PiLocalization₂.val u v g‖ ≤ C) ∧ (∀ γ ∈ GQ s.V, ∀ g, PiLocalization₂.val u v (γ * g) = PiLocalization₂.val u v g) ∧ (∀ k ∈ s.J, ∀ g, PiLocalization₂.val u v (g * k) = PiLocalization₂.val u v g) ∧ GlobalTheory.Grow.RapidDec s.V (PiLocalization₂.val u v)) ∧ ∀ (R : Finset (GA D s.V)) (f : GA D s.V → ℂ), heckeLin s.V R (fun g => conj (f g)) = fun g => conj (heckeLin s.V R f g) := by
  intro hP D c hc j _ s _
  refine ⟨fun u v => ?_, fun R f => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.ConjVal.good_val hP hc.inf
      (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) u.2 v
    refine ⟨h1, h2, h3, fun k hk g => by simpa using h4 k hk g, ?_⟩
    exact (GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP D s.V s.par s.M c.θ hc.inf _ _ _ u.2 v).2.2
  · funext g
    set_option synthInstance.maxHeartbeats 100000 in
      simp [heckeLin, map_sum]

end GlobalTheory.EvenOnto.ConjVal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalClassTermEqVolumeMulProdOrbitalIntegralsStatement
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalClassTerm_eq_volume_mul_prod_orbitalIntegrals : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsFullLattice E L], ∀ μa μf μ, IsRestrictedProd σ J L μa μf μ → ∀ fa ff, (∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w)) → IsFinFamily σ J L ff → ∀ dta dtf dt, IsTorusMeas P dta dtf dt → ∀ γ : GRat σ J, γ.1.1.charpoly = P.1 → ∀ (qf : ∀ v : HeightOneSpectrum (𝓞 F), XSet P (Fv F v) J) (qa : ∀ w : InfinitePlace F, XSet P w.Completion J), (∀ v, HasCls P _ J (proj σ J v (ratEmb σ J γ)) (qf v).1) → (∀ w, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) (qa w).1) → Integrable (descend (ratPts σ J) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (ratPts σ J) (ratEmb σ J γ) (tensor σ J fa ff))) (quotMeasure (ratPts σ J) μ) ∧ ∫ q, descend (ratPts σ J) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (ratPts σ J) (ratEmb σ J γ) (tensor σ J fa ff)) q ∂quotMeasure (ratPts σ J) μ = ((torVol P dt).toReal : ℂ) * ((∏ᶠ v, orbCls (μf v) (dtf v) (ff v) (qf v)) * ∏ w, orbCls (μa w) (dta w) (fa w) (qa w)) := by
  intro F E _ _ _ _ _ σ hcm r P J hJ L _ μa μf μ hμ fa ff hfa hff dta dtf dt hdt γ hγ qf qa hqf hqa
  exact GlobalTheory.TrClassTerm.class_term F E σ hcm r P J hJ L μa μf μ hμ fa ff hfa hff dta dtf dt hdt γ hγ qf qa hqf hqa
end

