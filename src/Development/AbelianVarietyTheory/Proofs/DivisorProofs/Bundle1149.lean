module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle0006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle0005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFPrimeB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFCoreA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0166
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0140
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1108
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1114
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1111
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightKernelLowestType
section
noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

theorem highestWeightKernel_lowestType : AlgDatum := by
  intro n ε lam hg M _ _ E hE hU z hz0 hzp hz hcas S hSfd hSk hzS

  have hz' : IsKHWVec ε (fun a b => TensorProduct.map (E a b) LinearMap.id +
      LinearMap.lTensor M (sgE ε cpFock cmFock a b)) (gaW ε lam) z := by
    have e : (diagE ε (eT E) cpT cmT : Fin n → Fin n → Module.End ℂ (TensorProduct ℂ M (Fock n))) =
        fun a b => TensorProduct.map (E a b) LinearMap.id + LinearMap.lTensor M (sgE ε cpFock cmFock a b) := by
      funext a b
      delta diagE eT
      rw [sgE_cpT]
    rw [← e]; exact hz
  obtain ⟨s, hy0, hy⟩ := khw_extract ε hg.1 hz' hz0
  set y := tcoef ((fockBasis n).coord s) z with hydef

  have hs : s ⊆ lfPhysModes ε := by
    intro m hm
    by_contra hnm
    apply hy0
    refine tco_physSub_zero hzp hm fun hp => hnm ?_
    obtain ⟨x, rfl⟩ := finProdFinEquiv.surjective m
    rw [Equiv.symm_apply_apply] at hp
    exact (lf_mem_phys ε x.1 x.2).2 hp
  set Ph := gcPh ε s with hPh
  have hwt : gaW ε lam - fockWt ε s = lowK ε lam - phSum Ph := by
    rw [gc_wt_eq ε hs]
    funext a
    delta gaW lowK
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [hwt] at hy
  have hyS : y ∈ S := hzS s
  set V := kLowSpan ε E y with hV
  have hVS : V ≤ S := kLowSpan_le hSk hyS
  haveI : FiniteDimensional ℂ S := hSfd
  have hVfd : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le hVS
  have hVirr : IsKIrrHW ε E (lowK ε lam - phSum Ph) V := kLowSpan_kIrrHW hE hU hy hy0 hVfd

  set T : Submodule ℂ M := LinearMap.ker (casimir E - ((casVal lam : ℝ) : ℂ) • (1 : Module.End ℂ M)) with hT
  have hTk : IsKStableSub ε E T := by
    intro a b _ v hv
    rw [hT, LinearMap.mem_ker] at hv ⊢
    have hc := congrArg (fun X : Module.End ℂ M => X v) (casimir_comm hE a b)
    simp only [Module.End.mul_apply] at hc
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hv ⊢
    rw [hc, sub_eq_zero.1 hv, map_smul, sub_self]
  have hyT : y ∈ T := by
    rw [hT, LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [hcas s, sub_self]
  have hVT : V ≤ T := kLowSpan_le hTk hyT
  have hVc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v := by
    intro v hv
    have := hVT hv
    rw [hT, LinearMap.mem_ker] at this
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at this
    exact sub_eq_zero.1 this

  have hPh0 : Ph = ∅ := by
    by_contra hne
    exact dirac_sharp hg hE hU (gc_isPosNC ε hs) (Finset.nonempty_iff_ne_empty.2 hne) hVirr hVc
  rw [hPh0] at hVirr
  delta phSum at hVirr
  simp only [Finset.sum_empty, sub_zero] at hVirr
  refine ⟨V, hVirr, ?_, hVc⟩
  intro h0
  apply hy0
  have : y ∈ V := self_mem_kLowSpan y
  rw [h0] at this
  exact (Submodule.mem_bot ℂ).1 this

end GlobalTheory.PsCo.PcEF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertEigenvaluesIffThetaLiftInertLabels
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.InertTransferW

theorem complex_smul_left_cancel_of_ne_zero {V : Type*} [AddCommGroup V] [Module ℂ V] {a b : ℂ} {w : V} (hw : w ≠ 0) (h : a • w = b • w) :
    a = b := by
  by_contra hne
  apply hw
  have h2 : (a - b) • w = 0 := by rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)

theorem field_smul_left_cancel_of_ne_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {a b : K} {w : V} (hw : w ≠ 0)
    (h : a • w = b • w) : a = b := by
  by_contra hne
  apply hw
  have h2 : (a - b) • w = 0 := by rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)


set_option maxHeartbeats 4000000 in
theorem inertEigenvalues_iff_thetaLift_inertLabels_alt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → ∀ (j : Fin D.R.m) c c' (u u' : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) (x x' : (A3.A.fam.L j A3.A.μ0).S.Forms), (∀ i, (A3.liftI j A3.A.μ0).opAll i x = u i • x) → (∀ i, (A3.liftI j A3.A.μ0).opAll i x' = u' i • x') → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x') ∈ R.Wc' j c' → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0 → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x') ≠ 0 → ((∀ k, u (Sum.inr k) = u' (Sum.inr k)) ↔ (∀ P d, Good R.toRealDat A3.A.μ0 P → conjPl P = P → IsLab (Wc D j) P d → c P d = c' P d)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hLI hOk hW hE hS hTS hJunk j c c' u u' x x' hx hx' hc hc' hn hn'
  obtain ⟨hcore, hSF, -, hWc⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW hE
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  obtain ⟨hW0, hWops, -, -, -, -, hWev, -⟩ := _root_.GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt R.toRealDat F.lv2 hcore hS hX R.SF hSF j
  obtain ⟨hV, hVops, -⟩ := (GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 hcore.lev hcore.fam hcore.models).2 j A3.A.μ0
  have K : ∀ {cc : Pl D.host.E → List ℤ → ℂ} {z : (A3.A.fam.L j A3.A.μ0).S.Forms},
      R.thG j A3.A.μ0 (R.jV j A3.A.μ0 z) ∈ R.Wc' j cc → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 z) ≠ 0 →
      ∀ P, Good R.toRealDat A3.A.μ0 P → ∀ cV cW, GlobalTheory.Hk3.MatchW R.toRealDat j A3.A.μ0 P cV cW → ∀ σ : ℂ,
      hV P cV (R.jV j A3.A.μ0 z) = σ • R.jV j A3.A.μ0 z → σ = GlobalTheory.Hk3.evC (Wc D j) P (cc P) cW := by
    intro cc z hz hz0 P hP cV cW hM σ hσ
    rw [hWc j cc] at hz
    have h1 := (_root_.GlobalTheory.SysW.matched_operators_theta_intertwine R.toRealDat F.lv2 hcore hS hX R.SF hSF j A3.A.μ0 P hP cV cW hM hV hVops).1 hW0 hWops
      (R.jV j A3.A.μ0 z)
    have h4 := hWev cc P hP cW _ hz
    have h5 : σ • R.thG j A3.A.μ0 (R.jV j A3.A.μ0 z) = GlobalTheory.Hk3.evC (Wc D j) P (cc P) cW • R.thG j A3.A.μ0 (R.jV j A3.A.μ0 z) :=
      ((R.thG j A3.A.μ0).map_smul σ (R.jV j A3.A.μ0 z)).symm.trans ((congrArg (R.thG j A3.A.μ0) hσ).symm.trans (h1.trans h4))
    exact complex_smul_left_cancel_of_ne_zero hz0 h5
  have hrank : (Vc D j).rank = (A3.A.fam.L j A3.A.μ0).n := R.B.rankL j
  have V1 : ∀ (Q : A3.okI A3.A.μ0) (sq : List ℕ), Formalism.L2.Col.InertTypeOk (Vc D j).rank sq → ∀ f,
      R.jV j A3.A.μ0 (A3.heckeLI j A3.A.μ0 (Q, sq) f) =
        hV (R.plI Q) (Finsupp.single (labIn (Vc D j).rank sq) 1) (R.jV j A3.A.μ0 f) := by
    intro Q sq hsq f
    have tie := (hW.inert.hL j A3.A.μ0).some
    refine ((_root_.GlobalTheory.InertHeckeLift.inert_lifts R.toRealDat F.lv2 hcore.lev hcore.fam hcore.models j A3.A.μ0 _
      (fun k : A3.okI A3.A.μ0 × List ℕ => R.plI k.1) (fun k => labIn (Vc D j).rank k.2) (A3.heckeLI j A3.A.μ0)
      (fun k => Formalism.L2.Col.InertTypeOk (Vc D j).rank k.2) ?_ tie (Q, sq) hsq).2.2.2 hV hVops f)
    intro k hk
    obtain ⟨hg, hcj⟩ := (_root_.GlobalTheory.InertPlaces.inert_places_iff R F hW A3.A.μ0 (R.plI k.1)).1 ⟨k.1, k.1.2, rfl⟩
    refine ⟨hg, hcj, ?_⟩
    exact ((_root_.GlobalTheory.Hk3.labIn_selfDual_iff (Vc D j).rank (labIn (Vc D j).rank k.2)).2 ⟨k.2, hk.2.2, hk.1, hk.2.1, rfl⟩).2.1
  have hx0 : x ≠ 0 := by rintro rfl; exact hn (by simp)
  have hx0' : x' ≠ 0 := by rintro rfl; exact hn' (by simp)
  have hopx : ∀ k, A3.heckeLI j A3.A.μ0 k x = u (Sum.inr k) • x := fun k => hx (Sum.inr k)
  have hopx' : ∀ k, A3.heckeLI j A3.A.μ0 k x' = u' (Sum.inr k) • x' := fun k => hx' (Sum.inr k)
  constructor
  · intro hu P d hP hPc hd
    obtain ⟨Q, hQ, rfl⟩ := (_root_.GlobalTheory.InertPlaces.inert_places_iff R F hW A3.A.μ0 P).2 ⟨hP, hPc⟩
    obtain ⟨cV, hM⟩ := ((hTS _ hP hPc).2 j).2 (Finsupp.single d 1)
    obtain ⟨σ, h1, h2⟩ := _root_.GlobalTheory.InertEig.veig R.toRealDat hcore.models j A3.A.μ0 hV hVops _ hP hPc
      (fun sq => D.what₂.embLL (u (Sum.inr (⟨Q, hQ⟩, sq)))) (R.jV j A3.A.μ0 x) (R.jV j A3.A.μ0 x')
      (fun sq hsq => ⟨(V1 ⟨Q, hQ⟩ sq hsq x).symm.trans ((congrArg (R.jV j A3.A.μ0) (hopx _)).trans (map_smulₛₗ _ _ _)),
        (V1 ⟨Q, hQ⟩ sq hsq x').symm.trans ((congrArg (R.jV j A3.A.μ0) (hopx' _)).trans ((map_smulₛₗ _ _ _).trans
          (congrArg (fun a => D.what₂.embLL a • R.jV j A3.A.μ0 x') (hu _).symm)))⟩) cV
    have e1 := K hc hn _ hP cV _ hM σ h1
    have e2 := K hc' hn' _ hP cV _ hM σ h2
    unfold GlobalTheory.Hk3.evC at e1 e2
    rw [Finsupp.sum_single_index (by simp), if_pos hd, one_mul] at e1 e2
    exact e1.symm.trans e2
  · rintro hcc ⟨⟨Q0, hQ0⟩, sq⟩
    have hPl := (_root_.GlobalTheory.InertPlaces.inert_places_iff R F hW A3.A.μ0 (R.plI Q0)).1 ⟨Q0, hQ0, rfl⟩
    rcases hJunk.2 j A3.A.μ0 (⟨Q0, hQ0⟩, sq) with h0 | ⟨y, hy, hop⟩
    · have a1 : u (Sum.inr (⟨Q0, hQ0⟩, sq)) • x = 0 :=
        (hopx (⟨Q0, hQ0⟩, sq)).symm.trans ((LinearMap.congr_fun h0 x).trans (LinearMap.zero_apply x))
      have a2 : u' (Sum.inr (⟨Q0, hQ0⟩, sq)) • x' = 0 :=
        (hopx' (⟨Q0, hQ0⟩, sq)).symm.trans ((LinearMap.congr_fun h0 x').trans (LinearMap.zero_apply x'))
      rw [(smul_eq_zero.mp a1).resolve_right hx0, (smul_eq_zero.mp a2).resolve_right hx0']
    · have a1 : u (Sum.inr (⟨Q0, hQ0⟩, sq)) = u (Sum.inr (⟨Q0, hQ0⟩, y)) := by
        exact field_smul_left_cancel_of_ne_zero hx0 ((hopx (⟨Q0, hQ0⟩, sq)).symm.trans ((LinearMap.congr_fun hop x).trans (hopx (⟨Q0, hQ0⟩, y))))
      have a2 : u' (Sum.inr (⟨Q0, hQ0⟩, sq)) = u' (Sum.inr (⟨Q0, hQ0⟩, y)) := by
        exact field_smul_left_cancel_of_ne_zero hx0' ((hopx' (⟨Q0, hQ0⟩, sq)).symm.trans ((LinearMap.congr_fun hop x').trans (hopx' (⟨Q0, hQ0⟩, y))))
      rw [a1, a2]
      rw [← hrank] at hy
      obtain ⟨cW, hM⟩ := ((hTS _ hPl.1 hPl.2).2 j).1 (Finsupp.single (labIn (Vc D j).rank y) 1)
      have b1 := K hc hn _ hPl.1 _ cW hM _ ((V1 ⟨Q0, hQ0⟩ y hy x).symm.trans ((congrArg (R.jV j A3.A.μ0) (hopx _)).trans (map_smulₛₗ _ _ _)))
      have b2 := K hc' hn' _ hPl.1 _ cW hM _ ((V1 ⟨Q0, hQ0⟩ y hy x').symm.trans ((congrArg (R.jV j A3.A.μ0) (hopx' _)).trans (map_smulₛₗ _ _ _)))
      apply D.what₂.embLL.injective
      refine b1.trans (Eq.trans ?_ b2.symm)
      unfold GlobalTheory.Hk3.evC
      refine Finsupp.sum_congr fun d _ => ?_
      split_ifs with hd
      · rw [hcc _ d hPl.1 hPl.2 hd]
      · rfl

end GlobalTheory.InertTransferW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceNormGramInverseEqMulMatrix
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat

theorem nrmL_dlt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ u β : B.A, IsUnit (GlobalTheory.TwLat.gram e b β) → B.σ β = β * ((-1) ^ (m - 1) * u) → (nrmL m w (GlobalTheory.TwLat.dlt e b β)).val = GlobalTheory.TwLat.mulMat e b u := by
  intro E _ _ _ _ w hw K e hec _ _ B m b u β hG hβ
  let B' : GlobalTheory.UnitLemma.InvAlg K := { B with g := u }
  have hGc0 := GlobalTheory.GramTwistNorm.gram_map_conj B' (w.adicCompletion E) e (cj w) hec m β hβ b
  set G := gram e b β with hGdef
  set P := mulMat e b u with hP
  set Φ := GlobalTheory.Tw.Phi m (w.adicCompletion E) with hΦ
  set s : w.adicCompletion E := (-1) ^ (m - 1) with hs
  have hGc : G.map (cj w) = s • (Gᵀ * P) := hGc0
  have hGd : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hG
  have hΦT : Φᵀ * Φ = 1 := mul_eq_one_comm.1 (GlobalTheory.GramTwistNorm.phi_mul_transpose m)
  have hd : (dlt e b β).val = (G⁻¹)ᵀ * Φᵀ := by
    rw [dlt, dite_eq_left hG]
    change ((hG.unit⁻¹ : (Matrix (Fin m) (Fin m) (w.adicCompletion E))ˣ).val)ᵀ * Φᵀ = _
    rw [Matrix.coe_units_inv, IsUnit.unit_spec]
  have hdi : ((dlt e b β)⁻¹).val = Φ * Gᵀ := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hd, Matrix.mul_assoc, ← Matrix.mul_assoc Φᵀ, hΦT, Matrix.one_mul, ← Matrix.transpose_mul,
      Matrix.mul_nonsing_inv G hGd, Matrix.transpose_one]
  have hΦΦ : Φᵀ * Φᵀ = s • (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) := by
    rw [← Matrix.transpose_mul, hΦ, GlobalTheory.GramTwistNorm.phi_mul_self, Matrix.transpose_smul, Matrix.transpose_one]
  have hθ : (thetaGL m (cj w) (dlt e b β)).val = Φ * (((dlt e b β)⁻¹).val.map (cj w))ᵀ * Φᵀ := rfl
  have hGG : (G⁻¹)ᵀ * Gᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv G hGd, Matrix.transpose_one]
  have hss : s * s = 1 := by rw [hs, ← mul_pow, neg_one_mul, neg_neg, one_pow]
  rw [nrmL, if_neg hw, Units.val_mul, hθ, hdi, Matrix.map_mul, hΦ, GlobalTheory.GramTwistNorm.phi_map, ← hΦ,
    Matrix.transpose_mul, Matrix.transpose_map, Matrix.transpose_transpose, hGc, hd]
  calc (G⁻¹)ᵀ * Φᵀ * (Φ * (s • (Gᵀ * P) * Φᵀ) * Φᵀ)
      = s • (((G⁻¹)ᵀ * Gᵀ) * P * (Φᵀ * Φᵀ)) + (0 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) := by
        rw [add_zero]
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Φᵀ Φ, hΦT, Matrix.one_mul]
    _ = P := by
        rw [add_zero, hGG, hΦΦ, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hss, one_smul]

end GlobalTheory.TwLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfFixedVectorsAdelicLevelNeBotOfLocalLevel
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FixLev
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem ext_fin {x y : UA E n} (hx : x ∈ finU (E := E) (n := n)) (hy : y ∈ finU (E := E) (n := n)) (h : ∀ v : Pl E, cLoc v x = cLoc v y) : x = y := by
  have hx' : cInf x = 1 := hx
  have hy' : cInf y = 1 := hy
  apply Subtype.ext
  apply ga_ext
  · exact hx'.trans hy'.symm
  · exact Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v =>
      by
        have := congrArg (fun z : GLw n v => (z : Matrix (Fin n) (Fin n) (v.adicCompletion E)) i j) (h v)
        exact this)

theorem integral_eventually (g : UA E n) : ∀ᶠ v in cofinite, ∀ i j : Fin n,
    (cLoc v g) i j ∈ v.adicCompletionIntegers E ∧ (cLoc v g)⁻¹ i j ∈ v.adicCompletionIntegers E := by
  have h1 : ∀ x : Af E, ∀ᶠ v in cofinite, pLoc E v x ∈ v.adicCompletionIntegers E := fun x => x.2
  have h2 : ∀ i j : Fin n, ∀ᶠ v in cofinite,
      (cLoc v g) i j ∈ v.adicCompletionIntegers E ∧ (cLoc v g)⁻¹ i j ∈ v.adicCompletionIntegers E := by
    intro i j
    filter_upwards [h1 (pFin E ((g : GA E n) i j)), h1 (pFin E (((g⁻¹ : UA E n) : GA E n) i j))] with v hv hv'
    refine ⟨hv, ?_⟩
    rw [← map_inv]
    exact hv'
  exact Filter.eventually_all.2 fun i => Filter.eventually_all.2 (h2 i)

def fib (B : Finset (Pl E)) : Set (Pl E) :=
  {u | ∃ t ∈ B, u.under (𝓞 (maximalRealSubfield E)) = t.under (𝓞 (maximalRealSubfield E))}

theorem fib_closed (B : Finset (Pl E)) (u v : Pl E)
    (h : u.under (𝓞 (maximalRealSubfield E)) = v.under (𝓞 (maximalRealSubfield E))) (hu : u ∈ fib B) : v ∈ fib B := by
  obtain ⟨t, ht, e⟩ := hu
  exact ⟨t, ht, h.symm.trans e⟩

def stabU (φ : UA E n → ℂ) : Subgroup (UA E n) where
  carrier := {x | RU E n x φ = φ}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem one_entry_mem (v : Pl E) (i j : Fin n) : (1 : GLw n v) i j ∈ v.adicCompletionIntegers E := by
  change (1 : Matrix (Fin n) (Fin n) (v.adicCompletion E)) i j ∈ _
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem local_fixed (S : Set (Pl E)) (hS : IsSection S) (K' : ∀ w : Pl E, Subgroup (UL n w)) (φ : UA E n → ℂ)
    (hφ : ∀ w ∈ S, ∀ x ∈ locU n w, (∃ k ∈ K' w, k.1 = cLoc w x) → RU E n x φ = φ) (B : Finset (Pl E)) :
    ∀ h : UA E n, h ∈ finU (E := E) (n := n) → (∀ w ∈ S, ∃ k ∈ K' w, k.1 = cLoc w h) → (∀ v, v ∉ fib B → cLoc v h = 1) →
      h ∈ stabU φ := by
  induction B using Finset.induction_on with
  | empty =>
    intro h hfin _ h1
    have : h = 1 := ext_fin hfin (one_mem _) fun v => by
      rw [h1 v (by rintro ⟨t, ht, _⟩; simp at ht), map_one]
    rw [this]
    exact one_mem _
  | insert t B _ ih =>
    intro h hfin hK h1
    obtain ⟨wt, ⟨hwtS, hwt⟩, _⟩ := hS t
    obtain ⟨x, hxfin, hx⟩ := GlobalTheory.T.exists_finiteAdelicUnitaryPoint_cut_to_fibreUnion E n (fib {t}) (fib_closed {t}) h hfin
    have hxloc : x ∈ locU n wt := by
      refine Subgroup.mem_inf.2 ⟨hxfin, Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => ?_⟩
      rw [MonoidHom.mem_ker, hx u, if_neg]
      rintro ⟨t', ht', e⟩
      rw [Finset.mem_singleton] at ht'
      subst ht'
      exact hu (e.trans hwt.symm)
    have hwtf : wt ∈ fib {t} := ⟨t, Finset.mem_singleton_self t, hwt⟩
    have hxS : x ∈ stabU φ := by
      obtain ⟨k, hk, hkx⟩ := hK wt hwtS
      refine hφ wt hwtS x hxloc ⟨k, hk, ?_⟩
      rw [hx wt, if_pos hwtf, hkx]
    have hrest : x⁻¹ * h ∈ stabU φ := by
      refine ih _ (mul_mem (inv_mem hxfin) hfin) ?_ ?_
      · intro w hw
        rw [map_mul, map_inv, hx w]
        split_ifs
        · exact ⟨1, one_mem _, by rw [inv_mul_cancel]; rfl⟩
        · rw [inv_one, one_mul]; exact hK w hw
      · intro v hv
        rw [map_mul, map_inv, hx v]
        split_ifs with hvt
        · exact inv_mul_cancel _
        · rw [inv_one, one_mul]
          refine h1 v ?_
          rintro ⟨t', ht', e⟩
          rcases Finset.mem_insert.1 ht' with rfl | ht'
          · exact hvt ⟨t', Finset.mem_singleton_self _, e⟩
          · exact hv ⟨t', ht', e⟩
    have : h = x * (x⁻¹ * h) := by group
    rw [this]
    exact mul_mem hxS hrest

theorem inf_fixed_globLev_ne_bot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S →
    ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' →
    ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → HasLevel S π K' → π ⊓ fixed (RF E n) (globLev S K') ≠ ⊥ := by
  intro E _ _ _ n S hS K' _ π hπ hL
  obtain ⟨φ, hφπ, hφ0, hφfix⟩ := hL
  have hlev := (hπ.aut φ hφπ).level
  have key : ∀ g : finU (E := E) (n := n), g ∈ globLev S K' → (g : UA E n) ∈ stabU φ := by
    intro g hg
    have hgS : ∀ w ∈ S, ∃ k ∈ K' w, k.1 = cLoc w (g : UA E n) := by
      intro w hw
      have h1 := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg w) hw
      rw [Subgroup.mem_comap] at h1
      obtain ⟨k, hk, e⟩ := Subgroup.mem_map.1 h1
      exact ⟨k, hk, e⟩
    obtain ⟨T, hT⟩ := GlobalTheory.T.mem_open_nhd_one_of_integral_eq_one_on_finset E n _ hlev (by simp)
    have hbad := Filter.eventually_cofinite.1 (integral_eventually (g : UA E n))
    let B : Finset (Pl E) := T ∪ hbad.toFinset
    obtain ⟨x, hxfin, hx⟩ := GlobalTheory.T.exists_finiteAdelicUnitaryPoint_cut_to_fibreUnion E n (fib B) (fib_closed B) (g : UA E n) g.2
    have hxS : x ∈ stabU φ := by
      refine local_fixed S hS K' φ hφfix B x hxfin ?_ ?_
      · intro w hw
        rw [hx w]
        split_ifs
        · exact hgS w hw
        · exact ⟨1, one_mem _, rfl⟩
      · intro v hv
        rw [hx v, if_neg hv]
    have hc : ∀ v, cLoc v (x⁻¹ * (g : UA E n)) = if v ∈ fib B then 1 else cLoc v (g : UA E n) := by
      intro v
      rw [map_mul, map_inv, hx v]
      split_ifs
      · exact inv_mul_cancel _
      · rw [inv_one, one_mul]
    have hint : ∀ v, v ∉ fib B → ∀ i j : Fin n, (cLoc v (g : UA E n)) i j ∈ v.adicCompletionIntegers E ∧
        (cLoc v (g : UA E n))⁻¹ i j ∈ v.adicCompletionIntegers E := by
      intro v hv
      by_contra hc'
      exact hv ⟨v, Finset.mem_union_right _ (hbad.mem_toFinset.2 hc'), rfl⟩
    have hrest : x⁻¹ * (g : UA E n) ∈ stabU φ := by
      have := hT ⟨x⁻¹ * (g : UA E n), mul_mem (inv_mem hxfin) g.2⟩ ?_ ?_ ?_
      · exact this
      · intro v hv
        change cLoc v (x⁻¹ * (g : UA E n)) = 1
        rw [hc v, if_pos ⟨v, Finset.mem_union_left _ hv, rfl⟩]
      · intro v i j
        change (cLoc v (x⁻¹ * (g : UA E n))) i j ∈ _
        rw [hc v]
        split_ifs with hv
        · exact one_entry_mem v i j
        · exact (hint v hv i j).1
      · intro v i j
        change (cLoc v (x⁻¹ * (g : UA E n)))⁻¹ i j ∈ _
        rw [hc v]
        split_ifs with hv
        · rw [inv_one]; exact one_entry_mem v i j
        · exact (hint v hv i j).2
    have : (g : UA E n) = x * (x⁻¹ * (g : UA E n)) := by group
    rw [this]
    exact mul_mem hxS hrest
  intro hbot
  have hmem : φ ∈ π ⊓ fixed (RF E n) (globLev S K') := by
    refine ⟨hφπ, ?_⟩
    intro h
    change RU E n ((h : finU (E := E) (n := n)) : UA E n) φ = (1 : ℂˣ) • φ
    rw [one_smul]
    exact key h h.2
  rw [hbot] at hmem
  exact hφ0 ((Submodule.mem_bot ℂ).1 hmem)

end GlobalTheory.FixLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPairTermEqPointSumAnyTrivialisationStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kottwitzPair_term_eq_pointSum_any_trivialisation : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (δ z : Gr G r), IsNrm G r P.atP δ z → P.term Kf f r K φ = P.termAt Kf f r K φ x t hx δ z := by
  first | (exact @GlobalTheory.LKMid.Pair.term_eq_termAt) | (exact GlobalTheory.LKMid.Pair.term_eq_termAt) | (intros; apply GlobalTheory.LKMid.Pair.term_eq_termAt <;> assumption)
end

