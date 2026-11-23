module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0523
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0582
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0148
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0334
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0455
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0525
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0433
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0415
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0500
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterMtEqSmulOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0382
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0428
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDatumBoxTensorLineOverVacuum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AeCharUnramAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ShapeSecond

variable {D : D7}


set_option maxHeartbeats 2000000 in
theorem ae_charUnramAt (χ : (AE D)ˣ →* Circle) (hχ : Continuous χ) :
    ∀ᶠ v : GlobalTheory.FinPl.Pl D in Filter.cofinite, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χ v := by
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D χ hχ
  filter_upwards [GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D (N : D.host.E)⁻¹] with v hv x h1 h2 h3 h4
  have ha : (x : AE D) - 1 ∈ GlobalTheory.FinPl.intAt D (· = v) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show infPart D ((x : AE D) - 1) = 0
      rw [RingHom.map_sub, h1, RingHom.map_one, sub_self]
    · refine (Submodule.mem_iInf _).2 fun w => ?_
      show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w.1 (finPart D ((x : AE D) - 1)) = 0
      rw [RingHom.map_sub, RingHom.map_sub, h2 w.1 w.2, RingHom.map_one, RingHom.map_one, sub_self]
    · rw [RingHom.map_sub, RingHom.map_one]
      exact sub_mem h3 (GlobalTheory.HeckeConj.one_mem_intAE D)
  have e : (x : AE D) - 1 = N • (incA D (N : D.host.E)⁻¹ * ((x : AE D) - 1)) := by
    rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (incA D), ← RingHom.map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), RingHom.map_one, one_mul]
  have key : ∃ z ∈ intAE D, finPart D (x : AE D) - 1 = N • z := by
    refine ⟨_, (hv _ ha).2, ?_⟩
    have e2 : finPart D ((x : AE D) - 1) = finPart D (x : AE D) - 1 := by rw [RingHom.map_sub, RingHom.map_one]
    rw [← e2]
    exact (congrArg (finPart D) e).trans ((finPart D).toAddMonoidHom.map_nsmul _ _)
  exact hker x ⟨h1, h3, h4⟩ key

end GlobalTheory.FinPl.ShapeSecond
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledLatticeHeightFunProperties
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP
variable {D : D7} (A : HSp D) (L : Lat A) (a : GL (Fin A.rank) (AE D))

theorem hgtL_eq_prod (hL : IsSelfDualC A L) (ha : IsMaj A a) (g : GA D A) : hgtL A L a g = (∏ w, hgtArch D.sp.cm.sig (dblSp A).gram w (Formalism.UG.bc (compInf _ _ w) a)
      (ioH _ D.sp.cm.sig (gram_hdbl A) (projArch D.sp.cm.sig A.gram w g, 1))) *
      ∏ᶠ v, hgtFin D.sp.cm.sig (dblSp A).gram L v (ioH _ D.sp.cm.sig (gram_hdbl A) (proj D.sp.cm.sig A.gram v g, 1)) := by
  haveI : Submodule.IsFullLattice D.host.E L := GlobalTheory.ProjXCols.selfDual_isFullLattice A L hL
  have hI := _root_.GlobalTheory.Core.Rk.IP.hasIwasawa_KAd_selfDual D A L a hL ha
  simpa only [hgtL, io, proj_ioH, projArch_ioH, map_one] using
    hI.hgtAd_eq (isCMExt_host D) (io A (g, 1))

theorem isOpen_openOff (hL : IsSelfDualC A L) (Sf : Finset (FinPl D)) : IsOpen (openOff A L Sf) := by
  haveI : Submodule.IsFullLattice D.host.E L := GlobalTheory.ProjXCols.selfDual_isFullLattice A L hL
  let H : Subgroup (GA D A) := ⨅ (v) (_ : v ∉ Sf), (stabLoc D.sp.cm.sig A.gram L v).comap (proj D.sp.cm.sig A.gram v)
  have hH : (H : Set (GA D A)) = openOff A L Sf := by
    ext g
    simp [H, openOff, Subgroup.mem_iInf, Subgroup.mem_comap]
  rw [← hH]
  refine Subgroup.isOpen_mono (H₁ := levelOpen D.sp.cm.sig A.gram L) (fun g hg => ?_) (isOpen_levelOpen _ _ _)
  simp only [H, Subgroup.mem_iInf, Subgroup.mem_comap]
  exact fun v _ => (mem_levelOpen.1 hg) v

theorem continuous_hgtL (hL : IsSelfDualC A L) (ha : IsMaj A a) : Continuous (hgtL A L a) := by
  haveI : Submodule.IsFullLattice D.host.E L := GlobalTheory.ProjXCols.selfDual_isFullLattice A L hL
  haveI := t2Space_adeleRing' (F := D.host.F)
  have hI := _root_.GlobalTheory.Core.Rk.IP.hasIwasawa_KAd_selfDual D A L a hL ha
  exact (hI.continuous_hgtH continuous_absE (isCompact_KAd (isCMExt_host D))).comp
    ((continuous_io A).comp (continuous_id.prodMk continuous_const))

theorem hgtL_le_one (hL : IsSelfDualC A L) (ha : IsMaj A a) (g : GA D A) : hgtL A L a g ≤ 1 := by
  rw [hgtL_eq_prod A L a hL ha g]
  refine mul_le_one' (Finset.prod_le_one' fun w _ => ?_) ?_
  · have := _root_.GlobalTheory.Core.Rk.HgtArch.hgtW_le_one D A a ha w (projArch D.sp.cm.sig A.gram w g)
    simpa [GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW] using this
  · by_cases hf : (Function.mulSupport fun v => hgtFin D.sp.cm.sig (dblSp A).gram L v
        (ioH _ D.sp.cm.sig (gram_hdbl A) (proj D.sp.cm.sig A.gram v g, 1))).Finite
    · rw [finprod_eq_prod _ hf]
      exact Finset.prod_le_one' fun v _ => _root_.GlobalTheory.Core.Rk.IP.hgtFin_ioAt_le_one D A L hL v _
    · rw [finprod_of_infinite_mulSupport hf]

theorem hgtL_eq_prod_off (hL : IsSelfDualC A L) (ha : IsMaj A a) (Sf : Finset (FinPl D)) (g : GA D A)
    (hg : g ∈ openOff A L Sf) : (hgtL A L a g : ℝ) = (∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW A a w (projArch D.sp.cm.sig A.gram w g)) *
      ∏ v ∈ Sf, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV A L v (proj D.sp.cm.sig A.gram v g) := by
  haveI : Submodule.IsFullLattice D.host.E L := GlobalTheory.ProjXCols.selfDual_isFullLattice A L hL
  rw [hgtL_eq_prod A L a hL ha g]
  have hsub : (Function.mulSupport fun v => hgtFin D.sp.cm.sig (dblSp A).gram L v
      (ioH _ D.sp.cm.sig (gram_hdbl A) (proj D.sp.cm.sig A.gram v g, 1))) ⊆ (Sf : Set (FinPl D)) := by
    intro v hv
    by_contra hvS
    exact hv (hgtH_of_mem (continuous_absEv v) (isCompact_KFin v)
      ((ioH_mem_KFin (gram_hdbl A)).2 ⟨hg v hvS, one_mem _⟩))
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  push_cast
  rfl

theorem hgtL_props : ∀ (D : D7) (A : HSp D) (L : Lat A) (a : GL (Fin A.rank) (AE D)), IsSelfDualC A L → IsMaj A a → Continuous (hgtL A L a) ∧ (∀ g, 0 < hgtL A L a g ∧ hgtL A L a g ≤ 1) ∧ ∀ (Sf : Finset (FinPl D)), IsOpen (openOff A L Sf) ∧ ∀ g ∈ openOff A L Sf, (hgtL A L a g : ℝ) = (∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW A a w (projArch D.sp.cm.sig A.gram w g)) * ∏ v ∈ Sf, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV A L v (proj D.sp.cm.sig A.gram v g) := by
  intro D A L a hL ha
  exact ⟨continuous_hgtL A L a hL ha, fun g => ⟨hgtH_pos _, hgtL_le_one A L a hL ha g⟩,
    fun Sf => ⟨isOpen_openOff A L hL Sf, fun g hg => hgtL_eq_prod_off A L a hL ha Sf g hg⟩⟩

end GlobalTheory.Core.Rk.IP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingEulerProductFarRight
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.EulerProd

open Filter Topology

theorem limit_eq_prod_mul {ι : Type} (S : Finset ι) (f : ι → ℂ) (I : Finset ι → ℂ) {P J : ℂ}
    (hP : HasProd (fun v : {v : ι // v ∉ (S : Set ι)} => f v.1) P) (hJ : Tendsto I atTop (𝓝 J))
    (h : ∀ T U : Finset ι, Disjoint S T → (∀ u, u ∈ U ↔ u ∈ S ∨ u ∈ T) → I U = (∏ v ∈ T, f v) * I S) :
    J = P * I S := by
  classical
  let e : {v : ι // v ∉ (S : Set ι)} ↪ ι := Function.Embedding.subtype _
  have ht : Tendsto (fun T : Finset {v : ι // v ∉ (S : Set ι)} => S ∪ T.map e) atTop atTop := by
    refine tendsto_atTop.2 fun b => (eventually_ge_atTop (b.subtype fun v => v ∉ (S : Set ι))).mono fun T hT u hu => ?_
    by_cases hS : u ∈ S
    · exact Finset.mem_union_left _ hS
    · exact Finset.mem_union_right _ (Finset.mem_map.2 ⟨⟨u, hS⟩, hT (Finset.mem_subtype.2 hu), rfl⟩)
  have h1 := hJ.comp ht
  have h2 : Tendsto (fun T : Finset {v : ι // v ∉ (S : Set ι)} => (∏ v ∈ T, f v.1) * I S) atTop (𝓝 (P * I S)) :=
    Tendsto.mul_const _ hP
  refine tendsto_nhds_unique h1 (h2.congr fun T => ?_)
  rw [Function.comp_apply, h (T.map e) _ ?_ fun u => Finset.mem_union, Finset.prod_map]
  · rfl
  · refine Finset.disjoint_left.2 fun u hu hu' => ?_
    obtain ⟨w, -, rfl⟩ := Finset.mem_map.1 hu'
    exact w.2 hu

theorem bounded_of_isParamFun (hP : GlobalTheory.Published.CuspRapidDecay) {D : D7} (hB : ParamBoundOn D (fun _ => True))
    {θ : InfFam D} {A : HSp D} {cA : CptF A} {L : Lat A} (hθ : IsInfFam θ) (hL : IsSelfDualC A L)
    (m : Measure (GA D A)) (hm : m.IsHaarMeasure) {Sf : Finset (FinPl D)} {u : GA D A → ℂ} (hu : u ∈ A0 θ A cA)
    {par : GlobalTheory.LFun.Fam D.host.E} (hpar : GlobalTheory.LFun.IsParamFun D.sp.cm.sig A.gram L (Sf : Set (FinPl D)) u par) :
    GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (Sf : Set (FinPl D))) par A.rank ((A.rank : ℝ) / 2) := by
  intro w hw
  have hv : w.under (𝓞 D.host.F) ∉ Sf := hw
  have h0 : u ≠ 0 := (hpar _ hw w rfl).ne_zero
  have hs : SphFun A L Sf u := fun v hv k hk g => by
    obtain ⟨w', hw'⟩ : ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v := by
      have := v.isMaximal
      obtain ⟨Q, hQ, e⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
        (by rw [(RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).1
          (FaithfulSMul.algebraMap_injective _ _)]; exact bot_le)
      refine ⟨⟨Q, hQ.isPrime, fun hb => v.ne_bot ?_⟩, HeightOneSpectrum.ext e⟩
      rw [← e, hb, Ideal.under_bot]
    exact (congrFun ((hpar v hv w' hw').mem_fixed ⟨k, hk⟩) g).trans (by simp)
  have hc := _root_.GlobalTheory.Core.Rk.SphCoef.isSphCoef_rcoef hP D θ A cA L hθ m hm Sf u hu u hu par hpar hs _ hv 1 (map_one _)
  have h1 : MemL2Quotient (GQ A) m u := memL2_of_cusp_form hP hθ (mem_cuspForms.1 hu).1
  have hpos := petersson_self_pos h1 (mem_cuspForms.1 hu).1.1.toIsAutFun.cont h0
  have hne : rcoef m u u (1 * emb D.sp.cm.sig A.gram (w.under (𝓞 D.host.F)) 1) ≠ 0 := by
    have e : rTr A (1 * emb D.sp.cm.sig A.gram (w.under (𝓞 D.host.F)) 1) u = u := funext fun g => by
      simp only [rTr, map_one, mul_one]
    rw [rcoef, e]
    intro h
    rw [h] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨h2, h3⟩ := hB A L hL _ trivial par _ hc hne w rfl
  exact ⟨h2.le, h3⟩

theorem eulerRight : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, SphFactor D → LocalZetaOn D (fun _ => True) →
    ParamBoundOn D (fun _ => True) → EulerRight D := by
  intro hP D hS hZ hB ψ θ A B χA χB sA sB t cA a om ν 𝓕 hp LA LB Sf Φ₁ Φ₂ hΦ₁ hΦ₂ hU m hm u₁ hu₁ u₂ hu₂ par hpar hsph
    s hs hint
  have ha : (0 : ℝ) ≤ A.rank := Nat.cast_nonneg _
  have hb := bounded_of_isParamFun hP hB hp.setting.2.2.2.1 hU.sdA m hm hu₁ hpar
  have hL := _root_.GlobalTheory.LSD_hasProd_LvTw D Sf par χB _ _ hb (s + 1 / 2) (by
    have : (s + 1 / 2 : ℂ).re = s.re + 1 / 2 := by simp
    rw [this]; linarith)
  obtain ⟨hd0, hdv, hd⟩ := (GlobalTheory.T.partialNormalizingFactorProduct_analytic_ne_zero D (Sf : Set (FinPl D)) A.rank B.rank).2 s (by linarith)
  refine limit_eq_prod_mul Sf
    (fun v => GlobalTheory.LFun.LvTw par (GlobalTheory.LFun.val χB) v (s + 1 / 2) / GlobalTheory.LFun.dv D.host.E A.rank B.rank v s)
    (fun S => ∫ g in openOff A LA S, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m) ?_
    (_root_.GlobalTheory.Core.Rk.IP.tendsto_setIntegral_openOff D A LA hU.sdA m _ hint) fun T U hT hTU =>
      _root_.GlobalTheory.Core.Rk.EulStep.setIntegral_openOff_union hP D hS hZ ψ θ A B χA χB sA sB t cA a om ν 𝓕 hp LA LB Sf Φ₁ Φ₂ hΦ₁ hΦ₂ hU m hm u₁ hu₁ u₂ hu₂ par
        hpar hsph s (by linarith) hint Sf T le_rfl hT U hTU
  exact (Tendsto.div hL hd hd0).congr fun T => (Finset.prod_div_distrib _ _).symm

end GlobalTheory.Core.Rk.EulerProd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSphericalFactorizationOfWeilDualPairStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingSphericalFactorization_of_weilDualPair : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ D : D7, SphFactor D := by
  first | exact @GlobalTheory.Core.Rk.IP.sphFactor_of_weilRepresentationUnitaryPair | exact GlobalTheory.Core.Rk.IP.sphFactor_of_weilRepresentationUnitaryPair | (intros; apply GlobalTheory.Core.Rk.IP.sphFactor_of_weilRepresentationUnitaryPair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EmbZeroTrivialWittDecomposition
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.FinPl.LastInhab

open GlobalTheory.Unf.Inhab

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem eventually_charUnramAt (D : D7) (χ : (AE D)ˣ →* Circle) (hχ : Continuous χ) :
    ∀ᶠ v : Pl D in Filter.cofinite, CharUnramAt D χ v := by
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D χ hχ
  filter_upwards [GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D (N : D.host.E)⁻¹] with v hv x h1 h2 h3 h4
  have ha : (x : AE D) - 1 ∈ intAt D (· = v) := by
    refine ⟨Ideal.mem_inf.2 ⟨?_, Submodule.mem_iInf _ |>.2 fun w => ?_⟩, ?_⟩
    · rw [RingHom.mem_ker, RingHom.map_sub, RingHom.map_one, h1, sub_self]
    · rw [RingHom.mem_ker, RingHom.map_sub, RingHom.map_one, GlobalTheory.FinPl.compAt, RingHom.comp_apply, h2 _ w.2, sub_self]
    · rw [RingHom.map_sub, RingHom.map_one]; exact sub_mem h3 (GlobalTheory.HeckeConj.one_mem_intAE D)
  have e : (x : AE D) - 1 = N • (incA D (N : D.host.E)⁻¹ * ((x : AE D) - 1)) := by
    rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (incA D), ← RingHom.map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), RingHom.map_one, one_mul]
  obtain ⟨y, hy, hye⟩ : ∃ y, y ∈ intAt D (· = v) ∧ (x : AE D) - 1 = N • y := ⟨_, hv _ ha, e⟩
  refine hker x ⟨h1, h3, h4⟩ ⟨finPart D y, hy.2, ?_⟩
  rw [← RingHom.map_one (finPart D), ← RingHom.map_sub, hye]
  exact (finPart D).toAddMonoidHom.map_nsmul _ _

end GlobalTheory.FinPl.LastInhab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentPlacesCharacterized
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CommonVac

theorem latV_eq_of_moves {D : D7} {S : HSp D} {g : GA D S} {Λ M N : GlobalTheory.FinPl.Lat S} {P : GlobalTheory.FinPl.Pl D → Prop}
    (hM : GlobalTheory.FinPl.Moves S g Λ M P) (hN : GlobalTheory.FinPl.Moves S g Λ N P) :
    GlobalTheory.FinPl.latV S M P = GlobalTheory.FinPl.latV S N P := by
  have h1 : GlobalTheory.FinPl.Moves S (g * g⁻¹) M N P := GlobalTheory.StMoves.moves_mul (GlobalTheory.StMoves.moves_inv hM) hN
  rw [mul_inv_cancel] at h1
  have e1 : ∀ y : Fin S.rank → AE D, mt S (1 : GA D S) *ᵥ y = y := fun y => by
    rw [show mt S (1 : GA D S) = 1 from rfl, Matrix.one_mulVec]
  ext y
  constructor
  · intro hy
    have := (h1 y (GlobalTheory.FinPl.FrameLat.latV_supp hy)).1 hy
    rwa [e1] at this
  · intro hy
    have h2 := h1 y (fun i => by
      have := GlobalTheory.FinPl.FrameLat.latV_supp hy i
      exact this)
    rw [e1] at h2
    exact h2.2 hy

end GlobalTheory.CommonVac

namespace GlobalTheory.CommonVac

theorem exists_common_vacua : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b : ∀ j, GA D (Yc D j)) (v : VCom (commOf (pk W) u (mkGeo m b))), (commOf (pk W) u (mkGeo m b)).Is → v.τ = y.τ → v.NT = a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → GlobalTheory.Core.Mi.IsTypePlaces (pk W).Pg → (∀ j, b j ∈ GfC (Yc D j)) → a.bT ∈ GfC D.sp.X' → IsSelfDualC D.sp.X' a.LT → (∀ P, GlobalTheory.FinPl.Moves D.sp.X' a.bT (pk W).ΛX a.LT P) → (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (v.N j) ∧ ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) → GlobalTheory.FinPl.Moves (Yc D j) (b j) ((pk W).ΛY j) (v.N j) P) → v.b = b → v.bT = a.bT → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → ∃ (Ψ : ∀ j, PolF D (Yc D (j + 1)).rank (Yc D j).rank → GA D (Yc D j) → GA D (Yc D (j + 1)) → WO (Yc D j) (Yc D (j + 1)) → ℂ) (ΨT : ∀ j, j + 2 * 0 + 2 = D.R.m → PolF D D.sp.X'.rank (Yc D (j + 1)).rank → WO (Yc D (j + 1)) D.sp.X' → ℂ), (∀ j, j + 1 < D.R.m → ∀ P, ∀ x ∈ GinfC _, ∀ x' ∈ GinfC _, GlobalTheory.FinPl.Vac (pk W).ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) (Ψ j P x x')) ∧ (∀ j h P, GlobalTheory.FinPl.Vac (pk W).ψ _ _ (v.N (j + 1)) v.NT (fun _ => True) (ΨT j h P)) ∧ ∀ j row col, VTie (⟨mkGeo m b, j, row, col⟩ : FamCh W u) { v with Ψ := Ψ, ΨT := ΨT } := by
  intro D L hT Gi Gl Kc Yd cX ex W u hpk a y m b v hc hτ hNT hgP hTy hb hbT hLT hmT hN hvb hvbT htP

  have hQ : ∀ p ∈ v.gP, ((∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D p ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a ∈ GlobalTheory.FinPl.intAt D (· = p), incA D D.host.xi0 * a ∈ GlobalTheory.FinPl.intAt D (· = p) ∧ incA D D.host.xi0⁻¹ * a ∈ GlobalTheory.FinPl.intAt D (· = p)) ∧ ∀ (V : HSp D) (Λ : GlobalTheory.FinPl.Lat V), GlobalTheory.FinPl.latA V Λ (· = p) = GlobalTheory.FinPl.latV V Λ (· = p)) := by
    intro p hp
    obtain ⟨PP, hPP, rfl⟩ := (hgP p).1 hp
    exact _root_.GlobalTheory.LevelPlaces.split_unit W hpk hTy PP hPP

  have hY : ∀ j, ∃ o : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ, j + 1 < D.R.m →
      GlobalTheory.FinPl.CombAt (· ∈ v.gP) o ∧
      (∀ P, ∀ x ∈ GinfC (Yc D j), ∀ x' ∈ GinfC (Yc D (j + 1)), GlobalTheory.FinPl.Vac (pk W).ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True)
        (comb (pk W).ψ _ _ o ((pk W).ωY W.P.A3.A.μ0 j (x * b j, x' * b (j + 1)) (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) P)))) ∧
      comb (pk W).ψ _ _ o ((pk W).ωY W.P.A3.A.μ0 j (b j, b (j + 1))
        (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) 1)) ≠ 0 := by
    intro j
    by_cases hj : j + 1 < D.R.m
    · obtain ⟨M, hM, hMv⟩ := _root_.GlobalTheory.MovedLat.movedLat W hpk j (by omega) (b j)
      obtain ⟨M', hM', hM'v⟩ := _root_.GlobalTheory.MovedLat.movedLat W hpk (j + 1) hj (b (j + 1))
      obtain ⟨hvac, hnz⟩ := _root_.GlobalTheory.StepMove.fock_vac_moved W hpk j hj (b j) (b (j + 1)) (hb j) (hb (j + 1)) M M' hM hM' hMv hM'v
      obtain ⟨o, ho, hoV⟩ := _root_.GlobalTheory.VacRebase.rebase_vac D (pk W).ψ hc.std (Yc D j) (Yc D (j + 1)) M (v.N j) M' (v.N (j + 1)) v.gP hM
        (hN j (by omega)).1 hM' (hN (j + 1) hj).1 hQ (fun p hp =>
          ⟨latV_eq_of_moves (hMv (· = p)) ((hN j (by omega)).2 (· = p) (fun p' hp' => hp' ▸ hp)),
            latV_eq_of_moves (hM'v (· = p)) ((hN (j + 1) hj).2 (· = p) (fun p' hp' => hp' ▸ hp))⟩)
      have hv1 := hvac 1 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
      simp only [one_mul] at hv1
      exact ⟨o, fun _ => ⟨ho, fun P x hx x' hx' => (hoV _ (hvac P x hx x' hx')).1, (hoV _ hv1).2 hnz⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose O hO using hY

  have hTs : ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ o : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ, GlobalTheory.FinPl.CombAt (· ∈ v.gP) o ∧
      (∀ P, GlobalTheory.FinPl.Vac (pk W).ψ _ _ (v.N (j + 1)) v.NT (fun _ => True)
        (comb (pk W).ψ _ _ o (omT (pk W) W.P.A3.A.μ0 j h (b (j + 1), a.bT) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) P)))) ∧
      comb (pk W).ψ _ _ o (omT (pk W) W.P.A3.A.μ0 j h (b (j + 1), a.bT) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) 1)) ≠ 0 := by
    intro j h
    have hj : j + 1 < D.R.m := by omega
    obtain ⟨M', hM', hM'v⟩ := _root_.GlobalTheory.MovedLat.movedLat W hpk (j + 1) hj (b (j + 1))
    obtain ⟨hvac, hnz⟩ := _root_.GlobalTheory.TopMove.fock_vac_moved_top W hpk j h (b (j + 1)) a.bT (hb (j + 1)) hbT M' a.LT hM' hLT hM'v hmT
    have hNT' : IsSelfDualC D.sp.X' v.NT := hNT ▸ hLT
    obtain ⟨o, ho, hoV⟩ := _root_.GlobalTheory.VacRebase.rebase_vac D (pk W).ψ hc.std (Yc D (j + 1)) D.sp.X' M' (v.N (j + 1)) a.LT v.NT v.gP hM'
      (hN (j + 1) hj).1 hLT hNT' hQ (fun p hp =>
        ⟨latV_eq_of_moves (hM'v (· = p)) ((hN (j + 1) hj).2 (· = p) (fun p' hp' => hp' ▸ hp)), by rw [hNT]⟩)
    exact ⟨o, ho, fun P => (hoV _ (hvac P)).1, (hoV _ (hvac 1)).2 hnz⟩
  choose OT hOT using hTs
  refine ⟨fun j P x x' => comb (pk W).ψ _ _ (O j) ((pk W).ωY W.P.A3.A.μ0 j (x * b j, x' * b (j + 1)) (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) P)),
    fun j h P => comb (pk W).ψ _ _ (OT j h) (omT (pk W) W.P.A3.A.μ0 j h (b (j + 1), a.bT) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) P)),
    fun j hj P x hx x' hx' => (hO j hj).2.1 P x hx x' hx', fun j h P => (hOT j h).2.1 P, ?_⟩
  intro j' row col
  exact {
    b := fun j => by rw [hvb]
    bT := ⟨hvbT, hNT⟩
    gP := hgP
    tP := htP
    moves := fun j hj P hP => (hN j hj).2 P hP
    movesT := hmT
    Ψ := fun j hj => ⟨O j, (hO j hj).1, fun P x x' => rfl⟩
    ΨT := fun j h => ⟨OT j h, (hOT j h).1, fun P => rfl⟩
    nz := ⟨fun j hj => ⟨1, by simpa only [one_mul] using (hO j hj).2.2⟩, fun j h => ⟨1, (hOT j h).2.2⟩⟩ }

end GlobalTheory.CommonVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselCompatibility
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

theorem GlobalTheory.MiTop.levFn_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
    {LL : Type} [CommRing LL] (hc : Formalism.BasicNotions.CMData F E) (J : Matrix (Fin n) (Fin n) E)
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : Formalism.L2.DIV.LevDat E LL n) {x y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hx : x ∈ Formalism.L2.DIV.lev hc J β L) (hy : y ∈ Formalism.L2.DIV.lev hc J β L) :
    Formalism.L2.DIV.levFn β L (x * y * x⁻¹) = Formalism.L2.DIV.levFn β L y := by
  have e := congrArg (Formalism.L2.DIV.levChar hc J β L)
    (show (⟨x, hx⟩ * ⟨y, hy⟩ * (⟨x, hx⟩ : Formalism.L2.DIV.lev hc J β L)⁻¹ : Formalism.L2.DIV.lev hc J β L) =
      ⟨x * y * x⁻¹, _⟩ from rfl)
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm] at e
  exact e.symm

namespace GlobalTheory.MiTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

end GlobalTheory.MiTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDatumBoxTensorLineOverVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_datum_boxTensor_line_over_vacuum : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n'' : Type) [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S X T L'' : HSp D) (o'' : OrthDec X T L'') (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L'' ζ₀ → ∀ (β : Frame p S n) (γ : Frame p T n'') (γ₀ : Frame p X (n'' ⊕ Fin 1)), IsSumFrame o'' ζ₀ γ γ₀ → ∀ (LS : Lat S) (LT : Lat T) (LX : Lat X), IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC X LX → ∀ (f₂ F₂ : WO S T → ℂ) (Ψ₂ : Matrix n'' n k → ℂ), Over ψ β γ LS LT f₂ Ψ₂ F₂ → ∀ (b : (n → k) → ℂ) (g₃ : WO S L'' → ℂ) (T₃ : (WO S L'' → ℂ) →ₗ[ℂ] (WO S L'' → ℂ)), IsThetaFunO ψ S L'' g₃ → IsPlaceModel ψ (symplO S L'') (heisO ψ S L'') p.e (latO S L'' (LS : Set _) ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀} : Lat L'') : Set _) (· = p.v)) 1 g₃ T₃ → GlobalTheory.FinPl.tensRow Ψ₂ b ∈ SB (Matrix (n'' ⊕ Fin 1) n k) → ∃ g, Over ψ β γ₀ LS LX g (GlobalTheory.FinPl.tensRow Ψ₂ b) (o''.boxT S F₂ (T₃ (rowFun β ζ₀ b))) := by
  exact @GlobalTheory.FinPl.BoxDatum.over_boxT
end

