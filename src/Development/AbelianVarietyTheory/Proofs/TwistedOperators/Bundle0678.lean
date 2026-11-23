module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0674
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0245
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.RelIndexMulMeasure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Definitions.Divisors.GridTestLatticeLargestSlopeBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VolumePeriodProjectionSetEqFamilyLevel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0672
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0643
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0289
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CellVolumeMulCoef
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0437
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0675
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselLevelOneCosetAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.OneCosetBFPlace

theorem one_coset_place : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ g ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v), (∃ u : UX D ρ, ∃ a ∈ (pcBF W F ρ h).A₁, MxOff (· = v) (Formalism.L2.Theta.mt (G.V (.grid (2 * ρ + 1) 0)) g⁻¹ ⬝ (xZero (F.dJ ρ h) ⬝ u.1.1) - xZero (F.dJ ρ h) - a)) → ∃ r ∈ Rgrp (G.V (.grid (2 * ρ + 1) 0)) (xZero (F.dJ ρ h)), r ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v) ∧ ∃ k ∈ lev G (.grid (2 * ρ + 1) 0), k ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v) ∧ g = r * k := by
  intro D hq T L μ hL sc G W M hM F hF ρ h v hv g hg hc
  obtain ⟨u, a, ha, hc⟩ := hc
  obtain ⟨k, hk, hkv, hm⟩ := _root_.GlobalTheory.CosetBF.besselOrbit_at_badPlace_eq_congruenceTranslate D hq T L μ hL sc G W M hM F hF ρ h v hv g hg u a ha hc
  obtain ⟨r, hr, hrv, rfl⟩ := GlobalTheory.T.exists_unitriangularStabilizer_of_principal_move _ _ _ g k u hg hkv hm
  exact ⟨r, hr, hrv, k⁻¹, inv_mem hk, inv_mem hkv, rfl⟩

end GlobalTheory.OneCosetBFPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BoxDepthDataMulLineVacuaBesselLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.BoxBF

theorem isHalf_mul {D : D7} {m n k : ℕ} {e : AE D} {u : Mx D m n} (h : IsHalf e u) (M : Mx D n k) : IsHalf e (u ⬝ M) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [← mul_assoc, h i l]

theorem main : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ Ξ₁ Ξ₂, VacG W.ψ _ _ (latCore G (2 * ρ + 1)) Ξ₁ → IsThetaFunO W.ψ _ _ Ξ₂ →
    VacG W.ψ _ _ (lineLat F ρ) (fun w => star (Ξ₂ ((F.lnk ρ).κ _ w))) → VacG W.ψ _ _ (pcBF W F ρ h).Γ₀ ((F.oB ρ h).boxS _ Ξ₁ Ξ₂) := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h Ξ₁ Ξ₂ h1 h2 h3
  have hn : ∀ x, ‖W.ψ x‖ = 1 := W.ψ_std.1.2.1
  refine ⟨(F.oB ρ h).isThetaFunO_boxS h1.1 h2, ?_, ?_⟩
  · intro u hu
    obtain ⟨w, hw, hw'⟩ := _root_.GlobalTheory.LineComp.main D hq T L μ0 hL sc G W M hM F hF ρ h u hu
    rw [OrthDec.heisO_boxS, map_nsmul, Prod.smul_fst, Prod.smul_snd,
      h1.2.1 _ (_root_.GlobalTheory.AscFin.pcBF_core_mem_latCore D hq T L μ0 hL sc G W M hM F hF ρ h u hu), hw',
      (_root_.GlobalTheory.KapVac.kappa_vac D W.ψ hn _ _ _ _ (F.line ρ) (F.lnk ρ) _ Ξ₂ h3.2 w hw).1]
  · intro e he u hu hh
    obtain ⟨w, hw, hw'⟩ := _root_.GlobalTheory.LineComp.main D hq T L μ0 hL sc G W M hM F hF ρ h u hu
    have ha : IsHalf e ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).1 := isHalf_mul hh _
    have hb : IsHalf e ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).2 := isHalf_mul hh _
    rw [OrthDec.heisO_boxS, h1.2.2 e he _ (_root_.GlobalTheory.AscFin.pcBF_core_mem_latCore D hq T L μ0 hL sc G W M hM F hF ρ h u hu) ha, hw']
    rw [hw'] at hb
    rw [(_root_.GlobalTheory.KapVac.kappa_vac D W.ψ hn _ _ _ _ (F.line ρ) (F.lnk ρ) _ Ξ₂ h3.2 w hw).2 e he hb]

end GlobalTheory.AscFin.BoxBF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainPreStepsExistOfDepthCongruenceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.core_chain_pre_steps_exist_of_depth_congruence : DepFixed → PreOK := by
  first | exact @GlobalTheory.CoreOnto.PreSteps.preOK | exact GlobalTheory.CoreOnto.PreSteps.preOK | (intros; apply GlobalTheory.CoreOnto.PreSteps.preOK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleCosetProjectionVolumeConstMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.CellMass

noncomputable section

namespace GlobalTheory.CellLevel

variable {D : D7}

theorem finE_range_eq (V : HSp D) : ((Lev.finE V).comp (GfC V).subtype).range = (Lev.finE V).range := by
  refine le_antisymm (fun y ⟨g, hg⟩ => ⟨g.1, hg⟩) ?_
  rintro _ ⟨g, rfl⟩
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue V 1 _ (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V g)
  refine ⟨⟨k, MonoidHom.mem_ker.2 k1⟩, ?_⟩
  show Formalism.UG.bc (Lev.swapAE D) (finHom V k) = Formalism.UG.bc (Lev.swapAE D) (finHom V g)
  rw [k2]

theorem relIndex_comap_fin (V : HSp D) (K K' : Subgroup (GL (Fin V.rank) (Lev.EAf D))) :
    (K.comap ((Lev.finE V).comp (GfC V).subtype)).relIndex (K'.comap ((Lev.finE V).comp (GfC V).subtype)) =
      (K.comap (Lev.finE V)).relIndex (K'.comap (Lev.finE V)) := by
  rw [Subgroup.relIndex_comap, Subgroup.relIndex_comap, Subgroup.map_comap_eq, Subgroup.map_comap_eq,
    finE_range_eq]

theorem isCompact_comap_fin (V : HSp D) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))} (h : IsCO V K) :
    IsCompact ((K.comap ((Lev.finE V).comp (GfC V).subtype) : Subgroup (GfC V)) : Set (GfC V)) := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  convert h.2 using 1
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact Lev.mem_levA.2 ⟨g.2, hg⟩
  · intro hy
    obtain ⟨h1, h2⟩ := Lev.mem_levA.1 hy
    exact ⟨⟨y, h1⟩, h2, rfl⟩

theorem isOpen_comap_fin (V : HSp D) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))}
    (h : IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V))) :
    IsOpen ((K.comap ((Lev.finE V).comp (GfC V).subtype) : Subgroup (GfC V)) : Set (GfC V)) :=
  h.preimage continuous_subtype_val

theorem relIndex_ne_zero (V : HSp D) {K K₃ : Subgroup (GL (Fin V.rank) (Lev.EAf D))} (h : IsCO V K)
    (h₃ : IsOpen ((K₃.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V))) :
    (K₃.comap ((Lev.finE V).comp (GfC V).subtype)).relIndex (K.comap ((Lev.finE V).comp (GfC V).subtype)) ≠ 0 := by
  have := GlobalTheory.LocVec.finiteIndex_of_isOpen (K.comap ((Lev.finE V).comp (GfC V).subtype)) (isCompact_comap_fin V h) subset_rfl
    ((K₃.comap ((Lev.finE V).comp (GfC V).subtype)).subgroupOf (K.comap ((Lev.finE V).comp (GfC V).subtype)))
    ((isOpen_comap_fin V h₃).preimage continuous_subtype_val)
  exact this.index_ne_zero

theorem vol_ratio (V : HSp D) {K₁ K₂ : Subgroup (GL (Fin V.rank) (Lev.EAf D))} (h₁ : IsCO V K₁) (h₂ : IsCO V K₂)
    (ν : Measure (GfC V)) [ν.IsHaarMeasure] {μ μ' : Measure (GA D V)} (hμ : Lev.IsMeasLevDef V K₁ μ)
    (hμ' : Lev.IsMeasLevDef V K₂ μ') (x : ℝ≥0) (hx : μ = x • μ') :
    ν {g | Lev.finE V g.1 ∈ K₂} = ν {g | Lev.finE V g.1 ∈ K₁} * x := by
  obtain ⟨hLC, hSC, hT2, hB, hTG, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hB; haveI := hTG
  haveI : μ.IsHaarMeasure := hμ.1
  have h₃ : IsOpen (((K₁ ⊓ K₂).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := h₁.1.inter h₂.1
  have hA₁ : μ (K₁.comap (Lev.finE V)) = 1 := GlobalTheory.Mass.Levels.measure_comap_finE hμ
  have hA₂ : μ (K₂.comap (Lev.finE V)) = x := by
    rw [hx, Measure.smul_apply, GlobalTheory.Mass.Levels.measure_comap_finE hμ', ENNReal.smul_def, smul_eq_mul, mul_one]
  have n₁ := relIndex_ne_zero V h₁ h₃
  have n₂ := relIndex_ne_zero V h₂ h₃
  rw [relIndex_comap_fin] at n₁ n₂
  haveI : (((K₁ ⊓ K₂).comap (Lev.finE V)).subgroupOf (K₁.comap (Lev.finE V))).FiniteIndex := ⟨n₁⟩
  haveI : (((K₁ ⊓ K₂).comap (Lev.finE V)).subgroupOf (K₂.comap (Lev.finE V))).FiniteIndex := ⟨n₂⟩
  have e₁ := Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure _ _ (Subgroup.comap_mono inf_le_left) h₃.measurableSet μ
  have e₂ := Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure _ _ (Subgroup.comap_mono inf_le_right) h₃.measurableSet μ
  rw [hA₁] at e₁
  rw [hA₂] at e₂
  have m₁ := relIndex_ne_zero V h₁ h₃
  have m₂ := relIndex_ne_zero V h₂ h₃
  haveI : ((((K₁ ⊓ K₂).comap ((Lev.finE V).comp (GfC V).subtype))).subgroupOf
    (K₁.comap ((Lev.finE V).comp (GfC V).subtype))).FiniteIndex := ⟨m₁⟩
  haveI : ((((K₁ ⊓ K₂).comap ((Lev.finE V).comp (GfC V).subtype))).subgroupOf
    (K₂.comap ((Lev.finE V).comp (GfC V).subtype))).FiniteIndex := ⟨m₂⟩
  have f₁ := Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure _ _ (Subgroup.comap_mono inf_le_left)
    (isOpen_comap_fin V h₃).measurableSet ν
  have f₂ := Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure _ _ (Subgroup.comap_mono inf_le_right)
    (isOpen_comap_fin V h₃).measurableSet ν
  rw [relIndex_comap_fin] at f₁ f₂
  change ν (K₂.comap ((Lev.finE V).comp (GfC V).subtype)) = ν (K₁.comap ((Lev.finE V).comp (GfC V).subtype)) * x
  rw [← f₁, ← f₂]
  have key : ∀ (p q a m X : ENNReal), p * m = 1 → q * m = X → q * a = p * a * X := by
    intro p q a m X h1 h2
    rw [← h2, ← mul_one (q * a), ← h1]
    ring
  exact key _ _ _ _ _ e₁ e₂

theorem vol_pos (V : HSp D) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))} (h : IsCO V K)
    (ν : Measure (GfC V)) [ν.IsHaarMeasure] : 0 < ν.real {g | Lev.finE V g.1 ∈ K} := by
  obtain ⟨hLC, hSC, hT2, hB, hTG, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hB; haveI := hTG
  refine ENNReal.toReal_pos ?_ ?_
  · exact ((isOpen_comap_fin V h.1).measure_pos ν ⟨1, one_mem _⟩).ne'
  · exact ((isCompact_comap_fin V h).measure_lt_top).ne

end GlobalTheory.CellLevel

namespace GlobalTheory.CellLevel

theorem pr_vol_of (hpr : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ), ∀ j ∈ idx D, ∀ (hj : j < D.R.m) (ν : Measure (GfC (ch.G.V (.top j)))),
    ν.IsHaarMeasure → ∃ c : ℝ, 0 < c ∧ ∀ t Φ β b, IsRep t ch.S.B s β b → ∀ hb : b j ∈ GfC _,
      ν.real (prSet ch.G j ⟨b j, hb⟩) = c * ν.real {g | Lev.finE (ch.G.V (.top j)) g.1 ∈ ch.S.toGridChoice.levTop t Φ β j hj}) : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ), ∀ j ∈ idx D, ∀ ν : Measure (GfC (ch.G.V (.top j))), ν.IsHaarMeasure →
    ∃ κ' : ℝ, 0 < κ' ∧ ∀ t Φ β b, IsRep t ch.S.B s β b → ∀ M M' : Vol ch.G, M.Is t → IsTermVol t ch.S.toGridChoice Φ β M' →
      ∀ x : ℝ≥0, M.ν (.top j) = x • M'.ν (.top j) → ∀ hb : b j ∈ GfC _, ν.real (prSet ch.G j ⟨b j, hb⟩) = κ' * x := by
  refine big_mono ?_ hpr
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch h s j hj ν hν
  have hjm : j < D.R.m := by
    simp only [idx, List.mem_range'_1] at hj
    omega
  have hj1 : 1 ≤ j := by
    simp only [idx, List.mem_range'_1] at hj
    omega
  obtain ⟨c, hc, hcb⟩ := h s j hj hjm ν hν
  have hMax : IsCO (ch.G.V (.top j)) (ch.G.levMax (.top j)) :=
    congLev_open_compact _ (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _
      (ch.G.isV (X := .top j) (show j ≤ D.R.m by omega) (fun _ h => Node.noConfusion h)).sd)
      (by simp)
  refine ⟨c * ν.real {g | Lev.finE (ch.G.V (.top j)) g.1 ∈ ch.G.levMax (.top j)}, mul_pos hc (vol_pos _ hMax ν), ?_⟩
  intro t Φ β b hb M M' hM hM' x hx hbj
  rw [hcb t Φ β b hb hbj]
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have h1 : Lev.IsMeasLevDef _ (ch.G.levMax (.top (j' + 1))) (M.ν (.top (j' + 1))) := by
    have := hM.vtx (.top (j' + 1)) (show j' + 1 ≤ D.R.m by omega)
    unfold Vol.IsAt at this
    rw [if_pos (show Node.neg D.R.m (.top (j' + 1)) = 0 from rfl)] at this
    exact this.1
  have h2 : Lev.IsMeasLevDef _ (ch.S.toGridChoice.levTop t Φ β (j' + 1) hjm) (M'.ν (.top (j' + 1))) := by
    have := hM'.1 (j' + 1) hjm
    unfold Vol.IsAt at this
    rw [if_pos (show Node.neg D.R.m (.top (j' + 1)) = 0 from rfl)] at this
    exact this.1
  have e := vol_ratio _ hMax (GridChoice.isCO_levTop _ _ t Φ β hjm) ν h1 h2 x hx
  simp only [Measure.real, e, ENNReal.toReal_mul, ENNReal.coe_toReal, mul_assoc]

end GlobalTheory.CellLevel

namespace GlobalTheory.CellLevel

theorem pr_vol : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ), ∀ j ∈ idx D, ∀ ν : Measure (GfC (ch.G.V (.top j))), ν.IsHaarMeasure →
    ∃ κ' : ℝ, 0 < κ' ∧ ∀ t Φ β b, IsRep t ch.S.B s β b → ∀ M M' : Vol ch.G, M.Is t → IsTermVol t ch.S.toGridChoice Φ β M' →
      ∀ x : ℝ≥0, M.ν (.top j) = x • M'.ν (.top j) → ∀ hb : b j ∈ GfC _, ν.real (prSet ch.G j ⟨b j, hb⟩) = κ' * x := pr_vol_of _root_.GlobalTheory.PrLevel.vol_prSet

end GlobalTheory.CellLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHaarVolumeOfConjugateLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.CellMass

noncomputable section

namespace GlobalTheory.CellIdx

section Abstract

variable {G : Type} [Group G] (M N K : Subgroup G)

variable {M N K}

variable [TopologicalSpace G] [IsTopologicalGroup G]

end Abstract

end GlobalTheory.CellIdx

namespace GlobalTheory.CellIdx
open GlobalTheory.RootEx GlobalTheory.LocGrp GlobalTheory.LocGrpIff GlobalTheory.RowRep

section Flag
variable {D : D7} {K : Type} [Field K] (π : AE D →+* K) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

variable {Y₀ : Type} [Fintype Y₀] [DecidableEq Y₀] (b : Matrix (Fin S₀.rank) Y₀ K) (b' : Matrix Y₀ (Fin S₀.rank) K)

end Flag

variable {D : D7}

end GlobalTheory.CellIdx

namespace GlobalTheory.CellIdx
open GlobalTheory.RootEx GlobalTheory.LocGrp GlobalTheory.RowRep GlobalTheory.SplitWeil

section Local
variable {k : Type} [Field k]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Local

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}


set_option maxHeartbeats 1600000 in
theorem vol_mul_colCoef : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ), ∀ j ∈ idx D,
    ∀ la : Measure ((rowN ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j)))), la.IsHaarMeasure →
    ∃ V₀ : ℝ, 0 < V₀ ∧ ∀ t β b, IsRep t ch.S.B s β b → ∀ hb : b j ∈ GfC _,
      la.real {n | (⟨b j, hb⟩ : GfC _)⁻¹ * n.1 * ⟨b j, hb⟩ ∈ (latGrp ch.G j).subgroupOf (GfC _)} *
        (GlobalTheory.RowWt.colCoef ch t β j : ℝ) = V₀ := by
  first
  | (exact @_root_.GlobalTheory.SymmetricJacobianSignature.cell_volume_mul_coef)
  | exact @_root_.GlobalTheory.SymmetricJacobianSignature.cell_volume_mul_coef
  | exact _root_.GlobalTheory.SymmetricJacobianSignature.cell_volume_mul_coef
  | (apply _root_.GlobalTheory.SymmetricJacobianSignature.cell_volume_mul_coef <;> assumption)
  | (intros; apply _root_.GlobalTheory.SymmetricJacobianSignature.cell_volume_mul_coef <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SymmetricJacobianSignature.cell_volume_mul_coef <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SymmetricJacobianSignature.cell_volume_mul_coef ..)

end GlobalTheory.CellIdx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionPairingInvariantInnerVertexLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance


variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} in
theorem colMapV_congr (S : GridChoice W U) (t : T)
    (v v' : ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ) (x x' : ∀ j, FinPt G (.top j))
    (h : ∀ j (hj : j < D.R.m), fockComp W S.N.frC (.top t j) (v ⟨j, hj⟩) (x j * S.N.u _) (x (j + 1) * S.N.u _) =
      fockComp W S.N.frC (.top t j) (v' ⟨j, hj⟩) (x' j * S.N.u _) (x' (j + 1) * S.N.u _)) :
    colMapV S t v x = colMapV S t v' x' := by
  have e : (fun j => if hj : j < D.R.m then S.Z.scal 1 (.top t j) •
      fockComp W S.N.frC (.top t j) (v ⟨j, hj⟩) (x j * S.N.u _) (x (j + 1) * S.N.u _) else 0) =
      (fun j => if hj : j < D.R.m then S.Z.scal 1 (.top t j) •
      fockComp W S.N.frC (.top t j) (v' ⟨j, hj⟩) (x' j * S.N.u _) (x' (j + 1) * S.N.u _) else 0) := by
    funext j
    by_cases hj : j < D.R.m
    · rw [dite_eq_left hj, dite_eq_left hj, h j hj]
    · rw [dite_eq_right hj, dite_eq_right hj]
  unfold colMapV
  rw [e]

theorem pairPts_update_top : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))),
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (j : ℕ) (hj : 0 < j) (hjm : j < D.R.m) (k : FinPt G (.top j)),
      finG (G.V (.top j)) k ∈ S.levTop t Φ β j hjm →
      pairPts S τ (Function.update x j (x j * k)) y (Ψ (Function.update x j (x j * k) 0)) (F (y 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0)) := by
  intro D T L sc G W U S t Φ β τ μ₀ hL hde hc ht hβ hτ hv Ψ F x y j hj hjm k hk
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hx0 : Function.update x (j + 1) (x (j + 1) * k) 0 = x 0 := Function.update_of_ne (by omega) _ _
  rw [hx0, pairPts_eq_pairV, pairPts_eq_pairV]
  set u := S.N.u (.top (j + 1)) with hu
  set g : FinPt G (.top (j + 1)) := u⁻¹ * k * u with hg
  have thv : ∀ d ∈ τ.support, ∀ j' : Fin D.R.m, IsThetaFunO W.ψ (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)) (S.Z.vec (d.1 j')) :=
    fun d hd j' => GlobalTheory.VecThetaDef.vec_isThetaFunO S.Z (d.1 j') (show j'.1 + 1 ≤ D.R.m by omega) (by simp [Pair.InRange, Node.InRange]; try omega) ((hv d hd).1 j')
  have hcol : ∀ d ∈ τ.support, colMapV S t (fun j' => S.Z.vec (d.1 j')) (Function.update x (j + 1) (x (j + 1) * k)) =
      colMapV S t (movedCol S d j hjm g) x := by
    intro d hd
    refine colMapV_congr S t _ _ _ _ fun j' hj' => ?_
    by_cases h1 : j = j'
    · subst h1
      have hA := GlobalTheory.FockTranslate.fockComp_translate W S.N.frC t j (by omega) _ (thv d hd ⟨j, hj'⟩) (x j * S.N.u _) 1 (x (j + 1) * u) g
      rw [mul_one] at hA
      have e1 : x (j + 1) * k * u = x (j + 1) * u * g := by rw [hg]; group
      have m1 : (⟨j, hj'⟩ : Fin D.R.m) ≠ ⟨j + 1, hjm⟩ := by intro h; simp [Fin.ext_iff] at h
      rw [Function.update_of_ne (by omega : j ≠ j + 1), Function.update_self, e1, hA, movedCol,
        Function.update_of_ne m1, Function.update_self]
      try simp only [OneMemClass.coe_one]
      all_goals rfl
    · by_cases h2 : j + 1 = j'
      · subst h2
        have hA := GlobalTheory.FockTranslate.fockComp_translate W S.N.frC t (j + 1) (by omega) _ (thv d hd ⟨j + 1, hj'⟩) (x (j + 1) * u) g (x (j + 1 + 1) * S.N.u _) 1
        rw [mul_one] at hA
        have e1 : x (j + 1) * k * u = x (j + 1) * u * g := by rw [hg]; group
        rw [Function.update_self, Function.update_of_ne (by omega : j + 1 + 1 ≠ j + 1), e1, hA, movedCol, Function.update_self]
        try simp only [OneMemClass.coe_one]
        all_goals rfl
      · have m1 : (⟨j', hj'⟩ : Fin D.R.m) ≠ ⟨j + 1, hjm⟩ := by intro h; simp [Fin.ext_iff] at h; omega
        have m2 : (⟨j', hj'⟩ : Fin D.R.m) ≠ ⟨j, by omega⟩ := by intro h; simp [Fin.ext_iff] at h; omega
        rw [Function.update_of_ne (by omega : j' ≠ j + 1), Function.update_of_ne (by omega : j' + 1 ≠ j + 1), movedCol,
          Function.update_of_ne m1, Function.update_of_ne m2]
  have key : pairV S t τ (fun d j' => S.Z.vec (d.1 j')) (fun d i => S.Z.vec (d.2 i)) (Function.update x (j + 1) (x (j + 1) * k)) y =
      pairV S t τ (fun d => movedCol S d j hjm g) (fun d i => S.Z.vec (d.2 i)) x y := by
    unfold pairV
    refine Finsupp.sum_congr fun d hd => ?_
    rw [hcol d hd]
  rw [key]
  refine congrArg (fun φ => φ (Ψ (x 0)) (F (y 0))) (GlobalTheory.ExpansionInvariance.pairV_eq_of_prodFun_eq S t τ _ _ _ _ ?_ ?_ (_root_.GlobalTheory.ExpansionInvariance.product_invariant S hL hde hc ht hβ hτ hv j hjm k hk) x y)
  · intro d hd j'
    refine ⟨?_, thv d hd j'⟩
    by_cases h2 : j' = ⟨j + 1, hjm⟩
    · subst h2
      rw [movedCol, Function.update_self]
      exact (W.om_is _ (by simp [Pair.InRange, Node.InRange]; try omega)).om_pres _ _ (thv d hd _)
    · by_cases h1 : j' = ⟨j, by omega⟩
      · subst h1
        rw [movedCol, Function.update_of_ne h2, Function.update_self]
        exact (W.om_is _ (by simp [Pair.InRange, Node.InRange]; try omega)).om_pres _ _ (thv d hd _)
      · rw [movedCol, Function.update_of_ne h2, Function.update_of_ne h1]
        exact thv d hd j'
  · intro d hd i
    have h := GlobalTheory.VecThetaDef.vec_isThetaFunO S.Z (d.2 i) (show i.1 + 1 ≤ D.R.m ∧ D.R.m = D.R.m by omega) (show i.1 + 1 ≤ D.R.m ∧ D.R.m ≤ D.R.m by omega) ((hv d hd).2 i)
    exact ⟨h, h⟩

end GlobalTheory.ExpansionInvariance

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorSumProdLocalPureTensorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flippedFiniteTensor_sum_prod_local_pure_tensors : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ConLin ch → ∀ (t : T) (Φ : ch.G.Datum) (τ : SchRow ch.G × SchDown ch.G t →₀ ℂ), IsFlipFin t ch.S.B ch.rm Φ τ → ∀ (β : CosFam ch.G t) (e : AE D), IsIdemSum e (locPl ch.G t) → ∃ (α : Type) (SA : Finset α) (xA : α → ℂ) (φ : α → (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)) (fd : α → SchDown ch.G t) (fr : α → SchRow ch.G), (∀ a ∈ SA, ∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ a w b)) ∧ (∀ a ∈ SA, (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ a w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fd a j)) ∧ (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ a w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fr a i))) ∧ (∀ (u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) (y : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))), (∀ j, IsHalf e (u j)) → (∀ i, IsHalf e (y i)) → ∏ w, (ch.S.term t Φ β w).datum (ch.S.colAt t w.1 u) (ch.S.rowAt t w.1 y) = ∑ a ∈ SA, xA a * ∏ w : locPl ch.G t, flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (φ a w))) (ch.S.colAt t w.1 u) (ch.S.rowAt t w.1 y)) ∧ ∀ (M : Vol ch.G) (hM : M.Is t) (P : PolDown ch.G) (h : Pts ch.G) (u : ColPt ch.G) (y : RowPt ch.G), (τ.sum fun d x => x * evT (conAt ch.W hM (fockD ch.W t d.2 P) h) d.1 u y) = ∑ a ∈ SA, xA a * evT (conAt ch.W hM (fockD ch.W t (fd a) P) h) (fr a) u y := by
  first | exact @GlobalTheory.LocAsm.flipFin_productExpansion | exact GlobalTheory.LocAsm.flipFin_productExpansion | (intros; apply GlobalTheory.LocAsm.flipFin_productExpansion <;> assumption)
end

