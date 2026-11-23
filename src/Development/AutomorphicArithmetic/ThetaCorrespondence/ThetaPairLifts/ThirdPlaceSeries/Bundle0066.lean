module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0989
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0324
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0058
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1756
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1811
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0036
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1864

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiCompatPk
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
noncomputable section
open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV in
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.Fam.chi_compat_pk_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg → Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ π' : Formalism.IndefR.Datum.EAf D →+* k, (∀ a, π' (Formalism.IndefR.Datum.toEAf D a) = q.pr a) → GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) → ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ μ : kˣ →* ℂˣ, IsTame μ → (ofSplit q).IsComp (Formalism.IndefR.Lift.chrStep (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta j).1⁻¹ μ → GlobalTheory.FunObj.Comparison₂.Compat (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) ((_root_.GlobalTheory.Fam.pk_z W).chi j PP) μ := by
  intro D L hT Gi Gl Kc Yd cX ex W hW k _ _ _ _ q PP hP hI π' hπ hR j hj1 hj2 μ hμ hC
  have hL := hW.bot.hyp.2.2.2.1.lev
  intro s u x hu hx
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : Formalism.L2.DIV.kP PP)
  have hoa : ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Datum.EAf D) =
      Formalism.IndefR.Datum.toEAf D (incA D (a : D.host.E)) := rfl
  have hψa : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E a) =
      q.pr (incA D (a : D.host.E)) := by
    rw [RingHom.comp_apply, Subring.coe_subtype, hoa, hπ]
  have hres : Formalism.L2.DIV.resS D.host.F PP (Formalism.L2.DIV.oToS D.host.F D.host.E a) = u := by
    rw [Formalism.L2.DIV.resS_oToS, ha]
  have h1 : valuation k (q.pr (incA D (a : D.host.E))) = 1 := by
    rw [← hψa, ← hR.isUnit_iff, hres]; exact u.isUnit
  have h2 : valuation k ((x : k) - q.pr (incA D (a : D.host.E))) < 1 := by
    rw [← hψa, hx, ← map_sub]
    refine (hR.ker _).1 ?_
    rw [map_sub, hres, ← hu, sub_self]
  have hp0 : q.pr (incA D (a : D.host.E)) ≠ 0 := fun h => by rw [h, map_zero] at h1; exact zero_ne_one h1
  have hμx : μ x = μ (Units.mk0 _ hp0) := by
    have : μ (x * (Units.mk0 _ hp0)⁻¹) = 1 := hμ _ (by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, ← mul_inv_cancel₀ hp0, ← sub_mul, map_mul, map_inv₀, h1,
        inv_one, mul_one]
      exact h2)
    rw [map_mul, map_inv, mul_inv_eq_one] at this; exact this
  have ha0 : (a : D.host.E) ≠ 0 := fun h => by rw [h, map_zero, map_zero] at h1; exact zero_ne_one h1
  have hee : q.e * q.e = q.e := hI.1.1
  let y : (AE D)ˣ := ⟨Formalism.L2.JoinChr.locE D q.e (a : D.host.E), Formalism.L2.JoinChr.locE D q.e (a : D.host.E)⁻¹,
    GlobalTheory.ChainOnto.locE_mul_inv D hee ha0, by rw [mul_comm]; exact GlobalTheory.ChainOnto.locE_mul_inv D hee ha0⟩
  have hyι : (y : AE D) = (ofSplit q).ι ((Units.mk0 _ hp0 : kˣ) : k) + (1 - (ofSplit q).e) := by
    show Formalism.L2.JoinChr.locE D q.e (a : D.host.E) = q.sec (q.pr (incA D (a : D.host.E))) + (1 - q.e)
    rw [q.sec_pr, GlobalTheory.ChainOnto.locE_eq]
  have hcomp := hC _ y hyι
  have hinf : infPart D q.e = 0 := (GlobalTheory.IdemSupport.delta_of_isIdemAt (comp_toAd D) hI).1
  have hint : ∀ z : D.host.E, valuation k (q.pr (incA D z)) = 1 →
      finPart D (Formalism.L2.JoinChr.locE D q.e z) ∈ intAE D := by
    intro z hz
    rw [GlobalTheory.ChainOnto.locE_eq, ← q.sec_pr, map_add, (finPart D).map_sub, (finPart D).map_one]
    refine add_mem ((q.int_iff _).1 ?_) (sub_mem (GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (mul_one 1))
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← (finPart D).map_mul, hee])))
    exact (Valuation.mem_integer_iff _ _).2 hz.le
  have hinv : q.pr (incA D (a : D.host.E)⁻¹) = (q.pr (incA D (a : D.host.E)))⁻¹ := map_inv₀ (q.pr.comp (incA D)) _
  have hUnr : UnramEverywhere D (_root_.GlobalTheory.Fam.pk_z W).eta :=
    GlobalTheory.EtaConjExist.unram_of_chrEq hL.eta (Formalism.L2.Host.CharFrame.isEta _).unr
  have hη : (_root_.GlobalTheory.Fam.pk_z W).eta y = 1 := hUnr y (by
      show infPart D (Formalism.L2.JoinChr.locE D q.e (a : D.host.E)) = 1
      rw [GlobalTheory.ChainOnto.locE_eq, map_add, (infPart D).map_mul, (infPart D).map_sub, (infPart D).map_one, hinf,
        zero_mul, zero_add, sub_zero])
    (hint _ h1) (hint _ (by rw [hinv, map_inv₀, h1, inv_one]))
  have hS : (Formalism.IndefR.Lift.chrStep (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta j).1 y = (_root_.GlobalTheory.Fam.pk_z W).mu0 j y := by
    unfold Formalism.IndefR.Lift.chrStep
    split_ifs <;> simp [hη]
  have hj : j - 1 + 1 = j := Nat.sub_add_cancel hj1
  have hH1 := hL.mu0 ⟨j - 1, by omega⟩
  have hH2 := hL.chi ⟨j - 1, by omega⟩
  dsimp only at hH1 hH2
  rw [hj] at hH1 hH2
  have hIP : Formalism.L2.JoinChr.IsPlIdem D q.e PP := by
    obtain ⟨h1', h2', v, ε, h3', h4'⟩ := hI.1
    exact ⟨h1', ⟨v, ε, h3', Or.inl ⟨h2', h4'⟩⟩, hI.2⟩
  have e1 := hH1.2 PP q.e hIP (Units.mk0 _ ha0) y rfl
  have e2 := hH2 PP hP a (Units.mk0 _ ha0) u rfl ha.symm
  apply Units.ext
  rw [hμx, hcomp, MonoidHom.inv_apply, Circle.coe_inv, hS, e1, ← e2, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_inv]
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiMulPsiInvMemCoreStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chi_mul_psi_inv_mem_range_algebraMap : ∀ {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC} {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : GlobalTheory.BigTop.PtAt ex Csz) (i : Fin D.R.m), p.PointConditions' → GlobalTheory.CovTop.RecTied D L → ∀ u : (p.F.lv2.lvl false).P, (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) ∈ Set.range (algebraMap p.T.Q.c.F D.what₂.LL) := by
  first | exact @_root_.GlobalTheory.CovTop.chi_mul_psi_inv_mem_core_alt | exact _root_.GlobalTheory.CovTop.chi_mul_psi_inv_mem_core_alt | (intros; apply _root_.GlobalTheory.CovTop.chi_mul_psi_inv_mem_core_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CofiniteLabelsAtStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_place_finite_set_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    {v : HeightOneSpectrum (𝓞 D.host.E) | (Ideal.absNorm v.asIdeal).Prime ∧
      ¬ ∃ Q : (blk p j (p.R.mu w)).Pl, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal ∧ labOf p j (p.R.mu w) Q = v}.Finite := by
  first | exact @_root_.GlobalTheory.FrameAutCof.cofinite_labels_at_alt | exact _root_.GlobalTheory.FrameAutCof.cofinite_labels_at_alt | (intros; apply _root_.GlobalTheory.FrameAutCof.cofinite_labels_at_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top
namespace GlobalTheory.Cp
abbrev BaseLevelTiedChoiceAlt (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    {P : Formalism.L2.Rows.RowSideFamily (Fm.ex x hx i) // _root_.Formalism.L2.Rows.RowSideDeterminedAlt ((sel Fm hc).2 x hx h i).T P}
abbrev SelectionDefiniteHeightCondition (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    {p : ℕ × ℕ // (Fm.D x i).s.Del = (p.1 : ℚ) ∧ (Fm.L x i).etaSz = ((Fm.D x i).R.m : ℝ) * (p.2 : ℝ)}
abbrev ColumnChoiceCompatibleSelection (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) (selP : _root_.GlobalTheory.Cp.BaseLevelTiedChoiceAlt 𝒜 sel) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    _root_.GlobalTheory.Cp.SquareIntegrableColumns ((sel Fm hc).2 x hx h i).T (selP Fm hc x hx h i).1
abbrev SelectionSpectralCondition (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt ((sel Fm hc).2 x hx h i)
def IndefiniteScaleAtPoint {𝒜 : FamClass} (sel : _root_.Formalism.L2.TwistSelection 𝒜) (selP : _root_.GlobalTheory.Cp.BaseLevelTiedChoiceAlt 𝒜 sel) (selDH : _root_.GlobalTheory.Cp.SelectionDefiniteHeightCondition 𝒜 sel) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm)
    (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x) :
    Formalism.L2.Indef.DefSub (selP Fm hc x hx h i).1.A3.fam3.amb3 → Formalism.L2.Indef.IndefScale (selP Fm hc x hx h i).1.A3.fam3.base3 :=
  fun Zs =>
    let z := Formalism.L2.DIV.ZscOfNum3 (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0
      (Formalism.L2.DIV.ofRecord (Fm.D x i) (Fm.L x i) (selDH Fm hc x hx h i).1.1 (selDH Fm hc x hx h i).1.2) (Equiv.refl _) (Fm.L x i).Nc Zs
    { z with l6m := fun j => z.l6m j - Fm.Csz * z.l6u, l6u := 0 }
abbrev SelectionBundle (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) (selS : _root_.GlobalTheory.Cp.SelectionSpectralCondition 𝒜 sel) (selP : _root_.GlobalTheory.Cp.BaseLevelTiedChoiceAlt 𝒜 sel) (selDH : _root_.GlobalTheory.Cp.SelectionDefiniteHeightCondition 𝒜 sel) (selC : _root_.GlobalTheory.Cp.ColumnChoiceCompatibleSelection 𝒜 sel selP) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    _root_.Formalism.IndefR.RealTBAlt ((sel Fm hc).2 x hx h i) (selP Fm hc x hx h i).1 (selC Fm hc x hx h i).c.face (selC Fm hc x hx h i).Sp
      (_root_.GlobalTheory.Cp.IndefiniteScaleAtPoint sel selP selDH Fm hc x hx h i) (selS Fm hc x hx h i)
def EventuallyAlongSelection {𝒜 : FamClass} (sel : _root_.Formalism.L2.TwistSelection 𝒜) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm)
    (Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x), Prop) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x), x0 ≤ x → ∀ i : Fm.Ix x, Q x hx h i
end GlobalTheory.Cp
namespace GlobalTheory.Fc
open GlobalTheory.Cp
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure BundleCondition (D : D7) (O : Obj D) (c : ℝ) : Type 1 where
  R : _root_.Formalism.L2.RecTAlt O.ex
  S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R
  P : Formalism.L2.Rows.RowSideFamily O.ex
  pin : _root_.Formalism.L2.Rows.RowSideDeterminedAlt R.T P
  DH : {p : ℕ × ℕ // D.s.Del = (p.1 : ℚ) ∧ O.L.etaSz = (D.R.m : ℝ) * (p.2 : ℝ)}
  C : _root_.GlobalTheory.Cp.SquareIntegrableColumns R.T P
  B : _root_.Formalism.IndefR.RealTBAlt R P C.c.face C.Sp (zsc P DH.1.1 DH.1.2 c) S
variable {𝒜 : FamClass} (σ : RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜)
def familySelection : _root_.Formalism.L2.TwistSelection 𝒜 := fun Fm hc => ⟨Fm.x1, fun x hx _ i => (σ Fm hc x hx i).R⟩
def spectralConditionOfRawSelection : _root_.GlobalTheory.Cp.SelectionSpectralCondition 𝒜 (_root_.GlobalTheory.Fc.familySelection σ) := fun Fm hc x hx _ i => (σ Fm hc x hx i).S
def baseLevelChoiceOfRawSelection : _root_.GlobalTheory.Cp.BaseLevelTiedChoiceAlt 𝒜 (_root_.GlobalTheory.Fc.familySelection σ) := fun Fm hc x hx _ i => ⟨(σ Fm hc x hx i).P, (σ Fm hc x hx i).pin⟩
def definiteHeightOfRawSelection : _root_.GlobalTheory.Cp.SelectionDefiniteHeightCondition 𝒜 (_root_.GlobalTheory.Fc.familySelection σ) := fun Fm hc x hx _ i => (σ Fm hc x hx i).DH
def columnChoiceOfRawSelection : _root_.GlobalTheory.Cp.ColumnChoiceCompatibleSelection 𝒜 (_root_.GlobalTheory.Fc.familySelection σ) (_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) := fun Fm hc x hx _ i => (σ Fm hc x hx i).C
def selectionBundleOfRawSelection : _root_.GlobalTheory.Cp.SelectionBundle 𝒜 (_root_.GlobalTheory.Fc.familySelection σ) (_root_.GlobalTheory.Fc.spectralConditionOfRawSelection σ) (_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) (_root_.GlobalTheory.Fc.definiteHeightOfRawSelection σ) (_root_.GlobalTheory.Fc.columnChoiceOfRawSelection σ) := fun Fm hc x hx _ i => (σ Fm hc x hx i).B
end GlobalTheory.Fc
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CommOfIs
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.CommIs
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt GlobalTheory.Core.Mi
end GlobalTheory.Fam.CommIs
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt in
theorem GlobalTheory.Fam.commOf_is_of_geoMeas_of_coords_is : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ g : GlobalTheory.Fam.Geo D, GeoMeas (_root_.GlobalTheory.Fam.pk_z W) g → (∀ j, j ≤ D.R.m → (g.x j).Is) → (commOf (_root_.GlobalTheory.Fam.pk_z W) u g).Is := by
  intro hDS hHC D L hT Gi Gl Kc Yd cX ex W u hp g hm hx
  have hC : W.Q.Rl.Char3 W.Q.F := hp.bot.hyp.2.2.2.1
  have hS : StepsOK (_root_.GlobalTheory.Fam.pk_z W) := GlobalTheory.Chain.StepVac.stepsOK _ _ _ _ _ _ (_root_.GlobalTheory.Fam.pk_z W) hC.lev hC.models.inf hC.chain.ωY hC.chain.ωX
    hC.chain.vY hC.chain.vX
  have hθ : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := hC.models.inf
  have hm1 : D.R.m - 1 < D.R.m := Nat.sub_lt (lt_of_lt_of_le two_pos D.R.two_le_m) one_pos
  have hY : ∀ j, j + 1 < D.R.m → GlobalTheory.Core.Mi.ItSpans ((_root_.GlobalTheory.Fam.pk_z W).MY j) ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ItY j) := by
    intro j hj
    have h := hS.1 W.P.A3.A.μ0 ⟨j, by omega⟩ hj
    obtain ⟨χS, χT, hω, he⟩ := h.1
    exact GlobalTheory.Fam.CommIs.itSpans_of hDS hHC _ _ _ _ _ _ _ _ _ hθ ⟨χS, χT, hω, he⟩ h.2 (hC.chain.ItY W.P.A3.A.μ0 j hj)
  have hX : GlobalTheory.Core.Mi.ItSpans ((_root_.GlobalTheory.Fam.pk_z W).MY (D.R.m - 1)) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ItX := by
    have h := hS.2 W.P.A3.A.μ0 ⟨D.R.m - 1, hm1⟩ rfl
    obtain ⟨χS, χT, hω, he⟩ := h.1
    exact GlobalTheory.Fam.CommIs.itSpans_of hDS hHC _ _ _ _ _ _ _ _ _ hθ ⟨χS, χT, hω, he⟩ h.2 (hC.chain.ItX W.P.A3.A.μ0)
  have hXc : ∀ n (e : D.R.m - 1 = n), GlobalTheory.Core.Mi.ItSpans ((_root_.GlobalTheory.Fam.pk_z W).MY n) (_root_.GlobalTheory.Fam.pk_z W).MX
      (Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] SmT ((_root_.GlobalTheory.Fam.pk_z W).MY n))
        (_root_.GlobalTheory.Fam.pk_z W).ItX e) := by
    intro n e
    subst e
    exact hX
  refine ⟨W.Q.stdChar, hθ, hx, GlobalTheory.SeeSaw.Inh.coCpt_of_isDefinite D.sp.X'_sig fun τ => Or.inl (D.X'_posDef τ), hm.μf, hm.ρJ,
    hm.ρB, fun j hj => hY j hj, fun j h => hXc (j + 1) (idx_top h)⟩
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CondUnif
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Topology
noncomputable section
namespace GlobalTheory.WeilCondUnif
open GlobalTheory.FinPl GlobalTheory.SplitCharCond
section Local
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Local
section Unif
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {K : Type} [Field K] [NumberField K]
end Unif
theorem cond_unif_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (a : XGeo D) (PP : Pl D.host.E), PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP → ∀ l : LocX a (_root_.GlobalTheory.Fam.pk_z W).βX PP, (∃ ψk : AddChar l.k Circle, (ofSplit l.q).IsChar (_root_.GlobalTheory.Fam.pk_z W).ψ ψk ∧ HasConductor ψk 1) ∧ (∃ ν : Measure l.k, IsUnitVol ν) ∧ (_root_.GlobalTheory.Fam.QAllAlt W PP → ∃ ϖ : l.kˣ, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ ∧ GlobalTheory.SymBridge.IsCompl PP (Formalism.L2.Col.qOf PP) (l.q.pr.comp (incA D)) ϖ) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a PP hPP l
  have hstd : IsStdChar D (_root_.GlobalTheory.Fam.pk_z W).ψ (-1) := W.Q.stdChar
  refine ⟨?_, GlobalTheory.SplitWeil.exists_isUnitVol l.k, fun hQ => ?_⟩
  · obtain ⟨⟨ψk, hψk⟩, -, hxi, -⟩ := GlobalTheory.LocChar.weil_char_split D l.k (ofSplit l.q) (_root_.GlobalTheory.Fam.pk_z W).ψ hstd
    exact ⟨ψk, hψk, hasConductor_weil l.q l.unit _ hstd ψk hψk hxi⟩
  · obtain ⟨t, ht⟩ := hQ
    obtain ⟨⟨p, -, hcard, hp2, -⟩, -⟩ := W.Q.charW.base.lev.Q_pl t PP ht
    have hqp : Formalism.L2.Col.qOf PP = p := by
      rw [← hcard]
      unfold Formalism.L2.Col.qOf
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have hq2 : ((Formalism.L2.Col.qOf PP : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2 := by rw [hqp]; exact hp2
    obtain ⟨k', _, _, _, _, q', hqe, -, hint', hd'⟩ := GlobalTheory.LocMod.SplitCompl.exists_place D PP l.q.e l.idem
    have hint : ∀ x, (l.q.pr.comp (incA D)) x ∈ 𝒪[l.k] ↔ Formalism.L2.Col.IntAt PP x := fun x =>
      (int_transfer l.q q' hqe.symm (incA D x)).trans (hint' x)
    have hd := dense_transfer l.q q' hqe.symm hd'
    obtain ⟨ϖ, hu, hϖ⟩ := isUnif_of PP _ hint hd hq2
    exact ⟨ϖ, hu, ⟨hint, hd, rfl, hϖ⟩⟩
end GlobalTheory.WeilCondUnif
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreLeOfGramMeasRat
section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
namespace GlobalTheory.CoreSlope
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem coreLe_of_gram_meas_rat_alt : _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.MeasureCondition → _root_.GlobalTheory.CovTop.LiftRational → _root_.GlobalTheory.CovTop.CoreBound' := by
  intro hg hm hr
  unfold _root_.GlobalTheory.CovTop.GramCondition _root_.GlobalTheory.CovTop.MeasureCondition _root_.GlobalTheory.CovTop.LiftRational _root_.GlobalTheory.CovTop.CoreBound' _root_.GlobalTheory.CovTop.LiftsCondition at *
  refine Closed.imp (Closed.and (Closed.and hg hm) hr) ?_
  rintro eps Fm CH - ⟨⟨⟨C1, -, hg'⟩, ⟨C, hC, hm'⟩⟩, ⟨C3, -, hr'⟩⟩
  refine ⟨2 * C, by linarith, ?_⟩
  obtain ⟨x0, h⟩ := (hg'.and hm').and hr'
  exact ⟨x0, fun x hx hle ι p hp i =>
    coreAt_of p i C ((h x hx hle ι p hp).1.1 i) ((h x hx hle ι p hp).1.2 i) ((h x hx hle ι p hp).2 i)⟩
end GlobalTheory.CoreSlope
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoversOfLifts
section
set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.CovTop.CovSz
theorem covers_and_alt
    {Q Q' : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (_Y : Cov p i) (PP : ℝ), Prop}
    (h : _root_.GlobalTheory.CovTop.CoversCondition fun Fm x hx ι p i Y PP _ => Q Fm x hx ι p i Y PP)
    (h' : _root_.GlobalTheory.CovTop.CoversCondition fun Fm x hx ι p i Y PP _ => Q' Fm x hx ι p i Y PP) :
    _root_.GlobalTheory.CovTop.CoversCondition fun Fm x hx ι p i Y PP _ => Q Fm x hx ι p i Y PP ∧ Q' Fm x hx ι p i Y PP := by
  refine (Formalism.MainNotions.Closed.and h h').imp fun Fm CH _ hh => ?_
  obtain ⟨⟨C, hC, a, ha⟩, ⟨C', hC', b, hb⟩⟩ := hh
  exact ⟨C, hC, max a b, fun x hx hle ι p hp i hi Y hY =>
    ⟨ha x hx ((le_max_left _ _).trans hle) ι p hp i hi Y hY, hb x hx ((le_max_right _ _).trans hle) ι p hp i hi Y hY⟩⟩
theorem covers_of_lifts_alt
    {P : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (PP C : ℝ), Prop}
    {Q : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (_Y : Cov p i) (PP : ℝ), Prop}
    (h : _root_.GlobalTheory.CovTop.LiftsCondition P)
    (hQ : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (C : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → P Fm x hx ι p i (Fm.parT x hx ι).PP C → (i : ℕ) + 1 < (Fm.D x ι).R.m →
      ∀ Y : Cov p i, GoodCov p i Y → Q Fm x hx ι p i Y (Fm.parT x hx ι).PP) :
    _root_.GlobalTheory.CovTop.CoversCondition fun Fm x hx ι p i Y PP _ => Q Fm x hx ι p i Y PP := by
  refine h.imp fun Fm CH _ hh => ?_
  obtain ⟨C, hC, a, ha⟩ := hh
  exact ⟨C, hC, a, fun x hx hle ι p hp i hi Y hY => hQ Fm x hx ι p i C hp (ha x hx hle ι p hp i) hi Y hY⟩
theorem covers_of_covers_of_imp
    {Q R : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (_Y : Cov p i) (PP : ℝ), Prop}
    (h : _root_.GlobalTheory.CovTop.CoversCondition fun Fm x hx ι p i Y PP _ => Q Fm x hx ι p i Y PP)
    (hQ : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (Y : Cov p i) (PP : ℝ), Q Fm x hx ι p i Y PP → R Fm x hx ι p i Y PP) :
    _root_.GlobalTheory.CovTop.CoversCondition fun Fm x hx ι p i Y PP _ => R Fm x hx ι p i Y PP := by
  refine h.imp fun Fm CH _ hh => ?_
  obtain ⟨C, hC, a, ha⟩ := hh
  exact ⟨C, hC, a, fun x hx hle ι p hp i hi Y hY => hQ Fm x hx ι p i Y _ (ha x hx hle ι p hp i hi Y hY)⟩
end GlobalTheory.CovTop.CovSz
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CovolXOfSteps
section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.AllWt GlobalTheory.BigTop Filter Topology
namespace GlobalTheory.CovTop.Assembly
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem covolX_of_lift_bounds_and_coreLe : _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftRecursive → _root_.GlobalTheory.CovTop.LiftTruncation → _root_.GlobalTheory.CovTop.LiftBadSet → _root_.GlobalTheory.CovTop.LiftLambdaBound → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoreBound' → _root_.GlobalTheory.CovTop.LiftLowBound → _root_.GlobalTheory.CovTop.CovolumeBoundOfX := by
  intro hG hR hC hB hL hS hK hW
  refine Closed.imp (Closed.and (Closed.and (Closed.and hG hR) (Closed.and hC hB))
    (Closed.and (Closed.and hL hS) (Closed.and hK hW))) ?_
  rintro eps Fm CH he ⟨⟨⟨⟨_, -, g⟩, ⟨_, -, r⟩⟩, ⟨⟨_, -, c⟩, ⟨_, -, b⟩⟩⟩, ⟨⟨A, -, l⟩, ⟨B, -, s⟩⟩, ⟨C1, h1, k⟩, ⟨C2, h2, w⟩⟩
  have hez : 0 < Fm.ez := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_ez 0 i]
    exact (Fm.L 0 i).sc.ez_pos
  obtain ⟨x0, hx0⟩ := exists_loss_le (show 0 < Fm.ez / 7 by positivity) A B (C1 + C2 + 1)
  obtain ⟨x1, h⟩ := (((g.and r).and (c.and b)).and ((l.and s).and (k.and w)))
  refine ⟨C1 + C2 + 1, by linarith, max x0 x1, fun x hx hle ι p hp C hC i => ?_⟩
  obtain ⟨⟨⟨g, r⟩, c, b⟩, ⟨l, s⟩, k, w⟩ := h x hx ((le_max_right _ _).trans hle) ι p hp
  have ex := Fm.L_x x ι hx
  have ee := Fm.L_ez x ι
  have hs := hx0 x ((le_max_left _ _).trans hle)
  have hx' : 0 < x := (zero_lt_one.trans Fm.one_lt_family_threshold).trans hx
  have main := lcv_le p i (ex.symm ▸ hx') h1 h2 (by rw [ex, ee]; exact hs) (g i) (r i) (c i) (b i) (l i) (s i) (k i) (w i)
  have hE : 0 ≤ unitE p := by
    obtain ⟨s1, s2, -⟩ := s i
    linarith
  refine main.trans ?_
  show mainT p i + (C1 + C2 + 1) * unitE p ≤ mainT p i + C * unitE p
  have := mul_le_mul_of_nonneg_right hC hE
  linarith
end GlobalTheory.CovTop.Assembly
end
end
end

