module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelRuleSection
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0001
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalRingCardinality.Bundle0003
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
public import Development.WeilBound.CoreStatements.NefModelVolumes.TwoLtHalfFinrank
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0008
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusFlagUnitWeightBundlesNef
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1664
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.ConstantSupremum.Imports
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0006
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.DetLineExistsHorizontalSection
section
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.DetLine
open ReciprocityTheory.ChartRestriction.G.PullbackSections.AnFrameC ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows GlobalTheory.DetLine.GoodTransport
namespace GlobalTheory.DetLine.PeriodFlat
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}
section Linear
variable {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} {Hm : Matrix (Fin g) (Fin g) ℂ}
end Linear
section Fibre
variable {Xo : Moduli D l} {σ : KA l →+* ℂ} {g₀ : ℕ} {ty : Fin g₀ → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n)
variable {Fu i} {P : (Fu.Di i).La →+ (Fin g₀ → ℂ)}
end Fibre
section Model
variable {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {U : (Xo.XF c).Opens} {τ : E →+* ℂ}
end Model
end GlobalTheory.DetLine.PeriodFlat
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.BdryUnit in
theorem GlobalTheory.DetLine.PeriodFlat.detLine_exists_horizontal_section : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.CanonicalExtensionRankOne → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H), ∃ (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1), (V : Set (Xo.XF c)) = Z ∧ sig ∈ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.sections Y V τ.1 ∧ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig ∧ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsHorizontal sig := by
  intro hp _ E _ _ _ H Dw l Xo c r U x hL Z τ
  obtain ⟨Y, -⟩ := hp.p1 E H Dw hL.pos l Xo c
  obtain ⟨V, hV, hirr⟩ := GlobalTheory.GeomIrrComp.exists_open_irreducibleSpace_baseChange E H Dw l Xo c hL.geo Z
  have hc : IsClosed (V : Set (Xo.XF c)) := hV ▸ isClosed_of_mem_irreducibleComponents _ Z.2
  have hG : GeometricallyConnected (V.ι ≫ toF Xo c) :=
    ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.2 fun K _ _ => by
      have := hirr K (algebraMap c.F K)
      exact (inferInstance : ConnectedSpace ↑(pullback (V.ι ≫ toF Xo c) (spMap (algebraMap c.F K))))⟩
  obtain ⟨-, σ, -, -, hf, -, hY⟩ := detLineTrivial_of_toroidal hp.p1 E H Dw l Xo c V hc hG τ.1 τ.2
  obtain ⟨σb, hs, hz, hres, -⟩ := hY _ _ Y (GlobalTheory.FlatRow.isNormal_genFibre Y)
  refine ⟨Y, V, fun R _ _ a => σb R a.x a.v a.w, hV, fun R R' _ _ j j' a a' f M N h => ?_,
    fun R _ j a => hz R j _ _ _ (PeriodFlat.frY_framed a), PeriodFlat.isHorizontal_of_isFlatAt hc hres hz hf⟩
  rw [mul_comm, mul_comm _ N.det]
  exact (sec_chg hs (PeriodFlat.frY_framed a) (PeriodFlat.frY_framed a') ⟨h.2.1, h.2.2⟩).symm
end
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.BdryUnit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detLine_period_flat : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.CanonicalExtensionRankOne → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H), ∃ (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1), (V : Set (Xo.XF c)) = Z ∧ sig ∈ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.sections Y V τ.1 ∧ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig ∧ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsHorizontal sig := by
  first | exact @_root_.GlobalTheory.DetLine.PeriodFlat.detLine_exists_horizontal_section | exact _root_.GlobalTheory.DetLine.PeriodFlat.detLine_exists_horizontal_section | (intros; apply _root_.GlobalTheory.DetLine.PeriodFlat.detLine_exists_horizontal_section <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsTwistedSectionWithDeepRoot
section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.KeyTwDeep
theorem exists_twisted_section_root_of_depth : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, Nonempty (GlobalTheory.FlatTw.TwSec Y.U (xiR D) Z (wtOf (T.Q.Dw j) 0 1)) := by
  intro _ D T hT j hp _ _ hj Y e o hG _ _ Z
  have hg0 : ∀ p : ℕ, p.Prime → T.Q.l.GoodAt p :=
    Formalism.L2.Pj.goodAt_of_two_primes hT.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
  have hg : ∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p := GlobalTheory.LawsDeep.goodAt_of_mul _ _ _ hG.lev.1.2.1 hg0
  exact twSec_keyRoot _ _ _ _ _ _ _ _ _ hG.unf hG.xiAbs hG.geo (le_add_right hp) hg Z
end GlobalTheory.KeyTwDeep
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twisted_section_with_deep_root : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, Nonempty (GlobalTheory.FlatTw.TwSec Y.U (xiR D) Z (wtOf (T.Q.Dw j) 0 1)) := by
  first | exact @_root_.GlobalTheory.KeyTwDeep.exists_twisted_section_root_of_depth | exact _root_.GlobalTheory.KeyTwDeep.exists_twisted_section_root_of_depth | (intros; apply _root_.GlobalTheory.KeyTwDeep.exists_twisted_section_root_of_depth <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HeightAddLogNonneg
section
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
namespace GlobalTheory.CovHt.HtTopG
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} {p : PtAt ex Csz} {i : Fin D.R.m} {Y : Cov p i}
theorem height_add_log_nonneg (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) {u1 : AllWt.Weight (dat p i)} {Z : Comp Y.d.Xo₂ Y.d.c₂} {n : ℕ}
    {w : Fin n → cuspOn Y.U Z (wtOf (dat p i) u1 0)} {abelian₂ : ℝ}
    (hw : IsShortGen (normOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0))
        (latOn Y.U Z (wtOf (dat p i) u1 0)) w abelian₂)
    (hG : GoodOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0)) (hd : 0 < Y.dg u1 Z) :
    0 ≤ Y.ht u1 Z + Real.log abelian₂ := by
  haveI hTC : IsTotallyComplex Y.d.c₂.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := Y.d.c₂) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  have hd' : 0 < compDeg Y.U Z (wtOf (dat p i) u1 0) := by exact_mod_cast hd
  exact _root_.GlobalTheory.ImageHeightNonneg.imageHeight_nonneg_of_divisor hP _ _ _ _ _ _ _ _ w abelian₂ hG.1 (fun σ f => petOn_conj _ _ _ _ Z _ σ f) hG.2.2 hw hd'
theorem slope_le_height (hPX : _root_.SelfIntersectionVolumeEstimates.VolumeEstimateHypotheses) (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (hHT : HTCmp Y.d.Xo₂ Y.d.c₂)
    {u1 : AllWt.Weight (dat p i)} {Z : Comp Y.d.Xo₂ Y.d.c₂} {n : ℕ}
    {w : Fin n → cuspOn Y.U Z (wtOf (dat p i) u1 0)} {abelian₂ : ℝ}
    (hw : IsShortGen (normOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0))
        (latOn Y.U Z (wtOf (dat p i) u1 0)) w abelian₂)
    (hGo : GoodOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0))
    (hBir : GlobalTheory.DegVal.BirOn Y.U Z (wtOf (dat p i) u1 0))
    (hdel : (1 - rhoB (dat p i) u1) * Y.dg u1 Z ≤ delPrime Y.U Z u1) (hρ : rhoB (dat p i) u1 < 1) (hd : 0 < Y.dg u1 Z)
    {cc B s cs : ℝ} (hM : Mult Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z u1 (uPrime (dat p i) u1) cc)
    (hcc : 0 ≤ cc) (hh : 0 ≤ htCost Y.d.l₂ B * l1 (uPrime (dat p i) u1)) (hcs : Real.log abelian₂ ≤ cs)
    (hnn : 0 ≤ Y.ht u1 Z + cs)
    (hs : (s : EReal) ≤ compVolSlope Y.U (xiR D) 8 (mixVals Y.d.Xo₂ Y.d.c₂ B) Z (uPrime (dat p i) u1)) :
    (1 - rhoB (dat p i) u1) * max 0 (s + cs) ≤ Y.ht u1 Z + cs + (cc + htCost Y.d.l₂ B * l1 (uPrime (dat p i) u1)) := by
  have h1ρ : 0 < 1 - rhoB (dat p i) u1 := by linarith
  have hdelpos : 0 < topDeg Y.U Z (uPrime (dat p i) u1) :=
    lt_of_lt_of_le (mul_pos h1ρ hd) hdel
  have hf := two_lt_half_finrank D
  set hc := htCost Y.d.l₂ B * l1 (uPrime (dat p i) u1) with hhc
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hA := (le_compVolSlope_iff Y.U (xiR D) 8 (mixVals Y.d.Xo₂ Y.d.c₂ B) hdelpos s).1 hs cs
  have hB := GlobalTheory.CovHtCmp.compVol_le_volL_deep D p.T.toCore ((i : ℕ) + 1) Y e o hY hf hHT Z u1 (uPrime (dat p i) u1) cc B cs ε hM hε
  have hC := _root_.SelfIntersectionVolumeEstimates.VolUpG.volume_line_bundle_le hPX hP D p.T.toCore ((i : ℕ) + 1) Y e o hY hf Z u1 n w abelian₂ (cs + cc + hc + ε) hGo hBir hM.1 hd hw
    (by linarith)
  have hABC := hA.trans (hB.trans hC)
  have hpos : 0 ≤ Y.dg u1 Z * (Y.ht u1 Z + (cs + cc + hc + ε)) := mul_nonneg hd.le (by linarith)
  rw [ENNReal.ofReal_le_ofReal_iff hpos] at hABC
  change delPrime Y.U Z u1 * (s + cs) ≤ _ at hABC
  have key : (1 - rhoB (dat p i) u1) * max 0 (s + cs) * Y.dg u1 Z ≤ (Y.ht u1 Z + cs + (cc + hc) + ε) * Y.dg u1 Z := by
    rcases le_total (s + cs) 0 with h | h
    · rw [max_eq_left h, mul_zero, zero_mul]
      exact mul_nonneg (by linarith) hd.le
    · rw [max_eq_right h]
      calc (1 - rhoB (dat p i) u1) * (s + cs) * Y.dg u1 Z = ((1 - rhoB (dat p i) u1) * Y.dg u1 Z) * (s + cs) := by ring
        _ ≤ delPrime Y.U Z u1 * (s + cs) := mul_le_mul_of_nonneg_right hdel h
        _ ≤ _ := hABC
        _ = _ := by ring
  exact le_of_mul_le_mul_right key hd
theorem heightAt_eq_of_cover (hPX : _root_.SelfIntersectionVolumeEstimates.VolumeEstimateHypotheses) (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (hHT : HTCmp Y.d.Xo₂ Y.d.c₂)
    {C0 Cs Cm Cb PP : ℝ} (h0 : 0 ≤ C0) (hs0 : 0 ≤ Cs) (hm0 : 0 ≤ Cm) (hb0 : 0 ≤ Cb) (hU : 0 ≤ unitE p)
    (hmean : MeanAll Y.U (xiR D) (ell D) C0) (hne : Nonempty (Comp Y.d.Xo₂ Y.d.c₂)) {u1 : AllWt.Weight (dat p i)}
    (hρ : rhoB (dat p i) u1 < 1) (hDeg : DegAt p i Y u1) (hS : ShortAt p i Y PP Cs u1) (hGe : GeomAt p i Y u1)
    (hM : MultAt p i Y PP Cm u1) (hB : BudgetAt p i Y PP Cb u1) :
    HeightAt p i Y PP (Cs + Cm + Cb + C0 * Cb) u1 := by
  obtain ⟨abelian₂, hLam, hSb⟩ := hS
  obtain ⟨cc, hcc, hccb, hMZ⟩ := hM
  obtain ⟨-, g, hgap, herr0, herrb, hht0, hhtb⟩ := hB
  obtain ⟨sl, hsl, hX⟩ := hmean (uPrime (dat p i) u1) g hgap
  obtain ⟨δ, hδ, hδZ⟩ := hDeg
  have hdg : ∀ Z, 0 < Y.dg u1 Z := fun Z => lt_of_lt_of_le hδ (hδZ Z).1
  have hLam1 : 1 ≤ abelian₂ := by
    obtain ⟨Z⟩ := hne
    obtain ⟨n, w, hw⟩ := hLam Z
    exact hw.one_le
  have hcs : 0 ≤ Real.log abelian₂ := Real.log_nonneg hLam1
  have hl1 : 0 ≤ l1 (uPrime (dat p i) u1) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hhc : 0 ≤ htCost Y.d.l₂ (bndB (uPrime (dat p i) u1) g) * l1 (uPrime (dat p i) u1) := mul_nonneg hht0 hl1
  have hT : (0 : ℝ) ≤ lenT p i PP := Nat.cast_nonneg _
  have hnn : ∀ Z, 0 ≤ Y.ht u1 Z + Real.log abelian₂ := fun Z => by
    obtain ⟨n, w, hw⟩ := hLam Z
    exact _root_.GlobalTheory.CovHt.HtTopG.height_add_log_nonneg hP hw (hGe Z).1 (hdg Z)
  have e1 : 0 ≤ Cs * unitE p := mul_nonneg hs0 hU
  have e2 : 0 ≤ Cm * unitE p := mul_nonneg hm0 hU
  have e3 : 0 ≤ Cb * unitE p := mul_nonneg hb0 hU
  have e4 : 0 ≤ C0 * Cb * unitE p := mul_nonneg (mul_nonneg h0 hb0) hU
  refine ⟨Real.log abelian₂, cc + htCost Y.d.l₂ (bndB (uPrime (dat p i) u1) g) * l1 (uPrime (dat p i) u1),
    C0 * errX (ell D) (uPrime (dat p i) u1) g, sl, hcs, add_nonneg hcc hhc, mul_nonneg h0 herr0, hnn, fun Z => ?_, hX,
    ?_, ?_, ?_⟩
  · obtain ⟨n, w, hw⟩ := hLam Z
    exact _root_.GlobalTheory.CovHt.HtTopG.slope_le_height hPX hP hY hHT hw (hGe Z).1 (hGe Z).2.1 (hGe Z).2.2 hρ (hdg Z) (hMZ Z) hcc hhc le_rfl (hnn Z) (hsl Z)
  · have : (lenT p i PP : ℝ) * (C0 * errX (ell D) (uPrime (dat p i) u1) g) ≤ C0 * Cb * unitE p := by
      rw [mul_left_comm, mul_assoc]
      exact mul_le_mul_of_nonneg_left herrb h0
    linarith
  · rw [mul_add]
    linarith
  · linarith
end Point
end GlobalTheory.CovHt.HtTopG
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.IsNefHodgeBundleUnitWeight
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NefUnit
open GlobalTheory.FlagMod (FlagCover Frames ev ev_res ev_spMap ext_ev tau tau_le spMap_ev ev_tau le_preimage_comp le_preimage_mono
  vec tanPull tanPull_actR tanPull_vec tan_ext_left ev_pull_g)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
open GlobalTheory.Toroidal (gen genι genStr)
open GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm (epsAt IsEigBasisAt IsCombAt IsFrame chi compactOf toF)
open GlobalTheory.DetLine (FrY RuleY SecY NzY)
section Glue
variable {W : Scheme.{0}}
end Glue
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y)
theorem isNef_hodgeBundle_unitWeight : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ τ : Psi H, letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.unitWt τ 1)) ∧ IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.unitWt τ (-1))) := by
  intro hP _ E _ _ _ H Dw l Xo c TF Z hF τ
  letI := algebraΓOfHom (str₀ TF.X Z)
  have hp := (VarFlag.isVariety₀_flag E H Dw l Xo c TF Z hF).2.1
  exact ⟨(isGenerated_unitWt hP.p1 TF Z hF τ 1).isNef_of_isProjOver hp,
    (isGenerated_unitWt hP.p1 TF Z hF τ (-1)).isNef_of_isProjOver hp⟩
end GlobalTheory.NefUnit
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeBundle_unitWeight_nef : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ τ : Psi H, letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.unitWt τ 1)) ∧ IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.unitWt τ (-1))) := by
  first | exact @_root_.GlobalTheory.NefUnit.isNef_hodgeBundle_unitWeight | exact _root_.GlobalTheory.NefUnit.isNef_hodgeBundle_unitWeight | (intros; apply _root_.GlobalTheory.NefUnit.isNef_hodgeBundle_unitWeight <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberUpperBoundAlt
section
section
namespace MainStatements.Tam.Plug
theorem tamagawa_number_upper_bound : _root_.MainStatements.Tam.ArchimedeanTamagawaUpperBound := _root_.MainStatements.Tam.tamagawa_number_upper_bound MainStatements.Tam.vol MainStatements.Tam.stab MainStatements.Tam.num
end MainStatements.Tam.Plug
end
end

