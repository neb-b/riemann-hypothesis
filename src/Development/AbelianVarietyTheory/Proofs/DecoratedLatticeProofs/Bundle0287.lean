module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0281
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0285
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.GammaRangeOfSizeHypotheses
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagAtScale
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0087
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0275
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0080
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0287
public import Formalism.LocalToGlobal.Columns.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0158
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0448
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CollSOn
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem collS_on : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ S : Set ℝ, AmpOn S → CountBoundOn S → SmallOn S → TieOn S → On S CollS := by
  intro hSMR S hAmp hCnt hSmall hTie
  intro Cg cb Cu cT CT hcb hcT
  obtain ⟨c3, cH, thr1, hC⟩ := hCnt Cg cb Cu cT CT
  obtain ⟨cV, thr2, hT⟩ := hTie Cg cb Cu cT CT
  obtain ⟨Ca, C2, Ch, -, hCh, hA⟩ := hAmp Cg cb Cu cT CT hcb hcT
  set c : ℝ := max (max (max (max c3 1) CT) (|cH| + 2)) (|cV| + 2) with hc
  have hc3 : c3 ≤ c := le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) (le_max_left _ _))
  have hc1 : 1 ≤ c := le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) (le_max_left _ _))
  have hcT' : CT ≤ c := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hcH : |cH| + 2 ≤ c := le_trans (le_max_right _ _) (le_max_left _ _)
  have hcV : |cV| + 2 ≤ c := le_max_right _ _
  set C : ℝ := max (max (max (max (max c (4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2))) (2 * C2)) |Ca|)
    (408 * (Real.exp 1 * Real.pi))) CT with hCdef
  have hCc : c ≤ C := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hC4 : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C := le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hC2 : 2 * C2 ≤ C := le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hCa : |Ca| ≤ C := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hC408 : 408 * (Real.exp 1 * Real.pi) ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCT : CT ≤ C := le_max_right _ _
  obtain ⟨thr3, hA3⟩ := hA (9 * c + 3) 1 one_pos
  obtain ⟨thr4, hS⟩ := hSmall Cg cb Cu cT CT 1 hcb hcT one_pos
  obtain ⟨thr5, hsum⟩ := _root_.GlobalTheory.Core.Deg.collS_of_rowBounds hSMR CT C hC408 hCT
  refine ⟨max (max (max (max (max thr1 thr2) thr3) thr4) thr5) (max (3 * |C2|) 4), ?_⟩
  intro C0 hC0 C' Cl hC' hCl D large₂ X Y hF hI u hCG hTies hadm hH0 hConc hAbs
  have hle : ∀ {x : ℝ}, max (max (max (max (max thr1 thr2) thr3) thr4) thr5) (max (3 * |C2|) 4) ≤ x →
      thr1 ≤ x ∧ thr2 ≤ x ∧ thr3 ≤ x ∧ thr4 ≤ x ∧ thr5 ≤ x ∧ 3 * |C2| ≤ x ∧ 4 ≤ x := by
    intro x hx
    simp only [max_le_iff] at hx
    exact ⟨hx.1.1.1.1.1, hx.1.1.1.1.2, hx.1.1.1.2, hx.1.1.2, hx.1.2, hx.2.1, hx.2.2⟩
  obtain ⟨h1', h2', h3', h4', h5', h6', h7'⟩ := hle hC'
  obtain ⟨h1l, h2l, h3l, h4l, h5l, -, h7l⟩ := hle hCl
  have hCnt' := hC C0 hC0 C' Cl h1' h1l D large₂ u
  have hc3' := hCnt'.1 c hc3
  obtain ⟨T, Z, hTA, hVol⟩ := hT C0 hC0 C' Cl h2' h2l D large₂ X Y hF hI u hTies hH0 hConc
  have hAmpAt := hA3 C0 hC0 C' Cl h3' h3l D large₂ hCG hTies hadm hConc.2.2.2.2.2.2.2
  have hSm := hS C0 hC0 C' Cl h4' h4l D large₂ hTies hadm
  have hHyp : Cnt.Hyp D large₂ u u C' Cl Cg cb Cu cT CT C0 1 :=
    Formalism.MainNotions.count_hypotheses_diagonal_words D large₂ C' Cl Cg cb Cu cT CT C0 1 hH0.2.1 hH0.1 hH0.2.2 (by linarith) (by linarith) le_rfl u
  have hC2' : |C2| ≤ C' := by have := abs_nonneg C2; linarith
  have hDeg := _root_.GlobalTheory.Core.Deg.rowsDeg_at_record CT cH cV Ca C2 Ch c C hc1 hcT' hcH hcV hCh hCc hC4 hC2 hCa D large₂ u T Z C' Cl Cg cb Cu cT C0
    h6' hHyp hc3' hCnt'.2 hVol hAmpAt hSm hTA.2.2.2.1 hTA.2.2.2.2.1 hTA.2.2.2.2.2.1
  have hND := _root_.GlobalTheory.Core.Deg.rowsND_one_record CT cH cV Ca C2 Ch c C hc1 hcH hcV hCh hCc hC4 D large₂ u T Z C' Cl Cg cb Cu cT C0
    hC2' hHyp hc3' hCnt'.2 hVol hAmpAt hSm hTA.2.2.2.1 hTA.2.2.2.2.1 hTA.2.2.2.2.2.1
  exact hsum D large₂ X Y hF hI u T Z C' Cl Cg cb Cu cT C0 h5' h5l hH0 hConc hAbs hTA (hSm.2.2.2.2 hH0 u) hND hDeg

end GlobalTheory.Core.Deg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateVectorPairForm
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

noncomputable section

namespace GlobalTheory.MiTop.PairingL2

open Formalism.L2.SG.JoinSI Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowsJoinPinned

variable {D : D7}

theorem inner_sp {St : Formalism.L2.SG.HidaSetting.HidaSetting D} (s : Bool) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs}
    (Dc : DefCols Df) (hK : St.LevelSubgroupCharacter) (Gd : GoodOp St) (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW St hK (wdD x))
    (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram) (Sp : SPer Dc) (hSp : Sp = spOf s Dc hK Gd wdD pw bR)
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (sEE : E →ₗ⋆[ℂ] Sp.HH) (sEEc : E →ₗ⋆[ℂ] Tw s (HHX St)) (h : HEq sEE sEEc) (e : E) (m : Dc.Mem)
    (c : Fin (Dc.a m) → ℂ) :
    ⟪sEE e, Sp.Pu m (cjv s c)⟫_ℂ = cj s ⟪Tw.out (sEEc e), (pw m).op (ramCrd (bR m) c)⟫_ℂ := by
  subst hSp
  obtain rfl := eq_of_heq h
  exact inner_spOf s Dc hK Gd wdD pw bR m _ c

theorem inner_join {St : Formalism.L2.SG.HidaSetting.HidaSetting D} (s : Bool) {Bs : DefBase D.what₂.LL} {Z : Type}
    {sd : Z → DefSide Bs} (Dcf : ∀ z, DefCols (sd z)) (Spf : ∀ z, SPer (Dcf z)) (z0 z1 : Z) (hz : z0 = z1)
    (Dc : DefCols (sd z1)) (hdc : Dcf z1 = Dc) (hK : St.LevelSubgroupCharacter) (Gd : GoodOp St)
    (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW St hK (wdD x)) (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram)
    (hsp : HEq (Spf z1) (spOf s Dc hK Gd wdD pw bR))
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (sEE : E →ₗ⋆[ℂ] (Spf z0).HH) (sEEc : E →ₗ⋆[ℂ] Tw s (HHX St)) (h : HEq sEE sEEc) (e : E)
    (m : (Dcf z0).Mem) (m' : Dc.Mem) (hm : HEq m m') (c : Fin ((Dcf z0).a m) → ℂ) (c' : Fin (Dc.a m') → ℂ)
    (hc : HEq c c') :
    ⟪sEE e, (Spf z0).Pu m (cjv s c)⟫_ℂ = cj s ⟪Tw.out (sEEc e), (pw m').op (ramCrd (bR m') c')⟫_ℂ := by
  subst hz
  subst hdc
  obtain rfl := eq_of_heq hm
  obtain rfl := eq_of_heq hc
  exact inner_sp s (Dcf z0) hK Gd wdD pw bR (Spf z0) (eq_of_heq hsp) sEE sEEc h e m c

theorem iota_symm_eq {I : Formalism.MainNotions.S.AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ι : GA D (D.sp.Y 0) ≃* I.GA) (hι : HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv) (x : I.GA) :
    ι.symm x = ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)).symm x := by
  subst h
  obtain rfl := eq_of_heq hι
  rfl

end GlobalTheory.MiTop.PairingL2

namespace GlobalTheory.MiTop.PairingL2

open Formalism.L2.SG.JoinSI Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowsJoinPinned

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem op_eq {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {hK : X.LevelSubgroupCharacter} {u : D.what₂.Word} (p : PerW X hK u) (y : (D.mem u).A.Mu0)
    (T : Cu X u hK) (hT : Formalism.L2.SG.ColDict.colDictL X p.Tr hK T = (y : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)) :
    ((p.op y : HHX X) : L2X X) = PuFun X u hK p.Dt T := by
  have hd : (Formalism.L2.SG.ColDict.colDict X p.Tr hK p.hI p.hB).symm y = T := by
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext hT.symm
  show ((Formalism.L2.SG.PoincareInHH.PoincareSetting.Pu X u hK p.Dt p.hD p.hin p.hlin
    ((Formalism.L2.SG.ColDict.colDict X p.Tr hK p.hI p.hB).symm y) : HHX X) : L2X X) = _
  rw [hd]
  rfl

end GlobalTheory.MiTop.PairingL2

namespace GlobalTheory.MiTop.PairingL2

open Formalism.L2.SG.JoinSI Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowsJoinPinned

theorem exists_eval {D : D7} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))}
    {𝓕 : Set (GA D (D.sp.Y 0))} {E : Submodule ℂ (MMap M)} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} {Gd : GoodOp St}
    {ι : GA D (D.sp.Y 0) ≃* St.B.I.GA} {t : GA D (D.sp.Y 0)} {c : ℝ} (hE : EvalTieT M μ 𝓕 E St Gd ι t c)
    (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hι : HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv) :
    ∃ v₀ : M.Vec, (∀ τ, ‖(v₀ τ : M.H τ)‖ = 1) ∧ ∀ T : E, ∃ F : L2X St,
      ((F : St.B.I.GA → ℂ) =ᵐ[muX St] evS St h t (PiTensorProduct.lift (T : MMap M) (PiTensorProduct.tprod ℂ v₀))) ∧
      star F ∈ HHX St ∧ ((sEEofTT M μ 𝓕 E St Gd ι t c T : HHX St) : L2X St) = star F := by
  refine ⟨hE.choose, hE.choose_spec.1, fun T => ⟨(hE.choose_spec.2.choose T : EEC St Gd), ?_, ?_, ?_⟩⟩
  · refine (hE.choose_spec.2.choose_spec T).1.trans (Filter.Eventually.of_forall fun x => ?_)
    have h1 : ι.symm x = (iotaX St h).symm x := iota_symm_eq h ι hι x
    show (T : MMap M) hE.choose (ι.symm x * t) =
      PiTensorProduct.lift (T : MMap M) (PiTensorProduct.tprod ℂ hE.choose) ((iotaX St h).symm x * t)
    rw [h1]
    exact (congrFun (PiTensorProduct.lift.tprod (φ := (T : MMap M)) hE.choose) _).symm
  · exact ((mem_EEC St Gd _).1 (hE.choose_spec.2.choose T).2).1
  · unfold sEEofTT
    simp only [dif_pos hE]
    rfl

theorem inner_smul_star {D : D7} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (t : GA D (D.sp.Y 0)) (f g : GA D (D.sp.Y 0) → ℂ) (l a : ℂ) (hfg : f = l • g) (F φ P : L2X St)
    (hF : (F : St.B.I.GA → ℂ) =ᵐ[muX St] evS St h t f) (hφ : (φ : St.B.I.GA → ℂ) =ᵐ[muX St] evS St h t g)
    (y z : HHX St) (hy : (y : L2X St) = star F) (hz : (z : L2X St) = P) :
    ⟪a • y, z⟫_ℂ = starRingEnd ℂ a * l * ⟪star φ, P⟫_ℂ := by
  have h1 : F = l • φ := by
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [hF, hφ, MeasureTheory.Lp.coeFn_smul l φ] with x h1 h2 h3
    rw [h1, h3, Pi.smul_apply, h2, hfg]
    rfl
  have h2 : star (l • φ) = starRingEnd ℂ l • star φ := (Formalism.L2.SG.RowDict.conjL (muX St)).map_smulₛₗ l φ
  rw [inner_smul_left, Submodule.coe_inner, hy, hz, h1, h2, inner_smul_left, starRingEnd_self_apply, mul_assoc]

end GlobalTheory.MiTop.PairingL2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalTheoremOfFourPointBounds
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

noncomputable section
namespace GlobalTheory.Core.Diag
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exp_neg_le_two_fifths {x : ℝ} (hx : 2 ≤ x) : Real.exp (-x) ≤ 2 / 5 * Real.exp (-x / 2) := by
  have h2 : Real.exp (-x / 2) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
  have h1 : Real.exp (-1) < 2 / 5 := by
    rw [Real.exp_neg]
    have := Real.exp_one_gt_d9
    rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  have e : Real.exp (-x) = Real.exp (-x / 2) * Real.exp (-x / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

theorem diag_arith {H N₁ N₂ P s dd d E₂ E Γ₁ Γ₂ Γ : ℝ} (hH : H ≤ 3 / 2 * N₁ + 3 * N₂)
    (h₁ : N₁ ≤ 2 * P * (s * dd + E₂ * d + Γ₁ * dd + Γ₂ * dd)) (h₂ : N₂ ≤ d * E) (hP : P ≤ 6 / 5)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hdd : 0 ≤ dd) (hd : 0 ≤ d) (hE₂ : 0 ≤ E₂) (hE : E ≤ 2 / 5 * E₂)
    (hΓ₁ : 0 ≤ Γ₁) (hΓ₂ : 0 ≤ Γ₂) (hΓ : Γ₁ + Γ₂ ≤ Γ) :
    H ≤ 4 * ((Γ + 1) * dd + d * E₂) + 2 * d * E := by
  have hS : 0 ≤ s * dd + E₂ * d + Γ₁ * dd + Γ₂ * dd := by positivity
  have p1 : 2 * P * (s * dd + E₂ * d + Γ₁ * dd + Γ₂ * dd) ≤ 2 * (6 / 5) * (s * dd + E₂ * d + Γ₁ * dd + Γ₂ * dd) :=
    mul_le_mul_of_nonneg_right (by linarith) hS
  have p2 : s * dd ≤ dd := mul_le_of_le_one_left hdd hs1
  have p3 : (Γ₁ + Γ₂) * dd ≤ Γ * dd := mul_le_mul_of_nonneg_right hΓ hdd
  have p4 : d * E ≤ d * (2 / 5 * E₂) := mul_le_mul_of_nonneg_left hE hd
  nlinarith

theorem sDiagAt_of_points : ∀ (D : D7) (c : Formalism.L2.SG.ThmSOwn.ConcK D) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Γ₁ Γ₂ Γ : ℝ)
    (u : D.what₂.Word), 29 ≤ C' → 29 ≤ Cl → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 0 ≤ Γ₁ → 0 ≤ Γ₂ → Γ₁ + Γ₂ ≤ Γ →
    VanishingGramTermsBound c.Y u → CollS c.Y u →
    (c.Y.tO u u).pairSum ((c.Y.tO u u).one (c.Y.tO u u).genSet) ≤ Γ₁ * ddC c.X c.Y u u →
    (c.Y.tO u u).pairSum ((c.Y.tO u u).one (c.Y.tO u u).ngSet) ≤ Γ₂ * ddC c.X c.Y u u → SDiagAt D u Γ (1 / 2) := by
  intro D c large₂ C' Cl Cg cb Cu cT CT C0 Γ₁ Γ₂ Γ u hC' hCl h0 hg1 hg2 hg hG0 hColl hgen hng
  obtain ⟨hExp, hAbs⟩ := _root_.GlobalTheory.Core.Diag.kExp_absConv_tied
  have hT := c.tie
  have hA : (c.Y.tO u u).AbsConv := hAbs D c.X c.Y u u hT
  have hK2 := Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of D large₂ C' Cl Cg cb Cu cT CT C0 h0.2.1 h0.1 h0.2.2 (by linarith)
  have hPg : PgC c.Y ≤ 6 / 5 := _root_.GlobalTheory.Core.Deg.pgC_le_six_fifths C' Cl Cg cb Cu cT CT C0 D large₂ c.X c.Y hK2
  have hPg0 : 0 ≤ PgC c.Y := Finset.prod_nonneg fun v _ => by positivity
  have hGB : (c.Y.tO u u).GGBound (PgC c.Y) :=
    Formalism.L2.SG.TermOp.ggBound c.Y.TR (c.Y.cs u) (c.Y.cs u) (c.Y.FN u) (c.Y.FN u) Formalism.L2.SG.Closed.TermsGGBound_holds
      c.Y.psi_ne (fun v => card_ge_three hK2.2 c.Y.TR v)
  have hNE := normExpSatTied_holds D c.X c.Y u u hT
  have hK0 := _root_.GlobalTheory.diag_abstract_collisions_once _ _ _ _ _ (c.Y.tO u u) (oneC c.X c.Y u) (PgC c.Y) _ _ _ hPg0 hA hNE.1 hNE.2 hGB
    (Formalism.L2.SG.TermOp.rowOrth c.Y.TR (c.Y.cs u) (c.Y.cs u) (c.Y.FN u) (c.Y.FN u))
    (Formalism.L2.SG.KappaOffDiagonal.corankPosC_holds D c.X c.Y u u hT) (idOneC_holds D c.X c.Y u hT) hColl hgen hng
  have hsplit := _root_.GlobalTheory.Core.Rk.hsDev_le_split_three_halves D u
  rw [Formalism.L2.SG.ThmSOwn.hsNormSq_diag c.hI (hExp D c.X c.Y u u hT) hA (Formalism.L2.SG.Pf.SatGram.idDegenerate_tO c.Y u u),
    Formalism.L2.SG.ThmSOwn.hsNormSq_Kpp c.hI hA] at hsplit
  have hdd : 0 ≤ ddC c.X c.Y u u := dd_nonneg hT u u
  have hdu : duC c.X c.Y u = (D.duS u : ℝ) := hT.2.2.1 u
  have hddE : ddC c.X c.Y u u = (D.duS u : ℝ) ^ 2 / D.what₂.Dstar := by
    unfold ddC; rw [hdu, hT.2.2.2.1]; ring
  have hd0 : (0 : ℝ) ≤ duC c.X c.Y u := Nat.cast_nonneg _

  have hk5 : 5 ≤ D.R.k := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  have hf1 : 1 ≤ D.R.f := by
    have h4 : D.R.m ^ 4 ≤ D.R.f := h0.1.2.2.1
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by have := D.R.two_le_m; omega)
    omega
  have hkR : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk5
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1
  have hlog : 1 ≤ Real.log D.R.k := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hx2 : 2 ≤ (D.R.k : ℝ) * D.R.f * Real.log D.R.k := by
    have : (5 : ℝ) * 1 * 1 ≤ (D.R.k : ℝ) * D.R.f * Real.log D.R.k := by gcongr
    linarith
  have hE := exp_neg_le_two_fifths hx2

  have g0 : (1 : ℝ) ≤ (D.host.g 0 : ℝ) := by exact_mod_cast (D.host.g_prime 0).one_lt.le
  have g1 : (1 : ℝ) ≤ (D.host.g 1 : ℝ) := by exact_mod_cast (D.host.g_prime 1).one_lt.le
  have hq : 1 ≤ Real.sqrt ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := Real.one_le_sqrt.2 (one_le_mul_of_one_le_of_one_le g0 g1)
  have hi0 : 0 ≤ (Real.sqrt ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have key := diag_arith hsplit hK0 hG0.2 hPg (pow_nonneg hi0 _) (pow_le_one₀ hi0 (inv_le_one_of_one_le₀ hq)) hdd hd0
    (Real.exp_pos _).le hE hg1 hg2 hg
  have e1 : Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k) / 2) =
      Real.exp (-((1 / 2 : ℝ) * D.R.k * D.R.f * Real.log D.R.k)) := by
    congr 1; ring
  unfold SDiagAt
  unfold epsK at key
  rw [hddE, hdu, e1] at key
  calc _ ≤ _ := key
    _ = _ := by ring

end GlobalTheory.Core.Diag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiscreteSeriesDetSqrtCoverOfUnitaryClassificatio
section
open Formalism.BasicNotions.TH GlobalTheory.RealPar

noncomputable section

namespace GlobalTheory.CoverDS

theorem discreteSeriesCover_of_classification :
    GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.DiscreteSeriesCover := by
  intro hcl
  obtain ⟨hExists, hExhaust, hUnique, hInfChar, hLowK, hKTypes, -⟩ :=
    GlobalTheory.ClassificationConsequences.consequences_of_dsClass
      (GlobalTheory.Published.discreteSeriesClassification_iff.1 hcl)
  have hC : GlobalTheory.Published.DiscreteSeriesCoverExists :=
    GlobalTheory.Published.CoverSeries.of_upq
      (GlobalTheory.Published.discreteSeriesUpqExists_iff_dsExists.2 hExists)
      (fun p q h T U hU => ((GlobalTheory.T.harishChandraModules_indefiniteUnitaryGroup.1 p q h T).1 U hU).2.1)
  intro p q hn T
  choose D hD using fun lam : {lam : Ix p q → ℚ // IsParam lam} => hC p q T lam.1 lam.2
  refine ⟨D, ?_, ?_⟩
  · intro lam
    exact _root_.GlobalTheory.CoverDS.hasTypes_of_hasParam_of_group
      hLowK hKTypes hInfChar p q hn T (D lam) lam.1 lam.2 (hD lam)
  · intro R
    obtain ⟨lam, hl, hR⟩ := _root_.GlobalTheory.CoverExhaust.exists_param hExhaust p q hn T R
    exact ⟨⟨lam, hl⟩, _root_.GlobalTheory.CoverDS.unitEquiv_of_dsUnique
      hUnique p q hn T R (D ⟨lam, hl⟩) lam hl hR (hD ⟨lam, hl⟩)⟩

end GlobalTheory.CoverDS

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DisjointReferenceTwistPrimes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Core.Rk
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Rk.RowRead

theorem map_mem_span_range {K L M N J : Type*} [Semiring K] [Semiring L] [AddCommMonoid M] [AddCommMonoid N] [Module K M]
    [Module L N] {σ : K →+* L} (f : M →ₛₗ[σ] N) {φ : J → M} (h : Submodule.span K (Set.range φ) = ⊤) (z : M) :
    f z ∈ Submodule.span L (Set.range fun a => f (φ a)) := by
  have hz : z ∈ Submodule.span K (Set.range φ) := h ▸ Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact Submodule.subset_span ⟨a, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

section G
open GlobalTheory.PeriodOnStep
variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) {I : ChainIn X.E X.K X.Tau R} (b0 : (I.S R.m).β)
  (til : ∀ b, (stepX Ch sel mu P).D b → (I.S R.m).D b0) (ext : ∀ b, (stepX Ch sel mu P).G b →* (I.S R.m).G b0)
  (tz : X.E) (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K))) (σ : X.K →+* ℂ)

def valMt (H : ∀ b, Subgroup ((stepX Ch sel mu P).G b)) :
    (perOn W Ch sel mu P b0 til ext tz H).Mt X.emb σ →ₗ[ℂ] ((stepX Ch sel mu P).D () → Pol ℂ X.Tau (R.N R.m - 1)) where
  toFun F p := F.1 () p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def valMtP : MtP W Ch sel mu P σ →ₗ[ℂ] ((stepX Ch sel mu P).D () → Pol ℂ X.Tau (R.N R.m - 1)) where
  toFun G p := G.1 (toRow sel mu p.1.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem valMtP_injective : Function.Injective (valMtP W Ch sel mu P σ) := by
  intro G G' h
  refine Subtype.ext (funext fun d => ?_)
  obtain ⟨p, rfl⟩ := toRow_surjective sel mu d
  exact congrFun h (trivPt X _ _ _ _ p)

theorem rowEmb_linearIndependent (H : ∀ b, Subgroup ((stepX Ch sel mu P).G b)) {J : Type} {φ : J → MtildeV W Ch sel mu P}
    (h : LinearIndependent X.K φ) :
    LinearIndependent ℂ fun a => rowEmb W Ch sel mu P b0 til ext tz H hd σ (φ a) :=
  LinearIndependent.of_comp (valMt W Ch sel mu P b0 til ext tz σ H)
    ((toMtilde_linearIndependent W Ch sel mu P σ h).map' (valMtP W Ch sel mu P σ)
      (LinearMap.ker_eq_bot.2 (valMtP_injective W Ch sel mu P σ)))

theorem rowEmb_span (hX : X.Ok) {J : Type} {φ : J → MtildeV W Ch sel mu P} (h : Submodule.span X.K (Set.range φ) = ⊤) :
    Submodule.span ℂ (Set.range fun a => rowEmb W Ch sel mu P b0 til ext tz (fun _ => ⊤) hd σ (φ a)) = ⊤ :=
  GlobalTheory.PerQ.RowIntModel.eq_top_of_rowEmb_mem W Ch sel mu P b0 til ext tz hd σ hX _ fun z _ =>
    map_mem_span_range (rowEmb W Ch sel mu P b0 til ext tz (fun _ => ⊤) hd σ) h z

end G

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

end GlobalTheory.Core.Rk.RowRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledThetaVectorFixedUnramifiedStabilizer
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP.VacFix

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ), IsThetaFunO ψ A B Φ₁ → IsThetaFunO ψ A B Φ₂ → Unram ψ A B χB LA LB Sf Φ₁ Φ₂ → ∀ v ∉ Sf, ∀ k ∈ KFin D.sp.cm.sig (dblSp A).gram LA v, omh (emb D.sp.cm.sig (dblSp A).gram v k, 1) (delta A B Φ₁ Φ₂) = delta A B Φ₁ Φ₂ := by
  intro D ψ A B χB omh hW LA LB Sf Φ₁ Φ₂ h1 h2 hU v hv k hk
  have hstd := hW.std
  obtain ⟨hsd, hvac⟩ := _root_.GlobalTheory.Core.Rk.VacBox.doubling_isLatVac D ψ A B LA LB hstd hU.sdA
  have hth := _root_.GlobalTheory.Core.Rk.DeltaTheta.main D ψ A B hstd Φ₁ Φ₂ h1 h2
  have hlv := hvac Sf Φ₁ Φ₂ hU.sph₁ hU.sph₂ v hv
  have u1 : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.UnramAt (1 : (AE D)ˣ →* Circle) v := fun _ _ _ _ => rfl
  have u2 : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.UnramAt χB v := by
    obtain ⟨χ, hc⟩ := _root_.GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D χB hW.hecT
    refine GlobalTheory.UnramOver.unramAt_of_unrAt D χB χ hc v _ ?_ ?_
    · refine ⟨singleV _ v 1, rfl, ?_, ?_⟩
      · classical
        exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) v 1
      · intro v' hv'
        classical
        exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) 1 hv'
    · intro P hP
      exact (GlobalTheory.LFun.unrAt_iff_of_chrEq hc P).1 (hU.unr P (by
        simp only [GlobalTheory.LFun.above, Set.mem_setOf_eq, hP]
        exact_mod_cast hv))
  have key : ∀ C, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.VacuumFixedOn D C → C v →
      omh (emb D.sp.cm.sig (dblSp A).gram v k, 1) (delta A B Φ₁ Φ₂) = delta A B Φ₁ Φ₂ := by
    intro C hC hCv
    have := hC ψ (dblSp A) B 1 χB omh (sumLat finSumFinEquiv LA LA) LB hW hsd hU.sdB v hCv u1 u2 _ hth hlv k hk 1
      (one_mem _)
    rwa [map_one] at this
  by_cases hs : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsSplitPlace D v
  · exact key _ (GlobalTheory.PlaceTensor.splitVacuumFixed D) hs
  · exact key _ (GlobalTheory.PlaceTensor.inertVacuumFixed D) hs

end GlobalTheory.Core.Rk.IP.VacFix
end

