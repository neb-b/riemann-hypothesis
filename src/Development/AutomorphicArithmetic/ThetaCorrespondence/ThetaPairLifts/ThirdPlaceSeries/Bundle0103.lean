module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderEqOrSmulUnderEq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0060
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0486
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0058
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0081
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0285
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0055
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0070
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0446
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0892
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1619
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0085
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0482
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0505
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnderMemSStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChain_stageY_is_of_pkHyp_of_lt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ j, j < D.R.m → (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).Is (_root_.GlobalTheory.BaseChain.com_z W) j := by
  first | exact @_root_.GlobalTheory.BaseChain.stage_y_is | exact _root_.GlobalTheory.BaseChain.stage_y_is | (intros; apply _root_.GlobalTheory.BaseChain.stage_y_is <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnifOfRead
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel
noncomputable section
namespace GlobalTheory.LevelUnif
open GlobalTheory.LocMod.PinEx GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum GlobalTheory.SplitWeil GlobalTheory.SymChain
open GlobalTheory.FinPl (SplitPt)
open Formalism.L2.NTheta (IsIdemAt)
section Elem
variable {κ : Type} [CommRing κ] {r : ℕ}
end Elem
section Local
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)
  {PP : Pl D.host.E} (h : IsIdemAt q.e PP) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
end Local
section Levels
variable {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ}
end Levels
section Gen
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word}
theorem valuation_uniformizer_sub_q_lt (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) {v : VCom f.c} {N : ℕ} (G : Fin N → GLoc v) (pl : Fin N ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg) (hR : _root_.GlobalTheory.Fam.LocalGroupReading f G pl)
    (hP : GlobalTheory.Core.Mi.IsTypePlaces (_root_.GlobalTheory.Fam.pk_z W).Pg) (n : Fin N) :
    valuation (G n).k ((((G n).S.ϖ : (G n).kˣ) : (G n).k) - ((Formalism.L2.Col.qOf (pl n).1 : ℕ) : (G n).k)) <
      valuation (G n).k (((G n).S.ϖ : (G n).kˣ) : (G n).k) := by
  have hid : ∀ i, IsIdemAt (G i).q.e (pl i).1 := fun i => (hR.idem i).1
  have hq : ∀ i, ∃ t : (G i).kˣ, IsUnif t ∧ (t : (G i).k) = ((Formalism.L2.Col.qOf (pl i).1 : ℕ) : (G i).k) := fun i => by
    obtain ⟨-, hi, hd⟩ := place_facts (G i).q (hid i)
    obtain ⟨t, h1, h2⟩ := GlobalTheory.WeilCondUnif.isUnif_of (pl i).1 ((G i).q.pr.comp (incA D)) hi hd (norm_notMem_sq (hP.1 _ (pl i).2))
    exact ⟨t, h1, h2.trans (map_natCast _ _)⟩
  choose t ht htq using hq
  choose α hα using fun i => exists_res (G i).q (hid i) (G i).S.cond (G i).S.unif
  choose β hβ using fun i => exists_res (G i).q (hid i) (G i).S.cond (ht i)
  obtain ⟨ψ₀, -, h0, π, hπ, hH, hχ⟩ := W.Q.charW.base.grp.levels
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hrS : D.R.rS = D.R.m / 2 - 1 := rfl
  have hA : ∀ c, ψ₀ (pl n).1 c = β n c := fun c => by
    let i : Fin D.R.r := ⟨0, by omega⟩
    let j : Fin D.R.r := ⟨1, by omega⟩
    have hij : i ≠ j := fun e => zero_ne_one (congrArg Fin.val e)
    have hE : ∀ a : Fin D.R.r, ¬ supEdge a a := fun a h => by unfold supEdge at h; omega
    let x : G0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r := Pi.mulSingle (pl n) (elem hij c)
    have hx : x ∈ (P0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r ψ₀).H :=
      single_mem _ _ (unipCol_le _ 0 0 (elem_mem_unipCol hij zero_lt_one c 0 0 one_ne_zero))
    obtain ⟨hx', e1⟩ := chi_of_eq h0 x hx
    have e2 : (((P0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r ψ₀).chi ⟨x, hx⟩ : ℂˣ) : ℂ) = ∏ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, ψ₀ PP.1 (edgeSum supEdge (x PP)) := by
      unfold P0 LevelP.ofLocal
      rw [MonoidHom.finsetProd_apply, Units.coe_prod]
      rfl
    have e3 := W.Q.signs (fun PP => (G (pl.symm PP)).q.e) (fun PP => by
      have := hid (pl.symm PP)
      rwa [pl.apply_symm_apply] at this) ⟨(_root_.GlobalTheory.Fam.pk_z W).eG.symm x, hx'⟩
    have e4 : (((P0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r ψ₀).chi ⟨x, hx⟩ : ℂˣ) : ℂ) = _ := (congrArg Units.val e1).symm.trans e3
    rw [e2, ← pl.prod_comp, ← pl.prod_comp, prod_single pl (fun m => ψ₀ (pl m).1) supEdge hE hij rfl] at e4
    rw [e4, ← prod_single pl β supEdge hE hij rfl n c]
    refine Finset.prod_congr rfl fun m _ => ?_
    rw [pl.symm_apply_apply, psiAt_eq (G m).q (G m).char]
    change _ = β m (edgeSum supEdge (x (pl m)))
    rw [edgeSum_eq_supSum, ← Function.surjInv_eq Ideal.Quotient.mk_surjective (Formalism.IndefR.Mi.supSum (x (pl m)).val), ← hβ,
      Units.val_inv_eq_inv_val, htq, MulEquiv.apply_symm_apply]
    refine congrArg (fun y => ((G m).S.ψ y : ℂ)) ?_
    change ((G m).q.pr.comp (incA D)) _ = _
    rw [map_mul, map_inv₀, map_natCast]
    rfl
  have hC : ∀ c, ψ₀ (pl n).1 c = α n c := fun c => by
    let i : Fin D.R.r := ⟨D.R.rS, by omega⟩
    let j : Fin D.R.r := ⟨D.R.rS + 1, by omega⟩
    have hij : i ≠ j := fun e => by have := congrArg Fin.val e; simp [i, j] at this
    have hE : ∀ a : Fin D.R.r, ¬ symEdge D.R.rS D.R.k a a := fun a h => by unfold symEdge at h; omega
    have hEij : symEdge D.R.rS D.R.k i j := Or.inl ⟨rfl, by show D.R.rS + 1 ≠ _; omega, by show D.R.rS + 1 ≠ _; omega⟩
    let y : G0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r := Pi.mulSingle (pl n) (elem hij c)
    have hy : y ∈ (PsharpSym (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r D.R.rS D.R.k ψ₀).H :=
      single_mem _ _ (elem_mem_unipCol hij (Nat.lt_succ_self _) c _ _ (by show D.R.rS + 1 ≠ _; omega))
    let g : G0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r := reord π.symm y
    have hgy : ∀ PP a b, (y PP).val a b = (g PP).val (π a) (π b) := fun PP a b => by
      change _ = (y PP).val (π.symm (π a)) (π.symm (π b))
      rw [π.symm_apply_apply, π.symm_apply_apply]
    have hre : reord π g = y := funext fun PP => Units.ext (Matrix.ext fun a b => (hgy PP a b).symm)
    have hg : g ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H := (hH g).2 (hre ▸ hy)
    choose x hx using (hR.lev g).1.1 hg
    have e1 := (hR.lev g).2 hg x hx
    have e2 : (_root_.GlobalTheory.Fam.complexLevelStructure W).chi ⟨g, hg⟩ = (PsharpSym (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r D.R.rS D.R.k ψ₀).chi ⟨y, hy⟩ :=
      (hχ g hg (hre ▸ hy)).trans (congrArg _ (Subtype.ext hre))
    have e3 : (((PsharpSym (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r D.R.rS D.R.k ψ₀).chi ⟨y, hy⟩ : ℂˣ) : ℂ) =
        ∏ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, ψ₀ PP.1 (edgeSum (symEdge D.R.rS D.R.k) (y PP)) := by
      unfold PsharpSym LevelP.ofLocal
      rw [MonoidHom.finsetProd_apply, Units.coe_prod]
      rfl
    rw [← e2, e1, ← pl.prod_comp, prod_single pl (fun m => ψ₀ (pl m).1) _ hE hij hEij, Units.coe_prod] at e3
    rw [← e3, ← prod_single pl α _ hE hij hEij n c]
    refine Finset.prod_congr rfl fun m _ => ?_
    have h1 := (G m).hs
    have h2 := (G m).S.odd
    have hρ : D.R.rS = (G m).S.ρ := by omega
    let e : Fin D.R.k ⊕ Fin ((G m).s + 1) ≃ Fin D.R.r := finSumFinEquiv.trans (finCongr (by omega))
    have he : ∀ a, (e a).val = framePos _ _ a := by rintro (a | a) <;> simp [e, framePos]
    have := sym_chr (G m).S (prO (G m).q) e he (hρ ▸ hπ) (g (pl m)) (y (pl m)) (hgy _) (α m) (hα m) (x m)
      fun a b => hx m a b _ _ (he a) (he b)
    rw [← hρ] at this
    exact this
  rw [← htq]
  exact near_of_res (G n).q (hid n) (G n).S.cond (G n).S.unif (ht n) fun z =>
    Circle.coe_injective ((hα n z).trans (((hC _).symm.trans (hA _)).trans (hβ n z).symm))
end Gen
theorem int_and_unif_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is → ∀ n : Fin a.n, (∀ x : (I.rec7 l Z).host.E, (ofSplit (a.G n).q).pr x ∈ 𝒪[(a.G n).k] ↔ Formalism.L2.Col.IntAt (a.pl n).1 x) ∧ valuation (a.G n).k ((((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) - ((Formalism.L2.Col.qOf (a.pl n).1 : ℕ) : (a.G n).k)) < valuation (a.G n).k (((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha _ _ n
  have hR := (ha.tie (fun t => (GlobalTheory.Fam.TopLocFac.nonempty_rowCh (D := I.rec7 l Z) _ _ u a.g W.Q.stdChar t).some)
    fun t => (GlobalTheory.Fam.TopLocFac.nonempty_colCh (D := I.rec7 l Z) u _).some).2
  have h2 := _root_.GlobalTheory.LevelUnif.valuation_uniformizer_sub_q_lt (D := I.rec7 l Z) _ _ _ hR hW.lev.1 n
  exact ⟨(place_facts (a.G n).q (hR.idem n).1).2.1, h2⟩
end GlobalTheory.LevelUnif
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnitVectorLineConjugateStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_vector_rows_conjugate_alt : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → ∀ (v₀ v : (W.Q.Rl.MY 0).Vec), ConjVec W.S.X W.Q.instEq W.Q.Rl.θ (W.Q.Rl.MY 0) v → (∀ τ, ‖(v₀ τ : (W.Q.Rl.MY 0).H τ)‖ = 1) → ∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, T ≠ 0 → ∀ φ : L2X W.S.X, (φ : W.S.X.B.I.GA → ℂ) =ᵐ[muX W.S.X] evS W.S.X W.Q.instEq (show GA D (D.sp.Y 0) from W.Q.tS) (T (PiTensorProduct.tprod ℂ v₀)) → star φ ∈ HHX W.S.X → ∃ l : ℂ, l ≠ 0 ∧ PiTensorProduct.tprod ℂ v₀ = l • PiTensorProduct.tprod ℂ v := by
  first | exact @_root_.GlobalTheory.MiTop.unit_vector_line_conjugate_alt | exact _root_.GlobalTheory.MiTop.unit_vector_line_conjugate_alt | (intros; apply _root_.GlobalTheory.MiTop.unit_vector_line_conjugate_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.VTDisjointVGs
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Col2.DisjProof
theorem vT_disjoint_vGs_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ u : B.Word, Disjoint ((B.primes X).vT u) (B.primes X).vGs := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  have hT0 : (B.primes X).piT u ≠ 0 := fun h => by
    have := hPr.piT_norm u
    rw [h, zero_mul] at this
    exact (hPr.T_prime u).ne_zero (Nat.cast_eq_zero.1 this.symm)
  exact Finset.disjoint_left.2 fun P h1 h2 =>
    Formalism.L2.Col.piT_notMem_vGs hPr u ⟨P, h2⟩ ((Formalism.L2.Col.mem_divs hT0 P).1 h1)
end GlobalTheory.Mem.Col2.DisjProof
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZ
section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
namespace GlobalTheory.CovTop.WtShape
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem wtN_z : _root_.GlobalTheory.CovTop.LiftWeightNumerator := by
  refine ⟨1, one_pos, fun eps he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    ⟨0, le_rfl, max 8 ((3 : ℝ) ^ (4 / eps)), fun x hx hle ι p _ i => ?_⟩⟩⟩
  refine wtNum_at p i (Fm.params x hx ι) (Fm.parT x hx ι) (Fm.sizes x hx ι) ?_ ?_
  · rw [Fm.L_x x ι hx]; exact (le_max_left _ _).trans hle
  · rw [Fm.L_x x ι hx, Fm.L_eps x ι]
    have h3 : ((3 : ℝ) ^ (4 / eps)) ^ (eps / 4) = 3 := by
      rw [← Real.rpow_mul (by norm_num)]
      have : 4 / eps * (eps / 4) = 1 := by field_simp
      rw [this, Real.rpow_one]
    calc (3 : ℝ) = ((3 : ℝ) ^ (4 / eps)) ^ (eps / 4) := h3.symm
      _ ≤ x ^ (eps / 4) := Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hle) (by positivity)
end GlobalTheory.CovTop.WtShape
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.XiEqXiOffMulJoin
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem xi_eq_xiOff_mul_join_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ j (hj : j + 1 ≤ B.R.m) α γ z, J.A.xi j hj (J.ι j α) (J.ι (j + 1) γ) z = xiOff J.A j hj (J.ι j α) (J.ι (j + 1) γ) z * ∏ i, B.embLL (locXi J.A j (J.ι j α) (J.ι (j + 1) γ) (J.P i) (homOf I l Z j hj z)) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ _ t J hJ j hj α γ z
  rw [(_root_.GlobalTheory.QTw.Join.xi_factor_and_entry I hW.tr.ok hW.tr.tw l Z u (W.P.I.tup t) J.Ch₀ J.A hJ.is).1 j hj (J.ι j α) (J.ι (j + 1) γ) z]
  congr 1
  symm
  refine Finset.prod_bij (fun i _ => J.P i) ?_ ?_ ?_ ?_
  · intro i _
    rw [Finset.mem_filter, hJ.eq i]
    refine ⟨Finset.mem_univ _, fun h => ?_⟩
    exact Finset.disjoint_left.1 ((_root_.GlobalTheory.PkPlaces.pk_places_alt W hW.pk).2 t).1 ((hW.lev.2.1 _).2 h) (J.mem i)
  · intro i₁ _ i₂ _ h
    exact hJ.inj (((hJ.eq i₁).symm.trans (congrArg Subtype.val h)).trans (hJ.eq i₂))
  · intro P hP
    have hv : P.1 ∉ (B.primes X).vGs := (Finset.mem_filter.1 hP).2
    have hq : P.1 ∈ Formalism.L2.Col.QE I.sel (I.tup (W.P.I.tup t) : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K) := by
      rcases Finset.mem_union.1 P.2 with h | h
      · exact absurd h hv
      · exact h
    obtain ⟨i, hi⟩ := hJ.surj _ ((hW.tq.Q t P.1).2 hq)
    exact ⟨i, Finset.mem_univ _, Subtype.ext ((hJ.eq i).trans hi)⟩
  · intro i _
    rfl
end GlobalTheory.Fam
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ZeroForms
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem zero_forms_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col t (Ch₀ : ℕ → Type) (A : TwDat I l Z u (W.P.I.tup t) Ch₀) ι w c₀, PinChL (_root_.GlobalTheory.Fam.pk_z W) a.g (col t) c₀ A ι w → (∀ β, A.kb 0 β = TC.kStd X u (B.R.N 0)) → ∀ α, (∀ φ, _root_.GlobalTheory.MiTop.col0_alt (a.fam row col) t φ ∈ ((a.fam row col).t t).Ram 0 ∧ ∀ y, ((a.fam row col).t t).rd 0 α (_root_.GlobalTheory.MiTop.col0_alt (a.fam row col) t φ) y = (GlobalTheory.Core.Mi.chart0 (_root_.GlobalTheory.MiTop.formsAtZero W u)).rd W.Q.Rl.θ ((I.rec7 l Z).eMu u φ).1 y) ∧ ∀ ψ ∈ ((a.fam row col).t t).Ram 0, ∃ φ, ψ = _root_.GlobalTheory.MiTop.col0_alt (a.fam row col) t φ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha1 ha2 row col t Ch₀ A ι w c₀ hP hkb α
  have hr := hP.ram 0 (Nat.zero_le _)
  have hq := hP.rdq 0 (Nat.zero_le _)
  have hl := hP.live
  have hok : I.Ok := hW.tr.ok
  obtain ⟨hpins⟩ := hW.tr.pins
  obtain ⟨hstd⟩ := hW.tr.std
  obtain ⟨l0, -⟩ := hW.tw
  have hθ : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := ha2.pinX.inf
  refine ⟨fun φ => ⟨?_, fun y => ?_⟩, fun ψ hψ => ?_⟩
  · show _ ∈ (col t).Ram 0
    exact (hr _).2 ⟨(GlobalTheory.T.stepZero_ramifiedForms_transport_iff I hok l Z l0 u (W.P.I.tup t) _).1 ((I.rec7 l Z).eMu u φ).2, fun c hc => absurd (hl.first _) hc⟩
  · show (col t).rd 0 α _ y = _
    refine (hq α _ y).trans ?_
    exact _root_.GlobalTheory.Fam.rd_zero_std I hok hpins l Z _ hstd u (W.P.I.tup t) Ch₀ A hP.is (ι 0 α) (hkb _) _ hθ _ ((I.rec7 l Z).eMu u φ).2 y
  · have h1 : GlobalTheory.AdForm.RamT 0 ψ := ((hr ψ).1 hψ).1
    have h2 : ((I.rec7 l Z).e0Tw u (W.P.I.tup t)).symm ψ ∈ ((I.rec7 l Z).mem u).A.Mram :=
      (GlobalTheory.T.stepZero_ramifiedForms_transport_iff I hok l Z l0 u (W.P.I.tup t) _).2 (by rwa [LinearEquiv.apply_symm_apply])
    obtain ⟨φ, hφ⟩ := EquivLike.surjective ((I.rec7 l Z).eMu u) ⟨_, h2⟩
    refine ⟨φ, ?_⟩
    show ψ = (I.rec7 l Z).e0Tw u (W.P.I.tup t) (((I.rec7 l Z).eMu u) φ).1
    rw [hφ]
    exact (LinearEquiv.apply_symm_apply _ ψ).symm
end GlobalTheory.Fam
end
end

