module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0046
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0865
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsLatticeVacuumIffSignedRationalFixed
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0515
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0508
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0499

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedClassEqPartAddTwoMovedShiftedPoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.LiftLevel.MovedClass

open GlobalTheory.LiftLevel

variable {D : D7}

theorem partAt_eq_smul {S T : HSp D} (c : AE D) (w : WO S T) : partAt c w = c • w := by
  ext i j; rfl

theorem actO_smul' (S T : HSp D) (g : GA D S) (h : GA D T) (c : AE D) (x : WO S T) :
    actO S T g h (c • x) = c • actO S T g h x := by
  simp only [actO, Matrix.mul_smul, Matrix.smul_mul]

theorem actO_actO_inv (S T : HSp D) (g : GA D S) (x : WO S T) : actO S T g 1 (actO S T g⁻¹ 1 x) = x := by
  simpa using GlobalTheory.WeilVacMove.actO_inv_actO (S := S) (T := T) g⁻¹ 1 x

theorem finW_two (S T : HSp D) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    finW S T (2 • y) = 2 • finW S T y := by
  ext a k
  simp only [finW, two_nsmul, Matrix.add_apply, Matrix.of_apply, TensorProduct.tmul_add]

theorem tens_mono {E : Type} [Field E] [NumberField E] {n r : ℕ} (Λ : Lt E n) {L L' : Lt E r} (h : L ≤ L') :
    tens Λ L ≤ tens Λ L' :=
  AddSubgroup.closure_mono fun _ ⟨v, hv, u, hu, e⟩ => ⟨v, hv, u, h hu, e⟩

theorem tens_two {E : Type} [Field E] [NumberField E] {n r : ℕ} (Λ : Lt E n) (N : Lt E r)
    {y : Matrix (Fin n) (Fin r) E} (hy : y ∈ tens Λ (Ideal.span {(2 : 𝓞 E)} • N)) :
    ∃ y' ∈ tens Λ N, y = 2 • y' := by
  have key : tens Λ (Ideal.span {(2 : 𝓞 E)} • N) ≤
      (tens Λ N).map (DistribSMul.toAddMonoidHom (Matrix (Fin n) (Fin r) E) (2 : ℕ)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨v, hv, u, hu, rfl⟩
    rw [Submodule.ideal_span_singleton_smul] at hu
    obtain ⟨u', hu', rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hu
    refine ⟨vecMulVec v u', AddSubgroup.subset_closure ⟨v, hv, u', hu', rfl⟩, ?_⟩
    ext i j
    simp [vecMulVec_apply, two_smul, two_nsmul, mul_add]
  obtain ⟨y', hy', e⟩ := key hy
  exact ⟨y', hy', e.symm⟩

theorem mem_sh {S T : HSp D} (C : Ctx S T) (Lv : GlobalTheory.SW.Level C.X) :
    Lv.𝔪 • (conjI Lv.𝔪 • C.X.Λ) ≤ Lv.sh C.X.Λ := by
  intro v hv b hb
  exact Submodule.smul_mono le_rfl Submodule.smul_le_right (Submodule.smul_mem _ b hv)

theorem moved_class : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ y ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ), ∃ v ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), actO S T k₀ 1 (finW S T y) = GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y)) + 2 • v ∧ C.ψ (symplOH S T (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))) (2 • v)) = 1 := by
  intro D S T C hn ΛT hT hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' hab hmov hgen hΛ' Lv hLv y hy
  rw [Submodule.mul_smul] at hy
  obtain ⟨y', hy', rfl⟩ := tens_two _ _ hy
  have hS := C.m.gS
  set std := stdL D.host.E S.rank with hstd
  set x := finW S T y' with hx
  set X := actO S T k₀ 1 x with hX
  have hX2 : actO S T k₀ 1 (finW S T (2 • y')) = 2 • X := by
    rw [finW_two, GlobalTheory.WeilVacMove.actO_two_nsmul]
  rw [hX2]

  have hxM : x ∈ hatA S T (tens std (conjI Lv.𝔪 • C.X.Λ)) := by
    rw [hx, GlobalTheory.Ker.SignVac.finW_eq]; exact GlobalTheory.Ker.SignVac.finTens_mem (GlobalTheory.TensLatMove.intAf_one (D := D)) hy'
  have hE : partAt e x ∈ hatA S T (tens std (Lv.sh C.X.Λ)) := _root_.GlobalTheory.LiftLevel.partAt_finW_mem_hatA_sh D S T C Pg Q e he Lv hLv y' hy'
  have hF : partAt (1 - e - cA D e) x ∈ hatA S T (tens std (Lv.sh C.X.Λ)) := by
    refine _root_.GlobalTheory.OffIdemLat.partAt_off_mem D S T e (Pg ∪ Q) he _ _ ?_ x hxM
    have : (∏ PP ∈ Pg ∪ Q, conjI PP.asIdeal) = Lv.𝔪 := by rw [hLv]; rfl
    rw [this]; exact mem_sh C Lv
  have hB : (1 - cA D e) • x ∈ hatA S T (tens std (Lv.sh C.X.Λ)) := by
    have : (1 - cA D e) • x = partAt e x + partAt (1 - e - cA D e) x := by
      rw [partAt_eq_smul, partAt_eq_smul, ← add_smul]; congr 1; ring
    rw [this]; exact add_mem hE hF
  have hmov1 : IsMov (fmt T 1) (Lv.sh C.X.Λ) (Lv.sh C.X.Λ) := by
    have hmt1 : Formalism.L2.Theta.mt T 1 = 1 := by simp [Formalism.L2.Theta.mt]
    have hfmt1 : fmt T 1 = 1 := by simp [fmt, hmt1]
    rw [hfmt1]
    intro u
    exact ⟨fun h => ⟨u, h, (Matrix.one_mulVec u).symm⟩, fun ⟨u₀, h, e⟩ => by rw [e, Matrix.one_mulVec]; exact h⟩
  obtain ⟨u₀, hu₀, hu₀e⟩ := (GlobalTheory.TensLatMove.mem_hatA_iff S T hS k₀⁻¹ 1 Λ' std (Lv.sh C.X.Λ) (Lv.sh C.X.Λ)
    hΛ' hmov1 _).1 hB
  have hv : partAt (1 - cA D e) X = u₀ := by
    rw [partAt_eq_smul, hX, ← actO_smul', hu₀e, actO_actO_inv]
  refine ⟨partAt (1 - cA D e) X, hv ▸ hu₀, ?_, ?_⟩
  · rw [partAt_eq_smul, partAt_eq_smul, smul_comm (cA D e) (2 : ℕ) X, ← smul_add, ← add_smul]
    congr 1
    rw [add_sub_cancel, one_smul]
  · have hce : cA D e * cA D e = cA D e := by rw [← map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he]
    have hint1 : finPart D (cA D e) ∈ intAE D :=
      GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hce])
    have hce' : (1 - cA D e) * (1 - cA D e) = 1 - cA D e := by linear_combination hce
    have hint2 : finPart D (1 - cA D e) ∈ intAE D :=
      GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hce'])
    have hstar : ∀ v : Fin S.rank → D.host.E, v ∈ std ↔ star v ∈ std := by
      have : ∀ v : Fin S.rank → D.host.E, v ∈ std → star v ∈ std := fun v hv =>
        (GlobalTheory.SW.Base.mem_stdL _).2 fun a => GlobalTheory.SW.Base.isIntegral_cc ((GlobalTheory.SW.Base.mem_stdL _).1 hv a)
      exact fun v => ⟨this v, fun h => by simpa using this _ h⟩
    have hlat := GlobalTheory.Ker.LatTens.latO_eq_hatA D S T C std std ΛT C.X.Λ hstar hAA
    have hxΛ : x ∈ hatA S T (tens std C.X.Λ) := by
      rw [hx, GlobalTheory.Ker.SignVac.finW_eq]
      exact GlobalTheory.Ker.SignVac.finTens_mem (GlobalTheory.TensLatMove.intAf_one (D := D)) (tens_mono _ Submodule.smul_le_right hy')
    rw [← hlat] at hxΛ
    have hP := Formalism.IndefR.Fin.latO_smul_mem S T std ΛT hint1 hxΛ
    have hR := Formalism.IndefR.Fin.latO_smul_mem S T std ΛT hint2 hxΛ
    have hpair := GlobalTheory.LatVac.char_sympl_eq_one C.std (GlobalTheory.Ker.Base.selfDualC_stdL hS) hT hP hR
    have hpair' : C.ψ (symplO S T (cA D e • X) ((1 - cA D e) • X)) = 1 := by
      rw [hX, ← actO_smul', ← actO_smul', GlobalTheory.SymplOInv.symplO_actO]; exact hpair
    rw [partAt_eq_smul, partAt_eq_smul, smul_comm (cA D e) (2 : ℕ) X, two_nsmul, two_nsmul,
      GlobalTheory.SplitScalar.symplOH_add_left, GlobalTheory.SplitScalar.symplOH_add_self, GlobalTheory.LatVac.symplO_add_right,
      AddChar.map_add_eq_mul, hpair', one_mul]

end GlobalTheory.LiftLevel.MovedClass

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrbitAny
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.OrbitAny

open GlobalTheory.FinPl.SplitOrbit

theorem orbitAny : ∀ (D : D7) (V₀ A L : HSp D) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (L₀ : Lat V₀) (LA : Lat A) (LL : Lat L) (v : GlobalTheory.FinPl.Pl D), IsSelfDualC V₀ L₀ → IsSelfDualC A LA → IsSelfDualC L LL → OrthAt o L₀ LA LL v → ∀ γ ∈ grpAt V₀ (· = v), (∀ a : AE D, a • ratV (vecB o ζ) ∈ latA V₀ L₀ (· = v) → mt V₀ γ⁻¹ *ᵥ (a • ratV (vecB o ζ)) ∈ latA V₀ L₀ (· = v)) → ∃ a ∈ grpAt A (· = v), ∃ κ, InK V₀ L₀ (· = v) κ ∧ γ = o.emb (a, 1) * κ := by
  intro D V₀ A L o ζ hζ L₀ LA LL v hL₀ hLA hLL hO γ hγ hz
  have hT := GlobalTheory.FinPl.TamePlaces.tame D v
  have hM := isSDAt_pre_unitary (_root_.GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V₀ L₀ v hL₀) γ⁻¹
  obtain ⟨hA, hsplit⟩ := split_of_le o hM (_root_.GlobalTheory.IwaPlace.LocSD.isSDAt_latV D L LL v hLL) (line_le o hζ hO _ hz)
  obtain ⟨a, ha, hmv⟩ := _root_.GlobalTheory.IwaOrbit.selfDual_orbit D A v _ _ hT (_root_.GlobalTheory.IwaPlace.LocSD.isSDAt_latV D A LA v hLA) hA
  exact ⟨a, ha, (o.emb (a, 1))⁻¹ * γ, ⟨mul_mem (inv_mem (emb_mem_grpAt o ha)) hγ,
    moves_of_split o hO γ a hsplit hmv⟩, (mul_inv_cancel_left _ _).symm⟩

end GlobalTheory.AscFin.OrbitAny

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PositiveRealPartTraceCharacterMemNhds
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.PosNhdsChar

theorem posNhds : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (n ρ : ℕ) (L : Mx D ρ n) (x : Mx D n ρ), {z : Mx D n ρ | 0 < (star (psiE ψ (upSum (L ⬝ (z - x))))).re} ∈ nhds x := by
  intro D ψ hψ n ρ L x
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd (AF D.host.F) (AE D)
  have hlin : ∀ c : AE D, Continuous fun a : AE D => c * a := fun c =>
    IsModuleTopology.continuous_of_linearMap (LinearMap.mulLeft (AF D.host.F) c)
  have htr : Continuous fun a : AE D => Algebra.trace (AF D.host.F) (AE D) a :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  have hψc : Continuous ψ := hψ.1.1
  have hcont : Continuous fun z : Mx D n ρ => star (psiE ψ (upSum (L ⬝ (z - x)))) := by
    refine continuous_star.comp (hψc.comp (htr.comp ?_))
    unfold upSum
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    split_ifs
    · simp only [Matrix.mul_apply, Matrix.sub_apply]
      refine continuous_finsetSum _ fun k _ => ?_
      have hk : Continuous fun z : Mx D n ρ => z k j - x k j := by
        simp only [sub_eq_add_neg]
        exact (continuous_id.matrix_elem k j).add continuous_const
      exact (hlin (L i k)).comp hk
    · exact continuous_const
  refine IsOpen.mem_nhds (isOpen_lt continuous_const (Complex.continuous_re.comp hcont)) ?_
  show (0:ℝ) < (star (psiE ψ (upSum (L ⬝ (x - x))))).re
  simp [upSum, psiE]

end GlobalTheory.PosNhdsChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealDictionaryHypotheses
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

open scoped Classical

namespace GlobalTheory.ThetaInterchange

open Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {Wd : Spc F E d}

def Good (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (T : ℝ → Module.End ℂ ((Fin n × Fin d → AF F) → ℂ))
    (Φ : (Fin n × Fin d → AF F) → ℂ) : Prop :=
  Φ ∈ schA F (Fin n × Fin d) ∧ ∃ Φ' ∈ schA F (Fin n × Fin d), (∀ x, HasDerivAt (fun t => T t Φ x) (Φ' x) 0) ∧
    ∀ w, HasDerivAt (fun t => thetaSum F (M.co.rho ψ w (T t Φ))) (thetaSum F (M.co.rho ψ w Φ')) 0

theorem rho_add (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (w : Matrix (Fin n) (Fin d) (AE F E))
    (a b : (Fin n × Fin d → AF F) → ℂ) : M.co.rho ψ w (a + b) = M.co.rho ψ w a + M.co.rho ψ w b := by
  funext x
  simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, mul_add]

theorem rho_smul (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (w : Matrix (Fin n) (Fin d) (AE F E)) (c : ℂ)
    (a : (Fin n × Fin d → AF F) → ℂ) : M.co.rho ψ w (c • a) = c • M.co.rho ψ w a := by
  funext x
  simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]
  ring

theorem rho_zero (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (w : Matrix (Fin n) (Fin d) (AE F E)) :
    M.co.rho ψ w (0 : (Fin n × Fin d → AF F) → ℂ) = 0 := by
  funext x
  simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]

theorem theta_add (M : Model σ Y Wd) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : Matrix (Fin n) (Fin d) (AE F E))
    {a b : (Fin n × Fin d → AF F) → ℂ} (ha : a ∈ schA F (Fin n × Fin d)) (hb : b ∈ schA F (Fin n × Fin d)) :
    thetaSum F (M.co.rho ψ w (a + b)) = thetaSum F (M.co.rho ψ w a) + thetaSum F (M.co.rho ψ w b) := by
  rw [rho_add]
  unfold GlobalTheory.WeilM.thetaSum
  exact (GlobalTheory.WeilM.summable_of_mem_schA F (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ w _ ha)).tsum_add
    (GlobalTheory.WeilM.summable_of_mem_schA F (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ w _ hb))

theorem theta_smul (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (w : Matrix (Fin n) (Fin d) (AE F E)) (c : ℂ)
    (a : (Fin n × Fin d → AF F) → ℂ) : thetaSum F (M.co.rho ψ w (c • a)) = c * thetaSum F (M.co.rho ψ w a) := by
  rw [rho_smul]
  unfold GlobalTheory.WeilM.thetaSum
  simp only [Pi.smul_apply, smul_eq_mul, tsum_mul_left]

theorem good_zero (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (T : ℝ → Module.End ℂ ((Fin n × Fin d → AF F) → ℂ)) :
    Good M ψ T 0 := by
  refine ⟨Submodule.zero_mem _, 0, Submodule.zero_mem _, fun x => ?_, fun w => ?_⟩
  · simp only [map_zero, Pi.zero_apply]
    exact hasDerivAt_const _ _
  · simp only [map_zero, rho_zero, GlobalTheory.WeilM.thetaSum, Pi.zero_apply, tsum_zero]
    exact hasDerivAt_const (0 : ℝ) (0 : ℂ)

theorem good_add (M : Model σ Y Wd) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {T : ℝ → Module.End ℂ ((Fin n × Fin d → AF F) → ℂ)} (hT : ∀ t, ∀ Φ ∈ schA F (Fin n × Fin d), T t Φ ∈ schA F _)
    {a b : (Fin n × Fin d → AF F) → ℂ} (ha : Good M ψ T a) (hb : Good M ψ T b) : Good M ψ T (a + b) := by
  obtain ⟨ha, a', ha', hpa, hta⟩ := ha
  obtain ⟨hb, b', hb', hpb, htb⟩ := hb
  refine ⟨Submodule.add_mem _ ha hb, a' + b', Submodule.add_mem _ ha' hb', fun x => ?_, fun w => ?_⟩
  · simp only [map_add (f := _), Pi.add_apply]
    exact (hpa x).add (hpb x)
  · have e : (fun t => thetaSum F (M.co.rho ψ w (T t (a + b)))) =
        fun t => thetaSum F (M.co.rho ψ w (T t a)) + thetaSum F (M.co.rho ψ w (T t b)) := by
      funext t
      rw [map_add (f := _), theta_add M hψ w (hT t a ha) (hT t b hb)]
    rw [e, theta_add M hψ w ha' hb']
    exact (hta w).add (htb w)

theorem good_smul (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (T : ℝ → Module.End ℂ ((Fin n × Fin d → AF F) → ℂ)) (c : ℂ)
    {a : (Fin n × Fin d → AF F) → ℂ} (ha : Good M ψ T a) : Good M ψ T (c • a) := by
  obtain ⟨ha, a', ha', hpa, hta⟩ := ha
  refine ⟨Submodule.smul_mem _ c ha, c • a', Submodule.smul_mem _ c ha', fun x => ?_, fun w => ?_⟩
  · simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    exact (hpa x).const_mul c
  · simp only [map_smul, theta_smul]
    exact (hta w).const_mul c

theorem schA_le_of_pure {κ : Type} [Fintype κ] {N : Submodule ℂ ((κ → AF F) → ℂ)}
    (h : ∀ (f : SInf F κ) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) → pure f φ ∈ N) :
    schA F κ ≤ N := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, g, hg, rfl⟩
  replace hg := GlobalTheory.SBSpan.mem_span_restrictedProd F _ g hg
  induction hg using Submodule.span_induction with
  | zero => rw [show pureA F f 0 = 0 from funext fun _ => mul_zero _]; exact N.zero_mem
  | add a b _ _ ha hb =>
    rw [show pureA F f (a + b) = pureA F f a + pureA F f b from funext fun _ => mul_add _ _ _]; exact N.add_mem ha hb
  | smul c a _ ha =>
    rw [show pureA F f (c • a) = c • pureA F f a from funext fun _ => mul_left_comm _ _ _]; exact N.smul_mem c ha
  | mem p hp =>
    obtain ⟨φ, hφ, hs, rfl⟩ := hp
    exact h f φ hφ hs

end GlobalTheory.ThetaInterchange

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealIntertwinerDownArrowTransportAdjoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.AdjTr

variable {D : D7}

theorem isIntw_transport {V W : HSp D} {S S' : D.what₂.Tau → SPar} {X Y P P' : Type} [AddCommGroup P] [Module ℂ P]
    [AddCommGroup P'] [Module ℂ P'] (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (ω : GA D V × GA D W →* Module.End ℂ (X → ℂ)) (ω₀ : GA D V × GA D W →* Module.End ℂ (Y → ℂ))
    (pt : P → (X → ℂ)) (pt₀ : P' → (Y → ℂ)) (e : P ≃ₗ[ℂ] P') (b : Y → X) (It : P' →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M)
    (hpt : ∀ φ, pt₀ (e φ) = pt φ ∘ b) (hω : ∀ p F, ω₀ p (F ∘ b) = ω p F ∘ b) (h : IsIntw θ M M' ω₀ pt₀ It) :
    IsIntw θ M M' ω pt (It ∘ₗ e.toLinearMap) := by
  refine { ne := ?_, bdd := ?_, eqK := ?_, eqg := ?_, invK := ?_, invg := ?_ }
  · intro h0
    apply h.ne
    apply LinearMap.ext
    intro φ
    have hφ := congrArg (fun L => L (e.symm φ)) h0
    simpa using hφ
  · intro φ w
    exact h.bdd (e φ) w
  · intro τ g hg φ φ' hφ v
    exact h.eqK τ g hg (e φ) (e φ') (by rw [hpt, hpt, hφ, hω]) v
  · intro τ Y hY φ φ' hd v
    exact h.eqg τ Y hY (e φ) (e φ') (fun z => by
      simpa only [hpt, hω, Function.comp_apply] using hd (b z)) v
  · intro τ k hk φ φ' v v' hφ hv
    exact h.invK τ k hk (e φ) (e φ') v v' (by rw [hpt, hpt, hφ, hω]) hv
  · intro τ Y hY φ φ' v v' hd hv
    exact h.invg τ Y hY (e φ) (e φ') v v' (fun z => by
      simpa only [hpt, hω, Function.comp_apply] using hd (b z)) hv


open GlobalTheory.FockAdjoint in
theorem ptOf_dag {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {V W : HSp D} {SV SW : D.what₂.Tau → SPar} (M : DSModel V SV) (M' : DSModel W SW) {g : WO V W → ℂ}
    (hg : IsThetaFunO ψ V W g) (Q : PolF D W.rank V.rank) :
    ptOf ψ θ M' M (dag V W g) (jHom (Fr.ofModel M) (Fr.ofModel M') Q) = dag V W (ptOf ψ θ M M' g Q) := by
  set A := Fr.ofModel M
  set B := Fr.ofModel M'
  have L := GlobalTheory.AdjLawPf.adjLaw D ψ hψ V W
  have cA := GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A
  have cB := GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B
  have hd := L.theta g hg
  show ptF ψ θ B A (dag V W g) (jHom A B Q) = dag V W (ptF ψ θ A B g Q)
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [jHom_C, ← mul_one (MvPolynomial.C _), ptF_C, ptF_one, ← mul_one (MvPolynomial.C a), ptF_C, ptF_one,
      dag_smul']
  | add p q hp hq => rw [map_add (f := _), ptF_add, ptF_add, hp, hq, dag_add]
  | mul_X p v hp =>
    obtain ⟨τ, i, j⟩ := v
    rw [map_mul, jHom_X, mul_comm (jHom A B p), mul_assoc, ptF_C, ptF_X_mul hψ hθ B A hd, hp, mul_comm p,
      ptF_X_mul hψ hθ A B hg]
    dsimp only
    rw [aPlus_dag hψ hθ L τ (cA τ) (cB τ) _ (ptF_theta hψ hθ A B hg p), cdag_unitMap,
      aPlus_real_smul hψ hθ (ptF_theta hψ hθ A B hg p), dag_smul', Complex.conj_ofReal, smul_smul]
    rw [show ((sg (B.ε τ i) * sg (A.ε τ j) : ℝ) : ℂ) = sgv A B τ i j from rfl, sgv_mul_self, one_smul]

open GlobalTheory.FockAdjoint in
theorem jHom_map_conj {S T : HSp D} (A : Fr S) (B : Fr T) (P : PolF D T.rank S.rank) :
    jHom A B (MvPolynomial.map (starRingEnd ℂ) P) = swapHom A B P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [jHom_C, swapHom]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p v hp => rw [map_mul, map_mul, hp, MvPolynomial.map_X, jHom_X, map_mul, swapHom_X]

theorem dag_cj {S T : HSp D} (F : WO S T → ℂ) : dag S T (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id F) = F ∘ adjO S T := by
  funext y; simp [dag, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]

end GlobalTheory.AdjTr


open GlobalTheory.AdjTr in
theorem GlobalTheory.AdjTr.downArrow_transport : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χ : (AE D)ˣ →* Circle)
    (ω : GlobalTheory.Grid.WRep S.V T.V) (f : WO S.V T.V → ℂ), IsInfFam θ → GlobalTheory.Grid.IsWeil ψ true S.V T.V χ χ ω →
    GlobalTheory.Grid.IsVac ψ θ true S T f →
    ∃ (ω₀ : GlobalTheory.Grid.WRep T.V S.V) (f₀ : WO T.V S.V → ℂ) (χ₀ : (AE D)ˣ →* Circle)
      (e : GlobalTheory.Grid.Pol S T ≃ₗ[ℂ] PolF D S.V.rank T.V.rank),
      IsWeilDatumO ψ T.V S.V χ₀ χ₀ ω₀ ∧ (∀ τ a, HasInfExp D χ τ a → HasInfExp D χ₀ τ (-a)) ∧
      IsVacVec ψ θ T.M S.M f₀ ∧
      ∀ It : PolF D S.V.rank T.V.rank →ₗ[ℂ] SmT S.M →ₗ[ℂ] SmT T.M, IsItW θ T.M S.M ω₀ (ptOf ψ θ T.M S.M f₀) It →
        GlobalTheory.Grid.IsIntw θ T.M S.M ω.swap (GlobalTheory.Grid.fock ψ θ true S T f) (It ∘ₗ e.toLinearMap) := by
  intro D S T ψ θ χ ω f hθ hW hV
  set A := Fr.ofModel S.M
  set B := Fr.ofModel T.M
  have hstd : IsStdChar D ψ (-1) := hV.1
  have L := GlobalTheory.AdjLawPf.adjLaw D ψ hstd S.V T.V
  have hth : IsThetaFunO ψ (GlobalTheory.Grid.neg S.V) T.V f := hV.2.theta
  have hvv := _root_.GlobalTheory.VacCjNeg.isVacVec_cj_of_isVac_neg S T ψ θ f hV
  refine ⟨adjRep ω, dag S.V T.V (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f), χ⁻¹, (swapEquiv A B).toLinearEquiv, ?_,
    fun τ a h => GlobalTheory.Mem.HeckeExp.hasInfExp_inv h, ⟨L.theta _ hvv.theta, ?_, fun τ => GlobalTheory.FockAdjoint.vac_dag hstd hθ L τ
      (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A τ) (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B τ) hvv.theta (hvv.vac τ)⟩,
    fun It hIt => ?_⟩
  · exact GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ S.V T.V χ⁻¹ χ⁻¹ (conjRep ω) (GlobalTheory.T.isWeilDatum_complexConjugate_of_negHermitianSpace ψ S.V T.V χ χ ω hW)
  · intro h0
    apply hvv.ne
    funext x
    have := congrFun h0 (adjO T.V S.V x)
    simp only [dag, GlobalTheory.AdjLawPf.adj_invol, Pi.zero_apply, map_eq_zero] at this
    exact this
  · refine isIntw_transport θ T.M S.M ω.swap (adjRep ω) (GlobalTheory.Grid.fock ψ θ true S T f)
      (ptOf ψ θ T.M S.M (dag S.V T.V (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f))) (swapEquiv A B).toLinearEquiv (adjO S.V T.V) It
      (fun φ => ?_) (fun p F => ?_) ((GlobalTheory.Grid.isIntw_iff θ T.M S.M _ _ It).2 hIt)
    · show ptOf ψ θ T.M S.M (dag S.V T.V (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f)) (swapHom A B φ) = _
      rw [← jHom_map_conj, ptOf_dag hstd hθ S.M T.M hvv.theta, ← _root_.GlobalTheory.FockConjNeg.fock_neg_cj S T ψ θ f hstd hθ hth, dag_cj]
    · obtain ⟨h, g⟩ := p
      rw [adjRep_apply, WRep.swap_apply]
      funext y
      simp only [Function.comp_apply, GlobalTheory.AdjLawPf.adj_invol]

end
end

