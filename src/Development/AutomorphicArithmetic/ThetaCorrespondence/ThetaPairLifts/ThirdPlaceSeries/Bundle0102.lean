module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0074
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0460
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0081
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0058
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0055
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0082
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1858
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1821
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0086
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1896
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1779
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjIdealEqCP
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0500
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0489

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieRatOfStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tieRat_of_twAdm_and_at : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.ConditionAtPlace → _root_.GlobalTheory.BigOn.Exp.CompatibilityRational := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.tieRat_of_alt | exact _root_.GlobalTheory.BigOn.Exp.tieRat_of_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.tieRat_of_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TraceAtGOfMem
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FamTrace.TraceFwd
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colPos)
open GlobalTheory.SymBridge GlobalTheory.RootEx
section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Loc
set_option maxHeartbeats 1000000 in
theorem traceAtG_of_mem_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U → _root_.GlobalTheory.FamTrace.TraceAtElement a κ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha _ row col _ κ _ y hκy hy i g hg
  obtain ⟨hS⟩ := hA.tr.std
  obtain ⟨hP⟩ := hA.tr.pins
  obtain ⟨k₀, hR⟩ := (hS u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  obtain ⟨A, hU, hA'⟩ := exists_red I hA.tr.ok ((TC.spaces_in_coordinates I hA.tr.ok hP l Z).2.2.2 0 (Nat.zero_le _)).1
    ((W.R.T.cols.forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev hR ⟨_, hy⟩ (a.pl i).1 ((hA.lev.2.1 _).1 (a.pl i).2)
  letI := (a.G i).fld; letI := (a.G i).val; letI := (a.G i).top; letI := (a.G i).loc
  exact embX_mem (a.G i).S g (colGroup_of_red (a.G i).q ((ha.tie row col).2.idem i).1 ((I.rec7 l Z).sp.X 0)
    (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) (show B.R.N 0 = B.R.k by simp [Ranks.N]) _
    ((ha.stdG i).1 0 (Nat.zero_le _)) hκy hA' hU g hg)
end GlobalTheory.FamTrace.TraceFwd
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TraceChiColFactor
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000
noncomputable section
namespace GlobalTheory.FamTraceChiCol
set_option maxHeartbeats 8000000 in
theorem trace_chi_col_factor_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {hT : GatTies (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Gi : Formalism.MainNotions.G.Inst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L} {Gl : Formalism.MainNotions.G.LatInst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {cX : ExtraC} {ex : Extra (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (y : (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U), (((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.chi y : ℂˣ) : ℂ) * ∏ i : Fin a.n, GlobalTheory.FamTraceChiCol.colLam (_root_.GlobalTheory.MiTop.formsAtZero W u) ((a.pl i).1.under (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F)) y.1 = 1 := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a y
  have hTP : GlobalTheory.Core.Mi.IsTypePlaces (_root_.GlobalTheory.Fam.pk_z W).Pg := hA.lev.1
  set w : Fin a.n → IsDedekindDomain.HeightOneSpectrum (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) := fun i => (a.pl i).1.under (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) with hw
  have hw_mem : ∀ i, (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g 0 * (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g 1 : ℕ) : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∈ (w i).asIdeal := by
    intro i
    have h1 := hTP.1 (a.pl i).1 (a.pl i).2
    show _ ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, map_natCast]
    exact h1
  have hw_inj : Function.Injective w := by
    intro i i' hii
    obtain ⟨PP, _, hu⟩ := hTP.2 (w i) (hw_mem i)
    have e1 := hu (a.pl i).1 ⟨(a.pl i).2, rfl⟩
    have e2 := hu (a.pl i').1 ⟨(a.pl i').2, hii.symm⟩
    exact a.pl.injective (Subtype.ext (e1.trans e2.symm))
  set S : Fin 2 → Set (IsDedekindDomain.HeightOneSpectrum (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F)) :=
    fun j => {v | ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g j : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∈ v.asIdeal} with hS
  have hrange : S 0 ∪ S 1 = Set.range w := by
    ext v
    simp only [Set.mem_union, hS, Set.mem_setOf_eq, Set.mem_range]
    constructor
    · intro hv
      have hv' : (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g 0 * (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g 1 : ℕ) : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∈ v.asIdeal := (mem_type_prod_iff v).2 (Fin.exists_fin_two.2 hv)
      obtain ⟨PP, ⟨hPP, hPv⟩, _⟩ := hTP.2 v hv'
      exact ⟨a.pl.symm ⟨PP, hPP⟩, by simp [hw, hPv]⟩
    · rintro ⟨i, rfl⟩
      exact Fin.exists_fin_two.1 ((mem_type_prod_iff (w i)).1 (hw_mem i))
  have hfin : ∀ j, (S j).Finite := fun j =>
    (Set.finite_range w).subset (hrange ▸ (by
      rcases Fin.exists_fin_two.mp ⟨j, rfl⟩ with hj | hj <;> subst hj
      · exact Set.subset_union_left
      · exact Set.subset_union_right))
  have hdisj : Disjoint (S 0) (S 1) := by
    rw [Set.disjoint_left]
    intro v h0 h1
    exact absurd (type_idx_unique (D := _root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) h0 h1) (by decide)
  have hinner : ∀ j : Fin 2,
      (∏ᶠ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F)) (h : ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g j : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∈ v.asIdeal),
        (Formalism.L2.Forms.lamJ ((_root_.GlobalTheory.MiTop.formsAtZero W u).gl.psi0 j v h) ((_root_.GlobalTheory.MiTop.formsAtZero W u).gl.chiB j v h) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.k (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.t 0 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.k
          (Formalism.L2.Forms.redM (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F v ((_root_.GlobalTheory.MiTop.formsAtZero W u).gl.mat j v h ((_root_.GlobalTheory.MiTop.formsAtZero W u).glev0.fr j v h)
            (Formalism.UG.bc (Formalism.UG.prV (E := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) v) y.1))))⁻¹) =
      ∏ᶠ v ∈ S j, (colLam (_root_.GlobalTheory.MiTop.formsAtZero W u) v y.1)⁻¹ := by
    intro j
    refine finprod_congr fun v => finprod_congr fun h => ?_
    rw [colLam_eq (_root_.GlobalTheory.MiTop.formsAtZero W u) j h y.1]
  have hchi := (_root_.GlobalTheory.MiTop.formsAtZero W u).glev0.chi_eq y
  rw [Fin.prod_univ_two, hinner 0, hinner 1, ← finprod_mem_union hdisj (hfin 0) (hfin 1), hrange,
    finprod_mem_range hw_inj, finprod_eq_prod_of_fintype] at hchi
  rw [hchi, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => inv_mul_cancel₀ (colLam_ne_zero (_root_.GlobalTheory.MiTop.formsAtZero W u) _ _)
end GlobalTheory.FamTraceChiCol
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TraceOfAtAltAlt
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.SerBase
theorem traceOfAt_alt : _root_.GlobalTheory.BigOn.Exp.SerBase.TraceAt' := by
  refine _root_.GlobalTheory.BigOn.Exp.TwistConditions.of_forall fun Fm x hx i p hR hM w hw j => ?_
  intro ρ hρ hpin hlev h P
  have hL := _root_.GlobalTheory.BigOn.links2_of_rows_alt _ _ _ _ _ _ _ _ _ _ p hR hM.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hBo : BaseOf (R2 p) j (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) := by
    have h0 := baseOf_of_realPin_at (cG := p.cG) hC.lev hρ hpin ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
    exact { h0 with }
  have key := _root_.GlobalTheory.TraceLevelPf.traceLevel _ _ _ _ _ _ (R2 p) (F2 p) hC j _ (hρ.base _ j _) hBo (F2 p).P0 (F2 p).ψ0⁻¹
    ((p.R.eG.trans p.cG).trans (ρ.eG ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)))
    ?_ ?_ ?_ _ (hρ.weil_base _ j _) h P
  · exact key.symm
  · intro g Q hQ hQ' a c
    have e := hpin.grp ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) ((p.R.eG.trans p.cG) g) Q hQ hQ' a c
    rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at e
    exact e
  · intro g
    exact mem_level_iff hM.2.2 hlev _ j _ g
  · intro u hu
    refine (level_chi hM.2.2 hρ hlev _ j _ u hu).1.trans ?_
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀]
    rfl
end GlobalTheory.BigOn.Exp.SerBase
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TraceSt
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Datum
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open GlobalTheory.ConjTwist (BaseOf)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TraceFlatLevel
open GlobalTheory.TraceLevelPf
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end GlobalTheory.TraceFlatLevel
namespace GlobalTheory.BigOn.Exp.TupLe
theorem traceSt_alt : _root_.GlobalTheory.BigOn.Exp.TupLe.TraceCondition := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j hr hm ρ hρ hpin hlev i b ψ ω hψ hQ hω h P
  have hL := _root_.GlobalTheory.BigOn.links2_of_rows_alt _ _ _ _ _ _ _ _ _ _ p hr hm.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hBo : BaseOf (R2 p) j (ρ.B i j b) := { baseOf_of_realPin_at (cG := p.cG) hC.lev hρ hpin i j b with }
  refine GlobalTheory.TraceFlatLevel.traceLevel_flat (R2 p) j (ρ.B i j b) (hρ.base i j b) hBo (F2 p).P0 (F2 p).ψ0⁻¹
    ((p.R.eG.trans p.cG).trans (ρ.eG i j b)) (fun g P h h' a c => ?_) (fun g => mem_level_iff hm.2.2 hlev i j b g)
    (fun u hu => ?_) ψ hψ hQ ω hω h P
  · have e1 := hpin.grp i j b (p.cG (p.R.eG g)) P h h' a c
    rw [MulEquiv.symm_apply_apply] at e1
    exact e1
  · refine (level_chi hm.2.2 hρ hlev i j b u hu).1.trans ?_
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀]
    rfl
end GlobalTheory.BigOn.Exp.TupLe
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TruePack
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.MiS GlobalTheory.Mem GlobalTheory.Mem.Col2
namespace GlobalTheory.Fam
inductive TruePackAlt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}, _root_.GlobalTheory.MiS.RealPackAlt ex → Prop
  | mk {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
      {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
      {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) :
      _root_.GlobalTheory.Fam.AllFamilyConditions W → TruePackAlt W
def RealPackageCondition {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop :=
  (_root_.GlobalTheory.MiS.packageCoefficientSpace W).MIstar2 (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs) W.Q.sEE
end GlobalTheory.Fam
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwAdmStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_admissible' : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.twAdm_alt | exact _root_.GlobalTheory.BigOn.Exp.twAdm_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.twAdm_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwChrOfTwAdmStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_character_of_artin' : GlobalTheory.Published.GlobalArtinReciprocity → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter := by
  first | exact @_root_.GlobalTheory.TwistChr.twChr_of_twAdm_alt | exact _root_.GlobalTheory.TwistChr.twChr_of_twAdm_alt | (intros; apply _root_.GlobalTheory.TwistChr.twChr_of_twAdm_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwLevAtHolds
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
open GlobalTheory.BigOn.Exp.TwConj GlobalTheory.IdemSupport
open Formalism.L2.Host (HChar IsDelta IsPsi)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.TwConj.LevAt
section Places
variable {D : D7}
end Places
section Transfer
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end Transfer
section Chars
variable {D : D7}
variable {q l : ℕ} {δ ψ : HChar D.host.E} {Q : Finset (Pl D.host.E)}
end Chars
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {w : D.what₂.places.Pl}
end Point
end GlobalTheory.BigOn.Exp.TwConj.LevAt
namespace GlobalTheory.BigOn.Exp.TwConj
open LevAt in
theorem twLevAt_holds_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter →
    _root_.GlobalTheory.BigOn.Exp.TwConj.TwLevAtAlt := fun _ _ _ hA hC => by
  refine _root_.GlobalTheory.BigOn.Exp.TwistConditions.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hA (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hC _root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt)) fun Fm x hx i p hr hm w hw j H => ?_
  obtain ⟨⟨a1, -, -⟩, a2, a3⟩ := H
  intro ρ ρ' hρ hρ' hp hs hA
  have hl := ((Fm.D x i).ntw.lPrime ((Fm.ex x hx i).nch.twI w)).out
  have hlow : ∀ P ∈ (Fm.ex x hx i).nch.Q w,
      (((Fm.D x i).host.pde * (Fm.D x i).host.pde' : ℕ) : 𝓞 (Fm.D x i).host.E) ∉ P.asIdeal := fun P hP h => by
    refine Finset.disjoint_left.1 a1.2.1 hP (a3 P ?_)
    rw [mul_assoc _ (Fm.D x i).host.pde, ← mul_assoc, Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ h
  have pw : ∀ σ σ' : Setup (Fm.D x i).ntw, σ.Good → Adapted p w σ → σ'.rc = σ.rc →
      ∃ a : ℕ, (a + 1).Coprime ((Fm.D x i).ntw.l ((Fm.ex x hx i).nch.twI w)) ∧
        ChrEq (twW (Fm.ex x hx i) w σ').chi (p.Tp.psi w ^ (a + 1)) := fun σ σ' hσ hσA e => by
    obtain ⟨a, ha, h⟩ := exists_pow e ((Fm.ex x hx i).nch.sd w) a1
    rcases a with _ | a
    · exact absurd (Nat.coprime_zero_left _ |>.1 ha) hl.one_lt.ne'
    · exact ⟨a, ha, by rw [twW, h]; exact chrEq_pow (a2 σ hσ hσA).1 a⟩
  obtain ⟨⟨a, ha, hc⟩, a', ha', hc'⟩ : (∃ a : ℕ, (a + 1).Coprime ((Fm.D x i).ntw.l ((Fm.ex x hx i).nch.twI w)) ∧
        ChrEq (twW (Fm.ex x hx i) w ρ).chi (p.Tp.psi w ^ (a + 1))) ∧
      ∃ a : ℕ, (a + 1).Coprime ((Fm.D x i).ntw.l ((Fm.ex x hx i).nch.twI w)) ∧
        ChrEq (twW (Fm.ex x hx i) w ρ').chi (p.Tp.psi w ^ (a + 1)) :=
    hA.elim (fun h => ⟨pw ρ ρ hρ h rfl, pw ρ ρ' hρ h hs.1⟩) fun h => ⟨pw ρ' ρ hρ' h hs.1.symm, pw ρ' ρ' hρ' h rfl⟩
  obtain ⟨xiR, h1⟩ := twLev_pow hm.2.2 p.charW.base.fam p.qGuard hw j hlow hρ hp ha hc
  obtain ⟨xiR', h2⟩ := twLev_pow hm.2.2 p.charW.base.fam p.qGuard hw j hlow hρ hp ha' hc'
  have hQ : (twW (Fm.ex x hx i) w ρ').Q = half (ρ.ch ((Fm.ex x hx i).nch.twI w)) ((Fm.ex x hx i).nch.Q w) := by
    simp only [Setup.tw, twistOf, hs.2.1]
  obtain ⟨q, hq, hδ, -⟩ := exists_delta p.R.C ((Fm.ex x hx i).nch.twI w)
  obtain ⟨v, hv⟩ := exists_over (D := Fm.D x i) hq
  have hψ := p.Tp.psi_is w ((p.tw_iff w).1 hw)
  rw [← (Fm.ex x hx i).nch.twI_l] at hψ
  have hne : ∀ n : ℕ, p.R.C.delAt ((Fm.D x i).ntw.l ((Fm.ex x hx i).nch.twI w)) * p.Tp.psi w ^ n ≠ 1 := fun n e =>
    not_unr hδ hψ hl n hv (by rw [e]; exact fun _ _ => rfl)
  refine ⟨_, _, xiR, xiR', h1, hQ ▸ h2, hne _, hne _, or_iff_not_imp_left.2 fun e => ?_⟩
  rw [Ne, not_not] at e
  exact GlobalTheory.ChrEqUnique.idc_unique _ _ _ _ h1.xi (e ▸ h2.xi)
end GlobalTheory.BigOn.Exp.TwConj
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UlocLeLevelPrime
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
noncomputable section
namespace GlobalTheory.PenLevPrime
section Comp
set_option synthInstance.maxHeartbeats 200000
variable {D : D7}
end Comp
section Level
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word}
end Level
set_option maxHeartbeats 2000000 in
theorem uloc_le_levelPrime_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → (J.A.K j (show j ≤ B.R.m by omega) (J.ι j α)).lev.Uloc v ≤ (J'.A.K j (show j ≤ B.R.m by omega) (J'.ι j α')).lev.Uloc v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α t' J' hJ' α' v hv
  letI : Field a.k := a.fld
  letI : ValuativeRel a.k := a.val
  letI : TopologicalSpace a.k := a.top
  letI : IsNonarchimedeanLocalField a.k := a.loc
  exact uloc_le_of_std hW.tr.ok hW.tr.pins.some hJ.is hJ'.is hTr.std a.o.I ha.shape.pre.nodup ha.shape.pre.all j _ _ _ v
    (exists_splitPt hTr.std v hv)
end GlobalTheory.PenLevPrime
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.VolLevTopNeZero
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl
noncomputable section
namespace GlobalTheory.TopVol
theorem volLev_top_ne_zero_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ U : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X'), U ≤ GfC _ → IsCompact (U : Set (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) → IsOpen ((U.subgroupOf (GfC _) : Subgroup (GfC (I.rec7 l Z).sp.X')) : Set (GfC (I.rec7 l Z).sp.X')) → volLev a.g.volT U ≠ 0 := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a _ _ U hle hc ho
  exact volLev_ne_zero_of_isCompact _
    (Formalism.IndefR.Eqv.isCompact_GinfC (I.rec7 l Z).sp.X'_sig fun τ => Or.inl ((I.rec7 l Z).X'_posDef τ)) _ U hle hc ho
end GlobalTheory.TopVol
end
end
end

