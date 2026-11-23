module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LiftsGen
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueLevelCharacterArgumentAtTypePlace
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0126

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalFormCoordinatesCoeffMemCoefficientField
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

namespace GlobalTheory.FormCoef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem typeX_mem (R : RealDat D A Ks) (t : T) (M : Subfield ℂ)
    (hχ : ∀ i : Fin D.R.m, ∀ PP ∈ R.Pg, ∀ x, ((R.chi ((i : ℕ) + 1) PP x : ℂˣ) : ℂ) ∈ M)
    (hξ : ∀ PP ∈ R.Q t, ∀ x, ((R.xiR t PP x : ℂˣ) : ℂ) ∈ M) (k) :
    (((levEnv D.sp.X' R.βX (R.datXt t)).χ k : ℂˣ) : ℂ) ∈ M := by
  show levFn R.βX (Lev.flag1L (R.datXt t)) _ ∈ GlobalTheory.RationalValues.unitsIn M
  unfold levFn
  refine mul_mem (mul_mem ?_ (prod_mem fun PP hPP => prod_mem fun c hc => ?_)) (prod_mem fun PP hPP => ?_)
  · have h1 : ∀ x, ext1 (Lev.flag1L (R.datXt t)).P.H (Lev.flag1L (R.datXt t)).P.chi x = 1 := fun x => Lev.subgroupCharExtension_one_apply _ x
    rw [h1]
    exact one_mem _
  · have hc' : c < D.R.m := Finset.mem_range.1 hc
    exact show R.chi ((⟨c, hc'⟩ : Fin D.R.m) + 1 : ℕ) PP _ ∈ GlobalTheory.RationalValues.unitsIn M from hχ ⟨c, hc'⟩ PP hPP _
  · exact inv_mem (show R.xiR t PP _ ∈ GlobalTheory.RationalValues.unitsIn M from hξ PP hPP _)

end GlobalTheory.FormCoef

namespace GlobalTheory.FormCoef

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1600000 in
theorem coeff_formC_mem : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A),
    HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (x : A.fam.amb.FR t) (y : FinPt ch.G (.grid 0 D.R.m)) m,
      AddMonoidAlgebra.coeff (ch.S.formC t (R.jX t x) y).1 m ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F hS _ _ t x y m
  obtain ⟨gram, c₀, c₁, hT, hco⟩ := ch.S.co_is
  have hc := hS.core
  obtain ⟨k, v, hv⟩ := GlobalTheory.RationalValues.exists_ext_eq (R.B.R t).pres c₀ (GlobalTheory.RationalValues.coef_mem (hT.coefR t))
    (GlobalTheory.RationalValues.rho_mem hT.mapR) x (toXf y)
  have h0 : (R.HX t).e (R.jX t x) (toXf y) = (((levEnv D.sp.X' R.βX (R.datXt t)).χ k : ℂˣ) : ℂ) • c₀ v :=
    (congrFun (hc.models.jX t x) (toXf y)).trans hv
  have i0 : Fin D.R.m := ⟨0, by have := D.R.two_le_m; omega⟩
  obtain ⟨a, ha⟩ := typeX_mem R t D.what₂.embLL.fieldRange (GlobalTheory.RationalValues.chiVal_of_chiW R hc.grp.chiW)
    (GlobalTheory.RationalValues.xiR_mem R hc.lev hc.fam.pl_onto hc.fam.muVal hT.ok i0 t) k
  have h1 : ch.S.formC t (R.jX t x) y = ch.S.co (c₀ (a • v)) := by
    rw [SumChoice.formC, h0, map_smulₛₗ, ha]
  rw [h1, hco, ← MvPolynomial.map_rename, MvPolynomial.coeff_map]
  exact ⟨_, rfl⟩

end GlobalTheory.FormCoef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexLevelSelfDualStabilizerEqProdLocal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)

noncomputable section

namespace GlobalTheory.ParIndex

theorem gram_herm (D : D7) (V : HSp D) : Formalism.UG.IsHerm (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := by
  refine Matrix.ext fun i j => ?_
  show (D.sp.cm.sig : D.host.E →+* D.host.E) (V.gram j i) = V.gram i j
  exact V.herm.eq (V.frame j) (V.frame i)

theorem gram_det_ne (D : D7) (V : HSp D) : V.gram.det ≠ 0 :=
  ((GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V).2

theorem hermitianSpace_standard_lattice_span_eq_top (D : D7) (V : HSp D) :
    Submodule.span D.host.E (L0c D V) = ⊤ := by
  let f := V.frame.equivFun.toLinearMap
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := V.L0.map (f.restrictScalars (𝓞 D.host.E))
  have hL : (L : Set (Fin V.rank → D.host.E)) = L0c D V := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ∑ i, V.frame.equivFun x i • V.frame i ∈ V.L0
      rwa [V.frame.sum_equivFun]
    · intro hv
      refine ⟨V.frame.equivFun.symm v, ?_, V.frame.equivFun.apply_symm_apply v⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact hv
  rw [← hL, eq_top_iff]
  intro v _
  obtain ⟨x, rfl⟩ := V.frame.equivFun.surjective v
  have hx : x ∈ Submodule.span D.host.E (V.L0 : Set V.V) := by
    classical
    let W := Submodule.span D.host.E (V.L0 : Set V.V)
    have hW : W = ⊤ := by
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨z, hz, hz₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
        (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e z ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
        intro y hy
        have hyz : V.hT (e z) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hz)
        have := V.herm.eq (e z) y
        simp only [hyz, map_zero] at this
        simp [← this]
      let j : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e z)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective j fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hz₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
    change x ∈ W
    rw [hW]; trivial
  have := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_span] at this
  exact this

theorem relIndex_levV_latLev : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Hl : ∀ PP : ↥R.Pg, Subgroup (GL (Fin D.R.r) (kP PP.1))) (cl : ∀ PP : ↥R.Pg, Hl PP →* ℂˣ), GlobalTheory.Hk3.Core R F → P = LevelP.ofLocal Hl cl → (((GlobalTheory.AdelicScalar.levV R i t P m).relIndex (GlobalTheory.Mass.Levels.latLev (Vc D i)) : ℕ) : ℝ) = (∏ PP ∈ R.Pg.attach, (Nat.card (GL (Fin (Vc D i).rank) (kP PP.1)) : ℝ) / ((Nat.card (Hl PP) : ℝ) * (Nat.card (GL (Fin D.R.t) (kP PP.1)) : ℝ) * (Nat.card (kP PP.1) : ℝ) ^ (D.R.r * D.R.t))) * ∏ PP ∈ R.Q t, (Nat.card (GL (Fin (Vc D i).rank) (kP PP)) : ℝ) / ((Nat.card (GL (Fin D.R.r) (kP PP)) : ℝ) * (Nat.card (GL (Fin D.R.t) (kP PP)) : ℝ) * (Nat.card (kP PP) : ℝ) ^ (D.R.r * D.R.t)) := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t P m Hl cl hC hP
  obtain ⟨c, hB⟩ := hC.lev.βV i
  rw [one_pow] at hB
  have hK := _root_.GlobalTheory.LatLevEq.latLev_eq_UA_inf_St D (Vc D i) (R.βV i) _ hB
  obtain ⟨hsplit, hdis⟩ := _root_.GlobalTheory.TwistTypePlaces.isSplitSet_union R F hC t
  have hspan : Submodule.span D.host.E ((R.ΛV i : Submodule (𝓞 D.host.E) _) : Set (Fin (Vc D i).rank → D.host.E)) = ⊤ := by
    rw [eq_top_iff, ← hermitianSpace_standard_lattice_span_eq_top D (Vc D i)]
    refine Submodule.span_mono fun x hx => ?_
    have := hB.2.2.2.1 x hx
    rwa [Nat.cast_one, one_smul] at this
  have hdual : dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) (Vc D i).gram (R.ΛV i) = ((R.ΛV i : Submodule (𝓞 D.host.E) _) : Set (Fin (Vc D i).rank → D.host.E)) := by
    have e := Formalism.IndefR.Fin.Lifts.span_dualSet_eq (D.sp.cm.sig : D.host.E →+* D.host.E) (Vc D i).gram (R.ΛV i)
    have h := hB.2.1
    unfold Formalism.L2.Herm.dualL at h
    rw [h] at e
    exact e.symm
  have hn : (Vc D i).rank = D.R.r + D.R.t := by
    rw [D.sp.V_rank _ (Nat.le_add_left _ _) i.2]; rfl
  have hSt : ∀ x ∈ GlobalTheory.Mass.Levels.latLev (Vc D i), x ∈ Formalism.L2.DIV.St (R.βV i) := by
    intro x hx; rw [hK] at hx; exact hx.2
  set Ts := R.Pg ∪ R.Q t with hTs
  let φ : GlobalTheory.Mass.Levels.latLev (Vc D i) →* (∀ PP : ↥Ts, GL (Fin (Vc D i).rank) (kP PP.1)) :=
    { toFun := fun x PP => redFn (R.βV i) PP.1 x
      map_one' := by funext PP; exact redFn_one _
      map_mul' := fun x y => by funext PP; exact redFn_mul (hSt _ x.2) (hSt _ y.2) _ }
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx, hred⟩ := Formalism.IndefR.Fin.Lifts.redSurj_sd D.sp.cm Ts (gram_herm D (Vc D i))
      (isUnit_iff_ne_zero.2 (gram_det_ne D (Vc D i))) hspan hdual hB.1 hsplit y
    exact ⟨⟨x, by rw [hK]; exact hx⟩, funext hred⟩
  let Bl : ∀ PP : ↥Ts, Subgroup (GL (Fin (Vc D i).rank) (kP PP.1)) := fun PP =>
    if h : PP.1 ∈ R.Pg then parSub (r_le_V i) (Hl ⟨PP.1, h⟩) else blockTri (blk2 D.R.r)
  have hBp : ∀ (PP : ↥Ts) (h : PP.1 ∈ R.Pg), Bl PP = parSub (r_le_V i) (Hl ⟨PP.1, h⟩) := fun PP h => dif_pos h
  have hBn : ∀ (PP : ↥Ts), PP.1 ∉ R.Pg → Bl PP = blockTri (blk2 D.R.r) := fun PP h => dif_neg h
  have hcomap : (GlobalTheory.AdelicScalar.levV R i t P m).subgroupOf (GlobalTheory.Mass.Levels.latLev (Vc D i)) =
      (Subgroup.pi Set.univ Bl).comap φ := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi]
    have hxK : (x : GL (Fin (Vc D i).rank) (Lev.EAf D)) ∈ Formalism.L2.DIV.UA D.sp.cm (Vc D i).gram ⊓ Formalism.L2.DIV.St (R.βV i) := by
      rw [← hK]; exact x.2
    subst hP
    constructor
    · intro hx PP _
      have hx' := (mem_lev.1 hx)
      obtain ⟨-, -, hg, hq⟩ := mem_parLev.1 hx'.1
      show redFn (R.βV i) PP.1 x ∈ Bl PP
      by_cases h : PP.1 ∈ R.Pg
      · rw [hBp PP h]
        refine ⟨?_, ?_⟩
        · have := hg PP.1 h
          change redFn (R.βV i) PP.1 x ∈ blockTri (blkOf D.R.r D.R.t) at this
          rwa [blockTri_blkOf_eq hn] at this
        · exact hx'.2 ⟨PP.1, h⟩ (Set.mem_univ _)
      · rw [hBn PP h]
        have hQ : PP.1 ∈ R.Q t := by
          rcases Finset.mem_union.1 PP.2 with h' | h'
          · exact absurd h' h
          · exact h'
        exact hq PP.1 hQ
    · intro hx
      have hx1 : ∀ PP (h : PP ∈ Ts), redFn (R.βV i) PP x ∈ Bl ⟨PP, h⟩ := fun PP h => hx ⟨PP, h⟩ (Set.mem_univ _)
      refine mem_lev.2 ⟨mem_parLev.2 ⟨hxK.1, hxK.2, fun PP hPP => ?_, fun PP hPP => ?_⟩, ?_⟩
      · have := hx1 PP (Finset.mem_union_left _ hPP)
        rw [hBp ⟨PP, Finset.mem_union_left _ hPP⟩ hPP] at this
        show _ ∈ blockTri (blkOf D.R.r D.R.t)
        rw [blockTri_blkOf_eq hn]
        exact this.1
      · have := hx1 PP (Finset.mem_union_right _ hPP)
        by_cases h : PP ∈ R.Pg
        · rw [hBp ⟨PP, Finset.mem_union_right _ hPP⟩ h] at this
          exact this.1
        · rw [hBn ⟨PP, Finset.mem_union_right _ hPP⟩ h] at this
          exact this
      · intro PP _
        have := hx1 PP.1 (Finset.mem_union_left _ PP.2)
        rw [hBp ⟨PP.1, Finset.mem_union_left _ PP.2⟩ PP.2] at this
        exact this.2

  have hidx : (((GlobalTheory.AdelicScalar.levV R i t P m).relIndex (GlobalTheory.Mass.Levels.latLev (Vc D i)) : ℕ) : ℝ) =
      ∏ PP : ↥Ts, (((Bl PP).index : ℕ) : ℝ) := by
    rw [Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hφ, GlobalTheory.index_pi_univ_dep, Nat.cast_prod]
  let g : Pl D.host.E → ℝ := fun PP =>
    if h : PP ∈ R.Pg then (Nat.card (GL (Fin (Vc D i).rank) (kP PP)) : ℝ) / ((Nat.card (Hl ⟨PP, h⟩) : ℝ) *
      (Nat.card (GL (Fin D.R.t) (kP PP)) : ℝ) * (Nat.card (kP PP) : ℝ) ^ (D.R.r * D.R.t))
    else (Nat.card (GL (Fin (Vc D i).rank) (kP PP)) : ℝ) / ((Nat.card (GL (Fin D.R.r) (kP PP)) : ℝ) *
      (Nat.card (GL (Fin D.R.t) (kP PP)) : ℝ) * (Nat.card (kP PP) : ℝ) ^ (D.R.r * D.R.t))
  have hloc : ∀ PP : ↥Ts, (((Bl PP).index : ℕ) : ℝ) = g PP.1 := by
    intro PP
    haveI : PP.1.asIdeal.IsMaximal := PP.1.isMaximal
    letI : Field (kP PP.1) := Ideal.Quotient.field _
    have hc := Subgroup.card_mul_index (Bl PP)
    have hpos : (Nat.card (Bl PP) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := Bl PP)).ne'
    have e1 : (((Bl PP).index : ℕ) : ℝ) = (Nat.card (GL (Fin (Vc D i).rank) (kP PP.1)) : ℝ) / (Nat.card (Bl PP) : ℝ) := by
      rw [eq_div_iff hpos, mul_comm]
      exact_mod_cast hc
    rw [e1]
    by_cases h : PP.1 ∈ R.Pg
    · have e2 : Bl PP = parSub (r_le_V i) (Hl ⟨PP.1, h⟩) := hBp PP h
      simp only [g, dif_pos h]
      rw [e2, _root_.GlobalTheory.ParIndex.card_parSub (kP PP.1) _ _ _ (r_le_V i) hn]
      push_cast; ring
    · have e2 : Bl PP = parSub (r_le_V i) ⊤ := by
        rw [hBn PP h]
        ext x
        simp [mem_parSub]
      simp only [g, dif_neg h]
      rw [e2, _root_.GlobalTheory.ParIndex.card_parSub (kP PP.1) _ _ _ (r_le_V i) hn, Subgroup.card_top]
      push_cast; ring
  rw [hidx, Finset.prod_congr rfl (fun PP _ => hloc PP), Finset.prod_coe_sort Ts g, hTs, Finset.prod_union hdis]
  congr 1
  · rw [← Finset.prod_attach R.Pg g]
    refine Finset.prod_congr rfl fun PP _ => ?_
    simp only [g, dif_pos PP.2]
  · refine Finset.prod_congr rfl fun PP hPP => ?_
    have h : PP ∉ R.Pg := Finset.disjoint_right.1 hdis hPP
    simp only [g, dif_neg h]

end GlobalTheory.ParIndex

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueLevelCharacterArgumentAtTypePlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_levelCharacterArgument_at_typePlace : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∀ PP ∈ R.Pg, ∀ κ : GA D (Yc D 0), finE (Yc D 0) κ ∈ St β → GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ)) = ∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then ((GlobalTheory.SeeConjChar.wA D.R.rS D.R.k (GlobalTheory.SeeConjChar.sideAt X h PP) i j : ℤ) : kP PP) * ((upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) : GL (Fin D.R.r) (kP PP)).val i j) else 0 := by
  first | exact @GlobalTheory.SeeResAt.resT_argT | exact GlobalTheory.SeeResAt.resT_argT | (intros; apply GlobalTheory.SeeResAt.resT_argT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubstMemFg
section
namespace GlobalTheory.SubstitutionFinitelyGenerated

theorem fg_of_vars {σ ι : Type*} (φ : ι → MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ)
    (h : ∀ v, ∃ U : Submodule ℂ (MvPolynomial σ ℂ), U.FG ∧ ∀ i, φ i (MvPolynomial.X v) ∈ U)
    (P : MvPolynomial σ ℂ) : ∃ V : Submodule ℂ (MvPolynomial σ ℂ), V.FG ∧ ∀ i, φ i P ∈ V := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    refine ⟨Submodule.span ℂ {MvPolynomial.C c}, Submodule.fg_span_singleton _, fun i => ?_⟩
    have : φ i (MvPolynomial.C c) = MvPolynomial.C c := (φ i).commutes c
    rw [this]
    exact Submodule.mem_span_singleton_self _
  | add p q hp hq =>
    obtain ⟨V₁, h₁, h₁'⟩ := hp
    obtain ⟨V₂, h₂, h₂'⟩ := hq
    refine ⟨V₁ ⊔ V₂, h₁.sup h₂, fun i => ?_⟩
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (h₁' i) (h₂' i)
  | mul_X p v hp =>
    obtain ⟨V₁, h₁, h₁'⟩ := hp
    obtain ⟨V₂, h₂, h₂'⟩ := h v
    refine ⟨V₁ * V₂, h₁.mul h₂, fun i => ?_⟩
    rw [map_mul]
    exact Submodule.mul_mem_mul (h₁' i) (h₂' i)

theorem subst_mem_fg : ∀ {D : Formalism.BasicNotions.D7} {a b : ℕ} (τ : Formalism.BasicNotions.Rows.Data.Tau (Formalism.BasicNotions.D7.what₂ D)) (ε : Fin a → Bool) (ε' : Fin b → Bool) (P : Formalism.IndefR.Links.PolF D b a), ∃ (V : Submodule ℂ (Formalism.IndefR.Links.PolF D b a)), Submodule.FG V ∧ ∀ (g : Matrix (Fin a) (Fin a) ℂ) (k : Matrix (Fin b) (Fin b) ℂ), (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.subst τ ε ε' g k : Formalism.IndefR.Links.PolF D b a → Formalism.IndefR.Links.PolF D b a) P ∈ V := by
  intro D a b τ ε ε' P
  obtain ⟨V, hV, hV'⟩ := fg_of_vars
    (fun gk : Matrix (Fin a) (Fin a) ℂ × Matrix (Fin b) (Fin b) ℂ => GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.subst τ ε ε' gk.1 gk.2) (by
      intro v
      refine ⟨Submodule.span ℂ (insert (MvPolynomial.X v)
        (Set.range fun lm : Fin b × Fin a => MvPolynomial.X (τ, lm.1, lm.2))),
        Submodule.fg_span ((Set.finite_range _).insert _), fun gk => ?_⟩
      unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.subst
      rw [MvPolynomial.aeval_X]
      by_cases hv : v.1 = τ
      · rw [if_pos hv]
        refine Submodule.sum_mem _ fun l _ => Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
        exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨(l, m), rfl⟩)
      · rw [if_neg hv]
        exact Submodule.subset_span (Set.mem_insert _ _)) P
  exact ⟨V, hV, fun g k => hV' (g, k)⟩

end GlobalTheory.SubstitutionFinitelyGenerated
end

