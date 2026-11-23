module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0998
public import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1658
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaTildeHeckeCharSplitMulSignOfNormFormula
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCongruentOfCommutatorPhaseEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnramifiedAwayDifferent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.StdCharUnrF

open GlobalTheory.Idele WithZero
open GlobalTheory.StdDual (codiff codiff_ne_zero)

theorem psiUnr_of_not_le : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → PsiUnr ψ v := by
  classical
  intro F _ _ ψ hψ v hv x
  have hc := GlobalTheory.SplitUnram.count_codiff_eq_zero v (fun h => hv (Ideal.le_of_dvd h))
  set α : Af F := GlobalTheory.AdelicU.singleFin v x with hα
  have hαv : α v = x := GlobalTheory.AdelicU.evalV_singleFin_self v x
  have hαw : ∀ w, w ≠ v → α w = 0 := fun w hw => GlobalTheory.AdelicU.evalV_singleFin_ne hw x
  have h := GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.LatVacArith.psi_fin_rat hψ) α
  have key : (∀ y ∈ v.adicCompletionIntegers F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v (x * y) = 1) ↔
      ∀ β : Af F, (∀ w, β w ∈ w.adicCompletionIntegers F) → ψ (pairA F 0 (β * α)) = 1 := by
    constructor
    · intro H β hβ
      have e : β * α = GlobalTheory.AdelicU.singleFin v (x * β v) := by
        apply GlobalTheory.AdelicU.af_ext
        intro u
        by_cases hu : u = v
        · subst hu
          rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]
          change β u * x = x * β u
          ring
        · rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]
      rw [e]
      exact H _ (hβ v)
    · intro H y hy
      have e : GlobalTheory.AdelicU.singleFin v y * α = GlobalTheory.AdelicU.singleFin v (x * y) := by
        rw [hα, ← GlobalTheory.AdelicU.singleFin_mul, mul_comm]
      have := H (GlobalTheory.AdelicU.singleFin v y) (fun w => by
        by_cases hw : w = v
        · subst hw
          change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin w y) ∈ _
          rw [GlobalTheory.AdelicU.evalV_singleFin_self]
          exact hy
        · change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin v y) ∈ _
          rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw]
          exact zero_mem _)
      rw [e] at this
      exact this
  rw [key, ← h, mem_adelicIdeal_iff codiff_ne_zero, HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro H
    have := H v
    rwa [hc, neg_zero, exp_zero, hαv] at this
  · intro H w
    by_cases hw : w = v
    · subst hw
      rw [hc, neg_zero, exp_zero, hαv]
      exact H
    · rw [hαw w hw, map_zero]
      exact zero_le

end GlobalTheory.StdCharUnrF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerOperatorMemAdelicSchwartzStdChar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchrSchA

theorem schr_mem_schA_of_isStdChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ]
    (w : (κ → AF D.host.F) × (κ → AF D.host.F)), ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
      GlobalTheory.WeilM.schr ψ w φ ∈ GlobalTheory.WeilM.schA D.host.F κ := by
  intro D ψ hψ κ _ w φ hφ
  exact GlobalTheory.HeisSchA.schr_mem_schA ψ (GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ) w φ hφ

end GlobalTheory.SchrSchA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhatStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_preserves_schwartz_bruhat : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v),
      GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt ψ v) w φ ∈ GlobalTheory.WeilM.SB _ := by
  first | exact @GlobalTheory.SchrSB.schr_mem_SB | exact GlobalTheory.SchrSB.schr_mem_SB | (intros; apply GlobalTheory.SchrSB.schr_mem_SB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartz
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

namespace GlobalTheory.SchrKeepsSchA

theorem schr_mem_schA : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (p : (κ → AF F) × (κ → AF F)), ∀ Φ ∈ schA F κ, schr ψ p Φ ∈ schA F κ := by
  intro F _ _ ψ hψ κ _ p Φ hΦ
  exact GlobalTheory.HeisSchA.schr_mem_schA ψ hψ p Φ hΦ

end GlobalTheory.SchrKeepsSchA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTorusTsumMajorantTranslatedRationalPointsL
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.SiegelSet.tsum_maj_invPt_torus_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ c : ℝ, 0 < c → ∀ K : Set (Mx D V.rank n), IsCompact K → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a : GA D V, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram X Y t a → ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ENNReal.ofReal (GlobalTheory.Unf.maj θ K N (GlobalTheory.SiegelFormula.invPt V a ξ)) ≤ ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  intro D θ hθ V n r X Y hXY c hc K hK
  obtain ⟨L, hL, hden⟩ := _root_.GlobalTheory.ThetaConv.exists_den_of_inBox D V.rank n K hK
  obtain ⟨N, C, hC, hst⟩ := _root_.GlobalTheory.TorusStack.lattice_count_stack D V.rank n r X Y
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram)
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) c hc L hL
  refine ⟨N, C, hC, fun t ht a ha => ?_⟩
  obtain ⟨hfin, hrel⟩ := _root_.GlobalTheory.TorusInv.torus_inv D θ hθ V r X Y hXY t ht.1 a ha
  refine le_trans (ENNReal.tsum_le_tsum fun ξ => ?_)
    (hst t ht (fun τ => compAt θ τ (Formalism.L2.Theta.mt V a⁻¹)) hrel)
  have e : (GlobalTheory.SiegelFormula.invPt V a ξ : Matrix (Fin V.rank) (Fin n) (AE D)) =
      HMul.hMul (Formalism.L2.Theta.mt V a⁻¹) (ξ.map (incA D) : Matrix (Fin V.rank) (Fin n) (AE D)) := rfl
  have hcomp : ∀ τ, compAt θ τ (GlobalTheory.SiegelFormula.invPt V a ξ) =
      compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) * ξ.map (tauE D τ) := by
    intro τ
    have h1 : compAt θ τ (ξ.map (incA D) : Mx D V.rank n) = ξ.map (tauE D τ) := by
      ext i j
      exact (hθ τ).1 (ξ i j)
    rw [e, ← h1]
    exact Matrix.map_mul (f := (θ τ).comp (infPart D))
  unfold GlobalTheory.Unf.maj
  split_ifs with hb
  · have hmem : ξ ∈ {ξ : Matrix (Fin V.rank) (Fin n) D.host.E |
        ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)} := by
      refine hden _ ξ ?_ hb
      rw [e, Matrix.map_mul, hfin, Matrix.one_mul]
    rw [Set.indicator_of_mem hmem]
    simp only [GlobalTheory.Unf.realSize, hcomp, le_refl]
  · simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignForWeilModelFamily
section
noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.DatumFourier

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar


end GlobalTheory.DatumFourier

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne

theorem isThPVecOf_empty {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS sT ΛS ΛT βS βT Pg Q ξ ξ' f₀ f}
    (hQ : Q = ∅) (h : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg ∅ ξ f₀ f) :
    IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ' f₀ f := by
  subst hQ
  have e : ∀ y, omegaQ (a := T.rank) (b := S.rank) ∅ T.rank ξ' (-1) y = omegaQ ∅ T.rank ξ (-1) y := fun y => by
    simp [omegaQ]
  unfold IsThPVecOf at h ⊢
  simp only [e]
  exact h


end GlobalTheory.GalOne

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianLatticeSplitPlaceComponentsDualStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewHermitianLattice_splitPlace_components_dual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d : ℕ) (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (c : GL (Fin d) (Fv F v)), IsSplitBasis t W.L c →
    ∃ (z : (Fv F v)ˣ) (c₂ : GL (Fin d) (Fv F v)), (PsiUnr B.ψ v → z = 1) ∧
      (c₂⁻¹).1 = (z : Fv F v) • (c.1ᵀ * W.J.map t) ∧ IsSplitBasis (t.comp σ) W.L c₂ := by
  first | exact @GlobalTheory.SkewSplitDual.skewSplitDual | exact GlobalTheory.SkewSplitDual.skewSplitDual | (intros; apply GlobalTheory.SkewSplitDual.skewSplitDual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPartBaseLinksOfPrimitiveRows
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.LowRow.baseLinks_of_prims : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), ∀ s : ℕ, A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → PrimRows3 R F → (∀ i, R.phs i = 1) → GlobalTheory.Hk3.Core R.toRealDat F.lv2 ∧ A3.A.fam.Ok s ∧ BaseLinks R.toRealDat F.lv2 := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F s hOk hsep hC hE hP hph
  have c := RealDat3.characterisation_of_weak hC hE
  have hR := complex_data_conditions_base_level_of_primitive_links hOk hsep hC hP
  refine ⟨⟨c.lev, c.grp, c.fam, c.models, c.chain, c.thP⟩, hOk.ok2, ?_, ?_, ?_⟩
  · have h := hR.lifts0.1
    rw [GlobalTheory.CharRealise.toCx3_eq_one R F hph] at h
    exact h
  · have h := hR.ratTh
    rw [GlobalTheory.CharRealise.toCx3_eq_one R F hph] at h
    exact h
  · have h := hR.proviso0
    rw [GlobalTheory.CharRealise.toCx3_eq_one R F hph] at h
    exact h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuInvHasInfinityTypeCmType
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.SqNum

theorem nuH_inv_hasInf : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (i j : Fin D.R.m), (nuH G μ₀ i j)⁻¹.HasInf (Formalism.L2.Host.embTau D) (fun τ => 2 * ((GlobalTheory.ChiGrid.num D sc.cGap τ).e (j + 1) + GlobalTheory.ChiGrid.cen D sc.cGap τ (D.R.m - i))) := by
  intro D T L sc μ₀ hL G i j k
  have a1 : 1 ≤ D.R.m - i := by have := i.2; omega
  have a2 : D.R.m - i ≤ D.R.m := by omega
  obtain ⟨n', hn', hinf⟩ := (L.C.isMu0 j).inf
  have hk : ∀ τ, Formalism.L2.Host.embTau D τ (k : D.host.E) ≠ 0 := fun τ => by simp
  rw [nuH, hL.xi_base, mul_one, div_eq_mul_inv, HChar.inf_inv, HChar.inf_mul, HChar.inf_inv, Units.val_inv_eq_inv_val,
    Units.val_mul, Units.val_inv_eq_inv_val, hinf k, G.ch.inf _ a1 a2 k, ← D.eTau.prod_comp, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h1 : n' (D.eTau τ) = -(2 * (num D sc.cGap τ).e (j + 1)) := by
    have := hn' (D.eTau τ)
    beta_reduce at this
    rw [Formalism.L2.Host.eExp, Equiv.symm_apply_apply,
      (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D sc.cGap) (cen D sc.cGap τ)).2.2] at this
    have h2 : ((n' (D.eTau τ) : ℤ) : ℚ) = ((-(2 * (num D sc.cGap τ).e (j + 1)) : ℤ) : ℚ) := by
      rw [this]; push_cast; unfold num; ring
    exact_mod_cast h2
  have hne : (Formalism.L2.Host.embTau D τ (k : D.host.E) / ((‖Formalism.L2.Host.embTau D τ (k : D.host.E)‖ : ℝ) : ℂ)) ≠ 0 :=
    div_ne_zero (hk τ) (by simpa using hk τ)
  beta_reduce
  rw [h1]
  change ((Formalism.L2.Host.embTau D τ (k : D.host.E) / ((‖Formalism.L2.Host.embTau D τ (k : D.host.E)‖ : ℝ) : ℂ)) ^ _ * _)⁻¹ = _
  rw [← zpow_neg, ← zpow_add₀ hne, ← zpow_neg]
  congr 1
  ring

end GlobalTheory.FunObj.SqNum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuInvUnramifiedOverInertPrime
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.SqNum

theorem nuH_inv_unrAt_of_inertQ : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (i j : Fin D.R.m) (P : HeightOneSpectrum (𝓞 D.host.E)), (∃ q : ℕ, q.Prime ∧ InertQ D q ∧ ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) → (nuH G μ₀ i j)⁻¹.UnrAt P := by
  intro D T L sc μ₀ hL G i j P hq
  obtain ⟨q, hqp, hqi, hqP⟩ := hq

  have hmu : (L.C.mu0 j).UnrAt P := (L.C.isMu0 j).unr P fun k hk => by
    have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := hk
    have e := prime_unique (K := D.host.E) hqp (D.host.g_prime k) hqP hk'
    exact GlobalTheory.Mem.Col2.SplitChar.not_inertQ_g k (e ▸ hqi)

  have hchi : (G.ch.chiH (D.R.m - i)).UnrAt P := by
    refine G.ch.unr (D.R.m - i) (by omega) (by omega) P fun hv => ?_
    obtain ⟨e, he⟩ := G.pl.w_split _ hv
    have hov := G.pl.w_over _ hv
    set w := G.pl.w (P.under (𝓞 D.host.F))
    have h1 : ((q : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (q : 𝓞 D.host.F) ∈ P.asIdeal
      simpa using hqP
    rw [← hov] at h1
    have hqw : ((q : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
      have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (q : 𝓞 D.host.F) ∈ w.asIdeal := h1
      simpa using h2
    have hfix := hqi _ w.isPrime w.ne_bot hqw
    obtain ⟨⟨e1, e2, v, ε, hε, e3⟩, e4⟩ := he
    exact GlobalTheory.DualPairCheck.split_ne e ⟨e1, e2, v, ε, hε, e3⟩
      (GlobalTheory.EtaProduct.cA_of_fixed ⟨e1, ⟨v, ε, hε, Or.inl ⟨e2, e3⟩⟩, e4⟩ hfix)
  have e : nuH G μ₀ i j = L.C.mu0 j * (G.ch.chiH (D.R.m - i))⁻¹ := by
    rw [nuH, hL.xi_base, mul_one, div_eq_mul_inv]
  rw [e]
  exact (hmu.mul hchi.inv).inv

end GlobalTheory.FunObj.SqNum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCongruentOfCommutatorPhaseEqStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_congruent_of_commutatorPhase_eq : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → IsCoprime 𝔪 D.host.𝔟 → ∀ {a d : ℕ}, a ≤ d → ∀ (r r' : GA D a), r ∈ intG D a → r' ∈ intG D a → ∀ x x' : Matrix (Fin d) (Fin a) D.host.E, pt D (tor0 D ⊤ δ) δ x ∈ (La0 D (tor0 D ⊤ δ) a d) → pt D (tor0 D ⊤ δ) δ x' ∈ (La0 D (tor0 D ⊤ δ) a d) → (∀ i j, (x.map (inc D) - (unitBlock D 0 a d).map (inc D) * (((r⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈ hatId D 𝔪) → (∀ i j, (x'.map (inc D) - (unitBlock D 0 a d).map (inc D) * (((r'⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈ hatId D 𝔪) → (∀ y ∈ (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)), Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x) y = Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x') y) → CongOne D 𝔪 (r⁻¹ * r') := by
  first | exact @GlobalTheory.FunObj.StdDatum.PhaseCong.cong_of_kap_eq | exact GlobalTheory.FunObj.StdDatum.PhaseCong.cong_of_kap_eq | (intros; apply GlobalTheory.FunObj.StdDatum.PhaseCong.cong_of_kap_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicAddCharNontrivialFinitePlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1 := by
  first | exact @GlobalTheory.PsiNontrivAt.exists_psiAt_ne_one | exact GlobalTheory.PsiNontrivAt.exists_psiAt_ne_one | (intros; apply GlobalTheory.PsiNontrivAt.exists_psiAt_ne_one <;> assumption)
end

