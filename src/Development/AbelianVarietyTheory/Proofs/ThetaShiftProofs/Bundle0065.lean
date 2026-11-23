module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TransvInOfHasPrinc
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPolynomialBoundRunConstantsDegreeFour
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmFamilyFunctionalsDetectLowCoefficients
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridgeAlt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.QuotientBoundOfKillDetectConstantRoomStatement
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0040
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumFunctionalKillsComplexCombinations
section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ArcCM

section Free

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ

theorem kill_comb_over (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁]
    [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (ι : K₁ →+* ℂ) (σ : c.F →+* ℂ) (hσ : ι.comp (algebraMap c.F K₁) = σ)
    (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (La c₁ : ℝ)
    (hg : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hd : Fam n' La c₁ d) (hD : Dom a' n)
    (hP : GlobalTheory.FrameNorm.HasPrinc U l.M)
    (hχ : ∀ k, ∀ gm ∈ (U.X k).Γ, (U.X k).χ (Formalism.L2.PjFree.laU U a' n k) gm = 1)
    (m : ℕ) (a : Fin m → ℂ) (F : Fin m → Rul Xo c) (f : ∀ k : U.Comp, Frame (U.X k).Ψ r → ℂ)
    (hF : ∀ i, F i ∈ sec Xo c a' n)
    (hB : ∀ i k, (U.X k).IsBddSec (Formalism.L2.PjFree.laU U a' n k) (Formalism.L2.PjFree.rdU U (F i) k))
    (hf : ∀ k, f k ∈ (U.X k).SSgt (Formalism.L2.PjFree.laU U a' n k) c₁)
    (he : ∀ k, ∀ x ∈ (U.X k).dom, f k x = ∑ i, a i * Formalism.L2.PjFree.rdU U (F i) k x) (μ : ArcLt Dw →₀ ℕ) :
    ∑ i, a i * ι (cfOf d.yF μ d.jj (F i)) = 0 := by
  subst hσ
  exact _root_.GlobalTheory.ArcKill.sum_cfOf_eq_zero GlobalTheory.ArcCM.known_holds E H Dw l Xo c K₁ d ι r U a' n n' La c₁ hg hU hd hD
    (GlobalTheory.TransvPrinc.transvIn_of_hasPrinc E H Dw l Xo c _ r U a' n hP hχ) m a F f hF hB hf he μ

end Free

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions GlobalTheory.ArcCM GlobalTheory.Shares

theorem kill_comb_rec : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ), InR D j → ∀ (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁), FamQ T.toCore j ka CR Tt cc K₁ d → ∀ σ₁ : K₁ →+* ℂ, σ₁.comp (algebraMap T.Q.c.F K₁) = T.σ₀ → ∀ (m : ℕ) (a : Fin m → ℂ) (F : Fin m → (recB h.toLawsCore).Cusp j ka) (f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ), (∀ k, f k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j ka k) (WeightFamilies.c1 D CR Tt cc j)) → (∀ k, ∀ x ∈ ((T.U j T.σ₀).X k).dom, f k x = ∑ i, a i * rdR h j (F i) k x) → ∑ i, a i * σ₁ (cfOf d.yF d.μ d.jj (F i).1) = 0 := by
  intro D T h j hj ka CR Tt cc K₁ _ _ _ d hd σ₁ hσ m a F f hf he
  exact kill_comb_over _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d σ₁ T.σ₀ hσ D.R.r (Formalism.L2.PjFree.Unf.ofPj (T.U j T.σ₀))
    (wtA ka) ka.n _ _ _ T.good_σ₀ (h.unf j hj _ T.good_σ₀) hd (dom_wtA ka)
    (GlobalTheory.RunIn.gamAt_of_lawsM D T.toCore h.toLawsCore.toLawsM j hj _ T.good_σ₀)
    (h.chiTriv j hj _ T.good_σ₀ _ _ (dom_wtA ka)) m a (fun i => (F i).1) f
    (fun i => cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) _ _ (cutR_le T.C j _ (F i).2))
    (fun i k => ((GlobalTheory.CuspFormsCompare.mem_holSub_iff_forall_SS _ _ _).1
      (((mem_cusp (T.Q.Xo j) T.Q.c (T.U j) _ _ _).1 (cutR_le T.C j _ (F i).2)).2 _ T.good_σ₀) k).1) hf he d.μ

end GlobalTheory.ArcCM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RecursivePageLatticeBound
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

set_option autoImplicit false

namespace GlobalTheory.RunJoin


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem qAt_run : ∃ Cq : ℝ → ℝ → ℝ, ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → j < D.R.m → LatAt (recB h.toLawsCore) j ka → QAt large₂ (recB h.toLawsCore) j ka 7 H.CK 1 4 (Cq H.CA H.CK) 4 Tn (cc D large₂ C2 A2 7 wL) := by
  obtain ⟨C₀, hC₀, hroom⟩ := _root_.GlobalTheory.ArcCM.Room.room_four
  refine ⟨fun a b => 1 + 3 * C₀ a 7 b + 1041, ?_⟩
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hP hjm hL hCR hO hn hlast hsz hT hc hTc
  have h3 : 3 ≤ D.R.r := le_trans (by norm_num) hP.r8
  have hcc : Real.log (Ideal.absNorm D.host.ccK) ≤ large₂.sc.L := by
    obtain ⟨Q, -, -⟩ := hP.page
    exact Q.ccK_log
  obtain ⟨hZ, hR⟩ := hroom D large₂ j ka H.CA 7 H.CK Tn (cc D large₂ C2 A2 7 wL) hP.hyp.1 hcc hj hjm h3 hCR hsz hT hc hTc
  obtain ⟨-, -, -, -, -, -, -, -, hdim, -⟩ := GlobalTheory.RunJoin.net_at_run D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hP
  have hG := GlobalTheory.RunIn.gamAt_of_lawsCore D T.toCore h.toLawsCore
  have hK := _root_.GlobalTheory.ArcCM.known_holds
  have hpp : 1041 * Zb D large₂ ^ 3 ≤ WeightFamilies.PPv D large₂ 1041 3 * ka.size := by
    have e : WeightFamilies.PPv D large₂ 1041 3 = 1041 * Zb D large₂ ^ 3 := by
      unfold WeightFamilies.PPv
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rfl
    rw [e]
    have hZ' : (1 : ℝ) ≤ Zb D large₂ := hZ
    exact le_mul_of_one_le_right (by positivity) ka.one_le_size
  have key := GlobalTheory.ArcCM.qat_of_kill_detect hK D T.toCore h.toLawsCore j ka 7 Tn
    (cc D large₂ C2 A2 7 wL) large₂ H.CK 1 4 (C₀ H.CA 7 H.CK) 4 1041 3
    hG hj hjm hL (GlobalTheory.ArcCM.killQ_of_gamAt hK D T.toCore h.toLawsCore j ka 7 Tn _ hG hj hjm)
    (GlobalTheory.ArcCM.detectQ_of_known hK D T.toCore h.toLawsCore j ka 7 Tn _ hG hj hjm h3 hT hc)
    hZ (hC₀ _ _ _) (by norm_num) hR
    (le_trans hdim hpp)
  have e4 : max (4 : ℝ) (max 4 3) = 4 := by norm_num
  rw [e4] at key
  exact key hCR hO hn hlast hsz hT hc hTc

end GlobalTheory.RunJoin
end

