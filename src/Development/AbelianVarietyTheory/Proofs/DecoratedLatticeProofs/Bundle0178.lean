module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0142
public import Formalism.SharpRestriction.Bundle0001
public import Formalism.LocalRingCardinality.HostCls
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationOfMemNotMemSq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepConjSourceLineEqTargetLine
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0143
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistParahoricChainLastStepsAgreeColumns
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

noncomputable section

namespace GlobalTheory.TwLast

theorem toLoc_of_mat {E k A B : Type} [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : E →+* k) {a b : ℕ} (e : A ≃ Fin a) (e' : B ≃ Fin b) (x : Matrix A B E) :
    x.map ι = toLoc ι e e' (Matrix.toLin' (Matrix.of fun i j => x (e.symm i) (e'.symm j))) := by
  ext i j
  simp [toLoc, Matrix.toLin'_apply, Matrix.mulVec_single, Function.swap]

theorem psi_isLocallyConstant {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (R : Ranks) (W : TwData k) (g : GL (XIx (Fin R.k) (Fin R.t) s ⊕ Fin (0 + 1)) k) :
    IsLocallyConstant (fun p : Matrix (XIx (Fin R.k) (Fin R.t) (s + 1)) (XIx (Fin R.k) (Fin R.t) s) k × (XIx (Fin R.k) (Fin R.t) (s + 1) → k) =>
      (W.T s R).Psi g p.1 p.2) := by
  have hΦ : (W.T s R).Phi s 0 rfl ∈ SB _ := (Chain.ofTwist_regular _ _ _ _ _).1 s 0 rfl
  unfold Chain.Psi om
  refine (IsLocallyConstant.const _).mul (hΦ.1.comp_continuous ?_)
  refine (continuous_const.matrix_mul ?_).matrix_mul continuous_const
  refine continuous_pi fun r => continuous_pi fun c => ?_
  rcases r with r | r <;> rcases c with c | c
  · exact (continuous_apply c).comp ((continuous_apply r).comp continuous_fst)
  · exact (continuous_apply r).comp continuous_snd
  · exact r.elim0
  · exact r.elim0

theorem lastAgree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → LastAgree Ch sel mu cst σ₀ P ι s W ν L := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν hc hA L G hL
  have hPhi := GlobalTheory.T.parahoric_test_functions_agree_rational_points X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hc hA
  have hnm : P.1 ∉ Pr.vGs := hA.nmem
  have hint : ∀ a : X.E, ι a ∈ 𝒪[k] ↔ IntAt P.1 a := hA.compl.int
  have hϖ : (W.ϖ : k) = ι (qOf P.1 : X.E) := hA.compl.unif
  refine ⟨fun al g hg => ⟨fun x₀ y => ?_, fun e' e he' he x₀ y' =>
    GlobalTheory.T.penultimateStepPsi_rationalRep_eq_columnsDatum X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hc hA hPhi _ g hg e' e he' he x₀ y'⟩, ?_⟩
  · have hrat := GlobalTheory.T.penultimateStepPsi_rationalRep_eq_columnsDatum X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hc hA hPhi _ g hg
      (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R s) (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) (GlobalTheory.MatchCompare.isOrd_ordX R s) (GlobalTheory.MatchCompare.isOrd_ordX R (s + 1))
    refine _root_.GlobalTheory.DenseBox.support_invariance_of_dense k X.E ι hA.compl.dense _ _ ((W.T s R).Psi g) (psi_isLocallyConstant s R W g) (W.ϖ ^ cst.M) ?_ ?_ x₀ y
    · intro x y hne
      rw [toLoc_of_mat ι (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R s) x] at hne
      have hy : (fun a => ι (y a)) = fun a => ι ((fun i => y ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)) ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) a)) := by
        simp
      rw [hy, hrat _ (fun i => y ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i))] at hne
      have hs := hL.psiSupp al P _ _ (fun h => (right_ne_zero_of_mul hne) (by rw [h, map_zero]))
      rw [if_neg hnm] at hs
      rw [mem_box]
      intro a
      have h1 := hs ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) a)
      simp only [Equiv.symm_apply_apply] at h1
      have h' := (hint _).2 h1
      rw [map_mul, map_pow, ← hϖ] at h'
      have hϖ0 : ((W.ϖ : k) ^ cst.M) ≠ 0 := pow_ne_zero _ W.ϖ.ne_zero
      calc valuation k (ι (y a)) = valuation k (((W.ϖ : k) ^ cst.M)⁻¹ * ((W.ϖ : k) ^ cst.M * ι (y a))) := by
            rw [inv_mul_cancel_left₀ hϖ0]
        _ = valuation k (((W.ϖ : k) ^ cst.M)⁻¹) * valuation k ((W.ϖ : k) ^ cst.M * ι (y a)) := map_mul _ _ _
        _ ≤ valuation k (((W.ϖ : k) ^ cst.M)⁻¹) * 1 := by gcongr; exact (Valuation.mem_integer_iff _ _).1 h'
        _ = valuation k (((W.ϖ ^ cst.M)⁻¹ : kˣ) : k) := by simp
    · intro x y z hz
      rw [toLoc_of_mat ι (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R s) x]
      have hy : (fun a => ι (y a)) = fun a => ι ((fun i => y ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)) ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) a)) := by
        simp
      have hyz : (fun a => ι (y a + z a)) = fun a => ι (((fun i => y ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)) +
          (fun i => z ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i))) ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) a)) := by
        simp
      rw [hy, hyz, hrat, hrat _ (fun i => y ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)), hL.psiInv al P _ _ _ ?_]
      rw [if_neg hnm]
      intro i
      apply (hint _).1
      rw [mem_box] at hz
      have h1 := hz ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)
      rw [map_mul, map_inv₀, map_pow, ← hϖ, Valuation.mem_integer_iff, map_mul, map_inv₀]
      have hv0 : valuation k ((W.ϖ : k) ^ cst.M) ≠ 0 := by simp
      calc (valuation k ((W.ϖ : k) ^ cst.M))⁻¹ * valuation k (ι (z ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)))
          ≤ (valuation k ((W.ϖ : k) ^ cst.M))⁻¹ * valuation k ((W.ϖ : k) ^ cst.M) :=
            by gcongr; simpa using h1
        _ = 1 := inv_mul_cancel₀ hv0
  · intro e' e he' he y y' hy'
    simp only [Chain.xiTop]
    rw [GlobalTheory.T.lastStepTestFunction_eq_columnsTestFunction X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hA hPhi e' e he' he y,
      GlobalTheory.T.fourierTransform_cosetIndicator_eq_finiteColumnTransform X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hc hA (hL.depthQ P hnm) e' e he' he y y' hy', map_mul]

end GlobalTheory.TwLast
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwoLeOfLogPos
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt.RowsOfDesign

theorem two_le_of_log_pos' (n : ℕ) (h : 0 < Real.log (n : ℝ)) : 2 ≤ n := by
  by_contra hn
  have h1 : n = 0 ∨ n = 1 := by omega
  rcases h1 with rfl | rfl <;> simp at h

theorem two_le_rdE' (D : D7) (hq : 2 ≤ D.host.q) (hd : 2 ≤ D.host.d) : 2 ≤ D.host.rdE := by
  have h := (factRd D.R D.host).2.2
  have hf : (2 : ℝ) ≤ D.R.f := by
    have := D.host.four_le_n'
    have h2 : D.R.f = 2 * D.R.n := rfl
    exact_mod_cast (by omega : 2 ≤ D.R.f)
  have h0 : 0 ≤ D.host.rdE := by unfold Host.rdE; positivity
  nlinarith

theorem rows_of_design : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L), Formalism.MainNotions.SizesAt L → Real.log (4 * L.sc.x) ≤ L.sc.L →
    DelNat D → ThickUp L → HtRowsS L P.CYL := by
  intro D L P hS hx4 hDN hTU
  obtain ⟨-, -, -, -, hT, hCond, hQD, -, hLa, hRho, hBot, -, -, hEta, hNodes, -, hDel, -⟩ := hS
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hq2 : 2 ≤ D.host.q := two_le_of_log_pos' _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.1)
  have hd2 : 2 ≤ D.host.d := two_le_of_log_pos' _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.2.2.2.1)
  have hq' : (2 : ℝ) ≤ D.host.q := by exact_mod_cast hq2
  have hd' : (2 : ℝ) ≤ D.host.d := by exact_mod_cast hd2
  have hrd2 := two_le_rdE' D hq2 hd2
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := by have := D.host.four_le_n'; omega
    exact_mod_cast this
  have ht1 : (1 : ℝ) ≤ D.R.t := hT.1
  have hm1 : (1 : ℝ) ≤ D.R.m := by
    have : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    exact_mod_cast this
  have hk0 : (0 : ℝ) < D.R.k := by
    have : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hb1 : 1 ≤ L.sc.b := by unfold Scale.b; exact Real.one_le_exp (by linarith)
  refine ⟨⟨P⟩, ⟨?_, hQD.2.2.2.2.2.1, hx4⟩, ?_, ⟨?_, hEta.1, hEta.2.2.2.2.1, hDel.2.2.2.1, ?_⟩, hDN, hTU⟩
  ·
    have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
    have hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d :=
      Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have hc : D.host.rdE ≤ Formalism.MainNotions.szCond L := by
      refine hQD.2.2.2.2.2.2.2.trans ?_
      unfold Formalism.MainNotions.szCond
      have : (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤
          (D.host.QS : ℝ) / 2 * ((D.host.q : ℝ) * D.host.d) := mul_le_mul_of_nonneg_left hs (by positivity)
      have h0 : 0 ≤ (D.host.QS : ℝ) * ((D.host.q : ℝ) * D.host.d) := by positivity
      nlinarith
    have hc1 : 1 ≤ Formalism.MainNotions.szCond L := by linarith
    have h36 : Formalism.MainNotions.szCond L ≤ Formalism.MainNotions.szCond L ^ 36 := le_self_pow₀ hc1 (by norm_num)
    have h150 : Formalism.MainNotions.szCond L ^ 36 ≤ Formalism.MainNotions.szCond L ^ 36 * (D.R.t : ℝ) ^ 150 :=
      le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht1)
    have hsb : Real.sqrt L.sc.b ≤ L.sc.b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have hfin : D.host.rdE ≤ L.sc.b := hc.trans (h36.trans (h150.trans (hCond.trans hsb)))
    have := Real.log_le_log (by linarith) hfin
    rwa [show Real.log L.sc.b = L.sc.L by unfold Scale.b; exact Real.log_exp _] at this
  · intro i
    obtain ⟨Y, hY1, -, hY3, hY4⟩ := P.g_Y
    have hY0 : 0 < Y := lt_of_lt_of_le (by positivity) hY1
    have hg0 : (0 : ℝ) < D.host.g i := lt_of_lt_of_le hY0 (hY4 i).1
    have h1 := Real.log_le_log hg0 (hY4 i).2
    rw [Real.log_mul (by norm_num) hY0.ne'] at h1
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    linarith
  · have h1 := hNodes.2.2.2.1
    have h2 : L.etaSz / D.R.m ≤ L.etaSz := div_le_self L.etaSz_pos.le hm1
    have h3 : (0 : ℝ) ≤ D.R.t := by linarith
    linarith
  · intro t
    have h1 := hBot t
    have hLa0 : 0 ≤ L.LaG := le_trans (Real.rpow_pos_of_pos hx0 _).le hLa.1
    have h2 : 0 ≤ L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / D.R.k :=
      div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_pos_of_pos hx0 _).le (Real.log_nonneg hx1.le)) hLa0) hk0.le
    have h3 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by norm_num)
    have hb' : 0 ≤ L.sc.b' := by
      unfold Scale.b' Scale.a Scale.X' Scale.b
      positivity
    have hR : 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k +
        L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / D.R.k ≤ L.sc.x ^ (-2 : ℝ) := hRho
    have h4 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 := by
      have : 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
          4 * (Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
      have h0 : 0 ≤ Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k := by
        unfold Formalism.MainNotions.szNst Scale.delta1
        have := Real.rpow_pos_of_pos hx0 (-(L.sc.eps / 8))
        have := Real.rpow_pos_of_pos hx0 L.sc.eps
        positivity
      linarith
    have h5 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
        Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k * L.sc.b' := by ring
    rw [h5] at h1
    nlinarith

end GlobalTheory.CoreHt.RowsOfDesign
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedCharTrivialOnIntegralUnitsAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)

noncomputable section

namespace GlobalTheory.UnrPlDict

open GlobalTheory.IdemSupport

variable {D : D7}

theorem exists_glue_kill {χ : (AE D)ˣ →* Circle} {w : HeightOneSpectrum (𝓞 D.host.E)} (hu : UnrAt χ w)
    {e : AE D} (hd : GlobalTheory.IdemSupport.IsDelta (GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E) w e)
    (x : (AE D)ˣ) (h1 : finPart D (x : AE D) ∈ intAE D) (h2 : finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D) :
    ∃ y : (AE D)ˣ, (y : AE D) = e * (x : AE D) + (1 - e) ∧ χ y = 1 := by
  have hΦ : Comp D (GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E) := by
    obtain ⟨a, b, c, d, e⟩ := (GlobalTheory.LFun.EulerTie.comp_finComp (F := D.host.F) (E := D.host.E))
    exact ⟨a, b, c, d, e⟩
  have hm : GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E (x : AE D) w *
      GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E ((x⁻¹ : (AE D)ˣ) : AE D) w = 1 := by
    rw [← ev_mul, Units.mul_inv, map_one]
    try rfl
  let u : (w.adicCompletion D.host.E)ˣ :=
    ⟨_, _, hm, by rw [mul_comm]; exact hm⟩
  have hU : Formalism.L2.Host.IsUnitAt w u := by
    rw [GlobalTheory.LFun.EulerTie.isUnitAt_iff]
    exact ⟨(hΦ.int _).1 h1 w, (hΦ.int _).1 h2 w⟩
  refine ⟨GlobalTheory.LFun.locIdele D.host.F w u, (GlobalTheory.LFun.EulerTie.glue_eq_locIdele hd rfl).symm, ?_⟩
  have := congrArg (fun z : ℂˣ => (z : ℂ)) (hu u hU)
  exact Circle.ext this

theorem unrPl_of_unrAt : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)),
    w.under (𝓞 D.host.F) = v → ∀ χ : (AE D)ˣ →* Circle,
    (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → UnrAt χ w') → UnrPl w χ := by
  intro D v w hw χ hχ e f hp x hx h1 h2
  have hΦ : Comp D (GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E) := by
    obtain ⟨a, b, c, d, e⟩ := (GlobalTheory.LFun.EulerTie.comp_finComp (F := D.host.F) (E := D.host.E))
    exact ⟨a, b, c, d, e⟩
  have hd := (of_isPrimeIdem hΦ hp).1
  rcases hp with ⟨hi, rfl⟩ | ⟨rfl, -, -⟩
  · have hd' := delta_conj hΦ hd
    obtain ⟨y, hy, hy1⟩ := exists_glue_kill (hχ w hw) hd x h1 h2
    obtain ⟨z, hz, hz1⟩ := exists_glue_kill (hχ (cP w) ((under_cP w).trans hw)) hd' x h1 h2
    have ho : e * cA D e = 0 := hi.1.2.1
    have e1 : x = y * z := Units.ext (by
      rw [Units.val_mul, hy, hz]
      linear_combination (-1 : AE D) * hx - ((x : AE D) - 1) ^ 2 * ho)
    rw [e1, map_mul, hy1, hz1, one_mul]
  · obtain ⟨y, hy, hy1⟩ := exists_glue_kill (hχ w hw) hd x h1 h2
    have e1 : x = y := Units.ext (by rw [hy]; linear_combination (-1 : AE D) * hx)
    rw [e1, hy1]

end GlobalTheory.UnrPlDict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedHeckeVacuumLargerEqSmaller
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LFun (heckeVec)

namespace GlobalTheory.ChainOnto


open Formalism.UG GlobalTheory.Hk3 GlobalTheory.SphTheta in
theorem heckeVec_howe : GlobalTheory.Hk3.HoweUnram → ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∀ h' ∈ Hecke ℂ (KU σ n'), ∃ h ∈ Hecke ℂ (KU σ n), heckeVec (ω.comp (MonoidHom.inl _ _)) (KU σ n) h s = heckeVec (ω.comp (MonoidHom.inr _ _)) (KU σ n') h' s := by
  intro hH L _ _ _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s hS h' hh'
  have hU := hS.1.unr
  obtain ⟨-, hw2⟩ := hH L ϖ σ q δ n n' (antiG L n) (antiG L n') ψ M ρ ω hS.1 s hS.2.1 hS.2.2.1 hS.2.2.2
  have hK := P.isCommensurated_integral_unitary_of_unramified hU n
  have hK' := P.isCommensurated_integral_unitary_of_unramified hU n'
  have f1 : ∀ k ∈ KU σ n, ω (k, 1) s = s := fun k hk => hS.1.fix k 1 (mem_KU_iff.1 hk) (one_mem _) s hS.2.2.1
  have f2 : ∀ k ∈ KU σ n', ω (1, k) s = s := fun k hk => hS.1.fix 1 k (one_mem _) (mem_KU_iff.1 hk) s hS.2.2.1
  set w := heckeVec (ω.comp (MonoidHom.inr _ _)) (KU σ n') h' s with hw
  have w1 : ∀ k ∈ KU σ n, ω (k, 1) w = w := fun k hk => by
    rw [hw, GlobalTheory.LFun.map_heckeVec hK' hh' (ρ' := ω.comp (MonoidHom.inr _ _)) (ω (k, 1)) (fun g y => by
      show (ω (k, 1) * ω (1, g)) y = (ω (1, g) * ω (k, 1)) y
      rw [← map_mul, ← map_mul]
      simp), f1 k hk]
  have w2 : ∀ k ∈ KU σ n', ω (1, k) w = w := fun k hk => by
    have hs : s ∈ GlobalTheory.PRep.fixed (ω.comp (MonoidHom.inr _ _)) (KU σ n') := GlobalTheory.LGrp.mem_fixed.2 f2
    let e : GU σ n' ⧸ KU σ n' ≃ GU σ n' ⧸ KU σ n' := MulAction.toPerm k
    conv_rhs => rw [hw, GlobalTheory.LFun.heckeVec_eq_of_section hh'.1 hs (fun c => k * (e.symm c).out) (fun c => by
      rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
      exact e.apply_symm_apply c), ← finsum_comp_equiv e]
    rw [hw]
    refine ((ω (1, k)).toAddMonoidHom.map_finsum (GlobalTheory.LFun.finite_heckeVec hK' hh' _ s)).trans (finsum_congr fun c => ?_)
    have := hh'.1 ⟨k, hk⟩ 1 c.out
    simp only [OneMemClass.coe_one, mul_one] at this
    simp only [Equiv.symm_apply_apply, this, map_mul, LinearMap.toAddMonoidHom_coe, map_smul]
    rfl
  obtain ⟨h, hh, e⟩ := _root_.GlobalTheory.SphTheta.AvgHecke.exists_hecke_of_mem_span _ (KU σ n) hK M (ω.comp (MonoidHom.inl _ _)) s w f1 w1
    (hw2 w fun g hg => w2 g (mem_KU_iff.2 hg))
  exact ⟨h, hh, e⟩

end GlobalTheory.ChainOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpInjWOfAForm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory.Core.Rk.UpInjWProof

theorem upInjW_of_aForm : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ SF, GlobalTheory.Hk3.IsSF R SF → GlobalTheory.LiftRows.AForm R SF → GlobalTheory.LiftRows.UpInjW R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS hIrr SF hSF hA
  obtain ⟨a, ha, hAF⟩ := hA
  intro i t x hx h0
  obtain ⟨h, -, -, -, hspan, -⟩ := GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt R F hC hS hIrr SF hSF i

  have hpart : ∀ c, GlobalTheory.Hk3.Wcc R SF i c ≤ LinearMap.range (R.thG i t) := by
    intro c y hy
    by_cases hc : GlobalTheory.Hk3.Wcc R SF i c = ⊥
    · rw [hc] at hy
      rw [(Submodule.mem_bot ℂ).1 hy]
      exact Submodule.zero_mem _
    · obtain ⟨z, hz, hS'⟩ := hAF i t c hc
      obtain ⟨B, -, -, hzpos, -⟩ := hz
      have hne : ((a i * z : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (mul_pos (ha i) hzpos).ne'
      refine ⟨((a i * z : ℝ) : ℂ)⁻¹ • LinearMap.adjoint (R.thG i t) y, ?_⟩
      rw [map_smul, hS' y hy, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hxr : x ∈ LinearMap.range (R.thG i t) := by
    have : x ∈ LinearMap.range (GlobalTheory.Hk3.eH R i) := ⟨x, hx⟩
    rw [← hspan] at this
    exact (iSup_le hpart) this
  obtain ⟨v, rfl⟩ := hxr
  have h1 : ⟪R.thG i t v, R.thG i t v⟫_ℂ = 0 := by
    rw [← LinearMap.adjoint_inner_right, h0, inner_zero_right]
  exact inner_self_eq_zero.1 h1

end GlobalTheory.Core.Rk.UpInjWProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepSourceLineEqOppositeTargetLine
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.ConjLine

theorem weil_source_line_opposite : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E), L.rank = L'.rank → τᴴ ⬝ (L.gram ⬝ τ) = (((-1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram → ∀ (χz χ χ' : ((AE D)ˣ →* Circle)) (om : Om L S) (om' : Om S L'), IsWeilDatumO ψ L S χz χ om → IsWeilDatumO ψ S L' χ' χz⁻¹ om' → ∀ f, IsThetaFunO ψ L S f → IsThetaFunO ψ S L' (fun w => f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w))) ∧ ∀ h, om' (h, 1) (fun w => f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w))) = fun w => om (1, h) f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)) := by
  intro D ψ L L' S τ hrk hg χz χ χ' om om' hom hom' f hf
  have hstd : IsStdChar D ψ (-1) := hom.std
  have CA := _root_.GlobalTheory.WeilConjAdjoint.conjAdjoint_holds D ψ hstd S L'
  have h1 := (CA.conj_target χ' χz⁻¹ om' hom').1
  rw [inv_inv] at h1
  have hg' : τᴴ ⬝ (L.gram ⬝ τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • (GlobalTheory.ChiGrid.negSp L').gram := by
    rw [hg, GlobalTheory.ChiGrid.negSp_gram]; simp
  have H := _root_.GlobalTheory.ConjLine.conj_line D ψ L (GlobalTheory.ChiGrid.negSp L') S τ hrk hg' χz χ χ'⁻¹ om (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjTarget om') hom h1 f hf
  refine ⟨?_, ?_⟩
  · have := H.1
    exact (CA.theta_neg _).1.mp this
  · intro h
    have key : ∀ F : WO S L' → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjTarget om' (h, 1) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id F) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (om' (h, 1) F) := by
      intro F
      have e := GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cjEnd_cj (Equiv.refl (WO S L')) (om' (h, (GlobalTheory.ChiGrid.negGA L').symm 1)) F
      simpa [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjTarget] using e
    have H2 := H.2 h
    have K : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjTarget om' (h, 1) (fun w => star (f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)))) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (om' (h, 1) (fun w => f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)))) := key (fun w => f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)))
    rw [K] at H2
    funext w
    have := congrArg star (congrFun H2 w)
    simpa [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj] using this

end GlobalTheory.ConjLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittHyperbolicIsotropicColumnsAtRealPlace
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.AdelicU Formalism.UG

namespace GlobalTheory.IsoColReal

theorem compInf_incA {D : D7} (w : InfinitePlace D.host.F) (x : D.host.E) :
    compInf D.host.F D.host.E w (incA D x) = inclR (F := D.host.F) w.Completion x := by
  simp [compInf, incA, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]

theorem sigR_inclR_real {D : D7} (w : InfinitePlace D.host.F) (x : D.host.E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion D.sp.cm.sig (inclR (F := D.host.F) w.Completion x) = inclR (F := D.host.F) w.Completion (star x) := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  rfl

theorem isotropic_at_real : ∀ {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (w : InfinitePlace D.host.F), (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion D.sp.cm.sig) (Matrix.map d.jX (compInf D.host.F D.host.E w)) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion T.gram : Matrix (Fin r) (Fin T.rank) (TensorProduct D.host.F w.Completion D.host.E)) * Matrix.map d.jX (compInf D.host.F D.host.E w) = 0 := by
  intro D T T₀ r d w
  have hm : Matrix.map d.jX (compInf D.host.F D.host.E w) = d.e.map (inclR (F := D.host.F) w.Completion) := by
    ext i j
    simp [HypDec.jX, rat, compInf_incA]
  have hc : Formalism.UG.cT (sigR w.Completion D.sp.cm.sig) (d.e.map (inclR (F := D.host.F) w.Completion)) =
      (d.eᴴ).map (inclR (F := D.host.F) w.Completion) := by
    ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply, sigR_inclR_real]
  have hJ : JR w.Completion T.gram = T.gram.map (inclR (F := D.host.F) w.Completion) := rfl
  rw [hm, hc, hJ]
  have h0 := congrArg (fun M => M.map (inclR (F := D.host.F) w.Completion)) d.ee
  simp only [Matrix.map_mul, Matrix.map_zero, map_zero] at h0
  exact h0

end GlobalTheory.IsoColReal
end

