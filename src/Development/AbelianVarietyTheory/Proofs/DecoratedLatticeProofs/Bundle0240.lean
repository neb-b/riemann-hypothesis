module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0219
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0830
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0136
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralSplitPlaceAdelic
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

open Formalism.UG (IsUnifV qV)
open GlobalTheory.LFun (KGL IsSatVecGL eulerFac UnrAt LvTw)
open GlobalTheory.LFun (locChar IsSplitChart IsInertChart KGL UnrAt toCompl locMat IsFrameAt IsSatVecU eulerFac LvTw dv Fam)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.Doubling (ioH_mem_KFin)

namespace GlobalTheory.Core.Rk.IP


set_option maxHeartbeats 2000000 in
theorem localZetaOn_split : GlobalTheory.Published.UnramifiedDoublingGL →
    ∀ D : D7, LocalZetaOn D fun v => Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  intro hP D A L hL χ b hχ hb v hv hU μ hμH hK s hs φ hφ par c hc
  classical
  have hcm := isCMExt_host D
  have h2 : Module.finrank D.host.F D.host.E = 2 := hcm.2.2.1
  have hJ : IsHermND D.sp.cm.sig A.gram := GlobalTheory.Doubling.isHermND_gram A
  haveI : Submodule.IsFullLattice D.host.E L :=
    Formalism.IndefR.Fin.PDA.selfDual_isFullLattice A L hL
  have hd : IsSelfDualAt D.sp.cm.sig A.gram L v :=
    (SelfDual.forall_isSelfDualAt_iff (σ := D.sp.cm.sig) (GlobalTheory.Doubling.isHermND_gram A).2
      inferInstance).2
      (fun y => hL.2 y) v
  obtain ⟨w, h⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  have hc' := hc
  obtain ⟨⟨C, hC⟩, V, _, _, ρ, x, ℓ, hpar, -, hcx⟩ := hc
  obtain ⟨w', hne, hall, hN, hN', -⟩ := GlobalTheory.LFun.SplitChart.exists_conj_place hcm h hv
  have h' : w'.under (𝓞 D.host.F) = v := (hall w').2 (Or.inr rfl)
  obtain ⟨e, he, hsat⟩ : ∃ e, IsSplitChart D.sp.cm.sig A.gram L h e ∧
      IsSatVecGL w (ρ.comp e.symm.toMonoidHom) x (par w) := by
    rcases hpar w h with ⟨-, e, he, hsat⟩ | ⟨hw, -⟩
    · exact ⟨e, he, hsat⟩
    · exact absurd hv (GlobalTheory.LFun.not_isSplit_of_isInertAt hw)
  have hB' : par w' = (par w).map (·⁻¹) :=
    GlobalTheory.LFun.ConjPlace.eq_map_inv_of_isParamVec hcm hJ hd hne (hpar w h) (hpar w' h')
  have hm : GlobalTheory.LFun.val χ w * GlobalTheory.LFun.val χ w' = 1 :=
    GlobalTheory.LFun.ResEta.val_mul_val h2 ((GlobalTheory.LFun.resEta_iff χ _).1 hb) hne h h' (hU w h) (hU w' h')
  have hfix : ∀ k ∈ stabLoc D.sp.cm.sig A.gram L v, ρ k x = x :=
    GlobalTheory.LGrp.mem_fixed.1 (hpar w h).mem_fixed
  have hz1 : ‖(((GlobalTheory.LFun.val χ w)⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv, GlobalTheory.LFun.norm_val, inv_one]
  have hker := GlobalTheory.T.sphericalSection_graph_splitPlace D A L hL χ b hb v hv hU s φ hφ w h e he
  have hbd : ℓ x ≠ 0 → ∀ β ∈ par w, ‖(β : ℂ)‖ ≤ (qV D.host.E w : ℝ) ^ ((A.rank : ℝ) / 2) ∧
      ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV D.host.E w : ℝ) ^ ((A.rank : ℝ) / 2) := by
    intro h0 β hβ
    have hc1 : c 1 ≠ 0 := by rw [hcx, map_one, Module.End.one_apply]; exact h0
    have Hb := GlobalTheory.T.sphericalParameterBound_split_place D A L hL v hv par c hc' hc1
    refine ⟨(Hb w h).2 β hβ, ?_⟩
    have H2 := (Hb w' h').2 β⁻¹ (hB' ▸ Multiset.mem_map_of_mem _ hβ)
    have e2 : ((Ideal.absNorm w'.asIdeal : ℕ) : ℝ) = (qV D.host.E w : ℝ) := by
      rw [hN', ← hN]; rfl
    rwa [e2] at H2
  have hsum := GlobalTheory.ZetaGL.zeta_sum_GL_complex hP D.host.E w A.rank s (by have : (0 : ℝ) ≤ A.rank := Nat.cast_nonneg _; linarith)
    (GlobalTheory.LFun.val χ w)⁻¹ (fun g => φ (ioAt A v (e.symm g))) hz1 hker V (ρ.comp e.symm.toMonoidHom) x (par w) hsat ℓ
    ⟨C, fun g => by have := hC (e.symm g); rwa [hcx] at this⟩ hbd
  have hval := GlobalTheory.LocValSplit.LvTw_div_dv_split D.host.F D.host.E par (GlobalTheory.LFun.val χ) v w w' A.rank b s hv
    (GlobalTheory.LFun.isUnram_of_isSplit h2 hv) hne hall hN hN' hB' hm
  have hinv : ∀ y, ∀ k ∈ stabLoc D.sp.cm.sig A.gram L v,
      φ (ioAt A v (y * k)) * c (y * k) = φ (ioAt A v y) * c y := by
    intro y k hk
    have e1 : ioAt A v (y * k) = ioAt A v y * ioAt A v k := by
      unfold ioAt
      rw [← map_mul]
      simp
    have hk' : ioAt A v k ∈ KFin D.sp.cm.sig (dblSp A).gram L v :=
      (ioH_mem_KFin (gram_hdbl A)).2 ⟨hk, one_mem _⟩
    rw [e1, hφ.2.1 _ hk', hcx, hcx, map_mul, Module.End.mul_apply, hfix k hk]
  have hsum' := _root_.GlobalTheory.hasSum_quotient_transport _ _ e (stabLoc D.sp.cm.sig A.gram L v) (KGL w (n := A.rank)) he.2
    (fun y => φ (ioAt A v y) * c y) hinv _ (by
      refine hsum.congr_fun ?_
      intro a
      simp [hcx])
  obtain ⟨hI, hE⟩ := _root_.GlobalTheory.InertZeta.cosetIntegral_holds (Gv A v) μ (stabLoc D.sp.cm.sig A.gram L v)
    (GlobalTheory.AdelicU.isOpen_stabLoc _ _ _ v) hK (fun y => φ (ioAt A v y) * c y) _ hinv hsum'
  refine ⟨hI, ?_⟩
  rw [hE, hval, hcx, map_one, Module.End.one_apply]

end GlobalTheory.Core.Rk.IP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumRealEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealEqWeil

theorem weilDatum_realEq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT χS' χT' : (AE D)ˣ →* Circle) (om om' : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS' χT' om' → (∀ τ, ∃ e : ℚ, HasInfExp D χS τ e ∧ HasInfExp D χS' τ e) → (∀ τ, ∃ e : ℚ, HasInfExp D χT τ e ∧ HasInfExp D χT' τ e) → ∀ a ∈ GinfC S, ∀ b ∈ GinfC T, ∀ f, IsThetaFunO ψ S T f → om (a, b) f = om' (a, b) f := by
  intro D ψ S T χS χT χS' χT' om om' hW hW' hS hT a ha b hb f hf
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D

  have eS : ∀ τ, HasInfExp D (χS' * χS⁻¹) τ ((0 : ℤ) : ℚ) := fun τ => by
    obtain ⟨e, h1, h2⟩ := hS τ
    simpa using GlobalTheory.Chain.hasInfExp_div h2 h1
  have eT : ∀ τ, HasInfExp D (χT' * χT⁻¹) τ ((0 : ℤ) : ℚ) := fun τ => by
    obtain ⟨e, h1, h2⟩ := hT τ
    simpa using GlobalTheory.Chain.hasInfExp_div h2 h1
  obtain ⟨om'', hW'', hmv⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ hW.std S T χS χT (χS' * χS⁻¹) (χT' * χT⁻¹) om hW
    (GlobalTheory.WeilVacChar.hecke_mul_inv hW'.hecS hW.hecS) (GlobalTheory.WeilVacChar.hecke_mul_inv hW'.hecT hW.hecT)
    (GlobalTheory.WeilVacChar.resEta_mul_inv hW'.resS hW.resS) (GlobalTheory.WeilVacChar.resEta_mul_inv hW'.resT hW.resT)
  rw [GlobalTheory.WeilVacChar.mul_mul_inv_cancel, GlobalTheory.WeilVacChar.mul_mul_inv_cancel] at hW''
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ S (GlobalTheory.RealPairBound.gramAt_det_ne D S) a ha
  obtain ⟨y, hy, hyv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ T (GlobalTheory.RealPairBound.gramAt_det_ne D T) b hb
  have x1 : (χT' * χT⁻¹) x = 1 := by
    apply Circle.coe_injective
    rw [hxv _ (fun _ => 0) eT]
    simp
  have y1 : (χS' * χS⁻¹) y = 1 := by
    apply Circle.coe_injective
    rw [hyv _ (fun _ => 0) eS]
    simp
  have h1 := hmv a b x y hx hy
  rw [x1, y1, inv_one, one_mul, Circle.coe_one, one_smul] at h1
  rw [← h1]
  exact GlobalTheory.WeilUniq.weilDatum_unique D ψ hW.std S T χS' χT' om'' om' hW'' hW' (a, b) f hf

end GlobalTheory.RealEqWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorFirstCommutesHeisenbergDerivativeSec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DerivComm

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem exists_biBound (hψ : IsStdChar D ψ (-1)) {A S A' : HSp D} {C : WO A S → WO S A' → ℂ}
    (h : IsBiTheta ψ A S A' C) : ∃ B : ℝ, ∀ u v, ‖C u v‖ ≤ B := by
  obtain ⟨B, hB⟩ := GlobalTheory.WeilVacMove.exists_bound (f := GlobalTheory.BiTransfer.join
    (GlobalTheory.BiTransfer.sumDec A (GlobalTheory.ChiGrid.negSp A')) S C) hψ
    (GlobalTheory.BiTransfer.isThetaFunO_join (GlobalTheory.BiTransfer.sumDec A (GlobalTheory.ChiGrid.negSp A')) h)
  refine ⟨B, fun u v => ?_⟩
  have := hB (GlobalTheory.BiTransfer.inlH (GlobalTheory.BiTransfer.sumDec A (GlobalTheory.ChiGrid.negSp A')) S u +
    GlobalTheory.BiTransfer.inrH (GlobalTheory.BiTransfer.sumDec A (GlobalTheory.ChiGrid.negSp A')) S v)
  rwa [GlobalTheory.BiTransfer.join_inl_inr] at this

theorem om_dLine_right : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (χA χS χS' χA' : (AE D)ˣ →* Circle) (oma : Om A S) (omb : Om S A'), IsWeilDatumO ψ A S χA χS oma → IsWeilDatumO ψ S A' χS' χA' omb → BiAct D → ∀ G : WO A S → WO S A' → ℂ, IsBiTheta ψ A S A' G → ∀ M' : ℝ →+ WO S A', Continuous M' → (∀ s, (M' s).map (finPart D) = 0) → ∀ p u v, oma p (fun u' => GlobalTheory.WeilVacMove.dLine ψ S A' M' (G u') v) u = GlobalTheory.WeilVacMove.dLine ψ S A' M' (fun v' => oma p (fun u' => G u' v') u) v := by
  intro D ψ A S A' χA χS χS' χA' oma omb hA hB hBi G hG M' hM hM0 p u v
  have hψ : IsStdChar D ψ (-1) := hA.std
  set G' : WO A S → WO S A' → ℂ := fun u v => GlobalTheory.WeilVacMove.dLine ψ S A' M' (G u) v with hG'def
  have hG' : IsBiTheta ψ A S A' G' := (_root_.GlobalTheory.BiDeriv.isBiTheta_dLine D ψ hψ A S A' G hG).2 M' hM hM0
  set H : WO A S → WO S A' → ℂ := fun u v => oma p (fun u' => G u' v) u with hHdef
  have hH : IsBiTheta ψ A S A' H := (hBi ψ A S A' χA χS χS' χA' oma omb hA hB G hG).1 p
  set H' : WO A S → WO S A' → ℂ := fun u v => oma p (fun u' => G' u' v) u with hH'def
  have hH' : IsBiTheta ψ A S A' H' := (hBi ψ A S A' χA χS χS' χA' oma omb hA hB G' hG').1 p

  set c : ℝ → ℂ := fun s => ψ (symplOH S A' v (M' s)) with hcdef
  have hc : Continuous c := hψ.1.1.comp (GlobalTheory.WeilVacMove.continuous_symplOH S A' continuous_const hM)
  have hc1 : ∀ s, ‖c s‖ = 1 := fun s => hψ.1.2.1 _
  have hheis : ∀ (f : WO S A' → ℂ) s, heisO ψ S A' (M' s) f v = c s * f (v + M' s) := fun f s => rfl
  have hvm : Continuous fun s => v + M' s := continuous_const.add hM
  have hG'c : Continuous fun q : ℝ × WO A S => G' q.2 (v + M' q.1) :=
    hG'.cont.comp (f := fun q : ℝ × WO A S => (q.2, v + M' q.1)) (continuous_snd.prodMk (hvm.comp continuous_fst))
  have hH'c : Continuous fun q : ℝ × WO A S => H' q.2 (v + M' q.1) :=
    hH'.cont.comp (f := fun q : ℝ × WO A S => (q.2, v + M' q.1)) (continuous_snd.prodMk (hvm.comp continuous_fst))
  have hF0 : Continuous fun q : ℝ × WO A S => c q.1 * G' q.2 (v + M' q.1) := (hc.comp continuous_fst).mul hG'c
  have hoF0 : Continuous fun q : ℝ × WO A S => c q.1 * H' q.2 (v + M' q.1) := (hc.comp continuous_fst).mul hH'c

  set F : ℝ → WO A S → ℂ := fun s u' => c s * G' u' (v + M' s) with hFdef
  have hFth : ∀ s, IsThetaFunO ψ A S (F s) := fun s =>
    GlobalTheory.WeilVacMove.isTheta_smul (c s) (GlobalTheory.FrComb.slice_left hG' (v + M' s))
  have hFc : Continuous fun q : ℝ × WO A S => F q.1 q.2 := hF0
  obtain ⟨B1, hB1⟩ := exists_biBound hψ hG'
  have hFb : ∃ C : ℝ, ∀ a x, ‖F a x‖ ≤ C := ⟨B1, fun a x => by
    rw [hFdef, norm_mul, hc1, one_mul]; exact hB1 _ _⟩
  have hoF : ∀ s, oma p (F s) = fun u => c s * H' u (v + M' s) := by
    intro s
    have e : F s = c s • (fun u' => G' u' (v + M' s)) := rfl
    rw [e, map_smul]
    rfl
  have hoFc : Continuous fun q : ℝ × WO A S => oma p (F q.1) q.2 := by
    simp only [hoF]
    exact hoF0
  obtain ⟨B2, hB2⟩ := exists_biBound hψ hH'
  have hoFb : ∃ C : ℝ, ∀ a x, ‖oma p (F a) x‖ ≤ C := ⟨B2, fun a x => by
    rw [hoF, norm_mul, hc1, one_mul]; exact hB2 _ _⟩

  have hftc : ∀ u' t, ∫ s in (0 : ℝ)..t, F s u' = c t * G u' (v + M' t) - G u' v := by
    intro u' t
    have hd : ∀ s, HasDerivAt (fun t : ℝ => heisO ψ S A' (M' t) (G u') v)
        (heisO ψ S A' (M' s) (G' u') v) s := fun s =>
      GlobalTheory.WeilVacMove.hasDerivAt_line hψ hM hM0 (GlobalTheory.FrComb.slice_right hG u') v s
    have hcont : Continuous fun s => F s u' :=
      hF0.comp (f := fun s : ℝ => (s, u')) (continuous_id.prodMk continuous_const)
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t) (fun s _ => hd s)
      (hcont.intervalIntegrable _ _)
    change ∫ s in (0 : ℝ)..t, heisO ψ S A' (M' s) (G' u') v = _
    rw [this, hheis, hheis]
    simp only [hcdef, map_zero, add_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul]

  set φ : ℝ → ℂ := fun t => c t * H u (v + M' t) with hφdef
  set k : ℝ → ℂ := fun s => c s * H' u (v + M' s) with hkdef
  have hk : Continuous k := hoF0.comp (f := fun s : ℝ => (s, u)) (continuous_id.prodMk continuous_const)
  have hφint : ∀ t, 0 ≤ t → φ t = φ 0 + ∫ s in (0 : ℝ)..t, k s := by
    intro t ht
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) t)) :=
      isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
    have hth : IsThetaFunO ψ A S (fun x => ∫ a, F a x ∂(volume.restrict (Set.Ioc (0 : ℝ) t))) := by
      have e : (fun x => ∫ a, F a x ∂(volume.restrict (Set.Ioc (0 : ℝ) t))) =
          c t • (fun u' => G u' (v + M' t)) - (fun u' => G u' v) := by
        funext x
        rw [← intervalIntegral.integral_of_le ht, hftc]
        rfl
      rw [e]
      exact GlobalTheory.WeilVacMove.isTheta_sub (GlobalTheory.WeilVacMove.isTheta_smul _ (GlobalTheory.FrComb.slice_left hG _))
        (GlobalTheory.FrComb.slice_left hG v)
    have hcomm := _root_.GlobalTheory.CommIntBdd.om_integral_comm_bdd D ψ A S χA χS oma hA ℝ (volume.restrict (Set.Ioc (0 : ℝ) t)) F p hFth hFc hFb hoFc hoFb hth u
    have e1 : (fun y => ∫ a, F a y ∂(volume.restrict (Set.Ioc (0 : ℝ) t))) =
        c t • (fun u' => G u' (v + M' t)) - (fun u' => G u' v) := by
      funext x
      rw [← intervalIntegral.integral_of_le ht, hftc]
      rfl
    rw [e1, map_sub, map_smul] at hcomm
    have e2 : ∫ a, oma p (F a) u ∂(volume.restrict (Set.Ioc (0 : ℝ) t)) = ∫ s in (0 : ℝ)..t, k s := by
      rw [intervalIntegral.integral_of_le ht]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      show oma p (F s) u = k s
      rw [hoF]
    rw [e2] at hcomm
    have e3 : φ 0 = H u v := by
      rw [hφdef]; simp only [map_zero, add_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, hcdef, AddChar.map_zero_eq_one, one_mul]
    rw [e3, ← hcomm]
    simp only [hφdef, hHdef, LinearMap.sub_apply, Pi.sub_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    ring

  have h1 : HasDerivAt φ (GlobalTheory.WeilVacMove.dLine ψ S A' M' (H u) v) 0 :=
    (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ hM hM0 (GlobalTheory.FrComb.slice_right hH u)).1 v
  have h2 : HasDerivWithinAt φ (k 0) (Set.Ici 0) 0 := by
    have h3 : HasDerivAt (fun t => φ 0 + ∫ s in (0 : ℝ)..t, k s) (k 0) 0 :=
      ((hk.integral_hasStrictDerivAt 0 0).hasDerivAt).const_add _
    refine h3.hasDerivWithinAt.congr (fun t ht => hφint t ht) (hφint 0 le_rfl)
  have h4 := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ h1.hasDerivWithinAt h2
  have e4 : k 0 = H' u v := by
    simp only [hkdef, hcdef, map_zero, add_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul]
  rw [e4] at h4
  exact h4.symm

end GlobalTheory.DerivComm
end
end

