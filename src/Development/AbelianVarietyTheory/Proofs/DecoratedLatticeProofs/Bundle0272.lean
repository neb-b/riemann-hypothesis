module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GramMatrixAdjoint
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0237
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0013
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0268
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0265
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRational
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondOnCommonRangeOfSecond
section
noncomputable section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SiegelWeilLitCompare

open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model
open GlobalTheory.IndefiniteRowSideFullHecke
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

variable {D : D7} {n : ℕ}

theorem summable_rat {θ : InfFam D} (hθ : IsInfFam θ) {m : ℕ} (φ : schwartzA θ m n) :
    Summable fun ξ : Matrix (Fin m) (Fin n) D.host.E => ‖φ.1 (ξ.map (incA D))‖ := by
  obtain ⟨N, hN⟩ := _root_.GlobalTheory.Unf.MajLoc.summable_bound D θ hθ m n
  obtain ⟨-, K, hK, hC⟩ := _root_.GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ m n φ.1
    (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ m n φ.1 φ.2)
  obtain ⟨C, hC⟩ := hC N
  obtain ⟨b, hb, hb'⟩ := hN K {0} hK isCompact_singleton
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => (hC _).trans ?_) (hb.mul_left |C|)
  have := hb' 0 rfl ξ
  rw [zero_add] at this
  exact mul_le_mul (le_abs_self C) this (GlobalTheory.Unf.maj_nonneg _ _ _ _) (abs_nonneg C)

theorem gramQ_adj {m : ℕ} {T : Matrix (Fin m) (Fin m) D.host.E} (hT : IsHermND D.sp.cm.sig T) (x y : Mx D m n) :
    adj (GramMatrixBlocks.gramQ T x y) = GramMatrixBlocks.gramQ T y x := by
  have h : adj (rat T : Mx D m m) = rat T := by
    ext i j
    exact (GlobalTheory.DualPairCheck.cA_incA _).trans (congrArg (incA D) (hT.1 i j))
  change adj ((adj x * (rat T : Mx D m m)) * y) = (adj y * (rat T : Mx D m m)) * x
  rw [adj_mul, adj_mul, adj_adj, h, Matrix.mul_assoc]

theorem selfDual_of_covolOne {m : ℕ} {T : Matrix (Fin m) (Fin m) D.host.E} (hT : IsHermND D.sp.cm.sig T)
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
    (hμ : IsCovolOne (ratMx D m n) μ 𝓕) : SelfDual μ (GramMatrixBlocks.pairing (n := n) T ψ) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.GramAnnih.ratMx_annihilator D m n T hT ψ hψ
  have hs : ∀ x y : Mx D m n, GramMatrixBlocks.pairing T ψ x y = GramMatrixBlocks.pairing T ψ y x := fun x y => by
    unfold GramMatrixBlocks.pairing GramMatrixBlocks.trA
    rw [← gramQ_adj hT x y, ← GlobalTheory.DualPairCheck.trace_cA (Matrix.trace (GramMatrixBlocks.gramQ T x y))]
    congr 2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, map_sum]
    rfl
  refine _root_.GlobalTheory.CovolumeOneSelfDual.selfDual_of_covolume_one _ (ratMx D m n) K hK hKc _ (fun y => ?_) hs (fun x x' y => ?_) (fun x y => hψ.2.1 _) h1 h2 μ 𝓕
    hμ.1 hμ.2.1 hμ.2.2
  · simp only [hs _ y]
    haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
    haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    have ht : Continuous (GramMatrixBlocks.trA (D := D)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
    exact hψ.1.comp (ht.comp (continuous_const.matrix_mul continuous_id).matrix_trace)
  · simp only [hs _ y]
    unfold GramMatrixBlocks.pairing GramMatrixBlocks.trA GramMatrixBlocks.gramQ GramMatrixBlocks.mmul
    rw [Matrix.mul_add, Matrix.trace_add, map_add (f := _), AddChar.map_add_eq_mul]

theorem hE_equivFun (V : HSp D) (x y : V.V) :
    hE D.sp.cm.sig V.gram (V.frame.equivFun x) (V.frame.equivFun y) = V.hT x y := by
  conv_rhs => rw [← V.frame.sum_equivFun x, ← V.frame.sum_equivFun y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, Formalism.UG.hform, HSpace.gram, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul,
    LinearMap.smul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  change star _ * _ * _ = _ * (star _ * _)
  ring

theorem wittIdx_eq (V : HSp D) : GramMatrixBlocks.wittIdx V.gram = Formalism.MainNotions.SchurIrreducible.wittIdx V := by
  unfold GramMatrixBlocks.wittIdx Formalism.MainNotions.SchurIrreducible.wittIdx
  refine congrArg sSup (Set.ext fun r => ⟨?_, ?_⟩)
  · rintro ⟨W, hW, hr⟩
    refine ⟨W.map V.frame.equivFun.symm.toLinearMap, (LinearEquiv.finrank_map_eq V.frame.equivFun.symm W).trans hr, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    refine (hE_equivFun V _ _).symm.trans ?_
    rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact hW x hx y hy
  · rintro ⟨W, hr, hW⟩
    refine ⟨W.map V.frame.equivFun.toLinearMap, ?_, (LinearEquiv.finrank_map_eq V.frame.equivFun W).trans hr⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact (hE_equivFun V x y).trans (hW x hx y hy)

variable {V : HSp D} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle}

theorem gramQ_eq (x y : Mx D V.rank n) : GramMatrixBlocks.gramQ V.gram x y = StdUnn.inner V x y := Matrix.mul_assoc _ _ _

theorem isWeilSch_unique {μ : Measure (Mx D V.rank n)} {ω ω' : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (h : IsWeilSch ψ χ θ V μ ω) (h' : IsWeilSch ψ χ θ V μ ω') : ω = ω' := by
  have := _root_.GlobalTheory.StdUnn.eq_top_of_levi_unip_weyl D n (ω.toHomUnits.eqLocus ω'.toHomUnits)
    (fun g a hg => Units.ext (LinearMap.ext fun Φ => Subtype.ext (funext fun x =>
      (h.levi g a hg Φ x).trans (h'.levi g a hg Φ x).symm)))
    (fun g b hg => Units.ext (LinearMap.ext fun Φ => Subtype.ext (funext fun x =>
      (h.unip g b hg Φ x).trans (h'.unip g b hg Φ x).symm)))
    (fun g hg => Units.ext (LinearMap.ext fun Φ => Subtype.ext (funext fun x =>
      (h.weyl g hg Φ x).trans (h'.weyl g hg Φ x).symm)))
  refine MonoidHom.ext fun g => ?_
  have hg : g ∈ ω.toHomUnits.eqLocus ω'.toHomUnits := this ▸ Subgroup.mem_top g
  exact congrArg Units.val hg

theorem leftInv_theta (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (Φ : schwartzA θ V.rank n) (g : G D n) :
    LeftInv (GQ V) (theta ω Φ g) := by
  intro γ hγ h
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin V.rank) D.host.E, mt V γ⁻¹ = rat u.1 := by
    obtain ⟨u, -, hu⟩ := (GQ V).inv_mem hγ
    exact ⟨u, (congrArg Units.val hu).symm⟩
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    ⟨fun ξ => u.1 * ξ, fun ξ => (u⁻¹).1 * ξ, fun ξ => by simp [← Matrix.mul_assoc], fun ξ => by simp [← Matrix.mul_assoc]⟩
  refine (tsum_congr fun ξ => ?_).trans (e.tsum_eq _)
  have : mt V (γ * h)⁻¹ = mt V h⁻¹ * mt V γ⁻¹ := by rw [mul_inv_rev]; rfl
  rw [this, hu, Matrix.mul_assoc, ← rat_mul]
  rfl

end GlobalTheory.SiegelWeilLitCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaMajorantAverageIdentity
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

noncomputable section

namespace GlobalTheory.IkedaK

variable {D : D7}

theorem bdd_om_compact {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : WRep S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {P : Set (GA D S × GA D T)}
    (hP : IsCompact P) : ∃ C : ℝ, ∀ p ∈ P, ∀ x, ‖om p f x‖ ≤ C := by
  obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  have hc := GlobalTheory.Unf.jointCont_all D ψ S T χS χT om hW f hf
  obtain ⟨C, hC⟩ := (hP.prod hK).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun p hp x => ?_⟩
  obtain ⟨γ, ⟨γ', rfl⟩, hx⟩ := hKc x
  have hq := (hW.om_pres p f hf).quasi γ' x
  have e : (((incA D).toAddMonoidHom.mapMatrix (m := Fin T.rank) (n := Fin S.rank)) γ') = ratW T S γ' := rfl
  rw [e] at hx
  have h1 := hW.std.1.2.1 (-(symplOH S T (ratW T S γ') x))
  have := hC (p, ratW T S γ' + x) ⟨hp, hx⟩
  simp only at this
  rw [hq, norm_mul, h1, one_mul] at this
  exact this

theorem om_mul_apply {S T : HSp D} (om : WRep S T) (p q : GA D S × GA D T) (f : WO S T → ℂ) :
    om p (om q f) = om (p * q) f := by
  rw [map_mul]; rfl

theorem weilRepUnitaryPair_left_apply_right {S T : HSp D} (om : WRep S T) (g : GA D S) (k : GA D T) (f : WO S T → ℂ) :
    om (g, 1) (om (1, k) f) = om (g, k) f := by
  rw [om_mul_apply]; congr 1; ext <;> simp

theorem weilRepUnitaryPair_right_apply_left {S T : HSp D} (om : WRep S T) (g : GA D S) (k : GA D T) (f : WO S T → ℂ) :
    om (1, k) (om (g, 1) f) = om (g, k) f := by
  rw [om_mul_apply]; congr 1; ext <;> simp

end GlobalTheory.IkedaK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionTrivialAfterFlagUnipotentFixing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

open GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction

variable {D : D7}

theorem form_mulVec_mulVec (S : HSp D) {k l : ℕ} (M : Mx D S.rank k) (N : Mx D S.rank l) (x : Fin k → AE D)
    (y : Fin l → AE D) :
    form S (M *ᵥ x) (N *ᵥ y) = (fun i => cA D (y i)) ⬝ᵥ ((adj N ⬝ (gA S ⬝ M)) *ᵥ x) := by
  have h : (fun i => cA D ((N *ᵥ y) i)) = (N.map (cA D)) *ᵥ fun i => cA D (y i) := by
    funext i
    exact RingHom.map_mulVec (cA D) N y i
  rw [form, h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec _ (adj N), adj,
    Matrix.vecMul_transpose]

theorem form_act_act (S : HSp D) (g : GA D S) (x y : VA S) : form S (act S g x) (act S g y) = form S x y := by
  rw [act, act, form_mulVec_mulVec, mt_unitary, form]

theorem act_vecX_of_mem_Nfix {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (j : Fin ρ) (a : Fin ρ → AE D)
    (ha : ∀ i, j < i → a i = 0) {m : GA D V} (hm : m ∈ Nfix d j) : act V m (vecX d a) = vecX d a := by
  have hm' : ∀ i : Fin ρ, i ≤ j → ∀ k, (mt V m ⬝ d.jX : Mx D V.rank ρ) k i = d.jX k i := by
    intro i hi k
    have h1 := (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hm).2) ⟨i, hi⟩
    have h2 := congrFun (congrFun (mem_fixer.1 h1) k) 0
    simpa [Matrix.mul_apply, Matrix.submatrix_apply] using h2
  rw [act, vecX, Matrix.mulVec_mulVec]
  funext k
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ≤ j
  · rw [hm' i hi k]
  · rw [ha i (not_le.1 hi), mul_zero, mul_zero]

theorem rat_mulVec_ratVec {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) (a : Fin n → D.host.E) :
    rat x *ᵥ ratVec a = ratVec (x *ᵥ a) := by
  funext i
  exact (RingHom.map_mulVec (incA D) x a i).symm

theorem transv_trivial_after_Nfix : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W), IsWeilDatumO ψ V W χV χW om → ∀ (vS : VolM D W.rank ρ) (Ψ : WO V W → ℂ), IsThetaFunO ψ V W Ψ → ∀ (j : Fin ρ) (a : Fin ρ → D.host.E), (∀ i, j < i → a i = 0) → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V) (u : GA D V), GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u → ∀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E, x *ᵥ a = 0 → ∀ m ∈ Nfix d j, ∀ n : GA D V, term ψ d W vS (om (m * u * n, 1) Ψ) x = term ψ d W vS (om (m * n, 1) Ψ) x := by
  intro D hD ψ V V₀ W ρ d χV χW om hW vS Ψ hΨ j a ha v u hv hu x hx m hm n
  obtain ⟨-, hConj, hTriv⟩ := _root_.GlobalTheory.Unf.transvLemma_of_descent D hD
  have ha' : ∀ i, j < i → ratVec a i = 0 := fun i hi => by simp [ratVec, ha i hi]
  have hmw : act V m (vecX d (ratVec a)) = vecX d (ratVec a) := act_vecX_of_mem_Nfix d j _ ha' hm
  have hc := hConj V V₀ ρ d (ratVec a) v hv u m hu
  rw [hmw] at hc
  have hv' : form V (vecX d (ratVec a)) (act V m v) = 0 := by
    rw [← hmw, form_act_act, hv]
  have hx' : rat x *ᵥ ratVec a = 0 := by
    rw [rat_mulVec_ratVec, hx]
    funext i
    simp [ratVec]
  have e : ((m * u * n, (1 : GA D W)) : GA D V × GA D W) = (m * u * m⁻¹, 1) * (m * n, 1) := by
    ext
    · simp [mul_assoc]
    · simp
  have key := hTriv V V₀ W ρ d ψ χV χW om hW vS.μ vS.𝓕 vS.covol a (act V m v) hv' (m * u * m⁻¹) hc (rat x) hx'
    (om (m * n, 1) Ψ) (hW.om_pres _ _ hΨ)
  rw [term, term, e, map_mul, Module.End.mul_apply]
  exact congrFun key 0

end GlobalTheory.Unf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldNormBaseTermTranslate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

theorem mt_mem_GQ_rat' {D : D7} (V : HSp D) {γ : GA D V} (hγ : γ ∈ GQ V) :
    ∃ M : Matrix (Fin V.rank) (Fin V.rank) D.host.E, mt V γ = rat M := by
  simp only [GQ, HFinIn, HFin, Subgroup.mem_subgroupOf] at hγ
  obtain ⟨u, -, hu⟩ := hγ
  exact ⟨u.1, (congrArg Units.val hu).symm⟩


set_option maxHeartbeats 1000000 in
theorem unfold_norm_base_term_translate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (vW : Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ (𝓐 : Set (flagN d)) (𝓑 : Set (GA D W)), IsFundamentalDomain ((GQ V ⊓ radX d).subgroupOf (flagN d)) 𝓐 vN.ν → IsFundamentalDomain (GQ W ⊓ Rgrp W (rat x₀) : Subgroup (GA D W)) 𝓑 vW.μ → ∀ g : GA D V, ∫⁻ p in 𝓐 ×ˢ 𝓑, ‖G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) x₀‖ₑ ∂(vN.ν.prod vW.μ) = ∫⁻ p in vN.𝓝 ×ˢ vW.𝓕, ∑' y : Orb W x₀, ‖G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1‖ₑ ∂(vN.ν.prod vW.μ) := by
  intro D ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vW x₀ hx G Φ hG hΦ 𝓐 𝓑 h𝓐 h𝓑 g
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨c1, c2, c3, c4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (GlobalTheory.MixPer.isIsoSub_e d)
  obtain ⟨hN1, hN2, hN3⟩ := vN.unit
  haveI := vW.haar
  haveI : SFinite vN.ν := inferInstance
  haveI : SFinite vW.μ := inferInstance
  obtain ⟨act, y₀, hy₀, hrel, htrans, hstab1, hstab2⟩ := GlobalTheory.T.flagUnitaryOrbitAction_transitive_with_stabilizer D V V₀ W ρ d x₀ hx
  letI := act
  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin W.rank) (Fin ρ) D.host.E) := inferInstanceAs (Countable (Fin _ → Fin _ → _))
  haveI hΓc : Countable ((NFlagQ V d.e).prod (GQ W)) := Function.Injective.countable
    (f := fun γ : (NFlagQ V d.e).prod (GQ W) => ((⟨γ.1.1, (Subgroup.mem_prod.1 γ.2).1⟩ : NFlagQ V d.e),
      (⟨γ.1.2, (Subgroup.mem_prod.1 γ.2).2⟩ : GQ W)))
    fun a b h => by
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      exact Subtype.ext (Prod.ext h.1 h.2)
  haveI : Countable ((MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀).map (Subgroup.subtype _)) :=
    (Subgroup.inclusion_injective (Subgroup.map_subtype_le (MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀))).countable
  have hF : IsFundamentalDomain ((NFlagQ V d.e).prod (GQ W)) (vN.𝓝 ×ˢ vW.𝓕) (vN.ν.prod vW.μ) := by
    refine _root_.GlobalTheory.isFundamentalDomain_prod_of_ker_image _ _ vN.ν vW.μ _ vN.𝓝 vW.𝓕 ?_ ?_
    · have hc : ((NFlagQ V d.e).prod (GQ W)).comap (MonoidHom.inl (flagN d) (GA D W)) = NFlagQ V d.e := by
        ext n
        simp only [Subgroup.mem_comap, MonoidHom.inl_apply, Subgroup.mem_prod, one_mem, and_true]
      rw [hc]; exact hN2
    · have hc : ((NFlagQ V d.e).prod (GQ W)).map (MonoidHom.snd (flagN d) (GA D W)) = GQ W := by
        ext h
        constructor
        · rintro ⟨p, hp, rfl⟩
          exact (Subgroup.mem_prod.1 hp).2
        · intro hh
          exact ⟨(1, h), Subgroup.mem_prod.2 ⟨one_mem _, hh⟩, rfl⟩
      rw [hc]; exact vW.fund
  have hG' : IsFundamentalDomain ((MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀).map (Subgroup.subtype _))
      (𝓐 ×ˢ 𝓑) (vN.ν.prod vW.μ) := by
    refine _root_.GlobalTheory.isFundamentalDomain_prod_of_ker_image _ _ vN.ν vW.μ _ 𝓐 𝓑 ?_ ?_
    · rw [hstab1]; exact h𝓐
    · rw [hstab2]; exact h𝓑
  have hmeas : ∀ y : Orb W x₀, Measurable fun p : flagN d × GA D W =>
      G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1 := by
    intro y
    have t4 := (_root_.GlobalTheory.Unf.TermLaw.term_laws D ψ V V₀ W ρ d χV χW om om' hω hω' vS Φ hΦ).2.2.2.1 y.1
    refine Continuous.measurable ?_
    refine (hG.2.1.comp continuous_snd).mul ?_
    exact t4.comp (((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk continuous_snd)
  have hinv : ∀ (γ : (NFlagQ V d.e).prod (GQ W)) (y : Orb W x₀) (p : flagN d × GA D W),
      G ((γ : flagN d × GA D W) * p).2 *
        term ψ d W vS (om (((γ : flagN d × GA D W) * p).1.1 * g, ((γ : flagN d × GA D W) * p).2) Φ) (γ • y).1 =
      G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1 := by
    intro γ y p
    have hmem := Subgroup.mem_prod.1 γ.2
    have hq1 : ((γ.1.1 : flagN d) : GA D V) ∈ GQ V := hmem.1
    have hq2 : γ.1.2 ∈ GQ W := hmem.2
    obtain ⟨M, hM⟩ := mt_mem_GQ_rat' W hq2
    have hΨ := hω.om_pres (p.1.1 * g, p.2) Φ hΦ
    have hΨ' := hω.om_pres (1, γ.1.2) _ hΨ
    have key : term ψ d W vS (om ((γ.1.1 : GA D V) * p.1.1 * g, γ.1.2 * p.2) Φ) (γ • y).1 =
        term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1 := by
      have hsplit : ((γ.1.1 : GA D V) * p.1.1 * g, γ.1.2 * p.2) =
          (((γ.1.1 : GA D V), 1) * ((1 : GA D V), γ.1.2)) * (p.1.1 * g, p.2) := by
        ext <;> simp [mul_assoc]
      rw [hsplit, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      have t2 := (_root_.GlobalTheory.Unf.TermLaw.term_laws D ψ V V₀ W ρ d χV χW om om' hω hω' vS _ hΨ').2.1
      have t3 := (_root_.GlobalTheory.Unf.TermLaw.term_laws D ψ V V₀ W ρ d χV χW om om' hω hω' vS _ hΨ).2.2.1
      have e1 : (rat (M * y.1) : Mx D W.rank ρ) = rat (γ • y).1 ⬝ blockX d (γ.1.1 : GA D V) := by
        rw [hrel γ y, hM, rat_mul]
      rw [t2 _ hq1 γ.1.1.2 (γ • y).1 (M * y.1) e1, t3 _ hq2 (M * y.1) y.1 (by rw [hM, rat_mul])]
    have hGG : G (γ.1.2 * p.2) = G p.2 := hG.1 _ hq2 p.2
    show G (γ.1.2 * p.2) *
        term ψ d W vS (om ((γ.1.1 : GA D V) * p.1.1 * g, γ.1.2 * p.2) Φ) (γ • y).1 = _
    exact congrArg₂ (· * ·) hGG key
  obtain ⟨hl, -⟩ := _root_.GlobalTheory.Unf.lintegral_integral_unfold_transitive (flagN d × GA D W) (vN.ν.prod vW.μ) ((NFlagQ V d.e).prod (GQ W)) (Orb W x₀) y₀ htrans
    (vN.𝓝 ×ˢ vW.𝓕) (𝓐 ×ˢ 𝓑) hF hG'
    (fun y p => G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1) hmeas hinv
  simp only [hy₀] at hl
  exact hl

end GlobalTheory.Unf
end
end

