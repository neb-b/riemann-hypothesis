module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0285
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0316
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0394
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0310
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralDefiniteQuotientEqClassSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselAdaptedTranslateLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColMatch

theorem unitaryAdelicPointFiniteMatrix_inv_eq_of_mul_eq_one {D : D7} (a : GA D (D.sp.X 0)) (M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D))
    (hM : M * GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a = 1) :
    GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ = M := by
  have h1 : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a *
      GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ = 1 := by
    rw [← unitaryAdelicPointFiniteMatrix_base_space_mul, mul_inv_cancel, unitaryAdelicPointFiniteMatrix_base_space_one]
  calc _ = (M * GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a) *
        GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ := by rw [hM, one_mul]
    _ = M := by rw [mul_assoc, h1, mul_one]

end GlobalTheory.ColMatch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFourierJacobiUnfoldingHeisenbergExchange
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.HeisExchange

open GlobalTheory.Unf.ContrHeis

variable {D : D7}

theorem kappa_mul {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D) (g : GA D S)
    (w : WO S B'.L) : l.κ S (w ⬝ mt S g⁻¹) = mt S g ⬝ l.κ S w := by
  have hτ := (GlobalTheory.Unf.LinkGram.link_gram D ρ B B'.L B'.ζ B'.line l).1
  exact (GlobalTheory.LinkKappa.kappa_props D B.L B'.L S l.τ 1 hτ (l.κ S) (fun _ => rfl)).2.2.2.1 g w

theorem sympl_resT {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) (c d : WO S L) :
    symplOH S T ((o.resT S).symm (0, c)) ((o.resT S).symm (0, d)) = symplOH S L c d := by
  rw [o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_left, zero_add]

theorem sympl_resS {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) (c d : WO L S) :
    symplOH T S ((o.resS S).symm (0, c)) ((o.resS S).symm (0, d)) = symplOH L S c d := by
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_left, zero_add]

theorem act_resT {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) (g : GA D S) (a : GA D A) (c : WO S L) :
    actO S T g (o.emb (a, 1)) ((o.resT S).symm (0, c)) = (o.resT S).symm (0, c ⬝ mt S g⁻¹) := by
  rw [AddEquiv.eq_symm_apply, o.resT_actO, AddEquiv.apply_symm_apply]
  simp only [actO_eq, mt_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul]

theorem act_resS {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) (g : GA D S) (a : GA D A) (c : WO L S) :
    actO T S (o.emb (a, 1)) g ((o.resS S).symm (0, c)) = (o.resS S).symm (0, mt S g ⬝ c) := by
  rw [AddEquiv.eq_symm_apply, o.resS_actO, AddEquiv.apply_symm_apply]
  simp only [actO_eq, inv_one, mt_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one]

theorem quasi_resT {ψ : AddChar (AF D.host.F) ℂ} {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) {γ : WO S L} (hγ : γ ∈ ratMx D L.rank S.rank) (v : WO S L) :
    f ((o.resT S).symm (0, γ + v)) = ψ (-symplOH S L γ v) * f ((o.resT S).symm (0, v)) := by
  have r : (o.resT S).symm (0, γ) ∈ ratMx D T.rank S.rank := by
    refine (o.mem_ratL_resT S _).2 ?_
    simpa only [AddEquiv.apply_symm_apply, Prod.fst, Prod.snd] using (show (0 : WO S A) ∈ ratL A S ∧ γ ∈ ratL L S from ⟨zero_mem _, hγ⟩)
  obtain ⟨γ₂, hγ₂⟩ := r
  have q := hf.quasi γ₂ ((o.resT S).symm (0, v))
  have e : ratW T S γ₂ = (o.resT S).symm (0, γ) := hγ₂
  rwa [e, ← map_add, Prod.mk_add_mk, zero_add, sympl_resT] at q

theorem quasi_resS {ψ : AddChar (AF D.host.F) ℂ} {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) {f : WO T S → ℂ}
    (hf : IsThetaFunO ψ T S f) {γ : WO L S} (hγ : γ ∈ ratMx D S.rank L.rank) (v : WO L S) :
    f ((o.resS S).symm (0, γ + v)) = ψ (-symplOH L S γ v) * f ((o.resS S).symm (0, v)) := by
  have r : (o.resS S).symm (0, γ) ∈ ratMx D S.rank T.rank := by
    refine (o.mem_ratL_resS S _).2 ?_
    simpa only [AddEquiv.apply_symm_apply, Prod.fst, Prod.snd] using (show (0 : WO A S) ∈ ratL S A ∧ γ ∈ ratL S L from ⟨zero_mem _, hγ⟩)
  obtain ⟨γ₂, hγ₂⟩ := r
  have q := hf.quasi γ₂ ((o.resS S).symm (0, v))
  have e : ratW S T γ₂ = (o.resS S).symm (0, γ) := hγ₂
  rwa [e, ← map_add, Prod.mk_add_mk, zero_add, sympl_resS] at q

theorem integral_exchange {ψ : AddChar (AF D.host.F) ℂ} {S L : HSp D} (vL : VolM D L.rank S.rank) (T Y : WO S L → ℂ)
    (hT : ∀ γ ∈ ratMx D L.rank S.rank, ∀ v, T (γ + v) = ψ (-symplOH S L γ v) * T v)
    (hY : ∀ γ ∈ ratMx D L.rank S.rank, ∀ v, Y (γ + v) = ψ (symplOH S L γ v) * Y v) (x : WO S L) :
    ∫ v in vL.𝓕, T v * (ψ (-symplOH S L v x) * Y (v + x)) ∂vL.μ =
      ∫ v in vL.𝓕, ψ (symplOH S L v (-x)) * T (v + -x) * Y v ∂vL.μ := by
  have neg : ∀ v y : WO S L, symplOH S L v (-y) = -symplOH S L v y := by
    intro v y
    have h := GlobalTheory.OrientedHeis.symplOH_add_right (S := S) (T := L) v y (-y)
    rw [add_neg_cancel, symplOH_zero_right] at h
    linear_combination -h
  rw [← covolOne_integral_add vL.covol (fun v => ψ (symplOH S L v (-x)) * T (v + -x) * Y v) ?_ x]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    show _ = ψ (symplOH S L (v + x) (-x)) * T (v + x + -x) * Y (v + x)
    rw [add_neg_cancel_right, neg, GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_self, add_zero]
    ring
  · intro γ hγ a
    show ψ (symplOH S L (γ + a) (-x)) * T (γ + a + -x) * Y (γ + a) = ψ (symplOH S L a (-x)) * T (a + -x) * Y a
    rw [add_assoc, hT γ hγ, hY γ hγ, GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right,
      AddChar.map_add_eq_mul]
    have e : ψ (symplOH S L γ (-x)) * ψ (-(symplOH S L γ a + symplOH S L γ (-x))) * ψ (symplOH S L γ a) = 1 := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_zero_eq_one ψ]
      congr 1
      ring
    linear_combination (ψ (symplOH S L a (-x)) * T (a + -x) * Y a) * e

theorem besselFourierJacobi_unfolding_heisenberg_exchange : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (φ : GA D B.A → ℂ), IsContAut B.A φ →
    ∀ (Ξ : WO B.V₀ J.W₀ → ℂ) (Θ : WO J.W₀ B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ J.W₀ Ξ → IsThetaFunO ψ J.W₀ B'.V₀ Θ → ∀ w₀ : WO J.W₀ B'.L,
      hand0 s₁ s₂ l vL φ (heisO ψ B.V₀ J.W₀ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w₀)) Ξ) Θ =
        hand0 s₁ s₂ l vL φ Ξ (heisO ψ J.W₀ B'.V₀ ((B'.o.resT J.W₀).symm (0, -w₀)) Θ) := by
  intro D ψ σ B J B' s₁ s₂ l vL φ _ Ξ Θ hΞ hΘ w₀
  funext h₁
  refine integral_congr_ae (Filter.Eventually.of_forall fun h₀ => ?_)
  have key := integral_exchange (ψ := ψ) vL
    (fun v => s₂.om₀ (h₀, B'.o.emb (h₁, 1)) Θ ((B'.o.resT J.W₀).symm (0, v)))
    (fun v => liftA B.o s₁.om₀ B.vA φ Ξ h₀ (l.κ J.W₀ v))
    (fun γ hγ v => quasi_resT B'.o J.W₀ (s₂.weil₀.om_pres _ _ hΘ) hγ v)
    (fun γ hγ v => by
      simp only [liftA]
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      beta_reduce
      rw [kappa_add, quasi_resS B.o J.W₀ (s₁.weil₀.om_pres _ _ hΞ) (kappa_rat l _ γ hγ), symplOH_kappa, neg_neg]
      ring) (w₀ ⬝ mt J.W₀ h₀⁻¹)
  simp only [pairKer, contractT, thPair, handBF_eq, RCLike.star_def, Complex.conj_conj]
  refine Eq.trans ?_ (key.trans ?_)
  · refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    beta_reduce
    congr 1
    simp only [liftA]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    beta_reduce
    rw [s₁.weil₀.om_heis _ _ _ _ hΞ, act_resS, ← kappa_mul, heisO, sympl_resS, symplOH_kappa, ← map_add (f := _),
      Prod.mk_add_mk, add_zero, ← kappa_add]
    ring
  · refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    beta_reduce
    rw [s₂.weil₀.om_heis _ _ _ _ hΘ, act_resT, heisO, sympl_resT, ← map_add (f := _), Prod.mk_add_mk, add_zero, Matrix.neg_mul]

end GlobalTheory.FinPl.HeisExchange

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFrameEmbeddingLocalElementEqEmbeddedMatrix
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocGrp
open GlobalTheory.LocMod GlobalTheory.RootEx GlobalTheory.SplitWeil

theorem isLoc_embA : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (B : BesLev D ρ) (s : k) (FA : GlobalTheory.LocMod.Frame k B.A.rank n) (F : GlobalTheory.LocMod.Frame k B.V.rank (n ⊕ Fin c)), p.IsBesFrame B s FA F → ∀ (h : GA D B.A) (γ : GL n k), p.IsLoc FA h γ → p.IsLoc F (embA B.d B.o h) (GlobalTheory.RootEx.embX c γ) := by
  intro D k _ _ _ _ p n _ _ c ρ B s FA F hF h γ hh
  obtain ⟨rfl, h0, hX, hz, hY⟩ := hF
  rw [embA_apply]
  have eA : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jA) = B.d.j0 ⬝ B.o.jA ⬝ mt B.A h := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jA, Matrix.mul_assoc]
  have eB : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jB) = B.d.j0 ⬝ B.o.jB := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jB, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have rA : B.d.j0 ⬝ B.o.jA = rat (B.d.i₀ * B.o.iA) := (rat_mul _ _).symm
  have rB : B.d.j0 ⬝ B.o.jB = rat (B.d.i₀ * B.o.iB) := (rat_mul _ _).symm
  rw [rA] at eA
  rw [rB] at eB
  refine ⟨suppAt_wittLeviEmbedding B.d (suppAt_emb B.o hh.1),
    eq_embX F _ γ ((rat (B.d.i₀ * B.o.iA)).map p.π * FA.β) h0 (intertwine p eA hh) fun j => ?_⟩
  rcases lt_trichotomy j.val ρ with hj | hj | hj
  · exact fix_col (map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclX _)) _ ⟨j.val, hj⟩ (hX _ j rfl)
  · refine fix_vec (map_fix p eB) s (Witness.prH p ∘ B.ζ) fun r => (hz j hj r).trans (congrArg (s * ·) ?_)
    rw [vecB, Matrix.mulVec_mulVec]
    exact RingHom.map_mulVec (Witness.prH p) _ _ r
  · exact fix_col (map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclY _)) _ ⟨2 * ρ - j.val, by omega⟩ (hY _ j (by simp only; omega))

end GlobalTheory.LocGrp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiCombEqLOpROp
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section

namespace GlobalTheory.ProdLocInv

section Ops

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D)

def lOp (c : WO A S →₀ ℂ) (C : WO A S → WO S A' → ℂ) : WO A S → WO S A' → ℂ :=
  fun u v => comb ψ A S c (fun u' => C u' v) u

def rOp (c : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) : WO A S → WO S A' → ℂ :=
  fun u => comb ψ S A' c (C u)

theorem biComb_eq_lOp_rOp (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) :
    biComb ψ A S A' c c' C = lOp ψ A S A' c (rOp ψ A S A' c' C) := rfl

theorem lOp_rOp (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) :
    lOp ψ A S A' c (rOp ψ A S A' c' C) = rOp ψ A S A' c' (lOp ψ A S A' c C) := by
  funext u v
  simp only [lOp, rOp, comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem lOp_lOp (c d e : WO A S →₀ ℂ) (h : ∀ f, comb ψ A S e f = comb ψ A S c (comb ψ A S d f))
    (C : WO A S → WO S A' → ℂ) : lOp ψ A S A' c (lOp ψ A S A' d C) = lOp ψ A S A' e C := by
  funext u v
  exact congrFun (h fun u'' => C u'' v).symm u

theorem rOp_rOp (c d e : WO S A' →₀ ℂ) (h : ∀ f, comb ψ S A' e f = comb ψ S A' c (comb ψ S A' d f))
    (C : WO A S → WO S A' → ℂ) : rOp ψ A S A' c (rOp ψ A S A' d C) = rOp ψ A S A' e C := by
  funext u
  exact (h (C u)).symm

theorem lOp_comm (c d : WO A S →₀ ℂ) (h : ∀ f, comb ψ A S c (comb ψ A S d f) = comb ψ A S d (comb ψ A S c f))
    (C : WO A S → WO S A' → ℂ) : lOp ψ A S A' c (lOp ψ A S A' d C) = lOp ψ A S A' d (lOp ψ A S A' c C) := by
  funext u v
  exact congrFun (h fun u'' => C u'' v) u

theorem rOp_comm (c d : WO S A' →₀ ℂ) (h : ∀ f, comb ψ S A' c (comb ψ S A' d f) = comb ψ S A' d (comb ψ S A' c f))
    (C : WO A S → WO S A' → ℂ) : rOp ψ A S A' c (rOp ψ A S A' d C) = rOp ψ A S A' d (rOp ψ A S A' c C) := by
  funext u
  exact h (C u)

theorem biComb_comp (c d e : WO A S →₀ ℂ) (c' d' e' : WO S A' →₀ ℂ)
    (hl : ∀ f, comb ψ A S e f = comb ψ A S c (comb ψ A S d f))
    (hr : ∀ f, comb ψ S A' e' f = comb ψ S A' c' (comb ψ S A' d' f)) (C : WO A S → WO S A' → ℂ) :
    biComb ψ A S A' c c' (biComb ψ A S A' d d' C) = biComb ψ A S A' e e' C := by
  simp only [biComb_eq_lOp_rOp]
  rw [← lOp_rOp ψ A S A' d c', lOp_lOp ψ A S A' c d e hl, rOp_rOp ψ A S A' c' d' e' hr]

theorem biComb_comm (c d : WO A S →₀ ℂ) (c' d' : WO S A' →₀ ℂ)
    (hl : ∀ f, comb ψ A S c (comb ψ A S d f) = comb ψ A S d (comb ψ A S c f))
    (hr : ∀ f, comb ψ S A' c' (comb ψ S A' d' f) = comb ψ S A' d' (comb ψ S A' c' f)) (C : WO A S → WO S A' → ℂ) :
    biComb ψ A S A' c c' (biComb ψ A S A' d d' C) = biComb ψ A S A' d d' (biComb ψ A S A' c c' C) := by
  simp only [biComb_eq_lOp_rOp]
  rw [← lOp_rOp ψ A S A' d c', lOp_comm ψ A S A' c d hl, rOp_comm ψ A S A' c' d' hr, lOp_rOp ψ A S A' c d']

theorem comb_single_zero (T T' : HSp D) (f : WO T T' → ℂ) : comb ψ T T' (Finsupp.single 0 1) f = f := by
  classical
  funext w
  have h0 : symplOH T T' w 0 = 0 := by simp [symplOH, symplO, hO]
  simp [comb, heisO, h0]

end Ops

theorem comm_foldr {α ι : Type} (F : α → α) (H : ι → α → α) (l : List ι) (h : ∀ i ∈ l, ∀ x, F (H i x) = H i (F x))
    (x : α) : F (l.foldr H x) = l.foldr H (F x) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons]
    rw [h i (by simp), ih (fun j hj => h j (by simp [hj]))]

theorem foldr_mem {α ι : Type} (H : ι → α → α) (s : Set α) (l : List ι) (h : ∀ i ∈ l, ∀ x ∈ s, H i x ∈ s) (x : α)
    (hx : x ∈ s) : l.foldr H x ∈ s := by
  induction l with
  | nil => exact hx
  | cons i l ih => exact h i (by simp) _ (ih fun j hj => h j (by simp [hj]))

section Lists

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D)

theorem prodList {ι' : Type} (e₁ : ι' → WO A S →₀ ℂ) (e₂ : ι' → WO S A' →₀ ℂ) (l : List ι') :
    ∃ (e : WO A S →₀ ℂ) (e' : WO S A' →₀ ℂ),
      (∀ w ∈ e.support, w ∈ AddSubmonoid.closure (⋃ i ∈ l, ((e₁ i).support : Set (WO A S)))) ∧
      (∀ w ∈ e'.support, w ∈ AddSubmonoid.closure (⋃ i ∈ l, ((e₂ i).support : Set (WO S A')))) ∧
      ∀ C, biComb ψ A S A' e e' C = l.foldr (fun i C => biComb ψ A S A' (e₁ i) (e₂ i) C) C := by
  classical
  induction l with
  | nil =>
    refine ⟨Finsupp.single 0 1, Finsupp.single 0 1, ?_, ?_, fun C => ?_⟩
    · intro w hw
      rw [Finsupp.mem_support_single] at hw
      rw [hw.1]; exact zero_mem _
    · intro w hw
      rw [Finsupp.mem_support_single] at hw
      rw [hw.1]; exact zero_mem _
    · funext u v
      simp only [List.foldr_nil, biComb, comb_single_zero]
  | cons i l ih =>
    obtain ⟨e0, e0', hs, hs', hc⟩ := ih
    obtain ⟨c, hcs, hcf⟩ := (GlobalTheory.HeisComb.main D ψ A S).1 (e₁ i) e0
    obtain ⟨c', hcs', hcf'⟩ := (GlobalTheory.HeisComb.main D ψ S A').1 (e₂ i) e0'
    refine ⟨c, c', ?_, ?_, fun C => ?_⟩
    · intro w hw
      obtain ⟨x, hx, y, hy, rfl⟩ := hcs w hw
      refine add_mem (AddSubmonoid.subset_closure ?_) (AddSubmonoid.closure_mono ?_ (hs y hy))
      · simp only [Set.mem_iUnion]
        exact ⟨i, by simp, hx⟩
      · intro z hz
        simp only [Set.mem_iUnion] at hz ⊢
        obtain ⟨j, hj, hz⟩ := hz
        exact ⟨j, List.mem_cons_of_mem _ hj, hz⟩
    · intro w hw
      obtain ⟨x, hx, y, hy, rfl⟩ := hcs' w hw
      refine add_mem (AddSubmonoid.subset_closure ?_) (AddSubmonoid.closure_mono ?_ (hs' y hy))
      · simp only [Set.mem_iUnion]
        exact ⟨i, by simp, hx⟩
      · intro z hz
        simp only [Set.mem_iUnion] at hz ⊢
        obtain ⟨j, hj, hz⟩ := hz
        exact ⟨j, List.mem_cons_of_mem _ hj, hz⟩
    · rw [List.foldr_cons, ← hc]
      exact (biComb_comp ψ A S A' _ _ _ _ _ _ hcf hcf' C).symm

theorem keyList {ι' : Type} (e₁ g₁ : ι' → WO A S →₀ ℂ) (e₂ g₂ : ι' → WO S A' →₀ ℂ)
    (Cl Vl : ι' → Set (WO A S → WO S A' → ℂ)) (l : List ι') (hl : l.Nodup)
    (horth : ∀ i ∈ l, ∀ i' ∈ l, i ≠ i' → (∀ x, x ∈ (e₁ i).support ∨ x ∈ (g₁ i).support → ∀ y ∈ (e₁ i').support,
      symplO A S x y = 0) ∧ ∀ x, x ∈ (e₂ i).support ∨ x ∈ (g₂ i).support → ∀ y ∈ (e₂ i').support, symplO S A' x y = 0)
    (hloc : ∀ i ∈ l, ∀ C ∈ Cl i, biComb ψ A S A' (e₁ i) (e₂ i) C ∈ Vl i ∧
      C = biComb ψ A S A' (g₁ i) (g₂ i) (biComb ψ A S A' (e₁ i) (e₂ i) C))
    (hstab : ∀ i ∈ l, ∀ i' ∈ l, i ≠ i' → ∀ C ∈ Cl i, biComb ψ A S A' (e₁ i') (e₂ i') C ∈ Cl i)
    (C : WO A S → WO S A' → ℂ) (hC : ∀ i ∈ l, C ∈ Cl i) :
    (∀ i ∈ l, l.foldr (fun i C => biComb ψ A S A' (e₁ i) (e₂ i) C) C ∈ Vl i) ∧
      C = l.foldr (fun i C => biComb ψ A S A' (g₁ i) (g₂ i) C)
        (l.foldr (fun i C => biComb ψ A S A' (e₁ i) (e₂ i) C) C) := by
  induction l generalizing C with
  | nil => simp
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    have ih' := ih hl.2 (fun a ha b hb hab => horth a (by simp [ha]) b (by simp [hb]) hab)
      (fun a ha => hloc a (by simp [ha])) (fun a ha b hb hab => hstab a (by simp [ha]) b (by simp [hb]) hab)
    have hne : ∀ j ∈ l, i ≠ j := fun j hj h => hl.1 (h ▸ hj)
    have hEE : ∀ j ∈ l, ∀ Y, biComb ψ A S A' (e₁ i) (e₂ i) (biComb ψ A S A' (e₁ j) (e₂ j) Y) =
        biComb ψ A S A' (e₁ j) (e₂ j) (biComb ψ A S A' (e₁ i) (e₂ i) Y) := by
      intro j hj Y
      obtain ⟨h1, h2⟩ := horth i (by simp) j (by simp [hj]) (hne j hj)
      exact biComb_comm ψ A S A' _ _ _ _
        ((GlobalTheory.HeisComb.main D ψ A S).2.1 _ _ fun x hx y hy => h1 x (Or.inl hx) y hy)
        ((GlobalTheory.HeisComb.main D ψ S A').2.1 _ _ fun x hx y hy => h2 x (Or.inl hx) y hy) Y
    have hGE : ∀ j ∈ l, ∀ Y, biComb ψ A S A' (e₁ i) (e₂ i) (biComb ψ A S A' (g₁ j) (g₂ j) Y) =
        biComb ψ A S A' (g₁ j) (g₂ j) (biComb ψ A S A' (e₁ i) (e₂ i) Y) := by
      intro j hj Y
      obtain ⟨h1, h2⟩ := horth j (by simp [hj]) i (by simp) (hne j hj).symm
      exact (biComb_comm ψ A S A' _ _ _ _
        ((GlobalTheory.HeisComb.main D ψ A S).2.1 (g₁ j) (e₁ i) fun x hx y hy => h1 x (Or.inr hx) y hy)
        ((GlobalTheory.HeisComb.main D ψ S A').2.1 (g₂ j) (e₂ i) fun x hx y hy => h2 x (Or.inr hx) y hy) Y).symm
    have hEL := comm_foldr (biComb ψ A S A' (e₁ i) (e₂ i)) (fun j C => biComb ψ A S A' (e₁ j) (e₂ j) C) l hEE
    have hGL := comm_foldr (biComb ψ A S A' (e₁ i) (e₂ i)) (fun j C => biComb ψ A S A' (g₁ j) (g₂ j) C) l hGE
    have hCi : C ∈ Cl i := hC i (by simp)
    have hstabL : l.foldr (fun j C => biComb ψ A S A' (e₁ j) (e₂ j) C) C ∈ Cl i :=
      foldr_mem _ (Cl i) l (fun j hj Y hY => hstab i (by simp) j (by simp [hj]) (hne j hj) Y hY) C hCi
    obtain ⟨-, ihC⟩ := ih' C (fun j hj => hC j (by simp [hj]))
    obtain ⟨ihV2, -⟩ := ih' (biComb ψ A S A' (e₁ i) (e₂ i) C)
      (fun j hj => hstab j (by simp [hj]) i (by simp) (hne j hj).symm C (hC j (by simp [hj])))
    refine ⟨fun j hj => ?_, ?_⟩
    · simp only [List.foldr_cons]
      rcases List.mem_cons.1 hj with h | hj
      · subst h
        exact (hloc _ (by simp) _ hstabL).1
      · rw [hEL]
        exact ihV2 j hj
    · simp only [List.foldr_cons]
      rw [← hGL, ← ihC]
      exact (hloc i (by simp) C hCi).2

end Lists

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (ι' P : Type) (l : List ι') (X : P → WO A S → WO S A' → ℂ) (e₁ g₁ : ι' → WO A S →₀ ℂ) (e₂ g₂ : ι' → WO S A' →₀ ℂ) (Cl Vl : ι' → Set (WO A S → WO S A' → ℂ)), l.Nodup → (∀ i ∈ l, ∀ i' ∈ l, i ≠ i' → (∀ x, x ∈ (e₁ i).support ∨ x ∈ (g₁ i).support → ∀ y ∈ (e₁ i').support, symplO A S x y = 0) ∧ ∀ x, x ∈ (e₂ i).support ∨ x ∈ (g₂ i).support → ∀ y ∈ (e₂ i').support, symplO S A' x y = 0) → (∀ i ∈ l, ∀ p, X p ∈ Cl i) → (∀ i ∈ l, ∀ C ∈ Cl i, biComb ψ A S A' (e₁ i) (e₂ i) C ∈ Vl i ∧ C = biComb ψ A S A' (g₁ i) (g₂ i) (biComb ψ A S A' (e₁ i) (e₂ i) C)) → (∀ i ∈ l, ∀ i' ∈ l, i ≠ i' → ∀ C ∈ Cl i, biComb ψ A S A' (e₁ i') (e₂ i') C ∈ Cl i) → ∃ (e : WO A S →₀ ℂ) (e' : WO S A' →₀ ℂ), (∀ w ∈ e.support, w ∈ AddSubmonoid.closure (⋃ i ∈ l, ((e₁ i).support : Set (WO A S)))) ∧ (∀ w ∈ e'.support, w ∈ AddSubmonoid.closure (⋃ i ∈ l, ((e₂ i).support : Set (WO S A')))) ∧ ∀ p, (∀ i ∈ l, biComb ψ A S A' e e' (X p) ∈ Vl i) ∧ X p = l.foldr (fun i C => biComb ψ A S A' (g₁ i) (g₂ i) C) (biComb ψ A S A' e e' (X p)) := by
  intro D ψ A S A' ι' P l X e₁ g₁ e₂ g₂ Cl Vl hl horth hX hloc hstab
  obtain ⟨e, e', hs, hs', hc⟩ := prodList ψ A S A' e₁ e₂ l
  refine ⟨e, e', hs, hs', fun p => ?_⟩
  rw [hc]
  exact keyList ψ A S A' e₁ g₁ e₂ g₂ Cl Vl l hl horth hloc hstab (X p) fun i hi => hX i hi p

end GlobalTheory.ProdLocInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChOfDil
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

theorem chOf_dil : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ j, j ≤ B.R.m → ∀ (v : (I.atT l u a).vT) (s : ((I.atT l u a).Fv v)ˣ) (c : (I.chain l u a).cls j),
    A.chOf j ((I.fm l u a).dil j v s c) = A.chOf j c := by
  intro B X I hI hP l Z u a Ch A hA j hj v s c
  exact ((hA.reads j hj).key _ _).2 ⟨rfl, GlobalTheory.Mem.Col2.DiaChart.cosetIn_rep I l u a j v s c⟩

end GlobalTheory.AdForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColCond
section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.PhiOneVal

def ColCond {E : Type} [Field E] [NumberField E] {a b : ℕ} (P : HeightOneSpectrum (𝓞 E)) (t : 𝓞 E)
    (x : (Fin a → E) →ₗ[E] (Fin b → E)) : Prop :=
  ∀ r : Fin a, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ c : Fin b → 𝓞 E,
    (∀ q, algebraMap (𝓞 E) E (c q) = algebraMap (𝓞 E) E s * x (Pi.single r 1) q) ∧
    ∀ q : Fin b, q.1 + 1 = b → t * (c q - if r.1 + 1 = a then s else 0) ∈ P.asIdeal

end GlobalTheory.PhiOneVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyNhdsOneAdelicMatrixCongruentOneAtPrimeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_nhds_one_adelicMatrixCongruentOneAtPrime : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n N : ℕ) (P : HeightOneSpectrum (𝓞 E)), letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, GlobalTheory.TwU.CongAt P N u := by
  first | exact @GlobalTheory.TwU.NearOne.congAt_eventually_nhds_one | exact GlobalTheory.TwU.NearOne.congAt_eventually_nhds_one | (intros; apply GlobalTheory.TwU.NearOne.congAt_eventually_nhds_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharValueSplitPrimeNotRootOfUnityStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_value_split_prime_not_root_of_unity : ∀ (D : D7) (χ : (AE D)ˣ →* Circle), IsHeckeChar D χ → (∀ τ : D.what₂.Tau, ∃ a : ℚ, a ≠ 0 ∧ HasInfExp D χ τ a) → ∀ p : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.SplitsCompletely D p → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal → GlobalTheory.LFun.UnrAt χ w → ¬ IsOfFinOrder (GlobalTheory.LFun.val (F := D.host.F) χ w) := by
  first | exact @GlobalTheory.SplitValueAdelic.not_isOfFinOrder_val | exact GlobalTheory.SplitValueAdelic.not_isOfFinOrder_val | (intros; apply GlobalTheory.SplitValueAdelic.not_isOfFinOrder_val <;> assumption)
end

