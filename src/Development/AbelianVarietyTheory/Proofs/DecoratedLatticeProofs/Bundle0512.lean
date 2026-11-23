module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0308
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0511
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0510
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0507
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0280
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContractionOfVacuumCombinationsProof
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ContrOpProof

variable {D : D7}

theorem mxAt_mul_right {P : Pl D → Prop} {m n r : ℕ} {u : Mx D m n} (hu : MxAt P u) (N : Mx D n r) :
    MxAt P (u * N) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hu i k)

theorem mxAt_mul_left {P : Pl D → Prop} {m n r : ℕ} (N : Mx D r m) {u : Mx D m n} (hu : MxAt P u) :
    MxAt P (N * u) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hu k j)

theorem mxAt_sub {P : Pl D → Prop} {m n : ℕ} {u v : Mx D m n} (hu : MxAt P u) (hv : MxAt P v) : MxAt P (u - v) :=
  fun i j => by simpa only [Matrix.sub_apply] using Ideal.sub_mem _ (hu i j) (hv i j)

theorem mxAt_neg {P : Pl D → Prop} {m n : ℕ} {u : Mx D m n} (hu : MxAt P u) : MxAt P (-u) :=
  fun i j => by simpa only [Matrix.neg_apply] using Submodule.neg_mem _ (hu i j)

theorem fin_of_mxAt {P : Pl D → Prop} {m n : ℕ} {u : Mx D m n} (hu : MxAt P u) : u.map (infPart D) = 0 := by
  ext i j
  exact RingHom.mem_ker.1 (Ideal.mem_inf.1 (hu i j)).1

theorem contr_smul_left {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D)
    (vL : VolM D B'.L.rank S.rank) (c : ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ) :
    GlobalTheory.Unf.contr l S vL (c • f₁) f₂ = c • GlobalTheory.Unf.contr l S vL f₁ f₂ := by
  funext u v
  simp only [GlobalTheory.Unf.contr, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

theorem biComb_single (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (a : WO A S) (a' : WO S A') (r : ℂ)
    (C : WO A S → WO S A' → ℂ) (u : WO A S) (v : WO S A') :
    biComb ψ A S A' (Finsupp.single a r) (Finsupp.single a' 1) C u v =
      r * heisO ψ A S a (fun u' => heisO ψ S A' a' (C u') v) u := by
  by_cases hr : r = 0
  · subst hr
    simp [biComb, comb]
  · simp [biComb, comb, Finsupp.support_single_ne_zero _ hr]

theorem symplOH_self {S T : HSp D} (x : WO S T) : symplOH S T x (-x) = 0 := by
  have h1 := GlobalTheory.SplitScalar.symplOH_skew S T x x
  have h2 := GlobalTheory.SplitScalar.symplOH_add_self S T x x
  have h3 : symplO S T x x = 0 := by
    rw [← h2]
    nth_rewrite 2 [h1]
    exact add_neg_cancel _
  have h4 : symplOH S T x x = 0 := by rw [symplOH, h3, mul_zero]
  have h5 := GlobalTheory.SplitScalar.symplOH_add_right S T x x (-x)
  rw [add_neg_cancel, GlobalTheory.ContrComb.symplOH_zero_right, h4, zero_add] at h5
  exact h5.symm

theorem heisO_neg_cancel (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (x : WO S T) (g : WO S T → ℂ) :
    heisO ψ S T x (heisO ψ S T (-x) g) = g := by
  rw [GlobalTheory.SplitScalar.heisO_heisO, add_neg_cancel, GlobalTheory.SplitScalar.heisO_zero, symplOH_self, AddChar.map_zero_eq_one,
    one_smul]

theorem line_step {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ)
    (hf₁ : IsThetaFunO ψ B.V₀ S f₁) (hf₂ : IsThetaFunO ψ S B'.V₀ f₂) (y : WO B.L S) (w : WO S B'.L)
    (hy : ((B.o.resS S).symm (0, y)).map (infPart D) = 0)
    (hk : (-(B.o.resS S).symm (0, l.κ S w)).map (infPart D) = 0) (c : ℂ)
    (hc : GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y - l.κ S w)) f₁) f₂ =
      c • GlobalTheory.Unf.contr l S vL f₁ f₂) :
    GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁) (heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, w)) f₂) =
      (ψ (symplOH B.V₀ S (-(B.o.resS S).symm (0, l.κ S w)) ((B.o.resS S).symm (0, y))) * c) •
        GlobalTheory.Unf.contr l S vL f₁ f₂ := by
  have hth : IsThetaFunO ψ B.V₀ S (heisO ψ B.V₀ S (-(B.o.resS S).symm (0, l.κ S w))
      (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁)) :=
    GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 hk (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 hy hf₁)
  have hmove := _root_.GlobalTheory.Unf.ContrHeis.contr_heisO D ψ hψ ρ σ B B' l S vL _ f₂ hth hf₂ w
  rw [heisO_neg_cancel] at hmove
  rw [hmove, GlobalTheory.SplitScalar.heisO_heisO, contr_smul_left]
  have he : -(B.o.resS S).symm (0, l.κ S w) + (B.o.resS S).symm (0, y) = (B.o.resS S).symm (0, y - l.κ S w) := by
    rw [← map_neg, ← map_add (f := _), Prod.neg_mk, neg_zero, Prod.mk_add_mk, zero_add, neg_add_eq_sub]
  rw [he, hc, smul_smul]


open Classical in
def cstL (ψ : AddChar (AF D.host.F) ℂ) {ρ : ℕ} (B : BesLev D ρ) (S : HSp D) (M : Lat B.V₀) (LS : Lat S) (P : Pl D → Prop)
    (y : WO B.L S) : ℂ :=
  if (B.o.resS S).symm (0, y) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P then
    (if h : ∃ c : ℂ, ∀ f, Vac ψ B.V₀ S M LS P f → heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f = c • f
      then h.choose else 0) else 0

def coefL (ψ : AddChar (AF D.host.F) ℂ) {ρ σ : ℕ} (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D)
    (M : Lat B.V₀) (LS : Lat S) (P : Pl D → Prop) (u : WO B.V₀ S) (u' : WO S B'.V₀) : ℂ :=
  ψ (symplOH B.V₀ S (-(B.o.resS S).symm (0, l.κ S (B'.o.resT S u').2)) ((B.o.resS S).symm (0, (B.o.resS S u).2))) *
    cstL ψ B S M LS P ((B.o.resS S u).2 - l.κ S (B'.o.resT S u').2)

set_option maxHeartbeats 2000000 in
theorem contrOp : ∀ D : D7, ContrOp D := by
  intro D k _ _ _ _ ι p I P hP n' n'' _ _ _ _ ψ hψ ρ σ B B' l S vL α α₀ γ γ₀ M LS M' Λ Λ' hM hLS hM' hfr e₁ e₂ he₁ he₂
  classical
  have key : ∀ y, MxAt P y → ∀ f₁ f₂, Vac ψ B.V₀ S M LS P f₁ → Vac ψ S B'.V₀ LS M' P f₂ →
      GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁) f₂ =
        cstL ψ B S M LS P y • GlobalTheory.Unf.contr l S vL f₁ f₂ := by
    intro y hy f₁ f₂ h₁ h₂
    by_cases hin : (B.o.resS S).symm (0, y) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P
    · have hex : ∃ c : ℂ, ∀ f, Vac ψ B.V₀ S M LS P f → heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f = c • f := by
        obtain ⟨c, hc⟩ := _root_.GlobalTheory.HalfGenScalar.exists_scalar D ψ B.V₀ S _ _ (_root_.GlobalTheory.HalfGen.latO_le_closure_halves D k ι p I P hP B.V₀ S _ _ _ hin)
        exact ⟨c, fun f hf => hc f hf.2⟩
      have hcst : cstL ψ B S M LS P y = hex.choose := by simp only [cstL, if_pos hin, dif_pos hex]
      rw [hcst, hex.choose_spec f₁ h₁, contr_smul_left]
    · have hcst : cstL ψ B S M LS P y = 0 := by simp only [cstL, if_neg hin]
      rw [hcst, zero_smul, GlobalTheory.T.thetaLine_translate_off_lattice_kills_contraction D k ι p I P hP n' n'' ψ hψ ρ σ B B' l S vL α α₀ γ γ₀ M LS M' Λ Λ' hM hLS hM' hfr
        y hy hin f₁ f₂ h₁ h₂]
  let s := e₁.support ×ˢ e₂.support
  refine ⟨⟨s.card, fun i => Finsupp.single (B.o.resS S (s.equivFin.symm i).1.1).1
      (e₁ (s.equivFin.symm i).1.1 * e₂ (s.equivFin.symm i).1.2 *
        coefL ψ B B' l S M LS P (s.equivFin.symm i).1.1 (s.equivFin.symm i).1.2),
    fun i => Finsupp.single (B'.o.resT S (s.equivFin.symm i).1.2).1 1⟩, ?_, ?_⟩
  · intro i
    have hq := (s.equivFin.symm i).2
    rw [Finset.mem_product] at hq
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hx)]
      exact mxAt_mul_right (he₁ _ hq.1) _
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hx)]
      exact mxAt_mul_left _ (he₂ _ hq.2)
  intro f₁ f₂ h₁ h₂
  have hth₁ : ∀ u, MxAt P u → IsThetaFunO ψ B.V₀ S (heisO ψ B.V₀ S u f₁) := fun u hu =>
    GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (fin_of_mxAt hu) h₁.1
  have hth₂ : ∀ u, MxAt P u → IsThetaFunO ψ S B'.V₀ (heisO ψ S B'.V₀ u f₂) := fun u hu =>
    GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (fin_of_mxAt hu) h₂.1
  have hint : ∀ g₁ g₂, IsThetaFunO ψ B.V₀ S g₁ → IsThetaFunO ψ S B'.V₀ g₂ → ∀ (u : WO B.A S) (v : WO S B'.A),
      IntegrableOn (fun x => g₂ ((B'.o.resT S).symm (v, x)) * g₁ ((B.o.resS S).symm (u, l.κ S x))) vL.𝓕 vL.μ := by
    intro g₁ g₂ hg₁ hg₂ u v
    obtain ⟨hc, hp⟩ := _root_.GlobalTheory.ContrComb.integrand_cont_per D ρ σ B B' l S ψ g₁ g₂ hg₁ hg₂
    exact (GlobalTheory.Unf.ParCont.parCont D B'.L.rank S.rank vL (WO B.A S × WO S B'.A)
      (fun x q => g₂ ((B'.o.resT S).symm (q.2, x)) * g₁ ((B.o.resS S).symm (q.1, l.κ S x))) hc
      (fun γ' hγ x q => hp γ' hγ x q.1 q.2)).1 (u, v)
  have hLR : ∀ (g₁ : WO B.V₀ S → ℂ) (g₂ : WO S B'.V₀ → ℂ) (b : WO B.A S) (b' : WO S B'.A),
      GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (b, 0)) g₁) (heisO ψ S B'.V₀ ((B'.o.resT S).symm (b', 0)) g₂) =
        fun u₀ v₀ => heisO ψ B.A S b (fun u'' => heisO ψ S B'.A b' (GlobalTheory.Unf.contr l S vL g₁ g₂ u'') v₀) u₀ := by
    intro g₁ g₂ b b'
    funext u₀ v₀
    rw [← GlobalTheory.ContrComb.heis_left ψ l S vL g₁ _ b u₀ v₀]
    congr 1
    funext u''
    rw [GlobalTheory.ContrComb.heis_right]
  have heL : ∀ z : WO B.L S, MxAt P z → MxAt P ((B.o.resS S).symm (0, z)) := by
    intro z hz
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add]
    exact mxAt_mul_right hz _
  have pair : ∀ u, MxAt P u → ∀ u', MxAt P u' →
      GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S u f₁) (heisO ψ S B'.V₀ u' f₂) =
        fun u₀ v₀ => coefL ψ B B' l S M LS P u u' * heisO ψ B.A S (B.o.resS S u).1
          (fun u'' => heisO ψ S B'.A (B'.o.resT S u').1 (GlobalTheory.Unf.contr l S vL f₁ f₂ u'') v₀) u₀ := by
    intro u hu u' hu'
    have hsL : u = (B.o.resS S).symm ((B.o.resS S u).1, 0) + (B.o.resS S).symm (0, (B.o.resS S u).2) := by
      rw [← map_add (f := _), Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta, AddEquiv.symm_apply_apply]
    have hsR : u' = (B'.o.resT S).symm ((B'.o.resT S u').1, 0) + (B'.o.resT S).symm (0, (B'.o.resT S u').2) := by
      rw [← map_add (f := _), Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta, AddEquiv.symm_apply_apply]
    have hoL : symplO B.V₀ S ((B.o.resS S).symm ((B.o.resS S u).1, 0)) ((B.o.resS S).symm (0, (B.o.resS S u).2)) = 0 := by
      rw [B.o.symplO_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.SplitScalar.symplO_zero_right,
        GlobalTheory.SplitScalar.symplO_zero_left, add_zero]
    have hoR : symplO S B'.V₀ ((B'.o.resT S).symm ((B'.o.resT S u').1, 0)) ((B'.o.resT S).symm (0, (B'.o.resT S u').2)) = 0 := by
      rw [B'.o.symplO_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.SplitScalar.symplO_zero_right,
        GlobalTheory.SplitScalar.symplO_zero_left, add_zero]
    have hy : MxAt P (B.o.resS S u).2 := mxAt_mul_right hu _
    have hw : MxAt P (B'.o.resT S u').2 := mxAt_mul_left _ hu'
    have hkw : MxAt P (l.κ S (B'.o.resT S u').2) := _root_.GlobalTheory.LinkKapMx.mxAt_linkKappa D ρ B B'.L B'.ζ l S P _ hw
    have hline := line_step ψ hψ l S vL f₁ f₂ h₁.1 h₂.1 (B.o.resS S u).2 (B'.o.resT S u').2 (fin_of_mxAt (heL _ hy))
      (fin_of_mxAt (mxAt_neg (heL _ hkw))) _ (key _ (mxAt_sub hy hkw) f₁ f₂ h₁ h₂)
    have e1 : heisO ψ B.V₀ S u f₁ = heisO ψ B.V₀ S ((B.o.resS S).symm ((B.o.resS S u).1, 0))
        (heisO ψ B.V₀ S ((B.o.resS S).symm (0, (B.o.resS S u).2)) f₁) := by
      rw [← GlobalTheory.SplitScalar.heisO_add_of_orth ψ _ _ hoL, ← hsL]
    have e2 : heisO ψ S B'.V₀ u' f₂ = heisO ψ S B'.V₀ ((B'.o.resT S).symm ((B'.o.resT S u').1, 0))
        (heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, (B'.o.resT S u').2)) f₂) := by
      rw [← GlobalTheory.SplitScalar.heisO_add_of_orth ψ _ _ hoR, ← hsR]
    rw [e1, e2, hLR, hline]
    funext u₀ v₀
    simp only [coefL, heisO, Pi.smul_apply, smul_eq_mul]
    ring
  funext u₀ v₀
  have hexp : GlobalTheory.Unf.contr l S vL (comb ψ _ _ e₁ f₁) (comb ψ _ _ e₂ f₂) u₀ v₀ =
      ∑ u' ∈ e₂.support, ∑ u ∈ e₁.support, (e₂ u' * e₁ u) *
        GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S u f₁) (heisO ψ S B'.V₀ u' f₂) u₀ v₀ := by
    simp only [GlobalTheory.Unf.contr, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul_sum]
    have hI : ∀ u' ∈ e₂.support, ∀ u ∈ e₁.support, IntegrableOn (fun x =>
        e₂ u' * heisO ψ S B'.V₀ u' f₂ ((B'.o.resT S).symm (v₀, x)) *
          (e₁ u * heisO ψ B.V₀ S u f₁ ((B.o.resS S).symm (u₀, l.κ S x)))) vL.𝓕 vL.μ := by
      intro u' hu' u hu
      refine Integrable.congr ((hint _ _ (hth₁ u (he₁ u hu)) (hth₂ u' (he₂ u' hu')) u₀ v₀).const_mul (e₂ u' * e₁ u))
        (ae_of_all _ fun x => ?_)
      simp only
      ring
    rw [integral_finsetSum _ fun u' hu' => integrable_finsetSum _ fun u hu => hI u' hu' u hu]
    refine Finset.sum_congr rfl fun u' hu' => ?_
    rw [integral_finsetSum _ fun u hu => hI u' hu' u hu]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hexp, Finset.sum_comm]
  simp only [BiOp.app, Finset.sum_apply]
  rw [Equiv.sum_comp s.equivFin.symm (fun q : s => biComb ψ B.A S B'.A
      (Finsupp.single (B.o.resS S q.1.1).1 (e₁ q.1.1 * e₂ q.1.2 * coefL ψ B B' l S M LS P q.1.1 q.1.2))
      (Finsupp.single (B'.o.resT S q.1.2).1 1) (GlobalTheory.Unf.contr l S vL f₁ f₂) u₀ v₀),
    Finset.sum_coe_sort s (fun q => biComb ψ B.A S B'.A
      (Finsupp.single (B.o.resS S q.1).1 (e₁ q.1 * e₂ q.2 * coefL ψ B B' l S M LS P q.1 q.2))
      (Finsupp.single (B'.o.resT S q.2).1 1) (GlobalTheory.Unf.contr l S vL f₁ f₂) u₀ v₀), Finset.sum_product]
  refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun u' hu' => ?_
  rw [pair u (he₁ u hu) u' (he₂ u' hu'), biComb_single]
  ring

end GlobalTheory.FinPl.ContrOpProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeOperatorsActRamifiedColumnsVanishing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms NumberField Matrix GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.AdForm ValuativeRel IsLocalRing

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sOp_zero_fun {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n) (P : Pair k n) (q : Unif k)
    (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) : sOp β P q χ ε 0 = 0 := by
  have h0 : formAt β P 0 = 0 := by
    funext P₁
    simp [formAt]
  simp [sOp, h0]

theorem foldr_sOp_zero_fun {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ι : Type} {p : ι → SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n)
    (P : ι → Pair k n) (q : Unif k) (χ : ι → AddChar 𝓀[k] ℂ) (η : ι → 𝓀[k]ˣ) (J : List ι) :
    J.foldr (fun i f => sOp (β i) (P i) q (χ i) (η i) f) 0 = 0 := by
  induction J with
  | nil => rfl
  | cons i J ih => simp only [List.foldr_cons, ih]; exact sOp_zero_fun _ _ _ _ _

theorem infM_one_eq {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (τ : D.what₂.Tau) :
    infM θ V hn 1 τ = 1 := by
  simp [infM, Formalism.L2.Theta.mt, Datum.compAt]

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch : ℕ → Type}

theorem TwDat.rd_eq_zero_of_vanish (A : TwDat I l Z u a Ch) (θ : InfFam (I.rec7 l Z)) (j : ℕ) (hj : j ≤ B.R.m) (b : Ch j)
    (φ : ColT I l u a j) (hφ : ∀ c, A.chOf j c = b → φ c = 0) (y : (I.chain l u a).Y j) : A.rd θ j hj b φ y = 0 := by
  funext g
  unfold TwDat.rd rdS
  split_ifs with h
  · simp [hφ _ h.choose.1.2, atFr]
    intro _
    rfl
  · rfl

theorem twS_ramL : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch₀ Ch : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ιc : ∀ j, Ch j → Ch₀ j), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, GlobalTheory.FinPl.Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank)) (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)), StdT I l Z u p β Q L → ∀ (J : List ι) (q : Unif k) (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1), ∃ S : ∀ j, (ι → 𝓀[k]ˣ) → ColT I l u a j → ColT I l u a j, ∀ j (hj : j ≤ B.R.m) φ, A.RamL ιc j φ → (∀ b y, IsContAut _ (A.rd θ j hj b φ y) ∧ ∀ i, GlobalTheory.FinPl.RamAt (β j i) (Q j i) (A.rd θ j hj b φ y)) ∧ ∀ η, A.RamL ιc j (S j η φ) ∧ ∀ b y, A.rd θ j hj b (S j η φ) y = J.foldr (fun i f => sOp (β j i) (Q j i) q (resChar (χ i) (hχ i) q) (η i) f) (A.rd θ j hj b φ y) := by
  intro B X I hOk hPins l Z u a Ch₀ Ch A ιc hA θ hθ k _ _ _ _ ι p β Q L hStd J q χ hχ
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.AdForm.TwSProof.twS I hOk hPins l Z u a Ch₀ A hA θ hθ k ι p β Q L hStd J q χ hχ
  refine ⟨S, fun j hj φ hφ => ?_⟩
  obtain ⟨h1, h2⟩ := hS j hj φ hφ.1
  refine ⟨h1, fun η => ⟨⟨(h2 η).1, ?_⟩, (h2 η).2⟩⟩
  intro c hc
  have hrd0 : ∀ y, A.rd θ j hj (A.chOf j c) φ y = 0 := fun y =>
    TwDat.rd_eq_zero_of_vanish A θ j hj _ φ (fun c' hc' => hφ.2 c' (by rw [hc']; exact hc)) y
  have hrdS : ∀ y, A.rd θ j hj (A.chOf j c) (S j η φ) y = 0 := by
    intro y
    rw [(h2 η).2, hrd0]
    exact foldr_sOp_zero_fun _ _ _ _ _ _
  funext y'
  have hTr : IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) 1) ⟨y'.1, y'.2⟩ ⟨y'.1, y'.2⟩ := by
    intro τ
    rw [infM_one_eq]
    first
    | exact (Matrix.one_mul _).symm
    | exact (one_mul _).symm
    | exact (one_smul _ _).symm
    | (show _ = _; simp [Matrix.one_mul])
  have key := (GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple I hOk hPins l Z u a Ch₀ A hA θ hθ j hj (S j η φ) (h2 η).1.1).2 (A.chOf j c) y' 1 (one_mem _)
    ⟨c, rfl⟩ 1 (one_mem _) 1 y' hTr
  rw [hrdS] at key
  simpa using key.symm

end GlobalTheory.AdForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTwistPlaceLawsOfRootOfUnityRescaling
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QTw

theorem laws_of_pin_resc : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → t.Is → v.Is → WeilOK (t := t) v → QPinU v w → QLaw v w ∧ QLast v w ∧ QFin v w :=
  fun D c v t w hc ht hv hW h =>
    GlobalTheory.QTw.RescTest.laws_of_qpinU v (fun w₀ h₀ =>
      ⟨GlobalTheory.T.seeSawIteratedIntegralLaw_at_twist_of_factorisation D c v t w₀ hc ht hv hW h₀, GlobalTheory.T.seeSawIteratedIntegralLawLastSteps_of_localFactorisation D c v t w₀ hc ht hv hW h₀, GlobalTheory.T.seeSawFiniteCells_at_twistPlaces_of_localFactorisation D c v t w₀ hc ht hv hW h₀⟩) w h

end GlobalTheory.QTw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallVectorCoefficientVanishesOffPrincipalLevel
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

open Classical

namespace GlobalTheory.Core.Rk.Exh.SmallSupp

theorem selfDual_frameLat {D : D7} (V : HSp D) : IsSelfDualC V (frameLat V) := by
  have h : frameLat V = GlobalTheory.PlaceModel.latFrame V :=
    Submodule.ext fun y => (mem_frameLat V y).trans (GlobalTheory.PlaceModel.mem_latFrame V y).symm
  rw [h]
  exact GlobalTheory.PlaceModel.isSelfDualC_latFrame V

theorem wcoef_eq_zero_off_prin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sA : RealMat A) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → A.rank ≤ H.rank → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Places A β Z → ∀ (βH : GL (Fin H.rank) (Formalism.IndefR.Lev.EAf D)) (f₀ f : WO A H → ℂ), Formalism.L2.DIV.IsFrame βH (frameLat H) → IsStepVecOf ψ θ A H sA sH (frameLat A) (frameLat H) β βH (prinDat A Z) (fun _ => 1) ∅ (fun _ => 1) f₀ f → IsThetaFunO ψ A H f → ∀ ν 𝓕, IsCovolOne (ratL H A) ν 𝓕 → ∀ g ∈ openOff A (frameLat A) (under Z), g ∉ prinInf A β Z → wcoef om ν 𝓕 f f g = 0 := by
  intro D ψ θ A H χA om sA sH _hθ _hη hW _hcA _hcH hrank β Z hP βH f₀ f hβH hvec hthf ν 𝓕 hν g hg hnot
  have sdA := selfDual_frameLat A
  have sdH := selfDual_frameLat H
  obtain ⟨_hvac, e, he, hth⟩ := hvec
  have hQ : (prinDat A Z).Q = ∅ := rfl
  have hPg : (prinDat A Z).Pg = Z := rfl
  have hint : ∀ v, (∀ PP ∈ (prinDat A Z).Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) →
      GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig A.gram (frameLat A) v := by
    intro v hv
    apply hg v
    intro hmem
    simp only [under, Finset.mem_image] at hmem
    obtain ⟨PP, hPP, hPPv⟩ := hmem
    exact hv PP (hPg ▸ hPP) hPPv
  have hsupp := fun x hx => by_contra fun h => hnot
    (GlobalTheory.T.finitePart_mem_level_of_thetaDatum_ne_zero D A H (frameLat A) β βH (prinDat A Z) (fun _ => 1) (fun _ => 1) e sdA hP.frame hrank hQ he g hint x hx h)
  have hsb := _root_.GlobalTheory.ChainOnto.isSBHalf_stepDatum D A H (frameLat A) (frameLat H) β βH (prinDat A Z) (fun _ => 1) (fun _ => 1)
    ((prinDat A Z).Pg ∪ ∅) e sdA sdH hP.frame hβH he
  obtain ⟨n, a, y, -, h1, h2⟩ := _root_.GlobalTheory.HalfSep.sep D ψ A H hW.std (frameLat A) (frameLat H) sdA sdH
    ((prinDat A Z).Pg ∪ ∅) e he f₀ _ f hsb hth g hsupp
  exact _root_.GlobalTheory.ChainOnto.coef_zero_of_heis_relations D ψ A H χA 1 om hW ν 𝓕 hν f hthf g n a y h1 h2

end GlobalTheory.Core.Rk.Exh.SmallSupp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainCoefVanishesOffLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Classical

namespace GlobalTheory.ChainOnto.CoefSuppPf

theorem coefSupp : ∀ D : D7, CoefSupp D := by
  intro D _hgap c hc k _hk s s' hs hs' p hp m X hX φ g hg hnot
  obtain ⟨ξ, f₀, hvec⟩ := hp.vec
  have hthf : IsThetaFunO c.ψ s.V s'.V p.f := GlobalTheory.VecTheta.isThetaFunO_stepVec hvec
  obtain ⟨_hvac, e, he, hth⟩ := hvec
  obtain ⟨hr, ξL, hL⟩ := hs.lev
  have hQ : s.L.Q = ∅ := by rw [hL]; rfl
  have hPg : s.L.Pg = c.Pg := by rw [hL]; rfl
  have hrank : s.V.rank ≤ s'.V.rank := by
    rw [hs.rank, hs'.rank]
    show D.R.r + k * D.R.t ≤ D.R.r + (k + 1) * D.R.t
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ k)) _
  have hint : ∀ v, (∀ PP ∈ s.L.Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) →
      GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v := by
    intro v hv
    apply hg v
    intro hmem
    simp only [Com.S, Finset.mem_image] at hmem
    obtain ⟨PP, hPP, hPPv⟩ := hmem
    exact hv PP (hPg ▸ hPP) hPPv
  have hsupp := fun x hx => by_contra fun h => hnot
    (GlobalTheory.T.finitePart_mem_level_of_thetaDatum_ne_zero D s.V s'.V s.Λ s.β s'.β s.L (c.chi (k + 1)) ξ e hs.selfDual hs.frame hrank hQ he g hint x hx h)
  have hsb := _root_.GlobalTheory.ChainOnto.isSBHalf_stepDatum D s.V s'.V s.Λ s'.Λ s.β s'.β s.L (c.chi (k + 1)) ξ (s.L.Pg ∪ ∅) e
    hs.selfDual hs'.selfDual hs.frame hs'.frame he
  obtain ⟨n, a, y, hy, h1, h2⟩ := _root_.GlobalTheory.HalfSep.sep D c.ψ s.V s'.V hc.std s.Λ s'.Λ hs.selfDual hs'.selfDual
    (s.L.Pg ∪ ∅) e he f₀ _ p.f hsb hth g hsupp
  obtain ⟨H1, -⟩ := _root_.GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D c.ψ c.θ s.V s'.V hc.std hc.inf (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f hthf
    n a y (fun i => (hy i).1) φ
  obtain ⟨H2, H0⟩ := _root_.GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D c.ψ c.θ s.V s'.V hc.std hc.inf (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f hthf
    n (fun i => conj (a i)) (fun i => actO s.V s'.V g⁻¹ 1 (-(y i))) (fun i => (hy i).2) φ
  have R1 : ∑ i, a i • heisO c.ψ s.V s'.V (y i) (p.pt φ) = p.pt φ := by
    show ∑ i, a i • heisO c.ψ s.V s'.V (y i) (pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f φ) = _
    rw [H1, h1]
    rfl
  have R2 : ∑ i, conj (a i) • heisO c.ψ s.V s'.V (actO s.V s'.V g⁻¹ 1 (-(y i))) (p.pt φ) = 0 := by
    show ∑ i, conj (a i) • heisO c.ψ s.V s'.V (actO s.V s'.V g⁻¹ 1 (-(y i)))
      (pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f φ) = _
    rw [H2, h2, H0]
  exact _root_.GlobalTheory.ChainOnto.coef_zero_of_heis_relations D c.ψ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) p.ω hp.weil m X hX (p.pt φ) (hp.theta φ) g n a y R1 R2

end GlobalTheory.ChainOnto.CoefSuppPf
end

