module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0386
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastTwoStepsDoubleLiftPeriodEqIntegral
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0402

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftAdditive
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastOneLin

variable {D : D7}

theorem sum_fin {G M : Type*} [AddCommMonoid M] (s : Finset G) (F : G → M) :
    ∑ g ∈ s, F g = ∑ i : Fin s.card, F (s.equivFin.symm i) := by
  rw [← Finset.sum_coe_sort s F]
  exact (Equiv.sum_comp s.equivFin.symm (fun x => F x)).symm

section Theta

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem biTheta_left (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {A S A' : HSp D} {C : WO A S → WO S A' → ℂ}
    (hC : IsBiTheta ψ A S A' C) (c : WO A S →₀ ℂ) :
    IsBiTheta ψ A S A' (fun u v => comb ψ A S c (fun u' => C u' v) u) := by
  let d := GlobalTheory.BiTransfer.sumDec A (GlobalTheory.ChiGrid.negSp A')
  rw [GlobalTheory.BiTransfer.isBiTheta_iff_join d] at hC ⊢
  have e : GlobalTheory.BiTransfer.join d S (fun u v => comb ψ A S c (fun u' => C u' v) u) =
      fun w => ∑ x ∈ c.support, c x * heisO ψ _ S (GlobalTheory.BiTransfer.inlH d S x) (GlobalTheory.BiTransfer.join d S C) w := by
    funext w
    simp only [GlobalTheory.BiTransfer.join_apply, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [GlobalTheory.BiTransfer.symplOH_split d, map_add (GlobalTheory.BiTransfer.fstH d S), map_add (GlobalTheory.BiTransfer.sndH d S),
      GlobalTheory.BiTransfer.fst_inl, GlobalTheory.BiTransfer.snd_inl, add_zero, GlobalTheory.FinTranslate.symplOH_zero_right]
  rw [e]
  exact GlobalTheory.SeeSawFold.theta_sum' c.support _ fun x _ =>
    GlobalTheory.SeeSawFold.theta_const_mul' (c x) (GlobalTheory.Unf.MatCoef.theta_heisO_any hψ hθ hC _)

theorem biTheta_right (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {A S A' : HSp D} {C : WO A S → WO S A' → ℂ}
    (hC : IsBiTheta ψ A S A' C) (c : WO S A' →₀ ℂ) :
    IsBiTheta ψ A S A' (fun u v => comb ψ S A' c (C u) v) := by
  let d := GlobalTheory.BiTransfer.sumDec A (GlobalTheory.ChiGrid.negSp A')
  rw [GlobalTheory.BiTransfer.isBiTheta_iff_join d] at hC ⊢
  have e : GlobalTheory.BiTransfer.join d S (fun u v => comb ψ S A' c (C u) v) =
      fun w => ∑ y ∈ c.support, c y * heisO ψ _ S (GlobalTheory.BiTransfer.inrH d S y) (GlobalTheory.BiTransfer.join d S C) w := by
    funext w
    simp only [GlobalTheory.BiTransfer.join_apply, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [GlobalTheory.BiTransfer.symplOH_split d, map_add (GlobalTheory.BiTransfer.fstH d S), map_add (GlobalTheory.BiTransfer.sndH d S),
      GlobalTheory.BiTransfer.fst_inr, GlobalTheory.BiTransfer.snd_inr, add_zero, GlobalTheory.FinTranslate.symplOH_zero_right, zero_add]
  rw [e]
  exact GlobalTheory.SeeSawFold.theta_sum' c.support _ fun y _ =>
    GlobalTheory.SeeSawFold.theta_const_mul' (c y) (GlobalTheory.Unf.MatCoef.theta_heisO_any hψ hθ hC _)

theorem biTheta_biComb_any (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {A S A' : HSp D} {C : WO A S → WO S A' → ℂ}
    (hC : IsBiTheta ψ A S A' C) (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) :
    IsBiTheta ψ A S A' (biComb ψ A S A' c c' C) :=
  biTheta_left hψ hθ (biTheta_right hψ hθ hC c') c

end Theta

theorem aconv_one {G : Type} [AddMonoid G] (d : G →₀ ℂ) : aconv [d] = d := by
  apply AddMonoidAlgebra.ofCoeff_injective (R := ℂ) (M := G)
  rw [GlobalTheory.QValOuter.aconv_cons, GlobalTheory.QValOuter.aconv_nil, mul_one]

theorem comb_aconv_pair (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {E : AE D} (hE : cA D E = E) (hEE : E * E = E)
    (c d : WO S T →₀ ℂ) (hc : ∀ u ∈ c.support, IsHalf (1 - E) u) (hd : ∀ u ∈ d.support, IsHalf E u)
    (f : WO S T → ℂ) : comb ψ S T (aconv [c, d]) f = comb ψ S T c (comb ψ S T d f) := by
  have h := GlobalTheory.QFinLaw.comb_aconv_cons ψ S T c [d] (fun x hx y hy => by
    rw [aconv_one] at hy
    exact GlobalTheory.HeisComb.symplO_half S T (1 - E) E x y (by rw [map_sub, map_one, hE])
      (by rw [sub_mul, one_mul, hEE, sub_self]) (hc x hx) (hd y hy)) f
  rwa [aconv_one] at h

theorem place_idem {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) : cA D (q.e + cA D q.e) = q.e + cA D q.e ∧
      (q.e + cA D q.e) * (q.e + cA D q.e) = q.e + cA D q.e := by
  obtain ⟨h1, h2, -⟩ := q.split
  have h3 : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, h1]
  refine ⟨by rw [map_add (f := _), cA_cA, add_comm], ?_⟩
  linear_combination h1 + 2 * h2 + h3

theorem lin : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → v.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 → (v.τ Q.s h)ᴴ * ((c.bes Q.s 0 h).L.gram * v.τ Q.s h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∀ s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h), s₁.χW = χ Q.s → ∀ oma omb, IsWeilDatumO c.ψ _ _ (χ Q.s) (χ Q.s) oma → IsWeilDatumO c.ψ _ _ (χ (Q.s + 1)) (χ (Q.s + 1)) omb → ∀ c₁ c₂, (∀ u ∈ c₁.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → (∀ u ∈ c₂.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → ∀ Ψ₁ Ψ₂, IsThetaFunO c.ψ _ _ Ψ₁ → IsThetaFunO c.ψ _ _ Ψ₂ → ∀ φ, IsContAut (c.X Q.s) φ → ∀ (ι : Type) (S : Finset ι) (d₁ : ι → WO (c.X Q.s) (c.X (Q.s + 1)) →₀ ℂ) (d₂ : ι → WO (c.X (Q.s + 1)) (c.X (Q.s + 1 + 1)) →₀ ℂ), (∀ i, ∀ u ∈ (d₁ i).support, IsHalf (Q.q.e + cA D Q.q.e) u) → (∀ i, ∀ u ∈ (d₂ i).support, IsHalf (Q.q.e + cA D Q.q.e) u) → c.bl Q.s oma omb φ (biComb c.ψ _ _ _ c₁ c₂ (∑ i ∈ S, biComb c.ψ _ _ _ (d₁ i) (d₂ i) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂))) = ∑ i ∈ S, c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, d₁ i]) (aconv [c₂, d₂ i]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) := by
  intro D c v χ Q hc hv h hr hτ s₁ hs₁ oma omb hoa hob c₁ c₂ hc₁ hc₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ ι S d₁ d₂ hd₁ hd₂
  obtain ⟨hE, hEE⟩ := place_idem (D := D) Q.q
  have hL : IsBiTheta c.ψ _ _ _ (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂) := by
    obtain ⟨-, -, hthS, -⟩ := GlobalTheory.WeilSrc.om0_ext0_eq_om_emb0_of_isWeilDatumO D c.ψ (c.V (Q.s + 1)) (c.X (Q.s + 1)) c.T (c.jac Q.s 0 h).d hc.std
    have hY' : IsThetaFunO c.ψ (c.X (Q.s + 1)) c.T (fun w => Ψ₂ ((c.jac Q.s 0 h).d.ext0 c.T w)) := (hthS Ψ₂).2 hΨ₂
    have hZ' : IsThetaFunO c.ψ (c.B Q.s 0 h).V (c.J Q.s 0 h).W Ψ₁ := hΨ₁
    obtain ⟨hΞ, -⟩ := GlobalTheory.LastRed.val_zero s₁ hZ'
    exact GlobalTheory.LastRed.lastBi_biTheta D c.ψ (c.bes Q.s 0 h).V₀ (c.X Q.s) (c.bes Q.s 0 h).L (c.X (Q.s + 1))
      (c.X (Q.s + 1 + 1)) c.T c.Lz (c.bes Q.s 0 h).o (c.oT (Q.s + 1 + 1) h) (v.τ Q.s h) hτ (flatBF s₁ Ψ₁) _ hΞ hY'
  have hB : BiAct D := GlobalTheory.SeeSaw.biAct_all D
  have hA : CoCpt (c.X Q.s) := (hc.x Q.s (by omega)).cpt
  have hS : CoCpt (c.X (Q.s + 1)) := (hc.x (Q.s + 1) (by omega)).cpt
  have step : biComb c.ψ _ _ _ c₁ c₂ (∑ i ∈ S, biComb c.ψ _ _ _ (d₁ i) (d₂ i) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) =
      ∑ i ∈ S, biComb c.ψ _ _ _ (aconv [c₁, d₁ i]) (aconv [c₂, d₂ i]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂) := by
    show (GlobalTheory.BiCombStable.biCombL c.ψ _ _ _ c₁ c₂) (∑ i ∈ S, biComb c.ψ _ _ _ (d₁ i) (d₂ i) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact GlobalTheory.ProdLocInv.biComb_comp c.ψ _ _ _ c₁ (d₁ i) (aconv [c₁, d₁ i]) c₂ (d₂ i) (aconv [c₂, d₂ i])
      (comb_aconv_pair c.ψ _ _ hE hEE c₁ (d₁ i) hc₁ (hd₁ i)) (comb_aconv_pair c.ψ _ _ hE hEE c₂ (d₂ i) hc₂ (hd₂ i)) _
  rw [step]
  funext h₂
  rw [Finset.sum_apply, sum_fin S (fun i => biComb c.ψ _ _ _ (aconv [c₁, d₁ i]) (aconv [c₂, d₂ i]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)),
    sum_fin S (fun i => c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, d₁ i]) (aconv [c₂, d₂ i]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) h₂)]
  exact GlobalTheory.SeeSmallPf.biLift_sum hB hoa hob hA hS _ _ hφ
    (fun j => biComb c.ψ _ _ _ (aconv [c₁, d₁ (S.equivFin.symm j)]) (aconv [c₂, d₂ (S.equivFin.symm j)])
      (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂))
    (fun j => biTheta_biComb_any hc.std hc.inf hL _ _) h₂

end GlobalTheory.LastOneLin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeRationalLineTraceFractionalIdeal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatLine

open GlobalTheory.FinPl.FrameLat GlobalTheory.SeeSaw.IdVMul

variable {D : D7}

theorem mul_idV_int {𝔠 : FI D} {v : GlobalTheory.FinPl.Pl D} {a : AE D}
    (h : ∀ c ∈ 𝔠, incA D c * a ∈ intAt D (· = v)) {y : AE D} (hy : y ∈ idV 𝔠 v) : y * a ∈ intAt D (· = v) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, h0, c, hc, rfl⟩ := hy
    have e := incA_mul_tmul (D := D) c (pairA D.host.F 0 α) 1
    rw [mul_one] at e
    rw [← e, mul_comm (incA D c), mul_assoc]
    exact intAt_mul (tmul_one_mem_intAt hα h0) (h c hc)
  | zero => rw [zero_mul]; exact intAt_zero
  | add x y _ _ hx hy => rw [add_mul]; exact intAt_add hx hy
  | neg x _ hx => rw [neg_mul]; exact intAt_neg hx

theorem mem_idV_inv {𝔠 : FI D} (h𝔠 : 𝔠 ≠ 0) {v : GlobalTheory.FinPl.Pl D} {a : AE D} (ha : a ∈ idAt D (· = v))
    (h : ∀ c ∈ 𝔠, incA D c * a ∈ intAt D (· = v)) : a ∈ idV 𝔠⁻¹ v := by
  obtain ⟨b, hb0, hb⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔠⁻¹ (inv_ne_zero h𝔠)
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔠 h𝔠
  have hm := idV_mul_gen D v 𝔠⁻¹ 𝔠 b c hb0 hc0 hb hc (GlobalTheory.FinPlLoc.idem D (· = v))
  rw [inv_mul_cancel₀ h𝔠, GlobalTheory.SeeSaw.idV_one_eq_intAt] at hm
  obtain ⟨h1, h2⟩ := hm.1 (GlobalTheory.FinPlLoc.idem_mem_intAt _)
  have h3 : incA D b⁻¹ * GlobalTheory.FinPlLoc.idem D (· = v) ∈ idV 𝔠 v := by
    refine (hc _).2 ⟨?_, Ideal.mul_mem_left _ _ h2⟩
    rw [← mul_assoc, ← map_mul, ← mul_inv, mul_comm c b]
    exact h1
  have h4 := mul_idV_int h h3
  rw [mul_assoc, (GlobalTheory.FinPlLoc.mem_idAt_iff _ a).1 ha] at h4
  exact (hb a).2 ⟨h4, ha⟩

theorem pairing_smul_ratV (S : HSp D) (s x : Fin S.rank → D.host.E) (a : AE D) :
    pairing S s (a • ratV x) = incA D (∑ b, row S s b * x b) * a := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [pairing, ratV, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem incA_inj : Function.Injective (incA D) := GlobalTheory.MixModel.incA_injective

theorem smul_mem_latV {S : HSp D} {L : Lat S} {x : Fin S.rank → D.host.E} {𝔞 : FI D} (h : ∀ t ∈ 𝔞, t • x ∈ L)
    {v : GlobalTheory.FinPl.Pl D} {a : AE D} (ha : a ∈ idV 𝔞 v) : a • ratV x ∈ latV S L (· = v) := by
  induction ha using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, h0, t, ht, rfl⟩ := hy
    have e := incA_mul_tmul (D := D) t (pairA D.host.F 0 α) 1
    rw [mul_one] at e
    have := int_mul_mem (tmul_one_mem_intAt hα h0) (h t ht)
    convert this using 1
    funext i
    rw [← e]
    simp only [ratV, Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  | zero => rw [zero_smul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_smul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_smul]; exact neg_mem hx

theorem line_trace : ∀ (D : D7) (S : HSp D) (L : Lat S) (x : Fin S.rank → D.host.E), IsSelfDualC S L → x ≠ 0 → ∃ 𝔞 : FI D, 𝔞 ≠ 0 ∧ (∀ t : D.host.E, t • x ∈ L ↔ t ∈ 𝔞) ∧ ∀ v : GlobalTheory.FinPl.Pl D, ∀ a ∈ idAt D (· = v), a • ratV x ∈ latV S L (· = v) ↔ a ∈ idV 𝔞 v := by
  intro D S L x hL hx
  obtain ⟨m, s, s', hs, hs', hexp⟩ := exists_expansion hL
  set c : Fin m → D.host.E := fun l => ∑ b, row S (s' l) b * x b with hc
  have hx' : ∀ i, x i = ∑ l, c l * s l i := by
    intro i
    apply incA_inj (D := D)
    have := hexp ((1 : AE D) • ratV x) i
    simp only [pairing_smul_ratV, mul_one] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simpa only [one_smul, ratV, map_mul] using this
  set 𝔠 : FI D := FractionalIdeal.spanFinset (𝓞 D.host.E) Finset.univ c with h𝔠def
  have hmem : ∀ y, y ∈ 𝔠 ↔ y ∈ Submodule.span (𝓞 D.host.E) (Set.range c) := by
    intro y
    rw [← FractionalIdeal.mem_coe, h𝔠def, FractionalIdeal.spanFinset_coe, Finset.coe_univ, Set.image_univ]
  have h𝔠 : 𝔠 ≠ 0 := by
    intro h0
    apply hx
    funext i
    rw [hx' i]
    refine Finset.sum_eq_zero fun l _ => ?_
    have : c l ∈ 𝔠 := (hmem _).2 (Submodule.subset_span ⟨l, rfl⟩)
    rw [h0, FractionalIdeal.mem_zero_iff] at this
    rw [this, zero_mul]
  have hglob : ∀ t : D.host.E, t • x ∈ L ↔ t ∈ 𝔠⁻¹ := by
    intro t
    rw [FractionalIdeal.mem_inv_iff h𝔠]
    constructor
    · intro ht y hy
      rw [hmem] at hy
      rw [← FractionalIdeal.mem_coe]
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨l, rfl⟩ := hy
        obtain ⟨o, ho⟩ := (hL.2 _).1 ht (s' l) (hs' l)
        rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_one_iff]
        refine ⟨o, ho.trans ?_⟩
        rw [Finset.sum_comm]
        simp only [hc, GlobalTheory.FinPl.FrameLat.row, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      | zero => rw [mul_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
      | smul o y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy
    · intro ht
      have ho : ∀ l, ∃ o : 𝓞 D.host.E, algebraMap _ D.host.E o = t * c l := fun l =>
        (FractionalIdeal.mem_one_iff _).1 (ht _ ((hmem _).2 (Submodule.subset_span ⟨l, rfl⟩)))
      choose o ho using ho
      have : t • x = ∑ l, o l • s l := by
        funext i
        rw [Pi.smul_apply, smul_eq_mul, hx' i, Finset.mul_sum, Finset.sum_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Pi.smul_apply, Algebra.smul_def, ho, mul_assoc]
      rw [this]
      exact Submodule.sum_mem _ fun l _ => L.smul_mem _ (hs l)
  refine ⟨𝔠⁻¹, inv_ne_zero h𝔠, hglob, fun v a ha => ⟨fun h => ?_, smul_mem_latV fun t ht => (hglob t).2 ht⟩⟩
  refine mem_idV_inv h𝔠 ha fun y hy => ?_
  rw [hmem] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, rfl⟩ := hy
    refine ⟨Ideal.mul_mem_left _ _ ha, ?_⟩
    have := pairing_int hL (hs' l) h
    rwa [pairing_smul_ratV] at this
  | zero => rw [map_zero, zero_mul]; exact intAt_zero
  | add y z _ _ hy hz => rw [map_add (f := _), add_mul]; exact intAt_add hy hz
  | smul o y hy' hy =>
    have h1 := GlobalTheory.IdVGen.gen_mem_intAt (v := v) (GlobalTheory.FinPlLoc.ePl_int (· = v))
      (fun w hw => by rw [GlobalTheory.FinPlLoc.evalV_ePl, if_neg hw]) o
    have e := incA_mul_tmul (D := D) (algebraMap (𝓞 D.host.E) D.host.E o) (pairA D.host.F 0 (GlobalTheory.FinPlLoc.ePl D (· = v))) 1
    rw [mul_one] at e
    have h2 := intAt_mul h1 hy
    rw [← e] at h2
    have h3 : GlobalTheory.FinPlLoc.idem D (· = v) * a = a := (GlobalTheory.FinPlLoc.mem_idAt_iff _ a).1 ha
    convert h2 using 1
    rw [Algebra.smul_def, map_mul]
    conv_lhs => rw [← h3]
    simp only [GlobalTheory.FinPlLoc.idem]
    ring

end GlobalTheory.Core.Mi.LatLine

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeSplitsOffUnitNormLineAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch.SplitOff

variable {D : D7}

theorem hermAt_eq (S : HSp D) (x y : Fin S.rank → AE D) :
    GlobalTheory.IwaPlace.hermAt S x y = (fun i => cA D (y i)) ⬝ᵥ (gA S *ᵥ x) := by
  simp only [GlobalTheory.IwaPlace.hermAt, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hermAt_mulVec (S : HSp D) {k : ℕ} (a : Mx D S.rank k) (x : Fin S.rank → AE D) (y : Fin k → AE D) :
    GlobalTheory.IwaPlace.hermAt S x (a *ᵥ y) = (fun i => cA D (y i)) ⬝ᵥ ((adj a ⬝ gA S) *ᵥ x) := by
  have h : (fun i => cA D ((a *ᵥ y) i)) = (fun i => cA D (y i)) ᵥ* adj a := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hermAt_eq, h, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec _ (adj a)]

theorem hermAt_jB {S A B : HSp D} (o : OrthDec S A B) (y : Fin S.rank → AE D) (l : Fin B.rank → AE D) :
    GlobalTheory.IwaPlace.hermAt S y (o.jB *ᵥ l) = GlobalTheory.IwaPlace.hermAt B (o.pB *ᵥ y) l := by
  rw [hermAt_mulVec, hermAt_eq, Matrix.mulVec_mulVec, o.pB_eq, ← Matrix.mul_assoc (gA B), gA_mul_giA, Matrix.one_mul]

theorem ratV_vecB {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) :
    ratV (vecB o ζ) = o.jB *ᵥ ratV ζ :=
  funext fun i => RingHom.map_mulVec (incA D) o.iB ζ i

theorem hermAt_smul (S : HSp D) (c a : AE D) (x y : Fin S.rank → AE D) :
    GlobalTheory.IwaPlace.hermAt S (c • x) (a • y) = c * cA D a * GlobalTheory.IwaPlace.hermAt S x y := by
  simp only [GlobalTheory.IwaPlace.hermAt, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem cA_incA (e : D.host.E) : cA D (incA D e) = incA D (star e) := rfl

theorem hermAt_ratV (S : HSp D) (x : Fin S.rank → D.host.E) :
    GlobalTheory.IwaPlace.hermAt S (ratV x) (ratV x) = incA D (star x ⬝ᵥ S.gram *ᵥ x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GlobalTheory.IwaPlace.hermAt, gA, rat, ratV, Matrix.map_apply, dotProduct, Matrix.mulVec, map_sum, map_mul,
    Finset.mul_sum, cA_incA, Pi.star_apply, mul_assoc]

end GlobalTheory.Core.Mi.LatMatch.SplitOff

namespace GlobalTheory.Core.Mi.LatMatch.SplitOff

variable {D : D7}

theorem eps_mem_idV (v : GlobalTheory.FinPl.Pl D) :
    algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) ∈ idV (1 : FI D) v := by
  apply AddSubgroup.subset_closure
  refine ⟨GlobalTheory.SelfDualAt.indP (· = v), ?_, ?_, 1, ?_, ?_⟩
  · intro w
    rw [GlobalTheory.SelfDualAt.evalV_indP]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · intro w hw
    rw [GlobalTheory.SelfDualAt.evalV_indP, if_neg hw]
  · exact FractionalIdeal.one_mem_one _
  · rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rfl

theorem incA_mul_mem_idV (c : D.host.E) {𝔞 : FI D} {v : GlobalTheory.FinPl.Pl D} {x : AE D} (hx : x ∈ idV 𝔞 v) :
    incA D c * x ∈ idV (FractionalIdeal.spanSingleton _ c * 𝔞) v := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, h1, h2, a, ha, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    refine ⟨α, h1, h2, c * a, FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) ha, ?_⟩
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] c) * (_ ⊗ₜ[D.host.F] _) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem natInv_mul_mem_intAt {T : ℕ} {v : GlobalTheory.FinPl.Pl D} (hT : (T : 𝓞 D.host.F) ∉ v.asIdeal) {x : AE D}
    (hx : x ∈ intAt D (· = v)) : incA D ((T : D.host.E)⁻¹) * x ∈ intAt D (· = v) := by
  rw [← GlobalTheory.SeeSaw.idV_one_eq_intAt] at hx ⊢
  exact GlobalTheory.SeeSaw.idV_natInv_mul_le D 1 T v hT (incA_mul_mem_idV _ hx)

end GlobalTheory.Core.Mi.LatMatch.SplitOff

namespace GlobalTheory.Core.Mi.LatMatch.SplitOff

variable {D : D7}

theorem norm_factor {μ : D.host.E} (hμ : μ ≠ 0) (T : ℕ) (N : D.host.E) (hN : N = -(μ * star μ * (T : D.host.E))) :
    (incA D (star μ⁻¹) : AE D) * incA D N = -((incA D (T : D.host.E) : AE D) * incA D μ) := by
  have hstar : star μ ≠ 0 := star_ne_zero.2 hμ
  have e : star μ⁻¹ * N = -((T : D.host.E) * μ) := by
    rw [hN, star_inv₀]
    field_simp
  rw [← map_mul, e, map_neg, map_mul]

theorem nat_ne_zero {T : ℕ} {v : GlobalTheory.FinPl.Pl D} (hT : (T : 𝓞 D.host.F) ∉ v.asIdeal) : (T : D.host.E) ≠ 0 := by
  rintro h0
  apply hT
  have : T = 0 := by exact_mod_cast h0
  rw [this, Nat.cast_zero]
  exact zero_mem _

theorem cancel_mem {T : ℕ} {v : GlobalTheory.FinPl.Pl D} (hT : (T : 𝓞 D.host.F) ∉ v.asIdeal) {x : AE D}
    (h : incA D (T : D.host.E) * x ∈ intAt D (· = v)) : x ∈ intAt D (· = v) := by
  have h2 := natInv_mul_mem_intAt hT h
  rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ (nat_ne_zero hT), map_one, one_mul] at h2

theorem line_part {S A L : HSp D} (o : OrthDec S A L) {ζ : Fin L.rank → D.host.E} {M : Lat S} {μ : D.host.E} {T : ℕ}
    {v : GlobalTheory.FinPl.Pl D} (hM : IsSelfDualC S M) (hμ : μ ≠ 0) (hline : LineAt (vecB o ζ) μ M v)
    (hnorm : star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E))) (hT : (T : 𝓞 D.host.F) ∉ v.asIdeal)
    {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D (· = v)) (hyM : y ∈ latV S M (· = v)) (c : AE D)
    (hc : c ∈ idAt D (· = v)) (hl : o.pB *ᵥ y = c • ratV ζ) : incA D μ * c ∈ intAt D (· = v) := by
  have hεI : algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) ∈ intAt D (· = v) :=
    (GlobalTheory.SeeSaw.idV_one_eq_intAt D v _).1 (eps_mem_idV v)
  have hεc := GlobalTheory.SelfDualAt.algebraMap_placeIdempotent_mul (· = v) c hc
  have hεε := GlobalTheory.SelfDualAt.cA_alg (D := D) (GlobalTheory.SelfDualAt.cP (· = v))
  have ha : algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) * incA D μ⁻¹ ∈ idAt D (· = v) :=
    Ideal.mul_mem_right _ _ hεI.1
  have haM := (hline _ ha).2 (by
    rw [mul_left_comm, ← map_mul, mul_inv_cancel₀ hμ, map_one, mul_one]
    exact hεI)
  have hsd := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D S M v hM
  have hh := ((hsd.2.2 y hy).1 hyM) _ haM
  have hXY := norm_factor (D := D) hμ T _ hnorm
  rw [ratV_vecB, ← Matrix.mulVec_smul, hermAt_jB, hl, hermAt_smul, hermAt_ratV, map_mul, hεε, cA_incA] at hh
  have key : c * (algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) * incA D (star μ⁻¹)) *
      incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ) = -(incA D (T : D.host.E) * (incA D μ * c)) := by
    linear_combination (algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) * c) * hXY -
      (incA D (T : D.host.E) * incA D μ) * hεc
  rw [key] at hh
  rw [← GlobalTheory.SeeSaw.idV_one_eq_intAt] at hh
  have h3 := neg_mem hh
  rw [neg_neg, GlobalTheory.SeeSaw.idV_one_eq_intAt] at h3
  exact cancel_mem hT h3

end GlobalTheory.Core.Mi.LatMatch.SplitOff

namespace GlobalTheory.Core.Mi.LatMatch.SplitOff

theorem splitsAt : ∀ (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M : Lat S) (μ : D.host.E) (T : ℕ) (v : GlobalTheory.FinPl.Pl D), IsLineVec L ζ → IsSelfDualC S M → μ ≠ 0 → LineAt (vecB o ζ) μ M v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → (T : 𝓞 D.host.F) ∉ v.asIdeal → SplitsAt o M v := by
  intro D S A L o ζ M μ T v hζ hM hμ hline hnorm hT y hy
  have hsum : o.jA *ᵥ (o.pA *ᵥ y) + o.jB *ᵥ (o.pB *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, o.sum_eq_one, Matrix.one_mulVec]
  constructor
  · intro hyM
    have hs : ∀ j k : Fin L.rank, j = k := fun j k => Fin.ext (by have := hζ.1; omega)
    obtain ⟨i, hi⟩ : ∃ i, ζ i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hζ.2
      rw [show ζ = 0 from funext hcon]
      simp
    have hl : o.pB *ᵥ y = ((o.pB *ᵥ y) i * incA D (ζ i)⁻¹) • ratV ζ := funext fun j => by
      rw [hs j i, Pi.smul_apply, smul_eq_mul, ratV, mul_assoc, ← map_mul, inv_mul_cancel₀ hi, map_one, mul_one]
    have hc : (o.pB *ᵥ y) i * incA D (ζ i)⁻¹ ∈ idAt D (· = v) :=
      Ideal.mul_mem_right _ _ (GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy i)
    have hB : o.jB *ᵥ (o.pB *ᵥ y) ∈ latV S M (· = v) := by
      have hvec : o.jB *ᵥ (o.pB *ᵥ y) = ((o.pB *ᵥ y) i * incA D (ζ i)⁻¹) • ratV (vecB o ζ) := by
        conv_lhs => rw [hl]
        rw [Matrix.mulVec_smul, ratV_vecB]
      rw [hvec]
      exact (hline _ hc).2 (line_part o hM hμ hline hnorm hT hy hyM _ hc hl)
    refine ⟨?_, hB⟩
    rw [eq_sub_of_add_eq hsum]
    exact sub_mem hyM hB
  · rintro ⟨h1, h2⟩
    rw [← hsum]
    exact add_mem h1 h2

end GlobalTheory.Core.Mi.LatMatch.SplitOff

end
end

