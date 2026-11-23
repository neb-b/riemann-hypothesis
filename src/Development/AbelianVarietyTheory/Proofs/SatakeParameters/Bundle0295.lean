module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Formalism.LocalToGlobal.Columns.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0271
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumTwistPrimeInvariantCongruentFrames
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1740
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SymmTransSymm
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.AwayTop

theorem inFr_trans {E : Type} [Field E] {n m : ℕ} (f f₁ : Sp E n ≃ₗ[E] Sp E n) (g g₁ : Sp E m ≃ₗ[E] Sp E m) (z : HomE E n m) :
    inFr f₁ g₁ z = (g₁.trans g.symm).symm.toLinearMap ∘ₗ inFr f g z ∘ₗ (f₁.trans f.symm).toLinearMap := by
  refine LinearMap.ext fun w => ?_
  simp [inFr, LinearEquiv.trans_symm]

theorem symm_trans_symm {E : Type} [Field E] {n : ℕ} (f f₁ : Sp E n ≃ₗ[E] Sp E n) (y : Sp E n) :
    f₁.symm y = (f₁.trans f.symm).symm (f.symm y) := by
  simp [LinearEquiv.trans_symm]

theorem ptAway_top : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i hi, i = t.m2 + 1 → PtAway A a i hi) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie i hi hi1
  subst hi1
  intro β β' x x' x₁ x₁' p p' p₁ p₁' h1 h2 h3 h4 hag
  have hagS : ∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1 :=
    fun v hv => (hag v hv).1
  have hagT : ∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁'.1 = bc (prV (E := D.host.E) v) x'.1 :=
    fun v hv => (hag v hv).2
  have hok := t.idx_ok μ
  have hc := hok.cst_ok
  have e : ∀ q q', xiPt A (t.m2 + 1) hi β β' q q' =
      XiTop t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) q (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β q) q' := by
    intro q q'
    funext z
    unfold xiPt
    rw [dite_eq_right (by omega), if_neg (by omega)]
  rw [e, e]

  have hF := GlobalTheory.T.chartFrames_congruent_one_of_same_badPlace_components A dtU a hP hTie (t.m2 + 1) (Nat.le_of_succ_le hi) β x x₁ p p₁ h1 h3 hagS
  have hF' := GlobalTheory.T.chartFrames_congruent_one_of_same_badPlace_components A dtU a hP hTie (t.m2 + 1 + 1) hi β' x' x₁' p' p₁' h2 h4 hagT

  have hcos : cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁ = cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p := by
    ext y
    simp only [cosetOf, Set.mem_setOf_eq]
    refine forall_congr' fun P => ?_
    have hb := _root_.GlobalTheory.TwV.cplCoset_bound A dtU a hP hTie (Nat.le_of_succ_le hi) β P (y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P)
      ((GlobalTheory.TwU.Model.sameCoset_equiv t.sel (t.tup μ) (t.cst μ) P).refl _)
    have key := _root_.GlobalTheory.CosetLoc.sameCoset_symm_iff t.sel (t.tup μ) (t.cst μ) P ((frsF t.sel (t.tup μ) p₁ P).trans (frsF t.sel (t.tup μ) p P).symm)
      (y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P) hc (hF P).1 (hF P).2 (hok.depthQ P) hb.1 hb.2 ((frsF t.sel (t.tup μ) p P).symm y)
    rw [← symm_trans_symm] at key
    exact key
  rw [hcos]
  funext z
  rw [XiTop_eq, XiTop_eq]
  congr 1
  ·
    unfold phiT
    congr 1
    refine propext (forall_congr' fun P => ?_)
    have hA := GlobalTheory.T.point_decoration_agree_below A dtU a hP hTie (t.m2 + 1) (Nat.le_of_succ_le hi) β x x₁ p p₁ h1 h3 hagS P
    have hA' := GlobalTheory.T.point_decoration_agree_below A dtU a hP hTie (t.m2 + 1 + 1) hi β' x' x₁' p' p₁' h2 h4 hagT P
    have hB := GlobalTheory.T.chartFunctional_eq_of_agree_at_badPlaces A dtU a hP hTie (t.m2 + 1) (Nat.le_of_succ_le hi) β x x₁ p p₁ h1 h3 hagS P
    have hB' := GlobalTheory.T.chartFunctional_eq_of_agree_at_badPlaces A dtU a hP hTie (t.m2 + 1 + 1) hi β' x' x₁' p' p₁' h2 h4 hagT P
    rw [hA, hA']
    refine forall_congr' fun w => imp_congr_right fun hw => and_congr_right fun hzw => ?_
    rw [hB w hw (hA ▸ hw), hB' _ hzw (hA' ▸ hzw)]
  ·
    refine Finset.prod_congr rfl fun P _ => ?_
    obtain ⟨r, hr⟩ := _root_.GlobalTheory.CosetApprox.exists_sameCoset t.sel (t.tup μ) (t.cst μ) (frsF t.sel (t.tup μ) p) (fun P => y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P)
    have hrep : repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) ∈ cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p :=
      Classical.epsilon_spec (p := fun y => y ∈ cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) ⟨r, hr⟩
    have hb := _root_.GlobalTheory.TwV.cplCoset_bound A dtU a hP hTie (Nat.le_of_succ_le hi) β P _ (hrep P)
    rw [inFr_trans (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p₁ P) (frsF t.sel (t.tup μ) p' P) (frsF t.sel (t.tup μ) p₁' P) z,
      symm_trans_symm (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p₁ P)]
    by_cases hG : P.1 ∈ t.Pr.vGs
    · exact _root_.GlobalTheory.TwV.AwayTopG.topDat_frames_vGs A dtU a hP hTie P hG _ _ (hF P).1 (hF P).2 (hF' P).1 (hF' P).2 _ _ (hb.1 hG)
    · exact _root_.GlobalTheory.TopFrameQ.topDat_frames_tie A dtU a hP hTie P hG _ _ (hF P).1 (hF P).2 (hF' P).1 (hF' P).2 _ _ (hb.2 hG)

end GlobalTheory.TwV.AwayTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeNonzeroRecursionOfEigen
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TypeNZJoin

open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.RecTie


set_option maxHeartbeats 1000000 in
theorem inj_at {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (hT : ∀ j t, GlobalTheory.DownLift.TypeNZ X.R j t) (i : D.nd.Loc) (hS : GlobalTheory.NJoin.EigString X i)
    (hG : GlobalTheory.NJoin.EigGood X i) (hμ : Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (x : D.nd.X i) (hx : x ∈ ZgoodN D.nd D.naut i) (f : D.what₂.Mt (D.nd.mu i) (j.1 + 1))
    (hf : (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x)
    (h0 : D.what₂.thetaP (D.nd.mu i) (j.1 + 1) f = 0) : f = 0 := by
  have hC := X.given.core
  have hfm := (X.IL.jMt _ hμ j f).2
  obtain ⟨y, hy⟩ : ∃ y, (LinearEquiv.ofInjective _ (X.hinj j (X.tupT (D.nd.mu i)))).symm
      ⟨((X.IL.jMt _ hμ j f).1 : Formalism.L2.Theta.GA D (Vc D j) → (X.R.cV j).W), hfm.1⟩ = y := ⟨_, rfl⟩
  have hyf : X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f := by
    rw [← hy]
    exact congrArg Subtype.val ((LinearEquiv.ofInjective _ (X.hinj j (X.tupT (D.nd.mu i)))).apply_symm_apply _)
  have hthG : X.R.thG j (X.tupT (D.nd.mu i)) y = 0 := by
    have hM := GlobalTheory.ThetaLevelP.thF_mem_level X.R X.F hC.lev hC.models hC.thP X.R.hv0 false j (X.tupT (D.nd.mu i)) y
      (by rw [hyf]; exact hfm.2)
    obtain ⟨w, hw1, hw2, hw3⟩ := X.fire.2.1 (D.nd.mu i) hμ j f
    have hw' : PiTensorProduct.lift (X.R.thF j (X.tupT (D.nd.mu i)) y) ∘ₗ
        (toLiftReal X.R X.F X.tupT X.hm X.hTop X.hinj).embK j =
        (toLiftReal X.R X.F X.tupT X.hm X.hTop X.hinj).thC _ j (X.IL.jMt _ hμ j f) := by
      rw [← hy]; rfl
    have hwe : w = PiTensorProduct.lift (X.R.thF j (X.tupT (D.nd.mu i)) y) := by
      refine sub_eq_zero.1 (X.fire.2.2 j _ (sub_mem hw1 (Submodule.mem_map_of_mem hM)) ?_)
      exact (LinearMap.sub_comp _ _ _).trans (by rw [hw2]; exact sub_eq_zero.2 hw'.symm)
    have hth := X.recR.tied.lift.theta (D.nd.mu i) hμ j f w (X.fire.1 _ hμ j) hw1 hw2 hw3
    rw [h0, map_zero, ZeroMemClass.coe_zero, hwe] at hth
    have h2 : PiTensorProduct.lift (postOn _ (X.R.eWf j (sg0 D X.A)) (X.R.thF j (X.tupT (D.nd.mu i)) y)) = 0 := by
      rw [GlobalTheory.ThetaFireLift.lift_postOn]; exact hth.symm
    have h3 : (X.R.HW j (sg0 D X.A)).e (X.R.thG j (X.tupT (D.nd.mu i)) y) = 0 := by
      rw [hC.thP.thG]; exact (LinearEquiv.map_eq_zero_iff _).1 h2
    exact (hC.models.HW j _).1 (h3.trans (map_zero _).symm)
  have hy0 : y = 0 := by
    by_contra hne
    obtain ⟨h, hh⟩ := GlobalTheory.LiftOntoCompare.exists_opsV hC.lev hC.models j (X.tupT (D.nd.mu i))
    obtain ⟨s, hs1, hs2⟩ := hS hμ j hj x hx f hf y hyf hne h hh
    exact hne (hT j _ h hh s hs1 y hs2 (hG hμ j hj x hx f hf y hyf) hthG)
  have h4 : X.IL.jMt _ hμ j f = 0 := by
    apply Subtype.ext
    show X.fn hμ j f = 0
    rw [← hyf, hy0, map_zero]
  exact (LinearEquiv.map_eq_zero_iff _).1 h4

theorem of_cast {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) (S : Submodule ℂ (D.what₂.Mt μ b))
    (H : ∀ f : D.what₂.Mt μ a, (h ▸ f : D.what₂.Mt μ b) ∈ S → D.what₂.thetaP μ a f = 0 → f = 0) :
    ∀ F ∈ S, D.what₂.thetaP μ b F = 0 → F = 0 := by
  subst h
  exact H

end GlobalTheory.TypeNZJoin
end
end

