module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0193
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0142
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0195
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0188
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerFixesTailCoords

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.JDRvStepAOfLvlA
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Filter Topology
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.GrpMA

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def LvlA : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (hr : 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (D' : Set (Q.Mx k r)) (Y : ℂ),
    inWb k r z → inWb k r z' → Q.IsDom k r z z' (TemperedBoundGL3.lr hr).castSucc D' →
    ∀ J₀ ∈ Q.FFl k r z z' π π' (TemperedBoundGL3.lr hr).castSucc D', ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r),
      g ∈ Qx6.Dc1 (TemperedBoundGL3.lr hr) D' c →
      NLv k r z z' (TemperedBoundGL3.lr hr).castSucc (Q.uC k r (Fin.last r) Y - 1) J₀
          (Q.w1 k r (TemperedBoundGL3.lr hr) (c (TemperedBoundGL3.lr hr)) * g) =
        -((Q.uC k r (Fin.last r) Y - 1 - ((Q.mdim k r (Fin.last r) - 1 : ℕ) : ℂ)) •
              Q.tL k r z z' (Fin.last r) Y 0 1 (fun x => J₀ (Q.w1 k r (TemperedBoundGL3.lr hr) (c (TemperedBoundGL3.lr hr)) * x)) g -
            pbOp (TemperedBoundGL3.lr hr) (fun c' => Q.tL k r z z' (Fin.last r) Y 0 1
              (fun x => J₀ (Q.w1 k r (TemperedBoundGL3.lr hr) (c' (TemperedBoundGL3.lr hr)) * x)) g) c) -
          (star (c (TemperedBoundGL3.lr hr)))⁻¹ •
            Q.tL k r z z' (Fin.last r) Y 1 1 (fun x => J₀ (Q.w1 k r (TemperedBoundGL3.lr hr) (c (TemperedBoundGL3.lr hr)) * x)) g

section ops

variable {k r : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem nlv_smulC (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 1)) (u : ℂ) :
    Formalism.FourierDecayAlt.P5.SmulC (E := X) (NLv k r z z' l u) := by
  intro α f
  funext x
  simp only [NLv, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [Formalism.FourierDecayAlt.P5.qminorOp_smulC (fun a b => Formalism.FourierDecayAlt.P5.eabH_smulC _ a b) _ _ u α f, Pi.smul_apply, smul_comm]

theorem nlv_left {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 1))
    (u : ℂ) (i : Fin (r + 1)) {c : Fin r → ℂ} (hc : c ∈ OmX r) (f : Q.Mx k r → X) :
    NLv k r z z' l u (fun x => f (Q.wCell k r i c * x)) = fun x => NLv k r z z' l u f (Q.wCell k r i c * x) := by
  funext x
  simp only [NLv]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [TemperedBoundGL3.hermitian_invariant_cell_action i hc hz x]
  congr 1
  exact congrFun (Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian X _ _ (Hpk k r) f _ _ u _) x

end ops

theorem jDRvStepA_of_lvlA (h : LvlA) : JDRvStepA := by
  intro Wp Wq _ _ _ _ k r hr z z' π π' D Y hz hz' hD J hJ c hc g hg hcg
  obtain ⟨hJ₀, hD'⟩ := TemperedBoundGL3.br1 hz hz' hD hJ hc (TemperedBoundGL3.lr hr)
  have hcg' : Q.wCell k r (TemperedBoundGL3.lr hr).succ c * g ∈ D := by rw [TemperedBoundGL3.lr_succ]; exact hcg
  have hgD' := TemperedBoundGL3.cell_preimage_mem_domain (TemperedBoundGL3.lr hr) hcg'
  have hL := h Wp Wq k r hr z z' π π' _ Y hz hz' hD' _ hJ₀ c hc g hg hgD'

  set l : Fin r := TemperedBoundGL3.lr hr with hl
  set J₀ := Q.resG k r l.castSucc J c with hJ₀def
  set W : (Fin r → ℂ) → ℂ := fun c' => ((‖c' l‖ ^ (Mdim k r l - 1) : ℝ) : ℂ) with hW
  set A' : (Fin r → ℂ) → (Wq →L[ℂ] Wp) := fun c' =>
    Q.tL k r z z' (Fin.last r) Y 0 1 (fun x => J₀ (Q.w1 k r l (c' l) * x)) g with hA'
  set T22 := Q.tL k r z z' (Fin.last r) Y 1 1 (fun x => J₀ (Q.w1 k r l (c l) * x)) g with hT22

  have hb := TemperedBoundGL3.br2 l (NLv k r z z' l.castSucc (Q.uC k r (Fin.last r) Y - 1)) (nlv_smulC z z' _ _) c
    (nlv_left hz z' _ _ l.castSucc hc) J g
  rw [TemperedBoundGL3.lr_succ] at hb
  have eL : FNv k r z z' Y J ⟨r - 1, by omega⟩ c g =
      W c • NLv k r z z' l.castSucc (Q.uC k r (Fin.last r) Y - 1) J₀ (Q.w1 k r l (c l) * g) := by
    show Q.resG k r (Fin.last r) (NLv k r z z' l.castSucc (Q.uC k r (Fin.last r) Y - 1) J) c g = _
    rw [hb]

  have eR : ∀ c' ∈ OmX r, (∀ a : Fin r, a.val < l.val → c' a = c a) →
      Q.resG k r (Fin.last r) J c' = fun x => W c' • J₀ (Q.w1 k r l (c' l) * x) := by
    intro c' hc' hcc
    rw [← TemperedBoundGL3.lr_succ hr, Qx6.resG_succ]
    funext x
    show W c' • Q.resG k r l.castSucc J c' (Q.w1 k r l (c' l) * x) = _
    rw [Qx6.ind_resG l.castSucc J c' hc' c hc (fun a ha => hcc a ha)]
  have eRc := eR c hc (fun _ _ => rfl)

  have hTop := mirror_residue_top_holds Wp Wq k r z z' π π' D Y hz hz' hD J hJ
  set f₂ : (Fin r → ℂ) → (Wq →L[ℂ] Wp) := fun c' =>
    Q.tL k r z z' (Fin.last r) Y 0 1 (Q.resG k r (Fin.last r) J c') g with hf₂
  have hgerm : (fun c' => FNv k r z z' Y J (Fin.last r) c' g) =ᶠ[𝓝 c] fun c' => -f₂ c' := by
    filter_upwards [Qx6.near_pt (Qx6.open_Dcell hD.1 (Fin.last r)) hc hcg] with c' hc'
    rw [hTop c' hc'.1 g hg hc'.2]
    rfl
  have hfam := (Formalism.FourierDecayAlt.P.restriction_good_family Wp Wq k r z z' π π' D hz hz' hD J hJ (Fin.last r)).1
  have hf₂d : DifferentiableAt ℝ f₂ c :=
    Formalism.FourierDecayAlt.P.Qx3.fam_differentiableAt (Formalism.FourierDecayAlt.P.Qx3.pres_tL z z' Y 0 1 _ hfam) (x := (c, g)) ⟨hc, hcg⟩ hg
  have hrr := Formalism.FourierDecayAlt.P.Qx3.pres_tL (i := l.succ) (U₀ := Qx6.UU (Qx6.Dc1 l (Qx6.Dcell D l.castSucc c))) z z' Y 0 1 _
    (Qx6.sf_rr Formalism.FourierDecayAlt.P.weyl_level_element_properties l hJ₀.1)
  rw [TemperedBoundGL3.lr_succ] at hrr
  have hA'd : DifferentiableAt ℝ A' c :=
    Formalism.FourierDecayAlt.P.Qx3.fam_differentiableAt hrr (x := (c, g)) ⟨hc, hgD'⟩ hg
  have hWd : DifferentiableAt ℝ W c := Qx6.diff_gamma l _ hc
  have hf₃d : DifferentiableAt ℝ (fun c' => W c' • A' c') c := hWd.smul hA'd
  have hline : ∀ᶠ s in 𝓝 (c l), (fun c' => -f₂ c') (Function.update c l s) =
      (-1 : ℂ) • (fun c' => W c' • A' c') (Function.update c l s) := by
    filter_upwards [isOpen_ne.mem_nhds (hc l)] with s hs
    have hu : Function.update c l s ∈ OmX r := Qx6.update_mem_Om hc l hs
    have hcc : ∀ a : Fin r, a.val < l.val → Function.update c l s a = c a := fun a ha =>
      Function.update_of_ne (fun e => by rw [e] at ha; exact lt_irrefl _ ha) _ _
    show -(Q.tL k r z z' (Fin.last r) Y 0 1 (Q.resG k r (Fin.last r) J (Function.update c l s)) g) = _
    rw [eR _ hu hcc, show (fun x => W (Function.update c l s) • J₀ (Q.w1 k r l (Function.update c l s l) * x)) =
      W (Function.update c l s) • (fun x => J₀ (Q.w1 k r l (Function.update c l s l) * x)) from rfl,
      Formalism.FourierDecayAlt.P5.tL_smulC z z' (Fin.last r) Y 0 1 (W (Function.update c l s))
      (fun x => J₀ (Q.w1 k r l (Function.update c l s l) * x)), neg_one_smul]
    rfl
  have hp1 : pbOp l (fun c' => FNv k r z z' Y J (Fin.last r) c' g) c = pbOp l (fun c' => -f₂ c') c :=
    Qx6.opL_germ l 3 hgerm
  have hp2 : pbOp l (fun c' => -f₂ c') c = (-1 : ℂ) • pbOp l (fun c' => W c' • A' c') c :=
    Qx6.opL_dir l 3 (-1) hf₂d.neg hf₃d hline
  have hp3 : pbOp l (fun c' => W c' • A' c') c = W c • pbOp l A' c + ((((Mdim k r l - 1 : ℕ) : ℂ) / 2) * W c) • A' c := by
    rw [Qx6.pbOp_smul l hc hWd hA'd, Qx6.pbOp_gamma l hc]

  have eF : FNv k r z z' Y J (Fin.last r) c g = -(W c • A' c) := by
    rw [hTop c hc g hg hcg]
    show -(Q.tL k r z z' (Fin.last r) Y 0 1 (Q.resG k r (Fin.last r) J c) g) = _
    rw [eRc, show (fun x => W c • J₀ (Q.w1 k r l (c l) * x)) = W c • (fun x => J₀ (Q.w1 k r l (c l) * x)) from rfl,
      Formalism.FourierDecayAlt.P5.tL_smulC z z' (Fin.last r) Y 0 1 (W c) (fun x => J₀ (Q.w1 k r l (c l) * x))]
    rfl
  have e11 : Q.QL k r z z' (Fin.last r) Y 1 1 (Q.resG k r (Fin.last r) J) c g = W c • T22 := by
    show Q.tL k r z z' (Fin.last r) Y 1 1 (Q.resG k r (Fin.last r) J c) g = _
    rw [eRc, show (fun x => W c • J₀ (Q.w1 k r l (c l) * x)) = W c • (fun x => J₀ (Q.w1 k r l (c l) * x)) from rfl,
      Formalism.FourierDecayAlt.P5.tL_smulC z z' (Fin.last r) Y 1 1 (W c) (fun x => J₀ (Q.w1 k r l (c l) * x))]
    rfl

  have hmd : ((Q.mdim k r (Fin.last r) - 1 : ℕ) : ℂ) = (Q.mdim k r (Fin.last r) : ℂ) - 1 := by
    have : 1 ≤ Q.mdim k r (Fin.last r) := by simp [Q.mdim]
    push_cast [Nat.cast_sub this]
    ring
  have hMd : ((Mdim k r l - 1 : ℕ) : ℂ) = (Q.mdim k r (Fin.last r) : ℂ) + 1 := by
    rw [Qx6.stp_Mdim, TemperedBoundGL3.lr_succ]
  have hU : Q.uC k r (Fin.last r) Y - 1 - ((Q.mdim k r (Fin.last r) - 1 : ℕ) : ℂ) =
      Y - ((Mdim k r l - 1 : ℕ) : ℂ) / 2 := by
    rw [hmd, hMd]
    unfold Q.uC
    ring

  rw [eL, hL, hU]
  show _ = Y • FNv k r z z' Y J (Fin.last r) c g - pbOp l (fun c' => FNv k r z z' Y J (Fin.last r) c' g) c -
    (star (c l))⁻¹ • Q.QL k r z z' (Fin.last r) Y 1 1 (Q.resG k r (Fin.last r) J) c g
  rw [hp1, hp2, hp3, eF, e11]
  module

end

end Formalism.FourierDecayAlt.P.CutMP.GrpMA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftTypeActionHolds
section
open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LeftTypeActionHermitianCurvature

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)} {i : Fin (r + 1)} {mm : ℕ∞}

theorem mem_left (hD : IsDom k r z z' i D) {g h : Mx k r} (hg : g ∈ Glev k r i ∩ D)
    (hh : h ∈ UWset k r z) : h * g ∈ Glev k r i ∩ D := by
  have := Qx8.dom_mem hD hg hh (Qx8.nlev_one _) (Qx8.uw_one z') (Qx8.nlev_one _)
  simpa using this

theorem J_left (hπ : IsCRepOn (UWset k r z) π) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D) {g h : Mx k r}
    (hg : g ∈ Glev k r i ∩ D) (hh : h ∈ UWset k r z) : J (h * g) = (π h).comp (J g) := by
  have e1 := hJ.2.2.2 g hg 1 (Qx8.uw_one z) 1 (Qx8.uw_one z')
  have e2 := hJ.2.2.2 g hg h hh 1 (Qx8.uw_one z')
  rw [Matrix.one_mul, Matrix.mul_one, hπ.1] at e1
  rw [Matrix.mul_one] at e2
  have e3 : (1 : Wp →L[ℂ] Wp).comp ((J g).comp (π' 1)) = (J g).comp (π' 1) := ContinuousLinearMap.id_comp _
  rw [e3] at e1
  rw [e2, ← e1]

theorem ld_left (hD : IsDom k r z z' i D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wp →L[ℂ] Wp}
    (hF : ∀ g ∈ Glev k r i ∩ D, F g = B.comp (J g)) {X : Mx k r} (hX : QrD.InLieW k r z X)
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) : LdV X F g = (B.comp (QrD.dOp π X)).comp (J g) := by
  have h := QrD.dOp_hasDeriv hπ hc hX
  let L : (Wp →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
    (ContinuousLinearMap.compL ℂ Wq Wp Wp B).comp ((ContinuousLinearMap.compL ℂ Wq Wp Wp).flip (J g))
  have h2 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have h3 : (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • X) * g)) =
      (L.restrictScalars ℝ) ∘ fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) := by
    funext t
    rw [hF _ (mem_left hD hg (QrD.exp_uw hX t)), J_left hπ hJ hg (QrD.exp_uw hX t)]
    rfl
  unfold LdV
  rw [h3]
  exact h2.deriv

theorem lz_left (hD : IsDom k r z z' i D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wp →L[ℂ] Wp}
    (hF : ∀ g ∈ Glev k r i ∩ D, F g = B.comp (J g)) {Z : Mx k r}
    (h1 : QrD.InLieW k r z (hpart1 (Hpk k r) Z)) (h2 : QrD.InLieW k r z (hpart2 (Hpk k r) Z))
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    LZ (Hpk k r) Z F g = (B.comp (QrD.ecOp π Z)).comp (J g) := by
  unfold LZ QrD.ecOp
  rw [ld_left hD hπ hc hJ hF h1 hg, ld_left hD hπ hc hJ hF h2 hg]
  ext v
  simp

theorem fold_left (hD : IsDom k r z z' i D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    (L : List (ℂ × Mx k r))
    (hL : ∀ p ∈ L, QrD.InLieW k r z (hpart1 (Hpk k r) p.2) ∧ QrD.InLieW k r z (hpart2 (Hpk k r) p.2)) :
    ∀ (F : Mx k r → (Wq →L[ℂ] Wp)) (B : Wp →L[ℂ] Wp), (∀ g ∈ Glev k r i ∩ D, F g = B.comp (J g)) →
      ∀ g ∈ Glev k r i ∩ D, ∀ v,
        (L.map fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + LZ (Hpk k r) p.2 y).foldl (fun h T => T h) F g v =
          B ((L.map fun p => fun y : Wp => p.1 • y + EcRep (Hpk k r) π p.2 y).foldr (fun T h => T h) (J g v)) := by
  induction L with
  | nil =>
    intro F B hF g hg v
    simp only [List.map_nil, List.foldl_nil, List.foldr_nil]
    rw [hF g hg]
    rfl
  | cons p L ih =>
    intro F B hF g hg v
    have hp := hL p (by simp)
    simp only [List.map_cons, List.foldl_cons, List.foldr_cons]
    rw [ih (fun q hq => hL q (by simp [hq])) (p.1 • F + LZ (Hpk k r) p.2 F) (p.1 • B + B.comp (QrD.ecOp π p.2))
      (fun x hx => by
        simp only [Pi.add_apply, Pi.smul_apply]
        rw [lz_left hD hπ hc hJ hF hp.1 hp.2 hx, hF x hx]
        ext v
        simp) g hg v, QrD.ecRep_eq hπ hc hp.1 hp.2]
    simp

end LeftTypeActionHermitianCurvature

theorem left_type_action_holds : LeftTypeAction0 := by
  intro Wp Wq _ _ _ _ _ k r m z z' π π' D mm _ _ hD hπ hc J hJ g hg Bs hB w v
  unfold capLft capRep qmFrev qmF
  simp only [Finset.sum_apply, Pi.smul_apply, _root_.sum_apply, _root_.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have e1 := LeftTypeActionHermitianCurvature.fold_left hD hπ hc hJ
    (List.ofFn fun j : Fin m => ((if σ j = j then w - ((j : ℕ) : ℂ) else 0 : ℂ), unitB (Hpk k r) Bs (σ j) j))
    (by
      intro p hp
      rw [List.mem_ofFn] at hp
      obtain ⟨j, rfl⟩ := hp
      exact QrD.frame_lie hB (σ j) j) J 1 (fun x _ => (ContinuousLinearMap.id_comp _).symm) g hg v
  simp only [List.map_ofFn, Function.comp_def, ite_smul, zero_smul] at e1
  simp only [id]
  rw [e1]
  rfl

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LieBasisHolds
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LieBasisConstruction

def lieSubR (k r : ℕ) : Submodule ℝ (B.Mat k r) where
  carrier := {X | B.inLie k r X}
  add_mem' := by
    intro X Y hX hY
    unfold B.inLie at *
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    calc _ = (Xᴴ * _ + _ * X) + (Yᴴ * _ + _ * Y) := by abel
      _ = 0 := by rw [hX, hY, add_zero]
  zero_mem' := by
    unfold B.inLie
    simp
  smul_mem' := by
    intro c X hX
    unfold B.inLie at *
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

end LieBasisConstruction

theorem lie_basis_holds : LieBasis := by
  intro k r
  let S := LieBasisConstruction.lieSubR k r
  let b := Module.finBasis ℝ S
  let L0 : (Fin (Module.finrank ℝ S) → ℝ) →ₗ[ℝ] B.Mat k r := S.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hinj : LinearMap.ker L0 = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact S.injective_subtype.comp b.equivFun.symm.injective
  obtain ⟨M0, hM0⟩ := L0.exists_leftInverse_of_injective hinj
  have hML : ∀ y, M0 (L0 y) = y := fun y => LinearMap.congr_fun hM0 y
  refine ⟨Module.finrank ℝ S, LinearMap.toContinuousLinearMap L0, LinearMap.toContinuousLinearMap M0,
    fun x => (b.equivFun.symm x).2, fun x => hML x, fun X hX => ?_⟩
  have e : L0 (b.equivFun ⟨X, hX⟩) = X := by simp [L0]
  show L0 (M0 X) = X
  calc L0 (M0 X) = L0 (M0 (L0 (b.equivFun ⟨X, hX⟩))) := by rw [e]
    _ = X := by rw [hML, e]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LimitOfModuleForms
section
open Filter Topology

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem limit_of_module_forms : Formalism.FourierDecayAlt.KB.FormLimit := by
  intro Cb
  obtain ⟨Cl, _, hL⟩ := PBE.belowTop
  obtain ⟨Ct, hT⟩ := PBE.formLimit_top Cb
  refine ⟨max Cl Ct, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P0 p f χ ε A N cut hDD hχ hε hf hfA hA hcut
  refine ⟨fun n => PBE.cutCpt P0 p.T.base f χ ε cut hχ hε hf hcut n, ?_⟩
  intro i w hwc hw a b
  have hX : 0 ≤ ((P0.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P0.r : ℝ) + P0.k + 1) ^ 2 + (2 * (P0.r : ℝ) + P0.k + 1) ^ 3) := by
    positivity
  rcases lt_trichotomy i (P0.r + 1) with hlt | heq | hgt
  · exact hL (max Cl Ct) (le_max_left _ _) Wp Wq P0 p f χ ε A N cut hχ hε hf hfA hA hcut i (by omega) w hw a b
  · subst heq
    refine hT Wp Wq P0 p f χ ε A N cut hDD hχ hε hf hfA ?_ hcut w hwc hw a b
    refine le_trans ?_ hA
    have := mul_le_mul_of_nonneg_right (le_max_right Cl Ct) hX
    nlinarith
  · have h0 : ∀ F, p.RR F i w a b = 0 := by
      intro F
      unfold KB.Pl.RR D.RRplace
      split_ifs <;> first | rfl | (exfalso; omega)
    simp only [h0]
    exact tendsto_const_nhds

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MinorCellOfParts
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def RightRuleE : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (D : Set (Q.Mx k r)) (f : Q.Mx k r → E), inWb k r z' → IsOpen D → Q.SmoothLev k r 0 D f →
    Q.RightEq k r z' 0 D f → ∀ g ∈ Q.Glev k r 0 ∩ D, ∀ a b : Fin r, a.val < b.val →
      Q.EH k r (eI k r a) (eI k r b) f g = (if b.val = a.val + 1 then (1 : ℂ) else 0) • f g

def LeftRuleCell : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (D : Set (Q.Mx k r)) (f : Q.Mx k r → E), inWb k r z → IsOpen D →
    (∀ g ∈ Q.Glev k r 0 ∩ D, ∀ n ∈ Q.Nlev k r 0, n * g ∈ D) → Q.SmoothLev k r 0 D f → Q.LeftEq k r z 0 D f →
    ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D → ∀ a b : Fin r, b.val < a.val →
      Q.EH k r (eI k r a) (eI k r b) f (Q.wCell k r (Fin.last r) c * g) =
        (if a.val = b.val + 1 then c a / c b else 0) • f (Q.wCell k r (Fin.last r) c * g)

def TorusCell : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (D : Set (Q.Mx k r)) (f : Q.Mx k r → E),
    IsOpen D → Q.SmoothLev k r 0 D f → ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r),
    Q.wCell k r (Fin.last r) c * g ∈ D → ∀ l : Fin r,
      Q.EH k r (eI k r l) (eI k r l) f (Q.wCell k r (Fin.last r) c * g) =
        pOp l (fun c' => f (Q.wCell k r (Fin.last r) c' * g)) c

def GaugeP : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (r : ℕ) (n : Fin r → ℕ) (H : (Fin r → ℂ) → E)
    (c : Fin r → ℂ), c ∈ OmX r → DifferentiableAt ℝ H c → ∀ l : Fin r,
      pOp l (fun c' => ((∏ a, ‖c' a‖ ^ n a : ℝ) : ℂ) • H c') c =
        ((∏ a, ‖c a‖ ^ n a : ℝ) : ℂ) • (pOp l H c + ((n l : ℂ) / 2) • H c)

def MinorCellOfParts : Prop := RightRuleE → LeftRuleCell → TorusCell → GaugeP → MinorCell

end Formalism.FourierDecayAlt.P.PBN
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NilpotentLieFiniteHolds
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

theorem nilpotent_lie_finite_holds : LieNFin := by
  intro k r
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℝ (JfS.lieOf (Nset k r))
  have hfin : b.Finite := hli.setFinite
  have : Fintype b := hfin.fintype
  let Xs : Fin (Fintype.card b) → B.Mat k r := fun i => ((Fintype.equivFin b).symm i : B.Mat k r)
  have hrange : Set.range Xs = b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ((Fintype.equivFin b).symm i).2
    · intro hx
      refine ⟨Fintype.equivFin b ⟨x, hx⟩, ?_⟩
      simp [Xs]
  refine ⟨Fintype.card b, Xs, fun i => hbS ((Fintype.equivFin b).symm i).2, fun X hX => ⟨?_, ?_⟩⟩
  · exact LieSplitPf.lieHpk_of (fun t => (hX t).1)
  · have hmem : X ∈ Submodule.span ℝ (Set.range Xs) := by
      rw [hrange, hspan]
      exact Submodule.subset_span hX
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
    refine ⟨a, ?_⟩
    rw [← ha]
    refine Finset.sum_congr rfl fun i _ => ?_
    ext p q
    simp [Matrix.smul_apply, Complex.real_smul]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SymbolOperatorLinearHolds
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem symbol_operator_linear_holds : SOpLin := by
  intro d S T c O hST hS hT
  obtain ⟨o, a⟩ := S
  obtain ⟨o', b⟩ := T
  simp only at hST
  subst hST
  refine ⟨⟨o, fun k w x => c * a k w x + b k w x⟩, rfl, ?_, ?_, ?_⟩
  · intro i w
    exact (contDiffOn_const.mul (hS i w)).add (hT i w)
  · intro u x
    simp only [SOp.app, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun w _ => ?_
    ring
  · intro x ξ
    simp only [SOp.symb, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

