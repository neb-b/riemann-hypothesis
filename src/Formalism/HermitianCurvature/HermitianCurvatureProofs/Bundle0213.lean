module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0201
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0112
public import Formalism.FormalDegreeBessel.Bundle0001
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0197
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ResGContDiffAt
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN.MC

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section cell

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]


open Classical in
def resW (h : Mx k r → V) (g : Mx k r) : (Fin r → ℂ) → V :=
  fun c' => if c' ∈ OmX r then resG k r (Fin.last r) h c' g else 0

theorem resG_contDiffAt (Bs : B.RealPlaceData k r Wp Wq) {h : Mx k r → V}
    (hh : SmoothLev k r 0 (OmPlus k r Bs.z Bs.z') h) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r))
    (hG : 0 < GGl k r Bs.z Bs.z' g) {c₀ : Fin r → ℂ} (hc₀ : c₀ ∈ OmX r) :
    ContDiffAt ℝ ∞ (fun c' => resG k r (Fin.last r) h c' g) c₀ := by
  have hsf := Formalism.FourierDecayAlt.P5.Rad.sf_resG hh
  obtain ⟨U, F, hU, hxU, hF, hE⟩ := hsf (c₀, g)
    ⟨hc₀, Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus Bs.z_mem Bs.z'_mem hc₀ hg hG⟩ hg
  have hpre : IsOpen ((fun c : Fin r → ℂ => (c, g)) ⁻¹' U) := hU.preimage (by fun_prop)
  have hmem : c₀ ∈ (fun c : Fin r → ℂ => (c, g)) ⁻¹' U := hxU
  have hcd : ContDiffAt ℝ ∞ (fun c : Fin r → ℂ => F (c, g)) c₀ := by
    have h1 : ContDiffOn ℝ ∞ (fun c : Fin r → ℂ => F (c, g)) ((fun c : Fin r → ℂ => (c, g)) ⁻¹' U) :=
      hF.comp (by fun_prop : ContDiff ℝ ∞ (fun c : Fin r → ℂ => (c, g))).contDiffOn (fun c hc => hc)
    exact h1.contDiffAt (hpre.mem_nhds hmem)
  refine hcd.congr_of_eventuallyEq ?_
  filter_upwards [hpre.mem_nhds hmem] with c hc
  exact hE (c, g) hc hg

theorem resG_wsm (Bs : B.RealPlaceData k r Wp Wq) {h : Mx k r → V} (hh : SmoothLev k r 0 (OmPlus k r Bs.z Bs.z') h)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (hG : 0 < GGl k r Bs.z Bs.z' g) :
    resW h g ∈ WSm r V := by
  refine ⟨?_, fun x hx => by simp [resW, hx]⟩
  intro c hc
  have h1 := (resG_contDiffAt Bs hh hg hG hc).contDiffWithinAt (s := OmX r)
  refine h1.congr (fun c' hc' => by simp [resW, hc']) (by simp [resW, hc])

theorem wsm_resG_eq (h : Mx k r → V) (g : Mx k r) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    resW h g c = resG k r (Fin.last r) h c g := by
  simp [resW, hc]

theorem cell_diff (Bs : B.RealPlaceData k r Wp Wq) {h : Mx k r → V} (hh : SmoothLev k r 0 (OmPlus k r Bs.z Bs.z') h)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (hG : 0 < GGl k r Bs.z Bs.z' g) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) : DifferentiableAt ℝ (fun c' => h (wCell k r (Fin.last r) c' * g)) c := by
  have hgl : ∀ c' ∈ OmX r, wCell k r (Fin.last r) c' * g ∈ Glev k r 0 := fun c' hc' =>
    Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc' _) (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hg)
  obtain ⟨U, F, hU, hgU, hF, hE⟩ := hh (wCell k r (Fin.last r) c * g)
    ⟨hgl c hc, Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus Bs.z_mem Bs.z'_mem hc hg hG⟩
  have hw : ContDiffOn ℝ ∞ (fun c' : Fin r → ℂ => wCell k r (Fin.last r) c' * g) (OmX r) :=
    Formalism.FourierDecayAlt.P.Qx3.cdo_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_smooth _) contDiffOn_const
  have hwc : ContinuousAt (fun c' : Fin r → ℂ => wCell k r (Fin.last r) c' * g) c :=
    (hw.continuousOn).continuousAt ((Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc)
  have hd : DifferentiableAt ℝ (fun c' => F (wCell k r (Fin.last r) c' * g)) c := by
    have hFd : DifferentiableAt ℝ F (wCell k r (Fin.last r) c * g) :=
      (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
    have hwd : DifferentiableAt ℝ (fun c' : Fin r → ℂ => wCell k r (Fin.last r) c' * g) c :=
      (hw.differentiableOn (by simp)).differentiableAt ((Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc)
    exact hFd.comp c hwd
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [(Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc, hwc.preimage_mem_nhds (hU.mem_nhds hgU)]
    with c' h1 h2
  exact hE _ h2 (hgl c' h1)

end cell

section chain

variable {r : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem wsm_sub {f g : (Fin r → ℂ) → V} (hf : f ∈ WSm r V) (hg : g ∈ WSm r V) : f - g ∈ WSm r V :=
  (WSm r V).sub_mem hf hg

theorem opL_mem (l : Fin r) (i : Fin 6) {f : (Fin r → ℂ) → V} (hf : f ∈ WSm r V) : opL l i f ∈ WSm r V :=
  preserved_operators_holds r V l i f hf

theorem opL_sub (l : Fin r) (i : Fin 6) {f g : (Fin r → ℂ) → V} (hf : f ∈ WSm r V) (hg : g ∈ WSm r V) :
    opL l i (f - g) = opL l i f - opL l i g := by
  have hng : (-1 : ℂ) • g ∈ WSm r V := (WSm r V).smul_mem _ hg
  have e : f - g = f + (-1 : ℂ) • g := by rw [neg_one_smul, sub_eq_add_neg]
  rw [e, (linear_operators_holds r V l i f _ 1 hf hng).1, (linear_operators_holds r V l i g g (-1) hg hg).2, neg_one_smul,
    sub_eq_add_neg]

theorem opL_add (l : Fin r) (i : Fin 6) {f g : (Fin r → ℂ) → V} (hf : f ∈ WSm r V) (hg : g ∈ WSm r V) :
    opL l i (f + g) = opL l i f + opL l i g :=
  (linear_operators_holds r V l i f g 1 hf hg).1

theorem opL_smul (l : Fin r) (i : Fin 6) {f : (Fin r → ℂ) → V} (hf : f ∈ WSm r V) (a : ℂ) :
    opL l i (a • f) = a • opL l i f :=
  (linear_operators_holds r V l i f f a hf hf).2

theorem pOp_zero (l : Fin r) : pOp l (fun _ : Fin r → ℂ => (0 : V)) = fun _ => 0 := by
  funext x; unfold pOp wirt; split_ifs <;> simp

theorem vAB_mem (y : ℂ) : ∀ (i : ℕ) {G : (Fin r → ℂ) → V}, G ∈ WSm r V →
    (vAB r y i).1 G ∈ WSm r V ∧ (vAB r y i).2 G ∈ WSm r V := by
  intro i
  induction i with
  | zero =>
    intro G hG
    exact ⟨hG, (WSm r V).zero_mem⟩
  | succ i ih =>
    intro G hG
    obtain ⟨hA, hB⟩ := ih hG
    by_cases hi : i < r
    · simp only [vAB, dite_eq_left hi]
      refine ⟨wsm_sub ((WSm r V).add_mem ((WSm r V).smul_mem y hA) (opL_mem ⟨i, hi⟩ 0 hA))
        (opL_mem ⟨i, hi⟩ 1 hB), opL_mem ⟨i, hi⟩ 2 hA⟩
    · simp only [vAB, dite_eq_right hi]
      exact ⟨hA, hB⟩

theorem vAB_lin (y : ℂ) : ∀ (i : ℕ) {G₁ G₂ : (Fin r → ℂ) → V}, G₁ ∈ WSm r V → G₂ ∈ WSm r V → ∀ s : ℂ,
    (vAB r y i).1 (G₁ + s • G₂) = (vAB r y i).1 G₁ + s • (vAB r y i).1 G₂ ∧
      (vAB r y i).2 (G₁ + s • G₂) = (vAB r y i).2 G₁ + s • (vAB r y i).2 G₂ := by
  intro i
  induction i with
  | zero =>
    intro G₁ G₂ _ _ s
    exact ⟨rfl, by show (0 : (Fin r → ℂ) → V) = 0 + s • 0; simp⟩
  | succ i ih =>
    intro G₁ G₂ h₁ h₂ s
    obtain ⟨ih1, ih2⟩ := ih h₁ h₂ s
    obtain ⟨hA₁, hB₁⟩ := vAB_mem y i h₁
    obtain ⟨hA₂, hB₂⟩ := vAB_mem y i h₂
    have hsA := (WSm r V).smul_mem s hA₂
    have hsB := (WSm r V).smul_mem s hB₂
    by_cases hi : i < r
    · simp only [vAB, dite_eq_left hi]
      rw [ih1, ih2]
      refine ⟨?_, ?_⟩
      · have e1 : pOp ⟨i, hi⟩ ((vAB r y i).1 G₁ + s • (vAB r y i).1 G₂) =
            pOp ⟨i, hi⟩ ((vAB r y i).1 G₁) + s • pOp ⟨i, hi⟩ ((vAB r y i).1 G₂) := by
          rw [show pOp ⟨i, hi⟩ = opL ⟨i, hi⟩ 0 from rfl, opL_add _ _ hA₁ hsA, opL_smul _ _ hA₂]
        have e2 : cOp ⟨i, hi⟩ ((vAB r y i).2 G₁ + s • (vAB r y i).2 G₂) =
            cOp ⟨i, hi⟩ ((vAB r y i).2 G₁) + s • cOp ⟨i, hi⟩ ((vAB r y i).2 G₂) := by
          rw [show cOp ⟨i, hi⟩ = opL ⟨i, hi⟩ 1 from rfl, opL_add _ _ hB₁ hsB, opL_smul _ _ hB₂]
        rw [e1, e2]
        funext x
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_add, smul_sub]
        rw [smul_comm y s]
        abel
      · rw [show ciOp ⟨i, hi⟩ = opL ⟨i, hi⟩ 2 from rfl, opL_add _ _ hA₁ hsA, opL_smul _ _ hA₂]
    · simp only [vAB, dite_eq_right hi]
      exact ⟨ih1, ih2⟩

theorem vAB_comm (y : ℂ) (j : Fin r) : ∀ (i : ℕ), i ≤ j.val → ∀ {G : (Fin r → ℂ) → V}, G ∈ WSm r V →
    (vAB r y i).1 G ∈ WSm r V ∧ (vAB r y i).2 G ∈ WSm r V ∧
      (vAB r y i).1 (pOp j G) = pOp j ((vAB r y i).1 G) ∧ (vAB r y i).2 (pOp j G) = pOp j ((vAB r y i).2 G) := by
  intro i
  induction i with
  | zero =>
    intro _ G hG
    exact ⟨hG, (WSm r V).zero_mem, rfl, by simp only [vAB]; exact (pOp_zero j).symm⟩
  | succ i ih =>
    intro hij G hG
    obtain ⟨hA, hB, c1, c2⟩ := ih (by omega) hG
    have hpG : pOp j G ∈ WSm r V := opL_mem j 0 hG
    have hi : i < r := by have := j.isLt; omega
    have hne : (⟨i, hi⟩ : Fin r) ≠ j := by intro h; rw [← h] at hij; simp at hij
    obtain ⟨hm1, hm2⟩ := vAB_mem y (i + 1) hG
    refine ⟨hm1, hm2, ?_, ?_⟩
    · simp only [vAB, dite_eq_left hi]
      rw [c1, c2]
      have hpA : pOp ⟨i, hi⟩ ((vAB r y i).1 G) ∈ WSm r V := opL_mem _ 0 hA
      have hcB : cOp ⟨i, hi⟩ ((vAB r y i).2 G) ∈ WSm r V := opL_mem _ 1 hB
      have hyA : y • (vAB r y i).1 G ∈ WSm r V := (WSm r V).smul_mem y hA
      rw [show pOp j = opL j 0 from rfl, opL_sub _ _ ((WSm r V).add_mem hyA hpA) hcB,
        opL_add _ _ hyA hpA, opL_smul _ _ hA]
      have k1 : opL j 0 (pOp ⟨i, hi⟩ ((vAB r y i).1 G)) = pOp ⟨i, hi⟩ (opL j 0 ((vAB r y i).1 G)) :=
        (commuting_functional_holds r V j ⟨i, hi⟩ 0 0 _ hA (Or.inl (Ne.symm hne)))
      have k2 : opL j 0 (cOp ⟨i, hi⟩ ((vAB r y i).2 G)) = cOp ⟨i, hi⟩ (opL j 0 ((vAB r y i).2 G)) :=
        (commuting_functional_holds r V j ⟨i, hi⟩ 0 1 _ hB (Or.inl (Ne.symm hne)))
      rw [k1, k2]
    · simp only [vAB, dite_eq_left hi]
      rw [c1]
      exact (commuting_functional_holds r V j ⟨i, hi⟩ 0 2 _ hA (Or.inl (Ne.symm hne))).symm

end chain

end Formalism.FourierDecayAlt.P.PBN.MC
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RightGeneratorWordEvaluation
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix Filter Topology
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace FExpR

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Rep (m : ℕ∞) (O : Set (B.Mat k r)) (φ : B.Mat k r → E) : Prop :=
  ∃ F : B.Mat k r → E, ContDiffOn ℝ (m : WithTop ℕ∞) F O ∧ ∀ x ∈ O, x ∈ B.GV k r → φ x = F x

theorem rep_mono {m m' : ℕ∞} (hmm : m ≤ m') {O : Set (B.Mat k r)} {φ : B.Mat k r → E} (h : Rep m' O φ) :
    Rep m O φ := by
  obtain ⟨F, hF, he⟩ := h
  exact ⟨F, hF.of_le (by exact_mod_cast hmm), he⟩

theorem rep_RdV {m : ℕ∞} {O : Set (B.Mat k r)} (hO : IsOpen O) {φ : B.Mat k r → E} {X : B.Mat k r}
    (hX : B.inLie k r X) (h : Rep (m + 1) O φ) : Rep m O (RdV X φ) := by
  obtain ⟨F, hF, he⟩ := h
  refine ⟨fun x => fderiv ℝ F x (x * X), ?_, ?_⟩
  · have h1 := hF.fderiv_of_isOpen (m := (m : WithTop ℕ∞)) hO (by push_cast; exact le_rfl)
    exact h1.clm_apply (mulRightRealCLM X).contDiff.contDiffOn
  · intro x hx hxG
    have hd : DifferentiableAt ℝ F x :=
      (hF.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hx)
    exact (Formalism.FourierDecayAlt.P.B5.hasDerivAt_of_ext hO hx hxG hX hd he).deriv

theorem rep_Rw {O : Set (B.Mat k r)} (hO : IsOpen O) {f : B.Mat k r → E} {N : ℕ} (h : Rep (N : ℕ∞) O f)
    (w : List (B.Mat k r)) (hw : ∀ X ∈ w, B.inLie k r X) (m : ℕ) (hle : m + w.length ≤ N) :
    Rep (m : ℕ∞) O (B.Rw w f) := by
  induction w generalizing m with
  | nil => exact rep_mono (by exact_mod_cast (by simpa using hle)) h
  | cons X w ih =>
    have e : B.Rw (X :: w) f = RdV X (B.Rw w f) := rfl
    rw [e]
    apply rep_RdV hO (hw X (by simp))
    have := ih (fun Y hY => hw Y (by simp [hY])) (m + 1) (by simp at hle; omega)
    exact_mod_cast this

theorem rep_hasDerivAt {O : Set (B.Mat k r)} (hO : IsOpen O) {φ : B.Mat k r → E} {x X : B.Mat k r}
    (hx : x ∈ O) (hxG : x ∈ B.GV k r) (hX : B.inLie k r X) (h : Rep ((1 : ℕ) : ℕ∞) O φ) :
    HasDerivAt (fun t : ℝ => φ (x * NormedSpace.exp ((t : ℂ) • X))) (RdV X φ x) 0 := by
  obtain ⟨F, hF, he⟩ := h
  have hd : DifferentiableAt ℝ F x := (hF.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hx)
  exact (Formalism.FourierDecayAlt.P.B5.hasDerivAt_of_ext hO hx hxG hX hd he).differentiableAt.hasDerivAt

theorem rdV_congr {O : Set (B.Mat k r)} (hO : IsOpen O) {φ ψ : B.Mat k r → E}
    (he : ∀ y ∈ O, y ∈ B.GV k r → φ y = ψ y) {x X : B.Mat k r} (hx : x ∈ O) (hxG : x ∈ B.GV k r)
    (hX : B.inLie k r X) : RdV X φ x = RdV X ψ x := by
  show deriv (fun t : ℝ => φ (x * NormedSpace.exp ((t : ℂ) • X))) 0 =
    deriv (fun t : ℝ => ψ (x * NormedSpace.exp ((t : ℂ) • X))) 0
  apply Filter.EventuallyEq.deriv_eq
  have hγ := hasDerivAt_mul_exp_smul_zero x X
  have hγ0 := Formalism.FourierDecayAlt.P.B5.curve_zero x X
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, x * NormedSpace.exp ((t : ℂ) • X) ∈ O :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hO.mem_nhds hx)
  filter_upwards [hmem] with t ht
  exact he _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hxG hX t)

theorem wsEvalR_append (a b : List (Polynomial ℂ × List (B.Mat k r))) (u : ℂ) (f : B.Mat k r → E)
    (x : B.Mat k r) : wsEvalR (a ++ b) u f x = wsEvalR a u f x + wsEvalR b u f x := by
  simp [wsEvalR, List.map_append, List.sum_append]

theorem wsEvalR_flatMap {α : Type} (F : α → List (Polynomial ℂ × List (B.Mat k r))) (u : ℂ)
    (f : B.Mat k r → E) (x : B.Mat k r) :
    ∀ L : List α, wsEvalR (L.flatMap F) u f x = (L.map fun a => wsEvalR (F a) u f x).sum
  | [] => by simp [wsEvalR]
  | a :: L => by
    rw [List.flatMap_cons, wsEvalR_append, wsEvalR_flatMap F u f x L, List.map_cons, List.sum_cons]

theorem wsEvalR_map_mul (p : Polynomial ℂ) (φ : List (B.Mat k r) → List (B.Mat k r)) (u : ℂ)
    (f : B.Mat k r → E) (x : B.Mat k r) :
    ∀ ws : List (Polynomial ℂ × List (B.Mat k r)),
      wsEvalR (ws.map fun t => (p * t.1, φ t.2)) u f x = p.eval u • wsEvalR (ws.map fun t => (t.1, φ t.2)) u f x
  | [] => by simp [wsEvalR]
  | t :: ws => by
    have ih := wsEvalR_map_mul p φ u f x ws
    simp only [wsEvalR, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, smul_add, Polynomial.eval_mul, mul_smul]

theorem fexp_words : ∀ (gens : List (GenW k r)), (∀ gn ∈ gens, ∀ dX ∈ gn.2, B.inLie k r dX.2) →
    ∀ t ∈ fexp gens, t.2.length ≤ gens.length ∧ ∀ X ∈ t.2, B.inLie k r X
  | [], _, t, ht => by
    simp only [fexp, List.mem_singleton] at ht
    subst ht
    simp
  | gn :: gs, hL, t, ht => by
    have hL' : ∀ g ∈ gs, ∀ dX ∈ g.2, B.inLie k r dX.2 := fun g hg => hL g (List.mem_cons_of_mem _ hg)
    have ih := fexp_words gs hL'
    simp only [fexp, List.mem_append, List.mem_map, List.mem_flatMap] at ht
    rcases ht with ⟨s, hs, rfl⟩ | ⟨dX, hdX, s, hs, rfl⟩
    · have := (ih s hs).1
      refine ⟨?_, (ih s hs).2⟩
      show s.2.length ≤ (gn :: gs).length
      simp only [List.length_cons]; omega
    · have := (ih s hs).1
      refine ⟨?_, ?_⟩
      · show (dX.2 :: s.2).length ≤ (gn :: gs).length
        simp only [List.length_cons]; omega
      · intro X hX
        rcases List.mem_cons.1 hX with rfl | hX
        · exact hL gn (by simp) dX hdX
        · exact (ih s hs).2 X hX

theorem ws_hasDerivAt {O : Set (B.Mat k r)} (hO : IsOpen O) {x X : B.Mat k r} (hx : x ∈ O)
    (hxG : x ∈ B.GV k r) (hX : B.inLie k r X) (u : ℂ) (f : B.Mat k r → E) :
    ∀ ws : List (Polynomial ℂ × List (B.Mat k r)), (∀ t ∈ ws, Rep ((1 : ℕ) : ℕ∞) O (B.Rw t.2 f)) →
      HasDerivAt (fun s : ℝ => wsEvalR ws u f (x * NormedSpace.exp ((s : ℂ) • X)))
        (wsEvalR (ws.map fun t => (t.1, X :: t.2)) u f x) 0
  | [], _ => by
    have e : ∀ y, wsEvalR ([] : List (Polynomial ℂ × List (B.Mat k r))) u f y = (0 : E) := fun y => by
      simp [wsEvalR]
    simp only [List.map_nil, e]
    exact hasDerivAt_const _ _
  | t :: ws, h => by
    have h1 := (rep_hasDerivAt hO hx hxG hX (h t (by simp))).const_smul (t.1.eval u)
    have h2 := ws_hasDerivAt hO hx hxG hX u f ws (fun s hs => h s (List.mem_cons_of_mem _ hs))
    have e1 : (fun s : ℝ => wsEvalR (t :: ws) u f (x * NormedSpace.exp ((s : ℂ) • X))) =
        fun s : ℝ => t.1.eval u • B.Rw t.2 f (x * NormedSpace.exp ((s : ℂ) • X)) +
          wsEvalR ws u f (x * NormedSpace.exp ((s : ℂ) • X)) := by
      funext s; simp only [wsEvalR, List.map_cons, List.sum_cons]
    have e2 : wsEvalR ((t :: ws).map fun t => (t.1, X :: t.2)) u f x =
        t.1.eval u • RdV X (B.Rw t.2 f) x + wsEvalR (ws.map fun t => (t.1, X :: t.2)) u f x := by
      simp only [wsEvalR, List.map_cons, List.sum_cons] <;> rfl
    rw [e1, e2]
    exact h1.add h2

theorem right_generator_word_evaluation (u : ℂ) : ∀ (gens : List (GenW k r)) (O : Set (B.Mat k r)) (f : B.Mat k r → E), IsOpen O →
    (∀ gn ∈ gens, ∀ dX ∈ gn.2, B.inLie k r dX.2) → Rep (gens.length : ℕ∞) O f → ∀ x ∈ O, x ∈ B.GV k r →
      (gens.map (fun gn => genOpR gn u)).foldr (fun T h => T h) f x = wsEvalR (fexp gens) u f x
  | [], O, f, _, _, _, x, _, _ => by simp [fexp, wsEvalR, B.Rw]
  | gn :: gs, O, f, hO, hL, hf, x, hx, hxG => by
    have hL' : ∀ g ∈ gs, ∀ dX ∈ g.2, B.inLie k r dX.2 := fun g hg => hL g (List.mem_cons_of_mem _ hg)
    have hf' : Rep (gs.length : ℕ∞) O f := rep_mono (by exact_mod_cast (by simp : gs.length ≤ (gn :: gs).length)) hf
    have IH := right_generator_word_evaluation u gs O f hO hL' hf'
    have hW := fexp_words gs hL'
    have hrep : ∀ t ∈ fexp gs, Rep ((1 : ℕ) : ℕ∞) O (B.Rw t.2 f) := fun t ht =>
      rep_Rw hO hf t.2 (hW t ht).2 1 (by have := (hW t ht).1; simp only [List.length_cons]; omega)
    have hD : ∀ X, B.inLie k r X → RdV X (wsEvalR (fexp gs) u f) x =
        wsEvalR ((fexp gs).map fun t => (t.1, X :: t.2)) u f x := fun X hX =>
      (ws_hasDerivAt hO hx hxG hX u f (fexp gs) hrep).deriv
    have hR : wsEvalR (fexp (gn :: gs)) u f x = gn.1.eval u • wsEvalR (fexp gs) u f x +
        (gn.2.map fun dX => dX.1 • wsEvalR ((fexp gs).map fun t => (t.1, dX.2 :: t.2)) u f x).sum := by
      simp only [fexp]
      rw [wsEvalR_append, wsEvalR_flatMap]
      congr 1
      · have := wsEvalR_map_mul gn.1 id u f x (fexp gs)
        simpa using this
      · congr 1
        apply List.map_congr_left
        intro dX _
        have := wsEvalR_map_mul (Polynomial.C dX.1) (fun w => dX.2 :: w) u f x (fexp gs)
        simpa using this
    set Φ := (gs.map fun gn => genOpR gn u).foldr (fun T h => T h) f with hΦdef
    have hΦ : ∀ X, B.inLie k r X → RdV X Φ x = RdV X (wsEvalR (fexp gs) u f) x := fun X hX =>
      rdV_congr hO (fun y hy hyG => IH y hy hyG) hx hxG hX
    rw [hR]
    change gn.1.eval u • Φ x + (gn.2.map fun dX => dX.1 • RdV dX.2 Φ x).sum = _
    rw [IH x hx hxG]
    congr 2
    apply List.map_congr_left
    intro dX hdX
    have hX := hL gn (by simp) dX hdX
    rw [hΦ dX.2 hX, hD dX.2 hX]

end FExpR

theorem right_exponential_evaluation : FExpEvalR := by
  intro k r E _ _ gens u UU f hL hf g hg hgG
  obtain ⟨U, f', hU, hgU, hf', he⟩ := hf g hg
  exact FExpR.right_generator_word_evaluation u gens U f hU hL ⟨f', hf', he⟩ g hgU hgG

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

