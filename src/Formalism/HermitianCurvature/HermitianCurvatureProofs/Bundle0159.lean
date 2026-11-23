module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0151
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDensityModerateGrowth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0158
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0156
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0051
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0061
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvOther
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0064
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0070
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0157
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdjCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCongrRight
section
open Matrix MeasureTheory
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section comp

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} [Fintype ι]

theorem op_comp (b : Bool) {X : Mat k r} (hX : inLie k r X) {G : Mat k r → (ι → E)}
    (hG : CkOn ((1 : ℕ) : ℕ∞) (GV k r) G) (i : ι) {g : Mat k r} (hg : g ∈ GV k r) :
    P.B4.op b X (fun h => G h i) g = P.B4.op b X G g i := by
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hG g hg
  have hc0 : ContDiffOn ℝ (((0 + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) f' U := by simpa using hc
  have e1 := P.B4.op_eq_op' 0 b hU hc0 hff hX g hgU hg
  let pr : (ι → E) →L[ℝ] E := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => E) i).restrictScalars ℝ
  have hc' : ContDiffOn ℝ (((0 + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) (fun h => f' h i) U :=
    pr.contDiff.comp_contDiffOn hc0
  have hff' : ∀ h ∈ U, h ∈ GV k r → (fun h => G h i) h = (fun h => f' h i) h := fun h hU' hG' => by
    simp only [hff h hU' hG']
  have e2 := P.B4.op_eq_op' 0 b hU hc' hff' hX g hgU hg
  rw [e2, e1]
  unfold P.B4.op'
  have hd : DifferentiableAt ℝ f' g :=
    (hc0.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have hfd : HasFDerivAt (fun h => f' h i) (pr.comp (fderiv ℝ f' g)) g :=
    pr.hasFDerivAt.comp g hd.hasFDerivAt
  rw [hfd.fderiv]
  rfl

theorem W_comp (w : List (Bool × Mat k r)) (hw : P.B4.AllLie w) {G : Mat k r → (ι → E)}
    (hG : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) G) (i : ι) :
    ∀ g ∈ GV k r, P.B4.W w (fun h => G h i) g = P.B4.W w G g i := by
  induction w with
  | nil => intro g _; rfl
  | cons x w ih =>
    intro g hg
    have hw' : P.B4.AllLie w := fun y hy => hw y (List.mem_cons_of_mem _ hy)
    have hl : w.length ≤ (x :: w).length := by simp
    have hl1 : 1 + w.length ≤ (x :: w).length := by simp; omega
    rw [P.B4.W_cons, P.B4.W_cons,
      P.B4.op_congr x.1 (hw x List.mem_cons_self) (ih hw' (P.B4.ckOn_mono hl hG)) g hg]
    exact op_comp x.1 (hw x List.mem_cons_self) (P.B4.smooth_on_of_word_derivatives w hw' 1 (P.B4.ckOn_mono hl1 hG)) i hg

theorem ckOn_comp {m : ℕ∞} {G : Mat k r → (ι → E)} (hG : CkOn m (GV k r) G) (i : ι) :
    CkOn m (GV k r) (fun h => G h i) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hG g₀ hg₀
  let pr : (ι → E) →L[ℝ] E := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => E) i).restrictScalars ℝ
  exact ⟨U, fun h => f' h i, hU, hgU, pr.contDiff.comp_contDiffOn hc, fun g hg hgG => by simp only [hff g hg hgG]⟩

theorem ccle_comp {A c : ℝ} {m : ℕ} {G : Mat k r → (ι → E)} (hG : CCle A m G c) (i : ι) :
    CCle A m (fun h => G h i) c := by
  refine ⟨ckOn_comp hG.1 i, fun u v hu hv hl g hg => ?_⟩
  have hw : P.B4.AllLie (P.B4.lr u v) := by
    intro x hx
    simp only [P.B4.lr, List.mem_append, List.mem_map] at hx
    rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
    · exact (hu X hX).1
    · exact (hv X hX).1
  have hlen : (P.B4.lr u v).length ≤ m := by simp [P.B4.lr]; omega
  have e : dLR u v (fun h => G h i) g = dLR u v G g i := by
    rw [P.B4.dLR_eq, P.B4.dLR_eq]
    exact W_comp _ hw (P.B4.ckOn_mono hlen hG.1) i g hg
  rw [e]
  refine le_trans ?_ (hG.2 u v hu hv hl g hg)
  have hgN : 0 ≤ gN g ^ A := Real.rpow_nonneg (Real.sqrt_nonneg _) A
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (dLR u v G g) i) hgN

end comp

section beta

open Formalism.FourierDecayAlt.P.JCx2 Filter

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem beta_congr_right (D : RealPlaceData k r Wp Wq) {F G G₂ : Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ GV k r, G g = G₂ g) : beta D F G = beta D F G₂ := by
  unfold B.beta betaBig
  refine integral_congr_ae ?_
  filter_upwards [ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.big_cell_orbit_set k r Wp Wq D)] with q hq
  by_cases hQ : q ∈ B.Qset D
  · have hg : bigCell k r q.1 (D.μsec q.2) ∈ GV k r := (hq hQ).1
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F (bigCell k r q.1 (D.μsec q.2)))) =
      (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G₂ (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F (bigCell k r q.1 (D.μsec q.2))))
    rw [sq_jf_congr D h hg]
  · have hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 :=
      le_antisymm (not_lt.1 hQ) (sq_bcWeight_nonneg _ _ q)
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _ = (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _
    rw [hw]
    simp

end beta

end Formalism.FourierDecayAlt.P.FormNormSumIdentities

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.JCx2

theorem form_model : Formalism.FourierDecayAlt.P.FormNormSumIdentities.FormModel := by
  intro Wp Wq _ _ _ _ _ _ P0 T sg j w a mm ε' Sg hε' ha hmm hmm5 hSg V _ _ Mo
  let comp : V → Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp) := fun u e γ => Mo.ev u γ e
  have hcc : ∀ u e, CCle a mm (comp u e) ‖u‖ := fun u e => FormNormSumIdentities.ccle_comp (Mo.mem u) e
  have hin : ∀ u e, InCC a mm (comp u e) := fun u e => ⟨_, hcc u e⟩
  have hadd : ∀ u u', comp (u + u') = comp u + comp u' := by
    intro u u'; funext e γ; simp [comp, map_add (f := _)]
  have hsmul : ∀ (c : ℂ) u, comp (c • u) = c • comp u := by
    intro c u; funext e γ; simp [comp, map_smul]
  have hzero : comp 0 = 0 := by funext e γ; simp [comp]
  have hS := fun x x' y c hx hx' hy => JCx4.formLev_sesq_core P0 T sg j w a mm ha hmm x x' y c hx hx' hy
  have h0l : ∀ u', D.formLev T sg j w 0 (comp u') = 0 := by
    intro u'
    have h := (hS (comp 0) (comp 0) (comp u') 1 (hin 0) (hin 0) (hin u')).1
    rw [hzero, one_smul, add_zero, one_mul] at h
    linear_combination -h
  have h0r : ∀ u, D.formLev T sg j w (comp u) 0 = 0 := by
    intro u
    have h := (hS (comp 0) (comp 0) (comp u) 1 (hin 0) (hin 0) (hin u)).2
    rw [hzero, one_smul, add_zero, map_one, one_mul] at h
    linear_combination -h
  let Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun u u' => D.formLev T sg j w (comp u) (comp u'))
    (fun u₁ u₂ u' => by
      rw [hadd]
      have h := (hS (comp u₁) (comp u₂) (comp u') 1 (hin u₁) (hin u₂) (hin u')).1
      rw [one_smul, one_mul] at h
      exact h)
    (fun c u u' => by
      simp only [RingHom.id_apply, smul_eq_mul]
      rw [hsmul]
      have h := (hS (comp 0) (comp u) (comp u') c (hin 0) (hin u) (hin u')).1
      rw [hzero, zero_add, h0l, zero_add] at h
      exact h)
    (fun u u₁ u₂ => by
      rw [hadd]
      have h := (hS (comp u₁) (comp u₂) (comp u) 1 (hin u₁) (hin u₂) (hin u)).2
      rw [one_smul, map_one, one_mul] at h
      exact h)
    (fun c u u' => by
      simp only [smul_eq_mul]
      rw [hsmul]
      have h := (hS (comp 0) (comp u') (comp u) c (hin 0) (hin u') (hin u)).2
      rw [hzero, zero_add, h0r, zero_add] at h
      exact h)
  obtain ⟨Cf, hCf0, hCf⟩ := JCx4.formLev_bound_mm P0 T sg j w a ha
  have hN0 : (0 : ℝ) ≤ (w.length : ℝ) := Nat.cast_nonneg _
  refine ⟨Bf, Real.sqrt Cf, Real.sqrt_nonneg _, fun u => ?_, ?_⟩
  · have hb := hCf (comp u) (comp u) ‖u‖ ‖u‖
      (fun b => pd_ccle_mono (by linarith) hmm5 (hcc u b))
      (fun b => pd_ccle_mono (by linarith) (by omega) (hcc u b))
    have e : Bf u u = D.formLev T sg j w (comp u) (comp u) := rfl
    rw [e]
    calc (D.formLev T sg j w (comp u) (comp u)).re ≤ ‖D.formLev T sg j w (comp u) (comp u)‖ := Complex.re_le_norm _
      _ ≤ Cf * ‖u‖ * ‖u‖ := hb
      _ = (Real.sqrt Cf * ‖u‖) ^ 2 := by rw [mul_pow, Real.sq_sqrt hCf0]; ring
  · intro u u' x x' ε'' hε'' hx hx' hxu hxu'
    show D.formLev T sg j w (comp u) (comp u') = D.formLev T sg j w x x'
    unfold D.formLev
    refine Finset.sum_congr rfl fun e _ => ?_
    have hRR := JCx4.ma_hS P0 T sg j w
    have hmmU : 5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ P5.mmUser P0 w.length :=
      pd_thr_mm P0 j w.length _ le_rfl
    have hinx : ∀ b, InCC (P5.Auser P0 w.length + 1) ((2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (x b) :=
      fun b => sq_inCC_mono le_rfl (by omega) (hx b).2.1
    have hinu : ∀ b, InCC (P5.Auser P0 w.length + 1) ((2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (comp u b) :=
      fun b => sq_inCC_mono ha (by omega) (hin u b)
    have hloc : ∀ g ∈ GV P0.k (P0.r - j), D.actOp (D.RRlev T sg j w) (comp u) e g =
        D.actOp (D.RRlev T sg j w) x e g := by
      intro g hg
      rw [JCx4.ma_actOp_eq, JCx4.ma_actOp_eq]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hA : P5.Auser P0 w.length + 1 - ((2 * w.length : ℕ) : ℝ) + ((2 * w.length : ℕ) : ℝ) =
          P5.Auser P0 w.length + 1 := by ring
      have hm : 0 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length =
          (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length := by ring
      refine (hRR e b).2.2 (P5.Auser P0 w.length + 1 - ((2 * w.length : ℕ) : ℝ)) 0 (comp u b) (x b)
        (by rw [hA, hm]; exact hinu b) (by rw [hA, hm]; exact hinx b) (fun γ hγ => hxu b γ hγ) g hg
    rw [sq_beta_congr (T.bs j) hloc]
    exact FormNormSumIdentities.beta_congr_right (T.bs j) (fun γ hγ => hxu' e γ hγ)

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CsliceContDiffAt
section
open MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem update_mem_OmX {c : Fin r → ℂ} (hc : c ∈ OmX r) (l : Fin r) {t : ℂ} (ht : t ≠ 0) :
    Function.update c l t ∈ OmX r := by
  intro j
  by_cases hj : j = l
  · subst hj; simpa using ht
  · rw [Function.update_of_ne hj]; exact hc j

theorem cslice_contDiffAt (Φ : RadSp k r z z' π π') (g : Mx k r) {x : Fin r → ℂ} (hx : x ∈ OmX r) :
    ContDiffAt ℝ ∞ (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) x := by
  by_cases hg : g ∈ Glev k r (Fin.last r) ∧ 0 < GGl k r z z' g
  · obtain ⟨-, hs, -⟩ := Φ.2
    obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs (x, g) ⟨hx, hg.1, hg.2⟩
    have hcont : Continuous (fun c' : Fin r → ℂ => (c', g)) := continuous_id.prodMk continuous_const
    have hV : IsOpen ((fun c' : Fin r → ℂ => (c', g)) ⁻¹' U) := hU.preimage hcont
    have hFx : ContDiffAt ℝ ∞ (fun c' : Fin r → ℂ => F (c', g)) x :=
      (hF.contDiffAt (hU.mem_nhds hxU)).comp x (contDiff_id.prodMk contDiff_const).contDiffAt
    refine hFx.congr_of_eventuallyEq ?_
    filter_upwards [hV.mem_nhds hxU] with c' hc'
    exact hΦ (c', g) hc' hg.1
  · have h0 : (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) = fun _ => 0 := by
      funext c'
      exact radSp_zero_off Φ (x := (c', g)) (fun h => hg ⟨h.2.1, h.2.2⟩)
    rw [h0]; exact contDiffAt_const

theorem dZv_update {f : (Fin r → ℂ) → (Wq →L[ℂ] Wp)} (c : Fin r → ℂ) (l : Fin r) (t : ℂ)
    (hf : DifferentiableAt ℝ f (Function.update c l t)) :
    dZv (fun s => f (Function.update c l s)) t = wirt l f (Function.update c l t) ∧
      dZbv (fun s => f (Function.update c l s)) t = wirtBar l f (Function.update c l t) := by
  have hu := hasFDerivAt_update (𝕜 := ℝ) c (i := l) t
  have h := hf.hasFDerivAt.comp t hu
  have hd : ∀ v : ℂ, fderiv ℝ (fun s => f (Function.update c l s)) t v =
      fderiv ℝ f (Function.update c l t) (Pi.single l v) := by
    intro v
    rw [show (fun s => f (Function.update c l s)) = f ∘ Function.update c l from rfl, h.fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    congr 1
    funext j
    by_cases hj : j = l
    · subst hj; simp
    · simp [hj]
  constructor
  · unfold dZv wirt; rw [hd, hd]
  · unfold dZbv wirtBar; rw [hd, hd]

theorem site_p_adj_g (X : ActualOps k r z z' π π') (Φ Ψ : RadSp k r z z' π π') (l : Fin r) (c : Fin r → ℂ)
    (hc : c ∈ OmX r) (g : Mx k r)
    (h0 : Integrable (fun t : ℂ => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ)))
    (h1 : Integrable (fun t : ℂ => B.hsInner ((X.op l 0 Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ)))
    (h2 : Integrable (fun t : ℂ => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((X.op l 3 Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ))) :
    ∫ t : ℂ, B.hsInner ((X.op l 0 Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ) =
    -∫ t : ℂ, B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((X.op l 3 Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ) := by
  set fΦ : (Fin r → ℂ) → (Wq →L[ℂ] Wp) := fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g with hfΦ
  set fΨ : (Fin r → ℂ) → (Wq →L[ℂ] Wp) := fun c' => (Ψ : Fn k r (Wq →L[ℂ] Wp)) c' g with hfΨ
  set A : ℂ → (Wq →L[ℂ] Wp) := fun t => fΦ (Function.update c l t) with hA
  set Bf : ℂ → (Wq →L[ℂ] Wp) := fun t => fΨ (Function.update c l t) with hB
  have hupd : ContDiff ℝ ∞ (fun t : ℂ => Function.update c l t) :=
    contDiff_pi.mpr fun j => by
      by_cases hj : j = l
      · subst hj; simp only [Function.update_self]; exact contDiff_id
      · simpa [Function.update_of_ne hj] using contDiff_const
  have hAc : ContDiffOn ℝ 1 A {t | t ≠ 0} := fun t ht =>
    (((cslice_contDiffAt Φ g (update_mem_OmX hc l ht)).comp t hupd.contDiffAt).of_le (by simp)).contDiffWithinAt
  have hBc : ContDiffOn ℝ 1 Bf {t | t ≠ 0} := fun t ht =>
    (((cslice_contDiffAt Ψ g (update_mem_OmX hc l ht)).comp t hupd.contDiffAt).of_le (by simp)).contDiffWithinAt
  have hpΦ : ∀ t : ℂ, t ≠ 0 → (X.op l 0 Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g = t • dZv A t := by
    intro t ht
    have hd := dZv_update (f := fΦ) c l t
      ((cslice_contDiffAt Φ g (update_mem_OmX hc l ht)).differentiableAt (by simp))
    rw [X.op_apply, hd.1]
    show pOp l fΦ (Function.update c l t) = _
    unfold pOp
    rw [if_pos (update_mem_OmX hc l ht), Function.update_self]
  have hpΨ : ∀ t : ℂ, t ≠ 0 → (X.op l 3 Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g =
      conj t • dZbv Bf t := by
    intro t ht
    have hd := dZv_update (f := fΨ) c l t
      ((cslice_contDiffAt Ψ g (update_mem_OmX hc l ht)).differentiableAt (by simp))
    rw [X.op_apply, hd.2]
    show pbOp l fΨ (Function.update c l t) = _
    unfold pbOp
    rw [if_pos (update_mem_OmX hc l ht), Function.update_self]
    rfl
  have e1 : (fun t : ℂ => B.hsInner ((X.op l 0 Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ)) =
      fun t => B.hsInner (t • dZv A t) (Bf t) / ((‖t‖ ^ 2 : ℝ) : ℂ) := by
    funext t
    by_cases ht : t = 0
    · subst ht; simp
    · rw [hpΦ t ht]
  have e2 : (fun t : ℂ => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((X.op l 3 Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ)) =
      fun t => B.hsInner (A t) (conj t • dZbv Bf t) / ((‖t‖ ^ 2 : ℝ) : ℂ) := by
    funext t
    by_cases ht : t = 0
    · subst ht; simp
    · rw [hpΨ t ht]
  have h1' := e1 ▸ h1
  have h2' := e2 ▸ h2
  rw [e1, e2]
  exact pLogAdjHS A Bf hAc hBc h0 h1' h2'

theorem site_p_adj (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)) [SFinite μ] (Φ Ψ : RadSp k r z z' π π')
    (l : Fin r) (c : Fin r → ℂ) (hc : c ∈ OmX r)
    (h0 : Integrable (fun q : ℂ × Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l q.1)
      (Matrix.of q.2)) ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l q.1) (Matrix.of q.2)) /
        ((‖q.1‖ ^ 2 : ℝ) : ℂ)) (volume.prod μ))
    (h1 : Integrable (fun q : ℂ × Mt k r => B.hsInner ((X.op l 0 Φ : Fn k r (Wq →L[ℂ] Wp))
      (Function.update c l q.1) (Matrix.of q.2)) ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l q.1)
        (Matrix.of q.2)) / ((‖q.1‖ ^ 2 : ℝ) : ℂ)) (volume.prod μ))
    (h2 : Integrable (fun q : ℂ × Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l q.1)
      (Matrix.of q.2)) ((X.op l 3 Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l q.1) (Matrix.of q.2)) /
        ((‖q.1‖ ^ 2 : ℝ) : ℂ)) (volume.prod μ)) :
    ∫ t : ℂ, pairAt μ (X.op l 0 Φ) Ψ (Function.update c l t) / ((‖t‖ ^ 2 : ℝ) : ℂ) =
      -∫ t : ℂ, pairAt μ Φ (X.op l 3 Ψ) (Function.update c l t) / ((‖t‖ ^ 2 : ℝ) : ℂ) := by
  unfold pairAt
  simp only [← integral_div]
  rw [integral_integral_swap h1]
  conv_rhs => rw [integral_integral_swap h2]
  rw [← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [h0.prod_left_ae, h1.prod_left_ae, h2.prod_left_ae] with x hx0 hx1 hx2
  exact site_p_adj_g X Φ Ψ l c hc (Matrix.of x) hx0 hx1 hx2

end Formalism.FourierDecayAlt.P5.HerB
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnFoldRev
section
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.En

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem cV_smul {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (Y α : ℂ) (f : B.Mat k r → E) :
    Q.CV k r Y (α • f) = α • Q.CV k r Y f :=
  Formalism.FourierDecayAlt.P5.qminorOp_smulC (Formalism.FourierDecayAlt.P5.eH_smulC (k := k) (r := r)) _ _ _ α f

section fold

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {Dm : Set (Q.Mx k r)}

theorem ckOn_of_ffl {J : Q.Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ Q.FFl k r z z' π π' 0 Dm) :
    B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (Dm ∩ B.GV k r) J := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hc, he⟩ := hJ.1 g₀ ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hg₀.2, hg₀.1⟩
  exact ⟨U, F, hU, hgU, hc.of_le (by exact_mod_cast le_top), fun g hg hgG => he g hg (Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hgG)⟩

theorem letter_congr (hCL : CVLocal) (hDm : IsOpen Dm) {J₁ J₂ : Q.Mx k r → (Wq →L[ℂ] Wp)}
    (h₁ : J₁ ∈ Q.FFl k r z z' π π' 0 Dm) (h₂ : J₂ ∈ Q.FFl k r z z' π π' 0 Dm)
    (he : ∀ g ∈ Q.Glev k r 0 ∩ Dm, J₁ g = J₂ g) (Y : ℝ) (s : ℂ) :
    ∀ g ∈ Q.Glev k r 0 ∩ Dm, (s • Q.CV k r (Y : ℂ) J₁) g = (s • Q.CV k r (Y : ℂ) J₂) g := by
  intro g hg
  have := hCL k r _ Dm J₁ J₂ (Y : ℂ) hDm (ckOn_of_ffl h₁) (ckOn_of_ffl h₂)
    (fun x hx => he x ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hx.2, hx.1⟩) g ⟨hg.2, hg.1.1⟩
  simp only [Pi.smul_apply, this]

theorem letter_swap (hDm : IsOpen Dm) {J : Q.Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ Q.FFl k r z z' π π' 0 Dm)
    (x y : ℝ) (s : ℂ) : ∀ g ∈ Q.Glev k r 0 ∩ Dm,
      (s • Q.CV k r (x : ℂ) (s • Q.CV k r (y : ℂ) J)) g = (s • Q.CV k r (y : ℂ) (s • Q.CV k r (x : ℂ) J)) g := by
  intro g hg
  simp only [cV_smul, Pi.smul_apply]
  unfold Q.CV
  rw [Formalism.FourierDecayAlt.P.capelli_commutation _ k r 0 Dm J hDm hJ.1 g hg]

theorem foldCV_append (s : ℂ) (l₁ l₂ : List C.Letter) (J : Q.Mx k r → (Wq →L[ℂ] Wp)) :
    foldCV k r s (l₁ ++ l₂) J = foldCV k r s l₁ (foldCV k r s l₂ J) := by
  unfold foldCV; rw [List.foldr_append]

end fold

theorem foldRev_of (hCL : CVLocal) : FoldRev := by
  intro k r Wp Wq _ _ _ _ z z' π π' Dm hDm hcl J hJ s a
  have hcomm : ∀ (b : List C.Letter) (J : Q.Mx k r → (Wq →L[ℂ] Wp)), J ∈ Q.FFl k r z z' π π' 0 Dm →
      ∀ x : C.Letter, ∀ g ∈ Q.Glev k r 0 ∩ Dm,
        foldCV k r s b (s • Q.CV k r (x.2 : ℂ) J) g = (s • Q.CV k r (x.2 : ℂ) (foldCV k r s b J)) g := by
    intro b
    induction b with
    | nil => intro J _ x g _; rfl
    | cons y b ih =>
      intro J hJ x g hg
      have h1 := letter_congr hCL hDm (foldCV_mem hcl (hcl J hJ x.2 s) s b)
        (hcl _ (foldCV_mem hcl hJ s b) x.2 s) (ih J hJ x) y.2 s g hg
      have h2 := letter_swap hDm (foldCV_mem hcl hJ s b) y.2 x.2 s g hg
      rw [foldCV_cons, h1, h2]
      rfl
  induction a generalizing J with
  | nil => intro g _; rfl
  | cons x a ih =>
    intro g hg
    rw [List.reverse_cons, foldCV_append]
    rw [ih (foldCV k r s [x] J) (hcl J hJ x.2 s) g hg]
    exact hcomm a J hJ x g hg

theorem folding_reversal_holds : FoldRev := foldRev_of coefficient_vector_locality

end Formalism.FourierDecayAlt.P.CutMP.En
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableOfAdj
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open Formalism.FourierDecayAlt.P.CutMP.JA

theorem jAFFStable_of_adjComm (hA : AdjComm) : JAFFStable :=
  jAFFStable_of_parts germ_operators_holds extension_locality_holds smooth_operators_holds hA equivariant_operators_holds positive_domain_condition_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGACutGraded
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.GA

theorem graded_truncation_action_holds : GACutGraded := by
  refine ⟨2, by norm_num, ?_⟩
  intro k r Wp Wq _ _ _ _ _ _ Bs χ₀ hχ ε A Bg F hε hBg hF hFg
  obtain ⟨δ, -, hcut, -⟩ := Formalism.FourierDecayAlt.P.JCTx6.Lev0.isCutG_div hχ hε
  exact Formalism.FourierDecayAlt.P.CutMP.JA.gcut_graded Bs.z Bs.z' (fun x => χ₀ (x / ε)) (δ * ε) hcut
    (by linarith) hF hFg

end Formalism.FourierDecayAlt.P.CutMP.JA.GA

end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutRegFFName
section
namespace Formalism.FourierDecayAlt.P.CutMP

abbrev JfSmoothBuilt : Prop := JfSmoothDS

end Formalism.FourierDecayAlt.P.CutMP
end

