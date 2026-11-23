module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockRelationTwistedHeight
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0024
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0129
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0068
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCHolPh
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0128
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0080

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ArelStar
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.WordCorrespondence

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.PBH

section core

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {T : V →ₗ[ℂ] V'}
  {S : Type} [Fintype S] [DecidableEq S]

theorem rel_inv {a b : Pr V} {a' b' : Pr V'} (h : Rel T a a') (hab : a * b = 1) (hba : b * a = 1)
    (hab' : a' * b' = 1) (hba' : b' * a' = 1) : Rel T b b' := by
  have e1 : a.1 * b.1 = 1 := congrArg Prod.fst hab
  have e2 : b'.1 * a'.1 = 1 := congrArg Prod.fst hba'
  have e3 : a.2.unop * b.2.unop = 1 := congrArg (fun x : Pr V => x.2.unop) hba
  have e4 : b'.2.unop * a'.2.unop = 1 := congrArg (fun x : Pr V' => x.2.unop) hab'
  refine ⟨LinearMap.ext fun v => ?_, LinearMap.ext fun v => ?_⟩
  · have i1 : a.1 (b.1 v) = v := by simpa using LinearMap.congr_fun e1 v
    have i2 : b'.1 (a'.1 (T (b.1 v))) = T (b.1 v) := by simpa using LinearMap.congr_fun e2 (T (b.1 v))
    have i3 : a'.1 (T (b.1 v)) = T (a.1 (b.1 v)) := LinearMap.congr_fun h.1 (b.1 v)
    show b'.1 (T v) = T (b.1 v)
    rw [← i2, i3, i1]
  · have i1 : a.2.unop (b.2.unop v) = v := by simpa using LinearMap.congr_fun e3 v
    have i2 : b'.2.unop (a'.2.unop (T (b.2.unop v))) = T (b.2.unop v) := by
      simpa using LinearMap.congr_fun e4 (T (b.2.unop v))
    have i3 : a'.2.unop (T (b.2.unop v)) = T (a.2.unop (b.2.unop v)) := LinearMap.congr_fun h.2 (b.2.unop v)
    show b'.2.unop (T v) = T (b.2.unop v)
    rw [← i2, i3, i1]

theorem arel_star' {M : SlopeTestRemainingChoices S (Pr V)} {M' : SlopeTestRemainingChoices S (Pr V')} (h : ARel T M M') : ARel T (star M) (star M') :=
  fun x y => by
    rw [Matrix.star_apply, Matrix.star_apply]
    exact rel_star (h y x)

theorem arel_pow' {M : SlopeTestRemainingChoices S (Pr V)} {M' : SlopeTestRemainingChoices S (Pr V')} (h : ARel T M M') : ∀ n : ℕ, ARel T (M ^ n) (M' ^ n)
  | 0 => by rw [pow_zero, pow_zero]; exact arel_one
  | n + 1 => by rw [pow_succ, pow_succ]; exact arel_mul (arel_pow' h n) h

theorem brel_of {a b c d : SlopeTestRemainingChoices S (Pr V)} {a' b' c' d' : SlopeTestRemainingChoices S (Pr V')} (h1 : ARel T a a') (h2 : ARel T b b')
    (h3 : ARel T c c') (h4 : ARel T d d') : BRel T !![a, b; c, d] !![a', b'; c', d'] := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact h1
  · exact h2
  · exact h3
  · exact h4

structure Gen {r₀ r₁ : ℕ} (T : V →ₗ[ℂ] V') (L₀ : LevelData (Pr V) r₀) (L : LevelData (Pr V') r₁) : Prop where
  ζ : Rel T L₀.ζ L.ζ
  ζi : Rel T L₀.ζi L.ζi
  ζb : Rel T L₀.ζb L.ζb
  ζbi : Rel T L₀.ζbi L.ζbi
  GG : Rel T L₀.GG L.GG
  GGi : Rel T L₀.GGi L.GGi
  TT : L₀.TT = L.TT

abbrev Corr (T : V →ₗ[ℂ] V') (inv0 : Set ℂ) (f₀ : FrameData S (Pr V)) (f : FrameData S (Pr V')) : Prop :=
  ARel T f₀.F f.F ∧ ARel T f₀.Fi f.Fi ∧ ARel T f₀.c f.c ∧ ARel T f₀.ci f.ci ∧ (∀ Y, ARel T (f₀.x Y) (f.x Y)) ∧
    (∀ Y ∈ inv0, ARel T (f₀.xi Y) (f.xi Y)) ∧ (∀ Y, BRel T (f₀.TT Y) (f.TT Y)) ∧ f₀.N = f.N ∧ f₀.q = f.q ∧
    f₀.inv = f.inv ∧ f₀.inv ⊆ inv0

variable {r₀ r₁ : ℕ} {L₀ : LevelData (Pr V) r₀} {L : LevelData (Pr V') r₁}

theorem l_eq {r : ℕ} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (L : LevelData A r) (f : FrameData S A)
    (hf : IsFrame L f) (Y : ℂ) (hY : Y ∈ f.inv) (hY1 : Y + 1 ∈ f.inv) :
    f.l L Y = f.xi Y * io L.GGi * f.F * f.TT Y 1 0 * f.Fi := by
  have h := hf.frame_l Y hY hY1
  have hio : (io L.GGi : SlopeTestRemainingChoices S A) * io L.GG = 1 := by simp only [io, ← map_mul, L.GGi_GG, map_one]
  have hx := (hf.x_xi Y hY).2
  calc f.l L Y = (f.xi Y * f.x Y) * f.l L Y * (f.F * f.Fi) := by rw [hx, hf.F_Fi, one_mul, mul_one]
    _ = f.xi Y * ((io L.GGi * io L.GG) * f.x Y * f.l L Y * f.F) * f.Fi := by
      rw [hio]; simp only [one_mul, mul_assoc]
    _ = f.xi Y * io L.GGi * (io L.GG * f.x Y * f.l L Y * f.F) * f.Fi := by simp only [mul_assoc]
    _ = f.xi Y * io L.GGi * f.F * f.TT Y 1 0 * f.Fi := by rw [← h]; simp only [mul_assoc]

theorem l_rel (G : Gen T L₀ L) {inv0 : Set ℂ} {f₀ : FrameData S (Pr V)} {f : FrameData S (Pr V')}
    (hc : Corr T inv0 f₀ f) (hf₀ : IsFrame L₀ f₀) (hf : IsFrame L f) (Y : ℂ) (hY : Y ∈ f₀.inv)
    (hY1 : Y + 1 ∈ f₀.inv) : ARel T (f₀.l L₀ Y) (f.l L Y) := by
  obtain ⟨hF, hFi, -, -, -, hxi, hTT, -, -, hinv, hsub⟩ := hc
  rw [l_eq L₀ f₀ hf₀ Y hY hY1, l_eq L f hf Y (hinv ▸ hY) (hinv ▸ hY1)]
  exact arel_mul (arel_mul (arel_mul (arel_mul (hxi Y (hsub hY)) (arel_io G.GGi)) hF) (hTT Y 1 0)) hFi

theorem m_rel (G : Gen T L₀ L) {inv0 : Set ℂ} {f₀ : FrameData S (Pr V)} {f : FrameData S (Pr V')}
    (hc : Corr T inv0 f₀ f) (hf₀ : IsFrame L₀ f₀) (hf : IsFrame L f) (Y : ℂ) (hY : Y - 1 ∈ f₀.inv)
    (hY1 : Y ∈ f₀.inv) : ARel T (f₀.m L₀ Y) (f.m L Y) := by
  have hl := l_rel G hc hf₀ hf (Y - 1) hY (by rw [sub_add_cancel]; exact hY1)
  obtain ⟨-, -, hc', hci, -, -, -, hN, -, -, -⟩ := hc
  have hwt : ARel T (wt (S := S) L₀) (wt L) := arel_io (rel_mul (rel_mul G.ζ G.ζb) G.GGi)
  have hwti : ARel T (wti (S := S) L₀) (wti L) := arel_io (rel_mul (rel_mul G.GG G.ζi) G.ζbi)
  unfold FrameData.m FrameData.d FrameData.di
  rw [hN]
  exact arel_mul (arel_mul (arel_mul hci (arel_pow' hwti _)) (arel_star' hl)) (arel_mul (arel_pow' hwt _) hc')

theorem corr_plus (G : Gen T L₀ L) {inv0 : Set ℂ} {f₀ : FrameData S (Pr V)} {f : FrameData S (Pr V')}
    (hc : Corr T inv0 f₀ f) (hf₀ : IsFrame L₀ f₀) (hf : IsFrame L f) (a : S) (Ya : ℂ) (h1 : Ya ∈ f₀.inv)
    (h2 : Ya + 1 ∈ f₀.inv) : Corr T inv0 (f₀.plus L₀ a Ya) (f.plus L a Ya) := by
  have hl := l_rel G hc hf₀ hf Ya h1 h2
  obtain ⟨hF, hFi, hc', hci, hx, hxi, hTT, hN, hq, hinv, hsub⟩ := hc
  dsimp only [FrameData.plus]
  refine ⟨?_, ?_, ?_, ?_, fun Y => ?_, fun Y hY => ?_, fun Y => ?_, by rw [hN], by rw [hq], by rw [hinv],
    Set.inter_subset_left.trans hsub⟩
  · exact arel_mul (arel_ins a (brel_mul (brel_of (arel_io G.ζi) arel_zero arel_zero (arel_io G.ζbi))
      (brel_of arel_one arel_zero (arel_mul (arel_io G.GG) hl) (arel_io G.GG)))) hF
  · exact arel_mul hFi (arel_ins a (brel_mul (brel_of arel_one arel_zero (arel_neg hl) (arel_io G.GGi))
      (brel_of (arel_io G.ζ) arel_zero arel_zero (arel_io G.ζb))))
  · rw [hq]
    exact arel_mul hc' (arel_ins a (brel_of (arel_smul _ (hxi _ (hsub h2))) arel_zero arel_zero (hx Ya)))
  · rw [hq]
    exact arel_mul hci (arel_ins a (brel_of (arel_smul _ (hx _)) arel_zero arel_zero (hxi _ (hsub h1))))
  · exact arel_mul (hx Y) (arel_ins a (brel_of (arel_smul _ arel_one) arel_zero arel_zero arel_one))
  · exact arel_mul (hxi Y hY) (arel_ins a (brel_of (arel_smul _ arel_one) arel_zero arel_zero arel_one))
  · exact brel_mul (hTT Y) (block_relation_height a _)

theorem corr_minus (G : Gen T L₀ L) {inv0 : Set ℂ} {f₀ : FrameData S (Pr V)} {f : FrameData S (Pr V')}
    (hc : Corr T inv0 f₀ f) (hf₀ : IsFrame L₀ f₀) (hf : IsFrame L f) (b : S) (Yb : ℂ) (h1 : Yb ∈ f₀.inv)
    (h0 : Yb - 1 ∈ f₀.inv) : Corr T inv0 (f₀.minus L₀ b Yb) (f.minus L b Yb) := by
  have hm := m_rel G hc hf₀ hf Yb h0 h1
  obtain ⟨hF, hFi, hc', hci, hx, hxi, hTT, hN, hq, hinv, hsub⟩ := hc
  dsimp only [FrameData.minus]
  refine ⟨?_, ?_, ?_, ?_, fun Y => ?_, fun Y hY => ?_, fun Y => ?_, by rw [hN], by rw [hq], by rw [hinv],
    Set.inter_subset_left.trans hsub⟩
  · exact arel_mul (arel_ins b (brel_mul (brel_of (arel_io G.ζbi) arel_zero arel_zero (arel_io G.ζi))
      (brel_of arel_one arel_zero (arel_mul (arel_io G.GG) hm) (arel_io G.GG)))) hF
  · exact arel_mul hFi (arel_ins b (brel_mul (brel_of arel_one arel_zero (arel_neg hm) (arel_io G.GGi))
      (brel_of (arel_io G.ζb) arel_zero arel_zero (arel_io G.ζ))))
  · rw [hq]
    exact arel_mul hc' (arel_ins b (brel_of (arel_smul _ (hxi _ (hsub h0))) arel_zero arel_zero (hx Yb)))
  · rw [hq]
    exact arel_mul hci (arel_ins b (brel_of (arel_smul _ (hx _)) arel_zero arel_zero (hxi _ (hsub h1))))
  · exact arel_mul (hx Y) (arel_ins b (brel_of (arel_smul _ arel_one) arel_zero arel_zero arel_one))
  · exact arel_mul (hxi Y hY) (arel_ins b (brel_of (arel_smul _ arel_one) arel_zero arel_zero arel_one))
  · exact brel_mul (block_relation_twisted_height b _) (hTT Y)

variable {st₀ : Start (Pr V)} {st : Start (Pr V')}

theorem x_rel (G : Gen T L₀ L) (hQ : ∀ Y, MRel T (st₀.QQ Y) (st.QQ Y)) (hs₀ : IsLevelStart L₀ st₀)
    (hs : IsLevelStart L st) (Y : ℂ) : Rel T (st₀.x Y) (st.x Y) := by
  have e₀ : st₀.x Y = L₀.GGi * st₀.QQ Y 1 1 := by rw [hs₀.tau, ← mul_assoc, L₀.GGi_GG, one_mul]
  have e : st.x Y = L.GGi * st.QQ Y 1 1 := by rw [hs.tau, ← mul_assoc, L.GGi_GG, one_mul]
  rw [e₀, e]
  exact rel_mul G.GGi (hQ Y 1 1)

theorem corr_word (G : Gen T L₀ L) (hQ : ∀ Y, MRel T (st₀.QQ Y) (st.QQ Y)) (hq : st₀.q = st.q)
    (hinv : st₀.inv = st.inv) (hL₀ : IsStarLevel L₀) (hL : IsStarLevel L) (hs₀ : IsLevelStart L₀ st₀)
    (hs : IsLevelStart L st) :
    ∀ w : List (Letter ℂ S), AdmRec L₀ st₀ w → AdmRec L st w →
      Corr T st₀.inv (ofWord L₀ st₀ w) (ofWord L st w) := by
  intro w
  induction w with
  | nil =>
    intro _ _
    refine ⟨arel_one, arel_one, arel_one, arel_one, fun Y => arel_io (x_rel G hQ hs₀ hs Y), fun Y hY => ?_,
      fun Y => brel_lift0 (hQ Y), rfl, hq, hinv, subset_rfl⟩
    exact arel_io (rel_inv (x_rel G hQ hs₀ hs Y) (hs₀.x_xi Y hY).1 (hs₀.x_xi Y hY).2
      (hs.x_xi Y (hinv ▸ hY)).1 (hs.x_xi Y (hinv ▸ hY)).2)
  | cons l w ih =>
    intro h₀ h
    unfold AdmRec at h₀ h
    obtain ⟨hw₀, -, -, hp0, hp1, hrest⟩ := h₀
    obtain ⟨hw, -⟩ := h
    have hf₀ := Formalism.FourierDecayAlt.P.frame_of_recursive_word (Pr V) S r₀ L₀ st₀ w hL₀ hs₀ hw₀
    have hf := Formalism.FourierDecayAlt.P.frame_of_recursive_word (Pr V') S r₁ L st w hL hs hw
    by_cases hp : l.plus
    · simpa only [ofWord, ite_eq_left hp] using
        corr_plus G (ih hw₀ hw) hf₀ hf l.intersection_update_fsHerm_neg_one l.pt hp0 hp1
    · rw [ite_eq_right hp] at hrest
      simpa only [ofWord, ite_eq_right hp] using
        corr_minus G (ih hw₀ hw) hf₀ hf l.intersection_update_fsHerm_neg_one l.pt hp0 hrest.1

theorem act_frame (G : Gen T L₀ L) (hQ : ∀ Y, MRel T (st₀.QQ Y) (st.QQ Y)) (hq : st₀.q = st.q)
    (hinv : st₀.inv = st.inv) (hL₀ : IsStarLevel L₀) (hL : IsStarLevel L) (hs₀ : IsLevelStart L₀ st₀)
    (hs : IsLevelStart L st) (w : List (Letter ℂ S)) (h₀ : admitted st₀ w) (h : admitted st w) (Ψ : Ix S → V) (e : Ix S) :
    T (∑ b, ((ofWord L₀ st₀ w).F e b).1 (Ψ b)) = ∑ b, ((ofWord L st w).F e b).1 (T (Ψ b)) :=
  act_tr (corr_word G hQ hq hinv hL₀ hL hs₀ hs w
    (Formalism.FourierDecayAlt.P.admissible_rec_of_admissible (Pr V) S r₀ L₀ st₀ w h₀)
    (Formalism.FourierDecayAlt.P.admissible_rec_of_admissible (Pr V') S r₁ L st w h)).1 Ψ e

end core

end Formalism.FourierDecayAlt.P.WordCorrespondence
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousSandwichedProduct
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

private theorem lintegral_comp_eq_of_map_eq {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] {μ : Measure α} {f : α → α}
    (hμ : μ.map f = μ) {G : α → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G (f x) ∂μ = ∫⁻ x, G x ∂μ := by
  by_cases hf : AEMeasurable f μ
  · conv_rhs => rw [← hμ]
    rw [lintegral_map' hG.aemeasurable hf]
  · by_cases h0 : μ = 0
    · simp [h0]
    · haveI : Nonempty α := Measure.nonempty_of_not_aemeasurable hf
      have hd : μ = Measure.dirac (Classical.ofNonempty : α) :=
        hμ.symm.trans (Measure.map_of_not_aemeasurable_of_ne_zero hf h0)
      rw [hd] at hf
      exact (hf aemeasurable_dirac).elim

theorem lint_lmul {μ : Measure (Formalism.QuantumDeterminants.Mt k r)} {a : Mx k r} (hμ : μ.map (Formalism.QuantumDeterminants.lmulM a) = μ)
    {G : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G (Formalism.QuantumDeterminants.lmulM a x) ∂μ = ∫⁻ x, G x ∂μ := by
  exact lintegral_comp_eq_of_map_eq hμ hG

theorem param_left {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    [SigmaFinite μW] [SigmaFinite μN] (hz : Formalism.QuantumDeterminants.inWb k r z)
    {h0 n0 : Mx k r} (hh0 : h0 ∈ Formalism.QuantumDeterminants.UWset k r z) (hn0 : n0 ∈ Formalism.QuantumDeterminants.Nset k r)
    {F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F (fun i j => (h0 * n0 * (Matrix.of p.1 * Matrix.of p.2)) i j) ∂(μW.prod μN) =
      ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) ∂(μW.prod μN) := by
  have hm1 : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      F (fun i j => (h0 * n0 * (Matrix.of p.1 * Matrix.of p.2)) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (h0 * n0 * (Matrix.of p.1 * Matrix.of p.2)) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have hm2 : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have hm3 : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      F (fun i j => (h0 * Matrix.of p.1 * Matrix.of p.2) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (h0 * Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have hae : ∀ᵐ x ∂μW, Matrix.of x ∈ Formalism.QuantumDeterminants.UWset k r z := ae_iff.mpr hW.2.2.1

  have step1 : (fun x => ∫⁻ y, F (fun i j => (h0 * n0 * (Matrix.of x * Matrix.of y)) i j) ∂μN) =ᵐ[μW]
      fun x => ∫⁻ y, F (fun i j => (h0 * Matrix.of x * Matrix.of y) i j) ∂μN := by
    filter_upwards [hae] with x hx
    obtain ⟨hxi, hx1, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hx
    have hm : (Matrix.of x)⁻¹ * n0 * Matrix.of x ∈ Formalism.QuantumDeterminants.Nset k r := by
      have h1 := (Formalism.QuantumDeterminants.uWNormal k r z hz _ hxi n0 hn0).1
      rwa [Matrix.nonsing_inv_nonsing_inv _ (Matrix.isUnit_det_of_right_inverse hx1)] at h1
    have hG : Measurable (fun w : Formalism.QuantumDeterminants.Mt k r =>
        F (fun i j => (h0 * Matrix.of x * Matrix.of w) i j)) :=
      (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun w : Formalism.QuantumDeterminants.Mt k r => (fun i j => (h0 * Matrix.of x * Matrix.of w) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
    have e1 : ∀ y : Formalism.QuantumDeterminants.Mt k r, h0 * n0 * (Matrix.of x * Matrix.of y) =
        h0 * Matrix.of x * Matrix.of (Formalism.QuantumDeterminants.lmulM ((Matrix.of x)⁻¹ * n0 * Matrix.of x) y) := by
      intro y
      show _ = h0 * Matrix.of x * ((Matrix.of x)⁻¹ * n0 * Matrix.of x * Matrix.of y)
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Matrix.of x) (Matrix.of x)⁻¹, hx1, Matrix.one_mul]
    simp_rw [e1]
    exact lint_lmul (hN.2.2.2 _ hm) hG
  rw [MeasureTheory.lintegral_prod _ hm1.aemeasurable, MeasureTheory.lintegral_prod _ hm2.aemeasurable,
    MeasureTheory.lintegral_congr_ae step1,
    MeasureTheory.lintegral_lintegral_swap (f := fun (x y : Formalism.QuantumDeterminants.Mt k r) => F (fun i j => (h0 * Matrix.of x * Matrix.of y) i j))
      hm3.aemeasurable,
    MeasureTheory.lintegral_lintegral_swap (f := fun (x y : Formalism.QuantumDeterminants.Mt k r) => F (fun i j => (Matrix.of x * Matrix.of y) i j))
      hm2.aemeasurable]

  refine MeasureTheory.lintegral_congr fun y => ?_
  have hG : Measurable (fun w : Formalism.QuantumDeterminants.Mt k r => F (fun i j => (Matrix.of w * Matrix.of y) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun w : Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of w * Matrix.of y) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have e2 : ∀ x : Formalism.QuantumDeterminants.Mt k r, h0 * Matrix.of x * Matrix.of y =
      Matrix.of (Formalism.QuantumDeterminants.lmulM h0 x) * Matrix.of y := fun x => rfl
  simp_rw [e2]
  exact lint_lmul (hW.2.2.2 h0 hh0) hG

theorem lint_rmul {μ : Measure (Formalism.QuantumDeterminants.Mt k r)} {a : Mx k r} (hμ : μ.map (B.rmulF a) = μ)
    {G : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G (B.rmulF a x) ∂μ = ∫⁻ x, G x ∂μ := by
  exact lintegral_comp_eq_of_map_eq hμ hG

theorem lint_conj {μ : Measure (Formalism.QuantumDeterminants.Mt k r)} {a : Mx k r} (hμ : μ.map (Formalism.QuantumDeterminants.conjM a) = μ)
    {G : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G (Formalism.QuantumDeterminants.conjM a x) ∂μ = ∫⁻ x, G x ∂μ := by
  exact lintegral_comp_eq_of_map_eq hμ hG

theorem param_right {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    [SigmaFinite μW] [SigmaFinite μN] (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    {h0 n0 : Mx k r} (hh0 : h0 ∈ Formalism.QuantumDeterminants.UWset k r z) (hn0 : n0 ∈ Formalism.QuantumDeterminants.Nset k r)
    {F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2 * (h0 * n0)) i j) ∂(μW.prod μN) =
      ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) ∂(μW.prod μN) := by
  obtain ⟨hi, h1, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hh0
  have hinv : h0⁻¹⁻¹ = h0 := Matrix.nonsing_inv_nonsing_inv _ (Matrix.isUnit_det_of_right_inverse h1)
  have hconj : μN.map (Formalism.QuantumDeterminants.conjM h0⁻¹) = μN :=
    Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r z μN hz hT hN _ hi
  have hm1 : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      F (fun i j => (Matrix.of p.1 * Matrix.of p.2 * (h0 * n0)) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2 * (h0 * n0)) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have hm2 : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have hm3 : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      F (fun i j => (Matrix.of p.1 * h0 * Matrix.of p.2) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * h0 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)

  have inner : ∀ x : Formalism.QuantumDeterminants.Mt k r,
      ∫⁻ y, F (fun i j => (Matrix.of x * Matrix.of y * (h0 * n0)) i j) ∂μN =
        ∫⁻ y, F (fun i j => (Matrix.of x * h0 * Matrix.of y) i j) ∂μN := by
    intro x
    have hG1 : Measurable (fun w : Formalism.QuantumDeterminants.Mt k r =>
        F (fun i j => (Matrix.of x * h0 * Matrix.of w * n0) i j)) :=
      (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun w : Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of x * h0 * Matrix.of w * n0) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
    have hG2 : Measurable (fun w : Formalism.QuantumDeterminants.Mt k r =>
        F (fun i j => (Matrix.of x * h0 * Matrix.of w) i j)) :=
      (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun w : Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of x * h0 * Matrix.of w) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
    have e1 : ∀ y : Formalism.QuantumDeterminants.Mt k r, Matrix.of x * Matrix.of y * (h0 * n0) =
        Matrix.of x * h0 * Matrix.of (Formalism.QuantumDeterminants.conjM h0⁻¹ y) * n0 := by
      intro y
      show _ = Matrix.of x * h0 * (h0⁻¹ * Matrix.of y * h0⁻¹⁻¹) * n0
      rw [hinv]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc h0 h0⁻¹, h1, Matrix.one_mul]
    have e2 : ∀ y : Formalism.QuantumDeterminants.Mt k r, Matrix.of x * h0 * Matrix.of y * n0 =
        Matrix.of x * h0 * Matrix.of (B.rmulF n0 y) := by
      intro y
      show _ = Matrix.of x * h0 * (Matrix.of y * n0)
      simp only [Matrix.mul_assoc]
    simp_rw [e1]
    rw [lint_conj hconj hG1]
    simp_rw [e2]
    exact lint_rmul (hN.right n0 hn0) hG2
  rw [MeasureTheory.lintegral_prod _ hm1.aemeasurable, MeasureTheory.lintegral_prod _ hm2.aemeasurable]
  simp_rw [inner]
  rw [MeasureTheory.lintegral_lintegral_swap (f := fun (x y : Formalism.QuantumDeterminants.Mt k r) => F (fun i j => (Matrix.of x * h0 * Matrix.of y) i j))
      hm3.aemeasurable,
    MeasureTheory.lintegral_lintegral_swap (f := fun (x y : Formalism.QuantumDeterminants.Mt k r) => F (fun i j => (Matrix.of x * Matrix.of y) i j))
      hm2.aemeasurable]

  refine MeasureTheory.lintegral_congr fun y => ?_
  have hG3 : Measurable (fun w : Formalism.QuantumDeterminants.Mt k r => F (fun i j => (Matrix.of w * Matrix.of y) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun w : Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of w * Matrix.of y) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have e3 : ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x * h0 * Matrix.of y =
      Matrix.of (B.rmulF h0 x) * Matrix.of y := fun x => rfl
  simp_rw [e3]
  exact lint_rmul (hW.right h0 hh0) hG3

end Formalism.FourierDecayAlt.P.S3dx4
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCHolRest
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem phase_holomorphy_holds : GTCPhHol := by
  intro TT u hu h1 R _ hR
  exact Ph.hol_unit (TT := TT) hu (fun ζ hζ => h1 ζ hζ) hR

theorem phase_curvature_holds : GTCPhCurv := by
  intro TT u hu h1 ζ hζ
  exact Ph.curv_unit (TT := TT) hu (fun ζ hζ => h1 ζ hζ) hζ

theorem connection_phase_holds : GTCConnPhase := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hyp e A B u hAB hu hC
  exact connF_phase P (tt_nonneg_of_hyp hyp) Bs d e A B u hAB hC hu

theorem gTCHol_of_ref (hRef : GTCRef) : GTCHol :=
  gTCHol_of_cut hRef phase_relation_holds connection_uniqueness_holds connection_phase_holds phase_holomorphy_holds

theorem gTCCurv_of_ref (hRef : GTCRef) : GTCCurv :=
  gTCCurv_of_cut hRef phase_relation_holds connection_uniqueness_holds connection_phase_holds phase_curvature_holds

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

