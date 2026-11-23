module

public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0021
public import Formalism.HermitianCurvature.Bundle0009
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0051
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0016
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0053
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelOneWordEstimate
section
namespace Formalism.FourierDecayAlt.P.PBD

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd

def LevelOneWordEstimate : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (q : ℝ → ℝ) (w : List (Letter ℝ S)) (N : ℕ) (dl Y : ℝ),
    8 ≤ N → w.length ≤ N → (N : ℝ) ^ 2 / 8 ≤ dl →
    (∀ l ∈ w, if l.plus then dl ≤ |Y - l.pt| else dl ≤ |Y - l.pt| ∧ dl ≤ |Y - (l.pt - 1)|) →
    q Y ≠ 0 →
    Real.exp (-2) ≤ qw q w Y / q Y ∧ qw q w Y / q Y ≤ Real.exp 2

private lemma exp_le_succ_div_self_le_exp_of_le_abs {z dl : ℝ} (hdl : 8 ≤ dl) (hz : dl ≤ |z|) :
    Real.exp (-2 * (1 / dl)) ≤ (z + 1) / z ∧ (z + 1) / z ≤ Real.exp (1 / dl) := by
  have hdl0 : 0 < dl := by linarith
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, abs_zero] at hz
    linarith
  have hx : |1 / z| ≤ 1 / dl := by
    rw [abs_div, abs_one]
    exact one_div_le_one_div_of_le hdl0 hz
  have hx8 : 1 / dl ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) hdl
  have hx0 : 0 < 1 / dl := by positivity
  rw [add_div, div_self hz0]
  have h1 := abs_le.mp hx
  constructor
  · have hexp : 1 + 2 * (1 / dl) ≤ Real.exp (2 * (1 / dl)) := by
      linarith [Real.add_one_le_exp (2 * (1 / dl))]
    have hone : Real.exp (-2 * (1 / dl)) * Real.exp (2 * (1 / dl)) = 1 := by
      rw [← Real.exp_add]
      simp
    have hpos := Real.exp_pos (-2 * (1 / dl))
    have h2 : Real.exp (-2 * (1 / dl)) * (1 + 2 * (1 / dl)) ≤ 1 := by
      calc Real.exp (-2 * (1 / dl)) * (1 + 2 * (1 / dl))
          ≤ Real.exp (-2 * (1 / dl)) * Real.exp (2 * (1 / dl)) := mul_le_mul_of_nonneg_left hexp hpos.le
        _ = 1 := hone
    have h3 : Real.exp (-2 * (1 / dl)) ≤ 1 - 1 / dl := by
      by_contra hc
      push_neg at hc
      have h4 : (1 - 1 / dl) * (1 + 2 * (1 / dl)) < Real.exp (-2 * (1 / dl)) * (1 + 2 * (1 / dl)) :=
        mul_lt_mul_of_pos_right hc (by positivity)
      nlinarith [mul_nonneg hx0.le (by linarith : (0 : ℝ) ≤ 1 - 2 * (1 / dl))]
    linarith [h1.1]
  · linarith [Real.add_one_le_exp (1 / dl), h1.2]

private lemma exp_le_qw_div_le_exp_of_far_letters {S : Type} (q : ℝ → ℝ) (dl Y : ℝ) (hdl : 8 ≤ dl) (hq : q Y ≠ 0)
    (w : List (Letter ℝ S))
    (hw : ∀ l ∈ w, if l.plus then dl ≤ |Y - l.pt| else dl ≤ |Y - l.pt| ∧ dl ≤ |Y - (l.pt - 1)|) :
    Real.exp (-2 * (1 / dl) * w.length) ≤ qw q w Y / q Y ∧ qw q w Y / q Y ≤ Real.exp (1 / dl * w.length) := by
  induction w with
  | nil => simp [qw, div_self hq]
  | cons l w ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun l' hl' => hw l' (List.mem_cons_of_mem l hl'))
    have hl := hw l (List.mem_cons.2 (Or.inl rfl))
    obtain ⟨F, hF, hF1, hF2⟩ : ∃ F, qw q (l :: w) Y / q Y = qw q w Y / q Y * F ∧
        Real.exp (-2 * (1 / dl)) ≤ F ∧ F ≤ Real.exp (1 / dl) := by
      cases hp : l.plus
      · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hl
        have hz : dl ≤ |l.pt - Y - 1| := by
          rw [show l.pt - Y - 1 = -(Y - (l.pt - 1)) by ring, abs_neg]
          exact hl.2
        refine ⟨(l.pt - Y - 1 + 1) / (l.pt - Y - 1), ?_, exp_le_succ_div_self_le_exp_of_le_abs hdl hz⟩
        simp only [qw, hp, Bool.false_eq_true, ↓reduceIte]
        rw [mul_div_right_comm, show l.pt - Y - 1 + 1 = l.pt - Y by ring]
      · simp only [hp, ↓reduceIte] at hl
        refine ⟨(Y - l.pt + 1) / (Y - l.pt), ?_, exp_le_succ_div_self_le_exp_of_le_abs hdl hl⟩
        simp only [qw, hp, ↓reduceIte]
        rw [mul_div_right_comm]
    have hA : 0 < Real.exp (-2 * (1 / dl) * w.length) := Real.exp_pos _
    have hr0 : 0 ≤ qw q w Y / q Y := le_trans hA.le ih1
    have hF0 : 0 ≤ F := le_trans (Real.exp_pos _).le hF1
    rw [hF, List.length_cons]
    push_cast
    constructor
    · calc Real.exp (-2 * (1 / dl) * ((w.length : ℝ) + 1))
          = Real.exp (-2 * (1 / dl) * w.length) * Real.exp (-2 * (1 / dl)) := by
            rw [← Real.exp_add]
            ring_nf
        _ ≤ qw q w Y / q Y * F := mul_le_mul ih1 hF1 (Real.exp_pos _).le hr0
    · calc qw q w Y / q Y * F ≤ Real.exp (1 / dl * w.length) * Real.exp (1 / dl) :=
          mul_le_mul ih2 hF2 hF0 (Real.exp_pos _).le
        _ = Real.exp (1 / dl * ((w.length : ℝ) + 1)) := by
            rw [← Real.exp_add]
            ring_nf

theorem level_one_word_estimate : LevelOneWordEstimate := by
  intro S _ _ q w N dl Y hN hlen hdl hw hq
  have hN8 : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hdl8 : 8 ≤ dl := by nlinarith [mul_le_mul hN8 hN8 (by norm_num) (by linarith)]
  obtain ⟨h1, h2⟩ := exp_le_qw_div_le_exp_of_far_letters q dl Y hdl8 hq w hw
  have hdl0 : 0 < dl := by linarith
  have hlenR : (w.length : ℝ) ≤ N := by exact_mod_cast hlen
  have hx : (1 / dl) * w.length ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one hdl0]
    nlinarith [mul_le_mul_of_nonneg_left hN8 (by linarith : (0 : ℝ) ≤ N)]
  constructor
  · calc Real.exp (-2) ≤ Real.exp (-2 * (1 / dl) * w.length) := Real.exp_le_exp.2 (by nlinarith)
      _ ≤ _ := h1
  · calc _ ≤ Real.exp (1 / dl * w.length) := h2
      _ ≤ Real.exp 2 := Real.exp_le_exp.2 (by linarith)

end Formalism.FourierDecayAlt.P.PBD
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalNormNonneg
section
open Finset Filter Topology
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBA

open Formalism.FourierDecayAlt NumberField

section defeq
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
  (RR : Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)

end defeq

theorem extract_prob {ι X : Type} [Fintype ι] (U : Finset X) (θ : ℕ → ι → X → ℝ)
    (hθ : ∀ n A, TB.IsProb U (θ n A)) :
    ∃ (φ : ℕ → ℕ) (θ' : ι → X → ℝ), StrictMono φ ∧ (∀ A, TB.IsProb U (θ' A)) ∧
      ∀ A, ∀ x ∈ U, Tendsto (fun n => θ (φ n) A x) atTop (𝓝 (θ' A x)) := by
  classical
  let x : ℕ → (ι × U) → ℝ := fun n p => θ n p.1 p.2.1
  have hK : IsCompact (Set.Icc (0 : ι × U → ℝ) 1) := isCompact_Icc
  have hmem : ∀ n, x n ∈ Set.Icc (0 : ι × U → ℝ) 1 := by
    intro n
    refine ⟨fun p => (hθ n p.1).1 _, fun p => ?_⟩
    have h := Finset.single_le_sum (fun y _ => (hθ n p.1).1 y) p.2.2
    rw [(hθ n p.1).2.2] at h
    exact h
  obtain ⟨y, _, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hl : ∀ A z (h : z ∈ U), Tendsto (fun n => θ (φ n) A z) atTop (𝓝 (y (A, ⟨z, h⟩))) := fun A z h =>
    ((continuous_apply (A, (⟨z, h⟩ : U))).tendsto y).comp hlim
  refine ⟨φ, fun A z => if h : z ∈ U then y (A, ⟨z, h⟩) else 0, hφ, ?_, ?_⟩
  · intro A
    refine ⟨fun z => ?_, fun z hz => by simp [hz], ?_⟩
    · by_cases h : z ∈ U
      · simp only [h, dite_true]
        exact ge_of_tendsto' (hl A z h) fun n => (hθ (φ n) A).1 z
      · simp [h]
    · have hs : Tendsto (fun n => ∑ z ∈ U, θ (φ n) A z) atTop
          (𝓝 (∑ z ∈ U, if h : z ∈ U then y (A, ⟨z, h⟩) else 0)) := by
        apply tendsto_finsetSum
        intro z hz
        simp only [hz, dite_true]
        exact hl A z hz
      have h1 : (fun n => ∑ z ∈ U, θ (φ n) A z) = fun _ => (1 : ℝ) := funext fun n => (hθ (φ n) A).2.2
      rw [h1] at hs
      exact tendsto_nhds_unique hs tendsto_const_nhds
  · intro A z hz
    simp only [hz, dite_true]
    exact hl A z hz

section conv
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
  (RR : ℕ → Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)

theorem gram_withRR (n : ℕ) (ε : ℝ) (i : ℕ) (w : C.Word S.f) (p q : TB.Pt E) :
    (KB.withRR S (RR n)).gram ε i w p q = if i ≤ S.G.r + 1 then ∏ v, ((√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G
      (C.loc (S.σ v) p)) * √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G (C.loc (S.σ v) q)) : ℝ) : ℂ) *
        RR n v ε i (w v) (C.loc (S.σ v) p) (C.loc (S.σ v) q) else 0 := rfl

theorem gram_S (ε : ℝ) (i : ℕ) (w : C.Word S.f) (p q : TB.Pt E) :
    S.gram ε i w p q = if i ≤ S.G.r + 1 then ∏ v, ((√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G
      (C.loc (S.σ v) p)) * √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G (C.loc (S.σ v) q)) : ℝ) : ℂ) *
        (S.pd v).RR ε i (w v) (C.loc (S.σ v) p) (C.loc (S.σ v) q) else 0 := rfl

variable {S RR}

theorem gram_tendsto
    (hconv : ∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ p q,
      Tendsto (fun n => RR n v ε i a p q) atTop (𝓝 ((S.pd v).RR ε i a p q)))
    {ε : ℝ} (hε : 0 < ε) (i : ℕ) (w : S.W) (p q : TB.Pt E) :
    Tendsto (fun n => (KB.withRR S (RR n)).gram ε i w.1 p q) atTop (𝓝 (S.gram ε i w.1 p q)) := by
  simp only [gram_withRR, gram_S]
  split_ifs
  · apply tendsto_finsetProd
    intro v _
    exact tendsto_const_nhds.mul (hconv v ε hε i _ ⟨w, rfl⟩ _ _)
  · exact tendsto_const_nhds

theorem nst_tendsto
    (hconv : ∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ p q,
      Tendsto (fun n => RR n v ε i a p q) atTop (𝓝 ((S.pd v).RR ε i a p q)))
    {ε : ℝ} (hε : 0 < ε) (i s : ℕ) (w : S.W) (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ) (t t' : E) :
    Tendsto (fun n => (KB.withRR S (RR n)).base.Nst ε i s w Y κ t t') atTop
      (𝓝 (S.base.Nst ε i s w Y κ t t')) := by
  have e1 : ∀ n, (KB.withRR S (RR n)).base.Nst ε i s w Y κ t t' = (∑ h ∈ Y, ∑ h' ∈ Y,
      κ h h' * (KB.withRR S (RR n)).gram ε i w.1 (TB.join h s t) (TB.join h' s t')) / (S.base.wt w : ℂ) :=
    fun n => rfl
  have e2 : S.base.Nst ε i s w Y κ t t' = (∑ h ∈ Y, ∑ h' ∈ Y,
      κ h h' * S.gram ε i w.1 (TB.join h s t) (TB.join h' s t')) / (S.base.wt w : ℂ) := rfl
  rw [e2]; simp only [e1]
  apply Tendsto.div_const
  apply tendsto_finsetSum; intro h _
  apply tendsto_finsetSum; intro h' _
  exact tendsto_const_nhds.mul (gram_tendsto hconv hε i w _ _)

theorem base_count_tendsto
    (hconv : ∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ p q,
      Tendsto (fun n => RR n v ε i a p q) atTop (𝓝 ((S.pd v).RR ε i a p q)))
    {ε : ℝ} (hε : 0 < ε) (k : ℕ) (w : S.W) (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ) :
    Tendsto (fun n => (KB.withRR S (RR n)).base.N0 ε k w Y κ) atTop (𝓝 (S.base.N0 ε k w Y κ)) := by
  have e1 : ∀ n, (KB.withRR S (RR n)).base.N0 ε k w Y κ = (∑ h ∈ Y, ∑ h' ∈ Y,
      κ h h' * (KB.withRR S (RR n)).gram ε k w.1 h h').re / S.base.wt w := fun n => rfl
  have e2 : S.base.N0 ε k w Y κ = (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * S.gram ε k w.1 h h').re / S.base.wt w := rfl
  rw [e2]; simp only [e1]
  apply Tendsto.div_const
  apply (Complex.continuous_re.tendsto _).comp
  apply tendsto_finsetSum; intro h _
  apply tendsto_finsetSum; intro h' _
  exact tendsto_const_nhds.mul (gram_tendsto hconv hε k w _ _)

theorem gram_psd {S : C.HidaSetting E Wp Wq} (hP : C.ThmPPos S) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (w : S.W)
    (Y : Finset (TB.Pt E)) : TB.PSDOn Y (fun h h' => S.gram ε k w.1 h h') := by
  classical
  by_cases hk : k ≤ S.G.r + 1
  · have : ∀ v ∈ (univ : Finset (Fin S.f)), TB.PSDOn Y
        (fun h h' => S.gramLoc v ε k (w.1 v) (C.loc (S.σ v) h) (C.loc (S.σ v) h')) := by
      intro v _
      exact JCx1.decay.psd_pull (Y.image (C.loc (S.σ v))) _ (hP v ε hε k hk w _) Y _
        (fun h hh => Finset.mem_image_of_mem _ hh)
    refine Jx7.psd_congr ?_ (Jx7.psd_prod univ _ this)
    intro x _ y _
    simp only [C.HidaSetting.gram, hk, if_true]
  · refine Jx7.psd_congr ?_ (Jx7.psd_zero (F := Y))
    intro x _ y _
    simp only [C.HidaSetting.gram, hk, if_false]

theorem local_norm_nonneg_alt {S : C.HidaSetting E Wp Wq} (hP : C.ThmPPos S) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (w : S.W)
    (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ) (hκ : TB.PSDOn Y κ) : 0 ≤ S.base.N0 ε k w Y κ := by
  have e2 : S.base.N0 ε k w Y κ = (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * S.gram ε k w.1 h h').re / S.base.wt w := rfl
  rw [e2]
  apply div_nonneg (BaseGramNonnegativity.sum_re_nonneg Y κ _ hκ (gram_psd hP hε k w Y))
  show 0 ≤ C.Word.size S.P w.1
  unfold C.Word.size
  exact Finset.prod_nonneg fun v _ => List.prod_nonneg fun x hx => by
    obtain ⟨a, _, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg _

end conv

theorem limit_closed : KB.LimitClosed := by
  intro E _ _ _ Wp Wq _ _ _ _ S RR hconv
  refine ⟨?_, ?_, ?_⟩
  · intro Λ hL ε hε i s hs hsi hir w hw hcnt
    choose θn hθn hbd using fun n => hL n ε hε i s hs hsi hir w hw hcnt
    obtain ⟨φ, θ, hφ, hθ, hlim⟩ := extract_prob (ι := Finset (Fin S.f)) (X := S.W × S.W)
      (S.base.Wb (S.base.cnt w + S.base.K) ×ˢ S.base.Wb (S.base.cnt w + S.base.K)) (fun n => θn n) hθn
    refine ⟨θ, hθ, ?_⟩
    intro Y T κ hY hκ t ht t' ht' h0 h0' ho A
    have h1 : ∀ n, (∏ v ∈ A, S.base.av v (t⁻¹ - t'⁻¹) ^ S.base.K) *
        ‖(KB.withRR S (RR (φ n))).base.Nst ε i s w Y (TB.blk κ s t t') t t'‖ ≤
        (∏ v ∈ A, Λ (i - s + 1) s v ^ S.base.K) *
          ∑ x ∈ S.base.Wb (S.base.cnt w + S.base.K) ×ˢ S.base.Wb (S.base.cnt w + S.base.K), θn (φ n) A x *
            ((((KB.withRR S (RR (φ n))).base.Nst ε i s x.1 Y (TB.blk κ s t t) t t).re +
              ((KB.withRR S (RR (φ n))).base.Nst ε i s x.2 Y (TB.blk κ s t' t') t' t').re) / 2) :=
      fun n => hbd (φ n) Y T κ hY hκ t ht t' ht' h0 h0' ho A
    refine le_of_tendsto_of_tendsto' (b := (atTop : Filter ℕ)) ?_ ?_ h1
    · exact tendsto_const_nhds.mul ((nst_tendsto hconv hε i s w Y _ t t').comp hφ.tendsto_atTop).norm
    · refine tendsto_const_nhds.mul (tendsto_finsetSum _ fun x hx => (hlim A x hx).mul ?_)
      refine Tendsto.div_const (Tendsto.add ?_ ?_) _
      · exact (Complex.continuous_re.tendsto _).comp ((nst_tendsto hconv hε i s x.1 Y _ t t).comp hφ.tendsto_atTop)
      · exact (Complex.continuous_re.tendsto _).comp
          ((nst_tendsto hconv hε i s x.2 Y _ t' t').comp hφ.tendsto_atTop)
  · intro Λ' hL ε hε s hs hsr w hw hcnt
    choose θn hθn hbd using fun n => hL n ε hε s hs hsr w hw hcnt
    obtain ⟨φ, θ, hφ, hθ, hlim⟩ := extract_prob (ι := Finset (Fin S.f)) (X := S.W)
      (S.base.Wb (S.base.cnt w + S.base.K)) (fun n => θn n) hθn
    refine ⟨θ, hθ, ?_⟩
    intro Y hY κ hκ t ht B
    have h1 : ∀ n, ((KB.withRR S (RR (φ n))).base.Nst ε (S.G.r + 1) s w Y κ t t).re ≤
        (∏ v ∈ B, (S.base.av v t * Λ' (S.G.r + 2 - s) s v) ^ (2 * S.base.K)) *
          ∑ w' ∈ S.base.Wb (S.base.cnt w + S.base.K), θn (φ n) B w' *
            ((KB.withRR S (RR (φ n))).base.Nst ε (S.G.r + 1) s w' Y κ t t).re :=
      fun n => hbd (φ n) Y hY κ hκ t ht B
    refine le_of_tendsto_of_tendsto' (b := (atTop : Filter ℕ)) ?_ ?_ h1
    · exact (Complex.continuous_re.tendsto _).comp
        ((nst_tendsto hconv hε (S.G.r + 1) s w Y κ t t).comp hφ.tendsto_atTop)
    · refine tendsto_const_nhds.mul (tendsto_finsetSum _ fun x hx => (hlim B x hx).mul ?_)
      exact (Complex.continuous_re.tendsto _).comp
        ((nst_tendsto hconv hε (S.G.r + 1) s x Y κ t t).comp hφ.tendsto_atTop)
  · intro C₄ hP _ hSF ε hε i s hs hsi hir w hw hcnt hvol
    set Bd := C₄ ^ (S.base.f * s) * (∏ s' ∈ Ico 1 s, S.base.vol (i - s + 1) s')
    have H : ∀ n, ∃ θ : Unit → S.W → ℝ, (∀ u, TB.IsProb (S.base.Wb (S.base.cnt w + s * S.base.K)) (θ u)) ∧
        ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = i - s) → ∀ κ, TB.PSDOn Y κ →
          ∀ (t₀ : E) (T : Finset E), (∀ t ∈ T, t ≠ 0 ∧ t - t₀ ∈ S.base.La (i - s + 1) s) →
            ∑ t ∈ T, ((KB.withRR S (RR n)).base.Nst ε i s w Y κ t t).re ≤
              Bd * ∑ w' ∈ S.base.Wb (S.base.cnt w + s * S.base.K), θ () w' *
                (KB.withRR S (RR n)).base.N0 ε (i - s) w' Y κ := by
      intro n
      obtain ⟨Mv, hMv, θ, hθ, hb⟩ := hSF n ε hε i s hs hsi hir w hw hcnt hvol
      refine ⟨fun _ => θ, fun _ => hθ, ?_⟩
      intro Y hY κ hκ t₀ T hT
      refine (hb Y hY κ hκ t₀ T hT).trans ?_
      apply mul_le_mul_of_nonneg_right hMv
      exact Finset.sum_nonneg fun w' _ => mul_nonneg (hθ.1 w') (local_norm_nonneg_alt (hP n) hε _ w' Y κ hκ)
    choose θn hθn hbd using H
    obtain ⟨φ, θ, hφ, hθ, hlim⟩ := extract_prob _ θn hθn
    refine ⟨Bd, le_refl _, θ (), hθ (), ?_⟩
    intro Y hY κ hκ t₀ T hT
    have h1 : ∀ n, ∑ t ∈ T, ((KB.withRR S (RR (φ n))).base.Nst ε i s w Y κ t t).re ≤
        Bd * ∑ w' ∈ S.base.Wb (S.base.cnt w + s * S.base.K), θn (φ n) () w' *
          (KB.withRR S (RR (φ n))).base.N0 ε (i - s) w' Y κ := fun n => hbd (φ n) Y hY κ hκ t₀ T hT
    refine le_of_tendsto_of_tendsto' (b := (atTop : Filter ℕ)) ?_ ?_ h1
    · exact tendsto_finsetSum _ fun t _ => (Complex.continuous_re.tendsto _).comp
        ((nst_tendsto hconv hε i s w Y κ t t).comp hφ.tendsto_atTop)
    · refine tendsto_const_nhds.mul (tendsto_finsetSum _ fun x hx => (hlim () x hx).mul ?_)
      exact (base_count_tendsto hconv hε (i - s) x Y κ).comp hφ.tendsto_atTop

end Formalism.FourierDecayAlt.P.PBA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MirrorResidueSplittingHolds
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

section
variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r}

theorem inverse_mul_regular_element {y : ℂ} (hy : RegY P y) : xInvM P y * xA P (DQ P) y = 1 := by
  unfold xInvM xA
  rw [← map_mul]
  have : ((fun π => (M.xC P π y)⁻¹) * fun π => M.xC P π y) = (1 : M.Ty P → ℂ) := by
    funext π; simp only [Pi.mul_apply, Pi.one_apply]; exact inv_mul_cancel₀ (hy π)
  rw [this, map_one]

theorem jdr_kap_DG (g : M.Ty P → ℂ) {z : A P (DQ P)} (hz : z ∈ Formalism.FourierDecayAlt.P.MAx3.H.DG P) :
    kap P (DQ P) g * z = z * kap P (DQ P) g := Formalism.FourierDecayAlt.P.MAx3.H.kap_comm_DG P g hz

theorem jdr_SC_DG {z : A P (DQ P)} (hz : z ∈ Formalism.FourierDecayAlt.P.MAx3.H.SC P) : z ∈ Formalism.FourierDecayAlt.P.MAx3.H.DG P := by
  obtain ⟨w, rfl⟩ := hz
  exact Formalism.FourierDecayAlt.P.MAx3.H.sc_memDG P w

end

theorem residue_splitting_holds : ResidueSplittingModelAlgebra := by
  intro P L hL y hy
  obtain ⟨hDr, hDrb, hDri, -⟩ := Formalism.FourierDecayAlt.P.MAx3.H.DrSC hL
  have hGG : L.GG = ggA P (DQ P) := hL.2.2.2.2.2.2.2.2.2.2.1
  have hGGsc : L.GG ∈ Formalism.FourierDecayAlt.P.MAx3.H.SC P := (Formalism.FourierDecayAlt.P.MAx3.H.levSC hL).2.2.2.2.2.2.2.2.1
  have hl0 : L.l0 y = l0A P (DQ P) y := by
    obtain ⟨-, -, -, -, -, -, -, -, hzb, -, -, hgi, hn, -, -⟩ := hL
    simp only [LevelData.l0, l0A, hn, hzb, hgi]
  set X := xInvM P y with hXdef
  set x := xA P (DQ P) y with hxdef
  have hXx : X * x = 1 := inverse_mul_regular_element hy
  have cD : X * L.Drb = L.Drb * X := jdr_kap_DG _ (jdr_SC_DG hDrb)
  have cG : X * L.GG = L.GG * X := jdr_kap_DG _ (jdr_SC_DG hGGsc)
  have hDriDr : L.Dri * L.Dr = 1 := by
    rw [Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (Formalism.FourierDecayAlt.P.MAx3.H.memDri L) (Formalism.FourierDecayAlt.P.MAx3.H.memDr L)]
    exact Formalism.FourierDecayAlt.P.MAx3.H.Dr_Dri' L

  have hterm : ∀ l ∈ Finset.Icc 1 (P.k - 1),
      X * SSn P L l * kap P (DQ P) (fun π => M.xEx P {l} π y) * L.Ahat y =
        X * L.Drb * (SS P (DQ P) l * kap P (DQ P) (fun π => M.xEx P {l} π y)) * L.Ar y := by
    intro l _
    have c1 : SS P (DQ P) l * L.Dr = L.Dr * SS P (DQ P) l := Formalism.FourierDecayAlt.P.MAx3.H.SS_comm_SC P l hDr
    have c2 : kap P (DQ P) (fun π => M.xEx P {l} π y) * L.Dr = L.Dr * kap P (DQ P) (fun π => M.xEx P {l} π y) :=
      jdr_kap_DG _ (jdr_SC_DG hDr)
    unfold SSn LevelData.Ahat
    calc X * (L.Drb * L.Dri * SS P (DQ P) l) * kap P (DQ P) (fun π => M.xEx P {l} π y) * (L.Dr * L.Ar y)
        = X * L.Drb * L.Dri * (SS P (DQ P) l * (kap P (DQ P) (fun π => M.xEx P {l} π y) * L.Dr)) * L.Ar y := by
          simp only [mul_assoc]
      _ = X * L.Drb * (L.Dri * L.Dr) * (SS P (DQ P) l * kap P (DQ P) (fun π => M.xEx P {l} π y)) * L.Ar y := by
          rw [c2, ← mul_assoc (SS P (DQ P) l), c1]; simp only [mul_assoc]
      _ = _ := by rw [hDriDr, mul_one]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Finset.mul_sum]
  have hS21 : (∑ l ∈ Finset.Icc 1 (P.k - 1), SS P (DQ P) l * kap P (DQ P) (fun π => M.xEx P {l} π y)) =
      weightedSumBis P (DQ P) y := rfl
  rw [hS21]

  have hR : X * RhM P L y = L.R0 y + X * L.Drb * weightedSumBis P (DQ P) y * L.Ar y := by
    unfold RhM LevelData.R0 t21 t22
    rw [hl0, hGG]
    have e1 : X * (ggA P (DQ P) * x) = ggA P (DQ P) := by
      rw [← mul_assoc, ← hGG, cG, mul_assoc, hXx, mul_one]
    have e2 : X * (ggA P (DQ P) * x * l0A P (DQ P) y) = ggA P (DQ P) * l0A P (DQ P) y := by
      rw [← mul_assoc X, e1]
    calc X * (L.Drb * ((ggA P (DQ P) * x * l0A P (DQ P) y + weightedSumBis P (DQ P) y) * L.Ar y + ggA P (DQ P) * x * L.Br y))
        = L.Drb * ((X * (ggA P (DQ P) * x * l0A P (DQ P) y) + X * weightedSumBis P (DQ P) y) * L.Ar y +
            X * (ggA P (DQ P) * x) * L.Br y) := by
          rw [← mul_assoc, cD, mul_assoc]; simp only [mul_add, add_mul, mul_assoc]
      _ = L.Drb * ggA P (DQ P) * (l0A P (DQ P) y * L.Ar y + L.Br y) + X * L.Drb * weightedSumBis P (DQ P) y * L.Ar y := by
          rw [e1, e2, cD]; simp only [mul_add, add_mul, mul_assoc]; abel
  rw [hR]; abel

theorem mirror_residue_splitting_holds : MirrorResidueSplittingModelAlgebra := by
  intro P L hL y hy
  obtain ⟨hDr, hDrb, -, hDrbi⟩ := Formalism.FourierDecayAlt.P.MAx3.H.DrSC hL
  have hGG : L.GG = ggA P (DQ P) := hL.2.2.2.2.2.2.2.2.2.2.1
  have hGGsc : L.GG ∈ Formalism.FourierDecayAlt.P.MAx3.H.SC P := (Formalism.FourierDecayAlt.P.MAx3.H.levSC hL).2.2.2.2.2.2.2.2.1
  have hm0 : L.m0 y = m0A P (DQ P) y := by
    obtain ⟨-, -, -, -, -, -, hz, -, -, -, -, hgi, -, hns, -⟩ := hL
    simp only [LevelData.m0, m0A, hns, hz, hgi]
  have sDrb : star L.Drb = L.Dr := by
    unfold LevelData.Drb LevelData.Dr
    rw [Formalism.FourierDecayAlt.P.MAx3.H.star_list_prod', List.map_ofFn]
    have : (star ∘ L.cb) = L.c := funext fun l => by
      obtain ⟨-, -, hc, -, hcb, -⟩ := hL
      show star (L.cb l) = L.c l
      rw [hcb, hc]
      simp only [cbA, cA, sc, Matrix.scalar_apply, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
      rfl
    rw [this, Formalism.FourierDecayAlt.P.MAx3.H.rev_prod L]
    intro x hx; obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact Formalism.FourierDecayAlt.P.MAx3.H.memF L (m_c L l)
  have sDri : star L.Dri = L.Drbi := by
    unfold LevelData.Dri LevelData.Drbi
    rw [Formalism.FourierDecayAlt.P.MAx3.H.star_list_prod', List.map_ofFn]
    have : (star ∘ L.ci) = L.cbi := funext fun l => by
      obtain ⟨-, -, -, hci, -, hcbi, -⟩ := hL
      show star (L.ci l) = L.cbi l
      rw [hci, hcbi]
      simp only [ciA, cbiA, sc, Matrix.scalar_apply, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
      rfl
    rw [this, Formalism.FourierDecayAlt.P.MAx3.H.rev_prod L]
    intro x hx; obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact Formalism.FourierDecayAlt.P.MAx3.H.memF L (m_cbi L l)
  set X := xInvM P y with hXdef
  set x := xA P (DQ P) y with hxdef
  have hXx : X * x = 1 := inverse_mul_regular_element hy
  have cD : X * L.Dr = L.Dr * X := jdr_kap_DG _ (jdr_SC_DG hDr)
  have cG : X * L.GG = L.GG * X := jdr_kap_DG _ (jdr_SC_DG hGGsc)
  have hDrbiDrb : L.Drbi * L.Drb = 1 := by
    rw [Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (Formalism.FourierDecayAlt.P.MAx3.H.memDrbi L) (Formalism.FourierDecayAlt.P.MAx3.H.memDrb L)]
    exact Formalism.FourierDecayAlt.P.MAx3.H.Drb_Drbi' L
  have cDD : L.Dr * L.Drb = L.Drb * L.Dr :=
    Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (Formalism.FourierDecayAlt.P.MAx3.H.memDr L) (Formalism.FourierDecayAlt.P.MAx3.H.memDrb L)
  have hterm : ∀ l ∈ Finset.Icc 1 (P.k - 1),
      X * kap P (DQ P) (fun π => M.xEx P {l} π y) * star (SSn P L l) * L.Ahatv y =
        X * L.Dr * (kap P (DQ P) (fun π => M.xEx P {l} π y) * star (SS P (DQ P) l)) * L.Avr y := by
    intro l _
    have c1 : star (SS P (DQ P) l) * L.Dr = L.Dr * star (SS P (DQ P) l) := Formalism.FourierDecayAlt.P.MAx3.H.SSs_comm_SC l hDr
    have c2 : kap P (DQ P) (fun π => M.xEx P {l} π y) * L.Dr = L.Dr * kap P (DQ P) (fun π => M.xEx P {l} π y) :=
      jdr_kap_DG _ (jdr_SC_DG hDr)
    have hs : star (SSn P L l) = star (SS P (DQ P) l) * L.Drbi * L.Dr := by
      unfold SSn; rw [star_mul, star_mul, sDri, sDrb, mul_assoc]
    rw [hs]
    unfold LevelData.Ahatv
    calc X * kap P (DQ P) (fun π => M.xEx P {l} π y) * (star (SS P (DQ P) l) * L.Drbi * L.Dr) * (L.Drb * L.Avr y)
        = X * kap P (DQ P) (fun π => M.xEx P {l} π y) * star (SS P (DQ P) l) * (L.Drbi * (L.Dr * L.Drb)) *
            L.Avr y := by simp only [mul_assoc]
      _ = X * (kap P (DQ P) (fun π => M.xEx P {l} π y) * (star (SS P (DQ P) l) * L.Dr)) * L.Avr y := by
          rw [cDD, ← mul_assoc L.Drbi, hDrbiDrb, one_mul]; simp only [mul_assoc]
      _ = _ := by rw [c1, ← mul_assoc (kap P (DQ P) _), c2]; simp only [mul_assoc]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Finset.mul_sum]
  have hS12 : (∑ l ∈ Finset.Icc 1 (P.k - 1), kap P (DQ P) (fun π => M.xEx P {l} π y) * star (SS P (DQ P) l)) =
      S12 P (DQ P) y := rfl
  rw [hS12]
  have hR : X * RhvM P L y = L.R0v y + X * L.Dr * S12 P (DQ P) y * L.Avr y := by
    unfold RhvM LevelData.R0v t12 t22
    rw [hm0, hGG]
    have e1 : X * (ggA P (DQ P) * x) = ggA P (DQ P) := by
      rw [← mul_assoc, ← hGG, cG, mul_assoc, hXx, mul_one]
    have e2 : X * (ggA P (DQ P) * x * m0A P (DQ P) y) = ggA P (DQ P) * m0A P (DQ P) y := by
      rw [← mul_assoc X, e1]
    calc X * (L.Dr * ((ggA P (DQ P) * x * m0A P (DQ P) y + S12 P (DQ P) y) * L.Avr y + ggA P (DQ P) * x * L.Bvr y))
        = L.Dr * ((X * (ggA P (DQ P) * x * m0A P (DQ P) y) + X * S12 P (DQ P) y) * L.Avr y +
            X * (ggA P (DQ P) * x) * L.Bvr y) := by
          rw [← mul_assoc, cD, mul_assoc]; simp only [mul_add, add_mul, mul_assoc]
      _ = L.Dr * ggA P (DQ P) * (m0A P (DQ P) y * L.Avr y + L.Bvr y) + X * L.Dr * S12 P (DQ P) y * L.Avr y := by
          rw [e1, e2, cD]; simp only [mul_add, add_mul, mul_assoc]; abel
  rw [hR]; abel

end

end Formalism.FourierDecayAlt.P.CutMP
end

