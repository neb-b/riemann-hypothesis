module

public import Mathlib
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.VanishingOfL2Equivariant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0046
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0049
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0045
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixTranspose
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LduDecompositionExists

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleAtomicFormOneReduction
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

set_option maxHeartbeats 3200000

namespace Formalism.FourierDecayAlt.P

namespace UnipotentHaarMeasurability

open Formalism.FourierDecayAlt.ThreeDimData

theorem smooth_admissible_form_one_side : AtFormAdmOneOfSteps := by
  intro hSch hBC hNI hBB hSh hKF hZ hZD hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, -, -, -, -, hW, hN, hG, hq⟩ := hS'
  obtain ⟨hBC1, -, -, -⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  obtain ⟨d, hd, hSd⟩ := hSch k r ε lam H σ μG hlam hσ hG
  have hw0n : w0 ≠ 0 := by
    obtain ⟨P, -, hn1, -⟩ := hw0
    intro h0; rw [h0, norm_zero] at hn1; exact zero_ne_one hn1
  have hdeg : ∀ x : H, x ≠ 0 → PI.BesselPeriodGGP.fdegH μG σ x = d := fun x hx => DDSmoothness.fdeg_eq hd hSd hx
  have hmu := DDSmoothness.muSof_facts hW hN
  have hae := DDSmoothness.ae_UH_of_quot hG.2.2.1 hmu.1 hmu.2 hq
  have hAs : ∀ v : H, IsAdm σ w0 v → v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
    intro v hv
    rcases hv with hv | hv
    · exact DDSmoothness.DD_smooth hIn.2.2.1 hlam hσ hw0 v hv
    · exact hIn.2.2.1 k r ε lam H σ hlam hσ v hv
  by_cases hnz : ∃ x ∈ DDsp σ w0, ∃ y ∈ DDsp σ w0, be z c π σ μW μN x y ≠ 0
  · obtain ⟨l, hl, hx1, hid⟩ := hSh hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz
    have hK := hKF hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS l hl hx1 hid
    have hI : ∀ v : H, IsAdm σ w0 v → ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
        be z c π σ μW μN x v = (innerSL ℂ (l v)).smulRight (l x) := by
      intro v hv x hx
      rcases hv with hv | hv
      · exact hid x hx v hv
      · exact hK v hv x hx
    refine ⟨l, hl, fun x hx v hv => ⟨hBC1 x hx v hv, hI v hv x hx⟩, ?_⟩
    intro x hx hx0 v hv
    have hNv := (hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hx v hv (l v)).1
    rw [hI v hv v (hAs v hv)] at hNv
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply] at hNv
    rw [hdeg w0 hw0n] at hNv
    rw [hdeg x hx0]
    refine DDSmoothness.l2_norm_scaling _ _ (l v) _ _ (by positivity) hNv (hae.mono fun g hg => ?_)
    rw [hI v hv _ (PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε lam H σ hσ x hx _ hg)]
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  · push_neg at hnz
    have h0 := hZ hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz
    have h0D := hZD hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz
    refine ⟨fun _ => 0, DDSmoothness.bessel_zero, fun x hx v hv => ⟨hBC1 x hx v hv, ?_⟩,
      fun x _ _ v _ => by simp⟩
    show be z c π σ μW μN x v = _
    have hz0 : be z c π σ μW μN x v = 0 := by
      rcases hv with hv | hv
      · exact h0D v hv x hx
      · exact h0 v hv x hx
    rw [hz0]
    ext ξ; simp

end UnipotentHaarMeasurability

theorem admissible_atomic_form_one_reduction : Formalism.FourierDecayAlt.ThreeDimData.AtFormAdmOneOfSteps := UnipotentHaarMeasurability.smooth_admissible_form_one_side

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleWordLengthLe
section
open Matrix Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma admissible_word_mem_lie {n : ℕ} {w : List (Bool × Mat k r)} (h : admitted n w) : ∀ x ∈ w, inLie k r x.2 := by
  obtain ⟨u, v, hu, hv, -, rfl⟩ := h
  exact lie_LR (unit_lie hu) (unit_lie hv)

lemma admissible_word_length_le {n : ℕ} {w : List (Bool × Mat k r)} (h : admitted n w) : w.length ≤ n := by
  obtain ⟨u, v, -, -, hl, rfl⟩ := h
  rw [len_LR]
  exact hl

section defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def LSS (f : Mat k r → E) (S : Set (Mat k r)) : Prop :=
  ∀ g ∈ S, ∃ f' : Mat k r → E, ContDiff ℝ ∞ f' ∧ ∃ V : Set (Mat k r), IsOpen V ∧ g ∈ V ∧
    ∀ g' ∈ GV k r, g' ∈ V → f g' = f' g'

def UB (f : Mat k r → E) (S : Set (Mat k r)) (n : ℕ) (C : ℝ) (e γ : ℕ) : Prop :=
  ∀ w, admitted n w → ∀ g ∈ S, ‖Dw w f g‖ ≤ C * gN g ^ (e + γ * w.length)

lemma lss_of_contDiff {f : Mat k r → E} (hf : ContDiff ℝ ∞ f) (S : Set (Mat k r)) : LSS f S := by
  intro g _
  exact ⟨f, hf, univ, isOpen_univ, mem_univ g, fun _ _ _ => rfl⟩

lemma lss_mono {f : Mat k r → E} {S S' : Set (Mat k r)} (h : LSS f S) (hS : S' ⊆ S) : LSS f S' := fun g hg => h g (hS hg)

lemma lss_congr {f f₂ : Mat k r → E} {S : Set (Mat k r)} {V : Set (Mat k r)} (hV : IsOpen V) (hSV : S ⊆ V)
    (he : ∀ g ∈ GV k r, g ∈ V → f g = f₂ g) (h : LSS f₂ S) : LSS f S := by
  intro g hg
  obtain ⟨f', hf', W, hW, hgW, hfW⟩ := h g hg
  refine ⟨f', hf', V ∩ W, hV.inter hW, ⟨hSV hg, hgW⟩, ?_⟩
  intro g' hg' hgVW
  rw [he g' hg' hgVW.1, hfW g' hg' hgVW.2]

lemma ub_congr {f f₂ : Mat k r → E} {S : Set (Mat k r)} {V : Set (Mat k r)} (hV : IsOpen V) (hSV : S ⊆ V)
    (hSG : S ⊆ GV k r) (he : ∀ g ∈ GV k r, g ∈ V → f g = f₂ g) {n : ℕ} {C : ℝ} {e γ : ℕ} (h : UB f₂ S n C e γ) :
    UB f S n C e γ := by
  intro w hw g hg
  rw [Dw_congr_loc (admissible_word_mem_lie hw) hV he g (hSG hg) (hSV hg)]
  exact h w hw g hg

lemma lss_of_ckOn {f : Mat k r → E} {UU S : Set (Mat k r)} (hf : CkOn ⊤ UU f) (hS : S ⊆ UU) : LSS f S := by
  intro g hg
  obtain ⟨U, f', hU, hgU, hf', hfU⟩ := hf g (hS hg)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU g hgU
  let χ : ContDiffBump g := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hcl : Metric.closedBall g (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  refine ⟨fun x => χ x • f' x, ?_, Metric.ball g (ε / 4), Metric.isOpen_ball,
    Metric.mem_ball_self (by positivity), ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Metric.closedBall g (ε / 2)
    · exact χ.contDiff.contDiffAt.smul (hf'.contDiffAt (hU.mem_nhds (hcl hx)))
    · have hzero : (fun x => χ x • f' x) =ᶠ[𝓝 x] fun _ => (0 : E) := by
        filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hx] with y hy
        have hy' : ε / 2 ≤ dist y g := by
          simp only [mem_compl_iff, Metric.mem_closedBall, not_le] at hy
          exact hy.le
        have : χ y = 0 := χ.zero_of_le_dist hy'
        simp [this]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  · intro g' hg' hgb
    have h1 : χ g' = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hgb)
    dsimp only
    rw [h1, one_smul]
    exact hfU g' (hball (Metric.ball_subset_ball (by linarith) hgb)) hg'

lemma lss_clm {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (L : E →L[ℝ] E') {f : Mat k r → E}
    {S : Set (Mat k r)} (h : LSS f S) : LSS (fun g => L (f g)) S := by
  intro g hg
  obtain ⟨f', hf', V, hV, hgV, hfV⟩ := h g hg
  exact ⟨fun x => L (f' x), L.contDiff.comp hf', V, hV, hgV,
    fun g' hg' hgV' => by dsimp only; rw [hfV g' hg' hgV']⟩

lemma ub_clm {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (L : E →L[ℝ] E') {f : Mat k r → E}
    {S : Set (Mat k r)} (hSG : S ⊆ GV k r) (hl : LSS f S) {n : ℕ} {C : ℝ} {e γ : ℕ} (h : UB f S n C e γ) :
    UB (fun g => L (f g)) S n (‖L‖ * C) e γ := by
  intro w hw g hg
  obtain ⟨f', hf', V, hV, hgV, hfV⟩ := hl g hg
  have hlie := admissible_word_mem_lie hw
  have e1 := Dw_congr_loc hlie hV (f := fun x => L (f x)) (f₂ := fun x => L (f' x))
    (fun g' hg' hgV' => by rw [hfV g' hg' hgV']) g (hSG hg) hgV
  have e2 := Dw_congr_loc hlie hV hfV g (hSG hg) hgV
  have e3 : Dw w (fun x => L (f' x)) g = L (Dw w f' g) := congrFun (dw_clm L w hf') g
  rw [e1, e3, ← e2, mul_assoc]
  exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h w hw g hg) (norm_nonneg L))

lemma ub_mono {f : Mat k r → E} {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {n : ℕ} {C : ℝ} {e γ e' γ' : ℕ}
    (h : UB f S n C e γ) (hC : 0 ≤ C) (he : e ≤ e') (hγ : γ ≤ γ') : UB f S n C e' γ' := by
  intro w hw g hg
  have h1 := gN_ge_one (hSG hg)
  refine (h w hw g hg).trans (mul_le_mul_of_nonneg_left ?_ hC)
  exact pow_le_pow_right₀ h1 (Nat.add_le_add he (Nat.mul_le_mul_right _ hγ))

private lemma Dw_cons_const_eq_zero (c : E) (x : Bool × Mat k r) (w : List (Bool × Mat k r)) :
    Dw (x :: w) (fun _ : Mat k r => c) = fun _ => 0 := by
  induction w generalizing x with
  | nil =>
    funext g
    show Dx x (fun _ => c) g = 0
    rw [Dx_eq]
    exact deriv_const _ _
  | cons y w ih =>
    show Dx x (Dw (y :: w) fun _ => c) = fun _ => 0
    rw [ih]
    exact Dx_zero x

lemma ub_const (c : E) (S : Set (Mat k r)) (hSG : S ⊆ GV k r) (n : ℕ) (γ : ℕ) :
    UB (fun _ : Mat k r => c) S n ‖c‖ 0 γ := by
  intro w _ g hg
  have h0 : 0 ≤ gN g := (gN_pos (hSG hg)).le
  cases w with
  | nil =>
    show ‖c‖ ≤ ‖c‖ * gN g ^ (0 + γ * 0)
    simp
  | cons x w =>
    rw [Dw_cons_const_eq_zero]
    simp only [norm_zero]
    exact mul_nonneg (norm_nonneg c) (pow_nonneg h0 _)

end defs

section app

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma leibC (g : Mat k r) (M : ℝ) (w : List (Bool × Mat k r)) (a : Mat k r → (F →L[ℂ] E)) (b : Mat k r → F)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hM : ∀ w₁ w₂, Spl w w₁ w₂ → ‖Dw w₁ a g‖ * ‖Dw w₂ b g‖ ≤ M) :
    ‖Dw w (fun g => a g (b g)) g‖ ≤ 2 ^ w.length * M := by
  let R : (F →L[ℂ] E) →L[ℝ] (F →L[ℝ] E) := ContinuousLinearMap.restrictScalarsL ℂ F E ℝ ℝ
  have hR : ∀ T : F →L[ℂ] E, ‖R T‖ = ‖T‖ := fun T => ContinuousLinearMap.norm_restrictScalars T
  have hRa : ContDiff ℝ ∞ (fun x => R (a x)) := R.contDiff.comp ha
  have hD : ∀ w₁ : List (Bool × Mat k r), Dw w₁ (fun x => R (a x)) g = R (Dw w₁ a g) :=
    fun w₁ => congrFun (dw_clm R w₁ ha) g
  have key := leibA g M w (fun x => R (a x)) b hRa hb
    (fun w₁ w₂ hs => by rw [hD, hR]; exact hM w₁ w₂ hs)
  exact key

lemma lss_app {S : Set (Mat k r)} {a : Mat k r → (F →L[ℂ] E)} {b : Mat k r → F} (ha : LSS a S) (hb : LSS b S) :
    LSS (fun g => a g (b g)) S := by
  intro g hg
  obtain ⟨a', ha', V₁, hV₁, hg₁, haV⟩ := ha g hg
  obtain ⟨b', hb', V₂, hV₂, hg₂, hbV⟩ := hb g hg
  let R : (F →L[ℂ] E) →L[ℝ] (F →L[ℝ] E) := ContinuousLinearMap.restrictScalarsL ℂ F E ℝ ℝ
  refine ⟨fun x => a' x (b' x), ?_, V₁ ∩ V₂, hV₁.inter hV₂, ⟨hg₁, hg₂⟩, ?_⟩
  · exact cd_app (a := fun x => R (a' x)) (R.contDiff.comp ha') hb'
  · intro g' hg' hV
    dsimp only
    rw [haV g' hg' hV.1, hbV g' hg' hV.2]

lemma ub_app {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {a : Mat k r → (F →L[ℂ] E)} {b : Mat k r → F}
    (hla : LSS a S) (hlb : LSS b S) {n : ℕ} {Ca Cb : ℝ} {ea eb γ : ℕ} (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb)
    (ha : UB a S n Ca ea γ) (hb : UB b S n Cb eb γ) :
    UB (fun g => a g (b g)) S n (2 ^ n * (Ca * Cb)) (ea + eb) γ := by
  intro w hw g hg
  obtain ⟨a', ha', V₁, hV₁, hg₁, haV⟩ := hla g hg
  obtain ⟨b', hb', V₂, hV₂, hg₂, hbV⟩ := hlb g hg
  have hgG := hSG hg
  have h0 : 0 ≤ gN g := (gN_pos hgG).le
  have hra : ∀ w' : List (Bool × Mat k r), admitted n w' → Dw w' a g = Dw w' a' g :=
    fun w' hw' => Dw_congr_loc (admissible_word_mem_lie hw') hV₁ haV g hgG hg₁
  have hrb : ∀ w' : List (Bool × Mat k r), admitted n w' → Dw w' b g = Dw w' b' g :=
    fun w' hw' => Dw_congr_loc (admissible_word_mem_lie hw') hV₂ hbV g hgG hg₂
  have happ : Dw w (fun x => a x (b x)) g = Dw w (fun x => a' x (b' x)) g :=
    Dw_congr_loc (admissible_word_mem_lie hw) (hV₁.inter hV₂)
      (fun g' hg' hV => by rw [haV g' hg' hV.1, hbV g' hg' hV.2]) g hgG ⟨hg₁, hg₂⟩
  have key := leibC g (Ca * Cb * gN g ^ (ea + eb + γ * w.length)) w a' b' ha' hb' (by
    intro w₁ w₂ hs
    have hw₁ := Adm_sub hs.1 hw
    have hw₂ := Adm_sub hs.2.1 hw
    rw [← hra w₁ hw₁, ← hrb w₂ hw₂]
    have hexp : ea + γ * w₁.length + (eb + γ * w₂.length) = ea + eb + γ * w.length := by
      rw [← spl_len hs]; ring
    calc ‖Dw w₁ a g‖ * ‖Dw w₂ b g‖
        ≤ (Ca * gN g ^ (ea + γ * w₁.length)) * (Cb * gN g ^ (eb + γ * w₂.length)) :=
          mul_le_mul (ha w₁ hw₁ g hg) (hb w₂ hw₂ g hg) (norm_nonneg _)
            (mul_nonneg hCa (pow_nonneg h0 _))
      _ = Ca * Cb * gN g ^ (ea + γ * w₁.length + (eb + γ * w₂.length)) := by rw [pow_add]; ring
      _ = Ca * Cb * gN g ^ (ea + eb + γ * w.length) := by rw [hexp])
  rw [happ]
  refine key.trans ?_
  have hM : 0 ≤ Ca * Cb * gN g ^ (ea + eb + γ * w.length) :=
    mul_nonneg (mul_nonneg hCa hCb) (pow_nonneg h0 _)
  have h2 : (2 : ℝ) ^ w.length ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (admissible_word_length_le hw)
  calc (2 : ℝ) ^ w.length * (Ca * Cb * gN g ^ (ea + eb + γ * w.length))
      ≤ 2 ^ n * (Ca * Cb * gN g ^ (ea + eb + γ * w.length)) := mul_le_mul_of_nonneg_right h2 hM
    _ = 2 ^ n * (Ca * Cb) * gN g ^ (ea + eb + γ * w.length) := by ring

end app

end Formalism.FourierDecayAlt.P.AdmissibleLieWords
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellDiagonalMap
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

set_option linter.unusedSimpArgs false

noncomputable section

namespace Formalism.FourierDecayAlt.P.BigCellDiagonalMap

variable {k j ρ : ℕ}

theorem leviElement_mul_mMap (W Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k ρ) (hW : IsUnit W.det) :
    muP k j ρ W * mMap k j ρ Z γ = mMap k j ρ (Wᴴ⁻¹ * Z) γ := by
  unfold mMap muP
  rw [Ux3.block3_mul]
  have h13 : W * (Zᴴ⁻¹ * G.wMat j) = (Wᴴ⁻¹ * Z)ᴴ⁻¹ * G.wMat j := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hW, Matrix.mul_assoc]
  have h31 : G.wMat j * Wᴴ⁻¹ * G.wMat j * (G.wMat j * Z) = G.wMat j * (Wᴴ⁻¹ * Z) := by
    rw [Matrix.mul_assoc, Ux4.w_w_mul, Matrix.mul_assoc]
  congr 1 <;> simp [h13, h31]

theorem leviElement_nset (p : Matrix (Fin j) (Fin j) ℂ) (hp : Formalism.DoubleCosetMeasures.IsUpUni p) : muP k j ρ p ∈ Nset k (j + ρ) := by
  have hdet : p.det ≠ 0 := by rw [Formalism.DoubleCosetMeasures.isUpUni_det ℂ hp]; exact one_ne_zero
  refine ⟨(Formalism.FourierDecayAlt.P.slice_membership k j ρ).2.1 p hdet, ?_, ?_⟩
  · intro a i hai
    obtain ⟨x, rfl⟩ := (eB k j ρ).surjective i
    obtain ⟨y, hy⟩ := (eB k j ρ).surjective (eI k (j + ρ) a)
    unfold muP
    rw [← hy, Ux3.block3_apply]
    simp only [(eB k j ρ).apply_eq_iff_eq]
    have hv := congrArg Fin.val hy
    have ha := a.isLt
    simp only [eI] at hv
    rw [← hv] at hai
    rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>
      simp only [Ux3.block_index_first_val, Ux3.block_index_middle_val, Ux3.block_index_last_val] at hv hai
    all_goals first
      | (exfalso; have := x.isLt; have := y.isLt; omega)
      | (simp [Matrix.one_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
          Matrix.fromCols_apply_inr]; done)
      | skip

    simp only [Matrix.fromBlocks_apply₁₁, Sum.inl.injEq]
    rcases eq_or_lt_of_le hai with h | h
    · have : x = y := Fin.ext h.symm
      subst this; simp [hp.2]
    · have hne : x ≠ y := fun e => by subst e; omega
      rw [if_neg hne]
      exact hp.1 (show y < x from h)
  · intro i c hc1 hc2 hi
    obtain ⟨x, rfl⟩ := (eB k j ρ).surjective i
    obtain ⟨y, rfl⟩ := (eB k j ρ).surjective c
    unfold muP
    rw [Ux3.block3_apply]
    simp only [(eB k j ρ).apply_eq_iff_eq]
    rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>
      simp only [Ux3.block_index_first_val, Ux3.block_index_middle_val, Ux3.block_index_last_val] at hc1 hc2 hi <;>
      first
      | (simp [Matrix.one_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
          Matrix.fromCols_apply_inr]; done)
      | (exfalso; have := x.isLt; have := y.isLt; omega)

def eW (k : ℕ) : Fin (2 * 0 + k + 1) ≃ Fin (k + 1) := finCongr (by omega)

def muOf (γ : B.Mat k 0) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := Matrix.reindex (eW k) (eW k) γ

theorem hb_eq (k : ℕ) : Hb k = Matrix.reindex (eW k) (eW k) (Hpk k 0) := by
  ext i j
  simp only [Hb, Hpk, eW, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.diagonal_apply, finCongr_symm,
    finCongr_apply, Fin.coe_cast, Fin.ext_iff, Fin.val_last]
  split_ifs <;> first | rfl | omega

theorem muOf_mem (γ : B.Mat k 0) (hγ : γ ∈ B.GV k 0) : (muOf γ)ᴴ * Hb k * muOf γ = Hb k := by
  have h : γᴴ * Hpk k 0 * γ = Hpk k 0 := hγ
  rw [hb_eq]
  simp only [muOf, Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, h]

theorem inv_diag {r : ℕ} (v : Fin r → ℂ) (hv : ∀ a, v a ≠ 0) :
    (Matrix.diagonal v)⁻¹ = Matrix.diagonal (fun a => (v a)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  exact inv_mul_cancel₀ (hv a)

theorem mMap_diag (r : ℕ) (d : Fin r → ℂ) (hd : ∀ a, d a ≠ 0) (γ : B.Mat k 0) :
    (mMap k r 0 (Matrix.diagonal d) γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
      bigCell k r d (muOf γ) := by
  ext i l
  obtain ⟨x, rfl⟩ := (eB k r 0).surjective i
  obtain ⟨y, rfl⟩ := (eB k r 0).surjective l
  unfold mMap
  rw [Matrix.diagonal_conjTranspose, inv_diag (star d) (fun a => by simpa [Pi.star_apply] using hd a), Ux3.block3_apply]
  have v1 := @Ux3.block_index_first_val k r 0
  have v2 := @Ux3.block_index_middle_val k r 0
  have v3 := @Ux3.block_index_last_val k r 0
  rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>
    simp only [bigCell, v1, v2, v3, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply]
  all_goals
    have hx := x.isLt
    have hy := y.isLt
    simp only [Fin.ext_iff, v1, v2, v3, esI, G.wMat, Matrix.of_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Ring.inverse_eq_inv', Pi.star_apply, Fin.val_rev, Pi.inv_apply, Complex.star_def, mul_one,
      one_mul, mul_zero, zero_mul]
    split_ifs <;> first
      | rfl
      | (exfalso; omega)
      | (congr 1; ext; simp only [Fin.val_mk]; omega)
      | (congr 2; ext; simp only [Fin.val_mk]; omega)
      | (intro h; exfalso; omega)
      | (simp; done)
      | (simp only [mul_one]; congr 3; ext; simp only [Fin.val_mk]; omega)
      | (simp only [muOf, eW, Matrix.reindex_apply, Matrix.submatrix_apply]; congr 1 <;> (ext; simp))
      | skip

theorem dmin_lead {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (l : ℕ) (hl : l ≤ r) : Dmin k r z z' g ⟨l, by omega⟩ = Formalism.FourierDecayAlt.S3.lead (Zh k r 0 g) l hl := by
  unfold Dmin Formalism.FourierDecayAlt.S3.lead
  congr 1
  ext a b
  simp only [Matrix.submatrix_apply]
  rw [Ux3.zhat_apply_low]
  · rfl
  · simp; omega
  · simp; omega

theorem cellDecomp : BigCellDecomposition.CellDecomp := by
  intro k r z z' g hg hD
  have hDl : ∀ (l : ℕ) (hl : l ≤ r), Formalism.FourierDecayAlt.S3.lead (Zh k r 0 g) l hl ≠ 0 := fun l hl => by
    rw [← dmin_lead z z' g l hl]; exact hD ⟨l, by omega⟩ hl
  have hDj : DjU k r 0 g ≠ 0 := by
    have h := Formalism.FourierDecayAlt.P.hat_z_minimum_degree k r 0 z z' g
    rw [← h]; exact hD ⟨r, by omega⟩ le_rfl
  obtain ⟨x, x', Z, γ, _hZ, hγ, hgeq⟩ := Ux3.bigCell_exists (k := k) (j := r) (ρ := 0) g hg hDj
  have hZh : Zh k r 0 g = Z := by rw [hgeq]; exact Formalism.FourierDecayAlt.P.hat_z_on_slice k r 0 x x' Z γ
  have hDZ : ∀ (l : ℕ) (hl : l ≤ r), Formalism.FourierDecayAlt.S3.lead Z l hl ≠ 0 := by rw [← hZh]; exact hDl
  obtain ⟨L, U, d, hL, hU, hLDU, hlead⟩ :=
    Formalism.FourierDecayAlt.P.ldu_decomposition_exists ℂ r Z (fun l hl => (hDZ l hl.le).isUnit)
  have hd : ∀ a, d a ≠ 0 := fun a h0 => by
    have h1 := hlead a.val a.isLt
    rw [h0, zero_mul] at h1
    exact hDZ (a.val + 1) a.isLt h1
  have hLh : Formalism.DoubleCosetMeasures.IsUpUni Lᴴ := by
    refine ⟨fun i j hij => ?_, fun a => ?_⟩
    · rw [Matrix.conjTranspose_apply, hL.1 hij, star_zero]
    · rw [Matrix.conjTranspose_apply, hL.2 a, star_one]
  have hLu : IsUnit L.det := by rw [Formalism.DoubleCosetMeasures.isLowUni_det ℂ hL]; exact isUnit_one
  have hLhu : IsUnit Lᴴ.det := by rw [Formalism.DoubleCosetMeasures.isUpUni_det ℂ hLh]; exact isUnit_one
  have hP : muP k r 0 Lᴴ ∈ Nset k (r + 0) := leviElement_nset _ hLh
  have hPu : IsUnit (muP k r 0 Lᴴ).det := Ux3.gv_det hP.1
  have h1 : muP k r 0 Lᴴ * mMap k r 0 Z γ = mMap k r 0 (Matrix.diagonal d) γ * muP k r 0 U := by
    rw [leviElement_mul_mMap _ _ _ hLhu, Ux4.mMap_mul_muP, hLDU, Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hLu, Matrix.one_mul]
  have key : mMap k r 0 Z γ = (muP k r 0 Lᴴ)⁻¹ * (mMap k r 0 (Matrix.diagonal d) γ * muP k r 0 U) := by
    rw [← h1, Matrix.nonsing_inv_mul_cancel_left _ _ hPu]
  refine ⟨muP k r 0 Lᴴ * Rn k r 0 x, WeylGroupFacts.mem_n_mul hP (Ux3.rn_nset x),
    muP k r 0 U * Rn k r 0 x', WeylGroupFacts.mem_n_mul (leviElement_nset _ hU) (Ux3.rn_nset x'), d, hd, muOf γ, muOf_mem γ hγ, ?_⟩
  rw [hgeq, key, ← mMap_diag r d hd γ, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

end Formalism.FourierDecayAlt.P.BigCellDiagonalMap

namespace Formalism.FourierDecayAlt.P

theorem big_cell_decomposition : BigCellDecomposition.CellDecomp := by
  exact BigCellDiagonalMap.cellDecomp

theorem psiOnto_true : Formalism.FourierDecayAlt.JF.PsiOnto := jf_psiOnto_of_cellDecomp BigCellDiagonalMap.cellDecomp

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnAdmLen
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.En

theorem admissible_length_holds : AdmLen := by
  intro E _ _ _ Wp Wq _ _ _ _ S v a ha
  obtain ⟨w, rfl⟩ := ha
  exact le_trans (Finset.le_sup (f := fun v => (w.1 v).length) (Finset.mem_univ v)) w.2.2

end Formalism.FourierDecayAlt.P.CutMP.En
end

