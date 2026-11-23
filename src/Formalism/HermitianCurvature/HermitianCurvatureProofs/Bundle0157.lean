module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0152
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.Bundle0003
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0041
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
public import Formalism.FormalDegreeBessel.Bundle0002

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section gcut

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem gcut_ckOn_smul {m : ℕ∞} {a : B.Mat k r → ℂ} (ha : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.CkOn m (B.GV k r) F) :
    B.CkOn m (B.GV k r) (fun g => a g • F g) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hF g₀ hg₀
  refine ⟨U, fun g => a g • f' g, hU, hgU,
    ((ha.of_le (by exact_mod_cast le_top)).contDiffOn).smul hc, fun g hg hG => ?_⟩
  simp only [hff g hg hG]

theorem gcut_sum_const {X : Type*} (c : ℕ) (l : List X) :
    (((l.map (fun _ => c)).sum : ℕ) : ℝ) = (c : ℝ) * l.length := by
  have h : ∀ l : List X, (l.map (fun _ => c)).sum = c * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring
  rw [h]; push_cast; ring

theorem gcut_leib {a : B.Mat k r → ℂ} (ha : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a) (c n : ℕ) (Ca : ℝ)
    (hWB : PI.UnitaryCorollaryDerivatives.WB (fun _ => c) a n Ca 0)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV k r) F) {A Bg : ℝ} (hc : (c : ℝ) ≤ Bg)
    (hFg : ∀ m : ℕ, B.InCC (A - Bg * m) m F) :
    B.InCC (A - Bg * n) n (fun g => a g • F g) := by
  choose cF hcF using hFg
  set K : ℝ := ∑ j ∈ Finset.range (n + 1), |cF j| with hK
  have hKj : ∀ j ≤ n, |cF j| ≤ K := fun j hj =>
    Finset.single_le_sum (f := fun j => |cF j|) (fun i _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hBg : 0 ≤ Bg := le_trans (Nat.cast_nonneg c) hc
  refine ⟨2 ^ n * (|Ca| * K), gcut_ckOn_smul ha (sCkOn_mono le_top hF), fun u v hu hv hl g hg => ?_⟩
  set L : ℂ →L[ℂ] ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) with hL
  set a' : B.Mat k r → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) := fun h => L (a h) with ha'
  have hfun : (fun g => a g • F g) = ap a' F := by funext h; simp [ap, ha', hL]
  have hlie := lie_LR (unit_lie hu) (unit_lie hv)
  have hca : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a' := (L.restrictScalars ℝ).contDiff.comp ha
  have hP : Pr (∅ : Set (B.Mat k r)) (B.GV k r) ((wL u ++ wR v).length : ℕ) a' F :=
    ⟨PI.UnitaryCorollaryDerivatives.ckOn_of_contDiff hca, sCkOn_mono le_top hF, fun _ _ h => absurd h (Set.notMem_empty _)⟩
  have hp := gN_pos hg
  have hg1 := gN_ge_one hg
  have hLn : ∀ x : ℂ, ‖L x‖ ≤ ‖x‖ := by
    intro x
    have : L x = x • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) := by simp [hL]
    rw [this, norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_id_le)
  have hw : (wL u ++ wR v).length = u.length + v.length := len_LR u v
  have hb := leib_bound isOpen_empty (fun g hg => Or.inr hg) g hg
    (|Ca| * K * B.gN g ^ (Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A)) (wL u ++ wR v) a' F hlie hP (by
      intro w₁ w₂ hs₁ hs₂ hl₁₂
      obtain ⟨u₁, v₁, hu₁, hv₁, rfl⟩ := sub_LR hs₁
      obtain ⟨u₂, v₂, hu₂, hv₂, rfl⟩ := sub_LR hs₂
      rw [len_LR, len_LR] at hl₁₂
      have hl₁ : u₁.length + v₁.length ≤ n := by
        have := hu₁.length_le; have := hv₁.length_le; omega
      have hl₂ : u₂.length + v₂.length ≤ n := by
        have := hu₂.length_le; have := hv₂.length_le; omega
      have hu₁' : ∀ X ∈ u₁, B.unitLie k r X := fun X hX => hu X (hu₁.subset hX)
      have hv₁' : ∀ X ∈ v₁, B.unitLie k r X := fun X hX => hv X (hv₁.subset hX)
      have hu₂' : ∀ X ∈ u₂, B.unitLie k r X := fun X hX => hu X (hu₂.subset hX)
      have hv₂' : ∀ X ∈ v₂, B.unitLie k r X := fun X hX => hv X (hv₂.subset hX)
      have ea : Dw (wL u₁ ++ wR v₁) a' g = L (Dw (wL u₁ ++ wR v₁) a g) :=
        PI.UnitaryCorollaryDerivatives.Dw_clm L _ (lie_LR (unit_lie hu₁') (unit_lie hv₁'))
          (PI.UnitaryCorollaryDerivatives.ckOn_of_contDiff ha) g hg
      set L₁ : ℝ := ((u₁.length + v₁.length : ℕ) : ℝ) with hL₁
      set L₂ : ℝ := ((u₂.length + v₂.length : ℕ) : ℝ) with hL₂
      have b1 : ‖Dw (wL u₁ ++ wR v₁) a' g‖ ≤ |Ca| * B.gN g ^ (Bg * L₁) := by
        rw [ea]
        refine (hLn _).trans ?_
        rw [← dLR_eq]
        have h1 := hWB u₁ v₁ hu₁' hv₁' hl₁ g hg
        rw [gcut_sum_const, List.length_append, zero_add] at h1
        have h1' : ‖B.dLR u₁ v₁ a g‖ ≤ Ca * B.gN g ^ ((c : ℝ) * L₁) := by
          rw [hL₁]; exact h1
        have h2 : B.gN g ^ ((c : ℝ) * L₁) ≤ B.gN g ^ (Bg * L₁) :=
          Real.rpow_le_rpow_of_exponent_le hg1 (mul_le_mul_of_nonneg_right hc (by rw [hL₁]; positivity))
        calc _ ≤ Ca * B.gN g ^ ((c : ℝ) * L₁) := h1'
          _ ≤ |Ca| * B.gN g ^ ((c : ℝ) * L₁) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hp.le _)
          _ ≤ |Ca| * B.gN g ^ (Bg * L₁) :=
            mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      have b2 : ‖Dw (wL u₂ ++ wR v₂) F g‖ ≤ K * B.gN g ^ (Bg * L₂ - A) := by
        rw [← dLR_eq]
        have h1 := (hcF (u₂.length + v₂.length)).2 u₂ v₂ hu₂' hv₂' le_rfl g hg
        have e : B.gN g ^ (Bg * L₂ - A) * B.gN g ^ (A - Bg * L₂) = 1 := by
          rw [← Real.rpow_add hp]; simp
        have h4 : ‖B.dLR u₂ v₂ F g‖ = B.gN g ^ (Bg * L₂ - A) * (B.gN g ^ (A - Bg * L₂) * ‖B.dLR u₂ v₂ F g‖) := by
          rw [← mul_assoc, e, one_mul]
        rw [h4]
        have h5 : B.gN g ^ (A - Bg * L₂) * ‖B.dLR u₂ v₂ F g‖ ≤ K := by
          refine le_trans ?_ (hKj _ hl₂)
          refine le_trans ?_ (le_abs_self _)
          simpa [hL₂] using h1
        calc _ ≤ B.gN g ^ (Bg * L₂ - A) * K := mul_le_mul_of_nonneg_left h5 (Real.rpow_nonneg hp.le _)
          _ = K * B.gN g ^ (Bg * L₂ - A) := mul_comm _ _
      have hsum : Bg * L₁ + (Bg * L₂ - A) = Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A := by
        rw [← hl₁₂, hL₁, hL₂]; push_cast; ring
      calc ‖Dw (wL u₁ ++ wR v₁) a' g‖ * ‖Dw (wL u₂ ++ wR v₂) F g‖
          ≤ (|Ca| * B.gN g ^ (Bg * L₁)) * (K * B.gN g ^ (Bg * L₂ - A)) :=
            mul_le_mul b1 b2 (norm_nonneg _) (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hp.le _))
        _ = |Ca| * K * (B.gN g ^ (Bg * L₁) * B.gN g ^ (Bg * L₂ - A)) := by ring
        _ = |Ca| * K * B.gN g ^ (Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A) := by
            rw [← Real.rpow_add hp, hsum])
  rw [hfun, dLR_eq]
  have hlen : ((wL u ++ wR v).length : ℕ) ≤ n := by rw [hw]; exact hl
  have e2 : B.gN g ^ (A - Bg * n) * B.gN g ^ (Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A) ≤ 1 := by
    rw [← Real.rpow_add hp]
    refine Real.rpow_le_one_of_one_le_of_nonpos hg1 ?_
    have : (((wL u ++ wR v).length : ℕ) : ℝ) ≤ n := by exact_mod_cast hlen
    nlinarith
  have e3 : (2 : ℝ) ^ (wL u ++ wR v).length ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hlen
  have hCK : 0 ≤ |Ca| * K := mul_nonneg (abs_nonneg _) hK0
  calc B.gN g ^ (A - Bg * n) * ‖Dw (wL u ++ wR v) (ap a' F) g‖
      ≤ B.gN g ^ (A - Bg * n) * (2 ^ (wL u ++ wR v).length *
          (|Ca| * K * B.gN g ^ (Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A))) :=
        mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hp.le _)
    _ = 2 ^ (wL u ++ wR v).length * (|Ca| * K) *
          (B.gN g ^ (A - Bg * n) * B.gN g ^ (Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A)) := by ring
    _ ≤ 2 ^ (wL u ++ wR v).length * (|Ca| * K) * 1 :=
        mul_le_mul_of_nonneg_left e2 (mul_nonneg (by positivity) hCK)
    _ ≤ 2 ^ n * (|Ca| * K) := by rw [mul_one]; exact mul_le_mul_of_nonneg_right e3 hCK

theorem gcut_graded (z z' : Fin (2 * r + k + 1) → ℂ) (h : ℝ → ℝ) (ε : ℝ) (hh : U.IsCutG ε h) {A Bg : ℝ}
    (hBg : 2 * ((r : ℝ) + 1) ≤ Bg) {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV k r) F)
    (hFg : ∀ m : ℕ, B.InCC (A - Bg * m) m F) :
    B.CkOn ⊤ (B.GV k r) (fun g => ((h (Gf k r z z' g) : ℝ) : ℂ) • F g) ∧
      ∀ m : ℕ, B.InCC (A - Bg * m) m (fun g => ((h (Gf k r z z' g) : ℝ) : ℂ) • F g) := by
  have hW := PI.UnitaryCorollaryDerivatives.gfWB_of PI.UnitaryCorollaryDerivatives.generating_function_polynomial PI.UnitaryCorollaryDerivatives.polynomial_bound PI.UnitaryCorollaryDerivatives.compact_region_estimate
  have hcd := (hW k r z z' h ε 0 hh).1
  refine ⟨gcut_ckOn_smul hcd hF, fun m => ?_⟩
  obtain ⟨C, hC⟩ := (hW k r z z' h ε m hh).2
  exact gcut_leib hcd (2 * (r + 1)) m C hC hF (by push_cast; linarith) hFg

end gcut

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomUBLTools
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords
open scoped ContDiff Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section tools

variable {k r : ℕ}

theorem ckOn_of_cd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : Mat k r → E} (hf : ContDiff ℝ ∞ f)
    (m : ℕ∞) (UU : Set (Mat k r)) : CkOn m UU f := by
  intro g₀ _
  exact ⟨Set.univ, f, isOpen_univ, Set.mem_univ _,
    (hf.of_le (WithTop.coe_le_coe.2 le_top)).contDiffOn, fun _ _ _ => rfl⟩

theorem lss_add {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set (Mat k r)}
    {f₁ f₂ : Mat k r → E} (hl₁ : LSS f₁ S) (hl₂ : LSS f₂ S) : LSS (fun g => f₁ g + f₂ g) S := by
  intro g hg
  obtain ⟨a, ha, V, hV, hgV, hae⟩ := hl₁ g hg
  obtain ⟨b, hb, W, hW, hgW, hbe⟩ := hl₂ g hg
  refine ⟨fun g => a g + b g, ha.add hb, V ∩ W, hV.inter hW, ⟨hgV, hgW⟩, fun g' hg' hm => ?_⟩
  show f₁ g' + f₂ g' = a g' + b g'
  rw [hae g' hg' hm.1, hbe g' hg' hm.2]

theorem ubl_add {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set (Mat k r)} (hSG : S ⊆ GV k r)
    {f₁ f₂ : Mat k r → E} {n e γ : ℕ} (h₁ : UBL f₁ S n e γ) (h₂ : UBL f₂ S n e γ) :
    UBL (fun g => f₁ g + f₂ g) S n e γ := by
  obtain ⟨⟨C₁, hC₁, hb₁⟩, hl₁⟩ := h₁
  obtain ⟨⟨C₂, hC₂, hb₂⟩, hl₂⟩ := h₂
  refine ⟨⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun w hw g hg => ?_⟩, lss_add hl₁ hl₂⟩
  obtain ⟨a, ha, V, hV, hgV, haa⟩ := hl₁ g hg
  obtain ⟨b, hb, W, hW, hgW, hbb⟩ := hl₂ g hg
  have hlie := admissible_word_mem_lie hw
  have hG := hSG hg
  have e0 : Dw w (fun g => f₁ g + f₂ g) g = Dw w (fun g => a g + b g) g :=
    Dw_congr_loc hlie (hV.inter hW) (fun g' hG' hg' => by simp [haa g' hG' hg'.1, hbb g' hG' hg'.2]) g hG
      ⟨hgV, hgW⟩
  rw [e0, Dw_add hlie (ckOn_of_cd ha _ _) (ckOn_of_cd hb _ _) g hG,
    ← Dw_congr_loc hlie hV haa g hG hgV, ← Dw_congr_loc hlie hW hbb g hG hgW]
  refine (norm_add_le _ _).trans ?_
  rw [add_mul]
  exact add_le_add (hb₁ w hw g hg) (hb₂ w hw g hg)

theorem ubl_sum {ι E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set (Mat k r)} (hSG : S ⊆ GV k r)
    (s : Finset ι) {f : ι → Mat k r → E} {n e γ : ℕ} (h : ∀ i ∈ s, UBL (f i) S n e γ) :
    UBL (fun g => ∑ i ∈ s, f i g) S n e γ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ubl_mono hSG (ubl_const (0 : E) hSG n γ) (Nat.zero_le e) le_rfl
  | @insert a s has ih =>
    simp only [Finset.sum_insert has]
    exact ubl_add hSG (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem lss_pi {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set (Mat k r)}
    {f : Mat k r → ι → E} (h : ∀ i, LSS (fun g => f g i) S) : LSS f S := by
  intro g hg
  choose F hF V hV hgV hFe using fun i => h i g hg
  refine ⟨fun g i => F i g, contDiff_pi.2 hF, ⋂ i, V i, isOpen_iInter_of_finite hV,
    Set.mem_iInter.2 hgV, fun g' hg' hm => funext fun i => hFe i g' hg' (Set.mem_iInter.1 hm i)⟩

theorem ubl_pi {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set (Mat k r)}
    (hSG : S ⊆ GV k r) {f : Mat k r → ι → E} {n e γ : ℕ} (h : ∀ i, UBL (fun g => f g i) S n e γ) :
    UBL f S n e γ := by
  have h1 := fun i => (h i).1
  have hL := fun i => (h i).2
  choose C hC hB using h1
  have hCs : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => hC i
  refine ⟨⟨∑ i, C i, hCs, fun w hw g hg => ?_⟩, lss_pi hL⟩
  have hlie := admissible_word_mem_lie hw
  have hgG := hSG hg
  have hgN : 0 ≤ gN g := Real.sqrt_nonneg _
  obtain ⟨F, hF, V, hV, hgV, hFe⟩ := lss_pi hL g hg
  rw [Dw_congr_loc hlie hV hFe g hgG hgV]
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hCs (pow_nonneg hgN _))).2 fun i => ?_
  rw [Formalism.FourierDecayAlt.P.Ux8.Dw_pi hlie (ckOn_of_cd hF _ _) g hgG i]
  have e1 := Dw_congr_loc hlie hV (f := fun g => f g i) (f₂ := fun g => F g i)
    (fun g' hg' hm => congrFun (hFe g' hg' hm) i) g hgG hgV
  rw [← e1]
  calc ‖Dw w (fun g => f g i) g‖ ≤ C i * gN g ^ (e + γ * w.length) := hB i w hw g hg
    _ ≤ (∑ j, C j) * gN g ^ (e + γ * w.length) :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))
          (pow_nonneg hgN _)

theorem ubl_star {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {f : Mat k r → ℂ} {n e γ : ℕ} (h : UBL f S n e γ) :
    UBL (fun g => star (f g)) S n e γ := by
  have hfun : (fun g => star (f g)) =
      fun g => (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap (f g) := by
    funext g; rfl
  rw [hfun]
  exact ubl_clm _ hSG h

theorem ubl_mmul {m : ℕ} {S : Set (Mat k r)} (hSG : S ⊆ GV k r)
    {A B : Mat k r → Matrix (Fin m) (Fin m) ℂ} {n ea eb γ : ℕ}
    (hA : ∀ i j, UBL (fun g => A g i j) S n ea γ) (hB : ∀ i j, UBL (fun g => B g i j) S n eb γ) (i j : Fin m) :
    UBL (fun g => (A g * B g) i j) S n (ea + eb) γ := by
  have hfun : (fun g => (A g * B g) i j) = fun g => ∑ l ∈ Finset.univ, A g i l * B g l j := by
    funext g; simp [Matrix.mul_apply]
  rw [hfun]
  exact ubl_sum hSG _ fun l _ => ubl_mul hSG (hA i l) (hB l j)

end tools

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutRegFF
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

def JfFF (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) : Prop :=
  ∀ v, B.JF (T v).base (f v) ∈
    Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)

end defs

def JfSmoothDS : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    JCT.IsBuiltPlace Cc S T f χ ν' m₀ top A₀ → JfFF S T f

def ModelPlaceBuilt3 : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    JCT.IsBuiltPlace Cc S T f χ ν' m₀ top A₀ → JfFF S T f → (∀ v, (S.G.place (S.pl v)).Ok) →
    Sz.IsWord S.G.k S.de → Sz.IsWord S.G.k S.de' → ∀ c : LE.Cut, c.χ = χ → ∀ v : Fin S.f,
      ∃ (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r)
        (j : M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT)
        (lam : Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1) → ℝ) (Cm σ : ℝ),
        JC.IsModelPlace S T f χ v L j lam c Cm σ

def RegFF3 : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ → JfFF S T f →
    ∀ v, B.JF (T v).base (f v) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) ∧ ∀ ε : ℝ, 0 < ε → B.JF (T v).base (D.cutF (T v).base χ (f v) ε) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)

section proofs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem gf_SgS (Bs : B.RealPlaceData k r Wp Wq) {s s' : Q.Mx k r} (hs : s ∈ Sset k r Bs.z) (hs' : s' ∈ Sset k r Bs.z')
    (g : Q.Mx k r) : Gf k r Bs.z Bs.z' (s * g * s') = Gf k r Bs.z Bs.z' g := by
  unfold Gf
  rw [dInv k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem s hs s' hs' g,
    dInv k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem s hs s' hs' g]

theorem one_mem_Sset (z : Fin (2 * r + k + 1) → ℂ) : (1 : Q.Mx k r) ∈ Sset k r z :=
  ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r z, 1, (nSubgroup k r).1, by simp⟩

theorem n_mem_Sset (z : Fin (2 * r + k + 1) → ℂ) {n : Q.Mx k r} (hn : n ∈ Q.Nlev k r 0) : n ∈ Sset k r z :=
  ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r z, n, hn.1, by simp⟩

theorem h_mem_Sset (z : Fin (2 * r + k + 1) → ℂ) {h : Q.Mx k r} (hh : h ∈ UWset k r z) : h ∈ Sset k r z :=
  ⟨h, hh, 1, (nSubgroup k r).1, by simp⟩

theorem cut_mem_FFl (Bs : B.RealPlaceData k r Wp Wq) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (ε : ℝ)
    {Dm : Set (Q.Mx k r)} {J : Q.Mx k r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ Q.FFl k r Bs.z Bs.z' Bs.π Bs.π' 0 Dm) :
    (fun g => ((χ (Gf k r Bs.z Bs.z' g / ε) : ℝ) : ℂ) • J g) ∈ Q.FFl k r Bs.z Bs.z' Bs.π Bs.π' 0 Dm := by
  obtain ⟨hS, hL, hR, hU⟩ := hJ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hFJ⟩ := hS g₀ hg₀
    refine ⟨U, fun g => ((χ (Gf k r Bs.z Bs.z' g / ε) : ℝ) : ℂ) • F g, hU, hgU, ?_, ?_⟩
    · have hc : ContDiff ℝ (⊤ : ℕ∞) (fun g : Q.Mx k r => ((χ (Gf k r Bs.z Bs.z' g / ε) : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp (hχ.comp ((Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').div_const ε))
      exact hc.contDiffOn.smul hF
    · intro g hgU hgG
      simp only [hFJ g hgU hgG]
  · intro g hg n hn
    have e : Gf k r Bs.z Bs.z' (n * g) = Gf k r Bs.z Bs.z' g := by
      have := gf_SgS Bs (n_mem_Sset Bs.z hn) (one_mem_Sset Bs.z') g
      simpa using this
    simp only [e, hL g hg n hn]
    rw [smul_comm]
  · intro g hg n hn
    have e : Gf k r Bs.z Bs.z' (g * n) = Gf k r Bs.z Bs.z' g := by
      have := gf_SgS Bs (one_mem_Sset Bs.z) (n_mem_Sset Bs.z' hn) g
      simpa using this
    simp only [e, hR g hg n hn]
    rw [smul_comm]
  · intro g hg h hh h' hh'
    have e : Gf k r Bs.z Bs.z' (h * g * h') = Gf k r Bs.z Bs.z' g :=
      gf_SgS Bs (h_mem_Sset Bs.z hh) (h_mem_Sset Bs.z' hh') g
    simp only [e, hU g hg h hh h' hh']
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

end proofs

theorem regularity_smooth_forms_holds : RegFF3 := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB hJ v
  refine ⟨hJ v, fun ε _ => ?_⟩
  have hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := hB.1.2.2.2.1.1.1
  have e : B.JF (T v).base (D.cutF (T v).base χ (f v) ε) =
      fun g => ((χ (Gf S.G.k S.G.r (T v).base.z (T v).base.z' g / ε) : ℝ) : ℂ) • B.JF (T v).base (f v) g :=
    funext fun g => Formalism.FourierDecayAlt.P.JCTx2.JF_cutF (T v).base χ (f v) ε g
  rw [e]
  exact cut_mem_FFl (T v).base hχ ε (hJ v)

section bridge

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem isBuiltPlace_mono3 {Cc₁ Cc₂ : ℝ} (h : Cc₁ ≤ Cc₂) {S : C.HidaSetting E Wp Wq}
    {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ}
    {ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ} {m₀ : Fin S.f → B.Mat S.G.k S.G.r}
    {top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ}
    {A₀ : ℝ} (hB : JCT.IsBuiltPlace Cc₂ S T f χ ν' m₀ top A₀) : JCT.IsBuiltPlace Cc₁ S T f χ ν' m₀ top A₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hB
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_, le_trans h h9, h10, h11, ?_, h13⟩
  · intro v
    have hv := h8 v
    have hX : 0 ≤ (S.G.k : ℝ) * S.Ntop * ((S.G.r : ℝ) + 1) ^ 2 + (S.Ntop : ℝ) ^ 2 * ((S.G.r : ℝ) + 1) ^ 2 +
        (S.Ntop : ℝ) ^ 3 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h hX]
  · have hX : 0 ≤ ((S.G.r : ℝ) + 1) ^ 4 *
        ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) := by positivity
    have := mul_le_mul_of_nonneg_right h hX
    nlinarith

end bridge

theorem modelPlaceBuilt2_of_3 (hJ : JfSmoothDS) (h3 : ModelPlaceBuilt3) : JCT.ModelPlaceBuilt2 := by
  obtain ⟨C₁, hC₁⟩ := hJ
  obtain ⟨C₂, hC₂⟩ := h3
  refine ⟨max C₁ C₂, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB
  exact hC₂ E Wp Wq S T f χ ν' m₀ top A₀ (isBuiltPlace_mono3 (le_max_right _ _) hB)
    (hC₁ E Wp Wq S T f χ ν' m₀ top A₀ (isBuiltPlace_mono3 (le_max_left _ _) hB))

end

end Formalism.FourierDecayAlt.P.CutMP
end

