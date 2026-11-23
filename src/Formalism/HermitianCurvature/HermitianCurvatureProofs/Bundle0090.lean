module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0054
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0086
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.StatementJF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0037
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0032
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0040
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0028
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0031
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0033
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0026
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenAdelicUnipotentTimesIntegralOutsideSet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RttUpperRelationsFromDescent
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0061
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0034
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QxChain
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0043
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0064
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0072
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterlaceSignTwo
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0085
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralFormulaPassesToLimits
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P

theorem integral_formula_passes_to_limits : Formalism.FourierDecayAlt.KB.LimitInt := by
  intro E _ _ _ Wp Wq _ _ _ _ S RR hg1 hg2 hU hconv hInt hB
  have hbd : ∀ v ε, 0 < ε → ∀ i, 1 ≤ i → i ≤ S.G.r + 1 → ∀ a, D.AdmAt S v a → ∀ h h',
      D.ptSize h = i - 1 → D.ptSize h' = i - 1 → ∃ M : ℝ, ∀ n, ∀ c : ℂ, c ≠ 0 →
        ‖(KB.withRR S (RR n)).gramLoc v ε i a (h ++ [(1, c)]) (h' ++ [(1, c)])‖ ≤ M * ((1 + ‖c‖) ^ 3)⁻¹ := by
    intro v ε hε i hi1 hi2 a ha h h' hh hh'
    obtain ⟨M, hM⟩ := hB v ε hε i hi1 hi2 a ha h h' hh hh'
    exact ⟨M, fun n => (hM n).1⟩
  refine ⟨PBB.K8.intAll_limit S RR hg1 hg2 hconv hInt hB, ?_⟩
  intro X hX ε hε i hi1 hi2 w hw hcnt
  set B := S.base.Wb (S.base.cnt w + C.Kst) with hBdef
  have hθ : ∀ n, ∃ θ : Finset (Fin S.f) → S.W → ℝ, (∀ A, TB.IsProb B (θ A)) ∧
      ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = i - 1) → ∀ κ, TB.PSDOn Y κ →
        ∀ l ∈ S.base.Lad i, l ≠ 0 → ∀ A : Finset (Fin S.f),
          (∏ v ∈ A, S.base.av v l ^ C.Kst) * ‖(KB.withRR S (RR n)).Nhat ε i w.1 Y κ l‖ ≤
            (∏ v ∈ A, X i v ^ C.Kst) *
              ∑ w' ∈ B, θ A w' * (KB.withRR S (RR n)).base.N0 ε (i - 1) w' Y κ :=
    fun n => hX n ε hε i hi1 hi2 w hw hcnt
  choose θ hprob hineq using hθ

  let F : ℕ → (Finset (Fin S.f) → B → ℝ) := fun n A x => θ n A x.1
  have hFb : ∀ n, F n ∈ Metric.closedBall (0 : Finset (Fin S.f) → B → ℝ) 1 := by
    intro n
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro A
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro x
    have h0 := (hprob n A).1 x.1
    show ‖θ n A x.1‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    calc θ n A x.1 ≤ ∑ w' ∈ B, θ n A w' :=
          Finset.single_le_sum (fun w' _ => (hprob n A).1 w') x.2
      _ = 1 := (hprob n A).2.2
  obtain ⟨a, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hFb
  have hco : ∀ A (x : B), Filter.Tendsto (fun n => θ (φ n) A x.1) Filter.atTop (nhds (a A x)) := by
    intro A x
    exact ((continuous_apply x).comp (continuous_apply A)).tendsto a |>.comp hlim
  let θ' : Finset (Fin S.f) → S.W → ℝ := fun A w' => if h : w' ∈ B then a A ⟨w', h⟩ else 0
  have hθ' : ∀ A w' (h : w' ∈ B), θ' A w' = a A ⟨w', h⟩ := fun A w' h => dif_pos h
  refine ⟨θ', ?_, ?_⟩
  · intro A
    refine ⟨?_, ?_, ?_⟩
    · intro w'
      by_cases h : w' ∈ B
      · rw [hθ' A w' h]
        exact ge_of_tendsto' (hco A ⟨w', h⟩) fun n => (hprob (φ n) A).1 w'
      · show 0 ≤ (if h : w' ∈ B then a A ⟨w', h⟩ else 0)
        rw [dite_eq_right h]
    · intro w' h
      show (if h : w' ∈ B then a A ⟨w', h⟩ else 0) = 0
      rw [dite_eq_right h]
    · have e1 : ∑ w' ∈ B, θ' A w' = ∑ x : B, a A x := by
        rw [← Finset.sum_coe_sort B]
        exact Finset.sum_congr rfl fun x _ => hθ' A x.1 x.2
      have e2 : ∀ n, ∑ x : B, θ (φ n) A x.1 = 1 := fun n => by
        rw [Finset.sum_coe_sort B (θ (φ n) A)]
        exact (hprob (φ n) A).2.2
      rw [e1]
      refine tendsto_nhds_unique (tendsto_finsetSum _ fun x _ => hco A x) ?_
      simp_rw [e2]
      exact tendsto_const_nhds
  · intro Y hY κ hκ l hl hl0 A
    have hL : Filter.Tendsto (fun n => (∏ v ∈ A, S.base.av v l ^ C.Kst) *
        ‖(KB.withRR S (RR (φ n))).Nhat ε i w.1 Y κ l‖) Filter.atTop
        (nhds ((∏ v ∈ A, S.base.av v l ^ C.Kst) * ‖S.Nhat ε i w.1 Y κ l‖)) :=
      (((PBB.tendsto_Nhat S RR hconv hInt hbd ε hε i hi1 hi2 w Y hY κ l).comp
        hφ.tendsto_atTop).norm).const_mul _
    have hR : Filter.Tendsto (fun n => (∏ v ∈ A, X i v ^ C.Kst) *
        ∑ w' ∈ B, θ (φ n) A w' * (KB.withRR S (RR (φ n))).base.N0 ε (i - 1) w' Y κ) Filter.atTop
        (nhds ((∏ v ∈ A, X i v ^ C.Kst) * ∑ w' ∈ B, θ' A w' * S.base.N0 ε (i - 1) w' Y κ)) := by
      refine Filter.Tendsto.const_mul _ (tendsto_finsetSum _ fun w' hw' => ?_)
      refine Filter.Tendsto.mul ?_ ((PBB.tendsto_base_norm_of_regularization S RR hconv ε hε (i - 1) (by omega) w' Y κ).comp
        hφ.tendsto_atTop)
      rw [hθ' A w' hw']
      exact hco A ⟨w', hw'⟩
    exact le_of_tendsto_of_tendsto' hL hR fun n => hineq (φ n) Y hY κ hκ l hl hl0 A

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
section
namespace Formalism.FourierDecayAlt.P

theorem jacquet_derivative_formula : Formalism.FourierDecayAlt.JF.JWords :=
  bessel_words_of_domain bessel_integral_domain

theorem jacquet_smooth_coordinates : Formalism.FourierDecayAlt.JF.JqSmooth :=
  bessel_smooth_of_parts jacquet_derivative_formula big_cell_domain

theorem casimir_under_jacquet_integral : Formalism.FourierDecayAlt.JF.CVUnderInt :=
  capelli_under_integral_of_parts jacquet_derivative_formula capelli_word_sum rewrite_rho_action

theorem right_transfer_upper_levels : Formalism.FourierDecayAlt.Q.RTTUpper :=
  rtt_upper_relations_from_descent chain_descent_relation resSurj_statement capelli_commutation operator_preserves_fusion_forms
    transfer_triples rtt_sandwich rtt_independence leading_term_alt transfer_linear_local

theorem right_transfer_all_levels : Formalism.FourierDecayAlt.Q.RTTLevel :=
  rtt_level_from_upper right_transfer_upper_levels level_transfer level_group_image flag_frame_transfer
    transfer_linear_local

namespace JacquetIntegral

theorem detCore : Formalism.FourierDecayAlt.Q.DetAt fun P => Fin.last P.r :=
  determinant_capelli_from_descent right_transfer_all_levels quantum_determinant_from_rtt determinant_hat right_type_action
    left_type_action operator_preserves_fusion_forms transfer_linear_local

end JacquetIntegral

theorem actual_operators_exist : Formalism.FourierDecayAlt.Q.ActualOpsExist :=
  actual_operators_from_parts operator_preserves_fusion_forms transfer_linear_local transfer_joint_smooth radial_operators

theorem actual_adjointness : Formalism.FourierDecayAlt.Q.ActualAdjoint :=
  actual_adjointness_from_hermitian hermitian_haar_invariance

theorem actual_start : Formalism.FourierDecayAlt.Q.ActualStart :=
  actual_start_from_level_starts right_transfer_all_levels JacquetIntegral.detCore transfer_linear_local

namespace JacquetIntegral

theorem normalFormActual_of_fromModule (h : Formalism.FourierDecayAlt.Q.NormalFormFromModule) : Formalism.FourierDecayAlt.Q.NormalFormActual :=
  h actual_start zeta_commutes leading_term_alt spectral_two_by_two actual_operators_exist

theorem levelStartActual_of_normalForm (h : Formalism.FourierDecayAlt.Q.NormalFormActual) : Formalism.FourierDecayAlt.Q.LevelStartActual :=
  level_start_from_normal_form h actual_start model_is_normal_form interlace_sign_two

theorem levelStartActual_of_fromModule (h : Formalism.FourierDecayAlt.Q.NormalFormFromModule) : Formalism.FourierDecayAlt.Q.LevelStartActual :=
  levelStartActual_of_normalForm (normalFormActual_of_fromModule h)

end JacquetIntegral

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenBigCellSet
section
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.MinorPolynomials

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def V0 (D : RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) : Set (Mat k r) :=
  {x | 0 < Gf k r D.z D.z' x} ∩ ⋂ l ∈ L, {x | Dmin k r D.z D.z' x l ≠ 0}

lemma isOpen_big_cell_set (D : RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) : IsOpen (V0 D L) := by
  unfold V0
  refine (isOpen_lt continuous_const (Gf_cont D.z D.z')).inter ?_
  refine isOpen_biInter_finset (fun l _ => ?_)
  exact isOpen_ne_fun (Dmin_cont D.z D.z' l) continuous_const

lemma mem_domL (D : RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) (g : Mat k r) :
    g ∈ C6.domL D L ↔ g ∈ GV k r ∧ g ∈ V0 D L := by
  simp only [C6.domL, V0, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]

lemma domL_gpos {D : RealPlaceData k r Wp Wq} {L : Finset (Fin (r + 2))} {g : Mat k r} (hg : g ∈ C6.domL D L) :
    g ∈ GPos D := by
  exact ⟨hg.1, hg.2.1⟩

lemma nz_of_domL {D : RealPlaceData k r Wp Wq} {L : Finset (Fin (r + 2))} {g : Mat k r} (hg : g ∈ C6.domL D L)
    {nf : ℕ} {e : CT k r nf × List (Mat k r)} (he : Good L e) :
    (∀ l, (e.1.a l ≠ 0 ∨ e.1.b l ≠ 0) → Dmin k r D.z D.z' g l ≠ 0) ∧
      (e.1.c ≠ 0 → ((Gf k r D.z D.z' g : ℝ) : ℂ) ≠ 0) := by
  have hlast : Dmin k r D.z D.z' g (Fin.last (r + 1)) ≠ 0 := by
    intro h0
    have hG : 0 < Gf k r D.z D.z' g := hg.2.1
    simp only [Gf, h0, Complex.normSq_zero, zero_sub] at hG
    have := mul_nonneg (mul_pos D.T_pos D.T'_pos).le (Complex.normSq_nonneg (Dmin k r D.z D.z' g ⟨r, by omega⟩))
    linarith
  obtain ⟨hab, -, -⟩ := he
  refine ⟨fun l hl => ?_, fun _ => ?_⟩
  · rcases hab l hl with hl | rfl
    · exact hg.2.2 l hl
    · exact hlast
  · exact_mod_cast hg.2.1.ne'

lemma shape_flatMap' (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (F : Mat k r → (Wq →L[ℂ] Wp)) (Lf : FS k r nf) (f : CT k r nf × List (Mat k r) → FS k r nf) (g : Mat k r) :
    shape D fib F (Lf.flatMap f) g = (Lf.map fun e => shape D fib F (f e) g).sum := by
  induction Lf with
  | nil => simp [shape]
  | cons e Lf ih =>
    simp only [shape] at ih ⊢
    simp [ih, List.sum_append]

private lemma ckOn_rw_of_ckOn_add_length {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {UU : Set (Mat k r)}
    {f : Mat k r → E} : ∀ (w : List (Mat k r)) (n : ℕ∞), (∀ X ∈ w, inLie k r X) →
      CkOn (n + w.length) UU f → CkOn n UU (Rw w f) := by
  intro w
  induction w with
  | nil => intro n _ hf; simpa [Rw] using hf
  | cons X w ih =>
    intro n hw hf
    rw [Rw_cons']
    refine CkOn_Dx (x := (false, X)) (hw X (by simp)) (ih (n + 1) (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) ?_)
    have e : n + 1 + (w.length : ℕ∞) = n + ((X :: w).length : ℕ∞) := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring
    rw [e]; exact hf

private lemma hasDerivAt_shape_crv_of_good (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) (L : Finset (Fin (r + 2))) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn (m : ℕ∞) (GV k r) F) {X : Mat k r} (hX : inLie k r X) {g : Mat k r} (hg : g ∈ C6.domL D L) :
    ∀ Lf : FS k r nf, (∀ e ∈ Lf, Good L e) → (∀ e ∈ Lf, e.2.length + 1 ≤ m) →
      HasDerivAt (fun s => shape D fib F Lf (crv (false, X) g s)) (shape D fib F (step D X Lf) g) 0 := by
  intro Lf
  induction Lf with
  | nil =>
    intro _ _
    simp only [shape, step, List.map_nil, List.sum_nil, List.flatMap_nil]
    exact hasDerivAt_const _ _
  | cons e Lf ih =>
    intro hL hm
    have he : Good L e := hL e (by simp)
    have hgp := domL_gpos hg
    have hnz := nz_of_domL hg he
    have hcv := hasDerivAt_cv D fib hfib hX hgp e.1 hnz.1 hnz.2 he.2.1
    have hRw : CkOn 1 (GV k r) (Rw e.2 F) := by
      refine ckOn_rw_of_ckOn_add_length e.2 1 he.2.2 (sCkOn_mono ?_ hF)
      have := hm e (by simp)
      rw [add_comm]; exact_mod_cast this
    have hR : HasDerivAt (fun s => Rw e.2 F (crv (false, X) g s)) (Rw (X :: e.2) F g) 0 := by
      rw [Rw_cons']
      exact CkOn_diff (x := (false, X)) hX hRw hgp.1 hgp.1
    have hcv' := ((ContinuousLinearMap.restrictScalarsL ℂ (Wq →L[ℂ] Wp) (Wq →L[ℂ] Wp) ℝ ℝ).hasFDerivAt).comp_hasDerivAt
      (0 : ℝ) hcv
    have h1 := hcv'.clm_apply hR
    have h2 := ih (fun e' he' => hL e' (List.mem_cons_of_mem _ he')) (fun e' he' => hm e' (List.mem_cons_of_mem _ he'))
    have h3 := h1.add h2
    show HasDerivAt (fun s => cv D fib e.1 (crv (false, X) g s) (Rw e.2 F (crv (false, X) g s)) +
      shape D fib F Lf (crv (false, X) g s)) _ 0
    refine h3.congr_deriv ?_
    rw [crv_zero]
    have hs : shape D fib F (step D X (e :: Lf)) g =
        shape D fib F (stepOne D X e) g + shape D fib F (step D X Lf) g := by
      simp only [step, shape_flatMap', List.map_cons, List.sum_cons]
    rw [hs]
    congr 1
    simp only [shape, stepOne, List.map_append, List.map_map, List.sum_append, Function.comp_def, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [← list_sum_apply, crv_zero]
    try rfl

theorem step_eq (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) (L : Finset (Fin (r + 2))) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn (m : ℕ∞) (GV k r) F) {X : Mat k r} (hX : inLie k r X) {Lf : FS k r nf}
    (hL : ∀ e ∈ Lf, Good L e) (hm : ∀ e ∈ Lf, e.2.length + 1 ≤ m) {g : Mat k r} (hg : g ∈ C6.domL D L) :
    RdV X (shape D fib F Lf) g = shape D fib F (step D X Lf) g := by
  have hd := hasDerivAt_shape_crv_of_good D fib hfib L hF hX hg Lf hL hm
  rw [← hd.deriv]
  exact Dx_eq (false, X) (shape D fib F Lf) g

theorem expand (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) (L : Finset (Fin (r + 2))) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn (m : ℕ∞) (GV k r) F) :
    ∀ (w : List (Mat k r)) (Lf : FS k r nf), (∀ X ∈ w, inLie k r X) → (∀ e ∈ Lf, Good L e) →
      (∀ e ∈ Lf, e.2.length + w.length ≤ m) → ∀ g ∈ C6.domL D L,
        Rw w (shape D fib F Lf) g = shape D fib F (steps D w Lf) g := by
  intro w
  induction w with
  | nil => intro Lf _ _ _ g _; rfl
  | cons X w ih =>
    intro Lf hw hL hm g hg
    have hX : inLie k r X := hw X (by simp)
    have hw' : ∀ Y ∈ w, inLie k r Y := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    have hm' : ∀ e ∈ Lf, e.2.length + w.length ≤ m := fun e he => by
      have := hm e he; simp only [List.length_cons] at this; omega
    have hev : (fun t : ℝ => Rw w (shape D fib F Lf) (crv (false, X) g t)) =ᶠ[𝓝 0]
        (fun t => shape D fib F (steps D w Lf) (crv (false, X) g t)) := by
      have hV : g ∈ V0 D L := ((mem_domL D L g).1 hg).2
      filter_upwards [crv_ev (x := (false, X)) (isOpen_big_cell_set D L) hV] with t ht
      exact ih Lf hw' hL hm' _ ((mem_domL D L _).2 ⟨crv_mem (x := (false, X)) hX hg.1 t, ht⟩)
    have hgood := good_steps D w hw' Lf hL
    have hstep := step_eq D fib hfib L hF hX (Lf := steps D w Lf) (fun e he => (hgood e he).1)
      (fun e he => by
        obtain ⟨-, e0, he0, hle⟩ := hgood e he
        have := hm e0 he0
        simp only [List.length_cons] at this
        omega) hg
    calc Rw (X :: w) (shape D fib F Lf) g
        = deriv (fun t : ℝ => Rw w (shape D fib F Lf) (crv (false, X) g t)) 0 := by
          rw [Rw_cons']; exact Dx_eq (false, X) _ g
      _ = deriv (fun t : ℝ => shape D fib F (steps D w Lf) (crv (false, X) g t)) 0 := hev.deriv_eq
      _ = RdV X (shape D fib F (steps D w Lf)) g := (Dx_eq (false, X) _ g).symm
      _ = shape D fib F (steps D (X :: w) Lf) g := hstep

end Formalism.FourierDecayAlt.P.MinorPolynomials
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.L1QuotientIntegralBound
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem prod_ae {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) :
    ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  obtain ⟨hWs, -, hWc, -⟩ := hW
  obtain ⟨hNs, -, hNc, -⟩ := hN
  have := hWs; have := hNs
  rw [ae_iff]
  have hsub : {p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r |
      ¬ (Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r)} ⊆
      ({x | Matrix.of x ∉ Formalism.QuantumDeterminants.UWset k r z} ×ˢ Set.univ) ∪
        (Set.univ ×ˢ {x | Matrix.of x ∉ Formalism.QuantumDeterminants.Nset k r}) := by
    intro p hp
    by_cases h1 : Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z
    · exact Or.inr ⟨Set.mem_univ _, fun h2 => hp ⟨h1, h2⟩⟩
    · exact Or.inl ⟨h1, Set.mem_univ _⟩
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · rw [Measure.prod_prod, hWc, zero_mul]
  · rw [Measure.prod_prod, hNc, mul_zero]

theorem beInt_norm_le {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {σ : Mx k r → (H →L[ℂ] H)} (hds : PI.UpqRep.IsDSHpk k r ε lam σ)
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {x v : H} {g : Mx k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r}
    (hp : Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r) :
    ‖beInt z c π σ (σ g x) v p‖ ≤ ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * g) x⟫_ℂ‖ := by
  have hhn : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    DDSmoothness.uh_mul hp.1.1 hp.2.1
  have hσ : σ (Matrix.of p.1 * Matrix.of p.2 * g) x = σ (Matrix.of p.1 * Matrix.of p.2) (σ g x) := by
    rw [sigma_mul' hds hhn hg]; rfl
  have hi := (MatrixMultiplicationContinuity.uw_inv hp.1).1
  have hπn : ‖π (Matrix.of p.1)⁻¹‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      (fun w => by rw [MatrixMultiplicationContinuity.piW_unitary hT hπ _ hi w, one_mul])
  have hψ : ‖star (Formalism.QuantumDeterminants.psi k r z c (Matrix.of p.2))‖ = 1 := by
    rw [norm_star]; unfold Formalism.QuantumDeterminants.psi; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  unfold beInt
  rw [norm_smul, norm_mul, hψ, mul_one, hσ]
  exact mul_le_of_le_one_right (norm_nonneg _) hπn

theorem be_enorm_le {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp]
    {σ : Mx k r → (H →L[ℂ] H)} (hds : PI.UpqRep.IsDSHpk k r ε lam σ)
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    {x v : H} {g : Mx k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ‖be z c π σ μW μN (σ g x) v‖ₑ ≤
      ∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * g) x⟫_ℂ‖ₑ ∂(μW.prod μN) := by
  unfold be
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
  filter_upwards [prod_ae hW hN] with p hp
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (beInt_norm_le hds hT hπ hg hp)

theorem l1_quotient_integral_bound {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mx k r → (H →L[ℂ] H)} (hds : PI.UpqRep.IsDSHpk k r ε lam σ)
    {z : Fin (2 * r + k + 1) → ℂ} {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (hGm : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG)
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG (muSof μW μN) νq)
    {x v : H} {C a : ℝ}
    (hC : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖⟪v, σ y x⟫_ℂ‖ ≤ C * B.gN y ^ (-a))
    (hI : Integrable (fun y : Formalism.QuantumDeterminants.Mt k r => B.gN (Matrix.of y) ^ (-a)) μG) :
    ∫⁻ g, (∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ ∂(μW.prod μN)) ∂νq < ⊤ := by
  obtain ⟨e, he, hee⟩ := coef_ext hds v x
  set U : Set (Formalism.QuantumDeterminants.Mt k r) := {y | Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} with hU
  set f : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := U.indicator (fun y => ‖e (Matrix.of y)‖ₑ) with hf
  have hfm : Measurable f := by
    have hc : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => e (Matrix.of y)) :=
      he.comp (show Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) from continuous_id)
    have : Measurable (fun y : Formalism.QuantumDeterminants.Mt k r => ‖e (Matrix.of y)‖ₑ) := hc.measurable.enorm
    exact this.indicator uh_mem_measurableSet
  have hφ : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) := by
    have h1 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.1 : Mx k r)) := continuous_fst
    have h2 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.2 : Mx k r)) := continuous_snd
    exact h1.matrix_mul h2
  have hmul : ∀ g : Formalism.QuantumDeterminants.Mt k r, Measurable (fun s : Formalism.QuantumDeterminants.Mt k r =>
      f (fun i j => (Matrix.of s * Matrix.of g) i j)) := by
    intro g
    have : Continuous (fun s : Formalism.QuantumDeterminants.Mt k r =>
        (fun i j => (Matrix.of s * Matrix.of g) i j : Formalism.QuantumDeterminants.Mt k r)) := by
      have h1 : Continuous (fun s : Formalism.QuantumDeterminants.Mt k r => (Matrix.of s : Mx k r)) := continuous_id
      exact h1.matrix_mul continuous_const
    exact hfm.comp this.measurable
  have hfacts := DDSmoothness.muSof_facts hW hN
  have hae := DDSmoothness.ae_UH_of_quot hGm.2.2.1 hfacts.1 hfacts.2 hq

  have step1 : ∀ᵐ g ∂νq, (∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ ∂(μW.prod μN)) =
      ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of g) i j) ∂(muSof μW μN) := by
    filter_upwards [hae] with g hg
    unfold muSof
    rw [lintegral_map (hmul g) hφ.measurable]
    apply lintegral_congr_ae
    filter_upwards [prod_ae hW hN] with p hp
    have hhn : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hp.1.1 hp.2.1
    have hin : Matrix.of p.1 * Matrix.of p.2 * Matrix.of g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
      DDSmoothness.uh_mul hhn hg
    have key : (fun i j => (Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) *
        Matrix.of g) i j : Formalism.QuantumDeterminants.Mt k r) ∈ U := hin
    show ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ =
      f (fun i j => (Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) * Matrix.of g) i j)
    rw [hf, Set.indicator_of_mem key]
    show _ = ‖e (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g)‖ₑ
    rw [hee _ hin]
  rw [lintegral_congr_ae step1, ← hq f hfm]

  have hb : ∀ᵐ y ∂μG, f y ≤ ‖C * B.gN (Matrix.of y) ^ (-a)‖ₑ := by
    have hGc : ∀ᵐ y ∂μG, Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
      rw [ae_iff]; simpa using hGm.2.2.1
    filter_upwards [hGc] with y hy
    simp only [hf]
    rw [Set.indicator_of_mem (show y ∈ U from hy), hee _ hy, ← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((hC _ hy).trans (le_abs_self _) |>.trans (le_of_eq (Real.norm_eq_abs _).symm))
  calc ∫⁻ y, f y ∂μG ≤ ∫⁻ y, ‖C * B.gN (Matrix.of y) ^ (-a)‖ₑ ∂μG := lintegral_mono_ae hb
    _ < ⊤ := (hI.const_mul C).hasFiniteIntegral

end Formalism.FourierDecayAlt.P.S3dx4
end
end

