module

public import Formalism.HermitianCurvature.StatementJF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0031
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0032
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0040
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0043
public import Mathlib
public import Formalism.HermitianCurvature.StatementTop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InsCombineMk

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveOrbitOpen
section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PositiveOrbitOpen

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section local_

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rdV_local {f₁ f₂ : Mat k r → E} {V : Set (Mat k r)} (hV : IsOpen V)
    (h : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x) {X : Mat k r} (hX : inLie k r X) :
    ∀ x ∈ V, x ∈ GV k r → RdV X f₁ x = RdV X f₂ x := by
  intro x hx hxG
  have hγ := Formalism.FourierDecayAlt.P.B5.curve_hasDerivAt x X 0
  have hγ0 : x * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = x := by simp
  have hmem : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), x * NormedSpace.exp ((t : ℂ) • X) ∈ V :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hV.mem_nhds hx)
  show deriv (fun t : ℝ => f₁ (x * NormedSpace.exp ((t : ℂ) • X))) 0 =
    deriv (fun t : ℝ => f₂ (x * NormedSpace.exp ((t : ℂ) • X))) 0
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hmem] with t ht
  exact h _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hxG hX t)

theorem rw_local {f₁ f₂ : Mat k r → E} {V : Set (Mat k r)} (hV : IsOpen V)
    (h : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x) (w : List (Mat k r)) (hw : ∀ X ∈ w, inLie k r X) :
    ∀ x ∈ V, x ∈ GV k r → Rw w f₁ x = Rw w f₂ x := by
  induction w with
  | nil => exact h
  | cons X w ih =>
    intro x hx hxG
    exact rdV_local hV (ih (fun Y hY => hw Y (List.mem_cons_of_mem X hY))) (hw X (by simp)) x hx hxG

theorem rw_smul (w : List (Mat k r)) (c : ℂ) (f : Mat k r → E) : Rw w (c • f) = c • Rw w f := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    show RdV X (Rw w (c • f)) = c • RdV X (Rw w f)
    rw [ih]
    funext g
    simp only [RdV, Pi.smul_apply]
    exact deriv_const_smul_field (f := fun t : ℝ => Rw w f (g * NormedSpace.exp ((t : ℂ) • X))) c

end local_

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

omit [FiniteDimensional ℂ Wq] in
theorem zhat_cont (z z' : Fin (2 * r + k + 1) → ℂ) : Continuous (fun g : Mat k r => Zhat k r z z' g) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  unfold Zhat herm
  exact continuous_const.dotProduct (continuous_const.matrix_mulVec (continuous_id.matrix_mulVec continuous_const))

omit [FiniteDimensional ℂ Wq] in
theorem dmin_cont (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    Continuous (fun g : Mat k r => Dmin k r z z' g l) := by
  unfold Dmin
  exact ((zhat_cont z z').matrix_submatrix _ _).matrix_det

omit [FiniteDimensional ℂ Wq] in
theorem gf_cont (z z' : Fin (2 * r + k + 1) → ℂ) : Continuous (fun g : Mat k r => Gf k r z z' g) := by
  unfold Gf
  exact (Complex.continuous_normSq.comp (dmin_cont z z' _)).sub
    (continuous_const.mul (Complex.continuous_normSq.comp (dmin_cont z z' _)))

omit [FiniteDimensional ℂ Wq] in
theorem omPlus_open (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (Q.OmPlus k r z z') := by
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have h1 : ∀ᶠ x in 𝓝 g, ∀ l : Fin (r + 2), l.val ≤ r → Dmin k r z z' x l ≠ 0 := by
    refine Filter.eventually_all.2 fun l => ?_
    by_cases hl : l.val ≤ r
    · filter_upwards [(dmin_cont z z' l).continuousAt.eventually_ne (hg.1 l hl)] with x hx
      exact fun _ => hx
    · exact Filter.Eventually.of_forall fun x h => absurd h hl
  have h2 : ∀ᶠ x in 𝓝 g, 0 < Gf k r z z' x := continuousAt_const.eventually_lt (gf_cont z z').continuousAt hg.2
  filter_upwards [h1, h2] with x hx1 hx2
  exact ⟨hx1, hx2⟩

omit [FiniteDimensional ℂ Wq] in
theorem sgs_S (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) :
    (Matrix.of p.1.2 * Matrix.of p.1.1 : Mat k r)⁻¹ ∈ Sset k r D.z ∧
      (Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r) ∈ Sset k r D.z' := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  refine ⟨?_, ?_⟩
  · rw [Matrix.mul_inv_rev]
    exact ⟨_, BigCellInversePair.uw_inv h1, _, WeylGroupFacts.mem_n_inv h2, rfl⟩
  · exact (sGroup k r D.z' D.z'_mem).2.1 _ ⟨1, BigCellZetaMinors.one_uw _, _, h4, (Matrix.one_mul _).symm⟩ _
      ⟨_, h3, 1, WeylGroupFacts.mem_n_one, (Matrix.mul_one _).symm⟩

omit [FiniteDimensional ℂ Wq] in
theorem sgs_GV (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {y : Mat k r} (hy : y ∈ GV k r) :
    sgs p y ∈ GV k r := by
  rw [B5.sgs_eq]
  exact WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv (B5.inSS_left D hp)) hy) (B5.inSS_right D hp)

omit [FiniteDimensional ℂ Wq] in
theorem sgs_Om (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {y : Mat k r} (hy : y ∈ Om k r D.z D.z') :
    sgs p y ∈ Om k r D.z D.z' := by
  refine ⟨sgs_GV D hp hy.1, fun l hl => ?_, ?_⟩
  · rw [BigCellZetaMinors.dmin_sgs D hp]; exact hy.2.1 l hl
  · obtain ⟨hs, hs'⟩ := sgs_S D hp
    show 0 < Gf k r D.z D.z' (sgs p y)
    rw [B5.sgs_eq, gInv k r D.z D.z' D.z_mem D.z'_mem _ hs _ hs' y]
    exact hy.2.2


end Formalism.FourierDecayAlt.P.PositiveOrbitOpen

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothWordsAll
section
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.WeakDominationWordBounds

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.SandwichRhoAction Formalism.FourierDecayAlt.P.ChartIntegralLocal Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
  Formalism.FourierDecayAlt.P.LetterPairRecursion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]

section
variable (D : RealPlaceData k r Wp Wq) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)} (hFm : CkOn (m : ℕ∞) (GV k r) F)
    (hDom1 : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) → u.length + v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z',
        AEStronglyMeasurable (fun p => rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g) D.μSS)
    (hDom2 : ∀ K : Set (Mat k r), IsCompact K → K ⊆ Om k r D.z D.z' →
      ∃ b : SS k r → ℝ, Integrable b D.μSS ∧
        ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
          u.length + v.length ≤ m → ∀ g ∈ K, ∀ᵐ p ∂D.μSS,
            ‖rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g‖ ≤ b p)
include hFm hDom1 hDom2

lemma words_all :
    ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) → u.length + v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z', dLR u v (JF D F) g = ∫ p, xiP D p • dLR u v (rho D p F) g ∂D.μSS := by
  have base : ∀ v : List (Mat k r), (∀ X ∈ v, unitLie k r X) → v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z', dLR [] v (JF D F) g = ∫ p, xiP D p • dLR [] v (rho D p F) g ∂D.μSS := by
    intro v
    induction v with
    | nil => intro _ _ g _; rfl
    | cons X v ih =>
      intro hv hl
      have hv' : ∀ Y ∈ v, unitLie k r Y := fun Y hY => hv Y (List.mem_cons_of_mem _ hY)
      exact step_pair D hFm hDom1 hDom2 false (hv X List.mem_cons_self) (u := []) (v := v) (u2 := [])
        (v2 := X :: v) (by simp) hv' (by simp) hv (by simpa using hl) (by simp) (fun f => rfl)
        (ih hv' (by simp at hl; omega))
  intro u
  induction u with
  | nil => intro v _ hv hl; exact base v hv (by simpa using hl)
  | cons X u ih =>
    intro v hu hv hl
    have hu' : ∀ Y ∈ u, unitLie k r Y := fun Y hY => hu Y (List.mem_cons_of_mem _ hY)
    exact step_pair D hFm hDom1 hDom2 true (hu X List.mem_cons_self) (u := u) (v := v) (u2 := X :: u) (v2 := v)
      hu' hv hu hv hl (by simp) (fun f => rfl) (ih v hu' hv (by simp at hl; omega))

lemma ck_all : Formalism.FourierDecayAlt.Q.CkLev k r 0 m (Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z') (JF D F) := by
  classical
  haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  intro g0 hg0
  have hg0G : g0 ∈ GV k r := hg0.1.1
  have hchart0 : Formalism.FourierDecayAlt.P.Ux10.chart g0 0 = g0 := by
    have h1 : (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) = Formalism.FourierDecayAlt.P.Ux10.co 0 :=
      funext fun i => (Formalism.FourierDecayAlt.P.Ux10.co_zero i).symm
    unfold Formalism.FourierDecayAlt.P.Ux10.chart Formalism.FourierDecayAlt.P.Ux10.kap
    rw [h1, Formalism.FourierDecayAlt.P.Ux10.Mv_co, Formalism.FourierDecayAlt.P.Ux10.prj_zero]
    simp
  have hcont : ContinuousAt (Formalism.FourierDecayAlt.P.Ux10.chart g0) 0 :=
    (Formalism.FourierDecayAlt.P.Ux10.chart_diff g0 Formalism.FourierDecayAlt.P.Ux10.zero_mem_dom).continuousAt
  have hV : Formalism.FourierDecayAlt.P.Ux10.Dom k r ∩ Formalism.FourierDecayAlt.P.Ux10.chart g0 ⁻¹' Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' ∈
      𝓝 (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) :=
    Filter.inter_mem (Formalism.FourierDecayAlt.P.Ux10.dom_open.mem_nhds Formalism.FourierDecayAlt.P.Ux10.zero_mem_dom)
      (hcont.preimage_mem_nhds ((isOpen_OmPlus _ _).mem_nhds (by rw [hchart0]; exact hg0.2)))
  obtain ⟨δ1, hδ1, hsub⟩ := Metric.mem_nhds_iff.1 hV
  set δ := δ1 / 2 with hδ
  have hδp : 0 < δ := by rw [hδ]; linarith
  have hclb : Metric.closedBall (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) δ ⊆ Metric.ball 0 δ1 :=
    Metric.closedBall_subset_ball (by rw [hδ]; linarith)
  have hcl : Metric.closedBall (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) δ ⊆ Formalism.FourierDecayAlt.P.Ux10.Dom k r :=
    fun Y hY => (hsub (hclb hY)).1
  set K := Formalism.FourierDecayAlt.P.Ux10.chart g0 '' Metric.closedBall (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) δ with hKdef
  have hK : IsCompact K :=
    (isCompact_closedBall _ _).image_of_continuousOn ((Formalism.FourierDecayAlt.P.Ux10.chart_cd g0).continuousOn.mono hcl)
  have hKOm : K ⊆ Om k r D.z D.z' := by
    rintro _ ⟨Y, hY, rfl⟩
    exact (⟨Formalism.FourierDecayAlt.P.Ux10.chart_mem hg0G (hcl hY), (hsub (hclb hY)).2⟩ :
      Formalism.FourierDecayAlt.P.Ux10.chart g0 Y ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z')
  have hKG : K ⊆ GV k r := fun x hx => (show x ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' from hKOm hx).1
  have hmemK : ∀ Y ∈ Metric.ball (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) δ, Formalism.FourierDecayAlt.P.Ux10.chart g0 Y ∈ K :=
    fun Y hY => ⟨Y, Metric.ball_subset_closedBall hY, rfl⟩
  obtain ⟨bd, hbdI, hbd⟩ := hDom2 K hK hKOm
  set WS : Set (List (Mat k r) × List (Mat k r)) :=
    (fun w : List (Formalism.FourierDecayAlt.P.Ux10.J k r) => (w.map Formalism.FourierDecayAlt.P.Ux10.Lt, ([] : List (Mat k r)))) ''
      {w | w.length ≤ m} with hWSdef
  have hWS : WS.Countable := (Set.to_countable _).image _
  have hunit : ∀ w : List (Formalism.FourierDecayAlt.P.Ux10.J k r), ∀ X ∈ w.map Formalism.FourierDecayAlt.P.Ux10.Lt, unitLie k r X := by
    intro w X hX
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hX
    exact Formalism.FourierDecayAlt.P.Ux10.Lt_unit i
  have hWSl : ∀ uv ∈ WS, (∀ Y ∈ uv.1, unitLie k r Y) ∧ (∀ Y ∈ uv.2, unitLie k r Y) ∧
      uv.1.length + uv.2.length ≤ m := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨hunit w, by simp, by simpa using hw⟩
  have good := good_set D hFm hK hKG hWS hWSl bd fun uv huv g' hg' =>
    hbd uv.1 uv.2 (hWSl uv huv).1 (hWSl uv huv).2.1 (hWSl uv huv).2.2 g' hg'
  set P0 : Set (SS k r) := {p | D.inSS p ∧ ∀ uv ∈ WS, ∀ g' ∈ K, ‖dLR uv.1 uv.2 (rho D p F) g'‖ ≤ bd p} with hP0
  have goodae : ∀ᵐ p ∂D.μSS, p ∈ P0 := good
  set hK' : SS k r → Mat k r → (Wq →L[ℂ] Wp) := fun p => if p ∈ P0 then rho D p F else fun _ => 0 with hK'def
  have hsel : ∀ p (u' v' : List (Mat k r)),
      dLR u' v' (hK' p) = if p ∈ P0 then dLR u' v' (rho D p F) else fun _ => 0 := by
    intro p u' v'
    by_cases hp : p ∈ P0
    · simp only [hK'def, if_pos hp]
    · simp only [hK'def, if_neg hp, dLR_zero]
  have hAL := int_chart_loc (xiP D) (fun p => norm_xiP D p) (continuous_xiP D).aestronglyMeasurable hK' m
    (fun p => by
      by_cases hp : p ∈ P0
      · simp only [hK'def, if_pos hp]; exact ckOn_rho D hp.1 hFm
      · simp only [hK'def, if_neg hp]; exact ckOn_zero _)
    hg0G hδp hcl
    (fun w hw Y hY => by
      refine (hDom1 (w.map Formalism.FourierDecayAlt.P.Ux10.Lt) [] (hunit w) (by simp) (by simpa using hw) _
        (hKOm (hmemK Y hY))).congr ?_
      filter_upwards [goodae] with p hp
      rw [hsel, if_pos hp, dLR_rho D hp.1])
    (fun p => ‖bd p‖) hbdI.norm
    (fun w hw Y hY p => by
      rw [hsel]
      by_cases hp : p ∈ P0
      · rw [if_pos hp]; exact (hp.2 _ ⟨w, hw, rfl⟩ _ (hmemK Y hY)).trans (Real.le_norm_self _)
      · rw [if_neg hp, norm_zero]; exact norm_nonneg _)
  have hAL' : ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞) (fun Y => JF D F (Formalism.FourierDecayAlt.P.Ux10.chart g0 Y))
      (Metric.ball 0 δ) := by
    refine hAL.congr fun Y _ => ?_
    show ∫ p, xiP D p • rho D p F _ ∂D.μSS = _
    refine integral_congr_ae ?_
    filter_upwards [goodae] with p hp
    simp only [hK'def, if_pos hp]
  obtain ⟨U, F', hU, hgU, hF', hUF⟩ := ck_at_of_chart hg0G hδp hAL'
  exact ⟨U, F', hU, hgU, hF', fun g hg hgl => hUF g hg hgl.1⟩

end

theorem _root_.Formalism.FourierDecayAlt.P.bessel_words_of_domain : JWordsOfDom := by
  intro hDom k r Wp Wq _ _ _ _ _ _ D A m F hThr hCC
  obtain ⟨hDom1, hDom2⟩ := hDom k r Wp Wq D A m F hThr hCC
  obtain ⟨c, hc⟩ := hCC
  have hFm : CkOn (m : ℕ∞) (GV k r) F := hc.1
  have hW := words_all D hFm hDom1 hDom2
  refine ⟨ck_all D hFm hDom1 hDom2, fun u v hu hv hl g hg => ?_⟩
  obtain ⟨bd, hbdI, hbd⟩ := hDom2 {g} isCompact_singleton (Set.singleton_subset_iff.2 hg)
  have hb := hbd u v hu hv hl g (Set.mem_singleton g)
  refine ⟨hbdI.norm.mono' ((continuous_xiP D).aestronglyMeasurable.smul (hDom1 u v hu hv hl g hg)) ?_, ?_⟩
  · filter_upwards [hb] with p hp
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_xiP D p)).trans (hp.trans (Real.le_norm_self _))
  · rw [hW u v hu hv hl g hg]
    refine integral_congr_ae ?_
    filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_inSS D] with p hp
    rw [dLR_rho D hp]

end Formalism.FourierDecayAlt.P.WeakDominationWordBounds
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TopPSD
section
open Formalism.FourierDecayAlt NumberField MeasureTheory
open scoped ComplexOrder

namespace Formalism.FourierDecayAlt.P

theorem top_positive_semidefinite : Top.TopPSDT := by
  intro Wp Wq _ _ _ _ _ P l0 T ν' m₀ Θ TP f χ admitted ε hε w hw hne Y
  unfold TB.PSDOn
  set F := D.cutF T.base χ f ε
  set dd := Top.dH P l0 (Formalism.QuantumDeterminants.Tz P.k P.r T.base.z * Formalism.QuantumDeterminants.Tz P.k P.r T.base.z') w

  let X : Wd.Ix (Fin w.length) → M.Ty P → C.LPt → (Wq →L[ℂ] Wp) :=
    fun e ρ p => (TP.E ρ).comp (D.vecV T.base ν' m₀ (Θ.Θ w e F) p)
  let g : Wd.Ix (Fin w.length) → M.Ty P → Matrix Y Y ℂ := fun e ρ =>
    Matrix.of fun x y => ((dd (x : C.LPt) e ρ * dd (y : C.LPt) e ρ : ℝ) : ℂ) * B.hsInner (X e ρ x) (X e ρ y)
  have hterm : ∀ e ρ, (g e ρ).PosSemidef := by
    intro e ρ
    let v : Y → _ := fun x => ((dd (x : C.LPt) e ρ : ℝ) : ℂ) • B.hsVec (X e ρ x)
    have h := (Matrix.posSemidef_gram ℂ v).transpose
    have heq : g e ρ = (Matrix.gram ℂ v).transpose := by
      ext x y
      simp only [g, v, Matrix.of_apply, Matrix.transpose_apply, Matrix.gram_apply, inner_smul_left,
        inner_smul_right, B.hsInner, Complex.conj_ofReal]
      push_cast
      ring
    rw [heq]
    exact h
  have hsum : (Matrix.of fun x y : Y => Top.topOf P l0 T ν' m₀ Θ TP F w x y) = ∑ e, ∑ ρ, g e ρ := by
    ext x y
    simp [g, X, dd, Top.topOf, Matrix.sum_apply]
  rw [hsum]
  refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ ha hb => ha.add hb) Matrix.PosSemidef.zero
    (fun e _ => ?_)
  exact Finset.sum_induction _ Matrix.PosSemidef (fun _ _ ha hb => ha.add hb) Matrix.PosSemidef.zero
    (fun ρ _ => hterm e ρ)

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TopTwistDensOfWaveQQ
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

namespace TwistedTransfer

section Actual

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem mulOp_comm_fn (X : ActualOps k r z z' π π') (W : Module.End ℂ (RadSp k r z z' π π'))
    (m : (Fin r → ℂ) → Mx k r → ℂ) (hW : multiplicationOperator W m) (j : Fin 6) : W * X.fn j = X.fn j * W := by
  have hW1 : ∀ (Φ : RadSp k r z z' π π') c g, (W Φ : Fn k r (Wq →L[ℂ] Wp)) c g =
      m c g • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g := hW
  apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
  simp only [Module.End.mul_apply]
  rw [hW1]
  by_cases hp : (c, g) ∈ DomR k r z z'
  · have h1 := X.fn_apply j Φ (c, g) hp
    have h2 := X.fn_apply j (W Φ) (c, g) hp
    simp only at h1 h2
    rw [h1, h2, hW1, smul_comm]
  · have h1 := (X.fn j Φ).2.1 (c, g) hp
    have h2 := (X.fn j (W Φ)).2.1 (c, g) hp
    simp only at h1 h2
    rw [h1, h2, smul_zero]

end Actual

end TwistedTransfer

end Formalism.FourierDecayAlt.P5
end
end

