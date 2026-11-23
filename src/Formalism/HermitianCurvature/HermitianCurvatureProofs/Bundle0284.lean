module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0282
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0164
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomVMul
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

theorem vector_multiplication_holds : NFVMul := by
  intro Wp Wq _ _ _ _ _ _ P p φ F γ _hγ hG
  by_cases hc : ((φ (TBB.Gp p γ) : ℝ) : ℂ) = 0
  · rw [hc, zero_smul]
    unfold KB.Pl.V D.vecV
    split_ifs with h1 h2
    · have hae : ∀ᵐ q ∂p.T.base.μSS,
          D.orbIntegrand p.T.base h2.choose
            (fun g => ((φ (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • F g) q =
          (1 : ℂ) • D.orbIntegrand p.T.base h2.choose (fun _ => (0 : Wq →L[ℂ] Wp)) q := by
        filter_upwards [TBBx2.ae_inSS p.T.base] with q hq
        have hGq : Gf P.k P.r p.T.base.z p.T.base.z' (B.sgs q h2.choose) = TBB.Gp p γ := by
          rw [TBBx2.Gf_sgs _ q hq, TBBx2.Gf_of_Zhat _ _ _ _ h2.choose_spec.2.1]
          rfl
        unfold D.orbIntegrand B.rho
        simp [hGq, hc]
      rw [TBBx4.orbJ_smul_ae _ _ _ _ _ _ one_ne_zero hae, one_smul]
      have h0 := TBBx4.orbJ_smul_ae p.T.base h2.choose
        (D.muR p.T.base h2.choose (h1.1.2 ▸ D.ptPerm γ)) (fun _ => (0 : Wq →L[ℂ] Wp))
        (fun _ => (0 : Wq →L[ℂ] Wp)) (2 : ℂ) two_ne_zero
        (ae_of_all _ fun q => by unfold D.orbIntegrand B.rho; simp)
      rw [two_smul] at h0
      simpa using h0
    · simp
    · simp
  · unfold KB.Pl.V D.vecV
    split_ifs with h1 h2
    · apply TBBx4.orbJ_smul_ae _ _ _ _ _ _ hc
      filter_upwards [TBBx2.ae_inSS p.T.base] with q hq
      have hGq : Gf P.k P.r p.T.base.z p.T.base.z' (B.sgs q h2.choose) = TBB.Gp p γ := by
        rw [TBBx2.Gf_sgs _ q hq, TBBx2.Gf_of_Zhat _ _ _ _ h2.choose_spec.2.1]
        rfl
      unfold D.orbIntegrand B.rho
      simp only [hGq, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
      rw [smul_comm]
    · simp
    · simp

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopFormTDMDop
section
namespace Formalism.FourierDecayAlt.P.CutBP.TDM

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section loc

variable {k r : ℕ} {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]

theorem dop_rdV_local {X : B.Mat k r} (hX : B.inLie k r X) {U : Set (B.Mat k r)} (hU : IsOpen U)
    {f f' : B.Mat k r → E₁} (he : ∀ x ∈ U, x ∈ B.GV k r → f x = f' x) {g : B.Mat k r} (hg : g ∈ U)
    (hgG : g ∈ B.GV k r) : Formalism.REAL.RdV X f g = Formalism.REAL.RdV X f' g := by
  show deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0 =
    deriv (fun t : ℝ => f' (g * NormedSpace.exp ((t : ℂ) • X))) 0
  apply Filter.EventuallyEq.deriv_eq
  have hc : Continuous (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) :=
    (Formalism.FourierDecayAlt.P.B5.curve_contDiff g X).continuous
  have hev : ∀ᶠ t : ℝ in nhds (0 : ℝ), g * NormedSpace.exp (((t : ℝ) : ℂ) • X) ∈ U := by
    apply hc.continuousAt.preimage_mem_nhds
    show U ∈ nhds (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X))
    rw [Formalism.FourierDecayAlt.P.B5.curve_zero]
    exact hU.mem_nhds hg
  filter_upwards [hev] with t ht
  exact he _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hgG hX t)

theorem dop_rw_local (w : List (B.Mat k r)) (hw : ∀ X ∈ w, B.inLie k r X) {U : Set (B.Mat k r)} (hU : IsOpen U)
    {f f' : B.Mat k r → E₁} (he : ∀ x ∈ U, x ∈ B.GV k r → f x = f' x) :
    ∀ x ∈ U, x ∈ B.GV k r → B.Rw w f x = B.Rw w f' x := by
  induction w with
  | nil => exact he
  | cons X w ih =>
    intro x hx hxG
    exact dop_rdV_local (hw X (by simp)) hU (ih (fun Y hY => hw Y (by simp [hY]))) hx hxG

theorem dop_rw_zero : ∀ v : List (B.Mat k r), B.Rw v (0 : B.Mat k r → E₁) = 0
  | [] => rfl
  | X :: v => by
    show Formalism.REAL.RdV X (B.Rw v 0) = 0
    rw [dop_rw_zero v]
    funext g
    simp [Formalism.REAL.RdV]

theorem dop_ckOn_ap {UU : Set (B.Mat k r)} {a : B.Mat k r → (E₁ →L[ℂ] E₂)} {Φ : B.Mat k r → E₁}
    (ha : B.CkOn ⊤ UU a) (hΦ : B.CkOn ⊤ UU Φ) : B.CkOn ⊤ UU (fun g => a g (Φ g)) := by
  intro g₀ hg₀
  obtain ⟨U, a', hU, hgU, hc, hff⟩ := ha g₀ hg₀
  obtain ⟨U₂, Φ', hU₂, hgU₂, hc₂, hff₂⟩ := hΦ g₀ hg₀
  refine ⟨U ∩ U₂, fun g => a' g (Φ' g), hU.inter hU₂, ⟨hgU, hgU₂⟩, ?_,
    fun g hg hgG => by simp only [hff g hg.1 hgG, hff₂ g hg.2 hgG]⟩
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun g => ContinuousLinearMap.restrictScalarsL ℂ E₁ E₂ ℝ ℝ (a' g)) (U ∩ U₂) :=
    (ContinuousLinearMap.restrictScalarsL ℂ E₁ E₂ ℝ ℝ).contDiff.comp_contDiffOn
      (hc.mono Set.inter_subset_left)
  exact h1.clm_apply (hc₂.mono Set.inter_subset_right)

theorem dop_ckOn_Rw {UU : Set (B.Mat k r)} {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X)
    {f : B.Mat k r → E₁} (hf : B.CkOn ⊤ UU f) : B.CkOn ⊤ UU (B.Rw w f) := by
  rw [← Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw_wR]
  apply Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_Dw (fun x hx => Formalism.FourierDecayAlt.P.BetaSesquilinearity.lie_LR (u := []) (by simp) hw x
    (by simpa [Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL] using hx))
  have e : ((⊤ : ℕ∞) + ((Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR w).length : ℕ∞)) = ⊤ := top_add _
  rw [e]; exact hf

end loc

section op

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem dop_ckOn_opApply {UU : Set (B.Mat k r)} {J : B.Mat k r → (Wq →L[ℂ] Wp)} (hJ : B.CkOn ⊤ UU J) :
    ∀ Θ : B.DiffOp k r Wp Wq, (∀ T ∈ Θ, B.CkOn ⊤ UU T.coef) → B.CkOn ⊤ UU (B.opApply Θ J)
  | [], _ => by
    have e : B.opApply ([] : B.DiffOp k r Wp Wq) J = fun _ => 0 := by funext g; simp [B.opApply]
    rw [e]; exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_zero
  | T :: Θ, h => by
    have e : B.opApply (T :: Θ) J = fun g => T.coef g (B.Rw T.word J g) + B.opApply Θ J g := by
      funext g; simp [B.opApply]
    rw [e]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add (dop_ckOn_ap (h T (by simp)) (dop_ckOn_Rw T.word_lie hJ))
      (dop_ckOn_opApply hJ Θ (fun T' hT' => h T' (by simp [hT'])))

theorem dop_opApply_zero (Θ : B.DiffOp k r Wp Wq) {O : Set (B.Mat k r)} (hO : IsOpen O)
    {J : B.Mat k r → (Wq →L[ℂ] Wp)} (hJ : ∀ g ∈ O, g ∈ B.GV k r → J g = 0) :
    ∀ g ∈ O, g ∈ B.GV k r → B.opApply Θ J g = 0 := by
  intro g hg hgG
  unfold B.opApply
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨T, _, rfl⟩ := List.mem_map.1 hx
  rw [dop_rw_local T.word T.word_lie hO (f' := 0) hJ g hg hgG, dop_rw_zero]
  simp

end op

theorem diff_operator_in_class_CC : DopCC := by
  intro Wp Wq _ _ _ _ _ _ P p X w Cb hD hX hw e
  obtain ⟨nf, fib, o, κ, Dop, hfib, hDD, -, -, hΘ⟩ := hD w hw e
  set Bs := p.T.base with hBs
  obtain ⟨hXs, ⟨R, hR⟩, ⟨ε, hε, hXε⟩⟩ := hX
  set O : Set (B.Mat P.k P.r) := {g | R < B.gN g} ∪ {g | Gf P.k P.r Bs.z Bs.z' g < ε} with hOdef
  have hO : IsOpen O := (isOpen_lt continuous_const Formalism.FourierDecayAlt.P.B6.gN_continuous).union
    (isOpen_lt (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.gf_cont _ _) continuous_const)
  have hX0 : ∀ g ∈ O, g ∈ B.GV P.k P.r → X g = 0 := by
    intro g hg hgG
    by_contra hne
    rcases hg with h | h
    · exact absurd (hR g hgG hne) (not_le.2 h)
    · exact absurd (hXε g hgG hne) (not_le.2 h)
  set Y : B.Mat P.k P.r → (Wq →L[ℂ] Wp) := B.opApply Dop X with hYdef
  have hY0 : ∀ g ∈ O, g ∈ B.GV P.k P.r → Y g = 0 := dop_opApply_zero Dop hO hX0
  have hYs : B.CkOn ⊤ (B.GV P.k P.r) Y := by
    intro g₀ hg₀
    by_cases hgO : g₀ ∈ O
    · exact ⟨O, 0, hO, hgO, contDiffOn_const, fun g hg hgG => hY0 g hg hgG⟩
    · have hG : ε ≤ Gf P.k P.r Bs.z Bs.z' g₀ := by
        by_contra h; exact hgO (Or.inr (not_le.1 h))
      have hdom : g₀ ∈ C6.domL Bs ∅ := ⟨hg₀, lt_of_lt_of_le hε hG, fun l hl => absurd hl (Finset.notMem_empty l)⟩
      have hXd : B.CkOn ⊤ (C6.domL Bs ∅) X := fun g hg => hXs g hg.1
      exact dop_ckOn_opApply hXd Dop (fun T hT => (hDD.1 T hT).1) g₀ hdom
  refine ⟨Y, fun g hg hG => ?_, fun A => ?_⟩
  · exact (hΘ X g ⟨hg, hG, fun l hl => absurd hl (Finset.notMem_empty l)⟩).symm
  ·
    set K : Set (B.Mat P.k P.r) := B.GV P.k P.r ∩ ({g | B.gN g ≤ R} ∩ {g | ε ≤ Gf P.k P.r Bs.z Bs.z' g}) with hKdef
    have hK : IsCompact K := (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le P.k P.r R).of_isClosed_subset
      (Formalism.FourierDecayAlt.P.B5.GV_closed.inter ((isClosed_le Formalism.FourierDecayAlt.P.B6.gN_continuous continuous_const).inter
        (isClosed_le continuous_const (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.gf_cont _ _))))
      (fun g hg => hg.2.1)
    have hYc : ContinuousOn Y (B.GV P.k P.r) := Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn hYs
    have hfc : ContinuousOn (fun g => B.gN g ^ A * ‖Y g‖) K := by
      refine ContinuousOn.mul ?_ ((hYc.mono Set.inter_subset_left).norm)
      exact (Formalism.FourierDecayAlt.P.B6.gN_continuous.continuousOn).rpow_const
        (fun g hg => Or.inl (ne_of_gt (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_pos hg.1)))
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hfc
    refine ⟨max C 0, ⟨?_, ?_⟩⟩
    · intro g₀ hg₀
      obtain ⟨U, f', hU, hgU, hc, he⟩ := hYs g₀ hg₀
      exact ⟨U, f', hU, hgU, hc.of_le (by exact_mod_cast le_top), he⟩
    · intro u v _ _ huv g hg
      have hu : u = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hv : v = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hu; subst hv
      show B.gN g ^ A * ‖Y g‖ ≤ max C 0
      by_cases hgK : g ∈ K
      · have := hC g hgK
        rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (le_of_lt (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_pos hg)) _)
          (norm_nonneg _))] at this
        exact le_trans this (le_max_left _ _)
      · have hgO : g ∈ O := by
          by_contra hgO
          apply hgK
          refine ⟨hg, ?_, ?_⟩
          · show B.gN g ≤ R
            by_contra h; exact hgO (Or.inl (not_le.1 h))
          · show ε ≤ Gf P.k P.r Bs.z Bs.z' g
            by_contra h; exact hgO (Or.inr (not_le.1 h))
        rw [hY0 g hgO hg, norm_zero, mul_zero]
        exact le_max_right _ _

end

end Formalism.FourierDecayAlt.P.CutBP.TDM
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopFormTDMSE
section
namespace Formalism.FourierDecayAlt.P.CutBP.TDM

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

theorem nPt_bigPt_eq (k r : ℕ) (TT : ℝ) (c : Fin (r + 1) → ℂ) :
    TBB.nPt k r TT (TBB.bigPt r c) = ∏ i : Fin (r + 1), (if 1 + (i : ℕ) = r + 1 then
      (Complex.normSq (c (Fin.last r)) - TT) ^ (k - 1)
      else ‖c i‖ ^ (2 * (C.Mlev k r (1 + (i : ℕ)) - 2))) := by
  unfold TBB.nPt D.ptGG
  rw [Formalism.FourierDecayAlt.P.CutBP.ptLast_bigPt]
  exact Formalism.FourierDecayAlt.P.CutBP.level_product_of_constant_weights k r _ (r + 1) c 1

theorem measurable_nPt_bigPt (k r : ℕ) (TT : ℝ) :
    Measurable (fun c : Fin (r + 1) → ℂ => TBB.nPt k r TT (TBB.bigPt r c)) := by
  simp only [nPt_bigPt_eq]
  refine Finset.measurable_prod _ fun i _ => ?_
  by_cases h : 1 + (i : ℕ) = r + 1
  · simp only [h, if_true]
    exact ((Complex.continuous_normSq.measurable.comp (measurable_pi_apply _)).sub_const _).pow_const _
  · simp only [h, if_false]
    have hm : Measurable (fun c : Fin (r + 1) → ℂ => ‖c i‖) := continuous_norm.measurable.comp (measurable_pi_apply i)
    exact hm.pow_const _

theorem wPt_bigPt_eq (TT : ℝ) (r : ℕ) (c : Fin (r + 1) → ℂ) :
    Top.wPt TT r (TBB.bigPt r c) = Complex.normSq (∏ i, c i) /
      (Complex.normSq (∏ i, c i) - TT * Complex.normSq (∏ a : Fin r, c a.castSucc)) := by
  show Complex.normSq (D.ptMatN (Formalism.FourierDecayAlt.P.PBJ.bigPt c) (r + 1)).det /
    D.ptG TT r (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = _
  unfold D.ptG
  rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
    Matrix.det_diagonal, Matrix.det_diagonal]

theorem measurable_wPt_bigPt (TT : ℝ) (r : ℕ) :
    Measurable (fun c : Fin (r + 1) → ℂ => Top.wPt TT r (TBB.bigPt r c)) := by
  simp only [wPt_bigPt_eq]
  have h1 : Measurable (fun c : Fin (r + 1) → ℂ => Complex.normSq (∏ i, c i)) :=
    (Complex.continuous_normSq.comp (continuous_finsetProd _ fun i _ => continuous_apply i)).measurable
  have h2 : Measurable (fun c : Fin (r + 1) → ℂ => Complex.normSq (∏ a : Fin r, c a.castSucc)) :=
    (Complex.continuous_normSq.comp (continuous_finsetProd _ fun a _ => continuous_apply _)).measurable
  exact h1.div (h1.sub (h2.const_mul TT))

theorem scalar_point_measurability_holds : ScalarMeas := fun k r TT => ⟨measurable_nPt_bigPt k r TT, measurable_wPt_bigPt TT r⟩

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem entry_le_gN {k r : ℕ} (g : B.Mat k r) (i j : Fin (2 * r + k + 1)) : ‖g i j‖ ≤ B.gN g := by
  unfold B.gN
  rw [← Real.sqrt_sq (norm_nonneg (g i j)), Complex.sq_norm]
  apply Real.sqrt_le_sqrt
  have h1 : Complex.normSq (g i j) ≤ ∑ j', Complex.normSq (g i j') :=
    Finset.single_le_sum (f := fun j' => Complex.normSq (g i j')) (fun j' _ => Complex.normSq_nonneg _)
      (Finset.mem_univ j)
  have h2 : ∑ j', Complex.normSq (g i j') ≤ ∑ i', ∑ j', Complex.normSq (g i' j') :=
    Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (g i' j'))
      (fun i' _ => Finset.sum_nonneg fun j' _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  exact h1.trans h2

theorem gN_ball_compact (k r : ℕ) (R : ℝ) : IsCompact {g : B.Mat k r | B.gN g ≤ R} := by
  have hc : Continuous (fun g : B.Mat k r => B.gN g) := by
    unfold B.gN
    exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      Complex.continuous_normSq.comp (continuous_id.matrix_elem i j))
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_le hc continuous_const) ?_
  rw [isBounded_iff_forall_norm_le]
  refine ⟨max R 0, fun g hg => ?_⟩
  rw [Matrix.norm_le_iff (le_max_right _ _)]
  intro i j
  exact (entry_le_gN g i j).trans (le_trans hg (le_max_left _ _))

theorem cptCoef_inCC {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {X : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hX : KB.CptCoef Bs X) (A : ℝ) (m : ℕ) : B.InCC A m X := by
  obtain ⟨R, hR⟩ := hX.2.1
  exact Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hX.1 (gN_ball_compact k r R)
    (fun g hg hgC => by by_contra h; exact hgC (hR g hg h)) A m

theorem empty_list_measurability_holds : EmptyMeas := by
  intro Wp Wq _ _ _ _ _ _ P p X hX
  set Bs := p.T.base with hBs
  set T := Tz P.k P.r Bs.z with hT
  set T' := Tz P.k P.r Bs.z' with hT'
  set A : ℝ := 9 * ((P.r : ℝ) + 1) * (((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 2 + 1) with hA
  have hThr : JF.TransportedAlt P.k P.r A 0 := by
    unfold JF.TransportedAlt
    have hr : (0 : ℝ) < 9 * ((P.r : ℝ) + 1) := by positivity
    rw [Nat.cast_zero, mul_zero, sub_zero, lt_div_iff₀ hr, hA]
    nlinarith
  have hc := Formalism.FourierDecayAlt.P.CutBP.jgq_continuousOn Bs hThr (cptCoef_inCC Bs hX A 0)
  have hcn : ContinuousOn (fun q => ‖B.hsVec (B.JF Bs X (B.gq Bs q))‖ ^ 2) (JF.QDom P.k P.r Bs.z Bs.z') :=
    ((Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.continuous.comp_continuousOn hc).norm).pow 2
  have hm := Formalism.FourierDecayAlt.P.CutBP.aesm_weight_smul Bs hcn
  let e : (Fin (P.r + 1) → ℂ) ≃ᵐ (Fin P.r → ℂ) × ℂ :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last P.r)).trans MeasurableEquiv.prodComm
  have hmp : MeasurePreserving e volume volume :=
    (Measure.measurePreserving_swap).comp (volume_preserving_piFinSuccAbove (fun _ : Fin (P.r + 1) => ℂ) (Fin.last P.r))
  have he : ∀ c, e c = ((fun j => c j.castSucc), c (Fin.last P.r)) := by
    intro c
    simp [e, MeasurableEquiv.piFinSuccAbove]
    rfl
  have hm2 := hm.comp_measurePreserving hmp
  refine hm2.congr ?_
  filter_upwards [ae_all_ne P.r] with c hc0
  show bcWeight P.k P.r T T' (e c) • ‖B.hsVec (B.JF Bs X (B.gq Bs (e c)))‖ ^ 2 = topD p X [] c
  rw [he c, smul_eq_mul]
  have hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hc0
  unfold topD
  rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p X hl]
  have hk : 2 ≤ P.k := p.hl.2.2
  have hcin : ∀ a : Fin P.r, c a.castSucc ≠ 0 := fun a => hc0 _
  have hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
    Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hcin a)
  have hGeq : TBB.Gp p (TBB.bigPt P.r c) =
      Complex.normSq (∏ i : Fin P.r, c i.castSucc) * (Complex.normSq (c (Fin.last P.r)) - T * T') := by
    show D.ptG (T * T') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = _
    unfold D.ptG
    rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
      Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
    ring
  by_cases hG : 0 < TBB.Gp p (TBB.bigPt P.r c)
  · rw [Formalism.FourierDecayAlt.P.CutBP.hsVec_norm_V_bigPt p X c hc0 hG]
    have hζ : T * T' ≤ Complex.normSq (c (Fin.last P.r)) := by
      rw [hGeq] at hG
      have := (pos_iff_pos_of_mul_pos hG).1 hp
      linarith
    have hn : TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) =
        bcWeight P.k P.r T T' ((fun j => c j.castSucc), c (Fin.last P.r)) :=
      Formalism.FourierDecayAlt.P.CutBP.nPt_bigPt P.k P.r T T' c hζ
    rw [hn, Real.mul_self_sqrt (Formalism.FourierDecayAlt.P.CutBP.bcWeight_nonneg0 _ _ _ _ _)]
    rfl
  · have hV : p.V X (TBB.bigPt P.r c) = 0 := by
      unfold KB.Pl.V D.vecV
      rw [dite_eq_right (fun h => hG h.2)]
    rw [hV]
    have hw0 : bcWeight P.k P.r T T' ((fun j => c j.castSucc), c (Fin.last P.r)) = 0 := by
      unfold bcWeight
      split_ifs with hle
      · have hle2 : Complex.normSq (c (Fin.last P.r)) ≤ T * T' := by
          by_contra hlt
          push Not at hlt
          apply hG
          rw [hGeq]
          exact mul_pos hp (by linarith)
        have hle' : T * T' ≤ Complex.normSq (c (Fin.last P.r)) := hle
        have heq : Complex.normSq (c (Fin.last P.r)) - T * T' = 0 := by linarith
        show (∏ a : Fin P.r, ‖c a.castSucc‖ ^ (2 * (Mdim P.k P.r a - 2))) *
          (Complex.normSq (c (Fin.last P.r)) - T * T') ^ (P.k - 1) = 0
        rw [heq, zero_pow (by omega), mul_zero]
      · rfl
    rw [hw0]
    have h0 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
      unfold B.hsVec
      rfl
    simp [h0]

end

end Formalism.FourierDecayAlt.P.CutBP.TDM
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopFormTDMVV
section
namespace Formalism.FourierDecayAlt.P.CutBP.TDM

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

section orb

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem vv_choose_congr {α : Sort*} {P Q : α → Prop} (e : P = Q) (hP : ∃ x, P x) (hQ : ∃ x, Q x) :
    hP.choose = hQ.choose := by
  subst e; rfl

theorem orbJ_congr_gpos (Bs : B.RealPlaceData k r Wp Wq) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
    (hpos : 0 < Gf k r Bs.z Bs.z' γ) (μR : Measure (Mt k r)) (Y Y' : B.Mat k r → (Wq →L[ℂ] Wp))
    (hYY : ∀ g ∈ B.GV k r, 0 < Gf k r Bs.z Bs.z' g → Y g = Y' g) :
    D.orbJ Bs γ μR Y = D.orbJ Bs γ μR Y' := by
  have hae : D.orbIntegrand Bs γ Y =ᵐ[Bs.μSS] D.orbIntegrand Bs γ Y' := by
    filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with q hq
    have hG : 0 < Gf k r Bs.z Bs.z' (B.sgs q γ) := by
      have e : Gf k r Bs.z Bs.z' (B.sgs q γ) = Gf k r Bs.z Bs.z' γ := by
        unfold Gf
        rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hq, Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hq]
      rw [e]; exact hpos
    unfold D.orbIntegrand B.rho
    rw [hYY _ (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_GV Bs hq hγ) hG]
  have hP : (fun θ => D.IsNormCut Bs γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Bs γ Y q) Bs.μSS) =
      (fun θ => D.IsNormCut Bs γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Bs γ Y' q) Bs.μSS) := by
    funext θ
    apply propext
    apply and_congr_right
    intro _
    exact integrable_congr (hae.mono fun q hq => by simp only [hq])
  unfold D.orbJ
  by_cases h : ∃ θ, D.IsNormCut Bs γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Bs γ Y q) Bs.μSS
  · have h2 : ∃ θ, D.IsNormCut Bs γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Bs γ Y' q) Bs.μSS := hP ▸ h
    rw [dite_eq_left h, dite_eq_left h2, vv_choose_congr hP h h2]
    apply integral_congr_ae
    filter_upwards [hae] with q hq
    rw [hq]
  · have h2 : ¬∃ θ, D.IsNormCut Bs γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Bs γ Y' q) Bs.μSS := hP ▸ h
    rw [dite_eq_right h, dite_eq_right h2]

end orb

theorem vector_positive_cone : VecVGPos := by
  intro Wp Wq _ _ _ _ _ _ P p Y Y' hYY a
  unfold KB.Pl.V D.vecV
  by_cases h : D.IsLocPt a (P.r + 1) ∧
      0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r a
  · rw [dite_eq_left h, dite_eq_left h]
    by_cases h' : ∃ γ ∈ B.GV P.k P.r, Zhat P.k P.r p.T.base.z p.T.base.z' γ = D.ptMatN a (P.r + 1) ∧
        D.IsDFrame p.T.base p.ν' p.m₀ γ
    · rw [dite_eq_left h', dite_eq_left h']
      obtain ⟨hγ, hZ, -⟩ := h'.choose_spec
      have hpos : 0 < Gf P.k P.r p.T.base.z p.T.base.z' h'.choose := by
        rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ a _ h.1 hZ]; exact h.2
      exact orbJ_congr_gpos p.T.base hγ hpos _ Y Y' hYY
    · rw [dite_eq_right h', dite_eq_right h']
  · rw [dite_eq_right h, dite_eq_right h]

end

end Formalism.FourierDecayAlt.P.CutBP.TDM
end

