module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0078
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0079
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsScalarEvaluationsCuspFormsFiniteNetStatement
section
open Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.NetNorms NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.exists_scalar_evaluations_cusp_forms_finite_net : ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → 16 ≤ D.R.f → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∃ (n : ℕ) (ev : Fin n → ((recB h.toLawsCore).Cusp j w →ₛₗ[σ] ℂ)), (∀ F, ∃ y, (recB h.toLawsCore).supN j w σ F / 4 ≤ ‖ev y F‖) ∧ (∀ y F, ‖ev y F‖ ≤ (recB h.toLawsCore).supN j w σ F) ∧ Real.log (16 * (n : ℝ)) ≤ 1041 * Zb D large₂ ^ 3 ∧ ∀ (m : ℕ) (F : Fin m → (recB h.toLawsCore).Cusp j w), LinearIndependent T.Q.c.F F → LinearIndependent ℂ (fun i => fun y => ev y (F i)) := by
  intro D T h hG large₂ j hj w hP hL hr hf σ hσ
  classical
  obtain ⟨NN, -, hnet, hlog⟩ :=
    GlobalTheory.RunIn.exists_net_max_at_goodEmb D T h hG large₂ j hj w hP hL hr hf σ hσ
  obtain ⟨L, hLdef⟩ : ∃ L, L = lieFac (T.Q.Dw j) (xiR D) (wtA w) := ⟨_, rfl⟩
  have hL0 : 0 < L := hLdef ▸ lieFac_pos _ _ _

  have hpn : ∀ (k : (T.U j σ).Comp) (P : Frame ((T.U j σ).X k).Ψ D.R.r → ℂ) x,
      ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) P x
        = ‖P x‖ * ((T.U j σ).X k).nfac (laU (T.U j σ) (wtA w) w.n k) x := fun _ _ _ => rfl
  have hnf : ∀ (k : (T.U j σ).Comp) x, 0 ≤ ((T.U j σ).X k).nfac (laU (T.U j σ) (wtA w) w.n k) x := by
    intro k x
    have h1 := GlobalTheory.NetNormExamples.pnorm_nonneg ((T.U j σ).X k) (laU (T.U j σ) (wtA w) w.n k)
      (fun _ => (1 : ℂ)) x
    rwa [hpn, norm_one, one_mul] at h1
  have hg : goodOf T.Q.c σ = σ := by rw [goodOf, ite_eq_left hσ]

  have hsup : ∀ F : (recB h.toLawsCore).Cusp j w, (recB h.toLawsCore).supN j w σ F =
      L * supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) F.1) := by
    intro F
    dsimp only [recB, cutN]
    rw [ite_eq_left hj]
    dsimp only [Formalism.L2.Pj.Core.Ns, supC]
    rw [hg, hLdef]

  have hC (F : (recB h.toLawsCore).Cusp j w) :
      F.1 ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n := (Submodule.mem_inf.mp F.2).1
  have hhol : ∀ F : (recB h.toLawsCore).Cusp j w,
      rdU (T.U j σ) F.1 ∈ holSub (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) := by
    intro F
    exact ((mem_cusp _ _ _ _ _ _).mp (hC F)).2 σ hσ

  let pt : Fin NN.card → FPt (T.U j σ).X := fun y => (NN.equivFin.symm y).1
  have hsurj : ∀ p ∈ NN, ∃ y, pt y = p := fun p hp =>
    ⟨NN.equivFin ⟨p, hp⟩, by simp only [pt, Equiv.symm_apply_apply]⟩
  let a : Fin NN.card → ℝ := fun y =>
    L * ((T.U j σ).X (pt y).1).nfac (laU (T.U j σ) (wtA w) w.n (pt y).1) (pt y).2
  have ha : ∀ y, 0 ≤ a y := fun y => mul_nonneg hL0.le (hnf _ _)

  let ev : Fin NN.card → ((recB h.toLawsCore).Cusp j w →ₛₗ[σ] ℂ) := fun y =>
    { toFun := fun F => (a y : ℂ) * rdU (T.U j σ) F.1 (pt y).1 (pt y).2
      map_add' := fun F G => by
        show (a y : ℂ) * rdU (T.U j σ) (F.1 + G.1) (pt y).1 (pt y).2 =
          (a y : ℂ) * rdU (T.U j σ) F.1 (pt y).1 (pt y).2 + (a y : ℂ) * rdU (T.U j σ) G.1 (pt y).1 (pt y).2
        rw [map_add (f := _), Pi.add_apply, Pi.add_apply, mul_add]
      map_smul' := fun c F => by
        show (a y : ℂ) * rdU (T.U j σ) (c • F.1) (pt y).1 (pt y).2 =
          σ c • ((a y : ℂ) * rdU (T.U j σ) F.1 (pt y).1 (pt y).2)
        rw [LinearMap.map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
        ring }
  have hev : ∀ y F, ev y F = (a y : ℂ) * rdU (T.U j σ) F.1 (pt y).1 (pt y).2 := fun _ _ => rfl
  have hnorm : ∀ y F, ‖ev y F‖ =
      L * ((T.U j σ).X (pt y).1).pnorm (laU (T.U j σ) (wtA w) w.n (pt y).1)
        (rdU (T.U j σ) F.1 (pt y).1) (pt y).2 := by
    intro y F
    rw [hev, norm_mul, Complex.norm_of_nonneg (ha y), hpn]
    simp only [a]
    ring
  refine ⟨NN.card, ev, ?_, ?_, ?_, ?_⟩
  · intro F
    obtain ⟨p, hp, hb⟩ := hnet _ (hhol F)
    obtain ⟨y, rfl⟩ := hsurj p hp
    refine ⟨y, ?_⟩
    rw [hnorm, hsup]
    have := mul_le_mul_of_nonneg_left hb hL0.le
    linarith
  · intro y F
    rw [hnorm, hsup]
    exact mul_le_mul_of_nonneg_left
      (GlobalTheory.NetNormExamples.pnorm_le_supN (T.U j σ) _ (hhol F) (pt y)) hL0.le
  · exact hlog
  · intro m F hF
    have hlin := hF.map' (cutR T.C j w).subtype (cutR T.C j w).ker_subtype
    have hmem : ∀ i, (F i).1 ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n := fun i =>
      Formalism.L2.Pj.cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n (hC (F i))
    have hU := h.unf j hj σ hσ
    have hB := GlobalTheory.lawsFieldsSeparately.2.1
    have hreading := (GlobalTheory.reading_linearIndependent_and_injective hB _ _ _ _ (T.Q.Xo j) T.Q.c σ _
      (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) ((Formalism.L2.PjFree.isUnf_ofPj (T.U j σ)).2 hU)
      (wtA w) w.n).1 m (fun i => (F i).1) hmem hlin
    have hind : LinearIndependent ℂ (fun i => rdU (T.U j σ) (F i).1) := by
      exact hreading
    rw [Fintype.linearIndependent_iff] at hind ⊢
    intro g hgz i
    refine hind g ?_ i
    show ∑ i, g i • rdU (T.U j σ) (F i).1 = 0
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = ∑ i, g i • rdU (T.U j σ) (F i).1 := ⟨_, rfl⟩
    rw [← hQ]
    have hQmem : Q ∈ holSub (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) := by
      rw [hQ]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hhol (F i))
    have hval : ∀ y, (a y : ℂ) * Q (pt y).1 (pt y).2 = 0 := by
      intro y
      have h1 := congrFun hgz y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hev] at h1
      rw [hQ, Finset.sum_apply, Finset.sum_apply, Finset.mul_sum, ← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    obtain ⟨p, hp, hb⟩ := hnet Q hQmem
    obtain ⟨y, rfl⟩ := hsurj p hp
    have h0 : ((T.U j σ).X (pt y).1).pnorm (laU (T.U j σ) (wtA w) w.n (pt y).1) (Q (pt y).1) (pt y).2 = 0 := by
      have hn := congrArg (‖·‖) (hval y)
      simp only [norm_mul, Complex.norm_of_nonneg (ha y), norm_zero] at hn
      simp only [a] at hn
      rw [hpn]
      have h2 : L * (‖Q (pt y).1 (pt y).2‖ *
          ((T.U j σ).X (pt y).1).nfac (laU (T.U j σ) (wtA w) w.n (pt y).1) (pt y).2) = 0 := by
        rw [← hn]; ring
      exact (mul_eq_zero.mp h2).resolve_left hL0.ne'
    have hS : supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) Q ≤ 0 := by
      rw [h0, mul_zero] at hb
      exact hb
    funext k x
    by_cases hx : x ∈ ((T.U j σ).X k).dom
    · show Q k x = 0
      apply GlobalTheory.NetNormExamples.eq_zero_of_pnorm ((T.U j σ).X k) (laU (T.U j σ) (wtA w) w.n k) _ hx
      exact le_antisymm
        ((GlobalTheory.NetNormExamples.pnorm_le_supN (T.U j σ) _ hQmem ⟨k, ⟨x, hx⟩⟩).trans hS)
        (GlobalTheory.NetNormExamples.pnorm_nonneg _ _ _ _)
    · show Q k x = 0
      rw [hQ, Finset.sum_apply, Finset.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hz : rdU (T.U j σ) (F i).1 k x = 0 := by
        simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dite_eq_right hx]
      rw [Pi.smul_apply, Pi.smul_apply, hz, smul_zero]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaGeneratorReadingNeZeroAllFrames
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem exists_theta_ne_zero_record : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), D.R.r ≤ w.n → 3 * WeightAlgebra.DF w + 2 ≤ T.Q.l.M → ∀ (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ k, ∀ x ∈ ((T.U j σ).X k).dom, ∃ f ∈ T.th j w, rdU (T.U j σ) f k x ≠ 0 := by
  intro hC D T h j hj w hn hM σ hσ k x hx
  obtain ⟨_, _, _, _, hr1, hxi, hDF, _, hc, _⟩ := _root_.GlobalTheory.SupDict.record_dictionary D T h j hj w
  obtain ⟨st, hnab⟩ := h.nabPin j hj
  obtain ⟨f, hf, hne⟩ := _root_.GlobalTheory.ThetaNoZero.exists_thGen_rdU_ne_zero hC _ _ _ _ (T.Q.Xo j) T.Q.c σ D.R.r (Formalism.L2.PjFree.Unf.ofPj (T.U j σ))
    ((Formalism.L2.PjFree.goodEmb_iff σ).2 hσ) ((Formalism.L2.PjFree.isUnf_ofPj _).2 (h.toLawsCore.unf j hj σ hσ)) hr1
    (2 * xiR D) (mul_pos two_pos hxi) (hc σ hσ) (wtA w) w.n (dom_wtA w) hn (by omega) st (T.nab j) hnab k x hx
  refine ⟨f, hf, ?_⟩
  rwa [Formalism.L2.PjFree.rdU_ofPj] at hne

end GlobalTheory.RunIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogSupNormThetaGeneratorLe
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem log_sup_theta_generator_le : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → ∀ (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P ∈ harmA T.Q.c (wtA w) w.n → ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c (T.nab j) x P f → ∀ (σ : T.Q.c.F →+* ℂ) (ℓ : ℝ), 0 ≤ ℓ → l1At σ P ≤ Real.exp ℓ → Real.log (T.Ns j w σ f) ≤ ℓ + 10 * large₂.sc.L * absA w + 200 * D.R.f * D.R.r * w.n * large₂.sc.L := by
  intro hCI D T hT hG large₂ j hj w hPR hL hr hLP x P hP f hf σ ℓ hℓ hp1
  obtain ⟨inst, hnab⟩ := hT.nabPin j hj
  have hunf : IsUnf (T.U j (goodOf T.Q.c σ)) := hT.toLawsCore.unf j hj _ (goodEmb_goodOf T.Q.c σ)
  obtain ⟨hfd, hrdl, hrd1, hf1, hr1, hxi, hDF, habs, hcU, hlie, -, -, -, hl1⟩ :=
    _root_.GlobalTheory.SupDict.record_dictionary D T hT j hj w
  obtain ⟨-, hLrd, -, -, hLf, -, -, hLa, hLn⟩ := id hPR
  have hL0 : (0 : ℝ) < large₂.sc.L := by linarith
  have ha0 : (0 : ℝ) ≤ absA w := by rw [habs]; exact Nat.cast_nonneg _
  have hσg : GoodEmb T.Q.c (goodOf T.Q.c σ) := goodEmb_goodOf T.Q.c σ
  have hNs : T.Ns j w σ f = lieFac (T.Q.Dw j) (xiR D) (wtA w) *
      supN (T.U j (goodOf T.Q.c σ)).X (laU (T.U j (goodOf T.Q.c σ)) (wtA w) w.n)
        (rdU (T.U j (goodOf T.Q.c σ)) f) := rfl
  have hS0 : 0 ≤ supN (T.U j (goodOf T.Q.c σ)).X (laU (T.U j (goodOf T.Q.c σ)) (wtA w) w.n)
      (rdU (T.U j (goodOf T.Q.c σ)) f) := ENNReal.toReal_nonneg
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [hNs, ← h0, mul_zero, Real.log_zero]
    positivity

  have hC : f ∈ T.C j w := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTies1.cuspTie D T hT j hj w hLP x P hP f hf
  obtain ⟨k, xf, -, hort, hSle, hla, hlog⟩ :=
    _root_.GlobalTheory.RunIn.half_sup_at_ortho_frame D T hT hG large₂ j hj w hPR hL hr hLP (goodOf T.Q.c σ) hσg f hC hpos
  have hlam0 : 0 < Real.sqrt (((T.U j (goodOf T.Q.c σ)).X k).firstMinimumSq xf.1) := Real.sqrt_pos.mpr hla
  have hlam2 : Real.sqrt (((T.U j (goodOf T.Q.c σ)).X k).firstMinimumSq xf.1) ^ 2 =
      ((T.U j (goodOf T.Q.c σ)).X k).firstMinimumSq xf.1 := Real.sq_sqrt hla.le

  have hU := _root_.GlobalTheory.Dict.ThetaPt.theta_bound_ortho hCI _ _ _ _ (T.Q.Xo j) T.Q.c (goodOf T.Q.c σ) D.R.r
    (Formalism.L2.PjFree.Unf.ofPj (T.U j (goodOf T.Q.c σ))) ((Formalism.L2.PjFree.goodEmb_iff _).mpr hσg)
    ((Formalism.L2.PjFree.isUnf_ofPj _).mpr hunf) hr1 (2 * xiR D) (by linarith)
    (fun k τ => hcU _ hσg k τ) (wtA w) w.n (dom_wtA w) inst (T.nab j) hnab x P hP f hf k xf hort
    _ hlam0 hlam2.le
  rw [hfd] at hU
  have key := GlobalTheory.log_exp_mul_le_of_generator_sup_bound D.R.f D.R.r w.n
    (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w)) large₂.sc.L ℓ (absA w) (rdE D.host.E)
    (Real.sqrt (((T.U j (goodOf T.Q.c σ)).X k).firstMinimumSq xf.1)) (2 * xiR D) 1 _ _ (l1At σ P)
    hL hf1 hr1 hr (by rw [habs]; exact_mod_cast hDF) (by rw [habs]; exact hLa) hLn hLf hrd1
    (by rw [hrdl]; exact hLrd) hlam0 (by rw [hlam2]; exact hlog) (by linarith) hℓ
    (by unfold l1At; exact Finset.sum_nonneg fun _ _ => norm_nonneg _) hp1 zero_le_one
    (Real.one_le_exp (by positivity)) hS0 hSle (by rw [one_mul, ← hl1 _ σ P]; exact hU)
  rw [hNs, hlie]
  exact key

end GlobalTheory.RunIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormShortGeneratorEvalLeOrthonormalFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_short_generator_eval_le_orthonormal_frame : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ t : ℝ, 0 < t → (∀ k τ, (U.X k).c τ = t) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → r ≤ n → ∀ d : DeltaDat Xo c n, d.IsLev → 0 < d.pd → l.A = 1 → d.l₂.A = 1 → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → (∃ ph ψ x₀, d.PhiPin ph ψ x₀) → UnitC d → ∀ (Λ : GenLat E n) (N : ℕ) (x0 : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → (∃ β : c.F, β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β) → P ∈ harmL c Λ a → IsShortRule Xo c d Λ N x0 P f → ∀ k (x : (U.X k).dom), (U.X k).IsOrtho x.1 → ∀ lam : ℝ, 0 < lam → lam ^ 2 ≤ (U.X k).firstMinimumSq x.1 → ‖Formalism.L2.PjFree.toC (evR Xo c f (U.un k x))‖ ≤ (d.pd : ℝ) ^ (fdeg E * r * n) * ((∑ m ∈ P.support, ‖σ (P.coeff m)‖) * (Real.pi * Real.exp 1 * t * (Formalism.L2.Pj.DF Dw a : ℕ)) ^ (((Formalism.L2.Pj.DF Dw a : ℕ) : ℝ) / 2) * Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * (fdeg E * r : ℕ) * n) * (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^ (fdeg E * r * n)) := by
  first | exact @GlobalTheory.Dict.ShortPoint.norm_evR_le | exact GlobalTheory.Dict.ShortPoint.norm_evR_le | (intros; apply GlobalTheory.Dict.ShortPoint.norm_evR_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaGeneratorsNoCommonZeroOfChartIndependence
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory

theorem noCommonZero_of_chartIndep : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → NoCommonZeroSt := by
  intro hC D T h j hj w hn _hlast hM _hα σ hσ k x hx

  obtain ⟨-, -, -, -, hr1, hxi, hDF, -, hc, -⟩ := _root_.GlobalTheory.SupDict.record_dictionary D T h j hj w

  obtain ⟨st, hnab⟩ := h.nabPin j hj

  obtain ⟨f, hf, hne⟩ := _root_.GlobalTheory.ThetaNoZero.exists_thGen_rdU_ne_zero hC _ _ _ _ _ _ σ D.R.r (Formalism.L2.PjFree.Unf.ofPj (T.U j σ))
    ((Formalism.L2.PjFree.goodEmb_iff σ).mpr hσ) ((Formalism.L2.PjFree.isUnf_ofPj _).mpr (h.unf j hj σ hσ)) hr1
    (2 * xiR D) (by linarith) (fun k τ => hc σ hσ k τ) (wtA w) w.n (dom_wtA w) hn (by omega) st (T.nab j)
    hnab k x hx
  exact ⟨f, hf, by rwa [Formalism.L2.PjFree.rdU_ofPj] at hne⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRuleValuePeriods
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem thetaRule_value_periods : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (xf : (U.X k).dom) (W : UnfAt U k xf) (Wu : UnitAt W) (nab : NabV Xo c), IsNab Xo c nab → FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k xf) → ∀ (n : ℕ) (x x2 : Fin n → Dw.La), (∀ b, x2 b ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ b, x2 b - x b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ f : Rul Xo c, IsThRule Xo c nab x P f → Differentiable ℂ Wu.θ ∧ toC (evR Xo c f (U.un k xf)) = ((l.M : ℂ)⁻¹) ^ P.totalDegree * I2.polyDeriv (MvPolynomial.map σ P) (letDir W.e) (fun z => ∏ b, fock Wu.Hm ((l.M : ℤ) ^ 2) (((l.M : ℂ) ^ 2)⁻¹ • W.Pm (W.F.t (W.ik k) (x2 b))) (fun w => Wu.θ ((l.M : ℂ) • w)) (z b)) 0 := by
  intro hci E _ _ _ H Dw l Xo c _ σ r U k xf W Wu nab hnab hft n x x2 h2 hx a P hP f hf
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨Φ, hof, hHm, -, -, hrd, -, hlin, hlev⟩ := GlobalTheory.T.exists_analytic_frame_of_unit_uniformisation_frame E H Dw l Xo c σ r U k xf W Wu
  have hv := GlobalTheory.T.thetaRuleValue_testRing_eq_thetaValue hci E H Dw l Xo c nab hnab a n x P hP f hf (CAt σ) (U.un k xf) hft
  refine ⟨((GlobalTheory.AnVal.reading_existsUnique_isTh _ _ _ _ _ Φ.toAnFr 1 _).2.1 _ hrd).1, ?_⟩
  have key := _root_.GlobalTheory.AnVal.thValAt_eq_polyDeriv_fock hci E H Dw l Xo c (U.un k xf) W.g _ W.e Φ
    (W.Pm.comp (W.F.t (W.ik k)).toAddMonoidHom) (fun a => by rw [hof.2.1]; exact ⟨_, rfl⟩) hlin hlev nab hnab Wu.θ hrd
    n x x2 h2 hx a P hP _ hv
  rw [hHm] at key
  exact key

end GlobalTheory.AnVal
end

