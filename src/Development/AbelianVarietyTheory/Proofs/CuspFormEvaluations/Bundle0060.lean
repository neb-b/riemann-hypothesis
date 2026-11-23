module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SumNormSqOrbit
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PoinSumMul
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SquareIntegrableSingularMetricOrderOne
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.QuotientNoPositiveMaxOffCommonZeros

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AeExistsFlatDatumLinearCombination
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.GenericFlat

theorem ae_exists_flat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (K : Type) [Field K] [Countable K] (σ : K →+* ℂ), RelIn σ X Xa → ∀ᵐ t : Fin (nd X + 1) × Fin Xa.N → ℂ, ∃ Fl : FlatM X Xa, (∀ x, Fl.w0 x = ∑ j, t (0, j) * Xa.w j x) ∧ ∀ k x, Fl.s k x = ∑ j, t (k.succ, j) * Xa.w j x := by
  intro E _ _ _ r X Xa K _ _ σ hR
  filter_upwards [_root_.GlobalTheory.ae_eval₂_ne_zero_of_countable K σ (Fin (nd X + 1) × Fin Xa.N), GlobalTheory.T.ae_coefficients_common_zeros_simple E r X Xa] with t hgen hsimple

  have hdom : ∃ C : ℝ, ∀ x ∈ X.dom, ∑ k, ‖Xa.w k x‖ ^ 2 ≤ C * ∑ i, ‖∑ j, t (i, j) * Xa.w j x‖ ^ 2 :=
    GlobalTheory.T.theta_forms_bounded_by_generic_combinations E r X Xa K σ t hgen hR
  have hlow : ∃ ε c0 : ℝ, 0 < ε ∧ 0 < c0 ∧ ∀ x ∈ X.dom,
      ∑ i : Fin (nd X), ‖∑ j, t (i.succ, j) * Xa.w j x‖ ^ 2 < ε * ‖∑ j, t (0, j) * Xa.w j x‖ ^ 2 →
        c0 ≤ ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 :=
    GlobalTheory.T.theta_forms_not_small_where_combinations_vanish E r X Xa K σ t hgen hR
  have hsim : ∀ x ∈ X.dom, ∑ j, t (0, j) * Xa.w j x ≠ 0 →
      (∀ k : Fin (nd X), ∑ j, t (k.succ, j) * Xa.w j x = 0) →
      (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
        (∑ j, t (k.succ, j) * Xa.w j (cpt X x z)) / ∑ j, t (0, j) * Xa.w j (cpt X x z) : V (nd X))) 0).det ≠ 0 :=
    hsimple
  obtain ⟨C, hC⟩ := hdom

  have hzero : ∀ x ∈ X.dom, (∀ k : Fin (nd X), ∑ j, t (k.succ, j) * Xa.w j x = 0) →
      (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
        (∑ j, t (k.succ, j) * Xa.w j (cpt X x z)) / ∑ j, t (0, j) * Xa.w j (cpt X x z) : V (nd X))) 0).det ≠ 0 := by
    intro x hx hs
    have hs0 : ∑ j, t (0, j) * Xa.w j x ≠ 0 := by
      intro h0
      obtain ⟨k, hk⟩ := Xa.w_nz x hx
      have hsum : ∑ i, ‖∑ j, t (i, j) * Xa.w j x‖ ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨m, rfl⟩
        · simp [h0]
        · simp [hs m]
      have hle := hC x hx
      rw [hsum, mul_zero] at hle
      have hk' : ‖Xa.w k x‖ ^ 2 ≤ ∑ k, ‖Xa.w k x‖ ^ 2 :=
        Finset.single_le_sum (f := fun k => ‖Xa.w k x‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)
      have h2 : ‖Xa.w k x‖ ^ 2 = 0 := le_antisymm (hk'.trans hle) (by positivity)
      exact hk (by simpa using h2)
    exact hsim x hx hs0 hs
  obtain ⟨Fl, h0, hs⟩ := GlobalTheory.FlatPoints.exists_flat GlobalTheory.ClosedDiscontinuity.firstMinimum_invariant_continuous_pos_on_frames
    GlobalTheory.FlagMahler.mahler_compactness r X Xa (fun i j => t (i, j)) ⟨C, hC⟩ hlow hzero
  exact ⟨Fl, fun x => congrFun h0 x, fun k x => congrFun (congrFun hs k) x⟩

end GlobalTheory.GenericFlat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoverMulShortThetaSeriesIndepOfFramedLiftStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_mul_shortThetaSeries_indep_of_framed_lift : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), @ToroidalLevelCompatibility E _ _ _ H Dw → d.IsLev → d.l₂.A = l.A → ∀ [StarRing (𝓞 E)], IsNab d.Xo₂ d.c₂ d.nab₂ → (∃ ph ψ x₀, d.PhiPin ph ψ x₀ ∧ d.PsiTie ψ) → ∀ (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) d.c₂.F), P ∈ HHa Dw.mult n d.c₂.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (x0 : Fin n → Dw.La) (β : d.c₂.F), ∀ (r' : d.Xo₂.X ⟶ Xo.X) (m' : SABMap d.Xo₂.univ.t Xo.univ.t r'), DeltaDat.EtaOK { d with r := r', m := m' } → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k], (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) → ∀ (y : FrPt Xo c k) (y₂ y₂' : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y → FrOver { d with r := r', m := m' } y₂' y → ∀ v v', ShortValAt d.Xo₂ d.c₂ d.nab₂ (d.w x0) Λ β N P y₂ v → ShortValAt d.Xo₂ d.c₂ d.nab₂ (d.w x0) Λ β N P y₂' v' → evR d.Xo₂ d.c₂ d.cδ y₂ * v = evR d.Xo₂ d.c₂ d.cδ y₂' * v' := by
  first | exact @GlobalTheory.ShortLiftInvariance.cover_product_indep_of_lift | exact GlobalTheory.ShortLiftInvariance.cover_product_indep_of_lift | (intros; apply GlobalTheory.ShortLiftInvariance.cover_product_indep_of_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DivisionOrderOne
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.DivFreeWeight

open ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra GlobalTheory.Up.DivCorePf

theorem division_order_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r), (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) + bb < m ∧ ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, m * leviRh X x0 z ξ ≤ leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ) → (∀ P, X.IsBddSec (G + (nd X + 1) • Xa.L) P → P ∈ X.SS (G + (nd X + 1) • Xa.L)) → (∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f ∈ X.SS (G + (nd X + 1) • Xa.L), ∃ c : Fin K → ℂ, ∀ x ∈ X.dom, f x = ∑ i, c i * g i x) → ∀ f, X.IsBddSec (G + (nd X + 1) • Xa.L) f → (∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm (G + (nd X + 1) • Xa.L) f x ^ 2 ≤ C * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (nd X + 1)) → (∀ j, f (Fl.xs j) = 0) → ∃ h : Fin (nd X) → Frame X.Ψ r → ℂ, (∀ k, X.IsBddSec (G + nd X • Xa.L) (h k)) ∧ ∀ x ∈ X.dom, f x = ∑ k, Fl.s k x * h k x := by
  intro E _ _ _ r X Xa Fl G ⟨bb, m, hbb, hbm, hmar⟩ hcusp ⟨K, gs, hgs⟩ f hf hfC hvan
  have h2 := Xa.n_ge
  have hPD : PropDisc X := GlobalTheory.ClosedDiscontinuity.propDisc_closed r X
  obtain ⟨-, -, -, hPo, hOn⟩ := GlobalTheory.PoincareClosed.unfold_poincare_onto (E := E)
  have hExt := GlobalTheory.FrameMeasureClosed.extF_holds (E := E)
  obtain ⟨x0, ho⟩ : ∃ x0, IsOrth X x0 := by
    choose P hP hG using X.signature
    exact ⟨fun τ => P τ, fun τ => hG τ⟩
  obtain ⟨FF, hFF⟩ := fundSet_holds r X x0 ho hPD
  have hbb0 : 0 ≤ bb := le_trans (by positivity) hbb.le
  have hbm' : bb ≤ m := by
    have : 0 ≤ bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) := by positivity
    linarith
  have hs : ∀ k, X.IsSec Xa.L (Fl.s k) := fun k => (Fl.s_van k).1.1.1
  have hIn := _root_.GlobalTheory.FreeWeightInFF.inFF_order_one E r X Xa Fl G x0 ho FF hFF f hf.1 hfC hvan
  obtain ⟨hMT, hLT, hET⟩ := _root_.GlobalTheory.FreeDivMetric.freeDivMetric E r X Xa Fl G (nd X + 1) (by omega)
  obtain ⟨hMn, hLn, -⟩ := _root_.GlobalTheory.FreeDivMetric.freeDivMetric E r X Xa Fl G (nd X) (by omega)
  obtain ⟨⟨k0, z0, hz0, hz0'⟩, hLev⟩ := _root_.GlobalTheory.Shares.divLevi_freeWeight E r X Xa Fl G (nd X + 1) (by omega) x0 ho
  obtain ⟨F, P, hF, hFI, hP, hPF, hpo⟩ := hOn r X x0 ho hPD _ _
    (fun x => phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) +
      (((nd X + 1 : ℕ) : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2))
    (fun z => Fl.s k0 (cpt X x0 z)) bb m hMT hLT hbb hbm (OntoB.hol_comp X x0 (hs k0).1)
    ⟨z0, hz0, hz0'⟩ (hLev k0).1 (fun z hz hz' => hET _ hz ⟨k0, hz'⟩)
    (fun z hz hz' ξ => (hmar x0 ho z hz ξ).trans ((hLev k0).2 z hz hz' ξ)) hcusp FF hFF
    ⟨K, gs, fun f hf _ => hgs f hf⟩ _ (hcusp _ hf) hIn
  obtain ⟨H, hH, hFH⟩ := GlobalTheory.T.one_division_upstairs_free_weight E r X Xa Fl G x0 ho bb
    (fun z hz ξ => (mul_le_mul_of_nonneg_right hbm'
      (OntoB.levi_rh_nonneg RhGradFStatement_holds ho hz ξ)).trans (hmar x0 ho z hz ξ))
    ⟨k0, z0, hz0, hz0'⟩ F hF hFI
  choose Q hQ hQH using fun k => exists_extension hExt ho hLn hbb0 (hH k).1 (hH k).2
  have hPQ := fun k => hPo r X x0 ho hPD _ _ bb hMn hLn hbb (H k) (Q k) (hH k).1 (hH k).2 (hQ k) (hQH k)
  have hwt : G + (nd X + 1) • Xa.L = G + nd X • Xa.L + Xa.L := by
    rw [succ_nsmul, add_assoc]
  have hsum : ∀ y ∈ X.dom, P y = ∑ k, Fl.s k y * Q k y := by
    intro y hy
    refine sub_eq_zero.1 (bigCellStatement_holds r X x0 ho (G + (nd X + 1) • Xa.L)
      (fun y => P y - ∑ k, Fl.s k y * Q k y) ⟨?_, fun x hx b hb => ?_⟩ (fun z hz => ?_) y hy)
    · exact hP.1.sub (DifferentiableOn.fun_sum fun k _ => (hs k).1.mul (hQ k).1)
    · beta_reduce
      rw [mul_sub, hP.2 x hx b hb, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [(hs k).2.1 x hx b hb, (hQ k).2 x hx b hb, hwt, bchar_add X hb _ Xa.L]
      ring
    · rw [hPF z hz, hFH z hz, sub_eq_zero]
      exact Finset.sum_congr rfl fun k _ => by rw [hQH k z hz]
  refine ⟨fun k => poin X (G + nd X • Xa.L) (Q k), fun k => (hPQ k).2.1, fun x hx => ?_⟩
  rw [← hpo x hx, hwt]
  exact poin_sum_mul _ (fun k _ => hs k) hsum hx fun k _ => (hPQ k).1 x hx

end GlobalTheory.DivFreeWeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumBoundAtHalfSupremumCuspForm
section
noncomputable section

namespace GlobalTheory.RunIn

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

theorem firstMin_at_halfMax : ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ f ∈ T.C j w, ∀ (k : (T.U j σ).Comp), ∀ z0 ∈ ((T.U j σ).X k).dom, (∀ x ∈ ((T.U j σ).X k).dom, ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) x ≤ 2 * ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) z0) → 0 < ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) z0 → 0 < ((T.U j σ).X k).firstMinimumSq z0 ∧ Real.log (1 / ((T.U j σ).X k).firstMinimumSq z0) ≤ 80 * large₂.sc.L := by
  intro D T hL hG large₂ j hj w hP hL2 hr σ hσ f hf k z0 hz0 hmax hpos

  have hr1 : 1 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega

  have hSS : ∀ Q ∈ Formalism.L2.Pj.holSub (T.U j σ).X (laU (T.U j σ) (wtA w) w.n), ∀ c,
      Q c ∈ ((T.U j σ).X c).SS (laU (T.U j σ) (wtA w) w.n c) := by
    intro Q hQ
    unfold Formalism.L2.Pj.holSub at hQ
    induction hQ using Submodule.span_induction with
    | mem x hx => intro c; exact hx c
    | zero =>
      intro c
      exact ⟨ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_zero _ _,
        fun ξ _ x _ => ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_zero _ _ _ _ _⟩
    | add x y _ _ hx hy =>
      intro c
      obtain ⟨hx1, hx2⟩ := hx c
      obtain ⟨hy1, hy2⟩ := hy c
      refine ⟨ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_add _ hx1 hy1, fun ξ hξ x' hx' => ?_⟩
      rw [Pi.add_apply, ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_add _ hx1 hy1 hξ hx', hx2 ξ hξ x' hx',
        hy2 ξ hξ x' hx', add_zero]
    | smul a x _ hx =>
      intro c
      obtain ⟨hx1, hx2⟩ := hx c
      refine ⟨ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_smul _ a hx1, fun ξ hξ x' hx' => ?_⟩
      rw [Pi.smul_apply, ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_smul, hx2 ξ hξ x' hx', mul_zero]
  have hcusp : (rdU (T.U j σ)) f ∈ Formalism.L2.Pj.holSub (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) := by
    unfold Formalism.L2.Pj.Core.C at hf
    exact ((Formalism.L2.Pj.mem_cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n f).1 hf).2 σ hσ
  have hPk := hSS _ hcusp k
  obtain ⟨e, M, wg, hM1, hMlog, hwg, _hwglog, hfwlog, hk⟩ :=
    _root_.GlobalTheory.CuspDataBounds.cusp_data_bounds D T hL hG large₂ j hj w hP hL2 hr σ hσ
  obtain ⟨hspread, hflow, _hla, hNA, _hNC, _hg, hk0⟩ := hk k

  have hmb := ReciprocityTheory.ChartRestriction.G.FD.maxBound_holds D.R.r (e k).toX (laU (T.U j σ) (wtA w) w.n k)
    ((rdU (T.U j σ)) f k) M wg hPk (by linarith) hspread hwg hflow z0 hz0 hmax hpos
  have hk0pos : 0 < (e k).k0 := (e k).minWeight_pos
  have hk0le : (e k).k0 ≤ 2 := (e k).k0_le
  have hNApos : (0 : ℝ) < (e k).NA := by exact_mod_cast (e k).NA_pos
  have hMpos : 0 < M := by linarith
  have hfw : (0 : ℝ) < (fdeg D.host.E : ℝ) * wg + 2 := by positivity
  have hε : 0 < ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.epStar
    apply lt_min one_pos
    apply div_pos Real.pi_pos
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    positivity

  have hc : ∀ τ : ((T.U j σ).X k).Ψ, ((T.U j σ).X k).c τ = (e k).k0 := by
    intro τ
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.c
    rw [(e k).ξ0_abs τ]
    ring

  have hbpos : 0 < (e k).k0 * ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 / ((e k).NA : ℝ) ^ 2 :=
    div_pos (mul_pos hk0pos hε) (pow_pos hNApos 2)
  have hlow : (e k).k0 * ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 / ((e k).NA : ℝ) ^ 2 ≤
      ((T.U j σ).X k).firstMinimumSq z0 := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.firstMinimumSq
    apply le_csInf
    · by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have h0 : ∀ v ∈ ((T.U j σ).X k).Λ, v = 0 := by
        intro v hv
        by_contra hv0
        have hin : (∑ τ, ((T.U j σ).X k).c τ * ((T.U j σ).X k).maj z0 τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)) ∈
            {t | ∃ v ∈ ((T.U j σ).X k).Λ, v ≠ 0 ∧
              t = ∑ τ, ((T.U j σ).X k).c τ * ((T.U j σ).X k).maj z0 τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)} :=
          ⟨v, hv, hv0, rfl⟩
        rw [hemp] at hin
        exact hin
      have hbot : Submodule.span D.host.E (((T.U j σ).X k).Λ : Set (Fin D.R.r → D.host.E)) = ⊥ :=
        Submodule.span_eq_bot.mpr h0
      rw [((T.U j σ).X k).Λ_span] at hbot
      have hmem : (Pi.single (⟨0, hr1⟩ : Fin D.R.r) (1 : D.host.E)) ∈
          (⊤ : Submodule D.host.E (Fin D.R.r → D.host.E)) := Submodule.mem_top
      rw [hbot, Submodule.mem_bot] at hmem
      have h01 := congrFun hmem ⟨0, hr1⟩
      simp at h01
    · rintro t ⟨v, hv, hv0, rfl⟩
      have hNAv : ((e k).NA : D.host.E) • v ∈ (e k).L' := (e k).NA_sub v hv
      have hNAv0 : ((e k).NA : D.host.E) • v ≠ 0 := by
        refine smul_ne_zero ?_ hv0
        exact_mod_cast (e k).NA_pos.ne'
      obtain ⟨τ0, hτ0⟩ := hmb _ hNAv hNAv0
      have hτ0' : ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 ≤
          ((T.U j σ).X k).maj z0 τ0 (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 (((e k).NA : D.host.E) • v)) := hτ0
      have hemb : ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 (((e k).NA : D.host.E) • v) =
          (Complex.ofReal ((e k).NA : ℝ)) • ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 v := by
        funext a
        simp [ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
      rw [hemb, ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags.maj_smul _ hz0 τ0 ((e k).NA : ℝ) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 v)] at hτ0'
      have hsum := Finset.single_le_sum
        (f := fun τ => ((T.U j σ).X k).c τ * ((T.U j σ).X k).maj z0 τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v))
        (fun τ _ => mul_nonneg (by rw [hc τ]; exact hk0pos.le)
          (ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds.maj_nonneg _ hz0 τ _)) (Finset.mem_univ τ0)
      simp only [hc τ0] at hsum
      have hstep : (e k).k0 * ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 / ((e k).NA : ℝ) ^ 2 ≤
          (e k).k0 * ((T.U j σ).X k).maj z0 τ0 (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 v) := by
        rw [mul_div_assoc]
        apply mul_le_mul_of_nonneg_left _ hk0pos.le
        rw [div_le_iff₀ (pow_pos hNApos 2)]
        linarith
      exact le_trans hstep hsum
  have hla1 : 0 < ((T.U j σ).X k).firstMinimumSq z0 := lt_of_lt_of_le hbpos hlow
  refine ⟨hla1, ?_⟩

  have h1 : Real.log (1 / ((T.U j σ).X k).firstMinimumSq z0) ≤
      Real.log (1 / ((e k).k0 * ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 / ((e k).NA : ℝ) ^ 2)) :=
    Real.log_le_log (one_div_pos.mpr hla1) (one_div_le_one_div_of_le hbpos hlow)
  have hlog2 : Real.log 2 ≤ large₂.sc.L := by
    have := Real.log_two_lt_d9
    linarith
  have hε' := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfLam1Row.neg_log_epStar M (fdeg D.host.E) wg (e k).k0 hMpos hfw hk0pos hk0le
  have hε2 : -Real.log (ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0) ≤ 36 * large₂.sc.L := by
    refine hε'.trans (max_le (by linarith) ?_)
    linarith
  have h1b : Real.log (1 / ((e k).k0 * ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 / ((e k).NA : ℝ) ^ 2)) =
      2 * Real.log ((e k).NA : ℝ) + Real.log (1 / (e k).k0) -
        Real.log (ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0) := by
    rw [one_div_div, Real.log_div (pow_pos hNApos 2).ne' (mul_pos hk0pos hε).ne', Real.log_pow,
      Real.log_mul hk0pos.ne' hε.ne', one_div, Real.log_inv]
    push_cast
    ring
  rw [h1b] at h1
  linarith

end GlobalTheory.RunIn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.QuotientNoPositiveMaxOffCommonZerosStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_no_positive_max_off_common_zeros : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (f : Frame X.Ψ r → ℂ), X.IsSec (Xa.Fp + Xa.T • Xa.L) f → let Φ : Frame X.Ψ r → ℝ := fun x => X.pnorm (Xa.Fp + Xa.T • Xa.L) f x ^ 2 * X.pnorm ((nd X + 4) • Xa.L - Xa.Fp) Xa.th2 x ^ 2 * X.pnorm (2 • Xa.L - Xa.de) Xa.th1 x ^ 2 * (X.pnorm ((Xa.i * (Xa.g0 / 2)) • Xa.de) Xa.et x ^ 2) ^ ((1 : ℝ) / (Xa.i * (Xa.g0 / 2) : ℕ)) / (∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) ^ ((Xa.T : ℝ) + nd X + 6 + 1 / 2); ∀ x0 ∈ X.dom, (∃ k, Fl.s k x0 ≠ 0) → 0 < Φ x0 → ¬ ∀ x ∈ X.dom, Φ x ≤ Φ x0 := by
  first | exact @GlobalTheory.QuotNoMax.no_pos_max | exact GlobalTheory.QuotNoMax.no_pos_max | (intros; apply GlobalTheory.QuotNoMax.no_pos_max <;> assumption)
end

