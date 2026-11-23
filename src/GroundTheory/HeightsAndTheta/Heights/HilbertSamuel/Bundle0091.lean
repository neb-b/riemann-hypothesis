module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0049
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0087
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0068
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0078
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0070
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0076
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0082
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0072

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComplexGramMetricChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Filter Asymptotics
open scoped ComplexConjugate Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace ComplexGramMetricChange

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem eval_smul_of_homog {ι : Type*} {F : MvPolynomial ι ℂ} {n : ℕ} (hF : F.IsHomogeneous n) (c : ℂ)
    (z : ι → ℂ) : eval (c • z) F = c ^ n * eval z F := by
  classical
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hdeg : s.degree = n := by
    by_contra h
    exact (mem_support_iff.mp hs) (hF.coeff_eq_zero h)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have h : s.degree = ∑ i ∈ s.support, s i := rfl
  rw [← hdeg, h]
  ring

theorem resPt_ne_zero (d : HSMDatum D Ω κ) (y : d.R.X) : resPt d y ≠ 0 := by
  obtain ⟨i, hi⟩ := (d.R.mem y y (d.R.mem_U y)).1 ()
  intro h
  exact hi (congrFun h ⟨(), i⟩)

theorem pair_smul (m : ConeMetric ℂ (Ix κ)) {z : Ix κ → ℂ} (hz : z ≠ 0) {c : ℂ} (hc : c ≠ 0) {n : ℕ}
    {b b' : MvPolynomial (Ix κ) ℚ} (hb : b.IsHomogeneous n) (hb' : b'.IsHomogeneous n) :
    eval (c • z) (map (algebraMap ℚ ℂ) b) * conj (eval (c • z) (map (algebraMap ℚ ℂ) b')) *
        ((Real.exp (-(n : ℝ) * (2 * Real.log (m.ρ (c • z)))) : ℝ) : ℂ) = pairVal m n b b' z := by
  have hρ : 0 < m.ρ z := m.pos z hz
  have hcn : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hexp : Real.exp (-(n : ℝ) * (2 * Real.log (m.ρ (c • z)))) = ((‖c‖ * m.ρ z) ^ (2 * n))⁻¹ := by
    rw [m.smul, show -(n : ℝ) * (2 * Real.log (‖c‖ * m.ρ z)) = -(((2 * n : ℕ) : ℝ) * Real.log (‖c‖ * m.ρ z)) by
      push_cast; ring, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (mul_pos hcn hρ)]
  have hcc : c ^ n * conj c ^ n = ((‖c‖ : ℝ) : ℂ) ^ (2 * n) := by
    rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_mul]
    push_cast
    ring
  rw [hexp, eval_smul_of_homog (hb.map _), eval_smul_of_homog (hb'.map _), pairVal]
  have hρc : ((m.ρ z : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ.ne'
  have hcc' : ((‖c‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hcn.ne'
  simp only [map_mul, map_pow]
  push_cast
  field_simp
  linear_combination (eval z (map (algebraMap ℚ ℂ) b) * conj (eval z (map (algebraMap ℚ ℂ) b')) *
    ((m.ρ z : ℝ) : ℂ) ^ (2 * n)) * hcc

theorem continuous_diff {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}
    (W₁ W₀ : Weight L) : Continuous (Weight.diff W₁ W₀) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hx : x ∈ (A.chart (chartIdx A x)).source := Classical.choose_spec (A.cover x)
  set j := chartIdx A x
  have hT : (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source = (A.chart j).target :=
    Set.inter_eq_left.2 fun y hy => (A.chart j).map_target hy
  have h₁ := (W₁.smooth j j).continuousOn
  have h₀ := (W₀.smooth j j).continuousOn
  rw [hT] at h₁ h₀
  have hg := (h₁.sub h₀).continuousAt ((A.chart j).open_target.mem_nhds ((A.chart j).map_source hx))
  refine (hg.comp ((A.chart j).continuousAt hx)).congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hx] with y hy
  simp only [Pi.sub_apply, Function.comp_apply, (A.chart j).left_inv hy]
  exact (Weight.diff_eq W₁ W₀ j hy).symm

theorem eventually_pow_le (C ε : ℝ) (hε : 0 < ε) (hD : 1 ≤ D) :
    ∀ᶠ n : ℕ in atTop, C * ((n : ℝ) + 1) ^ (D - 1) ≤ ε * (n : ℝ) ^ D := by
  obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  obtain ⟨N, hN⟩ := exists_nat_ge (|C| * 2 ^ D' / ε)
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast le_of_max_le_left hn
  have hkey : |C| * 2 ^ D' ≤ ε * n := by
    have := hN.trans hnN
    rw [div_le_iff₀ hε] at this
    linarith
  calc C * ((n : ℝ) + 1) ^ D' ≤ |C| * ((n : ℝ) + 1) ^ D' :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (2 * (n : ℝ)) ^ D' :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) _) (abs_nonneg C)
    _ = (|C| * 2 ^ D') * (n : ℝ) ^ D' := by rw [mul_pow]; ring
    _ ≤ (ε * n) * (n : ℝ) ^ D' := mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = ε * (n : ℝ) ^ (D' + 1) := by ring

end ComplexGramMetricChange


open ComplexGramMetricChange in
theorem ComplexGramMetricChange.proof (hMC : MetricChange.Statement) (hPB : ProjectionBounds.Statement)
    (hFS : PullFSExtension.Statement) (hPair : ResolutionMetricPair.Statement)
    (hInd : ResolutionFormsIndependent.Statement) (hDeg : ResolutionDegree.Statement) :
    ComplexGramMetricChange.Statement := by
  classical
  intro D Ω _ _ κ _ d m₁ P0₁ hs hc hle hp e he
  obtain ⟨A, L, W₀, W₁, dV, σ, -, hW₀, hW₁, hμ, hsec, hval, hdens⟩ := hPair D Ω κ d m₁ P0₁ hs hle hp
  choose c hc0 hσ hφ₀ hφ₁ using hval

  have hex : ∀ n, ∃ q : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n q.2 := fun n => by
    obtain ⟨b, hb⟩ := exists_isSecBasis d.x n
    exact ⟨⟨_, b⟩, hb⟩
  let p : ℕ → (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ) := fun n => (hex n).choose
  have hp' : ∀ n, IsSecBasis d.x n (p n).2 := fun n => (hex n).choose_spec
  have hhom : ∀ n k, ((p n).2 k).IsHomogeneous n := fun n k => by
    obtain ⟨f, hf, hfe⟩ := (hp' n).1 k
    rw [hfe]
    exact hf.map _
  let v : ∀ n, Fin (p n).1 → Fin A.n → d.R.X → ℂ := fun n k => σ n ((p n).2 k)
  have hli : ∀ n, LinearIndependent ℂ (v n) := by
    intro n
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : g = 0 := hInd D Ω κ d n _ (p n).2 (hp' n) g fun y => by
      have h := congrFun (congrFun hg (chartIdx A y)) y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v,
        hσ y n _ (hhom n _), eval_smul_of_homog ((hhom n _).map _)] at h
      have hcn : c y ^ n ≠ 0 := pow_ne_zero _ (hc0 y)
      apply (mul_right_inj' hcn).1
      rw [mul_zero, Finset.mul_sum, ← h]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    intro k
    rw [h0]
    rfl
  let V : ℕ → Submodule ℂ (Fin A.n → d.R.X → ℂ) := fun n => Submodule.span ℂ (Set.range (v n))
  have : ∀ n, FiniteDimensional ℂ (V n) := fun n => FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hrank : ∀ n, Module.finrank ℂ (V n) = (p n).1 := fun n =>
    (finrank_span_eq_card (hli n)).trans (Fintype.card_fin _)
  let eB : ∀ n, Module.Basis (Fin (Module.finrank ℂ (V n))) ℂ (V n) := fun n =>
    (Module.Basis.span (hli n)).reindex (finCongr (hrank n).symm)

  have hgram : ∀ (W : Weight L) (m : ConeMetric ℂ (Ix κ)),
      (∀ y, W.φ (chartIdx A y) y = 2 * Real.log (m.ρ (c y • resPt d y))) → ∀ n,
      chiGram W dV n (fun a => ((eB n a : V n) : Fin A.n → d.R.X → ℂ)) =
        -(1 / 2) * Real.log (Matrix.det (fun k l => ∫ y, pairVal m n ((p n).2 k) ((p n).2 l) (resPt d y) ∂d.dV :
          Matrix (Fin (p n).1) (Fin (p n).1) ℂ)).re := by
    intro W m hW n
    have he : (fun a => ((eB n a : V n) : Fin A.n → d.R.X → ℂ)) = fun a => v n ((finCongr (hrank n).symm).symm a) := by
      funext a
      simp only [eB, Module.Basis.reindex_apply, Module.Basis.span_apply]
    have hsub : gram W dV n (fun a => v n ((finCongr (hrank n).symm).symm a)) =
        (gram W dV n (v n)).submatrix (finCongr (hrank n).symm).symm (finCongr (hrank n).symm).symm := by
      ext a a'
      rfl
    have hg : gram W dV n (v n) = fun k l => ∫ y, pairVal m n ((p n).2 k) ((p n).2 l) (resPt d y) ∂d.dV := by
      ext k l
      simp only [gram, Matrix.of_apply, hμ, v]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only
      rw [hσ y n _ (hhom n k), hσ y n _ (hhom n l), hW y]
      exact pair_smul m (resPt_ne_zero d y) (hc0 y) (hhom n k) (hhom n l)
    rw [chiGram, he, hsub, Matrix.det_submatrix_equiv_self, hg]
  have hC₀ : ∀ n, resCChi d n = -(1 / 2) * Real.log (Matrix.det (fun k l =>
      ∫ y, pairVal d.m n ((p n).2 k) ((p n).2 l) (resPt d y) ∂d.dV :
        Matrix (Fin (p n).1) (Fin (p n).1) ℂ)).re := fun n => by
    rw [resCChi, dite_eq_left (hex n)]
    rfl
  have hC₁ : ∀ n, resCChi (d.withMetric m₁ P0₁ hs hc hle hp) n = -(1 / 2) * Real.log (Matrix.det (fun k l =>
      ∫ y, pairVal m₁ n ((p n).2 k) ((p n).2 l) (resPt d y) ∂d.dV :
        Matrix (Fin (p n).1) (Fin (p n).1) ℂ)).re := fun n => by
    rw [resCChi, dite_eq_left (show ∃ q : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ),
      IsSecBasis (d.withMetric m₁ P0₁ hs hc hle hp).x n q.2 from hex n)]
    rfl

  obtain ⟨mF, hsF, hcF, hpF, hpullF⟩ := hFS D Ω κ d.x e he
  obtain ⟨-, -, C, -, -, -, -, hr, -⟩ := hPB D Ω κ (d.withMetric mF ⊥ hsF hcF bot_le hpF) e he hpullF
  have hr' : ∀ n : ℕ, |(Module.finrank ℤ (sec ℤ d.x n) : ℝ) - (projDeg d.x e : ℝ) * (n : ℝ) ^ D /
      (D.factorial : ℝ)| ≤ C * ((n : ℝ) + 1) ^ (D - 1) := hr
  have hsmooth : ∀ t : ℝ, IsSmoothMetric (interp d.m m₁ t) := fun t => by
    show ContDiffOn ℝ _ (fun z => d.m.ρ z ^ (1 - t) * m₁.ρ z ^ t) _
    exact (d.smooth.rpow_const_of_ne fun z hz => (d.m.pos z hz).ne').mul
      (hs.rpow_const_of_ne fun z hz => (m₁.pos z hz).ne')
  have hInt : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∫ y, bergmanDens (W₀.lerp W₁ t) dV y ∂dV.μ = (projDeg d.x e : ℝ) / (D.factorial : ℝ) := by
    intro t ht
    have h := hdens t ht (fun _ => 1) continuous_const
    simp only [one_mul] at h
    rw [h, hDeg D Ω κ d e _ he (hsmooth t)]
  have hdim : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (∫ y, bergmanDens (W₀.lerp W₁ t) dV y ∂dV.μ - ε) * (n : ℝ) ^ D ≤ Module.finrank ℂ (V n) := by
    intro t ht ε hε
    rw [hInt t ht]
    filter_upwards [eventually_pow_le C ε hε d.one_le] with n hn
    rw [hrank n, (hp' n).card_eq]
    have h := (abs_le.1 (hr' n)).1
    have e1 : ((projDeg d.x e : ℝ) / (D.factorial : ℝ) - ε) * (n : ℝ) ^ D =
        (projDeg d.x e : ℝ) * (n : ℝ) ^ D / (D.factorial : ℝ) - ε * (n : ℝ) ^ D := by ring
    rw [e1]
    linarith
  have hVle : ∀ n, V n ≤ L.sections n := fun n =>
    Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hsec n _ (hhom n k))
  have hM := hMC A L W₀ W₁ dV hW₀ hW₁ V hVle hdim eB

  have hdiff : ∀ y, Weight.diff W₁ W₀ y = 2 * logRatio d.m m₁ (resPt d y) := by
    intro y
    have hz := resPt_ne_zero d y
    have hcn : ‖c y‖ ≠ 0 := norm_ne_zero_iff.2 (hc0 y)
    rw [Weight.diff, hφ₁ y, hφ₀ y, logRatio, m₁.smul, d.m.smul, Real.log_mul hcn (m₁.pos _ hz).ne',
      Real.log_mul hcn (d.m.pos _ hz).ne', Real.log_div (m₁.pos _ hz).ne' (d.m.pos _ hz).ne']
    ring
  have hcont : Continuous fun y => logRatio d.m m₁ (resPt d y) := by
    have h : (fun y => logRatio d.m m₁ (resPt d y)) = fun y => Weight.diff W₁ W₀ y / 2 := by
      funext y
      rw [hdiff]
      ring
    rw [h]
    exact (continuous_diff W₁ W₀).div_const 2
  have hK : ∫ t in (0 : ℝ)..1, ∫ y, Weight.diff W₁ W₀ y * bergmanDens (W₀.lerp W₁ t) dV y ∂dV.μ =
      2 / (D.factorial : ℝ) * resMetricInt d m₁ := by
    rw [resMetricInt, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le zero_le_one] at ht
    simp only [hdiff]
    have h := hdens t ht _ hcont
    simp only [mul_assoc]
    rw [integral_const_mul, h]
    ring

  rw [isLittleO_iff]
  intro ε hε
  filter_upwards [hM ε hε] with n hn
  rw [hgram W₁ m₁ hφ₁ n, hgram W₀ d.m hφ₀ n, hK] at hn
  rw [hC₁ n, hC₀ n, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (D + 1))]
  have e2 : (n : ℝ) ^ (D + 1) / 2 * (2 / (D.factorial : ℝ) * resMetricInt d m₁) =
      (n : ℝ) ^ (D + 1) / (D.factorial : ℝ) * resMetricInt d m₁ := by ring
  rw [e2] at hn
  exact hn

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormDehomCharpoly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace FibreNormDehomCharpoly

theorem finiteDimensional_pullField (hR : PullRatiosAlgebraic.Statement) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω] {y : (Σ k, ι k) → Ω} {D : ℕ} {e : K → ℕ}
    {L : Fin (D + 1) → MRing ι} (hA : IsArithVar (mCoordIdeal y) (D + 1)) (hB : Birational y) (he : ∀ k, 1 ≤ e k)
    (hL : ∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e)
    (hz : ∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) :
    FiniteDimensional (pullField y L) Ω := by
  classical
  obtain ⟨_, ⟨_, _, hrel⟩, _, _⟩ := hA
  obtain ⟨c, hc⟩ := CoordArithOfFnField.nonzero_of_relevant y hrel
  have hrel' : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => ⟨c k, hc k⟩
  set P := pullField y L
  set S : Set Ω := {t | ∃ p q : Σ k, ι k, p.1 = q.1 ∧ t = y p / y q} with hS
  have hSf : S.Finite := (Set.finite_range fun pq : (Σ k, ι k) × (Σ k, ι k) => y pq.1 / y pq.2).subset
    (by rintro _ ⟨p, q, -, rfl⟩; exact ⟨(p, q), rfl⟩)
  have : Finite S := hSf.to_subtype
  have hSi : ∀ x ∈ S, IsIntegral P x := by
    rintro _ ⟨p, q, hpq, rfl⟩
    exact (hR K ι Ω y D e L hrel' he hL hz p q hpq).isIntegral
  have hfd : FiniteDimensional P (IntermediateField.adjoin P S) := IntermediateField.finiteDimensional_adjoin hSi
  have htop : IntermediateField.adjoin P S = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    have hx : x ∈ blockFnField y := (PullFormsGeneric.blockFnField_eq_top c hc hB).symm ▸ IntermediateField.mem_top
    have hle : blockFnField y ≤ (IntermediateField.adjoin P S).restrictScalars ℚ := by
      rw [blockFnField, IntermediateField.adjoin_le_iff]
      exact fun t ht => IntermediateField.subset_adjoin P S ht
    exact hle hx
  have hfd' : FiniteDimensional P (⊤ : IntermediateField P Ω) := htop ▸ hfd
  exact (IntermediateField.topEquiv (F := P) (E := Ω)).toLinearEquiv.finiteDimensional

end FibreNormDehomCharpoly


open FibreNormDehomCharpoly in
theorem FibreNormDehomCharpoly.proof (hG : PullFormsGeneric.Statement) (hR : PullRatiosAlgebraic.Statement)
    (hI : PullSectionIntegral.Statement) (hC : DehomCharpolyForms.Statement) : FibreNormDehomCharpoly.Statement := by
  intro K _ ι _ Ω _ _ y D e L q hA hB he hL hz
  classical
  have hfin : FiniteDimensional (pullField y L) Ω := finiteDimensional_pullField hR hA hB he hL hz
  refine ⟨hfin, fun τ s hs j hj => ?_⟩
  set l : Fin (D + 1) → Ω := fun i => aeval y (L i) with hl
  have hgen : ∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0 :=
    hG K ι Ω y D e L hA hB he hL hz
  have hne : ∀ k, l k ≠ 0 := fun k h0 =>
    X_ne_zero (R := ℚ) k (hgen 1 (X k) (isHomogeneous_X ℚ k) (by rw [aeval_X]; exact h0))
  have hint : ∀ k, s / l j ^ (q * τ) * (l j / l k) ^ (q * τ) ∈
      integralClosure (Algebra.adjoin ℚ (Set.range fun i => l i / l k)) Ω := by
    intro k
    have h : s / l j ^ (q * τ) * (l j / l k) ^ (q * τ) = s / l k ^ (q * τ) := by
      rw [div_pow, div_mul_div_comm, mul_comm (l j ^ (q * τ)), mul_div_mul_right _ _ (pow_ne_zero _ (hne j))]
    rw [h]
    exact hI K ι Ω y D e L q hA hB he hL hz τ s hs k (hne k)
  obtain ⟨c, hc0, hch, hcp, hcn⟩ := hC Ω D l (pullField y L) rfl hgen j (q * τ) (s / l j ^ (q * τ)) hint
  exact ⟨c, ⟨hj, hfin, hc0, hch, hcp⟩, fun hs0 => hcn (div_ne_zero hs0 (pow_ne_zero _ hj))⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormPrimeBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem FibreNormPrimeBound.block_ne_zero {y : (Σ k, ι k) → Ω} {e : K → ℕ} {f : MRing ι}
    (he : ∀ k, 1 ≤ e k) (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f e) (hy : aeval y f ≠ 0) (k : K) : ∃ i, y ⟨k, i⟩ ≠ 0 := by
  by_contra h
  push Not at h
  apply hy
  rw [aeval_def, eval₂_eq']
  refine Finset.sum_eq_zero fun m hm => ?_
  have hsum : ∑ i, m ⟨k, i⟩ ≠ 0 := by rw [hf m hm k]; exact (Nat.one_le_iff_ne_zero.mp (he k))
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ ⟨k, i⟩) ?_)
  rw [h i, zero_pow hi]


omit [Fintype K] in
theorem FibreNormPrimeBound.exists_chart (V : ValuationSubring Ω) {y : (Σ k, ι k) → Ω}
    (hblk : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) :
    ∃ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) ∧ ∀ q : Σ k, ι k, y q / y ⟨q.1, c q.1⟩ ∈ V := by
  classical
  have hmax : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 ∧ ∀ i', V.valuation (y ⟨k, i'⟩) ≤ V.valuation (y ⟨k, i⟩) := by
    intro k
    obtain ⟨i, hi, hm⟩ := Finset.exists_max_image (Finset.univ.filter fun i => y ⟨k, i⟩ ≠ 0)
      (fun i => V.valuation (y ⟨k, i⟩)) (by obtain ⟨i0, h0⟩ := hblk k; exact ⟨i0, by simp [h0]⟩)
    refine ⟨i, (Finset.mem_filter.mp hi).2, fun i' => ?_⟩
    by_cases h : y ⟨k, i'⟩ = 0
    · rw [h, map_zero]; exact zero_le
    · exact hm i' (by simp [h])
  choose c hc0 hcm using hmax
  refine ⟨c, hc0, fun ⟨k, i⟩ => ?_⟩
  have hv : V.valuation (y ⟨k, c k⟩) ≠ 0 := (Valuation.ne_zero_iff _).mpr (hc0 k)
  rw [← V.valuation_le_one_iff, div_eq_mul_inv, map_mul, map_inv₀]
  calc V.valuation (y ⟨k, i⟩) * (V.valuation (y ⟨k, c k⟩))⁻¹
      ≤ V.valuation (y ⟨k, c k⟩) * (V.valuation (y ⟨k, c k⟩))⁻¹ := mul_le_mul_left (hcm k i) _
    _ = 1 := mul_inv_cancel₀ hv

theorem FibreNormPrimeBound.mem_of_isIntegral (V : ValuationSubring Ω) {S : Subalgebra ℤ Ω} (hS : ∀ s ∈ S, s ∈ V)
    {u : Ω} (hu : IsIntegral S u) : u ∈ V := by
  let φ : S →+* V :=
    { toFun := fun r => ⟨r, hS r r.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  obtain ⟨f, hf, hfu⟩ := hu
  have hint : IsIntegral V u := ⟨f.map φ, hf.map φ, by rw [Polynomial.eval₂_map]; exact hfu⟩
  obtain ⟨v, hv⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp hint
  exact hv ▸ v.2

theorem FibreNormPrimeBound.proof (hG : PullFormsGeneric.Statement) (hN : NormFormGaussBound.Statement)
    (hC : ChartPrimePowerInverse.Statement) : FibreNormPrimeBound.Statement := by
  classical
  intro K _ ι _ Ω _ _ y D e L q hAr hBir he hhomL hnz p hp
  have hM : ∀ j, ∃ M : ℕ, aeval y (L j) ≠ 0 → ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      (p : Ω) ^ M * (∏ k, y ⟨k, c k⟩ ^ e k) / aeval y (L j) ∈
        Subring.closure (Set.range (fun q : Σ k, ι k => y q / y ⟨q.1, c q.1⟩) ∪
          Set.range (fun i => aeval y (L i) / aeval y (L j)) ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹}) := by
    intro j
    by_cases hj : aeval y (L j) = 0
    · exact ⟨0, fun h => (h hj).elim⟩
    · obtain ⟨M, hM⟩ := hC K ι Ω y D e L hhomL hnz p hp j hj
      exact ⟨M, fun _ => hM⟩
  choose M hM using hM
  refine ⟨Module.finrank (pullField y L) Ω * (∑ j, M j) * q, ?_⟩
  intro τ s hs j c hc μ
  obtain ⟨hLj, hfd, -, hhom, hcp⟩ := hc
  have := hfd
  set S := ∑ j, M j with hS
  set Sset : Set Ω := {z | ∃ i k, z = aeval y (L i) / aeval y (L k)} ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹}
  have key : ∀ V : ValuationSubring Ω, Sset ⊆ V.toSubring →
      (p : Ω) ^ (S * (q * τ)) * (s / aeval y (L j) ^ (q * τ)) ∈ V := by
    intro V hSV
    obtain ⟨c, hc0, hcV⟩ :=
      FibreNormPrimeBound.exists_chart V (FibreNormPrimeBound.block_ne_zero he (hhomL j) hLj)
    set Z := ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * ((q * e k : ℕ) : ℤ))) with hZ
    set Y := ∏ k, y ⟨k, c k⟩ ^ e k with hY
    have hu : s * Z ∈ V := by
      refine FibreNormPrimeBound.mem_of_isIntegral V (S := chartRingZ y c) ?_ (hs c hc0)
      intro t ht
      rw [chartRingZ, Algebra.adjoin_int] at ht
      refine (Subring.closure_le (t := V.toSubring)).mpr ?_ ht
      rintro _ ⟨q', rfl⟩
      exact hcV q'
    have hw : (p : Ω) ^ M j * Y / aeval y (L j) ∈ V := by
      refine (Subring.closure_le (t := V.toSubring)).mpr ?_ (hM j hLj c hc0)
      rintro z ((⟨q', rfl⟩ | ⟨i, rfl⟩) | hz)
      · exact hcV q'
      · exact hSV (Or.inl ⟨i, j, rfl⟩)
      · exact hSV (Or.inr hz)
    have hpV : (p : Ω) ∈ V := natCast_mem V p
    obtain ⟨r, hr⟩ : ∃ r, S = M j + r :=
      ⟨S - M j, (Nat.add_sub_cancel' (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))).symm⟩
    have hZY : Z * Y ^ (q * τ) = 1 := by
      rw [hZ, hY, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun k _ => ?_
      rw [← pow_mul, ← zpow_natCast (y _) (e k * (q * τ)), ← zpow_add₀ (hc0 k)]
      have h0 : -((τ : ℤ) * ((q * e k : ℕ) : ℤ)) + ((e k * (q * τ) : ℕ) : ℤ) = 0 := by push_cast; ring
      rw [h0, zpow_zero]
    have heq : (p : Ω) ^ (S * (q * τ)) * (s / aeval y (L j) ^ (q * τ)) =
        (s * Z) * ((p : Ω) ^ r) ^ (q * τ) * ((p : Ω) ^ M j * Y / aeval y (L j)) ^ (q * τ) := by
      rw [hr]
      calc (p : Ω) ^ ((M j + r) * (q * τ)) * (s / aeval y (L j) ^ (q * τ))
          = s * (Z * Y ^ (q * τ)) * (p : Ω) ^ ((M j + r) * (q * τ)) / aeval y (L j) ^ (q * τ) := by
            rw [hZY]; ring
        _ = _ := by ring
    rw [heq]
    exact mul_mem (mul_mem hu (pow_mem (pow_mem hpV _) _)) (pow_mem hw _)
  have hint : (p : Ω) ^ (S * (q * τ)) * (s / aeval y (L j) ^ (q * τ)) ∈
      integralClosure (Subring.closure Sset) Ω := by
    have hmem : (p : Ω) ^ (S * (q * τ)) * (s / aeval y (L j) ^ (q * τ)) ∈
        (integralClosure (Subring.closure Sset) Ω).toSubring := by
      rw [← iInf_valuationSubring_superset]
      exact Subring.mem_iInf.mpr fun V => key V.1 V.2
    exact hmem
  have h := hN Ω D (fun i => aeval y (L i)) (pullField y L) rfl
    (hG K ι Ω y D e L hAr hBir he hhomL hnz) p hp j (S * (q * τ))
    (Module.finrank (pullField y L) Ω * (q * τ)) (s / aeval y (L j) ^ (q * τ)) c
    (hhom _ le_rfl) hcp hint μ
  have hn : Module.finrank (pullField y L) Ω * (S * (q * τ)) =
      Module.finrank (pullField y L) Ω * S * q * τ := by ring
  rw [hn] at h
  exact h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullRatiosAlgebraic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

theorem PullRatiosAlgebraic.proof (h₁ : PullConeNull.Statement) (h₂ : PullConeDegree.Statement)
    (h₃ : PullGradedAlgebraic.Statement) : PullRatiosAlgebraic.Statement := by
  intro K _ ι _ Ω _ _ y D e L hy he hL hz
  obtain ⟨N, hN⟩ := h₁ K ι Ω y D L hz
  exact h₃ K ι Ω y D e L (fun k => e k + N * Fintype.card (ι k)) hy he hL
    (fun d g hg hd => h₂ K ι Ω y D e L N hy hL hN d g hg hd)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

