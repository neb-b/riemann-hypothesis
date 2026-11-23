module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LeviFormWeightMetricOrthonormalDiagonal
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.SumNormSqWPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.BoundOfIneqs
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

namespace GlobalTheory.ProperFromMinimum

theorem bound_of_ineqs {K K' c i δ S n p : ℝ} {a : ℕ} (hδ : 0 < δ) (hac : (a : ℝ) * c < i)
    (hS : 0 ≤ S) (h1 : Real.exp (-(2 * c * p)) ≤ K * S) (h2 : n ≤ K' * Real.exp (-(2 * i * p)))
    (h3 : δ * S ^ a ≤ n) : p ≤ K ^ a * K' / δ / (2 * (i - a * c)) := by
  have hK : 0 ≤ K := by
    by_contra hK
    have : K * S ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt (not_le.1 hK)) hS
    linarith [Real.exp_pos (-(2 * c * p))]
  have hKa : 0 ≤ K ^ a := pow_nonneg hK a
  have e1 : Real.exp (-(2 * c * p)) ^ a ≤ K ^ a * S ^ a := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Real.exp_pos _).le h1 a
  have e2 : δ * Real.exp (-(2 * c * p)) ^ a ≤ K ^ a * K' * Real.exp (-(2 * i * p)) := by
    calc δ * Real.exp (-(2 * c * p)) ^ a ≤ δ * (K ^ a * S ^ a) :=
          mul_le_mul_of_nonneg_left e1 hδ.le
      _ = K ^ a * (δ * S ^ a) := by ring
      _ ≤ K ^ a * (K' * Real.exp (-(2 * i * p))) := mul_le_mul_of_nonneg_left (h3.trans h2) hKa
      _ = _ := by ring
  have e3 : Real.exp (-(2 * c * p)) ^ a =
      Real.exp (2 * (i - a * c) * p) * Real.exp (-(2 * i * p)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [e3, ← mul_assoc] at e2
  have e4 : δ * Real.exp (2 * (i - a * c) * p) ≤ K ^ a * K' :=
    le_of_mul_le_mul_right e2 (Real.exp_pos _)
  have e5 : 2 * (i - a * c) * p ≤ Real.exp (2 * (i - a * c) * p) := by
    linarith [Real.add_one_le_exp (2 * (i - a * c) * p)]
  have hd : 0 < 2 * (i - a * c) := by linarith
  rw [le_div_iff₀ hd, le_div_iff₀ hδ]
  nlinarith [mul_le_mul_of_nonneg_left e5 hδ.le]

theorem exists_compact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (L eW : Wt X.Ψ r) (N a : ℕ) (w : Fin N → Frame X.Ψ r → ℂ) (et : Frame X.Ψ r → ℂ) (c i : ℝ) (ph : Frame X.Ψ r → ℝ), (∃ ca ε0 : ℝ, 0 < ca ∧ 0 < ε0 ∧ ∀ x ∈ X.dom, X.la1 x < ε0 → ca / X.la1 x ^ 2 ≤ ph x) → InterpolationModelInequalities X L eW w et c i ph → (a : ℝ) * c < i → ∀ δ : ℝ, 0 < δ → ∃ C : Set (Frame X.Ψ r), IsCompact C ∧ C ⊆ X.dom ∧ ∀ x ∈ X.dom, δ * (∑ k, X.pnorm L (w k) x ^ 2) ^ a ≤ X.pnorm eW et x ^ 2 → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ C := by
  intro E _ _ _ r X L eW N a w et c i ph hph hI hac δ hδ
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hsub : Subsingleton (Frame X.Ψ 0) := inferInstance
    refine ⟨X.dom, (Set.subsingleton_of_subsingleton).finite.isCompact, subset_rfl, ?_⟩
    intro x hx _
    refine ⟨1, X.Γ.one_mem, x, fun τ => ⟨(hx τ).1, fun a => a.elim0⟩, ?_⟩
    rwa [Subsingleton.elim (lact 1 (rmul x x)) x]
  obtain ⟨ca, ε0, hca, hε0, hlow⟩ := hph
  obtain ⟨⟨K, hK⟩, K', hK'⟩ := hI
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = max (K ^ a * K' / δ / (2 * (i - a * c))) 1 := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; exact lt_of_lt_of_le one_pos (le_max_right _ _)
  have hε : 0 < min ε0 (Real.sqrt (ca / B)) := lt_min hε0 (Real.sqrt_pos.2 (div_pos hca hB0))
  obtain ⟨C, hC, hCd, hmeet⟩ := reductionTheory_holds (E := E) r X _ hε
  refine ⟨C, hC, hCd, fun x hx h3 => hmeet x hx ?_⟩
  by_cases hsmall : X.la1 x < ε0
  · refine (min_le_right _ _).trans ?_
    have hpos : 0 < X.la1 x := la1_pos_of_mem_dom X hr hx
    have hp : ph x ≤ B := by
      rw [hB]
      exact (bound_of_ineqs hδ hac (Finset.sum_nonneg fun _ _ => sq_nonneg _) (hK x hx) (hK' x hx)
        h3).trans (le_max_left _ _)
    have h4 : ca / X.la1 x ^ 2 ≤ B := (hlow x hx hsmall).trans hp
    rw [div_le_iff₀ (by positivity)] at h4
    apply Real.sqrt_le_iff.2
    refine ⟨hpos.le, ?_⟩
    rw [div_le_iff₀ hB0]
    linarith
  · exact (min_le_left _ _).trans (not_lt.1 hsmall)

end GlobalTheory.ProperFromMinimum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsBoundOrthonormalFrameMahlerStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.exists_bound_orthonormal_frame_mahler : (∀ (r : ℕ) (X : Data E r) (ε : ℝ), 0 < ε → ∃ R : ℝ, ∀ x, IsOrth X x → ε ≤ X.la1 x → ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∀ τ a b, ‖lact γ x τ a b‖ ≤ R) := by
  first | exact @GlobalTheory.OrthFrameMahler.exists_bound_orthonormal_frame | exact GlobalTheory.OrthFrameMahler.exists_bound_orthonormal_frame | (intros; apply GlobalTheory.OrthFrameMahler.exists_bound_orthonormal_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LeviFormWeightMetricOrthonormalDiagonalStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.leviForm_weightMetric_orthonormal_diagonal : (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r), IsOrth X x → ∀ ξ : Fin (nd X) → ℂ, leviM X (phla X la) x 0 ξ = ∑ e : Ent X, sgn X.p0 e.2.1.1 * sgn X.p0 e.2.1.2 * ((la e.1 e.2.1.2 : ℝ) - (la e.1 e.2.1.1 : ℝ)) * ‖ξ (Fintype.equivFin (Ent X) e)‖ ^ 2) := by
  first | exact @GlobalTheory.LeviZero.leviZero | exact GlobalTheory.LeviZero.leviZero | (intros; apply GlobalTheory.LeviZero.leviZero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OfRealRpowNegLe
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Up.DivMetricPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
theorem _root_.GlobalTheory.Up.DivMetricPf.exp_neg_phla {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom)
    (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) :
    Real.exp (-_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.phla X la x) = X.nfac la x ^ 2 := by
  have hpos := _root_.ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.nfac_pos X hx la
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.phla
  rw [show -(-2 * Real.log (X.nfac la x)) = Real.log (X.nfac la x) + Real.log (X.nfac la x) by
    ring, Real.exp_add, Real.exp_log hpos]
  ring


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
theorem _root_.GlobalTheory.Up.DivMetricPf.pnorm_rmul (hN : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacRmulStatement (E := E)) {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    {P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hP : X.IsSec la P) {x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom)
    (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r) :
    X.pnorm la P (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) = X.pnorm la P x :=
  _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.pnorm_rmul X la P hP.2.1 x hx b hb


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
theorem _root_.GlobalTheory.Up.DivMetricPf.pnorm_lact (hN : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement (E := E)) {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    {P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hP : X.IsSec la P) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.pnorm la P (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) = X.pnorm la P x := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement at hN
  change ‖P (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x)‖ * X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) = ‖P x‖ * X.nfac la x
  rw [hP.2.2 γ hγ x hx, norm_mul, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.chi_norm X la hγ, one_mul, hN r X la γ hγ x hx]


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
theorem _root_.GlobalTheory.Up.DivMetricPf.measurable_cut {f : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℝ}
    (hf : ContinuousOn f X.dom) :
    Measurable (X.dom.indicator fun x => ENNReal.ofReal (f x)) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact ContinuousOn.measurable_piecewise (ENNReal.continuous_ofReal.comp_continuousOn hf)
    continuousOn_const (FourierCoefficientDomain.isOpen_dom X).measurableSet


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
theorem _root_.GlobalTheory.Up.DivMetricPf.exists_sum_le {N : ℕ} {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    {P : Fin N → _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hP : ∀ k, X.IsBddSec la (P k)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ X.dom, ∑ k, X.pnorm la (P k) x ^ 2 ≤ C := by
  choose C hC using fun k => (hP k).2
  refine ⟨1 + ∑ k, C k ^ 2, by positivity, fun x hx => ?_⟩
  have hle : ∀ k, X.pnorm la (P k) x ^ 2 ≤ C k ^ 2 := by
    intro k
    have h0 : 0 ≤ X.pnorm la (P k) x := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
      exact mul_nonneg (norm_nonneg _) (_root_.ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.nfac_pos X hx la).le
    exact pow_le_pow_left₀ h0 (hC k x hx) 2
  calc ∑ k, X.pnorm la (P k) x ^ 2 ≤ ∑ k, C k ^ 2 := Finset.sum_le_sum fun k _ => hle k
    _ ≤ 1 + ∑ k, C k ^ 2 := by linarith


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
theorem _root_.GlobalTheory.Up.DivMetricPf.ofReal_rpow_neg_le {a C t : ℝ} (hC : 0 < C) (h : a ≤ C) (ht : 0 ≤ t) :
    ENNReal.ofReal (C ^ (-t)) ≤ ENNReal.ofReal a ^ (-t) := by
  rcases lt_or_ge 0 a with ha | ha
  · rw [ENNReal.ofReal_rpow_of_pos ha]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos ha h (by linarith))
  · rw [ENNReal.ofReal_of_nonpos ha]
    rcases ht.lt_or_eq with ht | ht
    · rw [ENNReal.zero_rpow_of_neg (by linarith)]
      exact le_top
    · subst ht
      simp

variable (Xa : ArchInM X) (Fl : FlatM X Xa) (n : ℕ)

end GlobalTheory.Up.DivMetricPf
end

