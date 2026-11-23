module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.RealLieGroupChartsSmooth
section
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep
open scoped ContDiff

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem chart_ex (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    ∃ y : GA E a, ∀ f : GA E a → ℂ, chart f g x = f y := by
  refine ⟨g * infGL E a (show IsUnit (Matrix.of x) from hx).unit, fun f => ?_⟩
  exact chart_val f g (show IsUnit (Matrix.of x) from hx).unit

private theorem chart_at_one (u : GA E a → ℂ) (g : GA E a) : chart u g (oneL E a) = u g := by
  simpa using chart_val u g 1

private theorem ev_inv : ∀ᶠ x in nhds (oneL E a), x ∈ invSet E a :=
  isOpen_invSet.mem_nhds (show oneL E a ∈ invSet E a from isUnit_one)

private theorem comp_mem {h : ℂ → ℂ} {S : Set ℂ} (hh : ContDiffOn ℝ ∞ h S) {f : GA E a → ℂ} (hf : f ∈ Sm E a)
    (hS : ∀ g, f g ∈ S) : (fun g => h (f g)) ∈ Sm E a := by
  intro g
  refine (hh.comp (hf g) fun x hx => ?_).congr fun x hx => ?_
  · obtain ⟨y, hy⟩ := chart_ex g hx
    rw [hy]; exact hS y
  · obtain ⟨y, hy⟩ := chart_ex g hx
    simp only [Function.comp, hy]

private theorem comp_lie {h : ℂ → ℂ} {f : GA E a → ℂ} (hf : f ∈ Sm E a) (g : GA E a) {d : ℂ}
    (hd : HasDerivAt h d (f g)) (X : Lie E a) : lieD X (fun g => h (f g)) g = d * lieD X f g := by
  have e : chart (fun g => h (f g)) g =ᶠ[nhds (oneL E a)] h ∘ chart f g := by
    filter_upwards [ev_inv] with x hx
    obtain ⟨y, hy⟩ := chart_ex g hx
    simp only [Function.comp, hy]
  rw [← chart_at_one f g] at hd
  have h2 := (hd.hasFDerivAt.restrictScalars ℝ).comp (oneL E a) (differentiableAt_chart hf g).hasFDerivAt
  rw [lieD, lieD, e.fderiv_eq, h2.fderiv]
  simp [mul_comm]

private theorem prodSm_mem {f f' : GA E a → ℂ} (h : f ∈ Sm E a) (h' : f' ∈ Sm E a) :
    (fun g => f g * f' g) ∈ Sm E a := by
  intro g
  refine ((h g).mul (h' g)).congr fun x hx => ?_
  obtain ⟨y, hy⟩ := chart_ex g hx
  simp only [hy]

private theorem prod_lie {f f' : GA E a → ℂ} (h : f ∈ Sm E a) (h' : f' ∈ Sm E a) (g : GA E a) (X : Lie E a) :
    lieD X (fun g => f g * f' g) g = f g * lieD X f' g + lieD X f g * f' g := by
  have e : chart (fun g => f g * f' g) g =ᶠ[nhds (oneL E a)] chart f g * chart f' g := by
    filter_upwards [ev_inv] with x hx
    obtain ⟨y, hy⟩ := chart_ex g hx
    simp only [Pi.mul_apply, hy]
  rw [lieD, lieD, lieD, e.fderiv_eq, fderiv_mul (differentiableAt_chart h g) (differentiableAt_chart h' g),
    chart_at_one, chart_at_one]
  simp [mul_comm]

end

theorem UpperTheory.realLieGroup_charts_smooth :
    MeanSm := by
  intro E _ _ _ a ha L hL
  have hT := (UpperTheory.hermitian_space_geometric_estimate E a ha L hL).1
  have hS := UpperTheory.hermitian_chart_scalar_invariance E a ha L hL
  have mem : ∀ P ∈ poly E a, mean L P ∈ meanAlg L := fun P hP => Algebra.subset_adjoin ⟨P, hP, rfl⟩
  obtain ⟨θ, hθ, hθX⟩ := hS 1 (one_mem _)
  have hv : ∀ g, θ.1 g = (Th L g : ℝ) := fun g => by rw [hθ]; exact (hT g).2
  have hpos : ∀ g, 0 < Th L g := fun g => lt_of_lt_of_le one_pos (hT g).1
  have hne : ∀ g, θ.1 g ≠ 0 := fun g => by
    rw [hv]; exact_mod_cast (hpos g).ne'
  have hsl : ∀ g, θ.1 g ∈ Complex.slitPlane := fun g => by
    rw [hv]; exact Complex.ofReal_mem_slitPlane.2 (hpos g)
  refine ⟨fun P hP => ?_, ?_⟩
  · obtain ⟨φ, hφ, hφX⟩ := hS P hP
    have hi : (fun g => (θ.1 g)⁻¹) ∈ Sm E a :=
      comp_mem (S := {0}ᶜ) ((contDiffOn_inv ℂ).restrict_scalars ℝ) θ.2 hne
    refine ⟨⟨fun g => φ.1 g * (θ.1 g)⁻¹, prodSm_mem φ.2 hi⟩, ?_, fun X => ?_⟩
    · funext g
      simp only [mean, hφ, hv, div_eq_mul_inv]
    · obtain ⟨Q, hQ, eQ⟩ := hφX X
      obtain ⟨R, hR, eR⟩ := hθX X
      have e : (lie E a X ⟨fun g => φ.1 g * (θ.1 g)⁻¹, prodSm_mem φ.2 hi⟩).1 = mean L Q - mean L P * mean L R := by
        funext g
        have e1 : lieD X φ.1 g = gsum L (pg Q) g := congrFun eQ g
        have e2 : lieD X θ.1 g = gsum L (pg R) g := congrFun eR g
        rw [GlobalTheory.CuspRep.lie_apply]
        change lieD X (fun g => φ.1 g * (fun g => (θ.1 g)⁻¹) g) g = _
        rw [prod_lie φ.2 hi, comp_lie θ.2 g (hasDerivAt_inv (hne g)), e1, e2]
        simp only [Pi.sub_apply, Pi.mul_apply, mean, ← hv, hφ]
        have := hne g
        field_simp
        ring
      rw [e]
      exact sub_mem (mem Q hQ) (mul_mem (mem P hP) (mem R hR))
  · have hl : (fun g => Complex.log (θ.1 g)) ∈ Sm E a :=
      comp_mem (S := Complex.slitPlane)
        (fun z hz => ((Complex.contDiffAt_log hz).restrict_scalars ℝ).contDiffWithinAt) θ.2 hsl
    refine ⟨⟨_, hl⟩, fun g => ?_, fun X => ?_⟩
    · change Complex.log (θ.1 g) = _
      rw [hv, fn, Complex.ofReal_log (hpos g).le]
    · obtain ⟨R, hR, eR⟩ := hθX X
      have e : (lie E a X ⟨_, hl⟩).1 = mean L R := by
        funext g
        have e2 : lieD X θ.1 g = gsum L (pg R) g := congrFun eR g
        rw [GlobalTheory.CuspRep.lie_apply]
        change lieD X (fun g => Complex.log (θ.1 g)) g = _
        rw [comp_lie θ.2 g (Complex.hasDerivAt_log (hsl g)), e2, mean, hv, div_eq_inv_mul]
      rw [e]
      exact mem R hR
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.TraceFormPosDefOfTotallyReal
section
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

private theorem trF_sub_smul {E : Type} [Field E] [NumberField E] {a : ℕ}
    (X W : Matrix (Fin a) (Fin a) (Cinf E)) (r : ℝ) :
    trF (X - r • (1 : Matrix (Fin a) (Fin a) (Cinf E))) W = trF X W - r * trF 1 W := by
  simp [trF, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]

private theorem qf_pos {E : Type} [Field E] [NumberField E] {a : ℕ} {w : Fin a → Cinf E} (hw : w ≠ 0) :
    0 < qf w := by
  rw [← norm_euc_sq]
  exact pow_pos (norm_pos_iff.2 fun h => hw (euc.map_eq_zero_iff.1 h)) 2

theorem UpperTheory.traceForm_posDef_of_totallyReal :
    Grad := by
  intro E _ _ _ a ha L hL
  obtain ⟨cA, hcA, hA⟩ := UpperTheory.hermitian_point_embedding_injective E a ha L hL
  obtain ⟨CB, hB⟩ := UpperTheory.hermitian_space_gradient_estimate E a ha L hL
  obtain ⟨c, C, N, hc, hS⟩ := UpperTheory.convex_separation_positive_distance E a ha L hL
  obtain ⟨CF, hF⟩ := UpperTheory.hermitian_space_log_estimate E a ha L hL
  have hT := (UpperTheory.hermitian_space_geometric_estimate E a ha L hL).1
  have hq := (UpperTheory.V.Lit.Geo.qhtFacts E a).1
  set δ : ℝ := cA / 2 * c ^ 2 / (|CB| + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  refine ⟨(cA / 2) ^ 2, max (Real.log 2) (|CF| * (1 + Real.log (C / δ ^ N)) + 1), by positivity, fun g hg => ?_⟩
  have h2 : 2 ≤ Th L g :=
    (Real.log_le_log_iff two_pos (one_pos.trans_le (hT g).1)).1 ((le_max_left _ _).trans hg)
  obtain ⟨w, hw, hwC, hwv⟩ := hS g
  have hw0 := qf_pos hw
  have hq1 : 1 ≤ qht g := hq g
  have hsm : qf w ≤ δ := by
    by_contra hn
    have h1 : qht g ≤ C / δ ^ N := by
      rw [le_div_iff₀ (by positivity)]
      exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ0.le (not_le.1 hn).le N) (by linarith)).trans hwC
    have h3 := Real.log_le_log (by linarith) h1
    have h4 := Real.log_nonneg hq1
    have h5 := (le_max_right _ _).trans hg
    have h6 : CF * (1 + Real.log (qht g)) ≤ |CF| * (1 + Real.log (C / δ ^ N)) :=
      mul_le_mul (le_abs_self _) (by linarith) (by linarith) (abs_nonneg _)
    linarith [hF g]
  obtain ⟨r1, r2, -⟩ := UpperTheory.traceForm_cauchy_schwarz_cmDatum E a w
  have hb := hB g w c hc hwv
  have ha' := hA g h2
  have hb' : CB * qf w ^ 2 / c ^ 2 ≤ cA / 2 * qf w := by
    rw [div_le_iff₀ (by positivity)]
    have h7 : qf w * (|CB| + 1) ≤ cA / 2 * c ^ 2 := (le_div_iff₀ (by positivity)).1 hsm
    have h8 : CB ≤ |CB| + 1 := (le_abs_self _).trans (by linarith)
    calc CB * qf w ^ 2 ≤ (|CB| + 1) * qf w ^ 2 := mul_le_mul_of_nonneg_right h8 (by positivity)
      _ = qf w * (|CB| + 1) * qf w := by ring
      _ ≤ cA / 2 * c ^ 2 * qf w := mul_le_mul_of_nonneg_right h7 hw0.le
      _ = _ := by ring
  have he : trF (dev L g).1 (vecMulVec w (star w)) =
      trF (mom L g).1 (vecMulVec w (star w)) - ell E a (toL (mom L g).1) * qf w := by
    rw [← r1, ← trF_sub_smul]
    rfl
  have h9 : cA / 2 * qf w ≤ -trF (dev L g).1 (vecMulVec w (star w)) := by
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right ha' hw0.le]
  have h10 := pow_le_pow_left₀ (by positivity) h9 2
  rw [neg_sq, mul_pow] at h10
  exact le_of_mul_le_mul_right (h10.trans (r2 (dev L g))) (by positivity)
end

