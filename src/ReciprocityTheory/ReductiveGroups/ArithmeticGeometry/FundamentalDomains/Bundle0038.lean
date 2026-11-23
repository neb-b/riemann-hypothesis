module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivityHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bNormHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0028

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaximumBoundField
section
namespace ReciprocityTheory.ChartRestriction.G.FD.flowTermNormDecay

open NumberField Complex Filter
open scoped ComplexConjugate Topology Real

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_eq_zero (X : DataX E r) {z0 : Frame X.Ψ r} (hz0 : z0 ∈ X.dom) {v : Fin r → E}
    (hv : v ∈ X.L') (hsmall : ∀ τ : X.Ψ, X.maj z0 τ (Data.emb τ.1 v) < 1) : herm X.Gm v v = 0 := by
  apply UnipotentCoefficientShift.eq_zero_of_conj_lt_one (X.L'_int v hv v hv)
  have key : ∀ τ : X.Ψ, ‖τ.1 (herm X.Gm v v)‖ < 1 := by
    intro τ
    have h := lt_of_le_of_lt
      (UnipotentCoefficientShift.norm_hermC_le_maj (hz := hz0) (τ := τ) (v := Data.emb τ.1 v)) (hsmall τ)
    have e : hermC τ.1 X.Gm (Data.emb τ.1 v) (Data.emb τ.1 v) = τ.1 (herm X.Gm v v) :=
      EmbeddingHermitianPairs.hermC_emb (x := v) (y := v) ..
    rwa [e] at h
  intro σ
  by_cases hσ : σ ∈ X.Ψ
  · exact key ⟨σ, hσ⟩
  · have hc : NumberField.ComplexEmbedding.conjugate σ ∈ X.Ψ := by
      by_contra h
      exact hσ ((X.cmType σ).2 h)
    have h := key ⟨_, hc⟩
    simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using h

theorem herm_nsmul (G : Matrix (Fin r) (Fin r) E) (n : ℕ) (v : Fin r → E) :
    herm G ((n : E) • v) ((n : E) • v) = (n : E) * n * herm G v v := by
  unfold herm cc
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem flowMat_nsmul (X : Data E r) (v : Fin r → E) (n : ℕ) (τ : X.Ψ) (s : ℂ) :
    X.flowMat ((n : E) • v) τ s = X.flowMat v τ ((n : ℂ) ^ 2 * s) := by
  ext a b
  simp only [Data.flowMat, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]
  simp only [mul_left_comm _ (n : ℂ), ← Finset.mul_sum]
  ring

theorem nfac_pos (X : Data E r) (la : Wt X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    0 < X.nfac la x := by
  unfold Data.nfac
  refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ?_ _
  have hne : ∀ j : Fin (r + 1), dmin X.Gm x τ j ≠ 0 := fun j h => by
    have := (hx τ).2 j
    rw [h, Complex.zero_re, mul_zero] at this
    exact lt_irrefl 0 this
  exact norm_pos_iff.mpr (div_ne_zero (hne _) (hne _))

theorem term_norm {ι : Type*} [Fintype ι] (c : ℂ) (ν : ι → ℝ) (ζ : ℂ) (n : ℕ) :
    ‖c * cexp (4 * π * I * ∑ τ, (ν τ : ℂ) * (ζ / (n : ℂ) ^ 2))‖ =
      ‖c‖ * Real.exp (-(4 * π * (∑ τ, ν τ) / (n : ℝ) ^ 2 * ζ.im)) := by
  have h : (4 * π * I * ∑ τ, (ν τ : ℂ) * (ζ / (n : ℂ) ^ 2)) =
      I * (((4 * π * (∑ τ, ν τ) / (n : ℝ) ^ 2 : ℝ)) : ℂ) * ζ := by
    rw [← Finset.sum_mul]
    push_cast
    ring
  rw [norm_mul, h, Complex.norm_exp]
  congr 2
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

theorem tendsto_zero (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : P ∈ X.SS la)
    {z0 : Frame X.Ψ r} (hz0 : z0 ∈ X.dom) {v : Fin r → E} (hv : v ∈ X.L')
    (hvv : herm X.Gm v v = 0) (hv0 : v ≠ 0)
    (hdom : ∀ ζ : ℂ, 0 ≤ ζ.im → X.flow v (fun _ => ζ) z0 ∈ X.dom) (G : ℂ → ℂ)
    (hG : ∀ ζ : ℂ, 0 < ζ.im → G ζ = P (X.flow v (fun _ => ζ) z0)) :
    Tendsto G (comap im atTop) (𝓝 0) := by
  classical
  set n := X.NC with hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast X.NC_pos.ne'
  set ξ : Fin r → E := (n : E) • v with hξdef
  have hξ : X.IsIso ξ := by
    refine ⟨X.NC_sub v hv, ?_, ?_⟩
    · rw [hξdef, herm_nsmul, hvv, mul_zero]
    · exact smul_ne_zero (by exact_mod_cast X.NC_pos.ne') hv0
  have hflow : ∀ ζ : ℂ, X.flow v (fun _ => ζ) z0 = X.flow ξ (fun _ => ζ / (n : ℂ) ^ 2) z0 := by
    intro ζ
    funext τ
    simp only [Data.flow]
    rw [flowMat_nsmul]
    congr 2
    field_simp
  set a : (X.Ψ → ℝ) → ℂ := fun ν => X.fj la ξ ν P z0 with ha
  have hexp : ∀ ζ : ℂ, 0 ≤ ζ.im → HasSum (fun ν : X.Ψ → ℝ =>
      a ν * cexp (4 * π * I * ∑ τ, (ν τ : ℂ) * (ζ / (n : ℂ) ^ 2))) (P (X.flow v (fun _ => ζ) z0)) := by
    intro ζ hζ
    rw [hflow]
    exact m3bExp_holds r X.toData la P hP.1.1 ξ hξ z0 hz0 (fun _ => ζ / (n : ℂ) ^ 2)
      (by rw [← hflow]; exact hdom ζ hζ)
  obtain ⟨C, hC⟩ := hP.1.2
  have hpos := (moderateCoefficientPositivity_holds r X.toData la P C 0 hP.1.1 (fun x hx => by simpa using hC x hx)).1
  have ha0 : a 0 = 0 := hP.2 ξ hξ z0 hz0
  have hS : ∀ ν, a ν ≠ 0 → 0 < ∑ τ, ν τ := by
    intro ν hν
    have hnn : ∀ τ, 0 ≤ ν τ := hpos ξ hξ ν z0 hz0 hν
    have hne : ν ≠ 0 := by
      rintro rfl
      exact hν ha0
    obtain ⟨τ, hτ⟩ : ∃ τ, ν τ ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (funext h)
    exact Finset.sum_pos' (fun τ _ => hnn τ) ⟨τ, Finset.mem_univ _, lt_of_le_of_ne (hnn τ) (Ne.symm hτ)⟩
  have hsum : Summable fun ν => ‖a ν‖ := by
    have h0 := (hexp 0 (le_refl _)).summable
    simp only [zero_div, mul_zero, Finset.sum_const_zero, Complex.exp_zero, mul_one] at h0
    exact summable_norm_iff.2 h0
  have hab : ∀ ν : X.Ψ → ℝ, Tendsto (fun ζ : ℂ =>
      a ν * cexp (4 * π * I * ∑ τ, (ν τ : ℂ) * (ζ / (n : ℂ) ^ 2))) (comap im atTop) (𝓝 0) := by
    intro ν
    by_cases hν : a ν = 0
    · simp only [hν, zero_mul]
      exact tendsto_const_nhds
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [term_norm]
    have hk : 0 < 4 * π * (∑ τ, ν τ) / (n : ℝ) ^ 2 := by
      have := hS ν hν
      have : (0 : ℝ) < n := by exact_mod_cast X.NC_pos
      positivity
    have h1 : Tendsto (fun ζ : ℂ => ζ.im) (comap im atTop) atTop := tendsto_comap
    have h2 := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (h1.const_mul_atTop hk))
    have h3 := h2.const_mul ‖a ν‖
    simpa using h3
  have hbound : ∀ᶠ ζ in comap im atTop, ∀ ν : X.Ψ → ℝ,
      ‖a ν * cexp (4 * π * I * ∑ τ, (ν τ : ℂ) * (ζ / (n : ℂ) ^ 2))‖ ≤ ‖a ν‖ := by
    have hev : ∀ᶠ ζ in comap im atTop, (0 : ℝ) ≤ ζ.im :=
      tendsto_comap.eventually (eventually_ge_atTop 0)
    filter_upwards [hev] with ζ hζ ν
    rw [term_norm]
    by_cases hν : a ν = 0
    · simp [hν]
    have hk : 0 ≤ 4 * π * (∑ τ, ν τ) / (n : ℝ) ^ 2 := by
      have := hS ν hν
      positivity
    refine mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.2 ?_)
    have := mul_nonneg hk hζ
    linarith
  have hT := tendsto_tsum_of_dominated_convergence hsum hab hbound
  simp only [tsum_zero] at hT
  refine hT.congr' ?_
  have hev : ∀ᶠ ζ in comap im atTop, (0 : ℝ) < ζ.im :=
    tendsto_comap.eventually (eventually_gt_atTop 0)
  filter_upwards [hev] with ζ hζ
  rw [hG ζ hζ]
  exact (hexp ζ hζ.le).tsum_eq

theorem spread_nonneg' (X : Data E r) (la : Wt X.Ψ r) (τ : X.Ψ) : 0 ≤ X.spread la τ := by
  rcases isEmpty_or_nonempty (Fin r) with h | ⟨⟨i⟩⟩
  · simp [Data.spread, Real.iSup_of_isEmpty, Real.iInf_of_isEmpty]
  · unfold Data.spread
    have h1 := ciInf_le (Set.finite_range fun i => (la τ i : ℝ)).bddBelow i
    have h2 := le_ciSup (Set.finite_range fun i => (la τ i : ℝ)).bddAbove i
    linarith

end ReciprocityTheory.ChartRestriction.G.FD.flowTermNormDecay
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealFlowPeriodsSpanEqTop
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Module
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem realFlowPeriods_span_eq_top {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) :
    Submodule.span ℝ {p : X.Ψ → ℝ | ∃ a : E, cc a = a ∧ IsIntegral ℤ a ∧
      p = fun τ => ((X.m * X.chiOrd la : ℕ) : ℝ) * (τ.1 a).re} = ⊤ := by
  classical
  have hNpos : (0 : ℝ) < ((X.m * X.chiOrd la : ℕ) : ℝ) := by
    have h1 : 0 < X.m := X.m_pos
    have h2 : 0 < X.chiOrd la := (X.χ_fin la).choose_spec.1
    exact_mod_cast Nat.mul_pos h1 h2
  have hD := integerApproximationCount_holds (E := E)
  unfold IntegerApproximationCount at hD
  obtain ⟨happrox, -⟩ := hD r X
  have hadd : ∀ x y : E, cc (x + y) = cc x + cc y := by
    intro x y
    unfold cc
    exact map_add _ x y
  rw [eq_top_iff]
  intro v _
  rw [← SetLike.mem_coe]
  apply (Submodule.closed_of_finiteDimensional _).closure_subset
  rw [Metric.mem_closure_iff]
  intro ε hε
  set N : ℝ := ((X.m * X.chiOrd la : ℕ) : ℝ) with hN
  set B : ℝ := 2 * (fdeg E : ℝ) ^ 2 * rdE E with hB
  set t : ℝ := (|B| + 1) / ε with ht
  have htpos : 0 < t := div_pos (by positivity) hε
  have hεt : ε * t = |B| + 1 := by
    rw [ht]
    field_simp
  obtain ⟨α, hα⟩ := happrox (fun τ => ((t * v τ : ℝ) : ℂ))
  set a : E := (α : E) + cc (α : E) with ha
  have hcca : cc a = a := by
    rw [ha, hadd, cc_cc, add_comm]
  have hinta : IsIntegral ℤ a := by
    have h0 : IsIntegral ℤ (α : E) := NumberField.RingOfIntegers.isIntegral_coe α
    exact h0.add (isIntegral_cc h0)
  have hre : ∀ τ : X.Ψ, (τ.1 a).re = 2 * (τ.1 (α : E)).re := by
    intro τ
    rw [ha, map_add (f := _), emb_cc, Complex.add_re, Complex.conj_re]
    ring
  refine ⟨(1 / (2 * N * t)) • (fun τ : X.Ψ => N * (τ.1 a).re), ?_, ?_⟩
  · rw [SetLike.mem_coe]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨a, hcca, hinta, rfl⟩
  · rw [dist_eq_norm]
    have hlt : ∀ τ : X.Ψ,
        ‖(v - (1 / (2 * N * t)) • (fun τ : X.Ψ => N * (τ.1 a).re)) τ‖ < ε := by
      intro τ
      have hval : (v - (1 / (2 * N * t)) • (fun τ : X.Ψ => N * (τ.1 a).re)) τ
          = (t * v τ - (τ.1 (α : E)).re) / t := by
        have hN0 : N ≠ 0 := hNpos.ne'
        have ht0 : t ≠ 0 := htpos.ne'
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hre]
        field_simp <;> ring
      rw [hval, Real.norm_eq_abs, abs_div, abs_of_pos htpos, div_lt_iff₀ htpos]
      have h1 : |t * v τ - (τ.1 (α : E)).re| ≤ ‖τ.1 (α : E) - ((t * v τ : ℝ) : ℂ)‖ := by
        have h := Complex.abs_re_le_norm (τ.1 (α : E) - ((t * v τ : ℝ) : ℂ))
        rw [Complex.sub_re, Complex.ofReal_re] at h
        rw [abs_sub_comm]
        exact h
      have h2 : ‖τ.1 (α : E) - ((t * v τ : ℝ) : ℂ)‖ ≤ B := hα τ
      linarith [le_abs_self B]
    exact (pi_norm_lt_iff hε).2 hlt

theorem spectralGap_holds : CuspFormGapCondition (E := E) := by
  classical
  unfold CuspFormGapCondition
  intro r X la P hP
  have hP' : X.IsBddSec la P ∧ ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, X.fj la ξ 0 P x = 0 := hP
  have hB : X.IsSec la P ∧ ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ C := hP'.1
  obtain ⟨C, hC⟩ := hB.2
  have hm3 := moderateCoefficientPositivity_holds (E := E)
  unfold ModerateCoefficientPositivity at hm3
  have hnn := (hm3 r X la P C 0 hB.1 (fun x hx => by simpa using hC x hx)).1
  have hspan := realFlowPeriods_span_eq_top X la
  obtain ⟨T, hTS, hTspan, hTli⟩ := exists_linearIndependent ℝ
    {p : X.Ψ → ℝ | ∃ a : E, cc a = a ∧ IsIntegral ℤ a ∧
      p = fun τ => ((X.m * X.chiOrd la : ℕ) : ℝ) * (τ.1 a).re}
  rw [hspan] at hTspan
  have hTfin : T.Finite := hTli.setFinite
  set M : ℝ := ∑ p ∈ hTfin.toFinset, ∑ σ, |p σ| with hM
  have hM0 : 0 ≤ M :=
    Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun σ _ => abs_nonneg (p σ)))
  have hcpos : (0 : ℝ) < 1 / (2 * M + 2) := div_pos one_pos (by linarith)
  refine ⟨1 / (2 * M + 2), hcpos, ?_⟩
  show P ∈ X.SS la ∧ ∀ ξ, X.IsIso ξ → ∀ ν : X.Ψ → ℝ, ∑ τ, ν τ ≤ 1 / (2 * M + 2) →
    ∀ x ∈ X.dom, X.fj la ξ ν P x = 0
  refine ⟨hP, ?_⟩
  intro ξ hξ ν hν x hx
  by_contra hne
  have hint : ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k := by
    by_contra hc
    apply hne
    rw [Data.fj, if_neg hc]
  have hpos : ∀ τ, 0 ≤ ν τ := hnn ξ hξ ν x hx hne
  have hsmall : ∀ τ, ν τ ≤ 1 / (2 * M + 2) := fun τ =>
    le_trans (Finset.single_le_sum (fun σ _ => hpos σ) (Finset.mem_univ τ)) hν
  have hzero : ∀ p ∈ T, ∑ σ, ν σ * p σ = 0 := by
    intro p hp
    obtain ⟨k, hk⟩ := hint p (AddSubgroup.subset_closure (hTS hp))
    have hpM : ∑ σ, |p σ| ≤ M :=
      Finset.single_le_sum (f := fun q : X.Ψ → ℝ => ∑ σ, |q σ|)
        (fun q _ => Finset.sum_nonneg (fun σ _ => abs_nonneg (q σ))) (hTfin.mem_toFinset.2 hp)
    have habs : |∑ σ, ν σ * p σ| ≤ 1 / (2 * M + 2) * M := by
      calc |∑ σ, ν σ * p σ| ≤ ∑ σ, |ν σ * p σ| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ σ, 1 / (2 * M + 2) * |p σ| := by
          apply Finset.sum_le_sum
          intro σ _
          rw [abs_mul, abs_of_nonneg (hpos σ)]
          exact mul_le_mul_of_nonneg_right (hsmall σ) (abs_nonneg _)
        _ = 1 / (2 * M + 2) * ∑ σ, |p σ| := by simp only [Finset.mul_sum]
        _ ≤ 1 / (2 * M + 2) * M := mul_le_mul_of_nonneg_left hpM hcpos.le
    have hfrac : 2 * (1 / (2 * M + 2) * M) < 1 := by
      rw [show 2 * (1 / (2 * M + 2) * M) = (2 * M) / (2 * M + 2) by ring,
        div_lt_one (by linarith)]
      linarith
    have hlt : |(k : ℝ)| < 1 := by
      rw [← hk, abs_mul, abs_two]
      linarith
    have hk0 : k = 0 := by
      have h := abs_lt.1 hlt
      have h1 : -1 < k := by exact_mod_cast h.1
      have h2 : k < 1 := by exact_mod_cast h.2
      omega
    rw [hk0, Int.cast_zero] at hk
    linarith
  let f : (X.Ψ → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun q => ∑ σ, ν σ * q σ
      map_add' := fun q q' => by
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c q => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun σ _ => by ring) }
  have hle : Submodule.span ℝ T ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    intro p hp
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact hzero p hp
  have hmem : ν ∈ Submodule.span ℝ T := by
    rw [hTspan]
    exact Submodule.mem_top
  have hsq : ∑ σ, ν σ * ν σ = 0 := LinearMap.mem_ker.1 (hle hmem)
  have hν0 : ν = 0 := by
    funext σ
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (ν i))).1 hsq σ
      (Finset.mem_univ σ)
    simpa using mul_self_eq_zero.1 h
  subst hν0
  exact hne (hP'.2 ξ hξ x hx)

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
section
namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem siegelSpaceAlgebra_holds : SiegelSpaceAlgebra (E := E) := BoundedSectionAlgebra.siegelSpaceAlgebra_of moderateCoefficientPositivity_holds coefficientConvolution_holds

end ReciprocityTheory.ChartRestriction.G.FD
end

