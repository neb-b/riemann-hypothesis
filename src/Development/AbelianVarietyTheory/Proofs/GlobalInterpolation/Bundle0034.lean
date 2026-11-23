module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LFunctionConjEqZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ZeroFreePrincipal
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0030
public import Formalism.LocalRingCardinality.DataRows
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.IsSemiChar
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerCoefficientNormLeOneIffJetsBoundedMeasureM
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionFamilyContinuationGrowth
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExceptionalDirichletZeroUniqueZeroFreeRegion
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.ExceptionalPair

theorem one_le_log {M : ℕ} (hM : 3 ≤ M) : 1 ≤ Real.log M := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_d9]

theorem log_mul_le {M : ℕ} (hM : 3 ≤ M) {a : ℝ} (ha : 0 < a) (ha3 : a ≤ 3) :
    Real.log (a * M) ≤ 2 * Real.log M := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  rw [Real.log_mul ha.ne' hM0.ne']
  have := Real.log_le_log ha (show a ≤ (M : ℝ) by linarith)
  linarith

theorem le_log_mul {M : ℕ} (hM : 3 ≤ M) {a : ℝ} (ha : 1 ≤ a) :
    Real.log M ≤ Real.log (a * M) := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  exact Real.log_le_log hM0 (le_mul_of_one_le_left hM0.le ha)

theorem div_log_le {M : ℕ} (hM : 3 ≤ M) {c₁ c : ℝ} (h0 : 0 ≤ c) (h : c₁ ≤ c / 2) :
    c₁ / Real.log M ≤ c / Real.log (2 * M) := by
  have hl := log_mul_le hM (a := 2) (by norm_num) (by norm_num)
  have hpos : 0 < Real.log M := lt_of_lt_of_le one_pos (one_le_log hM)
  have hpos2 : 0 < Real.log (2 * M) := by
    linarith [le_log_mul hM (a := 2) (by norm_num)]
  rw [div_le_div_iff₀ hpos hpos2]
  nlinarith [mul_nonneg (sub_nonneg.2 h) hpos2.le, mul_nonneg h0 (sub_nonneg.2 hl)]

private theorem exists_ne_zero_smul_mem_of_mem_span' {a b x y : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hx : 0 < x) (hxy : x ≤ y) :
    a / y ≤ b / x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  rw [div_le_div_iff₀ hy hx]
  nlinarith [mul_le_mul_of_nonneg_right hab hx.le, mul_le_mul_of_nonneg_left hxy (ha.trans hab)]

theorem main : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₀ → ∃ c : ℝ, 0 < c ∧ ∀ (M : ℕ) [NeZero M], 3 ≤ M → (∀ (χ χ' : DirichletCharacter ℂ M) (β β' : ℝ), IsExc c₁ χ β → IsExc c₁ χ' β' → χ = χ' ∧ β = β') ∧ (∀ (χ : DirichletCharacter ℂ M) (β : ℝ), IsExc c₁ χ β → χ ≠ 1 ∧ 7 / 8 ≤ β ∧ LFunction χ β = 0 ∧ ord χ β = 1 ∧ c / ((M : ℝ) ^ 2 * Real.log M) ≤ 1 - β) ∧ ∀ (χ : DirichletCharacter ℂ M) (ρ : ℂ), ρ.re < 1 → LFunction χ ρ = 0 → (ρ.im = 0 ∧ IsExc c₁ χ ρ.re) ∨ ρ.re ≤ 1 - c / Real.log (M * (|ρ.im| + 2)) := by
  obtain ⟨cu, hcu, hU⟩ := GlobalTheory.RealZeroNearOne.main
  obtain ⟨cp, hcp, hP⟩ := GlobalTheory.ZeroFreePrincipal.zero_free
  obtain ⟨cz, hcz, hZ⟩ := GlobalTheory.ZeroFreeComplex.zero_free_region
  obtain ⟨cs, hcs, hS⟩ := _root_.GlobalTheory.ZeroGapNearOne.exists_gap
  refine ⟨min (1 / 8) (min (cu / 2) (cp / 2)),
    lt_min (by norm_num) (lt_min (by linarith) (by linarith)), fun c₁ hc₁ hc₁0 => ?_⟩
  have hc18 : c₁ ≤ 1 / 8 := hc₁0.trans (min_le_left _ _)
  have hcu2 : c₁ ≤ cu / 2 := hc₁0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcp2 : c₁ ≤ cp / 2 := hc₁0.trans ((min_le_right _ _).trans (min_le_right _ _))
  set c := min c₁ (min cz (min cp (cs / 2))) with hcdef
  have hcpos : 0 < c := lt_min hc₁ (lt_min hcz (lt_min hcp (by linarith)))
  have hcc₁ : c ≤ c₁ := min_le_left _ _
  have hccz : c ≤ cz := (min_le_right _ _).trans (min_le_left _ _)
  have hccp : c ≤ cp := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hccs : c ≤ cs / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨c, hcpos, fun M _ hM => ?_⟩
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hlog1 : 1 ≤ Real.log M := one_le_log hM
  have hlogpos : 0 < Real.log M := lt_of_lt_of_le one_pos hlog1
  have hsmall : c₁ / Real.log M ≤ 1 / 8 := (div_le_self hc₁.le hlog1).trans hc18
  have hlogT : ∀ t : ℝ, 0 < Real.log (M * (|t| + 2)) := fun t =>
    Real.log_pos (by nlinarith [abs_nonneg t])
  have hexc : ∀ (χ : DirichletCharacter ℂ M) (β : ℝ), IsExc c₁ χ β →
      χ ≠ 1 ∧ 7 / 8 ≤ β ∧ LFunction χ β = 0 ∧ 1 - cu / Real.log (2 * M) ≤ β := by
    intro χ β h
    obtain ⟨_, hlt, hlt1, hL⟩ := h
    have hβ : 7 / 8 ≤ β := by linarith
    have hne : (β : ℂ) ≠ 1 := fun h => by
      have := congrArg Complex.re h
      simp at this
      linarith
    have hLχ : LFunction χ β = 0 :=
      (GlobalTheory.T.dirichletL_zeros_eq_primitiveCharacter_zeros M χ β (by simp; linarith) (Or.inr hne)).1.mpr hL
    refine ⟨fun hχ => ?_, hβ, hLχ, by linarith [div_log_le hM hcu.le hcu2]⟩
    rw [hχ] at hLχ
    have h1 := hP M (β : ℂ) hne hLχ
    have e : (M : ℝ) * 2 = 2 * M := mul_comm _ _
    rw [Complex.ofReal_re, Complex.ofReal_im, abs_zero, zero_add, e] at h1
    linarith [div_log_le hM hcp.le hcp2]
  refine ⟨fun χ χ' β β' h h' => ?_, fun χ β h => ?_, fun χ ρ hre hL => ?_⟩
  · obtain ⟨n1, -, L1, b1⟩ := hexc χ β h
    obtain ⟨n2, -, L2, b2⟩ := hexc χ' β' h'
    obtain ⟨s1, -⟩ := h
    obtain ⟨s2, -⟩ := h'
    obtain ⟨e1, e2, -⟩ := hU M χ χ' β β' n1 n2 s1 s2 b1 b2 L1 L2
    exact ⟨e1, e2⟩
  · obtain ⟨n1, h78, L1, b1⟩ := hexc χ β h
    obtain ⟨s1, -⟩ := h
    refine ⟨n1, h78, L1, ?_, ?_⟩
    · have hd := (hU M χ χ β β n1 n1 s1 s1 b1 b1 L1 L1).2.2
      have h1 := (GlobalTheory.RealZeroNearOne.analyticAt_L n1 (β : ℂ)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
        L1 hd
      rw [GlobalTheory.Lin.ord, analyticOrderNatAt, h1]
      rfl
    · have h1 := hS M χ β (Or.inl n1) L1 (by simp)
      rw [Complex.ofReal_re] at h1
      have hl3 := log_mul_le hM (a := 3) (by norm_num) le_rfl
      have hl3pos : 0 < Real.log (3 * M) := Real.log_pos (by linarith)
      have hD : 0 < (M : ℝ) ^ 2 * Real.log M := by positivity
      have hE : 0 < (M : ℝ) ^ 2 * Real.log (3 * M) := by positivity
      calc c / ((M : ℝ) ^ 2 * Real.log M) ≤ (cs / 2) / ((M : ℝ) ^ 2 * Real.log M) :=
            exists_ne_zero_smul_mem_of_mem_span' hcpos.le hccs hD le_rfl
        _ = cs / (2 * ((M : ℝ) ^ 2 * Real.log M)) := div_div cs 2 _
        _ ≤ cs / ((M : ℝ) ^ 2 * Real.log (3 * M)) :=
            exists_ne_zero_smul_mem_of_mem_span' hcs.le le_rfl hE (by nlinarith [sq_nonneg (M : ℝ)])
        _ ≤ 1 - β := h1
  · by_cases hreal : χ ^ 2 = 1 ∧ ρ.im = 0
    · obtain ⟨hsq, him⟩ := hreal
      have hρ : ρ = (ρ.re : ℂ) := Complex.ext (by simp) (by simp [him])
      by_cases hbig : 1 - c₁ / Real.log M < ρ.re
      · left
        refine ⟨him, ?_⟩
        have hpos : 0 < ρ.re := by linarith
        have hne : ρ ≠ 1 := fun h => by
          rw [h] at hre
          simp at hre
        have hL' := (GlobalTheory.T.dirichletL_zeros_eq_primitiveCharacter_zeros M χ ρ hpos (Or.inr hne)).1.mp hL
        unfold IsExc
        refine ⟨hsq, hbig, hre, ?_⟩
        rw [← hρ]
        exact hL'
      · right
        replace hbig := not_lt.mp hbig
        rw [him, abs_zero, zero_add]
        have h2 : Real.log M ≤ Real.log (M * 2) := by
          rw [mul_comm]
          exact le_log_mul hM (by norm_num)
        have := exists_ne_zero_smul_mem_of_mem_span' hcpos.le hcc₁ hlogpos h2
        linarith
    · right
      have hne' : χ ^ 2 = 1 → ρ.im ≠ 0 := fun h h' => hreal ⟨h, h'⟩
      by_cases hχ : χ = 1
      · have him : ρ.im ≠ 0 := hne' (by rw [hχ]; exact one_pow 2)
        have hne : ρ ≠ 1 := fun h => him (by rw [h]; simp)
        rw [hχ] at hL
        have h1 := hP M ρ hne hL
        have := exists_ne_zero_smul_mem_of_mem_span' hcpos.le hccp (hlogT ρ.im) le_rfl
        linarith
      · have hor : χ ^ 2 ≠ 1 ∨ ρ.im ≠ 0 := by
          by_cases h : χ ^ 2 = 1
          · exact Or.inr (hne' h)
          · exact Or.inl h
        have h1 := hZ M χ ρ hχ hL hor
        have := exists_ne_zero_smul_mem_of_mem_span' hcpos.le hccz (hlogT ρ.im) le_rfl
        linarith

end GlobalTheory.ExceptionalPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsCombOfMemClosureFinset
section
open Formalism.BasicNotions NumberField

namespace GlobalTheory


open NumberField in
theorem _root_.GlobalTheory.exists_oLat_of_fg_ringOfIntegers : ∀ (O K : Type) [CommRing O] [Field K] [NumberField K] (o : O →+* K) (e : K →+* ℂ) (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (W : Type) [AddCommGroup W] [Module ℂ W] (j : V →ₛₗ[e] W) (N : Submodule (𝓞 K) V), (∀ z, IsIntegral ℤ (o z)) → N.FG → Submodule.span ℂ (j '' (N : Set V)) = ⊤ → ∃ L : _root_.Formalism.BasicNotions.Rows.OLat O (e.comp o) W, L.carrier = j '' (N : Set V) ∧ (∀ v ∈ L.gen, v ∈ j '' (N : Set V)) ∧ (∀ y, (∃ c : W → 𝓞 K, y = ∑ v ∈ L.gen, e (c v : K) • v) ↔ y ∈ j '' (N : Set V)) ∧ ∀ (a : 𝓞 K), ∀ y ∈ L.carrier, e (a : K) • y ∈ L.carrier := by
  intro O K _ _ _ o e V _ _ _ _ W _ _ j N ho hN hspan
  have hNZ : (N.restrictScalars ℤ).FG := hN.restrictScalars
  obtain ⟨S, hS⟩ := hNZ.map j.toAddMonoidHom.toIntLinearMap
  have hmem : ∀ y, y ∈ Submodule.span ℤ (S : Set W) ↔ y ∈ j '' (N : Set V) := by
    intro y
    rw [hS, Submodule.mem_map]
    rfl
  have hsmul : ∀ (a : 𝓞 K) (y : W), y ∈ j '' (N : Set V) → e (a : K) • y ∈ j '' (N : Set V) := by
    rintro a _ ⟨n, hn, rfl⟩
    refine ⟨a • n, N.smul_mem a hn, ?_⟩
    rw [← algebraMap_smul K a n, j.map_smulₛₗ]
  have hcomb : ∀ c : W → 𝓞 K, ∑ v ∈ S, e (c v : K) • v ∈ j '' (N : Set V) := by
    intro c
    refine Finset.sum_induction _ (fun y => y ∈ j '' (N : Set V)) ?_ ⟨0, N.zero_mem, map_zero j⟩ ?_
    · rintro _ _ ⟨n₁, hn₁, rfl⟩ ⟨n₂, hn₂, rfl⟩
      exact ⟨n₁ + n₂, N.add_mem hn₁ hn₂, map_add j n₁ n₂⟩
    · intro v hv
      exact hsmul (c v) v ((hmem v).1 (Submodule.subset_span hv))
  have hint : ∀ y ∈ j '' (N : Set V), ∃ f : W → ℤ, y = ∑ v ∈ S, (f v : ℂ) • v := by
    intro y hy
    obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 ((hmem y).2 hy)
    refine ⟨f, ?_⟩
    rw [← hf]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Int.cast_smul_eq_zsmul]
  have hsub : j '' (N : Set V) ⊆ Submodule.span ℂ (S : Set W) := fun y hy =>
    Submodule.span_le_restrictScalars ℤ ℂ (S : Set W) ((hmem y).2 hy)
  let L : _root_.Formalism.BasicNotions.Rows.OLat O (e.comp o) W :=
    ⟨S, eq_top_iff.2 (hspan ▸ Submodule.span_le.2 hsub)⟩
  have hcarrier : L.carrier = j '' (N : Set V) := by
    unfold _root_.Formalism.BasicNotions.Rows.OLat.carrier
    ext y
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨c, rfl⟩
      exact hcomb fun v => ⟨o (c v), ho (c v)⟩
    · intro hy
      obtain ⟨f, rfl⟩ := hint y hy
      exact ⟨fun v => (f v : O), by simp [L]⟩
  refine ⟨L, hcarrier, fun v hv => (hmem v).1 (Submodule.subset_span hv), fun y => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨c, rfl⟩
    exact hcomb c
  · intro hy
    obtain ⟨f, rfl⟩ := hint y hy
    exact ⟨fun v => (f v : 𝓞 K), by simp [L]⟩
  · intro a y hy
    rw [hcarrier] at hy ⊢
    exact hsmul a y hy

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleFiniteProductStatement
section
open Complex
open scoped Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobiTriple_finite_product : ∀ (s x : ℂ), s ≠ 0 → ‖s‖ < 1 → x ≠ 0 → ∀ n : ℕ, ∏ k ∈ Finset.range n, ((1 + x * s ^ (2 * k + 1)) * (1 + x⁻¹ * s ^ (2 * k + 1))) = ∑ j ∈ Finset.Icc (-(n : ℤ)) n, GlobalTheory.JacobiTriple.finCoeff (s ^ 2) n j * (x ^ j * s ^ (j ^ 2)) := by
  first | exact @GlobalTheory.JacobiTriple.finTriple | exact GlobalTheory.JacobiTriple.finTriple | (intros; apply GlobalTheory.JacobiTriple.finTriple <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetsAreBoundedMeasureMomentsOfChartCoeffBoundStatement
section
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetsAreBoundedMeasureMoments_of_chart_coeff_bound : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (G : ℂ → ℂ), Differentiable ℂ G → Bd 1 (hat ι (C ω * logS) G) → MomInt ι (fun _ : Unit => ι.symm ω) G := by
  first | exact @GlobalTheory.MomOneAmice.momInt_of_bd_hat | exact GlobalTheory.MomOneAmice.momInt_of_bd_hat | (intros; apply GlobalTheory.MomOneAmice.momInt_of_bd_hat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsOfTensorFourthPower
section
open GlobalTheory.MomN Formalism.L2.Th1.H

noncomputable section

namespace GlobalTheory.MomRoot

theorem mahler_comp_clm (E V : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup V] [NormedSpace ℂ V]
    (κ : Type) [Fintype κ] (L : E →L[ℂ] V) (u : κ → E) (G : V → ℂ) (hG : ContDiff ℂ ⊤ G) (k : κ → ℕ) :
    mahler u (fun z => G (L z)) k = mahler (fun i => L (u i)) G k := by
  unfold GlobalTheory.MomN.mahler
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  unfold GlobalTheory.MomN.monoJet
  have h := L.iteratedFDeriv_comp_right hG (0 : E) (i := m.toMultiset.toList.length) le_top
  change iteratedFDeriv ℂ _ (G ∘ L) 0 _ = _
  rw [h, ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]

theorem mahler_embed (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (κ ι' : Type) [Fintype κ] [Fintype ι']
    (e : κ ↪ ι') (w : κ → V) (u : ι' → V) (G : V → ℂ) (hG : ContDiff ℂ ⊤ G)
    (hu : ∀ i, u (e i) = w i) (hz : ∀ p, p ∉ Set.range e → u p = 0) :
    (∀ k : ι' → ℕ, (∃ p, p ∉ Set.range e ∧ k p ≠ 0) → mahler u G k = 0) ∧
    (∀ k : ι' → ℕ, (∀ p, p ∉ Set.range e → k p = 0) → mahler u G k = mahler w G (fun i => k (e i))) :=
  _root_.GlobalTheory.MomEmbed.mahler_embed V κ ι' e w u G hG hu hz

theorem mahler_mul_disj (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (ι' : Type) [Fintype ι'] [DecidableEq ι']
    (u : ι' → V) (F H : V → ℂ) (hF : ContDiff ℂ ⊤ F) (hH : ContDiff ℂ ⊤ H) (S T : Finset ι') (hST : Disjoint S T)
    (hFS : ∀ k : ι' → ℕ, (∃ p, p ∉ S ∧ k p ≠ 0) → mahler u F k = 0)
    (hHT : ∀ k : ι' → ℕ, (∃ p, p ∉ T ∧ k p ≠ 0) → mahler u H k = 0) :
    (∀ N : ι' → ℕ, (∃ p, p ∉ S ∪ T ∧ N p ≠ 0) → mahler u (fun z => F z * H z) N = 0) ∧
    (∀ N : ι' → ℕ, (∀ p, p ∉ S ∪ T → N p = 0) → mahler u (fun z => F z * H z) N =
      mahler u F (fun p => if p ∈ S then N p else 0) * mahler u H (fun p => if p ∈ T then N p else 0)) :=
  _root_.GlobalTheory.mahler_mul_of_disjoint_support V ι' u F H hF hH S T hST hFS hHT

variable {n : Type} [Fintype n]

def sliceL (a : Fin 4) : (Fin 4 × n → ℂ) →L[ℂ] (n → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (a, i)

theorem sliceL_apply (a : Fin 4) (z : Fin 4 × n → ℂ) : sliceL a z = slice a z := rfl

def fourBlockInclusionVector (b : Fin 4) (x : n → ℂ) : Fin 4 × n → ℂ := fun z => if z.1 = b then x z.2 else 0

theorem slice_fourBlockInclusionVector (a b : Fin 4) (x : n → ℂ) : slice a (fourBlockInclusionVector b x) = if a = b then x else 0 := by
  funext i; by_cases h : a = b <;> simp [slice, fourBlockInclusionVector, h]

end GlobalTheory.MomRoot

namespace GlobalTheory.MomRoot

theorem jets_root : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (n : Type) [Fintype n] (ω : ℂ_[q]) (Λ : AddSubgroup (n → ℂ))
    (G : (n → ℂ) → ℂ), ContDiff ℂ ⊤ G → LatInt ι ω (pow4 Λ) (tens4 G) → LatInt ι ω Λ G := by
  intro q _ ι n _ ω Λ G hG hL κ _ v hv
  classical
  set c := ι.symm ω
  rw [_root_.GlobalTheory.MomCrit.momInt_iff_norm_mahler_le q ι (n → ℂ) κ _ G hG]
  intro m
  let U : Fin 4 × κ → (Fin 4 × n → ℂ) := fun p => c • fourBlockInclusionVector p.1 (v p.2)
  have hU : MomInt ι U (tens4 G) := hL (Fin 4 × κ) (fun p => fourBlockInclusionVector p.1 (v p.2)) (fun p a => by
    show slice a (fourBlockInclusionVector p.1 (v p.2)) ∈ Λ
    rw [slice_fourBlockInclusionVector]; split_ifs
    · exact hv _
    · exact Λ.zero_mem)
  have hGa : ∀ a, ContDiff ℂ ⊤ (fun z => G (slice a z)) := fun a => by
    have h : ContDiff ℂ ⊤ (sliceL (n := n) a) := ContinuousLinearMap.contDiff _
    exact hG.comp h
  have ht : tens4 G = fun z => G (slice 0 z) * G (slice 1 z) * G (slice 2 z) * G (slice 3 z) := by
    funext z; simp [tens4, Fin.prod_univ_four]
  have hcd : ContDiff ℂ ⊤ (tens4 G) := by
    rw [ht]; exact (((hGa 0).mul (hGa 1)).mul (hGa 2)).mul (hGa 3)
  have hb := ((_root_.GlobalTheory.MomCrit.momInt_iff_norm_mahler_le q ι _ _ U (tens4 G) hcd).1 hU) (fun p => m p.2)
  let S : Fin 4 → Finset (Fin 4 × κ) := fun a => Finset.univ.filter (fun p => p.1 = a)
  let e : Fin 4 → κ ↪ Fin 4 × κ := fun a => ⟨fun i => (a, i), fun i j h => (Prod.mk.inj h).2⟩
  have hposition : ∀ a, (∀ k : Fin 4 × κ → ℕ, (∃ p, p ∉ S a ∧ k p ≠ 0) → mahler U (fun z => G (slice a z)) k = 0) ∧
      (∀ k : Fin 4 × κ → ℕ, (∀ p, p ∉ S a → k p = 0) →
        mahler U (fun z => G (slice a z)) k = mahler (fun i => c • v i) G (fun i => k (a, i))) := by
    intro a
    have he : ∀ i, e a i = (a, i) := fun _ => rfl
    have hcomp : ∀ k, mahler U (fun z => G (slice a z)) k = mahler (fun p => sliceL a (U p)) G k :=
      fun k => by
        have h := mahler_comp_clm _ _ _ (sliceL a) U G hG k
        simp only [sliceL_apply] at h
        exact h
    have hrange : ∀ p : Fin 4 × κ, p ∈ Set.range (e a) ↔ p ∈ S a := by
      rintro ⟨b, i⟩; simp [Set.mem_range, he, S, eq_comm]
    obtain ⟨h1, h2⟩ := mahler_embed (n → ℂ) κ (Fin 4 × κ) (e a) (fun i => c • v i) (fun p => sliceL a (U p)) G hG
      (fun i => by simp [U, he, sliceL_apply, slice_fourBlockInclusionVector])
      (fun p hp => by
        have : p.1 ≠ a := fun h => hp ((hrange p).2 (by simp [S, h]))
        simp [U, sliceL_apply, slice_fourBlockInclusionVector, Ne.symm this])
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [hcomp]; obtain ⟨p, hp, hk⟩ := hk; exact h1 k ⟨p, by rwa [hrange], hk⟩
    · rw [hcomp]; exact h2 k (fun p hp => hk p (by rwa [← hrange]))
  have dj : ∀ (A : Finset (Fin 4)) (b : Fin 4), b ∉ A → Disjoint (A.biUnion S) (S b) := by
    intro A b hb
    rw [Finset.disjoint_left]; intro p hp hq
    simp only [Finset.mem_biUnion, S, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    obtain ⟨a, ha, rfl⟩ := hp; exact hb (hq ▸ ha)
  have u1 : ({0} : Finset (Fin 4)).biUnion S = S 0 := by simp
  have u2 : ({0, 1} : Finset (Fin 4)).biUnion S = S 0 ∪ S 1 := by simp [Finset.biUnion_insert]
  have u3 : ({0, 1, 2} : Finset (Fin 4)).biUnion S = S 0 ∪ S 1 ∪ S 2 := by
    simp [Finset.biUnion_insert, Finset.union_assoc]
  have d1 := dj {0} 1 (by decide)
  have d2 := dj {0, 1} 2 (by decide)
  have d3 := dj {0, 1, 2} 3 (by decide)
  rw [u1] at d1; rw [u2] at d2; rw [u3] at d3
  obtain ⟨A1v, A1⟩ := mahler_mul_disj _ _ U _ _ (hGa 0) (hGa 1) (S 0) (S 1) d1 (hposition 0).1 (hposition 1).1
  obtain ⟨A2v, A2⟩ := mahler_mul_disj _ _ U _ _ ((hGa 0).mul (hGa 1)) (hGa 2) (S 0 ∪ S 1) (S 2) d2 A1v (hposition 2).1
  obtain ⟨-, A3⟩ := mahler_mul_disj _ _ U _ _ (((hGa 0).mul (hGa 1)).mul (hGa 2)) (hGa 3)
    (S 0 ∪ S 1 ∪ S 2) (S 3) d3 A2v (hposition 3).1
  have key : mahler U (tens4 G) (fun p => m p.2) = (mahler (fun i => c • v i) G m) ^ 4 := by
    rw [ht, A3 _ ?_, A2 _ ?_, A1 _ ?_, (hposition 0).2 _ ?_, (hposition 1).2 _ ?_, (hposition 2).2 _ ?_, (hposition 3).2 _ ?_]
    · simp only [S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      norm_num
      ring
    all_goals
      intro p hp
      rcases p with ⟨b, i⟩
      simp only [S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      fin_cases b <;> simp at hp ⊢
  rw [key, map_pow, norm_pow] at hb
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 hb
end GlobalTheory.MomRoot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionFamilyContinuationGrowthStatement
section
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayClassLFunctionFamily_continuation_growth : ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ), AnalyticOnNhd ℂ (𝓕.F χ) {s | 1 / 2 < s.re} ∧ (∀ s : ℂ, 1 < s.re → LSeriesSummable (𝓕.aChi χ) s ∧ 𝓕.F χ s = (if χ = 1 then s - 1 else 1) * LSeries (𝓕.aChi χ) s) ∧ (∀ s : ℂ, 11 / 20 ≤ s.re → ‖𝓕.F χ s‖ ≤ 300 * 𝓕.B * (‖s‖ + 1) ^ 2) ∧ (χ * χ = 1 → ∀ s : ℂ, 𝓕.F χ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (𝓕.F χ s)) := by
  first | exact @GlobalTheory.Hk.RayCont.continuation_growth | exact GlobalTheory.Hk.RayCont.continuation_growth | (intros; apply GlobalTheory.Hk.RayCont.continuation_growth <;> assumption)
end

