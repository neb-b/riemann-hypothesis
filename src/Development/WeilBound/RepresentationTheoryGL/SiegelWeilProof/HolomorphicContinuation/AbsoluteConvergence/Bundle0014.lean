module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0012
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0013
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousSecondCayleyBlockMap
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0010

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousGramX
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem scal_zero (X : Fin n → ℝ) (y : Fin m → Fin n → ℂ) : scal (aH X 0) y = y := by
  funext a j; simp [scal, aH]

theorem continuous_scal (α : Fin n → ℝ) : Continuous (scal (m := m) α) :=
  continuous_pi fun a => continuous_pi fun j => continuous_const.mul ((continuous_apply j).comp (continuous_apply a))

theorem continuous_gs (c : ℝ) : Continuous (gs (m := m) (n := n) c) := by
  unfold gs; fun_prop

theorem continuous_gramX (ε : Fin m → Bool) : Continuous (gramX (n := n) ε) :=
  continuous_pi fun i => continuous_pi fun j => continuous_evX _

theorem prod_aH (X : Fin n → ℝ) (h : ℝ) :
    (∏ j, aH X h j ^ (2 * m) : ℝ) = Real.exp (2 * (h * ((m : ℝ) * ∑ j, X j))) := by
  simp only [aH, ← Real.exp_nat_mul, ← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast; ring

theorem gaussPart : GaussPart := by
  intro m n ε c t hc X b hb Q
  set r : ℝ := (Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1 with hr
  set E : (Fin m → Fin n → ℂ) → ℂ := fun y => Complex.exp (Complex.I * t * (b * gramX ε y).trace) with hEdef
  have hE : ∀ y, ‖E y‖ = 1 := fun y => norm_phase t _ (trace_im ε y hb)
  have hEc : Continuous E := by
    refine Complex.continuous_exp.comp (continuous_const.mul ?_)
    exact (continuous_const.matrix_mul (continuous_gramX ε)).matrix_trace
  set A : ℝ := (m : ℝ) * ∑ j, X j with hA
  set P' : PX m n := dil c X Q - ((m : ℂ) * ∑ j, (X j : ℂ)) • Q with hP'
  let φ : ℝ → (Fin m → Fin n → ℂ) → ℂ := fun s y => evX Q (scal (aH X s) y) * gs c (scal (aH X s) y) * E y
  let φ' : ℝ → (Fin m → Fin n → ℂ) → ℂ := fun s y => evX P' (scal (aH X s) y) * gs c (scal (aH X s) y) * E y
  have hφc : ∀ (P : PX m n) (s : ℝ), Continuous fun y => evX P (scal (aH X s) y) * gs c (scal (aH X s) y) * E y :=
    fun P s => (((continuous_evX P).comp (continuous_scal _)).mul ((continuous_gs c).comp (continuous_scal _))).mul hEc
  have hH : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hint : Integrable (fun y : Fin m → Fin n → ℂ => (1 + ‖y‖) ^ (-r)) := by
    have : ((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ)) < r := by rw [hr]; linarith
    exact integrable_one_add_norm this
  have hdomI : ∀ (P : PX m n), ∃ K : ℝ, ∀ s : ℝ, |s| < 1 → ∀ y,
      ‖evX P (scal (aH X s) y) * gs c (scal (aH X s) y) * E y‖ ≤ K * (1 + ‖y‖) ^ (-r) := by
    intro P
    obtain ⟨K, -, hK⟩ := dom_bound c hc X P
    exact ⟨K, fun s hs y => by rw [norm_mul, hE, mul_one]; exact hK s hs y⟩
  have hintP : ∀ (P : PX m n) (s : ℝ), |s| < 1 →
      Integrable fun y => evX P (scal (aH X s) y) * gs c (scal (aH X s) y) * E y := by
    intro P s hs
    obtain ⟨K, hK⟩ := hdomI P
    exact Integrable.mono' (hint.const_mul K) (hφc P s).aestronglyMeasurable
      (Eventually.of_forall fun y => hK s hs y)

  have key : ∀ h : ℝ, Complex.exp (-((h * A : ℝ) : ℂ)) * secN ε c t Q (bS X h b) =
      Complex.exp (((h * A : ℝ) : ℂ)) * ∫ y, φ h y := by
    intro h
    have hpos : ∀ j, 0 < aH X h j := fun j => Real.exp_pos _
    have h1 : secN ε c t Q (bS X h b) = ((∏ j, aH X h j ^ (2 * m) : ℝ) : ℂ) * ∫ y, φ h y := by
      unfold secN
      rw [integral_scal (aH X h) hpos]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [φ, hEdef, trace_scal]
    rw [h1, prod_aH, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    congr 2
    rw [hA]; push_cast; ring

  obtain ⟨K, hK⟩ := hdomI P'
  have hΨ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := φ) (F' := φ') (x₀ := (0 : ℝ))
    (bound := fun y => K * (1 + ‖y‖) ^ (-r)) (Metric.ball_mem_nhds (0 : ℝ) one_pos)
    (Eventually.of_forall fun s => (hφc Q s).aestronglyMeasurable)
    (hintP Q 0 (by simp)) ((hφc P' 0).aestronglyMeasurable)
    (Eventually.of_forall fun y s hs => hK s (by simpa [Real.dist_eq] using hs) y) (hint.const_mul K)
    (Eventually.of_forall fun y s _ => by
      have := (hasDerivAt_phi c X Q y s).mul_const (E y)
      refine this.congr_deriv ?_
      simp only [φ', hP', evX_eq, map_sub, smul_eval])

  have hexp : HasDerivAt (fun h : ℝ => Complex.exp (((h * A : ℝ) : ℂ))) (Complex.exp (((0 * A : ℝ) : ℂ)) * (A : ℂ)) 0 :=
    (((hasDerivAt_id (0 : ℝ)).mul_const A).ofReal_comp).cexp.congr_deriv (by simp)
  have hF := hexp.mul hΨ.2
  have hfun : (fun h : ℝ => Complex.exp (-((h * ((m : ℝ) * ∑ j, X j) : ℝ) : ℂ)) * secN ε c t Q (bS X h b)) =
      fun h => Complex.exp (((h * A : ℝ) : ℂ)) * ∫ y, φ h y := funext key
  rw [hfun]
  refine hF.congr_deriv ?_

  have hφ0 : ∀ y, φ 0 y = evX Q y * gs c y * E y := fun y => by simp only [φ, scal_zero]
  have hφ'0 : ∀ y, φ' 0 y = evX P' y * gs c y * E y := fun y => by simp only [φ', scal_zero]
  have hI1 := hintP Q 0 (by simp)
  have hI2 := hintP P' 0 (by simp)
  simp only [scal_zero] at hI1 hI2
  have hdil : ∀ y, evX (dil c X Q) y * gs c y * E y =
      ((m : ℂ) * ∑ j, (X j : ℂ)) * (evX Q y * gs c y * E y) + evX P' y * gs c y * E y := by
    intro y
    simp only [hP', evX_eq, map_sub, smul_eval]
    ring
  unfold secN
  simp only [hφ0, hφ'0, zero_mul, Complex.ofReal_zero, Complex.exp_zero, one_mul]
  rw [integral_congr_ae (Eventually.of_forall hdil), integral_add (hI1.const_mul _) hI2, integral_const_mul]
  simp only [hEdef, hA]
  push_cast
  ring

end PositivityTheory.Rg.Sw.AbsSt.DF
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.HzBound0
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Far

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n}
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem hz_bound (hD : CayleyBlocksInvertible) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) {Q : PX m n} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖sec Q x‖ ≤ C * ‖sec 1 x‖) {σ₁ σ₂ : ℝ} {z : ℂ} (h₁ : σ₁ ≤ z.re) (h₂ : z.re ≤ σ₂) (x : G) :
    ‖hz Ht sec s₀ z Q x‖ ≤ C * (‖hz Ht sec s₀ (σ₁ : ℂ) 1 x‖ + ‖hz Ht sec s₀ (σ₂ : ℂ) 1 x‖) := by
  rw [norm_hz hD hG, norm_hz hD hG, norm_hz hD hG, Complex.ofReal_re, Complex.ofReal_re]
  have hx := Ht_pos hD hG x
  have hr := rpow_le_add hx (show σ₁ - s₀.re ≤ z.re - s₀.re by linarith) (show z.re - s₀.re ≤ σ₂ - s₀.re by linarith)
  calc (Ht x : ℝ) ^ (z.re - s₀.re) * ‖sec Q x‖
      ≤ ((Ht x : ℝ) ^ (σ₁ - s₀.re) + (Ht x : ℝ) ^ (σ₂ - s₀.re)) * (C * ‖sec 1 x‖) :=
        mul_le_mul hr (hC x) (norm_nonneg _) (by positivity)
    _ = C * ((Ht x : ℝ) ^ (σ₁ - s₀.re) * ‖sec 1 x‖ + (Ht x : ℝ) ^ (σ₂ - s₀.re) * ‖sec 1 x‖) := by ring

theorem hz_bound0 (hD : CayleyBlocksInvertible) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) {Q : PX m n} {C : ℝ}
    (hC : ∀ x, ‖sec Q x‖ ≤ C * ‖sec 1 x‖) (z : ℂ) (x : G) :
    ‖hz Ht sec s₀ z Q x‖ ≤ C * ‖hz Ht sec s₀ z 1 x‖ := by
  rw [norm_hz hD hG, norm_hz hD hG]
  calc (Ht x : ℝ) ^ (z.re - s₀.re) * ‖sec Q x‖ ≤ (Ht x : ℝ) ^ (z.re - s₀.re) * (C * ‖sec 1 x‖) :=
        mul_le_mul_of_nonneg_left (hC x) (Real.rpow_nonneg (Ht_pos hD hG x).le _)
    _ = C * ((Ht x : ℝ) ^ (z.re - s₀.re) * ‖sec 1 x‖) := by ring

theorem farHol (hI : Iwa) (hM : Mult) (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) : ∃ σ : ℝ,
    (∀ Q g, DifferentiableOn ℂ (fun z => GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z Q) g) (GlobalTheory.Cont.rightOf σ)) ∧
    (∀ Q g (z : ℂ), σ < z.re → Summable fun q => GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z Q) g q) ∧
    (∀ z : ℂ, σ < z.re → ∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧
      ∀ g ∈ C, ∀ q', ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z 1) g q'‖ ≤ u q') := by
  obtain ⟨U, d, E, σ, -, -, -, -, -, -, -, hconv⟩ := hG.eis
  have hmaj : ∀ z : ℂ, σ < z.re → ∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧
      ∀ g ∈ C, ∀ q', ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z 1) g q'‖ ≤ u q' :=
    fun z hzr C hC => (hconv z hzr).1 C hC
  refine ⟨σ, ?_, ?_, hmaj⟩
  · intro Q g z₀ hz₀
    have hz₀' : σ < z₀.re := hz₀
    obtain ⟨C, hC0, hC⟩ := sec_bound hI hM hD hL hG Q
    set σ₁ : ℝ := (σ + z₀.re) / 2
    set σ₂ : ℝ := z₀.re + 1
    have hσ₁ : σ < ((σ₁ : ℂ)).re := by simp only [Complex.ofReal_re, σ₁]; linarith
    have hσ₂ : σ < ((σ₂ : ℂ)).re := by simp only [Complex.ofReal_re, σ₂]; linarith
    obtain ⟨u₁, hu₁, hb₁⟩ := hmaj _ hσ₁ {g} isCompact_singleton
    obtain ⟨u₂, hu₂, hb₂⟩ := hmaj _ hσ₂ {g} isCompact_singleton
    set V : Set ℂ := {z | σ₁ < z.re ∧ z.re < σ₂}
    have hV : IsOpen V := (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
    have hz₀V : z₀ ∈ V := ⟨by simp only [σ₁]; linarith, by simp only [σ₂]; linarith⟩
    have hdiff : DifferentiableOn ℂ (fun w => ∑' q', GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ w Q) g q') V := by
      refine Complex.differentiableOn_tsum_of_summable_norm ((hu₁.add hu₂).mul_left C) (fun q' => ?_) hV
        (fun q' w hw => ?_)
      · have hne : (((Ht (((q'.out : Γ) : G) * g) : ℝ) : ℂ)) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (Ht_pos hD hG _).ne'
        exact (((differentiable_id.sub_const s₀).const_cpow (Or.inl hne)).mul_const _).differentiableOn
      · have h := hz_bound hD hG hC0 hC (σ₁ := σ₁) (σ₂ := σ₂) (z := w) hw.1.le hw.2.le (((q'.out : Γ) : G) * g)
        calc ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ w Q) g q'‖ ≤ C * (‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ (σ₁ : ℂ) 1) g q'‖ +
              ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ (σ₂ : ℂ) 1) g q'‖) := h
          _ ≤ C * (u₁ q' + u₂ q') := mul_le_mul_of_nonneg_left
              (add_le_add (hb₁ g (mem_singleton g) q') (hb₂ g (mem_singleton g) q')) hC0
          _ = (fun q' => C * (u₁ q' + u₂ q')) q' := rfl
    exact (hdiff.differentiableAt (hV.mem_nhds hz₀V)).differentiableWithinAt
  · intro Q g z hzr
    obtain ⟨C, hC0, hC⟩ := sec_bound hI hM hD hL hG Q
    obtain ⟨u, hu, hb⟩ := hmaj z hzr {g} isCompact_singleton
    refine Summable.of_norm_bounded (hu.mul_left C) fun q' => ?_
    calc ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z Q) g q'‖ ≤ C * ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z 1) g q'‖ :=
          hz_bound0 hD hG hC z _
      _ ≤ C * u q' := mul_le_mul_of_nonneg_left (hb g (mem_singleton g) q') hC0

end PositivityTheory.Rg.Sw.AbsSt.Far
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RpowLeAdd
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.FarK

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.Far

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n}

theorem sL_bound (hI : Iwa) (hM : Mult) (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ) (Q : PX m n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : GR n, ‖sL Q y‖ ≤ C * ‖F0 p q e y‖ := by
  have hK := PositivityTheory.Rg.Sw.AbsSt.Far.isCompact_KR (n := n)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hL.cont Q).continuousOn
  have hne : ((KR n : Subgroup (GR n)) : Set (GR n)).Nonempty := ⟨1, (KR n).one_mem⟩
  obtain ⟨k0, -, hmin⟩ := hK.exists_isMinOn hne (continuous_weight_factor (n := n) hD p q e).norm.continuousOn
  have hδ : 0 < ‖F0 p q e k0‖ := norm_pos_iff.mpr (weight_factor_ne_zero hD p q e k0)
  refine ⟨max B 0 / ‖F0 p q e k0‖, div_nonneg (le_max_right _ _) hδ.le, fun y => ?_⟩
  obtain ⟨u, k, hu, hk, rfl⟩ := hI n y
  have hmk : ‖F0 p q e k0‖ ≤ ‖F0 p q e k‖ := hmin hk
  rw [hL.law Q u k hu, ((hM n p q e).1 u k hk).1, norm_mul, norm_mul]
  have h1 : ‖sL Q k‖ ≤ max B 0 := (hB k hk).trans (le_max_left _ _)
  have h2 : max B 0 ≤ max B 0 / ‖F0 p q e k0‖ * ‖F0 p q e k‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    exact mul_le_mul_of_nonneg_left hmk (le_max_right _ _)
  calc ‖F0 p q e u‖ * ‖sL Q k‖ ≤ ‖F0 p q e u‖ * (max B 0 / ‖F0 p q e k0‖ * ‖F0 p q e k‖) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (norm_nonneg _)
    _ = max B 0 / ‖F0 p q e k0‖ * (‖F0 p q e u‖ * ‖F0 p q e k‖) := by ring

theorem rpow_le_add {a x₁ x₂ s : ℝ} (ha : 0 < a) (h₁ : x₁ ≤ s) (h₂ : s ≤ x₂) : a ^ s ≤ a ^ x₁ + a ^ x₂ := by
  rcases le_total 1 a with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h h₂
    have := Real.rpow_nonneg ha.le x₁
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge ha h h₁
    have := Real.rpow_nonneg ha.le x₂
    linarith

section Glob

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)}

theorem Ht_pos (hD : CayleyBlocksInvertible) (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) (x : G) : 0 < (Ht x : ℝ) := by
  obtain ⟨x₀, y, S, r, hr, rfl, h⟩ := hG.split x
  rw [(h y).1]
  exact mul_pos hr (hLoc_pos hD y)

theorem sec_bound (hI : Iwa) (hM : Mult) (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) (Q : PX m n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : G, ‖sec Q x‖ ≤ C * ‖sec 1 x‖ := by
  obtain ⟨C, hC0, hC⟩ := PositivityTheory.Rg.Sw.AbsSt.FarK.sL_bound hI hM hD hL Q
  refine ⟨C, hC0, fun x => ?_⟩
  obtain ⟨x0, y, S, r, -, hx, hy⟩ := hG.split x
  subst hx
  rw [(hy y).2 Q, (hy y).2 1, hL.vac y, norm_mul, norm_mul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg S)

theorem norm_hz (hD : CayleyBlocksInvertible) (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) (z : ℂ) (Q : PX m n) (x : G) :
    ‖hz Ht sec s₀ z Q x‖ = (Ht x : ℝ) ^ (z.re - s₀.re) * ‖sec Q x‖ := by
  have hpos := PositivityTheory.Rg.Sw.AbsSt.FarK.Ht_pos hD hG x
  simp only [hz, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.sub_re]

end Glob

end PositivityTheory.Rg.Sw.AbsSt.FarK
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerMC
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.SDM

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.DF

variable {m n : ℕ}

theorem aE_eq (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : aE H σ = NormedSpace.exp (σ • H) := by
  unfold aE; rw [Complex.coe_smul]

theorem hasDerivAt_aE_entry (H : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (i j : Fin n) :
    HasDerivAt (fun σ : ℝ => aE H σ i j) ((aE H s * H) i j) s := by
  simp only [aE_eq]
  open scoped Matrix.Norms.Operator in
  exact ((Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt s
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) H s)

theorem mulR_mul (A B : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) :
    mulR B (mulR A y) = mulR (A * B) y := by
  funext a j
  simp only [mulR, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

theorem mulR_one (y : Fin m → Fin n → ℂ) : mulR (1 : Matrix (Fin n) (Fin n) ℂ) y = y := by
  funext a j
  simp [mulR, Matrix.one_apply]

theorem hasDerivAt_mulR (H : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) (s : ℝ) (a : Fin m) (j : Fin n) :
    HasDerivAt (fun σ : ℝ => mulR (aE H σ) y a j) (mulR H (mulR (aE H s) y) a j) s := by
  have h : HasDerivAt (fun σ : ℝ => ∑ i, y a i * aE H σ i j) (∑ i, y a i * (aE H s * H) i j) s :=
    HasDerivAt.fun_sum fun i _ => (hasDerivAt_aE_entry H s i j).const_mul (y a i)
  have e : ∑ i, y a i * (aE H s * H) i j = mulR H (mulR (aE H s) y) a j := by
    rw [mulR_mul]; rfl
  exact e ▸ h

theorem hasDerivAt_ept (H : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) (s : ℝ) (k : Fin m × Fin n × Bool) :
    HasDerivAt (fun σ : ℝ => ept (mulR (aE H σ) y) k) (ept (mulR H (mulR (aE H s) y)) k) s := by
  rcases k with ⟨a, j, b⟩
  cases b
  · exact hasDerivAt_mulR H y s a j
  · exact (hasDerivAt_mulR H y s a j).star

theorem evX_eulH (H : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) (z : Fin m → Fin n → ℂ) :
    evX (eulH H R) z = ∑ k, MvPolynomial.eval (ept z) (pderiv k R) * ept (mulR H z) k := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [eulH, evX_eq, map_sum, map_add (f := _), map_mul, eval_X, eval_C]
  rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun a _ => Fintype.sum_prod_type _]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  simp only [ept, mulR, if_true, Bool.false_eq_true, if_false, star_sum, star_mul']
  ring_nf

def trHQ (ε : Fin m → Bool) (H : Matrix (Fin n) (Fin n) ℂ) : PX m n :=
  ∑ i, ∑ j, MvPolynomial.C (H i j) * (Qb ε true j i + Qb ε false j i)

theorem evX_Qb_add (ε : Fin m → Bool) (z : Fin m → Fin n → ℂ) (i j : Fin n) :
    evX (Qb ε true i j + Qb ε false i j) z = ∑ a, star (z a i) * z a j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Qb, evX_eq, map_add (f := _), map_sum, map_mul, eval_X, ept, if_true, Bool.false_eq_true, if_false]
  convert Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => ε x = true) (fun x => star (z x i) * z x j) using 3
  ext x; simp

theorem evX_trHQ (ε : Fin m → Bool) (H : Matrix (Fin n) (Fin n) ℂ) (z : Fin m → Fin n → ℂ) :
    evX (trHQ ε H) z = ∑ a, ∑ j, star (z a j) * mulR H z a j := by
  have e : evX (trHQ ε H) z = ∑ i, ∑ j, H i j * evX (Qb ε true j i + Qb ε false j i) z := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [trHQ, evX_eq, map_sum, map_mul, eval_C]
  rw [e]
  simp only [evX_Qb_add, mulR, Finset.mul_sum]
  calc ∑ i, ∑ j, ∑ a, H i j * (star (z a j) * z a i) = ∑ j, ∑ i, ∑ a, H i j * (star (z a j) * z a i) :=
        Finset.sum_comm
    _ = ∑ j, ∑ a, ∑ i, H i j * (star (z a j) * z a i) := Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ a, ∑ j, ∑ i, H i j * (star (z a j) * z a i) := Finset.sum_comm
    _ = ∑ a, ∑ j, ∑ i, star (z a j) * (z a i * H i j) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem trHQ_real (ε : Fin m → Bool) {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (z : Fin m → Fin n → ℂ) :
    (evX (trHQ ε H) z).im = 0 := by
  have hij : ∀ i j, star (H i j) = H j i := fun i j => by
    have := congrFun (congrFun hH j) i
    simpa [Matrix.conjTranspose_apply] using this
  have hconj : star (evX (trHQ ε H) z) = evX (trHQ ε H) z := by
    rw [evX_trHQ]
    simp only [mulR, star_sum, star_mul', star_star, Finset.mul_sum, hij]
    refine Finset.sum_congr rfl fun a _ => ?_
    calc ∑ j, ∑ i, z a j * (star (z a i) * H j i) = ∑ i, ∑ j, z a j * (star (z a i) * H j i) := Finset.sum_comm
      _ = ∑ i, ∑ j, star (z a i) * (z a j * H j i) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have := congrArg Complex.im hconj
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith

theorem hasDerivAt_normSq (w : ℝ → ℂ) (w' : ℂ) (s : ℝ) (hw : HasDerivAt w w' s) :
    HasDerivAt (fun σ => ‖w σ‖ ^ 2) (2 * (star (w s) * w').re) s := by
  have hre : HasDerivAt (fun σ => (w σ).re) w'.re s := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hw
  have him : HasDerivAt (fun σ => (w σ).im) w'.im s := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hw
  have h := (hre.pow 2).add (him.pow 2)
  have e : ∀ σ, (w σ).re ^ 2 + (w σ).im ^ 2 = ‖w σ‖ ^ 2 := fun σ => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun σ => (e σ).symm)).congr_deriv ?_
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  push_cast
  ring

theorem hasDerivAt_gsE (c : ℝ) (ε : Fin m → Bool) {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    (y : Fin m → Fin n → ℂ) (s : ℝ) :
    HasDerivAt (fun σ => gs c (mulR (aE H σ) y))
      (gs c (mulR (aE H s) y) * (-(2 * (c : ℂ)) * evX (trHQ ε H) (mulR (aE H s) y))) s := by
  have hS : HasDerivAt (fun σ => ∑ a, ∑ j, ‖mulR (aE H σ) y a j‖ ^ 2)
      (∑ a, ∑ j, 2 * (star (mulR (aE H s) y a j) * mulR H (mulR (aE H s) y) a j).re) s :=
    HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun j _ => hasDerivAt_normSq _ _ s (hasDerivAt_mulR H y s a j)
  have hg := (((hS.const_mul c).ofReal_comp).neg).cexp
  set T := evX (trHQ ε H) (mulR (aE H s) y) with hTdef
  have h0 : T.im = 0 := trHQ_real ε hH _
  have hsum : (∑ a, ∑ j, 2 * (star (mulR (aE H s) y a j) * mulR H (mulR (aE H s) y) a j).re) = 2 * T.re := by
    rw [hTdef, evX_trHQ]
    simp only [Complex.re_sum, Finset.mul_sum]
  have hT' : ((T.re : ℝ) : ℂ) = T := Complex.ext (by simp) (by simp [h0])
  unfold gs
  refine hg.congr_deriv ?_
  simp only [Pi.neg_apply]
  rw [hsum]
  push_cast
  rw [hT']
  ring

end PositivityTheory.Rg.Sw.AbsSt.SDM
end
end

