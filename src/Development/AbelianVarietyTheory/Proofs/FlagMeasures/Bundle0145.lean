module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicInductionPhiPlusInductionFromBlockUni
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFdegGOfTotal
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec.SchurTotal

open Filter Topology

theorem span_ext {G H : Type} [MeasurableSpace G] (μ : Measure G) [AddCommGroup H] [Module ℂ H]
    (S : Set H) (f : H → G → ℂ) (r : H → ℂ) (φ : ℂ → ℂ)
    (hf0 : ∀ g, f 0 g = 0) (hr0 : r 0 = 0)
    (hfa : ∀ a b g, f (a + b) g = f a g + f b g) (hra : ∀ a b, r (a + b) = r a + r b)
    (hfs : ∀ (c : ℂ) a g, f (c • a) g = φ c * f a g) (hrs : ∀ (c : ℂ) a, r (c • a) = φ c * r a)
    (h : ∀ v ∈ S, Integrable (f v) μ ∧ ∫ g, f v g ∂μ = r v) :
    ∀ v ∈ Submodule.span ℂ S, Integrable (f v) μ ∧ ∫ g, f v g ∂μ = r v := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    have : f 0 = fun _ => 0 := funext hf0
    rw [this, hr0]
    exact ⟨integrable_zero _ _ _, by simp⟩
  | add x y _ _ hx hy =>
    have : f (x + y) = fun g => f x g + f y g := funext (hfa x y)
    rw [this, hra]
    exact ⟨hx.1.add hy.1, by rw [integral_add hx.1 hy.1, hx.2, hy.2]⟩
  | smul c x _ hx =>
    have : f (c • x) = fun g => φ c * f x g := funext (hfs c x)
    rw [this, hrs]
    exact ⟨hx.1.const_mul _, by rw [integral_const_mul, hx.2]⟩

variable {G : Type} [MeasurableSpace G] (μ : Measure G) {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] (σ : G → (H →L[ℂ] H)) (d : ℝ)

def Rel (v w v' w' : H) : Prop :=
  Integrable (fun g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ ∧
    ∫ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)

theorem rel_span (S : Set H) (h : ∀ v ∈ S, ∀ w ∈ S, ∀ v' ∈ S, ∀ w' ∈ S, Rel μ σ d v w v' w') :
    ∀ v ∈ Submodule.span ℂ S, ∀ w ∈ Submodule.span ℂ S, ∀ v' ∈ Submodule.span ℂ S,
      ∀ w' ∈ Submodule.span ℂ S, Rel μ σ d v w v' w' := by
  have h1 : ∀ v ∈ S, ∀ w ∈ S, ∀ v' ∈ S, ∀ w' ∈ Submodule.span ℂ S, Rel μ σ d v w v' w' := by
    intro v hv w hw v' hv'
    refine span_ext μ S (fun w' g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ)
      (fun w' => ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) (fun c => c) ?_ ?_ ?_ ?_ ?_ ?_ (h v hv w hw v' hv')
    · intro g; simp
    · simp
    · intro a b g; simp only [inner_add_left, star_add]; ring
    · intro a b; simp only [inner_add_right]; ring
    · intro c a g; simp only [inner_smul_left, star_mul', RCLike.star_def, Complex.conj_conj]; ring
    · intro c a; simp only [inner_smul_right]; ring
  have h2 : ∀ v ∈ S, ∀ w ∈ S, ∀ w' ∈ Submodule.span ℂ S, ∀ v' ∈ Submodule.span ℂ S,
      Rel μ σ d v w v' w' := by
    intro v hv w hw w' hw'
    refine span_ext μ S (fun v' g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ)
      (fun v' => ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) (fun c => star c) ?_ ?_ ?_ ?_ ?_ ?_
      (fun v' hv' => h1 v hv w hw v' hv' w' hw')
    · intro g; simp
    · simp
    · intro a b g; simp only [map_add (f := _), inner_add_right, star_add]; ring
    · intro a b; simp only [inner_add_left]; ring
    · intro c a g; simp only [map_smul, inner_smul_right, star_mul']; ring
    · intro c a; simp only [inner_smul_left, RCLike.star_def]; ring
  have h3 : ∀ v ∈ S, ∀ w' ∈ Submodule.span ℂ S, ∀ v' ∈ Submodule.span ℂ S,
      ∀ w ∈ Submodule.span ℂ S, Rel μ σ d v w v' w' := by
    intro v hv w' hw' v' hv'
    refine span_ext μ S (fun w g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ)
      (fun w => ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) (fun c => star c) ?_ ?_ ?_ ?_ ?_ ?_
      (fun w hw => h2 v hv w hw w' hw' v' hv')
    · intro g; simp
    · simp
    · intro a b g; simp only [inner_add_left]; ring
    · intro a b; simp only [inner_add_left]; ring
    · intro c a g; simp only [inner_smul_left, RCLike.star_def]; ring
    · intro c a; simp only [inner_smul_left, RCLike.star_def]; ring
  intro v hv w hw v' hv' w' hw'
  revert v
  refine span_ext μ S (fun v g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ)
      (fun v => ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) (fun c => c) ?_ ?_ ?_ ?_ ?_ ?_
      (fun v hv => h3 v hv w' hw' v' hv' w hw)
  · intro g; simp
  · simp
  · intro a b g; simp only [map_add (f := _), inner_add_right]; ring
  · intro a b; simp only [inner_add_right]; ring
  · intro c a g; simp only [map_smul, inner_smul_right]; ring
  · intro c a; simp only [inner_smul_right]; ring

theorem mul_star_eq (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem lint_of_rel (v w : H) (h : Rel μ σ d v w v w) :
    ∫⁻ g, ENNReal.ofReal (‖⟪w, σ g v⟫_ℂ‖ ^ 2) ∂μ = ENNReal.ofReal (‖v‖ ^ 2 * ‖w‖ ^ 2 / d) := by
  obtain ⟨h1, h2⟩ := h
  simp only [mul_star_eq] at h1 h2
  have h3 : Integrable (fun g => ‖⟪w, σ g v⟫_ℂ‖ ^ 2) μ := by
    have := h1.re
    simpa only [RCLike.re_to_complex, Complex.ofReal_re] using this
  rw [← ofReal_integral_eq_lintegral_ofReal h3 (ae_of_all _ fun g => by positivity)]
  congr 1
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h2
  apply Complex.ofReal_injective
  rw [h2]; push_cast; rfl

theorem lint_le (T : Set H) (hT : Dense T) (hm : ∀ v w : H, Measurable fun g => ⟪w, σ g v⟫_ℂ)
    (h : ∀ v ∈ T, ∀ w ∈ T, Rel μ σ d v w v w) (v w : H) :
    ∫⁻ g, ENNReal.ofReal (‖⟪w, σ g v⟫_ℂ‖ ^ 2) ∂μ ≤ ENNReal.ofReal (‖v‖ ^ 2 * ‖w‖ ^ 2 / d) := by
  obtain ⟨a, ha, hav⟩ := mem_closure_iff_seq_limit.1 (hT v)
  obtain ⟨b, hb, hbw⟩ := mem_closure_iff_seq_limit.1 (hT w)
  have h1 := lintegral_liminf_le (μ := μ) (u := atTop)
    (f := fun (n : ℕ) g => ENNReal.ofReal (‖⟪b n, σ g (a n)⟫_ℂ‖ ^ 2))
    (fun n => ((hm (a n) (b n)).norm.pow_const 2).ennreal_ofReal)
  have h2 : ∀ g, liminf (fun n => ENNReal.ofReal (‖⟪b n, σ g (a n)⟫_ℂ‖ ^ 2)) atTop
      = ENNReal.ofReal (‖⟪w, σ g v⟫_ℂ‖ ^ 2) := by
    intro g
    apply Tendsto.liminf_eq
    exact ENNReal.tendsto_ofReal
      ((hbw.inner (((σ g).continuous.tendsto v).comp hav)).norm.pow 2)
  have h3 : liminf (fun n => ∫⁻ g, ENNReal.ofReal (‖⟪b n, σ g (a n)⟫_ℂ‖ ^ 2) ∂μ) atTop
      = ENNReal.ofReal (‖v‖ ^ 2 * ‖w‖ ^ 2 / d) := by
    apply Tendsto.liminf_eq
    simp only [fun n => lint_of_rel μ σ d (a n) (b n) (h _ (ha n) _ (hb n))]
    exact ENNReal.tendsto_ofReal (((hav.norm.pow 2).mul (hbw.norm.pow 2)).div_const d)
  simpa only [h2, h3] using h1

theorem inner_toLp {f g : G → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hg.toLp g, hf.toLp f⟫_ℂ = ∫ x, f x * star (g x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]; simp

theorem rel_dense (hd : 0 < d) (T : Set H) (hT : Dense T)
    (hm : ∀ v w : H, Measurable fun g => ⟪w, σ g v⟫_ℂ)
    (h : ∀ v ∈ T, ∀ w ∈ T, ∀ v' ∈ T, ∀ w' ∈ T, Rel μ σ d v w v' w') (v w v' w' : H) :
    Rel μ σ d v w v' w' := by
  have hle := lint_le μ σ d T hT hm (fun v hv w hw => h v hv w hw v hv w hw)
  have hint : ∀ v w : H, Integrable (fun g => ‖⟪w, σ g v⟫_ℂ‖ ^ 2) μ := by
    intro v w
    refine ⟨((hm v w).norm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun g => by positivity)]
    exact (hle v w).trans_lt ENNReal.ofReal_lt_top
  have hL : ∀ v w : H, MemLp (fun g => ⟪w, σ g v⟫_ℂ) 2 μ := fun v w =>
    (memLp_two_iff_integrable_sq_norm (hm v w).aestronglyMeasurable).2 (hint v w)
  let C : H → H → Lp ℂ 2 μ := fun v w => (hL v w).toLp _
  have hC : ∀ v w, ‖C v w‖ ≤ ‖v‖ * ‖w‖ / √d := by
    intro v w
    have e1 : ((‖C v w‖ ^ 2 : ℝ) : ℂ) = ((∫ g, ‖⟪w, σ g v⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
      have := inner_toLp μ (hL v w) (hL v w)
      simp only [mul_star_eq] at this
      rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at this
      rw [← this]; push_cast; rfl
    have e2 := Complex.ofReal_injective e1
    have e3 : ∫ g, ‖⟪w, σ g v⟫_ℂ‖ ^ 2 ∂μ ≤ ‖v‖ ^ 2 * ‖w‖ ^ 2 / d := by
      have := hle v w
      rw [← ofReal_integral_eq_lintegral_ofReal (hint v w) (ae_of_all _ fun g => by positivity)] at this
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this
    apply le_of_sq_le_sq _ (by positivity)
    rw [e2, div_pow, mul_pow, Real.sq_sqrt hd.le]
    exact e3
  have hsplit : ∀ v w v0 w0, C v w - C v0 w0 = C (v - v0) w + C v0 (w - w0) := by
    intro v w v0 w0
    simp only [C]
    rw [← MemLp.toLp_sub, ← MemLp.toLp_add]
    apply MemLp.toLp_congr
    refine ae_of_all _ fun g => ?_
    simp only [Pi.sub_apply, Pi.add_apply, map_sub, inner_sub_left, inner_sub_right]
    ring
  have hcont : Continuous fun p : H × H => C p.1 p.2 := by
    rw [continuous_iff_continuousAt]
    intro p
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hc : Continuous fun q : H × H =>
        ‖q.1 - p.1‖ * ‖q.2‖ / √d + ‖p.1‖ * ‖q.2 - p.2‖ / √d := by fun_prop
    have ht := hc.tendsto p
    simp only [sub_self, norm_zero, zero_mul, mul_zero, zero_div, add_zero] at ht
    refine squeeze_zero (fun _ => norm_nonneg _) (fun q => ?_) ht
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add (hC _ _) (hC _ _))
  refine ⟨?_, ?_⟩
  · exact (hL v w).integrable_mul (hL v' w').star
  · have key : ∀ x : (H × H) × (H × H), ⟪C x.2.1 x.2.2, C x.1.1 x.1.2⟫_ℂ
        = ⟪x.2.1, x.1.1⟫_ℂ * ⟪x.1.2, x.2.2⟫_ℂ / (d : ℂ) := by
      have hD : Dense ((T ×ˢ T) ×ˢ (T ×ˢ T)) := (hT.prod hT).prod (hT.prod hT)
      have := Continuous.ext_on hD
        (f := fun x : (H × H) × (H × H) => ⟪C x.2.1 x.2.2, C x.1.1 x.1.2⟫_ℂ)
        (g := fun x => ⟪x.2.1, x.1.1⟫_ℂ * ⟪x.1.2, x.2.2⟫_ℂ / (d : ℂ))
        ((hcont.comp continuous_snd).inner (hcont.comp continuous_fst))
        (by fun_prop) (by
          rintro ⟨⟨a, b⟩, ⟨a', b'⟩⟩ ⟨⟨ha, hb⟩, ⟨ha', hb'⟩⟩
          exact (inner_toLp μ (hL a b) (hL a' b')).trans (h a ha b hb a' ha' b' hb').2)
      exact congrFun this
    exact (inner_toLp μ (hL v w) (hL v' w')).symm.trans (key ((v, w), (v', w')))

end GlobalTheory.Dec.SchurTotal

theorem GlobalTheory.Dec.isFdegG_of_total : ∀ (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : G → (H →L[ℂ] H)) (d : ℝ) (S : Set H), IsURep σ → 0 < d → Dense (Submodule.span ℂ S : Set H) → (∀ v ∈ S, ∀ w ∈ S, ∀ v' ∈ S, ∀ w' ∈ S, Integrable (fun g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ ∧ ∫ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) → IsFdegG μ σ d := by
  intro G _ _ _ _ μ H _ _ σ d S hσ hd hS h
  refine ⟨hd, fun v w v' w' => ?_⟩
  exact GlobalTheory.Dec.SchurTotal.rel_dense μ σ d hd _ hS
    (fun v w => (continuous_const.inner (hσ.2.2.2 v)).measurable)
    (GlobalTheory.Dec.SchurTotal.rel_span μ σ d S h) v w v' w'
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIrrAndDenseOfIsFdegG
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem IsFdegG.dense_span_orbit {G : Type} [MeasurableSpace G] {μ : Measure G} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : G → (H →L[ℂ] H)} {d : ℝ} (h : IsFdegG μ σ d)
    (w : H) (hw : w ≠ 0) : Dense (Submodule.span ℂ (Set.range fun g => σ g w) : Set H) := by
  obtain ⟨hd, hint⟩ := h
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro u hu
  rw [Submodule.mem_orthogonal] at hu

  have hzero : ∀ g, ⟪u, σ g w⟫_ℂ = 0 := fun g =>
    inner_eq_zero_symm.mp (hu (σ g w) (Submodule.subset_span ⟨g, rfl⟩))

  have key := (hint w u w u).2
  have hfun : (fun g => ⟪u, σ g w⟫_ℂ * star ⟪u, σ g w⟫_ℂ) = fun _ => (0 : ℂ) := by
    funext g
    simp [hzero g]
  rw [hfun, integral_zero] at key
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hw' : ⟪w, w⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hw
  have huu : ⟪u, u⟫_ℂ = 0 := by
    rcases div_eq_zero_iff.mp key.symm with h1 | h1
    · exact (mul_eq_zero.mp h1).resolve_left hw'
    · exact absurd h1 hd'
  exact inner_self_eq_zero.mp huu

theorem isIrr_and_dense_of_isFdegG : ∀ (G : Type) [MeasurableSpace G] (μ : Measure G) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G → (H →L[ℂ] H)) (d : ℝ), IsFdegG μ σ d → IsIrr σ ∧ ∀ w : H, w ≠ 0 → Dense (Submodule.span ℂ (Set.range fun g => σ g w) : Set H) := by
  intro G _ μ H _ _ _ σ d h
  refine ⟨?_, fun w hw => IsFdegG.dense_span_orbit h w hw⟩
  intro S hS hinv
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨w, hwS, hw⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot

    have hsub : Submodule.span ℂ (Set.range fun g => σ g w) ≤ S := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact hinv g w hwS
    have hcl : closure ((Submodule.span ℂ (Set.range fun g => σ g w) : Submodule ℂ H) : Set H) ⊆ (S : Set H) :=
      closure_minimal (fun y hy => hsub hy) hS
    rw [Submodule.eq_top_iff']
    intro x
    exact hcl (by rw [(IsFdegG.dense_span_orbit h w hw).closure_eq]; exact Set.mem_univ x)

end GlobalTheory.Dec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRiemannianHaarOnSubgroupMapMulRightUnitary
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GaugeRightInv

open Topology

theorem map_mul_right_of_conj_nhds {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsMulLeftInvariant] (B : Set G) (hBm : MeasurableSet B) (hB : B ∈ 𝓝 (1 : G))
    (h0 : ν B ≠ 0) (ht : ν B ≠ ⊤) (l : G) (hl : ∀ g, g * l ∈ B ↔ l * g ∈ B) :
    ν.map (fun g => g * l) = ν := by
  have hU : (interior B).Nonempty := ⟨1, mem_interior_iff_mem_nhds.2 hB⟩
  have hmeas : Measurable (fun g : G => g * l) := measurable_mul_const l
  haveI : IsFiniteMeasureOnCompacts ν :=
    ⟨fun K hK => measure_lt_top_of_isCompact_of_isMulLeftInvariant' hU ht hK⟩

  have hVo : IsOpen ((fun g : G => g * l⁻¹) ⁻¹' interior B) :=
    isOpen_interior.preimage (continuous_mul_const l⁻¹)
  have hV : ν.map (fun g => g * l) ((fun g : G => g * l⁻¹) ⁻¹' interior B) = ν (interior B) := by
    rw [Measure.map_apply hmeas hVo.measurableSet]
    congr 1
    ext g
    simp [mul_assoc]
  haveI : IsFiniteMeasureOnCompacts (ν.map (fun g => g * l)) :=
    ⟨fun K hK => measure_lt_top_of_isCompact_of_isMulLeftInvariant _ hVo
      ⟨l, by simpa using mem_interior_iff_mem_nhds.2 hB⟩
      (by rw [hV]; exact ((measure_mono interior_subset).trans_lt ht.lt_top).ne) hK⟩

  obtain ⟨c₁, e₁⟩ : ∃ c : NNReal, ν = c • (Measure.haar : Measure G) :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul ν Measure.haar⟩
  obtain ⟨c₂, e₂⟩ : ∃ c : NNReal, ν.map (fun g => g * l) = c • (Measure.haar : Measure G) :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul _ Measure.haar⟩

  have hBB : ν.map (fun g => g * l) B = ν B := by
    rw [Measure.map_apply hmeas hBm,
      show (fun g => g * l) ⁻¹' B = (fun g => l * g) ⁻¹' B from Set.ext hl]
    exact measure_preimage_mul ν l B
  have hpos : (Measure.haar : Measure G) B ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hB).ne'
  have hc₁ : (c₁ : ENNReal) ≠ 0 := by
    rintro h
    apply h0
    rw [e₁, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, h, zero_mul]
  have hfin : (Measure.haar : Measure G) B ≠ ⊤ := by
    intro h
    apply ht
    rw [e₁, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, h, ENNReal.mul_top hc₁]
  rw [e₂, e₁, Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, ENNReal.smul_def,
    smul_eq_mul, smul_eq_mul, ENNReal.mul_left_inj hpos hfin] at hBB
  rw [e₂, e₁, ENNReal.coe_injective hBB]

theorem map_mul_right_of_conj_nhds_subgroup {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (M : Subgroup G) (hM : IsClosed (M : Set G)) (μ : Measure G) (hμ : μ (M : Set G)ᶜ = 0)
    (hinv : ∀ s ∈ M, μ.map (fun g => s * g) = μ) (B : Set G) (hBm : MeasurableSet B) (hB : B ∈ 𝓝 (1 : G))
    (h0 : μ B ≠ 0) (ht : μ B ≠ ⊤) (l : G) (hlM : l ∈ M) (hl : ∀ g, g * l ∈ B ↔ l * g ∈ B) :
    μ.map (fun g => g * l) = μ := by
  haveI : LocallyCompactSpace M := hM.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology M := inferInstanceAs (SecondCountableTopology (M : Set G))
  haveI : BorelSpace M := inferInstanceAs (BorelSpace (M : Set G))
  have emb : MeasurableEmbedding (Subtype.val : M → G) :=
    MeasurableEmbedding.subtype_coe hM.measurableSet

  set ν : Measure M := μ.comap Subtype.val with hν
  have hμν : ν.map Subtype.val = μ := by
    rw [hν, emb.map_comap, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hμ)
  haveI : ν.IsMulLeftInvariant := ⟨fun s => by
    ext A hA
    rw [Measure.map_apply (measurable_const_mul s) hA, hν, emb.comap_apply, emb.comap_apply]
    have himg : Subtype.val '' ((fun x => s * x) ⁻¹' A) =
        (fun x : G => (s : G) * x) ⁻¹' (Subtype.val '' A) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨s * y, hy, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        have hx : x ∈ M := by
          have : x = (s : G)⁻¹ * y := by rw [hyx, ← mul_assoc, inv_mul_cancel, one_mul]
          rw [this]
          exact M.mul_mem (M.inv_mem s.2) y.2
        refine ⟨⟨x, hx⟩, ?_, rfl⟩
        show s * (⟨x, hx⟩ : M) ∈ A
        rw [show s * (⟨x, hx⟩ : M) = y from Subtype.ext hyx.symm]
        exact hy
    rw [himg, ← Measure.map_apply (measurable_const_mul (s : G)) (emb.measurableSet_image' hA),
      hinv s s.2]⟩
  have hνB : ν (Subtype.val ⁻¹' B) = μ B := by
    conv_rhs => rw [← hμν]
    rw [Measure.map_apply measurable_subtype_coe hBm]
  have key := map_mul_right_of_conj_nhds ν (Subtype.val ⁻¹' B)
    (hBm.preimage measurable_subtype_coe)
    (continuous_subtype_val.continuousAt.preimage_mem_nhds hB)
    (by rwa [hνB]) (by rwa [hνB]) ⟨l, hlM⟩ (fun g => hl g)
  rw [← hμν, Measure.map_map (measurable_mul_const l) measurable_subtype_coe,
    show (fun g : G => g * l) ∘ Subtype.val = Subtype.val ∘ (fun g : M => g * ⟨l, hlM⟩) from rfl,
    ← Measure.map_map measurable_subtype_coe (measurable_mul_const _), key]

theorem hs_eq_re_trace {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.hs X = (trace (X * Xᴴ)).re := by
  simp only [Formalism.REAL.hs, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

private theorem hs_mul_mul_conjTranspose_of_unitary {n : ℕ} (L M : Matrix (Fin n) (Fin n) ℂ) (hL : Lᴴ * L = 1) :
    Formalism.REAL.hs (L * M * Lᴴ) = Formalism.REAL.hs M := by
  rw [hs_eq_re_trace, hs_eq_re_trace, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  congr 1
  calc trace (L * M * Lᴴ * (L * (Mᴴ * Lᴴ))) = trace (L * (M * Mᴴ) * Lᴴ) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Lᴴ L, hL, Matrix.one_mul]
    _ = trace (Lᴴ * (L * (M * Mᴴ))) := Matrix.trace_mul_comm _ _
    _ = trace (M * Mᴴ) := by rw [← Matrix.mul_assoc, hL, Matrix.one_mul]

theorem hs_conj {n : ℕ} (L X : Matrix (Fin n) (Fin n) ℂ) (hL : Lᴴ * L = 1) :
    Formalism.REAL.hs (L * X - 1) = Formalism.REAL.hs (X * L - 1) := by
  have hL' : L * Lᴴ = 1 := mul_eq_one_comm.mp hL

  have h : L * X - 1 = L * (X * L - 1) * Lᴴ := by
    simp only [mul_sub, sub_mul, mul_one, mul_assoc, hL']
  rw [h, hs_mul_mul_conjTranspose_of_unitary L _ hL]

theorem isGaugeSub_map_mul_right (n : ℕ) (ε : Fin n → Bool) (M : Subgroup (Formalism.REAL.UJ ε)) (d : ℕ)
    (μ : Measure (Formalism.REAL.UJ ε)) (hM : IsClosed (M : Set (Formalism.REAL.UJ ε)))
    (hμ : IsGaugeSub (M : Set (Formalism.REAL.UJ ε)) d μ) (l : Formalism.REAL.UJ ε) (hlM : l ∈ M) (hlK : l ∈ maxK ε) :
    μ.map (fun g => g * l) = μ := by
  unfold IsGaugeSub at hμ
  obtain ⟨hμc, hinv, hlim⟩ := hμ
  have hlU : (uMat l)ᴴ * uMat l = 1 := by unfold maxK at hlK; exact hlK

  obtain ⟨r, ⟨h1, h2⟩, hr⟩ : ∃ r : ℝ,
      μ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} / ENNReal.ofReal (r ^ d) ∈ Set.Ioo 0 ⊤ ∧ 0 < r := by
    refine ((hlim.eventually (Ioo_mem_nhds ?_ ?_)).and self_mem_nhdsWithin).exists
    · exact Metric.measure_ball_pos _ _ one_pos
    · exact measure_ball_lt_top
  have hB0 : μ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ 0 := by
    intro h
    rw [h, ENNReal.zero_div] at h1
    exact lt_irrefl _ h1
  have hBt : μ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ ⊤ := by
    intro h
    rw [h, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at h2
    exact lt_irrefl _ h2
  have hu : Continuous fun g : Formalism.REAL.UJ ε => uMat g := by
    unfold uMat
    fun_prop
  have hc : Continuous fun g : Formalism.REAL.UJ ε => √(Formalism.REAL.hs (uMat g - 1)) := by
    unfold Formalism.REAL.hs
    fun_prop
  have hBn : {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} ∈ 𝓝 (1 : Formalism.REAL.UJ ε) := by
    have h1' : √(Formalism.REAL.hs (uMat (1 : Formalism.REAL.UJ ε) - 1)) < r := by
      rw [show uMat (1 : Formalism.REAL.UJ ε) = 1 from rfl, sub_self]
      simp [Formalism.REAL.hs, hr]
    exact Filter.mem_of_superset ((isOpen_lt hc continuous_const).mem_nhds h1') fun g hg =>
      show √(Formalism.REAL.hs (uMat g - 1)) ≤ r from le_of_lt hg

  have hcomm : ∀ g, g * l ∈ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} ↔
      l * g ∈ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} := by
    intro g
    show √(Formalism.REAL.hs (uMat (g * l) - 1)) ≤ r ↔ √(Formalism.REAL.hs (uMat (l * g) - 1)) ≤ r
    rw [show uMat (g * l) = uMat g * uMat l from rfl, show uMat (l * g) = uMat l * uMat g from rfl,
      hs_conj (uMat l) (uMat g) hlU]
  exact map_mul_right_of_conj_nhds_subgroup M hM μ hμc hinv _
    (isClosed_le hc continuous_const).measurableSet hBn hB0 hBt l hlM hcomm

end GlobalTheory.GaugeRightInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeStabiliserCommensurableIntegralPoints
section
open NumberField GlobalTheory.HL
open scoped Pointwise Classical

namespace GlobalTheory.HL.CommInt

theorem stabL_relIndex_K0_ne_zero_of_four_mul_add_seven_le : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ Λ : G.Lt, Submodule.IsFullLattice E Λ → (G.stabL Λ).relIndex G.K0 ≠ 0 ∧ G.K0.relIndex (G.stabL Λ) ≠ 0 := by
  intro F E _ _ _ _ _ sig A r k G hk Λ hΛ
  obtain ⟨-, hlat, -⟩ := _root_.GlobalTheory.HL.PlacesRec.lattice_local A (k + 2 * r + 1) Λ hΛ
  obtain ⟨hfin, -⟩ := GlobalTheory.HL.MassProduct.mass_eq_finprod A r k G hk Λ (by first | exact hΛ | exact hΛ.toIsLattice)
  let U : ∀ p, Subgroup (G.S p).GLV :=
    fun p => (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (A.lat p Λ)
  let K : ∀ p, Subgroup (G.S p).GLV := fun p => (G.S p).K0
  have hidx : ∀ p, (K p).relIndex (U p) ≠ 0 ∧ (U p).relIndex (K p) ≠ 0 := by
    intro p
    haveI := (A.loc p).lf
    haveI := (A.loc p).char0
    obtain ⟨a, b, -⟩ := (GlobalTheory.HL.volSt (A.L p) r k (G.S p)).1 (A.lat p Λ) (hlat p)
    exact ⟨a, b⟩
  have hKU : {p | K p ≠ U p}.Finite := hfin.subset fun p hp h => hp h.symm
  obtain ⟨h1, h2, -⟩ := _root_.GlobalTheory.HL.invVol_pi_univ K U hKU hidx
  let φ := GlobalTheory.HL.MassProduct.extHom A (k + 2 * r + 1)
  have e1 : G.K0 = (Subgroup.pi Set.univ K).comap φ := (GlobalTheory.HL.MassProduct.comap_pi A _ K).symm
  have e2 : G.stabL Λ = (Subgroup.pi Set.univ U).comap φ := (GlobalTheory.HL.MassProduct.comap_pi A _ U).symm
  rw [e1, e2, Subgroup.relIndex_comap, Subgroup.relIndex_comap]
  exact ⟨fun h0 => h2 (Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_comap_le _ _) h0),
    fun h0 => h1 (Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_comap_le _ _) h0)⟩

end GlobalTheory.HL.CommInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicInductionPhiPlusInductionFromBlockUniStatement
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolicInductionPhiPlus_inductionFromBlockUni : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i m : ℕ) (ρ : Gn g i → ℂ), i < m → ∀ x : Gn g (m + 1), InMir (x : Mt g (m + 1)) → indV ψ m (indR ψ i m ρ) x = indR ψ i (m + 1) ρ x := by
  first | exact @GlobalTheory.GLm.indV_indR | exact GlobalTheory.GLm.indV_indR | (intros; apply GlobalTheory.GLm.indV_indR <;> assumption)
end

