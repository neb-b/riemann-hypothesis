module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0014
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0010
public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0015
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.VacCore
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0011

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumSection
section
namespace PositivityTheory.Rg.Sw.AbsSt

theorem derivative_vacuum_section : DerivativeVacuumDilations := DF.derivative_vacuum_of_parts DF.gaussPart DF.groupPart

end PositivityTheory.Rg.Sw.AbsSt
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.HzBound
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.FarK

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.Far

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n}
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)}

theorem hz_bound (hD : CayleyBlocksInvertible) (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) {Q : PX m n} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖sec Q x‖ ≤ C * ‖sec 1 x‖) {σ₁ σ₂ : ℝ} {z : ℂ} (h₁ : σ₁ ≤ z.re) (h₂ : z.re ≤ σ₂) (x : G) :
    ‖hz Ht sec s₀ z Q x‖ ≤ C * (‖hz Ht sec s₀ (σ₁ : ℂ) 1 x‖ + ‖hz Ht sec s₀ (σ₂ : ℂ) 1 x‖) := by
  rw [norm_hz hD hG, norm_hz hD hG, norm_hz hD hG, Complex.ofReal_re, Complex.ofReal_re]
  have hx := Ht_pos hD hG x
  have hr := rpow_le_add hx (show σ₁ - s₀.re ≤ z.re - s₀.re by linarith) (show z.re - s₀.re ≤ σ₂ - s₀.re by linarith)
  calc (Ht x : ℝ) ^ (z.re - s₀.re) * ‖sec Q x‖
      ≤ ((Ht x : ℝ) ^ (σ₁ - s₀.re) + (Ht x : ℝ) ^ (σ₂ - s₀.re)) * (C * ‖sec 1 x‖) :=
        mul_le_mul hr (hC x) (norm_nonneg _) (by positivity)
    _ = C * ((Ht x : ℝ) ^ (σ₁ - s₀.re) * ‖sec 1 x‖ + (Ht x : ℝ) ^ (σ₂ - s₀.re) * ‖sec 1 x‖) := by ring

theorem hz_bound0 (hD : CayleyBlocksInvertible) (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) {Q : PX m n} {C : ℝ}
    (hC : ∀ x, ‖sec Q x‖ ≤ C * ‖sec 1 x‖) (z : ℂ) (x : G) :
    ‖hz Ht sec s₀ z Q x‖ ≤ C * ‖hz Ht sec s₀ z 1 x‖ := by
  rw [norm_hz hD hG, norm_hz hD hG]
  calc (Ht x : ℝ) ^ (z.re - s₀.re) * ‖sec Q x‖ ≤ (Ht x : ℝ) ^ (z.re - s₀.re) * (C * ‖sec 1 x‖) :=
        mul_le_mul_of_nonneg_left (hC x) (Real.rpow_nonneg (Ht_pos hD hG x).le _)
    _ = C * ((Ht x : ℝ) ^ (z.re - s₀.re) * ‖sec 1 x‖) := by ring

theorem farHol (hI : Iwa) (hM : Mult) (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) : ∃ σ : ℝ,
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

end PositivityTheory.Rg.Sw.AbsSt.FarK
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RootsBound
section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Vac

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n} {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem roots_bound (d : Polynomial ℂ) (hd : d ≠ 0) : ∃ σ : ℝ, ∀ z : ℂ, σ < z.re → d.eval z ≠ 0 := by
  refine ⟨∑ r ∈ d.roots.toFinset, |r.re|, fun z hz h0 => ?_⟩
  have hm : z ∈ d.roots.toFinset := Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hd).mpr h0)
  have h1 : |z.re| ≤ ∑ r ∈ d.roots.toFinset, |r.re| :=
    Finset.single_le_sum (f := fun r : ℂ => |r.re|) (fun r _ => abs_nonneg _) hm
  linarith [le_abs_self z.re]

theorem top_E [MeasurableSpace (KR n)] [BorelSpace (KR n)] [CompactSpace (KR n)] (μ : Measure (KR n))
    [IsFiniteMeasure μ] (hL : LocData ε c t p q e sL ρ) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (hD : CayleyBlocksInvertible)
    (hHP : HolParam) {a b : GR n} {nb : (Fin n → Fin n → ℝ) → GR n} (hnbc : Continuous nb)
    {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) {cz : ℂ → ℂ}
    (hczd : Differentiable ℂ cz)
    (hceig : ∀ (w : ℂ) (y : GR n), ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, ((hLoc (y * (k : GR n) * a * nb x * b) : ℂ) ^ w *
        F0 p q e (y * (k : GR n) * a * nb x * b)) * ψ x) ∂μ = cz w * ((hLoc y : ℂ) ^ w * F0 p q e y))
    {U : Set ℂ} {d : Polynomial ℂ} {E : ℂ → G → ℂ} {σ : ℝ} (hUo : IsOpen U) (hUr : GlobalTheory.Cont.IsRightDomain U)
    (hd : d ≠ 0) (hEh : ∀ g, DifferentiableOn ℂ (fun z => E z g) U)
    (hEc : ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ univ))
    (hEr : ∀ z : ℂ, σ < z.re → (∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧ ∀ g ∈ C, ∀ q,
        ‖GlobalTheory.Eis.term Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec 1 x) g q‖ ≤ u q) ∧
      ∀ g, E z g = d.eval z * GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec 1 x) g) :
    ∀ z ∈ U, ∀ g, Top μ ι p q e a b nb ψ (E z) g = cz (z - s₀) * E z g := by
  have hsm : ∀ (c : ℂ) (F : G → ℂ) (g : G),
      Top μ ι p q e a b nb ψ (fun x => c * F x) g = c * Top μ ι p q e a b nb ψ F g := by
    intro c F g
    simp only [Top, mul_assoc c]
    simp_rw [integral_const_mul, mul_left_comm _ c, integral_const_mul]
  intro z hzU g
  have hdiff : DifferentiableOn ℂ
      (fun w => Top μ ι p q e a b nb ψ (E w) g - cz (w - s₀) * E w g) U := by
    have h1 : DifferentiableOn ℂ (fun w => Top μ ι p q e a b nb ψ (E w) g) U :=
      top_hol (p := p) (q := q) (e := e) (a := a) (b := b) μ hD hHP hG.ιcont hnbc hψc hψs hUo E hEc hEh g
    have h2 : DifferentiableOn ℂ (fun w => cz (w - s₀)) U :=
      (hczd.comp (differentiable_id.sub_const s₀)).differentiableOn
    exact h1.sub (h2.mul (hEh g))
  have hVo : IsOpen (connectedComponentIn U z) := hUo.connectedComponentIn
  have hVU : connectedComponentIn U z ⊆ U := connectedComponentIn_subset U z
  have han := (hdiff.mono hVU).analyticOnNhd hVo
  have hray : (fun t : ℝ => z + (t : ℂ)) '' Ici 0 ⊆ connectedComponentIn U z := by
    apply IsPreconnected.subset_connectedComponentIn
    · exact isPreconnected_Ici.image _ (by fun_prop : Continuous fun t : ℝ => z + (t : ℂ)).continuousOn
    · exact ⟨0, Set.mem_Ici.mpr le_rfl, by simp⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact hUr.2 z hzU t ht
  have hT : (0 : ℝ) ≤ max 0 (σ - z.re) + 1 := by
    have := le_max_left 0 (σ - z.re)
    linarith
  have hw0 : z + ((max 0 (σ - z.re) + 1 : ℝ) : ℂ) ∈ connectedComponentIn U z := hray ⟨_, hT, rfl⟩
  have hre : σ < (z + ((max 0 (σ - z.re) + 1 : ℝ) : ℂ)).re := by
    have := le_max_right 0 (σ - z.re)
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hev : (fun w => Top μ ι p q e a b nb ψ (E w) g - cz (w - s₀) * E w g)
      =ᶠ[𝓝 (z + ((max 0 (σ - z.re) + 1 : ℝ) : ℂ))] 0 := by
    have hopen : IsOpen {w : ℂ | σ < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hre] with w hw
    have hEw : E w = fun x => d.eval w * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ w) x :=
      funext fun x => (hEr w hw).2 x
    have hs := top_sum μ hL hG hD hG.ιcont hnbc hψc hψs hceig w (hEr w hw).1 g
    simp only [Pi.zero_apply]
    rw [hEw, hsm (d.eval w) (fun x => GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ w) x), hs]
    ring
  have h := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_connectedComponentIn
    hw0 hev (mem_connectedComponentIn hzU)
  simp only [Pi.zero_apply] at h
  exact sub_eq_zero.mp h

end PositivityTheory.Rg.Sw.AbsSt.Vac
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerMD
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.SDM

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.DF

variable {m n : ℕ}

theorem hasDerivAt_phiE (c : ℝ) (ε : Fin m → Bool) {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (R : PX m n)
    (y : Fin m → Fin n → ℂ) (s : ℝ) :
    HasDerivAt (fun σ => evX R (mulR (aE H σ) y) * gs c (mulR (aE H σ) y))
      (evX (DMp ε c H R) (mulR (aE H s) y) * gs c (mulR (aE H s) y)) s := by
  have hR : HasDerivAt (fun σ => evX R (mulR (aE H σ) y)) (evX (eulH H R) (mulR (aE H s) y)) s := by
    rw [evX_eulH]
    exact hasDerivAt_eval_curve R (fun σ => ept (mulR (aE H σ) y)) _ s
      (fun k => hasDerivAt_ept H y s k)
  refine (hR.mul (hasDerivAt_gsE c ε hH y s)).congr_deriv ?_
  simp only [DMp, trHQ, evX_eq, map_sub, map_mul, MvPolynomial.eval_C]
  ring

theorem norm_mulR_le (A : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) :
    ‖mulR A y‖ ≤ (∑ i, ∑ j, ‖A i j‖) * ‖y‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun a => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
  calc ‖mulR A y a j‖ = ‖∑ i, y a i * A i j‖ := rfl
    _ ≤ ∑ i, ‖y a i * A i j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖y‖ * ‖A i j‖ := by
        gcongr with i
        rw [norm_mul]
        gcongr
        exact (norm_le_pi_norm (y a) i).trans (norm_le_pi_norm y a)
    _ = ‖y‖ * ∑ i, ‖A i j‖ := by rw [Finset.mul_sum]
    _ ≤ ‖y‖ * ∑ i, ∑ j, ‖A i j‖ := by
        gcongr with i
        exact Finset.single_le_sum (f := fun j => ‖A i j‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)
    _ = _ := mul_comm _ _

theorem continuous_aE_entry (H : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : Continuous fun σ : ℝ => aE H σ i j :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_aE_entry H s i j).continuousAt

theorem dom_boundE (c : ℝ) (hc : 0 < c) (H : Matrix (Fin n) (Fin n) ℂ) (P : PX m n) (s : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ, |σ - s| < 1 → ∀ y : Fin m → Fin n → ℂ,
      ‖evX P (mulR (aE H σ) y) * gs c (mulR (aE H σ) y)‖ ≤
        K * (1 + ‖y‖) ^ (-((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1)) := by
  set r : ℝ := (Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1 with hr
  have hr0 : 0 ≤ r := by positivity
  obtain ⟨Cp, k, hCp, hP⟩ := PositivityTheory.Rg.Sw.AbsSt.DF.poly_bound P
  obtain ⟨Cd, hCd, hdec⟩ := PositivityTheory.Rg.Sw.AbsSt.DF.decay k c hc r
  obtain ⟨L, hL⟩ := (isCompact_Icc (a := s - 1) (b := s + 1)).exists_bound_of_continuousOn
    (f := fun σ : ℝ => ∑ i, ∑ j, ‖aE H (-σ) i j‖)
    (Continuous.continuousOn (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      ((continuous_aE_entry H i j).comp continuous_neg).norm))
  set L' := max L 1 with hL'
  have hL'1 : 1 ≤ L' := le_max_right _ _
  have hL'0 : 0 ≤ L' := by linarith
  refine ⟨Cp * Cd * L' ^ r, mul_nonneg (mul_nonneg hCp hCd) (Real.rpow_nonneg hL'0 r),
    fun σ hσ y => ?_⟩
  set z := mulR (aE H σ) y with hz
  have hσI : σ ∈ Icc (s - 1) (s + 1) := by
    rw [abs_lt] at hσ
    constructor <;> linarith [hσ.1, hσ.2]
  have hsum : ∑ i, ∑ j, ‖aE H (-σ) i j‖ ≤ L' := by
    have := hL σ hσI
    rw [Real.norm_of_nonneg (by positivity)] at this
    exact this.trans (le_max_left _ _)
  have hy : ‖y‖ ≤ L' * ‖z‖ := by
    have hyz : y = mulR (aE H (-σ)) z := by rw [hz, mulR_mul, aE_mul_neg', mulR_one]
    calc ‖y‖ = ‖mulR (aE H (-σ)) z‖ := by rw [← hyz]
      _ ≤ (∑ i, ∑ j, ‖aE H (-σ) i j‖) * ‖z‖ := norm_mulR_le _ _
      _ ≤ L' * ‖z‖ := mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
  have hg : ‖gs c z‖ ≤ Real.exp (-(c * ‖z‖ ^ 2)) := by
    rw [gs, Complex.norm_exp]
    simp only [Complex.neg_re, Complex.ofReal_re]
    exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left (PositivityTheory.Rg.Sw.AbsSt.DF.sq_norm_le_sum z) hc.le))
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hmain : ‖evX P z * gs c z‖ ≤ Cp * Cd * (1 + ‖z‖) ^ (-r) := by
    rw [norm_mul]
    calc ‖evX P z‖ * ‖gs c z‖ ≤ (Cp * (1 + ‖z‖) ^ k) * Real.exp (-(c * ‖z‖ ^ 2)) :=
          mul_le_mul (hP z) hg (norm_nonneg _) (by positivity)
      _ = Cp * ((1 + ‖z‖) ^ k * Real.exp (-(c * ‖z‖ ^ 2))) := by ring
      _ ≤ Cp * (Cd * (1 + ‖z‖) ^ (-r)) := mul_le_mul_of_nonneg_left (hdec _ hz0) hCp
      _ = _ := by ring
  have hcmp : (1 + ‖z‖) ^ (-r) ≤ L' ^ r * (1 + ‖y‖) ^ (-r) := by
    have h1 : 1 + ‖y‖ ≤ L' * (1 + ‖z‖) := by nlinarith
    have h2 : (L' * (1 + ‖z‖)) ^ (-r) ≤ (1 + ‖y‖) ^ (-r) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
    rw [Real.mul_rpow hL'0 (by positivity)] at h2
    calc (1 + ‖z‖) ^ (-r) = L' ^ r * (L' ^ (-r) * (1 + ‖z‖) ^ (-r)) := by
          rw [← mul_assoc, ← Real.rpow_add (by linarith), add_neg_cancel, Real.rpow_zero, one_mul]
      _ ≤ L' ^ r * (1 + ‖y‖) ^ (-r) := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hL'0 r)
  calc ‖evX P z * gs c z‖ ≤ Cp * Cd * (1 + ‖z‖) ^ (-r) := hmain
    _ ≤ Cp * Cd * (L' ^ r * (1 + ‖y‖) ^ (-r)) :=
        mul_le_mul_of_nonneg_left hcmp (mul_nonneg hCp hCd)
    _ = _ := by ring

end PositivityTheory.Rg.Sw.AbsSt.SDM
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SplitMul
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

theorem split_mul (x₀ : G) (y k : GR n) : x₀ * ι y * ι k = x₀ * ι (y * k) := by
  rw [mul_assoc, ← map_mul]

theorem cont_hz (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ)
    (z : ℂ) (b : GR n) (x : G) : Continuous fun k : KR n => hz Ht sec s₀ z 1 (x * ι ((k : GR n) * b)) := by
  obtain ⟨x₀, y, S, r, hr, hx, h⟩ := hG.split x
  subst hx
  have hfun : (fun k : KR n => hz Ht sec s₀ z 1 (x₀ * ι y * ι ((k : GR n) * b))) =
      fun k : KR n => ((r * hLoc (y * ((k : GR n) * b)) : ℝ) : ℂ) ^ (z - s₀) *
        (S * sL 1 (y * ((k : GR n) * b))) := by
    funext k
    unfold hz
    rw [split_mul, (h _).1, (h _).2]
  rw [hfun]
  have hcy : Continuous fun k : KR n => y * ((k : GR n) * b) :=
    continuous_const.mul (continuous_subtype_val.mul continuous_const)
  refine Continuous.mul ?_ (continuous_const.mul ((hL.cont 1).comp hcy))
  refine Continuous.cpow ?_ continuous_const
    (fun k => Complex.ofReal_mem_slitPlane.2 (mul_pos hr (hLoc_pos hD _)))
  exact Complex.continuous_ofReal.comp (continuous_const.mul ((continuous_hLoc hD).comp hcy))

theorem pointId [MeasurableSpace (KR n)] (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) {ν : Measure (KR n)} {κ : KR n → ℂ} {N : ℕ}
    {yy : Fin N → GR n} {QQ : Fin N → PX m n} {M : ℂ → Matrix (Fin N) (Fin N) ℂ}
    (hMid : ∀ (w : ℂ) (i : Fin N) (y' : GR n), ∫ k, κ k * ((hLoc (y' * (k : GR n) * yy i) : ℂ) ^ w *
        F0 p q e (y' * (k : GR n) * yy i)) ∂ν = (hLoc y' : ℂ) ^ w * ∑ j, M w i j * sL (QQ j) y')
    (z : ℂ) (i : Fin N) (x : G) :
    ∫ k, κ k * hz Ht sec s₀ z 1 (x * ι ((k : GR n) * yy i)) ∂ν = ∑ j, M (z - s₀) i j * hz Ht sec s₀ z (QQ j) x := by
  obtain ⟨x₀, y, S, r, hr, hx, h⟩ := hG.split x
  subst hx
  have key : ∀ (P : PX m n) (g : GR n), hz Ht sec s₀ z P (x₀ * ι g) =
      (r : ℂ) ^ (z - s₀) * S * ((hLoc g : ℂ) ^ (z - s₀) * sL P g) := by
    intro P g
    unfold hz
    rw [(h g).1, (h g).2, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hr.le (hLoc_pos hD g).le]
    ring
  have hx' : ∀ k : KR n, x₀ * ι y * ι ((k : GR n) * yy i) = x₀ * ι (y * (k : GR n) * yy i) := by
    intro k
    rw [split_mul, mul_assoc]
  simp_rw [hx', key, hL.vac]
  simp only [mul_left_comm (κ _) ((r : ℂ) ^ (z - s₀) * S)]
  rw [integral_const_mul, hMid (z - s₀) i y, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

end PositivityTheory.Rg.Sw.AbsSt.Far
end
end

