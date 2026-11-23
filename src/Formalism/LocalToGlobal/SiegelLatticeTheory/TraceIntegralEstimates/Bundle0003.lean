module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SchurTensRep

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsFolnerExp
section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

section General

variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]

private theorem norm_eq_of_inner_self_eq_inner_self_lemma {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {a b : E} (h : ⟪a, a⟫_ℂ = ⟪b, b⟫_ℂ) : ‖a‖ = ‖b‖ := by
  have h2 : ‖a‖ ^ 2 = ‖b‖ ^ 2 := by
    have h' := h
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h'
    exact_mod_cast h'
  nlinarith [norm_nonneg a, norm_nonneg b]

end General

section Main

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

def gvec (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (x : G) :
    PiLp 2 (fun _ : Fin (Module.finrank ℂ V) => HH) :=
  WithLp.toLp 2 (fun i => ⟪W x, stdOrthonormalBasis ℂ V i⟫_ℂ • σ x w)

def Fk (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (z z' q : G) : ℂ :=
  ⟪W (q * z'), W z⟫_ℂ * ⟪σ z w, σ (q * z') w⟫_ℂ

theorem fol_rep_norm {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (x : G) (a : HH) : ‖σ x a‖ = ‖a‖ := by
  obtain ⟨-, -, hin, -⟩ := id hσ
  exact norm_eq_of_inner_self_eq_inner_self_lemma (hin x a a)

theorem fol_rep_mul {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (x y : G) (a : HH) :
    σ (x * y) a = σ x (σ y a) := by
  obtain ⟨-, hmul, -, -⟩ := id hσ
  calc σ (x * y) a = (σ x * σ y) a := by rw [hmul x y]
    _ = σ x (σ y a) := rfl

theorem W_inner_trans {S : Set G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    {s : G} (hs : s ∈ S) (x y : G) : ⟪W (s * x), W (s * y)⟫_ℂ = ⟪W x, W y⟫_ℂ := by
  rw [hWeq s hs x, hWeq s hs y, hτu s hs]

theorem W_norm_trans {S : Set G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    {s : G} (hs : s ∈ S) (x : G) : ‖W (s * x)‖ = ‖W x‖ :=
  norm_eq_of_inner_self_eq_inner_self_lemma (W_inner_trans hWeq hτu hs x x)

theorem gvec_continuous {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {W : G → V} (hWc : Continuous W) :
    Continuous (gvec σ w W) := by
  obtain ⟨-, -, -, hσc⟩ := id hσ
  have hi : ∀ i : Fin (Module.finrank ℂ V),
      Continuous fun x => ⟪W x, stdOrthonormalBasis ℂ V i⟫_ℂ • σ x w :=
    fun i => (hWc.inner continuous_const).smul (hσc w)
  show Continuous fun x =>
    (WithLp.toLp 2 (fun i => ⟪W x, stdOrthonormalBasis ℂ V i⟫_ℂ • σ x w) :
      PiLp 2 (fun _ : Fin (Module.finrank ℂ V) => HH))
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi hi)

theorem gvec_norm {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {w : HH} (hw : ‖w‖ = 1) (W : G → V) (x : G) :
    ‖gvec σ w W x‖ = ‖W x‖ := by
  have hn : ‖σ x w‖ = 1 := by rw [(fol_rep_norm hσ), hw]
  have key : ∑ i, ‖⟪W x, stdOrthonormalBasis ℂ V i⟫_ℂ‖ ^ 2 = ‖W x‖ ^ 2 := by
    exact (stdOrthonormalBasis ℂ V).sum_sq_norm_inner_left (W x)
  have hs : ‖gvec σ w W x‖ ^ 2 = ‖W x‖ ^ 2 := by
    rw [← key]
    rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_congr rfl fun i _ => by simp [gvec, norm_smul, hn]
  nlinarith [norm_nonneg (gvec σ w W x), norm_nonneg (W x)]

theorem gvec_inner (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (x y : G) :
    ⟪gvec σ w W x, gvec σ w W y⟫_ℂ = ⟪W y, W x⟫_ℂ * ⟪σ x w, σ y w⟫_ℂ := by
  have hb : ∑ i, ⟪W y, stdOrthonormalBasis ℂ V i⟫_ℂ * ⟪stdOrthonormalBasis ℂ V i, W x⟫_ℂ = ⟪W y, W x⟫_ℂ := by
    exact (stdOrthonormalBasis ℂ V).sum_inner_mul_inner (W y) (W x)
  rw [← hb, Finset.sum_mul]
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [gvec, PiLp.toLp_apply, inner_smul_left, inner_smul_right, inner_conj_symm]
  ring

theorem Fk_continuous {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {W : G → V} (hWc : Continuous W)
    {X : Type} [TopologicalSpace X] {a b c : X → G} (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    Continuous (fun x => Fk σ w W (a x) (b x) (c x)) := by
  obtain ⟨-, -, -, hσc⟩ := id hσ
  have hcb : Continuous fun x => c x * b x := hc.mul hb
  have h1 : Continuous fun x => W (c x * b x) := hWc.comp hcb
  have h2 : Continuous fun x => W (a x) := hWc.comp ha
  have h3 : Continuous fun x => σ (a x) w := (hσc w).comp ha
  have h4 : Continuous fun x => σ (c x * b x) w := (hσc w).comp hcb
  show Continuous fun x => ⟪W (c x * b x), W (a x)⟫_ℂ * ⟪σ (a x) w, σ (c x * b x) w⟫_ℂ
  exact (h1.inner h2).mul (h3.inner h4)

theorem Fk_bound {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {w : HH} (hw : ‖w‖ = 1) {S : Set G}
    {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (z z' : G) {q : G} (hq : q ∈ S) : ‖Fk σ w W z z' q‖ ≤ ‖W z‖ * ‖W z'‖ := by
  have h1 : ‖⟪W (q * z'), W z⟫_ℂ‖ ≤ ‖W z‖ * ‖W z'‖ := by
    calc ‖⟪W (q * z'), W z⟫_ℂ‖ ≤ ‖W (q * z')‖ * ‖W z‖ := norm_inner_le_norm _ _
      _ = ‖W z‖ * ‖W z'‖ := by rw [W_norm_trans hWeq hτu hq z', mul_comm]
  have h2 : ‖⟪σ z w, σ (q * z') w⟫_ℂ‖ ≤ 1 := by
    calc ‖⟪σ z w, σ (q * z') w⟫_ℂ‖ ≤ ‖σ z w‖ * ‖σ (q * z') w‖ := norm_inner_le_norm _ _
      _ = 1 := by rw [(fol_rep_norm hσ), (fol_rep_norm hσ), hw, mul_one]
  show ‖⟪W (q * z'), W z⟫_ℂ * ⟪σ z w, σ (q * z') w⟫_ℂ‖ ≤ ‖W z‖ * ‖W z'‖
  rw [norm_mul]
  calc ‖⟪W (q * z'), W z⟫_ℂ‖ * ‖⟪σ z w, σ (q * z') w⟫_ℂ‖ ≤ (‖W z‖ * ‖W z'‖) * 1 :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = ‖W z‖ * ‖W z'‖ := mul_one _

theorem kF {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {S : Set G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hSinv : ∀ a ∈ S, a⁻¹ ∈ S)
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (z z' : G) {s t : G} (hs : s ∈ S) :
    ⟪W (t⁻¹ * z'), W (s⁻¹ * z)⟫_ℂ * ⟪σ (s⁻¹ * z) w, σ (t⁻¹ * z') w⟫_ℂ = Fk σ w W z z' (s * t⁻¹) := by
  obtain ⟨-, -, hin, -⟩ := id hσ
  have e1 : ⟪W (t⁻¹ * z'), W (s⁻¹ * z)⟫_ℂ = ⟪W (s * t⁻¹ * z'), W z⟫_ℂ := by
    rw [← W_inner_trans hWeq hτu hs (t⁻¹ * z') (s⁻¹ * z), mul_assoc, mul_inv_cancel_left]
  have e2 : ⟪σ (s⁻¹ * z) w, σ (t⁻¹ * z') w⟫_ℂ = ⟪σ z w, σ (s * t⁻¹ * z') w⟫_ℂ := by
    rw [← hin s (σ (s⁻¹ * z) w) (σ (t⁻¹ * z') w), ← (fol_rep_mul hσ), ← (fol_rep_mul hσ), mul_inv_cancel_left,
      mul_assoc]
  rw [e1, e2]
  rfl

end Main

end Formalism.L2.S.Pv.EnergyAbs
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsRep
section
noncomputable section

open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

def kG (σ : G → (HH →L[ℂ] HH)) (d : ℝ) (w : HH) (W : G → V) (W' : G → V') (γ : G) (q : G × G) :
    V' →L[ℂ] V :=
  ((d : ℂ) * ⟪σ q.1 w, σ γ (σ q.2 w)⟫_ℂ) • rk1A (W q.1) (W' q.2)

theorem rankOne_eq_smulRightL (a : V) (b : V') :
    rk1A a b = ContinuousLinearMap.smulRightL ℂ V' V (innerSL ℂ b) a := rfl

theorem norm_rk1A_le (a : V) (b : V') : ‖rk1A a b‖ ≤ ‖a‖ * ‖b‖ := by
  have h : ‖rk1A a b‖ = ‖innerSL ℂ b‖ * ‖a‖ := ContinuousLinearMap.norm_smulRight_apply _ _
  rw [h, innerSL_apply_norm, mul_comm]

theorem continuous_rk1A {α : Type*} [TopologicalSpace α] {f : α → V} {g : α → V'} (hf : Continuous f)
    (hg : Continuous g) : Continuous (fun x => rk1A (f x) (g x)) := by
  simp only [rankOne_eq_smulRightL]
  exact ((ContinuousLinearMap.smulRightL ℂ V' V).continuous.comp
    ((innerSL ℂ).continuous.comp hg)).clm_apply hf

theorem continuous_kG {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (d : ℝ) (w : HH) {W : G → V} {W' : G → V'}
    (hW : Continuous W) (hW' : Continuous W') (γ : G) : Continuous (kG σ d w W W' γ) := by
  obtain ⟨-, -, -, hc⟩ := hσ
  have h1 : Continuous fun q : G × G => σ q.1 w := (hc w).comp continuous_fst
  have h2 : Continuous fun q : G × G => σ γ (σ q.2 w) :=
    (σ γ).continuous.comp ((hc w).comp continuous_snd)
  exact (continuous_const.mul (Continuous.inner (𝕜 := ℂ) h1 h2)).smul
    (continuous_rk1A (hW.comp continuous_fst) (hW'.comp continuous_snd))

theorem integral_kG {μ : Measure G} [μ.IsMulLeftInvariant] [SFinite μ] {σ : G → (HH →L[ℂ] HH)}
    (hσ : IsUnitRep σ) {d : ℝ} {w : HH} {S : Set G} {τ : G → (V →L[ℂ] V)} {ν : Measure G} {W : G → V}
    (hW : IsWAbs μ σ d w S τ ν W) (W' : G → V') (γ : G) (hi : Integrable (kG σ d w W W' γ) (μ.prod μ)) :
    ∫ q, kG σ d w W W' γ q ∂(μ.prod μ) = ∫ x, rk1A (W x) (W' (γ⁻¹ * x)) ∂μ := by
  obtain ⟨-, hmul, hunit, -⟩ := hσ
  obtain ⟨-, -, -, -, -, hrep, -⟩ := hW
  have hF : ∀ x : G, Integrable (fun g => ((d : ℂ) * ⟪σ g w, σ x w⟫_ℂ) • W g) μ ∧
      ∫ g, ((d : ℂ) * ⟪σ g w, σ x w⟫_ℂ) • W g ∂μ = W x := by
    intro x
    obtain ⟨hI, hE⟩ := hrep x
    have hin : ∀ g, ⟪σ g w, σ x w⟫_ℂ = conj ⟪w, σ (x⁻¹ * g) w⟫_ℂ := by
      intro g
      rw [inner_conj_symm, ← hunit x (σ (x⁻¹ * g) w) w, ← ContinuousLinearMap.mul_apply, ← hmul,
        mul_inv_cancel_left]
    have heq : (fun g => ((d : ℂ) * ⟪σ g w, σ x w⟫_ℂ) • W g)
        = fun g => (fun y => ((d : ℂ) * conj ⟪w, σ y w⟫_ℂ) • W (x * y)) (x⁻¹ * g) := by
      funext g
      simp only [mul_inv_cancel_left, hin]
    rw [heq]
    exact ⟨hI.comp_mul_left x⁻¹,
      (integral_mul_left_eq_self (fun y => ((d : ℂ) * conj ⟪w, σ y w⟫_ℂ) • W (x * y)) x⁻¹).trans hE⟩
  rw [integral_prod_symm _ hi]
  have hin : ∀ g' : G, ∫ g, kG σ d w W W' γ (g, g') ∂μ = rk1A (W (γ * g')) (W' g') := by
    intro g'
    have hk : (fun g => kG σ d w W W' γ (g, g'))
        = fun g => (ContinuousLinearMap.smulRightL ℂ V' V (innerSL ℂ (W' g')))
          (((d : ℂ) * ⟪σ g w, σ (γ * g') w⟫_ℂ) • W g) := by
      funext g
      simp only [kG, map_smul, ← rankOne_eq_smulRightL, hmul, ContinuousLinearMap.mul_apply]
    rw [hk, ContinuousLinearMap.integral_comp_comm _ (hF _).1, (hF _).2, ← rankOne_eq_smulRightL]
  simp_rw [hin]
  have h := integral_mul_left_eq_self (μ := μ) (fun x => rk1A (W x) (W' (γ⁻¹ * x))) γ
  simp only [inv_mul_cancel_left] at h
  exact h

end Formalism.L2.S.Pv.EnergyAbs
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SchurTensSpan
section
noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.SchurTens

open Formalism.L2.SG.Pf.EnergyAbs

section Gen

variable {K : Type*} [MeasurableSpace K] {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]

def SP (m : Measure K) (σs : K → (Hs →L[ℂ] Hs)) (D : ℝ) (a b a' b' : Hs) : Prop :=
  Integrable (fun x => ⟪b, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) m ∧
    ∫ x, ⟪b, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ ∂m = ⟪a', a⟫_ℂ * ⟪b, b'⟫_ℂ / (D : ℂ)

variable {m : Measure K} {σs : K → (Hs →L[ℂ] Hs)} {D : ℝ}

theorem integrable_conj' {f : K → ℂ} (hf : Integrable f m) : Integrable (fun x => conj (f x)) m := by
  exact hf.mono (Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (ae_of_all _ fun x => by simp)

theorem SP_swap {a b a' b' : Hs} (h : SP m σs D a b a' b') : SP m σs D a' b' a b := by
  unfold SP at h ⊢
  have e : (fun x => ⟪b', σs x a'⟫_ℂ * conj ⟪b, σs x a⟫_ℂ) =
      fun x => conj (⟪b, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) := by
    funext x
    rw [map_mul, Complex.conj_conj]
    ring
  rw [e]
  refine ⟨integrable_conj' h.1, ?_⟩
  rw [integral_conj, h.2]
  rw [map_div₀, map_mul, Complex.conj_ofReal, inner_conj_symm, inner_conj_symm]

theorem SP_zero_a (b a' b' : Hs) : SP m σs D 0 b a' b' := by
  unfold SP
  simp

theorem SP_add_a {a₁ a₂ b a' b' : Hs} (h₁ : SP m σs D a₁ b a' b') (h₂ : SP m σs D a₂ b a' b') :
    SP m σs D (a₁ + a₂) b a' b' := by
  unfold SP at h₁ h₂ ⊢
  have e : (fun x => ⟪b, σs x (a₁ + a₂)⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) =
      fun x => ⟪b, σs x a₁⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ + ⟪b, σs x a₂⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ := by
    funext x
    rw [map_add (f := _), inner_add_right, add_mul]
  rw [e]
  refine ⟨h₁.1.add h₂.1, ?_⟩
  rw [integral_add h₁.1 h₂.1, h₁.2, h₂.2, inner_add_right]
  ring

theorem SP_smul_a (c : ℂ) {a b a' b' : Hs} (h : SP m σs D a b a' b') : SP m σs D (c • a) b a' b' := by
  unfold SP at h ⊢
  have e : (fun x => ⟪b, σs x (c • a)⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) =
      fun x => c * (⟪b, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) := by
    funext x
    rw [map_smul, inner_smul_right, mul_assoc]
  rw [e]
  refine ⟨h.1.const_mul c, ?_⟩
  rw [integral_const_mul]
  rw [h.2, inner_smul_right]
  ring

theorem SP_zero_b (a a' b' : Hs) : SP m σs D a 0 a' b' := by
  unfold SP
  simp

theorem SP_add_b {a b₁ b₂ a' b' : Hs} (h₁ : SP m σs D a b₁ a' b') (h₂ : SP m σs D a b₂ a' b') :
    SP m σs D a (b₁ + b₂) a' b' := by
  unfold SP at h₁ h₂ ⊢
  have e : (fun x => ⟪b₁ + b₂, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) =
      fun x => ⟪b₁, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ + ⟪b₂, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ := by
    funext x
    rw [inner_add_left, add_mul]
  rw [e]
  refine ⟨h₁.1.add h₂.1, ?_⟩
  rw [integral_add h₁.1 h₂.1, h₁.2, h₂.2, inner_add_left]
  ring

theorem SP_smul_b (c : ℂ) {a b a' b' : Hs} (h : SP m σs D a b a' b') : SP m σs D a (c • b) a' b' := by
  unfold SP at h ⊢
  have e : (fun x => ⟪c • b, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) =
      fun x => conj c * (⟪b, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) := by
    funext x
    rw [inner_smul_left, mul_assoc]
  rw [e]
  refine ⟨h.1.const_mul _, ?_⟩
  rw [integral_const_mul]
  rw [h.2, inner_smul_left]
  ring

private theorem mem_span_of_closed_lemma {P : Hs → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (c : ℂ) x, P x → P (c • x)) {E : Set Hs} (hE : ∀ a ∈ E, P a) :
    ∀ a ∈ Submodule.span ℂ E, P a := by
  intro a ha
  let S : Submodule ℂ Hs :=
    { carrier := {x | P x}
      add_mem' := fun {x y} hx hy => hadd x y hx hy
      zero_mem' := h0
      smul_mem' := fun c {x} hx => hsmul c x hx }
  have hle : Submodule.span ℂ E ≤ S := Submodule.span_le.mpr fun x hx => hE x hx
  exact hle ha

theorem SP_span {E : Set Hs} (h : ∀ a ∈ E, ∀ b ∈ E, ∀ a' ∈ E, ∀ b' ∈ E, SP m σs D a b a' b') :
    ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ Submodule.span ℂ E, ∀ a' ∈ Submodule.span ℂ E,
      ∀ b' ∈ Submodule.span ℂ E, SP m σs D a b a' b' := by
  have s1 : ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ E, ∀ a' ∈ E, ∀ b' ∈ E, SP m σs D a b a' b' :=
    mem_span_of_closed_lemma (P := fun a => ∀ b ∈ E, ∀ a' ∈ E, ∀ b' ∈ E, SP m σs D a b a' b')
      (fun b _ a' _ b' _ => SP_zero_a b a' b')
      (fun x y hx hy b hb a' ha' b' hb' => SP_add_a (hx b hb a' ha' b' hb') (hy b hb a' ha' b' hb'))
      (fun c x hx b hb a' ha' b' hb' => SP_smul_a c (hx b hb a' ha' b' hb'))
      (fun a ha => h a ha)
  have s2 : ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ Submodule.span ℂ E, ∀ a' ∈ E, ∀ b' ∈ E,
      SP m σs D a b a' b' := by
    intro a ha
    exact mem_span_of_closed_lemma (P := fun b => ∀ a' ∈ E, ∀ b' ∈ E, SP m σs D a b a' b')
      (fun a' _ b' _ => SP_zero_b a a' b')
      (fun x y hx hy a' ha' b' hb' => SP_add_b (hx a' ha' b' hb') (hy a' ha' b' hb'))
      (fun c x hx a' ha' b' hb' => SP_smul_b c (hx a' ha' b' hb'))
      (fun b hb => s1 a ha b hb)
  have s3 : ∀ a' ∈ Submodule.span ℂ E, ∀ b' ∈ E, ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ Submodule.span ℂ E,
      SP m σs D a' b' a b :=
    mem_span_of_closed_lemma
      (P := fun a' => ∀ b' ∈ E, ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ Submodule.span ℂ E, SP m σs D a' b' a b)
      (fun b' _ a _ b _ => SP_zero_a b' a b)
      (fun x y hx hy b' hb' a ha b hb => SP_add_a (hx b' hb' a ha b hb) (hy b' hb' a ha b hb))
      (fun c x hx b' hb' a ha b hb => SP_smul_a c (hx b' hb' a ha b hb))
      (fun a' ha' b' hb' a ha b hb => SP_swap (s2 a ha b hb a' ha' b' hb'))
  have s4 : ∀ a' ∈ Submodule.span ℂ E, ∀ b' ∈ Submodule.span ℂ E, ∀ a ∈ Submodule.span ℂ E,
      ∀ b ∈ Submodule.span ℂ E, SP m σs D a' b' a b := by
    intro a' ha'
    exact mem_span_of_closed_lemma
      (P := fun b' => ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ Submodule.span ℂ E, SP m σs D a' b' a b)
      (fun a _ b _ => SP_zero_b a' a b)
      (fun x y hx hy a ha b hb => SP_add_b (hx a ha b hb) (hy a ha b hb))
      (fun c x hx a ha b hb => SP_smul_b c (hx a ha b hb))
      (fun b' hb' => s3 a' ha' b' hb')
  intro a ha b hb a' ha' b' hb'
  exact SP_swap (s4 a' ha' b' hb' a ha b hb)

end Gen

section Pure

variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, MeasurableSpace (G v)] {H : ι → Type} [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
  {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {σ : ∀ v, G v → (H v →L[ℂ] H v)} {σs : (∀ v, G v) → (Hs →L[ℂ] Hs)} {tens : (∀ v, H v) → Hs}

theorem SP_pure (μ : ∀ v, Measure (G v)) [∀ v, SigmaFinite (μ v)] (d : ι → ℝ)
    (hS : ∀ v, IsSchur (μ v) (σ v) (d v)) (h : IsTensAbs σ σs tens) (α β α' β' : ∀ v, H v) :
    SP (Measure.pi μ) σs (∏ v, d v) (tens α) (tens β) (tens α') (tens β') := by
  have hf : (fun x => ⟪tens β, σs x (tens α)⟫_ℂ * conj ⟪tens β', σs x (tens α')⟫_ℂ) =
      fun x => ∏ v, (⟪β v, σ v (x v) (α v)⟫_ℂ * conj ⟪β' v, σ v (x v) (α' v)⟫_ℂ) := by
    funext x
    rw [h.2.1, h.2.1, h.1, h.1, map_prod, ← Finset.prod_mul_distrib]
  refine ⟨?_, ?_⟩
  · rw [hf]
    exact Integrable.fintype_prod_dep fun v => ((hS v).2 (α v) (β v) (α' v) (β' v)).1
  · rw [hf, integral_fintype_prod_eq_prod (fun v y => ⟪β v, σ v y (α v)⟫_ℂ * conj ⟪β' v, σ v y (α' v)⟫_ℂ)]
    simp only [fun v => ((hS v).2 (α v) (β v) (α' v) (β' v)).2]
    rw [h.1, h.1, Finset.prod_div_distrib, Finset.prod_mul_distrib, Complex.ofReal_prod]

end Pure

end Formalism.L2.S.Pv.SchurTens
end
end

