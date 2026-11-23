module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
public import GroundTheory.HeightsAndTheta.Theta.Weil.PartialFourierAdelicPi

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.EAddRight
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G.OrthogonalVectors

open GroundTheory.Automorphic.FourierWhittaker

variable {F : Type} [Field F] [NumberField F]

private noncomputable def E (κ : Fin 2 → F) (u : Fin 2 → A F) : ℂ := ψ (rt (κ 0) * u 0 + rt (κ 1) * u 1)

private theorem E_cont (κ : Fin 2 → F) : Continuous (E κ) :=
  continuous_ψ.comp (((continuous_const).mul (continuous_apply 0)).add ((continuous_const).mul (continuous_apply 1)))

private theorem E_norm (κ : Fin 2 → F) (u : Fin 2 → A F) : ‖E κ u‖ = 1 := norm_ψ _

private theorem E_add_left (κ κ' : Fin 2 → F) (u : Fin 2 → A F) : E (κ + κ') u = E κ u * E κ' u := by
  simp only [E, ← UpperTheory.ConvolutionTheory.R2.ψ_add]
  congr 1
  simp only [Pi.add_apply, map_add (f := _)]
  ring

private theorem E_add_right (κ : Fin 2 → F) (u v : Fin 2 → A F) : E κ (u + v) = E κ u * E κ v := by
  simp only [E, ← UpperTheory.ConvolutionTheory.R2.ψ_add]
  congr 1
  simp only [Pi.add_apply]
  ring

private theorem E_zero (u : Fin 2 → A F) : E (0 : Fin 2 → F) u = 1 := by
  simp [E]

private theorem E_per (κ : Fin 2 → F) : ∀ ξ ∈ vecLattice F (Fin 2), ∀ x, E κ (ξ + x) = E κ x := by
  intro ξ hξ x
  obtain ⟨η, rfl⟩ := mem_vecLattice.1 hξ
  rw [E_add_right]
  have : E κ (fun i => algebraMap F (A F) (η i)) = 1 := by
    simp only [E]
    rw [← map_mul, ← map_mul, ← map_add (f := _)]
    exact ψ_rt _
  rw [this, one_mul]

private theorem exists_ne (κ : Fin 2 → F) (hκ : κ ≠ 0) : ∃ a, E κ a ≠ 1 := by
  obtain ⟨x, hx⟩ : ∃ x, adelicChar F x ≠ 1 := by
    by_contra h
    push_neg at h
    exact adelicChar_ne_one (K := F) (DFunLike.ext _ _ fun x => by simpa using h x)
  have hx' : ψ x ≠ 1 := fun h => hx (Circle.ext (by simpa [ψ] using h))
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hκ
  have hr : rt (κ i) * rt (κ i)⁻¹ = (1 : A F) := by
    rw [← map_mul, mul_inv_cancel₀ hi, map_one]
  refine ⟨Pi.single i (rt (κ i)⁻¹ * x), ?_⟩
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue] at hr ⊢
    simp only [E, Pi.single_eq_same, ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, add_zero,
      ← mul_assoc, hr, one_mul, Fin.isValue, one_ne_zero]
    exact hx'
  · simp only [Fin.mk_one, Fin.isValue] at hr ⊢
    simp only [E, Pi.single_eq_same, ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, zero_add,
      ← mul_assoc, hr, one_mul, Fin.isValue, one_ne_zero]
    exact hx'

private theorem E_int (κ : Fin 2 → F) (hκ : κ ≠ 0) : ∫ u in FS2 F, E κ u ∂(adeleMeasurePi F) = 0 := by
  obtain ⟨a, ha⟩ := exists_ne κ hκ
  change ∫ u in vecDomain F (Fin 2), E κ u ∂(vecMeasure F (Fin 2)) = 0
  have h := setIntegral_comp_add (K := F) (ι := Fin 2) a (h := E κ) (E_per κ)
  simp only [E_add_right] at h
  rw [integral_mul_const] at h
  have h1 : (∫ u in vecDomain F (Fin 2), E κ u ∂(vecMeasure F (Fin 2))) * (E κ a - 1) = 0 := by
    rw [mul_sub, h, mul_one, sub_self]
  exact (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 ha)

private theorem vol : (adeleMeasurePi F).restrict (FS2 F) Set.univ = 1 := by
  rw [Measure.restrict_apply_univ]
  exact vecMeasure_vecDomain

private theorem fin_inst : IsFiniteMeasure ((adeleMeasurePi F).restrict (FS2 F)) :=
  ⟨by rw [vol]; exact ENNReal.one_lt_top⟩

private theorem int_const (a : ℝ) : ∫ _ in FS2 F, a ∂(adeleMeasurePi (ι := Fin 2) F) = a := by
  rw [integral_const, measureReal_def, vol]
  simp

private theorem E_int_zero : ∫ u in FS2 F, E (0 : Fin 2 → F) u ∂(adeleMeasurePi F) = 1 := by
  simp only [E_zero]
  rw [integral_const, measureReal_def, vol]
  simp

private theorem cont_int {g : (Fin 2 → A F) → ℂ} (hg : Continuous g) : IntegrableOn g (FS2 F) (adeleMeasurePi F) := by
  obtain ⟨C, hC, hs⟩ := exists_isCompact_superset_vecDomain (K := F) (ι := Fin 2)
  exact (hg.continuousOn.integrableOn_compact (μ := vecMeasure F (Fin 2)) hC).mono_set hs

private theorem core (κ₀ : Fin 2 → F) (L : (Fin 2 → F) → Fin 2 → F) (c₀ : ℂ) (c : (Fin 2 → F) → ℂ)
    (hc : Summable fun ξ => ‖c ξ‖) (Φ : (Fin 2 → A F) → ℂ) (hΦ : ∀ u, Φ u = c₀ + ∑' ξ, E (L ξ) u * c ξ) :
    IntegrableOn (fun u => Φ u * E κ₀ u) (FS2 F) (adeleMeasurePi F) ∧
    HasSum (fun ξ => (∫ u in FS2 F, E (κ₀ + L ξ) u ∂(adeleMeasurePi F)) * c ξ)
      ((∫ u in FS2 F, Φ u * E κ₀ u ∂(adeleMeasurePi F)) - c₀ * ∫ u in FS2 F, E κ₀ u ∂(adeleMeasurePi F)) := by
  haveI := countable_numberField F
  haveI := fin_inst (F := F)
  set g : (Fin 2 → F) → (Fin 2 → A F) → ℂ := fun ξ u => E (κ₀ + L ξ) u * c ξ with hgdef
  have hgc : ∀ ξ, Continuous (g ξ) := fun ξ => (E_cont _).mul continuous_const
  have hgn : ∀ ξ u, ‖g ξ u‖ = ‖c ξ‖ := fun ξ u => by simp [hgdef, norm_mul, E_norm]
  have hsum : ∀ u, Summable fun ξ => E (L ξ) u * c ξ := fun u =>
    Summable.of_norm (by simpa [norm_mul, E_norm] using hc)
  have e : ∀ u, Φ u * E κ₀ u = c₀ * E κ₀ u + ∑' ξ, g ξ u := by
    intro u
    rw [hΦ, add_mul, ← tsum_mul_right]
    congr 1
    refine tsum_congr fun ξ => ?_
    simp only [hgdef, E_add_left]
    ring
  have hcont : Continuous fun u => ∑' ξ, g ξ u := continuous_tsum hgc hc fun ξ u => (hgn ξ u).le
  have hI := cont_int hcont
  have hT := cont_int (E_cont κ₀)
  have hT' : IntegrableOn (fun u => c₀ * E κ₀ u) (FS2 F) (adeleMeasurePi F) := hT.const_mul c₀
  refine ⟨?_, ?_⟩
  · simp only [e]
    exact hT'.add hI
  · have hS := hasSum_integral_of_summable_integral_norm (μ := (adeleMeasurePi F).restrict (FS2 F))
      (F := g) (fun ξ => cont_int (hgc ξ)) (by
        simp only [hgn]
        simpa only [int_const] using hc)
    have h2 : (∫ u in FS2 F, Φ u * E κ₀ u ∂(adeleMeasurePi F)) - c₀ * ∫ u in FS2 F, E κ₀ u ∂(adeleMeasurePi F) =
        ∫ u in FS2 F, ∑' ξ, g ξ u ∂(adeleMeasurePi F) := by
      simp only [e]
      rw [integral_add hT' hI, integral_const_mul]
      ring
    rw [h2]
    simpa only [hgdef, integral_mul_const] using hS

end UpperTheory.ConvolutionTheory.R2.G.OrthogonalVectors

open UpperTheory.ConvolutionTheory.R2.G.OrthogonalVectors in
theorem UpperTheory.ConvolutionTheory.R2.G.orth :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F), δ ≠ 0 → ∀ (c₀ : ℂ) (c : (Fin 2 → F) → ℂ) (Φ : (Fin 2 → A F) → ℂ), Summable (fun ξ => ‖c ξ‖) →
    (∀ u, Φ u = c₀ + ∑' ξ, chi δ ξ u * c ξ) → IntegrableOn Φ (FS2 F) (adeleMeasurePi F) ∧
    IntegrableOn (fun u => Φ u * ψ (2 * u 0)) (FS2 F) (adeleMeasurePi F) ∧
    ∫ u in FS2 F, Φ u ∂(adeleMeasurePi F) = c₀ + c 0 ∧ ∫ u in FS2 F, Φ u * ψ (2 * u 0) ∂(adeleMeasurePi F) = c ![1, 0] := by
  intro F _ _ δ hδ c₀ c Φ hc hΦ
  set L : (Fin 2 → F) → Fin 2 → F := fun ξ => ![-(2 * ξ 0), 2 * δ * ξ 1] with hL
  have hchi : ∀ ξ u, chi δ ξ u = E (L ξ) u := by
    intro ξ u
    simp only [chi, E, hL]
    congr 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_neg, map_mul, map_ofNat]
    ring
  have hΦ' : ∀ u, Φ u = c₀ + ∑' ξ, E (L ξ) u * c ξ := fun u => by
    rw [hΦ]; simp only [hchi]
  set κ : Fin 2 → F := ![2, 0] with hκ
  have hψ : ∀ u : Fin 2 → A F, ψ (2 * u 0) = E κ u := by
    intro u
    have h2A : rt (2 : F) = (2 : A F) := map_ofNat _ 2
    simp only [E, hκ]
    congr 1
    simp [h2A]
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hκ0 : κ ≠ 0 := fun h => h2 (by simpa [hκ] using congrFun h 0)
  obtain ⟨i0, s0⟩ := core 0 L c₀ c hc Φ hΦ'
  obtain ⟨i1, s1⟩ := core κ L c₀ c hc Φ hΦ'
  simp only [E_zero, mul_one, zero_add] at i0 s0
  simp only [← hψ] at i1
  refine ⟨i0, i1, ?_, ?_⟩
  · have t : HasSum (fun ξ => (∫ u in FS2 F, E (L ξ) u ∂(adeleMeasurePi F)) * c ξ) (c 0) := by
      have hL0 : L 0 = 0 := by
        ext i; fin_cases i <;> simp [hL]
      have := hasSum_single (f := fun ξ => (∫ u in FS2 F, E (L ξ) u ∂(adeleMeasurePi F)) * c ξ) (0 : Fin 2 → F) (fun ξ hξ => by
        have hne : L ξ ≠ 0 := fun h => hξ (by
          have a0 := congrFun h 0
          have a1 := congrFun h 1
          simp only [hL, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, neg_eq_zero, mul_eq_zero, h2, hδ, false_or] at a0 a1
          ext i; fin_cases i
          · exact a0
          · exact a1)
        rw [E_int _ hne, zero_mul])
      simpa only [hL0, E_int_zero, one_mul] using this
    have e1 := s0.unique t
    have e2 : ∫ u in FS2 F, (1 : ℂ) ∂(adeleMeasurePi F) = 1 := by
      simpa only [E_zero] using E_int_zero (F := F)
    rw [e2, mul_one] at e1
    rw [sub_eq_iff_eq_add] at e1
    rw [e1, add_comm]
  · have t : HasSum (fun ξ => (∫ u in FS2 F, E (κ + L ξ) u ∂(adeleMeasurePi F)) * c ξ) (c ![1, 0]) := by
      have hL0 : κ + L ![1, 0] = 0 := by
        ext i; fin_cases i <;> simp [hL, hκ]
      have := hasSum_single (f := fun ξ => (∫ u in FS2 F, E (κ + L ξ) u ∂(adeleMeasurePi F)) * c ξ) (![1, 0] : Fin 2 → F) (fun ξ hξ => by
        have hne : κ + L ξ ≠ 0 := fun h => hξ (by
          have a0 := congrFun h 0
          have a1 := congrFun h 1
          simp only [hL, hκ, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, zero_add, mul_eq_zero, h2, hδ, false_or] at a0 a1
          ext i; fin_cases i
          · have : 2 * (1 - ξ 0) = 0 := by linear_combination a0
            have := (mul_eq_zero.1 this).resolve_left h2
            simpa using (sub_eq_zero.1 this).symm
          · simpa using a1)
        rw [E_int _ hne, zero_mul])
      simpa only [hL0, E_int_zero, one_mul] using this
    have e1 := s1.unique t
    rw [E_int κ hκ0, mul_zero, sub_zero] at e1
    simpa only [hψ] using e1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.FinHat
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G.FiniteFourierHat

variable {F : Type} [Field F] [NumberField F]

private theorem slice_mem {g : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ finiteSchwartzBruhatPi F (ι := Fin 4)) (v : Fin 4 → FiniteAdeleRing (𝓞 F) F) :
    (fun s => g (Function.update v 1 s)) ∈ finiteSchwartzBruhat F := by
  obtain ⟨hl, hc⟩ := hg
  have hcont : Continuous fun s : FiniteAdeleRing (𝓞 F) F => Function.update v 1 s :=
    continuous_const.update 1 continuous_id
  refine ⟨hl.comp_continuous hcont, ?_⟩
  refine HasCompactSupport.intro (hc.isCompact.image (continuous_apply 1)) fun s hs => ?_
  by_contra h
  exact hs ⟨Function.update v 1 s, subset_tsupport _ h, by simp⟩

private noncomputable def T (g : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (v : Fin 4 → FiniteAdeleRing (𝓞 F) F) : ℂ :=
  finiteFourier F (fun s => g (Function.update v 1 s)) (-(v 1))

private theorem T_tensor (h : Fin 4 → FiniteAdeleRing (𝓞 F) F → ℂ) :
    T (finiteTensor h) =
      finiteTensor ![h 0, fun x => finiteFourier F (h 1) (-x), h 2, h 3] := by
  funext v
  have hs : ∀ s, finiteTensor h (Function.update v 1 s) * (finiteAdelicChar F (s * -(v 1)) : ℂ) =
      (h 0 (v 0) * h 2 (v 2) * h 3 (v 3)) * (h 1 s * (finiteAdelicChar F (s * -(v 1)) : ℂ)) := by
    intro s
    simp [finiteTensor, Fin.prod_univ_four, Function.update_apply]
    ring
  simp only [T, finiteFourier]
  simp_rw [hs]
  rw [integral_const_mul]
  simp [finiteTensor, Fin.prod_univ_four, finiteFourier]
  ring

private theorem neg_mem {f : FiniteAdeleRing (𝓞 F) F → ℂ} (hf : f ∈ finiteSchwartzBruhat F) :
    (fun x => f (-x)) ∈ finiteSchwartzBruhat F :=
  ⟨hf.1.comp_continuous continuous_neg, hf.2.comp_homeomorph (Homeomorph.neg _)⟩

private theorem T_mem {g : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ finiteSchwartzBruhatPi F (ι := Fin 4)) :
    T g ∈ finiteSchwartzBruhatPi F (ι := Fin 4) := by
  have hsub := (finiteSchwartzBruhatPi_eq_span (K := F) (ι := Fin 4)).ge
  rw [finiteSchwartzBruhatPi_eq_span] at hg
  induction hg using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨J, a⟩, rfl⟩ := hf
    rw [T_tensor]
    refine finiteTensor_mem fun i => ?_
    fin_cases i
    · exact cosetIndicator_mem_finiteSchwartzBruhat J _
    · exact neg_mem (finiteFourier_mem_finiteSchwartzBruhat
        (cosetIndicator_mem_finiteSchwartzBruhat J _))
    · exact cosetIndicator_mem_finiteSchwartzBruhat J _
    · exact cosetIndicator_mem_finiteSchwartzBruhat J _
  | zero =>
    have : T (0 : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ) = 0 := by
      funext v
      simp [T, finiteFourier]
    rw [this]
    exact zero_mem _
  | add f₁ f₂ h₁ h₂ ih₁ ih₂ =>
    have : T (f₁ + f₂) = T f₁ + T f₂ := by
      funext v
      exact congrFun (finiteFourier_add
        (integrable_of_mem_finiteSchwartzBruhat (slice_mem (hsub h₁) v))
        (integrable_of_mem_finiteSchwartzBruhat (slice_mem (hsub h₂) v))) _
    rw [this]
    exact add_mem ih₁ ih₂
  | smul c f _ ih =>
    have : T (c • f) = c • T f := by
      funext v
      simp only [T, finiteFourier, Pi.smul_apply, smul_eq_mul, mul_assoc]
      exact integral_const_mul _ _
    rw [this]
    exact Submodule.smul_mem _ c ih

end UpperTheory.ConvolutionTheory.R2.G.FiniteFourierHat

theorem UpperTheory.ConvolutionTheory.R2.G.finHat :
    ∀ (F : Type) [Field F] [NumberField F], ∀ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4), (∀ v, Integrable (fun s => g (Function.update v 1 s)) (finiteAdeleMeasure F)) ∧
    (fun v => ∫ s, g (Function.update v 1 s) * ((finiteAdelicChar F (-(s * v 1)) : Circle) : ℂ) ∂(finiteAdeleMeasure F)) ∈ finiteSchwartzBruhatPi F (ι := Fin 4) := by
  intro F _ _ g hg
  refine ⟨fun v => integrable_of_mem_finiteSchwartzBruhat (FiniteFourierHat.slice_mem hg v), ?_⟩
  have he : (fun v => ∫ s, g (Function.update v 1 s) * ((finiteAdelicChar F (-(s * v 1)) : Circle) : ℂ) ∂(finiteAdeleMeasure F)) = FiniteFourierHat.T g := by
    funext v
    simp only [FiniteFourierHat.T, finiteFourier, mul_neg]
  rw [he]
  exact FiniteFourierHat.T_mem hg
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.FockMul
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem poly_pull {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    {p : (Fin 2 → A F) → ℂ} (hp : p ∈ polyOn F (Fin 2)) :
    (fun v : V4 F => p ![v 0, v 1]) ∈ polyFn (F := F) := by
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, w, rfl⟩ := hx
    refine Algebra.subset_adjoin ?_
    fin_cases i
    · exact ⟨0, w, rfl⟩
    · exact ⟨1, w, rfl⟩
  | algebraMap r => exact Subalgebra.algebraMap_mem _ r
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

private theorem ind_mul_mem {F : Type} [Field F] [NumberField F]
    {T : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F)} (hc : IsCompact T) (ho : IsOpen T)
    {g : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi F (ι := Fin 4)) :
    (fun y : Fin 4 → FiniteAdeleRing (𝓞 F) F =>
      (T.indicator (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) ![y 0, y 1]) * g y) ∈
        finiteSchwartzBruhatPi F (ι := Fin 4) := by
  obtain ⟨h1, h2⟩ := (mem_finiteSchwartzBruhatPi F).1 hg
  have hcl : IsClopen T := ⟨hc.isClosed, ho⟩
  have hi : IsLocallyConstant (T.indicator (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ)) := by
    exact ((LocallyConstant.const (Fin 2 → FiniteAdeleRing (𝓞 F) F) (1 : ℂ)).indicator hcl).isLocallyConstant
  have hcont : Continuous fun y : Fin 4 → FiniteAdeleRing (𝓞 F) F => (![y 0, y 1] : Fin 2 → _) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_apply 0
    · exact continuous_apply 1
  exact (mem_finiteSchwartzBruhatPi F).2 ⟨(hi.comp_continuous hcont).mul h1, h2.mul_left⟩

theorem UpperTheory.ConvolutionTheory.R2.G.fockMul :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F), (∀ χ ∈ FockFn δ, ∀ p ∈ polyOn F (Fin 2), ∀ T : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F), IsCompact T → IsOpen T →
    (fun v : V4 F => p ![v 0, v 1] * T.indicator 1 (finPartPi ![v 0, v 1]) * χ v) ∈ FockFn δ) ∧ ∀ v₀ : V4 F, ∃ χ ∈ FockFn δ, χ v₀ ≠ 0 := by
  intro F _ _ _ δ
  refine ⟨?_, ?_⟩
  · intro χ hχ p hp T hc ho
    induction hχ using Submodule.span_induction with
    | mem φ hφ =>
      obtain ⟨q, hq, g, hg, rfl⟩ := hφ
      refine Submodule.subset_span ⟨_, mul_mem (poly_pull hp) hq, _, ind_mul_mem hc ho hg, ?_⟩
      funext v
      have hfin : finPartPi ![v 0, v 1] = ![finPartPi v 0, finPartPi v 1] := by
        funext i
        fin_cases i <;> rfl
      simp only [hfin, Pi.mul_apply]
      ring
    | zero =>
      have : (fun v : V4 F => p ![v 0, v 1] * T.indicator 1 (finPartPi ![v 0, v 1]) * (0 : V4 F → ℂ) v) = 0 := by
        funext v
        simp
      rw [this]
      exact zero_mem _
    | add x y _ _ hx hy =>
      have := add_mem hx hy
      convert this using 1
      funext v
      simp only [Pi.add_apply]
      ring
    | smul a x _ hx =>
      have := Submodule.smul_mem _ a hx
      convert this using 1
      funext v
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  · intro v₀
    refine ⟨_, Submodule.subset_span ⟨1, one_mem _,
      finiteTensor fun i => cosetIndicator (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (v₀ i).2,
      finiteTensor_mem fun i => cosetIndicator_mem_finiteSchwartzBruhat _ _, rfl⟩, ?_⟩
    have hone : finiteTensor (fun i => cosetIndicator (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (v₀ i).2)
        (finPartPi v₀) = 1 := by
      have hself : ∀ a : FiniteAdeleRing (𝓞 F) F,
          cosetIndicator (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) a a = 1 := fun a => by
        rw [cosetIndicator_apply, if_pos]
        rw [sub_self]
        exact zero_mem _
      exact Finset.prod_eq_one fun i _ => hself _
    simp only [hone, Pi.one_apply, one_mul, mul_one]
    exact Complex.exp_ne_zero _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.GoodSpan
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.goodSpan :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E), Good D 0 ∧ (∀ Φ Φ', Good D Φ → Good D Φ' → Good D (Φ + Φ')) ∧ ∀ (c : ℂ) Φ, Good D Φ → Good D (c • Φ) := by
  intro F E _ _ _ _ _ D
  have hWE : ∀ (Φ : GL (Fin 2) (A E) → ℂ) h,
      WE D Φ h = ∫ u in FS2 F, Φ (nE D u * h) * ψ (2 * u 0) ∂(adeleMeasurePi F) := fun _ _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨fun _ _ => rfl, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun h => ?_⟩
    · simpa using (integrableOn_zero (μ := adeleMeasurePi F) (s := FS2 F))
    · simpa using (integrableOn_zero (μ := adeleMeasurePi F) (s := FS2 F))
    · simp
    · have : ∀ ξ : Rw F, WE D (0 : GL (Fin 2) (A E) → ℂ) (aE (al D ξ.1) * h) = 0 := by
        intro ξ
        rw [hWE]
        simp
      simp only [this]
      exact hasSum_zero
  · intro Φ Φ' h1 h2
    refine ⟨fun γ h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · simp only [Pi.add_apply, h1.left, h2.left]
    · exact (h1.int0 h).add (h2.int0 h)
    · have heq : (fun u => (Φ + Φ') (nE D u * h) * ψ (2 * u 0))
          = (fun u => Φ (nE D u * h) * ψ (2 * u 0)) + fun u => Φ' (nE D u * h) * ψ (2 * u 0) := by
        funext u
        simp only [Pi.add_apply, add_mul]
      rw [heq]
      exact (h1.int1 h).add (h2.int1 h)
    · simp only [Pi.add_apply]
      rw [integral_add (h1.int0 h) (h2.int0 h), h1.zero, h2.zero, add_zero]
    · have : ∀ ξ : Rw F, WE D (Φ + Φ') (aE (al D ξ.1) * h)
          = WE D Φ (aE (al D ξ.1) * h) + WE D Φ' (aE (al D ξ.1) * h) := by
        intro ξ
        simp only [hWE, Pi.add_apply, add_mul]
        exact integral_add (h1.int1 _) (h2.int1 _)
      simp only [this, Pi.add_apply]
      exact (h1.sum h).add (h2.sum h)
  · intro c Φ h1
    refine ⟨fun γ h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · simp only [Pi.smul_apply, h1.left]
    · exact (h1.int0 h).const_mul c
    · have heq : (fun u => (c • Φ) (nE D u * h) * ψ (2 * u 0))
          = fun u => c * (Φ (nE D u * h) * ψ (2 * u 0)) := by
        funext u
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
      rw [heq]
      exact (h1.int1 h).const_mul c
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [integral_const_mul, h1.zero, mul_zero]
    · have : ∀ ξ : Rw F, WE D (c • Φ) (aE (al D ξ.1) * h) = c * WE D Φ (aE (al D ξ.1) * h) := by
        intro ξ
        simp only [hWE, Pi.smul_apply, smul_eq_mul, mul_assoc]
        exact integral_const_mul _ _
      simp only [this, Pi.smul_apply, smul_eq_mul]
      exact (h1.sum h).mul_left c
end

