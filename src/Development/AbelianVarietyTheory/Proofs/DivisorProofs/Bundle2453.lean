module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1427
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2327
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianCompletionSupIdealSmulEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneous
section
set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal
open GlobalTheory.CxForm GlobalTheory.ChartGlue

namespace GlobalTheory.LineForm.TopInt

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem loc_add (α β : A.Fld) (i : A.ι) (v : V n) : A.loc (α + β) i v = A.loc α i v + A.loc β i v := by
  unfold HolAtlas.loc; split_ifs
  · rfl
  · exact (add_zero 0).symm

theorem loc_smul (c : ℂ) (α : A.Fld) (i : A.ι) (v : V n) : A.loc (c • α) i v = c • A.loc α i v := by
  unfold HolAtlas.loc; split_ifs
  · rfl
  · exact (smul_zero c).symm

theorem dens_add (x y : Alt n) : dens (x + y) = dens x + dens y := by
  simp only [dens, map_add (f := _), Finsupp.add_apply, add_div]

theorem dens_smul (c : ℂ) (x : Alt n) : dens (c • x) = c * dens x := by
  simp only [dens, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_div_assoc]

theorem reDens_add (α β : A.Fld) (i : A.ι) (v : V n) :
    A.reDens (α + β) i v = A.reDens α i v + A.reDens β i v := by
  simp only [HolAtlas.reDens, loc_add, dens_add, Complex.add_re]

theorem reDens_smul (t : ℝ) (α : A.Fld) (i : A.ι) (v : V n) :
    A.reDens ((t : ℂ) • α) i v = t * A.reDens α i v := by
  simp only [HolAtlas.reDens, loc_smul, dens_smul, Complex.re_ofReal_mul]

variable [MeasurableSpace M]

def G (r : A.ι → V n → ℝ) : Measure M := glueMeas A.e fun i y => ENNReal.ofReal (r i (A.e i y))

def Good (r : A.ι → V n → ℝ) : Prop :=
  (∀ i, ContinuousOn (r i) (A.e i).target) ∧
  ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
    r i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * r j (A.e j y)

theorem part_eq (γ : A.Fld) (ε : ℤˣ) (r : A.ι → V n → ℝ) (h : ∀ i v, ((ε : ℤ) : ℝ) * A.reDens γ i v = r i v) :
    A.part γ ε = G A r := by
  simp only [HolAtlas.part, G]
  congr 1
  funext i y
  rw [← h]
  rfl

theorem good_lin {α : A.Fld} (hα : A.IsForm α) (c : ℝ) : Good A fun i v => c * A.reDens α i v :=
  ⟨fun i => continuousOn_const.mul (A.continuousOn_reDens hα i),
    fun i j y hi hj => by simp only [A.reDens_compat hα i j y hi hj]; ring⟩

theorem isJacobianCompatibleDensity_linearCombination_realDensity {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) (c d : ℝ) :
    Good A fun i v => c * A.reDens α i v + d * A.reDens β i v :=
  ⟨fun i => (continuousOn_const.mul (A.continuousOn_reDens hα i)).add
      (continuousOn_const.mul (A.continuousOn_reDens hβ i)),
    fun i j y hi hj => by simp only [A.reDens_compat hα i j y hi hj, A.reDens_compat hβ i j y hi hj]; ring⟩

theorem glueMeas_mono [BorelSpace M] {ρ ρ' : A.ι → M → ℝ≥0∞} (h : ∀ i y, ρ i y ≤ ρ' i y) :
    glueMeas A.e ρ ≤ glueMeas A.e ρ' := by
  unfold glueMeas
  exact iSup_mono fun i => Measure.le_iff.2 fun S hS => by
    rw [chartMeas_apply _ _ hS, chartMeas_apply _ _ hS]
    exact lintegral_mono fun v => h i _

variable [BorelSpace M] [SecondCountableTopology M]

theorem aem {r : A.ι → V n → ℝ} (hr : Good A r) (i : A.ι) (S : Set M) :
    AEMeasurable (fun v => ENNReal.ofReal (r i (A.e i ((A.e i).symm v))))
      (volume.restrict ((A.e i).target ∩ (A.e i).symm ⁻¹' S)) :=
  (HolAtlas.aemeasurable_ofReal_chart (A.e i) (r i) (hr.1 i)).mono_measure
    (Measure.restrict_mono (inter_subset_inter_right _ (preimage_mono (subset_univ S))) le_rfl)

theorem G_add {r₁ r₂ : A.ι → V n → ℝ} (h₁ : Good A r₁) (h₂ : Good A r₂) :
    glueMeas A.e (fun i y => ENNReal.ofReal (r₁ i (A.e i y)) + ENNReal.ofReal (r₂ i (A.e i y))) = G A r₁ + G A r₂ := by
  ext S hS
  rw [Measure.add_apply]
  exact glueMeas_add_of_compat_on A.e A.holo A.cover hS _ _
    (fun i j y _ hi hj => A.ofReal_compat r₁ h₁.2 i j y hi hj)
    (fun i j y _ hi hj => A.ofReal_compat r₂ h₂.2 i j y hi hj) (fun i => aem A h₁ i S)

theorem holAtlasGluedDensityMeasure_add_three {r₁ r₂ r₃ : A.ι → V n → ℝ} (h₁ : Good A r₁) (h₂ : Good A r₂) (h₃ : Good A r₃) :
    glueMeas A.e (fun i y => ENNReal.ofReal (r₁ i (A.e i y)) + ENNReal.ofReal (r₂ i (A.e i y)) +
      ENNReal.ofReal (r₃ i (A.e i y))) = G A r₁ + G A r₂ + G A r₃ := by
  ext S hS
  have c₁ := A.ofReal_compat r₁ h₁.2
  have c₂ := A.ofReal_compat r₂ h₂.2
  have c₃ := A.ofReal_compat r₃ h₃.2
  rw [Measure.add_apply, Measure.add_apply,
    glueMeas_add_of_compat_on A.e A.holo A.cover hS
      (fun i y => ENNReal.ofReal (r₁ i (A.e i y)) + ENNReal.ofReal (r₂ i (A.e i y)))
      (fun i y => ENNReal.ofReal (r₃ i (A.e i y)))
      (fun i j y _ hi hj => by rw [c₁ i j y hi hj, c₂ i j y hi hj, mul_add])
      (fun i j y _ hi hj => c₃ i j y hi hj)
      (fun i => (aem A h₁ i S).add (aem A h₂ i S)),
    glueMeas_add_of_compat_on A.e A.holo A.cover hS
      (fun i y => ENNReal.ofReal (r₁ i (A.e i y))) (fun i y => ENNReal.ofReal (r₂ i (A.e i y)))
      (fun i j y _ hi hj => c₁ i j y hi hj) (fun i j y _ hi hj => c₂ i j y hi hj)
      (fun i => aem A h₁ i S)]
  rfl

theorem G_smul {r : A.ι → V n → ℝ} (h : Good A r) {c : ℝ} (hc : 0 ≤ c) :
    G A (fun i v => c * r i v) = ENNReal.ofReal c • G A r := by
  have hc' : Good A (fun i v => c * r i v) :=
    ⟨fun i => continuousOn_const.mul (h.1 i), fun i j y hi hj => by simp only [h.2 i j y hi hj]; ring⟩
  refine ext_of_cover (fun i => (A.e i).source) (fun i => (A.e i).open_source) A.cover fun i S hS hSi => ?_
  rw [Measure.smul_apply, G, G, glueMeas_apply _ _ A.holo (fun i j y hi hj => A.ofReal_compat (fun i v => c * r i v) hc'.2 i j y hi hj) i hS hSi,
    glueMeas_apply _ _ A.holo (fun i j y hi hj => A.ofReal_compat _ h.2 i j y hi hj) i hS hSi,
    chartMeas_apply_of_subset _ _ hS hSi, chartMeas_apply_of_subset _ _ hS hSi, smul_eq_mul,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun v => ?_
  rw [ENNReal.ofReal_mul hc]

theorem part_finite [CompactSpace M] {α : A.Fld} (hα : A.IsForm α) (ε : ℤˣ) : IsFiniteMeasure (A.part α ε) := by
  have h := good_lin A hα ((ε : ℤ) : ℝ)
  have e : A.part α ε = G A (fun i v => ((ε : ℤ) : ℝ) * A.reDens α i v) := part_eq A α ε _ fun _ _ => rfl
  have fin : G A (fun i v => ((ε : ℤ) : ℝ) * A.reDens α i v) univ ≠ ∞ :=
    GlobalTheory.T.glueMeas_univ_ne_infty_of_continuousOn A.e A.cover A.holo (fun i v => ((ε : ℤ) : ℝ) * A.reDens α i v) h.1 h.2
  refine ⟨?_⟩
  rw [e]
  exact lt_top_iff_ne_top.2 fin

theorem part_add_le {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) (ε : ℤˣ) :
    A.part (α + β) ε ≤ A.part α ε + A.part β ε := by
  rw [part_eq A (α + β) ε (fun i v => ((ε : ℤ) : ℝ) * A.reDens α i v + ((ε : ℤ) : ℝ) * A.reDens β i v)
      fun i v => by rw [reDens_add, mul_add],
    part_eq A α ε (fun i v => ((ε : ℤ) : ℝ) * A.reDens α i v) fun _ _ => rfl,
    part_eq A β ε (fun i v => ((ε : ℤ) : ℝ) * A.reDens β i v) fun _ _ => rfl,
    ← G_add A (good_lin A hα _) (good_lin A hβ _)]
  exact glueMeas_mono A fun i y => ENNReal.ofReal_add_le

theorem part_balance {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) :
    A.part (α + β) 1 + A.part α (-1) + A.part β (-1) = A.part (α + β) (-1) + A.part α 1 + A.part β 1 := by
  rw [part_eq A (α + β) 1 (fun i v => 1 * A.reDens α i v + 1 * A.reDens β i v)
      fun i v => by simp [reDens_add],
    part_eq A α (-1) (fun i v => (-1) * A.reDens α i v + 0 * A.reDens β i v) fun i v => by simp,
    part_eq A β (-1) (fun i v => 0 * A.reDens α i v + (-1) * A.reDens β i v) fun i v => by simp,
    part_eq A (α + β) (-1) (fun i v => (-1) * A.reDens α i v + (-1) * A.reDens β i v)
      fun i v => by simp [reDens_add]; ring,
    part_eq A α 1 (fun i v => 1 * A.reDens α i v + 0 * A.reDens β i v) fun i v => by simp,
    part_eq A β 1 (fun i v => 0 * A.reDens α i v + 1 * A.reDens β i v) fun i v => by simp,
    ← holAtlasGluedDensityMeasure_add_three A (isJacobianCompatibleDensity_linearCombination_realDensity A hα hβ _ _) (isJacobianCompatibleDensity_linearCombination_realDensity A hα hβ _ _) (isJacobianCompatibleDensity_linearCombination_realDensity A hα hβ _ _),
    ← holAtlasGluedDensityMeasure_add_three A (isJacobianCompatibleDensity_linearCombination_realDensity A hα hβ _ _) (isJacobianCompatibleDensity_linearCombination_realDensity A hα hβ _ _) (isJacobianCompatibleDensity_linearCombination_realDensity A hα hβ _ _)]
  congr 1
  funext i y
  have := HolAtlas.ofReal_posNeg (A.reDens α i (A.e i y)) (-A.reDens β i (A.e i y))
  convert this using 3 <;> ring_nf

theorem part_smul_nonneg {α : A.Fld} (hα : A.IsForm α) {t : ℝ} (ht : 0 ≤ t) (ε : ℤˣ) :
    A.part ((t : ℂ) • α) ε = ENNReal.ofReal t • A.part α ε := by
  rw [part_eq A ((t : ℂ) • α) ε (fun i v => t * (((ε : ℤ) : ℝ) * A.reDens α i v))
      fun i v => by rw [reDens_smul]; ring,
    part_eq A α ε (fun i v => ((ε : ℤ) : ℝ) * A.reDens α i v) fun _ _ => rfl,
    G_smul A (good_lin A hα _) ht]

theorem part_smul_nonpos {α : A.Fld} (hα : A.IsForm α) {t : ℝ} (ht : t ≤ 0) (ε : ℤˣ) :
    A.part ((t : ℂ) • α) ε = ENNReal.ofReal (-t) • A.part α (-ε) := by
  rw [part_eq A ((t : ℂ) • α) ε (fun i v => (-t) * ((((-ε : ℤˣ) : ℤ) : ℝ) * A.reDens α i v))
      fun i v => by rw [reDens_smul, Units.val_neg, Int.cast_neg]; ring,
    part_eq A α (-ε) (fun i v => (((-ε : ℤˣ) : ℤ) : ℝ) * A.reDens α i v) fun _ _ => rfl,
    G_smul A (good_lin A hα _) (neg_nonneg.2 ht)]

theorem part_congr {α β : A.Fld} (h : ∀ x, dens (α x) = dens (β x)) (ε : ℤˣ) : A.part α ε = A.part β ε := by
  simp only [HolAtlas.part]
  congr 1
  funext i y
  congr 3
  unfold HolAtlas.loc
  split_ifs
  · exact h _
  · rfl

end GlobalTheory.LineForm.TopInt

namespace GlobalTheory.LineForm

open GlobalTheory.LineForm.TopInt

theorem wInt_props : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n),
    (∀ α : A.Fld, A.IsForm α → ∀ ε : ℤˣ, IsFiniteMeasure (A.part α ε)) ∧
    (∀ (g : M → ℝ) (α β : A.Fld), A.IsForm α → A.IsForm β → (∀ ε : ℤˣ, Integrable g (A.part α ε)) →
      (∀ ε : ℤˣ, Integrable g (A.part β ε)) →
      (∀ ε : ℤˣ, Integrable g (A.part (α + β) ε)) ∧ wInt A g (α + β) = wInt A g α + wInt A g β) ∧
    (∀ (g : M → ℝ) (t : ℝ) (α : A.Fld), A.IsForm α → wInt A g ((t : ℂ) • α) = t * wInt A g α) ∧
    (∀ (g : M → ℝ) (α β : A.Fld), (∀ x, dens (α x) = dens (β x)) → wInt A g α = wInt A g β) := by
  intro M _ _ _ _ _ _ n A
  refine ⟨fun α hα ε => part_finite A hα ε, fun g α β hα hβ ga gb => ?_, fun g t α hα => ?_,
    fun g α β h => by simp only [wInt, part_congr A h]⟩
  · have gs : ∀ ε : ℤˣ, Integrable g (A.part (α + β) ε) := fun ε =>
      ((ga ε).add_measure (gb ε)).mono_measure (part_add_le A hα hβ ε)
    refine ⟨gs, ?_⟩
    have key := congrArg (fun μ : Measure M => ∫ y, g y ∂μ) (part_balance A hα hβ)
    rw [integral_add_measure (((gs 1).add_measure (ga (-1)))) (gb (-1)),
      integral_add_measure (gs 1) (ga (-1)),
      integral_add_measure (((gs (-1)).add_measure (ga 1))) (gb 1),
      integral_add_measure (gs (-1)) (ga 1)] at key
    simp only [wInt]
    linarith
  · rcases le_total 0 t with ht | ht
    · simp only [wInt, part_smul_nonneg A hα ht, integral_smul_measure, ENNReal.toReal_ofReal ht, smul_eq_mul]
      ring
    · simp only [wInt, part_smul_nonpos A hα ht, integral_smul_measure, ENNReal.toReal_ofReal (neg_nonneg.2 ht),
        smul_eq_mul, neg_neg]
      ring

end GlobalTheory.LineForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HopfHeightOnePrimitiveEqZeroOfZeroDifferential
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDiv.HeightOnePrim

theorem apply_eq_zero_of_mem_sq {K H : Type} [Field K] [CommRing H] [HopfAlgebra K H]
    [IsCocomm K H] [Module.Finite K H] {φ : CartierDual K H} (hφ : cobOne K (CartierDual K H) φ = 0) {b : H}
    (hb : b ∈ augIdeal K H ^ 2) : φ b = 0 := by
  have hp := isPrimitiveElem_of_mem_ker (R := K) (A := CartierDual K H) (b := φ) hφ
  have hmul : ∀ x y : H, φ (x * y) = φ x * counit (R := K) y + counit (R := K) x * φ y := by
    intro x y
    rw [← CartierDual.pair_comul_tmul, show comul φ = _ from hp, map_add (f := _), LinearMap.add_apply,
      CartierDual.pair_tmul_tmul, CartierDual.pair_tmul_tmul, CartierDual.one_apply,
      CartierDual.one_apply]
  rw [pow_two] at hb
  refine Submodule.mul_induction_on hb (fun x hx y hy => ?_) (fun x y hx hy => ?_)
  · have hx' : counit (R := K) x = 0 := hx
    have hy' : counit (R := K) y = 0 := hy
    rw [hmul, hx', hy', mul_zero, zero_mul, add_zero]
  · rw [map_add (f := _), hx, hy, add_zero]

theorem eq_zero_of_cobOne_eq_zero_of_dUnit_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p] [CommRing H]
    [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H], (∀ a ∈ augIdeal K H, a ^ p = 0) →
    ∀ b : H, cobOne K H b = 0 → dUnit (R := K) b = 0 → b = 0 := by
  intro p _ K H _ _ _ _ _ _ hpow b hb hd
  have hcb : counit (R := K) b = 0 := (mulBy_of_cobOne_eq_zero hb 0).2
  have hsq : b ∈ augIdeal K H ^ 2 := by
    have := (AugCot.d_eq_zero_iff (counitAlgHom K H) b).1 hd
    simpa [hcb] using this
  have hgen := _root_.GlobalTheory.HeightOneDual.adjoin_primitive_eq_top p K H hpow
  have hall : ∀ φ : CartierDual K H, φ b = 0 := by
    intro φ
    have hφ : φ ∈ Algebra.adjoin K {φ : CartierDual K H | cobOne K (CartierDual K H) φ = 0} := by
      rw [hgen]; trivial
    induction hφ using Algebra.adjoin_induction with
    | mem x hx => exact apply_eq_zero_of_mem_sq hx hsq
    | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one]
      change r • (1 : CartierDual K H) b = 0
      rw [CartierDual.one_apply, hcb, smul_zero]
    | add x y _ _ hx hy => rw [WithConv.ofConv_add, LinearMap.add_apply, hx, hy, add_zero]
    | mul x y _ _ hx hy =>
      have := evalAt_mul (R := K) (A := H) ⟨b, hb⟩ x y
      simp only [CartierDual.evalAt_apply] at this
      rw [this, hx, hy, smul_zero, smul_zero, add_zero]
  exact CartierDual.eq_of_forall_apply (R := K) fun φ => by rw [hall φ, map_zero]

end GlobalTheory.PDiv.HeightOnePrim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageBasePointRationalFractionField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.RatBase

theorem nsmul_b' {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {k : ℕ} {g h : GtPtF D F} (H : GtPtF.IsNsmul k g h) : h.b = g.b ^ k := by
  obtain ⟨gs, h0, hs, rfl⟩ := H
  have : ∀ i : Fin (k + 1), (gs i).b = g.b ^ (i : ℕ) := fun i => by
    induction i using Fin.induction with
    | zero => rw [Fin.val_zero, pow_zero]; exact h0.1
    | succ i ih => rw [(hs i).1, ih, Fin.val_succ, pow_succ]; rfl
  exact this _

theorem pow_comp' {S : Scheme.{0}} {G H Z : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ]
    (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem ratBase : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (p₀ p : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n), p.y = F.e • p₀.y → GtPtAct F.o F.e p₀.g p.g → ∃ b : TF (R := R) (FractionRing R) ⟶ D'.toPre.P.A, p.g.b.left = spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ b.left := by
  intro o W _ _ _ T R _ _ _ iw I _ s ε n _ hn _ ζ _ Q e hD hT D' F p₀ p hy hg
  haveI := F.inc_hom
  haveI := F.pr_hom
  set L := AlgebraicClosure (FractionRing R)
  set a := F.xp p₀.y
  let b₀ : TF (R := R) L ⟶ Q.B := p₀.g.b ≫ F.pr
  have hpb : p.g.b = b₀ ≫ F.inc := by rw [hg.1, ← F.pr_inc, Category.assoc]
  obtain ⟨h, h1, h2⟩ := p₀.eq
  have hn1 : p₀.g.b ^ n = toUnit _ ≫ D'.toPre.c p₀.y := (nsmul_b' h1).symm.trans h2.1
  have hcpr : D'.toPre.c p₀.y ≫ F.pr = Q.c a := by
    have h3 : D'.toPre.c p₀.y ≫ F.pr ≫ F.inc = Q.c a ≫ F.inc := by
      rw [F.pr_inc, ← F.o.c_lin, ← F.xi_xp, F.c_xi]
    have h4 := congrArg (· ≫ F.pr) h3
    simpa only [Category.assoc, F.inc_pr, Category.comp_id] using h4
  have hb₀ : b₀ ^ n = toUnit _ ≫ Q.c a := by
    rw [← pow_comp', hn1, Category.assoc, hcpr]
  obtain ⟨β, β₂, w, hpb', hsq, hw, hc, htau⟩ := hD

  have hcomm : (spMap iw ≫ (T.c₀ (e a)).left) ≫ T.B.hom = 𝟙 (Sp R) ≫ spMap iw := by
    rw [Category.assoc, Over.w (T.c₀ (e a))]; simp
  let d : 𝟙_ (Over (Sp R)) ⟶ Q.B := Over.homMk (hpb'.1.lift _ _ hcomm) (by simpa using hpb'.1.lift_snd _ _ hcomm)
  have hd : d.left ≫ β = spMap iw ≫ (T.c₀ (e a)).left := hpb'.1.lift_fst _ _ hcomm
  have hdn : d ^ n = Q.c a := by
    refine Over.OverMorphism.ext (hpb'.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    rw [GlobalTheory.FrameMove.pow_comm hpb' hd n, hc a]
    congr 2
    have key : ∀ k : ℕ, T.c₀ ((k : ℤ) • e a) = T.c₀ (e a) ^ k := fun k => by
      induction k with
      | zero => rw [Nat.cast_zero, zero_smul, pow_zero, T.c₀_zero]
      | succ k ih => rw [Nat.cast_succ, add_smul, one_smul, T.c₀_add, ih, pow_succ]
    exact (key n).symm

  let κ := algebraMap (FractionRing R) L
  let x : TF (R := R) L ⟶ Q.B := b₀ * (toUnit _ ≫ d)⁻¹
  have hx : x ^ n = 1 := by
    simp only [x]
    rw [mul_pow, inv_pow, hb₀, ← GlobalTheory.FrameMove.comp_pow, hdn, mul_inv_cancel]
  obtain ⟨x₀, hx₀⟩ := hT L κ x hx
  let ρ : TF (R := R) L ⟶ TK R := Over.homMk (spMap κ) rfl
  have hxρ : x = ρ ≫ x₀ := Over.OverMorphism.ext hx₀
  have hb₀' : b₀ = ρ ≫ (x₀ * (toUnit _ ≫ d)) := by
    rw [MonObj.comp_mul, ← hxρ, ← Category.assoc, toUnit_unique (ρ ≫ toUnit _) (toUnit _)]
    simp only [x, inv_mul_cancel_right]
  let σ : TF (R := R) (FractionRing R) ⟶ TK R := Over.homMk (jFK (R := R) (FractionRing R)) rfl
  refine ⟨σ ≫ (x₀ * (toUnit _ ≫ d)) ≫ F.inc, ?_⟩
  rw [hpb, hb₀']
  simp only [Over.comp_left]

  have hj : jFK (R := R) (FractionRing R) = 𝟙 _ := by
    simp only [jFK, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have hσ : σ.left = 𝟙 _ := hj
  rw [hσ, Category.id_comp, Category.assoc]
  rfl

end GlobalTheory.Mum.RatBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImHermFormAlternatingNondegenerateOnLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.HermImNondeg

theorem hermForm_add_right' {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]

theorem hermForm_smul_right' {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm z (a • w) = star a * hermForm Hm z w := by
  simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hermForm_self_star {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (z : Fin g → ℂ) :
    star (hermForm Hm z z) = hermForm Hm z z := by
  simp only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', Pi.star_apply, star_star, h.apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem im_hermForm_alternating_nondegenerate (La : Type) [AddCommGroup La] (g : ℕ) (P : La →+ (Fin g → ℂ))
    (Hm : Matrix (Fin g) (Fin g) ℂ) (EF : LinearMap.BilinForm ℤ La) (hP : Function.Injective P)
    (hspan : Submodule.span ℝ (Set.range P) = ⊤) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hEF : ∀ x y, (hermForm Hm (P x) (P y)).im = EF x y) :
    (∀ x, EF x x = 0) ∧ ∀ x, (∀ y, EF x y = 0) → x = 0 := by
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · have hc : ((EF x x : ℤ) : ℝ) = 0 := by
      rw [← hEF]
      have h1 := congrArg Complex.im (hermForm_self_star hH (P x))
      have h2 : (star (hermForm Hm (P x) (P x))).im = -(hermForm Hm (P x) (P x)).im := Complex.conj_im _
      linarith
    exact_mod_cast hc
  · set z := P x with hz
    have key : ∀ w : Fin g → ℂ, (hermForm Hm z w).im = 0 := by
      intro w
      have hw : w ∈ Submodule.span ℝ (Set.range P) := hspan ▸ Submodule.mem_top
      induction hw using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨y, rfl⟩ := ha
        rw [hEF, hx y]; simp
      | zero => simp [hermForm]
      | add a b _ _ h1 h2 => rw [hermForm_add_right', Complex.add_im, h1, h2, add_zero]
      | smul r a _ h1 =>
        rw [← Complex.coe_smul, hermForm_smul_right']
        simp [h1]
    have hI := key (Complex.I • z)
    rw [hermForm_smul_right'] at hI
    have hre : (hermForm Hm z z).re = 0 := by
      have : (star Complex.I * hermForm Hm z z).im = -(hermForm Hm z z).re := by
        simp [Complex.mul_im]
      linarith
    by_contra hne
    have hz0 : z ≠ 0 := by
      intro h0; apply hne; apply hP; rw [← hz, h0, map_zero]
    have := hpos z hz0
    linarith

end GlobalTheory.HermImNondeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageGenericBaseChangeModificatio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isAffineOpen_preimage_genericBaseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S) (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ W : G.left.Opens, IsAffineOpen W → IsAffineOpen (α ⁻¹ᵁ W) := by
  intro R _ _ M G Y α t h W hW
  haveI := M.proper
  haveI : M.S.IsSeparated := by
    constructor
    rw [← terminal.comp_from M.π]
    infer_instance
  haveI : IsAffineHom M.gp := by
    haveI : IsAffineHom (M.gp ≫ terminal.from M.S) := inferInstance
    exact IsAffineHom.of_comp M.gp (terminal.from M.S)
  haveI : IsAffineHom α := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  exact hW.preimage α

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianCompletionSupIdealSmulEqStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangianCompletion_sup_ideal_smul_eq : ∀ (C : Type) [CommRing C] (I : Ideal C) (H : Type 1) [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H] (O : Type) [Ring O] (ρ : O →+* Module.End C H) (bar : O → O) (φ : LinearMap.BilinForm C H) (e : Module.End C H), e * e = e → (∀ a, ρ a * e = e * ρ a) → (∀ x y, φ x y = -φ y x) → (∀ a, bar (bar a) = a) → (∀ a x y, φ (ρ a x) y = φ x (ρ (bar a) y)) → (∀ x y, φ (e x) y = φ x (y - e y)) → Function.Bijective φ → ∀ F : Submodule C H, I • ⊤ ≤ F → (∀ x ∈ F, ∀ y ∈ F, φ x y ∈ I) → (∀ x, (∀ y ∈ F, φ x y ∈ I) → x ∈ F) → (∀ x ∈ F, e x ∈ F) → ∀ G M : Submodule C H, G ⊓ M = ⊥ → G ⊔ M = LinearMap.range e → (∀ a, ∀ x ∈ G, ρ a x ∈ G) → G ⊔ (I • ⊤ ⊓ LinearMap.range e) = F ⊓ LinearMap.range e → ∃ E : Submodule C H, (∃ N : Submodule C H, IsCompl E N) ∧ E ⊓ LinearMap.range e = G ∧ E ⊔ I • ⊤ = F ∧ (∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ (∀ a, ∀ x ∈ E, ρ a x ∈ E) ∧ ∀ x ∈ E, e x ∈ E := by
  first | (exact @GlobalTheory.lagrangian_completion_sup_smul_eq) | (exact GlobalTheory.lagrangian_completion_sup_smul_eq) | (intros; apply GlobalTheory.lagrangian_completion_sup_smul_eq  <;> assumption)
end

