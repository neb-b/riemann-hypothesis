module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0052
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.AeZero
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem kappa_ne_zero {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (M : Meas F)
    {U : Set (G1 F)} (hU : IsOpen U) {k : G1 F} (hk : k ∈ KK F) (hkU : k ∈ U) : M.κ U ≠ 0 := by
  intro h0
  obtain ⟨hKs, hC⟩ := UpperTheory.ConvolutionTheory.R2.M.kkCpt F
  have hmem : ∀ x ∈ KK F, ∀ y ∈ KK F, x * y⁻¹ ∈ KK F := by
    intro x hx y hy
    rw [hKs] at hx hy ⊢
    exact (UpperTheory.ConvolutionTheory.R2.M.Ks F).mul_mem hx ((UpperTheory.ConvolutionTheory.R2.M.Ks F).inv_mem hy)
  have hnull : ∀ c ∈ KK F, M.κ ((fun x => c * x) ⁻¹' U) = 0 := by
    intro c hc
    have hm : Measurable (fun x : G1 F => c * x) := (continuous_const.mul continuous_id).measurable
    rw [← Measure.map_apply hm hU.measurableSet, M.κ_left c hc]
    exact h0
  obtain ⟨t, ht, hcov⟩ := hC.elim_nhds_subcover (fun x => (fun y => (k * x⁻¹) * y) ⁻¹' U) (by
    intro x hx
    refine ((continuous_const.mul continuous_id).isOpen_preimage _ hU).mem_nhds ?_
    simpa using hkU)
  have hK0 : M.κ (KK F) = 0 := by
    refine measure_mono_null hcov ?_
    exact (measure_biUnion_null_iff t.countable_toSet).2 fun x hx => hnull _ (hmem k hk x (ht x hx))
  haveI := M.prob
  have hle : M.κ Set.univ ≤ M.κ (KK F) + M.κ (KK F)ᶜ := by
    rw [← Set.union_compl_self (KK F)]
    exact measure_union_le _ _
  rw [hK0, M.supp, measure_univ] at hle
  simp at hle

theorem UpperTheory.ConvolutionTheory.R2.G.aeZero :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : Meas F) (u : IdeleGroup F × G1 F → ℂ), ContinuousOn u (Set.univ ×ˢ KK F) → (∀ᵐ p ∂M.ν, u p = 0) →
    ∀ a, ∀ k ∈ KK F, u (a, k) = 0 := by
  intro F _ _ _ M u hu h a k hk
  by_contra hne
  haveI := M.prob
  have hc : ContinuousWithinAt u (Set.univ ×ˢ KK F) (a, k) := hu (a, k) ⟨Set.mem_univ _, hk⟩
  have h1 : {p | u p ≠ 0} ∈ 𝓝[Set.univ ×ˢ KK F] (a, k) := hc.eventually_ne hne
  rw [nhdsWithin_prod_eq, Filter.mem_prod_iff] at h1
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := h1
  rw [nhdsWithin_univ, mem_nhds_iff] at ht₁
  obtain ⟨V, hVt, hVo, haV⟩ := ht₁
  obtain ⟨U, hUo, hkU, hUt⟩ := mem_nhdsWithin.1 ht₂
  have hnull : M.ν (V ×ˢ (U ∩ KK F)) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 h)
    intro p hp
    exact hsub ⟨hVt hp.1, hUt hp.2⟩
  have hprod : ideleMeasure F V * M.κ (U ∩ KK F) = 0 := by
    rw [← Measure.prod_prod]
    exact hnull
  have hV : ideleMeasure F V ≠ 0 := hVo.measure_ne_zero _ ⟨a, haV⟩
  have hU : M.κ (U ∩ KK F) ≠ 0 := by
    intro h0
    refine kappa_ne_zero M hUo hk hkU (measure_mono_null (t := (U ∩ KK F) ∪ (KK F)ᶜ) ?_ ?_)
    · intro x hx
      by_cases hxK : x ∈ KK F
      · exact Or.inl ⟨hx, hxK⟩
      · exact Or.inr hxK
    · exact measure_union_null h0 M.supp
  exact (mul_ne_zero hV hU) hprod
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.CharZero
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private lemma bdd_int {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) (u g : Ω → ℂ)
    (hu : Measurable u) (hb : ∀ ω, ‖u ω‖ ≤ 1) (hg : Integrable g ν) :
    Integrable (fun ω => u ω * g ω) ν := by
  refine Integrable.mono' hg.norm (hu.aestronglyMeasurable.mul hg.1) (ae_of_all _ fun ω => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hb ω)

private lemma real_diff {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω)
    (X : Ω → ι → ℝ) (f : Ω → ℝ) (hX : Measurable X) (hf : Integrable f ν)
    (G : (ι → ℝ) → ℂ) (hG : Measurable G) (hGb : ∀ x, ‖G x‖ ≤ 1) :
    ∫ x, G x ∂((ν.withDensity fun ω => ENNReal.ofReal (f ω)).map X)
      - ∫ x, G x ∂((ν.withDensity fun ω => ENNReal.ofReal (-f ω)).map X)
      = ∫ ω, G (X ω) * (f ω : ℂ) ∂ν :=
  _root_.UpperTheory.Reformulated.B.Qh3.real_diff ν X f hX hf G hG hGb

private lemma real_case {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω)
    (X : Ω → ι → ℝ) (f : Ω → ℝ) (hX : Measurable X) (hf : Integrable f ν)
    (h : ∀ t : ι → ℝ, ∫ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * (f ω : ℂ) ∂ν = 0)
    (S : Set (ι → ℝ)) (hS : MeasurableSet S) :
    ∫ ω, S.indicator 1 (X ω) * (f ω : ℂ) ∂ν = 0 := by
  haveI : IsFiniteMeasure (ν.withDensity fun ω => ENNReal.ofReal (f ω)) :=
    isFiniteMeasure_withDensity_ofReal hf.2
  haveI : IsFiniteMeasure (ν.withDensity fun ω => ENNReal.ofReal (-f ω)) :=
    isFiniteMeasure_withDensity_ofReal hf.neg.2
  have hEq : (ν.withDensity fun ω => ENNReal.ofReal (f ω)).map X
      = (ν.withDensity fun ω => ENNReal.ofReal (-f ω)).map X := by
    refine Measure.ext_of_charFunDual (funext fun L => ?_)
    rw [charFunDual_apply, charFunDual_apply]
    have key := real_diff ν X f hX hf (fun x => Complex.exp ((L x : ℂ) * Complex.I))
      (by fun_prop) (fun x => by rw [Complex.norm_exp_ofReal_mul_I])
    have h0 := h (fun i => L (fun j => if i = j then 1 else 0))
    have hL : ∀ x : ι → ℝ, L x = ∑ i, L (fun j => if i = j then 1 else 0) * x i := by
      intro x
      have := LinearMap.pi_apply_eq_sum_univ (L : (ι → ℝ) →ₗ[ℝ] ℝ) x
      simpa [mul_comm] using this
    simp only [← hL] at h0
    rw [h0] at key
    exact sub_eq_zero.mp key
  have key := real_diff ν X f hX hf (S.indicator 1)
    (measurable_one.indicator hS) (fun x => by
      by_cases hx : x ∈ S <;> simp [hx])
  rw [hEq, sub_self] at key
  exact key.symm

theorem UpperTheory.ConvolutionTheory.R2.G.charZero :
    ∀ (Ω ι : Type) [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω) (X : Ω → ι → ℝ) (ρ : Ω → ℂ), Measurable X → Integrable ρ ν →
    (∀ t : ι → ℝ, ∫ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * ρ ω ∂ν = 0) →
    ∀ S : Set (ι → ℝ), MeasurableSet S → ∫ ω, S.indicator 1 (X ω) * ρ ω ∂ν = 0 := by
  intro Ω ι _ _ ν X ρ hX hρ h S hS
  have hconjI : Integrable (fun ω => (starRingEnd ℂ) (ρ ω)) ν := by
    simpa using (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hρ
  have hE : ∀ t : ι → ℝ, Measurable fun ω =>
      Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) := by
    intro t
    have : ∀ i, Measurable fun ω => X ω i := fun i => (measurable_pi_apply i).comp hX
    fun_prop
  have hEb : ∀ (t : ι → ℝ) (ω : Ω),
      ‖Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I)‖ ≤ 1 := by
    intro t ω
    rw [Complex.norm_exp_ofReal_mul_I]
  have hc : ∀ t : ι → ℝ,
      ∫ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * (starRingEnd ℂ) (ρ ω) ∂ν = 0 := by
    intro t
    have h1 := congrArg (starRingEnd ℂ) (h (-t))
    rw [← integral_conj, map_zero] at h1
    rw [← h1]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [map_mul, ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I]
    simp
  have hlin : ∀ (a b : ℂ) (t : ι → ℝ),
      ∫ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) *
        (a * ρ ω + b * (starRingEnd ℂ) (ρ ω)) ∂ν = 0 := by
    intro a b t
    have e1 := bdd_int ν _ ρ (hE t) (hEb t) hρ
    have e2 := bdd_int ν _ _ (hE t) (hEb t) hconjI
    have : ∀ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) *
        (a * ρ ω + b * (starRingEnd ℂ) (ρ ω))
        = a * (Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * ρ ω)
          + b * (Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * (starRingEnd ℂ) (ρ ω)) := by
      intro ω; ring
    simp only [this]
    rw [integral_add (e1.const_mul a) (e2.const_mul b), integral_const_mul, integral_const_mul,
      h t, hc t]
    simp
  have hre : Integrable (fun ω => (ρ ω).re) ν := hρ.re
  have him : Integrable (fun ω => (ρ ω).im) ν := hρ.im
  have r1 := real_case ν X (fun ω => (ρ ω).re) hX hre (fun t => by
    rw [← hlin (1 / 2) (1 / 2) t]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    have : ((ρ ω).re : ℂ) = 1 / 2 * ρ ω + 1 / 2 * (starRingEnd ℂ) (ρ ω) := by
      rw [Complex.re_eq_add_conj]; ring
    simp only [this]) S hS
  have r2 := real_case ν X (fun ω => (ρ ω).im) hX him (fun t => by
    rw [← hlin (1 / (2 * Complex.I)) (-(1 / (2 * Complex.I))) t]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    have : ((ρ ω).im : ℂ) = 1 / (2 * Complex.I) * ρ ω
        + -(1 / (2 * Complex.I)) * (starRingEnd ℂ) (ρ ω) := by
      rw [Complex.im_eq_sub_conj]; ring
    simp only [this]) S hS
  have hind : Measurable fun ω => S.indicator (1 : (ι → ℝ) → ℂ) (X ω) :=
    (measurable_one.indicator hS).comp hX
  have hindb : ∀ ω, ‖S.indicator (1 : (ι → ℝ) → ℂ) (X ω)‖ ≤ 1 := by
    intro ω
    by_cases hx : X ω ∈ S <;> simp [hx]
  have i1 := bdd_int ν _ (fun ω => ((ρ ω).re : ℂ)) hind hindb hre.ofReal
  have i2 := bdd_int ν _ (fun ω => ((ρ ω).im : ℂ)) hind hindb him.ofReal
  have hsplit : ∀ ω, S.indicator 1 (X ω) * ρ ω
      = S.indicator 1 (X ω) * ((ρ ω).re : ℂ)
        + Complex.I * (S.indicator 1 (X ω) * ((ρ ω).im : ℂ)) := by
    intro ω
    conv_lhs => rw [← Complex.re_add_im (ρ ω)]
    ring
  simp only [hsplit]
  rw [integral_add i1 (i2.const_mul _), integral_const_mul, r1, r2]
  simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.CoefBd
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.coefBd :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (φ : S4 F) (C : Set (G1 F)) (U : Submodule ℂ (S4 F)), IsCompact C → FiniteDimensional ℂ U → (∀ k ∈ C, W.Om k φ ∈ U) →
    ∃ (n : ℕ) (b : Fin n → S4 F) (c : Fin n → G1 F → ℂ) (B : ℝ), (∀ i, b i ∈ U) ∧ (∀ i, ContinuousOn (c i) C) ∧
    ∀ k ∈ C, (∀ i, ‖c i k‖ ≤ B) ∧ W.Om k φ = ∑ i, c i k • b i := by
  intro F E _ _ _ _ _ _ _ D W φ C U hC hU hmem
  haveI := hU
  let b := Module.finBasis ℂ U
  let ev : V4 F → Module.Dual ℂ U := fun v =>
    { toFun := fun u => (u.1).1 v, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have htop : Submodule.span ℂ (Set.range ev) = ⊤ := by
    have hb : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      rw [Submodule.mem_dualCoannihilator] at hu
      have : u = 0 := by
        apply Subtype.ext
        apply Subtype.ext
        funext v
        exact hu (ev v) (Submodule.subset_span ⟨v, rfl⟩)
      simpa using this
    have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev))
    rw [← h2, hb]
    simp
  have hco : ∀ i, ∃ a : V4 F →₀ ℂ, a.sum (fun v x => x • ev v) = b.coord i := by
    intro i
    have h3 : b.coord i ∈ Submodule.span ℂ (Set.range ev) := by
      rw [htop]
      trivial
    exact (Finsupp.mem_span_range_iff_exists_finsupp).1 h3
  choose a ha using hco
  let c : Fin (Module.finrank ℂ U) → G1 F → ℂ := fun i k => ∑ v ∈ (a i).support, a i v * (W.Om k φ).1 v
  have hc : ∀ i, Continuous (c i) := by
    intro i
    refine continuous_finsetSum _ fun v _ => continuous_const.mul ?_
    exact (W.cont φ).comp (continuous_id.prodMk continuous_const)
  have hB : ∀ i, ∃ B : ℝ, ∀ k ∈ C, ‖c i k‖ ≤ B := fun i =>
    hC.exists_bound_of_continuousOn (hc i).continuousOn
  choose B hB using hB
  refine ⟨Module.finrank ℂ U, fun i => (b i).1, c, ∑ i, |B i|, fun i => (b i).2,
    fun i => (hc i).continuousOn, ?_⟩
  intro k hk
  refine ⟨fun i => ?_, ?_⟩
  · calc ‖c i k‖ ≤ B i := hB i k hk
      _ ≤ |B i| := le_abs_self _
      _ ≤ ∑ i, |B i| := Finset.single_le_sum (f := fun i => |B i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  · have hck : ∀ i, b.repr ⟨W.Om k φ, hmem k hk⟩ i = c i k := by
      intro i
      have h4 : b.coord i ⟨W.Om k φ, hmem k hk⟩ = c i k := by
        rw [← ha i, Finsupp.sum, LinearMap.sum_apply]
        rfl
      simpa using h4
    have h5 := b.sum_repr ⟨W.Om k φ, hmem k hk⟩
    have h6 := congrArg Subtype.val h5
    simp only [hck, Submodule.coe_sum, Submodule.coe_smul] at h6
    exact h6.symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.CuspOf
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Fb in
private theorem setIntegral_haar {E : Type} [Field E] [NumberField E] {a r : ℕ} {φ : GA E a → ℂ}
    (hl : IsLeftInvariant φ) (g : GA E a) (h : constantTerm r φ g = 0) (ν : Measure (UPos a r → Ad E))
    [ν.IsAddHaarMeasure] {D : Set (UPos a r → Ad E)} (hD : IsAddFundamentalDomain (unipLattice E a r) D ν) :
    ∫ x in D, φ (unipGL x * g) ∂ν = 0 := by
  have hD' : IsAddFundamentalDomain (unipLattice E a r) D (unipMeasure E a r) :=
    hD.mono (Measure.absolutelyContinuous_isAddHaarMeasure _ _)
  rw [constantTerm_eq_setIntegral hl hD'] at h
  rw [Measure.isAddLeftInvariant_eq_smul ν (unipMeasure E a r), Measure.restrict_smul, integral_smul_nnreal_measure, h,
    smul_zero]

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Fb in
private def ixEq (a r : ℕ) : UPos a r ≃ BlockIx a r where
  toFun p := ⟨p.1, p.2.1, p.2.2⟩
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Fb in
private theorem unipGL_ixEq {R : Type} [CommRing R] {a r : ℕ} (x : BlockIx a r → R) :
    unipGL (fun p => x (ixEq a r p)) = unip x := by
  refine Units.ext ?_
  change 1 + blockEntry (fun p => x (ixEq a r p)) = 1 + nilM x
  congr 1

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Fb in
private theorem cusp_of {E : Type} [Field E] [NumberField E] {a : ℕ} {φ : GA E a → ℂ}
    (hl : IsLeftInvariant φ) (hφ : AutomorphicForm.IsCuspidal φ) : GlobalTheory.CuspRep.IsCuspidal φ := by
  intro r h0 h1 i1 i2 μ 𝓕 hμ hF g
  obtain rfl : i1 = MeasurableSpace.pi :=
    (@BorelSpace.measurable_eq _ _ i1 i2).trans (@BorelSpace.measurable_eq _ _ _ Pi.borelSpace).symm
  let β : (BlockIx a r → Ad E) ≃ₜ+ (UPos a r → Ad E) :=
    { toFun := fun x p => x (ixEq a r p)
      invFun := fun x p => x ((ixEq a r).symm p)
      left_inv := fun x => rfl
      right_inv := fun x => rfl
      map_add' := fun x y => rfl
      continuous_toFun := continuous_pi fun p => continuous_apply _
      continuous_invFun := continuous_pi fun p => continuous_apply _ }
  let e : unipLattice E a r ≃ ratN E a r :=
    { toFun := fun y => ⟨β.symm y, by
        obtain ⟨_, y, rfl⟩ := y
        exact ⟨fun p => y ((ixEq a r).symm p), rfl⟩⟩
      invFun := fun x => ⟨β x, by
        obtain ⟨_, y, rfl⟩ := x
        exact ⟨fun p => y (ixEq a r p), rfl⟩⟩
      left_inv := fun y => Subtype.ext (β.apply_symm_apply y)
      right_inv := fun x => Subtype.ext (β.symm_apply_apply x) }
  let m := β.toHomeomorph.toMeasurableEquiv
  haveI : (μ.map m).IsAddHaarMeasure := β.isAddHaarMeasure_map μ
  have h2 := setIntegral_haar hl g (hφ r h0 h1 g) (μ.map m) (D := m '' 𝓕)
    (hF.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving e fun y x => by
      change β (β.symm y + x) = y + β x
      rw [map_add (f := _), β.apply_symm_apply])
  rw [m.measurableEmbedding.setIntegral_map, m.injective.preimage_image] at h2
  rw [← h2]
  congr 1
  funext x
  exact congrArg (fun u => φ (u * g)) (unipGL_ixEq x).symm

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.ConvolutionTheory.R2.Pp in
private theorem found_cusp {E : Type} [Field E] [NumberField E] {Φ : GL (Fin 2) (A E) → ℂ}
    (h0 : ∀ h, ∫ b in fundamentalSet E, Φ (gl (nU b) * h) ∂(adeleMeasure E) = 0) :
    AutomorphicForm.IsCuspidal Φ := by
  intro r hr hr2 g
  obtain rfl : r = 1 := by omega
  letI : Unique (UPos 2 1) := ⟨⟨⟨(0, 1), by decide⟩⟩, by decide⟩
  rw [← h0 g, ← int_one (ι := UPos 2 1)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have : gl (nU (x default)) = unipGL x := by
    refine Units.ext ?_
    change (nU (x default)).1 = unipMatrix x
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nU, unipMatrix, blockEntry_apply]
    rfl
  simp only [this]

theorem UpperTheory.ConvolutionTheory.R2.G.cuspOf :
    ∀ (E : Type) [Field E] [NumberField E] (Φ : GL (Fin 2) (A E) → ℂ), (∀ γ h, Φ (ratGL E 2 γ * h) = Φ h) →
    (∀ h, ∫ b in fundamentalSet E, Φ (gl (nU b) * h) ∂(adeleMeasure E) = 0) → GlobalTheory.CuspRep.IsCuspidal Φ := by
  intro E _ _ Φ hl h0
  exact cusp_of hl (found_cusp h0)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Factor
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.factor :
    ∀ (X Y : Type) [TopologicalSpace X] [SigmaCompactSpace X] [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    (r : X → Y) (H : X → ℂ), Continuous r → Continuous H → (∀ x x', r x = r x' → H x = H x') → ∃ h : Y → ℂ, Measurable h ∧ ∀ x, h (r x) = H x := by
  intro X Y _ _ _ _ _ _ r H hr hH hf
  have key : ∀ F : Set X, IsClosed F → MeasurableSet (r '' F) := by
    intro F hF
    have e : r '' F = ⋃ n, r '' (F ∩ compactCovering X n) := by
      rw [← Set.image_iUnion, ← Set.inter_iUnion, iUnion_compactCovering, Set.inter_univ]
    rw [e]
    refine MeasurableSet.iUnion fun n => ?_
    exact (((isCompact_compactCovering X n).inter_left hF).image hr).isClosed.measurableSet
  have hrange : MeasurableSet (Set.range r) := by
    rw [← Set.image_univ]
    exact key _ isClosed_univ
  let h : Y → ℂ := fun y => if hy : ∃ x, r x = y then H hy.choose else 0
  have hh : ∀ x, h (r x) = H x := by
    intro x
    have hy : ∃ x', r x' = r x := ⟨x, rfl⟩
    simp only [h, dif_pos hy]
    exact hf _ _ hy.choose_spec
  refine ⟨h, measurable_of_isClosed fun C hC => ?_, hh⟩
  have himg : MeasurableSet (r '' (H ⁻¹' C)) := key _ (hC.preimage hH)
  have hout : ∀ y, y ∉ Set.range r → h y = 0 := by
    intro y hy
    have hy' : ¬ ∃ x, r x = y := hy
    simp only [h, dif_neg hy']
  by_cases h0 : (0 : ℂ) ∈ C
  · have e : h ⁻¹' C = r '' (H ⁻¹' C) ∪ (Set.range r)ᶜ := by
      ext y
      constructor
      · intro hy
        by_cases hyr : y ∈ Set.range r
        · obtain ⟨x, rfl⟩ := hyr
          refine Or.inl ⟨x, ?_, rfl⟩
          have : h (r x) ∈ C := hy
          rw [hh] at this
          exact this
        · exact Or.inr hyr
      · rintro (⟨x, hx, rfl⟩ | hy)
        · show h (r x) ∈ C
          rw [hh]
          exact hx
        · show h y ∈ C
          rw [hout y hy]
          exact h0
    rw [e]
    exact himg.union hrange.compl
  · have e : h ⁻¹' C = r '' (H ⁻¹' C) := by
      ext y
      constructor
      · intro hy
        by_cases hyr : y ∈ Set.range r
        · obtain ⟨x, rfl⟩ := hyr
          refine ⟨x, ?_, rfl⟩
          have : h (r x) ∈ C := hy
          rw [hh] at this
          exact this
        · have : h y ∈ C := hy
          rw [hout y hyr] at this
          exact absurd this h0
      · rintro ⟨x, hx, rfl⟩
        show h (r x) ∈ C
        rw [hh]
        exact hx
    rw [e]
    exact himg
end

