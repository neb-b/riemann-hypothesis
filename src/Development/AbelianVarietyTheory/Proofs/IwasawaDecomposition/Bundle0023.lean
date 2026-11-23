module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOneTmulOfForallFixed
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0012
public import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasicOpenEqZeroOfMemIInfPowSmul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
section
open NumberField IsDedekindDomain

namespace GlobalTheory

noncomputable def unitaryCharToCircle {A : Type} [CommGroup A] (a : A →* ℂˣ)
    (ha : ∀ y, ‖((a y : ℂˣ) : ℂ)‖ = 1) : A →* Circle where
  toFun y := ⟨(a y : ℂ), by simpa [Submonoid.unitSphere] using ha y⟩
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    exact (congrArg (fun u : ℂˣ => (u : ℂ)) (map_mul a x y)).trans (Units.val_mul _ _)

theorem toUnits_unitaryCharToCircle {A : Type} [CommGroup A] (a : A →* ℂˣ)
    (ha : ∀ y, ‖((a y : ℂˣ) : ℂ)‖ = 1) (y : A) :
    Circle.toUnits (unitaryCharToCircle a ha y) = a y := by
  ext
  rfl

private lemma continuous_toUnits_comp {X : Type} [TopologicalSpace X] {f : X → Circle}
    (hf : Continuous f) : Continuous fun x => Circle.toUnits (f x) := by
  rw [Units.continuous_iff]
  refine ⟨continuous_subtype_val.comp hf, ?_⟩
  have h : (fun x => (((Circle.toUnits (f x))⁻¹ : ℂˣ) : ℂ)) = fun x => (((f x)⁻¹ : Circle) : ℂ) := by
    funext x
    simp
  rw [h]
  exact continuous_subtype_val.comp hf.inv

theorem exists_unitary_char_of_open_subgroup_and_hom :
    ∀ (G A : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [CommGroup A] (U : Subgroup G), IsOpen (U : Set G) → ∀ (α : A →* G) (a : A →* ℂˣ) (ψ : G →* ℂˣ), Continuous ψ → (∀ x, ‖((ψ x : ℂˣ) : ℂ)‖ = 1) → (∀ y, ‖((a y : ℂˣ) : ℂ)‖ = 1) → (∀ y, α y ∈ U → a y = ψ (α y)) → ∃ χ : G →* ℂˣ, Continuous χ ∧ (∀ x, ‖((χ x : ℂˣ) : ℂ)‖ = 1) ∧ (∀ x ∈ U, χ x = ψ x) ∧ ∀ y, χ (α y) = a y := by
  intro G A _ _ _ _ U hU α a ψ hψc hψ ha hagree
  let _ : TopologicalSpace A := ⊥
  have _ : DiscreteTopology A := ⟨rfl⟩

  set ψ₁ : G →* Circle := unitaryCharToCircle ψ hψ
  set a₁ : A →* Circle := unitaryCharToCircle a ha
  have hψ₁c : Continuous ψ₁ := Continuous.subtype_mk (Units.continuous_val.comp hψc) _
  have hψ₁coe : ∀ x, ((ψ₁ x : Circle) : ℂ) = (ψ x : ℂ) := fun x => rfl
  have ha₁coe : ∀ y, ((a₁ y : Circle) : ℂ) = (a y : ℂ) := fun y => rfl

  let H : Subgroup (G × A) := U.prod ⊤
  have hH : IsOpen (H : Set (G × A)) := by
    simpa [H, Subgroup.coe_prod] using hU.prod isOpen_univ
  let N : Subgroup (G × A) := (MonoidHom.prod α (MonoidHom.id A)).range
  let φ : H →* Circle :=
    ((ψ₁.comp (MonoidHom.fst G A)) / (a₁.comp (MonoidHom.snd G A))).comp H.subtype
  have hφ : ∀ x : H, φ x = ψ₁ (x : G × A).1 / a₁ (x : G × A).2 := fun x => rfl
  have hφc : Continuous φ := by
    have h1 : Continuous fun x : H => ψ₁ (x : G × A).1 :=
      hψ₁c.comp (continuous_fst.comp continuous_subtype_val)
    have h2 : Continuous fun x : H => a₁ (x : G × A).2 :=
      continuous_of_discreteTopology.comp (continuous_snd.comp continuous_subtype_val)
    have hfun : (φ : H → Circle) = fun x : H => ψ₁ (x : G × A).1 / a₁ (x : G × A).2 := funext hφ
    rw [hfun]
    exact h1.div' h2

  have htriv : ∀ x : H, (x : G × A) ∈ N → φ x = 1 := by
    rintro ⟨x, hxH⟩ ⟨y, rfl⟩
    have hyU : α y ∈ U := (Subgroup.mem_prod.1 hxH).1
    change ψ₁ (α y) / a₁ y = 1
    rw [div_eq_one]
    apply Circle.ext
    rw [hψ₁coe, ha₁coe, hagree y hyU]
  obtain ⟨χ₂, hχ₂c, hχ₂N, hχ₂H⟩ :=
    exists_continuous_circle_char_extension (G × A) H N φ hH hφc htriv

  refine ⟨Circle.toUnits.comp (χ₂.comp (MonoidHom.inl G A)), ?_, ?_, ?_, ?_⟩
  · exact continuous_toUnits_comp (hχ₂c.comp (continuous_id.prodMk continuous_const))
  · intro x
    exact Circle.norm_coe _
  · intro x hx
    have hxH : ((x, 1) : G × A) ∈ H := Subgroup.mem_prod.2 ⟨hx, Subgroup.mem_top 1⟩
    have h : χ₂ (x, 1) = ψ₁ x / a₁ 1 := hχ₂H ⟨(x, 1), hxH⟩
    change Circle.toUnits (χ₂ (x, 1)) = ψ x
    rw [h, map_one, div_one]
    exact toUnits_unitaryCharToCircle ψ hψ x
  · intro y
    have hN : ((α y, y) : G × A) ∈ N := ⟨y, rfl⟩
    have h0 : χ₂ (α y, y) = 1 := hχ₂N _ hN
    have hyH : ((1, y) : G × A) ∈ H := Subgroup.mem_prod.2 ⟨U.one_mem, Subgroup.mem_top y⟩
    have h1 : χ₂ (1, y) = ψ₁ 1 / a₁ y := hχ₂H ⟨(1, y), hyH⟩
    have hsplit : ((α y, y) : G × A) = (α y, 1) * (1, y) :=
      Prod.ext (mul_one _).symm (one_mul _).symm
    rw [hsplit, map_mul, h1, map_one, one_div, mul_inv_eq_one] at h0
    change Circle.toUnits (χ₂ (α y, 1)) = a y
    rw [h0]
    exact toUnits_unitaryCharToCircle a ha y

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalEigenspaceSumSqInvariantFieldsA
section
open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory

theorem finiteDimensional_eigenspace_sum_sq_invariantFields : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] (L : Type) [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L] (S : Submodule ℂ (K → ℂ)), (∀ f ∈ S, Continuous f) → ∀ e : L → K, (∀ X : L, Continuous fun t : ℝ => e (t • X)) → e 0 = 1 → (∀ r : ℝ, 0 < r → e '' Metric.ball 0 r ∈ 𝓝 (1 : K)) → ∀ d : L → Module.End ℂ S, (∀ X Y, d (X + Y) = d X + d Y) → (∀ (a : ℝ) X, d (a • X) = (a : ℂ) • d X) → (∀ (X : L) (f : S) (x : K) (t : ℝ), HasDerivAt (fun t : ℝ => f.1 (x * e (t • X))) ((d X f).1 (x * e (t • X))) t) → ∀ (ι : Type) [Fintype ι] (X : ι → L), Submodule.span ℝ (Set.range X) = ⊤ → ∀ lam : ℂ, FiniteDimensional ℂ (Module.End.eigenspace (∑ i, d (X i) * d (X i)) lam) := by
  intro K _ _ _ _ _ L _ _ _ S hS e he he0 hU d hadd hsmul hder ι _ X hX lam
  classical
  letI : MeasurableSpace K := borel K
  haveI : BorelSpace K := ⟨rfl⟩
  set μ : Measure K := haarProb K with hμ
  have hc : ∀ f : S, Continuous f.1 := fun f => hS f.1 f.2
  have hint : ∀ {F : Type} [NormedAddCommGroup F] {g : K → F}, Continuous g → Integrable g μ :=
    fun hg => hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : ∀ f g : S, Integrable (fun x => (starRingEnd ℂ) (f.1 x) * g.1 x) μ :=
    fun f g => hint ((Complex.continuous_conj.comp (hc f)).mul (hc g))

  have hskew : ∀ (Y : L) (f : S), ((∫ x, ‖(d Y f).1 x‖ ^ 2 ∂μ : ℝ) : ℂ) +
      ∫ x, (starRingEnd ℂ) (f.1 x) * (d Y (d Y f)).1 x ∂μ = 0 := by
    intro Y f
    have c1 : Continuous fun x => (starRingEnd ℂ) (f.1 x) :=
      Complex.continuous_conj.comp (hc f)
    have c2 : Continuous fun x => (starRingEnd ℂ) ((d Y f).1 x) :=
      Complex.continuous_conj.comp (hc _)
    have h := (_root_.GlobalTheory.right_translation_curve_sq_le_and_integral_deriv_eq_zero K μ (fun t => e (t • Y)) (he Y) (by simp [he0])
      (fun x => (starRingEnd ℂ) (f.1 x) * (d Y f).1 x)
      (fun x => (starRingEnd ℂ) ((d Y f).1 x) * (d Y f).1 x
        + (starRingEnd ℂ) (f.1 x) * (d Y (d Y f)).1 x)
      (c1.mul (hc _)) ((c2.mul (hc _)).add (c1.mul (hc _)))
      (fun x t => (hder Y f x t).star.mul (hder Y (d Y f) x t))).2
    rw [integral_add (hi2 _ _) (hi2 _ _)] at h
    rw [← h, ← integral_complex_ofReal]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [Complex.conj_mul']
  have hsum : ∀ f : S, f ∈ Module.End.eigenspace (∑ i, d (X i) * d (X i)) lam →
      ∑ i, ∫ x, ‖(d (X i) f).1 x‖ ^ 2 ∂μ ≤ ‖lam‖ * ∫ x, ‖f.1 x‖ ^ 2 ∂μ := by
    intro f hf
    rw [Module.End.mem_eigenspace_iff] at hf
    have h1 : ∑ i, ∫ x, (starRingEnd ℂ) (f.1 x) * (d (X i) (d (X i) f)).1 x ∂μ
        = lam * ((∫ x, ‖f.1 x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
      rw [← integral_finsetSum _ (fun i _ => hi2 _ _), ← integral_complex_ofReal,
        ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      have h2 := congrArg (fun g : S => g.1 x) hf
      simp only [LinearMap.sum_apply, Module.End.mul_apply, Submodule.coe_sum, Finset.sum_apply,
        Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at h2
      simp only
      rw [← Finset.mul_sum, h2, mul_left_comm, Complex.conj_mul']
      simp
    have h3 : ((∑ i, ∫ x, ‖(d (X i) f).1 x‖ ^ 2 ∂μ : ℝ) : ℂ)
        = - (lam * ((∫ x, ‖f.1 x‖ ^ 2 ∂μ : ℝ) : ℂ)) := by
      rw [← h1, Complex.ofReal_sum, eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun i _ => hskew _ _
    have h4 := congrArg norm h3
    rw [norm_neg, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (a := ∫ x, ‖f.1 x‖ ^ 2 ∂μ)
        (integral_nonneg fun x => by positivity)] at h4
    rw [← h4]
    exact le_abs_self _
  obtain ⟨a, ha⟩ := (Fintype.linearCombination ℝ X).exists_rightInverse_of_surjective
    (by rw [Fintype.range_linearCombination, hX])
  have hac : Continuous a := a.continuous_of_finiteDimensional
  have hd0 : d 0 = 0 := by
    have := hsmul 0 0
    simpa using this
  have hdY : ∀ Y, d Y = ∑ i, ((a Y i : ℝ) : ℂ) • d (X i) := by
    intro Y
    have h1 : Y = ∑ i, a Y i • X i := by
      have := LinearMap.congr_fun ha Y
      simpa [Fintype.linearCombination_apply] using this.symm
    let D : L →+ Module.End ℂ S := ⟨⟨d, hd0⟩, hadd⟩
    calc d Y = D (∑ i, a Y i • X i) := congrArg d h1
      _ = ∑ i, D (a Y i • X i) := map_sum D _ _
      _ = _ := Finset.sum_congr rfl fun i _ => hsmul _ _
  have hbound : ∀ (Y : L) (f : S), ∫ x, ‖(d Y f).1 x‖ ^ 2 ∂μ ≤
      (∑ i, (a Y i) ^ 2) * ∑ i, ∫ x, ‖(d (X i) f).1 x‖ ^ 2 ∂μ := by
    intro Y f
    have ci : ∀ g : S, Continuous fun x => ‖g.1 x‖ ^ 2 := fun g => (hc g).norm.pow 2
    rw [← integral_finsetSum _ (fun i _ => hint (ci _)), ← integral_const_mul]
    refine integral_mono (hint (ci _))
      (hint (continuous_const.mul (continuous_finsetSum _ fun i _ => ci _))) fun x => ?_
    have h1 : ‖(d Y f).1 x‖ ≤ ∑ i, |a Y i| * ‖(d (X i) f).1 x‖ := by
      rw [hdY Y]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Finset.sum_apply,
        Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      simp
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |a Y i|)
      (fun i => ‖(d (X i) f).1 x‖)
    simp only [sq_abs] at h2
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have hcont : Continuous fun Y : L => (∑ i, (a Y i) ^ 2) * ‖lam‖ := by fun_prop
  have hev : ∀ᶠ Y in 𝓝 (0 : L), (∑ i, (a Y i) ^ 2) * ‖lam‖ < 1 / 4 :=
    hcont.continuousAt.eventually_lt continuousAt_const (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hfin := _root_.GlobalTheory.finiteDimensional_of_uniformly_almost_invariant K μ
    ((Module.End.eigenspace (∑ i, d (X i) * d (X i)) lam).map S.subtype)
    (by rintro _ ⟨f, -, rfl⟩; exact hc f) _ (hU r hr) (by
      rintro _ ⟨f, hf, rfl⟩ _ ⟨Y, hY, rfl⟩
      have h := (_root_.GlobalTheory.right_translation_curve_sq_le_and_integral_deriv_eq_zero K μ (fun t => e (t • Y)) (he Y) (by simp [he0])
        f.1 (d Y f).1 (hc _) (hc _) (hder Y f)).1
      simp only [one_smul] at h
      have hn : 0 ≤ ∫ x, ‖f.1 x‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
      have hs : 0 ≤ ∑ i, (a Y i) ^ 2 := Finset.sum_nonneg fun i _ => by positivity
      calc _ ≤ _ := h
        _ ≤ _ := hbound Y f
        _ ≤ (∑ i, (a Y i) ^ 2) * (‖lam‖ * ∫ x, ‖f.1 x‖ ^ 2 ∂μ) :=
          mul_le_mul_of_nonneg_left (hsum f hf) hs
        _ = ((∑ i, (a Y i) ^ 2) * ‖lam‖) * ∫ x, ‖f.1 x‖ ^ 2 ∂μ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hball Y hY).le hn)
  exact (Submodule.equivMapOfInjective S.subtype S.subtype_injective _).symm.finiteDimensional

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalKerAevalOfEigenspacesStatement
section
open MeasureTheory Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_ker_aeval_of_eigenspaces' : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M), (∀ lam : ℂ, FiniteDimensional ℂ (T.eigenspace lam)) → ∀ p : Polynomial ℂ, p ≠ 0 → FiniteDimensional ℂ (LinearMap.ker (Polynomial.aeval T p)) := by
  first | exact @GlobalTheory.finiteDimensional_ker_aeval_of_eigenspaces | exact GlobalTheory.finiteDimensional_ker_aeval_of_eigenspaces | (intros; apply GlobalTheory.finiteDimensional_ker_aeval_of_eigenspaces <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankIInfKerOfIsBaseChange
section
open TensorProduct Module

namespace GlobalTheory

theorem finrank_iInf_ker_of_isBaseChange : ∀ (L Ω M M' ι : Type) [Field L] [Field Ω] [Algebra L Ω]
    [AddCommGroup M] [Module L M] [AddCommGroup M'] [Module Ω M'] [Module L M']
    [IsScalarTower L Ω M'] (J : M →ₗ[L] M') (f : ι → M →ₗ[L] M) (f' : ι → M' →ₗ[Ω] M'),
    IsBaseChange Ω J → (∀ i x, f' i (J x) = J (f i x)) →
      finrank Ω ↥(⨅ i, LinearMap.ker (f' i)) = finrank L ↥(⨅ i, LinearMap.ker (f i)) := by
  intro L Ω M M' ι _ _ _ _ _ _ _ _ _ J f f' hJ hf
  have h1 : ⨅ i, LinearMap.ker (f' i) =
      Submodule.span Ω (J '' (⨅ i, LinearMap.ker (f i) : Submodule L M)) := by
    rw [GlobalTheory.GaloisDescent.span_image_iInf hJ]
    exact iInf_congr fun i =>
      (GlobalTheory.GaloisDescent.span_image_ker hJ hJ (f i) (f' i) (fun v => hf i v)).symm
  have h2 : Submodule.span Ω (J '' (⨅ i, LinearMap.ker (f i) : Submodule L M)) =
      ((⨅ i, LinearMap.ker (f i) : Submodule L M).baseChange Ω).map hJ.equiv.toLinearMap := by
    rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, Set.image_image]
    congr 2
    ext x
    simp [IsBaseChange.equiv_tmul]
  rw [h1, h2, LinearEquiv.finrank_map_eq, GlobalTheory.finrank_baseChange]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatComapMapOfOneTmulMemStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_map_comap_of_one_tmul_mem_map : ∀ {B C R : Type} [CommRing B] [CommRing C] [CommRing R] [Algebra B C] [Algebra B R] [Module.Flat B R] (J : Ideal C) (r : R), (1 : C) ⊗ₜ[B] r ∈ J.map (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[B] R) → r ∈ (J.comap (algebraMap B C)).map (algebraMap B R) := by
  first | exact @GlobalTheory.flat_comap_map_of_one_tmul_mem | exact GlobalTheory.flat_comap_map_of_one_tmul_mem | (intros; apply GlobalTheory.flat_comap_map_of_one_tmul_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GermSectionsHalfPlaneGlobalSectionStatement
section
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germSections_halfPlane_global_section : ∀ (Y : Type) (G : ℂ → (ℂ → Y) → Prop) (T : ℝ), (∀ w s s', s =ᶠ[𝓝 w] s' → G w s → G w s') → (∀ w : ℂ, T < w.im → ∃ s, ∀ᶠ z in 𝓝 w, G z s) → (∀ (U : Set ℂ) (s s' : ℂ → Y), IsOpen U → Convex ℝ U → (∀ z ∈ U, T < z.im) → (∀ z ∈ U, G z s) → (∀ z ∈ U, G z s') → ∀ w ∈ U, s w = s' w → Set.EqOn s s' U) → (∀ (U : Set ℂ) (s s' : ℂ → Y), IsOpen U → Convex ℝ U → (∀ z ∈ U, T < z.im) → (∀ z ∈ U, G z s) → ∀ w ∈ U, G w s' → ∃ s'' : ℂ → Y, (∀ z ∈ U, G z s'') ∧ s'' w = s' w) → ∃ s : ℂ → Y, ∀ w : ℂ, T < w.im → G w s := by
  first | exact @GlobalTheory.germSections_halfPlane_global | exact GlobalTheory.germSections_halfPlane_global | (intros; apply GlobalTheory.germSections_halfPlane_global <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtInvDetAndInvAtIdentity
section
open Matrix

namespace GlobalTheory.Mem.InvDer

theorem hasDerivAt_inv_det_and_inv (n : ℕ) (M : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (M' : Matrix (Fin n) (Fin n) ℂ) (h0 : M 0 = 1)
    (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) 0) :
    HasDerivAt (fun t => ((M t).det)⁻¹) (-M'.trace) 0 ∧
      ∀ i j, HasDerivAt (fun t => (M t)⁻¹ i j) (-M' i j) 0 := by
  have hd := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det M M' 0 hM
  rw [h0, adjugate_one, Matrix.one_mul] at hd
  have hdet0 : (M 0).det = 1 := by rw [h0, det_one]
  have hne : (M 0).det ≠ 0 := by rw [hdet0]; exact one_ne_zero
  have hinv : HasDerivAt (fun t => ((M t).det)⁻¹) (-M'.trace) 0 := by
    have h1 : HasDerivAt (fun z : ℂ => z⁻¹) (-((M 0).det ^ 2)⁻¹) (M 0).det := hasDerivAt_inv hne
    have h2 := h1.comp_of_eq (0 : ℝ) hd rfl
    refine HasDerivAt.congr_deriv h2 ?_
    rw [hdet0]; simp
  refine ⟨hinv, ?_⟩
  have hdiff : ∀ i j, DifferentiableAt ℝ (fun t => (M t)⁻¹ i j) 0 := by
    intro i j
    have hadj : DifferentiableAt ℝ (fun t => (M t).adjugate i j) 0 := by
      have := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det (fun t => (M t).updateRow j (Pi.single i 1))
        (M'.updateRow j 0) 0 (by
          intro a b
          by_cases h : a = j
          · simp only [updateRow_apply, h, if_true]
            exact hasDerivAt_const _ _
          · simp only [updateRow_apply, h, if_false]
            exact hM a b)
      simpa only [adjugate_apply] using this.differentiableAt
    have := hinv.differentiableAt.mul hadj
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp [Matrix.inv_def, Ring.inverse_eq_inv']
  intro i j
  have hev : ∀ᶠ t in nhds (0 : ℝ), (M t).det ≠ 0 := hd.continuousAt.eventually_ne hne
  have hprod : HasDerivAt (fun t => ∑ k, (M t)⁻¹ i k * M t k j)
      (∑ k, (deriv (fun t => (M t)⁻¹ i k) 0 * M 0 k j + (M 0)⁻¹ i k * M' k j)) 0 :=
    HasDerivAt.fun_sum fun k _ => ((hdiff i k).hasDerivAt.fun_mul (hM k j))
  have hconst : HasDerivAt (fun t => ∑ k, (M t)⁻¹ i k * M t k j) 0 0 := by
    refine (hasDerivAt_const (0 : ℝ) ((1 : Matrix (Fin n) (Fin n) ℂ) i j)).congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr ht)]
  have huniq := hprod.unique hconst
  rw [h0, inv_one, Finset.sum_add_distrib] at huniq
  simp [Matrix.one_apply] at huniq
  have hfin : deriv (fun t => (M t)⁻¹ i j) 0 = -M' i j := eq_neg_of_add_eq_zero_left huniq
  rw [← hfin]
  exact (hdiff i j).hasDerivAt

end GlobalTheory.Mem.InvDer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvEntryNormLeOfSubSmulOnePosSemidefStatement
section
open Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_entry_norm_le_of_sub_smul_one_posSemidef : ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (c : ℝ), 0 < c → (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ∀ i j, ‖(Y.map Complex.ofReal)⁻¹ i j‖ ≤ 1 / c := by
  first | exact @GlobalTheory.inv_entry_norm_le_of_sub_posSemidef | exact GlobalTheory.inv_entry_norm_le_of_sub_posSemidef | (intros; apply GlobalTheory.inv_entry_norm_le_of_sub_posSemidef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegrallyClosedOfConductorNonZeroDivisorOfAss
section
open IsLocalRing

namespace GlobalTheory

theorem isIntegrallyClosed_of_conductor_nonZeroDivisor_of_associatedPrimes
    (R : Type) [CommRing R] [IsNoetherianRing R] (x : R) (hx : x ∈ nonZeroDivisors R)
    (hloc : ∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) →
      ∃ _ : IsDomain (Localization.AtPrime P), IsIntegrallyClosed (Localization.AtPrime P))
    (hcond : ∀ c : FractionRing R, IsIntegral R c →
      ∃ s : R, algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) x * c) :
    IsIntegrallyClosed R := by
  rw [isIntegrallyClosed_iff (FractionRing R)]
  intro c hc
  obtain ⟨s, hs⟩ := hcond c hc

  suffices hmem : Ideal.Quotient.mk (Ideal.span {x}) s = 0 by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hmem
    obtain ⟨w, rfl⟩ := hmem
    refine ⟨w, ?_⟩
    have hu : IsUnit (algebraMap R (FractionRing R) x) :=
      IsLocalization.map_units (FractionRing R) ⟨x, hx⟩
    apply hu.mul_left_cancel
    rw [← hs, map_mul, mul_comm]
  have key := eq_zero_of_forall_associatedPrimes_exists_smul_eq_zero
    (A := R) (M := R ⧸ Ideal.span {x}) (x := Ideal.Quotient.mk (Ideal.span {x}) s)
  apply key
  intro P hP
  haveI hPp : P.IsPrime := hP.isPrime
  obtain ⟨hdom, hic⟩ := hloc P hP
  let RP := Localization.AtPrime P
  let K := FractionRing RP

  have hreg : ∀ b ∈ nonZeroDivisors R, IsUnit (algebraMap R K b) := by
    intro b hb
    rw [IsScalarTower.algebraMap_apply R RP K]
    refine IsLocalization.map_units K (⟨algebraMap R RP b, ?_⟩ : nonZeroDivisors RP)
    refine mem_nonZeroDivisors_of_ne_zero fun h0 ↦ ?_
    obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl RP b).1 h0
    have : (t : R) = 0 := (mem_nonZeroDivisors_iff_right.1 hb) t ht
    exact t.2 (this ▸ P.zero_mem)
  let φ : FractionRing R →+* K :=
    IsLocalization.lift (M := nonZeroDivisors R) (g := algebraMap R K) fun b ↦ hreg b b.2
  have hφ : ∀ r : R, φ (algebraMap R (FractionRing R) r) = algebraMap RP K (algebraMap R RP r) :=
    fun r ↦ by
      rw [IsLocalization.lift_eq, IsScalarTower.algebraMap_apply R RP K]
  have hint : IsIntegral RP (φ c) := by
    refine IsIntegral.map_of_comp_eq (algebraMap R RP) φ ?_ hc
    ext r
    simp only [RingHom.comp_apply]
    rw [hφ]
  obtain ⟨u, hu⟩ := (isIntegrallyClosed_iff K).1 hic hint
  have hxu : algebraMap R RP x * u = algebraMap R RP s := by
    apply IsFractionRing.injective RP K
    rw [map_mul, hu, ← hφ, ← hφ, hs, map_mul]
  obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.surj P.primeCompl u
  have h2 : algebraMap R RP (x * r) = algebraMap R RP (s * t) := by
    simp only at hrt
    rw [map_mul, map_mul, ← hxu, ← hrt]
    ring
  obtain ⟨t', ht'⟩ := (IsLocalization.eq_iff_exists P.primeCompl RP).1 h2
  refine ⟨t' * t, P.primeCompl.mul_mem t'.2 t.2, ?_⟩
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton']
  refine ⟨t' * r, ?_⟩
  linear_combination ht'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitMapOfMemNonZeroDivisorsTensorStatement
section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_map_of_mem_nonZeroDivisors_tensor' : ∀ (T U C F K L : Type) [CommRing T] [IsDomain T] [CommRing U] [IsDomain U] [CommRing C] [IsDomain C] [Field F] [Field K] [Field L] [Algebra T U] [Algebra T C] [Algebra T F] [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra U L] [IsFractionRing U L] [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Algebra T L] [Algebra F L] [IsScalarTower T U L] [IsScalarTower T F L] [Module.Finite T C] (φ : U ⊗[T] C →+* L ⊗[F] K), Function.Injective φ → (∀ u c, φ (u ⊗ₜ c) = algebraMap U L u ⊗ₜ algebraMap C K c) → ∀ s ∈ nonZeroDivisors (U ⊗[T] C), IsUnit (φ s) := by
  first | exact @GlobalTheory.isUnit_map_of_mem_nonZeroDivisors_tensor | exact GlobalTheory.isUnit_map_of_mem_nonZeroDivisors_tensor | (intros; apply GlobalTheory.isUnit_map_of_mem_nonZeroDivisors_tensor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationAtPrimeIsDiscreteValuationRingOfHeig
section
namespace GlobalTheory

theorem localizationAtPrime_isDiscreteValuationRing_of_height_eq_one :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      (q : Ideal A) [q.IsPrime], q.height = 1 → IsDiscreteValuationRing (Localization.AtPrime q) := by
  intro A _ _ _ _ q _ hq
  exact isDiscreteValuationRing_of_height_eq_one q hq (Localization.AtPrime q)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSpanMapOfEvalMemOfNeZeroStatement
section
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_map_of_eval_mem_of_ne_zero : ∀ (k : Type) [Field k] [Infinite k] (σ τ : Type) (M : Submodule k (MvPolynomial σ k)) (D : MvPolynomial τ k), D ≠ 0 → ∀ P : MvPolynomial σ (MvPolynomial τ k), (∀ y : τ → k, MvPolynomial.eval y D ≠ 0 → MvPolynomial.map (MvPolynomial.eval y) P ∈ M) → P ∈ Submodule.span (MvPolynomial τ k) (MvPolynomial.map (algebraMap k (MvPolynomial τ k)) '' (M : Set (MvPolynomial σ k))) := by
  first | exact @GlobalTheory.mem_span_map_of_eval_mem | exact GlobalTheory.mem_span_map_of_eval_mem | (intros; apply GlobalTheory.mem_span_map_of_eval_mem <;> assumption)
end

