module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsVecFixGroup

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PSemidirectCovering
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory MeasureTheory.Measure Topology
open scoped ENNReal

noncomputable section

theorem SemidirectCovering.proof (H L N : Type*) [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H]
    [MeasurableSpace H] [BorelSpace H] [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    [LocallyCompactSpace L] [SecondCountableTopology L] [T2Space L] [MeasurableSpace L]
    [BorelSpace L] [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N]
    [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] :
    SemidirectCovering.Statement H L N := by
  intro i q j hi hq hj hqi hker μL _ μN _ hconj Γ C T hC hT hTfin hCcov hTcov ν _
  have hqj : ∀ n, q (j n) = 1 := fun n => (hker _).2 ⟨n, rfl⟩
  have hmem : ∀ g, g * (i (q g))⁻¹ ∈ Set.range j := fun g =>
    (hker _).1 (by simp [hqi])
  let e := Equiv.ofInjective j hj.injective
  let k : H → N := fun g => e.symm ⟨g * (i (q g))⁻¹, hmem g⟩
  have hjk : ∀ g, j (k g) = g * (i (q g))⁻¹ := fun g =>
    Equiv.apply_ofInjective_symm hj.injective _
  have hk : Continuous k := by
    rw [hj.isEmbedding.continuous_iff]
    have : (j ∘ k) = fun g => g * (i (q g))⁻¹ := funext hjk
    rw [this]; fun_prop

  let Φ : N × L ≃ₜ H :=
    { toFun := fun p => j p.1 * i p.2
      invFun := fun g => (k g, q g)
      left_inv := fun p => by
        have h1 : q (j p.1 * i p.2) = p.2 := by simp [hqj, hqi]
        refine Prod.ext (hj.injective ?_) h1
        rw [hjk, h1]; simp
      right_inv := fun g => by simp [hjk]
      continuous_toFun := by fun_prop
      continuous_invFun := hk.prodMk hq }
  have hΦ : ∀ p, Φ p = j p.1 * i p.2 := fun _ => rfl
  let μ' : Measure H := (μN.prod μL).map Φ
  have : IsFiniteMeasureOnCompacts μ' := ⟨fun K hK => by
    rw [Measure.map_apply Φ.continuous.measurable hK.isClosed.measurableSet]
    exact (Φ.isCompact_preimage.2 hK).measure_lt_top⟩
  have : IsOpenPosMeasure μ' := Φ.continuous.isOpenPosMeasure_map Φ.surjective
  have : IsMulLeftInvariant μ' := by
    refine ⟨fun h => ?_⟩
    obtain ⟨⟨n₀, l₀⟩, rfl⟩ := Φ.surjective h

    let c : N → N := fun n => k (i l₀ * j n * (i l₀)⁻¹)
    have hjc : ∀ n, j (c n) = i l₀ * j n * (i l₀)⁻¹ := fun n => by
      simp only [c, hjk, map_mul, map_inv, hqj, hqi]; simp
    have hcc : Continuous c := by fun_prop
    have hcμ : MeasurePreserving c μN μN := by
      refine ⟨hcc.measurable, ?_⟩
      have hjm := hj.measurableEmbedding
      calc μN.map c = (((μN.map c).map j).comap j) := (hjm.comap_map _).symm
        _ = ((μN.map j).comap j) := by
          rw [Measure.map_map hjm.measurable hcc.measurable,
            show j ∘ c = fun n => i l₀ * j n * (i l₀)⁻¹ from funext hjc, hconj l₀]
        _ = μN := hjm.comap_map _
    have hF : MeasurePreserving (Prod.map (fun n => n₀ * c n) (fun l => l₀ * l))
        (μN.prod μL) (μN.prod μL) :=
      ((measurePreserving_mul_left μN n₀).comp hcμ).prod (measurePreserving_mul_left μL l₀)
    have hcomp : (fun g => Φ (n₀, l₀) * g) ∘ Φ =
        Φ ∘ Prod.map (fun n => n₀ * c n) (fun l => l₀ * l) := by
      funext ⟨n, l⟩
      simp only [Function.comp_apply, hΦ, Prod.map_fst, Prod.map_snd, map_mul, hjc]
      group
    simp only [μ']
    rw [Measure.map_map (measurable_const_mul _) Φ.continuous.measurable, hcomp,
      ← Measure.map_map Φ.continuous.measurable hF.measurable, hF.map_eq]
  have : IsHaarMeasure μ' := {}

  refine ⟨Φ.symm ⁻¹' (C ×ˢ T), Φ.symm.continuous.measurable (hC.isClosed.measurableSet.prod hT),
    ?_, ?_⟩
  · rw [isMulLeftInvariant_eq_smul ν μ', Measure.smul_apply,
      Measure.map_apply Φ.continuous.measurable
        (Φ.symm.continuous.measurable (hC.isClosed.measurableSet.prod hT))]
    have : Φ ⁻¹' (Φ.symm ⁻¹' (C ×ˢ T)) = C ×ˢ T := by ext p; simp
    rw [this, Measure.prod_prod, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top hC.measure_lt_top hTfin)
  · intro g
    obtain ⟨γ₁, hγ₁, hγ₁T⟩ := hTcov (q g)
    obtain ⟨δ, hδ, hδC⟩ := hCcov (k (γ₁ * g))
    refine ⟨j δ * γ₁, Γ.mul_mem hδ hγ₁, ?_⟩
    have h1 : q (j δ * γ₁ * g) = q γ₁ * q g := by simp [hqj]
    have h2 : k (j δ * γ₁ * g) = δ * k (γ₁ * g) := by
      apply hj.injective
      rw [hjk, h1, map_mul j, hjk, map_mul i]
      simp [mul_assoc]
    show (k (j δ * γ₁ * g), q (j δ * γ₁ * g)) ∈ C ×ˢ T
    rw [h1, h2]
    exact ⟨hδC, hγ₁T⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnfoldAlongSubgroup
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory
open scoped ENNReal Pointwise

theorem UnfoldAlongSubgroup.proof (G Y : Type*) [Group G] [MeasurableSpace G] [MeasurableSpace Y] :
    UnfoldAlongSubgroup.Statement G Y := by
  intro μ H _ ν _ _ ρ _ s hm hμ Γ _ hΓH FD FD₀ hFD hFD₀ f hf hfH
  have hms : ∀ y, Measurable (fun x : H => (x : G) * s y) := fun y =>
    hm.comp measurable_prodMk_right

  have hnull : ∀ Z : Set G, μ Z = 0 →
      ∀ᵐ y ∂ρ, ν ((fun x : H => (x : G) * s y) ⁻¹' Z) = 0 := by
    intro Z hZ
    have hZm : MeasurableSet (toMeasurable μ Z) := measurableSet_toMeasurable μ Z
    have hin : ∀ y, ∫⁻ x, (toMeasurable μ Z).indicator 1 ((x : G) * s y) ∂ν =
        ν ((fun x : H => (x : G) * s y) ⁻¹' toMeasurable μ Z) := fun y => by
      rw [← lintegral_indicator_one (hZm.preimage (hms y))]
      rfl
    have h0 := hμ ((toMeasurable μ Z).indicator 1) (measurable_one.indicator hZm)
    rw [lintegral_indicator_one hZm, measure_toMeasurable, hZ] at h0
    simp only [hin] at h0
    have hmeas : Measurable fun y => ν ((fun x : H => (x : G) * s y) ⁻¹' toMeasurable μ Z) := by
      simp only [← hin]
      exact ((measurable_one.indicator hZm).comp hm).lintegral_prod_left'
    filter_upwards [(lintegral_eq_zero_iff hmeas).1 h0.symm] with y hy
    exact measure_mono_null (Set.preimage_mono (subset_toMeasurable μ Z)) hy

  let toΓ : Γ.subgroupOf H → Γ := fun γ => ⟨((γ : H) : G), Subgroup.mem_subgroupOf.1 γ.2⟩
  have htoΓ : Function.Injective toΓ := fun a b h => by
    simp only [toΓ, Subtype.mk.injEq] at h
    exact Subtype.ext (Subtype.ext h)
  have : Countable (Γ.subgroupOf H) := htoΓ.countable

  have hslice : ∀ y (γ : Γ.subgroupOf H) (A : Set G),
      (fun x : H => (x : G) * s y) ⁻¹' ((toΓ γ) • A) =
        γ • ((fun x : H => (x : G) * s y) ⁻¹' A) := by
    intro y γ A
    ext x
    simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def,
      smul_eq_mul, toΓ, InvMemClass.coe_inv, Subgroup.coe_mul, mul_assoc]

  obtain ⟨t, htFD, htm, htae⟩ := hFD.nullMeasurableSet.exists_measurable_subset_ae_eq
  have hZ1 : μ {g | ¬ ∃ γ : Γ, γ • g ∈ FD} = 0 := ae_iff.1 hFD.ae_covers
  have hZ2 : μ (FD \ t) = 0 := (ae_eq_set.1 htae).2
  have hZ3 : ∀ γ δ : Γ, ∀ᵐ y ∂ρ, γ ≠ δ →
      ν ((fun x : H => (x : G) * s y) ⁻¹' (γ • FD ∩ δ • FD)) = 0 := by
    intro γ δ
    by_cases h : γ = δ
    · exact ae_of_all _ fun _ h' => absurd h h'
    · filter_upwards [hnull _ (hFD.aedisjoint h)] with y hy _ using hy
  have hgood : ∀ᵐ y ∂ρ, ν ((fun x : H => (x : G) * s y) ⁻¹' t) = ν FD₀ := by
    filter_upwards [hnull _ hZ1, hnull _ hZ2, ae_all_iff.2 fun γ => ae_all_iff.2 (hZ3 γ)]
      with y h1 h2 h3
    have hae : (fun x : H => (x : G) * s y) ⁻¹' t =ᵐ[ν] (fun x : H => (x : G) * s y) ⁻¹' FD := by
      refine ae_eq_set.2 ⟨?_, h2⟩
      rw [Set.sdiff_eq_empty.2 (Set.preimage_mono htFD), measure_empty]
    have hFDy : IsFundamentalDomain (Γ.subgroupOf H) ((fun x : H => (x : G) * s y) ⁻¹' FD) ν :=
      { nullMeasurableSet := (htm.preimage (hms y)).nullMeasurableSet.congr hae
        ae_covers := by
          filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1] with x hx
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, not_not] at hx
          obtain ⟨γ, hγ⟩ := hx
          refine ⟨⟨⟨γ, hΓH γ.2⟩, Subgroup.mem_subgroupOf.2 γ.2⟩, ?_⟩
          simpa only [Set.mem_preimage, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul,
            mul_assoc] using hγ
        aedisjoint := by
          intro γ δ hγδ
          change ν (γ • _ ∩ δ • _) = 0
          rw [← hslice, ← hslice, ← Set.preimage_inter]
          exact h3 _ _ (htoΓ.ne hγδ) }
    rw [measure_congr hae, hFDy.measure_eq hFD₀]
  have hsm : Measurable s := by
    convert hm.comp ((measurable_const : Measurable fun _ : Y => (1 : H)).prodMk measurable_id) using 1
    ext y
    simp
  calc ∫⁻ g in FD, f g ∂μ = ∫⁻ g in t, f g ∂μ := setLIntegral_congr htae.symm
    _ = ∫⁻ g, t.indicator f g ∂μ := (lintegral_indicator htm _).symm
    _ = ∫⁻ y, ∫⁻ x, t.indicator f ((x : G) * s y) ∂ν ∂ρ := hμ _ (hf.indicator htm)
    _ = ∫⁻ y, f (s y) * ν ((fun x : H => (x : G) * s y) ⁻¹' t) ∂ρ := by
      refine lintegral_congr fun y => ?_
      have he : (fun x : H => t.indicator f ((x : G) * s y)) =
          ((fun x : H => (x : G) * s y) ⁻¹' t).indicator fun _ => f (s y) := by
        ext x
        by_cases hx : (x : G) * s y ∈ t
        · simp [hx, hfH]
        · simp [hx]
      rw [he, lintegral_indicator_const (htm.preimage (hms y))]
    _ = ∫⁻ y, ν FD₀ * f (s y) ∂ρ := lintegral_congr_ae (by
      filter_upwards [hgood] with y hy
      rw [hy, mul_comm])
    _ = ν FD₀ * ∫⁻ y, f (s y) ∂ρ := lintegral_const_mul _ (hf.comp hsm)

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnfoldingIntegral
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal ComplexOrder

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] [Fintype ι]
  [DecidableEq ι] in
theorem two_le_finrank_of_isotropic [FiniteDimensional E W] (h : HermitianForm F E W) {x₀ : W}
    (hne : x₀ ≠ 0) (hiso : h.toSesq x₀ x₀ = 0) : 2 ≤ finrank E W := by
  by_contra hlt
  have hpos : 0 < finrank E W := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨x₀, hne⟩
  have h1 : finrank E W = 1 := by omega
  have hspan := (finrank_eq_one_iff_of_nonzero' x₀ hne).mp h1
  apply hne
  apply h.nonsingular.1
  rw [map_zero]
  ext y
  obtain ⟨c, rfl⟩ := hspan y
  rw [LinearMap.zero_apply, map_smul, hiso, smul_zero]


omit [DecidableEq ι] in
theorem re_form_smul (P : Matrix ι ι ℂ) (b : ℂ) (y : ι → ℂ) :
    (star (b • y) ⬝ᵥ (P *ᵥ (b • y))).re = (star y ⬝ᵥ (P *ᵥ y)).re * ‖b‖ ^ 2 := by
  have hb : star b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, hb, Complex.re_ofReal_mul, mul_comm]

theorem UnfoldingIntegral.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : UnfoldingTorus.Statement h v)
    (h₂ : TorusIntegralHomogeneous.Statement (InfinitePlace E))
    (h₃ : DiscreteFundamentalDomain.Statement (archUnitary h v)) :
    UnfoldingIntegral.Statement h v := by
  intro M μ _ D La x₀ hLa hx₀ hne hiso
  have : FiniteDimensional E W := v.finiteDimensional_of_finite

  have hdisc : DiscreteTopology (vecStabGroup h v La x₀) := by
    have := ArchLatticeDiscrete.proof h v La hLa.isLattice
    have hle : vecStabGroup h v La x₀ ≤ archLatticeGroup h v La := by
      rintro _ ⟨γ, -, rfl⟩
      exact ⟨(γ : h.unitaryGroup), γ.2, rfl⟩
    exact DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective hle)
  obtain ⟨FD, -, hFD⟩ := h₃ μ _ hdisc
  obtain ⟨c, hc0, hctop, hc⟩ := h₁ M μ D La x₀ hLa hx₀ hne hiso
  set y := vecAt v x₀ with hy
  set q : InfinitePlace E → ℝ := fun w => (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re with hq_def
  have hq : ∀ w, 0 < q w := fun w =>
    (Complex.pos_iff.mp ((M.posDef w).dotProduct_mulVec_pos (VecAtNeZero.proof v x₀ hne w))).1
  obtain ⟨C, hC0, hCtop, hC⟩ := h₂ q hq (finrank E W - 2)

  obtain ⟨k, hk⟩ : ∃ k, finrank E W = k + 2 :=
    ⟨finrank E W - 2, by have := two_le_finrank_of_isotropic h hne hiso; omega⟩
  have hcard : Fintype.card (InfinitePlace E) = finrank ℚ F := by
    have h1 := IsTotallyComplex.finrank (K := E)
    have h2 : finrank ℚ F * finrank F E = finrank ℚ E := Module.finrank_mul_finrank ℚ F E
    rw [Algebra.IsQuadraticExtension.finrank_eq_two F E] at h2
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero]
    omega
  have hexp : (2 * (finrank E W - 2) + 2) * Fintype.card (InfinitePlace E) =
      2 * finrank ℚ F * (finrank E W - 1) := by
    rw [hcard, hk, Nat.add_sub_cancel, show k + 2 - 1 = k + 1 by omega]
    ring
  refine ⟨FD, hFD, c * C, ENNReal.mul_pos hc0.ne' hC0.ne', ENNReal.mul_lt_top hctop hCtop,
    fun t ht => ?_⟩

  have hset : {b : InfinitePlace E → ℂ | M.len (fun w => b w • y w) < t} =
      {b | ∑ w, q w * ‖b w‖ ^ 2 < t ^ 2} := by
    ext b
    simp only [Set.mem_ofPred_eq, Majorant.len, Real.sqrt_lt' ht, re_form_smul, hq_def,
      mul_comm]
  rw [hc FD hFD t ht, hset, hC t ht, hexp]
  exact (mul_assoc c C _).symm

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StComplementLattice
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

section Complement

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def ComplementLattice.Statement [FiniteDimensional E W] (h : HermitianForm F E W) : Prop :=
  ∀ v₀ w₀ : W, IsHyperbolicPair h v₀ w₀ → ∀ h' : HermitianForm F E (hypComplement h v₀ w₀),
    (∀ x y, h'.toSesq x y = h.toSesq x y) → ∀ D n : ℕ, 0 < n → ∃ D' : ℕ,
      ∀ La : AddSubgroup W, IsDIntegral h D La →
        (∀ x ∈ La, ∃ a ∈ lineCoeffs (E := E) La v₀, ∃ b ∈ lineCoeffs (E := E) La w₀,
          n • x - a • v₀ - b • w₀ ∈ hypComplement h v₀ w₀) →
        IsDIntegral h' D' (La.comap (hypComplement h v₀ w₀).subtype.toAddMonoidHom)

end Complement

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StLineNormalForm
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

section NormalForm

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def LineNormalForm.Statement (h : HermitianForm F E W) : Prop :=
  ∀ D : ℕ, ∃ KK : Set (AddSubgroup E × AddSubgroup E), KK.Finite ∧ ∃ n : ℕ, 0 < n ∧
    ∀ (La : AddSubgroup W) (l : Submodule E W), IsDIntegral h D La → IsIsotropicLine h l →
      ∃ v w : W, v ∈ l ∧ IsHyperbolicPair h v w ∧
        (lineCoeffs (E := E) La v, lineCoeffs (E := E) La w) ∈ KK ∧
        ∀ x ∈ La, (n : E) * h.toSesq w x ∈ lineCoeffs (E := E) La v ∧
          (n : E) * h.toSesq v x ∈ lineCoeffs (E := E) La w

end NormalForm

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsAdaptedReduction
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

section Reduction

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def AdaptedReduction.Statement [FiniteDimensional E W] (h : HermitianForm F E W) : Prop :=
  ∀ v₀ w₀ : W, IsHyperbolicPair h v₀ w₀ → ∀ h' : HermitianForm F E (hypComplement h v₀ w₀),
    (∀ x y, h'.toSesq x y = h.toSesq x y) → ∀ D : ℕ,
    ∃ KK : Set (AddSubgroup E × AddSubgroup E), KK.Finite ∧ ∃ n D' : ℕ, 0 < n ∧
      ∀ (La : AddSubgroup W) (l : Submodule E W), IsDIntegral h D La → IsIsotropicLine h l →
        ∃ (g : h.unitaryGroup) (La₁ : AddSubgroup W), g • La₁ = La ∧ g • v₀ ∈ l ∧
          (lineCoeffs (E := E) La₁ v₀, lineCoeffs (E := E) La₁ w₀) ∈ KK ∧
          (∀ x ∈ La₁, ∃ a ∈ lineCoeffs (E := E) La₁ v₀, ∃ b ∈ lineCoeffs (E := E) La₁ w₀,
            n • x - a • v₀ - b • w₀ ∈ hypComplement h v₀ w₀) ∧
          IsDIntegral h' D' (La₁.comap (hypComplement h v₀ w₀).subtype.toAddMonoidHom)

end Reduction

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsArchUnimodular
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def ArchUnimodular.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (μ : Measure (archUnitary h v)) [μ.IsHaarMeasure], μ.IsMulRightInvariant

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsComplementExtension
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

section Extension

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def ComplementExtension.Statement (h : HermitianForm F E W) : Prop :=
  ∀ v w : W, IsHyperbolicPair h v w → ∀ h' : HermitianForm F E (hypComplement h v w),
    (∀ x y, h'.toSesq x y = h.toSesq x y) → ∀ m : h'.unitaryGroup,
    ∃ g : h.unitaryGroup, g • v = v ∧ g • w = w ∧
      ∀ x : hypComplement h v w, g • (x : W) = ((m • x : hypComplement h v w) : W)

end Extension

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

