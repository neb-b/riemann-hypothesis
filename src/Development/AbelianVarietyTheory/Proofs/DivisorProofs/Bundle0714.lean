module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0708
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0704
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0648

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspidalLieActionOfIsCuspForm
section
noncomputable section
open NumberField Topology MeasureTheory Filter Metric
open scoped Pointwise

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem countable_ratN (r : ℕ) : Countable (ratN E a r) := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  refine Function.Surjective.countable (f := fun q : BlockIx a r → E =>
    (⟨fun p => algebraMap E (Ad E) (q p), q, rfl⟩ : ratN E a r)) ?_
  rintro ⟨x, q, rfl⟩
  exact ⟨q, rfl⟩

theorem covol_lt_top {r : ℕ} [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
    (μ : Measure (BlockIx a r → Ad E)) [μ.IsAddHaarMeasure] (𝓕 : Set (BlockIx a r → Ad E))
    (h : IsAddFundamentalDomain (ratN E a r) 𝓕 μ) : μ 𝓕 < ⊤ := by
  obtain ⟨K, hK, hcov⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  have := countable_ratN (E := E) (a := a) r
  let Cm : Set (BlockIx a r → Ad E) := Set.univ.pi fun _ => K
  have hCm : IsCompact Cm := isCompact_univ_pi fun _ => hK
  have hcovm : ∀ x : BlockIx a r → Ad E, ∃ γ : ratN E a r, x ∈ γ +ᵥ Cm := by
    intro x
    choose q hq using fun p => hcov (x p)
    refine ⟨⟨fun p => algebraMap E (Ad E) (q p), q, rfl⟩, fun p => x p - algebraMap E (Ad E) (q p),
      fun p _ => hq p, ?_⟩
    funext p
    show algebraMap E (Ad E) (q p) + (x p - algebraMap E (Ad E) (q p)) = x p
    abel
  have h1 : μ 𝓕 ≤ ∑' γ : ratN E a r, μ ((γ +ᵥ Cm) ∩ 𝓕) := by
    calc μ 𝓕 ≤ μ (⋃ γ : ratN E a r, ((γ +ᵥ Cm) ∩ 𝓕)) := by
          refine measure_mono fun x hx => ?_
          obtain ⟨γ, hγ⟩ := hcovm x
          exact Set.mem_iUnion.mpr ⟨γ, hγ, hx⟩
      _ ≤ ∑' γ : ratN E a r, μ ((γ +ᵥ Cm) ∩ 𝓕) := measure_iUnion_le _
  have : MeasurableConstVAdd (ratN E a r) (BlockIx a r → Ad E) :=
    ⟨fun γ => (continuous_const.add continuous_id :
      Continuous fun x : BlockIx a r → Ad E => (γ : BlockIx a r → Ad E) + x).measurable⟩
  have : VAddInvariantMeasure (ratN E a r) (BlockIx a r → Ad E) μ :=
    ⟨fun γ s _ => measure_preimage_add μ (γ : BlockIx a r → Ad E) s⟩
  rw [← h.measure_eq_tsum Cm] at h1
  exact h1.trans_lt hCm.measure_lt_top

theorem chart_unip_periodic {r : ℕ} {φ : Sm E a} (hφ : IsAutForm φ) (g : GA E a) (q : BlockIx a r → E)
    (x : BlockIx a r → Ad E) :
    chart φ.1 (unip ((fun p => algebraMap E (Ad E) (q p)) + x) * g) = chart φ.1 (unip x * g) := by
  rw [unip_add, unip_algebraMap, mul_assoc]
  funext y
  unfold chart
  split_ifs
  · rw [mul_assoc, hφ.left]
  · rfl

theorem chart_cont_bound {r : ℕ} {φ : Sm E a} (hφ : IsAutForm φ) (g : GA E a) (X : Lie E a) :
    (∀ y ∈ invSet E a, Continuous fun x : BlockIx a r → Ad E => chart φ.1 (unip x * g) y) ∧
    (∀ y ∈ invSet E a, Continuous fun x : BlockIx a r → Ad E => fderiv ℝ (chart φ.1 (unip x * g)) y X) ∧
    ∀ S : Set (Lie E a), IsCompact S → S ⊆ invSet E a → ∃ C, ∀ x : BlockIx a r → Ad E, ∀ y ∈ S,
      ‖chart φ.1 (unip x * g) y‖ ≤ C ∧ ‖fderiv ℝ (chart φ.1 (unip x * g)) y X‖ ≤ C := by
  have h1 := (_root_.GlobalTheory.CuspRep.JointCont.chart_jointCont E a r φ hφ g X).1
  have h2 := (_root_.GlobalTheory.CuspRep.JointCont.chart_jointCont E a r φ hφ g X).2
  have hm : ∀ y ∈ invSet E a, ∀ x : BlockIx a r → Ad E,
      ((x, y) : (BlockIx a r → Ad E) × Lie E a) ∈ Set.univ ×ˢ invSet E a :=
    fun y hy x => Set.mem_prod.2 ⟨Set.mem_univ _, hy⟩
  refine ⟨fun y hy => ?_, fun y hy => ?_, fun S hS hSi => ?_⟩
  · have := h1.comp_continuous (continuous_id.prodMk continuous_const) (hm y hy)
    exact this
  · have := h2.comp_continuous (continuous_id.prodMk continuous_const) (hm y hy)
    exact this
  obtain ⟨K, hK, hcov⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  have hKc : IsCompact ((Set.univ.pi fun _ : BlockIx a r => K) ×ˢ S) := (isCompact_univ_pi fun _ => hK).prod hS
  have hsub : (Set.univ.pi fun _ : BlockIx a r => K) ×ˢ S ⊆ Set.univ ×ˢ invSet E a :=
    Set.prod_mono (Set.subset_univ _) hSi
  obtain ⟨C1, hC1⟩ := hKc.exists_bound_of_continuousOn (h1.mono hsub)
  obtain ⟨C2, hC2⟩ := hKc.exists_bound_of_continuousOn (h2.mono hsub)
  refine ⟨max C1 C2, fun x y hy => ?_⟩
  choose q hq using fun p => hcov (x p)
  have hx : x = (fun p => algebraMap E (Ad E) (q p)) + fun p => x p - algebraMap E (Ad E) (q p) := by
    funext p
    show x p = algebraMap E (Ad E) (q p) + (x p - algebraMap E (Ad E) (q p))
    exact (add_sub_cancel _ _).symm
  have hx' : ((fun p => x p - algebraMap E (Ad E) (q p)), y) ∈ (Set.univ.pi fun _ : BlockIx a r => K) ×ˢ S :=
    ⟨fun p _ => hq p, hy⟩
  rw [hx, chart_unip_periodic hφ]
  exact ⟨(hC1 _ hx').trans (le_max_left _ _), (hC2 _ hx').trans (le_max_right _ _)⟩

theorem isCuspidal_lie (X : Lie E a) (φ : Sm E a) (hφ : IsCuspForm φ) : IsCuspidal (lie E a X φ).1 := by
  intro r h0 h1 _ _ μ 𝓕 hμ hF g
  haveI := hμ
  obtain ⟨hc1, hc2, hb⟩ := chart_cont_bound (r := r) hφ.1 g X
  let ℓ : ℝ → Lie E a := fun t => oneL E a + t • X
  have hℓc : Continuous ℓ := continuous_const.add (continuous_id.smul continuous_const)
  have hT : IsOpen (ℓ ⁻¹' invSet E a) := isOpen_invSet.preimage hℓc
  have h0T : (0:ℝ) ∈ ℓ ⁻¹' invSet E a := by
    show oneL E a + (0:ℝ) • X ∈ invSet E a
    rw [zero_smul, add_zero]; exact isUnit_one
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hT 0 h0T
  have hε : 0 < δ / 2 := by positivity
  have hS : IsCompact (ℓ '' closedBall 0 (δ / 2)) := (isCompact_closedBall 0 (δ / 2)).image hℓc
  have hSinv : ℓ '' closedBall 0 (δ / 2) ⊆ invSet E a := by
    rintro _ ⟨t, ht, rfl⟩; exact hball (closedBall_subset_ball (by linarith) ht)
  obtain ⟨C, hC⟩ := hb _ hS hSinv
  have hfin := covol_lt_top μ 𝓕 hF
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have hballT : ∀ t ∈ ball (0:ℝ) (δ / 2), ℓ t ∈ invSet E a := fun t ht => hball (ball_subset_ball (by linarith) ht)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕)
    (F := fun t x => chart φ.1 (unip x * g) (ℓ t))
    (F' := fun t x => fderiv ℝ (chart φ.1 (unip x * g)) (ℓ t) X) (x₀ := 0)
    (bound := fun _ => C) (s := ball 0 (δ / 2)) (ball_mem_nhds 0 hε) ?meas ?int ?meas' ?bd (integrable_const C) ?diff
  case meas =>
    filter_upwards [ball_mem_nhds (0:ℝ) hε] with t ht
    exact (hc1 _ (hballT t ht)).aestronglyMeasurable
  case int =>
    refine Integrable.of_bound (hc1 _ (hballT 0 (mem_ball_self hε))).aestronglyMeasurable C ?_
    exact Filter.Eventually.of_forall fun x => (hC x _ ⟨0, mem_closedBall_self hε.le, rfl⟩).1
  case meas' => exact (hc2 _ (hballT 0 (mem_ball_self hε))).aestronglyMeasurable
  case bd =>
    exact Filter.Eventually.of_forall fun x t ht => (hC x _ ⟨t, ball_subset_closedBall ht, rfl⟩).2
  case diff =>
    refine Filter.Eventually.of_forall fun x t ht => ?_
    have hd := ((contDiffAt_chart φ.2 (unip x * g) (hballT t ht)).differentiableAt (by simp)).hasFDerivAt
    have hl : HasDerivAt ℓ X t := by
      have := ((hasDerivAt_id t).smul_const X).const_add (oneL E a)
      rw [one_smul] at this
      exact this
    exact hd.comp_hasDerivAt t hl
  have heq : (fun t => ∫ x in 𝓕, chart φ.1 (unip x * g) (ℓ t) ∂μ) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [ball_mem_nhds (0:ℝ) hε] with t ht
    have hu : IsUnit (Matrix.of (ℓ t)) := hballT t ht
    have e : ∀ x : BlockIx a r → Ad E, chart φ.1 (unip x * g) (ℓ t) = φ.1 (unip x * (g * infGL E a hu.unit)) := fun x => by
      rw [chart, dite_eq_left hu, mul_assoc]
    simp only [e]
    exact hφ.2 r h0 h1 μ 𝓕 hμ hF _
  have h2 := key.2.unique ((hasDerivAt_const (0:ℝ) (0:ℂ)).congr_of_eventuallyEq heq)
  have e0 : ℓ 0 = oneL E a := by simp [ℓ]
  simp only [e0] at h2
  exact h2

theorem isCuspidal_lie_of_isCuspForm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (X : Lie E a) (φ : Sm E a), IsCuspForm φ → IsCuspidal (lie E a X φ).1 :=
  fun _ _ _ _ _ X φ h => isCuspidal_lie X φ h

end GlobalTheory.CuspRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitMpTenExtIff
section
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh
open scoped TensorProduct

namespace GlobalTheory.Obs.TenExt

variable {R : Type} [CommRing R] (N : Type) [AddCommGroup N] [Module R N]

theorem rTensor_smul {B B' : Type} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B'] (f : B →ₐ[R] B')
    (a : B) (m : B ⊗[R] N) :
    LinearMap.rTensor N f.toLinearMap (a • m) = f a • LinearMap.rTensor N f.toLinearMap m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

variable {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def tenMap {T T' : C} (φ : T ⟶ T') :
    TrivSqZeroExt (F.obj T) (F.obj T ⊗[R] N) →ₐ[R] TrivSqZeroExt (F.obj T') (F.obj T' ⊗[R] N) where
  toFun c := TrivSqZeroExt.inl (mp F φ c.fst) + TrivSqZeroExt.inr (LinearMap.rTensor N (mp F φ).toLinearMap c.snd)
  map_one' := by ext <;> simp
  map_mul' c d := by
    ext
    · simp
    · simp [rTensor_smul]
  map_zero' := by ext <;> simp
  map_add' c d := by ext <;> simp
  commutes' r := by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

@[simp] theorem fst_tenMap {T T' : C} (φ : T ⟶ T') (c : TrivSqZeroExt (F.obj T) (F.obj T ⊗[R] N)) :
    (tenMap N F φ c).fst = mp F φ c.fst := by simp [tenMap]

@[simp] theorem snd_tenMap {T T' : C} (φ : T ⟶ T') (c : TrivSqZeroExt (F.obj T) (F.obj T ⊗[R] N)) :
    (tenMap N F φ c).snd = LinearMap.rTensor N (mp F φ).toLinearMap c.snd := by simp [tenMap]

def tenExt : C ⥤ CommAlgCat.{0} R where
  obj T := CommAlgCat.of R (TrivSqZeroExt (F.obj T) (F.obj T ⊗[R] N))
  map φ := CommAlgCat.ofHom (tenMap N F φ)
  map_id T := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ TrivSqZeroExt.ext ((fst_tenMap N F _ c).trans (mp_id F T _)) (by
    refine (snd_tenMap N F _ c).trans ?_
    rw [show (mp F (𝟙 T)).toLinearMap = LinearMap.id from LinearMap.ext fun x ↦ mp_id F T x]
    simp))
  map_comp φ ψ := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ TrivSqZeroExt.ext (by
    change (tenMap N F (φ ≫ ψ) c).fst = (tenMap N F ψ (tenMap N F φ c)).fst
    simp only [fst_tenMap]; exact mp_comp F φ ψ _) (by
    change (tenMap N F (φ ≫ ψ) c).snd = (tenMap N F ψ (tenMap N F φ c)).snd
    simp only [snd_tenMap]
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    congr 2
    exact LinearMap.ext fun x ↦ mp_comp F φ ψ x))

theorem isUnit_mp_tenExt_iff {T S : C} (u : T ⟶ S) (c : (tenExt N F).obj T) :
    IsUnit (mp (tenExt N F) u c) ↔ IsUnit (mp F u c.fst) :=
  TrivSqZeroExt.isUnit_iff_isUnit_fst.trans (iff_of_eq (congrArg IsUnit (fst_tenMap N F u c)))

theorem span_inl_eq_top {S : C} {n : ℕ} {b : Fin n → F.obj S} (hb : Ideal.span (Set.range b) = ⊤) :
    Ideal.span (Set.range fun i ↦ (TrivSqZeroExt.inl (b i) : (tenExt N F).obj S)) = ⊤ := by
  have := congrArg (Ideal.map (TrivSqZeroExt.inlHom (F.obj S) (F.obj S ⊗[R] N))) hb
  rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  exact this

end GlobalTheory.Obs.TenExt

namespace GlobalTheory.Obs.TenExt

variable {R : Type} [CommRing R] (N : Type) [AddCommGroup N] [Module R N]
variable {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem surj_key {T T' : C} (l : T ⟶ T') (c : TrivSqZeroExt (F.obj T) (F.obj T ⊗[R] N))
    (y : TrivSqZeroExt (F.obj T') (F.obj T' ⊗[R] N)) (a₀ : F.obj T)
    (η₀ : F.obj T ⊗[R] N) (k₁ k₂ : ℕ) (ha : y.fst * mp F l (c.fst ^ k₁) = mp F l a₀)
    (hη : mp F l (c.fst ^ k₂) • y.snd = LinearMap.rTensor N (mp F l).toLinearMap η₀) :
    y * tenMap N F l c ^ (k₁ + k₂ + 1) = tenMap N F l (TrivSqZeroExt.inl (a₀ * c.fst ^ (k₂ + 1)) +
      TrivSqZeroExt.inr ((k₁ + k₂ + 1) • (a₀ * c.fst ^ k₂) • c.snd + c.fst ^ (k₁ + 1) • η₀)) := by
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, fst_tenMap, fst_tenMap]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, map_mul,
      map_pow] at ha ⊢
    linear_combination (mp F l c.fst) ^ (k₂ + 1) * ha
  · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _),
      TrivSqZeroExt.fst_pow, snd_tenMap, fst_tenMap, snd_tenMap]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, map_add, map_nsmul,
      rTensor_smul, map_mul, map_pow, op_smul_eq_smul, Nat.pred_succ] at ha hη ⊢
    rw [← hη, ← ha]
    module

theorem ker_key {T : C} (c x : TrivSqZeroExt (F.obj T) (F.obj T ⊗[R] N)) (m₁ m₂ : ℕ)
    (h₁ : c.fst ^ m₁ * x.fst = 0) (h₂ : c.fst ^ m₂ • x.snd = 0) : c ^ (m₁ + m₂ + 1) * x = 0 := by
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, TrivSqZeroExt.fst_zero]
    linear_combination c.fst ^ (m₂ + 1) * h₁
  · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _),
      TrivSqZeroExt.fst_pow, TrivSqZeroExt.snd_zero, op_smul_eq_smul, Nat.pred_succ]
    linear_combination (norm := module) c.fst ^ (m₁ + 1) • h₂ + h₁ • ((m₁ + m₂ + 1) • c.fst ^ m₂ • c.snd)

theorem hasLoc_tenExt (H : Desc.HasLoc F) : Desc.HasLoc (tenExt N F) := by
  intro T c
  obtain ⟨T', l, h1, h2, h3, h4⟩ := H T c.fst
  letI : Algebra (F.obj T) (F.obj T') := (mp F l : F.obj T →+* F.obj T').toAlgebra
  haveI : IsScalarTower R (F.obj T) (F.obj T') :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((mp F l).commutes r).symm
  haveI := GlobalTheory.CechDR.FormExt.isLocalization_of_data F l c.fst h1 h2 h3
  have hp : ∀ m, LinearMap.rTensor N (mp F l).toLinearMap m =
      TensorProduct.AlgebraTensorModule.rTensor R N (Algebra.linearMap (F.obj T) (F.obj T')) m := by
    intro m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hs : ∀ (a : F.obj T) (η : F.obj T' ⊗[R] N), a • η = mp F l a • η := fun a η ↦
    (algebraMap_smul (F.obj T') a η).symm
  refine ⟨T', l, (isUnit_mp_tenExt_iff N F l c).2 h1, fun y ↦ ?_, fun x hx ↦ ?_,
    fun S u hu ↦ h4 S u ((isUnit_mp_tenExt_iff N F u c).1 hu)⟩
  · obtain ⟨⟨a₀, _, k₁, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers c.fst) y.fst
    obtain ⟨⟨η₀, _, k₂, rfl⟩, hη⟩ := IsLocalizedModule.surj (Submonoid.powers c.fst)
      (TensorProduct.AlgebraTensorModule.rTensor R N (Algebra.linearMap (F.obj T) (F.obj T'))) y.snd
    change y.fst * mp F l (c.fst ^ k₁) = mp F l a₀ at ha
    change (c.fst ^ k₂) • y.snd = _ at hη
    rw [hs, ← hp] at hη
    exact ⟨k₁ + k₂ + 1, _, surj_key N F l c y a₀ η₀ k₁ k₂ ha hη⟩
  · have e1 : mp F l x.fst = 0 :=
      (fst_tenMap N F l x).symm.trans (congrArg TrivSqZeroExt.fst hx)
    have e2 : TensorProduct.AlgebraTensorModule.rTensor R N (Algebra.linearMap (F.obj T) (F.obj T')) x.snd = 0 :=
      (hp _).symm.trans ((snd_tenMap N F l x).symm.trans (congrArg TrivSqZeroExt.snd hx))
    obtain ⟨m₁, h₁⟩ := h3 _ e1
    obtain ⟨⟨_, m₂, rfl⟩, h₂⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers c.fst)
      (f := TensorProduct.AlgebraTensorModule.rTensor R N (Algebra.linearMap (F.obj T) (F.obj T'))) (x₁ := x.snd) (x₂ := 0)
      (by rw [e2, map_zero])
    rw [smul_zero, Submonoid.smul_def] at h₂
    exact ⟨m₁ + m₂ + 1, ker_key N F c x m₁ m₂ h₁ h₂⟩

end GlobalTheory.Obs.TenExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfIsotropicSignature
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible NumberField IsDedekindDomain MeasureTheory Filter Topology GlobalTheory.ThetaInner
open scoped InnerProductSpace
open Matrix

namespace GlobalTheory.WittSignature


open scoped ComplexOrder in
theorem le_of_isotropic_standard {p q k : ℕ} (N : Matrix (Fin p ⊕ Fin q) (Fin k) ℂ) (L : Matrix (Fin k) (Fin p ⊕ Fin q) ℂ)
    (hL : L * N = 1) (h : Nᴴ * Formalism.UG.Jpq p q * N = 0) : k ≤ p ∧ k ≤ q := by
  have key : ∀ v : Fin k → ℂ, star ((N *ᵥ v) ∘ Sum.inl) ⬝ᵥ ((N *ᵥ v) ∘ Sum.inl) =
      star ((N *ᵥ v) ∘ Sum.inr) ⬝ᵥ ((N *ᵥ v) ∘ Sum.inr) := by
    intro v
    have h1 : star (N *ᵥ v) ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ (N *ᵥ v)) = 0 := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]
      simp
    generalize N *ᵥ v = x at h1 ⊢
    rw [Formalism.UG.Jpq, Matrix.fromBlocks_mulVec] at h1
    simp only [dotProduct, Fintype.sum_sum_type, Matrix.one_mulVec, Matrix.zero_mulVec, Matrix.neg_mulVec, add_zero, zero_add,
      Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib] at h1
    simp only [dotProduct]
    exact add_neg_eq_zero.1 h1
  have inj : ∀ v : Fin k → ℂ, (N *ᵥ v) ∘ Sum.inl = 0 → (N *ᵥ v) ∘ Sum.inr = 0 → v = 0 := by
    intro v h1 h2
    have h3 : N *ᵥ v = 0 := by
      funext i
      rcases i with i | i
      · exact congrFun h1 i
      · exact congrFun h2 i
    have : (L * N) *ᵥ v = 0 := by rw [← Matrix.mulVec_mulVec, h3, Matrix.mulVec_zero]
    simpa [hL] using this
  constructor
  · have hf : Function.Injective ((LinearMap.funLeft ℂ ℂ (Sum.inl : Fin p → Fin p ⊕ Fin q)).comp N.mulVecLin) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro v hv
      have h1 : (N *ᵥ v) ∘ Sum.inl = 0 := hv
      have h2 := key v
      rw [h1, dotProduct_zero] at h2
      exact inj v h1 (dotProduct_star_self_eq_zero.1 h2.symm)
    simpa using LinearMap.finrank_le_finrank_of_injective hf
  · have hf : Function.Injective ((LinearMap.funLeft ℂ ℂ (Sum.inr : Fin q → Fin p ⊕ Fin q)).comp N.mulVecLin) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro v hv
      have h1 : (N *ᵥ v) ∘ Sum.inr = 0 := hv
      have h2 := key v
      rw [h1, dotProduct_zero] at h2
      exact inj v (dotProduct_star_self_eq_zero.1 h2) h1
    simpa using LinearMap.finrank_le_finrank_of_injective hf

theorem le_of_isotropic_signature {n p q k : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (hJ : Formalism.UG.HasSignature J p q)
    (M : Matrix (Fin n) (Fin k) ℂ) (L : Matrix (Fin k) (Fin n) ℂ)
    (hL : L * M = 1) (h : Mᴴ * J * M = 0) : k ≤ p ∧ k ≤ q := by
  obtain ⟨e, P, hP⟩ := hJ
  have hP' : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * J.submatrix e.symm e.symm *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Formalism.UG.Jpq p q := hP
  have hPP : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * (P⁻¹ : GL _ ℂ) = 1 := P.mul_inv
  have hN : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ).val * M.submatrix e.symm id) = M.submatrix e.symm id := by
    rw [← Matrix.mul_assoc, hPP, Matrix.one_mul]
  refine le_of_isotropic_standard ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ).val * M.submatrix e.symm id) (L.submatrix id e.symm * P.val) ?_ ?_
  · rw [Matrix.mul_assoc, hN, Matrix.submatrix_mul_equiv, hL, Matrix.submatrix_id_id]
  · rw [← hP']
    generalize ((P⁻¹ : GL _ ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * M.submatrix e.symm id = N at hN ⊢
    calc _ = ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * N)ᴴ * J.submatrix e.symm e.symm *
          ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * N) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by
          rw [hN, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h]
          rfl

theorem wittIdx_le_signature : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E), S.SigOK → ∀ τ : E →+* ℂ, (∀ a : E, τ (star a) = starRingEnd ℂ (τ a)) → wittIdx S ≤ (S.sig τ).1 ∧ wittIdx S ≤ (S.sig τ).2 := by
  intro E _ _ _ S hS τ hτ
  have main : ∀ W : Submodule E S.V, (∀ x ∈ W, ∀ y ∈ W, S.hT x y = 0) →
      Module.finrank E W ≤ (S.sig τ).1 ∧ Module.finrank E W ≤ (S.sig τ).2 := by
    intro W hW
    let b := Module.finBasis E W
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective W.subtype W.ker_subtype
    let M := LinearMap.toMatrix b S.frame W.subtype
    let L := LinearMap.toMatrix S.frame b g
    have hL : L * M = 1 := by
      rw [← LinearMap.toMatrix_comp, hg, LinearMap.toMatrix_id]
    have hb : ∀ i, (b i : S.V) = ∑ a, M a i • S.frame a := by
      intro i
      simp only [M, LinearMap.toMatrix_apply, Submodule.subtype_apply]
      exact (S.frame.sum_repr _).symm
    have h : Mᴴ * S.gram * M = 0 := by
      ext i j
      have h0 := hW _ (b i).2 _ (b j).2
      rw [hb i, hb j] at h0
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
        starRingEnd_apply] at h0
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, HSpace.gram, Matrix.zero_apply]
      rw [← h0]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    refine le_of_isotropic_signature _ (hS τ) (M.map τ) (L.map τ) ?_ ?_
    · rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero τ) (map_one τ)]
    · have : (M.map τ)ᴴ = (Mᴴ).map τ := by
        ext i j
        simp [Matrix.conjTranspose_apply, hτ]
      rw [this, ← Matrix.map_mul, ← Matrix.map_mul, h, Matrix.map_zero _ (map_zero τ)]
  constructor
  · refine csSup_le' ?_
    rintro k ⟨W, rfl, hW⟩
    exact (main W hW).1
  · refine csSup_le' ?_
    rintro k ⟨W, rfl, hW⟩
    exact (main W hW).2

end GlobalTheory.WittSignature
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodHomPushEnd
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem periodHom_push_end : PEnd := by
  intro A _ g hA L u P hP α _ M hM x x' hx
  have hsep : A.left.IsSeparated := by
    haveI : IsProper A.hom := hA.proper
    refine ⟨?_⟩
    rw [← terminal.comp_from A.hom]
    infer_instance
  have hΛ : ∀ l : u.Λ, M l ∈ u.Λ := fun l ↦ by
    rw [← u.ker, hM, (u.ker _).2 l.2, MonObj.one_comp]
  let N : u.Λ →+ u.Λ :=
    { toFun l := ⟨M l, hΛ l⟩
      map_zero' := Subtype.ext (map_zero M)
      map_add' a b := Subtype.ext (map_add M _ _) }
  obtain rfl : x' = N x := Subtype.ext hx
  refine LinearMap.ext fun c ↦ ?_
  have key := _root_.GlobalTheory.AnPer.isPeriod_pull1_eq_comap (fibUnif u) (fibUnif u) hsep hsep id analyticOnNhd_id (fun _ h ↦ h) M N
    (fun _ _ _ ↦ rfl) (RingHom.id ℂ) α.left (homMor (dp0 ℂ) (𝟙 _) α).isMor (fun _ ↦ rfl)
    (fun p _ ↦ (congrArg Over.Hom.left (hM p.2)).symm) c.1 _ _ (hP c)
    (hP (primPull (dp0 ℂ) (𝟙 _) α c)) x
  exact congrArg (fun f : Hol (fibFam u).V ↦ f.1 ⟨0, trivial⟩) key

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFderivBelowDiagonalStatement
section
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryChartSection_fderiv_below_diagonal : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ (z : V (nd X)) (τ : X.Ψ) (a b : Fin r), b < a → dY X z τ a b = nmat X z τ a b := by
  first | exact @GlobalTheory.SUChartSection.dY_lower | exact GlobalTheory.SUChartSection.dY_lower | (intros; apply GlobalTheory.SUChartSection.dY_lower <;> assumption)
end

