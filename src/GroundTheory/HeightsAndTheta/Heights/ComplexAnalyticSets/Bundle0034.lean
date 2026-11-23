module

public import Mathlib
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularUFDLocalization
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0028

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.AuslanderBuchsbaumDepthBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing CategoryTheory RingTheory.Sequence Ideal
open scoped Pointwise

universe u

variable {R : Type u} [CommRing R]

theorem exists_ne_zero_mul_eq_zero_of_forall_not_isSMulRegular [IsLocalRing R] [IsNoetherianRing R]
    (h : ∀ y ∈ maximalIdeal R, ¬ IsSMulRegular R y) :
    ∃ s : R, s ≠ 0 ∧ ∀ a ∈ maximalIdeal R, a * s = 0 := by
  have hmk : ∀ y : R, y • (1 : R ⧸ maximalIdeal R) = Ideal.Quotient.mk (maximalIdeal R) y := fun y ↦ by
    rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
  have hns : ¬ Subsingleton ((R ⧸ maximalIdeal R) →ₗ[R] R) := by
    rw [IsSMulRegular.subsingleton_linearMap_iff]
    rintro ⟨r, hr, hreg⟩
    refine h r ?_ hreg
    have h1 := Module.mem_annihilator.mp hr (1 : R ⧸ maximalIdeal R)
    rwa [hmk, Ideal.Quotient.eq_zero_iff_mem] at h1
  rw [not_subsingleton_iff_nontrivial] at hns
  obtain ⟨f, hf⟩ := exists_ne (0 : (R ⧸ maximalIdeal R) →ₗ[R] R)
  refine ⟨f 1, fun h0 ↦ hf (LinearMap.ext fun y ↦ ?_), fun a ha ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← hmk, map_smul, h0, smul_zero, LinearMap.zero_apply]
  · rw [← smul_eq_mul, ← map_smul, hmk, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

theorem hasProjectiveDimensionLE_zero_of_forall_not_isSMulRegular [IsLocalRing R] [IsNoetherianRing R]
    (h : ∀ y ∈ maximalIdeal R, ¬ IsSMulRegular R y) (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (k : ℕ) (hM : HasProjectiveDimensionLT (ModuleCat.of R M) (k + 1)) :
    HasProjectiveDimensionLE (ModuleCat.of R M) 0 := by
  obtain ⟨s, hs, hms⟩ := exists_ne_zero_mul_eq_zero_of_forall_not_isSMulRegular h
  have : Module.Free R M := GroundTheory.Arith.SchemeCoh.free_of_hasProjectiveDimensionLT_of_mul_eq_zero hs hms k M hM
  exact (projective_iff_hasProjectiveDimensionLE_zero _).mp (by
    rw [← IsProjective.iff_projective]; infer_instance)

theorem hasProjectiveDimensionLT_of_quotSMulTop [IsLocalRing R] [IsNoetherianRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hxR : IsSMulRegular R x) (k : ℕ) (M : Type u) [AddCommGroup M]
    [Module R M] [Module.Finite R M] (hxM : IsSMulRegular M x)
    (hM : HasProjectiveDimensionLT (ModuleCat.of (R ⧸ span {x}) (QuotSMulTop x M)) (k + 1)) :
    HasProjectiveDimensionLT (ModuleCat.of R M) (k + 1) := by
  have hne : span {x} ≠ ⊤ := fun h ↦ (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hx))
  have : Nontrivial (R ⧸ span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing (R ⧸ span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
  induction k generalizing M with
  | zero =>
    rw [zero_add, ← projective_iff_hasProjectiveDimensionLT_one, ← IsProjective.iff_projective]
      at hM ⊢
    have : Module.Finite (R ⧸ span {x}) (QuotSMulTop x M) :=
      Module.Finite.of_restrictScalars_finite R _ _
    have hfree : Module.Free (R ⧸ span {x}) (QuotSMulTop x M) := Module.free_of_flat_of_isLocalRing
    have := Module.finitePresentation_of_finite R M
    have : Module.Free R M :=
      (Module.free_quotSMulTop_iff_free R M (IsLocalRing.ringJacobson_eq_maximalIdeal R ▸ hx) hxM).mp hfree
    infer_instance
  | succ k ih =>
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
    let K := LinearMap.ker π
    have hS := LinearMap.shortExact_shortComplexKer hπ
    have hproj : Projective (π.shortComplexKer).X₂ := by
      rw [← IsProjective.iff_projective]; infer_instance
    have hxF : IsSMulRegular (Fin n → R) x := by
      intro a b h
      funext i
      exact hxR (congrFun h i)
    have hxK : IsSMulRegular K x := fun a b h ↦ Subtype.ext (hxF (congrArg Subtype.val h))
    let f₁ : QuotSMulTop x K →ₗ[R] QuotSMulTop x (Fin n → R) := QuotSMulTop.map x K.subtype
    let f₂ : QuotSMulTop x (Fin n → R) →ₗ[R] QuotSMulTop x M := QuotSMulTop.map x π
    have hex0 : Function.Exact K.subtype π := fun y ↦
      ⟨fun h ↦ ⟨⟨y, h⟩, rfl⟩, by rintro ⟨k, rfl⟩; exact k.2⟩
    have ex : Function.Exact f₁ f₂ := QuotSMulTop.map_exact x hex0 hπ
    have surj : Function.Surjective f₂ := QuotSMulTop.map_surjective x hπ
    have inj : Function.Injective f₁ := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro y hy
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
      rw [LinearMap.mem_ker] at hy
      simp only [f₁, Submodule.mkQ_apply, QuotSMulTop.map_apply_mk, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_smul_pointwise_iff_exists] at hy
      obtain ⟨b, -, hb⟩ := hy
      have hπb : π b = 0 := by
        apply hxM
        show x • π b = x • 0
        rw [← map_smul, hb, smul_zero]
        exact y.2
      rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨⟨b, hπb⟩, Submodule.mem_top, Subtype.ext hb⟩
    let g₁ := f₁.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := span {x}))
    let g₂ := f₂.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := span {x}))
    let T := ModuleCat.shortComplexOfCompEqZero g₁ g₂
      (LinearMap.ext fun y ↦ ex.apply_apply_eq_zero y)
    have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T ex inj surj
    have hproj2 : Projective T.X₂ := by
      rw [← IsProjective.iff_projective]; infer_instance
    have hK' : HasProjectiveDimensionLT (ModuleCat.of (R ⧸ span {x}) (QuotSMulTop x K)) (k + 1) :=
      (hT.hasProjectiveDimensionLT_X₃_iff k hproj2).mp hM
    exact (hS.hasProjectiveDimensionLT_X₃_iff k hproj).mpr (ih K hxK hK')

theorem length_le_of_isWeaklyRegular_quotient_span_singleton [IsLocalRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hxR : IsSMulRegular R x) [IsLocalRing (R ⧸ span {x})] (d : ℕ)
    (hd : ∀ rs : List R, (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs → rs.length ≤ d + 1)
    (rs : List (R ⧸ span {x})) (hrs : ∀ r ∈ rs, r ∈ maximalIdeal (R ⧸ span {x}))
    (hreg : IsWeaklyRegular (R ⧸ span {x}) rs) : rs.length ≤ d := by
  let lift : R ⧸ span {x} → R := Function.surjInv Ideal.Quotient.mk_surjective
  have hlift : ∀ b, Ideal.Quotient.mk (span {x}) (lift b) = b :=
    Function.surjInv_eq Ideal.Quotient.mk_surjective
  have hrs' : (rs.map lift).map (algebraMap R (R ⧸ span {x})) = rs := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id rs]
    exact List.map_congr_left fun b _ ↦ by simp [Ideal.Quotient.algebraMap_eq, hlift]
  have hloc : IsLocalHom (Ideal.Quotient.mk (span {x})) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hcomap : (maximalIdeal (R ⧸ span {x})).comap (Ideal.Quotient.mk (span {x})) =
      maximalIdeal R := IsLocalRing.maximalIdeal_comap _
  have hmem : ∀ r ∈ x :: rs.map lift, r ∈ maximalIdeal R := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hx
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr
      rw [← hcomap, Ideal.mem_comap, hlift]
      exact hrs b hb
  have e : (R ⧸ span {x}) ≃ₗ[R] QuotSMulTop x R :=
    Submodule.quotEquivOfEq _ _ (by
      rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top])
  have hreg' : IsWeaklyRegular R (x :: rs.map lift) := by
    rw [isWeaklyRegular_cons_iff]
    refine ⟨hxR, (e.isWeaklyRegular_congr _).mp ?_⟩
    rw [← isWeaklyRegular_map_algebraMap_iff (R ⧸ span {x}), hrs']
    exact hreg
  have := hd _ hmem hreg'
  simp only [List.length_cons, List.length_map] at this
  omega

theorem hasProjectiveDimensionLE_of_forall_isWeaklyRegular_length_le (d : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      (∀ rs : List R, (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs → rs.length ≤ d) →
      ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] (k : ℕ),
        HasProjectiveDimensionLT (ModuleCat.of R M) (k + 1) →
          HasProjectiveDimensionLE (ModuleCat.of R M) d := by
  induction d with
  | zero =>
    intro R _ _ _ hd M _ _ _ k hM
    refine hasProjectiveDimensionLE_zero_of_forall_not_isSMulRegular (fun y hy hy' ↦ ?_) M k hM
    have := hd [y] (by simpa using hy) ((isWeaklyRegular_singleton_iff R y).mpr hy')
    simp at this
  | succ d ih =>
    intro R _ _ _ hd M _ _ _ k hM
    by_cases hex : ∃ y ∈ maximalIdeal R, IsSMulRegular R y
    swap
    · push Not at hex
      have := hasProjectiveDimensionLE_zero_of_forall_not_isSMulRegular hex M k hM
      exact hasProjectiveDimensionLT_of_ge _ (0 + 1) (d + 1 + 1) (by omega)
    obtain ⟨x, hx, hxR⟩ := hex
    have hne : span {x} ≠ ⊤ := fun h ↦ (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hx))
    have : Nontrivial (R ⧸ span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing (R ⧸ span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
    have hd' := length_le_of_isWeaklyRegular_quotient_span_singleton hx hxR d hd
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
    let K := LinearMap.ker π
    have hS := LinearMap.shortExact_shortComplexKer hπ
    have hproj : Projective (π.shortComplexKer).X₂ := by
      rw [← IsProjective.iff_projective]; infer_instance
    have hK : HasProjectiveDimensionLT (ModuleCat.of R K) (k + 1) :=
      (hS.hasProjectiveDimensionLT_X₃_iff k hproj).mp
        (hasProjectiveDimensionLT_of_ge _ (k + 1) (k + 1 + 1) (by omega))
    have hxF : IsSMulRegular (Fin n → R) x := by
      intro a b h
      funext i
      exact hxR (congrFun h i)
    have hxK : IsSMulRegular K x := fun a b h ↦ Subtype.ext (hxF (congrArg Subtype.val h))
    have hKx := GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_quotSMulTop hxR k K hxK hK
    have : Module.Finite (R ⧸ span {x}) (QuotSMulTop x K) :=
      Module.Finite.of_restrictScalars_finite R _ _
    have hKx' := ih (R ⧸ span {x}) hd' (QuotSMulTop x K) k hKx
    have hK2 := hasProjectiveDimensionLT_of_quotSMulTop hx hxR d K hxK hKx'
    exact (hS.hasProjectiveDimensionLT_X₃_iff d hproj).mpr hK2

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.EqZeroOfMemZeroLocusLineOriginIdeal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Filter Topology Matrix
open scoped ContDiff ENNReal

noncomputable section

variable {n d e : ℕ}

def zeroLocus {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) : Set (Fin n → ℂ) :=
  {x | ∀ q ∈ J, eval x q = 0}

structure IsAffVariety (J : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) : Prop where
  isPrime : J.IsPrime
  dim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d



section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.HolomorphicZerosNotIsolated
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric

theorem analyticAt_det_fderiv {k : ℕ} {f : (Fin k → ℂ) → Fin k → ℂ} {x : Fin k → ℂ}
    (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℂ (fun z => LinearMap.det (fderiv ℂ f z : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)) x := by
  have hd : AnalyticAt ℂ (fderiv ℂ f) x := hf.fderiv
  have he : ∀ i j : Fin k, AnalyticAt ℂ (fun z => fderiv ℂ f z (Pi.single j 1) i) x := by
    intro i j
    let L : ((Fin k → ℂ) →L[ℂ] Fin k → ℂ) →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i).comp
        (ContinuousLinearMap.apply ℂ (Fin k → ℂ) (Pi.single j 1))
    show AnalyticAt ℂ (L ∘ fderiv ℂ f) x
    exact (L.analyticAt _).comp hd
  have heq : (fun z => LinearMap.det (fderiv ℂ f z : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)) =
      fun z => ∑ σ : Equiv.Perm (Fin k),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, fderiv ℂ f z (Pi.single i 1) (σ i) := by
    funext z
    rw [← LinearMap.det_toMatrix', Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    rfl
  rw [heq]
  exact Finset.analyticAt_fun_sum _ fun σ _ =>
    analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => he (σ i) i)

theorem exists_zero_ne_near {k : ℕ} (hk : 2 ≤ k) {J : (Fin k → ℂ) → ℂ} {c : Fin k → ℂ}
    (hJ : AnalyticAt ℂ J c) (hc : J c = 0) {W : Set (Fin k → ℂ)} (hW : W ∈ 𝓝 c) :
    ∃ z ∈ W, z ≠ c ∧ J z = 0 := by
  have : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  by_cases h0 : ∀ᶠ y in 𝓝 c, J y = 0
  · have h1 : ∀ᶠ y in 𝓝[≠] c, y ∈ W ∧ J y = 0 := nhdsWithin_le_nhds (Filter.inter_mem hW h0)
    obtain ⟨y, ⟨hyW, hy0⟩, hyc⟩ := (h1.and self_mem_nhdsWithin).exists
    exact ⟨y, hyW, hyc, hy0⟩
  obtain ⟨v, hv⟩ := exists_line_eventually_ne_zero hJ h0
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨t, ht⟩ := hv.exists
    simp [hc] at ht

  obtain ⟨u, -, hu⟩ : ∃ u ∈ (⊤ : Submodule ℂ (Fin k → ℂ)), u ∉ ℂ ∙ v := by
    refine SetLike.exists_of_lt (lt_top_iff_ne_top.2 fun htop => ?_)
    have h1 := finrank_span_singleton (K := ℂ) hv0
    rw [htop, finrank_top, Module.finrank_fin_fun] at h1
    omega
  obtain ⟨R, hR, han⟩ := hJ.exists_ball_analyticOnNhd
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.1 hW
  set ρ := min R ε with hρ
  have hρ0 : 0 < ρ := lt_min hR hε
  obtain ⟨δ, hδ, hδv⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hv)
  set r := min (δ / 2) (ρ / (2 * (‖v‖ + 1))) with hr
  have hr0 : 0 < r := lt_min (by positivity) (by positivity)
  have hrδ : r < δ := (min_le_left _ _).trans_lt (by linarith)
  have hrv : r * ‖v‖ < ρ / 2 := by
    have h1 : r ≤ ρ / (2 * (‖v‖ + 1)) := min_le_right _ _
    have h2 : r * ‖v‖ ≤ ρ / (2 * (‖v‖ + 1)) * ‖v‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have h3 : ρ / (2 * (‖v‖ + 1)) * ‖v‖ < ρ / 2 := by
      rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [norm_nonneg v]
    linarith

  have hmem : ∀ s t : ℂ, ‖s • u‖ < ρ / 2 → ‖t‖ ≤ r → c + s • u + t • v ∈ ball c ρ := by
    intro s t hs ht
    rw [mem_ball, dist_eq_norm, add_assoc, add_sub_cancel_left]
    calc ‖s • u + t • v‖ ≤ ‖s • u‖ + ‖t‖ * ‖v‖ := (norm_add_le _ _).trans (le_of_eq (by rw [norm_smul t v]))
      _ < ρ / 2 + ρ / 2 := add_lt_add_of_lt_of_le hs (by nlinarith [norm_nonneg v])
      _ = ρ := by ring
  have hballR : ball c ρ ⊆ ball c R := ball_subset_ball (min_le_left _ _)

  have hK : IsCompact (sphere (0 : ℂ) r) := isCompact_sphere 0 r
  have hKne : (sphere (0 : ℂ) r).Nonempty := NormedSpace.sphere_nonempty.2 hr0.le
  have hcontJ : ∀ p ∈ ball c ρ, ContinuousAt J p := fun p hp => (han p (hballR hp)).continuousAt
  have hF0 : ∀ t ∈ sphere (0 : ℂ) r, J (c + t • v) ≠ 0 := by
    intro t ht
    have htn : ‖t‖ = r := by simpa using ht
    refine hδv (by simpa [dist_eq_norm, htn] using hrδ) (by rintro rfl; simp at htn; linarith)
  have hline : ∀ t : ℂ, ‖t‖ ≤ r → c + t • v ∈ ball c ρ := by
    intro t ht
    have h1 := hmem 0 t (by rw [zero_smul, norm_zero]; exact half_pos hρ0) ht
    rwa [zero_smul, add_zero] at h1
  have hcontK : ContinuousOn (fun t : ℂ => ‖J (c + t • v)‖) (sphere 0 r) := by
    intro t ht
    have hp := hline t (mem_sphere_zero_iff_norm.1 ht).le
    exact (ContinuousAt.comp (f := fun t : ℂ => c + t • v) (hcontJ _ hp) (by fun_prop)).norm.continuousWithinAt
  obtain ⟨t0, ht0K, ht0min⟩ := hK.exists_isMinOn hKne hcontK
  set m := ‖J (c + t0 • v)‖ with hm
  have hm0 : 0 < m := norm_pos_iff.2 (hF0 t0 ht0K)

  have hcirc : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ t ∈ sphere (0 : ℂ) r, m / 2 < ‖J (c + s • u + t • v)‖ := by
    refine hK.eventually_forall_of_forall_eventually fun t ht => ?_
    have htr : ‖t‖ ≤ r := (mem_sphere_zero_iff_norm.1 ht).le
    have hcont : ContinuousAt (fun p : ℂ × ℂ => J (c + p.1 • u + p.2 • v)) (0, t) := by
      refine ContinuousAt.comp (f := fun p : ℂ × ℂ => c + p.1 • u + p.2 • v) ?_ (by fun_prop)
      exact hcontJ _ (hmem 0 t (by simpa using half_pos hρ0) htr)
    have hle : ‖J (c + t0 • v)‖ ≤ ‖J (c + t • v)‖ := isMinOn_iff.1 ht0min t ht
    exact hcont.norm.eventually (lt_mem_nhds (by simp only [zero_smul, add_zero]; linarith))
  have hcen : ∀ᶠ s in 𝓝 (0 : ℂ), ‖J (c + s • u)‖ < m / 2 := by
    have hcont : ContinuousAt (fun s : ℂ => J (c + s • u)) 0 :=
      ContinuousAt.comp (f := fun s : ℂ => c + s • u) (by simpa using hcontJ c (mem_ball_self hρ0))
        (by fun_prop)
    have h1 : ‖J (c + (0 : ℂ) • u)‖ < m / 2 := by simpa [hc] using half_pos hm0
    exact hcont.norm.eventually (gt_mem_nhds h1)
  have hsmall : ∀ᶠ s in 𝓝 (0 : ℂ), ‖s • u‖ < ρ / 2 := by
    have hcont : ContinuousAt (fun s : ℂ => ‖s • u‖) 0 := by fun_prop
    exact hcont.eventually (gt_mem_nhds (by simpa using half_pos hρ0))
  obtain ⟨s, ⟨⟨hs1, hs2⟩, hs3⟩, hs0⟩ :=
    ((((hcirc.and hcen).and hsmall).filter_mono (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))).and
      (self_mem_nhdsWithin (s := {(0 : ℂ)}ᶜ))).exists

  obtain ⟨t, ht, htz⟩ : ∃ t ∈ closedBall (0 : ℂ) r, J (c + s • u + t • v) = 0 := by
    by_contra hne
    simp only [not_exists, not_and] at hne
    have hdiff : DifferentiableOn ℂ (fun t : ℂ => (J (c + s • u + t • v))⁻¹) (closedBall 0 r) := by
      intro t ht
      have htr : ‖t‖ ≤ r := by simpa using ht
      have hp := hmem s t hs3 htr
      have hJd : DifferentiableAt ℂ J (c + s • u + t • v) := (han _ (hballR hp)).differentiableAt
      have hcomp : DifferentiableAt ℂ (fun t : ℂ => J (c + s • u + t • v)) t :=
        hJd.comp t (by fun_prop : DifferentiableAt ℂ (fun t : ℂ => c + s • u + t • v) t)
      exact (hcomp.inv (hne t ht)).differentiableWithinAt
    have hdc : DiffContOnCl ℂ (fun t : ℂ => (J (c + s • u + t • v))⁻¹) (ball 0 r) :=
      hdiff.diffContOnCl_ball subset_rfl
    have hbd := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc (C := (m / 2)⁻¹)
      (fun t ht => by
        rw [frontier_ball 0 hr0.ne'] at ht
        rw [norm_inv]
        exact inv_anti₀ (half_pos hm0) (hs1 t ht).le)
      (subset_closure (mem_ball_self hr0))
    have hJs : J (c + s • u) ≠ 0 := by simpa using hne 0 (mem_closedBall_self hr0.le)
    simp only [zero_smul, add_zero, norm_inv] at hbd
    have := inv_lt_inv₀ (half_pos hm0) (norm_pos_iff.2 hJs) |>.2 hs2
    linarith
  refine ⟨c + s • u + t • v, hεW ?_, ?_, htz⟩
  · exact ball_subset_ball (min_le_right R ε) (hmem s t hs3 (by simpa using ht))
  · intro heq
    apply hu
    have h1 : s • u = -(t • v) := by
      have : s • u + t • v = 0 := by
        have := congrArg (· - c) heq
        simpa [add_assoc] using this
      exact eq_neg_of_add_eq_zero_left this
    have hs : s ≠ 0 := by simpa using hs0
    rw [Submodule.mem_span_singleton]
    refine ⟨-(s⁻¹ * t), ?_⟩
    calc -(s⁻¹ * t) • v = s⁻¹ • (-(t • v)) := by rw [smul_neg, smul_smul, neg_smul]
      _ = s⁻¹ • (s • u) := by rw [h1]
      _ = u := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.ImportsAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Matrix

theorem GenericProjectionFinite.equiv :
    GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.GenericProjectionFinite.Statement := by
  unfold GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.Statement
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.GenericProjectionFinite.Statement
  refine forall_congr' fun n => forall_congr' fun d => forall_congr' fun J =>
    imp_congr_right fun _ => imp_congr_right fun _ => ?_
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · constructor
    · rintro ⟨U, ⟨S, rfl⟩, ⟨A, hA⟩, hU⟩
      exact ⟨S, ⟨A, hA⟩, fun M hM => (Objects.isFiniteProjection_iff J M).mp (hU M hM)⟩
    · rintro ⟨S, ⟨A, hA⟩, hS⟩
      exact ⟨{M | ∃ f ∈ S, eval (fun p : Fin d × Fin n => M p.1 p.2) f ≠ 0}, ⟨S, rfl⟩, ⟨A, hA⟩,
        fun M hM => (Objects.isFiniteProjection_iff J M).mpr (hS M hM)⟩
  · simp only [Set.Nonempty, Set.mem_ofPred_eq, Objects.isFiniteProjection_iff]
  · simp only [Objects.orthoRows_eq, Objects.isFiniteProjection_iff]
  · constructor
    · intro h m F hF
      obtain ⟨U, hU, hk⟩ := h m fun k => ⟨(F k)ᴴ, by
        simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem (hF k)⟩
      refine ⟨Uᴴ, by simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem hU,
        fun k s => ?_⟩
      rw [← Objects.isFiniteProjection_iff]
      simpa [Matrix.conjTranspose_mul] using hk k s
    · intro h m F
      obtain ⟨U, hU, hk⟩ := h m (fun k => (F k : Matrix (Fin n) (Fin n) ℂ)ᴴ) fun k => by
        simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem (F k).2
      refine ⟨Uᴴ, by simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem hU,
        fun k s => ?_⟩
      rw [Objects.isFiniteProjection_iff]
      simpa [Matrix.conjTranspose_mul] using hk k s

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAreaGraph
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology

open scoped ENNReal NNReal

theorem AreaGraph.proof (h : AreaGraphBound.Statement) : AreaGraph.Statement := by
  intro k m U F hU hF A hAU hA

  change μH[(k : ℝ)] (realGraphPt F '' A) =
    ∫⁻ x in A, ENNReal.ofReal (graphJac (fderiv ℝ F x :
      EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) ∂(μH[(k : ℝ)])
  set S := μH[(k : ℝ)] (realGraphPt F '' A)
  set I := ∫⁻ x in A, ENNReal.ofReal (graphJac (fderiv ℝ F x :
      EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) ∂(μH[(k : ℝ)])

  have hplus : ∀ j : ℕ,
      Tendsto (fun δ : ℝ≥0 => ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ j) (𝓝[>] 0) (𝓝 1) := by
    intro j
    have hcont : Continuous (fun δ : ℝ≥0 => ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ j) :=
      (ENNReal.continuous_pow j).comp (ENNReal.continuous_coe.comp (continuous_const.add continuous_id))
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hminus : ∀ j : ℕ,
      Tendsto (fun δ : ℝ≥0 => ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ j) (𝓝[>] 0) (𝓝 1) := by
    intro j
    have hcont : Continuous (fun δ : ℝ≥0 => ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ j) :=
      (ENNReal.continuous_pow j).comp (ENNReal.continuous_coe.comp (continuous_const.sub continuous_id))
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds

  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0), 0 < δ ∧ δ < 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ≥0) < 1 from one_pos)] with δ hδ
    exact hδ
  have hb : ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0),
      S ≤ ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ (k + 1) * I ∧
        ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k * I ≤ ((1 + δ : ℝ≥0) : ℝ≥0∞) * S := by
    filter_upwards [hev] with δ hδ
    exact h k m U F hU hF A hAU hA δ hδ.1 hδ.2
  apply le_antisymm
  · have hlim := ENNReal.Tendsto.mul_const (hplus (k + 1)) (b := I) (Or.inl one_ne_zero)
    rw [one_mul] at hlim
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim (hb.mono fun δ hδ => hδ.1)
  · have hlim₁ := ENNReal.Tendsto.mul_const (hminus k) (b := I) (Or.inl one_ne_zero)
    have hlim₂ := ENNReal.Tendsto.mul_const (by simpa using hplus 1) (b := S) (Or.inl one_ne_zero)
    rw [one_mul] at hlim₁ hlim₂
    exact le_of_tendsto_of_tendsto hlim₁ hlim₂ (hb.mono fun δ hδ => hδ.2)

end GroundTheory.Heights₂.Heights
end

