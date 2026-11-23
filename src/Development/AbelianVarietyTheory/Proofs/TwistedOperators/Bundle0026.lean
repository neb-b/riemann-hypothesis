module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleTensorProductOperatorStableCountable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuadBaseChangeIsFieldOrSplit
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Matrix

namespace GlobalTheory

theorem quadAlg_isField_or_split {K A : Type} [Field K] [CommRing A] [Algebra K A] [Nontrivial A]
    (h2 : (2 : K) ≠ 0) (τ : A →+* A) (hτ : ∀ k, τ (algebraMap K A k) = algebraMap K A k)
    (δ : A) (d : K) (hd : d ≠ 0) (hδ : δ * δ = algebraMap K A d) (hs : τ δ = -δ)
    (hsp : ∀ x : A, ∃ a b : K, x = algebraMap K A a + algebraMap K A b * δ) :
    IsField A ∨ ∃ φ : A ≃+* K × K, ∀ x, φ (τ x) = (φ x).swap := by
  by_cases hsq : ∃ s : K, d = s * s
  · right
    obtain ⟨s, rfl⟩ := hsq
    have hs0 : s ≠ 0 := fun h => hd (by simp [h])
    set e : A := algebraMap K A (2⁻¹) + algebraMap K A (2⁻¹ * s⁻¹) * δ with he
    have h1 : algebraMap K A (2⁻¹) * 2 = 1 := by
      rw [show (2 : A) = algebraMap K A 2 from (map_ofNat _ 2).symm, ← map_mul,
        inv_mul_cancel₀ h2, map_one]
    have h3 : algebraMap K A (s⁻¹) * algebraMap K A s = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hs0, map_one]
    rw [map_mul] at hδ he
    have hee : e * e = e := by
      rw [he]
      generalize algebraMap K A (2⁻¹) = p at *
      generalize algebraMap K A (s⁻¹) = q at *
      generalize algebraMap K A s = t at *
      linear_combination (p + p * q * δ) * h1 + p ^ 2 * q ^ 2 * hδ + p ^ 2 * (q * t + 1) * h3
    have hτe : τ e = 1 - e := by
      rw [he]
      simp only [map_add (f := _), map_mul, hτ, hs]
      linear_combination h1
    have hτe' : τ (1 - e) = e := by
      rw [map_sub, map_one, hτe]; ring
    have hδe : δ = algebraMap K A s * e + algebraMap K A (-s) * (1 - e) := by
      rw [he, map_neg]
      generalize algebraMap K A (2⁻¹) = p at *
      generalize algebraMap K A (s⁻¹) = q at *
      generalize algebraMap K A s = t at *
      linear_combination (-t - t * q * δ) * h1 - δ * h3
    have he0 : e ≠ 0 := by
      intro h
      rw [h] at hτe
      simp at hτe
    have he1 : 1 - e ≠ 0 := by
      intro h
      rw [h, map_zero] at hτe'
      exact he0 hτe'.symm
    let ψ : K × K →+* A :=
      { toFun := fun x => algebraMap K A x.1 * e + algebraMap K A x.2 * (1 - e)
        map_one' := by simp
        map_zero' := by simp
        map_add' := by intro x y; simp only [Prod.fst_add, Prod.snd_add, map_add (f := _)]; ring
        map_mul' := by
          intro x y
          simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
          generalize algebraMap K A x.1 = a
          generalize algebraMap K A x.2 = b
          generalize algebraMap K A y.1 = c
          generalize algebraMap K A y.2 = f
          linear_combination (-(a - b) * (c - f)) * hee }
    have hψ : ∀ x, ψ x = algebraMap K A x.1 * e + algebraMap K A x.2 * (1 - e) := fun _ => rfl
    have hinj : Function.Injective ψ := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro x hx
      rw [hψ] at hx
      have ha : algebraMap K A x.1 * e = 0 := by
        linear_combination e * hx - (algebraMap K A x.1 - algebraMap K A x.2) * hee
      have hb : algebraMap K A x.2 * (1 - e) = 0 := by
        linear_combination hx - ha
      rw [← Algebra.smul_def, smul_eq_zero] at ha hb
      exact Prod.ext (ha.resolve_right he0) (hb.resolve_right he1)
    have hsurj : Function.Surjective ψ := by
      intro x
      obtain ⟨a, b, rfl⟩ := hsp x
      refine ⟨(a + b * s, a - b * s), ?_⟩
      rw [hψ]
      simp only [map_add (f := _), map_sub, map_mul]
      rw [map_neg] at hδe
      linear_combination (-algebraMap K A b) * hδe
    refine ⟨(RingEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm, fun x => ?_⟩
    obtain ⟨y, rfl⟩ := (RingEquiv.ofBijective ψ ⟨hinj, hsurj⟩).surjective x
    rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_eq]
    change τ (ψ y) = ψ y.swap
    simp only [hψ, map_add (f := _), map_mul, hτ, hτe, hτe', Prod.fst_swap,
      Prod.snd_swap]
    ring
  · left
    refine ⟨exists_pair_ne A, mul_comm, fun {x} hx => ?_⟩
    obtain ⟨a, b, rfl⟩ := hsp x
    have hn : a * a - d * (b * b) ≠ 0 := by
      intro h
      by_cases hb : b = 0
      · subst hb
        have : a = 0 := by simpa using h
        subst this
        simp at hx
      · refine hsq ⟨a / b, ?_⟩
        field_simp
        linear_combination -h
    refine ⟨(algebraMap K A a - algebraMap K A b * δ) * algebraMap K A (a * a - d * (b * b))⁻¹, ?_⟩
    have h4 : algebraMap K A (a * a - d * (b * b)) * algebraMap K A (a * a - d * (b * b))⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hn, map_one]
    generalize algebraMap K A (a * a - d * (b * b))⁻¹ = u at *
    simp only [map_sub, map_mul] at h4
    linear_combination h4 - (algebraMap K A b) ^ 2 * u * hδ

theorem quadExt_exists_skew {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) (hr : Module.finrank F E = 2) (hσ : ∀ a, σ (σ a) = a) (hne : ∃ a, σ a ≠ a) :
    ∃ (δ : E) (d : F), d ≠ 0 ∧ δ * δ = algebraMap F E d ∧ σ δ = -δ ∧
      ∀ x : E, ∃ a b : F, x = algebraMap F E a + algebraMap F E b * δ := by
  obtain ⟨t, ht⟩ := hne
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  set δ := t - σ t with hδ
  have hδ0 : δ ≠ 0 := fun h => ht (sub_eq_zero.mp h).symm
  have hs : σ δ = -δ := by rw [hδ, map_sub, hσ]; ring
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro a b h
    have h' := congrArg σ h
    rw [map_add (f := _), Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, σ.commutes, σ.commutes, hs,
      map_one, map_zero, ← Algebra.smul_def, ← Algebra.smul_def, smul_neg] at h'
    have ha : (2 * a) • (1 : E) = 0 := by
      rw [two_mul, add_smul]; linear_combination h + h'
    have hb : (2 * b) • δ = 0 := by
      rw [two_mul, add_smul]; linear_combination h - h'
    rw [smul_eq_zero] at ha hb
    exact ⟨by simpa using ha, by simpa [hδ0] using hb⟩
  have hsp : ∀ x : E, ∃ a b : F, x = algebraMap F E a + algebraMap F E b * δ := by
    intro x
    let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hr])
    refine ⟨B.repr x 0, B.repr x 1, ?_⟩
    have h := B.sum_repr x
    rw [Fin.sum_univ_two] at h
    have h0 : B 0 = 1 := by simp [B]
    have h1 : B 1 = δ := by simp [B]
    rw [h0, h1, Algebra.smul_def, Algebra.smul_def, mul_one] at h
    exact h.symm
  obtain ⟨a, b, hab⟩ := hsp (δ * δ)
  have h' := congrArg σ hab
  simp only [map_add (f := _), map_mul, hs, AlgHom.commutes] at h'
  have hd : δ * δ = algebraMap F E a := by
    have h2 : (2 : E) ≠ 0 := two_ne_zero
    apply mul_left_cancel₀ h2
    linear_combination hab + h'
  refine ⟨δ, a, ?_, hd, hs, hsp⟩
  rintro rfl
  simp [hδ0] at hd

theorem quadBaseChange_isField_or_split :
    ∀ (F E K : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [Field K] [Algebra F K] (σ : E →ₐ[F] E), Module.finrank F E = 2 → (∀ a, σ (σ a) = a) → (∃ a, σ a ≠ a) → (IsField (K ⊗[F] E) ∨ ∃ φ : K ⊗[F] E ≃+* K × K, ∀ x, φ (sigR K σ x) = (φ x).swap) ∧ ∃ (δ : K ⊗[F] E) (d : K), d ≠ 0 ∧ δ * δ = algebraMap K (K ⊗[F] E) d ∧ sigR K σ δ = -δ ∧ ∀ x : K ⊗[F] E, ∃ a b : K, x = algebraMap K (K ⊗[F] E) a + algebraMap K (K ⊗[F] E) b * δ := by
  intro F E K _ _ _ _ _ _ σ hr hσ hne
  obtain ⟨δ, d, hd, hδ, hs, hsp⟩ := quadExt_exists_skew σ hr hσ hne
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have hd' : algebraMap F K d ≠ 0 := by simpa using hd
  have hδ' : ((1 : K) ⊗ₜ[F] δ) * ((1 : K) ⊗ₜ[F] δ) =
      algebraMap K (K ⊗[F] E) (algebraMap F K d) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, hδ, one_mul, ← IsScalarTower.algebraMap_apply,
      Algebra.TensorProduct.algebraMap_apply']
  have hsig : ∀ (k : K) (x : E), sigR K σ (k ⊗ₜ[F] x) = k ⊗ₜ[F] σ x := fun k x => by
    simp [sigR]
  have hs' : sigR K σ ((1 : K) ⊗ₜ[F] δ) = -((1 : K) ⊗ₜ[F] δ) := by
    rw [hsig, hs, TensorProduct.tmul_neg]
  have hsp' : ∀ x : K ⊗[F] E, ∃ a b : K, x = algebraMap K (K ⊗[F] E) a +
      algebraMap K (K ⊗[F] E) b * ((1 : K) ⊗ₜ[F] δ) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul k x =>
      obtain ⟨a, b, rfl⟩ := hsp x
      refine ⟨a • k, b • k, ?_⟩
      rw [← Algebra.smul_def, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_add,
        TensorProduct.tmul_smul, TensorProduct.tmul_smul]
      simp [Algebra.TensorProduct.algebraMap_apply, TensorProduct.smul_tmul']
    | add x y hx hy =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨c, e, rfl⟩ := hy
      exact ⟨a + c, b + e, by simp only [map_add (f := _)]; ring⟩
  refine ⟨quadAlg_isField_or_split two_ne_zero (sigR K σ) (fun k => ?_) _ _ hd' hδ' hs' hsp',
    _, _, hd', hδ', hs', hsp'⟩
  rw [Algebra.TensorProduct.algebraMap_apply, hsig, map_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RightConvEqSmulOfInnerTranslates
section
open MeasureTheory

namespace GlobalTheory

theorem rightConv_eq_smul_of_inner_translates : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤ → ∀ {H : Subgroup G} (m : Measure H) [SFinite m] (α : H → ℂ), Integrable α m → ∀ (φ : G → ℂ), Continuous φ → ∀ B : ℝ, (∀ g, ‖φ g‖ ≤ B) → (∀ γ ∈ Γ, ∀ x, φ (γ * x) = φ x) → ∀ c : ℂ, (∀ h' : H, ∫ x in 𝓕, star (φ (x * (h' : G))) * (∫ h, α h * φ (x * (h : G)) ∂m) ∂μ = c * ∫ x in 𝓕, star (φ (x * (h' : G))) * φ x ∂μ) → ∀ x, ∫ h, α h * φ (x * (h : G)) ∂m = c * φ x := by
  intro G _ _ _ _ _ _ Γ _ μ _ 𝓕 hF hμ H m _ α hα φ hφ B hB hinv c hc
  set Φ : G → ℂ := fun x => ∫ h, α h * φ (x * (h : G)) ∂m with hΦdef

  have intOn : ∀ f : G → ℂ, Continuous f → ∀ C : ℝ, (∀ g, ‖f g‖ ≤ C) → IntegrableOn f 𝓕 μ :=
    fun f hf C hC => Measure.integrableOn_of_bounded hμ.ne hf.aestronglyMeasurable (ae_of_all _ hC)
  have hΦc : Continuous Φ := GlobalTheory.T.continuous_right_convolution_bounded_integrable m α hα φ hφ B hB
  set K : ℝ := ∫ h, ‖α h‖ * B ∂m
  have hΦb : ∀ x, ‖Φ x‖ ≤ K := by
    intro x
    refine norm_integral_le_of_norm_le (hα.norm.mul_const B) (ae_of_all _ fun h => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
  set D : G → ℂ := fun x => Φ x - c * φ x with hDdef
  have hDc : Continuous D := hΦc.sub (continuous_const.mul hφ)
  have hDb : ∀ x, ‖D x‖ ≤ K + ‖c‖ * B := by
    intro x
    refine (norm_sub_le _ _).trans (add_le_add (hΦb x) ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
  have hsφc : Continuous (fun x => star (φ x)) := hφ.star
  have hsφb : ∀ x, ‖star (φ x)‖ ≤ B := fun x => by rw [norm_star]; exact hB x

  have h1 : ∀ h' : H, ∫ x in 𝓕, star (φ (x * (h' : G))) * D x ∂μ = 0 := by
    intro h'
    have hc1 : Continuous (fun x => star (φ (x * (h' : G)))) :=
      hsφc.comp (continuous_id.mul continuous_const)
    have hb1 : ∀ x, ‖star (φ (x * (h' : G)))‖ ≤ B := fun x => hsφb _
    have i1 : IntegrableOn (fun x => star (φ (x * (h' : G))) * Φ x) 𝓕 μ :=
      intOn _ (hc1.mul hΦc) (B * K) fun x => by
        rw [norm_mul]; exact mul_le_mul (hb1 x) (hΦb x) (norm_nonneg _) ((norm_nonneg _).trans (hB 1))
    have i2 : IntegrableOn (fun x => star (φ (x * (h' : G))) * (c * φ x)) 𝓕 μ :=
      intOn _ (hc1.mul (continuous_const.mul hφ)) (B * (‖c‖ * B)) fun x => by
        rw [norm_mul, norm_mul]
        exact mul_le_mul (hb1 x) (mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)) (by positivity) ((norm_nonneg _).trans (hB 1))
    have : (fun x => star (φ (x * (h' : G))) * D x) = fun x => star (φ (x * (h' : G))) * Φ x - star (φ (x * (h' : G))) * (c * φ x) := by
      funext x; simp only [hDdef]; ring
    rw [this, integral_sub i1 i2, hc h']
    have : (fun x => star (φ (x * (h' : G))) * (c * φ x)) = fun x => c * (star (φ (x * (h' : G))) * φ x) := by
      funext x; ring
    rw [this, integral_const_mul]
    simp [Φ]

  have hsα : Integrable (fun h => star (α h)) m := by
    simpa using Complex.conjCLE.toContinuousLinearMap.integrable_comp hα
  have F := GlobalTheory.T.integral_fundamentalDomain_convolution_comm_of_bounded (H := H) μ 𝓕 hμ m (fun h => star (α h)) hsα D (fun x => star (φ x)) hDc hsφc
    (K + ‖c‖ * B) B hDb hsφb
  have hstarΦ : ∀ x, star (Φ x) = ∫ h, star (α h) * star (φ (x * (h : G))) ∂m := by
    intro x
    simp only [Φ, ← starRingEnd_apply, ← integral_conj, map_mul]
  have h3 : ∫ x in 𝓕, D x * star (Φ x) ∂μ = 0 := by
    simp_rw [hstarΦ]
    rw [F.2.2]
    refine integral_eq_zero_of_ae (ae_of_all _ fun h => ?_)
    have := h1 h
    have e : (fun x => D x * star (φ (x * (h : G)))) = fun x => star (φ (x * (h : G))) * D x := by
      funext x; ring
    simp only [Pi.zero_apply, e, this, mul_zero]

  have h4 : ∫ x in 𝓕, D x * star (φ x) ∂μ = 0 := by
    have := h1 1
    simp only [OneMemClass.coe_one, mul_one] at this
    rw [← this]; congr 1; funext x; ring

  have iDΦ : IntegrableOn (fun x => D x * star (Φ x)) 𝓕 μ :=
    intOn _ (hDc.mul hΦc.star) ((K + ‖c‖ * B) * K) fun x => by
      rw [norm_mul, norm_star]
      exact mul_le_mul (hDb x) (hΦb x) (norm_nonneg _) ((norm_nonneg _).trans (hDb x))
  have iDφ : IntegrableOn (fun x => star c * (D x * star (φ x))) 𝓕 μ :=
    intOn _ (continuous_const.mul (hDc.mul hsφc)) (‖c‖ * ((K + ‖c‖ * B) * B)) fun x => by
      rw [norm_mul, norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hDb x) (hsφb x) (norm_nonneg _) ((norm_nonneg _).trans (hDb x))) (norm_nonneg _)
  have h5 : ∫ x in 𝓕, ((‖D x‖ ^ 2 : ℝ) : ℂ) ∂μ = 0 := by
    have e : (fun x => ((‖D x‖ ^ 2 : ℝ) : ℂ)) = fun x => D x * star (Φ x) - star c * (D x * star (φ x)) := by
      funext x
      rw [Complex.ofReal_pow, ← Complex.mul_conj', starRingEnd_apply]
      simp only [hDdef, star_sub, star_mul']
      ring
    rw [e, integral_sub iDΦ iDφ, integral_const_mul, h3, h4, mul_zero, sub_zero]
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at h5
  have indexDSecond : IntegrableOn (fun x => ‖D x‖ ^ 2) 𝓕 μ :=
    Measure.integrableOn_of_bounded hμ.ne (hDc.norm.pow 2).aestronglyMeasurable
      (M := (K + ‖c‖ * B) ^ 2) (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_pow, abs_norm]
        exact pow_le_pow_left₀ (norm_nonneg _) (hDb x) 2)
  have hae := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun x => by positivity) indexDSecond).1 h5
  have hae' : ∀ᵐ x ∂(μ.restrict 𝓕), D x = 0 := hae.mono fun x hx => by
    simpa using hx

  have hDinv : ∀ γ ∈ Γ, ∀ x, D (γ * x) = D x := by
    intro γ hγ x
    simp only [hDdef, Φ, mul_assoc, hinv γ hγ]
  have := GlobalTheory.T.eq_zero_of_ae_zero_on_fundamentalDomain Γ μ 𝓕 hF D hDc hDinv hae'
  intro x
  exact sub_eq_zero.1 (this x)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology

namespace GlobalTheory.RootEx


open MeasureTheory ValuativeRel Matrix in
open scoped Topology Pointwise in
theorem _root_.GlobalTheory.RootEx.exists_isOpen_addSubgroup_add_eq {X : Type*}
    [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] {Φ : X → ℂ} (hlc : IsLocallyConstant Φ) (hcs : IsCompact (tsupport Φ)) :
    ∃ Λ : AddSubgroup X, IsOpen (Λ : Set X) ∧ ∀ x, ∀ y ∈ Λ, Φ (x + y) = Φ x := by
  classical
  obtain ⟨t, ht⟩ := hcs.elim_finite_subcover (fun c : ℂ => {x | Φ x = c})
    (fun c => hlc.isOpen_fiber c) (fun x _ => Set.mem_iUnion.2 ⟨Φ x, rfl⟩)
  have hV : ∀ c : ℂ, ∃ V ∈ 𝓝 (0 : X), c ≠ 0 → {x | Φ x = c} + V ⊆ {x | Φ x = c} := by
    intro c
    by_cases hc : c = 0
    · exact ⟨Set.univ, Filter.univ_mem, fun h => (h hc).elim⟩
    · have hsub : {x | Φ x = c} ⊆ tsupport Φ := fun x hx =>
        subset_tsupport Φ (by
          rw [Function.mem_support]
          rw [Set.mem_setOf_eq] at hx
          rw [hx]
          exact hc)
      obtain ⟨V, hV0, hVs⟩ := compact_open_separated_add_right
        (hcs.of_isClosed_subset (hlc.isClosed_fiber c) hsub) (hlc.isOpen_fiber c) le_rfl
      exact ⟨V, hV0, fun _ => hVs⟩
  choose V hV0 hVsub using hV
  have hW : (⋂ c ∈ t, (V c ∩ -V c)) ∈ 𝓝 (0 : X) :=
    (Filter.biInter_finset_mem t).2 fun c _ =>
      Filter.inter_mem (hV0 c) (neg_mem_nhds_zero X (hV0 c))
  have hstep : ∀ x, ∀ v ∈ (⋂ c ∈ t, (V c ∩ -V c)), Φ (x + v) = Φ x := by
    intro x v hv
    have hv' : ∀ c ∈ t, v ∈ V c ∧ -v ∈ V c := by
      intro c hc
      have h := Set.mem_iInter₂.1 hv c hc
      exact ⟨h.1, Set.mem_neg.1 h.2⟩
    by_cases h0 : Φ x = 0
    · by_contra hne
      have hne' : Φ (x + v) ≠ 0 := by rwa [h0] at hne
      have hxK : x + v ∈ tsupport Φ := subset_tsupport Φ hne'
      obtain ⟨c, hct, hc⟩ := Set.mem_iUnion₂.1 (ht hxK)
      have hc' : Φ (x + v) = c := hc
      have hc0 : c ≠ 0 := hc' ▸ hne'
      have h := hVsub c hc0 (Set.add_mem_add hc (hv' c hct).2)
      have h' : Φ (x + v + -v) = c := h
      rw [add_neg_cancel_right] at h'
      exact hc0 (h'.symm.trans h0)
    · have hxK : x ∈ tsupport Φ := subset_tsupport Φ h0
      obtain ⟨c, hct, hc⟩ := Set.mem_iUnion₂.1 (ht hxK)
      have hc' : Φ x = c := hc
      have hc0 : c ≠ 0 := hc' ▸ h0
      have h := hVsub c hc0 (Set.add_mem_add hc (hv' c hct).1)
      have h' : Φ (x + v) = c := h
      exact h'.trans hc'.symm
  refine ⟨AddSubgroup.closure (⋂ c ∈ t, (V c ∩ -V c)),
    AddSubgroup.isOpen_of_mem_nhds _ (g := 0)
      (Filter.mem_of_superset hW AddSubgroup.subset_closure), ?_⟩
  intro x y hy
  induction hy using AddSubgroup.closure_induction generalizing x with
  | mem y hy => exact hstep x y hy
  | zero => simp
  | add y z _ _ hy hz => rw [← add_assoc, hz, hy]
  | neg y _ hy =>
    have h := hy (x + -y)
    rw [neg_add_cancel_right] at h
    exact h.symm


open MeasureTheory ValuativeRel Matrix in
open scoped Topology Pointwise in
theorem _root_.GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (a b : Type) [Fintype a] [Fintype b], ∀ Φ ∈ _root_.GlobalTheory.SplitWeil.SB (Matrix a b k),
      ∃ Λ : AddSubgroup (Matrix a b k), IsOpen (Λ : Set (Matrix a b k)) ∧
        ∀ x, ∀ y ∈ Λ, Φ (x + y) = Φ x := by
  intro k _ _ _ _ a b _ _ Φ hΦ
  obtain ⟨hlc, hcs⟩ := hΦ
  exact _root_.GlobalTheory.RootEx.exists_isOpen_addSubgroup_add_eq hlc hcs

end GlobalTheory.RootEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOverStableSubmoduleTensorPureKernelSpan
section
open scoped TensorProduct

namespace GlobalTheory.TensHead

def quotOps {V : Type} [AddCommGroup V] [Module ℂ V] (G : Set (Module.End ℂ V))
    (K : Submodule ℂ V) : Set (Module.End ℂ (V ⧸ K)) :=
  {f | ∃ g ∈ G, f ∘ₗ K.mkQ = K.mkQ ∘ₗ g}

theorem quot_simple {V : Type} [AddCommGroup V] [Module ℂ V] (G : Set (Module.End ℂ V))
    (K : Submodule ℂ V) (hs : Stab G K) (hK : SimpleOver G K) :
    ∀ U : Submodule ℂ (V ⧸ K), Stab (quotOps G K) U → U = ⊥ ∨ U = ⊤ := by
  intro U hU
  have hst : Stab G (U.comap K.mkQ) := by
    intro g hg x hx
    have hf : (K.mapQ K g (fun y hy => hs g hg y hy)) ∘ₗ K.mkQ = K.mkQ ∘ₗ g := by
      ext y; simp
    have := hU _ ⟨g, hg, hf⟩ _ hx
    simpa using this
  have hle : K ≤ U.comap K.mkQ := by
    intro x hx; simp [(Submodule.Quotient.mk_eq_zero K).2 hx]
  rcases hK _ hst hle with h | h
  · left
    rw [← Submodule.map_comap_eq_of_surjective K.mkQ_surjective U, h, Submodule.mkQ_map_self]
  · right
    rw [← Submodule.map_comap_eq_of_surjective K.mkQ_surjective U, h, Submodule.map_top,
      LinearMap.range_eq_top.2 K.mkQ_surjective]

theorem ker_map_mkQ_le {V₀ V₁ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁]
    [Module ℂ V₁] (K₀ : Submodule ℂ V₀) (K₁ : Submodule ℂ V₁) :
    LinearMap.ker (TensorProduct.map K₀.mkQ K₁.mkQ) ≤ tensKer K₀ K₁ := by
  rw [TensorProduct.map_ker (LinearMap.exact_subtype_mkQ K₀) K₀.mkQ_surjective
    (LinearMap.exact_subtype_mkQ K₁) K₁.mkQ_surjective]
  refine sup_le ?_ ?_
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul x k => exact Submodule.subset_span ⟨x, k, Or.inr k.2, by simp⟩
    | add a b ha hb => simpa only [map_add] using add_mem ha hb
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul k y => exact Submodule.subset_span ⟨k, y, Or.inl k.2, by simp⟩
    | add a b ha hb => simpa only [map_add] using add_mem ha hb

theorem simpleOver_tensKer : ∀ {V₀ V₁ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
    (A : Set (Module.End ℂ V₀)) (B : Set (Module.End ℂ V₁)) (K₀ : Submodule ℂ V₀) (K₁ : Submodule ℂ V₁),
    Module.rank ℂ V₀ ≤ Cardinal.aleph0 → GlobalTheory.TensHead.Stab A K₀ → GlobalTheory.TensHead.Stab B K₁ →
    GlobalTheory.TensHead.SimpleOver A K₀ → GlobalTheory.TensHead.SimpleOver B K₁ →
    GlobalTheory.TensHead.SimpleOver (GlobalTheory.TensHead.tensOps A B) (GlobalTheory.TensHead.tensKer K₀ K₁) := by
  intro V₀ V₁ _ _ _ _ A B K₀ K₁ hr hA hB hsA hsB N hN hKN
  set φ := TensorProduct.map K₀.mkQ K₁.mkQ with hφ
  have hker : LinearMap.ker φ ≤ N := (ker_map_mkQ_le K₀ K₁).trans hKN
  have hstU : Stab (tensOps (quotOps A K₀) (quotOps B K₁)) (N.map φ) := by
    rintro f hf _ ⟨x, hx, rfl⟩
    rcases hf with ⟨f', ⟨g, hg, hfg⟩, rfl⟩ | ⟨f', ⟨g, hg, hfg⟩, rfl⟩
    · have hc : TensorProduct.map f' LinearMap.id ∘ₗ φ = φ ∘ₗ TensorProduct.map g LinearMap.id := by
        rw [hφ, ← TensorProduct.map_comp, ← TensorProduct.map_comp, hfg]; rfl
      refine ⟨TensorProduct.map g LinearMap.id x, hN _ (Or.inl ⟨g, hg, rfl⟩) x hx, ?_⟩
      exact (LinearMap.congr_fun hc x).symm
    · have hc : TensorProduct.map LinearMap.id f' ∘ₗ φ = φ ∘ₗ TensorProduct.map LinearMap.id g := by
        rw [hφ, ← TensorProduct.map_comp, ← TensorProduct.map_comp, hfg]; rfl
      refine ⟨TensorProduct.map LinearMap.id g x, hN _ (Or.inr ⟨g, hg, rfl⟩) x hx, ?_⟩
      exact (LinearMap.congr_fun hc x).symm
  rcases _root_.GlobalTheory.TensHead.simple_tensor (quotOps A K₀) (quotOps B K₁) ((rank_quotient_le K₀).trans hr)
    (quot_simple A K₀ hA hsA) (quot_simple B K₁ hB hsB) _ hstU with h | h
  · left
    refine le_antisymm ?_ hKN
    intro x hx
    apply ker_map_mkQ_le K₀ K₁
    rw [LinearMap.mem_ker, ← Submodule.mem_bot ℂ, ← h]
    exact Submodule.mem_map_of_mem hx
  · right
    rw [eq_top_iff]
    intro x _
    have : φ x ∈ N.map φ := h ▸ Submodule.mem_top
    obtain ⟨y, hy, hxy⟩ := this
    have : x - y ∈ LinearMap.ker φ := by simp [hxy]
    simpa using add_mem (hker this) hy

end GlobalTheory.TensHead
end

