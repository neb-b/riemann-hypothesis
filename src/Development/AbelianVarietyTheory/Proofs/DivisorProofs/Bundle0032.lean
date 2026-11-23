module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentSeparabilityAverage
section
open scoped TensorProduct

namespace GlobalTheory.SepAverage

variable {C : Type} [CommRing C] {H : Type*} [AddCommGroup H] [Module C H]

theorem exists_proj (E' M : Submodule C H) (h : IsCompl E' M) :
    ∃ σ : Module.End C H, (∀ e ∈ E', σ e = 0) ∧ ∀ u, u - σ u ∈ E' := by
  refine ⟨M.projection E' h.symm, fun e he => Submodule.projection_apply_of_mem_right h.symm he, ?_⟩
  intro u
  have := Submodule.projection_add_projection_eq_self h u
  have e : u - M.projection E' h.symm u = E'.projection M h u := by
    exact (eq_sub_of_add_eq this).symm
  rw [e]; exact Submodule.projection_apply_mem _ _

theorem map_smul_top_le (I : Ideal C) (f : Module.End C H) (P : Submodule C H)
    (hf : ∀ w, f w ∈ P) : ∀ w ∈ I • (⊤ : Submodule C H), f w ∈ I • P := by
  intro w hw
  have : Submodule.map f (I • (⊤ : Submodule C H)) ≤ I • P := by
    rw [Submodule.map_smul'']
    apply Submodule.smul_mono le_rfl
    rintro _ ⟨v, -, rfl⟩; exact hf v
  exact this ⟨w, hw, rfl⟩

end GlobalTheory.SepAverage

namespace GlobalTheory.SepAverage

theorem avg_comm {C : Type} [CommRing C] {H : Type*} [AddCommGroup H] [Module C H]
    {O : Type} [Ring O] (ρ : O →+* Module.End C H) {k : ℕ} (x y : Fin k → O)
    (hsep : ∀ c : O, ∑ j, (c * x j) ⊗ₜ[ℤ] y j = ∑ j, x j ⊗ₜ[ℤ] (y j * c))
    (g : Module.End C H) (c : O) :
    ρ c * ∑ j, ρ (x j) * g * ρ (y j) = (∑ j, ρ (x j) * g * ρ (y j)) * ρ c := by
  let B : O →ₗ[ℤ] O →ₗ[ℤ] Module.End C H :=
    LinearMap.mk₂ ℤ (fun a b => ρ a * g * ρ b)
      (by intros; simp [add_mul]) (by intros; simp only [map_zsmul, smul_mul_assoc])
      (by intros; simp [mul_add]) (by intros; simp only [map_zsmul, mul_smul_comm])
  have h := congrArg (TensorProduct.lift B) (hsep c)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, TensorProduct.lift.tmul, B, LinearMap.mk₂_apply] at h
  calc ρ c * ∑ j, ρ (x j) * g * ρ (y j) = ∑ j, ρ (c * x j) * g * ρ (y j) := by
        simp [Finset.mul_sum, map_mul, mul_assoc]
    _ = ∑ j, ρ (x j) * g * ρ (y j * c) := h
    _ = _ := by simp [Finset.sum_mul, map_mul, mul_assoc]

theorem comm_poly {C : Type} [CommRing C] {H : Type*} [AddCommGroup H] [Module C H]
    (a p : Module.End C H) (h : a * p = p * a) :
    a * (p * p * 3 - p * p * p * 2) = (p * p * 3 - p * p * p * 2) * a := by
  have hc : Commute a p := h
  exact (((hc.mul_right hc).mul_right (Commute.ofNat_right a 3)).sub_right
    (((hc.mul_right hc).mul_right hc).mul_right (Commute.ofNat_right a 2))).eq

theorem exists_idempotent_average : ∀ (C O : Type) [CommRing C] [Ring O] (I : Ideal C), I ^ 2 = ⊥ → ∀ (N : ℤ) (k : ℕ) (x y : Fin k → O), ∑ j, x j * y j = (N : O) → (∀ c : O, ∑ j, (c * x j) ⊗ₜ[ℤ] y j = ∑ j, x j ⊗ₜ[ℤ] (y j * c)) → IsUnit (N : C) → ∀ (H : Type*) [AddCommGroup H] [Module C H] (ρ : O →+* Module.End C H) (ε : Module.End C H), ε * ε = ε → (∀ c, ρ c * ε = ε * ρ c) → ∀ F : Submodule C H, I • ⊤ ≤ F → (∀ c, ∀ x ∈ F, ρ c x ∈ F) → (∀ x ∈ F, ε x ∈ F) → (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) → ∃ π : Module.End C H, π * π = π ∧ (∀ c, ρ c * π = π * ρ c) ∧ π * ε = π ∧ ε * π = π ∧ (∀ z, ε z = z → z - π z ∈ F) ∧ (∀ z ∈ F, ε z = z → π z ∈ I • (⊤ : Submodule C H)) := by
  intro C O _ _ I hI N k x y hxy hsep hN H _ _ ρ ε hε hρε F hIF hρF hεF hEM
  obtain ⟨E', M, hc, hEF⟩ := hEM
  obtain ⟨σ, hσE, hσ⟩ := exists_proj E' M hc
  obtain ⟨n, hn⟩ := hN.exists_left_inv
  have hE'F : E' ≤ F := hEF ▸ le_sup_left
  have hpres : ∀ f : Module.End C H, ∀ w ∈ I • (⊤ : Submodule C H), f w ∈ I • (⊤ : Submodule C H) :=
    fun f => map_smul_top_le I f ⊤ (fun _ => trivial)
  have hερ : ∀ c v, ε (ρ c v) = ρ c (ε v) := fun c v => (LinearMap.congr_fun (hρε c) v).symm
  set q : Module.End C H := ε * σ * ε with hq
  have hεq : ε * q = q := by simp only [hq, ← mul_assoc, hε]
  have hqε : q * ε = q := by simp only [hq, mul_assoc, hε]
  set p : Module.End C H := n • ∑ j, ρ (x j) * q * ρ (y j) with hp
  have hpc : ∀ c, ρ c * p = p * ρ c := by
    intro c; rw [hp, mul_smul_comm, smul_mul_assoc, avg_comm ρ x y hsep]
  have hεp : ε * p = p := by
    rw [hp, mul_smul_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, ← mul_assoc, ← hρε, mul_assoc (ρ (x j)) ε q, hεq]
  have hpε : p * ε = p := by
    rw [hp, smul_mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc (ρ (x j) * q), hρε, ← mul_assoc, mul_assoc (ρ (x j)) q ε, hqε]
  have hsum : ∀ z, ∑ j, ρ (x j) (ρ (y j) z) = (N : C) • z := by
    intro z
    have := LinearMap.congr_fun (congrArg ρ hxy) z
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_intCast, LinearMap.sum_apply, Module.End.mul_apply,
      Module.End.intCast_apply] at this
    rw [this, Int.cast_smul_eq_zsmul]
  have hpz : ∀ z, p z = n • ∑ j, ρ (x j) (ε (σ (ε (ρ (y j) z)))) := by
    intro z
    simp [hp, hq, LinearMap.sum_apply, Module.End.mul_apply]
  have ha : ∀ z, ε z = z → z - p z ∈ F := by
    intro z hz
    have key : z - p z = n • ∑ j, ρ (x j) (ε (ρ (y j) z - σ (ρ (y j) z))) := by
      have hw : ∀ j, ε (ρ (y j) z) = ρ (y j) z := fun j => by rw [hερ, hz]
      rw [hpz]
      simp only [hw, map_sub, Finset.sum_sub_distrib, hsum, smul_sub, smul_smul, hn, one_smul]
    rw [key]
    refine F.smul_mem _ (F.sum_mem fun j _ => hρF _ _ (hεF _ (hE'F (hσ _))))
  have hb : ∀ z ∈ F, p z ∈ I • (⊤ : Submodule C H) := by
    intro z hzF
    rw [hpz]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => hpres _ _ (hpres _ _ ?_))
    have hv : ε (ρ (y j) z) ∈ F := hεF _ (hρF _ _ hzF)
    rw [← hEF] at hv
    obtain ⟨e, he, t, ht, het⟩ := Submodule.mem_sup.mp hv
    rw [← het, map_add (f := _), hσE e he, zero_add]
    exact hpres σ t ht
  set u : Module.End C H := p * p - p with hu_def
  have hu : ∀ z, u z ∈ I • (⊤ : Submodule C H) := by
    intro z
    have h1 : p z = p (ε z) := by rw [← Module.End.mul_apply, hpε]
    have h2 : ε (ε z - p (ε z)) = ε z - p (ε z) := by
      rw [map_sub, ← Module.End.mul_apply ε ε, hε, ← Module.End.mul_apply ε p, hεp]
    have h3 := hb _ (ha (ε z) (by rw [← Module.End.mul_apply, hε]))
    have e : u z = -(p (ε z - p (ε z))) := by
      simp only [hu_def, LinearMap.sub_apply, Module.End.mul_apply, map_sub, h1]
      rw [← h1]; abel
    rw [e]; exact Submodule.neg_mem _ h3
  have huu : u * u = 0 := by
    ext z
    have h := map_smul_top_le I u (I • ⊤) hu _ (hu z)
    rw [← Submodule.mul_smul, ← pow_two, hI, Submodule.bot_smul, Submodule.mem_bot] at h
    simpa using h
  refine ⟨p * p * 3 - p * p * p * 2, ?_, fun c => comm_poly _ _ (hpc c), ?_, ?_, ?_, ?_⟩
  · have e : (p * p * 3 - p * p * p * 2) * (p * p * 3 - p * p * p * 2)
        - (p * p * 3 - p * p * p * 2) = (p * p - p) * (p * p - p) * (4 * (p * p) - 4 * p - 3) := by
      noncomm_ring
    rw [← hu_def, huu, zero_mul] at e
    exact sub_eq_zero.mp e
  · simp only [sub_mul, mul_assoc, hpε]
    simp only [← mul_assoc, Commute.ofNat_left 3 ε |>.eq, Commute.ofNat_left 2 ε |>.eq]
    simp only [mul_assoc, hpε]
  · simp only [mul_sub, ← mul_assoc, hεp]
  all_goals
    have hd : ∀ z, (p * p * 3 - p * p * p * 2) z - p z ∈ I • (⊤ : Submodule C H) := by
      intro z
      have e : p * p * 3 - p * p * p * 2 - p = -((p * p - p) * (2 * p - 1)) := by noncomm_ring
      rw [← LinearMap.sub_apply, e, LinearMap.neg_apply, ← hu_def, Module.End.mul_apply]
      exact Submodule.neg_mem _ (hu _)
  · intro z hz
    have := F.sub_mem (ha z hz) (hIF (hd z))
    convert this using 1; abel
  · intro z hzF _
    have := Submodule.add_mem _ (hb z hzF) (hd z)
    convert this using 1; abel

end GlobalTheory.SepAverage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveOfIsIntegral
section
namespace GlobalTheory.InjectiveOfIntegral

theorem exists_injective_of_isIntegral {A B O C : Type} [CommRing A] [IsDomain A] [CommRing B]
    [IsDomain B] [CommRing O] [Field C] [IsAlgClosed C] [Algebra O C] (v : Valuation C NNReal)
    (hv : Valuation.Integers v O) [Algebra A B] [Algebra.IsIntegral A B]
    (hAB : Function.Injective (algebraMap A B)) (j : A →+* O)
    (hj : Function.Injective ((algebraMap O C).comp j)) :
    ∃ j' : B →+* O, Function.Injective ((algebraMap O C).comp j') := by
  classical
  let _ : Algebra A C := ((algebraMap O C).comp j).toAlgebra
  let _ : Algebra A O := j.toAlgebra
  have : IsScalarTower A O C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hAC : Function.Injective (algebraMap A C) := hj
  have : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr hAB
  have : Module.IsTorsionFree A C := Module.isTorsionFree_iff_algebraMap_injective.mpr hAC
  have : Algebra.IsAlgebraic A B := Algebra.IsIntegral.isAlgebraic
  let ψ : B →ₐ[A] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hker : RingHom.ker (ψ : B →+* C) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := A)
    ext a
    rw [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot,
      show (ψ : B →+* C) (algebraMap A B a) = algebraMap A C a from ψ.commutes a]
    exact ⟨fun h => hAC (h.trans (map_zero _).symm), fun h => by rw [h, map_zero]⟩
  have hψ : Function.Injective (ψ : B →+* C) := (RingHom.injective_iff_ker_eq_bot _).mpr hker
  have hint : ∀ b : B, v (ψ b) ≤ 1 := by
    intro b
    have hb : IsIntegral A (ψ b) := (Algebra.IsIntegral.isIntegral b).map ψ
    exact hv.mem_of_integral hb.tower_top
  choose g hg using fun b => hv.exists_of_le_one (hint b)
  let j' : B →+* O :=
    { toFun := g
      map_one' := hv.hom_inj (by simp only [hg, map_one])
      map_mul' := fun x y => hv.hom_inj (by simp only [hg, map_mul])
      map_zero' := hv.hom_inj (by simp only [hg, map_zero])
      map_add' := fun x y => hv.hom_inj (by simp only [hg, map_add (f := _)]) }
  refine ⟨j', ?_⟩
  have e : (algebraMap O C).comp j' = (ψ : B →+* C) := RingHom.ext hg
  rw [e]
  exact hψ

end GlobalTheory.InjectiveOfIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegrableDensityOfBoundByIntegralCompactA
section
open MeasureTheory

namespace GlobalTheory

theorem exists_integrable_density_of_bound_by_integral_compact : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (K : Set X), IsCompact K → μ K < ⊤ → ∀ (S : Submodule ℂ (X → ℂ)), (∀ f ∈ S, Continuous f) → ∀ (Λ : (X → ℂ) → ℂ) (C : ℝ), (∀ f ∈ S, ∀ f' ∈ S, ∀ c : ℂ, Λ (c • f + f') = c * Λ f + Λ f') → (∀ f ∈ S, ‖Λ f‖ ≤ C * ∫ x in K, ‖f x‖ ∂μ) → ∃ a : X → ℂ, Measurable a ∧ Integrable a μ ∧ (∀ x ∉ K, a x = 0) ∧ ∀ f ∈ S, ∫ x, f x * a x ∂μ = Λ f := by
  intro X _ _ _ _ μ K hK hμK S hS Λ C hlin hbd
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  set ν := μ.restrict K with hν
  haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hμK.ne
  have hmem : ∀ f : S, MemLp (f : X → ℂ) 2 ν := by
    intro f
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hS f f.2).continuousOn
    exact MemLp.of_bound (hS f f.2).aestronglyMeasurable M
      ((ae_restrict_iff' hKm).2 (Filter.Eventually.of_forall hM))
  let T : S →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := fun f => (hmem f).toLp _
      map_add' := fun f g => MemLp.toLp_add (hmem f) (hmem g)
      map_smul' := fun c f => MemLp.toLp_const_smul c (hmem f) }
  have hT : ∀ f : S, T f = (hmem f).toLp _ := fun f => rfl
  have hΛ0 : Λ 0 = 0 := by
    have := hlin 0 S.zero_mem 0 S.zero_mem 1
    simpa using this
  let Λ' : S →ₗ[ℂ] ℂ :=
    { toFun := fun f => Λ f
      map_add' := fun f g => by
        have := hlin f f.2 g g.2 1
        simpa using this
      map_smul' := fun c f => by
        have := hlin f f.2 0 S.zero_mem c
        simpa [hΛ0] using this }
  have hΛ' : ∀ f : S, Λ' f = Λ f := fun f => rfl

  have hkey : ∀ f : S, ∫ x in K, ‖(f : X → ℂ) x‖ ∂μ ≤ ((ν Set.univ) ^ (1/2 : ℝ)).toReal * ‖T f‖ := by
    intro f
    have h12 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (μ := ν)
      (by norm_num) (hS f f.2).aestronglyMeasurable
    have hexp : (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) = (1 / 2 : ℝ) := by norm_num
    rw [hexp] at h12
    have hint : ∫ x in K, ‖(f : X → ℂ) x‖ ∂μ = (eLpNorm (f : X → ℂ) 1 ν).toReal := by
      rw [integral_norm_eq_lintegral_enorm (hS f f.2).aestronglyMeasurable,
        eLpNorm_one_eq_lintegral_eNorm (hS f f.2).aestronglyMeasurable]
    have hfin : eLpNorm (f : X → ℂ) 2 ν * ν Set.univ ^ (1 / 2 : ℝ) ≠ ⊤ :=
      ENNReal.mul_ne_top (hmem f).eLpNorm_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _))
    rw [hint, hT, Lp.norm_toLp]
    calc _ ≤ (eLpNorm (f : X → ℂ) 2 ν * ν Set.univ ^ (1 / 2 : ℝ)).toReal :=
          ENNReal.toReal_mono hfin h12
      _ = _ := by rw [ENNReal.toReal_mul, mul_comm]
  set B : ℝ := max C 0 * ((ν Set.univ) ^ (1/2 : ℝ)).toReal with hBdef
  have hB : ∀ f : S, ‖Λ' f‖ ≤ B * ‖T f‖ := by
    intro f
    have hI0 : 0 ≤ ∫ x in K, ‖(f : X → ℂ) x‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
    rw [hΛ']
    calc ‖Λ f‖ ≤ C * ∫ x in K, ‖(f : X → ℂ) x‖ ∂μ := hbd f f.2
      _ ≤ max C 0 * ∫ x in K, ‖(f : X → ℂ) x‖ ∂μ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hI0
      _ ≤ max C 0 * (((ν Set.univ) ^ (1/2 : ℝ)).toReal * ‖T f‖) :=
          mul_le_mul_of_nonneg_left (hkey f) (le_max_right _ _)
      _ = B * ‖T f‖ := by rw [hBdef, mul_assoc]
  have hker : LinearMap.ker T ≤ LinearMap.ker Λ' := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    have := hB f
    rw [hf, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  let φ₀ : LinearMap.range T →ₗ[ℂ] ℂ :=
    ((LinearMap.ker T).liftQ Λ' hker).comp T.quotKerEquivRange.symm.toLinearMap
  have hφ₀ : ∀ f : S, φ₀ ⟨T f, LinearMap.mem_range_self T f⟩ = Λ f := by
    intro f
    have h1 : T.quotKerEquivRange.symm ⟨T f, LinearMap.mem_range_self T f⟩
        = Submodule.Quotient.mk f := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [φ₀, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, h1,
      Submodule.liftQ_apply, hΛ']
  have hφb : ∀ v, ‖φ₀ v‖ ≤ B * ‖v‖ := by
    rintro ⟨v, f, rfl⟩
    have := hφ₀ f
    rw [this, ← hΛ']
    exact hB f
  let φ : StrongDual ℂ (LinearMap.range T) := φ₀.mkContinuous B hφb
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range T) φ
  set a₀ : Lp ℂ 2 ν := (InnerProductSpace.toDual ℂ (Lp ℂ 2 ν)).symm g with ha₀
  have hrep : ∀ f : S, inner ℂ a₀ (T f) = Λ f := by
    intro f
    rw [ha₀, InnerProductSpace.toDual_symm_apply]
    have := hg ⟨T f, LinearMap.mem_range_self T f⟩
    rw [this]
    simp only [φ, LinearMap.mkContinuous_apply]
    exact hφ₀ f
  have hm : Measurable (a₀ : X → ℂ) := (Lp.stronglyMeasurable a₀).measurable
  refine ⟨K.indicator (fun x => starRingEnd ℂ (a₀ x)),
    (Complex.continuous_conj.measurable.comp hm).indicator hKm, ?_, ?_, ?_⟩
  · rw [integrable_indicator_iff hKm]
    have : Integrable (a₀ : X → ℂ) ν := (Lp.memLp a₀).integrable (by norm_num)
    exact this.mono (Complex.continuous_conj.comp_aestronglyMeasurable this.1)
      (Filter.Eventually.of_forall fun x => by simp)
  · intro x hx
    exact Set.indicator_of_notMem hx _
  · intro f hf
    have key := hrep ⟨f, hf⟩
    rw [L2.inner_def] at key
    have hae : ((T ⟨f, hf⟩ : Lp ℂ 2 ν) : X → ℂ) =ᵐ[ν] f := MemLp.coeFn_toLp (hmem ⟨f, hf⟩)
    rw [← key]
    have hfun : (fun x => f x * K.indicator (fun x => starRingEnd ℂ (a₀ x)) x)
        = K.indicator (fun x => f x * starRingEnd ℂ (a₀ x)) := by
      funext x
      by_cases hx : x ∈ K <;> simp [hx]
    rw [hfun, integral_indicator hKm]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
    simp [mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralDomainExtensionWithMonicRoots
section
open Polynomial

namespace GlobalTheory

theorem exists_integral_domain_extension_monic_roots :
    ∀ (D : Type) [CommRing D] [IsDomain D], ∃ (C : Type) (_ : CommRing C) (_ : Algebra D C),
      IsDomain C ∧ Algebra.IsIntegral D C ∧ Function.Injective (algebraMap D C) ∧
      (∀ f : C[X], f.Monic → 0 < f.natDegree → ∃ y : C, f.eval y = 0) ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (h : D →+* K), Function.Injective h →
        ∃ e : C →+* K, Function.Injective e ∧ e.comp (algebraMap D C) = h := by
  intro D _ _
  have hDL : Function.Injective (algebraMap D (AlgebraicClosure (FractionRing D))) := by
    rw [IsScalarTower.algebraMap_eq D (FractionRing D) (AlgebraicClosure (FractionRing D))]
    exact (algebraMap (FractionRing D) (AlgebraicClosure (FractionRing D))).injective.comp
      (IsFractionRing.injective D (FractionRing D))
  have hCL : Function.Injective (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D)))
      (AlgebraicClosure (FractionRing D))) := Subtype.val_injective
  refine ⟨integralClosure D (AlgebraicClosure (FractionRing D)), inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro a b hab
    apply hDL
    simpa using congrArg Subtype.val hab
  · intro f hf hdeg
    have hdeg' : (f.map (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D)))
        (AlgebraicClosure (FractionRing D)))).degree ≠ 0 := by
      rw [degree_map_eq_of_injective hCL, degree_eq_natDegree hf.ne_zero]
      exact_mod_cast hdeg.ne'
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg'
    have hy' : f.eval₂ (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D)))
        (AlgebraicClosure (FractionRing D))) y = 0 := by rwa [IsRoot, eval_map] at hy
    have hyC : IsIntegral (integralClosure D (AlgebraicClosure (FractionRing D))) y :=
      ⟨f, hf, hy'⟩
    have hyD : IsIntegral D y := isIntegral_trans y hyC
    refine ⟨⟨y, hyD⟩, ?_⟩
    apply hCL
    rw [← eval₂_at_apply, map_zero]
    exact hy'
  · intro K _ _ h hinj
    letI : Algebra (FractionRing D) K := (IsFractionRing.lift hinj : FractionRing D →+* K).toAlgebra
    let φ : AlgebraicClosure (FractionRing D) →ₐ[FractionRing D] K := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    refine ⟨φ.toRingHom.comp (integralClosure D (AlgebraicClosure (FractionRing D))).val.toRingHom,
      φ.toRingHom.injective.comp Subtype.val_injective, ?_⟩
    ext a
    show φ (algebraMap D (AlgebraicClosure (FractionRing D)) a) = h a
    rw [IsScalarTower.algebraMap_apply D (FractionRing D) (AlgebraicClosure (FractionRing D)),
      AlgHom.commutes]
    exact IsFractionRing.lift_algebraMap hinj a

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralInvOneAddPrimeMulPadic
section
open scoped TensorProduct Classical

namespace GlobalTheory

theorem exists_integral_inv_one_add_prime_mul :
    ∀ (ℓ : ℕ) [Fact ℓ.Prime] (S : Type) [CommRing S] [Algebra ℤ_[ℓ] S] (s : S),
      IsIntegral ℤ_[ℓ] s → ∃ r : S, (1 + (ℓ : S) * s) * r = 1 ∧ IsIntegral ℤ_[ℓ] r := by
  intro ℓ _ S _ _ s hs
  let B := integralClosure ℤ_[ℓ] S
  let b : B := ⟨s, hs⟩
  have hu : IsUnit (1 + (ℓ : B) * b) := by
    by_contra hn
    obtain ⟨M, hM, hmem⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hn)
    have hmax : (M.comap (algebraMap ℤ_[ℓ] B)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ_[ℓ]) M
    have heq := IsLocalRing.eq_maximalIdeal hmax
    have hl : (ℓ : ℤ_[ℓ]) ∈ M.comap (algebraMap ℤ_[ℓ] B) := by
      rw [heq, PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap, map_natCast] at hl
    have h1 : (1 : B) ∈ M := by
      have := M.sub_mem hmem (M.mul_mem_right b hl)
      simpa using this
    exact hM.ne_top ((Ideal.eq_top_iff_one M).mpr h1)
  obtain ⟨r, hr⟩ := hu.exists_right_inv
  refine ⟨(r : S), ?_, r.2⟩
  have := congrArg (fun x : B => (x : S)) hr
  simpa [b] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantDerivationOfCounitalComul
section
open scoped TensorProduct

namespace GlobalTheory

theorem invariant_derivation_exists :
    ∀ (k A : Type) [CommRing k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → ∀ l : A →ₗ[k] k, (∀ a b, l (a * b) = ε a * l b + ε b * l a) → ∃ D : Derivation k A A, ∀ a, ε (D a) = l a := by
  intro k A _ _ _ ε Δ hε l hl
  obtain ⟨h1, h2⟩ := hε
  let F : A ⊗[k] A →ₗ[k] A := (TensorProduct.rid k A).toLinearMap ∘ₗ LinearMap.lTensor A l
  let E : A ⊗[k] A →ₗ[k] A :=
    (TensorProduct.rid k A).toLinearMap ∘ₗ LinearMap.lTensor A ε.toLinearMap
  have hF : ∀ a b : A, F (a ⊗ₜ b) = l b • a := fun a b => by simp [F]
  have hE : ∀ a b : A, E (a ⊗ₜ b) = ε b • a := fun a b => by simp [E]
  have key : ∀ x y : A ⊗[k] A, F (x * y) = E x * F y + E y * F x := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul c d =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, hF, hF, hF, hE, hE, hl]
        simp only [Algebra.smul_def, map_add (f := _), map_mul]
        ring
      | add y₁ y₂ ih₁ ih₂ =>
        rw [mul_add, map_add (f := _), ih₁, ih₂, map_add (f := _), map_add (f := _)]
        ring
    | add x₁ x₂ ih₁ ih₂ =>
      rw [add_mul, map_add (f := _), ih₁, ih₂, map_add (f := _), map_add (f := _)]
      ring
  have hEΔ : ∀ a, E (Δ a) = a := fun a => h2 a
  have hεF : ∀ x : A ⊗[k] A,
      ε (F x) = l (TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [hF]
      simp [mul_comm]
    | add x₁ x₂ ih₁ ih₂ => rw [map_add (f := _), map_add (f := _), ih₁, ih₂, map_add (f := _), map_add (f := _), map_add (f := _)]
  refine ⟨Derivation.mk' (F ∘ₗ Δ.toLinearMap) (fun a b => ?_), fun a => ?_⟩
  · simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, map_mul,
      key, hEΔ, smul_eq_mul]
  · show ε (F (Δ a)) = l a
    rw [hεF, h1]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFibreAndEqOfSpecializesOfIsFinite
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem finite_fibre_and_eq_of_specializes_of_isFinite :
    ∀ (Y Y' : Scheme.{0}) (k : Y' ⟶ Y), IsFinite k → ∀ y : Y,
      {a : Y' | k a = y}.Finite ∧ ∀ a b : Y', k a = y → k b = y → a ⤳ b → a = b := by
  intro Y Y' k hk y
  refine ⟨k.finite_preimage_singleton y, ?_⟩
  intro a b ha hb h
  have hd := (k.isDiscrete_preimage_singleton y).to_subtype
  have h' : (⟨a, ha⟩ : k ⁻¹' {y}) ⤳ ⟨b, hb⟩ :=
    Topology.IsInducing.subtypeVal.specializes_iff.mp h
  exact congrArg Subtype.val h'.eq

end GlobalTheory
end

