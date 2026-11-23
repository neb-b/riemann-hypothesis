module

public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.RhoRepresentations.EquivSection
section
noncomputable section

open MeasureTheory

namespace PositivityTheory.RgDs.K

theorem equivariant_section_holds : EquivSection := by
  intro G _ _ _ _ _ _ _ A S _ _ _ _ _ _ ρ σ hρ1 hρm hρc hσ1 hσm hσc f hf hfe
  obtain ⟨s0, hs0⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  have hs0y : ∀ y, f (s0 y) = y := fun y => by
    simpa using congrArg (fun T : S →ₗ[ℂ] S => T y) hs0
  have hσmul : ∀ a b y, σ (a * b) y = σ a (σ b y) := fun a b y => by rw [hσm]; rfl
  have hρmul : ∀ a b x, ρ (a * b) x = ρ a (ρ b x) := fun a b x => by rw [hρm]; rfl
  have hσinv : ∀ g y, σ g (σ g⁻¹ y) = y := fun g y => by
    rw [← hσmul, mul_inv_cancel, hσ1]; rfl
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure G, μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  let F : S → G → A := fun y g => ρ g (s0 (σ g⁻¹ y))
  have hFc : ∀ y, Continuous (F y) := fun y =>
    hρc.clm_apply ((LinearMap.continuous_of_finiteDimensional s0).comp ((hσc y).comp continuous_inv))
  have hFi : ∀ y, Integrable (F y) μ := fun y =>
    integrableOn_univ.mp ((hFc y).continuousOn.integrableOn_compact isCompact_univ)
  have hFadd : ∀ x y, F (x + y) = F x + F y := fun x y => by
    funext g; simp [F]
  have hFsmul : ∀ (r : ℂ) y, F (r • y) = r • F y := fun r y => by
    funext g; simp [F]
  set c : ℝ := μ.real Set.univ with hc_def
  have hc : c ≠ 0 := by
    rw [hc_def, Measure.real]
    exact ENNReal.toReal_ne_zero.mpr ⟨isOpen_univ.measure_ne_zero μ Set.univ_nonempty, measure_ne_top μ _⟩
  let s : S →ₗ[ℂ] A :=
    { toFun := fun y => ((c : ℂ)⁻¹) • ∫ g, F y g ∂μ
      map_add' := fun x y => by
        simp only [hFadd]
        rw [Pi.add_def, integral_add (hFi x) (hFi y), smul_add]
      map_smul' := fun r y => by
        simp only [hFsmul, RingHom.id_apply]
        rw [Pi.smul_def, integral_smul, smul_comm] }
  refine ⟨s, fun y => ?_, fun h y => ?_⟩
  · let fL : A →L[ℂ] S := LinearMap.toContinuousLinearMap f
    have h1 : f (∫ g, F y g ∂μ) = ∫ g, fL (F y g) ∂μ :=
      (fL.integral_comp_comm (hFi y)).symm
    have h2 : ∀ g, fL (F y g) = y := fun g => by
      show f (ρ g (s0 (σ g⁻¹ y))) = y
      rw [hfe, hs0y, hσinv]
    show f (((c : ℂ)⁻¹) • ∫ g, F y g ∂μ) = y
    rw [map_smul, h1]
    simp only [h2, integral_const]
    rw [← hc_def, ← Complex.coe_smul, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hc), one_smul]
  · have h3 : ∀ g, F (σ h y) (h * g) = ρ h (F y g) := fun g => by
      show ρ (h * g) (s0 (σ (h * g)⁻¹ (σ h y))) = ρ h (ρ g (s0 (σ g⁻¹ y)))
      rw [hρmul, mul_inv_rev, hσmul, ← hσmul h⁻¹ h, inv_mul_cancel, hσ1]; rfl
    have h4 : ∫ g, F (σ h y) g ∂μ = ρ h (∫ g, F y g ∂μ) := by
      rw [← integral_mul_left_eq_self (F (σ h y)) h]
      simp only [h3]
      exact (ρ h).integral_comp_comm (hFi y)
    show ((c : ℂ)⁻¹) • ∫ g, F (σ h y) g ∂μ = ρ h (((c : ℂ)⁻¹) • ∫ g, F y g ∂μ)
    rw [h4, map_smul]

end PositivityTheory.RgDs.K
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.RhoRepresentations.RhoRep
section
noncomputable section

open Finset Matrix

namespace PositivityTheory.RgDs.K

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

lemma rr_toMK_one (ε : Fin n → Bool) : toMK (1 : KG ε) = 1 := rfl

lemma rr_toMK_mul {ε : Fin n → Bool} (k k' : KG ε) : toMK (k * k') = toMK k * toMK k' := rfl

lemma rr_toMK_inv {ε : Fin n → Bool} (k : KG ε) : (toMK k)⁻¹ = toMK k⁻¹ := by
  show _ = ((((k : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
  rw [Matrix.coe_units_inv]

lemma rr_adC_one (p q : Fin n × Fin n) : adC (1 : Matrix (Fin n) (Fin n) ℂ) p q = if p = q then 1 else 0 := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  simp only [adC, inv_one, Matrix.one_apply, Prod.mk.injEq]
  by_cases h1 : a = c <;> by_cases h2 : b = d <;> simp [h1, h2, eq_comm]

lemma rr_adC_mul (A B : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n × Fin n) :
    adC (A * B) p q = ∑ r : Fin n × Fin n, adC B p r * adC A r q := by
  simp only [adC, Matrix.mul_inv_rev, Matrix.mul_apply, Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r1 _ => Finset.sum_congr rfl fun r2 _ => ?_
  ring

lemma rr_prod_ite {l : ℕ} (w x : Fin l → Fin n × Fin n) :
    (∏ i, (if w i = x i then (1 : ℂ) else 0)) = if w = x then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma rr_op_one {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : T.op 1 = 1 := by
  simp [KType.op]

lemma rr_op_mul {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k k' : KG ε) (v : T.V) :
    T.op (k * k') v = T.op k (T.op k' v) := by
  simp [KType.op]

theorem rho_representation_holds : PositivityTheory.RgDs.K.RhoRep := by
  intro n ε Λ T m
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a
    funext x'
    simp only [rhoA, rr_toMK_one, rr_adC_one, rr_prod_ite, rr_op_one, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  · intro k k' a
    funext x'
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [rhoA, map_sum, map_smul, Finset.smul_sum, smul_smul]
    refine Eq.trans ?_ (Finset.sum_comm (s := (Finset.univ : Finset (Fin x'.1 → Fin n × Fin n))) (t := (Finset.univ : Finset (Fin x'.1 → Fin n × Fin n)))).symm
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Finset.sum_smul, rr_op_mul]
    congr 1
    simp only [rr_toMK_mul, rr_adC_mul]
    rw [Finset.prod_univ_sum]
    simp only [Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    ring
  · intro k a a'
    funext x'
    simp only [rhoA, Pi.add_apply, map_add (f := _), smul_add, Finset.sum_add_distrib]
  · intro k c a
    funext x'
    simp only [rhoA, Pi.smul_apply, map_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [smul_comm]
  · intro a
    have hK : Continuous fun k : KG ε => toMK k :=
      (continuous_toM ε).comp continuous_subtype_val
    have hKi : Continuous fun k : KG ε => (toMK k)⁻¹ := by
      simp only [rr_toMK_inv]
      exact hK.comp continuous_inv
    have hop : ∀ v : T.V, Continuous fun k : KG ε => T.op k v := fun v =>
      (continuous_subtype_val.comp T.cont).clm_apply continuous_const
    refine continuous_pi fun x' => ?_
    simp only [rhoA]
    refine continuous_finsetSum _ fun w _ => ?_
    refine Continuous.smul ?_ (hop _)
    refine continuous_finsetProd _ fun i _ => ?_
    simp only [adC]
    exact ((continuous_apply _).comp ((continuous_apply _).comp hK)).mul
      ((continuous_apply _).comp ((continuous_apply _).comp hKi))

end PositivityTheory.RgDs.K
end
end

