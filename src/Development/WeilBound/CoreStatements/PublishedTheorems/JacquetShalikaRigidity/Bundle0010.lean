module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
public import GroundTheory.AutomorphicForms.ReductionMahler
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SepSum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0679

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.RowsCompactSum
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace RowsCompactSum

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ}

theorem contFin : Continuous (fun (y : Fin k → Ad E) (i : Fin k) => pFin E (y i)) :=
  continuous_pi fun i => (GlobalTheory.CuspRep.GASplit.continuous_pFin E).comp (continuous_apply i)

theorem contInf : Continuous (fun (y : Fin k → Ad E) (i : Fin k) => pInf E (y i)) :=
  continuous_pi fun i => (GlobalTheory.CuspRep.GASplit.continuous_pInf E).comp (continuous_apply i)

theorem one_le (C₀ : Set (Fin k → Ad E)) (hC₀ : IsCompact C₀) (M : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ y,
    C₀.indicator (fun _ => (1 : ℝ≥0∞)) y ≤ ENNReal.ofReal B * ENNReal.ofReal
      (((fun y (i : Fin k) => pFin E (y i)) '' C₀).indicator
        (fun _ => ((1 + ‖fun i => pInf E (y i)‖) ^ M)⁻¹) fun i => pFin E (y i)) := by
  obtain ⟨R, hR⟩ := hC₀.exists_bound_of_continuousOn (contInf (E := E) (k := k)).continuousOn
  refine ⟨(1 + max R 0) ^ M, by positivity, fun y => ?_⟩
  by_cases hy : y ∈ C₀
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (Set.mem_image_of_mem _ hy), ← ENNReal.ofReal_mul (by positivity)]
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have h0 : 0 < (1 + ‖fun i => pInf E (y i)‖) ^ M := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ h0, one_mul]
    apply pow_le_pow_left₀ (by positivity)
    have := hR y hy
    linarith [le_max_left R 0]
  · rw [Set.indicator_of_notMem hy]
    exact bot_le

theorem sum_le (hN : N0) (hG3 : ThetaSeriesBound) (hk : 1 ≤ k) (C₀ : Set (Fin k → Ad E)) (hC₀ : IsCompact C₀) (a : ℕ) (ha : k ≤ a) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ (g : GA E k) (r : ℝ), 0 < r → (∀ ξ, ξ ≠ 0 → r ≤ height g ξ) →
      ∑' ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g)) ≤
        ENNReal.ofReal (B * (C * (r ^ a)⁻¹)) := by
  have hCf : IsCompact ((fun y (i : Fin k) => pFin E (y i)) '' C₀) := hC₀.image contFin
  obtain ⟨M, C, hMC⟩ := hG3 E k _ hCf a ha
  obtain ⟨B, hB, hB1⟩ := one_le C₀ hC₀ M
  have hlast := (hN E k k hk le_rfl).2.2.2.2.2.2.2.2.2
  refine ⟨B, max C 0, hB, le_max_right _ _, fun g r hr hrh => ?_⟩
  have hinj : Function.Injective (fun ξ : RowT E k k => (⟨ξ.1, ξ.2.1⟩ : {ξ : Fin k → E // ξ ≠ 0})) := by
    intro x y h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext h
  let F : {ξ : Fin k → E // ξ ≠ 0} → ℝ≥0∞ := fun ξ => ENNReal.ofReal
    (((fun y (i : Fin k) => pFin E (y i)) '' C₀).indicator
      (fun _ => ((1 + ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i)‖) ^ M)⁻¹)
      fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i))
  have hF : ∑' ξ, F ξ ≤ ENNReal.ofReal (C * (r ^ a)⁻¹) := hMC g r hr hrh
  have h1 : ∀ ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g)) ≤
      ENNReal.ofReal B * F ⟨ξ.1, ξ.2.1⟩ := by
    intro ξ
    rw [hlast]
    exact hB1 _
  calc _ ≤ ∑' ξ : RowT E k k, ENNReal.ofReal B * F ⟨ξ.1, ξ.2.1⟩ := ENNReal.tsum_le_tsum h1
    _ ≤ ∑' ξ, ENNReal.ofReal B * F ξ := ENNReal.tsum_comp_le_tsum_of_injective hinj (fun ξ => ENNReal.ofReal B * F ξ)
    _ = ENNReal.ofReal B * ∑' ξ, F ξ := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal B * ENNReal.ofReal (max C 0 * (r ^ a)⁻¹) := by
        gcongr
        refine hF.trans (ENNReal.ofReal_le_ofReal ?_)
        gcongr
        exact le_max_left _ _
    _ = ENNReal.ofReal (B * (max C 0 * (r ^ a)⁻¹)) := (ENNReal.ofReal_mul hB).symm

theorem r_le (hD : D0) (hK : K1) (hk : 1 ≤ k) (g : GA E k) :
    0 < dmin g * Dt g ^ ((k : ℝ)⁻¹) ∧ ∀ ξ, ξ ≠ 0 → dmin g * Dt g ^ ((k : ℝ)⁻¹) ≤ height g ξ := by
  have hDt := (hD E k).1 g
  have hK' := hK E k hk
  have hp : 0 < Dt g ^ ((k : ℝ)⁻¹) := Real.rpow_pos_of_pos hDt _
  refine ⟨mul_pos (hK'.2.1 g) hp, fun ξ hξ => ?_⟩
  have h1 := hK'.2.2.1 g ξ hξ
  have h2 : height g ξ = ht g ξ * Dt g ^ ((k : ℝ)⁻¹) := by
    unfold ht; field_simp
  rw [h2]
  exact mul_le_mul_of_nonneg_right h1 hp.le

end RowsCompactSum

theorem rows_compact_of_bound : D0 → N0 → H0 → ThetaSeriesBound → K1 → RowsInCompactSet := by
  intro hD hN _ hG3 hK E _ _ _ k hk C₀ hC₀
  refine ⟨fun g => ?_, fun a ha => ?_⟩
  · obtain ⟨B, C, hB, hC, h⟩ := RowsCompactSum.sum_le hN hG3 hk C₀ hC₀ k le_rfl
    obtain ⟨hr, hrh⟩ := RowsCompactSum.r_le hD hK hk g
    have hfin := h g _ hr hrh
    have hne : ∑' ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g)) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfin
    refine (ENNReal.finite_const_le_of_tsum_ne_top hne one_ne_zero).subset fun ξ hξ => ?_
    simp only [Set.mem_setOf_eq] at hξ ⊢
    rw [Set.indicator_of_mem hξ]
  · obtain ⟨B, C, hB, hC, h⟩ := RowsCompactSum.sum_le hN hG3 hk C₀ hC₀ a ha
    refine ⟨B * C, fun g => ?_⟩
    obtain ⟨hr, hrh⟩ := RowsCompactSum.r_le hD hK hk g
    have hDt := (hD E k).1 g
    have hd := (hK E k hk).2.1 g
    have hp : 0 < Dt g ^ ((k : ℝ)⁻¹) := Real.rpow_pos_of_pos hDt _
    have hw0 : 0 ≤ wt a g := by unfold wt; exact pow_nonneg (le_min zero_le_one hd.le) _
    have hw : wt a g ≤ dmin g ^ a := by unfold wt; exact pow_le_pow_left₀ (le_min zero_le_one hd.le) (min_le_right _ _) _
    calc (∑' ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g))) *
          ENNReal.ofReal (wt a g)
        ≤ ENNReal.ofReal (B * (C * ((dmin g * Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹)) * ENNReal.ofReal (wt a g) := by
          gcongr; exact h g _ hr hrh
      _ = ENNReal.ofReal (B * (C * ((dmin g * Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹) * wt a g) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (B * C * Dt g ^ (-(a : ℝ) / k)) := by
          apply ENNReal.ofReal_le_ofReal
          have he : Dt g ^ (-(a : ℝ) / k) = ((Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹ := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hDt.le, ← Real.rpow_neg hDt.le]
            congr 1; ring
          rw [he, mul_pow, mul_inv]
          have hda : 0 < dmin g ^ a := pow_pos hd _
          have hpa : 0 < (Dt g ^ ((k : ℝ)⁻¹)) ^ a := pow_pos hp _
          calc B * (C * ((dmin g ^ a)⁻¹ * ((Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹)) * wt a g
              ≤ B * (C * ((dmin g ^ a)⁻¹ * ((Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹)) * dmin g ^ a := by
                gcongr
            _ = B * C * ((Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹ := by field_simp

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SeparatedThetaSum
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace SeparatedThetaSum

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ}

omit [_root_.NumberField.IsTotallyComplex E] in
theorem isOpen_fInt (S : Finset (HeightOneSpectrum (𝓞 E))) :
    IsOpen {y : Fin k → Af E | ∀ v, v ∉ S → ∀ i, y i v ∈ v.adicCompletionIntegers E} := by
  have h := RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (A := fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E)))
    (fun v => Valued.isOpen_integer _) (p := fun v => v ∉ S)
  have e : {y : Fin k → Af E | ∀ v, v ∉ S → ∀ i, y i v ∈ v.adicCompletionIntegers E} =
      ⋂ i, (fun y : Fin k → Af E => y i) ⁻¹' {x | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers E} := by
    ext y; simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
    exact ⟨fun h i v hv => h v hv i, fun h v hv i => h i v hv⟩
  rw [e]
  exact isOpen_iInter_of_finite fun i => h.preimage (continuous_apply i)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem exists_finite_fInt {C : Set (Fin k → Af E)} (hC : IsCompact C) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 E)), ∀ y ∈ C, ∀ v, v ∉ S → ∀ i, y i v ∈ v.adicCompletionIntegers E := by
  classical
  obtain ⟨T, hT⟩ := hC.elim_finite_subcover
    (fun S : Finset (HeightOneSpectrum (𝓞 E)) =>
      {y : Fin k → Af E | ∀ v, v ∉ S → ∀ i, y i v ∈ v.adicCompletionIntegers E})
    (fun S => isOpen_fInt S) (fun y _ => by
      have hfin : (⋃ i, {v : HeightOneSpectrum (𝓞 E) | y i v ∉ v.adicCompletionIntegers E}).Finite :=
        Set.finite_iUnion fun i => Filter.eventually_cofinite.1 (y i).2
      refine Set.mem_iUnion.2 ⟨hfin.toFinset, fun v hv i => ?_⟩
      by_contra h
      exact hv (hfin.mem_toFinset.2 (Set.mem_iUnion.2 ⟨i, h⟩)))
  refine ⟨T.sup id, fun y hy v hv => ?_⟩
  obtain ⟨S, hS, hyS⟩ := Set.mem_iUnion₂.1 (hT hy)
  exact hyS v fun h => hv (Finset.mem_sup.2 ⟨S, hS, h⟩)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem fin_bd (C : Set (Fin k → Af E)) (hC : IsCompact C) : ∃ B : ℝ, 1 ≤ B ∧ ∀ (g : GA E k) (ξ : Fin k → E), ξ ≠ 0 →
    (fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val) i)) ∈ C →
      ∏ᶠ v, ‖finComp v ((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val)‖ ≤ B := by
  classical
  obtain ⟨S, hS⟩ := exists_finite_fInt hC
  have hfin : ∀ v : HeightOneSpectrum (𝓞 E), ∃ m : ℝ, 1 ≤ m ∧ ∀ y ∈ C, ‖fun i => y i v‖ ≤ m := fun v =>
    exists_one_le_bound hC (f := fun y => ‖fun i => y i v‖)
      (continuous_norm.comp (continuous_pi fun i =>
        (RestrictedProduct.continuous_eval v).comp (continuous_apply i)))
  choose b hb1 hb using hfin
  refine ⟨∏ v ∈ S, b v, by simpa using Finset.prod_le_prod₀ (s := S) (f := fun _ => (1:ℝ)) (fun _ _ => zero_le_one) (fun v _ => hb1 v), fun g ξ hξ hy => ?_⟩
  have hfc := hasFiniteContent_height g hξ
  set y : Fin k → Ad E := (fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val with hy'
  set b' : HeightOneSpectrum (𝓞 E) → ℝ := fun v => if v ∈ S then b v else 1 with hb'
  have hsub : Function.mulSupport b' ⊆ (S : Set _) := fun v hv => by
    by_contra h
    exact hv (by simp only [hb', if_neg (show v ∉ S from h)])
  refine (finprod_le_finprod_of_nonneg hfc.finite_mulSupport ((S.finite_toSet).subset hsub)
    (fun v => norm_nonneg _) fun v => ?_).trans (le_of_eq ?_)
  · simp only [hb']
    split_ifs with hv
    · exact hb v _ hy
    · exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => norm_le_one_of_mem v (hS _ hy v hv i)
  · rw [finprod_eq_prod_of_mulSupport_subset b' hsub]
    exact Finset.prod_congr rfl fun v hv => by simp only [hb', if_pos hv]

theorem norm_pInf (a : Ad E) (w : InfinitePlace E) : ‖pInf E a w‖ = ‖a.1 w‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _

theorem ht_le (C : Set (Fin k → Af E)) (hC : IsCompact C) : ∃ B : ℝ, 0 < B ∧ ∀ (g : GA E k) (ξ : Fin k → E), ξ ≠ 0 →
    (fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val) i)) ∈ C →
      height g ξ ≤ B * ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val) i)‖ ^
        (∑ w : InfinitePlace E, w.mult) := by
  obtain ⟨Bf, hBf, hf⟩ := fin_bd C hC
  refine ⟨Bf * (√k + 1) ^ (∑ w : InfinitePlace E, w.mult), by positivity, fun g ξ hξ hy => ?_⟩
  set y : Fin k → Ad E := (fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val with hy'
  set z := fun i => pInf E (y i) with hz
  have e : height g ξ = adelicNorm y := rfl
  rw [e, adelicNorm]
  have hw : ∀ w : InfinitePlace E, euclidNorm (infComp w y) ≤ (√k + 1) * ‖z‖ := fun w => by
    refine (euclidNorm_le_sqrt_mul _).trans (mul_le_mul (by linarith) ?_ (norm_nonneg _) (by positivity))
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    change ‖(y i).1 w‖ ≤ ‖z‖
    rw [← norm_pInf]
    exact (norm_le_pi_norm (z i) w).trans (norm_le_pi_norm z i)
  have h1 : (∏ w : InfinitePlace E, euclidNorm (infComp w y) ^ w.mult) ≤
      ((√k + 1) * ‖z‖) ^ (∑ w : InfinitePlace E, w.mult) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod₀ (fun w _ => pow_nonneg (euclidNorm_nonneg _) _)
      fun w _ => pow_le_pow_left₀ (euclidNorm_nonneg _) (hw w) _
  have h2 := hf g ξ hξ hy
  have h3 : 0 ≤ ∏ᶠ v, ‖finComp v y‖ := finprod_nonneg fun _ => norm_nonneg _
  calc (∏ w : InfinitePlace E, euclidNorm (infComp w y) ^ w.mult) * ∏ᶠ v, ‖finComp v y‖
      ≤ ((√k + 1) * ‖z‖) ^ (∑ w : InfinitePlace E, w.mult) * Bf :=
        mul_le_mul h1 h2 h3 (by positivity)
    _ = _ := by rw [mul_pow]; ring

end SeparatedThetaSum

namespace SeparatedThetaSum

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ}

theorem real_ineq (ρ : ℝ) (hρ : 0 < ρ) (d k a : ℕ) (hka : k ≤ a) :
    ((ρ ^ d) ^ k)⁻¹ * ((1 + ρ) ^ (d * a))⁻¹ ≤ ((ρ ^ d) ^ a)⁻¹ := by
  have ht : 0 < ρ ^ d := pow_pos hρ d
  have h1 : 1 ≤ (1 + ρ) ^ (d * a) := one_le_pow₀ (by linarith)
  have h2 : (ρ ^ d) ^ a ≤ (1 + ρ) ^ (d * a) := by
    rw [pow_mul]; exact pow_le_pow_left₀ ht.le (pow_le_pow_left₀ hρ.le (by linarith) d) a
  rcases le_total (ρ ^ d) 1 with h | h
  · have h3 : ((ρ ^ d) ^ k)⁻¹ ≤ ((ρ ^ d) ^ a)⁻¹ :=
      inv_anti₀ (pow_pos ht a) (pow_le_pow_of_le_one ht.le h hka)
    have h4 : ((1 + ρ) ^ (d * a))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    calc ((ρ ^ d) ^ k)⁻¹ * ((1 + ρ) ^ (d * a))⁻¹ ≤ ((ρ ^ d) ^ a)⁻¹ * 1 :=
          mul_le_mul h3 h4 (by positivity) (by positivity)
      _ = _ := mul_one _
  · have h3 : ((ρ ^ d) ^ k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ h)
    have h4 : ((1 + ρ) ^ (d * a))⁻¹ ≤ ((ρ ^ d) ^ a)⁻¹ := inv_anti₀ (pow_pos ht a) h2
    calc ((ρ ^ d) ^ k)⁻¹ * ((1 + ρ) ^ (d * a))⁻¹ ≤ 1 * ((ρ ^ d) ^ a)⁻¹ :=
          mul_le_mul h3 h4 (by positivity) zero_le_one
      _ = _ := one_mul _

theorem dim_eq : Module.finrank ℝ (Fin k → Cinf E) = k * ∑ w : InfinitePlace E, w.mult := by
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, IsTotallyComplex.mult_eq]

open Classical in
theorem core {ι X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] (C0 : ℝ)
    (hsep : ∀ ρ : ℝ, 0 < ρ → ∀ P : Finset X, (∀ p ∈ P, ρ ≤ ‖p‖) → (∀ p ∈ P, ∀ q ∈ P, p ≠ q → ρ ≤ ‖p - q‖) →
      ∑ p ∈ P, ((1 + ‖p‖) ^ (Module.finrank ℝ X + 1))⁻¹ ≤ C0 * (ρ ^ Module.finrank ℝ X)⁻¹)
    (z : ι → X) (p : ι → Prop) (ρ : ℝ) (hρ : 0 < ρ) (hn : ∀ i, p i → ρ ≤ ‖z i‖)
    (hs : ∀ i j, p i → p j → i ≠ j → ρ ≤ ‖z i - z j‖) (m : ℕ) :
    ∑' i, ENNReal.ofReal (if p i then ((1 + ‖z i‖) ^ (Module.finrank ℝ X + 1 + m))⁻¹ else 0) ≤
      ENNReal.ofReal (C0 * (ρ ^ Module.finrank ℝ X)⁻¹ * ((1 + ρ) ^ m)⁻¹) := by
  classical
  refine tsum_le_of_sum_le' (by simp) fun s => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by split_ifs <;> positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Finset.sum_filter]
  set t := s.filter p with ht
  have hp : ∀ i ∈ t, p i := fun i hi => (Finset.mem_filter.1 hi).2
  have hinj : Set.InjOn z t := fun i hi j hj hij => by
    by_contra h
    have := hs i j (hp i hi) (hp j hj) h
    rw [hij, sub_self, norm_zero] at this
    linarith
  calc ∑ i ∈ t, ((1 + ‖z i‖) ^ (Module.finrank ℝ X + 1 + m))⁻¹
      ≤ ∑ i ∈ t, ((1 + ‖z i‖) ^ (Module.finrank ℝ X + 1))⁻¹ * ((1 + ρ) ^ m)⁻¹ := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [pow_add, mul_inv]
        have h0 : 0 < 1 + ‖z i‖ := by positivity
        exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity)
          (pow_le_pow_left₀ (by linarith) (by linarith [hn i (hp i hi)]) m)) (by positivity)
    _ = (∑ x ∈ t.image z, ((1 + ‖x‖) ^ (Module.finrank ℝ X + 1))⁻¹) * ((1 + ρ) ^ m)⁻¹ := by
        rw [Finset.sum_image hinj, Finset.sum_mul]
    _ ≤ C0 * (ρ ^ Module.finrank ℝ X)⁻¹ * ((1 + ρ) ^ m)⁻¹ := by
        refine mul_le_mul_of_nonneg_right (hsep ρ hρ _ ?_ ?_) (by positivity)
        · intro x hx
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
          exact hn i (hp i hi)
        · intro x hx y hy hxy
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
          exact hs i j (hp i hi) (hp j hj) fun h => hxy (h ▸ rfl)

end SeparatedThetaSum

theorem theta_bound_holds : ThetaSeriesBound := by
  intro E _ _ _ k Cf hCf a hka
  classical
  set K : Set (Fin k → Af E) := Cf ∪ (fun p : (Fin k → Af E) × (Fin k → Af E) => p.1 - p.2) '' (Cf ×ˢ Cf) with hK
  have hKc : IsCompact K := hCf.union ((hCf.prod hCf).image (continuous_fst.sub continuous_snd))
  obtain ⟨B, hB, hht⟩ := SeparatedThetaSum.ht_le K hKc
  obtain ⟨C0, hC0, hsep⟩ := SeparatedThetaSum.sep_sum (Fin k → Cinf E)
  set d := ∑ w : InfinitePlace E, w.mult with hd
  have hdpos : 0 < d := by rw [hd, InfinitePlace.sum_mult_eq]; exact Module.finrank_pos
  refine ⟨Module.finrank ℝ (Fin k → Cinf E) + 1 + d * a, C0 * B ^ a, fun g r hr hrh => ?_⟩
  set ρ : ℝ := (r / B) ^ ((d : ℝ)⁻¹) with hρdef
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos (div_pos hr hB) _
  have hρd : ρ ^ d = r / B := Real.rpow_inv_natCast_pow (div_pos hr hB).le hdpos.ne'
  have hY : ∀ ξ ξ' : Fin k → E, (fun i => algebraMap E (Ad E) ((ξ - ξ') i)) ᵥ* g.val =
      (fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val - (fun i => algebraMap E (Ad E) (ξ' i)) ᵥ* g.val := by
    intro ξ ξ'
    rw [← sub_vecMul]; congr 1; ext i; simp [map_sub]
  have key : ∀ ξ : Fin k → E, ξ ≠ 0 →
      (fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val) i)) ∈ K →
      ρ ≤ ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val) i)‖ := fun ξ hξ hK => by
    have h1 := (hrh ξ hξ).trans (hht g ξ hξ hK)
    have h2 : ρ ^ d ≤ ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val) i)‖ ^ d := by
      rw [hρd, div_le_iff₀ hB]; linarith
    exact (pow_le_pow_iff_left₀ hρ0.le (norm_nonneg _) hdpos.ne').1 h2
  have hcore := SeparatedThetaSum.core (ι := {ξ : Fin k → E // ξ ≠ 0}) C0 hsep
    (fun ξ => fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i))
    (fun ξ => (fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i)) ∈ Cf) ρ hρ0
    (fun ξ hξ => key ξ.1 ξ.2 (Or.inl hξ))
    (fun ξ ξ' h h' hne => by
      have hne' : ξ.1 - ξ'.1 ≠ 0 := sub_ne_zero.2 fun h => hne (Subtype.ext h)
      have := key (ξ.1 - ξ'.1) hne' (Or.inr ⟨(_, _), ⟨h, h'⟩, by
        simp only [hY]; ext i; simp [map_sub]⟩)
      refine this.trans_eq (congrArg norm ?_)
      rw [hY]; ext i; simp [map_sub]) (d * a)
  refine le_trans ?_ (hcore.trans (ENNReal.ofReal_le_ofReal ?_))
  · refine le_of_eq (tsum_congr fun ξ => ?_)
    simp only [Set.indicator_apply]
  · rw [SeparatedThetaSum.dim_eq, ← hd, mul_comm k d, pow_mul]
    have h := SeparatedThetaSum.real_ineq ρ hρ0 d k a hka
    have e : ((ρ ^ d) ^ a)⁻¹ = B ^ a * (r ^ a)⁻¹ := by rw [hρd, div_pow, inv_div, div_eq_mul_inv]
    rw [e] at h
    calc _ = C0 * (((ρ ^ d) ^ k)⁻¹ * ((1 + ρ) ^ (d * a))⁻¹) := by ring
      _ ≤ C0 * (B ^ a * (r ^ a)⁻¹) := mul_le_mul_of_nonneg_left h hC0
      _ = _ := by ring

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.TableDegreeOneUnipotent
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace tableDegreeOneUnipotent

theorem mul_le_sq_add (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := by gcongr
      _ = b ^ 2 := (sq b).symm
      _ ≤ _ := le_add_self
  · calc a * b ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ _ := le_self_add

theorem integ {X : Type} [MeasurableSpace X] {ν : Measure X} {f φ : X → ℂ}
    (hf : AEStronglyMeasurable f ν) (hφ : AEStronglyMeasurable φ ν)
    (h1 : ∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν < ∞) (h2 : ∫⁻ g, ‖φ g‖ₑ ^ 2 ∂ν < ∞) :
    Integrable (fun g => f g * conj (φ g)) ν := by
  refine ⟨hf.mul (Complex.continuous_conj.comp_aestronglyMeasurable hφ), ?_⟩
  show ∫⁻ g, ‖f g * conj (φ g)‖ₑ ∂ν < ∞
  calc ∫⁻ g, ‖f g * conj (φ g)‖ₑ ∂ν ≤ ∫⁻ g, (‖f g‖ₑ ^ 2 + ‖φ g‖ₑ ^ 2) ∂ν := by
        refine lintegral_mono fun g => ?_
        have hc : ‖conj (φ g)‖ₑ = ‖φ g‖ₑ := by simp [enorm_eq_nnnorm]
        rw [enorm_mul, hc]
        exact mul_le_sq_add _ _
    _ = ∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν + ∫⁻ g, ‖φ g‖ₑ ^ 2 ∂ν := lintegral_add_left' (hf.enorm.pow_const 2) _
    _ < ∞ := ENNReal.add_lt_top.2 ⟨h1, h2⟩

theorem pre_of_good {E : Type} [Field E] [NumberField E] {k : ℕ} {ψ : AddChar (Ad E) ℂ} {m : ℕ}
    {f : GA E k → ℂ} (h : Good ψ m f) : Pre ψ m f :=
  ⟨h.cont, h.left, h.law⟩

theorem main (hU1 : U1) (hP1 : P1) (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (k : ℕ)
    (μ : Measure (GA E k)) [μ.IsHaarMeasure] (ψ : AddChar (Ad E) ℂ) (hψ : StdPsi ψ) :
    ∀ m, m < k → ∀ β, IsWt (nuP E k m) β → ∃ β', IsWt (nuP E k 0) β' ∧
      ∀ f φ, Pre ψ m f → Good ψ m φ → ∫⁻ g, ‖f g‖ₑ ^ 2 ∂μ.withDensity β < ∞ →
        ∫⁻ g, ‖φ g‖ₑ ^ 2 ∂μ.withDensity β < ∞ →
        Integrable (fun g => whit ψ m f g * conj (whit ψ m φ g)) (μ.withDensity β') ∧
        ∫ g, f g * conj (φ g) ∂μ.withDensity β = ∫ g, whit ψ m f g * conj (whit ψ m φ g) ∂μ.withDensity β' := by
  intro m
  induction m with
  | zero =>
    intro _ β hβ
    refine ⟨β, hβ, fun f φ hf hφ h1 h2 => ⟨?_, rfl⟩⟩
    exact integ hf.cont.aestronglyMeasurable (pre_of_good hφ).cont.aestronglyMeasurable h1 h2
  | succ m ih =>
    intro hm β hβ
    obtain ⟨β1, hβ1, hL2, hip⟩ := hU1 E k μ ψ hψ (m + 1) (by omega) hm β hβ
    obtain ⟨β', hβ', h⟩ := ih (by omega) β1 hβ1
    refine ⟨β', hβ', fun f φ hf hφ h1 h2 => ?_⟩
    have hf' : Pre ψ m (colT ψ (m + 1) f) := (hP1 E k ψ hψ (m + 1) (by omega) hm f hf).1
    have hφ' : Good ψ m (colT ψ (m + 1) φ) := by
      refine { cont := ?_, left := ?_, law := ?_, van := ?_ }
      · exact _root_.GlobalTheory.CuspGeneric.continuous_colT_good E k ψ hψ m φ hφ
      · exact _root_.GlobalTheory.CuspGeneric.colT_isMir_invariant E k ψ hψ m φ hm hφ
      · intro j hj y g
        rcases Nat.lt_or_ge (m + 1) j with h | h
        · exact _root_.GlobalTheory.T.columnWhittakerTransform_keeps_later_law E k ψ m φ hφ j h y g
        · obtain rfl : j = m + 1 := by omega
          exact _root_.GlobalTheory.CuspGeneric.colT_blkU_mul E k ψ hψ m φ hφ y g
      · exact _root_.GlobalTheory.CuspGeneric.avg_colT_blk_eq_zero E k ψ hψ m φ hm hφ
    obtain ⟨hi, he⟩ := h _ _ hf' hφ' ((hL2 f hf).trans_lt h1) ((hL2 φ (pre_of_good hφ)).trans_lt h2)
    exact ⟨hi, (hip f φ hf hφ h1 h2).trans he⟩

end tableDegreeOneUnipotent

theorem unitaryGroupGeometricSide_of_quotient_identities : U1 → P1 → U2 := by
  intro hU1 hP1 E _ _ _ k μ _ ψ hψ
  exact tableDegreeOneUnipotent.main hU1 hP1 E k μ ψ hψ

end PositivityTheory.AdelicQuotientData

end
end

