module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.RSubPowApply
section
namespace UpperTheory.Esk.CommutingOperatorTraces

open Module Module.End

variable {J V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

noncomputable def E (T : J → Module.End ℂ V) (s : J → ℂ) : Submodule ℂ V :=
  ⨅ j, (T j).maxGenEigenspace (s j)

lemma mapsTo_E (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (i : J) : Set.MapsTo (T i) (E T s) (E T s) := by
  intro x hx
  simp only [E, SetLike.mem_coe, Submodule.mem_iInf] at hx ⊢
  intro j
  exact Module.End.mapsTo_maxGenEigenspace_of_comm (hT j i) (s j) (hx j)

lemma mapsTo_prod (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (W : List J) : Set.MapsTo (W.map T).prod (E T s) (E T s) := by
  induction W with
  | nil => intro x hx; simpa using hx
  | cons a W ih =>
    intro x hx
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    exact mapsTo_E T hT s a (ih hx)

noncomputable def R (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (j : J) : Module.End ℂ (E T s) :=
  (T j).restrict (mapsTo_E T hT s j)

lemma R_apply (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (j : J) (x : E T s) : ((R T hT s j x : E T s) : V) = T j x := rfl

lemma R_comm (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (i j : J) : Commute (R T hT s i) (R T hT s j) := by
  show R T hT s i * R T hT s j = R T hT s j * R T hT s i
  refine LinearMap.ext fun x => Subtype.ext ?_
  simp only [Module.End.mul_apply, R_apply]
  exact LinearMap.congr_fun (hT i j) x

lemma R_prod_apply (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (W : List J) (x : E T s) : (((W.map (R T hT s)).prod x : E T s) : V) = (W.map T).prod x := by
  induction W with
  | nil => simp
  | cons a W ih => simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, R_apply, ih]

lemma R_sub_pow_apply (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i)
    (s : J → ℂ) (j : J) (n : ℕ) (x : E T s) :
    ((((R T hT s j - algebraMap ℂ _ (s j)) ^ n) x : E T s) : V) = ((T j - s j • 1) ^ n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
    rw [← ih]
    simp [R_apply, Algebra.algebraMap_eq_smul_one]

lemma R_nil (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ) (j : J) :
    IsNilpotent (R T hT s j - algebraMap ℂ _ (s j)) := by
  rw [Module.End.isNilpotent_iff_of_finite]
  intro x
  have hx := x.2
  simp only [E] at hx
  obtain ⟨k, hk⟩ := (Module.End.mem_iInf_maxGenEigenspace_iff T s (x : V)).mp hx j
  refine ⟨k, Subtype.ext ?_⟩
  rw [R_sub_pow_apply, hk]
  rfl

lemma trace_R_prod (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (W : List J) : LinearMap.trace ℂ (E T s) (W.map (R T hT s)).prod =
      (Module.finrank ℂ (E T s) : ℂ) * (W.map s).prod := by
  induction W with
  | nil => simp [LinearMap.trace_one]
  | cons a W ih =>
    have hc : Commute (W.map (R T hT s)).prod (R T hT s a) := by
      apply Commute.list_prod_left
      intro y hy
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp hy
      exact R_comm T hT s b a
    simp only [List.map_cons, List.prod_cons]
    rw [← hc.eq, Module.End.mul_eq_comp,
      LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent (s a) hc (R_nil T hT s a), ih]
    ring

lemma trace_restrict (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (W : List J) (h : Set.MapsTo (W.map T).prod (E T s) (E T s)) :
    LinearMap.trace ℂ (E T s) ((W.map T).prod.restrict h) =
      (Module.finrank ℂ (E T s) : ℂ) * (W.map s).prod := by
  have : (W.map T).prod.restrict h = (W.map (R T hT s)).prod := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    rw [R_prod_apply]
    rfl
  rw [this, trace_R_prod]

lemma exists_eigvec (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (hs : E T s ≠ ⊥) : ∃ f : V, f ≠ 0 ∧ ∀ j, T j f = s j • f := by
  classical
  let P : Set (Submodule ℂ V) :=
    {U | U ≠ ⊥ ∧ U ≤ E T s ∧ ∀ j, ∀ x ∈ U, T j x ∈ U}
  have hP : (E T s) ∈ P := ⟨hs, le_rfl, fun j x hx => mapsTo_E T hT s j hx⟩
  obtain ⟨U, ⟨hU0, hUE, hUT⟩, hmin⟩ := (wellFounded_lt (α := Submodule ℂ V)).has_min P ⟨_, hP⟩
  obtain ⟨x, hxU, hx0⟩ := (Submodule.ne_bot_iff U).mp hU0
  refine ⟨x, hx0, fun j => ?_⟩

  have hsub : ∀ n : ℕ, ∀ y ∈ U, ((T j - s j • 1) ^ n) y ∈ U := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih =>
      intro y hy
      rw [pow_succ', Module.End.mul_apply]
      have h1 := ih y hy
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact U.sub_mem (hUT j _ h1) (U.smul_mem _ h1)
  let U' : Submodule ℂ V := U ⊓ (T j).eigenspace (s j)
  have hU'P : U' ∈ P := by
    refine ⟨?_, inf_le_left.trans hUE, ?_⟩
    · have hxE : x ∈ E T s := hUE hxU
      simp only [E] at hxE
      have hex := (Module.End.mem_iInf_maxGenEigenspace_iff T s x).mp hxE j
      let k := Nat.find hex
      have hk : ((T j - s j • 1) ^ k) x = 0 := Nat.find_spec hex
      have hk0 : k ≠ 0 := by
        intro h0
        rw [h0, pow_zero, Module.End.one_apply] at hk
        exact hx0 hk
      obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      have hne : ((T j - s j • 1) ^ k') x ≠ 0 := by
        have := Nat.find_min hex (show k' < k by omega)
        exact this
      rw [Submodule.ne_bot_iff]
      refine ⟨((T j - s j • 1) ^ k') x, ⟨hsub k' x hxU, ?_⟩, hne⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      have h2 : ((T j - s j • 1) ^ k) x = 0 := hk
      rw [hk', pow_succ', Module.End.mul_apply] at h2
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at h2
      exact sub_eq_zero.mp h2
    · intro i y hy
      refine ⟨hUT i y hy.1, ?_⟩
      have hy2 : T j y = s j • y := (Module.End.mem_eigenspace_iff).mp hy.2
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      have := LinearMap.congr_fun (hT j i) y
      simp only [Module.End.mul_apply] at this
      rw [this, hy2, map_smul]
  have hle : U' ≤ U := inf_le_left
  have hUU : U' = U := by
    by_contra hne
    exact hmin U' hU'P (lt_of_le_of_ne hle hne)
  have hxU' : x ∈ U' := hUU ▸ hxU
  exact (Module.End.mem_eigenspace_iff).mp hxU'.2

end UpperTheory.Esk.CommutingOperatorTraces

open UpperTheory.Esk.CommutingOperatorTraces in
theorem UpperTheory.Esk.pf_Sys : UpperTheory.Esk.Sys := by
  intro J V _ _ _ T hT
  classical
  have hind : iSupIndep (E T) :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo T
      (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hT j i) φ)
  have htop : ⨆ s, E T s = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute T
      (fun i j _ => hT i j) (fun i => Module.End.iSup_maxGenEigenspace_eq_top (T i))
  have hfin : {s | E T s ≠ ⊥}.Finite := WellFoundedGT.finite_ne_bot_of_iSupIndep hind
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  have htr : ∀ W : List J, LinearMap.trace ℂ V (W.map T).prod =
      ∑ s ∈ hfin.toFinset, (Module.finrank ℂ (E T s) : ℂ) * (W.map s).prod := by
    intro W
    rw [LinearMap.trace_eq_sum_trace_restrict' hint hfin (mapsTo_prod T hT · W)]
    exact Finset.sum_congr rfl fun s _ => trace_restrict T hT s W _
  refine ⟨hfin.toFinset, fun s => Module.finrank ℂ (E T s), ?_, ?_, ?_, htr⟩
  · intro s
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · exact exists_eigvec T hT s
    · rintro ⟨f, hf0, hf⟩ hbot
      have hfE : f ∈ E T s := by
        simp only [E, Submodule.mem_iInf]
        intro j
        apply Module.End.eigenspace_le_maxGenEigenspace
        exact (Module.End.mem_eigenspace_iff).mpr (hf j)
      rw [hbot, Submodule.mem_bot] at hfE
      exact hf0 hfE
  · intro s hs
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hs
    exact Submodule.one_le_finrank_iff.mpr hs
  · have h0 := htr []
    simp only [List.map_nil, List.prod_nil, LinearMap.trace_one, mul_one] at h0
    exact_mod_cast h0.symm
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.RadialIntegralUnitCircleEq
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.RadialIntegralLemmas
open UpperTheory.Esk

theorem one_sub_ne (ζ : ℂ) (hζ : ‖ζ‖ = 1) (hζ1 : ζ ≠ 1) (r : ℝ) : 1 - ζ * (r : ℂ) ^ 2 ≠ 0 := by
  intro h
  have h1 : ζ * (r : ℂ) ^ 2 = 1 := by linear_combination -h
  have h2 : ‖ζ * (r : ℂ) ^ 2‖ = 1 := by rw [h1, norm_one]
  rw [norm_mul, hζ, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h2
  have h3 : (r : ℂ) ^ 2 = 1 := by exact_mod_cast h2
  apply hζ1
  rw [h3, mul_one] at h1
  exact h1

theorem radial_integral_unit_circle_eq (n : ℕ) (K ζ : ℂ) (hζ : ‖ζ‖ = 1) (hζ1 : ζ ≠ 1) :
    ∫ r in (0 : ℝ)..1, K * (4 * (r : ℂ) * (1 - (r : ℂ) ^ 2) ^ n / (1 - ζ * (r : ℂ) ^ 2) ^ (n + 2))
      = K * (2 / (((n : ℂ) + 1) * (1 - ζ))) := by
  have hne := one_sub_ne ζ hζ hζ1
  have hζ1' : ζ - 1 ≠ 0 := sub_ne_zero.2 hζ1
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  set G : ℝ → ℂ := fun r => K * (2 / (((n : ℂ) + 1) * (ζ - 1))) *
    ((1 - (r : ℂ) ^ 2) / (1 - ζ * (r : ℂ) ^ 2)) ^ (n + 1) with hG
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt G
      (K * (4 * (x : ℂ) * (1 - (x : ℂ) ^ 2) ^ n / (1 - ζ * (x : ℂ) ^ 2) ^ (n + 2))) x := by
    intro x _
    have h1 : HasDerivAt (fun w : ℂ => 1 - w ^ 2) (-(2 * (x : ℂ))) (x : ℂ) := by
      simpa using ((hasDerivAt_pow 2 (x : ℂ)).const_sub 1)
    have h2 : HasDerivAt (fun w : ℂ => 1 - ζ * w ^ 2) (-(ζ * (2 * (x : ℂ)))) (x : ℂ) := by
      simpa using (((hasDerivAt_pow 2 (x : ℂ)).const_mul ζ).const_sub 1)
    have h3 := ((h1.div h2 (hne x)).pow (n + 1)).const_mul (K * (2 / (((n : ℂ) + 1) * (ζ - 1))))
    have h5 : HasDerivAt G _ x := h3.comp_ofReal
    refine h5.congr_deriv ?_
    have e := hne x
    simp only [Pi.div_apply, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, div_pow]
    field_simp
    ring
  have hcont : ContinuousOn (fun x : ℝ => K * (4 * (x : ℂ) * (1 - (x : ℂ) ^ 2) ^ n / (1 - ζ * (x : ℂ) ^ 2) ^ (n + 2)))
      (Set.uIcc 0 1) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div₀ (by fun_prop) (by fun_prop)
    intro x _
    exact pow_ne_zero _ (hne x)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp only [hG]
  push_cast
  have e0 : (1 : ℂ) - ζ * 0 ^ 2 = 1 := by ring
  simp only [one_pow, sub_self, zero_div, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    not_false_eq_true, zero_pow, mul_zero, zero_sub]
  field_simp
  ring

theorem rad_int (k : ℕ) (hk : 2 ≤ k) (c η ζ : ℂ) (hζ : ‖ζ‖ = 1) (hζ1 : ζ ≠ 1) :
    ∫ p in Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi, ((4 * p.1 / (1 - p.1 ^ 2) ^ 2 : ℝ) : ℂ) *
      (c * (η * (1 - (p.1 : ℂ) ^ 2) / (1 - ζ * (p.1 : ℂ) ^ 2)) ^ k)
      = c * η ^ k * (4 * Real.pi / (((k : ℂ) - 1) * (1 - ζ))) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  have hne := one_sub_ne ζ hζ hζ1
  have e1 := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun r : ℝ => ((4 * r / (1 - r ^ 2) ^ 2 : ℝ) : ℂ) * (c * (η * (1 - (r : ℂ) ^ 2) / (1 - ζ * (r : ℂ) ^ 2)) ^ (n + 2)))
    (fun _ : ℝ => (1 : ℂ)) (Set.Ioo 0 1) (Set.Ioo (-Real.pi) Real.pi)
  simp only [mul_one] at e1
  rw [Measure.volume_eq_prod, e1]
  rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
  have e2 : ∫ r in Set.Ioo (0 : ℝ) 1, ((4 * r / (1 - r ^ 2) ^ 2 : ℝ) : ℂ) *
      (c * (η * (1 - (r : ℂ) ^ 2) / (1 - ζ * (r : ℂ) ^ 2)) ^ (n + 2)) =
      ∫ r in Set.Ioo (0 : ℝ) 1, (c * η ^ (n + 2)) *
        (4 * (r : ℂ) * (1 - (r : ℂ) ^ 2) ^ n / (1 - ζ * (r : ℂ) ^ 2) ^ (n + 2)) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    have h1 : (1 - (r : ℂ) ^ 2) ≠ 0 := by
      have : (1 - r ^ 2 : ℝ) ≠ 0 := by nlinarith [hr.1, hr.2]
      exact_mod_cast this
    have h2 := hne r
    simp only []
    push_cast
    rw [div_pow, mul_pow]
    field_simp
    ring
  rw [e2, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    radial_integral_unit_circle_eq n _ ζ hζ hζ1]
  have hζ1' : 1 - ζ ≠ 0 := sub_ne_zero.2 (Ne.symm hζ1)
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  rw [show (n : ℂ) + 2 - 1 = n + 1 by ring]
  simp only [Complex.real_smul]
  push_cast
  field_simp
  ring

end UpperTheory.Esk.RadialIntegralLemmas
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.UpperHalfPlaneCoordinatesProof
section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UpperTheory.Esk.UpperHalfPlaneCoordinates

def Ψ (x y : ℝ) : ℂ := (y : ℂ) * (x + Complex.I)

theorem cont_Ψ : Continuous (fun p : ℝ × ℝ => Ψ p.1 p.2) := by
  unfold Ψ; fun_prop

theorem key (G : ℂ → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x, ∫⁻ y, ENNReal.ofReal (1 / |y|) * G (Ψ x y)
      = ∫⁻ z, ENNReal.ofReal (1 / z.im ^ 2) * G z := by
  have hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (1 / |p.2|) * G (Ψ p.1 p.2)) := by
    refine Measurable.mul ?_ (hG.comp cont_Ψ.measurable)
    exact ENNReal.measurable_ofReal.comp (by fun_prop)
  rw [lintegral_lintegral_swap hm.aemeasurable]
  have hF : Measurable (fun z : ℂ => ENNReal.ofReal (1 / z.im ^ 2) * G z) := by
    refine Measurable.mul ?_ hG
    exact ENNReal.measurable_ofReal.comp (by fun_prop)
  have hR : ∫⁻ z, ENNReal.ofReal (1 / z.im ^ 2) * G z
      = ∫⁻ y : ℝ, ∫⁻ u : ℝ, ENNReal.ofReal (1 / y ^ 2) * G ((u : ℂ) + y * Complex.I) := by
    rw [← (Complex.volume_preserving_equiv_real_prod.symm).lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _)]
    rw [Measure.volume_eq_prod, lintegral_prod_symm]
    · congr 1; funext y; congr 1; funext u
      simp only [Complex.measurableEquivRealProd]
      congr 2
      exact Complex.mk_eq_add_mul_I u y
    · exact (hF.comp (MeasurableEquiv.measurable _)).aemeasurable
  rw [hR]
  congr 1; funext y
  have hmx : Measurable (fun x : ℝ => G (Ψ x y)) :=
    hG.comp (cont_Ψ.comp (Continuous.prodMk continuous_id continuous_const)).measurable
  rw [lintegral_const_mul _ hmx]
  have hmu : Measurable (fun u : ℝ => G ((u : ℂ) + y * Complex.I)) :=
    hG.comp (by fun_prop : Continuous (fun u : ℝ => (u : ℂ) + y * Complex.I)).measurable
  rw [lintegral_const_mul _ hmu]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have hsc : ∫⁻ x, G (Ψ x y) = ENNReal.ofReal |y⁻¹| * ∫⁻ u : ℝ, G ((u : ℂ) + y * Complex.I) := by
      calc ∫⁻ x, G (Ψ x y) = ∫⁻ x : ℝ, G (((y * x : ℝ) : ℂ) + y * Complex.I) := by
            congr 1; funext x; congr 1; simp only [Ψ]; push_cast; ring
        _ = ∫⁻ u : ℝ, G ((u : ℂ) + y * Complex.I) ∂(Measure.map (fun x => y * x) volume) :=
            (lintegral_map hmu (measurable_const_mul y)).symm
        _ = _ := by rw [Real.map_volume_mul_left hy, lintegral_smul_measure, smul_eq_mul]
    rw [hsc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    rw [show 1 / |y| * |y⁻¹| = 1 / y ^ 2 by
      rw [abs_inv, one_div, one_div, ← mul_inv, ← pow_two, sq_abs]]

def ν0 : Measure P := Measure.comap Subtype.val volume

theorem vol_eq : (volume : Measure P) = ν0.withDensity (fun z => ENNReal.ofReal (1 / z.1.im ^ 2)) := rfl

theorem hS : MeasurableSet {z : ℂ | z.im ≠ 0} :=
  (isOpen_ne_fun Complex.continuous_im continuous_const).measurableSet

theorem cont_pt : Continuous (fun p : ℝ × {y : ℝ // y ≠ 0} => pt p.1 p.2.1 p.2.2) := by
  unfold pt
  exact Continuous.subtype_mk (by fun_prop) _

theorem meas_pres : MeasurePreserving (fun p : ℝ × {y : ℝ // y ≠ 0} => pt p.1 p.2.1 p.2.2)
    ((volume : Measure ℝ).prod ((Measure.comap Subtype.val volume).withDensity
      fun y => ENNReal.ofReal (1 / |y.1|))) volume := by
  have hemb : MeasurableEmbedding (Subtype.val : P → ℂ) := MeasurableEmbedding.subtype_coe hS
  have hY : MeasurableSet {y : ℝ | y ≠ 0} := (measurableSet_singleton 0).compl
  have hembY : MeasurableEmbedding (Subtype.val : {y : ℝ // y ≠ 0} → ℝ) := MeasurableEmbedding.subtype_coe hY
  have : SigmaFinite (Measure.comap (Subtype.val : {y : ℝ // y ≠ 0} → ℝ) volume) :=
    SigmaFinite.of_map _ measurable_subtype_coe.aemeasurable (by rw [hembY.map_comap]; infer_instance)
  refine ⟨cont_pt.measurable, ?_⟩
  ext s hs
  set G : ℂ → ℝ≥0∞ := (Subtype.val '' s).indicator 1 with hGdef
  have hGm : Measurable G := measurable_one.indicator (hemb.measurableSet_image.2 hs)
  have hGv : ∀ z : P, G z.1 = s.indicator 1 z := by
    intro z
    have hz : z.1 ∈ Subtype.val '' s ↔ z ∈ s :=
      ⟨fun ⟨w, hw, e⟩ => (Subtype.ext e : w = z) ▸ hw, fun h => ⟨z, h, rfl⟩⟩
    rw [hGdef]
    by_cases h : z ∈ s
    · rw [Set.indicator_of_mem (hz.2 h), Set.indicator_of_mem h]; rfl
    · rw [Set.indicator_of_notMem (mt hz.1 h), Set.indicator_of_notMem h]
  rw [Measure.map_apply cont_pt.measurable hs, ← lintegral_indicator_one (cont_pt.measurable hs)]
  have e1 : ∀ p : ℝ × {y : ℝ // y ≠ 0},
      ((fun p : ℝ × {y : ℝ // y ≠ 0} => pt p.1 p.2.1 p.2.2) ⁻¹' s).indicator 1 p = G (Ψ p.1 p.2.1) := by
    intro p
    rw [show Ψ p.1 p.2.1 = (pt p.1 p.2.1 p.2.2).1 from rfl, hGv]
    rfl
  simp_rw [e1]
  have hGΨ : Measurable (fun p : ℝ × {y : ℝ // y ≠ 0} => G (Ψ p.1 p.2.1)) :=
    hGm.comp (cont_Ψ.comp (Continuous.prodMk continuous_fst
      (continuous_subtype_val.comp continuous_snd))).measurable
  rw [lintegral_prod _ hGΨ.aemeasurable]
  have e2 : ∀ x : ℝ, ∫⁻ y, G (Ψ x y.1) ∂((Measure.comap Subtype.val volume).withDensity
      fun y : {y : ℝ // y ≠ 0} => ENNReal.ofReal (1 / |y.1|))
      = ∫⁻ y, ENNReal.ofReal (1 / |y|) * G (Ψ x y) := by
    intro x
    have hd : Measurable (fun y : {y : ℝ // y ≠ 0} => ENNReal.ofReal (1 / |y.1|)) :=
      (by fun_prop : Measurable (fun y : ℝ => ENNReal.ofReal (1 / |y|))).comp measurable_subtype_coe
    have hg : Measurable (fun y : {y : ℝ // y ≠ 0} => G (Ψ x y.1)) :=
      hGm.comp (cont_Ψ.comp (Continuous.prodMk continuous_const continuous_subtype_val)).measurable
    rw [lintegral_withDensity_eq_lintegral_mul _ hd hg]
    have := lintegral_subtype_comap (μ := (volume : Measure ℝ)) hY
      (fun y => ENNReal.ofReal (1 / |y|) * G (Ψ x y))
    rw [show ({y : ℝ | y ≠ 0} : Set ℝ) = {0}ᶜ from rfl, restrict_compl_singleton] at this
    exact this
  simp_rw [e2]
  rw [key G hGm]
  have hv : (volume : Measure P) s = ∫⁻ z : P, ENNReal.ofReal (1 / z.1.im ^ 2) * G z.1 ∂ν0 := by
    rw [vol_eq, withDensity_apply _ hs, ← lintegral_indicator hs]
    congr 1; funext z
    rw [hGv]; by_cases h : z ∈ s <;> simp [Set.indicator, h]
  have hv2 : ∫⁻ z : P, ENNReal.ofReal (1 / z.1.im ^ 2) * G z.1 ∂ν0
      = ∫⁻ z in {z : ℂ | z.im ≠ 0}, ENNReal.ofReal (1 / z.im ^ 2) * G z :=
    lintegral_subtype_comap hS (fun z => ENNReal.ofReal (1 / z.im ^ 2) * G z)
  rw [hv, hv2, ← lintegral_indicator hS]
  congr 1; funext z
  by_cases h : z.im ≠ 0
  · simp [Set.indicator, h]
  · simp [Set.indicator, not_not.1 h]

theorem bij : Function.Bijective (fun p : ℝ × {y : ℝ // y ≠ 0} => pt p.1 p.2.1 p.2.2) := by
  constructor
  · rintro ⟨x, y, hy⟩ ⟨x', y', hy'⟩ h
    have h' : (y : ℂ) * (x + Complex.I) = (y' : ℂ) * (x' + Complex.I) := congrArg Subtype.val h
    have him := congrArg Complex.im h'
    have hre := congrArg Complex.re h'
    simp at him hre
    subst him
    have : x = x' := mul_left_cancel₀ hy hre
    subst this; rfl
  · rintro ⟨z, hz⟩
    refine ⟨(z.re / z.im, ⟨z.im, hz⟩), ?_⟩
    apply Subtype.ext
    show (z.im : ℂ) * ((z.re / z.im : ℝ) + Complex.I) = z
    apply Complex.ext <;> simp; field_simp

end UpperTheory.Esk.UpperHalfPlaneCoordinates

theorem UpperTheory.Esk.upper_half_plane_measure_coordinates : UpperTheory.Esk.UpperHalfPlaneMeasureCoordinates :=
  ⟨UpperTheory.Esk.UpperHalfPlaneCoordinates.meas_pres, UpperTheory.Esk.UpperHalfPlaneCoordinates.bij, UpperTheory.Esk.UpperHalfPlaneCoordinates.cont_pt⟩
end
end

