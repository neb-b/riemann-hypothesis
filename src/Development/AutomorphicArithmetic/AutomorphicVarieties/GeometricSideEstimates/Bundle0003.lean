module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0002
public import GroundTheory.GlobalFields.TateThesis.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.AdmissibleFunctionClassClosureProperties
section
open UpperTheory.V.Lit.Geo
open scoped ContDiff

section aux

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

private def pA (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] : Subalgebra ℂ (V → ℂ) :=
  Algebra.adjoin ℂ (Set.range fun l : V →ₗ[ℝ] ℂ => (l : V → ℂ))

omit [FiniteDimensional ℝ V] in
private theorem lin_mem (l : V →ₗ[ℝ] ℂ) : (l : V → ℂ) ∈ pA V :=
  Algebra.subset_adjoin ⟨l, rfl⟩

omit [FiniteDimensional ℝ V] in
private theorem const_mem (c : ℂ) : (fun _ : V => c) ∈ pA V :=
  (pA V).algebraMap_mem c

private theorem pA_smooth {P : V → ℂ} (hP : P ∈ pA V) : ContDiff ℝ ∞ P := by
  induction hP using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨l, rfl⟩ := hf
    exact (LinearMap.toContinuousLinearMap l).contDiff
  | algebraMap c => exact contDiff_const (c := c)
  | add f g _ _ hf hg => exact hf.add hg
  | mul f g _ _ hf hg => exact hf.mul hg

omit [FiniteDimensional ℝ V] in
private theorem pA_comp (T : V →ₗ[ℝ] V) {P : V → ℂ} (hP : P ∈ pA V) : (fun x => P (T x)) ∈ pA V := by
  induction hP using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨l, rfl⟩ := hf
    exact lin_mem (l.comp T)
  | algebraMap c => exact const_mem c
  | add f g _ _ hf hg => exact (pA V).add_mem hf hg
  | mul f g _ _ hf hg => exact (pA V).mul_mem hf hg

private theorem pA_der (F : V → V) (hF : ∀ l : V →ₗ[ℝ] ℂ, (fun x => l (F x)) ∈ pA V) {P : V → ℂ}
    (hP : P ∈ pA V) : (fun x => fderiv ℝ P x (F x)) ∈ pA V := by
  induction hP using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨l, rfl⟩ := hf
    have h : (fun x => fderiv ℝ (l : V → ℂ) x (F x)) = fun x => l (F x) := by
      funext x
      have := (LinearMap.toContinuousLinearMap l).fderiv (x := x)
      exact congrArg (fun L : V →L[ℝ] ℂ => L (F x)) this
    exact h ▸ hF l
  | algebraMap c =>
    have h : (fun x => fderiv ℝ (algebraMap ℂ (V → ℂ) c) x (F x)) = fun _ => 0 := by
      funext x
      have : fderiv ℝ (algebraMap ℂ (V → ℂ) c) x = 0 := fderiv_const_apply c
      rw [this]; rfl
    rw [h]
    exact const_mem 0
  | add f g hf' hg' hf hg =>
    have df := (pA_smooth hf').differentiable (by simp)
    have dg := (pA_smooth hg').differentiable (by simp)
    have h : (fun x => fderiv ℝ (f + g) x (F x)) =
        (fun x => fderiv ℝ f x (F x)) + fun x => fderiv ℝ g x (F x) := by
      funext x
      rw [fderiv_add (df x) (dg x)]
      rfl
    rw [h]
    exact (pA V).add_mem hf hg
  | mul f g hf' hg' hf hg =>
    have df := (pA_smooth hf').differentiable (by simp)
    have dg := (pA_smooth hg').differentiable (by simp)
    have h : (fun x => fderiv ℝ (f * g) x (F x)) =
        f * (fun x => fderiv ℝ g x (F x)) + g * fun x => fderiv ℝ f x (F x) := by
      funext x
      rw [fderiv_mul (df x) (dg x)]
      simp
    rw [h]
    exact (pA V).add_mem ((pA V).mul_mem hf' hg) ((pA V).mul_mem hg' hf)

private theorem pA_bd (q : V → ℝ) (hq : ∀ x, ‖x‖ ^ 2 ≤ q x) {P : V → ℂ} (hP : P ∈ pA V) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ x, ‖P x‖ ≤ C * (1 + q x) ^ k := by
  have h1 : ∀ x, 1 ≤ 1 + q x := fun x => by nlinarith [hq x, sq_nonneg ‖x‖]
  induction hP using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨l, rfl⟩ := hf
    refine ⟨‖LinearMap.toContinuousLinearMap l‖, 1, norm_nonneg _, fun x => ?_⟩
    refine ((LinearMap.toContinuousLinearMap l).le_opNorm x).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [pow_one]
    nlinarith [hq x, sq_nonneg (‖x‖ - 1), sq_nonneg ‖x‖]
  | algebraMap c =>
    refine ⟨‖c‖, 0, norm_nonneg _, fun x => ?_⟩
    rw [pow_zero, mul_one]
    exact le_rfl
  | add f g _ _ hf hg =>
    obtain ⟨C, k, hC, hf⟩ := hf
    obtain ⟨D, m, hD, hg⟩ := hg
    refine ⟨C + D, k + m, add_nonneg hC hD, fun x => ?_⟩
    refine (norm_add_le _ _).trans ?_
    rw [add_mul]
    refine add_le_add ((hf x).trans ?_) ((hg x).trans ?_)
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (h1 x) (Nat.le_add_right _ _)) hC
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (h1 x) (Nat.le_add_left _ _)) hD
  | mul f g _ _ hf hg =>
    obtain ⟨C, k, hC, hf⟩ := hf
    obtain ⟨D, m, hD, hg⟩ := hg
    refine ⟨C * D, k + m, mul_nonneg hC hD, fun x => ?_⟩
    rw [Pi.mul_apply, norm_mul, pow_add, mul_mul_mul_comm]
    exact mul_le_mul (hf x) (hg x) (norm_nonneg _) ((norm_nonneg _).trans (hf x))

end aux

theorem UpperTheory.admissibleFunctionClass_closure_properties :
    PolyBd := by
  intro E _ _ a P hP
  have hq := fun x => ((UpperTheory.geometric_side_quadraticForm_identity E a).2.2.2.2.2 x).1
  refine ⟨pA_smooth hP, ?_, fun T => ⟨?_, pA_comp T hP, fun u => ?_⟩⟩
  · obtain ⟨C, k, _, h⟩ := pA_bd qf hq hP
    exact ⟨C, k, h⟩
  · exact pA_der T (fun l => lin_mem (l.comp T)) hP
  · exact pA_der (fun _ => u) (fun l => const_mem (l u)) hP
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideUpperBound
section
open UpperTheory.V.Lit.Geo

theorem UpperTheory.geometric_side_upper_bound :
    ThetaUp := by
  classical
  intro N
  obtain ⟨⟨K, hK, hK1⟩⟩ : Nonempty {K : ℝ // K ^ N * Real.exp (-K) < 1 / (2 * Real.exp Real.pi) ∧ 1 ≤ K} := by
    obtain ⟨K, hK⟩ := (((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N).eventually
      (gt_mem_nhds (show (0 : ℝ) < 1 / (2 * Real.exp Real.pi) by positivity))).and
      (Filter.eventually_ge_atTop (1 : ℝ))).exists
    exact ⟨⟨K, hK⟩⟩
  have hK0 : 0 ≤ K := by linarith
  have ha : Real.exp (-Real.pi * (K - 1)) * K ^ N ≤ 1 / 2 := by
    have e1 : Real.exp (-Real.pi * (K - 1)) = Real.exp Real.pi * Real.exp (-(Real.pi * K)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have e2 : Real.exp (-(Real.pi * K)) ≤ Real.exp (-K) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
    have hKN : 0 ≤ K ^ N := by positivity
    calc Real.exp (-Real.pi * (K - 1)) * K ^ N
        = Real.exp Real.pi * (K ^ N * Real.exp (-(Real.pi * K))) := by rw [e1]; ring
      _ ≤ Real.exp Real.pi * (K ^ N * Real.exp (-K)) := by gcongr
      _ ≤ Real.exp Real.pi * (1 / (2 * Real.exp Real.pi)) := by gcongr
      _ = 1 / 2 := by field_simp
  refine ⟨2 * K ^ N, by positivity, ?_⟩
  intro ι q i₀ μ hS hμ hμ1 hgap
  have hKμ : 1 / μ ≤ K / μ := by gcongr
  obtain ⟨hsY, hY⟩ := hS.2 (1 / μ) (K / μ) (by positivity) hKμ
  have hsX : Summable fun i => Real.exp (-Real.pi * (K / μ * q i)) :=
    (hS.2 (K / μ) (K / μ) (by positivity) le_rfl).1
  have hsI : Summable (fun i => if i = i₀ then (1 : ℝ) else 0) := (hasSum_ite_eq i₀ (1 : ℝ)).summable
  have hX2 : ∑' i, Real.exp (-Real.pi * (K / μ * q i)) ≤
      1 + Real.exp (-Real.pi * (K - 1)) * ∑' i, Real.exp (-Real.pi * (1 / μ * q i)) := by
    calc ∑' i, Real.exp (-Real.pi * (K / μ * q i))
        ≤ ∑' i, ((if i = i₀ then (1 : ℝ) else 0) +
            Real.exp (-Real.pi * (K - 1)) * Real.exp (-Real.pi * (1 / μ * q i))) := by
          refine Summable.tsum_le_tsum (fun i => ?_) hsX (hsI.add (hsY.mul_left _))
          by_cases h : i = i₀
          · have hq := hS.1 i
            have h0 : -Real.pi * (K / μ * q i) ≤ 0 := by
              have : 0 ≤ K / μ * q i := by positivity
              nlinarith [Real.pi_pos]
            have h1 := Real.exp_le_one_iff.mpr h0
            have h2 : 0 ≤ Real.exp (-Real.pi * (K - 1)) * Real.exp (-Real.pi * (1 / μ * q i)) := by positivity
            rw [if_pos h]
            linarith
          · have hr : 1 ≤ q i / μ := by
              rw [le_div_iff₀ hμ]
              linarith [hgap i h]
            rw [if_neg h, zero_add, ← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have e3 : K / μ * q i = K * (q i / μ) := by ring
            have e4 : 1 / μ * q i = q i / μ := by ring
            rw [e3, e4]
            nlinarith [mul_nonneg (sub_nonneg.2 hK1) (sub_nonneg.2 hr), Real.pi_pos]
      _ = 1 + Real.exp (-Real.pi * (K - 1)) * ∑' i, Real.exp (-Real.pi * (1 / μ * q i)) := by
          rw [Summable.tsum_add hsI (hsY.mul_left _), tsum_mul_left]
          congr 1
          exact tsum_ite_eq i₀ (fun _ => (1 : ℝ))
  have eK : K / μ / (1 / μ) = K := by field_simp
  rw [eK] at hY
  have hX0 : 0 ≤ ∑' i, Real.exp (-Real.pi * (K / μ * q i)) := tsum_nonneg fun i => (Real.exp_pos _).le
  have hX : ∑' i, Real.exp (-Real.pi * (K / μ * q i)) ≤ 2 := by
    have ha0 : 0 ≤ Real.exp (-Real.pi * (K - 1)) := (Real.exp_pos _).le
    have := mul_le_mul_of_nonneg_left hY ha0
    nlinarith
  have h1K : 1 ≤ K / μ := by
    rw [le_div_iff₀ hμ]
    linarith
  obtain ⟨-, hS1⟩ := hS.2 1 (K / μ) one_pos h1K
  simp only [one_mul, div_one] at hS1
  have hpow : 0 ≤ (K / μ) ^ N := by positivity
  calc ∑' i, Real.exp (-Real.pi * q i) ≤ (K / μ) ^ N * ∑' i, Real.exp (-Real.pi * (K / μ * q i)) := hS1
    _ ≤ (K / μ) ^ N * 2 := by gcongr
    _ = 2 * K ^ N / μ ^ N := by rw [div_pow]; ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GlobalGeometricEstimateOfLocal
section
open UpperTheory.V.Lit.Geo
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

private theorem key {E : Type} [Field E] [NumberField E] {a : ℕ} (g : GA E a) {c x : E} (hc : c ≠ 0) (hx : x ≠ 0)
    (y : Fin a → Ad E) (i : Fin a) (hy : algebraMap E (Ad E) x = ∑ j, y j * (g⁻¹).val j i)
    (hf : ∀ j p, ‖(algebraMap E (Ad E) c * y j).2 p‖ ≤ 1) {r : ℝ} (hr0 : 0 ≤ r) (hr : ∀ j w, ‖(y j).1 w‖ ≤ r) :
    1 ≤ (∏ w : InfinitePlace E, (‖(c : w.Completion)‖ * a * r) ^ w.mult) * AutomorphicForm.height (K := E) g := by
  have hcx : c * x ≠ 0 := mul_ne_zero hc hx
  have e : algebraMap E (Ad E) (c * x) = ∑ j, (algebraMap E (Ad E) c * y j) * (g⁻¹).val j i := by
    rw [map_mul, hy, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm
  rw [← prod_norm_mul_finprod_norm hcx, AutomorphicForm.height, ← mul_assoc, ← Finset.prod_mul_distrib]
  refine mul_le_mul ?_ ?_ (finprod_nonneg fun _ => norm_nonneg _)
    (Finset.prod_nonneg fun w _ => by have := locHeight_pos (infAt w g); positivity)
  · refine Finset.prod_le_prod₀ (fun _ _ => pow_nonneg (norm_nonneg _) _) fun w _ => ?_
    rw [← mul_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
    have h1 : ((c * x : E) : w.Completion) = ∑ j, ((c : w.Completion) * (y j).1 w) * ((infAt w g)⁻¹).val j i := by
      have := congrArg (infEval w) e
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at this
      conv at this =>
        lhs
        rw [infEval_apply, AdeleRing.algebraMap_fst_apply]
      refine Eq.trans this (Finset.sum_congr rfl fun j _ => ?_)
      rw [map_mul, map_mul, ← infAt_inv]
      simp only [infEval_apply, AdeleRing.algebraMap_fst_apply, infAt_apply]
    rw [h1]
    calc _ ≤ ∑ _j : Fin a, ‖(c : w.Completion)‖ * r * locHeight (infAt w g) := by
          refine norm_sum_le_of_le _ fun j _ => ?_
          rw [norm_mul, norm_mul]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hr j w) (norm_nonneg _))
            (norm_inv_apply_le_locHeight _ j i) (norm_nonneg _) (by positivity)
      _ = _ := by simp; ring
  · refine finprod_le_finprod₀ (Filter.eventually_cofinite.1 (eventually_norm_eq_one hcx)) (fun _ => norm_nonneg _)
      (finite_mulSupport_locHeight_finAt g) fun p => ?_
    have h1 : ((c * x : E) : p.adicCompletion E) =
        ∑ j, (algebraMap E (Ad E) c * y j).2 p * ((finAt p g)⁻¹).val j i := by
      have := congrArg (finEval p) e
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at this
      refine Eq.trans this (Finset.sum_congr rfl fun j _ => ?_)
      rw [map_mul, ← finAt_inv]
      rfl
    change ‖((c * x : E) : p.adicCompletion E)‖ ≤ locHeight (finAt p g)
    rw [h1]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (locHeight_pos _).le fun j _ => ?_
    rw [norm_mul]
    exact (mul_le_mul (hf j p) (norm_inv_apply_le_locHeight _ j i) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem UpperTheory.global_geometric_estimate_of_local :
    LatMin := by
  intro E _ _ _ a _ L hL
  have hT : IsCompact (⋃ j : Fin a, (fun y : Fin a → Af E => y j) '' (L : Set (Fin a → Af E))) :=
    isCompact_iUnion fun j => hL.isCompact.image (continuous_apply j)
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_mul_mem_integralFiniteAdeles_of_isCompact (K := E) hT
  have hc : algebraMap (𝓞 E) E d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0
  set c := algebraMap (𝓞 E) E d with hcdef
  set A : ℝ := ∏ w : InfinitePlace E, (‖(c : w.Completion)‖ * a) ^ 2 with hA
  refine ⟨max 1 A, 1, le_max_left _ _, fun g v hv hv0 => ?_⟩
  rw [pow_one]
  have hH := one_le_height (K := E) g
  have hq0 := qf_nonneg (pt g v)
  rcases le_total 1 (qf (pt g v)) with hq | hq
  · exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) hH) hq
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
  set y : Fin a → Ad E := ratVec v ᵥ* g.val with hy
  have hyi : algebraMap E (Ad E) (v i) = ∑ j, y j * (g⁻¹).val j i := by
    have : y ᵥ* (g⁻¹).val = ratVec v := by
      rw [hy, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
    exact (congrFun this i).symm
  have hF : ∀ j, (y j).2 = ptF g v j := fun j => by
    change pFin E (∑ k, ratVec v k * g.val k j) = ∑ k, vFin v k * pFin E (g.val k j)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_mul]; rfl
  have hI : ∀ j, pInf E (y j) = pt g v j := fun j => by
    change pInf E (∑ k, ratVec v k * g.val k j) = ∑ k, vInf v k * pInf E (g.val k j)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_mul]; rfl
  have hn : ∀ (x : Ad E) (w : InfinitePlace E), ‖pInf E x w‖ = ‖x.1 w‖ := fun x w =>
    (AddMonoidHomClass.isometry_iff_norm (InfinitePlace.Completion.extensionEmbedding w)).1
      (InfinitePlace.Completion.isometry_extensionEmbedding w) (x.1 w)
  have h := key g hc hi y i hyi (fun j p => by
      have h1 := hd (ptF g v j) (Set.mem_iUnion.2 ⟨j, ptF g v, hv, rfl⟩)
      rw [← hF] at h1
      exact norm_le_one_of_mem p (GroundTheory.Global.mem_integralFiniteAdeles.1 h1 p))
    (norm_nonneg (pt g v)) fun j w => by
      rw [← hn, hI]
      exact (norm_le_pi_norm (pt g v j) w).trans (norm_le_pi_norm _ j)
  have hm : ∀ w : InfinitePlace E, w.mult = 2 := fun w => InfinitePlace.IsComplex.mult_eq_two (IsTotallyComplex.isComplex w)
  have hr := ((UpperTheory.geometric_side_quadraticForm_identity E a).2.2.2.2.2 (pt g v)).1
  have h2 : (∏ w : InfinitePlace E, (‖(c : w.Completion)‖ * a * ‖pt g v‖) ^ w.mult) ≤ max 1 A * qf (pt g v) := by
    simp only [hm, mul_pow _ ‖pt g v‖, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    refine mul_le_mul (le_max_right _ _) ?_ (by positivity) (by positivity)
    exact (pow_le_of_le_one (sq_nonneg _) (hr.trans hq) Fintype.card_ne_zero).trans hr
  calc 1 ≤ _ := h
    _ ≤ max 1 A * qf (pt g v) * AutomorphicForm.height (K := E) g := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = _ := by ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.InfinitePlaceNormContinuity
section
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem row_last (i : Fin a) (hi : i.val + 1 = a) (b k : GA E a)
    (hb : b ∈ Reduction.adelicBorel (K := E) (n := a)) (d : Fin a → (Ad E)ˣ) (j : Fin a) :
    (b * Reduction.diagUnits a d * k : GA E a).val i j = (d i : Ad E) * (b.val i i * k.val i j) := by
  have hb' : (b.val : Matrix (Fin a) (Fin a) (Ad E)).IsUpperTriangular := hb
  rw [Units.val_mul, Units.val_mul, Reduction.coe_diagUnits, Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [Matrix.mul_diagonal]; ring
  · intro l _ hl
    have hlt : l < i := by
      have h1 := l.2
      have h2 : l.val ≠ i.val := fun h => hl (Fin.ext h)
      rw [Fin.lt_def]; omega
    rw [Matrix.mul_diagonal, hb' hlt, zero_mul, zero_mul]
  · simp

private theorem row_map {R : Type} [CommRing R] (f : Ad E →+* R) (γ : GL (Fin a) E) (g : GA E a) (i j : Fin a) :
    ((fun l => f (algebraMap E (Ad E) (γ.val i l))) ᵥ* (GeneralLinearGroup.map f g).val) j =
      f ((ratGL E a γ * g).val i j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Units.val_mul, Matrix.mul_apply, map_sum, Matrix.vecMul, dotProduct]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul]
  rfl

variable [_root_.NumberField.IsTotallyComplex E]

private theorem norm_pInf (x : Ad E) (w : InfinitePlace E) : ‖pInf E x w‖ = ‖x.1 w‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) (x.1 w)

private theorem cont_pInf : Continuous (pInf E) :=
  continuous_pi fun w => (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
    ((continuous_apply w).comp continuous_fst)

end

theorem UpperTheory.infinite_place_norm_continuity :
    SiegelRow := by
  intro E _ _ _ a ha
  obtain ⟨Ω, C, N, hΩ, hB, h⟩ := UpperTheory.height_bound_of_quasiHeight_le E a
  let i : Fin a := ⟨a - 1, by omega⟩
  have hi : i.val + 1 = a := by simp only [i]; omega
  let Φ : GA E a × GA E a → Fin a → Ad E := fun p j => p.1.val i i * p.2.val i j
  have hΦ : ∀ j, Continuous fun p => Φ p j := fun j =>
    ((Units.continuous_val.comp continuous_fst).matrix_elem i i).mul
      ((Units.continuous_val.comp continuous_snd).matrix_elem i j)
  have hS := hΩ.prod (Reduction.isCompact_maxCompact (K := E) (n := a))
  have hF : Continuous fun (p : GA E a × GA E a) (j : Fin a) => pFin E (Φ p j) :=
    continuous_pi fun j => continuous_snd.comp (hΦ j)
  have hI : Continuous fun p : GA E a × GA E a => qf fun j => pInf E (Φ p j) :=
    continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun w _ =>
      ((continuous_apply w).comp (cont_pInf.comp (hΦ j))).norm.pow 2
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hI.continuousOn
  refine ⟨_, C * M ^ N, N, hS.image hF, fun g => ?_⟩
  obtain ⟨γ, b, k, ρ, hρ, hb, hk, e, hq⟩ := h g
  have hrow : ∀ j, (ratGL E a γ * g.1).val i j =
      ((Reduction.posIdele (K := E) (ρ i) (hρ i) : (Ad E)ˣ) : Ad E) * Φ (b, k) j := fun j => by
    rw [e]
    exact row_last i hi b k (hB b hb) _ j
  refine ⟨γ.val i, fun h0 => ?_, ⟨(b, k), ⟨hb, hk⟩, funext fun j => ?_⟩, ?_⟩
  · have h1 := congrFun (congrFun γ.mul_inv i) i
    simp [Matrix.mul_apply, h0] at h1
  · refine Eq.trans ?_ (row_map (pFin E) γ g.1 i j).symm
    have h1 : pFin E ((Reduction.posIdele (K := E) (ρ i) (hρ i) : (Ad E)ˣ) : Ad E) = 1 :=
      IsDedekindDomain.FiniteAdeleRing.ext _ fun v => Reduction.posIdele_finite (K := E) (ρ i) (hρ i) v
    rw [hrow, map_mul, h1, one_mul]
  · have h1 : qf (pt (E := E) (a := a) g.1 (γ.val i)) = ρ i ^ 2 * qf fun j => pInf E (Φ (b, k) j) := by
      unfold qf
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      have h2 : pt (E := E) (a := a) g.1 (γ.val i) j = _ := row_map (pInf E) γ g.1 i j
      rw [h2, hrow, map_mul, Pi.mul_apply, norm_mul, norm_pInf, Reduction.norm_posIdele_infinite, mul_pow]
    have h3 : (qf fun j => pInf E (Φ (b, k) j)) ≤ M := (Real.le_norm_self _).trans (hM (b, k) ⟨hb, hk⟩)
    have h4 : 0 ≤ qht (E := E) (a := a) g.1 := Real.iInf_nonneg fun _ => (AutomorphicForm.height_pos _).le
    have h5 := (hq i).1 hi
    have h6 : 0 ≤ qht (E := E) (a := a) g.1 * ρ i ^ (2 * N) := mul_nonneg h4 (pow_nonneg (hρ i).le _)
    rw [h1, mul_pow, ← pow_mul, ← mul_assoc]
    exact mul_le_mul h5 (pow_le_pow_left₀ (qf_nonneg _) h3 N) (pow_nonneg (qf_nonneg _) N) (h6.trans h5)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.PointEvaluationMultiplicativeTsum
section
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep

private theorem tsum_reindex {α M : Type} [AddCommGroup α] [AddCommMonoid M] [TopologicalSpace M]
    (S T : AddSubgroup α) (e : α ≃ α) (he : ∀ v, v ∈ S ↔ e v ∈ T) (f f' : α → M) (hf : ∀ v, f v = f' (e v)) :
    ∑' v : S, f v.1 = ∑' v : T, f' v.1 := by
  rw [← (e.subtypeEquiv he : S ≃ T).tsum_eq (fun v : T => f' v.1)]
  exact tsum_congr fun v => hf v.1

private def mulEquivRow {R : Type} [CommRing R] {a : ℕ} (γ : GL (Fin a) R) : (Fin a → R) ≃ (Fin a → R) where
  toFun v := v ᵥ* γ.val
  invFun v := v ᵥ* (γ⁻¹).val
  left_inv v := by
    show (v ᵥ* γ.val) ᵥ* (γ⁻¹).val = v
    rw [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
  right_inv v := by
    show (v ᵥ* (γ⁻¹).val) ᵥ* γ.val = v
    rw [Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]

section

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem ptF_mul (g k : GA E a) (v : Fin a → E) :
    ptF (g * k) v = ptF g v ᵥ* (GeneralLinearGroup.map (pFin E) k).val := by
  show vFin v ᵥ* (GeneralLinearGroup.map (pFin E) (g * k)).val = (vFin v ᵥ* (GeneralLinearGroup.map (pFin E) g).val) ᵥ* _
  rw [map_mul, Units.val_mul, Matrix.vecMul_vecMul]

variable [_root_.NumberField.IsTotallyComplex E]

private theorem pt_mul (g k : GA E a) (v : Fin a → E) :
    pt (g * k) v = pt g v ᵥ* (GeneralLinearGroup.map (pInf E) k).val := by
  show vInf v ᵥ* (GeneralLinearGroup.map (pInf E) (g * k)).val = (vInf v ᵥ* (GeneralLinearGroup.map (pInf E) g).val) ᵥ* _
  rw [map_mul, Units.val_mul, Matrix.vecMul_vecMul]

end

theorem UpperTheory.point_evaluation_multiplicative_tsum :
    SumInv := by
  intro E _ _ _ a ha L M _ _ F
  obtain ⟨h1, h2, h3, h4⟩ := UpperTheory.rationalPoint_retraction_exists_cmDatum E a ha
  have h5 := UpperTheory.cmDatum_infinitePlaces_complex_split E a ha
  refine ⟨fun γ t g => ?_, fun g h => ?_, fun U hU hL u hu g => ?_⟩
  · refine tsum_reindex _ _ (mulEquivRow γ) (fun v => ?_) (fun v => F (pt (rt _) v)) (fun v => F (pt (rt g) v))
      (fun v => ?_)
    · show ptF _ v ∈ L ↔ ptF g (v ᵥ* γ.val) ∈ L
      rw [← (h2 _).2.2, h1, (h3 γ (rt g) v).1, (h2 g).2.2]
    · show F (pt (rt _) v) = F (pt (rt g) (v ᵥ* γ.val))
      rw [h1, (h3 γ (rt g) v).2]
  · refine tsum_reindex _ _ (Equiv.refl _) (fun v => ?_) (fun v => F (pt (rt _) v))
      (fun v => F (sc h.val • (pt (rt g) v ᵥ* h.val))) (fun v => ?_)
    · show ptF _ v ∈ L ↔ ptF g v ∈ L
      rw [ptF_mul, pFin_infGL, Units.val_one, Matrix.vecMul_one]
    · show F (pt (rt _) v) = F (sc h.val • (pt (rt g) v ᵥ* h.val))
      rw [h5]
  · refine tsum_reindex _ _ (Equiv.refl _) (fun v => ?_) (fun v => F (pt (rt _) v)) (fun v => F (pt (rt g) v))
      (fun v => ?_)
    · show ptF _ v ∈ L ↔ ptF g v ∈ L
      rw [ptF_mul, pFin_finGL]
      refine ⟨fun hv => ?_, hL u hu _⟩
      have h6 := hL u⁻¹ (U.inv_mem hu) _ hv
      rwa [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one] at h6
    · show F (pt (rt _) v) = F (pt (rt g) v)
      rw [h4 U hU u hu, pt_mul, pInf_finGL, Units.val_one, Matrix.vecMul_one]
end

