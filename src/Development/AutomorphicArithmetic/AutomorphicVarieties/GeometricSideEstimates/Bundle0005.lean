module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0022

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.ConvexSeparationPositiveDistance
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V.Lit.Geo

private theorem dot_cancel {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (f : R →+* S) (g : GL (Fin a) R)
    (x y : Fin a → S) :
    (x ᵥ* (GeneralLinearGroup.map f g).val) ⬝ᵥ ((GeneralLinearGroup.map f g⁻¹).val *ᵥ y) = x ⬝ᵥ y := by
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
    Units.val_one, Matrix.one_mulVec]

private theorem back {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (f : R →+* S) (g : GL (Fin a) R)
    (y : Fin a → S) (h : (GeneralLinearGroup.map f g⁻¹).val *ᵥ y = 0) : y = 0 := by
  have h2 := congrArg (fun z => (GeneralLinearGroup.map f g).val *ᵥ z) h
  simp only [Matrix.mulVec_zero] at h2
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
    Units.val_one, Matrix.one_mulVec] at h2

private theorem abs_inf {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (x : E) (w : InfinitePlace E) :
    ‖pInf E (algebraMap E (Ad E) x) w‖ = w x := by
  rw [pInf_algebraMap, InfinitePlace.norm_embedding_eq]

private theorem inf_ne {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (x : E) (hx : x ≠ 0) :
    pInf E (algebraMap E (Ad E) x) ≠ 0 := by
  intro h
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have h1 := abs_inf x w
  rw [h] at h1
  have h2 := InfinitePlace.pos_iff (w := w).2 hx
  simp at h1
  exact h2.ne h1

private theorem sep {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (T : Set (Af E)) (hT : IsCompact T) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : E, algebraMap E (Af E) x ∈ T → x = 0 ∨ c ≤ ‖pInf E (algebraMap E (Ad E) x)‖ := by
  have hf := UpperTheory.V.Lit.Dr.finField E 1 T hT
  have hf2 := (hf.subset (Set.diff_subset (t := {0}))).image fun x => ‖pInf E (algebraMap E (Ad E) x)‖⁻¹
  obtain ⟨M, hM⟩ := hf2.bddAbove
  refine ⟨(max M 1)⁻¹, by positivity, fun x hx => ?_⟩
  by_cases h0 : x = 0
  · exact Or.inl h0
  right
  have hp : 0 < ‖pInf E (algebraMap E (Ad E) x)‖ := norm_pos_iff.2 (inf_ne x h0)
  rw [inv_le_comm₀ (by positivity) hp]
  by_cases h1 : ∀ w : InfinitePlace E, w x ≤ 1
  · exact (hM ⟨x, ⟨⟨h1, hx⟩, h0⟩, rfl⟩).trans (le_max_left _ _)
  · push Not at h1
    obtain ⟨w, hw⟩ := h1
    refine le_trans (inv_le_one_of_one_le₀ ?_) (le_max_right _ _)
    rw [← abs_inf] at hw
    exact hw.le.trans (norm_le_pi_norm _ w)

theorem UpperTheory.convex_separation_positive_distance :
    ShortCol := by
  intro E _ _ _ a ha L hL
  obtain ⟨T, C, N, hT, H⟩ := UpperTheory.positivity_at_all_places E a ha
  obtain ⟨-, hR, -⟩ := UpperTheory.rationalPoint_retraction_exists_cmDatum E a ha
  have hc : IsCompact ((fun p : (Fin a → Af E) × (Fin a → Af E) => p.1 ⬝ᵥ p.2) '' ((L : Set (Fin a → Af E)) ×ˢ T)) :=
    (hL.isCompact.prod hT).image (continuous_fst.dotProduct continuous_snd)
  obtain ⟨c, hc0, hsep⟩ := sep _ hc
  refine ⟨c, C, N, hc0, fun g => ?_⟩
  obtain ⟨ξ, hξ, h1, h2⟩ := H (retractOne g)
  change (GeneralLinearGroup.map (pFin E) (rt g)⁻¹).val *ᵥ vFin ξ ∈ T at h1
  change qht (rt g) * qf ((GeneralLinearGroup.map (pInf E) (rt g)⁻¹).val *ᵥ vInf ξ) ^ N ≤ C at h2
  refine ⟨(GeneralLinearGroup.map (pInf E) (rt g)⁻¹).val *ᵥ vInf ξ, fun h => hξ ?_, (hR g).2.1 ▸ h2, fun v hv => ?_⟩
  · have h3 := back _ _ _ h
    funext i
    by_contra hi
    exact inf_ne (ξ i) hi (congrFun h3 i)
  · have e1 : pt (rt g) v ⬝ᵥ ((GeneralLinearGroup.map (pInf E) (rt g)⁻¹).val *ᵥ vInf ξ)
        = pInf E (algebraMap E (Ad E) (v ⬝ᵥ ξ)) := by
      refine (dot_cancel (pInf E) (rt g) (vInf v) (vInf ξ)).trans ?_
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dotProduct, vInf, map_sum, map_mul]
    have e2 : ptF (rt g) v ⬝ᵥ ((GeneralLinearGroup.map (pFin E) (rt g)⁻¹).val *ᵥ vFin ξ)
        = algebraMap E (Af E) (v ⬝ᵥ ξ) := by
      refine (dot_cancel (pFin E) (rt g) (vFin v) (vFin ξ)).trans ?_
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dotProduct, vFin, map_sum, map_mul]
    have hv' : ptF (rt g) v ∈ L := by rw [(hR g).2.2]; exact hv
    rw [e1]
    rcases hsep (v ⬝ᵥ ξ) ⟨(_, _), ⟨hv', h1⟩, e2⟩ with h | h
    · left; rw [h, map_zero, map_zero]
    · exact Or.inr h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometryOfNumbersLatticeEstimate
section
open UpperTheory.V.Lit.Geo NumberField

theorem UpperTheory.geometry_of_numbers_lattice_estimate :
    LatScale := by
  intro E _ _ _ a ha L hL
  letI : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin a × InfinitePlace E)) :=
    InnerProductSpace.rclikeToReal ℂ _
  refine ⟨Module.finrank ℝ (EuclideanSpace ℂ (Fin a × InfinitePlace E)), fun g => ?_⟩
  obtain ⟨C, N, hC, hmin⟩ := UpperTheory.global_geometric_estimate_of_local E a ha L hL
  obtain ⟨-, hrt, -⟩ := UpperTheory.rationalPoint_retraction_exists_cmDatum E a ha
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ v ∈ lat L (rt g), v ≠ 0 → 1 ≤ B * qf (pt (rt g) v) := ⟨_, hmin (rt g)⟩
  have hlat : lat L (rt g) = lat L g := by
    unfold lat
    rw [(hrt g).2.2]
  rw [hlat] at hB
  let φ : lat L g →+ EuclideanSpace ℂ (Fin a × InfinitePlace E) :=
    (euc.toLinearMap.toAddMonoidHom.comp (pt (rt g))).comp (lat L g).subtype
  have hφ : ∀ v : lat L g, ‖φ v‖ ^ 2 = qf (pt (rt g) v.1) := fun v => norm_euc_sq _
  have hM : (0 : ℝ) < max B 1 := lt_max_of_lt_right one_pos
  have key := UpperTheory.scaling_invariance_of_geometric_functional (lat L g) (EuclideanSpace ℂ (Fin a × InfinitePlace E)) φ
    (Real.sqrt (1 / max B 1)) (Real.sqrt_pos.2 (by positivity)) (fun v hv => by
      have h1 := hB v.1 v.2 (fun h => hv (Subtype.ext h))
      rw [← hφ] at h1
      apply Real.sqrt_le_iff.2
      refine ⟨norm_nonneg _, ?_⟩
      rw [div_le_iff₀ hM, mul_comm]
      exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)))
  simpa only [hφ] using key
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.LatticePointCountBound
section
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum

private theorem gauss_sum_determines_value_and_deviation {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (L : AddSubgroup (Fin a → Af E)) (g g' : GA E a)
    (hR : gsum L gauss g' = gsum L gauss g)
    (hC : ∀ F : (Fin a → Cinf E) → ℂ, gsum L F g' = gsum L F g) :
    fn L g' = fn L g ∧ dev L g' = dev L g := by
  have hT : Th L g' = Th L g := hR
  have hm : ∀ P, mean L P g' = mean L P g := fun P => by
    unfold mean
    rw [hT, hC]
  have hmom : mom L g' = mom L g := by
    apply Subtype.ext
    ext i j w
    exact hm _
  refine ⟨?_, ?_⟩
  · unfold fn
    rw [hT]
  · unfold dev
    rw [hmom]

theorem UpperTheory.lattice_point_count_bound :
    FnInv := by
  intro E _ _ _ a ha L
  refine ⟨fun γ t g => gauss_sum_determines_value_and_deviation L _ _ ((UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℝ gauss).1 γ t g)
      (fun F => (UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℂ F).1 γ t g),
    fun U hU hL u hu g => gauss_sum_determines_value_and_deviation L _ _ ((UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℝ gauss).2.2 U hU hL u hu g)
      (fun F => (UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℂ F).2.2 U hU hL u hu g), fun k g => ?_⟩
  have h1 := (UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℝ gauss).2.1 g (Unitary.toUnits k)
  have hk : (Unitary.toUnits k : GL (Fin a) (Cinf E)).val = k.1 := rfl
  have hs : sc k.1 = 1 := (UpperTheory.deriv_similitudeChar_at_one_eq_trace E a).2.2.2.2 k
  have hq := UpperTheory.geometric_side_quadraticForm_identity E a
  unfold Th
  rw [h1]
  unfold gsum
  refine tsum_congr fun v => ?_
  rw [hk, hs, one_smul]
  unfold gauss
  rw [hq.2.2.1, (Unitary.mem_iff.1 k.2).2, hq.1]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.NsmulOrbitBoundedOfCompact
section
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum Filter Topology

private theorem nsmul_mem_of_compact {E : Type} [Field E] [NumberField E] {a : ℕ} (L : AddSubgroup (Fin a → Af E))
    (hL : IsOpen (L : Set (Fin a → Af E))) {T : Set (Fin a → Af E)} (hT : IsCompact T) :
    ∃ M : ℕ, 0 < M ∧ ∀ x ∈ T, M • x ∈ L := by
  have hc : Continuous fun p : Af E × (Fin a → Af E) => p.1 • p.2 := continuous_fst.smul continuous_snd
  have hev : ∀ᶠ r in 𝓝 (0 : Af E), ∀ x ∈ T, r • x ∈ L := by
    refine hT.eventually_forall_of_forall_eventually fun x _ => ?_
    refine hc.continuousAt.preimage_mem_nhds (hL.mem_nhds ?_)
    show (0 : Af E) • x ∈ L
    rw [zero_smul]
    exact L.zero_mem
  obtain ⟨n, hn⟩ := ((GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele E).eventually hev).exists
  refine ⟨n.factorial, n.factorial_pos, fun x hx => ?_⟩
  have h := hn x hx
  rwa [Nat.cast_smul_eq_nsmul] at h

theorem UpperTheory.nsmul_orbit_bounded_of_compact :
    ShortRow := by
  intro E _ _ _ a ha L hL
  obtain ⟨T, C, N, hT, hrow⟩ := UpperTheory.infinite_place_norm_continuity E a ha
  obtain ⟨M, hM, hML⟩ := nsmul_mem_of_compact L hL.isOpen hT
  refine ⟨((M : ℝ) ^ 2) ^ N * C, N, fun g => ?_⟩
  obtain ⟨-, hq, hF⟩ := (UpperTheory.rationalPoint_retraction_exists_cmDatum E a ha).2.1 g
  obtain ⟨v, hv, hvT, hvC⟩ := hrow (retractOne g)
  change ptF (rt g) v ∈ T at hvT
  change qht (rt g) * qf (pt (rt g) v) ^ N ≤ C at hvC
  rw [hF] at hvT
  rw [hq] at hvC
  refine ⟨M • v, ?_, ?_, ?_⟩
  · show ptF g (M • v) ∈ L
    rw [map_nsmul]
    exact hML _ hvT
  · rw [← Nat.cast_smul_eq_nsmul E]
    exact smul_ne_zero (Nat.cast_ne_zero.2 hM.ne') hv
  · rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, (UpperTheory.geometric_side_quadraticForm_identity E a).2.2.2.1, mul_pow, mul_left_comm]
    exact mul_le_mul_of_nonneg_left hvC (by positivity)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.QuadraticFormGradientFormula
section
open UpperTheory.V.Lit.Geo
open NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped ContDiff

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem qf_mem : (fun x : Fin a → Cinf E => ((qf x : ℝ) : ℂ)) ∈ poly E a := by
  have h : (fun x : Fin a → Cinf E => ((qf x : ℝ) : ℂ)) =
      ∑ i : Fin a, ∑ w : InfinitePlace E,
        ((fun x : Fin a → Cinf E => x i w) * (fun x : Fin a → Cinf E => (starRingEnd ℂ) (x i w))) := by
    funext x
    simp only [qf, Finset.sum_apply, Pi.mul_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  rw [h]
  refine Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun w _ => Subalgebra.mul_mem _ ?_ ?_
  · exact Algebra.subset_adjoin ⟨⟨⟨fun x => x i w, fun _ _ => rfl⟩, fun _ _ => rfl⟩, rfl⟩
  · refine Algebra.subset_adjoin ⟨⟨⟨fun x => (starRingEnd ℂ) (x i w), fun _ _ => ?_⟩, fun c x => ?_⟩, rfl⟩
    · simp
    · simp

private theorem pg_eq (P : (Fin a → Cinf E) → ℂ) :
    pg P = fun x => P x * Complex.exp (-(Real.pi : ℂ) * ((qf x : ℝ) : ℂ)) := by
  funext x
  simp only [pg, gauss]
  push_cast
  rfl

private theorem fderiv_pg {P : (Fin a → Cinf E) → ℂ} (hP : P ∈ poly E a) (x u : Fin a → Cinf E) :
    fderiv ℝ (pg P) x u = (fderiv ℝ P x u - (Real.pi : ℂ) * (P x *
      fderiv ℝ (fun y : Fin a → Cinf E => ((qf y : ℝ) : ℂ)) x u)) * (gauss x : ℝ) := by
  have h1 : HasFDerivAt P (fderiv ℝ P x) x :=
    (((UpperTheory.admissibleFunctionClass_closure_properties E a P hP).1.differentiable (by simp)) x).hasFDerivAt
  have h2 := (((UpperTheory.admissibleFunctionClass_closure_properties E a _ qf_mem).1.differentiable (by simp)) x).hasFDerivAt
  have h3 := h1.mul ((h2.const_mul (-(Real.pi : ℂ))).cexp)
  have hg : ((gauss x : ℝ) : ℂ) = Complex.exp (-(Real.pi : ℂ) * ((qf x : ℝ) : ℂ)) := by
    simp only [gauss]
    push_cast
    rfl
  have h4 := h3.fderiv
  rw [pg_eq, hg]
  erw [h4]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

end

theorem UpperTheory.quadratic_form_gradient_formula :
    PolyD := by
  intro E _ _ a P hP
  obtain ⟨hP1, -, hP3⟩ := UpperTheory.admissibleFunctionClass_closure_properties E a P hP
  obtain ⟨hR1, -, hR3⟩ := UpperTheory.admissibleFunctionClass_closure_properties E a _ qf_mem
  refine ⟨?_, ?_, fun T => ?_⟩
  · rw [pg_eq]
    exact hP1.mul (contDiff_const.mul hR1).cexp
  · let b := Module.finBasis ℝ (Fin a → Cinf E)
    obtain ⟨C₀, hC₀, hb⟩ := b.exists_opNorm_le (F := ℂ)
    have hQ : ∀ u : Fin a → Cinf E, ∃ (C : ℝ) (k : ℕ), ∀ x, ‖fderiv ℝ P x u - (Real.pi : ℂ) * (P x *
        fderiv ℝ (fun y : Fin a → Cinf E => ((qf y : ℝ) : ℂ)) x u)‖ ≤ C * (1 + qf x) ^ k := fun u =>
      (UpperTheory.admissibleFunctionClass_closure_properties E a _ (Subalgebra.sub_mem _ ((hP3 0).2.2 u)
        (Subalgebra.smul_mem _ (Subalgebra.mul_mem _ hP ((hR3 0).2.2 u)) (Real.pi : ℂ)))).2.1
    choose C k hCk using hQ
    refine ⟨C₀ * ∑ i, |C (b i)|, ∑ i, k (b i), fun x => ?_⟩
    have hq : 1 ≤ 1 + qf x := by linarith [qf_nonneg x]
    have hg : 0 < gauss x := Real.exp_pos _
    have hS : 0 ≤ ∑ i, |C (b i)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have key := hb (u := fderiv ℝ (pg P) x) (M := (∑ i, |C (b i)|) * (1 + qf x) ^ (∑ i, k (b i)) * gauss x)
      (by positivity) (fun i => by
        rw [fderiv_pg hP, norm_mul, Complex.norm_real, Real.norm_of_nonneg hg.le]
        refine mul_le_mul_of_nonneg_right ((hCk (b i) x).trans ?_) hg.le
        refine (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans ?_
        refine mul_le_mul ?_ (pow_le_pow_right₀ hq ?_) (by positivity) hS
        · exact Finset.single_le_sum (f := fun i => |C (b i)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
        · exact Finset.single_le_sum (f := fun i => k (b i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
    calc _ ≤ _ := key
      _ = _ := by ring
  · exact ⟨_, Subalgebra.sub_mem _ (hP3 T).1
      (Subalgebra.smul_mem _ (Subalgebra.mul_mem _ hP (hR3 T).1) (Real.pi : ℂ)), fun x => fderiv_pg hP x (T x)⟩
end

