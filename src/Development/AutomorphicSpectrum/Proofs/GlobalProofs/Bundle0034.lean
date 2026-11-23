module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0031
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.WeilBound.CoreStatements.ProjectiveValuations.CompactSpaceComplexPointsOfProper

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AnalyticVectorExponentialSeries
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

section Chain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem hasDerivAt_one_sub_pow_succ_div_factorial (N : ℕ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (1 - t) ^ (N + 1) / ((N + 1).factorial : ℝ))
      (-((1 - s) ^ N / (N.factorial : ℝ))) s := by
  have h0 : HasDerivAt (fun t : ℝ => 1 - t) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub 1
  have h1 : HasDerivAt (fun t : ℝ => (1 - t) ^ (N + 1)) (((N + 1 : ℕ) : ℝ) * (1 - s) ^ (N + 1 - 1) * (-1)) s :=
    h0.pow (N + 1)
  refine (h1.div_const ((N + 1).factorial : ℝ)).congr_deriv ?_
  rw [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  have : (N.factorial : ℝ) ≠ 0 := by positivity
  field_simp

private theorem hasDerivAt_sum_one_sub_pow_div_factorial_smul {f : ℕ → ℝ → E} (hf : ∀ m s, HasDerivAt (f m) (f (m + 1) s) s)
    (N : ℕ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ∑ m ∈ Finset.range (N + 1), ((1 - t) ^ m / (m.factorial : ℝ)) • f m t)
      (((1 - s) ^ N / (N.factorial : ℝ)) • f (N + 1) s) s := by
  induction N with
  | zero => simpa using hf 0 s
  | succ N ih =>
    have h2 := ih.add ((hasDerivAt_one_sub_pow_succ_div_factorial N s).smul (hf (N + 1) s))
    convert (preTransparency := .reducible) h2 using 1
    · funext t
      exact Finset.sum_range_succ _ _
    · rw [neg_smul]
      abel

theorem norm_chain_sub_partial_le {f : ℕ → ℝ → E} (hf : ∀ m s, HasDerivAt (f m) (f (m + 1) s) s) (N : ℕ) {A : ℝ}
    (hA : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖f (N + 1) s‖ ≤ A) :
    ‖f 0 1 - ∑ m ∈ Finset.range (N + 1), ((m.factorial : ℝ)⁻¹) • f m 0‖ ≤ A / ((N + 1).factorial : ℝ) := by
  let F : ℝ → E := fun t => ∑ m ∈ Finset.range (N + 1), ((1 - t) ^ m / (m.factorial : ℝ)) • f m t
  have hF1 : F 1 = f 0 1 := by
    simp [F, Finset.sum_range_succ']
  have hF0 : F 0 = ∑ m ∈ Finset.range (N + 1), ((m.factorial : ℝ)⁻¹) • f m 0 := by
    simp [F]
  have hD : ∀ t, HasDerivAt F (((1 - t) ^ N / (N.factorial : ℝ)) • f (N + 1) t) t :=
    fun t => hasDerivAt_sum_one_sub_pow_div_factorial_smul hf N t
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := fun t => F t - F 0) (a := 0) (b := 1)
    (f' := fun t => ((1 - t) ^ N / (N.factorial : ℝ)) • f (N + 1) t)
    (B := fun t => A / ((N + 1).factorial : ℝ) - A * ((1 - t) ^ (N + 1) / ((N + 1).factorial : ℝ)))
    (B' := fun t => A * ((1 - t) ^ N / (N.factorial : ℝ)))
    (fun t _ => ((hD t).continuousAt.sub continuousAt_const).continuousWithinAt)
    (fun t _ => ((hD t).sub_const (F 0)).hasDerivWithinAt)
    (by simp [div_eq_mul_inv])
    (fun t => (((hasDerivAt_one_sub_pow_succ_div_factorial N t).const_mul A).const_sub
      (A / ((N + 1).factorial : ℝ))).congr_deriv (by ring))
    (fun t ht => by
      have hc : 0 ≤ (1 - t) ^ N / (N.factorial : ℝ) := by
        have : 0 ≤ 1 - t := by linarith [ht.2]
        positivity
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, mul_comm A]
      exact mul_le_mul_of_nonneg_left (hA t ⟨ht.1, ht.2.le⟩) hc)
  have h1 := key (x := 1) ⟨zero_le_one, le_rfl⟩
  simp only [hF1, hF0, sub_self, zero_pow (Nat.succ_ne_zero N), zero_div, mul_zero, sub_zero] at h1
  exact h1

theorem hasSum_chain {f : ℕ → ℝ → E} (hf : ∀ m s, HasDerivAt (f m) (f (m + 1) s) s) {a : ℕ → ℝ}
    (ha : ∀ m, ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖f m s‖ ≤ a m)
    (hs : Summable fun m : ℕ => a m / (m.factorial : ℝ)) :
    HasSum (fun m : ℕ => ((m.factorial : ℝ)⁻¹) • f m 0) (f 0 1) := by
  have hn : Summable fun m : ℕ => ‖((m.factorial : ℝ)⁻¹) • f m 0‖ := by
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hs
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (ha m 0 ⟨le_rfl, zero_le_one⟩) (by positivity)
  rw [hasSum_iff_tendsto_nat_of_summable_norm hn, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_ hs.tendsto_atTop_zero
  refine Filter.eventually_atTop.mpr ⟨1, fun n hn1 => ?_⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  rw [norm_sub_rev]
  exact norm_chain_sub_partial_le hf N (ha (N + 1))

end Chain

section Exp

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem continuous_exp_smul_real {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun t : ℝ => NormedSpace.exp (t • X) := by
  exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

end Exp

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {v : H}

theorem exp_add_smul_real (X : Matrix (Fin n) (Fin n) ℂ) (s h : ℝ) :
    NormedSpace.exp ((s + h) • X) = NormedSpace.exp (s • X) * NormedSpace.exp (h • X) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right h)

theorem isSmoothVec_iterate_dRep (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H}
    (hs : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (m : ℕ) :
    IsSmoothVec G π ((dRep π X)^[m] v) := by
  induction m with
  | zero => exact hs
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact (hasDerivAt_dRep_and_isSmoothVec hG hrep ih hX).2

theorem hasDerivAt_orbit_smooth (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {u : H}
    (hu : IsSmoothVec G π u) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (s : ℝ) :
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) u) (π (NormedSpace.exp (s • X)) (dRep π X u)) s := by
  have hd := (hasDerivAt_dRep_and_isSmoothVec hG hrep hu hX).1
  have hmem : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G := hX
  have heq : (fun t : ℝ => π (NormedSpace.exp (t • X)) u) =
      fun t => π (NormedSpace.exp (s • X)) (π (NormedSpace.exp ((t - s) • X)) u) := by
    funext t
    have h1 : NormedSpace.exp (t • X) = NormedSpace.exp (s • X) * NormedSpace.exp ((t - s) • X) := by
      rw [← exp_add_smul_real, add_sub_cancel]
    rw [h1, hrep.2 _ (hmem s) _ (hmem (t - s))]
    rfl
  rw [heq]
  have hd' : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) u) (dRep π X u) (s - s) := by
    rw [sub_self]
    exact hd
  have hc := hd'.comp_sub_const s s
  exact ((π (NormedSpace.exp (s • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hc

theorem exists_bound_orbit_Icc [CompleteSpace H] (hc : ∀ v, ContinuousOn (fun g => π g v) G)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) :
    ∃ B : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖π (NormedSpace.exp (s • X))‖ ≤ B := by
  have hcont : ∀ w, ContinuousOn (fun s : ℝ => π (NormedSpace.exp (s • X)) w) (Set.Icc 0 1) := by
    intro w
    exact (hc w).comp (continuous_exp_smul_real X).continuousOn (fun s _ => hX s)
  have hb : ∀ w, ∃ C, ∀ i : Set.Icc (0 : ℝ) 1, ‖π (NormedSpace.exp ((i : ℝ) • X)) w‖ ≤ C := by
    intro w
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hcont w)
    exact ⟨C, fun i => hC i i.2⟩
  obtain ⟨B, hB⟩ := banach_steinhaus (g := fun i : Set.Icc (0 : ℝ) 1 => π (NormedSpace.exp ((i : ℝ) • X))) hb
  exact ⟨B, fun s hs => hB ⟨s, hs⟩⟩

theorem norm_iterate_dRep_le {C : ℝ}
    (hb : ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ HCSS.lieOf G) →
      ‖l.foldr (dRep π) v‖ ≤ C ^ (l.length + 1) * l.length.factorial * (l.map mnorm).prod)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (m : ℕ) :
    ‖(dRep π X)^[m] v‖ ≤ C ^ (m + 1) * m.factorial * mnorm X ^ m := by
  have hfold : ∀ k, List.foldr (dRep π) v (List.replicate k X) = (dRep π X)^[k] v := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [List.replicate_succ, List.foldr_cons, ih, Function.iterate_succ_apply']
  have h := hb (List.replicate m X) (fun Y hY => by rw [List.eq_of_mem_replicate hY]; exact hX)
  rw [hfold, List.length_replicate, List.map_replicate, List.prod_replicate] at h
  exact h

theorem mnorm_nonneg' (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ mnorm X := by
  unfold mnorm
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => norm_nonneg _

theorem hasSum_orbit_of_wordBound : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hc : ∀ v, ContinuousOn (fun g => π g v) G) {v : H} (hs : IsSmoothVec G π v)
    (hw : WordBound G π v), ∃ r : ℝ, 0 < r ∧ ∀ X ∈ HCSS.lieOf G, mnorm X < r →
      HasSum (fun m : ℕ => ((m.factorial : ℂ)⁻¹) • (dRep π X)^[m] v) (π (NormedSpace.exp X) v) := by
  intro n G H _ _ _ π hG hrep hc v hs hw
  obtain ⟨C, hC0, hC⟩ := hw
  refine ⟨C⁻¹, inv_pos.mpr hC0, fun X hX hXr => ?_⟩
  obtain ⟨B, hB⟩ := exists_bound_orbit_Icc hc hX
  let f : ℕ → ℝ → H := fun m s => π (NormedSpace.exp (s • X)) ((dRep π X)^[m] v)
  have hf : ∀ m s, HasDerivAt (f m) (f (m + 1) s) s := by
    intro m s
    have := hasDerivAt_orbit_smooth hG hrep (isSmoothVec_iterate_dRep hG hrep hs hX m) hX s
    simpa only [f, Function.iterate_succ_apply'] using this
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 ⟨le_rfl, zero_le_one⟩)
  have hmX := mnorm_nonneg' X
  let a : ℕ → ℝ := fun m => B * (C ^ (m + 1) * m.factorial * mnorm X ^ m)
  have ha : ∀ m, ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖f m s‖ ≤ a m := by
    intro m s hs'
    calc ‖f m s‖ ≤ ‖π (NormedSpace.exp (s • X))‖ * ‖(dRep π X)^[m] v‖ := (π _).le_opNorm _
      _ ≤ B * (C ^ (m + 1) * m.factorial * mnorm X ^ m) :=
        mul_le_mul (hB s hs') (norm_iterate_dRep_le hC hX m) (norm_nonneg _) hB0
  have hsum : Summable fun m : ℕ => a m / (m.factorial : ℝ) := by
    have heq : (fun m : ℕ => a m / (m.factorial : ℝ)) = fun m => (B * C) * (C * mnorm X) ^ m := by
      funext m
      have : (m.factorial : ℝ) ≠ 0 := by positivity
      simp only [a]
      field_simp
      ring
    rw [heq]
    refine Summable.mul_left _ (summable_geometric_of_lt_one (mul_nonneg hC0.le hmX) ?_)
    calc C * mnorm X < C * C⁻¹ := mul_lt_mul_of_pos_left hXr hC0
      _ = 1 := mul_inv_cancel₀ hC0.ne'
  have key := hasSum_chain hf ha hsum
  have h1 : f 0 1 = π (NormedSpace.exp X) v := by
    simp [f]
  have h2 : ∀ m, f m 0 = (dRep π X)^[m] v := by
    intro m
    simp [f, hrep.1]
  rw [h1] at key
  simp only [h2] at key
  convert key using 1
  funext m
  rw [show ((m.factorial : ℂ)⁻¹) = (((m.factorial : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.coe_smul]

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CompactSpaceCxPtsOfIsProper
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.Gaga

theorem compactSpace_cxPts_of_isProper :
    ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ), IsProper p → CompactSpace (CxPts p (RingHom.id ℂ)) :=
  DifferentiableLines.compactSpace_complex_points_of_proper

end GlobalTheory.CompanionTheory.Gaga
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionAdditive
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem hasDerivAt_exp_entries (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => (Matrix.of.symm (NormedSpace.exp (t • X)) : Fin n → Fin n → ℂ))
      (Matrix.of.symm X) 0 := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Fin n → Fin n → ℂ) :=
    { toFun := fun M => Matrix.of.symm M
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem hasDerivAt_orbit {G : Set (Matrix (Fin n) (Fin n) ℂ)} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {v : H}
    {F : (Fin n → Fin n → ℂ) → H} (hF : ContDiff ℝ ∞ F) (hFG : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) :
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v)
      (fderiv ℝ F (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ)) (Matrix.of.symm X)) 0 := by
  have hfun : (fun t : ℝ => π (NormedSpace.exp (t • X)) v) =
      fun t : ℝ => F (Matrix.of.symm (NormedSpace.exp (t • X))) := by
    funext t
    have hmem : Matrix.of (Matrix.of.symm (NormedSpace.exp (t • X))) ∈ G := by
      rw [Matrix.of.apply_symm_apply]
      exact hX t
    simpa only [Matrix.of.apply_symm_apply] using hFG _ hmem
  rw [hfun]
  have hdiff : DifferentiableAt ℝ F (Matrix.of.symm (NormedSpace.exp ((0 : ℝ) • X))) :=
    (hF.differentiable (by simp)) _
  have h := hdiff.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp_entries X)
  rw [zero_smul, NormedSpace.exp_zero] at h
  exact h

theorem differentiableAt_orbit {G : Set (Matrix (Fin n) (Fin n) ℂ)} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) :
    DifferentiableAt ℝ (fun t : ℝ => π (NormedSpace.exp (t • X)) v) 0 := by
  obtain ⟨F, hF, hFG⟩ := hv
  exact (hasDerivAt_orbit hF hFG hX).differentiableAt

theorem dRep_linear : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {u v : H} (hu : IsSmoothVec G π u) (hv : IsSmoothVec G π v)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G),
    dRep π (X + Y) v = dRep π X v + dRep π Y v ∧ dRep π X (u + v) = dRep π X u + dRep π X v ∧
      ∀ c : ℂ, dRep π X (c • v) = c • dRep π X v := by
  intro n G H _ _ π hG _hrep u v hu hv X Y hX hY
  have hXY : X + Y ∈ HCSS.lieOf G := (lieOf_isLieSubalgebra hG).1 X Y hX hY
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨F, hF, hFG⟩ := hv
    simp only [dRep]
    rw [(hasDerivAt_orbit hF hFG hXY).deriv, (hasDerivAt_orbit hF hFG hX).deriv,
      (hasDerivAt_orbit hF hFG hY).deriv]
    exact (fderiv ℝ F (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ))).map_add
      (Matrix.of.symm X) (Matrix.of.symm Y)
  · simp only [dRep, map_add (f := _)]
    exact deriv_add (differentiableAt_orbit hu hX) (differentiableAt_orbit hv hX)
  · intro c
    simp only [dRep, map_smul]
    exact deriv_const_smul c (differentiableAt_orbit hv hX)

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionCommutator
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Bracket

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def rightMul (Y : Matrix (Fin n) (Fin n) ℂ) : (Fin n → Fin n → ℂ) →L[ℝ] (Fin n → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => Matrix.of.symm (Matrix.of z * Y)
      map_add' := fun x y => by
        ext a b
        simp [Matrix.mul_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        ext a b
        simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc] }

theorem rightMul_apply (Y : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → Fin n → ℂ) :
    rightMul Y z = Matrix.of.symm (Matrix.of z * Y) := rfl

open scoped Matrix.Norms.Operator in
theorem hasDerivAt_entry (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X)) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem hasDerivAt_curve (z : Fin n → Fin n → ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => (Matrix.of.symm (Matrix.of z * NormedSpace.exp (t • X)) : Fin n → Fin n → ℂ))
      (rightMul X z) 0 := by
  rw [hasDerivAt_pi]
  intro a
  rw [hasDerivAt_pi]
  intro b
  simp only [rightMul_apply, Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
  exact HasDerivAt.fun_sum (fun c _ => (hasDerivAt_entry X c b).const_mul (z a c))

def one : Fin n → Fin n → ℂ := Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ)

theorem of_one : Matrix.of (one (n := n)) = 1 := by exact Matrix.of.apply_symm_apply _

section Smooth

variable {G : Set (Matrix (Fin n) (Fin n) ℂ)} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {v : H}
  {F : (Fin n → Fin n → ℂ) → H}

theorem hasDerivAt_along (hG : IsLinRed G) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) {z : Fin n → Fin n → ℂ} (hz : Matrix.of z ∈ G) :
    HasDerivAt (fun t : ℝ => π (Matrix.of z * NormedSpace.exp (t • X)) v)
      (fderiv ℝ F z (rightMul X z)) 0 := by
  have hd : HasFDerivAt F (fderiv ℝ F z) (Matrix.of.symm (Matrix.of z * NormedSpace.exp ((0 : ℝ) • X))) := by
    have : (Matrix.of.symm (Matrix.of z * NormedSpace.exp ((0 : ℝ) • X)) : Fin n → Fin n → ℂ) = z := by
      simp
    rw [this]
    exact (hF.differentiable (by simp) z).hasFDerivAt
  have h := hd.comp_hasDerivAt (0 : ℝ) (hasDerivAt_curve z X)
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have hm : Matrix.of z * NormedSpace.exp (t • X) ∈ G := hG.mul_mem _ hz _ (hX t)
  have := hFv (Matrix.of.symm (Matrix.of z * NormedSpace.exp (t • X))) (by simpa only [Matrix.of.apply_symm_apply] using hm)
  simpa only [Matrix.of.apply_symm_apply, Function.comp_def] using this

theorem hasDerivAt_exp_along (hG : IsLinRed G) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) :
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (fderiv ℝ F one (rightMul X one)) 0 := by
  have h := hasDerivAt_along hG hF hFv hX (z := one) (by rw [of_one]; exact hG.one_mem)
  simpa [of_one] using h

theorem dRep_eq (hG : IsLinRed G) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) : dRep π X v = fderiv ℝ F one (rightMul X one) :=
  (hasDerivAt_exp_along hG hF hFv hX).deriv

theorem rep_dRep (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) {z : Fin n → Fin n → ℂ} (hz : Matrix.of z ∈ G) :
    π (Matrix.of z) (dRep π X v) = fderiv ℝ F z (rightMul X z) := by
  have h1 := hasDerivAt_exp_along hG hF hFv hX
  have h2 := ((π (Matrix.of z)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h3 := hasDerivAt_along hG hF hFv hX hz
  rw [dRep_eq hG hF hFv hX]
  refine HasDerivAt.unique ?_ h3
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have := hrep.2 _ hz _ (hX t)
  simp [this]

theorem dRep_dRep (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G) :
    dRep π X (dRep π Y v) =
      fderiv ℝ (fderiv ℝ F) one (rightMul X one) (rightMul Y one) +
        fderiv ℝ F one (rightMul Y (rightMul X one)) := by
  have hF1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_cast)
  have hdF : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) one) one :=
    (hF1.differentiable (by simp) one).hasFDerivAt
  have hG1 := hdF.clm_apply (rightMul Y).hasFDerivAt
  have hc := hasDerivAt_curve (one (n := n)) X
  have h0 : (Matrix.of.symm (Matrix.of (one (n := n)) * NormedSpace.exp ((0 : ℝ) • X)) : Fin n → Fin n → ℂ) = one := by
    simp [one]
  have h := hG1.comp_hasDerivAt_of_eq (0 : ℝ) hc h0.symm
  have h' : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) (dRep π Y v)) _ 0 :=
    h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
      have := rep_dRep hG hrep hF hFv hY (z := Matrix.of.symm (NormedSpace.exp (t • X)))
        (by simpa only [Matrix.of.apply_symm_apply] using hX t)
      simpa only [Matrix.of.apply_symm_apply, of_one, one_mul, Function.comp_def] using this)
  refine h'.deriv.trans ?_
  simp [add_comm]

end Smooth

theorem dRep_bracket {G : Set (Matrix (Fin n) (Fin n) ℂ)} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G) :
    dRep π (X * Y - Y * X) v = dRep π X (dRep π Y v) - dRep π Y (dRep π X v) := by
  obtain ⟨F, hF, hFv⟩ := hv
  have hZ : X * Y - Y * X ∈ HCSS.lieOf G := (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.lieOf_isLieSubalgebra hG).2.2.1 X Y hX hY
  have hsymm : IsSymmSndFDerivAt ℝ F one :=
    (hF.contDiffAt).isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 le_top)
  rw [dRep_dRep hG hrep hF hFv hX hY, dRep_dRep hG hrep hF hFv hY hX, dRep_eq hG hF hFv hZ,
    hsymm.eq (rightMul X one) (rightMul Y one), add_sub_add_left_eq_sub, ← map_sub]
  congr 1
  simp only [rightMul_apply, Matrix.of.apply_symm_apply, of_one, one_mul]
  ext a b
  rfl

theorem smooth_bracket : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G), dRep π (X * Y - Y * X) v = dRep π X (dRep π Y v) - dRep π Y (dRep π X v) :=
  fun hG hrep _ hv _ _ hX hY => dRep_bracket hG hrep hv hX hY

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Bracket

end
end

