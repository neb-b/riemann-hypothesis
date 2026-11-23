module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.HomOmZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.UnitarySimilitudeGroupIsSmoothCmDatum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpacePointLogEstimate

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.LeExpSelf
section
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af

private theorem le_exp_self' (x : ℝ) : x ≤ Real.exp x := by
  have := Real.add_one_le_exp x
  linarith

theorem UpperTheory.V.Lit.Geo.prim :
    Prim := by
  intro E _ _ _ a U hU Ξ f Y C c f₀ hS q η hη hM
  have hc := hS.c_pos
  have hC : 0 ≤ C := (abs_nonneg _).trans (hS.near 1 0 1 (by simp) (by simp))
  have hq := (qhtFacts E a).1
  have hqf : ∀ (g : GA E a) (x : ℝ), f g ≤ x → qht g ≤ Real.exp (C * (1 + x)) := fun g x hx =>
    (Real.le_exp_log _).trans (Real.exp_le_exp.2 ((hS.le_f g).trans (mul_le_mul_of_nonneg_left (by linarith) hC)))
  obtain ⟨B, hB, hstep⟩ := oneStep E a U Ξ (-Y) C hS.fld.neg q
  obtain ⟨N, C', hC', hgr⟩ := (bdGrowth E a Ξ (q + 1) _).1 hM
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = |f₀| + C := ⟨_, rfl⟩
  have hf0 := le_abs_self f₀
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨M₀, hM₀, hcp⟩ := bdCompact E a U hU Ξ q η hη (Real.exp (C * (1 + K)))
  have p1 : 0 ≤ (N : ℝ) * C * (1 + K + C) := by positivity
  have p2 : 0 ≤ (N : ℝ) * C * c := by positivity
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = M₀ + 2 * B + C' + N * C * (1 + K + C) + N * C * c := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hneg : ∀ (g : GA E a) (t : ℝ), (1 : Matrix (Fin a) (Fin a) (Cinf E)) + t • ((-Y) g).1 = 1 + (-t) • (Y g).1 :=
    fun g t => by
      rw [neg_smul]
      exact congrArg (1 + ·) (smul_neg t (Y g).1)
  have hnear : ∀ (g : GA E a) (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → ∀ h : GL (Fin a) (Cinf E),
      h.val * star h.val = 1 + t • ((-Y) g).1 → f (g * infGL E a h) ≤ f g + C := fun g t ht h hh => by
    have := (abs_le.1 (hS.near g (-t) h (by rw [abs_neg, abs_of_nonneg ht.1]; exact ht.2) (hh.trans (hneg g t)))).2
    linarith
  have main : ∀ n : ℕ, ∃ η' : Co Ξ q, IsLev U Ξ η' ∧ dCo (smLie Ξ) η' = dCo (smLie Ξ) η ∧
      ∀ g : GA E a, f g ≤ K + n * c → Bd η' g (Real.exp (D * (n + 1))) := by
    intro n
    induction n with
    | zero =>
      refine ⟨η, hη, rfl, fun g hg => (hcp g (hqf g K (by simpa using hg))).mono ?_⟩
      refine (le_exp_self' M₀).trans (Real.exp_le_exp.2 ?_)
      simp only [Nat.cast_zero, zero_add, mul_one]
      linarith
    | succ n ih =>
      obtain ⟨ζ, hζ, hd, hb⟩ := ih
      obtain ⟨ζ', hζ', hd', hb'⟩ := hstep ζ hζ
      refine ⟨ζ', hζ', hd'.trans hd, fun g hg => ?_⟩
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hnc : 0 ≤ (n : ℝ) * c := by positivity
      push_cast at hg ⊢
      refine (hb' g (Real.exp (D * (n + 1))) (Real.exp (D * (n + 1))) (Real.exp_pos _).le (Real.exp_pos _).le
        (fun h hh => hb _ ?_) (fun t ht h hh => ?_)).mono ?_
      · by_cases hf : f₀ ≤ f g
        · have := hS.down g h hf (hh.trans (sub_eq_add_neg _ _).symm)
          linarith
        · have := hnear g 1 ⟨zero_le_one, le_rfl⟩ h (by rw [one_smul]; exact hh)
          have := not_le.1 hf
          linarith
      · rw [hd]
        refine (hgr _).mono ?_
        have h1 := hqf (g * infGL E a h) (K + (n + 1) * c + C) (by have := hnear g t ht h hh; linarith)
        have h2 := pow_le_pow_left₀ (zero_le_one.trans (hq _)) h1 N
        rw [← Real.exp_nat_mul] at h2
        refine (mul_le_mul (le_exp_self' C') h2 (pow_nonneg (zero_le_one.trans (hq _)) _) (Real.exp_pos _).le).trans ?_
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have e : D * (n + 1) = C' + N * (C * (1 + (K + (n + 1) * c + C))) +
            ((M₀ + 2 * B) * (n + 1) + (C' + N * C * (1 + K + C)) * n) := by rw [hD]; ring
        rw [e]
        exact le_add_of_nonneg_right (by positivity)
      · have e : Real.exp (D * (n + 1 + 1)) = Real.exp D * Real.exp (D * (n + 1)) := by
          rw [← Real.exp_add]; congr 1; ring
        have h2 : 2 * B ≤ Real.exp D := le_trans (by linarith) (le_exp_self' D)
        rw [e]
        have := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (D * (n + 1))).le
        linarith
  refine ⟨D, hD0, fun n => ?_⟩
  obtain ⟨ζ, h1, h2, h3⟩ := main n
  exact ⟨ζ, h1, h2, fun g hg => h3 g (by linarith)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.StepEx
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo

private theorem trF_smul {E : Type} [Field E] [NumberField E] {a : ℕ} (s : ℝ) (X Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    trF X (s • Y) = s * trF X Y := by
  simp [trF, Finset.mul_sum]

theorem UpperTheory.V.Lit.Geo.stepEx :
    StepEx := by
  intro E _ _ _ a ha U hU
  obtain ⟨L, hL, hUL⟩ := UpperTheory.unitaryGroup_lieAlgebra_eq_skewHermitian E a U hU
  obtain ⟨ε₁, C₁, hε₁, hroot⟩ := UpperTheory.unitarySimilitudeGroup_isSmooth_cmDatum E a
  obtain ⟨hI1, hI2, hI3⟩ := UpperTheory.lattice_point_count_bound E a ha L
  have hK := UpperTheory.hermitian_gaussian_moment_bound E a ha L hL
  obtain ⟨hT, hM⟩ := UpperTheory.hermitian_space_geometric_estimate E a ha L hL
  obtain ⟨hS1, φ, hφ, hS2⟩ := UpperTheory.realLieGroup_charts_smooth E a ha L hL
  obtain ⟨hB1, hB2⟩ := UpperTheory.lieDerivative_isDerivation_smoothFunctions E a {f | ∃ P ∈ poly E a, f = mean L P} (by
    rintro _ ⟨P, hP, rfl⟩
    exact ⟨(hM P hP).2, hS1 P hP⟩)
  obtain ⟨hD1, ⟨B, hB, hD2⟩, hD3⟩ := UpperTheory.hermitian_trace_form_estimate E a ha L hL
  obtain ⟨C₂, ε₂, hC₂, hε₂, hTay⟩ := UpperTheory.hermitian_trace_form_entry_estimate E a ha L hL
  obtain ⟨C₃, hC₃⟩ := UpperTheory.hermitian_space_log_estimate E a ha L hL
  obtain ⟨C₄, hC₄⟩ := UpperTheory.hermitian_space_point_log_estimate E a ha L hL
  obtain ⟨c₀, f₀, hc₀, hG⟩ := UpperTheory.traceForm_posDef_of_totallyReal E a ha L hL
  obtain ⟨δ, hδ, hδ1, hδ2, hδ3⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * B ≤ ε₁ ∧ δ * B ≤ ε₂ ∧ C₂ * (δ * B) ^ 2 ≤ δ * c₀ := by
    have hp : 0 < C₂ * B ^ 2 + 1 := by positivity
    refine ⟨min (min (ε₁ / B) (ε₂ / B)) (c₀ / (C₂ * B ^ 2 + 1)), by positivity, ?_, ?_, ?_⟩
    · exact (le_div_iff₀ hB).1 ((min_le_left _ _).trans (min_le_left _ _))
    · exact (le_div_iff₀ hB).1 ((min_le_left _ _).trans (min_le_right _ _))
    · set d := min (min (ε₁ / B) (ε₂ / B)) (c₀ / (C₂ * B ^ 2 + 1))
      have h0 : 0 < d := by positivity
      have h1 : d * (C₂ * B ^ 2 + 1) ≤ c₀ := (le_div_iff₀ hp).1 (min_le_right _ _)
      nlinarith
  have hf0 : ∀ g, 0 ≤ fn L g := fun g => Real.log_nonneg (hT g).1
  have hq0 : ∀ g : GA E a, 0 ≤ Real.log (qht g) := fun g => Real.log_nonneg
    (le_ciInf fun _ => GroundTheory.Automorphic.AutomorphicForm.one_le_height _)
  have hn : ∀ g (t : ℝ), |t| ≤ 1 → ‖toL (t • ((-δ) • dev L g).1)‖ ≤ δ * B := fun g t ht => by
    change ‖t • (-δ) • toL (dev L g).1‖ ≤ _
    rw [norm_smul, norm_smul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hδ]
    have h1 := mul_le_mul_of_nonneg_left (hD2 g).2.1 hδ.le
    have h2 : 0 ≤ δ * ‖toL (dev L g).1‖ := by positivity
    nlinarith
  have key : ∀ g (t : ℝ) (h : GL (Fin a) (Cinf E)), |t| ≤ 1 → h.val * star h.val = 1 + t • ((-δ) • dev L g).1 →
      |fn L (g * infGL E a h) - fn L g - Real.pi * t * δ * trF (dev L g).1 (dev L g).1| ≤ δ * c₀ := fun g t h ht hh => by
    have h0 : ell E a (toL (t • ((-δ) • dev L g).1)) = 0 := by
      change ell E a (t • (-δ) • toL (dev L g).1) = 0
      rw [map_smul, map_smul, (hD3 g).1, smul_zero, smul_zero]
    have h1 := hTay g _ h h0 ((hn g t ht).trans hδ2) hh
    have h2 : trF (mom L g).1 (t • ((-δ) • dev L g).1) = -(t * δ * trF (dev L g).1 (dev L g).1) := by
      change trF (mom L g).1 (t • (-δ) • (dev L g).1) = _
      rw [trF_smul, trF_smul, (hD3 g).2]
      ring
    rw [h2] at h1
    have h3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hn g t ht) 2) hC₂
    refine le_trans (le_of_eq ?_) (h1.trans (h3.trans hδ3))
    congr 1
    ring
  have hπ : 0 ≤ Real.pi - 2 := by linarith [Real.pi_gt_three]
  refine ⟨fn L, fun g => (-δ) • dev L g, max (max C₁ (Real.pi * δ * B + δ * c₀)) (max C₃ C₄), δ * c₀, f₀,
    ⟨mul_pos hδ hc₀, ⟨φ, hφ, hB2 φ hS2⟩, fun γ t g => (hI1 γ t g).1, fun k g => ?_, fun u hu g => (hI2 U hU hUL u hu g).1,
      hf0, fun g => ?_, fun g => ?_, fun i j w => ?_, fun γ t g => ?_, fun k g => ?_, fun u hu g => ?_, fun g t ht => ?_,
      fun g h hg hh => ?_, fun g h hg hh => ?_, fun g t h ht hh => ?_⟩⟩
  · rw [fn, hI3, fn]
  · exact (hC₃ g).trans (mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_left _ _)) (by linarith [hq0 g]))
  · exact (hC₄ g).trans (mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_right _ _)) (by linarith [hf0 g]))
  · obtain ⟨ψ, h1, h2⟩ := hB1 _ (Subalgebra.smul_mem _ (hD1 i j w) ((-δ : ℝ) : ℂ))
    exact ⟨ψ, fun g => by rw [h1]; rfl, h2⟩
  · rw [(hI1 γ t g).2]
  · rw [← hK k g]
    exact Subtype.ext (by simp [adHerm])
  · rw [(hI2 U hU hUL u hu g).2]
  · obtain ⟨h, h1, h2, h3⟩ := hroot (t • (-δ) • dev L g) ((hn g t ht).trans hδ1)
    exact ⟨h, h1, h2.trans (le_max_of_le_left (le_max_left _ _)), h3.trans (le_max_of_le_left (le_max_left _ _))⟩
  · have h1 := (abs_le.1 (key g 1 h (by simp) (by rwa [one_smul]))).1
    have h2 := mul_le_mul_of_nonneg_left (hG g hg) hδ.le
    have h3 := mul_pos hδ hc₀
    nlinarith
  · have h1 := (abs_le.1 (key g (-1) h (by simp) (by rwa [neg_one_smul, ← sub_eq_add_neg]))).2
    have h2 := mul_le_mul_of_nonneg_left (hG g hg) hδ.le
    have h3 := mul_pos hδ hc₀
    nlinarith
  · refine le_max_of_le_left (le_max_of_le_right ?_)
    have h1 := key g t h ht hh
    have h2 : |Real.pi * t * δ * trF (dev L g).1 (dev L g).1| ≤ Real.pi * δ * B := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hδ]
      have := (hD2 g).2.2
      calc Real.pi * |t| * δ * |trF (dev L g).1 (dev L g).1| ≤ Real.pi * 1 * δ * B := by
            have := Real.pi_pos
            gcongr
        _ = _ := by ring
    have h3 := abs_add_le (fn L (g * infGL E a h) - fn L g - Real.pi * t * δ * trF (dev L g).1 (dev L g).1)
      (Real.pi * t * δ * trF (dev L g).1 (dev L g).1)
    rw [sub_add_cancel] at h3
    linarith
end

