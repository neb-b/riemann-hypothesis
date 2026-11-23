module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsNormEmbId
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.HsTrace
section
noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta GlobalTheory.SmVec GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace

namespace PositivityTheory.UnitaryDecomposition.X4

theorem hs_trace {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : (hs X : ℂ) = trace (Xᴴ * X) := by
  simp only [hs, trace, diag_apply, Matrix.mul_apply, conjTranspose_apply]
  rw [Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem jm_ct {m : ℕ} (ε : Fin m → Bool) : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, diagonal_conjTranspose]
  congr 1; funext a
  simp only [Pi.star_apply]; split_ifs <;> simp

theorem stab : ∀ {n r : ℕ} {ε : Fin n → Bool} {ε' : Fin r → Bool} (ι : UJ ε' →* UJ ε) (z : Fin n → ℂ), IsStdStab ε ε' ι z → IsNormEmb ι ∧ (∀ h, hs (umat (ι h)) = hs (umat h) + 1) ∧ ∀ g : UJ ε, umat g *ᵥ z = z → ∃ h, ι h = g := by
  intro n r ε ε' ι z ⟨F, hF, FF, Fz, hz⟩
  set Z : Matrix (Fin n) Unit ℂ := replicateCol Unit z with hZ
  have col : ∀ {k : ℕ} (M : Matrix (Fin k) (Fin n) ℂ), M * Z = replicateCol Unit (M *ᵥ z) := fun M => by
    ext i j; simp [hZ, Matrix.mul_apply, mulVec, dotProduct]
  have FZ : Fᴴ * Z = 0 := by rw [col, Fz]; ext; simp
  have ZF : Zᴴ * F = 0 := by simpa using congrArg conjTranspose FZ
  have ZZ : Zᴴ * Z = 1 := by
    ext i j
    have : ((nsq z : ℝ) : ℂ) = 1 := by rw [hz]; simp
    simp only [hZ, Matrix.mul_apply, conjTranspose_apply, replicateCol_apply, Complex.star_def, Complex.conj_mul', Subsingleton.elim i j,
      one_apply_eq]
    rw [← this, GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq]; push_cast; rfl
  have S : F * Fᴴ + Z * Zᴴ = 1 := by
    have e : Fin n ≃ Fin r ⊕ Unit := Fintype.equivOfCardEq (by simp [← hF.codim])
    have h1 : (fromCols F Z)ᴴ * fromCols F Z = 1 := by
      rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols, FF, FZ, ZF, ZZ, fromBlocks_one]
    have h2 := (mul_eq_one_comm_of_equiv e.symm).1 h1
    rwa [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows] at h2
  have FJZ : Fᴴ * Jm ε * Z = 0 := by rw [col, hF.perp]; ext; simp
  have ZJF : Zᴴ * Jm ε * F = 0 := by
    have := congrArg conjTranspose FJZ
    simpa [jm_ct, Matrix.mul_assoc] using this
  have ZJZ : Zᴴ * Jm ε * Z = 1 := by
    ext i j
    rw [Matrix.mul_assoc, col, Subsingleton.elim i j, one_apply_eq, ← hF.one]
    simp [hZ, mul_apply, dotProduct]
  have JZ : Jm ε * Z = Z := by
    rw [← Matrix.one_mul (Jm ε * Z), ← S, Matrix.add_mul, Matrix.mul_assoc F, Matrix.mul_assoc Z, ← Matrix.mul_assoc Fᴴ,
      ← Matrix.mul_assoc Zᴴ, FJZ, ZJZ]; simp
  have A : ∀ h, umat (ι h) = F * umat h * Fᴴ + Z * Zᴴ := fun h => by
    rw [← Matrix.mul_one (umat (ι h)), ← S, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hF.act, col, hF.fix]
  have hsF : ∀ M : Matrix (Fin r) (Fin r) ℂ, trace ((F * M * Fᴴ)ᴴ * (F * M * Fᴴ)) = trace (Mᴴ * M) := fun M => by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Fᴴ F, FF, Matrix.one_mul, trace_mul_comm]
    simp only [Matrix.mul_assoc, FF, Matrix.mul_one]
  have cA : Continuous fun h => umat (ι h) := by
    simp only [A]
    exact ((continuous_const.matrix_mul Formalism.MainNotions.BridgeCSchur.continuous_umat).matrix_mul continuous_const).add continuous_const
  refine ⟨⟨?_, fun h => ?_⟩, fun h => ?_, fun g hg => ?_⟩
  · refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨cA, ?_⟩)
    have : Continuous fun h => umat (ι h⁻¹) := cA.comp continuous_inv
    exact this.congr fun h => by rw [map_inv]; rfl
  · have : umat (ι h) - 1 = F * (umat h - 1) * Fᴴ := by
      rw [A, ← S, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]; abel
    exact_mod_cast (by rw [hs_trace, hs_trace, this, hsF] : (hs (umat (ι h) - 1) : ℂ) = hs (umat h - 1))
  · have : (hs (umat (ι h)) : ℂ) = hs (umat h) + 1 := by
      rw [hs_trace, hs_trace, A, conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, trace_add, trace_add,
        trace_add, hsF]
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Fᴴ Z, FZ, ← Matrix.mul_assoc Zᴴ F, ZF, ← Matrix.mul_assoc Zᴴ Z, ZZ, Matrix.one_mul]
      simp [trace_mul_comm Z, ZZ]
    exact_mod_cast this
  · have gZ : umat g * Z = Z := by rw [col, hg]
    have gJ : (umat g)ᴴ * Jm ε * umat g = Jm ε := g.2
    have ZgF : Zᴴ * (umat g * F) = 0 := by
      have h1 : Zᴴ = Zᴴ * (umat g)ᴴ * Jm ε := by
        rw [← conjTranspose_mul, gZ, ← jm_ct ε, ← conjTranspose_mul, JZ]
      calc _ = Zᴴ * (umat g)ᴴ * Jm ε * (umat g * F) := by rw [← h1]
        _ = Zᴴ * ((umat g)ᴴ * Jm ε * umat g) * F := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [gJ, ZJF]
    have gF : umat g * F = F * (Fᴴ * (umat g * F)) := by
      conv_lhs => rw [← Matrix.one_mul (umat g * F), ← S, Matrix.add_mul, Matrix.mul_assoc Z, ZgF, Matrix.mul_zero, add_zero,
        Matrix.mul_assoc]
    set h := Fᴴ * (umat g * F) with hh
    have hU : inUJ ε' h := by
      show hᴴ * Jm ε' * h = Jm ε'
      calc hᴴ * Jm ε' * h = (F * h)ᴴ * Jm ε * (F * h) := by
            rw [← hF.gram]; simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = Fᴴ * ((umat g)ᴴ * Jm ε * umat g) * F := by rw [← gF]; simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [gJ, hF.gram]
    refine ⟨indefiniteUnitaryMk ε' h hU, Subtype.ext (Units.ext ?_)⟩
    show umat _ = umat g
    rw [A, show umat (indefiniteUnitaryMk ε' h hU) = h from rfl, ← gF]
    conv_rhs => rw [← Matrix.mul_one (umat g), ← S, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, gZ]

end PositivityTheory.UnitaryDecomposition.X4
end
end

-- bundled from Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.Unfold
section
open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta GlobalTheory.SmVec GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace

namespace PositivityTheory.UnitaryDecomposition.X4

theorem unfold : ∀ {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure] (ι : H →* G), Continuous ι → ∀ (F : G → ENNReal), Measurable F → ∀ (S C : Set G) (U : Set H), MeasurableSet S → MeasurableSet C → MeasurableSet U → (∀ g ∈ S, ∃ h₀ : H, ∀ u ∈ U, (ι (h₀ * u))⁻¹ * g ∈ C) → ∀ s : ENNReal, (∀ c ∈ C, ∫⁻ h, F (ι h * c) ∂ν ≤ s) → ν U * ∫⁻ g in S, F g ∂μ ≤ μ C * s := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ ι hι F hF S C U hS hC hU hSC s hs
  have hind : Measurable (C.indicator (1 : G → ENNReal)) := measurable_one.indicator hC
  have hin : ∀ g : G, Measurable (fun h : H => C.indicator (1 : G → ENNReal) ((ι h)⁻¹ * g)) :=
    fun g => hind.comp (((hι.inv).mul continuous_const).measurable)
  have step1 : ∀ g ∈ S, ν U ≤ ∫⁻ h, C.indicator (1 : G → ENNReal) ((ι h)⁻¹ * g) ∂ν := by
    intro g hg
    obtain ⟨h₀, hh₀⟩ := hSC g hg
    have hT : MeasurableSet ((fun h => h₀⁻¹ * h) ⁻¹' U) := measurable_const_mul h₀⁻¹ hU
    calc ν U = ν ((fun h => h₀⁻¹ * h) ⁻¹' U) := (measure_preimage_mul ν h₀⁻¹ U).symm
      _ = ∫⁻ h, ((fun h => h₀⁻¹ * h) ⁻¹' U).indicator 1 h ∂ν := (lintegral_indicator_one hT).symm
      _ ≤ ∫⁻ h, C.indicator (1 : G → ENNReal) ((ι h)⁻¹ * g) ∂ν := by
        refine lintegral_mono fun h => ?_
        by_cases hm : h ∈ (fun h => h₀⁻¹ * h) ⁻¹' U
        · have hc := hh₀ _ hm
          simp only [mul_inv_cancel_left] at hc
          rw [Set.indicator_of_mem hm, Set.indicator_of_mem hc]
          simp
        · rw [Set.indicator_of_notMem hm]
          exact bot_le
  calc ν U * ∫⁻ g in S, F g ∂μ = ∫⁻ g in S, ν U * F g ∂μ := (lintegral_const_mul _ hF).symm
    _ = ∫⁻ g, S.indicator (fun g => ν U * F g) g ∂μ := (lintegral_indicator hS _).symm
    _ ≤ ∫⁻ g, ∫⁻ h, C.indicator (1 : G → ENNReal) ((ι h)⁻¹ * g) * F g ∂ν ∂μ := by
        refine lintegral_mono fun g => ?_
        by_cases hg : g ∈ S
        · rw [Set.indicator_of_mem hg, lintegral_mul_const _ (hin g)]
          exact mul_le_mul' (step1 g hg) le_rfl
        · rw [Set.indicator_of_notMem hg]
          exact bot_le
    _ = ∫⁻ h, ∫⁻ g, C.indicator (1 : G → ENNReal) ((ι h)⁻¹ * g) * F g ∂μ ∂ν := by
        refine lintegral_lintegral_swap ?_
        exact ((hind.comp (((hι.comp continuous_snd).inv.mul continuous_fst).measurable)).mul
          (hF.comp measurable_fst)).aemeasurable
    _ = ∫⁻ h, ∫⁻ c, C.indicator (1 : G → ENNReal) c * F (ι h * c) ∂μ ∂ν := by
        refine lintegral_congr fun h => ?_
        rw [← lintegral_mul_left_eq_self _ (ι h)]
        simp only [inv_mul_cancel_left]
    _ = ∫⁻ c, ∫⁻ h, C.indicator (1 : G → ENNReal) c * F (ι h * c) ∂ν ∂μ := by
        refine lintegral_lintegral_swap ?_
        exact ((hind.comp measurable_snd).mul
          (hF.comp ((hι.comp continuous_fst).mul continuous_snd).measurable)).aemeasurable
    _ = ∫⁻ c, C.indicator (1 : G → ENNReal) c * ∫⁻ h, F (ι h * c) ∂ν ∂μ := by
        refine lintegral_congr fun c => ?_
        exact lintegral_const_mul _ (hF.comp (hι.mul continuous_const).measurable)
    _ ≤ ∫⁻ c, C.indicator (1 : G → ENNReal) c * s ∂μ := by
        refine lintegral_mono fun c => ?_
        by_cases hc : c ∈ C
        · rw [Set.indicator_of_mem hc]
          simpa using hs c hc
        · rw [Set.indicator_of_notMem hc]
          simp
    _ = μ C * s := by
        rw [lintegral_mul_const _ hind, lintegral_indicator_one hC]

end PositivityTheory.UnitaryDecomposition.X4
end

