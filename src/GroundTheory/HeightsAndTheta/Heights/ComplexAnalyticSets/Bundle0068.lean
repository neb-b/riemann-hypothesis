module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0058
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0055
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0045
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0047
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0051
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0056

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVanishNearPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

theorem VanishNearPoint.proof (hOpen : FiniteMapOpen.Statement) : VanishNearPoint.Statement := by
  classical
  intro n J f x hJ hx hf
  by_contra hfJ
  have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ.ne_top
  obtain ⟨d, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ (MvPolynomial (Fin n) ℂ ⧸ J)
  choose p hp using fun i => Ideal.Quotient.mk_surjective (g (X i))
  have hg : g = (Ideal.Quotient.mkₐ ℂ J).comp (aeval p) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [hp]
  subst hg
  let _ := ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)).toRingHom.toAlgebra
  have hint : IsIntegral (MvPolynomial (Fin d) ℂ) (Ideal.Quotient.mk J f) :=
    RingHom.IsIntegral.of_finite hfin _
  have hf0 : Ideal.Quotient.mk J f ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨h, hh, hh0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ideal.comap_ne_bot_of_integral_mem hf0 (Ideal.mem_span_singleton_self _) hint)
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hh
  obtain ⟨a, ha⟩ := hh
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hJmem : aeval p h - q * f ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, sub_eq_zero]
    exact ha.symm

  have hval : ∀ z ∈ zeroLocus J, eval (fun i => eval z (p i)) h = eval z q * eval z f := by
    intro z hz
    have h1 := hz _ hJmem
    rw [map_sub, map_mul, sub_eq_zero] at h1
    rw [← h1]
    have h2 := DFunLike.congr_fun (MvPolynomial.comp_aeval (R := ℂ) (aeval z : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) (f := p)) h
    rw [AlgHom.comp_apply] at h2
    exact h2.symm
  have hV := hOpen n d J p hJ hinj hfin x hx _ hf
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  apply hh0
  refine MvPolynomial.funext_set (fun i => Metric.ball (eval x (p i)) ε)
    (fun i => infinite_of_mem_nhds _ (Metric.ball_mem_nhds _ hε)) fun w hw => ?_
  rw [← ball_pi _ hε] at hw
  obtain ⟨z, ⟨hz, hzU⟩, rfl⟩ := hball hw
  rw [hval z hz, hzU hz, mul_zero, map_zero]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarietyMassLower
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory
open scoped ENNReal

noncomputable section

theorem VarietyMassLower.proof (hG : VarietyTangentGraphDense.Statement)
    (hL : TangentGraphLowerDensity.Statement) (hM : VarietyLelongMono.Statement) :
    VarietyMassLower.Statement := by
  intro n d J hJ hd R
  set τ := μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) with hτdef
  have hτ : 0 < τ := TangentGraphLowerDensity.unitBall_pos d
  set m : ℝ≥0∞ := min τ 1 with hmdef
  have hm0 : 0 < m := lt_min hτ one_pos
  have hmtop : m ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hmτ : m ≤ τ := min_le_left _ _
  have hmr : 0 < m.toReal := ENNReal.toReal_pos hm0.ne' hmtop
  refine ⟨(1 / 2) * (1 / 2) ^ (2 * d) * m.toReal, by positivity, fun z hz _ ρ hρ => ?_⟩
  obtain ⟨hρ0, -⟩ := hρ
  obtain ⟨b, I₀, Ω, V, g, w₀, hcard, hΩ, hV, hw₀, hg, hproj, hZV, htan, hdist⟩ :=
    hG n d J hJ hd z hz (ρ / 2) (by linarith)
  have hz₀ : g w₀ ∈ zeroSetEuc J := by
    have h : g w₀ ∈ g '' Ω := ⟨w₀, hw₀, rfl⟩
    rw [← hZV] at h
    exact h.1
  obtain ⟨r₀, hr₀, hlow⟩ := hL n d b I₀ (zeroSetEuc J) Ω V g w₀ hcard hΩ hV hw₀ hg hproj hZV htan
    (1 / 2) ⟨by norm_num, by norm_num⟩
  set t := min (r₀ / 2) (ρ / 2) with htdef
  have ht0 : 0 < t := lt_min (by linarith) (by linarith)
  have htr : t < r₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hts : t ≤ ρ / 2 := min_le_right _ _
  have h1 := hlow t ⟨ht0, htr⟩
  have h2 := hM n d J hJ hd (g w₀) hz₀ t (ρ / 2) ht0 hts
  have hsub : zeroSetEuc J ∩ Metric.ball (g w₀) (ρ / 2) ⊆ zeroSetEuc J ∩ Metric.ball z ρ :=
    Set.inter_subset_inter_right _ (Metric.ball_subset_ball' (by linarith))
  have h3 := measure_mono (μ := μH[((2 * d : ℕ) : ℝ)]) hsub
  have key : ENNReal.ofReal (t ^ (2 * d)) * (ENNReal.ofReal ((1 / 2) * (ρ / 2) ^ (2 * d)) * τ) ≤
      ENNReal.ofReal (t ^ (2 * d)) * μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball (g w₀) (ρ / 2)) := by
    calc ENNReal.ofReal (t ^ (2 * d)) * (ENNReal.ofReal ((1 / 2) * (ρ / 2) ^ (2 * d)) * τ)
        = ENNReal.ofReal ((ρ / 2) ^ (2 * d)) * (ENNReal.ofReal ((1 / 2) * t ^ (2 * d)) * τ) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
          ring
      _ ≤ ENNReal.ofReal ((ρ / 2) ^ (2 * d)) *
            μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball (g w₀) t) := by gcongr
      _ ≤ _ := h2
  have key' := (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 (pow_pos ht0 _)).ne'
    ENNReal.ofReal_ne_top).1 key
  have hc : (1 / 2) * (1 / 2) ^ (2 * d) * m.toReal * ρ ^ (2 * d) =
      ((1 / 2) * (ρ / 2) ^ (2 * d)) * m.toReal := by
    rw [div_pow, div_pow, one_pow]
    ring
  calc ENNReal.ofReal ((1 / 2) * (1 / 2) ^ (2 * d) * m.toReal * ρ ^ (2 * d))
      = ENNReal.ofReal ((1 / 2) * (ρ / 2) ^ (2 * d)) * m := by
        rw [hc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hmtop]
    _ ≤ ENNReal.ofReal ((1 / 2) * (ρ / 2) ^ (2 * d)) * τ := by gcongr
    _ ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball (g w₀) (ρ / 2)) := key'
    _ ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball z ρ) := h3

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarietySlabMeasure
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped ENNReal

noncomputable section

namespace VarietySlabMeasure

theorem isFiniteLinProj_of {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (h : ComplexSets.IsFiniteProjection J A) :
    IsFiniteLinProj J A :=
  ⟨h.injective, h.finite⟩

theorem fibreCount_le {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : J.IsPrime)
    (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) {U : Matrix (Fin n) (Fin n) ℂ}
    {s : Fin d → Fin n} (hA : ComplexSets.IsFiniteProjection J (U.submatrix s id))
    (B : Set (EuclideanSpace ℂ (Fin n))) (x : EuclideanSpace ℂ (Fin d)) :
    {z | z ∈ zeroSetEuc J ∩ B ∧ rowsProj U s z = x}.encard ≤
      ComplexSets.projDegree J (U.submatrix s id) := by
  obtain ⟨-, hfin, hle⟩ := ComplexSets.FibreBound.proof n d J _ hJ hd hA (WithLp.ofLp x)
  calc _ ≤ (ComplexSets.fibre J (U.submatrix s id) (WithLp.ofLp x)).encard := by
        refine Set.encard_le_encard_of_injOn (f := fun z : EuclideanSpace ℂ (Fin n) => WithLp.ofLp z)
          ?_ (fun a _ b _ h => WithLp.ofLp_injective 2 h)
        rintro z ⟨⟨hz, -⟩, hx⟩
        exact ⟨hz, congrArg WithLp.ofLp hx⟩
    _ = ((ComplexSets.fibre J (U.submatrix s id) (WithLp.ofLp x)).ncard : ℕ∞) :=
        hfin.cast_ncard_eq.symm
    _ ≤ _ := by exact_mod_cast hle

end VarietySlabMeasure

theorem VarietySlabMeasure.proof (hG : ComplexSets.FiniteProjectionsGeneric.Statement)
    (hW : VarietyProjectionMass.Statement) (hP : IndefiniteRowSideFullHecke.ComplexSets.PolySublevel.Statement) :
    VarietySlabMeasure.Statement := by
  classical
  intro n d J u hJ hdim hu R
  rcases hdim.lt_or_eq with hlt | heq
  · refine ⟨1, 1, one_pos, one_pos, fun ε _ _ => ?_⟩
    calc _ ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J) := measure_mono (by exact fun z hz => hz.1)
      _ = 0 := NullSmaller.proof n d J hlt
      _ ≤ _ := by simp
  obtain ⟨U, hU, hfin⟩ := (hG n d J hJ heq).2.2 1 (fun _ => 1)
  have hA : ∀ s : Fin d → Fin n, StrictMono s →
      ComplexSets.IsFiniteProjection J (U.submatrix s id) := fun s hs => by
    simpa using hfin 0 ⟨s, hs.injective⟩

  have hQ : ∀ s : Fin d → Fin n, ∃ Q : MvPolynomial (Fin d) ℂ, StrictMono s → Q ≠ 0 ∧
      ∀ z ∈ zeroSetEuc J, ‖z‖ ≤ R →
        ‖eval ((U.submatrix s id).mulVec fun j => z j) Q‖ ≤ ‖∑ j, u j * z j‖ := by
    intro s
    by_cases hs : StrictMono s
    · obtain ⟨Q, hQ0, hb⟩ := IndefiniteRowSideFullHecke.ComplexSets.SlabBound.affine n d J (U.submatrix s id) u hJ
        (VarietySlabMeasure.isFiniteLinProj_of (hA s hs)) hu
      obtain ⟨C, hC⟩ := hb R
      have hK : (0 : ℝ) < max C 1 := lt_max_of_lt_right one_pos
      refine ⟨MvPolynomial.C ((max C 1 : ℝ) : ℂ)⁻¹ * Q, fun _ => ⟨?_, fun z hz hzR => ?_⟩⟩
      · exact mul_ne_zero (by simpa using hK.ne') hQ0
      · rw [eval_mul, eval_C, norm_mul, norm_inv, Complex.norm_of_nonneg hK.le, inv_mul_le_iff₀ hK]
        exact (hC z hz hzR).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    · exact ⟨0, fun h => absurd h hs⟩
  choose Q hQ using hQ

  have hR' : ∀ s : Fin d → Fin n, ∃ R' : ℝ, 0 < R' ∧
      ∀ z : EuclideanSpace ℂ (Fin n), ‖z‖ ≤ R → ‖rowsProj U s z‖ < R' := by
    intro s
    have hc : Continuous (rowsProj U s) := by
      unfold rowsProj
      fun_prop
    obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : EuclideanSpace ℂ (Fin n)) R).exists_bound_of_continuousOn
      hc.continuousOn
    refine ⟨max K 0 + 1, by positivity, fun z hz => ?_⟩
    have := hK z (mem_closedBall_zero_iff.mpr hz)
    linarith [le_max_left K 0]
  choose R' hR'0 hR' using hR'

  have hS : ∀ s : Fin d → Fin n, ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ (StrictMono s → ∀ η : ℝ, 0 < η → η ≤ 1 →
      μH[((2 * d : ℕ) : ℝ)] {x : EuclideanSpace ℂ (Fin d) | x ∈ Metric.ball 0 (R' s) ∧
        ‖eval (fun i => x i) (Q s)‖ ≤ η} ≤ ENNReal.ofReal (C * η ^ α)) := by
    intro s
    by_cases hs : StrictMono s
    · obtain ⟨C, α, hC, hα, hb⟩ := hP d (Q s) (hQ s hs).1 (R' s) (hR'0 s)
      exact ⟨C, α, hC, hα, fun _ => hb⟩
    · exact ⟨1, 1, one_pos, one_pos, fun h => absurd h hs⟩
  choose C α hC hα hS using hS
  set T := Finset.univ.filter (fun s : Fin d → Fin n => StrictMono s) with hT

  obtain ⟨α₀, hα₀, hα₀le⟩ : ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ s ∈ T, α₀ ≤ α s := by
    by_cases hne : T.Nonempty
    · exact ⟨T.inf' hne α, (Finset.lt_inf'_iff hne).2 fun s _ => hα s,
        fun s hs => Finset.inf'_le _ hs⟩
    · exact ⟨1, one_pos, fun s hs => absurd ⟨s, hs⟩ hne⟩
  set N : (Fin d → Fin n) → ℕ := fun s => ComplexSets.projDegree J (U.submatrix s id)
  have hNC : 0 ≤ ∑ s ∈ T, (N s : ℝ) * C s :=
    Finset.sum_nonneg fun s _ => mul_nonneg (Nat.cast_nonneg _) (hC s).le
  refine ⟨∑ s ∈ T, (N s : ℝ) * C s + 1, α₀, by linarith, hα₀, fun ε hε hε1 => ?_⟩
  set B : Set (EuclideanSpace ℂ (Fin n)) := {z | ‖z‖ ≤ R ∧ ‖∑ j, u j * z j‖ ≤ ε}
  have hB : MeasurableSet B := by
    have hc : Continuous fun z : EuclideanSpace ℂ (Fin n) => ‖∑ j, u j * z j‖ := by fun_prop
    exact (measurableSet_le continuous_norm.measurable measurable_const).inter
      (measurableSet_le hc.measurable measurable_const)
  have hεα : 0 < ε ^ α₀ := Real.rpow_pos_of_pos hε _
  have hterm : ∀ s ∈ T,
      (⨆ x : EuclideanSpace ℂ (Fin d),
          (({z | z ∈ zeroSetEuc J ∩ B ∧ rowsProj U s z = x}.encard : ℕ∞) : ℝ≥0∞)) *
          μH[((2 * d : ℕ) : ℝ)] (rowsProj U s '' (zeroSetEuc J ∩ B)) ≤
        ENNReal.ofReal ((N s : ℝ) * C s * ε ^ α₀) := by
    intro s hs
    have hs' : StrictMono s := (Finset.mem_filter.mp hs).2
    rw [mul_assoc, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    gcongr
    · refine iSup_le fun x => ?_
      have := VarietySlabMeasure.fibreCount_le hJ heq (hA s hs') B x
      exact_mod_cast ENat.toENNReal_le.mpr this
    · calc _ ≤ μH[((2 * d : ℕ) : ℝ)] {x : EuclideanSpace ℂ (Fin d) | x ∈ Metric.ball 0 (R' s) ∧
            ‖eval (fun i => x i) (Q s)‖ ≤ ε} := by
            refine measure_mono ?_
            rintro _ ⟨z, ⟨hz, hzR, hzε⟩, rfl⟩
            exact ⟨mem_ball_zero_iff.mpr (hR' s z hzR), ((hQ s hs').2 z hz hzR).trans hzε⟩
        _ ≤ ENNReal.ofReal (C s * ε ^ α s) := hS s hs' ε hε hε1
        _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_ge hε hε1 (hα₀le s hs)) (hC s).le)
  calc μH[((2 * d : ℕ) : ℝ)] {z | z ∈ zeroSetEuc J ∧ ‖z‖ ≤ R ∧ ‖∑ j, u j * z j‖ ≤ ε}
        = μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ B) := rfl
    _ ≤ _ := hW n d J hJ heq U hU B hB
    _ ≤ ∑ s ∈ T, ENNReal.ofReal ((N s : ℝ) * C s * ε ^ α₀) := Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (∑ s ∈ T, (N s : ℝ) * C s * ε ^ α₀) :=
        (ENNReal.ofReal_sum_of_nonneg fun s _ => by have := hC s; positivity).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.sum_mul, add_mul, one_mul]
        linarith

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PZeroSetOpenMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Filter Topology

noncomputable section

theorem exists_eval_ne_zero_of_isOpen {d : ℕ} {P : MvPolynomial (Fin d) ℂ} (hP : P ≠ 0)
    {S : Set (Fin d → ℂ)} (hS : IsOpen S) (hne : S.Nonempty) : ∃ y ∈ S, eval y P ≠ 0 := by
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hS y₀ hy₀
  by_contra h
  push Not at h
  apply hP
  have hinf : ∀ i, (Metric.ball (y₀ i) r).Infinite := fun i =>
    infinite_of_mem_nhds (y₀ i) (Metric.ball_mem_nhds _ hr)
  refine (funext_set_iff (p := P) (q := 0) _ hinf).mpr fun y hy => ?_
  rw [map_zero]
  exact h y (hball (by rwa [ball_pi _ hr]))

theorem eval_linPoly {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (z : Fin n → ℂ) :
    (fun i => eval z (GroundTheory.Heights₂.Heights.ComplexSets.linPoly A i)) = A.mulVec z := by
  ext i
  simp [GroundTheory.Heights₂.Heights.ComplexSets.linPoly, Matrix.mulVec, dotProduct]

theorem finrank_real_fin_complex (d : ℕ) : Module.finrank ℝ (Fin d → ℂ) = 2 * d := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Complex.finrank_real_complex, smul_eq_mul, mul_comm]

theorem ZeroSetOpenMass.proof
    (hG : GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.Statement)
    (hD : GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.Statement)
    (hF : FiniteMapOpen.Statement) : ZeroSetOpenMass.Statement := by
  intro n d W hW hdim x O hO hxO hxZ
  obtain ⟨A, hA⟩ := (hG n d W hW hdim).2.1
  obtain ⟨P, hP0, hPcov⟩ := hD n d W A hW hdim hA
  have hopen := hF n d W (GroundTheory.Heights₂.Heights.ComplexSets.linPoly A) hW hA.injective hA.finite x hxZ O
    (hO.mem_nhds hxO)
  have hfun : (fun z : Fin n → ℂ => fun i => eval z (GroundTheory.Heights₂.Heights.ComplexSets.linPoly A i)) =
      fun z => A.mulVec z := funext (eval_linPoly A)
  rw [hfun, eval_linPoly A x] at hopen
  obtain ⟨y, hyS, hPy⟩ := exists_eval_ne_zero_of_isOpen hP0 isOpen_interior
    ⟨_, mem_interior_iff_mem_nhds.mpr hopen⟩
  obtain ⟨z, ⟨hzW, hzO⟩, hzy⟩ := interior_subset hyS
  subst hzy
  obtain ⟨-, -, hloc⟩ := hPcov _ hPy
  obtain ⟨U, V, g, hU, hzU, hV, hzV, hg, hgz, hAg, hZV⟩ := hloc z ⟨hzW, rfl⟩
  set U' := U ∩ g ⁻¹' (O ∩ V) with hU'def
  have hU' : IsOpen U' := hg.continuousOn.isOpen_inter_preimage hU (hO.inter hV)
  have hzU' : A.mulVec z ∈ U' := ⟨hzU, by simp only [Set.mem_preimage, hgz]; exact ⟨hzO, hzV⟩⟩
  have hsub : g '' U' ⊆ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ O := by
    rintro _ ⟨w, ⟨hwU, hwO, -⟩, rfl⟩
    have hw : g w ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ V := by
      rw [hZV]; exact Set.mem_image_of_mem g hwU
    exact ⟨hw.1, hwO⟩
  have himg : (fun z => A.mulVec z) '' (g '' U') = U' := by
    rw [Set.image_image]
    exact (Set.image_congr fun w (hw : w ∈ U') => hAg w hw.1).trans (Set.image_id' _)
  obtain ⟨K, hK⟩ : ∃ K, LipschitzWith K (fun z : Fin n → ℂ => A.mulVec z) :=
    ⟨_, (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).lipschitz⟩
  have hpos : 0 < μH[((2 * d : ℕ) : ℝ)] U' := by
    rw [← finrank_real_fin_complex d]
    exact hU'.measure_pos _ ⟨_, hzU'⟩
  have hle := hK.hausdorffMeasure_image_le (by positivity : (0 : ℝ) ≤ ((2 * d : ℕ) : ℝ)) (g '' U')
  rw [himg] at hle
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  refine pos_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, mul_zero] at hle
  exact hpos.ne' (nonpos_iff_eq_zero.mp hle)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PlaneIdealTwoOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory

noncomputable section

theorem mdisc_const_smul {D : ℕ} (c : ℂ) (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    ReciprocityTheory.AnForm.mdisc (fun k => c • A k) = c ^ D * ReciprocityTheory.AnForm.mdisc A := by
  unfold ReciprocityTheory.AnForm.mdisc
  simp only [← Finset.smul_sum, Matrix.det_smul, Fintype.card_fin, Finset.mul_sum]
  exact Finset.sum_congr rfl fun S _ => by ring

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchAwayFromRim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

noncomputable section

def BranchAwayFromRim.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u p x : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → GroundTheory.Heights₂.Heights.VarBranch J k p),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (k : ℕ) → linForm u ∉ J →
    (∃ N ∈ 𝓝 x, GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) →
    (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {y | GroundTheory.Heights₂.Heights.linEval u y = 0}) →
    ∀ b, ∃ ε > 0, ∃ ρ < (γ b).radius, ∀ τ ∈ Metric.ball 0 (γ b).radius,
      (γ b).toFun τ ∈ Metric.ball x ε → ‖τ‖ ≤ ρ

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartIntCountAdd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def ChartIntCountAdd.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (E : ℕ → Set (Fin n → ℂ)),
    W.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) → IsFiniteProjection W A →
    Continuous f → HasCompactSupport f → (∀ k, SmoothNear (zeroSet W) (φ k)) →
    (∀ i, MeasurableSet (E i)) → Pairwise (Function.onFun Disjoint E) →
      HasSum (fun i => chartInt W A ((E i).indicator f) φ) (chartInt W A ((⋃ i, E i).indicator f) φ)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveBranchLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets Filter Topology

noncomputable section

def CurveBranchLength.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (u q : Fin n → ℂ) (m : ℕ)
    (c : Fin m → VarBranch I 1 q) (ord : Fin m → ℕ),
    IsRadicalAt I q →
    (∃ N ∈ 𝓝 q, zeroSet I ∩ N ⊆ ⋃ b, (c b).image) →
    (∀ b b', b ≠ b' → (c b).image ∩ (c b').image ⊆ {x | linEval u x = 0}) →
    (∀ b, VanishesToOrder (fun t => linEval u ((c b).toFun t)) (c b).radius (ord b)) →
      localMult (I ⊔ Ideal.span {linForm u}) (RingHom.ker (eval q)) = ∑ b, ord b

end

end GroundTheory.Heights₂.Heights
end

