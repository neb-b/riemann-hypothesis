module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.TransportGeo
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0009
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.ContinuousBlkWConj
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ReproducingFormulaClosedInvariant
section
noncomputable section

open Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool}

theorem convolution_integral_fubini {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (f : L2 ε)
    (hFc : Continuous (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)))
    (hF2 : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε))
    (hγ : MemLp (fGam ε f) 2 (Formalism.REAL.muG ε)) {N : Set (Formalism.REAL.UJ ε)}
    (hNf : Formalism.REAL.muG ε N ≠ ∞) (x : Formalism.REAL.UJ ε) :
    ∫ z in N, fPhi ε F f (z * x) ∂(Formalism.REAL.muG ε) =
      ∫ y, (∫ z in N, F (Formalism.MainNotions.S.umat (z * y)) ∂(Formalism.REAL.muG ε)) * fGam ε f (y⁻¹ * x)
        ∂(Formalism.REAL.muG ε) := by
  set μ := Formalism.REAL.muG ε with hμ
  have e1 : (fun z => fPhi ε F f (z * x)) =
      fun z => ∫ y, F (Formalism.MainNotions.S.umat (z * y)) * fGam ε f (y⁻¹ * x) ∂μ := by
    funext z
    unfold fPhi
    rw [← integral_mul_left_eq_self (fun y => F (Formalism.MainNotions.S.umat y) * fGam ε f (y⁻¹ * (z * x))) z]
    congr 1
    funext y
    congr 2
    group
  rw [e1]
  set G2 : Formalism.REAL.UJ ε → Formalism.REAL.UJ ε → ℂ :=
    fun z y => F (Formalism.MainNotions.S.umat (z * y)) * fGam ε f (y⁻¹ * x) with hG2
  have hcont : Continuous (Function.uncurry G2) := by
    show Continuous fun p : Formalism.REAL.UJ ε × Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat (p.1 * p.2)) * fGam ε f (p.2⁻¹ * x)
    exact (hFc.comp continuous_mul).mul ((matrix_coefficient_continuous ε f).comp (continuous_snd.inv.mul continuous_const))
  have hB : MemLp (fun y => fGam ε f (y⁻¹ * x)) 2 μ :=
    hγ.comp_measurePreserving ((measurePreserving_mul_right ε x).comp (Measure.measurePreserving_inv μ))
  have hA : ∀ z, MemLp (fun y => F (Formalism.MainNotions.S.umat (z * y))) 2 μ :=
    fun z => hF2.comp_measurePreserving (measurePreserving_mul_left μ z)
  have hint : Integrable (Function.uncurry G2) ((μ.restrict N).prod μ) := by
    rw [integrable_prod_iff hcont.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun z => (hA z).integrable_mul hB, ?_⟩
    have : IsFiniteMeasure (μ.restrict N) := isFiniteMeasure_restrict.2 hNf
    refine Integrable.of_bound hcont.aestronglyMeasurable.norm.integral_prod_right'
      ((∫ y, ‖F (Formalism.MainNotions.S.umat y)‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
        (∫ y, ‖fGam ε f (y⁻¹ * x)‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) (ae_of_all _ fun z => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have hH := integral_mul_norm_le_Lp_mul_Lq (μ := μ) Real.HolderConjugate.two_two
      (f := fun y => F (Formalism.MainNotions.S.umat (z * y))) (g := fun y => fGam ε f (y⁻¹ * x))
      (by rw [ENNReal.ofReal_ofNat]; exact hA z) (by rw [ENNReal.ofReal_ofNat]; exact hB)
    have ht : ∫ y, ‖F (Formalism.MainNotions.S.umat (z * y))‖ ^ (2 : ℝ) ∂μ = ∫ y, ‖F (Formalism.MainNotions.S.umat y)‖ ^ (2 : ℝ) ∂μ :=
      integral_mul_left_eq_self (fun y => ‖F (Formalism.MainNotions.S.umat y)‖ ^ (2 : ℝ)) z
    rw [ht] at hH
    refine le_of_eq_of_le ?_ hH
    simp only [Function.uncurry_apply_pair, hG2, norm_mul]
  rw [integral_integral_swap hint]
  congr 1
  funext y
  exact integral_mul_const _ _

theorem reproducing_formula_closed_invariant {K : Submodule ℂ (L2 ε)} {d : ℝ} {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hFc : ContinuousOn F (UJset ε))
    (hF2 : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε))
    (hKc : IsClosed (K : Set (L2 ε))) (hfK : toL2 ε F ∈ K)
    (hKs : ∀ g ∈ UJset ε, ∀ u ∈ K, rreg ε g u ∈ K)
    (hS : ∀ a ∈ K, ∀ b ∈ K, ∀ a' ∈ K, ∀ b' ∈ K,
      Integrable (fun y : Formalism.REAL.UJ ε => ⟪a, rreg ε (Formalism.MainNotions.S.umat y) b⟫_ℂ *
        star ⟪a', rreg ε (Formalism.MainNotions.S.umat y) b'⟫_ℂ) (Formalism.REAL.muG ε) ∧
      ∫ y, ⟪a, rreg ε (Formalism.MainNotions.S.umat y) b⟫_ℂ * star ⟪a', rreg ε (Formalism.MainNotions.S.umat y) b'⟫_ℂ
        ∂(Formalism.REAL.muG ε) = ⟪b', b⟫_ℂ * ⟪a, a'⟫_ℂ / (d : ℂ)) :
    ∀ x ∈ UJset ε, ∫ y, F (Formalism.MainNotions.S.umat y) *
        ⟪toL2 ε F, rreg ε ((Formalism.MainNotions.S.umat y)⁻¹ * x) (toL2 ε F)⟫_ℂ ∂(Formalism.REAL.muG ε) =
      ⟪toL2 ε F, toL2 ε F⟫_ℂ / (d : ℂ) * F x := by
  intro x hx
  obtain ⟨x, rfl⟩ := exists_unitary_preimage ε hx
  set f := toL2 ε F with hfdef
  set μ := Formalism.REAL.muG ε with hμ
  set c : ℂ := ⟪f, f⟫_ℂ / (d : ℂ) with hc
  have hL : ∫ y, F (Formalism.MainNotions.S.umat y) * ⟪f, rreg ε ((Formalism.MainNotions.S.umat y)⁻¹ * Formalism.MainNotions.S.umat x) f⟫_ℂ ∂μ =
      fPhi ε F f x := by
    unfold fPhi fGam
    congr 1
    funext y
    rw [unitary_matrix_mul, unitary_matrix_inv_alt]
  rw [hL]
  have hFc' : Continuous (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) :=
    hFc.comp_continuous (continuous_unitary_matrix ε) (fun g => unitary_matrix_mem_set ε g)
  have hγ : MemLp (fGam ε f) 2 μ := matrix_coefficient_memLp ε hS hfK hfK
  set D : Formalism.REAL.UJ ε → ℂ := fun w => fPhi ε F f w - c * F (Formalism.MainNotions.S.umat w) with hD
  have hDc : Continuous D := (convolution_coefficient_continuous hS hF2 hfK).sub (continuous_const.mul hFc')
  by_contra hne
  have hδ : D x ≠ 0 := fun h0 => hne (sub_eq_zero.1 h0)
  have hδp : 0 < ‖D x‖ := norm_pos_iff.2 hδ
  have hDz : Continuous fun z : Formalism.REAL.UJ ε => D (z * x) := hDc.comp (continuous_id.mul continuous_const)
  have hev : ∀ᶠ z in 𝓝 (1 : Formalism.REAL.UJ ε), ‖D (z * x) - D x‖ < ‖D x‖ / 2 := by
    have ht := hDz.tendsto 1
    simp only [one_mul] at ht
    have := (Metric.tendsto_nhds.1 ht) (‖D x‖ / 2) (by linarith)
    simpa [dist_eq_norm] using this
  obtain ⟨C₀, hC₀c, hC₀n⟩ := exists_compact_mem_nhds (1 : Formalism.REAL.UJ ε)
  set N := interior ({z | ‖D (z * x) - D x‖ < ‖D x‖ / 2} ∩ C₀) with hN
  have hNo : IsOpen N := isOpen_interior
  have h1N : (1 : Formalism.REAL.UJ ε) ∈ N := mem_interior_iff_mem_nhds.2 (Filter.inter_mem hev hC₀n)
  have hNC : N ⊆ C₀ := interior_subset.trans Set.inter_subset_right
  have hNP : ∀ z ∈ N, ‖D (z * x) - D x‖ < ‖D x‖ / 2 := fun z hz => (interior_subset hz).1
  have hNlt : μ N < ∞ := lt_of_le_of_lt (measure_mono hNC) hC₀c.measure_lt_top
  have hNf : μ N ≠ ∞ := hNlt.ne
  have hNpos : 0 < μ N := hNo.measure_pos μ ⟨1, h1N⟩
  have hNr : 0 < (μ N).toReal := ENNReal.toReal_pos hNpos.ne' hNf
  have hNm : MeasurableSet N := hNo.measurableSet
  have hIphi : IntegrableOn (fun z => fPhi ε F f (z * x)) N μ :=
    (((convolution_coefficient_continuous hS hF2 hfK).comp (continuous_id.mul continuous_const)).continuousOn.integrableOn_compact
      hC₀c).mono_set hNC
  have hIF : IntegrableOn (fun z => F (Formalism.MainNotions.S.umat (z * x))) N μ :=
    ((hFc'.comp (continuous_id.mul continuous_const)).continuousOn.integrableOn_compact hC₀c).mono_set hNC
  have hkey : ∫ z in N, fPhi ε F f (z * x) ∂μ = c * ∫ z in N, F (Formalism.MainNotions.S.umat (z * x)) ∂μ := by
    rw [convolution_integral_fubini f hFc' hF2 hγ hNf x]
    have e2 : (fun y => (∫ z in N, F (Formalism.MainNotions.S.umat (z * y)) ∂μ) * fGam ε f (y⁻¹ * x)) =
        fun y => ⟪(indicatorConstLp 2 hNm hNf (1 : ℂ) : L2 ε), rreg ε (Formalism.MainNotions.S.umat y) f⟫_ℂ *
          fGam ε f (y⁻¹ * x) := by
      funext y
      rw [inner_indicator_right_regular ε hF2 hNm hNf y]
      rfl
    rw [e2, schur_orthogonality_integral hKc hKs hS hfK, inner_indicator_right_regular ε hF2 hNm hNf x, hc]
    simp only [unitary_matrix_mul]
    ring
  have hzero : ∫ z in N, D (z * x) ∂μ = 0 := by
    simp only [hD]
    rw [integral_sub hIphi (hIF.const_mul c), integral_const_mul, hkey, sub_self]
  have hID : IntegrableOn (fun z => D (z * x)) N μ := hIphi.sub (hIF.const_mul c)
  have hIc : IntegrableOn (fun _ : Formalism.REAL.UJ ε => D x) N μ :=
    (continuous_const.continuousOn.integrableOn_compact hC₀c).mono_set hNC
  have hNr' : 0 < μ.real N := hNr
  have hbound := norm_setIntegral_le_of_norm_le_const (μ := μ) (f := fun z => D (z * x) - D x) hNlt
    (fun z hz => (hNP z hz).le)
  rw [integral_sub hID hIc, hzero, setIntegral_const,
    zero_sub, norm_neg, norm_smul, Real.norm_of_nonneg hNr'.le] at hbound
  nlinarith [mul_pos hNr' hδp]

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SIntEquiv
section
noncomputable section

open Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.Lap.EvaluationEquivalence

open Formalism.QuantumDeterminants ReciprocityTheory.ChartRestriction.DS

variable {k r : ℕ}

def biEquiv (a b : Mat k r) (ha : IsUnit a.det) (hb : IsUnit b.det) : Mt k r ≃ᵐ Mt k r where
  toFun x := (a * Matrix.of x * b : Mat k r)
  invFun x := (a⁻¹ * Matrix.of x * b⁻¹ : Mat k r)
  left_inv x := by
    show a⁻¹ * (a * Matrix.of x * b) * b⁻¹ = Matrix.of x
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ ha, Matrix.mul_nonsing_inv _ hb,
      Matrix.mul_one]
  right_inv x := by
    show a * (a⁻¹ * Matrix.of x * b⁻¹) * b = Matrix.of x
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ ha, Matrix.nonsing_inv_mul _ hb,
      Matrix.mul_one]
  measurable_toFun := by
    have hc : @Continuous (Mt k r) (Mt k r) _ _ (fun x : Mt k r => (a * Matrix.of x * b : Mat k r)) :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact hc.measurable
  measurable_invFun := by
    have hc : @Continuous (Mt k r) (Mt k r) _ _ (fun x : Mt k r => (a⁻¹ * Matrix.of x * b⁻¹ : Mat k r)) :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact hc.measurable

theorem sInt_equiv {u : Fin k → ℝ} {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {Vp : Type}
    [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp] {π : Mat k r → (Vp →L[ℂ] Vp)}
    {μW μN : Measure (Mt k r)} (hB : IsBData z c u π μW μN) (f : Mat k r → ℂ) (ξ : Vp) (g : Mat k r)
    {h₀ m₀ : Mat k r} (hh₀ : h₀ ∈ UWset k r z) (hm₀ : m₀ ∈ Nset k r) :
    sInt μW μN (Formalism.MainNotions.S.psiGen k r z c) π f ξ (h₀ * m₀ * g) =
      Formalism.MainNotions.S.psiGen k r z c m₀ • π h₀ (sInt μW μN (Formalism.MainNotions.S.psiGen k r z c) π f ξ g) := by
  obtain ⟨hz, hT, -, hHC, hW, hN⟩ := hB
  have hπ : Formalism.MainNotions.S.IsURepOn (UWset k r z) π := hcTypeW_uRep k r z u Vp π hz hT hHC
  have hMP := Mult1.S0.A.shift_measurePreserving Mult1.haarUniqueSF' Formalism.FourierDecayAlt.P.weyl_subgroup_closed
    Formalism.FourierDecayAlt.P.weyl_haar_exists Formalism.FourierDecayAlt.P.unipotent_radical_closed Formalism.FourierDecayAlt.P.unipotent_haar_exists
    Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof hz hT hW hN hh₀ hm₀
  have hd := TransportGeo.uh_det hh₀.1
  have hdm := TransportGeo.uh_det hm₀.1
  let e := MeasurableEquiv.prodCongr (biEquiv (1 : Mat k r) h₀ (by simp) hd)
    (biEquiv h₀⁻¹ (h₀ * m₀) (TransportGeo.uh_det (TransportGeo.uh_inv hh₀.1))
      (TransportGeo.uh_det (TransportGeo.uh_mul hh₀.1 hm₀.1)))
  have he : (fun p : Mt k r × Mt k r => Prod.mk (α := Mt k r) (β := Mt k r) (Matrix.of p.1 * h₀ : Mat k r)
      (h₀⁻¹ * Matrix.of p.2 * h₀ * m₀ : Mat k r)) = e := by
    funext p
    refine Prod.ext ?_ ?_
    · show (Matrix.of p.1 * h₀ : Mat k r) = 1 * Matrix.of p.1 * h₀
      rw [Matrix.one_mul]
    · exact Matrix.mul_assoc _ h₀ m₀
  have : SigmaFinite μW := hW.1
  have : SigmaFinite μN := hN.1
  have hWae : ∀ᵐ y ∂μW, Matrix.of y ∈ UWset k r z := by rw [ae_iff]; simpa using hW.2.2.1
  have hNae : ∀ᵐ y ∂μN, Matrix.of y ∈ Nset k r := by rw [ae_iff]; simpa using hN.2.2.1
  have hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)
  set F : Mt k r × Mt k r → Vp := fun p => f (Matrix.of p.1 * Matrix.of p.2 * g) •
    chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ with hF
  let L : Vp →ₗᵢ[ℂ] Vp := ⟨(π h₀ : Vp →ₗ[ℂ] Vp), hπ.2.1 h₀ hh₀⟩
  have h1 : sInt μW μN (Formalism.MainNotions.S.psiGen k r z c) π f ξ (h₀ * m₀ * g) =
      ∫ p, Formalism.MainNotions.S.psiGen k r z c m₀ • L (F (e p)) ∂(μW.prod μN) := by
    unfold sInt
    refine integral_congr_ae ?_
    filter_upwards [hae] with p hp
    rw [← he]
    exact Mult1.S0.A.integrand_shift Formalism.FourierDecayAlt.P.weyl_subgroup_closed Formalism.FourierDecayAlt.P.unipotent_radical_closed
      Formalism.QuantumDeterminants.unitary_weyl_normal_holds hz c hπ f ξ hh₀ hm₀ hp.1 hp.2
  rw [he] at hMP
  rw [h1, integral_smul, L.integral_comp_comm (fun p => F (e p)), hMP.integral_comp' F]
  rfl

end ReciprocityTheory.ChartRestriction.DS.Lap.EvaluationEquivalence
end
end

