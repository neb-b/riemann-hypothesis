module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import GroundTheory.AutomorphicForms.ReductionSiegel
public import GroundTheory.AutomorphicForms.Reduction
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0648
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0653
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0696
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0714
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0652
public import Formalism.PieriBlockIdeals.StatementE
public import Formalism.PieriBlockIdeals.Bundle0007
public import Formalism.PieriBlockIdeals.PieriColumnMinors.RecursionInclusionExceptional
public import Formalism.PieriBlockIdeals.PieriColumnMinors.WeightBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0120
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalIdempotentsAdeleUnitCombination
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

namespace GlobalTheory.QSA.PickUnit

variable {F : Type} [Field F] [NumberField F]

def compInf (w : InfinitePlace F) : AF F →+* w.Completion :=
  (Pi.evalRingHom (fun u : InfinitePlace F => u.Completion) w).comp (RingHom.fst _ _)

def compFin (v : HeightOneSpectrum (𝓞 F)) : AF F →+* v.adicCompletion F :=
  (RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v).comp
    (RingHom.snd _ _)

theorem ext_comp {a b : AF F} (h1 : ∀ w, compInf w a = compInf w b) (h2 : ∀ v, compFin v a = compFin v b) :
    a = b :=
  Prod.ext (funext h1) (Subtype.ext (funext h2))

theorem isUnit_of_comp {a : AF F} (h1 : ∀ w, compInf w a ≠ 0) (h2 : ∀ v, compFin v a ≠ 0)
    (h3 : ∀ᶠ v in Filter.cofinite, Valued.v (compFin v a) = 1) : IsUnit a :=
  Prod.isUnit_iff.2 ⟨Pi.isUnit_iff.2 fun w => isUnit_iff_ne_zero.2 (h1 w), FiniteAdeleRing.isUnit_iff.2 ⟨h2, h3⟩⟩

variable {ι : Type} [DecidableEq ι]

def ind (a : InfinitePlace F → ι) (b : HeightOneSpectrum (𝓞 F) → ι) (i : ι) : AF F :=
  ((fun w => if a w = i then 1 else 0),
    ⟨fun v => if b v = i then 1 else 0, Filter.Eventually.of_forall fun v => by
      by_cases h : b v = i
      · simp only [h, if_true]; exact one_mem _
      · simp only [h, if_false]; exact zero_mem _⟩)

theorem compInf_ind (a : InfinitePlace F → ι) (b : HeightOneSpectrum (𝓞 F) → ι) (i : ι) (w : InfinitePlace F) :
    compInf w (ind a b i) = if a w = i then 1 else 0 := rfl

theorem compFin_ind (a : InfinitePlace F → ι) (b : HeightOneSpectrum (𝓞 F) → ι) (i : ι)
    (v : HeightOneSpectrum (𝓞 F)) : compFin v (ind a b i) = if b v = i then 1 else 0 := rfl

end GlobalTheory.QSA.PickUnit


open GlobalTheory.QSA.PickUnit in
theorem GlobalTheory.QSA.exists_idem_pick_unit : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι]
    (n u : ι → AF F), IsUnit (∑ i, u i * n i) → ∃ η : ι → AF F, (∀ i, η i * η i = η i) ∧
      (∀ i j, i ≠ j → η i * η j = 0) ∧ ∑ i, η i = 1 ∧ IsUnit (∑ i, η i * n i) := by
  intro F _ _ ι _ n u hs
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · rw [Finset.univ_eq_empty, Finset.sum_empty] at hs
    refine ⟨fun _ => 0, fun i => isEmptyElim i, fun i => isEmptyElim i, ?_, ?_⟩
    · rw [Finset.univ_eq_empty, Finset.sum_empty]; exact isUnit_zero_iff.1 hs
    · rw [Finset.univ_eq_empty, Finset.sum_empty]; exact hs
  have hinf : ∀ w, ∃ i, compInf w (n i) ≠ 0 := by
    intro w
    by_contra h
    push_neg at h
    apply (hs.map (compInf w)).ne_zero
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [map_mul, h i, mul_zero]
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F), ∃ i, ∀ j, Valued.v (compFin v (n j)) ≤ Valued.v (compFin v (n i)) := by
    intro v
    obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => Valued.v (compFin v (n j)))
      ⟨i₀, Finset.mem_univ _⟩
    exact ⟨i, fun j => hi j (Finset.mem_univ _)⟩
  choose a ha using hinf
  choose b hb using hfin
  refine ⟨ind a b, ?_, ?_, ?_, ?_⟩
  · intro i
    apply ext_comp
    · intro w; rw [map_mul, compInf_ind]; split_ifs <;> simp
    · intro v; rw [map_mul, compFin_ind]; split_ifs <;> simp
  · intro i j hij
    apply ext_comp
    · intro w; rw [map_mul, map_zero, compInf_ind, compInf_ind]
      by_cases h1 : a w = i
      · rw [if_pos h1, if_neg (fun h2 => hij (h1.symm.trans h2)), mul_zero]
      · rw [if_neg h1, zero_mul]
    · intro v; rw [map_mul, map_zero, compFin_ind, compFin_ind]
      by_cases h1 : b v = i
      · rw [if_pos h1, if_neg (fun h2 => hij (h1.symm.trans h2)), mul_zero]
      · rw [if_neg h1, zero_mul]
  · apply ext_comp
    · intro w; rw [map_sum, map_one]; simp only [compInf_ind]; rw [Finset.sum_ite_eq]; simp
    · intro v; rw [map_sum, map_one]; simp only [compFin_ind]; rw [Finset.sum_ite_eq]; simp
  · have hcInf : ∀ w, compInf w (∑ i, ind a b i * n i) = compInf w (n (a w)) := by
      intro w
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_eq_single (a w)]
      · rw [map_mul, compInf_ind, if_pos rfl, one_mul]
      · intro j _ hj; rw [map_mul, compInf_ind, if_neg (Ne.symm hj), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hcFin : ∀ v, compFin v (∑ i, ind a b i * n i) = compFin v (n (b v)) := by
      intro v
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_eq_single (b v)]
      · rw [map_mul, compFin_ind, if_pos rfl, one_mul]
      · intro j _ hj; rw [map_mul, compFin_ind, if_neg (Ne.symm hj), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    apply isUnit_of_comp
    · intro w; rw [hcInf]; exact ha w
    · intro v h0
      rw [hcFin] at h0
      apply (hs.map (compFin v)).ne_zero
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      have h := hb v j
      rw [h0, map_zero] at h
      rw [map_mul, (Valuation.zero_iff _).1 (le_antisymm h zero_le'), mul_zero]
    · have hsu := (FiniteAdeleRing.isUnit_iff.1 (hs.map (RingHom.snd (InfiniteAdeleRing F) (Af F)))).2
      have hint : ∀ᶠ v in Filter.cofinite, ∀ j,
          Valued.v (compFin v (u j)) ≤ 1 ∧ Valued.v (compFin v (n j)) ≤ 1 := by
        refine Filter.eventually_all.2 fun j => ?_
        filter_upwards [(u j).2.2, (n j).2.2] with v h1 h2
        exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F v).1 h1,
          (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F v).1 h2⟩
      filter_upwards [hsu, hint] with v hv1 hv2
      rw [hcFin]
      refine le_antisymm (hv2 _).2 ?_
      have hv1' : Valued.v (compFin v (∑ i, u i * n i)) = 1 := hv1
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hv1', map_sum]
      refine Valuation.map_sum_le _ fun j _ => ?_
      rw [map_mul, map_mul]
      exact (mul_le_of_le_one_left zero_le' (hv2 j).1).trans (hb v j)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalPureQuaternionSqOfAdelic
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QSA.PureSq

theorem mul_self_of_re_eq_zero {R : Type*} [CommRing R] {a b : R} (p : ℍ[R, a, b]) (hp : p.re = 0) :
    p * p = algebraMap R ℍ[R, a, b] (a * p.imI ^ 2 + b * p.imJ ^ 2 - a * b * p.imK ^ 2) := by
  ext <;> simp [QuaternionAlgebra.algebraMap_eq, hp] <;> ring

theorem exists_completion_hom_of_real {K : Type} [Field K] (σ : K →+* ℝ) :
    ∃ (w : InfinitePlace K) (f : w.Completion →+* ℝ), ∀ x : K, f (algebraMap K w.Completion x) = σ x := by
  have hφ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp
  have hw : (InfinitePlace.mk (Complex.ofRealHom.comp σ)).IsReal := InfinitePlace.isReal_mk_iff.2 hφ
  refine ⟨_, InfinitePlace.Completion.extensionEmbeddingOfIsReal hw, fun x => ?_⟩
  have he := InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw
    ((WithAbs.equiv _).symm x)
  rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
    Algebra.algebraMap_self_apply]
  refine Eq.trans he ?_
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hφ]
  simp

variable {F : Type} [Field F] [NumberField F]

theorem isotropic_of_ringHom {a b c : F} (q : DA F a b) (hq0 : q.re = 0)
    (hqq : q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c))
    {k : Type*} [Field k] (φ : AF F →+* k) (ψ : F →+* k)
    (hφ : ∀ x, φ (algebraMap F (AF F) x) = ψ x) :
    ∃ x : Fin 4 → k, x ≠ 0 ∧ ∑ i, ψ (![a, b, -(a * b), -c] i) * x i ^ 2 = 0 := by
  rw [mul_self_of_re_eq_zero q hq0] at hqq
  have h1 := congrArg QuaternionAlgebra.re hqq
  simp only [QuaternionAlgebra.algebraMap_eq, QuaternionAlgebra.re_coe] at h1
  have h2 := congrArg φ h1
  simp only [map_add (f := _), map_sub, map_mul, map_pow, hφ] at h2
  refine ⟨![φ q.imI, φ q.imJ, φ q.imK, 1], fun h => by simpa using congrFun h 3, ?_⟩
  simp [Fin.sum_univ_four]
  linear_combination h2

end GlobalTheory.QSA.PureSq

namespace GlobalTheory.QSA.PureSq

variable {F : Type} [Field F] [NumberField F]

theorem isotropic_real {a b c : F} (q : DA F a b) (hq0 : q.re = 0)
    (hqq : q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c)) (σ : F →+* ℝ) :
    ∃ x : Fin 4 → ℝ, x ≠ 0 ∧ ∑ i, σ (![a, b, -(a * b), -c] i) * x i ^ 2 = 0 := by
  obtain ⟨w, f, hf⟩ := exists_completion_hom_of_real σ
  refine isotropic_of_ringHom q hq0 hqq
    (f.comp ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w).comp (fstA F).toRingHom)) σ
    (fun x => ?_)
  rw [← hf x]
  rfl

theorem isotropic_finite {a b c : F} (q : DA F a b) (hq0 : q.re = 0)
    (hqq : q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c)) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ x : Fin 4 → v.adicCompletion F, x ≠ 0 ∧
      ∑ i, algebraMap F (v.adicCompletion F) (![a, b, -(a * b), -c] i) * x i ^ 2 = 0 :=
  isotropic_of_ringHom q hq0 hqq ((evalV F v).comp (sndA F)).toRingHom (algebraMap F _)
    (fun x => ((evalV F v).comp (sndA F)).commutes x)

theorem exists_ternary_eq {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) {u₁ u₂ u₃ : F}
    (hu : (u₁, u₂, u₃) ≠ (0, 0, 0)) (h : a * u₁ ^ 2 + b * u₂ ^ 2 - a * b * u₃ ^ 2 = 0) (c : F) :
    ∃ y₁ y₂ y₃ : F, a * y₁ ^ 2 + b * y₂ ^ 2 - a * b * y₃ ^ 2 = c := by
  have key : ∀ v₁ v₂ v₃ : F, a * u₁ * v₁ + b * u₂ * v₂ - a * b * u₃ * v₃ ≠ 0 →
      ∃ y₁ y₂ y₃ : F, a * y₁ ^ 2 + b * y₂ ^ 2 - a * b * y₃ ^ 2 = c := by
    intro v₁ v₂ v₃ hD
    set D := a * u₁ * v₁ + b * u₂ * v₂ - a * b * u₃ * v₃ with hDdef
    set t := (c - (a * v₁ ^ 2 + b * v₂ ^ 2 - a * b * v₃ ^ 2)) / (2 * D) with ht
    have h2 : (2 : F) * D ≠ 0 := mul_ne_zero two_ne_zero hD
    have ht' : t * (2 * D) = c - (a * v₁ ^ 2 + b * v₂ ^ 2 - a * b * v₃ ^ 2) := div_mul_cancel₀ _ h2
    refine ⟨t * u₁ + v₁, t * u₂ + v₂, t * u₃ + v₃, ?_⟩
    linear_combination t ^ 2 * h + ht'
  by_cases h1 : u₁ = 0
  · by_cases h2 : u₂ = 0
    · have h3 : u₃ ≠ 0 := fun h3 => hu (by simp [h1, h2, h3])
      exact key 0 0 1 (by simp [ha, hb, h3])
    · exact key 0 1 0 (by simp [hb, h2, h1])
  · exact key 1 0 0 (by simp [ha, h1])

theorem exists_rat_of_adelic : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ c : F, c ≠ 0 →
    ∀ q : DA F a b, q.re = 0 → q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) →
    ∃ p : ℍ[F, a, b], p.re = 0 ∧ p * p = algebraMap F ℍ[F, a, b] c := by
  intro F _ _ a b ha hb c hc q hq0 hqq
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.LocalQuad.isotropic_of_locally_isotropic GlobalTheory.QNorm.hasseNormSt F
    (ι := Fin 4) (by simp) ![a, b, -(a * b), -c]
    (fun i => by fin_cases i <;> simp [ha, hb, hc])
    (isotropic_real q hq0 hqq) (isotropic_finite q hq0 hqq)
  simp [Fin.sum_univ_four] at hx
  have pure : ∀ y₁ y₂ y₃ : F, a * y₁ ^ 2 + b * y₂ ^ 2 - a * b * y₃ ^ 2 = c →
      ∃ p : ℍ[F, a, b], p.re = 0 ∧ p * p = algebraMap F ℍ[F, a, b] c := by
    intro y₁ y₂ y₃ hy
    refine ⟨⟨0, y₁, y₂, y₃⟩, rfl, ?_⟩
    rw [mul_self_of_re_eq_zero _ rfl]
    change algebraMap F ℍ[F, a, b] (a * y₁ ^ 2 + b * y₂ ^ 2 - a * b * y₃ ^ 2) = _
    rw [hy]
  by_cases h3 : x 3 = 0
  · rw [h3] at hx
    obtain ⟨y₁, y₂, y₃, hy⟩ := exists_ternary_eq ha hb (u₁ := x 0) (u₂ := x 1) (u₃ := x 2)
      (fun h => hx0 (by
        simp only [Prod.mk.injEq] at h
        funext i; fin_cases i <;> simp [h.1, h.2.1, h.2.2, h3]))
      (by linear_combination hx) c
    exact pure y₁ y₂ y₃ hy
  · refine pure (x 0 / x 3) (x 1 / x 3) (x 2 / x 3) ?_
    field_simp
    linear_combination hx

end GlobalTheory.QSA.PureSq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelSetReductionAdelicDetNormBand
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff

open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GlobalTheory.HCF

theorem exists_siegel_band : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), ∃ Ω : Set (GA E a), IsCompact Ω ∧ Ω ⊆ ((adelicBorel : Subgroup (GA E a)) : Set (GA E a)) ∧ ∃ t c₁ c₂ : ℝ, 0 < t ∧ 0 < c₁ ∧ ∀ g ∈ band E a, ∃ γ : GL (Fin a) E, ∃ b ∈ Ω, ∃ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) ∧ c₁ ≤ ∏ i, r i ∧ ∏ i, r i ≤ c₂ ∧ ∃ k ∈ (maxCompact : Subgroup (GA E a)), ratGL E a γ * g = b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k := by
  intro E _ _ a
  obtain ⟨W0, hW, hWB, t, ht, h⟩ := exists_siegelSet (K := E) a
  obtain ⟨B₁, B₂, hB₁, hB₁₂, hB⟩ := exists_pos_bounds hW
    (f := fun b => (ideleModule E (AdelicGLn.det E a b) : ℝ))
    (continuous_subtype_val.comp (continuous_ideleModule.comp (AdelicGLn.continuous_det E a)))
    (fun b _ => (ideleModule E (AdelicGLn.det E a b)).2)
  set d := Module.finrank ℚ E with hd
  have hd0 : 0 < d := Module.finrank_pos
  have hB₂ : 0 < B₂ := hB₁.trans_le hB₁₂
  set X₁ : ℝ := min 1 B₂⁻¹ with hX₁def
  set X₂ : ℝ := max 1 (2 / B₁) with hX₂def
  have hX₁ : 0 < X₁ := lt_min one_pos (inv_pos.2 hB₂)
  refine ⟨W0, hW, hWB, t, X₁, X₂, ht, hX₁, fun g hg => ?_⟩
  obtain ⟨γ, hγ⟩ := h g
  obtain ⟨b, hbW, _, ⟨r, hr, hrat, rfl⟩, k, hk, hgeq⟩ := hγ
  have hgmod : (ideleModule E (AdelicGLn.det E a g) : ℝ) = absDetA g := (adeleAbs_units _).symm
  have hmod := congrArg (fun x => (ideleModule E (AdelicGLn.det E a x) : ℝ)) hgeq
  rw [det_mul_mul, ideleModule_det_diagUnits_posIdele r hr,
    mem_normOneGL.1 (maxCompact_le_normOneGL hk), mul_one, map_mul, map_mul, Positive.val_mul,
    mem_normOneGL.1 (rationalGL_le_normOneGL ⟨γ, rfl⟩), one_mul, hgmod] at hmod
  set X : ℝ := ∏ i, r i with hX
  have hXpos : 0 < X := Finset.prod_pos fun i _ => hr i
  have hb := hB b hbW
  obtain ⟨h1, h2⟩ := hg
  have hXd1 : X ^ d ≤ 2 / B₁ := by
    rw [le_div_iff₀ hB₁]
    calc X ^ d * B₁ ≤ X ^ d * (ideleModule E (AdelicGLn.det E a b) : ℝ) :=
          mul_le_mul_of_nonneg_left hb.1 (pow_nonneg hXpos.le _)
      _ = absDetA g := by rw [mul_comm, hmod]
      _ ≤ 2 := h2
  have hXd2 : B₂⁻¹ ≤ X ^ d := by
    rw [inv_le_iff_one_le_mul₀' hB₂]
    calc (1 : ℝ) ≤ _ := h1
      _ = (ideleModule E (AdelicGLn.det E a b) : ℝ) * X ^ d := hmod
      _ ≤ B₂ * X ^ d := mul_le_mul_of_nonneg_right hb.2 (pow_nonneg hXpos.le _)
  have hratGL : ratGL E a γ = AdelicGLn.diagonal E a γ := rfl
  refine ⟨γ, b, hbW, r, hr, hrat, ?_, ?_, k, hk, by rw [hratGL]; exact hgeq⟩
  · rcases le_or_gt 1 X with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (hXd2.trans (pow_le_of_le_one hXpos.le h.le hd0.ne'))
  · rcases le_or_gt X 1 with h | h
    · exact h.trans (le_max_left _ _)
    · exact (le_self_pow₀ h.le hd0.ne').trans (hXd1.trans (le_max_right _ _))
end GlobalTheory.HCF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecialUnitarySectionLowerUnitriangularCha
section
noncomputable section

namespace GlobalTheory.SUChartSection
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal ComplexConjugate ContDiff

theorem exists_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ∃ (σ : V (nd X) → realSU X.Ψ X.Gm) (ρ : ℝ) (D₁ : V (nd X) →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ)), 0 < ρ ∧ σ 0 = 1 ∧ ContinuousOn σ (Metric.ball 0 ρ) ∧ (∀ z ∈ Metric.ball (0 : V (nd X)) ρ, ∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul (cpt X x z) b) ∧ HasStrictFDerivAt (fun z => (fun τ a b => ((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b)) D₁ 0 ∧ ∀ z, D₁ z ∈ realLie X.Ψ X.Gm ∧ (∀ τ a b, b < a → inFrame x (D₁ z) τ a b = nmat X z τ a b) ∧ ∀ τ a, inFrame x (D₁ z) τ a a = 0 := by
  intro E _ _ _ r X x hx
  classical
  obtain ⟨R, hR, hball⟩ := exists_ball X hx
  have hdet1 : ∀ w, cpt X x w ∈ X.dom → ∀ τ, (secM X x w τ).det ≠ 0 := fun w hw τ => by
    rw [_root_.GlobalTheory.SUChartSection.det_secM_eq_one X hx hw τ]; exact one_ne_zero
  let secU : ∀ w, cpt X x w ∈ X.dom → realSU X.Ψ X.Gm := fun w hw =>
    ⟨fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero (secM X x w τ) (hdet1 w hw τ),
      fun τ => ⟨_root_.GlobalTheory.SUChartSection.det_secM_eq_one X hx hw τ, GlobalTheory.T.complexHermitianForm_unitaryChartSection X hx hw τ⟩⟩
  have hsecU : ∀ w (hw : cpt X x w ∈ X.dom) τ,
      ((((secU w hw : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
        secM X x w τ := fun _ _ _ => rfl
  let σ : V (nd X) → realSU X.Ψ X.Gm := fun w => if h : w ∈ Metric.ball (0 : V (nd X)) R then secU w (hball w h) else 1
  have hσ : ∀ w (h : w ∈ Metric.ball (0 : V (nd X)) R) τ,
      ((((σ w : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
        secM X x w τ := fun w h τ => by
    simp only [σ, dif_pos h]; rfl
  have hx0 : ∀ τ, IsUnit (mat x τ).det := fun τ => isUnit_iff_ne_zero.2 (det_ne_of_orth X hx τ)
  have h0 : (0 : V (nd X)) ∈ Metric.ball (0 : V (nd X)) R := Metric.mem_ball_self hR
  let Cx : (X.Ψ → Fin r → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → Fin r → ℂ) :=
    { toFun := fun Y τ => (mat x τ * Matrix.of (Y τ) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)
      map_add' := fun Y Z => by
        funext τ
        have e : Matrix.of ((Y + Z) τ) = Matrix.of (Y τ) + Matrix.of (Z τ) := rfl
        simp only [e, Matrix.mul_add, Matrix.add_mul]; rfl
      map_smul' := fun c Y => by
        funext τ
        have e : Matrix.of ((c • Y) τ) = c • Matrix.of (Y τ) := rfl
        simp only [e, Matrix.mul_smul, Matrix.smul_mul]; rfl }
  let C := LinearMap.toContinuousLinearMap Cx
  have hC : ∀ Y τ, C Y τ = (mat x τ * Matrix.of (Y τ) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) := fun _ _ => rfl
  refine ⟨σ, R, C.comp (dY X), hR, ?_, ?_, ?_, ?_, ?_⟩
  · refine Subtype.ext (funext fun τ => Units.ext ?_)
    rw [hσ 0 h0 τ, secM_zero X hx τ]; rfl
  · rw [continuousOn_iff_continuous_restrict]
    have hg : ∀ τ, Continuous fun w : Metric.ball (0 : V (nd X)) R => gsB X w τ := fun τ => by
      refine continuous_pi fun a => continuous_pi fun b => ?_
      exact ((_root_.GlobalTheory.SUChartSection.GSSmooth.gsB_contDiffOn X hx τ a b).continuousOn.mono (fun w hw => hball w hw)).restrict
    have hM : ∀ τ, Continuous fun w : Metric.ball (0 : V (nd X)) R => secM X x w τ := fun τ => by
      refine (continuous_const.matrix_mul ?_).matrix_mul continuous_const
      exact ((PoinPf.cont_nmatm X τ).comp continuous_subtype_val).matrix_mul (hg τ)
    refine continuous_induced_rng.2 (continuous_pi fun τ => Units.continuous_iff.2 ⟨?_, ?_⟩)
    · refine (hM τ).congr fun w => ?_
      simp only [Function.comp_apply, Set.restrict_apply]
      exact (hσ w w.2 τ).symm
    · refine ((hM τ).matrix_adjugate).congr fun w => ?_
      simp only [Function.comp_apply, Set.restrict_apply]
      rw [Matrix.coe_units_inv, hσ w w.2 τ, Matrix.inv_def, _root_.GlobalTheory.SUChartSection.det_secM_eq_one X hx (hball w w.2) τ, Ring.inverse_one, one_smul]
  · intro z hz
    refine ⟨FrameDegreeData.bOf X (cpt X x z), FrameDegreeData.bOf_mem X (hball z hz), ?_⟩
    funext τ
    show (((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ :
      Matrix (Fin r) (Fin r) ℂ) = (mat (cpt X x z) τ * mat (FrameDegreeData.bOf X (cpt X x z)) τ : Matrix (Fin r) (Fin r) ℂ)
    rw [hσ z hz τ, bOf_cpt X hx z]
    show mat x τ * yM X z τ * (mat x τ)⁻¹ * mat x τ = mat x τ * mat (nmat X z) τ * gsB X z τ
    rw [Matrix.mul_assoc _ (mat x τ)⁻¹, Matrix.nonsing_inv_mul _ (hx0 τ), Matrix.mul_one, yM, Matrix.mul_assoc]
  · have h1 : HasStrictFDerivAt (fun z => C (yF X z)) (C.comp (dY X)) 0 :=
      C.hasStrictFDerivAt.comp 0 (GlobalTheory.T.unitaryChartSectionFrameEntries_hasStrictFDerivAt X hx)
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : V (nd X)) hR] with z hz
    funext τ a b
    rw [hσ z hz τ, hC]
    rfl
  · intro z
    have hdiag : ∀ τ a, dY X z τ a a = 0 := fun τ a => by
      have h6 := congrArg Complex.re (GlobalTheory.T.unitaryChartSectionFrameEntriesFDeriv_skew X hx z τ a a)
      have h7 := GlobalTheory.T.unitaryChartSectionFrameEntriesFDeriv_diag_im X hx z τ a
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
        Complex.conj_im, h7, Complex.zero_re, mul_zero, sub_zero, zero_mul, neg_zero] at h6
      have hs := PoinPf.sgn_ne X.p0 (a : ℕ)
      have hre : (dY X z τ a a).re = 0 := by
        have : 2 * sgn X.p0 (a : ℕ) * (dY X z τ a a).re = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · exact absurd (by linarith : sgn X.p0 (a : ℕ) = 0) hs
        · exact h
      exact Complex.ext hre h7
    have hIF : ∀ τ, inFrame x (C.comp (dY X) z) τ = Matrix.of (dY X z τ) := fun τ => by
      show (mat x τ)⁻¹ * Matrix.of (C (dY X z) τ) * mat x τ = _
      rw [hC]
      show (mat x τ)⁻¹ * (mat x τ * Matrix.of (dY X z τ) * (mat x τ)⁻¹) * mat x τ = _
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hx0 τ), Matrix.one_mul,
        Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hx0 τ), Matrix.mul_one]
    refine ⟨?_, fun τ a b h => ?_, fun τ a => ?_⟩
    · exact _root_.GlobalTheory.SUChartSection.conj_mem_realLie X hx (fun τ => Matrix.of (dY X z τ)) (fun τ a b => GlobalTheory.T.unitaryChartSectionFrameEntriesFDeriv_skew X hx z τ a b) hdiag
    · rw [hIF]; exact GlobalTheory.T.unitaryChartSection_fderiv_below_diagonal X hx z τ a b h
    · rw [hIF]; exact hdiag τ a
end GlobalTheory.SUChartSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentOfRecordVsFormulas
section
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

namespace GlobalTheory

theorem exponent_of_record_vs_formulas :
    Formalism.CohomologicalDescent.E.ExCut → ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P →
      ∀ l : ℕ, l.Prime → (¬ W.WRange P l → W.JA P l ≤ W.Jrec7 P l) ∧ (W.WRange P l → W.coarseWeightBound P l = W.Jrec7 P l) := by
  intro hC P hH hL ι _ _ W hW l hl
  refine ⟨fun hR => ?_, fun hR => ?_⟩
  · by_cases hc : (l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W.Sp
    · rw [seventh_recursion_eq_a_of_small_prime W P l hc]
    · have h1 : P.lJ < (l : ℝ) := not_le.mp fun h => hc (Or.inl h)
      have h2 : ¬ P.Excl l := fun h => hc (Or.inr (Or.inl h))
      have h3 : l ∉ W.Sp := fun h => hc (Or.inr (Or.inr h))
      have hh : P.h < (l : ℝ) := not_le.mp fun h => hR ⟨h1, h, h2, h3⟩
      have hb := Formalism.CohomologicalDescent.E.beyond_height_exceptional (Formalism.CohomologicalDescent.E.exIntervalLt_of_exCut hC) hC P hH hL ι W hW l hl h1 hh
      rw [hb.2.1]
      exact Nat.zero_le _
  · obtain ⟨h1, _, h2, h3⟩ := hR
    have hc : ¬ ((l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W.Sp) := by
      rintro (h | h | h)
      · exact absurd h (not_le.mpr h1)
      · exact h2 h
      · exact h3 h
    rw [seventh_recursion_eq_w_of_large_prime W P l hc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationNatCastEqOneOfCoprimeStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime : ∀ (V : ValuationSubring ℂ) (a b : ℕ), Nat.Coprime a b → V.valuation (a : ℂ) = 1 ∨ V.valuation (b : ℂ) = 1 := by
  first | exact @GlobalTheory.CMModel.valuation_natCast_eq_one_of_coprime | exact GlobalTheory.CMModel.valuation_natCast_eq_one_of_coprime | (intros; apply GlobalTheory.CMModel.valuation_natCast_eq_one_of_coprime <;> assumption)
end

