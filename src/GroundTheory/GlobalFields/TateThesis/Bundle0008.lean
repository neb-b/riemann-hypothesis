module

public import Mathlib
public import GroundTheory.GlobalFields.TateThesis.EulerFactorsArch
public import GroundTheory.GlobalFields.TateThesis.Bundle0002
public import GroundTheory.GlobalFields.TateThesis.TraceFourier
public import GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass
public import GroundTheory.GlobalFields.Adele.Bundle0001
public import GroundTheory.GlobalFields.TateThesis.Bundle0007
public import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
public import GroundTheory.GlobalFields.TateThesis.Bundle0005

@[expose] public section

-- bundled from GroundTheory.GlobalFields.TateThesis.EulerFactorsInfinite
section
open NumberField InfinitePlace InfinitePlace.Completion MeasureTheory Complex ComplexConjugate
  NumberField.mixedEmbedding Function
open scoped Real SchwartzMap Classical RealInnerProductSpace

namespace GroundTheory.Global

noncomputable section

theorem hasTemperateGrowth_finsetProd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} (s : Finset ι) {f : ι → E → ℂ} (hf : ∀ i ∈ s, (f i).HasTemperateGrowth) :
    (fun x ↦ ∏ i ∈ s, f i x).HasTemperateGrowth := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact HasTemperateGrowth.const (1 : ℂ)
  | insert a s ha ih =>
    simp_rw [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).mul
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

theorem ofReal_finsetProd_cpow {ι : Type*} (t : Finset ι) {r : ι → ℝ} (hr : ∀ i ∈ t, 0 ≤ r i)
    (s : ℂ) : ((∏ i ∈ t, r i : ℝ) : ℂ) ^ s = ∏ i ∈ t, ((r i : ℝ) : ℂ) ^ s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ofReal_mul,
      mul_cpow_ofReal_nonneg (hr a (Finset.mem_insert_self _ _))
        (Finset.prod_nonneg fun i hi ↦ hr i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ hr i (Finset.mem_insert_of_mem hi)]

variable {K : Type*} [Field K] [NumberField K]

theorem norm_mixedToEuclidean_sq (x : mixedSpace K) :
    ‖mixedToEuclidean K x‖ ^ 2 = ∑ w, x.1 w ^ 2 + 2 * ∑ w, ‖x.2 w‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  change ⟪(euclidean.toMixed K).symm (mapComplexCoord K sqrtTwoSMulComplex x),
    (euclidean.toMixed K).symm (mapComplexCoord K sqrtTwoSMulComplex x)⟫ = _
  rw [inner_toMixed_symm, mapComplexCoord_apply, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun w _ ↦ by ring
  · refine Finset.sum_congr rfl fun w _ ↦ ?_
    dsimp only
    rw [sqrtTwoSMulComplex_apply, Complex.real_smul, map_mul, conj_ofReal,
      show ((√2 : ℝ) : ℂ) * conj (x.2 w) * (((√2 : ℝ) : ℂ) * x.2 w) =
        (((√2 : ℝ) ^ 2 : ℝ) : ℂ) * (conj (x.2 w) * x.2 w) by push_cast; ring,
      Real.sq_sqrt (by norm_num), Complex.conj_mul']
    norm_cast

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

def infinitePoly (x : mixedSpace K) : ℂ :=
  (∏ w : {w // IsReal w}, ((x.1 w : ℝ) : ℂ) ^ (χ.infiniteWeight w).natAbs) *
    ∏ w : {w // IsComplex w},
      (if 0 < χ.infiniteWeight w then conj (x.2 w) else x.2 w) ^ (χ.infiniteWeight w).natAbs

theorem hasTemperateGrowth_infinitePoly : χ.infinitePoly.HasTemperateGrowth := by
  have h1 : ∀ w : {w // IsReal w}, (fun x : mixedSpace K ↦
      ((x.1 w : ℝ) : ℂ) ^ (χ.infiniteWeight w).natAbs).HasTemperateGrowth := fun w ↦ by
    have h := (((Complex.ofRealCLM.comp ((ContinuousLinearMap.proj w :
      ({w // IsReal w} → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ ({w // IsReal w} → ℝ)
        ({w // IsComplex w} → ℂ))) : mixedSpace K →L[ℝ] ℂ)).hasTemperateGrowth).pow (χ.infiniteWeight w).natAbs
    exact h
  have h2 : ∀ w : {w // IsComplex w}, (fun x : mixedSpace K ↦
      (if 0 < χ.infiniteWeight w then conj (x.2 w) else x.2 w) ^
        (χ.infiniteWeight w).natAbs).HasTemperateGrowth := by
    intro w
    by_cases hw : 0 < χ.infiniteWeight w
    · simp only [ite_eq_left hw]
      have h := (((Complex.conjCLE.toContinuousLinearMap.comp ((ContinuousLinearMap.proj w :
        ({w // IsComplex w} → ℂ) →L[ℝ] ℂ).comp (ContinuousLinearMap.snd ℝ ({w // IsReal w} → ℝ)
          ({w // IsComplex w} → ℂ))) : mixedSpace K →L[ℝ] ℂ)).hasTemperateGrowth).pow (χ.infiniteWeight w).natAbs
      exact h
    · simp only [ite_eq_right hw]
      have h := ((((ContinuousLinearMap.proj w : ({w // IsComplex w} → ℂ) →L[ℝ] ℂ).comp
        (ContinuousLinearMap.snd ℝ ({w // IsReal w} → ℝ)
          ({w // IsComplex w} → ℂ)) : mixedSpace K →L[ℝ] ℂ)).hasTemperateGrowth).pow (χ.infiniteWeight w).natAbs
      exact h
  exact (hasTemperateGrowth_finsetProd _ fun w _ ↦ h1 w).mul
    (hasTemperateGrowth_finsetProd _ fun w _ ↦ h2 w)

def infiniteSchwartz : 𝓢(mixedSpace K, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ χ.infinitePoly
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedToEuclidean K)
      (gaussianSchwartz (euclidean.mixedSpace K)))

theorem infiniteSchwartz_apply (x : mixedSpace K) :
    χ.infiniteSchwartz x = χ.infinitePoly x *
      ((Real.exp (-π * (∑ w, x.1 w ^ 2 + 2 * ∑ w, ‖x.2 w‖ ^ 2)) : ℝ) : ℂ) := by
  rw [infiniteSchwartz, SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth_infinitePoly,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, gaussianSchwartz_apply,
    norm_mixedToEuclidean_sq, smul_eq_mul]

theorem infiniteSchwartz_homeomorphMixedSpace (x : InfiniteAdeleRing K) :
    χ.infiniteSchwartz (homeomorphMixedSpace K x) = ∏ w, χ.infiniteTest w (x w) := by
  rw [infiniteSchwartz_apply, prod_eq_prod_mul_prod, homeomorphMixedSpace_apply,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  simp only [infinitePoly, infiniteTest, Finset.prod_mul_distrib]
  have hr : ∀ w : {w // IsReal w}, (if 0 < χ.infiniteWeight w.1 then
      conj (extensionEmbedding w.1 (x w.1)) else extensionEmbedding w.1 (x w.1)) =
        ((extensionEmbeddingOfIsReal w.2 (x w.1) : ℝ) : ℂ) := fun w ↦ by
    rw [extensionEmbeddingOfIsReal_apply]
    split_ifs
    · rw [← extensionEmbeddingOfIsReal_apply w.2, conj_ofReal]
    · rfl
  have hnr : ∀ w : {w // IsReal w}, (extensionEmbeddingOfIsReal w.2 (x w.1)) ^ 2 = ‖x w.1‖ ^ 2 :=
    fun w ↦ by
      rw [← (isometry_extensionEmbeddingOfIsReal w.2).norm_map_of_map_zero (map_zero _),
        Real.norm_eq_abs, sq_abs]
  have hnc : ∀ w : {w // IsComplex w}, ‖extensionEmbedding w.1 (x w.1)‖ = ‖x w.1‖ := fun w ↦
    (isometry_extensionEmbedding w.1).norm_map_of_map_zero (map_zero _) _
  simp only [hr, hnr, hnc, mult_isReal, mult_isComplex]
  have hexp : ((Real.exp (-π * (∑ w : {w // IsReal w}, ‖x w.1‖ ^ 2 +
      2 * ∑ w : {w // IsComplex w}, ‖x w.1‖ ^ 2)) : ℝ) : ℂ) =
      (∏ w : {w // IsReal w}, ((Real.exp (-(π * ((1 : ℕ) : ℝ) * ‖x w.1‖ ^ 2)) : ℝ) : ℂ)) *
        ∏ w : {w // IsComplex w}, ((Real.exp (-(π * ((2 : ℕ) : ℝ) * ‖x w.1‖ ^ 2)) : ℝ) : ℂ) := by
    rw [← ofReal_prod, ← ofReal_prod, ← ofReal_mul, ← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add]
    congr 2
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun w _ ↦ by push_cast; ring
  rw [hexp]
  ring

theorem toIdele_ofInfinite (a : (InfiniteAdeleRing K)ˣ) :
    χ.toIdele (IdeleGroup.ofInfinite a) =
      ∏ w, χ.infiniteComponent w (IdeleGroup.infiniteComponent w a) := by
  have ha : a = ∏ w, Units.map (IdeleGroup.infiniteAdeleSingle w) (IdeleGroup.infiniteComponent w a) := by
    ext1
    rw [Units.coe_prod]
    simp only [Units.coe_map, IdeleGroup.coe_infiniteComponent]
    exact (Finset.univ_prod_mulSingle (fun w ↦ (a : InfiniteAdeleRing K) w)).symm
  conv_lhs => rw [ha]
  rw [map_prod, map_prod]
  exact Finset.prod_congr rfl fun w _ ↦ by
    rw [IdeleGroup.ofInfinite_map_infiniteAdeleSingle]
    rfl

theorem integral_infiniteSchwartz {s : ℂ} (hs : 0 < s.re) :
    ∫ a : (InfiniteAdeleRing K)ˣ, χ.infiniteSchwartz (homeomorphMixedSpace K a) *
      (χ.toIdele (IdeleGroup.ofInfinite a) : ℂ) *
        ((∏ w, ‖(a : InfiniteAdeleRing K) w‖ ^ w.mult : ℝ) : ℂ) ^ s ∂infiniteIdeleMeasure K =
      ∏ w, infiniteConst w * χ.infiniteGamma w s := by
  have he : MeasurableEmbedding (infiniteUnitsEquiv K).symm :=
    (infiniteUnitsEquiv K).symm.toHomeomorph.measurableEmbedding
  rw [infiniteIdeleMeasure, he.integral_map]
  have hpt : ∀ y : Π w : InfinitePlace K, (w.Completion)ˣ,
      χ.infiniteSchwartz (homeomorphMixedSpace K ((infiniteUnitsEquiv K).symm y)) *
        (χ.toIdele (IdeleGroup.ofInfinite ((infiniteUnitsEquiv K).symm y)) : ℂ) *
        ((∏ w, ‖(((infiniteUnitsEquiv K).symm y : (InfiniteAdeleRing K)ˣ) :
          InfiniteAdeleRing K) w‖ ^ w.mult : ℝ) : ℂ) ^ s =
      ∏ w, χ.infiniteTest w (y w) * χ.infiniteComponent w (y w) *
        ((‖(y w : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ s := by
    intro y
    have hy : ∀ w, (((infiniteUnitsEquiv K).symm y : (InfiniteAdeleRing K)ˣ) :
        InfiniteAdeleRing K) w = (y w : w.Completion) := fun w ↦ rfl
    have hc : ∀ w, IdeleGroup.infiniteComponent w ((infiniteUnitsEquiv K).symm y) = y w :=
      fun w ↦ Units.ext rfl
    rw [infiniteSchwartz_homeomorphMixedSpace, toIdele_ofInfinite,
      ofReal_finsetProd_cpow _ (fun w _ ↦ by positivity)]
    have hcp : ((∏ w, χ.infiniteComponent w (y w) : Circle) : ℂ) =
        ∏ w, (χ.infiniteComponent w (y w) : ℂ) :=
      map_prod Circle.coeHom (fun w ↦ χ.infiniteComponent w (y w)) Finset.univ
    simp only [hy, hc, hcp, Finset.prod_mul_distrib]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have hfub := integral_fintype_prod_eq_prod (μ := fun w : InfinitePlace K ↦ infinitePlaceUnitsMeasure w)
    (fun w (u : (w.Completion)ˣ) ↦ χ.infiniteTest w u * (χ.infiniteComponent w u : ℂ) *
      ((‖(u : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ s)
  exact hfub.trans (Finset.prod_congr rfl fun w _ ↦ χ.integral_infiniteTest w hs)

end HeckeCharacter

end

end GroundTheory.Global
end

-- bundled from GroundTheory.GlobalFields.TateThesis.SchwartzBruhatDual
section
namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MeasureTheory Measure WithZero
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise nonZeroDivisors

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem eq_exp_of_le_of_not_le {a : ℤᵐ⁰} {n : ℤ} (h1 : a ≤ exp n) (h2 : ¬ a ≤ exp (n - 1)) :
    a = exp n := by
  have ha : a ≠ 0 := by
    rintro rfl
    exact h2 zero_le
  rw [← exp_log ha] at h1 h2 ⊢
  rw [exp_le_exp] at h1 h2
  rw [exp_inj]
  omega

theorem coe_differentIdeal_ne_zero :
    ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
  exact differentIdeal_ne_bot

theorem intValuation_le_of_mem_ideal (v : HeightOneSpectrum (𝓞 K)) {𝔞 : Ideal (𝓞 K)} (h𝔞 : 𝔞 ≠ ⊥)
    {y : 𝓞 K} (hy : y ∈ 𝔞) :
    v.intValuation y ≤ exp (-FractionalIdeal.count K v (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) := by
  rw [FractionalIdeal.count_coe K v h𝔞]
  refine (v.intValuation_le_pow_iff_mem y _).mpr ?_
  have hle := (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr h𝔞)
      v.associates_irreducible (k := (Associates.mk v.asIdeal).count (Associates.mk 𝔞).factors)).mpr
      le_rfl
  rw [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le] at hle
  exact hle hy

theorem exists_mem_ideal_intValuation_eq (v : HeightOneSpectrum (𝓞 K)) {𝔞 : Ideal (𝓞 K)}
    (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ y ∈ 𝔞,
      v.intValuation y = exp (-FractionalIdeal.count K v (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) := by
  set n := (Associates.mk v.asIdeal).count (Associates.mk 𝔞).factors with hn
  have hnot : ¬ 𝔞 ≤ v.asIdeal ^ (n + 1) := by
    intro h
    have h' := (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr h𝔞)
      v.associates_irreducible (k := n + 1)).not
    rw [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le] at h'
    exact h'.mpr (by omega) h
  obtain ⟨y, hy, hyn⟩ := SetLike.not_le_iff_exists.mp hnot
  refine ⟨y, hy, eq_exp_of_le_of_not_le (intValuation_le_of_mem_ideal v h𝔞 hy) fun h ↦ hyn ?_⟩
  rw [← v.intValuation_le_pow_iff_mem]
  convert h using 2
  rw [FractionalIdeal.count_coe K v h𝔞, ← hn]
  push_cast
  ring

theorem mem_localInvDifferent_iff_valued (v : HeightOneSpectrum (𝓞 K)) (z : v.adicCompletion K) :
    z ∈ localInvDifferent v ↔ Valued.v z ≤
      exp (FractionalIdeal.count K v ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) :
        FractionalIdeal (𝓞 K)⁰ K)) := by
  set δ := FractionalIdeal.count K v ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) :
        FractionalIdeal (𝓞 K)⁰ K)
  constructor
  · intro h
    obtain ⟨y, hy, hyv⟩ := exists_mem_ideal_intValuation_eq v (differentIdeal_ne_bot (A := ℤ))
    have h1 := h y hy
    rw [mem_adicCompletionIntegers, Valuation.map_mul, valued_coe_algebraMap, hyv] at h1
    calc Valued.v z = Valued.v z * exp (-δ) * exp δ := by
            rw [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]
      _ ≤ 1 * exp δ := by gcongr
      _ = exp δ := one_mul _
  · intro h y hy
    rw [mem_adicCompletionIntegers, Valuation.map_mul, valued_coe_algebraMap]
    calc Valued.v z * v.intValuation y ≤ exp δ * exp (-δ) :=
          mul_le_mul' h (intValuation_le_of_mem_ideal v (differentIdeal_ne_bot (A := ℤ)) hy)
      _ = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]


variable (K) in
def finiteAdelicChar : AddChar 𝔸ᶠ[K] Circle :=
  (adelicChar K).compAddMonoidHom finiteAdeleInr

theorem finiteAdelicChar_apply (x : 𝔸ᶠ[K]) :
    finiteAdelicChar K x = adelicChar K (finiteAdeleInr x) := rfl

theorem continuous_finiteAdelicChar : Continuous (finiteAdelicChar K) :=
  (continuous_adelicChar (K := K)).comp (continuous_const.prodMk continuous_id)

theorem finiteAdelicChar_eq_one_of_mem {x : 𝔸ᶠ[K]} (hx : x ∈ finiteInvDifferent K) :
    finiteAdelicChar K x = 1 := by
  rw [finiteAdelicChar_apply, adelicChar_of_mem_invDifferentAdeles
    (mem_invDifferentAdeles.mpr (by rw [finiteAdeleInr_snd]; exact hx)),
    finiteAdeleInr_fst, map_zero, neg_zero, AddChar.map_zero_eq_one]

theorem finiteAdelicChar_finiteAdeleSingleAdd (v : HeightOneSpectrum (𝓞 K))
    (w : v.adicCompletion K) :
    finiteAdelicChar K (finiteAdeleSingleAdd v w) = localAdelicChar K v w := rfl

theorem finiteAdeleSingleAdd_mul (v : HeightOneSpectrum (𝓞 K)) (w : v.adicCompletion K)
    (y : 𝔸ᶠ[K]) : finiteAdeleSingleAdd v w * y = finiteAdeleSingleAdd v (w * y v) := by
  refine Subtype.ext (funext fun u ↦ ?_)
  change finiteAdeleSingleAdd v w u * y u = finiteAdeleSingleAdd v (w * y v) u
  rcases eq_or_ne u v with rfl | hu
  · rw [finiteAdeleSingleAdd_apply_self, finiteAdeleSingleAdd_apply_self]
  · rw [finiteAdeleSingleAdd_apply_of_ne hu, finiteAdeleSingleAdd_apply_of_ne hu, zero_mul]

theorem count_traceDualIdeal (v : HeightOneSpectrum (𝓞 K)) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    FractionalIdeal.count K v (traceDualIdeal K I : FractionalIdeal (𝓞 K)⁰ K) =
      -(FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) +
        FractionalIdeal.count K v ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) :
          FractionalIdeal (𝓞 K)⁰ K)) := by
  rw [traceDualIdeal_eq, FractionalIdeal.count_inv,
    FractionalIdeal.count_mul K v I.ne_zero coe_differentIdeal_ne_zero]

theorem forall_finiteAdelicChar_mul_eq_one_iff (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (y : 𝔸ᶠ[K]) :
    (∀ x ∈ idealFiniteAdeles I, finiteAdelicChar K (x * y) = 1) ↔
      y ∈ idealFiniteAdeles (traceDualIdeal K I) := by
  simp only [mem_idealFiniteAdeles, count_traceDualIdeal, neg_neg]
  constructor
  · intro h v
    set i := FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)
    set δ := FractionalIdeal.count K v ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) :
      FractionalIdeal (𝓞 K)⁰ K)
    set t : v.adicCompletion K := ((uniformizerUnit v ^ i : (v.adicCompletion K)ˣ) :
      v.adicCompletion K) with ht
    have htv : Valued.v t = exp (-i) := valued_uniformizerUnit_zpow v i
    have hloc : t * y v ∈ localInvDifferent v := by
      refine (forall_localAdelicChar_mul_eq_one_iff v _).mp fun a ha ↦ ?_
      have hx : finiteAdeleSingleAdd v (a * t) ∈ idealFiniteAdeles I := by
        intro u
        rcases eq_or_ne u v with rfl | hu
        · rw [finiteAdeleSingleAdd_apply_self, Valuation.map_mul, htv]
          exact mul_le_of_le_one_left' ((mem_adicCompletionIntegers _ _ _).mp ha)
        · rw [finiteAdeleSingleAdd_apply_of_ne hu, Valuation.map_zero]
          exact zero_le
      have := h _ hx
      rwa [finiteAdeleSingleAdd_mul, finiteAdelicChar_finiteAdeleSingleAdd, mul_assoc] at this
    rw [mem_localInvDifferent_iff_valued, Valuation.map_mul, htv] at hloc
    calc Valued.v (y v) = exp i * (exp (-i) * Valued.v (y v)) := by
            rw [← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]
      _ ≤ exp i * exp δ := by gcongr
      _ = exp (i + δ) := by rw [exp_add]
  · intro hy x hx
    refine finiteAdelicChar_eq_one_of_mem fun v ↦ ?_
    change x v * y v ∈ localInvDifferent v
    rw [mem_localInvDifferent_iff_valued, Valuation.map_mul]
    calc Valued.v (x v) * Valued.v (y v) ≤
          exp (-FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)) *
            exp (FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) +
              FractionalIdeal.count K v ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) :
                FractionalIdeal (𝓞 K)⁰ K)) := mul_le_mul' (hx v) (hy v)
      _ = _ := by rw [← exp_add, neg_add_cancel_left]

theorem traceDualIdeal_traceDualIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    traceDualIdeal K (traceDualIdeal K I) = I :=
  Units.ext (FractionalIdeal.dual_dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))

theorem finiteAdeleMeasure_idealFiniteAdeles_toReal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (finiteAdeleMeasure K (idealFiniteAdeles I)).toReal =
      ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ))⁻¹ *
        (NNReal.sqrt ‖discr K‖₊ : ℝ)⁻¹ := by
  rw [finiteAdeleMeasure_idealFiniteAdeles, ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (inv_nonneg.mpr (by exact_mod_cast (FractionalIdeal.absNorm_nonneg _))),
    ENNReal.coe_toReal, NNReal.coe_inv]

theorem finiteAdeleMeasure_idealFiniteAdeles_ne_top (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    finiteAdeleMeasure K (idealFiniteAdeles I) ≠ ∞ := by
  rw [finiteAdeleMeasure_idealFiniteAdeles]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top

theorem finiteAdeleMeasure_idealFiniteAdeles_mul_traceDual (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (finiteAdeleMeasure K (idealFiniteAdeles I)).toReal *
      (finiteAdeleMeasure K (idealFiniteAdeles (traceDualIdeal K I))).toReal = 1 := by
  rw [finiteAdeleMeasure_idealFiniteAdeles_toReal, finiteAdeleMeasure_idealFiniteAdeles_toReal,
    traceDualIdeal_eq, map_inv₀, map_mul, FractionalIdeal.coeIdeal_absNorm,
    absNorm_differentIdeal K (𝓞 K)]
  have hN : (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ≠ 0 := by
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.mpr I.ne_zero)
  have hs : ((NNReal.sqrt ‖discr K‖₊ : ℝ)) ^ 2 = ((discr K).natAbs : ℝ) := by
    rw [← NNReal.coe_pow, NNReal.sq_sqrt, coe_nnnorm, Int.norm_eq_abs, Nat.cast_natAbs,
      Int.cast_abs]
  have hs0 : (NNReal.sqrt ‖discr K‖₊ : ℝ) ≠ 0 := by
    exact_mod_cast sqrt_discr_ne_zero K
  generalize (NNReal.sqrt ‖discr K‖₊ : ℝ) = s at hs hs0 ⊢
  generalize (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) = N at hN ⊢
  rw [Rat.cast_inv, Rat.cast_mul, Rat.cast_natCast, ← hs]
  field_simp

end

end GroundTheory.Global
end

