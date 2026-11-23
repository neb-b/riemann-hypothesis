module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCurve
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0010

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterDivSupp
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

theorem OrbitCenterDivSupp.proof (hMI : OrbitCenterMemIff.Statement)
    (hPr : OrbitCenterPrime.Statement) (hSP : SubringPrimeMaximal.Statement) :
    OrbitCenterDivSupp.Statement := by
  intro ι _ _ n x s a hx hs hsW v hsv
  obtain ⟨c, hc⟩ := exists_chart_ciSup x hx v
  have hrel : Geo.IsRelevant (ι := blockIdx n) (orbitCenter x v) := fun k ↦ ⟨c k, fun h ↦ by
    have := (hMI ι n x hx v _ _ ((geoMultiHomog_iff _ _).mpr
      (isWeightedHomogeneous_X ℤ (coordDeg n) ⟨k, c k⟩))).mp h
    simp [evalCone, coordDeg, Pi.single_apply, pow_ite, (hc k).1] at this⟩
  have hW : orbitIdeal x ≤ orbitCenter x v := by
    obtain ⟨S, hS, hspan⟩ := OrbitCurve.isMultiHomogIdeal_orbitIdeal x
    have hSW : ∀ F ∈ S, F ∈ orbitIdeal x := fun F hF ↦ by rw [hspan]; exact Ideal.subset_span hF
    rw [hspan]
    refine Ideal.span_le.mpr fun F hF ↦ ?_
    obtain ⟨d, hd⟩ := hS F hF
    refine Ideal.subset_span ⟨d, hd, ?_⟩
    rw [(mem_orbitIdeal_iff_of_isMultiHomog x F d hd).mp (hSW F hF), map_zero]
    exact Finset.prod_pos fun k _ ↦ pow_pos (hc k).2 _
  refine ⟨⟨⟨hPr ι n x hx v, sup_le hW ((Ideal.span_singleton_le_iff_mem _).mpr hsv)⟩,
    fun Q hQ hle ↦ ?_⟩, hrel⟩
  have := hQ.1
  exact orbitCenter_le_of_le hMI hSP x hx v c hc s a hs hsW Q (le_sup_left.trans hQ.2)
    (hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))) hle

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartDehom
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

abbrev chartOneIdeal (c : (k : ι) → Fin (n k + 1)) : Ideal (MvPolynomial (Coord n) ℤ) :=
  Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1)

theorem weightedHomogeneousComponent_mem_of_mem_divSupp (x : Cone n (AlgebraicClosure ℚ))
    {s : MvPolynomial (Coord n) ℤ} {a : ι → ℕ} (hs : IsWeightedHomogeneous (coordDeg n) s a)
    {V : Ideal (MvPolynomial (Coord n) ℤ)} (hV : V ∈ Geo.divSupp (orbitIdeal x) s)
    {f : MvPolynomial (Coord n) ℤ} (hf : f ∈ V) (b : ι → ℕ) :
    weightedHomogeneousComponent (coordDeg n) b f ∈ V := by
  have hP : NumbersDVR.IsMultiHomogIdeal (ι := blockIdx n) (R := ℤ) (orbitIdeal x) :=
    fun g hg b ↦ OrbitCurve.weightedHomogeneousComponent_mem_orbitIdeal x hg b
  have hJ := NumbersDVR.SupSpanMultiHomog.proof ℤ ι (blockIdx n) (orbitIdeal x) s a hP hs
  exact NumbersDVR.MinimalPrimeMultiHomog.proof ℤ ι (blockIdx n) _ V hJ hV.1 f hf b

variable (V : Ideal (MvPolynomial (Coord n) ℤ)) [V.IsPrime]

def classFrac : MvPolynomial (Coord n) ℤ →ₐ[ℤ] FractionRing (MvPolynomial (Coord n) ℤ ⧸ V) :=
  (IsScalarTower.toAlgHom ℤ (MvPolynomial (Coord n) ℤ ⧸ V) _).comp (Ideal.Quotient.mkₐ ℤ V)

def dehomFrac (c : (k : ι) → Fin (n k + 1)) :
    MvPolynomial (Coord n) ℤ →ₐ[ℤ] FractionRing (MvPolynomial (Coord n) ℤ ⧸ V) :=
  aeval fun p ↦ classFrac V (X p) / classFrac V (X ⟨p.1, c p.1⟩)

omit [Fintype ι] [DecidableEq ι] [V.IsPrime] in
theorem classFrac_eq_zero_iff (f : MvPolynomial (Coord n) ℤ) : classFrac V f = 0 ↔ f ∈ V := by
  change algebraMap _ (FractionRing (MvPolynomial (Coord n) ℤ ⧸ V)) (Ideal.Quotient.mk V f) = 0 ↔ _
  rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]

variable {V}

theorem dehomFrac_of_isWeightedHomogeneous (c : (k : ι) → Fin (n k + 1))
    (G : MvPolynomial (Coord n) ℤ) (d : ι → ℕ) (hG : IsWeightedHomogeneous (coordDeg n) G d) :
    dehomFrac V c G = classFrac V G * ∏ k, (classFrac V (X ⟨k, c k⟩) ^ d k)⁻¹ := by
  have e : (aeval fun p ↦ classFrac V (X p)) = classFrac V := MvPolynomial.algHom_ext fun p ↦ aeval_X _ _
  rw [dehomFrac, aeval_div_chart (fun p ↦ classFrac V (X p)) c G d hG, DFunLike.congr_fun e G]

theorem ker_dehomFrac
    (hVh : ∀ f ∈ V, ∀ b : ι → ℕ, weightedHomogeneousComponent (coordDeg n) b f ∈ V)
    {c : (k : ι) → Fin (n k + 1)} (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) :
    RingHom.ker (dehomFrac V c) = V ⊔ chartOneIdeal c := by
  have hz : ∀ k, classFrac V (X ⟨k, c k⟩) ≠ 0 := fun k h ↦ hc k ((classFrac_eq_zero_iff V _).mp h)
  have hle : V ⊔ chartOneIdeal c ≤ RingHom.ker (dehomFrac V c) := by
    refine sup_le (fun f hf ↦ ?_) (Ideal.span_le.mpr ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [RingHom.mem_ker, ← sum_weightedHomogeneousComponent (w := coordDeg n) f,
        finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f), map_sum]
        refine Finset.sum_eq_zero fun b _ ↦ ?_
        rw [dehomFrac_of_isWeightedHomogeneous c _ b
            (weightedHomogeneousComponent_isWeightedHomogeneous b f),
          (classFrac_eq_zero_iff V _).mpr (hVh f hf b), zero_mul]
    · rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, dehomFrac, aeval_X]
      exact sub_eq_zero.mpr (div_self (hz k))
  refine le_antisymm (fun f hf ↦ ?_) hle
  rw [RingHom.mem_ker] at hf
  have hχ : ∀ k, Ideal.Quotient.mk (V ⊔ chartOneIdeal c) (X ⟨k, c k⟩) = 1 := fun k ↦ by
    rw [← map_one (Ideal.Quotient.mk (V ⊔ chartOneIdeal c)), Ideal.Quotient.eq]
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
  obtain ⟨D, G, hG, hGf⟩ := exists_isWeightedHomogeneous_eq_of_chart
    (Ideal.Quotient.mk (V ⊔ chartOneIdeal c)) c hχ f
  have hd : G - f ∈ V ⊔ chartOneIdeal c := Ideal.Quotient.eq.mp hGf
  have h0 : dehomFrac V c G = 0 := by
    have := hle hd
    rwa [RingHom.mem_ker, map_sub, hf, sub_zero] at this
  rw [dehomFrac_of_isWeightedHomogeneous c G D hG, mul_eq_zero] at h0
  have hGV : G ∈ V := by
    refine (classFrac_eq_zero_iff V G).mp (h0.resolve_right ?_)
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ inv_ne_zero (pow_ne_zero _ (hz k))
  simpa using sub_mem (Ideal.mem_sup_left hGV) hd

theorem comap_sup_chartOneIdeal
    (hVh : ∀ f ∈ V, ∀ b : ι → ℕ, weightedHomogeneousComponent (coordDeg n) b f ∈ V)
    {c : (k : ι) → Fin (n k + 1)} (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) :
    (V ⊔ chartOneIdeal c).comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) =
      V.comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) := by
  refine le_antisymm (fun a ha ↦ ?_) (Ideal.comap_mono le_sup_left)
  rw [Ideal.mem_comap, ← ker_dehomFrac hVh hc, RingHom.mem_ker] at ha
  rw [Ideal.mem_comap, ← classFrac_eq_zero_iff V]
  rw [← ha]
  exact ((classFrac V).commutes a).trans ((dehomFrac V c).commutes a).symm

def quotEquivRange
    (hVh : ∀ f ∈ V, ∀ b : ι → ℕ, weightedHomogeneousComponent (coordDeg n) b f ∈ V)
    {c : (k : ι) → Fin (n k + 1)} (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) :
    (MvPolynomial (Coord n) ℤ ⧸ (V ⊔ chartOneIdeal c)) ≃+* (dehomFrac V c).range :=
  (Ideal.quotEquivOfEq (ker_dehomFrac hVh hc).symm).trans
    (Ideal.quotientKerEquivRange (dehomFrac V c)).toRingEquiv


omit [Fintype ι] [DecidableEq ι] in
theorem range_dehomFrac_le {c c' : (k : ι) → Fin (n k + 1)}
    (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V)
    (hc' : ∀ k, (X ⟨k, c' k⟩ : MvPolynomial (Coord n) ℤ) ∉ V)
    (hF : IsField (dehomFrac V c).range) : (dehomFrac V c').range ≤ (dehomFrac V c).range := by
  have hz : ∀ k, classFrac V (X ⟨k, c k⟩) ≠ 0 := fun k h ↦ hc k ((classFrac_eq_zero_iff V _).mp h)
  have hz' : ∀ k, classFrac V (X ⟨k, c' k⟩) ≠ 0 :=
    fun k h ↦ hc' k ((classFrac_eq_zero_iff V _).mp h)
  rw [dehomFrac, ← Algebra.adjoin_range_eq_range_aeval]
  refine Algebra.adjoin_le ?_
  rintro _ ⟨p, rfl⟩
  have hmem : ∀ q : Coord n, classFrac V (X q) / classFrac V (X ⟨q.1, c q.1⟩) ∈ (dehomFrac V c).range :=
    fun q ↦ (AlgHom.mem_range _).mpr ⟨X q, by rw [dehomFrac, aeval_X]⟩
  let u : (dehomFrac V c).range := ⟨_, hmem ⟨p.1, c' p.1⟩⟩
  have hu : u ≠ 0 := fun h ↦ div_ne_zero (hz' p.1) (hz p.1) (congrArg Subtype.val h)
  obtain ⟨w, hw⟩ := hF.mul_inv_cancel hu
  have hinv : (u : FractionRing (MvPolynomial (Coord n) ℤ ⧸ V))⁻¹ ∈ (dehomFrac V c).range := by
    rw [← eq_inv_of_mul_eq_one_right (congrArg Subtype.val hw)]
    exact w.2
  have e : classFrac V (X p) / classFrac V (X ⟨p.1, c' p.1⟩) =
      classFrac V (X p) / classFrac V (X ⟨p.1, c p.1⟩) * (u : FractionRing _)⁻¹ := by
    change _ = _ * (classFrac V (X ⟨p.1, c' p.1⟩) / classFrac V (X ⟨p.1, c p.1⟩))⁻¹
    field_simp [hz p.1, hz' p.1]
  change classFrac V (X p) / classFrac V (X ⟨p.1, c' p.1⟩) ∈ (dehomFrac V c).range
  rw [e]
  exact mul_mem (hmem p) hinv

theorem OrbitChartDehom.proof (hM : OrbitChartMax.Statement) (hQ : OrbitChartQuot.Statement) :
    OrbitChartDehom.Statement := by
  intro ι _ _ _ n A x s hx hs V hV c c' hc hc'
  have hPV : orbitIdeal x ≤ V := le_sup_left.trans hV.1.1.2
  have : V.IsPrime := hV.1.1.1
  obtain ⟨a, -, hsa, -⟩ := id hs
  have hVh : ∀ f ∈ V, ∀ b : ι → ℕ, weightedHomogeneousComponent (coordDeg n) b f ∈ V :=
    fun f hf b ↦ weightedHomogeneousComponent_mem_of_mem_divSupp x ((geoMultiHomog_iff s a).mp hsa)
      hV hf b
  refine ⟨comap_sup_chartOneIdeal hVh hc, ?_⟩
  have hfield : ∀ d : (k : ι) → Fin (n k + 1),
      (∀ k, (X ⟨k, d k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) → IsField (dehomFrac V d).range := by
    intro d hd
    have hxd : ∀ k, x k (d k) ≠ 0 := by
      intro k h0
      apply hd k
      apply hPV
      rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]
      simp [flatCone, h0]
    obtain ⟨eQ⟩ := hQ ι n x d hxd V hPV
    have hmax := hM ι n A x s hx hs V hV d hd
    exact MulEquiv.isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax)
      (eQ.trans (quotEquivRange hVh hd)).symm.toMulEquiv
  have hr : (dehomFrac V c).range = (dehomFrac V c').range :=
    le_antisymm (range_dehomFrac_le hc' hc (hfield c' hc')) (range_dehomFrac_le hc hc' (hfield c hc))
  exact ⟨(quotEquivRange hVh hc).trans
    ((Subalgebra.equivOfEq _ _ hr).toRingEquiv.trans (quotEquivRange hVh hc').symm)⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartMultLemmas
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace OrbitChartMult

variable {ι : Type} {n : ι → ℕ}

def chartCone (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) (D : Type*)
    [CommRing D] [Algebra (chartRing x c) D] : MvPolynomial (Coord n) ℤ →+* MvPolynomial ι D :=
  eval₂Hom (Int.castRingHom _) fun p ↦ C (algebraMap (chartRing x c) D (chartEval x c (X p))) * X p.1

def chartIncl (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    chartRing x c →+* AlgebraicClosure ℚ :=
  (ratioField x).val.toRingHom.comp (chartRing x c).val.toRingHom

variable (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))

theorem chartIncl_injective : Function.Injective (chartIncl x c) :=
  fun _ _ h ↦ Subtype.ext (Subtype.ext h)

theorem chartIncl_chartEval_X (p : Coord n) :
    chartIncl x c (chartEval x c (X p)) = x p.1 p.2 / x p.1 (c p.1) := by
  simp [chartIncl, chartEval, chartRatio]

theorem chartEval_X_chart (hc : ∀ k, x k (c k) ≠ 0) (k : ι) :
    chartEval x c (X ⟨k, c k⟩) = 1 := by
  apply chartIncl_injective x c
  rw [chartIncl_chartEval_X, map_one]
  exact div_self (hc k)

variable [Fintype ι] [DecidableEq ι]


omit [DecidableEq ι] in
theorem chartEval_chartMonomial (hc : ∀ k, x k (c k) ≠ 0) (d : ι → ℕ) :
    chartEval x c (chartMonomial c d) = 1 := by
  simp [chartMonomial, map_prod, chartEval_X_chart x c hc]

theorem chartCone_of_isWeightedHomogeneous (D : Type*) [CommRing D] [Algebra (chartRing x c) D]
    {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ} (hF : IsWeightedHomogeneous (coordDeg n) F d) :
    chartCone x c D F = C (algebraMap (chartRing x c) D (chartEval x c F)) * ∏ k, X k ^ d k := by
  classical
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hm' : ∀ k, ∑ i, m ⟨k, i⟩ = d k := fun k ↦ by
    rw [← weight_coordDeg_apply, hF (mem_support_iff.mp hm)]
  have hε : chartEval x c (monomial m (AddMonoidAlgebra.coeff F m)) =
      algebraMap ℤ _ (AddMonoidAlgebra.coeff F m) * ∏ p, chartEval x c (X p) ^ m p := by
    rw [chartEval, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
    simp only [aeval_X]
  have hX : ∏ p : Coord n, (X p.1 : MvPolynomial ι D) ^ m p = ∏ k, X k ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    show ∏ i, (X k : MvPolynomial ι D) ^ m ⟨k, i⟩ = _
    rw [← hm' k, Finset.prod_pow_eq_pow_sum]
  rw [hε, chartCone, coe_eval₂Hom, eval₂_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow, eq_intCast,
    map_intCast]
  ring


omit [Fintype ι] [DecidableEq ι] in
theorem chartCone_eq_zero_iff (hc : ∀ k, x k (c k) ≠ 0) (F : MvPolynomial (Coord n) ℤ) :
    chartCone x c (chartRing x c) F = 0 ↔ F ∈ orbitIdeal x := by
  let σ : MvPolynomial ι (AlgebraicClosure ℚ) →ₐ[AlgebraicClosure ℚ]
      MvPolynomial ι (AlgebraicClosure ℚ) := aeval fun k ↦ C (x k (c k)) * X k
  let σ' : MvPolynomial ι (AlgebraicClosure ℚ) →ₐ[AlgebraicClosure ℚ]
      MvPolynomial ι (AlgebraicClosure ℚ) := aeval fun k ↦ C (x k (c k))⁻¹ * X k
  have hσ : σ'.comp σ = AlgHom.id _ _ := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [σ, σ', AlgHom.comp_apply, aeval_X, map_mul, aeval_C, AlgHom.id_apply,
      algebraMap_eq, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
  have hσi : Function.Injective σ := fun a b h ↦ by
    have := congrArg σ' h
    rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, hσ, AlgHom.id_apply, AlgHom.id_apply] at this
  have hcomp : (σ.toRingHom.comp (map (chartIncl x c))).comp
      (chartCone x c (chartRing x c)) =
      (Geo.mConeMap (ι := blockIdx n) (flatCone x)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp
    · intro p
      have h1 : chartIncl x c (chartEval x c (X p)) * x p.1 (c p.1) = x p.1 p.2 := by
        rw [chartIncl_chartEval_X, div_mul_cancel₀ _ (hc p.1)]
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, chartCone,
        coe_eval₂Hom, eval₂_X, aeval_X,
        map_mul, map_C, map_X, Algebra.algebraMap_self, RingHom.id_apply, Geo.mConeMap, σ, aeval_C,
        algebraMap_eq, flatCone]
      rw [← mul_assoc, ← C_mul, h1]
  have key : ∀ G, σ (map (chartIncl x c) (chartCone x c (chartRing x c) G)) =
      Geo.mConeMap (ι := blockIdx n) (flatCone x) G := fun G ↦ by
    have := congrArg (fun f ↦ f G) hcomp
    simpa using this
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, ← key]
  constructor
  · intro h
    rw [h, map_zero, map_zero]
  · intro h
    refine map_injective _ (chartIncl_injective x c) (hσi ?_)
    rw [h, map_zero, map_zero]

theorem mem_orbitIdeal_of_chartEval_eq_zero (hc : ∀ k, x k (c k) ≠ 0)
    {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ} (hF : IsWeightedHomogeneous (coordDeg n) F d)
    (h0 : chartEval x c F = 0) : F ∈ orbitIdeal x := by
  rw [← chartCone_eq_zero_iff x c hc, chartCone_of_isWeightedHomogeneous x c _ hF, h0]
  simp


attribute [local instance] MvPolynomial.weightedGradedAlgebra in
theorem weightedHomogeneousComponent_mem_of_isMultiHomogIdeal
    {V : Ideal (MvPolynomial (Coord n) ℤ)} (hV : Geo.IsMultiHomogIdeal (ι := blockIdx n) V)
    {v : MvPolynomial (Coord n) ℤ} (hv : v ∈ V) (e : ι → ℕ) :
    weightedHomogeneousComponent (coordDeg n) e v ∈ V := by
  obtain ⟨S, hS, rfl⟩ := hV
  have hh : (Ideal.span S).IsHomogeneous (weightedHomogeneousSubmodule ℤ (coordDeg n)) :=
    Ideal.homogeneous_span _ S fun f hf ↦ by
      obtain ⟨a, ha⟩ := hS f hf
      exact ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ((geoMultiHomog_iff f a).mp ha)⟩
  exact weightedHomogeneousComponent_mem_of_mem ℤ (coordDeg n) hh hv e

theorem mem_of_chartEval_mem_chartPoint (hc : ∀ k, x k (c k) ≠ 0)
    {V : Ideal (MvPolynomial (Coord n) ℤ)} [hVp : V.IsPrime] (hWV : orbitIdeal x ≤ V)
    (hV : ∀ v ∈ V, ∀ e, weightedHomogeneousComponent (coordDeg n) e v ∈ V)
    (hXV : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V)
    {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ} (hF : IsWeightedHomogeneous (coordDeg n) F d)
    (hFm : chartEval x c F ∈ chartPoint x c V) : F ∈ V := by
  classical
  obtain ⟨v, hv, hvF⟩ := (Ideal.mem_map_iff_of_surjective _ (chartEval_surjective x c)).mp hFm
  have hfin := weightedHomogeneousComponent_finsupp (w := coordDeg n) v
  set S := hfin.toFinset
  have hvsum : v = ∑ e ∈ S, weightedHomogeneousComponent (coordDeg n) e v := by
    conv_lhs => rw [← sum_weightedHomogeneousComponent (w := coordDeg n) v, finsum_eq_sum _ hfin]
  set E : ι → ℕ := d + ∑ e ∈ S, e
  have hdE : d ≤ E := le_self_add
  have heE : ∀ e ∈ S, e ≤ E := fun e he ↦
    (Finset.single_le_sum (f := fun e : ι → ℕ ↦ e) (fun _ _ ↦ zero_le) he).trans le_add_self
  set G := chartMonomial c (E - d) * F -
    ∑ e ∈ S, chartMonomial c (E - e) * weightedHomogeneousComponent (coordDeg n) e v
  have hG : IsWeightedHomogeneous (coordDeg n) G E := by
    rw [← mem_weightedHomogeneousSubmodule]
    refine Submodule.sub_mem _ ?_ (Submodule.sum_mem _ fun e he ↦ ?_)
    · rw [mem_weightedHomogeneousSubmodule]
      simpa [tsub_add_cancel_of_le hdE] using (isWeightedHomogeneous_chartMonomial c (E - d)).mul hF
    · rw [mem_weightedHomogeneousSubmodule]
      simpa [tsub_add_cancel_of_le (heE e he)] using
        (isWeightedHomogeneous_chartMonomial c (E - e)).mul
          (weightedHomogeneousComponent_isWeightedHomogeneous e v)
  have hG0 : chartEval x c G = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [G, map_sub, map_sum, map_mul, chartEval_chartMonomial x c hc, one_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← hvsum, hvF, sub_self]
  have hGW := mem_orbitIdeal_of_chartEval_eq_zero x c hc hG hG0
  have hmem : chartMonomial c (E - d) * F ∈ V := by
    have e : chartMonomial c (E - d) * F = G +
        ∑ e ∈ S, chartMonomial c (E - e) * weightedHomogeneousComponent (coordDeg n) e v := by
      simp only [G, sub_add_cancel]
    rw [e]
    exact V.add_mem (hWV hGW) (V.sum_mem fun e _ ↦ V.mul_mem_left _ (hV v hv e))
  have hmon : chartMonomial c (E - d) ∉ V := by
    rw [chartMonomial]
    intro h
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hXV k (hVp.mem_of_pow_mem _ hk)
  exact (hVp.mem_or_mem hmem).resolve_left hmon

end OrbitChartMult

end

end GroundTheory.Heights₂.Heights
end

