module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Assembly
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace FibreLocal

@[local instance] theorem isProbabilityMeasure_sphere : IsProbabilityMeasure sphereMeasure :=
  sphereInv_thm.1

theorem add_mul_gPoly (k : ℕ) :
    (X 0 + X 1 : MvPolynomial (Fin 2) ℝ) * gPoly k = X 1 * (X 0 ^ (2 * k) - X 1 ^ (2 * k)) := by
  have h := (Commute.all (-(X 1 : MvPolynomial (Fin 2) ℝ)) (X 0)).geom_sum₂_mul (2 * k)
  have hs : ∑ j ∈ Finset.range (2 * k),
      (-1 : ℝ) ^ j • ((X 0 : MvPolynomial (Fin 2) ℝ) ^ (2 * k - 1 - j) * X 1 ^ j) =
      ∑ i ∈ Finset.range (2 * k), (-(X 1 : MvPolynomial (Fin 2) ℝ)) ^ i * X 0 ^ (2 * k - 1 - i) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, map_pow, map_neg, map_one, neg_pow (X 1 : MvPolynomial (Fin 2) ℝ)]
    ring
  rw [gPoly, hs]
  rw [(even_two_mul k).neg_pow] at h
  linear_combination (-(X 1 : MvPolynomial (Fin 2) ℝ)) * h

theorem gPoly_eq (k : ℕ) : gPoly k = FlagBundles.gKernel ℝ k := by
  have hne : (X 0 + X 1 : MvPolynomial (Fin 2) ℝ) ≠ 0 := by
    intro h
    have := congrArg (eval ![1, 0]) h
    simp at this
  exact mul_left_cancel₀ hne (by rw [add_mul_gPoly, (FlagBundles.GKernelIdentity.full ℝ k).1])

theorem dgPoly_eq (k : ℕ) : dgPoly k = FlagBundles.gMixed k := by
  rw [dgPoly, FlagBundles.gMixed, gPoly_eq]

theorem integrable_kernel :
    Integrable (fun p : S2 × S2 => (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (p.1 : E3) (p.2 : E3)) / 2))
      (sphereMeasure.prod sphereMeasure) :=
  FlagBundles.FibreIntegralInvariant.integrable_kernel FlagBundles.FibreConstantClosedForm.full

theorem integrable_mul (f : S2 × S2 → ℝ) (hf : Continuous f) :
    Integrable (fun p : S2 × S2 =>
      (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (p.1 : E3) (p.2 : E3)) / 2) * f p)
      (sphereMeasure.prod sphereMeasure) :=
  FlagBundles.FibreIntegralInvariant.integrable_term integrable_kernel f hf

theorem continuous_evalPair (g : MvPolynomial (Fin 2) ℝ) (u v : S2 × S2 → ℝ) (hu : Continuous u)
    (hv : Continuous v) : Continuous fun p => eval ![u p, v p] g := by
  have h2 : Continuous fun p => (![u p, v p] : Fin 2 → ℝ) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · simpa using hu
    · simpa using hv
  exact (MvPolynomial.continuous_eval g).comp h2

theorem kappa_eq (k : ℕ) : kappa k = -FlagBundles.fibreConstant k := by
  have hc : Continuous fun p : S2 × S2 => eval ![(p.1 : E3) 2, (p.2 : E3) 2] (dgPoly k) :=
    continuous_evalPair _ _ _ ((EuclideanSpace.proj (2 : Fin 3)).continuous.comp
      (continuous_subtype_val.comp continuous_fst))
      ((EuclideanSpace.proj (2 : Fin 3)).continuous.comp (continuous_subtype_val.comp continuous_snd))
  rw [kappa, FlagBundles.fibreConstant, neg_inj]
  refine (integral_prod _ (integrable_mul _ hc)).symm.trans ?_
  simp_rw [dgPoly_eq]
  rfl

theorem sphere_moment (a : E3) (m : ℕ) :
    ∫ n : S2, inner ℝ a (n : E3) ^ (2 * m) ∂sphereMeasure = inner ℝ a a ^ m / (2 * m + 1) := by
  by_cases ha : a = 0
  · subst ha
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · simp [inner_zero_left, zero_pow (by omega : 2 * m ≠ 0), zero_pow (by omega : m ≠ 0)]
  · set r : ℝ := ‖a‖ with hr
    have hr0 : r ≠ 0 := norm_ne_zero_iff.mpr ha
    set u : E3 := r⁻¹ • a with hu
    have hu1 : ‖u‖ = 1 := by rw [hu, norm_smul, norm_inv, norm_norm, ← hr, inv_mul_cancel₀ hr0]
    have hin : ∀ n : S2, inner ℝ a (n : E3) = r * inner ℝ (n : E3) u := by
      intro n
      rw [hu, inner_smul_right, real_inner_comm, ← mul_assoc, mul_inv_cancel₀ hr0, one_mul]
    have hA := (archimedes_thm u u u (fun t => (r * t) ^ (2 * m)) hu1
      (Continuous.intervalIntegrable (by fun_prop) _ _)).2.1
    simp_rw [hin]
    rw [hA]
    simp_rw [mul_pow]
    rw [intervalIntegral.integral_const_mul, integral_pow, real_inner_self_eq_norm_sq, ← hr]
    have h1 : ((-1 : ℝ)) ^ (2 * m + 1) = -1 := by rw [pow_succ, (even_two_mul m).neg_one_pow]; ring
    rw [h1, ← pow_mul]
    push_cast
    field_simp
    ring

theorem eval_momentPoly {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ)
    (Q : MvPolynomial (Fin 3) (Ω → ℝ)) (hQ : ∀ m, Integrable (fun p => w p * AddMonoidAlgebra.coeff Q m p) μ)
    (a : Fin 3 → ℝ) :
    eval a (momentPoly μ w Q) = ∫ p, w p * eval₂ (Pi.evalRingHom (fun _ : Ω => ℝ) p) a Q ∂μ := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [momentPoly, map_sum]
  simp only [eval_monomial]
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum _ (fun m _ => (hQ m).mul_const _)]
  congr 1
  funext p
  rw [eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [Finsupp.prod]
  ring

def coordS (i : Fin 3) : C(S2, ℝ) :=
  ⟨fun n => (n : E3) i, (EuclideanSpace.proj i).continuous.comp continuous_subtype_val⟩

theorem dotPoly_id_pow (N : ℕ) :
    (dotPoly (id : S2 → S2)) ^ N =
      MvPolynomial.map (ContinuousMap.coeFnRingHom : C(S2, ℝ) →+* (S2 → ℝ)) ((∑ i, X i * C (coordS i)) ^ N) := by
  rw [map_pow, dotPoly]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_X, map_C]
  rfl

theorem pushMomentPoly_eq (k : ℕ) (hk : 1 ≤ k) :
    pushMomentPoly k = -(∑ i, X i ^ 2) ^ (k - 1) := by
  apply MvPolynomial.funext
  intro a
  have hQ : ∀ m, Integrable (fun p : S2 => (1 : ℝ) * AddMonoidAlgebra.coeff ((dotPoly (id : S2 → S2)) ^ (2 * k - 2)) m p)
      sphereMeasure := by
    intro m
    rw [dotPoly_id_pow, coeff_map]
    simp only [one_mul]
    exact (ContinuousMap.continuous (AddMonoidAlgebra.coeff ((∑ i, X i * C (coordS i)) ^ (2 * k - 2)) m)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [pushMomentPoly, smul_eval, eval_momentPoly _ _ _ hQ]
  have he : ∀ p : S2, eval₂ (Pi.evalRingHom (fun _ : S2 => ℝ) p) a ((dotPoly id) ^ (2 * k - 2)) =
      inner ℝ (WithLp.toLp 2 a : E3) (p : E3) ^ (2 * k - 2) := by
    intro p
    rw [eval₂_pow, dotPoly]
    simp [eval₂_sum, PiLp.inner_apply, mul_comm]
  simp_rw [he, one_mul]
  have hkk : 2 * k - 2 = 2 * (k - 1) := by omega
  rw [hkk, sphere_moment]
  have haa : inner ℝ (WithLp.toLp 2 a : E3) (WithLp.toLp 2 a) = ∑ i, a i ^ 2 := by
    rw [real_inner_self_eq_norm_sq, EuclideanSpace.norm_sq_eq]
    simp [sq_abs]
  rw [haa]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_neg, map_pow, map_sum, eval_X]
  have hc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk, Nat.cast_one]
  rw [hc]
  have hk' : (2 * ((k : ℝ) - 1) + 1) ≠ 0 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  field_simp
  ring

theorem fibreMomentPoly_eq (k : ℕ) : fibreMomentPoly k = FlagBundles.fibrePoly k := by
  have hQ : aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] (dgPoly k) =
      FlagBundles.FibreIntegralInvariant.fibreQ k := by
    rw [FlagBundles.FibreIntegralInvariant.fibreQ, dgPoly_eq]
    refine congrArg (fun x => aeval x (FlagBundles.gMixed k)) ?_
    funext r
    fin_cases r <;> simp [dotPoly]
  rw [FlagBundles.FibreIntegralInvariant.fibrePoly_eq, fibreMomentPoly, momentPoly, hQ]
  rfl

theorem proof : FibreLocal.Statement := by
  refine ⟨fun k a => ?_, fun k B _ _ a => ?_, fun k hk a => ?_, fun k hk B _ _ a => ?_, fun k => ?_⟩
  · have hc : Continuous fun p : S2 × S2 => eval ![inner ℝ a (p.1 : E3), inner ℝ a (p.2 : E3)] (dgPoly k) :=
      continuous_evalPair _ _ _ (continuous_const.inner (continuous_subtype_val.comp continuous_fst))
        (continuous_const.inner (continuous_subtype_val.comp continuous_snd))
    refine (integral_prod _ (integrable_mul _ hc)).symm.trans ?_
    simp_rw [dgPoly_eq]
    rw [kappa_eq, neg_neg]
    exact FlagBundles.FibreIntegralInvariant.full.1 k a
  · rw [fibreMomentPoly_eq, FlagBundles.FibreIntegralInvariant.full.2 k B a, kappa_eq, neg_neg]
  · have hkk : 2 * k - 2 = 2 * (k - 1) := by omega
    rw [hkk, sphere_moment]
    have hc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk, Nat.cast_one]
    rw [hc]
    have hk' : (2 * ((k : ℝ) - 1) + 1) ≠ 0 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    field_simp
    ring
  · rw [pushMomentPoly_eq k hk]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_neg, map_pow, map_sum, aeval_X]
  · rw [kappa_eq, FlagBundles.fibreConstant_eq]
    ring

end FibreLocal

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIUnique
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace ThmIUnique

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem recR_congr {I J : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (P : Ideal (MRing ι))
    {n : ℕ} (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι)
    (h : ∀ W ∈ divSupp P s, IsHorizontal W → I W n L = J W n L) :
    recR I P L A s = recR J P L A s := by
  classical
  unfold recR
  congr 1
  refine finsum_mem_congr rfl fun W hW => ?_
  by_cases hh : IsHorizontal W
  · rw [if_pos hh, if_pos hh, h W hW hh]
  · rw [if_neg hh, if_neg hh]

theorem isMultiHomog_one' : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  subst hm
  simp

theorem isMultiHomog_mul' {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]


open Classical in
theorem isMultiHomog_X' (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRing ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => h (congrArg Sigma.fst e).symm
    simp [Finsupp.single_apply, this, h, Pi.single_apply]

theorem isMultiHomog_pow' {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using (isMultiHomog_one' (ι := ι))
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact isMultiHomog_mul' ih hf

theorem isMultiHomog_coordMonomial (c : ∀ k, ι k) (d : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) d := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing ι) ^ d k)
      (∑ k ∈ s, d k • Pi.single k 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (isMultiHomog_one' (ι := ι))
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact isMultiHomog_mul' (isMultiHomog_pow' (isMultiHomog_X' k (c k)) _) ih
  have e : (∑ k, d k • (Pi.single k 1 : K → ℕ)) = d := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ
  rwa [e] at this

theorem coordMonomial_not_mem {P : Ideal (MRing ι)} (hP : P.IsPrime) (c : ∀ k, ι k)
    (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) (d : K → ℕ) :
    (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) ∉ P := by
  intro h
  obtain ⟨k, -, hk⟩ := (hP.prod_mem_iff).mp h
  exact hc k (hP.mem_of_pow_mem _ hk)

theorem eq_of_lower {I J : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsRFamily I) (hJ : IsRFamily J) {P : Ideal (MRing ι)} {m : ℕ}
    (L : Fin m → HermLine ι) (A : HermLine ι) (hP : IsArithVar P (m + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hlow : ∀ W, IsArithVar W m → I W m L = J W m L) :
    I P (m + 1) (Fin.snoc L A) = J P (m + 1) (Fin.snoc L A) := by
  classical
  have hPp : P.IsPrime := hP.2.1.1
  choose c hc using hP.2.1.2.2

  let b : K → ℕ := fun k => (-A.a k).toNat
  let e : K → ℕ := fun k => (A.a k + (b k : ℤ)).toNat
  let B : HermLine ι := HermLine.sqMetric b
  have hB : IsSmoothHerm B := isSmoothHerm_sqMetric b
  have hC : IsSmoothHerm (A.tensor B) := isSmoothHerm_tensor hA hB
  have hBa : ∀ k, B.a k = (b k : ℤ) := fun k => rfl
  have hCa : ∀ k, (A.tensor B).a k = (e k : ℤ) := by
    intro k
    have h0 : (0 : ℤ) ≤ A.a k + ((-A.a k).toNat : ℤ) := by
      rw [Int.toNat_eq_max]
      omega
    exact (Int.toNat_of_nonneg h0).symm
  let sB : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ b k
  let sC : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ e k
  have hsB : IsMultiHomog sB b := isMultiHomog_coordMonomial c b
  have hsC : IsMultiHomog sC e := isMultiHomog_coordMonomial c e
  have hsBP : sB ∉ P := coordMonomial_not_mem hPp c hc b
  have hsCP : sC ∉ P := coordMonomial_not_mem hPp c hc e

  have diff : ∀ F : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ, IsRFamily F →
      F P (m + 1) (Fin.snoc L A) = recR F P L (A.tensor B) sC - recR F P L B sB := by
    intro F hF
    have h1 := hF.1 P m L A B hP hL hA hB
    rw [hF.2 P m L (A.tensor B) sC e hP hL hC hCa hsC hsCP,
      hF.2 P m L B sB b hP hL hB hBa hsB hsBP] at h1
    linarith
  have hor : ∀ (X' : HermLine ι) (s : MRing ι), IsSectionOn P X' s →
      ∀ W ∈ divSupp P s, IsHorizontal W → I W m L = J W m L := fun X' s hs W hW hh =>
    hlow W ((divSuppArith K ι P m X' s W hP hs hW).1 hh)
  rw [diff I hI, diff J hJ,
    recR_congr P L (A.tensor B) sC (hor _ sC ⟨e, hCa, hsC, hsCP⟩),
    recR_congr P L B sB (hor _ sB ⟨b, hBa, hsB, hsBP⟩)]

end ThmIUnique

theorem ThmIUnique.proof (h₀ : ArithVarZeroStatement) : ThmIUnique.Statement := by
  unfold ThmIUnique.Statement UniqueStatement
  intro K _ ι _ I J hI hJ
  have key : ∀ (m : ℕ) (P : Ideal (MRing ι)) (L : Fin (m + 1) → HermLine ι), IsArithVar P (m + 1) →
      (∀ j, IsSmoothHerm (L j)) → I P (m + 1) L = J P (m + 1) L := by
    intro m
    induction m with
    | zero =>
      intro P L hP hL
      rw [← Fin.snoc_init_self L]
      exact ThmIUnique.eq_of_lower hI hJ _ _ hP (fun j => hL j.castSucc) (hL _)
        fun W hW => absurd hW (h₀ K ι W)
    | succ m ih =>
      intro P L hP hL
      rw [← Fin.snoc_init_self L]
      exact ThmIUnique.eq_of_lower hI hJ _ _ hP (fun j => hL j.castSucc) (hL _)
        fun W hW => ih W _ hW fun j => hL j.castSucc
  intro P n L hn hP hL
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact key m P L hP hL

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section Pull

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]

def pullHerm {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) (A : HermLine ι) :
    HermLine ι' where
  a := pullDeg κ A.a
  h z := A.h fun p => z (v p)
  pos z hz := A.pos _ fun k => by
    obtain ⟨i', hi'⟩ := hz (κ k)
    obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
    have h2 : p.1 = k := hv.1 (by rw [← hv.2.2.1 p, hp])
    obtain ⟨pk, pi⟩ := p
    simp only at h2
    subst h2
    exact ⟨pi, by rw [hp]; exact hi'⟩
  smul c z hc := by
    show A.h (fun p => c (v p).1 * z (v p)) = (∏ k', ‖c k'‖ ^ pullDeg κ A.a k') * A.h (fun p => z (v p))
    have e1 : (fun p => c (v p).1 * z (v p)) = fun p : Σ k, ι k => (fun k => c (κ k)) p.1 * z (v p) := by
      funext p
      rw [hv.2.2.1 p]
    rw [e1, A.smul _ _ fun k => hc (κ k)]
    congr 1
    refine Fintype.prod_of_injective κ hv.1 _ _ (fun k' hk' => ?_) (fun k => ?_)
    · rw [pullDeg, Function.extend_apply' _ _ _ (by simpa using hk')]
      simp
    · rw [pullDeg, hv.1.extend_apply]

omit [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem isPullHerm_pullHerm {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (A : HermLine ι) : IsPullHerm κ v A (pullHerm hv A) :=
  ⟨rfl, fun _ => rfl⟩

end Pull

section Bundles

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

abbrev FnField (P : Ideal (MRing ι)) : Type := FractionRing (MRing ι ⧸ P)

def genPt (P : Ideal (MRing ι)) : (Σ k, ι k) → FnField P :=
  fun p => algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P (X p))

abbrev PBlk (ι : K → Type) (N1 : ℕ) : K ⊕ Unit → Type := Sum.elim ι fun _ => Fin N1

abbrev PluckerBlocks (N1 n : ℕ) : Fin (n - 1) → Type := fun j => {S : Finset (Fin N1) // S.card = j + 1}

def flagMinor {R : Type} [CommRing R] {n N1 : ℕ} (M : Matrix (Fin n) (Fin N1) R) (j : Fin (n - 1))
    (S : PluckerBlocks N1 n j) : R :=
  (M.submatrix (Fin.castLE (by have := j.2; omega)) (S.1.orderEmbOfFin S.2)).det

def genMat (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) R) :=
  Matrix.of fun a b => X (a, b)

def flagDim (n : ℕ) : ℕ := n * (n - 1) / 2

end Bundles

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingFrac
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def LocRingFrac.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)),
    P.IsPrime → W.IsPrime → P ≤ W →
    ∀ y ∈ locRing P W, ∃ (u v : MRing ι) (a : K → ℕ),
      IsMultiHomog u a ∧ IsMultiHomog v a ∧ v ∉ W ∧ y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) = algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u)

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingNoeth
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def LocRingNoeth.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)),
    P.IsPrime → W.IsPrime → P ≤ W → IsRelevant W → IsNoetherianRing (locRing P W)

end

end GroundTheory.Heights₂.Heights.Inter
end

