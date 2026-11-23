module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenter
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Comparison

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterDivSupp
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField MvPolynomial

def OrbitCenterDivSupp.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ))
    (s : MvPolynomial (Coord n) ℤ) (a : ι → ℕ),
    BlockNonzero x → Geo.IsMultiHomog (ι := blockIdx n) s a → s ∉ orbitIdeal x →
    ∀ v : FinitePlace (coordField x), s ∈ orbitCenter x v →
      orbitCenter x v ∈ Geo.divSupp (orbitIdeal x) s

theorem exists_finitePlace_two_lt_one (K : Type) [Field K] [NumberField K] :
    ∃ v : FinitePlace K, v 2 < 1 := by
  have : (Ideal.span {(2 : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K)
    (Ideal.span {(2 : ℤ)}) ⊥ (fun a ha ↦ by
      rw [Ideal.mem_comap, Ideal.mem_bot,
        map_eq_zero_iff _ (algebraMap ℤ (𝓞 K)).injective_int] at ha
      simp [ha])
  have h2 : (2 : 𝓞 K) ∈ Q := by
    have h2Z : (2 : ℤ) ∈ Ideal.under ℤ Q :=
      hQc.symm ▸ Ideal.mem_span_singleton_self 2
    simpa using (Ideal.mem_under (A := ℤ) (P := Q)).mp h2Z
  have hne : Q ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mem_bot] at h2
    exact two_ne_zero h2
  refine ⟨FinitePlace.mk ⟨Q, hQ, hne⟩, ?_⟩
  rw [FinitePlace.mk_apply, show (2 : K) = algebraMap (𝓞 K) K 2 from (map_ofNat _ 2).symm]
  exact (FinitePlace.norm_lt_one_iff_mem (K := K)
    (v := (⟨Q, hQ, hne⟩ : IsDedekindDomain.HeightOneSpectrum (𝓞 K))) (2 : 𝓞 K)).mpr h2

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField

def OrbitCenterLe.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ))
    (v : FinitePlace (coordField x)) (F : MvPolynomial (Coord n) ℤ) (d : ι → ℕ),
    Geo.IsMultiHomog (ι := blockIdx n) F d →
      v (evalCone (coordVec x) F) ≤ ∏ k, (⨆ i, v (coordVec x k i)) ^ d k

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterMemIff
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField

def OrbitCenterMemIff.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ)),
    BlockNonzero x → ∀ (v : FinitePlace (coordField x)) (F : MvPolynomial (Coord n) ℤ)
      (d : ι → ℕ), Geo.IsMultiHomog (ι := blockIdx n) F d →
      (F ∈ orbitCenter x v ↔ v (evalCone (coordVec x) F) < ∏ k, (⨆ i, v (coordVec x k i)) ^ d k)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField

def OrbitCenterPrime.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ)),
    BlockNonzero x → ∀ v : FinitePlace (coordField x), (orbitCenter x v).IsPrime

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField

def OrbitCenterZero.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    ∀ v : FinitePlace (coordField x), orbitCenter x v ∉ Geo.divSupp (orbitIdeal x) s →
      finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s)) = 0

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} {n : ι → ℕ}

def chartRatio (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) (p : Coord n) :
    ratioField x :=
  ⟨x p.1 p.2 / x p.1 (c p.1), div_mem_ratioField x p.1 p.2 (c p.1)⟩

def chartRing (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    Subalgebra ℤ (ratioField x) :=
  Algebra.adjoin ℤ (Set.range (chartRatio x c))

def chartEval (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    MvPolynomial (Coord n) ℤ →ₐ[ℤ] chartRing x c :=
  aeval fun p ↦ ⟨chartRatio x c p, Algebra.subset_adjoin (Set.mem_range_self p)⟩

def chartPoint (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (V : Ideal (MvPolynomial (Coord n) ℤ)) : Ideal (chartRing x c) :=
  Ideal.map (chartEval x c) V

def AbsCentredAt {L : Type*} [Field L] (O : Subalgebra ℤ L) (m : Ideal O) (φ : L → ℝ) : Prop :=
  (∀ u : O, φ u ≤ 1) ∧ ∀ u : O, φ u < 1 ↔ u ∈ m

def localQuotLength {O : Type*} [CommRing O] (m : Ideal O) [m.IsPrime] (f : O) : ℕ :=
  (Module.length (Localization.AtPrime m)
    (Localization.AtPrime m ⧸ Ideal.span {algebraMap O (Localization.AtPrime m) f})).toNat


end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitDegreeRatio
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G

def OrbitDegreeRatio.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (x : Cone n (AlgebraicClosure ℚ)), BlockNonzero x →
    Geo.degC (ι := blockIdx n) (orbitIdeal x) = Module.finrank ℚ (ratioField x)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitLocalSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField

def OrbitLocalSum.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    ∀ V ∈ Geo.divSupp (orbitIdeal x) s,
      (Module.finrank ℚ (coordField x) : ℝ) *
          ((Geo.multAt (orbitIdeal x ⊔ Ideal.span {s}) V : ℝ) *
            ((Geo.geoNum (ι := blockIdx n) 0 V Fin.elim0 : ℝ) * Real.log (Geo.charOf V))) =
        (Module.finrank ℚ (ratioField x) : ℝ) *
          ∑ᶠ v ∈ {v : FinitePlace (coordField x) | orbitCenter x v = V},
            (finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s)))

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.PHeightRecR
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}


omit [DecidableEq ι] in
theorem mConeMap_of_isMultiHomog {Ω : Type*} [Field Ω] (y : Coord n → Ω)
    (s : MvPolynomial (Coord n) ℤ) (a : ι → ℕ) (hs : Geo.IsMultiHomog (ι := blockIdx n) s a) :
    Geo.mConeMap (ι := blockIdx n) y s = C (eval₂ (Int.castRingHom Ω) y s) * ∏ k, X k ^ a k := by
  classical
  conv_lhs => rw [s.as_sum]
  conv_rhs => rw [s.as_sum, eval₂_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hmon : ∏ p ∈ m.support, (X p.1 : MvPolynomial ι Ω) ^ m p = ∏ k, X k ^ a k := by
    rw [Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp ↦ by
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero]), Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    show ∏ i, (X k : MvPolynomial ι Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hs m hm k]
  rw [Geo.mConeMap, aeval_monomial, eval₂_monomial, Finsupp.prod, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, hmon, map_mul, map_prod, map_pow, eq_intCast,
    map_intCast]
  ring

theorem evalCone_coordVec_ne_zero (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ)
    (a : ι → ℕ) (hs : Geo.IsMultiHomog (ι := blockIdx n) s a) (hW : s ∉ orbitIdeal x) :
    evalCone (coordVec x) s ≠ 0 := by
  intro h
  apply hW
  have e : eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) (flatCone x) s =
      algebraMap (coordField x) (AlgebraicClosure ℚ) (evalCone (coordVec x) s) := by
    rw [← evalCone_map]
    rfl
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_isMultiHomog _ s a hs, e, h,
    map_zero, map_zero, zero_mul]

theorem HeightRecR.proof (hV : OrbitDivVertical.Statement) (hF : OrbitFiniteSum.Statement)
    (hA : OrbitArchSum.Statement) : HeightRecR.Statement := by
  intro ι _ _ _ n I A x s hx hs
  obtain ⟨a, _, hsa, hsW⟩ := id hs
  have ht : evalCone (coordVec x) s ≠ 0 := evalCone_coordVec_ne_zero x s a hsa hsW
  have e1 : Geo.recR I (orbitIdeal x) (Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) A.toGeo s =
      (∑ᶠ V ∈ Geo.divSupp (orbitIdeal x) s,
        (Geo.multAt (orbitIdeal x ⊔ Ideal.span {s}) V : ℝ) *
          ((Geo.geoNum (ι := blockIdx n) 0 V Fin.elim0 : ℝ) * Real.log (Geo.charOf V))) -
      Geo.arInt (orbitIdeal x) s A.toGeo (Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) := by
    unfold Geo.recR
    congr 1
    refine finsum_mem_congr rfl fun V hV' ↦ ?_
    rw [if_neg (hV ι n A x s hx hs V hV')]
    congr 4
    funext j
    exact j.elim0
  have hpos : ∀ σ : coordField x →+* ℂ, 0 < A.metric (fun k i ↦ σ (coordVec x k i)) :=
    fun σ ↦ A.metric_pos _ (blockNonzero_sigma hx σ)
  have e2 : ∀ σ : coordField x →+* ℂ,
      Real.log (‖evalCone (fun k i ↦ σ (coordVec x k i)) s‖ /
          A.metric (fun k i ↦ σ (coordVec x k i))) =
        Real.log ‖σ (evalCone (coordVec x) s)‖ -
          Real.log (A.metric (fun k i ↦ σ (coordVec x k i))) := fun σ ↦ by
    rw [evalCone_map, Real.log_div (norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr ht)) (hpos σ).ne']
  have hsupp1 : (Function.support fun v : FinitePlace (coordField x) ↦
      finiteTerm A v (coordVec x)).Finite := finite_support_height A x hx
  have hsupp2 : (Function.support fun v : FinitePlace (coordField x) ↦
      Real.log (v (evalCone (coordVec x) s))).Finite := by
    refine Set.Finite.subset (FinitePlace.hasFiniteMulSupport ht) fun v hv h ↦ hv ?_
    simp only [h, Real.log_one]
  have hprod := sum_log_places_eq_zero ht
  rw [e1, hF ι n A x s hx hs, hA ι n A x s hx hs, finsum_sub_distrib hsupp1 hsupp2,
    Finset.sum_congr rfl fun σ _ ↦ e2 σ, Finset.sum_sub_distrib, height]
  simp only [finiteTerm]
  linear_combination (-((Geo.degC (ι := blockIdx n) (orbitIdeal x) : ℝ) /
    Module.finrank ℚ (coordField x))) * hprod

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} {n : ι → ℕ}

def homogForm (g : Polynomial ℤ) (p q : Coord n) : MvPolynomial (Coord n) ℤ :=
  ∑ j ∈ Finset.range (g.natDegree + 1), C (g.coeff j) * X p ^ j * X q ^ (g.natDegree - j)

theorem eval_homogForm (g : Polynomial ℤ) (p q : Coord n) (z : Coord n → ℂ) :
    eval z (map (Int.castRingHom ℂ) (homogForm g p q)) =
      ∑ j ∈ Finset.range (g.natDegree + 1), (g.coeff j : ℂ) * z p ^ j * z q ^ (g.natDegree - j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [homogForm, map_sum]

theorem homog_sum_eq {F : Type*} [Field F] (g : Polynomial ℤ) (u v : F) (hv : v ≠ 0) :
    ∑ j ∈ Finset.range (g.natDegree + 1), (g.coeff j : F) * u ^ j * v ^ (g.natDegree - j) =
      v ^ g.natDegree * Polynomial.aeval (u / v) g := by
  rw [Polynomial.aeval_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' : j ≤ g.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have e : v ^ g.natDegree = v ^ j * v ^ (g.natDegree - j) := by
    rw [← pow_add, Nat.add_sub_cancel' hj']
  rw [e, zsmul_eq_mul, div_pow]
  field_simp

theorem homog_sum_zero {F : Type*} [CommRing F] (g : Polynomial ℤ) (u : F) :
    ∑ j ∈ Finset.range (g.natDegree + 1), (g.coeff j : F) * u ^ j * (0 : F) ^ (g.natDegree - j) =
      (g.leadingCoeff : F) * u ^ g.natDegree := by
  rw [Finset.sum_eq_single g.natDegree]
  · rw [Nat.sub_self, pow_zero, mul_one]
    rfl
  · intro j hj hjN
    have : 0 < g.natDegree - j :=
      Nat.sub_pos_of_lt (lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hjN)
    rw [zero_pow this.ne', mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h

theorem homogForm_mem_orbitIdeal [Fintype ι] [DecidableEq ι] (x : Cone n (AlgebraicClosure ℚ)) (g : Polynomial ℤ)
    (p q : Coord n) (hpq : p.1 = q.1) (hq : flatCone x q ≠ 0)
    (hg : Polynomial.aeval (flatCone x p / flatCone x q) g = 0) :
    homogForm g p q ∈ orbitIdeal x := by
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker]
  set y := flatCone x
  have key : ∀ j ∈ Finset.range (g.natDegree + 1),
      Geo.mConeMap (ι := blockIdx n) y (C (g.coeff j) * X p ^ j * X q ^ (g.natDegree - j)) =
        MvPolynomial.C ((g.coeff j : AlgebraicClosure ℚ) * y p ^ j * y q ^ (g.natDegree - j)) *
          MvPolynomial.X q.1 ^ g.natDegree := by
    intro j hj
    have hj' : j ≤ g.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have e : (MvPolynomial.X q.1 : MvPolynomial ι (AlgebraicClosure ℚ)) ^ g.natDegree =
        MvPolynomial.X q.1 ^ j * MvPolynomial.X q.1 ^ (g.natDegree - j) := by
      rw [← pow_add, Nat.add_sub_cancel' hj']
    simp only [Geo.mConeMap, map_mul, map_pow, aeval_X, e, hpq, eq_intCast, map_intCast]
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [homogForm, map_sum, Finset.sum_congr rfl key, ← Finset.sum_mul, ← map_sum,
    homog_sum_eq g _ _ hq]
  simp only [y] at hg ⊢
  simp only [map_mul, mul_eq_zero]
  exact Or.inl (Or.inr (MvPolynomial.C_eq_zero.mpr (by
    rw [Polynomial.aeval_def] at hg ⊢
    convert hg using 2
    exact RingHom.ext_int _ _)))

theorem exists_int_relation (r : AlgebraicClosure ℚ) :
    ∃ g : Polynomial ℤ, g ≠ 0 ∧ Polynomial.aeval r g = 0 :=
  (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic r)

theorem eval_conj_eq_zero [Fintype ι] [DecidableEq ι] (x : Cone n (AlgebraicClosure ℚ)) (σ : AlgebraicClosure ℚ →+* ℂ)
    {f : MvPolynomial (Coord n) ℤ} (hf : f ∈ orbitIdeal x) :
    eval (fun p ↦ σ (flatCone x p)) (map (Int.castRingHom ℂ) f) = 0 := by
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker] at hf
  have h : ∀ f : MvPolynomial (Coord n) ℤ,
      eval (fun p ↦ σ (flatCone x p)) (map (Int.castRingHom ℂ) f) =
        σ (eval (fun _ : ι ↦ (1 : AlgebraicClosure ℚ))
          (Geo.mConeMap (ι := blockIdx n) (flatCone x) f)) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [Geo.mConeMap]
    | add f g hf hg => simp only [map_add (f := _), hf, hg]
    | mul_X f p hf => simp only [map_mul, hf, eval_X, map_X, Geo.mConeMap, aeval_X, eval_C, mul_one]
  rw [h, hf, map_zero, map_zero]

theorem OrbitDegree.full : OrbitDegree.Statement := by
  intro ι _ _ n x hx
  set W := orbitIdeal x
  set Q := Quot fun z z' : Geo.mcPts (ι := blockIdx n) W ↦
    ∃ c : ι → ℂ, (∀ k, c k ≠ 0) ∧ (z' : Coord n → ℂ) = fun p ↦ c p.1 * (z : Coord n → ℂ) p
  show 0 < Nat.card Q
  rw [Nat.card_pos_iff]

  let _ : Algebra.IsAlgebraic ℤ (AlgebraicClosure ℚ) := ⟨fun r ↦
    (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic r)⟩
  let σ : AlgebraicClosure ℚ →+* ℂ :=
    (IsAlgClosed.lift (R := ℤ) (S := AlgebraicClosure ℚ) (M := ℂ)).toRingHom
  have hσ : (fun p ↦ σ (flatCone x p)) ∈ Geo.mcPts (ι := blockIdx n) W := by
    refine ⟨fun k ↦ ?_, fun f hf ↦ eval_conj_eq_zero x σ hf⟩
    obtain ⟨i, hi⟩ := Function.ne_iff.mp (hx k)
    exact ⟨i, (map_ne_zero σ).mpr hi⟩
  refine ⟨⟨Quot.mk _ ⟨_, hσ⟩⟩, ?_⟩

  obtain ⟨c, hc⟩ := exists_chart hx
  let q : Coord n → Coord n := fun p ↦ ⟨p.1, c p.1⟩
  have hq : ∀ p, flatCone x (q p) ≠ 0 := fun p ↦ hc p.1
  choose g hg0 hg using fun p ↦ exists_int_relation (flatCone x p / flatCone x (q p))
  have hmem : ∀ p, homogForm (g p) p (q p) ∈ W := fun p ↦
    homogForm_mem_orbitIdeal x (g p) p (q p) rfl (hq p) (hg p)
  have hform : ∀ z ∈ Geo.mcPts (ι := blockIdx n) W, ∀ p,
      ∑ j ∈ Finset.range ((g p).natDegree + 1),
        ((g p).coeff j : ℂ) * z p ^ j * z (q p) ^ ((g p).natDegree - j) = 0 := fun z hz p ↦ by
    rw [← eval_homogForm]; exact hz.2 _ (hmem p)

  have hz0 : ∀ z ∈ Geo.mcPts (ι := blockIdx n) W, ∀ k, z ⟨k, c k⟩ ≠ 0 := by
    intro z hz k h0
    obtain ⟨i, hi⟩ := hz.1 k
    have := hform z hz ⟨k, i⟩
    simp only [q] at this
    rw [h0, homog_sum_zero] at this
    exact mul_ne_zero (Int.cast_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr (hg0 _)))
      (pow_ne_zero _ hi) this

  let T : Set (Coord n → ℂ) := Set.pi Set.univ fun p ↦ {t | ((g p).map (Int.castRingHom ℂ)).IsRoot t}
  have hT : T.Finite := Set.Finite.pi fun p ↦
    Polynomial.finite_setOfPred_isRoot ((Polynomial.map_ne_zero_iff (RingHom.injective_int _)).mpr (hg0 p))
  have hrat : ∀ z ∈ Geo.mcPts (ι := blockIdx n) W, (fun p ↦ z p / z (q p)) ∈ T := by
    intro z hz p _
    have h := hform z hz p
    rw [homog_sum_eq _ _ _ (hz0 z hz p.1)] at h
    have h' := (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (hz0 z hz p.1))
    rw [Polynomial.aeval_def, algebraMap_int_eq] at h'
    simpa [Polynomial.IsRoot, Polynomial.eval_map] using h'
  let F : Q → T := Quot.lift (fun z ↦ ⟨_, hrat z.1 z.2⟩) (by
    rintro z z' ⟨a, ha, e⟩
    apply Subtype.ext
    funext p
    simp only [e, q]
    rw [mul_div_mul_left _ _ (ha p.1)])
  have hF : Function.Injective F := by
    rintro ⟨z, hz⟩ ⟨z', hz'⟩ h
    have h' := fun p ↦ congrFun (congrArg Subtype.val h) p
    simp only [F] at h'
    refine Quot.sound ⟨fun k ↦ z' ⟨k, c k⟩ / z ⟨k, c k⟩,
      fun k ↦ div_ne_zero (hz0 z' hz' k) (hz0 z hz k), ?_⟩
    funext p
    have hp := h' p
    simp only [q] at hp
    have h1 := hz0 z hz p.1
    have h2 := hz0 z' hz' p.1
    have e : z' p = z p / z ⟨p.1, c p.1⟩ * z' ⟨p.1, c p.1⟩ := by
      rw [hp, div_mul_cancel₀ _ h2]
    show z' p = z' ⟨p.1, c p.1⟩ / z ⟨p.1, c p.1⟩ * z p
    rw [e]
    field_simp
  have : Finite T := hT.to_subtype
  exact Finite.of_injective F hF

end

end GroundTheory.Heights₂.Heights
end

