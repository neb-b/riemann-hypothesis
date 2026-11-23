module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefProductNonneg
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHyperplaneRegularSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace HyperplaneRegularSection

theorem exists_notMem_of_finite {V : Type*} [AddCommGroup V] [Module ℚ V] (S : Set (Submodule ℚ V))
    (hS : S.Finite) (htop : ∀ W ∈ S, W ≠ ⊤) : ∃ v : V, ∀ W ∈ S, v ∉ W := by
  have hne := Subspace.biUnion_ne_univ_of_top_notMem (k := ℚ) (E := V) (s := hS.toFinset)
    (by rw [Set.Finite.mem_toFinset]; exact fun h => htop ⊤ h rfl)
  obtain ⟨v, hv⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  refine ⟨v, fun W hW hvW => hv ?_⟩
  exact Set.mem_biUnion ((Set.Finite.mem_toFinset hS).mpr hW) hvW

theorem mem_span_of_mul_mem {A : Type*} [CommRing A] [IsNoetherianRing A] (f w u : A)
    (hw : ∀ p ∈ associatedPrimes A (A ⧸ Ideal.span {f}), w ∉ p) (h : w * u ∈ Ideal.span {f}) :
    u ∈ Ideal.span {f} := by
  by_contra hu
  have hx : (Ideal.Quotient.mk (Ideal.span {f}) u) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hmem : w ∈ {r : A | ∃ x : A ⧸ Ideal.span {f}, x ≠ 0 ∧ r • x = 0} :=
    ⟨_, hx, by rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]; exact h⟩
  rw [← biUnion_associatedPrimes_eq_zero_divisors] at hmem
  obtain ⟨p, hp, hwp⟩ := Set.mem_iUnion₂.mp hmem
  exact hw p hp hwp

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

theorem isNoetherianRing_chartRingQ (y : (Σ k, ι k) → Ω) (c' : ∀ k, ι k) :
    IsNoetherianRing (chartRingQ y c') := by
  classical
  refine isNoetherianRing_of_fg ⟨Finset.univ.image fun p : Σ k, ι k => y p / y ⟨p.1, c' p.1⟩, ?_⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rfl

def gen (y : (Σ k, ι k) → Ω) (c' : ∀ k, ι k) (k : K) (i : ι k) : chartRingQ y c' :=
  ⟨y ⟨k, i⟩ / y ⟨k, c' k⟩, Algebra.subset_adjoin ⟨⟨k, i⟩, rfl⟩⟩

def eqn (y : (Σ k, ι k) → Ω) (c c' : ∀ k, ι k) : chartRingQ y c' :=
  ∏ k, gen y c' k (c k)

def avoidSub (y : (Σ k, ι k) → Ω) (c' : ∀ k, ι k) (k : K) (p : Ideal (chartRingQ y c')) :
    Submodule ℚ (ι k → ℚ) :=
  (p.restrictScalars ℚ).comap (Fintype.linearCombination ℚ (gen y c' k))

def twist (y : (Σ k, ι k) → Ω) (c' : ∀ k, ι k) (a : K → ℤ) : Ω :=
  ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))


omit [∀ k, Fintype (ι k)] [CharZero Ω] in
theorem twist_add (y : (Σ k, ι k) → Ω) {c' : ∀ k, ι k} (hc' : ∀ k, y ⟨k, c' k⟩ ≠ 0) (a a' : K → ℤ) :
    twist y c' (a + a') = twist y c' a * twist y c' a' := by
  simp only [twist, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_add₀ (hc' k)]
  congr 1
  simp only [Pi.add_apply]
  ring


omit [∀ k, Fintype (ι k)] [CharZero Ω] in
theorem twist_zero (y : (Σ k, ι k) → Ω) (c' : ∀ k, ι k) : twist y c' 0 = 1 := by
  simp [twist]


omit [∀ k, Fintype (ι k)] in
theorem coe_eqn (y : (Σ k, ι k) → Ω) (c c' : ∀ k, ι k) :
    (eqn y c c' : Ω) = (∏ k, y ⟨k, c k⟩) * twist y c' 1 := by
  simp only [eqn, gen, twist, Pi.one_apply]
  simp [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_inv_distrib]

end HyperplaneRegularSection


set_option synthInstance.maxHeartbeats 400000 in
open HyperplaneRegularSection in
theorem HyperplaneRegularSection.proof : HyperplaneRegularSection.Statement := by
  intro K _ ι _ Ω _ _ y c e hc
  classical
  have hnoeth : ∀ c' : ∀ k, ι k, IsNoetherianRing (chartRingQ y c') := isNoetherianRing_chartRingQ y

  have hlam : ∀ k, ∃ v : ι k → ℚ, ∑ i, v i • y ⟨k, i⟩ ≠ 0 ∧
      ∀ c' : ∀ k, ι k, (∀ k, y ⟨k, c' k⟩ ≠ 0) →
        ∀ p ∈ associatedPrimes (chartRingQ y c') (chartRingQ y c' ⧸ Ideal.span {eqn y c c'}),
          Fintype.linearCombination ℚ (gen y c' k) v ∉ p := by
    intro k
    let S : Set (Submodule ℚ (ι k → ℚ)) :=
      {LinearMap.ker (Fintype.linearCombination ℚ fun i => y ⟨k, i⟩)} ∪
        ⋃ c' : {c' : ∀ k, ι k // ∀ k, y ⟨k, c' k⟩ ≠ 0},
          avoidSub y c'.1 k '' associatedPrimes (chartRingQ y c'.1)
            (chartRingQ y c'.1 ⧸ Ideal.span {eqn y c c'.1})
    have hS : S.Finite := (Set.finite_singleton _).union
      (Set.finite_iUnion fun c' => (associatedPrimes.finite _ _).image _)
    have htop : ∀ W ∈ S, W ≠ ⊤ := by
      intro W hW hWtop
      rcases hW with hW | hW
      · rw [Set.mem_singleton_iff] at hW
        have h1 : Pi.single (c k) (1 : ℚ) ∈ W := hWtop ▸ Submodule.mem_top
        rw [hW, LinearMap.mem_ker, Fintype.linearCombination_apply_single, one_smul] at h1
        exact hc k h1
      · obtain ⟨c', p, hp, rfl⟩ := Set.mem_iUnion.mp hW
        have h1 : Pi.single (c'.1 k) (1 : ℚ) ∈ avoidSub y c'.1 k p := hWtop ▸ Submodule.mem_top
        rw [avoidSub, Submodule.mem_comap, Submodule.restrictScalars_mem,
          Fintype.linearCombination_apply_single, one_smul,
          show gen y c'.1 k (c'.1 k) = 1 from Subtype.ext (div_self (c'.2 k))] at h1
        exact (IsAssociatedPrime.isPrime hp).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    obtain ⟨v, hv⟩ := exists_notMem_of_finite S hS htop
    refine ⟨v, fun h0 => hv _ (Or.inl rfl) ?_, fun c' hc' p hp hvp =>
      hv _ (Or.inr (Set.mem_iUnion.mpr ⟨⟨c', hc'⟩, p, hp, rfl⟩)) hvp⟩
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply]
    exact h0
  choose v hv0 hvp using hlam
  set m := ∏ k, y ⟨k, c k⟩ with hm_def
  have hm : m ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  set l : K → Ω := fun k => ∑ i, v k i • y ⟨k, i⟩ with hl
  set σ : Ω := ∏ k, l k ^ e k with hσ

  have hφ : ∀ (c' : ∀ k, ι k) (k : K),
      ((Fintype.linearCombination ℚ (gen y c' k) (v k) : chartRingQ y c') : Ω) = l k / y ⟨k, c' k⟩ := by
    intro c' k
    simp [Fintype.linearCombination_apply, gen, hl, Finset.sum_div, smul_div_assoc]
  let w : ∀ c' : ∀ k, ι k, chartRingQ y c' := fun c' =>
    ∏ k, Fintype.linearCombination ℚ (gen y c' k) (v k) ^ e k
  have hw : ∀ c' : ∀ k, ι k, (∀ k, y ⟨k, c' k⟩ ≠ 0) →
      (w c' : Ω) = σ * twist y c' (fun k => (e k : ℤ)) := by
    intro c' hc'
    simp only [w, SubmonoidClass.coe_finsetProd, SubmonoidClass.coe_pow, hφ, twist, hσ, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [div_pow, zpow_neg, Nat.cast_one, one_mul, zpow_natCast, div_eq_mul_inv]
  have hwp : ∀ c' : ∀ k, ι k, (∀ k, y ⟨k, c' k⟩ ≠ 0) →
      ∀ p ∈ associatedPrimes (chartRingQ y c') (chartRingQ y c' ⧸ Ideal.span {eqn y c c'}), w c' ∉ p := by
    intro c' hc' p hp hwp
    have := IsAssociatedPrime.isPrime hp
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (p := p)).mp hwp
    exact hvp k c' hc' p hp (this.mem_of_pow_mem _ hk)
  refine ⟨σ, Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hv0 k), ?_, ?_⟩
  · intro c' hc'
    show σ * twist y c' (fun k => (e k : ℤ)) ∈ chartRingQ y c'
    rw [← hw c' hc']
    exact (w c').2
  · intro b s hs h c' hc'
    have hnc := hnoeth c'
    have hT : twist y c' 1 * twist y c' (-1) = 1 := by
      rw [← twist_add y hc', add_neg_cancel, twist_zero]
    have hM : m * m⁻¹ = 1 := mul_inv_cancel₀ hm
    let u : chartRingQ y c' := ⟨s * twist y c' b, hs c' hc'⟩
    let u' : chartRingQ y c' :=
      ⟨σ * s / m * twist y c' (b + (fun k => (e k : ℤ)) - 1), h c' hc'⟩
    have key : w c' * u = eqn y c c' * u' := by
      apply Subtype.ext
      simp only [Subalgebra.coe_mul, u, u']
      rw [hw c' hc', coe_eqn, ← hm_def, sub_eq_add_neg, twist_add y hc', twist_add y hc']
      linear_combination (-(σ * s * twist y c' b * twist y c' (fun k => (e k : ℤ)))) * hM +
        (-(σ * s * twist y c' b * twist y c' (fun k => (e k : ℤ))) * (m * m⁻¹)) * hT
    have hu : u ∈ Ideal.span {eqn y c c'} :=
      mem_span_of_mul_mem _ _ _ (hwp c' hc') (by
        rw [key]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hu
    have ha' : (a : Ω) * (m * twist y c' 1) = s * twist y c' b := by
      rw [← coe_eqn]
      exact congrArg Subtype.val ha
    show s / m * twist y c' (b - 1) ∈ chartRingQ y c'
    have heq : s / m * twist y c' (b - 1) = a := by
      rw [sub_eq_add_neg, twist_add y hc', div_eq_mul_inv]
      linear_combination (-(m⁻¹ * twist y c' (-1))) * ha' + ((a : Ω) * (twist y c' 1 * twist y c' (-1))) * hM +
        (a : Ω) * hT
    rw [heq]
    exact a.2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIsomInvariance
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

namespace IsomInvariance

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_ratSection {P : Ideal (MRing ι)} (hP : P.IsPrime) (hrel : IsRelevant P) (B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) :
    ∃ s t : MRing ι, ReciprocityTheory.ChartRestriction.G.AI.I2.IsRatSectionOn P B s t := by
  classical
  let c : ∀ k, ι k := fun k => (hrel k).choose
  have hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P := fun k => (hrel k).choose_spec
  exact ⟨_, _, fun k => (B.a k).toNat, fun k => (-B.a k).toNat, Inter.AvoidRing.isMultiHomog_coordProd c _,
    Inter.AvoidRing.isMultiHomog_coordProd c _, Inter.AvoidRing.coordProd_not_mem hP c hc _,
    Inter.AvoidRing.coordProd_not_mem hP c hc _, fun k => Int.toNat_sub_toNat_neg _⟩

theorem snoc_eq (hR : RatRStatement) {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) {P : Ideal (MRing ι)} {m : ℕ} (N : Fin m → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (hP : IsArithVar P (m + 1)) (hN : ∀ j, IsSmoothHerm (N j)) (hA : IsSmoothHerm A) (hB : IsSmoothHerm B)
    (hAB : IsIsometricOn P A B) : I P (m + 1) (Fin.snoc N A) = I P (m + 1) (Fin.snoc N B) := by
  obtain ⟨f, g, α, β, hf, hg, hfP, hgP, hdeg, hdiv, hnorm⟩ := hAB
  have hPp : P.IsPrime := hP.2.1.1
  have nm : ∀ {x y : MRing ι}, x ∉ P → y ∉ P → x * y ∉ P := fun hx hy h => (hPp.mem_or_mem h).elim hx hy
  obtain ⟨s, t, σ, τ, hs, ht, hsP, htP, hst⟩ := exists_ratSection hPp hP.2.1.2.2 B
  have hB' : ReciprocityTheory.ChartRestriction.G.AI.I2.IsRatSectionOn P B (s * g) (t * g) :=
    ⟨σ + β, τ + β, Inter.AvoidRing.isMultiHomog_mul hs hg, Inter.AvoidRing.isMultiHomog_mul ht hg,
      nm hsP hgP, nm htP hgP, fun k => by have := hst k; simp only [Pi.add_apply]; push_cast; linarith⟩
  have hA' : ReciprocityTheory.ChartRestriction.G.AI.I2.IsRatSectionOn P A (s * f * g) (t * g * g) :=
    ⟨σ + α + β, τ + β + β,
      Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_mul hs hf) hg,
      Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_mul ht hg) hg,
      nm (nm hsP hfP) hgP, nm (nm htP hgP) hgP,
      fun k => by have := hst k; have := hdeg k; simp only [Pi.add_apply]; push_cast; linarith⟩
  rw [hR K ι I hI P m N A _ _ hP hN hA hA', hR K ι I hI P m N B _ _ hP hN hB hB']
  unfold recRRat
  have hfg : cycR I P N f = cycR I P N g := by
    rw [Inter.cycR_eq_sum, Inter.cycR_eq_sum, hdiv]
  have hint : ptsIntegral P (pot N) (logNormRat A (s * f * g) (t * g * g)) =
      ptsIntegral P (pot N) (logNormRat B (s * g) (t * g)) := by
    refine Inter.DiagRAux.ptsIntegral_congr_mcPts P (fun _ _ _ => rfl) fun z hz => ?_
    unfold logNormRat
    congr 1
    have ha := A.pos z hz.1
    have hb := B.pos z hz.1
    have hn := hnorm z hz
    simp only [map_mul, norm_mul] at hn ⊢
    set S := ‖eval z (map (Int.castRingHom ℂ) s)‖
    set T := ‖eval z (map (Int.castRingHom ℂ) t)‖
    set F := ‖eval z (map (Int.castRingHom ℂ) f)‖
    set G := ‖eval z (map (Int.castRingHom ℂ) g)‖
    rcases eq_or_ne T 0 with hT | hT
    · simp [hT]
    rcases eq_or_ne G 0 with hG | hG
    · simp [hG]
    rw [div_div, div_div, div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (S * G * G * T) * hn
  rw [Inter.cycR_mul I hPp N (nm hsP hfP) hgP, Inter.cycR_mul I hPp N hsP hfP,
    Inter.cycR_mul I hPp N (nm htP hgP) hgP, Inter.cycR_mul I hPp N htP hgP,
    Inter.cycR_mul I hPp N hsP hgP, hint, hfg]
  ring

theorem update_eq (hR : RatRStatement) {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) {P : Ideal (MRing ι)} {n : ℕ} (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (j : Fin n)
    (B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hP : IsArithVar P n) (hL : ∀ i, IsSmoothHerm (L i)) (hB : IsSmoothHerm B)
    (hLB : IsIsometricOn P (L j) B) : I P n L = I P n (Function.update L j B) := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) j.2))
  have hL' : ∀ i, IsSmoothHerm (Function.update L j B i) := fun i => by
    by_cases hi : i = j
    · subst hi; simpa using hB
    · simpa [Function.update_of_ne hi] using hL i
  let σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap j (Fin.last m)
  let N : Fin m → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun i => L (σ i.castSucc)
  have hne : ∀ i : Fin m, σ i.castSucc ≠ j := fun i h => by
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
    exact Fin.castSucc_ne_last i h
  have e1 : L ∘ σ = Fin.snoc N (L j) := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [σ]
    · simp [N]
  have e2 : Function.update L j B ∘ σ = Fin.snoc N B := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [σ]
    · simp [N, Function.update_of_ne (hne i)]
  rw [← hI.1 P _ L σ hP hL, ← hI.1 P _ _ σ hP hL', e1, e2]
  exact snoc_eq hR hI N (L j) B hP (fun i => hL _) (hL j) hB hLB

end IsomInvariance

theorem IsomInvariance.proof (hR : Inter.RatR.Statement) : IsomInvariance.Statement := by
  classical
  intro K _ ι _ I hI P n L L' hP hL hL' hiso
  let M : Finset (Fin n) → Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun S j => if j ∈ S then L' j else L j
  have hM : ∀ S j, IsSmoothHerm (M S j) := fun S j => by
    by_cases h : j ∈ S
    · simpa [M, h] using hL' j
    · simpa [M, h] using hL j
  have key : ∀ S : Finset (Fin n), I P n L = I P n (M S) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [M]
    | insert a S ha ih =>
      have e : M (insert a S) = Function.update (M S) a (L' a) := by
        funext j
        by_cases hj : j = a
        · subst hj; simp [M]
        · simp [M, hj]
      have hMa : M S a = L a := by simp [M, ha]
      rw [ih, e]
      exact IsomInvariance.update_eq hR hI (M S) a (L' a) hP (hM S) (hL' a) (hMa ▸ hiso a)
  have hU : M Finset.univ = L' := by funext j; simp [M]
  rw [key Finset.univ, hU]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKleimanNefF
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace KleimanNefF

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiProjPrime_dvr [DecidableEq K] {V : Ideal (MRingOver F ι)} (hV : IsMultiProjPrime V) :
    NumbersDVR.IsMultiProjPrime (R := F) (ι := ι) V :=
  ⟨hV.1, (NumbersDVR.VocabMultiHomogIdeal.proof NumbersDVR.VocabMultiHomog.proof F K ι V).1 hV.2.1, hV.2.2⟩

theorem isProjVarF_of_mem_support [DecidableEq K] {V : Ideal (MRingOver F ι)} {n : ℕ}
    (hV : IsProjVarF V (n + 1)) {f g : MRingOver F ι} {bf bg : K → ℕ}
    (hf : NumbersDVR.IsMultiHomog f bf) (hg : NumbersDVR.IsMultiHomog g bg) (hfV : f ∉ V) (hgV : g ∉ V)
    {W : Ideal (MRingOver F ι)} (hW : W ∈ (ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv V f g).support) :
    IsProjVarF W n := by
  have hVd := isMultiProjPrime_dvr hV.1
  have hrel : FieldNumbers.relDim V = ((n + 1 : ℕ) : WithBot (WithTop ℤ)) :=
    (FieldNumbers.CutRegular.relDim_eq_natCast_iff V (n + 1)).2 hV.2
  have key : ∀ (s : MRingOver F ι) (b : K → ℕ), NumbersDVR.IsMultiHomog s b → s ∉ V →
      ReciprocityTheory.ChartRestriction.G.Geo.divCycle V s W ≠ 0 → IsProjVarF W n := by
    intro s b hs hsV hne
    have hne' : NumbersDVR.divCycle V s W ≠ 0 := by
      rw [← NumbersDVR.VocabDivCycle.proof F K ι V s W]
      exact_mod_cast hne
    obtain ⟨hW1, hW2⟩ := FieldNumbers.DivCycleSupport.full F K ι V hVd n hrel b s hs hsV W hne'
    exact ⟨⟨hW1.isPrime, (NumbersDVR.VocabMultiHomogIdeal.proof NumbersDVR.VocabMultiHomog.proof F K ι W).2
      hW1.multiHomog, hW1.relevant⟩, (FieldNumbers.CutRegular.relDim_eq_natCast_iff W n).1 hW2⟩
  rw [Finsupp.mem_support_iff, ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv, Finsupp.sub_apply, Finsupp.mapRange_apply,
    Finsupp.mapRange_apply] at hW
  by_cases hfW : ReciprocityTheory.ChartRestriction.G.Geo.divCycle V f W = 0
  · refine key g bg hg hgV fun h => hW ?_
    rw [hfW, h]
    simp
  · exact key f bf hf hfV hfW

theorem eq_intNum [DecidableEq K] {I : IFamily F ι} (hI : IsFieldIntersection I) :
    ∀ (n : ℕ) (V : Ideal (MRingOver F ι)) (L : Fin n → K → ℤ), IsProjVarF V n →
      I V n L = NumbersDVR.intNum F V L := by
  have hJ : IsFieldIntersection (F := F) (ι := ι) (fun V _ L => NumbersDVR.intNum F V L) :=
    NumbersDVR.IntNumIsFieldIntersection.full F K ι
  intro n
  induction n with
  | zero =>
    intro V L hV
    choose i hi using hV.1.2.2
    exact (hI.1 V L i hV hi).trans (hJ.1 V L i hV hi).symm
  | succ n ih =>
    intro V L hV
    obtain ⟨bf, bg, f, g, hf, hg, hfV, hgV, hb⟩ :=
      FieldNumbers.ExistsForm.full F K ι V (isMultiProjPrime_dvr hV.1) (L (Fin.last n))
    have hs : IsRatSection V (L (Fin.last n)) f g :=
      ⟨bf, bg, (NumbersDVR.VocabMultiHomog.proof F K ι f bf).2 hf,
        (NumbersDVR.VocabMultiHomog.proof F K ι g bg).2 hg, hfV, hgV, fun k => congrFun hb k⟩
    have e1 : I V (n + 1) L = ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval (fun W => I W n (Fin.init L))
        (ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv V f g) := by
      have h := hI.2 V n (Fin.init L) (L (Fin.last n)) f g hV hs
      rwa [Fin.snoc_init_self] at h
    have e2 : NumbersDVR.intNum F V L = ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval
        (fun W => NumbersDVR.intNum F W (Fin.init L)) (ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv V f g) := by
      have h := hJ.2 V n (Fin.init L) (L (Fin.last n)) f g hV hs
      rwa [Fin.snoc_init_self] at h
    rw [e1, e2, ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval, ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval]
    refine Finsupp.sum_congr fun W hW => ?_
    rw [ih W _ (isProjVarF_of_mem_support hV hf hg hfV hgV hW)]

theorem map_update_add₂ {I : IFamily F ι} (hI : IsFieldIntersection I) {V : Ideal (MRingOver F ι)} {n : ℕ}
    (hV : IsProjVarF V n) (L : Fin n → K → ℤ) (j : Fin n) (x y : K → ℤ) :
    I V n (Function.update L j (x + y)) = I V n (Function.update L j x) + I V n (Function.update L j y) := by
  classical
  rw [eq_intNum hI n V _ hV, eq_intNum hI n V _ hV, eq_intNum hI n V _ hV]
  have hVd := isMultiProjPrime_dvr hV.1
  exact FieldNumbers.IntNumAdd.full F K ι V hVd.multiHomog hVd.relevant n
    ((FieldNumbers.CutRegular.relDim_eq_natCast_iff V n).2 hV.2) L j x y

theorem nsmul_position {I : IFamily F ι} (hI : IsFieldIntersection I) {V : Ideal (MRingOver F ι)} {n : ℕ}
    (hV : IsProjVarF V n) (L : Fin n → K → ℤ) (j : Fin n) (m : ℕ) (x : K → ℤ) :
    I V n (Function.update L j ((m : ℤ) • x)) = m * I V n (Function.update L j x) := by
  induction m with
  | zero =>
    have h := map_update_add₂ hI hV L j 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, zero_smul, zero_mul]
    linarith
  | succ m ih =>
    rw [Nat.cast_succ, add_smul, one_smul, map_update_add₂ hI hV, ih]
    ring

end KleimanNefF

theorem KleimanNefF.proof (hKA : KH.KAmpStatement) (hGP : GeneratedProductNonneg.Statement) :
    KH.KleimanNefFStatement := by
  classical
  intro F _ K _ ι _ I V n a hI hV hnef
  let _ : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  let H : K → ℤ := fun _ => ((1 : ℕ) : ℤ)
  let c : Finset (Fin n) → ℤ := fun S => I V n (fun i => if i ∈ S then H else a i)
  have key : ∀ q : ℕ, 1 ≤ q → 0 ≤ ∑ S : Finset (Fin n), (q : ℤ) ^ Sᶜ.card * c S := by
    intro q hq
    have hamp := fun j => hKA F K ι I V n (a j) q 1 hI hV (hnef j) hq le_rfl
    choose p hp hgen _ using hamp
    let B : Fin n → K → ℤ := fun j => p j • (q • a j + H)
    have hB : 0 ≤ I V n B := hGP F K ι I V n B hI hV hgen
    have hposition : ∀ (L : Fin n → K → ℤ) (i : Fin n), I V n (Function.update L i (B i)) =
        ((q : ℤ) * p i) * I V n (Function.update L i (a i)) + (p i : ℤ) * I V n (Function.update L i H) := by
      intro L i
      have e : B i = ((q * p i : ℕ) : ℤ) • a i + ((p i : ℕ) : ℤ) • H := by
        funext k
        simp only [B, Pi.add_apply, Pi.smul_apply]
        simp only [H, nsmul_eq_mul, smul_eq_mul]
        push_cast
        ring
      rw [e, KleimanNefF.map_update_add₂ hI hV, KleimanNefF.nsmul_position hI hV, KleimanNefF.nsmul_position hI hV]
      push_cast
      ring
    have hexp := Kleiman.sum_expand_positions (I V n) B a (fun _ => H) (fun i => (q : ℤ) * p i)
      (fun i => (p i : ℤ)) hposition
    have hw : ∀ S : Finset (Fin n), (∏ i ∈ S, (p i : ℤ)) * (∏ i ∈ Sᶜ, ((q : ℤ) * p i)) =
        (∏ i, (p i : ℤ)) * (q : ℤ) ^ Sᶜ.card := by
      intro S
      rw [Finset.prod_mul_distrib, Finset.prod_const, ← mul_assoc, mul_comm _ ((q : ℤ) ^ _), mul_assoc,
        Finset.prod_mul_prod_compl, mul_comm]
    simp only [hw, mul_assoc] at hexp
    rw [← Finset.mul_sum] at hexp
    have hprod : 0 < ∏ i, (p i : ℤ) := Finset.prod_pos fun i _ => by exact_mod_cast hp i
    rw [hexp] at hB
    exact (mul_nonneg_iff_of_pos_left hprod).mp hB
  have h0 := Kleiman.nonneg_of_poly c key
  simpa [c] using h0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedEffectiveSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GeneratedEffectiveSection.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver F ι)) (a : K → ℤ),
    IsMultiProjPrime V → KH.GeneratedV F V a →
    ∃ f g : MRingOver F ι, IsRatSection V a f g ∧ ∀ W, 0 ≤ ratDiv V f g W

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

