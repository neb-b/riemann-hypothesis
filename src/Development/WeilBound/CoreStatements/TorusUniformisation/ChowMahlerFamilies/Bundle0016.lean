module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0015

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FiniteNonvanishingSelection
section
open MvPolynomial

theorem PositivityTheory.Xgn.finite_nonvanishing_selection : ∀ (σ : Type) [Finite σ] (F : Set (MvPolynomial σ ℤ)), ∃ T : Finset (MvPolynomial σ ℤ), (T : Set (MvPolynomial σ ℤ)) ⊆ F ∧ ∀ z : σ → ℂ, (∃ s ∈ F, eval z (MvPolynomial.map (Int.castRingHom ℂ) s) ≠ 0) → ∃ s ∈ T, eval z (MvPolynomial.map (Int.castRingHom ℂ) s) ≠ 0 := by
  intro σ _ F
  have hfg : (Submodule.span (MvPolynomial σ ℤ) F).FG := IsNoetherian.noetherian _
  obtain ⟨T, hTF, hT⟩ := (Submodule.fg_span_iff_fg_span_finset_subset F).1 hfg
  refine ⟨T, hTF, fun z hz => ?_⟩
  obtain ⟨s, hsF, hs⟩ := hz
  by_contra hall
  push_neg at hall
  let φ : MvPolynomial σ ℤ →+* ℂ := (eval z).comp (MvPolynomial.map (Int.castRingHom ℂ))
  have hle : Ideal.span (T : Set (MvPolynomial σ ℤ)) ≤ RingHom.ker φ := by
    rw [Ideal.span_le]
    intro t ht
    exact RingHom.mem_ker.2 (hall t ht)
  have hsT : s ∈ Submodule.span (MvPolynomial σ ℤ) (T : Set (MvPolynomial σ ℤ)) := by
    rw [← hT]
    exact Submodule.subset_span hsF
  exact hs (RingHom.mem_ker.1 (hle hsT))
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.HomogeneousPairComponent
section
open MvPolynomial

namespace PositivityTheory.Xgn.HomogeneousComponentProduct

theorem comp_mul {σ M R : Type*} [CommRing R] [AddCancelCommMonoid M] (w : σ → M)
    (g : MvPolynomial σ R) (bg : M) (hg : IsWeightedHomogeneous w g bg) (b : M)
    (s : MvPolynomial σ R) :
    weightedHomogeneousComponent w (b + bg) (s * g) = weightedHomogeneousComponent w b s * g := by
  conv_lhs => rw [s.as_sum, Finset.sum_mul]
  conv_rhs => rw [s.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  have hm : IsWeightedHomogeneous w (monomial d (AddMonoidAlgebra.coeff s d)) (Finsupp.weight w d) :=
    isWeightedHomogeneous_monomial _ _ _ rfl
  by_cases h : Finsupp.weight w d = b
  · subst h
    rw [(hm.mul hg).weightedHomogeneousComponent_same, hm.weightedHomogeneousComponent_same]
  · rw [(hm.mul hg).weightedHomogeneousComponent_ne _ (fun h' => h (add_right_cancel h').symm),
      hm.weightedHomogeneousComponent_ne _ (Ne.symm h), zero_mul]

theorem comp_mul_zero {σ M R : Type*} [CommRing R] [AddCommMonoid M] (w : σ → M)
    (g : MvPolynomial σ R) (bg : M) (hg : IsWeightedHomogeneous w g bg) (c : M)
    (hc : ∀ b, c ≠ b + bg) (s : MvPolynomial σ R) :
    weightedHomogeneousComponent w c (s * g) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [s.as_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_eq_zero (fun d _ => ?_)
  exact ((isWeightedHomogeneous_monomial _ _ _ rfl).mul hg).weightedHomogeneousComponent_ne _ (hc _)

end PositivityTheory.Xgn.HomogeneousComponentProduct

theorem PositivityTheory.Xgn.homogeneous_pair_component : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)), P.IsPrime → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P → ∀ (f g u₀ v₀ : MvPolynomial (Σ k, ι k) ℤ) (bf bg a : K → ℕ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f bf → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog g bg → f ∉ P → u₀ * f - v₀ * g ∈ P → weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a u₀ ∉ P → ∃ (b : K → ℕ) (v : MvPolynomial (Σ k, ι k) ℤ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg ∧ (weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a u₀) * f - v * g ∈ P := by
  intro K _ _ ι _ P hP hH f g u₀ v₀ bf bg a hf hg hfP hrel hu
  have h := hH _ hrel (a + bf)
  rw [map_sub, PositivityTheory.Xgn.HomogeneousComponentProduct.comp_mul _ f bf hf] at h
  by_cases hb : ∃ b, a + bf = b + bg
  · obtain ⟨b, hb⟩ := hb
    rw [hb, PositivityTheory.Xgn.HomogeneousComponentProduct.comp_mul _ g bg hg] at h
    exact ⟨b, _, weightedHomogeneousComponent_isWeightedHomogeneous b v₀, hb, h⟩
  · rw [PositivityTheory.Xgn.HomogeneousComponentProduct.comp_mul_zero _ g bg hg _
      (fun b hb' => hb ⟨b, hb'⟩), sub_zero] at h
    rcases hP.mem_or_mem h with h | h
    · exact absurd h hu
    · exact absurd h hfP
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.MultihomogeneousEvalScale
section
open MvPolynomial

theorem PositivityTheory.Xgn.multihomogeneous_eval_scale : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (s : MvPolynomial (Σ k, ι k) ℤ) (a : K → ℕ) (c : K → ℂ) (z : ((Σ k, ι k) → ℂ)), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog s a → eval (fun p => c p.1 * z p) (MvPolynomial.map (Int.castRingHom ℂ) s) = (∏ k, c k ^ a k) * eval z (MvPolynomial.map (Int.castRingHom ℂ) s) := by
  intro K _ _ ι _ s a c z hs
  rw [eval_map, eval_map, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw : Finsupp.weight (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) m = a :=
    hs (mem_support_iff.mp hm)
  have ha : ∀ k, a k = ∑ i : ι k, m ⟨k, i⟩ := by
    intro k
    rw [← hw, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
      Fintype.sum_sigma, Finset.sum_eq_single k]
    · simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight]
    · intro j _ hj
      simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight, Pi.single_apply, hj, hj.symm]
    · simp
  have h1 : ∏ p : (Σ k, ι k), c p.1 ^ m p = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [ha k, ← Finset.prod_pow_eq_pow_sum]
  simp only [mul_pow]
  rw [Finset.prod_mul_distrib, h1]
  ring
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.MultihomogeneousNonvanishingOff
section
open MvPolynomial

namespace PositivityTheory.Xgn.MultihomogeneousNonvanishing

open GroundTheory.Heights₂.Heights.NumbersDVR

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

theorem exists_component_ne (z : (Σ k, ι k) → ℂ) (q : MvPolynomial (Σ k, ι k) ℤ)
    (hq : eval z (MvPolynomial.map (Int.castRingHom ℂ) q) ≠ 0) :
    ∃ a : K → ℕ, eval z (MvPolynomial.map (Int.castRingHom ℂ)
      (weightedHomogeneousComponent (blockWeight ι) a q)) ≠ 0 := by
  by_contra h
  push_neg at h
  apply hq
  have hfin := weightedHomogeneousComponent_finsupp (w := blockWeight ι) q
  rw [← sum_weightedHomogeneousComponent (blockWeight ι) q]
  have key := map_finsum ((eval z).comp (MvPolynomial.map (Int.castRingHom ℂ))) hfin
  simp only [RingHom.coe_comp, Function.comp_apply] at key
  rw [key]
  simp [h]

theorem exists_form_ne (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (d : K → ℕ) :
    ∃ m : MvPolynomial (Σ k, ι k) ℤ, IsWeightedHomogeneous (blockWeight ι) m d ∧
      eval z (MvPolynomial.map (Int.castRingHom ℂ) m) ≠ 0 := by
  choose i hi using hz
  refine ⟨∏ k, X ⟨k, i k⟩ ^ d k, ?_, ?_⟩
  · have h := IsWeightedHomogeneous.prod Finset.univ
      (fun k => (X ⟨k, i k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ d k)
      (fun k => d k • blockWeight ι ⟨k, i k⟩)
      (fun k _ => (isWeightedHomogeneous_X ℤ (blockWeight ι) ⟨k, i k⟩).pow (d k))
    convert h using 1
    conv_lhs => rw [← Finset.univ_sum_single d]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ext j
    simp [blockWeight, Pi.single_apply]
  · simp [Finset.prod_ne_zero_iff, hi]

end PositivityTheory.Xgn.MultihomogeneousNonvanishing

theorem PositivityTheory.Xgn.multihomogeneous_nonvanishing_off : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (bf bg : K → ℕ) (z : ((Σ k, ι k) → ℂ)) (q : MvPolynomial (Σ k, ι k) ℤ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → q ∈ P → eval z (MvPolynomial.map (Int.castRingHom ℂ) q) ≠ 0 → ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog u a ∧ GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg ∧ u ∈ P ∧ v ∈ P ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0 ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) v) ≠ 0 := by
  intro K _ _ ι _ P bf bg z q hP hz hqP hq
  obtain ⟨a, ha⟩ := PositivityTheory.Xgn.MultihomogeneousNonvanishing.exists_component_ne z q hq
  obtain ⟨m1, hm1, hm1z⟩ := PositivityTheory.Xgn.MultihomogeneousNonvanishing.exists_form_ne z hz bg
  obtain ⟨m2, hm2, hm2z⟩ := PositivityTheory.Xgn.MultihomogeneousNonvanishing.exists_form_ne z hz bf
  have hcP : weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a q ∈ P :=
    hP q hqP a
  have hch := weightedHomogeneousComponent_isWeightedHomogeneous
    (w := GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a q
  refine ⟨a + bg, a + bf, _ * m1, _ * m2, hch.mul hm1, hch.mul hm2, by abel,
    P.mul_mem_right _ hcP, P.mul_mem_right _ hcP, ?_, ?_⟩
  · simpa using mul_ne_zero ha hm1z
  · simpa using mul_ne_zero ha hm2z
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.PolynomialEvalComplexConjugate
section
open MvPolynomial

theorem PositivityTheory.Xgn.polynomial_eval_complex_conjugate : ∀ (σ : Type) (s : MvPolynomial σ ℤ) (z : σ → ℂ), eval (fun p => (starRingEnd ℂ) (z p)) (MvPolynomial.map (Int.castRingHom ℂ) s) = (starRingEnd ℂ) (eval z (MvPolynomial.map (Int.castRingHom ℂ) s)) := by
  intro σ s z
  rw [MvPolynomial.eval_map, MvPolynomial.eval_map, MvPolynomial.eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.PolynomialNormSquareSmooth
section
open MvPolynomial

namespace PositivityTheory.Xgn.SmoothPolynomialNormSquare

theorem contDiff_eval (σ : Type) [Fintype σ] (p : MvPolynomial σ ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : σ → ℂ => MvPolynomial.eval z p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval_C]
    exact contDiff_const
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul (contDiff_apply ℝ (fun _ => ℂ) i)

end PositivityTheory.Xgn.SmoothPolynomialNormSquare

theorem PositivityTheory.Xgn.polynomial_norm_square_smooth : ∀ (σ : Type) [Fintype σ] (s : MvPolynomial σ ℤ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : σ → ℂ => ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) s)‖ ^ 2) := by
  intro σ _ s
  exact (PositivityTheory.Xgn.SmoothPolynomialNormSquare.contDiff_eval σ _).norm_sq ℝ
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.RelevantPrimeOrbitClosure
section
open MvPolynomial

namespace PositivityTheory.Xgn.MultihomogeneousOrbit

open GroundTheory.Heights₂.Heights.NumbersDVR

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

noncomputable def orb (z : (Σ k, ι k) → ℂ) : MvPolynomial (Σ k, ι k) ℤ →+* MvPolynomial K ℂ :=
  eval₂Hom (Int.castRingHom _) (fun v => C (z v) * X v.1)

lemma prod_weight (d : (Σ k, ι k) →₀ ℕ) :
    (d.prod fun v n => (X v.1 : MvPolynomial K ℂ) ^ n) =
      ∏ k, (X k : MvPolynomial K ℂ) ^ (Finsupp.weight (blockWeight ι) d k) := by
  refine Finsupp.induction d ?_ ?_
  · simp
  · intro v b f _ _ ih
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    have h1 : ((Finsupp.single v b).prod fun x n => (X x.1 : MvPolynomial K ℂ) ^ n) = X v.1 ^ b :=
      Finsupp.prod_single_index (pow_zero _)
    rw [h1, ih, map_add (f := _)]
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    congr 1
    simp [blockWeight, Pi.single_apply, Finsupp.weight_apply]

lemma orb_homog (z : (Σ k, ι k) → ℂ) (a : K → ℕ) (s : MvPolynomial (Σ k, ι k) ℤ)
    (hs : s.IsWeightedHomogeneous (blockWeight ι) a) :
    orb z s = C (eval z (MvPolynomial.map (Int.castRingHom ℂ) s)) *
      ∏ k, (X k : MvPolynomial K ℂ) ^ a k := by
  conv_lhs => rw [s.as_sum]
  conv_rhs => rw [s.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hw : Finsupp.weight (blockWeight ι) d = a := hs (mem_support_iff.mp hd)
  simp only [orb, coe_eval₂Hom, eval₂_monomial, map_monomial, eval_monomial, mul_pow,
    Finsupp.prod_mul]
  rw [prod_weight, hw]
  simp [map_finsuppProd, mul_assoc]

lemma orb_eq_zero (z : (Σ k, ι k) → ℂ) (s : MvPolynomial (Σ k, ι k) ℤ)
    (h : ∀ a : K → ℕ, eval z (MvPolynomial.map (Int.castRingHom ℂ)
      (weightedHomogeneousComponent (blockWeight ι) a s)) = 0) : orb z s = 0 := by
  rw [← sum_weightedHomogeneousComponent (blockWeight ι) s,
    map_finsum (orb z) (weightedHomogeneousComponent_finsupp s)]
  have h0 : ∀ a, orb z (weightedHomogeneousComponent (blockWeight ι) a s) = 0 := fun a => by
    rw [orb_homog z a _ (weightedHomogeneousComponent_isWeightedHomogeneous a s), h a, map_zero,
      zero_mul]
  simp [h0]

end PositivityTheory.Xgn.MultihomogeneousOrbit

theorem PositivityTheory.Xgn.relevant_prime_orbit_closure : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (z : ((Σ k, ι k) → ℂ)), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P → z ∈ ReciprocityTheory.ChartRestriction.G.Geo.mcPts P → ∃ W : Ideal (MvPolynomial (Σ k, ι k) ℤ), W.IsPrime ∧ P ≤ W ∧ GroundTheory.Heights₂.Heights.NumbersDVR.IsRelevant W ∧ (∀ p : Nat.Primes, (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W) ∧ ∀ s : MvPolynomial (Σ k, ι k) ℤ, s ∉ W → ∃ a : K → ℕ, eval z (MvPolynomial.map (Int.castRingHom ℂ) (weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a s)) ≠ 0 := by
  intro K _ _ ι _ P z hP hz
  obtain ⟨hz1, hz2⟩ := hz
  refine ⟨RingHom.ker (PositivityTheory.Xgn.MultihomogeneousOrbit.orb z), RingHom.ker_isPrime _, ?_, ?_, ?_, ?_⟩
  · intro q hq
    rw [RingHom.mem_ker]
    exact PositivityTheory.Xgn.MultihomogeneousOrbit.orb_eq_zero z q (fun a => hz2 _ (hP q hq a))
  · intro k
    obtain ⟨i, hi⟩ := hz1 k
    refine ⟨i, ?_⟩
    rw [RingHom.mem_ker]
    simp [PositivityTheory.Xgn.MultihomogeneousOrbit.orb, hi, X_ne_zero]
  · intro p
    rw [RingHom.mem_ker]
    simp [PositivityTheory.Xgn.MultihomogeneousOrbit.orb, p.prop.ne_zero]
  · intro s hs
    by_contra hne
    push_neg at hne
    exact hs (RingHom.mem_ker.mpr (PositivityTheory.Xgn.MultihomogeneousOrbit.orb_eq_zero z s hne))
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XVertdivCommensurable
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_vertdiv_commensurable

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] [DecidableEq K]
  {ι : K → Type} [∀ k, Fintype (ι k)]

def Pair (x : (Σ k, ι k) → Ω) (c : K → ℤ) (u : Ω) (f g : MRing ι O) : Prop :=
  (∃ bf bg : K → ℕ, IsMultiHomog f bf ∧ IsMultiHomog g bg ∧ (fun k => (bf k : ℤ) - bg k) = c) ∧
    aeval x f = u * aeval x g

theorem cross {x : (Σ k, ι k) → Ω} {c : K → ℤ} {u : Ω} {f g f' g' : MRing ι O}
    (h : Pair x c u f g) (h' : Pair x c u f' g') : f * g' - f' * g ∈ pointIdeal O x := by
  obtain ⟨⟨bf, bg, hf, hg, hd⟩, hv⟩ := h
  obtain ⟨⟨bf', bg', hf', hg', hd'⟩, hv'⟩ := h'
  have he : bf + bg' = bf' + bg := by
    funext k
    have h1 := congrFun hd k
    have h2 := congrFun hd' k
    simp only [Pi.add_apply] at h1 h2 ⊢
    omega
  have h1 : IsWeightedHomogeneous (blockWeight ι) (f * g') (bf + bg') := IsWeightedHomogeneous.mul hf hg'
  have h2 : IsWeightedHomogeneous (blockWeight ι) (f' * g) (bf + bg') := by
    rw [he]; exact IsWeightedHomogeneous.mul hf' hg
  refine GenericProjClosureDivisor.mem_of_homog (b := bf + bg') ?_ ?_
  · exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp
      (sub_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h1)
        ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h2))
  · rw [map_sub, map_mul, map_mul, hv, hv']
    ring

omit [∀ k, Fintype (ι k)] in
theorem mono_homog (s : ∀ k, ι k) (e : K → ℕ) :
    IsMultiHomog (∏ k, X ⟨k, s k⟩ ^ e k : MRing ι O) e := by
  have he : e = ∑ k, e k • blockWeight ι ⟨k, s k⟩ := by
    ext j
    simp [blockWeight, Pi.single_apply]
  unfold IsMultiHomog
  conv => enter [3]; rw [he]
  exact IsWeightedHomogeneous.prod _ _ _ fun k _ => (isWeightedHomogeneous_X O _ _).pow _

theorem product_powers_not_mem_prime {A : Type} [CommRing A] {W : Ideal A} (hW : W.IsPrime) {c : A} (hc : c ∉ W) (y : K → A)
    (hy : ∀ k, y k ∉ W) (n : ℕ) (e : K → ℕ) : c ^ n * ∏ k, y k ^ e k ∉ W := by
  intro hf
  rcases hW.mem_or_mem hf with h3 | h3
  · exact hc (hW.mem_of_pow_mem n h3)
  · obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (p := W)).1 h3
    exact hy k (hW.mem_of_pow_mem (e k) hk)

theorem zpow_aux (y : K → Ω) (hy : ∀ k, y k ≠ 0) (b b' : K → ℤ) (p q : K → ℕ)
    (h : ∀ k, b k + q k = b' k + p k) :
    (∏ k, y k ^ b k) * ∏ k, y k ^ q k = (∏ k, y k ^ b' k) * ∏ k, y k ^ p k := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hy k), ← zpow_add₀ (hy k), h k]

theorem mul_eq_one_of_covolume_identity {m m' t D P Q r u : Ω} (hm : m' ≠ 0) (h : t * m = r * (u * m')) (hb : m * Q = m' * P) :
    t * (D * P) = u * (r * D * Q) := by
  apply mul_left_cancel₀ hm
  linear_combination D * Q * h - D * t * hb

omit [∀ k, Fintype (ι k)] in
theorem pair_num {x : (Σ k, ι k) → Ω} {ϖ : O} {b b' : K → ℤ} {u : Ω} {s : ∀ k, ι k} (hs : mseg x s ≠ 0)
    {W : Ideal (MRing ι O)} (hW : W.IsPrime) (hϖ : (C ϖ : MRing ι O) ∉ W)
    (hX : ∀ k, (X ⟨k, s k⟩ : MRing ι O) ∉ W) {n : ℕ} {r : Ω} (hr : r ∈ chartRing O (mseg x) s)
    (h : algebraMap O Ω ϖ ^ n * chartMon x s b = r * (u * chartMon x s b')) :
    ∃ f g : MRing ι O, Pair x (b - b') u f g ∧ f ∉ W := by
  obtain ⟨d, F, hF, eF⟩ := A_forms_exist.chartRing_le_fracs x s hs hr
  have hx : ∀ k, x ⟨k, s k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hs k (Finset.mem_univ k)
  have hm : chartMon x s b' ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hx k)
  obtain ⟨p, hp⟩ : ∃ p : K → ℕ, ∀ k, p k = (b k - b' k).toNat := ⟨_, fun _ => rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : K → ℕ, ∀ k, q k = (b' k - b k).toNat := ⟨_, fun _ => rfl⟩
  have hpq : ∀ k, b k + q k = b' k + p k := fun k => by
    have e1 := hp k
    have e2 := hq k
    omega
  have hb : chartMon x s b * ∏ k, x ⟨k, s k⟩ ^ q k = chartMon x s b' * ∏ k, x ⟨k, s k⟩ ^ p k :=
    zpow_aux (fun k => x ⟨k, s k⟩) hx b b' p q hpq
  have h0 : IsMultiHomog (C ϖ ^ n : MRing ι O) 0 := by
    rw [← map_pow]
    exact isWeightedHomogeneous_C _ _
  have h1 : IsMultiHomog (C ϖ ^ n * ∏ k, X ⟨k, s k⟩ ^ (d + p) k : MRing ι O) (0 + (d + p)) :=
    IsWeightedHomogeneous.mul h0 (mono_homog s (d + p))
  have h2 : IsMultiHomog (F * ∏ k, X ⟨k, s k⟩ ^ q k : MRing ι O) (d + q) :=
    IsWeightedHomogeneous.mul hF (mono_homog s q)
  refine ⟨_, _, ⟨⟨_, _, h1, h2, ?_⟩, ?_⟩, product_powers_not_mem_prime hW hϖ (fun k => X ⟨k, s k⟩) hX n (d + p)⟩
  · funext k
    have e1 := hpq k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
    omega
  · simp only [map_mul, map_prod, map_pow, aeval_X, aeval_C, eF, Pi.add_apply, pow_add,
      Finset.prod_mul_distrib]
    exact mul_eq_one_of_covolume_identity hm h hb

theorem pair_at {x : (Σ k, ι k) → Ω} {ϖ : O} {b b' : K → ℤ} {u : Ω} (hu : u ≠ 0)
    (H : ∀ s, mseg x s ≠ 0 → (∃ n : ℕ, ∃ r ∈ chartRing O (mseg x) s, algebraMap O Ω ϖ ^ n * chartMon x s b = r * (u * chartMon x s b')) ∧ ∃ n : ℕ, ∃ r ∈ chartRing O (mseg x) s, algebraMap O Ω ϖ ^ n * (u * chartMon x s b') = r * chartMon x s b)
    (W : Ideal (MRing ι O)) (hW : W.IsPrime) (hPW : pointIdeal O x ≤ W) (hrel : IsRelevant W)
    (hϖ : (C ϖ : MRing ι O) ∉ W) :
    ∃ f g : MRing ι O, Pair x (b - b') u f g ∧ f ∉ W ∧ g ∉ W := by
  choose s hX using hrel
  have hs : mseg x s ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun k _ h0 => hX k (hPW ?_)
    exact GenericProjClosureDivisor.mem_of_homog (isWeightedHomogeneous_X O _ _) (by rw [aeval_X, h0])
  obtain ⟨⟨n, r, hr, h⟩, n', r', hr', h'⟩ := H s hs
  obtain ⟨f, g, hp, hf⟩ := pair_num hs hW hϖ hX hr h
  have h'' : algebraMap O Ω ϖ ^ n' * chartMon x s b' = r' * (u⁻¹ * chartMon x s b) := by
    apply mul_left_cancel₀ hu
    rw [mul_left_comm r', ← mul_assoc u u⁻¹, mul_inv_cancel₀ hu, one_mul, ← h']
    ring
  obtain ⟨g', f', ⟨⟨bg, bf, hg1, hf1, hd⟩, hv⟩, hg'⟩ := pair_num hs hW hϖ hX hr' h''
  have hp' : Pair x (b - b') u f' g' := by
    refine ⟨⟨bf, bg, hf1, hg1, ?_⟩, ?_⟩
    · funext k
      have h1 := congrFun hd k
      simp only [Pi.sub_apply] at h1 ⊢
      omega
    · rw [hv, ← mul_assoc, mul_inv_cancel₀ hu, one_mul]
  refine ⟨f, g, hp, hf, fun hg => ?_⟩
  have h1 := W.add_mem (hPW (cross hp hp')) (W.mul_mem_left f' hg)
  rw [sub_add_cancel] at h1
  exact (hW.mem_or_mem h1).elim hf hg'

end PositivityTheory.Xgn.A_vertdiv_commensurable

theorem PositivityTheory.Xgn.t_vertdiv_commensurable : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d : ℕ, IsModelOver (pointIdeal O x) d → ∀ (b b' : K → ℤ) (u : Ω), u ≠ 0 → (∀ s, mseg x s ≠ 0 → (∃ n : ℕ, ∃ r ∈ chartRing O (mseg x) s, algebraMap O Ω ϖ ^ n * chartMon x s b = r * (u * chartMon x s b')) ∧ ∃ n : ℕ, ∃ r ∈ chartRing O (mseg x) s, algebraMap O Ω ϖ ^ n * (u * chartMon x s b') = r * chartMon x s b) → ∃ f g : MRing ι O, IsVerticalDivisor (pointIdeal O x) ϖ (b - b') f g ∧ aeval x f = u * aeval x g := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x ϖ hϖ d hM b b' u hu H
  have hϖP : (C ϖ : MRing ι O) ∉ pointIdeal O x := by
    intro hm
    have h1 : ϖ ∈ (pointIdeal O x).comap (C : O →+* MRing ι O) := hm
    rw [hM.noTorsion, Ideal.mem_bot] at h1
    exact hϖ.ne_zero h1
  obtain ⟨f, g, hp, hf, hg⟩ := A_vertdiv_commensurable.pair_at hu H _ hM.multiProj.isPrime le_rfl
    hM.multiProj.relevant hϖP
  refine ⟨f, g, IsVerticalDivisor.of_unit_off_special hp.1 hf hg fun W hW hPW hrel hϖW => ?_, hp.2⟩
  obtain ⟨f', g', hp', hf', hg'⟩ := A_vertdiv_commensurable.pair_at hu H W hW hPW hrel hϖW
  refine ⟨g', f', hg', hf', ?_⟩
  rw [mul_comm g' f]
  exact A_vertdiv_commensurable.cross hp hp'
end

