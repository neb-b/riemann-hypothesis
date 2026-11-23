module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingNoeth
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem LocRingNoeth.proof (hF : LocRingFrac.Statement) : LocRingNoeth.Statement := by
  classical
  intro K _ ι _ P W hP hW hPW hrel
  have := hP
  let L := FractionRing (MRing ι ⧸ P)
  let q : MRing ι →+* L := (algebraMap (MRing ι ⧸ P) L).comp (Ideal.Quotient.mk P)
  have hq : ∀ f, f ∉ W → q f ≠ 0 := fun f hf h => hf (hPW (by
    rwa [RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h))
  have hnz : ∀ v, v ∉ W → Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P) := fun v hv =>
    mem_nonZeroDivisors_of_ne_zero fun h => hv (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))

  have hfrac : ∀ u v a, IsMultiHomog u a → IsMultiHomog v a → v ∉ W → q u / q v ∈ locRing P W := by
    intro u v a hu hv hvW
    refine Subring.subset_closure ⟨u, v, a, hnz v hvW, hvW, hu, hv, ?_⟩
    rw [IsFractionRing.mk'_eq_div]
    rfl
  choose c hc using hrel

  let g : (Σ k, ι k) → L := fun p => q (X p) / q (X ⟨p.1, c p.1⟩)
  let B : Subring L := Subring.closure (Set.range g)
  have hBN : IsNoetherianRing B := is_noetherian_subring_closure _ (Set.finite_range g)
  have hBS : B ≤ locRing P W := Subring.closure_le.mpr (by
    rintro _ ⟨p, rfl⟩
    exact hfrac _ _ _ (AvoidRing.isMultiHomog_X p.1 p.2) (AvoidRing.isMultiHomog_X p.1 (c p.1)) (hc p.1))
  let θ : MRing ι →+* L := eval₂Hom (Int.castRingHom L) g
  have hθB : ∀ f, θ f ∈ B := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r => rw [eval₂Hom_C, eq_intCast]; exact intCast_mem _ r
    | add f₁ f₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | mul_X f p hf => rw [map_mul, eval₂Hom_X']; exact mul_mem hf (Subring.subset_closure ⟨p, rfl⟩)

  have hkey : ∀ u a, IsMultiHomog u a → q u = θ u * q (∏ k, X ⟨k, c k⟩ ^ a k) := by
    intro u a hu
    conv_lhs => rw [u.as_sum]
    conv_rhs => rw [u.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.sum_mul, map_prod]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hT : ∏ k, q (X ⟨k, c k⟩ ^ a k) = ∏ p : Σ k, ι k, q (X ⟨p.1, c p.1⟩) ^ m p := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      show q (X ⟨k, c k⟩ ^ a k) = ∏ y, q (X ⟨k, c k⟩) ^ m ⟨k, y⟩
      rw [map_pow, Finset.prod_pow_eq_pow_sum, hu m hm k]
    have hθm : θ (monomial m (AddMonoidAlgebra.coeff u m)) = ((AddMonoidAlgebra.coeff u m : ℤ) : L) * ∏ p, g p ^ m p := by
      rw [show θ _ = eval₂ (Int.castRingHom L) g _ from rfl, eval₂_monomial, eq_intCast,
        Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    have hqm : q (monomial m (AddMonoidAlgebra.coeff u m)) = ((AddMonoidAlgebra.coeff u m : ℤ) : L) * ∏ p, q (X p) ^ m p := by
      rw [monomial_eq, map_mul, map_finsuppProd, Finsupp.prod_fintype _ _ (fun _ => by simp)]
      simp only [map_pow]
      congr 1
      exact eq_intCast (q.comp C) _
    rw [hT, hθm, hqm, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← mul_pow]
    congr 1
    exact (div_mul_cancel₀ _ (hq _ (hc p.1))).symm

  let _ : Algebra B (locRing P W) := (Subring.inclusion hBS).toAlgebra
  let M : Submonoid B := (IsUnit.submonoid (locRing P W)).comap (Subring.inclusion hBS)
  have hLoc : IsLocalization M (locRing P W) := by
    rw [isLocalization_iff]
    refine ⟨fun y => y.2, fun z => ?_, fun {b₁ b₂} h => ⟨1, ?_⟩⟩
    · obtain ⟨u, v, a, hu, hv, hvW, hzv⟩ := hF K ι P W hP hW hPW z z.2
      have hTW := AvoidRing.coordProd_not_mem hW c hc a
      have hu' := hkey u a hu
      have hv' := hkey v a hv
      have hinv := hfrac _ v a (AvoidRing.isMultiHomog_coordProd c a) hv hvW
      have hunit : IsUnit (Subring.inclusion hBS ⟨θ v, hθB v⟩) :=
        IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (by
          show θ v * (q _ / q v) = 1
          rw [mul_div_assoc', ← hv', div_self (hq v hvW)]))
      refine ⟨(⟨θ u, hθB u⟩, ⟨⟨θ v, hθB v⟩, hunit⟩), Subtype.ext ?_⟩
      show (z : L) * θ v = θ u
      apply mul_right_cancel₀ (hq _ hTW)
      rw [mul_assoc, ← hv', ← hu']
      exact hzv
    · rw [Subring.inclusion_injective hBS h]
  exact IsLocalization.isNoetherianRing M (locRing P W) hBN

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingPow
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter.AvoidRing

noncomputable section

namespace LocRingPow

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]


open Classical in
def multiDegWeight (ι : K → Type*) : (Σ k, ι k) → (K → ℕ) := fun p k => if p.1 = k then 1 else 0

theorem weight_multiDegWeight (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (multiDegWeight ι) m = fun k => ∑ i, m ⟨k, i⟩ := by
  classical
  funext k
  rw [← weight_blockWeight k m, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum,
    Finset.sum_apply]
  simp only [Pi.smul_apply, multiDegWeight, blockWeight]

theorem isMultiHomog_iff {f : MRing ι} {a : K → ℕ} :
    IsMultiHomog f a ↔ IsWeightedHomogeneous (multiDegWeight ι) f a := by
  constructor
  · intro h d hd
    rw [weight_multiDegWeight]
    funext k
    exact h d (mem_support_iff.mpr hd) k
  · intro h m hm k
    have := h (mem_support_iff.mp hm)
    rw [weight_multiDegWeight] at this
    exact congrFun this k

theorem component_mem [DecidableEq K] {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) {f : MRing ι}
    (hf : f ∈ J) (D : K → ℕ) : weightedHomogeneousComponent (multiDegWeight ι) D f ∈ J := by
  obtain ⟨g, hg, hgc⟩ := exists_blockComponent (isHomogeneous_of_isMultiHomogIdeal hJ) D Finset.univ hf
  convert hg using 1
  ext m
  rw [coeff_weightedHomogeneousComponent, hgc, weight_multiDegWeight]
  by_cases h : ∀ k, ∑ i, m ⟨k, i⟩ = D k
  · simp [h]
  · simp [h, funext_iff]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem exists_component_not_mem {J : Ideal (MRing ι)} {f : MRing ι} (hf : f ∉ J) :
    ∃ D : K → ℕ, weightedHomogeneousComponent (multiDegWeight ι) D f ∉ J := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hf
  rw [← sum_weightedHomogeneousComponent (w := multiDegWeight ι) (φ := f),
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
  exact Ideal.sum_mem _ fun D _ => h D

attribute [local instance] MvPolynomial.weightedGradedAlgebra


omit [∀ k, Fintype (ι k)] in
theorem component_mul_right [DecidableEq K] {f g : MRing ι} {i j : K → ℕ}
    (hg : IsWeightedHomogeneous (multiDegWeight ι) g j) :
    weightedHomogeneousComponent (multiDegWeight ι) (i + j) (f * g) =
      weightedHomogeneousComponent (multiDegWeight ι) i f * g := by
  rw [← weightedDecomposition.decompose'_apply, ← weightedDecomposition.decompose'_apply]
  exact DirectSum.coe_decompose_mul_add_of_right_mem (weightedHomogeneousSubmodule ℤ (multiDegWeight ι))
    ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hg)


omit [∀ k, Fintype (ι k)] in
theorem component_mul_of_not_le [DecidableEq K] {f g : MRing ι} {j n : K → ℕ}
    (hg : IsWeightedHomogeneous (multiDegWeight ι) g j) (h : ¬ j ≤ n) :
    weightedHomogeneousComponent (multiDegWeight ι) n (f * g) = 0 := by
  rw [← weightedDecomposition.decompose'_apply]
  exact DirectSum.coe_decompose_mul_of_right_mem_of_not_le (weightedHomogeneousSubmodule ℤ (multiDegWeight ι))
    ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hg) h

end LocRingPow


open LocRingPow in
theorem LocRingPow.proof : LocRingPow.Statement := by
  classical
  intro K _ ι _ P s t a W x u v b y hPp hPh hs hsP hW ht htW hx hu hv huW hvW hy
  have := hPp
  obtain ⟨hWmin, -⟩ := hW
  have hWp : W.IsPrime := hWmin.1.1
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2

  obtain ⟨n, d, hdW, hd⟩ : ∃ n : ℕ, ∃ d ∉ W, d * u ^ n ∈ P ⊔ Ideal.span {s} := by
    have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (Localization.AtPrime W) W _ hWmin
    have hu' : algebraMap (MRing ι) (Localization.AtPrime W) u ∈
        ((P ⊔ Ideal.span {s}).map (algebraMap _ (Localization.AtPrime W))).radical :=
      hrad ▸ Ideal.mem_map_of_mem _ huW
    obtain ⟨n, hn⟩ := hu'
    rw [← map_pow, IsLocalization.mem_map_algebraMap_iff W.primeCompl] at hn
    obtain ⟨⟨⟨i, hi⟩, ⟨c, hc⟩⟩, he⟩ := hn
    rw [← map_mul, IsLocalization.eq_iff_exists W.primeCompl] at he
    obtain ⟨⟨e, he'⟩, hee⟩ := he
    refine ⟨n, e * c, W.primeCompl.mul_mem he' hc, ?_⟩
    have : e * c * u ^ n = e * (u ^ n * c) := by ring
    rw [this, hee]
    exact Ideal.mul_mem_left _ _ hi

  obtain ⟨e, he⟩ := exists_component_not_mem hdW
  set ce := weightedHomogeneousComponent (multiDegWeight ι) e d with hce_def
  have hce : IsMultiHomog ce e :=
    isMultiHomog_iff.mpr (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hd
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hq

  set D : K → ℕ := e + n • b with hD
  have h1 : weightedHomogeneousComponent (multiDegWeight ι) D (d * u ^ n) = ce * u ^ n :=
    component_mul_right (isMultiHomog_iff.mp (isMultiHomog_pow hu n))
  obtain ⟨G, hG, hGs⟩ : ∃ G : MRing ι, IsMultiHomog (G * t) D ∧
      weightedHomogeneousComponent (multiDegWeight ι) D (g * s) = G * s := by
    by_cases hle : a ≤ D
    · refine ⟨weightedHomogeneousComponent (multiDegWeight ι) (D - a) g, ?_, ?_⟩
      · have := isMultiHomog_mul
          (isMultiHomog_iff.mpr (weightedHomogeneousComponent_isWeightedHomogeneous (D - a) g)) ht
        rwa [tsub_add_cancel_of_le hle] at this
      · conv_lhs => rw [← tsub_add_cancel_of_le hle]
        exact component_mul_right (isMultiHomog_iff.mp hs)
    · exact ⟨0, fun m hm => by simp at hm,
        by rw [zero_mul]; exact component_mul_of_not_le (isMultiHomog_iff.mp hs) hle⟩
  have hrel : ce * u ^ n - G * s ∈ P := by
    have := component_mem hPh hp D
    rwa [← add_sub_cancel_right p (g * s), hpq, map_sub, h1, hGs] at this

  have hden : ce * v ^ n ∉ W := fun h =>
    (hWp.mem_or_mem h).elim he fun h => hvW (hWp.mem_of_pow_mem _ h)
  have hdenP : Ideal.Quotient.mk P (ce * v ^ n) ∈ nonZeroDivisors (MRing ι ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero fun h => hden (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))
  refine ⟨n, IsLocalization.mk' (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (G * t)) ⟨_, hdenP⟩,
    Subring.subset_closure ⟨G * t, ce * v ^ n, D, hdenP, hden, hG, isMultiHomog_mul hce (isMultiHomog_pow hv n), rfl⟩,
    ?_⟩
  have hne : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (ce * v ^ n)) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hdenP
  apply mul_right_cancel₀ hne
  rw [mul_assoc x, IsLocalization.mk'_spec]
  have key := congrArg (algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P))) (Ideal.Quotient.eq.mpr hrel)
  simp only [map_mul, map_pow] at key hx hy ⊢
  calc y ^ n * (algebraMap _ _ (Ideal.Quotient.mk P ce) * algebraMap _ _ (Ideal.Quotient.mk P v) ^ n)
      = algebraMap _ _ (Ideal.Quotient.mk P ce) * (y * algebraMap _ _ (Ideal.Quotient.mk P v)) ^ n := by ring
    _ = algebraMap _ _ (Ideal.Quotient.mk P ce) * algebraMap _ _ (Ideal.Quotient.mk P u) ^ n := by rw [hy]
    _ = algebraMap _ _ (Ideal.Quotient.mk P G) * algebraMap _ _ (Ideal.Quotient.mk P s) := key
    _ = x * (algebraMap _ _ (Ideal.Quotient.mk P G) * algebraMap _ _ (Ideal.Quotient.mk P t)) := by
        rw [← hx]; ring

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PProjBundleFibre
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section LinSubst

variable {Φ : Type} [Field Φ] {σ : Type} [Fintype σ] {n : ℕ}

def linSubst (ℓ : σ → Fin n → Φ) : MvPolynomial σ Φ →ₐ[Φ] MvPolynomial (Fin n) Φ :=
  aeval fun q => ∑ a, C (ℓ q a) * X a

def linKerForms (ℓ : σ → Fin n → Φ) : Set (MvPolynomial σ Φ) :=
  {f | ∃ μ : σ → Φ, (∀ b, ∑ q, μ q * ℓ q b = 0) ∧ f = ∑ q, C (μ q) * X q}

theorem sum_C_mul_linForm {τ ρ : Type} [Fintype τ] [Fintype ρ] (c : ρ → Φ) (ν : ρ → τ → Φ) :
    ∑ a, C (c a) * ∑ q, C (ν a q) * (X q : MvPolynomial τ Φ) = ∑ q, C (∑ a, c a * ν a q) * X q := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, mul_assoc]

theorem linSubst_linForm (ℓ : σ → Fin n → Φ) (μ : σ → Φ) :
    linSubst ℓ (∑ q, C (μ q) * X q) = ∑ b, C (∑ q, μ q * ℓ q b) * X b := by
  rw [← sum_C_mul_linForm μ ℓ]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [linSubst, map_sum, map_mul, aeval_C, aeval_X, MvPolynomial.algebraMap_eq]

theorem ker_linSubst (ℓ : σ → Fin n → Φ) (ν : Fin n → σ → Φ)
    (hν : ∀ a b, ∑ q, ν a q * ℓ q b = if a = b then 1 else 0) :
    RingHom.ker (linSubst ℓ) = Ideal.span (linKerForms ℓ) := by
  classical
  refine le_antisymm (fun f hf => ?_) ?_
  · set I := Ideal.span (linKerForms ℓ)
    let ρ : MvPolynomial (Fin n) Φ →ₐ[Φ] MvPolynomial σ Φ ⧸ I :=
      aeval fun a => Ideal.Quotient.mk I (∑ q, C (ν a q) * X q)
    have hρ : ρ.comp (linSubst ℓ) = Ideal.Quotient.mkₐ Φ I := by
      refine MvPolynomial.algHom_ext fun q => ?_
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
      have h1 : ρ (linSubst ℓ (X q)) =
          Ideal.Quotient.mk I (∑ q', C (∑ a, ℓ q a * ν a q') * X q') := by
        rw [← sum_C_mul_linForm]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [ρ, linSubst, aeval_X, map_sum, map_mul, aeval_C]
        rfl
      rw [h1, Ideal.Quotient.eq]
      refine Ideal.subset_span ⟨fun q' => ∑ a, ℓ q a * ν a q' - if q' = q then 1 else 0, fun b => ?_, ?_⟩
      · simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, mul_assoc]
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum, hν, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
        simp
      · simp [sub_mul, Finset.sum_sub_distrib, apply_ite C, ite_mul]
    have h2 := congrArg (fun φ => φ f) hρ
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h2
    rw [RingHom.mem_ker] at hf
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← h2]
    erw [hf]
    exact map_zero ρ
  · rw [Ideal.span_le]
    rintro f ⟨μ, hμ, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    erw [linSubst_linForm]
    simp [hμ]

end LinSubst

section Main

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]




end Main

section Fibre

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]




end Fibre

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAddFirst
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

theorem PtsAddFirst.cxHessian_add {D : ℕ} {a b ψ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (ha : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 a y') (hb : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 b y')
    (hψ : ψ =ᶠ[𝓝 y] fun y' => a y' + b y') :
    cxHessian ψ y = cxHessian a y + cxHessian b y := by
  have h1 : fderiv ℝ ψ =ᶠ[𝓝 y] fun y' => fderiv ℝ a y' + fderiv ℝ b y' := by
    filter_upwards [hψ.fderiv (𝕜 := ℝ), ha, hb] with y' h1 h2 h3
    rw [h1]
    exact ((h2.differentiableAt (by norm_num)).hasFDerivAt.add
      (h3.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have da2 : DifferentiableAt ℝ (fderiv ℝ a) y :=
    (ha.self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have db2 : DifferentiableAt ℝ (fderiv ℝ b) y :=
    (hb.self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hH : fderiv ℝ (fderiv ℝ ψ) y = fderiv ℝ (fderiv ℝ a) y + fderiv ℝ (fderiv ℝ b) y := by
    rw [h1.fderiv_eq]
    exact (da2.hasFDerivAt.add db2.hasFDerivAt).fderiv
  ext i j
  simp only [cxHessian, hH, Matrix.add_apply, add_apply]
  push_cast
  ring

theorem PtsAddFirst.mixedDisc_cons_add {D : ℕ} (A B : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ)
    (C : Fin D → Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ) :
    mixedDisc (Fin.cons (A + B) C : Fin (D + 1) → _) =
      mixedDisc (Fin.cons A C : Fin (D + 1) → _) + mixedDisc (Fin.cons B C : Fin (D + 1) → _) := by
  have h := ReciprocityTheory.AnForm.A.mdisc_update_add (Fin.cons A C : Fin (D + 1) → _) 0 A B
  simp only [Fin.update_cons_zero] at h
  exact h

theorem PtsAddFirst.maDensity_cons_add {D : ℕ} (f g h : (Fin (D + 1) → ℂ) → ℝ)
    (ψ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (y : Fin (D + 1) → ℂ)
    (hH : cxHessian h y = cxHessian f y + cxHessian g y) :
    maDensity (Fin.cons h ψ) y = maDensity (Fin.cons f ψ) y + maDensity (Fin.cons g ψ) y := by
  have hc : ∀ u : (Fin (D + 1) → ℂ) → ℝ, (fun k => cxHessian ((Fin.cons u ψ : Fin (D + 1) → _) k) y) =
      Fin.cons (cxHessian u y) (fun k => cxHessian (ψ k) y) := by
    intro u
    funext k
    refine Fin.cases ?_ (fun i => ?_) k <;> simp
  simp only [maDensity, hc, hH, PtsAddFirst.mixedDisc_cons_add, Complex.add_re]
  ring

theorem PtsAddFirst.pot_cons {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    (M : HermLine ι) (L : Fin e → HermLine ι) :
    pot (Fin.cons M L : Fin (e + 1) → HermLine ι) = Fin.cons (fun z => Real.log (M.h z)) (pot L) := by
  funext j z
  refine Fin.cases ?_ (fun i => ?_) j <;> simp [pot]

theorem PtsAddFirst.sheetDensity_add {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {e : ℕ} (Q : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1 + 1) → ℂ))
    (L : Fin e → HermLine ι) (M N : HermLine ι) (hM : IsSmoothHerm M) (hN : IsSmoothHerm N)
    (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin (e + 1) → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity Q Ψ (Fin.cons (fun z => Real.log ((M.tensor N).h z)) (pot L)) g y w =
      sheetDensity Q Ψ (Fin.cons (fun z => Real.log (M.h z)) (pot L)) g y w +
        sheetDensity Q Ψ (Fin.cons (fun z => Real.log (N.h z)) (pot L)) g y w := by
  by_cases hγ : ∃ γ, IsSheet Q Ψ y w γ
  · simp only [sheetDensity, dif_pos hγ]
    set γ := hγ.choose
    have hs : IsSheet Q Ψ y w γ := hγ.choose_spec
    have han : ∀ᶠ y' in 𝓝 y, AnalyticAt ℂ γ y' := (sheet_analyticAt osgood hs).eventually_analyticAt
    have hmc : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts Q := hs.2.mono fun _ h => h.2.1
    have hcd : ∀ {A : HermLine ι}, IsSmoothHerm A →
        ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (A.h (γ y''))) y' := fun hA =>
      (han.and hmc).mono fun y' h => pot_contDiffAt hA h.1 h.2.1
    have hsum : (fun y' => Real.log ((M.tensor N).h (γ y'))) =ᶠ[𝓝 y]
        fun y' => Real.log (M.h (γ y')) + Real.log (N.h (γ y')) := hmc.mono fun y' h =>
      Real.log_mul (M.pos _ h.1).ne' (N.pos _ h.1).ne'
    have hcons : ∀ u : ((Σ k, ι k) → ℂ) → ℝ,
        (fun j y' => (Fin.cons u (pot L) : Fin (e + 1) → _) j (γ y')) =
          Fin.cons (fun y' => u (γ y')) (fun j y' => pot L j (γ y')) := by
      intro u
      funext j y'
      refine Fin.cases ?_ (fun i => ?_) j <;> simp
    rw [hcons, hcons, hcons, PtsAddFirst.maDensity_cons_add _ _ _ _ _
      (PtsAddFirst.cxHessian_add (hcd hM) (hcd hN) hsum), mul_add]
  · simp only [sheetDensity, dif_neg hγ, add_zero]

theorem PtsAddFirst.proof (hInt : PtsIntegrableStatement) : PtsAddFirst.Statement := by
  intro K _ ι _ Q e L M N E t hQ hL hM hN hE ht
  have hL' : ∀ A : HermLine ι, IsSmoothHerm A → ∀ j, IsSmoothHerm ((Fin.cons A L : Fin (e + 1) → _) j) :=
    fun A hA j => Fin.cases hA (fun i => hL i) j
  have hMN : IsSmoothHerm (M.tensor N) := hM.mul hN
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1 + 1) → ℂ), IsGoodProj Q Ψ
  · simp only [ptsIntegral, dif_pos hΨ, ptsIntegralAt]
    have hI : ∀ A : HermLine ι, IsSmoothHerm A → Integrable (fun y => ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre Q hΨ.choose y,
        sheetDensity Q hΨ.choose (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (logNorm E t) y w) := by
      intro A hA
      have h := hInt K ι Q (e + 1) hΨ.choose (Fin.cons A L) E t hQ hΨ.choose_spec (hL' A hA) hE ht
      rwa [PtsAddFirst.pot_cons] at h
    rw [← integral_add (hI M hM) (hI N hN)]
    congr 1
    funext y
    rw [← finsum_mem_add_distrib (fibreFinite K ι Q (e + 1) hΨ.choose hQ hΨ.choose_spec y)]
    exact finsum_mem_congr rfl fun w _ => PtsAddFirst.sheetDensity_add Q _ L M N hM hN _ y w
  · simp only [ptsIntegral, dif_neg hΨ, add_zero]

end GroundTheory.Heights₂.Heights.Inter
end
end

