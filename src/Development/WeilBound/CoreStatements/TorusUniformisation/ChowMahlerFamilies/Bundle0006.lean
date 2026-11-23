module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsPointOverNonvanishing
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.PointOverExistence

theorem exists_algHom (F R : Type) [Field F] [CommRing R] [Nontrivial R] [Algebra F R]
    [Algebra.FiniteType F R] [Algebra F ℂ] : Nonempty (R →ₐ[F] ℂ) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite F (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing F (R ⧸ m)
  exact ⟨(IsAlgClosed.lift : (R ⧸ m) →ₐ[F] ℂ).comp (Ideal.Quotient.mkₐ F m)⟩

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem scale {S : Type} [CommRing S] (t : K → S) (u : (Σ k, ι k) → S) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) :
    aeval (fun p : Σ k, ι k => t p.1 * u p) g = (∏ k, t k ^ d k) * aeval u g := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h : ∏ p : Σ k, ι k, t p.1 ^ m p = ∏ k, t k ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← hg m hm k]
    exact Finset.prod_pow_eq_pow_sum Finset.univ (fun i => m ⟨k, i⟩) (t k)
  simp only [mul_pow, Finset.prod_mul_distrib, h]
  ring

theorem map_aeval' {S T : Type} [CommRing S] [CommRing T] (j : S →+* T) (u : (Σ k, ι k) → S)
    (g : MRing ι) : j (aeval u g) = aeval (fun p => j (u p)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, aeval_X]

theorem evC_eq (z : (Σ k, ι k) → ℂ) (g : MRing ι) : evC z g = aeval z g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [evC]
  | add p q hp hq => simp only [evC, map_add (f := _)] at *; rw [hp, hq]
  | mul_X p i hp => simp only [evC, map_mul, map_X, eval_X, aeval_X] at *; rw [hp]

variable {Ω : Type} [Field Ω]

theorem cone_eq (y : (Σ k, ι k) → Ω) (g : MRing ι) : mConeMap y g =
    @aeval ℤ (MvPolynomial K Ω) _ _ _ (Ring.toIntAlgebra _) (fun p : Σ k, ι k => X p.1 * C (y p)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp only [eq_intCast, map_intCast]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, hp, aeval_X, mConeMap, aeval_X, mul_comm (C _)]

theorem aeval_ne_zero {y : (Σ k, ι k) → Ω} {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d)
    (hn : g ∉ mCoordIdeal y) : aeval y g ≠ 0 := by
  intro h0
  apply hn
  have h := scale (S := MvPolynomial K Ω) (fun k => X k) (fun p => C (y p)) hg
  rw [← map_aeval' (C : Ω →+* MvPolynomial K Ω) y g, h0, map_zero, mul_zero] at h
  show mConeMap y g = 0
  rw [cone_eq, h]

theorem aeval_eq_zero {y : (Σ k, ι k) → Ω} (t : K → Ω) {f : MRing ι} (hf : f ∈ mCoordIdeal y) :
    aeval (fun p : Σ k, ι k => t p.1 * y p) f = 0 := by
  have h0 : mConeMap y f = 0 := hf
  have h := map_aeval' (eval t : MvPolynomial K Ω →+* Ω)
    (fun p : Σ k, ι k => X p.1 * C (y p)) f
  rw [← cone_eq, h0, map_zero] at h
  rw [h]
  simp only [map_mul, eval_C, eval_X]

end PositivityTheory.Xgn.PointOverExistence

open PositivityTheory.Xgn.PointOverExistence in
theorem PositivityTheory.Xgn.exists_point_over_nonvanishing : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (σ : F →+* ℂ) (g : MRing ι) (d : K → ℕ), OverInt y φ → IsMultiHomog g d → g ∉ mCoordIdeal y → ∃ z, PtOver y φ σ z ∧ evC z g ≠ 0 := by
  intro K _ ι _ Ω _ F _ _ y φ σ g d hO hg hn
  choose c hc using hO.1
  letI : Algebra F Ω := φ.toAlgebra
  letI : Algebra F ℂ := σ.toAlgebra
  let t : K → Ω := fun k => (y ⟨k, c k⟩)⁻¹
  let w : (Σ k, ι k) → Ω := fun p => t p.1 * y p
  have hγ : aeval w g ≠ 0 := by
    rw [scale t y hg]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (inv_ne_zero (hc k)))
      (aeval_ne_zero hg hn)
  let A : Subalgebra F Ω := Algebra.adjoin F (insert (aeval w g)⁻¹ (Set.range w))
  haveI : Algebra.FiniteType F A :=
    Algebra.FiniteType.adjoin_of_finite ((Set.finite_range w).insert _)
  obtain ⟨ψ⟩ := exists_algHom F A
  let wA : (Σ k, ι k) → A := fun p => ⟨w p, Algebra.subset_adjoin (Or.inr ⟨p, rfl⟩)⟩
  let δ : A := ⟨(aeval w g)⁻¹, Algebra.subset_adjoin (Or.inl rfl)⟩
  have hco : ∀ f : MRing ι, ((aeval wA f : A) : Ω) = aeval w f := fun f =>
    map_aeval' (A.val : A →+* Ω) wA f
  have hev : ∀ f : MRing ι, evC (fun p => ψ (wA p)) f = ψ (aeval wA f) := fun f => by
    rw [evC_eq]
    exact (map_aeval' (ψ : A →+* ℂ) wA f).symm
  refine ⟨fun p => ψ (wA p), ⟨⟨fun k => ⟨c k, ?_⟩, fun f hf => ?_⟩, fun a e f h hf hh H => ?_⟩, ?_⟩
  · have : wA ⟨k, c k⟩ = 1 := Subtype.ext (inv_mul_cancel₀ (hc k))
    simp only [this, map_one]
    exact one_ne_zero
  · have : aeval wA f = 0 := Subtype.ext ((hco f).trans (aeval_eq_zero t hf))
    exact (hev f).trans (by rw [this, map_zero])
  · have : aeval wA f = algebraMap F A a * aeval wA h := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, hco, hco, scale t y hf, scale t y hh, H]
      show _ = φ a * _
      ring
    rw [hev, hev, this, map_mul, ψ.commutes]
    rfl
  · have : aeval wA g * δ = 1 := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, hco]
      exact mul_inv_cancel₀ hγ
    rw [hev]
    exact left_ne_zero_of_mul_eq_one (b := ψ δ) (by rw [← map_mul, this, map_one])
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsRepresentativeAvoidingIdeal
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.RepresentativeAvoidance

section General

variable {σ M R : Type*} [CommRing R] [AddCommGroup M] (w : σ → M)

theorem comp_mul (u f : MvPolynomial σ R) (d n : M) (hf : IsWeightedHomogeneous w f d) :
    weightedHomogeneousComponent w (n + d) (u * f) = weightedHomogeneousComponent w n u * f := by
  classical
  induction u using MvPolynomial.induction_on' with
  | monomial s a =>
    have h1 : IsWeightedHomogeneous w (monomial s a : MvPolynomial σ R) (Finsupp.weight w s) :=
      isWeightedHomogeneous_monomial w s a rfl
    have h2 := h1.mul hf
    by_cases hn : n = Finsupp.weight w s
    · subst hn
      rw [h1.weightedHomogeneousComponent_same, h2.weightedHomogeneousComponent_same]
    · rw [h1.weightedHomogeneousComponent_ne n hn,
        h2.weightedHomogeneousComponent_ne (n + d) (fun h => hn (add_right_cancel h)), zero_mul]
  | add p q hp hq => rw [add_mul, map_add (f := _), map_add (f := _), hp, hq, add_mul]

theorem comp_mem_span (S : Set (MvPolynomial σ R))
    (hS : ∀ f ∈ S, ∃ d, IsWeightedHomogeneous w f d) (x : MvPolynomial σ R)
    (hx : x ∈ Ideal.span S) (n : M) : weightedHomogeneousComponent w n x ∈ Ideal.span S := by
  have key : ∀ r n, weightedHomogeneousComponent w n (r * x) ∈ Ideal.span S := by
    induction hx using Submodule.span_induction with
    | mem x h =>
      intro r n
      obtain ⟨d, hd⟩ := hS x h
      have := comp_mul w r x d (n - d) hd
      rw [sub_add_cancel] at this
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span h)
    | zero => intro r n; simp
    | add x y _ _ hx hy => intro r n; rw [mul_add, map_add (f := _)]; exact add_mem (hx r n) (hy r n)
    | smul a x _ hx => intro r n; rw [smul_eq_mul, ← mul_assoc]; exact hx _ n
  simpa using key 1 n

theorem exists_comp_notMem (W : Ideal (MvPolynomial σ R)) (u : MvPolynomial σ R) (hu : u ∉ W) :
    ∃ n, weightedHomogeneousComponent w n u ∉ W := by
  by_contra h
  push Not at h
  apply hu
  rw [← sum_weightedHomogeneousComponent (w := w) u,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp u)]
  exact W.sum_mem fun n _ => h n

end General

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def wt (ι : K → Type) : (Σ k, ι k) → (K → ℤ) := fun p => Pi.single p.1 1

theorem weight_wt (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (wt ι) m k = ((∑ i, m ⟨k, i⟩ : ℕ) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma,
    Finset.sum_eq_single k]
  · simp [wt]
  · intro j _ hj
    simp [wt, Pi.single_eq_of_ne hj.symm]
  · simp

theorem wh_of_mh {f : MRing ι} {d : K → ℕ} (h : IsMultiHomog f d) :
    IsWeightedHomogeneous (wt ι) f (fun k => (d k : ℤ)) := by
  intro m hm
  funext k
  rw [weight_wt, h m (mem_support_iff.mpr hm) k]

theorem mh_of_wh {f : MRing ι} {d : K → ℤ} (h : IsWeightedHomogeneous (wt ι) f d) (h0 : f ≠ 0) :
    ∃ e : K → ℕ, IsMultiHomog f e ∧ ∀ k, (e k : ℤ) = d k := by
  obtain ⟨m0, hm0⟩ := exists_coeff_ne_zero h0
  refine ⟨fun k => ∑ i, m0 ⟨k, i⟩, fun m hm k => ?_, fun k => ?_⟩
  · have h1 := congrFun ((h (mem_support_iff.mp hm)).trans (h hm0).symm) k
    rw [weight_wt, weight_wt] at h1
    exact_mod_cast h1
  · rw [← weight_wt, h hm0]

theorem exists_mono (W : Ideal (MRing ι)) (hW : W.IsPrime) (hr : IsRelevant W) (e : K → ℕ) :
    ∃ m : MRing ι, m ∉ W ∧ IsWeightedHomogeneous (wt ι) m (fun k => (e k : ℤ)) := by
  choose c hc using hr
  refine ⟨∏ k, X ⟨k, c k⟩ ^ e k, fun h => ?_, ?_⟩
  · obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hc k (hW.mem_of_pow_mem _ hk)
  · have := IsWeightedHomogeneous.prod (w := wt ι) Finset.univ
      (fun k => (X ⟨k, c k⟩ : MRing ι) ^ e k) (fun k => e k • wt ι ⟨k, c k⟩)
      (fun k _ => (isWeightedHomogeneous_X ℤ (wt ι) _).pow _)
    convert this using 1
    funext k
    simp [wt, Finset.sum_apply, Pi.single_apply]

theorem exists_pair (P W : Ideal (MRing ι)) (f g : MRing ι) (df dg : K → ℕ)
    (hP : IsMultiProjPrime P) (hW : IsMultiProjPrime W) (hPW : P ≤ W) (hf : IsMultiHomog f df)
    (hg : IsMultiHomog g dg) (hu : IsUnitSec P f g) :
    ∃ (U V : MRing ι) (c : K → ℤ), IsWeightedHomogeneous (wt ι) U c ∧
      IsWeightedHomogeneous (wt ι) V (c + ((fun k => (df k : ℤ)) - fun k => (dg k : ℤ))) ∧
      U ∉ W ∧ V ∉ W ∧ U * f - V * g ∈ P := by
  obtain ⟨u, v, hu, hv, huv⟩ := hu W hW.1 hPW hW.2.2
  set δ : K → ℤ := (fun k => (df k : ℤ)) - fun k => (dg k : ℤ) with hδ
  have hpair : ∀ a : K → ℤ, weightedHomogeneousComponent (wt ι) a u * f -
      weightedHomogeneousComponent (wt ι) (a + δ) v * g ∈ P := by
    intro a
    obtain ⟨S, hS, rfl⟩ := hP.2.1
    have := comp_mem_span (wt ι) S (fun x hx => (hS x hx).elim fun d hd => ⟨_, wh_of_mh hd⟩) _ huv
      (a + fun k => (df k : ℤ))
    rw [map_sub, comp_mul _ u f _ a (wh_of_mh hf)] at this
    rw [← comp_mul _ v g _ (a + δ) (wh_of_mh hg)]
    convert this using 4
    rw [hδ]; abel
  have hA : ∀ a, IsWeightedHomogeneous (wt ι) (weightedHomogeneousComponent (wt ι) a u) a :=
    fun a => weightedHomogeneousComponent_isWeightedHomogeneous a u
  have hB : ∀ a, IsWeightedHomogeneous (wt ι) (weightedHomogeneousComponent (wt ι) a v) a :=
    fun a => weightedHomogeneousComponent_isWeightedHomogeneous a v
  obtain ⟨a, ha⟩ := exists_comp_notMem (wt ι) W u hu
  obtain ⟨b, hb⟩ := exists_comp_notMem (wt ι) W v hv
  obtain ⟨a', rfl⟩ : ∃ a', b = a' + δ := ⟨b - δ, by abel⟩
  by_cases h1 : weightedHomogeneousComponent (wt ι) (a + δ) v ∈ W
  swap
  · exact ⟨_, _, a, hA a, hB _, ha, h1, hpair a⟩
  by_cases h2 : weightedHomogeneousComponent (wt ι) a' u ∈ W
  swap
  · exact ⟨_, _, a', hA a', hB _, h2, hb, hpair a'⟩
  obtain ⟨m, hm, hmd⟩ := exists_mono W hW.1 hW.2.2 (fun k => (a' k - a k).toNat)
  obtain ⟨m', hm', hmd'⟩ := exists_mono W hW.1 hW.2.2 (fun k => (a k - a' k).toNat)
  have he : (fun k => (((a k - a' k).toNat : ℕ) : ℤ)) + a' =
      (fun k => (((a' k - a k).toNat : ℕ) : ℤ)) + a := by
    funext k
    simp only [Pi.add_apply]
    omega
  refine ⟨m * weightedHomogeneousComponent (wt ι) a u + m' * weightedHomogeneousComponent (wt ι) a' u,
    m * weightedHomogeneousComponent (wt ι) (a + δ) v +
      m' * weightedHomogeneousComponent (wt ι) (a' + δ) v,
    (fun k => (((a' k - a k).toNat : ℕ) : ℤ)) + a, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hmd.mul (hA a)).add (he ▸ hmd'.mul (hA a'))
  · refine IsWeightedHomogeneous.add ?_ ?_
    · rw [add_assoc]; exact hmd.mul (hB _)
    · rw [← he, add_assoc]; exact hmd'.mul (hB _)
  · intro h
    rw [W.add_mem_iff_left (W.mul_mem_left _ h2)] at h
    exact (hW.1.mem_or_mem h).elim hm ha
  · intro h
    rw [W.add_mem_iff_right (W.mul_mem_left _ h1)] at h
    exact (hW.1.mem_or_mem h).elim hm' hb
  · convert add_mem (P.mul_mem_left m (hpair a)) (P.mul_mem_left m' (hpair a')) using 1
    ring

end PositivityTheory.Xgn.RepresentativeAvoidance

theorem PositivityTheory.Xgn.exists_representative_avoiding_ideal : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)) (f g : MRing ι) (df dg : K → ℕ), IsMultiProjPrime P → IsMultiProjPrime W → P ≤ W → IsMultiHomog f df → IsMultiHomog g dg → g ∉ P → IsUnitSec P f g → ∃ (f' g' : MRing ι) (df' dg' : K → ℕ), IsMultiHomog f' df' ∧ IsMultiHomog g' dg' ∧ (∀ k, (df' k : ℤ) - dg' k = (df k : ℤ) - dg k) ∧ f' ∉ W ∧ g' ∉ W ∧ f' * g - g' * f ∈ P ∧ IsUnitSec P f' g' := by
  intro K _ ι _ P W f g df dg hP hW hPW hf hg hgP hu
  classical
  obtain ⟨U, V, c, hU, hV, hUW, hVW, hUV⟩ :=
    PositivityTheory.Xgn.RepresentativeAvoidance.exists_pair P W f g df dg hP hW hPW hf hg hu
  obtain ⟨eU, heU, hcU⟩ := PositivityTheory.Xgn.RepresentativeAvoidance.mh_of_wh hU
    (fun h => hUW (h ▸ W.zero_mem))
  obtain ⟨eV, heV, hcV⟩ := PositivityTheory.Xgn.RepresentativeAvoidance.mh_of_wh hV
    (fun h => hVW (h ▸ W.zero_mem))
  refine ⟨V, U, eV, eU, heV, heU, fun k => ?_, hVW, hUW, ?_, fun W' hW' hPW' hr => ?_⟩
  · rw [hcU, hcV]; simp
  · convert neg_mem hUV using 1
    ring
  · obtain ⟨u, v, hu', hv', huv⟩ := hu W' hW' hPW' hr
    refine ⟨u, v, hu', hv', (hP.1.mem_or_mem (x := g) ?_).resolve_left hgP⟩
    convert sub_mem (P.mul_mem_left U huv) (P.mul_mem_left u hUV) using 1
    ring
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.LineLatticeVectorBundle
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.LineLatticeVectorBundle

theorem alt_det {Ω E N : Type} [Field Ω] [AddCommGroup E] [Module Ω E] [AddCommGroup N] [Module Ω N] {p : ℕ}
    (f : E [⋀^Fin p]→ₗ[Ω] N) (v : Fin p → E) (c : Matrix (Fin p) (Fin p) Ω) :
    f (fun i => ∑ j, c i j • v j) = c.det • f v := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff Ω]
  intro φ
  have h := AlternatingMap.eq_smul_basis_det (Pi.basisFun Ω (Fin p))
    (φ.compAlternatingMap (f.compLinearMap (Fintype.linearCombination Ω v)))
  have h2 := congrArg (fun g => g (fun i => c i)) h
  simp only [LinearMap.compAlternatingMap_apply, AlternatingMap.compLinearMap_apply,
    AlternatingMap.smul_apply, Pi.basisFun_det_apply, Pi.basisFun_apply,
    Fintype.linearCombination_apply_single, one_smul, smul_eq_mul] at h2
  simp only [Fintype.linearCombination_apply] at h2
  rw [map_sub, map_smul, h2, smul_eq_mul, mul_comm, sub_eq_zero]
  rfl

theorem line_of_span {Ω E N : Type} [Field Ω] [AddCommGroup E] [Module Ω E] [AddCommGroup N] [Module Ω N] {p : ℕ}
    (f : E [⋀^Fin p]→ₗ[Ω] N) (v v' : Fin p → E)
    (h : Submodule.span Ω (Set.range v') = Submodule.span Ω (Set.range v)) : ∃ c : Ω, f v' = c • f v := by
  have : ∀ i, ∃ c : Fin p → Ω, ∑ j, c j • v j = v' i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (h ▸ Submodule.subset_span ⟨i, rfl⟩)
  choose c hc using this
  refine ⟨(Matrix.of c).det, ?_⟩
  rw [← alt_det]
  congr 1
  funext i
  exact (hc i).symm

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem wedge_frame {A : Lat ξ E} {p : ℕ} {v : Fin p → E} {x : Cpt ξ} (h : A.IsFrameAt v x) :
    A.wedge p x = Submodule.span (regAt ξ x) {exteriorPower.ιMulti Ω p v} := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro w ⟨b, hb, rfl⟩
    have : ∀ i, ∃ c : Fin p → regAt ξ x, ∑ j, c j • v j = b i := fun i =>
      (Submodule.mem_span_range_iff_exists_fun _).1 (h.2 ▸ hb i)
    choose c hc using this
    refine Submodule.mem_span_singleton.2 ⟨(Matrix.of c).det, ?_⟩
    have e := alt_det (exteriorPower.ιMulti Ω p) v ((regAt ξ x).subtype.mapMatrix (Matrix.of c))
    rw [← RingHom.map_det] at e
    refine e.symm.trans ?_
    congr 1
    funext i
    exact hc i
  · refine Submodule.span_mono ?_
    rintro w rfl
    exact ⟨v, fun i => h.2 ▸ Submodule.subset_span ⟨i, rfl⟩, rfl⟩

theorem span_unit {x : Cpt ξ} {u : Ω} (hu : unitAt ξ x u) (e : E) :
    Submodule.span (regAt ξ x) {u • e} = Submodule.span (regAt ξ x) {e} := by
  refine le_antisymm ?_ ?_ <;> rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
  · exact ⟨⟨u, hu.2.1⟩, rfl⟩
  · exact ⟨⟨u⁻¹, hu.2.2⟩, by
      change u⁻¹ • u • e = e
      rw [inv_smul_smul₀ hu.1]⟩

theorem coeff_unit {x : Cpt ξ} {a : E} (ha : a ≠ 0) {α α' : Ω} (h0 : α ≠ 0)
    (h : Submodule.span (regAt ξ x) {α • a} = Submodule.span (regAt ξ x) {α' • a}) :
    ∃ u, unitAt ξ x u ∧ α = u * α' := by
  obtain ⟨u, hu, e⟩ := ZUnit.exists_of_span_eq (smul_ne_zero h0 ha) h
  exact ⟨u, hu, smul_left_injective Ω ha (by simpa [mul_smul] using e)⟩

theorem on_line {A : Lat ξ E} {T : Set (Cpt ξ)} {p : ℕ} {V : Submodule Ω E} (hA : A.IsVBOn T p V)
    {a : ⋀[Ω]^p E} (ha : a ≠ 0) {x : Cpt ξ} (hx : x ∈ T) {α : Ω} (h0 : α ≠ 0)
    (h : A.wedge p x = Submodule.span (regAt ξ x) {α • a}) (v : Fin p → E)
    (hv : Submodule.span Ω (Set.range v) = V) : ∃ γ : Ω, γ ≠ 0 ∧ exteriorPower.ιMulti Ω p v = γ • a := by
  obtain ⟨U, hU, b, hb, hf⟩ := hA x hx
  have h1 := wedge_frame (hf x hx hU)
  obtain ⟨u, -, e⟩ := ZUnit.exists_of_span_eq (smul_ne_zero h0 ha) (h.symm.trans h1)
  obtain ⟨c, hc⟩ := line_of_span (exteriorPower.ιMulti Ω p) v b (hb.trans hv.symm)
  rw [hc, smul_smul] at e
  have huc : u * c ≠ 0 := by
    intro h'
    rw [h', zero_smul] at e
    exact smul_ne_zero h0 ha e
  refine ⟨(u * c)⁻¹ * α, mul_ne_zero (inv_ne_zero huc) h0, ?_⟩
  rw [mul_smul, e, inv_smul_smul₀ huc]

section
variable {A B : Lat ξ E} {p q : ℕ} {a : ⋀[Ω]^p E} {b : ⋀[Ω]^q E} {x : Cpt ξ}

theorem gen_of_coeff (ha : a ≠ 0) (hb : b ≠ 0) {f : Ω} (h : IsCoeffAt A B p q a b x f) :
    (lineLat A B p q a b).IsGenAt x f⁻¹ := by
  have h' := h
  obtain ⟨α, β, hα, hβ, hA, hB, e⟩ := h
  have hf : f ≠ 0 := by
    rintro rfl
    exact hβ (by rw [← e, zero_mul])
  refine ⟨inv_ne_zero hf, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)⟩
  · rintro t ⟨g, ⟨α', β', hα', hβ', hA', hB', e'⟩, rfl⟩
    obtain ⟨u, hu, eu⟩ := coeff_unit ha hα' (hA'.symm.trans hA)
    obtain ⟨w, hw, ew⟩ := coeff_unit hb hβ (hB.symm.trans hB')
    refine Submodule.mem_span_singleton.2 ⟨⟨u * w, mul_mem hu.2.1 hw.2.1⟩, ?_⟩
    change u * w * f⁻¹ = g⁻¹
    have hg : g ≠ 0 := by
      rintro rfl
      exact hβ' (by rw [← e', zero_mul])
    have key : f * α = (w * g * u) * α := by rw [e, ew, ← e', eu]; ring
    have key2 : f = w * g * u := mul_right_cancel₀ hα key
    have := hu.1
    have := hw.1
    rw [key2]
    field_simp
  · rintro t rfl
    exact ⟨f, h', rfl⟩

theorem gen_iff (ha : a ≠ 0) (hb : b ≠ 0) {f : Ω} (h : IsCoeffAt A B p q a b x f) (t : Ω) :
    (lineLat A B p q a b).IsGenAt x t ↔ t ≠ 0 ∧ IsCoeffAt A B p q a b x t⁻¹ := by
  constructor
  · rintro ⟨ht, hL⟩
    refine ⟨ht, ?_⟩
    obtain ⟨u, hu, e⟩ := ZUnit.exists_of_span_eq ht (hL.symm.trans (gen_of_coeff ha hb h).2)
    obtain ⟨α, β, hα, hβ, hA, hB, e'⟩ := h
    refine ⟨u * α, β, mul_ne_zero hu.1 hα, hβ, ?_, hB, ?_⟩
    · rw [mul_smul, span_unit hu, hA]
    · have := hu.1
      rw [e, ← e', smul_eq_mul, mul_inv, inv_inv]
      field_simp
  · rintro ⟨-, h⟩
    simpa using gen_of_coeff ha hb h

theorem coeff_of_frames {v : Fin p → E} {w : Fin q → E} {α β : Ω} (hv : A.IsFrameAt v x) (hw : B.IsFrameAt w x)
    (hα : α ≠ 0) (hβ : β ≠ 0) (ev : exteriorPower.ιMulti Ω p v = α • a)
    (ew : exteriorPower.ιMulti Ω q w = β • b) : IsCoeffAt A B p q a b x (α / β)⁻¹ :=
  ⟨α, β, hα, hβ, ev ▸ wedge_frame hv, ew ▸ wedge_frame hw, by field_simp⟩

end

theorem ne_zero_of_frames {A : Lat ξ E} {p : ℕ} {a : ⋀[Ω]^p E} (ha : a ≠ 0) {x : Cpt ξ} {v v' : Fin p → E}
    {α α' : Ω} (hv : A.IsFrameAt v x) (hv' : A.IsFrameAt v' x) (e : exteriorPower.ιMulti Ω p v = α • a)
    (e' : exteriorPower.ιMulti Ω p v' = α' • a) (h : α' ≠ 0) : α ≠ 0 := by
  rintro rfl
  have h1 := (wedge_frame hv').symm.trans (wedge_frame hv)
  rw [e, e', zero_smul, Submodule.span_zero_singleton, Submodule.span_singleton_eq_bot] at h1
  exact smul_ne_zero h ha h1

end PositivityTheory.Xgn.LineLatticeVectorBundle

theorem PositivityTheory.Xgn.line_lattice_vector_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (A B : Lat ξ E) (p q : ℕ) (V V' : Submodule Ω E) (T : Set (Cpt ξ)) (a : ⋀[Ω]^p E) (b : ⋀[Ω]^q E), A.IsVBOn T p V → B.IsVBOn T q V' → a ≠ 0 → b ≠ 0 → (∃ x ∈ T, ∃ f, IsCoeffAt A B p q a b x f) → (lineLat A B p q a b).IsVBOn T 1 ⊤ ∧ (∀ x ∈ T, ∀ t : Ω, (lineLat A B p q a b).IsGenAt x t ↔ t ≠ 0 ∧ IsCoeffAt A B p q a b x t⁻¹) ∧ ∀ x ∈ T, ∀ (v : Fin p → E) (w : Fin q → E) (α β : Ω), A.IsFrameAt v x → B.IsFrameAt w x → exteriorPower.ιMulti Ω p v = α • a → exteriorPower.ιMulti Ω q w = β • b → (lineLat A B p q a b).IsGenAt x (α / β) := by
  intro X Ω _ ξ E _ _ A B p q V V' T a b hA hB ha hb hex
  obtain ⟨x₀, hx₀, f₀, α₀, β₀, hα₀, hβ₀, hA₀, hB₀, -⟩ := hex
  have loc : ∀ x ∈ T, ∃ U : X.Opens, x.1 ∈ U ∧ ∃ (v : Fin p → E) (w : Fin q → E) (α β : Ω), α ≠ 0 ∧ β ≠ 0 ∧
      exteriorPower.ιMulti Ω p v = α • a ∧ exteriorPower.ιMulti Ω q w = β • b ∧
      ∀ y ∈ T, y.1 ∈ U → A.IsFrameAt v y ∧ B.IsFrameAt w y := by
    intro x hx
    obtain ⟨U, hU, v, hv, hfv⟩ := hA x hx
    obtain ⟨U', hU', w, hw, hfw⟩ := hB x hx
    obtain ⟨α, hα, ev⟩ := PositivityTheory.Xgn.LineLatticeVectorBundle.on_line hA ha hx₀ hα₀ hA₀ v hv
    obtain ⟨β, hβ, ew⟩ := PositivityTheory.Xgn.LineLatticeVectorBundle.on_line hB hb hx₀ hβ₀ hB₀ w hw
    exact ⟨U ⊓ U', ⟨hU, hU'⟩, v, w, α, β, hα, hβ, ev, ew, fun y hy hyU => ⟨hfv y hy hyU.1, hfw y hy hyU.2⟩⟩
  refine ⟨fun x hx => ?_, fun x hx t => ?_, fun x hx v w α β hv hw ev ew => ?_⟩
  · obtain ⟨U, hU, v, w, α, β, hα, hβ, ev, ew, h⟩ := loc x hx
    have h0 : α / β ≠ 0 := div_ne_zero hα hβ
    have hr : Set.range (fun _ : Fin 1 => α / β) = {α / β} := Set.range_const
    refine ⟨U, hU, fun _ => α / β, ?_, fun y hy hyU => ⟨?_, ?_⟩⟩
    · rw [hr, eq_top_iff]
      intro s _
      exact Submodule.mem_span_singleton.2 ⟨s / (α / β), div_mul_cancel₀ s h0⟩
    · exact linearIndependent_unique_iff.2 h0
    · have := (PositivityTheory.Xgn.LineLatticeVectorBundle.gen_of_coeff ha hb
        (PositivityTheory.Xgn.LineLatticeVectorBundle.coeff_of_frames (h y hy hyU).1 (h y hy hyU).2 hα hβ ev ew)).2
      rw [inv_inv] at this
      rw [hr, this]
  · obtain ⟨U, hU, v, w, α, β, hα, hβ, ev, ew, h⟩ := loc x hx
    exact PositivityTheory.Xgn.LineLatticeVectorBundle.gen_iff ha hb
      (PositivityTheory.Xgn.LineLatticeVectorBundle.coeff_of_frames (h x hx hU).1 (h x hx hU).2 hα hβ ev ew) t
  · obtain ⟨U, hU, v', w', α', β', hα, hβ, ev', ew', h⟩ := loc x hx
    have := PositivityTheory.Xgn.LineLatticeVectorBundle.gen_of_coeff ha hb
      (PositivityTheory.Xgn.LineLatticeVectorBundle.coeff_of_frames hv hw
        (PositivityTheory.Xgn.LineLatticeVectorBundle.ne_zero_of_frames ha hv (h x hx hU).1 ev ev' hα)
        (PositivityTheory.Xgn.LineLatticeVectorBundle.ne_zero_of_frames hb hw (h x hx hU).2 ew ew' hβ) ev ew)
    rwa [inv_inv] at this
end

