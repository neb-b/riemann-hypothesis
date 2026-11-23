module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0016
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0060
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.MultihomogeneousLineBundle
section
open MvPolynomial

namespace PositivityTheory.Xgn.MultihomogeneousLine

theorem sum_scale {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {n : ℕ}
    (u : Fin n → MvPolynomial (Σ k, ι k) ℤ) (a : K → ℕ)
    (hu : ∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (u j) a) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    ∑ j, ‖eval (fun p => c p.1 * z p) (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2 =
      (∏ k, ‖c k‖ ^ a k) ^ 2 * ∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [PositivityTheory.Xgn.multihomogeneous_eval_scale K ι (u j) a c z (hu j), norm_mul, mul_pow, norm_prod]
  simp only [norm_pow]

theorem sum_pos {σ : Type} {n : ℕ} (u : Fin n → MvPolynomial σ ℤ) (z : σ → ℂ)
    (h : ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j)) ≠ 0) :
    0 < ∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2 := by
  obtain ⟨j, hj⟩ := h
  exact Finset.sum_pos' (fun i _ => sq_nonneg _)
    ⟨j, Finset.mem_univ j, pow_pos (norm_pos_iff.mpr hj) 2⟩

theorem sqrt_scale (x y N D : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt ((x ^ 2 * N) / (y ^ 2 * D)) = x / y * Real.sqrt (N / D) := by
  rw [mul_div_mul_comm, ← div_pow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (div_nonneg hx hy)]

end PositivityTheory.Xgn.MultihomogeneousLine

theorem PositivityTheory.Xgn.multihomogeneous_line_bundle : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a b : K → ℕ) (n : ℕ) (u v : Fin n → MvPolynomial (Σ k, ι k) ℤ), (∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (u j) a) → (∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (v j) b) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j)) ≠ 0) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j)) ≠ 0) → ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A → ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH A → ∃ A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, A'.a = (fun k => A.a k + (a k : ℤ) - (b k : ℤ)) ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A' ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH A' ∧ ∀ z : ((Σ k, ι k) → ℂ), A'.h z = A.h z * Real.sqrt ((∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) / (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2)) := by
  intro K _ _ ι _ A a b n u v hu hv hu0 hv0 hsm hconj
  refine ⟨⟨fun k => A.a k + (a k : ℤ) - (b k : ℤ),
    fun z => A.h z * Real.sqrt ((∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) /
      (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2)), ?_, ?_⟩, rfl, ?_, ?_, fun _ => rfl⟩
  · intro z hz
    exact mul_pos (A.pos z hz) (Real.sqrt_pos.mpr (div_pos
      (MultihomogeneousLine.sum_pos u z (hu0 z hz)) (MultihomogeneousLine.sum_pos v z (hv0 z hz))))
  · intro c z hc
    rw [A.smul c z hc, MultihomogeneousLine.sum_scale u a hu, MultihomogeneousLine.sum_scale v b hv,
      MultihomogeneousLine.sqrt_scale _ _ _ _
        (Finset.prod_nonneg fun k _ => pow_nonneg (norm_nonneg _) _)
        (Finset.prod_nonneg fun k _ => pow_nonneg (norm_nonneg _) _)]
    have : ∀ k, ‖c k‖ ^ (A.a k + (a k : ℤ) - (b k : ℤ)) = ‖c k‖ ^ A.a k * ‖c k‖ ^ a k / ‖c k‖ ^ b k := by
      intro k
      have h0 : ‖c k‖ ≠ 0 := norm_ne_zero_iff.mpr (hc k)
      rw [zpow_sub₀ h0, zpow_add₀ h0, zpow_natCast, zpow_natCast]
    simp only [this, Finset.prod_div_distrib, Finset.prod_mul_distrib]
    ring
  · have hN : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ =>
        ∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) :=
      ContDiff.sum fun j _ => PositivityTheory.Xgn.polynomial_norm_square_smooth _ (u j)
    have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ =>
        ∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2) :=
      ContDiff.sum fun j _ => PositivityTheory.Xgn.polynomial_norm_square_smooth _ (v j)
    exact ContDiffOn.mul hsm (ContDiffOn.sqrt
      (hN.contDiffOn.div hD.contDiffOn fun z hz => (MultihomogeneousLine.sum_pos v z (hv0 z hz)).ne')
      fun z hz => (div_pos (MultihomogeneousLine.sum_pos u z (hu0 z hz))
        (MultihomogeneousLine.sum_pos v z (hv0 z hz))).ne')
  · intro z
    have := hconj z
    simp only [this, PositivityTheory.Xgn.polynomial_eval_complex_conjugate, RCLike.norm_conj]
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.MultihomogeneousTwistFinite
section
open MvPolynomial

namespace PositivityTheory.Xgn.MultihomogeneousTwistFinite
open GroundTheory.Heights₂.Heights.NumbersDVR

theorem homog_prod {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} (c : ∀ k, ι k)
    (d : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ d k) d := by
  have h := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
    (fun k => (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ d k)
    (fun k => d k • blockWeight ι ⟨k, c k⟩)
    (fun k _ => (isWeightedHomogeneous_X ℤ (blockWeight ι) ⟨k, c k⟩).pow (d k))
  have e : ∑ k, d k • blockWeight ι ⟨k, c k⟩ = d := by
    funext j
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [e] at h
  exact h

theorem eval_mul_ne {K : Type} [Fintype K] {ι : K → Type} (c : ∀ k, ι k)
    (d : K → ℕ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (u : MvPolynomial (Σ k, ι k) ℤ)
    (hu : eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0) :
    eval z (MvPolynomial.map (Int.castRingHom ℂ)
      (u * ∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ d k)) ≠ 0 := by
  rw [map_mul, map_mul]
  refine mul_ne_zero hu ?_
  simp only [map_prod, map_pow, MvPolynomial.map_X, MvPolynomial.eval_X]
  exact Finset.prod_ne_zero_iff.2 (fun k _ => pow_ne_zero _ (hc k))

end PositivityTheory.Xgn.MultihomogeneousTwistFinite

theorem PositivityTheory.Xgn.multihomogeneous_twist_finite : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : (K → ℕ) → (K → ℕ) → MvPolynomial (Σ k, ι k) ℤ → MvPolynomial (Σ k, ι k) ℤ → Prop) (bf bg : K → ℕ), (∀ (a b d : K → ℕ) (u v m : MvPolynomial (Σ k, ι k) ℤ), Q a b u v → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog m d → Q (a + d) (b + d) (u * m) (v * m)) → (∀ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog u a ∧ GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) v) ≠ 0) → ∃ (A B : K → ℕ) (n : ℕ) (u v : Fin n → MvPolynomial (Σ k, ι k) ℤ), A + bf = B + bg ∧ (∀ j, Q A B (u j) (v j)) ∧ (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j)) ≠ 0) ∧ (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j)) ≠ 0) := by
  intro K _ _ ι _ Q bf bg hQmul hQ hU hV
  obtain ⟨TU, hTU, hselU⟩ :=
    PositivityTheory.Xgn.finite_nonvanishing_selection (Σ k, ι k) {u | ∃ a b v, Q a b u v}
  obtain ⟨TV, hTV, hselV⟩ :=
    PositivityTheory.Xgn.finite_nonvanishing_selection (Σ k, ι k) {v | ∃ a b u, Q a b u v}
  have wU : ∀ t : TU, ∃ a b v, Q a b t.1 v := fun t => hTU t.2
  have wV : ∀ t : TV, ∃ a b u, Q a b u t.1 := fun t => hTV t.2
  choose aU bU vU hqU using wU
  choose aV bV uV hqV using wV
  obtain ⟨A, hA⟩ : ∃ A : K → ℕ, A = bg + (∑ t, aU t + ∑ t, aV t) := ⟨_, rfl⟩
  have leU : ∀ t k, aU t k ≤ A k := by
    intro t k
    rw [hA]
    simp only [Pi.add_apply, Finset.sum_apply]
    have := Finset.single_le_sum (f := fun t => aU t k) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ t)
    omega
  have leV : ∀ t k, aV t k ≤ A k := by
    intro t k
    rw [hA]
    simp only [Pi.add_apply, Finset.sum_apply]
    have := Finset.single_le_sum (f := fun t => aV t k) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ t)
    omega
  have hbgA : ∀ k, bg k ≤ A k := by
    intro k
    rw [hA]
    simp only [Pi.add_apply]
    omega
  obtain ⟨B, hB⟩ : ∃ B : K → ℕ, B = A + bf - bg := ⟨_, rfl⟩
  have hAB : A + bf = B + bg := by
    funext k
    rw [hB]
    simp only [Pi.add_apply, Pi.sub_apply]
    have := hbgA k
    omega
  have lift : ∀ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ) (c : ∀ k, ι k), Q a b u v →
      (∀ k, a k ≤ A k) →
      Q A B (u * ∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - a) k)
        (v * ∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - a) k) := by
    intro a b u v c hq hle
    have h := hQmul a b (A - a) u v _ hq (MultihomogeneousTwistFinite.homog_prod c (A - a))
    obtain ⟨_, _, hab⟩ := hQ a b u v hq
    have e1 : a + (A - a) = A := by
      funext k
      simp only [Pi.add_apply, Pi.sub_apply]
      have := hle k
      omega
    have e2 : b + (A - a) = B := by
      funext k
      have h1 := congrFun hab k
      have h2 := congrFun hAB k
      simp only [Pi.add_apply, Pi.sub_apply] at h1 h2 ⊢
      have := hle k
      omega
    rw [e1, e2] at h
    exact h
  let e := Fintype.equivFin ((TU × (∀ k, ι k)) ⊕ (TV × (∀ k, ι k)))
  let uu : (TU × (∀ k, ι k)) ⊕ (TV × (∀ k, ι k)) → MvPolynomial (Σ k, ι k) ℤ :=
    Sum.elim (fun p => p.1.1 * ∏ k, (X ⟨k, p.2 k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - aU p.1) k)
      (fun p => uV p.1 * ∏ k, (X ⟨k, p.2 k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - aV p.1) k)
  let vv : (TU × (∀ k, ι k)) ⊕ (TV × (∀ k, ι k)) → MvPolynomial (Σ k, ι k) ℤ :=
    Sum.elim (fun p => vU p.1 * ∏ k, (X ⟨k, p.2 k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - aU p.1) k)
      (fun p => p.1.1 * ∏ k, (X ⟨k, p.2 k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - aV p.1) k)
  refine ⟨A, B, _, fun j => uu (e.symm j), fun j => vv (e.symm j), hAB, ?_, ?_, ?_⟩
  · intro j
    show Q A B (uu (e.symm j)) (vv (e.symm j))
    generalize e.symm j = w
    rcases w with ⟨t, c⟩ | ⟨t, c⟩
    · exact lift _ _ _ _ c (hqU t) (leU t)
    · exact lift _ _ _ _ c (hqV t) (leV t)
  · intro z hz
    obtain ⟨a, b, u, v, hq, hu⟩ := hU z hz
    choose c hc using hz
    obtain ⟨t, ht, htne⟩ := hselU z ⟨u, ⟨a, b, v, hq⟩, hu⟩
    refine ⟨e (Sum.inl (⟨t, ht⟩, c)), ?_⟩
    simp only [uu, Equiv.symm_apply_apply, Sum.elim_inl]
    exact MultihomogeneousTwistFinite.eval_mul_ne c _ z hc _ htne
  · intro z hz
    obtain ⟨a, b, u, v, hq, hv⟩ := hV z hz
    choose c hc using hz
    obtain ⟨t, ht, htne⟩ := hselV z ⟨v, ⟨a, b, u, hq⟩, hv⟩
    refine ⟨e (Sum.inr (⟨t, ht⟩, c)), ?_⟩
    simp only [vv, Equiv.symm_apply_apply, Sum.elim_inr]
    exact MultihomogeneousTwistFinite.eval_mul_ne c _ z hc _ htne
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.X_join_model
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_join_model

section Trdeg

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]

theorem mem_of_mem_adjoin (F : Subfield Ω) (hO : ∀ c : O, algebraMap O Ω c ∈ F) {a : Ω}
    (ha : a ∈ Algebra.adjoin O (F : Set Ω)) : a ∈ F := by
  induction ha using Algebra.adjoin_induction with
  | mem w hw => exact hw
  | algebraMap c => exact hO c
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2

theorem trdeg_add (hinj : Function.Injective (algebraMap O Ω)) (F F' : Subfield Ω) (hle : F ≤ F')
    (hO : ∀ c : O, algebraMap O Ω c ∈ F) {r : ℕ} (t : Fin r → Ω) (hind : AlgebraicIndependent F t)
    (hmem : ∀ i, t i ∈ F') (halg : ∀ v ∈ F', IsAlgebraic (IntermediateField.adjoin F (Set.range t)) v) :
    Algebra.trdeg O (Algebra.adjoin O (F' : Set Ω)) =
      Algebra.trdeg O (Algebra.adjoin O (F : Set Ω)) + r := by
  have hU : (F : Set Ω) ∪ (F' : Set Ω) = F' := Set.union_eq_right.2 hle
  have h := AdjoinTrdegAdd.proof O Ω hinj (F : Set Ω) (F' : Set Ω) (Fin r) t
    (by rintro _ ⟨i, rfl⟩; exact hmem i) ?_ ?_
  · rw [hU, Fintype.card_fin] at h
    exact h
  · let f : Algebra.adjoin O (F : Set Ω) →+* F :=
      (Algebra.adjoin O (F : Set Ω)).val.toRingHom.codRestrict F fun a => mem_of_mem_adjoin F hO a.2
    refine AlgebraicIndependent.of_ringHom_of_comp_eq f (RingHom.id Ω) hind ?_ ?_
    · intro a b hab
      exact Subtype.ext (congrArg (fun w : F => (w : Ω)) hab)
    · ext a; rfl
  · intro a ha
    have h1 : IsAlgebraic (Algebra.adjoin F (Set.range t)) a :=
      IntermediateField.isAlgebraic_adjoin_iff.1 (halg a ha)
    have hsub : ∀ w ∈ Algebra.adjoin F (Set.range t),
        w ∈ Algebra.adjoin O ((F : Set Ω) ∪ Set.range t) := by
      intro w hw
      induction hw using Algebra.adjoin_induction with
      | mem w hw => exact Algebra.subset_adjoin (Or.inr hw)
      | algebraMap c => exact Algebra.subset_adjoin (Or.inl c.2)
      | add _ _ _ _ h1 h2 => exact add_mem h1 h2
      | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2
    let f : Algebra.adjoin F (Set.range t) →+* Algebra.adjoin O ((F : Set Ω) ∪ Set.range t) :=
      (Algebra.adjoin F (Set.range t)).val.toRingHom.codRestrict _ fun w => hsub w w.2
    refine IsAlgebraic.ringHom_of_comp_eq f (RingHom.id Ω) h1 ?_ ?_
    · intro a b hab
      exact Subtype.ext (congrArg (fun w : Algebra.adjoin O ((F : Set Ω) ∪ Set.range t) => (w : Ω)) hab)
    · ext a; rfl

end Trdeg

section Model

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [IsDomain O] [IsDiscreteValuationRing O] [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem comap_eq_ker (y : (Σ k, ι k) → Ω) :
    (pointIdeal O y).comap (C : O →+* MRing ι O) = RingHom.ker (algebraMap O Ω) := by
  ext a
  simp [pointIdeal, RingHom.mem_ker, pointConeMap, MvPolynomial.algebraMap_apply]

theorem dim_eq (hinj : Function.Injective (algebraMap O Ω)) (y : (Σ k, ι k) → Ω)
    (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) :
    ringKrullDim (MRing ι O ⧸ pointIdeal O y) =
      (((Algebra.trdeg O (Algebra.adjoin O (fnField O y : Set Ω))).toENat +
        ((1 + Fintype.card K : ℕ) : ℕ∞) : ℕ∞) : WithBot ℕ∞) := by
  have h1 := DvrConeDimTrdeg.proof O K ι (pointIdeal O y)
    (GenericProjClosureDim.isMultiProjPrime_pointIdeal (R := O) _ hy)
    (by rw [comap_eq_ker]; exact (RingHom.injective_iff_ker_eq_bot _).1 hinj)
  have h2 : Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) = _ := ConeTrdegFnField.proof O Ω hinj K ι y hy
  rw [h1, h2, map_add (f := _), map_natCast]
  congr 1
  push_cast
  ring

theorem isModelOver_iff (y : (Σ k, ι k) → Ω) (d : ℕ) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O y) d ↔
      Nonempty K ∧ (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) ∧ Function.Injective (algebraMap O Ω) ∧
        (Algebra.trdeg O (Algebra.adjoin O (fnField O y : Set Ω))).toENat = d := by
  have key : ∀ T : ℕ∞, ((T + ((1 + Fintype.card K : ℕ) : ℕ∞) : ℕ∞) : WithBot ℕ∞) =
      ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) ↔ T = d := by
    intro T
    have e : ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) =
        (((d : ℕ∞) + ((1 + Fintype.card K : ℕ) : ℕ∞) : ℕ∞) : WithBot ℕ∞) := by
      rw [add_assoc, ← Nat.cast_add]; rfl
    rw [e, WithBot.coe_inj]
    exact ⟨fun h => WithTop.add_right_cancel (ENat.natCast_ne_top _) h, fun h => by rw [h]⟩
  constructor
  · intro h
    have hy := JoinTwoModels.exists_ne_zero y h
    rw [BundleExamples.mcIdeal_eq_pointIdeal, BundleExamples.isModelOver_iff] at h
    have hinj : Function.Injective (algebraMap O Ω) := by
      rw [RingHom.injective_iff_ker_eq_bot, ← comap_eq_ker y]
      exact h.2.noTorsion
    refine ⟨h.1, hy, hinj, (key _).1 ?_⟩
    rw [← dim_eq hinj y hy]
    exact h.2.dim
  · rintro ⟨hK, hy, hinj, hT⟩
    rw [BundleExamples.mcIdeal_eq_pointIdeal, BundleExamples.isModelOver_iff]
    refine ⟨hK, GenericProjClosureDim.isMultiProjPrime_pointIdeal (R := O) _ hy, ?_, ?_⟩
    · rw [comap_eq_ker]; exact (RingHom.injective_iff_ker_eq_bot _).1 hinj
    · rw [dim_eq hinj y hy]
      exact (key _).2 hT

end Model

end PositivityTheory.Xgn.A_join_model

theorem PositivityTheory.Xgn.t_join_model : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d r : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∀ t : Fin r → Ω, AlgebraicIndependent (fnField O x) t → (∀ i, t i ∈ fnField O (joinCoord x z)) → (∀ v ∈ fnField O (joinCoord x z), IsAlgebraic (IntermediateField.adjoin (fnField O x) (Set.range t)) v) → GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) (d + r) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d r hx K' _ _ ι' _ z hz t hind hmem halg
  obtain ⟨hK, hx0, hinj, hT⟩ := (PositivityTheory.Xgn.A_join_model.isModelOver_iff x d).1 hx
  refine (PositivityTheory.Xgn.A_join_model.isModelOver_iff (joinCoord x z) (d + r)).2 ⟨inferInstance, ?_, hinj, ?_⟩
  · rintro (k | k)
    · exact hx0 k
    · exact hz k
  · have hle : fnField O x ≤ fnField O (joinCoord x z) := by
      refine Subfield.closure_le.2 ?_
      rintro _ (⟨a, rfl⟩ | ⟨⟨k, i, j⟩, rfl⟩)
      · exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
      · exact Subfield.subset_closure (Or.inr ⟨⟨.inl k, (i, j)⟩, rfl⟩)
    rw [PositivityTheory.Xgn.A_join_model.trdeg_add hinj _ _ hle
      (fun c => Subfield.subset_closure (Or.inl ⟨c, rfl⟩)) t hind hmem halg, map_add, map_natCast, hT,
      Nat.cast_add]
end

