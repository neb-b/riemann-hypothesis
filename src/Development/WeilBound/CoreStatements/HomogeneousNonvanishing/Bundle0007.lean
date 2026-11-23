module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0025
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0019
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0004

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.CMadens
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

theorem madens_hess {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E ≃L[ℝ] E) (φ : E → ℝ) (y u v : E) :
    fderiv ℝ (fderiv ℝ (φ ∘ c)) y u v = fderiv ℝ (fderiv ℝ φ) (c y) (c u) (c v) := by
  set e : (E →L[ℝ] ℝ) ≃L[ℝ] (E →L[ℝ] ℝ) := c.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ) with he
  have h1 : fderiv ℝ (φ ∘ c) = e ∘ fderiv ℝ φ ∘ c := by
    funext z
    rw [c.comp_right_fderiv]
    ext w
    simp [he]
  rw [h1, e.comp_fderiv, c.comp_right_fderiv]
  simp [he]

theorem madens_cx (D : ℕ) (φ : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ) :
    cxHessian (fun y' => φ (fun i => starRingEnd ℂ (y' i))) y =
      (cxHessian φ (fun i => starRingEnd ℂ (y i))).map (starRingEnd ℂ) := by
  let c : (Fin D → ℂ) ≃L[ℝ] (Fin D → ℂ) := ContinuousLinearEquiv.piCongrRight (fun _ => Complex.conjCLE)
  have hc : ∀ z, c z = fun i => starRingEnd ℂ (z i) := fun z => rfl
  have hf : (fun y' : Fin D → ℂ => φ (fun i => starRingEnd ℂ (y' i))) = φ ∘ c := by
    funext z; simp [hc]
  have h1 : ∀ i : Fin D, c (Pi.single i 1) = Pi.single i 1 := by
    intro i; funext k; rw [hc]; by_cases h : k = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  have h2 : ∀ i : Fin D, c (Complex.I • Pi.single i 1) = -(Complex.I • Pi.single i 1) := by
    intro i; funext k; rw [hc]; by_cases h : k = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  ext i j
  simp only [cxHessian, Matrix.map_apply, hf, madens_hess, h1, h2, map_neg, ContinuousLinearMap.neg_apply, neg_neg]
  rw [hc y]
  generalize fderiv ℝ (fderiv ℝ φ) (fun i => starRingEnd ℂ (y i)) = H
  simp only [map_div₀, map_add (f := _), map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, sub_neg_eq_add, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_neg]
  ring

theorem c_madens : ∀ (D : ℕ) (φ : Fin D → (Fin D → ℂ) → ℝ) (y : Fin D → ℂ), maDensity (fun j y' => φ j (fun i => starRingEnd ℂ (y' i))) y = maDensity φ (fun i => starRingEnd ℂ (y i)) := by
  intro D φ y
  have key : ∀ A : Fin D → Matrix (Fin D) (Fin D) ℂ,
      mixedDisc (fun k => (A k).map (starRingEnd ℂ)) = starRingEnd ℂ (mixedDisc A) := by
    intro A
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [mixedDisc, map_mul, map_div₀, map_one, map_natCast, map_sum, map_pow, map_neg]
    congr 1
    refine Finset.sum_congr rfl fun S _ => ?_
    congr 1
    rw [RingHom.map_det]
    congr 1
    ext a b
    simp [Matrix.sum_apply]
  simp only [maDensity, madens_cx, key, Complex.conj_re]

end PositivityTheory.UnitarySelfGeneration
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.IAlgebra
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

theorem ialg_one {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  have : m = 0 := by
    by_contra h
    rw [mem_support_iff, coeff_one, if_neg (Ne.symm h)] at hm
    exact hm rfl
  simp [this]

theorem ialg_mul {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {f g : MRing ι} {a b : K → ℕ}
    (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.1 (support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m₁ h₁ k, hg m₂ h₂ k]

theorem ialg_rename {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {κ : K → K'}
    {v : (Σ k, ι k) → Σ k, ι' k} (hv : IsBlockMap κ v) {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    IsMultiHomog (rename v f : MRing ι') (Function.extend κ a 0) := by
  classical
  intro m' hm' k'
  rw [support_rename_of_injective hv.2.1] at hm'
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hm'
  by_cases hk : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := hk
    rw [hv.1.extend_apply, ← hf m hm k]
    have hc : ∀ i : ι k, ∃ j : ι' (κ k), v ⟨k, i⟩ = ⟨κ k, j⟩ := by
      intro i
      have h1 := hv.2.2.1 ⟨k, i⟩
      generalize v ⟨k, i⟩ = q at h1
      obtain ⟨k₁, j⟩ := q
      obtain rfl : k₁ = κ k := h1
      exact ⟨j, rfl⟩
    choose e he using hc
    have hb : Function.Bijective e := by
      constructor
      · intro i i' h
        have : v ⟨k, i⟩ = v ⟨k, i'⟩ := by rw [he, he, h]
        exact sigma_mk_injective (β := ι) (hv.2.1 this)
      · intro j
        obtain ⟨⟨k₀, i⟩, hq⟩ := hv.2.2.2 ⟨κ k, j⟩ ⟨k, rfl⟩
        have hk : κ k₀ = κ k := by
          have := hv.2.2.1 ⟨k₀, i⟩
          rw [hq] at this
          exact this.symm
        obtain rfl := hv.1 hk
        exact ⟨i, sigma_mk_injective (β := ι') ((he i).symm.trans hq)⟩
    refine (Fintype.sum_bijective e hb _ _ fun i => ?_).symm
    rw [← he, Finsupp.mapDomain_apply_of_injective hv.2.1]
  · rw [Function.extend_apply' _ _ _ hk]
    refine Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨p, hp⟩
    refine hk ⟨p.1, ?_⟩
    rw [← hv.2.2.1 p, hp]

theorem i_algebra : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)), IsMultiProjPrime P → (∀ a, IsLineIso P a a 1 1) ∧ (∀ a b f g, IsLineIso P a b f g → IsLineIso P b a g f) ∧ (∀ a b c f g f' g', IsLineIso P a b f g → IsLineIso P b c f' g' → IsLineIso P a c (f * f') (g * g')) ∧ (∀ a b a' b' f g f' g', IsLineIso P a b f g → IsLineIso P a' b' f' g' → IsLineIso P (a + a') (b + b') (f * f') (g * g')) ∧ ∀ (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (P' : Ideal (MRing ι')), IsBlockMap κ v → imageZ v P' = P → ∀ a b f g, IsLineIso P a b f g → IsLineIso P' (pullDeg κ a) (pullDeg κ b) (rename v f) (rename v g) := by
  intro K _ ι _ P hP
  have hp : P.IsPrime := hP.1
  have tens : ∀ f g f' g' : MRing ι, UnitRatio P f g → UnitRatio P f' g' → UnitRatio P (f * f') (g * g') := by
    rintro f g f' g' ⟨hf, hg, h⟩ ⟨hf', hg', h'⟩
    refine ⟨fun hh => (hp.mem_or_mem hh).elim hf hf', fun hh => (hp.mem_or_mem hh).elim hg hg',
      fun W hW hPW hr => ?_⟩
    obtain ⟨u, v, hu, hv, huv⟩ := h W hW hPW hr
    obtain ⟨u', v', hu', hv', huv'⟩ := h' W hW hPW hr
    refine ⟨u * u', v * v', fun hh => (hW.mem_or_mem hh).elim hu hu', fun hh => (hW.mem_or_mem hh).elim hv hv', ?_⟩
    have := P.add_mem (P.mul_mem_left (u' * f') huv) (P.mul_mem_left (v * g) huv')
    convert this using 1
    ring
  refine ⟨fun a => ⟨⟨0, 0, ialg_one, ialg_one, by simp⟩, ?_⟩, ?_, ?_, ?_, ?_⟩
  · have h1 : (1 : MRing ι) ∉ P := (Ideal.ne_top_iff_one P).1 hp.ne_top
    exact ⟨h1, h1, fun W hW _ _ => ⟨1, 1, (Ideal.ne_top_iff_one W).1 hW.ne_top,
      (Ideal.ne_top_iff_one W).1 hW.ne_top, by simp⟩⟩
  · rintro a b f g ⟨⟨α, γ, h1, h2, h3⟩, hf, hg, h⟩
    refine ⟨⟨γ, α, h2, h1, fun k => by linarith [h3 k]⟩, hg, hf, fun W hW hPW hr => ?_⟩
    obtain ⟨u, v, hu, hv, huv⟩ := h W hW hPW hr
    exact ⟨v, u, hv, hu, by simpa using P.neg_mem huv⟩
  · rintro a b c f g f' g' ⟨⟨α, γ, h1, h2, h3⟩, h⟩ ⟨⟨α', γ', h1', h2', h3'⟩, h'⟩
    refine ⟨⟨α + α', γ + γ', ialg_mul h1 h1', ialg_mul h2 h2', fun k => ?_⟩, tens _ _ _ _ h h'⟩
    simp only [Pi.add_apply, Nat.cast_add]
    linarith [h3 k, h3' k]
  · rintro a b a' b' f g f' g' ⟨⟨α, γ, h1, h2, h3⟩, h⟩ ⟨⟨α', γ', h1', h2', h3'⟩, h'⟩
    refine ⟨⟨α + α', γ + γ', ialg_mul h1 h1', ialg_mul h2 h2', fun k => ?_⟩, tens _ _ _ _ h h'⟩
    simp only [Pi.add_apply, Nat.cast_add]
    linarith [h3 k, h3' k]
  · rintro K' _ ι' _ κ v P' hv rfl a b f g ⟨⟨α, γ, h1, h2, h3⟩, hf, hg, h⟩
    refine ⟨⟨Function.extend κ α 0, Function.extend κ γ 0, ialg_rename hv h1, ialg_rename hv h2, fun k' => ?_⟩,
      hf, hg, fun W hW hPW hr => ?_⟩
    · unfold pullDeg
      by_cases hk : ∃ k, κ k = k'
      · obtain ⟨k, rfl⟩ := hk
        simp only [hv.1.extend_apply]
        exact h3 k
      · simp only [Function.extend_apply' _ _ _ hk]
        simp
    · have hr' : IsRelevant (imageZ v W) := by
        intro k
        obtain ⟨i, hi⟩ := hr (κ k)
        obtain ⟨⟨k₀, j⟩, hq⟩ := hv.2.2.2 ⟨κ k, i⟩ ⟨k, rfl⟩
        have hk : κ k₀ = κ k := by
          have := hv.2.2.1 ⟨k₀, j⟩
          rw [hq] at this
          exact this.symm
        obtain rfl := hv.1 hk
        refine ⟨j, fun hh => hi ?_⟩
        have : rename v (X ⟨k₀, j⟩ : MRing ι) ∈ W := hh
        rwa [rename_X, hq] at this
      obtain ⟨u, w, hu, hw, huw⟩ := h (imageZ v W) (Ideal.comap_isPrime _ W) (Ideal.comap_mono hPW) hr'
      refine ⟨rename v u, rename v w, hu, hw, ?_⟩
      have : rename v (u * f - w * g) ∈ P' := huw
      simpa using this

end PositivityTheory.UnitarySelfGeneration
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.ICycle
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

theorem icyc_mem {R : Type*} [CommRing R] {P W : Ideal R} (hW : W.IsPrime) (hP : P ≤ W) {f g u v : R}
    (hu : u ∉ W) (h : u * f - v * g ∈ P) (hg : g ∈ W) : f ∈ W := by
  have : u * f ∈ W := by simpa using W.add_mem (hP h) (W.mul_mem_left v hg)
  exact (hW.mem_or_mem this).resolve_left hu

theorem icyc_sub {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (f g : MRing ι)
    (h : ∀ W : Ideal (MRing ι), W.IsPrime → P ≤ W → IsRelevant W →
      ∃ u v : MRing ι, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P)
    (h' : ∀ W : Ideal (MRing ι), W.IsPrime → P ≤ W → IsRelevant W →
      ∃ u v : MRing ι, u ∉ W ∧ v ∉ W ∧ u * g - v * f ∈ P) : divSupp P f ⊆ divSupp P g := by
  rintro W ⟨⟨⟨hWp, hle⟩, hmin⟩, hr⟩
  have hPW : P ≤ W := le_sup_left.trans hle
  have hf : f ∈ W := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  refine ⟨⟨⟨hWp, sup_le hPW ?_⟩, ?_⟩, hr⟩
  · obtain ⟨u, v, hu, -, huv⟩ := h' W hWp hPW hr
    rw [Ideal.span_singleton_le_iff_mem]
    exact icyc_mem hWp hPW hu huv hf
  · rintro W' ⟨hW'p, hle'⟩ hWW
    have hPW' : P ≤ W' := le_sup_left.trans hle'
    have hr' : IsRelevant W' := fun k => (hr k).imp fun i hi hi' => hi (hWW hi')
    obtain ⟨u, v, hu, -, huv⟩ := h W' hW'p hPW' hr'
    refine hmin ⟨hW'p, sup_le hPW' ?_⟩ hWW
    rw [Ideal.span_singleton_le_iff_mem]
    exact icyc_mem hW'p hPW' hu huv (hle' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g)))

theorem icyc_map {R : Type*} [CommRing R] (W : Ideal R) [W.IsPrime] (P : Ideal R) (f g u v : R)
    (hu : u ∉ W) (h : u * f - v * g ∈ P) :
    Ideal.map (algebraMap R (Localization.AtPrime W)) (P ⊔ Ideal.span {f}) ≤
      Ideal.map (algebraMap R (Localization.AtPrime W)) (P ⊔ Ideal.span {g}) := by
  rw [Ideal.map_le_iff_le_comap]
  refine sup_le (le_sup_left.trans Ideal.le_comap_map) ?_
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
  have hU : IsUnit (algebraMap R (Localization.AtPrime W) u) :=
    IsLocalization.map_units (Localization.AtPrime W) (⟨u, hu⟩ : W.primeCompl)
  rw [← Ideal.unit_mul_mem_iff_mem _ hU, ← map_mul]
  apply Ideal.mem_map_of_mem
  have := (P ⊔ Ideal.span {g}).add_mem (Ideal.mem_sup_left h)
    (Ideal.mem_sup_right (Ideal.mul_mem_left _ v (Ideal.mem_span_singleton_self g)))
  simpa using this

theorem icyc_len {R : Type*} [CommRing R] (W : Ideal R) [W.IsPrime] (J : Ideal R) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) =
      Module.length (Localization.AtPrime W)
        (Localization.AtPrime W ⧸ Ideal.map (algebraMap R (Localization.AtPrime W)) J) := by
  refine LinearEquiv.length_eq ?_
  exact ((LocalizedModule.equivTensorProduct W.primeCompl (R ⧸ J)).trans
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime W) J).toLinearEquiv.symm)

theorem i_cycle : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (f g : MRing ι), UnitRatio P f g → divSupp P f = divSupp P g ∧ ∀ W ∈ divSupp P f, multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W := by
  intro K _ ι _ P f g h
  obtain ⟨-, -, h⟩ := h
  have h' : ∀ W : Ideal (MRing ι), W.IsPrime → P ≤ W → IsRelevant W →
      ∃ u v : MRing ι, u ∉ W ∧ v ∉ W ∧ u * g - v * f ∈ P := by
    intro W hW hP hr
    obtain ⟨u, v, hu, hv, huv⟩ := h W hW hP hr
    exact ⟨v, u, hv, hu, by simpa using P.neg_mem huv⟩
  refine ⟨Set.Subset.antisymm (icyc_sub P f g h h') (icyc_sub P g f h' h), fun W hW => ?_⟩
  have hWp : W.IsPrime := hW.1.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.1.2
  obtain ⟨u, v, hu, hv, huv⟩ := h W hWp hPW hW.2
  unfold multAt
  rw [dite_eq_left hWp, dite_eq_left hWp]
  congr 1
  rw [icyc_len, icyc_len]
  have e : Ideal.map (algebraMap (MRing ι) (Localization.AtPrime W)) (P ⊔ Ideal.span {f}) =
      Ideal.map (algebraMap (MRing ι) (Localization.AtPrime W)) (P ⊔ Ideal.span {g}) :=
    le_antisymm (icyc_map W P f g u v hu huv) (icyc_map W P g f v u hv (by simpa using P.neg_mem huv))
  rw [e]

end PositivityTheory.UnitarySelfGeneration
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.IDefect
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

namespace IDef

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

def wt : (Σ k, ι k) → K → ℤ := fun p => Pi.single p.1 1

theorem weight_wt (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (wt (ι := ι)) m k = ((∑ i, m ⟨k, i⟩ : ℕ) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp), Finset.sum_apply, Fintype.sum_sigma,
    Finset.sum_eq_single k]
  · simp [wt]
  · intro b _ hb
    simp [wt, Pi.single_eq_of_ne hb.symm]
  · simp

theorem mem_of_homog {s : MRing ι} {a : K → ℕ} (h : IsMultiHomog s a) :
    s ∈ weightedHomogeneousSubmodule ℤ (wt (ι := ι)) (fun k => (a k : ℤ)) := by
  rw [mem_weightedHomogeneousSubmodule]
  intro d hd
  funext k
  rw [weight_wt, h d (mem_support_iff.mpr hd) k]

theorem evC_smul {s : MRing ι} {d : K → ℤ} (h : s ∈ weightedHomogeneousSubmodule ℤ (wt (ι := ι)) d) (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) : evC (fun p => c p.1 * z p) s = (∏ k, c k ^ d k) * evC z s := by
  rw [mem_weightedHomogeneousSubmodule] at h
  by_cases hs : s = 0
  · simp [hs, evC]
  obtain ⟨m₀, hm₀⟩ := ne_zero_iff.mp hs
  have h1 : ∀ k, d k = ((∑ i, m₀ ⟨k, i⟩ : ℕ) : ℤ) := fun k => by rw [← h hm₀, weight_wt]
  have h2 : IsMultiHomog s fun k => ∑ i, m₀ ⟨k, i⟩ := by
    intro m hm k
    have := weight_wt m k
    rw [h (mem_support_iff.mp hm), h1] at this
    exact_mod_cast this.symm
  simp only [h1, zpow_natCast]
  exact eval_smul_homog s _ h2 c z

theorem homog_ideal {P : Ideal (MRing ι)} (h : IsMultiHomogIdeal P) :
    P.IsHomogeneous (weightedHomogeneousSubmodule ℤ (wt (ι := ι))) := by
  obtain ⟨S, hS, rfl⟩ := h
  refine Ideal.homogeneous_span _ S fun x hx => ?_
  obtain ⟨a, ha⟩ := hS x hx
  exact ⟨_, mem_of_homog ha⟩

theorem exists_homog_pair {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {f g u v : MRing ι} {α γ : K → ℕ}
    (hf : IsMultiHomog f α) (hg : IsMultiHomog g γ) (h : u * f - v * g ∈ P) {z : (Σ k, ι k) → ℂ}
    (hu : evC z u ≠ 0) : ∃ (u' v' : MRing ι) (d : K → ℤ), u' ∈ weightedHomogeneousSubmodule ℤ (wt (ι := ι)) d ∧
      v' ∈ weightedHomogeneousSubmodule ℤ (wt (ι := ι)) (d + (fun k => (α k : ℤ)) - fun k => (γ k : ℤ)) ∧
      u' * f - v' * g ∈ P ∧ evC z u' ≠ 0 := by
  classical
  set 𝒜 := weightedHomogeneousSubmodule ℤ (wt (ι := ι)) with h𝒜
  have h1 : ∃ d, evC z (DirectSum.decompose 𝒜 u d : MRing ι) ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hu
    rw [← DirectSum.sum_support_decompose 𝒜 u]
    unfold evC at hc ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    exact Finset.sum_eq_zero fun d _ => hc d
  obtain ⟨d, hd⟩ := h1
  refine ⟨_, _, d, (DirectSum.decompose 𝒜 u d).2,
    (DirectSum.decompose 𝒜 v (d + (fun k => (α k : ℤ)) - fun k => (γ k : ℤ))).2, ?_, hd⟩
  have h2 := homog_ideal hP (d + fun k => (α k : ℤ)) h
  rw [← DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 (mem_of_homog hf),
    ← DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 (mem_of_homog hg), sub_add_cancel]
  rw [DirectSum.decompose_sub] at h2
  exact h2

omit [DecidableEq K] in
theorem exists_pair {P : Ideal (MRing ι)} {f g : MRing ι} (h : UnitRatio P f g) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts P) : ∃ u v : MRing ι, evC z u ≠ 0 ∧ evC z v ≠ 0 ∧ u * f - v * g ∈ P := by
  let φ : MRing ι →+* ℂ := (eval z).comp (map (Int.castRingHom ℂ))
  exact h.2.2 (RingHom.ker φ) (RingHom.ker_isPrime φ) (fun s hs => hz.2 s hs) fun k => by
    obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, by simpa [φ, RingHom.mem_ker] using hi⟩

omit [DecidableEq K] in
theorem ratio_eq {P : Ideal (MRing ι)} (hP : P.IsPrime) {f g u v u' v' : MRing ι} (hg : g ∉ P)
    (h : u * f - v * g ∈ P) (h' : u' * f - v' * g ∈ P) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P)
    (hu : evC z u ≠ 0) (hu' : evC z u' ≠ 0) : ‖evC z v‖ / ‖evC z u‖ = ‖evC z v'‖ / ‖evC z u'‖ := by
  have h1 : (u * v' - u' * v) * g ∈ P := by
    have := P.sub_mem (P.mul_mem_left u' h) (P.mul_mem_left u h')
    convert this using 1
    ring
  have h2 := hz.2 _ ((hP.mem_or_mem h1).resolve_right hg)
  rw [← norm_div, ← norm_div]
  congr 1
  unfold evC at *
  simp only [map_sub, map_mul] at h2
  field_simp
  linear_combination -h2

end IDef

open IDef HolomorphicMinorCharts in
theorem i_defect : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e) (A B : HermLine ι) (f g : MRing ι), IsMultiProjPrime P → IsLineIso P A.a B.a f g → IsSmoothHerm A → IsSmoothHerm B → ∃ w : ((Σ k, ι k) → ℂ) → ℝ, IsDefectOn P (mcPts P) f g A B w ∧ (∀ z ∈ mcPts P, ∀ z', SameOrbit z z' → w z = w z') ∧ R.A.Smooth (fun x => w (R.lift x x)) := by
  intro K _ ι _ P J e R A B f g hP hI hA hB
  classical
  obtain ⟨⟨α, γ, hf, hg, hdeg⟩, hU⟩ := hI
  let w : ((Σ k, ι k) → ℂ) → ℝ := fun z =>
    if h : ∃ q : MRing ι × MRing ι, q.1 * f - q.2 * g ∈ P ∧ evC z q.1 ≠ 0 then
      Real.log (‖evC z h.choose.2‖ / ‖evC z h.choose.1‖ * B.h z / A.h z) else 0
  have hw : IsDefectOn P (mcPts P) f g A B w := by
    intro z hz u v h hu
    have hex : ∃ q : MRing ι × MRing ι, q.1 * f - q.2 * g ∈ P ∧ evC z q.1 ≠ 0 := ⟨(u, v), h, hu⟩
    simp only [w, dif_pos hex]
    rw [ratio_eq hP.1 hU.2.1 hex.choose_spec.1 h hz hex.choose_spec.2 hu]
  have hinv : ∀ z ∈ mcPts P, ∀ z', SameOrbit z z' → w z = w z' := by
    intro z hz z' hzz
    have hz' : z' ∈ mcPts P := mem_mcPts_of_sameOrbit hP.2.1 (so_symm hzz) hz
    obtain ⟨u₀, v₀, hu₀, -, h₀⟩ := exists_pair hU hz'
    obtain ⟨u, v, d, hu, hv, h, hu'⟩ := exists_homog_pair hP.2.1 hf hg h₀ hu₀
    obtain ⟨c, hc, rfl⟩ := hzz
    have hn : ∀ n : K → ℤ, (∏ k, c k ^ n k) ≠ 0 := fun n => Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
    have hn' : ∀ n : K → ℤ, (∏ k, ‖c k‖ ^ n k) ≠ 0 := fun n =>
      Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
    rw [hw _ hz u v h (by rw [evC_smul hu]; exact mul_ne_zero (hn d) hu'), hw _ hz' u v h hu', evC_smul hu, evC_smul hv,
      A.smul c z' hc, B.smul c z' hc]
    congr 1
    simp only [norm_mul, norm_prod, norm_zpow]
    have key : (∏ k, ‖c k‖ ^ (d + (fun k => (α k : ℤ)) - fun k => (γ k : ℤ)) k) * ∏ k, ‖c k‖ ^ B.a k =
        (∏ k, ‖c k‖ ^ d k) * ∏ k, ‖c k‖ ^ A.a k := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_add₀ (norm_ne_zero_iff.mpr (hc k)), ← zpow_add₀ (norm_ne_zero_iff.mpr (hc k))]
      congr 1
      have := hdeg k
      simp only [Pi.sub_apply, Pi.add_apply]
      linarith
    have h1 := hn' d
    have h2 := hn' A.a
    have h3 := (A.pos z' hz'.1).ne'
    have h4 := norm_ne_zero_iff.mpr hu'
    field_simp
    linear_combination ‖evC z' v‖ * B.h z' * key
  refine ⟨w, hw, hinv, fun j y hy => ContDiffAt.contDiffWithinAt ?_⟩
  set x := (R.A.chart j).symm y with hx
  have hO := ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds ⟨hy.1, R.mem_U x⟩
  have hz := R.mem x x (R.mem_U x)
  obtain ⟨u, v, hu, hv, h⟩ := exists_pair hU hz
  have hl : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => R.lift x ((R.A.chart j).symm y)) y :=
    (contDiffOn_lift R x j).contDiffAt hO
  have hev : ∀ s : MRing ι, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => evC (R.lift x ((R.A.chart j).symm y)) s) y := fun s =>
    ContDiffAt.comp (g := fun z => evC z s) y
      (((AnalyticOnNhd.eval_mvPolynomial (map (Int.castRingHom ℂ) s)) _ trivial).contDiffAt.restrict_scalars ℝ) hl
  have hNZ : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    rw [Set.setOf_forall]
    refine isOpen_iInter_of_finite fun k => ?_
    rw [Set.setOf_exists]
    exact isOpen_iUnion fun i => isOpen_ne_fun (continuous_apply _) continuous_const
  have hh : ∀ C : HermLine ι, IsSmoothHerm C → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => C.h (R.lift x ((R.A.chart j).symm y))) y := fun C hC =>
    ContDiffAt.comp (g := C.h) y (ContDiffOn.contDiffAt hC (hNZ.mem_nhds hz.1)) hl
  have hA0 := (A.pos _ hz.1).ne'
  have hB0 := (B.pos _ hz.1).ne'
  have hu0 := norm_ne_zero_iff.mpr hu
  have hv0 := norm_ne_zero_iff.mpr hv
  refine ContDiffAt.congr_of_eventuallyEq
    ((((((hev v).norm ℂ hv).div ((hev u).norm ℂ hu) hu0).mul (hh B hB)).div (hh A hA) hA0).log
      (div_ne_zero (mul_ne_zero (div_ne_zero hv0 hu0) hB0) hA0)) ?_
  filter_upwards [hO, (hev u).continuousAt.eventually_ne hu] with y' h1 h2
  simp only [Function.comp_apply]
  rw [hinv _ (R.mem _ _ (R.mem_U _)) _ (R.compat _ x _ ⟨R.mem_U _, h1.2⟩)]
  exact hw _ (R.mem x _ h1.2) u v h h2

end PositivityTheory.UnitarySelfGeneration
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Imports
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem tw_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : HostAut H), Nonempty (TwIso D g) := by
  intro E _ _ _ H D g
  have := D.fin
  have := D.proj
  obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.CompanionTheory.Ar.TwModule.twMod_finite_projective_finrank (𝓞 E) g.s D.La
  have := finite_int_of_finite_ringOfIntegers E D.La
  have := finite_int_of_finite_ringOfIntegers E (TwMod g.s D.La)
  have := free_int_of_projective_ringOfIntegers E D.La
  have := free_int_of_projective_ringOfIntegers E (TwMod g.s D.La)
  refine _root_.GlobalTheory.CompanionTheory.Ar.ProIso.nonempty_of_forall_prime (𝓞 E) D.La (TwMod g.s D.La) D.EF (twForm D g) fun p hp => ?_
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨φ, k1, k2⟩ := tw_g_padic E H.bar H.bar_eq H.unram p D.La (TwMod g.s D.La) D.EF (twForm D g) h3.symm D.alt
    D.unimod D.adj D.alt D.unimod fun a x y => (D.adj (g.s a) x y).trans (by rw [← g.s_bar]; rfl)
  exact _root_.GlobalTheory.CompanionTheory.Ar.proIsoAt_of_padic_isometry p (𝓞 E) D.La (TwMod g.s D.La) D.EF (twForm D g) φ k1 k2

end PositivityTheory.UnitarySelfGeneration
end

