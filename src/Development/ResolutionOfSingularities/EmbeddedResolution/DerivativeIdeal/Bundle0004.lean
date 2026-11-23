module

public import Mathlib
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.Bundle0002
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.Bundle0003
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativesInBlowupCharts
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdealSheaf
section
universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

theorem map_logDerivIdeal_basicOpen (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P I : X.IdealSheafData) :
    ∀ (U : X.affineOpens) (f : Γ(X, U.1)),
      Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
          (@logDerivIdeal k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) (I.ideal U)) =
        @logDerivIdeal k _ _ _ (sectionsAlgebra k p (X.affineBasicOpen f).1)
          (P.ideal (X.affineBasicOpen f)) (I.ideal (X.affineBasicOpen f)) := by
  intro U f
  have hUaff : IsAffineOpen U.1 := U.2
  let algU : Algebra k Γ(X, U.1) := sectionsAlgebra k p U.1
  let algV : Algebra k Γ(X, X.basicOpen f) := sectionsAlgebra k p (X.basicOpen f)
  let algUV : Algebra Γ(X, U.1) Γ(X, X.basicOpen f) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
  have tower : IsScalarTower k Γ(X, U.1) Γ(X, X.basicOpen f) :=
    isScalarTower_sections k p U.1 f rfl rfl rfl
  have loc : IsLocalization.Away f Γ(X, X.basicOpen f) := hUaff.isLocalization_basicOpen f
  have fp : Module.FinitePresentation Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1)) :=
    finitePresentation_kaehlerDifferential_sections k p U rfl
  have noeth : IsNoetherianRing Γ(X, U.1) := isNoetherianRing_sections k p U rfl
  have hP : (P.ideal U).FG := IsNoetherian.noetherian _
  have key := logDerivIdeal_map_away (S' := Γ(X, X.basicOpen f)) k f hP (I.ideal U)
  rw [← P.map_ideal_basicOpen U f, ← I.map_ideal_basicOpen U f]
  exact key

noncomputable def logDerivIdealSheaf (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P I : X.IdealSheafData) : X.IdealSheafData where
  ideal U := @logDerivIdeal k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) (I.ideal U)
  map_ideal_basicOpen := map_logDerivIdeal_basicOpen k p P I

@[simp] theorem logDerivIdealSheaf_ideal (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P I : X.IdealSheafData) (U : X.affineOpens) :
    (logDerivIdealSheaf k p P I).ideal U =
      @logDerivIdeal k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) (I.ideal U) :=
  rfl

theorem logDerivIdealSheaf_mono (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (P : X.IdealSheafData) :
    Monotone (logDerivIdealSheaf k p P) := by
  intro I J h U
  exact @logDerivIdeal_le_logDerivIdeal k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U)
    (I.ideal U) (J.ideal U) (h U)

theorem logDerivIdealSheaf_le_derivIdealSheaf (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P I : X.IdealSheafData) :
    logDerivIdealSheaf k p P I ≤ derivIdealSheaf k p I := by
  intro U
  exact @logDerivIdeal_le_derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) (I.ideal U)

noncomputable def logDerivIdealSheafIterate (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P : X.IdealSheafData) : ℕ → X.IdealSheafData → X.IdealSheafData
  | 0, I => I
  | (r + 1), I => logDerivIdealSheaf k p P (logDerivIdealSheafIterate k p P r I)

@[simp] theorem logDerivIdealSheafIterate_zero (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P I : X.IdealSheafData) : logDerivIdealSheafIterate k p P 0 I = I :=
  rfl

theorem logDerivIdealSheafIterate_succ (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P : X.IdealSheafData) (r : ℕ) (I : X.IdealSheafData) :
    logDerivIdealSheafIterate k p P (r + 1) I =
      logDerivIdealSheaf k p P (logDerivIdealSheafIterate k p P r I) :=
  rfl

theorem logDerivIdealSheafIterate_add (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P : X.IdealSheafData) (r s : ℕ) (I : X.IdealSheafData) :
    logDerivIdealSheafIterate k p P (r + s) I =
      logDerivIdealSheafIterate k p P r (logDerivIdealSheafIterate k p P s I) := by
  induction r with
  | zero =>
      rw [Nat.zero_add, logDerivIdealSheafIterate_zero]
  | succ r ih =>
      have hrs : r + 1 + s = (r + s) + 1 := by omega
      rw [hrs, logDerivIdealSheafIterate_succ, logDerivIdealSheafIterate_succ, ih]

@[simp] theorem logDerivIdealSheafIterate_ideal (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P : X.IdealSheafData) (r : ℕ) (I : X.IdealSheafData) (U : X.affineOpens) :
    (logDerivIdealSheafIterate k p P r I).ideal U =
      @logDerivIdealIterate k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) r (I.ideal U) := by
  induction r with
  | zero =>
      rw [logDerivIdealSheafIterate_zero,
        @logDerivIdealIterate_zero k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) (I.ideal U)]
  | succ r ih =>
      rw [logDerivIdealSheafIterate_succ, logDerivIdealSheaf_ideal, ih,
        @logDerivIdealIterate_succ k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) r (I.ideal U)]

theorem logDerivIdealSheafIterate_mono (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P : X.IdealSheafData) (r : ℕ) :
    Monotone (logDerivIdealSheafIterate k p P r) := by
  induction r with
  | zero =>
      intro I J h
      rw [logDerivIdealSheafIterate_zero, logDerivIdealSheafIterate_zero]
      exact h
  | succ r ih =>
      intro I J h
      rw [logDerivIdealSheafIterate_succ, logDerivIdealSheafIterate_succ]
      exact logDerivIdealSheaf_mono k p P (ih h)

theorem logDerivIdealSheafIterate_le_derivIdealSheafIterate (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P : X.IdealSheafData) (r : ℕ) (I : X.IdealSheafData) :
    logDerivIdealSheafIterate k p P r I ≤ derivIdealSheafIterate k p r I := by
  induction r with
  | zero =>
      exact le_of_eq
        ((logDerivIdealSheafIterate_zero k p P I).trans (derivIdealSheafIterate_zero k p I).symm)
  | succ r ih =>
      rw [logDerivIdealSheafIterate_succ, derivIdealSheafIterate_succ]
      exact le_trans
        (logDerivIdealSheaf_le_derivIdealSheaf k p P (logDerivIdealSheafIterate k p P r I))
        (derivIdealSheaf_mono k p ih)

end FunctorialResolution.EmbeddedResolution
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativesInBlowupCharts
section
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

private theorem finset_sum_derivation_apply {R : Type*} [CommRing R] {A : Type*} [CommRing A]
    [Algebra R A] {μ : Type*} (u : Finset μ) (D : μ → Derivation R A A) (x : A) :
    (∑ j ∈ u, D j) x = ∑ j ∈ u, (D j) x := by
  classical
  refine Finset.induction_on u ?_ ?_
  · simp
  · intro b t hb ih
    rw [Finset.sum_insert hb, Finset.sum_insert hb, ← ih]
    simp

private theorem smul_derivation_apply {R : Type*} [CommRing R] {A : Type*} [CommRing A]
    [Algebra R A] (a : A) (D : Derivation R A A) (x : A) : (a • D) x = a * D x := by
  simp

variable (k : Type*) [CommRing k] (ι : Type*) [DecidableEq ι]
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
  (S₁ : Type*) [CommRing S₁] [Algebra k S₁] [Algebra (MvPolynomial ι k) S₁]
  [IsScalarTower k (MvPolynomial ι k) S₁] [Algebra.FormallyEtale (MvPolynomial ι k) S₁]
  (φ : S →ₐ[k] S₁) (T : Finset ι) (s : ι)

theorem partialDeriv_mem_sup_of_span_pow_mul_eq_map
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁)
    (i : ι) (hiT : i ∈ T) (his : i ≠ s)
    (J : Ideal S) (L L' : Ideal S₁) (c : ℕ)
    (hJ : Ideal.span {coord k ι S₁ s ^ (c + 1)} * L = Ideal.map φ J)
    (hD : Ideal.map φ (derivIdeal k J) ≤ Ideal.span {coord k ι S₁ s ^ c} * L')
    (g : S₁) (hg : g ∈ L) :
    partialDeriv k ι S₁ i g ∈ L ⊔ L' := by
  have hmapspan : Ideal.span (⇑φ '' (J : Set S)) = Ideal.map φ J := by
    rw [← Ideal.map_span, Ideal.span_eq]
  have hgen : ∀ x ∈ (⇑φ '' (J : Set S)),
      partialDeriv k ι S₁ i x ∈ Ideal.span {coord k ι S₁ s ^ (c + 1)} * (L ⊔ L') := by
    rintro _ ⟨f, hf, rfl⟩
    have h1 : partialDeriv k ι S₁ i (φ f)
        = coord k ι S₁ s * φ (partialDeriv k ι S i f) :=
      partialDeriv_map_of_mem k ι S S₁ φ T s hin hs hout i hiT his f
    have h2 : φ (partialDeriv k ι S i f) ∈ Ideal.map φ (derivIdeal k J) :=
      Ideal.mem_map_of_mem φ
        (derivation_apply_mem_derivIdeal k J (partialDeriv k ι S i) (SetLike.mem_coe.mp hf))
    obtain ⟨z, hz, hzeq⟩ := Ideal.mem_span_singleton_mul.mp (hD h2)
    rw [h1, ← hzeq]
    exact Ideal.mem_span_singleton_mul.mpr ⟨z, Submodule.mem_sup_right hz, by ring⟩
  have hGT : Ideal.span (⇑φ '' (J : Set S))
      ≤ Ideal.span {coord k ι S₁ s ^ (c + 1)} * (L ⊔ L') := by
    rw [hmapspan, ← hJ]
    exact Ideal.mul_mono_right le_sup_left
  have hmem : coord k ι S₁ s ^ (c + 1) * g ∈ Ideal.span (⇑φ '' (J : Set S)) := by
    rw [hmapspan, ← hJ]
    exact Ideal.mem_span_singleton_mul.mpr ⟨g, hg, rfl⟩
  have key := derivation_apply_mem_of_mem_span (partialDeriv k ι S₁ i) hGT hgen hmem
  have hDy : partialDeriv k ι S₁ i (coord k ι S₁ s) = 0 :=
    partialDeriv_coord_of_ne k ι S₁ i s his
  have hDypow : partialDeriv k ι S₁ i (coord k ι S₁ s ^ (c + 1)) = 0 := by
    rw [Derivation.leibniz_pow, hDy, smul_zero, smul_zero]
  have hexp : partialDeriv k ι S₁ i (coord k ι S₁ s ^ (c + 1) * g)
      = coord k ι S₁ s ^ (c + 1) * partialDeriv k ι S₁ i g := by
    rw [Derivation.leibniz, hDypow, smul_zero, add_zero, smul_eq_mul]
  rw [hexp] at key
  obtain ⟨w, hw, hweq⟩ := Ideal.mem_span_singleton_mul.mp key
  have hnz : coord k ι S₁ s ^ (c + 1) ∈ nonZeroDivisors S₁ := pow_mem hnzd (c + 1)
  have h0 : (partialDeriv k ι S₁ i g - w) * coord k ι S₁ s ^ (c + 1) = 0 := by
    linear_combination -hweq
  have h1 : partialDeriv k ι S₁ i g - w = 0 :=
    (mem_nonZeroDivisors_iff.mp hnz).2 _ h0
  have h2 : partialDeriv k ι S₁ i g = w := sub_eq_zero.mp h1
  rw [h2]
  exact hw

theorem map_logDerivIdeal_le_span_pow_mul [Fintype ι]
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hsT : s ∈ T) (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁)
    (i : ι) (hiT : i ∈ T) (his : i ≠ s)
    (J : Ideal S) (J₁ : Ideal S₁) (m : ℕ) (hm : 1 ≤ m)
    (hJ : Ideal.map φ J ≤ Ideal.span {coord k ι S₁ s ^ m} * J₁) :
    Ideal.map φ (logDerivIdeal k (Ideal.span {coord k ι S i}) J)
      ≤ Ideal.span {coord k ι S₁ s ^ (m - 1)}
          * logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ := by
  obtain ⟨e, rfl⟩ : ∃ e, m = e + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hJmem : ∀ f ∈ J, ∃ f₁ ∈ J₁, φ f = coord k ι S₁ s ^ (e + 1) * f₁ := by
    intro f hf
    obtain ⟨f₁, hf₁, hfe⟩ := Ideal.mem_span_singleton_mul.mp (hJ (Ideal.mem_map_of_mem φ hf))
    exact ⟨f₁, hf₁, hfe.symm⟩
  have htan : ∀ j : ι, j ≠ i →
      partialDeriv k ι S₁ j ∈ tangentDerivations k (Ideal.span {coord k ι S₁ i}) := by
    intro j hj
    rw [mem_tangentDerivations_span_singleton]
    rw [partialDeriv_coord_of_ne k ι S₁ j i hj]
    exact Submodule.zero_mem _
  have htanmul : (coord k ι S₁ i) • partialDeriv k ι S₁ i
      ∈ tangentDerivations k (Ideal.span {coord k ι S₁ i}) :=
    smul_mem_tangentDerivations k (Ideal.span {coord k ι S₁ i})
      (Ideal.subset_span (Set.mem_singleton _)) (partialDeriv k ι S₁ i)
  rw [Ideal.map_le_iff_le_comap, logDerivIdeal_le_iff]
  refine ⟨?_, ?_⟩
  · intro f hf
    rw [Ideal.mem_comap]
    obtain ⟨f₁, hf₁, hfe⟩ := hJmem f hf
    refine Ideal.mem_span_singleton_mul.mpr ⟨coord k ι S₁ s * f₁, ?_, ?_⟩
    · exact le_logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ (J₁.mul_mem_left _ hf₁)
    · rw [hfe]; ring
  · intro D hD f hf
    rw [Ideal.mem_comap]
    obtain ⟨f₁, hf₁, hfe⟩ := hJmem f hf
    have hpd : ∀ j : ι, j ≠ i →
        partialDeriv k ι S₁ j f₁ ∈ logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ := by
      intro j hj
      exact derivation_apply_mem_logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁
        (partialDeriv k ι S₁ j) (htan j hj) hf₁
    have hpdi : coord k ι S₁ i * partialDeriv k ι S₁ i f₁
        ∈ logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ := by
      have h := derivation_apply_mem_logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁
        ((coord k ι S₁ i) • partialDeriv k ι S₁ i) htanmul hf₁
      rwa [smul_derivation_apply] at h
    have hDi : D (coord k ι S i) ∈ Ideal.span {coord k ι S i} :=
      (mem_tangentDerivations_span_singleton k (coord k ι S i) D).mp hD
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hDi
    have hDf : φ (D f) = ∑ j : ι, φ (D (coord k ι S j)) * φ (partialDeriv k ι S j f) := by
      have h0 : D f = ∑ j : ι, D (coord k ι S j) * partialDeriv k ι S j f := by
        conv_lhs => rw [eq_sum_smul_partialDeriv k ι S D]
        rw [finset_sum_derivation_apply]
        exact Finset.sum_congr rfl (fun j _ => smul_derivation_apply _ _ _)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h0, map_sum]
      exact Finset.sum_congr rfl (fun j _ => map_mul φ _ _)
    rw [hDf]
    refine Ideal.sum_mem _ ?_
    intro j _
    by_cases hji : j = i
    · rw [hji]
      have h1 : φ (partialDeriv k ι S i f)
          = coord k ι S₁ s ^ e * partialDeriv k ι S₁ i f₁ :=
        map_partialDeriv_eq_pow_mul_of_mem k ι S S₁ φ T s hin hs hout hnzd i hiT his f f₁ e hfe
      have h2 : φ (D (coord k ι S i)) = φ a * (coord k ι S₁ i * coord k ι S₁ s) := by
        rw [← ha, map_mul, hin i hiT his]
      rw [h1, h2]
      exact Ideal.mem_span_singleton_mul.mpr
        ⟨φ a * coord k ι S₁ s * (coord k ι S₁ i * partialDeriv k ι S₁ i f₁),
          Ideal.mul_mem_left _ _ hpdi, by ring⟩
    · have hkey : φ (partialDeriv k ι S j f)
          ∈ Ideal.span {coord k ι S₁ s ^ e}
              * logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ := by
        by_cases hjT : j ∈ T
        · by_cases hjs : j = s
          · rw [hjs]
            have h1 := map_partialDeriv_self_eq_pow_mul k ι S S₁ φ T s hin hs hout hsT hnzd f f₁ e hfe
            have hbr : coord k ι S₁ s * partialDeriv k ι S₁ s f₁ + ((e + 1 : ℕ) : S₁) * f₁
                - ∑ l ∈ T.erase s, coord k ι S₁ l * partialDeriv k ι S₁ l f₁
                ∈ logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ := by
              refine Ideal.sub_mem _ (Ideal.add_mem _ ?_ ?_) ?_
              · exact Ideal.mul_mem_left _ _ (hpd s his.symm)
              · exact Ideal.mul_mem_left _ _
                  (le_logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ hf₁)
              · refine Ideal.sum_mem _ ?_
                intro l _
                by_cases hli : l = i
                · rw [hli]; exact hpdi
                · exact Ideal.mul_mem_left _ _ (hpd l hli)
            rw [h1]
            exact Ideal.mem_span_singleton_mul.mpr ⟨_, hbr, rfl⟩
          · have h1 :=
              map_partialDeriv_eq_pow_mul_of_mem k ι S S₁ φ T s hin hs hout hnzd j hjT hjs f f₁ e hfe
            rw [h1]
            exact Ideal.mem_span_singleton_mul.mpr ⟨_, hpd j hji, rfl⟩
        · have h1 :=
            map_partialDeriv_eq_pow_mul_of_notMem k ι S S₁ φ T s hin hs hout hsT j hjT f f₁ e hfe
          rw [h1]
          exact Ideal.mem_span_singleton_mul.mpr
            ⟨coord k ι S₁ s * partialDeriv k ι S₁ j f₁,
              Ideal.mul_mem_left _ _ (hpd j hji), by ring⟩
      exact Ideal.mul_mem_left _ _ hkey

theorem map_logDerivIdealIterate_le_span_pow_mul [Fintype ι]
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hsT : s ∈ T) (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁)
    (i : ι) (hiT : i ∈ T) (his : i ≠ s)
    (J : Ideal S) (J₁ : Ideal S₁) (m : ℕ)
    (hJ : Ideal.map φ J ≤ Ideal.span {coord k ι S₁ s ^ m} * J₁)
    (j : ℕ) (hj : j ≤ m) :
    Ideal.map φ (logDerivIdealIterate k (Ideal.span {coord k ι S i}) j J)
      ≤ Ideal.span {coord k ι S₁ s ^ (m - j)}
          * logDerivIdealIterate k (Ideal.span {coord k ι S₁ i}) j J₁ := by
  revert hj
  induction j with
  | zero =>
      intro _
      rw [logDerivIdealIterate_zero, logDerivIdealIterate_zero, Nat.sub_zero]
      exact hJ
  | succ j ih =>
      intro hj
      have h1 := ih (Nat.le_of_succ_le hj)
      have h2 := map_logDerivIdeal_le_span_pow_mul k ι S S₁ φ T s hin hs hout hsT hnzd i hiT his
        (logDerivIdealIterate k (Ideal.span {coord k ι S i}) j J)
        (logDerivIdealIterate k (Ideal.span {coord k ι S₁ i}) j J₁) (m - j) (by omega) h1
      rw [logDerivIdealIterate_succ, logDerivIdealIterate_succ]
      have hsub : m - j - 1 = m - (j + 1) := by omega
      rwa [hsub] at h2

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end

