module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0016
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.AlgebraicIndependentLinearForms
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg.LinKer

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg

theorem algebraicIndependent_linearForms {F E : Type} [Field F] [Field E] [Algebra F E]
    {D κ : Type} [Fintype D] [Fintype κ] (u : D → E) (hu : AlgebraicIndependent F u)
    (v : κ → D → F) (hv : LinearIndependent F v) :
    AlgebraicIndependent F fun i => ∑ c, algebraMap F E (v i c) * u c := by
  classical
  obtain ⟨T, hT⟩ := LinearMap.exists_leftInverse_of_injective (Fintype.linearCombination F v)
    (LinearMap.ker_eq_bot.2 hv.fintypeLinearCombination_injective)
  have hTv : ∀ i, T (v i) = Pi.single i 1 := by
    intro i
    have := LinearMap.congr_fun hT (Pi.single i 1)
    simpa [Fintype.linearCombination_apply_single] using this
  have hdual : ∀ i j, ∑ c, v i c * T (Pi.single c 1) j = (Pi.single i 1 : κ → F) j := by
    intro i j
    have hvi : v i = ∑ c, v i c • (Pi.single c 1 : D → F) := by
      ext d
      simp [Finset.sum_apply, Pi.single_apply]
    rw [← hTv i]
    conv_rhs => rw [hvi]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, Finset.sum_apply]
  let A : MvPolynomial κ F →ₐ[F] MvPolynomial D F :=
    aeval fun i => ∑ c, MvPolynomial.C (v i c) * MvPolynomial.X c
  let B : MvPolynomial D F →ₐ[F] MvPolynomial κ F :=
    aeval fun c => ∑ j, MvPolynomial.C (T (Pi.single c 1) j) * MvPolynomial.X j
  have hBA : B.comp A = AlgHom.id F _ := by
    apply MvPolynomial.algHom_ext
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [A, B, AlgHom.comp_apply, aeval_X, map_sum, map_mul, algHom_C, AlgHom.id_apply,
      algebraMap_eq, Finset.mul_sum]
    rw [Finset.sum_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← mul_assoc, ← MvPolynomial.C_mul, ← Finset.sum_mul, ← map_sum, hdual]
    simp [Pi.single_apply, ite_mul]
  have hA : Function.Injective A := by
    intro f g h
    have := congrArg B h
    have e : ∀ f, B (A f) = f := fun f => by
      simpa using DFunLike.congr_fun hBA f
    rwa [e, e] at this
  have hcomp : (aeval fun i => ∑ c, algebraMap F E (v i c) * u c : MvPolynomial κ F →ₐ[F] E) =
      (aeval u).comp A := by
    apply MvPolynomial.algHom_ext
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [A, map_sum, aeval_X, algHom_C]
  have : Function.Injective (aeval fun i => ∑ c, algebraMap F E (v i c) * u c :
      MvPolynomial κ F →ₐ[F] E) := by
    rw [hcomp]
    exact Function.Injective.comp (f := A) hu hA
  exact this

theorem ker_eq_span_homogeneous {F E : Type} [Field F] [Field E] [Algebra F E]
    {P D : Type} [Fintype P] [Fintype D] (u : D → E) (hu : AlgebraicIndependent F u)
    (l : P → D → F) :
    RingHom.ker (aeval (fun p => ∑ c, algebraMap F E (l p c) * u c) : MvPolynomial P F →ₐ[F] E) =
      Ideal.span {f : MvPolynomial P F | f.IsHomogeneous 1 ∧
        aeval (fun p => ∑ c, algebraMap F E (l p c) * u c) f = 0} := by
  classical
  set x : P → E := fun p => ∑ c, algebraMap F E (l p c) * u c with hx
  set S : Set (MvPolynomial P F) := {f | f.IsHomogeneous 1 ∧ aeval x f = 0} with hS
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' F l
  haveI : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  have hc : ∀ p, ∃ c : κ → F, ∑ i, c i • l (a i) = l p := by
    intro p
    have hp : l p ∈ Submodule.span F (Set.range (l ∘ a)) := by
      rw [hspan]
      exact Submodule.subset_span ⟨p, rfl⟩
    simpa using (Submodule.mem_span_range_iff_exists_fun F).1 hp
  choose c hc using hc
  let ρ' : MvPolynomial P F →ₐ[F] MvPolynomial κ F :=
    aeval fun p => ∑ i, MvPolynomial.C (c p i) * MvPolynomial.X i
  let ρ : MvPolynomial P F →ₐ[F] MvPolynomial P F := (rename a).comp ρ'
  have hρX : ∀ p, ρ (MvPolynomial.X p) = ∑ i, MvPolynomial.C (c p i) * MvPolynomial.X (a i) := by
    intro p
    set_option synthInstance.maxHeartbeats 100000 in
      simp [ρ, ρ', map_sum, aeval_X, rename_C, rename_X]
  have hxp : ∀ p, x p = ∑ i, algebraMap F E (c p i) * x (a i) := by
    intro p
    simp only [hx, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    have : l p d = ∑ i, c p i * l (a i) d := by
      rw [← hc p]
      simp [Finset.sum_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, mul_assoc]
  have hmem : ∀ p, MvPolynomial.X p - ρ (MvPolynomial.X p) ∈ S := by
    intro p
    refine ⟨?_, ?_⟩
    · rw [hρX]
      exact (isHomogeneous_X F p).sub
        (IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X (c p i) (a i))
    · rw [hρX]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sub, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq]
      simpa [sub_eq_zero] using hxp p
  have hle : Ideal.span S ≤ RingHom.ker (aeval x : MvPolynomial P F →ₐ[F] E) := by
    rw [Ideal.span_le]
    intro f hf
    exact hf.2
  have hq : (Ideal.Quotient.mkₐ F (Ideal.span S)).comp ρ = Ideal.Quotient.mkₐ F (Ideal.span S) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    exact (Ideal.Quotient.eq.2 (Ideal.subset_span (hmem p))).symm
  have hdiff : ∀ f, f - ρ f ∈ Ideal.span S := by
    intro f
    have := DFunLike.congr_fun hq f
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
    exact Ideal.Quotient.eq.1 this.symm
  refine le_antisymm ?_ hle
  intro f hf
  have hf0 : aeval x f = 0 := hf
  have h1 : aeval x (ρ f) = 0 := by
    have := hle (hdiff f)
    have h2 : aeval x (f - ρ f) = 0 := this
    rw [map_sub, hf0, zero_sub, neg_eq_zero] at h2
    exact h2
  have hind : AlgebraicIndependent F (x ∘ a) :=
    algebraicIndependent_linearForms u hu (l ∘ a) hli
  have h2 : ρ' f = 0 := by
    apply hind
    rw [map_zero, ← h1]
    simp [ρ, aeval_rename]
  have h3 : ρ f = 0 := by simp [ρ, h2]
  simpa [h3] using hdiff f

theorem ker_linearForms_span : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (K : Type) [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (k₀ : K), (∀ a : K, a = k₀) → ∀ (C : Type) [Fintype C]
    (u : C → E) (l : (Σ k, ι k) → C → F), AlgebraicIndependent F u →
    ∃ S : Set (MRingOver F ι), (∀ f ∈ S, IsMultiHomog f fun _ => 1) ∧
      RingHom.ker (aeval (fun p => ∑ c, algebraMap F E (l p c) * u c) : MRingOver F ι →ₐ[F] E) =
        Ideal.span S := by
  intro F E _ _ _ K _ ι _ k₀ hk C _ u l hu
  refine ⟨_, ?_, ker_eq_span_homogeneous u hu l⟩
  rintro f ⟨hf, -⟩ m hm k
  have hd : ∑ p : (Σ k, ι k), m p = 1 := by
    have h : Finsupp.degree m = 1 := by
      rw [Finsupp.degree_eq_weight_one]
      exact hf (mem_support_iff.1 hm)
    rw [← h, Finsupp.degree_apply]
    exact (Finset.sum_subset (Finset.subset_univ _)
      fun p _ hp => by simpa using hp).symm
  rw [Fintype.sum_sigma] at hd
  have hk' : ∀ j : K, j = k := fun j => (hk j).trans (hk k).symm
  rw [Fintype.sum_eq_single k (fun j hj => absurd (hk' j) hj)] at hd
  exact hd

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg.LinKer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FiniteVerticalRecursion
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.RecSplit

section SlopeTestRemainingChoices

variable {K : Type} {ι : K → Type}

theorem intNumL_ofFn [DecidableEq K] (F : Type) [Field F] (Q : Ideal (MRing ι F)) {n : ℕ}
    (b : Fin n → K → ℤ) : intNumL F Q (List.ofFn b) = intNum F Q b := by
  unfold intNumL intNum mixedDiff
  rw [List.ofFn_get]

theorem exists_prime_mem (W : Ideal (MRing ι ℤ)) (hW : W.IsPrime) (h : ¬ IsHorizontal W) :
    ∃ p : Nat.Primes, (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W := by
  set J : Ideal ℤ := W.comap (C : ℤ →+* MRing ι ℤ) with hJ
  have hJp : J.IsPrime := Ideal.comap_isPrime _ _
  have hJ0 : J ≠ ⊥ := h
  obtain ⟨g, hg⟩ : ∃ g : ℤ, J = Ideal.span {g} := ⟨_, (Ideal.span_singleton_generator J).symm⟩
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hJ0 (by simpa using hg)
  have hgp : Prime g := (Ideal.span_singleton_prime hg0).1 (hg ▸ hJp)
  refine ⟨⟨g.natAbs, Int.prime_iff_natAbs_prime.1 hgp⟩, ?_⟩
  have : ((g.natAbs : ℕ) : ℤ) ∈ J := by
    rw [hg]
    exact Ideal.mem_span_singleton.2 (Int.dvd_natAbs.2 dvd_rfl)
  exact this

variable [Fintype K] [∀ k, Fintype (ι k)]

theorem divCycle_eq_zero_of_not_mem (P : Ideal (MRing ι ℤ)) (s : MRing ι ℤ) (W : Ideal (MRing ι ℤ))
    (h : W ∉ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s) : divCycle P s W = 0 := by
  unfold divCycle
  exact dif_neg h

theorem mem_of_divCycle_ne (P : Ideal (MRing ι ℤ)) (s : MRing ι ℤ) (W : Ideal (MRing ι ℤ))
    (h : divCycle P s W ≠ 0) : W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s := by
  by_contra hc
  exact h (divCycle_eq_zero_of_not_mem P s W hc)

theorem multAt_eq (P : Ideal (MRing ι ℤ)) (s : MRing ι ℤ) (W : Ideal (MRing ι ℤ))
    (h : W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s) :
    ((ReciprocityTheory.ChartRestriction.G.Geo.multAt (P ⊔ Ideal.span {s}) W : ℕ) : ℤ) = divCycle P s W := by
  rw [← VocabDivCycle.proof ℤ K ι P s W]
  congr 1
  classical
  show _ = (if W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s then
    ReciprocityTheory.ChartRestriction.G.Geo.multAt (P ⊔ Ideal.span {s}) W else 0)
  rw [if_pos h]

end SlopeTestRemainingChoices

section Main

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]


open Classical in
noncomputable def vertTerm (p : Nat.Primes) (W : Ideal (MRing ι ℤ)) (l : List (K → ℤ)) : ℤ :=
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  if (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W then intNumL (ZMod p) (extTo (ZMod p) W) l else 0

theorem vertTerm_of_not_mem (p : Nat.Primes) (W : Ideal (MRing ι ℤ)) (l : List (K → ℤ))
    (h : (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∉ W) : vertTerm p W l = 0 := by
  unfold vertTerm
  exact if_neg h

theorem vertAt_eq_sum (p : Nat.Primes) (P : Ideal (MRing ι ℤ)) (s : MRing ι ℤ) (l : List (K → ℤ))
    (T : Finset (Ideal (MRing ι ℤ))) (hT : Function.support (divCycle P s) ⊆ T) :
    vertAt p P s l = ∑ W ∈ T, divCycle P s W * vertTerm p W l := by
  unfold vertAt cycEval
  exact finsum_eq_sum_of_support_subset _ fun W hW => hT (left_ne_zero_of_mul hW)

theorem key_of_mem {P : Ideal (MRing ι ℤ)} {D : ℕ} (hP : IsArithVar P (D + 1)) {a : K → ℕ}
    {s : MRing ι ℤ} (hs : IsMultiHomog s a) (hsP : s ∉ P) (b : Fin D → K → ℤ)
    {W : Ideal (MRing ι ℤ)} (hW : divCycle P s W ≠ 0) (p : Nat.Primes)
    (hp : (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W) :
    charOf W = p ∧ ¬ IsHorizontal W ∧ geoNum D W b = vertTerm p W (List.ofFn b) := by
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.GeoNumFp.geoNum_eq_intNum K ι P D hP a s hs hsP W hW (p : ℕ) hp
  refine ⟨h1, h2, ?_⟩
  rw [h3 b]
  unfold vertTerm
  rw [if_pos hp, intNumL_ofFn]

theorem support_term_subset {P : Ideal (MRing ι ℤ)} {D : ℕ} (hP : IsArithVar P (D + 1)) {a : K → ℕ}
    {s : MRing ι ℤ} (hs : IsMultiHomog s a) (hsP : s ∉ P) (b : Fin D → K → ℤ)
    (W : Ideal (MRing ι ℤ)) {p : Nat.Primes} (hW : divCycle P s W ≠ 0)
    (hp : vertTerm p W (List.ofFn b) ≠ 0) : charOf W = p := by
  by_cases hm : (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W
  · exact (key_of_mem hP hs hsP b hW p hm).1
  · exact absurd (vertTerm_of_not_mem p W _ hm) hp


open Classical in
theorem finsum_term {P : Ideal (MRing ι ℤ)} {D : ℕ} (hP : IsArithVar P (D + 1)) {a : K → ℕ}
    {s : MRing ι ℤ} (hs : IsMultiHomog s a) (hsP : s ∉ P) (b : Fin D → K → ℤ)
    (W : Ideal (MRing ι ℤ)) :
    ∑ᶠ p : Nat.Primes, Real.log (p : ℕ) * ((divCycle P s W * vertTerm p W (List.ofFn b) : ℤ) : ℝ) =
      (divCycle P s W : ℝ) *
        (if IsHorizontal W then 0 else (geoNum D W b : ℝ) * Real.log (charOf W)) := by
  by_cases hW : divCycle P s W = 0
  · simp [hW]
  by_cases hh : IsHorizontal W
  · rw [if_pos hh, mul_zero]
    refine finsum_eq_zero_of_forall_eq_zero fun p => ?_
    have : vertTerm p W (List.ofFn b) = 0 := by
      by_contra hne
      by_cases hm : (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W
      · exact (key_of_mem hP hs hsP b hW p hm).2.1 hh
      · exact hne (vertTerm_of_not_mem p W _ hm)
    simp [this]
  · rw [if_neg hh]
    have hWp : W.IsPrime := (mem_of_divCycle_ne P s W hW).1.1.1
    obtain ⟨q, hq⟩ := exists_prime_mem W hWp hh
    obtain ⟨hc, -, hg⟩ := key_of_mem hP hs hsP b hW q hq
    rw [finsum_eq_single _ q]
    · rw [hc, hg]
      push_cast
      ring
    · intro p hpq
      have : vertTerm p W (List.ofFn b) = 0 := by
        by_contra hne
        have h2 := support_term_subset hP hs hsP b W hW hne
        exact hpq (Nat.Primes.coe_nat_injective (h2.symm.trans hc))
      simp [this]

theorem recR_split : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (a : K → ℕ) (s : MRing ι ℤ), IsMultiHomog s a → s ∉ P → ∀ (L : Fin D → HermLine ι) (A : HermLine ι), (Function.support fun p : Nat.Primes => vertAt p P s (List.ofFn fun j => (L j).a)).Finite ∧ recR I P L A s = (∑ᶠ W, (divCycle P s W : ℝ) * Set.indicator {W | IsHorizontal W} (fun W => I W D L) W) + (∑ᶠ p : Nat.Primes, Real.log (p : ℕ) * (vertAt p P s (List.ofFn fun j => (L j).a) : ℝ)) - arInt P s A L := by
  intro K _ _ ι _ P D hP I a s hs hsP L A
  classical
  set b : Fin D → K → ℤ := fun j => (L j).a with hb
  set T : Finset (Ideal (MRing ι ℤ)) := (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s).toFinset with hT
  have hTm : ∀ W, W ∈ T ↔ W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s := fun W => by simp [hT]
  have hsub : Function.support (divCycle P s) ⊆ T := fun W hW =>
    (hTm W).2 (mem_of_divCycle_ne P s W hW)
  constructor
  · have hfin : ((fun W : Ideal (MRing ι ℤ) => charOf W) '' (T : Set _)).Finite :=
      T.finite_toSet.image _
    refine (hfin.preimage (Nat.Primes.coe_nat_injective.injOn)).subset fun p hp => ?_
    have hp' : vertAt p P s (List.ofFn b) ≠ 0 := hp
    rw [vertAt_eq_sum p P s _ T hsub] at hp'
    obtain ⟨W, hWT, hW⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp'
    exact ⟨W, hWT, support_term_subset hP hs hsP b W (left_ne_zero_of_mul hW)
      (right_ne_zero_of_mul hW)⟩
  · have h1 : (∑ᶠ W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s,
          ((ReciprocityTheory.ChartRestriction.G.Geo.multAt (P ⊔ Ideal.span {s}) W : ℕ) : ℝ) *
            (if IsHorizontal W then I W D L else (geoNum D W b : ℝ) * Real.log (charOf W))) =
        ∑ W ∈ T, (divCycle P s W : ℝ) *
            (if IsHorizontal W then I W D L else (geoNum D W b : ℝ) * Real.log (charOf W)) := by
      rw [finsum_mem_eq_finite_toFinset_sum _ (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s)]
      refine Finset.sum_congr rfl fun W hW => ?_
      rw [← multAt_eq P s W ((hTm W).1 hW)]
      norm_cast
    have h2 : (∑ᶠ W, (divCycle P s W : ℝ) * Set.indicator {W | IsHorizontal W} (fun W => I W D L) W) =
        ∑ W ∈ T, (divCycle P s W : ℝ) * Set.indicator {W | IsHorizontal W} (fun W => I W D L) W := by
      refine finsum_eq_sum_of_support_subset _ fun W hW => hsub ?_
      have := left_ne_zero_of_mul hW
      exact fun h0 => this (by simp [h0])
    have h3 : (∑ᶠ p : Nat.Primes, Real.log (p : ℕ) * (vertAt p P s (List.ofFn b) : ℝ)) =
        ∑ W ∈ T, (divCycle P s W : ℝ) *
          (if IsHorizontal W then 0 else (geoNum D W b : ℝ) * Real.log (charOf W)) := by
      have e : ∀ p : Nat.Primes, Real.log (p : ℕ) * (vertAt p P s (List.ofFn b) : ℝ) =
          ∑ W ∈ T, Real.log (p : ℕ) * ((divCycle P s W * vertTerm p W (List.ofFn b) : ℤ) : ℝ) := by
        intro p
        rw [vertAt_eq_sum p P s _ T hsub, Int.cast_sum, Finset.mul_sum]
      simp_rw [e]
      rw [finsum_sum_comm]
      · exact Finset.sum_congr rfl fun W _ => finsum_term hP hs hsP b W
      · intro W _
        refine ((Set.finite_singleton (charOf W)).preimage
          (Nat.Primes.coe_nat_injective.injOn)).subset fun p hp => ?_
        have hne := right_ne_zero_of_mul (show _ ≠ (0 : ℝ) from hp)
        have hne' : divCycle P s W * vertTerm p W (List.ofFn b) ≠ 0 := by exact_mod_cast hne
        exact (support_term_subset hP hs hsP b W (left_ne_zero_of_mul hne')
          (right_ne_zero_of_mul hne')).symm
    have h0 : recR I P L A s = (∑ᶠ W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s,
          ((ReciprocityTheory.ChartRestriction.G.Geo.multAt (P ⊔ Ideal.span {s}) W : ℕ) : ℝ) *
            (if IsHorizontal W then I W D L else (geoNum D W b : ℝ) * Real.log (charOf W))) -
        arInt P s A L := rfl
    rw [h0, h1, h2, h3, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun W _ => ?_
    by_cases hh : IsHorizontal W
    · simp [hh, Set.indicator]
    · simp [hh, Set.indicator]

end Main

end GlobalTheory.CompanionTheory.Ar.Num.RecSplit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsBlockMapDrop
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {K : Type}

theorem isBlockMap_drop (j : K → FlBlock Ψ N) (k₀ : K) :
    IsBlockMap (Subtype.val : {k // k ≠ k₀} → K) (dropV j k₀) := by
  refine ⟨Subtype.val_injective, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨⟨a, ha⟩, x⟩ ⟨⟨b, hb⟩, y⟩ h
    have h' : (⟨a, x⟩ : Σ k, PIdx j k) = ⟨b, y⟩ := h
    cases h'
    rfl
  · rintro ⟨k, x⟩ ⟨⟨k', hk⟩, rfl⟩
    exact ⟨⟨⟨k', hk⟩, x⟩, rfl⟩

theorem imageZ_drop [Fintype K] [DecidableEq K] (j : K → FlBlock Ψ N) (k₀ : K) :
    imageZ (dropV j k₀) (PPart j) = PPart (dropJ j k₀) := by
  have key : ∀ f : MRing (PIdx (dropJ j k₀)), mConeMap (yPart j) (rename (dropV j k₀) f) =
      rename Subtype.val (mConeMap (yPart (dropJ j k₀)) f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp [hp, hq]
    | mul_X p n hp =>
      simp only [map_mul, hp, rename_X]
      congr 1
      simp [mConeMap, yPart, dropV, dropJ]
  ext f
  simp only [imageZ, PPart, mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker]
  show mConeMap (yPart j) (rename (dropV j k₀) f) = 0 ↔ _
  rw [key]
  constructor
  · intro h
    exact rename_injective _ Subtype.val_injective (by rw [h, map_zero])
  · intro h
    have h' : mConeMap (yPart (dropJ j k₀)) f = 0 := h
    rw [h', map_zero]

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LinRootRemainderBound
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem restSum_total_bound : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (bad : Finset ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (u : Wt Ψ N) (g : ℝ) (B : ℕ) (Q : Ψ → ℕ → RP Ψ N), 1 ≤ j → j < N → WeightHyp j u g → bigB0 u g < B + 1 → IsDecomp (linRoot u ^ (dimFl Ψ N + 1)) Q → |∑ τ, ∑ k ∈ Finset.Icc 1 N, restSum j bad frob B τ k (Q τ k)| ≤ 2 * (((dimFl Ψ N : ℝ) + 1) * flagDeg u) * ((min j (N - j) : ℕ) * spread u) :=
  RootFieldNumerics.rest_sum_total_bound

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RhoFactorialProductEq
section
namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

theorem prod_range_sub_eq_factorial (i n : ℕ) :
    ∏ k ∈ Finset.range n, (if i < k then ((k : ℝ) - (i : ℝ)) else 1) = (((n - 1 - i).factorial : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    by_cases h : i < n
    · obtain ⟨t, rfl⟩ : ∃ t, n = i + 1 + t := ⟨n - (i + 1), by omega⟩
      have e1 : i + 1 + t - 1 - i = t := by omega
      have e2 : i + 1 + t + 1 - 1 - i = t + 1 := by omega
      rw [if_pos h, e1, e2, Nat.factorial_succ]
      push_cast
      ring
    · have e1 : n - 1 - i = 0 := by omega
      have e2 : n + 1 - 1 - i = 0 := by omega
      rw [if_neg h, e1, e2]
      simp

theorem prod_rhoM_factorial (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) :
    ∏ p, (((rhoM Ψ N) p).factorial : ℝ) =
      ∏ _τ : Ψ, ∏ i : Fin N, ∏ k : Fin N, (if i < k then ((k : ℝ) - (i : ℝ)) else 1) := by
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ => ?_
  have h := prod_range_sub_eq_factorial (i : ℕ) N
  rw [← Fin.prod_univ_eq_prod_range (fun k => if (i : ℕ) < k then ((k : ℝ) - ((i : ℕ) : ℝ)) else 1) N] at h
  have hr : (rhoM Ψ N) (τ, i) = N - 1 - (i : ℕ) := rfl
  rw [hr, ← h]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [Fin.lt_def]

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg
end

