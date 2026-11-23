module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RegularLocalRegularSequence.RingKrullDimQuotientSpanSingletonAddOne

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.IdCompMat
section
open Polynomial Matrix

private noncomputable def UpperTheory.V.AlgebraTools.icmPt {K ι : Type} [Field K] (A : Matrix ι ι K) :
    PrimeSpectrum (MvPolynomial (ι × ι) K) :=
  ⟨RingHom.ker (MvPolynomial.eval (fun p : ι × ι => A p.1 p.2)), RingHom.ker_isPrime _⟩

private theorem UpperTheory.V.AlgebraTools.icmPt_left {K ι : Type} [Field K] [Fintype ι] (A : Matrix ι ι K) :
    ∃ ψ : MvPolynomial (ι × ι) K →+* MvPolynomial (ι × ι) K, ∀ B : Matrix ι ι K,
      UpperTheory.V.AlgebraTools.icmPt (A * B) = PrimeSpectrum.comap ψ (UpperTheory.V.AlgebraTools.icmPt B) := by
  refine ⟨(MvPolynomial.aeval fun p : ι × ι =>
    ∑ k, MvPolynomial.C (A p.1 k) * MvPolynomial.X (k, p.2)).toRingHom, fun B => ?_⟩
  have key : (MvPolynomial.eval fun p : ι × ι => (A * B) p.1 p.2) =
      (MvPolynomial.eval fun p : ι × ι => B p.1 p.2).comp
        (MvPolynomial.aeval fun p : ι × ι =>
          ∑ k, MvPolynomial.C (A p.1 k) * MvPolynomial.X (k, p.2)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro p
      simp [Matrix.mul_apply]
  apply PrimeSpectrum.ext
  show RingHom.ker _ = Ideal.comap _ (RingHom.ker _)
  rw [key, RingHom.comap_ker]

private theorem UpperTheory.V.AlgebraTools.icmPt_right {K ι : Type} [Field K] [Fintype ι] (A : Matrix ι ι K) :
    ∃ ψ : MvPolynomial (ι × ι) K →+* MvPolynomial (ι × ι) K, ∀ B : Matrix ι ι K,
      UpperTheory.V.AlgebraTools.icmPt (B * A) = PrimeSpectrum.comap ψ (UpperTheory.V.AlgebraTools.icmPt B) := by
  refine ⟨(MvPolynomial.aeval fun p : ι × ι =>
    ∑ k, MvPolynomial.X (p.1, k) * MvPolynomial.C (A k p.2)).toRingHom, fun B => ?_⟩
  have key : (MvPolynomial.eval fun p : ι × ι => (B * A) p.1 p.2) =
      (MvPolynomial.eval fun p : ι × ι => B p.1 p.2).comp
        (MvPolynomial.aeval fun p : ι × ι =>
          ∑ k, MvPolynomial.X (p.1, k) * MvPolynomial.C (A k p.2)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro p
      simp [Matrix.mul_apply]
  apply PrimeSpectrum.ext
  show RingHom.ker _ = Ideal.comap _ (RingHom.ker _)
  rw [key, RingHom.comap_ker]

theorem UpperTheory.V.AlgebraTools.idCompMat :
    ∀ (K G ι : Type) [Field K] [Group G] [Fintype ι] [DecidableEq ι] (r : G →* Matrix ι ι K),
      ∃ N : Subgroup G, N.Normal ∧ N.FiniteIndex ∧
        (∃ I : Set (MvPolynomial (ι × ι) K), ∀ g, g ∈ N ↔ ∀ f ∈ I, MvPolynomial.eval (fun p => r g p.1 p.2) f = 0) ∧
        ∀ (U : Subgroup G), U.FiniteIndex → ∀ (σ : G) (s : Finset (MvPolynomial (ι × ι) K)),
          (∀ f ∈ s, ∃ g ∈ N, MvPolynomial.eval (fun p => r (σ * g) p.1 p.2) f ≠ 0) →
          ∃ g ∈ U ⊓ N, ∀ f ∈ s, MvPolynomial.eval (fun p => r (σ * g) p.1 p.2) f ≠ 0 := by
  classical
  intro K G ι _ _ _ _ r
  let f : G → PrimeSpectrum (MvPolynomial (ι × ι) K) := fun g => UpperTheory.V.AlgebraTools.icmPt (r g)
  letI tG : TopologicalSpace G := TopologicalSpace.induced f inferInstance
  have hind : Topology.IsInducing f := ⟨rfl⟩
  haveI : TopologicalSpace.NoetherianSpace G := hind.noetherianSpace
  have hf : Continuous f := continuous_induced_dom
  have hL : ∀ g : G, Continuous fun x => g * x := by
    intro g
    obtain ⟨ψ, hψ⟩ := UpperTheory.V.AlgebraTools.icmPt_left (r g)
    refine continuous_induced_rng.2 ?_
    have : (f ∘ fun x => g * x) = PrimeSpectrum.comap ψ ∘ f := by
      funext x
      simp only [Function.comp_apply, f, map_mul]
      exact hψ (r x)
    rw [this]
    exact (PrimeSpectrum.continuous_comap ψ).comp hf
  have hR : ∀ g : G, Continuous fun x => x * g := by
    intro g
    obtain ⟨ψ, hψ⟩ := UpperTheory.V.AlgebraTools.icmPt_right (r g)
    refine continuous_induced_rng.2 ?_
    have : (f ∘ fun x => x * g) = PrimeSpectrum.comap ψ ∘ f := by
      funext x
      simp only [Function.comp_apply, f, map_mul]
      exact hψ (r x)
    rw [this]
    exact (PrimeSpectrum.continuous_comap ψ).comp hf
  obtain ⟨N, hNn, hNf, hNc, hNi, hNd⟩ := UpperTheory.V.AlgebraTools.idComp G hL hR
  have hmemZ : ∀ (S : Set (MvPolynomial (ι × ι) K)) (g : G),
      f g ∈ PrimeSpectrum.zeroLocus S ↔ ∀ q ∈ S, MvPolynomial.eval (fun p => r g p.1 p.2) q = 0 := by
    intro S g
    rw [PrimeSpectrum.mem_zeroLocus]
    constructor
    · intro h q hq
      exact (RingHom.mem_ker).1 (h hq)
    · intro h q hq
      exact (RingHom.mem_ker).2 (h q hq)
  refine ⟨N, hNn, hNf, ?_, ?_⟩
  · obtain ⟨t, ht, hNt⟩ := isClosed_induced_iff.1 hNc
    obtain ⟨S, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus t).1 ht
    refine ⟨S, fun g => ?_⟩
    rw [← hmemZ S g]
    constructor
    · intro hg
      have h' : g ∈ (N : Set G) := hg
      rw [← hNt] at h'
      exact h'
    · intro hg
      have h' : g ∈ f ⁻¹' PrimeSpectrum.zeroLocus S := hg
      rw [hNt] at h'
      exact h'
  · intro U hU σ s hs
    let W : MvPolynomial (ι × ι) K → Set G :=
      fun q => {g | MvPolynomial.eval (fun p => r (σ * g) p.1 p.2) q ≠ 0}
    have hWo : ∀ q, IsOpen (W q) := by
      intro q
      have h1 : IsOpen (f ⁻¹' (PrimeSpectrum.basicOpen q : Set _)) :=
        (PrimeSpectrum.isOpen_basicOpen).preimage hf
      have h2 := h1.preimage (hL σ)
      convert h2 using 1
      ext g
      simp only [W, Set.mem_setOf_eq, Set.mem_preimage, f, SetLike.mem_coe,
        PrimeSpectrum.mem_basicOpen]
      show _ ↔ q ∉ RingHom.ker _
      rw [RingHom.mem_ker]
    obtain ⟨x, hxN, hxO⟩ := (isIrreducible_iff_sInter.1 hNi) (s.image W)
      (by
        intro u hu
        obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
        exact hWo q)
      (by
        intro u hu
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hu
        obtain ⟨g, hgN, hg⟩ := hs q hq
        exact ⟨g, hgN, hg⟩)
    have hOo : IsOpen (⋂₀ (↑(s.image W) : Set (Set G))) := by
      apply Set.Finite.isOpen_sInter (Finset.finite_toSet _)
      intro u hu
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
      exact hWo q
    obtain ⟨g, hgO, hgUN⟩ := mem_closure_iff.1 (hNd U hU hxN) _ hOo hxO
    refine ⟨g, hgUN, fun q hq => ?_⟩
    have : g ∈ W q := hgO _ (Finset.mem_image_of_mem W hq)
    exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.RegOfDim
section
open Polynomial Matrix

theorem UpperTheory.V.AlgebraTools.regOfDim :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (J : Ideal R), J ≠ ⊤ →
      ((IsLocalRing.maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ J) → J = ⊥ := by
  intro R _ _ _ J hJ hdim
  have hR := ringKrullDim_le_spanFinrank_maximalIdeal R
  have hq := ringKrullDim_quotient_le J
  have heq : ((IsLocalRing.maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    le_antisymm (hdim.trans hq) hR
  have hJeq : ringKrullDim (R ⧸ J) = ((IsLocalRing.maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
    le_antisymm (hq.trans hR) hdim
  haveI : IsRegularLocalRing R := ⟨heq⟩
  haveI := PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.isDomain R
  by_contra hne
  obtain ⟨r, hrJ, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hnz : r ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hr0
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnz
  have hsub : Ideal.span {r} ≤ J := (Ideal.span_singleton_le_iff_mem J).2 hrJ
  have h2 : ringKrullDim (R ⧸ J) ≤ ringKrullDim (R ⧸ Ideal.span {r}) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hsub) (Ideal.Quotient.factor_surjective hsub)
  have h3 : ringKrullDim (R ⧸ J) + 1 ≤ ringKrullDim (R ⧸ J) := by
    calc ringKrullDim (R ⧸ J) + 1 ≤ ringKrullDim (R ⧸ Ideal.span {r}) + 1 := by gcongr
      _ ≤ ringKrullDim R := h1
      _ = ringKrullDim (R ⧸ J) := by rw [hJeq, heq]
  rw [hJeq] at h3
  norm_cast at h3
  omega
end

