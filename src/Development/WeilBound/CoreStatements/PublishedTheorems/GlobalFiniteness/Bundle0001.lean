module

public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalFiniteness.Transport
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Dimension
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CohomologicalDimensionTopologicalIso
public import ReciprocityTheory.Hypotheses.GalCoh
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
public import GroundTheory.ProfiniteCohomology.ContinuousCochains
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsDiscreteRepResMuROrep
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermFrameKTypeCoefficients
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.GlobalFiniteness.FiniteH2TorsionModule
section
noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace PositivityTheory.Lit1.GFParts

theorem card_eq_pow_of_torsion {V : Type} [AddCommGroup V] [Finite V] (l : ℕ) [Fact l.Prime] (r : ℕ)
    (h : ∀ a : V, (l ^ r) • a = 0) : ∃ k : ℕ, Nat.card V = l ^ k := by
  have hp : IsPGroup l (Multiplicative V) := fun g => ⟨r, by
    change Multiplicative.ofAdd ((l ^ r) • Multiplicative.toAdd g) = 1
    rw [h]; rfl⟩
  have : Finite (Multiplicative V) := inferInstanceAs (Finite V)
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  exact ⟨k, hk⟩

theorem mem_of_pow_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (l k : ℕ)
    (h : ((l ^ k : ℕ) : 𝓞 F) ∈ v.asIdeal) : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  rw [Nat.cast_pow] at h
  exact v.isPrime.mem_of_pow_mem k h

theorem finite_H2_torsion_module : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l → ∀ (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))))) [IsDiscreteRep A], Finite A.V → (∀ a : A.V, (l ^ r) • a = 0) → Finite (cohomology A 2) := by
  intro F Ω _ _ _ _ _ l _ r S hS A _ hAf hAk
  obtain ⟨K, S', hS', ⟨θ⟩⟩ := _root_.GlobalTheory.CompanionTheory.GSCd.Transport.exists_gs_transport F Ω l S hS
  obtain ⟨k, hk⟩ := card_eq_pow_of_torsion l r hAk
  have hK : ∀ v : HeightOneSpectrum (𝓞 K.1), ((Nat.card A.V : ℕ) : 𝓞 K.1) ∈ v.asIdeal →
      v ∈ (S' : Set (HeightOneSpectrum (𝓞 K.1))) := by
    intro v hv
    rw [hk] at hv
    exact Finset.mem_coe.2 (hS' v (mem_of_pow_mem v l k hv))
  refine PositivityTheory.Lit1.GFTransport.finite_cohomology_transport θ A 2 ?_
  let φ : galUnramifiedOutside K.1 (AlgebraicClosure ℚ) (S' : Set (HeightOneSpectrum (𝓞 K.1))) →*
      galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) :=
    (θ.symm : galUnramifiedOutside K.1 (AlgebraicClosure ℚ) (S' : Set (HeightOneSpectrum (𝓞 K.1))) ≃*
      galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F)))).toMonoidHom
  have : IsDiscreteRep (Rep.res φ A) := IsDiscreteRep.res (φ := φ) θ.symm.continuous A
  have : Finite (Rep.res φ A).V := hAf
  exact finite_cohomology_gs K (S' : Set (HeightOneSpectrum (𝓞 K.1))) (Rep.res φ A) hK 2 (by norm_num)

theorem cdp_gal_le_two (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ContainsAbove S l) (hl2 : l ≠ 2) :
    cdp l (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F)))) ≤ 2 := by
  obtain ⟨K, S', hS', ⟨e⟩⟩ := _root_.GlobalTheory.CompanionTheory.GSCd.Transport.exists_gs_transport F Ω l S hS
  rw [_root_.GlobalTheory.CompanionTheory.GSCd.cdp_eq_of_continuousMulEquiv _ _ l e]
  exact cdp_galUnramifiedOutside_le_two K (S' : Set (HeightOneSpectrum (𝓞 K.1))) Fact.out
    (fun v hv => hS' v hv) (Or.inl hl2)

theorem subsingleton_hn : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l → l ≠ 2 → ∀ (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))))) [IsDiscreteRep A], Finite A.V → (∀ a : A.V, (l ^ r) • a = 0) → ∀ n : ℕ, 3 ≤ n → Subsingleton (cohomology A n) := by
  intro F Ω _ _ _ _ _ l _ r S hS hl2 A _ _ hA n hn
  have hp : l.Prime := Fact.out
  have hcd := cdp_gal_le_two F Ω l S hS hl2
  refine subsingleton_cohomology_of_cdp_le_two (n := l ^ r) (pow_ne_zero r hp.ne_zero)
    (fun q hq hqd => ?_) A hA hn
  have hql : q = l := (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hqd)
  subst hql
  exact hcd

end PositivityTheory.Lit1.GFParts
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.GlobalFiniteness.VanishAll
section
noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open GlobalTheory.CompanionTheory.GSCd.Transport

namespace PositivityTheory.Lit1.GFVanish

theorem exists_gs_transport_field (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ContainsAbove S l) :
    ∃ (K : FiniteSubfield) (S' : Finset (HeightOneSpectrum (𝓞 K.1))), ContainsAbove S' l ∧
      Nonempty (F ≃+* K.1) ∧
      Nonempty (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≃ₜ*
        galUnramifiedOutside K.1 (AlgebraicClosure ℚ) (S' : Set (HeightOneSpectrum (𝓞 K.1)))) := by
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  obtain ⟨K, ψ, e, he⟩ := exists_embedded F Ω
  classical
  refine ⟨K, S.map (placeEquiv (RingOfIntegers.mapRingEquiv ψ)).toEmbedding, ?_, ⟨ψ⟩,
    nonempty_gal ψ e he ?_⟩
  · intro w hw
    have hv : (placeEquiv (RingOfIntegers.mapRingEquiv ψ)).symm w ∈ S := by
      apply hS
      change RingOfIntegers.mapRingEquiv ψ (l : 𝓞 F) ∈ w.asIdeal
      rw [map_natCast]
      exact hw
    exact Finset.mem_map.2 ⟨_, hv, (placeEquiv _).apply_symm_apply w⟩
  · intro v
    simp

theorem cdp_gal_le_two_gen (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ContainsAbove S l) (hK : l ≠ 2 ∨ IsTotallyComplex F) :
    cdp l (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F)))) ≤ 2 := by
  obtain ⟨K, S', hS', ⟨ψ⟩, ⟨e⟩⟩ := exists_gs_transport_field F Ω l S hS
  rw [_root_.GlobalTheory.CompanionTheory.GSCd.cdp_eq_of_continuousMulEquiv _ _ l e]
  refine cdp_galUnramifiedOutside_le_two K (S' : Set (HeightOneSpectrum (𝓞 K.1))) Fact.out
    (fun v hv => hS' v hv) (hK.imp id fun h => by
      let _ : IsTotallyComplex F := h
      let _ : Algebra F K.1 := ψ.toRingHom.toAlgebra
      exact isTotallyComplex_of_algebra F K.1)

theorem subsingleton_hn_gen (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ContainsAbove S l) (hK : l ≠ 2 ∨ IsTotallyComplex F)
    (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F)))))
    [IsDiscreteRep A] (hA : ∀ a : A.V, (l ^ r) • a = 0) (n : ℕ) (hn : 3 ≤ n) :
    Subsingleton (cohomology A n) := by
  have hp : l.Prime := Fact.out
  have hcd := cdp_gal_le_two_gen F Ω l S hS hK
  refine subsingleton_cohomology_of_cdp_le_two (n := l ^ r) (pow_ne_zero r hp.ne_zero)
    (fun q hq hqd => ?_) A hA hn
  have hql : q = l := (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hqd)
  subst hql
  exact hcd

theorem vanishAll : PositivityTheory.PoitouTateConclusion.VanishAll := by
  intro F Ω _ _ _ _ _ l _ r hK _ S hS M _ _ _ _ _ ρ hc n hn
  obtain ⟨A, _, _, hA, -, -, hAn⟩ := PositivityTheory.Lit1.GFTransport.cohDict S ρ hc
  obtain ⟨en⟩ := hAn n
  have : Subsingleton (cohomology A n) := subsingleton_hn_gen F Ω l r S hS hK A hA n hn
  exact en.toEquiv.subsingleton

end PositivityTheory.Lit1.GFVanish
end
end

