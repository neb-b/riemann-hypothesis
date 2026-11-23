module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PTConclAt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0130
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDefs
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsAddTransfer
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0112
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.MemDecompositionSubgroupIff
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso Pointwise

namespace PositivityTheory.PTNLoc

theorem mem_decompositionSubgroup_iff {F Ω : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] (A : ValuationSubring Ω) (σ : G F Ω) :
    σ ∈ A.decompositionSubgroup F ↔ ∀ x, σ x ∈ A ↔ x ∈ A := by
  constructor
  · intro h x
    exact ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec (F := F) h x
  · intro h
    show σ • A = A
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    have := h ((σ⁻¹ : G F Ω) y)
    rw [ReciprocityTheory.Gal.mul_inv_apply] at this
    exact this.symm

theorem valuation_le_one_transport {Ω Ω' : Type} [Field Ω] [Field Ω'] (E : Ω ≃+* Ω')
    {A : ValuationSubring Ω} {A' : ValuationSubring Ω'} (hA : ∀ x, E x ∈ A' ↔ x ∈ A) (x : Ω) :
    A'.valuation (E x) ≤ 1 ↔ A.valuation x ≤ 1 := by
  rw [A'.valuation_le_one_iff, A.valuation_le_one_iff]
  exact hA x

theorem valuation_lt_one_transport {Ω Ω' : Type} [Field Ω] [Field Ω'] (E : Ω ≃+* Ω')
    {A : ValuationSubring Ω} {A' : ValuationSubring Ω'} (hA : ∀ x, E x ∈ A' ↔ x ∈ A) (x : Ω) :
    A'.valuation (E x) < 1 ↔ A.valuation x < 1 := by
  rw [ReciprocityTheory.Gal.valuation_lt_one_iff', ReciprocityTheory.Gal.valuation_lt_one_iff', ← map_inv₀ E x,
    hA, hA, map_eq_zero_iff E E.injective]

theorem locHyp : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ σ : G F Ω, (σ ∈ Dec (F := F) A ↔ Φ σ ∈ Dec (F := F') A') ∧ (σ ∈ Inertia (F := F) A ↔ Φ σ ∈ Inertia (F := F') A') ∧ ∀ q : ℕ, IsFrob (F := F) A q σ ↔ IsFrob (F := F') A' q (Φ σ) := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE Φ hΦ A A' hA σ
  have hdec : σ ∈ A.decompositionSubgroup F ↔ Φ σ ∈ A'.decompositionSubgroup F' := by
    rw [mem_decompositionSubgroup_iff, mem_decompositionSubgroup_iff]
    constructor
    · intro h y
      obtain ⟨x, rfl⟩ := E.surjective y
      rw [hΦ, hA, hA]
      exact h x
    · intro h x
      have := h (E x)
      rwa [hΦ, hA, hA] at this
  refine ⟨hdec, ?_, fun q => ?_⟩
  · show (σ ∈ A.decompositionSubgroup F ∧ _) ↔ (Φ σ ∈ A'.decompositionSubgroup F' ∧ _)
    refine and_congr hdec ⟨fun h y hy => ?_, fun h x hx => ?_⟩
    · obtain ⟨x, rfl⟩ := E.surjective y
      rw [hΦ, ← map_sub E, valuation_lt_one_transport E hA]
      exact h x ((valuation_le_one_transport E hA x).1 hy)
    · have := h (E x) ((valuation_le_one_transport E hA x).2 hx)
      rwa [hΦ, ← map_sub E, valuation_lt_one_transport E hA] at this
  · show (σ ∈ A.decompositionSubgroup F ∧ _) ↔ (Φ σ ∈ A'.decompositionSubgroup F' ∧ _)
    refine and_congr hdec ⟨fun h y hy => ?_, fun h x hx => ?_⟩
    · obtain ⟨x, rfl⟩ := E.surjective y
      rw [hΦ, ← map_pow E x q, ← map_sub E, valuation_lt_one_transport E hA]
      exact h x ((valuation_le_one_transport E hA x).1 hy)
    · have := h (E x) ((valuation_le_one_transport E hA x).2 hx)
      rwa [hΦ, ← map_pow E x q, ← map_sub E, valuation_lt_one_transport E hA] at this

end PositivityTheory.PTNLoc
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PfContActionTwDualC
section
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

theorem contAction_twDual_C {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
    (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (hρ : ContAction ρ) : ContAction (twDual μ ρ) := by
  have hμc : Continuous μ := by
    have hq : Topology.IsQuotientMap (toGS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) :=
      QuotientGroup.isQuotientMap_mk _
    rw [hq.continuous_iff]
    have h2 : (⇑μ ∘ ⇑(toGS Ω (S : Set (HeightOneSpectrum (𝓞 F))))) = ⇑(cycMod F Ω l r) := by
      rw [← hμ]
      rfl
    rw [h2]
    exact GlobalTheory.Published.PoitouTate.continuous_cycMod
  have hρ' : Continuous fun p : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) × M => ρ p.1 p.2 := hρ
  haveI : Fintype M := Fintype.ofFinite M
  show Continuous fun p : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) × TDual (ZMod (l ^ r)) M =>
    twDual μ ρ p.1 p.2
  rw [continuous_prod_of_discrete_right]
  intro φ
  refine continuous_discrete_rng.mpr ?_
  intro ψ
  have hset : (fun g => (twDual μ ρ g) φ) ⁻¹' {ψ} =
      ⋂ m : M, (fun g : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) =>
        ((μ g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * φ (ρ g⁻¹ m)) ⁻¹' {ψ m} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
    constructor
    · rintro h m
      rw [← h, twDual_apply]
    · intro h
      apply DFunLike.ext
      intro m
      rw [twDual_apply]
      exact h m
  rw [hset]
  refine isOpen_iInter_of_finite fun m => ?_
  have h1 : Continuous fun g : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) =>
      ((μ g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) :=
    Units.continuous_val.comp hμc
  have h2 : Continuous fun g : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) => ρ g⁻¹ m :=
    hρ'.comp (continuous_inv.prodMk continuous_const)
  have h3 : Continuous fun g : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) => φ (ρ g⁻¹ m) :=
    continuous_of_discreteTopology.comp h2
  exact (isOpen_discrete _).preimage (h1.mul h3)

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsHyp
section
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

namespace PositivityTheory.PTN

def LocHyp : Prop :=
  ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ σ : G F Ω, (σ ∈ Dec (F := F) A ↔ Φ σ ∈ Dec (F := F') A') ∧ (σ ∈ Inertia (F := F) A ↔ Φ σ ∈ Inertia (F := F') A') ∧ ∀ q : ℕ, IsFrob (F := F) A q σ ↔ IsFrob (F := F') A' q (Φ σ)

def PtfsHyp : Prop :=
  ∀ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsAlgClosure K (AlgebraicClosure ℚ)], PTConclAt K (AlgebraicClosure ℚ)

end PositivityTheory.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsNineAdd
section
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

def NineAdd {N : ℕ} {A0 A1 A2 A3 A4 A5 A6 A7 A8 : Type} [AddCommGroup A0] [Module (ZMod N) A0] [AddCommGroup A1] [Module (ZMod N) A1] [AddCommGroup A2] [Module (ZMod N) A2] [AddCommGroup A3] [Module (ZMod N) A3] [AddCommGroup A4] [Module (ZMod N) A4] [AddCommGroup A5] [Module (ZMod N) A5] [AddCommGroup A6] [Module (ZMod N) A6] [AddCommGroup A7] [Module (ZMod N) A7] [AddCommGroup A8] [Module (ZMod N) A8]
    (f0 : A0 →ₗ[ZMod N] A1) (f1 : A1 →ₗ[ZMod N] A2) (f3 : A3 →ₗ[ZMod N] A4)
    (f4 : A4 →ₗ[ZMod N] A5) (f6 : A6 →ₗ[ZMod N] A7) (f7 : A7 →ₗ[ZMod N] A8) : Prop :=
  ∃ (B0 B1 B2 B3 B4 B5 B6 B7 BetaSesquilinearity : AddCommGrpCat.{0})
    (g0 : B0 →+ B1) (g1 : B1 →+ B2) (g2 : B2 →+ B3) (g3 : B3 →+ B4) (g4 : B4 →+ B5)
    (g5 : B5 →+ B6) (g6 : B6 →+ B7) (g7 : B7 →+ BetaSesquilinearity)
    (e0 : A0 ≃+ B0) (e1 : A1 ≃+ B1) (e2 : A2 ≃+ B2) (e3 : A3 ≃+ B3) (e4 : A4 ≃+ B4)
    (e5 : A5 ≃+ B5) (e6 : A6 ≃+ B6) (e7 : A7 ≃+ B7) (e8 : A8 ≃+ BetaSesquilinearity) (ε : Fin 6 → ℤˣ),
    (∀ a, g0 (e0 a) = (ε 0 : ℤ) • e1 (f0 a)) ∧ (∀ a, g1 (e1 a) = (ε 1 : ℤ) • e2 (f1 a)) ∧
    (∀ a, g3 (e3 a) = (ε 2 : ℤ) • e4 (f3 a)) ∧ (∀ a, g4 (e4 a) = (ε 3 : ℤ) • e5 (f4 a)) ∧
    (∀ a, g6 (e6 a) = (ε 4 : ℤ) • e7 (f6 a)) ∧ (∀ a, g7 (e7 a) = (ε 5 : ℤ) • e8 (f7 a)) ∧
    Function.Injective g0 ∧ Function.Exact g0 g1 ∧ Function.Exact g1 g2 ∧
    Function.Exact g2 g3 ∧ Function.Exact g3 g4 ∧ Function.Exact g4 g5 ∧ Function.Exact g5 g6 ∧
    Function.Exact g6 g7 ∧ Function.Surjective g7

theorem nineCmp_of_nineAdd {N : ℕ} {A0 A1 A2 A3 A4 A5 A6 A7 A8 : Type} [AddCommGroup A0] [Module (ZMod N) A0] [AddCommGroup A1] [Module (ZMod N) A1] [AddCommGroup A2] [Module (ZMod N) A2] [AddCommGroup A3] [Module (ZMod N) A3] [AddCommGroup A4] [Module (ZMod N) A4] [AddCommGroup A5] [Module (ZMod N) A5] [AddCommGroup A6] [Module (ZMod N) A6] [AddCommGroup A7] [Module (ZMod N) A7] [AddCommGroup A8] [Module (ZMod N) A8]
    {f0 : A0 →ₗ[ZMod N] A1} {f1 : A1 →ₗ[ZMod N] A2} {f3 : A3 →ₗ[ZMod N] A4}
    {f4 : A4 →ₗ[ZMod N] A5} {f6 : A6 →ₗ[ZMod N] A7} {f7 : A7 →ₗ[ZMod N] A8}
    (h : NineAdd f0 f1 f3 f4 f6 f7) : NineCmp f0 f1 f3 f4 f6 f7 := by
  obtain ⟨B0, B1, B2, B3, B4, B5, B6, B7, BetaSesquilinearity, g0, g1, g2, g3, g4, g5, g6, g7, e0, e1, e2, e3, e4,
    e5, e6, e7, e8, ε, h0, h1, h3, h4, h6, h7, hx⟩ := h
  obtain ⟨δ₁, δ₂, x⟩ := nine_of_addTransfer f0 f1 f3 f4 f6 f7 g0 g1 g2 g3 g4 g5 g6 g7
    e0 e1 e2 e3 e4 e5 e6 e7 e8 ε h0 h1 h3 h4 h6 h7 hx
  exact ⟨ModuleCat.of (ZMod N) A0, ModuleCat.of (ZMod N) A1, ModuleCat.of (ZMod N) A2,
    ModuleCat.of (ZMod N) A3, ModuleCat.of (ZMod N) A4, ModuleCat.of (ZMod N) A5,
    ModuleCat.of (ZMod N) A6, ModuleCat.of (ZMod N) A7, ModuleCat.of (ZMod N) A8,
    f0, f1, δ₁, f3, f4, δ₂, f6, f7, LinearEquiv.refl _ _, LinearEquiv.refl _ _,
    LinearEquiv.refl _ _, LinearEquiv.refl _ _, LinearEquiv.refl _ _, LinearEquiv.refl _ _,
    LinearEquiv.refl _ _, LinearEquiv.refl _ _, LinearEquiv.refl _ _, fun _ => 1,
    fun a => by simp, fun a => by simp, fun a => by simp, fun a => by simp, fun a => by simp,
    fun a => by simp, x⟩

def NineAddFS : Prop :=
  ∀ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsAlgClosure K (AlgebraicClosure ℚ)] (l : ℕ) [Fact l.Prime] (r : ℕ),
  (l ≠ 2 ∨ IsTotallyComplex K) → 0 < r →
  ∀ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ (l ^ r) → ∀ inv : InvFam K (AlgebraicClosure ℚ) l r,
  InvNormalised ζ inv →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), ContainsAbove S l →
  ∀ (Av : S → ValuationSubring (AlgebraicClosure ℚ)), (∀ v, IsPlaceOver (Av v) v.1) →
  ∀ (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod K (AlgebraicClosure ℚ) l r),
  ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))) M)
    (hρ : ContAction ρ),
    NineAdd (loc0 S Av ρ) (tr0 S Av μ (invAt S Av μ hμ inv) ρ) (loc1 S Av ρ)
      (tr1 S Av μ (invAt S Av μ hμ inv) ρ hρ) (loc2 S Av ρ) (tr2 S Av μ (invAt S Av μ hμ inv) ρ)

theorem nineCmpFS_of_nineAddFS (h : NineAddFS) : NineCmpFS := by
  intro K _ _ l _ r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M _ _ _ _ _ ρ hρ
  exact nineCmp_of_nineAdd (h K l r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M ρ hρ)

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsShaHalf
section
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

theorem shaHalf_of_perfectPair {n : ℕ} [NeZero n] {X Y : Type} [AddCommGroup X]
    [Module (ZMod n) X] [AddCommGroup Y] [Module (ZMod n) Y] (h : PerfectPair (R := ZMod n) X Y) :
    Finite Y ∧ Finite X ∧ Nonempty (X ≃ₗ[ZMod n] Module.Dual (ZMod n) Y) ∧
      Nat.card Y = Nat.card X := by
  obtain ⟨hX, hY, P, hP, hP'⟩ := h
  have key := _root_.GlobalTheory.CompanionTheory.ZModDual.equiv_dual_of_injective_pair n Y X ⟨P, hP.1⟩ ⟨P.flip, hP'.1⟩
  exact ⟨hY, hX, key.1, key.2⟩

section Published

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
  (Av : S → ValuationSubring Ω)
  (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)

theorem shaDual_of_perfectPair
    (h1 : PerfectPair (R := ZMod (l ^ r)) (Sha2 ρ (locFam S Av) (continuous_locFam S Av))
      (Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)))
    (h2 : PerfectPair (R := ZMod (l ^ r)) (Sha2 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av))
      (Sha1 ρ (locFam S Av) (continuous_locFam S Av))) : ShaDual S Av μ ρ := by
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩
  exact ⟨shaHalf_of_perfectPair h1, shaHalf_of_perfectPair h2⟩

end Published

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsTransfer
section
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

section Abstract

variable {R : Type} [CommRing R]

theorem exact_of_transfer {A B C A' B' C' : Type} [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] [AddCommGroup C] [Module R C] [AddCommGroup A'] [Module R A'] [AddCommGroup B']
    [Module R B'] [AddCommGroup C'] [Module R C'] (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (f' : A' →ₗ[R] B') (g' : B' →ₗ[R] C') (eA : A ≃ₗ[R] A') (eB : B ≃ₗ[R] B') (eC : C ≃ₗ[R] C')
    (u v : Rˣ) (hf : ∀ a, f' (eA a) = u • eB (f a)) (hg : ∀ b, g' (eB b) = v • eC (g b))
    (h : Function.Exact f' g') : Function.Exact f g := by
  unfold Function.Exact at h ⊢
  intro b
  constructor
  · intro hb
    have h1 : g' (eB b) = 0 := by rw [hg, hb, map_zero, smul_zero]
    obtain ⟨a', ha'⟩ := (h (eB b)).1 h1
    refine ⟨(u : R) • eA.symm a', eB.injective ?_⟩
    have := hf (eA.symm a')
    rw [LinearEquiv.apply_symm_apply, ha'] at this
    rw [map_smul, map_smul, this, Units.smul_def]
  · rintro ⟨a, rfl⟩
    have h2 : g' (f' (eA a)) = 0 := (h _).2 ⟨_, rfl⟩
    rw [hf, Units.smul_def, map_smul, hg, ← Units.smul_def, smul_eq_zero_iff_eq,
      smul_eq_zero_iff_eq, LinearEquiv.map_eq_zero_iff] at h2
    exact h2

end Abstract

section Published

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
  (Av : S → ValuationSubring Ω)
  (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
  (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
  (hρ : ContAction ρ)

theorem nineTermExact_of_nineCmp
    (h : NineCmp (loc0 S Av ρ) (tr0 S Av μ j ρ) (loc1 S Av ρ) (tr1 S Av μ j ρ hρ)
      (loc2 S Av ρ) (tr2 S Av μ j ρ)) : NineTermExact S Av μ j ρ hρ := by
  obtain ⟨B0, B1, B2, B3, B4, B5, B6, B7, BetaSesquilinearity, g0, g1, g2, g3, g4, g5, g6, g7,
    e0, e1, e2, e3, e4, e5, e6, e7, e8, u, h0, h1, h3, h4, h6, h7,
    i0, x01, x12, x23, x34, x45, x56, x67, s7⟩ := h
  have k2 : ∀ a, g2 (e2 a) = (1 : (ZMod (l ^ r))ˣ) • e3 ((e3.symm.toLinearMap ∘ₗ g2 ∘ₗ e2.toLinearMap) a) := by
    intro a; rw [one_smul]; exact (e3.apply_symm_apply _).symm
  have k5 : ∀ a, g5 (e5 a) = (1 : (ZMod (l ^ r))ˣ) • e6 ((e6.symm.toLinearMap ∘ₗ g5 ∘ₗ e5.toLinearMap) a) := by
    intro a; rw [one_smul]; exact (e6.apply_symm_apply _).symm
  refine ⟨e3.symm.toLinearMap ∘ₗ g2 ∘ₗ e2.toLinearMap, e6.symm.toLinearMap ∘ₗ g5 ∘ₗ e5.toLinearMap,
    ?_, exact_of_transfer _ _ _ _ e0 e1 e2 _ _ h0 h1 x01,
    exact_of_transfer _ _ _ _ e1 e2 e3 _ _ h1 k2 x12,
    exact_of_transfer _ _ _ _ e2 e3 e4 _ _ k2 h3 x23,
    exact_of_transfer _ _ _ _ e3 e4 e5 _ _ h3 h4 x34,
    exact_of_transfer _ _ _ _ e4 e5 e6 _ _ h4 k5 x45,
    exact_of_transfer _ _ _ _ e5 e6 e7 _ _ k5 h6 x56,
    exact_of_transfer _ _ _ _ e6 e7 e8 _ _ h6 h7 x67, ?_⟩
  · intro a b hab
    apply e0.injective
    apply i0
    rw [h0, h0, hab]
  · intro y
    obtain ⟨b, hb⟩ := s7 (e8 y)
    refine ⟨((u 5 : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) • e7.symm b, e8.injective ?_⟩
    have := h7 (e7.symm b)
    rw [LinearEquiv.apply_symm_apply, hb] at this
    rw [map_smul, map_smul, this, Units.smul_def]

end Published

end PositivityTheory.Lit1.PTN
end
end

