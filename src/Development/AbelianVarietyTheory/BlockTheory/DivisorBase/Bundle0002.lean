module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Formalism.PairingDivisors.StatementN

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
section
noncomputable section

open WittVector Ideal Matrix GlobalTheory.Sandwich

namespace GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

section Eigen

variable {O : Type} [CommRing O] (C : Type) [Field C] [Algebra O C]
  {Λ : Type} [CommRing Λ] {h : ℕ}

def eig (ρ : Λ → Matrix (Fin h) (Fin h) O) (σ : Λ →+* O) : Submodule C (Fin h → C) :=
  ⨅ a : Λ, Module.End.eigenspace (Matrix.toLin' ((ρ a).map (algebraMap O C)))
    (algebraMap O C (σ a))

abbrev detLine (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O) (N : ℕ) : Type :=
  ⋀[C]^N (eig C ρ τ)

end Eigen

section Datum

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] (C : Type) [Field C] [Algebra O C]
  {ε : PreTilt O p} {h h' : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]

def redC {m n : ℕ} (X : Matrix (Fin m) (Fin n) (Ainf p O)) : (Fin n → C) →ₗ[C] (Fin m → C) :=
  Matrix.toLin' (X.map ((algebraMap O C).comp (fontaineTheta O p)))

def alC (D : Datum ε h Λ) : (Fin h → C) →ₗ[C] (Fin h → C) := redC C D.F

def bC (D : Datum ε h Λ) : (Fin h → C) →ₗ[C] (Fin h → C) := redC C D.G

end Datum

end GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
section
namespace GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi

section Fibres

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {Z : Scheme.{0}} (f : Z ⟶ Spec (.of O))

def specialFibre : Scheme.{0} :=
  pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))

def specialι : specialFibre f ⟶ Z := pullback.fst _ _

end Fibres

end

end GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
section
noncomputable section

open NumberField Module
open scoped nonZeroDivisors

namespace GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals

variable {F : Type} [Field F] [NumberField F]

abbrev IdealsIn (C : ClassGroup (𝓞 F)) : Type := {I : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 I = C}

def IsClassZeta (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ Z {1}ᶜ ∧ ∀ s : ℂ, 1 < s.re →
    HasSum (fun I : IdealsIn C => ((Ideal.absNorm (I.1 : Ideal (𝓞 F)) : ℕ) : ℂ) ^ (-s)) (Z s)

def IsZetaValues (k : ℕ) (z : ClassGroup (𝓞 F) → ℚ) : Prop :=
  ∀ C, ∃ Z : ℂ → ℂ, IsClassZeta C Z ∧ Z (1 - (k : ℂ)) = (z C : ℂ)

def denomExp (l : ℕ) (r : ℚ) : ℕ := (-padicValRat l r).toNat

def cE (z : ClassGroup (𝓞 F) → ℚ) (l : ℕ) : ℕ :=
  Finset.univ.sup fun C => denomExp l (z C / 2 ^ finrank ℚ F)

def mMin (l n : ℕ) : ℕ := sInf {m | ∃ a : ℕ, 2 ≤ a ∧ a.Coprime l ∧ m = padicValNat l (a ^ n - 1)}

def LocalBound (k : ℕ) (z : ClassGroup (𝓞 F) → ℚ) (l : ℕ) : Prop :=
  cE z l ≤ finrank ℚ F * padicValNat l 2 + mMin l (finrank ℚ F * k) ∧
  (l ≠ 2 → ¬ (l - 1) ∣ finrank ℚ F * k → mMin l (finrank ℚ F * k) = 0) ∧
  (l ≠ 2 → (l - 1) ∣ finrank ℚ F * k → mMin l (finrank ℚ F * k) = 1 + padicValNat l (finrank ℚ F * k)) ∧
  (l = 2 → mMin l (finrank ℚ F * k) = 2 + padicValNat 2 (finrank ℚ F * k))

def SumBound (k : ℕ) (z : ClassGroup (𝓞 F) → ℚ) : Prop :=
  (Function.support fun l : Nat.Primes => (cE z l : ℝ) * Real.log (l : ℕ)).Finite ∧
  ∑ᶠ l : Nat.Primes, (cE z l : ℝ) * Real.log (l : ℕ) ≤
    ((finrank ℚ F * k : ℕ) : ℝ) * Real.log (((finrank ℚ F * k : ℕ) : ℝ) + 1)

def DenomAt (F : Type) [Field F] [NumberField F] (k : ℕ) : Prop :=
  (∃ z : ClassGroup (𝓞 F) → ℚ, IsZetaValues k z) ∧
  ∀ z : ClassGroup (𝓞 F) → ℚ, IsZetaValues k z →
    (∀ l : ℕ, l.Prime → LocalBound k z l) ∧ (16 ≤ finrank ℚ F * k → SumBound k z)

def ZetaDenominators : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (s : ℕ), 1 ≤ s → DenomAt (maximalRealSubfield E) (2 * s)

def ZetaDenominatorsReal : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (s : ℕ), 1 ≤ s → DenomAt F (2 * s)

theorem ZetaDenominatorsReal.cm (h : ZetaDenominatorsReal) : ZetaDenominators :=
  fun E _ _ _ s hs => h (maximalRealSubfield E) s hs

theorem IsClassZeta.eqOn {C : ClassGroup (𝓞 F)} {Z Z' : ℂ → ℂ} (h : IsClassZeta C Z) (h' : IsClassZeta C Z') :
    Set.EqOn Z Z' {1}ᶜ := by
  have ho : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) 1).isPreconnected
  refine (h.1.analyticOnNhd ho).eqOn_of_preconnected_of_eventuallyEq (h'.1.analyticOnNhd ho) hc (z₀ := 2) (by norm_num) ?_
  have ho' : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [ho'.mem_nhds (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by simp)] with s hs
  exact (h.2 s hs).unique (h'.2 s hs)

theorem mMin_mem {l : ℕ} (hl : 1 ≤ l) (n : ℕ) : ∃ a : ℕ, 2 ≤ a ∧ a.Coprime l ∧ mMin l n = padicValNat l (a ^ n - 1) :=
  Nat.sInf_mem (s := {m | ∃ a : ℕ, 2 ≤ a ∧ a.Coprime l ∧ m = padicValNat l (a ^ n - 1)})
    ⟨_, l + 1, by omega, by simp, rfl⟩

theorem LocalBound.mMin_eq {k : ℕ} {z : ClassGroup (𝓞 F) → ℚ} {l : ℕ} (h : LocalBound k z l) :
    mMin l (finrank ℚ F * k) = Formalism.PairingDivisionLocalBalance.mE l (finrank ℚ F * k) := by
  unfold Formalism.PairingDivisionLocalBalance.mE
  split_ifs with h1 h2
  · exact h.2.2.2 h1
  · exact h.2.2.1 h1 h2
  · exact h.2.1 h1 h2

theorem pir_rat : IsPrincipalIdealRing (𝓞 ℚ) :=
  IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm.toRingHom Rat.ringOfIntegersEquiv.symm.surjective

theorem absNorm_span_rat (n : ℕ) : Ideal.absNorm (Ideal.span {(n : 𝓞 ℚ)}) = n := by
  rw [Ideal.absNorm_span_singleton, show (n : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (n : ℤ) by simp, Algebra.norm_algebraMap,
    RingOfIntegers.rank]
  simp

theorem exists_span_rat (I : Ideal (𝓞 ℚ)) : ∃ n : ℕ, I = Ideal.span {(n : 𝓞 ℚ)} := by
  haveI := pir_rat
  obtain ⟨a, rfl⟩ : ∃ a, I = Ideal.span {a} := ⟨_, (IsPrincipalIdealRing.principal I).span_singleton_generator.symm⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, a = (m : 𝓞 ℚ) := ⟨Rat.ringOfIntegersEquiv a, by
    apply Rat.ringOfIntegersEquiv.injective; simp⟩
  refine ⟨m.natAbs, ?_⟩
  rcases Int.natAbs_eq m with h | h
  · rw [h]; simp
  · conv_lhs => rw [h]
    rw [Int.cast_neg, Ideal.span_singleton_neg, Int.cast_natCast]

theorem isClassZeta_rat (C : ClassGroup (𝓞 ℚ)) : IsClassZeta C riemannZeta := by
  refine ⟨fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt, fun s hs => ?_⟩
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  haveI := pir_rat
  haveI : Subsingleton (ClassGroup (𝓞 ℚ)) :=
    (@Fintype.card_le_one_iff_subsingleton _ instFintypeClassGroupOfIsPrincipalIdealRing).1
      (card_classGroup_eq_one (R := 𝓞 ℚ)).le
  let g : IdealsIn C → ℕ := fun I => Ideal.absNorm (I.1 : Ideal (𝓞 ℚ))
  have hg : Function.Injective g := fun I J h => by
    obtain ⟨n, hn⟩ := exists_span_rat (I.1 : Ideal (𝓞 ℚ))
    obtain ⟨m, hm⟩ := exists_span_rat (J.1 : Ideal (𝓞 ℚ))
    simp only [g, hn, hm, absNorm_span_rat] at h
    exact Subtype.ext (Subtype.ext (by rw [hn, hm, h]))
  have hr : ∀ n ∉ Set.range g, (n : ℂ) ^ (-s) = 0 := fun n hn => by
    by_cases h0 : n = 0
    · simp [h0, hs0]
    · refine (hn ⟨⟨⟨Ideal.span {(n : 𝓞 ℚ)}, mem_nonZeroDivisors_of_ne_zero ?_⟩, Subsingleton.elim _ _⟩,
        absNorm_span_rat n⟩).elim
      simpa using h0
  refine (hg.hasSum_iff (f := fun n : ℕ => (n : ℂ) ^ (-s)) hr).2 ?_
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  simpa only [Complex.cpow_neg, one_div] using (Complex.summable_one_div_nat_cpow.2 hs).hasSum

end GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals
end
end

