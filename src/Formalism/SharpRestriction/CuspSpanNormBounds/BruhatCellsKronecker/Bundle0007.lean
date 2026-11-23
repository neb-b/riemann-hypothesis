module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.GlobalConditionOfProductFormula
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellDef
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0006

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyPacketOfLocalModelsApprox
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocalSplitGroups Formalism.MainNotions.JointEigenvalueBoundsFromAnyDatum Formalism.MainNotions.LocalModelPeriodLattices
open scoped nonZeroDivisors

section Blocks

variable {A B : Type} [Monoid B] (f : ℕ → ℕ → A → B)

end Blocks

section Van

variable {D : Formalism.BasicNotions.D7}

end Van

section Top

variable {D : Formalism.BasicNotions.D7}

end Top

section Red2

open scoped ComplexOrder
open Formalism.MainNotions

variable {D : Formalism.BasicNotions.D7}

variable {eps : ℝ} (Fm : FamP eps) {Y : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)}

end Red2

end Formalism.MainNotions.BridgeLemma

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilySeparationBound
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
open scoped nonZeroDivisors NumberField

theorem szf_finrankE (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.der.finrank_E]
  simp only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
  omega

theorem szf_finrankF (D : D7) : Module.finrank ℚ D.host.F = D.R.f := by
  rw [D.host.der.finrank_F]
  simp only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]

theorem szf_finrankFE (D : D7) : Module.finrank D.host.F D.host.E = 2 := by
  have h1 := D.host.der.finrank_E
  have h2 := D.host.der.finrank_F
  have h3 : Module.finrank ℚ D.host.F * Module.finrank D.host.F D.host.E = Module.finrank ℚ D.host.E :=
    Module.finrank_mul_finrank ℚ D.host.F D.host.E
  have hpos : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
  rw [h1, h2] at h3
  rw [h1] at hpos
  have h4 : 2 * D.R.ord * Module.finrank D.host.F D.host.E = 2 * D.R.ord * 2 := by rw [h3]; ring
  exact Nat.eq_of_mul_eq_mul_left (by omega) h4

theorem szf_rd_pow (D : D7) : (D.host.rdE ^ D.R.f) ^ 2 = |(NumberField.discr D.host.E : ℝ)| := by
  have hE := szf_finrankE D
  have hpos : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
  have hf : 0 < D.R.f := by omega
  have hx0 : (0 : ℝ) ≤ |(NumberField.discr D.host.E : ℝ)| := abs_nonneg _
  unfold Formalism.BasicNotions.Host.rdE
  rw [hE, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
  have hc : (1 : ℝ) / ((2 * D.R.f : ℕ) : ℝ) * ((D.R.f * 2 : ℕ) : ℝ) = 1 := by
    rw [mul_comm D.R.f 2]
    exact one_div_mul_cancel (Nat.cast_ne_zero.mpr (by omega))
  rw [hc, Real.rpow_one]

theorem szf_normDD (D : D7) (hd : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2) : SzfNormDD D := by
  unfold SzfNormDD
  rw [szf_rd_pow D, hd]
  have hFE := szf_finrankFE D
  have gen : ∀ I : Ideal (𝓞 D.host.F), Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) I) =
      Ideal.absNorm I ^ Module.finrank (𝓞 D.host.F) (𝓞 D.host.E) := by
    intro I
    rw [← Ideal.absNorm_relNorm (𝓞 D.host.F), Ideal.relNorm_algebraMap, map_pow]
  have n2 : ∀ (K : Type) [Field K] [NumberField K],
      (Algebra.norm ℤ (2 : 𝓞 K)).natAbs = 2 ^ Module.finrank ℚ K := by
    intro K _ _
    rw [show (2 : 𝓞 K) = algebraMap ℤ (𝓞 K) 2 from (map_ofNat _ 2).symm, Algebra.norm_algebraMap,
      NumberField.RingOfIntegers.rank, Int.natAbs_pow]
    rfl
  have hR : Module.finrank (𝓞 D.host.F) (𝓞 D.host.E) = 2 := by
    have h2 := gen (Ideal.span {(2 : 𝓞 D.host.F)})
    rw [Ideal.map_span, Set.image_singleton, map_ofNat, Ideal.absNorm_span_singleton,
      Ideal.absNorm_span_singleton, n2, n2, szf_finrankE D, szf_finrankF D, ← pow_mul] at h2
    have h3 := Nat.pow_right_injective (le_refl 2) h2
    have hpos : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    rw [szf_finrankE D] at hpos
    have h4 : D.R.f * Module.finrank (𝓞 D.host.F) (𝓞 D.host.E) = D.R.f * 2 := by
      rw [← h3]; ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) h4
  have key : Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
      (differentIdeal ℤ (𝓞 D.host.F))) = Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F)) ^ 2 := by
    rw [gen, hR]
  have hc : FractionalIdeal.absNorm (Formalism.MainNotions.S.ddE D) =
      (Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
        (differentIdeal ℤ (𝓞 D.host.F))) : ℚ) := by
    first
    | exact FractionalIdeal.coeIdeal_absNorm _
    | exact FractionalIdeal.absNorm_coeIdeal _
    | exact FractionalIdeal.coe_absNorm _
  have hd2 : Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F)) = (NumberField.discr D.host.F).natAbs := by
    exact NumberField.absNorm_differentIdeal D.host.F (𝓞 D.host.F)
  rw [hc, key, hd2]
  push_cast
  first
  | simp [abs_pow, Nat.cast_natAbs]
  | rw [Nat.cast_natAbs, Int.cast_abs, abs_pow]

end Formalism.MainNotions.BridgeLemma

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.UnitriangularFrameLift
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals NumberField Module IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def EqualFlagsScalar : Prop :=
  ∀ (K E : Type) [Field K] [Field E] [NumberField E] [StarRing E] [Algebra K E] (S : HSpace E) (r : ℕ) (T : E)
    (F F' : FlagG S r T), T ≠ 0 →
    (∀ x : E, algebraMap K E (Algebra.trace K E x) = x + star x) →
    (∀ j, F'.Xa j = F.Xa j) → F'.Xplus = F.Xplus → Relevant K F F' →
    ∃ c : E, c * star c = 1 ∧ (∀ a, F'.e a - c • F.e a ∈ F.Xa a.val) ∧ F'.z - c • F.z ∈ F.X

def ScalarRootOfUnity : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T : E) (Λ : Submodule (𝓞 E) S.V)
    (F F' : LFlag S r T) (c : E), StarConj E →
    F'.fl.z ∈ Λ → (∀ d : E, d • F.fl.z ∈ Lsub Λ F → ∃ o : 𝓞 E, (o : E) = d) →
    c * star c = 1 → F'.fl.z - c • F.fl.z ∈ Xsp F → F'.fl.X = F.fl.X →
    ∃ o : 𝓞 E, (o : E) = c ∧ ∃ N : ℕ, 0 < N ∧ o ^ N = 1

def ScalarCongruentOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T : ℕ) (Λ : Submodule (𝓞 E) S.V) (g : ℕ)
    (F F' : LFlag S r (T : E)) (o : 𝓞 E),
    Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ → F.fl.z ∈ Λ → IsAdmissible Λ g F F' →
    F'.fl.z - (o : E) • F.fl.z ∈ Xsp F →
    ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → (T : 𝓞 E) ∉ P.asIdeal → o - 1 ∈ P.asIdeal

def RootsOfUnityFormal : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (ζ : R) (N : ℕ) (g1 g2 : ℕ) (P1 P2 : Ideal R), 0 < N → ζ ^ N = 1 →
    g1.Prime → g2.Prime → g1 ≠ g2 → P1 ≠ ⊤ → P2 ≠ ⊤ → (g1 : R) ∈ P1 → (g2 : R) ∈ P2 → ζ - 1 ∈ P1 → ζ - 1 ∈ P2 → ζ = 1

def ExistsPrimeAbove : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → ∃ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal

def UnitriangularFrameLift (D : D7) : Prop :=
  ∀ (T : D.host.E) (Λ : Submodule (𝓞 D.host.E) (hS D).V) (F F' : LFlag (D.sp.Y 0) D.R.rS T),
    FixedHyp D Λ F → IsLift Λ F' → IsFixedConv Λ (gS D) F' →
    (∀ a, F'.fl.e a - F.fl.e a ∈ Xflag F a.val) → F'.fl.z - F.fl.z ∈ Xsp F →
    ∃ n ∈ NLam Λ F, ∀ a, n (F.fl.e a) = F'.fl.e a

theorem id_coprime_notMem {R : Type} [CommRing R] (P : Ideal R) (hP : P ≠ ⊤) (a b : ℕ) (h : Nat.Coprime a b)
    (ha : (a : R) ∈ P) : (b : R) ∉ P := by
  intro hb
  apply hP
  rw [Ideal.eq_top_iff_one]
  have h' : ((Nat.gcd a b : ℕ) : ℤ) = (a : ℤ) * Nat.gcdA a b + (b : ℤ) * Nat.gcdB a b := Nat.gcd_eq_gcd_ab a b
  rw [Nat.Coprime.gcd_eq_one h] at h'
  have h'' : (1 : R) = (a : R) * (Nat.gcdA a b : R) + (b : R) * (Nat.gcdB a b : R) := by
    have := congrArg (fun z : ℤ => (z : R)) h'
    push_cast at this
    exact this
  rw [h'']
  exact P.add_mem (P.mul_mem_right _ ha) (P.mul_mem_right _ hb)

end Formalism.MainNotions.BridgeLemma

end
end

