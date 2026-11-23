module

public import Mathlib
public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Formalism.LocalRingCardinality.HostCls

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.OrbitLabellings.EvenAddOrderOfHPOfPowLe
section
open scoped BigOperators
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Classical

theorem UpperTheory.even_addOrderOf_hP_of_pow_le :
    (∀ (R : Ranks) (t : R.A), Odd (addOrderOf t) → R.toFrame.h t = 0 ∧ addOrderOf t ∣ R.toFrame.o) ∧
    ∀ (D : D7) (L : SizeData₂ D) (p : ℕ), L.sc.x ^ (L.sc.eps / 4) ≤ (addOrderOf (hP D p) : ℝ) → Even (addOrderOf (hP D p)) := by
  have key : ∀ (R : Ranks) (t : R.A), Odd (addOrderOf t) →
      R.toFrame.h t = 0 ∧ addOrderOf t ∣ R.toFrame.o := by
    intro R t ho
    have h1 := R.toFrame.addOrderOf_h_dvd t
    have h2 := R.toFrame.addOrderOf_h_dvd_two_pow t
    have hcop : Nat.Coprime (addOrderOf t) (2 ^ R.toFrame.e) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 ho)
    have h3 : addOrderOf (R.toFrame.h t) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    have h0 : R.toFrame.h t = 0 := AddMonoid.addOrderOf_eq_one_iff.1 h3
    exact ⟨h0, addOrderOf_dvd_iff_nsmul_eq_zero.2 (R.toFrame.o_nsmul_of_h_eq_zero h0)⟩
  refine ⟨key, fun D L p hx => ?_⟩
  by_contra hne
  have hd := (key D.R (hP D p) (Nat.not_even_iff_odd.1 hne)).2
  have hle : addOrderOf (hP D p) ≤ D.R.toFrame.o := Nat.le_of_dvd D.R.toFrame.o_pos hd
  have hle' : (addOrderOf (hP D p) : ℝ) ≤ (D.R.o : ℝ) := by exact_mod_cast hle
  have hlt : L.sc.x ^ (L.sc.eps / 100) < L.sc.x ^ (L.sc.eps / 4) :=
    Real.rpow_lt_rpow_of_exponent_lt L.sc.one_lt_alt (by linarith [L.sc.eps_pos])
  linarith [L.o_tie]
end

-- bundled from Development.AutomorphicArithmetic.OrbitLabellings.GalEArithFrobEqIotaHP
section
open scoped BigOperators
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Classical

theorem UpperTheory.galE_arithFrob_eq_iota_hP :
    ∀ (D : D7) (p : ℕ), p.Prime → IsResidueClassZero D p →
    ∀ (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] (σ : D.host.E ≃ₐ[ℚ] D.host.E), IsArithFrobAt ℤ σ P →
    D.host.galE σ = (Formalism.FrobeniusOrbits.c0, D.R.iota (hP D p)) ∧ orderOf (D.host.galE σ).2 = addOrderOf (hP D p) := by
  intro D p hp hc P hP1 hP2 σ hσ
  have hcl : primeClass D.host.toHostRaw p = PrimeClass.inertClass := hc
  obtain ⟨hN, hj, hps⟩ := (primeClass_eq_inert_iff_symbols hp).1 hcl
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime p D.host.condN := hp.coprime_iff_not_dvd.2 hN
  have hne : ∃ g, g ∈ frobSet D p := ⟨_, P, hP1, hP2, σ, hσ, rfl⟩
  obtain ⟨P', hP'1, hP'2, σ', hσ', hg⟩ := Classical.epsilon_spec hne
  have e1 := (D.host.frob_iff p hcop P σ).1 hσ
  have e2 := (D.host.frob_iff p hcop P' σ').1 hσ'
  have h1 : (D.host.galE σ).1 = Formalism.FrobeniusOrbits.c0 := (D.host.hostClasses p hN P σ hσ).2.2.2 ⟨hj, hps⟩
  have h2 : (D.host.galE σ).2 = D.R.iota (hP D p) := by
    unfold hP
    rw [Formalism.HC.Frame.iota_iotaInv, ← hg, e1, e2]
  exact ⟨Prod.ext h1 h2, by rw [h2, Formalism.HC.Frame.orderOf_iota]⟩
end

-- bundled from Development.AutomorphicArithmetic.OrbitLabellings.NotIsCsOfGIdx
section
noncomputable section

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions

namespace Formalism.MainNotions.G

theorem frobSet_ne' (D : D7) {p : ℕ} (hp : p.Prime) : ∃ g, g ∈ frobSet D p := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have : IsGaloisGroup (D.host.E ≃ₐ[ℚ] D.host.E) ℤ (𝓞 D.host.E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ D.host.E
  obtain ⟨P, hP, hlo⟩ := (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)))
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {(p : ℤ)}) (by simpa using hpZ.ne_zero) P
  have : Finite (𝓞 D.host.E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hne
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (D.host.E ≃ₐ[ℚ] D.host.E) P
  exact ⟨_, P, hP, hlo, σ, hσ, rfl⟩

theorem hEv_of_hNeZero {D : D7} {p : ℕ} (hp : p.Prime) (hN : HNeZero D.host p) : HEv D p := by
  obtain ⟨P, hP', hL, σ, hσ, hg⟩ := Classical.epsilon_spec (frobSet_ne' D hp)
  have h1 := @hN P hP' hL σ hσ
  rw [hg] at h1
  exact h1

end Formalism.MainNotions.G

end
end

