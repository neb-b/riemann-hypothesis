module

public import Development.AutomorphicArithmetic.CoprimeRanks.SecondSetNoRelation
public import Development.AutomorphicArithmetic.CoprimeRanks.OfPInjective
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.AnyLevel
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.OfRawToHostRaw

@[expose] public section

open NumberField Formalism.FrobeniusOrbits Formalism.HC

noncomputable section

namespace HostParam.Seam

variable {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M))

private theorem conductor_divisor_bounds {φ : Frame} {H : HostRaw φ} {e b : ℕ} (hQ : H.QS ∣ Nat.lcm (2 ^ (e + 2)) M) (hb : 4 * M ≤ b) :
    (∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ H.QS → l ∣ M ∧ 4 * l ≤ b) ∧ H.QS ≤ 4 * M * 2 ^ e := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have h1 := hQ.trans (Nat.lcm_dvd_mul _ _)
  refine ⟨fun l hl h2 h => ?_, (Nat.le_of_dvd (by positivity) h1).trans (le_of_eq (by ring))⟩
  have h3 : l ∣ M := (hl.dvd_mul.1 (h.trans h1)).resolve_left fun h4 =>
    h2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow h4))
  have := Nat.le_of_dvd hM h3
  exact ⟨h3, by omega⟩

end HostParam.Seam

end
