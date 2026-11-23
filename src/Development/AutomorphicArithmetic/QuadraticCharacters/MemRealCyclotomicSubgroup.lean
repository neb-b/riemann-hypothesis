module

public import Development.AutomorphicArithmetic.QuadraticCharacters.PreHostA

@[expose] public section

namespace HostParam

namespace AbField

variable (E : AbField)

end AbField

structure Core where
  e : ℕ
  two_le_e : 2 ≤ e
  E : AbField
  not_real : ¬ E.IsReal
  d : ℕ
  d_prime : d.Prime
  d_mod : d % 16 = 7
  d_dvd : d ∣ E.N
  K_le : E.chOf d d_dvd ∈ E.chars
  card_inertia_d : Nat.card (E.inertia d) = 2
  ps : DirichletCharacter ℂ E.N
  ps_mem : ps ∈ E.chars
  ps_ne_one : ps ≠ 1
  ps_sq : ps ^ 2 = 1
  ps_odd : ps.Odd
  ps_inertia : ∀ u ∈ E.inertiaUnits d, ps (u : ZMod E.N) = 1
  four_n_dvd : 4 * 2 ^ e ∣ E.N
  attached_subfield_le_adjoin_simple : ∀ u ∈ E.H, ZMod.unitsMap four_n_dvd u = 1 ∨ ZMod.unitsMap four_n_dvd u = -1
  A0 : Subgroup E.Gal
  base_exponent_le_a : A0 ≤ (E.toGalChar (E.chOf d d_dvd) K_le).ker ⊓ (E.toGalChar ps ps_mem).ker
  A0_inf_stabilizer_trivial : ∀ u : (ZMod E.N)ˣ, E.res u ∈ A0 →
    (QuotientGroup.mk (ZMod.unitsMap four_n_dvd u) : GalRealCyclotomic (2 ^ e)) = 1 → E.res u = 1
  split_ram : ∀ l : ℕ, l.Prime → l ≠ d → E.Ramified l → SplitsIn d l

namespace Core

variable (C : Core)



end Core

end HostParam
