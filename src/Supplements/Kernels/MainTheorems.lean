module

public import Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip
public import Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion

@[expose] public section

open Complex DirichletCharacter

theorem allChi : UpperTheory.EveryCharacter := UpperTheory.FinalTheorems.everyCharacter

theorem rhOfAll : RiemannHypothesis := Claim.zeta allChi

theorem claimAll : Claim.HalfPlane ∧ Claim.Strip ∧ Claim.Zeta :=
  ⟨allChi, Claim.strip allChi, rhOfAll⟩

theorem critAll (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (_hχ : χ.IsPrimitive) (s : ℂ)
    (h0 : 0 < s.re) (h1 : s.re < 1) (hz : LFunction χ s = 0) : s.re = 1 / 2 :=
  claimAll.2.1 N χ s h0 h1 hz
