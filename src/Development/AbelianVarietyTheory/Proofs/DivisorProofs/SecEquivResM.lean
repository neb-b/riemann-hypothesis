module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasicoherentOfLocallyIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AffGlue

structure Data (T : Scheme.{0}) where

  M : ∀ V : T.Opens, IsAffineOpen V → Type

  grp : ∀ V hV, AddCommGroup (M V hV)

  mod : ∀ V hV, Module Γ(T, V) (M V hV)

  ρ : ∀ {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V'), V' ≤ V → M V hV →+ M V' hV'
  ρ_smul : ∀ {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V)
    (a : Γ(T, V)) (m : M V hV), ρ hV hV' h (a • m) = resG T h a • ρ hV hV' h m
  ρ_self : ∀ {V : T.Opens} (hV : IsAffineOpen V) (h : V ≤ V) (m : M V hV), ρ hV hV h m = m
  ρ_ρ : ∀ {V V' V'' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (hV'' : IsAffineOpen V'') (h : V' ≤ V) (h' : V'' ≤ V') (m : M V hV),
    ρ hV' hV'' h' (ρ hV hV' h m) = ρ hV hV'' (h'.trans h) m

  loc_surj : ∀ {V : T.Opens} (hV : IsAffineOpen V) (f : Γ(T, V)) (hD : IsAffineOpen (T.basicOpen f))
    (m : M (T.basicOpen f) hD), ∃ (n : ℕ) (x : M V hV),
      resG T (T.basicOpen_le f) f ^ n • m = ρ hV hD (T.basicOpen_le f) x

  loc_inj : ∀ {V : T.Opens} (hV : IsAffineOpen V) (f : Γ(T, V)) (hD : IsAffineOpen (T.basicOpen f))
    (x : M V hV), ρ hV hD (T.basicOpen_le f) x = 0 → ∃ n : ℕ, f ^ n • x = 0

attribute [instance] Data.grp Data.mod

variable {T : Scheme.{0}} (D : Data T)

variable {D}

end GlobalTheory.AffGlue
