module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.Bundle0002

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem absorb (A N t e : ℝ) (k : ℕ) (hA : 0 ≤ A) (hk : A ≤ 16 ^ k) (hN : 16 ≤ N) (he : 0 ≤ e) (het : e ≤ t)
    (ht : 1 ≤ t) : A * N * N ^ 18 * e ^ 7 ≤ (N * t) ^ (k + 19) := by
  have h0 : 0 ≤ N := by linarith
  have h1 : A ≤ N ^ k := hk.trans (pow_le_pow_left₀ (by norm_num) hN k)
  have h2 : e ^ 7 ≤ t ^ (k + 19) := (pow_le_pow_left₀ he het 7).trans (pow_le_pow_right₀ ht (by omega))
  calc A * N * N ^ 18 * e ^ 7 ≤ N ^ k * N * N ^ 18 * t ^ (k + 19) := by gcongr
    _ = (N * t) ^ (k + 19) := by ring
