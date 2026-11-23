module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Counts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.TorsClass
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0014

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X

theorem UpperTheory.V.X.propZ :
    HV.PropZ := by
  intro Ω _ _ _ l _ c e h5 h2 hev hd
  by_cases h : l - 1 ∣ e
  · exact UpperTheory.V.X.zOne Ω l c.O (by omega) e (by omega) h
  · exact UpperTheory.V.X.zQuad Ω l c.O h5 e hev hd h
