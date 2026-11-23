module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsPolynomialPairFunctionalEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EulerProductAdjointEqStandard
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK

@[expose] public section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

private theorem unr_of {η : HeckeCharacter ℚ} {v : Ad3.Pl} (h : (toH η).UnrAt v) :
    IsUnramifiedChar (localChar η v) := by
  refine isUnramifiedChar_iff.2 fun x hx => ?_
  rw [← Ad3P.DihedralUnramifiedPlaces.loc_eq]
  apply h x
  show Valued.v (x : Ad3.Qv v) = 1
  rw [Ad3P.DihedralUnramifiedPlaces.ord_eq v x.ne_zero, neg_eq_zero] at hx
  have h0 : Valued.v (x : Ad3.Qv v) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  rw [← WithZero.exp_log h0, hx, WithZero.exp_zero]

private theorem unr_mul {c η : HeckeCharacter ℚ} {v : Ad3.Pl} (h₁ : IsUnramifiedChar (localChar c v))
    (h₂ : IsUnramifiedChar (localChar η v)) : IsUnramifiedChar (localChar (c * η) v) := by
  refine isUnramifiedChar_iff.2 fun x hx => ?_
  have e : localChar (c * η) v x = localChar c v x * localChar η v x := Units.ext rfl
  rw [e, isUnramifiedChar_iff.1 h₁ x hx, isUnramifiedChar_iff.1 h₂ x hx, one_mul]

private theorem val_mul' (c η : HeckeCharacter ℚ) (v : Ad3.Pl) :
    (toH (c * η)).val v = (toH c).val v * (toH η).val v := Units.ext rfl

private theorem norm_val (c : HeckeCharacter ℚ) (v : Ad3.Pl) : ‖((toH c).val v : ℂ)‖ = 1 :=
  Circle.norm_coe _

private theorem tri_mul (a x y : ℂˣ) : tri a (x * y) = (tri a x).map (· * (y : ℂ)) := by
  simp [tri, mul_assoc]
