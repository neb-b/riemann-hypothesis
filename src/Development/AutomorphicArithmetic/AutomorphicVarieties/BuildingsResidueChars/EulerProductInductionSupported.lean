module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EulerProductInductionUnramified
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeParametersTwistedAutomorphic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.NormLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0629
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191

@[expose] public section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem unr_cancel {a b : kˣ →* ℂˣ} (ha : IsUnram a) (hab : IsUnram (a * b)) : IsUnram b := fun x hx => by
  have h := hab x hx
  rwa [MonoidHom.mul_apply, ha x hx, one_mul] at h

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem unr_inv {a : kˣ →* ℂˣ} (ha : IsUnram a) : IsUnram a⁻¹ := fun x hx => by
  rw [MonoidHom.inv_apply, ha x hx, inv_one]


private theorem lin_zero (a : kˣ →* ℂˣ) : (lin a).eval 0 = 1 := by
  unfold lin
  split_ifs <;> simp

end Loc

private theorem unrAt_iff {F : Type} [Field F] [NumberField F] (χ : HChar F) (w : HeightOneSpectrum (𝓞 F)) :
    χ.UnrAt w ↔ IsUnram (χ.loc w) := by
  haveI : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  refine forall_congr' fun x => imp_congr_left ?_
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion F)) Valued.v).eq_one_iff_eq_one.symm

private theorem unr_iff (u : Ad3.Pl) (a : (u.adicCompletion ℚ)ˣ →* ℂˣ) : IsUnramifiedChar a ↔ IsUnram a := by
  haveI : (Valued.v : Valuation (u.adicCompletion ℚ) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [isUnramifiedChar_iff]
  refine forall_congr' fun x => imp_congr_left ?_
  rw [Ad3P.DihedralUnramifiedPlaces.ord_eq u x.ne_zero, neg_eq_zero,
    (ValuativeRel.isEquiv (ValuativeRel.valuation (u.adicCompletion ℚ)) Valued.v).eq_one_iff_eq_one]
  have h0 : Valued.v (x : u.adicCompletion ℚ) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  constructor
  · intro h
    rw [← WithZero.exp_log h0, h, WithZero.exp_zero]
  · intro h
    rw [h, WithZero.log_one]

private theorem under_eq {K : Type} [Field K] [NumberField K] {p : Ad3.Pl} (w : PlacesOver K p) : w.1.under (𝓞 ℚ) = p :=
  HeightOneSpectrum.ext w.2.over.symm

private theorem exists_above (K : Type) [Field K] [NumberField K] (S : Finset Ad3.Pl) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ w, w ∈ T ↔ w.under (𝓞 ℚ) ∈ S := by
  refine ⟨S.biUnion fun p => (Finset.univ : Finset (PlacesOver K p)).map (Function.Embedding.subtype _), fun w => ?_⟩
  simp only [Finset.mem_biUnion, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp, w', rfl⟩
    change w'.1.under (𝓞 ℚ) ∈ S
    rwa [under_eq]
  · exact fun h => ⟨_, h, ⟨w, ⟨rfl⟩⟩, rfl⟩

private theorem tri_pow (a x : ℂˣ) (f : ℕ) :
    ((({a ^ f, 1, (a ^ f)⁻¹} : Multiset ℂˣ).map (· * x ^ f)).map fun b : ℂˣ => (b : ℂ)) = (tri a x).map (· ^ f) := by
  simp [tri, mul_pow]
