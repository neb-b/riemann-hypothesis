module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.OfSupportHolds
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.QuadraticCharpolySplitting.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0344

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af
open UpperTheory.V UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Kato.WeilSphericalRecords.SphericalReciprocity

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem exists_unr {ξ : kˣ →* ℂˣ} (h : IsUnram ξ) : ∃ a : ℂˣ, ξ = unrChar k a := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.PrinTwo.NoFix.exists_unif k
  exact ⟨_, eq_unrChar h hϖ⟩

private theorem unr_eq {a b : ℂˣ} (h : (a : ℂ) = (resCard k : ℂ) * b) : unrChar k b = unrChar k a * absPow k 1 := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.PrinTwo.NoFix.exists_unif k
  have hU : IsUnram (unrChar k a * absPow k 1) := fun u hu => by
    rw [MonoidHom.mul_apply, isUnram_unrChar k a u hu, isUnram_absPow k 1 u hu, one_mul]
  rw [eq_unrChar hU hϖ]
  congr 1
  refine Units.ext ?_
  simp only [MonoidHom.mul_apply, Units.val_mul]
  rw [unrChar_uniformizer k a hϖ, val_absPow, Complex.cpow_one, h]
  have hn : nabs k ϖ = (resCard k : ℝ)⁻¹ := by
    rw [GlobalTheory.LGrp.nabs_eq_zpow, ord_eq_one hϖ]; simp
  have hq : (resCard k : ℂ) ≠ 0 := by
    have : (1 : ℝ) < resCard k := by exact_mod_cast one_lt_resCard (k := k)
    exact_mod_cast (by positivity : (resCard k : ℝ) ≠ 0)
  rw [hn]
  push_cast
  field_simp

end Loc

section WD

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem unr_of_level {n : ℕ} {x : WD h} (hL : IsLevelWD 1 n x) : x.unr := by
  obtain ⟨χ, b, hχ, e, hN, hb⟩ := hL
  have h1 : ((1 : ℕ) : 𝓞 E) ∉ w.asIdeal := by
    rw [Nat.cast_one]
    exact fun h1 => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  rw [← e, WD.unr_mk]
  refine ⟨hN, fun s => ?_⟩
  rw [hb s]
  simp [fun i => hχ i s (UpperTheory.inertia_fixes_roots_of_unity_prime_to_residue_char E Ω w A h 1 h1 s s.2), Module.End.one_eq_id]

private theorem eq_one_of_root {x : WD h} (hu : x.unr) (t : Ine (F := E) A) {z : ℂ}
    (hz : (x.charPol (ineIncl h t)).IsRoot z) : z = 1 := by
  obtain ⟨m, b, rfl⟩ := x.exists_rep
  rw [WD.unr_mk] at hu
  rw [WD.charPol_mk, hu.2 t, ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hz
  obtain ⟨v, hv⟩ := hz.exists_hasEigenvector
  have h3 := hv.apply_eq_smul
  exact smul_left_injective ℂ hv.2 (by simpa using h3.symm)

end WD

end UpperTheory.V.Z.Kato.WeilSphericalRecords.SphericalReciprocity

