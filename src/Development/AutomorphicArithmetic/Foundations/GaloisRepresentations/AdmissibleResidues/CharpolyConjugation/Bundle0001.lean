module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0034
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0040
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0024
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0033

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unlfrob
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.GalN UpperTheory.GalN.V
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private lemma root_inv {K L : Type*} [Field K] [Field L] (e : K ≃+* L) {n : ℕ} (g : GL (Fin n) K) (y : L)
    (h : ((g : Matrix (Fin n) (Fin n) K).charpoly.map e.toRingHom).IsRoot y) :
    y ≠ 0 ∧ (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).charpoly.map e.toRingHom).IsRoot y⁻¹ := by
  obtain ⟨x, rfl⟩ := e.surjective y
  have hx : (g : Matrix (Fin n) (Fin n) K).charpoly.IsRoot x :=
    (Polynomial.isRoot_map_iff (f := e.toRingHom) e.injective).1 h
  have hs : x ∈ spectrum K (g : Matrix (Fin n) (Fin n) K) :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.2 hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact spectrum.zero_notMem K (Units.isUnit g) hs
  have hi : x⁻¹ ∈ spectrum K ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    simpa using (spectrum.inv_mem_iff (r := Units.mk0 x hx0) (a := g)).1 (by simpa using hs)
  refine ⟨by simpa using hx0, ?_⟩
  have := (Polynomial.isRoot_map_iff (f := e.toRingHom) (x := x⁻¹) e.injective).2
    (Matrix.mem_spectrum_iff_isRoot_charpoly.1 hi)
  simpa using this
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unliso
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.GalN UpperTheory.GalN.V
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem isRoot_map_equiv {k : Type} [Field k] (ι : k ≃+* ℂ) (p : Polynomial k) (x : k) :
    (p.map ι.toRingHom).IsRoot (ι x) ↔ p.IsRoot x := by
  have h : (p.map ι.toRingHom).eval (ι x) = ι (p.eval x) := by
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_at_apply ι.toRingHom x
  rw [Polynomial.IsRoot.def, Polynomial.IsRoot.def, h]
  exact map_eq_zero_iff ι ι.injective

private theorem isRoot_charpoly_smul {k : Type} [Field k] {n : ℕ} (c : k) (hc : c ≠ 0)
    (M : Matrix (Fin n) (Fin n) k) (x : k) :
    (c • M).charpoly.IsRoot (c * x) ↔ M.charpoly.IsRoot x := by
  have h : Matrix.scalar (Fin n) (c * x) - c • M = c • (Matrix.scalar (Fin n) x - M) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, hij, mul_sub]
  rw [Polynomial.IsRoot.def, Polynomial.IsRoot.def, Matrix.eval_charpoly, Matrix.eval_charpoly, h,
    Matrix.det_smul]
  simp [hc]

private theorem ratio_smul {k : Type} [Field k] {n : ℕ} (ι : k ≃+* ℂ) (c : k) (hc0 : c ≠ 0)
    (M : Matrix (Fin n) (Fin n) k) (q : ℂ)
    (h : ∀ α : ℂ, (M.charpoly.map ι.toRingHom).IsRoot α →
      ¬ (M.charpoly.map ι.toRingHom).IsRoot (q * α)) :
    ∀ α : ℂ, ((c • M).charpoly.map ι.toRingHom).IsRoot α →
      ¬ ((c • M).charpoly.map ι.toRingHom).IsRoot (q * α) := by
  have key : ∀ y : ℂ, ((c • M).charpoly.map ι.toRingHom).IsRoot (ι c * y) ↔
      (M.charpoly.map ι.toRingHom).IsRoot y := by
    intro y
    obtain ⟨x, rfl⟩ := ι.surjective y
    rw [← map_mul, isRoot_map_equiv, isRoot_map_equiv, isRoot_charpoly_smul c hc0]
  intro α hα hβ
  have hιc : ι c ≠ 0 := (map_ne_zero_iff ι ι.injective).2 hc0
  have hα' : ι c * ((ι c)⁻¹ * α) = α := by field_simp
  have h1 : (M.charpoly.map ι.toRingHom).IsRoot ((ι c)⁻¹ * α) := by
    rw [← key, hα']
    exact hα
  refine h _ h1 ?_
  rw [← key]
  have h2 : ι c * (q * ((ι c)⁻¹ * α)) = q * α := by
    field_simp
  rw [h2]
  exact hβ
end

