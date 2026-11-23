module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.NarrowCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0871
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertFrames.InertB

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
open PositivityTheory.Rg.BcN UpperTheory.BaseChangeIdentities UpperTheory.Zero.LLC GlobalTheory.PRep

namespace UpperTheory.One.M.Ud

attribute [local instance] GlobalTheory.CuspRep.host_isCMField

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def UnitaryReadS {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} (B : NBC A) (rc : RecMap A) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ R.m → ∀ π : B.AU j, ∃ U : Submodule ℂ (UA H.E R.nV → ℂ), IsAutRepU U ∧
    (∀ w : PlE H, IsSplitPl H w → ∀ σ : LocIrr w R.nV,
      IsCompAlong U (locU R.nV w) ((cLoc w).comp (locU R.nV w).subtype) σ.ρ → B.locAU j π w = rc w R.nV σ) ∧
    (∀ w : PlE H, ¬ IsSplitPl H w → B.sphAU j π w → GlobalTheory.DefiniteBCGood.GoodSplitU U ∧
      ∃ α, IsSatAt U w α ∧ B.satAU j π w = Finset.univ.val.map fun i => (α i : ℂ)) ∧
    ∀ τ : H.E →+* ℂ, ∃ lam, HasWeightAt U τ lam ∧ B.infW j (B.wtAU j π) τ = infOfWeight lam


open GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BCSupport in
theorem good_of_sph {E : Type} [Field E] [NumberField E] {c n : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n) (w : HeightOneSpectrum (𝓞 E))
    (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E))) (h1 : GlobalTheory.LGrp.IsSpherical (locProd h w σ) (GlobalTheory.LFun.KGL w (n := n))) (i) :
    Good (clsOf (σ i)) := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  let e := prodIrrEquiv (k := w.adicCompletion E) h (fun i => (σ i).ρ) (fun i => (σ i).smooth) (fun i => (σ i).irred)
  have h1' : GlobalTheory.LGrp.IsSpherical (prodIrr (fun i => clsOf (σ i)) h) (GlobalTheory.LFun.KGL w (n := n)) := isSpherical_of_equiv e h1
  have h3 : GlobalTheory.SmGL.IsSpherical (prodIrr (fun i => clsOf (σ i)) h) :=
    isSphericalFor_of_eq (GlobalTheory.CohomologicalConjSelfDualTempered.UnrModel.kgl_eq_ko w n) ((GlobalTheory.LGrp.isSpherical_iff _ _).1 h1')
  exact (GlobalTheory.SphSupport.toral_and_good_of_isSpherical GlobalTheory.bernsteinZelevinskyFiniteness_holds _ _
    (GlobalTheory.LocLanglands.SphFac.isSpherical_factor _ c n _ h _ _ (IsSubquotient.refl _) h3 i)).2


end UpperTheory.One.M.Ud

end
