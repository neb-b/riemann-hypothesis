module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.Bundle0008
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.Bundle0004
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.Bundle0005
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0119
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0165
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibLam
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]

theorem lam_zb (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (hD : IsDual A B P)
    (hD' : IsDual B A (swap P)) (l : A ⟶ B) [IsMonHom l] (mu : B ⟶ A) [IsMonHom mu] (α : Matrix (Fin 4) (Fin 4) ℤ)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L)) :
    pull (sqToBase (G4 (A ⊗ B)) s) (zc hD.isLB l mu α) =
      lam (cls (zb mu α s P L) (isLB_zb mu α s hD.isLB hL)) (fst _ _) (snd _ _) := by
  haveI : IsCommMonObj A := hA.comm
  have hw : sqToBase (G4 (A ⊗ B)) s = Over.Hom.left (lift
      (toBase (G4 (A ⊗ B)) s (fst ((Over.pullback s).obj (G4 (A ⊗ B))) ((Over.pullback s).obj (G4 (A ⊗ B)))))
      (toBase (G4 (A ⊗ B)) s (snd ((Over.pullback s).obj (G4 (A ⊗ B))) ((Over.pullback s).obj (G4 (A ⊗ B)))))) := rfl
  rw [zc, hw, pull_zcPair, lift_fst, lift_snd]
  have hc : cls (zb mu α s P L) (isLB_zb mu α s hD.isLB hL) =
      cls (L.LinComb (phiL mu s) fun _ => 1) (LB.isLB_linComb hL _ _) +
        cls (P.LinComb (phiP s) fun ij => α ij.1 ij.2) (LB.isLB_linComb hD.isLB _ _) :=
    cls_tens (LB.isLB_linComb hL _ _) (LB.isLB_linComb hD.isLB _ _) (isLB_zb mu α s hD.isLB hL)
  rw [hc, cls_linComb hL, cls_linComb hD.isLB]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [lam_eq_lamHom, map_add (f := _), map_sum, map_sum]
  simp only [map_zsmul, one_smul, ← lam_eq_lamHom, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_four, line_bundle_pairing_zeroth hD l mu s L hL e, line_bundle_pairing_first hD hD' l mu s L hL e,
    line_bundle_pairing_second hD l mu s L hL e, line_bundle_pairing_third hD hD' l mu s L hL e, lam_phiP hD hD' s, zcPair, smul_add]
  abel

end PositivityTheory.PrwZar
end
end

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.PolFibreIsogAny
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

namespace PositivityTheory.PrwZar.Z2

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Ar.GR

theorem polFibreIsogAny : PositivityTheory.PrwZar.PolFibreIsogAny := by
  intro C _ _ v R _ _ hv A B _ _ P l g hA hB hgA hgB hD hD' hp Ω _ _ s
  have : IsMonHom l := hp.1
  obtain ⟨L, hL, ha, e⟩ := hp.2 Ω s
  have hA' := GlobalTheory.isAbelianScheme_pullback_obj s A hA
  have hB' := GlobalTheory.isAbelianScheme_pullback_obj s B hB
  have hgA' := GlobalTheory.FiniteData.relDim_pullback s A hgA
  have hgB' := GlobalTheory.FiniteData.relDim_pullback s B hgB
  haveI := hA'.comm
  obtain ⟨H, j, -, hH, hK⟩ := _root_.GlobalTheory.KernelRep.exists_finite_closed_kernel GlobalTheory.globalFns_holds Ω ((Over.pullback s).obj A) hA' L hL ha
  have hfin : IsFinite ((Over.pullback s).map l).left :=
    isFinite_of_ker hA' hB' _ H j hH fun T x hx => (hK T x).1 (ker_memKL hD l s L hL e x hx)
  obtain ⟨hfl, hsu⟩ := flat_surj_of_finite hA' hB' g hgA' hgB' _ hfin
  exact ⟨hfin, hfl, hsu⟩

end PositivityTheory.PrwZar.Z2
end
end

