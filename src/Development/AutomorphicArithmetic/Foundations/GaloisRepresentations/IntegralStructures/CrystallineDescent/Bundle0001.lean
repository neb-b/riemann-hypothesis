module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PatchOneAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1475
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1498
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
public import CompanionTheory.AutomorphicTheory.PlaceSeparation.ArtinA

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.AutTHolds
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open GlobalTheory.PRep Formalism.UG GlobalTheory.BCT

theorem UpperTheory.Gal.Int.Core.autT_holds : UpperTheory.Gal.Int.Core.AutT := by
  classical
  intro E _ _ _ a U hU
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU.ne_bot
  let L : Subgroup (finU (E := E) (n := a)) :=
    { carrier := {k | RU E a k φ = φ}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at *
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hLo : IsOpen (L : Set (finU (E := E) (n := a))) := (hU.aut φ hφ).level
  have hunr : ∀ᶠ w in Filter.cofinite, IsUnramU U w := by
    filter_upwards [GlobalTheory.T.eventually_localIntegralPoints_mem_openSubgroup_definiteUnitary E a L hLo] with w hw
    exact ⟨φ, hφ, hφ0, fun x hx hxK => hw x hx hxK hx.1⟩
  have hfin : {w | ¬ IsUnramU U w}.Finite := hunr
  refine ⟨hfin.toFinset.filter (fun w => ¬ IsSplitAt w), fun w hw => (Finset.mem_filter.1 hw).2, hU, fun w hs hT => ?_⟩
  by_contra hn
  exact hT (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hn, hs⟩)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PhiPol
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core

theorem UpperTheory.Gal.Int.Core.phiPol_holds :
    PhiPol := by
  intro F Ω _ _ _ _ _ A w h x y σ hs
  have split : ∀ z : WD h, ((z.charPol σ).roots.map fun a => X - C a).prod = z.charPol σ := by
    intro z
    induction z using WD.ind with
    | hP n a =>
      rw [WD.charPol_mk]
      exact Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (LinearMap.charpoly_monic _)
        (IsAlgClosed.splits _).natDegree_eq_card_roots.symm
  have hc : Multiset.card (x.charPol σ).roots = Multiset.card (y.charPol σ).roots := by
    have h0 := hs 0
    simp only [GlobalTheory.CongPhi.phiSum, pow_zero, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one] at h0
    exact_mod_cast h0
  rw [← split x, ← split y]
  exact GlobalTheory.CharpolyNewton.prod_eq_of_psum_eq _ _ hc hs
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.RamUnr
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace UpperTheory.Gal.Int.Core

theorem ramUnr_holds : RamUnr := by
  intro F Ω _ _ _ _ _ T Q hQ
  obtain ⟨u, huT, A, hA, τ, hτ, hfix⟩ := hQ
  haveI : Algebra.IsQuadraticExtension F ↥Q.K := ⟨Q.two⟩
  haveI : IsGalois F ↥Q.K := inferInstance
  obtain ⟨w, hw, hwu⟩ := CompanionTheory.FamInh.exists_place_between (K := F) (L := ↥Q.K) hA
  have hunder : w.under (𝓞 F) = u :=
    ReciprocityTheory.Gal.eq_of_isPlaceOver (fun x => by
      rw [IsScalarTower.algebraMap_apply F ↥Q.K Ω]
      exact hw (algebraMap (𝓞 F) (𝓞 ↥Q.K) x)) hA
  refine ⟨w, fun hun => hfix fun x => ?_, hunder ▸ huT⟩
  have he : w.asIdeal.ramificationIdx (𝓞 F) = 1 := Ideal.ramificationIdx_eq_one_iff.2 hun
  have hs := CompanionTheory.FamInh.res_mem_inertia (L := ↥Q.K) hw hτ
  rw [(CompanionTheory.FamInh.inertia_eq_bot_iff u w).2 he, Subgroup.mem_bot] at hs
  have hc := AlgEquiv.restrictNormal_commutes τ ↥Q.K x
  have h1 : AlgEquiv.restrictNormal τ ↥Q.K x = x := DFunLike.congr_fun hs x
  rw [h1] at hc
  exact hc.symm

end UpperTheory.Gal.Int.Core
end

