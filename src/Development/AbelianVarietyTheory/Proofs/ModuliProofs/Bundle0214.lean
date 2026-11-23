module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSegreCoordinates
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyOverThetaPointScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaIdealFamilyUniversalProperty
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0177
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0115
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0137
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0129
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyThetaObjectFamilyOpenClosure
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.ThetaFamily

theorem exists_coord_of_isLocalRing {X : Scheme.{0}} {M : LB X} {σ : Type} (th : σ → M.Sec) (hM : M.IsLB)
    {R : Type} [CommRing R] [IsLocalRing R] (x : Sp R ⟶ X) : ∃ v, SecCoord M th x v := by
  obtain ⟨k, hk⟩ : ∃ k, x (IsLocalRing.closedPoint R) ∈ M.U k :=
    TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge trivial)
  refine GlobalTheory.SegreCoord.exists_secCoord hM (k := k) fun y => ?_
  exact ((IsLocalRing.specializes_closedPoint y).map x.continuous).mem_open (M.U k).isOpen hk

theorem nonempty_thetaFam : Out.Laws → Out.Laws2 → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → Nonempty (ThetaFam n em C) := by
  intro h₁ h₂ hcrit g J _ Mat κ n w w' hn hodd
  obtain ⟨j₁, hglue⟩ := _root_.GlobalTheory.ZM.exists_family_over_MMPre h₁ h₂ hcrit g J Mat κ n w w' hn hodd
  obtain ⟨j₂, hrep⟩ := _root_.GlobalTheory.FamRep.family_universal h₁ h₂ g J Mat κ n w w' hn hodd
  refine ⟨max j₁ j₂, fun j hj o _ b em C d hb hC => ?_⟩
  have := hb.1
  obtain ⟨i₁, i₂, i₃⟩ := _root_.GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree o g (n ^ j) J b em C hb.2.2
  obtain ⟨Y⟩ := GlobalTheory.ZM.nonempty_MMPre o g n (n ^ j) (thIdeal em C) (pow_pos hn.pos j) i₁ i₂ i₃
  obtain ⟨t, hd, -, hth, hfib⟩ := hglue j (le_of_max_le_left hj) o b em C d hb hC Y
  refine ⟨{ MM := Y.MM
            s := Y.s
            qproj := Y.qproj
            flat := Y.flat
            reduced := Y.reduced
            univ := t
            dense := hd
            loc := fun R _ _ β x hx => ?_
            pts := fun R _ β v hv => ?_
            rep := hrep j (le_of_max_le_right hj) o b em C d hb hC Y t hth hfib
            unram := _root_.GlobalTheory.ZM.tangent_eq_constPt_of_tMap h₁ h₂ o g n (n ^ j) J b _ Y t hodd.pow hth }⟩
  · obtain ⟨v, hv⟩ := exists_coord_of_isLocalRing Y.th Y.isLB x
    exact ⟨v, (hth R x v).2 hv, Y.loc R β x v hx hv⟩
  · simpa only [hth] using Y.pts R β v hv

end GlobalTheory.ZM.ThetaFamily
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationExistenceAndTorsionStatements
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.ZH

theorem thmU_and_uTors : GlobalTheory.ZH.ThmUSt ∧ GlobalTheory.ZH.UTorsSt := by
  obtain ⟨L, L2, L3, L4, L5, -⟩ := _root_.GlobalTheory.allSixLaws
  refine ⟨GlobalTheory.ZH.thmU_of_allSet L GlobalTheory.homExtension_semiAbelian_dvr (by
    have h := _root_.GlobalTheory.UU.exists_degData_unif (_root_.GlobalTheory.UU.TorsionCount.card_torsion_points L.globalFns L.rigidity) L L2
    intro V _ _ _ A G _ _ s
    obtain ⟨D, U, -, hg, -⟩ := h V A G s
    exact ⟨D, U, hg⟩), _root_.GlobalTheory.ZH.uTors_of_laws L L2 L3 L4 L5⟩

end GlobalTheory.ZH
end

