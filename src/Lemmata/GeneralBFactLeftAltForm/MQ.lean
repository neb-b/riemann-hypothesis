module

public import Mathlib
public import Formalism.SharpRestriction.GrowthBounds.ObjPol
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalRingCardinality.DataArith
public import Formalism.LocalRingCardinality.DataKernels
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.SharpRestriction.CuspSpanNormBounds.DataS
public import Formalism.SharpRestriction.GrowthBounds.DataG
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.FrobeniusOrbits.Bundle0001
public import Formalism.FrobeniusOrbits.HostThickExists
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.CoboundaryTransfers.Statement
public import Formalism.DegreeFormula.FlagDegFormula
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
public import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
public import Formalism.SharpRestriction.GrowthBounds.DataGChain
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.RealCyclotomicSubfield
public import Formalism.LocalRingCardinality.DataLevel
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.FrobeniusOrbits.Statement
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0001
public import Formalism.TameInertiaTowers.CentralOrderTwo.OrderOfThreeUnitsTwoPow
public import Formalism.TameInertiaTowers.CentralOrderTwo.Bundle0001
public import Formalism.TameInertiaTowers.CentralOrderTwo.MemDecompositionSubgroupIff
public import Formalism.TameInertiaTowers.CentralOrderTwo.NegOneNeOneUnitsZmodFour
public import Formalism.TameInertiaTowers.CentralOrderTwo.Bundle0002
public import Formalism.TameInertiaTowers.CentralOrderTwo.Galois
public import Formalism.FormalDegreeBessel.Bundle0001
public import Formalism.FormalDegreeBessel.StatementWR
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0004
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0003
public import Formalism.RealPlaceAnalysis.StatementU
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0001
public import Formalism.RealPlaceAnalysis.Bundle0001
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0002
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0006
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet
public import Formalism.RealPlaceAnalysis.Bundle0002

@[expose] public section

namespace Bl.general_b_fact_left_alt_form

theorem goal1 :
  ∀ {O : Type} [inst : CommRing.{0} O]
  [inst_1 : @IsDomain.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))]
  [@IsDiscreteValuationRing.{0} O inst inst_1] {W : Type} [inst_3 : AddCommGroup.{0} W]
  [inst_4 :
    @Module.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) W
      (@OreLocalization.instSemiring.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
        (@nonZeroDivisors.{0} O
          (@Semiring.toMonoidWithZero.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))
        (@OreLocalization.oreSetComm.{0} O (@CommRing.toCommMonoid.{0} O inst)
          (@nonZeroDivisors.{0} O
            (@Semiring.toMonoidWithZero.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))))
      (@AddCommGroup.toAddCommMonoid.{0} W inst_3)]
  [inst_5 :
    @Module.{0, 0} O W (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
      (@AddCommGroup.toAddCommMonoid.{0} W inst_3)]
  [inst_6 :
    @IsScalarTower.{0, 0, 0} O (@Formalism.MainNotions.G.KK.{0} O inst inst_1) W
      (@OreLocalization.instSMulOfIsScalarTower.{0, 0, 0} O O O
        (@CommMonoid.toMonoid.{0} O (@CommRing.toCommMonoid.{0} O inst))
        (@nonZeroDivisors.{0} O
          (@Semiring.toMonoidWithZero.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))
        (@OreLocalization.oreSetComm.{0} O (@CommRing.toCommMonoid.{0} O inst)
          (@nonZeroDivisors.{0} O
            (@Semiring.toMonoidWithZero.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst)))))
        (@Monoid.toMulAction.{0} O (@CommMonoid.toMonoid.{0} O (@CommRing.toCommMonoid.{0} O inst)))
        (@instSMulOfMul.{0} O
          (@Distrib.toMul.{0} O
            (@instDistribOfSemiring.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst)))))
        (@instSMulOfMul.{0} O
          (@Distrib.toMul.{0} O
            (@instDistribOfSemiring.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst)))))
        _ _)
      (@SMulZeroClass.toSMul.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) W
        (@AddZero.toZero.{0} W
          (@AddZeroClass.toAddZero.{0} W
            (@AddMonoid.toAddZeroClass.{0} W
              (@SubNegMonoid.toAddMonoid.{0} W
                (@AddGroup.toSubNegMonoid.{0} W (@AddCommGroup.toAddGroup.{0} W inst_3))))))
        (@DistribSMul.toSMulZeroClass.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) W
          (@AddMonoid.toAddZeroClass.{0} W
            (@SubNegMonoid.toAddMonoid.{0} W (@AddGroup.toSubNegMonoid.{0} W (@AddCommGroup.toAddGroup.{0} W inst_3))))
          (@DistribMulAction.toDistribSMul.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) W
            (@OreLocalization.instMonoid.{0} O (@CommMonoid.toMonoid.{0} O (@CommRing.toCommMonoid.{0} O inst))
              (@nonZeroDivisors.{0} O
                (@Semiring.toMonoidWithZero.{0} O
                  (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))
              (@OreLocalization.oreSetComm.{0} O (@CommRing.toCommMonoid.{0} O inst)
                (@nonZeroDivisors.{0} O
                  (@Semiring.toMonoidWithZero.{0} O
                    (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))))
            (@SubNegMonoid.toAddMonoid.{0} W (@AddGroup.toSubNegMonoid.{0} W (@AddCommGroup.toAddGroup.{0} W inst_3)))
            (@Module.toDistribMulAction.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) W
              (@OreLocalization.instSemiring.{0} O
                (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
                (@nonZeroDivisors.{0} O
                  (@Semiring.toMonoidWithZero.{0} O
                    (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))
                (@OreLocalization.oreSetComm.{0} O (@CommRing.toCommMonoid.{0} O inst)
                  (@nonZeroDivisors.{0} O
                    (@Semiring.toMonoidWithZero.{0} O
                      (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))))
              (@AddCommGroup.toAddCommMonoid.{0} W inst_3) inst_4))))
      (@SMulZeroClass.toSMul.{0, 0} O W
        (@AddZero.toZero.{0} W
          (@AddZeroClass.toAddZero.{0} W
            (@AddMonoid.toAddZeroClass.{0} W
              (@SubNegMonoid.toAddMonoid.{0} W
                (@AddGroup.toSubNegMonoid.{0} W (@AddCommGroup.toAddGroup.{0} W inst_3))))))
        (@DistribSMul.toSMulZeroClass.{0, 0} O W
          (@AddMonoid.toAddZeroClass.{0} W
            (@SubNegMonoid.toAddMonoid.{0} W (@AddGroup.toSubNegMonoid.{0} W (@AddCommGroup.toAddGroup.{0} W inst_3))))
          (@DistribMulAction.toDistribSMul.{0, 0} O W
            (@Semiring.toMonoid.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst)))
            (@SubNegMonoid.toAddMonoid.{0} W (@AddGroup.toSubNegMonoid.{0} W (@AddCommGroup.toAddGroup.{0} W inst_3)))
            (@Module.toDistribMulAction.{0, 0} O W
              (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
              (@AddCommGroup.toAddCommMonoid.{0} W inst_3) inst_5))))]
  (M :
    @Submodule.{0, 0} O W (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
      (@AddCommGroup.toAddCommMonoid.{0} W inst_3) inst_5)
  (y : W),
  @Membership.mem.{0, 0} W
      (@Submodule.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) W
        (@DivisionSemiring.toSemiring.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1)
          (@Semifield.toDivisionSemiring.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1)
            (@Field.toSemifield.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) (@FractionRing.field.{0} O inst inst_1))))
        (@AddCommGroup.toAddCommMonoid.{0} W inst_3) inst_4)
      (@SetLike.instMembership.{0, 0}
        (@Submodule.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) W
          (@DivisionSemiring.toSemiring.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1)
            (@Semifield.toDivisionSemiring.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1)
              (@Field.toSemifield.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) (@FractionRing.field.{0} O inst inst_1))))
          (@AddCommGroup.toAddCommMonoid.{0} W inst_3) inst_4)
        W
        (@Submodule.setLike.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) W
          (@DivisionSemiring.toSemiring.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1)
            (@Semifield.toDivisionSemiring.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1)
              (@Field.toSemifield.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) (@FractionRing.field.{0} O inst inst_1))))
          (@AddCommGroup.toAddCommMonoid.{0} W inst_3) inst_4))
      (@Formalism.MainNotions.G.MQ.{0, 0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) W (@FractionRing.field.{0} O inst inst_1) inst_3 inst_4 O
        inst inst_5
        (@OreLocalization.instAlgebra.{0, 0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
          (@nonZeroDivisors.{0} O
            (@Semiring.toMonoidWithZero.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))
          (@OreLocalization.oreSetComm.{0} O (@CommRing.toCommMonoid.{0} O inst)
            (@nonZeroDivisors.{0} O
              (@Semiring.toMonoidWithZero.{0} O
                (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst)))))
          O (@CommRing.toCommSemiring.{0} O inst) (@Algebra.id.{0} O (@CommRing.toCommSemiring.{0} O inst)))
        inst_6 M)
      y →
    @Exists.{1} O fun (a : O) ↦
      And
        (@Ne.{1} O a
          (@OfNat.ofNat.{0} O (nat_lit 0)
            (@Zero.toOfNat0.{0} O
              (@MulZeroClass.toZero.{0} O
                (@instMulZeroClassOfSemiring.{0} O
                  (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst)))))))
        (@Membership.mem.{0, 0} W
          (@Submodule.{0, 0} O W (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
            (@AddCommGroup.toAddCommMonoid.{0} W inst_3) inst_5)
          (@SetLike.instMembership.{0, 0}
            (@Submodule.{0, 0} O W (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
              (@AddCommGroup.toAddCommMonoid.{0} W inst_3) inst_5)
            W
            (@Submodule.setLike.{0, 0} O W (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
              (@AddCommGroup.toAddCommMonoid.{0} W inst_3) inst_5))
          M
          (@HSMul.hSMul.{0, 0, 0} O W W
            (@instHSMul.{0, 0} O W
              (@SMulZeroClass.toSMul.{0, 0} O W
                (@AddZero.toZero.{0} W
                  (@AddZeroClass.toAddZero.{0} W
                    (@AddMonoid.toAddZeroClass.{0} W
                      (@SubNegMonoid.toAddMonoid.{0} W
                        (@AddGroup.toSubNegMonoid.{0} W (@AddCommGroup.toAddGroup.{0} W inst_3))))))
                (@DistribSMul.toSMulZeroClass.{0, 0} O W
                  (@AddMonoid.toAddZeroClass.{0} W
                    (@SubNegMonoid.toAddMonoid.{0} W
                      (@AddGroup.toSubNegMonoid.{0} W (@AddCommGroup.toAddGroup.{0} W inst_3))))
                  (@DistribMulAction.toDistribSMul.{0, 0} O W
                    (@Semiring.toMonoid.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst)))
                    (@SubNegMonoid.toAddMonoid.{0} W
                      (@AddGroup.toSubNegMonoid.{0} W (@AddCommGroup.toAddGroup.{0} W inst_3)))
                    (@Module.toDistribMulAction.{0, 0} O W
                      (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
                      (@AddCommGroup.toAddCommMonoid.{0} W inst_3) inst_5)))))
            a y)) := by
  intro O _ _ _ W _ _ _ _ M y hy
  rw [Formalism.MainNotions.G.MQ] at hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact M.zero_mem⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem b hax
    · rw [mul_smul]; exact M.smul_mem a hbz
  | smul c x _ hx =>
    obtain ⟨b, hb, hbx⟩ := hx
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors O) c
    refine ⟨(s : O) * b, mul_ne_zero (nonZeroDivisors.ne_zero s.2) hb, ?_⟩
    have key : ((s : O) * b) • (c • x) = r • (b • x) := by
      rw [← algebraMap_smul (Formalism.MainNotions.G.KK O) ((s : O) * b) (c • x), smul_smul,
        ← algebraMap_smul (Formalism.MainNotions.G.KK O) r (b • x), ← algebraMap_smul (Formalism.MainNotions.G.KK O) b x, smul_smul]
      congr 1
      rw [map_mul, ← hrs]
      ring
    rw [key]
    exact M.smul_mem r hbx

end Bl.general_b_fact_left_alt_form
