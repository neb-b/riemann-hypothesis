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

namespace Bl.general_b_fact_left_version

theorem goal1 :
  ∀ {O : Type} [inst : CommRing.{0} O]
  [inst_1 : @IsDomain.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))] {V : Type}
  [inst_2 : AddCommGroup.{0} V]
  [inst_3 :
    @Module.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) V
      (@OreLocalization.instSemiring.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
        (@nonZeroDivisors.{0} O
          (@Semiring.toMonoidWithZero.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))
        (@OreLocalization.oreSetComm.{0} O (@CommRing.toCommMonoid.{0} O inst)
          (@nonZeroDivisors.{0} O
            (@Semiring.toMonoidWithZero.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))))
      (@AddCommGroup.toAddCommMonoid.{0} V inst_2)]
  [inst_4 :
    @Module.{0, 0} O V (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
      (@AddCommGroup.toAddCommMonoid.{0} V inst_2)]
  [inst_5 :
    @IsScalarTower.{0, 0, 0} O (@Formalism.MainNotions.G.KK.{0} O inst inst_1) V
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
      (@SMulZeroClass.toSMul.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) V
        (@AddZero.toZero.{0} V
          (@AddZeroClass.toAddZero.{0} V
            (@AddMonoid.toAddZeroClass.{0} V
              (@SubNegMonoid.toAddMonoid.{0} V
                (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))))
        (@DistribSMul.toSMulZeroClass.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) V
          (@AddMonoid.toAddZeroClass.{0} V
            (@SubNegMonoid.toAddMonoid.{0} V (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))
          (@DistribMulAction.toDistribSMul.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) V
            (@OreLocalization.instMonoid.{0} O (@CommMonoid.toMonoid.{0} O (@CommRing.toCommMonoid.{0} O inst))
              (@nonZeroDivisors.{0} O
                (@Semiring.toMonoidWithZero.{0} O
                  (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))
              (@OreLocalization.oreSetComm.{0} O (@CommRing.toCommMonoid.{0} O inst)
                (@nonZeroDivisors.{0} O
                  (@Semiring.toMonoidWithZero.{0} O
                    (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))))
            (@SubNegMonoid.toAddMonoid.{0} V (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2)))
            (@Module.toDistribMulAction.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) V
              (@OreLocalization.instSemiring.{0} O
                (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
                (@nonZeroDivisors.{0} O
                  (@Semiring.toMonoidWithZero.{0} O
                    (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))
                (@OreLocalization.oreSetComm.{0} O (@CommRing.toCommMonoid.{0} O inst)
                  (@nonZeroDivisors.{0} O
                    (@Semiring.toMonoidWithZero.{0} O
                      (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))))
              (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_3))))
      (@SMulZeroClass.toSMul.{0, 0} O V
        (@AddZero.toZero.{0} V
          (@AddZeroClass.toAddZero.{0} V
            (@AddMonoid.toAddZeroClass.{0} V
              (@SubNegMonoid.toAddMonoid.{0} V
                (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))))
        (@DistribSMul.toSMulZeroClass.{0, 0} O V
          (@AddMonoid.toAddZeroClass.{0} V
            (@SubNegMonoid.toAddMonoid.{0} V (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))
          (@DistribMulAction.toDistribSMul.{0, 0} O V
            (@Semiring.toMonoid.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst)))
            (@SubNegMonoid.toAddMonoid.{0} V (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2)))
            (@Module.toDistribMulAction.{0, 0} O V
              (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
              (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4))))]
  (M :
    @Submodule.{0, 0} O V (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
      (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4),
  @Eq.{1}
      (@Submodule.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) V
        (@DivisionSemiring.toSemiring.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1)
          (@Semifield.toDivisionSemiring.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1)
            (@Field.toSemifield.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) (@FractionRing.field.{0} O inst inst_1))))
        (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_3)
      (@Formalism.MainNotions.G.MQ.{0, 0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) V (@FractionRing.field.{0} O inst inst_1) inst_2 inst_3 O
        inst inst_4
        (@OreLocalization.instAlgebra.{0, 0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
          (@nonZeroDivisors.{0} O
            (@Semiring.toMonoidWithZero.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))
          (@OreLocalization.oreSetComm.{0} O (@CommRing.toCommMonoid.{0} O inst)
            (@nonZeroDivisors.{0} O
              (@Semiring.toMonoidWithZero.{0} O
                (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst)))))
          O (@CommRing.toCommSemiring.{0} O inst) (@Algebra.id.{0} O (@CommRing.toCommSemiring.{0} O inst)))
        inst_5 M)
      (@Top.top.{0}
        (@Submodule.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) V
          (@DivisionSemiring.toSemiring.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1)
            (@Semifield.toDivisionSemiring.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1)
              (@Field.toSemifield.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) (@FractionRing.field.{0} O inst inst_1))))
          (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_3)
        (@Submodule.instTop.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) V
          (@DivisionSemiring.toSemiring.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1)
            (@Semifield.toDivisionSemiring.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1)
              (@Field.toSemifield.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) (@FractionRing.field.{0} O inst inst_1))))
          (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_3)) →
    ∀ (x : V),
      @Exists.{1} O fun (a : O) ↦
        And
          (@Ne.{1} O a
            (@OfNat.ofNat.{0} O (nat_lit 0)
              (@Zero.toOfNat0.{0} O
                (@MulZeroClass.toZero.{0} O
                  (@instMulZeroClassOfSemiring.{0} O
                    (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst)))))))
          (@Membership.mem.{0, 0} V
            (@Submodule.{0, 0} O V (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
              (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4)
            (@SetLike.instMembership.{0, 0}
              (@Submodule.{0, 0} O V (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
                (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4)
              V
              (@Submodule.setLike.{0, 0} O V (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
                (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4))
            M
            (@HSMul.hSMul.{0, 0, 0} O V V
              (@instHSMul.{0, 0} O V
                (@SMulZeroClass.toSMul.{0, 0} O V
                  (@AddZero.toZero.{0} V
                    (@AddZeroClass.toAddZero.{0} V
                      (@AddMonoid.toAddZeroClass.{0} V
                        (@SubNegMonoid.toAddMonoid.{0} V
                          (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))))
                  (@DistribSMul.toSMulZeroClass.{0, 0} O V
                    (@AddMonoid.toAddZeroClass.{0} V
                      (@SubNegMonoid.toAddMonoid.{0} V
                        (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))
                    (@DistribMulAction.toDistribSMul.{0, 0} O V
                      (@Semiring.toMonoid.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst)))
                      (@SubNegMonoid.toAddMonoid.{0} V
                        (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2)))
                      (@Module.toDistribMulAction.{0, 0} O V
                        (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
                        (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4)))))
              a x)) := by
  intro O _ _ V _ _ _ _ M hM x
  have hx : x ∈ Submodule.span (Formalism.MainNotions.G.KK O) (M : Set V) := by
    have h : x ∈ (⊤ : Submodule (Formalism.MainNotions.G.KK O) V) := Submodule.mem_top
    rw [← hM] at h
    exact h
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact M.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact M.smul_mem b hay
    · rw [mul_smul]
      exact M.smul_mem a hbz
  | smul k y _ hy =>
    obtain ⟨b, hb, hby⟩ := hy
    obtain ⟨⟨n, d⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) k
    have hd : (d : O) ≠ 0 := nonZeroDivisors.coe_ne_zero d
    refine ⟨b * d, mul_ne_zero hb hd, ?_⟩
    have key : (d : O) • (IsLocalization.mk' (Formalism.MainNotions.G.KK O) n d • y) = n • y := by
      rw [← smul_assoc, Algebra.smul_def, IsLocalization.mk'_spec', algebraMap_smul]
    rw [mul_smul, key, smul_comm]
    exact M.smul_mem n hby

end Bl.general_b_fact_left_version
