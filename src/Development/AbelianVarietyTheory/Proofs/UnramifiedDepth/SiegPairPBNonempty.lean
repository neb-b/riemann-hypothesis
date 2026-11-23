module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StSiegPull

@[expose] public section

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv in
theorem siegPairPB_nonempty : ReciprocityTheory.ChartRestriction.G.Pdiv.StSiegPull := by
  intro S S' h M₁ B _ ζ s o f
  have hab : IsAbelianScheme ((Over.pullback f).obj o.A) :=
    { comm := by have := o.ab.comm; infer_instance
      smooth := by have := o.ab.smooth; show Smooth (Limits.pullback.snd _ _); infer_instance
      proper := by have := o.ab.proper; show IsProper (Limits.pullback.snd _ _); infer_instance
      geomConnected := by
        have := o.ab.geomConnected
        show GeometricallyConnected (Limits.pullback.snd _ _); infer_instance }
  have hP := LB.isLB_pull o.isLB (PullbackComparison.pφ₂ f o.A)
  obtain ⟨t₁, ht₁⟩ := o.rig₁
  obtain ⟨t₂, ht₂⟩ := o.rig₂
  exact ⟨{
    A := (Over.pullback f).obj o.A
    ab := hab
    φ := PullbackComparison.pφ f o.A
    φ₂ := PullbackComparison.pφ₂ f o.A
    pb := PullbackComparison.isGrpPullback f o.A
    sq := PullbackComparison.isSquare f o.A
    P := o.P.pull (PullbackComparison.pφ₂ f o.A)
    isLB := hP
    iso := PullbackComparison.gen_refl _ hP
    rig₁ := gen_chartPull (chartPullLinComb o.P _ _ _ _ (PullbackComparison.pφ f o.A)
      (fun _ => PullbackComparison.lift_one_id f o.A)) t₁ ht₁
    rig₂ := gen_chartPull (chartPullLinComb o.P _ _ _ _ (PullbackComparison.pφ f o.A)
      (fun _ => PullbackComparison.lift_id_one f o.A)) t₂ ht₂
    symm := LBIso.chartPull (chartPullPull o.P _ _ rfl)
      (chartPullLinComb o.P _ _ _ _ (PullbackComparison.pφ₂ f o.A) (fun _ => PullbackComparison.lift_swap f o.A)) o.symm }⟩

end GlobalTheory
