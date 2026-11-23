module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle0012
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.FLOf
section
namespace UpperTheory.Gal.TranscendenceTraces

theorem fL_of : PhiEx → FL := fL_of_parts phiQis_of extRes_of famHom_of

end UpperTheory.Gal.TranscendenceTraces
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPhiEx
section
namespace UpperTheory.Gal.TranscendenceTraces

theorem phiEx_of : LocFinSec → PhiEx := fun h => phiEx_of_parts phiUniv_of (phiExact_of (dSLoc_of (dSOne_of h)))

end UpperTheory.Gal.TranscendenceTraces
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPtInj
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem q_smul_sec (q : ℕ) (i : ℤ) {V : Scheme.{0}} (t : Sec (tw q i) V) : q • t = 0 := by
  have h0 : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    simp
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) q t, h0, zero_smul]

private theorem res_sub' {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a - b) = Sec.res g a - Sec.res g b := map_sub (F.obj.map g.op).hom a b

private theorem res_zero' {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) :
    Sec.res g (0 : Sec F U) = 0 := map_zero (F.obj.map g.op).hom

private theorem res_nsmul' {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℕ) (a : Sec F U) :
    Sec.res g (c • a) = c • Sec.res g a := map_nsmul (F.obj.map g.op).hom c a

private theorem sec_empty {R : Type} [CommRing R] (F : Shv R) {V : Scheme.{0}} [IsEmpty V] (a b : Sec F V) : a = b :=
  (_root_.GlobalTheory.EtC.sec_ext_glue R F V).1 a b ((GlobalTheory.T.etaleLocal_property_calculus_rules).2.2.2.2.2.2 V _)

theorem UpperTheory.Gal.TranscendenceTraces.ptInj_of :
    PtEx → PtInj := by
  intro hEx q _ i U b b' h
  have hy : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ U), Sec.res x (b - b') = 0 := by
    intro Ω _ _ x
    rw [res_sub', h Ω x, sub_self]
  refine (_root_.GlobalTheory.EtC.sec_ext_glue (ZMod q) (tw q i) U).1 b b' ?_
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ ((GlobalTheory.T.tateTwist_sections_locally_generated q i).1 U (b - b')) ?_
  intro V g hg
  have key : Sec.res g (b - b') = 0 := by
    rcases hg with hg | ⟨ζ, c, hc⟩
    · exact hg
    · rcases isEmpty_or_nonempty V with hV | ⟨⟨v⟩⟩
      · exact sec_empty _ _ _
      · obtain ⟨Ω, _, _, x, -⟩ := hEx V v
        have h1 : c • twGen i (ζ.map x.appTop.hom) = 0 := by
          have h2 := hy Ω (x ≫ g)
          rw [← res_res, hc, res_nsmul', (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1] at h2
          exact h2
        haveI : Nonempty (gp Ω) := ⟨IsLocalRing.closedPoint Ω⟩
        obtain ⟨d, rfl⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.1 (gp Ω) _ c h1
        rw [hc, mul_nsmul', q_smul_sec]
  rw [res_sub'] at key
  exact sub_eq_zero.1 key
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSumExLoc
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.sumExLoc_of :
    SecFun → FunSec → FibFin → SumExLoc := by
  intro hSF hFS hFF q _ i Z S p _ w hw A hζ a
  obtain ⟨ζ⟩ := hζ
  haveI : IsFinite A.r := Sq.finite A
  have hgen : twGen i (ζ.map A.r.appTop.hom) = Sec.res A.r (twGen i ζ) :=
    ((GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1 A.V A.U A.r ζ).symm
  obtain ⟨φ, hφ, hv⟩ := hSF q i A.V (ζ.map A.r.appTop.hom) a
  obtain ⟨ψ, hψ, hs⟩ := hw A φ hφ
  obtain ⟨b, hb⟩ := hFS q i A.U ζ ψ hψ
  refine ⟨b, fun Ω _ _ x => ?_⟩
  have hfin : (fib A.r x).Finite := hFF A.r Ω x
  have hz : ∀ z ∈ fib A.r x, Sec.res z a = φ (pt z) • Sec.res x (twGen i ζ) := by
    intro z hz
    have hz' : z ≫ A.r = x := hz
    rw [hv Ω z, hgen, res_res, hz']
  rw [hb Ω x, hs Ω x, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_smul]
  refine Finset.sum_congr rfl fun z hzm => ?_
  rw [hz z (hfin.mem_toFinset.mp hzm), mul_smul]
end

