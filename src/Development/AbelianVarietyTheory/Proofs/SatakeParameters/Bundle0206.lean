module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0170
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0047
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorSphericalUnitEqId
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

noncomputable section

open TensorProduct Formalism.UG

namespace GlobalTheory.OneAct

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

theorem compAt_conjAL (z : AL L) :
    compAt L v (conjAL L z) = Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom
      (v.adicCompletion (maximalRealSubfield L)) (compAt L v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem compAt_mem_tensInt {z : AL L} (hz : z ∈ ALint L) :
    compAt L v z ∈ tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L))
      (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v) := by
  have key : ALint L ≤ (tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L))
      (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v)).comap (compAt L v) := by
    rw [ALint, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · apply Subring.subset_closure
      left
      exact ⟨⟨(y : L), y, rfl⟩, by rw [GlobalTheory.InertUmax.compAt_tmul]; rfl⟩
    · apply Subring.subset_closure
      right
      exact ⟨⟨a v, ha v⟩, by rw [GlobalTheory.InertUmax.compAt_tmul]⟩
  exact key hz

theorem loc_mem_GU (Dv : InertDatum L n v w) (x : GAf L n) : Dv.loc x ∈ GU Dv.σw n := by
  set φ : AL L →+* w.adicCompletion L := (Dv.e : _ →+* _).comp (compAt L v) with hφdef
  have hφ : ∀ z, φ (conjAL L z) = Dv.σw (φ z) := fun z => by
    simp only [φ, RingHom.comp_apply, compAt_conjAL]
    exact Dv.comm _
  have hX : ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      conjT (conjAL L) ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := x.2
  have hX' := mul_eq_one_comm.mp hX
  set A : Matrix (Fin n) (Fin n) (w.adicCompletion L) :=
    ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map φ with hAdef
  have hA : cT Dv.σw A * A = 1 := by
    have : cT Dv.σw A = (conjT (conjAL L) ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))).map φ := by
      ext i j; simp [cT, conjT, A, hφ]
    rw [this, ← Matrix.map_mul, hX', Matrix.map_one _ (map_zero _) (map_one _)]
  have hloc : ((Dv.loc x : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) =
      ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) * A *
        (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) := rfl
  have hPP : cT Dv.σw ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
      cT Dv.σw (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) = 1 := by
    rw [← cT_mul, Units.mul_inv, cT_one]
  have hPP' : (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
      ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) = 1 :=
    Units.mul_inv _
  show cT Dv.σw ((Dv.loc x : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
      antiJ (w.adicCompletion L) n *
      ((Dv.loc x : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) =
      antiJ (w.adicCompletion L) n
  rw [← Dv.Panti, hloc, cT_mul, cT_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (cT Dv.σw _) (cT Dv.σw (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L))), hPP,
    Matrix.one_mul, ← Matrix.mul_assoc (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)), hPP',
    Matrix.one_mul, ← Matrix.mul_assoc (cT Dv.σw A) A, hA, Matrix.one_mul]

theorem mem_range_of_int {K : Type} [Field K] (S : Subring K) (g : GL (Fin n) K)
    (h1 : ∀ i j, (g : Matrix (Fin n) (Fin n) K) i j ∈ S)
    (h2 : ∀ i j, ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ S) :
    g ∈ (Formalism.UG.bc (n := Fin n) S.subtype).range := by
  let M : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, h1 i j⟩
  let N : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, h2 i j⟩
  have hM : M.map S.subtype = (g : Matrix (Fin n) (Fin n) K) := by ext i j; rfl
  have hN : N.map S.subtype = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by ext i j; rfl
  have inj : Function.Injective (fun A : Matrix (Fin n) (Fin n) S => A.map S.subtype) := by
    intro A B h; ext i j; exact congrFun (congrFun h i) j
  have hMN : M * N = 1 := inj (by
    simp only [Matrix.map_mul, hM, hN, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
  have hNM : N * M = 1 := inj (by
    simp only [Matrix.map_mul, hM, hN, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])
  refine ⟨⟨M, N, hMN, hNM⟩, Units.ext ?_⟩
  exact hM

theorem loc_entries_int (Dv : InertDatum L n v w) {x : GAf L n} (hx : x ∈ Umax L n) (i j : Fin n) :
    ((Dv.loc x : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈
      intL (w.adicCompletion L) := by
  have hP := GlobalTheory.InertUmax.entries_mem_of_range _ _ Dv.Pint
  have hP' := GlobalTheory.InertUmax.entries_mem_of_range _ _ (inv_mem Dv.Pint)
  have hA : ∀ k l, Dv.e (compAt L v (((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) k l)) ∈
      intL (w.adicCompletion L) := fun k l => (Dv.integ _).1 (compAt_mem_tensInt (hx k l))
  simp only [InertDatum.loc, Units.val_mul, Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _
    (Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hP' i l) (hA l k)) (hP k j)

theorem loc_mem_KU (Dv : InertDatum L n v w) {x : GAf L n} (hx : x ∈ Umax L n) :
    (⟨Dv.loc x, loc_mem_GU Dv x⟩ : GU Dv.σw n) ∈ KU Dv.σw n := by
  refine ⟨loc_mem_GU Dv x, mem_range_of_int _ _ (loc_entries_int Dv hx) ?_⟩
  have : (Dv.loc x)⁻¹ = Dv.loc x⁻¹ := by
    rw [show Dv.loc x⁻¹ = GlobalTheory.SatInd.CosetFin.locHom Dv x⁻¹ from rfl, map_inv]; rfl
  show ∀ i j, (((Dv.loc x)⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈ _
  rw [this]
  exact loc_entries_int Dv (inv_mem hx)

end GlobalTheory.OneAct

theorem GlobalTheory.OneAct.heckeFunI_unit : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (f : GAf L n → W), (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv (dosetInd ℂ (KU Dv.σw n) 1) f = f := by
  intro L _ _ _ n v w Dv U hU W _ _ f hf
  funext g
  unfold heckeFunI
  have hone : TrivOutside {v} (1 : GAf L n) := by
    intro u _
    show ((1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L u) = 1
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hdK : ∀ y : GU Dv.σw n, y ∈ (DoubleCoset.doubleCoset (1 : GU Dv.σw n) (KU Dv.σw n : Set (GU Dv.σw n))
      (KU Dv.σw n : Set (GU Dv.σw n))) ↔ y ∈ KU Dv.σw n := by
    intro y
    rw [DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      simpa using (KU Dv.σw n).mul_mem ha hb
    · intro hy
      exact ⟨y, hy, 1, (KU Dv.σw n).one_mem, by simp⟩
  rw [finsum_eq_single _ ((1 : GAf L n) : GAf L n ⧸ U)]
  · have hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = ((1 : GAf L n) : GAf L n ⧸ U) ∧ TrivOutside {v} x :=
      ⟨1, rfl, hone⟩
    rw [dite_eq_left hc]
    obtain ⟨hx1, hx2⟩ := hc.choose_spec
    have hxU : hc.choose ∈ U := by
      have := QuotientGroup.eq.1 hx1
      simpa using this
    have hxM : hc.choose ∈ Umax L n := (hU _ hx2).1 hxU
    have hval : Dv.hval (dosetInd ℂ (KU Dv.σw n) 1) (Dv.loc hc.choose) = 1 := by
      unfold InertDatum.hval
      rw [dite_eq_left (GlobalTheory.OneAct.loc_mem_GU Dv _)]
      unfold dosetInd
      rw [Set.indicator_of_mem ((hdK _).2 (GlobalTheory.OneAct.loc_mem_KU Dv hxM))]
      rfl
    rw [hval, one_smul]
    exact congrFun (hf _ hxU) g
  · intro c hc1
    split_ifs with hc
    · obtain ⟨hx1, hx2⟩ := hc.choose_spec
      have hval : Dv.hval (dosetInd ℂ (KU Dv.σw n) 1) (Dv.loc hc.choose) = 0 := by
        unfold InertDatum.hval
        split_ifs with hm
        · unfold dosetInd
          apply Set.indicator_of_notMem
          intro hmem
          have hK := (hdK _).1 hmem
          have hxM : hc.choose ∈ Umax L n :=
            _root_.GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv _ hx2 (fun i j => GlobalTheory.SatInd.CosetFin.entries_int hK i j)
          apply hc1
          rw [← hx1]
          exact QuotientGroup.eq.2 (by simpa using (hU _ hx2).2 hxM)
        · rfl
      rw [hval, zero_smul]
    · rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertLocalMemLocalUnitaryGroup
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

namespace GlobalTheory.InertLocUnitary

open TensorProduct

theorem compAt_conjAL (L : Type) [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (a : ReciprocityTheory.Aut.AL L) :
    ReciprocityTheory.Aut.compAt L v (ReciprocityTheory.Aut.conjAL L a) =
      Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L))
        (ReciprocityTheory.Aut.compAt L v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp [ReciprocityTheory.Aut.compAt, ReciprocityTheory.Aut.conjAL, Formalism.UG.sigR, Algebra.TensorProduct.map_tmul]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem loc_mem_GU (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (x : GAf L n) : Dv.loc x ∈ GU Dv.σw n := by
  set ψ : ReciprocityTheory.Aut.AL L →+* w.adicCompletion L :=
    (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L).comp
      (ReciprocityTheory.Aut.compAt L v) with hψ
  have hcomm : ∀ a, Dv.σw (ψ a) = ψ (ReciprocityTheory.Aut.conjAL L a) := by
    intro a
    simp only [hψ, RingHom.comp_apply, RingHom.coe_coe]
    rw [compAt_conjAL, Dv.comm]
  set M : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L) := (x.1 : GL (Fin n) (ReciprocityTheory.Aut.AL L)).val with hM
  have hx : M * ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL L) M = 1 := x.2
  set X : Matrix (Fin n) (Fin n) (w.adicCompletion L) := M.map ψ with hX
  have hXval : ((Formalism.UG.bc (n := Fin n) (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
      (Matrix.GeneralLinearGroup.map (ReciprocityTheory.Aut.compAt L v) (x : GL (Fin n) (ReciprocityTheory.Aut.AL L))) :
        GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) = X := by
    ext i j; rfl
  have hcTX : Formalism.UG.cT Dv.σw X = (ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL L) M).map ψ := by
    ext i j
    simp [Formalism.UG.cT, ReciprocityTheory.Aut.conjT, hX, hcomm]
  have hXX : X * Formalism.UG.cT Dv.σw X = 1 := by
    rw [hcTX, hX, ← Matrix.map_mul, hx, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  have hXX' : Formalism.UG.cT Dv.σw X * X = 1 := mul_eq_one_comm.mp hXX
  set P : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (Dv.P : GL (Fin n) (w.adicCompletion L)).val with hP
  set Q : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)).val with hQ
  have hPQ : P * Q = 1 := by rw [hP, hQ, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hJ : Formalism.UG.cT Dv.σw P * P = Formalism.UG.antiJ (w.adicCompletion L) n := Dv.Panti
  show Formalism.UG.cT Dv.σw (((Dv.loc x : GL (Fin n) _)) : Matrix _ _ _) * Formalism.UG.antiJ (w.adicCompletion L) n *
      ((Dv.loc x : GL (Fin n) _) : Matrix _ _ _) = Formalism.UG.antiJ (w.adicCompletion L) n
  have hloc : ((Dv.loc x : GL (Fin n) _) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) = Q * X * P := by
    simp only [InertDatum.loc, Units.val_mul, hXval, hQ, hP]
  have cQP : Formalism.UG.cT Dv.σw Q * Formalism.UG.cT Dv.σw P = 1 := by
    rw [← Formalism.UG.cT_mul, hPQ, Formalism.UG.cT_one]
  rw [hloc, ← hJ, Formalism.UG.cT_mul, Formalism.UG.cT_mul]
  calc _ = Formalism.UG.cT Dv.σw P * Formalism.UG.cT Dv.σw X * (Formalism.UG.cT Dv.σw Q * Formalism.UG.cT Dv.σw P) * (P * Q) * X * P := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT Dv.σw P * P := by
        rw [cQP, hPQ, Matrix.mul_one, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (Formalism.UG.cT Dv.σw X), hXX', Matrix.one_mul]

end GlobalTheory.InertLocUnitary

theorem GlobalTheory.InertLocUnitary.main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), ∀ x : GAf L n, Dv.loc x ∈ GU Dv.σw n :=
  fun L _ _ _ n v w Dv x => GlobalTheory.InertLocUnitary.loc_mem_GU L n v w Dv x
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeWordConditionsOfLargeScale
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.RecS

theorem jointCD_of_large : ∀ eps ez A : ℝ, 0 < eps → 0 < ez → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L)
    (HW : HWOf D.loc), L.sc.eps = eps → L.sc.ez = ez → Pm.CLw ≤ A → x0 ≤ L.sc.x → LocalSituation.adm7 D →
    (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.JointCD L HW := by
  intro eps ez A heps hez
  obtain ⟨x1, h1⟩ := _root_.GlobalTheory.HTW.roomy_of_large eps 100 A heps le_rfl
  obtain ⟨x2, h2⟩ := _root_.GlobalTheory.InertPrimeEleven.eleven_le ez hez
  refine ⟨max x1 x2, ?_⟩
  intro D L Pm HW he hZ hA hx hadm hfont hja i hin r ρ π hpt w hw
  have hR : Roomy L 100 := h1 D L Pm he hA (le_trans (le_max_left _ _) hx)
  have h11 : 11 ≤ D.nd.l i := h2 D L _ hZ (le_trans (le_max_right _ _) hx) Fact.out hin
  have hn2 := hin.ne_two
  have hj := hin.2.2.2
  refine ⟨_root_.GlobalTheory.bridge_field_le_unramified D.nbr i w hw hin.1 hin.2.1 hin.2.2.1, ?_⟩
  intro Cx hG
  obtain ⟨ε, g, hg, hB⟩ := GlobalTheory.T.wordConditions_common_natural_representation L 100 HW i r ρ π w hw Cx hG hR hadm hfont hja hpt hin.1 hin.2.1 hin.2.2.1
  have hs := (_root_.GlobalTheory.FrobSign.frobG_isArithFrob_and_sign D (D.nd.l i) hin.1 hin.2.1 hin.2.2.1).2
  have hm : (DV.frobG D (D.nd.l i)).1.2 = -1 := by
    refine (Int.units_eq_one_or _).resolve_left fun h => hj ?_
    rw [← hs, h]; rfl
  have hm' : ((DV.frobG D (D.nd.l i))⁻¹).1.2 = -1 := by
    change ((DV.frobG D (D.nd.l i)).1.2)⁻¹ = -1
    rw [hm]; rfl
  refine ⟨_, hB, _root_.GlobalTheory.HTW.RecS.setting_of_wordBase L HW i r ρ π w hw Cx hG _ hn2 hB, h11,
    _root_.GlobalTheory.HTW.Rec.recWord_wordBox L 100 _ ε g _ hR hg, ?_⟩
  rcases _root_.GlobalTheory.HTW.Rec.recWord_dichotomy L 100 _ ε g _ _ hR hg h11 hm' with h | ⟨d, hd⟩
  · exact Or.inl h
  · exact Or.inr ⟨d, hd, _root_.GlobalTheory.HTW.RecS.settingC_of_wordsAT L HW i r ρ π w hw Cx hG _ d h11 hB hd⟩

end GlobalTheory.HTW.RecS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSubquotientParabolicProductTwoFiniteL
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ProdSubquot

theorem subquot_dichotomy : ∀ (G : Type) [Group G] (U V A Q : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup A] [Module ℂ A] [AddCommGroup Q] [Module ℂ Q] (τ : Representation ℂ G U) (ρ : Representation ℂ G V) (α : Representation ℂ G A) (κ : Representation ℂ G Q) (i : α.IntertwiningMap ρ) (q : ρ.IntertwiningMap κ), τ.IsIrreducible → (∀ v, q v = 0 → ∃ a, i a = v) → IsSubquotient τ ρ → IsSubquotient τ α ∨ IsSubquotient τ κ := _root_.GlobalTheory.isSubquotient_of_exact_middle

theorem exists_irreducible_of_pred : ∀ (H : Type) [Group H] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V) (P : ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y], Representation ℂ H Y → Prop), HasFiniteLength ρ → (∀ (Y Y' : Type) [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Y'] [Module ℂ Y'] (σ : Representation ℂ H Y) (σ' : Representation ℂ H Y') (f : σ.IntertwiningMap σ'), Function.Injective f → P Y σ → P Y' σ') → (∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (σ : Representation ℂ H Y), P Y σ → Nontrivial Y) → (∀ A B : Subrepresentation ρ, B ≤ A → P _ A.toRepresentation → P _ B.toRepresentation ∨ P _ (subQuot A B)) → P V ρ → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (σ : Representation ℂ H Y), σ.IsIrreducible ∧ IsSubquotient σ ρ ∧ P Y σ := _root_.GlobalTheory.ExactIrr.main

theorem parIndMap_exact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (X Y : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (ξ : Representation ℂ (Levi k m) X) (η : Representation ℂ (Levi k m) Y) (i : ξ.IntertwiningMap η), Function.Injective i → Function.Injective (parIndMap e i) ∧ ∀ (Z : Type) [AddCommGroup Z] [Module ℂ Z] (ζ : Representation ℂ (Levi k m) Z) (q : η.IntertwiningMap ζ), (∀ y, q y = 0 → ∃ x, i x = y) → ∀ φ, parIndMap e q φ = 0 → ∃ ψ, parIndMap e i ψ = φ := _root_.GlobalTheory.ParIndExact.parInd_exact

def extMapLeft {G H A B W : Type} [Group G] [Group H] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup W] [Module ℂ W] {α : Representation ℂ G A} {β : Representation ℂ G B}
    (i : α.IntertwiningMap β) (ρ : Representation ℂ H W) :
    (extTensor α ρ).IntertwiningMap (extTensor β ρ) where
  toLinearMap := i.toLinearMap.rTensor W
  isIntertwining' g := TensorProduct.ext' fun v w => by
    simp [i.isIntertwining]

def extMapRight {G H A B X : Type} [Group G] [Group H] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X) {α : Representation ℂ H A} {β : Representation ℂ H B}
    (i : α.IntertwiningMap β) :
    (extTensor ρ α).IntertwiningMap (extTensor ρ β) where
  toLinearMap := i.toLinearMap.lTensor X
  isIntertwining' g := TensorProduct.ext' fun v w => by
    simp [i.isIntertwining]

theorem prod₂_exact_left : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (A B W : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [AddCommGroup W] [Module ℂ W] (α : Representation ℂ (GL (Fin r) k) A) (β : Representation ℂ (GL (Fin r) k) B) (ρ₂ : Representation ℂ (GL (Fin t) k) W) (i : α.IntertwiningMap β), Function.Injective i → ∃ I : (prod₂ α ρ₂).IntertwiningMap (prod₂ β ρ₂), Function.Injective I ∧ ∀ (C : Type) [AddCommGroup C] [Module ℂ C] (γ : Representation ℂ (GL (Fin r) k) C) (q : β.IntertwiningMap γ), Function.Surjective q → (∀ a, q (i a) = 0) → (∀ b, q b = 0 → ∃ a, i a = b) → ∃ Q : (prod₂ β ρ₂).IntertwiningMap (prod₂ γ ρ₂), ∀ φ, Q φ = 0 → ∃ ψ, I ψ = φ := by
  intro k _ _ _ _ r t A B W _ _ _ _ _ _ α β ρ₂ i hi
  let s := (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom
  have hi' : Function.Injective (compMap (extMapLeft i ρ₂) s) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hi
  obtain ⟨hI, hex⟩ := parIndMap_exact k Bool (Fin (r + t)) (Two (Fin r) (Fin t)) (two (stdSum rfl)) _ _
    _ _ (compMap (extMapLeft i ρ₂) s) hi'
  refine ⟨parIndMap _ (compMap (extMapLeft i ρ₂) s), hI, fun C _ _ γ q hq hqi hiq => ?_⟩
  refine ⟨parIndMap _ (compMap (extMapLeft q ρ₂) s), hex _ _ (compMap (extMapLeft q ρ₂) s) ?_⟩
  have hE : Function.Exact (i.toLinearMap.rTensor W) (q.toLinearMap.rTensor W) := by
    refine rTensor_exact W ?_ hq
    intro b
    refine ⟨hiq b, ?_⟩
    rintro ⟨a, rfl⟩
    exact hqi a
  intro y hy
  exact (hE y).1 hy

theorem prod₂_exact_right : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (X A B : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (ρ₁ : Representation ℂ (GL (Fin r) k) X) (α : Representation ℂ (GL (Fin t) k) A) (β : Representation ℂ (GL (Fin t) k) B) (i : α.IntertwiningMap β), Function.Injective i → ∃ I : (prod₂ ρ₁ α).IntertwiningMap (prod₂ ρ₁ β), Function.Injective I ∧ ∀ (C : Type) [AddCommGroup C] [Module ℂ C] (γ : Representation ℂ (GL (Fin t) k) C) (q : β.IntertwiningMap γ), Function.Surjective q → (∀ a, q (i a) = 0) → (∀ b, q b = 0 → ∃ a, i a = b) → ∃ Q : (prod₂ ρ₁ β).IntertwiningMap (prod₂ ρ₁ γ), ∀ φ, Q φ = 0 → ∃ ψ, I ψ = φ := by
  intro k _ _ _ _ r t X A B _ _ _ _ _ _ ρ₁ α β i hi
  let s := (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom
  have hi' : Function.Injective (compMap (extMapRight ρ₁ i) s) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hi
  obtain ⟨hI, hex⟩ := parIndMap_exact k Bool (Fin (r + t)) (Two (Fin r) (Fin t)) (two (stdSum rfl)) _ _
    _ _ (compMap (extMapRight ρ₁ i) s) hi'
  refine ⟨parIndMap _ (compMap (extMapRight ρ₁ i) s), hI, fun C _ _ γ q hq hqi hiq => ?_⟩
  refine ⟨parIndMap _ (compMap (extMapRight ρ₁ q) s), hex _ _ (compMap (extMapRight ρ₁ q) s) ?_⟩
  have hE : Function.Exact (i.toLinearMap.lTensor X) (q.toLinearMap.lTensor X) := by
    refine lTensor_exact X ?_ hq
    intro b
    refine ⟨hiq b, ?_⟩
    rintro ⟨a, rfl⟩
    exact hqi a
  intro y hy
  exact (hE y).1 hy

theorem nontrivial_of_prod₂ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r t : ℕ} (π : Irr k (r + t)) {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (σ₁ : Representation ℂ (GL (Fin r) k) X) (σ₂ : Representation ℂ (GL (Fin t) k) Y)
    (h : IsSubquotient π.π (prod₂ σ₁ σ₂)) : Nontrivial X ∧ Nontrivial Y := by
  obtain ⟨S, f, hf⟩ := h
  have := nontrivial_of_irreducible π.irr
  obtain ⟨w, hw⟩ := exists_ne (0 : π.V)
  obtain ⟨φ, rfl⟩ := hf w
  by_contra hc
  rw [not_and_or, not_nontrivial_iff_subsingleton, not_nontrivial_iff_subsingleton] at hc
  have hsub : Subsingleton (TensorProduct ℂ X Y) := by
    rcases hc with hc | hc
    · haveI := hc; infer_instance
    · haveI := hc; infer_instance
  apply hw
  have h0 : φ = 0 := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; funext g
    exact Subsingleton.elim _ _
  rw [h0, map_zero]

theorem step_left {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r t : ℕ} (π : Irr k (r + t)) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ₁ : Representation ℂ (GL (Fin r) k) V) (ρ₂ : Representation ℂ (GL (Fin t) k) W)
    (hf₁ : HasFiniteLength ρ₁) (hπ : IsSubquotient π.π (prod₂ ρ₁ ρ₂)) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (σ : Representation ℂ (GL (Fin r) k) Y),
      σ.IsIrreducible ∧ IsSubquotient σ ρ₁ ∧ IsSubquotient π.π (prod₂ σ ρ₂) := by
  refine exists_irreducible_of_pred (GL (Fin r) k) V ρ₁
    (fun Y _ _ σ => IsSubquotient π.π (prod₂ σ ρ₂)) hf₁ ?_ ?_ ?_ hπ
  · intro Y Y' _ _ _ _ σ σ' f hf h
    obtain ⟨I, hI, -⟩ := prod₂_exact_left k r t Y Y' W σ σ' ρ₂ f hf
    exact h.trans (IsSubquotient.of_injective I hI)
  · intro Y _ _ σ h
    exact (nontrivial_of_prod₂ π σ ρ₂ h).1
  · intro A B hBA h
    let i : B.toRepresentation.IntertwiningMap A.toRepresentation :=
      ⟨Submodule.inclusion hBA, fun _ => rfl⟩
    let q : A.toRepresentation.IntertwiningMap (subQuot A B) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    obtain ⟨I, hI, hQ⟩ := prod₂_exact_left k r t B.toSubmodule A.toSubmodule W B.toRepresentation
      A.toRepresentation ρ₂ i (Submodule.inclusion_injective hBA)
    obtain ⟨Q, hQ'⟩ := hQ _ (subQuot A B) q (Submodule.Quotient.mk_surjective _)
      (fun a => (Submodule.Quotient.mk_eq_zero (B.toSubmodule.comap A.toSubmodule.subtype)).2 a.2) (by
      intro b hb
      exact ⟨⟨b.1, (Submodule.Quotient.mk_eq_zero (B.toSubmodule.comap A.toSubmodule.subtype)).1 hb⟩,
        Subtype.ext rfl⟩)
    exact subquot_dichotomy _ _ _ _ _ π.π _ _ _ I Q π.irr hQ' h

theorem step_right {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r t : ℕ} (π : Irr k (r + t)) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ₁ : Representation ℂ (GL (Fin r) k) V) (ρ₂ : Representation ℂ (GL (Fin t) k) W)
    (hf₂ : HasFiniteLength ρ₂) (hπ : IsSubquotient π.π (prod₂ ρ₁ ρ₂)) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (σ : Representation ℂ (GL (Fin t) k) Y),
      σ.IsIrreducible ∧ IsSubquotient σ ρ₂ ∧ IsSubquotient π.π (prod₂ ρ₁ σ) := by
  refine exists_irreducible_of_pred (GL (Fin t) k) W ρ₂
    (fun Y _ _ σ => IsSubquotient π.π (prod₂ ρ₁ σ)) hf₂ ?_ ?_ ?_ hπ
  · intro Y Y' _ _ _ _ σ σ' f hf h
    obtain ⟨I, hI, -⟩ := prod₂_exact_right k r t V Y Y' ρ₁ σ σ' f hf
    exact h.trans (IsSubquotient.of_injective I hI)
  · intro Y _ _ σ h
    exact (nontrivial_of_prod₂ π ρ₁ σ h).2
  · intro A B hBA h
    let i : B.toRepresentation.IntertwiningMap A.toRepresentation :=
      ⟨Submodule.inclusion hBA, fun _ => rfl⟩
    let q : A.toRepresentation.IntertwiningMap (subQuot A B) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    obtain ⟨I, hI, hQ⟩ := prod₂_exact_right k r t V B.toSubmodule A.toSubmodule ρ₁ B.toRepresentation
      A.toRepresentation i (Submodule.inclusion_injective hBA)
    obtain ⟨Q, hQ'⟩ := hQ _ (subQuot A B) q (Submodule.Quotient.mk_surjective _)
      (fun a => (Submodule.Quotient.mk_eq_zero (B.toSubmodule.comap A.toSubmodule.subtype)).2 a.2) (by
      intro b hb
      exact ⟨⟨b.1, (Submodule.Quotient.mk_eq_zero (B.toSubmodule.comap A.toSubmodule.subtype)).1 hb⟩,
        Subtype.ext rfl⟩)
    exact subquot_dichotomy _ _ _ _ _ π.π _ _ _ I Q π.irr hQ' h

theorem irreducible_subquotient_prod₂ : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ₁ : Representation ℂ (GL (Fin r) k) V) (ρ₂ : Representation ℂ (GL (Fin t) k) W) (π : Irr k (r + t)), IsSmooth ρ₁ → IsSmooth ρ₂ → HasFiniteLength ρ₁ → HasFiniteLength ρ₂ → IsSubquotient π.π (prod₂ ρ₁ ρ₂) → ∃ (π₁ : Irr k r) (π₂ : Irr k t), IsSubquotient π₁.π ρ₁ ∧ IsSubquotient π₂.π ρ₂ ∧ IsSubquotient π.π (prod₂ π₁.π π₂.π) := by
  intro _hBZ k _ _ _ _ r t V W _ _ _ _ ρ₁ ρ₂ π h₁ h₂ hf₁ hf₂ hπ
  obtain ⟨Y₁, _, _, σ₁, hσ₁, hsq₁, hP₁⟩ := step_left π ρ₁ ρ₂ hf₁ hπ
  obtain ⟨Y₂, _, _, σ₂, hσ₂, hsq₂, hP₂⟩ := step_right π σ₁ ρ₂ hf₂ hP₁
  exact ⟨{ V := Y₁, π := σ₁, smooth := hsq₁.isSmooth h₁, irr := hσ₁ },
    { V := Y₂, π := σ₂, smooth := hsq₂.isSmooth h₂, irr := hσ₂ }, hsq₁, hsq₂, hP₂⟩

end GlobalTheory.ProdSubquot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbeddingStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligneParamAbove_l_independent_localEmbedding : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Om l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (Bw' : LocBridge l E Ω (Dec (F := E) A) O') (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)), Continuous (fun g => ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) → GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw' r → GlobalTheory.Pst.wdAt P ι Bw h hj r = GlobalTheory.Pst.wdAt P ι Bw' h hj' r := by
  first | exact @GlobalTheory.Pst.BridgeParam.wdAt_indep_bridge | exact GlobalTheory.Pst.BridgeParam.wdAt_indep_bridge | (intros; apply GlobalTheory.Pst.BridgeParam.wdAt_indep_bridge <;> assumption)
end

