module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0217
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RedBasicsPf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodAtReductionConjugatedUnitaryElement
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0135
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0376
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1620
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0424
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0099
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeRationalFlagIffRationalUnipot
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0048
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FinalClosed
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.DegIUp
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadingMinorLineUnitAmplitudesLargeGaps
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.LocalRingCardinality.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldFiniteAdeleTensorEquivMemIntegralAdeles
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

open IsDedekindDomain

namespace GlobalTheory.FixedConj

theorem comm_tensCastR_symm_mem_intAf {E : Type} [Field E] [NumberField E] {F₁ F₂ : Subfield E} (h : F₁ = F₂)
    (x : E ⊗[F₂] FiniteAdeleRing (𝓞 F₂) F₂)
    (hx : x ∈ Subring.closure ({x | ∃ y : 𝓞 E, x = (y : E) ⊗ₜ[F₂] (1 : FiniteAdeleRing (𝓞 F₂) F₂)} ∪
      {x | ∃ a : FiniteAdeleRing (𝓞 F₂) F₂, (∀ v, a v ∈ v.adicCompletionIntegers F₂) ∧ x = (1 : E) ⊗ₜ[F₂] a})) :
    (Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E).toRingEquiv
      ((GlobalTheory.StdFrame.tensCastR h).symm x) ∈ Formalism.L2.Herm.intAf (↥F₁) E := by
  subst h
  have hS : Subring.closure ({x | ∃ y : 𝓞 E, x = (y : E) ⊗ₜ[F₁] (1 : FiniteAdeleRing (𝓞 F₁) F₁)} ∪
      {x | ∃ a : FiniteAdeleRing (𝓞 F₁) F₁, (∀ v, a v ∈ v.adicCompletionIntegers F₁) ∧ x = (1 : E) ⊗ₜ[F₁] a}) ≤
      (Formalism.L2.Herm.intAf (↥F₁) E).comap
        (((GlobalTheory.StdFrame.tensCastR (rfl : F₁ = F₁)).symm.trans
          (Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E).toRingEquiv : _ ≃+* _) : _ →+* _) := by
    rw [Subring.closure_le]
    rintro z (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · show (Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E)
          ((Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E).symm ((y : E) ⊗ₜ[F₁] 1)) ∈ _
      rw [AlgEquiv.apply_symm_apply]
      exact Subring.subset_closure (Or.inl ⟨⟨(y : E), ⟨y, rfl⟩⟩, rfl⟩)
    · show (Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E)
          ((Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E).symm ((1 : E) ⊗ₜ[F₁] a)) ∈ _
      rw [AlgEquiv.apply_symm_apply]
      exact Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  exact hS hx

theorem adeleEquiv_mem_intAf : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (a : ReciprocityTheory.Aut.AL D.host.E),
    a ∈ ReciprocityTheory.Aut.ALint D.host.E → GlobalTheory.FixedConj.adeleEquiv D hF a ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E := by
  intro D hF a ha
  exact comm_tensCastR_symm_mem_intAf hF a ha

end GlobalTheory.FixedConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDegreeOnePrimeFrameReducedMatrices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped Matrix

namespace GlobalTheory.RowLev

theorem exists_coords_of_frame {A κ : Type} [CommRing A] [CommRing κ] {n : ℕ} (R : Subring A)
    (L : Submodule R (Fin n → A)) (β : GL (Fin n) A)
    (hβ : ∀ y, y ∈ L ↔ ∀ i, ((β⁻¹ : GL (Fin n) A).1 *ᵥ y) i ∈ R) (r : R →+* κ) (hr : Function.Surjective r) :
    ∃ c : L →ₛₗ[r] (Fin n → κ), Function.Surjective c ∧
      (∀ y : L, c y = 0 ↔ (y : Fin n → A) ∈ RingHom.ker r • L) ∧
      ∀ (X : GL (Fin n) A) (M : Matrix (Fin n) (Fin n) κ),
        (∀ y ∈ L, X.1 *ᵥ y ∈ L) →
        (∀ i j (h : (β⁻¹ * X * β : GL (Fin n) A).1 i j ∈ R), r ⟨_, h⟩ = M i j) →
        ∀ (y : L) (h : X.1 *ᵥ (y : Fin n → A) ∈ L), c ⟨_, h⟩ = M *ᵥ c y := by
  classical
  set B : Matrix (Fin n) (Fin n) A := (β⁻¹ : GL (Fin n) A).1 with hB
  have hBβ : B * β.1 = 1 := by rw [hB]; exact Units.inv_mul β
  have hβB : β.1 * B = 1 := by rw [hB]; exact Units.mul_inv β
  have hmem : ∀ y : L, ∀ i, (B *ᵥ (y : Fin n → A)) i ∈ R := fun y => (hβ y).1 y.2

  have hcol : ∀ j, (fun k => β.1 k j) ∈ L := by
    intro j
    refine (hβ _).2 fun i => ?_
    have e : (B *ᵥ fun k => β.1 k j) i = (B * β.1) i j := by
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    change (B *ᵥ fun k => β.1 k j) i ∈ R
    rw [e, hBβ, Matrix.one_apply]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem

  have hexp : ∀ v : Fin n → A, v = ∑ j, (B *ᵥ v) j • (fun k => β.1 k j) := by
    intro v
    have h1 : β.1 *ᵥ (B *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hβB, Matrix.one_mulVec]
    conv_lhs => rw [← h1]
    funext k
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  let c : L →ₛₗ[r] (Fin n → κ) :=
    { toFun := fun y i => r ⟨(B *ᵥ (y : Fin n → A)) i, hmem y i⟩
      map_add' := by
        intro y z
        funext i
        have e : (⟨(B *ᵥ ((y + z : L) : Fin n → A)) i, hmem (y + z) i⟩ : R) =
            ⟨_, hmem y i⟩ + ⟨_, hmem z i⟩ := Subtype.ext (by simp [Matrix.mulVec_add])
        simp only [Pi.add_apply]
        rw [e, map_add (f := _)]
      map_smul' := by
        intro a y
        funext i
        have e : (⟨(B *ᵥ ((a • y : L) : Fin n → A)) i, hmem (a • y) i⟩ : R) = a * ⟨_, hmem y i⟩ := by
          apply Subtype.ext
          change (B *ᵥ ((a : A) • (y : Fin n → A))) i = (a : A) * (B *ᵥ (y : Fin n → A)) i
          rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [e, map_mul] }
  have hc : ∀ (y : L) i, c y i = r ⟨(B *ᵥ (y : Fin n → A)) i, hmem y i⟩ := fun _ _ => rfl
  refine ⟨c, ?_, ?_, ?_⟩
  ·
    intro v
    choose x hx using fun i => hr (v i)
    set y0 : Fin n → A := β.1 *ᵥ fun i => (x i : A) with hy0
    have hc0 : ∀ i, (B *ᵥ y0) i = x i := by
      intro i
      rw [hy0, Matrix.mulVec_mulVec, hBβ, Matrix.one_mulVec]
    have hm : y0 ∈ L := (hβ y0).2 fun i => by rw [hc0 i]; exact (x i).2
    refine ⟨⟨y0, hm⟩, ?_⟩
    funext i
    rw [hc, ← hx i]
    congr 1
    exact Subtype.ext (hc0 i)
  · intro y
    constructor
    · intro hy
      have hk : ∀ j, (⟨_, hmem y j⟩ : R) ∈ RingHom.ker r := by
        intro j
        rw [RingHom.mem_ker, ← hc]
        exact congrFun hy j
      have e : (y : Fin n → A) = ∑ j, (⟨_, hmem y j⟩ : R) • (fun k => β.1 k j) := hexp _
      rw [e]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hk j) (hcol j)
    · intro hy
      have key : ∀ i, ∃ h : (B *ᵥ (y : Fin n → A)) i ∈ R, r ⟨_, h⟩ = 0 := by
        refine Submodule.smul_induction_on
          (p := fun z : Fin n → A => ∀ i, ∃ h : (B *ᵥ z) i ∈ R, r ⟨_, h⟩ = 0) hy ?_ ?_
        · intro a ha m hm i
          have e : (B *ᵥ (a • m)) i = (a : A) * (B *ᵥ m) i := by
            change (B *ᵥ ((a : A) • m)) i = _
            rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
          have hm' : (B *ᵥ m) i ∈ R := (hβ m).1 hm i
          refine ⟨e ▸ R.mul_mem a.2 hm', ?_⟩
          have e2 : (⟨(B *ᵥ (a • m)) i, e ▸ R.mul_mem a.2 hm'⟩ : R) = a * ⟨_, hm'⟩ := Subtype.ext e
          rw [e2, map_mul, (RingHom.mem_ker).1 ha, zero_mul]
        · intro u v hu hv i
          obtain ⟨h1, e1⟩ := hu i
          obtain ⟨h2, e2⟩ := hv i
          have e : (B *ᵥ (u + v)) i = (B *ᵥ u) i + (B *ᵥ v) i := by
            rw [Matrix.mulVec_add, Pi.add_apply]
          refine ⟨e ▸ R.add_mem h1 h2, ?_⟩
          have e3 : (⟨(B *ᵥ (u + v)) i, e ▸ R.add_mem h1 h2⟩ : R) = ⟨_, h1⟩ + ⟨_, h2⟩ := Subtype.ext e
          rw [e3, map_add (f := _), e1, e2, add_zero]
      funext i
      obtain ⟨_, h⟩ := key i
      rw [hc]
      exact h
  · intro X M hXL hM y h
    have hP : ∀ i j, (β⁻¹ * X * β : GL (Fin n) A).1 i j ∈ R := by
      intro i j
      have hXc : X.1 *ᵥ (fun k => β.1 k j) ∈ L := hXL _ (hcol j)
      have e : (β⁻¹ * X * β : GL (Fin n) A).1 i j = (B *ᵥ (X.1 *ᵥ fun k => β.1 k j)) i := by
        rw [Units.val_mul, Units.val_mul, ← hB, Matrix.mulVec_mulVec]
        simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
      rw [e]
      exact (hβ _).1 hXc i
    have hPv : B *ᵥ (X.1 *ᵥ (y : Fin n → A)) =
        (β⁻¹ * X * β : GL (Fin n) A).1 *ᵥ (B *ᵥ (y : Fin n → A)) := by
      rw [Units.val_mul, Units.val_mul, ← hB, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_assoc (B * X.1), hβB, Matrix.mul_one]
    funext i
    have e : (⟨(B *ᵥ (X.1 *ᵥ (y : Fin n → A))) i, hmem ⟨_, h⟩ i⟩ : R) =
        ∑ j, (⟨_, hP i j⟩ : R) * ⟨_, hmem y j⟩ := by
      apply Subtype.ext
      change (B *ᵥ (X.1 *ᵥ (y : Fin n → A))) i = _
      rw [hPv]
      simp [Matrix.mulVec, dotProduct]
    rw [hc]
    change r ⟨(B *ᵥ (X.1 *ᵥ (y : Fin n → A))) i, hmem ⟨_, h⟩ i⟩ = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    simp only [map_mul, hM, Matrix.mulVec, dotProduct, hc]

private theorem hatL_eq_Lf' (I : Formalism.MainNotions.S.AutInst) : Formalism.L2.Herm.hatL (F := I.F) I.L = I.Lf := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS Formalism.MainNotions.S.AutInst.Lf Formalism.MainNotions.S.lamAf
  rw [Set.image_eq_range]
  rfl

theorem exists_plFrame_of_isFrame : ∀ (I : Formalism.MainNotions.S.AutInst) (β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), Formalism.L2.DIV.IsFrame β₀ I.L → ∀ (N p : ℕ) (hN : I.n = N) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E)), p.Prime → Nat.card (𝓞 I.E ⧸ w.asIdeal) = p → ∃ fr : GlobalTheory.RowLev.PlFrame I N p w, ∀ k ∈ I.Kset, ∀ M : Matrix (Fin N) (Fin N) (ZMod p), (∀ (i j : Fin N) (hij : ((β₀⁻¹ * (k : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) (Fin.cast hN.symm i) (Fin.cast hN.symm j) ∈ Formalism.L2.Herm.intAf I.F I.E), Formalism.L2.DIV.resS I.F w ⟨_, hij⟩ = ((M i j).val : Formalism.L2.DIV.kP w)) → fr.ActsAs k M := by
  intro I β₀ hF N p hN w hp hcard
  subst hN
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hL : ∀ y, y ∈ I.Lf ↔
      ∀ i, ((β₀⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)).1 *ᵥ y) i ∈ Formalism.MainNotions.S.IntAf I.F I.E := by
    intro y
    rw [← hatL_eq_Lf' I]
    exact hF y

  have : Finite (Formalism.L2.DIV.kP w) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  let : Fintype (Formalism.L2.DIV.kP w) := Fintype.ofFinite _
  have hcard' : Fintype.card (Formalism.L2.DIV.kP w) = p := by rw [Fintype.card_eq_nat_card]; exact hcard
  have : CharP (Formalism.L2.DIV.kP w) p := charP_of_card_eq_prime hcard'
  let e : ZMod p ≃+* Formalism.L2.DIV.kP w := ZMod.ringEquiv (Formalism.L2.DIV.kP w) hcard'
  let r : Formalism.MainNotions.S.IntAf I.F I.E →+* ZMod p :=
    (e.symm : Formalism.L2.DIV.kP w →+* ZMod p).comp (Formalism.L2.DIV.resS I.F w)
  have hr : ∀ s, r s = e.symm (Formalism.L2.DIV.resS I.F w s) := fun _ => rfl
  have hres : ∀ a : 𝓞 I.E, r (Formalism.L2.DIV.oToS I.F I.E a) = 0 ↔ a ∈ w.asIdeal := by
    intro a
    rw [hr, Formalism.L2.DIV.resS_oToS, map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  have hrs : Function.Surjective r := by
    intro q
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := w.asIdeal) (e q)
    refine ⟨Formalism.L2.DIV.oToS I.F I.E a, ?_⟩
    rw [hr, Formalism.L2.DIV.resS_oToS, ha, RingEquiv.symm_apply_apply]
  obtain ⟨c, hcs, hck, hca⟩ := exists_coords_of_frame (Formalism.MainNotions.S.IntAf I.F I.E) I.Lf β₀ hL r hrs
  have hker : RingHom.ker r = extId I w.asIdeal := by
    refine Inhab.ker_eq_extId hp.ne_zero r fun a => ?_
    have e1 : Inhab.psi I.F I.E a = Formalism.L2.DIV.oToS I.F I.E a := Subtype.ext rfl
    rw [e1]
    exact hres a
  refine ⟨{ r := r, r_ker := fun a h => ?_, c := c, c_surj := hcs, c_ker := fun y => ?_ }, ?_⟩
  · have e1 : (⟨_, h⟩ : Formalism.MainNotions.S.IntAf I.F I.E) = Formalism.L2.DIV.oToS I.F I.E a := Subtype.ext rfl
    rw [e1]
    exact hres a
  · rw [hck y, hker]
  · intro k hk M hM y h
    refine hca (k : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) M (fun y hy => Inhab.mulVec_mem hk hy)
      (fun i j hij => ?_) y h
    have h1 : Formalism.L2.DIV.resS I.F w ⟨_, hij⟩ = ((M i j).val : Formalism.L2.DIV.kP w) := hM i j hij
    rw [hr, h1, map_natCast, ZMod.natCast_zmod_val]

end GlobalTheory.RowLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRectangularConjInstanceMatrixStandardPsi
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.FixedConjMat

theorem fmat_iota (D : D7) (x : Formalism.L2.Theta.GA D (D.sp.Y 0)) :
    (Formalism.L2.SG.InstExistsPf.instOf D).fmat ((Formalism.IndefR.RationalEmbedding.iota D x).2) =
      (Formalism.IndefR.Lev.finE (D.sp.Y 0) x).1 := by
  have hb := (Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D x)).2
  have e : (Formalism.IndefR.RationalEmbedding.iota D).symm (Formalism.IndefR.RationalEmbedding.iota D x) = x :=
    (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply x
  rw [hb]
  erw [e]
  ext i j
  exact GlobalTheory.RedFrame.tauF_gen (Formalism.IndefR.RationalEmbedding.inst D) _

theorem finE_val_eq (D : D7) (V : HSp D) (g : Formalism.L2.Theta.GA D V) :
    (Formalism.IndefR.Lev.finE V g).1 = (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g).map (Formalism.IndefR.Lev.swapAE D) := rfl

theorem map_cast_swap (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) {m n : Type}
    (M : Matrix m n (ReciprocityTheory.Aut.AL D.host.E)) :
    (M.map (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm).map (Formalism.IndefR.Lev.swapAE D) =
      M.map (GlobalTheory.FixedConj.adeleEquiv D hF) := by
  ext i j
  rfl

theorem map_mul_eq_one {k l R S : Type} [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] [CommRing R]
    [CommRing S] (f : R →+* S) {A : Matrix k l R} {B : Matrix l k R} (h : A * B = 1) :
    A.map f * B.map f = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero f) (map_one f)]

theorem conj_map {k l R S : Type} [Fintype k] [Fintype l] [CommRing R] [CommRing S] (f : R →+* S)
    (T : Matrix k k S) (Ti : Matrix k k S) (B : Matrix k l R) (Y : Matrix l l R) (B' : Matrix l k R)
    (g : Matrix l l S) (hg : Y.map f = g) :
    T * (B * Y * B').map f * Ti = T * B.map f * g * (B'.map f * Ti) := by
  rw [Matrix.map_mul, Matrix.map_mul, hg]
  simp only [Matrix.mul_assoc]


set_option maxHeartbeats 1000000 in
theorem finE_conj_stdPsi (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (PY : RowPsi (Yc D 0) D.R.r)
    (t : Formalism.L2.Theta.GA D (Yc D 0)) (hP : StdPsi hF PY) :
    ∃ (U : Matrix (Fin (Yc D 0).rank) (Fin D.R.r) (Formalism.IndefR.Lev.EAf D))
      (U' : Matrix (Fin D.R.r) (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)), U * U' = 1 ∧ U' * U = 1 ∧
      ∀ y : Formalism.AUTREP.GAf D.host.E D.R.r, (Formalism.IndefR.Lev.finE (Yc D 0) (MulAut.conj t (PY.ψ y))).1 =
        HMul.hMul (HMul.hMul U (((y : GL (Fin D.R.r) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin D.R.r) (Fin D.R.r)
          (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.FixedConj.adeleEquiv D hF))) U' := by
  obtain ⟨⟨β, β', h1, h2, hβ⟩, -⟩ := hP
  have hbb := map_mul_eq_one (Formalism.IndefR.Lev.swapAE D) h1
  have hbb' := map_mul_eq_one (Formalism.IndefR.Lev.swapAE D) h2
  refine ⟨HMul.hMul (Formalism.IndefR.Lev.finE (Yc D 0) t).1 (β.map (Formalism.IndefR.Lev.swapAE D)),
    HMul.hMul (β'.map (Formalism.IndefR.Lev.swapAE D)) ((Formalism.IndefR.Lev.finE (Yc D 0) t)⁻¹).1, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (β.map _), hbb, Matrix.one_mul, Units.mul_inv]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (((Formalism.IndefR.Lev.finE (Yc D 0) t)⁻¹).1), Units.inv_mul,
      Matrix.one_mul, hbb']
  · intro y
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul]
    have e1 := finE_val_eq D (Yc D 0) (PY.ψ y)
    have e3 := e1.trans (congrArg (fun M => M.map (Formalism.IndefR.Lev.swapAE D)) (hβ y))
    rw [e3]
    exact conj_map _ _ _ _ _ _ _ (map_cast_swap D hF _)

theorem fmat_iota_conj_stdPsi : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (PY : RowPsi (Yc D 0) D.R.r) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)), StdPsi hF PY → ∃ (U : Matrix (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Fin D.R.r) (Formalism.IndefR.Lev.EAf D)) (U' : Matrix (Fin D.R.r) (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Formalism.IndefR.Lev.EAf D)), U * U' = 1 ∧ U' * U = 1 ∧ ∀ y : Formalism.AUTREP.GAf D.host.E D.R.r, (Formalism.L2.SG.InstExistsPf.instOf D).fmat ((Formalism.IndefR.RationalEmbedding.iota D (MulAut.conj t (PY.ψ y))).2) = U * ((y : GL (Fin D.R.r) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin D.R.r) (Fin D.R.r) (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.FixedConj.adeleEquiv D hF) * U' := by
  intro D hF PY t hP
  obtain ⟨U, U', h1, h2, h3⟩ := finE_conj_stdPsi D hF PY t hP
  exact ⟨U, U', h1, h2, fun y => (fmat_iota D _).trans (h3 y)⟩

end GlobalTheory.FixedConjMat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTermLatticeBaseFramesOfBasePoint
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold

theorem tg_of_base_point : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ t : TauC Y u u', ptPN t = toPts w → ∃ Λ, TG F F' t Λ := by
  intro D X Y u u' F F' w hZ hG t hpt
  have hcF : IsInCell (ZhatOM (ZhatL F F')) w := by
    refine ⟨(1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), 1, ?_, ?_, by rw [hZ]; simp⟩
    · intro i j
      exact ⟨fun h => Matrix.one_apply_ne h.ne, fun h => h ▸ Matrix.one_apply_eq i⟩
    · intro i j
      exact ⟨fun h => Matrix.one_apply_ne h.ne', fun h => h ▸ Matrix.one_apply_eq i⟩
  have hGw := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.gpt_eq F F' w hcF
  have hw : Formalism.L2.SG.PairVal.ptOf t.toTerm = w := Formalism.L2.SG.NGCut.NormalVectorPairings.toPts_inj _ _ hpt
  have hex : ∃ w, t.toTerm.atPt w ∧ t.toTerm.relevant := by
    by_contra h
    apply hG
    rw [← hGw, ← hpt]
    show GPt _ (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm)) = 0
    unfold Formalism.L2.SG.PairVal.ptOf
    rw [dite_eq_right h]
    exact Formalism.L2.SG.NGCut.NormalVectorPairings.GPt_junk D u u'
  obtain ⟨F'', ⟨hP, hmk⟩, -, hcell⟩ := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm hex
  rw [hw] at hcell
  have hΛ := (Y.rowsOK u).1 t.lam t.mem
  have hmk' : Formalism.L2.SG.TermDef.mk _ _ _ ⟨F'', hP⟩ = Formalism.L2.SG.TermDef.mk _ _ _ ⟨t.frame, t.rep.2.2.2.2⟩ := hmk
  have hrel := (Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) t.lam hΛ _ _).1 hmk'
  have hcell' : IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) t.frame)) w := ((Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) t.lam hΛ).2.1 _ _ hrel w).1 hcell
  have hGt : Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
    intro h0
    apply hG
    rw [← hGw]
    exact (Formalism.L2.SG.NGCut.LeadingMinorIntegrality.gpt_eq (T := Tu D u) (T' := Tu D u') _ _ w hcell').trans h0
  obtain ⟨-, γ, hγ, ⟨A, hA, hc⟩, ⟨B, hB, hd⟩⟩ := _root_.GlobalTheory.LocOver.witt_frames_at_point D (lf D (X.Fu u)) F t.frame F' w
    (Formalism.L2.SG.Corank.tu_ne_zero u) (Formalism.L2.SG.Corank.tu_ne_zero u') hGt hcell' hZ
  exact ⟨Formalism.HermitianLatticesTheory.gmap γ t.lam, γ, ⟨hγ, fun a => GlobalTheory.FlagChange.chg_sub_mem F.fl hA hc a⟩,
    ⟨hγ, fun a => GlobalTheory.FlagChange.chg_sub_mem F'.fl hB hd a⟩, rfl⟩

end GlobalTheory.Unfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeEqHarishChandraOfGap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory

theorem dsig_eq_fdegHC_of_gap : ∀ (D : D7), Ties D → ∀ (τ : D.what₂.Tau) (h : ℝ),
    Formalism.QuantumDeterminants.IsHCParam (lamSH D.R (D.hc τ)) → Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamSH D.R (D.hc τ)) h →
    Formalism.MainNotions.GapDS.thrE (epsSH D.R) + 1 < h → D.dsig τ = Formalism.QuantumDeterminants.fdegHC (lamSH D.R (D.hc τ)) := by
  intro D hT τ h hlam hg hth
  have hth' : Formalism.MainNotions.GapDS.thrE (epsSH D.R) < h :=
    lt_trans (lt_add_of_pos_right _ zero_lt_one) hth
  obtain ⟨H, i1, i2, σ, hσ, -⟩ := ReciprocityTheory.ChartRestriction.DS.dsExistsG_closed _ (epsSH D.R) _ hlam h hg hth'
  have hpq := Formalism.MainNotions.S.Pv.DegI.minpq_pos D
  have hp : 1 ≤ ReciprocityTheory.ChartRestriction.DS.pOf (epsSH D.R) := le_trans hpq (min_le_left _ _)
  have hq : 1 ≤ ReciprocityTheory.ChartRestriction.DS.qOf (epsSH D.R) := le_trans hpq (min_le_right _ _)
  have htrue : ∃ a, epsSH D.R a = true := by
    unfold ReciprocityTheory.ChartRestriction.DS.pOf at hp
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one hp)
    exact ⟨a, (Finset.mem_filter.mp ha).2⟩
  have hfalse : ∃ a, epsSH D.R a = false := by
    unfold ReciprocityTheory.ChartRestriction.DS.qOf at hq
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one hq)
    exact ⟨a, (Finset.mem_filter.mp ha).2⟩
  have hd := _root_.GlobalTheory.FdegGap.fdeg_gap D.cd D.s.cdScale hT.cdScale_tie _ (epsSH D.R) _ h hlam htrue hfalse hg hth H σ hσ
  exact (hT.dsig_tie τ H σ _ hσ hd).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadingMinorLineUnitAmplitudesLargeGapsStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leadingMinor_line_unitAmplitudes_largeGaps : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 → CellConv → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C : ℝ, ∀ Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → Big D large₂ Cl m₀ → cdScaleTie D → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W → ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ A₀ : LocS W, GoodS D lam' A₀ → ∀ l : ℕ, l ≤ D.R.rS + 1 → ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ AI : Finset (Fin (2 * D.R.rS + D.R.k + 1)) → LocS W, (∀ I, I.card = l → (∃ A : LocS W, GoodS D (lam' + s • epsI I) A) → GoodS D (lam' + s • epsI I) (AI I)) → ∃ a : Finset (Fin (2 * D.R.rS + D.R.k + 1)) → ℂ, (∀ I, I.card = l → (¬ ∃ A : LocS W, GoodS D (lam' + s • epsI I) A) → a I = 0) ∧ (∑ I ∈ univ.filter (fun I => I.card = l), ‖a I‖) ≤ large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2) ∧ ∀ μsec, IsSection D.R.k D.R.rS W.z W.z' μsec → ∀ γ p, RelPt D W.z W.z' γ p → ∀ θ', normWin D large₂ C1 θ' → ∀ νR, RMeas D W γ θ' νR → DminN W.z W.z' γ l • jhUnit D w w' A₀ μsec νR γ = ∑ I ∈ univ.filter (fun I => I.card = l), a I • jhUnit D w w' (AI I) μsec νR γ := by
  first | exact @GlobalTheory.CellMinorLineGap.minor_line | exact GlobalTheory.CellMinorLineGap.minor_line | (intros; apply GlobalTheory.CellMinorLineGap.minor_line <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsIdentificationFstEqOneOfFiniteAdelic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.RealTrivIota

theorem iotaX_fst_eq_one_of_mem_GfC : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (g : Formalism.L2.Theta.GA D (D.sp.Y 0)), g ∈ GfC (D.sp.Y 0) → (Formalism.L2.SG.RowsJoinPinned.iotaX X h g).1 = 1 := by
  intro D X h g hg
  exact (GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff X h g).2 hg

end GlobalTheory.RealTrivIota
end

