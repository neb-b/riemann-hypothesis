module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0246
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0002
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0082

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexStandardInfSkewThetaLatticeEqAbsNormPow
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.SkewIndex

open GlobalTheory.IndefiniteRowSideFullHecke.PolarLatticePairs GlobalTheory.ThetaLatticePoints GlobalTheory.MatrixLatticeIndex GlobalTheory.NormSum.MovedLattice

theorem one_inf_div {E : Type} [Field E] [NumberField E] (𝔪 𝔫 : Ideal (𝓞 E)) (h𝔫 : 𝔫 ≠ ⊥)
    (hc : IsCoprime 𝔪 𝔫) :
    (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ⊓ ((𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) / 𝔫) = 𝔪 := by
  have h𝔫' : (𝔫 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔫
  apply le_antisymm
  · obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 (inf_le_left : (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ⊓ _ ≤ 1)
    rw [← hI]
    have h2 : (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≤ (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) / 𝔫 := hI ▸ inf_le_right
    rw [FractionalIdeal.le_div_iff_mul_le h𝔫', ← FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_le_coeIdeal] at h2
    rw [FractionalIdeal.coeIdeal_le_coeIdeal]
    have hs : 𝔪 ⊔ 𝔫 = ⊤ := Ideal.isCoprime_iff_sup_eq.1 hc
    calc I = I * (𝔪 ⊔ 𝔫) := by rw [hs, Ideal.mul_top]
      _ = I * 𝔪 ⊔ I * 𝔫 := Ideal.mul_sup _ _ _
      _ ≤ 𝔪 := sup_le (by first | exact Ideal.mul_le_right | exact Ideal.mul_le_left) h2
  · refine le_inf FractionalIdeal.coeIdeal_le_one ?_
    rw [FractionalIdeal.le_div_iff_mul_le h𝔫']
    calc (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * 𝔫 ≤ 𝔪 * 1 := mul_le_mul' le_rfl FractionalIdeal.coeIdeal_le_one
      _ = 𝔪 := mul_one _

theorem mul_inf {E : Type} [Field E] [NumberField E] (A X Y : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hA : A ≠ 0) : A * (X ⊓ Y) = A * X ⊓ A * Y := by
  apply le_antisymm
  · exact le_inf (mul_le_mul' le_rfl inf_le_left) (mul_le_mul' le_rfl inf_le_right)
  · have e : A * X ⊓ A * Y = A * (A⁻¹ * (A * X ⊓ A * Y)) := by
      rw [← mul_assoc, mul_inv_cancel₀ hA, one_mul]
    rw [e]
    refine mul_le_mul' le_rfl (le_inf ?_ ?_)
    · calc A⁻¹ * (A * X ⊓ A * Y) ≤ A⁻¹ * (A * X) := mul_le_mul' le_rfl inf_le_left
        _ = X := by rw [← mul_assoc, inv_mul_cancel₀ hA, one_mul]
    · calc A⁻¹ * (A * X ⊓ A * Y) ≤ A⁻¹ * (A * Y) := mul_le_mul' le_rfl inf_le_right
        _ = Y := by rw [← mul_assoc, inv_mul_cancel₀ hA, one_mul]

variable (D : D7)

def skewEnt (𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) /
    ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)

theorem mem_skewLat_iff (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ) (x : Fin N → D.host.E) :
    x ∈ skewLat D 𝔪 N ↔ ∀ i, x i ∈ (skewEnt D 𝔪 : Submodule (𝓞 D.host.E) D.host.E) := by
  simp only [skewLat, skewEnt, Submodule.mem_pi, Set.mem_univ, true_implies]

theorem mem_YYl_skew_iff (𝔪 : Ideal (𝓞 D.host.E)) (a d : ℕ) (x : Matrix (Fin d) (Fin a) D.host.E) :
    x ∈ YYl D (stdL D a) (skewLat D 𝔪 d) ↔
      ∀ i j, x i j ∈ ((D.host.AA0 * skewEnt D 𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E) := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨c, hc, A, hA, rfl⟩ := hB
      have hAe : ∀ i j, A i j ∈ (skewEnt D 𝔪 : Submodule (𝓞 D.host.E) D.host.E) := by
        induction hA using Submodule.span_induction with
        | mem A hA =>
          intro i j
          have hj : (Pi.single j (1 : D.host.E) : Fin a → D.host.E) ∈ stdL D a := by
            simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_implies]
            intro k
            by_cases hk : k = j
            · subst hk; simp [Submodule.one_eq_range]
            · simp [Pi.single_apply, hk]
          have h := (mem_skewLat_iff D 𝔪 d _).1 (hA _ hj) i
          simpa [Matrix.mulVec_single] using h
        | zero => intro i j; simp
        | add A B _ _ h1 h2 => intro i j; simpa using add_mem (h1 i j) (h2 i j)
        | smul r A _ h => intro i j; simpa using Submodule.smul_mem _ r (h i j)
      intro i j
      simp only [Matrix.smul_apply, smul_eq_mul]
      exact FractionalIdeal.mul_mem_mul hc (hAe i j)
    | zero => intro i j; simp
    | add A B _ _ h1 h2 => intro i j; simpa using add_mem (h1 i j) (h2 i j)
    | smul r A _ h => intro i j; simpa using Submodule.smul_mem _ r (h i j)
  · intro hx
    rw [Matrix.matrix_eq_sum_single x]
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    have hij := hx i j
    rw [FractionalIdeal.coe_mul] at hij
    refine Submodule.mul_induction_on (C := fun r => Matrix.single i j r ∈ YYl D (stdL D a) (skewLat D 𝔪 d)) hij ?_ ?_
    · intro m hm n hn
      refine Submodule.subset_span ⟨m, hm, Matrix.single i j n, Submodule.subset_span fun v hv => ?_, ?_⟩
      · refine (mem_skewLat_iff D 𝔪 d _).2 fun k => ?_
        have hvj : v j ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
          simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at hv
          exact hv j
        obtain ⟨o, ho⟩ := Submodule.mem_one.1 hvj
        by_cases hk : k = i
        · subst hk
          simp only [Matrix.mulVec, dotProduct, Matrix.single_apply, true_and]
          rw [Finset.sum_eq_single j (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
          simp only [if_true]
          rw [← ho, mul_comm, ← Algebra.smul_def]
          exact Submodule.smul_mem _ o hn
        · have hk' : i ≠ k := Ne.symm hk
          simp [Matrix.mulVec, dotProduct, Matrix.single_apply, hk']
      · rw [Matrix.smul_single, smul_eq_mul]
    · intro x y hx hy
      simpa [Matrix.single_add] using add_mem hx hy

theorem La_skew_eq_map (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) (a d : ℕ) :
    La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) =
      (matIn D a d ((D.host.AA0 * skewEnt D 𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E)).map (ptHom D ⊤ δ a d) := by
  apply le_antisymm
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨w, hw, A, hA, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (GlobalTheory.CurveLattice.mem_lamOf D ⊤ δ w).1 hw
    refine ⟨((c : D.host.K) : D.host.E) • A, fun i j => ?_, ptHom_smul D ⊤ δ a d c A⟩
    have := (mem_YYl_skew_iff D 𝔪 a d A).1 hA i j
    rw [Matrix.smul_apply, smul_eq_mul, ← coe_alg, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ this
  · rintro _ ⟨z, hz, rfl⟩
    refine AddSubgroup.subset_closure ⟨δ, (GlobalTheory.CurveLattice.mem_lamOf D ⊤ δ δ).2 ⟨1, trivial, by simp⟩, z,
      (mem_YYl_skew_iff D 𝔪 a d z).2 hz, ?_⟩
    rfl

end GlobalTheory.SkewIndex

namespace GlobalTheory.SkewIndex

open GlobalTheory.IndefiniteRowSideFullHecke.PolarLatticePairs GlobalTheory.ThetaLatticePoints GlobalTheory.MatrixLatticeIndex GlobalTheory.NormSum.MovedLattice

theorem index_inter_skew : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → ∀ (a d : ℕ), ((La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))).index = Ideal.absNorm 𝔪 ^ (a * d) := by
  intro D δ hC 𝔪 h𝔪 hcop a d
  have hδ : δ ≠ 0 := (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 ⊤ δ hC).2.1
  have hN : Ideal.absNorm (D.host.conj • 𝔪) = Ideal.absNorm 𝔪 := UnusedSlot33.HK.absNorm_smul D.host 𝔪
  have h𝔫 : (D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) ≠ ⊥ := by
    intro h
    apply h𝔪
    rw [← Ideal.absNorm_eq_zero_iff, ← hN, h, Ideal.absNorm_bot]
  have hA := inverseHalfDifferent_ne_zero D
  have h𝔪' : (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 h𝔪
  have h𝔫' : ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 h𝔫
  have hJ : D.host.AA0 * skewEnt D 𝔪 ≠ 0 := mul_ne_zero hA (div_ne_zero h𝔪' h𝔫')
  have hcoef : coefLat D ⊤ = (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
    rw [coefLat_eq, ext, Ideal.map_top, FractionalIdeal.coeIdeal_top, one_mul]

  have hF : D.host.AA0 ⊓ D.host.AA0 * skewEnt D 𝔪 =
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) *
        (D.host.AA0 * skewEnt D 𝔪) := by
    rw [show D.host.AA0 ⊓ D.host.AA0 * skewEnt D 𝔪 = D.host.AA0 * 1 ⊓ D.host.AA0 * skewEnt D 𝔪 by rw [mul_one]]
    rw [← mul_inf _ _ _ hA, skewEnt, one_inf_div 𝔪 _ h𝔫 hcop, mul_left_comm, mul_div_cancel₀ _ h𝔫']
  have he : ∀ J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E,
      ((((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * J :
        FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E) =
        (D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) • (J : Submodule (𝓞 D.host.E) D.host.E) := by
    intro J
    apply le_antisymm
    · rw [FractionalIdeal.coe_mul]
      refine Submodule.mul_le.2 fun x hx y hy => ?_
      obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem_smul hb hy
    · refine Submodule.smul_le.2 fun b hb y hy => ?_
      rw [Algebra.smul_def]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hb) hy
  have hinf : (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup ⊓
      ((D.host.AA0 * skewEnt D 𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup =
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) • ((D.host.AA0 * skewEnt D 𝔪 :
        FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E)).toAddSubgroup := by
    rw [← he, ← hF, FractionalIdeal.coe_inf]
    rfl
  show (La0 D (tor0 D ⊤ δ) a d).relIndex (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) = _
  rw [La0_eq_map, La_skew_eq_map, AddSubgroup.relIndex_map_map_of_injective _ _ (ptHom_injective D ⊤ hδ a d)]
  have hc := card_matIn D a d ((D.host.AA0 * skewEnt D 𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
    Submodule (𝓞 D.host.E) D.host.E) (coefLat D ⊤)
  rw [hcoef, ← AddSubgroup.inf_relIndex_right, hinf, relIndex_smul _ hJ _ h𝔫, hN] at hc
  rw [show lat0 D ⊤ a d = matIn D a d (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) by rw [lat0, hcoef]]
  exact hc

end GlobalTheory.SkewIndex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStanding
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.BaseGoodPlace

open GlobalTheory.Idele WithZero
open GlobalTheory.StdDual (codiff codiff_ne_zero)

theorem psiUnr_of_not_le {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : ¬ differentIdeal ℤ (𝓞 D.host.F) ≤ v.asIdeal) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr ψ v := by
  classical
  intro x
  have hc := GlobalTheory.SplitUnram.count_codiff_eq_zero v (fun h => hv (Ideal.le_of_dvd h))
  set α : Af D.host.F := GlobalTheory.AdelicU.singleFin v x with hα
  have hαv : α v = x := GlobalTheory.AdelicU.evalV_singleFin_self v x
  have hαw : ∀ w, w ≠ v → α w = 0 := fun w hw => GlobalTheory.AdelicU.evalV_singleFin_ne hw x
  have h := GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1.1 (GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ) α
  have key : (∀ y ∈ v.adicCompletionIntegers D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v (x * y) = 1) ↔
      ∀ β : Af D.host.F, (∀ w, β w ∈ w.adicCompletionIntegers D.host.F) → ψ (pairA D.host.F 0 (β * α)) = 1 := by
    constructor
    · intro H β hβ
      have e : β * α = GlobalTheory.AdelicU.singleFin v (x * β v) := by
        apply GlobalTheory.AdelicU.af_ext
        intro u
        by_cases hu : u = v
        · subst hu
          rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]
          change β u * x = x * β u
          ring
        · rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]
      rw [e]
      exact H _ (hβ v)
    · intro H y hy
      have e : GlobalTheory.AdelicU.singleFin v y * α = GlobalTheory.AdelicU.singleFin v (x * y) := by
        rw [hα, ← GlobalTheory.AdelicU.singleFin_mul, mul_comm]
      have := H (GlobalTheory.AdelicU.singleFin v y) (fun w => by
        by_cases hw : w = v
        · subst hw
          change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin w y) ∈ _
          rw [GlobalTheory.AdelicU.evalV_singleFin_self]
          exact hy
        · change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin v y) ∈ _
          rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw]
          exact zero_mem _)
      rw [e] at this
      exact this
  rw [key, ← h, mem_adelicIdeal_iff codiff_ne_zero, HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro H
    have := H v
    rwa [hc, neg_zero, exp_zero, hαv] at this
  · intro H w
    by_cases hw : w = v
    · subst hw
      rw [hc, neg_zero, exp_zero, hαv]
      exact H
    · rw [hαw w hw, map_zero]
      exact zero_le

end GlobalTheory.BaseGoodPlace

namespace GlobalTheory.BaseGoodPlace

theorem trInf_eq_trace (D : D7) (x : Ainf D.host.F) :
    GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.trInf D x = Algebra.trace ℝ (mixedEmbedding.mixedSpace D.host.F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F x) := by
  classical
  rw [Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  simp only [Algebra.trace_complex_apply]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.trInf
  rw [← Fintype.sum_subtype_add_sum_subtype (fun w : InfinitePlace D.host.F => w.IsReal)]
  congr 1
  · refine Fintype.sum_congr _ _ fun w => ?_
    rw [InfinitePlace.mult_isReal, Nat.cast_one, one_mul, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply w.2,
      Complex.ofReal_re]
    simp
  · refine Fintype.sum_equiv (Equiv.subtypeEquivRight fun w => InfinitePlace.not_isReal_iff_isComplex) _ _ fun w => ?_
    have h := InfinitePlace.mult_isComplex ⟨w.1, InfinitePlace.not_isReal_iff_isComplex.1 w.2⟩
    simp only at h
    rw [h]
    push_cast
    rfl

end GlobalTheory.BaseGoodPlace

namespace GlobalTheory.BaseGoodPlace

theorem isStd_of_isStdChar {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := by
  refine ⟨hψ.1.1, hψ.1.2.2.1, fun a ha => ?_⟩
  have h2 : a.2 = 0 := by
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F (pairA D.host.F 0 1) = 0 := by
      show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (0 : Ainf D.host.F) = 0
      exact map_zero _
    have := congrArg Prod.snd (ha (pairA D.host.F 0 1) h0)
    rw [smul_eq_mul] at this
    have e : (1 : Af D.host.F) * a.2 = 0 := this
    simpa using e
  have ha' : a = pairA D.host.F a.1 0 := Prod.ext rfl h2
  obtain ⟨θ, hθ⟩ := hψ.2.1
  have h := hψ.2.2 θ hθ a.1
  rw [GlobalTheory.DualPairCompare.sum_infFam θ hθ, trInf_eq_trace] at h
  rw [ha']
  change psiInf D.host.F ψ a.1 = _
  rw [h]
  congr 1
  push_cast
  change _ = -(2 * ↑Real.pi * Complex.I) * ((Algebra.trace ℝ (mixedEmbedding.mixedSpace D.host.F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F a.1) : ℝ) : ℂ)
  ring

end GlobalTheory.BaseGoodPlace

namespace GlobalTheory.BaseGoodPlace

theorem exists_ram_prime_of_le (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F))
    (hle : differentIdeal ℤ (𝓞 D.host.F) ≤ v.asIdeal) :
    ∃ p : ℕ, p ∣ D.host.QS * D.host.q * D.host.d ∧ (p : 𝓞 D.host.F) ∈ v.asIdeal := by
  obtain ⟨p, -, h1, h2⟩ := UpperTheory.Ram.Fun.exists_prime_of_different_le D.host v hle
  exact ⟨p, h1, h2⟩

end GlobalTheory.BaseGoodPlace

namespace GlobalTheory.FunObj

theorem base_isGood_of_standing : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (W : G.Weil) (t : T),
    SquareStanding G t → ∀ B : Base D.host.F D.host.E, B.ψ = W.ψ →
      (∀ v ∈ B.P, ∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v) → B.IsGood D.sp.cm.sig := by
  intro D T L sc G μ₀ _hL W t hS B hB hP
  have hψ : IsStdChar D B.ψ (-1) := hB ▸ W.ψ_std
  refine { cm := GlobalTheory.AdelicU.isCMExt_host D
           galois := D.host.hostE_isGalois
           unram := GlobalTheory.InertOfConj.unram D
           std := GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ
           inert := ?_
           psiP := ?_ }
  · intro v w hw
    have hns : ¬ Formalism.MainNotions.KudlaSiegelWeil.Split D v := by
      rintro ⟨w1, w2, hne, h1, h2⟩
      apply hne
      have key : ∀ u : HeightOneSpectrum (𝓞 D.host.E), Formalism.MainNotions.KudlaSiegelWeil.Over D u v → u = w := fun u hu => by
        have hle : w.asIdeal ≤ u.asIdeal := by
          rw [← hw]
          exact Ideal.map_le_iff_le_comap.2 (le_of_eq hu.symm)
        exact HeightOneSpectrum.ext (w.isMaximal.eq_of_le u.isPrime.ne_top hle).symm
      rw [key w1 h1, key w2 h2]
    obtain ⟨h2, h3, hd, -⟩ := Formalism.MainNotions.KudlaSiegelWeil.inert_conditions_hold D v hns
    exact ⟨h2, h3, GlobalTheory.BaseGoodPlace.psiUnr_of_not_le hψ v hd⟩
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := hP v hv
    refine GlobalTheory.BaseGoodPlace.psiUnr_of_not_le hψ _ fun hle => ?_
    obtain ⟨p, hp, hpv⟩ := GlobalTheory.BaseGoodPlace.exists_ram_prime_of_le D _ hle
    have hpw : (p : 𝓞 D.host.E) ∈ w.asIdeal := by
      have h := hpv
      change (p : 𝓞 D.host.F) ∈ w.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) at h
      rwa [Ideal.mem_comap, map_natCast] at h
    apply hS.2 w hw
    obtain ⟨c, hc⟩ := hp
    rw [hc]
    push_cast
    exact w.asIdeal.mul_mem_right _ (w.asIdeal.mul_mem_right _ hpw)

end GlobalTheory.FunObj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCartanInvolutionHermitianSmulBlockDiagonalRein
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped nonZeroDivisors

open scoped ComplexOrder

namespace GlobalTheory.CartanBlocks

theorem posDef_fromBlocks_diag {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {A : Matrix m m ℂ} {D : Matrix n n ℂ} (hA : A.PosDef) (hD : D.PosDef) :
    (Matrix.fromBlocks A 0 0 D).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose, hA.1.eq, hD.1.eq, Matrix.conjTranspose_zero, Matrix.conjTranspose_zero]
  · have key : star x ⬝ᵥ (Matrix.fromBlocks A 0 0 D *ᵥ x) =
        star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (D *ᵥ (x ∘ Sum.inr)) := by
      simp [dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_mulVec, Function.comp_def, Matrix.mulVec,
        Pi.star_apply]
    rw [key]
    by_cases h1 : x ∘ Sum.inl = 0
    · have h2 : x ∘ Sum.inr ≠ 0 := by
        intro h2; apply hx; funext i; rcases i with i | i
        · exact congrFun h1 i
        · exact congrFun h2 i
      rw [h1]; simpa using hD.dotProduct_mulVec_pos h2
    · exact add_pos_of_pos_of_nonneg (hA.dotProduct_mulVec_pos h1) (hD.posSemidef.dotProduct_mulVec_nonneg _)

theorem posDef_blk {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) {A : Matrix (Fin p) (Fin p) ℂ}
    {D : Matrix (Fin q) (Fin q) ℂ} (hA : A.PosDef) (hD : D.PosDef) : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e A D).PosDef := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk
  rw [Matrix.reindex_apply]
  exact (posDef_fromBlocks_diag hA hD).submatrix e.symm.injective

theorem blk_conjTranspose {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (A : Matrix (Fin p) (Fin p) ℂ)
    (D : Matrix (Fin q) (Fin q) ℂ) : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e A D)ᴴ = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e Aᴴ Dᴴ := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, Matrix.conjTranspose_reindex, Matrix.fromBlocks_conjTranspose]

theorem isCartan_blk : ∀ {a b d : ℕ} (e : Fin a ⊕ Fin b ≃ Fin d) (GA sA : Matrix (Fin a) (Fin a) ℂ) (GB sB : Matrix (Fin b) (Fin b) ℂ) {κ : ℝ},
    0 < κ → Formalism.IndefR.Datum.IsCartanInv GA sA → Formalism.IndefR.Datum.IsCartanInv GB sB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan ((κ : ℂ) • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e GA GB) ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e sA sB).map (starRingEnd ℂ)) := by
  intro a b d e GA sA GB sB κ hκ hA hB
  obtain ⟨hA1, hA2, hA3⟩ := hA
  obtain ⟨hB1, hB2, hB3⟩ := hB
  set S := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e sA sB with hS
  set G := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e GA GB with hG
  have hSS : S * S = 1 := by rw [hS, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_mul, hA1, hB1, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_one]
  have hSGS : Sᴴ * G * S = G := by
    rw [hS, hG, blk_conjTranspose, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_mul, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_mul, hA2, hB2]
  have hGS : (G * S).PosDef := by
    rw [hS, hG, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_mul]; exact posDef_blk e hA3 hB3

  have hGH : Gᴴ = G := by
    have h4 : Sᴴ * Gᴴ = G * S := by rw [← Matrix.conjTranspose_mul]; exact hGS.1.eq
    have h5 : Sᴴ * Sᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hSS, Matrix.conjTranspose_one]
    calc Gᴴ = Sᴴ * (Sᴴ * Gᴴ) := by rw [← Matrix.mul_assoc, h5, Matrix.one_mul]
      _ = G := by rw [h4, ← Matrix.mul_assoc, hSGS]
  have hSG : Sᴴ * G = G * S := by
    have := hGS.1.eq
    rw [Matrix.conjTranspose_mul, hGH] at this
    exact this
  have hT : (S.map (starRingEnd ℂ))ᵀ = Sᴴ := by
    ext i j; simp [Matrix.conjTranspose_apply]
  have hMM : (S.map (starRingEnd ℂ)).map star = S := by
    ext i j; simp
  refine ⟨?_, ?_, ?_⟩
  · rw [← Matrix.map_mul, hSS, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [hT, hMM, Matrix.mul_smul, Matrix.smul_mul, hSGS]
  · intro x hx
    have hy : star x ≠ 0 := by simpa using hx
    have hv : S.map (starRingEnd ℂ) *ᵥ x = star (S *ᵥ star x) := by
      ext i; simp [Matrix.mulVec, dotProduct, star_sum, Pi.star_apply, mul_comm]
    have hpos : ((κ : ℂ) • (G * S)).PosDef := hGS.smul (by exact_mod_cast hκ)
    have key : (S.map (starRingEnd ℂ) *ᵥ x) ⬝ᵥ ((κ : ℂ) • G) *ᵥ star x =
        star (star x) ⬝ᵥ (((κ : ℂ) • (G * S)) *ᵥ star x) := by
      rw [hv, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_smul, hSG]
    rw [key]
    have := hpos.dotProduct_mulVec_pos hy
    exact (Complex.lt_def.1 this).1

end GlobalTheory.CartanBlocks
end

