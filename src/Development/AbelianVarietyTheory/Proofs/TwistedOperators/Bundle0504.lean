module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1433
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0491
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0377
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanCoordinateActionSymplectic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealSmulSplit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0230
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0454
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0066
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionLineOperatorSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ThetaLineDeriv
open GlobalTheory.WeilM GlobalTheory.LFun Filter Topology
open scoped Classical

theorem rho_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    {m : ℕ} (φ : Fin m → (Fin n × Fin d → AF F) → ℂ) :
    M.co.rho ψ u (∑ i, φ i) = ∑ i, M.co.rho ψ u (φ i) := by
  funext x
  simp only [Darboux.rho, schr, Finset.sum_apply, Finset.mul_sum]

theorem rho_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    M.co.rho ψ u 0 = 0 := by
  funext x
  simp only [Darboux.rho, schr, Pi.zero_apply, mul_zero]

private theorem hasDerivAt_clm_comp_of_tendsto_slope {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F] (c : ℝ → SInf F κ)
    (f c' : SInf F κ) (hc0 : c 0 = f) (hl : Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 c'))
    (T : SInf F κ →L[ℂ] ℂ) : HasDerivAt (fun t => T (c t)) (T c') 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hT := ((T.restrictScalars ℝ).continuous.tendsto c').comp hl
  refine hT.congr fun t => ?_
  simp only [Function.comp_apply, slope_def_module, sub_zero, hc0]
  rw [← map_sub]
  exact (T.restrictScalars ℝ).map_smul t⁻¹ (c t - f)

theorem hasDerivAt_eval {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F] (c : ℝ → SInf F κ) (f c' : SInf F κ)
    (hc0 : c 0 = f) (hl : Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 c')) (y : κ → mixedEmbedding.mixedSpace F) :
    HasDerivAt (fun t => c t y) (c' y) 0 := by
  have h := hasDerivAt_clm_comp_of_tendsto_slope c f c' hc0 hl
    ((BoundedContinuousFunction.evalCLM ℂ y).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ))
  simpa using h

theorem hasDerivAt_clm {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F] (c : ℝ → SInf F κ) (f c' : SInf F κ)
    (hc0 : c 0 = f) (hl : Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 c')) (T : SInf F κ →L[ℂ] ℂ) :
    HasDerivAt (fun t => T (c t)) (T c') 0 :=
  hasDerivAt_clm_comp_of_tendsto_slope c f c' hc0 hl T

end GlobalTheory.ThetaLineDeriv

namespace GlobalTheory.ThetaLineDeriv
open GlobalTheory.WeilM GlobalTheory.LFun Filter Topology
open scoped Classical

end GlobalTheory.ThetaLineDeriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReversedMinorProductMemHarmonicRowHighest
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RenamedMinors

variable {D : D7} {S T : HSp D}

def phi (C : Ctx S T) : MvPolynomial (FVar D T.rank S.rank) ℂ →ₐ[ℂ] Harm.Poly ℂ C.X.Ψ C.q0 C.X.p0 (Fin S.rank) :=
  C.toH.comp (MvPolynomial.rename fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2))

theorem phi_varF_pos (C : Ctx S T) (τ : D.what₂.Tau) (b a : ℕ) (hb : b < C.X.p0) (ha : a < S.rank) :
    phi C (varF τ b a) = MvPolynomial.C (((2 / fockScale D τ : ℝ) : ℂ)) *
      MvPolynomial.X (C.m.e τ, Sum.inr ⟨b, hb⟩, ⟨a, ha⟩) := by
  have hr := C.hr
  have hbm : b < T.rank := by omega
  rw [varF, dite_eq_left ⟨hbm, ha⟩, phi, AlgHom.comp_apply, MvPolynomial.rename_X, Ctx.toH, MvPolynomial.aeval_X]
  congr 2
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  dsimp only
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  rw [rowIdx_inr]
  simp only [revPos]
  rw [dite_eq_left ⟨hb, by omega⟩]

theorem phi_varF_neg (C : Ctx S T) (τ : D.what₂.Tau) (b a : ℕ) (hb : b < C.q0) (ha : a < S.rank) :
    phi C (varF τ (C.X.p0 + b) a) = MvPolynomial.C (((2 / fockScale D τ : ℝ) : ℂ)) *
      MvPolynomial.X (C.m.e τ, Sum.inl ⟨b, hb⟩, ⟨a, ha⟩) := by
  have hr := C.hr
  have hbm : C.X.p0 + b < T.rank := by omega
  rw [varF, dite_eq_left ⟨hbm, ha⟩, phi, AlgHom.comp_apply, MvPolynomial.rename_X, Ctx.toH, MvPolynomial.aeval_X]
  congr 2
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  dsimp only
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  rw [rowIdx_inl]
  simp only [revPos]
  rw [dite_eq_right (by simp)]

theorem phi_minorPlus (C : Ctx S T) (hle : C.X.p0 ≤ S.rank) (τ : D.what₂.Tau) (i : Fin C.X.p0) :
    phi C (minorPlus τ (i.val + 1)) = MvPolynomial.C ((((2 / fockScale D τ : ℝ) : ℂ)) ^ (i.val + 1)) *
      Harm.yMinor (C.m.e τ) i (fun b : Fin C.X.p0 => (Pi.single (Fin.castLE hle b) (1 : ℂ) : Fin S.rank → ℂ)) := by
  rw [minorPlus, AlgHom.map_det, Harm.yMinor]
  have h : (phi C).mapMatrix (Matrix.of fun α β : Fin (i.val + 1) =>
      (varF τ β α : MvPolynomial (FVar D T.rank S.rank) ℂ)) =
      (MvPolynomial.C (((2 / fockScale D τ : ℝ) : ℂ)) : Harm.Poly ℂ C.X.Ψ C.q0 C.X.p0 (Fin S.rank)) • (Matrix.of fun a b : Fin (i.val + 1) =>
        (Harm.yForm (C.m.e τ) (Harm.lead i a)
          ((fun b : Fin C.X.p0 => (Pi.single (Fin.castLE hle b) (1 : ℂ) : Fin S.rank → ℂ)) (Harm.lead i b)) :
            Harm.Poly ℂ C.X.Ψ C.q0 C.X.p0 (Fin S.rank)))ᵀ := by
    ext α β
    have hβ : (β : ℕ) < C.X.p0 := by have := β.2; have := i.2; omega
    have hα : (α : ℕ) < S.rank := by have := α.2; have := i.2; omega
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
      Matrix.transpose_apply, smul_eq_mul]
    rw [phi_varF_pos C τ β α hβ hα, Harm.yForm_single]
    rfl
  rw [h, Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin, ← map_pow]

theorem phi_minorMinus (C : Ctx S T) (hn : T.rank ≤ S.rank) (τ : D.what₂.Tau) (i : Fin C.q0) : ∃ κ : ℂ,
    phi C (minorMinus τ C.X.p0 (i.val + 1)) = MvPolynomial.C κ *
      Harm.xMinor (C.m.e τ) i (fun a : Fin C.q0 => (Pi.single (⟨S.rank - 1 - a, by
        have := C.hr; have := a.2; omega⟩ : Fin S.rank) (1 : ℂ) : Fin S.rank → ℂ)) := by
  have hr := C.hr
  have hi := i.2
  rw [minorMinus, AlgHom.map_det, Harm.xMinor]
  have h : (phi C).mapMatrix (Matrix.of fun α β : Fin (i.val + 1) =>
      (varF τ (C.X.p0 + β) (S.rank - (i.val + 1) + α) : MvPolynomial (FVar D T.rank S.rank) ℂ)) =
      ((MvPolynomial.C (((2 / fockScale D τ : ℝ) : ℂ)) : Harm.Poly ℂ C.X.Ψ C.q0 C.X.p0 (Fin S.rank)) • (Matrix.of fun a b : Fin (i.val + 1) =>
        (Harm.xForm (C.m.e τ) (Harm.lead i a)
          ((fun a : Fin C.q0 => (Pi.single (⟨S.rank - 1 - a, by
            have := a.2; omega⟩ : Fin S.rank) (1 : ℂ) : Fin S.rank → ℂ)) (Harm.lead i b)) :
            Harm.Poly ℂ C.X.Ψ C.q0 C.X.p0 (Fin S.rank)))ᵀ).submatrix Fin.revPerm id := by
    ext α β : 1
    have hβ : (β : ℕ) < C.q0 := by have := β.2; omega
    have hα : S.rank - (i.val + 1) + (α : ℕ) < S.rank := by have := α.2; omega
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
      Matrix.transpose_apply, smul_eq_mul, Matrix.submatrix_apply, id]
    rw [phi_varF_neg C τ β _ hβ hα, Harm.xForm_single]
    have := α.2
    congr 1
    exact congrArg _ (Prod.ext rfl (Prod.ext rfl (Fin.ext (by
      simp only [Harm.lead, Fin.coe_castLE, Fin.revPerm_apply, Fin.val_rev]
      omega))))
  refine ⟨((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (i.val + 1))) : ℤ) : ℂ) *
    (((2 / fockScale D τ : ℝ) : ℂ)) ^ (i.val + 1), ?_⟩
  rw [h, Matrix.det_permute, Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin]
  simp only [map_mul, map_pow, map_intCast]
  ring

theorem prod_range_pow_eq {σ : Type} (N : ℕ) (g : ℕ → MvPolynomial σ ℂ) (h : Fin N → MvPolynomial σ ℂ) (d : ℕ → ℕ)
    (hg : ∀ i : Fin N, ∃ κ : ℂ, g i = MvPolynomial.C κ * h i) :
    ∃ κ : ℂ, ∏ i ∈ Finset.range N, g i ^ d i = MvPolynomial.C κ * ∏ i : Fin N, h i ^ d i := by
  choose κ hκ using hg
  refine ⟨∏ i : Fin N, κ i ^ d i, ?_⟩
  rw [← Fin.prod_univ_eq_prod_range (fun i => g i ^ d i), map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hκ i, mul_pow, map_pow]

theorem phi_delta (C : Ctx S T) (hn : T.rank ≤ S.rank) (ap am : D.what₂.Tau → ℕ → ℕ) : ∃ κ : ℂ,
    phi C (delta (m := T.rank) (n := S.rank) (fun _ => C.X.p0) (fun _ => C.q0) ap am) =
      MvPolynomial.C κ * Harm.minorProd
        (fun σ (i : Fin C.q0) => am (C.m.e.symm σ) i - if (i : ℕ) + 1 < C.q0 then am (C.m.e.symm σ) (i + 1) else 0)
        (fun σ (i : Fin C.X.p0) => ap (C.m.e.symm σ) i - if (i : ℕ) + 1 < C.X.p0 then ap (C.m.e.symm σ) (i + 1) else 0)
        (fun _ (a : Fin C.q0) => (Pi.single (⟨S.rank - 1 - a, by
          have := C.hr; have := a.2; omega⟩ : Fin S.rank) (1 : ℂ) : Fin S.rank → ℂ))
        (fun _ (b : Fin C.X.p0) => (Pi.single (Fin.castLE (by have := C.hr; omega) b) (1 : ℂ) : Fin S.rank → ℂ)) := by
  have hr := C.hr
  have hle : C.X.p0 ≤ S.rank := by omega
  have hτ : ∀ τ : D.what₂.Tau, ∃ κ : ℂ, phi C (deltaAt (m := T.rank) (n := S.rank) τ C.X.p0 (ap τ) C.q0 (am τ)) =
      MvPolynomial.C κ *
        ((∏ i : Fin C.q0, Harm.xMinor (C.m.e τ) i (fun a : Fin C.q0 => (Pi.single (⟨S.rank - 1 - a, by
            have := a.2; omega⟩ : Fin S.rank) (1 : ℂ) : Fin S.rank → ℂ)) ^
            (am τ i - if (i : ℕ) + 1 < C.q0 then am τ (i + 1) else 0)) *
          ∏ i : Fin C.X.p0, Harm.yMinor (C.m.e τ) i
            (fun b : Fin C.X.p0 => (Pi.single (Fin.castLE hle b) (1 : ℂ) : Fin S.rank → ℂ)) ^
            (ap τ i - if (i : ℕ) + 1 < C.X.p0 then ap τ (i + 1) else 0)) := by
    intro τ
    rw [deltaAt, map_mul, map_prod, map_prod]
    simp only [map_pow]
    obtain ⟨κ1, h1⟩ := prod_range_pow_eq C.X.p0 (fun i => phi C (minorPlus τ (i + 1)))
      (fun i : Fin C.X.p0 => Harm.yMinor (C.m.e τ) i
        (fun b : Fin C.X.p0 => (Pi.single (Fin.castLE hle b) (1 : ℂ) : Fin S.rank → ℂ)))
      (fun i => ap τ i - if i + 1 < C.X.p0 then ap τ (i + 1) else 0)
      (fun i => ⟨_, phi_minorPlus C hle τ i⟩)
    obtain ⟨κ2, h2⟩ := prod_range_pow_eq C.q0 (fun i => phi C (minorMinus τ C.X.p0 (i + 1)))
      (fun i : Fin C.q0 => Harm.xMinor (C.m.e τ) i (fun a : Fin C.q0 => (Pi.single (⟨S.rank - 1 - a, by
            have := a.2; omega⟩ : Fin S.rank) (1 : ℂ) : Fin S.rank → ℂ)))
      (fun i => am τ i - if i + 1 < C.q0 then am τ (i + 1) else 0)
      (fun i => phi_minorMinus C hn τ i)
    refine ⟨κ1 * κ2, ?_⟩
    rw [h1, h2, map_mul]
    ring
  choose κ hκ using hτ
  refine ⟨∏ τ, κ τ, ?_⟩
  rw [delta, map_prod, Finset.prod_congr rfl (fun τ _ => hκ τ), Finset.prod_mul_distrib, ← map_prod, Harm.minorProd]
  congr 1
  exact Fintype.prod_equiv C.m.e _ _ (fun τ => by simp only [Equiv.symm_apply_apply])

end GlobalTheory.RenamedMinors


open GlobalTheory.RenamedMinors in
theorem GlobalTheory.RenamedMinors.renamed_delta_mem_rowHighest : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), T.rank ≤ S.rank → ∀ (ap am : D.what₂.Tau → ℕ → ℕ), ∃ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ), C.toH (MvPolynomial.rename (fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2)) (Formalism.IndefR.Datum.delta (m := T.rank) (n := S.rank) (fun _ => C.X.p0) (fun _ => C.q0) ap am)) ∈ Harm.rowHighest ℂ c c' ∧ C.toH (MvPolynomial.rename (fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2)) (Formalism.IndefR.Datum.delta (m := T.rank) (n := S.rank) (fun _ => C.X.p0) (fun _ => C.q0) ap am)) ≠ 0 := by
  intro D S T C hn ap am
  have hr := C.hr
  obtain ⟨κ, hκ⟩ := phi_delta C hn ap am
  refine ⟨fun σ (i : Fin C.q0) => am (C.m.e.symm σ) i - if (i : ℕ) + 1 < C.q0 then am (C.m.e.symm σ) (i + 1) else 0,
    fun σ (i : Fin C.X.p0) => ap (C.m.e.symm σ) i - if (i : ℕ) + 1 < C.X.p0 then ap (C.m.e.symm σ) (i + 1) else 0,
    ?_, ?_⟩
  · change phi C _ ∈ _
    rw [hκ, ← MvPolynomial.smul_eq_C_mul]
    refine Submodule.smul_mem _ κ (Harm.minorProd_mem_rowHighest _ _ fun t a b => ?_)
    rw [single_dotProduct, one_mul, Pi.single_apply, if_neg]
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.coe_castLE] at h'
    have := a.2
    have := b.2
    omega
  · change phi C _ ≠ 0
    have hf : Function.Injective fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2) :=
      Function.LeftInverse.injective (g := fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2))
        fun v => by simp only [revPos_revPos]
    have hinj : Function.Injective (phi C) := C.toH_bijective.1.comp (MvPolynomial.rename_injective _ hf)
    exact (map_ne_zero_iff (phi C) hinj).2 (GlobalTheory.FockDelta.delta_ne_zero _ _ _ _ (fun _ => by omega) hn)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeriesAverageOtherPlaceType
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

noncomputable section

namespace GlobalTheory.AvgTypeOther

section SeriesClosure

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.REAL MeasureTheory Matrix
open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes
open GlobalTheory.SeriesToClosure
open scoped TensorProduct InnerProductSpace

theorem hasTypeAt_of_isTypeAt {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (τ : D.what₂.Tau) (S : SPar) (φ : GA D V → ℂ) (hHC : GlobalTheory.Published.HarishChandraModules) (hθ : IsInfFam (D := D) θ)
    (hφ : IsAutFunSm θ V φ) (hty : IsTypeAt θ V τ S φ) : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ V τ S φ := by
  obtain ⟨H, i1, i2, σ, lam, ε, P, hE, hD, hP, hJ, hx⟩ := hty
  intro K hK δ hδ
  haveI : CompleteSpace H := hD.1
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hσ : Std ε σ := std_of_isDS hHC hD
  have hlam : Formalism.QuantumDeterminants.IsHCParam lam := GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS hE.1 hD
  have hx' : ∀ x, HasTypeAll (lieSet ε) (UJset ε) σ (res θ V τ P φ x) := fun x =>
    hasTypeAll_transport _ H H _ σ (gramAt D V τ) (Jm ε) P (isUnit_gram hP hJ) hP hJ (LinearIsometryEquiv.refl ℂ H)
      (fun _ _ _ => rfl) (fun g => φ (x * atTau θ V τ g)) (hasTypeAll_iff.2 (hx x))
  choose W hW hc v ℓ C h using hx'
  have hk : Continuous fun k : KG ε => atTau θ V τ (P⁻¹ * toMK k * P) :=
    (continuousOn_atTau hθ V τ).comp_continuous continuous_conjK
      fun k => conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))
  obtain ⟨e, he, hap⟩ := _root_.GlobalTheory.KFinApprox.approx_identity _ ε (GA D V) (fun x k => φ (x * atTau θ V τ (P⁻¹ * toMK k * P)))
    (hφ.cont.comp (continuous_fst.mul (hk.comp continuous_snd))) K hK δ hδ
  obtain ⟨m, a, c, ha, hQ, hA⟩ := exists_rank_one hθ hP hJ hσ he
  choose T hT hTv using fun j => exists_gkMap hθ hP hJ hσ hφ hW hc h (hA j)
  refine ⟨∑ j, T j ⟨a j, mem_kFin_iff.2 (ha j)⟩, Submodule.sum_mem _ fun j _ =>
    (le_sSup (a := LinearMap.range (T j)) ⟨H, _, _, σ, lam, ε, P, T j, hE, hlam, hD, hP, hJ, hT j, rfl⟩ :
      _ ≤ finPartOfType θ V τ S) ⟨_, rfl⟩, fun x hxK => ?_⟩
  have h1 := (moves_avg hθ hP hJ hσ he φ x _ _ _ _ (hW x) (hc x) (h x)).1.2.2.2.2 1 (one_mem_UJ ε)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [res_one hθ hP, sigma_one hσ.1, hQ, map_sum, map_smul, smul_eq_mul] at h1
  have h2 := h1.unique (hasSum_sum fun j _ => (Expn.summable_term (h x) (c j) (hσ.2.2.1 _ (ha j))).hasSum)
  have h3 := hap x hxK
  have h4 : φ (x * atTau θ V τ (P⁻¹ * toMK (1 : KG ε) * P)) = φ x := res_one hθ hP φ x
  simp only [Finset.sum_apply, hTv]
  rw [← h2, ← h4]
  exact h3

end SeriesClosure

section ClosureSeries

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
open GlobalTheory.ClosureSeries

theorem isTypeAt_of_hasTypeAt_model {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (V : HSp D) (τ : D.what₂.Tau) (S : SPar) (φ : GA D V → ℂ) (hUn : GlobalTheory.Published.DiscreteSeriesUpqUnique)
    (hHC : GlobalTheory.Published.HarishChandraModules) (hCW : GlobalTheory.Published.CasselmanWallach) (hθ : IsInfFam (D := D) θ)
    (H : Type) [i1 : NormedAddCommGroup H] [i2 : InnerProductSpace ℂ H]
    (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (lam₀ : Fin V.rank → ℝ) (ε₀ : Fin V.rank → Bool)
    (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hE₀ : IsEnum S lam₀ ε₀) (hP₀ : Formalism.QuantumDeterminants.IsHCParam lam₀)
    (hσ : IsDS ε₀ lam₀ σ) (hPu : IsUnit P) (hPG : Pᴴ * Formalism.REAL.Jm ε₀ * P = gramAt D V τ)
    (hφ : IsAutFunSm θ V φ) (hT : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ V τ S φ) : IsTypeAt θ V τ S φ := by
  refine ⟨H, i1, i2, σ, lam₀, ε₀, P, hE₀, hσ, hPu, hPG, fun x => ?_⟩
  have hfin : ∀ ψ ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.finPartOfType θ V τ S, ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ)) (v : Fin m → H),
      (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε₀) σ (ℓ j)) ∧ (∀ j, SmoothVec (GlobalTheory.SmoothGlob.lieSet ε₀) σ (v j)) ∧
      ∀ y ∈ UJset ε₀, ψ (x * atTau θ V τ (P⁻¹ * y * P)) = ∑ j, ℓ j (σ y (v j)) := by
    intro ψ hψ
    rw [GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.finPartOfType, sSup_eq_iSup'] at hψ
    refine Submodule.iSup_induction (motive := fun ψ : GA D V → ℂ => ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ))
      (v : Fin m → H), (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε₀) σ (ℓ j)) ∧
      (∀ j, SmoothVec (GlobalTheory.SmoothGlob.lieSet ε₀) σ (v j)) ∧
      ∀ y ∈ UJset ε₀, ψ (x * atTau θ V τ (P⁻¹ * y * P)) = ∑ j, ℓ j (σ y (v j))) _ hψ ?_ ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0,
      fun y _ => by simp⟩ ?_
    · rintro ⟨W, H', j1, j2, σ', lam, ε, P', T, hE, hHC', hD', hP', hJ', hGK, rfl⟩ ψ ⟨w, rfl⟩
      obtain ⟨rfl, rfl⟩ := GlobalTheory.SignedParTest.isEnum_unique hE hE₀
      obtain ⟨ℓ, hℓ, hv, he⟩ := coef_of_gkMap θ V τ hθ hHC hCW H' σ' lam ε P' T hHC' hD' hP' hJ' hGK w x
      obtain ⟨ℓ', v', hℓ', hv', he'⟩ := coef_transport hUn _ ε lam hHC' H H' σ σ' hσ hD' P P' _ hPu hP' hPG hJ'
        (fun y => T w (x * atTau θ V τ y)) ℓ w hℓ hv he
      exact ⟨1, fun _ => ℓ', fun _ => v', fun _ => hℓ', fun _ => hv', fun y hy => by simpa using he' y hy⟩
    · rintro a b ⟨m, ℓ, v, h1, h2, h3⟩ ⟨m', ℓ', v', h1', h2', h3'⟩
      refine ⟨m + m', Fin.append ℓ ℓ', Fin.append v v', fun j => ?_, fun j => ?_, fun y hy => ?_⟩
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simpa using h1 i
        · simpa using h1' i
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simpa using h2 i
        · simpa using h2' i
      · show a _ + b _ = _
        rw [h3 y hy, h3' y hy, Fin.sum_univ_add]
        simp
  set f : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ := fun y => φ (x * atTau θ V τ (P⁻¹ * y * P)) with hf
  have hcont : ContinuousOn (fun y : Matrix (Fin V.rank) (Fin V.rank) ℂ => x * atTau θ V τ (P⁻¹ * y * P))
      (UJset ε₀) := by
    refine (continuous_mul_left_GA V x).comp_continuousOn ?_
    refine (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).continuousOn ?_
    intro y hy
    exact GlobalTheory.LowTypeDetermined.conj_inv_mem hPu hPG hy
  have hfc : ContinuousOn f (UJset ε₀) := hφ.cont.comp_continuousOn hcont
  have hB := closure_model hHC hCW _ ε₀ lam₀ hP₀ H σ hσ f hfc
    (GlobalTheory.TypeSum.GrowthAtPlace.umg_atTau D θ hθ V τ φ hφ ε₀ P hPu hPG x) (by
      intro C hC δ hδ
      have hK : IsCompact ((fun y => x * atTau θ V τ (P⁻¹ * y * P)) '' (C ∩ UJset ε₀)) :=
        (hC.inter_right (isClosed_UJset ε₀)).image_of_continuousOn (hcont.mono Set.inter_subset_right)
      obtain ⟨ψ, hψ, happ⟩ := hT _ hK δ hδ
      obtain ⟨m, ℓ, v, h1, h2, h3⟩ := hfin ψ hψ
      refine ⟨m, ℓ, v, h1, h2, fun y hyC hy => ?_⟩
      rw [← h3 y hy]
      exact happ _ ⟨y, ⟨hyC, hy⟩, rfl⟩)
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hPu
  have a1 := Matrix.mul_nonsing_inv _ hd
  have a2 := Matrix.nonsing_inv_mul _ hd
  have hi : P⁻¹⁻¹ = P := Matrix.nonsing_inv_nonsing_inv _ hd
  have t3 := GlobalTheory.TypeSum.hasTypeAll_transport _ H H σ (fun g => σ (P * g * P⁻¹)) (Formalism.REAL.Jm ε₀)
    (gramAt D V τ) P⁻¹ (GlobalTheory.TypeSum.isUnit_Jm ε₀) (IsUnit.of_mul_eq_one _ a2) (by
      rw [show gramAt D V τ = Pᴴ * Formalism.REAL.Jm ε₀ * P from hPG.symm]
      calc (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε₀ * P) * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε₀ * (P * P⁻¹) := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [a1]; simp) (LinearIsometryEquiv.refl ℂ H) (fun g _ v => by
      have e : P * (P⁻¹ * g * P⁻¹⁻¹) * P⁻¹ = g := by
        rw [hi]
        calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
          _ = g := by rw [a1, Matrix.one_mul, Matrix.mul_one]
      show σ g v = σ (P * (P⁻¹ * g * P⁻¹⁻¹) * P⁻¹) v
      rw [e]) f hB
  have e' : (fun y => f (P⁻¹⁻¹ * y * P⁻¹)) = fun y => φ (x * atTau θ V τ y) := by
    funext y
    show φ (x * atTau θ V τ (P⁻¹ * (P⁻¹⁻¹ * y * P⁻¹) * P)) = φ (x * atTau θ V τ y)
    rw [hi]
    congr 3
    calc P⁻¹ * (P * y * P⁻¹) * P = (P⁻¹ * P) * y * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = y := by rw [a2, Matrix.one_mul, Matrix.mul_one]
  rw [e'] at t3
  exact GlobalTheory.TypeSum.hasTypeAll_iff.1 t3

end ClosureSeries


end GlobalTheory.AvgTypeOther

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThOInjective
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.ThetaTransformInj

theorem thO_injective : ∀ (D : D7) {n k : ℕ} (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E n) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → Mo.IsGood ψ' →
    ∀ {d : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (e : Fin k ≃ Fin d), G.det ≠ 0 →
    ∀ F₁ ∈ GlobalTheory.WeilM.schA D.host.F (Fin n × Fin k), ∀ F₂ ∈ GlobalTheory.WeilM.schA D.host.F (Fin n × Fin k),
      GlobalTheory.TripleRead.thO Mo ψ' G e F₁ = GlobalTheory.TripleRead.thO Mo ψ' G e F₂ → F₁ = F₂ := by
  intro D n k Xs Ws Mo ψ' χX χW om τ hH hG d G e hdet F₁ hF₁ F₂ hF₂ h
  obtain ⟨-, hstd, -, hdX, -, hdW, -⟩ := hH
  obtain ⟨T, hT, hTi⟩ := GlobalTheory.ThetaTransformInj.linear_injective D Mo ψ' G e hG hstd hdX hdW hdet
  rw [← hT F₁ hF₁, ← hT F₂ hF₂, ← sub_eq_zero, ← map_sub] at h
  exact sub_eq_zero.1 (hTi _ (Submodule.sub_mem _ hF₁ hF₂) h)

end GlobalTheory.ThetaTransformInj

end
end

