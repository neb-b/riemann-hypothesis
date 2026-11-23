module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPolynomialMulGaussianOfAnnihilated
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0199
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ConjPurelyImaginaryGenerator
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0202
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ExistsBaseRingOfConjugationFixedTensor
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0216
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0213
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0312

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicSchwartzSlicePolynomialGaussianOfAnnihilat
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.Slice

variable {D : D7}

theorem compAt_add' (θ : InfFam D) (τ : D.what₂.Tau) {m n : ℕ} (x y : Mx D m n) :
    compAt θ τ (x + y) = compAt θ τ x + compAt θ τ y :=
  Matrix.ext fun i j => by
    show θ τ (infPart D (x i j + y i j)) = θ τ (infPart D (x i j)) + θ τ (infPart D (y i j))
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _)]

theorem finMap_add {m n : ℕ} (x y : Mx D m n) :
    (x + y).map (finPart D) = x.map (finPart D) + y.map (finPart D) :=
  Matrix.ext fun i j => by
    show finPart D (x i j + y i j) = finPart D (x i j) + finPart D (y i j)
    rw [RingHom.map_add (f := _)]

theorem slice_polyGauss : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : RealMat V), (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ (N : ℕ), ∀ φ ∈ schwartzA θ V.rank n, (∀ L : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin n) ℂ), L.length = N → L.foldr (fun q g => annS V l s θ q.1 q.2 g) φ = 0) → ∀ x₀ : Mx D V.rank n, ∃ p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ, ∀ x : Mx D V.rank n, x.map (finPart D) = x₀.map (finPart D) → φ x = evalPoly p (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x) := by
  intro D θ hθ V n l s hs N φ hφ hL x₀
  have hE := fun z : D.what₂.Tau → Fin V.rank → Fin n → ℂ =>
    _root_.GlobalTheory.StdUnn.exists_unique_of_comp_finPart D θ hθ V.rank n (fun τ => Matrix.of (z τ)) x₀
  let ι : (D.what₂.Tau → Fin V.rank → Fin n → ℂ) → Mx D V.rank n := fun z => Classical.choose (hE z).exists
  have hι : ∀ z, (∀ τ, compAt θ τ (ι z) = Matrix.of (z τ)) ∧ (ι z).map (finPart D) = x₀.map (finPart D) :=
    fun z => Classical.choose_spec (hE z).exists
  have huniq : ∀ z x, (∀ τ, compAt θ τ x = Matrix.of (z τ)) → x.map (finPart D) = x₀.map (finPart D) → x = ι z :=
    fun z x h1 h2 => (hE z).unique ⟨h1, h2⟩ (hι z)
  have hline : ∀ z τ (X : Matrix (Fin V.rank) (Fin n) ℂ) (w : D.what₂.Tau → Fin V.rank → Fin n → ℂ),
      w τ = X → (∀ τ', τ' ≠ τ → w τ' = 0) → ∀ t : ℝ, ι (z + t • w) = ι z + lineAt θ τ X t := by
    intro z τ X w hw0 hw1 t
    have hLn : IsLineAt θ τ X (lineAt θ τ X) :=
      Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ V.rank n τ X)
    symm
    apply huniq
    · intro τ'
      rw [compAt_add', (hι z).1, hLn.2.2 t τ']
      ext i j
      by_cases h : τ' = τ
      · subst h
        rw [if_pos rfl]
        show z τ' i j + ((t : ℂ) • X) i j = z τ' i j + t • w τ' i j
        rw [hw0, Complex.real_smul]
        rfl
      · rw [if_neg h]
        show z τ' i j + (0 : Matrix (Fin V.rank) (Fin n) ℂ) i j = z τ' i j + t • w τ' i j
        rw [hw1 τ' h]
        simp
    · rw [finMap_add, (hι z).2, hLn.2.1 t, add_zero]
  have hcomm : ∀ τ X (g : Mx D V.rank n → ℂ),
      annC V l s τ X (fun z => g (ι z)) = fun z => annS V l s θ τ X g (ι z) := by
    intro τ X g
    funext z
    simp only [annC, annS]
    congr 1
    · congr 1
      funext t
      congr 1
      apply hline z τ X
      · simp
      · intro τ' h
        simp [h]
    · rw [(hι z).1]
  have hfold : ∀ L : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin n) ℂ),
      L.foldr (fun q g => annC V l s q.1 q.2 g) (fun z => φ (ι z)) =
        fun z => (L.foldr (fun q g => annS V l s θ q.1 q.2 g) φ) (ι z) := by
    intro L
    induction L with
    | nil => rfl
    | cons q L ih => simp only [List.foldr_cons, ih, hcomm]
  have hsm : ∀ ψ : Mx D V.rank n → ℂ, ψ ∈ schwartzA θ V.rank n → ContDiff ℝ ∞ (fun z => ψ (ι z)) := by
    intro ψ hψ
    unfold schwartzA at hψ
    induction hψ using Submodule.span_induction with
    | mem ψ hψ =>
      obtain ⟨f, g, -, rfl⟩ := hψ
      have e : (fun z => f (fun τ i j => compAt θ τ (ι z) i j) * g (fun i j => finPart D (ι z i j))) =
          fun z => f z * g (fun i j => finPart D (x₀ i j)) := by
        funext z
        congr 1
        · congr 1
          funext τ i j
          rw [(hι z).1]
          rfl
        · congr 1
          funext i j
          exact congrFun (congrFun (hι z).2 i) j
      simp only
      rw [e]
      exact (f.smooth ⊤).mul contDiff_const
    | zero => exact contDiff_const
    | add a b _ _ ha hb => exact ha.add hb
    | smul c a _ ha => exact ha.const_smul c
  have hsmooth := hsm φ hφ
  obtain ⟨p, hp⟩ := _root_.GlobalTheory.StdUnn.exists_poly_mul_gauss_of_annC D V n l s hs N (fun z => φ (ι z)) hsmooth (fun L hLN => by
    rw [hfold, hL L hLN]
    rfl)
  refine ⟨p, fun x hx => ?_⟩
  have hx' : x = ι (fun τ i j => compAt θ τ x i j) := huniq _ x (fun τ => rfl) hx
  calc φ x = φ (ι (fun τ i j => compAt θ τ x i j)) := by rw [← hx']
    _ = _ := hp _

end GlobalTheory.StdUnn.Slice

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AnnihilationOperatorDoubledHermitianSpaceDecomp
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnnAnnDec

theorem mul_split {b n k : ℕ} (W : Matrix (Fin b) (Fin (n + n)) ℂ) (N : Matrix (Fin (n + n)) (Fin k) ℂ) :
    W * N = W.submatrix id (fun i => finSumFinEquiv (Sum.inl i)) * N.submatrix (fun i => finSumFinEquiv (Sum.inl i)) id
      + W.submatrix id (fun i => finSumFinEquiv (Sum.inr i)) * N.submatrix (fun i => finSumFinEquiv (Sum.inr i)) id := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_add]

theorem annih_dec : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (μ : D.host.E), IsSkew μ → ∀ (s' : RealMat (dblSp A)) (sB : RealMat B), IsStdInv A μ s' → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) → ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ), ∃ (X X' : Matrix (Fin B.rank) (Fin A.rank) ℂ) (c : ℂ), ∀ f, IsThetaFunO ψ (dblSp A) B f → annih (heisO ψ (dblSp A) B) θ τ (cplxO (s' τ) (sB τ)) Y f = annih (heisO ψ (dblSp A) B) θ τ (cplxO (s' τ) (sB τ)) (X * (dblDec A).qX.map (tauE D τ)) f + c • annih (heisO ψ (dblSp A) B) θ τ (cplxO (s' τ) (sB τ)) (X' * (dblDec A).qX.map (tauE D τ)) f := by
  intro D ψ hψ θ hθ A B μ hμ s' sB hs hsB τ Y
  have hLine : LineAtExists D := fun θ hθ m n τ z => ⟨_, GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z⟩
  obtain ⟨hadd, hsm, -⟩ := Formalism.IndefR.Fock.DRho.dRhoLin D ψ θ hψ hθ hLine (dblSp A) B τ
  have hs2 : s' τ * s' τ = 1 := (GlobalTheory.CartStd.isCartanInv_stdInv D A μ hμ s' hs τ).1
  have hB2 : sB τ * sB τ = 1 := (hsB τ).1

  obtain ⟨-, hdet, hinv⟩ := GlobalTheory.StdUnn.Tm_gram_inv D A μ hμ
  have hTR : Tm A μ * (Tm A μ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hMN : (Tm A μ).map (tauE D τ) * ((Tm A μ)⁻¹).map (tauE D τ) = 1 := by
    rw [← Matrix.map_mul, hTR, Matrix.map_one _ (tauE D τ).map_zero (tauE D τ).map_one]
  have htop : (((Tm A μ)⁻¹).map (tauE D τ)).submatrix (fun i => finSumFinEquiv (Sum.inl i)) id =
      (dblDec A).qX.map (tauE D τ) := by
    rw [hinv]; ext i j
    simp only [Matrix.map_apply, Matrix.submatrix_apply, id, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl]
  have hbot : (((Tm A μ)⁻¹).map (tauE D τ)).submatrix (fun i => finSumFinEquiv (Sum.inr i)) id =
      (μ⁻¹ • (dblDec A).qY).map (tauE D τ) := by
    rw [hinv]; ext i j
    simp only [Matrix.map_apply, Matrix.submatrix_apply, id, Equiv.symm_apply_apply, Matrix.fromRows_apply_inr]
  have hμ0 : tauE D τ μ ≠ 0 := (map_ne_zero (tauE D τ)).2 hμ.1
  have hn0 : (‖tauE D τ μ‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hμ0)
  set q := (dblDec A).qX.map (tauE D τ) with hq
  set k : ℂ := (tauE D τ μ)⁻¹ * (‖tauE D τ μ‖ : ℂ) with hk
  have hqs := GlobalTheory.StdUnnAnnih.qX_mul_stdInv A μ hμ s' hs τ
  have hbot' : (μ⁻¹ • (dblDec A).qY).map (tauE D τ) = k • (q * s' τ) := by
    rw [hqs, smul_smul, hk, mul_assoc, mul_inv_cancel₀ hn0, mul_one]
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
  set W := Y * (Tm A μ).map (tauE D τ) with hW
  set P := W.submatrix id (fun i => finSumFinEquiv (Sum.inl i)) with hP
  set R := W.submatrix id (fun i => finSumFinEquiv (Sum.inr i)) with hR
  have hYd : Y = P * q + R * (k • (q * s' τ)) := by
    have h1 : Y = W * ((Tm A μ)⁻¹).map (tauE D τ) := by rw [hW, Matrix.mul_assoc, hMN, Matrix.mul_one]
    rw [h1, mul_split, htop, hbot, hbot']
  refine ⟨P, (-Complex.I * k) • (sB τ * R), -Complex.I, fun f hf => ?_⟩
  set J := cplxO (s' τ) (sB τ) with hJ
  have hJadd : ∀ Z Z' : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ, J (Z + Z') = J Z + J Z' := by
    intro Z Z'
    simp only [hJ, cplxO, Matrix.mul_add, Matrix.add_mul, smul_add]
  have hJJ : ∀ Z : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ, J (J Z) = -Z := by
    intro Z
    simp only [hJ, cplxO, Matrix.mul_smul, Matrix.smul_mul, smul_smul, Complex.I_mul_I]
    simp only [Matrix.mul_assoc]
    rw [hs2, ← Matrix.mul_assoc (sB τ) (sB τ), hB2, Matrix.one_mul, Matrix.mul_one, neg_one_smul]
  have hneg : ∀ Z : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ,
      dRho (heisO ψ (dblSp A) B) θ τ (-Z) f = -dRho (heisO ψ (dblSp A) B) θ τ Z f := by
    intro Z
    have h := hsm (-1) Z f hf
    simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_one_smul] at h
    exact h
  have hAadd : ∀ Z Z' : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ,
      annih (heisO ψ (dblSp A) B) θ τ J (Z + Z') f =
        annih (heisO ψ (dblSp A) B) θ τ J Z f + annih (heisO ψ (dblSp A) B) θ τ J Z' f := by
    intro Z Z'
    simp only [Formalism.IndefR.Datum.annih]
    rw [hJadd, hadd _ _ f hf, hadd _ _ f hf, smul_add]
    abel
  have hAJ : ∀ Z : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ,
      annih (heisO ψ (dblSp A) B) θ τ J (J Z) f = (-Complex.I) • annih (heisO ψ (dblSp A) B) θ τ J Z f := by
    intro Z
    simp only [Formalism.IndefR.Datum.annih]
    rw [hJJ, hneg]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    linear_combination (dRho (heisO ψ (dblSp A) B) θ τ (J Z) f x) * Complex.I_sq
  have hdir : J (((-Complex.I * k) • (sB τ * R)) * q) = R * (k • (q * s' τ)) := by
    have hc : Complex.I * (-Complex.I * k) = k := by linear_combination (-k) * Complex.I_sq
    simp only [hJ, cplxO, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (sB τ) (sB τ), hB2, Matrix.one_mul]
  rw [hYd, ← hdir, hAadd, hAJ]

end GlobalTheory.StdUnnAnnDec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanParametersAddCharUnique
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.RealPar

variable {D : D7}

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

theorem finPart_cA_eq (z : AE D) :
    finPart D (cA D z) = Algebra.TensorProduct.map (AlgHom.id D.host.F (Af D.host.F)) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cA, sigR, finPart]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]


open Classical in
theorem exists_real_point {θ : InfFam D} (hθ : IsInfFam θ) (τ₀ : D.what₂.Tau) (t : ℝ) :
    ∃ x : Ainf D.host.F, ∀ τ, θ τ (x ⊗ₜ[D.host.F] (1 : D.host.E)) = if τ = τ₀ then (t : ℂ) else 0 := by
  obtain ⟨w, ⟨hw, hf⟩, -⟩ := exists_unique_of_comp_finPart D θ hθ 1 1
    (fun τ => fun _ _ => if τ = τ₀ then (t : ℂ) else 0) 0
  set a : AE D := w 0 0 with ha
  have hcomp : ∀ τ, θ τ (infPart D a) = if τ = τ₀ then (t : ℂ) else 0 := fun τ => by
    have := congrFun (congrFun (hw τ) 0) 0
    simpa [compAt] using this
  have hfin : finPart D a = 0 := by
    have := congrFun (congrFun hf 0) 0
    rw [Matrix.map_apply, Matrix.map_apply, Matrix.zero_apply, map_zero] at this
    exact this
  have hRC := RealComp.real_components D θ hθ
  have hc : cA D a = a := by
    have h0 : cA D a - a = 0 := by
      apply hRC.2.2.2
      · intro τ
        rw [map_sub, map_sub, hRC.2.1 a τ, hcomp τ]
        split_ifs <;> simp
      · rw [map_sub, finPart_cA_eq, hfin]
        simp
    exact sub_eq_zero.mp h0
  obtain ⟨y, hy⟩ := GlobalTheory.DetRootRows.fixed_mem_range a hc
  refine ⟨fstA D.host.F y, fun τ => ?_⟩
  rw [← hcomp τ, ← hy]
  rfl

theorem realPar_unique : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ l l' : D.what₂.Tau → ℝ, HasRealPar ψ θ l → HasRealPar ψ θ l' → l = l' := by
  classical
  intro D ψ θ hθ l l' hl hl'
  funext τ₀
  by_contra hne
  have hd : l τ₀ - l' τ₀ ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨x, hx⟩ := exists_real_point hθ τ₀ (1 / (2 * (l τ₀ - l' τ₀)))
  have e := (hl x).symm.trans (hl' x)
  simp only [hx, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp e
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have h1 : ((l τ₀ : ℂ) - l' τ₀) * ((1 / (2 * (l τ₀ - l' τ₀)) : ℝ) : ℂ) = n := by
    apply mul_left_cancel₀ hpi
    linear_combination hn
  have h2 : ((l τ₀ : ℂ) - l' τ₀) * ((1 / (2 * (l τ₀ - l' τ₀)) : ℝ) : ℂ) = 1 / 2 := by
    have hd' : ((l τ₀ : ℂ) - l' τ₀) ≠ 0 := by exact_mod_cast hd
    push_cast
    field_simp
  rw [h2] at h1
  have h3 : ((n : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; exact h1.symm
  have h4 : (n : ℝ) = 1 / 2 := by exact_mod_cast h3
  have h5 : (2 : ℝ) * n = 1 := by rw [h4]; norm_num
  have h6 : (2 : ℤ) * n = 1 := by exact_mod_cast h5
  omega

end GlobalTheory.StdUnn.RealPar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFourierJacobiContractedIsThetaFunctionEachVariable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.ContrTheta

theorem continuous_linkKappa {D : D7} {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E}
    (l : Link B L' ζ') (S : HSp D) : Continuous (l.κ S) := by
  unfold Link.κ GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj
  have h : Continuous fun w : WO S L' => giA S ⬝ (adj (rat l.τ ⬝ w) ⬝ gA B.L) :=
    Continuous.matrix_mul continuous_const (Continuous.matrix_mul
      (GlobalTheory.MixModel.continuous_adj.comp (continuous_const.matrix_mul continuous_id)) continuous_const)
  exact h.const_smul ((incA D) (-D.host.xi0⁻¹))

theorem integrable_restrict_of_bdd {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (s : Set X) (hs : μ s = 1) (f : X → ℂ) (hf : Continuous f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    Integrable f (μ.restrict s) := by
  haveI : IsFiniteMeasure (μ.restrict s) := ⟨by rw [Measure.restrict_apply_univ, hs]; exact ENNReal.one_lt_top⟩
  exact (integrable_const C).mono' hf.aestronglyMeasurable (ae_of_all _ fun x => by simpa using hC x)

theorem contr_isTheta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (χA χA' χz : ((AE D)ˣ →* Circle)) (oma : Om B.A J.W₀) (omz : Om B.L J.W₀) (omb : Om J.W₀ B'.A) (omz' : Om J.W₀ B'.L), s₁.χV = χA * χz → s₂.χW = χA' * χz → IsWeilDatumO ψ B.A J.W₀ χA s₁.χW oma → IsWeilDatumO ψ B.L J.W₀ χz s₁.χW omz → IsWeilDatumO ψ J.W₀ B'.A s₂.χV χA' omb → IsWeilDatumO ψ J.W₀ B'.L s₂.χV χz omz' → ∀ (Ξ₁ : WO B.V₀ J.W₀ → ℂ) (Ξ₂ : WO J.W₀ B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ J.W₀ Ξ₁ → IsThetaFunO ψ J.W₀ B'.V₀ Ξ₂ → (∀ v, IsThetaFunO ψ B.A J.W₀ fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) ∧ ∀ p, (IsThetaFunO ψ J.W₀ B'.A fun v => oma p (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0) ∧ ∀ v, oma p (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0 = ∫ w in vL.𝓕, Ξ₂ ((B'.o.resT J.W₀).symm (v, w)) * oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, l.κ J.W₀ w))) 0 ∂vL.μ := by
  intro D ψ σ B J B' s₁ s₂ l vL χA χA' χz oma omz omb omz' _ _ hoa _ _ _ Ξ₁ Ξ₂ hΞ₁ hΞ₂
  have hstd : IsStdChar D ψ (-1) := hoa.std
  haveI hbor : ∀ m n, BorelSpace (Mx D m n) := fun _ _ => ⟨rfl⟩
  have hκ : Continuous (l.κ J.W₀) := continuous_linkKappa l J.W₀
  have hκm : Measurable (l.κ J.W₀) := hκ.measurable
  have hvol : vL.μ vL.𝓕 = 1 := vL.covol.2.2
  have ha : ∀ v, Integrable (fun w => Ξ₂ ((B'.o.resT J.W₀).symm (v, w))) (vL.μ.restrict vL.𝓕) := by
    intro v
    obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded _ _ ψ hstd Ξ₂ hΞ₂
    exact integrable_restrict_of_bdd _ _ hvol _ (hΞ₂.cont.comp ((OrthDec.continuous_resT_symm _ _).comp
      (Continuous.prodMk continuous_const continuous_id))) C (fun w => hC _)
  have hG : ∀ p, IsThetaFunO ψ B.V₀ J.W₀ (fun x => oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, (B.o.resS J.W₀ x).2)))
      (B.o.resS J.W₀ x).1) := fun p =>
    (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ B.V₀ B.A B.L J.W₀ B.o χA s₁.χW oma hoa Ξ₁ hΞ₁ _ (vL.μ.restrict vL.𝓕) (l.κ J.W₀) _ hκm (ha 0) p).1
  have hb : ∀ p, Integrable (fun w => oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, l.κ J.W₀ w))) 0)
      (vL.μ.restrict vL.𝓕) := by
    intro p
    obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded _ _ ψ hstd _ (hG p)
    have heq : (fun w => oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, l.κ J.W₀ w))) 0) = fun w =>
        (fun x => oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, (B.o.resS J.W₀ x).2))) (B.o.resS J.W₀ x).1)
          ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) := by
      funext w; simp only [AddEquiv.apply_symm_apply]
    rw [heq]
    exact integrable_restrict_of_bdd _ _ hvol _ ((hG p).cont.comp ((OrthDec.continuous_resS_symm _ _).comp
      (Continuous.prodMk continuous_const hκ))) C (fun w => hC _)
  have hcom : ∀ p v, oma p (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0 = ∫ w in vL.𝓕, Ξ₂ ((B'.o.resT J.W₀).symm (v, w)) *
      oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, l.κ J.W₀ w))) 0 ∂vL.μ := fun p v =>
    (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ B.V₀ B.A B.L J.W₀ B.o χA s₁.χW oma hoa Ξ₁ hΞ₁ _ (vL.μ.restrict vL.𝓕) (l.κ J.W₀) _ hκm (ha v) p).2 0
  refine ⟨fun v => ?_, fun p => ⟨?_, hcom p⟩⟩
  · exact _root_.GlobalTheory.SuperposS.superpos_isTheta D ψ hstd B.V₀ B.A B.L J.W₀ B.o Ξ₁ hΞ₁ _ (vL.μ.restrict vL.𝓕) (l.κ J.W₀) _ hκm (ha v)
  · have h := _root_.GlobalTheory.SuperposT.superpos_target D ψ hstd B'.V₀ B'.A B'.L J.W₀ B'.o Ξ₂ hΞ₂ _ (vL.μ.restrict vL.𝓕) id _ measurable_id (hb p)
    have heq : (fun v => oma p (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0) = fun v =>
        ∫ w, oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, l.κ J.W₀ w))) 0 * Ξ₂ ((B'.o.resT J.W₀).symm (v, id w))
          ∂(vL.μ.restrict vL.𝓕) := by
      funext v; rw [hcom]; congr 1; funext w; rw [mul_comm]; rfl
    rw [heq]; exact h

end GlobalTheory.ContrTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateHalfPointNegMultipliesByCharacterStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateHalfPoint_neg_multiplies_by_character : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ → ∀ (n n'' : Type) [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (S₀ A L W₀ : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (β : Frame p W₀ n) (γ : Frame p A n'') (γ₀ : Frame p S₀ (n'' ⊕ Fin 1)), IsSumFrame o ζ γ γ₀ → ∀ t : n → k, IsHalf (cA D p.e) ((o.resT W₀).symm (0, -GlobalTheory.FinPl.LineAct.wCol p ζ β t)) ∧ ∀ x : WO W₀ S₀, IsHalf p.e x → ψ (symplO W₀ S₀ x ((o.resT W₀).symm (0, -GlobalTheory.FinPl.LineAct.wCol p ζ β t))) = (χ (-((fun j => rd β γ₀ x (Sum.inr 0) j) ⬝ᵥ t)) : ℂ) := by
  first | exact @GlobalTheory.FinPl.LineAct.ConjModul.conj_half_modul | exact GlobalTheory.FinPl.LineAct.ConjModul.conj_half_modul | (intros; apply GlobalTheory.FinPl.LineAct.ConjModul.conj_half_modul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqZeroOfOrthFock
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockTotal

theorem eq_zero_of_orth_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ vac, IsVacO ψ θ S T x.s y.s x.L y.L vac → ∀ (v : VolM D T.rank S.rank) f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T x.L y.L fun _ => True) f → (∀ P, thPair v.μ v.𝓕 f (pureTensorO ψ θ S T x.s y.s x.B y.B vac P) = 0) → f = 0 := by
  intro D ψ θ hθ S T x y hx hy vac hvac v f hf hlat horth
  have hne : vac ≠ 0 := by
    intro h0
    have h1 := hvac.2.norm.2 (v.μ, v.𝓕) v.covol
    simp [h0, nrm2] at h1
  exact _root_.GlobalTheory.ThetaIrred.eq_zero_of_orth_heis D ψ hvac.1 S T v f vac hf hvac.2.theta hne
    (_root_.GlobalTheory.FinOrth.orth_all D ψ θ hθ S T x y hx hy vac hvac v f hf hlat
      (GlobalTheory.T.orth_realHeisenbergTranslates_vacuum_of_orth_fock D ψ θ hθ S T x y hx hy vac hvac v f hf horth))

end GlobalTheory.FockTotal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSobolevBoundThetaPointwise
section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section

namespace GlobalTheory.ThetaDensSup

theorem sup_le_sobO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ (d : ℕ) (C : ℝ≥0), ∀ f ∈ thetaLevel ψ S T U, ∀ w, ‖f w‖ₑ ≤ C * sobO ψ θ μ 𝓕 d f := by
  intro D ψ hψ θ hθ S T μ 𝓕 hm U hU
  haveI : LocallyCompactSpace (WO S T) := (GlobalTheory.MixModel.lattice_Mx D T.rank S.rank).2.1
  obtain ⟨K₀, hK₀n, hK₀U, hK₀c⟩ := local_compact_nhds (hU.mem_nhds U.zero_mem)
  obtain ⟨C, hC⟩ := GlobalTheory.LevelSupBound.pointwise (S := S) (T := T) hψ hθ hK₀n hK₀c
  refine ⟨Module.finrank ℝ (GlobalTheory.FockCompare.RW T S), C, fun f hf w => ?_⟩
  have h := hC μ 𝓕 hm 1 one_pos f hf.1 (fun u hu hinf => by rw [one_smul]; exact hf.2 u (hK₀U hu) hinf) w
  refine h.trans (le_of_eq ?_)
  congr 1
  simp

end GlobalTheory.ThetaDensSup
end
end

