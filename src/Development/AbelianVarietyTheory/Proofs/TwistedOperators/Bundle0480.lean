module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0429
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0473
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryAdelicDecompositionSplitSupport
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockFrameChangeLastColumnDefinitePair
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open GlobalTheory.FockReal MvPolynomial
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FockFrameChange

private theorem sum4_lemma {α β γ δ R : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [AddCommMonoid R]
    (f : α → β → γ → δ → R) :
    ∑ k, ∑ l, ∑ k', ∑ l', f k l k' l' = ∑ k', ∑ l', ∑ k, ∑ l, f k l k' l' := by
  calc ∑ k, ∑ l, ∑ k', ∑ l', f k l k' l' = ∑ k, ∑ k', ∑ l, ∑ l', f k l k' l' :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k', ∑ k, ∑ l, ∑ l', f k l k' l' := Finset.sum_comm
    _ = ∑ k', ∑ k, ∑ l', ∑ l, f k l k' l' :=
        Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k', ∑ l', ∑ k, ∑ l, f k l k' l' := Finset.sum_congr rfl fun k' _ => Finset.sum_comm

theorem substF_mul {ι : Type} {N n : ℕ} (h h' : ι → Matrix (Fin N) (Fin N) ℂ) (g g' : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    GlobalTheory.CompactHowe.substF h g (GlobalTheory.CompactHowe.substF h' g' P) =
      GlobalTheory.CompactHowe.substF (fun τ => h τ * h' τ) (fun τ => g τ * g' τ) P := by
  unfold GlobalTheory.CompactHowe.substF
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  refine congrArg (fun F => (MvPolynomial.aeval F) P) (funext fun p => ?_)
  obtain ⟨τ, a, b⟩ := p
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq, Matrix.mul_apply]
  simp only [Finset.sum_mul_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine (sum4_lemma _).trans ?_
  refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun l' _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem change_mul {n : ℕ} {A F : Matrix (Fin n) (Fin n) ℂ} (hA : A * A⁻¹ = 1) (hF : F * F⁻¹ = 1)
    (M : Matrix (Fin n) (Fin n) ℂ) : F⁻¹ * A * (A⁻¹ * M * A) = F⁻¹ * M * F * (F⁻¹ * A) := by
  calc F⁻¹ * A * (A⁻¹ * M * A) = F⁻¹ * (A * A⁻¹) * M * A := by simp only [Matrix.mul_assoc]
    _ = F⁻¹ * M * A := by rw [hA, Matrix.mul_one]
    _ = F⁻¹ * M * (F * F⁻¹) * A := by rw [hF, Matrix.mul_one]
    _ = F⁻¹ * M * F * (F⁻¹ * A) := by simp only [Matrix.mul_assoc]

theorem change_mul_invT {n : ℕ} {A F : Matrix (Fin n) (Fin n) ℂ} (hA : A * A⁻¹ = 1) (hF : F * F⁻¹ = 1)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    ((F⁻¹ * A)⁻¹).transpose * ((A⁻¹ * M * A)⁻¹).transpose = ((F⁻¹ * M * F)⁻¹).transpose * ((F⁻¹ * A)⁻¹).transpose := by
  rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, ← Matrix.mul_inv_rev (F⁻¹ * A) (A⁻¹ * M * A),
    ← Matrix.mul_inv_rev (F⁻¹ * M * F) (F⁻¹ * A), change_mul hA hF M]

theorem subst_change {ι : Type} {N n : ℕ} {A F : ι → Matrix (Fin N) (Fin N) ℂ} {A' F' : ι → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ τ, A τ * (A τ)⁻¹ = 1) (hF : ∀ τ, F τ * (F τ)⁻¹ = 1) (hA' : ∀ τ, A' τ * (A' τ)⁻¹ = 1)
    (hF' : ∀ τ, F' τ * (F' τ)⁻¹ = 1) (M : ι → Matrix (Fin N) (Fin N) ℂ) (M' : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    GlobalTheory.CompactHowe.substF (fun τ => ((F τ)⁻¹ * A τ).map (starRingEnd ℂ))
                 (fun τ => ((((F' τ)⁻¹ * A' τ)⁻¹).transpose).map (starRingEnd ℂ))
                 (GlobalTheory.CompactHowe.substF (fun τ => ((A τ)⁻¹ * M τ * A τ).map (starRingEnd ℂ))
                   (fun τ => ((((A' τ)⁻¹ * M' τ * A' τ)⁻¹).transpose).map (starRingEnd ℂ)) P) =
      GlobalTheory.CompactHowe.substF (fun τ => ((F τ)⁻¹ * M τ * F τ).map (starRingEnd ℂ))
        (fun τ => ((((F' τ)⁻¹ * M' τ * F' τ)⁻¹).transpose).map (starRingEnd ℂ))
        (GlobalTheory.CompactHowe.substF (fun τ => ((F τ)⁻¹ * A τ).map (starRingEnd ℂ))
          (fun τ => ((((F' τ)⁻¹ * A' τ)⁻¹).transpose).map (starRingEnd ℂ)) P) := by
  rw [substF_mul, substF_mul]
  exact congrArg₂ (fun h g => GlobalTheory.CompactHowe.substF h g P)
    (funext fun τ => by
      simp only [← Matrix.map_mul]
      rw [change_mul (hA τ) (hF τ)])
    (funext fun τ => by
      simp only [← Matrix.map_mul]
      rw [change_mul_invT (hA' τ) (hF' τ)])

theorem map_mul_inv {n : ℕ} {E : Type} [Field E] (φ : E →+* ℂ) (g : GL (Fin n) E) :
    g.1.map φ * (g.1.map φ)⁻¹ = 1 := by
  apply Matrix.mul_nonsing_inv
  have h := (Matrix.isUnits_det_units g).map φ
  rw [RingHom.map_det] at h
  exact h

private theorem fock_frame_lemma {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (BS A' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT A : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hBS : ∀ τ, BS τ * (BS τ)⁻¹ = 1) (hBT : ∀ τ, BT τ * (BT τ)⁻¹ = 1)
    (f : WO (GlobalTheory.ChiGrid.negSp S) T → ℂ) (hf : IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T f)
    (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) A' A f P =
      pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) BS BT f
        (GlobalTheory.CompactHowe.substF (fun τ => ((BT τ)⁻¹ * A τ).map (starRingEnd ℂ))
          (fun τ => ((((BS τ)⁻¹ * A' τ)⁻¹).transpose).map (starRingEnd ℂ)) P) := by
  have e1 : A' = fun τ => BS τ * ((BS τ)⁻¹ * A' τ) := by
    funext τ
    rw [← Matrix.mul_assoc, hBS τ, Matrix.one_mul]
  have e2 : A = fun τ => BT τ * ((BT τ)⁻¹ * A τ) := by
    funext τ
    rw [← Matrix.mul_assoc, hBT τ, Matrix.one_mul]
  conv_lhs => rw [e1, e2]
  exact GlobalTheory.FockNegSubst.pureTensorO_negSp_subst D ψ θ S T hψ hθ BS (fun τ => (BS τ)⁻¹ * A' τ) BT
    (fun τ => (BT τ)⁻¹ * A τ) f hf P

theorem exists_frame_change : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T},
    L.Is μ0 → ∀ (i : ℕ), i < D.R.m →
    ∃ σ₀ : PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank →ₗ[ℂ] PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank,
      (∀ t ∈ U, ∀ d : FinDatum G t (.chi i D.R.m), S.Z.HasVec d → ∀ P,
        W.fock (.chi i D.R.m) (S.Z.vec d) P = fockIn W S.N.frC (.chi i D.R.m) (S.Z.vec d) (σ₀ P)) ∧
      ∀ k : GA D (G.V (.grid i D.R.m)), k ∈ GinfC (G.V (.grid i D.R.m)) →
        ∀ k' : GA D (G.V (.grid (i + 1) D.R.m)), k' ∈ GinfC (G.V (.grid (i + 1) D.R.m)) → ∀ P,
          σ₀ (realSubst W W.onb (.chi i D.R.m) k k' P) = realSubst W S.N.frC (.chi i D.R.m) k k' (σ₀ P) := by
  intro D T L sc G W U S μ0 hL i hi
  have hdT : DefNode D.R.m (Node.grid i D.R.m) := by
    unfold DefNode
    exact ⟨hi.le, rfl⟩
  have hdS : DefNode D.R.m (Node.grid (i + 1) D.R.m) := by
    unfold DefNode
    exact ⟨hi, rfl⟩
  have hdP : DefPair D.R.m (Pair.chi i D.R.m : Pair T) := by
    unfold DefPair
    exact ⟨hi, rfl⟩
  have honb : ∀ X, DefNode D.R.m X → ∀ τ, W.onb X τ * (W.onb X τ)⁻¹ = 1 := fun X hX τ =>
    Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse (GlobalTheory.FockReal.onb_def hL W hX τ))
  have hfr : ∀ X τ, S.N.frC X τ * (S.N.frC X τ)⁻¹ = 1 := fun X τ => map_mul_inv (tauE D τ) (S.N.fr X)
  refine ⟨(GlobalTheory.CompactHowe.substF
      (fun τ => ((S.N.frC (Node.grid i D.R.m) τ)⁻¹ * W.onb (Node.grid i D.R.m) τ).map (starRingEnd ℂ))
      (fun τ => ((((S.N.frC (Node.grid (i + 1) D.R.m) τ)⁻¹ * W.onb (Node.grid (i + 1) D.R.m) τ)⁻¹).transpose).map
        (starRingEnd ℂ))).toLinearMap, ?_, ?_⟩
  · intro t _ d hd P
    have hf := (GlobalTheory.FockRealVec.vec_theta_fock W S.Z hdP d hd).1
    have hcS : G.cartS W.cart (Pair.chi i D.R.m : Pair T) = fun _ => -1 := by
      funext τ
      show -W.cart (Node.grid (i + 1) D.R.m) τ = -1
      rw [GlobalTheory.FockReal.cart_def hL W hdS τ]
    have hcT : G.onT W.cart (Pair.chi i D.R.m : Pair T) = fun _ => 1 := by
      funext τ
      exact GlobalTheory.FockReal.cart_def hL W hdT τ
    unfold GlobalTheory.ChiGrid.GridData.Weil.fock GlobalTheory.FunObj.fockIn
    rw [hcS, hcT, AlgHom.toLinearMap_apply]
    exact fock_frame_lemma W.ψ W.θ (G.V (Node.grid (i + 1) D.R.m)) (G.V (Node.grid i D.R.m)) W.ψ_std W.θ_is
      (S.N.frC (Node.grid (i + 1) D.R.m)) (W.onb (Node.grid (i + 1) D.R.m))
      (S.N.frC (Node.grid i D.R.m)) (W.onb (Node.grid i D.R.m))
      (hfr _) (hfr _) (S.Z.vec d) hf P
  · intro k _ k' _ P
    unfold GlobalTheory.FockReal.realSubst
    rw [AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply]
    exact subst_change (A := W.onb (Node.grid i D.R.m)) (F := S.N.frC (Node.grid i D.R.m))
      (A' := W.onb (Node.grid (i + 1) D.R.m)) (F' := S.N.frC (Node.grid (i + 1) D.R.m))
      (fun τ => honb _ hdT τ) (hfr _) (fun τ => honb _ hdS τ) (hfr _) _ _ P

end GlobalTheory.FockFrameChange

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPartialFourierColumnBlockSchwartzBruhat
section
namespace GlobalTheory.ColFourier
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
variable {A C : Type} [Fintype A] [DecidableEq C]

theorem fourierInt_add (ψ : AddChar k Circle) (m : Measure k) (hψ : HasConductor ψ 1) (hm : IsUnitVol m)
    (P : Finset C) {Ξ₁ Ξ₂ : Matrix A C k → ℂ} (h₁ : Ξ₁ ∈ SB (Matrix A C k)) (h₂ : Ξ₂ ∈ SB (Matrix A C k)) :
    fourierInt ψ m P (Ξ₁ + Ξ₂) = fourierInt ψ m P Ξ₁ + fourierInt ψ m P Ξ₂ := by
  haveI := hm.1
  haveI := secondCountable k
  haveI := isAddHaarMeasure_volM m (A := A) P
  haveI : BorelSpace (Matrix A P k) := inferInstanceAs (BorelSpace (A → P → k))
  have hi : ∀ Ξ ∈ SB (Matrix A C k), ∀ Y : Matrix A C k,
      Integrable (fun U => Ξ (setCols P Y U) * (ψ (pairCols P Y U) : ℂ)) (volM m A P) := by
    intro Ξ hΞ Y
    have hg := comp_setCols_mem_SB hΞ P Y
    have hc : Continuous fun U : Matrix A P k => pairCols P Y U := by unfold pairCols; fun_prop
    exact (hg.1.continuous.integrable_of_hasCompactSupport hg.2).mul_bdd (c := 1)
      ((continuous_subtype_val.comp (hψ.continuous.comp hc)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun U => (Circle.norm_coe _).le)
  funext Y
  simp only [fourierInt, Pi.add_apply, add_mul]
  exact integral_add (hi _ h₁ Y) (hi _ h₂ Y)

theorem fourierInt_shift [Fintype C] (ψ : AddChar k Circle) (m : Measure k) (hm : IsUnitVol m) (P : Finset C)
    (Ξ : Matrix A C k → ℂ) (T R : Matrix A C k) (hT : ∀ r, ∀ s ∉ P, T r s = 0) (hR : ∀ r, ∀ s ∈ P, R r s = 0) :
    fourierInt ψ m P (fun S => (ψ (GlobalTheory.FlipMatch.pairM S R) : ℂ) * Ξ (S + T)) =
      fun Z => (ψ (GlobalTheory.FlipMatch.pairM Z R - GlobalTheory.FlipMatch.pairM Z T) : ℂ) * fourierInt ψ m P Ξ Z := by
  haveI := hm.1
  haveI := isAddHaarMeasure_volM m (A := A) P
  haveI : MeasurableAdd (Matrix A P k) := inferInstanceAs (MeasurableAdd (A → P → k))
  funext Z
  unfold fourierInt
  set Tp := restrictCols P T
  rw [← integral_add_right_eq_self (μ := volM m A P)
    (fun U => Ξ (setCols P Z U) * (ψ (pairCols P Z U) : ℂ)) Tp, ← integral_const_mul]
  congr 1
  funext U
  have ea : GlobalTheory.FlipMatch.pairM (setCols P Z U) R = GlobalTheory.FlipMatch.pairM Z R := by
    simp only [GlobalTheory.FlipMatch.pairM]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j ∈ P
    · simp [setCols, h, hR i j h]
    · simp [setCols, h]
  have eb : setCols P Z U + T = setCols P Z (U + Tp) := by
    ext i j
    by_cases h : j ∈ P
    · simp [setCols, h, Tp, restrictCols]
    · simp [setCols, h, hT i j h]
  have ec : pairCols P Z (U + Tp) = pairCols P Z U + GlobalTheory.FlipMatch.pairM Z T := by
    simp only [pairCols, GlobalTheory.FlipMatch.pairM, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_subset (Finset.subset_univ P) (fun j _ hj => by simp [hT i j hj]),
      ← Finset.sum_coe_sort P, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Tp, restrictCols]
    ring
  have key : (ψ (GlobalTheory.FlipMatch.pairM Z R - GlobalTheory.FlipMatch.pairM Z T) : ℂ) *
      ψ (pairCols P Z U + GlobalTheory.FlipMatch.pairM Z T) = ψ (GlobalTheory.FlipMatch.pairM Z R) * ψ (pairCols P Z U) := by
    rw [← Circle.coe_mul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 2; ring
  dsimp only
  rw [ea, eb, ec]
  linear_combination (Ξ (setCols P Z (U + Tp))) * key.symm

end GlobalTheory.ColFourier

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

theorem GlobalTheory.ColFourier.exists_blockFourier : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A : Type) [Fintype A] [DecidableEq A] (C : Type) [Fintype C] [DecidableEq C] (ψ : AddChar k Circle) (ϖ : kˣ) (P : Finset C), IsUnif ϖ → HasConductor ψ 1 →
    ∃ 𝓕 : (Matrix A C k → ℂ) →ₗ[ℂ] (Matrix A C k → ℂ), Set.BijOn 𝓕 (GlobalTheory.WeilM.SB (Matrix A C k) : Set _) (GlobalTheory.WeilM.SB (Matrix A C k) : Set _) ∧
      (∀ Ξ ∈ GlobalTheory.WeilM.SB (Matrix A C k), ∀ T R : Matrix A C k, (∀ r, ∀ s ∈ P, T r s = 0) → (∀ r, ∀ s ∉ P, R r s = 0) →
        𝓕 (fun S => (ψ (pairM S R) : ℂ) * Ξ (S + T)) = fun Z => 𝓕 Ξ (Z + (T + R))) ∧
      (∀ Ξ ∈ GlobalTheory.WeilM.SB (Matrix A C k), ∀ T R : Matrix A C k, (∀ r, ∀ s ∉ P, T r s = 0) → (∀ r, ∀ s ∈ P, R r s = 0) →
        𝓕 (fun S => (ψ (pairM S R) : ℂ) * Ξ (S + T)) = fun Z => (ψ (pairM Z R - pairM Z T) : ℂ) * 𝓕 Ξ Z) ∧
      ∀ Ξ ∈ GlobalTheory.WeilM.SB (Matrix A C k), ∀ n, IsNatDatum ϖ n (𝓕 Ξ) → fourierSum ψ⁻¹ ϖ n P (𝓕 Ξ) = Ξ := by
  intro k _ _ _ _ A _ _ C _ _ ψ ϖ P hϖ hψ
  borelize k
  obtain ⟨m, hm⟩ := exists_isUnitVol k
  haveI := hm.1
  have hψ' : HasConductor ψ⁻¹ 1 := GlobalTheory.ColFourier.hasConductor_inv hψ
  have hSB := fun (χ : AddChar k Circle) (hχ : HasConductor χ 1) (Ξ : Matrix A C k → ℂ)
    (h : Ξ ∈ SB (Matrix A C k)) => _root_.GlobalTheory.ColFourier.fourierInt_mem_SB k A C χ m hχ hm P Ξ h
  have hInv := fun (χ : AddChar k Circle) (hχ : HasConductor χ 1) (Ξ : Matrix A C k → ℂ)
    (h : Ξ ∈ SB (Matrix A C k)) => _root_.GlobalTheory.ColFourier.fourierInt_inv_fourierInt k A C χ m hχ hm P Ξ h
  let L : SB (Matrix A C k) →ₗ[ℂ] (Matrix A C k → ℂ) :=
    { toFun := fun Ξ => fourierInt ψ m P Ξ
      map_add' := fun a b => GlobalTheory.ColFourier.fourierInt_add ψ m hψ hm P a.2 b.2
      map_smul' := fun c a => by
        funext Y
        simp only [SetLike.val_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, fourierInt]
        rw [← integral_const_mul]
        congr 1; funext U; ring }
  obtain ⟨F, hF⟩ := LinearMap.exists_extend L
  have hFe : ∀ Ξ ∈ SB (Matrix A C k), F Ξ = fourierInt ψ m P Ξ := fun Ξ h => LinearMap.congr_fun hF ⟨Ξ, h⟩
  have hmod : ∀ Ξ ∈ SB (Matrix A C k), ∀ T R : Matrix A C k,
      (fun S => (ψ (pairM S R) : ℂ) * Ξ (S + T)) ∈ SB (Matrix A C k) := by
    intro Ξ hΞ T R
    have hc : Continuous fun S : Matrix A C k => pairM S R := by unfold pairM; fun_prop
    refine ⟨((hψ.isLocallyConstant.comp_continuous hc).comp (fun z : Circle => (z : ℂ))).mul
      (hΞ.1.comp_continuous (continuous_add_const T)), ?_⟩
    exact (hΞ.2.comp_homeomorph (Homeomorph.addRight T)).mul_left
  refine ⟨F, ⟨fun Ξ h => ?_, fun Ξ₁ h₁ Ξ₂ h₂ he => ?_, fun Ψ hΨ => ?_⟩, fun Ξ hΞ T R hT hR => ?_,
    fun Ξ hΞ T R hT hR => ?_, fun Ξ hΞ n hn => ?_⟩
  · show F Ξ ∈ SB (Matrix A C k)
    rw [hFe Ξ h]; exact hSB ψ hψ Ξ h
  · rw [hFe _ h₁, hFe _ h₂] at he
    rw [← hInv ψ hψ Ξ₁ h₁, ← hInv ψ hψ Ξ₂ h₂, he]
  · have h1 := hSB ψ⁻¹ hψ' Ψ hΨ
    refine ⟨_, h1, ?_⟩
    rw [hFe _ h1]
    simpa only [inv_inv] using hInv ψ⁻¹ hψ' Ψ hΨ
  · rw [hFe _ (hmod Ξ hΞ T R), hFe _ hΞ]
    funext Z
    unfold fourierInt
    congr 1
    funext U
    have e1 : setCols P Z U + T = setCols P (Z + (T + R)) U := by
      ext i j
      by_cases h : j ∈ P
      · simp [setCols, h, hT i j h]
      · simp [setCols, h, hR i j h]
    have e2 : pairM (setCols P Z U) R + pairCols P Z U = pairCols P (Z + (T + R)) U := by
      simp only [pairM, pairCols, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_subset (Finset.subset_univ P) (fun j _ hj => by simp [setCols, hj, hR i j hj]),
        ← Finset.sum_coe_sort P, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [setCols, j.2, hT i j j.2]
      ring
    dsimp only
    rw [e1, ← e2, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  · rw [hFe _ (hmod Ξ hΞ T R), hFe _ hΞ]
    exact GlobalTheory.ColFourier.fourierInt_shift ψ m hm P Ξ T R hT hR
  · rw [hFe _ hΞ] at hn ⊢
    rw [← GlobalTheory.ColFourier.fourierInt_eq_fourierSum k A C ψ⁻¹ m ϖ hϖ hψ' hm P n _ hn]
    exact hInv ψ hψ Ξ hΞ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalSplitStabilizerDecomposition
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open Matrix

namespace GlobalTheory.RatSplitLat

theorem colLat_fg {K : Type} [Field K] [NumberField K] {n : ℕ} (B : GL (Fin n) K) : (colLat B).FG :=
  Submodule.fg_span (Set.finite_range _)

theorem colLat_span {K : Type} [Field K] [NumberField K] {n : ℕ} (B : GL (Fin n) K) :
    Submodule.span K ((colLat B : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K)) = ⊤ := by
  unfold colLat
  rw [Submodule.span_span_of_tower]
  rw [eq_top_iff]
  intro x _
  have hx : x = ∑ j, (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) j •
      (fun a : Fin n => (B : Matrix (Fin n) (Fin n) K) a j) := by
    funext a
    have := congrFun (show (B : Matrix (Fin n) (Fin n) K) *ᵥ (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) = x by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]) a
    conv_lhs => rw [← this]
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [hx]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem stab_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (H : AddSubgroup (Fin n → GlobalTheory.AdLat.RA F E)) (k : GL (Fin n) (GlobalTheory.AdLat.RA F E)) (N : ℕ)
    (h1 : ∀ z ∈ H, ∃ w ∈ H, k.1 *ᵥ z - z = N • w) (h2 : ∀ z ∈ H, (k⁻¹).1 *ᵥ z ∈ H) (y : Fin n → GlobalTheory.AdLat.RA F E) :
    y ∈ H ↔ k.1 *ᵥ y ∈ H := by
  constructor
  · intro hy
    obtain ⟨w, hw, e⟩ := h1 y hy
    rw [show k.1 *ᵥ y = (k.1 *ᵥ y - y) + y by abel, e]
    exact H.add_mem (H.nsmul_mem hw N) hy
  · intro hy
    have := h2 _ hy
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this


set_option maxHeartbeats 1000000 in
theorem exists_rat_split_lat : ∀ {D : D7} (V : HSp D) (B : GL (Fin V.rank) D.host.E) (N : ℕ), 0 < N → ∀ g : GfC V,
    ∃ r s k : GfC V, GlobalTheory.MovedKappaEx.RatFin V r ∧ GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N (finHom V s.1).1 ∧
      (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B) ↔
        Matrix.mulVec (Formalism.IndefR.Lev.finE V k.1).1 v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B)) ∧ g = r * s * k := by
  intro D V B N hN g
  obtain ⟨-, -, -, -, c2, -, c1, gh, gd, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨γ', h', k', u1, u2, u3, hg, hs, hk, hki⟩ := GlobalTheory.T.exists_unitary_adelic_decomposition_split_support D.host.F D.host.E (GlobalTheory.Member.cF D) V.rank V.gramᵀ
    ⟨c2, c1, gh, gd⟩ (GlobalTheory.UnRep.Space.finrank_two D) (colLat B) (colLat_fg B) (colLat_span B) (finHom V g.1) N
    (GlobalTheory.UnRep.Space.isUnA_finHom V g.1) hN
  obtain ⟨-, -, -, lift, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D V
  obtain ⟨r1, -, r3, -⟩ := GlobalTheory.Member.RatElt.rational_elements D V
  obtain ⟨h, hh, eh⟩ := lift h' u2
  obtain ⟨k, hk', ek⟩ := lift k' u3
  obtain ⟨γ, hγ⟩ := r3 γ' fun u v => by rw [GlobalTheory.UnRep.Space.herm_neg_eq, GlobalTheory.UnRep.Space.herm_neg_eq, u1]
  have eγ : (finHom V γ).1 = GlobalTheory.UnRep.fm D.host.F γ'.1 := GlobalTheory.Member.RatElt.fin_eq hγ
  have e : finHom V g.1 = finHom V γ * finHom V h * finHom V k := by
    apply Units.ext
    rw [hg, Units.val_mul, Units.val_mul, eγ, eh, ek]
  refine ⟨g * ⟨k, hk'⟩⁻¹ * ⟨h, hh⟩⁻¹, ⟨h, hh⟩, ⟨k, hk'⟩, ⟨γ, (r1 γ).2 ⟨γ', hγ⟩, ?_⟩, ?_, ?_, by rw [inv_mul_cancel_right, inv_mul_cancel_right]⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, map_mul, map_mul, map_inv, map_inv, e]
    rw [mul_inv_cancel_right, mul_inv_cancel_right]
  · change GlobalTheory.UnRep.SuppSplit _ N (finHom V h).1
    rw [eh]
    exact hs
  · intro v
    have key := GlobalTheory.StdFrames.hatL_of_hat (F := D.host.F) (colLat B) (colLat B) k'.1
      (stab_iff _ k' N hk hki) v
    have hm : (Formalism.IndefR.Lev.finE V k).1 =
        k'.1.map (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E) := by
      rw [← ek]; rfl
    refine key.trans (iff_of_eq ?_)
    exact congrArg (fun M => M *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B)) hm.symm

end GlobalTheory.RatSplitLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockComponentTransportedPointsEqJetOperator
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.AvgColJet

theorem fockIn_frC {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T} (hL : L.Is μ0)
    (W : G.Weil) {U : Set T} (N : Std G U) (t : T) (j : ℕ) (hj : j < D.R.m)
    (f : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ) (hf : IsThetaFunO W.ψ (G.pS (.top t j)) (G.pT (.top t j)) f)
    (Q : PolF D (G.pT (.top t j)).rank (G.pS (.top t j)).rank) :
    fockIn W N.frC (.top t j) f Q = W.fock (.top t j) f (AvgCol.frCh W N j Q) := by
  have hn : DefNode D.R.m (.top j) ∧ DefNode D.R.m (.top (j + 1)) :=
    ⟨show j ≤ D.R.m by omega, show j + 1 ≤ D.R.m by omega⟩
  have c1 : W.cart (.top j) = fun _ => 1 := funext (GlobalTheory.FockReal.cart_def hL W hn.1)
  have c2 : W.cart (.top (j + 1)) = fun _ => 1 := funext (GlobalTheory.FockReal.cart_def hL W hn.2)
  have e : ∀ X, DefNode D.R.m X → N.frC X = fun τ => W.onb X τ * AvgCol.frRel W N X τ := by
    intro X hX
    funext τ
    have hu : IsUnit (W.onb X τ).det := Matrix.isUnit_det_of_left_inverse (GlobalTheory.FockReal.onb_def hL W hX τ)
    rw [AvgCol.frRel, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  simp only [fockIn, GridData.Weil.fock, GridData.cartS, GridData.onT, GridData.onS, c1, c2, e _ hn.1, e _ hn.2]
  rw [GlobalTheory.FockBaseChange.pureTensorO_subst D W.ψ W.θ _ _ W.ψ_std W.θ_is _ _ _ _ f hf]
  rfl

theorem fockComp_frC_eq_jetOp : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j < D.R.m → ∀ (t : T) (d : FinDatum G t (.top t j)), S.Z.HasVec d →
    ∀ (x : FinPt G (.top j)) (y : FinPt G (.top (j + 1))),
      fockComp W S.N.frC (.top t j) (S.Z.vec d) (x * S.N.u _) (y * S.N.u _) =
        Formalism.L2.Ker.jetOp (wt G (.top j)) (wt G (.top (j + 1)))
          (fun m => W.ker (.top t j) (W.fock (.top t j) (movedVec t S d) (GlobalTheory.AvgCol.frCh W S.N j (MvPolynomial.monomial m 1)))
            (x : GA D (G.V (.top j))) (y : GA D (G.V (.top (j + 1)))))
          (nuEnd G (.top t j)) := by
  intro D T L sc G W U S μ0 hL j hj t d hd x y
  have hp : DefPair D.R.m (Pair.top t j : Pair T) := show j + 1 ≤ D.R.m by omega
  have hf := (GlobalTheory.FockRealVec.vec_theta_fock W S.Z hp d hd).1
  unfold fockComp
  refine congrArg (fun F => Formalism.L2.Ker.jetOp (wt G (.top j)) (wt G (.top (j + 1))) F (nuEnd G (.top t j))) (funext fun m => ?_)
  unfold jetTab kerFin
  have hid : m.mapDomain (fvar G (.top t j)) = m := Finsupp.mapDomain_id
  rw [hid, Subgroup.coe_mul, Subgroup.coe_mul, GlobalTheory.FockReal.ker_mul, fockIn_frC hL W S.N t j hj _ hf]
  congr 1
  exact GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ _ _ _ _ (W.om (.top t j)) (W.om_is (.top t j) (show j + 1 ≤ D.R.m by omega))
    W.θ W.θ_is _ (S.N.u _).2 _ (S.N.u _).2 _ _ _ _ _ _ hf

end GlobalTheory.AvgColJet
end
end

