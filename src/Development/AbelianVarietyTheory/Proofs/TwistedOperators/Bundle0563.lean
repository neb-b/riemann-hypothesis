module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0561
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0447
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatMapSupportProof
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParameterSubgroupTransposeGramRealPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.LineAtPlace

variable {D : D7}

theorem emb_eq_or_conj (e₁ e₂ : D.host.E →+* ℂ)
    (h : ∀ a : D.host.F, e₁ (algebraMap D.host.F D.host.E a) = e₂ (algebraMap D.host.F D.host.E a)) :
    (∀ x, e₂ x = e₁ x) ∨ ∀ x, e₂ x = starRingEnd ℂ (e₁ x) := by
  have hconj : ∀ a : D.host.E, e₁ (star a) = starRingEnd ℂ (e₁ a) := D.sp.cm.cmUnram.2.1 e₁
  have hb := Eqv.star_alphaE D
  have hdec : ∀ y : D.host.E, ∃ p q : D.host.F,
      y = algebraMap D.host.F D.host.E p + algebraMap D.host.F D.host.E q * Eqv.alphaE D := by
    intro y
    refine ⟨(Eqv.basE D).repr y 0, (Eqv.basE D).repr y 1, ?_⟩
    conv_lhs => rw [← (Eqv.basE D).sum_repr y]
    rw [Fin.sum_univ_two, Eqv.basE_zero, Eqv.basE_one, Algebra.smul_def, Algebra.smul_def, mul_one]
  have hb2 : e₂ (Eqv.alphaE D) ^ 2 = e₁ (Eqv.alphaE D) ^ 2 := by
    have h1 : star (Eqv.alphaE D ^ 2) = Eqv.alphaE D ^ 2 := by rw [star_pow, hb]; ring
    obtain ⟨t, ht⟩ := (D.sp.cm.fixed _).1 h1
    rw [← map_pow, ← map_pow, ← ht, h]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hb2 with hc | hc
  · left
    intro y
    obtain ⟨p, q, rfl⟩ := hdec y
    rw [map_add (f := _), map_add (f := _), map_mul, map_mul, hc, h, h]
  · right
    intro y
    obtain ⟨p, q, rfl⟩ := hdec y
    rw [← hconj, star_add, star_mul, Eqv.star_algebraMapF, Eqv.star_algebraMapF, hb, map_add (f := _), map_add (f := _), map_mul, map_mul,
      map_neg, hc, h, h]
    ring

theorem exists_piInf (τ : D.what₂.Tau) (p : GlobalTheory.AdelicU.EmbOver D.host.E (Eqv.plW D τ)) :
    ∃ c : ℂ →+* ℂ, Continuous c ∧ (∀ (t : ℝ) z, c (t • z) = t • c z) ∧
      ∀ y : AE D, Eqv.psiT D τ y = c (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf p y) := by
  have key : ∀ c : ℂ →+* ℂ, (∀ t : ℝ, c t = t) → (∀ x, tauE D τ x = c (p.1 x)) →
      ∀ y : AE D, Eqv.psiT D τ y = c (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf p y) := by
    intro c hc hx y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]
    | tmul a x =>
      have l1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf p (a ⊗ₜ[D.host.F] x) = Eqv.gW D (Eqv.plW D τ) (fstA D.host.F a) * p.1 x :=
        GlobalTheory.AdelicU.infEmb_tmul p _ x
      have l2 : Eqv.psiT D τ (a ⊗ₜ[D.host.F] x) = Eqv.gW D (Eqv.plW D τ) (fstA D.host.F a) * tauE D τ x :=
        Eqv.thetaC_tmul D τ _ x
      rw [l1, l2, map_mul, hx, Eqv.gW_real, hc]
  rcases emb_eq_or_conj p.1 (tauE D τ) (fun a => RingHom.congr_fun (p.2.trans (Eqv.plW_embedding D τ)) a) with h | h
  · exact ⟨RingHom.id ℂ, continuous_id, fun _ _ => rfl, key _ (fun _ => rfl) h⟩
  · exact ⟨starRingEnd ℂ, Complex.continuous_conj, fun t z => by simp, key _ Complex.conj_ofReal h⟩

theorem kapX_surj (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (k : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) : ∃ h, kapX X e hJ h = k := by
  subst hJ
  have h1 : (k.1.1)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D.host.xi0 • reindex e e X.gramᵀ) * (k.1.1).map (cA D) =
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D.host.xi0 • reindex e e X.gramᵀ) := k.2
  rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul] at h1
  have hx : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have h2 := congrArg (fun Y => ((incA D D.host.xi0⁻¹ • Y)ᵀ).submatrix e e) h1
  simp only [smul_smul, ← map_mul, inv_mul_cancel₀ hx, map_one, one_smul, transpose_mul,
    transpose_transpose, ← Matrix.mul_assoc] at h2
  rw [← submatrix_mul_equiv _ _ _ e, ← submatrix_mul_equiv _ _ _ e] at h2
  have e1 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (reindex e e X.gramᵀ))ᵀ.submatrix e e = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram := by
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  rw [e1] at h2
  refine ⟨⟨Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom k.1, h2⟩, Subtype.ext (Units.ext ?_)⟩
  show reindex e e (reindex e.symm e.symm k.1.1) = k.1.1
  simp


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem lie_of_exp {n : ℕ} (Y H : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ t : ℝ, (NormedSpace.exp (t • Y))ᴴ * H * NormedSpace.exp (t • Y) = H) : Yᴴ * H + H * Y = 0 := by
  have h1 := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) Yᴴ (0 : ℝ)).mul_const H).fun_mul
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ))
  have h2 : (fun t : ℝ => NormedSpace.exp (t • Yᴴ) * H * NormedSpace.exp (t • Y)) = fun _ => H := by
    funext t
    have e : t • Yᴴ = (t • Y)ᴴ := by rw [Matrix.conjTranspose_smul, star_trivial]
    rw [e, Matrix.exp_conjTranspose]
    exact h t
  have h3 := (h1.congr_of_eventuallyEq (f₁ := fun _ => H)
    (Filter.Eventually.of_forall fun t => (congrFun h2 t).symm)).unique (hasDerivAt_const _ _)
  simpa using h3


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem exp_map {n d : ℕ} (e : Fin n ≃ Fin d) (c : ℂ →+* ℂ) (hc : Continuous c) (Z : Matrix (Fin d) (Fin d) ℂ) :
    ((NormedSpace.exp Z).map c).submatrix e e = NormedSpace.exp ((Z.map c).submatrix e e) :=
  NormedSpace.map_exp ((Matrix.reindexAlgEquiv ℂ ℂ e.symm).toRingHom.comp c.mapMatrix)
    ((continuous_id.matrix_map hc).matrix_submatrix e e) Z

end GlobalTheory.LineAtPlace

open GlobalTheory.LineAtPlace in
theorem GlobalTheory.LineAtPlace.exists_oneP : ∀ (D : D7) (θ : InfFam D) (X : HSp D), IsInfFam θ → ∀ {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ)
    (emb : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w) (w : InfinitePlace D.host.F)
    (Z : Matrix (Fin d) (Fin d) ℂ) (γ : Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Wd.J),
    γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Wd →
    (∀ t : ℝ, (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (emb w)) =
      NormedSpace.exp (t • Z)) →
    (∀ (t : ℝ) (w' : InfinitePlace D.host.F), w' ≠ w →
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (emb w')) = 1) →
    ∃ (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ), Y ∈ lieAt X τ ∧
      ∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hJ (oneP θ X τ Y t) := by
  intro D θ X hθ d e Wd hJ emb w Z γ hγ hw ho
  obtain rfl := Eqv.eq_thetaC D hθ
  obtain ⟨τ, rfl⟩ : ∃ τ, Eqv.plW D τ = w := ⟨_, Eqv.plW_symm D w⟩
  choose h hh using fun t : ℝ => kapX_surj X e hJ (γ (Multiplicative.ofAdd t))
  have hm : ∀ t, Eqv.matA D X (h t) = (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).submatrix e e := by
    intro t
    rw [← hh t]
    show _ = (reindex e e (Eqv.matA D X (h t))).submatrix e e
    simp
  obtain ⟨c, hc, hcs, hp⟩ := exists_piInf τ (emb _)
  have h1 : ∀ t : ℝ, infMat D.sp.cm.sig X.gram (Eqv.thetaC D τ) (h t) =
      NormedSpace.exp (t • (Z.map c).submatrix e e) := by
    intro t
    have e1 : t • (Z.map c).submatrix e e = ((t • Z).map c).submatrix e e := by
      ext i j
      exact (hcs t _).symm
    rw [Eqv.infMat_thetaC, hm, e1, ← exp_map e c hc, ← hw]
    ext i j
    exact hp _
  have hu : ∀ t : ℝ, (NormedSpace.exp (t • (Z.map c).submatrix e e))ᴴ * gramAt D X τ *
      NormedSpace.exp (t • (Z.map c).submatrix e e) = gramAt D X τ := by
    intro t
    rw [← h1]
    exact Eqv.infMat_unitary' D X (h t) τ
  refine ⟨τ, (Z.map c).submatrix e e, lie_of_exp _ _ hu, fun t => ?_⟩
  rw [← hh t, oneP, Eqv.atTau_eq D X τ _ (hu t)]
  congr 1
  apply Eqv.matA_inj D X
  rw [Eqv.matA_atH]
  refine Eqv.matA_of_isAtTau D X ⟨(Eqv.mem_GinfC D X _).2 ?_, h1 t, fun ρ hρ => ?_⟩
  · ext i j
    have k1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t)) (e i) (e j) - (1 : Matrix _ _ (AE D)) (e i) (e j)) :=
      fun u hu => congrFun (congrFun (hγ.2 _ u hu) (e i)) (e j)
    have k2 := GlobalTheory.ConjInfExp.finPart_eq_one
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t)) (e i) (e j) - (1 : Matrix _ _ (AE D)) (e i) (e j) + 1)
      (by rwa [add_sub_cancel_right])
    rw [RingHom.map_add (f := _), RingHom.map_one, add_eq_right, RingHom.map_sub, sub_eq_zero] at k2
    rw [Matrix.map_apply, hm, submatrix_apply, k2]
    by_cases k : i = j
    · subst k; simp
    · simp [Matrix.one_apply_ne k, Matrix.one_apply_ne (e.injective.ne k)]
  · obtain ⟨c', -, -, hp'⟩ := exists_piInf ρ (emb _)
    have k1 : Eqv.plW D ρ ≠ Eqv.plW D τ := fun k => hρ (by rw [← Eqv.symm_plW D ρ, k, Eqv.symm_plW])
    rw [Eqv.infMat_thetaC, hm]
    ext i j
    have k2 := congrFun (congrFun (ho t _ k1) (e i)) (e j)
    rw [Matrix.map_apply] at k2
    rw [Matrix.map_apply, submatrix_apply, hp', k2]
    by_cases k : i = j
    · subst k; simp
    · simp [Matrix.one_apply_ne k, Matrix.one_apply_ne (e.injective.ne k)]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianThetaImagesAlgebraic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ThetaGaussAlg

variable {D : D7}

theorem fockF_one (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) {M X : HSp D} (A : Fr M) (B : Fr X)
    (f : WO M X → ℂ) : fockF ψ θ ε A B f 1 = f := by
  simp only [fockF, pureTensorO, pureTensorL]
  have h1 : (1 : MvPolynomial (FVar D X.rank M.rank) ℂ) = MvPolynomial.basisMonomials (FVar D X.rank M.rank) ℂ 0 := by
    rw [MvPolynomial.coe_basisMonomials]
    rfl
  rw [h1, Module.Basis.constr_basis]
  simp [opPow]

theorem det_gram_ne_zero (V : HSp D) : V.gram.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet

  have hb : ∀ i, V.hT (V.frame i) (∑ j, v j • V.frame j) = 0 := by
    intro i
    have hi : V.hT (V.frame i) (∑ j, v j • V.frame j) = (V.gram *ᵥ v) i := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul, Matrix.mulVec, dotProduct, Formalism.BasicNotions.HSpace.gram]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hi, hv]
    rfl
  have hy : (∑ j, v j • V.frame j) = 0 := by
    refine V.nondeg.2 _ fun x => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← V.frame.sum_repr x, map_sum V.hT, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun i _ => by rw [map_smulₛₗ, LinearMap.smul_apply, hb, smul_zero]
  exact hv0 (funext (Fintype.linearIndependent_iff.mp V.frame.linearIndependent v hy))

theorem incM_gram_inv (S : HSp D) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram⁻¹ = 1 ∧
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram = 1 := by
  have hu : IsUnit S.gram.det := isUnit_iff_ne_zero.mpr (det_gram_ne_zero S)
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  constructor
  · rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]

def crd (S X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) : Matrix (Fin S.rank) (Fin k) (AE D) ≃+ WO S X where
  toFun u := (HMul.hMul (uᵀ.submatrix e.symm id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram) : Matrix (Fin X.rank) (Fin S.rank) (AE D))
  invFun x := GlobalTheory.TripleRead.ptO S.gram e x
  left_inv u := by
    simp only [GlobalTheory.TripleRead.ptO]
    rw [Matrix.mul_assoc, (incM_gram_inv S).1, Matrix.mul_one]
    ext i j
    simp
  right_inv x := by
    have : (GlobalTheory.TripleRead.ptO S.gram e x)ᵀ.submatrix e.symm id =
        (HMul.hMul x (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram⁻¹) : Matrix (Fin X.rank) (Fin S.rank) (AE D)) := by
      ext i j
      simp [GlobalTheory.TripleRead.ptO]
    simp only [this]
    rw [Matrix.mul_assoc, (incM_gram_inv S).2, Matrix.mul_one]
  map_add' u v := by
    rw [← Matrix.add_mul]
    rfl

end GlobalTheory.ThetaGaussAlg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfVectorSymplecticOrthogonal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.OrthOff

theorem orthOff : All fun {D} _ _ _ {G} _ _ => ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)), ∀ u ∈ latO S T LS LT (fun v => v ∉ G.pl.S0), ∀ y : WO S T, IsHalf e y → symplO S T u y = 0 := by
  intro D _ T L μ0 _ sc G W M _ e he S T' LS LT u hu y hy
  classical
  have hx : FinPl.MxAt (fun p => ∃ PP ∈ G.pl.W0, p = HeightOneSpectrum.under (𝓞 D.host.F) PP) (y.map (cA D)) :=
    GlobalTheory.PlaceModelComb.mxAt_of_idemSum he (Or.inr fun i j => by
      rw [Matrix.map_apply, ← map_mul, hy i j])
  have hu' := GlobalTheory.FinPl.LatMem.latO_mxAt hu
  have hoff : ∀ i j, u i j ∈ FinPl.idOff D (fun p => ∃ PP ∈ G.pl.W0, p = HeightOneSpectrum.under (𝓞 D.host.F) PP) := by
    intro i j
    rw [FinPl.idOff, Ideal.mem_iInf]
    rintro ⟨w, PP, hPP, rfl⟩
    have hin : HeightOneSpectrum.under (𝓞 D.host.F) PP ∈ G.pl.S0 := by
      unfold Places.W0 at hPP
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hPP
      rw [G.pl.under_w hv]
      exact hv
    have h := hu' i j
    rw [FinPl.idAt, Ideal.mem_inf, Ideal.mem_iInf] at h
    exact h.2 ⟨_, fun h' => h' hin⟩
  have hh : hO S T' u y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun d _ => ?_
    have h0 : cA D (y c b) * u d a = 0 :=
      GlobalTheory.FinPl.FlatUnitPf.idAt_mul_idOff _ _ _ (hx c b) (hoff d a)
    calc incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T'.gram c d) * u d a
        = incA D (S.gram⁻¹ a b) * incA D (T'.gram c d) * (cA D (y c b) * u d a) := by ring
      _ = 0 := by rw [h0, mul_zero]
  unfold symplO
  rw [hh, mul_zero, map_zero]

end GlobalTheory.OrthOff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulMemIdVOfLines
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc

variable {D : D7}

theorem pX_xLast_castSucc {W W₀ : HSp D} {σ : ℕ} (dW : HypDec W W₀ σ) (z : Fin W₀.rank → D.host.E) (k l : Fin σ) :
    (dW.pX ⬝ xLast dW z) k l.castSucc = (1 : Mx D σ σ) k l := by
  rw [← dW.pX_jX]
  simp only [Matrix.mul_apply, SuppShift.xLast_castSucc]

theorem pX_xLast_last {W W₀ : HSp D} {σ : ℕ} (dW : HypDec W W₀ σ) (z : Fin W₀.rank → D.host.E) (k : Fin σ) :
    (dW.pX ⬝ xLast dW z) k (Fin.last σ) = 0 := by
  have h : (dW.pX ⬝ xLast dW z) k (Fin.last σ) = ((dW.pX ⬝ dW.j0) *ᵥ ratV z) k := by
    rw [← Matrix.mulVec_mulVec]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, SuppShift.xLast_last]
  rw [h, dW.pX_j0, Matrix.zero_mulVec, Pi.zero_apply]

theorem pX_xLast_mul_apply {W W₀ : HSp D} {σ : ℕ} (dW : HypDec W W₀ σ) (z : Fin W₀.rank → D.host.E)
    (N : Mx D (σ + 1) (σ + 1)) (k : Fin σ) (j : Fin (σ + 1)) :
    (dW.pX ⬝ (xLast dW z ⬝ N)) k j = N k.castSucc j := by
  rw [← Matrix.mul_assoc, Matrix.mul_apply, Fin.sum_univ_castSucc, pX_xLast_last, zero_mul, add_zero]
  simp only [pX_xLast_castSucc, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end GlobalTheory.UniStepFB

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc

variable {D : D7}

theorem psiE_idem_entry {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V V₀ W W₀ : HSp D} {σ : ℕ}
    (dV : HypDec V V₀ (σ + 1)) (dW : HypDec W W₀ σ) (z : Fin W₀.rank → D.host.E) (LV : Lat V) (LW : Lat W) (LW₀ : Lat W₀)
    {v : Pl D} (hm : MonoAt dW LW LW₀ v) (hp : PrimAt ψ dV LV v) (hc : ColsAt dV (xLast dW z) LV LW v)
    (N : Mx D (σ + 1) (σ + 1))
    (hY : ∀ y ∈ latV V LV (· = v), (xLast dW z ⬝ N ⬝ dV.pX) *ᵥ y ∈ latA W LW (· = v))
    (i j : Fin (σ + 1)) (hij : j.1 = i.1 + 1) : psiE ψ (idem D (· = v) * N i j) = 1 := by
  obtain ⟨-, -, -, -, -, -, f7⟩ := _root_.GlobalTheory.SeeSaw.idV_props D ψ hψ v
  have hiσ : i.1 < σ := by have := j.2; omega
  set i' : Fin σ := ⟨i.1, hiσ⟩ with hi'
  have hii : i'.castSucc = i := Fin.ext rfl
  set s := idem D (· = v) * N i j with hsdef
  have hs : s ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ (idem_mem_idAt _)
  have key : ∀ a : AE D, colMul dV.jX j a ∈ latV V LV (· = v) → colMul dV.jX i (s * a) ∈ latV V LV (· = v) := by
    intro a ha
    have haA : a ∈ idAt D (· = v) := GlobalTheory.SeeSaw.PrimSplit.idAt_of_colMul dV ha
    have h1 := hY _ ha
    rw [PsiUnit.mulVec_colMul, Matrix.mul_assoc, dV.pX_jX, Matrix.mul_one] at h1
    have hb : N i j * a ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ haA
    have h2 : colMul (xLast dW z) i (N i j * a) ∈ latA W LW (· = v) := by
      refine (f7 W LW _).2 ⟨fun k => Ideal.mul_mem_right _ _ hb, fun t ht => ?_⟩
      have h3 := ((f7 W LW _).1 h1).2 t ht
      have h4 := ((hm _).1 h3).1 i'
      have e1 : (dW.pX *ᵥ (t • colMul (xLast dW z ⬝ N) j a)) i' = t * (a * N i j) := by
        rw [Matrix.mulVec_smul, PsiUnit.mulVec_colMul, Pi.smul_apply, smul_eq_mul, colMul,
          pX_xLast_mul_apply dW z N, hii]
      rw [e1] at h4
      convert h4 using 1
      ext k
      simp [colMul, ← hii, SuppShift.xLast_castSucc, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
    have h5 := (hc i (N i j * a) hb).2 h2
    have e2 : s * a = N i j * a := by
      rw [hsdef, mul_comm (idem D (· = v)), mul_assoc, (mem_idAt_iff _ a).1 haA]
    rwa [e2]
  have h6 := (hp i j hij s hs).1 key (idem D (· = v)) (idem_mem_intAt _)
  rwa [hsdef, mul_assoc, mul_comm (N i j), ← mul_assoc, idem_mul_self] at h6

end GlobalTheory.UniStepFB

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc

variable {D : D7}

theorem mul_mem_idV_of_lines {V V₀ W W₀ : HSp D} {σ : ℕ} (dV : HypDec V V₀ (σ + 1)) (dW : HypDec W W₀ σ)
    (z : Fin W₀.rank → D.host.E) (LV : Lat V) (A : AddSubgroup (Fin W.rank → AE D)) (𝔟V 𝔟W : GlobalTheory.SeeSaw.FI D) {v : Pl D}
    (k : Fin σ) (j : Fin (σ + 1)) (hV : ∀ a ∈ GlobalTheory.SeeSaw.idV 𝔟V v, colMul dV.jX j a ∈ latV V LV (· = v))
    (hW : ∀ y ∈ A, (dW.pX *ᵥ y) k ∈ GlobalTheory.SeeSaw.idV 𝔟W v) (N : Mx D (σ + 1) (σ + 1))
    (hY : ∀ y ∈ latV V LV (· = v), (xLast dW z ⬝ N ⬝ dV.pX) *ᵥ y ∈ A) :
    ∀ a ∈ GlobalTheory.SeeSaw.idV 𝔟V v, N k.castSucc j * a ∈ GlobalTheory.SeeSaw.idV 𝔟W v := by
  intro a ha
  have h1 := hY _ (hV a ha)
  rw [PsiUnit.mulVec_colMul, Matrix.mul_assoc, dV.pX_jX, Matrix.mul_one] at h1
  have h2 := hW _ h1
  rwa [PsiUnit.mulVec_colMul, colMul, pX_xLast_mul_apply dW z N k j, mul_comm] at h2

end GlobalTheory.UniStepFB

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc

variable {D : D7}

theorem span_neg (x : D.host.E) : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (-x) = FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ x :=
  (FractionalIdeal.spanSingleton_eq_spanSingleton).2 ⟨-1, by simp⟩

theorem line_ratio (I 𝔞 𝔞' : GlobalTheory.SeeSaw.FI D) (h𝔞 : 𝔞 ≠ 0) (h𝔞' : 𝔞' ≠ 0) (x : D.host.E) (hx : x ≠ 0) (n k : ℕ) :
    I * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (x ^ (k + 1)))⁻¹ * (𝔞 ^ n * (𝔞' ^ (k + 1))⁻¹) *
      ((FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (x ^ (k + 1 + 1)))⁻¹ * (𝔞 ^ n * (𝔞' ^ (k + 1 + 1))⁻¹))⁻¹ =
      I * FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ x * 𝔞' := by
  have hs : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ x ≠ 0 := by
    rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
  rw [pow_succ x (k + 1), ← FractionalIdeal.spanSingleton_mul_spanSingleton, pow_succ 𝔞' (k + 1)]
  have h1 : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (x ^ (k + 1)) ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact pow_ne_zero _ hx
  have h2 : 𝔞' ^ (k + 1) ≠ 0 := pow_ne_zero _ h𝔞'
  have h3 : 𝔞 ^ n ≠ 0 := pow_ne_zero _ h𝔞
  field_simp

end GlobalTheory.UniStepFB

namespace GlobalTheory.UniStepFB

variable {D : D7}

theorem line_ratio' (I 𝔞 𝔞' : GlobalTheory.SeeSaw.FI D) (h𝔞 : 𝔞 ≠ 0) (h𝔞' : 𝔞' ≠ 0) (x : D.host.E) (hx : x ≠ 0) (n k : ℕ) :
    FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ ((x ^ (k + 1))⁻¹) * (𝔞 ^ n * (𝔞' ^ (k + 1))⁻¹) * I *
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ ((x ^ (k + 1 + 1))⁻¹) * (𝔞 ^ n * (𝔞' ^ (k + 1 + 1))⁻¹))⁻¹ =
      I * FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ x * 𝔞' := by
  rw [← FractionalIdeal.spanSingleton_inv, ← FractionalIdeal.spanSingleton_inv]
  rw [← line_ratio I 𝔞 𝔞' h𝔞 h𝔞' x hx n k]
  ring

end GlobalTheory.UniStepFB
end
end

