module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0255
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0017

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSeesawTensorMapPolynomialFockVector
section
noncomputable section

namespace GlobalTheory.Core.Rk.FockBox

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (resL resR)
open GlobalTheory.OrientedHeis

theorem killed_of_leibniz {P Q U V : Type} [Zero U] [AddCommGroup V] (a : P → U → U) (b : Q → V → V) (TU : U → Prop)
    (TV : V → Prop) (δ : U → U → V) (c₁ c₂ : Q → P) (ha : ∀ p f, TU f → TU (a p f)) (hb : ∀ q f, TV f → TV (b q f))
    (hadd : ∀ q f g, TV f → TV g → b q (f + g) = b q f + b q g) (hb0 : ∀ q, b q 0 = 0)
    (hδ : ∀ f g, TU f → TU g → TV (δ f g)) (h1 : ∀ g, δ 0 g = 0) (h2 : ∀ f, δ f 0 = 0)
    (hL : ∀ q f g, TU f → TU g → b q (δ f g) = δ (a (c₁ q) f) g + δ f (a (c₂ q) g)) (N : ℕ) :
    ∀ (N₁ N₂ : ℕ) (f g : U), N₁ + N₂ ≤ N → TU f → TU g →
      (∀ l : List P, l.length = N₁ → l.foldr a f = 0) → (∀ l : List P, l.length = N₂ → l.foldr a g = 0) →
      ∀ l : List Q, l.length = N → l.foldr b (δ f g) = 0 := by
  have w0 : ∀ l : List Q, l.foldr b 0 = 0 := fun l => by
    induction l with
    | nil => rfl
    | cons q l ih => rw [List.foldr_cons, ih, hb0]
  have wT : ∀ (l : List Q) f, TV f → TV (l.foldr b f) := fun l f hf => by
    induction l with
    | nil => exact hf
    | cons q l ih => exact hb _ _ ih
  have wadd : ∀ (l : List Q) f g, TV f → TV g → l.foldr b (f + g) = l.foldr b f + l.foldr b g := fun l f g hf hg => by
    induction l with
    | nil => rfl
    | cons q l ih => rw [List.foldr_cons, ih, hadd _ _ _ (wT l f hf) (wT l g hg)]; rfl
  have step : ∀ (M : ℕ) (f : U) (p : P), (∀ l : List P, l.length = M + 1 → l.foldr a f = 0) →
      ∀ l : List P, l.length = M → l.foldr a (a p f) = 0 := fun M f p h l hl => by
    have := h (l ++ [p]) (by simp [hl])
    rwa [List.foldr_append] at this
  induction N with
  | zero =>
    intro N₁ N₂ f g hN _ _ k₁ _ l _
    have : f = 0 := k₁ [] (by simp; omega)
    rw [this, h1, w0]
  | succ N ih =>
    intro N₁ N₂ f g hN hf hg k₁ k₂ l hl
    rcases N₁ with _ | M₁
    · have : f = 0 := k₁ [] rfl
      rw [this, h1, w0]
    rcases N₂ with _ | M₂
    · have : g = 0 := k₂ [] rfl
      rw [this, h2, w0]
    obtain rfl | ⟨l', q, rfl⟩ := l.eq_nil_or_concat'
    · simp at hl
    have hl' : l'.length = N := by simpa using hl
    rw [List.foldr_append, List.foldr_cons, List.foldr_nil, hL q f g hf hg,
      wadd _ _ _ (hδ _ _ (ha _ _ hf) hg) (hδ _ _ hf (ha _ _ hg)),
      ih M₁ (M₂ + 1) _ _ (by omega) (ha _ _ hf) hg (step _ _ _ k₁) k₂ l' hl',
      ih (M₁ + 1) M₂ _ _ (by omega) hf (ha _ _ hg) k₁ (step _ _ _ k₂) l' hl', add_zero]

variable {D : D7} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ}

theorem lineAt_neg (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) :
    lineAt θ τ (-z) = -lineAt θ τ z := by
  have hL := isLineAt_lineAt hθ τ z
  refine GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (isLineAt_lineAt hθ τ _) ⟨?_, fun t => ?_, fun t τ' => ?_⟩
  · have e : ⇑(-lineAt θ τ z) = fun t => lineAt θ τ z (-t) := by
      funext t; rw [AddMonoidHom.neg_apply, map_neg]
    rw [e]
    exact hL.1.comp continuous_neg
  · rw [AddMonoidHom.neg_apply, ← map_neg]
    exact hL.2.1 _
  · rw [AddMonoidHom.neg_apply, ← map_neg, hL.2.2]
    simp

theorem lineAt_col (hθ : IsInfFam θ) {m n k : ℕ} (c : Fin k → Fin n) (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ)
    (t : ℝ) : lineAt θ τ (z.submatrix id c) t = (lineAt θ τ z t).submatrix id c := by
  have hL := isLineAt_lineAt hθ τ z
  let L : ℝ →+ Mx D m k :=
    { toFun := fun t => (lineAt θ τ z t).submatrix id c
      map_zero' := by rw [map_zero]; rfl
      map_add' := fun s t => by rw [map_add (f := _)]; rfl }
  have hL' : IsLineAt θ τ (z.submatrix id c) L := by
    refine ⟨continuous_matrix fun i j => hL.1.matrix_elem i (c j), fun t => ?_, fun t τ' => ?_⟩
    · exact congrArg (fun x => Matrix.submatrix x id c) (hL.2.1 t)
    · refine (congrArg (fun x => Matrix.submatrix x id c) (hL.2.2 t τ')).trans ?_
      split_ifs <;> rfl
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (isLineAt_lineAt hθ τ _) hL']
  rfl

section One

variable {S T : HSp D}

theorem hasDerivAt_dRho (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (w : WO S T) :
    HasDerivAt (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) f w) (dRho (heisO ψ S T) θ τ z f w) 0 :=
  (hasDerivAt_heisO hθ hψ (isRealDir_lineAt hθ τ z) hf w 0).differentiableAt.hasDerivAt

theorem dRho_add (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    dRho (heisO ψ S T) θ τ z (f + g) = dRho (heisO ψ S T) θ τ z f + dRho (heisO ψ S T) θ τ z g := by
  funext w
  have := (hasDerivAt_dRho hθ hψ τ z hf w).add (hasDerivAt_dRho hθ hψ τ z hg w)
  refine Eq.trans ?_ this.deriv
  unfold Formalism.IndefR.Datum.dRho
  congr 1
  funext t
  simp only [heisO, Pi.add_apply, mul_add]

theorem dRho_neg (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) :
    dRho (heisO ψ S T) θ τ (-z) f = -dRho (heisO ψ S T) θ τ z f := by
  funext w
  have := deriv_comp_neg (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) f w) 0
  rw [neg_zero] at this
  refine Eq.trans ?_ this
  unfold Formalism.IndefR.Datum.dRho
  simp only [lineAt_neg hθ, AddMonoidHom.neg_apply, map_neg]

end One

variable {A B : HSp D}

theorem symplOH_dbl (x y : WO (dblSp A) B) : symplOH (dblSp A) B x y =
    symplOH A B (resL A B x) (resL A B y) - symplOH A B (-resR A B x) (-resR A B y) := by
  have hu : IsUnit A.gram.det := (isHermND_gram A).2.isUnit
  have hi : (dblSp A).gram⁻¹ = blkMat finSumFinEquiv A.gram⁻¹ (-A.gram⁻¹) := Matrix.inv_eq_right_inv (by
    rw [gram_hdbl, dblGram, blkMat_mul, neg_mul_neg, Matrix.mul_nonsing_inv _ hu, blkMat_one])
  have h : hO (dblSp A) B x y = hO A B (resL A B x) (resL A B y) - hO A B (-resR A B x) (-resR A B y) := by
    simp only [hO, hi, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, resL, resR, Matrix.of_apply,
      blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, map_zero,
      map_neg, zero_mul, Finset.sum_const_zero, add_zero, zero_add, neg_mul, mul_neg, neg_neg,
      Finset.sum_neg_distrib, sub_eq_add_neg]
  simp only [symplOH, symplO, h, mul_sub, map_sub]

theorem heisO_delta (hψ : IsStdChar D ψ (-1)) (u : WO (dblSp A) B) (f₁ f₂ : WO A B → ℂ) :
    heisO ψ (dblSp A) B u (delta A B f₁ f₂) =
      delta A B (heisO ψ A B (resL A B u) f₁) (heisO ψ A B (-resR A B u) f₂) := by
  funext x
  have e₁ : resL A B (x + u) = resL A B x + resL A B u := rfl
  have e₂ : -resR A B (x + u) = -resR A B x + -resR A B u := by
    rw [← neg_add]; rfl
  have e₃ : ∀ a, ψ (-a) = conj (ψ a) := fun a => by
    rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.1.2.1 a)]
  simp only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta, symplOH_dbl, e₁, e₂, sub_eq_add_neg, AddChar.map_add_eq_mul, e₃, map_mul]
  ring

abbrev colL (A : HSp D) : Fin A.rank → Fin (dblSp A).rank := fun j => finSumFinEquiv (Sum.inl j)

abbrev colR (A : HSp D) : Fin A.rank → Fin (dblSp A).rank := fun j => finSumFinEquiv (Sum.inr j)

theorem dRho_delta (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (z : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ) {f₁ f₂ : WO A B → ℂ} (h₁ : IsThetaFunO ψ A B f₁)
    (h₂ : IsThetaFunO ψ A B f₂) :
    dRho (heisO ψ (dblSp A) B) θ τ z (delta A B f₁ f₂) =
      delta A B (dRho (heisO ψ A B) θ τ (z.submatrix id (colL A)) f₁) f₂ +
        delta A B f₁ (dRho (heisO ψ A B) θ τ (-z.submatrix id (colR A)) f₂) := by
  funext x
  have d := (hasDerivAt_dRho hθ hψ τ (z.submatrix id (colL A)) h₁ (resL A B x)).mul
    (hasDerivAt_dRho hθ hψ τ (-z.submatrix id (colR A)) h₂ (-resR A B x)).star
  simp only [map_zero, heisO_zero] at d
  refine Eq.trans ?_ d.deriv
  unfold Formalism.IndefR.Datum.dRho
  congr 1
  funext t
  rw [heisO_delta hψ]
  simp only [Pi.mul_apply, lineAt_neg hθ, AddMonoidHom.neg_apply, lineAt_col hθ]
  rfl

theorem cplxO_colL (s : Matrix (Fin A.rank) (Fin A.rank) ℂ) (s' : Matrix (Fin B.rank) (Fin B.rank) ℂ)
    (z : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ) :
    (cplxO (n := (dblSp A).rank) ((Matrix.fromBlocks s 0 0 (-s)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) s' z).submatrix
      id (colL A) = cplxO s s' (z.submatrix id (colL A)) := by
  ext i j
  simp only [cplxO, Matrix.submatrix_apply, Matrix.smul_apply, id]
  congr 1
  rw [Matrix.mul_apply, Matrix.mul_apply]
  erw [← finSumFinEquiv.sum_comp]
  simp [Fintype.sum_sum_type, Matrix.mul_apply, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]

theorem cplxO_colR (s : Matrix (Fin A.rank) (Fin A.rank) ℂ) (s' : Matrix (Fin B.rank) (Fin B.rank) ℂ)
    (z : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ) :
    (cplxO (n := (dblSp A).rank) ((Matrix.fromBlocks s 0 0 (-s)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) s' z).submatrix
      id (colR A) = cplxO s s' (-z.submatrix id (colR A)) := by
  ext i j
  simp only [cplxO, Matrix.submatrix_apply, Matrix.smul_apply, id]
  congr 1
  rw [Matrix.mul_apply, Matrix.mul_apply]
  erw [← finSumFinEquiv.sum_comp]
  simp [Fintype.sum_sum_type, Matrix.mul_apply, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]

theorem annih_delta (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (s : Matrix (Fin A.rank) (Fin A.rank) ℂ) (s' : Matrix (Fin B.rank) (Fin B.rank) ℂ)
    (z : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ) {f₁ f₂ : WO A B → ℂ} (h₁ : IsThetaFunO ψ A B f₁)
    (h₂ : IsThetaFunO ψ A B f₂) :
    annih (heisO ψ (dblSp A) B) θ τ (cplxO (n := (dblSp A).rank)
        ((Matrix.fromBlocks s 0 0 (-s)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) s') z (delta A B f₁ f₂) =
      delta A B (annih (heisO ψ A B) θ τ (cplxO s s') (z.submatrix id (colL A)) f₁) f₂ +
        delta A B f₁ (annih (heisO ψ A B) θ τ (cplxO s s') (-z.submatrix id (colR A)) f₂) := by
  unfold annih
  rw [dRho_delta hθ hψ τ _ h₁ h₂, dRho_delta hθ hψ τ _ h₁ h₂, cplxO_colL, cplxO_colR, dRho_neg hθ τ (cplxO _ _ _)]
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, map_add (f := _), map_mul, map_neg, Complex.conj_I]
  ring

theorem isFockVec_delta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (sA : RealMat A) (sB : RealMat B), IsStdChar D ψ (-1) → IsInfFam θ → ∀ Φ₁ Φ₂, IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ → IsFockVec ψ θ (dblSp A) B (fun τ => (Matrix.fromBlocks (sA τ) 0 0 (-sA τ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) sB (delta A B Φ₁ Φ₂) := by
  intro D ψ θ A B sA sB hψ hθ Φ₁ Φ₂ ⟨t₁, N₁, k₁⟩ ⟨t₂, N₂, k₂⟩
  have hT : ∀ (S : HSp D) τ J z f, IsThetaFunO ψ S B f → IsThetaFunO ψ S B (annih (heisO ψ S B) θ τ J z f) :=
    fun S τ J z f hf => theta_add (theta_dRho hθ hψ τ z hf) (theta_smul _ (theta_dRho hθ hψ τ _ hf))
  refine ⟨_root_.GlobalTheory.Core.Rk.DeltaTheta.main D ψ A B hψ _ _ t₁ t₂, N₁ + N₂, ?_⟩
  refine killed_of_leibniz (P := D.what₂.Tau × Matrix (Fin B.rank) (Fin A.rank) ℂ)
    (Q := D.what₂.Tau × Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ)
    (fun p f => annih (heisO ψ A B) θ p.1 (cplxO (sA p.1) (sB p.1)) p.2 f)
    (fun p f => annih (heisO ψ (dblSp A) B) θ p.1 (cplxO (n := (dblSp A).rank)
      ((Matrix.fromBlocks (sA p.1) 0 0 (-sA p.1)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) (sB p.1)) p.2 f)
    (IsThetaFunO ψ A B) (IsThetaFunO ψ (dblSp A) B) (delta A B)
    (fun q => (q.1, q.2.submatrix id (colL A))) (fun q => (q.1, -q.2.submatrix id (colR A)))
    (fun p f hf => hT A _ _ _ f hf) (fun p f hf => hT _ _ _ _ f hf) (fun q f g hf hg => ?_) (fun q => ?_)
    (_root_.GlobalTheory.Core.Rk.DeltaTheta.main D ψ A B hψ) (fun g => ?_) (fun f => ?_) (fun q f g hf hg => annih_delta hθ hψ q.1 (sA q.1) (sB q.1) q.2 hf hg)
    _ N₁ N₂ Φ₁ Φ₂ le_rfl t₁ t₂ k₁ k₂
  · simp only [annih]
    rw [dRho_add hθ hψ _ _ hf hg, dRho_add hθ hψ _ _ hf hg, smul_add]
    abel
  · funext x
    simp [annih, Formalism.IndefR.Datum.dRho, heisO]
  · funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta]
  · funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta]

end GlobalTheory.Core.Rk.FockBox

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelLeviDetHomLeviMulUnipotent
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw

namespace GlobalTheory.Core.Rk.SWLaw

theorem aP_levi_mul_nC : ∀ (D : D7) (A : HSp D) (p : siegel A) (a : GL (Fin A.rank) (AE D)) (c : skewA D A.rank), (p : GA D (dblSp A)) = (dblDec A).levi a * (dblDec A).nC c → aP A p = Matrix.GeneralLinearGroup.det a := by
  intro D A p a c hp
  have hM : Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A)) ⬝ (dblDec A).jX = (dblDec A).jX ⬝ a.1 := by
    rw [hp, GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, HypDec.nC_jX, HypDec.levi_jX]
  apply Units.ext
  rw [GlobalTheory.Doubling.val_aOf]
  show (GlobalTheory.Doubling.leviMat finSumFinEquiv (Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A)))).det = a.1.det
  set M := Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A)) with hMdef
  have key : GlobalTheory.Doubling.leviMat finSumFinEquiv M * rat A.gram⁻¹ = rat A.gram⁻¹ * a.1 := by
    ext i j
    have h := congrFun (congrFun hM (finSumFinEquiv (Sum.inl i))) j
    simp only [HypDec.jX, dblDec, rat, stackRows, Matrix.mul_apply, Matrix.map_apply, Matrix.submatrix_apply,
      Fin.sum_univ_add, finSumFinEquiv_apply_left, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, id] at h
    simp only [GlobalTheory.Doubling.leviMat, rat, Matrix.mul_apply, Matrix.add_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.of_apply, Matrix.submatrix_apply, Matrix.map_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      add_mul, Finset.sum_add_distrib]
    exact h
  have hu : IsUnit (rat (D := D) A.gram⁻¹).det := by
    rw [rat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (Matrix.isUnit_nonsing_inv_det _ (gram_det_ne A).isUnit).map _
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm] at hd
  exact hu.mul_left_cancel hd

end GlobalTheory.Core.Rk.SWLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualDirectionDerivativeMixedCoordinateBound
section
namespace I195MixedCoordinates_e50a010289c1774166bfaddf

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_e50a010289c1774166bfaddf

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section

namespace GlobalTheory.Unf

theorem gram_posSp_one (D : D7) (n : ℕ) : (GlobalTheory.Size.posSp D n).gram = 1 := by
  funext i j
  refine (Examples₂.stdSpace_gram_apply (E := D.host.E) Examples₂.star_isIntegral n (fun _ => false) n 0 i j).trans ?_
  change (if i = j then (Examples₂.sgn false : D.host.E) else 0) = if i = j then 1 else 0
  by_cases h : i = j <;> simp [h, Examples₂.sgn]

theorem giA_posSp (D : D7) (n : ℕ) : giA (GlobalTheory.Size.posSp D n) = 1 := by
  rw [giA, gram_posSp_one, inv_one]
  unfold rat
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem hO_posSp (D : D7) (T : HSp D) (ρ : ℕ) (x y : Mx D T.rank ρ) :
    hO (GlobalTheory.Size.posSp D ρ) T x y = pairS T x y := by
  refine (hO_eq_trace (GlobalTheory.Size.posSp D ρ) T x y).trans ?_
  have h1 := giA_posSp D ρ
  unfold pairS
  erw [h1, Matrix.one_mul]
  rfl

theorem symplO_eq_two_half {D : D7} (S T : HSp D) (x y : WO S T) :
    symplO S T x y = symplOH S T x y + symplOH S T x y := by
  unfold symplOH
  rw [← add_mul, ← map_add (f := _)]
  norm_num

theorem symplAt_posSp (D : D7) (T : HSp D) (ρ : ℕ) (τ : D.what₂.Tau) (z X : Matrix (Fin T.rank) (Fin ρ) ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D ρ) T τ z X = 2 * (tauE D τ D.host.xi0 * (Xᴴ * gramAt D T τ * z).trace).re := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.hermAt
  have hg : (gramAt D (GlobalTheory.Size.posSp D ρ) τ)⁻¹ = 1 := by rw [GlobalTheory.Size.gramAt_posSp, inv_one]
  simp only [hg, Matrix.one_mul]
  rfl

end GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem norm_mixS_dRho_ge : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin ρ) ℂ), ∃ Z : Matrix (Fin T.rank) (Fin S.rank) ℂ, ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ x w, |2 * (tauE D τ D.host.xi0 * ((compAt θ τ x)ᴴ * gramAt D T τ * z).trace).re| * ‖d.mixS T ψ v.μ v.𝓕 f x w‖ ≤ ‖d.mixS T ψ v.μ v.𝓕 (dRho (heisO ψ S T) θ τ Z f) x w‖ := by
  intro D ψ hψ θ hθ S S₀ T ρ d v τ z
  refine ⟨z * compAt θ τ d.pY, ?_⟩
  intro f hf x w
  have hL := GlobalTheory.OrientedHeis.isLineAt_lineAt (m := T.rank) (n := ρ) hθ τ z
  have hL' : IsLineAt θ τ (z * compAt θ τ d.pY) ((d.extY T).comp (lineAt θ τ z)) := by
    refine ⟨?_, fun t => ?_, fun t τ' => ?_⟩
    · exact hL.1.matrix_mul continuous_const
    · show ((lineAt θ τ z t) * d.pY).map (finPart D) = 0
      rw [Matrix.map_mul, hL.2.1 t, Matrix.zero_mul]
    · show compAt θ τ' ((lineAt θ τ z t) * d.pY) = _
      rw [GlobalTheory.OrientedHeis.compAt_mul, hL.2.2 t τ']
      split_ifs with h
      · subst h
        rw [Matrix.smul_mul]
      · rw [Matrix.zero_mul]
  have hline := GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ hL' (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ _)
  have hline' : ∀ t, d.extY T (lineAt θ τ z t) = lineAt θ τ (z * compAt θ τ d.pY) t := fun t => by
    rw [← hline]; rfl
  have hder := _root_.GlobalTheory.Unf.hasDerivAt_mixS_extY D ψ hψ θ hθ S S₀ T ρ d v f hf (lineAt θ τ z) hL.1 hL.2.1 x w
  have hfun : (fun p => deriv (fun t : ℝ => heisO ψ S T (d.extY T (lineAt θ τ z t)) f p) 0) =
      dRho (heisO ψ S T) θ τ (z * compAt θ τ d.pY) f := by
    funext p
    simp only [hline']
    rfl
  rw [hfun] at hder
  have hphase : ∀ t : ℝ, ψ (symplO S T (d.extX T x) (d.extY T (lineAt θ τ z t))) =
      Complex.exp ((2 * Real.pi * Complex.I *
        (GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D ρ) T τ z (compAt θ τ x) : ℂ)) * t) := by
    intro t
    have e := GlobalTheory.ThetaDecay.psi_symplOH_lineAt hψ hθ (GlobalTheory.Size.posSp D ρ) T x τ z t
    have e2 : symplOH S T (d.extX T x) (d.extY T (lineAt θ τ z t)) =
        symplOH (GlobalTheory.Size.posSp D ρ) T x (lineAt θ τ z t) := by
      rw [d.symplOH_extX_extY]
      exact (congrArg (trHalf D) (hO_posSp D T ρ x _)).symm
    have e3 : ψ (symplOH S T (d.extX T x) (d.extY T (lineAt θ τ z t))) =
        Complex.exp ((Real.pi * Complex.I) *
          ((t * GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D ρ) T τ z (compAt θ τ x) : ℝ) : ℂ)) := by
      rw [e2]; exact e
    rw [symplO_eq_two_half, AddChar.map_add_eq_mul, e3, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hfun2 : (fun t : ℝ => ψ (symplO S T (d.extX T x) (d.extY T (lineAt θ τ z t))) * (_root_.I195MixedCoordinates_e50a010289c1774166bfaddf.source d) T ψ v.μ v.𝓕 f x w) =
      fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I *
        (GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D ρ) T τ z (compAt θ τ x) : ℂ)) * t) * (_root_.I195MixedCoordinates_e50a010289c1774166bfaddf.source d) T ψ v.μ v.𝓕 f x w :=
    funext fun t => by rw [hphase]
  rw [hfun2] at hder
  set a : ℝ := GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D ρ) T τ z (compAt θ τ x) with ha_def
  set M := (_root_.I195MixedCoordinates_e50a010289c1774166bfaddf.source d) T ψ v.μ v.𝓕 f x w with hM
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I * (a : ℂ)) * t) * M)
      ((2 * Real.pi * Complex.I * (a : ℂ)) * M) 0 := by
    have h2 : HasDerivAt (fun u : ℂ => Complex.exp ((2 * Real.pi * Complex.I * (a : ℂ)) * u) * M)
        (Complex.exp ((2 * Real.pi * Complex.I * (a : ℂ)) * ((0:ℝ):ℂ)) * ((2 * Real.pi * Complex.I * (a : ℂ)) * 1) * M)
        ((0:ℝ):ℂ) :=
      (((hasDerivAt_id _).const_mul (2 * Real.pi * Complex.I * (a : ℂ))).cexp).mul_const M
    have h3 := h2.comp_ofReal
    refine h3.congr_deriv ?_
    simp
  have heq := hder.unique hexp
  change d.mixS T ψ v.μ v.𝓕 (dRho (heisO ψ S T) θ τ (z * compAt θ τ d.pY) f) x w = _ at heq
  rw [heq]
  have ha : 2 * (tauE D τ D.host.xi0 * ((compAt θ τ x)ᴴ * gramAt D T τ * z).trace).re = a := by
    rw [ha_def]
    exact (symplAt_posSp D T ρ τ z (compAt θ τ x)).symm
  rw [ha, norm_mul]
  have hn : ‖2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)‖ = 2 * Real.pi * |a| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    ring
  rw [hn]
  change M = d.mixS T ψ v.μ v.𝓕 f x w at hM
  rw [← hM]
  have h1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have h0 : 0 ≤ |a| * ‖M‖ := by positivity
  nlinarith

end GlobalTheory.Unf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthDec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OrthSumExists

def orthDecHsum (D : D7) (A L : HSp D) : OrthDec (GlobalTheory.Doubling.hsum A L) A L where
  iA := (Matrix.fromRows (1 : Matrix (Fin A.rank) (Fin A.rank) D.host.E) (0 : Matrix (Fin L.rank) (Fin A.rank) D.host.E)).submatrix finSumFinEquiv.symm id
  iB := (Matrix.fromRows (0 : Matrix (Fin A.rank) (Fin L.rank) D.host.E) (1 : Matrix (Fin L.rank) (Fin L.rank) D.host.E)).submatrix finSumFinEquiv.symm id
  isoA := by
    rw [GlobalTheory.Doubling.gram_hsum, GlobalTheory.Doubling.blkMat, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
    simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]
  isoB := by
    rw [GlobalTheory.Doubling.gram_hsum, GlobalTheory.Doubling.blkMat, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
    simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]
  orth := by
    rw [GlobalTheory.Doubling.gram_hsum, GlobalTheory.Doubling.blkMat, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
    simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]
  rank_add := rfl

theorem exists_orthDec (D : D7) (A L : HSp D) : Nonempty (Σ V₀ : HSp D, OrthDec V₀ A L) :=
  ⟨⟨GlobalTheory.Doubling.hsum A L, orthDecHsum D A L⟩⟩

end GlobalTheory.OrthSumExists
end

