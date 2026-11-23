module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KappaConjugateHalfPointTranslatesLastColumn
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LineAct.ColTrans

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem adelicConj_adelicConj_eq_self (x : AE D) : cA D (cA D x) = x := by
  have := congrFun (congrFun (adj_adj (D := D) (m := 1) (n := 1) (Matrix.of fun _ _ => x)) 0) 0
  simpa [adj] using this

theorem e_mul_sec (p : SplitPt D k) (x : k) : p.e * p.sec x = p.sec x := by
  rw [← p.sec_pr, p.pr_sec]

theorem map_pr_rat (p : SplitPt D k) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    (rat M : Mx D m n).map p.pr = M.map (iota p) := by
  ext i j; rfl

theorem matrix_mul_replicateCol_eq_replicateCol_mulVec {R : Type} [CommRing R] {m l : Type} [Fintype l] (A : Matrix m l R) (x : l → R) :
    A * replicateCol (Fin 1) x = replicateCol (Fin 1) (A *ᵥ x) := by
  ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

variable {n : Type} [Fintype n] [DecidableEq n]

theorem adj_wCol (p : SplitPt D k) {W₀ L' : HSp D} (ζ' : Fin L'.rank → D.host.E) (β : Frame p W₀ n) (t : n → k) :
    adj (wCol p ζ' β t) = Matrix.of fun i j => p.sec (dualPick ((L'.gram.map (iota p)) *ᵥ fun i => iota p (ζ' i)) j *
      ((iota p D.host.xi0)⁻¹ * ((W₀.gram.map (iota p)) *ᵥ (β.b *ᵥ t)) i)) := by
  ext i j
  simp only [adj, wCol, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, adelicConj_adelicConj_eq_self]

end GlobalTheory.FinPl.LineAct.ColTrans

namespace GlobalTheory.FinPl.LineAct
open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj)
open GlobalTheory.FinPl.LineAct.ColTrans


set_option maxHeartbeats 2000000 in
theorem kappa_wCol_translate : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (L' W₀ : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ'), IsLineVec L' ζ' → ∀ (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p W₀ n), IsSumFrame B.o B.ζ α α₀ → ∀ t : n → k, IsHalf p.e ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wCol p ζ' β t))) ∧ ∀ i j, rd α₀ β ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wCol p ζ' β t))) i j = Sum.elim (fun _ => 0) (fun _ => -t i) j := by
  intro D k _ _ _ _ p n n' _ _ _ _ ρ B L' W₀ ζ' l hL α α₀ β hsum t
  set ι := iota p with hι
  set g' : Fin L'.rank → k := (L'.gram.map ι) *ᵥ fun i => ι (ζ' i) with hg'
  set v : Fin W₀.rank → k := fun j => (ι D.host.xi0)⁻¹ * ((W₀.gram.map ι) *ᵥ (β.b *ᵥ t)) j with hv
  have hadj : adj (wCol p ζ' β t) = Matrix.of fun i j => p.sec (dualPick g' j * v i) := adj_wCol p ζ' β t
  have hu : (B.o.resS W₀).symm (0, l.κ W₀ (wCol p ζ' β t)) =
      (incA D (-D.host.xi0⁻¹) • giA W₀) ⬝ adj (wCol p ζ' β t) ⬝ (adj (rat l.τ) ⬝ gA B.L ⬝ B.o.pB) := by
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add, Link.κ, ofAdj, adj_mul]
    simp only [Matrix.smul_mul, Matrix.mul_assoc]
  rw [hu]
  constructor
  · have hA : p.e • adj (wCol p ζ' β t) = adj (wCol p ζ' β t) := by
      rw [hadj]; ext i j; simp [e_mul_sec]
    intro i j
    have : p.e • ((incA D (-D.host.xi0⁻¹) • giA W₀) ⬝ adj (wCol p ζ' β t) ⬝ (adj (rat l.τ) ⬝ gA B.L ⬝ B.o.pB)) =
        (incA D (-D.host.xi0⁻¹) • giA W₀) ⬝ adj (wCol p ζ' β t) ⬝ (adj (rat l.τ) ⬝ gA B.L ⬝ B.o.pB) := by
      conv_rhs => rw [← hA]
      rw [Matrix.mul_smul (incA D (-D.host.xi0⁻¹) • giA W₀) p.e (adj (wCol p ζ' β t)),
        Matrix.smul_mul p.e ((incA D (-D.host.xi0⁻¹) • giA W₀) ⬝ adj (wCol p ζ' β t))]
    exact congrFun (congrFun this i) j
  · generalize hUdef : (incA D (-D.host.xi0⁻¹) • giA W₀) ⬝ adj (wCol p ζ' β t) ⬝
        (adj (rat l.τ) ⬝ gA B.L ⬝ B.o.pB) = U
    replace hUdef := hUdef.symm
    have hR : adj (rat l.τ) ⬝ gA B.L ⬝ B.o.pB = rat (l.τᴴ * B.L.gram * B.o.qB) := by
      rw [← rat_conjTranspose, gA, OrthDec.pB, ← rat_mul, ← rat_mul]
    have hX : (incA D (-D.host.xi0⁻¹) • giA W₀ : Mx D W₀.rank W₀.rank).map p.pr =
        ι (-D.host.xi0⁻¹) • (W₀.gram⁻¹).map ι := by
      ext i j; simp [giA, rat, hι, iota]
    have hW : (adj (wCol p ζ' β t)).map p.pr = vecMulVec v (dualPick g') := by
      rw [hadj]; ext i j; simp [vecMulVec, p.pr_sec, mul_comm]
    have hUm : U.map p.pr = (ι (-D.host.xi0⁻¹) • (W₀.gram⁻¹).map ι) * vecMulVec v (dualPick g') *
        (l.τᴴ * B.L.gram * B.o.qB).map ι := by
      rw [hUdef, hR, Matrix.map_mul, Matrix.map_mul, hX, hW, map_pr_rat]
    have hUA : U ⬝ B.o.jA = 0 := by
      simp only [hUdef, Matrix.mul_assoc, OrthDec.pB_jA, Matrix.mul_zero]

    have hrat : (l.τᴴ * B.L.gram * B.o.qB) *ᵥ vecB B.o B.ζ =
        -((D.host.xi0 * star D.host.xi0) • (L'.gram *ᵥ ζ')) := by
      have hz : B.ζ = -(l.τ *ᵥ ζ') := by rw [l.map, neg_neg]
      rw [vecB, Matrix.mulVec_mulVec, Matrix.mul_assoc, B.o.qB_iB, Matrix.mul_one, hz, Matrix.mulVec_neg,
        Matrix.mulVec_mulVec, Matrix.mul_assoc, GlobalTheory.Unf.Model.tau_gram l hL, Matrix.smul_mulVec]
    have hgi : ∀ i, g' i = ι ((L'.gram *ᵥ ζ') i) := fun i => (RingHom.map_mulVec ι _ _ i).symm
    have hg0 : g' ≠ 0 := by
      intro h0
      apply hL.2
      have h1 : L'.gram *ᵥ ζ' = 0 := by
        funext i
        apply ι.injective
        rw [← hgi, h0, Pi.zero_apply, Pi.zero_apply, map_zero]
      rw [h1, dotProduct_zero]
    have hxi : ι D.host.xi0 ≠ 0 := fun h => GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D ((iota p).injective (h.trans (map_zero _).symm))
    have hGG : (W₀.gram⁻¹).map ι * W₀.gram.map ι = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (gram_isUnit_det W₀), Matrix.map_one _ (map_zero _) (map_one _)]
    have hcol : U.map p.pr *ᵥ (fun i => p.pr (ratV (vecB B.o B.ζ) i)) = -(β.b *ᵥ t) := by
      have h1 : (fun i => p.pr (ratV (vecB B.o B.ζ) i)) = ι ∘ vecB B.o B.ζ := rfl
      have h2 : (l.τᴴ * B.L.gram * B.o.qB).map ι *ᵥ (ι ∘ vecB B.o B.ζ) =
          (-(ι (D.host.xi0 * star D.host.xi0))) • g' := by
        funext i
        rw [← RingHom.map_mulVec, hrat, Pi.smul_apply, hgi]
        simp [map_neg, map_mul]
      have h3 : vecMulVec v (dualPick g') *ᵥ g' = v := by
        rw [Matrix.vecMulVec_mulVec, dualPick_dot g' hg0, MulOpposite.op_one, one_smul]
      have h4 : v = (ι D.host.xi0)⁻¹ • ((W₀.gram.map ι) *ᵥ (β.b *ᵥ t)) := rfl
      rw [h1, hUm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_smul, h3, h4,
        Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_mulVec, hGG, Matrix.one_mulVec,
        smul_smul, smul_smul, ← neg_one_smul k (β.b *ᵥ t)]
      congr 1
      have hs : ι (star D.host.xi0) = -ι D.host.xi0 := by rw [GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg]
      rw [map_mul, hs, map_neg, map_inv₀]
      field_simp
    have hrd : rd α₀ β U = fromCols 0 (replicateCol (Fin 1) (-t)) := by
      have hb : α₀.b = _ := hsum
      rw [rd, hb, Matrix.mul_assoc, Matrix.mul_fromCols, Matrix.mul_fromCols, ← Matrix.mul_assoc (U.map p.pr),
        ← Matrix.map_mul, hUA, Matrix.map_zero _ (map_zero _), Matrix.zero_mul, Matrix.mul_zero, matrix_mul_replicateCol_eq_replicateCol_mulVec,
        matrix_mul_replicateCol_eq_replicateCol_mulVec, hcol, Matrix.mulVec_neg, Matrix.mulVec_mulVec, β.b'b, Matrix.one_mulVec]
    intro i j
    rw [hrd]
    cases j with
    | inl j => simp
    | inr j => simp

end GlobalTheory.FinPl.LineAct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KappaSplitHalfPointMultipliesByCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KappaRowChar

variable {D : D7}

theorem half_mul_right {m n r : ℕ} {f : AE D} {M : Mx D m n} (h : IsHalf f M) (N : Mx D n r) : IsHalf f (M ⬝ N) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, h i _]

theorem half_mul_left {m n r : ℕ} {f : AE D} {M : Mx D n r} (N : Mx D m n) (h : IsHalf f M) : IsHalf f (N ⬝ M) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, h k j]

theorem half_smul {m n : ℕ} {f : AE D} {M : Mx D m n} (c : AE D) (h : IsHalf f M) : IsHalf f (c • M) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, h i j]

theorem half_adj {m n : ℕ} {f : AE D} {M : Mx D m n} (h : IsHalf f M) : IsHalf (cA D f) (adj M) := by
  intro i j
  show cA D f * cA D (M j i) = cA D (M j i)
  rw [← map_mul, h j i]

theorem trace_half {n : ℕ} {f : AE D} {M : Mx D n n} (h : IsHalf f M) : f * M.trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, Finset.mul_sum, h _ _]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_mul_sec (p : GlobalTheory.FinPl.SplitPt D k) (a : k) : p.e * p.sec a = p.sec a := by
  rw [← p.sec_pr, p.pr_sec]

theorem wRow_half {n : Type} [Fintype n] [DecidableEq n] (p : GlobalTheory.FinPl.SplitPt D k) {W₀ L' : HSp D}
    (ζ' : Fin L'.rank → D.host.E) (β : GlobalTheory.FinPl.Frame p W₀ n) (t : n → k) :
    IsHalf p.e (GlobalTheory.FinPl.LineAct.wRow p ζ' β t) := by
  intro i j
  exact e_mul_sec p _

theorem trace_vecMulVec_mul {R : Type} [CommRing R] {a b c : Type} [Fintype a] [Fintype b] [Fintype c]
    (u : a → R) (v : b → R) (X : Matrix b c R) (J : Matrix c a R) :
    (vecMulVec u v * X * J).trace = v ⬝ᵥ (X *ᵥ (J *ᵥ u)) := by
  rw [Matrix.mul_assoc, Matrix.mulVec_mulVec]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.KappaRowChar

end

namespace GlobalTheory.KappaRowChar

open GlobalTheory.FinPl.LineAct (iota)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_trace {n : Type} [Fintype n] [DecidableEq n] (p : GlobalTheory.FinPl.SplitPt D k) {W₀ L' : HSp D} {a b : ℕ}
    (τ : Matrix (Fin a) (Fin L'.rank) D.host.E) (ζ' : Fin L'.rank → D.host.E) (ζ : Fin a → D.host.E) (hτ : τ *ᵥ ζ' = -ζ)
    (β : GlobalTheory.FinPl.Frame p W₀ n) (t : n → k) (x : Mx D W₀.rank b) (iB : Matrix (Fin b) (Fin a) D.host.E) :
    p.pr (((rat τ : Mx D a L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝ (x ⬝ (rat iB : Mx D b a))).trace =
      -(t ⬝ᵥ (β.b' *ᵥ (x.map p.pr *ᵥ (iB.map (iota p) *ᵥ fun i => iota p (ζ i))))) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show p.pr (((rat τ : Mx D a L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝ (x ⬝ (rat iB : Mx D b a))).trace =
      ((((rat τ : Mx D a L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝ (x ⬝ (rat iB : Mx D b a))).map p.pr).trace from by
    simp only [Matrix.trace, Matrix.diag, map_sum]; rfl]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]
  have hτm : (rat τ : Mx D a L'.rank).map p.pr = τ.map (iota p) := rfl
  have hwm : (GlobalTheory.FinPl.LineAct.wRow p ζ' β t).map p.pr = vecMulVec (fun i => iota p (ζ' i)) (t ᵥ* β.b') := by
    ext i j
    simp only [Matrix.map_apply, GlobalTheory.FinPl.LineAct.wRow, Matrix.of_apply, p.pr_sec, vecMulVec_apply]
  have hjm : (rat iB : Mx D b a).map p.pr = iB.map (iota p) := rfl
  have ha : τ.map (iota p) *ᵥ (fun i => iota p (ζ' i)) = -(fun i => iota p (ζ i)) := by
    funext i
    have h := RingHom.map_mulVec (iota p) τ ζ' i
    rw [hτ] at h
    simp only [Pi.neg_apply, map_neg] at h ⊢
    exact h.symm
  rw [hτm, hwm, hjm, Matrix.mul_vecMulVec, ← Matrix.mul_assoc, trace_vecMulVec_mul, ha, Matrix.mulVec_neg,
    Matrix.mulVec_neg, dotProduct_neg, Matrix.dotProduct_mulVec t]

end GlobalTheory.KappaRowChar

namespace GlobalTheory.KappaRowChar

open GlobalTheory.FinPl.LineAct (iota)


set_option maxHeartbeats 1600000 in
theorem kappa_wRow_char : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (L' W₀ : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p W₀ n), IsSumFrame B.o B.ζ α α₀ → ∀ t : n → k, IsHalf (cA D p.e) ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t))) ∧ ∀ x : WO B.V₀ W₀, IsHalf p.e x → ψ (symplO B.V₀ W₀ x ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t)))) = (χ (-(t ⬝ᵥ fun i => rd α₀ β x i (Sum.inr 0))) : ℂ) := by
  intro D k _ _ _ _ p ψ χ hχ n n' _ _ _ _ ρ B L' W₀ ζ' l α α₀ β hsum t
  have hwh : IsHalf p.e (GlobalTheory.FinPl.LineAct.wRow p ζ' β t) := wRow_half p ζ' β t
  have hmh : IsHalf p.e ((rat l.τ : Mx D B.L.rank L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) := half_mul_left _ hwh
  have hk : l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t) = incA D (-D.host.xi0⁻¹) •
      (giA W₀ ⬝ (adj ((rat l.τ : Mx D B.L.rank L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝ gA B.L)) := rfl
  have hu : (B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t)) =
      l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝ B.o.pB := by
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add]
  refine ⟨?_, fun x _ => ?_⟩
  · rw [hu, hk]
    exact half_mul_right (half_smul _ (half_mul_left _ (half_mul_right (half_adj hmh) _))) _
  · have h0 : symplO B.A W₀ ((B.o.resS W₀) x).1 0 = 0 := by simp [symplO, hO]
    have hxi : incA D D.host.xi0 * cA D (incA D (-D.host.xi0⁻¹)) = 1 := by
      have hne := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
      rw [GlobalTheory.DualPairCheck.cA_incA, ← map_mul, star_neg, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, neg_inv, neg_neg,
        mul_inv_cancel₀ hne, map_one]
    have hxi' : ∀ T : AE D, incA D D.host.xi0 * (cA D (incA D (-D.host.xi0⁻¹)) * T) = T := fun T => by
      rw [← mul_assoc, hxi, one_mul]
    have hs : symplO B.V₀ W₀ x ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t))) =
        Algebra.trace (AF D.host.F) (AE D)
          (((rat l.τ : Mx D B.L.rank L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝ (x ⬝ B.o.jB)).trace := by
      rw [OrthDec.symplO_resS, AddEquiv.apply_symm_apply, h0, zero_add, symplO, hO_eq_trace, hk]
      simp only [adj_smul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc,
        giA_gA_cancel, trace_smul, smul_eq_mul, OrthDec.resS_apply]
      rw [hxi']
    rw [hs, show B.o.jB = (rat B.o.iB : Mx D B.V₀.rank B.L.rank) from rfl]
    have hc := trace_half (half_mul_right hmh (x ⬝ (rat B.o.iB : Mx D B.V₀.rank B.L.rank)))
    have hsec : p.sec (p.pr (((rat l.τ : Mx D B.L.rank L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝
        (x ⬝ (rat B.o.iB : Mx D B.V₀.rank B.L.rank))).trace) =
        (((rat l.τ : Mx D B.L.rank L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝
          (x ⬝ (rat B.o.iB : Mx D B.V₀.rank B.L.rank))).trace := by
      rw [p.sec_pr]; exact hc
    show psiE ψ _ = _
    rw [← hsec, ← hχ, pr_trace p l.τ ζ' B.ζ l.map β t x B.o.iB]
    have hb : ∀ r, α₀.b r (Sum.inr 0) = (B.o.iB.map (iota p) *ᵥ fun i => iota p (B.ζ i)) r := by
      intro r
      rw [hsum]
      simp only [fromCols_apply_inr, replicateCol_apply, ratV, vecB]
      exact RingHom.map_mulVec (iota p) B.o.iB B.ζ r
    have hcol : (fun i => rd α₀ β x i (Sum.inr 0)) =
        β.b' *ᵥ (x.map p.pr *ᵥ (B.o.iB.map (iota p) *ᵥ fun i => iota p (B.ζ i))) := by
      funext i
      rw [Matrix.mulVec_mulVec]
      simp only [rd, Matrix.mul_apply, hb]
      rfl
    rw [hcol]

end GlobalTheory.KappaRowChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatIndLastKerRow
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {T L : HSp D} {n : Type} [Fintype n] [DecidableEq n]

def zcol (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (y : WO L T) : n → k :=
  β.b' *ᵥ fun i => p.pr ((y *ᵥ fun j => incA D (ζ j)) i)


open Classical in
def colFun (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (a : (n → k) → ℂ) (y : WO L T) : ℂ :=
  if IsHalf p.e y then a (zcol β ζ y) else 0

def zrow (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (x : WO T L) : n → k :=
  (p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)))⁻¹ •
    ((fun i => p.pr (((fun j => incA D ((star ζ ᵥ* L.gram) j)) ᵥ* x) i)) ᵥ* β.b)


open Classical in
def rowFun (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (b : (n → k) → ℂ) (x : WO T L) : ℂ :=
  if IsHalf p.e x then b (zrow β ζ x) else 0

def restrModel {m n m' n' m'' n'' : ℕ} (r : Mx D m n ≃+ Mx D m' n' × Mx D m'' n'') (h : Mx D m'' n'' → ℂ)
    (T' : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ)) (y : Mx D m'' n'') :
    (Mx D m' n' → ℂ) →ₗ[ℂ] (Mx D m' n' → ℂ) where
  toFun Φ := fun w => T' (fun t => Φ (r t).1 * h (r t).2) (r.symm (w, y))
  map_add' Φ Φ' := by
    funext w
    have : (fun t => (Φ + Φ') (r t).1 * h (r t).2) = (fun t => Φ (r t).1 * h (r t).2) + fun t => Φ' (r t).1 * h (r t).2 := by
      funext t; simp [add_mul]
    rw [this, map_add (f := _)]; rfl
  map_smul' c Φ := by
    funext w
    have : (fun t => (c • Φ) (r t).1 * h (r t).2) = c • fun t => Φ (r t).1 * h (r t).2 := by
      funext t; simp [mul_assoc]
    rw [this, map_smul]; rfl

theorem restrModel_apply {m n m' n' m'' n'' : ℕ} (r : Mx D m n ≃+ Mx D m' n' × Mx D m'' n'') (h : Mx D m'' n'' → ℂ)
    (T' : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ)) (y : Mx D m'' n'') (Φ : Mx D m' n' → ℂ) (w : Mx D m' n') :
    restrModel r h T' y Φ w = T' (fun t => Φ (r t).1 * h (r t).2) (r.symm (w, y)) := rfl

theorem heisO_resS_symm (ψ : AddChar (AF D.host.F) ℂ) {S A L T : HSp D} (o : OrthDec S A L) (a : WO A T)
    (F : WO S T → ℂ) (w : WO A T) (y : WO L T) :
    heisO ψ S T ((o.resS T).symm (a, 0)) F ((o.resS T).symm (w, y)) =
      heisO ψ A T a (fun w' => F ((o.resS T).symm (w', y))) w := by
  simp only [heisO]
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have h0 : symplOH L T y 0 = 0 := by simp [symplOH, symplO, hO]
  rw [h0, add_zero, ← map_add (f := _)]
  simp

theorem heisO_resT_symm (ψ : AddChar (AF D.host.F) ℂ) {S A L T : HSp D} (o : OrthDec S A L) (a : WO T A)
    (F : WO T S → ℂ) (w : WO T A) (y : WO T L) :
    heisO ψ T S ((o.resT T).symm (a, 0)) F ((o.resT T).symm (w, y)) =
      heisO ψ T A a (fun w' => F ((o.resT T).symm (w', y))) w := by
  simp only [heisO]
  rw [o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have h0 : symplOH T L y 0 = 0 := by simp [symplOH, symplO, hO]
  rw [h0, add_zero, ← map_add (f := _)]
  simp

theorem symplO_resS_symm {S A L T : HSp D} (o : OrthDec S A L) (t : WO S T) (a : WO A T) :
    symplO S T t ((o.resS T).symm (a, 0)) = symplO A T ((o.resS T) t).1 a := by
  rw [o.symplO_resS, AddEquiv.apply_symm_apply]
  simp [symplO, hO]

theorem symplO_resT_symm {S A L T : HSp D} (o : OrthDec S A L) (t : WO T S) (a : WO T A) :
    symplO T S t ((o.resT T).symm (a, 0)) = symplO T A ((o.resT T) t).1 a := by
  rw [o.symplO_resT, AddEquiv.apply_symm_apply]
  simp [symplO, hO]

theorem half_resS_symm {S A L T : HSp D} (o : OrthDec S A L) {e : AE D} {a : WO A T} (ha : IsHalf e a) :
    IsHalf e ((o.resS T).symm (a, 0)) := by
  intro i j
  rw [OrthDec.resS_symm_apply]
  simp only [Matrix.zero_mul, add_zero, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [← mul_assoc, ha]

theorem half_resT_symm {S A L T : HSp D} (o : OrthDec S A L) {e : AE D} {a : WO T A} (ha : IsHalf e a) :
    IsHalf e ((o.resT T).symm (a, 0)) := by
  intro i j
  rw [OrthDec.resT_symm_apply]
  simp only [Matrix.mul_zero, add_zero, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [mul_left_comm, ha]

section Lat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [Fintype n']

theorem latInd_lastKer (ΛA : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)) :
    latInd (lastKer ΛA) ΛT = tensCol (latInd ΛA ΛT) (vecInd ΛT) := by
  classical
  funext x
  have hmv : ∀ y : n' ⊕ Fin 1 → k, x *ᵥ y = x.submatrix id Sum.inl *ᵥ (y ∘ Sum.inl) +
      y (Sum.inr 0) • fun i => x i (Sum.inr 0) := by
    intro y; funext i
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, mul_comm]
  have key : (∀ y ∈ lastKer ΛA, x *ᵥ y ∈ ΛT) ↔
      (∀ y ∈ ΛA, x.submatrix id Sum.inl *ᵥ y ∈ ΛT) ∧ (fun i => x i (Sum.inr 0)) ∈ ΛT := by
    constructor
    · intro h
      refine ⟨fun y hy => ?_, ?_⟩
      · have hm : Sum.elim y 0 ∈ lastKer ΛA := GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨by simpa using hy, by simp⟩
        have := h _ hm
        rw [hmv] at this
        simpa using this
      · have hm : (Sum.elim 0 1 : n' ⊕ Fin 1 → k) ∈ lastKer ΛA :=
          GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨by simpa using ΛA.zero_mem, by simp⟩
        have := h _ hm
        rw [hmv] at this
        simpa using this
    · rintro ⟨h1, h2⟩ y hy
      obtain ⟨hy1, hy2⟩ := GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.1 hy
      rw [hmv]
      refine ΛT.add_mem (h1 _ hy1) ?_
      have := ΛT.smul_mem (⟨y (Sum.inr 0), hy2⟩ : 𝒪[k]) h2
      exact this
  simp only [latInd, tensCol, vecInd]
  by_cases h : ∀ y ∈ lastKer ΛA, x *ᵥ y ∈ ΛT
  · rw [if_pos h, if_pos (key.1 h).1, if_pos (key.1 h).2, mul_one]
  · rw [if_neg h]
    by_cases h1 : ∀ y ∈ ΛA, x.submatrix id Sum.inl *ᵥ y ∈ ΛT
    · rw [if_pos h1, if_neg fun h2 => h (key.2 ⟨h1, h2⟩), mul_zero]
    · rw [if_neg h1, zero_mul]

theorem latInd_lastKer_row (ΛA : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)) :
    latInd ΛT (lastKer ΛA) = tensRow (latInd ΛT ΛA) (dualInd ΛT) := by
  classical
  funext x
  have key : (∀ y ∈ ΛT, x *ᵥ y ∈ lastKer ΛA) ↔
      (∀ y ∈ ΛT, x.submatrix Sum.inl id *ᵥ y ∈ ΛA) ∧ InDual ΛT (x (Sum.inr 0)) := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer, InDual]
    exact ⟨fun h => ⟨fun y hy => (h y hy).1, fun y hy => (h y hy).2⟩, fun h y hy => ⟨h.1 y hy, h.2 y hy⟩⟩
  simp only [latInd, tensRow, dualInd]
  by_cases h : ∀ y ∈ ΛT, x *ᵥ y ∈ lastKer ΛA
  · rw [if_pos h, if_pos (key.1 h).1, if_pos (key.1 h).2, mul_one]
  · rw [if_neg h]
    by_cases h1 : ∀ y ∈ ΛT, x.submatrix Sum.inl id *ᵥ y ∈ ΛA
    · rw [if_pos h1, if_neg fun h2 => h (key.2 ⟨h1, h2⟩), mul_zero]
    · rw [if_neg h1, zero_mul]

end Lat

end GlobalTheory.FinPl.ExtZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaIntegralTranslateSmul
section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ThetaInv

def rmulEquiv {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (g : G) :
    GlobalTheory.AutomorphicL2Unitary.Quot Γ ≃ᵐ GlobalTheory.AutomorphicL2Unitary.Quot Γ where
  toFun := rmul Γ g
  invFun := rmul Γ g⁻¹
  left_inv q := by rw [← rmul_mul, mul_inv_cancel, rmul_one]
  right_inv q := by rw [← rmul_mul, inv_mul_cancel, rmul_one]
  measurable_toFun := measurable_rmul g
  measurable_invFun := measurable_rmul g⁻¹

end GlobalTheory.ThetaInv
end
end

