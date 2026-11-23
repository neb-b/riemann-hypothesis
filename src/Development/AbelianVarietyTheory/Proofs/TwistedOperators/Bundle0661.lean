module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0606
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiFrameOfGridLatticeLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.FlatPlace

namespace NormalJac

theorem jacobiDualColumn_scalar_identity {K : Type} [Field K] (X : K) (hX : X ≠ 0) (i k : ℕ) :
    (X ^ (i + 1 + k))⁻¹ * (-((-X) ^ (i + 1 + k) * X ^ (i + 1 + k)) / X) * (-1 / X) ^ k = (-X) ^ i := by
  have h1 : ((-1 : K) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [neg_pow X, neg_pow X, div_pow]
  field_simp
  linear_combination (X * X ^ i * X ^ k * (-1) ^ i) * h1

theorem mul_col_eq {ι' ι κ μ K : Type} [Fintype ι] [Field K] (P : Matrix ι' ι K) (Y : Matrix ι κ K) (Z : Matrix ι μ K)
    (c : κ) (c' : μ) (h : ∀ l, Y l c = Z l c') (r : ι') : (P * Y) r c = (P * Z) r c' := by
  simp only [Matrix.mul_apply, h]

theorem hz_besAt {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {t : T} {M : Vol G} (hM : M.Is t)
    (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (vN : GlobalTheory.Unf.VolN (besDecAt G j σ hj)) {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) :
    p.hz (besAt G hM j σ hj vN) = -((-p.xi) ^ σ * p.xi ^ σ) := by
  simp only [Place.hz, besAt, dotProduct, mulVec]
  show p.pr (∑ i : Fin 1, star (fun _ : Fin 1 => D.host.xi0 ^ σ) i * ∑ i_1 : Fin 1, (GlobalTheory.SeeSaw.Model.nLine D).gram i i_1 * D.host.xi0 ^ σ) = _
  simp only [Fin.sum_univ_one, nLine_gram, Pi.star_apply, star_pow, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, Place.xi, Place.pr, map_mul, map_neg, map_pow, map_one]
  ring

theorem pr_mul' {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
    (x y : D.host.E) : p.pr (x * y) = p.pr x * p.pr y := map_mul (p.π.comp (incA D)) x y

theorem place_proj_neg_xi_pow {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (n : ℕ) : p.pr ((-D.host.xi0) ^ n) = (-p.xi) ^ n :=
  (map_pow (p.π.comp (incA D)) _ n).trans (congrArg (· ^ n) (map_neg (p.π.comp (incA D)) _))

theorem neg_mul_neg_one_eq_of_eq {K : Type} [Field K] (y a S : K) (h : S = a) : -(y * a) * -1 = S * y := by rw [h]; ring

end NormalJac


open NormalJac in
set_option maxHeartbeats 1600000 in
theorem big_jacP : Big fun ch => JacP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch hsc => ?_⟩⟩
  clear hε hx hsc hch s
  intro t w hw p hp M hM j σ hj vN a ha c hc
  have h1 := ch.S.row t trivial w hw (j + 1) (by omega)
  have hm : (locGrid ch.G t w).m = D.R.m := rfl
  obtain rfl : c = 2 * σ := by
    have h2 := topRank_add (G := locGrid ch.G t w) one_le_sLen (j + 1)
    rw [hm] at h2; omega
  have hpr : ∀ x, p.pr x = algebraMap D.host.E (Kw w) x := fun x =>
    (hp.2.1 _).trans (Comparison₂.cpt_tmul w x)
  have hxi : p.xi ≠ 0 := by
    rw [Place.xi, hpr]; exact (map_ne_zero _).2 (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D)
  have hE : (epsV ch.G t w (D.R.m, j + 1)).val =
      diagonal fun q => if topRank (locGrid ch.G t w) (j + 1) + σ ≤ q.val then -1 else 1 := by
    by_cases hσ : σ = 0
    · subst hσ
      rw [epsV_eq_one _ _ (by omega), Units.val_one]
      ext q q'
      rw [Matrix.one_apply, diagonal_apply, if_neg (show ¬ (topRank (locGrid ch.G t w) (j + 1) + 0 ≤ q.val) by have := q.2; omega)]
    · have hodd : Odd (j + 1) := by
        obtain ⟨b, hb⟩ := D.R.m_even
        exact ⟨j / 2, by omega⟩
      rw [epsV_apply, if_pos (mem_idx.2 ⟨by omega, by omega⟩), sgnAt, GlobalTheory.SplitFlip.diagGL_val]
      congr 1
      funext q
      have e : (D.R.m - 1 - (j + 1)) / 2 = σ := by omega
      simp only [e, hodd, true_and]
      split_ifs <;> simp
  have h₁ : j + 1 < D.R.m := by omega
  have h₂ : D.R.m - 1 - (j + 1) = 2 * σ := by omega
  obtain ⟨T0, T1, T2⟩ : (mt _ a).map p.π * (rowJac ch.G (j + 1) h₁ σ h₂).i₀.map p.pr = (rowJac ch.G (j + 1) h₁ σ h₂).i₀.map p.pr ∧
      (mt _ a).map p.π * (rowJac ch.G (j + 1) h₁ σ h₂).e.map p.pr =
        ((rowJac ch.G (j + 1) h₁ σ h₂).e * diagonal fun a : Fin σ => (D.host.xi0 ^ a.1)⁻¹).map p.pr ∧
      (mt _ a).map p.π * (rowJac ch.G (j + 1) h₁ σ h₂).e'.map p.pr =
        ((rowJac ch.G (j + 1) h₁ σ h₂).e' * diagonal fun a : Fin σ => star (D.host.xi0 ^ a.1)).map p.pr := by
    rcases ha with ⟨rfl, rfl⟩ | ⟨δ, hδ, hδa⟩
    · refine ⟨?_, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
      rw [show mt (ch.G.V (Node.grid D.R.m (j + 1))) 1 = 1 by simp [Formalism.L2.Theta.mt], Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    · obtain ⟨e0, e1, e2⟩ := hδ.2.2 σ h₁ h₂
      have key : ∀ {n : ℕ} (X Y : Matrix (Fin (ch.G.V (Node.grid D.R.m (j + 1))).rank) (Fin n) D.host.E),
          HMul.hMul (mt _ δ) (X.map (incA D)) = Y.map (incA D) → (mt _ a).map p.π * X.map p.pr = Y.map p.pr := by
        intro n X Y h
        have := congrArg (fun Z => Z.map p.π) h
        simp only [Matrix.map_mul, Matrix.map_map] at this
        rw [hδa]
        exact this
      exact ⟨key _ _ e0, key _ _ e1, key _ _ e2⟩
  have hfl : ∀ {a c b : ℕ} (h : a + c = b) (x : Fin a), ((frame h (Sum.inl x)) : ℕ) = x := by intros; simp [frame]
  have hfr : ∀ {a c b : ℕ} (h : a + c = b) (q : Fin c), ((frame h (Sum.inr q)) : ℕ) = a + q := by intros; simp [frame]
  clear ha
  have T0' : ∀ {n : Type} [Fintype n] (Z : Matrix (Fin (ch.G.V (Node.top (j + 1))).rank) n (Kw w)), (mt _ a).map p.π * ((rowJac ch.G (j + 1) h₁ σ h₂).i₀.map p.pr * Z) =
      (rowJac ch.G (j + 1) h₁ σ h₂).i₀.map p.pr * Z := by
    intro n _ Z; rw [← Matrix.mul_assoc, T0]
  dsimp only [Place.IsJacFrame, jacAt]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro r x
    simp only [mvFr, frRow, frOf, frTop, submatrix_apply, id, hE, mul_diagonal]
    rw [if_neg (by rw [hfl]; omega), mul_one]
    refine (mul_col_eq _ _ ((rowJac ch.G (j + 1) h₁ σ h₂).i₀.map p.pr *
      (loc w (ch.S.βp (j + 1))).val.submatrix id (Fin.cast (topRank_eq ch.G t w h₁.le))) _ x (fun l => ?_) r).trans
      (congrFun (congrFun (T0' _) r) x)
    have e1 := congrFun (congrFun h1 l) (Sum.inl (Fin.cast (topRank_eq ch.G t w h₁.le) x))
    simp only [submatrix_apply, id, fromCols_apply_inl, Matrix.mul_apply, Matrix.map_apply] at e1
    simp only [submatrix_apply, id, Matrix.mul_apply, Matrix.map_apply, hpr]
    refine (congrArg _ (Fin.ext ?_)).trans e1
    simp [frame]
  · intro i jj hij r
    simp only [mvFr, frRow, frOf, submatrix_apply, id, hE, mul_diagonal]
    rw [if_neg (by rw [hfr]; omega), mul_one]
    refine (mul_col_eq _ _ ((rowJac ch.G (j + 1) h₁ σ h₂).e.map p.pr) _ i (fun l => ?_) r).trans ?_
    rotate_left
    · rw [T1]
      have hinv : ∀ x : D.host.E, p.π (incA D x⁻¹) = (p.π (incA D x))⁻¹ := fun x => map_inv₀ (p.π.comp (incA D)) x
      simp only [Matrix.map_apply, mul_diagonal, Place.pr, Place.xi, map_mul, hinv, map_pow]
      have hx : p.π (incA D D.host.xi0) ≠ 0 := hxi
      have e : p.π (incA D D.host.xi0) ^ σ = p.π (incA D D.host.xi0) ^ (σ - i.val) * p.π (incA D D.host.xi0) ^ i.val := by
        rw [← pow_add]; congr 1; omega
      rw [e]
      field_simp
    · have e1 := congrFun (congrFun h1 l) (Sum.inr (Fin.cast h₂.symm jj))
      simp only [submatrix_apply, id, fromCols_apply_inr, mul_diagonal, Matrix.map_apply] at e1
      rw [if_neg (Nat.succ_ne_zero j), pow_zero, mul_one, frameSign, if_neg (by simp only [Fin.val_cast]; omega), mul_one] at e1
      simp only [submatrix_apply, id, Matrix.map_apply, hpr]
      refine (congrArg _ (Fin.ext ?_)).trans (e1.trans ?_)
      · simp [frame, topRank_eq ch.G t w h₁.le]
      · have he : (rowJac ch.G (j + 1) h₁ σ h₂).e l i = (ch.G.rowDec (j + 1) h₁).a l (Fin.castLE (by omega) i) := rfl
        rw [he]
        exact congrArg _ (congrArg _ (Fin.ext (by simp; omega)))
  · intro i jj hij r
    simp only [mvFr, frRow, frOf, submatrix_apply, id, hE, mul_diagonal]
    rw [if_pos (by rw [hfr]; omega)]
    refine (congrArg (· * (-1)) (mul_col_eq _ _ (-((rowJac ch.G (j + 1) h₁ σ h₂).e'.map p.pr)) _ i (fun l => ?_) r)).trans ?_
    rotate_left
    · rw [Matrix.mul_neg, Matrix.neg_apply, T2, hz_besAt]
      simp only [Matrix.neg_apply, Matrix.map_apply, mul_diagonal, pr_mul', star_pow, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, place_proj_neg_xi_pow]
      have key := jacobiDualColumn_scalar_identity p.xi hxi i (σ - 1 - i)
      rw [show (i : ℕ) + 1 + (σ - 1 - i) = σ by omega] at key
      exact neg_mul_neg_one_eq_of_eq _ _ _ key
    · have e1 := congrFun (congrFun h1 l) (Sum.inr (Fin.cast h₂.symm jj))
      simp only [submatrix_apply, id, fromCols_apply_inr, mul_diagonal, Matrix.map_apply] at e1
      rw [if_neg (Nat.succ_ne_zero j), pow_zero, mul_one, frameSign, if_pos (by simp only [Fin.val_cast]; omega), mul_neg_one] at e1
      simp only [submatrix_apply, id, Matrix.neg_apply, Matrix.map_apply, hpr]
      refine (congrArg _ (Fin.ext ?_)).trans (e1.trans ?_)
      · simp [frame, topRank_eq ch.G t w h₁.le]
      · simp only [rowJac, jacDec, submatrix_apply, id]
        exact congrArg _ (congrArg _ (congrArg _ (Fin.ext (by simp; omega))))

end GlobalTheory.FlatPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselCarriesFlagLinesRowPeriodSucc
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowShape.ColsJB

variable {D : D7} {A B : HSp D} {c : ℕ}

theorem coreMat_iB' {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iB = midCol d h := by
  refine (Matrix.submatrix_mul_equiv _ _ _ _ _).trans ?_
  show Matrix.fromCols (frameMat B A d.ι) (midCol d h) *
      Matrix.fromRows (0 : Matrix (Fin A.rank) (Fin 1) D.host.E) (1 : Matrix (Fin 1) (Fin 1) D.host.E) = _
  rw [Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, zero_add]

theorem coreMat_vecB {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) (x : D.host.E) :
    coreMat d h *ᵥ vecB (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)) (fun _ => x) =
      fun k => x * d.a k ⟨σ, by omega⟩ := by
  show coreMat d h *ᵥ (_ *ᵥ _) = _
  rw [Matrix.mulVec_mulVec, coreMat_iB']
  funext k
  show ∑ j : Fin 1, midCol d h k j * x = _
  simp [midCol, mul_comm]

end GlobalTheory.RowShape.ColsJB

theorem GlobalTheory.RowShape.cols_jacBes_rowN : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ i σ (hi : i + 2 * (σ + 1) + 1 = D.R.m) v, GlobalTheory.FinPl.ColsAt (rowJac ch.G i (by omega) (σ + 1) (by omega))
    (xLast (besDecAt ch.G (i + 1) σ (by omega)) (vecB (GlobalTheory.OrthSumExists.orthDecHsum D (ch.G.V (.top (i + 1))) (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ))
    (GlobalTheory.RowShape.rowN ch.G i) (GlobalTheory.RowShape.rowN ch.G (i + 1)) v := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ => ?_⟩⟩
  intro i σ hi v a s hs
  have hodd : Odd i := by
    obtain ⟨k, hk⟩ := D.R.m_even
    exact ⟨k - σ - 2, by omega⟩
  unfold GlobalTheory.RowShape.rowN
  rw [dite_eq_left (by omega), dite_eq_left (by omega)]
  have hrat : ∀ {m n : ℕ} (N : Matrix (Fin m) (Fin n) D.host.E) (z : Fin n → D.host.E),
      GlobalTheory.MixModel.rat N *ᵥ ratV z = ratV (N *ᵥ z) := by
    intro m n N z
    funext k
    set_option synthInstance.maxHeartbeats 100000 in
      simp [GlobalTheory.MixModel.rat, ratV, Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hL : colMul (rowJac ch.G i (by omega) (σ + 1) (by omega)).jX a s =
      fun k => s * incA D ((ch.G.rowDec i (by omega)).a k ⟨a.1, by omega⟩) := by
    funext k
    rfl
  have hR : colMul (xLast (besDecAt ch.G (i + 1) σ (by omega))
      (vecB (GlobalTheory.OrthSumExists.orthDecHsum D (ch.G.V (.top (i + 1))) (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ)) a s =
      fun k => (s * incA D (D.host.xi0 ^ a.1)) * incA D ((ch.G.rowDec (i + 1) (by omega)).a k ⟨a.1, by omega⟩) := by
    funext k
    induction a using Fin.lastCases with
    | last =>
      have e1 := GlobalTheory.RowShape.ColsJB.coreMat_vecB (ch.G.rowDec (i + 1) (by omega)) (σ := σ) (by omega) (D.host.xi0 ^ σ)
      simp only [colMul, xLast, Matrix.of_apply, Fin.snoc_last, HypDec.j0, hrat, Fin.val_last]
      show s * ratV ((coreMat (ch.G.rowDec (i + 1) (by omega)) (σ := σ) (by omega)) *ᵥ _) k = _
      rw [e1]
      simp only [ratV, map_mul]
      ring
    | cast b =>
      simp only [colMul, xLast, Matrix.of_apply, Fin.snoc_castSucc, HypDec.jX, GlobalTheory.MixModel.rat, Matrix.map_apply]
      show s * incA D ((Matrix.submatrix (ch.G.rowDec (i + 1) (by omega)).a id (Fin.castLE (by omega)) *
        diagonal (lam (D := D) σ) : Matrix (Fin _) (Fin σ) D.host.E) k b) = _
      rw [Matrix.mul_diagonal, map_mul]
      simp only [lam, Matrix.submatrix_apply, id, Fin.coe_castSucc]
      rw [mul_comm (incA D _) (incA D _), ← mul_assoc]
      rfl
  rw [hL, hR, (GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff _ (neg_ne_zero.2 one_ne_zero) _ _ _ v s).1,
    (GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff _ (neg_ne_zero.2 one_ne_zero) _ _ _ v _).2]
  have hx : D.host.xi0 ^ a.1 ≠ 0 := pow_ne_zero _ (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D)
  have h1 : GlobalTheory.RowShape.rowId D i ⟨a.1, by omega⟩ = FractionalIdeal.spanSingleton _ ((D.host.xi0 ^ a.1)⁻¹) *
      stairId D.host.AA D.host.AAbar (D.R.m - 1 - i) ⟨a.1, by omega⟩ := by
    unfold GlobalTheory.RowShape.rowId GlobalTheory.RowShape.tiltSc
    rw [if_pos hodd, if_pos (by simp only; omega)]
  have h2 : D.host.AA * GlobalTheory.RowShape.rowId D (i + 1) ⟨a.1, by omega⟩ =
      stairId D.host.AA D.host.AAbar (D.R.m - 1 - i) ⟨a.1, by omega⟩ := by
    unfold GlobalTheory.RowShape.rowId GlobalTheory.RowShape.tiltSc
    rw [if_neg (by rw [Nat.not_odd_iff_even]; exact hodd.add_one), FractionalIdeal.spanSingleton_one, one_mul]
    unfold stairId
    rw [show D.R.m - 1 - i - a.1 = (D.R.m - 1 - (i + 1) - a.1) + 1 by omega, pow_succ]
    ring
  rw [h1, h2, idV_spanSingleton_mul_iff D v _ _ (inv_ne_zero hx) s, inv_inv, mul_comm, and_iff_left hs]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowCharsUnramifiedOffTensorPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastRowUnram

theorem chars_unram : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ (t : T) (v : GlobalTheory.FinPl.Pl D), (∀ w ∈ locPl ch.G t, w.under (𝓞 D.host.F) ≠ v) → ∀ i, i < D.R.m →
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (ch.G.chrS (.mu t D.R.m i)) v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (ch.G.chrT (.mu t D.R.m i)) v := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ => ?_⟩⟩
  intro t v hv i hi
  classical
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hS0 := GlobalTheory.RowVacScalar.notMem_S0_of_no_place_above ch.G t hv
  have hQ : ∀ PP ∈ R.toLevCh.Q t, PP ∈ locPl ch.G t := fun PP h => by
    unfold locPl
    exact Finset.mem_union_right _ h
  have hmu : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (R.toLevCh.mu t (i + 1)) v := by
    refine GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => ?_
    show GlobalTheory.LFun.UnrAt (R.toLevCh.mu0 (i + 1) * R.toLevCh.xi t) w
    refine GlobalTheory.LFun.UnrAt.mul ?_ ?_
    · refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.mu0 ⟨i, hi⟩) w).2 ((R.toLevCh.C.isMu0 ⟨i, hi⟩).unr w fun k hk => ?_)
      refine hS0 (ch.G.pl.mem_S0_of_sum_eq.2 (Or.inr ((GlobalTheory.ChiGrid.S1_mem_OmF D).2 ?_)))
      have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
        show algebraMap _ (𝓞 D.host.E) _ ∈ w.asIdeal
        rw [map_natCast]; exact hk
      rw [hw] at this
      fin_cases k
      · exact Or.inl this
      · exact Or.inr (Or.inl this)
    · refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.xi t) w).2 ?_
      by_contra hu
      rcases (hL.Q_ram t w).1 hu with h | ⟨P', hP', hc⟩
      · exact hv w (hQ w h) hw
      · exact hv P' (hQ P' hP') ((GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc).trans hw)
  have key := GlobalTheory.RowVacScalar.attChr_charUnramAt hmu (GlobalTheory.RowVacScalar.eta_charUnramAt hL v)
  exact ⟨key _, key _⟩

end GlobalTheory.LastRowUnram
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastSeesawLineMapKeepsLatticesLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.LastLineLat

variable {D : D7}

theorem of_tmul_eq (p : AF D.host.F) {m n : ℕ} (y : Fin m → Fin n → D.host.E) :
    (Matrix.of fun i j => p ⊗ₜ[D.host.F] y i j : Mx D m n) = (p ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) • rat (Matrix.of y) := by
  ext i j
  simp only [rat, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  change _ = _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] y i j)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem cA_tmul_one (p : AF D.host.F) : cA D (p ⊗ₜ[D.host.F] (1 : D.host.E)) = p ⊗ₜ[D.host.F] (1 : D.host.E) := by
  simp [cA, sigR]

theorem adj_rat {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) : adj (rat M : Mx D m n) = rat Mᴴ := by
  ext i j
  simp [adj, rat, Matrix.conjTranspose_apply, GlobalTheory.DualPairCheck.cA_incA]

theorem rat_smul' {m n : ℕ} (c : D.host.E) (M : Matrix (Fin m) (Fin n) D.host.E) :
    (rat (c • M) : Mx D m n) = incA D c • rat M := by
  ext i j
  simp [rat]

theorem kap_gen {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) {c0 : D.host.E} (hτ : ∀ i k, τ i k = c0)
    (V : HSp D) (p : AF D.host.F) (a : D.host.E) (s : Fin V.rank → D.host.E)
    (t : Fin L''.rank → D.host.E) :
    kap τ V (Matrix.of fun i j => p ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * V.gram k j)) =
      Matrix.of fun i j => p ⊗ₜ[D.host.F] (s i * star (D.host.xi0⁻¹ * c0 * ∑ l, a * t l) * ∑ k, L.gram k j) := by
  have hy : (Matrix.of fun i j => a * t i * ∑ k, star (s k) * V.gram k j) =
      Matrix.vecMulVec (fun i => a * t i) (star s) * V.gram := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Finset.mul_sum, mul_assoc]
  have h1 := of_tmul_eq (D := D) p (fun i j => a * t i * ∑ k, star (s k) * V.gram k j)
  rw [hy] at h1
  have h2 := of_tmul_eq (D := D) p (fun i j => s i * star (D.host.xi0⁻¹ * c0 * ∑ l, a * t l) * ∑ k, L.gram k j)
  beta_reduce at h1 h2
  rw [h1, h2]
  unfold GlobalTheory.FinPl.kap GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj
  have he := cA_tmul_one (D := D) p
  generalize (p ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) = e at he ⊢
  rw [Matrix.mul_smul, adj_smul, he]
  rw [rat_mul (Matrix.vecMulVec (fun i => a * t i) (star s)) V.gram, ← Matrix.mul_assoc (rat τ), ← rat_mul τ,
    show (rat V.gram : Mx D V.rank V.rank) = gA V from rfl, adj_mul, adj_gA, adj_rat, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc, giA_gA_cancel, show gA L = (rat L.gram : Mx D L.rank L.rank) from rfl, ← rat_mul, smul_comm,
    ← rat_smul']
  congr 2
  ext i j
  congr 1
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, hτ,
    Pi.star_apply, Matrix.of_apply, smul_eq_mul, star_sum, star_mul', star_star, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg,
    Finset.mul_sum, Finset.sum_mul, inv_neg]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.LastLineLat

namespace GlobalTheory.LastLineLat

variable {D : D7}

theorem kap_add' {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (S : HSp D) (w w' : WO S L'') :
    kap τ S (w + w') = kap τ S w + kap τ S w' := by
  have hadj : ∀ x y : Mx D L.rank S.rank, adj (x + y) = adj x + adj y := fun x y => by
    ext i j
    simp [adj]
  unfold GlobalTheory.FinPl.kap GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj
  rw [Matrix.mul_add (rat τ) w w', hadj, Matrix.add_mul, Matrix.mul_add, smul_add]

theorem line_mem {L V : HSp D} (J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (hJ : D.host.AA ≤ D.host.AAbar * J)
    (Λ : Set (Fin V.rank → D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (α : Af D.host.F)
    (hα : α ∈ intAf D.host.F) (hP : ∀ v, ¬ P v → evalV D.host.F v α = 0) (s : Fin V.rank → D.host.E) (hs : s ∈ Λ)
    (c : D.host.E) (hc : c ∈ D.host.AA) :
    (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (s i * star c * ∑ k, L.gram k j) : Mx D V.rank L.rank) ∈
      latO L V (GlobalTheory.RowShape.latPi L J : Set _) Λ P := by
  have hc' : c ∈ D.host.AAbar * J := hJ hc
  refine FractionalIdeal.mul_induction_on (C := fun c => (Matrix.of fun i j =>
      pairA D.host.F 0 α ⊗ₜ[D.host.F] (s i * star c * ∑ k, L.gram k j) : Mx D V.rank L.rank) ∈
      latO L V (GlobalTheory.RowShape.latPi L J : Set _) Λ P) hc' ?_ ?_
  · intro b hb e he
    refine AddSubgroup.subset_closure ⟨α, hα, hP, star b, ?_, fun _ => e, ?_, s, hs, ?_⟩
    · rw [bridge_star_holds D.R D.host b]; exact Formalism.L2.Pj.conj_mem_AA D hb
    · exact Submodule.mem_pi.2 fun _ _ => he
    · ext i j
      simp only [Matrix.of_apply, star_mul', Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun _ _ => by ring
  · intro x y hx hy
    have : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (s i * star (x + y) * ∑ k, L.gram k j) :
        Mx D V.rank L.rank) = (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (s i * star x * ∑ k, L.gram k j)) +
        (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (s i * star y * ∑ k, L.gram k j)) := by
      ext i j
      simp only [Matrix.of_apply, Matrix.add_apply, star_add, mul_add, add_mul, TensorProduct.tmul_add]
    rw [this]
    exact add_mem hx hy

theorem AA_le_lineId (D : D7) (j : ℕ) (hj : j + 2 = D.R.m) :
    D.host.AA ≤ D.host.AAbar * GlobalTheory.RowShape.lineId D j := by
  have hb : D.host.AAbar ≠ 0 := by
    intro h
    have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rw [h] at h1
    simp at h1
  unfold GlobalTheory.RowShape.lineId
  rw [show (D.R.m - 2 - j) / 2 + 1 = 1 by omega, pow_one, pow_one, mul_comm D.host.AA, ← mul_assoc,
    mul_inv_cancel₀ hb, one_mul]

theorem mul_mem_AA {a : D.host.E} (ha : a ∈ D.host.AA) {t : D.host.E}
    (ht : t ∈ ((1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E)) : a * t ∈ D.host.AA := by
  rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_one_iff] at ht
  obtain ⟨y, rfl⟩ := ht
  rw [mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ y ha

end GlobalTheory.LastLineLat

namespace GlobalTheory.LastLineLat

theorem kap_latO (D : D7) (V : HSp D) (Λ : Set (Fin V.rank → D.host.E)) (j : ℕ) (hj : j + 2 = D.R.m)
    (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ∀ w ∈ latO V (pLine D) Λ (GlobalTheory.RowShape.topL D : Set _) (· = v),
      kap lastTau V w ∈ latO (Model.nLine D) V (GlobalTheory.RowShape.lineL D j : Set _) Λ (· = v) := by
  have hle : latO V (pLine D) Λ (GlobalTheory.RowShape.topL D : Set _) (· = v) ≤
      (latO (Model.nLine D) V (GlobalTheory.RowShape.lineL D j : Set _) Λ (· = v)).comap (AddMonoidHom.mk' (kap lastTau V) (kap_add' lastTau V)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, AddMonoidHom.mk'_apply]
    rw [kap_gen lastTau (c0 := -D.host.xi0) (fun _ _ => rfl)]
    refine line_mem _ (AA_le_lineId D j hj) Λ _ α hα hP s hs _ ?_
    have hx := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
    rw [show D.host.xi0⁻¹ * -D.host.xi0 = -1 by rw [mul_neg, inv_mul_cancel₀ hx], neg_one_mul]
    have ht' : t ∈ GlobalTheory.RowShape.latPi (pLine D) 1 := ht
    exact Submodule.neg_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) (Submodule.sum_mem _ fun l _ => mul_mem_AA ha (Submodule.mem_pi.1 ht' l (Set.mem_univ _)))
  exact fun w hw => hle hw

end GlobalTheory.LastLineLat

theorem GlobalTheory.LastLineLat.kap_lastTau_latO : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j, j + 2 = D.R.m → ∀ v, ∀ w ∈ latO (ch.G.V (.top (j + 1))) (pLine D) (ch.G.Λ (.top (j + 1)) : Set _) (GlobalTheory.RowShape.topL D : Set _) (· = v),
    GlobalTheory.FinPl.kap lastTau _ w ∈ latO (GlobalTheory.SeeSaw.Model.nLine D) (ch.G.V (.top (j + 1))) (GlobalTheory.RowShape.lineL D j : Set _) (ch.G.Λ (.top (j + 1)) : Set _) (· = v) := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R _ _ ch _ _ j hj v
  exact GlobalTheory.LastLineLat.kap_latO D _ _ j hj v
end
end

