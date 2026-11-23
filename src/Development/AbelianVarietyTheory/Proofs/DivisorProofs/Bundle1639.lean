module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
public import Formalism.PolynomialDimension.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSlopeSqLocalMatricesEqDeterminants
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0796
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0816
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0803
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0810
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1528
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0433
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulCutSubOneEntry
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1614
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeDualWeylFibreLatticeGe
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.FibSlope

section Log

variable {K : Type} [Field K] {φ : K → ℝ} (hφ : ∀ x y, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
include hφ

theorem log_one : φ 1 = 0 := by
  have := hφ 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at this
  linarith

theorem log_prod {ι : Type} (s : Finset ι) (f : ι → K) (hf : ∀ i, f i ≠ 0) :
    φ (∏ i ∈ s, f i) = ∑ i ∈ s, φ (f i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using log_one hφ
  | cons i s hi ih =>
    rw [Finset.prod_cons, Finset.sum_cons, hφ _ _ (hf i) (Finset.prod_ne_zero_iff.2 fun j _ => hf j), ih]

theorem log_pow {x : K} (hx : x ≠ 0) (n : ℕ) : φ (x ^ n) = n * φ x := by
  have := log_prod hφ (Finset.range n) (fun _ => x) fun _ => hx
  simpa using this

theorem log_det_rhoMat [CharZero K] {n : ℕ} {la : Fin n → ℕ} (hla : Antitone la) {g : Matrix (Fin n) (Fin n) K}
    (hg : g.det ≠ 0) : (rhoMat la g).det ≠ 0 ∧
      φ (rhoMat la g).det = (dim la : ℝ) * ((size la : ℝ) / (n : ℝ) * φ g.det) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Subsingleton.elim g 1, GlobalTheory.DefPt.Model.rhoMat_one, Matrix.det_one, log_one hφ]
    simp
  · have h := det_rhoMat_pow K n la hla g
    have h0 : (rhoMat la g).det ≠ 0 := fun h0 => by
      rw [h0, zero_pow hn.ne'] at h
      exact pow_ne_zero _ hg h.symm
    refine ⟨h0, ?_⟩
    have h1 := congrArg φ h
    rw [log_pow hφ h0, log_pow hφ hg] at h1
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    push_cast at h1
    field_simp
    linarith

theorem log_det_kron {T : Type} [Fintype T] [DecidableEq T] {J : T → Type} [∀ t, Fintype (J t)]
    [∀ t, DecidableEq (J t)] {c : K} (hc : c ≠ 0) (M : ∀ t, Matrix (J t) (J t) K) (hM : ∀ t, (M t).det ≠ 0)
    (r : T → ℝ) (hr : ∀ t, φ (M t).det = Fintype.card (J t) * r t) :
    (c • kron M).det ≠ 0 ∧ φ (c • kron M).det = Fintype.card (∀ t, J t) * (φ c + ∑ t, r t) := by
  have hk := (kronFamily_mul_one_det T J K M M).2.2
  have hp : ∀ t, (M t).det ^ (∏ s ∈ Finset.univ.erase t, Fintype.card (J s)) ≠ 0 := fun t => pow_ne_zero _ (hM t)
  have h0 : (kron M).det ≠ 0 := hk ▸ Finset.prod_ne_zero_iff.2 fun t _ => hp t
  rw [Matrix.det_smul]
  refine ⟨mul_ne_zero (pow_ne_zero _ hc) h0, ?_⟩
  rw [hφ _ _ (pow_ne_zero _ hc) h0, log_pow hφ hc, hk, log_prod hφ _ _ hp, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [log_pow hφ (hM t), hr, ← mul_assoc, ← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ t),
    Fintype.card_pi]

end Log

section Val

variable {K : Type} [Field K] [NumberField K]

theorem vAdd_mul_real (w : HeightOneSpectrum (𝓞 K)) (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    (vAdd w (x * y) : ℝ) = vAdd w x + vAdd w y := by
  have h1 : w.valuation K x ≠ 0 := by simpa using hx
  have h2 : w.valuation K y ≠ 0 := by simpa using hy
  rw [← Int.cast_add, vAdd, vAdd, vAdd, map_mul, WithZero.log_mul h1 h2, neg_add]

theorem valuation_det_le {ι : Type} [Fintype ι] [DecidableEq ι] (w : HeightOneSpectrum (𝓞 K)) {M : Matrix ι ι K}
    (hM : IntAt w M) : w.valuation K M.det ≤ 1 := by
  rw [Matrix.det_apply']
  refine Valuation.map_sum_le _ fun σ _ => ?_
  rw [map_mul, map_prod]
  refine mul_le_one' ?_ (Finset.prod_le_one' fun i _ => hM _ _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem finite_vAdd_det {ι : Type} [Fintype ι] [DecidableEq ι] {A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K}
    (hA : IsAdelic A) : (Function.support fun w => (vAdd w (A w).det : ℝ)).Finite := by
  refine hA.2.subset fun w hw h => hw ?_
  have h1 := valuation_det_le w h.1
  have h2 := valuation_det_le w h.2
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀] at h2
  have h0 : w.valuation K (A w).det ≠ 0 := by simpa using hA.1 w
  have h3 : w.valuation K (A w).det = 1 :=
    le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 h0)).1 h2)
  simp [vAdd, h3]

end Val

theorem log_norm_mul (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) : Real.log ‖x * y‖ = Real.log ‖x‖ + Real.log ‖y‖ := by
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy)]

variable {T : Type} [Fintype T] [DecidableEq T] {N : T → ℕ} {la : ∀ t, Fin (N t) → ℕ}

theorem vAdd_det_fibA {K : Type} [Field K] [NumberField K] (hla : ∀ t, Antitone (la t)) (w : HeightOneSpectrum (𝓞 K))
    {a : K} (ha : a ≠ 0) {B : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K} (hB : ∀ t, (B t).det ≠ 0) :
    (vAdd w (fibA la a B).det : ℝ) =
      Fintype.card (TIdx la) * (vAdd w a + ∑ t, (size (la t) : ℝ) / (N t : ℝ) * vAdd w (B t).det) :=
  (log_det_kron (φ := fun x => (vAdd w x : ℝ)) (vAdd_mul_real w) ha _
    (fun t => (log_det_rhoMat (φ := fun x => (vAdd w x : ℝ)) (vAdd_mul_real w) (hla t) (hB t)).1) _
    (fun t => by
      rw [← dim_eq_card]
      exact (log_det_rhoMat (φ := fun x => (vAdd w x : ℝ)) (vAdd_mul_real w) (hla t) (hB t)).2)).2

theorem log_det_fibY (hla : ∀ t, Antitone (la t)) {s : ℝ} (hs : 0 < s) {X : ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ}
    (hX : ∀ t, (X t).det ≠ 0) : (fibY la s X).det ≠ 0 ∧ Real.log ‖(fibY la s X).det‖ =
      Fintype.card (TIdx la) * (Real.log s + ∑ t, (Real.log ‖(onMat (la t)).det‖ / dim (la t) +
        (size (la t) : ℝ) / (N t : ℝ) * Real.log ‖(X t).det‖)) := by
  have hρ := fun t => log_det_rhoMat (φ := fun x : ℂ => Real.log ‖x‖) log_norm_mul (hla t) (hX t)
  have ho := fun t => (_root_.GlobalTheory.OnMatGram.norm_det_onMat_sq_le _ (la t) (hla t)).1
  have h := log_det_kron (φ := fun x : ℂ => Real.log ‖x‖) log_norm_mul (c := (s : ℂ))
    (Complex.ofReal_ne_zero.2 hs.ne') (fun t => onMat (la t) * rhoMat (la t) (X t))
    (fun t => by rw [Matrix.det_mul]; exact mul_ne_zero (ho t) (hρ t).1)
    (fun t => Real.log ‖(onMat (la t)).det‖ / dim (la t) + (size (la t) : ℝ) / (N t : ℝ) * Real.log ‖(X t).det‖)
    (fun t => by
      have hd : (dim (la t) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (dim_pos (hla t)).ne'
      have h2 := (hρ t).2
      rw [← dim_eq_card, Matrix.det_mul, log_norm_mul _ _ (ho t) (hρ t).1, h2, mul_add, mul_div_cancel₀ _ hd])
  simp only [Complex.norm_real, Real.norm_of_nonneg hs.le] at h
  exact h

theorem log_det_onMat_le {n : ℕ} {la : Fin n → ℕ} (hla : Antitone la) :
    Real.log ‖(onMat la).det‖ / dim la ≤ Real.log (dim la) / 2 := by
  obtain ⟨h0, h⟩ := _root_.GlobalTheory.OnMatGram.norm_det_onMat_sq_le _ la hla
  have hd : (0 : ℝ) < dim la := Nat.cast_pos.2 (dim_pos hla)
  have h1 := Real.log_le_log (pow_pos (norm_pos_iff.2 h0) 2) h
  rw [Real.log_pow, Real.log_pow] at h1
  rw [div_le_iff₀ hd]
  push_cast at h1
  linarith

theorem slope_fibre_ge : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ), (∀ t, Antitone (la t)) → ∀ (a : HeightOneSpectrum (𝓞 K) → K) (B : HeightOneSpectrum (𝓞 K) → ∀ t, Matrix (Fin (N t)) (Fin (N t)) K) (s : (K →+* ℂ) → ℝ) (X : (K →+* ℂ) → ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ), (∀ w, a w ≠ 0) → (Function.support fun w => vAdd w (a w)).Finite → (∀ t, IsAdelic fun w => B w t) → (∀ σ, 0 < s σ) → (∀ σ t, (X σ t).det ≠ 0) → (∀ σ, s ((starRingEnd ℂ).comp σ) = s σ) → (∀ σ t, ‖(X ((starRingEnd ℂ).comp σ) t).det‖ = ‖(X σ t).det‖) → (∀ σ, (fibY la (s σ) (X σ)).det ≠ 0) ∧ lineDeg s (fun w => (vAdd w (a w) : ℝ)) + ∑ t, ((size (la t) : ℝ) / (N t : ℝ) * detDeg (fun w => B w t) (fun σ => X σ t) - Real.log (dim (la t)) / 2) ≤ slope_sq (matNorm fun σ => fibY la (s σ) (X σ)) (locLat fun w => fibA la (a w) (B w)) / 2 := by
  intro K _ _ _ T _ _ N la hla a B s X ha hfa hB hs hX hsc hXc
  have hY := fun σ => log_det_fibY hla (hs σ) (hX σ)
  refine ⟨fun σ => (hY σ).1, ?_⟩
  have hD : 0 < Fintype.card (TIdx la) := by
    rw [Fintype.card_pi]
    exact Finset.prod_pos fun t _ => dim_eq_card (la t) ▸ dim_pos (hla t)
  haveI : Nonempty (TIdx la) := Fintype.card_pos_iff.1 hD
  have hD' : (Fintype.card (TIdx la) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hD.ne'
  have hK : (0 : ℝ) < finrank ℚ K := Nat.cast_pos.mpr finrank_pos
  rw [_root_.GlobalTheory.LocMatSlope.slope_sq_locLat K (TIdx la) _ _ (GlobalTheory.FibAdel.fibA_isAdelic K T N la a B ha hfa hB) (fun σ => (hY σ).1)
    (fun σ => Real.log_injOn_pos (norm_pos_iff.2 (hY _).1) (norm_pos_iff.2 (hY _).1) (by
      rw [(hY _).2, (hY _).2]; simp only [hsc, hXc]))]
  have hfa' : (Function.support fun w => (vAdd w (a w) : ℝ)).Finite := hfa.subset fun w hw h => hw (by
    simp only at h ⊢; rw [h, Int.cast_zero])
  have hfB := fun t => finite_vAdd_det (hB t)
  have hfin : ∑ᶠ w, (vAdd w (fibA la (a w) (B w)).det : ℝ) * lw K w = Fintype.card (TIdx la) *
      (∑ᶠ w, (vAdd w (a w) : ℝ) * lw K w +
        ∑ t, (size (la t) : ℝ) / (N t : ℝ) * ∑ᶠ w, (vAdd w (B w t).det : ℝ) * lw K w) := by
    have hsub : ∀ t, (Function.support fun w => (size (la t) : ℝ) / (N t : ℝ) *
        ((vAdd w (B w t).det : ℝ) * lw K w)).Finite := fun t =>
      (fin_mul (hfB t) (lw K)).subset (Function.support_mul_subset_right _ _)
    simp only [mul_finsum]
    rw [← finsum_sum_comm _ _ (fun t _ => hsub t), ← finsum_add_distrib (fin_mul hfa' _), mul_finsum]
    · refine finsum_congr fun w => ?_
      rw [vAdd_det_fibA hla w (ha w) (fun t => (hB t).1 w), mul_assoc, add_mul, Finset.sum_mul]
      simp only [mul_assoc]
    · exact (Set.finite_iUnion hsub).subset fun w hw => by
        by_contra hn
        simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at hn
        exact hw (Finset.sum_eq_zero fun t _ => hn t)
  have hinf : ∑ σ, Real.log ‖(fibY la (s σ) (X σ)).det‖ = Fintype.card (TIdx la) *
      (∑ σ, Real.log (s σ) + ∑ t, (finrank ℚ K * (Real.log ‖(onMat (la t)).det‖ / dim (la t)) +
        (size (la t) : ℝ) / (N t : ℝ) * ∑ σ, Real.log ‖(X σ t).det‖)) := by
    simp only [(hY _).2]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Embeddings.card, nsmul_eq_mul,
      Finset.mul_sum]
  simp only [detDeg, lineDeg]
  rw [hfin, hinf]
  have key : ∀ u v : ℝ, 2 * (Fintype.card (TIdx la) * u - Fintype.card (TIdx la) * v / finrank ℚ K) /
      (Fintype.card (TIdx la) : ℝ) / 2 = u - v / finrank ℚ K := fun u v => by field_simp
  rw [key, add_div, Finset.sum_div (ι := T)]
  have hle : ∑ t, ((size (la t) : ℝ) / (N t : ℝ) * ((∑ᶠ w, (vAdd w (B w t).det : ℝ) * lw K w) -
      (∑ σ, Real.log ‖(X σ t).det‖) / finrank ℚ K) - Real.log (dim (la t)) / 2) ≤
      ∑ t, ((size (la t) : ℝ) / (N t : ℝ) * ∑ᶠ w, (vAdd w (B w t).det : ℝ) * lw K w -
        (finrank ℚ K * (Real.log ‖(onMat (la t)).det‖ / dim (la t)) +
        (size (la t) : ℝ) / (N t : ℝ) * ∑ σ, Real.log ‖(X σ t).det‖) / finrank ℚ K) :=
    Finset.sum_le_sum fun t _ => by
      have := log_det_onMat_le (hla t)
      rw [add_div, mul_div_cancel_left₀ _ hK.ne', mul_sub, mul_div_assoc]
      linarith
  rw [Finset.sum_sub_distrib (f := fun t => (size (la t) : ℝ) / (N t : ℝ) * ∑ᶠ w, (vAdd w (B w t).det : ℝ) * lw K w)]
    at hle
  linarith

end GlobalTheory.FibSlope

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairSecondEqMovedBottomDatum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotFrames

theorem isThetaAt_stdSnd_move : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ (t : T) (g' : GA D A') (h : GA D WW) (x' y : (AE D)ˣ),
    Formalism.L2.Theta.SuppAt (Y.e t) A' g' → Formalism.IndefR.Lev.finE A' g' ∈ Formalism.L2.DIV.St Y.rA'.β →
    Formalism.L2.Theta.IsDetAt (Y.e t) A' g' x' →
    Formalism.L2.Theta.SuppAt (Y.e t) WW h → Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β → Formalism.L2.Theta.IsDetAt (Y.e t) WW h y →
    (∀ u : WO A' WW, IsHalf (cA D (Y.e t)) u →
      frMapAdj A' WW Y.rA'.β Y.rW.β (actO A' WW g' h u) = frMapAdj A' WW X.rA'.β X.rW.β u) →
    IsThetaAt W.ψ (symplO A' WW) (heisO W.ψ A' WW) (cA D (Y.e t))
      (latO A' WW X.rA'.Λ X.rW.Λ fun _ => True) 1 Y.vac'
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t) (Y.ideal (locPl G) t)
        A.rank A' WW X.rA'.β X.rW.β)
      (((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) • Y.ω' t (g'⁻¹, h⁻¹) (Y.f' t)) := by
  intro D T L sc G W i j A A' WW X Y hX hY t g' h x' y hS1 hSt1 hD1 hS2 hSt2 hD2 hfr
  have hi := hY.is
  have hW : IsWeilDatumO W.ψ A' WW (botAlpha L i j t) (botAlpha L i j t / botBeta G i j) (Y.ω' t) :=
    (GlobalTheory.Grid.isWeil_false _ _ _ _ _ _).1 (hi.weil' t)
  have hSA : IsSelfDualC A' Y.rA'.Λ := hi.rigA'.1
  have hSW : IsSelfDualC WW Y.rW.Λ := hi.rigW.1
  have hFA : Formalism.L2.DIV.IsFrame Y.rA'.β Y.rA'.Λ := hi.rigA'.2.1
  have hFW : Formalism.L2.DIV.IsFrame Y.rW.β Y.rW.Λ := hi.rigW.2.1
  have eA : X.rA'.Λ = Y.rA'.Λ := isStd_lat_eq hX.std' hY.std'
  have eW : X.rW.Λ = Y.rW.Λ := isStd_lat_eq hX.stdW hY.stdW
  rw [eA, eW]
  have hL := GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D A' WW Y.rA'.Λ Y.rW.Λ Y.rA'.β Y.rW.β hSA hSW hFA hFW g' h hSt1 hSt2
  have hvac := hi.isVac'
  have hIS := hi.idem t
  obtain ⟨ι, P, es, hsp, horth, hsum⟩ := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hIS
  have hc0 : Y.e t * cA D (Y.e t) = 0 := hIS.2
  have hes : ∀ k ∈ P, es k * Y.e t = es k := by
    intro k hk
    rw [hsum, Finset.mul_sum, Finset.sum_eq_single_of_mem k hk (fun b hb hne => horth k hk b hb hne)]
    exact (hsp k hk).1
  have hecs : ∀ a ∈ P, ∀ b ∈ P, es a * cA D (es b) = 0 := by
    intro a ha b hb
    have h2 : cA D (es b) * cA D (Y.e t) = cA D (es b) := by rw [← map_mul, hes b hb]
    rw [← hes a ha, ← h2]
    calc es a * Y.e t * (cA D (es b) * cA D (Y.e t)) = es a * cA D (es b) * (Y.e t * cA D (Y.e t)) := by ring
      _ = 0 := by rw [hc0, mul_zero]
  have h0 : Y.ω' t (g', h) Y.vac' =
      ((splitFacO (botAlpha L i j t) (botAlpha L i j t / botBeta G i j) x' y : Circle) : ℂ) • Y.vac' := by
    rw [hsum] at hS1 hS2 hD1 hD2
    exact GlobalTheory.WeilSplit.om_latVac_sum hW hSA hSW hvac.2.theta hvac.2.lat es P hsp horth hecs g' h hS1 hS2 hL x' y hD1 hD2
  have hos := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hIS).conj
  have hc : ((splitFacO (botAlpha L i j t) (botAlpha L i j t / botBeta G i j) x' y : Circle) : ℂ) ≠ 0 :=
    Circle.coe_ne_zero _
  have hΦ : (LinearMap.funLeft ℂ ℂ (actO A' WW g' h))
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (botAlpha L i j t / botBeta G i j) (Y.e t) (Y.ideal (locPl G) t) A.rank A' WW Y.rA'.β Y.rW.β) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (botAlpha L i j t / botBeta G i j) (Y.e t) (Y.ideal (locPl G) t) A.rank A' WW X.rA'.β X.rW.β := by
    funext u
    rw [LinearMap.funLeft_apply]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd
    by_cases hu : IsHalf (cA D (Y.e t)) u
    · have hd : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW Y.rA'.β Y.rW.β (actO A' WW g' h u) =
          GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW X.rA'.β X.rW.β u := by
        unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord
        rw [hfr u hu]
      rw [hd, GlobalTheory.SchrMove.isHalf_actO_iff]
    · rw [if_neg, if_neg]
      · exact fun hh => hu hh.1
      · exact fun hh => hu ((GlobalTheory.SchrMove.isHalf_actO_iff g' h u).1 hh.1)
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hi.snd t
  refine ⟨⟨T₀, hT₀⟩, fun T' hT' => ?_⟩
  have th1 := GlobalTheory.SchrTheta.isTheta_placeModel D W.ψ hW.std A' WW Y.rA'.Λ Y.rW.Λ hSA hSW (cA D (Y.e t)) hos.idem
    hos.infPart_eq Y.vac' hvac.2.theta T' hT'
  have pm := GlobalTheory.SchrMove.isPlaceModel_move hW hL hT' th1 hc h0
  have hf' := hall _ pm
  have omm : ∀ p q (F : WO A' WW → ℂ), Y.ω' t p (Y.ω' t q F) = Y.ω' t (p * q) F := fun p q F => by
    rw [map_mul]; rfl
  show _ = T' _
  rw [← hΦ, hf']
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [omm, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one]
  rfl

end GlobalTheory.BotFrames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableSchwartzOfSummableSeminorms
section
open MeasureTheory Filter Topology

namespace GlobalTheory.ConvSeries

theorem seminorm_finset_sum_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Seminorm ℂ (SchwartzMap E ℂ)) (u : Finset ℕ) (t : ℕ → SchwartzMap E ℂ) :
    p (∑ j ∈ u, t j) ≤ ∑ j ∈ u, p (t j) := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert a u ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (map_add_le_add p _ _).trans (by gcongr)

theorem summable_of_summable_seminorm (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : ℕ → SchwartzMap E ℂ)
    (h : ∀ k n, Summable (fun j => SchwartzMap.seminorm ℂ k n (t j))) : Summable t := by
  classical
  have iteratedFDeriv_sub' (f g : (SchwartzMap E ℂ)) (n : ℕ) (x : E) :
      iteratedFDeriv ℝ n (⇑(f - g)) x = iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n g x := by
    have hf : ContDiff ℝ n f := f.smooth n
    have hg : ContDiff ℝ n g := g.smooth n
    rw [show (⇑(f - g) : E → ℂ) = ⇑f - ⇑g from rfl]
    exact iteratedFDeriv_sub_apply hf.contDiffAt hg.contDiffAt
  
  have cauchy_seminorm {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (k n : ℕ) {ε : ℝ} (hε : 0 < ε) :
      ∃ N, ∀ a ≥ N, ∀ b ≥ N, SchwartzMap.seminorm ℝ k n (u a - u b) < ε := by
    rw [cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero, tendsto_comap_iff] at hu
    have h := ((schwartz_withSeminorms ℝ E ℂ).tendsto_nhds _ 0).1 hu (k, n) ε hε
    obtain ⟨⟨N₁, N₂⟩, hN⟩ := eventually_atTop.1 h
    refine ⟨max N₁ N₂, fun a ha b hb => ?_⟩
    have := hN (b, a) (Prod.mk_le_mk.2 ⟨le_of_max_le_left hb, le_of_max_le_right ha⟩)
    simpa [schwartzSeminormFamily] using this
  
  let limD (u : ℕ → (SchwartzMap E ℂ)) (n : ℕ) (x : E) :
      ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ :=
    limUnder atTop fun j => iteratedFDeriv ℝ n (u j) x
  
  have tendsto_limD {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (n : ℕ) (x : E) :
      Tendsto (fun j => iteratedFDeriv ℝ n (u j) x) atTop (𝓝 (limD u n x)) := by
    refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ?_)
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := cauchy_seminorm hu 0 n hε
    refine ⟨N, fun a ha b hb => ?_⟩
    rw [dist_eq_norm, ← iteratedFDeriv_sub']
    have := SchwartzMap.le_seminorm ℝ 0 n (u a - u b) x
    simp only [pow_zero, one_mul] at this
    exact this.trans_lt (hN a ha b hb)
  
  have key {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (k n : ℕ) {ε : ℝ} (hε : 0 < ε) :
      ∃ N, ∀ j ≥ N, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u j) x - limD u n x‖ ≤ ε := by
    obtain ⟨N, hN⟩ := cauchy_seminorm hu k n hε
    refine ⟨N, fun j hj x => ?_⟩
    have ht : Tendsto (fun b => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u j) x - iteratedFDeriv ℝ n (u b) x‖)
        atTop (𝓝 (‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u j) x - limD u n x‖)) :=
      ((tendsto_const_nhds.sub (tendsto_limD hu n x)).norm).const_mul _
    refine le_of_tendsto ht (eventually_atTop.2 ⟨N, fun b hb => ?_⟩)
    rw [← iteratedFDeriv_sub']
    exact (SchwartzMap.le_seminorm ℝ k n (u j - u b) x).trans (hN j hj b hb).le
  
  have tendstoUniformly_limD {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (n : ℕ) :
      TendstoUniformly (fun j => iteratedFDeriv ℝ n (u j)) (limD u n) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := key hu 0 n (half_pos hε)
    refine eventually_atTop.2 ⟨N, fun j hj x => ?_⟩
    have := hN j hj x
    rw [pow_zero, one_mul] at this
    rw [dist_eq_norm, norm_sub_rev]
    linarith
  
  have continuous_limD {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (n : ℕ) :
      Continuous (limD u n) :=
    (tendstoUniformly_limD hu n).continuous (Eventually.of_forall (f := atTop) fun j =>
      ((u j).smooth ⊤).continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).frequently
  
  have hasFDerivAt_limD {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (m : ℕ) (x : E) :
      HasFDerivAt (limD u m) ((limD u (m + 1) x).curryLeft) x := by
    refine hasFDerivAt_of_tendstoUniformly (f := fun j => iteratedFDeriv ℝ m (u j))
      (f' := fun j y => fderiv ℝ (iteratedFDeriv ℝ m (⇑(u j))) y)
      (g' := fun y => (limD u (m + 1) y).curryLeft) ?_ ?_ (fun y => tendsto_limD hu m y) x
    · exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) ℂ).isometry.uniformContinuous.comp_tendstoUniformly
        (tendstoUniformly_limD hu (m + 1))
    · intro j y
      exact ((((u j).smooth ⊤).differentiable_iteratedFDeriv
        (by exact_mod_cast WithTop.coe_lt_top (m : ℕ))) y).hasFDerivAt
  
  have hasFTaylorSeries {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) :
      HasFTaylorSeriesUpTo ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (limD u 0 x).curry0)
        (fun x => (fun m => limD u m x : FormalMultilinearSeries ℝ E ℂ)) := by
    exact { zero_eq := fun _ => rfl
            fderiv := fun m _ x => hasFDerivAt_limD hu m x
            cont := fun m _ => continuous_limD hu m }
  
  let limMap (u : ℕ → (SchwartzMap E ℂ)) (hu : CauchySeq u) : (SchwartzMap E ℂ) := by
    refine { toFun := fun x => (limD u 0 x).curry0
             smooth' := (hasFTaylorSeries hu).contDiff
             decay' := ?_ }
    intro k n
    obtain ⟨N, hN⟩ := key hu k n one_pos
    refine ⟨SchwartzMap.seminorm ℝ k n (u N) + 1, fun x => ?_⟩
    rw [← (hasFTaylorSeries hu).eq_iteratedFDeriv (m := n) (by exact_mod_cast le_top) x]
    have h1 := hN N le_rfl x
    have h2 := SchwartzMap.le_seminorm ℝ k n (u N) x
    have h3 : ‖limD u n x‖ ≤ ‖iteratedFDeriv ℝ n (u N) x‖ + ‖iteratedFDeriv ℝ n (u N) x - limD u n x‖ := by
      have := norm_sub_le (iteratedFDeriv ℝ n (u N) x) (iteratedFDeriv ℝ n (u N) x - limD u n x)
      simpa using this
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ ‖x‖ ^ k)
    change ‖x‖ ^ k * ‖limD u n x‖ ≤ _
    rw [mul_add] at h4
    linarith

  have iteratedFDeriv_limMap {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (n : ℕ) (x : E) :
      iteratedFDeriv ℝ n (limMap u hu) x = limD u n x :=
    ((hasFTaylorSeries hu).eq_iteratedFDeriv (m := n) (by exact_mod_cast le_top) x).symm
  
  have tendsto_limMap {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) :
      Tendsto u atTop (𝓝 (limMap u hu)) := by
    rw [(schwartz_withSeminorms ℝ E ℂ).tendsto_nhds]
    rintro ⟨k, n⟩ ε hε
    obtain ⟨N, hN⟩ := key hu k n (half_pos hε)
    refine eventually_atTop.2 ⟨N, fun j hj => ?_⟩
    refine lt_of_le_of_lt ?_ (half_lt_self hε)
    refine SchwartzMap.seminorm_le_bound ℝ k n _ (half_pos hε).le fun x => ?_
    rw [iteratedFDeriv_sub', iteratedFDeriv_limMap hu]
    exact hN j hj x
  
  haveI : CompleteSpace (SchwartzMap E ℂ) := by
    haveI : (uniformity (SchwartzMap E ℂ)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
    exact UniformSpace.complete_of_cauchySeq_tendsto fun u hu => ⟨limMap u hu, tendsto_limMap hu⟩
  rw [summable_iff_vanishing]
  intro U hU
  obtain ⟨s, r, hr, hsub⟩ := (schwartz_withSeminorms ℂ E ℂ).mem_nhds_iff 0 U |>.1 hU
  have hr' : 0 < r / 2 := half_pos hr
  have hS : ∀ i : ℕ × ℕ, ∃ S : Finset ℕ, ∀ u : Finset ℕ, Disjoint u S →
      ∑ j ∈ u, SchwartzMap.seminorm ℂ i.1 i.2 (t j) ∈ Set.Iio (r / 2) :=
    fun i => summable_iff_vanishing.1 (h i.1 i.2) _ (Iio_mem_nhds (by simpa using hr'))
  choose S hS using hS
  refine ⟨s.biUnion S, fun u hu => hsub ?_⟩
  rw [Seminorm.mem_ball_zero]
  refine lt_of_le_of_lt (Seminorm.finset_sup_apply_le hr'.le fun i hi => ?_) (half_lt_self hr)
  refine (seminorm_finset_sum_le _ u t).trans ?_
  exact (hS i u (Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem S hi) hu)).le

end GlobalTheory.ConvSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceHermitianTensorIntegralOfCharTrivialStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_hermitianTensor_integral_of_char_trivial : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (ψ : AddChar (AF F) ℂ) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl (F := F)), PsiUnr ψ v →
    ∀ X₀ : Matrix (Fin n) (Fin d) E, (∀ γ ∈ latAtV X Y v,
      ψ (symp (cA σ) (-1) (incM F X.J) (incM F Y.J) (GlobalTheory.EmbChart.atPlace v 1 • incM F X₀) γ) = 1) →
    ∀ x ∈ X.L, ∀ y ∈ Y.L, algebraMap F (Fv F v) (Algebra.trace F E (-GlobalTheory.WeilM.hTens σ X.J Y.J X₀ (Matrix.vecMulVec x y)))
      ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.KFinLoc.trace_hTens_integral_of_char | exact GlobalTheory.KFinLoc.trace_hTens_integral_of_char | (intros; apply GlobalTheory.KFinLoc.trace_hTens_integral_of_char <;> assumption)
end

