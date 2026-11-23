module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0482
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0528
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1735
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0817
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0531

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiVertexLatticeSplitsAlongWittAtPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.MonoJac

variable {D : D7}

open GlobalTheory.SeeSaw.SplitLat (colProj colProj_mulVec colMul_rat rat_mulVec_mem_latV mulVec_eq_sum_colMul)

theorem monoAt_of_proj {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀)
    (hX : ∀ i : Fin ρ, ∀ x ∈ L, colProj d.qX d.e i *ᵥ x ∈ L)
    (hY : ∀ i : Fin ρ, ∀ x ∈ L, colProj d.qY d.e' i *ᵥ x ∈ L)
    (h0 : ∀ x ∈ L, d.q0 *ᵥ x ∈ L₀) (hi : ∀ x ∈ L₀, d.i₀ *ᵥ x ∈ L) (v : GlobalTheory.FinPl.Pl D) :
    MonoAt d L L₀ v := by
  intro y
  constructor
  · intro hy
    refine ⟨fun i => ?_, fun i => ?_, ?_⟩
    · change GlobalTheory.FinPl.colMul (rat d.e) i ((rat d.qX *ᵥ y) i) ∈ _
      rw [colMul_rat]
      exact rat_mulVec_mem_latV _ (hX i) _ hy
    · change GlobalTheory.FinPl.colMul (rat d.e') i ((rat d.qY *ᵥ y) i) ∈ _
      rw [colMul_rat]
      exact rat_mulVec_mem_latV _ (hY i) _ hy
    · exact rat_mulVec_mem_latV d.q0 h0 _ hy
  · rintro ⟨h1, h3, h2⟩
    have hrat : d.e * d.qX + d.i₀ * d.q0 + d.e' * d.qY = 1 := by
      have h : fromRows (fromRows d.qX d.q0) d.qY * fromCols (fromCols d.e d.i₀) d.e' = 1 := by
        rw [fromRows_mul_fromCols, fromRows_mul_fromCols, fromRows_mul, mul_fromCols,
          GlobalTheory.SeeSaw.SplitLat.qX_e, GlobalTheory.SeeSaw.SplitLat.qX_i₀,
          GlobalTheory.SeeSaw.SplitLat.qX_e', GlobalTheory.SeeSaw.SplitLat.qY_e,
          GlobalTheory.SeeSaw.SplitLat.qY_i₀, GlobalTheory.SeeSaw.SplitLat.qY_e',
          GlobalTheory.SeeSaw.SplitLat.wittDecomposition_coreProj_mul_e_eq_zero,
          GlobalTheory.SeeSaw.SplitLat.wittDecomposition_coreProj_mul_core_eq_one,
          GlobalTheory.SeeSaw.SplitLat.wittZeroProjection_mul_dualBasis_eq_zero,
          fromBlocks_one, fromRows_zero, fromCols_zero, fromBlocks_one]
      rw [← fromCols_mul_fromRows, ← fromCols_mul_fromRows]
      exact (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [← d.rank_add]; ring)).1 h
    have hsum : d.jX * d.pX + d.j0 * d.p0 + d.jY * d.pY = 1 := by
      have h := congrArg rat hrat
      change (d.e * d.qX + d.i₀ * d.q0 + d.e' * d.qY).map (incA D) = (1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E).map (incA D) at h
      rw [Matrix.map_add _ (map_add (incA D)), Matrix.map_add _ (map_add (incA D)),
        Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_one] at h
      · exact h
      · exact map_zero (incA D)
      · exact map_one (incA D)
    have e : y = d.jX *ᵥ (d.pX *ᵥ y) + d.j0 *ᵥ (d.p0 *ᵥ y) + d.jY *ᵥ (d.pY *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
        hsum, Matrix.one_mulVec]
    rw [e, mulVec_eq_sum_colMul d.jX, mulVec_eq_sum_colMul d.jY]
    refine add_mem (add_mem (sum_mem fun i _ => h1 i) ?_) (sum_mem fun i _ => h3 i)
    exact rat_mulVec_mem_latV d.i₀ hi _ h2

open GlobalTheory.SeeSaw.SplitLat (colProj)

theorem sumLat_map {n k c : ℕ} {M : Matrix (Fin n) (Fin k) D.host.E} {Λ : Submodule (𝓞 D.host.E) (Fin k → D.host.E)}
    {a : Matrix (Fin n) (Fin c) D.host.E} {𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}
    (N : Matrix (Fin n) (Fin n) D.host.E) (w : Fin c → D.host.E) (hM : N * M = 0) (ha : N * a = a * Matrix.diagonal w)
    (hw : ∀ p, w p = 0 ∨ w p = 1) : ∀ x ∈ sumLat M Λ a 𝔟, N *ᵥ x ∈ sumLat M Λ a 𝔟 := by
  rintro _ ⟨y, -, u, hu, rfl⟩
  refine ⟨0, Λ.zero_mem, Matrix.diagonal w *ᵥ u, fun p => ?_, ?_⟩
  · rw [Matrix.mulVec_diagonal]
    rcases hw p with h | h
    · rw [h, zero_mul]; exact (𝔟 p).zero_mem
    · rw [h, one_mul]; exact hu p
  · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM, ha, ← Matrix.mulVec_mulVec,
      Matrix.zero_mulVec, Matrix.mulVec_zero, zero_add]

theorem sumLat_proj {n k c : ℕ} {M : Matrix (Fin n) (Fin k) D.host.E} {Λ : Submodule (𝓞 D.host.E) (Fin k → D.host.E)}
    {a : Matrix (Fin n) (Fin c) D.host.E} {𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}
    (q : Matrix (Fin k) (Fin n) D.host.E) (hM : q * M = 1) (ha : q * a = 0) : ∀ x ∈ sumLat M Λ a 𝔟, q *ᵥ x ∈ Λ := by
  rintro _ ⟨y, hy, u, -, rfl⟩
  rwa [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM, ha, Matrix.one_mulVec, Matrix.zero_mulVec,
    add_zero]

theorem mem_sumLat_of {n k c : ℕ} {M : Matrix (Fin n) (Fin k) D.host.E} {Λ : Submodule (𝓞 D.host.E) (Fin k → D.host.E)}
    {a : Matrix (Fin n) (Fin c) D.host.E} {𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {y : Fin k → D.host.E}
    (hy : y ∈ Λ) : M *ᵥ y ∈ sumLat M Λ a 𝔟 :=
  ⟨y, hy, 0, fun p => (𝔟 p).zero_mem, by rw [Matrix.mulVec_zero, add_zero]⟩

theorem colProj_mul {S : HSp D} {ρ m l : ℕ} (q : Matrix (Fin ρ) (Fin m) D.host.E) (f : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (i : Fin ρ) (N : Matrix (Fin m) (Fin l) D.host.E) : colProj (S := S) q f i * N = colProj (S := S) (q * N) f i := by
  ext k j
  simp only [colProj, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, mul_assoc]

theorem colProj_zero {S : HSp D} {ρ m : ℕ} (f : Matrix (Fin S.rank) (Fin ρ) D.host.E) (i : Fin ρ) :
    colProj (S := S) (0 : Matrix (Fin ρ) (Fin m) D.host.E) f i = 0 := by
  ext k j
  simp [colProj]

section SlopeTestRemainingChoices

variable {A B : HSp D} {c ρ : ℕ}

def cfE (c : ℕ) : Matrix (Fin ρ) (Fin c) D.host.E := fun p q => if p.1 = q.1 then ((-D.host.xi0) ^ (p.1 + 1))⁻¹ else 0

def cfE' (c : ℕ) (s : Fin ρ → D.host.E) : Matrix (Fin ρ) (Fin c) D.host.E := fun p q => if q.1 + p.1 + 1 = c then (s p)⁻¹ else 0

theorem eq_idempotent_mul_add_of_mul_sub_eq {n : ℕ} (a : Matrix (Fin n) (Fin c) D.host.E) (hc : c = 2 * ρ) (h : ρ ≤ c) (s : Fin ρ → D.host.E)
    (hs : ∀ p, s p ≠ 0) :
    a = (colsOf a (Fin.castLE h) (fun p : Fin ρ => (-D.host.xi0) ^ (p.1 + 1)) : Matrix (Fin n) (Fin ρ) D.host.E) *
        (cfE c : Matrix (Fin ρ) (Fin c) D.host.E) +
      (colsOf a (fun p : Fin ρ => (Fin.castLE h p : Fin c).rev) s : Matrix (Fin n) (Fin ρ) D.host.E) *
        (cfE' c s : Matrix (Fin ρ) (Fin c) D.host.E) := by
  have hx : ∀ p : ℕ, ((-D.host.xi0) ^ (p + 1)) ≠ 0 := fun p => pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)
  refine Matrix.ext fun k q => ?_
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [colsOf, cfE, cfE']
  by_cases hq : q.1 < ρ
  · rw [Finset.sum_eq_single ⟨q.1, hq⟩, Finset.sum_eq_zero]
    · rw [if_pos rfl, add_zero, show (Fin.castLE h ⟨q.1, hq⟩ : Fin c) = q from Fin.ext rfl, mul_comm,
        ← mul_assoc, inv_mul_cancel₀ (hx _), one_mul]
    · intro p _
      rw [if_neg (by omega), mul_zero]
    · intro p _ hp
      rw [if_neg (fun e => hp (Fin.ext e)), mul_zero]
    · intro hn; exact absurd (Finset.mem_univ _) hn
  · have hp' : c - 1 - q.1 < ρ := by have := q.2; omega
    rw [Finset.sum_eq_zero, Finset.sum_eq_single ⟨c - 1 - q.1, hp'⟩]
    · rw [if_pos (by have := q.2; simp only [Fin.val_mk]; omega), zero_add,
        show ((Fin.castLE h ⟨c - 1 - q.1, hp'⟩ : Fin c).rev) = q from Fin.ext (by simp [Fin.val_rev]; omega),
        mul_comm, ← mul_assoc, inv_mul_cancel₀ (hs _), one_mul]
    · intro p _ hp
      rw [if_neg (fun e => hp (Fin.ext (show p.1 = c - 1 - q.1 by omega))), mul_zero]
    · intro hn; exact absurd (Finset.mem_univ _) hn
    · intro p _
      rw [if_neg (by have := p.2; omega), mul_zero]

end SlopeTestRemainingChoices

open GlobalTheory.SeeSaw.SplitLat (colProj)

theorem auxiliaryLattice_splitsAlongWitt_at_place {A B : HSp D} {c ρ : ℕ} (t : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B A ρ) (hc : c = 2 * ρ)
    (hh : IsAuxiliaryVectorWittDec t d) (hi : d.i₀ = frameMat B A t.ι) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (v : GlobalTheory.FinPl.Pl D) : MonoAt d (t.lat Λ 𝔟) Λ v := by
  obtain ⟨h2, he, s, he'⟩ := hh
  have hρ : ρ ≤ c := by omega
  have hx : ∀ p : ℕ, ((-D.host.xi0) ^ (p + 1)) ≠ 0 := fun p => pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)
  have hs : ∀ p, s p ≠ 0 := by
    intro p hp
    have h1 := congrFun (congrFun d.e'e p) p
    rw [Matrix.one_apply_eq] at h1
    have hcol : ∀ k, d.e' k p = 0 := fun k => by rw [he']; simp [colsOf, hp]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hcol] at h1
  have ha := eq_idempotent_mul_add_of_mul_sub_eq t.a hc hρ s hs
  rw [← he, ← he'] at ha
  have hX : d.qX * t.a = cfE c := by
    rw [ha, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.SeeSaw.SplitLat.qX_e, GlobalTheory.SeeSaw.SplitLat.qX_e',
      Matrix.one_mul, Matrix.zero_mul, add_zero]
  have hY : d.qY * t.a = cfE' c s := by
    rw [ha, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.SeeSaw.SplitLat.qY_e, GlobalTheory.SeeSaw.SplitLat.qY_e',
      Matrix.one_mul, Matrix.zero_mul, zero_add]
  have h0 : d.q0 * t.a = 0 := by
    rw [ha, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.SeeSaw.SplitLat.wittDecomposition_coreProj_mul_e_eq_zero, GlobalTheory.SeeSaw.SplitLat.wittZeroProjection_mul_dualBasis_eq_zero,
      Matrix.zero_mul, Matrix.zero_mul, add_zero]
  refine monoAt_of_proj d _ _ (fun i => ?_) (fun i => ?_) ?_ ?_ v
  · refine sumLat_map _ (Pi.single (Fin.castLE hρ i) 1) ?_ ?_ ?_
    · rw [colProj_mul, ← hi, GlobalTheory.SeeSaw.SplitLat.qX_i₀, colProj_zero]
    · rw [colProj_mul, hX]
      refine Matrix.ext fun k q => ?_
      rw [Matrix.mul_diagonal, he]
      simp only [colProj, Matrix.of_apply, colsOf, cfE]
      by_cases hq : i.1 = q.1
      · have e : (Fin.castLE hρ i : Fin c) = q := Fin.ext hq
        subst e
        rw [if_pos hq, Pi.single_eq_same, mul_one, mul_comm ((-D.host.xi0) ^ _), mul_assoc, mul_inv_cancel₀ (hx _),
          mul_one]
      · have e : q ≠ (Fin.castLE hρ i : Fin c) := fun e => hq (by rw [e]; rfl)
        rw [if_neg hq, mul_zero, Pi.single_apply, if_neg e, mul_zero]
    · intro p
      rw [Pi.single_apply]
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
  · refine sumLat_map _ (Pi.single (Fin.castLE hρ i : Fin c).rev 1) ?_ ?_ ?_
    · rw [colProj_mul, ← hi, GlobalTheory.SeeSaw.SplitLat.qY_i₀, colProj_zero]
    · rw [colProj_mul, hY]
      refine Matrix.ext fun k q => ?_
      rw [Matrix.mul_diagonal, he']
      simp only [colProj, Matrix.of_apply, colsOf, cfE']
      by_cases hq : q.1 + i.1 + 1 = c
      · have e : (Fin.castLE hρ i : Fin c).rev = q := Fin.ext (by simp [Fin.val_rev]; omega)
        subst e
        rw [if_pos hq, Pi.single_eq_same, mul_one, mul_comm (s i), mul_assoc, mul_inv_cancel₀ (hs _), mul_one]
      · have e : q ≠ (Fin.castLE hρ i : Fin c).rev := fun e => hq (by rw [e]; simp [Fin.val_rev]; omega)
        rw [if_neg hq, mul_zero, Pi.single_apply, if_neg e, mul_zero]
    · intro p
      rw [Pi.single_apply]
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
  · exact sumLat_proj d.q0 (by rw [← hi]; exact GlobalTheory.SeeSaw.SplitLat.wittDecomposition_coreProj_mul_core_eq_one d) h0
  · intro x hx
    rw [hi]
    exact mem_sumLat_of hx

theorem monoAt_jac : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Frames G), Std F →
    ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D),
      MonoAt (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v := by
  intro D T L sc G F hF ρ h v
  have H := auxiliaryLattice_splitsAlongWitt_at_place (G.colDec (2 * ρ + 1) (by omega) (by omega)) (F.dJ ρ h) (by omega) (hF.hJ ρ h) (hF.aJ ρ h)
    (G.Λ (.core (2 * ρ + 1))) (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) v
  rw [← G.sp.colLat (2 * ρ + 1) (by omega) (by omega)] at H
  exact H

end GlobalTheory.AscFin.MonoJac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergDerivativeRealPlacePureDatum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section

namespace GlobalTheory.HeisLineTransfer

theorem schr_schr_apply {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (Φ : (κ → R) → ℂ) (x : κ → R) :
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.schr ψ w' Φ) x =
      ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) * GlobalTheory.WeilM.schr ψ (w + w') Φ x := by
  simp only [GlobalTheory.WeilM.schr, ← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc]
  congr 2
  simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  rw [dotProduct_comm w'.1 w.2]
  first
    | linear_combination (w.1 ⬝ᵥ w'.2) * invOf_mul_self (2 : R)
    | linear_combination (-(w.1 ⬝ᵥ w'.2)) * invOf_mul_self (2 : R)

end GlobalTheory.HeisLineTransfer

namespace GlobalTheory.HeisLineTransfer


set_option maxHeartbeats 1600000 in
theorem isDatum_dRho_heisO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        ∀ f : WO S X → ℂ, IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) f →
        ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ) (g₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (M.heisLine Bs.ψ (cS.symm (lineAt θ τ z 1))) g g₁ →
          IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ) (dRho (heisO ψ (sgn ε S) X) θ τ z f) := by
  intro D ψ θ hθ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hc g φ hφ hvac f hf τ z g₁ hact
  subst hψ
  obtain ⟨hΦ, hfΦ⟩ := hf
  have hF : IsTotallyReal D.host.F := hBs.cm.1
  have hψc : IsCharAF D.host.F Bs.ψ := GlobalTheory.StdCharFromIsStd.isCharAF hBs.std
  have hstd : ∀ᶠ v in Filter.cofinite, φ v =
      Set.indicator {x : Fin S.rank × Fin d → v.adicCompletion D.host.F | ∀ i, x i ∈ v.adicCompletionIntegers D.host.F} 1 :=
    (hvac.and hM.std).mono fun v h => h.1.trans h.2
  have h1 := GlobalTheory.TensUniq.pure_mem_schA g₁ φ hφ hstd
  refine ⟨h1, fun u => ?_⟩

  obtain ⟨G, hGdef⟩ : ∃ G : Matrix (Fin S.rank) (Fin S.rank) D.host.E,
    (if ε then -1 else 1 : D.host.E) • S.gram = G := ⟨_, rfl⟩
  rw [hGdef] at hc
  have hs : (sgn ε S).gram = G := by
    rw [← hGdef]
    cases ε
    · ext i j; simp [sgn, HSpace.gram]
    · ext i j; simp [HSpace.gram]
  have hVJ : Vs.J = -G := by
    rw [hJ, ← hGdef]; cases ε <;> simp
  have hdet : IsUnit G.det := by rw [← hs]; exact (Formalism.L2.Theta.gram_det_ne (sgn ε S)).isUnit
  have hHG : (G⁻¹).map (incA D) * G.map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hG : (G.map (incA D)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = (G.map (incA D))ᵀ := by
    ext i j
    have h := hV.herm j i
    rw [hVJ, Matrix.neg_apply, Matrix.neg_apply, map_neg, neg_inj] at h
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig (incA D (G i j)) = incA D (G j i)
    rw [← h]
    rfl
  obtain ⟨co, hco⟩ := GlobalTheory.SquareAgree.exists_darboux_transpose_mul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) e
    (X.gram.map (incA D)) (incA D D.host.xi0) hHG hG (JV := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J)
    (JW := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) (JA := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
    (JB := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (sgn ε S).gram⁻¹))
    (by rw [hVJ]; exact Matrix.map_neg _ (map_neg (incA D)) _) (by rw [hJW]; exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) rfl
    (by rw [hs]; exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) M.co cS hc
  have hform : ∀ w w' : Matrix (Fin S.rank) (Fin d) (AE D), symplO (sgn ε S) X (cS w) (cS w') =
      (M.co.e w).1 ⬝ᵥ (M.co.e w').2 - (M.co.e w').1 ⬝ᵥ (M.co.e w).2 := by
    intro w w'
    rw [← GlobalTheory.WeilSchrodinger.symp_eq_symplO D (sgn ε S) X X.gramᵀ (D.host.xi0 • (sgn ε S).gram⁻¹) 1 rfl
      (one_smul _ _), co.form, hco, hco]

  obtain ⟨hline, -⟩ := GlobalTheory.LineRealAd.lineAt_realAd_smul D θ hθ τ z
  set u₀ := cS.symm (lineAt θ τ z 1) with hu₀
  have hcs : ∀ (a : AF D.host.F) (v : Matrix (Fin S.rank) (Fin d) (AE D)), cS (a • v) = a • cS v := by
    intro a v
    rw [hc, hc, ← Matrix.smul_mul]
    rfl
  have hL : ∀ t : ℝ, lineAt θ τ z t = cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) := by
    intro t
    rw [hcs, hu₀, AddEquiv.apply_symm_apply, hline]
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) = ⅟(2 : AF D.host.F) :=
    (invOf_eq_right_inv (by rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]; norm_num)).symm

  have hkey : ∀ t : ℝ, heisO Bs.ψ (sgn ε S) X (lineAt θ τ z t) f (cS u) =
      GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ u
        (M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ))) := by
    intro t
    set u' := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀
    have e1 : ∀ x, M.co.rho Bs.ψ u (M.co.rho Bs.ψ u' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) x =
        Bs.ψ (⅟(2 : AF D.host.F) * ((M.co.e u).1 ⬝ᵥ (M.co.e u').2 - (M.co.e u').1 ⬝ᵥ (M.co.e u).2)) *
          M.co.rho Bs.ψ (u + u') (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) x := by
      intro x
      simp only [GlobalTheory.WeilM.Darboux.rho, map_add (f := _)]
      exact schr_schr_apply Bs.ψ _ _ _ x
    rw [hL t]
    simp only [heisO]
    rw [← map_add (f := _), ← hfΦ (u + u')]
    simp only [GlobalTheory.WeilM.thetaSum, e1, tsum_mul_left]
    rw [symplOH, hform, h2]

  have hd : ∀ x, HasDerivAt
      (fun t : ℝ => M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) x)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ x) 0 :=
    fun x => hact _ (GlobalTheory.ThK.EvUniqInf.rest_pure g φ hφ hstd) x
  have hder : HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum D.host.F
      (M.co.rho Bs.ψ u (M.co.rho Bs.ψ
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ))))
      (GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ u
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ))) 0 := by
    simp only [GlobalTheory.WeilM.Darboux.rho, map_smul] at hd ⊢
    exact GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_schr Bs.ψ hF hψc (M.co.e u₀) hΦ h1 hd (M.co.e u)
  show GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ u (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ)) =
    Formalism.IndefR.Datum.dRho (heisO Bs.ψ (sgn ε S) X) θ τ z f (cS u)
  have hfun : (fun t : ℝ => heisO Bs.ψ (sgn ε S) X (lineAt θ τ z t) f (cS u)) = fun t : ℝ =>
      GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ u
        (M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ))) := funext hkey
  unfold Formalism.IndefR.Datum.dRho
  rw [hfun]
  exact hder.deriv.symm

end GlobalTheory.HeisLineTransfer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatPtSLeClosureAndSelfDual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.SmallDatLat

theorem latPtS_le_closure_and_selfDual : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j),
    Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram → Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e → ∀ v : Pl D.host.F,
      GlobalTheory.SmallDat.latPtS t e v ≤ AddSubgroup.closure (GlobalTheory.SmallDat.genPtS t e v) ∧
      ∀ z : GlobalTheory.SmallDat.PtS G i j, At (evFin D.host.F v) z → (z ∈ GlobalTheory.SmallDat.latPtS t e v ↔ ∀ γ ∈ GlobalTheory.SmallDat.latPtS t e v, W.ψ (GlobalTheory.SmallDat.sympS Γ z γ) = 1) := by
  intro D T L sc G μ₀ hL W t i j e Γ hW₁ hWW v
  have s0 := (node_isV G hL (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩).sd
  have s1 := (node_isV G hL (X := .grid (i : ℕ) ((j : ℕ) + 1)) ⟨i.2.le, j.2⟩).sd
  have s2 := (node_isV G hL (X := .grid ((i : ℕ) + 1) (j : ℕ)) ⟨i.2, j.2.le⟩).sd
  refine ⟨GlobalTheory.BigDatLat.le_of_gen (GlobalTheory.SmallDat.maps t e) v _ (fun _ => Iff.rfl) _
    (fun u hu => AddSubgroup.subset_closure (Or.inl ⟨u, hu, rfl⟩))
    fun ε hε u hu h1 h2 => AddSubgroup.subset_closure (Or.inr ⟨hu, ε, hε, h1, h2⟩), fun z hz => ?_⟩
  exact GlobalTheory.BigDatLat.mem_iff_char (GlobalTheory.SmallDat.maps t e) v _ s0 s1 (isSelfDualC_neg s2) s0 (fun _ => Iff.rfl) W.ψ_std
    (GlobalTheory.SmallDat.sympS Γ) (GlobalTheory.SmallDat.sympS_eq t e Γ hW₁ hWW) hz

end GlobalTheory.SmallDatLat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedKernelOfVectorAdd
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopZeroInv

open MvPolynomial

private theorem jetLin_add_tab {K : Type} [Field K] {ι : Type} {a b : ℕ} (J J' : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → K) :
    Formalism.L2.Ker.jetLin (J + J') = Formalism.L2.Ker.jetLin J + Formalism.L2.Ker.jetLin J' := by
  refine (basisMonomials ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) K).ext fun m => ?_
  simp only [Formalism.L2.Ker.jetLin, LinearMap.add_apply, Module.Basis.constr_basis, Pi.add_apply, map_add (f := _)]

theorem kkVec_add : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (p : Pair T) {f f' : WO (G.pS p) (G.pT p) → ℂ},
    IsThetaFunO W.ψ _ _ f → IsThetaFunO W.ψ _ _ f' → ∀ (x : FinPt G p.small) (y : FinPt G p.big),
    kkVec S p (f + f') x y = kkVec S p f x y + kkVec S p f' x y := by
  intro D T L sc G W U S p f f' hf hf' x y
  have hJ : ∀ x' y', GlobalTheory.FunObj.jetTab W S.N.frC p (f + f') x' y' =
      GlobalTheory.FunObj.jetTab W S.N.frC p f x' y' + GlobalTheory.FunObj.jetTab W S.N.frC p f' x' y' := by
    intro x' y'
    funext k
    simp only [GlobalTheory.FunObj.jetTab, GlobalTheory.FunObj.kerFin, GlobalTheory.FunObj.fockIn, Pi.add_apply]
    rw [GlobalTheory.SpecFac.pureTensorO_add W.ψ_std W.θ_is _ _ _ _ hf hf']
    simp only [GlobalTheory.ChiGrid.GridData.Weil.ker, thetaKO, map_add (f := _), Pi.add_apply]
  unfold kkVec GlobalTheory.FunObj.fockComp
  rw [hJ, ← smul_add]
  congr 1
  ext1 F
  simp only [Formalism.L2.Ker.jetOp, Formalism.L2.Ker.jetMap, jetLin_add_tab, LinearMap.comp_apply, LinearMap.add_apply, map_add (f := _)]

end GlobalTheory.TopZeroInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorSymplecticFormAtSplitFinitePlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorSymplecticForm_at_split_finite_place : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d), (∀ r s, σ (X.J s r) = X.J r s) → (∀ r s, σ (Y.J s r) = -Y.J r s) → ∀ (ψ : AddChar (AF F) ℂ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v)
    (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (x u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    At (evFin F v) x → At (evFin F v) u →
    ψ (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) x u) =
      psiLoc ψ v (pairM (coX t b c x) (coY σ X Y t b c u) - pairM (coY σ X Y t b c x) (coX t b c u)) := by
  first | exact @GlobalTheory.FlipMatch.SplitSymp.symp_at_split | exact GlobalTheory.FlipMatch.SplitSymp.symp_at_split | (intros; apply GlobalTheory.FlipMatch.SplitSymp.symp_at_split <;> assumption)
end

