module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CfgTopFalseIff
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaBoundOnBoundary
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0006
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
public import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyExponentOfFormalDegree
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Finset

theorem capelliPoly_ofReal {n : ℕ} (lam : Fin n → ℝ) (Y : ℝ) :
    Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) (Y : ℂ) = ((∏ s, (Y + lam s) : ℝ) : ℂ) := by
  simp only [Formalism.QuantumDeterminants.capP, Complex.ofReal_prod, Complex.ofReal_add]

private theorem prod_Icc_one_eq_prod_fin_succ {M : Type*} [CommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∏ i ∈ Finset.Icc 1 n, f i = ∏ i : Fin n, f (i.1 + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Fin.prod_univ_castSucc]
    rfl

theorem cfg_P (D : D7) (τ : D.what₂.Tau) (Y : ℝ) :
    (cfgOf D τ).P Y = ∏ s : Fin D.R.r, (Y + lamS D.R (D.hc τ) s) := by
  unfold Formalism.FourierDecayAlt.Sz.Cfg.P
  rw [prod_Icc_one_eq_prod_fin_succ]
  exact Finset.prod_congr rfl fun s _ => congrArg (Y + ·) (cfg_lam D τ s)

theorem cfg_aeff (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : (cfgOf D τ).aeff = aEff D u τ := by
  have hk := D.R.m_add_three_le_k
  have hv := cfg_v D τ 1 le_rfl (by omega)
  have hD : (cfgOf D τ).Del = (D.s.Del : ℝ) := rfl
  have ha : (cfgOf D τ).a = uOne D u τ 1 := (uOne_one D u τ).symm
  unfold Formalism.FourierDecayAlt.Sz.Cfg.aeff aEff
  rw [hv, hD, ha]
  by_cases h : IsTop D τ
  · have ht : (cfgOf D τ).top = true := (cfg_top_iff D τ).2 h
    rw [if_pos ht, if_pos h]
    rfl
  · have ht : (cfgOf D τ).top = false := (cfg_top_false_iff D τ).2 h
    rw [if_neg (by simp [ht]), if_neg h]

theorem deOf_ne (D : D7) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (h5 : ∀ w : D.what₂.Word, ¬ IsTop D τ → uOne D w τ D.R.k = vOne D τ (D.R.k - 1) - 1 / 2)
    (l : ℕ) (h1 : 1 ≤ l) (h2 : l ≤ D.R.k - 2) (hne : uOne D u τ (l + 1) ≠ uOne D u' τ (l + 1)) :
    deOf D u l ≠ deOf D u' l := by
  intro heq
  apply hne
  have hk : (cfgOf D τ).k = D.R.k := rfl
  rw [← cfg_u D u τ (h5 u) (l + 1) (by omega) (by omega), ← cfg_u D u' τ (h5 u') (l + 1) (by omega) (by omega)]
  have a1 : l + 1 ≠ 1 := by omega
  have a2 : l + 1 ≠ (cfgOf D τ).k := by rw [hk]; omega
  simp only [Formalism.FourierDecayAlt.Sz.Cfg.u, a1, a2, if_false, Nat.add_sub_cancel, heq]

theorem Tr_pos (D : D7) (u : D.what₂.Word) : 0 < Tr D u := by
  unfold Tr
  exact_mod_cast (D.mem u).A.T_prime.pos

theorem ka_pos_of {D : D7} (hv : 1 ≤ D.host.v) : 0 < D.host.ka := by
  exact div_pos Real.pi_pos (by linarith)

section Family

variable {eps : ℝ} {Fm : FamP eps}

end Family

end Formalism.MainNotions.BridgeLemma

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SplittingAdmissibleOfTermData
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals NumberField Module

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rec

variable {D : D7} (X : TermTie D)

theorem tie_Tu_pos (D : D7) (u : D.what₂.Word) : 0 < Tu D u := (D.mem u).A.T_prime.pos

theorem tie_Gval_ne {u u' : D.what₂.Word} (t : D.s.Term u u') (h : D.s.Gterm t ≠ 0) :
    Gval (X.fl t) (X.fl' t) ≠ 0 := by
  rw [← X.G_eq t]
  exact (map_ne_zero _).2 h

theorem tie_G_pos {u u' : D.what₂.Word} (t : D.s.Term u u') (h : D.s.Gterm t ≠ 0) (τ : D.host.E →+* ℂ) :
    0 < (τ (Gval (X.fl t) (X.fl' t))).re :=
  (b_G_pos (p_starConj D) (tie_Tu_pos D u) (X.fl t) (X.fl' t) (X.fixed t).2.2.1.2 (X.lift' t).2
    (tie_Gval_ne X t h) (p_posX D _ (tie_Tu_pos D u) (X.fl t)) τ).1

theorem GDr_of_tie : PX.GDr D X := by
  intro u u' t h
  have hpos := tie_G_pos X t h
  refine ⟨fun h1 => ?_, fun _ τ => hpos _⟩

  have hG : Gval (X.fl t) (X.fl' t) = -(((Tu D u : ℕ) : D.host.E) * ((Tu D u' : ℕ) : D.host.E) *
      (Dl (X.fl t).fl (X.fl' t).fl D.R.rS * star (Dl (X.fl t).fl (X.fl' t).fl D.R.rS))) := by
    simp only [Formalism.MainNotions.S.Lat.Gval, Formalism.MainNotions.S.Gflag, h1, star_zero, mul_zero, zero_sub]
  haveI := D.host.isCMField_hostE
  have hc : ∀ y : D.host.E, D.host.φ₀ (star y) = starRingEnd ℂ (D.host.φ₀ y) := fun y =>
    NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ y
  have h0 := hpos D.host.φ₀
  rw [hG, map_neg, map_mul, map_mul, map_mul, map_natCast, map_natCast, hc, Complex.mul_conj] at h0
  have key : 0 ≤ ((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ) *
      Complex.normSq (D.host.φ₀ (Dl (X.fl t).fl (X.fl' t).fl D.R.rS)) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Complex.normSq_nonneg _)
  simp at h0
  linarith

end Rec

theorem tie_Dl_eq' {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
    (F : FlagG S r T) (F' : FlagG S r T') (j : ℕ) (hj : j ≤ r + 1) :
    Dl F F' j = ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj)).det := by
  unfold Formalism.MainNotions.S.Dl Formalism.MainNotions.S.leadMinorE
  rw [dite_eq_left hj]

section Packets

variable {D : D7} (X : TermTie D)

theorem tie_X_le_ker {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (F : FlagG S r T) (y : S.V) (h : ∀ a, S.hT (F.e a) y = 0) : ∀ x ∈ F.X, S.hT x y = 0 := by
  intro x hx
  unfold Formalism.MainNotions.S.FlagG.X at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact h a
  | zero => simp
  | add x z _ _ hx hz => simp [hx, hz]
  | smul c x _ hx => simp [hx]

end Packets

section Fam

variable {eps : ℝ} (Fm : FamP eps)

end Fam

end Formalism.MainNotions.BridgeLemma

end
end

