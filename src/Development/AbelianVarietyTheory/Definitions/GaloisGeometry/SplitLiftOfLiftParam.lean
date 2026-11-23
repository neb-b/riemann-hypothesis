module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeSplitOne

@[expose] public section

noncomputable section

namespace GlobalTheory.ThetaExh.Check

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.ThetaExh

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

private theorem foldr_lpSum_lpChar_comm {ι : Type} (hL : ParamLaws N A) (χ : A.CG 1) (w : PlE H)
    (c : ι → ℝ) (b : A.LP w) (L : List ι) :
    L.foldr (fun k acc => A.lpSum (A.lpTw (A.lpChar b (A.locG χ w)) (c k)) acc) (A.lpZero w) =
      A.lpChar (L.foldr (fun k acc => A.lpSum (A.lpTw b (c k)) acc) (A.lpZero w)) (A.locG χ w) := by
  have hd : A.lpDim (A.locG χ w) = 1 := A.locG_dim χ w
  induction L with
  | nil => exact ((hL w).2.1 _ hd).symm
  | cons k L ih =>
    simp only [List.foldr_cons]
    rw [ih, (hL w).1 _ _ _ hd, (hL w).2.2.1 _ _ _ hd]

theorem speh_char (hL : ParamLaws N A) (p : Part A.CG) (χ : A.CG 1) (w : PlE H) :
    spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w = A.lpChar (spehLoc N A p w) (A.locG χ w) := by
  unfold spehLoc
  simp only [A.locG_tw]
  exact foldr_lpSum_lpChar_comm N A hL χ w (fun k : ℝ => ((p.d : ℝ) - 1) / 2 - k) (A.locG p.π w) _

theorem iso_char (hL : ParamLaws N A) (S : List (Part A.CG)) (χ : A.CG 1) (w : PlE H) :
    isoLoc N A (twistIso N A S χ) w = A.lpChar (isoLoc N A S w) (A.locG χ w) := by
  have hd : A.lpDim (A.locG χ w) = 1 := A.locG_dim χ w
  induction S with
  | nil => exact ((hL w).2.1 _ hd).symm
  | cons p S ih =>
    show A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A S χ) w) =
      A.lpChar (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (A.locG χ w)
    rw [ih, speh_char N A hL p χ w, (hL w).1 _ _ _ hd]

theorem iso_append (S : List (Part A.CG)) (p : Part A.CG) (w : PlE H) :
    isoLoc N A (S ++ [p]) w = A.lpSum (isoLoc N A S w) (spehLoc N A p w) := by
  induction S with
  | nil => exact A.lpSum_comm _ _
  | cons q S ih =>
    show A.lpSum (spehLoc N A q w) (isoLoc N A (S ++ [p]) w) =
      A.lpSum (A.lpSum (spehLoc N A q w) (isoLoc N A S w)) (spehLoc N A p w)
    rw [ih, A.lpSum_assoc]

end GlobalTheory.ThetaExh.Check
