module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN

@[expose] public section

noncomputable section

namespace GlobalTheory.ThetaExh

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def RowSize : Prop := ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ → ∀ w, IsSplitPl H w →
  A.unr (A.locW i σ w) → ∀ α ∈ A.frobEig (A.locW i σ w),
    ‖α‖ < ((normV w : ℕ) : ℝ) ^ (((R.t : ℝ) - 1) / 2)

def RowSizeLe : Prop := ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ → ∀ w, IsSplitPl H w →
  A.unr (A.locW i σ w) → ∀ α ∈ A.frobEig (A.locW i σ w),
    ‖α‖ ≤ ((normV w : ℕ) : ℝ) ^ (((R.r : ℝ) - 1) / 2)

def HeckeSplitOne : Prop := ∀ χ χ' : A.CG 1,
  (∀ᶠ w in Filter.cofinite, IsSplitPl H w → A.locG χ w = A.locG χ' w) → χ = χ'

def Tempered : Prop := ∀ (a : ℕ) (π : A.CG a), A.csd π → A.ralg π → ∀ w, A.tempered (A.locG π w)

def ThetaOne : Prop := ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ → ∃ P, thetaOf N A i σ P

def Pairs (i : N.Loc) (σ : what₂.FT) (P : A.AV i) : Prop :=
  ∃ f ∈ what₂.isot (N.j i) σ, ∃ F ∈ A.typeV i P, inner ℂ F (what₂.thetaT (N.mu i) (N.j i) f) ≠ 0

def HoweUp (i : N.Loc) : Prop := ∀ σ P P', Pairs N A i σ P → Pairs N A i σ P' → P = P'

def TypeOrth (i : N.Loc) : Prop := ∀ P P', P ≠ P' → A.typeV i P ⟂ A.typeV i P'

def PartOrth (i : N.Loc) : Prop := ∀ σ σ', σ ≠ σ' → what₂.isot (N.j i) σ ⟂ what₂.isot (N.j i) σ'

def liftPar (i : N.Loc) (w : PlE H) (a : A.LP w) : A.LP w :=
  A.lpChar (A.lpSum a (spehLoc N A (muPart N A i) w)) (A.locG A.etaTinv w)

def SplitLift (i : N.Loc) : Prop := ∀ σ P, thetaOf N A i σ P → ∀ w, IsSplitPl H w →
  A.locV i P w = liftPar N A i w (A.locW i σ w)

def ParamLaws : Prop := ∀ w : PlE H,
  (∀ a b χ : A.LP w, A.lpDim χ = 1 → A.lpChar (A.lpSum a b) χ = A.lpSum (A.lpChar a χ) (A.lpChar b χ)) ∧
  (∀ χ : A.LP w, A.lpDim χ = 1 → A.lpChar (A.lpZero w) χ = A.lpZero w) ∧
  (∀ (a χ : A.LP w) (s : ℝ), A.lpDim χ = 1 → A.lpChar (A.lpTw a s) χ = A.lpTw (A.lpChar a χ) s) ∧
  (∀ a b χ : A.LP w, A.lpDim χ = 1 → A.lpChar a χ = A.lpChar b χ → a = b) ∧
  (∀ a b c : A.LP w, A.lpSum a c = A.lpSum b c → a = b)

def PtLocal (i : N.Loc) : Prop := ∀ (P : A.AV i) (x : N.X i),
  (∀ w, SplitOut N i w → ∃ p : Polynomial (N.O i),
    p.map (iotaO N A i) = galPol A (A.lpTw (A.locV i P w) ((1 - (R.nV : ℝ)) / 2)) ∧
    p.map (IsLocalRing.residue (N.O i)) = (heckePol N i x w).map (IsLocalRing.residue (N.O i))) →
  ∃ y, A.ptV i P = some y

def PtOfLoc (i : N.Loc) : Prop := ∀ (P P' : A.AV i) (x : N.X i), A.ptV i P' = some x →
  (∀ w, SplitOut N i w → A.locV i P w = A.locV i P' w) → A.ptV i P = some x

def LocOfPt (i : N.Loc) : Prop := ∀ (P P' : A.AV i) (x : N.X i), A.ptV i P = some x →
  A.ptV i P' = some x → ∀ w, IsSplitPl H w → A.locV i P w = A.locV i P' w

def LiftParam (i : N.Loc) : Prop := ∀ σ P, thetaOf N A i σ P → ∃ Sig, HasParamW N A i σ Sig ∧
  IsBCV N A i P (twistIso N A (Sig ++ [muPart N A i]) A.etaTinv)

def TypePlSplit : Prop := ∀ k v, IsSplitPl H (A.plGw k v)

def DownMem (i : N.Loc) : Prop := ∀ x ∈ ZgoodN N A i, ∀ Sig, HasParamX N A i x Sig →
  (eigC N A i x).map (what₂.thetaP (N.mu i) (N.j i)) ≤ MjSig N A i Sig

def GoodPart (i : N.Loc) : Prop :=
  goodPartM N A i = ⨆ x ∈ ZgoodN N A i, ⨆ Sig ∈ {Sig | HasParamX N A i x Sig}, MjSig N A i Sig

end GlobalTheory.ThetaExh
