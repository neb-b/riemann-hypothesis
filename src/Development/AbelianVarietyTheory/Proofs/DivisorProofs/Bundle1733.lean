module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianNegTraceZeroInvHermitianUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1480
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffThetaTransformArchimedeanCm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1475
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1479
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1714
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1717
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0974

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.TopFlip

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc}


variable (G) in
abbrev spX (i j : ℕ) : HSp D := GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)


variable (G) in
def latX (i j : ℕ) : Submodule (𝓞 D.host.E) (Fin (spX G i j).rank → D.host.E) :=
  GlobalTheory.Doubling.sumLat finSumFinEquiv (G.Λ (.grid i (j + 1))) (G.Λ (.grid (i + 1) j))


variable (G) in
def homLatA (i j : ℕ) : AddSubgroup (WO (spW G i j) (spX G i j)) :=
  latO (GlobalTheory.Grid.neg (spW G i j)) (spX G i j) (G.Λ (.grid (i + 1) (j + 1))) (latX G i j) fun _ => True


variable (G) in
def homLatB (i j : ℕ) : AddSubgroup (WO (spW₁ G i j) (spX G i j)) :=
  latO (spW₁ G i j) (spX G i j) (G.Λ (.grid i j)) (latX G i j) fun _ => True


variable (G) in
def orderingsOnSpW (i j : ℕ) : Set (WO (spW G i j) (spX G i j)) :=
  {x | GlobalTheory.RouteSeesaw.topR (A := spV G i j) (B := spV₁ G i j) x ∈
      latO (negSp (spW G i j)) (spV G i j) (G.Λ (.grid (i + 1) (j + 1))) (G.Λ (.grid i (j + 1))) (fun _ => True) ∧
    GlobalTheory.RouteSeesaw.adjM (spW G i j) (spV₁ G i j) (GlobalTheory.RouteSeesaw.botR (A := spV G i j) (B := spV₁ G i j) x) ∈
      latO (spV₁ G i j) (spW G i j) (G.Λ (.grid (i + 1) j)) (G.Λ (.grid (i + 1) (j + 1))) fun _ => True}


variable (G) in
def orderingsOnSpWOne (i j : ℕ) : Set (WO (spW₁ G i j) (spX G i j)) :=
  {y | GlobalTheory.RouteSeesaw.topR (A := spV G i j) (B := spV₁ G i j) y ∈
      latO (spW₁ G i j) (spV G i j) (G.Λ (.grid i j)) (G.Λ (.grid i (j + 1))) (fun _ => True) ∧
    GlobalTheory.RouteSeesaw.adjM (spW₁ G i j) (negSp (spV₁ G i j)) (GlobalTheory.RouteSeesaw.botR (A := spV G i j) (B := spV₁ G i j) y) ∈
      latO (negSp (spV₁ G i j)) (spW₁ G i j) (G.Λ (.grid (i + 1) j)) (G.Λ (.grid i j)) fun _ => True}

section Vac

variable {W : G.Weil} (ρ : RealMatch W) (i j : ℕ)

def vacA : WO (spW G i j) (spX G i j) → ℂ :=
  GlobalTheory.RouteSeesaw.box2 (S := negSp (spW G i j)) (A := spV G i j) (B := spV₁ G i j) (ρ.vX i (j + 1))
    fun y => ρ.vT (i + 1) j (GlobalTheory.RouteSeesaw.adjM (spW G i j) (spV₁ G i j) y)

def vacB : WO (spW₁ G i j) (spX G i j) → ℂ :=
  GlobalTheory.RouteSeesaw.box2 (S := spW₁ G i j) (A := spV G i j) (B := spV₁ G i j) (ρ.vT i j)
    fun y => ρ.vX i j (GlobalTheory.RouteSeesaw.adjM (spW₁ G i j) (negSp (spV₁ G i j)) y)

theorem datumA_vac (t : T) : datumA W (t := t) (i := i) (j := j) (Finsupp.single (((), ρ.vX i (j + 1)), ρ.vT (i + 1) j) 1) = vacA ρ i j := by
  unfold datumA
  erw [Finsupp.sum_single_index (by exact zero_smul ℂ _), one_smul]
  rfl

theorem datumB_vac (t : T) : datumB W (t := t) (i := i) (j := j) (Finsupp.single (((), ρ.vT i j), ρ.vX i j) 1) = vacB ρ i j := by
  unfold datumB
  erw [Finsupp.sum_single_index (by exact zero_smul ℂ _), one_smul]
  rfl

end Vac

section Coord

variable (B : Frames G) (t : T) (i j : Fin D.R.m)

def frX : GL (Fin (spX G i j).rank) (EAf D) := GlobalTheory.Doubling.blkGL finSumFinEquiv (B.β i (j + 1), -B.β (i + 1) j)


variable (G) in
def colX (w : Pl D.host.E) : Fin (spX G i j).rank ≃ (locGrid G t w).Cols i j :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (finCongr (rank_vertex G t w (X := (i, j + 1)) ⟨i.2.le, j.2⟩).symm)
    (finCongr (rank_vertex G t w (X := (i + 1, j)) ⟨i.2, j.2.le⟩).symm))


variable (G) in
def ordX (w : Pl D.host.E) :
    (locGrid G t w).Cols i j ≃ Fin ((locGrid G t w).rank (i + 1, j + 1) + (locGrid G t w).rank (i, j)) :=
  (stdSplit ((locGrid G t w).rank_square i j)).symm.trans finSumFinEquiv


variable (G) in
abbrev MatA (w : Pl D.host.E) : Type :=
  Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w)


variable (G) in
abbrev MatB (w : Pl D.host.E) : Type := Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w)

def linA (w : Pl D.host.E) (x : WO (spW G i j) (spX G i j)) : MatA G t i j w :=
  reindex (finCongr (rankW G t i j w)) (colX G t i j w)
    ((frMapO (spW G i j) (spX G i j) (B.β (i + 1) (j + 1)) (frX B i j) x).map (cpt w))ᵀ

def linB (w : Pl D.host.E) (y : WO (spW₁ G i j) (spX G i j)) : MatB G t i j w :=
  reindex (finCongr (rankW₁ G t i j w)) (colX G t i j w)
    ((frMapAdj (spW₁ G i j) (spX G i j) (B.β i j) (frX B i j) y).map (cpt w))


open Classical in
def prodA (ε : AE D) (Ξ : ∀ w, MatA G t i j w → ℂ) (x : WO (spW G i j) (spX G i j)) : ℂ :=
  if IsHalf ε x then ∏ w ∈ locPl G t, Ξ w (linA B t i j w x) else 0


open Classical in
def prodB (ε : AE D) (Ψ : ∀ w, MatB G t i j w → ℂ) (y : WO (spW₁ G i j) (spX G i j)) : ℂ :=
  if IsHalf (cA D ε) y then ∏ w ∈ locPl G t, Ψ w (linB B t i j w y) else 0

variable {W : G.Weil} (ρ : RealMatch W)

def IsLinA (ε : AE D) (Ξ : ∀ w, MatA G t i j w → ℂ) (F : WO (spW G i j) (spX G i j) → ℂ) : Prop :=
  IsThetaAt W.ψ (symplO (GlobalTheory.Grid.neg (spW G i j)) (spX G i j)) (heisO W.ψ (GlobalTheory.Grid.neg (spW G i j)) (spX G i j)) ε
    (homLatA G i j) 1 (vacA ρ i j) (prodA B t i j ε Ξ) F

def IsLinB (ε : AE D) (Ψ : ∀ w, MatB G t i j w → ℂ) (F : WO (spW₁ G i j) (spX G i j) → ℂ) : Prop :=
  IsThetaAt W.ψ (symplO (spW₁ G i j) (spX G i j)) (heisO W.ψ (spW₁ G i j) (spX G i j)) (cA D ε)
    (homLatB G i j) 1 (vacB ρ i j) (prodB B t i j ε Ψ) F

end Coord

section Model

variable {i j : ℕ} (e : Num G i j)

def ptA (u : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) : WO (spW G i j) (spX G i j) :=
  (HMul.hMul (uᵀ.submatrix (e.symm.trans finSumFinEquiv).symm id) (incM (GlobalTheory.Grid.sgn true (spW G i j)).gram) :
    Matrix (Fin (_ + _)) (Fin _) (AE D))

def ptB (u : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) : WO (spW₁ G i j) (spX G i j) :=
  (HMul.hMul (uᵀ.submatrix (e.symm.trans finSumFinEquiv).symm id) (incM (spW₁ G i j).gram) :
    Matrix (Fin (_ + _)) (Fin _) (AE D))

end Model

section Charts

variable (W : G.Weil) (B : Frames G) (t : T) {i j : Fin D.R.m} (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (w : Pl D.host.E)


variable (G i j) in
abbrev ToA : Type :=
  ((Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F (w.under (𝓞 D.host.F))) → ℂ) →ₗ[ℂ]
    (MatA G t i j w → ℂ)


variable (G i j) in
abbrev ToB : Type :=
  ((Fin (spW₁ G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F (w.under (𝓞 D.host.F))) → ℂ) →ₗ[ℂ]
    (MatB G t i j w → ℂ)

def IsLinModelA (ι : ToA G t i j w) : Prop :=
  IsLagrModel Γ.M W.ψ (w.under (𝓞 D.host.F)) {u | IsHalf (atPl w 1) (ptA e u)} {u | IsHalf (cA D (atPl w 1)) (ptA e u)}
    (fun u => linA B t i j w (ptA e u)) ι

def IsLinModelB (ι : ToB G t i j w) : Prop :=
  IsLagrModel Γ.M' W.ψ (w.under (𝓞 D.host.F)) {u | IsHalf (cA D (atPl w 1)) (ptB e u)} {u | IsHalf (atPl w 1) (ptB e u)}
    (fun u => linB B t i j w (ptB e u)) ι

def IsMixModelA (ι : ToA G t i j w) : Prop :=
  IsLagrModel Γ.M W.ψ (w.under (𝓞 D.host.F)) (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w) ι

def IsMixModelB (ι : ToB G t i j w) : Prop :=
  IsLagrModel Γ.M' W.ψ (w.under (𝓞 D.host.F)) (mixHalfS e (atPl w 1)) (mixHalfS e (cA D (atPl w 1))) (mixCoS B t e w) ι

end Charts

section ZetaNonvanishing₂

variable (G) (t : T) (i j : Fin D.R.m) (w : Pl D.host.E)

def zetaA (Ξ : MatA G t i j w → ℂ) : GL ((locGrid G t w).Cols i j) (Kw w) → ℂ :=
  bigP (haarVol (KO (Kw w) _)) (unifAt w) (stdSplit ((locGrid G t w).rank_square i j)) ((locGrid G t w).nu i j) 1 Ξ

def zetaB (Ψ : MatB G t i j w → ℂ) : GL ((locGrid G t w).Cols i j) (Kw w) → ℂ :=
  smallP (haarVol (KO (Kw w) _)) (stdSplit ((locGrid G t w).rank_square i j)) ((locGrid G t w).nu i j)
    ((locGrid G t w).nu i j * 1) Ψ

def levVol : ℝ :=
  (haarVol (KO (Kw w) (Fin ((locGrid G t w).rank (i, j))))).real ((givenLevel G t w (i, j)).map invT : Subgroup _)

end ZetaNonvanishing₂

section Std

variable (B : Frames G) (t : T) {i j : Fin D.R.m} (X : TriG G i j) (w : Pl D.host.E)

def chA : GL (Fin ((locGrid G t w).rank (i + 1, j + 1))) (Kw w) :=
  GlobalTheory.StepData.reGL (finCongr (rankW G t i j w)) (invT ((loc w X.rA.β)⁻¹ * loc w (B.β (i + 1) (j + 1))))

def chB : GL (Fin ((locGrid G t w).rank (i, j))) (Kw w) :=
  GlobalTheory.StepData.reGL (finCongr (rankW₁ G t i j w))
    (Units.map (Matrix.scalar (Fin (spW₁ G i j).rank)).toMonoidHom
        (Units.mk0 (xiAt w) ((_root_.map_ne_zero _).2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)) *
      ((loc w X.rA'.β)⁻¹ * loc w (B.β i j)))

def chX : GL ((locGrid G t w).Cols i j) (Kw w) :=
  GlobalTheory.StepData.reGL (colX G t i j w) ((loc w (frX B i j))⁻¹ * loc w X.rW.β)

def locFst (Z : MatA G t i j w) : ℂ :=
  GlobalTheory.StdPairCone.stdA ((locGrid G t w).nu i j) (unifAt w) (X.c t w) _ _
    (reindex (Equiv.refl _) (ordX G t i j w) ((chA B t X w).val * Z * (invT (chX B t X w)).val))

def locSnd (Y : MatB G t i j w) : ℂ :=
  GlobalTheory.StdPairCone.stdB ((locGrid G t w).nu i j) (unifAt w) (X.c t w) _ _
    (reindex (Equiv.refl _) (ordX G t i j w) ((chB B t X w).val * Y * (chX B t X w).val))

end Std

end GlobalTheory.TopFlip

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunOMul
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

namespace GlobalTheory.BigDat.ThBox

theorem isThetaFunO_mul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T S₁ T₁ S₂ T₂ : HSp D} (p₁ : WO S T →+ WO S₁ T₁)
    (p₂ : WO S T →+ WO S₂ T₂) (c₁ : Continuous p₁) (c₂ : Continuous p₂)
    (hs : ∀ x y, symplO S T x y = symplO S₁ T₁ (p₁ x) (p₁ y) + symplO S₂ T₂ (p₂ x) (p₂ y))
    (r₁ : ∀ γ, ∃ γ', p₁ (ratW T S γ) = ratW T₁ S₁ γ') (r₂ : ∀ γ, ∃ γ', p₂ (ratW T S γ) = ratW T₂ S₂ γ')
    (hi : ∀ u, u.map (infPart D) = 0 → (p₁ u).map (infPart D) = 0 ∧ (p₂ u).map (infPart D) = 0)
    (hf : ∀ u, u.map (finPart D) = 0 → (p₁ u).map (finPart D) = 0 ∧ (p₂ u).map (finPart D) = 0)
    {f₁ : WO S₁ T₁ → ℂ} {f₂ : WO S₂ T₂ → ℂ} (h₁ : IsThetaFunO ψ S₁ T₁ f₁) (h₂ : IsThetaFunO ψ S₂ T₂ f₂) :
    IsThetaFunO ψ S T fun u => f₁ (p₁ u) * f₂ (p₂ u) := by
  have hH : ∀ x y, symplOH S T x y = symplOH S₁ T₁ (p₁ x) (p₁ y) + symplOH S₂ T₂ (p₂ x) (p₂ y) := fun x y => by
    unfold symplOH
    rw [hs, mul_add]
  refine ⟨fun γ w => ?_, ?_, (h₁.cont.comp c₁).mul (h₂.cont.comp c₂), fun k L hL hL0 w => ?_⟩
  · obtain ⟨γ₁, e₁⟩ := r₁ γ
    obtain ⟨γ₂, e₂⟩ := r₂ γ
    rw [map_add (f := _), map_add (f := _), hH, e₁, e₂, h₁.quasi, h₂.quasi, neg_add, AddChar.map_add_eq_mul]
    ring
  · obtain ⟨U₁, o₁, hU₁⟩ := h₁.level
    obtain ⟨U₂, o₂, hU₂⟩ := h₂.level
    refine ⟨U₁.comap p₁ ⊓ U₂.comap p₂, (o₁.preimage c₁).inter (o₂.preimage c₂), fun u hu h0 => funext fun w => ?_⟩
    have a₁ := congrFun (hU₁ (p₁ u) hu.1 (hi u h0).1) (p₁ w)
    have a₂ := congrFun (hU₂ (p₂ u) hu.2 (hi u h0).2) (p₂ w)
    unfold heisO at a₁ a₂ ⊢
    beta_reduce
    rw [← a₁, ← a₂, hH, map_add (f := p₁), map_add (f := p₂), AddChar.map_add_eq_mul]
    ring
  · simp only [map_add (f := _)]
    exact (h₁.smooth k (p₁.comp L) (c₁.comp hL) (fun t => (hf _ (hL0 t)).1) (p₁ w)).mul
      (h₂.smooth k (p₂.comp L) (c₂.comp hL) (fun t => (hf _ (hL0 t)).2) (p₂ w))

theorem mulG_map_zero {D : D7} {R : Type} [CommRing R] (φ : AE D →+* R) (S : HSp D) {n : ℕ}
    (x : Matrix (Fin n) (Fin S.rank) (AE D)) (h : x.map φ = 0) : (mulG S x).map φ = 0 := by
  rw [mulG_eq, Matrix.map_mul, h, Matrix.zero_mul]

theorem continuous_mulG {D : D7} (S : HSp D) {n : ℕ} : Continuous (mulG S (n := n)) := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  exact continuous_id.matrix_mul continuous_const

theorem mulG_rat {D : D7} (S : HSp D) {n : ℕ} (x : Matrix (Fin n) (Fin S.rank) D.host.E) :
    mulG S (x.map (incA D)) = (x * S.gram).map (incA D) := by
  rw [mulG_eq, Matrix.map_mul]

theorem infPart_cA {D : D7} (x : AE D) :
    infPart D (cA D x) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem finPart_cA {D : D7} (x : AE D) :
    finPart D (cA D x) = sigR (Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]
  | tmul a x => rfl

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

theorem maps_map_zero {R : Type} [CommRing R] (φ : AE D →+* R) (hφ : ∀ x, φ x = 0 → φ (cA D x) = 0) (e : Num G i j)
    (u : Pt G i j) (h : u.map φ = 0) : (mapV e u).map φ = 0 ∧ (mapW e u).map φ = 0 := by
  have h0 : ∀ a b, φ (u a b) = 0 := fun a b => congrFun (congrFun h a) b
  refine ⟨mulG_map_zero φ _ _ (Matrix.ext fun a b => h0 _ _), ?_⟩
  have h2 := mulG_map_zero φ (spV₁ G i j) ((u.submatrix id fun k => e (.inr k)).map (cA D))
    (Matrix.ext fun a b => hφ _ (h0 _ _))
  exact Matrix.ext fun a b => (map_neg φ _).trans (neg_eq_zero.2 (congrFun (congrFun h2 a) b))

theorem continuous_mapV (e : Num G i j) : Continuous (mapV e) :=
  (continuous_mulG (negSp (spW G i j))).comp (continuous_id.matrix_submatrix id fun k => e (.inl k)).matrix_transpose

theorem continuous_mapW (e : Num G i j) : Continuous (mapW e) := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  exact ((continuous_mulG (spV₁ G i j)).comp ((continuous_id.matrix_submatrix id fun k => e (.inr k)).matrix_map
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D))).neg

theorem mapV_rat (e : Num G i j) (γ : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) D.host.E) :
    ∃ γ', mapV e (γ.map (incA D)) = ratW (spV G i j) (negSp (spW G i j)) γ' :=
  ⟨_, mulG_rat (negSp (spW G i j)) (γ.submatrix id fun k => e (.inl k))ᵀ⟩

theorem mapW_rat (e : Num G i j) (γ : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) D.host.E) :
    ∃ γ', mapW e (γ.map (incA D)) = ratW (spW G i j) (spV₁ G i j) γ' :=
  ⟨-_, (congrArg Neg.neg (mulG_rat (spV₁ G i j) ((γ.submatrix id fun k => e (.inr k)).map star))).trans
    (Matrix.map_neg _ (map_neg (incA D)) _).symm⟩

theorem thetaPt_box : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (t : T) (i j : ℕ) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X → IsTriple Bs Γ X om om' →
    (∀ Φ ∈ schA D.host.F (Ix G i j), ∀ Φ' ∈ schA D.host.F (Ix G i j), thetaPt Γ W.ψ (Φ + Φ') = thetaPt Γ W.ψ Φ + thetaPt Γ W.ψ Φ') ∧
    (∀ Φ ∈ schA D.host.F (Ix G i j), ∀ Φ' ∈ schA D.host.F (Ix G i j), thetaPt Γ W.ψ Φ = thetaPt Γ W.ψ Φ' → Φ = Φ') ∧
    ∀ (f₁ : HomV G i j → ℂ) (f₂ : HomW G i j → ℂ), IsThetaFunO W.ψ _ _ f₁ → IsThetaFunO W.ψ _ _ f₂ →
      ∃ Φ ∈ schA D.host.F (Ix G i j), thetaPt Γ W.ψ Φ = box e f₁ f₂ := by
  intro D T L sc G W M t i j e Bs Γ X om om' h hT
  obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.WeilSchrodingerHerm.main D Bs hT.base _ Γ.V _ _ hT.geo.hV
  obtain ⟨hJ, L', hL, h4, h5, h6⟩ := _root_.GlobalTheory.WeilSchrodingerSkew.main D Bs hT.base _ Γ.W _ _ hT.geo.hW
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  let T₀ := GlobalTheory.WeilSchrodinger.hspOf D Γ.V.Jᵀ h1 h2 Γ.V.L hT.geo.hV.lat.toIsLattice h3 (fun _ => (0, 0))
  let S₀ := GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 L' hL h6 (fun _ => (0, 0))
  have eA : Γ.V.J = T₀.gramᵀ := by rw [GlobalTheory.WeilSchrodinger.gram_hspOf]; rfl
  have eB : (-1 : AE D) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S₀.gram⁻¹) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
    have e1 : (-D.host.xi0 • Γ.W.J⁻¹)⁻¹ = (-D.host.xi0)⁻¹ • Γ.W.J := Matrix.inv_eq_left_inv (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJ,
        inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul])
    have e2 : D.host.xi0 • (-D.host.xi0)⁻¹ • Γ.W.J = -Γ.W.J := by
      rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ, neg_one_smul]
    show (-1 : AE D) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (-D.host.xi0 • Γ.W.J⁻¹)⁻¹)
    rw [e1, e2]
    funext a b
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  have hψ : IsStdChar D W.ψ (-1) := h.ψ ▸ _root_.GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D Bs.ψ hT.base.std
  obtain ⟨ha, hi, hs⟩ := GlobalTheory.ThetaTransform.thetaTr_bij (S := S₀) (T := T₀) Γ.M.co hψ eA eB hT.geo.hM.rat
  refine ⟨ha, hi, fun f₁ f₂ hf₁ hf₂ => (hs _).1 ?_⟩
  exact isThetaFunO_mul (S := S₀) (T := T₀) (AddMonoidHom.mk' (mapV e) (mapV_add e)) (AddMonoidHom.mk' (mapW e) (mapW_add e))
    (continuous_mapV e) (continuous_mapW e)
    (fun x y => (GlobalTheory.ThetaTransform.symplO_eq_symp eA eB x y).trans (symp_eq e Γ h.JW h.JWW x y))
    (mapV_rat e) (mapW_rat e)
    (maps_map_zero (infPart D) (fun x hx => by rw [infPart_cA, hx, map_zero]) e)
    (maps_map_zero (finPart D) (fun x hx => by rw [finPart_cA, hx, map_zero]) e) hf₁ hf₂

end GlobalTheory.BigDat.ThBox

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryOnWeilDatumTransportAdelicSchwartz
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section
namespace GlobalTheory.WeilUnitaryTransportF

theorem isUnitaryOn_transportF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → IsUnitaryOn (adeleClass F) om := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hσ χS χT hcS hcT rS rT ω hω JA JB ξ hA hBm κ _ co hrat om hom
  have hψ := hω.std
  rintro μ hμ ⟨a, b⟩ Φ hΦ
  obtain ⟨g, h, hh, hg⟩ := _root_.GlobalTheory.WeilPairPartnerF.pair_partnerF F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm a b
  obtain ⟨ν, 𝓕, hν, h𝓕⟩ := _root_.GlobalTheory.TowerFD.exists_fd_any F E nS nT
  obtain ⟨ν', 𝓕', hν', h𝓕', heq⟩ :=
    _root_.GlobalTheory.RatDarbouxTransferF.haar_fundDomain_transfer F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat ν 𝓕 hν h𝓕
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.ThetaParseval.exists_lintegral_sq_eq_mul_setLIntegral_theta F B.ψ hψ.1 κ μ hμ ν' hν' 𝓕' h𝓕'
  have hiso : ∀ Ψ ∈ schA F κ, ∫⁻ x, ‖Ψ x‖ₑ ^ 2 ∂μ =
      c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Ψ w‖ₑ ^ 2 ∂ν := by
    intro Ψ hΨ
    rw [hc Ψ hΨ, ← heq]
    rfl
  have hth : IsThetaFunOF σ JS JT ξ₀ B.ψ (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) :=
    ⟨_root_.GlobalTheory.ThetaQuasiRatF.thetaTr_ratWF_add F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ,
     GlobalTheory.T.thetaTransform_adelicSchwartz_hasFiniteLevel_CM F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ,
     _root_.GlobalTheory.ThetaTrContF.continuous_thetaTrF F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ,
     _root_.GlobalTheory.ThetaSmoothF.contDiff_thetaTr_realF F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ⟩
  have ht := hom a b g h hh hg Φ hΦ
  calc
    _ = c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ ((om (a, b)) Φ) w‖ₑ ^ 2 ∂ν := hiso _ ht.1
    _ = c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ w‖ₑ ^ 2 ∂ν := by
      calc
        _ = c * ∫⁻ w in 𝓕, ‖(ω (g, h)) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) w‖ₑ ^ 2 ∂ν := by
          congr 1
          apply lintegral_congr
          intro w
          exact congrArg (fun z : ℂ => ‖z‖ₑ ^ 2) (congrFun ht.2 w)
        _ = _ := congrArg (c * ·) (hω.om_unit ν 𝓕 hν h𝓕 _ _ hth)
    _ = _ := (hiso _ hΦ).symm

end GlobalTheory.WeilUnitaryTransportF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorsProductCompatibleStatement
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_operators_product_compatible : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ → Fv F v)) →
    (∀ᶠ v in cofinite, ev v (stdInd F κ v) = stdInd F κ v) →
    (∀ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in cofinite, φ v = stdInd F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    Set.SurjOn e (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ)) →
    (∀ v, ev v (stdInd F κ v) ≠ 0) →
    ∀ v, ∀ χ ∈ SB (κ → Fv F v), ∃ ψ ∈ SB (κ → Fv F v), ev v ψ = χ := by
  first | exact @GlobalTheory.EvOnto.ev_surjOn_SB | exact GlobalTheory.EvOnto.ev_surjOn_SB | (intros; apply GlobalTheory.EvOnto.ev_surjOn_SB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeCentraliserClassNumberFiniteBorelStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitudeCentraliser_classNumber_finite_borel : ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (p : ℕ) [Fact p.Prime], letI : TopologicalSpace (AfP p ⊗[ℚ] D) := moduleTopology (AfP p) (AfP p ⊗[ℚ] D); letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] D) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] D); ∀ U : Subgroup (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), (∃ O : Set (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), IsOpen O ∧ 1 ∈ O ∧ ∀ z ∈ O, GlobalTheory.CentCls.TC D σ β y (AfP p) z.1 → GlobalTheory.CentCls.TC D σ β y ℚ_[p] z.2 → z ∈ U) → ∃ S : Finset (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), ∀ z : ((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ), GlobalTheory.CentCls.TC D σ β y (AfP p) z.1 → GlobalTheory.CentCls.TC D σ β y ℚ_[p] z.2 → ∃ γ : Dˣ × ℚˣ, (γ.1 : D) * β * (σ (γ.1 : D)).unop = algebraMap ℚ D (γ.2 : ℚ) * β ∧ Commute (γ.1 : D) y ∧ ∃ s ∈ S, ∃ u ∈ U, z = GlobalTheory.TorCls.dg D p γ * s * u := by
  first | (exact @GlobalTheory.CentCls.Fin.classes_finite) | (exact GlobalTheory.CentCls.Fin.classes_finite) | (intros; apply GlobalTheory.CentCls.Fin.classes_finite  <;> assumption)
end

