module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ChainMatrices
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev Ef (D : D7) : Type := Formalism.IndefR.Lev.EAf D

variable {D : D7}

def ratM {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E) : Matrix (Fin a) (Fin b) (Ef D) :=
  M.map (Formalism.IndefR.Datum.eToEAf D)

def adjM {a b : ℕ} (M : Matrix (Fin a) (Fin b) (Ef D)) : Matrix (Fin b) (Fin a) (Ef D) :=
  Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) M

def mulM {a b c : ℕ} (M : Matrix (Fin a) (Fin b) (Ef D)) (N : Matrix (Fin b) (Fin c) (Ef D)) : Matrix (Fin a) (Fin c) (Ef D) :=
  HMul.hMul M N

def AgreeAt (PP : Pl D.host.E) {a b : ℕ} (M M' : Matrix (Fin a) (Fin b) (Ef D)) : Prop :=
  ∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e PP ∧
    ∀ i j, Formalism.IndefR.Datum.toEAf D e * M i j = Formalism.IndefR.Datum.toEAf D e * M' i j


variable (D) in
def nAux (j : ℕ) : ℕ := D.R.m - 1 - j


variable (D) in
def IsAuxiliaryHeckeCharacter (j : ℕ) (E Ev : ℕ → (D.sp.Y j).V) (z : (D.sp.Y j).V) : Prop :=
  (∀ i < nAux D j / 2, ∀ l < nAux D j / 2,
    (D.sp.Y j).hD (E i) (E l) = 0 ∧ (D.sp.Y j).hD (Ev i) (Ev l) = 0 ∧
      (D.sp.Y j).hD (E i) (Ev l) = if i = l then 1 else 0) ∧
  (∀ i < nAux D j / 2, ∀ x,
    (D.sp.Y j).hD (E i) (D.sp.iXY j x) = 0 ∧ (D.sp.Y j).hD (Ev i) (D.sp.iXY j x) = 0) ∧
  (Even j → (D.sp.Y j).hD z z = -(D.sp.T : D.host.E) ∧ (∀ x, (D.sp.Y j).hD z (D.sp.iXY j x) = 0) ∧
    ∀ i < nAux D j / 2, (D.sp.Y j).hD (E i) z = 0 ∧ (D.sp.Y j).hD (Ev i) z = 0)


variable (D) in
def normalFr (j : ℕ) (E Ev : ℕ → (D.sp.Y j).V) (z : (D.sp.Y j).V) (n : ℕ) : (D.sp.Y j).V :=
  if n < nAux D j / 2 then E n
  else if Even j ∧ n = nAux D j / 2 then z
  else (if Even j then -(D.sp.T : D.host.E) else (D.sp.T : D.host.E)) • Ev (nAux D j - 1 - n)


variable (D) in
def colX (j : ℕ) (γ : GL (Fin (D.sp.X j).rank) (Ef D)) (n : ℕ) (i : Fin (D.sp.Y j).rank) : Ef D :=
  if h : n < (D.sp.X j).rank then mulM (ratM (frameMat (D.sp.Y j) (D.sp.X j) (D.sp.iXY j))) γ.val i ⟨n, h⟩ else 0


variable (D) in
def chainMat (j : ℕ) (γ : GL (Fin (D.sp.X j).rank) (Ef D)) (E Ev : ℕ → (D.sp.Y j).V) (z : (D.sp.Y j).V) (s : ℕ) :
    Matrix (Fin (D.sp.Y j).rank) (Fin (D.sp.Y j).rank) (Ef D) :=
  fun i a =>
    if (a : ℕ) < D.R.k then colX D j γ a i
    else if (a : ℕ) < D.R.k + nAux D j then
      Formalism.IndefR.Datum.eToEAf D
        ((s : D.host.E) ^ ((a : ℕ) - D.R.k + 1) * (D.sp.Y j).frame.repr (normalFr D j E Ev z ((a : ℕ) - D.R.k)) i)
    else colX D j γ ((a : ℕ) - nAux D j) i

def SpansAt (PP : Pl D.host.E) (V : HSp D) (M : Matrix (Fin V.rank) (Fin V.rank) (Ef D)) : Prop :=
  ∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e PP ∧ ∀ x : Fin V.rank → Ef D,
    (fun i => Formalism.IndefR.Datum.toEAf D e * x i) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat V V.L0) ↔
      ∃ c : Fin V.rank → Ef D, (∀ a, c a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧
        ∀ i, Formalism.IndefR.Datum.toEAf D e * x i = Formalism.IndefR.Datum.toEAf D e * (M *ᵥ c) i

def ShapeY {T : Type} (L : LevCh D T) (j : ℕ) (γ : GL (Fin (D.sp.X j).rank) (Ef D)) (E Ev : ℕ → (D.sp.Y j).V) (z : (D.sp.Y j).V)
    (β : GL (Fin (D.sp.Y j).rank) (Ef D)) : Prop :=
  (∀ (l : Fin 2) (PP : Pl D.host.E), L.C.P.Div l PP → AgreeAt PP β.val (chainMat D j γ E Ev z (D.host.g l))) ∧
  ∀ t, ∀ PP ∈ L.Q t, SpansAt PP (D.sp.Y j) (chainMat D j γ E Ev z 1) → AgreeAt PP β.val (chainMat D j γ E Ev z 1)

def TopTie (j : ℕ) (β : GL (Fin (D.sp.Y j).rank) (Ef D)) (Λ : Submodule (𝓞 D.host.E) (Fin (D.sp.Y j).rank → D.host.E))
    (βX : GL (Fin D.sp.X'.rank) (Ef D)) : Prop :=
  IsFrame β Λ ∧ ∃ ι : D.sp.X'.V →ₗ[D.host.E] (D.sp.Y j).V, HEq ι D.sp.eYm.toLinearMap ∧
    ∀ (a : Fin (D.sp.Y j).rank) (b : Fin D.sp.X'.rank), (a : ℕ) = b →
      ∀ i, β.val i a = mulM (ratM (frameMat (D.sp.Y j) D.sp.X' ι)) βX.val i b

def IsStdSpace (V : HSp D) : Prop :=
  V.gram = 1 ∧ ∀ x : Fin V.rank → D.host.E, x ∈ L0c D V ↔ ∀ i, x i ∈ (algebraMap (𝓞 D.host.E) D.host.E).range

def OrthoFrame (i : Fin D.R.m) (β : GL (Fin (Vc D i).rank) (Ef D)) : Prop :=
  ∃ B : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E, β.val = ratM B ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B * (Vc D i).gram * B =
      if D.sp.Vneg ((i : ℕ) + 1) then -1 else 1

def Transport (Pg : Finset (Pl D.host.E)) (W Y : HSp D) (βW : GL (Fin W.rank) (Ef D)) (βY : GL (Fin Y.rank) (Ef D)) : Prop :=
  ∃ (x y : Matrix (Fin Y.rank) (Fin W.rank) (Ef D)) (y' : Matrix (Fin W.rank) (Fin Y.rank) (Ef D)),
    mulM (mulM (adjM x) (ratM Y.gram)) x = ratM W.gram ∧ mulM x βW.val = mulM βY.val y ∧
    Formalism.IndefR.Datum.IsIntM y ∧ Formalism.IndefR.Datum.IsIntM y' ∧ mulM y y' = 1 ∧ mulM y' y = 1 ∧
    ∀ PP ∈ Pg, AgreeAt PP y (Matrix.of fun a b => if (a : ℕ) = b then 1 else 0)

def FrameClauses {T : Type} (L : LevCh D T) : Prop :=
  (∀ j, j < D.R.m → IsSDFrame (Yc D j) (L.βY j) (L.ΛY j) (D.host.g 0 * D.host.g 1)) ∧
  IsSDFrame D.sp.X' L.βX L.ΛX 1 ∧
  (∀ i, IsSDFrame (Vc D i) (L.βV i) (L.ΛV i) 1) ∧
  ∀ i, IsSDFrame (Wc D i) (L.βW i) (L.ΛW i) 1

def StdShape {T : Type} (L : LevCh D T) (γ : ∀ j, GL (Fin (D.sp.X j).rank) (Ef D))
    (E Ev : ∀ j, ℕ → (D.sp.Y j).V) (z : ∀ j, (D.sp.Y j).V) : Prop :=
  (∀ j, j < D.R.m → IsAuxiliaryHeckeCharacter D (min j D.R.m) (E _) (Ev _) (z _) →
    ShapeY L (min j D.R.m) (γ _) (E _) (Ev _) (z _) (L.βY j)) ∧
  (∀ j, D.R.m ≤ j → TopTie (min j D.R.m) (L.βY j) (L.ΛY j) L.βX) ∧
  (IsStdSpace D.sp.X' → L.βX = 1) ∧
  (∀ i, OrthoFrame i (L.βV i) ∧ (IsStdSpace (Vc D i) → L.βV i = 1)) ∧
  ∀ i, Transport L.Pg (Wc D i) (Yc D 0) (L.βW i) (L.βY 0)

def SameChars {T : Type} (L L' : LevCh D T) : Prop :=
  L'.C = L.C ∧ L'.xiH = L.xiH ∧ L'.mu0 = L.mu0 ∧ L'.eta = L.eta ∧ L'.xi = L.xi ∧ L'.Pg = L.Pg ∧ L'.Q = L.Q ∧
    L'.chi = L.chi ∧ L'.xiR = L.xiR

def FramesStdExist : Prop :=
  ∀ (D : D7) (T : Type) (L : LevCh D T),
    (∀ PP, PP ∈ L.Pg ↔ ∃ l, L.C.P.Div l PP) → (∀ t, Formalism.IndefR.Lev.IsTwistPlaces D.host.g (L.Q t)) →
    ∀ (γ : ∀ j, GL (Fin (D.sp.X j).rank) (Ef D)) (E Ev : ∀ j, ℕ → (D.sp.Y j).V) (z : ∀ j, (D.sp.Y j).V),
      (∀ j, j < D.R.m → IsFrame (γ j) (Formalism.L2.Herm.crdLat (D.sp.X j) (D.sp.X j).L0)) →
      ∃ L' : LevCh D T, SameChars L L' ∧ FrameClauses L' ∧ StdShape L' γ E Ev z

theorem idx_lt {j : ℕ} (hj : j < D.R.m) (a : Fin (D.sp.Y j).rank) :
    ((a : ℕ) < D.R.k → (a : ℕ) < (D.sp.X j).rank) ∧
      (¬ (a : ℕ) < D.R.k + nAux D j → (a : ℕ) - nAux D j < (D.sp.X j).rank) := by
  have h1 := D.sp.X_rank j hj.le
  have h2 := D.sp.Y_rank j hj.le
  have h3 := a.2
  have h4 : j * (D.R.t + 1) = j * D.R.t + j := by ring
  simp only [Ranks.N, Ranks.rankY, Ranks.r] at h1 h2
  unfold nAux
  generalize j * D.R.t = u at *
  constructor <;> intro h <;> omega

theorem isAuxiliaryHyperbolicPart_initialChainSpace : IsAuxiliaryHeckeCharacter D 0 (fun i => if h : i < D.R.rS then D.sp.hypE ⟨i, h⟩ else 0)
    (fun i => if h : i < D.R.rS then D.sp.hypF ⟨i, h⟩ else 0) D.sp.zm := by
  have hρ : nAux D 0 / 2 = D.R.rS := by
    obtain ⟨a, ha⟩ := D.R.m_even
    unfold nAux Ranks.rS
    omega
  have sym : ∀ x y, (D.sp.Y 0).hT x y = 0 → (D.sp.Y 0).hT y x = 0 := fun x y h => by
    rw [← (D.sp.Y 0).herm.eq x y, h, map_zero]
  unfold IsAuxiliaryHeckeCharacter HSpace.hD
  rw [hρ]
  refine ⟨fun i hi l hl => ?_, fun i hi x => ?_, fun _ => ⟨D.sp.zm_norm, D.sp.zm_orth, fun i hi => ?_⟩⟩
  · simp only [dif_pos hi, dif_pos hl]
    refine ⟨D.sp.hyp_ee _ _, D.sp.hyp_ff _ _, ?_⟩
    rw [← (D.sp.Y 0).herm.eq, D.sp.hyp_ef]
    by_cases h : i = l <;> simp [h]
  · simp only [dif_pos hi]
    exact D.sp.hyp_orthX _ x
  · simp only [dif_pos hi]
    exact D.sp.hyp_orthz _

end GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory Formalism.L2.Theta
open Formalism.IndefR
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsDefiniteSpace (V : HSp D) : Prop := V.SigOK ∧ V.IsDefinite

def IsOpenCompactLevel (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) : Prop :=
  IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) ∧ IsCompact ((Lev.levA V K : Subgroup (GA D V)) : Set (GA D V))

def levelFin (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) : Subgroup (Bridge.Gf V) :=
  (Lev.toAfE V K).comap (finHom V).range.subtype

def classGroupAt (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (x : Bridge.Gf V) : Subgroup (GQ V) :=
  Bridge.stab (Bridge.ratF V) (levelFin V K) x

structure IsClassFun (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (Φ : GA D V → ℂ) : Prop where

  left : ∀ γ ∈ GQ V, ∀ h, Φ (γ * h) = Φ h

  real : ∀ k ∈ GinfC V, ∀ h, Φ (h * k) = Φ h

  level : ∀ k ∈ Lev.levA V K, ∀ h, Φ (h * k) = Φ h

def ClassSumIntegral : Prop :=
  ∀ (D : D7) (V : HSp D), IsDefiniteSpace V →
    ∀ (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))), IsOpenCompactLevel V K →
      ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), Links.IsMeasDef V K μ 𝓕 →
        ∀ (I : Type) [Fintype I] (y : I → Bridge.Gf V), Bridge.IsReps (Bridge.ratF V) (levelFin V K) y →
          ∀ (z : I → GA D V), (∀ i, (finHom V).rangeRestrict (z i) = y i) →
            ∀ (Φ : GA D V → ℂ), IsClassFun V K Φ →
              (∀ i, Finite (classGroupAt V K (y i))) ∧ IntegrableOn Φ 𝓕 μ ∧
                ∫ h in 𝓕, Φ h ∂μ = ∑ i, ((Nat.card (classGroupAt V K (y i)) : ℂ))⁻¹ * Φ (z i)

variable {V : HSp D} {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))}

theorem map_conj_inv {G H : Type} [Group G] [Group H] (f : G →* H) (a b : G) : f (a⁻¹ * b * a) = (f a)⁻¹ * f b * f a := by
  rw [map_mul, map_mul, map_inv]

theorem mem_levelFin (w : GA D V) : (finHom V).rangeRestrict w ∈ levelFin V K ↔ Lev.finE V w ∈ K := Iff.rfl

theorem mem_classGroupAt (z : GA D V) (γ : GQ V) :
    γ ∈ classGroupAt V K ((finHom V).rangeRestrict z) ↔ Lev.finE V (z⁻¹ * (γ : GA D V) * z) ∈ K := by
  unfold classGroupAt
  rw [Bridge.mem_stab]
  have e : ((finHom V).rangeRestrict z)⁻¹ * Bridge.ratF V γ * (finHom V).rangeRestrict z =
      (finHom V).rangeRestrict (z⁻¹ * (γ : GA D V) * z) := by
    have e0 : Bridge.ratF V γ = (finHom V).rangeRestrict (γ : GA D V) := by
      simp only [Bridge.ratF, MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [e0]
    exact (map_conj_inv (finHom V).rangeRestrict z γ).symm
  rw [e]
  exact mem_levelFin _

end GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev Formalism.IndefR.Links
open Formalism.IndefR.Datum (IsSelfDualC)
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev OA (D : D7) : Subring (EAf D) := Formalism.L2.Herm.intAf D.host.F D.host.E

abbrev inc (D : D7) : D.host.E →+* EAf D := Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)

abbrev cjA (D : D7) : EAf D →+* EAf D := Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)

abbrev Lat (V : HSp D) : Type := Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)

def hat {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → EAf D) :=
  {y | y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ}

def hA (V : HSp D) (x y : Fin V.rank → EAf D) : EAf D :=
  Formalism.UG.hform (cjA D) (V.gram.map (inc D)) y x

def vA (V : HSp D) (z : V.V) : Fin V.rank → EAf D := fun i => inc D (Formalism.L2.Herm.crd V z i)

def mA (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) : Matrix (Fin Y.rank) (Fin X.rank) (EAf D) :=
  (frameMat Y X ι).map (inc D)

def IsPlIdem (w : Pl D.host.E) (e : EAf D) : Prop :=
  ∃ he : e ∈ OA D, e * e = e ∧ resS D.host.F w ⟨e, he⟩ = 1 ∧
    ∀ w' : Pl D.host.E, w' ≠ w → resS D.host.F w' ⟨e, he⟩ = 0

def InCmp {n : ℕ} (e : EAf D) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (y : Fin n → EAf D) : Prop :=
  y ∈ hat Λ ∧ e • y = y

def IsSplitSet (S : Finset (Pl D.host.E)) : Prop := ∀ w ∈ S, ∀ w' ∈ S, ¬ Formalism.IndefR.Lev.IsConjPl w w'

def IsBasisAt (V : HSp D) (w : Pl D.host.E) (Λ : Lat V) {n : ℕ} (B : Matrix (Fin V.rank) (Fin n) (EAf D)) : Prop :=
  n = V.rank ∧ ∃ e, IsPlIdem w e ∧ e • B = B ∧
    ∀ y, InCmp e Λ y ↔ ∃ c : Fin n → OA D, y = B *ᵥ fun i => (c i : EAf D)

def IsVecBasisAt (V : HSp D) (w : Pl D.host.E) (B : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) : Prop :=
  ∃ e, IsPlIdem w e ∧ e • B = B ∧ ∃ C : Matrix (Fin V.rank) (Fin V.rank) (EAf D),
    B * C = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D))

def IsAdIsom (W Y : HSp D) (x : Matrix (Fin Y.rank) (Fin W.rank) (EAf D)) : Prop :=
  Function.Bijective (x.mulVec : (Fin W.rank → EAf D) → (Fin Y.rank → EAf D)) ∧
    ∀ a b, hA Y (x *ᵥ a) (x *ᵥ b) = hA W a b

def IsTransport (W Y : HSp D) (L : Lat W) (Λ : Lat Y) (S : Finset (Pl D.host.E)) {n : ℕ}
    (be : Pl D.host.E → Matrix (Fin W.rank) (Fin n) (EAf D)) (be' : Pl D.host.E → Matrix (Fin Y.rank) (Fin n) (EAf D))
    (x : Matrix (Fin Y.rank) (Fin W.rank) (EAf D)) : Prop :=
  IsAdIsom W Y x ∧ (∀ a, a ∈ hat L ↔ x *ᵥ a ∈ hat Λ) ∧ ∀ w ∈ S, x * be w = be' w

def InStabAway (W : HSp D) (L : Lat W) (S : Finset (Pl D.host.E)) (k : GL (Fin W.rank) (EAf D)) : Prop :=
  k ∈ Formalism.UG.levelAfL D.sp.cm.sig W.gram L ∧
    ∀ w ∈ S, Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) (w.under (𝓞 D.host.F))) k = 1

def PlIdemSt (D : D7) : Prop := ∀ w : Pl D.host.E, ∃! e : EAf D, IsPlIdem w e

def TransportSt (D : D7) : Prop :=
  ∀ (W Y : HSp D), W.rank = Y.rank → ∀ (L : Lat W) (Λ : Lat Y), IsSelfDualC W L → IsSelfDualC Y Λ →
    ∀ S : Finset (Pl D.host.E), IsSplitSet S → ∀ (n : ℕ)
      (be : Pl D.host.E → Matrix (Fin W.rank) (Fin n) (EAf D)) (be' : Pl D.host.E → Matrix (Fin Y.rank) (Fin n) (EAf D)),
      (∀ w ∈ S, IsBasisAt W w L (be w)) → (∀ w ∈ S, IsBasisAt Y w Λ (be' w)) →
      (∃ x, IsTransport W Y L Λ S be be' x) ∧
      ∀ x, IsTransport W Y L Λ S be be' x → ∀ x',
        IsTransport W Y L Λ S be be' x' ↔
          ∃ k, InStabAway W L S k ∧ x' = HMul.hMul x (k.1 : Matrix (Fin W.rank) (Fin W.rank) (EAf D))

def CorrectionSt (D : D7) : Prop :=
  ∀ (Y Y' : HSp D) (io : Y.V ≃ₗ[D.host.E] Y'.V), HSpace.IsIsomEmb Y Y' io.toLinearMap →
    ∀ (Λ : Lat Y) (Λ' : Lat Y'), IsSelfDualC Y Λ → IsSelfDualC Y' Λ' →
    ∀ S : Finset (Pl D.host.E), IsSplitSet S → ∀ (n : ℕ)
      (be : Pl D.host.E → Matrix (Fin Y.rank) (Fin n) (EAf D)) (be' : Pl D.host.E → Matrix (Fin Y'.rank) (Fin n) (EAf D)),
      (∀ w ∈ S, IsBasisAt Y w Λ (be w)) → (∀ w ∈ S, IsBasisAt Y' w Λ' (be' w)) →
      ∃ k ∈ GfC Y', IsTransport Y Y' Λ Λ' S be be'
        (HMul.hMul ((finE Y' k).1 : Matrix (Fin Y'.rank) (Fin Y'.rank) (EAf D)) (mA Y' Y io.toLinearMap))

def SplitGlueSt (D : D7) : Prop :=
  ∀ (V : HSp D) (Λ₀ : Lat V), IsSelfDualC V Λ₀ → ∀ S : Finset (Pl D.host.E), IsSplitSet S →
    ∀ B : Pl D.host.E → Matrix (Fin V.rank) (Fin V.rank) (EAf D), (∀ w ∈ S, IsVecBasisAt V w (B w)) →
      ∃! Λ : Lat V, IsSelfDualC V Λ ∧ (∀ w ∈ S, IsBasisAt V w Λ (B w)) ∧
        ∀ v : HeightOneSpectrum (𝓞 D.host.F), (∀ w ∈ S, w.under (𝓞 D.host.F) ≠ v) →
          Formalism.L2.Herm.locL v Λ = Formalism.L2.Herm.locL v Λ₀

def ImageSt (D : D7) : Prop :=
  ∀ (V : HSp D) (Λ : Lat V), IsSelfDualC V Λ → ∀ d ∈ GfC V,
    (∃ Λ' : Lat V, Submodule.IsLattice D.host.E Λ' ∧ Formalism.L2.Herm.Carries (finE V d) Λ Λ') ∧
    ∀ Λ' : Lat V, Submodule.IsLattice D.host.E Λ' → Formalism.L2.Herm.Carries (finE V d) Λ Λ' → IsSelfDualC V Λ'

def RationalSt (D : D7) : Prop :=
  ∀ W Y : HSp D, W.SigOK → Y.SigOK → W.rank = Y.rank → (∀ τ, W.sig τ = Y.sig τ) →
    ∃ φ : W.V ≃ₗ[D.host.E] Y.V, HSpace.IsIsomEmb W Y φ.toLinearMap

structure IsDec (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) {a ρ : ℕ} (z : Fin a → Y.V) (c : D.host.E)
    (e f : Fin ρ → Y.V) : Prop where
  isom : HSpace.IsIsomEmb X Y ι
  a_le : a ≤ 1
  rank : Y.rank = X.rank + a + 2 * ρ
  z_norm : ∀ i, Y.hD (z i) (z i) = c
  z_X : ∀ i x, Y.hD (ι x) (z i) = 0
  ee : ∀ i j, Y.hD (e i) (e j) = 0
  ff : ∀ i j, Y.hD (f i) (f j) = 0
  ef : ∀ i j, Y.hD (e i) (f j) = if i = j then 1 else 0
  hyp_X : ∀ i x, Y.hD (ι x) (e i) = 0 ∧ Y.hD (ι x) (f i) = 0
  hyperbolicDecomp_hyp_orthogonal_line : ∀ i j, Y.hD (z j) (e i) = 0 ∧ Y.hD (z j) (f i) = 0

abbrev Tu (D : D7) (u : D.what₂.Word) : D.host.E := ((D.mem u).A.T : D.host.E)

def IsPi (u : D.what₂.Word) (π : 𝓞 D.host.E) : Prop :=
  (π : D.host.E) ∈ D.host.K ∧ (π : D.host.E) * star (π : D.host.E) = Tu D u

def StdIsomSt (D : D7) : Prop :=
  ∀ u : D.what₂.Word, (∃ π, IsPi u π) ∧ ∀ π, IsPi u π → ∀ (s : ℤˣ) (a ρ : ℕ)
    (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Fin a → Y.V) (e f : Fin ρ → Y.V)
    (Y' X' : HSp D) (ι' : X'.V →ₗ[D.host.E] Y'.V) (z' : Fin a → Y'.V) (e' f' : Fin ρ → Y'.V),
    IsDec Y X ι z (((s : ℤ) : D.host.E) * Tu D u) e f → IsDec Y' X' ι' z' ((s : ℤ) : D.host.E) e' f' →
    X.SigOK → X'.SigOK → X.IsPosDef → X'.IsPosDef → X.rank = X'.rank →
    ∃ (φ : X.V ≃ₗ[D.host.E] X'.V) (io : Y.V ≃ₗ[D.host.E] Y'.V),
      HSpace.IsIsomEmb X X' φ.toLinearMap ∧ HSpace.IsIsomEmb Y Y' io.toLinearMap ∧
      (∀ x, io (ι x) = ι' (φ x)) ∧ (∀ i, io (z i) = (π : D.host.E) • z' i) ∧ ∀ i, io (e i) = e' i ∧ io (f i) = f' i

def RecordDecSt (D : D7) : Prop :=
  (∀ u, IsDec (D.sp.Y 0) (D.sp.X 0) (D.sp.iXY 0) (fun _ : Fin 1 => D.zmOf u) (-Tu D u) D.sp.hypE D.sp.hypF) ∧
  ∃ z' : (D.sp.Y 0).V, IsDec (D.sp.Y 0) (D.sp.X 0) (D.sp.iXY 0) (fun _ : Fin 1 => z') (-1) D.sp.hypE D.sp.hypF

section Flat

variable (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V)

def flatSp : Submodule D.host.E Y.V := LinearMap.range ι ⊔ Submodule.span D.host.E {z}

def IsSDIn (U : Submodule D.host.E Y.V) (L : Submodule (𝓞 D.host.E) Y.V) : Prop :=
  L.FG ∧ Submodule.span D.host.E (L : Set Y.V) = U ∧
    ∀ y ∈ U, y ∈ L ↔ ∀ x ∈ L, Y.hD x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range

def IsPrim (L : Submodule (𝓞 D.host.E) Y.V) : Prop :=
  ∀ a : D.host.E, a • z ∈ L ↔ a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range

def capX (L : Submodule (𝓞 D.host.E) Y.V) : Lat X :=
  Formalism.L2.Herm.crdLat X (L.comap (ι.restrictScalars (𝓞 D.host.E)))

def IsBasePair (u : D.what₂.Word) (π : 𝓞 D.host.E) (L₀ : Lat X) (f₀ : Pl D.host.E → Fin X.rank → EAf D) : Prop :=
  Submodule.IsFullLattice D.host.E L₀ ∧
  (∀ (w : Pl D.host.E) (e : EAf D), IsPlIdem w e → (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal →
    ∀ y, InCmp e L₀ y ↔ InCmp e (Formalism.L2.Herm.dualL D.sp.cm X L₀) y) ∧
  ∀ (w : Pl D.host.E) (e : EAf D), IsPlIdem w e → π ∈ w.asIdeal →
    e • f₀ w = f₀ w ∧ inc D (Tu D u) • f₀ w ∈ hat L₀ ∧ f₀ w ∉ hat L₀ ∧
    ∀ y, InCmp (cjA D e) L₀ y ↔
      cjA D e • y = y ∧ (∀ x, InCmp e L₀ x → hA X x y ∈ OA D) ∧ hA X (f₀ w) y ∈ OA D

def IsGlued (u : D.what₂.Word) (π : 𝓞 D.host.E) (L₀ : Lat X) (f₀ : Pl D.host.E → Fin X.rank → EAf D)
    (L : Submodule (𝓞 D.host.E) Y.V) : Prop :=
  L.FG ∧
  (∀ (w : Pl D.host.E) (e : EAf D), IsPlIdem w e → (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal →
    ∀ y, InCmp e (Formalism.L2.Herm.crdLat Y L) y ↔
      ∃ x, InCmp e L₀ x ∧ ∃ a ∈ OA D, y = mA Y X ι *ᵥ x + (a * e) • vA Y z) ∧
  ∀ (w : Pl D.host.E) (e : EAf D), IsPlIdem w e → π ∈ w.asIdeal →
    (∀ y, InCmp e (Formalism.L2.Herm.crdLat Y L) y ↔
      ∃ x, InCmp e L₀ x ∧ ∃ a ∈ OA D,
        y = mA Y X ι *ᵥ x + a • ((inc D (Tu D u)⁻¹ * e) • vA Y z + mA Y X ι *ᵥ f₀ w)) ∧
    ∀ y, InCmp (cjA D e) (Formalism.L2.Herm.crdLat Y L) y ↔
      cjA D e • y = y ∧ (∃ (x : Fin X.rank → EAf D) (a : EAf D), y = mA Y X ι *ᵥ x + a • vA Y z) ∧
        ∀ y', InCmp e (Formalism.L2.Herm.crdLat Y L) y' → hA Y y' y ∈ OA D

def lamN {ρ : ℕ} (e f : Fin ρ → Y.V) (L : Submodule (𝓞 D.host.E) Y.V)
    (nn : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) Y.V :=
  (⨆ i : Fin ρ, ((nn ^ (ρ - i.val) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E).map
      ((LinearMap.toSpanSingleton D.host.E Y.V (e i)).restrictScalars (𝓞 D.host.E))) ⊔ L ⊔
  ⨆ i : Fin ρ, (((nn ^ (ρ - i.val))⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E).map
      ((LinearMap.toSpanSingleton D.host.E Y.V (f i)).restrictScalars (𝓞 D.host.E))

end Flat

def IsLine (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V) (u : D.what₂.Word) : Prop :=
  HSpace.IsIsomEmb X Y ι ∧ (∀ x, Y.hD (ι x) z = 0) ∧ Y.hD z z = -Tu D u

def GluedSt (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (π : 𝓞 D.host.E), IsPi u π → ∀ (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V),
    IsLine Y X ι z u → ∀ (L₀ : Lat X) (f₀ : Pl D.host.E → Fin X.rank → EAf D), IsBasePair X u π L₀ f₀ →
      (∃! L, IsGlued Y X ι z u π L₀ f₀ L) ∧
      ∀ L, IsGlued Y X ι z u π L₀ f₀ L → IsSDIn Y (flatSp Y X ι z) L ∧ IsPrim Y z L ∧ capX Y X ι L = L₀

def UngluedSt (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (π : 𝓞 D.host.E), IsPi u π → ∀ (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V),
    IsLine Y X ι z u → ∀ L, IsSDIn Y (flatSp Y X ι z) L → IsPrim Y z L →
      ∃ f₀, IsBasePair X u π (capX Y X ι L) f₀ ∧ IsGlued Y X ι z u π (capX Y X ι L) f₀ L

def IsCStable (nn : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Prop :=
  nn ≠ 0 ∧ ∀ x : D.host.E, x ∈ nn ↔ star x ∈ nn

def LamNSt (D : D7) : Prop :=
  (∀ (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V) (ρ : ℕ) (e f : Fin ρ → Y.V),
    IsDec Y X ι (fun _ : Fin 1 => z) (-Tu D u) e f → ∀ L, IsSDIn Y (flatSp Y X ι z) L →
      ∀ nn, IsCStable nn → IsSelfDualC Y (Formalism.L2.Herm.crdLat Y (lamN Y e f L nn))) ∧
  IsCStable ((D.host.ddE : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹ ∧
  IsCStable (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ *
    D.host.AA * D.host.AAbar)

def FrameSt (D : D7) : Prop :=
  (∀ (V : HSp D) (N : ℕ), ∃ β Λ, IsSDFrame V β Λ N) ∧
  ∀ (V : HSp D) (Λ : Lat V) (N c : ℕ), IsSelfDualC V Λ → 0 < N →
    (∀ x ∈ L0c D V, ((N ^ c : ℕ) : D.host.E) • x ∈ Λ) → (∀ x ∈ Λ, ((N ^ c : ℕ) : D.host.E) • x ∈ L0c D V) →
    ∀ S : Finset (Pl D.host.E), IsSplitSet S → ∀ be : Pl D.host.E → Matrix (Fin V.rank) (Fin V.rank) (EAf D),
      (∀ w ∈ S, IsBasisAt V w Λ (be w)) →
      ∃ β, IsSDFrame V β Λ N ∧ ∀ w ∈ S, ∀ e, IsPlIdem w e →
        e • (β.1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) = be w

def AdelicIsometries (D : D7) : Prop :=
  PlIdemSt D ∧ TransportSt D ∧ CorrectionSt D ∧ SplitGlueSt D ∧ ImageSt D ∧ RationalSt D ∧ StdIsomSt D ∧ RecordDecSt D ∧
    GluedSt D ∧ UngluedSt D ∧ LamNSt D ∧ FrameSt D

end GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents

end
end

