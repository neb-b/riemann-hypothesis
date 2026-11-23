module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Formalism.LocalRingCardinality.Bundle0005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotInhAbsOfGamLe
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S

namespace GlobalTheory.Core.Rk

def IdE {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : Prop := ∀ x : X.B.I.E, HEq (X.ιE x) x


open GlobalTheory.Mem GlobalTheory.Mem.Col2 in
def TrueE (D : D7) : Prop :=
  ∃ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)),
    D = I.rec7 l Z ∧ ∃ w : World I l Z, IdE w.S.X

theorem TrueE.trueD {D : D7} (h : TrueE D) : TrueD D :=
  let ⟨B, X, I, l, Z, e, w, _⟩ := h; ⟨B, X, I, l, Z, e, ⟨w⟩⟩


def HD (D : D7) (L C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  Formalism.BasicNotions.Ties D ∧ Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D ∧ Deg.HypL D L C' Cl Cg cb Cu cT CT ∧ Deg.DataNW D ∧ Formalism.L2.SG.RowsConc.TFrameAt D

def LedE (D : D7) (L C' : ℝ) : Prop := ∃ large₂ : SizeData₂ D, large₂.sc.L = L ∧ 8 * large₂.CGam ≤ C'

def GamLe (D : D7) (L C' : ℝ) : Prop := ∀ u : D.what₂.Word, 8 * Real.log (D.mem u).A.GamP ≤ C' * mfL D L

def Row (E : D7 → ℝ → ℝ → Prop) (Q : ∀ D : D7, D.what₂.Word → ℝ → ℝ → Prop) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ C C'₀ Cl₀ : ℝ, 1 ≤ C ∧ ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : ℝ) (u : D.what₂.Word), TrueE D → E D L C' → HD D L C' Cl Cg cb Cu cT CT → Q D u L C

variable (E : D7 → ℝ → ℝ → Prop)

def RowDiag : Prop := Row E fun D u L C => SDiag D u L C

def RKRowAbs : Prop := Row E fun D u L C => RankMu D u → C * D.R.f * D.R.k * L ≤ Real.log (D.mem u).A.GamP → RK D u

def Inh (P : ∀ D : D7, D.what₂.Word → ℝ → ℝ → Prop) : Prop :=
  ∃ Cg cb Cu cT CT : ℝ, 0 < cb ∧ 0 < cT ∧ ∀ C C'₀ Cl₀ : ℝ, ∃ (C' Cl L : ℝ) (D : D7), C'₀ ≤ C' ∧ Cl₀ ≤ Cl ∧
    TrueE D ∧ E D L C' ∧ HD D L C' Cl Cg cb Cu cT CT ∧ ∀ u, P D u L C

def InhAbs : Prop := Inh E fun D u L C => RankMu D u ∧ C * D.R.f * D.R.k * L ≤ Real.log (D.mem u).A.GamP

variable {E}

theorem Inh.reach {P Q : ∀ D : D7, D.what₂.Word → ℝ → ℝ → Prop} (h : Inh E P) (h' : Row E fun D u L C => P D u L C → Q D u L C) :
    ∃ (D : D7) (L C : ℝ), TrueE D ∧ 1 ≤ C ∧ ∀ u, Q D u L C :=
  let ⟨Cg, cb, Cu, cT, CT, h1, h2, h⟩ := h
  let ⟨C, a, b, hC, h'⟩ := h' Cg cb Cu cT CT h1 h2
  let ⟨C', Cl, L, D, ha, hb, hD, he, hH, hP⟩ := h C a b
  ⟨D, L, C, hD, hC, fun u => h' C' Cl ha hb D L u hD he hH (hP u)⟩

theorem Inh.not_row_false {P : ∀ D : D7, D.what₂.Word → ℝ → ℝ → Prop} (h : Inh E P) :
    ¬ Row E fun D u L C => P D u L C → False := fun h' =>
  let ⟨D, _, _, _, _, h⟩ := h.reach (Q := fun _ _ _ _ => False) h'
  h D.u₀

theorem one_le_mfL {D : D7} {L C' Cl Cg cb Cu cT CT : ℝ} (hH : Deg.HypL D L C' Cl Cg cb Cu cT CT) :
    1 ≤ mfL D L ∧ 16 ≤ D.R.k ∧ 1 ≤ D.R.f := by
  obtain ⟨h1, -, h3, h4, -⟩ := hH
  have hm := D.R.two_le_m
  have h16 : 2 ^ 4 ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm 4
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by omega : 1 ≤ D.R.f)
  have hm' : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 5 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ D.R.m))
  refine ⟨?_, by omega, by omega⟩
  unfold mfL
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hm' hf) h1.le

theorem LedE.gamLe {D : D7} {L C' : ℝ} (h : LedE D L C') : GamLe D L C' := by
  obtain ⟨large₂, hL, h8⟩ := h
  intro u
  have hG := large₂.Gam_eq u
  have hL0 : 0 ≤ L := hL ▸ Real.rpow_nonneg (zero_le_one.trans large₂.sc.one_lt_alt.le) _
  rw [hL] at hG
  have hx : 0 ≤ mfL D L := by unfold mfL; positivity
  have e : Real.log (D.mem u).A.GamP = large₂.CGam * mfL D L := by rw [hG]; unfold mfL; ring
  rw [e]
  nlinarith

theorem GamLe.le_k {D : D7} {L C' Cl Cg cb Cu cT CT : ℝ} (h : GamLe D L C') (hH : Deg.HypL D L C' Cl Cg cb Cu cT CT)
    (u : D.what₂.Word) : 8 * Real.log (D.mem u).A.GamP ≤ D.R.k := by
  refine (h u).trans (le_trans (le_of_eq ?_) hH.2.1)
  unfold mfL
  ring

theorem GamLe.log_lt {D : D7} {L C C' Cl Cg cb Cu cT CT : ℝ} (h : GamLe D L C') (hH : Deg.HypL D L C' Cl Cg cb Cu cT CT)
    (hC : 1 ≤ C) (u : D.what₂.Word) : Real.log (D.mem u).A.GamP < C * D.R.f * D.R.k * L := by
  have h1 := h.le_k hH u
  obtain ⟨-, hk, hf⟩ := one_le_mfL hH
  have hk' : (16 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hf' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have a : (1 : ℝ) ≤ C * D.R.f * L := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC hf') hH.1.le
  nlinarith

theorem RKRowAbs.of_gamLe (hE : ∀ D L C', E D L C' → GamLe D L C') : RKRowAbs E :=
  fun _ _ _ _ _ _ _ => ⟨1, 0, 0, le_rfl, fun _ _ _ _ _ _ u _ he hH _ h =>
    absurd h (not_le.2 ((hE _ _ _ he).log_lt hH.2.2.1 le_rfl u))⟩

theorem not_inhAbs_of_gamLe (hE : ∀ D L C', E D L C' → GamLe D L C') : ¬ InhAbs E := fun h =>
  Inh.not_row_false h fun _ _ _ _ _ _ _ => ⟨1, 0, 0, le_rfl, fun _ _ _ _ _ _ u _ he hH h =>
    absurd h.2 (not_le.2 ((hE _ _ _ he).log_lt hH.2.2.1 le_rfl u))⟩

end GlobalTheory.Core.Rk

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
section
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Core.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Dense

variable {V W : HSp D} {S S' : D.what₂.Tau → SPar}


open Classical in
def SepCont (M : DSModel V S) (Λ : SmT M →ₗ[ℂ] ℂ) : Prop :=
  ∀ τ (v : M.Vec), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
    ∀ w : M.sm τ, ℓ w = Λ (PiTensorProduct.tprod ℂ (Function.update v τ w))

def KVecP (M : DSModel V S) (v : M.Vec) : Prop := ∀ τ, IsKFin (M.ε τ) (M.σ τ) (v τ : M.H τ)

def ItSpans (M : DSModel V S) (M' : DSModel W S') (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) : Prop :=
  ∀ v : M.Vec, KVecP M v → PiTensorProduct.tprod ℂ v ∈
    Submodule.span ℂ {x | ∃ (P : PolF D W.rank V.rank) (y : M'.Vec), KVecP M' y ∧ x = It P (PiTensorProduct.tprod ℂ y)}

end Dense

def PropTo {I : Type} (f τ : I → ℂ) : Prop := ∃ a : ℂ, ∀ i, f i = a * τ i

def DenseExt (D : D7) : Prop :=
  ∀ (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (S : D.what₂.Tau → SPar) (M : DSModel B.V S)
    (J : Set (GA D B.V)) (χ : GA D B.V → ℂ) (t : GA D B.V) (I : Type) (τ : I → ℂ) (φ : I → GA D B.A → ℂ)
    (T : I → SmT M →ₗ[ℂ] (GA D B.V → ℂ)), IsInfFam θ → IsStdChar D ψ (-1) → (∀ i, IsContAut B.A (φ i)) →
    (∀ i, T i ∈ MultT θ M J χ) →
    (∀ v : M.Vec, KVecP M v → PropTo (fun i => B.per ψ (φ i) (rTrans t (T i (PiTensorProduct.tprod ℂ v)))) τ) →
    ∀ x : SmT M, PropTo (fun i => B.per ψ (φ i) (rTrans t (T i x))) τ

def TowerSpans (W : Tower D) : Prop :=
  (∀ k, k + 1 < D.R.m → ItSpans (W.MY k) (W.MY (k + 1)) (W.ItY k)) ∧ ItSpans (W.MY (D.R.m - 1)) W.MX W.ItX

section Model

variable (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)

def IdE : Prop := ∀ x : X.B.I.E, HEq (X.ιE x) x

def rowJ : Set (GA D (D.sp.Y 0)) := iotaX X h ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}

def rowChi (k : GA D (D.sp.Y 0)) : ℂ := star (X.chi2 (iotaX X h k).2)

def Matches (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) : Prop :=
  t ∈ GfC (D.sp.Y 0) ∧ ConjLevel t⁻¹ J χ (rowJ X h) (rowChi X h)

def evS (t : GA D (D.sp.Y 0)) (F : GA D (D.sp.Y 0) → ℂ) : X.B.I.GA → ℂ := fun x => F ((iotaX X h).symm x * t)

def ConjVec (θ : InfFam D) {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S) (v₀ : M.Vec) : Prop :=
  ∃ c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ),
    (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) =
      X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) ∧
    ∀ τ, c τ (v₀ τ : M.H τ) = X.B.w (X.pl.symm τ)

def RealSplit (θ : InfFam D) : Prop :=
  (∀ k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) ↔ (iotaX X h k).1 = 1) ∧
  (∀ k : GA D (D.sp.Y 0), k ∈ GinfC (D.sp.Y 0) ↔ (iotaX X h k).2 = 1) ∧
  (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (iotaX X h (atTau θ (D.sp.Y 0) τ g)).2 = 1 ∧
    (∀ v, v ≠ X.pl.symm τ → (iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 v = 1) ∧
    HEq (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ)))
      ((fun Pm : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ => Pm⁻¹ * g * Pm)
        ((Formalism.L2.SG.InstExistsPf.instOf D).P (Formalism.L2.Host.tauPl D τ)))) ∧
  ∀ τ (y : Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))), ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ),
    (iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ) = y

def EvalAll (θ : InfFam D) {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0)))
    (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec) : Prop :=
  ∃ j : MultT θ M J χ →ₗ⋆[ℂ] HHX X, Function.Bijective j ∧ ∀ T : MultT θ M J χ,
    (((j T : HHX X) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X] fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x)

structure RowFun (f : X.B.I.GA → ℂ) : Prop where
  cont : Continuous f
  bdd : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C
  left : ∀ γ ∈ X.B.I.GFset, ∀ x, f (γ * x) = f x
  right : ∀ k ∈ X.K2, ∀ x, f (x * (1, k)) = star (X.chi2 k) * f x

structure SBes (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) where
  V₀ : HSp D
  L : HSp D
  d : HypDec (D.sp.Y 0) V₀ D.R.rS
  o : OrthDec V₀ A L
  ζ : Fin L.rank → D.host.E
  line : IsLineVec L ζ
  cpt : CoCpt A
  vA : Vol A
  vN : VolN d
  tieN : ∀ n, n ∈ flagN d ↔ (iotaX X h n).1 ∈ X.NinfU u ∧ (iotaX X h n).2 ∈ X.NfinU u
  tieH : ∀ g, g ∈ (embA d o).range ↔ (iotaX X h g).1 ∈ Hinf X u ∧ (iotaX X h g).2 ∈ Hfin X u
  tieψ : ∀ n ∈ flagN d, star (psiBes ψ d 1 (vecB o ζ) n) = X.psiInfU u (iotaX X h n).1 * X.psiFinU u (iotaX X h n).2

namespace SBes

variable {X h} {u : D.what₂.Word} {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A)

abbrev lev : BesLev D D.R.rS := ⟨D.sp.Y 0, B.V₀, A, B.L, B.d, B.o, B.ζ, B.line, B.cpt, B.vA, B.vN⟩

def toH (a : GA D A) : Hinf X u × Hfin X u :=
  (⟨(iotaX X h (embA B.d B.o a)).1, ((B.tieH _).1 ⟨a, rfl⟩).1⟩, ⟨(iotaX X h (embA B.d B.o a)).2, ((B.tieH _).1 ⟨a, rfl⟩).2⟩)

def colForm (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (ξ : X.Vpi u) : GA D A → ℂ := fun a => T ξ (B.toH a)

def PerLaw (Y : Formalism.L2.SG.Full.Full X) : Prop :=
  ∃ c : ℂ, ∀ (T : Cu X u Y.hK) (f : X.B.I.GA → ℂ) (φ : L2X X), RowFun X f → (φ : X.B.I.GA → ℂ) =ᵐ[muX X] f →
    ⟪star φ, PuFun X u Y.hK (Y.Dt u) T⟫_ℂ =
      c * ∫ y, B.lev.per ψ (B.colForm T.1 (X.Wu u y)) (fun g => f (iotaX X h g * (y, X.xu u))) ∂(X.nuQ u)

end SBes

theorem rank_eq (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) : (D.sp.Y 0).rank = X.B.I.n := by
  rw [h]; rfl

def SBes.Adapted {X : HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
    {ψ : AddChar (AF D.host.F) ℂ} (B : SBes X h u ψ (D.sp.X 0)) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  ∀ k j, (B.d.i₀ * B.o.iA) k j = X.ιE (X.crd (Formalism.L2.SG.ColDict.qFr wt
    (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) j)) (Fin.cast (rank_eq X h) k))

end Model

section MI

variable {F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u} (S : STrue D F₀) (u : D.what₂.Word) (W : Tower D) (L : Link D u W)

end MI


end GlobalTheory.Core.Mi

end
end

