module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd

@[expose] public section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7}

def inN (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) {n : ℕ} (hn : V.rank = n) (g : GA D V) :
    D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ := fun τ => (inB θ V B g τ).reindex (finCongr hn) (finCongr hn)

def castP {p q a b : ℕ} (hp : p = a) (hq : q = b) : PolF D q p →ₐ[ℂ] FP D.what₂.Tau a b :=
  MvPolynomial.rename fun v => (v.1, Fin.cast hq v.2.1, Fin.cast hp v.2.2)

structure RealD (c : Comm D) where

  N : ℕ → ℕ
  hN : ∀ j, j ≤ D.R.m → (c.X j).rank = N j

  NT : ℕ
  hT : c.T.rank = NT

  fr : ∀ j, c.Fr j ≃ FrN D (N j)

  lam : ∀ j, D.what₂.Tau → DomWeight (N j)
  n : ℕ → D.what₂.Tau → ℕ
  sS : ℕ → D.what₂.Tau → ℤ
  sD : ℕ → D.what₂.Tau → ℤ
  sc : ℕ → D.what₂.Tau → ℂ

  BT : D.what₂.Tau → Matrix (Fin c.T.rank) (Fin c.T.rank) ℂ
  sg : D.what₂.Tau → DomWeight NT

  J : SmT c.MT → GA D c.T → FrN D NT → ℂ

  low : ∀ n, n = D.R.m → ((FrN D (N n) → ℂ) →ₗ[ℂ] (FrN D NT → ℂ))

namespace RealD

variable {c : Comm D} (ρ : RealD c)

abbrev r (j : ℕ) (hj : j ≤ D.R.m) (g : GA D (c.X j)) := inN c.θ (c.X j) (c.x j).B (ρ.hN j hj) g

abbrev rT (g : GA D c.T) := inN c.θ c.T ρ.BT ρ.hT g

structure Is : Prop where
  uni : ∀ j hj, OntoUni fun k : GinfC (c.X j) => ρ.r j hj k.1
  uniT : OntoUni fun k : GinfC c.T => ρ.rT k.1
  rk : ∀ j, j < D.R.m → 0 < ρ.N j ∧ ρ.N j ≤ ρ.N (j + 1)
  sc : ∀ j τ, ρ.sc j τ ≠ 0
  n : ∀ j, j < D.R.m → ∀ τ, (ρ.n j τ : ℤ) = shiftOf (ρ.lam j) τ + ρ.sS j τ
  J : ∀ v, ρ.J v 1 ∈ ValC _ ρ.sg ∧ ∀ k ∈ GinfC c.T, ∀ z z', IsTr (ρ.rT k) z z' → ρ.J v k z' = ρ.J v 1 z
  low : ∀ n (h : n = D.R.m), ∃ hN : ρ.N n = ρ.NT + 1,
    (∀ τ, Formalism.L2.Col.Br.Interlace hN (ρ.lam n τ) (ρ.sg τ)) ∧ BrEqv hN _ _ (ρ.lam n) ρ.sg (ρ.low n h) ∧
    (∃ Φ ∈ ValC _ (ρ.lam n), ρ.low n h Φ ≠ 0) ∧
    ∀ k ∈ GinfC c.T, ∀ τ, GlobalTheory.BranchFormula.IsBlock hN (ρ.r n h.le ((c.oT n h).emb (k, 1)) τ) (ρ.rT k τ) 1

end RealD

structure ClsK {c : Comm D} (ρ : RealD c) (t : Tup c) where
  cl : ∀ j, t.Ch j → Type
  [fin : ∀ j β, Fintype (cl j β)]
  U : ∀ j, t.Ch j → Subgroup (GA D (c.X j))
  chi : ∀ j β, U j β →* ℂˣ
  h : ∀ j β, cl j β → GA D (c.X j)

  val : ∀ j β, t.Col j → cl j β → FrN D (ρ.N j) → ℂ

  abelian₂ : ∀ j α γ, cl j α → cl (j + 1) γ → (FP D.what₂.Tau (ρ.N j) (ρ.N (j + 1)) →ₗ[ℂ] ℂ)

attribute [instance] ClsK.fin

namespace ClsK

variable {c : Comm D} {ρ : RealD c} {t : Tup c} (A : ClsK ρ t)

structure Forms : Prop where
  reps : ∀ j, j ≤ D.R.m → ∀ β, IsReps (c.X j) (A.U j β) (A.h j β)
  chi : ∀ j, j ≤ D.R.m → ∀ β, Continuous fun κ => ((A.chi j β κ : ℂˣ) : ℂ)
  valC : ∀ j, j ≤ D.R.m → ∀ ψ ∈ t.Ram j, ∀ β a, A.val j β ψ a ∈ ValC _ (ρ.lam j)

  rd : ∀ j hj, ∀ ψ ∈ t.Ram j, ∀ β y, ∀ γ ∈ GQ (c.X j), ∀ a, ∀ k ∈ GinfC (c.X j), ∀ (κ : A.U j β) y',
    IsTr (ρ.r j hj k) (ρ.fr j y) y' → t.rd j β ψ y (γ * (A.h j β a * k) * κ.1) = (A.chi j β κ : ℂ) * A.val j β ψ a y'

def Real (_A : ClsK ρ t) : Prop :=
  ∀ j (hj : j + 1 ≤ D.R.m) α γ, ∀ k ∈ GinfC (c.X j), ∀ k' ∈ GinfC (c.X (j + 1)), ∀ P P',
    castP (ρ.hN j (Nat.le_of_succ_le hj)) (ρ.hN (j + 1) hj) P' =
      mvZ (fun τ => (ρ.r j (Nat.le_of_succ_le hj) k τ)⁻¹) (ρ.r (j + 1) hj k')
        (castP (ρ.hN j (Nat.le_of_succ_le hj)) (ρ.hN (j + 1) hj) P) →
    t.kom j (k, k') ((t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P) =
      (∏ τ, (ρ.r j (Nat.le_of_succ_le hj) k τ).det ^ ρ.sS j τ * (ρ.r (j + 1) hj k' τ).det ^ (-ρ.sD j τ)) •
        (t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P'

def Lev : Prop :=
  ∀ j, j < D.R.m → ∀ α γ (κ : A.U j α) (κ' : A.U (j + 1) γ),
    t.kom j (κ.1, κ'.1) (comb c.ψ _ _ (t.dd j α γ) (c.vac j)) =
      (((A.chi j α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (j + 1) γ κ' : ℂˣ) : ℂ)) • comb c.ψ _ _ (t.dd j α γ) (c.vac j)

def Core : Prop :=
  ∀ j (hj : j + 1 ≤ D.R.m) α γ a a' P,
    (volLev (c.x j).vol (A.U j α) : ℂ) *
        thetaKO (t.kom j) (A.h j α a) (A.h (j + 1) γ a') ((t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P) =
      t.cK j * A.abelian₂ j α γ a a' (mvZ (fun _ => 1) (fun τ => ρ.sc j τ • 1)
        (castP (ρ.hN j (Nat.le_of_succ_le hj)) (ρ.hN (j + 1) hj) P))

def Kval : Prop :=
  ∀ j, j < D.R.m → ∀ (hab : ρ.N j ≤ ρ.N (j + 1)), ∀ ψ ∈ t.Ram j,
    ∀ F : ∀ α, A.cl j α → PY D.what₂.Tau (ρ.N j), (∀ α a, F α a ∈ Vn (ρ.lam j) (ρ.n j)) →
      (∀ α a y, A.val j α ψ a y = evalAt y.1 (F α a) * ∏ τ, (y.1 τ).det ^ (-ρ.sS j τ)) →
      ∀ γ a' y', A.val (j + 1) γ (t.K j ψ) a' y' =
        ∑ α, ∑ a, ((stabOrd (A.U j α) (A.h j α a) : ℕ) : ℂ)⁻¹ * A.abelian₂ j α γ a a' (subY hab y'.1 (F α a)) *
          ∏ τ, (y'.1 τ).det ^ (-ρ.sD j τ)

def Is : Prop := A.Forms ∧ A.Real ∧ A.Lev ∧ A.Core ∧ A.Kval

end ClsK

structure ClsT {c : Comm D} (ρ : RealD c) (t : Tup c) where
  cl : Type
  [fin : Fintype cl]
  U : Subgroup (GA D c.T)
  h : cl → GA D c.T

  ell : ∀ n, n = D.R.m → t.Ch n → cl → t.CT → ((FrN D ρ.NT → ℂ) →ₗ[ℂ] ℂ)

attribute [instance] ClsT.fin

structure ClsT.Is {c : Comm D} {ρ : RealD c} {t : Tup c} (A : ClsT ρ t) : Prop where
  reps : IsReps c.T A.U A.h

  inv : ∀ n (h : n = D.R.m), ∀ ψ ∈ t.Ram n, ∀ (G : t.CT) v y β g, ∀ κ ∈ A.U,
    trc (t.eT n h β) (G.1 v) (g * κ) * t.rd n β ψ y ((c.oT n h).emb (g * κ, 1)) =
      trc (t.eT n h β) (G.1 v) g * t.rd n β ψ y ((c.oT n h).emb (g, 1))

  top : ∀ n (h : n = D.R.m) (G : t.CT) v β a, ∀ k ∈ GinfC c.T,
    trc (t.eT n h β) (G.1 v) (A.h a * k) = A.ell n h β a G (ρ.J v k)

  tail : ∀ n (h : n = D.R.m), ∀ ψ ∈ t.Ram n, ∀ G : t.CT,
    (volLev c.volT A.U : ℂ) * ∑ β, ∑ a, ((stabOrd A.U (A.h a) : ℕ) : ℂ)⁻¹ *
        A.ell n h β a G (ρ.low n h fun z => t.rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (A.h a, 1))) =
      t.cP * t.tail n h ψ G

def ClsPinD {c : Comm D} {𝒯 : Type} (t : 𝒯 → Tup c) : Prop :=
  ∃ ρ : RealD c, ρ.Is ∧ ∀ s, (∃ A : ClsK ρ (t s), A.Is) ∧ ∃ A : ClsT ρ (t s), A.Is

namespace Sized

theorem castP_rank {p q : ℕ} (P : PolF D q p) : castP (D := D) (rfl : p = p) (rfl : q = q) P = P := by
  have : (fun v : FVar D q p => ((v.1, Fin.cast rfl v.2.1, Fin.cast rfl v.2.2) : FVar D q p)) = id := by funext v; rfl
  unfold castP
  rw [this]; exact MvPolynomial.rename_id_apply P

theorem castP_bijective {p q a b : ℕ} (hp : p = a) (hq : q = b) : Function.Bijective (castP (D := D) hp hq) := by
  subst hp; subst hq
  have : (castP (D := D) (rfl : p = p) (rfl : q = q) : _ → _) = id := funext castP_rank
  rw [this]; exact Function.bijective_id

end Sized

@[reducible] def Comm.onFrames (c : Comm D) (N : ℕ → ℕ) : Comm D := { c with Fr := fun j => FrN D (N j) }

@[reducible] def Tup.onFrames {c : Comm D} (t : Tup c) {N : ℕ → ℕ} (fr : ∀ j, j ≤ D.R.m → (c.Fr j ≃ FrN D (N j))) :
    Tup (c.onFrames N) where
  om := t.om
  omT := t.omT
  pt := t.pt
  ptT := t.ptT
  sBF := t.sBF
  sFB := t.sFB
  CC := t.CC
  CT := t.CT
  io := t.io
  ioT := t.ioT
  kom := t.kom
  Ch := t.Ch
  dd := t.dd
  e := t.e
  eT := t.eT
  Col := t.Col
  Ram := t.Ram
  S := t.S
  K := t.K
  rd := fun j β ψ z => if hj : j ≤ D.R.m then t.rd j β ψ ((fr j hj).symm z) else 0
  tail := t.tail
  cI := t.cI
  cV := t.cV
  cK := t.cK
  cP := t.cP

def ClsPinF {c : Comm D} {𝒯 : Type} (t : 𝒯 → Tup c) : Prop :=
  ∃ (N : ℕ → ℕ) (fr : ∀ j, j ≤ D.R.m → (c.Fr j ≃ FrN D (N j))), ClsPinD fun s => (t s).onFrames fr

section Frames

variable {c : Comm D} {N : ℕ → ℕ} (fr : ∀ j, j ≤ D.R.m → (c.Fr j ≃ FrN D (N j)))

variable {𝒯 : Type} {t : 𝒯 → Tup c}

end Frames

@[reducible] def RealD.onFrames {c : Comm D} (ρ : RealD c) : RealD (c.onFrames ρ.N) :=
  ⟨ρ.N, ρ.hN, ρ.NT, ρ.hT, fun _ => Equiv.refl _, ρ.lam, ρ.n, ρ.sS, ρ.sD, ρ.sc, ρ.BT, ρ.sg, ρ.J, ρ.low⟩

end GlobalTheory.SeeSaw

end
