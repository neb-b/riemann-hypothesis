module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.HtPsiLeIffExists
section
noncomputable section

namespace GlobalTheory.Core.Rk

open NumberField Formalism.BasicNotions

variable (D : D7) (u : D.what₂.Word)

abbrev Pt : HLat D.what₂.LL := (D.fm u).ptLat

def IsPsi (Ψ : (D.div.Nu u).V →ₗ[D.what₂.LL] (Pt D u).V) : Prop :=
  ∀ x : (D.div.Nu u).V, (D.fm u).ptEmb (Ψ x) = PsiC (D.mem u).C (D.mem u).A (D.mem u).P (D.eMu u (D.jN u x))

def PsiRat : Prop := ∃ Ψ, IsPsi D u Ψ


open Classical in
def Psi : (D.div.Nu u).V →ₗ[D.what₂.LL] (Pt D u).V := if h : PsiRat D u then h.choose else 0

theorem isPsi_Psi (h : PsiRat D u) : IsPsi D u (Psi D u) := by
  unfold Psi; rw [dite_eq_left h]; exact h.choose_spec

def htPsi : ℝ := Formalism.HN.htMap (D.div.Nu u).b (D.div.Nu u).X (Pt D u).b (Pt D u).X (Psi D u)

def HtPsiLe (h : ℝ) : Prop := PsiRat D u ∧ (Psi D u ≠ 0 → htPsi D u ≤ h)

def PsiInt (N : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) : Prop :=
  PsiRat D u ∧ ∀ x ∈ N, Psi D u x ∈ (Pt D u).L

variable (Am : AmbForm D (RowSide.sharp D))

def IsPer (e : (Pt D u).V ≃ₗ[D.what₂.LL] (MtDual D Am).V) : Prop :=
  ∀ (x : (Pt D u).V) (z : (Mt D Am).V),
    D.what₂.embLL ((show Module.Dual D.what₂.LL (Mt D Am).V from e x) z) =
      (D.mem u).P.period ((D.fm u).ptEmb x) ((D.eMt u).symm (Am.jAmb D.what₂.mu0 z))

theorem IsPer.isPhi_comp {e} (he : IsPer D u Am e) {Ψ} (h : IsPsi D u Ψ) : IsPhi D Am u (e.toLinearMap ∘ₗ Ψ) := fun x z => by
  refine (he (Ψ x) z).trans ?_
  rw [h x]
  exact (PhiC_apply _ _ _ _ _).trans (D.perCol_base_eq_PtilCol u _ _).symm

def AmbMetric : Prop :=
  ∃ e, IsPer D u Am e ∧ ∀ (v : InfinitePlace D.what₂.LL) (x : (Pt D u).V),
    Formalism.HermitianLatticesTheory.normAt (MtDual D Am).b (MtDual D Am).X v (e x) = Formalism.HermitianLatticesTheory.normAt (Pt D u).b (Pt D u).X v x

def AmbLattice : Prop :=
  ∃ e, IsPer D u Am e ∧ (∀ x, e x ∈ (MtDual D Am).L → x ∈ (Pt D u).L) ∧
    ∀ x ∈ (Pt D u).L, ((D.mem u).C.DGam : D.what₂.LL) • e x ∈ (MtDual D Am).L

end GlobalTheory.Core.Rk

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealisedChainTorusEq
section
noncomputable section

namespace GlobalTheory.Core.Rk

open Formalism.BasicNotions

def TInAt (D : D7) (u : D.what₂.Word) (D' : D7) (u' : D'.what₂.Word) (r s : ℝ) : Prop :=
  Real.log (D.mem u).A.Xu - r ≤ Real.log ((D'.mem u').A.T : ℝ) ∧ Real.log ((D'.mem u').A.T : ℝ) ≤ s

def SameTops (D D' : D7) : Prop :=
  ∀ (τ : D.what₂.Tau) (τ' : D'.what₂.Tau) (t : D.host.TT) (t' : D'.host.TT) (h : 0 < D.R.k) (h' : 0 < D'.R.k),
    (D.eTau τ : D.R.GG) = D.R.tau1 t → (D'.eTau τ' : D'.R.GG) = D'.R.tau1 t' →
    (t : D.R.A).val = (t' : D'.R.A).val →
      (D.hc τ).u ⟨0, h⟩ = (D'.hc τ').u ⟨0, h'⟩ ∧
        (D.hc τ).u ⟨D.R.k - 1, by omega⟩ = (D'.hc τ').u ⟨D'.R.k - 1, by omega⟩

structure SameHost (D D' : D7) : Prop where

  R_eq : D.R = D'.R

  TT_eq : D.host.TT.image Formalism.HC.Frame.A.val = D'.host.TT.image Formalism.HC.Frame.A.val
  realisedChain_torus_eq : D.host.T2 = D'.host.T2
  q_eq : D.host.q = D'.host.q
  d_eq : D.host.d = D'.host.d
  g_eq : D.host.g = D'.host.g
  pde_eq : D.host.pde = D'.host.pde
  pde'_eq : D.host.pde' = D'.host.pde'

  QS_eq : D.host.QS = D'.host.QS

  art_eq : ∀ (p : ℕ) (h : Nat.Coprime p D.host.condN) (h' : Nat.Coprime p D'.host.condN),
    (D.host.art (ZMod.unitOfCoprime p h)).1 = (D'.host.art (ZMod.unitOfCoprime p h')).1 ∧
      (D.R.iotaInv (D.host.art (ZMod.unitOfCoprime p h)).2).val = (D'.R.iotaInv (D'.host.art (ZMod.unitOfCoprime p h')).2).val

theorem SameHost.condN_eq {D D' : D7} (h : SameHost D D') : D.host.condN = D'.host.condN := by
  show D.host.QS * D.host.q * D.host.d = D'.host.QS * D'.host.q * D'.host.d
  rw [h.QS_eq, h.q_eq, h.d_eq]

theorem SameHost.refl (D : D7) : SameHost D D := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩

theorem SameHost.trans {D D' D'' : D7} (h : SameHost D D') (h' : SameHost D' D'') : SameHost D D'' :=
  ⟨h.1.trans h'.1, h.2.trans h'.2, h.3.trans h'.3, h.4.trans h'.4, h.5.trans h'.5, h.6.trans h'.6, h.7.trans h'.7, h.8.trans h'.8,
    h.9.trans h'.9, fun p k k'' =>
      have k' : Nat.Coprime p D'.host.condN := h.condN_eq ▸ k
      ⟨(h.art_eq p k k').1.trans (h'.art_eq p k' k'').1, (h.art_eq p k k').2.trans (h'.art_eq p k' k'').2⟩⟩

structure SameWord (D : D7) (u : D.what₂.Word) (D' : D7) (u' : D'.what₂.Word) : Prop where
  host : SameHost D D'
  unitVector_val_eq : D.host.u0.val = D'.host.u0.val
  hc_eq : ∀ (τ : D.what₂.Tau) (τ' : D'.what₂.Tau), HEq (D.eTau τ) (D'.eTau τ') → HEq (D.hcW u τ) (D'.hcW u' τ')

structure Pts where

  Ix : ℝ → Type

  D : ∀ x, Ix x → D7

  Ix_ne : ∀ y, ∃ x, y ≤ x ∧ Nonempty (Ix x)

  same : ∀ x (i i' : Ix x), SameHost (D x i) (D x i')

namespace Pts

theorem ne_of_forall {Ix : ℝ → Type} (h : ∀ x, Nonempty (Ix x)) : ∀ y, ∃ x, y ≤ x ∧ Nonempty (Ix x) :=
  fun y => ⟨y, le_rfl, h y⟩

def single (D : ℝ → D7) : Pts :=
  ⟨fun _ => Unit, fun x _ => D x, ne_of_forall fun _ => ⟨()⟩, fun _ _ _ => SameHost.refl _⟩

variable (F : Pts)

def SomeAt (Q : ℝ → ∀ D : D7, D.what₂.Word → Prop) : Prop :=
  ∃ x₀ : ℝ, ∀ x, x₀ ≤ x → ∀ (i₀ : F.Ix x) (u₀ : ℕ), u₀ < (F.D x i₀).R.n →
    ∃ i : F.Ix x, (F.D x i).host.u0.val = u₀ ∧ SameTops (F.D x i) (F.D x i₀) ∧ ∃ u, Q x (F.D x i) u

def RKAll : Prop := ∃ x₀ : ℝ, ∀ x, x₀ ≤ x → ∀ i : F.Ix x, ∃ u, RK (F.D x i) u

def RKRoomOver (Tr : ℝ → D7 → Prop) (ε : ℝ) : Prop :=
  ∃ CR CT : ℝ, F.SomeAt fun x D u => ∃ (D' : D7) (u' : D'.what₂.Word), Tr x D' ∧ SameWord D u D' u' ∧
    TInAt D u D' u' (CR * x ^ ε) (CT * D.R.m * x ^ ε) ∧ RK D' u'

def Covered : Prop :=
  ∃ x₀ : ℝ, ∀ x, x₀ ≤ x → ∀ (i₀ : F.Ix x) (u₀ : ℕ), u₀ < (F.D x i₀).R.n →
    ∃ i : F.Ix x, (F.D x i).host.u0.val = u₀ ∧ SameTops (F.D x i) (F.D x i₀)

variable {F}

theorem SomeAt.exists {Q : ℝ → ∀ D : D7, D.what₂.Word → Prop} (h : F.SomeAt Q) :
    ∃ x₀ : ℝ, ∀ x, x₀ ≤ x → Nonempty (F.Ix x) → ∃ (i : F.Ix x) (u : (F.D x i).what₂.Word), Q x (F.D x i) u := by
  obtain ⟨x₀, h⟩ := h
  refine ⟨x₀, fun x hx ⟨i₀⟩ => ?_⟩
  obtain ⟨i, -, -, u, hu⟩ := h x hx i₀ 0 (F.D x i₀).R.ord_pos
  exact ⟨i, u, hu⟩

theorem SomeAt.exists_ge {Q : ℝ → ∀ D : D7, D.what₂.Word → Prop} (h : F.SomeAt Q) (y : ℝ) :
    ∃ x, y ≤ x ∧ ∃ (i : F.Ix x) (u : (F.D x i).what₂.Word), Q x (F.D x i) u := by
  obtain ⟨x₀, h⟩ := h.exists
  obtain ⟨x, hx, hne⟩ := F.Ix_ne (max x₀ y)
  exact ⟨x, le_of_max_le_right hx, h x (le_of_max_le_left hx) hne⟩

theorem not_rkRoomOver {ε : ℝ} {Tr : ℝ → D7 → Prop} (hT : ∀ x D u, Tr x D → ¬ RK D u) : ¬ F.RKRoomOver Tr ε := by
  rintro ⟨CR, CT, h⟩
  obtain ⟨x, -, i, u, D', u', h1, -, -, h2⟩ := h.exists_ge 0
  exact hT _ _ _ h1 h2

end Pts

namespace Pts

variable {F : Pts}

end Pts

section Hyp

variable (Fam : ℝ → Type 1) (Cl : ∀ ε, Fam ε → Prop) (pts : ∀ ε, Fam ε → Pts) (Form : ℝ → Pts → Prop)

end Hyp

end GlobalTheory.Core.Rk

end
end

