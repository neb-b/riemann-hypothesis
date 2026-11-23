module

public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.IsComplRatCompl

@[expose] public section

open Formalism.MainNotions.G Formalism.BasicNotions NumberField

noncomputable section

namespace Formalism.L2.G.Cmp

section Maps

variable {D : D7} (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} (Lv : Levels Fl)

structure CmpMaps where
  cmp : ∀ j, ((Tw.fm u (D.what₂.muAt w)).lat j).V →ₛₗ[c.embW u w h] Lv.Fm j
  li : ∀ j, j ≤ D.R.m → LinearIndependent (D.gat u w h).Kf
    fun a => cmp j (((Tw.fm u (D.what₂.muAt w)).lat j).b a)

variable {c Tw u w h Lv}

theorem CmpMaps.inj (M : CmpMaps c Tw u w h Lv) (j : ℕ) (hj : j ≤ D.R.m) : Function.Injective (M.cmp j) :=
  inj_of_li (M.cmp j) ((Tw.fm u (D.what₂.muAt w)).lat j).b (M.li j hj)


variable (Tw u w) in
def KLx (j : ℕ) : ((Tw.fm u (D.what₂.muAt w)).lat j).V →ₗ[D.what₂.LL] ((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).V :=
  ratMap ((Tw.fm u (D.what₂.muAt w)).emb j) ((Tw.fm u (D.what₂.muAt w)).emb (j + 1))
    ((Tw.fm u (D.what₂.muAt w)).emb_inj (j + 1)) ((D.chTw u (D.what₂.muAt w)).Klin j)

theorem KLx_eq (j : ℕ) (x : ((Tw.fm u (D.what₂.muAt w)).lat j).V) (y : ((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).V)
    (hxy : (Tw.fm u (D.what₂.muAt w)).emb (j + 1) y =
      (D.chTw u (D.what₂.muAt w)).K j ((Tw.fm u (D.what₂.muAt w)).emb j x)) : KLx Tw u w j x = y :=
  ratMap_eq _ _ _ _ x y hxy



open Classical in
def chainFirst (M : CmpMaps c Tw u w h Lv) : Chain Lv where
  Kz j := if hj : j < D.R.m then
      extK (M.cmp j) (M.cmp (j + 1)) ((Tw.fm u (D.what₂.muAt w)).lat j).b (M.li j hj.le) (KLx Tw u w j)
    else 0

theorem chainFirst_Kz (M : CmpMaps c Tw u w h Lv) (j : ℕ) (hj : j < D.R.m) :
    (chainFirst M).Kz j =
      extK (M.cmp j) (M.cmp (j + 1)) ((Tw.fm u (D.what₂.muAt w)).lat j).b (M.li j hj.le) (KLx Tw u w j) :=
  dif_pos hj

theorem chainFirst_apply (M : CmpMaps c Tw u w h Lv) (j : ℕ) (hj : j < D.R.m)
    (x : ((Tw.fm u (D.what₂.muAt w)).lat j).V) :
    (chainFirst M).Kz j (M.cmp j x) = M.cmp (j + 1) (KLx Tw u w j x) := by
  rw [chainFirst_Kz M j hj, extK_apply]

theorem chainFirst_cmp_K (M : CmpMaps c Tw u w h Lv) : ∀ j, j < D.R.m →
    ∀ (x : ((Tw.fm u (D.what₂.muAt w)).lat j).V) (y : ((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).V),
    (Tw.fm u (D.what₂.muAt w)).emb (j + 1) y = (D.chTw u (D.what₂.muAt w)).K j ((Tw.fm u (D.what₂.muAt w)).emb j x) →
    M.cmp (j + 1) y = (chainFirst M).Kz j (M.cmp j x) := by
  intro j hj x y hxy
  rw [chainFirst_apply M j hj, KLx_eq j x y hxy]

end Maps

section Vram

variable {D : D7} (c : LatCmp D)

def vramC (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Submodule (D.gat u w hg).O (D.gat u w hg).Fn :=
  (Submodule.span (D.gat u w hg).Kf
    (c.cmp u w hg '' ((D.fm u).ramSub : Set ((D.fm u).lat 0).V))).restrictScalars (D.gat u w hg).O

end Vram

end Formalism.L2.G.Cmp

end
