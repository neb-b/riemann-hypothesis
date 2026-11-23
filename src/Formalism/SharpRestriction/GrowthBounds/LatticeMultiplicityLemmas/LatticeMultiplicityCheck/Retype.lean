module

public import Formalism.SharpRestriction.SmoothDesignExistence.SumOverPrimesHypotheses

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.TwTie

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.MainNotions

structure KerAtMu (D : D7) (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}
    (Ch : Chain Lv) where

  fl_t : Fl.t = D.R.t
  fl_m : Fl.mm = D.R.m

  cls : ∀ j, Lv.comp j → (Fl.Pj j).Tup → (D.chTw u μ).cls j

  cls_iff : ∀ j, j ≤ D.R.m → ∀ (a a' : Lv.comp j) (L L' : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    (Fl.Pj j).IsLatTup L' →
    (cls j a L = cls j a' L' ↔ a = a' ∧ ∃ γ : (Lv.lev j a).Γ, L' = (Lv.lev j a).smul γ L)
  cls_surj : ∀ j, j ≤ D.R.m → ∀ x : (D.chTw u μ).cls j, ∃ a L, (Fl.Pj j).IsLatTup L ∧ cls j a L = x

  stab_zero : ∀ (a : Lv.comp 0) (L : (Fl.Pj 0).Tup), (Fl.Pj 0).IsLatTup L →
    Nat.card {γ : (Lv.lev 0 a).Γ // (Lv.lev 0 a).smul γ L = L} = 1

  stab_dvd : ∀ j, j ≤ D.R.m → ∀ (a : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    0 < Nat.card {γ : (Lv.lev j a).Γ // (Lv.lev j a).smul γ L = L} ∧
      Nat.card {γ : (Lv.lev j a).Γ // (Lv.lev j a).smul γ L = L} ∣ (D.mem u).C.DGam

  cmp : ∀ j, ((Tw.fm u μ).lat j).V →ₛₗ[c.embW u w h] Lv.Fm j
  cmp_inj : ∀ j, j ≤ D.R.m → Function.Injective (cmp j)

  cmp_zero : ∀ x : ((D.fm u).lat 0).V, cmp 0 (Tw.e0 u μ x) = c.cmp u w h x

  cmp_int : ∀ j, j ≤ D.R.m → Submodule.span (D.gat u w h).O
    (cmp j '' (((Tw.fm u μ).lat j).L : Set ((Tw.fm u μ).lat j).V)) = Lv.Int j

  cmp_K : ∀ j, j < D.R.m → ∀ (x : ((Tw.fm u μ).lat j).V) (y : ((Tw.fm u μ).lat (j + 1)).V),
    (Tw.fm u μ).emb (j + 1) y = (D.chTw u μ).K j ((Tw.fm u μ).emb j x) →
    cmp (j + 1) y = Ch.Kz j (cmp j x)

  rat : ∀ j, j < D.R.m → (Tw.fm u μ).KRat j

  val : ∀ (y : ((Tw.fm u μ).lat D.R.m).V) (s : ℝ),
    vGeLat (D.gat u w h) (Lv.Int D.R.m) (cmp D.R.m y) s → WeilJacquetShalikaLaw.VGe D w ((Tw.fm u μ).lat D.R.m).L y s

end Formalism.MainNotions.G.TwTie
