module

public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0003
public import Mathlib

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open scoped ComplexOrder

namespace Formalism.L2.Geo

section Abs

variable {K : Type} [Field K] [NumberField K]

end Abs

namespace FormsPkg

variable {D : D7} {G : DV.Geo D.what₂.LL} {NW : ℕ → ℕ} {CompW : ℕ → Type} [∀ j, Fintype (CompW j)]
  {algW : ∀ j, AlgPkg G D.what₂.Tau (NW j) (CompW j)} {PtY : ℕ → ℕ → Type}
  (P : FormsPkg D G NW CompW algW PtY)

def scalL (j : ℕ) : P.Forms j →ₗ[P.KO] P.KO where
  toFun x := P.scal (x : P.FormsS j)
  map_add' x y := P.scal_add x y
  map_smul' a x := P.scal_smul a x

def cuspF (j : ℕ) : Submodule P.KO (P.Forms j) := LinearMap.ker (P.scalL j)

theorem inc_mem_cuspF {j : ℕ} {w : WeightFamilies.Wt D j} (F : P.Cusp j w) : P.inc j w F ∈ P.cuspF j :=
  P.scal_incS F

variable {j : ℕ}


section Gauss

variable (la : HeightOneSpectrum (𝓞 P.KO)) (y : P.Pt j la)

end Gauss

end FormsPkg

variable {D : D7} {G : DV.Geo D.what₂.LL} {Lev : Type}


open Classical in
structure FormsKPkg (F : ShimFam D G Lev) : Type 1 where

  κs : Lev

  fs : FormsPkg D G (fun j => (datW D κs j).N) (fun j => (F.U (datW D κs j)).Comp)
    (fun j => (F.U (datW D κs j)).alg)
    (fun j p => ((F.U (datW D κs j)).pad.loc p).Pt ((F.U (datW D κs j)).pad.loc p).YY)

  Hb : Type
  [grpHb : Group Hb]
  [act : ∀ j, MulSemiringAction Hb (fs.Forms j)]

  act_smul : ∀ j (h : Hb) (a : fs.KO) (x : fs.Forms j), h • (a • x) = a • (h • x)

  act_wt : ∀ j (h : Hb) (w : WeightFamilies.Wt D j) (F : fs.Cusp j w), ∃ F' : fs.Cusp j w, h • fs.inc j w F = fs.inc j w F'

  mv : ∀ j (la : HeightOneSpectrum (𝓞 fs.KO)), Hb → fs.Pt j la → fs.Pt j la

  vAt_act : ∀ j la (h : Hb) (y : fs.Pt j la) (x : fs.Forms j), fs.vAt la y (h • x) = fs.vAt la (mv j la h y) x

  ip : ∀ j, (fs.KO →+* ℂ) → fs.Forms j → fs.Forms j → ℂ
  ip_add_left : ∀ j σ (f f' g : fs.Forms j), f ∈ fs.cuspF j → f' ∈ fs.cuspF j → g ∈ fs.cuspF j →
    ip j σ (f + f') g = ip j σ f g + ip j σ f' g
  ip_add_right : ∀ j σ (f g g' : fs.Forms j), f ∈ fs.cuspF j → g ∈ fs.cuspF j → g' ∈ fs.cuspF j →
    ip j σ f (g + g') = ip j σ f g + ip j σ f g'
  ip_smul_left : ∀ j σ (a : fs.KO) (f g : fs.Forms j), f ∈ fs.cuspF j → g ∈ fs.cuspF j →
    ip j σ (a • f) g = star (σ a) * ip j σ f g
  ip_smul_right : ∀ j σ (a : fs.KO) (f g : fs.Forms j), f ∈ fs.cuspF j → g ∈ fs.cuspF j →
    ip j σ f (a • g) = σ a * ip j σ f g
  ip_conj : ∀ j σ (f g : fs.Forms j), f ∈ fs.cuspF j → g ∈ fs.cuspF j → ip j σ g f = star (ip j σ f g)
  ip_nonneg : ∀ j σ (f : fs.Forms j), f ∈ fs.cuspF j → 0 ≤ (ip j σ f f).re

  ip_inc : ∀ j σ (w : WeightFamilies.Wt D j) (F : fs.Cusp j w), ip j σ (fs.inc j w F) (fs.inc j w F) = ((fs.l2NormAlt j w σ F ^ 2 : ℝ) : ℂ)

  ip_orth : ∀ j σ (w w' : WeightFamilies.Wt D j) (F : fs.Cusp j w) (F' : fs.Cusp j w'), w ≠ w' →
    ip j σ (fs.inc j w F) (fs.inc j w' F') = 0
  ip_act : ∀ j σ (h : Hb) (f g : fs.Forms j), f ∈ fs.cuspF j → g ∈ fs.cuspF j → ip j σ (h • f) (h • g) = ip j σ f g

  supv : ∀ j, (fs.KO →+* ℂ) → fs.Forms j → ℝ
  supv_inc : ∀ j σ (w : WeightFamilies.Wt D j) (F : fs.Cusp j w), supv j σ (fs.inc j w F) = fs.supN j w σ F
  supv_act : ∀ j σ (h : Hb) (u : fs.Forms j), supv j σ (h • u) = supv j σ u
  ip_mul : ∀ j σ (f u : fs.Forms j), f ∈ fs.cuspF j → u ∈ fs.cuspF j →
    (ip j σ (f * u) (f * u)).re ≤ supv j σ u ^ 2 * (ip j σ f f).re

  CmpK : ℕ → Type
  [cmpKFin : ∀ j, Fintype (CmpK j)]

  orbK : ∀ j, (F.U (datW D κs j)).Comp → CmpK j
  orbK_surj : ∀ j, Function.Surjective (orbK j)

  cmpPt : ∀ j la, fs.Pt j la → CmpK j

  prC : ∀ j, CmpK j → fs.cuspF j →ₗ[fs.KO] fs.cuspF j
  prC_sum : ∀ j (x : fs.cuspF j), ∑ c, prC j c x = x
  prC_orth : ∀ j c d (x : fs.cuspF j), c ≠ d → prC j c (prC j d x) = 0

  prC_inc : ∀ j o (w : WeightFamilies.Wt D j) (F : fs.Cusp j w), ∃ F' : fs.Cusp j w,
    (prC j o ⟨fs.inc j w F, fs.inc_mem_cuspF F⟩ : fs.Forms j) = fs.inc j w F' ∧
      ∀ c', fs.cmp j w c' F' = if orbK j c' = o then fs.cmp j w c' F else 0
  vAt_prC_self : ∀ j la (y : fs.Pt j la) (x : fs.cuspF j),
    fs.vAt la y (prC j (cmpPt j la y) x : fs.Forms j) = fs.vAt la y (x : fs.Forms j)
  vAt_prC_ne : ∀ j la (y : fs.Pt j la) c (x : fs.cuspF j), c ≠ cmpPt j la y → fs.vAt la y (prC j c x : fs.Forms j) = ⊤
  ip_prC : ∀ j σ c d (f g : fs.cuspF j), c ≠ d → ip j σ (prC j c f : fs.Forms j) (prC j d g : fs.Forms j) = 0

  ip_posDef : ∀ j σ (m : ℕ) (e : Fin m → fs.Forms j), (∀ a, e a ∈ fs.cuspF j) → LinearIndependent fs.KO e →
    (Matrix.of fun a c => ip j σ (e a) (e c)).PosDef

attribute [instance] FormsKPkg.grpHb FormsKPkg.act FormsKPkg.cmpKFin

namespace FormsKPkg

variable {F : ShimFam D G Lev} (P : FormsKPkg F)

end FormsKPkg

end Formalism.L2.Geo
