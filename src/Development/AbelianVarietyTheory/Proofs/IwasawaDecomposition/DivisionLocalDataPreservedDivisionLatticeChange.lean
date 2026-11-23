module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0598

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.WitTr

open Formalism.L2.Geo
open Formalism.L2.Geo.PadPkg renaming md → padMd
open Formalism.L2.Geo.CompatiblePlaces' renaming md → tiedMd

open DivX (md) in
@[reducible] def divXTr {B : Base} {f : Fr B.toPre} {T : TwDat B}
    (w : ColW B f T) (Z : w.Lt) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V)
    (h : B.Word → ℝ) (Y : DivX (w.D Z)) : DivX (w.D (setDivZ Z N h)) :=
  { Y with md := fun S κ p _ la z => { md Y S κ p la z with } }

namespace GeoDivTr

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}
variable (col : ColW B f T) (Z : col.Lt)
variable (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)

local notation "D₀" => col.D Z
local notation "D₁" => col.D (setDivZ Z N h)


set_option maxHeartbeats 4000000 in
@[reducible] def datBk {Lev : Type} (w : Dat D₁ Lev) : Dat D₀ Lev := { w with }


set_option maxHeartbeats 4000000 in
@[reducible] def mdlT {p : ℕ} [Fact p.Prime] {M : ℕ} {rk : DV.Emb D₀ p → ℕ} (m : DV.Mdl D₀ p M rk) : DV.Mdl D₁ p M rk := { m with }


set_option maxHeartbeats 4000000 in
@[reducible] def locT {M j p : ℕ} (l : ModuliIntegralCharts.Loc D₀ M j p) : ModuliIntegralCharts.Loc D₁ M j p := { l with }


set_option maxHeartbeats 4000000 in
@[reducible] def padT {M j : ℕ} {Comp : Type} {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D₀ p → (DV.KW p →+* ℂ)} {ng : NgPkg}
    (P : PadPkg D₀ M j Comp jC ng) : PadPkg D₁ M j Comp jC ng :=
  { P with
    loc := fun p => locT col Z N h (P.loc p)
    ex := fun p => { P.ex p with }
    locB := fun p hp => { P.locB p hp with }
    pbKF := fun p _ k => P.pbKF p k
    bc := fun p z => P.bc p z
    md := fun p _ la z => mdlT col Z N h (padMd P p la z) }


set_option maxHeartbeats 4000000 in
@[reducible] def shimUT {G : DV.Geo (D₀).what₂.LL} {Lev : Type} {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D₀ p → (DV.KW p →+* ℂ)} {ng : NgPkg}
    {w : Dat D₁ Lev} (U : ShimU D₀ G jC ng (datBk col Z N h w)) : ShimU D₁ G jC ng w :=
  { U with alg := { U.alg with }, pad := padT col Z N h U.pad }

@[reducible] def wtB {j : ℕ} (w : WeightFamilies.Wt D₁ j) : WeightFamilies.Wt D₀ j := { w with }


set_option maxHeartbeats 8000000 in
@[reducible] def formsT {G : DV.Geo (D₀).what₂.LL} {NW : ℕ → ℕ} {CompW : ℕ → Type} [∀ j, Fintype (CompW j)]
    {algW : ∀ j, AlgPkg G (D₀).what₂.Tau (NW j) (CompW j)} {PtY : ℕ → ℕ → Type}
    (P : FormsPkg D₀ G NW CompW algW PtY) :
    FormsPkg D₁ G NW CompW (fun j => { algW j with }) PtY where
  KO := P.KO
  fKO := P.fKO
  nfKO := P.nfKO
  eO := P.eO
  kL := P.kL
  kL_eO := P.kL_eO
  Cusp := fun j w => P.Cusp j (wtB col Z N h w)
  acgC := fun j w => P.acgC j (wtB col Z N h w)
  modC := fun j w => P.modC j (wtB col Z N h w)
  fdC := fun j w => P.fdC j (wtB col Z N h w)
  modOC := fun j w => P.modOC j (wtB col Z N h w)
  towC := fun j w => P.towC j (wtB col Z N h w)
  cmp := fun j w c => P.cmp j (wtB col Z N h w) c
  cmp_mem := fun j w c F => P.cmp_mem j (wtB col Z N h w) c F
  cmp_cusp := fun j w c F => P.cmp_cusp j (wtB col Z N h w) c F
  cmp_span := fun j h1 h2 w s hs => P.cmp_span j h1 h2 (wtB col Z N h w) s hs
  cmp_indep := fun j w _ v hv => P.cmp_indep j (wtB col Z N h w) v hv
  mulC := fun j w w' F F' => P.mulC j (wtB col Z N h w) (wtB col Z N h w') F F'
  cmp_mul := fun j w w' c F F' => P.cmp_mul j (wtB col Z N h w) (wtB col Z N h w') c F F'
  supN := fun j w => P.supN j (wtB col Z N h w)
  supN_nonneg := fun j w => P.supN_nonneg j (wtB col Z N h w)
  supN_eq_zero := fun j w => P.supN_eq_zero j (wtB col Z N h w)
  supN_smul := fun j w => P.supN_smul j (wtB col Z N h w)
  supN_add := fun j w => P.supN_add j (wtB col Z N h w)
  l2NormAlt := fun j w => P.l2NormAlt j (wtB col Z N h w)
  l2Norm_nonneg_bis := fun j w => P.l2Norm_nonneg_bis j (wtB col Z N h w)
  l2Norm_eq_zero_iff := fun j w => P.l2Norm_eq_zero_iff j (wtB col Z N h w)
  l2Norm_smul_alt := fun j w => P.l2Norm_smul_alt j (wtB col Z N h w)
  l2Norm_add_le' := fun j w => P.l2Norm_add_le' j (wtB col Z N h w)
  l2Norm_le_supNorm_alt := fun j w => P.l2Norm_le_supNorm_alt j (wtB col Z N h w)
  Cu := P.Cu
  Xc := P.Xc
  Xc_lat := P.Xc_lat
  FJt := fun j c χ w => P.FJt j c χ (wtB col Z N h w)
  acgF := fun j c χ w => P.acgF j c χ (wtB col Z N h w)
  modF := fun j c χ w => P.modF j c χ (wtB col Z N h w)
  sg := fun j c χ w => P.sg j c χ (wtB col Z N h w)
  Pt := P.Pt
  pt66 := P.pt66
  vAtC := fun j la y w => P.vAtC j la y (wtB col Z N h w)
  vAtC_zero := fun j la y w => P.vAtC_zero j la y (wtB col Z N h w)
  vAtC_ne_bot := fun j la y w => P.vAtC_ne_bot j la y (wtB col Z N h w)
  vAtC_add := fun j la y w => P.vAtC_add j la y (wtB col Z N h w)
  vAtC_smul := fun j la y w => P.vAtC_smul j la y (wtB col Z N h w)
  vAtC_mul := fun j la y w w' => P.vAtC_mul j la y (wtB col Z N h w) (wtB col Z N h w')
  thAll := fun j w => P.thAll j (wtB col Z N h w)
  shortTh := fun j w => P.shortTh j (wtB col Z N h w)


set_option maxHeartbeats 8000000 in
def famT {G : DV.Geo (D₀).what₂.LL} {Lev : Type} (F : ShimFam D₀ G Lev) : ShimFam D₁ G Lev :=
  { F with
    U := fun w => shimUT col Z N h (F.U (datBk col Z N h w))
    forms := formsT col Z N h F.forms }


set_option maxHeartbeats 4000000 in
theorem heq_mdlT {p : ℕ} [Fact p.Prime] {A A' : Type} {M M' : ℕ} {rk rk' : DV.Emb D₀ p → ℕ}
    (f : A → DV.Mdl D₀ p M rk) (g : A' → DV.Mdl D₀ p M' rk') (hA : A = A') (hM : M = M') (hrk : rk = rk')
    (hfg : HEq f g) : HEq (fun z => mdlT col Z N h (f z)) (fun z => mdlT col Z N h (g z)) := by
  subst hA hM hrk
  obtain rfl := eq_of_heq hfg
  rfl


set_option maxHeartbeats 8000000 in
theorem geoTiedP_divTr {X : DivX D₀} {inK : X.Lev → ℕ → Prop} (hg : GeoTiedP X inK) :
    GeoTiedP (divXTr col Z N h X) inK := by
  obtain ⟨F, ePl, eC, hT, hJ, hC, hI, hL⟩ := hg
  refine ⟨famT col Z N h F, ePl, eC, ⟨⟨hT.shv.lev, fun w hw => hT.shv.shv (datBk col Z N h w) hw⟩,
    ⟨hT.pl.wt, hT.pl.jc, fun w hw => hT.pl.mp (datBk col Z N h w) hw, ?_, fun w hw => hT.pl.curveM (datBk col Z N h w) hw,
      fun w hw => hT.pl.degM (datBk col Z N h w) hw, fun w hw => hT.pl.htMdl (datBk col Z N h w) hw,
      fun w hw => hT.pl.htCurve (datBk col Z N h w) hw⟩, ⟨fun j h1 h2 c => hT.geo.yv j h1 h2 c, fun j h1 h2 c => hT.geo.ybd j h1 h2 c,
      fun j h1 h2 c la => hT.geo.lw j h1 h2 c la⟩, hT.lev_κg⟩, hJ, hC,
    fun w w' hs hk hj hw hw' => hI (datBk col Z N h w) (datBk col Z N h w') hs hk hj hw hw', fun w M => hL (datBk col Z N h w) M⟩
  intro w hw p _ la
  have hS := hT.shv.shv (datBk col Z N h w) hw
  have hM : (X.shv w.S w.κ).N = (datBk col Z N h w).N := by rw [show w.S = (datBk col Z N h w).S from rfl, show w.κ = (datBk col Z N h w).κ from rfl, hS]; rfl
  have hj : (X.shv w.S w.κ).j = (datBk col Z N h w).j := by rw [show w.S = (datBk col Z N h w).S from rfl, show w.κ = (datBk col Z N h w).κ from rfl, hS]; rfl
  have hrk : DV.rkOf (DV.PsiOf D₀ (X.jC p la)) (X.shv w.S w.κ).N (X.shv w.S w.κ).j =
      DV.rkOf (DV.PsiOf D₀ (F.jC p (ePl p la))) (datBk col Z N h w).N (datBk col Z N h w).j := by
    rw [hT.pl.jc p la, hM, hj]
  exact heq_mdlT col Z N h _ _ (hT.pl.mp (datBk col Z N h w) hw p la) hM hrk (tiedMd hT.pl (datBk col Z N h w) hw p la)

end GeoDivTr

open GeoDivTr

set_option maxHeartbeats 8000000 in
theorem divT_setDiv : ∀ {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T)
    (Z : w.Lt) {Wt : Set B.places.Pl} {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch)
    (Y : DivX (w.D Z)) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ),
    DivT n Y →
    let n' : NchT w (setDivZ Z N h) Wt { nch with } :=
      { n with tp := { n.tp with }, tie := { n.tie with }, chrPsi := n.chrPsi }
    Nonempty (DivT n' (divXTr w Z N h Y)) := by
  intro B f T w Z Wt nch n Y N h d
  refine ⟨{
    Qp := d.Qp
    chr := { d.chr with }
    loc := ?_
    inK := d.inK
    geo := geoTiedP_divTr w Z N h d.geo }⟩
  obtain ⟨h1, h2⟩ := d.loc
  exact ⟨h1, { h2 with }⟩

end GlobalTheory.Mem.Top.Bl.WitTr

end
