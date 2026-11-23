module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDescendThrough
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PicardClassTrivialBySeesaw
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.TorusPic

open GlobalTheory.UU GlobalTheory.UU.PackageDescent

section Ratio

variable {X Y Z : Scheme.{0}} {K : Type} [Fintype K]

theorem exists_unit_ratio {L : LB X} (hL : L.IsLB) {φ φ' : K → (Y ⟶ X)} (hφ : φ = φ') {ε : K → ℤ}
    (a : LB.Gen (LB.LinComb L φ ε)) (ha : a.IsGen) (b : LB.Gen (LB.LinComb L φ' ε)) (hb : b.IsGen) :
    ∃ v : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      val a r z J = gm r z ⊤ v * val b r z J := by
  subst hφ
  obtain ⟨t, -, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen L _ _ _ _ a (LB.invGen L _ _ b))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ha (DVR.invGen_isGen _ _ _ _ hb))
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  have e : gm r z ⊤ (res le (t.s PEmpty.elim)) = val a r z J * (val b r z J)⁻¹ := by
    refine (gm_res r z le trivial _).trans ?_
    rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ]
    exact (val_of t r z J PEmpty.elim (fun k => k.elim)).symm
  rw [e, inv_mul_cancel_right]

theorem gm_pullTop (g : Z ⟶ Y) (p : Y ⟶ X) (z : Z) (f : Γ(X, ⊤)ˣ) :
    gm g z ⊤ (Units.map p.appTop.hom.toMonoidHom f) = gm (g ≫ p) z ⊤ f :=
  gm_pull g p z ⊤ trivial f

end Ratio

section Points

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G Y : Over S} [GrpObj G]

def act (i : splitTorus S X ⟶ G) (Y : Over S) : splitTorus S X ⊗ (G ⊗ Y) ⟶ G ⊗ Y :=
  lift ((fst _ _ ≫ i) * (snd _ _ ≫ fst G Y)) (snd _ _ ≫ snd G Y)

theorem lift_act (i : splitTorus S X ⟶ G) {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (y : Z ⟶ Y) :
    lift t (lift g y) ≫ act i Y = lift ((t ≫ i) * g) y := by
  simp [act, comp_lift, MonObj.comp_mul]

def sec (G : Over S) (y₀ : 𝟙_ (Over S) ⟶ Y) : G ⟶ G ⊗ Y := lift (𝟙 G) (toUnit G ≫ y₀)

theorem comp_sec {Z : Over S} (g : Z ⟶ G) (y₀ : 𝟙_ (Over S) ⟶ Y) :
    g ≫ sec G y₀ = lift g (toUnit Z ≫ y₀) := by
  simp [sec, comp_lift]

variable [Module.Free ℤ X] {X' : Scheme.{0}}

theorem exists_weight [ConnectedSpace (G ⊗ Y).left] [IsReduced (G ⊗ Y).left]
    (i : splitTorus S X ⟶ G) [IsMonHom i] (P : (G ⊗ Y).left ⟶ X')
    (hP : (act i Y).left ≫ P = (snd (splitTorus S X) (G ⊗ Y)).left ≫ P)
    {N : LB X'} (hN : N.IsLB) (u : LB.Gen (N.pull P)) (hu : u.IsGen) :
    ∃ χ : X, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (y : Z ⟶ Y) (z : Z.left) (J), Good N z J →
      val u (lift ((t ≫ i) * g) y).left z J = gm (𝟙 Z.left) z ⊤ (chV t χ) * val u (lift g y).left z J := by
  obtain ⟨v, hv⟩ := exists_unit_ratio hN (φ := fun _ : PUnit => (act i Y).left ≫ P)
    (φ' := fun _ => (snd (splitTorus S X) (G ⊗ Y)).left ≫ P) (funext fun _ => hP) (ε := fun _ => 1)
    (LB.pullGen N _ _ u (act i Y).left) (DVR.pullGen_isGen _ _ _ _ hu _)
    (LB.pullGen N _ _ u (snd (splitTorus S X) (G ⊗ Y)).left) (DVR.pullGen_isGen _ _ _ _ hu _)
  obtain ⟨χ, hχ⟩ := GlobalTheory.CompanionTheory.TorusMono.torus_unit_eq_char_mul S X (G ⊗ Y) v
  refine ⟨χ, fun Z t g y z J hJ => ?_⟩
  have key : ∀ t' : Z ⟶ splitTorus S X, val u (lift ((t' ≫ i) * g) y).left z J =
      gm (lift t' (lift g y)).left z ⊤ v * val u (lift g y).left z J := by
    intro t'
    have h := hv Z.left (lift t' (lift g y)).left z J hJ
    rw [val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, lift_act, lift_snd] at h
    exact h
  have h1 : gm (lift (1 : Z ⟶ splitTorus S X) (lift g y)).left z ⊤ v = 1 := by
    have h := key 1
    rw [MonObj.one_comp, _root_.one_mul] at h
    exact mul_eq_right.1 h.symm
  have h2 : Units.map (lift t (lift g y)).left.appTop.hom.toMonoidHom v = chV t χ *
      Units.map (lift (1 : Z ⟶ splitTorus S X) (lift g y)).left.appTop.hom.toMonoidHom v :=
    Units.ext (hχ Z t (lift g y))
  rw [key t, gm_top _ z v, h2, map_mul, ← gm_top, h1, _root_.mul_one]

theorem exists_unit_weight {B : Over S} (i : splitTorus S X ⟶ G) (q : G ⟶ B)
    (hiq : ∀ {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), ((t ≫ i) * g) ≫ q = g ≫ q)
    (P : (G ⊗ Y).left ⟶ X') (E : B.left ⟶ X') (y₀ : 𝟙_ (Over S) ⟶ Y)
    (hE : (sec G y₀).left ≫ P = q.left ≫ E)
    {N : LB X'} (hN : N.IsLB) (u : LB.Gen (N.pull P)) (hu : u.IsGen) (s : LB.Gen (N.pull E)) (hs : s.IsGen)
    (χ : X) (hw : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (y : Z ⟶ Y) (z : Z.left) (J), Good N z J →
      val u (lift ((t ≫ i) * g) y).left z J = gm (𝟙 Z.left) z ⊤ (chV t χ) * val u (lift g y).left z J) :
    ∃ f : Γ(G.left, ⊤)ˣ, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left),
      gm ((t ≫ i) * g).left z ⊤ f = gm (𝟙 Z.left) z ⊤ (chV t χ) * gm g.left z ⊤ f := by
  obtain ⟨f, hf⟩ := exists_unit_ratio hN (φ := fun _ : PUnit => (sec G y₀).left ≫ P)
    (φ' := fun _ => q.left ≫ E) (funext fun _ => hE) (ε := fun _ => 1)
    (LB.pullGen N _ _ u (sec G y₀).left) (DVR.pullGen_isGen _ _ _ _ hu _)
    (LB.pullGen N _ _ s q.left) (DVR.pullGen_isGen _ _ _ _ hs _)
  refine ⟨f, fun Z t g z => ?_⟩
  obtain ⟨J, hJ⟩ := exists_good_pt hN z
  have a := hf Z.left ((t ≫ i) * g).left z J hJ
  have b := hf Z.left g.left z J hJ
  rw [val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, comp_sec, hiq] at a
  rw [val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, comp_sec] at b
  have c := hw Z t g (toUnit Z ≫ y₀) z J hJ
  rw [a, b, ← _root_.mul_assoc] at c
  exact mul_right_cancel c

end Points

section Main

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B Y : Over S} [GrpObj G]

abbrev proj (q : G ⟶ B) (Y : Over S) : G ⊗ Y ⟶ B ⊗ Y := lift (fst G Y ≫ q) (snd G Y)

theorem lift_proj (q : G ⟶ B) {Z : Over S} (g : Z ⟶ G) (y : Z ⟶ Y) :
    lift g y ≫ proj q Y = lift (g ≫ q) y := by
  simp [comp_lift]

theorem exists_gen_of_weight (i : splitTorus S X ⟶ G) (q : G ⟶ B)
    [Flat (proj q Y).left] [Surjective (proj q Y).left] [QuasiCompact (proj q Y).left]
    (ker : ∀ {Z : Over S} (g g' : Z ⟶ G), g ≫ q = g' ≫ q → ∃ t : Z ⟶ splitTorus S X, g = (t ≫ i) * g')
    {N : LB (B ⊗ Y).left} (hN : N.IsLB) (u : LB.Gen (N.pull ((proj q Y).left ≫ 𝟙 _))) (hu : u.IsGen)
    (χ : X) (hw : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (y : Z ⟶ Y) (z : Z.left) (J), Good N z J →
      val u (lift ((t ≫ i) * g) y).left z J = gm (𝟙 Z.left) z ⊤ (chV t χ) * val u (lift g y).left z J)
    (f : Γ(G.left, ⊤)ˣ) (hf : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left),
      gm ((t ≫ i) * g).left z ⊤ f = gm (𝟙 Z.left) z ⊤ (chV t χ) * gm g.left z ⊤ f) :
    ∃ t : LB.Gen (N.pull (𝟙 _)), t.IsGen := by
  let v : Γ((G ⊗ Y).left, ⊤)ˣ := (Units.map (fst G Y).left.appTop.hom.toMonoidHom f)⁻¹
  have val' : ∀ (Z : Over S) (g : Z ⟶ G) (y : Z ⟶ Y) (z : Z.left) (J), Good N z J →
      val (scaleGen v u) (lift g y).left z J = (gm g.left z ⊤ f)⁻¹ * val u (lift g y).left z J := by
    intro Z g y z J hJ
    rw [val_scaleGen _ _ _ hJ, map_inv, gm_pullTop, ← Over.comp_left, lift_fst]
  have inv : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (y : Z ⟶ Y) (z : Z.left) (J), Good N z J →
      val (scaleGen v u) (lift ((t ≫ i) * g) y).left z J = val (scaleGen v u) (lift g y).left z J := by
    intro Z t g y z J hJ
    rw [val' _ _ _ z J hJ, val' _ _ _ z J hJ, hf, hw _ _ _ _ z J hJ, mul_inv,
      _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul]
  obtain ⟨t, ht, -⟩ := exists_gen_descend_val hN (proj q Y).left (fun _ : PUnit => 𝟙 _) (fun _ => 1)
    (scaleGen v u) (scaleGen_isGen _ hu) fun Z g₁ g₂ z J hJ e => by
      let T : Over S := Over.mk (g₂ ≫ (G ⊗ Y).hom)
      let k₂ : T ⟶ G ⊗ Y := Over.homMk g₂ rfl
      let k₁ : T ⟶ G ⊗ Y := Over.homMk g₁ (by
        change g₁ ≫ (G ⊗ Y).hom = g₂ ≫ (G ⊗ Y).hom
        rw [← Over.w (proj q Y), reassoc_of% e])
      have e' : k₁ ≫ proj q Y = k₂ ≫ proj q Y := Over.OverMorphism.ext e
      have h₁ : k₁ = lift (k₁ ≫ fst _ _) (k₁ ≫ snd _ _) := by ext <;> simp
      have h₂ : k₂ = lift (k₂ ≫ fst _ _) (k₂ ≫ snd _ _) := by ext <;> simp
      have ex : (k₁ ≫ fst _ _) ≫ q = (k₂ ≫ fst _ _) ≫ q := by
        simpa using e' =≫ fst _ _
      have ey : k₁ ≫ snd G Y = k₂ ≫ snd G Y := by
        simpa using e' =≫ snd _ _
      obtain ⟨t, ht⟩ := ker _ _ ex
      have a₁ : g₁ = (lift ((t ≫ i) * (k₂ ≫ fst _ _)) (k₂ ≫ snd G Y)).left := by
        rw [← ht, ← ey, ← h₁]; rfl
      have a₂ : g₂ = (lift (k₂ ≫ fst _ _) (k₂ ≫ snd G Y)).left := by
        rw [← h₂]; rfl
      rw [a₁, a₂]
      exact inv T t _ _ z J hJ
  exact ⟨t, ht⟩

end Main

theorem pic_inj : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (T : TorusExtension G) (Y : Over (Sp k)), Smooth Y.hom → GeometricallyConnected Y.hom → ∀ (y₀ : 𝟙_ (Over (Sp k)) ⟶ Y) (c : Pic (T.B ⊗ Y).left), pull (lift (fst G Y ≫ T.q) (snd G Y)).left c = 0 → pull (lift (𝟙 T.B) (toUnit T.B ≫ y₀)).left c = 0 → c = 0 := by
  intro k _ _ G _ _ hG T Y hYs hYc y₀ c h₁ h₂
  obtain ⟨N, hN, rfl⟩ := cls_surj c
  letI := T.addCommGroup
  letI := T.grpB
  have := T.free
  have := T.q_hom
  have := T.i_hom
  have := T.q_flat
  have := T.q_surjective
  have := T.q_quasiCompact
  have := hG.smooth
  have := hG.geomConnected
  have hsm : Smooth (G ⊗ Y).hom := by
    rw [Over.tensorObj_hom, pullback.condition]
    infer_instance
  have hgc : GeometricallyConnected (G ⊗ Y).hom := by
    rw [Over.tensorObj_hom, pullback.condition]
    exact GeometricallyConnected.comp _ _
  have : ConnectedSpace (G ⊗ Y).left :=
    GeometricallyConnected.connectedSpace (G ⊗ Y).hom (G ⊗ Y).hom.isOpenMap
  have : IsReduced (G ⊗ Y).left := isReduced_of_smooth (G ⊗ Y).hom
  have eπ : proj T.q Y = T.q ⊗ₘ 𝟙 Y := by ext <;> simp
  have hid₁ : Flat (𝟙 Y : Y ⟶ Y).left := by rw [Over.id_left]; infer_instance
  have hid₂ : Surjective (𝟙 Y : Y ⟶ Y).left := by rw [Over.id_left]; infer_instance
  have hid₃ : QuasiCompact (𝟙 Y : Y ⟶ Y).left := by rw [Over.id_left]; infer_instance
  have : Flat (proj T.q Y).left := eπ ▸ CosetQuotient.flat_tensorHom T.q (𝟙 Y)
  have : Surjective (proj T.q Y).left := eπ ▸ CosetQuotient.surjective_tensorHom T.q (𝟙 Y)
  have : QuasiCompact (proj T.q Y).left := eπ ▸ CosetQuotient.quasiCompact_tensorHom T.q (𝟙 Y)
  have hiq : ∀ {Z : Over (Sp k)} (t : Z ⟶ splitTorus (Sp k) T.X) (g : Z ⟶ G), ((t ≫ T.i) * g) ≫ T.q = g ≫ T.q := by
    intro Z t g
    rw [MonObj.mul_comp, Category.assoc, T.isKernel.w, ← Category.assoc,
      toUnit_unique (t ≫ toUnit _) (toUnit Z), ← Hom.one_def, _root_.one_mul]
  have ker : ∀ {Z : Over (Sp k)} (g g' : Z ⟶ G), g ≫ T.q = g' ≫ T.q →
      ∃ t : Z ⟶ splitTorus (Sp k) T.X, g = (t ≫ T.i) * g' := by
    intro Z g g' e
    have h : (g * g'⁻¹) ≫ T.q = toUnit Z ≫ η[T.B] := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, e, mul_inv_cancel]
      rfl
    exact ⟨T.isKernel.lift _ _ h, by rw [T.isKernel.lift_fst, inv_mul_cancel_right]⟩
  obtain ⟨u, hu⟩ := (cls_eq_zero_iff (pull_isLB hN ((proj T.q Y).left ≫ 𝟙 _))).1 (by
    rw [cls_pull hN, Category.comp_id]; exact h₁)
  obtain ⟨s, hs⟩ := (cls_eq_zero_iff (pull_isLB hN (lift (𝟙 T.B) (toUnit T.B ≫ y₀)).left)).1 (by
    rw [cls_pull hN]; exact h₂)
  obtain ⟨χ, hw⟩ := exists_weight T.i ((proj T.q Y).left ≫ 𝟙 _) (by
    rw [Category.comp_id, ← Over.comp_left, ← Over.comp_left]
    congr 1
    have e₁ : snd (splitTorus (Sp k) T.X) (G ⊗ Y) ≫ proj T.q Y =
        lift ((snd _ _ ≫ fst G Y) ≫ T.q) (snd _ _ ≫ snd G Y) := by
      rw [proj, comp_lift, Category.assoc]
    rw [act, lift_proj, e₁, hiq]) hN u hu
  obtain ⟨f, hf⟩ := exists_unit_weight T.i T.q hiq ((proj T.q Y).left ≫ 𝟙 _)
    (lift (𝟙 T.B) (toUnit T.B ≫ y₀)).left y₀ (by
      rw [Category.comp_id, ← Over.comp_left, ← Over.comp_left, sec, lift_proj]
      simp [comp_lift, toUnit_unique (T.q ≫ toUnit T.B) (toUnit G)]) hN u hu s hs χ hw
  obtain ⟨t, ht⟩ := exists_gen_of_weight T.i T.q ker hN u hu χ hw f hf
  have h := (cls_eq_zero_iff (pull_isLB hN (𝟙 _))).2 ⟨t, ht⟩
  rwa [cls_pull hN, pull_id] at h

end GlobalTheory.CompanionTheory.TorusPic
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameSectionBound
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd

section IntWeight

variable {K : Type} [Field K] {ι : Type}
  {pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type}
  {mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T], (S →ₐ[K] T) → pts S → pts T → Prop}
  {borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop}

theorem evalAt_bor_zpow [Fintype ι] (h : BorChart pts mapR borR) (e : ι → ℤ) {f : Rules pts}
    (hf : IsNatural pts mapR f)
    (hw : ∀ (p : TRing K) (t : ι → (p.R)ˣ) (y y' : pts p.R), borR t y y' →
      f p y' = ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) * f p y)
    (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ)
    (y y' : pts S) (hy : FromTest pts mapR y) (hy' : FromTest pts mapR y') (hb : borR t y y') :
    evalAt pts mapR f y' = ((∏ i, t i ^ e i : Sˣ) : S) * evalAt pts mapR f y := by
  unfold evalAt
  rw [dite_eq_left hy, dite_eq_left hy']
  apply eq_of_locM (K := K)
  intro m hm
  obtain ⟨A, u, c, c', B, uB, uB', tB, π, π', cB, hc, hc', hπ, hπ', hbB, e1, e2, e3⟩ := h S t y y' hb m
  rw [map_mul, chartAt_val hf hc' hy'.choose_spec.choose_spec.choose_spec,
    chartAt_val hf hc hy.choose_spec.choose_spec.choose_spec, ← e1, ← e2, AlgHom.comp_apply, AlgHom.comp_apply,
    ← hf A B π u uB hπ, ← hf A B π' u uB' hπ', hw B tB uB uB' hbB, map_mul]
  congr 1
  have key : ∀ i, Units.map cB.toRingHom.toMonoidHom (tB i) = Units.map (locM K m).toRingHom.toMonoidHom (t i) :=
    fun i => Units.ext (by simpa using e3 i)
  have h1 : cB ((∏ i, tB i ^ e i : (B.R)ˣ) : B.R) =
      ((Units.map cB.toRingHom.toMonoidHom (∏ i, tB i ^ e i) : (Localization.AtPrime m)ˣ) : Localization.AtPrime m) := rfl
  have h2 : locM K m ((∏ i, t i ^ e i : Sˣ) : S) =
      ((Units.map (locM K m).toRingHom.toMonoidHom (∏ i, t i ^ e i) : (Localization.AtPrime m)ˣ) :
        Localization.AtPrime m) := rfl
  rw [h1, h2, map_prod, map_prod]
  simp_rw [map_zpow, key]

end IntWeight

section Abs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {c : Coeff l}

def absHom (p : ℕ) [hp : Fact p.Prime] (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (e : ℕ) : T.Fr →*₀ ℝ where
  toFun := absT p la T e
  map_zero' := by simp [absT]
  map_one' := by
    have h1 : vV T.V (1 : T.Fr) = 0 := by simp [vV]
    simp [absT, h1]
  map_mul' x y := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    by_cases hx : x = 0
    · simp [absT, hx]
    by_cases hy : y = 0
    · simp [absT, hy]
    simp only [absT, if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy)]
    rw [← Real.rpow_add hp0, vV_mul hx hy]
    congr 1
    push_cast
    ring

theorem absHom_apply (p : ℕ) [Fact p.Prime] (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (e : ℕ) (x : T.Fr) :
    absHom p la T e x = absT p la T e x := rfl

theorem absT_of_nval {p : ℕ} [hp : Fact p.Prime] {la : HeightOneSpectrum (𝓞 c.F)} {T : CDVR} {e : ℕ} (he : 0 < e)
    (hr : 0 < ramOverZ la) (t : Ix Dw → T.Frˣ) (n : Ix Dw → ℤ) {g w : T.Fr}
    (hg : g = ((∏ i, t i ^ n i : T.Frˣ) : T.Fr) * w) {s : ℝ}
    (hs : nval T.V e g = ((ramOverZ la * s : ℝ) : EReal)) :
    absT p la T e w = (p : ℝ) ^ (-s) * ∏ j, tOf p la T e t j ^ n j := by
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [nval_zero] at hs
    exact EReal.coe_ne_top _ hs.symm
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have hr' : (ramOverZ la : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hv : (vV T.V g : ℝ) / e = ramOverZ la * s := by
    rw [nval_of_ne hg0] at hs
    exact_mod_cast hs
  have hag : absT p la T e g = (p : ℝ) ^ (-s) := by
    unfold absT
    rw [if_neg hg0]
    congr 1
    rw [← div_div, hv]
    field_simp
  have hu : absT p la T e ((∏ i, t i ^ n i : T.Frˣ) : T.Fr) = ∏ j, (tOf p la T e t j ^ n j)⁻¹ := by
    rw [Units.coe_prod, ← absHom_apply, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, absHom_apply, tOf, inv_zpow, inv_inv]
  have hm : absT p la T e g = absT p la T e ((∏ i, t i ^ n i : T.Frˣ) : T.Fr) * absT p la T e w := by
    rw [hg, ← absHom_apply, map_mul]
    rfl
  have hne : ∀ j, tOf p la T e t j ^ n j ≠ 0 := fun j => zpow_ne_zero _ (tOf_pos la T e t j).ne'
  have hP : (∏ j, tOf p la T e t j ^ n j) * ∏ j, (tOf p la T e t j ^ n j)⁻¹ = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun j _ => mul_inv_cancel₀ (hne j)
  rw [← hag, hm, hu]
  linear_combination (-absT p la T e w) * hP

end Abs

theorem readsZ_of_isIntPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or), ∀ (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ x : (Ref.pjSys Xo c).Pt la, (∀ f, (Ref.pjSys Xo c).val x f = nval T.V e (evI y f)) → FinRd.ReadsZ Fr z x (FinRd.tOf p la T e t) := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev hz hev la T io e y evT zT t hI x hx a f hf
  letI := io.toAlgebra
  letI := Small.cstAlg Or
  obtain ⟨hp, hO, -, -, -, hn, ⟨q, φ, ψ, yq, hφ, hψ, hA⟩, hb⟩ := hI
  have hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  have hWD := (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS E H Dw l Xo c).2.2.1
  have hrd : Fr.rd f = φ (f q yq) := Fr.rd_eq_of_frMap hWD hf.1 q φ yq hφ
  obtain ⟨hmem, hψe⟩ := hA (f q yq)
  have hm : Fr.rd f ∈ A := hrd ▸ hmem
  have hft : Formalism.L2.Pj.FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) zT := ⟨q, ψ, yq, hψ⟩
  have hzT : evR Xo c f zT = ψ (f q yq) := by
    unfold evR evalAt
    rw [dite_eq_left hft]
    exact hWD f hf.1 T.Fr _ q _ ψ _ yq zT hft.choose_spec.choose_spec.choose_spec hψ
  have hbor : evI y f = ((∏ i, t i ^ exZ Dw a i : T.Frˣ) : T.Fr) * evR Xo c f zT :=
    evalAt_bor_zpow (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS E H Dw l Xo c).2.1 (exZ Dw a) hf.1
      (fun p t y y' hb => by rw [hf.2 p t y y' hb, Units.coe_prod]) T.Fr t zT y.1 hft y.2.1 hb
  have hnorm : ‖ev ⟨Fr.rd f, hm⟩‖ = absT p la T e (evR Xo c f zT) := by
    rw [hn, hzT, hψe]
    exact congrArg (absT p la T e) (congrArg evT (Subtype.ext hrd))
  refine ⟨ev ⟨Fr.rd f, hm⟩, hev ⟨Fr.rd f, hm⟩, fun htop => ?_, fun s hs => ?_⟩
  · have h0 : evI y f = 0 := by
      by_contra hne
      rw [hx, nval_of_ne hne] at htop
      exact EReal.coe_ne_top _ htop
    have hw : evR Xo c f zT = 0 := by
      rw [h0] at hbor
      exact (mul_eq_zero.1 hbor.symm).resolve_left (Units.ne_zero _)
    rw [← norm_eq_zero, hnorm, hw]
    simp [absT]
  · rw [hnorm]
    exact absT_of_nval hO.1 (ram_pos hp) t (exZ Dw a) hbor (by rw [← hx]; exact hs)

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd
end
end

