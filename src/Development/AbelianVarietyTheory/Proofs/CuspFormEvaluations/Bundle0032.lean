module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramedBaseChange

theorem spec_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    spMap (ψ.comp φ) = spMap ψ ≫ spMap φ := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dual_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    dualMap (ψ.comp φ) = (dualMap ψ).comp (dualMap φ) :=
  RingHom.ext fun x => by ext <;> simp [dualMap]

theorem spec_algHom_id (K : Type) [Field K] (T : Type) [CommRing T] [Algebra K T] :
    spMap (AlgHom.id K T).toRingHom = 𝟙 _ := by
  simp [spMap]

theorem dual_id (T : Type) [CommRing T] : dualMap (RingHom.id T) = RingHom.id _ :=
  RingHom.ext fun x => by
    show TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr x.snd = x
    exact TrivSqZeroExt.inl_fst_add_inr_snd_eq x

theorem appLE_eq_of_eq {X Y : Scheme.{0}} {f g : X ⟶ Y} (e : f = g) (U : Y.Opens) (V : X.Opens)
    (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) : f.appLE U V hf = g.appLE U V hg := by
  subst e
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem chart_le {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  intro p hp
  have hp' : ∀ k, p ∈ (snd (Over.mk x') Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) :=
    Set.mem_iInter.1 hp
  have e := congrArg (fun f : Gx x' ⟶ Xo.univ.t.G.left => f.base p) hs
  show pm.base p ∈ ⋂ k, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
  refine Set.mem_iInter.2 fun k => ?_
  show (pm ≫ (snd (Over.mk x) Xo.univ.t.G).left).base p ∈ (Xo.univ.t.PP.L.U (i k) : Set _)
  rw [e]
  exact hp' k

theorem pulledGroup_hom_ext {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {W : Scheme.{0}} (a b : W ⟶ Gx x)
    (hs : a ≫ (snd (Over.mk x) Xo.univ.t.G).left = b ≫ (snd (Over.mk x) Xo.univ.t.G).left)
    (hf : a ≫ (fst (Over.mk x) Xo.univ.t.G).left = b ≫ (fst (Over.mk x) Xo.univ.t.G).left) : a = b := by
  have hw : a ≫ (Over.mk x ⊗ Xo.univ.t.G).hom = b ≫ (Over.mk x ⊗ Xo.univ.t.G).hom := by
    have e1 := Over.w (snd (Over.mk x) Xo.univ.t.G)
    rw [← e1, ← Category.assoc, hs, Category.assoc]
  let a' : Over.mk (a ≫ (Over.mk x ⊗ Xo.univ.t.G).hom) ⟶ Over.mk x ⊗ Xo.univ.t.G := Over.homMk a rfl
  let b' : Over.mk (a ≫ (Over.mk x ⊗ Xo.univ.t.G).hom) ⟶ Over.mk x ⊗ Xo.univ.t.G := Over.homMk b hw.symm
  have e : a' = b' := by
    apply CartesianMonoidalCategory.hom_ext
    · exact Over.OverMorphism.ext hf
    · exact Over.OverMorphism.ext hs
  exact congrArg CommaMorphism.left e

theorem refl {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    FrMap (AlgHom.id c.F S) y y := by
  have eid := spec_algHom_id c.F S
  have did : spMap (dualMap (AlgHom.id c.F S).toRingHom) = 𝟙 _ := by
    show spMap (dualMap (RingHom.id S)) = _
    rw [dual_id]
    simp [spMap]
  refine ⟨by rw [eid, Category.id_comp], fun τ i => by rw [did, Category.id_comp], 𝟙 _,
    Category.id_comp _, by rw [eid]; exact (Category.id_comp _).trans (Category.comp_id _).symm, ?_⟩
  intro i h
  have e : Scheme.Hom.appLE (𝟙 (Gx y.x)) ((PPx y.x).U i) ((PPx y.x).U i) h = 𝟙 _ := by
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    refine (Category.id_comp _).trans ?_
    rw [← (Gx y.x).presheaf.map_id]
    rfl
  rw [e, CommRingCat.hom_id, RingHom.id_apply]

theorem trans {S T U : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] [CommRing U]
    [Algebra c.F U] (φ : S →ₐ[c.F] T) (ψ : T →ₐ[c.F] U) {y : FrPt Xo c S} {z : FrPt Xo c T} {w : FrPt Xo c U}
    (h₁ : FrMap φ y z) (h₂ : FrMap ψ z w) : FrMap (ψ.comp φ) y w := by
  obtain ⟨hx1, hu1, pm1, hs1, hf1, ha1⟩ := h₁
  obtain ⟨hx2, hu2, pm2, hs2, hf2, ha2⟩ := h₂
  have esp : spMap (ψ.comp φ).toRingHom = spMap ψ.toRingHom ≫ spMap φ.toRingHom := by
    exact spec_comp φ.toRingHom ψ.toRingHom
  have edsp : spMap (dualMap (ψ.comp φ).toRingHom) =
      spMap (dualMap ψ.toRingHom) ≫ spMap (dualMap φ.toRingHom) := by
    show spMap (dualMap (ψ.toRingHom.comp φ.toRingHom)) = _
    rw [dual_comp, spec_comp]
  refine ⟨?_, ?_, pm2 ≫ pm1, ?_, ?_, ?_⟩
  · rw [hx2, hx1, esp, Category.assoc]
  · intro τ i
    rw [hu2 τ i, hu1 τ i, edsp, Category.assoc]
  · rw [Category.assoc, hs1, hs2]
  · rw [Category.assoc, hf1, ← Category.assoc, hf2, esp, Category.assoc]
  · intro i h
    have h1' := chart_le pm1 hs1 i
    have h2' := chart_le pm2 hs2 i
    have e : (pm2 ≫ pm1).appLE _ _ h = pm1.appLE _ _ h1' ≫ pm2.appLE _ _ h2' :=
      (Scheme.Hom.appLE_comp_appLE pm2 pm1 _ _ _ h1' h2').symm
    rw [e, CommRingCat.hom_comp, RingHom.comp_apply, ha1 i h1', ha2 i h2']

theorem cancel {S T U : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] [CommRing U]
    [Algebra c.F U] (φ : S →ₐ[c.F] T) (κ : T →ₐ[c.F] U) {y0 : FrPt Xo c S} {y : FrPt Xo c T} {z : FrPt Xo c U}
    (h₁ : FrMap φ y0 y) (h₂ : FrMap (κ.comp φ) y0 z) : FrMap κ y z := by
  obtain ⟨hx1, hu1, pm1, hs1, hf1, ha1⟩ := h₁
  obtain ⟨hx2, hu2, pm2, hs2, hf2, ha2⟩ := h₂
  have esp : spMap (κ.comp φ).toRingHom = spMap κ.toRingHom ≫ spMap φ.toRingHom :=
    spec_comp φ.toRingHom κ.toRingHom
  have edsp : spMap (dualMap (κ.comp φ).toRingHom) =
      spMap (dualMap κ.toRingHom) ≫ spMap (dualMap φ.toRingHom) := by
    show spMap (dualMap (κ.toRingHom.comp φ.toRingHom)) = _
    rw [dual_comp, spec_comp]
  have hx : spMap κ.toRingHom ≫ y.x = z.x := by rw [hx2, hx1, esp, Category.assoc]
  let pm : Gx z.x ⟶ Gx y.x :=
    ((Over.homMk (spMap κ.toRingHom) hx : Over.mk z.x ⟶ Over.mk y.x) ▷ Xo.univ.t.G).left
  have hs : pm ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (snd (Over.mk z.x) Xo.univ.t.G).left := by
    rw [← Over.comp_left, whiskerRight_snd]
  have hf : pm ≫ (fst (Over.mk y.x) Xo.univ.t.G).left =
      (fst (Over.mk z.x) Xo.univ.t.G).left ≫ spMap κ.toRingHom := by
    rw [← Over.comp_left, whiskerRight_fst]
    rfl
  have hcomp : pm ≫ pm1 = pm2 := by
    apply pulledGroup_hom_ext
    · rw [Category.assoc, hs1, hs, hs2]
    · rw [Category.assoc, hf1, ← Category.assoc, hf, Category.assoc, ← esp, hf2]
  refine ⟨?_, ?_, pm, hs, hf, ?_⟩
  · rw [hx2, hx1, esp, Category.assoc]
  · intro τ i
    rw [hu2 τ i, hu1 τ i, edsp, Category.assoc]
  · intro i h
    have h1' := chart_le pm1 hs1 i
    have h2' := chart_le pm2 hs2 i
    rw [← ha1 i h1', ← ha2 i h2']
    have e : pm1.appLE _ _ h1' ≫ pm.appLE _ _ h = pm2.appLE ((PPx y0.x).U i) ((PPx z.x).U i) h2' := by
      rw [Scheme.Hom.appLE_comp_appLE]
      exact appLE_eq_of_eq hcomp _ _ _ _
    rw [← e, CommRingCat.hom_comp, RingHom.comp_apply]

theorem unique {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {y : FrPt Xo c S} {z z' : FrPt Xo c T} (h₁ : FrMap φ y z) (h₂ : FrMap φ y z') :
    z = z' := by
  obtain ⟨x1, o1, u1, tan1, eig1, basis1, s1, gen1⟩ := z
  obtain ⟨x2, o2, u2, tan2, eig2, basis2, s2, gen2⟩ := z'
  obtain ⟨hx1, hu1, pm1, hs1, hf1, ha1⟩ := h₁
  obtain ⟨hx2, hu2, pm2, hs2, hf2, ha2⟩ := h₂
  dsimp only at hx1 hu1 pm1 hs1 hf1 ha1 hx2 hu2 pm2 hs2 hf2 ha2
  have hx : x1 = x2 := hx1.trans hx2.symm
  subst hx
  have hu : u1 = u2 := funext fun τ => funext fun i => (hu1 τ i).trans (hu2 τ i).symm
  subst hu
  have hpm : pm1 = pm2 := pulledGroup_hom_ext _ _ (hs1.trans hs2.symm) (hf1.trans hf2.symm)
  subst hpm
  have hsf : s1.f = s2.f := funext fun i =>
    (ha1 i (chart_le pm1 hs1 i)).symm.trans (ha2 i (chart_le pm1 hs1 i))
  obtain ⟨f1, c1⟩ := s1
  obtain ⟨f2, c2⟩ := s2
  dsimp only at hsf
  subst hsf
  rfl

theorem isPullSec {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {y : FrPt Xo c S} {z : FrPt Xo c T} (hm : FrMap φ y z)
    (h : ptO Xo z.x ⟶ ptO Xo y.x) (hh : h.left = spMap φ.toRingHom) :
    IsPullSec Xo.univ.t.G Xo.univ.t.PP.L 1 (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) y.s z.s := by
  obtain ⟨hx, hu, pm, hs, hf, ha⟩ := hm
  have hpm : pm = (h ▷ Xo.univ.t.G).left := by
    apply pulledGroup_hom_ext
    · rw [hs, ← Over.comp_left, whiskerRight_snd]
    · rw [hf, ← Over.comp_left, whiskerRight_fst, Over.comp_left, hh]
  subst hpm
  intro j
  exact (ha j (chart_le _ hs j)).symm

end GlobalTheory.FramedBaseChange

namespace GlobalTheory

theorem framedPoint_baseChange_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), FrMap (AlgHom.id c.F S) y y) ∧ (∀ (S T U : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] [CommRing U] [Algebra c.F U] (φ : S →ₐ[c.F] T) (ψ : T →ₐ[c.F] U) (y : FrPt Xo c S) (z : FrPt Xo c T) (w : FrPt Xo c U), FrMap φ y z → (FrMap ψ z w ↔ FrMap (ψ.comp φ) y w)) ∧ (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z z' : FrPt Xo c T), FrMap φ y z → FrMap φ y z' → z = z') ∧ ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → ∀ h : ptO Xo z.x ⟶ ptO Xo y.x, h.left = spMap φ.toRingHom → IsPullSec Xo.univ.t.G Xo.univ.t.PP.L 1 (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) y.s z.s :=
  fun _ _ _ _ _ _ _ _ _ =>
    ⟨fun _ _ _ y => FramedBaseChange.refl y,
     fun _ _ _ _ _ _ _ _ _ φ ψ _ _ _ h₁ =>
       ⟨fun h₂ => FramedBaseChange.trans φ ψ h₁ h₂, fun h₂ => FramedBaseChange.cancel φ ψ h₁ h₂⟩,
     fun _ _ _ _ _ _ φ _ _ _ h₁ h₂ => FramedBaseChange.unique φ h₁ h₂,
     fun _ _ _ _ _ _ φ _ _ hm h hh => FramedBaseChange.isPullSec φ hm h hh⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocallyNoetherian
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace UnivPol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

def pol (Xo : Moduli D l) : PolAV Xo.X := GlobalTheory.Obj.toPolAV Xo.univ

theorem smooth (Xo : Moduli D l) : Smooth Xo.s :=
  haveI := Xo.smooth
  SmoothOfRelativeDimension.smooth D.dim Xo.s

theorem isLocallyNoetherian (Xo : Moduli D l) : IsLocallyNoetherian Xo.X := by
  haveI := smooth Xo
  exact LocallyOfFiniteType.isLocallyNoetherian Xo.s

theorem isReduced (Xo : Moduli D l) : IsReduced Xo.X := by
  haveI := smooth Xo
  exact GlobalTheory.isReduced_of_smooth_of_isReduced Xo.s

theorem isUnit_natCast (Xo : Moduli D l) (n : ℕ) (hn : 0 < n) : IsUnit (n : Γ(Xo.X, ⊤)) := by
  have hK : IsUnit (n : KA l) := by
    haveI : CharZero (KA l) := (RingHom.charZero_iff (algebraMap (KA l) ℂ).injective).2 inferInstance
    exact (isUnit_iff_ne_zero).2 (Nat.cast_ne_zero.2 hn.ne')
  have hΓ := hK.map ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv.hom)
  have hX := hΓ.map Xo.s.appTop.hom
  simpa using hX

end UnivPol

theorem moduli_univ_polAV :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l), IsLocallyNoetherian Xo.X ∧ IsReduced Xo.X ∧ (∀ n : ℕ, 0 < n → IsUnit (n : Γ(Xo.X, ⊤))) ∧ IsAbelianScheme Xo.univ.t.G ∧ ∀ (p : ∀ (A : Over Xo.X) [GrpObj A] [IsCommMonObj A], LB A.left → ℕ → Prop), (∀ P : PolAV Xo.X, p P.A P.L P.g) → p Xo.univ.t.G Xo.univ.t.PP.L (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) := by
  intro E _ _ _ H Dw l Xo
  exact ⟨UnivPol.isLocallyNoetherian Xo, UnivPol.isReduced Xo, UnivPol.isUnit_natCast Xo,
    ObjDim.isAbelianScheme Xo.univ, fun p h => h (UnivPol.pol Xo)⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsTwistPullBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistBaseChange

theorem eq_pullS_of_isPullSec {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left} (a : ℤ) {T T' : Over S}
    (h : T' ⟶ T) {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')}
    (H : IsPullSec A L a (h ▷ A) (whiskerRight_snd _ _) s s') : s' = GlobalTheory.VVRank.pullS A a h s := by

  exact DVR.SecOps.sec_ext H

theorem isTwistPull_baseChange : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left), L.IsLB → ∀ (T T' : Over S) (h : T' ⟶ T) (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (ψ' : T' ⊗ A ⟶ T' ⊗ A) (m' : T' ⊗ A ⟶ A) (hm' : ψ' ≫ snd T' A = m'), ψ' ≫ h ▷ A = h ▷ A ≫ ψ → ∀ (a b : ℤ) (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])) (α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T' A).left, m'.left] ![a, -b])), α.IsGen → α'.IsGen → LB.Gen.Corr L _ _ _ _ α' (LB.pullGen L _ _ α (h ▷ A).left) → ∀ (s : LB.Sec (LPow A L b T)) (t : LB.Sec (LPow A L a T)) (s' : LB.Sec (LPow A L b T')) (t' : LB.Sec (LPow A L a T')), IsTwistPull A L ψ m hm a b α s t → IsPullSec A L b (h ▷ A) (whiskerRight_snd _ _) s s' → IsPullSec A L a (h ▷ A) (whiskerRight_snd _ _) t t' → IsTwistPull A L ψ' m' hm' a b α' s' t' := by
  intro S A _ L hL T T' h ψ m hm ψ' m' hm' hψ a b α α' hα hα' hcorr s t s' t' hst hs ht
  obtain rfl := eq_pullS_of_isPullSec A b h hs
  obtain rfl := eq_pullS_of_isPullSec A a h ht

  have e : ψ'.left ≫ (h ▷ A).left = (h ▷ A).left ≫ ψ.left := by
    rw [← Over.comp_left, hψ, Over.comp_left]
  refine GlobalTheory.VVRank.isTwistPull_of_sv A hL hα' (fun y J hJ => ?_)

  have hv : val α' (𝟙 _) y J = val α (𝟙 _ ≫ (h ▷ A).left) y J :=
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_corr hJ hcorr _).trans (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull hJ α _ _)
  rw [GlobalTheory.VVRank.sv_pullS A a h t _ y hJ, GlobalTheory.VVRank.sv_pullS A b h s _ y hJ,
    GlobalTheory.VVRank.sv_of_isTwistPull A hst _ y hJ, hv]
  simp only [Category.id_comp, e]

end GlobalTheory.TwistBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModNSqIffExistsGenLatSum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_dualFamily_of_nsmul_integral {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) {N : ℕ} (hN : 0 < N)
    (hu : ∀ v ∈ L, ∀ b, ∃ u : 𝓞 E, (u : E) = (N : E) * v b) :
    ∃ (m : ℕ) (w : Fin m → L) (lam : Fin m → (L →ₗ[𝓞 E] 𝓞 E)), ∀ v, ∑ i, lam i v • w i = v := by
  classical
  have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hfg : L.FG := by
    have hle : L ≤ Submodule.span (𝓞 E)
        (Set.range fun b : Fin n => (Pi.single b (N : E)⁻¹ : Fin n → E)) := by
      intro v hv
      choose u hu' using hu v hv
      have : v = ∑ b, u b • (Pi.single b (N : E)⁻¹ : Fin n → E) := by
        funext c
        rw [Finset.sum_apply, Finset.sum_eq_single c]
        · simp only [Pi.smul_apply, Pi.single_eq_same]
          rw [Algebra.smul_def]
          change v c = (u c : E) * _
          rw [hu']; field_simp
        · intro b _ hb
          simp [Pi.single_eq_of_ne hb.symm]
        · simp
      rw [this]
      exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
    exact Submodule.FG.of_le (Submodule.fg_span (Set.finite_range _)) hle
  have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hfg
  have : Module.FinitePresentation (𝓞 E) L := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) L := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 E) L
  refine ⟨m, fun i => f (Pi.single i 1), fun i => (LinearMap.proj i) ∘ₗ g, fun v => ?_⟩
  have h1 : f (g v) = v := LinearMap.congr_fun hfg v
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [← h1, pi_eq_sum_univ' (g v), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  congr 2

theorem mem_stdLat_iff_integral {E : Type} [Field E] [NumberField E] {n : ℕ} (v : Fin n → E) :
    v ∈ stdLat E n ↔ ∀ b, ∃ u : 𝓞 E, (u : E) = v b := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]

theorem modN_sq_iff_exists_genLat_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∀ a : Fin n → Dw.La, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • a j)) ↔ ∃ (m : ℕ) (x : Fin m → Dw.La) (v : Fin m → Fin n → 𝓞 E), (∀ i, ∃ w ∈ Λ.La, ∀ b, (v i b : E) = (N : E) * w b) ∧ ∀ b, a b = ∑ i, v i b • x i := by
  classical
  intro E _ _ _ H Dw n Λ N hU hN hle a
  have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hNO : (N : 𝓞 E) ≠ 0 := by exact_mod_cast hN.ne'
  have inj : Function.Injective (fun x : 𝓞 E => (x : E)) := RingOfIntegers.coe_injective
  have he : ∀ b : Fin n, (Pi.single b (N : E) : Fin n → E) ∈ Λ.La := by
    intro b
    apply hle
    have h1 : (Pi.single b (1 : E) : Fin n → E) ∈ stdLat E n := by
      rw [mem_stdLat_iff_integral]
      intro c
      by_cases h : c = b
      · subst h; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Pi.single_eq_of_ne h]⟩
    have h2 := Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (N : 𝓞 E)) h1
    convert h2 using 1
    funext c
    by_cases h : c = b
    · subst h; simp [Algebra.smul_def]
    · simp [Pi.single_eq_of_ne h]
  have hu : ∀ v ∈ Λ.La, ∀ b, ∃ u : 𝓞 E, (u : E) = (N : E) * v b := by
    intro v hv b
    obtain ⟨y, hy⟩ := (hU (Pi.single b (N : E))).1 (he b) v hv
    refine ⟨y, ?_⟩
    change algebraMap (𝓞 E) E y = _
    rw [hy, Finset.sum_eq_single b]
    · simp
    · intro c _ hc
      simp [Pi.single_eq_of_ne hc]
    · simp
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun b => b.elim0⟩
    obtain ⟨m, w, lam, hw⟩ := exists_dualFamily_of_nsmul_integral Λ.La hN hu
    let e : Fin n → Λ.La := fun b => ⟨Pi.single b (N : E), he b⟩
    have hx : ∀ i, ∃ x : Dw.La, ∑ j, lam i (e j) • a j = (N ^ 2) • x := by
      intro i
      refine h (Matrix.of fun _ j => (lam i (e j) : E) / N) ?_ (fun _ j => lam i (e j)) ?_ ⟨0, hn⟩
      · intro v hv
        rw [mem_stdLat_iff_integral]
        intro b
        refine ⟨lam i ⟨v, hv⟩, ?_⟩
        choose u hu' using hu v hv
        have h1 : ((N : 𝓞 E) * N) • (⟨v, hv⟩ : Λ.La) = ∑ j, u j • e j := by
          apply Subtype.ext
          funext c
          simp only [e, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
          rw [Finset.sum_eq_single c]
          · simp only [Pi.single_eq_same, Algebra.smul_def]
            change _ = (u c : E) * _
            rw [hu']; simp; ring
          · intro d _ hd
            simp [Pi.single_eq_of_ne hd.symm]
          · simp
        have h2 := congrArg (fun z => ((lam i z : 𝓞 E) : E)) h1
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_smul, map_sum, smul_eq_mul] at h2
        push_cast at h2
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
        apply mul_left_cancel₀ (mul_ne_zero hN' hN')
        rw [Finset.mul_sum]
        refine h2.trans (Finset.sum_congr rfl fun j _ => ?_)
        have := hu' j
        change (u j : E) * (lam i (e j) : E) = _
        rw [this]; field_simp
      · intro _ j
        simp only [Matrix.of_apply]; field_simp
    choose x hx using hx
    choose v hv using fun i => hu (w i) (w i).2
    refine ⟨m, x, v, fun i => ⟨w i, (w i).2, hv i⟩, fun b => ?_⟩
    have := Dw.proj
    have hd : ∀ j, ∑ i, v i b * lam i (e j) = if j = b then (N : 𝓞 E) ^ 2 else 0 := by
      intro j
      apply inj
      have h1 := congrFun (congrArg Subtype.val (hw (e j))) b
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        Algebra.smul_def] at h1
      have h2 : (((∑ i, v i b * lam i (e j) : 𝓞 E)) : E) = (N : E) * (e j : Fin n → E) b := by
        rw [← h1, Finset.mul_sum]
        change algebraMap (𝓞 E) E _ = _
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul]
        change (v i b : E) * _ = _
        rw [hv]; ring
      change (((∑ i, v i b * lam i (e j) : 𝓞 E)) : E) = _
      rw [h2]
      by_cases hj : j = b
      · subst hj; simp [e, sq]
      · simp [e, hj]
    apply smul_right_injective Dw.La (pow_ne_zero 2 hNO)
    have hx' : ∀ i, ((N : 𝓞 E) ^ 2) • x i = ∑ j, lam i (e j) • a j := by
      intro i
      rw [hx, ← Nat.cast_smul_eq_nsmul (𝓞 E), Nat.cast_pow]
    calc ((N : 𝓞 E) ^ 2) • a b = ∑ j, (∑ i, v i b * lam i (e j)) • a j := by
          simp [hd]
      _ = ∑ i, v i b • ∑ j, lam i (e j) • a j := by
          simp only [Finset.sum_smul, Finset.smul_sum, mul_smul]
          exact Finset.sum_comm
      _ = ((N : 𝓞 E) ^ 2) • ∑ i, v i b • x i := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← hx', smul_comm]
  · rintro ⟨m, x, v, hv, ha⟩ mu hmu cm hcm i
    choose w hw hvw using hv
    choose y hy using fun k => (mem_stdLat_iff_integral _).1 (hmu (w k) (hw k)) i
    have hd : ∀ k, ∑ j, cm i j * v k j = (N : 𝓞 E) ^ 2 * y k := by
      intro k
      apply inj
      change algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_mul]
      change _ = _ * (y k : E)
      rw [hy]
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul]
      change (cm i j : E) * (v k j : E) = _
      rw [hcm, hvw]; simp; ring
    refine ⟨∑ k, y k • x k, ?_⟩
    calc ∑ j, cm i j • a j = ∑ k, (∑ j, cm i j * v k j) • x k := by
          simp only [ha, Finset.sum_smul, Finset.smul_sum, mul_smul]
          exact Finset.sum_comm
      _ = _ := by
          rw [← Nat.cast_smul_eq_nsmul (𝓞 E), Nat.cast_pow, Finset.smul_sum]
          simp only [hd, mul_smul]

end GlobalTheory
end

