module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2827
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2995
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2998
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0865
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2996
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2978
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2992
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSectionsLinearSimilitudeMemKernelPolarization
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPel.HT.Hecke.KerPol
open GlobalTheory.UPel.HT.Hecke

theorem hecke_sections_triv : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, (∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (toUnit o.A ≫ h) (𝟙 o.A)).left).Gen, t.IsGen) ∧ (∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (𝟙 o.A) (toUnit o.A ≫ h)).left).Gen, t.IsGen) := by
  intro p _ D R _ b g c k N hc hk hN hNp hEF hg hck S s o h hh
  have hfib := GlobalTheory.T.hecke_bundle_trivial_geometric_fibre p D R b g c k N hc hk hN hNp hEF hg hck S s o h hh
  obtain ⟨x, rfl⟩ := hh
  have hP := o.isLB
  have clsPow : ∀ {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (n : ℕ) (h' : (GlobalTheory.UPel.HT.Hecke.lbPow L n).IsLB),
      GlobalTheory.CechPic.cls (GlobalTheory.UPel.HT.Hecke.lbPow L n) h' = n • GlobalTheory.CechPic.cls L hL := by
    intro X L hL n h'
    unfold GlobalTheory.UPel.HT.Hecke.lbPow at h' ⊢
    rw [GlobalTheory.CechPic.cls_linComb hL]
    simp [GlobalTheory.CechPic.pull_id]
  have hQ : (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb hP _ _
  have hadd := (GlobalTheory.AbDual.additive_of_cube GlobalTheory.CubeTop.cubeTheorem o.ab o.ab hP o.rig₁ o.rig₂).1
  have evcCls : ∀ {M : LB (o.A ⊗ o.A).left} (hM : M.IsLB) {Y : Over S} (a t : Y ⟶ o.A),
      GlobalTheory.AbDual.evc hM a t = GlobalTheory.CechPic.pull (lift a t).left (GlobalTheory.CechPic.cls M hM) := by
    intro M hM Y a t
    rw [← GlobalTheory.AbDual.cls_ev hM a t (pull_isLB hM _), GlobalTheory.CechPic.cls_pull hM]
  have evcQ : ∀ {Y : Over S} (a t : Y ⟶ o.A),
      GlobalTheory.AbDual.evc hQ a t = (k ^ 2 / c) • GlobalTheory.AbDual.evc hP a t := by
    intro Y a t
    rw [evcCls hQ, evcCls hP, clsPow hP _ hQ, map_nsmul]
  have hpow : ∀ (a : o.A ⟶ o.A) (n : ℕ),
      GlobalTheory.AbDual.evc hP (a ^ n) (𝟙 o.A) = n • GlobalTheory.AbDual.evc hP a (𝟙 o.A) := by
    intro a n
    induction n with
    | zero => rw [pow_zero, zero_smul]; exact GlobalTheory.AbDual.IsAdditive.evc_one hP hadd _
    | succ n ih => rw [pow_succ, (GlobalTheory.AbDual.isAdditive_iff hP).1 hadd, ih, succ_nsmul]
  have etaPow : ∀ (n : ℕ) (z : D.La), (o.eta z) ^ n = o.eta (n • z) := by
    intro n z
    induction n with
    | zero => rw [pow_zero, zero_smul, eta_zero]
    | succ n ih => rw [pow_succ, ih, succ_nsmul, o.eta_add]
  set th : o.A ⟶ o.A := toUnit o.A ≫ o.eta (N • g x) with hth
  have hk1 : th ^ k = 1 := by
    rw [hth, ← MonObj.comp_pow, etaPow, smul_smul, show k * N = N * k from mul_comm _ _, o.eta_ker, MonObj.comp_one]
  have htors : k • GlobalTheory.AbDual.evc hP th (𝟙 o.A) = 0 := by
    rw [← hpow, hk1]; exact GlobalTheory.AbDual.IsAdditive.evc_one hP hadd _
  have hQth : GlobalTheory.AbDual.evc hQ th (𝟙 o.A) = 0 := by
    have hM : (GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)).IsLB := pull_isLB hQ _
    have hunit : IsUnit ((k : Γ(S, ⊤))) := by
      have hR := b.unit k hk
      have e := hR.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
      have e2 := e.map (s.appTop.hom)
      simpa using e2
    have hrig : ∃ t : ((GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)).pull
        (1 : 𝟙_ (Over S) ⟶ o.A).left).Gen, t.IsGen := by
      rw [← GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hM _), GlobalTheory.CechPic.cls_pull hM, GlobalTheory.AbDual.cls_ev hQ,
        GlobalTheory.AbDual.pull_evc, evcQ, Category.comp_id, GlobalTheory.AbDual.evc_one_right hP o.rig₂, smul_zero]
    have hpowM : ∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow (GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)) k).Gen, t.IsGen := by
      have hMk : (GlobalTheory.UPel.HT.Hecke.lbPow (GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)) k).IsLB :=
        LB.isLB_linComb hM _ _
      refine (GlobalTheory.CechPic.cls_eq_zero_iff hMk).1 ?_
      rw [clsPow hM k hMk, GlobalTheory.AbDual.cls_ev hQ, evcQ,
        smul_comm, htors, smul_zero]
    obtain ⟨t, ht⟩ := GlobalTheory.T.rigidified_lineBundle_trivial_of_torsion_geometricFibres S o.A o.ab _ hM hrig k hunit hpowM hfib
    exact (GlobalTheory.AbDual.triv_ev_iff hQ _ _).1 ⟨t, ht⟩
  have hsw : GlobalTheory.CechPic.cls o.P hP = GlobalTheory.CechPic.cls (GlobalTheory.AbDual.swap o.P) (pull_isLB hP _) :=
    (GlobalTheory.CechPic.cls_eq_iff _ _).2 o.symm
  refine ⟨(GlobalTheory.AbDual.triv_ev_iff hQ _ _).2 hQth, (GlobalTheory.AbDual.triv_ev_iff hQ _ _).2 ?_⟩
  rw [evcQ, evcCls hP, hsw, ← evcCls (pull_isLB hP _), GlobalTheory.AbDual.evc_swap hP, ← evcQ]
  exact hQth

end GlobalTheory.UPel.HT.Hecke.KerPol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomSchemeLow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanonHom

theorem pullSec : ∀ {S S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left),
    IsGrpPullback G' G f φ → ∀ (O : Type) [CommRing O] (a' : OAct O G') (a : OAct O G), (∀ r, (a'.act r).left ≫ φ = φ ≫ (a.act r).left) →
    ∀ (X : Type) [AddCommGroup X] [Module O X] (T : Over S') (x₀ : X → (Over.mk (T.hom ≫ f) ⟶ G)),
    (∀ y z, x₀ (y + z) = x₀ y * x₀ z) → (∀ (r : O) y, x₀ (r • y) = x₀ y ≫ a.act r) →
    ∃ x : X → (T ⟶ G'), (∀ y, (x y).left ≫ φ = (x₀ y).left) ∧ (∀ y z, x (y + z) = x y * x z) ∧
      ∀ (r : O) y, x (r • y) = x y ≫ a'.act r := by
  intro S S' G' _ G _ f φ hφ O _ a' a ha X _ _ T x₀ hadd hlin
  have hw : ∀ y, (x₀ y).left ≫ G.hom = T.hom ≫ f := fun y => Over.w (x₀ y)
  let x : X → (T ⟶ G') := fun y => Over.homMk (hφ.1.lift (x₀ y).left T.hom (hw y)) (hφ.1.lift_snd _ _ _)
  have hx : ∀ y, (x y).left ≫ φ = (x₀ y).left := fun y => hφ.1.lift_fst _ _ _
  have uniq : ∀ (p q : T ⟶ G'), p.left ≫ φ = q.left ≫ φ → p = q := fun p q h => by
    ext; apply hφ.1.hom_ext h; rw [Over.w p, Over.w q]
  refine ⟨x, hx, fun y z => uniq _ _ ?_, fun r y => uniq _ _ ?_⟩
  · rw [hx, hadd, hφ.2 T (x y) (x z) (x₀ y) (x₀ z) (hx y).symm (hx z).symm]
  · rw [hx, hlin, Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc, hx]

theorem pushSec : ∀ {S S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left),
    IsGrpPullback G' G f φ → ∀ (O : Type) [CommRing O] (a' : OAct O G') (a : OAct O G), (∀ r, (a'.act r).left ≫ φ = φ ≫ (a.act r).left) →
    ∀ (X : Type) [AddCommGroup X] [Module O X] (T : Over S') (x : X → (T ⟶ G')),
    (∀ y z, x (y + z) = x y * x z) → (∀ (r : O) y, x (r • y) = x y ≫ a'.act r) →
    ∃ x₀ : X → (Over.mk (T.hom ≫ f) ⟶ G), (∀ y, (x₀ y).left = (x y).left ≫ φ) ∧ (∀ y z, x₀ (y + z) = x₀ y * x₀ z) ∧
      ∀ (r : O) y, x₀ (r • y) = x₀ y ≫ a.act r := by
  intro S S' G' _ G _ f φ hφ O _ a' a ha X _ _ T x hadd hlin
  have hw : ∀ y, ((x y).left ≫ φ) ≫ G.hom = (Over.mk (T.hom ≫ f)).hom := fun y => by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w (x y)]; rfl
  refine ⟨fun y => Over.homMk ((x y).left ≫ φ) (hw y), fun y => rfl, fun y z => ?_, fun r y => ?_⟩
  · ext
    change (x (y + z)).left ≫ φ = _
    rw [hadd]
    exact (hφ.2 T (x y) (x z) (Over.homMk _ (hw y)) (Over.homMk _ (hw z)) rfl rfl).symm
  · ext
    simp only [Over.homMk_left, Over.comp_left, hlin, Category.assoc, ha]

theorem objMap_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'}
    {S S' : Scheme.{0}} {s' : S' ⟶ Sp B'} {s : S ⟶ Sp B} {o' : Obj D l b' s'} {o : Obj D l b s} {f f' : S' ⟶ S}
    (h : f = f') (m : ObjMap o' o f) : ∃ m' : ObjMap o' o f', m'.toSABMap.φ = m.toSABMap.φ := by
  subst h; exact ⟨m, rfl⟩

theorem obj_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s₁ s₂ : S ⟶ Sp B}
    (h : s₁ = s₂) (o : Obj D l b s₁) : ∃ o₂ : Obj D l b s₂, ∀ {S₀ : Scheme.{0}} {B₀ : Type} [CommRing B₀] {b₀ : Base l B₀}
      {s₀ : S₀ ⟶ Sp B₀} (o₀ : Obj D l b₀ s₀) (f : S ⟶ S₀), Nonempty (ObjMap o o₀ f) → Nonempty (ObjMap o₂ o₀ f) := by
  subst h; exact ⟨o, fun _ _ h => h⟩

theorem homScheme_low : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X], ∃ (Cs : Scheme.{0}) (g : Cs ⟶ Sp c.F) (oC : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) (g ≫ lowMap c (RingHom.id c.F))) (u : X → (𝟙_ (Over Cs) ⟶ oC.t.G)), SmoothOfRelativeDimension (D'.dim + Module.finrank (𝓞 E) X * (Module.finrank ℚ E / 2 * (D'.p + D'.q))) g ∧ (∀ y z, u (y + z) = u y * u z) ∧ (∀ (a : 𝓞 E) y, u (a • y) = u y ≫ oC.t.act.act a) ∧ (∀ (V : Type) [CommRing V] [IsReduced V] (bV : c.F →+* V) (o' : LowObj D' c bV) (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) → (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (v : Sp V ⟶ Cs) (m : ObjMap o' oC v), v ≫ g = spMap bV ∧ ∀ y, (x y).left ≫ m.toSABMap.φ = v ≫ (u y).left) ∧ (∀ (A : Type) [CommRing A] [IsReduced A] (v₁ v₂ : Sp A ⟶ Cs), v₁ ≫ g = v₂ ≫ g → ∀ (s' : Sp A ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s') (m₁ : ObjMap o'' oC v₁) (m₂ : ObjMap o'' oC v₂) (z : X → (Sp A ⟶ o''.t.G.left)), s' = v₁ ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v₁ ≫ (u y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = v₂ ≫ (u y).left) → v₁ = v₂) ∧ (∀ (k : Type) [Field k] (v : Sp (DualNumber k) ⟶ Cs) (s' : Sp (DualNumber k) ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s') (m₁ : ObjMap o'' oC v) (m₂ : ObjMap o'' oC (constPt v)) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)), s' = v ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v ≫ (u y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = constPt v ≫ (u y).left) → v = constPt v) := by
  intro E _ _ _ H D' l c X _ _ _ _
  have hXo : Nonempty (Moduli D' (LowDat.lowLevel l)) := by
    by_cases hpq : 1 ≤ D'.p + D'.q
    · exact GlobalTheory.Moduli.moduli_scheme_exists E H D' _ hpq
    · exact _root_.GlobalTheory.UCanon.RankZero.nonempty_moduli H D' _ (by omega)
  obtain ⟨Xo⟩ := hXo
  set sF : Sp c.F ⟶ Sp (KA (LowDat.lowLevel l)) := lowMap c (RingHom.id c.F) with hsF
  have P := _root_.GlobalTheory.UCanon.obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)
  obtain ⟨oY, ⟨mY⟩⟩ := P.1 Xo.s Xo.univ (pullback.fst Xo.s sF) (pullback.snd Xo.s sF ≫ sF) pullback.condition.symm
  have hB : IsAbelianScheme oY.t.G := ⟨inferInstance, oY.t.semi.smooth, oY.proper, oY.t.semi.geomConnected⟩
  have hg := _root_.GlobalTheory.UObjDim.smoothOfRelativeDimension_obj D' (LowDat.lowLevel l) (pullback.snd Xo.s sF ≫ sF) oY
  haveI : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : Module.Projective (𝓞 E) X := GlobalTheory.Forms.projective_of_int _ _
  obtain ⟨C, _, u, -, hCsm, -, hadd, hlin, huniv⟩ :=
    GlobalTheory.HomScheme.exists_homObj_relDim _ oY.t.G hB _ hg oY.t.act X
  obtain ⟨oC, ⟨mC⟩⟩ := P.1 (pullback.snd Xo.s sF ≫ sF) oY C.hom ((C.hom ≫ pullback.snd Xo.s sF) ≫ sF)
    (Category.assoc _ _ _)
  obtain ⟨u', hu'φ, hu'add, hu'lin⟩ := pullSec oC.t.G oY.t.G C.hom mC.toSABMap.φ mC.cart (𝓞 E) oC.t.act oY.t.act mC.act X
    (𝟙_ (Over C.left)) (fun y => Over.homMk (𝟙 C.left) (by simp) ≫ u y) (fun y z => by rw [hadd, comp_mul])
    (fun r y => by rw [hlin, Category.assoc])
  have key : ∀ {T : Scheme.{0}} (v₁ v₂ : T ⟶ C.left), v₁ ≫ C.hom = v₂ ≫ C.hom →
      (∀ y, v₁ ≫ (u y).left = v₂ ≫ (u y).left) → v₁ = v₂ := by
    intro T v₁ v₂ hw hu
    obtain ⟨c0, -, huq⟩ := huniv (Over.mk (v₁ ≫ C.hom)) (fun y => Over.homMk v₁ rfl ≫ u y)
      (fun y z => by rw [hadd, comp_mul]) (fun r y => by rw [hlin, Category.assoc])
    have e1 := huq (Over.homMk v₁ rfl) (fun y => rfl)
    have e2 := huq (Over.homMk v₂ hw.symm) (fun y => by ext; simpa using (hu y).symm)
    simpa using congrArg CommaMorphism.left (e1.trans e2.symm)
  have hu'l : ∀ y, (u' y).left ≫ mC.toSABMap.φ = (u y).left := fun y => by rw [hu'φ]; simp
  have key2 : ∀ (A : Type) [CommRing A], IsNilpotent (nilradical A) → ∀ (v₁ v₂ : Sp A ⟶ C.left)
      (s' : Sp A ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s')
      (m₁ : ObjMap o'' oC v₁) (m₂ : ObjMap o'' oC v₂) (z : X → (Sp A ⟶ o''.t.G.left)), v₁ ≫ C.hom = v₂ ≫ C.hom →
      (∀ y, z y ≫ m₁.toSABMap.φ = v₁ ≫ (u' y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = v₂ ≫ (u' y).left) → v₁ = v₂ := by
    intro A _ hA v₁ v₂ s' o'' m₁ m₂ z hw hz₁ hz₂
    obtain ⟨k₁, hk₁⟩ := (P.2 _ _ s' oY oC o'' C.hom v₁ mC).1 m₁
    obtain ⟨k₂, hk₂⟩ := (P.2 _ _ s' oY oC o'' C.hom v₂ mC).1 m₂
    obtain ⟨k₂', hk₂'⟩ := objMap_congr hw.symm k₂
    have hφ := _root_.GlobalTheory.ObjMapUnique.objMap_unique_of_nilpotent_nilradical A hA s' _ o'' oY (v₁ ≫ C.hom) k₁ k₂'
    refine key v₁ v₂ hw fun y => ?_
    calc v₁ ≫ (u y).left = z y ≫ k₁.toSABMap.φ := by rw [hk₁, ← Category.assoc, hz₁, Category.assoc, hu'l]
      _ = z y ≫ k₂'.toSABMap.φ := by rw [hφ]
      _ = v₂ ≫ (u y).left := by rw [hk₂', hk₂, ← Category.assoc, hz₂, Category.assoc, hu'l]
  refine ⟨C.left, C.hom ≫ pullback.snd Xo.s sF, oC, u', ?_, hu'add, hu'lin, ?_, ?_, ?_⟩
  · haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := D'.dim)
    haveI h1 : SmoothOfRelativeDimension D'.dim (pullback.snd Xo.s sF) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @SmoothOfRelativeDimension D'.dim)
        (IsPullback.of_hasPullback Xo.s sF) Xo.smooth
    haveI := hCsm
    rw [add_comm]
    infer_instance
  · intro V _ _ bV o' x hxadd hxlin
    obtain ⟨f, ⟨hf, ⟨k⟩⟩, -⟩ := Xo.rep (Sp V) (lowMap c bV) inferInstance o'
    have hlow : lowMap c bV = spMap bV ≫ sF := by simp only [hsF, lowMap, spMap, ← Spec.map_comp]; rfl
    let fY : Sp V ⟶ pullback Xo.s sF := pullback.lift f (spMap bV) (hf.trans hlow)
    obtain ⟨k', -⟩ := objMap_congr (pullback.lift_fst f (spMap bV) (hf.trans hlow)).symm k
    obtain ⟨n, -⟩ := (P.2 Xo.s (pullback.snd Xo.s sF ≫ sF) (lowMap c bV) Xo.univ oY o' (pullback.fst _ _) fY mY).2 k'
    obtain ⟨x₀, hx₀, hx₀add, hx₀lin⟩ := pushSec o'.t.G oY.t.G fY n.toSABMap.φ n.cart (𝓞 E) o'.t.act oY.t.act n.act X
      (𝟙_ (Over (Sp V))) x hxadd hxlin
    obtain ⟨cc, hcc, -⟩ := huniv (Over.mk ((𝟙_ (Over (Sp V))).hom ≫ fY)) x₀ hx₀add hx₀lin
    have hccw : cc.left ≫ C.hom = fY := by simpa using Over.w cc
    obtain ⟨n', hn'⟩ := objMap_congr hccw.symm n
    obtain ⟨m, hm⟩ := (P.2 _ _ (lowMap c bV) oY oC o' C.hom cc.left mC).2 n'
    refine ⟨cc.left, m, ?_, fun y => ?_⟩
    · rw [← Category.assoc, hccw, pullback.lift_snd]
    · apply mC.cart.1.hom_ext
      · rw [Category.assoc, ← hm, hn', Category.assoc, hu'l, ← hx₀, ← hcc y]
        rfl
      · rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w (x y), Category.assoc, Over.w (u' y)]
        simp
  · intro A _ _ v₁ v₂ hv s' o'' m₁ m₂ z hs' hz₁ hz₂
    refine key2 A (by rw [nilradical_eq_zero]; exact IsNilpotent.zero) v₁ v₂ s' o'' m₁ m₂ z ?_ hz₁ hz₂
    obtain ⟨k₁, -⟩ := (P.2 _ _ s' oY oC o'' C.hom v₁ mC).1 m₁
    obtain ⟨K₁, -⟩ := (P.2 _ _ s' Xo.univ oY o'' (pullback.fst _ _) (v₁ ≫ C.hom) mY).1 k₁
    obtain ⟨k₂, -⟩ := (P.2 _ _ s' oY oC o'' C.hom v₂ mC).1 m₂
    obtain ⟨K₂, -⟩ := (P.2 _ _ s' Xo.univ oY o'' (pullback.fst _ _) (v₂ ≫ C.hom) mY).1 k₂
    have hv' := hv =≫ sF
    simp only [Category.assoc] at hv'
    have hs₁ : ((v₁ ≫ C.hom) ≫ pullback.fst Xo.s sF) ≫ Xo.s = s' := by
      rw [hs']; simp only [Category.assoc, pullback.condition]
    have hs₂ : ((v₂ ≫ C.hom) ≫ pullback.fst Xo.s sF) ≫ Xo.s = s' := by
      rw [hs']; simp only [Category.assoc, pullback.condition]; exact hv'.symm
    have hfst := (Xo.rep (Sp A) s' inferInstance o'').unique ⟨hs₁, ⟨K₁⟩⟩ ⟨hs₂, ⟨K₂⟩⟩
    apply pullback.hom_ext
    · simpa only [Category.assoc] using hfst
    · simpa only [Category.assoc] using hv
  · intro k _ v s' o'' m₁ m₂ z hs' hz₁ hz₂
    refine key2 (DualNumber k) (IsNoetherianRing.isNilpotent_nilradical _) v (constPt v) s' o'' m₁ m₂ z ?_ hz₁ hz₂
    haveI : FiniteDimensional ℚ c.F := c.fin
    haveI : Algebra.IsAlgebraic ℚ c.F := Algebra.IsAlgebraic.of_finite ℚ c.F
    have hcp : ∀ {W : Scheme.{0}} (w : C.left ⟶ W), constPt v ≫ w = constPt (v ≫ w) := fun w => by simp [constPt]
    obtain ⟨k₁, -⟩ := (P.2 _ _ s' oY oC o'' C.hom v mC).1 m₁
    obtain ⟨K₁, -⟩ := (P.2 _ _ s' Xo.univ oY o'' (pullback.fst _ _) (v ≫ C.hom) mY).1 k₁
    obtain ⟨k₂, -⟩ := (P.2 _ _ s' oY oC o'' C.hom (constPt v) mC).1 m₂
    obtain ⟨K₂, -⟩ := (P.2 _ _ s' Xo.univ oY o'' (pullback.fst _ _) (constPt v ≫ C.hom) mY).1 k₂
    obtain ⟨K₁', -⟩ := objMap_congr (Category.assoc v C.hom (pullback.fst Xo.s sF)) K₁
    obtain ⟨K₂', -⟩ := objMap_congr (show (constPt v ≫ C.hom) ≫ pullback.fst Xo.s sF =
      constPt (v ≫ C.hom ≫ pullback.fst Xo.s sF) by simp [constPt]) K₂
    have hs₁ : s' = (v ≫ C.hom ≫ pullback.fst Xo.s sF) ≫ Xo.s := by
      rw [hs']; simp only [Category.assoc, pullback.condition]
    obtain ⟨o₂, ho₂⟩ := obj_congr hs₁ o''
    have hfst := Xo.unram k _ o₂ (ho₂ Xo.univ _ ⟨K₁'⟩) (ho₂ Xo.univ _ ⟨K₂'⟩)
    apply pullback.hom_ext
    · simp only [Category.assoc]; rw [hcp]; exact hfst
    · simp only [Category.assoc]; rw [hcp]; exact GlobalTheory.Models.RankZero.eq_constPt_field _

end GlobalTheory.UCanonHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealDescentToComponentCompactification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoincDown

theorem exists_assoc_pow {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    [IsDiscreteValuationRing V'] (f : V →+* V') (hf : Function.Injective f) [IsLocalHom f] {ϖ : V} (hϖ : Irreducible ϖ)
    {ϖ' : V'} (hϖ' : Irreducible ϖ') : ∃ m : ℕ, 1 ≤ m ∧ Associated (f ϖ) (ϖ' ^ m) := by
  have h0 : f ϖ ≠ 0 := fun h => hϖ.ne_zero (hf (by rw [h, map_zero]))
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible h0 hϖ'
  refine ⟨m, Nat.one_le_iff_ne_zero.2 fun e => ?_, hm⟩
  subst e
  rw [pow_zero] at hm
  exact hϖ.not_isUnit ((isUnit_map_iff f ϖ).1 (associated_one_iff_isUnit.1 hm))

theorem map_eq_span_pow {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    [IsDiscreteValuationRing V'] (f : V →+* V') {ϖ : V} (hϖ : Irreducible ϖ) {ϖ' : V'} (hϖ' : Irreducible ϖ') {m : ℕ}
    (hm : Associated (f ϖ) (ϖ' ^ m)) {I : Ideal V} {b : ℕ} (h : I.map f = Ideal.span {ϖ' ^ b}) :
    ∃ a : ℕ, b = m * a ∧ I = Ideal.span {ϖ ^ a} := by
  have hI : I ≠ ⊥ := by
    rintro rfl
    rw [Ideal.map_bot, eq_comm, Ideal.span_singleton_eq_bot] at h
    exact pow_ne_zero _ hϖ'.ne_zero h
  obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  refine ⟨a, ?_, rfl⟩
  rw [Ideal.map_span, Set.image_singleton, map_pow, Ideal.span_singleton_eq_span_singleton] at h
  have h2 : Associated (ϖ' ^ (m * a)) (ϖ' ^ b) := by
    rw [pow_mul]; exact (hm.pow_pow (n := a)).symm.trans h
  have e1 := (pow_dvd_pow_iff hϖ'.ne_zero hϖ'.not_isUnit).1 h2.dvd
  have e2 := (pow_dvd_pow_iff hϖ'.ne_zero hϖ'.not_isUnit).1 h2.symm.dvd
  omega

theorem idealDescent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (A : Set C.Z), IsClopen A → IsIrreducible A → (A ∩ Set.range C.i).Nonempty → ∀ (X₁ : USetup C) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = A → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range C.i) → UValThru Xo c C.i X₁.π Set.univ φ J₁ ι → ∃ (d : ℕ) (J : C.Z.IdealSheafData), 1 ≤ d ∧ (∀ x ∈ J.support, x ∈ A ∧ x ∉ Set.range C.i) ∧ UValThru Xo c C.i (𝟙 C.Z) A φ J d := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C A hAc hAi hAn X₁ ι J₁ hι hπ hsupp hord
  obtain ⟨k, J, hk, hJs, hJo⟩ := _root_.GlobalTheory.UPoinc.UNormDown.normDescent E H Dw hpq φ hφ l Xo c C A hAc hAi hAn X₁ ι J₁ hι hπ hsupp hord
  refine ⟨k * ι, J, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), hJs, ?_⟩
  intro W _ _ _ hW ϖ hϖ χ y hy hA t tK h1 h2 P be hbe hmono
  let T : UTrait Xo c := { V := W, cdvr := hW, ϖ := ϖ, irr := hϖ, y := y, t := t, gen := ⟨tK, h1, h2⟩, P := P, be := be, lev := hbe, mono := hmono }
  have hy' : T.y ≫ C.i = jK T.V ≫ χ := by simpa using hy
  have hc : IsClopen (Set.range X₁.π) := by rw [hπ]; exact hAc
  obtain ⟨T', f, fK, ξ₁, hf, hfl, hfK, hyy, hsq, hgen⟩ := _root_.GlobalTheory.UPoinc.uTraitLift_setup E H Dw l Xo c C X₁ hc T χ hy' (by rw [hπ]; exact hA)
  obtain ⟨tK', g1, g2⟩ := T'.gen
  obtain ⟨a₁, ha₁, hJ₁⟩ := hord T'.V T'.cdvr T'.ϖ T'.irr ξ₁ T'.y hgen trivial T'.t tK' g1 g2 T'.P T'.be T'.lev T'.mono
  have hJ := hJo T' ξ₁ hgen
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  haveI : IsDiscreteValuationRing T'.V := T'.cdvr.1
  obtain ⟨m, hm1, hm⟩ := exists_assoc_pow f hf T.irr T'.irr
  have hφ' := _root_.GlobalTheory.UPoinc.UTraitRam.evalZ_eq_mul E H Dw l Xo c hpq T T' f fK hf hfl hfK hyy m hm φ hφ
  have e1 : (idlAlong J χ).map f = Ideal.span {T'.ϖ ^ (a₁ * k)} := by
    rw [← GlobalTheory.TraitOrder.idlAlong_comp, hsq, hJ, hJ₁, Ideal.span_singleton_pow, ← pow_mul]
  obtain ⟨a, hb, ha⟩ := map_eq_span_pow f T.irr T'.irr hm e1
  refine ⟨a, ?_, ha⟩
  have hb' : ((a₁ : ℝ) * k) = m * a := by exact_mod_cast hb
  rw [ha₁, hφ'] at hb'
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  push_cast
  apply mul_left_cancel₀ hm0.ne'
  have : (T.be : LinearMap.BilinForm ℤ T.P.D.toPre.X) = be := rfl
  linarith [hb']

end GlobalTheory.UPoincDown
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveModOfSurjectiveModOpposite
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

noncomputable section

namespace GlobalTheory.LowFilt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem datum_finite_int (D : Datum H) : Module.Finite ℤ D.La := by
  haveI := D.fin
  exact Module.Finite.trans (𝓞 E) D.La

theorem datum_isTorsionFree_int (D : Datum H) : Module.IsTorsionFree ℤ D.La := by
  refine Module.isTorsionFree_iff_smul_eq_zero.2 ?_
  intro k x hkx
  by_contra hk
  push_neg at hk
  have hx : x = 0 := D.unimod.1 (LinearMap.ext fun b => by
    have := congrArg (fun v => D.EF v b) hkx
    simp only [map_zsmul, LinearMap.smul_apply, map_zero, LinearMap.zero_apply, smul_eq_mul, mul_eq_zero] at this
    simpa using this.resolve_left hk.1)
  exact hk.2 hx

theorem sub_free_finite (D : Datum H) (Z : Submodule (𝓞 E) D.La) : Module.Free ℤ Z ∧ Module.Finite ℤ Z := by
  haveI := datum_finite_int D
  haveI := datum_isTorsionFree_int D
  haveI : IsNoetherian ℤ D.La := isNoetherian_of_isNoetherianRing_of_finite ℤ D.La
  let f : Z →ₗ[ℤ] D.La := Z.subtype.toAddMonoidHom.toIntLinearMap
  have hf : Function.Injective f := Subtype.val_injective
  haveI : Module.Finite ℤ Z := Module.Finite.of_injective f hf
  haveI : Module.IsTorsionFree ℤ Z := hf.moduleIsTorsionFree f (fun r m => f.map_smul r m)
  exact ⟨inferInstance, inferInstance⟩

theorem IsOpp.finrank_int_eq {D : Datum H} {Z Z' : Submodule (𝓞 E) D.La} (h : IsOpp D Z Z') :
    Module.finrank ℤ Z' = Module.finrank ℤ Z := by
  obtain ⟨hZf, hZn⟩ := sub_free_finite D Z
  let ψ : Z' →ₗ[ℤ] Module.Dual ℤ Z :=
    { toFun := fun b => (D.EF.flip (b : D.La)).comp Z.subtype.toAddMonoidHom.toIntLinearMap
      map_add' := fun b b' => by ext a; simp
      map_smul' := fun k b => by ext a; simp }
  have hψ : Function.Bijective ψ := by
    refine ⟨fun b b' hbb => ?_, fun φ => ?_⟩
    · obtain ⟨c, -, hu⟩ := h.2.2.1 ((ψ b).toAddMonoidHom)
      have e1 := hu b (fun a => rfl)
      have e2 := hu b' (fun a => by rw [hbb]; rfl)
      exact e1.trans e2.symm
    · obtain ⟨b, hb, -⟩ := h.2.2.1 φ.toAddMonoidHom
      exact ⟨b, LinearMap.ext fun a => hb a⟩
  rw [(LinearEquiv.ofBijective ψ hψ).finrank_eq]
  classical
  let bZ := Module.Free.chooseBasis ℤ Z
  rw [Module.finrank_eq_card_basis bZ.dualBasis, Module.finrank_eq_card_basis bZ]

theorem IsOpp.mem_nsmul_of_surj_mod {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (D : Datum H) (y : D.La →ₗ[𝓞 E] X) (n : ℕ) (hn : 0 < n) (Z Z' : Submodule (𝓞 E) D.La)
    (h : IsOpp D Z Z') (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X)
    (hs : ∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) (b : D.La) (hb : b ∈ Z') (hy : ∃ e, y b = n • e) :
    ∃ e ∈ Z', b = n • e := by
  obtain ⟨hZf, hZn⟩ := sub_free_finite D Z
  obtain ⟨hZf', hZn'⟩ := sub_free_finite D Z'
  have hrank : Module.finrank ℤ Z' = Module.finrank ℤ X := by
    rw [h.finrank_int_eq, GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul E Z,
      GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul E X, hr]
  let nB : AddSubgroup X := (nsmulAddMonoidHom n : X →+ X).range
  let nA : AddSubgroup Z' := (nsmulAddMonoidHom n : Z' →+ Z').range
  let g : Z' →+ X := y.toAddMonoidHom.comp Z'.subtype.toAddMonoidHom
  let f : Z' →+ X ⧸ nB := (QuotientAddGroup.mk' nB).comp g
  have hf : Function.Surjective f := by
    rintro ⟨x⟩
    obtain ⟨c, hc, e, he⟩ := hs x
    refine ⟨⟨c, hc⟩, ?_⟩
    show (QuotientAddGroup.mk (y c) : X ⧸ nB) = QuotientAddGroup.mk x
    rw [he, QuotientAddGroup.eq]
    exact ⟨-e, by simp⟩
  have hAK : nA ≤ f.ker := by
    rintro _ ⟨a, rfl⟩
    rw [AddMonoidHom.mem_ker]
    show (QuotientAddGroup.mk (y ((n • a : Z') : D.La)) : X ⧸ nB) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact ⟨y a, by simp⟩
  have hK : f.ker.index = n ^ Module.finrank ℤ X := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf, AddSubgroup.card_top]
    exact AddSubgroup.index_range_nsmul X n
  have hA : nA.index = n ^ Module.finrank ℤ X := by
    rw [← hrank]
    exact AddSubgroup.index_range_nsmul Z' n
  have hpos : 0 < n ^ Module.finrank ℤ X := pow_pos hn _
  have hrel : nA.relIndex f.ker = 1 := by
    have := AddSubgroup.relIndex_mul_index hAK
    rw [hK, hA] at this
    exact (Nat.mul_eq_right hpos.ne').1 this
  have hmem : (⟨b, hb⟩ : Z') ∈ f.ker := by
    obtain ⟨e, he⟩ := hy
    rw [AddMonoidHom.mem_ker]
    show (QuotientAddGroup.mk (y b) : X ⧸ nB) = 0
    rw [QuotientAddGroup.eq_zero_iff, he]
    exact ⟨e, rfl⟩
  obtain ⟨c, hc⟩ := AddSubgroup.relIndex_eq_one.1 hrel hmem
  exact ⟨c, c.2, (congrArg Subtype.val hc).symm.trans rfl⟩

end GlobalTheory.LowFilt

theorem GlobalTheory.LowFilt.inj_mod_of_surj_mod : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ), 0 < n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X → (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) →
    ∀ b ∈ Z', (∃ e, y b = n • e) → ∃ e ∈ Z', b = n • e :=
  fun D _ _ _ _ _ y n hn Z Z' h hr hs b hb hy => IsOpp.mem_nsmul_of_surj_mod D y n hn Z Z' h hr hs b hb hy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameIdentityOfGenericPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralFrame_identity_of_genericPoint : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (N : ℕ) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A), b ^ N = 1 → ∀ (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen → ∀ (κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1)), Normd κ → (∀ z J, Good D.P.L z J → val t (toUnit (TF (R := V) (FractionRing V))).left z J ^ (N ^ 2) * val κ ((toUnit (TF (R := V) (FractionRing V))).left ≫ b.left) z J = 1) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V) (z : Z) J, Good D.P.L z J → val t r z J ^ (N ^ 2) * val κ (r ≫ b.left) z J = 1 := by
  first | exact @GlobalTheory.Poinc.Sep.FrameInt.kap_of_generic | exact GlobalTheory.Poinc.Sep.FrameInt.kap_of_generic | (intros; apply GlobalTheory.Poinc.Sep.FrameInt.kap_of_generic <;> assumption)
end

