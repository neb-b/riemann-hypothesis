module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomFromConstThickeningOfDerivation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.DerMor

def preHom {Z X : Scheme.{0}} (n : Z ⟶ X) (c : ∀ W : X.Opens, Γ(X, W) →+* Γ(Z, n ⁻¹ᵁ W))
    (hres : ∀ W W' (h : W' ≤ W) f, c W' (resG X h f) = resG Z (fun _ hy => h hy) (c W f)) :
    Z.toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := n.base
  c :=
    { app := fun W => CommRingCat.ofHom (c W.unop)
      naturality := fun W W' i => by
        ext f
        exact hres W.unop W'.unop i.unop.le f }

def deform {Z X : Scheme.{0}} (n : Z ⟶ X) (c : ∀ W : X.Opens, Γ(X, W) →+* Γ(Z, n ⁻¹ᵁ W))
    (hres : ∀ W W' (h : W' ≤ W) f, c W' (resG X h f) = resG Z (fun _ hy => h hy) (c W f))
    (hnil : ∀ W f, IsNilpotent (c W f - (n.app W).hom f)) : Z ⟶ X :=
  ⟨⟨preHom n c hres, fun x => ⟨fun a ha => by
    obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.germ_exist X.presheaf a
    have hU' : n x ∈ U := hU
    have h1 := PresheafedSpace.stalkMap_germ_apply (preHom n c hres) U x hU s
    have h2 : IsUnit ((Z.presheaf.germ (n ⁻¹ᵁ U) x hU').hom (c U s)) := by
      have ha' := ha
      erw [h1] at ha'
      exact ha'
    have h3 : IsUnit ((Z.presheaf.germ (n ⁻¹ᵁ U) x hU').hom ((n.app U).hom s)) := by
      have hn := ((hnil U s).map (Z.presheaf.germ (n ⁻¹ᵁ U) x hU').hom).neg
      have := hn.isUnit_add_left_of_commute h2 (Commute.all _ _)
      simpa using this
    have h4 := Scheme.Hom.germ_stalkMap_apply n U x hU' s
    have h5 : IsUnit ((n.stalkMap x).hom ((X.presheaf.germ U (n x) hU').hom s)) := by
      erw [h4]
      exact h3
    exact (isUnit_map_iff (n.stalkMap x).hom _).mp h5⟩⟩⟩

theorem deform_app {Z X : Scheme.{0}} (n : Z ⟶ X) (c : ∀ W : X.Opens, Γ(X, W) →+* Γ(Z, n ⁻¹ᵁ W))
    (hres : ∀ W W' (h : W' ≤ W) f, c W' (resG X h f) = resG Z (fun _ hy => h hy) (c W f))
    (hnil : ∀ W f, IsNilpotent (c W f - (n.app W).hom f)) (W : X.Opens) :
    (deform n c hres hnil).app W = CommRingCat.ofHom (c W) := rfl

def cH {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ U le_top).hom

theorem cH_eq {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (a : R) :
    constFn p U a = cH p U a := rfl

theorem appLE_cH {R : Type} [CommRing R] {X Y : Scheme.{0}} (p : X ⟶ Sp R) (f : Y ⟶ X) (U : X.Opens)
    (V : Y.Opens) (e : V ≤ f ⁻¹ᵁ U) (a : R) :
    (f.appLE U V e).hom (cH p U a) = cH (f ≫ p) V a := by
  unfold cH
  have key := Scheme.Hom.appLE_comp_appLE f p ⊤ U V le_top e
  rw [← CommRingCat.comp_apply, Category.assoc]
  exact congrArg (fun φ => ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ φ).hom a) key

theorem app_cH {R : Type} [CommRing R] {X Y : Scheme.{0}} (p : X ⟶ Sp R) (f : Y ⟶ X) (U : X.Opens)
    (a : R) : (f.app U).hom (cH p U a) = cH (f ≫ p) (f ⁻¹ᵁ U) a := by
  rw [Scheme.Hom.app_eq_appLE]
  exact appLE_cH p f U (f ⁻¹ᵁ U) le_rfl a

theorem res_cH {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U)
    (a : R) : resG X h (cH p U a) = cH p V a := by
  unfold cH resG
  have key := Scheme.Hom.appLE_map p (U := ⊤) (V := U) (V' := V) le_top (homOfLE h).op
  rw [← CommRingCat.comp_apply, Category.assoc]
  exact congrArg (fun φ => ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ φ).hom a) key

theorem cH_spMap {R S : Type} [CommRing R] [CommRing S] {X : Scheme.{0}} (q : X ⟶ Sp S) (g : R →+* S)
    (U : X.Opens) (a : R) : cH (q ≫ spMap g) U a = cH q U (g a) := by
  unfold cH spMap
  have k1 := Scheme.Hom.comp_appLE q (Spec.map (CommRingCat.ofHom g)) ⊤ U le_top
  have k3 := congrArg (fun φ => (φ ≫ q.appLE ⊤ U le_top).hom a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  simp only [Category.assoc] at k3
  exact (congrArg (fun φ => ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ φ).hom a) k1).trans k3.symm

theorem res_app {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    (f.app V).hom (resG X h a) = resG Y (fun _ hy => h hy) ((f.app U).hom a) := by
  unfold resG
  rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
  rfl

theorem appLE_app_of_section {Y Y' : Scheme.{0}} (ρ : Y' ⟶ Y) (j : Y ⟶ Y') (h : j ≫ ρ = 𝟙 Y)
    (O : Y.Opens) (e : O ≤ j ⁻¹ᵁ (ρ ⁻¹ᵁ O)) (a : Γ(Y, O)) :
    (j.appLE (ρ ⁻¹ᵁ O) O e).hom ((ρ.app O).hom a) = a := by
  have key : ∀ (g : Y ⟶ Y), g = 𝟙 Y → ∀ e' : O ≤ g ⁻¹ᵁ O, (g.appLE O O e').hom a = a := by
    intro g hg e'
    subst hg
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact congrArg (fun φ => φ.hom a) (Y.presheaf.map_id (Opposite.op O))
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  exact key _ h _

theorem ext_cH {R : Type} [CommRing R] {X : Scheme.{0}} (f g : X ⟶ Sp R)
    (h : ∀ a, cH f ⊤ a = cH g ⊤ a) : f = g := by
  have top : ∀ (k : X ⟶ Sp R) (r : R),
      cH k ⊤ r = (Scheme.Γ.map k.op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    intro k r
    have e1 : k.appLE ⊤ ⊤ le_top = k.app ⊤ := k.appLE_eq_app
    unfold cH
    rw [e1]
    rfl
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  ext r
  exact (top f r).symm.trans ((h r).trans (top g r))

def pert {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) (e : C)
    (he : e * e = 0) (d : A → B) (hadd : ∀ f f', d (f + f') = d f + d f')
    (hmul : ∀ f f', d (f * f') = a f * d f' + a f' * d f) : A →+* C where
  toFun f := b (a f) + e * b (d f)
  map_one' := by
    have h := hmul 1 1
    rw [show (1 : A) * 1 = 1 from mul_one 1, map_one] at h
    have h1 : d 1 = 0 := by linear_combination -h
    simp [h1]
  map_zero' := by
    have h := hadd 0 0
    simp only [add_zero] at h
    have h1 : d 0 = 0 := by linear_combination -h
    simp [h1]
  map_add' f f' := by
    simp only [hadd, map_add (f := _)]; ring
  map_mul' f f' := by
    simp only [hmul, map_add (f := _), map_mul]
    linear_combination (-(b (d f) * b (d f'))) * he

theorem exists_mor : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → ∀ (R : Type) [CommRing R] (xD : R →+* DualNumber ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : Y ⟶ X) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)), m ≫ p = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ spMap xD → LocDer q p m (fun r => (xD r).snd) ⊤ d → ∃ Φ : Y' ⟶ X, j ≫ Φ = m ∧ Φ ≫ p = π ≫ spMap xD := by
  intro Y Y' q π ρ j hpb hjρ hjπ R _ xD X p m d hmp hd
  have hee : ∀ V : Y'.Opens, cH π V DualNumber.eps * cH π V DualNumber.eps = 0 := by
    intro V
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  let c : ∀ W : X.Opens, Γ(X, W) →+* Γ(Y', (ρ ≫ m) ⁻¹ᵁ W) := fun W =>
    pert (m.app W).hom (ρ.app (m ⁻¹ᵁ W)).hom (cH π _ DualNumber.eps) (hee _) (d W)
      (hd.add W le_top) (hd.mul W le_top)
  have hres : ∀ W W' (h : W' ≤ W) f,
      c W' (resG X h f) = resG Y' (fun _ hy => h hy) (c W f) := by
    intro W W' h f
    show (ρ.app _).hom ((m.app W').hom (resG X h f)) +
        cH π _ DualNumber.eps * (ρ.app _).hom (d W' (resG X h f)) =
      resG Y' _ ((ρ.app _).hom ((m.app W).hom f) + cH π _ DualNumber.eps * (ρ.app _).hom (d W f))
    have h1 := (congrArg (ρ.app (m ⁻¹ᵁ W')).hom (res_app m h f)).trans
      (res_app ρ (U := m ⁻¹ᵁ W) (V := m ⁻¹ᵁ W') (fun _ hy => h hy) ((m.app W).hom f))
    have h2 := (congrArg (ρ.app (m ⁻¹ᵁ W')).hom (hd.res W W' h le_top f)).trans
      (res_app ρ (U := m ⁻¹ᵁ W) (V := m ⁻¹ᵁ W') (fun _ hy => h hy) (d W f))
    have h3 := (res_cH π (U := ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) (V := ρ ⁻¹ᵁ (m ⁻¹ᵁ W')) (fun _ hy => h hy)
      DualNumber.eps).symm
    rw [map_add (f := _), map_mul]
    exact congrArg₂ (· + ·) h1 (congrArg₂ (· * ·) h3 h2)
  have hnil : ∀ W f, IsNilpotent (c W f - ((ρ ≫ m).app W).hom f) := by
    intro W f
    refine ⟨2, ?_⟩
    show ((ρ.app _).hom ((m.app W).hom f) + cH π _ DualNumber.eps * (ρ.app _).hom (d W f) -
      (ρ.app _).hom ((m.app W).hom f)) ^ 2 = 0
    rw [add_sub_cancel_left, mul_pow, sq (cH π _ _), hee, zero_mul]
  have hdual : ∀ x : DualNumber ℂ,
      algebraMap ℂ (DualNumber ℂ) x.fst + DualNumber.eps * algebraMap ℂ (DualNumber ℂ) x.snd = x := by
    intro x
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hfst : ∀ z : DualNumber ℂ, (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom z = z.fst := fun z => rfl
  have hq : ∀ (V : Y.Opens) (z : ℂ),
      (ρ.app V).hom (cH q V z) = cH π (ρ ⁻¹ᵁ V) (algebraMap ℂ (DualNumber ℂ) z) := by
    intro V z
    rw [app_cH, hpb.w, cH_spMap]
  have hc : ∀ W (r : R), c W (cH p W r) = cH π ((ρ ≫ m) ⁻¹ᵁ W) (xD r) := by
    intro W r
    show (ρ.app _).hom ((m.app W).hom (cH p W r)) +
      cH π _ DualNumber.eps * (ρ.app _).hom (d W (cH p W r)) = _
    rw [← cH_eq p W r, hd.base W le_top r]
    simp only [cH_eq]
    rw [app_cH, hmp, ← Category.assoc, cH_spMap, cH_spMap, hq, hq, ← map_mul, ← map_add (f := _), hfst,
      hdual]
    rfl
  refine ⟨deform (ρ ≫ m) c hres hnil, ?_, ?_⟩
  · have hb : (j ≫ deform (ρ ≫ m) c hres hnil).base = m.base := by
      show (j ≫ ρ ≫ m).base = m.base
      rw [← Category.assoc, hjρ, Category.id_comp]
    refine Scheme.Hom.ext hb ?_
    intro U
    have hle : m ⁻¹ᵁ U ≤ j ⁻¹ᵁ (ρ ⁻¹ᵁ (m ⁻¹ᵁ U)) := by
      intro x hx
      have hx' : (j ≫ ρ) x = x := by rw [hjρ]; rfl
      show (j ≫ ρ) x ∈ m ⁻¹ᵁ U
      rw [hx']
      exact hx
    apply CommRingCat.hom_ext
    ext f
    change (j.appLE (ρ ⁻¹ᵁ (m ⁻¹ᵁ U)) (m ⁻¹ᵁ U) hle).hom
      (((deform (ρ ≫ m) c hres hnil).app U).hom f) = _
    rw [deform_app]
    show (j.appLE _ _ hle).hom ((ρ.app _).hom ((m.app U).hom f) +
      cH π _ DualNumber.eps * (ρ.app _).hom (d U f)) = _
    rw [map_add (f := _), map_mul, appLE_app_of_section ρ j hjρ _ hle, appLE_cH, hjπ, cH_spMap, hfst]
    simp
  · apply ext_cH
    intro r
    rw [cH_spMap]
    have e1 := app_cH p (deform (ρ ≫ m) c hres hnil) ⊤ r
    rw [deform_app] at e1
    have e2 := res_cH (deform (ρ ≫ m) c hres hnil ≫ p)
      (U := (deform (ρ ≫ m) c hres hnil) ⁻¹ᵁ ⊤) (V := ⊤) le_top r
    rw [← e2, ← e1]
    show resG Y' _ (c ⊤ (cH p ⊤ r)) = _
    rw [hc]
    exact res_cH π _ _

end GlobalTheory.KS.DerMor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomOfDerivation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.DerMorK

section Deform
variable {Z X : Scheme.{0}} (g : Z ⟶ X) (ψ : ∀ W : X.Opens, Γ(X, W) →+* Γ(Z, g ⁻¹ᵁ W))
  (hnat : ∀ (W W' : X.Opens) (h : W' ≤ W) (f : Γ(X, W)),
    ψ W' (resG X h f) = resG Z (g.preimage_mono h) (ψ W f))

def deformPsh : Z.toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := g.base
  c :=
    { app := fun W => CommRingCat.ofHom (ψ W.unop)
      naturality := fun W W' i => by
        ext f
        exact hnat W.unop W'.unop i.unop.le f }

def deformHom (hnil : ∀ (W : X.Opens) (f : Γ(X, W)), IsNilpotent (ψ W f - (g.app W).hom f)) : Z ⟶ X :=
  ⟨⟨deformPsh g ψ hnat, fun x => ⟨fun a ha => by
    obtain ⟨W, hW, f, rfl⟩ := X.presheaf.germ_exist a
    have h1 := PresheafedSpace.stalkMap_germ_apply (deformPsh g ψ hnat) W x hW f
    have h2 := Scheme.Hom.germ_stalkMap_apply g W x hW f
    have h3 : IsNilpotent ((Z.presheaf.germ (g ⁻¹ᵁ W) x hW).hom (ψ W f - (g.app W).hom f)) :=
      (hnil W f).map _
    have h4 : IsUnit ((Z.presheaf.germ (g ⁻¹ᵁ W) x hW).hom (ψ W f)) := by
      erw [h1] at ha
      exact ha
    have h5 : IsUnit ((Z.presheaf.germ (g ⁻¹ᵁ W) x hW).hom ((g.app W).hom f)) := by
      have := h3.neg.isUnit_add_right_of_commute h4 (Commute.all _ _)
      rw [map_sub] at this
      convert this using 1
      ring
    rw [← h2] at h5
    exact isUnit_of_map_unit (g.stalkMap x).hom _ h5⟩⟩⟩

theorem deformHom_base (hnil) : (deformHom g ψ hnat hnil).base = g.base := rfl

end Deform

theorem hom_ext_appLE {Z X : Scheme.{0}} {f g : Z ⟶ X} (hb : f.base = g.base)
    (h : ∀ U e, f.appLE U (g ⁻¹ᵁ U) e = g.app U) : f = g := by
  refine Scheme.Hom.ext hb fun U => ?_
  rw [← h U (le_of_eq congr((TopologicalSpace.Opens.map $hb.symm).obj U))]
  rfl

theorem appLE_constFn {R : Type} [CommRing R] {Z X : Scheme.{0}} (f : Z ⟶ X) (p : X ⟶ Sp R)
    {U : X.Opens} {V : Z.Opens} (e : V ≤ f ⁻¹ᵁ U) (a : R) :
    (f.appLE U V e).hom (constFn p U a) = constFn (f ≫ p) V a := by
  unfold constFn
  rw [← Scheme.Hom.appLE_comp_appLE f p ⊤ U V (fun _ _ => trivial) e]
  rfl

theorem app_constFn {R : Type} [CommRing R] {Z X : Scheme.{0}} (f : Z ⟶ X) (p : X ⟶ Sp R)
    (U : X.Opens) (a : R) :
    (f.app U).hom (constFn p U a) = constFn (f ≫ p) (f ⁻¹ᵁ U) a := by
  rw [Scheme.Hom.app_eq_appLE, appLE_constFn]

theorem constFn_spMap {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}} (p : X ⟶ Sp R')
    (φ : R →+* R') (U : X.Opens) (a : R) :
    constFn (p ≫ spMap φ) U a = constFn p U (φ a) := by
  unfold constFn
  rw [← Scheme.Hom.appLE_comp_appLE p (spMap φ) ⊤ ⊤ U (fun _ _ => trivial) (fun _ _ => trivial)]
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  have h2 := congr(($h).hom a)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2 ⊢
  rw [h2]
  congr 1

def constHom {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem constFn_eq {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (a : R) :
    constFn p U a = constHom p U a := rfl

theorem res_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U)
    (a : R) : resG X h (constFn p U a) = constFn p V a := by
  have := Scheme.Hom.appLE_map p (U := ⊤) (V := U) (V' := V) (fun _ _ => trivial) (homOfLE h).op
  exact congr(($this).hom _)

theorem res_app {Z X : Scheme.{0}} (f : Z ⟶ X) {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    (f.app V).hom (resG X h a) = resG Z (f.preimage_mono h) ((f.app U).hom a) := by
  have := f.naturality (homOfLE h).op
  exact congr(($this).hom _)

theorem pbT_eq_app {Z X : Scheme.{0}} (f : Z ⟶ X) {U : X.Opens} (a : Γ(X, U)) :
    pbT f a (f ⁻¹ᵁ U) = (f.app U).hom a := by
  unfold pbT
  rw [dite_eq_left le_rfl, Scheme.Hom.appLE_eq_app]

section Main
variable {K : Type} [Field K] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp K} (π : Y' ⟶ Sp (DualNumber K)) (ρ : Y' ⟶ Y)
  {R : Type} [CommRing R] {D : R → K} {X : Scheme.{0}} {p : X ⟶ Sp R} {m : Y ⟶ X}
  {d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)}

theorem eps_sq (U : Y'.Opens) :
    constFn π U DualNumber.eps * constFn π U DualNumber.eps = 0 := by
  rw [constFn_eq, ← map_mul, DualNumber.eps_mul_eps, map_zero]

def psi (hd : LocDerK q p m D ⊤ d) (W : X.Opens) : Γ(X, W) →+* Γ(Y', (ρ ≫ m) ⁻¹ᵁ W) where
  toFun f := (ρ.app (m ⁻¹ᵁ W)).hom ((m.app W).hom f) +
    constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ W) DualNumber.eps * (ρ.app (m ⁻¹ᵁ W)).hom (d W f)
  map_one' := by
    have h := hd.mul W le_top 1 1
    simp only [_root_.mul_one, map_one, _root_.one_mul] at h
    have h0 : d W 1 = 0 := by linear_combination -h
    simp only [h0, map_one, map_zero, mul_zero, add_zero]
    rfl
  map_mul' f f' := by
    have h := eps_sq π (ρ ⁻¹ᵁ m ⁻¹ᵁ W)
    rw [hd.mul W le_top]
    simp only [map_mul, map_add (f := _)]
    change (_ : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W)) = (_ : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W)) * (_ : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W))
    linear_combination -((ρ.app (m ⁻¹ᵁ W)).hom (d W f) * (ρ.app (m ⁻¹ᵁ W)).hom (d W f')) * h
  map_zero' := by
    have h := hd.add W le_top 0 0
    simp only [add_zero] at h
    have h0 : d W 0 = 0 := by linear_combination -h
    simp only [h0, map_zero, mul_zero, add_zero]
    rfl
  map_add' f f' := by
    rw [hd.add W le_top]
    simp only [map_add (f := _)]
    change (_ : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W)) = (_ : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W)) + (_ : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W))
    ring

theorem psi_apply (hd : LocDerK q p m D ⊤ d) (W : X.Opens) (f : Γ(X, W)) :
    (psi π ρ hd W f : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W)) = (ρ.app (m ⁻¹ᵁ W)).hom ((m.app W).hom f) +
    constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ W) DualNumber.eps * (ρ.app (m ⁻¹ᵁ W)).hom (d W f) := rfl

theorem psi_nat (hd : LocDerK q p m D ⊤ d) (W W' : X.Opens) (h : W' ≤ W) (f : Γ(X, W)) :
    psi π ρ hd W' (resG X h f) = resG Y' ((ρ ≫ m).preimage_mono h) (psi π ρ hd W f) := by
  have h1 : m ⁻¹ᵁ W' ≤ m ⁻¹ᵁ W := m.preimage_mono h
  have h2 : (ρ.app (m ⁻¹ᵁ W')).hom ((m.app W').hom (resG X h f)) +
      constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ W') DualNumber.eps * (ρ.app (m ⁻¹ᵁ W')).hom (d W' (resG X h f)) =
      resG Y' (ρ.preimage_mono h1) ((ρ.app (m ⁻¹ᵁ W)).hom ((m.app W).hom f) +
      constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ W) DualNumber.eps * (ρ.app (m ⁻¹ᵁ W)).hom (d W f)) := by
    rw [hd.res W W' h le_top, rsT, dite_eq_left h1, res_app, res_app, res_app, map_add (f := _), map_mul, res_constFn]
  exact h2

theorem psi_nil (hd : LocDerK q p m D ⊤ d) (W : X.Opens) (f : Γ(X, W)) :
    IsNilpotent (psi π ρ hd W f - ((ρ ≫ m).app W).hom f) := by
  have h : IsNilpotent ((ρ.app (m ⁻¹ᵁ W)).hom ((m.app W).hom f) +
      constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ W) DualNumber.eps * (ρ.app (m ⁻¹ᵁ W)).hom (d W f) -
      (ρ.app (m ⁻¹ᵁ W)).hom ((m.app W).hom f)) := by
    refine ⟨2, ?_⟩
    have h := eps_sq π (ρ ⁻¹ᵁ m ⁻¹ᵁ W)
    linear_combination ((ρ.app (m ⁻¹ᵁ W)).hom (d W f)) ^ 2 * h
  exact h

end Main

theorem exists_hom_of_derivation : ∀ (K : Type) [Field K] (Y Y' : Scheme.{0}) (q : Y ⟶ Sp K) (π : Y' ⟶ Sp (DualNumber K)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap K (DualNumber K))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → ∀ (R : Type) [CommRing R] (xD : R →+* DualNumber K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : Y ⟶ X) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)), m ≫ p = q ≫ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ spMap xD → LocDerK q p m (fun r => (xD r).snd) ⊤ d → ∃ Φ : Y' ⟶ X, j ≫ Φ = m ∧ Φ ≫ p = π ≫ spMap xD ∧ ∀ (W : X.Opens) (f : Γ(X, W)), pbT Φ f (ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) = pbT (ρ ≫ m) f _ + constFn π _ DualNumber.eps * pbT ρ (d W f) _ := by
  intro K _ Y Y' q π ρ j hpb hjρ hjπ R _ xD X p m d hm hd
  let Φ := deformHom (ρ ≫ m) (psi π ρ hd) (psi_nat π ρ hd) (psi_nil π ρ hd)
  have hjm : j ≫ ρ ≫ m = m := by rw [← Category.assoc, hjρ, Category.id_comp]
  refine ⟨Φ, ?_, ?_, ?_⟩
  · refine hom_ext_appLE (congr(($hjm).base)) fun U e => ?_
    ext f
    have e' : m ⁻¹ᵁ U ≤ j ⁻¹ᵁ (ρ ⁻¹ᵁ m ⁻¹ᵁ U) := e
    have h1 : ((j ≫ Φ).appLE U (m ⁻¹ᵁ U) e).hom f = (j.appLE (ρ ⁻¹ᵁ m ⁻¹ᵁ U) (m ⁻¹ᵁ U) e').hom
        ((ρ.app (m ⁻¹ᵁ U)).hom ((m.app U).hom f) +
          constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ U) DualNumber.eps * (ρ.app (m ⁻¹ᵁ U)).hom (d U f)) := rfl
    have h2 : (j.appLE (ρ ⁻¹ᵁ m ⁻¹ᵁ U) (m ⁻¹ᵁ U) e').hom ((ρ.app (m ⁻¹ᵁ U)).hom ((m.app U).hom f)) =
        ((j ≫ ρ ≫ m).appLE U (m ⁻¹ᵁ U) e').hom f := rfl
    have h3 : ∀ (k : Y ⟶ X) (_ : k = m) (e''), k.appLE U (m ⁻¹ᵁ U) e'' = m.app U := by
      rintro k rfl e''
      exact Scheme.Hom.appLE_eq_app _
    rw [h1, map_add (f := _), map_mul, h2, h3 (j ≫ ρ ≫ m) hjm e', appLE_constFn, hjπ, constFn_spMap, constFn_eq]
    simp
  · apply ext_of_isAffine
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R)).inv]
    ext r
    have h0 : ∀ {Z : Scheme.{0}} (k : Z ⟶ Sp R),
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ k.appTop).hom r = constFn k ⊤ r := by
      intro Z k
      have := Scheme.Hom.appLE_eq_app k (U := ⊤)
      exact congr(($this.symm).hom _)
    rw [h0, h0, constFn_spMap]
    have h1 : constFn (Φ ≫ p) ⊤ r = (ρ.app (m ⁻¹ᵁ ⊤)).hom ((m.app ⊤).hom (constFn p ⊤ r)) +
        constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ ⊤) DualNumber.eps * (ρ.app (m ⁻¹ᵁ ⊤)).hom (d ⊤ (constFn p ⊤ r)) :=
      (app_constFn Φ p ⊤ r).symm
    rw [h1, hd.base ⊤ le_rfl, app_constFn, hm, ← Category.assoc, constFn_spMap, constFn_spMap,
      app_constFn, app_constFn, hpb.w, constFn_spMap, constFn_spMap, constFn_eq, constFn_eq, constFn_eq,
      ← map_mul, ← map_add]
    change constHom π ⊤ _ = constHom π ⊤ _
    congr 1
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  · intro W f
    have h1 := pbT_eq_app Φ f
    have h2 := pbT_eq_app (ρ ≫ m) f
    have h3 := pbT_eq_app ρ (d W f)
    refine h1.trans ?_
    rw [h3]
    erw [h2]
    rfl

end GlobalTheory.KS.DerMorK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapExtendingOfIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem Cpt.arith_and_proOpen {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {U : Scheme.{0}}
    {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t : SAB H U} {β : O →+* F} (C : Cpt c t β)
    (hβ : IsDedFrac β) (hO : Algebra.FiniteType ℤ O) :
    (∃ z : C.X ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) ∧ IsPreimmersion C.j ∧ Flat C.j ∧ IsDominant C.j ∧
      QuasiCompact C.j := by
  obtain ⟨⟨hdom, hded⟩, hchar, hfr⟩ := hβ
  let _ : Algebra O F := β.toAlgebra
  have h := GlobalTheory.genericPart_dense_proOpen O F C.X U C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  refine ⟨⟨C.s ≫ spMap (algebraMap ℤ O), ?_, ?_⟩, h.2.2.2⟩
  · have hprop : IsProper C.s := by
      obtain ⟨N, i, hi, e⟩ := C.proj
      have := isProper_str O N
      rw [← e]; infer_instance
    have : LocallyOfFiniteType (spMap (algebraMap ℤ O)) := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      exact RingHom.finiteType_algebraMap.mpr hO
    infer_instance
  · have := C.flat
    have : Flat (spMap (algebraMap ℤ O)) := by
      rw [Flat.SpecMap_iff]
      exact RingHom.flat_algebraMap_iff.mpr inferInstance
    infer_instance

theorem exists_sabMap_extending_of_iso : ((∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X U : Scheme.{0}) (j : U ⟶ X), (IsNormalScheme X ∧ ∃ z : X ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (t₀ : SAB H U) (t t' : SAB H X) (a : SABMap t₀ t j) (a' : SABMap t₀ t' j), IsProper t₀.G.hom → ∃ b : SABMap t t' (𝟙 X), a.φ ≫ b.φ = a'.φ) → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (C : Cpt c t β) (C' : Cpt c' t' β') (r : U' ⟶ U) (ν : SABMap t' t r) (f : C'.X ⟶ C.X), IsDedFrac β' → Algebra.FiniteType ℤ O' → IsProper t'.G.hom → C'.j ≫ f = r ≫ C.j → ∃ mu : SABMap C'.t C.t f, C'.m.φ ≫ mu.φ = ν.φ ≫ C.m.φ := by
  intro hS hT E _ _ _ H U F O _ _ c t β U' F' O' _ _ c' t' β' C C' r ν f hβ hO hp hj
  obtain ⟨hz, h1, h2, h3, h4⟩ := C'.arith_and_proOpen hβ hO
  obtain ⟨PP', cub, sym, adj, prim, p, -⟩ := sabPull Out.CubePf.cubePull f C.t
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.m ν
  obtain ⟨n', hn'⟩ := GlobalTheory.exists_sabMap_of_base_eq n (g := C'.j ≫ f) hj.symm
  obtain ⟨a', ha'⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ p n'
  obtain ⟨b, hb⟩ := hS hT E H C'.X U' C'.j ⟨C'.normal, hz⟩ h1 h2 h3 h4 t' C'.t _ C'.m a' hp
  obtain ⟨m, hm⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ p b
  obtain ⟨mu, hmu⟩ := GlobalTheory.exists_sabMap_of_base_eq m (Category.id_comp f)
  refine ⟨mu, ?_⟩
  exact (congrArg (C'.m.φ ≫ ·) (hmu.trans hm)).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ p.φ) hb).trans (ha'.symm.trans (hn'.trans hn))))

end GlobalTheory.Models
end

