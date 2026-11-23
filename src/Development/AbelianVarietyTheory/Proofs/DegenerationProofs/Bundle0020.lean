module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFormSec
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.FormSec
open scoped Pointwise

theorem map_form {B B' J : Type} [CommRing B] [CommRing B'] (ψ : B →+* B') (T : Finset (J →₀ ℕ))
    (c : (J →₀ ℕ) → B) (s : J → B) :
    ψ (∑ m ∈ T, c m * m.prod (fun i n => s i ^ n)) =
      ∑ m ∈ T, ψ (c m) * m.prod (fun i n => ψ (s i) ^ n) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, Finsupp.prod, map_prod, map_pow]

theorem form_scale {B J : Type} [CommRing B] (T : Finset (J →₀ ℕ)) (d : ℕ)
    (hT : ∀ m ∈ T, ∑ i ∈ m.support, m i = d) (c : (J →₀ ℕ) → B) (u : B) (s : J → B) :
    ∑ m ∈ T, c m * m.prod (fun i n => (u * s i) ^ n) =
      u ^ d * ∑ m ∈ T, c m * m.prod (fun i n => s i ^ n) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hT m hm]
  ring

section Supp
variable {A X : Type} [CommRing A] [AddCommGroup X]

theorem supp_mul {x y : AddMonoidAlgebra A X} {S S' : Set X} (hx : (x.coeff.support : Set X) ⊆ S)
    (hy : (y.coeff.support : Set X) ⊆ S') : ((x * y).coeff.support : Set X) ⊆ S + S' := by
  classical
  intro a ha
  obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.1 (AddMonoidAlgebra.support_coeff_mul_subset x y ha)
  exact Set.add_mem_add (hx hb) (hy hc)

theorem supp_one : ((1 : AddMonoidAlgebra A X).coeff.support : Set X) ⊆ 0 := by
  intro a ha
  have := AddMonoidAlgebra.support_coeff_one_subset (k := A) (G := X) ha
  simpa using this

theorem supp_pow {x : AddMonoidAlgebra A X} {S : Set X} (hx : (x.coeff.support : Set X) ⊆ S) (n : ℕ) :
    ((x ^ n).coeff.support : Set X) ⊆ n • S := by
  induction n with
  | zero => rw [pow_zero, zero_nsmul]; exact supp_one
  | succ n ih => rw [pow_succ, succ_nsmul]; exact supp_mul ih hx

theorem supp_prod {J : Type} {x : J → AddMonoidAlgebra A X} {S : Set X}
    (hx : ∀ i, ((x i).coeff.support : Set X) ⊆ S) (n : J → ℕ) (t : Finset J) :
    ((∏ i ∈ t, x i ^ n i).coeff.support : Set X) ⊆ (∑ i ∈ t, n i) • S := by
  classical
  induction t using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, zero_nsmul]; exact supp_one
  | insert j t hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, add_nsmul]
    exact supp_mul (supp_pow (hx j) _) ih

theorem supp_form {B J : Type} [CommRing B] (f : A →+* B)
    (g : Multiplicative X →* B) (hc : ∀ x y, Commute (f x) (g y))
    (hb : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f g hc)) (T : Finset (J →₀ ℕ)) (d : ℕ)
    (hT : ∀ m ∈ T, ∑ i ∈ m.support, m i = d) (c : (J →₀ ℕ) → A) (s : J → B) (S : Set X)
    (hs : ∀ i α, ((Equiv.ofBijective _ hb).symm (s i)).coeff α ≠ 0 → α ∈ S) (α : X)
    (hα : ((Equiv.ofBijective _ hb).symm (∑ m ∈ T, f (c m) * m.prod (fun i n => s i ^ n))).coeff α ≠ 0) :
    ∃ β : Fin d → X, (∀ n, β n ∈ S) ∧ α = ∑ n, β n := by
  let e := RingEquiv.ofBijective _ hb
  have h1 : ∀ x, e.symm (f x) = AddMonoidAlgebra.single 0 x := fun x => by
    rw [RingEquiv.symm_apply_eq]
    change _ = AddMonoidAlgebra.liftNCRingHom f g hc _
    simp [AddMonoidAlgebra.liftNCRingHom]
  change (e.symm.toRingHom _).coeff α ≠ 0 at hα
  rw [map_form, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply] at hα
  obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hα
  have h2 : ((e.symm.toRingHom (f (c m))).coeff.support : Set X) ⊆ 0 := by
    change ((e.symm (f (c m))).coeff.support : Set X) ⊆ 0
    rw [h1, AddMonoidAlgebra.coeff_single]
    intro a ha
    simpa using Finsupp.support_single_subset ha
  have h3 := supp_mul h2 (supp_prod (x := fun i => e.symm.toRingHom (s i)) (S := S)
    (fun i a ha => hs i a (Finsupp.mem_support_iff.1 ha)) m m.support) (Finsupp.mem_support_iff.2 hne)
  rw [zero_add, hT m hm, Set.mem_nsmul] at h3
  obtain ⟨β, hβ⟩ := h3
  exact ⟨fun n => β n, fun n => (β n).2, by rw [← hβ, List.sum_ofFn]⟩

end Supp

theorem res_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (q : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U)
    (a : R) : resG X h (constFn q U a) = constFn q V a :=
  congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map q (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

theorem valHom_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (x : Sp R ⟶ X)
    (hx : x ≫ p = 𝟙 _) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : R) :
    CrdCalc.valHom x U h (constFn p U a) = a := by
  have e : p.appLE ⊤ U (fun _ _ => trivial) ≫ x.appLE U ⊤ h = 𝟙 _ := by
    refine (Scheme.Hom.appLE_comp_appLE x p ⊤ U ⊤ (fun _ _ => trivial) h).trans ?_
    generalize_proofs h₁
    revert h₁
    rw [hx]
    intro h₁
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
    exact (Category.id_comp _).trans ((Sp R).presheaf.map_id _)
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (p.appLE ⊤ U (fun _ _ => trivial) ≫ x.appLE U ⊤ h) ≫
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom a = a
  rw [e, Category.id_comp, Iso.inv_hom_id]
  rfl

theorem deg_of_mem {k J : Type} [Field k] {d : ℕ} {Pf : MvPolynomial J k} (h : Pf.IsHomogeneous d) :
    ∀ m ∈ Pf.support, ∑ i ∈ m.support, m i = d := fun m hm => by
  have := h (MvPolynomial.mem_support_iff.1 hm)
  simpa [Finsupp.weight_apply, Finsupp.sum] using this

def formSec {k : Type} [Field k] (Φ : FibPre k) {J : Type} (F : J → (Φ.H 1).Sec) {d : ℕ}
    (Pf : MvPolynomial J k) (h : Pf.IsHomogeneous d) : (Φ.H d).Sec where
  f l := ∑ m ∈ Pf.support, constFn Φ.G.hom ((Φ.H d).U l) (Pf.coeff m) *
    m.prod (fun i n => (show Γ(Φ.G.left, (Φ.H d).U l) from (F i).f l) ^ n)
  compat l l' := by
    let V : Φ.G.left.Opens := (Φ.H d).U l ⊓ (Φ.H d).U l'
    let r : Γ(Φ.G.left, (Φ.H d).U l) →+* Γ(Φ.G.left, V) := resG _ inf_le_left
    let r' : Γ(Φ.G.left, (Φ.H d).U l') →+* Γ(Φ.G.left, V) := resG _ inf_le_right
    let u : Γ(Φ.G.left, V)ˣ := pullU Φ.D.q.left (Φ.N₀.U l ⊓ Φ.N₀.U l') (Φ.N₀.g l l')
    have hF : ∀ i, r ((F i).f l) = (u : Γ(Φ.G.left, V)) * r' ((F i).f l') := fun i => by
      have := (F i).compat l l'
      change r ((F i).f l) = ((u ^ 1 : Γ(Φ.G.left, V)ˣ) : Γ(Φ.G.left, V)) * r' ((F i).f l') at this
      exact this.trans (congrArg (fun w : Γ(Φ.G.left, V)ˣ => (w : Γ(Φ.G.left, V)) * r' ((F i).f l')) (pow_one u))
    change r _ = ((u ^ d : Γ(Φ.G.left, V)ˣ) : Γ(Φ.G.left, V)) * r' _
    rw [map_form, map_form, Units.val_pow_eq_pow_val, ← form_scale _ d (deg_of_mem h)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [res_constFn, res_constFn]
    congr 2
    funext i n
    exact congrArg (· ^ n) (hF i)

theorem exists_formSec : (∀ (k : Type) [Field k] (Φ : FibPre k) (J : Type) (F : J → (Φ.H 1).Sec) (d : ℕ) (Pf : MvPolynomial J k), Pf.IsHomogeneous d → ∃ φ : (Φ.H d).Sec, (∀ l, φ.f l = ∑ m ∈ Pf.support, constFn Φ.G.hom ((Φ.H d).U l) (Pf.coeff m) * m.prod (fun i n => (show Γ(Φ.G.left, (Φ.H d).U l) from (F i).f l) ^ n)) ∧ (∀ α ∈ Φ.supp φ, ∃ β : Fin d → Φ.E.X, (∀ n, ∃ i, β n ∈ Φ.supp (F i)) ∧ α = ∑ n, β n) ∧ ∀ (x : Φ.Pt) (v : J → k), Crd (Φ.H 1) F x.left v → (MvPolynomial.eval v Pf = 0 ↔ ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ)) := by
  intro k _ Φ J F d Pf h
  refine ⟨formSec Φ F Pf h, fun _ => rfl, ?_, ?_⟩
  · rintro α ⟨l, hl⟩
    refine supp_form _ _ _ (Φ.D.coord (Φ.ch l) _ (Φ.aff l) (Φ.le l)) Pf.support d (deg_of_mem h)
      (fun m => constFn Φ.E.B.hom _ (Pf.coeff m)) (fun i => (F i).f l) {β | ∃ i, β ∈ Φ.supp (F i)}
      (fun i β hβ => ⟨i, l, hβ⟩) α ?_
    simp only [WtLin.app_constFn _ _ _ (Over.w Φ.D.q)]
    exact hl
  · rintro x v ⟨l, c, hl, hv⟩
    have hl' : ⊤ ≤ x.left ⁻¹ᵁ (Φ.H d).U l := hl
    have hc : Crd (Φ.H d) (fun _ : Unit => formSec Φ F Pf h) x.left (fun _ => MvPolynomial.eval v Pf) := by
      refine ⟨l, c ^ d, hl', fun _ => ?_⟩
      rw [CrdCalc.valR_eq _ _ hl']
      change _ = _ * CrdCalc.valHom x.left _ hl' (∑ m ∈ Pf.support, _)
      rw [map_form, Units.val_pow_eq_pow_val, ← form_scale _ d (deg_of_mem h), MvPolynomial.eval_eq]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [valHom_constFn _ _ (Over.w x)]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hv i, CrdCalc.valR_eq _ _ hl]
      rfl
    rw [← CrdCalc.crd_isUnit_iff () hc, isUnit_iff_ne_zero, not_not]

end GlobalTheory.ZH.FormSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMonHomExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.GenericHom

theorem mul_eq_of_generic {A B P : Type*} [Group A] [Group B] (j : P → A) (f : P → B)
    (hm : ∀ x y z, j x * j y = j z → f x * f y = f z)
    (hg : ∀ s : List A, ∃ u, ∀ h ∈ s, ∃ p, j p = h * u) (a x b y : P)
    (h : j a * j x = j b * j y) : f a * f x = f b * f y := by
  obtain ⟨u, hu⟩ := hg [1, j x, j y, j a * j x]
  obtain ⟨c, hc⟩ := hu 1 (by simp)
  obtain ⟨p, hp⟩ := hu (j x) (by simp)
  obtain ⟨q, hq⟩ := hu (j y) (by simp)
  obtain ⟨r, hr⟩ := hu (j a * j x) (by simp)
  rw [_root_.one_mul] at hc
  have e1 := hm x c p (by rw [hc, hp])
  have e2 := hm y c q (by rw [hc, hq])
  have e3 := hm a p r (by rw [hp, hr, _root_.mul_assoc])
  have e4 := hm b q r (by rw [hq, hr, h, _root_.mul_assoc])
  apply mul_right_cancel (b := f c)
  rw [_root_.mul_assoc, _root_.mul_assoc, e1, e2, e3, e4]

theorem mul_four_eq_of_generic {A B P : Type*} [Group A] [Group B] (j : P → A) (f : P → B)
    (hm : ∀ x y z, j x * j y = j z → f x * f y = f z)
    (hg : ∀ s : List A, ∃ u, ∀ h ∈ s, ∃ p, j p = h * u) (a x b y c z : P)
    (h : (j a * j x) * (j b * j y) = j c * j z) : (f a * f x) * (f b * f y) = f c * f z := by
  obtain ⟨u, hu⟩ := hg [1, j y, j b * j y, j x * (j b * j y), j c * j z, j z]
  obtain ⟨p₀, h₀⟩ := hu 1 (by simp)
  obtain ⟨p₁, h₁⟩ := hu (j y) (by simp)
  obtain ⟨p₂, h₂⟩ := hu (j b * j y) (by simp)
  obtain ⟨p₃, h₃⟩ := hu (j x * (j b * j y)) (by simp)
  obtain ⟨p₄, h₄⟩ := hu (j c * j z) (by simp)
  obtain ⟨p₅, h₅⟩ := hu (j z) (by simp)
  rw [_root_.one_mul] at h₀
  have e1 := hm y p₀ p₁ (by rw [h₀, h₁])
  have e2 := hm b p₁ p₂ (by rw [h₁, h₂, _root_.mul_assoc])
  have e3 := hm x p₂ p₃ (by rw [h₂, h₃]; simp only [_root_.mul_assoc])
  have e4 := hm a p₃ p₄ (by rw [h₃, h₄, ← h]; simp only [_root_.mul_assoc])
  have e5 := hm z p₀ p₅ (by rw [h₀, h₅])
  have e6 := hm c p₅ p₄ (by rw [h₅, h₄, _root_.mul_assoc])
  apply mul_right_cancel (b := f p₀)
  simp only [_root_.mul_assoc]
  rw [e1, e2, e3, e4, e5, e6]

variable {k : Type} [Field k] [IsAlgClosed k]

theorem exists_point_mem (X : Over (Sp k)) [LocallyOfFiniteType X.hom] (W : Set X.left)
    (hW : IsLocallyClosed W) (hne : W.Nonempty) :
    ∃ x : 𝟙_ (Over (Sp k)) ⟶ X, ∀ p, x.left p ∈ W := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨c, hcW, hc⟩ := nonempty_inter_closedPoints hne hW
  exact ⟨Over.homMk (pointOfClosedPoint (K := k) X.hom c hc) (pointOfClosedPoint_comp (K := k) X.hom c hc),
    fun p => (congrArg (· ∈ W) (pointOfClosedPoint_apply (K := k) X.hom c hc p)).mpr hcW⟩

theorem hom_ext_points {X Y : Over (Sp k)}
    [Smooth X.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] (f g : X ⟶ Y)
    (h : ∀ x : 𝟙_ (Over (Sp k)) ⟶ X, x ≫ f = x ≫ g) : f = g := by
  have := isNormalScheme_of_smooth (S := Spec (.of k)) X.hom
  have : IsReduced X.left := IsNormalScheme.isReduced
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  refine Over.OverMorphism.ext (ext_of_apply_eq (K := k) Y.hom Set.univ
    isOpen_univ.isLocallyClosed dense_univ (fun x _ hx => ?_) (by rw [Over.w, Over.w]))
  obtain ⟨p, hp⟩ := exists_point_mem X {x} hx.isLocallyClosed ⟨x, rfl⟩
  have h1 : p.left ≫ f.left = p.left ≫ g.left := congrArg CommaMorphism.left (h p)
  have h2 : f.left (p.left (IsLocalRing.closedPoint k)) =
      g.left (p.left (IsLocalRing.closedPoint k)) :=
    congrArg (fun φ => φ (IsLocalRing.closedPoint k)) h1
  have h3 : p.left (IsLocalRing.closedPoint k) = x := hp _
  exact (congrArg f.left h3).symm.trans (h2.trans (congrArg g.left h3))


omit [IsAlgClosed k] in
theorem exists_lift {U H Z : Over (Sp k)} (j : U ⟶ H) [IsOpenImmersion j.left] (x : Z ⟶ H)
    (hx : ∀ p, x.left p ∈ Set.range j.left) : ∃ y : Z ⟶ U, y ≫ j = x := by
  have hr : Set.range x.left ⊆ Set.range j.left := by rintro _ ⟨p, rfl⟩; exact hx p
  refine ⟨Over.homMk (IsOpenImmersion.lift j.left x.left hr) ?_, Over.OverMorphism.ext
    (IsOpenImmersion.lift_fac j.left x.left hr)⟩
  rw [← Over.w j, IsOpenImmersion.lift_fac_assoc, Over.w]

theorem exists_generic {U H : Over (Sp k)} [LocallyOfFiniteType H.hom] [IrreducibleSpace H.left]
    (j : U ⟶ H) [IsOpenImmersion j.left] [Nonempty U.left] (s : List (H ≅ H)) :
    ∃ u : 𝟙_ (Over (Sp k)) ⟶ H, ∀ φ ∈ s, ∃ p, p ≫ j = u ≫ φ.hom := by
  have key : ∃ W : Set H.left, IsOpen W ∧ W.Nonempty ∧
      ∀ φ ∈ s, ∀ w ∈ W, φ.hom.left w ∈ Set.range j.left := by
    induction s with
    | nil => exact ⟨Set.univ, isOpen_univ, Set.univ_nonempty, by simp⟩
    | cons φ s ih =>
      obtain ⟨W, h1, h2, h3⟩ := ih
      have ho : IsOpen (φ.hom.left ⁻¹' Set.range j.left) :=
        (IsOpenImmersion.isOpen_range j.left).preimage φ.hom.left.continuous
      have hn : (φ.hom.left ⁻¹' Set.range j.left).Nonempty := by
        obtain ⟨v⟩ := ‹Nonempty U.left›
        refine ⟨φ.inv.left (j.left v), v, ?_⟩
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, φ.inv_hom_id]
        rfl
      refine ⟨W ∩ φ.hom.left ⁻¹' Set.range j.left, h1.inter ho,
        nonempty_preirreducible_inter h1 ho h2 hn, ?_⟩
      intro ψ hψ w hw
      rcases List.mem_cons.1 hψ with rfl | hψ
      · exact hw.2
      · exact h3 ψ hψ w hw.1
  obtain ⟨W, h1, h2, h3⟩ := key
  obtain ⟨u, hu⟩ := exists_point_mem H W h1.isLocallyClosed h2
  exact ⟨u, fun φ hφ => exists_lift j _ fun p => h3 φ hφ _ (hu p)⟩


omit [IsAlgClosed k] in
theorem point_comp_mul {X G : Over (Sp k)} [GrpObj G] (x : 𝟙_ (Over (Sp k)) ⟶ X)
    (a : 𝟙_ (Over (Sp k)) ⟶ G) (g : X ⟶ G) : x ≫ ((toUnit X ≫ a) * g) = a * (x ≫ g) := by
  rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (x ≫ toUnit _) (𝟙 _), Category.id_comp]

theorem exists_monHom_extension : ∀ (k : Type) [Field k] [IsAlgClosed k] (H G U : Over (Sp k)) [GrpObj H] [GrpObj G], SmConn H → SmConn G → ∀ (j : U ⟶ H) (f : U ⟶ G), IsOpenImmersion j.left → Nonempty U.left → (∀ x y z : (𝟙_ (Over (Sp k)) ⟶ U), (x ≫ j) * (y ≫ j) = z ≫ j → (x ≫ f) * (y ≫ f) = z ≫ f) → ∃ F : H ⟶ G, IsMonHom F ∧ j ≫ F = f := by
  intro k _ _ H G U _ _ ⟨hc, hs, _, _, hgc⟩ ⟨_, _, _, _, _⟩ j f hj hU hm
  have : IsIntegral H.left := isIntegral_of_smooth_of_geometricallyConnected H.hom
  have htr : ∀ (a x : 𝟙_ (Over (Sp k)) ⟶ H), x ≫ (transl a).hom = a * x := fun a x =>
    (point_comp_mul x a (𝟙 H)).trans (by rw [Category.comp_id])
  have hg : ∀ s : List (𝟙_ (Over (Sp k)) ⟶ H), ∃ u, ∀ h ∈ s,
      ∃ p : 𝟙_ (Over (Sp k)) ⟶ U, p ≫ j = h * u := by
    intro s
    obtain ⟨u, hu⟩ := exists_generic j (s.map transl)
    exact ⟨u, fun h hh => htr h u ▸ hu _ (List.mem_map_of_mem hh)⟩
  have hdec : ∀ h : 𝟙_ (Over (Sp k)) ⟶ H, ∃ a x : 𝟙_ (Over (Sp k)) ⟶ U,
      (a ≫ j) * (x ≫ j) = h := by
    intro h
    obtain ⟨u, hu⟩ := exists_generic j [Iso.refl H, asIso (ι[H]) ≪≫ transl h]
    obtain ⟨x, hx⟩ := hu (Iso.refl H) (by simp)
    obtain ⟨a, ha⟩ := hu (asIso (ι[H]) ≪≫ transl h) (by simp)
    refine ⟨a, x, ?_⟩
    rw [ha, hx, Iso.trans_hom, ← Category.assoc, htr, asIso_hom, Iso.refl_hom, Category.comp_id,
      ← Hom.inv_def, inv_mul_cancel_right]
  let J : (𝟙_ (Over (Sp k)) ⟶ U) → (U ⟶ H) := fun a => j ≫ (transl (a ≫ j)).hom
  let φ : (𝟙_ (Over (Sp k)) ⟶ U) → (U ⟶ G) := fun a => (toUnit U ≫ a ≫ f) * f
  have hJ : ∀ a x : 𝟙_ (Over (Sp k)) ⟶ U, x ≫ J a = (a ≫ j) * (x ≫ j) := fun a x => by
    rw [← htr, Category.assoc]
  have hφ : ∀ a x : 𝟙_ (Over (Sp k)) ⟶ U, x ≫ φ a = (a ≫ f) * (x ≫ f) := fun a x =>
    point_comp_mul x _ _
  have hJo : ∀ a, IsOpenImmersion (J a).left := fun a => by
    have : IsIso (transl (a ≫ j)).hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map (transl (a ≫ j)).hom))
    exact inferInstanceAs (IsOpenImmersion (j.left ≫ (transl (a ≫ j)).hom.left))
  have hcov : ∀ y : H.left, ∃ a, y ∈ Set.range (J a).left := by
    by_contra hn
    push Not at hn
    obtain ⟨y, hy⟩ := hn
    have hcl : IsClosed (⋃ a, Set.range (J a).left)ᶜ :=
      (isOpen_iUnion fun a => IsOpenImmersion.isOpen_range (J a).left).isClosed_compl
    obtain ⟨h, hh⟩ := exists_point_mem H _ hcl.isLocallyClosed ⟨y, by simpa using hy⟩
    obtain ⟨a, x, e⟩ := hdec h
    rw [← hJ] at e
    subst e
    exact hh (IsLocalRing.closedPoint k) (Set.mem_iUnion.2 ⟨a, x.left (IsLocalRing.closedPoint k), rfl⟩)
  have hsU : Smooth U.hom := by rw [← Over.w j]; infer_instance
  let 𝒰 : H.left.OpenCover := Scheme.Cover.mkOfCovers (𝟙_ (Over (Sp k)) ⟶ U) (fun _ => U.left)
    (fun a => (J a).left) (fun y => hcov y) hJo
  have hcomp : ∀ a b, pullback.fst (J a).left (J b).left ≫ (φ a).left =
      pullback.snd (J a).left (J b).left ≫ (φ b).left := by
    intro a b
    let Z : Over (Sp k) := Over.mk (pullback.fst (J a).left (J b).left ≫ U.hom)
    have : Smooth Z.hom := inferInstanceAs (Smooth (pullback.fst (J a).left (J b).left ≫ U.hom))
    let p₁ : Z ⟶ U := Over.homMk (pullback.fst (J a).left (J b).left) rfl
    let p₂ : Z ⟶ U := Over.homMk (pullback.snd (J a).left (J b).left) (by
      show _ = pullback.fst (J a).left (J b).left ≫ U.hom
      have e := congrArg (· ≫ H.hom) (pullback.condition (f := (J a).left) (g := (J b).left))
      simp only [Category.assoc, Over.w] at e
      exact e.symm)
    have hp : p₁ ≫ J a = p₂ ≫ J b := Over.OverMorphism.ext pullback.condition
    have : p₁ ≫ φ a = p₂ ≫ φ b := hom_ext_points _ _ fun z => by
      rw [← Category.assoc, ← Category.assoc, hφ, hφ]
      refine mul_eq_of_generic (· ≫ j) (· ≫ f) hm hg _ _ _ _ ?_
      show (a ≫ j) * ((z ≫ p₁) ≫ j) = (b ≫ j) * ((z ≫ p₂) ≫ j)
      rw [← hJ, ← hJ, Category.assoc, Category.assoc, hp]
    exact congrArg CommaMorphism.left this
  let F₀ : H.left ⟶ G.left := 𝒰.glueMorphisms (fun a => (φ a).left) hcomp
  have hF₀ : ∀ a, (J a).left ≫ F₀ = (φ a).left := fun a =>
    𝒰.ι_glueMorphisms (fun a => (φ a).left) hcomp a
  let F : H ⟶ G := Over.homMk F₀ (𝒰.hom_ext _ _ fun a => by
    show (J a).left ≫ F₀ ≫ G.hom = (J a).left ≫ H.hom
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ G.hom) (hF₀ a)).trans
      ((Over.w (φ a)).trans (Over.w (J a)).symm)))
  have hF : ∀ a x : 𝟙_ (Over (Sp k)) ⟶ U, ((a ≫ j) * (x ≫ j)) ≫ F = (a ≫ f) * (x ≫ f) := by
    intro a x
    have : J a ≫ F = φ a := Over.OverMorphism.ext (hF₀ a)
    rw [← hJ, Category.assoc, this, hφ]
  have hmul : ∀ h h' : 𝟙_ (Over (Sp k)) ⟶ H, (h * h') ≫ F = (h ≫ F) * (h' ≫ F) := by
    intro h h'
    obtain ⟨c, z, e⟩ := hdec (h * h')
    obtain ⟨a, x, rfl⟩ := hdec h
    obtain ⟨b, y, rfl⟩ := hdec h'
    rw [← e, hF, hF, hF]
    exact (mul_four_eq_of_generic (· ≫ j) (· ≫ f) hm hg _ _ _ _ _ _ e.symm).symm
  refine ⟨F, ⟨?_, ?_⟩, hom_ext_points _ _ fun w => ?_⟩
  · have := hmul 1 1
    rw [_root_.one_mul] at this
    have h1 : (1 : 𝟙_ (Over (Sp k)) ⟶ H) ≫ F = 1 := left_eq_mul.1 this
    simpa [Hom.one_def] using h1
  · have : Smooth (H ⊗ H).hom := inferInstanceAs (Smooth (pullback.fst H.hom H.hom ≫ H.hom))
    refine hom_ext_points _ _ fun z => ?_
    have := hmul (z ≫ fst H H) (z ≫ snd H H)
    rw [Hom.mul_def, Hom.mul_def, lift_comp_fst_snd] at this
    rw [← Category.assoc, this, ← Category.assoc]
    congr 1
    ext <;> simp
  · obtain ⟨a, x, e⟩ := hdec (w ≫ j)
    rw [← Category.assoc, ← e, hF]
    exact hm _ _ _ e

end GlobalTheory.GenericHom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothFreeAway
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem free_localizedModule_mul {C : Type} [CommRing C] (M : Type) [AddCommGroup M] [Module C M]
    (r g : C) (h : Module.Free (Localization.Away r) (LocalizedModule (Submonoid.powers r) M)) :
    Module.Free (Localization.Away (r * g)) (LocalizedModule (Submonoid.powers (r * g)) M) := by
  let _ : Algebra (Localization.Away r) (Localization.Away (r * g)) :=
    (IsLocalization.Away.awayToAwayRight (S := Localization.Away r) r g).toAlgebra
  have _ : IsScalarTower C (Localization.Away r) (Localization.Away (r * g)) :=
    IsScalarTower.of_algebraMap_eq fun c =>
      (IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away r) r g c).symm
  let _ : Module (Localization.Away r) (LocalizedModule (Submonoid.powers (r * g)) M) :=
    Module.compHom _ (algebraMap (Localization.Away r) (Localization.Away (r * g)))
  have _ : IsScalarTower (Localization.Away r) (Localization.Away (r * g))
      (LocalizedModule (Submonoid.powers (r * g)) M) :=
    ⟨fun a b x => by
      show (a • b) • x = algebraMap _ (Localization.Away (r * g)) a • b • x
      rw [Algebra.smul_def, mul_smul]⟩
  have _ : IsScalarTower C (Localization.Away r) (LocalizedModule (Submonoid.powers (r * g)) M) :=
    ⟨fun c a x => by
      show algebraMap _ (Localization.Away (r * g)) (c • a) • x =
        c • algebraMap _ (Localization.Away (r * g)) a • x
      rw [Algebra.smul_def, map_mul, mul_smul,
        ← IsScalarTower.algebraMap_apply C (Localization.Away r) (Localization.Away (r * g)),
        algebraMap_smul]⟩
  have hr := LocalizedModule.isBaseChange (Submonoid.powers r) M
  have hrg := LocalizedModule.isBaseChange (Submonoid.powers (r * g)) M
  rw [← hr.lift_comp (LocalizedModule.mkLinearMap (Submonoid.powers (r * g)) M)] at hrg
  exact Module.Free.of_equiv (hr.of_comp hrg).equiv

theorem exists_smooth_free_away : ∀ (k C : Type) [Field k] [PerfectField k] [CommRing C] [Nontrivial C] [IsReduced C] [Algebra k C] [Algebra.FiniteType k C] (M : Type) [AddCommGroup M] [Module C M] [Module.Finite C M], ∃ f : C, f ≠ 0 ∧ Algebra.Smooth k (Localization.Away f) ∧ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) := by
  intro k C _ _ _ _ _ _ _ M _ _ _
  have _ : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing k C
  have _ : Algebra.FinitePresentation k C := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have _ : Module.FinitePresentation C M := Module.finitePresentation_of_finite C M
  obtain ⟨m, hm⟩ := Ideal.exists_maximal C
  have := hm.isPrime
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal C)) (J := m) bot_le
  have _ : p.IsPrime := hp.1.1
  have _ : Ring.KrullDimLE 0 (Localization.AtPrime p) := Ring.KrullDimLE.of_isLocalization p hp _
  let _ : Field (Localization.AtPrime p) := (Ring.KrullDimLE.isField_of_isReduced).toField
  have _ : Algebra.IsSmoothAt k p := Algebra.FormallySmooth.of_perfectField
  have _ : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
    Module.Free.of_divisionRing _ _
  obtain ⟨f₁, hf₁p, hf₁⟩ := Algebra.IsSmoothAt.exists_notMem_smooth k p
  obtain ⟨r, hrp, hr, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M) (Localization.AtPrime p)
  refine ⟨r * f₁, ?_, ?_, free_localizedModule_mul M r f₁ hr⟩
  · intro h0
    have : r * f₁ ∈ p := by rw [h0]; exact p.zero_mem
    exact (Ideal.IsPrime.mem_or_mem ‹_› this).elim hrp hf₁p
  · rw [← Algebra.basicOpen_subset_smoothLocus_iff_smooth] at hf₁ ⊢
    exact fun x hx => hf₁ (PrimeSpectrum.basicOpen_mul_le_right r f₁ hx)

end GlobalTheory.SS
end

