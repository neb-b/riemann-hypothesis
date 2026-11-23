module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
public import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
public import Development.EtaleCohomology.EtaleSheaves.Bundle0003
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0011
public import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsUnitEqMultiplicativeGroupSection
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace UpperTheory
open Polynomial

private def evalX {A : Type} [CommRing A] (a : A) : ℤ[X] →+* A := Polynomial.eval₂RingHom (Int.castRingHom A) a

private lemma evalX_X {A : Type} [CommRing A] (a : A) : evalX a X = a := by simp [evalX]

private lemma evalX_comp {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    f.comp (evalX a) = evalX (f a) := by
  apply Polynomial.ringHom_ext'
  · exact RingHom.ext_int _ _
  · simp [evalX]

private abbrev TT : Scheme.{0} := Spec (CommRingCat.of ℤ[X])

private def phi {V : Scheme.{0}} (a : Γ(V, ⊤)) : V ⟶ TT :=
  V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (evalX a))

private def psi {V : Scheme.{0}} (f : V ⟶ TT) : Γ(V, ⊤) :=
  f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv.hom X)

private lemma phi_nat {V W : Scheme.{0}} (k : W ⟶ V) (a : Γ(V, ⊤)) :
    k ≫ phi a = phi (k.appTop.hom a) := by
  unfold phi
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  congr 2
  ext1
  exact evalX_comp k.appTop.hom a

private lemma psi_nat {V W : Scheme.{0}} (k : W ⟶ V) (f : V ⟶ TT) :
    psi (k ≫ f) = k.appTop.hom (psi f) := by
  unfold psi
  rw [Scheme.Hom.comp_appTop]
  rfl

private lemma psi_phi {V : Scheme.{0}} (a : Γ(V, ⊤)) : psi (phi a) = a := by
  unfold phi
  rw [psi_nat]
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (evalX a))
  have h2 := congrArg (fun m => m.hom X) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  unfold psi
  rw [← h2, evalX_X, Scheme.toSpecΓ_appTop]
  exact ConcreteCategory.congr_hom (Iso.inv_hom_id (Scheme.ΓSpecIso Γ(V, ⊤))) a

private lemma yo_sheaf : Presieve.IsSheaf Scheme.etaleTopology (yoneda.obj TT) :=
  Presieve.isSheaf_of_le _ Scheme.etaleTopology_le_proetaleTopology
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

private lemma glueG {U : Scheme.{0}} (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U)
    (s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Γ(V, ⊤))
    (hs : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g),
      k.appTop.hom (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) :
    ∃ a : Γ(U, ⊤), ∀ V g hg, g.appTop.hom a = s V g hg := by
  let x : Presieve.FamilyOfElements (yoneda.obj TT) S.arrows := fun V g hg => phi (s V g hg)
  have hx : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro V W g k hg
    change phi (s W (k ≫ g) _) = k ≫ phi (s V g hg)
    rw [phi_nat, hs]
  obtain ⟨t, ht, -⟩ := yo_sheaf S hS x hx
  refine ⟨psi t, fun V g hg => ?_⟩
  rw [← psi_nat]
  have h1 : g ≫ t = phi (s V g hg) := ht g hg
  rw [h1, psi_phi]

private lemma sepG {U : Scheme.{0}} (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U) (a b : Γ(U, ⊤))
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → g.appTop.hom a = g.appTop.hom b) : a = b := by
  let x : Presieve.FamilyOfElements (yoneda.obj TT) S.arrows := fun V g _ => phi (g.appTop.hom a)
  have h1 : x.IsAmalgamation (phi a) := fun V g hg => phi_nat g a
  have h2 : x.IsAmalgamation (phi b) := fun V g hg => by
    refine (phi_nat g b).trans ?_
    change phi _ = phi _
    rw [h V g hg]
  have h3 : phi a = phi b := (yo_sheaf S hS).isSeparatedFor x _ _ h1 h2
  rw [← psi_phi a, h3, psi_phi]

private lemma glueU {U : Scheme.{0}} (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U)
    (v : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → (Γ(V, ⊤))ˣ)
    (hv : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g),
      Units.map k.appTop.hom.toMonoidHom (v V g hg) = v W (k ≫ g) (S.downward_closed hg k)) :
    ∃ u : (Γ(U, ⊤))ˣ, ∀ V g hg, Units.map g.appTop.hom.toMonoidHom u = v V g hg := by
  obtain ⟨a, ha⟩ := glueG S hS (fun V g hg => (v V g hg : Γ(V, ⊤))) (fun V W g k hg => by
    have := congrArg Units.val (hv V W g k hg)
    simpa using this)
  obtain ⟨b, hb⟩ := glueG S hS (fun V g hg => ((v V g hg)⁻¹ : (Γ(V, ⊤))ˣ)) (fun V W g k hg => by
    have := congrArg (fun w => ((w⁻¹ : (Γ(W, ⊤))ˣ) : Γ(W, ⊤))) (hv V W g k hg)
    simpa using this)
  have hab : a * b = 1 := sepG S hS _ _ fun V g hg => by
    rw [map_mul, ha V g hg, hb V g hg, map_one, Units.mul_inv]
  refine ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, fun V g hg => Units.ext ?_⟩
  simpa using ha V g hg

private lemma sepU {U : Scheme.{0}} (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U) (u v : (Γ(U, ⊤))ˣ)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g →
      Units.map g.appTop.hom.toMonoidHom u = Units.map g.appTop.hom.toMonoidHom v) : u = v :=
  Units.ext (sepG S hS _ _ fun V g hg => by
    have := congrArg Units.val (h V g hg)
    simpa using this)

private lemma res_unitSec {V U : Scheme.{0}} (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Sec.res g (unitSec u) = unitSec (Units.map g.appTop.hom.toMonoidHom u) := by
  have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).naturality g.op
  exact (congrArg (fun m => m.hom (ULift.up (Additive.ofMul u) : ULift (Additive (Γ(U, ⊤))ˣ))) h).symm

private lemma unitSec_mul {U : Scheme.{0}} (u v : (Γ(U, ⊤))ˣ) :
    unitSec (u * v) = unitSec u + unitSec v :=
  map_add ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom
    (ULift.up (Additive.ofMul u) : ULift (Additive (Γ(U, ⊤))ˣ)) (ULift.up (Additive.ofMul v))

private lemma unitSec_inj {U : Scheme.{0}} (u v : (Γ(U, ⊤))ˣ) (h : unitSec u = unitSec v) : u = v := by
  have h0 : unitSec (u * v⁻¹) = 0 := by
    have h1 := unitSec_mul (u * v⁻¹) v
    rw [inv_mul_cancel_right, h] at h1
    exact (right_eq_add.mp h1)
  obtain ⟨S, hS, hl⟩ := (GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift ℤ (Scheme.Γ ⋙ unitsF)).2.1 U
    (ULift.up (Additive.ofMul (u * v⁻¹)) : ULift (Additive (Γ(U, ⊤))ˣ)) h0
  have h1 : u * v⁻¹ = 1 := sepU S hS _ _ fun V g hg => by
    have h2 := hl V g hg
    have h3 : Additive.ofMul (Units.map g.appTop.hom.toMonoidHom (u * v⁻¹)) = 0 :=
      congrArg ULift.down h2
    rw [map_one]
    exact h3
  exact mul_inv_eq_one.mp h1

end UpperTheory

open UpperTheory in
theorem UpperTheory.exists_unit_eq_multiplicativeGroup_section :
    ∀ (X : Scheme.{0}) (b : Sec Gm X), ∃ u : (Γ(X, ⊤))ˣ, unitSec u = b := by
  intro X b
  obtain ⟨S, hS, h⟩ := (GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift ℤ (Scheme.Γ ⋙ unitsF)).1 X b
  have h' : ∀ (V : Scheme.{0}) (g : V ⟶ X), S.arrows g →
      ∃ v : (Γ(V, ⊤))ˣ, unitSec v = Sec.res g b := by
    intro V g hg
    obtain ⟨x, hx⟩ := h V g hg
    exact ⟨x.down.toMul, hx⟩
  choose v hv using h'
  obtain ⟨u, hu⟩ := glueU S hS v (fun V W g k hg => by
    apply unitSec_inj
    rw [← res_unitSec, hv, hv]
    change (Gm.obj.map k.op).hom ((Gm.obj.map g.op).hom b) = (Gm.obj.map (k ≫ g).op).hom b
    rw [op_comp, Functor.map_comp]
    rfl)
  refine ⟨u, (_root_.GlobalTheory.EtC.sec_ext_glue ℤ Gm X).1 _ _ ⟨S, hS, fun V g hg => ?_⟩⟩
  change Sec.res g (unitSec u) = Sec.res g b
  rw [res_unitSec, hu V g hg, hv]

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoOfBijectiveOnSimplices
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

theorem UpperTheory.isIso_of_bijective_on_simplices :
    ∀ {S S' : Spc} (f : S ⟶ S'), (∀ (k : ℕ) (T : Scheme.{0}), Function.Bijective (fun x : Sx S k T => x.map f)) → IsIso f := by
  intro S S' f h
  haveI : ∀ n : SimplexCategoryᵒᵖ, IsIso (f.app n) := by
    intro n
    haveI : ∀ T : Schemeᵒᵖ, IsIso ((f.app n).app T) := by
      intro T
      obtain ⟨⟨k⟩⟩ := n
      obtain ⟨T⟩ := T
      rw [isIso_iff_bijective]
      exact h k T
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IsPullbackOfUniqueSimplicesPullback
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

theorem UpperTheory.isPullback_of_unique_simplices_pullback :
    ∀ {P A B C : Spc} (t : P ⟶ A) (l : P ⟶ B) (r : A ⟶ C) (u : B ⟶ C), t ≫ r = l ≫ u →
        (∀ (k : ℕ) (T : Scheme.{0}) (x : Sx A k T) (y : Sx B k T), x.map r = y.map u → ∃! z : Sx P k T, z.map t = x ∧ z.map l = y) →
        IsPullback t l r u := by
  intro P A B C t l r u hw h
  refine IsPullback.of_forall_isPullback_app (fun n => ?_)
  refine IsPullback.of_forall_isPullback_app (fun T => ?_)
  obtain ⟨⟨k⟩⟩ := n
  obtain ⟨T⟩ := T
  have hw' : ∀ x : Sx P k T, Sx.map r (Sx.map t x) = Sx.map u (Sx.map l x) := by
    intro x
    have := congrArg (fun f : P ⟶ C => (f.app (op ⟨k⟩)).app (op T) x) hw
    simpa [Sx.map] using this
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext x
    exact hw' x
  · rintro x y ⟨h1, h2⟩
    obtain ⟨z, -, hz⟩ := h k T (Sx.map t (x : Sx P k T)) (Sx.map l (x : Sx P k T)) (hw' x)
    have hx := hz x ⟨rfl, rfl⟩
    have hy := hz y ⟨h1.symm, h2.symm⟩
    exact hx.trans hy.symm
  · intro a b hab
    obtain ⟨z, ⟨h1, h2⟩, -⟩ := h k T a b hab
    exact ⟨z, h1, h2⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.LeafProdLeafLocOfLeafLevel
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut

private theorem conn_iso {R : Type} [CommRing R] (F : Shv R) (c : ℤ) {E E' : Spc} (f : E ⟶ E') [IsIso f] :
    Conn R F c f := by
  have hb : ∀ n, Function.Bijective (pull R f F n) := fun n =>
    Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n,
      fun x => by rw [← pull_comp, IsIso.inv_hom_id, pull_id],
      fun x => by rw [← pull_comp, IsIso.hom_inv_id, pull_id]⟩
  exact fun n => ⟨fun _ => hb n, fun _ => (hb n).1⟩

private theorem conn_congr {R : Type} [CommRing R] {F : Shv R} {c : ℤ} {X : Scheme.{0}} {U U' : X.Opens} (e : U = U')
    (h : Conn R F c (sch.map U.ι)) : Conn R F c (sch.map U'.ι) := e ▸ h

private theorem conn_top {R : Type} [CommRing R] (F : Shv R) (c : ℤ) {X : Scheme.{0}} {U : X.Opens} (e : U = ⊤) :
    Conn R F c (sch.map U.ι) := by
  subst e
  haveI : IsIso (⊤ : X.Opens).ι := by
    first
      | infer_instance
      | (rw [← Scheme.topIso_hom]; infer_instance)
      | exact isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
  exact conn_iso F c _

private theorem exists_good {R : Type} [CommRing R] {F : Shv R} {c : ℤ} {X : Scheme.{0}} {U : X.Opens}
    (H : ∀ x : X, x ∉ U → ∀ W : X.Opens, x ∈ W → ∃ (Y : Scheme.{0}) (j : Y ⟶ X) (_ : IsOpenImmersion j),
      x ∈ Set.range j ∧ Set.range j ⊆ (W : Set X) ∧ Conn R F c (sch.map (j ⁻¹ᵁ U).ι))
    {Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j] (y : Y) :
    ∃ (O : Scheme.{0}) (o : O ⟶ Y) (_ : IsOpenImmersion o), y ∈ Set.range o ∧
      Conn R F c (sch.map ((o ≫ j) ⁻¹ᵁ U).ι) := by
  by_cases hy : j y ∈ U
  · refine ⟨_, (j ⁻¹ᵁ U).ι, inferInstance, ?_, conn_top F c ?_⟩
    · rw [Scheme.Opens.range_ι]
      exact hy
    · rw [Scheme.Hom.comp_preimage]
      exact Scheme.Opens.ι_preimage_self _
  · obtain ⟨Y', j', hj', hx, hsub, hC⟩ := H (j y) hy j.opensRange ⟨y, rfl⟩
    have hle : Set.range j' ⊆ Set.range j := hsub
    have hfac : IsOpenImmersion.lift j j' hle ≫ j = j' := IsOpenImmersion.lift_fac j j' hle
    haveI : IsOpenImmersion (IsOpenImmersion.lift j j' hle ≫ j) := by rw [hfac]; exact hj'
    refine ⟨Y', IsOpenImmersion.lift j j' hle, IsOpenImmersion.of_comp _ j, ?_, ?_⟩
    · obtain ⟨z, hz⟩ := hx
      refine ⟨z, j.isOpenEmbedding.injective ?_⟩
      rw [← hz, ← Scheme.Hom.comp_apply, hfac]
    · rw [hfac]
      exact hC

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.MapZeroS
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

noncomputable section

namespace UpperTheory.Kun

variable {R : Type} [CommRing R]

abbrev sh (Q : Cx R) : Cx R := (CategoryTheory.shiftFunctor (Cx R) (-1 : ℤ)).obj Q

abbrev LL (I Q : Cx R) : Cx R := I ⊞ sh Q

def c₁ {I Q : Cx R} {T : Scheme.{0}} {s : ℤ} : Sec ((LL I Q).X s) T →+ Sec (I.X s) T :=
  ((((biprod.fst : LL I Q ⟶ I).f s).hom.app (op T)).hom).toAddMonoidHom

def c₂ {I Q : Cx R} {T : Scheme.{0}} {s : ℤ} : Sec ((LL I Q).X s) T →+ Sec (Q.X (s + -1)) T :=
  ((((biprod.snd : LL I Q ⟶ sh Q).f s).hom.app (op T)).hom).toAddMonoidHom

def cc {I Q : Cx R} {T : Scheme.{0}} {s : ℤ} (a : Sec (I.X s) T) (b : Sec (Q.X (s + -1)) T) : Sec ((LL I Q).X s) T :=
  Sec.map ((biprod.inl : I ⟶ LL I Q).f s) a + Sec.map ((biprod.inr : sh Q ⟶ LL I Q).f s) (show Sec ((sh Q).X s) T from b)

def psi (W : Scheme.{0}) {I Q P : Cx R} (μ : Pair Q P I) (z : Sec (P.X 1) W) (T : Scheme.{0}) (s : ℤ) :
    Sec ((LL I Q).X s) T →+ Sec (I.X s) (W ⨯ T) :=
  AddMonoidHom.mk' (fun x => Sec.res (prod.snd : W ⨯ T ⟶ T) (c₁ x) +
      s.negOnePow • μ.mul (W ⨯ T) (s + -1) 1 s (by omega) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ x)) (Sec.res (prod.fst : W ⨯ T ⟶ W) z))
    (fun x y => by
      simp only [map_add (f := _), LinearMap.add_apply, smul_add]
      abel)

def inL {K I Q : Cx R} {m n : ℤ} (h : m + 1 = n) (α₁ : Cocycle K I n) (α₂ : Cocycle K Q m) : Cocycle K (LL I Q) n :=
  zcomp α₁ (Cocycle.ofHom (biprod.inl : I ⟶ LL I Q)) (add_zero n) +
    ((n.negOnePow : ℤˣ) : ℤ) • zcomp (α₂.rightShift (-1) n (by omega)) (Cocycle.ofHom (biprod.inr : sh Q ⟶ LL I Q)) (add_zero n)

def sg {X : Scheme.{0}} {I : Cx R} {n : ℤ} (α : Cocycle ((chains R).obj (sch.obj X)) I n) : Sec (I.X n) X :=
  ev α.1 0 n (by simp) X (𝟙 X)

end UpperTheory.Kun

namespace UpperTheory.Kun
variable {R : Type} [CommRing R]

theorem res_id {F : Shv R} {X : Scheme.{0}} (b : Sec F X) : Sec.res (𝟙 X) b = b := by
  change (F.obj.map (𝟙 (op X))).hom b = b
  rw [F.obj.map_id]
  rfl

theorem res_res {F : Shv R} {X Y Z : Scheme.{0}} (f : Y ⟶ X) (g : Z ⟶ Y) (b : Sec F X) :
    Sec.res g (Sec.res f b) = Sec.res (g ≫ f) b := by
  change _ = (F.obj.map (f.op ≫ g.op)).hom b
  rw [F.obj.map_comp]
  rfl

theorem map_map {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map ψ (Sec.map φ x) = Sec.map (φ ≫ ψ) x := rfl

theorem map_idS {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := rfl

theorem map_zeroS {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := rfl

theorem map_addS {F G : Shv R} (φ ψ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) : Sec.map (φ + ψ) x = Sec.map φ x + Sec.map ψ x := rfl

theorem res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (ConcreteCategory.congr_hom (φ.hom.naturality g.op) x).symm

theorem c₁_cc {I Q : Cx R} {T : Scheme.{0}} {s : ℤ} (a : Sec (I.X s) T) (b : Sec (Q.X (s + -1)) T) : c₁ (cc (I := I) (Q := Q) a b) = a := by
  have h1 : ((biprod.inl : I ⟶ LL I Q).f s) ≫ ((biprod.fst : LL I Q ⟶ I).f s) = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, biprod.inl_fst, HomologicalComplex.id_f]
  have h2 : ((biprod.inr : sh Q ⟶ LL I Q).f s) ≫ ((biprod.fst : LL I Q ⟶ I).f s) = 0 := by
    rw [← HomologicalComplex.comp_f, biprod.inr_fst, HomologicalComplex.zero_f]
  unfold cc
  rw [map_add (f := _)]
  change Sec.map _ (Sec.map _ a) + Sec.map _ (Sec.map _ _) = a
  rw [map_map, map_map, h1, h2, map_idS, map_zeroS, add_zero]

theorem c₂_cc {I Q : Cx R} {T : Scheme.{0}} {s : ℤ} (a : Sec (I.X s) T) (b : Sec (Q.X (s + -1)) T) : c₂ (cc (I := I) (Q := Q) a b) = b := by
  have h1 : ((biprod.inl : I ⟶ LL I Q).f s) ≫ ((biprod.snd : LL I Q ⟶ sh Q).f s) = 0 := by
    rw [← HomologicalComplex.comp_f, biprod.inl_snd, HomologicalComplex.zero_f]
  have h2 : ((biprod.inr : sh Q ⟶ LL I Q).f s) ≫ ((biprod.snd : LL I Q ⟶ sh Q).f s) = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, biprod.inr_snd, HomologicalComplex.id_f]
  unfold cc
  rw [map_add (f := _)]
  change (Sec.map (((biprod.inl : I ⟶ LL I Q).f s) ≫ ((biprod.snd : LL I Q ⟶ sh Q).f s)) a +
    Sec.map (((biprod.inr : sh Q ⟶ LL I Q).f s) ≫ ((biprod.snd : LL I Q ⟶ sh Q).f s)) (show Sec ((sh Q).X s) T from b) : Sec ((sh Q).X s) T) = b
  rw [h1, h2, map_zeroS, zero_add]
  rfl

theorem cc_c {I Q : Cx R} {T : Scheme.{0}} {s : ℤ} (x : Sec ((LL I Q).X s) T) : cc (c₁ x) (c₂ x) = x := by
  have h : ((biprod.fst : LL I Q ⟶ I).f s) ≫ ((biprod.inl : I ⟶ LL I Q).f s) +
      ((biprod.snd : LL I Q ⟶ sh Q).f s) ≫ ((biprod.inr : sh Q ⟶ LL I Q).f s) = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, ← HomologicalComplex.add_f_apply, biprod.total, HomologicalComplex.id_f]
  change Sec.map _ (Sec.map _ x) + Sec.map _ (Sec.map _ x) = x
  rw [map_map, map_map, ← map_addS, h, map_idS]

theorem LLsec_ext {I Q : Cx R} {T : Scheme.{0}} {s : ℤ} (x y : Sec ((LL I Q).X s) T) (h₁ : c₁ x = c₁ y) (h₂ : c₂ x = c₂ y) : x = y := by
  rw [← cc_c x, ← cc_c y, h₁, h₂]

theorem c₁_res {I Q : Cx R} {V T : Scheme.{0}} {s : ℤ} (g : V ⟶ T) (x : Sec ((LL I Q).X s) T) : c₁ (Sec.res g x) = Sec.res g (c₁ x) :=
  (res_map _ g x).symm

theorem c₂_res {I Q : Cx R} {V T : Scheme.{0}} {s : ℤ} (g : V ⟶ T) (x : Sec ((LL I Q).X s) T) : c₂ (Sec.res g x) = Sec.res g (c₂ x) :=
  (res_map ((biprod.snd : LL I Q ⟶ sh Q).f s) g x).symm

theorem c₁_d {I Q : Cx R} {T : Scheme.{0}} (s t : ℤ) (x : Sec ((LL I Q).X s) T) : c₁ (Sec.map ((LL I Q).d s t) x) = Sec.map (I.d s t) (c₁ x) := by
  change Sec.map _ (Sec.map _ x) = Sec.map _ (Sec.map _ x)
  rw [map_map, map_map, (biprod.fst : LL I Q ⟶ I).comm]

theorem sh_d (Q : Cx R) (s t : ℤ) : (sh Q).d s t = - Q.d (s + -1) (t + -1) := by
  have : (sh Q).d s t = (-1 : ℤ).negOnePow • Q.d (s + -1) (t + -1) := CochainComplex.shiftFunctor_obj_d' _ _ _ _
  rw [this]
  simp

theorem c₂_d {I Q : Cx R} {T : Scheme.{0}} (s t : ℤ) (x : Sec ((LL I Q).X s) T) :
    c₂ (Sec.map ((LL I Q).d s t) x) = - Sec.map (Q.d (s + -1) (t + -1)) (c₂ x) := by
  have h := (biprod.snd : LL I Q ⟶ sh Q).comm s t
  have e : ((biprod.snd : LL I Q ⟶ sh Q).f s) ≫ (sh Q).d s t =
      -(((biprod.snd : LL I Q ⟶ sh Q).f s) ≫ (show (sh Q).X s ⟶ (sh Q).X t from Q.d (s + -1) (t + -1))) := by
    rw [sh_d]
    exact Preadditive.comp_neg _ _
  change Sec.map _ (Sec.map _ x) = _
  rw [map_map, ← h, e]
  rfl

theorem sg_pull {X Y : Scheme.{0}} {I : Cx R} {n : ℤ} (f : Y ⟶ X) (α : Cocycle ((chains R).obj (sch.obj X)) I n) :
    sg (zcomp (Cocycle.ofHom ((chains R).map (sch.map f))) α (zero_add n)) = Sec.res f (sg α) := by
  let k := op (SimplexCategory.mk 0)
  let g := (sch.map f).app k
  have hChains : (chainsXIso R (sch.obj Y) 0).inv ≫ ((chains R).map (sch.map f)).f (-((0 : ℕ) : ℤ)) =
      (free R).map g ≫ (chainsXIso R (sch.obj X) 0).inv := by
    have h : ((chains R).map (sch.map f)).f (-((0 : ℕ) : ℤ)) =
        (chainsXIso R (sch.obj Y) 0).hom ≫ ((chainsN R).map (sch.map f)).f 0 ≫
          (chainsXIso R (sch.obj X) 0).inv :=
      HomologicalComplex.extendMap_f ((chainsN R).map (sch.map f))
        ComplexShape.embeddingDownNat (i := 0) rfl
    rw [h, Iso.inv_hom_id_assoc]
    rfl
  have hMap : Sec.map ((free R).map g) (freeGen R ((sch.obj Y).obj k) Y (𝟙 Y)) =
      freeGen R ((sch.obj X).obj k) Y f := by
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app (toSheafify_naturality Scheme.etaleTopology.{0} ((freeP R).map (yoneda.map f))) (op Y))
      (ModuleCat.freeMk (ULift.up (𝟙 Y)))
    have hGen : ((freeP R).map (yoneda.map f)).app (op Y) (ModuleCat.freeMk (ULift.up (𝟙 Y))) =
        ModuleCat.freeMk (ULift.up f) := by
      change (ModuleCat.free (ULift.{1} R)).map (TypeCat.ofHom (fun x : ULift (Y ⟶ Y) => ULift.up (x.down ≫ f)))
        (ModuleCat.freeMk (ULift.up (𝟙 Y))) = _
      rw [ModuleCat.free_map_apply]
      exact congrArg (fun a : Y ⟶ X => ModuleCat.freeMk (ULift.up a)) (Category.id_comp f)
    exact h.symm.trans (congrArg ((toSheafify Scheme.etaleTopology ((freeP R).obj (yoneda.obj X))).app (op Y)).hom hGen)
  have hRes : Sec.res f (freeGen R ((sch.obj X).obj k) X (𝟙 X)) = freeGen R ((sch.obj X).obj k) Y f := by
    have h := ConcreteCategory.congr_hom
      ((toSheafify Scheme.etaleTopology ((freeP R).obj (yoneda.obj X))).naturality f.op)
      (ModuleCat.freeMk (ULift.up (𝟙 X)))
    have hGen : ((freeP R).obj (yoneda.obj X)).map f.op (ModuleCat.freeMk (ULift.up (𝟙 X))) =
        ModuleCat.freeMk (ULift.up f) := by
      change (ModuleCat.free (ULift.{1} R)).map (TypeCat.ofHom (fun x : ULift (X ⟶ X) => ULift.up (f ≫ x.down)))
        (ModuleCat.freeMk (ULift.up (𝟙 X))) = _
      rw [ModuleCat.free_map_apply]
      exact congrArg (fun a : Y ⟶ X => ModuleCat.freeMk (ULift.up a)) (Category.comp_id f)
    exact h.symm.trans (congrArg ((toSheafify Scheme.etaleTopology ((freeP R).obj (yoneda.obj X))).app (op Y)).hom hGen)
  change Sec.map ((chainsXIso R (sch.obj Y) 0).inv ≫
      ((Cochain.ofHom ((chains R).map (sch.map f))).comp α.1 (zero_add n)).v _ _ (by simp))
      (freeGen R ((sch.obj Y).obj k) Y (𝟙 Y)) =
    Sec.res f (Sec.map ((chainsXIso R (sch.obj X) 0).inv ≫ α.1.v _ _ (by simp))
      (freeGen R ((sch.obj X).obj k) X (𝟙 X)))
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, hChains, Category.assoc,
    ← map_map, hMap, res_map, hRes]

theorem sg_sub {X : Scheme.{0}} {I : Cx R} {n : ℤ} (α β : Cocycle ((chains R).obj (sch.obj X)) I n) : sg (α - β) = sg α - sg β := by
  change ev (α.1 - β.1) 0 n (by simp) X (𝟙 X) = sg α - sg β
  simp only [sg, ev, Cochain.sub_v, Preadditive.comp_sub]
  rfl

theorem res_add {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) : Sec.res g (x + y) = Sec.res g x + Sec.res g y :=
  map_add _ _ _

theorem res_units {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (ε : ℤˣ) (x : Sec F U) : Sec.res g (ε • x) = ε • Sec.res g x := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp

theorem psi_nat (W : Scheme.{0}) {I Q P : Cx R} (μ : Pair Q P I) (z : Sec (P.X 1) W) {T' T : Scheme.{0}} (g : T' ⟶ T) (s : ℤ)
    (a : Sec ((LL I Q).X s) T) : Sec.res (prod.map (𝟙 W) g) (psi W μ z T s a) = psi W μ z T' s (Sec.res g a) := by
  change Sec.res (prod.map (𝟙 W) g) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₁ a) +
      s.negOnePow • μ.mul (W ⨯ T) (s + -1) 1 s (by omega) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ a)) (Sec.res (prod.fst : W ⨯ T ⟶ W) z)) =
    Sec.res (prod.snd : W ⨯ T' ⟶ T') (c₁ (Sec.res g a)) +
      s.negOnePow • μ.mul (W ⨯ T') (s + -1) 1 s (by omega) (Sec.res (prod.snd : W ⨯ T' ⟶ T') (c₂ (Sec.res g a))) (Sec.res (prod.fst : W ⨯ T' ⟶ W) z)
  rw [res_add, res_units, μ.nat, c₁_res, c₂_res, res_res, res_res, res_res, res_res, res_res]
  simp

theorem LL_inj {I Q : Cx R} (hI : ∀ s, Injective (I.X s)) (hQ : ∀ s, Injective (Q.X s)) (s : ℤ) : Injective ((LL I Q).X s) := by
  have hQ' : Injective ((sh Q).X s) := hQ (s + -1)
  have h : ((biprod.fst : LL I Q ⟶ I).f s) ≫ ((biprod.inl : I ⟶ LL I Q).f s) +
      ((biprod.snd : LL I Q ⟶ sh Q).f s) ≫ ((biprod.inr : sh Q ⟶ LL I Q).f s) = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, ← HomologicalComplex.add_f_apply, biprod.total, HomologicalComplex.id_f]
  refine ⟨fun {X Y} g f _ => ?_⟩
  haveI := hI s
  obtain ⟨h₁, e₁⟩ := Injective.factors (g ≫ (biprod.fst : LL I Q ⟶ I).f s) f
  obtain ⟨h₂, e₂⟩ := Injective.factors (g ≫ (biprod.snd : LL I Q ⟶ sh Q).f s) f
  refine ⟨h₁ ≫ (biprod.inl : I ⟶ LL I Q).f s + h₂ ≫ (biprod.inr : sh Q ⟶ LL I Q).f s, ?_⟩
  rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc, e₁, e₂, Category.assoc, Category.assoc, ← Preadditive.comp_add, h, Category.comp_id]

theorem LL_ge (I Q : Cx R) [I.IsStrictlyGE 0] [Q.IsStrictlyGE 0] : (LL I Q).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  have hI := I.isZero_of_isStrictlyGE 0 i hi
  have hQ : IsZero ((sh Q).X i) := Q.isZero_of_isStrictlyGE 0 (i + -1) (by omega)
  have h : ((biprod.fst : LL I Q ⟶ I).f i) ≫ ((biprod.inl : I ⟶ LL I Q).f i) +
      ((biprod.snd : LL I Q ⟶ sh Q).f i) ≫ ((biprod.inr : sh Q ⟶ LL I Q).f i) = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, ← HomologicalComplex.add_f_apply, biprod.total, HomologicalComplex.id_f]
  rw [IsZero.iff_id_eq_zero, ← h, hI.eq_of_tgt ((biprod.fst : LL I Q ⟶ I).f i) 0, hQ.eq_of_tgt ((biprod.snd : LL I Q ⟶ sh Q).f i) 0]
  simp

end UpperTheory.Kun
end
end

