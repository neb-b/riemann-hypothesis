module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0529
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionTranslateZerosLt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsUnitNatCastSections
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.TowerOfAt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0545

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj

namespace GlobalTheory.HTMap

attribute [local instance] Over.cartesianMonoidalCategory

section Pull

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {T T' : Scheme.{0}} {y : T ⟶ X} {y' : T' ⟶ X}

theorem spc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by rw [← Spec.map_comp]; rfl

theorem spc_assoc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) {Z : Scheme.{0}}
    (h : Sp A ⟶ Z) : spMap g ≫ spMap f ≫ h = spMap (g.comp f) ≫ h := by rw [← Category.assoc, spc]

def pull (g : T' ⟶ T) (h : g ≫ y = y') : (Over.mk y ⟶ G) →* (Over.mk y' ⟶ G) := Formalism.L2.Pj.preHom (Over.homMk g h)

omit [GrpObj G] in
theorem over_w (w : Over.mk y ⟶ G) : w.left ≫ G.hom = y := Over.w w


omit [GrpObj G] in
def mkPt (w : T ⟶ G.left) (h : w ≫ G.hom = y) : Over.mk y ⟶ G := Over.homMk w h

omit [GrpObj G] in
theorem mkPt_left (w : T ⟶ G.left) (h : w ≫ G.hom = y) : (mkPt w h).left = w := rfl

theorem eq_pull {g : T' ⟶ T} (w : Over.mk y ⟶ G) (w' : Over.mk y' ⟶ G) (e : w'.left = g ≫ w.left) :
    ∃ h : g ≫ y = y', w' = pull g h w :=
  ⟨by rw [← over_w w, ← over_w w', e, Category.assoc], Over.OverMorphism.ext e⟩

theorem tors_of {g : T' ⟶ T} {w : Over.mk y ⟶ G} {w' : Over.mk y' ⟶ G} (e : w'.left = g ≫ w.left) {q : ℕ}
    (hw : w ^ q = 1) : w' ^ q = 1 := by
  obtain ⟨h, rfl⟩ := eq_pull w w' e
  rw [← map_pow, hw, map_one]

theorem one_of {g : T' ⟶ T} (h : g ≫ y = y') : (1 : Over.mk y' ⟶ G).left = g ≫ (1 : Over.mk y ⟶ G).left := by
  rw [← map_one (pull (G := G) g h)]; rfl

end Pull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {A : Type} [CommRing A] {x₀ : Sp A ⟶ X} {q : ℕ}


variable (t x₀ q) in
structure FP : Type 1 where
  f : A
  B : Type
  [ring : CommRing B]
  [alg : Algebra (Localization.Away f) B]
  u : Over.mk (spMap (algebraMap (Localization.Away f) B) ≫ spMap (algebraMap A (Localization.Away f)) ≫ x₀) ⟶ t.G
  ne : f ≠ 0
  fin : IsFinPart t (spMap (algebraMap A (Localization.Away f)) ≫ x₀) q u

attribute [instance] FP.ring FP.alg

namespace FP

variable (P : FP t x₀ q) {S S' : Type} [CommRing S] [CommRing S']

def str : A →+* P.B := (algebraMap (Localization.Away P.f) P.B).comp (algebraMap A (Localization.Away P.f))

def At (φ : A →+* S) (w : Sp S ⟶ t.G.left) (β : P.B →+* S) : Prop := β.comp P.str = φ ∧ spMap β ≫ P.u.left = w

variable {P}

theorem alg_ext {β β' : P.B →+* S} (h : β.comp P.str = β'.comp P.str) :
    β.comp (algebraMap (Localization.Away P.f) P.B) = β'.comp (algebraMap (Localization.Away P.f) P.B) :=
  IsLocalization.ringHom_ext (Submonoid.powers P.f) h

theorem At.map {φ : A →+* S} {w : Sp S ⟶ t.G.left} {β : P.B →+* S} (h : P.At φ w β) (ψ : S →+* S') :
    P.At (ψ.comp φ) (spMap ψ ≫ w) (ψ.comp β) :=
  ⟨by rw [← h.1]; rfl, by rw [← h.2]; exact (spc_assoc _ _ _).symm⟩

theorem At.over {φ : A →+* S} {w : Sp S ⟶ t.G.left} {β : P.B →+* S} (h : P.At φ w β) :
    w ≫ t.G.hom = spMap φ ≫ x₀ := by
  rw [← h.2, ← h.1, Category.assoc, over_w P.u, spc_assoc, spc_assoc]; rfl

theorem At.tors {φ : A →+* S} {y : Sp S ⟶ X} {w : Over.mk y ⟶ t.G} {β : P.B →+* S} (h : P.At φ w.left β) :
    w ^ q = 1 := tors_of h.2.symm P.fin.tors

theorem At.unit {φ : A →+* S} {w : Sp S ⟶ t.G.left} {β : P.B →+* S} (h : P.At φ w β) : IsUnit (φ P.f) := by
  rw [← h.1]
  exact ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away P.f) P.f).map
    (algebraMap (Localization.Away P.f) P.B)).map β

theorem at_iff (φ : Localization.Away P.f →+* S) (w : Sp S ⟶ t.G.left) :
    (∃ β, P.At (φ.comp (algebraMap A _)) w β) ↔ Thru t P.u.left φ w :=
  exists_congr fun _ => and_congr_left fun _ =>
    ⟨fun h => IsLocalization.ringHom_ext (Submonoid.powers P.f) h, fun h => by rw [← h]; rfl⟩

theorem ex_lift {φ : A →+* S} (hu : IsUnit (φ P.f)) :
    ∃ φ' : Localization.Away P.f →+* S, φ'.comp (algebraMap A _) = φ :=
  ⟨IsLocalization.Away.lift P.f hu, IsLocalization.Away.lift_comp _ _⟩

theorem at_open {φ : A →+* S} (hu : IsUnit (φ P.f)) {y : Sp S ⟶ X} (hy : y = spMap φ ≫ x₀) (w : Over.mk y ⟶ t.G)
    (hw : w ^ q = 1) (h : ∀ 𝔪 : Ideal S, 𝔪.IsMaximal →
      ∃ β, P.At ((Ideal.Quotient.mk 𝔪).comp φ) (spMap (Ideal.Quotient.mk 𝔪) ≫ w.left) β) :
    ∃ β, P.At φ w.left β := by
  obtain ⟨φ', rfl⟩ := ex_lift hu
  rw [← spc_assoc] at hy
  subst hy
  exact (at_iff _ _).2 (P.fin.isOpen S φ' w hw fun 𝔪 h𝔪 => (at_iff _ _).1 (h 𝔪 h𝔪))

theorem at_one {φ : A →+* S} (hu : IsUnit (φ P.f)) {y : Sp S ⟶ X} (hy : y = spMap φ ≫ x₀) :
    ∃ β, P.At φ (1 : Over.mk y ⟶ t.G).left β := by
  obtain ⟨φ', rfl⟩ := ex_lift hu
  rw [← spc_assoc] at hy
  subst hy
  exact (at_iff _ _).2 (P.fin.one S φ')

theorem At.mul {φ : A →+* S} {y : Sp S ⟶ X} {w w' : Over.mk y ⟶ t.G} {β β' : P.B →+* S} (h : P.At φ w.left β)
    (h' : P.At φ w'.left β') : ∃ β'', P.At φ (w * w').left β'' := by
  have hy : y = spMap φ ≫ x₀ := (over_w w).symm.trans h.over
  obtain ⟨φ', rfl⟩ := ex_lift h.unit
  rw [← spc_assoc] at hy
  subst hy
  exact (at_iff _ _).2 (P.fin.mul S φ' w w' ((at_iff _ _).1 ⟨_, h⟩) ((at_iff _ _).1 ⟨_, h'⟩))


end FP



section Dom

variable [IsDomain A]

namespace FP

variable (P : FP t x₀ q)

variable {P}



end FP

variable [IsIntegrallyClosed A] {κ : (Sp (FractionRing A) ⟶ t.G.left) → Aˣ}

end Dom

section Tan

variable {S : Type} [CommRing S] {x : Sp S ⟶ X}

theorem tan_tors {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x v) (hq : (q : S) = 0)
    {y : Sp (DualNumber S) ⟶ X} (w : Over.mk y ⟶ t.G) (e : w.left = v) : w ^ q = 1 := by
  have key : ∀ n : ℕ, smT x (n : S) (ovT hv) = ovT hv ^ n := fun n => by
    induction n with
    | zero => rw [Nat.cast_zero, pow_zero, smT_zero_ovT]
    | succ n ih => rw [Nat.cast_succ, smT_add x _ (smT_zero_ovT hv), ih, smT_unit, pow_succ]
  have h : ovT hv ^ q = 1 := by rw [← key, hq, smT_zero_ovT]
  exact tors_of (w := ovT hv) (g := 𝟙 _) (e.trans (Category.id_comp _).symm) h

theorem comb_single {g : ℕ} {e : Fin g → (Sp (DualNumber S) ⟶ t.G.left)} (he : ∀ i, IsTanAtG t x (e i)) (i : Fin g) :
    IsCombAtG t x e (Pi.single i 1) (e i) :=
  (isCombAtG_iff t x (fun j => ovT (he j)) _ _).2 (by rw [combT_single _ _ fun j => smT_zero_ovT _]; rfl)

theorem tan_at (P : FP t x₀ q) {φ : A →+* S} {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t (spMap φ ≫ x₀) v)
    (hq : (q : S) = 0) {S' : Type} [CommRing S'] (ψ : DualNumber S →+* S')
    (hu : IsUnit (ψ (((algebraMap S (DualNumber S)).comp φ) P.f))) :
    ∃ β, P.At (ψ.comp ((algebraMap S (DualNumber S)).comp φ)) (spMap ψ ≫ v) β := by
  refine FP.at_open (φ := ψ.comp ((algebraMap S (DualNumber S)).comp φ)) hu ?_ (mkPt (spMap ψ ≫ v) rfl)
    (tors_of (g := spMap ψ) (w := ovT hv) rfl (tan_tors hv hq _ rfl)) fun 𝔪 h𝔪 => ?_
  · rw [Category.assoc, hv.1, spc_assoc, spc_assoc]
  let ρ := (Ideal.Quotient.mk 𝔪).comp ψ
  have hρ : ρ = (ρ.comp (algebraMap S (DualNumber S))).comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
    refine RingHom.ext fun z => ?_
    have h0 : ρ (TrivSqZeroExt.inr z.snd) = 0 :=
      mul_self_eq_zero.1 (by rw [← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero])
    conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq z, map_add (f := _), h0, add_zero]
    rfl
  have e : spMap (Ideal.Quotient.mk 𝔪) ≫ spMap ψ ≫ v =
      (1 : Over.mk (spMap (ρ.comp (algebraMap S (DualNumber S))) ≫ spMap φ ≫ x₀) ⟶ t.G).left := by
    rw [one_of rfl, ← hv.2]
    exact (spc_assoc _ _ _).trans ((congrArg (fun z => spMap z ≫ v) hρ).trans (spc_assoc _ _ _).symm)
  rw [mkPt_left, e]
  exact FP.at_one (hu.map (Ideal.Quotient.mk 𝔪)) (spc_assoc _ _ _)

end Tan

section Char

variable {O : Type} [CommRing O] [IsLocalRing O] {x : A →+* O} {P : FP t x₀ q}

end Char


theorem cast_quot (R : Type) [CommRing R] (p n : ℕ) : ((p ^ n : ℕ) : R ⧸ Ideal.span {(p : R) ^ n}) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
  exact Ideal.mem_span_singleton_self _

end GlobalTheory.HTMap
