module

public import Development.WeilBound.CoreStatements.SesquilinearFractions.GLieIntB
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0129
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0133

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.GLieIntC
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

noncomputable section

namespace PositivityTheory.Xgf.isogeny_decomposition_product

variable {R : Type} [CommRing R]

theorem lc (C : Out.PolAV (Sp R)) (v : epsR R ⟶ C.A) (hv : IsLieBasis ![v]) (V : Type) [CommRing V] (f : R →+* V) :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module V E) (M : LieModel C.A (spMap f ≫ 𝟙 (Sp R)) E)
      (b : Module.Basis (Fin 1) V E), (M.pt (b 0)).left = spMap (dualMap f) ≫ v.left := by
  obtain ⟨E0, i0, m0, ⟨M0⟩⟩ := lieModel_exists (Sp R) C.A R (𝟙 (Sp R))
  obtain ⟨b0, hb0⟩ := basis_of_lieBasis v hv M0
  obtain ⟨E1, i1, m1, ⟨M1⟩⟩ := lieModel_exists (Sp R) C.A V (spMap f ≫ 𝟙 (Sp R))
  obtain ⟨j, hj, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LieBaseChange.existsUnique_semilinear_lifts (Sp R) C.A R V f (𝟙 _) E0 E1 M0 M1
  letI : Algebra R V := f.toAlgebra
  letI : Module R E1 := Module.compHom E1 f
  haveI : IsScalarTower R V E1 := ⟨fun r x e => by
    show (f r * x) • e = f r • (x • e)
    rw [mul_smul]⟩
  let jR : E0 →ₗ[R] E1 :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun r e => by
        show j (r • e) = f r • j e
        exact j.map_smulₛₗ r e }
  haveI : SmoothOfRelativeDimension C.g C.A.hom := C.smoothDim
  haveI : Smooth C.A.hom := by
    first
    | exact SmoothOfRelativeDimension.smooth C.g C.A.hom
    | exact SmoothOfRelativeDimension.smooth C.g
    | exact SmoothOfRelativeDimension.smooth (n := C.g)
  have hbc : IsBaseChange V jR := _root_.GlobalTheory.CompanionTheory.Ar.lieModel_isBaseChange (Sp R) C.A R V (𝟙 _) E0 E1 M0 M1 jR (fun e => hj e)
  refine ⟨E1, i1, m1, M1, hbc.basis b0, ?_⟩
  rw [IsBaseChange.basis_apply]
  have h := hj (b0 0)
  unfold LieModel.Lifts at h
  have h' := (Category.comp_id (M1.pt (j (b0 0))).left).symm.trans h
  show (M1.pt (j (b0 0))).left = _
  rw [h', hb0]

end PositivityTheory.Xgf.isogeny_decomposition_product

end
end

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.GModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf.TransportLieModel

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x : Sp R ⟶ S}

def transport {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E'] (M : LieModel G x E)
    (e : E ≃ₗ[R] E') : LieModel G x E' where
  pt v := M.pt (e.symm v)
  tan v := M.tan _
  inj a b h := e.symm.injective (M.inj h)
  onto v hv := by
    obtain ⟨w, hw⟩ := M.onto v hv
    exact ⟨e w, by simpa using hw⟩
  add a b := by rw [map_add (f := _), M.add]
  smul c a := by rw [map_smul]; exact M.smul c _

theorem isTanAt_comp {v : epsAt x ⟶ G} (hv : IsTanAt G x v) (f : G ⟶ G) [IsMonHom f] : IsTanAt G x (v ≫ f) := by
  unfold IsTanAt at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, MonObj.one_comp]

theorem mul_comp' {T : Over S} (u v : T ⟶ G) (f : G ⟶ G) [IsMonHom f] : (u * v) ≫ f = (u ≫ f) * (v ≫ f) := by
  simp [Hom.mul_def]

variable {E : Type} [AddCommGroup E] [Module R E]

def endo (M : LieModel G x E) (f : G ⟶ G) [IsMonHom f] (e : E) : E :=
  Classical.choose (M.onto (M.pt e ≫ f) (isTanAt_comp (M.tan e) f))

theorem endo_spec (M : LieModel G x E) (f : G ⟶ G) [IsMonHom f] (e : E) : M.pt (endo M f e) = M.pt e ≫ f :=
  Classical.choose_spec (M.onto (M.pt e ≫ f) (isTanAt_comp (M.tan e) f))

def diff (M : LieModel G x E) (f : G ⟶ G) [IsMonHom f] : E →ₗ[R] E where
  toFun := endo M f
  map_add' a b := M.inj (by rw [endo_spec, M.add, M.add, endo_spec, endo_spec, mul_comp'])
  map_smul' c a := M.inj (by
    rw [endo_spec, RingHom.id_apply, LieModel.pt_smul, LieModel.pt_smul, endo_spec, Category.assoc])

theorem diff_spec (M : LieModel G x E) (f : G ⟶ G) [IsMonHom f] (e : E) : M.pt (diff M f e) = M.pt e ≫ f :=
  endo_spec M f e

def rho {O : Type} [CommRing O] (act : OAct O G) (M : LieModel G x E) : O →+* Module.End R E where
  toFun a := letI := act.hom a; diff M (act.act a)
  map_one' := by
    ext e
    apply M.inj
    letI := act.hom 1
    show M.pt (diff M (act.act 1) e) = M.pt e
    rw [diff_spec, act.one, Category.comp_id]
  map_mul' a b := by
    ext e
    apply M.inj
    letI := act.hom a; letI := act.hom b; letI := act.hom (a * b)
    show M.pt (diff M (act.act (a * b)) e) = M.pt (diff M (act.act a) (diff M (act.act b) e))
    rw [diff_spec, diff_spec, diff_spec, mul_comm, act.mul, Category.assoc]
  map_zero' := by
    ext e
    apply M.inj
    letI := act.hom 0
    show M.pt (diff M (act.act 0) e) = M.pt 0
    have h0 : act.act 0 = 1 := by
      have := act.add 0 0
      rw [add_zero] at this
      exact mul_eq_left.1 this.symm
    rw [diff_spec, LieModel.pt_zero, h0, Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (M.pt e ≫ toUnit G)]
  map_add' a b := by
    ext e
    apply M.inj
    letI := act.hom a; letI := act.hom b; letI := act.hom (a + b)
    show M.pt (diff M (act.act (a + b)) e) = M.pt (diff M (act.act a) e + diff M (act.act b) e)
    rw [diff_spec, M.add, diff_spec, diff_spec, act.add, comp_mul]

theorem rho_isActOf {O : Type} [CommRing O] (act : OAct O G) (M : LieModel G x E) : M.IsActOf act.act (rho act M) :=
  fun a e => by letI := act.hom a; exact diff_spec M (act.act a) e

end PositivityTheory.Xgf.TransportLieModel

namespace PositivityTheory.Xgf

open TransportLieModel in
theorem lie_model_action_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (R : Type) [CommRing R] [IsLocalRing R] (x : Sp R ⟶ S), ∃ (n : ℕ) (M : LieModel t.G x (Fin n → R)) (ρ : 𝓞 E →+* Module.End R (Fin n → R)), M.IsActOf t.act.act ρ ∧ ∀ (R' : Type) [CommRing R'] (f : R →+* R') (x' : Sp R' ⟶ S), x' = spMap f ≫ x → ∃ (M' : LieModel t.G x' (Fin n → R')) (ρ' : 𝓞 E →+* Module.End R' (Fin n → R')), M'.IsActOf t.act.act ρ' ∧ (∀ u, (M'.pt (f ∘ u)).left = spMap (dualMap f) ≫ (M.pt u).left) ∧ ∀ a u, ρ' a (f ∘ u) = f ∘ ρ a u := by
  intro E _ _ _ H S t R _ _ x
  letI := t.grp
  haveI := t.comm
  haveI : Smooth t.G.hom := t.semi.smooth
  obtain ⟨L, _, _, ⟨M0⟩⟩ := lieModel_exists S t.G R x
  obtain ⟨hfin, hproj⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieModel_finite_projective S t.G R x L M0
  haveI := hfin
  haveI := hproj
  haveI : Module.Free R L := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis R L
  let M := transport M0 b.equivFun
  refine ⟨Module.finrank R L, M, rho t.act M, rho_isActOf t.act M, ?_⟩
  intro R' _ f x' hx'
  subst hx'
  letI : Algebra R R' := f.toAlgebra
  obtain ⟨T', _, _, _, _, M1, j, hj, hbc⟩ := FlagFib.lieModel_liftBaseChange S t.G R R' x L M0
  let b' := hbc.basis b
  let M' : LieModel t.G (spMap f ≫ x) (Fin (Module.finrank R L) → R') := transport M1 b'.equivFun
  have key : ∀ u : Fin (Module.finrank R L) → R, b'.equivFun.symm (f ∘ u) = j (b.equivFun.symm u) := by
    intro u
    apply b'.equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    funext i
    rw [Module.Basis.equivFun_apply, IsBaseChange.basis_repr_comp_apply, ← Module.Basis.equivFun_apply,
      LinearEquiv.apply_symm_apply]
    rfl
  have hpt : ∀ u, M'.pt (f ∘ u) = M1.pt (j (b.equivFun.symm u)) := by
    intro u
    show M1.pt (b'.equivFun.symm (f ∘ u)) = _
    rw [key]
  refine ⟨M', rho t.act M', rho_isActOf t.act M', ?_, ?_⟩
  · intro u
    rw [hpt]
    have h3 := hj (b.equivFun.symm u)
    simp only [LieModel.Lifts, Category.comp_id] at h3
    exact h3
  · intro a u
    apply M'.inj
    have h1 := rho_isActOf t.act M' a (f ∘ u)
    have h2 : M0.pt (b.equivFun.symm (rho t.act M a u)) = M0.pt (b.equivFun.symm u) ≫ t.act.act a :=
      rho_isActOf t.act M a u
    rw [h1, hpt, hpt]
    have h3 := hj (b.equivFun.symm u)
    have h4 := hj (b.equivFun.symm (rho t.act M a u))
    simp only [LieModel.Lifts, Category.comp_id] at h3 h4
    ext1
    rw [Over.comp_left, h3, h4, h2, Over.comp_left, Category.assoc]

end PositivityTheory.Xgf
end
end

