module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsTangentEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0528
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0511
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0544
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtExponentialDerivativeBijectiveTangent
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantPeriodMarkingUniversalCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0538
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemBasicOpenOfMemClosure

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenDecompositionVectorBundle
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet GlobalTheory.Points GlobalTheory.GradedPieces GlobalTheory.LieVB GlobalTheory.VB

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.EigenFrames
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover)
open GlobalTheory.QCoh (appLinear appLinear_apply)
open GlobalTheory.LB (resG_resG le_iSup_inf)

variable {X : Scheme.{0}} {F G : X.Modules}

theorem isFrame_mkSec (N : Sub F) {U : X.Opens} {ν : Type} [Fintype ν] (e : ν → Γ(F, U))
    (he : ∀ i, e i ∈ N.sec U)
    (hli : ∀ (V : X.Opens) (h : V ≤ U), LinearIndependent Γ(X, V) fun i => resM F h (e i))
    (hsp : ∀ (V : X.Opens) (h : V ≤ U) (x : Γ(F, V)), x ∈ N.sec V →
      x ∈ Submodule.span Γ(X, V) (Set.range fun i => resM F h (e i))) :
    GlobalTheory.VB.IsFrame (F := N.toMod) fun i => N.mkSec (e i) (he i) := by
  rw [GlobalTheory.VB.isFrame_iff]
  intro V h
  have hcomp : (appLinear N.incl V) ∘ (fun i => resM N.toMod h (N.mkSec (e i) (he i))) =
      fun i => resM F h (e i) := funext fun i => by
    simp only [Function.comp, appLinear_apply]
    rw [app_resM]
    rfl
  refine ⟨LinearIndependent.of_comp (appLinear N.incl V) (hcomp ▸ hli V h), ?_⟩
  rintro y -
  have hx := hsp V h _ (N.incl_app_mem y)
  rw [← hcomp, Set.range_comp, Submodule.span_image] at hx
  obtain ⟨y', hy', e'⟩ := hx
  have : y' = y := N.incl_app_injective V (by rwa [appLinear_apply] at e')
  exact this ▸ hy'

section Frames

variable {O : Type} [CommRing O] (ρ : O →+* CategoryTheory.End F) {κ : Type} [Fintype κ]
  (τ : κ → (O →+* Γ(X, ⊤))) {m : κ → ℕ} {U : X.Opens} (B : (Σ i, Fin (m i)) → Γ(F, U))
  (hB : GlobalTheory.VB.IsFrame B)
  (hact : ∀ i k a, (act ρ a).app U (B ⟨i, k⟩) = resG X (le_top : U ≤ ⊤) (τ i a) • B ⟨i, k⟩)

end Frames

end GlobalTheory.EigenFrames
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenFrameBasePointLiftsUniqueFlagSpace
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F]

theorem spMap_inj' {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g := by
  have h1 : CommRingCat.ofHom f = CommRingCat.ofHom g := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom h1

private theorem spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f)
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem stalkPt_genStr (B : GlobalTheory.ProjVar.Var F) (e : F ≃+* c.F) (j : B.X ⟶ gen Z)
    (hj : j ≫ genStr Z ≫ spMap e.toRingHom = B.str) (z : B.X) (φA : c.F →+* B.X.presheaf.stalk z)
    (hφ : constF e B = (algebraMap (B.X.presheaf.stalk z) B.X.functionField).comp φA) :
    stalkPt B z ≫ j ≫ genStr Z = spMap φA := by
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (stalkPt B z ≫ j ≫ genStr Z)
  have hgen : spMap (algebraMap (B.X.presheaf.stalk z) B.X.functionField) ≫ stalkPt B z = genericPt B :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec B.X).specializes trivial)
  have hpt : genericPt B ≫ B.str = spMap (algebraMap F B.Fn) := (ratOf B).pt_s
  have key : ((algebraMap (B.X.presheaf.stalk z) B.X.functionField).comp ψ.hom).comp e.toRingHom =
      algebraMap F B.Fn := by
    apply spMap_inj'
    rw [spMap_comp_moduli_spaces, spMap_comp_moduli_spaces, ← hpt, ← hj, ← hgen,
      show spMap ψ.hom = stalkPt B z ≫ j ≫ genStr Z from hψ]
    simp only [Category.assoc]
  have hψeq : ψ.hom = φA := by
    ext a
    apply IsFractionRing.injective (B.X.presheaf.stalk z) B.X.functionField
    have e1 := RingHom.congr_fun key (e.symm a)
    have e2 := RingHom.congr_fun hφ a
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply] at e1
    simp only [constF, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at e2
    exact e1.trans e2
  rw [← hψ, ← hψeq]
  try rfl

private theorem coord_unique' {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    {φ : c.F →+* R} {φ' : c.F →+* R'} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} {f : EigFrame Z φ x}
    {ψ₁ ψ₂ : R →+* R'} {g : EigFrame Z φ' x'} {M₁ M₂ : Mat Dw.mult R'} (hψ : ψ₁ = ψ₂)
    (h₁ : f.Coord ψ₁ g M₁) (h₂ : f.Coord ψ₂ g M₂) : M₁ = M₂ := by
  subst hψ
  obtain ⟨hx, hφ, -⟩ := id h₁
  exact ((GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible _ _ _ _ _ _ _ _ _ _ _ _ f _ _ _ ψ₁ inferInstance
    (GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing _ _ _ _ _ _ _ _ _ _ _ _ f inferInstance) hx hφ).1 g).1.unique h₁ h₂

private theorem coord_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] [IsLocalRing R'']
    {φ : c.F →+* R} {φ' : c.F →+* R'} {φ'' : c.F →+* R''} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X}
    {x'' : Sp R'' ⟶ Z.X} {f : EigFrame Z φ x} {g : EigFrame Z φ' x'} {k : EigFrame Z φ'' x''}
    {ψ : R →+* R'} {ψ' : R' →+* R''} {M : Mat Dw.mult R'} {M' : Mat Dw.mult R''}
    (h₁ : f.Coord ψ g M) (h₂ : g.Coord ψ' k M') : f.Coord (ψ'.comp ψ) k (M' * M.map ψ') :=
  _root_.GlobalTheory.ShFam.CoordComp.coord_comp _ _ _ _ _ _ _ _ _ _ _ _ f _ _ _ g _ _ _ k ψ ψ' M M' inferInstance h₁ h₂

private theorem exists_coord_unit_det_of_baseChange {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    {φ : c.F →+* R} {φ' : c.F →+* R'} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} (f : EigFrame Z φ x)
    (ψ : R →+* R') (hx : x' = spMap ψ ≫ x) (hφ : φ' = ψ.comp φ) (g : EigFrame Z φ' x') :
    ∃ M : Mat Dw.mult R', f.Coord ψ g M ∧ ∀ τ, IsUnit (M τ).det := by
  have H := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible _ _ _ _ _ _ _ _ _ _ _ _ f _ _ _ ψ inferInstance
    (GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing _ _ _ _ _ _ _ _ _ _ _ _ f inferInstance) hx hφ).1 g
  obtain ⟨M, hM, -⟩ := H.1
  exact ⟨M, hM, H.2 M hM⟩

section Lifts

variable (e : F ≃+* c.F) (C : FlagCpt Z e) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z)
  (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn)
  (S' : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₁ : Mat Dw.mult C.Y.Fn) (φ : B.Fn →ₐ[F] C.Y.Fn) (f : C.Y.X ⟶ B.X)

theorem coord_iff (hπ : C.π = f ≫ j) (hT : Tied e B j f₀ S A₀) (hT' : Tied e C.Y C.π C.f0 S' A₁)
    (hC : f₀.Coord (φ : B.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹)) (hR : Refines S S' φ f)
    {K : Type} [Field K] {χ : c.F →+* K} {x : Sp K ⟶ gen Z} (p : Sp K ⟶ C.Y.X) (hx : (p ≫ f) ≫ j = x)
    (g : EigFrame Z χ (x ≫ genι Z))
    {A : Mat Dw.mult B.Fn} (_hA : A ∈ S.S (f (p (IsLocalRing.closedPoint K))))
    {φA : c.F →+* B.X.presheaf.stalk (f (p (IsLocalRing.closedPoint K)))}
    {fA : EigFrame Z φA (stalkPt B (f (p (IsLocalRing.closedPoint K))) ≫ j ≫ genι Z)}
    (hfA : fA.Coord (algebraMap _ B.X.functionField) f₀ (A₀ * A⁻¹))
    {h : Mat Dw.mult K} (hh : fA.Coord (Scheme.stalkClosedPointTo (R := .of K) (p ≫ f)).hom g h)
    {A' : Mat Dw.mult C.Y.Fn} (hA' : A' ∈ S'.S (p (IsLocalRing.closedPoint K)))
    {φ₁ : c.F →+* C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))}
    {f₁ : EigFrame Z φ₁ (stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z)}
    (hf₁ : f₁.Coord (algebraMap _ C.Y.X.functionField) C.f0 (A₁ * A'⁻¹)) :
    (∀ τ, (((A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p)) τ).det ≠ 0) ∧
    ∀ h' : Mat Dw.mult K, f₁.Coord (Scheme.stalkClosedPointTo (R := .of K) p).hom g h' ↔
      h = h' * (A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p) := by
  obtain ⟨hA₀g, -⟩ := id hT
  obtain ⟨hA₁g, -⟩ := id hT'
  have hA₁d : ∀ τ, (A₁ τ).det ≠ 0 := Fr.det_ne hA₁g
  have hA'd : ∀ τ, (A' τ).det ≠ 0 := Fr.det_ne hA'
  have hA₀φ : ∀ τ, ((A₀.map φ) τ).det ≠ 0 := by
    intro τ
    have e0 : ((A₀.map φ) τ).det = (φ : B.Fn →+* C.Y.Fn) (A₀ τ).det :=
      (RingHom.map_det (φ : B.Fn →+* C.Y.Fn) (A₀ τ)).symm
    rw [e0]
    exact (map_ne_zero _).2 (Fr.det_ne hA₀g τ)
  have hσ : (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField).comp (f.stalkMap (p (IsLocalRing.closedPoint K))).hom =
      (φ : B.Fn →+* C.Y.Fn).comp (algebraMap (B.X.presheaf.stalk (f (p (IsLocalRing.closedPoint K)))) B.X.functionField) := by
    ext a
    exact (map_algebraMap_stalk hR.hom _ a).symm
  have hxC : stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z =
      spMap (f.stalkMap (p (IsLocalRing.closedPoint K))).hom ≫ (stalkPt B (f (p (IsLocalRing.closedPoint K))) ≫ j ≫ genι Z) := by
    rw [hπ]
    show C.Y.X.fromSpecStalk _ ≫ (f ≫ j) ≫ genι Z =
      Spec.map (f.stalkMap _) ≫ B.X.fromSpecStalk _ ≫ j ≫ genι Z
    simp only [Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]
  obtain ⟨-, hφf₁, -⟩ := id hf₁
  obtain ⟨-, hφfA, -⟩ := id hfA
  have hφ₁ : φ₁ = (f.stalkMap (p (IsLocalRing.closedPoint K))).hom.comp φA := by
    ext a
    apply IsFractionRing.injective (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField
    have e1 := RingHom.congr_fun hφf₁ a
    have e2 := RingHom.congr_fun hφfA a
    have e3 := RingHom.congr_fun hσ (φA a)
    simp only [RingHom.comp_apply] at e1 e2 e3 ⊢
    rw [← e1, e3, ← e2]
    simp [constF]
  obtain ⟨N, hN, hNu⟩ := exists_coord_unit_det_of_baseChange fA (f.stalkMap (p (IsLocalRing.closedPoint K))).hom hxC hφ₁ f₁
  have h2 := coord_comp' hfA hC
  have h4 := coord_comp' hN hf₁
  have h5 := coord_unique' hσ h4 h2
  rw [Mat.map_mul, Mat.map_inv] at h5
  try simp only [AlgHom.coe_toRingHom] at h5
  have hNeq : N.map (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) = A' * (A.map φ)⁻¹ := by
    calc N.map (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) = (A' * A₁⁻¹) * (A₁ * A'⁻¹ * N.map (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField)) := by
          simp only [← mul_assoc]
          rw [mul_assoc A' A₁⁻¹ A₁, Mat.inv_mul hA₁d, mul_one, Mat.mul_inv hA'd, one_mul]
      _ = (A' * A₁⁻¹) * (A₁ * (A₀.map φ)⁻¹ * (A₀.map φ * (A.map φ)⁻¹)) := by rw [h5]
      _ = A' * (A.map φ)⁻¹ := by
          simp only [← mul_assoc]
          rw [mul_assoc A' A₁⁻¹ A₁, Mat.inv_mul hA₁d, mul_one, mul_assoc A' (A₀.map φ)⁻¹ (A₀.map φ),
            Mat.inv_mul hA₀φ, mul_one]
  have hval : ∀ n : C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K)),
      (ratOf C.Y).val p ((algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) n) = (Scheme.stalkClosedPointTo (R := .of K) p).hom n := by
    intro n
    calc (ratOf C.Y).val p ((algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) n)
        = (ratOf C.Y).val (spMap (Scheme.stalkClosedPointTo (R := .of K) p).hom ≫ C.Y.X.fromSpecStalk (p (IsLocalRing.closedPoint K))) ((algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) n) := by
          exact congrArg (fun q : Sp K ⟶ C.Y.X => (ratOf C.Y).val q ((algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) n))
            (spMap_stalkClosedPointTo p).symm
      _ = (Scheme.stalkClosedPointTo (R := .of K) p).hom n := val_ratOf _ _
  have hM : (A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p) = N.map (Scheme.stalkClosedPointTo (R := .of K) p).hom := by
    rw [← hNeq]
    funext τ
    ext a b
    exact hval (N τ a b)
  have hdetN : ∀ τ, ((N.map (Scheme.stalkClosedPointTo (R := .of K) p).hom) τ).det ≠ 0 := by
    intro τ
    have e0 : ((N.map (Scheme.stalkClosedPointTo (R := .of K) p).hom) τ).det = (Scheme.stalkClosedPointTo (R := .of K) p).hom (N τ).det := (RingHom.map_det (Scheme.stalkClosedPointTo (R := .of K) p).hom (N τ)).symm
    rw [e0]
    exact ((hNu τ).map _).ne_zero
  have hdetM : ∀ τ, (((A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p)) τ).det ≠ 0 := by
    rw [hM]; exact hdetN
  have hev : (Scheme.stalkClosedPointTo (R := .of K) (p ≫ f)).hom = (Scheme.stalkClosedPointTo (R := .of K) p).hom.comp (f.stalkMap (p (IsLocalRing.closedPoint K))).hom := by
    rw [Scheme.stalkClosedPointTo_comp]; try rfl
  have fwd : ∀ h' : Mat Dw.mult K, f₁.Coord (Scheme.stalkClosedPointTo (R := .of K) p).hom g h' → h = h' * N.map (Scheme.stalkClosedPointTo (R := .of K) p).hom := by
    intro h' hh'
    exact coord_unique' hev hh (coord_comp' hN hh')
  obtain ⟨hxg, hχ, -⟩ := id hh
  have hxg' : x ≫ genι Z = spMap (Scheme.stalkClosedPointTo (R := .of K) p).hom ≫ (stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z) := by
    rw [hxC, hxg, hev, spMap_comp_moduli_spaces, Category.assoc]
  have hχ' : χ = (Scheme.stalkClosedPointTo (R := .of K) p).hom.comp φ₁ := by
    rw [hχ, hev, hφ₁, RingHom.comp_assoc]
  obtain ⟨h'', hh'', -⟩ := exists_coord_unit_det_of_baseChange f₁ (Scheme.stalkClosedPointTo (R := .of K) p).hom hxg' hχ' g
  refine ⟨hdetM, fun h' => ⟨fun hh' => ?_, fun heq => ?_⟩⟩
  · rw [fwd h' hh', hM]
  · have e1 := fwd h'' hh''
    rw [← hM] at e1
    have e2 : h'' * (A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p) =
        h' * (A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p) := e1.symm.trans heq
    have e3 : h'' = h' := by
      calc h'' = h'' * (A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p) *
            ((A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p))⁻¹ := by rw [mul_assoc, Mat.mul_inv hdetM, mul_one]
        _ = h' * (A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p) *
            ((A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p))⁻¹ := by rw [e2]
        _ = h' := by rw [mul_assoc, Mat.mul_inv hdetM, mul_one]
    rw [← e3]
    exact hh''

end Lifts

theorem flagex_lifts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z) (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn) (S' : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₁ : Mat Dw.mult C.Y.Fn) (φ : B.Fn →ₐ[F] C.Y.Fn) (f : C.Y.X ⟶ B.X), j ≫ genStr Z ≫ spMap e.toRingHom = B.str → C.π = f ≫ j → Tied e B j f₀ S A₀ → Tied e C.Y C.π C.f0 S' A₁ → f₀.Coord (φ : B.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹) → Refines S S' φ f → ∀ (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z) (x' : Sp K ⟶ B.X), x' ≫ j = x → x ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x' ∧ C.Carries p g := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C B j f₀ S A₀ S' A₁ φ f hj hπ hT hT' hC hR K _ χ x x' hx' hxs g
  obtain ⟨A, hA⟩ := S.nonempty (x' (IsLocalRing.closedPoint K))
  obtain ⟨-, hTie⟩ := id hT
  obtain ⟨φA, fA, hfA⟩ := hTie _ A hA
  have hx'f : spMap (Scheme.stalkClosedPointTo (R := .of K) x').hom ≫ stalkPt B (x' (IsLocalRing.closedPoint K)) = x' := spMap_stalkClosedPointTo x'
  obtain ⟨-, hφA, -⟩ := id hfA
  have hsg := stalkPt_genStr B e j hj (x' (IsLocalRing.closedPoint K)) φA hφA
  have hχ : χ = (Scheme.stalkClosedPointTo (R := .of K) x').hom.comp φA := by
    apply spMap_inj'
    calc spMap χ = x ≫ genStr Z := hxs.symm
      _ = (x' ≫ j) ≫ genStr Z := by rw [hx']
      _ = ((spMap (Scheme.stalkClosedPointTo (R := .of K) x').hom ≫ stalkPt B (x' (IsLocalRing.closedPoint K))) ≫ j) ≫ genStr Z := by rw [hx'f]
      _ = spMap (Scheme.stalkClosedPointTo (R := .of K) x').hom ≫ (stalkPt B (x' (IsLocalRing.closedPoint K)) ≫ j ≫ genStr Z) := by simp only [Category.assoc]
      _ = spMap (Scheme.stalkClosedPointTo (R := .of K) x').hom ≫ spMap φA := by rw [hsg]
      _ = spMap ((Scheme.stalkClosedPointTo (R := .of K) x').hom.comp φA) := (spMap_comp_moduli_spaces _ _).symm
  have hxg : x ≫ genι Z = spMap (Scheme.stalkClosedPointTo (R := .of K) x').hom ≫ (stalkPt B (x' (IsLocalRing.closedPoint K)) ≫ j ≫ genι Z) := by
    calc x ≫ genι Z = (x' ≫ j) ≫ genι Z := by rw [hx']
      _ = ((spMap (Scheme.stalkClosedPointTo (R := .of K) x').hom ≫ stalkPt B (x' (IsLocalRing.closedPoint K))) ≫ j) ≫ genι Z := by rw [hx'f]
      _ = _ := by simp only [Category.assoc]
  obtain ⟨h, hh, hu⟩ := exists_coord_unit_det_of_baseChange fA (Scheme.stalkClosedPointTo (R := .of K) x').hom hxg hχ g
  have hPar : Par (0 : (E →+* ℂ) → ℕ) ⊤ h := fun τ =>
    ⟨fun _ _ => Subring.mem_top _, (hu τ).ne_zero, Subring.mem_top _, fun i _ hi => by simp at hi⟩
  obtain ⟨p, ⟨hp1, hp2⟩, huniq⟩ := hR.lifts K x' A hA h hPar
  obtain ⟨-, hTie'⟩ := id hT'
  have key : ∀ q : Sp K ⟶ C.Y.X, q ≫ f = x' → (Bears S' φ A h q ↔ C.Carries q g) := by
    intro q hq
    subst hq
    rw [GlobalTheory.T.carriesFlags_iff_adaptedFrame_at_image _ _ _ _ _ _ _ _ _ _ e C S' A₁ K χ (x ≫ genι Z) g q hT']
    constructor
    · rintro ⟨A', hA', hPar'⟩
      obtain ⟨φ₁, f₁, hf₁⟩ := hTie' _ A' hA'
      have hci := coord_iff e C B j f₀ S A₀ S' A₁ φ f hπ hT hT' hC hR q hx' g hA hfA hh hA' hf₁
      refine ⟨A', hA', φ₁, f₁, h * ((A' * (A.map φ)⁻¹).map ((ratOf C.Y).val q))⁻¹, hf₁, ?_, hPar'⟩
      rw [hci.2, mul_assoc, Mat.inv_mul hci.1, mul_one]
    · rintro ⟨A', hA', φ₁, f₁, h', hf₁, hh', hPar'⟩
      have hci := coord_iff e C B j f₀ S A₀ S' A₁ φ f hπ hT hT' hC hR q hx' g hA hfA hh hA' hf₁
      refine ⟨A', hA', ?_⟩
      rw [(hci.2 h').1 hh', mul_assoc, Mat.mul_inv hci.1, mul_one]
      exact hPar'
  exact ⟨p, ⟨hp1, (key p hp1).1 hp2⟩, fun q hq => huniq q ⟨hq.1, (key q hq.1).2 hq.2⟩⟩

end GlobalTheory.ShFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleChartHolomorphicCoordinateChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh

theorem valAt'_eq_ev {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {U : Y.Opens}
    {x : CxPts p σ} (h : x ∈ CxPts.ptsIn p σ U) (f : Γ(Y, U)) : valAt' x.1 U f = CxPts.ev p σ U f x := by
  rw [CxPts.ev_eq h, CxPts.evHom_eq_evalPt h, TangentOrigin.valAt'_eq_evalPt _ _ h]

theorem chart_change : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ) (c : AlgChart p σ n) (ψ : OpenPartialHomeomorph (ReciprocityTheory.L2DbarEstimates.V n) (Fin n → ℂ)), DifferentiableOn ℂ ψ ψ.source → DifferentiableOn ℂ ψ.symm ψ.target → (∀ j, HolAlong (c.e.trans ψ).source fun x => (c.e.trans ψ) x j) ∧ IsHolTo (c.e.trans ψ).target (fun z => ((c.e.trans ψ).symm z).1) := by
  intro k _ Y p n σ c ψ hψ hψs
  refine ⟨fun j V _ _ _ B x hB hx hm => ?_, fun U' f => ⟨?_, ?_⟩⟩
  · have hs : ∀ b ∈ B, x b ∈ c.e.source ∧ c.e (x b) ∈ ψ.source := fun b hb => by
      simpa [OpenPartialHomeomorph.trans_source] using hm hb
    have hco : ∀ a, DifferentiableOn ℂ (fun b => c.e (x b) a) B := fun a => by
      refine ((hx c.U (c.x a)).2.mono fun b hb => ⟨hb, c.source_subset (hs b hb).1⟩).congr fun b hb => ?_
      rw [c.apply_eq _ (hs b hb).1, valAt'_eq_ev (c.source_subset (hs b hb).1)]
    have hce : DifferentiableOn ℂ (fun b => c.e (x b)) B := differentiableOn_euclidean.2 hco
    have h2 : DifferentiableOn ℂ (fun b => ψ (c.e (x b))) B := hψ.comp hce fun b hb => (hs b hb).2
    exact differentiableOn_pi.1 h2 j
  · exact (c.e.trans ψ).continuousOn_symm.isOpen_inter_preimage (c.e.trans ψ).open_target
      (CxPts.isOpen_ptsIn U')
  · have hm : ∀ z ∈ {z ∈ (c.e.trans ψ).target | ⊤ ≤ ((c.e.trans ψ).symm z).1 ⁻¹ᵁ U'},
        z ∈ ψ.target ∧ ψ.symm z ∈ c.e.target ∧ c.e.symm (ψ.symm z) ∈ CxPts.ptsIn p σ U' := fun z hz => by
      have h1 := hz.1
      simp only [OpenPartialHomeomorph.trans_target, Set.mem_inter_iff, Set.mem_preimage] at h1
      exact ⟨h1.1, h1.2, hz.2⟩
    have h2 : DifferentiableOn ℂ (CxPts.ev p σ U' f ∘ c.e.symm ∘ ψ.symm)
        {z ∈ (c.e.trans ψ).target | ⊤ ≤ ((c.e.trans ψ).symm z).1 ⁻¹ᵁ U'} :=
      (c.holo U' f).comp (hψs.mono fun z hz => (hm z hz).1) fun z hz => ⟨(hm z hz).2.1, (hm z hz).2.2⟩
    refine h2.congr fun z hz => ?_
    exact valAt'_eq_ev (hm z hz).2.2 f

end GlobalTheory.ShFam.Hor.LogCh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstIntegralCoordsLatticeSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_const_integral_coords_lattice_section : ∀ (n g r : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ζ : (Fin n → ℂ) → Fin g → ℂ) (b₀ : Fin n → ℂ), IsPreconnected B → ContinuousOn lam B → ContinuousOn ζ B → (∀ b ∈ B, IsLatBasis (K b) (lam b)) → (∀ b ∈ B, ζ b ∈ K b) → b₀ ∈ B → ∃ m : Fin r → ℤ, ∀ b ∈ B, ζ b = ∑ j, m j • lam b j := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.exists_const_coords | exact GlobalTheory.ShFam.Hor.LogCh.exists_const_coords | (intros; apply GlobalTheory.ShFam.Hor.LogCh.exists_const_coords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantLieBasisAnalyticBasisArc
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.ArcLieFrame

theorem exists_const_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu), ∃ (e : Fin g → Out.GtPt a.D₀ (epsR ℂ)) (v : Fin g → (epsR (PowerSeries ℂ) ⟶ W.t.G)) (z : Fin g → Fin g → ℂ), (∀ k, GlobalTheory.ArcQ.LieImg W (e k) (v k) ∧ GlobalTheory.ArcQ.AnVec Ha (e k) (z k)) ∧ IsLieBasis v ∧ (Matrix.of z).det ≠ 0 := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha
  have hG := GlobalTheory.SemiRigid.globalFns
  obtain ⟨g', e, v, -, hev, hb, hu, -⟩ := GlobalTheory.ConstLie.exists_const_basis hG E H Dw l Xo c V V.subtype Y ℂ
    (σ.comp V.subtype) a χ W
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.ExpTan.anVec_bijective hG E H Dw l Xo c σ V V.subtype Y a χ W g ty Fu Ha
  choose z hz using fun i => (h1 (e i) (hev i).1).exists
  have hli : LinearIndependent ℂ z := by
    rw [Fintype.linearIndependent_iff]
    intro cf hcf
    obtain ⟨ν, hν⟩ := GlobalTheory.ConstLie.exists_gtComb cf e
    obtain ⟨ν₀, hν₀⟩ := GlobalTheory.ConstLie.exists_gtComb (0 : Fin g' → ℂ) e
    have a1 := (h4 g' cf e z ν hz).1 hν
    have a0 := (h4 g' 0 e z ν₀ hz).1 hν₀
    rw [hcf] at a1
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at a0
    obtain rfl : ν = ν₀ := (h2 0).unique a1 a0
    have ht := h3 _ _ a1
    have := (hu ν ht).unique hν hν₀
    exact fun i => congrFun this i
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range z) := by
    intro z₀ _
    rw [Submodule.mem_span_range_iff_exists_fun]
    obtain ⟨ν, hν, -⟩ := h2 z₀
    obtain ⟨cf, hcf, -⟩ := hu ν (h3 _ _ hν)
    exact ⟨cf, (h1 ν (h3 _ _ hν)).unique ((h4 g' cf e z ν hz).1 hcf) hν⟩
  have hg : g' = g := by
    have := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
    simpa using this.symm
  subst hg
  refine ⟨e, v, z, fun k => ⟨(hev k).2, hz k⟩, hb, ?_⟩
  have hu' : IsUnit (Matrix.of z) := (Matrix.linearIndependent_rows_iff_isUnit).1 (by simpa using hli)
  exact (Matrix.isUnit_iff_isUnit_det _).1 hu' |>.ne_zero

end GlobalTheory.ArcLieFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantPeriodMarkingUniversalCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constant_periodMarking_universalCover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (n g' r k : ℕ) (ch : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g') (lam : (Fin n → ℂ) → Fin r → Fin g' → ℂ) (ρ : Fin g' → Fin r → ℂ), IsLogChart k ch ex lam ρ → ∃ (i : Fin Fu.n) (T₀ : (Fu.Di i).La ≃+ (Fin r → ℤ)), ∀ s ∈ logDom n k, ∀ (a : CxFr Z σ) (W : Letter Dw → Fin g' → ℂ), a.1 = ch.symm (logExp k s) → Dirs a (fun w => (ex a.1 w).left) W → ∃ (Q : (Fu.Di i).La →+ (Letter Dw → ℂ)) (gm : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i).La), Per Fu a i Q ∧ IsIsom (Fu.Di i) gm ∧ ∀ v, ∑ z, Q (gm v) z • W z = ∑ m, T₀ v m • lam s m := by
  first | exact @GlobalTheory.ShFam.Hor.Mark.exists_marking_const | exact GlobalTheory.ShFam.Hor.Mark.exists_marking_const | (intros; apply GlobalTheory.ShFam.Hor.Mark.exists_marking_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagCellOfNonvanishingLeadingMinorsStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flagCell_of_nonvanishing_leading_minors : ∀ (T : Type) (m : T → ℕ) (K : Type) [Field K] (M : ℕ) (D c u : Let m → Fin (M + 1) → K) (w : Pm m), LeftInv D c → InBlock c u → (∀ τ j hj, ∑ q, lform D (wLet w ∘ std τ j hj) q * plk u (std τ j hj) q ≠ 0) → ∃ (x : CellVar m → K) (d : Let m → K), (∀ z, d z ≠ 0) ∧ Tri (cellVec c w x) u d := by
  first | exact @GlobalTheory.FlagEmb.CellLU.exists_cell | exact GlobalTheory.FlagEmb.CellLU.exists_cell | (intros; apply GlobalTheory.FlagEmb.CellLU.exists_cell <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsProjOverIsIsoMorphismRestrict
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ChowLemma

theorem exists_dominant_lift {X X' : Scheme.{0}} (π : X' ⟶ X) {U W : X.Opens} (h : U ≤ W)
    (t : U.toScheme ⟶ X') [IsDominant t] (ht : t ≫ π = U.ι) :
    ∃ σ : U.toScheme ⟶ (π ⁻¹ᵁ W).toScheme, IsDominant σ ∧ σ ≫ (π ⁻¹ᵁ W).ι = t ∧
      σ ≫ π ∣_ W = X.homOfLE h := by
  have hr : Set.range t ⊆ Set.range (π ⁻¹ᵁ W).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change π (t x) ∈ W
    rw [← Scheme.Hom.comp_apply, ht]
    exact h x.2
  have e := IsOpenImmersion.lift_fac (π ⁻¹ᵁ W).ι t hr
  refine ⟨IsOpenImmersion.lift (π ⁻¹ᵁ W).ι t hr, ?_, e, ?_⟩
  · have : IsDominant (IsOpenImmersion.lift (π ⁻¹ᵁ W).ι t hr ≫ (π ⁻¹ᵁ W).ι) := by
      rwa [e]
    exact IsDominant.of_comp_of_isOpenImmersion _ (π ⁻¹ᵁ W).ι
  · rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, reassoc_of% e, ht, X.homOfLE_ι]

theorem exists_isProjOver_isIso_morphismRestrict : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp R) [IsProper f], ∃ (X' : Scheme.{0}) (π : X' ⟶ X) (U : X.Opens), IsProjOver (π ≫ f) ∧ (U : Set X).Nonempty ∧ IsIso (π ∣_ U) := by
  first
  | exact @_root_.GlobalTheory.BasicOpenLocalExtension.chow_integral
  | exact _root_.GlobalTheory.BasicOpenLocalExtension.chow_integral
  | (apply _root_.GlobalTheory.BasicOpenLocalExtension.chow_integral <;> assumption)
  | (intros; apply _root_.GlobalTheory.BasicOpenLocalExtension.chow_integral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.BasicOpenLocalExtension.chow_integral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.BasicOpenLocalExtension.chow_integral ..)

end GlobalTheory.ChowLemma
end

