module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0528
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0511
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0501
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0521
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoordLetterEquivApplyConjugate
public import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0527
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0529
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0079
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLieEigenpartsFrameFamilyOverVariety
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam.TieBase

theorem spMap_trans {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem exists_affine_factor {Y : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R] (x : Sp R ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) (h : x (IsLocalRing.closedPoint R) ∈ U) :
    ∃ ψ : Γ(Y, U) →+* R, spMap ψ ≫ hU.fromSpec = x := by
  obtain ⟨ψ, hψ⟩ := EigLoc.exists_stalk_factor x _ (specializes_refl _)
  refine ⟨ψ.comp (Y.presheaf.germ U _ h).hom, ?_⟩
  have hg : spMap (Y.presheaf.germ U _ h).hom ≫ hU.fromSpec = Y.fromSpecStalk _ := by
    rw [← hU.fromSpecStalk_eq_fromSpecStalk h]; rfl
  rw [spMap_trans, Category.assoc, hg, hψ]

theorem par_zero_iff {ι : Type} {m : ι → ℕ} {R K : Type} [CommRing R] [Field K] (a : R →+* K)
    (ha : Function.Injective a) (O : Subring K) (hO : ∀ x, x ∈ O ↔ ∃ r, a r = x) (P : Mat m K) :
    Par 0 O P ↔ ∃ G : Mat m R, (∀ τ, IsUnit (G τ).det) ∧ P = G.map a := by
  constructor
  · intro hP
    have hent : ∀ τ i j, ∃ r, a r = P τ i j := fun τ i j => (hO _).1 ((hP τ).1 i j)
    choose G₀ hG using hent
    let G : Mat m R := fun τ => Matrix.of (G₀ τ)
    have hGP : P = G.map a := by
      funext τ i j
      exact (hG τ i j).symm
    refine ⟨G, fun τ => ?_, hGP⟩
    obtain ⟨s, hs⟩ := (hO _).1 (hP τ).2.2.1
    have hdet : a (G τ).det = (P τ).det := by
      rw [hGP]
      exact RingHom.map_det a (G τ)
    refine isUnit_iff_exists_inv.2 ⟨s, ha ?_⟩
    rw [map_mul, hdet, hs, map_one, mul_inv_cancel₀ (hP τ).2.1]
  · rintro ⟨G, hG, rfl⟩ τ
    have hdet : (G.map a τ).det = a (G τ).det := (RingHom.map_det a (G τ)).symm
    obtain ⟨u, hu⟩ := hG τ
    refine ⟨fun i j => (hO _).2 ⟨G τ i j, rfl⟩, ?_, ?_, fun i j hi _ => absurd hi (Nat.not_lt_zero _)⟩
    · rw [hdet, ← hu]
      exact (u.isUnit.map a).ne_zero
    · rw [hdet, ← hu]
      exact (hO _).2 ⟨((u⁻¹ : Rˣ) : R), by rw [map_units_inv]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem frames_iff {R R₁ K : Type} [CommRing R] [CommRing R₁] [IsLocalRing R₁] [Field K] {φ : c.F →+* R}
    {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) (hf : f.Stable) (ψ : R →+* R₁) (a : R₁ →+* K) (ha : Function.Injective a)
    {x₁ : Sp R₁ ⟶ Z.X} (hx : x₁ = spMap ψ ≫ x) {φ₀ : c.F →+* K} {x₀ : Sp K ⟶ Z.X} (f₀ : EigFrame Z φ₀ x₀)
    {T : Mat Dw.mult K} (hT : f.Coord (a.comp ψ) f₀ T) (A : Mat Dw.mult K) :
    ((∀ τ, (A τ).det ≠ 0) ∧ ∃ (φ₁ : c.F →+* R₁) (g : EigFrame Z φ₁ x₁), g.Coord a f₀ A⁻¹) ↔
      ∃ G : Mat Dw.mult R₁, (∀ τ, IsUnit (G τ).det) ∧ A * T = G.map a := by
  have hU := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z R φ x f K φ₀ x₀ (a.comp ψ) inferInstance hf hT.1 hT.2.1).1 f₀
  have huniq : ∀ B, f.Coord (a.comp ψ) f₀ B → B = T := fun B hB => hU.1.unique hB hT
  constructor
  · rintro ⟨hA, φ₁, g, hg⟩
    have hφ₁ : φ₁ = ψ.comp φ := by
      apply RingHom.ext
      intro r
      apply ha
      have h := RingHom.congr_fun (hg.2.1.symm.trans hT.2.1) r
      simpa using h
    subst hφ₁
    obtain ⟨hE, hunits⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z R φ x f R₁ (ψ.comp φ) x₁ ψ inferInstance hf hx rfl).1 g
    obtain ⟨G, hG, -⟩ := hE
    refine ⟨G, hunits G hG, ?_⟩
    have hc := _root_.GlobalTheory.ShFam.CoordComp.coord_comp E H Dw l Xo c O β Z R φ x f R₁ (ψ.comp φ) x₁ g K φ₀ x₀ f₀ ψ a G A⁻¹ inferInstance hG hg
    rw [← huniq _ hc, ← mul_assoc, Mat.mul_inv hA, one_mul]
  · rintro ⟨G, hG, hAT⟩
    obtain ⟨g, hfg⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z R φ x f R₁ (ψ.comp φ) x₁ ψ inferInstance hf hx rfl).2 G hG
    have hgs : g.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z R₁ (ψ.comp φ) x₁ g inferInstance
    have hx₀ : x₀ = spMap a ≫ x₁ := by rw [hT.1, hx, spMap_trans, Category.assoc]
    have hφ₀ : φ₀ = a.comp (ψ.comp φ) := hT.2.1.trans (RingHom.comp_assoc _ _ _)
    obtain ⟨⟨B, hB, -⟩, -⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z R₁ (ψ.comp φ) x₁ g K φ₀ x₀ a inferInstance hgs hx₀ hφ₀).1 f₀
    have hc := _root_.GlobalTheory.ShFam.CoordComp.coord_comp E H Dw l Xo c O β Z R φ x f R₁ (ψ.comp φ) x₁ g K φ₀ x₀ f₀ ψ a G B inferInstance hfg hB
    have hTB : B * G.map a = T := huniq _ hc
    have hGd : ∀ τ, (G.map a τ).det ≠ 0 := fun τ => by
      have h := ((hG τ).map a).ne_zero
      rw [RingHom.map_det] at h
      exact h
    have hAB : A * B = 1 := by
      calc A * B = A * B * (G.map a * (G.map a)⁻¹) := by rw [Mat.mul_inv hGd, mul_one]
      _ = A * (B * G.map a) * (G.map a)⁻¹ := by simp only [mul_assoc]
      _ = 1 := by rw [hTB, hAT, Mat.mul_inv hGd]
    have hAτ : ∀ τ, A τ * B τ = 1 := fun τ => congrFun hAB τ
    have hAd : ∀ τ, (A τ).det ≠ 0 := fun τ hd => by
      have h := congrArg Matrix.det (hAτ τ)
      rw [Matrix.det_mul, hd, zero_mul, Matrix.det_one] at h
      exact zero_ne_one h
    have hAi : A⁻¹ = B := funext fun τ => Matrix.inv_eq_right_inv (hAτ τ)
    refine ⟨hAd, ψ.comp φ, g, ?_⟩
    rw [hAi]
    exact hB

variable {F : Type} [Field F]

theorem genericPt_eq (B : GlobalTheory.ProjVar.Var F) (y : B.X) :
    genericPt B = spMap (algebraMap (B.X.presheaf.stalk y) B.X.functionField) ≫ stalkPt B y := by
  unfold genericPt stalkPt
  rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)]
  rfl

theorem genericPt_str (e : F ≃+* c.F) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z)
    (hj : j ≫ genStr Z ≫ spMap e.toRingHom = B.str) : (genericPt B ≫ j) ≫ genStr Z = spMap (constF e B) := by
  have hs : genericPt B ≫ B.str = spMap (algebraMap F B.Fn) := by
    apply ext_of_isAffine
    unfold genericPt spMap
    rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, ← cancel_mono (Scheme.ΓSpecIso _).hom,
      Scheme.ΓSpecIso_naturality]
    ext a
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
    rw [IsScalarTower.algebraMap_apply F Γ(B.X, ⊤) B.Fn, GlobalTheory.ProjVar.Var.algebraMap_Γ,
      GlobalTheory.Cartier.CartierDiv.algebraMap_top, CommRingCat.inv_hom_apply]
    have hmap : (Spec (B.X.presheaf.stalk (genericPoint B.X))).presheaf.map
        (homOfLE (le_top : (⊤ : (Spec (B.X.presheaf.stalk (genericPoint B.X))).Opens) ≤ ⊤)).op = 𝟙 _ := by
      rw [show (homOfLE (le_top : (⊤ : (Spec (B.X.presheaf.stalk (genericPoint B.X))).Opens) ≤ ⊤)) = 𝟙 _ from rfl]
      exact CategoryTheory.Functor.map_id _ _
    rw [hmap, CommRingCat.hom_id, RingHom.id_apply]
    exact CommRingCat.hom_inv_apply _ _
  have hid : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
    rw [← spMap_trans, RingEquiv.toRingHom_comp_symm_toRingHom]
    simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]
  unfold constF
  rw [spMap_trans, ← hs, ← hj]
  simp only [Category.assoc, hid, Category.comp_id]

def fam (e : F ≃+* c.F) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z)
    (hj : j ≫ genStr Z ≫ spMap e.toRingHom = B.str) (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) :
    Fr (ratOf B) Dw.mult 0 where
  S (y : B.X) := {A | (∀ τ, (A τ).det ≠ 0) ∧ ∃ (φ : c.F →+* B.X.presheaf.stalk y)
    (f : EigFrame Z φ (stalkPt B y ≫ j ≫ genι Z)),
    f.Coord (algebraMap (B.X.presheaf.stalk y) B.X.functionField) f₀ A⁻¹}
  loc (z : B.X) := by
    obtain ⟨U, hU, φ, f, hz, hφ, hf⟩ := _root_.GlobalTheory.ShFam.EigSpread.exists_stable_eigFrame E H Dw l Xo c O β Z (j z)
    have key : ∀ y : B.X, j y ∈ U → ∃ ψ : Γ(gen Z, U) →+* B.X.presheaf.stalk y,
        spMap ψ ≫ hU.fromSpec = stalkPt B y ≫ j := fun y hy =>
      exists_affine_factor _ hU (by
        show j (B.X.fromSpecStalk y (IsLocalRing.closedPoint _)) ∈ U
        rw [Scheme.fromSpecStalk_closedPoint]; exact hy)
    have key' : ∀ (y : B.X) (ψ : Γ(gen Z, U) →+* B.X.presheaf.stalk y), spMap ψ ≫ hU.fromSpec = stalkPt B y ≫ j →
        spMap ((algebraMap (B.X.presheaf.stalk y) B.X.functionField).comp ψ) ≫ hU.fromSpec = genericPt B ≫ j :=
      fun y ψ h => by rw [spMap_trans, Category.assoc, h, genericPt_eq B y, Category.assoc]
    obtain ⟨ψ₀, hψ₀⟩ := key z hz
    have h₀ := key' z ψ₀ hψ₀
    obtain ⟨⟨T, hT, -⟩, hu⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ φ _ f B.Fn (constF e B) (genericPt B ≫ j ≫ genι Z)
      ((algebraMap (B.X.presheaf.stalk z) B.X.functionField).comp ψ₀) inferInstance hf
      (by rw [← Category.assoc, ← h₀, Category.assoc])
      (EigLoc.spMap_inj (by rw [← genericPt_str e B j hj, ← h₀, Category.assoc, hφ, ← spMap_trans]))).1 f₀
    have hTd : ∀ τ, (T τ).det ≠ 0 := fun τ => (hu T hT τ).ne_zero
    refine ⟨j ⁻¹ᵁ U, T⁻¹, hz, fun τ => ?_, fun (y : B.X) hy A => ?_⟩
    · exact (Matrix.isUnit_det_of_right_inverse (congrFun (Mat.inv_mul hTd) τ)).ne_zero
    · obtain ⟨ψ, hψ⟩ := key y hy
      have e1 : (algebraMap (B.X.presheaf.stalk z) B.X.functionField).comp ψ₀ =
          (algebraMap (B.X.presheaf.stalk y) B.X.functionField).comp ψ :=
        EigLoc.spMap_inj ((cancel_mono hU.fromSpec).1 (h₀.trans (key' y ψ hψ).symm))
      rw [e1] at hT
      have ha : Function.Injective (algebraMap (B.X.presheaf.stalk y) B.X.functionField) :=
        IsFractionRing.injective _ _
      rw [Mat.inv_inv hTd]
      refine (frames_iff f hf ψ _ ha (by rw [← Category.assoc, ← hψ, Category.assoc]) f₀ hT A).trans
        (par_zero_iff _ ha _ (fun x => mem_O_ratOf (Y := B) (y := y) (g := x)) _).symm

end GlobalTheory.ShFam.TieBase


open GlobalTheory.ShFam.TieBase in
theorem GlobalTheory.ShFam.TieBase.exists_tied : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z), j ≫ genStr Z ≫ spMap e.toRingHom = B.str → ∃ (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn), Tied e B j f₀ S A₀ := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e B j hj
  have hx : (genericPt B ≫ j) ≫ genι Z = genericPt B ≫ j ≫ genι Z := Category.assoc _ _ _
  obtain ⟨f₀⟩ : Nonempty (EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) := by
    rw [← hx]
    exact EigLoc.exists_eigFrame E H Dw l Xo c O β Z B.Fn (constF e B) (genericPt B ≫ j) (genericPt_str e B j hj)
  refine ⟨f₀, fam e B j hj f₀, 1, ?_⟩
  unfold GlobalTheory.ShFam.Tied
  refine ⟨?_, ?_⟩
  · have hst : f₀.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z B.Fn (constF e B) _ f₀ inferInstance
    have hsp : spMap (RingHom.id B.Fn) = 𝟙 _ := by simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]
    obtain ⟨⟨A₁, hA₁, huq⟩, hu⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z B.Fn (constF e B) _ f₀ B.Fn (constF e B) _
      (RingHom.id B.Fn) inferInstance hst (by rw [hsp, Category.id_comp]) (RingHom.id_comp _).symm).1 f₀
    have h2 := _root_.GlobalTheory.ShFam.CoordComp.coord_comp E H Dw l Xo c O β Z B.Fn (constF e B) _ f₀ B.Fn (constF e B) _ f₀ B.Fn (constF e B) _ f₀
      (RingHom.id B.Fn) (RingHom.id B.Fn) A₁ A₁ inferInstance hA₁ hA₁
    have hm : A₁.map (RingHom.id B.Fn) = A₁ := by
      funext τ i j
      rfl
    rw [RingHom.id_comp, hm] at h2
    have hsq : A₁ * A₁ = A₁ := huq _ h2
    have hdet : ∀ τ, (A₁ τ).det ≠ 0 := fun τ => (hu A₁ hA₁ τ).ne_zero
    have h1 : A₁ = 1 := by
      calc A₁ = A₁⁻¹ * (A₁ * A₁) := by rw [← mul_assoc, Mat.inv_mul hdet, one_mul]
      _ = 1 := by rw [hsq, Mat.inv_mul hdet]
    have hinv : (1 : Mat Dw.mult B.Fn)⁻¹ = 1 := funext fun τ => by simp
    have halg : @algebraMap (B.X.presheaf.stalk (genericPoint B.X)) B.X.functionField _ _
        (AlgebraicGeometry.stalkFunctionFieldAlgebra (X := B.X) (genericPoint B.X)) = RingHom.id _ := by
      ext r
      show (B.X.presheaf.stalkSpecializes _).hom r = r
      rw [TopCat.Presheaf.stalkSpecializes_refl]
      rfl
    show (∀ τ, ((1 : Mat Dw.mult B.Fn) τ).det ≠ 0) ∧ ∃ (φ : c.F →+* B.X.presheaf.stalk (genericPoint B.X))
      (f : EigFrame Z φ (stalkPt B (genericPoint B.X) ≫ j ≫ genι Z)),
      f.Coord (@algebraMap (B.X.presheaf.stalk (genericPoint B.X)) B.X.functionField _ _
        (AlgebraicGeometry.stalkFunctionFieldAlgebra (X := B.X) (genericPoint B.X))) f₀ (1 : Mat Dw.mult B.Fn)⁻¹
    refine ⟨fun τ => by simp, constF e B, f₀, ?_⟩
    rw [halg, hinv, ← h1]
    exact hA₁
  · intro y A hA
    have hA' : (∀ τ, (A τ).det ≠ 0) ∧ ∃ (φ : c.F →+* B.X.presheaf.stalk y)
        (f : EigFrame Z φ (stalkPt B y ≫ j ≫ genι Z)),
        f.Coord (algebraMap (B.X.presheaf.stalk y) B.X.functionField) f₀ A⁻¹ := hA
    obtain ⟨-, φ, f, hf⟩ := hA'
    exact ⟨φ, f, by rw [one_mul]; exact hf⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEquationComplexPoints
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.HolFrames

section Hol

open GlobalTheory.Points

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {B : Set V} {T : Scheme.{0}}

theorem holTan_of_affine {U : T.Opens} (hU : IsAffineOpen U) (hB : IsOpen B) {z : V → (Sp (DualNumber ℂ) ⟶ T)}
    (hz : ∀ b ∈ B, ⊤ ≤ z b ⁻¹ᵁ U)
    (h₁ : ∀ a : Γ(T, U), DifferentiableOn ℂ (fun b => (valR (A := DualNumber ℂ) (z b) U a).fst) B)
    (h₂ : ∀ a : Γ(T, U), DifferentiableOn ℂ (fun b => (valR (A := DualNumber ℂ) (z b) U a).snd) B) : HolTan B z := by
  intro W f v hv
  refine DifferentiableAt.differentiableWithinAt ?_
  obtain ⟨h, hhW, hh⟩ := hU.exists_basicOpen_le (V := W) ⟨_, (le_preimage_iff _ _).1 hv.2⟩
    ((le_preimage_iff _ _).1 (hz v hv.1))
  have key : ∀ b ∈ B, ⊤ ≤ z b ⁻¹ᵁ T.basicOpen h ↔ (valR (A := DualNumber ℂ) (z b) U h).fst ≠ 0 := fun b hb =>
    (le_preimage_basicOpen_iff _ (hz b hb) h).trans (TrivSqZeroExt.isUnit_iff_isUnit_fst.trans isUnit_iff_ne_zero)
  have hv0 := (key v hv.1).1 ((le_preimage_iff _ _).2 hh)
  have := hU.isLocalization_basicOpen h
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj h ((T.presheaf.map (homOfLE hhW).op).hom f)
  have d₁ := fun a => (h₁ a).differentiableAt (hB.mem_nhds hv.1)
  have d₂ := fun a => (h₂ a).differentiableAt (hB.mem_nhds hv.1)
  have nz : ∀ b ∈ B, (valR (A := DualNumber ℂ) (z b) U h).fst ≠ 0 →
      (valR (A := DualNumber ℂ) (z b) U (h ^ n)).fst ≠ 0 := fun b hb h0 => by
    rw [valR_pow _ _ (hz b hb), TrivSqZeroExt.fst_pow]
    exact pow_ne_zero n h0
  have di := (d₁ (h ^ n)).inv (nz v hv.1 hv0)
  have hq := ((d₂ a).sub (((d₁ a).mul di).mul (d₂ (h ^ n)))).mul di
  refine hq.congr_of_eventuallyEq ?_
  filter_upwards [hB.mem_nhds hv.1, (d₁ h).continuousAt.eventually_ne hv0] with w hw hw0
  have hw1 := (key w hw).2 hw0
  have ha' : (T.presheaf.map (homOfLE hhW).op).hom f * (T.presheaf.map (homOfLE (T.basicOpen_le h)).op).hom h ^ n =
    (T.presheaf.map (homOfLE (T.basicOpen_le h)).op).hom a := ha
  have e := congrArg (valR (z w) (T.basicOpen h)) ha'
  rw [← map_pow, valR_mul _ _ hw1, valR_res _ _ hw1, valR_res _ _ hw1, valR_res _ _ hw1] at e
  have e₁ := congrArg TrivSqZeroExt.fst e
  have e₂ := congrArg TrivSqZeroExt.snd e
  rw [TrivSqZeroExt.fst_mul] at e₁
  rw [DualNumber.snd_mul] at e₂
  have := nz w hw hw0
  simp only [Pi.inv_apply, Pi.sub_apply, Pi.mul_apply]
  rw [← e₁, ← e₂]
  field_simp
  ring

theorem holTan_dualMap {A : Type} [CommRing A] (hB : IsOpen B) (v : Sp (DualNumber A) ⟶ T) (ψ : ∀ b ∈ B, A →+* ℂ)
    (hψ : ∀ a, ∃ g : V → ℂ, DifferentiableOn ℂ g B ∧ ∀ b hb, ψ b hb a = g b) {w : V → (Sp (DualNumber ℂ) ⟶ T)}
    (hw : ∀ b hb, w b = spMap (dualMap (ψ b hb)) ≫ v) : HolTan B w := by
  classical
  by_cases hne : B.Nonempty
  swap
  · intro U f b hb
    exact (hne ⟨b, hb.1⟩).elim
  obtain ⟨b₀, hb₀⟩ := hne
  let ψ' : V → (A →+* ℂ) := fun b => if hb : b ∈ B then ψ b hb else ψ b₀ hb₀
  have e : ∀ b hb, ψ' b = ψ b hb := fun b hb => dite_eq_left hb
  have hd : ∀ a, DifferentiableOn ℂ (fun b => ψ' b a) B := fun a =>
    have ⟨g, hg, hg'⟩ := hψ a
    hg.congr fun b hb => by rw [e b hb, hg']
  have hv : ∀ b (a : DualNumber A), valR (spMap (dualMap (ψ' b))) ⊤
      ((Scheme.ΓSpecIso (.of (DualNumber A))).inv.hom a) = dualMap (ψ' b) a := fun b a =>
    valR_specMap (CommRingCat.ofHom (dualMap (ψ' b))) a
  have hs : ∀ s : Γ(Sp (DualNumber A), ⊤), ∃ a, (Scheme.ΓSpecIso (.of (DualNumber A))).inv.hom a = s := fun s =>
    ⟨(Scheme.ΓSpecIso (.of (DualNumber A))).hom.hom s, by simp⟩
  have h0 : HolTan B fun b => spMap (dualMap (ψ' b)) :=
    holTan_of_affine (isAffineOpen_top _) hB (fun b _ => le_preimage_top _)
      (fun s => by obtain ⟨a, rfl⟩ := hs s; simp only [hv]; simpa [dualMap] using hd a.fst)
      (fun s => by obtain ⟨a, rfl⟩ := hs s; simp only [hv]; simpa [dualMap] using hd a.snd)
  intro U f
  refine ((h0 (v ⁻¹ᵁ U) ((v.app U).hom f)).mono (s := {b ∈ B | ⊤ ≤ w b ⁻¹ᵁ U}) fun b hb => ⟨hb.1, ?_⟩).congr fun b hb => ?_
  · have := hb.2
    rw [hw b hb.1, ← e b hb.1] at this
    exact this
  · rw [hw b hb.1, ← e b hb.1, valR_comp]

theorem valR_eq_germ {C : Type} [CommRing C] [IsLocalRing C] (p : Sp C ⟶ T) (U : T.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) :
    valMap p U h = T.presheaf.germ U _ ((le_preimage_iff p U).1 h) ≫ Scheme.stalkClosedPointTo (R := .of C) p := by
  rw [Scheme.germ_stalkClosedPointTo]
  rfl

end Hol

section Expo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)


end Expo

section Frames

open GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc GlobalTheory.ShFam.CoordUniq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem exists_bc {A B : Type} [CommRing A] [CommRing B] {φ : c.F →+* A} {x : Sp A ⟶ Z.X} (fr : EigFrame Z φ x)
    (ψ : A →+* B) {φ' : c.F →+* B} {x' : Sp B ⟶ Z.X} (hφ : φ' = ψ.comp φ) (hx : x' = spMap ψ ≫ x) :
    ∃ g : EigFrame Z φ' x', ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ fr.v τ i := by
  subst hφ hx
  obtain ⟨g, hg⟩ := GlobalTheory.ShFam.Spread.exists_bc fr ψ rfl rfl
  exact ⟨g, fun τ i => congrArg (fun v => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left) (hg τ i)⟩

theorem spMap_comp₂ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

end Frames


end GlobalTheory.ShFam.HolFrames
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsScfEmbeddingDvd
section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Pad.Pull

open Cardinal

theorem exists_scf_embedding_dvd :
    ∀ (p : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], p.Prime → (p : V) ∈ IsLocalRing.maximalIdeal V → Cardinal.mk V ≤ Cardinal.continuum → ∃ (C : SCF p) (φ : V →+* ↥(intO ↥C.S)), Function.Injective φ ∧ ∀ a b : V, ‖((φ a : ↥(intO ↥C.S)) : ↥C.S)‖ ≤ ‖((φ b : ↥(intO ↥C.S)) : ↥C.S)‖ → b ∣ a := by
  intro p V _ _ _ _ hp hpm hV
  let K := FractionRing V
  have hp0 : (p : V) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  obtain ⟨C, _, _, _, _, _, hC, hCp⟩ :=
    GlobalTheory.exists_complete_isAlgClosed_of_isDiscreteValuationRing V K hp0 hpm
      (inv_pos.2 (zero_lt_one.trans h1)) (inv_lt_one_of_one_lt₀ h1)
  have hK : #K ≤ 𝔠 :=
    (IsLocalization.cardinalMk_le (nonZeroDivisors V)).trans hV
  have hx : 1 < ‖algebraMap K C (algebraMap V K p)⁻¹‖ := by
    rw [map_inv₀, norm_inv, hCp, inv_inv]; exact h1
  obtain ⟨L, hKL, hcl, hac, hL⟩ := GlobalTheory.SmallClosedField.exists_small_closed_subfield hK hx
  letI : NontriviallyNormedField L :=
    { (inferInstance : NormedField L) with non_trivial := ⟨⟨_, hKL _⟩, hx⟩ }
  haveI : CompleteSpace L := hcl.completeSpace_coe
  haveI : CharZero K := charZero_of_injective_ringHom (IsFractionRing.injective V K)
  let i : K →+* L := (algebraMap K C).codRestrict L hKL
  have hi : ∀ y, ‖i y‖ = ‖algebraMap K C y‖ := fun _ => rfl
  haveI : CharZero L := charZero_of_injective_ringHom i.injective
  have hLp : ‖(p : L)‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast i, hi, ← map_natCast (algebraMap V K), hCp]
  obtain ⟨D, e, he⟩ := GlobalTheory.SmallClosedField.exists_scf_isometry hLp hL
  let g : V →+* D.S := (e.comp i).comp (algebraMap V K)
  have hg : ∀ a : V, ‖g a‖ = ‖algebraMap K C (algebraMap V K a)‖ := fun a => by
    simp only [g, RingHom.comp_apply, he, hi]
  have hle : ∀ a : V, g a ∈ intO D.S := fun a => by
    change ‖g a‖ ≤ 1
    rw [hg]; exact (hC _).2 ⟨a, rfl⟩
  refine ⟨D, g.codRestrict _ hle, fun a b hab => ?_, fun a b hab => ?_⟩
  · have h := congrArg Subtype.val hab
    exact IsFractionRing.injective V K (i.injective (e.injective h))
  · change ‖g a‖ ≤ ‖g b‖ at hab
    rw [hg, hg] at hab
    by_cases hb : b = 0
    · subst hb
      have : algebraMap K C (algebraMap V K a) = 0 := by
        rw [map_zero, map_zero, norm_zero] at hab
        exact norm_le_zero_iff.1 hab
      rw [(map_eq_zero_iff _ (algebraMap K C).injective).1 this |>
        (map_eq_zero_iff _ (IsFractionRing.injective V K)).1]
    · have hb' : algebraMap V K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 hb
      have hbC : 0 < ‖algebraMap K C (algebraMap V K b)‖ :=
        norm_pos_iff.2 ((map_ne_zero_iff _ (algebraMap K C).injective).2 hb')
      obtain ⟨c, hc⟩ := (hC (algebraMap V K a / algebraMap V K b)).1 (by
        rw [map_div₀, norm_div]; exact div_le_one_of_le₀ hab hbC.le)
      refine ⟨c, IsFractionRing.injective V K ?_⟩
      rw [map_mul, hc, mul_div_cancel₀ _ hb']

end GlobalTheory.ShFam.Pad.Pull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCoefficientEqWeightRatio
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FramePairGram

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramePairGram

theorem coef_eq_coW_change {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ}
    (hj : j ≤ r) (hp : X.p0 = r - j) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom) (hx' : x' ∈ X.dom) (τ : X.Ψ)
    (h : moeb (frameCo X hj x τ) 0 = moeb (frameCo X hj x' τ) 0) :
    (Matrix.of fun b i : Fin j => coef X x x' τ.1 b i) = (coW X hj x' τ)⁻¹ * coW X hj x τ := by
  have hd' : IsUnit (mat x' τ).det := (hx' τ).1.isUnit
  have hN : frameCo X hj x τ = frameCo X hj x' τ * reindex (idx hj) (idx hj) ((mat x' τ)⁻¹ * mat x τ) := by
    simp only [frameCo, reindex_apply, submatrix_mul_equiv]
    rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hd']
  have hu' := frameCo_isUnit₂₂ X hj hp hx' τ
  have hW : coW X hj x τ = coW X hj x' τ * (reindex (idx hj) (idx hj) ((mat x' τ)⁻¹ * mat x τ)).toBlocks₁₁ := by
    unfold coW
    rw [h, hN, moeb_zero]
    generalize frameCo X hj x' τ = g at *
    generalize reindex (idx hj) (idx hj) ((mat x' τ)⁻¹ * mat x τ) = N
    have e11 : (g * N).toBlocks₁₁ = g.toBlocks₁₁ * N.toBlocks₁₁ + g.toBlocks₁₂ * N.toBlocks₂₁ := by
      conv_lhs => rw [← fromBlocks_toBlocks g, ← fromBlocks_toBlocks N]
      rw [fromBlocks_multiply, toBlocks_fromBlocks₁₁]
    have e21 : (g * N).toBlocks₂₁ = g.toBlocks₂₁ * N.toBlocks₁₁ + g.toBlocks₂₂ * N.toBlocks₂₁ := by
      conv_lhs => rw [← fromBlocks_toBlocks g, ← fromBlocks_toBlocks N]
      rw [fromBlocks_multiply, toBlocks_fromBlocks₂₁]
    rw [e11, e21]
    simp only [Matrix.mul_add, Matrix.sub_mul, Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hu']
    abel
  rw [hW, ← Matrix.mul_assoc, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 ((isUnit_iff_isUnit_det _).2 (isUnit_coW X hj hp hx' τ))), Matrix.one_mul]
  ext b i
  have hb : X.p0 + (b : ℕ) < r := by have := b.2; have := X.p0_le; omega
  have hi : X.p0 + (i : ℕ) < r := by have := i.2; have := X.p0_le; omega
  have eb : (idx hj).symm (Sum.inl b) = ⟨X.p0 + b, hb⟩ := Fin.ext (by rw [idx_symm_inl]; show r - j + (b : ℕ) = X.p0 + b; omega)
  have ei : (idx hj).symm (Sum.inl i) = ⟨X.p0 + i, hi⟩ := Fin.ext (by rw [idx_symm_inl]; show r - j + (i : ℕ) = X.p0 + i; omega)
  simp only [of_apply, coef, dif_pos τ.2, ent, dif_pos (And.intro hb hi), Subtype.coe_eta, toBlocks₁₁, reindex_apply,
    submatrix_apply, eb, ei]

end GlobalTheory.FramePairGram
end
end

