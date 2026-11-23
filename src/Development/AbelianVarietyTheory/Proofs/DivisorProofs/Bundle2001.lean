module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullG
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1953
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaEqOfMkEq
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
set_option autoImplicit false
noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TorsSpec

def ValAt {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) {V : Scheme.{0}} (ℓ : V ⟶ X') {M : Type}
    (w : M → (V ⟶ G.left)) (p : (torsion G n).left) (c : M) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (y : Sp Ω ⟶ Spec ((torsion G n).left.presheaf.stalk p)) (z : Sp Ω ⟶ V),
    y ≫ (torsion G n).left.fromSpecStalk p ≫ (torsion G n).hom = z ≫ ℓ →
      y ≫ (torsion G n).left.fromSpecStalk p ≫ (torsion.ι G n).left = z ≫ w c

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem etaSec_w (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X')
    (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (b : Dw.La) :
    (i₀ TF.Y Z ≫ (TF.Y.oF.eta b).left ≫ TF.Y.m.φ) ≫ TF.Y.t.G.hom = ℓ ≫ φ ≫ (barComp TF.Y Z).ι := by
  have h1 := TF.Y.m.cart.1.w
  have h2 := Over.w (TF.Y.oF.eta b)
  simp only [Category.assoc] at h1 ⊢
  rw [h1, ← Category.assoc ((TF.Y.oF.eta b).left), h2, reassoc_of% hℓ, j₀_ι]
  exact congrArg (i₀ TF.Y Z ≫ ·) (Category.id_comp _)

def etaSec (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X')
    (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (b : Dw.La) : V₀ TF.Y Z ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left :=
  pullback.lift _ _ (etaSec_w TF Z φ ℓ hℓ b)

theorem eta_eq_of_mk_eq (TF : TorFlag Xo c) {b b' : Dw.La}
    (h : (Submodule.Quotient.mk b : LevelMod Dw l) = Submodule.Quotient.mk b') :
    TF.Y.oF.eta b = TF.Y.oF.eta b' := by
  rw [Submodule.Quotient.eq] at h
  have := TF.Y.oF.eta_add b' (b - b')
  rwa [add_sub_cancel, TF.Y.oF.eta_ker _ h, mul_one] at this

def etaSecL (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X')
    (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (x : LevelMod Dw l) : V₀ TF.Y Z ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left :=
  Quot.liftOn x (etaSec TF Z φ ℓ hℓ) fun b b' h => by
    have e := eta_eq_of_mk_eq TF (b := b) (b' := b') (Quot.sound h)
    unfold etaSec
    congr 2
    rw [e]

theorem etaSecL_w (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X')
    (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (x : LevelMod Dw l) :
    etaSecL TF Z φ ℓ hℓ x ≫ (GlobalTheory.EqvAct.pullG TF Z φ).hom = ℓ := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact pullback.lift_snd _ _ _

theorem etaSecL_ψ (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X')
    (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (b : Dw.La) :
    etaSecL TF Z φ ℓ hℓ (Submodule.Quotient.mk b) ≫ GlobalTheory.EqvAct.pullψ TF Z φ =
      i₀ TF.Y Z ≫ (TF.Y.oF.eta b).left ≫ TF.Y.m.φ :=
  pullback.lift_fst _ _ _

end GlobalTheory.TorsSpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMvPolynomialEval2HomRestrictSmallerAffines
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.EtaleRestrict

theorem etale_eval₂_res : ∀ (X Y : Scheme.{0}) (q : Y ⟶ X) (ι : Type) (U U' : X.Opens) (hU' : U' ≤ U), IsAffineOpen U → IsAffineOpen U' → ∀ (W W' : Y.Opens) (hW' : W' ≤ W), IsAffineOpen W → IsAffineOpen W' → ∀ (hWU : W ≤ q ⁻¹ᵁ U) (hW'U' : W' ≤ q ⁻¹ᵁ U') (N : ι → Γ(Y, W)), (MvPolynomial.eval₂Hom (q.appLE U W hWU).hom N).Etale → (MvPolynomial.eval₂Hom (q.appLE U' W' hW'U').hom (fun a ↦ resG Y hW' (N a))).Etale := by
  intro X Y q ι U U' hU' hU hU'a W W' hW' hW hW'a hWU hW'U' N hN
  have h1 : (resG Y hW').Etale := GlobalTheory.TopForm.etale_resG hW hW'a hW'
  have h2 : ((resG Y hW').comp (MvPolynomial.eval₂Hom (q.appLE U W hWU).hom N)).Etale :=
    RingHom.Etale.stableUnderComposition _ _ hN h1
  have h3 : (resG X hU').Etale := GlobalTheory.TopForm.etale_resG hU hU'a hU'
  have h4 : (MvPolynomial.map (σ := ι) (resG X hU')).Etale := by
    algebraize [resG X hU']
    letI := MvPolynomial.algebraMvPolynomial (σ := ι) (R := Γ(X, U)) (S := Γ(X, U'))
    exact RingHom.Etale.isStableUnderBaseChange Γ(X, U) Γ(X, U') (MvPolynomial ι Γ(X, U)) (MvPolynomial ι Γ(X, U')) h3
  have h5 : (MvPolynomial.eval₂Hom (q.appLE U' W' hW'U').hom (fun a ↦ resG Y hW' (N a))).comp
      (MvPolynomial.map (resG X hU')) = (resG Y hW').comp (MvPolynomial.eval₂Hom (q.appLE U W hWU).hom N) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.map_C, MvPolynomial.eval₂Hom_C]
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE,
        ← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
    · intro i
      simp
  rw [← h5] at h2
  algebraize [MvPolynomial.map (σ := ι) (resG X hU'),
    MvPolynomial.eval₂Hom (q.appLE U' W' hW'U').hom (fun a ↦ resG Y hW' (N a)),
    (MvPolynomial.eval₂Hom (q.appLE U' W' hW'U').hom (fun a ↦ resG Y hW' (N a))).comp
      (MvPolynomial.map (resG X hU'))]
  exact Algebra.Etale.of_restrictScalars (R := MvPolynomial ι Γ(X, U)) _ _

end GlobalTheory.EtaleRestrict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfFormallyUnramifiedStandardSmoothSameRelDi
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem etale_of_formallyUnramified_of_relDim : ∀ (A B C : Type) [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (g : ℕ),
    Algebra.IsStandardSmoothOfRelativeDimension g A B →
    Algebra.IsStandardSmoothOfRelativeDimension g A C →
    Algebra.FormallyUnramified B C → Algebra.Etale B C := by
  intro A B C _ _ _ _ _ _ _ g hB hC hU
  have : Algebra.IsStandardSmooth A B := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have : Algebra.IsStandardSmooth A C := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have hs : Function.Surjective (KaehlerDifferential.mapBaseChange A B C) := fun x =>
    (KaehlerDifferential.exact_mapBaseChange_map A B C x).mp (Subsingleton.elim _ _)
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange A B C) := by
    rcases subsingleton_or_nontrivial C with hC0 | hC0
    · intro x y _
      exact Subsingleton.elim (α := TensorProduct B C Ω[B⁄A]) x y
    · have : Nontrivial B := (algebraMap B C).domain_nontrivial
      have : Module.Free B Ω[B⁄A] := Algebra.IsStandardSmooth.free_kaehlerDifferential
      have : Module.Free C Ω[C⁄A] := Algebra.IsStandardSmooth.free_kaehlerDifferential
      have hr : Module.rank C Ω[C⁄A] = Module.rank C (TensorProduct B C Ω[B⁄A]) := by
        rw [Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential g, Module.rank_baseChange,
          Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential g]
        simp
      obtain ⟨e⟩ := nonempty_linearEquiv_of_rank_eq hr
      have h2 : Function.Surjective (e.toLinearMap ∘ₗ KaehlerDifferential.mapBaseChange A B C) :=
        e.surjective.comp hs
      have h3 := OrzechProperty.injective_of_surjective_endomorphism _ h2
      exact fun x y hxy => h3 (by simp [hxy])
  have : Algebra.FormallySmooth B C := by
    rw [Algebra.formallySmooth_iff]
    constructor
    · exact Module.Projective.of_free
    · refine subsingleton_of_forall_eq 0 fun x => ?_
      have h₁ : Algebra.H1Cotangent.δ A B C x = 0 := by
        apply hinj
        rw [map_zero]
        exact (Algebra.H1Cotangent.exact_δ_mapBaseChange A B C).apply_apply_eq_zero x
      obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ A B C x).mp h₁
      rw [Subsingleton.elim y 0, map_zero]
  have : Algebra.FormallyEtale B C := Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth
  have : Algebra.FinitePresentation B C := Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A B C
  exact ⟨inferInstance, inferInstance⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffinePreimageLe
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Tube

theorem exists_affine_preimage_le :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S) [UniversallyClosed f] (s : S) (W : X.Opens), (∀ x, f x = s → x ∈ W) → ∃ U : S.Opens, IsAffineOpen U ∧ s ∈ U ∧ f ⁻¹ᵁ U ≤ W := by
  intro X S f _ s W hW
  have hc : IsClosed (f '' (W : Set X)ᶜ) := f.isClosedMap _ W.isOpen.isClosed_compl
  have hs : s ∈ (f '' (W : Set X)ᶜ)ᶜ := by
    rintro ⟨x, hx, rfl⟩
    exact hx (hW x rfl)
  obtain ⟨U, hU, hsU, hUV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
    (show s ∈ (⟨_, hc.isOpen_compl⟩ : S.Opens) from hs)
  refine ⟨U, hU, hsU, fun x hx => ?_⟩
  by_contra hxW
  exact hUV hx ⟨x, hxW, rfl⟩

end GlobalTheory.Tube
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenAffineOpenMeetingFibresGrpScheme
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.chartAroundUnit (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (s : Sp R) :
    ∃ f : R, s ∈ Set.range (spMap (algebraMap R (Localization.Away f))) ∧ ∃ W : A.left.Opens,
      IsAffineOpen W ∧ ∀ t ∈ Set.range (spMap (algebraMap R (Localization.Away f))),
        ∃ x ∈ W, A.hom x = t := by
  let e : Sp R ⟶ A.left := (η[A]).left
  have he : e ≫ A.hom = 𝟙 (Sp R) := Over.w (η[A])
  have hpt : ∀ t : Sp R, A.hom (e t) = t := by
    intro t
    rw [← Scheme.Hom.comp_apply, he]
    rfl
  obtain ⟨W, hW, hsW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := e s) trivial
  have hrange : ∀ f : R, Set.range (spMap (algebraMap R (Localization.Away f))) =
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
    intro f
    exact PrimeSpectrum.localization_away_comap_range (Localization.Away f) f
  have hopen : IsOpen (e ⁻¹' (W : Set A.left)) := W.isOpen.preimage e.continuous
  obtain ⟨_, ⟨f, rfl⟩, hsf, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open
      (a := s) hsW hopen
  refine ⟨f, ?_, W, hW, ?_⟩
  · rw [hrange]; exact hsf
  · intro t ht
    rw [hrange] at ht
    exact ⟨e t, hsub ht, hpt t⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenCellChoose
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem GlobalTheory.LogPole.exists_basicOpen_cell_choose : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J), W ≤ toBase TF Z ⁻¹ᵁ U.1 → W ≤ inc₀ TF.X Z ⁻¹ᵁ TF.X.F.U k → Nonempty W → ∃ a : Γ(TF.Y.X, U.1), TF.Y.X.basicOpen a ≤ LogKS.interior TF.Y ⊓ barComp TF.Y Z ⊓ (TF.X.F.M k).U ∧ ∃ w : Y₀ TF.X Z, w ∈ W ∧ w ∈ U₀ TF.X Z ∧ toBase TF Z w ∈ TF.Y.X.basicOpen a := by
  intro E _ _ _ H Dw l Xo c TF Z U W k hWU hWk hW
  obtain ⟨⟨w₁, hw₁⟩⟩ := hW
  obtain ⟨w, hwW, hw0⟩ := (dense_U₀ TF.X Z).inter_open_nonempty (W : Set (Y₀ TF.X Z)) W.isOpen ⟨w₁, hw₁⟩
  have hcomp : toBase TF Z w = TF.X.π w.1 := Scheme.Hom.comp_apply _ _ _
  have hU : toBase TF Z w ∈ U.1 := hWU hwW
  have hI : toBase TF Z w ∈ LogKS.interior TF.Y := by
    rw [hcomp]; exact hw0
  have hB : toBase TF Z w ∈ barComp TF.Y Z := by
    rw [hcomp]; exact w.2
  have hM : toBase TF Z w ∈ (TF.X.F.M k).U := by
    rw [hcomp]; exact TF.X.F.le k (hWk hwW)
  obtain ⟨a, ha, hxa⟩ := U.2.exists_basicOpen_le
    (V := LogKS.interior TF.Y ⊓ barComp TF.Y Z ⊓ (TF.X.F.M k).U) ⟨toBase TF Z w, ⟨⟨hI, hB⟩, hM⟩⟩ hU
  exact ⟨a, ha, w, hwW, hw0, hxa⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenTopFormFrameOfStalkKaehlerBasis
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.FrameSpread

open GlobalTheory.TopForm

theorem exists_basicOpen_isFrame_dOn : ∀ (k : Type) [Field k] (X : Scheme.{0}) (p : X ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n p] (U : X.affineOpens) (x₀ : X) (hx : x₀ ∈ U.1) (x : Fin n → Γ(X, U.1)), (letI := ((X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1)).toAlgebra; ∃ bs : Module.Basis (Fin n) (X.presheaf.stalk x₀) Ω[X.presheaf.stalk x₀⁄k], ∀ i, bs i = KaehlerDifferential.D k (X.presheaf.stalk x₀) ((X.presheaf.germ U.1 x₀ hx).hom (x i))) → ∃ s : Γ(X, U.1), x₀ ∈ X.basicOpen s ∧ GlobalTheory.TopForm.IsFrame (GlobalTheory.TopForm.dOn p fun i => resG X (X.basicOpen_le s) (x i)) := by
  intro k _ X p n _ U x₀ hx x hbs
  obtain ⟨V, ω, hxV, hω⟩ := TopForm.exists_isFrame p n x₀
  obtain ⟨s, hsV, hxs⟩ := U.2.exists_basicOpen_le ⟨x₀, hxV⟩ hx
  have hWU : X.basicOpen s ≤ U.1 := X.basicOpen_le s
  have hWaff : IsAffineOpen (X.basicOpen s) := U.2.basicOpen s
  have hωW := hω.res hWaff hsV
  set η : FormsOn p n (X.basicOpen s) := TopForm.dOn p (fun i => resG X hWU (x i)) with hη
  set J : Γ(X, X.basicOpen s) := hωW.gen.repr η with hJdef
  have hJ : J • TopForm.resForm hsV ω = η := hωW.gen.repr_smul η
  obtain ⟨bs, hbs⟩ := hbs
  set ρ : Γ(X, X.basicOpen s) →+* X.presheaf.stalk x₀ := (X.presheaf.germ (X.basicOpen s) x₀ hxs).hom with hρ
  have hgerm : ∀ a : Γ(X, U.1), ρ (resG X hWU a) = (X.presheaf.germ U.1 x₀ hx).hom a := fun a => by
    have := TopCat.Presheaf.germ_res X.presheaf (homOfLE hWU) x₀ hxs
    exact congrArg (fun φ => (ConcreteCategory.hom φ) a) this
  have hρα : ρ.comp (algX p (X.basicOpen s)) = (X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1) := by
    rw [← resG_comp_algX p hWU]
    ext a
    exact hgerm _
  have hfe : letI := ρ.toAlgebra; Algebra.FormallyEtale Γ(X, X.basicOpen s) (X.presheaf.stalk x₀) := by
    letI := ρ.toAlgebra
    haveI := hWaff.isLocalization_stalk ⟨x₀, hxs⟩
    exact Algebra.FormallyEtale.of_isLocalization (hWaff.primeIdealOf ⟨x₀, hxs⟩).asIdeal.primeCompl
  have h1 : IsFreeGen (X.presheaf.stalk x₀) (TopForm.formMap n ρ hρα (TopForm.resForm hsV ω)) := by
    letI := (algX p (X.basicOpen s)).toAlgebra
    letI := ((X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1)).toAlgebra
    letI := ρ.toAlgebra
    haveI : IsScalarTower k Γ(X, X.basicOpen s) (X.presheaf.stalk x₀) :=
      IsScalarTower.of_algebraMap_eq' hρα.symm
    haveI : Algebra.FormallyEtale Γ(X, X.basicOpen s) (X.presheaf.stalk x₀) := hfe
    exact hωW.gen.of_isBaseChange (isBaseChange_exteriorPower
      (KaehlerDifferential.isBaseChange_of_formallyEtale k Γ(X, X.basicOpen s) (X.presheaf.stalk x₀)) n)
  have h2 : IsFreeGen (X.presheaf.stalk x₀)
      (dForm ((X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1))
        (fun i => (X.presheaf.germ U.1 x₀ hx).hom (x i))) :=
    isFreeGen_dForm _ bs hbs
  have h3 : TopForm.formMap n ρ hρα η = ρ J • TopForm.formMap n ρ hρα (TopForm.resForm hsV ω) := by
    rw [← hJ, map_smulₛₗ]
  have h4 : TopForm.formMap n ρ hρα η = dForm ((X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1))
      (fun i => (X.presheaf.germ U.1 x₀ hx).hom (x i)) := by
    rw [hη, dOn, formMap_dForm]
    simp only [hgerm]
  have hu : IsUnit (ρ J) := h1.smul_iff.1 (h3 ▸ h4 ▸ h2)
  have hxJ : x₀ ∈ X.basicOpen J := (X.mem_basicOpen J x₀ hxs).2 hu
  obtain ⟨t, htJ, hxt⟩ := U.2.exists_basicOpen_le ⟨x₀, hxJ⟩ hx
  refine ⟨t, hxt, ?_⟩
  have hJW : X.basicOpen J ≤ X.basicOpen s := X.basicOpen_le J
  have hte : X.basicOpen t ≤ X.basicOpen s := htJ.trans hJW
  have hframe := hωW.res (U.2.basicOpen t) hte
  have e : TopForm.dOn p (fun i => resG X (X.basicOpen_le t) (x i)) =
      resG X hte J • TopForm.resForm hte (TopForm.resForm hsV ω) := by
    rw [← resForm_smul, hJ, hη, resForm_dOn]
    simp only [resG_resG]
  rw [e]
  refine ⟨U.2.basicOpen t, hframe.gen.smul_iff.2 ?_⟩
  have hu' : IsUnit (resG X hJW J) := X.toRingedSpace.isUnit_res_basicOpen J
  have := hu'.map (resG X htJ)
  rwa [resG_resG] at this

end GlobalTheory.FrameSpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDominantPullbackWithClass
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.DomPull

variable {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X'] (φ : X' ⟶ X) [IsDominant φ]

theorem unitAt_map {x : X'} {f : X.functionField} (h : UnitAt (φ x) f) :
    UnitAt x (GlobalTheory.functionFieldMap φ f) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨φ.stalkMap x a, ha.map _, (functionFieldMap_algebraMap φ x a).symm⟩

abbrev unitsMap : X.functionFieldˣ →* X'.functionFieldˣ := Units.map (GlobalTheory.functionFieldMap φ).toMonoidHom

theorem germOf_map_eq (D : CartierDiv X) {x : X'} {g g' : X.functionFieldˣ} (hg : D.IsEqn (φ x) g)
    (hg' : D.IsEqn (φ x) g') : germOf x (unitsMap φ g) = germOf x (unitsMap φ g') := by
  rw [germOf_eq_iff]
  have := unitAt_map φ (hg.iff_unitAt.1 hg')
  simpa only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, map_div₀] using this

def pullback (D : CartierDiv X) : CartierDiv X' :=
  show cartierGroup X' from ⟨fun x => germOf x (unitsMap φ (D.exists_isEqn (φ x)).choose), fun x => by
    obtain ⟨U, hU, g, hg⟩ := D.exists_isEqn_nhds (φ x)
    exact ⟨φ ⁻¹ᵁ U, hU, unitsMap φ g, fun y hy =>
      germOf_map_eq φ D (D.exists_isEqn (φ y)).choose_spec (hg _ hy)⟩⟩

theorem isEqn_pullback (D : CartierDiv X) {x : X'} {g : X.functionFieldˣ} (h : D.IsEqn (φ x) g) :
    (pullback φ D).IsEqn x (unitsMap φ g) :=
  germOf_map_eq φ D (D.exists_isEqn (φ x)).choose_spec h

theorem fnOf_app {U : X.Opens} (hU : genericPoint X' ∈ φ ⁻¹ᵁ U) (a : Γ(X, U)) :
    fnOf (φ ⁻¹ᵁ U) hU (φ.app U a) = GlobalTheory.functionFieldMap φ (fnOf U (gen_mem (x := φ (genericPoint X')) hU) a) := by
  rw [← algebraMap_germ (x := φ (genericPoint X')) hU a, functionFieldMap_algebraMap]
  erw [Scheme.Hom.germ_stalkMap_apply]
  exact (algebraMap_germ (X := X') hU _).symm

def pullEqns (D : CartierDiv X) (J : ((toLB D).pull φ).ι) : X'.functionFieldˣ :=
  unitsMap φ (J PUnit.unit).1.2

theorem fnOf_pull_g (D : CartierDiv X) (J J' : ((toLB D).pull φ).ι)
    (hg : genericPoint X' ∈ ((toLB D).pull φ).U J ⊓ ((toLB D).pull φ).U J') :
    fnOf _ hg (((toLB D).pull φ).g J J' : Γ(X', ((toLB D).pull φ).U J ⊓ ((toLB D).pull φ).U J')) =
      GlobalTheory.functionFieldMap φ (((J PUnit.unit).1.2 : X.functionField) / ((J' PUnit.unit).1.2 : X.functionField)) := by
  have h₀ : genericPoint X' ∈ φ ⁻¹ᵁ ((toLB D).U (J PUnit.unit) ⊓ (toLB D).U (J' PUnit.unit)) :=
    ⟨mem_pull.1 hg.1, mem_pull.1 hg.2⟩
  show fnOf _ hg (Units.val (∏ _k : PUnit.{1}, _ ^ (1 : ℤ))) = _
  rw [Fintype.prod_unique]
  erw [zpow_one, LB.val_res, fnOf_resG]
  exact (fnOf_app φ h₀ _).trans (congrArg _ (fnOf_toLB_g _ _ _))

theorem presents_pullback (D : CartierDiv X) :
    Presents (pullback φ D) ((toLB D).pull φ) (pullEqns φ D) := by
  refine ⟨LB.isLB_pull (isLB_toLB D) φ, fun J J' hg => ?_, fun J x hx => ?_⟩
  · rw [fnOf_pull_g φ D J J' hg]
    show GlobalTheory.functionFieldMap φ _ = GlobalTheory.functionFieldMap φ _ * GlobalTheory.functionFieldMap φ _
    rw [← map_mul, div_mul_cancel₀ _ (Units.ne_zero _)]
  · exact isEqn_pullback φ D ((J PUnit.unit).2.2 _ (mem_pull.1 hx))

end GlobalTheory.Cartier.DomPull

namespace GlobalTheory.Cartier


open DomPull in
theorem exists_pullback_cartierDiv : ∀ (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (φ : X' ⟶ X) [IsDominant φ]
    (D : CartierDiv X), ∃ D' : CartierDiv X', cls (toLB D') (isLB_toLB D') =
      cls ((toLB D).pull φ) (LB.isLB_pull (isLB_toLB D) φ) ∧
      ∀ (x : X') (g : X.functionFieldˣ), D.IsEqn (φ x) g →
        D'.IsEqn x (Units.map (GlobalTheory.functionFieldMap φ).toMonoidHom g) := by
  intro X X' _ _ φ _ D
  refine ⟨pullback φ D, ?_, fun x g h => isEqn_pullback φ D h⟩
  rw [← toPic_apply]
  exact (presents_pullback φ D).toPic_eq

end GlobalTheory.Cartier
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrLocalizationOfMinimalPrime
section
open Polynomial

namespace GlobalTheory

theorem exists_dvr_localization_of_minimal_prime : ∀ {κ : Type} [Field κ] (R : Subring κ)
    [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R κ] (Q : Ideal R) [Q.IsPrime],
    Q ≠ ⊥ → (∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → p ≤ Q → p = Q) →
    ∃ W : ValuationSubring κ, IsDiscreteValuationRing W ∧ (∀ r : R, (r : κ) ∈ W) ∧
      (∀ r : R, r ∉ Q → (r : κ)⁻¹ ∈ W) ∧ (∀ r : R, r ∈ Q → r ≠ 0 → (r : κ)⁻¹ ∉ W) ∧
      (∀ w ∈ W, ∃ b s : R, s ∉ Q ∧ w = b / s) := by
  first
  | exact @_root_.GlobalTheory.AuxiliaryLemmaSecond.main
  | exact _root_.GlobalTheory.AuxiliaryLemmaSecond.main
  | (apply _root_.GlobalTheory.AuxiliaryLemmaSecond.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AuxiliaryLemmaSecond.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AuxiliaryLemmaSecond.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AuxiliaryLemmaSecond.main ..)

end GlobalTheory
end

