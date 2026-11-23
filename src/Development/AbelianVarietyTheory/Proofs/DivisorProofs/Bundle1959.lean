module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBidualNaturalityDualSheafTranspose
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0552
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1936
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1534
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1915
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocallyFreeSubsheafDetIso
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.SubGlue
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover)
open GlobalTheory.LB (resG_resG resG_self exists_fun_of_cover)
open GlobalTheory.QCoh (appLinear appLinear_apply)

variable {X : Scheme.{0}} {F : X.Modules} {r : ℕ} {L : LB X}

abbrev spanRes (s : ∀ k : L.ι, Fin r → Γ(F, L.U k)) (k : L.ι) {W : X.Opens} (hk : W ≤ L.U k) :
    Submodule Γ(X, W) Γ(F, W) :=
  Submodule.span Γ(X, W) (Set.range fun i => resM F hk (s k i))

theorem resM_mem_spanRes (s : ∀ k : L.ι, Fin r → Γ(F, L.U k)) {k : L.ι} {W W' : X.Opens}
    (hW : W' ≤ W) (hk : W ≤ L.U k) {x : Γ(F, W)} (hx : x ∈ spanRes s k hk) :
    resM F hW x ∈ spanRes s k (hW.trans hk) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
  refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun i => resG X hW (c i), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, resM_smul, resM_resM]

theorem spanRes_le (s : ∀ k : L.ι, Fin r → Γ(F, L.U k))
    (A : ∀ k k' : L.ι, Matrix (Fin r) (Fin r) Γ(X, L.U k ⊓ L.U k'))
    (hA : ∀ (k k' : L.ι) (i : Fin r), resM F (inf_le_right : L.U k ⊓ L.U k' ≤ L.U k') (s k' i) =
      ∑ j, A k k' j i • resM F (inf_le_left : L.U k ⊓ L.U k' ≤ L.U k) (s k j))
    (k k' : L.ι) {W : X.Opens} (hk : W ≤ L.U k) (hk' : W ≤ L.U k') :
    spanRes s k' hk' ≤ spanRes s k hk := by
  rw [spanRes, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have e := congrArg (resM F (le_inf hk hk')) (hA k k' i)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [resM_resM, map_sum, resM_smul] at e
  change resM F hk' (s k' i) ∈ spanRes s k hk
  rw [show resM F hk' (s k' i) = _ from e]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

def IsLoc (s : ∀ k : L.ι, Fin r → Γ(F, L.U k)) (V : X.Opens) (x : Γ(F, V)) : Prop :=
  ∀ p ∈ V, ∃ (k : L.ι) (W : X.Opens) (h : W ≤ V) (hk : W ≤ L.U k), p ∈ W ∧
    resM F h x ∈ spanRes s k hk

def sub (hL : L.IsLB) (s : ∀ k : L.ι, Fin r → Γ(F, L.U k))
    (hmono : ∀ (k k' : L.ι) (W : X.Opens) (hk : W ≤ L.U k) (hk' : W ≤ L.U k'),
      spanRes s k' hk' ≤ spanRes s k hk) : VB.Sub F where
  sec V :=
    { carrier := {x | IsLoc s V x}
      zero_mem' := fun p hp => by
        obtain ⟨k, hk⟩ := Semi.LB.mem_of_cover hL p
        exact ⟨k, V ⊓ L.U k, inf_le_left, inf_le_right, ⟨hp, hk⟩, by rw [map_zero]; exact zero_mem _⟩
      add_mem' := fun {x y} hx hy p hp => by
        obtain ⟨k, W, h, hk, hpW, hxW⟩ := hx p hp
        obtain ⟨k', W', h', hk', hpW', hyW'⟩ := hy p hp
        refine ⟨k, W ⊓ W', inf_le_left.trans h, inf_le_left.trans hk, ⟨hpW, hpW'⟩, ?_⟩
        rw [map_add (f := _)]
        refine add_mem ?_ (hmono k k' _ (inf_le_left.trans hk) (inf_le_right.trans hk') ?_)
        · have := resM_mem_spanRes s (inf_le_left : W ⊓ W' ≤ W) hk hxW
          rw [resM_resM] at this
          exact this
        · have := resM_mem_spanRes s (inf_le_right : W ⊓ W' ≤ W') hk' hyW'
          rw [resM_resM] at this
          exact this
      smul_mem' := fun a x hx p hp => by
        obtain ⟨k, W, h, hk, hpW, hxW⟩ := hx p hp
        refine ⟨k, W, h, hk, hpW, ?_⟩
        rw [resM_smul]
        exact Submodule.smul_mem _ _ hxW }
  res_mem {V W} hWV x hx := fun p hp => by
    obtain ⟨k, W', h', hk, hp', hx'⟩ := (hx : IsLoc s V x) p (hWV hp)
    refine ⟨k, W ⊓ W', inf_le_left, inf_le_right.trans hk, ⟨hp, hp'⟩, ?_⟩
    rw [resM_resM]
    have := resM_mem_spanRes s (inf_le_right : W ⊓ W' ≤ W') hk hx'
    rw [resM_resM] at this
    exact this
  mem_of_local {V x} H := fun p hp => by
    obtain ⟨W, h, hpW, hW⟩ := H p hp
    obtain ⟨k, W', h', hk, hp', hx'⟩ := (hW : IsLoc s W _) p hpW
    refine ⟨k, W', h'.trans h, hk, hp', ?_⟩
    rw [resM_resM] at hx'
    exact hx'

theorem mem_spanRes_of_mem (hL : L.IsLB) (s : ∀ k : L.ι, Fin r → Γ(F, L.U k))
    (hmono : ∀ (k k' : L.ι) (W : X.Opens) (hk : W ≤ L.U k) (hk' : W ≤ L.U k'),
      spanRes s k' hk' ≤ spanRes s k hk)
    (hli : ∀ (k : L.ι) (V : X.Opens) (h : V ≤ L.U k),
      LinearIndependent Γ(X, V) fun i => resM F h (s k i))
    {k : L.ι} {V : X.Opens} (hV : V ≤ L.U k) {x : Γ(F, V)}
    (hx : x ∈ (sub hL s hmono).sec V) : x ∈ spanRes s k hV := by
  have hx' : IsLoc s V x := hx
  choose k' W hW hk' hpW hxW using fun p : V => hx' p p.2
  have hc : V ≤ iSup W := fun p hp => Opens.mem_iSup.2 ⟨⟨p, hp⟩, hpW _⟩
  have hin (p : V) : resM F (hW p) x ∈ spanRes s k ((hW p).trans hV) :=
    hmono k (k' p) _ _ _ (hxW p)
  choose c hc' using fun p => (Submodule.mem_span_range_iff_exists_fun _).1 (hin p)
  have key (p q : V) (i : Fin r) : resG X (inf_le_left : W p ⊓ W q ≤ W p) (c p i) =
      resG X (inf_le_right : W p ⊓ W q ≤ W q) (c q i) := by
    have hl := hli k (W p ⊓ W q) (inf_le_left.trans ((hW p).trans hV))
    have e1 := congrArg (resM F (inf_le_left : W p ⊓ W q ≤ W p)) (hc' p)
    have e2 := congrArg (resM F (inf_le_right : W p ⊓ W q ≤ W q)) (hc' q)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, resM_smul, resM_resM] at e1 e2
    exact Fintype.linearIndependent_iffₛ.1 hl _ _ (e1.trans e2.symm) i
  choose b hb using fun i => exists_fun_of_cover W hW hc (fun p => c p i) fun p q => key p q i
  refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨b, ?_⟩
  refine sec_ext_of_cover W hW hc fun p => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, resM_smul, resM_resM, hb]
  exact hc' p

end GlobalTheory.SubGlue

namespace GlobalTheory.SubGlue
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover)
open GlobalTheory.QCoh (appLinear appLinear_apply)

theorem exists_sub_isVB_lbIso_det : ∀ (X : Scheme.{0}) (F : X.Modules) (r : ℕ) (L : LB X), L.IsLB → ∀ (s : ∀ k : L.ι, Fin r → Γ(F, L.U k)) (A : ∀ k k' : L.ι, Matrix (Fin r) (Fin r) Γ(X, L.U k ⊓ L.U k')), (∀ (k : L.ι) (V : X.Opens) (h : V ≤ L.U k), LinearIndependent Γ(X, V) fun i => GlobalTheory.Twist.resM F h (s k i)) → (∀ (k k' : L.ι) (i : Fin r), GlobalTheory.Twist.resM F (inf_le_right : L.U k ⊓ L.U k' ≤ L.U k') (s k' i) = ∑ j, A k k' j i • GlobalTheory.Twist.resM F (inf_le_left : L.U k ⊓ L.U k' ≤ L.U k) (s k j)) → (∀ k k' : L.ι, (L.g k k').val = (A k k').det) → ∃ (W : X.Modules) (ι : W ⟶ F), Mono ι ∧ GlobalTheory.VB.IsVB W r ∧ LBIso L (GlobalTheory.VB.det W r) := by
  intro X F r L hL s A hli hA hdet
  have hmono := spanRes_le s A hA
  let N := sub hL s hmono
  have hmem (k : L.ι) (i : Fin r) : s k i ∈ N.sec (L.U k) := fun p hp =>
    ⟨k, L.U k, le_rfl, le_rfl, hp, Submodule.subset_span ⟨i, rfl⟩⟩
  have hfr (k : L.ι) : VB.IsFrame fun i => N.mkSec (s k i) (hmem k i) :=
    GlobalTheory.EigenFrames.isFrame_mkSec N (s k) (hmem k) (hli k)
      fun V h x hx => mem_spanRes_of_mem hL s hmono hli h hx
  have hv (k k' : L.ι) (i : Fin r) :
      resM N.toMod (inf_le_right : L.U k ⊓ L.U k' ≤ L.U k') (N.mkSec (s k' i) (hmem k' i)) =
        ((hfr k).basis (inf_le_left : L.U k ⊓ L.U k' ≤ L.U k)).equivFun.symm
          fun j => A k k' j i := by
    rw [VB.IsFrame.basis_equivFun_symm]
    apply N.incl_app_injective
    rw [app_resM, VB.Sub.incl_app_mkSec, hA]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← appLinear_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, appLinear_apply, app_resM, VB.Sub.incl_app_mkSec]
  refine ⟨N.toMod, N.incl, inferInstance, ?_⟩
  refine VB.lbIso_det_of_frames hL _ hfr fun k k' => Units.ext ?_
  rw [hdet, VB.IsFrame.val_detUnit, Module.Basis.det_apply]
  congr 1
  ext a b
  rw [Module.Basis.toMatrix_apply, hv, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

end GlobalTheory.SubGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogVectorFieldExtendFunctionFieldDerivatio
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

namespace GlobalTheory.LogKSDiv

theorem exists_derivation_extend {k A K : Type} [CommRing k] [CommRing A] [CommRing K] [Algebra k A] [Algebra k K]
    [Algebra A K] [IsScalarTower k A K] [Algebra.FormallyEtale A K] (D : Derivation k A A) :
    ∃ D' : Derivation k K K, ∀ a, D' (algebraMap A K a) = algebraMap A K (D a) := by
  let d : Derivation k A K := (Algebra.linearMap A K).compDer D
  let f : Ω[A⁄k] →ₗ[A] K := d.liftKaehlerDifferential
  have hb := KaehlerDifferential.isBaseChange_of_formallyEtale k A K
  let g : Ω[K⁄k] →ₗ[K] K := hb.lift f
  refine ⟨g.compDer (KaehlerDifferential.D k K), fun a => ?_⟩
  change g (KaehlerDifferential.D k K (algebraMap A K a)) = _
  rw [← KaehlerDifferential.map_D k k A K]
  erw [hb.lift_eq]
  simp [f, d]

end GlobalTheory.LogKSDiv

namespace GlobalTheory.LogKSDiv

theorem germ_appLE_apply {X Y : Scheme.{0}} (f : X ⟶ Y) (V : Y.Opens) (U' : X.Opens) (e : U' ≤ f ⁻¹ᵁ V) (x : X)
    (hx : x ∈ U') (hfx : f x ∈ V) (y : Γ(Y, V)) :
    X.presheaf.germ U' x hx (f.appLE V U' e y) = f.stalkMap x (Y.presheaf.germ V (f x) hfx y) := by
  rw [Scheme.Hom.germ_stalkMap_apply f V x hfx y, Scheme.Hom.appLE]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, TopCat.Presheaf.germ_res_apply]

end GlobalTheory.LogKSDiv

namespace GlobalTheory.LogKSDiv

def derivOfConst {k A : Type} [CommRing k] [CommRing A] (φ : k →+* A) (D : Derivation ℤ A A)
    (hD : ∀ a, D (φ a) = 0) : (letI := φ.toAlgebra; Derivation k A A) :=
  letI := φ.toAlgebra
  { toFun := D
    map_add' := D.map_add
    map_smul' := fun a x => by
      rw [Algebra.smul_def, D.leibniz, RingHom.algebraMap_toAlgebra, hD, smul_zero, add_zero]
      rfl
    map_one_eq_zero' := D.map_one_eq_zero
    leibniz' := D.leibniz }

end GlobalTheory.LogKSDiv

namespace GlobalTheory.LogKSDiv

theorem exists_genDer_extend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι → ∀ {N : ℕ} (Dl : Fin N → LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U), ∃ D : Fin N → GlobalTheory.LogKSDiv.GenDer TF Z, letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j r, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (ρ r) = ρ ((Dl j).1 r) := by
  intro E _ _ _ H Dw l Xo c TF Z _ U hU ρ hρ N Dl
  set W := barComp TF.Y Z with hW
  set η₀ := genericPoint (X₀ TF.Y Z) with hη₀
  have hη : W.ι η₀ ∈ U.1 := by
    have e := congrArg (fun f : Sp (X₀ TF.Y Z).functionField ⟶ TF.Y.X => f (IsLocalRing.closedPoint _)) hρ
    simp only [Scheme.Hom.comp_apply] at e
    show W.ι η₀ ∈ (U.1 : Set TF.Y.X)
    rw [← U.2.range_fromSpec]
    refine ⟨_, e.trans ?_⟩
    exact congrArg W.ι Scheme.fromSpecStalk_closedPoint
  have hmono : Mono (LogKS.chart U) := by
    haveI := U.2.isOpenImmersion_fromSpec
    unfold LogKS.chart; infer_instance
  have hρ' : ρ = (TF.Y.X.presheaf.germ U.1 (W.ι η₀) hη ≫ W.ι.stalkMap η₀).hom := by
    have e : CommRingCat.ofHom ρ = TF.Y.X.presheaf.germ U.1 (W.ι η₀) hη ≫ W.ι.stalkMap η₀ := by
      apply Spec.map_injective
      rw [← cancel_mono (LogKS.chart U)]
      refine hρ.trans ?_
      have e1 := U.2.fromSpecStalk_eq_fromSpecStalk hη
      rw [Spec.map_comp, Category.assoc, LogKS.chart]
      show (X₀ TF.Y Z).fromSpecStalk η₀ ≫ W.ι = _
      rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← e1]
      rfl
    exact congrArg CommRingCat.Hom.hom e
  subst hρ'
  have hiso : IsIso (W.ι.stalkMap η₀) := inferInstance
  letI iA : Algebra c.F Γ(TF.Y.X, U.1) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX TF.Y.s U.1).toAlgebra
  letI iK : Algebra c.F (X₀ TF.Y Z).functionField := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra
  letI iAK : Algebra Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField :=
    (TF.Y.X.presheaf.germ U.1 (W.ι η₀) hη ≫ W.ι.stalkMap η₀).hom.toAlgebra
  have htow : IsScalarTower c.F Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext a
    simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, GlobalTheory.Cartier.constFn, GlobalTheory.Cartier.fnOf,
      ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX, CommRingCat.hom_comp]
    refine (germ_appLE_apply (s₀ TF.Y Z) ⊤ ⊤ _ (genericPoint (X₀ TF.Y Z)) trivial trivial _).trans ?_
    refine Eq.trans ?_ (congrArg (W.ι.stalkMap η₀).hom
      (germ_appLE_apply TF.Y.s ⊤ U.1 _ (W.ι η₀) hη trivial _)).symm
    rw [show s₀ TF.Y Z = W.ι ≫ TF.Y.s from rfl, Scheme.Hom.stalkMap_comp]
    rfl
  letI iS : Algebra Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk (W.ι η₀)) :=
    TopCat.Presheaf.algebra_section_stalk TF.Y.X.presheaf (U := U.1) ⟨W.ι η₀, hη⟩
  have hloc := U.2.isLocalization_stalk ⟨W.ι η₀, hη⟩
  let eK : TF.Y.X.presheaf.stalk (W.ι η₀) ≃ₐ[Γ(TF.Y.X, U.1)] (X₀ TF.Y Z).functionField :=
    AlgEquiv.ofRingEquiv (f := (asIso (W.ι.stalkMap η₀)).commRingCatIsoToRingEquiv) fun _ => rfl
  haveI := IsLocalization.isLocalization_of_algEquiv (U.2.primeIdealOf ⟨W.ι η₀, hη⟩).asIdeal.primeCompl eK
  haveI : Algebra.FormallyEtale Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField :=
    Algebra.FormallyEtale.of_isLocalization (U.2.primeIdealOf ⟨W.ι η₀, hη⟩).asIdeal.primeCompl
  choose D hD using fun j => exists_derivation_extend (k := c.F) (K := (X₀ TF.Y Z).functionField)
    (derivOfConst (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX TF.Y.s U.1) (Dl j).1 (Dl j).2.1)
  exact ⟨D, fun j r => hD j r⟩

end GlobalTheory.LogKSDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPackingSetMeasureGeCovolume
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

open MeasureTheory
open scoped Pointwise

theorem packing_set_covolume_le :
    ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) (Γ : Subgroup H), Countable Γ → ∃ F : Set H, MeasurableSet F ∧ covolume Γ H ν ≤ ν F ∧ ∀ γ ∈ Γ, ∀ y ∈ F, γ * y ∈ F → γ = 1 := by
  intro H _ _ _ ν Γ _
  classical
  by_cases hF : HasFundamentalDomain Γ H ν
  swap
  · refine ⟨∅, MeasurableSet.empty, ?_, ?_⟩
    · simp [covolume, hF]
    · intro γ _ y hy; exact absurd hy (Set.notMem_empty y)
  · set s := hF.ExistsIsFundamentalDomain.choose with hs_def
    have hs : IsFundamentalDomain Γ s ν := hF.ExistsIsFundamentalDomain.choose_spec
    have hcov : covolume Γ H ν = ν s := by simp [covolume, hF, hs_def]
    obtain ⟨t, hts, htm, hte⟩ := hs.nullMeasurableSet.exists_measurable_subset_ae_eq
    have hsmul : ∀ g : Γ, (g • t : Set H) = (fun y => (g : H)⁻¹ * y) ⁻¹' t := by
      intro g; ext y
      simp [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def]
    have hmeas : ∀ g : Γ, MeasurableSet (g • t : Set H) := by
      intro g; rw [hsmul g]; exact (measurable_const_mul _) htm
    let U : Set H := ⋃ g : {g : Γ // g ≠ 1}, (g.1 • t : Set H)
    have hUm : MeasurableSet U := MeasurableSet.iUnion (fun g => hmeas g.1)
    have hnull : ν (t ∩ U) = 0 := by
      rw [Set.inter_iUnion]
      refine measure_iUnion_null (fun g => ?_)
      have h1 := hs.aedisjoint (Ne.symm g.2 : (1 : Γ) ≠ g.1)
      have h2 : ν ((1 : Γ) • s ∩ g.1 • s) = 0 := h1
      rw [one_smul] at h2
      exact measure_mono_null (Set.inter_subset_inter hts (Set.smul_set_mono hts)) h2
    refine ⟨t \ U, htm.diff hUm, ?_, ?_⟩
    · rw [hcov, ← Set.sdiff_self_inter, measure_sdiff_null hnull]
      exact (measure_congr hte).ge
    · intro γ hγ y hy hγy
      by_contra hne
      have hne' : (⟨γ, hγ⟩ : Γ) ≠ 1 := fun h => hne (congrArg Subtype.val h)
      apply hγy.2
      refine Set.mem_iUnion.2 ⟨⟨⟨γ, hγ⟩, hne'⟩, ?_⟩
      exact ⟨y, hy.1, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosCombinationSmoothConeSymmIntForm
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.ConeInterior

section Help

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem exists_nat_comb {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCone bar φ γ)
    {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X) {c : Fin m → ℝ} (hc : ∀ i, 0 ≤ c i)
    (h : toReal β = ∑ i, c i • toReal (γ i)) : ∃ n : Fin m → ℕ, β = ∑ i, n i • γ i := by
  classical
  obtain ⟨f, hf⟩ := hγ.basis.exists_dual
  have hz : ∀ i, c i = (f i ⟨β, hβ⟩ : ℤ) := fun i => by
    have h0 : ∑ o : Option (Fin m), (Option.elim o (-1) c) • toReal ((balForms bar X).subtype
        (Option.elim o (⟨β, hβ⟩ : balForms bar X) fun k => ⟨γ k, hγ.mem k⟩)) = 0 := by
      rw [Fintype.sum_option]
      simp only [Option.elim_none, Option.elim_some, Submodule.subtype_apply, h, neg_one_smul, neg_add_cancel]
    have := sum_mul_eq_zero_of_sum_toReal Subtype.val_injective (f i) h0
    rw [Fintype.sum_option] at this
    simp only [Option.elim_none, Option.elim_some, hf] at this
    simp at this
    linarith
  have hn : ∀ i, ∃ n : ℕ, c i = n := fun i => by
    have h1 : (0 : ℤ) ≤ f i ⟨β, hβ⟩ := by exact_mod_cast (hz i ▸ hc i : (0 : ℝ) ≤ (f i ⟨β, hβ⟩ : ℤ))
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h1
    exact ⟨n, by rw [hz i, hn, Int.cast_natCast]⟩
  choose n hn using hn
  refine ⟨n, LinearMap.ext₂ fun a b => ?_⟩
  have := LinearMap.congr_fun₂ h a b
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul, hn, nsmul_eq_mul] at this ⊢
  exact_mod_cast this

theorem exists_pos_comb (hP : IsPolFanOn bar φ X) {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X)
    (hp : toReal β ∈ psdCone (bar := bar) (X := X)) :
    ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (cf : Fin m → ℕ),
      IsCone bar φ γ ∧ (∀ j, 0 < cf j) ∧ β = ∑ j, cf j • γ j := by
  classical
  obtain ⟨m, γ, c, hγ, hc, h⟩ := hP.cover _ hp
  obtain ⟨n, hn⟩ := exists_nat_comb hγ hβ hc h
  let S : Finset (Fin m) := Finset.univ.filter fun i => 0 < n i
  let s : Fin S.card ↪ Fin m := (S.orderEmbOfFin rfl).toEmbedding
  have hs : Finset.univ.map s = S := Finset.map_orderEmbOfFin_univ S rfl
  refine ⟨S.card, fun i => γ (s i), fun i => n (s i), hP.face _ _ γ s hγ, fun j => ?_, ?_⟩
  · exact (Finset.mem_filter.1 (S.orderEmbOfFin_mem rfl j)).2
  · rw [hn, ← Finset.sum_map Finset.univ s fun i => n i • γ i, hs]
    refine (Finset.sum_subset (Finset.subset_univ S) fun i _ hi => ?_).symm
    have : n i = 0 := by simpa [S] using hi
    rw [this, zero_smul]

end Help

theorem exists_pos_comb_int : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ r : ℕ, r ≤ g → ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → toReal b ∈ psdCone (bar := (id : ℤ → ℤ)) (X := (Fin r → ℤ)) → ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)) (cf : Fin m → ℕ), IsCone id φ γ ∧ (∀ j, 0 < cf j) ∧ b = ∑ j, cf j • γ j := by
  intro g φ hφ r hr b hb hp
  exact exists_pos_comb (hφ (Fin r → ℤ) (by simpa using hr)) (mem_balForms_int.2 hb) hp

end GlobalTheory.ConeInterior
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianMapModelOfIntegralFramedPointStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelianMap_model_of_integralFramedPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y : FrPt Xo c T.Fr) (x : Sp T.V ⟶ Y.X), spMap (algebraMap T.V T.Fr) ≫ x = GlobalTheory.FlagMod.frX y ≫ Y.j → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t y.x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))), ∃ (ψ : SABMap G Y.t x) (ρ : t'.G.left ⟶ Y.oF.t.G.left), ρ ≫ Y.m0.toSABMap.φ = m1.φ ∧ ρ ≫ Y.oF.t.G.hom = t'.G.hom ≫ GlobalTheory.FlagMod.frX y ∧ ρ ≫ Y.m.φ = m2.φ ≫ ψ.φ := by
  first | exact @GlobalTheory.exists_sabMap_model_of_integral_frPt | exact GlobalTheory.exists_sabMap_model_of_integral_frPt | (intros; apply GlobalTheory.exists_sabMap_model_of_integral_frPt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearL2CuspForm
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CovTop.PetRep
open MeasureTheory

section Gen

open ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {D : D7}

end Gen


set_option maxHeartbeats 2000000 in
theorem adelMeas_one_of_good {D : D7} {T : Core D} {j : ℕ} (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o)
    (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) :
    AdelMeas Y.U σ (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) := by
  obtain ⟨th, hr, hth, hd⟩ := h.dictU σ hσ
  have hN : 0 < D.host.g 0 * D.host.g 1 * Y.d.pd := by
    rw [h.pd]
    exact Nat.mul_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) (pow_pos (by norm_num) _)
  have hL := GlobalTheory.DictLocTest.locClause_of_unif_places hd (fun k hk => ((h.levelK k).1 hk).1)
    (GlobalTheory.LevelNbhd.level_mul_inf_mem_nhds D _ _ Y.Kf hN h.levelK) (fun c τ => ⟨_, hth c τ⟩)
  exact adelMeas_of_aut Y.d.Xo₂ Y.d.c₂ (U := Y.U) (σ := σ)
    (GlobalTheory.PetDef.adelAut_of_gamma (fun k la γ hγ => GlobalTheory.CovTop.Model.chi_eq_one h σ hσ k la γ hγ) hd
      (GlobalTheory.PetDef.muUnit_one Y h σ hσ) hL continuous_const)

end GlobalTheory.CovTop.PetRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueGenericFibreDualNumberPointOfModelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_genericFibreDualNumberPoint_of_model : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (y : epsR V ⟶ G), (∃! yA, VecAt U.toUnifPre F y yA) ∧ (∃! v : epsR (FractionRing V) ⟶ A.A, IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) y v) ∧ ∀ (v : epsR (FractionRing V) ⟶ A.A) yA, IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) y v → VecAt U.toUnifPre F y yA → yA ≫ (snd (TFK (R := V) F) A.A).left = spMap (dualMap (algebraMap (FractionRing V) F)) ≫ v.left := by
  first | exact @GlobalTheory.MBLow.vecAt_genFibre | exact GlobalTheory.MBLow.vecAt_genFibre | (intros; apply GlobalTheory.MBLow.vecAt_genFibre <;> assumption)
end

