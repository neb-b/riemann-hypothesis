module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2110
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.DescGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1946
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1975
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1996
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleFirstOrderTaylorSqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2064

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOfInvariantPullbackGenerator
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharKer

section Descent

variable {X Y : Scheme.{0}}

lemma appLE_eq_of_eq_hom {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

lemma opens_toTop_bijective (U : X.Opens) : Function.Bijective (U.ι.appLE U ⊤ U.ι_preimage_self.ge) := by
  have e : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
    rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]; rfl
  rw [e]
  exact ConcreteCategory.bijective_of_isIso U.topIso.inv

lemma restrict_appTop_toTop (p : X ⟶ Y) (V : Y.Opens) (a : Γ(Y, V)) :
    (p ∣_ V).appTop (V.ι.appLE V ⊤ V.ι_preimage_self.ge a) =
      (p ⁻¹ᵁ V).ι.appLE (p ⁻¹ᵁ V) ⊤ (p ⁻¹ᵁ V).ι_preimage_self.ge (p.app V a) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  congr 1
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]
  erw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  exact congrArg _ (appLE_eq_of_eq_hom (morphismRestrict_ι p V) _ _ _)

lemma restrict_props (p : X ⟶ Y) [Flat p] [Surjective p] [IsAffineHom p] (V : Y.Opens) :
    Flat (p ∣_ V) ∧ Surjective (p ∣_ V) ∧ IsAffineHom (p ∣_ V) :=
  ⟨inferInstance, IsZariskiLocalAtTarget.restrict ‹_› V, by first | exact HasAffineProperty.restrict ‹_› V | exact IsZariskiLocalAtTarget.restrict (P := @IsAffineHom) ‹_› V | exact (MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom) (isPullback_morphismRestrict p V).flip ‹_›) | exact (inferInstance : IsAffineHom (p.resLE V (p ⁻¹ᵁ V) le_rfl))⟩

lemma appTop_toTop (V : X.Opens) {Z : Scheme.{0}} (y : Z ⟶ V.toScheme) (s : Γ(X, V)) :
    y.appTop (V.ι.appLE V ⊤ V.ι_preimage_self.ge s) =
      (y ≫ V.ι).appLE V ⊤ (fun z _ => (y z).2) s := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  erw [Scheme.Hom.appLE_comp_appLE]
  rfl

theorem exists_app_eq_of_invariant (p : X ⟶ Y) [Flat p] [Surjective p] [IsAffineHom p] (V : Y.Opens)
    (s : Γ(X, p ⁻¹ᵁ V))
    (hs : ∀ (Z : Scheme.{0}) (y₁ y₂ : Z ⟶ X), y₁ ≫ p = y₂ ≫ p → ∀ (h₁ : ⊤ ≤ y₁ ⁻¹ᵁ (p ⁻¹ᵁ V))
      (h₂ : ⊤ ≤ y₂ ⁻¹ᵁ (p ⁻¹ᵁ V)), y₁.appLE _ ⊤ h₁ s = y₂.appLE _ ⊤ h₂ s) :
    ∃ a : Γ(Y, V), p.app V a = s := by
  obtain ⟨h1, h2, h3⟩ := restrict_props p V
  obtain ⟨v, hv⟩ := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.descend_gen (p ∣_ V)
    ((p ⁻¹ᵁ V).ι.appLE (p ⁻¹ᵁ V) ⊤ (p ⁻¹ᵁ V).ι_preimage_self.ge s) (fun y₁ y₂ h => by
      rw [appTop_toTop, appTop_toTop]
      refine hs _ _ _ ?_ _ _
      rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, ← Category.assoc, h, Category.assoc])
  obtain ⟨a, rfl⟩ := (opens_toTop_bijective V).2 v
  refine ⟨a, (opens_toTop_bijective (p ⁻¹ᵁ V)).1 ?_⟩
  rw [← restrict_appTop_toTop]
  exact hv

lemma app_map_homOfLE (p : X ⟶ Y) {U V : Y.Opens} (h : V ≤ U) (a : Γ(Y, U)) :
    p.app V (Y.presheaf.map (homOfLE h).op a) =
      X.presheaf.map (homOfLE (fun _ hx => h hx : p ⁻¹ᵁ V ≤ p ⁻¹ᵁ U)).op (p.app U a) := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
  rfl

end Descent


open ReciprocityTheory.ChartRestriction.G.DVR.TG in
theorem triv_of_isPullGen_of_invariant : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y), Flat p → Surjective p → IsAffineHom p → ∀ (M : LB Y) (e : ∀ k, Γ(X, p ⁻¹ᵁ M.U k)ˣ), IsPullGen p M e → (∀ (Z : Scheme.{0}) (y₁ y₂ : Z ⟶ X), y₁ ≫ p = y₂ ≫ p → ∀ (k : M.ι) (W : Z.Opens) (h₁ : W ≤ y₁ ⁻¹ᵁ (p ⁻¹ᵁ M.U k)) (h₂ : W ≤ y₂ ⁻¹ᵁ (p ⁻¹ᵁ M.U k)), res h₁ (pullU y₁ _ (e k)) = res h₂ (pullU y₂ _ (e k))) → Triv M := by
  intro X Y p _ _ _ M e he hinv
  have hval : ∀ (k : M.ι) (u : Γ(X, p ⁻¹ᵁ M.U k)ˣ), (u = e k ∨ u = (e k)⁻¹) →
      ∃ a : Γ(Y, M.U k), p.app _ a = u := by
    intro k u hu
    refine exists_app_eq_of_invariant p (M.U k) u ?_
    intro Z y₁ y₂ hy h₁ h₂
    have H := hinv Z y₁ y₂ hy k ⊤ h₁ h₂
    rcases hu with rfl | rfl
    · exact congrArg Units.val H
    · have H' := congrArg (fun x => x⁻¹) H
      simp only [← map_inv] at H'
      exact congrArg Units.val H'
  choose f hf using fun k => hval k (e k) (Or.inl rfl)
  choose f' hf' using fun k => hval k (e k)⁻¹ (Or.inr rfl)
  have inj := fun V => app_injective_of_flat_surj p V
  have hmul : ∀ k, f k * f' k = 1 := fun k =>
    inj _ (by rw [map_mul, map_one, hf, hf', Units.mul_inv])
  let fu : ∀ k, Γ(Y, M.U k)ˣ := fun k => ⟨f k, f' k, hmul k, by rw [mul_comm]; exact hmul k⟩
  refine ⟨⟨fu⟩, fun i j => Units.ext (inj _ ?_)⟩
  have H := congrArg Units.val
    (he i j (p ⁻¹ᵁ (M.U i ⊓ M.U j)) (fun _ hx => hx.1) (fun _ hx => hx.2) le_rfl)
  have eX : ∀ {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)ˣ),
      ((res h a : Γ(X, V)ˣ) : Γ(X, V)) = X.presheaf.map (homOfLE h).op a := fun _ _ => rfl
  have eY : ∀ {U V : Y.Opens} (h : V ≤ U) (a : Γ(Y, U)ˣ),
      ((res h a : Γ(Y, V)ˣ) : Γ(Y, V)) = Y.presheaf.map (homOfLE h).op a := fun _ _ => rfl
  have eP : ((pullU p (M.U i ⊓ M.U j) (M.g i j) : Γ(X, p ⁻¹ᵁ (M.U i ⊓ M.U j))ˣ) : Γ(X, p ⁻¹ᵁ (M.U i ⊓ M.U j))) =
      p.app _ (M.g i j) := rfl
  have eid : X.presheaf.map (homOfLE (le_rfl : p ⁻¹ᵁ (M.U i ⊓ M.U j) ≤ p ⁻¹ᵁ (M.U i ⊓ M.U j))).op =
      𝟙 _ := by
    rw [show homOfLE (le_rfl : p ⁻¹ᵁ (M.U i ⊓ M.U j) ≤ _) = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
  simp only [Units.val_mul, eX, eP] at H
  rw [eid, CommRingCat.id_apply] at H
  simp only [Units.val_mul, map_mul, eY, app_map_homOfLE]
  show X.presheaf.map _ (p.app _ (f i)) = _ * X.presheaf.map _ (p.app _ (f j))
  rw [hf, hf]
  exact H

end GlobalTheory.CharKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelCompactIntertwines
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.DblScal in
theorem GlobalTheory.DblScal.scalW_main : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ κ : UA σ W.J → ℂ, (∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = κ h • fun Y => ι φ (Y * (GlobalTheory.SplitFlip.invT (locMat t c h)).val)) →
    ∀ h ∈ UAt σ W (evFin F v), κ h = (chrW χX t (GlobalTheory.SplitFlip.gdet (locMat t c h)) : ℂ) *
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (locMat t c h)) (-(n : ℂ) / 2) := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v t b c ι hι κ hκ h hh
  obtain ⟨⟨-, dd, omd, hdc, hws, hbox⟩, -, -⟩ := hP.weil
  have hspl := hws.2.1
  have hloc := GlobalTheory.T.double_splitting_pair_identity hPr F E σ B n d X W M χX χW om r s r' s' hP dd omd hspl v
  obtain ⟨ιd, hιd, hprod⟩ := GlobalTheory.T.linear_model_double_splitting hPr F E σ B n d X W M χX χW om r s r' s' hP v t b c ι hι dd hdc
  obtain ⟨cd, hcd⟩ := GlobalTheory.T.double_scaling_local_identity hPr F E σ B n d X W M χX χW om r s r' s' hP v t b c dd omd hspl hloc ιd hιd
  obtain ⟨χd, hχd⟩ := GlobalTheory.T.double_scaling_local_equivariance hPr F E σ B n d X W M χX χW om r s r' s' hP v t b c dd omd hspl hloc ιd hιd cd hcd
  obtain ⟨gd, hgd⟩ := exists_diag_one h
  have hgdAt : gd ∈ UDAt σ W.J (evFin F v) := by
    intro u hu
    change u • (((gd : GL (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) = 0
    have h1 : u • (mat h - 1) = 0 := hh u hu
    rw [hgd, fromBlocks_sub_one, Matrix.fromBlocks_smul, h1]
    simp
  have e1 : κ h = cd gd := GlobalTheory.T.linear_model_compact_equivariance hPr F E σ B n d X W M χX χW om r s r' s' hP v t b c ι hι κ hκ dd omd hdc hspl
    (fun g gd' hg φ₁ hφ₁ φ₂ hφ₂ => hbox g gd' hg φ₁ hφ₁ φ₂ hφ₂) hloc ιd hιd hprod cd hcd h hh gd hgd
  obtain ⟨p, hpAt, hp⟩ := GlobalTheory.T.double_scaling_iwasawa_decomposition F E σ B n d X W M χX χW om r s r' s' hP v t c (fixDiag (locMat t c h))
  have e5 := GlobalTheory.T.double_scaling_local_vanishing hPr F E σ B n d X W M χX χW om r s r' s' hP v t b c dd omd hdc hws hloc ιd hιd cd hcd p hpAt
    ⟨1, by rw [hp]; exact fixDiag_diag _⟩
  rw [hp, gdet_fixDiag] at e5
  have f1 : cd gd = χd (GlobalTheory.SplitFlip.gdet (locMat t c h)) := by rw [hχd gd hgdAt, gdet_locMatD_diag t c h gd hgd]
  have f2 : cd p = χd (GlobalTheory.SplitFlip.gdet (locMat t c h)) := by rw [hχd p hpAt, hp, gdet_fixDiag]
  rw [e1, f1, ← f2]
  exact e5
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearlyDisjointFunctionFieldOfFlatBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

namespace GlobalTheory.Desc.FlatLin

theorem fnOf_algX {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (p : X ⟶ Sp R) (U : X.Opens)
    (hU : genericPoint X ∈ U) (r : R) :
    fnOf U hU (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U r) = cst p r := by
  simp only [ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX, cst, RingHom.comp_apply, fnOf, Scheme.Hom.appLE,
    CommRingCat.hom_comp]
  erw [TopCat.Presheaf.germ_res_apply]
  rfl

theorem gen_map {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {π : Y ⟶ X}
    {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ) : π (genericPoint Y) = genericPoint X := by
  obtain ⟨l, h1, h2⟩ := h
  rw [Category.comp_id] at h1
  subst h1
  have eY : gp Y (closedPoint (Y.presheaf.stalk (genericPoint Y))) = genericPoint Y :=
    Scheme.fromSpecStalk_closedPoint
  have hc : (spMap θ) (closedPoint (Y.presheaf.stalk (genericPoint Y))) =
      closedPoint (X.presheaf.stalk (genericPoint X)) :=
    Subsingleton.elim (α := PrimeSpectrum X.functionField) _ _
  calc π (genericPoint Y) = π (gp Y (closedPoint (Y.presheaf.stalk (genericPoint Y)))) := by rw [eY]
    _ = (gp Y ≫ π) (closedPoint (Y.presheaf.stalk (genericPoint Y))) := (Scheme.Hom.comp_apply _ _ _).symm
    _ = (spMap θ ≫ gp X) (closedPoint (Y.presheaf.stalk (genericPoint Y))) := by rw [h2]
    _ = gp X (spMap θ (closedPoint (Y.presheaf.stalk (genericPoint Y)))) := Scheme.Hom.comp_apply _ _ _
    _ = genericPoint X := by rw [hc]; exact Scheme.fromSpecStalk_closedPoint

theorem fnOf_appLE {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {π : Y ⟶ X}
    {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ) (U : X.Opens) (V : Y.Opens)
    (e : V ≤ π ⁻¹ᵁ U) (hU : genericPoint X ∈ U) (hV : genericPoint Y ∈ V) (a : Γ(X, U)) :
    fnOf V hV ((π.appLE U V e).hom a) = θ (fnOf U hU a) := by
  rw [GaussPt.theta_fnOf h U hU (e hV) a]
  simp only [fnOf, Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
  erw [TopCat.Presheaf.germ_res_apply]

theorem linDisj_of_flat : ∀ (T D : Type) [CommRing T] [CommRing D] (a : T →+* D), a.Flat → ∀ (H : Over (Sp T)) [IsIntegral H.left] (H' : Over (Sp D)) [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → LinDisj (GlobalTheory.Desc.cst H.hom) (GlobalTheory.Desc.cst H'.hom) θ := by
  intro T D _ _ a ha H _ H' _ π θ hpb hθ n u hu r hr
  classical
  letI : Algebra T D := a.toAlgebra
  haveI : Module.Flat T D := ha
  have hη : π (genericPoint H'.left) = genericPoint H.left := gen_map hθ
  obtain ⟨U, hUa, hηU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 H.left.isBasis_affineOpens)
    (show genericPoint H.left ∈ (⊤ : H.left.Opens) from trivial)
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen H.left U hUa
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors Γ(H.left, U)) u
  choose A hA using hs
  have hA' : ∀ i, fnOf U hηU (A i) = fnOf U hηU s * u i := fun i => by
    have := hA i; rw [Algebra.smul_def] at this; exact this
  have hs0 : fnOf U hηU s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  letI : Algebra T Γ(H.left, U) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX H.hom U).toAlgebra
  let f : (Fin n → T) →ₗ[T] Γ(H.left, U) :=
    { toFun := fun c => ∑ i, c i • A i
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun t c => by simp [Finset.smul_sum, smul_smul] }
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    apply hu c
    have h1 := congrArg (fnOf U hηU) hc
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_zero, Algebra.smul_def, map_mul,
      RingHom.algebraMap_toAlgebra, fnOf_algX, hA'] at h1
    have e : fnOf U hηU s * ∑ i, cst H.hom (c i) * u i = 0 := by
      rw [Finset.mul_sum, ← h1]; refine Finset.sum_congr rfl fun i _ => ?_; ring
    exact (mul_eq_zero.1 e).resolve_left hs0
  have hfD : Function.Injective (f.lTensor D) := Module.Flat.lTensor_preserves_injective_linearMap f hf
  let x := (TensorProduct.piScalarRight T T D (Fin n)).symm r
  have hx : f.lTensor D x = ∑ i, r i ⊗ₜ[T] A i := by
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [show x = ∑ i, (TensorProduct.piScalarRight T T D (Fin n)).symm (Pi.single i (r i)) by
      simp only [x, ← map_sum, Finset.univ_sum_single]]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [TensorProduct.piScalarRight_symm_single, map_sum, LinearMap.lTensor_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    simp [f, Pi.single_apply]
  let V' : H'.left.Opens := π ⁻¹ᵁ U ⊓ H'.hom ⁻¹ᵁ ⊤
  have hV' : genericPoint H'.left ∈ V' := ⟨show π _ ∈ U by rw [hη]; exact hηU, trivial⟩
  let E := ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens H.hom H'.hom π hpb U hUa
  let y : TensorProduct T Γ(H.left, U) D := TensorProduct.comm T D Γ(H.left, U) (f.lTensor D x)
  have hy : y = ∑ i, A i ⊗ₜ[T] r i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [y, hx, map_sum, TensorProduct.comm_tmul]
  have hEy : fnOf V' hV' (E y) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy, map_sum, map_sum]
    have step : ∀ i, fnOf V' hV' (E (A i ⊗ₜ[T] r i)) = θ (fnOf U hηU s * u i) * cst H'.hom (r i) := fun i => by
      rw [show E (A i ⊗ₜ[T] r i) = _ from ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens_tmul H.hom H'.hom π hpb U hUa (A i) (r i)]
      rw [map_mul, fnOf_appLE hθ U V' inf_le_left hηU hV', fnOf_algX, hA']
    rw [Finset.sum_congr rfl fun i _ => step i]
    have e : ∑ i, θ (fnOf U hηU s * u i) * cst H'.hom (r i) =
        θ (fnOf U hηU s) * ∑ i, cst H'.hom (r i) * θ (u i) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [map_mul]; ring
    rw [e, hr, mul_zero]
  have hy0 : y = 0 := by
    have : E y = 0 := fnOf_injective V' hV' (by rw [hEy, map_zero])
    exact E.injective (this.trans E.map_zero.symm)
  have hx0 : x = 0 := by
    apply hfD
    rw [map_zero]
    exact (TensorProduct.comm T D Γ(H.left, U)).injective (hy0.trans (map_zero _).symm)
  have : r = (TensorProduct.piScalarRight T T D (Fin n)) x := by simp only [x, LinearEquiv.apply_symm_apply]
  rw [this, hx0, map_zero]

end GlobalTheory.Desc.FlatLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocIsoTransportCochainsInIdeal
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

theorem mul_eq_zero_of_mem_sqMap {R : Type} [CommRing R] {I : Ideal R} {B : Type} [CommRing B] [Algebra R B]
    (hJ : I.map (algebraMap R B) ^ 2 = 0) {u v : B} (hu : u ∈ I.map (algebraMap R B))
    (hv : v ∈ I.map (algebraMap R B)) : u * v = 0 := by
  have := Ideal.mul_mem_mul hu hv
  rwa [← pow_two, hJ, Ideal.zero_eq_bot, Ideal.mem_bot] at this

theorem algHom_apply_mem_map {R : Type} [CommRing R] {I : Ideal R} {A B : Type} [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] (f : A →ₐ[R] B) {x : A} (hx : x ∈ I.map (algebraMap R A)) : f x ∈ I.map (algebraMap R B) := by
  have := Ideal.mem_map_of_mem (f : A →+* B) hx
  rwa [Ideal.map_map, AlgHom.comp_algebraMap] at this

theorem eq_of_sub_mem_map {R : Type} [CommRing R] {I : Ideal R} {A B : Type} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (hJ : I.map (algebraMap R B) ^ 2 = 0) (f g : A →ₐ[R] B)
    (h : ∀ b, f b - g b ∈ I.map (algebraMap R B)) {x : A} (hx : x ∈ I.map (algebraMap R A)) : f x = g x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, -, rfl⟩ := hy
    rw [AlgHom.commutes, AlgHom.commutes]
  | zero => rw [map_zero, map_zero]
  | add y y' _ _ h1 h2 => rw [map_add (f := _), map_add (f := _), h1, h2]
  | smul a y hy ih =>
    rw [smul_eq_mul, map_mul, map_mul, ← ih, ← sub_eq_zero, ← sub_mul]
    exact mul_eq_zero_of_mem_sqMap hJ (h a) (algHom_apply_mem_map f hy)

theorem locIso_transport : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S'), (∀ z : Z1 S.F, S.IsIdealValuedLiftSystemCocycle z → ∃ z' : Z1 S'.F, S'.IsIdealValuedLiftSystemCocycle z' ∧ ∀ U V a, z'.1 U V a = Φ.φ V (z.1 U V a)) ∧ (∀ g : C0 S.F, S.IsIdealValuedLiftSystemCochain g → ∀ U V a, d0 S'.F (fun W ↦ Φ.φ W (g W)) U V a = Φ.φ V (d0 S.F g U V a)) ∧ ∀ c ∈ I • (⊤ : Submodule R (Cr hI π s₀)), ∃ (z : Z1 S.F) (z' : Z1 S'.F), S.IsIdealValuedLiftSystemCocycle z ∧ H1.mk _ z = S.r hI c ∧ H1.mk _ z' = S'.r hI c ∧ ∀ U V a, z'.1 U V a = Φ.φ V (z.1 U V a) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ S S' Φ
  have hres : ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U),
      mp S'.F a (Φ.φ U b) - Φ.φ V (mp S.F a b) ∈ I.map (algebraMap R (S'.F.obj V)) := fun U V a b ↦ by
    rw [← S'.ker V, map_sub, S'.nat a, Φ.red, Φ.red, S.nat a, sub_self]
  have hcomm : ∀ (U V : AffOp X₀) (a : U ⟶ V) (x : S.F.obj U), x ∈ I.map (algebraMap R (S.F.obj U)) →
      mp S'.F a (Φ.φ U x) = Φ.φ V (mp S.F a x) := fun U V a x hx ↦
    eq_of_sub_mem_map (map_sq hI _) ((mp S'.F a).comp (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U))
      ((Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V).comp (mp S.F a)) (hres U V a) hx
  have c1 : ∀ z : Z1 S.F, S.IsIdealValuedLiftSystemCocycle z → ∃ z' : Z1 S'.F, S'.IsIdealValuedLiftSystemCocycle z' ∧ ∀ U V a, z'.1 U V a = Φ.φ V (z.1 U V a) := by
    intro z hz
    refine ⟨⟨fun U V a ↦ Φ.φ V (z.1 U V a), ?_⟩, fun U V a ↦ ?_, fun _ _ _ ↦ rfl⟩
    · intro U V W a b
      show Φ.φ W (z.1 U W (a ≫ b)) = mp S'.F b (Φ.φ V (z.1 U V a)) + Φ.φ W (z.1 V W b)
      rw [Z1.comp z a b, map_add (f := _), hcomm V W b _ (hz U V a)]
    · exact algHom_apply_mem_map (Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V) (hz U V a)
  have c2 : ∀ g : C0 S.F, S.IsIdealValuedLiftSystemCochain g → ∀ U V a,
      d0 S'.F (fun W ↦ Φ.φ W (g W)) U V a = Φ.φ V (d0 S.F g U V a) := by
    intro g hg U V a
    rw [amitsur_d0_apply, amitsur_d0_apply, map_sub, hcomm U V a _ (hg U)]
  refine ⟨c1, c2, fun c hc ↦ ?_⟩
  refine Submodule.smul_induction_on hc ?_ ?_
  · intro r hr c₀ _
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c₀
    let z : Z1 S.F := r • (S.coef hI).pullbackOneCocycle f
    have hzI : S.IsIdealValuedLiftSystemCocycle z := fun U V a ↦ by
      show r • (show S.F.obj V from ev f ((S.thick hI).map a)) ∈ I.map (algebraMap R (S.F.obj V))
      rw [Algebra.smul_def, mul_comm]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hr)
    obtain ⟨z', -, hz'⟩ := c1 z hzI
    refine ⟨z, z', hzI, ?_, ?_, hz'⟩
    · show H1.mk _ (r • _) = S.r hI (r • H1.mk _ f)
      rw [map_smul, map_smul]
      rfl
    · rw [map_smul, show S'.r hI (H1.mk _ f) = H1.mk _ ((S'.coef hI).pullbackOneCocycle f) from rfl, ← map_smul,
        H1.mk_eq_mk]
      let ΦH : ∀ W : AffOp X₀, S.thickObj hI W ⟶ S'.thickObj hI W := fun W ↦
        S.thickHom S' hI (𝟙 W) (Φ.φ W : S.F.obj W →ₐ[R] S'.F.obj W)
          (fun b ↦ (Φ.red W b).trans (mp_id (OAff s₀) W (S.p W b)).symm)
      refine ⟨fun W ↦ -(r • @id (S'.F.obj W) (ev f (ΦH W))), ?_⟩
      funext U V a
      have hz'' := hz' U V a
      have e1 : @id (S'.F.obj V) (ev f (ΦH U ≫ (S'.thick hI).map a)) =
          mp S'.F a (@id (S'.F.obj U) (ev f (ΦH U))) + @id (S'.F.obj V) (ev f ((S'.thick hI).map a)) :=
        ev_comp f (ΦH U) ((S'.thick hI).map a)
      have e2 : @id (S'.F.obj V) (ev f ((S.thick hI).map a ≫ ΦH V)) =
          Φ.φ V (@id (S.F.obj V) (ev f ((S.thick hI).map a))) + @id (S'.F.obj V) (ev f (ΦH V)) :=
        ev_comp f ((S.thick hI).map a) (ΦH V)
      have e3 : algebraMap R (S'.F.obj V) r * (@id (S'.F.obj V) (ev f ((S.thick hI).map a ≫ ΦH V)) -
          @id (S'.F.obj V) (ev f (ΦH U ≫ (S'.thick hI).map a))) = 0 := by
        obtain ⟨⟨Q, hQ⟩, tay⟩ := _root_.GlobalTheory.LiftSys.Taylor.ev_sub_ev_eq R R₀ I hI π hπ hk X₀ s₀ S S' U V
        obtain ⟨θ, hθ, -⟩ := (_root_.GlobalTheory.LiftSys.theta_classify R R₀ (S.F.obj U) (Sec s₀ U.unop.1) (S'.F.obj V) I hI π hπ (S.p U)
          (S.semi U) (S.surj U) (S.ker U) ((mp S'.F a).comp (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U))).1
          ((Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V).comp (mp S.F a)) (hres U V a)
        have t := tay Q hQ (ΦH U ≫ (S'.thick hI).map a) ((S.thick hI).map a ≫ ΦH V) θ hθ f
        have t' : @id (S'.F.obj V) (ev f ((S.thick hI).map a ≫ ΦH V)) -
            @id (S'.F.obj V) (ev f (ΦH U ≫ (S'.thick hI).map a)) ∈ I.map (algebraMap R (S'.F.obj V)) := by
          rw [show @id (S'.F.obj V) (ev f ((S.thick hI).map a ≫ ΦH V)) -
            @id (S'.F.obj V) (ev f (ΦH U ≫ (S'.thick hI).map a)) = _ from t]
          exact hθ.mem _
        exact mul_eq_zero_of_mem_sqMap (map_sq hI _) (Ideal.mem_map_of_mem _ hr) t'
      show -(r • @id (S'.F.obj V) (ev f (ΦH V))) - mp S'.F a (-(r • @id (S'.F.obj U) (ev f (ΦH U)))) =
        z'.1 U V a - r • @id (S'.F.obj V) (ev f ((S'.thick hI).map a))
      rw [hz'']
      show _ = Φ.φ V (r • @id (S.F.obj V) (ev f ((S.thick hI).map a))) - _
      rw [map_neg, map_smul, map_smul]
      simp only [Algebra.smul_def]
      linear_combination -(algebraMap R (S'.F.obj V) r) * (e1 - e2) - e3
  · rintro x y ⟨z₁, z₁', h₁, hx₁, hx₁', e₁⟩ ⟨z₂, z₂', h₂, hy₂, hy₂', e₂⟩
    refine ⟨z₁ + z₂, z₁' + z₂', fun U V a ↦ ?_, ?_, ?_, fun U V a ↦ ?_⟩
    · show z₁.1 U V a + z₂.1 U V a ∈ _
      exact Ideal.add_mem _ (h₁ U V a) (h₂ U V a)
    · rw [map_add (f := _), map_add (f := _), hx₁, hy₂]
    · rw [map_add (f := _), map_add (f := _), hx₁', hy₂']
    · show z₁'.1 U V a + z₂'.1 U V a = Φ.φ V (z₁.1 U V a + z₂.1 U V a)
      rw [map_add (f := _), e₁, e₂]

end GlobalTheory.LiftSys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardSmallSectionsGeOfShiftNef
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem log_ncard_ball_one_ge_of_shift_nef : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (a c : ℤ) (M : HermLB p) (α t₀ : ℝ), P.Rep a c M → M.IsSelfInter α → (M.shift (fun _ => t₀) fun _ => rfl).IsNef D → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (α / (D + 1).factorial - ε) * (m : ℝ) ^ (D + 1) ≤ P.lc (m * a) (m * c) 1 := by
  intro hHS hAC k _ X _ p D hX P b s t hG a c M α t₀ hRep hSI hNef ε hε
  exact _root_.GlobalTheory.VolBr.log_ncard_ball_one_eventually_ge X.functionField (fun m : ℕ => P.H (m * a) (m * c)) (fun m : ℕ => P.Bl (m * a) (m * c))
    (D + 1) (Nat.succ_pos D) (fun m => _root_.GlobalTheory.VolBr.Pair.isBallFam k X p P _ _)
    (fun m R => _root_.GlobalTheory.VolBr.BallFinite.bl_finite hHS k X p D hX P b s t hG _ _ R hAC)
    (α / (D + 1).factorial) ((D + 1) * gdeg M D / (D + 1).factorial) t₀
    (fun t ht => _root_.GlobalTheory.VolBr.lc_tendsto_of_rep hHS hAC k X p D hX P a c M α t₀ hRep hSI hNef t ht) ε hε

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelLocalRingEssFiniteTypeInt
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc

namespace GlobalTheory.Izumi

theorem essFiniteType_int_O : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω)
    (x : M.Z), Algebra.EssFiniteType ℤ (M.O x) := by
  intro o Ω _ _ _ hA M x
  haveI : LocallyOfFiniteType M.s := M.lft
  let y : PrimeSpectrum o := M.s x
  letI A : Algebra o ((Sp o).presheaf.stalk (M.s x)) := StructureSheaf.stalkAlgebra _ y
  haveI : @IsLocalization.AtPrime o _ ((Sp o).presheaf.stalk (M.s x)) _ A y.asIdeal _ :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := @algebraMap o ((Sp o).presheaf.stalk (M.s x)) _ _ A
  have h₁ : (M.s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap M.s x
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  haveI : Algebra.FiniteType ℤ o := hA.ft
  have h₀ : (algebraMap ℤ o).EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
  have h₃ : (M.stalkEquiv x).toRingHom.EssFiniteType :=
    (RingHom.FiniteType.of_surjective _ (M.stalkEquiv x).surjective).essFiniteType
  have h := ((h₀.comp h₂).comp h₁)
  have h' := h.comp h₃
  rw [← RingHom.essFiniteType_algebraMap]
  convert h'
  exact RingHom.ext_int _ _

end GlobalTheory.Izumi
end

