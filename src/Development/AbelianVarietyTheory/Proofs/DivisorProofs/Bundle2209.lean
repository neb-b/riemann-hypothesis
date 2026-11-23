module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0194
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
public import Formalism.SharpRestriction.Divisibility.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackCompositionCompatible
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

variable {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]

theorem functionFieldMap_comp_dominant (s : Y ⟶ X) [IsDominant s] (t : Z ⟶ Y) [IsDominant t] :
    functionFieldMap (t ≫ s) = (functionFieldMap t).comp (functionFieldMap s) := by
  ext f
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective
    (A := X.presheaf.stalk ((t ≫ s) (genericPoint Z))) f
  have key : ∀ c : X.presheaf.stalk ((t ≫ s) (genericPoint Z)),
      functionFieldMap (t ≫ s) (algebraMap _ X.functionField c) =
        functionFieldMap t (functionFieldMap s (algebraMap _ X.functionField c)) := by
    intro c
    have h1 := functionFieldMap_algebraMap (t ≫ s) (genericPoint Z) c
    have h2 := functionFieldMap_algebraMap s (t (genericPoint Z)) c
    have h3 := functionFieldMap_algebraMap t (genericPoint Z) (s.stalkMap (t (genericPoint Z)) c)
    refine h1.trans (Eq.trans ?_ ((congrArg (functionFieldMap t) h2).trans h3).symm)
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  simp only [map_div₀, RingHom.comp_apply, key]

theorem pullCart_comp (s : Y ⟶ X) [IsDominant s] (t : Z ⟶ Y) [IsDominant t] (D : CartierDiv X) :
    pullCart (t ≫ s) D = pullCart t (pullCart s D) :=
  CartierDiv.ext_of_isEqn fun z => by
    obtain ⟨g, hg⟩ := D.exists_isEqn ((t ≫ s) z)
    refine ⟨_, isEqn_pullCart (t ≫ s) hg, ?_⟩
    have e : fnPull (t ≫ s) g = fnPull t (fnPull s g) :=
      Units.ext (RingHom.congr_fun (functionFieldMap_comp_dominant s t) g)
    rw [e]
    exact isEqn_pullCart t (isEqn_pullCart s hg)

theorem isDivOfForm_ratPull_comp {k : Type} [Field k] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s]
    (t : Z ⟶ Y) [IsDominant t] (n : ℕ) (η : RatForms p n) (K : CartierDiv Z) :
    IsDivOfForm K (EtaleKlt.ratPull p (t ≫ s) n η) ↔
      IsDivOfForm K (EtaleKlt.ratPull (s ≫ p) t n (EtaleKlt.ratPull p s n η)) := by
  have key : ∀ (q q' : Z ⟶ Sp k) (_ : q = q') (φ : X.functionField →+* Z.functionField)
      (h : φ.comp (Cartier.constFn p) = Cartier.constFn q) (h' : φ.comp (Cartier.constFn p) = Cartier.constFn q'),
      IsDivOfForm (p := q) K (TopForm.formMap n φ h η) ↔
        IsDivOfForm (p := q') K (TopForm.formMap n φ h' η) := by
    intro q q' e φ h h'
    subst e
    rfl
  have h' : (functionFieldMap (t ≫ s)).comp (Cartier.constFn p) = Cartier.constFn (t ≫ s ≫ p) := by
    rw [EtaleKlt.functionFieldMap_comp_constFn, Category.assoc]
  have e : EtaleKlt.ratPull (s ≫ p) t n (EtaleKlt.ratPull p s n η) =
      TopForm.formMap n (functionFieldMap (t ≫ s)) h' η :=
    formMap_formMap _ _ _ (functionFieldMap_comp_dominant s t).symm _ _ _ η
  rw [e]
  exact key _ _ (Category.assoc t s p) _ _ h'

theorem pull_comp : ∀ (k : Type) [Field k] (X Y Z : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s] (t : Z ⟶ Y) [IsDominant t], functionFieldMap (t ≫ s) = (functionFieldMap t).comp (functionFieldMap s) ∧ (∀ D : CartierDiv X, pullCart (t ≫ s) D = pullCart t (pullCart s D)) ∧ ∀ (n : ℕ) (η : RatForms p n) (K : CartierDiv Z), IsDivOfForm K (EtaleKlt.ratPull p (t ≫ s) n η) ↔ IsDivOfForm K (EtaleKlt.ratPull (s ≫ p) t n (EtaleKlt.ratPull p s n η)) :=
  fun _ _ _ _ _ _ _ _ p s _ t _ =>
    ⟨functionFieldMap_comp_dominant s t, pullCart_comp s t, isDivOfForm_ratPull_comp p s t⟩

end GlobalTheory.Discrepancy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackNonzeroSectionInjectiveDomainMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.PullNonzero

theorem eq_zero_of_dominant {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {ψ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L ψ ε)) (h : Y' ⟶ Y) [IsSchemeTheoreticallyDominant h] [QuasiCompact h]
    (h0 : ∀ y J, Good L y J → sval s h y J = 0) (j : K → L.ι) : s.f j = 0 := by
  refine h.app_injective (LB.wchart L ψ j) (Eq.trans ?_ (map_zero (h.app (LB.wchart L ψ j)).hom).symm)
  refine fn_ext fun y hy => ?_
  choose I hI using fun χ : Y' ⟶ X => exists_chart hL (χ y)
  have e₁ := gs_pull (𝟙 Y') h y (LB.wchart L ψ j) hy (s.f j)
  rw [Category.id_comp] at e₁
  have e₂ := sec_trans s h y (j := j) hy (Good.mem hI ψ h)
  have e₃ : gs h y _ _ = 0 := h0 y I hI
  rw [e₃, MulZeroClass.mul_zero] at e₂
  refine (e₁.trans e₂).trans ?_
  rw [gs_eq _ y _ hy, map_zero, map_zero]

theorem sval_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {ψ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L ψ ε)) (h0 : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval s r z J = 0 := by
  refine (congrArg (gs r z (LB.wchart L ψ (fun k => J (r ≫ ψ k)))) (h0 _)).trans ((gs_eq r z _ (hJ.mem ψ r) _).trans ?_)
  exact (congrArg _ (map_zero _)).trans (map_zero _)

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V) (D' : DegPre V) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (U' : GlobalTheory.UU.PreU (maximalIdeal V) D' A' G') (F : G'.left ⟶ G.left) (C : GlobalTheory.LN.Cmp φ U U' F), GlobalTheory.LN.CDvr V → Function.Injective φ → ∀ (σ : U.SecGT (𝟙_ _) 1) (σ' : U'.SecGT (𝟙_ _) 1), (∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left), r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' → sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))).val ^ 1 * sval σ' r' z J') → (∃ j, σ.f j ≠ 0) → ∃ j, σ'.f j ≠ 0 := by
  intro R _ _ _ _ D A G _ _ U V _ _ _ φ D' A' G' _ _ U' F C _ hφ σ σ' H ⟨j, hj⟩
  by_contra h0
  push Not at h0
  have hs := U.semi.smooth
  have : Flat G.hom := inferInstance
  have : IsDominant (spMap φ) := by
    refine ⟨?_⟩
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2
      (by rw [(RingHom.injective_iff_ker_eq_bot φ).1 hφ]; exact bot_le)
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap φ)
  have : IsSchemeTheoreticallyDominant F := IsSchemeTheoreticallyDominant.of_isPullback C.pb.1.flip
  have : QuasiCompact F := MorphismProperty.of_isPullback (P := @QuasiCompact) C.pb.1.flip inferInstance
  have e : ∀ {S : Scheme.{0}} (B : Over S), (λ_ B).inv.left ≫ (snd _ B).left = 𝟙 _ := fun B =>
    congrArg (fun q => q.left) (leftUnitor_inv_snd B)
  have : IsIso (λ_ G).inv.left := inferInstanceAs (IsIso ((Over.forget _).map (λ_ G).inv))
  refine hj (eq_zero_of_dominant U.P.L.isLB σ (F ≫ (λ_ G).inv.left) (fun y J hJ => ?_) j)
  choose J' hJ' using fun χ : G'.left ⟶ G'.left => exists_chart U'.P.L.isLB (χ y)
  have e₁ := H _ (λ_ G').inv.left (F ≫ (λ_ G).inv.left)
    (by rw [Category.assoc, e, ← Category.assoc, e, Category.id_comp, Category.comp_id]) y J J' hJ hJ'
  rw [sval_zero σ' h0 _ y hJ', MulZeroClass.mul_zero] at e₁
  exact e₁

end GlobalTheory.PullNonzero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackTwistedSectionIso
section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.Twist

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CutPull

variable {X Y : Scheme.{0}} (f : Y ⟶ X) {L : LB X}

theorem homEquiv_pullbackZIso_hom (hL : L.IsLB) (G : X.Modules) (n : ℤ) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackZIso G f hL n).hom =
      Twist.map (lbZPow L n) ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G) ≫
        (projZIso f hL ((Scheme.Modules.pullback f).obj G) n).inv := by
  have e : (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (twist G (lbZPow L n)) ≫
      (Scheme.Modules.pushforward f).map (pullbackHom G (lbZPow L n) f) =
        Twist.map (lbZPow L n) ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G) ≫
          (projIso (lbZPow L n) f _).inv :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)
  rw [Adjunction.homEquiv_unit, pullbackZIso, Iso.trans_hom, Functor.map_comp, ← Category.assoc,
    pullbackIso_hom, e, projZIso, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_hom, Category.assoc]

theorem pullback_mulSecOfEq (hL : L.IsLB) (G : X.Modules) {n m k : ℤ} (σ : LB.Sec (lbZPow L m))
    (h : n + m = k) :
    (Scheme.Modules.pullback f).map (mulSecOfEq G σ h) ≫ (pullbackZIso G f hL k).hom =
      (pullbackZIso G f hL n).hom ≫ mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zpull f σ) h := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    homEquiv_pullbackZIso_hom, homEquiv_pullbackZIso_hom, Category.assoc]
  have e : (Scheme.Modules.pushforward f).map
      (mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zpull f σ) h) ≫
        (projZIso f hL ((Scheme.Modules.pullback f).obj G) k).hom =
      (projZIso f hL ((Scheme.Modules.pullback f).obj G) n).hom ≫
        mulSecOfEq ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj G)) σ h := by
    refine zhom_ext fun V (s : Γ(twistZ ((Scheme.Modules.pullback f).obj G) (L.pull f) n, f ⁻¹ᵁ V)) i => ?_
    refine (zcoord_projZIso_hom_app f hL _ ((mulSecOfEq _ (zpull f σ) h).app _ s) i).trans ?_
    refine Eq.trans ?_ (zcoord_mulSecOfEq_app σ h ((projZIso f hL _ n).hom.app V s) i).symm
    have e : (f.app (V ⊓ L.U i)).hom (resG X inf_le_right (zfun σ i)) =
        (f.appLE (L.U i) _ (f.preimage_mono (inf_le_right : V ⊓ L.U i ≤ L.U i))).hom (zfun σ i) := by
      rw [← Scheme.Hom.appLE_eq_app, LB.appLE_resG]
    rw [zcoord_mulSecOfEq_app, resM_smul, resG_resG, zfun_zpull, LB.resG_appLE]
    refine Eq.trans (congrArg (· • resM _ (le_pidx_inf f V i) (zcoord s (pidx L f i))) e.symm) ?_
    exact congrArg (fun t : Γ((Scheme.Modules.pullback f).obj G, f ⁻¹ᵁ (V ⊓ L.U i)) =>
      (f.app (V ⊓ L.U i)).hom (resG X inf_le_right (zfun σ i)) • t)
      (zcoord_projZIso_hom_app f hL _ s i).symm
  have e' : (projZIso f hL ((Scheme.Modules.pullback f).obj G) n).inv ≫
      (Scheme.Modules.pushforward f).map (mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zpull f σ) h) =
        mulSecOfEq ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj G)) σ h ≫
          (projZIso f hL ((Scheme.Modules.pullback f).obj G) k).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact e
  rw [e', ← Category.assoc, ← Category.assoc]
  congr 1
  symm
  refine zhom_ext fun V s i => ?_
  change zcoord ((mulSecOfEq _ σ h).app V ((Twist.map (lbZPow L n) _).app V s)) i =
    zcoord ((Twist.map (lbZPow L k) _).app V ((mulSecOfEq G σ h).app V s)) i
  rw [zcoord_mulSecOfEq_app, zcoord_map_app, zcoord_map_app, zcoord_mulSecOfEq_app,
    Scheme.Modules.Hom.app_smul]

end GlobalTheory.CutPull

namespace GlobalTheory


open GlobalTheory.CutPull in
theorem cut_pullback_iso : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) (G : X.Modules) [G.IsQuasicoherent] {L : LB X} (hL : L.IsLB) (s : L.Sec) (hL' : (L.pull f).IsLB), Nonempty ((Scheme.Modules.pullback f).obj (cut G hL s) ≅ cut ((Scheme.Modules.pullback f).obj G) hL' (secPull s f)) := by
  intro X Y f G _ L hL s hL'
  have : PreservesColimits (Scheme.Modules.pullback f) :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits
  have hz : ∀ j, zfun (zpull f (zofSec s)) j = zfun (zofSec (secPull s f)) j := fun j => by
    rw [zfun_zpull, zfun_zofSec, zfun_zofSec]
    rfl
  have hM : mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zpull f (zofSec s)) (neg_add_cancel (1 : ℤ)) =
      mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zofSec (secPull s f)) (neg_add_cancel (1 : ℤ)) :=
    zhom_ext fun V t j => by rw [zcoord_mulSecOfEq_app, zcoord_mulSecOfEq_app, hz]
  have e := pullback_mulSecOfEq f hL G (zofSec s) (neg_add_cancel (1 : ℤ))
  rw [hM, ← Iso.eq_comp_inv] at e
  have key : (Scheme.Modules.pullback f).map (cutHom G hL s) =
      (pullbackZIso G f hL (-1)).hom ≫
        (mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zofSec (secPull s f)) (neg_add_cancel (1 : ℤ)) ≫
          ((pullbackZIso G f hL 0).symm ≪≫ (Scheme.Modules.pullback f).mapIso (twistZZeroIso G hL).symm).hom) := by
    rw [cutHom, Functor.map_comp, e]
    simp
  exact ⟨PreservesCokernel.iso (Scheme.Modules.pullback f) (cutHom G hL s) ≪≫ cokernelIsoOfEq key ≪≫
    cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _ ≪≫
    (cokernelCompIsIso _ (twistZZeroIso ((Scheme.Modules.pullback f).obj G) hL').inv).symm⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseIsogenyPairBaseChangeGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.UPel.HT.ES

theorem pullQuasiInv : ∀ (T Y : Scheme.{0}) (t : T ⟶ Y) (A B : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) (A₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] (φ : A₁.left ⟶ A.left), IsAbelianScheme B → IsQuasiInv k ψ ψ' → IsGrpPullback A₁ A t φ → ∃ (B₁ : Over T) (_ : GrpObj B₁) (_ : IsCommMonObj B₁) (θ : B₁.left ⟶ B.left) (ψ₁ : A₁ ⟶ B₁) (ψ₁' : B₁ ⟶ A₁), IsAbelianScheme B₁ ∧ IsGrpPullback B₁ B t θ ∧ IsQuasiInv k ψ₁ ψ₁' ∧ φ ≫ ψ.left = ψ₁.left ≫ θ ∧ θ ≫ ψ'.left = ψ₁'.left ≫ φ := by
  intro T Y t A B _ _ _ _ k ψ ψ' A₁ _ _ φ hB hq hA
  obtain ⟨hψ, hψ', h1, h2⟩ := hq
  obtain ⟨e, he, hφ⟩ := grpPullback_iso hA (isGrpPullback_pullback A t)
  have hinv : IsMonHom e.inv := inferInstance
  have hinvφ : e.inv.left ≫ φ = pullback.fst A.hom t := by
    rw [← hφ, ← Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left, Category.id_comp]
  have hmap : ∀ (X M : Over Y) [MonObj M] (f : X ⟶ M) (n : ℕ),
      (Over.pullback t).map (f ^ n) = ((Over.pullback t).map f) ^ n := fun X M _ f n => by
    rw [← Functor.homMonoidHom_apply, map_pow, Functor.homMonoidHom_apply]
  have hid : ∀ (M : Over Y) [GrpObj M], (Over.pullback t).map ((𝟙 M) ^ k) = (𝟙 _) ^ k := fun M _ => by
    rw [hmap, CategoryTheory.Functor.map_id]
  refine ⟨(Over.pullback t).obj B, inferInstance, inferInstance, pullback.fst B.hom t,
    e.hom ≫ (Over.pullback t).map ψ, (Over.pullback t).map ψ' ≫ e.inv,
    ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t B hB, isGrpPullback_pullback B t, ⟨inferInstance, inferInstance, ?_, ?_⟩, ?_, ?_⟩
  · calc (e.hom ≫ (Over.pullback t).map ψ) ≫ (Over.pullback t).map ψ' ≫ e.inv
          = e.hom ≫ (Over.pullback t).map (ψ ≫ ψ') ≫ e.inv := by simp
      _ = e.hom ≫ ((𝟙 ((Over.pullback t).obj A)) ^ k) ≫ e.inv := by rw [h1, hid]
      _ = (𝟙 A₁) ^ k := by
        rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, e.hom_inv_id]
  · calc ((Over.pullback t).map ψ' ≫ e.inv) ≫ e.hom ≫ (Over.pullback t).map ψ
          = (Over.pullback t).map (ψ' ≫ ψ) := by simp
      _ = (𝟙 _) ^ k := by rw [h2, hid]
  · rw [Over.comp_left, Category.assoc]
    show φ ≫ ψ.left = e.hom.left ≫ pullback.lift _ _ _ ≫ pullback.fst B.hom t
    rw [pullback.lift_fst, ← Category.assoc, hφ]
  · rw [Over.comp_left, Category.assoc, hinvφ]
    show pullback.fst B.hom t ≫ ψ'.left = pullback.lift _ _ _ ≫ pullback.fst A.hom t
    rw [pullback.lift_fst]

end GlobalTheory.UPel.HT.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientPointCharacterValuePowIsUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.UnramCharPow

open GlobalTheory.TorusExt GlobalTheory.BXOf GlobalTheory.UnramTorsion

attribute [local instance] gtGroup

theorem charVal_pow_unit : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Subring F) [IsLocalRing T] (φ₁ : R →+* T), (∀ r, (φ₁ r : F) = algebraMap (FractionRing R) F (algebraMap R _ r)) → ∀ (J₀ : D.P.A.left → D.P.L.ι), (∀ x, x ∈ D.P.L.U (J₀ x)) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → (∀ ψ : Sp T ⟶ D.P.A.left, J (spMap T.subtype ≫ ψ) = J₀ (ψ (closedPoint T))) → (∀ χ, ∃ u : Tˣ, (GlobalTheory.BXOf.sig F (val (D.psi χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F) J) : F) = ((u : T) : F)) → ∀ (k : ℕ) (p : QkPt D F k) (b : Sp T ⟶ D.P.A.left), spMap T.subtype ≫ b = p.g.b.left → b ≫ D.P.A.hom = spMap φ₁ → ∀ χ, ∃ u : Tˣ, (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal p.g χ (closedPoint F) J) : F) ^ k = ((u : T) : F) := by
  intro R _ _ D hB F _ _ T _ φ₁ hφ J₀ h₀ J hJ eJ hψ k p b hb hbA χ
  let H : Subgroup Fˣ := (Units.map T.subtype.toMonoidHom).range
  let w : ((TF (R := R) F).left.presheaf.stalk (closedPoint F))ˣ →* Fˣ ⧸ H :=
    (QuotientGroup.mk' H).comp (sig F)
  let ρ : TF (R := R) F ⟶ Over.mk (spMap φ₁) := Over.homMk (spMap T.subtype) (by
    show spMap T.subtype ≫ spMap φ₁ = jFK (R := R) F ≫ jK R
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hφ)
  let b' : Over.mk (spMap φ₁) ⟶ D.P.A := Over.homMk b hbA
  have hb' : ρ ≫ b' = p.g.b := Over.OverMorphism.ext hb
  have mem : ∀ s : ((TF (R := R) F).left.presheaf.stalk (closedPoint F))ˣ,
      (∃ u : Tˣ, (sig F s : F) = ((u : T) : F)) → w s = 1 := fun s ⟨u, hu⟩ => by
    show (QuotientGroup.mk' H) (sig F s) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨u, Units.ext hu.symm⟩
  have hw : ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ D.P.A.left)) (ε : K → ℤ)
      (t : LB.Gen (LB.LinComb D.P.L φ ε)) (r : (Over.mk (spMap φ₁)).left ⟶ Y),
      w (val t (ρ.left ≫ r) (closedPoint F) J) = 1 := by
    intro Y K _ φ ε t r
    exact mem _ (val_integral T.subtype h₀ eJ t r)
  have e₁ := w_nsmul ρ hJ w hw p.g b' hb' χ k
  obtain ⟨g, hg, hi⟩ := p.eq
  have hp : k • p.g = g := ((isNsmul_iff_eq _ _ _).1 hg).symm
  have hv : charVal g χ (closedPoint F) J = tauVal D F p.y χ (closedPoint F) J :=
    ((isIota_iff _ _).1 hi).2 χ (closedPoint F) J hJ
  rw [hp, hv, w_tau ρ hJ w hw, mem _ (hψ _), mem _ (hψ _), mem _ (hψ _)] at e₁
  simp only [inv_one, _root_.mul_one] at e₁
  have e₂ : (QuotientGroup.mk' H) (sig F (charVal p.g χ (closedPoint F) J) ^ k) = 1 := by
    rw [map_pow]; exact e₁.symm
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at e₂
  obtain ⟨u, hu⟩ := e₂
  exact ⟨u, by rw [← Units.val_pow_eq_pow_val, ← hu]; rfl⟩

end GlobalTheory.UnramCharPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientPointsFiniteRepresentatives
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum

theorem qkPt_finite_reps : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), k ≠ 0 → Finite {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} → ∃ Rep : Set (QkPt D F k), Rep.Finite ∧ ∀ p : QkPt D F k, ∃ p' ∈ Rep, ∃ (z : D.X) (t : GtPtF D F), t.b = 1 ∧ (letI := GlobalTheory.TorusExt.gtGroup D F; k • t = 0 ∧ p.g = p'.g + GlobalTheory.TorusExt.iota hB F z + t) := by
  intro R _ _ D hB F _ _ k hk hfin
  letI := GlobalTheory.TorusExt.gtGroup D F
  classical
  by_cases hne : Nonempty (QkPt D F k)
  swap
  · exact ⟨∅, Set.finite_empty, fun p => (hne ⟨p⟩).elim⟩
  let K : AddSubgroup D.X := (nsmulAddMonoidHom (α := D.X) k).range
  haveI : K.FiniteIndex := ⟨by
    simp only [K, AddSubgroup.index_range_nsmul]; exact pow_ne_zero _ hk⟩
  haveI : Finite (D.X ⧸ K) := AddSubgroup.finite_quotient_of_finiteIndex
  let Q : QkPt D F k → D.X ⧸ K := fun p => (p.y : D.X ⧸ K)
  let bp : D.X ⧸ K → QkPt D F k := Function.invFun Q
  have hbp : ∀ p, Q (bp (Q p)) = Q p := fun p => Function.invFun_eq ⟨p, rfl⟩
  have hz : ∀ p, ∃ z : D.X, k • z = -(bp (Q p)).y + p.y := by
    intro p
    have h := QuotientAddGroup.eq.mp (hbp p)
    obtain ⟨z, hz⟩ := AddMonoidHom.mem_range.mp h
    exact ⟨z, by simpa using hz⟩
  let zOf : QkPt D F k → D.X := fun p => (hz p).choose
  have hzOf : ∀ p, k • zOf p = -(bp (Q p)).y + p.y := fun p => (hz p).choose_spec
  let δ : QkPt D F k → GtPtF D F := fun p =>
    p.g - (bp (Q p)).g - GlobalTheory.TorusExt.iota hB F (zOf p)
  have hδk : ∀ p, k • δ p = 0 := by
    intro p
    simp only [δ, smul_sub, GlobalTheory.TorusExt.qk_nsmul hB, ← map_nsmul, hzOf]
    rw [map_add (f := _), map_neg]; abel
  have hδb : ∀ p, (δ p).b ^ k = 1 := by
    intro p
    rw [← GlobalTheory.TorusExt.nsmul_b, hδk p, GlobalTheory.TorusExt.zero_b]
  let Φ : QkPt D F k → (D.X ⧸ K) × {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} :=
    fun p => (Q p, ⟨(δ p).b, hδb p⟩)
  let rep : (D.X ⧸ K) × {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} → QkPt D F k :=
    Function.invFun Φ
  have hrep : ∀ p, Φ (rep (Φ p)) = Φ p := fun p => Function.invFun_eq ⟨p, rfl⟩
  refine ⟨Set.range (rep ∘ Φ), ?_, ?_⟩
  · rw [Set.range_comp]; exact (Set.toFinite _).image _
  intro p
  set p' := rep (Φ p) with hp'
  have h1 : Q p' = Q p := congrArg Prod.fst (hrep p)
  have h2 : (δ p').b = (δ p).b := congrArg (fun x => x.2.1) (hrep p)
  refine ⟨p', ⟨p, rfl⟩, zOf p - zOf p', δ p - δ p', ?_, ?_, ?_⟩
  · rw [sub_eq_add_neg, GlobalTheory.TorusExt.add_b, GlobalTheory.TorusExt.neg_b, h2, mul_inv_cancel]
  · rw [smul_sub, hδk, hδk, sub_zero]
  · have hb : bp (Q p') = bp (Q p) := by rw [h1]
    simp only [δ, hb, map_sub]
    abel

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackBijectiveBirational
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TopForm

theorem bijective_formMap_of_bijective {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    {α : k →+* A} {β : k →+* B} (D : ℕ) (ρ : A →+* B) (h : ρ.comp α = β)
    (hρ : Function.Bijective ρ) : Function.Bijective (TopForm.formMap D ρ h) := by
  let e : A ≃+* B := RingEquiv.ofBijective ρ hρ
  let σ : B →+* A := e.symm.toRingHom
  have e1 : σ.comp ρ = RingHom.id A := RingHom.ext fun a => e.symm_apply_apply a
  have e2 : ρ.comp σ = RingHom.id B := RingHom.ext fun b => e.apply_symm_apply b
  have h' : σ.comp β = α := by
    rw [← h, ← RingHom.comp_assoc, e1, RingHom.id_comp]
  refine Function.bijective_iff_has_inverse.mpr ⟨TopForm.formMap D σ h', fun x => ?_, fun y => ?_⟩
  · rw [formMap_formMap ρ σ (RingHom.id A) e1 h h' (RingHom.id_comp α)]
    exact formMap_of_eq_id _ rfl _ x
  · rw [formMap_formMap σ ρ (RingHom.id B) e2 h' h (RingHom.id_comp β)]
    exact formMap_of_eq_id _ rfl _ y

end GlobalTheory.TopForm

namespace GlobalTheory.EtaleKlt

theorem ratPull_bijective_of_birational : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X]
    [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s],
    Function.Bijective (functionFieldMap s) → ∀ n : ℕ,
      Function.Bijective (EtaleKlt.ratPull p s n) := by
  intro k _ X Y _ _ p s _ hs n
  exact TopForm.bijective_formMap_of_bijective n _ (functionFieldMap_comp_constFn p s) hs

end GlobalTheory.EtaleKlt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsAdditiveLineBundleFamiliesCompareStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representsAdditiveLineBundleFamilies_compare : ∀ (S : Scheme.{0}) (A B' S' C Z : Over S) [GrpObj A] (b' : B' ⟶ S') (P' : LB (A ⊗ B').left) (e : C ⟶ Z) (Q : LB (A ⊗ C).left), GlobalTheory.DualCon.Rep A b' P' → GlobalTheory.DualCon.Rep A e Q → ∃ q : B' ⊗ Z ⟶ C, q ≫ e = snd B' Z ∧ IsPullback q.left (fst B' Z ≫ b').left C.hom S'.hom ∧ Same A P' Q (fst B' Z) q := by
  first | exact @GlobalTheory.Pinch.rep_cmp | exact GlobalTheory.Pinch.rep_cmp | (intros; apply GlobalTheory.Pinch.rep_cmp <;> assumption)
end

