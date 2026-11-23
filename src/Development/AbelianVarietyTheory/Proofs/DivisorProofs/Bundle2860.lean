module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1451
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1585
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2841
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2555
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreProductAffineOpenClosureLegsEqTop
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BaseChangeAffine

theorem closure_range_union_eq_top_of_isPushout {A B C P : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C}
    {i : B ⟶ P} {j : C ⟶ P} (h : IsPushout f g i j) :
    Subring.closure (Set.range i.hom ∪ Set.range j.hom) = ⊤ := by
  set R := Subring.closure (Set.range i.hom ∪ Set.range j.hom)
  let l : B ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (i.hom.codRestrict R fun b => Subring.subset_closure (Or.inl ⟨b, rfl⟩))
  let r : C ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (j.hom.codRestrict R fun c => Subring.subset_closure (Or.inr ⟨c, rfl⟩))
  have w : f ≫ l = g ≫ r := by
    ext a
    have := congrArg (fun q : A ⟶ P => q.hom a) h.w
    simpa [l, r] using this
  let s : CommRingCat.of R ⟶ P := CommRingCat.ofHom R.subtype
  have hid : h.desc l r w ≫ s = 𝟙 P := by
    apply h.hom_ext
    · ext b; simp [l, s]
    · ext c; simp [r, s]
  refine eq_top_iff.2 fun x _ => ?_
  have hx : (((h.desc l r w).hom x : R) : P) = x := by
    have := congrArg (fun q : P ⟶ P => q.hom x) hid
    simpa [s] using this
  rw [← hx]
  exact ((h.desc l r w).hom x).2

theorem affine_and_closure_eq_top : ∀ (Z Z' X X' : Scheme.{0}) (p : Z ⟶ X) (p' : Z' ⟶ X') (φ : Z' ⟶ Z) (g : X' ⟶ X), IsPullback φ p' p g → ∀ (U : X.affineOpens) (U' : X'.affineOpens), U'.1 ≤ g ⁻¹ᵁ U.1 → ∀ (O : Z.affineOpens), O.1 ≤ p ⁻¹ᵁ U.1 → IsAffineOpen (φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) ∧ Subring.closure (Set.range (φ.appLE O.1 (φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) inf_le_left).hom ∪ Set.range (p'.appLE U'.1 (φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) inf_le_right).hom) = ⊤ := by
  intro Z Z' X X' p p' φ g H U U' hU' O hO
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine U'.1.toScheme := U'.2
  have : IsAffine O.1.toScheme := O.2
  have hpb := Scheme.Hom.isPullback_resLE H (US := U.1) (UT := U'.1) (UX := O.1)
    (UY := φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) hU' hO rfl
  refine ⟨.of_isIso hpb.isoPullback.hom, ?_⟩
  have po := (isIso_pushoutSection_iff H hU' hO (UY := φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) rfl).1
    (isIso_pushoutSection_of_isAffineOpen H hU' hO rfl U.2 U'.2 O.2)
  exact closure_range_union_eq_top_of_isPushout po

end GlobalTheory.BaseChangeAffine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderLiftDerivationCommTranslations
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KS.LiftComm

theorem appLE_congr {Z X : Scheme.{0}} {k k' : Z ⟶ X} (h : k = k') (U : X.Opens) (V : Z.Opens)
    (e : V ≤ k ⁻¹ᵁ U) (e' : V ≤ k' ⁻¹ᵁ U) : k.appLE U V e = k'.appLE U V e' := by
  subst h; rfl

theorem pbT_of_le {Z Y : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (s : Γ(Y, O₀)) (O : Z.Opens)
    (h : O ≤ f ⁻¹ᵁ O₀) : pbT f s O = (f.appLE O₀ O h).hom s := by
  unfold pbT; rw [dite_eq_left h]

theorem ext_of_opens {Z X : Scheme.{0}} {a b : Z ⟶ X} (hb : a.base = b.base) (O : X.Opens → Z.Opens)
    (hO : ∀ U, O U = b ⁻¹ᵁ U)
    (h : ∀ U (e1 : O U ≤ a ⁻¹ᵁ U) (e2 : O U ≤ b ⁻¹ᵁ U), a.appLE U (O U) e1 = b.appLE U (O U) e2) :
    a = b := by
  refine GlobalTheory.KS.DerMorK.hom_ext_appLE hb fun U e => ?_
  have key : ∀ V (_ : V = O U) (e1 : V ≤ a ⁻¹ᵁ U) (e2 : V ≤ b ⁻¹ᵁ U), a.appLE U V e1 = b.appLE U V e2 := by
    intro V hV e1 e2; subst hV; exact h U e1 e2
  rw [key _ (hO U).symm e le_rfl, Scheme.Hom.appLE_eq_app]

theorem translate_comm : ∀ (k : Type) [Field k] (Y Y' X : Scheme.{0}) (m : Y ⟶ X) (π : Y' ⟶ Sp (DualNumber k)) (ρ' : Y' ⟶ Y) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)) (Φ : Y' ⟶ X), (∀ y, Φ y = m (ρ' y)) → (∀ (W : X.Opens) (f : Γ(X, W)), pbT Φ f (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W)) = pbT (ρ' ≫ m) f (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W)) + constFn π (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W)) DualNumber.eps * pbT ρ' (d W f) (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W))) → ∀ (T : X ⟶ X) (T₀ : Y ⟶ Y) (TY : Y' ⟶ Y'), T₀ ≫ m = m ≫ T → TY ≫ ρ' = ρ' ≫ T₀ → TY ≫ π = π → (∀ (W : X.Opens) (f : Γ(X, W)), d (T ⁻¹ᵁ W) ((T.app W).hom f) = pbT T₀ (d W f) (m ⁻¹ᵁ (T ⁻¹ᵁ W))) → TY ≫ Φ = Φ ≫ T := by
  intro k _ Y Y' X m π ρ' d Φ hb hΦ T T₀ TY h₀ h₁ h₂ hd
  have hcomp : TY ≫ ρ' ≫ m = ρ' ≫ m ≫ T := by
    rw [← Category.assoc, h₁, Category.assoc, h₀]
  have hbase : (TY ≫ Φ).base = (Φ ≫ T).base := by
    ext y
    have e := congrArg (fun g => g.base y) hcomp
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at e ⊢
    rw [hb, hb, e]
  have hle : ∀ (Z : Scheme.{0}) (V : X.Opens) (g : Z ⟶ Y'), g ⁻¹ᵁ ρ' ⁻¹ᵁ m ⁻¹ᵁ V ≤ g ⁻¹ᵁ Φ ⁻¹ᵁ V := by
    intro Z V g y hy
    show Φ.base (g.base y) ∈ V
    rw [hb]; exact hy
  refine ext_of_opens hbase (fun W => ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) (fun W => ?_) (fun W e1 e2 => ?_)
  · exact le_antisymm (hle Y' (T ⁻¹ᵁ W) (𝟙 _)) (by
      intro y hy
      show T.base (m.base (ρ'.base y)) ∈ W
      rw [← hb]; exact hy)
  · ext f
    have hO' : ρ' ⁻¹ᵁ m ⁻¹ᵁ W ≤ Φ ⁻¹ᵁ W := hle Y' W (𝟙 _)
    have e' : ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W ≤ TY ⁻¹ᵁ ρ' ⁻¹ᵁ m ⁻¹ᵁ W :=
      le_of_eq (congrArg (fun g => g ⁻¹ᵁ W) hcomp.symm)
    have e2' : ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W ≤ Φ ⁻¹ᵁ T ⁻¹ᵁ W := hle Y' (T ⁻¹ᵁ W) (𝟙 _)
    have hT0 : m ⁻¹ᵁ T ⁻¹ᵁ W ≤ T₀ ⁻¹ᵁ m ⁻¹ᵁ W := le_of_eq (congrArg (fun g => g ⁻¹ᵁ W) h₀.symm)
    have hL : ((TY ≫ Φ).appLE W _ e1).hom f = (TY.appLE _ _ e').hom ((Φ.appLE W _ hO').hom f) := by
      rw [← Scheme.Hom.appLE_comp_appLE TY Φ W _ _ hO' e']; rfl
    have hR : ((Φ ≫ T).appLE W _ e2).hom f = (Φ.appLE (T ⁻¹ᵁ W) _ e2').hom ((T.app W).hom f) := by
      rw [Scheme.Hom.app_eq_appLE, ← Scheme.Hom.appLE_comp_appLE Φ T W (T ⁻¹ᵁ W) _ le_rfl e2']; rfl
    rw [hL, hR, ← pbT_of_le Φ f _ hO', ← pbT_of_le Φ _ _ e2', hΦ, hΦ, map_add (f := _), map_mul,
      GlobalTheory.KS.DerMorK.appLE_constFn, h₂, hd]
    have a1 : pbT (ρ' ≫ m) f (ρ' ⁻¹ᵁ m ⁻¹ᵁ W) = ((ρ' ≫ m).appLE W (ρ' ⁻¹ᵁ m ⁻¹ᵁ W) le_rfl).hom f :=
      pbT_of_le _ _ _ _
    have a2 : pbT ρ' (d W f) (ρ' ⁻¹ᵁ m ⁻¹ᵁ W) = (ρ'.appLE (m ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ W) le_rfl).hom (d W f) :=
      pbT_of_le _ _ _ _
    have a3 : pbT (ρ' ≫ m) ((T.app W).hom f) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) =
        ((ρ' ≫ m).appLE (T ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) le_rfl).hom ((T.app W).hom f) :=
      pbT_of_le _ _ _ _
    have a4 : pbT T₀ (d W f) (m ⁻¹ᵁ T ⁻¹ᵁ W) = (T₀.appLE (m ⁻¹ᵁ W) (m ⁻¹ᵁ T ⁻¹ᵁ W) hT0).hom (d W f) :=
      pbT_of_le _ _ _ _
    have a5 : ∀ x : Γ(Y, m ⁻¹ᵁ T ⁻¹ᵁ W), pbT ρ' x (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) =
        (ρ'.appLE (m ⁻¹ᵁ T ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) le_rfl).hom x :=
      fun x => pbT_of_le _ _ _ _
    rw [a1, a2, a3, a4, a5]
    congr 1
    · have c1 := Scheme.Hom.appLE_comp_appLE TY (ρ' ≫ m) W (ρ' ⁻¹ᵁ m ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) le_rfl e'
      have c2 := Scheme.Hom.appLE_comp_appLE (ρ' ≫ m) T W (T ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) le_rfl le_rfl
      have c3 := appLE_congr (hcomp.trans (Category.assoc _ _ _).symm) W (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W)
        (le_of_eq (congrArg (fun g => g ⁻¹ᵁ W) hcomp.symm)) le_rfl
      rw [Scheme.Hom.app_eq_appLE]
      exact (congr(($c1).hom f)).trans ((congr(($c3).hom f)).trans (congr(($c2).hom f)).symm)
    · congr 1
      have c1 := Scheme.Hom.appLE_comp_appLE TY ρ' (m ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) le_rfl e'
      have c2 := Scheme.Hom.appLE_comp_appLE ρ' T₀ (m ⁻¹ᵁ W) (m ⁻¹ᵁ T ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) hT0 le_rfl
      have c3 := appLE_congr h₁ (m ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W)
        (le_trans e' le_rfl) (le_trans le_rfl (ρ'.preimage_mono hT0))
      exact (congr(($c1).hom (d W f))).trans ((congr(($c3).hom (d W f))).trans (congr(($c2).hom (d W f))).symm)

end GlobalTheory.KS.LiftComm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupPullbackAbelianSchemeDualNumberEq
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualRigidityField

theorem subsingleton_sp_dualNumber (K : Type) [Field K] : Subsingleton (Sp (DualNumber K)) := by
  have h : ∀ p : PrimeSpectrum (DualNumber K),
      p.asIdeal = IsLocalRing.maximalIdeal (DualNumber K) := by
    intro p
    refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun x hx => ?_
    have hn : IsNilpotent x := by
      rw [TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst]
      have : ¬ IsUnit x.fst := fun hu => hx (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hu)
      have h0 : x.fst = 0 := by simpa using this
      rw [h0]; exact IsNilpotent.zero
    obtain ⟨n, hn⟩ := hn
    exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)
  exact ⟨fun p q => PrimeSpectrum.ext ((h p).trans (h q).symm)⟩

theorem eq_of_eq_closedFibre {K : Type} [Field K] (A' G' : Over (Sp (DualNumber K))) [GrpObj A'] [GrpObj G']
    (a b : A' ⟶ G') (hA : IsAbelianScheme A')
    (hab : pullback.fst A'.hom (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ a.left =
      pullback.fst A'.hom (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ b.left)
    (hη : η[A'] ≫ a = η[A'] ≫ b) : a = b := by
  haveI := subsingleton_sp_dualNumber K
  let j := pullback.fst A'.hom (spMap (TrivSqZeroExt.fstHom K K K).toRingHom)
  have hj : IsPullback j (pullback.snd A'.hom (spMap (TrivSqZeroExt.fstHom K K K).toRingHom)) A'.hom
      (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := IsPullback.of_hasPullback _ _
  let c : A' ⟶ G' := a * b⁻¹
  let j' : Over.mk (j ≫ A'.hom) ⟶ A' := Over.homMk j rfl
  have h1 : j' ≫ a = j' ≫ b := Over.OverMorphism.ext hab
  have h2 : j' ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, h1, mul_inv_cancel]
  have h3 : η[A'] ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, hη, mul_inv_cancel]
  obtain ⟨t₀⟩ : Nonempty (Sp K) := inferInstance
  let t : Sp (DualNumber K) := spMap (TrivSqZeroExt.fstHom K K K).toRingHom t₀
  have hc : ∀ x : A'.left, c.left x = (η[G'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ G').left t := by
    intro x
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hj x t₀ (Subsingleton.elim _ _)
    have e : j ≫ c.left = (j' ≫ c).left := rfl
    rw [← Scheme.Hom.comp_apply, e, h2, Hom.one_def, Over.comp_left]
    refine (Scheme.Hom.comp_apply _ _ _).trans ?_
    congr 1
    exact Subsingleton.elim (α := Sp (DualNumber K)) _ _
  have hη' : (η[A'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ A').left ≫ A'.hom = 𝟙 _ := Over.w η[A']
  have key := GlobalTheory.DualRigidity.eq_comp_section_of_const A'.hom _ c.left hη' (GlobalTheory.globalFns_holds _ A' hA).2 _ hc
  have key' : c = toUnit A' ≫ η[A'] ≫ c := Over.OverMorphism.ext key
  rw [h3, MonObj.comp_one] at key'
  exact mul_inv_eq_one.1 key'

theorem pullback_eq : ∀ {R : Type} [CommRing R] (k : Type) [Field k] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (f : R →+* DualNumber k) (π₁ π₂ : B'.left ⟶ A.left), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsGrpPullback B' A (spMap f) π₁ → IsGrpPullback B' A (spMap f) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → π₁ = π₂ := by
  intro R _ k _ A _ g B' _ f π₁ π₂ hA hg h1 h2 hx
  have hB := (GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback f A B' π₂ g h2 hA hg).1
  let α : B' ⟶ B' := Over.homMk (h2.1.lift π₁ B'.hom h1.1.w) (h2.1.lift_snd _ _ _)
  have hα : α.left ≫ π₂ = π₁ := h2.1.lift_fst _ _ _
  haveI : IsMonHom α := GlobalTheory.UU.isMonHom_of_over_isMonHom h1 h2 (𝟙 A) α (by rw [hα]; rfl)
  have hα1 : α = 𝟙 B' := by
    refine eq_of_eq_closedFibre B' B' α (𝟙 B') hB ?_ (by rw [IsMonHom.one_hom, Category.comp_id])
    apply h2.1.hom_ext
    · simp only [Category.assoc, Over.id_left, Category.comp_id]
      rw [hα]
      exact hx _ _ _ pullback.condition
    · simp only [Category.assoc, Over.id_left, Category.comp_id]
      rw [Over.w α]
  rw [← hα, hα1, Over.id_left, Category.id_comp]

end GlobalTheory.DualRigidityField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupPullbackTranslationCompEq
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.TranslPull

theorem transl_comp_of_isGrpPullback : ∀ {S S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (x : 𝟙_ (Over S') ⟶ G') (s : 𝟙_ (Over S) ⟶ G), x.left ≫ φ = f ≫ s.left → (lift (toUnit G' ≫ x) (𝟙 G') ≫ μ[G']).left ≫ φ = φ ≫ (lift (toUnit G ≫ s) (𝟙 G) ≫ μ[G]).left := by
  intro S S' G' _ G _ f φ h x s hx
  have hu' : ∀ (Y : Over S'), (toUnit Y).left = Y.hom := fun Y => by
    simpa using Over.w (toUnit Y)
  have hu : ∀ (Y : Over S), (toUnit Y).left = Y.hom := fun Y => by
    simpa using Over.w (toUnit Y)
  have hs : s.left ≫ G.hom = 𝟙 S := by simpa using Over.w s
  let x₀ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk (G'.hom ≫ f ≫ s.left) (by
    simp [hs])
  let y₀ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ (by simpa using h.1.w)
  have key := h.2 G' (toUnit G' ≫ x) (𝟙 G') x₀ y₀ (by
      simp [x₀, hu', hx]) (by simp [y₀])
  have e1 : lift (toUnit G' ≫ x) (𝟙 G') ≫ μ[G'] = (toUnit G' ≫ x) * 𝟙 G' := rfl
  have e2 : x₀ * y₀ = (Over.homMk φ (by simpa using h.1.w) : Over.mk (G'.hom ≫ f) ⟶ G) ≫ (lift (toUnit G ≫ s) (𝟙 G) ≫ μ[G]) := by
    rw [← Category.assoc, comp_lift, Category.comp_id]
    have hx0 : x₀ = ((Over.homMk φ (by simpa using h.1.w) : Over.mk (G'.hom ≫ f) ⟶ G) ≫ toUnit G) ≫ s := by
      apply Over.OverMorphism.ext
      simp [x₀, hu]
    rw [hx0]
    rfl
  rw [e1, ← key, e2]
  rfl
end GlobalTheory.TranslPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGoodReductionOfManyRationalTorsionPoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GoodRedTorsion

def secHom {S T : Scheme.{0}} (f : T ⟶ S) (G : Over S) [GrpObj G] :
    (𝟙_ (Over S) ⟶ G) →* (𝟙_ (Over T) ⟶ (Over.pullback f).obj G) :=
  (GlobalTheory.RedPts.precomp _ (Functor.LaxMonoidal.ε (Over.pullback f))).comp (Over.pullback f).homMonoidHom

theorem secHom_apply {S T : Scheme.{0}} (f : T ⟶ S) (G : Over S) [GrpObj G] (s : 𝟙_ (Over S) ⟶ G) :
    secHom f G s = GlobalTheory.IsogRed.sec f s := rfl

theorem card_le_of_fibres {M N : Type} [CommGroup M] [DecidableEq N] (TF : Finset M) (m c B : ℕ)
    (hT : ∀ a ∈ TF, a ^ m = 1) (F : M → N)
    (hF : ∀ a ∈ TF, ∀ b ∈ TF, F a = F b → a ^ c = b ^ c)
    (hfin : {x : M | x ^ Nat.gcd m c = 1}.Finite) (hB : {x : M | x ^ Nat.gcd m c = 1}.ncard ≤ B) :
    TF.card ≤ B * (TF.image F).card := by
  classical
  refine Finset.card_le_mul_card_image TF B fun y hy => ?_
  obtain ⟨a0, ha0, rfl⟩ := Finset.mem_image.1 hy
  calc (TF.filter fun x => F x = F a0).card ≤ hfin.toFinset.card := by
        refine Finset.card_le_card_of_injOn (fun a => a * a0⁻¹) ?_ ?_
        · intro a ha
          have ha' : a ∈ TF.filter fun x => F x = F a0 := by simpa using ha
          obtain ⟨haT, haF⟩ := Finset.mem_filter.1 ha'
          have h1 : (a * a0⁻¹) ^ m = 1 := by rw [mul_pow, inv_pow, hT a haT, hT a0 ha0]; simp
          have h2 : (a * a0⁻¹) ^ c = 1 := by rw [mul_pow, inv_pow, hF a haT a0 ha0 haF, mul_inv_cancel]
          simpa using pow_gcd_eq_one.2 ⟨h1, h2⟩
        · intro a _ b _ h
          simpa using h
    _ = {x : M | x ^ Nat.gcd m c = 1}.ncard := (Set.ncard_eq_toFinset_card _ hfin).symm
    _ ≤ B := hB

theorem torsion_finite_ncard_le (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) (g : ℕ) (hg : SmoothOfRelativeDimension g A.hom) (d : ℕ) (hd : (d : K) ≠ 0) :
    {x : 𝟙_ (Over (Sp K)) ⟶ A | x ^ d = 1}.Finite ∧
      {x : 𝟙_ (Over (Sp K)) ⟶ A | x ^ d = 1}.ncard ≤ d ^ (2 * g) := by
  have hc := _root_.GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K (AlgebraicClosure K) A hA g hg d hd
  let u : ptOver K (AlgebraicClosure K) ⟶ 𝟙_ (Over (Sp K)) := toUnit _
  have hu : u.left = spMap (algebraMap K (AlgebraicClosure K)) := by simpa using Over.w u
  have hdom : IsDominant (spMap (algebraMap K (AlgebraicClosure K))) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      change RingHom.ker (algebraMap K (AlgebraicClosure K)) ≤ _
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap K (AlgebraicClosure K)).injective]; exact bot_le)⟩
  have : IsProper A.hom := hA.proper
  have hinj : Function.Injective (fun x : 𝟙_ (Over (Sp K)) ⟶ A => u ≫ x) := by
    intro x y h
    have h' : spMap (algebraMap K (AlgebraicClosure K)) ≫ x.left = spMap (algebraMap K (AlgebraicClosure K)) ≫ y.left := by
      rw [← hu]; exact congrArg Over.Hom.left h
    exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp K) A.hom
      ((Over.w x).trans (Over.w y).symm) (spMap (algebraMap K (AlgebraicClosure K))) h')
  have hd0 : d ≠ 0 := by rintro rfl; exact hd Nat.cast_zero
  have hfinB : Finite {x : ptOver K (AlgebraicClosure K) ⟶ A // x ^ d = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hd0)
  let φ : {x : 𝟙_ (Over (Sp K)) ⟶ A | x ^ d = 1} → {x : ptOver K (AlgebraicClosure K) ⟶ A // x ^ d = 1} :=
    fun x => ⟨u ≫ x.1, by rw [← MonObj.comp_pow, x.2, MonObj.comp_one]⟩
  have hφ : Function.Injective φ := fun x y h => Subtype.ext (hinj (congrArg Subtype.val h))
  have : Finite {x : 𝟙_ (Over (Sp K)) ⟶ A | x ^ d = 1} := Finite.of_injective φ hφ
  refine ⟨Set.toFinite _, ?_⟩
  rw [← Nat.card_coe_set_eq, ← hc]
  exact Nat.card_le_card_of_injective φ hφ

end GlobalTheory.GoodRedTorsion

namespace GlobalTheory.GoodRedTorsion

theorem hasGoodReduction_of_torsion : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], GlobalTheory.SS.SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ g : ℕ, SmoothOfRelativeDimension g A.hom → {m : ℕ | (m : ResidueField R) ≠ 0 ∧ Nat.card {x : 𝟙_ (Over (Sp K)) ⟶ A // x ^ m = 1} = m ^ (2 * g)}.Infinite → HasGoodReduction R K A := by
  intro R K _ _ _ _ _ hS A _ _ hA g hg hinf
  obtain ⟨G, inst, hG, he, c, hc, hs⟩ :=
    GlobalTheory.SS.exists_neutral_group_model R K hS A hA (_root_.GlobalTheory.ProjField.isProjBy_of_isAbelianScheme K A hA)
  obtain ⟨hDVR, hHen, hAC, hFR⟩ := hS
  have := hG.1
  have := hG.2.1
  have := hG.2.2.1
  have := GlobalTheory.schemeTheoreticallyDominant_fractionField R K
  have heL : IsIso G.e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map G.e.hom))
  have hgenP : IsProper ((Over.pullback (spMap (algebraMap R K))).obj G.Y).hom := by
    rw [← Over.w G.e.hom]; have := hA.proper; infer_instance
  have hGg : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R K))).obj G.Y).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_horiz_isIso (g := 𝟙 _) ⟨(Over.w G.e.hom).trans (Category.comp_id _).symm⟩) hg
  let ψ : (𝟙_ (Over (Sp R)) ⟶ G.Y) →* (𝟙_ (Over (Sp K)) ⟶ A) :=
    { toFun := fun t => secHom (spMap (algebraMap R K)) G.Y t ≫ G.e.hom
      map_one' := by rw [map_one]; exact MonObj.one_comp _
      map_mul' := fun t t' => by rw [map_mul]; exact MonObj.mul_comp _ _ _ }
  have hψinj : Function.Injective ψ := fun t t' h =>
    GlobalTheory.IsogRed.sec_injective (spMap (algebraMap R K)) ((cancel_mono G.e.hom).1 h)
  have hψ : ∀ a : 𝟙_ (Over (Sp K)) ⟶ A, ∃ t, ψ t = a ^ c := fun a => by
    obtain ⟨s, hs'⟩ := hs a
    refine ⟨s, ?_⟩
    change GlobalTheory.IsogRed.sec _ s ≫ G.e.hom = _
    rw [GlobalTheory.IsogRed.sec_eq_comp _ G.e s (a ^ c) hs', Category.assoc, Iso.inv_hom_id, Category.comp_id]
  choose sA hsA using hψ
  have hred : ∀ t : 𝟙_ (Over (Sp R)) ⟶ G.Y, ∀ n : ℕ, IsUnit (n : R) → t ^ n = 1 →
      secHom (spMap (residue R)) G.Y t = 1 → t = 1 := by
    intro t n hn htn ht
    refine GlobalTheory.RedPts.eq_one_of_pow_of_closedPoint G.Y (𝟙 (Sp R)) hn t htn (Z := Over.mk (spMap (residue R)))
      (Over.homMk (spMap (residue R)) (Category.comp_id _))
      ⟨IsLocalRing.closedPoint _, IsLocalRing.comap_closedPoint (IsLocalRing.residue R)⟩ ?_
    rw [← MonObj.comp_one (Over.homMk (spMap (residue R)) (Category.comp_id _) :
      Over.mk (spMap (residue R)) ⟶ Over.mk (𝟙 (Sp R)))]
    apply Over.OverMorphism.ext
    have e1 := GlobalTheory.IsogRed.sec_left (spMap (residue R)) t
    have e2 := GlobalTheory.IsogRed.sec_left (spMap (residue R)) (1 : 𝟙_ (Over (Sp R)) ⟶ G.Y)
    have e3 : GlobalTheory.IsogRed.sec (spMap (residue R)) t = GlobalTheory.IsogRed.sec (spMap (residue R)) 1 := by
      rw [← secHom_apply, ← secHom_apply, map_one]; exact ht
    change spMap (residue R) ≫ t.left = spMap (residue R) ≫ (1 : 𝟙_ (Over (Sp R)) ⟶ G.Y).left
    rw [← e1, ← e2, e3]
  have hunit : ∀ m : ℕ, (m : ResidueField R) ≠ 0 → IsUnit (m : R) := fun m hm => by
    by_contra h
    exact hm (by rw [← map_natCast (residue R)]; exact (residue_eq_zero_iff _).2 ((mem_maximalIdeal _).2 h))
  have hsp : IsProper (GlobalTheory.SS.spFibre G.Y).hom := by
    refine _root_.GlobalTheory.properOfInfinitelyManyLargeTorsionCounts (ResidueField R) (GlobalTheory.SS.spFibre G.Y) (GlobalTheory.IsogRed.smConn_baseChange _ _ hG) g
      (GlobalTheory.IsogRed.relDim_spFibre (K := K) G.Y hG g hGg) (c ^ (2 * g)) (hinf.mono ?_)
    rintro m ⟨hm, hcard⟩
    refine ⟨hm, ?_⟩
    have hm0 : m ≠ 0 := by rintro rfl; exact hm Nat.cast_zero
    have hmK : (m : K) ≠ 0 := by
      have := ((hunit m hm).map (algebraMap R K)).ne_zero
      rwa [map_natCast] at this
    have hfinT : {x : 𝟙_ (Over (Sp K)) ⟶ A | x ^ m = 1}.Finite := by
      have : Finite {x : 𝟙_ (Over (Sp K)) ⟶ A // x ^ m = 1} :=
        Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hm0)
      exact Set.finite_coe_iff.mp this
    have hTcard : hfinT.toFinset.card = m ^ (2 * g) := by
      rw [← hcard, ← Set.ncard_eq_toFinset_card _ hfinT, ← Nat.card_coe_set_eq]; rfl
    have hT : ∀ a ∈ hfinT.toFinset, a ^ m = 1 := fun a ha => by simpa using ha
    have hsAm : ∀ a : 𝟙_ (Over (Sp K)) ⟶ A, a ^ m = 1 → sA a ^ m = 1 := fun a ha =>
      hψinj (by rw [map_pow, hsA, map_one, ← pow_mul, mul_comm, pow_mul, ha, one_pow])
    classical
    refine ⟨hfinT.toFinset.image fun a => secHom (spMap (residue R)) G.Y (sA a), ?_, ?_⟩
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      rw [← map_pow, hsAm a (hT a ha), map_one]
    · have hd : ((Nat.gcd m c : ℕ) : K) ≠ 0 := by
        obtain ⟨k, hk⟩ := Nat.gcd_dvd_left m c
        intro h0
        apply hmK
        rw [hk, Nat.cast_mul, h0, zero_mul]
      obtain ⟨hfin, hB⟩ := torsion_finite_ncard_le K A hA g hg _ hd
      rw [← hTcard]
      refine card_le_of_fibres _ m c (c ^ (2 * g)) hT _ ?_ hfin
        (hB.trans (Nat.pow_le_pow_left (Nat.le_of_dvd hc (Nat.gcd_dvd_right m c)) _))
      intro a ha b hb hab
      have ht : (sA a * (sA b)⁻¹) ^ m = 1 := by
        rw [mul_pow, inv_pow, hsAm a (hT a ha), hsAm b (hT b hb)]; simp
      have h1 := hred _ m (hunit m hm) ht (by rw [map_mul, map_inv, hab, mul_inv_cancel])
      rw [← hsA a, ← hsA b, mul_inv_eq_one.1 h1]
  have hprop : IsProper G.Y.hom := _root_.GlobalTheory.GoodRedProper.isProper_of_proper_fibres R K G.Y hG hgenP hsp
  exact ⟨G.Y, inst, GlobalTheory.T.isAbelianScheme_of_smConn_of_isProper' _ G.Y hG hprop, G.e, he⟩

end GlobalTheory.GoodRedTorsion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegreeTwoAnyRing
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem primE2_any_ring : PrimitiveExtendedDegTwoVanish := by
  apply GlobalTheory.T.primitive_degree_two_extension
  apply GlobalTheory.T.additiveClassDegreeTwo_structureSheaf_vanish
  intro R _ A _ g hA hs
  exact ⟨(_root_.GlobalTheory.AbCoh.oStr R A g hA hs).1,
    (_root_.GlobalTheory.AbCoh.oStr R A g hA hs).2.1⟩

end GlobalTheory.Obs
end

