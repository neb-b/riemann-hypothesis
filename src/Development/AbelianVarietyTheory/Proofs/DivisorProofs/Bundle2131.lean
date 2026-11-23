module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2080
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0053
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0690
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0694
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisOfLocalizationsAtPrime
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUnitSmulEqOfBijectiveToSpanSingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2066
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0921
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0450

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidLevelRigid
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleRigid

open GlobalTheory.CechPic GlobalTheory.RealMult


set_option autoImplicit false in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.AmpleRigid.mul_comp_of_grpPullback_id {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G]
    (f : G' ⟶ G) (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G (𝟙 S) f.left) {T : Over S} (x y : T ⟶ G') :
    (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
  have H := h.2 T x y
  revert H
  generalize hg : T.hom ≫ 𝟙 S = g
  rw [Category.comp_id] at hg
  subst hg
  intro H
  exact Over.OverMorphism.ext (H (x ≫ f) (y ≫ f) rfl rfl).symm


set_option autoImplicit false in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.AmpleRigid.isMonHom_of_mul_comp {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H]
    (e : G ⟶ H) (mul : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ e = (x ≫ e) * (y ≫ e)) :
    IsMonHom e := by
  have hone : (1 : 𝟙_ (Over S) ⟶ G) ≫ e = 1 := by
    have h1 := mul (𝟙_ (Over S)) 1 1
    rw [_root_.mul_one] at h1
    exact _root_.left_eq_mul.mp h1
  refine ⟨?_, ?_⟩
  · simpa [Hom.one_def] using hone
  · have h2 := mul (G ⊗ G) (fst G G) (snd G G)
    simpa [Hom.mul_def] using h2

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem pull_cls_diag {S : Scheme.{0}} (X : Obj F 𝔠 S) (ψ : X.A.left ⟶ X.A.left) (hψ : X.IsPullBy X (𝟙 _) ψ)
    (c : 𝔠.elt) :
    pull ψ (cls (X.diag c) (pull_isLB (X.isLB c) _)) = cls (X.diag c) (pull_isLB (X.isLB c) _) := by
  obtain ⟨φ₂, hsq, hiso⟩ := hψ.pol
  have hw : ψ ≫ X.A.hom = X.A.hom := by simpa using hψ.grp.1.w
  have hw2 : φ₂ ≫ (X.A ⊗ X.A).hom = (X.A ⊗ X.A).hom := by
    calc φ₂ ≫ (X.A ⊗ X.A).hom = φ₂ ≫ (fst X.A X.A).left ≫ X.A.hom := by rw [Over.w]
      _ = (fst X.A X.A).left ≫ ψ ≫ X.A.hom := by rw [← Category.assoc, hsq.1, Category.assoc]
      _ = (X.A ⊗ X.A).hom := by rw [hw, Over.w]
  let Ψ : X.A ⟶ X.A := Over.homMk ψ hw
  let Φ : X.A ⊗ X.A ⟶ X.A ⊗ X.A := Over.homMk φ₂ hw2
  have e : Ψ ≫ lift (𝟙 X.A) (𝟙 X.A) = lift (𝟙 X.A) (𝟙 X.A) ≫ Φ := by
    apply CartesianMonoidalCategory.hom_ext
    · apply Over.OverMorphism.ext
      simp only [Category.assoc, lift_fst, Category.comp_id, Over.comp_left]
      rw [show Φ.left = φ₂ from rfl, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst]
      rfl
    · apply Over.OverMorphism.ext
      simp only [Category.assoc, lift_snd, Category.comp_id, Over.comp_left]
      rw [show Φ.left = φ₂ from rfl, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd]
      rfl
  have e' : ψ ≫ (lift (𝟙 X.A) (𝟙 X.A)).left = (lift (𝟙 X.A) (𝟙 X.A)).left ≫ φ₂ := congrArg (·.left) e
  have h1 : pull φ₂ (cls (X.P c) (X.isLB c)) = cls (X.P c) (X.isLB c) :=
    ((cls_eq_iff (X.isLB c) (pull_isLB (X.isLB c) φ₂)).2 (hiso c)).symm
  unfold Obj.diag
  rw [cls_pull (X.isLB c), ← pull_comp, e', pull_comp, h1]

end GlobalTheory.AmpleRigid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidSeparated
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleRigid

open GlobalTheory.CechPic GlobalTheory.EffBound

theorem pull_one_left_eq_zero {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] (c : Pic A.left) :
    pull (1 : A ⟶ A).left c = 0 := by
  have h : pull (η[A] : 𝟙_ (Over (Sp K)) ⟶ A).left c = 0 := GlobalTheory.ThetaExtend.pic_local (R := K) _
  rw [Hom.one_def, Over.comp_left, pull_comp, h, map_zero]

theorem choose_two_succ (n : ℕ) : (n + 1).choose 2 = n + n.choose 2 := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right]

theorem pull_pow_left (hcube : CubeSt) {K : Type} [Field K] [IsAlgClosed K] {A : Over (Sp K)} [GrpObj A]
    [IsCommMonObj A] (hA : IsAbelianScheme A) (L : LB A.left) (hL : L.IsLB) (hamp : Out.RelAmple A L)
    (c : Pic A.left) (ψ : A ⟶ A) (n : ℕ) :
    pull (ψ ^ n).left c = (((n + 1).choose 2 : ℕ) : ℤ) • pull ψ.left c + ((n.choose 2 : ℕ) : ℤ) • pull ψ⁻¹.left c := by
  have hrec : ∀ n : ℕ, pull (ψ ^ (n + 2)).left c + pull (ψ ^ n).left c =
      2 • pull (ψ ^ (n + 1)).left c + pull ψ.left c + pull ψ⁻¹.left c := by
    intro n
    have h := hcube K A hA L hL hamp c (ψ ^ (n + 1)) ψ ψ⁻¹
    have e1 : ψ ^ (n + 1) * ψ * ψ⁻¹ = ψ ^ (n + 1) := mul_inv_cancel_right _ _
    have e2 : ψ ^ (n + 1) * ψ = ψ ^ (n + 2) := (pow_succ _ _).symm
    have e3 : ψ ^ (n + 1) * ψ⁻¹ = ψ ^ n := by rw [pow_succ, mul_inv_cancel_right]
    have e4 : ψ * ψ⁻¹ = 1 := mul_inv_cancel _
    rw [e1, e2, e3, e4, pull_one_left_eq_zero, add_zero, add_zero] at h
    rw [two_nsmul]
    exact h.symm
  have key : ∀ n : ℕ, (pull (ψ ^ n).left c = (((n + 1).choose 2 : ℕ) : ℤ) • pull ψ.left c +
      ((n.choose 2 : ℕ) : ℤ) • pull ψ⁻¹.left c) ∧ (pull (ψ ^ (n + 1)).left c =
      (((n + 1 + 1).choose 2 : ℕ) : ℤ) • pull ψ.left c + (((n + 1).choose 2 : ℕ) : ℤ) • pull ψ⁻¹.left c) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [pow_zero, pull_one_left_eq_zero]; simp
      · rw [pow_one]; simp
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h := eq_sub_of_add_eq (hrec n)
      rw [show n + 1 + 1 = n + 2 from rfl, h, ih.1, ih.2]
      rw [show n + 2 + 1 = n + 1 + 1 + 1 from rfl, choose_two_succ (n + 1 + 1), choose_two_succ (n + 1),
        choose_two_succ n]
      push_cast
      module
  exact (key n).1

theorem separatedSt_of_const_cube : ConstSt → CubeSt → SeparatedSt := by
  intro hconst hcube K _ _ A _ _ hA L hL hamp Q hQ u hu
  haveI := GlobalTheory.isIntegral_of_isAbelianScheme_field K A hA
  obtain ⟨d, hd, n0, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy K A L hL).1 hamp
  have heff : ∀ φ : A.left ⟶ A.left, Eff (pull φ ((d : ℤ) • cls L hL)) := by
    intro φ
    rw [← cls_pw hL (d : ℤ)]
    exact eff_pull_of_veryAmpleBy K A.hom _ n0 s _ hs φ inferInstance
  have heffn : ∀ (φ : A.left ⟶ A.left) (j : ℕ), 1 ≤ j → Eff ((j : ℤ) • pull φ ((d : ℤ) • cls L hL)) := by
    intro φ j hj
    induction j, hj using Nat.le_induction with
    | base => simpa using heff φ
    | succ j hj ih =>
      push_cast
      rw [add_zsmul, one_zsmul]
      exact eff_add _ _ ih (heff φ)
  obtain ⟨t₀, ht₀⟩ := hconst K A hA L hL hamp ((d : ℤ) • pull u.left (cls L hL))
  have hN : t₀ + 2 < Q ^ (t₀ + 2) := Nat.lt_pow_self (by omega)
  obtain ⟨ψ, hψ, rfl⟩ := hu (t₀ + 2)
  have hpow := pull_pow_left hcube hA L hL hamp (cls L hL) ψ (Q ^ (t₀ + 2))
  have hψ1 : ψ = 1 := by
    refine ht₀ (d * (Q ^ (t₀ + 2) + 1).choose 2) ?_ ψ hψ ?_
    · have h1 : Q ^ (t₀ + 2) ≤ (Q ^ (t₀ + 2) + 1).choose 2 := by
        rw [choose_two_succ]; omega
      have h2 : (Q ^ (t₀ + 2) + 1).choose 2 ≤ d * (Q ^ (t₀ + 2) + 1).choose 2 :=
        Nat.le_mul_of_pos_left _ hd
      omega
    · have hb : 1 ≤ (Q ^ (t₀ + 2)).choose 2 := Nat.choose_pos (by omega)
      have e : (d : ℤ) • pull (ψ ^ (Q ^ (t₀ + 2))).left (cls L hL) -
          (d * (Q ^ (t₀ + 2) + 1).choose 2) • pull ψ.left (cls L hL) =
          (((Q ^ (t₀ + 2)).choose 2 : ℕ) : ℤ) • pull ψ⁻¹.left ((d : ℤ) • cls L hL) := by
        rw [hpow, map_zsmul, ← natCast_zsmul]
        push_cast
        module
      rw [e]
      exact heffn _ _ hb
  rw [hψ1, one_pow]

end GlobalTheory.AmpleRigid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveAffineOpenFlatBaseChangeProper
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.AffInj

theorem inr_injective_of_isPushout {R A K P : CommRingCat.{0}} {φ : R ⟶ A} {ψ : R ⟶ K}
    {inl : A ⟶ P} {inr : K ⟶ P} (H : IsPushout φ ψ inl inr) (hφ : Function.Injective φ.hom)
    (hψ : ψ.hom.Flat) : Function.Injective inr.hom := by
  algebraize [φ.hom, ψ.hom]
  let e := (CommRingCat.isPushout_tensorProduct R A K).isoIsPushout _ _ H
  have h1 : inr = _ ≫ e.hom :=
    (IsPushout.inr_isoIsPushout_hom _ _ (CommRingCat.isPushout_tensorProduct R A K) H).symm
  rw [h1, CommRingCat.hom_comp, RingHom.coe_comp]
  refine (ConcreteCategory.injective_of_mono_of_preservesPullback e.hom).comp ?_
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := K)
    (Algebra.linearMap R A) hφ
  intro a b hab
  apply (TensorProduct.lid R K).symm.injective
  apply hinj
  simpa using hab

end GlobalTheory.AffInj

namespace GlobalTheory.AffInj

theorem app_injective_of_isPullback (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R)
    (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S) (hπ : IsProper π) (hy : Flat y)
    (H : IsPullback p q y π) (hinj : Function.Injective π.appTop.hom) (V : Y.Opens)
    (hV : IsAffineOpen V) : Function.Injective (p.app V).hom := by
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace π
  have hUY : p ⁻¹ᵁ V = q ⁻¹ᵁ ⊤ ⊓ p ⁻¹ᵁ V := by simp
  have hST : V ≤ y ⁻¹ᵁ ⊤ := le_top
  have hSX : (⊤ : S.Opens) ≤ π ⁻¹ᵁ ⊤ := le_top
  let σ := pushoutSection H.flip hST hSX hUY
  have hm : Mono σ := mono_pushoutSection_of_isCompact_of_flat_right H.flip hST hSX hUY
    (isAffineOpen_top _) hV (by simpa using isCompact_univ)
  have hσ : Function.Injective σ.hom := (ConcreteCategory.mono_iff_injective_of_preservesPullback σ).mp hm
  have h1 : pushout.inr _ _ ≫ σ = p.appLE V (p ⁻¹ᵁ V) le_rfl := pushout.inr_desc _ _ _
  have hφ : Function.Injective (π.appLE ⊤ ⊤ hSX).hom := by
    have e : π.appLE ⊤ ⊤ hSX = π.appTop := (Scheme.Hom.app_eq_appLE π (U := ⊤)).symm
    rw [e]; exact hinj
  have hinr := inr_injective_of_isPushout (IsPushout.of_hasPushout (π.appLE ⊤ ⊤ hSX)
    (y.appLE ⊤ V hST)) hφ (y.flat_appLE (isAffineOpen_top _) hV _)
  have h2 : p.app V = p.appLE V (p ⁻¹ᵁ V) le_rfl := Scheme.Hom.app_eq_appLE p
  rw [h2, ← h1, CommRingCat.hom_comp, RingHom.coe_comp]
  exact hσ.comp hinr

end GlobalTheory.AffInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveDescentOfAffineOpens
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.Glue

theorem app_map {Y Z : Scheme.{0}} (p : Z ⟶ Y) {U V : Y.Opens} (i : U ⟶ V) (a : Γ(Y, V)) :
    (p.app U).hom ((Y.presheaf.map i.op).hom a) =
      (Z.presheaf.map (homOfLE (p.preimage_mono i.le)).op).hom ((p.app V).hom a) := by
  rw [← CommRingCat.comp_apply, p.naturality, CommRingCat.comp_apply]
  rfl

theorem map_map {X : Scheme.{0}} {U V W : X.Opens} (i : V ⟶ U) (j : W ⟶ V) (x : Γ(X, U)) :
    (X.presheaf.map j.op).hom ((X.presheaf.map i.op).hom x) =
      (X.presheaf.map (homOfLE (j.le.trans i.le)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem le_iSup_affine (Y : Scheme.{0}) (V : Y.Opens) :
    V ≤ ⨆ U : {U : Y.affineOpens // U.1 ≤ V}, U.1.1 := by
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, hUV⟩, hxU⟩

theorem le_iSup_preimage_affine {Y Z : Scheme.{0}} (p : Z ⟶ Y) (V : Y.Opens) :
    p ⁻¹ᵁ V ≤ ⨆ U : {U : Y.affineOpens // U.1 ≤ V}, p ⁻¹ᵁ U.1.1 := by
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, hUV⟩, hxU⟩

end GlobalTheory.Mum.Glue

namespace GlobalTheory.Mum

theorem app_injective_and_descent_of_affineOpens : ∀ (Y Z : Scheme.{0}) (p : Z ⟶ Y), (∀ V : Y.Opens, IsAffineOpen V → (Function.Injective (p.app V).hom ∧ ∀ f : Γ(Z, p ⁻¹ᵁ V), (∀ h : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V), ((pullback.fst p p).app _).hom f = ((pullback.snd p p).appLE _ _ h.ge).hom f) → f ∈ Set.range (p.app V).hom)) → ∀ V : Y.Opens, (Function.Injective (p.app V).hom ∧ ∀ f : Γ(Z, p ⁻¹ᵁ V), (∀ h : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V), ((pullback.fst p p).app _).hom f = ((pullback.snd p p).appLE _ _ h.ge).hom f) → f ∈ Set.range (p.app V).hom) := by
  intro Y Z p H
  have inj : ∀ W : Y.Opens, Function.Injective (p.app W).hom := by
    intro W a b hab
    refine Y.sheaf.eq_of_locally_eq' (fun U : {U : Y.affineOpens // U.1 ≤ W} ↦ U.1.1) W
      (fun U ↦ homOfLE U.2) (Glue.le_iSup_affine Y W) a b fun U ↦ ?_
    apply (H U.1.1 U.1.2).1
    show (p.app _).hom ((Y.presheaf.map (homOfLE U.2).op).hom a) =
      (p.app _).hom ((Y.presheaf.map (homOfLE U.2).op).hom b)
    rw [Glue.app_map, Glue.app_map, hab]
  intro V
  refine ⟨inj V, fun f hf ↦ ?_⟩
  have hV : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    show (pullback.snd p p ≫ p) ⁻¹ᵁ V = (pullback.fst p p ≫ p) ⁻¹ᵁ V
    rw [pullback.condition]
  have hf' := hf hV
  have hU : ∀ U : {U : Y.affineOpens // U.1 ≤ V}, ∃ g : Γ(Y, U.1.1), (p.app U.1.1).hom g =
      (Z.presheaf.map (homOfLE (p.preimage_mono U.2)).op).hom f := by
    intro U
    apply (H U.1.1 U.1.2).2
    intro h'
    rw [Glue.app_map, hf', ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, ← CommRingCat.comp_apply,
      Scheme.Hom.map_appLE]
  choose g hg using hU
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun U : {U : Y.affineOpens // U.1 ≤ V} ↦ U.1.1) V
    (fun U ↦ homOfLE U.2) (Glue.le_iSup_affine Y V) g (by
      intro U U'
      apply inj
      show (p.app _).hom ((Y.presheaf.map _).hom (g U)) = (p.app _).hom ((Y.presheaf.map _).hom (g U'))
      rw [Glue.app_map, Glue.app_map, hg, hg, Glue.map_map, Glue.map_map])
  refine ⟨s, ?_⟩
  refine Z.sheaf.eq_of_locally_eq' (fun U : {U : Y.affineOpens // U.1 ≤ V} ↦ p ⁻¹ᵁ U.1.1) (p ⁻¹ᵁ V)
    (fun U ↦ homOfLE (p.preimage_mono U.2)) (Glue.le_iSup_preimage_affine p V) _ _ fun U ↦ ?_
  have e := Glue.app_map p (homOfLE U.2) s
  have hsU : (Y.presheaf.map (homOfLE U.2).op).hom s = g U := hs U
  rw [hsU, hg] at e
  exact e.symm

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem jK_appTop_injective (R : Type) [CommRing R] [IsDomain R] :
    Function.Injective (jK R).appTop.hom := by
  intro a b h
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom h
  have h3 : ∀ x, (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom ((jK R).appTop.hom x) =
      algebraMap R (FractionRing R) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) := fun x =>
    congrArg (fun f => f.hom x) e
  rw [h3, h3] at h2
  have h4 := IsFractionRing.injective R (FractionRing R) h2
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h4
  simpa using this

theorem Modif.gp_appTop_injective {R : Type} [CommRing R] [IsDomain R] (M : Modif R) :
    Function.Injective M.gp.appTop.hom := by
  haveI := M.integral
  haveI := M.dominant
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro s hs
  rw [← AlgebraicGeometry.basicOpen_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨y, hy⟩ := M.gp.denseRange.exists_mem_open (M.S.basicOpen s).isOpen ⟨x, hx⟩
  have : y ∈ M.gp ⁻¹ᵁ M.S.basicOpen s := hy
  rw [Scheme.preimage_basicOpen_top, hs, Scheme.basicOpen_zero] at this
  exact absurd this (by simp)

theorem Modif.appTop_comp {R : Type} [CommRing R] [IsDomain R] (M : Modif R) (a : Γ(Sp R, ⊤)) :
    M.gp.appTop.hom (M.π.appTop.hom a) = (jK R).appTop.hom a := by
  rw [← M.gp_π, Scheme.Hom.comp_appTop]
  rfl

theorem Modif.appTop_bijective_surjective : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (M : Modif R), Function.Bijective M.π.appTop.hom ∧ Surjective M.π := by
  intro R _ _ _ _ M
  haveI := M.proper
  haveI := M.integral
  have hinj : Function.Injective M.π.appTop.hom := fun a b h => jK_appTop_injective R (by
    rw [← M.appTop_comp, ← M.appTop_comp, h])
  refine ⟨⟨hinj, fun b => ?_⟩, ⟨?_⟩⟩
  ·
    obtain ⟨p, hpm, hp⟩ := isIntegral_appTop_of_universallyClosed M.π b
    let eR := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
    let eK := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv
    have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    have h3 : ∀ x, eK ((jK R).appTop.hom x) = algebraMap R (FractionRing R) (eR x) := fun x =>
      congrArg (fun f => f.hom x) e
    have hc : IsIntegral R (eK (M.gp.appTop.hom b)) := by
      refine ⟨p.map eR.toRingHom, hpm.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have : (algebraMap R (FractionRing R)).comp eR.toRingHom =
          (eK.toRingHom.comp M.gp.appTop.hom).comp M.π.appTop.hom := by
        ext x
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
        rw [M.appTop_comp, h3]
      rw [this]
      calc _ = (eK.toRingHom.comp M.gp.appTop.hom) (p.eval₂ M.π.appTop.hom b) :=
            (Polynomial.hom_eval₂ _ _ _ _).symm
        _ = 0 := by rw [hp, map_zero]
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hc
    refine ⟨eR.symm r, M.gp_appTop_injective (eK.injective ?_)⟩
    rw [M.appTop_comp, h3, RingEquiv.apply_symm_apply, hr]
  ·
    have hcl : IsClosed (Set.range M.π) := (M.π.isClosedMap).isClosed_range
    have hd : Dense (Set.range (jK R)) := (Modif.self R).dominant.denseRange
    have hsub : Set.range (jK R) ⊆ Set.range M.π := by
      rintro _ ⟨y, rfl⟩
      exact ⟨M.gp y, by rw [← Scheme.Hom.comp_apply, M.gp_π]⟩
    have := (hd.mono hsub).closure_eq
    rw [hcl.closure_eq] at this
    exact Set.range_eq_univ.1 this

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopInjectiveOfSurjectiveIntegralToSpecDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem appTop_injective_of_surjective_toSpec_domain :
    ∀ (R : Type) [CommRing R] [IsDomain R] (S : Scheme.{0}) (π : S ⟶ Sp R),
      Surjective π → IsIntegral S → Function.Injective π.appTop.hom := by
  intro R _ _ S π hπ hS
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro r hr
  have h1 : π ⁻¹ᵁ (Sp R).basicOpen r = ⊥ := by
    rw [Scheme.preimage_basicOpen_top, hr, Scheme.basicOpen_zero]
  rw [← basicOpen_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := hπ.surj x
  have hy : y ∈ π ⁻¹ᵁ (Sp R).basicOpen r := hx
  rw [h1] at hy
  exact hy.elim

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalancedSymmetricPairMatrixHorizontalSingleStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.balancedSymmetricPairMatrix_horizontal_single : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} (ε : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw), ∃ κ : Fin Dw.dim ≃ HIx Dw (psiSet H), ∀ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (j : Fin Dw.dim) (k : HIx Dw (psiSet H)), f (GlobalTheory.LogKSDiv.symPair (R := R) e (ε j) (e ⟨k.1.1, k.2.2⟩) (e ⟨conjEmb k.1.1, k.2.1⟩)) = (Pi.single (κ j) (1 : S) : HIx Dw (psiSet H) → S) k := by
  first | exact @GlobalTheory.LogKSDiv.PairEntry.symPair_horizontal_single | exact GlobalTheory.LogKSDiv.PairEntry.symPair_horizontal_single | (intros; apply GlobalTheory.LogKSDiv.PairEntry.symPair_horizontal_single <;> assumption)
end

