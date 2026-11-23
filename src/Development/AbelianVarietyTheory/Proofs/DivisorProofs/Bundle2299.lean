module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2128
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierTrivialization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2221
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2182
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoPullbackOfIsOpenImmersion
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections res_pullbackSections pullbackSections_res
  pullback_map_app_pullbackSections)
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)

namespace GlobalTheory.FlagLocal

variable {X Y S : Scheme.{0}} {A A' A'' E E' : X.Modules}

theorem bijective_pullbackSections (a : Y ⟶ X) [IsOpenImmersion a] (E : X.Modules) {V : X.Opens}
    (hV : V ≤ a.opensRange) {W : Y.Opens} (hW : W = a ⁻¹ᵁ V) :
    Function.Bijective (pullbackSections a E hW.le) := by
  subst hW
  have e := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction a)
    (Scheme.Modules.pullbackPushforwardAdjunction a) E
  have h1 : Function.Bijective (E.presheaf.map (homOfLE (a.image_preimage_le V)).op) :=
    QCoh.res_bijective_of_eq E _ (by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]; exact inf_eq_right.2 hV)
  have h2 := ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.restrictFunctorIsoPullback a).hom.app E).app (a ⁻¹ᵁ V))
  convert h2.comp h1 using 1
  funext s
  exact (resM_self _ _).trans congr(($e).app V s).symm

theorem mem_range_of_pullback (a : Y ⟶ X) [IsOpenImmersion a] (v : A ⟶ E) {V : X.Opens}
    (hV : V ≤ a.opensRange) {W : Y.Opens} (hW : W = a ⁻¹ᵁ V) (t : Γ(E, V))
    (h : ∃ m, ((Scheme.Modules.pullback a).map v).app W m = pullbackSections a E hW.le t) :
    ∃ m, v.app V m = t := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨m, rfl⟩ := (bijective_pullbackSections a A hV hW).2 m
  rw [pullback_map_app_pullbackSections] at hm
  exact ⟨m, (bijective_pullbackSections a E hV hW).1 hm⟩

section Cover

variable {J : Type*} {T : J → Scheme.{0}} (a : ∀ i, T i ⟶ X) [∀ i, IsOpenImmersion (a i)]

variable {G : ∀ i, (T i).Modules} (v : ∀ i, G i ⟶ (Scheme.Modules.pullback (a i)).obj E)


end Cover

end GlobalTheory.FlagLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismDescendsNearFibreRigidity
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MorDesc

theorem factor_of_isIso_appTop {X T A : Scheme.{0}} (f : X ⟶ T) [IsIso f.appTop] [IsAffine A]
    (g : X ⟶ A) : ∃ g₀ : T ⟶ A, f ≫ g₀ = g := by
  refine ⟨T.toSpecΓ ≫ Spec.map (g.appTop ≫ inv f.appTop) ≫ A.isoSpec.inv, ?_⟩
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Category.assoc (Spec.map _),
    ← Spec.map_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id, ← Category.assoc,
    ← Scheme.toSpecΓ_naturality, Category.assoc, ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]

theorem morphism_descends : ∀ (R : Type) [CommRing R] (S Y Z W : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → Function.Bijective π.appTop.hom → Flat y → IsPullback p q y π → ∀ (O : Z.Opens) (h : O.toScheme ⟶ W) (y₀ : Y) (w : W), (∀ z : Z, p z = y₀ → z ∈ O) → (∀ z : O.toScheme, p (O.ι z) = y₀ → h z = w) → ∃ (V : Y.Opens) (hV : p ⁻¹ᵁ V ≤ O) (h₀ : V.toScheme ⟶ W), y₀ ∈ V ∧ (p ∣_ V) ≫ h₀ = Z.homOfLE hV ≫ h := by
  intro R _ S Y Z W π y p q hprop _ hbij hflat hpb O h y₀ w hfib hconst
  haveI : IsProper π := hprop
  haveI : IsProper p := MorphismProperty.of_isPullback (P := @IsProper) hpb.flip hprop
  obtain ⟨O', hO', hwO', -⟩ := exists_isAffineOpen_mem_and_subset (show w ∈ (⊤ : W.Opens) from trivial)
  haveI : IsAffine O'.toScheme := hO'
  let T : Z.Opens := O.ι ''ᵁ (h ⁻¹ᵁ O')
  have hTO : T ≤ O := Scheme.Opens.ι_image_le O _
  have hcl : IsClosed (p '' (T : Set Z)ᶜ) := p.isClosedMap _ T.isOpen.isClosed_compl
  let V : Y.Opens := ⟨(p '' (T : Set Z)ᶜ)ᶜ, hcl.isOpen_compl⟩
  have hVT : p ⁻¹ᵁ V ≤ T := by
    intro z hz
    by_contra hzT
    exact hz ⟨z, hzT, rfl⟩
  have hy₀ : y₀ ∈ V := by
    rintro ⟨z, hzT, hz⟩
    apply hzT
    have hzO := hfib z hz
    refine ⟨⟨z, hzO⟩, ?_, Scheme.Opens.ι_apply O _⟩
    show h ⟨z, hzO⟩ ∈ O'
    rw [hconst ⟨z, hzO⟩ (by rw [Scheme.Opens.ι_apply]; exact hz)]
    exact hwO'
  have hV : p ⁻¹ᵁ V ≤ O := hVT.trans hTO
  have hrange : Set.range (Z.homOfLE hV ≫ h) ⊆ Set.range O'.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    obtain ⟨u, hu, hux⟩ := hVT x.2
    have : Z.homOfLE hV x = u := by
      apply Subtype.ext
      refine (Scheme.homOfLE_apply hV x).trans ?_
      exact hux.symm.trans (Scheme.Opens.ι_apply O u)
    show h (Z.homOfLE hV x) ∈ O'
    rw [this]
    exact hu
  have hg := IsOpenImmersion.lift_fac O'.ι _ hrange
  haveI hiso : IsIso (p.app (V.ι ''ᵁ ⊤)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (_root_.GlobalTheory.Mum.app_bijective_of_flat_baseChange R S Y Z π y p q inferInstance inferInstance hbij hflat hpb _)
  haveI : IsIso (p ∣_ V).appTop := by
    rw [morphismRestrict_appTop]
    refine @IsIso.comp_isIso _ _ _ _ _ _ _ hiso ?_
    first
      | exact Functor.map_isIso _ _
      | exact (Z.presheaf.mapIso (eqToIso _).op).isIso_hom
      | (apply Functor.map_isIso)
  obtain ⟨g₀, hg₀⟩ := factor_of_isIso_appTop (p ∣_ V) (IsOpenImmersion.lift O'.ι _ hrange)
  refine ⟨V, hV, g₀ ≫ O'.ι, hy₀, ?_⟩
  rw [← Category.assoc, hg₀, hg]

end GlobalTheory.MorDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPMemFrobeniusKernelOfVerschiebungEqZero
section
set_option autoImplicit false

open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra

namespace GlobalTheory.PDivGroup

theorem mulP_mem_kerIdeal_of_verschiebung_eq_zero (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (a : G.A 1) (ha : (verschiebung h G).app 1 a = 0) :
    G.mulP 1 a ∈ kerIdeal ((G.mulP 1).comp ((relFrob h G).app 1)) := by
  let f := (G.mulP 1).comp ((relFrob h G).app 1)
  let K := kerIdeal f
  let x := Ideal.Quotient.mkₐ R K
  have hx := (kerIdeal_le_ker_iff f x).1
    fun c hc => Ideal.Quotient.eq_zero_iff_mem.2 hc
  let y := x.comp ((relFrob h G).app 2 : (frobTwist h G).A 2 →ₐ[R] G.A 2)
  have hy : torsionIdeal (R := R) (A := (frobTwist h G).A 2) p ≤ RingHom.ker y :=
    (kerIdeal_le_ker_iff (mulBy R ((frobTwist h G).A 2) p) y).2 fun z => by
      change x ((relFrob h G).app 2 (mulBy R ((frobTwist h G).A 2) p z)) = _
      rw [← (frobTwist h G).mulP_res 1 z, PDivGroup.app_mulP (relFrob h G)]
      simpa only [f, BialgHom.coe_comp, Function.comp_apply, CoalgHomClass.counit_comp_apply]
        using hx ((frobTwist h G).res 1 z)
  obtain ⟨b, rfl⟩ := G.res_surjective 1 a
  rw [← PDivGroup.res_app (verschiebung h G)] at ha
  have hb : (verschiebung h G).app 2 b ∈ torsionIdeal (R := R) (A := (frobTwist h G).A 2) p := by
    have : (verschiebung h G).app 2 b ∈ torsionIdeal (R := R) (A := (frobTwist h G).A 2) (p ^ 1) := by
      rw [← (frobTwist h G).ker_res 1]
      exact ha
    rwa [pow_one] at this
  have h1 : x ((relFrob h G).app 2 ((verschiebung h G).app 2 b)) = 0 := hy hb
  rw [relFrob_app_verschiebung_app] at h1
  rw [mulP_res]
  exact Ideal.Quotient.eq_zero_iff_mem.1 h1

end GlobalTheory.PDivGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePullbackTrivialOfImFormInt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

namespace GlobalTheory.TorusRM.KerTriv

open GlobalTheory.TorusRM.TransFrame

theorem dot_herm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (a b : Fin g → ℂ) :
    a ⬝ᵥ Hm *ᵥ star b = star (b ⬝ᵥ Hm *ᵥ star a) := by
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', Pi.star_apply, star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hH.apply i j, star_star]
  ring

theorem exp_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (w l : Fin g → ℂ) (n : ℤ)
    (hn : (w ⬝ᵥ Hm *ᵥ star l).im = n) :
    Complex.exp (Real.pi * (l ⬝ᵥ Hm *ᵥ star w)) = Complex.exp (Real.pi * (w ⬝ᵥ Hm *ᵥ star l)) := by
  rw [dot_herm_swap hH l w]
  set a := w ⬝ᵥ Hm *ᵥ star l
  have e : (star a : ℂ) = a + (-n : ℤ) * (2 * Complex.I) := by
    apply Complex.ext <;> simp [hn, Complex.conj_re, Complex.conj_im] <;> ring
  rw [e, mul_add, Complex.exp_add]
  have : (Real.pi : ℂ) * ((-n : ℤ) * (2 * Complex.I)) = ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I, _root_.mul_one]

end GlobalTheory.TorusRM.KerTriv


open GlobalTheory.TorusRM.TransFrame GlobalTheory.TorusRM.KerTriv in
theorem GlobalTheory.TorusRM.hasGen_lam_pull_of_im_int : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → GlobalTheory.TorusRM.IsFactorAH u Hm χ → ∀ w : Fin g → ℂ, (∀ l ∈ u.Λ, ∃ n : ℤ, (w ⬝ᵥ Hm.mulVec (star l)).im = n) → ∃ t : ((abelian₂ A M).pull (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex w)).left).Gen, t.IsGen := by
  intro A _ _ g hA M u Hm χ hM hF w hw
  have hp : IsProjOver A.hom :=
    (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver A.hom).1 (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme ℂ A hA)
  have hL : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  have hL' : ((abelian₂ A M).pull (pairRight (u.ex w)).left).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨t, ht⟩ := GlobalTheory.HolUnifSec.hasGen_of_periodic A hA hp _ hL' g (transUnif u w)
    (fun z => Complex.exp (Real.pi * (z ⬝ᵥ Hm *ᵥ star w))) (by
      have hd : Differentiable ℂ (fun z : Fin g → ℂ => z ⬝ᵥ Hm *ᵥ star w) := by
        simp only [dotProduct]; fun_prop
      exact ((differentiable_const _).mul hd).cexp) (fun z => Complex.exp_ne_zero _) (by
      intro l hl i z hz
      obtain ⟨n, hn⟩ := hw l hl
      rw [transUnif_factor u hF w ⟨l, hl⟩ i z hz, add_dotProduct, mul_add, Complex.exp_add,
        exp_swap hF.1 w l n hn]
      ring)
  have hρ : fst A (𝟙_ (Over (Sp ℂ))) ≫ pairRight (u.ex w) =
      lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex w) := by
    simp only [pairRight, comp_lift, Category.comp_id]
    rw [← Category.assoc, toUnit_unique (fst A (𝟙_ (Over (Sp ℂ))) ≫ toUnit A) (snd A (𝟙_ (Over (Sp ℂ))))]
  have key : (fun _ : PUnit => (fst A (𝟙_ (Over (Sp ℂ)))).left ≫ (pairRight (u.ex w)).left) =
      (fun _ : PUnit => (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex w)).left) := by
    funext _
    rw [← Over.comp_left, hρ]
  have H : ∃ t : (LB.LinComb (abelian₂ A M) (fun _ : PUnit => (fst A (𝟙_ (Over (Sp ℂ)))).left ≫
      (pairRight (u.ex w)).left) (fun _ => 1)).Gen, t.IsGen :=
    ⟨_, ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen (abelian₂ A M) _ _ t ht (fst A (𝟙_ (Over (Sp ℂ)))).left⟩
  rw [key] at H
  exact H
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleRootExistsOverFgSubalgebra
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

noncomputable section

open GlobalTheory

namespace GlobalTheory.RootFG

theorem lbIso_of_factor {Y Y' X₀ : Scheme.{0}} {M N : LB X₀} (a : Y ⟶ X₀) (j : Y' ⟶ Y) (a' : Y' ⟶ X₀)
    (e : a' = j ≫ a) (h : LBIso (M.pull a) (N.pull a)) : LBIso (M.pull a') (N.pull a') :=
  LBIso.chartPull (chartPullSame M _ _ _ j fun _ => e) (chartPullSame N _ _ _ j fun _ => e) h

theorem exists_fg_lbIso_of_isPullback {k : Type} [Field k] {C : Type} [CommRing C] [Algebra k C] {X : Scheme.{0}}
    (pB : X ⟶ Sp k) [QuasiCompact pB] [QuasiSeparated pB] {R₀ : Subalgebra k C} (h₀ : R₀.FG) {Y₀ Y : Scheme.{0}}
    (q₀ : Y₀ ⟶ Sp R₀) (a₀ : Y₀ ⟶ X) (hY₀ : IsPullback a₀ q₀ pB (spMap (algebraMap k R₀)))
    (y : Y ⟶ Y₀) (q : Y ⟶ Sp C) (hY : IsPullback y q q₀ (spMap R₀.val.toRingHom))
    (M N : LB Y₀) (hM : M.IsLB) (hN : N.IsLB) (H : LBIso (M.pull y) (N.pull y)) :
    ∃ (R : Subalgebra k C) (hR : R₀ ≤ R), R.FG ∧ ∀ (Y₁ : Scheme.{0}) (q₁ : Y₁ ⟶ Sp R) (y₁ : Y₁ ⟶ Y₀),
      y₁ ≫ q₀ = q₁ ≫ spMap (Subalgebra.inclusion hR).toRingHom → LBIso (M.pull y₁) (N.pull y₁) := by
  let e : pullback pB (spMap (algebraMap k R₀)) ⟶ Y₀ :=
    hY₀.lift (pullback.fst _ _) (pullback.snd _ _) pullback.condition
  have e₁ : e ≫ a₀ = pullback.fst _ _ := hY₀.lift_fst _ _ _
  have e₂ : e ≫ q₀ = pullback.snd _ _ := hY₀.lift_snd _ _ _
  let f : pullback pB (spMap (algebraMap k C)) ⟶ Y :=
    hY.lift (baseChangeMap pB R₀.val ≫ e) (pullback.snd _ _) (by
      rw [Category.assoc, e₂, baseChangeMap_snd])
  have hf : f ≫ y = baseChangeMap pB R₀.val ≫ e := hY.lift_fst _ _ _
  have H₀ : LBIso ((M.pull e).pull (baseChangeMap pB R₀.val)) ((N.pull e).pull (baseChangeMap pB R₀.val)) := by
    have := lbIso_of_factor y f _ hf.symm H
    exact LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) (pull_isLB (pull_isLB hN _) _)
      (Spread.lbIso_pull_pull hM _ rfl).symm
      (LBIso.trans (pull_isLB hM _) (pull_isLB hN _) (pull_isLB (pull_isLB hN _) _) this
        (Spread.lbIso_pull_pull hN _ rfl))
  obtain ⟨R, hR, hRfg, H₁⟩ := exists_fg_lbIso pB h₀ (M.pull e) (N.pull e) (pull_isLB hM _) (pull_isLB hN _) H₀
  refine ⟨R, hR, hRfg, fun Y₁ q₁ y₁ w => ?_⟩
  have H₂ : LBIso (M.pull (baseChangeMap pB (Subalgebra.inclusion hR) ≫ e))
      (N.pull (baseChangeMap pB (Subalgebra.inclusion hR) ≫ e)) :=
    LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hN _)
      (Spread.lbIso_pull_pull hM _ rfl)
      (LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB (pull_isLB hN _) _) (pull_isLB hN _) H₁
        (Spread.lbIso_pull_pull hN _ rfl).symm)
  have hs : spMap (Subalgebra.inclusion hR).toRingHom ≫ spMap (algebraMap k R₀) = spMap (algebraMap k R) := by
    rw [spMap_comp_ring]; rfl
  let m : Y₁ ⟶ pullback pB (spMap (algebraMap k R)) :=
    pullback.lift (y₁ ≫ a₀) q₁ (by rw [Category.assoc, hY₀.w, ← Category.assoc, w, Category.assoc, hs])
  refine lbIso_of_factor _ m y₁ ?_ H₂
  apply hY₀.hom_ext
  · rw [Category.assoc, Category.assoc, e₁, baseChangeMap_fst, pullback.lift_fst]
  · rw [Category.assoc, Category.assoc, e₂, baseChangeMap_snd, pullback.lift_snd_assoc, w]

end GlobalTheory.RootFG


open GlobalTheory GlobalTheory.RootFG in
theorem GlobalTheory.RootFG.root_fg : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left),
    P.IsLB → ∀ (k : Type) [Field k] (t : Sp k ⟶ S) (C : Type) [CommRing C] [Algebra k C],
    Root A P (spMap (algebraMap k C) ≫ t) → ∃ B : Subalgebra k C, B.FG ∧ Root A P (spMap (algebraMap k B) ≫ t) := by
  intro S A _ hA P hP k _ t C _ _ hRt
  obtain ⟨B', _, _, β, β₂, hβ, hsq, L, hL, H⟩ := hRt
  obtain ⟨A₀, _, φ₀, h₀⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A t
  have hA₀ : IsAbelianScheme A₀ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h₀
  have := hA₀.proper
  have : IsProper (A₀ ⊗ A₀).hom := by
    change IsProper (pullback.fst A₀.hom A₀.hom ≫ A₀.hom)
    infer_instance

  let φ' : B'.left ⟶ A₀.left := h₀.1.lift β (B'.hom ≫ spMap (algebraMap k C)) (by rw [hβ.1.w, Category.assoc])
  have hφ'₁ : φ' ≫ φ₀ = β := h₀.1.lift_fst _ _ _
  have hφ'₂ : φ' ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k C) := h₀.1.lift_snd _ _ _
  have hB'₀ : IsGrpPullback B' A₀ (spMap (algebraMap k C)) φ' :=
    IsGrpPullback.cancel h₀ (by rw [hφ'₁]; exact hβ) hφ'₂

  obtain ⟨R₁, M, ρ, hR₁, hM, hρ₁, hρ₂, HL⟩ := GlobalTheory.LBDescent.exists_fg_lb A₀.hom B'.hom φ' hB'₀.1 L hL
  obtain ⟨B₁, _, β₁, h₁⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A₀ (spMap (algebraMap k R₁))
  have hB₁ : IsAbelianScheme B₁ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA₀ h₁
  haveI : IsCommMonObj B₁ := hB₁.comm
  let e₁ : B₁.left ⟶ pullback A₀.hom (spMap (algebraMap k R₁)) := h₁.1.isoPullback.hom
  let L₁ : LB B₁.left := M.pull e₁
  have hL₁ : L₁.IsLB := pull_isLB hM _
  let σ : Sp C ⟶ Sp R₁ := spMap R₁.val.toRingHom
  have hσ : σ ≫ spMap (algebraMap k R₁) = spMap (algebraMap k C) := by
    rw [spMap_comp_ring]; rfl
  let ψ : B'.left ⟶ B₁.left := h₁.1.lift φ' (B'.hom ≫ σ) (by rw [hφ'₂, Category.assoc, hσ])
  have hψ₁ : ψ ≫ β₁ = φ' := h₁.1.lift_fst _ _ _
  have hψ₂ : ψ ≫ B₁.hom = B'.hom ≫ σ := h₁.1.lift_snd _ _ _
  have hψ : IsGrpPullback B' B₁ σ ψ := IsGrpPullback.cancel h₁ (by rw [hψ₁, hσ]; exact hB'₀) hψ₂
  have hρψ : ρ = ψ ≫ e₁ := by
    apply pullback.hom_ext
    · rw [hρ₁, Category.assoc, IsPullback.isoPullback_hom_fst, hψ₁]
    · rw [hρ₂, Category.assoc, IsPullback.isoPullback_hom_snd, hψ₂]
  have HL₁ : LBIso L (L₁.pull ψ) :=
    LBIso.trans hL (pull_isLB hM _) (pull_isLB hL₁ _) HL (Spread.lbIso_pull_pull hM ψ hρψ)

  have hc : IsGrpPullback B₁ A (spMap (algebraMap k R₁) ≫ t) (β₁ ≫ φ₀) := h₁.comp h₀
  let β₂₁ := (lift (pushPt hc.1.w (fst B₁ B₁)) (pushPt hc.1.w (snd B₁ B₁))).left
  have hsq₁ : IsSquare (β₁ ≫ φ₀) β₂₁ := GlobalTheory.LamPull.exists_isSquare hc.1.w
  let V := lift (pushPt hψ.1.w (fst B' B')) (pushPt hψ.1.w (snd B' B'))
  have hsqψ : IsSquare ψ V.left := GlobalTheory.LamPull.exists_isSquare hψ.1.w
  have c₁ : LBIso (abelian₂ B' L) ((abelian₂ B₁ L₁).pull V.left) :=
    GlobalTheory.SymSpread.lbIso_cube hψ hL₁ hL HL₁ (x2 B₁) (x2 B') V (fun i => by fin_cases i <;> simp [V, x2])
  have hβ₂ : β₂ = V.left ≫ β₂₁ := by
    have h' := GlobalTheory.ZM.SiegPull.isSquare_comp hsqψ hsq₁
    have eβ : ψ ≫ β₁ ≫ φ₀ = β := by rw [← Category.assoc, hψ₁, hφ'₁]
    rw [eβ] at h'
    apply pullback.hom_ext
    · exact hsq.1.trans h'.1.symm
    · exact hsq.2.trans h'.2.symm
  have hΛ₁ : (abelian₂ B₁ L₁).IsLB := LB.isLB_linComb hL₁ _ _
  have hΛ' : (abelian₂ B' L).IsLB := LB.isLB_linComb hL _ _
  have HV : LBIso ((abelian₂ B₁ L₁).pull V.left) ((P.pull β₂₁).pull V.left) :=
    LBIso.trans (pull_isLB hΛ₁ _) hΛ' (pull_isLB (pull_isLB hP _) _) c₁.symm
      (LBIso.trans hΛ' (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) H (Spread.lbIso_pull_pull hP V.left hβ₂))

  obtain ⟨R₂, h₁₂, hR₂, HD⟩ := exists_fg_lbIso_of_isPullback (A₀ ⊗ A₀).hom hR₁ (B₁ ⊗ B₁).hom _
    (GlobalTheory.SymSpread.isPullback_square h₁) V.left (B' ⊗ B').hom (GlobalTheory.SymSpread.isPullback_square hψ)
    (abelian₂ B₁ L₁) (P.pull β₂₁) hΛ₁ (pull_isLB hP _) HV
  let τ : Sp R₂ ⟶ Sp R₁ := spMap (Subalgebra.inclusion h₁₂).toRingHom
  have hτ : τ ≫ spMap (algebraMap k R₁) = spMap (algebraMap k R₂) := by
    rw [spMap_comp_ring]; rfl
  obtain ⟨B₂, _, κ, hκ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback B₁ τ
  have hB₂ : IsAbelianScheme B₂ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB₁ hκ
  haveI : IsCommMonObj B₂ := hB₂.comm
  refine ⟨R₂, hR₂, ?_⟩
  rw [← hτ, Category.assoc]
  let W := lift (pushPt hκ.1.w (fst B₂ B₂)) (pushPt hκ.1.w (snd B₂ B₂))
  have hsqW : IsSquare κ W.left := GlobalTheory.LamPull.exists_isSquare hκ.1.w
  have hL₂ : (L₁.pull κ).IsLB := pull_isLB hL₁ κ
  refine ⟨B₂, inferInstance, inferInstance, κ ≫ β₁ ≫ φ₀, W.left ≫ β₂₁, hκ.comp hc,
    GlobalTheory.ZM.SiegPull.isSquare_comp hsqW hsq₁, L₁.pull κ, hL₂, ?_⟩
  have d₁ : LBIso (abelian₂ B₂ (L₁.pull κ)) ((abelian₂ B₁ L₁).pull W.left) :=
    GlobalTheory.SymSpread.lbIso_cube hκ hL₁ hL₂ (lbIso_refl hL₂) (x2 B₁) (x2 B₂) W (fun i => by fin_cases i <;> simp [W, x2])
  have d₂ : LBIso ((abelian₂ B₁ L₁).pull W.left) ((P.pull β₂₁).pull W.left) :=
    HD _ (B₂ ⊗ B₂).hom W.left (GlobalTheory.SymSpread.isPullback_square hκ).w
  exact LBIso.trans (LB.isLB_linComb hL₂ _ _) (pull_isLB hΛ₁ _) (pull_isLB hP _) d₁
    (LBIso.trans (pull_isLB hΛ₁ _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) d₂
      (Spread.lbIso_pull_pull hP W.left rfl).symm)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesAlgHomIsNilpotentOfConstantCoeffZer
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem mvPowerSeries_algHom_isNilpotent_of_constantCoeff_zero :
    ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A],
      ∀ φ : MvPowerSeries σ k →ₐ[k] A, (∀ i, IsNilpotent (φ (X i))) →
        ∀ a : MvPowerSeries σ k, constantCoeff a = 0 → IsNilpotent (φ a) := by
  intro k _ σ _ A _ _ φ hφ a ha
  classical
  haveI := Fintype.ofFinite σ
  have hc : ∀ α : σ →₀ ℕ, ∃ o : Option σ, (α = 0 ∧ o = none) ∨ ∃ i, o = some i ∧ α i ≠ 0 := by
    intro α
    by_cases h : α = 0
    · exact ⟨none, Or.inl ⟨h, rfl⟩⟩
    · obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 h
      exact ⟨some i, Or.inr ⟨i, rfl, by simpa using hi⟩⟩
  choose c hc using hc
  let g : σ → MvPowerSeries σ k := fun i α => if c α = some i then coeff α a else 0
  have hg : ∀ i α, coeff α (g i) = if c α = some i then coeff α a else 0 := fun _ _ => rfl
  have hsum : a = ∑ i, g i := by
    ext α
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [hg]
    rcases hc α with ⟨h0, h1⟩ | ⟨i, h1, -⟩
    · rw [h1, h0]
      simpa using ha
    · rw [h1]
      simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum]
  refine isNilpotent_sum fun i _ => ?_
  have hd : (X i : MvPowerSeries σ k) ∣ g i := by
    rw [X_dvd_iff]
    intro m hm
    rw [hg, if_neg]
    intro h
    rcases hc m with ⟨-, h1⟩ | ⟨j, h1, h2⟩
    · rw [h1] at h; cases h
    · rw [h1] at h
      cases h
      exact h2 hm
  obtain ⟨b, hb⟩ := hd
  rw [hb, map_mul]
  exact (Commute.all _ _).isNilpotent_mul_right (hφ i)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OLinearOfBasisProductsAdditivePointsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oLinear_of_basis_products_additive_points : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (H : Scheme.{0}) (Y AH : Over H) [GrpObj AH] [IsCommMonObj AH] (actH : OActN D.O AH) (u : D.La → (Y ⟶ AH)), (∀ x y, u (x + y) = u x * u y) → ∀ (ιO ιL : Type) (bO : Module.Basis ιO ℤ D.O) (bL : Module.Basis ιL ℤ D.La), (∀ j i, u (bO j • bL i) = u (bL i) ≫ actH.act (bO j)) → ∀ (c : D.O) x, u (c • x) = u x ≫ actH.act c := by
  first | (exact @GlobalTheory.basisLin_oLinear) | (exact GlobalTheory.basisLin_oLinear) | (intros; apply GlobalTheory.basisLin_oLinear  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalAtNilpotentXEqCoordinate
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem evA_X (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A]
    (x : σ → A) (hx : ∀ i, IsNilpotent (x i)) (i : σ) : evA k x hx (X i) = x i := by
  have ha : HasSubst (fun i => (C (x i) : MvPowerSeries Empty A)) :=
    hasSubst_of_constantCoeff_nilpotent fun i => by simpa using hx i
  show (constantCoeff : MvPowerSeries Empty A →+* A) (substAlgHom (R := k) ha (X i)) = x i
  rw [substAlgHom_apply, subst_X ha, constantCoeff_C]

end GlobalTheory.Katz
end

