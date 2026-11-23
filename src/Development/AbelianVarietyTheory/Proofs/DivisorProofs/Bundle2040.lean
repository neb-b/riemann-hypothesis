module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0490
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLbOfGeneratedSystem
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1987
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0865
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1919
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1988
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerLiftedRatiosProjectiveRelations
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg.LiftRatios

theorem appLE_rs {X Y : Scheme.{0}} (f : X ⟶ Y) {U U' : Y.Opens} {V V' : X.Opens} (hU : U' ≤ U) (hV : V' ≤ V)
    (h : V ≤ f ⁻¹ᵁ U) (h' : V' ≤ f ⁻¹ᵁ U') (y : Γ(Y, U)) :
    (f.appLE U' V' h').hom (rs Y hU y) = rs X hV ((f.appLE U V h).hom y) := by
  change (Y.presheaf.map (homOfLE hU).op ≫ f.appLE U' V' h').hom y =
    (f.appLE U V h ≫ X.presheaf.map (homOfLE hV).op).hom y
  rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem app_cst_comp {R : Type} [CommRing R] {X X' : Scheme.{0}} (φ : X' ⟶ X) (f : X ⟶ Spec (CommRingCat.of R))
    (V : X.Opens) (r : R) : (φ.app V).hom (cst f V r) = cst (φ ≫ f) (φ ⁻¹ᵁ V) r := by
  have e := Scheme.Hom.appLE_comp_appLE φ f ⊤ V (φ ⁻¹ᵁ V) (by simp) le_rfl
  rw [Scheme.Hom.app_eq_appLE]
  exact congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) e

theorem preimage_injective {X Y : Scheme.{0}} (f : X ⟶ Y) (hf : Surjective f) {U U' : Y.Opens}
    (h : f ⁻¹ᵁ U = f ⁻¹ᵁ U') : U = U' := by
  refine SetLike.ext fun y => ?_
  obtain ⟨z, rfl⟩ := hf.surj y
  rw [← Scheme.Hom.mem_preimage, ← Scheme.Hom.mem_preimage, h]

theorem mem_of_appLE_mem (R : Type) [CommRing R] (I : Ideal R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (e : ℕ)
    (V : (Y (e + 1)).left.Opens) (hV : IsAffineOpen V) (W : (Y e).left.Opens) (hW : β e ⁻¹ᵁ V = W)
    (x : Γ((Y (e + 1)).left, V)) (hx : ((β e).appLE V W hW.ge).hom x ∈ towerIdeal Y e I W) :
    x ∈ towerIdeal Y (e + 1) I V := by
  subst hW
  rw [Scheme.Hom.appLE_eq_app] at hx
  obtain ⟨-, -, hk⟩ := _root_.GlobalTheory.FormalAlg.baseChange_quotient R (I ^ (e + 1)) _ _ ((Y (e + 1)).hom ≫ thick R I (e + 1)) (β e) (Y e).hom
    ((_root_.GlobalTheory.FormalAlg.towerSquares R I Y β hβ).1 e)
  obtain ⟨hs, hker⟩ := hk V hV
  have hc : β e ≫ (Y (e + 1)).hom ≫ thick R I (e + 1) = (Y e).hom ≫ thick R I e := by
    rw [← Category.assoc, (hβ e).w, Category.assoc, thickTrans_comp]
  have hmap : Ideal.map ((β e).app V).hom (towerIdeal Y (e + 1) I V) = towerIdeal Y e I (β e ⁻¹ᵁ V) := by
    unfold towerIdeal
    rw [Ideal.map_map]
    congr 1
    ext r
    rw [RingHom.comp_apply, app_cst_comp, hc]
  have hx' : x ∈ Ideal.comap ((β e).app V).hom (Ideal.map ((β e).app V).hom (towerIdeal Y (e + 1) I V)) := by
    rw [hmap]
    exact hx
  rw [Ideal.comap_map_of_surjective _ hs] at hx'
  have hle : Ideal.comap ((β e).app V).hom ⊥ ≤ towerIdeal Y (e + 1) I V := by
    intro y hy
    have hy' : y ∈ RingHom.ker ((β e).app V).hom := hy
    rw [hker] at hy'
    exact Ideal.map_mono (Ideal.pow_le_self (Nat.succ_ne_zero e)) hy'
  exact SetLike.le_def.1 (sup_le le_rfl hle) hx'

theorem lifted_ratios_mod : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), (∀ e i j, (Y e).left.basicOpen (C.ρ e i j) = C.D e i ⊓ C.D e j) ∧ (∀ e i, C.ρ e i i - 1 ∈ towerIdeal Y e I (C.D e i)) ∧ ∀ e i j l, rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i l) - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) * rs (Y e).left (inf_le_right : C.D e i ⊓ C.D e j ≤ C.D e j) (C.ρ e j l) ∈ towerIdeal Y e I (C.D e i ⊓ C.D e j) := by
  intro R _ I Y β hβ n C
  have hsur : ∀ e, Surjective (β e) := fun e =>
    MorphismProperty.of_isPullback (P := @Surjective) (hβ e).flip (GlobalTheory.GenSystem.surjective_thickTrans R I e)
  have h1 : ∀ e i j, (Y e).left.basicOpen (C.ρ e i j) = C.D e i ⊓ C.D e j := by
    intro e
    induction e with
    | zero => exact C.basic
    | succ e ih =>
      intro i j
      refine preimage_injective (β e) (hsur e) ?_
      have hb := Scheme.basicOpen_appLE (β e) (C.D e i) (C.D (e + 1) i) (C.pre e i).ge (C.ρ (e + 1) i j)
      rw [C.ρ_pull, ih] at hb
      rw [Scheme.Hom.preimage_inf, C.pre, C.pre, hb]
      exact (inf_eq_right.2 ((Scheme.Hom.preimage_mono (β e) (Scheme.basicOpen_le _ _)).trans
        (C.pre e i).le)).symm
  refine ⟨h1, ?_, ?_⟩
  · intro e
    induction e with
    | zero =>
      intro i
      rw [C.ρ_self, sub_self]
      exact Ideal.zero_mem _
    | succ e ih =>
      intro i
      refine mem_of_appLE_mem R I Y β hβ e _ (C.aff (e + 1) i) _ (C.pre e i) _ ?_
      rw [map_sub, map_one, C.ρ_pull]
      exact ih i
  · intro e
    induction e with
    | zero =>
      intro i j l
      rw [C.cocycle, sub_self]
      exact Ideal.zero_mem _
    | succ e ih =>
      intro i j l
      have hV : IsAffineOpen (C.D (e + 1) i ⊓ C.D (e + 1) j) := by
        rw [← h1 (e + 1) i j]
        exact (C.aff (e + 1) i).basicOpen _
      have hW : β e ⁻¹ᵁ (C.D (e + 1) i ⊓ C.D (e + 1) j) = C.D e i ⊓ C.D e j := by
        rw [Scheme.Hom.preimage_inf, C.pre, C.pre]
      refine mem_of_appLE_mem R I Y β hβ e _ hV _ hW _ ?_
      rw [map_sub, map_mul, appLE_rs (β e) _ inf_le_left (C.pre e i).ge, appLE_rs (β e) _ inf_le_left (C.pre e i).ge,
        appLE_rs (β e) _ inf_le_right (C.pre e j).ge, C.ρ_pull, C.ρ_pull, C.ρ_pull]
      exact ih i j l

end GlobalTheory.FormalAlg.LiftRatios
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsValsReal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.SiegelTor GlobalTheory.UT
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ThetaLevel

theorem isGenSec_real {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) :
    IsGenSec ρ.P.A ρ.P.L 1 ρ.th₁ := by
  intro s
  obtain ⟨r, hr, -⟩ := ρ.th₁_basis s
  exact ⟨r 0, fun j => (hr j).trans (Fin.sum_univ_one _)⟩

end GlobalTheory.ThetaLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLineBundleTrivialBasicOpenOfTrivialFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.TorsionSpread

theorem triv_lbPow_pull {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) (k : ℕ) (φ : Y ⟶ X)
    (h : ∃ t : (Hecke.lbPow M k).Gen, t.IsGen) : ∃ t : (Hecke.lbPow (M.pull φ) k).Gen, t.IsGen := by
  have hP : (Hecke.lbPow M k).IsLB := LB.isLB_linComb hM _ _
  have hM' : (M.pull φ).IsLB := LB.isLB_pull hM φ
  have hP' : (Hecke.lbPow (M.pull φ) k).IsLB := LB.isLB_linComb hM' _ _
  have e : ∀ {Z : Scheme.{0}} {N : LB Z} (hN : N.IsLB) (h' : (Hecke.lbPow N k).IsLB),
      CechPic.cls _ h' = k • CechPic.cls N hN := by
    intro Z N hN h'
    apply (CechPic.cls_linComb hN (fun _ : Fin k => 𝟙 Z) (fun _ => 1) h').trans
    simp [CechPic.pull_id]
  rw [← CechPic.cls_eq_zero_iff hP']
  rw [← CechPic.cls_eq_zero_iff hP] at h
  rw [e hM' hP', CechPic.cls_pull hM φ hM', ← map_nsmul, ← e hM hP, h, map_zero]

theorem triv_basicOpen_of_triv_fibre : (∀ (T : Type) [CommRing T] [IsLocalRing T] (e : T), (∀ a ∈ IsLocalRing.maximalIdeal T, a * e = 0) → e ∈ IsLocalRing.maximalIdeal T → ∀ (A : Over (Sp T)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → ∀ k : ℕ, IsUnit (k : T) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (X' : Scheme.{0}) (π : X' ⟶ A.left) (f' : X' ⟶ Sp (T ⧸ Ideal.span {e})), IsPullback π f' A.hom (spMap (Ideal.Quotient.mk (Ideal.span {e}))) → (∃ t : (M.pull π).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen) → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over (Sp R)) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit (k : R) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (K : Type) [Field K] (g₀ : R →+* K), (∃ t : (M.pull (pullback.fst A.hom (spMap g₀))).Gen, t.IsGen) → ∃ r : R, g₀ r ≠ 0 ∧ ∃ t : (M.pull (A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).Gen, t.IsGen := by
  intro hinf R _ _ A _ hA M hM _hrig k hk hpow K _ g₀ ht₀
  haveI := hA.proper
  haveI := hA.smooth
  have hP := GlobalTheory.ProperFinite.nonempty_perf_of_isProper A.hom hM
  haveI : Surjective A.hom := by
    haveI : Surjective ((1 : 𝟙_ (Over (Sp R)) ⟶ A).left ≫ A.hom) := by
      rw [Over.w]
      change Surjective (𝟙 _)
      infer_instance
    exact Surjective.of_comp (1 : 𝟙_ (Over (Sp R)) ⟶ A).left A.hom
  have h₀ := IsPullback.of_hasPullback A.hom (spMap g₀)
  obtain ⟨r, I, hr, hI, H⟩ := GlobalTheory.AbLaw.Seesaw.seesaw R A.left A.hom M hM hP inferInstance inferInstance K g₀
    _ _ _ h₀ (GlobalTheory.AbLaw.CubeOpen.bijective_appTop GlobalTheory.ExpansionTotal.globalFns A hA h₀) ht₀
  haveI : (RingHom.ker g₀).IsPrime := RingHom.ker_isPrime g₀
  obtain ⟨c, hc, hcI⟩ := GlobalTheory.AbLaw.CubeOpen.exists_ann (RingHom.ker g₀) I hI
    ((H K g₀ _ _ _ h₀ (Ne.isUnit hr)).1 ht₀) (fun T _ _ g e hu he he' hle => by
      have hg := IsPullback.of_hasPullback A.hom (spMap g)
      refine (H T g _ _ _ hg (hu r hr)).1 ?_
      have hkT : IsUnit (k : T) := by simpa using hk.map g
      letI : GrpObj ((Over.pullback (spMap g)).obj A) := Functor.grpObjObj
      have hp := IsPullback.of_hasPullback ((Over.pullback (spMap g)).obj A).hom
        (spMap (Ideal.Quotient.mk (Ideal.span {e})))
      refine hinf T e he he' ((Over.pullback (spMap g)).obj A)
        (Out.TLinPf.isAb_pullback (spMap g) A hA) (M.pull (pullback.fst A.hom (spMap g)))
        (LB.isLB_pull hM _) k hkT (triv_lbPow_pull hM k _ hpow) _ _ _ hp ?_
      have hq := hp.paste_horiz hg
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at hq
      exact GlobalTheory.AbLaw.CubeOpen.triv_pull_pull _ _
        ((H _ _ _ _ _ hq ((hu r hr).map (Ideal.Quotient.mk (Ideal.span {e})))).2 hle))
  refine ⟨r * c, by rw [map_mul]; exact mul_ne_zero hr hc, ?_⟩
  let L := Localization.Away (r * c)
  have hu : IsUnit (algebraMap R L (r * c)) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul, IsUnit.mul_iff] at hu
  have hp := IsPullback.of_hasPullback A.hom (Spec.map (CommRingCat.ofHom (algebraMap R L)))
  have ht := (H L (algebraMap R L) _ _ _ hp hu.1).2 fun x hx => by
    rw [RingHom.mem_ker, ← hu.2.mul_right_eq_zero, ← map_mul, hcI x hx, map_zero]
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R L))) :=
    IsOpenImmersion.of_isLocalization (r * c)
  have hsub : Set.range ((A.hom ⁻¹ᵁ (PrimeSpectrum.basicOpen (r * c))).ι ≫ A.hom) ⊆
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap R L))) := by
    rintro _ ⟨y, rfl⟩
    have := PrimeSpectrum.localization_away_comap_range L (r * c)
    change _ ∈ Set.range (PrimeSpectrum.comap (algebraMap R L))
    rw [this]
    exact y.2
  exact GlobalTheory.AbLaw.CubeOpen.triv_comp (hp.lift _ _ (IsOpenImmersion.lift_fac _ _ hsub).symm)
    (hp.lift_fst _ _ _) ht

end GlobalTheory.TorsionSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorSquare
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.PoincareDescent

theorem torsor_square {C : Type*} [Category C] [CartesianMonoidalCategory C] {A A' N : C} [GrpObj A] [GrpObj A']
    [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') [IsMonHom q] (h : IsPullback i (toUnit N) q η[A']) :
    IsPullback (fst A N) (fst A N * (snd A N ≫ i)) q q := by
  have hiq : i ≫ q = 1 := by
    rw [h.w]; rfl
  have hdiff : ∀ {W : C} (x y : W ⟶ A), x ≫ q = y ≫ q → (x⁻¹ * y) ≫ q = toUnit W ≫ η[A'] := by
    intro W x y e
    rw [MonObj.mul_comp, GrpObj.inv_comp, e, inv_mul_cancel]; rfl
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ lift s.fst (h.lift (s.fst⁻¹ * s.snd) (toUnit _)
      (hdiff _ _ s.condition))) (fun s ↦ lift_fst _ _) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_)⟩⟩
  · rw [MonObj.mul_comp, Category.assoc, hiq, MonObj.comp_one, _root_.mul_one]
  · rw [MonObj.comp_mul, lift_fst, lift_snd_assoc, h.lift_fst, mul_inv_cancel_left]
  · have e₁ : m ≫ fst A N = s.fst := h₁
    refine CartesianMonoidalCategory.hom_ext _ _ (by rw [e₁, lift_fst]) ?_
    rw [lift_snd]
    refine h.hom_ext ?_ (toUnit_unique _ _)
    rw [h.lift_fst, ← h₂, MonObj.comp_mul, e₁, Category.assoc, inv_mul_cancel_left]

end GlobalTheory.PoincareDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransitionUnitPowValueAtPointCocycle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge

noncomputable section
namespace GlobalTheory.MBLow.TanGauge

theorem trV_cocycle : ∀ {X : Scheme.{0}} (L : LB X), L.IsLB → ∀ {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b c : L.ι) (n : ℤ),
    ⊤ ≤ y ⁻¹ᵁ L.U a → ⊤ ≤ y ⁻¹ᵁ L.U b → ⊤ ≤ y ⁻¹ᵁ L.U c →
    trV L y a b n * trV L y b c n = trV L y a c n := by
  intro X L hL A _ y a b c n ha hb hc
  have hT : ⊤ ≤ y ⁻¹ᵁ (L.U a ⊓ L.U b ⊓ L.U c) := fun q hq => ⟨⟨ha hq, hb hq⟩, hc hq⟩
  have e := congrArg (fun u => ((u ^ n : Γ(X, L.U a ⊓ L.U b ⊓ L.U c)ˣ) : Γ(X, L.U a ⊓ L.U b ⊓ L.U c))) (hL.cocycle a b c)
  simp only [mul_zpow, ← map_zpow, Units.val_mul] at e
  have e' := congrArg (valR y (L.U a ⊓ L.U b ⊓ L.U c)) e
  rw [GlobalTheory.ZH.CrdCalc.valR_mul y _ hT] at e'
  unfold trV
  rw [← GlobalTheory.ZH.CrdCalc.valR_res y (inf_le_left : L.U a ⊓ L.U b ⊓ L.U c ≤ L.U a ⊓ L.U b) hT,
    ← GlobalTheory.ZH.CrdCalc.valR_res y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      L.U a ⊓ L.U b ⊓ L.U c ≤ L.U b ⊓ L.U c) hT,
    ← GlobalTheory.ZH.CrdCalc.valR_res y (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      L.U a ⊓ L.U b ⊓ L.U c ≤ L.U a ⊓ L.U c) hT]
  exact e'

end GlobalTheory.MBLow.TanGauge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateSectionValuesBoundedIntegralTangent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

theorem trVal_bounded : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (k : ℕ), 1 ≤ k → ∀ (s : Fam D.toPre C k) (gm₀ : GtPt D.toPre (epsR V)) (gm : GtPt D.toPre (TE V C)), GtTan gm₀ → GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → ∀ α : N.X, ∃ b : ℝ, ∀ mu : N.X, ‖(trVal ν s gm α mu).fst‖ ≤ b ∧ ‖(trVal ν s gm α mu).snd‖ ≤ b := by
  intro V _ _ _ D C _ _ _ _ _ hC N ν hν k hk s gm₀ gm _ hpull α
  obtain ⟨S, hS, hint⟩ := hν
  obtain ⟨n, a, σ, σF, hsc, hsum⟩ := _root_.GlobalTheory.SpanBall.span_ball V D C hC S hS k hk (ν.eX α) (s.s (ν.eX α))
  refine ⟨∑ i, ‖a i‖, fun mu => ?_⟩
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.translatedDualPoint_of_integralTorusExtPoint V D.toPre C gm₀ gm hpull (ν.eX mu)
  have e := GlobalTheory.T.dualNumberSectionValue_linearCombination V D.toPre C k (ν.eX α) (s.s (ν.eX α)) n a σF hsum _ ν.J ν.good h3
  have hb := fun i => GlobalTheory.T.pulledBackSection_integralValue_dualPoint V D C hC N ν ⟨S, hS, hint⟩ k _ (σ i) (σF i) (hsc i) _ h2 _ h1
  have hv : trVal ν s gm α mu = ∑ i, TrivSqZeroExt.inl (a i) * sE (σF i)
      ((lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE V C ⟶ TF (R := V) C) gm.b).left ≫
        (DegPre.trF D.toPre C (ν.eX mu)).left) ν.J := e
  rw [hv]
  constructor
  · rw [TrivSqZeroExt.fst_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hb i).1
  · rw [TrivSqZeroExt.snd_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, smul_zero, add_zero, smul_eq_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hb i).2

end GlobalTheory.MBLow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateTangentCombinationEqProd
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
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

def precompHom {C : Type*} [Category C] [CartesianMonoidalCategory C] {M P Q : C} [MonObj M] (f : P ⟶ Q) :
    (Q ⟶ M) →* (P ⟶ M) where
  toFun := fun g => f ≫ g
  map_one' := MonObj.comp_one f
  map_mul' := fun g₁ g₂ => MonObj.comp_mul f g₁ g₂

theorem comp_list_prod {C : Type*} [Category C] [CartesianMonoidalCategory C] {M P Q : C} [MonObj M]
    (f : P ⟶ Q) {m : ℕ} (u : Fin m → (Q ⟶ M)) :
    f ≫ (List.ofFn u).prod = (List.ofFn fun c => f ≫ u c).prod := by
  have h := map_list_prod (precompHom (M := M) f) (List.ofFn u)
  rw [List.map_ofFn] at h
  exact h

theorem translate_comb : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
    (t : SAB H X) (U : X.affineOpens) {m : ℕ} (v' : Fin m → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left))
    (cf : Fin m → Γ(X, U.1)) (va : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left) {S : Type} [CommRing S]
    (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ GlobalTheory.LogKS.chart U →
    ∀ (g' : overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ t.G) (y : Fin m → (overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ t.G)),
    (∀ c, IsTanAtG t (GlobalTheory.LogKS.chart U) (v' c)) → IsCombAtG t (GlobalTheory.LogKS.chart U) v' cf va →
    g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀ → (∀ c, (y c).left = spMap (dualMap φ) ≫ v' c) →
    (∀ c, smT (g₀ ≫ t.G.hom) 0 (y c) = 1) ∧
      ∀ w, GlobalTheory.LogKS.IsTranslate t φ g₀ va w →
        w = (g' * (List.ofFn fun c => smT (g₀ ≫ t.G.hom) (φ (cf c)) (y c)).prod).left := by
  intro E _ _ _ H X t U m v' cf va S _ φ g₀ hg g' y hTan hComb hg' hy
  have hr0 : (epsMul (0 : S)).comp (dualMap φ) =
      ((algebraMap S (DualNumber S)).comp φ).comp (TrivSqZeroExt.fstHom Γ(X, U.1) Γ(X, U.1) Γ(X, U.1)).toRingHom := by
    apply RingHom.ext
    intro r
    ext <;> simp [epsMul, dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hra : (dualMap φ).comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) =
      (algebraMap S (DualNumber S)).comp φ := by
    apply RingHom.ext
    intro r
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  refine ⟨fun c => ?_, fun w hw => ?_⟩
  · let gA : overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ Over.mk (GlobalTheory.LogKS.chart U) :=
      Over.homMk (spMap ((algebraMap S (DualNumber S)).comp φ)) (by
        show spMap _ ≫ GlobalTheory.LogKS.chart U = spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom
        rw [hg, spMap_comp, Category.assoc])
    have h1 : gA ≫ (1 : Over.mk (GlobalTheory.LogKS.chart U) ⟶ t.G) = 1 := MonObj.comp_one gA
    apply Over.OverMorphism.ext
    rw [← h1, smT_left, Over.comp_left, hy c, ← (hTan c).2]
    simp only [gA, Over.homMk_left]
    rw [← Category.assoc, spMap_comp', hr0, spMap_comp, Category.assoc]
  · obtain ⟨g'', V, h1, h2, h3⟩ := hw
    obtain ⟨u, hu, hprod⟩ := hComb
    have hg'' : g'' = g' := Over.OverMorphism.ext (h1.trans hg'.symm)
    let bA : overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ tEpsG (GlobalTheory.LogKS.chart U) :=
      Over.homMk (spMap (dualMap φ)) (by
        show spMap (dualMap φ) ≫ spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) ≫ GlobalTheory.LogKS.chart U =
          spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom
        rw [hg, ← Category.assoc, spMap_comp', hra, spMap_comp, Category.assoc])
    have hV : V = bA ≫ (List.ofFn u).prod := by
      apply Over.OverMorphism.ext
      rw [h2, Over.comp_left, hprod]
      rfl
    have hbAu : ∀ c, bA ≫ u c = smT (g₀ ≫ t.G.hom) (φ (cf c)) (y c) := by
      intro c
      apply Over.OverMorphism.ext
      rw [Over.comp_left, hu c, smT_left, hy c]
      simp only [bA, Over.homMk_left]
      rw [← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', Formalism.L2.Pj.dualMap_comp_epsMul]
    rw [← h3, hg'', hV, comp_list_prod]
    simp only [hbAu]

end GlobalTheory.LogKSDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedFibreFrameAtOriginEqRigidificationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedFibre_frame_at_origin_eq_rigidification : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (x : KeyIn ℂ)
    (φ : x.P.A.left ⟶ D.P.A.left) (he : eSec x.P.A ≫ φ = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A)
    (w : LB.Iso x.P.L (D.P.L.pull φ)), w.IsGen →
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x.P.A) (fun _ => 1)) x.rig
      (rigPullOf φ (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) he D.P.L D.rig) →
    ∀ (g : ℕ) (u : HolUnif x.P.A x.P.L g), u.IsRig x.rig → ∀ (k : x.P.L.ι) (j : D.P.L.ι),
      ⊤ ≤ (u.ex 0).left ⁻¹ᵁ x.P.L.U k → ⊤ ≤ (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A) ⁻¹ᵁ D.P.L.U j →
      valAt' (u.ex 0).left _ (w.s (fun _ => j, k)).val * u.fr k 0 =
        valF (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => j)) (D.rig.s (fun _ => j)).val := by
  first | exact @GlobalTheory.RigAtOrigin.frame_at_origin | exact GlobalTheory.RigAtOrigin.frame_at_origin | (intros; apply GlobalTheory.RigAtOrigin.frame_at_origin <;> assumption)
end

