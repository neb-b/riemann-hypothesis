module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0354
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicIndependentPulledBackProjCoordinateRati
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

namespace GlobalTheory.PD.XCover

attribute [local instance] MvPolynomial.gradedAlgebra

theorem injective_mvPolynomial_of_finite_of_ringKrullDim {k B : Type} [Field k] [CommRing B] {d : ℕ}
    (ψ : MvPolynomial (Fin d) k →+* B) (hψ : ψ.Finite) (hB : ringKrullDim B = d) :
    Function.Injective ψ := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hr0
  letI : Algebra (MvPolynomial (Fin d) k ⧸ RingHom.ker ψ) B := (RingHom.kerLift ψ).toAlgebra
  have hfin : (RingHom.kerLift ψ).Finite := by
    have e : ψ = (RingHom.kerLift ψ).comp (Ideal.Quotient.mk _) := by
      ext x <;> rfl
    exact RingHom.Finite.of_comp_finite (e ▸ hψ)
  haveI : Algebra.IsIntegral (MvPolynomial (Fin d) k ⧸ RingHom.ker ψ) B := ⟨hfin.to_isIntegral⟩
  have e1 : ringKrullDim B = ringKrullDim (MvPolynomial (Fin d) k ⧸ RingHom.ker ψ) :=
    ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective (RingHom.kerLift_injective ψ)
  have e2 : ringKrullDim (MvPolynomial (Fin d) k ⧸ RingHom.ker ψ) ≤
      ringKrullDim (MvPolynomial (Fin d) k ⧸ Ideal.span {r}) :=
    ringKrullDim_le_of_surjective _
      (Ideal.Quotient.factor_surjective (by rw [Ideal.span_singleton_le_iff_mem]; exact hr))
  have e3 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hr0)
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at e3
  have e4 : (d : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin d) k ⧸ Ideal.span {r}) :=
    (hB.symm.trans e1).le.trans e2
  have h := (add_le_add e4 (le_refl (1 : WithBot ℕ∞))).trans e3
  simp only [ENat.card_eq_coe_fintype_card, Fintype.card_fin, zero_add] at h
  norm_cast at h
  omega

theorem ratioSec_eq_projSpace_ratio (d : ℕ) (i j : Fin (d + 1)) (h : j ≠ i) : ratioSec d i j = GlobalTheory.ProjSpace.ratio ℂ d i j := by
  have e := GlobalTheory.ProjSpace.chartAlgEquiv_X ℂ d i ⟨j, h⟩
  rw [GlobalTheory.ProjSpace.chartAlgEquiv_apply, GlobalTheory.ProjSpace.polyToAway, MvPolynomial.eval₂Hom_X'] at e
  exact e

theorem algebraicIndependent_rat : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ)
    [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p →
    ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p → (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) →
      AlgebraicIndependent ℂ (fun j : Fin d => rat φ 0 j.succ) := by
  intro d Z _ p _ inst hinst φ _ hφ hgen
  subst hφ
  obtain ⟨hU, hψ₀⟩ := (GlobalTheory.ProjSpace.isFinite_iff_pullRatio φ (U := fun i => φ ⁻¹ᵁ chart d i)
    (fun _ => rfl)).1 inferInstance 0
  set c := (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str ℂ d) (φ ⁻¹ᵁ chart d 0)).hom with hc
  set y := GlobalTheory.ProjSpace.pullRatio φ (φ ⁻¹ᵁ chart d 0) 0 le_rfl with hy
  let ψ : MvPolynomial (Fin d) ℂ →+* Γ(Z, φ ⁻¹ᵁ chart d 0) := MvPolynomial.eval₂Hom c (fun j => y j.succ)
  let σ : MvPolynomial (Fin (d + 1)) ℂ →+* MvPolynomial (Fin d) ℂ :=
    MvPolynomial.eval₂Hom MvPolynomial.C (Fin.cases 1 MvPolynomial.X)
  have hcomp : ψ.comp σ = MvPolynomial.eval₂Hom c y := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · simp [ψ, σ]
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [ψ, σ, y]
      · simp [ψ, σ]
  have hψ : ψ.Finite := RingHom.Finite.of_comp_finite (hcomp ▸ hψ₀)
  have hdim : ringKrullDim Γ(Z, φ ⁻¹ᵁ chart d 0) = d :=
    GlobalTheory.SmoothDim.ringKrullDim_affineOpen ℂ Z (φ ≫ PSpace.str ℂ d) d inferInstance _ hU ⟨_, hgen 0⟩
  have hinj : Function.Injective ψ := injective_mvPolynomial_of_finite_of_ringKrullDim ψ hψ hdim
  have hgerm : Function.Injective (Z.presheaf.germ (φ ⁻¹ᵁ chart d 0) (genericPoint Z) (hgen 0)).hom :=
    germ_injective_of_isIntegral Z _ (hgen 0)
  have key : (MvPolynomial.aeval (R := ℂ) (fun j : Fin d => rat φ 0 j.succ)).toRingHom =
      (Z.presheaf.germ (φ ⁻¹ᵁ chart d 0) (genericPoint Z) (hgen 0)).hom.comp ψ := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C, RingHom.comp_apply, ψ,
        MvPolynomial.eval₂Hom_C]
      subst hinst
      have e : (φ ≫ PSpace.str ℂ d).appLE ⊤ (φ ⁻¹ᵁ chart d 0) le_top =
          (φ ≫ PSpace.str ℂ d).appTop ≫ Z.presheaf.map (homOfLE le_top).op := by
        rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
        exact (Scheme.Hom.appLE_map _ _ _).symm
      rw [hc, GlobalTheory.QCoh.Qcqs.baseRingHom, CommRingCat.hom_comp, RingHom.comp_apply, e,
        CommRingCat.hom_comp, RingHom.comp_apply, TopCat.Presheaf.germ_res_apply]
      rfl
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X, RingHom.comp_apply, ψ,
        MvPolynomial.eval₂Hom_X']
      rw [rat, dite_eq_left (hgen 0), hy, GlobalTheory.ProjSpace.pullRatio, ← ratioSec_eq_projSpace_ratio d 0 j.succ (Fin.succ_ne_zero j),
        Scheme.Hom.app_eq_appLE]
  rw [algebraicIndependent_iff_injective_aeval]
  have : ⇑(MvPolynomial.aeval (R := ℂ) (fun j : Fin d => rat φ 0 j.succ)) =
      ⇑((Z.presheaf.germ (φ ⁻¹ᵁ chart d 0) (genericPoint Z) (hgen 0)).hom.comp ψ) :=
    congrArg DFunLike.coe key
  rw [this]
  exact hgerm.comp hinj

end GlobalTheory.PD.XCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CechAbPullApp
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite

universe v v' u u'

noncomputable section

namespace GlobalTheory

structure Cube.PullHom {ι κ : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S]
    (σ : R →+* S) (τ : κ → ι) (A : Cube.{v} ι R) (B : Cube.{v'} κ S) where

  app : ∀ s : Finset κ, A.obj (s.image τ) →ₛₗ[σ] B.obj s

  app_res : ∀ {s t : Finset κ} (h : s ⊆ t) (x : A.obj (s.image τ)),
    app t (Cube.res A (Finset.image_subset_image h) x) = Cube.res B h (app s x)

namespace Cube.PullHom

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R] {S : Type u'} [Ring S]
  {σ : R →+* S} {τ : κ → ι} {A : Cube.{v} ι R} {B : Cube.{v'} κ S} (ψ : Cube.PullHom σ τ A B)

theorem card_image {p : ℕ} (t : {s : Finset κ // s.card = p}) (h : Set.InjOn τ (t.1 : Set κ)) :
    (t.1.image τ).card = p := by
  rw [Finset.card_image_of_injOn h, t.2]


open Classical in
def term (p : ℕ) : Cube.Term A p →ₛₗ[σ] Cube.Term B p where
  toFun x t := if h : Set.InjOn τ (t.1 : Set κ) then
      PD.sortSign τ t.1 • ψ.app t.1 (x ⟨t.1.image τ, card_image t h⟩) else 0
  map_add' x y := by
    funext t
    by_cases h : Set.InjOn τ (t.1 : Set κ)
    · simp only [dif_pos h, Pi.add_apply, map_add (f := _), smul_add]
    · simp only [dif_neg h, Pi.add_apply, add_zero]
  map_smul' r x := by
    funext t
    by_cases h : Set.InjOn τ (t.1 : Set κ)
    · simp only [dif_pos h, Pi.smul_apply, map_smulₛₗ, smul_comm (PD.sortSign τ t.1) (σ r)]
    · simp only [dif_neg h, Pi.smul_apply, smul_zero]

theorem term_apply_of_injOn {p : ℕ} (x : Cube.Term A p) (t : {s : Finset κ // s.card = p})
    (h : Set.InjOn τ (t.1 : Set κ)) :
    ψ.term p x t = PD.sortSign τ t.1 • ψ.app t.1 (x ⟨t.1.image τ, card_image t h⟩) := by
  unfold term
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos h]

theorem term_apply_of_not_injOn {p : ℕ} (x : Cube.Term A p) (t : {s : Finset κ // s.card = p})
    (h : ¬ Set.InjOn τ (t.1 : Set κ)) : ψ.term p x t = 0 := by
  unfold term
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_neg h]

end Cube.PullHom

section Sheaf

open SheafPull

variable {T T' : TopCat.{u}} (f : T' ⟶ T) {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {V : Opens T}
  {U : ι → Opens T} {V' : Opens T'} {U' : κ → Opens T'} (τ : κ → ι)
  (hτ : ∀ s : Finset κ, cechOpen V' U' s ≤ (Opens.map f).obj (cechOpen V U (s.image τ)))
  {F : AbSheaf T} {G : AbSheaf T'}

def cechAbPull (φ : F ⟶ (push f).obj G) :
    Cube.PullHom (RingHom.id ℤ) τ (cechAbCube F.obj V U) (cechAbCube G.obj V' U') where
  app s := (G.obj.map (homOfLE (hτ s)).op).hom.toIntLinearMap ∘ₗ
    (φ.hom.app (op (cechOpen V U (s.image τ)))).hom.toIntLinearMap
  app_res {s t} h x := by
    have e : φ.hom.app (op (cechOpen V U (t.image τ)))
        (F.obj.map (homOfLE (cechOpen_anti V U (Finset.image_subset_image (f := τ) h))).op x) =
        G.obj.map ((Opens.map f).map
          (homOfLE (cechOpen_anti V U (Finset.image_subset_image (f := τ) h)))).op
          (φ.hom.app (op (cechOpen V U (s.image τ))) x) :=
      ConcreteCategory.congr_hom (φ.hom.naturality _) x
    refine (congrArg (G.obj.map (homOfLE (hτ t)).op) e).trans ?_
    refine (ConcreteCategory.congr_hom (G.obj.map_comp _ _) _).symm.trans
      (Eq.trans ?_ (ConcreteCategory.congr_hom (G.obj.map_comp (homOfLE (hτ s)).op
        (homOfLE (cechOpen_anti V' U' h)).op) _))
    rfl

end Sheaf

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CechHomologyEquivFamStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechHomologyEquivFamAlt : ∀ (R : Type) [Field R] (ι : Type) [LinearOrder ι] (E : Type) [AddCommGroup E] [Module R E]
    (A : Finset ι → Submodule R E) (C : GlobalTheory.Cube ι R) (g : ∀ s, C.obj s →ₗ[R] E),
    (∀ s, s.Nonempty → Function.Injective (g s)) → (∀ s, s.Nonempty → LinearMap.range (g s) = A s) →
    (∀ s t (h : s ⊆ t), s.Nonempty → ∀ x, g t (Cube.res C h x) = g s x) →
    ∀ n : ℕ, ∃ e : (cechComplex C).homology n ≃ₗ[R] (GlobalTheory.PD.cech A).H (n : ℤ),
      (∀ (z : LinearMap.ker (Cube.d C (n + 1))) (w : (GlobalTheory.PD.cech A).Z (n : ℤ)),
        (∀ t : {s : Finset ι // s.card = n + 1}, (w : Finset ι → E) t.1 = g t.1 (z.1 t)) →
        e (cechClass C n z) = Submodule.Quotient.mk w) ∧
      (∀ z : LinearMap.ker (Cube.d C (n + 1)), ∃ w : (GlobalTheory.PD.cech A).Z (n : ℤ),
        ∀ t : {s : Finset ι // s.card = n + 1}, (w : Finset ι → E) t.1 = g t.1 (z.1 t)) ∧
      (∀ (x : Cube.Term C (n + 1)) (w : (GlobalTheory.PD.cech A).Z (n : ℤ)),
        (∀ t : {s : Finset ι // s.card = n + 1}, (w : Finset ι → E) t.1 = g t.1 (x t)) →
        Cube.d C (n + 1) x = 0) := by
  first | (exact @GlobalTheory.cechHomologyEquivFam) | (exact GlobalTheory.cechHomologyEquivFam) | (intros; apply GlobalTheory.cechHomologyEquivFam  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteEtaleFunctionFieldIntegralClosureDifferent
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

noncomputable section

namespace GlobalTheory.W1.SchFF

def eqv {A K σ : Type} [CommRing A] [CommRing K] [SetLike σ K] [SubringClass σ K] (g : A →+* K)
    (hg : Function.Injective g) (S : σ) (hS : ∀ y, y ∈ S ↔ ∃ f, g f = y) : A ≃+* S :=
  RingEquiv.ofBijective (g.codRestrict S fun f => (hS _).2 ⟨f, rfl⟩)
    ⟨fun a b h => hg (congrArg Subtype.val h), fun y => by
      obtain ⟨f, hf⟩ := (hS y).1 y.2
      exact ⟨f, Subtype.ext hf⟩⟩

@[simp] theorem eqv_coe {A K σ : Type} [CommRing A] [CommRing K] [SetLike σ K] [SubringClass σ K] (g : A →+* K)
    (hg : Function.Injective g) (S : σ) (hS : ∀ y, y ∈ S ↔ ∃ f, g f = y) (a : A) :
    ((eqv g hg S hS a : S) : K) = g a := rfl

theorem frac (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) (h : genericPoint X ∈ U) (x : X.functionField) :
    ∃ a b : Γ(X, U), (X.presheaf.germ U _ h).hom b ≠ 0 ∧ x * (X.presheaf.germ U _ h).hom b = (X.presheaf.germ U _ h).hom a := by
  haveI : Nonempty U := ⟨⟨_, h⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Γ(X, U)) x
  have hb' : algebraMap Γ(X, U) X.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  exact ⟨a, b, hb', div_mul_cancel₀ _ hb'⟩

theorem finiteEtale_functionField : ∀ (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) (c : Y ⟶ Z), c ≫ s = s' → IsFinite c → Etale c → ∀ (d : ℕ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] [i1 : Algebra ℂ Z.functionField] [i2 : Algebra ℂ Y.functionField] [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField], i1 = ffAlg s → i2 = ffAlg s' → (∀ (U : Z.Opens) (hU : genericPoint Z ∈ U) (hU' : genericPoint Y ∈ c ⁻¹ᵁ U) (f : Γ(Z, U)), (Y.presheaf.germ (c ⁻¹ᵁ U) (genericPoint Y) hU').hom ((c.app U).hom f) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ U (genericPoint Z) hU).hom f)) → FiniteDimensional Z.functionField Y.functionField ∧ ∀ (U : Z.Opens) (hU : genericPoint Z ∈ U) (hU' : genericPoint Y ∈ c ⁻¹ᵁ U) (B : Subalgebra ℂ Z.functionField) (B' : Subalgebra ℂ Y.functionField), IsAffineOpen U → (∀ y, y ∈ B ↔ ∃ f : Γ(Z, U), (Z.presheaf.germ U (genericPoint Z) hU).hom f = y) → (∀ y, y ∈ B' ↔ ∃ f : Γ(Y, c ⁻¹ᵁ U), (Y.presheaf.germ (c ⁻¹ᵁ U) (genericPoint Y) hU').hom f = y) → (∀ y ∈ B', IsIntegral B (y : Y.functionField)) ∧ (∀ x : Z.functionField, IsIntegral B x → x ∈ B) ∧ (∀ y : Y.functionField, IsIntegral B y → y ∈ B') ∧ (∀ v ∈ B', ∃ (m : ℕ) (b : Fin m → Y.functionField) (w : Fin m → Z.functionField), (∀ j, b j ∈ B' ∧ w j ∈ B) ∧ ι1 (D ℂ Y.functionField v) = ∑ j, b j • mapDR ℂ Z.functionField Y.functionField (ι1 (D ℂ Z.functionField (w j)))) := by
  intro Z Y _ _ s s' c hcs hfin het d _ _ i1 i2 _ _ h1 h2 hcomp
  haveI : Smooth s := SmoothOfRelativeDimension.smooth d s
  haveI : Smooth s' := SmoothOfRelativeDimension.smooth d s'
  haveI := hfin
  haveI := het
  have hφ : ∀ (U : Z.Opens) (hU : genericPoint Z ∈ U) (hU' : genericPoint Y ∈ c ⁻¹ᵁ U) {σ σ' : Type}
      [SetLike σ Z.functionField] [SubringClass σ Z.functionField] [SetLike σ' Y.functionField] [SubringClass σ' Y.functionField]
      (B : σ) (B' : σ') (hB : ∀ y, y ∈ B ↔ ∃ f : Γ(Z, U), (Z.presheaf.germ U (genericPoint Z) hU).hom f = y)
      (hB' : ∀ y, y ∈ B' ↔ ∃ f : Γ(Y, c ⁻¹ᵁ U), (Y.presheaf.germ (c ⁻¹ᵁ U) (genericPoint Y) hU').hom f = y),
      IsAffineOpen U → ∃ φ : B →+* B', (∀ x : B, (φ x : Y.functionField) = algebraMap Z.functionField Y.functionField x) ∧
        φ.Finite ∧ φ.FormallyUnramified ∧ Nonempty (Γ(Z, U) ≃+* B) ∧ Nonempty (Γ(Y, c ⁻¹ᵁ U) ≃+* B') := by
    intro U hU hU' σ σ' _ _ _ _ B B' hB hB' hUa
    let eB := GlobalTheory.W1.SchFF.eqv _ (germ_injective_of_isIntegral Z _ hU) B hB
    let eB' := GlobalTheory.W1.SchFF.eqv _ (germ_injective_of_isIntegral Y _ hU') B' hB'
    refine ⟨eB'.toRingHom.comp ((c.app U).hom.comp eB.symm.toRingHom), fun x => ?_, ?_, ?_, ⟨eB⟩, ⟨eB'⟩⟩
    · obtain ⟨f, rfl⟩ := eB.surjective x
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
      exact (GlobalTheory.W1.SchFF.eqv_coe _ _ _ _ _).trans (hcomp U hU hU' f)
    · exact (RingHom.Finite.of_surjective _ eB'.surjective).comp
        ((c.finite_app U hUa).comp (RingHom.Finite.of_surjective _ eB.symm.surjective))
    · have he := HasRingHomProperty.appLE @Etale c het ⟨U, hUa⟩ ⟨c ⁻¹ᵁ U, hUa.preimage c⟩ le_rfl
      rw [Scheme.Hom.appLE_eq_app] at he
      exact ((RingHom.FormallyUnramified.of_surjective eB.symm.surjective).comp
        (RingHom.Etale.formallyUnramified _ he)).comp (RingHom.FormallyUnramified.of_surjective eB'.surjective)
  have hfr : ∀ (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (h : genericPoint X ∈ U) {σ : Type}
      [SetLike σ X.functionField] [SubringClass σ X.functionField] (B : σ),
      (∀ y, y ∈ B ↔ ∃ f : Γ(X, U), (X.presheaf.germ U _ h).hom f = y) → IsAffineOpen U →
      ∀ x : X.functionField, ∃ a ∈ B, ∃ b ∈ B, b ≠ 0 ∧ x * b = a := by
    intro X _ U h σ _ _ B hB hUa x
    obtain ⟨a, b, hb, e⟩ := GlobalTheory.W1.SchFF.frac X U hUa h x
    exact ⟨_, (hB _).2 ⟨a, rfl⟩, _, (hB _).2 ⟨b, rfl⟩, hb, e⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨U₀, hU₀, hm⟩ := GlobalTheory.QCoh.exists_affine_mem (c (genericPoint Y))
    have hU₀' : genericPoint Y ∈ c ⁻¹ᵁ U₀ := hm
    have hU₀g : genericPoint Z ∈ U₀ := GlobalTheory.VB.genericPoint_mem hm
    obtain ⟨φ, hφ1, hφ2, -, -, -⟩ := hφ U₀ hU₀g hU₀' (Z.presheaf.germ U₀ _ hU₀g).hom.range
      (Y.presheaf.germ _ _ hU₀').hom.range (fun y => RingHom.mem_range) (fun y => RingHom.mem_range) hU₀
    exact GlobalTheory.T.finiteDimensional_of_finite_subring_hom_of_fractions _ _ _ _ φ hφ1 hφ2 (hfr Y _ hU₀' _ (fun y => RingHom.mem_range) (hU₀.preimage c))
  · intro U hU hU' B B' hUa hB hB'
    obtain ⟨φ, hφ1, hφ2, hφ3, ⟨eB⟩, ⟨eB'⟩⟩ := hφ U hU hU' B B' hB hB' hUa
    haveI := GlobalTheory.T.isIntegrallyClosed_sections_of_smooth_complex' Z s U hUa hU
    haveI := GlobalTheory.T.isIntegrallyClosed_sections_of_smooth_complex' Y s' (c ⁻¹ᵁ U) (hUa.preimage c) hU'
    haveI : IsIntegrallyClosed B := IsIntegrallyClosed.of_equiv eB
    haveI : IsIntegrallyClosed B' := IsIntegrallyClosed.of_equiv eB'
    obtain ⟨r1, r2, r3⟩ := GlobalTheory.T.integralClosure_of_finite_map_integrallyClosed_subrings ℂ _ _ B B' φ hφ1 hφ2 inferInstance inferInstance (hfr Z U hU B hB hUa)
      (hfr Y _ hU' B' hB' (hUa.preimage c))
    exact ⟨r1, r2, r3, GlobalTheory.T.formally_unramified_differentials_span ℂ _ _ B B' φ hφ1 hφ3⟩

end GlobalTheory.W1.SchFF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericGermDifferentialFormPullbackDominant
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HodgeCoh

section Alg
open GlobalTheory.CechDR

theorem mem_closure_smul_ιMulti_D (k B : Type) [CommRing k] [CommRing B] [Algebra k B] (z : DR k B) :
    z ∈ AddSubgroup.closure {w : DR k B | ∃ (q : ℕ) (c : B) (v : Fin q → B),
      w = c • ExteriorAlgebra.ιMulti B q (fun i => D k B (v i))} := by
  set A := AddSubgroup.closure {w : DR k B | ∃ (q : ℕ) (c : B) (v : Fin q → B),
      w = c • ExteriorAlgebra.ιMulti B q (fun i => D k B (v i))} with hA
  have hsmul : ∀ (b : B) (a : DR k B), a ∈ A → b • a ∈ A := by
    intro b a ha
    induction ha using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨q, c, v, rfl⟩ := hw
      exact AddSubgroup.subset_closure ⟨q, b * c, v, by rw [smul_smul]⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  have key : ∀ z : DR k B, ∀ a ∈ A, z * a ∈ A := by
    intro z
    induction z using indDR with
    | h b => intro a ha; rw [← Algebra.smul_def]; exact hsmul b a ha
    | hd b =>
      intro a ha
      induction ha using AddSubgroup.closure_induction with
      | mem w hw =>
        obtain ⟨q, c, v, rfl⟩ := hw
        refine AddSubgroup.subset_closure ⟨q + 1, c, Fin.cons b v, ?_⟩
        rw [mul_smul_comm, ExteriorAlgebra.ιMulti_succ_apply]
        simp [Matrix.vecTail, Function.comp_def]
      | zero => rw [mul_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
      | neg x _ hx => rw [mul_neg]; exact neg_mem hx
    | hm x y hx hy => intro a ha; rw [mul_assoc]; exact hx _ (hy a ha)
    | ha x y hx hy => intro a ha; rw [add_mul]; exact add_mem (hx a ha) (hy a ha)
  have h1 : (1 : DR k B) ∈ A :=
    AddSubgroup.subset_closure ⟨0, 1, Fin.elim0, by rw [ExteriorAlgebra.ιMulti_zero_apply, one_smul]⟩
  simpa using key z 1 h1

variable {R R' R'' B B' B'' : Type} [CommRing R] [CommRing B] [Algebra R B]
  [CommRing R'] [CommRing B'] [Algebra R' B'] [CommRing R''] [CommRing B''] [Algebra R'' B'']

theorem SemiHom.mDR_ιMulti_D {σ : R →+* R'} {α : B →+* B'} (h : SemiHom σ α) (q : ℕ) (v : Fin q → B) :
    h.mDR (ExteriorAlgebra.ιMulti B q fun i => D R B (v i)) =
      ExteriorAlgebra.ιMulti B' q fun i => D R' B' (α (v i)) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 1
  congr 1
  funext i
  exact (SemiHom.mDR_ι h _).trans (congrArg ι1 (SemiHom.m1_D h _))

theorem SemiHom.mDR_mDR {σ : R →+* R'} {α : B →+* B'} {τ : R' →+* R''} {β : B' →+* B''}
    {ρ : R →+* R''} {γ : B →+* B''} (h : SemiHom σ α) (h' : SemiHom τ β) (h'' : SemiHom ρ γ)
    (e : ∀ b, β (α b) = γ b) (x : DR R B) : h'.mDR (h.mDR x) = h''.mDR x := by
  induction x using indDR with
  | h b => simp [e]
  | hd b => simp [e]
  | hm x y hx hy => simp only [map_mul, hx, hy]
  | ha x y hx hy => simp only [map_add (f := _), hx, hy]

theorem isDRMap_mDR {k K K' : Type} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
    [Algebra k B] {g : B →+* K} {γ : B →+* K'} (hg : SemiHom (RingHom.id k) g)
    (hγ : SemiHom (RingHom.id k) γ) {ψ : K →ₐ[k] K'} {φ : DR k K →ₗ[k] DR k K'}
    (hφ : IsDRMap k ψ φ) (e : ∀ b, ψ (g b) = γ b) (z : DR k B) : φ (hg.mDR z) = hγ.mDR z := by
  induction mem_closure_smul_ιMulti_D k B z using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨q, c, v, rfl⟩ := hw
    rw [SemiHom.mDR_smul, SemiHom.mDR_ιMulti_D, hφ q (g c) (fun i => g (v i)), SemiHom.mDR_smul,
      SemiHom.mDR_ιMulti_D]
    simp only [e]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
  | neg x _ hx => rw [map_neg, map_neg, hx, map_neg]

end Alg

theorem formGermI_res_mapOver : ∀ (Z Z' : Scheme.{0}) [IsIntegral Z] [IsIntegral Z'] (p : Z ⟶ Sp ℂ) (p' : Z' ⟶ Sp ℂ),
    letI := algΓ p; letI := algΓ p'
    ∀ [inst : Algebra ℂ Z.functionField] [inst' : Algebra ℂ Z'.functionField] (hinst : inst = ffAlg p)
      (hinst' : inst' = ffAlg p') (f : Z' ⟶ Z) (hf : f ≫ p = p') (ψ : Z.functionField →ₐ[ℂ] Z'.functionField)
      (φ : DR ℂ Z.functionField →ₗ[ℂ] DR ℂ Z'.functionField), IsDRMap ℂ ψ φ →
      (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Z' ∈ f ⁻¹ᵁ V) (g : Γ(Z, V)),
        ψ ((Z.presheaf.germ V (genericPoint Z) hV).hom g) =
          (Z'.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Z') hV').hom (f.app V g)) →
      ∀ (j : ℕ) (V : Z.Opens) (V' : Z'.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
        (hη : genericPoint Z ∈ V) (hη' : genericPoint Z' ∈ V') (h : V' ≤ f ⁻¹ᵁ V)
        (y : sectionsOn (Omega p j) V),
        formGermI p' j hV' hη' hinst' (sectionsOn.res ℂ (Omega p' j) h
          (sectionsOn.mapOver (appTop_algebraMap hf) (omegaPull hf j) V y)) =
          φ (formGermI p j hV hη hinst y) := by
  intro Z Z' _ _ p p' inst inst' hinst hinst' f hf ψ φ hφ hψ j V V' hV hV' hη hη' h y
  subst hinst hinst'
  letI := algΓ p; letI := algΓ p'
  set x := (toOmEquiv p j hV).symm (sectionsOn.toΓ _ _ y) with hx
  have hy : sectionsOn.toΓ _ _ y = toOm p j V x := by
    exact (LinearEquiv.apply_symm_apply (toOmEquiv p j hV) _).symm
  have hz : sectionsOn.toΓ _ _ (sectionsOn.res ℂ (Omega p' j) h
      (sectionsOn.mapOver (appTop_algebraMap hf) (omegaPull hf j) V y)) =
      toOm p' j V' (formRes p' h j (formPull hf V j x)) := by
    have h2 : (omegaPull hf j).app V (toOm p j V x) = toOm p' j (f ⁻¹ᵁ V) (formPull hf V j x) :=
      omegaPull_toOmega hf j V x
    rw [sectionsOn.toΓ_res, sectionsOn.toΓ_mapOver, hy, h2, res_toOm]
  letI := ffAlg p; letI := ffAlg p'
  rw [formGermI_ffAlg, formGermI_ffAlg]
  simp only [formGerm, LinearMap.coe_mk, AddHom.coe_mk]
  rw [hz, ← toOmEquiv_apply p' j hV', LinearEquiv.symm_apply_apply, ← hx]
  have hγ : SemiHom (RingHom.id ℂ) ((germSec p' (h hη')).comp (appSec p p' f V)) :=
    fun r b ↦ (semiHom_appSec hf V).comp (semiHom_germSec p' (h hη')) r b
  rw [isDRMap_mDR (semiHom_germSec p hη) hγ hφ (fun b ↦ hψ V hη (h hη') b)]
  change (semiHom_germSec p' hη').mDR ((SemiHom.of_algHom (Sec.res p' h)).mDR
    ((semiHom_appSec hf V).mDR (x : DR ℂ (Sec p V)))) = _
  rw [SemiHom.mDR_mDR (semiHom_appSec hf V) (SemiHom.of_algHom (Sec.res p' h))
    ((semiHom_appSec hf V).comp (SemiHom.of_algHom (Sec.res p' h))) (fun _ ↦ rfl)]
  refine SemiHom.mDR_mDR _ (semiHom_germSec p' hη') hγ (fun b ↦ ?_) _
  change (Z'.presheaf.germ V' (genericPoint Z') hη').hom
      ((Z'.presheaf.map (homOfLE h).op).hom ((f.app V).hom b)) =
    (Z'.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Z') (h hη')).hom ((f.app V).hom b)
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]

end GlobalTheory.HodgeCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericGermDifferentialFormRestrictAffineOpen
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

namespace GlobalTheory.HodgeCoh

theorem formGermI_res : ∀ (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ),
    letI := algΓ p
    ∀ [inst : Algebra ℂ Z.functionField] (hinst : inst = ffAlg p) (j : ℕ) (V V' : Z.Opens)
      (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hη : genericPoint Z ∈ V) (hη' : genericPoint Z ∈ V')
      (h : V' ≤ V) (y : sectionsOn (Omega p j) V),
      formGermI p j hV' hη' hinst (sectionsOn.res ℂ (Omega p j) h y) = formGermI p j hV hη hinst y := by
  intro Z _ p
  letI := algΓ p
  intro inst hinst j V V' hV hV' hη hη' h y
  subst hinst
  letI := ffAlg p
  have key : (toOmEquiv p j hV').symm (sectionsOn.toΓ _ _ (sectionsOn.res ℂ (Omega p j) h y)) =
      formRes p h j ((toOmEquiv p j hV).symm (sectionsOn.toΓ _ _ y)) := by
    apply (toOmEquiv p j hV').injective
    rw [LinearEquiv.apply_symm_apply, toOmEquiv_apply, ← res_toOm, ← toOmEquiv_apply p j hV,
      LinearEquiv.apply_symm_apply, sectionsOn.toΓ_res]
  change (semiHom_germSec p hη').mDR
      ((toOmEquiv p j hV').symm (sectionsOn.toΓ _ _ (sectionsOn.res ℂ (Omega p j) h y)) : DR ℂ (Sec p V')) =
    (semiHom_germSec p hη).mDR ((toOmEquiv p j hV).symm (sectionsOn.toΓ _ _ y) : DR ℂ (Sec p V))
  rw [key]
  exact congrArg Subtype.val (SemiHom.mOm_mOm (SemiHom.of_algHom (Sec.res p h)) (semiHom_germSec p hη')
    (semiHom_germSec p hη) (fun b ↦ by
      change (Z.presheaf.germ V' (genericPoint Z) hη').hom ((Z.presheaf.map (homOfLE h).op).hom b) =
        (Z.presheaf.germ V (genericPoint Z) hη).hom b
      exact congrArg (fun f ↦ f.hom (show Γ(Z, V) from b))
        (TopCat.Presheaf.germ_res Z.presheaf (homOfLE h) (genericPoint Z) hη')) _)

end GlobalTheory.HodgeCoh
end

