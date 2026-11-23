module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulIncl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0852
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0920
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0935
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TwoRunDatumBoundUnitAtIndefinitePoint
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsEmptyOfNotAll
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1821
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2244
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2320

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleFiberProductOverMulTwoIsPullback
section
set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwoTors.TripleProd

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

def pt {T : Over S} (a b c : T ⟶ A) (h₁ : a ≫ sq A = b ≫ sq A) (h₂ : b ≫ sq A = c ≫ sq A) : T ⟶ tripO A :=
  Over.homMk (GlobalTheory.PolRoot.tri (sq A).left a.left b.left c.left (congrArg CommaMorphism.left h₁)
    (congrArg CommaMorphism.left h₂)) (by
      show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫ A.hom = _
      rw [GlobalTheory.PolRoot.tri, pullback.lift_fst_assoc, pullback.lift_fst_assoc, Over.w])

theorem pt_t₁ {T : Over S} (a b c : T ⟶ A) (h₁ h₂) : pt a b c h₁ h₂ ≫ t₁ A = a :=
  Over.OverMorphism.ext (by
    show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ = _
    rw [GlobalTheory.PolRoot.tri, pullback.lift_fst_assoc, pullback.lift_fst])

theorem pt_t₂ {T : Over S} (a b c : T ⟶ A) (h₁ h₂) : pt a b c h₁ h₂ ≫ t₂ A = b :=
  Over.OverMorphism.ext (by
    show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ = _
    rw [GlobalTheory.PolRoot.tri, pullback.lift_fst_assoc, pullback.lift_snd])

theorem pt_t₃ {T : Over S} (a b c : T ⟶ A) (h₁ h₂) : pt a b c h₁ h₂ ≫ t₃ A = c :=
  Over.OverMorphism.ext (by
    show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.snd _ _ ≫ pullback.snd _ _ = _
    rw [GlobalTheory.PolRoot.tri, pullback.lift_snd_assoc, pullback.lift_snd])

theorem ext₃ {T : Over S} {m n : T ⟶ tripO A} (h₁ : m ≫ t₁ A = n ≫ t₁ A) (h₂ : m ≫ t₂ A = n ≫ t₂ A)
    (h₃ : m ≫ t₃ A = n ≫ t₃ A) : m = n := by
  have e₁ : m.left ≫ pullback.fst _ _ ≫ pullback.fst _ _ = n.left ≫ pullback.fst _ _ ≫ pullback.fst _ _ :=
    congrArg CommaMorphism.left h₁
  have e₂ : m.left ≫ pullback.fst _ _ ≫ pullback.snd _ _ = n.left ≫ pullback.fst _ _ ≫ pullback.snd _ _ :=
    congrArg CommaMorphism.left h₂
  have e₃ : m.left ≫ pullback.snd _ _ ≫ pullback.snd _ _ = n.left ≫ pullback.snd _ _ ≫ pullback.snd _ _ :=
    congrArg CommaMorphism.left h₃
  have e₄ := e₂
  rw [pullback.condition] at e₄
  refine Over.OverMorphism.ext (pullback.hom_ext (pullback.hom_ext ?_ ?_) (pullback.hom_ext ?_ ?_))
  · exact (Category.assoc _ _ _).trans (e₁.trans (Category.assoc _ _ _).symm)
  · exact (Category.assoc _ _ _).trans (e₂.trans (Category.assoc _ _ _).symm)
  · exact (Category.assoc _ _ _).trans (e₄.trans (Category.assoc _ _ _).symm)
  · exact (Category.assoc _ _ _).trans (e₃.trans (Category.assoc _ _ _).symm)

theorem comp_ψ_fst {T : Over S} (m : T ⟶ tripO A) :
    ((m ≫ ψ A) ≫ fst _ _) ≫ incl A = (m ≫ t₁ A)⁻¹ * (m ≫ t₂ A) := by
  rw [Category.assoc, Category.assoc, ψ, lift_fst_assoc, dif_incl, MonObj.comp_mul, GrpObj.comp_inv]

theorem comp_ψ_snd {T : Over S} (m : T ⟶ tripO A) :
    ((m ≫ ψ A) ≫ snd _ _) ≫ incl A = (m ≫ t₂ A)⁻¹ * (m ≫ t₃ A) := by
  rw [Category.assoc, Category.assoc, ψ, lift_snd_assoc, dif_incl, MonObj.comp_mul, GrpObj.comp_inv]

theorem ext₂ {T : Over S} {m n : T ⟶ tripO A} (h₁ : m ≫ t₁ A = n ≫ t₁ A) (h : m ≫ ψ A = n ≫ ψ A) : m = n := by
  have e₂ := comp_ψ_fst m
  have e₃ := comp_ψ_snd m
  rw [h, comp_ψ_fst, h₁] at e₂
  have h₂ : m ≫ t₂ A = n ≫ t₂ A := (mul_left_cancel e₂).symm
  rw [h, comp_ψ_snd, h₂] at e₃
  exact ext₃ h₁ h₂ (mul_left_cancel e₃).symm

theorem mul_sq {T : Over S} (a : T ⟶ A) (x : T ⟶ Two A) : a ≫ sq A = (a * (x ≫ incl A)) ≫ sq A := by
  rw [comp_sq, comp_sq, mul_pow, incl_sq, _root_.mul_one]

theorem exists_pt {T : Over S} (a : T ⟶ A) (q : T ⟶ Two A ⊗ Two A) :
    ∃ m : T ⟶ tripO A, m ≫ t₁ A = a ∧ m ≫ ψ A = q := by
  refine ⟨pt a (a * ((q ≫ fst _ _) ≫ incl A)) ((a * ((q ≫ fst _ _) ≫ incl A)) * ((q ≫ snd _ _) ≫ incl A))
    (mul_sq _ _) (mul_sq _ _), pt_t₁ _ _ _ _ _, ?_⟩
  refine CartesianMonoidalCategory.hom_ext _ _ (two_ext ?_) (two_ext ?_)
  · rw [comp_ψ_fst, pt_t₁, pt_t₂, inv_mul_cancel_left]
  · rw [comp_ψ_snd, pt_t₂, pt_t₃, inv_mul_cancel_left]

theorem isPullback {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] :
    IsPullback (t₁ A).left (ψ A).left A.hom (Two A ⊗ Two A).hom := by
  have w : (t₁ A).left ≫ A.hom = (ψ A).left ≫ (Two A ⊗ Two A).hom := (Over.w _).trans (Over.w _).symm
  have key : ∀ s : PullbackCone A.hom (Two A ⊗ Two A).hom, ∃ l : s.pt ⟶ (tripO A).left,
      l ≫ (t₁ A).left = s.fst ∧ l ≫ (ψ A).left = s.snd := fun s => by
    obtain ⟨m, h₁, h₂⟩ := exists_pt (T := Over.mk (s.fst ≫ A.hom)) (Over.homMk s.fst rfl)
      (Over.homMk s.snd s.condition.symm)
    exact ⟨m.left, congrArg CommaMorphism.left h₁, congrArg CommaMorphism.left h₂⟩
  choose l hl₁ hl₂ using key
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w l hl₁ hl₂ fun s m h₁ h₂ => ?_⟩⟩
  have hw : ∀ k : s.pt ⟶ (tripO A).left, k ≫ (t₁ A).left = s.fst → k ≫ (tripO A).hom = s.fst ≫ A.hom :=
    fun k hk => by rw [← hk, Category.assoc, Over.w]
  have e : (Over.homMk m (hw m h₁) : Over.mk (s.fst ≫ A.hom) ⟶ tripO A) = Over.homMk (l s) (hw _ (hl₁ s)) :=
    ext₂ (Over.OverMorphism.ext (h₁.trans (hl₁ s).symm)) (Over.OverMorphism.ext (h₂.trans (hl₂ s).symm))
  exact congrArg CommaMorphism.left e

end GlobalTheory.TwoTors.TripleProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjCoefAt
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TwConj

open GlobalTheory.ConjTwist

theorem scale_pow_eq_of_isScale {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) {c c' : ℂ}
    (h : IsScale Rl v₀ B c) (h' : IsScale Rl v₀ B c') : ∃ k : ℕ, k ≠ 0 ∧ c' ^ k = c ^ k := by
  obtain ⟨gR, cR0, cL0, hT, u, hu, hF⟩ := h
  obtain ⟨gR', cR0', cL0', hT', u', hu', hF'⟩ := h'
  have huu : u' = u := funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
  subst huu
  obtain ⟨a, ⟨k, hk, hak⟩, ha⟩ := _root_.GlobalTheory.CoefRoot.coef_root _ _ _ _ _ _ _ _ _ _ _ _ _ hT hT' j
  obtain ⟨F, x, hx⟩ := _root_.GlobalTheory.CoeffNonvanish.exists_coefFn_ne_zero (FWT.lamV D j)
  have e1 := hF' F
  rw [ha] at e1
  erw [LinearMap.map_smul, LinearMap.map_smul, hF F] at e1
  have e2 := congrFun e1 x
  simp only [Pi.smul_apply, smul_eq_mul] at e2
  have hc : c' = D.what₂.embLL a * c := by
    have h3 : D.what₂.embLL a * c * coefFn D.what₂.embLL (FWT.lamV D j) (F : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) x =
        c' * coefFn D.what₂.embLL (FWT.lamV D j) (F : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) x := by
      rw [mul_assoc]; exact e2
    exact (mul_right_cancel₀ hx h3).symm
  refine ⟨k, hk, ?_⟩
  rw [hc, mul_pow, ← map_pow, hak, map_one, one_mul]

theorem coefFn_map_eq {D : D7} {n : ℕ} {K : Type} [Field K] (σ : K →+* ℂ) (lam : D.what₂.Tau → DomWeight n)
    (F : Formalism.L2.DIV.Pol K D.what₂.Tau n) : coefFn (RingHom.id ℂ) lam (MvPolynomial.map σ F) = coefFn σ lam F := by
  funext x
  simp only [coefFn, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map, RingHom.id_comp]

theorem exists_fixed_of_mem_span {D : D7} (j : Fin D.R.m) {W M : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup M] [Module ℂ M]
    (Φ : W →ₗ[ℂ] M) (c : VsV D j ℂ →ₗ[ℂ] W) (a₀ : ℂ) (S : Set (VV (↥D.LL0) (lamV D j))) {P : M}
    (hP : P ∈ Submodule.span (smallInt D)
      {P | ∃ Fv ∈ S, P = Φ (c (a₀ • GlobalTheory.CoefModel.mapVV (Formalism.L2.Host.embLL0 D) (lamV D j) Fv))}) :
    ∃ y : VsV D j ℂ, P = a₀ • Φ (c y) ∧
      ∀ τ : ℂ ≃+* ℂ, (∀ z, τ (Formalism.L2.Host.embLL0 D z) = Formalism.L2.Host.embLL0 D z) → ConjVec j τ y y := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨Fv, -, rfl⟩ := hP
    refine ⟨GlobalTheory.CoefModel.mapVV (Formalism.L2.Host.embLL0 D) (lamV D j) Fv, by rw [c.map_smul, Φ.map_smul], fun τ hτ => ?_⟩
    change MvPolynomial.map _ _ = MvPolynomial.map _ (MvPolynomial.map _ _)
    rw [MvPolynomial.map_map, show (τ : ℂ →+* ℂ).comp (Formalism.L2.Host.embLL0 D) = Formalism.L2.Host.embLL0 D from RingHom.ext hτ]
  | zero => exact ⟨0, by rw [c.map_zero, Φ.map_zero, smul_zero], fun τ _ => (map_zero _).symm⟩
  | add P₁ P₂ _ _ h1 h2 =>
    obtain ⟨y1, rfl, c1⟩ := h1
    obtain ⟨y2, rfl, c2⟩ := h2
    refine ⟨y1 + y2, by rw [map_add c, map_add Φ, smul_add], fun τ hτ => ?_⟩
    have e1 := c1 τ hτ
    have e2 := c2 τ hτ
    unfold ConjVec at e1 e2 ⊢
    rw [Submodule.coe_add, map_add (f := _), ← e1, ← e2]
  | smul a P₁ _ h1 =>
    obtain ⟨y1, rfl, c1⟩ := h1
    refine ⟨(a : ℂ) • y1, ?_, fun τ hτ => ?_⟩
    · rw [c.map_smul, Φ.map_smul, smul_comm a₀]
      rfl
    · have e1 := c1 τ hτ
      unfold ConjVec at e1 ⊢
      obtain ⟨o, ho⟩ := a.2
      have ha : (τ : ℂ →+* ℂ) (a : ℂ) = a := by rw [← ho]; exact hτ _
      rw [Submodule.coe_smul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← e1, ha]


end GlobalTheory.BigOn.Exp.TwConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEndomorphismCarriesPeriodPointBala
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.Mum.KeepsIota

variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_v (hG : GlobalFnsSt) (D : DegPre R) (f g : D.P.A ⟶ D.P.A) [IsMonHom f] [IsMonHom g]
    (k : D.X → D.X) (hk : ∀ χ, D.c (k χ) = D.c χ ≫ f)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)) (hu : u.IsGen)
    (u₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L)) (χ : D.X) :
    ∃ v : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 _) (k χ)) (D.Oφ g χ)) (Sum.elim Oε Oinvε)),
      Normd v ∧ ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J),
        Good D.P.L z J → val v (r ≫ x.left) z J = val u (r ≫ (lift (cP D T χ) x).left) z J := by
  have cf : ∀ T, cP D T (k χ) = cP D T χ ≫ f := fun T => by
    rw [cP, hk, ← Category.assoc]; rfl
  obtain ⟨v, hv, vv⟩ := exists_gen D.P.isLB
    (φ' := Sum.elim (D.Oφ (𝟙 _) (k χ)) (D.Oφ g χ)) (ε' := Sum.elim Oε Oinvε)
    (fun U _ h => by
      refine (prod_ros _ _ (cP D _ χ) (𝟙 D.P.A) h).trans (Eq.symm ?_)
      refine (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (GlobalTheory.UT.OLinEnd.prod_Oφ D (𝟙 _) (k χ) h)
        (GlobalTheory.UT.OLinEnd.prod_Oφ_inv D g χ h)).trans ?_
      rw [cf, Category.id_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.pullGen D.P.L _ _ u (lift (cP D D.P.A χ) (𝟙 D.P.A)).left) (pullGen_isGen _ _ _ _ hu _)
  have key : ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J),
      Good D.P.L z J → val v (r ≫ x.left) z J = val u (r ≫ (lift (cP D T χ) x).left) z J := fun T x Z r z J hJ => by
    rw [vv Z _ z J hJ, val_pull hJ, Category.assoc, ← Over.comp_left, comp_lift, comp_cP, Category.comp_id]
  refine ⟨v, ⟨hv, corr_of_val D.P.isLB fun y J hJ => ?_⟩, key⟩
  have C : IsCub (cubV D.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J) := isCub_cubV D.cub hJ
  have e := (ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) hJ 1 1 (cP D _ χ)).2
  rw [_root_.mul_one, MonObj.one_comp, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
  have e' : val₂ u (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J (cP D _ χ) 1 = 1 := mul_eq_left.1 e.symm
  have k' := key (𝟙_ (Over (Spec (CommRingCat.of R)))) 1 _ (𝟙 _) y J hJ
  have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left = eSec D.P.A := by
    rw [Hom.one_def, toUnit_unit, Category.id_comp]; rfl
  rw [o] at k'
  refine (val_pull hJ _ _ _).trans (k'.trans (Eq.trans ?_ (val_one _).symm))
  rw [Category.id_comp]
  exact e'

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ E : EndU U.toUnifPre, E.aB = a → E.h = h' → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (y : D.toPre.X) (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (h y) g' := by
  intro R _ _ _ _ D A G _ _ _ U a a' h h' hd E hEa hEh F _ _ _ y g g' hg hact
  subst hEa hEh
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  have hs := (endData_symm_and_ofOAct R D.toPre).1 _ _ _ _ hd
  obtain ⟨ha, ha', -, hc, hc', -⟩ := hd
  obtain ⟨-, -, hr', -, -, hbal'⟩ := hs
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.toPre.P.isAb D.toPre.P.isLB _ _ hr'
  obtain ⟨gb, gv⟩ := (isIota_iff _ _).1 hg
  refine (isIota_iff _ _).2 ⟨?_, fun χ z J hJ => ?_⟩
  · rw [hact.1, gb, cP, cP, hc, ← Category.assoc]
  · obtain ⟨v, hv, vv⟩ := exists_v hG D.toPre a' E.aB E.h hc' u hu u₀ χ
    have k1 : val (E.u χ) g.b.left z J = val u (lift (cP D.toPre _ χ) g.b).left z J := by
      have := vv _ g.b _ (𝟙 _) z J hJ
      rw [Category.id_comp, Category.id_comp] at this
      exact (GlobalTheory.UT.SymFrame.normd_unique hG (E.u_norm χ) hv _ z J hJ).trans this
    rw [hact.2 χ z J hJ, gv _ z J hJ, k1, gb]
    let κ : TF (R := R) F ⟶ TK R := Over.homMk (𝟙 _ ≫ jFK (R := R) F) (by rw [Category.id_comp]; rfl)
    have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hbal' u hu u₀ χ y) κ.left)
    have e' : val (LB.pullGen D.toPre.P.L _ _ u (D.toPre.pt2 χ y)) κ.left z J =
        val u (lift (cP D.toPre _ χ) (cP D.toPre _ y)).left z J := by
      rw [val_pull hJ, ← comp_cP D.toPre κ, ← comp_cP D.toPre κ y, ← comp_lift]; rfl
    rw [← e']
    exact (congrArg₂ (· * ·) (tau_symm (𝟙 (TF (R := R) F)) hJ _ _) rfl).trans
      (e.trans (tau_symm (𝟙 (TF (R := R) F)) hJ _ _))

end GlobalTheory.Mum.KeepsIota

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedAlongAllTraitsRestrictAffineOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyVals


open GlobalTheory.TorsionFormCompare GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum in
theorem hasUnif_of_iso {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (hV : IsAdicComplete (IsLocalRing.maximalIdeal V) V) (G G₀ : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀]
    [IsCommMonObj G₀] (ε : G ≅ G₀) (hε : IsMonHom ε.hom) (hsa : IsSemiAbelian G₀) (L₀ : LB G₀.left)
    (h : HasUnif G₀ L₀) : HasUnif G (L₀.pull ε.hom.left) := by
  obtain ⟨D, A₀, U₀, hL⟩ := h
  have hR : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  have he : eSec G ≫ ε.hom.left = 𝟙 _ ≫ eSec G₀ := by
    refine Eq.trans ?_ (Category.id_comp _).symm
    exact congrArg (fun f => f.left) (IsMonHom.one_hom ε.hom)
  let L' : RigLB G := ⟨U₀.LG.L.pull ε.hom.left, rigPullOf ε.hom.left (𝟙 _) he U₀.LG.L U₀.LG.rig,
    LB.isLB_pull U₀.LG.isLB _,
    GlobalTheory.CubePullLawChecks.rigPullIsGen ε.hom.left (𝟙 _) he U₀.LG.L U₀.LG.rig U₀.LG.isLB U₀.LG.rigGen⟩
  let w : LB.Iso L'.L (U₀.LG.L.pull ε.hom.left) := idIso L'.L
  have hw : RigAlong ε.hom U₀.LG L' w :=
    ⟨idIso_isGen L'.isLB, (maps_iff w _ (fun _ => eSec G₀) _ L'.rig U₀.LG.rig (𝟙 _) _
      (rigPull_le _ _ he U₀.LG.L) (fun _ => rfl)).1 (idIso_maps L')⟩
  obtain ⟨W, hW, hψ⟩ := psiOnExists V (IsLocalRing.maximalIdeal V) hR D
  obtain ⟨hD, -⟩ := exists_isIdPull V D.toPre W hW hψ
  obtain ⟨bc, U, -, -, hLG, -, -⟩ :=
    exists_unif_move V (IsLocalRing.maximalIdeal V) D A₀ G₀ G ε hR hsa hε U₀ L' w hw hD
  refine ⟨D, A₀, U, ?_⟩
  rw [hLG]
  exact LBIso.chartPull (GlobalTheory.chartPullPull _ _) (GlobalTheory.chartPullPull _ _) hL

theorem unifAlong_bG {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) {R : Type} [CommRing R]
    (f : Sp R ⟶ S) (hG : IsSemiAbelian G) (h : UnifAlong G L.L) : UnifAlong (bG G f) (bL L f).L := by
  intro V _ _ _ _ hV hf ξ hξ _
  have hξ' : ((ξ ≫ f) ⁻¹' abLocus G).Nonempty := by
    obtain ⟨p, hp⟩ := hξ
    refine ⟨p, ?_⟩
    have := (abLocus_pullback (G' := bG G f) abLocusOne hG (isGrpPullback_pullback G f).1 (ξ p)).2 hp
    simpa using this
  obtain ⟨ε, hε, hφ⟩ := grpPullback_iso ((isGrpPullback_pullback (bG G f) ξ).comp (isGrpPullback_pullback G f))
    (isGrpPullback_pullback G (ξ ≫ f))
  obtain ⟨D, A, U, hU⟩ := hasUnif_of_iso hV _ _ ε hε (IsSemiAbelian.pullback (ξ ≫ f) G hG) _ (h V hV hf (ξ ≫ f) hξ')
  refine ⟨D, A, U, LBIso.trans U.LG.isLB (LB.isLB_pull (LB.isLB_pull L.isLB _) _)
    (LB.isLB_pull (bL L f).isLB _) hU ?_⟩
  exact LBIso.chartPull (h := ε.hom.left)
    (chartPullLinComb L.L _ (fun _ : PUnit => ε.hom.left) (fun _ => pullback.fst G.hom (ξ ≫ f)) (fun _ => 1) _ fun _ => rfl)
    (chartPullLinComb L.L _ (fun _ : PUnit => pullback.fst (bG G f).hom ξ) (fun _ => pullback.fst G.hom (ξ ≫ f))
      (fun _ => 1) _ fun _ => hφ.symm)
    (PolBaseChange.lbIso_refl (LB.isLB_pull L.isLB _))

theorem unifAlong_affineOpen : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (W : S.Opens) (hW : IsAffineOpen W),
    IsSemiAbelian G → UnifAlong G L.L → UnifAlong (KeyVals.bG G hW.fromSpec) (KeyVals.bL L hW.fromSpec).L :=
  fun _ G _ _ L _ hW hG h => unifAlong_bG G L hW.fromSpec hG h

end GlobalTheory.KeyVals

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformiserOrderEqOfAssociatedStalkImage
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc

theorem uOrdEq_stalkHom_of_associated : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω) (x : M.Z) (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∀ (R : Type) [CommRing R] (j : M.Z.presheaf.stalk x →+* R) (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (h : T.V →+* V') (g' : R →+* V'), Function.Injective h → Irreducible (h T.ϖ) → spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ → ∀ (a : M.Z.presheaf.stalk x) (k : ℕ), Associated (g' (j a)) (h T.ϖ ^ k) → UOrdEq M T ξ (M.stalkHom x a) k := by
  intro E _ _ _ H Dw l Xo c o' Ω _ _ _ M x T ξ hx R _ j V' _ _ _ h g' hinj hirr hcomm a k ha
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  let v : M.Z.presheaf.stalk x ⟶ CommRingCat.of T.V :=
    M.Z.presheaf.stalkSpecializes hx ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of T.V) ξ
  have hv : Spec.map v ≫ M.Z.fromSpecStalk x = ξ := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have e1 : Spec.map (CommRingCat.ofHom j ≫ CommRingCat.ofHom g') = Spec.map (v ≫ CommRingCat.ofHom h) := by
    rw [← cancel_mono (M.Z.fromSpecStalk x), Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, hv]
    exact hcomm
  have e2 : g' (j a) = h (v.hom a) := congrArg (fun φ => φ.hom a) (Spec.map_injective e1)
  have e3 : M.val (jK T.V ≫ ξ) (M.stalkHom x a) = algebraMap T.V (FractionRing T.V) (v.hom a) := by
    refine (RatModel.val_spMap_comp (algebraMap T.V (FractionRing T.V)) ξ hx (M.stalkEquiv x a)).trans ?_
    rw [RatModel.valLoc, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply]
  rw [e2] at ha
  have h0 : v.hom a ≠ 0 := fun h0 => by
    rw [h0, map_zero] at ha
    exact pow_ne_zero k hirr.ne_zero (associated_zero_iff_eq_zero _ |>.1 ha.symm)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 T.irr
  have h1 : Associated (h T.ϖ ^ n) (h T.ϖ ^ k) := by
    refine Associated.trans ?_ ha
    rw [hu, map_mul, map_pow]
    exact (associated_unit_mul_left _ _ (u.isUnit.map h)).symm
  have hn : n = k := le_antisymm ((pow_dvd_pow_iff hirr.ne_zero hirr.not_isUnit).1 h1.dvd)
    ((pow_dvd_pow_iff hirr.ne_zero hirr.not_isUnit).1 h1.symm.dvd)
  exact ⟨u, by rw [e3, hu, hn, mul_comm]⟩

end GlobalTheory.UPoinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryActionBaseChangeSubalgebra
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UCovSep

theorem uAct_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R R' : Subalgebra o Ω) (h : R ≤ R') (P : PolAV (Sp R)) (P' : PolAV (Sp R')) (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A (spMap (Subalgebra.inclusion h).toRingHom) φ → LBIso P'.L (P.L.pull φ) → ∀ (act : 𝓞 E → (P.A ⟶ P.A)) (u : Sp (ratHull R) ⟶ Xo.XF c), (∀ a, IsMonHom (act a)) → GlobalTheory.UCovSep.UAct Xo c P act (toRat R) u → ∃ act' : 𝓞 E → (P'.A ⟶ P'.A), (∀ a, IsMonHom (act' a)) ∧ (∀ a, (act' a).left ≫ φ = φ ≫ (act a).left) ∧ GlobalTheory.UCovSep.UAct Xo c P' act' (toRat R') (spMap (Subalgebra.inclusion (ratHull_mono h)).toRingHom ≫ u) := by
  intro E _ _ _ H Dw l Xo c o Ω _ _ _ R R' h P P' φ hφ hL act u hact hU

  have inj : ∀ {T : Over (Sp R')} {x y : T ⟶ P'.A}, pushPt hφ.1.w x = pushPt hφ.1.w y → x = y := fun {T x y} e =>
    Over.OverMorphism.ext (hφ.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))
  let act' : 𝓞 E → (P'.A ⟶ P'.A) := fun a => Over.homMk (hφ.1.lift (φ ≫ (act a).left) P'.A.hom
    (by rw [Category.assoc, Over.w, hφ.1.w])) (hφ.1.lift_snd _ _ _)
  have ha : ∀ a, (act' a).left ≫ φ = φ ≫ (act a).left := fun a => hφ.1.lift_fst _ _ _
  have pa : ∀ {T : Over (Sp R')} (x : T ⟶ P'.A) a, pushPt hφ.1.w (x ≫ act' a) = pushPt hφ.1.w x ≫ act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have pm : ∀ {T : Over (Sp R')} (x y : T ⟶ P'.A), pushPt hφ.1.w (x * y) = pushPt hφ.1.w x * pushPt hφ.1.w y :=
    fun x y => map_mul (pushHom hφ _) x y
  have hact' : ∀ a, IsMonHom (act' a) := fun a => isMonHom_of_mul _ fun T x y => inj (by
    have := hact a
    rw [pa, pm, pm, pa, pa, MonObj.mul_comp])
  refine ⟨act', hact', ha, ?_⟩

  obtain ⟨G, _, α, β, hα, hβ, hLG, hf⟩ := hU
  set g := (Subalgebra.inclusion (ratHull_mono h)).toRingHom with hg
  have hG := isGrpPullback_pullback G (spMap g)
  have e : spMap g ≫ spMap (toRat R) = spMap (toRat R') ≫ spMap (Subalgebra.inclusion h).toRingHom := by
    rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  have hα₀ : IsGrpPullback ((Over.pullback (spMap g)).obj G) P.A
      (spMap (toRat R') ≫ spMap (Subalgebra.inclusion h).toRingHom) (pullback.fst _ _ ≫ α) := (hG.comp hα).congr e rfl
  have w : (pullback.fst G.hom (spMap g) ≫ α) ≫ P.A.hom =
      (((Over.pullback (spMap g)).obj G).hom ≫ spMap (toRat R')) ≫ spMap (Subalgebra.inclusion h).toRingHom := by
    rw [Category.assoc]; exact hα₀.1.w
  have e₁ := hφ.1.lift_fst _ _ w
  have hα' := hφ.cancel (hα₀.congr rfl e₁.symm) (hφ.1.lift_snd _ _ w)
  have hβ' := (hG.comp hβ).congr (Category.assoc _ _ _).symm rfl
  refine ⟨_, _, hφ.1.lift _ _ w, pullback.fst _ _ ≫ β, hα', hβ', ?_, fun a => ?_⟩
  · exact LBIso.trans (pull_isLB P'.isLB _) (pull_isLB P.isLB _) (pull_isLB Xo.univ.t.PP.isLB _)
      (GenSpread.lbIso_pull_of_lbIso hL _ e₁.symm) (GenSpread.lbIso_pull_comp _ rfl rfl hLG)
  · obtain ⟨f, hfα, hfβ⟩ := hf a
    have hfl : ((Over.pullback (spMap g)).map f).left ≫ pullback.fst G.hom (spMap g) = pullback.fst G.hom (spMap g) ≫ f.left :=
      pullback.lift_fst _ _ _
    refine ⟨(Over.pullback (spMap g)).map f, ?_, ?_⟩
    · apply hφ.1.hom_ext
      · rw [Category.assoc, e₁, Category.assoc, ha, ← Category.assoc (hφ.1.lift _ _ w), e₁,
          ← Category.assoc _ (pullback.fst _ _), hfl, Category.assoc, hfα, Category.assoc]
      · rw [Category.assoc, hφ.1.lift_snd, Category.assoc, Over.w, hφ.1.lift_snd, ← Category.assoc, Over.w]
    · rw [← Category.assoc, hfl, Category.assoc, hfβ, Category.assoc]

end GlobalTheory.UCovSep
end
end

