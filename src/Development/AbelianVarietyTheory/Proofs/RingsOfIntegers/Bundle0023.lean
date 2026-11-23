module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DvdOfAppEqZeroOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CstDvdOfCstMulEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsSecKIsUnit
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.GenericGenerated

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem gs_secOfIso {Y Z : Scheme.{0}} {A B : LB Y} (u : LB.Iso A B) (t : LB.Sec B) (hu : u.IsGen) (hA : A.IsLB)
    (hB : B.IsLB) (a : A.ι) (b : B.ι) (r : Z ⟶ Y) (z : Z) (hz : r z ∈ A.U a ⊓ B.U b) :
    gs r z (A.U a) ((secOfIso t hu hA hB).f a) =
      ((gm r z ((LB.div B A).U (b, a)) (u.s (b, a)))⁻¹).val * gs r z (B.U b) (t.f b) := by
  refine (gs_res r z inf_le_left hz _).symm.trans ?_
  refine (congrArg (gs r z (A.U a ⊓ B.U b)) (secOfIso_spec t hu hA hB a b)).trans ?_
  unfold isoCand
  refine (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ?_ (gs_res r z inf_le_right hz _))
  rw [gs_unit r z _ hz, map_inv, gm_res r z (divLe a b) hz]

theorem exists_sec_isUnit {X X' Y W Z : Scheme.{0}} {L : LB X} {M : LB X'} (hL : L.IsLB) (hM : M.IsLB)
    (g : Y ⟶ X) (gi : X ⟶ Y) (e₁ : gi ≫ g = 𝟙 X) (e₂ : g ≫ gi = 𝟙 Y) (p : Y ⟶ X')
    (H : LBIso (L.pull g) (M.pull p)) (i : W ⟶ X) (ρ : Y ⟶ W) (hρ : ρ ≫ i = g) (k : ℕ)
    (s : LB.Sec (LB.LinComb L (K := Fin k) (fun _ => i) (fun _ => 1))) (r : Z ⟶ Y) (z : Z)
    (hs : ρ (r z) ∈ nonzeroLocus s) (J : (Z ⟶ X') → M.ι) (hJ : Good M z J) :
    ∃ t : LB.Sec (LB.LinComb M (K := Fin 1) (fun _ => p) (fun _ => (k : ℤ))), IsUnit (sval t r z J) := by
  obtain ⟨w, hw⟩ : LBIso L (M.pull (gi ≫ p)) :=
    LBIso.chartPull (chartPullSec L g gi e₁)
      (chartPullSame M (fun _ : PUnit => gi ≫ p) (fun _ => p) (fun _ => 1) gi fun _ => rfl) H
  have H₂ := iso_linComb ((isGen_iff w).1 hw) (fun _ : Fin 1 => g) (fun _ => (k : ℤ))
  have ep : (fun _ : Fin 1 => g ≫ gi ≫ p) = fun _ => p := by
    funext _; rw [← Category.assoc, e₂, Category.id_comp]
  rw [ep] at H₂
  obtain ⟨u, hu⟩ := LBIso.symm H₂
  choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
  have hI' : Good L z I := hI
  have h1 : (LB.oneGen L (Y := Y)).IsGen := fun i j => (map_one _).trans
    ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm
  obtain ⟨s', hs'⟩ := exists_sec hL (φ' := fun _ : Fin 1 => g) (ε' := fun _ => (k : ℤ))
    (fun V _ h => by simp [Fintype.prod_sum_type, hρ])
    (pullMulSec s ρ (LB.oneGen L (Y := Y)) h1)
  have u₁ : IsUnit (sval s (r ≫ ρ) z I) := by
    obtain ⟨j, hj, hu⟩ := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_nonzeroLocus s _).1 hs
    have hj' : (r ≫ ρ) z ∈ LB.wchart L (fun _ : Fin k => i) j := hj
    have h₁ : IsUnit (gs (r ≫ ρ) z (LB.wchart L (fun _ : Fin k => i) j) (s.f j)) :=
      (congrArg IsUnit (gs_stalkMap (r ≫ ρ) z _ hj' _)).mpr (hu.map _)
    exact isUnit_of_mul_isUnit_right ((congrArg IsUnit (sec_trans s (r ≫ ρ) z hj' (hI'.mem _ _))).mp h₁)
  have u₂ : IsUnit (sval s' r z I) := by
    rw [hs' Z r z I hI', sval_pullMulSec s ρ _ _ r z hI']
    exact u₁.mul (Units.isUnit _)
  refine ⟨secOfIso s' hu (linComb_isLB M hM _ _) (linComb_isLB L hL _ _), ?_⟩
  have e := gs_secOfIso u s' hu (linComb_isLB M hM _ _) (linComb_isLB L hL _ _)
    (fun _ => J (r ≫ p)) (fun _ => I (r ≫ g)) r z
    ⟨hJ.mem (fun _ : Fin 1 => p) r, hI'.mem (fun _ : Fin 1 => g) r⟩
  exact (congrArg IsUnit e).mpr ((Units.isUnit _).mul u₂)

theorem exists_secK_isUnit : AmpleSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ), 4 ≤ k → ∀ (Z : Scheme.{0}) (r : Z ⟶ pullback G.hom (jK R)) (z : Z) (J), Geo.Tor.Good U.LG.L z J → ∃ s : U.SecK k, IsUnit (Geo.Tor.sval s r z J) := by
  intro hA R _ _ I D A G _ _ U k hk Z r z J hJ
  obtain ⟨N, s, hcov⟩ := (hA _ A k hk).1 ⊤ (isAffineOpen_top _)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : pullback G.hom (jK R) ⟶ (A.A.hom ⁻¹ᵁ ⊤).toScheme,
      ρ ≫ (A.A.hom ⁻¹ᵁ ⊤).ι = U.gen.hom.left :=
    ⟨IsOpenImmersion.lift _ U.gen.hom.left (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show ρ (r z) ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
  exact exists_sec_isUnit A.isLB U.LG.isLB U.gen.hom.left U.gen.inv.left
    (congrArg (fun q => q.left) U.gen.inv_hom_id) (congrArg (fun q => q.left) U.gen.hom_inv_id) _ U.ext _ ρ hρ k
    (s i) r z hi J hJ

end GlobalTheory.GenericGenerated
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpInt

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1

theorem secScal_sval {X Y Y' Z : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  have e := H (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k)) (by
    rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (r ≫ q)) e)
  have hm : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) :=
    ⟨hJ.mem φ₁ r, hJ.mem (fun k => h ≫ φ₂ k) r⟩
  have le : LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) ≤
      h ⁻¹ᵁ LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k)) :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  rw [sval_of s₂ (r ≫ h) z J (fun k => J (r ≫ h ≫ φ₂ k)) (fun k => by rw [Category.assoc])]
  have e2 := congrArg (gs r z _) e
  exact ((gs_res r z _ hm _).trans (gs_pull r h z _ (le hm.2) _)).symm.trans (e2.trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_res r z le_top hm _) (gs_res r z _ hm _))))

theorem gs_scal {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (q : Z ⟶ Y) (z : Z)
    (a : R) : gs q z ⊤ (scal p a) = cst (q ≫ p) z a := gs_pull q p z ⊤ trivial _

section Mul

variable {R : Type} [CommRing R] {Y : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of R)} {L : LB Y}

theorem exists_secIsMul (a : R) (τ : LB.Sec L) : ∃ σ, SecIsMul p a σ τ :=
  ⟨SecOps.secScale (scal p a) τ, fun _ => rfl⟩

theorem secIsMul_trans {a b : R} {ρ σ τ : LB.Sec L} (h₁ : SecIsMul p a ρ σ) (h₂ : SecIsMul p b σ τ) :
    SecIsMul p (a * b) ρ τ := fun j => by
  rw [h₁ j, h₂ j, ← _root_.mul_assoc, scal, scal, scal, map_mul, map_mul]
  exact congrArg (· * τ.f j) (map_mul _ _ _).symm

theorem secIsMul_one (σ : LB.Sec L) : SecIsMul p 1 σ σ := fun j => by
  rw [scal, map_one, map_one, Out.resTop, map_one, _root_.one_mul]

theorem secIsMul_symm {u : Rˣ} {σ τ : LB.Sec L} (h : SecIsMul p (u⁻¹ : Rˣ).val σ τ) : SecIsMul p u.val τ σ := by
  obtain ⟨ρ, hρ⟩ := exists_secIsMul (p := p) u.val σ
  have h₁ := secIsMul_trans hρ h
  rw [Units.mul_inv] at h₁
  exact fun j => ((secIsMul_one (p := p) τ j).trans (h₁ j).symm).trans (hρ j)

end Mul

theorem generic_app_injective {V : Type} [CommRing V] [IsDomain V] (G : Over (Spec (CommRingCat.of V))) [Flat G.hom]
    (W : G.left.Opens) : Function.Injective ((pullback.fst G.hom (jK V)).app W).hom := by
  have : IsDominant (jK V) := isDominant_jK
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK V)
  have : IsSchemeTheoreticallyDominant (pullback.fst G.hom (jK V)) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback G.hom (jK V)).flip
  exact (pullback.fst G.hom (jK V)).app_injective W

theorem secIsMul_of_generic {V : Type} [CommRing V] [IsDomain V] (G : Over (Spec (CommRingCat.of V))) [Flat G.hom]
    {L : LB G.left} (hL : L.IsLB) (k : ℕ) (σ σ' : H0 L k)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)))) (r : V)
    (h : GeneratorPullback.SecScal L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left)
      (fun _ => (k : ℤ)) σ (pullback.fst G.hom (jK V)) 1)
    (h' : GeneratorPullback.SecScal L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left)
      (fun _ => (k : ℤ)) σ' (pullback.fst G.hom (jK V)) (scal (pullback.snd G.hom (jK V) ≫ jK V) r)) :
    SecIsMul G.hom r σ' σ := by
  obtain ⟨ρ, hρ⟩ := exists_secIsMul (p := G.hom) r σ
  refine fun j => Eq.trans (generic_app_injective G _ (fn_ext fun y hy => ?_)) (hρ j)
  obtain ⟨J, hJ, e⟩ := exists_good L hL y (fun _ : Unit => (𝟙 _ ≫ pullback.fst G.hom (jK V)) ≫ 𝟙 G.left)
    (fun _ => j 0) (fun _ _ _ => rfl) (fun _ => Set.mem_iInter.1 hy 0)
  have ej : ∀ a : Fin 1, J ((𝟙 _ ≫ pullback.fst G.hom (jK V)) ≫ 𝟙 G.left) = j a := fun a => by
    rw [Subsingleton.elim a 0]; exact e ()
  have e₁ := SectionScalarValuation.secScal_sval h (𝟙 _) y hJ
  have e₂ := secScal_sval h' (𝟙 _) y hJ
  rw [← e₁, sval_of σ _ y J j ej, sval_of σ' _ y J j ej, gs_scal, ← pullback.condition, ← Category.assoc] at e₂
  refine (gs_pull (𝟙 _) _ y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 _) _ y _ hy _).symm)
  exact e₂.trans (secIsMul_gs hρ _ y j hy).symm

theorem isUnit_cst {V : Type} [CommRing V] [IsDomain V] {Z : Scheme.{0}}
    (q : Z ⟶ Spec (CommRingCat.of (FractionRing V))) (z : Z) {r : V} (hr : r ≠ 0) : IsUnit (cst (q ≫ jK V) z r) := by
  have h : algebraMap V (FractionRing V) r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V _)).2 hr
  have e : cst (q ≫ jK V) z r = cst q z (algebraMap V (FractionRing V) r) := cst_comp _ _ _ _
  rw [e]
  exact IsUnit.of_mul_eq_one (cst q z (algebraMap V (FractionRing V) r)⁻¹)
    (by rw [← cst_mul, mul_inv_cancel₀ h, cst_one])

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (k : ℕ) (σ : H0 U.LG.L k) (s : U.SecK k), GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => ((k : ℕ) : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((k : ℕ) : ℤ)) σ (pullback.fst G.hom (jK V)) 1 → ∀ E : Fam D.toPre (FractionRing V) k, U.Expands k s E → ∃ g : ∀ α : D.toPre.X, D.toPre.SecB k α, (∀ e, U.ExpandsAt e k σ g) ∧ ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) (E.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre (FractionRing V)).left 1 := by
  intro V _ _ _ ϖ hϖ D A G _ _ U k σ s hs E hE
  obtain ⟨r, hr, σ₁, f₁, h₁, hf₁, hE₁⟩ := hE
  have := U.smooth
  have : Flat G.hom := inferInstance
  have hσ₁ : SecIsMul G.hom r σ₁ σ := secIsMul_of_generic G U.LG.isLB k σ σ₁ s r hs h₁
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  obtain ⟨σ₂, hσ₂⟩ := exists_secIsMul (p := G.hom) (u⁻¹ : Vˣ).val σ₁
  choose f₂ hf₂ using fun α => exists_secIsMul (p := D.toPre.P.A.hom) (u⁻¹ : Vˣ).val (f₁ α)
  have hE₂ : ∀ e, U.ExpandsAt e k σ₂ f₂ := fun e =>
    expandsAt_secIsMul V _ D A G U e k _ σ₁ σ₂ f₁ f₂ hσ₂ hf₂ (hE₁ e)
  have hσ : SecIsMul G.hom (ϖ ^ n) σ₂ σ := by
    have := secIsMul_trans hσ₂ hσ₁
    rwa [Units.inv_mul_cancel_left] at this
  have hg : ∀ α, ∃ g : D.toPre.SecB k α, SecIsMul D.toPre.P.A.hom (ϖ ^ n) (f₂ α) g := fun α => by
    cases n with
    | zero => exact ⟨f₂ α, by rw [pow_zero]; exact secIsMul_one _⟩
    | succ m =>
      exact (GlobalTheory.ExtDiv.main V ϖ hϖ D A G U m k α (f₂ α)).1 (WeightPf.weightIndep V _ D A G U m k σ₂ f₂
        ((GlobalTheory.ThickDiv.main V ϖ hϖ G _ σ₂ m).2 ⟨σ, hσ⟩) (hE₂ m) α)
  choose g hg using hg
  refine ⟨g, fun e => expandsAt_cancel_pow V ϖ hϖ D A G U e n k σ σ₂ g f₂ hσ hg (hE₂ _), fun α => ?_⟩
  refine SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ => ?_
  have e₁ := secScal_sval (hf₁ α) (𝟙 _) y hJ
  have e₂ : sval (f₁ α) (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y J = _ *
      sval (g α) (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y J :=
    secIsMul_gs (secIsMul_trans (secIsMul_symm (hf₂ α)) (hg α)) _ y _ (hJ.mem _ _)
  rw [Category.assoc, Over.w] at e₂
  rw [e₂, gs_scal] at e₁
  refine (IsUnit.mul_right_inj ?_).1 e₁
  have e₃ : 𝟙 _ ≫ (DegPre.BF D.toPre (FractionRing V)).hom =
      ((fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left ≫ jFK (R := V) (FractionRing V)) ≫ jK V := by
    rw [Category.id_comp, Category.assoc]
    exact (Over.w (fst (TF (R := V) (FractionRing V)) D.toPre.P.A)).symm
  rw [e₃]
  exact isUnit_cst _ y hr

end GlobalTheory.ExpInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MemSpanCstOfCstMulEqZero
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_mem_pow_of_mul_mem_pow {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R) {r : R}
    (hr : r ≠ 0) : ∃ c : ℕ, ∀ (n : ℕ) (x : R), r * x ∈ I ^ (n + c) → x ∈ I ^ n := by
  first
  | exact @_root_.GlobalTheory.ShiftMemPowOfMulMemPow.exists_shift_mem_pow_of_mul_mem_pow
  | exact _root_.GlobalTheory.ShiftMemPowOfMulMemPow.exists_shift_mem_pow_of_mul_mem_pow
  | (apply _root_.GlobalTheory.ShiftMemPowOfMulMemPow.exists_shift_mem_pow_of_mul_mem_pow <;> assumption)
  | (intros; apply _root_.GlobalTheory.ShiftMemPowOfMulMemPow.exists_shift_mem_pow_of_mul_mem_pow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ShiftMemPowOfMulMemPow.exists_shift_mem_pow_of_mul_mem_pow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ShiftMemPowOfMulMemPow.exists_shift_mem_pow_of_mul_mem_pow ..)

theorem mem_span_cst_of_cst_mul_eq_zero {S : Type} [CommRing S] {X : Scheme.{0}} (p : X ⟶ Sp S) [Flat p] (x : X)
    {a : S} {t : X.presheaf.stalk x} (ht : cst p x a * t = 0) :
    t ∈ Ideal.span (cst p x '' {c | a * c = 0}) := by
  let φ : S →+* X.presheaf.stalk x := (p.stalkMap x).hom.comp
    (((Sp S).presheaf.germ ⊤ (p x) trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom)
  have hφ : ∀ c, φ c = cst p x c := fun c => by
    rw [cst, gs_stalkMap p x ⊤ trivial, gs_eq _ _ ⊤ trivial]; rfl
  have fl : φ.Flat := by
    refine RingHom.Flat.comp (RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv)) ?_) (Flat.stalkMap p x)
    have hU := isAffineOpen_top (Sp S)
    let _ := (Sp S).presheaf.algebra_section_stalk (U := ⊤) ⟨p x, trivial⟩
    have := hU.isLocalization_stalk ⟨p x, trivial⟩
    exact IsLocalization.flat ((Sp S).presheaf.stalk ((⟨p x, trivial⟩ : (⊤ : (Sp S).Opens)) : Sp S)) (hU.primeIdealOf ⟨p x, trivial⟩).asIdeal.primeCompl
  let _ := φ.toAlgebra
  have : Module.Flat S (X.presheaf.stalk x) := fl
  obtain ⟨l, c, y, hy, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := S)
    (f := fun _ : Unit => a) (x := fun _ => t) (by
      rw [Fintype.sum_unique]; exact (congrArg (· * t) (hφ a)).trans ht)
  rw [show t = _ from hy ()]
  refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right (y j) _ (Ideal.subset_span ⟨c () j, ?_, (hφ _).symm⟩)
  simpa using hc j

theorem stalkMap_mem_span_cst {S : Type} [CommRing S] {X Y : Scheme.{0}} (p : X ⟶ Sp S) (g : Y ⟶ X) (y : Y)
    {T : Set S} {t : X.presheaf.stalk (g y)} (ht : t ∈ Ideal.span (cst p (g y) '' T)) :
    (g.stalkMap y).hom t ∈ Ideal.span (cst (g ≫ p) y '' T) := by
  have h := Ideal.mem_map_of_mem (g.stalkMap y).hom ht
  rw [Ideal.map_span, Set.image_image] at h
  simpa only [cst_stalkMap] using h

section

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

def ExpandsAtMod (e k : ℕ) (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (S : Finset D.toPre.X)
    (T : Set R) : Prop :=
  ∀ (y : (thickObj R I e G).left) (J), Good D.toPre.P.L y J →
    (∀ α ∉ S, sval (f α) (pGl U e) y J ∈ Ideal.span (cst (fGl I G e ≫ G.hom) y '' T)) ∧
    ∀ jL, (fGl I G e) y ∈ U.LG.L.U jL →
      ((wv U e (𝟙 _) y (J (pGl U e)) jL ^ k).val * sv U k σ (fGl I G e) y jL -
        ∑ α ∈ S, sval (f α) (pGl U e) y J * (val (tG U e α) (𝟙 _) y J).val) ∈
        Ideal.span (cst (fGl I G e ≫ G.hom) y '' T)

theorem expandsAtMod_of_succ
    (e k : ℕ) (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (S : Finset D.toPre.X) (T : Set R)
    (h : ExpandsAtMod U (e + 1) k σ f S T) : ExpandsAtMod U e k σ f S T := by
  intro y J hJ
  have hq : thickMap R I e G ≫ pGl U (e + 1) = pGl U e := U.gt_q e
  have hf := thickMap_comp_fGl I e G
  have hJ₀ : Good D.toPre.P.L (thickMap R I e G y) (fun ψ => J (thickMap R I e G ≫ ψ)) :=
    fun ψ => hJ (thickMap R I e G ≫ ψ)
  obtain ⟨h₀, h₁⟩ := h _ _ hJ₀
  have hF : ∀ α, ((thickMap R I e G).stalkMap y).hom (sval (f α) (pGl U (e + 1)) _
      (fun ψ => J (thickMap R I e G ≫ ψ))) = sval (f α) (pGl U e) y J := fun α => by
    refine (stalkMap_gs _ _ y _ (hJ₀.mem _ _) _).trans ?_
    rw [← hq]
    exact (sval_of (f α) _ y J _ (fun a => by rw [Category.assoc])).symm
  have hT : ∀ α, ((thickMap R I e G).stalkMap y).hom (val (tG U (e + 1) α) (𝟙 _) _
      (fun ψ => J (thickMap R I e G ≫ ψ))).val = (val (tG U e α) (𝟙 _) y J).val := fun α => by
    have ht : val (tG U (e + 1) α) (thickMap R I e G) y J = val (tG U e α) (𝟙 _) y J := by
      have h₂ := val_pull hJ (tG U (e + 1) α) (thickMap R I e G) (𝟙 _)
      rw [Category.id_comp] at h₂
      exact h₂.symm.trans (val_corr hJ (U.gt_t e α) (𝟙 _))
    rw [← ht]
    refine (stalkMap_gm _ y _ (hJ₀.mem _ (𝟙 _)) _).trans (congrArg Units.val ?_)
    exact (val_of _ _ y J _ (fun a => by rw [Category.id_comp])).symm
  refine ⟨fun α hα => ?_, fun jL hL => ?_⟩
  · have H' := stalkMap_mem_span_cst _ (thickMap R I e G) y (h₀ α hα)
    rwa [hF, ← Category.assoc, hf] at H'
  · have hL' : fGl I G (e + 1) (thickMap R I e G y) ∈ U.LG.L.U jL :=
      (congrArg (fun g => g y ∈ U.LG.L.U jL) hf).mpr hL
    have H' := stalkMap_mem_span_cst _ (thickMap R I e G) y (h₁ jL hL')
    have hW : ((thickMap R I e G).stalkMap y).hom (wv U (e + 1) (𝟙 _) _
        (J (thickMap R I e G ≫ pGl U (e + 1))) jL).val = (wv U e (𝟙 _) y (J (pGl U e)) jL).val := by
      rw [← wv_thickMap U e y _ jL (hJ _) hL, ← hq]
      refine stalkMap_gm (thickMap R I e G) y _ ?_ _
      exact ⟨mem_pull.2 (hJ₀ (pGl U (e + 1))), mem_pull.2 hL'⟩
    have hS : ((thickMap R I e G).stalkMap y).hom (sv U k σ (fGl I G (e + 1)) _ jL) =
        sv U k σ (fGl I G e) y jL := by
      rw [← hf]
      exact stalkMap_gs _ _ y _ (Set.mem_iInter.2 fun _ => hL') _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_mul, Units.val_pow_eq_pow_val, map_pow, hW, hS, map_sum, ← Category.assoc, hf] at H'
    simp only [map_mul, hF, hT] at H'
    rw [Units.val_pow_eq_pow_val]
    exact H'

end

theorem expandsAt_cancel_of_ne_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) (r : R), r ≠ 0 → ∀ (σ σ' : H0 U.LG.L k) (f f' : ∀ α : D.toPre.X, D.toPre.SecB k α), SecIsMul G.hom r σ' σ → (∀ α, SecIsMul D.toPre.P.A.hom r (f' α) (f α)) → (∀ e, U.ExpandsAt e k σ' f') → ∀ e, U.ExpandsAt e k σ f := by
  intro R _ _ _ I D A G _ _ U k r hr σ σ' f f' hσ hf hE e
  obtain ⟨n, hn⟩ := exists_mem_pow_of_mul_mem_pow I hr
  have := U.smooth
  have : Flat G.hom := inferInstance
  have hs : ∀ d : ℕ, fGl I G d ≫ G.hom = (thickObj R I d G).hom ≫
      spMap (Ideal.Quotient.mk (I ^ (d + 1))) := fun d => pullback.condition
  obtain ⟨S, hS⟩ := expandsAt_val U (e + n) k σ' f' (hE _)
  have key : ∀ (y : (thickObj R I (e + n) G).left) (t : (thickObj R I (e + n) G).left.presheaf.stalk y),
      cst (fGl I G (e + n) ≫ G.hom) y r * t = 0 →
      t ∈ Ideal.span (cst (fGl I G (e + n) ≫ G.hom) y '' (I ^ (e + 1) : Ideal R)) := fun y t ht => by
    have : Flat (thickObj R I (e + n) G).hom :=
      inferInstanceAs (Flat (pullback.snd G.hom (thick R I (e + n))))
    rw [hs, cst_comp] at ht
    refine Ideal.span_mono ?_ (mem_span_cst_of_cst_mul_eq_zero (thickObj R I (e + n) G).hom y ht)
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨c, hn _ _ ?_, by rw [hs, cst_comp]⟩
    rw [Set.mem_setOf_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hc
    rwa [Nat.add_right_comm]
  have h₁ : ExpandsAtMod U (e + n) k σ f S (I ^ (e + 1) : Ideal R) := by
    intro y J hJ
    have hc : pGl U (e + n) ≫ D.toPre.P.A.hom = fGl I G (e + n) ≫ G.hom :=
      (Over.w (U.gt (e + n)).pG).trans (Over.w (fstG I (e + n) G)).symm
    have H := hS _ (𝟙 _) y J hJ
    simp only [Category.id_comp] at H
    have hF : ∀ α, sval (f' α) (pGl U (e + n)) y J =
        cst (fGl I G (e + n) ≫ G.hom) y r * sval (f α) (pGl U (e + n)) y J := fun α => by
      rw [← hc]
      exact secIsMul_gs (hf α) (pGl U (e + n)) y _ (hJ.mem _ _)
    refine ⟨fun α hα => key _ _ ((hF α).symm.trans (H.1 α hα)), fun jL hL => key _ _ ?_⟩
    have hs : sv U k σ' (fGl I G (e + n)) y jL =
        cst (fGl I G (e + n) ≫ G.hom) y r * sv U k σ (fGl I G (e + n)) y jL :=
      secIsMul_gs hσ (fGl I G (e + n)) y (fun _ => jL) (Set.mem_iInter.2 fun _ => hL)
    have H₂ := H.2 jL hL
    rw [hs, mul_left_comm] at H₂
    rw [mul_sub, H₂, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun α _ => by rw [hF, _root_.mul_assoc]
  have h₂ : ∀ m : ℕ, ExpandsAtMod U (e + m) k σ f S (I ^ (e + 1) : Ideal R) →
      ExpandsAtMod U e k σ f S (I ^ (e + 1) : Ideal R) := fun m => by
    induction m with
    | zero => exact id
    | succ m ih => exact fun h => ih (expandsAtMod_of_succ U (e + m) k σ f S _ h)
  refine expandsAt_of_val U e k σ f S fun y J hJ => ?_
  have hz : Ideal.span (cst (fGl I G e ≫ G.hom) y '' (I ^ (e + 1) : Ideal R)) = ⊥ := by
    refine Ideal.span_eq_bot.2 ?_
    rintro _ ⟨c, hc, rfl⟩
    rw [hs, cst_comp, Ideal.Quotient.eq_zero_iff_mem.2 hc, cst, map_zero]
    exact gs_zero _ _ _ trivial
  obtain ⟨a, b⟩ := h₂ n h₁ y J hJ
  simp only [hz, Ideal.mem_bot, sub_eq_zero] at a b
  exact ⟨a, b⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PowDegDiagonalAction
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem powDeg_diagonal_action : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X], (∀ (a : O) (x : D'.X), pD.xe (a • x) = a • pD.xe x) → ∀ oa : D.OAct O, ∃ oa' : D'.OAct O, ∀ a i, oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a :=
  GlobalTheory.TauBalBox.exists_pow_oAct

end GlobalTheory
end

