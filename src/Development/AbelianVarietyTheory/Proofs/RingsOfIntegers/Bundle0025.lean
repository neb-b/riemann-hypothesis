module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0095
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.VanishOfTermsVanish
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CrossEq
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ExpFun

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.ExpInt

theorem cross_eq {V : Type} [CommRing V] [IsDomain V] (G : Over (Spec (CommRingCat.of V))) [Flat G.hom]
    {L : LB G.left} (hL : L.IsLB) (k : ℕ) (σ σ' ρ ρ' : H0 L k)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)))) (r r' : V)
    (h : GeneratorPullback.SecScal L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left)
      (fun _ => (k : ℤ)) σ (pullback.fst G.hom (jK V)) (scal (pullback.snd G.hom (jK V) ≫ jK V) r))
    (h' : GeneratorPullback.SecScal L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left)
      (fun _ => (k : ℤ)) σ' (pullback.fst G.hom (jK V)) (scal (pullback.snd G.hom (jK V) ≫ jK V) r'))
    (hρ : SecIsMul G.hom r' ρ σ) (hρ' : SecIsMul G.hom r ρ' σ') : ρ = ρ' := by
  refine SecOps.sec_ext fun j => generic_app_injective G _ (fn_ext fun y hy => ?_)
  obtain ⟨J, hJ, e⟩ := exists_good L hL y (fun _ : Unit => (𝟙 _ ≫ pullback.fst G.hom (jK V)) ≫ 𝟙 G.left)
    (fun _ => j 0) (fun _ _ _ => rfl) (fun _ => Set.mem_iInter.1 hy 0)
  have ej : ∀ a : Fin 1, J ((𝟙 _ ≫ pullback.fst G.hom (jK V)) ≫ 𝟙 G.left) = j a := fun a => by
    rw [Subsingleton.elim a 0]; exact e ()
  have e₁ := secScal_sval h (𝟙 _) y hJ
  have e₂ := secScal_sval h' (𝟙 _) y hJ
  rw [sval_of σ _ y J j ej, gs_scal, ← pullback.condition, ← Category.assoc] at e₁
  rw [sval_of σ' _ y J j ej, gs_scal, ← pullback.condition, ← Category.assoc] at e₂
  refine (gs_pull (𝟙 _) _ y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 _) _ y _ hy _).symm)
  refine (secIsMul_gs hρ _ y j hy).trans (Eq.trans ?_ (secIsMul_gs hρ' _ y j hy).symm)
  exact (congrArg _ e₁).trans ((mul_left_comm _ _ _).trans (congrArg _ e₂).symm)

theorem main : lemmaBSt.{0} → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (k : ℕ) (s : U.SecK k) (E E' : Fam D.toPre (FractionRing V) k), U.Expands k s E → U.Expands k s E' → E = E' := by
  intro hB V _ _ _ D A G _ _ U k s E E' hE hE'
  obtain ⟨r, hr, σ, f, h, hf, hx⟩ := hE
  obtain ⟨r', hr', σ', f', h', hf', hx'⟩ := hE'
  have := U.smooth
  have : Flat G.hom := inferInstance
  obtain ⟨ρ, hρ⟩ := exists_secIsMul (p := G.hom) r' σ
  obtain ⟨ρ', hρ'⟩ := exists_secIsMul (p := G.hom) r σ'
  choose g hg using fun α => exists_secIsMul (p := D.toPre.P.A.hom) r' (f α)
  choose g' hg' using fun α => exists_secIsMul (p := D.toPre.P.A.hom) r (f' α)
  obtain rfl : ρ = ρ' := cross_eq G U.LG.isLB k σ σ' ρ ρ' s r r' h h' hρ hρ'
  obtain rfl : g = g' := GlobalTheory.ExpUniq.main hB V D A G U k ρ g g'
    (fun e => expandsAt_secIsMul V _ D A G U e k _ σ ρ f g hρ hg (hx e))
    (fun e => expandsAt_secIsMul V _ D A G U e k _ σ' ρ f' g' hρ' hg' (hx' e))
  refine fam_ext fun α j => sec_ext_val D.toPre.P.isLB (fun y J hJ => ?_) j
  have e₁ := secScal_sval (hf α) (𝟙 _) y hJ
  have e₁' := secScal_sval (hf' α) (𝟙 _) y hJ
  have e₂ : sval (g α) (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y J = _ *
      sval (f α) (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y J :=
    secIsMul_gs (hg α) _ y _ (hJ.mem _ _)
  have e₂' : sval (g α) (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y J = _ *
      sval (f' α) (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y J :=
    secIsMul_gs (hg' α) _ y _ (hJ.mem _ _)
  rw [Category.assoc, Over.w] at e₂ e₂'
  rw [gs_scal] at e₁ e₁'
  rw [e₁] at e₂
  rw [e₁', e₂, mul_left_comm] at e₂'
  have e₃ : 𝟙 _ ≫ (DegPre.BF D.toPre (FractionRing V)).hom =
      ((fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left ≫ jFK (R := V) (FractionRing V)) ≫ jK V := by
    rw [Category.id_comp, Category.assoc]
    exact (Over.w (fst (TF (R := V) (FractionRing V)) D.toPre.P.A)).symm
  rw [e₃] at e₂'
  exact (IsUnit.mul_right_inj (isUnit_cst _ y hr')).1 ((IsUnit.mul_right_inj (isUnit_cst _ y hr)).1 e₂')

end GlobalTheory.ExpFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntOfVgeZero
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.IntegralSection

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.IntegralExpansion

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

theorem exists_eq_of_nonneg (hϖ : Irreducible ϖ) {v : AddValuation (FractionRing V) (WithTop ℚ)}
    (hv : ValOver ϖ (FractionRing V) v) {c : FractionRing V} (h : 0 ≤ v c) :
    ∃ b : V, c = algebraMap V (FractionRing V) b := by
  rcases eq_or_ne c 0 with rfl | hc
  · exact ⟨0, (map_zero _).symm⟩
  obtain ⟨n, u, hu⟩ := hasVal_of_ne_zero hϖ hc

  have hvc : v c = ((n : ℚ) : WithTop ℚ) := hv c n ⟨u, hu⟩
  have hn : (0 : ℤ) ≤ n := by
    rw [hvc] at h
    have h' : (0 : ℚ) ≤ (n : ℚ) := WithTop.coe_le_coe.mp h
    exact_mod_cast h'

  lift n to ℕ using hn
  refine ⟨ϖ ^ n * (u : V), ?_⟩
  rw [hu, map_mul, map_pow, zpow_natCast]

theorem exists_int_of_vge_zero (hϖ : Irreducible ϖ) {D : DegData V (maximalIdeal V)}
    {v : AddValuation (FractionRing V) (WithTop ℚ)} (hv : ValOver ϖ (FractionRing V) v) {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k))}
    (hs : VGe D (FractionRing V) v k α s 0) :
    ∃ f : D.toPre.SecB k α,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) s
        (D.toPre.famφB α) (DegPre.famε k) f (DegPre.prB D.toPre (FractionRing V)).left 1 := by
  obtain ⟨n, a, σ, σF, hσ, ha, hsum⟩ := hs

  have hint : ∀ i, ∃ b : V, a i = algebraMap V (FractionRing V) b := fun i =>
    exists_eq_of_nonneg hϖ hv (by simpa using ha i)
  choose b hb using hint

  refine ⟨FamInt.secLin (fun i => constFn D.toPre.P.A.hom ⊤ (b i)) σ, ?_⟩
  refine SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ => ?_
  rw [SectionScalarValuation.sval_lin _ σ (fun j => rfl) _ y hJ,
    SectionScalarValuation.sval_lin (fun i => gF D.toPre (FractionRing V) (a i)) σF
      (fun j => (hsum j).trans (by simp only [constBF_eq]; rfl)) _ y hJ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [SectionScalarValuation.secScal_sval (hσ i) (𝟙 _) y hJ]
  congr 1
  clear hsum hσ ha hJ
  rw [gs_constFn]
  · rw [hb i]

    have e1 := gs_pull (𝟙 _) (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left y ⊤ trivial
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom (algebraMap V (FractionRing V) (b i)))
    rw [Category.id_comp] at e1
    have e1' : gs (𝟙 _) y ⊤ (gF D.toPre (FractionRing V) (algebraMap V (FractionRing V) (b i))) =
        cst (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left y (algebraMap V (FractionRing V) (b i)) := e1
    rw [e1', ← cst_comp, Category.id_comp]
    congr 1

    have h1 := Over.w (DegPre.prB D.toPre (FractionRing V))
    have h2 := Over.w (fst (TF (R := V) (FractionRing V)) D.toPre.P.A)
    rw [h1]
    rw [← h2]
    congr 1

    unfold TF spMap
    change jFK _ ≫ jK V = _
    unfold jFK jK
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · trivial

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK → ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (k : ℕ) (s : U.SecK k) (E : Fam D.toPre (FractionRing V) k), U.Expands k s E → (∀ α, VGe D (FractionRing V) vK k α (E.s α) 0) → ∃ σ : H0 U.LG.L k, GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => ((k : ℕ) : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((k : ℕ) : ℤ)) σ (pullback.fst G.hom (jK V)) 1 := by
  intro V _ _ _ ϖ hϖ D vK hvK A G _ _ U k s E hE hvE
  obtain ⟨r, hr, σ, f, hσ, hf, hexp⟩ := hE
  have hg : ∀ α, ∃ g : D.toPre.SecB k α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α)
      (DegPre.famε k) (E.s α) (D.toPre.famφB α) (DegPre.famε k) g (DegPre.prB D.toPre (FractionRing V)).left 1 :=
    fun α => exists_int_of_vge_zero hϖ hvK (hvE α)
  choose g hg using hg
  have hfg : ∀ α, SecIsMul D.toPre.P.A.hom r (f α) (g α) := fun α =>
    secIsMul_of_secScal D.toPre.P.isLB D.toPre.P.A.hom (prB_app_injective D.toPre) (hg α)
      (by rw [Over.w (DegPre.prB D.toPre (FractionRing V))]; exact hf α)
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ

  have hmul : ∀ α, ∃ g' : D.toPre.SecB k α, SecIsMul D.toPre.P.A.hom (ϖ ^ m) (f α) g' := by
    intro α
    obtain ⟨g', hg'⟩ := exists_secIsMul D.toPre.P.A.hom (u : V) (g α)
    obtain ⟨F', hF'⟩ := exists_secIsMul D.toPre.P.A.hom (ϖ ^ m) g'
    have hc := SecIsMul.comp hF' hg'
    have hF'f : F' = f α := SecOps.sec_ext fun j => by
      rw [hc j, hfg α j, hu, mul_comm (u : V)]
    exact ⟨g', hF'f ▸ hF'⟩
  choose g' hg' using hmul

  have hdiv : ∃ τ : H0 U.LG.L k, SecIsMul G.hom (ϖ ^ m) σ τ := by
    rcases m with _ | e
    · refine ⟨σ, fun j => ?_⟩
      simp [scal]
    · exact exists_div_of_expandsAt hϖ U e k σ g' f hg' (hexp e)
  obtain ⟨τ, hτ⟩ := hdiv

  obtain ⟨σ', hσ'⟩ := exists_secIsMul G.hom ((u⁻¹ : Vˣ) : V) τ
  refine ⟨σ', SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => ?_⟩
  have hlin : ∀ {a : V} {t t' : H0 U.LG.L k}, SecIsMul G.hom a t' t →
      sval t' (𝟙 _ ≫ pullback.fst G.hom (jK V)) y J =
        gs (𝟙 _ ≫ pullback.fst G.hom (jK V)) y ⊤ (scal G.hom a) * sval t (𝟙 _ ≫ pullback.fst G.hom (jK V)) y J := by
    intro a t t' ht
    have hl := SectionScalarValuation.sval_lin (fun _ : Fin 1 => scal G.hom a) (fun _ => t)
      (fun j => by rw [Fin.sum_univ_one]; exact ht j) (𝟙 _ ≫ pullback.fst G.hom (jK V)) y hJ
    rwa [Fin.sum_univ_one] at hl
  have hgs : ∀ {X : Scheme.{0}} (r' : _ ⟶ X) (p : X ⟶ Spec (CommRingCat.of V)) (a : V),
      gs r' y ⊤ (scal p a) = cst (r' ≫ p) y a := fun r' p a => gs_pull r' p y ⊤ trivial _
  have hq : (𝟙 _ ≫ pullback.fst G.hom (jK V)) ≫ G.hom = 𝟙 _ ≫ pullback.snd G.hom (jK V) ≫ jK V := by
    rw [Category.assoc, pullback.condition]
  have key := GlobalTheory.IntegralExpansion.sval_of_secScal hσ (𝟙 _) y hJ
  rw [hlin hτ, hgs, hgs, hq, hu, cst_mul] at key
  rw [hlin hσ', hgs, hq]

  have hunit : IsUnit (cst (𝟙 _ ≫ pullback.snd G.hom (jK V) ≫ jK V) y (ϖ ^ m)) := by
    have hK : algebraMap V (FractionRing V) (ϖ ^ m) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr (pow_ne_zero _ hϖ.ne_zero)
    rw [← Category.assoc]
    change IsUnit (cst (_ ≫ spMap (algebraMap V (FractionRing V))) y _)
    rw [cst_comp]
    have h1 := (cst_mul (𝟙 _ ≫ pullback.snd G.hom (jK V)) y (algebraMap V (FractionRing V) (ϖ ^ m))
      (algebraMap V (FractionRing V) (ϖ ^ m))⁻¹).symm.trans (by rw [mul_inv_cancel₀ hK, cst_one])
    exact ⟨⟨_, _, h1, (mul_comm _ _).trans h1⟩, rfl⟩
  have hT : sval τ (𝟙 _ ≫ pullback.fst G.hom (jK V)) y J =
      cst (𝟙 _ ≫ pullback.snd G.hom (jK V) ≫ jK V) y (u : V) * sval s (𝟙 _) y J :=
    hunit.mul_left_cancel (by rw [key]; ring)
  rw [hT, ← _root_.mul_assoc, ← cst_mul, Units.inv_mul, cst_one, _root_.one_mul]

end GlobalTheory.IntegralSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsSectionsOfNonzeroSpecial
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NonzeroClosedFibre

theorem exists_restrict {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (h : Y ⟶ X) (k : ℤ)
    (σ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => k))) :
    ∃ s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => h) (fun _ => k)),
      GeneratorPullback.SecScal L (fun _ : Fin 1 => h) (fun _ => k) s (fun _ : Fin 1 => 𝟙 X) (fun _ => k) σ h 1 := by
  have key : ∀ φ' : Fin 1 → (Y ⟶ X), (fun _ : Fin 1 => h ≫ 𝟙 X) = φ' →
      ∃ s : LB.Sec (LB.LinComb L φ' (fun _ => k)),
        GeneratorPullback.SecScal L φ' (fun _ => k) s (fun _ : Fin 1 => 𝟙 X) (fun _ => k) σ h 1 := by
    rintro _ rfl
    refine ⟨DVR.pullSec L (fun _ : Fin 1 => 𝟙 X) (fun _ => k) σ h,
      SectionScalarValuation.secScal_of_sval hL fun y J hJ => ?_⟩
    exact (SectionScalarValuation.sval_pullSec _ _ σ h _ y hJ).symm
  exact key _ (funext fun _ => Category.comp_id h)

theorem secIsMul_of_vge {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
    (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v) {k : ℕ} {χ : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k))} {g : D.toPre.SecB k χ}
    (hg : GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k) s (D.toPre.famφB χ)
      (DegPre.famε k) g (DegPre.prB D.toPre F).left 1) {r : ℚ} (hr : 0 < r) (hs : VGe D F v k χ s r) :
    ∃ g' : D.toPre.SecB k χ, SecIsMul D.toPre.P.A.hom ϖ g g' := by
  obtain ⟨n, a₀, τ, τF, hτ, hva, hsum⟩ := hs
  have hb : ∀ i, 0 < v (a₀ i) := fun i => lt_of_lt_of_le (by exact_mod_cast hr) (hva i)
  have vc : ∀ (t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k))) (x : F)
      {Z : Scheme.{0}} (q : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (j), q z ∈ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j →
      gs q z (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (DegPre.constBF D.toPre F x _ * t.f j) =
        cst (q ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z x *
          gs q z (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (t.f j) := fun t x Z q z j hz =>
    (gs_mul q z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res q z le_top hz _).trans
      (gs_pull q (fst (TF (R := V) F) D.toPre.P.A).left z ⊤ trivial _)) rfl)
  have div₁ := H1.dvd_of_comb hϖ D.toPre F v hv g τ a₀ hb (fun Z q z J hJ =>
    (H1.sval_scal hg q z hJ).symm.trans
      ((congrArg (gs _ z _) (hsum _)).trans ((H1.gs_sum q z _ (hJ.mem _ q) _).trans (Finset.sum_congr rfl fun i _ =>
        (vc (τF i) (a₀ i) q z _ (hJ.mem _ q)).trans (congrArg₂ (· * ·) rfl (H1.sval_scal (hτ i) q z hJ))))))
  have := D.toPre.P.isAb.smooth
  exact exists_div_sec D.toPre.P.A.hom hϖ.ne_zero g div₁

theorem main : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (ϑ : H0 U.LG.L 1), NonzeroOnSpecial U ϑ → ∃ g : ∀ α : D.toPre.X, D.toPre.SecB 1 α, (∀ e, U.ExpandsAt e 1 ϑ g) ∧ (¬ ∃ σ' : D.toPre.SecB 1 0, ∀ j, (g 0).f j = Geo.Tor.constFn D.toPre.P.A.hom _ ϖ * σ'.f j) ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∃ θ : Fam D.toPre F 1, (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε 1) (θ.s α) (D.toPre.famφB α) (DegPre.famε 1) (g α) (DegPre.prB D.toPre F).left 1) ∧ NuGe D Q F v 1 θ 0 ∧ ¬ ∃ r : ℚ, 0 < r ∧ NuGe D Q F v 1 θ r := by
  intro hG V _ _ _ ϖ hϖ D Q hQ A G _ _ U ϑ hϑ
  obtain ⟨s, hs⟩ := exists_restrict U.LG.isLB (pullback.fst G.hom (jK V)) ((1 : ℕ) : ℤ) ϑ
  obtain ⟨E, hE, -⟩ := (U.expand 1 le_rfl).1 s
  obtain ⟨g, hexp, hgE⟩ := _root_.GlobalTheory.ExpInt.main V ϖ hϖ D A G U.toUnifPre 1 ϑ s hs E hE
  have hdiv := (GlobalTheory.integralFamily_levelOne V ϖ hϖ D Q hQ (FractionRing V) (GlobalTheory.FamInt.ordVal hϖ)
    (GlobalTheory.FamInt.valOver_ordVal hϖ) E g hgE).2
  have hind : ¬ ∃ g' : D.toPre.SecB 1 0, SecIsMul D.toPre.P.A.hom ϖ (g 0) g' :=
    (GlobalTheory.ClosedFibreTerm.main V ϖ hϖ D A G U.toUnifPre ϑ g (hexp 0) hdiv).1 hϑ
  refine ⟨g, hexp, hind, fun F _ _ v hv => ?_⟩
  obtain ⟨θ, hθ⟩ := _root_.GlobalTheory.FamBaseChange.main hG V (maximalIdeal V) D 1 E g hgE F
  refine ⟨θ, hθ, (GlobalTheory.integralFamily_levelOne V ϖ hϖ D Q hQ F v hv θ g hθ).1, ?_⟩
  rintro ⟨r, hr, hν⟩
  refine hind (secIsMul_of_vge hϖ D F v hv (hθ 0) ?_ (hν 0))
  rw [QForm.Q_zero hϖ D hQ]
  simpa using hr

end GlobalTheory.NonzeroClosedFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionIntegralSectionIntegralNoetherianLocal
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.IntegralExpansionLocal

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.IntegralExpansion

theorem dvd_gs_of_dvd_sval {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {c : Z.presheaf.stalk z}
    (h : ∀ J, Good L z J → c ∣ sval s r z J) (j : K → L.ι) (hj : r z ∈ LB.wchart L φ j) :
    c ∣ gs r z (LB.wchart L φ j) (s.f j) := by
  obtain ⟨J, hJ, -⟩ := exists_good L hL z (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim) (fun a => a.elim)
  rw [sec_trans s r z hj (hJ.mem φ r)]
  exact dvd_mul_of_dvd_right (h J hJ) _

theorem isUnit_cst_of_ne_zero {R : Type} [CommRing R] [IsDomain R] {Z : Scheme.{0}}
    (p : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z) {r : R} (hr : r ≠ 0) :
    IsUnit (cst (p ≫ jK R) z r) := by
  have hne : algebraMap R (FractionRing R) r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr
  have key : cst (p ≫ jK R) z r = cst p z (algebraMap R (FractionRing R) r) :=
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst_comp p (algebraMap R (FractionRing R)) z r
  rw [key]
  refine isUnit_iff_exists_inv.2 ⟨cst p z (algebraMap R (FractionRing R) r)⁻¹, ?_⟩
  rw [← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, mul_inv_cancel₀ hne, ReciprocityTheory.ChartRestriction.G.H1.cst_one]

private theorem injective_app_pullback_fst_of_flat {R : Type} [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))) [Flat G.hom]
    (W : G.left.Opens) : Function.Injective ((pullback.fst G.hom (jK R)).app W).hom := by
  haveI : QuasiCompact (pullback.fst G.hom (jK R)) := inferInstance
  haveI : IsSchemeTheoreticallyDominant (jK R) := by
    unfold jK
    exact SchemeDominantSpecMap.isSchemeTheoreticallyDominant_specMap _ (IsFractionRing.injective R (FractionRing R))
  haveI : IsSchemeTheoreticallyDominant (pullback.fst G.hom (jK R)) := inferInstance
  exact Scheme.Hom.app_injective _ W

private theorem isUnit_gs_scal_of_ne_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (y : (D.BF (FractionRing R)).left)
    {r : R} (hr : r ≠ 0) : IsUnit (gs (𝟙 _) y ⊤ (scal (D.BF (FractionRing R)).hom r)) := by
  unfold scal
  erw [gs_pull (𝟙 _) (D.BF (FractionRing R)).hom y ⊤ trivial, Category.id_comp]
  unfold DegPre.BF
  change IsUnit (cst (TF (FractionRing R) ⊗ D.P.A).hom y r)
  rw [← Over.w (fst (TF (FractionRing R)) D.P.A)]
  unfold TF
  simp only [Over.mk_hom]
  rw [← Category.assoc]
  exact isUnit_cst_of_ne_zero _ y hr

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ maximalIdeal R → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) (σ : H0 U.LG.L k) (s : U.SecK k), GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => ((k : ℕ) : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((k : ℕ) : ℤ)) σ (pullback.fst G.hom (jK R)) 1 → ∀ E : Fam D.toPre (FractionRing R) k, U.Expands k s E → ∃ g : ∀ α : D.toPre.X, D.toPre.SecB k α, (∀ e, U.ExpandsAt e k σ g) ∧ ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (E.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre (FractionRing R)).left 1 := by
  intro R _ _ _ _ I hI D A G _ _ U k σ s hs E hE
  obtain ⟨r, hr, σ', f, hσ', hf, hexp⟩ := hE
  have hLG : U.LG.L.IsLB := U.LG.isLB
  have hP : D.toPre.P.L.IsLB := D.toPre.P.isLB
  haveI : Smooth G.hom := U.smooth
  have hinj : ∀ W : G.left.Opens, Function.Injective ((pullback.fst G.hom (jK R)).app W).hom :=
    fun W => injective_app_pullback_fst_of_flat G W
  have hσ'' : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ)) s
      (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)) σ' (pullback.fst G.hom (jK R))
      (scal (pullback.fst G.hom (jK R) ≫ G.hom) r) := by
    rw [pullback.condition]
    exact hσ'
  have h2 : SecIsMul G.hom r σ' σ := GlobalTheory.IntegralExpansion.secIsMul_of_secScal hLG G.hom hinj hs hσ''
  have h3 := fun e => GlobalTheory.expandsAt_dvd_of_secIsMul R I D A G U e k r σ' σ f h2 (hexp e)
  haveI : Smooth D.toPre.P.A.hom := D.toPre.P.isAb.smooth
  haveI : GeometricallyConnected D.toPre.P.A.hom := D.toPre.P.isAb.geomConnected
  have h4 : ∀ α, ∃ g : D.toPre.SecB k α, SecIsMul D.toPre.P.A.hom r (f α) g := by
    intro α
    refine GlobalTheory.GermDiv.main R I (hI.trans (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge)
      D.toPre.P.A _ (linComb_isLB _ hP _ _) (f α) r hr ?_
    intro n x j hx
    exact dvd_gs_of_dvd_sval hP (f α) (fstG I n D.toPre.P.A).left x (fun J hJ => h3 n α x J hJ) j hx
  choose g hg using h4
  refine ⟨g, fun e => expandsAt_cancel_of_ne_zero R I D A G U k r hr σ σ' g f h2 hg hexp e, ?_⟩
  intro α
  have hga := hg α
  unfold SecIsMul at hga
  refine ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.secScal_of_sval hP (fun y J hJ => ?_)
  have e1 := GlobalTheory.IntegralExpansion.sval_of_secScal (hf α) (𝟙 _) y hJ
  have hm := hJ.mem (D.toPre.famφB α) (𝟙 _ ≫ (D.toPre.prB (FractionRing R)).left)
  have e2 : sval (f α) (𝟙 _ ≫ (D.toPre.prB (FractionRing R)).left) y J =
      gs (𝟙 _ ≫ (D.toPre.prB (FractionRing R)).left) y ⊤ (scal D.toPre.P.A.hom r) *
        sval (g α) (𝟙 _ ≫ (D.toPre.prB (FractionRing R)).left) y J := by
    unfold sval
    erw [hga, gs_mul _ _ _ hm, gs_res _ _ le_top hm]
  rw [e2] at e1
  have e3 : gs (𝟙 _ ≫ (D.toPre.prB (FractionRing R)).left) y ⊤ (scal D.toPre.P.A.hom r) =
      gs (𝟙 _) y ⊤ (scal (D.toPre.BF (FractionRing R)).hom r) := by
    unfold scal
    rw [Category.id_comp]
    erw [gs_pull (D.toPre.prB (FractionRing R)).left D.toPre.P.A.hom y ⊤ trivial,
      gs_pull (𝟙 _) (D.toPre.BF (FractionRing R)).hom y ⊤ trivial, Category.id_comp, Over.w]
  rw [e3] at e1
  have hu : IsUnit (gs (𝟙 _) y ⊤ (scal (D.toPre.BF (FractionRing R)).hom r)) := isUnit_gs_scal_of_ne_zero D.toPre y hr
  exact hu.mul_left_cancel e1

end GlobalTheory.IntegralExpansionLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsUnitOfGenerates
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaNu

theorem isUnit_of_generates {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} {D : DegData R I}
    {k : ℕ} {α : D.toPre.X} {s t : D.toPre.SecB k α} (hs : SecBGenerates k α s) {a : R}
    (h : SecIsMul D.toPre.P.A.hom a s t) : IsUnit a := by
  obtain ⟨b, hb, -⟩ := hs t
  have h₁ : SecIsMul D.toPre.P.A.hom 1 s s := fun j => by simp only [scal, resTop, map_one, _root_.one_mul]
  have h₂ : SecIsMul D.toPre.P.A.hom (a * b) s s := fun j => by
    conv_lhs => rw [h j, hb j]
    simp only [scal, resTop, map_mul, _root_.mul_assoc]
  exact IsUnit.of_mul_eq_one b ((hs s).unique h₂ h₁)

end GlobalTheory.ThetaNu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.UniformisationPowerWithoutExpansionStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.uniformisation_power_without_expansion : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U : UnifPre I D A G), ∃ (U' : UnifPre I D' A' G') (wL : LB.Iso U'.LG.L (boxLB U.LG.L pG.pr)), (∀ i, U'.gen.hom ≫ pA.pr i = (Over.pullback (jK R)).map (pG.pr i) ≫ U.gen.hom) ∧ wL.IsGen ∧ (∃ b : LB.Gen (LB.LinComb U.LG.L (K := Fin j) (fun i => eSec G' ≫ (pG.pr i).left) (fun _ => 1)), GeneratorPullback.MapsAt U.LG.L U'.LG.L (fun i => (pG.pr i).left) wL (eSec G') 1 U'.LG.rig b ∧ LB.Gen.Corr U.LG.L _ _ _ _ b (GeneratorPullback.finProdGen U.LG.L (J := Fin j) (fun _ _ => eSec G) (fun _ _ => 1) (fun _ => U.LG.rig))) ∧ (∀ (e : ℕ) (i : Fin j), (U'.gt e).q ≫ (Over.pullback (thick R I e)).map (pD.pw.pr i) = (Over.pullback (thick R I e)).map (pG.pr i) ≫ (U.gt e).q) ∧ (∀ (e : ℕ) (x : D'.toPre.X), ∃ hψ : ∀ (i : Fin j) (k : Fin 4), D'.toPre.Oφ ((Over.map (thick R I e)).map (U'.gt e).q ≫ D'.toPre.prBe I e) x k ≫ (pD.pw.pr i).left = ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫ D.toPre.Oφ ((Over.map (thick R I e)).map (U.gt e).q ≫ D.toPre.prBe I e) (pD.xe x i) k, LB.Gen.Maps (LB.linCombIso pD.w _ Oinvε) ((U'.gt e).t x) (GeneratorPullback.boxGen D.toPre.P.L (fun i => (pD.pw.pr i).left) _ Oinvε (fun i => GeneratorPullback.pullAlong D.toPre.P.L (pD.pw.pr i).left ((Over.pullback (thick R I e)).map (pG.pr i)).left _ Oinvε _ (hψ i) ((U.gt e).t (pD.xe x i))))) ∧ (∀ (e : ℕ) (jNM : Fin j → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL' : U'.LG.L.ι) (jNL : Fin j → U.LG.L.ι), res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_left) : (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM') ⊓ (LB.div (D'.toPre.P.L.pull (U'.gt e).pG.left) (U'.LG.L.pull (fstG I e G').left)).U (fun _ => jM', fun _ => jL') ⊓ (⨅ i, ((Over.pullback (thick R I e)).map (pG.pr i)).left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left) (U.LG.L.pull (fstG I e G).left)).U (fun _ => jNM i, fun _ => jNL i)) ⊓ (fstG I e G').left ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jNL, jL') ≤ (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM')) (pullU (U'.gt e).pG.left _ (pD.w.s (jNM, jM'))) * res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_right)) ((U'.w e).s (fun _ => jM', fun _ => jL')) = (∏ i, res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_right.trans (iInf_le _ i))) (pullU ((Over.pullback (thick R I e)).map (pG.pr i)).left _ ((U.w e).s (fun _ => jNM i, fun _ => jNL i)))) * res (X := (thickObj R I e G').left) inf_le_right (pullU (Y := (thickObj R I e G').left) (fstG I e G').left _ (wL.s (jNL, jL')))) := by
  first | exact @GlobalTheory.PowUnif.main | exact GlobalTheory.PowUnif.main | (intros; apply GlobalTheory.PowUnif.main <;> assumption)
end

