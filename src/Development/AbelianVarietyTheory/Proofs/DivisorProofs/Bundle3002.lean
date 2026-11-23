module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2226
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2604
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2962
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1810
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsPairMass
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OmEqPullOfVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedVacuumReads
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertIntegralPointsFixAdelicClassicalVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2973
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderActionRosatiAdjoint

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFrameMulIntegralFrameEqRootMulRig
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT

namespace GlobalTheory.USep.FrameRoot

theorem exists_normd {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (ρ : LB.Gen (D.P.L.pull (eSec D.P.A)))
    (hρ : ρ.IsGen) (n : ℕ)
    (α : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![𝟙 D.P.A.left, (mulA D.P.A n).left] ![(n : ℤ) ^ 2, -1]))
    (hα : α.IsGen) (hn : IsNormMul D.P.A D.P.L ρ n α) :
    ∃ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1), Normd κ ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
        val κ r z J = val α r z J * val ρ (r ≫ D.P.A.hom) z J * (val ρ (r ≫ D.P.A.hom) z J ^ (n ^ 2))⁻¹ := by
  have hL := D.P.isLB
  let p := LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) ρ D.P.A.hom
  have hp : p.IsGen := DVR.pullGen_isGen _ _ _ _ hρ _
  let u := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ α p) (LB.invGen D.P.L _ _ (GeneratorPullback.powGen D.P.L _ _ p (n ^ 2)))
  have hu : u.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hα hp)
    (DVR.invGen_isGen _ _ _ _ (DVR.SectionScalarValuation.powGen_isGen' _ _ _ _ hp _))
  have h1 : (1 : D.P.A ⟶ D.P.A).left = D.P.A.hom ≫ eSec D.P.A := rfl
  obtain ⟨κ, hκ, hv⟩ := exists_gen hL
    (φ' := (![𝟙 _, (𝟙 D.P.A ^ n).left, (1 : D.P.A ⟶ D.P.A).left] : Fin 3 → (D.P.A.left ⟶ D.P.A.left)))
    (ε' := ![((n ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ) - ((n ^ 2 : ℕ) : ℤ)]) (by
      intro U _ h
      rw [h1]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module) u hu
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
      val κ r z J = val α r z J * val ρ (r ≫ D.P.A.hom) z J * (val ρ (r ≫ D.P.A.hom) z J ^ (n ^ 2))⁻¹ :=
    fun Z r z J hJ => by
      have a : val p r z J = val ρ (r ≫ D.P.A.hom) z J := val_pull hJ _ _ _
      refine (hv Z r z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg _ a)) ((val_inv _ _).trans (congrArg (·⁻¹) ?_))))
      exact (GlobalTheory.RatioVal.val_powGen _ _ _ _ _).trans (congrArg (· ^ (n ^ 2)) a)
  refine ⟨κ, ⟨hκ, corr_of_val hL fun y J hJ => ?_⟩, key⟩
  have a₃ : val (rigPow D.P.A D.P.L ρ ((n : ℤ) ^ 2)) (𝟙 _) y J = val ρ (𝟙 _) y J ^ ((n : ℤ) ^ 2) := map_zpow _ _ _
  have e₁ : (𝟙 _ ≫ eSec D.P.A) ≫ D.P.A.hom = 𝟙 _ := by
    rw [Category.id_comp]; exact Over.w η[D.P.A]
  have b := (val_pull hJ α (eSec D.P.A) (𝟙 _)).symm.trans ((val_corr hJ hn (𝟙 _)).trans ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) a₃ (val_inv ρ (𝟙 _)))))
  refine (val_pull hJ κ _ _).trans ((key _ _ y J hJ).trans (Eq.trans ?_ (val_one _).symm))
  rw [b]
  refine (congrArg (fun q => val ρ (𝟙 _) y J ^ ((n : ℤ) ^ 2) * (val ρ (𝟙 _) y J)⁻¹ * val ρ q y J *
    (val ρ q y J ^ (n ^ 2))⁻¹) e₁).trans ?_
  rw [← Nat.cast_pow, zpow_natCast, inv_mul_cancel_right, mul_inv_cancel]

theorem val_rigT {S : Scheme.{0}} (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))) (T : Over S) (k : ℤ) {Z : Scheme.{0}}
    (r : Z ⟶ T.left) {z : Z} {J : (Z ⟶ P.A.left) → P.L.ι} (hJ : Good P.L z J) :
    val (rigT P.A P.L rig T k) r z J = val rig (r ≫ T.hom) z J ^ k := by
  rw [val_of rig (r ≫ T.hom) z J (fun _ => J (r ≫ T.hom ≫ eSec P.A))
    (fun _ => by rw [Category.assoc])]
  have hm := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec P.A) r
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ?_)
  exact (gm_res r z _ hm _).trans (gm_pull r T.hom z
    (LB.wchart P.L (fun _ : PUnit => eSec P.A) (fun _ => J (r ≫ T.hom ≫ eSec P.A)))
    (Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hm 0) _)

theorem exists_root {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (T : Over (Sp V))
    (ρ : LB.Gen (D.P.L.pull (eSec D.P.A))) (hρ : ρ.IsGen) (n : ℕ) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A)
    (τ : LB.Gen (LB.LinComb D.P.L (Y := T.left) (K := Fin 1) (fun _ => (toUnit T ≫ b).left) (fun _ => 1)))
    (hτ : IsTorsFrame D.P ρ n (toUnit T ≫ b) τ)
    (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))) (ht : t.IsGen)
    (H : ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1), Normd κ → ∀ (z : T.left) J, Good D.P.L z J →
      val t T.hom z J ^ (n ^ 2) * val κ (T.hom ≫ b.left) z J = 1) :
    ∃ c : Γ(T.left, ⊤)ˣ, c ^ (n ^ 2) = 1 ∧ ∀ (z : T.left) J, Good D.P.L z J →
      val τ (𝟙 _) z J * val t T.hom z J = gm (𝟙 T.left) z ⊤ c * val ρ T.hom z J := by
  have hL := D.P.isLB
  obtain ⟨-, hτg, α, hα, hn, hc⟩ := hτ
  obtain ⟨κ, hκ, hv⟩ := exists_normd D ρ hρ n α hα hn
  have hx : (toUnit T ≫ b).left = T.hom ≫ b.left := rfl
  let p := LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) ρ T.hom
  have hp : p.IsGen := DVR.pullGen_isGen _ _ _ _ hρ _
  let q := LB.pullGen D.P.L _ _ t T.hom
  have hq : q.IsGen := DVR.pullGen_isGen _ _ _ _ ht _
  obtain ⟨u, hu, hw⟩ := exists_gen hL (φ' := fun _ : PUnit => T.hom ≫ eSec D.P.A) (ε' := fun _ => 1) (by
      intro U _ h
      rw [hx]
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type, DegPre.lineε, eSec, mul_comm, mul_left_comm])
    (LB.mulGen D.P.L _ _ _ _ τ q) (DVR.mulGen_isGen _ _ _ _ _ _ _ hτg hq)
  obtain ⟨c, hcv⟩ := GlobalTheory.CoordSep.exists_ratio_base hL (𝟙 T.left) (𝟙 T.left) (Category.comp_id _)
    (fun a => ⟨a, rfl⟩) hu hp
  have key : ∀ (z : T.left) J, Good D.P.L z J →
      val τ (𝟙 _) z J * val t T.hom z J = gm (𝟙 T.left) z ⊤ c * val ρ T.hom z J := fun z J hJ => by
    have a : val p (𝟙 _) z J = val ρ T.hom z J := (val_pull hJ _ _ _).trans (by rw [Category.id_comp])
    have a' : val q (𝟙 _) z J = val t T.hom z J := (val_pull hJ _ _ _).trans (by rw [Category.id_comp])
    have e := hcv _ (𝟙 _) z J hJ
    rw [hw _ _ z J hJ, val_mul hJ, a, a', Category.id_comp, mul_comm (val ρ T.hom z J)] at e
    exact e
  refine ⟨c, unit_ext fun z _ => ?_, key⟩
  choose J hJ using fun χ : T.left ⟶ D.P.A.left => exists_chart hL (χ z)
  replace hJ : Good D.P.L z J := hJ
  have e₁ : (T.hom ≫ b.left) ≫ D.P.A.hom = T.hom := Over.w (toUnit T ≫ b)
  have h₁ := H κ hκ z J hJ
  rw [hv _ _ z J hJ, e₁] at h₁
  have a₃ : val (powFrame D.P.A D.P.L _ τ ((n : ℤ) ^ 2)) (𝟙 _) z J = val τ (𝟙 _) z J ^ ((n : ℤ) ^ 2) := map_zpow _ _ _
  have h₂ := a₃.symm.trans ((val_corr hJ hc (𝟙 _)).trans ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (val_pull hJ α _ _) (val_rigT D.P ρ T 1 _ hJ))))
  replace h₂ : val τ (𝟙 _) z J ^ (n ^ 2) = val α (T.hom ≫ b.left) z J * val ρ T.hom z J := by
    rw [← zpow_natCast, Nat.cast_pow, h₂, zpow_one, Category.id_comp, Category.id_comp, hx]
  have h₃ := congrArg (· ^ (n ^ 2)) (key z J hJ)
  simp only [mul_pow] at h₃
  rw [map_pow, map_one]
  have aux : ∀ {U : Type} [CommGroup U] (a s g r r' w : U), s * (w * r' * r⁻¹) = 1 → a = w * r' → a * s = g * r →
      g = 1 := by
    rintro U _ a s g r r' w h rfl h'
    rw [← h, ← _root_.mul_assoc, mul_comm s, h', mul_inv_cancel_right]
  exact aux _ _ _ _ _ _ h₁ h₂ h₃

theorem frame_mul_eq_root : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (K : Type) [Field K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (n : ℕ), 1 ≤ n → ∀ (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A) (τ : LB.Gen (LB.LinComb D.P.L (Y := (Over.mk (spMap ev)).left) (K := Fin 1) (fun _ => (toUnit (Over.mk (spMap ev)) ≫ b).left) (fun _ => 1))), IsTorsFrame D.P ρ₀ n (toUnit (Over.mk (spMap ev)) ≫ b) τ → ∀ (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen → (∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1), Normd κ → ∀ (z : (Over.mk (spMap ev)).left) J, Good D.P.L z J → val t (Over.mk (spMap ev)).hom z J ^ (n ^ 2) * val κ ((Over.mk (spMap ev)).hom ≫ b.left) z J = 1) → ∃ ζ : K, ζ ^ (n ^ 2) = 1 ∧ ∀ (z : (Over.mk (spMap ev)).left) J, Good D.P.L z J → (val τ (𝟙 _) z J).val * (val t (Over.mk (spMap ev)).hom z J).val = gs (𝟙 (Over.mk (spMap ev)).left) z ⊤ (GlobalTheory.Ex.fnOf ζ) * (val ρ₀ (Over.mk (spMap ev)).hom z J).val := by
  intro V₁ _ _ D K _ ev ρ₀ hρ n _ b τ hτ t ht H
  obtain ⟨c, hc, hv⟩ := exists_root D (Over.mk (spMap ev)) ρ₀ hρ n b τ hτ t ht H
  let e : Γ((Over.mk (spMap ev)).left, ⊤) ≃+* K := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have he : ∀ a : K, GlobalTheory.Ex.fnOf a = e.symm a := fun _ => rfl
  refine ⟨e c.val, ?_, fun z J hJ => ?_⟩
  · rw [← map_pow, ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one]
  · rw [he, e.symm_apply_apply, gs_unit _ _ ⊤ trivial, ← Units.val_mul, ← Units.val_mul]
    exact congrArg Units.val (hv z J hJ)

end GlobalTheory.USep.FrameRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleIsoOfLinearDegenerationDataIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LinDataTriple


open GlobalTheory.LinearUnifIso in
theorem act_comm_noeth : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (RingHom.id R))).obj G), IsMonHom bc.hom → IsPullUnif (RingHom.id R) hD bc U U' → ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X] (ιD : D.toPre.OAct O) (ιD' : D'.toPre.OAct O) (ιA : A.OAct O) (ιA' : A'.OAct O) (ιG : RingAct G O) (ιG' : RingAct G' O), U.OLinear O ιD ιA ιG → U'.OLinear O ιD' ιA' ιG' → (∀ (x : O) (y : D'.toPre.X), hD.xe (x • y) = x • hD.xe y) → (∀ x, (ιD'.onB.act x).left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ≫ (ιD.onB.act x).left) → ∀ x, ιG'.act x ≫ bc.hom = bc.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (ιG.act x) := by
  intro hG R _ _ _ _ I hI D D' A A' G G' _ _ _ _ sG' U U' hD bc hbc hU O _ _ _ _ ιD ιD' ιA ιA' ιG ιG'
    lin lin' hx hB a
  have hs : specOf (RingHom.id R) = 𝟙 _ := specOf_id R
  have := hD.e_hom
  obtain ⟨φ, hφ, eφ⟩ := exists_hom_of_pullback_id hs bc
  obtain ⟨ψ, hψ, eψ⟩ := exists_hom_of_pullback_id hs hD.e
  obtain ⟨wL, -, he, -, H⟩ := (isPullUnif_iff_stalks R R I I _ D D' hD A A' G G' bc U U').1 hU
  have P : ∀ (e : ℕ) {X Y : Over (Spec (CommRingCat.of R))} (c : X ⟶ Y),
      ((Over.pullback (thick R I e)).map c).left ≫ pullback.fst Y.hom (thick R I e) =
        pullback.fst X.hom (thick R I e) ≫ c.left := fun e _ _ c => pullback.lift_fst _ _ _
  have hψa : ιD'.onB.act a ≫ ψ = ψ ≫ ιD.onB.act a := Over.OverMorphism.ext (by
    rw [Over.comp_left, Over.comp_left, eψ]; exact hB a)
  have key : ιG'.act a ≫ φ = φ ≫ ιG.act a := by
    have := sG'.smooth
    have := sG'.geomConnected
    have := U.separated
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I
      (hI ▸ IsLocalRing.maximalIdeal_le_jacobson ⊥) G').2 G _ _ fun e => ?_
    obtain ⟨h, hf, ⟨hp, ht⟩, -⟩ := H e
    obtain rfl : h = ((Over.pullback (thick R I e)).map φ).left := by
      rw [← cancel_mono (pullback.fst G.hom (thick R I e)), P, eφ]
      exact hf
    have hq : (Over.pullback (thick R I e)).map φ ≫ (U.gt e).q =
        (U'.gt e).q ≫ (Over.pullback (thick R I e)).map ψ := by
      refine Over.OverMorphism.ext ?_
      rw [← cancel_mono (pullback.fst D.toPre.P.A.hom (thick R I e)), Over.comp_left, Over.comp_left,
        Category.assoc, Category.assoc, P, eψ]
      exact hp.symm.trans (Category.assoc _ _ _)
    obtain ⟨s, hsi, hsx⟩ := exists_torus_map (U.gt e) (U'.gt e) _ _ hq hD.w hD.xe (fun x => (ht x).1)
      (fun x => (ht x).2)
    obtain ⟨t, tc, ti⟩ := lin.i_lin e a
    obtain ⟨t', tc', ti'⟩ := lin'.i_lin e a
    have := ιG.hom a
    have := ιG'.hom a
    have hts : t' ≫ s = s ≫ t := by
      refine PowTorus.torus_ext _ _ fun χ z => ?_
      obtain ⟨x, rfl⟩ := hD.xe.surjective χ
      rw [Over.comp_left, Over.comp_left, gm_torusEnd tc, ← hx, hsx, gm_comp_of_id _ _ _ (hsx x),
        ← gm_torusEnd tc', Category.id_comp]
    have E : (Over.pullback (thick R I e)).map (ιG'.act a) ≫ (Over.pullback (thick R I e)).map φ =
        (Over.pullback (thick R I e)).map φ ≫ (Over.pullback (thick R I e)).map (ιG.act a) := by
      refine hom_ext_torus (U.gt e) (U'.gt e) hG _ _ ?_ ?_
      · rw [Category.assoc, Category.assoc, lin.q_lin, hq, reassoc_of% hq, reassoc_of% (lin'.q_lin e a),
          ← Functor.map_comp, ← Functor.map_comp, hψa]
      · rw [reassoc_of% ti', ← hsi, ← reassoc_of% hsi, ti, reassoc_of% hts]
    rw [← Functor.map_comp, ← Functor.map_comp] at E
    exact (P e _).symm.trans ((congrArg (fun c => c.left ≫ pullback.fst G.hom (thick R I e)) E).trans (P e _))
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  have a₂ : ((Over.pullback (specOf (RingHom.id R))).map (ιG.act a)).left ≫
      pullback.fst G.hom (specOf (RingHom.id R)) = pullback.fst _ _ ≫ (ιG.act a).left :=
    pullback.lift_fst _ _ _
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, a₂, ← eφ, ← Category.assoc, ← eφ,
    ← Over.comp_left, key, Over.comp_left]

end GlobalTheory.LinDataTriple

theorem GlobalTheory.triple_iso_of_linear_data_iso : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (t t' : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (P' : PELUnif (maximalIdeal V) t') (hD : IsPullDeg (RingHom.id V) P.D.toPre P'.D.toPre), (∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y) → (letI := H.starRing; ∀ x, P'.oD.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id V))).map (P.oD.onB.act x)) → Nonempty (SABMap t' t (𝟙 _)) := by
  intro E _ _ _ H V _ _ _ hB t t' P P' hD hx hB'
  letI := H.starRing
  have hR : AdmBase V (maximalIdeal V) := hB.1
  have := hR.1
  obtain ⟨ψ, bc, -, hψm, hbcm, hbc', hP, -⟩ := GlobalTheory.unif_determined_by_data_normal V hR P.D P.A t.G t.semi P.U
    P'.D P'.A t'.G t'.semi P'.U hD
  have hL := GlobalTheory.firstFiveLaws.1
  have hBl : ∀ x, (P'.oD.onB.act x).left ≫ (hD.e.hom.left ≫ pullback.fst P.D.toPre.P.A.hom (specOf (RingHom.id V))) =
      (hD.e.hom.left ≫ pullback.fst P.D.toPre.P.A.hom (specOf (RingHom.id V))) ≫ (P.oD.onB.act x).left := by
    intro x
    have e := congrArg (fun c => c.left ≫ pullback.fst P.D.toPre.P.A.hom (specOf (RingHom.id V))) (hB' x)
    simp only [Over.comp_left, Category.assoc] at e
    rw [e]
    exact congrArg (hD.e.hom.left ≫ ·) (pullback.lift_fst _ _ _)
  have hact := GlobalTheory.LinDataTriple.act_comm_noeth hL.globalFns V (maximalIdeal V) rfl P.D P'.D P.A P'.A t.G t'.G
    t'.semi P.U P'.U hD bc hbcm hP (𝓞 E) P.oD P'.oD P.oA P'.oA t.act.toRingAct t'.act.toRingAct P.lin P'.lin hx hBl
  have hact' : ∀ a, (t'.act.act a).left ≫ ψ.hom.left = ψ.hom.left ≫ (t.act.act a).left := by
    intro a
    have e := congrArg (fun c => c.left ≫ pullback.fst t.G.hom (specOf (RingHom.id V))) (hact a)
    simp only [Over.comp_left, Category.assoc] at e
    rw [← hbc', Category.assoc]
    exact e.trans (congrArg (bc.hom.left ≫ ·) (pullback.lift_fst _ _ _))
  have hLB : LBIso t'.PP.L (t.PP.L.pull ψ.hom.left) := by
    obtain ⟨w, hw, -⟩ := hP.lg
    rw [← P.bundle, ← P'.bundle, ← hbc']
    exact ⟨w, hw⟩
  have := P'.U.gen_hom
  have hp : IsProper (pullback.snd t'.G.hom (jK V)) :=
    MorphismProperty.of_isPullback (P := @IsProper) (isGrpPullback_of_iso P'.U.gen).1 P'.A.isAb.proper
  have hab := GlobalTheory.RigCube.genericPoints_subset_abLocus t'.G t'.semi hp
  obtain ⟨ν, -⟩ := GlobalTheory.exists_sabMap_of_lbIso E H (Sp V) (Sp V) t t' (𝟙 _) ψ.hom.left ⟨inferInstance, hab⟩
    (isGrpPullback_of_iso ψ) hact' hLB
  exact ⟨ν⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryNormDescentIdealToComponent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.UNormDown

theorem jK_spMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (fK : FractionRing R →+* FractionRing S)
    (hc : ∀ a, fK (algebraMap R _ a) = algebraMap S _ (f a)) : jK S ≫ spMap f = spMap fK ≫ jK R := by
  simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a
  exact (hc a).symm

theorem normDescent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (A : Set C.Z), IsClopen A → IsIrreducible A → (A ∩ Set.range C.i).Nonempty → ∀ (X₁ : USetup C) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = A → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range C.i) → UValThru Xo c C.i X₁.π Set.univ φ J₁ ι → ∃ (k : ℕ) (J : C.Z.IdealSheafData), 1 ≤ k ∧ (∀ x ∈ J.support, x ∈ A ∧ x ∉ Set.range C.i) ∧ ∀ (T : UTrait Xo c) (ξ₁ : Sp T.V ⟶ X₁.M.Z), T.y ≫ C.i = jK T.V ≫ ξ₁ ≫ X₁.π → idlAlong J (ξ₁ ≫ X₁.π) = idlAlong J₁ ξ₁ ^ k := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C A hAc hAi hAm X₁ ι J₁ hι hπ hsupp hv
  have hne : ((⊤ : X₁.M.Z.Opens) : Set X₁.M.Z).Nonempty := Set.univ_nonempty
  haveI : CharZero X₁.Ω₁ := X₁.ar.char
  haveI hchar : CharZero Γ(X₁.M.Z, ⊤) := RingHom.charZero (X₁.M.res ⊤ hne)
  haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  haveI := X₁.M.lft
  have hLN : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
  obtain ⟨d, J, hd, hJs, hJl⟩ := _root_.GlobalTheory.NormSheaf.normDescentSheaf X₁.M.Z C.Z X₁.π X₁.fin inferInstance hLN X₁.normal C.normal
    (by rw [hπ]; exact hAc.isOpen) hchar J₁
  refine ⟨d, J, hd, fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hJs x hx
    exact ⟨hπ ▸ ⟨y, rfl⟩, hsupp y hy⟩
  intro T ξ₁ hgen
  obtain ⟨hdvr, hcpl, hch⟩ := (GlobalTheory.LN.cDvr_iff T.V).1 T.cdvr
  obtain ⟨V', _, _, _, _, f, ψ, hc', hfi, hfl, hψ, hprod⟩ :=
    hJl T.V hcpl (ξ₁ ≫ X₁.π) ⟨ξ₁ (closedPoint T.V), rfl⟩
  let fK : FractionRing T.V →+* FractionRing V' :=
    IsLocalization.map (FractionRing V') f (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hfi)
  have hfK : ∀ a, fK (algebraMap T.V _ a) = algebraMap V' _ (f a) := fun a => IsLocalization.map_eq _ a
  have hB : GlobalTheory.Mum.Base V' := ⟨⟨inferInstance, inferInstance, inferInstance, hc'⟩, inferInstance⟩
  obtain ⟨T₂, f₂, fK₂, hi₂, hl₂, -, hc₂, hy₂⟩ := _root_.GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo c V' hB inferInstance (spMap fK ≫ T.y)

  have hover : ∀ χ : Sp V' ⟶ X₁.M.Z, χ ≫ X₁.π = spMap f ≫ ξ₁ ≫ X₁.π →
      T₂.y ≫ C.i = jK T₂.V ≫ (spMap f₂ ≫ χ) ≫ X₁.π := by
    intro χ hχ
    have e1 : jK T₂.V ≫ (spMap f₂ ≫ χ) ≫ X₁.π = (jK T₂.V ≫ spMap f₂) ≫ (χ ≫ X₁.π) := by
      simp only [Category.assoc]
    have e2 : (jK V' ≫ spMap f) ≫ ξ₁ ≫ X₁.π = spMap fK ≫ T.y ≫ C.i := by
      rw [jK_spMap f fK hfK, Category.assoc, hgen]
    rw [e1, hχ, jK_spMap f₂ fK₂ hc₂, Category.assoc, ← Category.assoc (jK V'), e2, hy₂]
    simp only [Category.assoc]
  have hord : ∀ χ : Sp V' ⟶ X₁.M.Z, χ ≫ X₁.π = spMap f ≫ ξ₁ ≫ X₁.π →
      ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T₂.be ∧ idlAlong J₁ (spMap f₂ ≫ χ) = Ideal.span {T₂.ϖ ^ a} := by
    intro χ hχ
    obtain ⟨tK, h1, h2⟩ := T₂.gen
    exact hv T₂.V T₂.cdvr T₂.ϖ T₂.irr (spMap f₂ ≫ χ) T₂.y (hover χ hχ) trivial T₂.t tK h1 h2 T₂.P T₂.be T₂.lev
      T₂.mono
  obtain ⟨a₀, ha₀, h₀⟩ := hord (spMap f ≫ ξ₁) (Category.assoc _ _ _)
  have hj : ∀ j, idlAlong J₁ (spMap f₂ ≫ ψ j) = Ideal.span {T₂.ϖ ^ a₀} := by
    intro j
    obtain ⟨a, ha, h⟩ := hord (ψ j) (hψ j)
    rw [h, show a = a₀ from by exact_mod_cast ha.trans ha₀.symm]
  have hcomp : spMap (f₂.comp f) = spMap f₂ ≫ spMap f := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  haveI : IsLocalHom (f₂.comp f) := RingHom.isLocalHom_comp f₂ f
  have idlAlong_eq_map_local {X : Scheme.{0}} (I : X.IdealSheafData) {R : Type}
      [CommRing R] [IsLocalRing R] (χ : Sp R ⟶ X) (U : X.affineOpens)
      (hle : ⊤ ≤ χ ⁻¹ᵁ U.1) :
      idlAlong I χ = (I.ideal U).map (χ.appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of R)).hom).hom := by
    have hx : χ (closedPoint R) ∈ U.1 := hle trivial
    unfold idlAlong
    rw [ds_stalkId_eq_map I U _ hx, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
    congr 2
  have idlAlong_comp_local {X : Scheme.{0}} (I : X.IdealSheafData) {R S : Type}
      [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
      (χ : Sp R ⟶ X) (g : R →+* S) : idlAlong I (spMap g ≫ χ) = (idlAlong I χ).map g := by
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show χ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
    have hle : ⊤ ≤ χ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem χ hx).ge
    have hle' : ⊤ ≤ (spMap g ≫ χ) ⁻¹ᵁ U := fun x _ => hle (show spMap g x ∈ (⊤ : (Sp R).Opens) from trivial)
    rw [idlAlong_eq_map_local I χ ⟨U, hU⟩ hle, idlAlong_eq_map_local I _ ⟨U, hU⟩ hle', Ideal.map_map]
    congr 1
    have e : (spMap g ≫ χ).appLE U ⊤ hle' = χ.appLE U ⊤ hle ≫ (spMap g).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    rw [e, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, CommRingCat.hom_comp]
    rfl
  apply GlobalTheory.TraitOrder.map_injective (f₂.comp f) (hi₂.comp hfi)
  have hmp := map_prod (Ideal.mapHom f₂) (fun j => idlAlong J₁ (ψ j)) Finset.univ
  simp only [Ideal.mapHom_apply] at hmp
  rw [← Ideal.map_map, hprod, Ideal.map_pow, ← idlAlong_comp_local, hcomp, Category.assoc, h₀, hmp]
  simp only [← idlAlong_comp_local, hj, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end GlobalTheory.UPoinc.UNormDown
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFinitePartMovesVacuumAsThetaModel
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacMoveFin

theorem mulStep : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  GlobalTheory.NormSum.Inp D → ∀ t0 : ℂ, Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Even (a * d) → oddE0 D cc δ t0 a d e0 →
  HasFinPart χS W.chV W.ep → HasFinPart χT W.chV' (-W.ep') →
  ∀ f₀ : WO S T → ℂ, Reads ψ θ hS hT cc δ r e0 f₀ →
  ∀ (x₁ : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y₁ : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g₁ : GA D S) (h₁ : GA D T)
    (x₂ : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y₂ : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g₂ : GA D S) (h₂ : GA D T) (c₁ c₂ : ℂ),
    IsFinPt S g₁ x₁ → IsFinPt T h₁ y₁ → IsFinPt S g₂ x₂ → IsFinPt T h₂ y₂ →
    Reads ψ θ hS hT cc δ r (c₁ • W.Om x₁ y₁ e0) (om (g₁, h₁) f₀) → Reads ψ θ hS hT cc δ r (c₂ • W.Om x₂ y₂ e0) (om (g₂, h₂) f₀) →
    Reads ψ θ hS hT cc δ r ((c₁ * c₂) • W.Om (x₁ * x₂) (y₁ * y₂) e0) (om (g₁ * g₂, h₁ * h₂) f₀) := by
  intro D ψ θ S T a d hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT f₀ hf₀ x₁ y₁ g₁ h₁ x₂ y₂ g₂ h₂ c₁ c₂ hg₁ hh₁ hg₂ hh₂ hr₁ hr₂
  have he := GlobalTheory.NormSum.Model.vac_mem_TT hSet.crv hodd.1
  have hG := GlobalTheory.NormSum.RatExtend.TT_smul c₂ (W.maps x₂ y₂ e0 he)
  have key := _root_.GlobalTheory.NormExact.reads_om_of_vacuum ψ θ S T hS hT cc δ r hSet e0 W χS χT om hW hodd.1 x₁ y₁ g₁ h₁ hg₁ hh₁ c₁ f₀ hf₀ hr₁ _ hG _ hr₂
  have h1 : om (g₁ * g₂, h₁ * h₂) f₀ = om (g₁, h₁) (om (g₂, h₂) f₀) := by
    rw [← Prod.mk_mul_mk, map_mul, Module.End.mul_apply]
  have h2 : (c₁ * c₂) • W.Om (x₁ * x₂) (y₁ * y₂) e0 = c₁ • W.Om x₁ y₁ (c₂ • W.Om x₂ y₂ e0) := by
    rw [W.smul _ _ _ _ (W.maps x₂ y₂ e0 he), ← W.mul _ _ _ _ _ he, smul_smul]
  rw [h1, h2]; exact key

theorem vacuum_move_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  GlobalTheory.NormSum.Inp D → ∀ t0 : ℂ, Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Even (a * d) → oddE0 D cc δ t0 a d e0 →
  HasFinPart χS W.chV W.ep → HasFinPart χT W.chV' (-W.ep') →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∀ f₀ : WO S T → ℂ, Reads ψ θ hS hT cc δ r e0 f₀ → Reads ψ θ hS hT cc δ r (W.Om x y e0) (om (g, h) f₀) := by
  intro D ψ θ S T a d hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT x y g h hg hh f₀ hf₀
  exact _root_.GlobalTheory.VacTriv.vacuum_const_trivial ψ θ S T hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT f₀ hf₀
    (GlobalTheory.VacLine.moved_vacuum_reads ψ θ S T hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT f₀ hf₀)
    (mulStep ψ θ S T hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT f₀ hf₀)
    (GlobalTheory.SplitVacMove.reads_om_split ψ θ S T hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT f₀ hf₀)
    (_root_.GlobalTheory.VacInertMove.inert_vacuum_reads ψ θ S T hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT f₀ hf₀) x y g h hg hh

end GlobalTheory.VacMoveFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelOfSecondCoordTrivial
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open GlobalTheory.CechPic GlobalTheory.AbDual

namespace GlobalTheory.ZarhinFam.KerC

theorem ker_zarhinPolarization_of_pullback : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (T : Over S) (x : T ⟶ GlobalTheory.ZarhinFam.Zob c.A B), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → (∀ j, x ≫ GlobalTheory.ZarhinFam.pb c.A B j = 1) → ∀ j, ∏ i, (x ≫ GlobalTheory.ZarhinFam.pa c.A B i) ^ GlobalTheory.ZarhinFam.quat d j i = 1 := by
  intro h M d S t c B _ _ Q la mu hZ T x hx hv j
  obtain ⟨hB, hD1, hD2, hla, hmu, hlm, hml, hPiso⟩ := id hZ
  haveI : IsMonHom la := hla
  have hQ : Q.IsLB := hD1.isLB
  have hPQ : ∀ (Y : Over S) (a a' : Y ⟶ c.A), evc c.isLB a a' = evc hQ a (a' ≫ la) := by
    have e : cls c.P c.isLB = evc hQ (fst c.A c.A) (snd c.A c.A ≫ la) :=
      (cls_eq_iff c.isLB (pull_isLB hQ _)).2 hPiso
    intro Y a a'
    show CechPic.pull (lift a a').left (cls c.P c.isLB) = _
    rw [e, pull_evc, lift_fst, lift_snd_assoc]
  have hz := zarhinBundle_isLineBundle c.A B c.isLB hQ d mu
  have h0 : CechPic.pull (lift (snd (Zob c.A B) T ≫ x) (fst (Zob c.A B) T)).left
      (zCls c.A B c.isLB hQ d mu) = 0 := by
    rw [← cls_zP c.A B c.isLB hQ d mu, ← cls_pull hz]
    exact (cls_eq_zero_iff (pull_isLB hz _)).2 hx
  have h1 := congrArg (CechPic.pull
    (lift (mkZ c.A B (fun _ => 1) (fun j' => if j' = j then snd T B else 1)) (fst T B) :
      T ⊗ B ⟶ Zob c.A B ⊗ T).left) h0
  rw [← pull_comp, ← Over.comp_left, comp_lift, map_zero, lift_snd_assoc, lift_fst,
    AdjPf.pull_zCls c.isLB hQ d la mu hPQ] at h1
  simp only [AdjPf.zf, Category.assoc, AdjPf.mkZ_pa, AdjPf.mkZ_pb, hv, MonObj.comp_one, MonObj.one_comp,
    evc_one_right hQ hD1.zero, hD1.additive.evc_one hQ, smul_zero, Finset.sum_const_zero, zero_add, add_zero] at h1
  simp only [apply_ite (evc hQ _), evc_one_right hQ hD1.zero, smul_ite, smul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h1
  refine (hD1.isPerfect hD2).ker_left T _ ((triv_ev_iff hQ _ _).2 ?_)
  let F : (T ⊗ B ⟶ c.A) →* Multiplicative (Pic (T ⊗ B).left) :=
    MonoidHom.mk' (fun a => Multiplicative.ofAdd (evc hQ a (snd T B))) fun a a' => by
      rw [(isAdditive_iff hQ).1 hD1.additive, ofAdd_add]
  have eF : ∀ a, evc hQ a (snd T B) = Multiplicative.toAdd (F a) := fun _ => rfl
  have ep : fst T B ≫ ∏ i, (x ≫ pa c.A B i) ^ quat d j i = ∏ i, (fst T B ≫ x ≫ pa c.A B i) ^ quat d j i := by
    have := map_prod (AdjPf.pre (G := c.A) (fst T B)) (fun i => (x ≫ pa c.A B i) ^ quat d j i) Finset.univ
    simp only [map_zpow] at this
    exact this
  rw [ep, eF, map_prod, toAdd_prod]
  simp only [map_zpow, toAdd_zpow, ← eF]
  exact h1

end GlobalTheory.ZarhinFam.KerC
end
end

