module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3080
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2255
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3081
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2316
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3079
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0985
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2584
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3082
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentKummerCupProductBijectiveStrictlyHenselia
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Rosati
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0791
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalInjectionsAgreeCanonicalFamilyCoordinates
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2974
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3057

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorNonKltPointsNumericallyMultipleStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_divisor_nonKlt_points_numerically_multiple : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p;
    ∀ (Δ : X → ℚ) (m : ℕ) (G A : CartierDiv X) (D : X → ℚ) (P : Finset X) (z : X) (k : ℕ) (h : ℚ),
      IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB (toLB A) →
      IsQCart D → (∀ x ∈ P, IsClosed ({x} : Set X) ∧ z ⤳ x) → 1 ≤ k →
      topologicalKrullDim (closure ({z} : Set X)) = k → (z = genericPoint X ∨ IsNkltCentre p n (Δ + D) z) → 0 < h →
      (P.card : ℚ) * (k : ℚ) ^ k < h ^ k * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => toLB A : ℤ) →
      ∃ (B : X → ℚ) (δ₀ : ℚ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧ QNum p (toLB A) h B ∧ Off B z ∧
        (∀ δ : ℚ, 0 ≤ δ → δ ≤ δ₀ → ∀ x ∈ P, ¬ KltAt p n (Δ + (1 - δ) • D + B) x) ∧
        (∀ y, ¬ z ⤳ y → ∀ a : ℚ, 0 ≤ a → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + B) y) := by
  first | exact @GlobalTheory.AmpleStep.exists_divisor | exact GlobalTheory.AmpleStep.exists_divisor | (intros; apply GlobalTheory.AmpleStep.exists_divisor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalStructureOfGenericPolarisationE
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.EvenPackage

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'}

theorem jK_sq (hρ : Function.Injective ρ) : jK R' ≫ spMap ρ =
    spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) ≫ jK R := by
  simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  simp [IsFractionRing.map, IsLocalization.map_eq]

theorem exists_genericMap (hρ : Function.Injective ρ) {G : Over (Sp R)} {G₁ : Over (Sp R')} {β : G₁.left ⟶ G.left}
    (w : β ≫ G.hom = G₁.hom ≫ spMap ρ) : ∃ κ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R),
      κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β := by
  refine ⟨pullback.lift _ (pullback.snd _ _ ≫
    spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ)) ?_, pullback.lift_fst _ _ _⟩
  rw [Category.assoc, w, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, jK_sq hρ]

theorem isGrpPullback_generic (hρ : Function.Injective ρ) {G : Over (Sp R)} [GrpObj G] {G₁ : Over (Sp R')} [GrpObj G₁]
    {β : G₁.left ⟶ G.left} {κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)}
    (hβ : IsGrpPullback G₁ G (spMap ρ) β) (hκf : κ₁ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β) :
    IsGrpPullback ((Over.pullback (jK R')).obj G₁) ((Over.pullback (jK R)).obj G)
      (spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ)) κ₁ := by
  have hsq := jK_sq hρ
  have hmono : Mono (jK R) := EvenDesc.mono_jK R
  have w : κ₁ ≫ ((Over.pullback (jK R)).obj G).hom = ((Over.pullback (jK R')).obj G₁).hom ≫
      spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) := by
    apply (cancel_mono (jK R)).1
    rw [Category.assoc, Category.assoc]
    change κ₁ ≫ pullback.snd G.hom (jK R) ≫ jK R = pullback.snd G₁.hom (jK R') ≫
      spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) ≫ jK R
    rw [← pullback.condition, ← Category.assoc, hκf, Category.assoc, hβ.1.w, ← Category.assoc, pullback.condition,
      Category.assoc, hsq]
  exact (isGrpPullback_pullback G (jK R)).cancel
      (((isGrpPullback_pullback G₁ (jK R')).comp hβ).congr hsq hκf.symm) w

theorem exists_square_extLam (hρ : Function.Injective ρ) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {G₁ : Over (Sp R')} [GrpObj G₁] [IsCommMonObj G₁]
    {β : G₁.left ⟶ G.left} {κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)}
    (hβ : IsGrpPullback G₁ G (spMap ρ) β) (hκf : κ₁ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β)
    (L : LB ((Over.pullback (jK R)).obj G).left) (PP : LB (G2 G).left) (hL : L.IsLB) (hExt : ExtLam G L PP) :
    ∃ β₂ : (G2 G₁).left ⟶ (G2 G).left, Geo.Tor.IsSquare β β₂ ∧ ExtLam G₁ (L.pull κ₁) (PP.pull β₂) := by
  have hκ := isGrpPullback_generic hρ hβ hκf
  have : IsCommMonObj ((Over.pullback (jK R)).obj G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (jK R')).obj G₁) := Functor.isCommMonObj_obj
  obtain ⟨β₂κ, hsqκ, Hκ⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R')).obj G₁) κ₁ hκ
  obtain ⟨β₂, hsqβ, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G G₁ β hβ
  obtain ⟨g₂, hg₂, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G ((Over.pullback (jK R)).obj G) _ (isGrpPullback_pullback G (jK R))
  refine ⟨β₂, hsqβ, pull_isLB hExt.1 β₂, fun κ₂ hκ₂ => ?_⟩
  have hN := pull_isLB hL κ₁
  have H1 := Hκ L (L.pull κ₁) _ PP g₂ hL hN hExt.1 (GlobalTheory.PolBaseChange.lbIso_refl hN) (hExt.2 g₂ hg₂)
  have e : β₂κ ≫ g₂ = κ₂ ≫ β₂ := by
    apply pullback.hom_ext
    · show (β₂κ ≫ g₂) ≫ (fst G G).left = (κ₂ ≫ β₂) ≫ (fst G G).left
      rw [Category.assoc, hg₂.1, ← Category.assoc, hsqκ.1, Category.assoc, hκf, Category.assoc, hsqβ.1,
        reassoc_of% hκ₂.1]
    · show (β₂κ ≫ g₂) ≫ (snd G G).left = (κ₂ ≫ β₂) ≫ (snd G G).left
      rw [Category.assoc, hg₂.2, ← Category.assoc, hsqκ.2, Category.assoc, hκf, Category.assoc, hsqβ.2,
        reassoc_of% hκ₂.2]
  exact LBIso.trans (DVR.linComb_isLB _ hN _ _) (pull_isLB hExt.1 _) (pull_isLB (pull_isLB hExt.1 _) _) H1
    (LBIso.chartPull (chartPullSame PP _ (fun _ => β₂) _ κ₂ fun _ => e) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ κ₂ κ₂ rfl)
      (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hExt.1 β₂)))

theorem exists_generic_pol (hρ : Function.Injective ρ) {G : Over (Sp R)} [GrpObj G]
    {G₁ : Over (Sp R')} [GrpObj G₁]
    {β : G₁.left ⟶ G.left} {κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)}
    (hβ : IsGrpPullback G₁ G (spMap ρ) β) (hκf : κ₁ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β)
    (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A) (hgen : IsMonHom gen.hom) :
    ∃ (A' : PolAV (Sp (FractionRing R'))) (gen' : (Over.pullback (jK R')).obj G₁ ≅ A'.A), IsMonHom gen'.hom ∧
      LBIso (A'.L.pull gen'.hom.left) ((A.L.pull gen.hom.left).pull κ₁) := by
  have hκ := isGrpPullback_generic hρ hβ hκf
  obtain ⟨A', gA, pA, -, mA, tA⟩ := GlobalTheory.polBaseChange_holds _ _
    (spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ)) A
  have gpA : IsGrpPullback A'.A A.A (spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ)) gA :=
    ⟨pA, fun T x y x₀ y₀ hx hy => by
      have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
      have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
      rw [e₁, e₂, ← mA]; rfl⟩
  have tA' : LBIso (A.L.pull gA) A'.L := tA
  obtain ⟨e, he, hee⟩ := grpPullback_iso ((hκ.comp (isGrpPullback_of_iso gen)).congr (Category.comp_id _) rfl) gpA
  refine ⟨A', e, he, ?_⟩
  exact LBIso.trans (pull_isLB A'.isLB _) (pull_isLB A.isLB _) (pull_isLB (pull_isLB A.isLB _) _)
    (GlobalTheory.GenSpread.lbIso_pull_of_lbIso tA'.symm e.hom.left hee.symm)
    (GlobalTheory.GenSpread.lbIso_pull_pull A.isLB κ₁ rfl)

end GlobalTheory.Mum.EvenPackage


set_option maxHeartbeats 1000000 in
open GlobalTheory.Mum.EvenPackage in
theorem GlobalTheory.Mum.exists_even_package_of_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W) (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G.hom (jK R)), GlobalTheory.LN.CDvr W → Function.Injective φ → IsLocalHom φ → IsGrpPullback GW G (spMap φ) βW → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW → LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A.L.pull gen.hom.left).pull κ) → ∀ (R₃ : Type) [CommRing R₃] [IsDomain R₃] [IsLocalRing R₃] (ρ₃ : R →+* R₃) (G₃ : Over (Sp R₃)) [GrpObj G₃] [IsCommMonObj G₃] (β₃ : G₃.left ⟶ G.left) (κ₃ : pullback G₃.hom (jK R₃) ⟶ pullback G.hom (jK R)) (L₃ : LB G₃.left), FinExt ρ₃ → IsGrpPullback G₃ G (spMap ρ₃) β₃ → κ₃ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β₃ → L₃.IsLB → LBIso (L₃.pull (pullback.fst G₃.hom (jK R₃))) ((A.L.pull gen.hom.left).pull κ₃) → ∃ (R₉ : Type) (_ : CommRing R₉) (_ : IsDomain R₉) (_ : IsLocalRing R₉) (ρ : R →+* R₉) (G₉ : Over (Sp R₉)) (_ : GrpObj G₉) (_ : IsCommMonObj G₉) (β₉ : G₉.left ⟶ G.left) (β₉₂ : (G2 G₉).left ⟶ (G2 G).left) (P : GlobalTheory.UU.CP G₉) (A₉ : PolAV (Sp (FractionRing R₉))) (gen₉ : (Over.pullback (jK R₉)).obj G₉ ≅ A₉.A), FinExt ρ ∧ IsGrpPullback G₉ G (spMap ρ) β₉ ∧ Geo.Tor.IsSquare β₉ β₉₂ ∧ IsSemiAbelian G₉ ∧ LBIso (abelian₂ G₉ P.L.L) (PP.pull β₉₂) ∧ EvenOn P ∧ IsMonHom gen₉.hom ∧ LBIso (A₉.L.pull gen₉.hom.left) (P.L.L.pull (pullback.fst G₉.hom (jK R₉))) := by
  intro R _ _ _ hR G _ _ hG A gen hgen PP hPP W _ _ _ φ GW _ _ βW DW AW UW κ hW hφi hφl hGW hκ hUW
    R₃ _ _ _ ρ₃ G₃ _ _ β₃ κ₃ L₃ hρ₃ hβ₃ hκ₃ hL₃ hL₃g
  have hR₃ : Base R₃ := by
    haveI := hR.2
    exact ⟨hρ₃.1, charZero_of_injective_ringHom hρ₃.2.1⟩
  have hG₃ : IsSemiAbelian G₃ := EvenDesc.isSemiAbelian_of_isGrpPullback hβ₃ hG
  obtain ⟨R₉, i1, i2, i3, ρ₄, G₉, i4, i5, β₄, X, i6, i7, i8, hρ₄, hβ₄, hTQ⟩ :=
    exists_finExt_tq_closedFibre R₃ hR₃ G₃ hG₃
  have hρ : FinExt (ρ₄.comp ρ₃) := ⟨hρ₄.1, hρ₄.2.1.comp hρ₃.2.1, hρ₄.2.2.comp hρ₃.2.2⟩
  have hβ : IsGrpPullback G₉ G (spMap (ρ₄.comp ρ₃)) (β₄ ≫ β₃) :=
    (hβ₄.comp hβ₃).congr (TraitExt.spMap_comp _ _) rfl
  have hG₉ : IsSemiAbelian G₉ := EvenDesc.isSemiAbelian_of_isGrpPullback hβ hG
  obtain ⟨κ₄, hκ₄⟩ := exists_genericMap hρ₄.2.1 hβ₄.1.w
  have hκ₉ : (κ₄ ≫ κ₃) ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β₄ ≫ β₃ := by
    rw [Category.assoc, hκ₃, ← Category.assoc, hκ₄, Category.assoc]
  have hN : (A.L.pull gen.hom.left).IsLB := pull_isLB A.isLB _
  have hL₉ : (L₃.pull β₄).IsLB := pull_isLB hL₃ _
  have hL₉g : LBIso ((L₃.pull β₄).pull (pullback.fst G₉.hom (jK R₉))) ((A.L.pull gen.hom.left).pull (κ₄ ≫ κ₃)) :=
    LBIso.trans (pull_isLB hL₉ _) (pull_isLB hL₃ _) (pull_isLB hN _)
      (GlobalTheory.GenSpread.lbIso_pull_pull hL₃ (pullback.fst G₉.hom (jK R₉)) rfl).symm
      (GlobalTheory.GenSpread.lbIso_pull_comp κ₄ hκ₄.symm rfl hL₃g)
  obtain ⟨A₉, gen₉, hgen₉, hA₉⟩ := exists_generic_pol hρ.2.1 hβ hκ₉ A gen hgen
  have hA₉' : LBIso (A₉.L.pull gen₉.hom.left) ((L₃.pull β₄).pull (pullback.fst G₉.hom (jK R₉))) :=
    LBIso.trans (pull_isLB A₉.isLB _) (pull_isLB hN _) (pull_isLB hL₉ _) hA₉ hL₉g.symm
  have hprop : IsProper (pullback.snd G₉.hom (jK R₉)) := by
    have hi : IsIso gen₉.hom.left := ((Over.forget _).mapIso gen₉).isIso_hom
    have := A₉.isAb.proper
    have hw : pullback.snd G₉.hom (jK R₉) = gen₉.hom.left ≫ A₉.A.hom := (Over.w gen₉.hom).symm
    rw [hw]; infer_instance
  have hsym := GlobalTheory.sym_of_lbIso_pull_hom _ _ _ gen₉.hom hgen₉ _ _ A₉.isLB (pull_isLB hL₉ _) A₉.sym hA₉'
  haveI : IsNoetherianRing R₉ := hρ.1.1
  haveI : IsIntegrallyClosed R₉ := hρ.1.2.2.1
  obtain ⟨P, hP⟩ := GlobalTheory.CubSymPkg.exists_cp_of_generic_sym R₉ G₉ hG₉ hprop _ hL₉ hsym
  obtain ⟨β₂, hsq, hE⟩ := exists_square_extLam hρ.2.1 hβ hκ₉ _ PP hN hPP
  refine ⟨R₉, i1, i2, i3, ρ₄.comp ρ₃, G₉, i4, i5, β₄ ≫ β₃, β₂, P, A₉, gen₉, hρ, hβ, hsq, hG₉, ?_, ?_, hgen₉, ?_⟩
  · rw [hP]
    exact lbIso_lam_of_extLam R₉ G₉ hG₉ _ _ _ hL₉ (pull_isLB hN _) hL₉g.symm hE
  · refine evenOn_of_trait_unif R hR G hG A gen hgen W φ GW βW DW AW UW κ hW hφi hφl hGW hκ hUW R₉ _ G₉ _ _ P hρ hβ hκ₉
      ?_ X hTQ
    rw [hP]; exact hL₉g
  · rw [hP]; exact hA₉'

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeTranslatePolarisationBundle
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Hecke

theorem exists_pol_translate : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (act' : OActN D.O A') (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover (GlobalTheory.UPel.HT.Hecke.heckeSub o g N) (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → ∃ P' : LB (G2 A').left, P'.IsLB ∧ (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) ∧ (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) ∧ LBIso P' (P'.pull (lift (snd A' A') (fst A' A')).left) ∧ Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) ∧ (∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x ^ e = 1) ∧ (∀ c' : D.O, LBIso (P'.pull (lift (fst A' A' ≫ act'.act c') (snd A' A')).left) (P'.pull (lift (fst A' A') (snd A' A' ≫ act'.act (D.star c').unop)).left)) ∧ LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) := by
  intro p _ D R _ b g c k N hc hk hN hNp hEF hg hck S s o A' _ _ act' ψ hA' hψ hG hact
  obtain ⟨P₀, hP₀, w₀⟩ := GlobalTheory.T.exists_descent_bundle_power_hecke_quotient' p D R b g c k N hc hk hN hNp hEF hg hck S s o A' ψ hA' hψ hG
  obtain ⟨P', hP', r1, r2, w⟩ := GlobalTheory.T.exists_birigidified_bundle_of_descent p D R b (N * k) S s o A' ψ hψ _ P₀ hP₀ w₀
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.coprime_zero_left _ |>.1 hk)
  have hk2 : 0 < k ^ 2 := by positivity
  have hc0 : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; rw [zero_dvd_iff] at hck; omega)
  have hm1 : 1 ≤ k ^ 2 / c := Nat.div_pos (Nat.le_of_dvd hk2 hck) hc0
  have hmp : (k ^ 2 / c).Coprime p :=
    Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hck) (hk.pow_left 2)
  exact ⟨P', hP', r1, r2,
    _root_.GlobalTheory.HeckeSym.descended_symm p D R b (N * k) S s o A' ψ _ hA' hψ hG _ P' hP' w r1 r2,
    _root_.GlobalTheory.HeckeAmple.relAmple_diag_of_galois p D R b (N * k) S s o A' ψ _ hA' hψ hG _ hm1 P' hP' w,
    _root_.GlobalTheory.UPel.HT.Hecke.kernel_descent p D R b (N * k) S s o A' ψ _ hA' hψ hG _ hmp P' hP' w,
    _root_.GlobalTheory.UPel.HT.Hecke.rosati_of_descent p D R b (N * k) S s o A' act' ψ _ hA' hψ hG hact _ P' hP' w r1 r2, w⟩

end GlobalTheory.UPel.HT.Hecke
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerAbelianLocusChartRingStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kodairaSpencer_abelianLocus_chartRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (DV : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)), ∃ Θ₁, IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (fun a => spMap (dualMap (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) ≫ (tv (v' a)).left) ⇑DV Θ₁ := by
  first | exact @GlobalTheory.KSAbLocus.exists_isKS_abLocus | exact GlobalTheory.KSAbLocus.exists_isKS_abLocus | (intros; apply GlobalTheory.KSAbLocus.exists_isKS_abLocus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledCoverUnitaryPELTypeFiniteExtStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_labelledCover_unitaryPELType_finiteExt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (D : DegData R (maximalIdeal R)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), Nontrivial D.toPre.X → PelOK Dm D.toPre o → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D' : DegData R' (maximalIdeal R')), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D'.toPre) ∧ Nonempty (LabCover D') := by
  first | exact @GlobalTheory.Mum.exists_labCover_of_pelOK | exact GlobalTheory.Mum.exists_labCover_of_pelOK | (intros; apply GlobalTheory.Mum.exists_labCover_of_pelOK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelKilledCharOfTorusLabelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_killed_char_of_torus_label : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ, χ ^ (X₁.S.r * X₁.S.N) = 1 ∧ (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) := by
  first | exact @GlobalTheory.GSep.TorLabel.exists_torus_char | exact GlobalTheory.GSep.TorLabel.exists_torus_char | (intros; apply GlobalTheory.GSep.TorLabel.exists_torus_char <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorsSymbolZeroTorsionPointsHorizontal
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

namespace GlobalTheory.HeatPts

theorem exists_horizontal_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ y : P.D.toPre.X, ∃ c' : Sp (DualNumber k) ⟶ B'.left, c' ≫ B'.hom = 𝟙 _ ∧ c' ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left := by
  intro E _ _ _ H k _ _ m d t P gam hM hli hab Y n' v' dd hdd D q hD h hB hH hΘ ρ hρ B' _ π₁ π₂ h₁ h₂ h12 y
  have hw : (spMap ρ ≫ (P.D.toPre.c y).left) ≫ P.D.toPre.P.A.hom = 𝟙 _ ≫ spMap ρ := by
    rw [Category.assoc, Over.w]; simp
  refine ⟨h₁.1.lift (spMap ρ ≫ (P.D.toPre.c y).left) (𝟙 _) hw, h₁.1.lift_snd _ _ _, h₁.1.lift_fst _ _ _, ?_⟩
  exact GlobalTheory.T.translation_horizontal_of_commuting_heatOperators E H k m d t P gam hM hli hab Y n' v' dd hdd D q hD h hB hH hΘ ρ hρ B' inferInstance π₁ π₂ h₁ h₂ h12 y _
    (h₁.1.lift_snd _ _ _) (h₁.1.lift_fst _ _ _)

end GlobalTheory.HeatPts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomotopyInvarianceTateTwistStrictlyHenselianStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homotopyInvariance_tateTwist_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Eqv _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) := by
  first | (exact @GlobalTheory.homotopyInvariance_strictlyHenselian) | (exact GlobalTheory.homotopyInvariance_strictlyHenselian) | (intros; apply GlobalTheory.homotopyInvariance_strictlyHenselian  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentKummerCupProductBijectiveStrictlyHenseliaStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentKummerCupProduct_bijective_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Function.Bijective (gmPhi q A i) := by
  first | (exact @GlobalTheory.EtC.gmPhi_bijective) | (exact GlobalTheory.EtC.gmPhi_bijective) | (intros; apply GlobalTheory.EtC.gmPhi_bijective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearChangeEulerProduct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic

namespace GlobalTheory.DualHomPull

theorem exists_dual_hom : ∀ (Y : Scheme.{0}) (A G : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G] (χ : A ⟶ G) (P'' : LB (G2 G).left), IsAbelianScheme A → IsAbelianScheme G → IsMonHom χ → P''.IsLB → (∃ t : (P''.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P''.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → ∃ (D : Over Y) (_ : GrpObj D) (Q : LB (A ⊗ D).left) (h : A ⟶ D), IsAbelianScheme D ∧ GlobalTheory.AbDual.IsDual A D Q ∧ GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) ∧ IsMonHom h ∧ LBIso (P''.pull (χ ⊗ₘ χ).left) (Q.pull (lift (fst A A) (snd A A ≫ h)).left) := by
  intro Y A G _ _ _ _ χ P'' hA hG hχ hP h₁ h₂
  obtain ⟨D, _, Q, hD, -, q, q'⟩ := GlobalTheory.dualAbelianScheme Y A hA
  obtain ⟨a₁, a₂⟩ := GlobalTheory.CubeAxes.additive_of_triv_axes hG hP h₁ h₂
  have eχ : χ ⊗ₘ χ = lift (fst A A ≫ χ) (snd A A ≫ χ) := by ext <;> simp
  rw [eχ]
  have hE : (ev P'' (fst A A ≫ χ) (snd A A ≫ χ)).IsLB := pull_isLB hP _
  have k : ∀ {T : Over Y} (a t : T ⟶ A), evc hE a t = evc hP (a ≫ χ) (t ≫ χ) := fun a t ↦ by
    rw [evc_ev hP _ _ hE, lift_fst_assoc, lift_snd_assoc]
  have b₁ : IsAdditive (ev P'' (fst A A ≫ χ) (snd A A ≫ χ)) := (isAdditive_iff hE).2 fun T a a' t ↦ by
    haveI := hχ
    rw [k, k, k, MonObj.mul_comp]
    exact (isAdditive_iff hP).1 a₁ _ _ _ _
  have b₂ : IsAdditive (swap (ev P'' (fst A A ≫ χ) (snd A A ≫ χ))) :=
    (GlobalTheory.BirigidLift.isAdditive_swap_iff hE).2 fun T a t t' ↦ by
      haveI := hχ
      rw [k, k, k, MonObj.mul_comp]
      exact (GlobalTheory.BirigidLift.isAdditive_swap_iff hP).1 a₂ _ _ _ _
  obtain ⟨x, hx, e⟩ := GlobalTheory.BirigidLift.exists_hom q q'.additive hE b₁ b₂
  exact ⟨D, inferInstance, Q, x, hD, q, q'.additive, hx, (cls_eq_iff hE (pull_isLB q.isLB _)).1 e⟩

end GlobalTheory.DualHomPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalInjectionsAgreeCanonicalFamilyCoordinatesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localInjections_agree_canonicalFamily_coordinates : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], GlobalTheory.Mum.Base R' → ∀ θ₁ θ₂ : R →+* R', Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∀ κ₁ κ₂ : Sp (FractionRing R') ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK R' ≫ spMap θ₁ → κ₂ ≫ jK R = jK R' ≫ spMap θ₂ → κ₁ ≫ C.y = κ₂ ≫ C.y → ∀ k, θ₁ (Cn.ψ (MvPolynomial.X k)) = θ₂ (Cn.ψ (MvPolynomial.X k)) := by
  first | exact @GlobalTheory.UInj.coords_eq | exact GlobalTheory.UInj.coords_eq | (intros; apply GlobalTheory.UInj.coords_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareDeRhamDualityAbelianScheme
section
namespace GlobalTheory

theorem poincareDeRhamDuality : GlobalTheory.Published.PoincareDeRhamDuality :=
  GlobalTheory.T.poincareDeRhamDuality_of_hodgeDeRham_dual _root_.GlobalTheory.AbCoh.abelianHodgeDeRham _root_.GlobalTheory.dualAbelianScheme

end GlobalTheory
end

