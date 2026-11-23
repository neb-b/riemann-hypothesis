module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2477
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2219
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0590
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2279
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2331
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsTauCoord
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.E8Order

open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

variable {R : Type} [CommRing R] [IsDomain R]

abbrev unitsR (R : Type) [CommRing R] [IsDomain R] : Subgroup (FractionRing R)ˣ :=
  (Units.map (algebraMap R (FractionRing R)).toMonoidHom).range

abbrev QR (R : Type) [CommRing R] [IsDomain R] := (FractionRing R)ˣ ⧸ unitsR R

abbrev cls : (FractionRing R)ˣ →* QR R := QuotientGroup.mk' (unitsR R)

theorem cls_eq_iff (x y : (FractionRing R)ˣ) :
    cls x = cls y ↔ ∃ u : Rˣ, (x : FractionRing R) = (y : FractionRing R) * algebraMap R (FractionRing R) u := by
  rw [eq_comm, QuotientGroup.mk'_eq_mk']
  constructor
  · rintro ⟨z, ⟨u, rfl⟩, hz⟩
    exact ⟨u, by rw [← hz]; rfl⟩
  · rintro ⟨u, hu⟩
    exact ⟨_, ⟨u, rfl⟩, Units.ext (by rw [hu]; rfl)⟩

theorem cls_unit (u : Rˣ) : cls (Units.map (algebraMap R (FractionRing R)).toMonoidHom u) = 1 :=
  (QuotientGroup.eq_one_iff _).2 ⟨u, rfl⟩

variable [IsLocalRing R]

def tq (D : DegPre R) (a b : D.X) : QR R :=
  cls (psiCoord D (a + b)) * (cls (psiCoord D a))⁻¹ * (cls (psiCoord D b))⁻¹

theorem cls_tauCoord {D : DegPre R} {a b : D.X} {x : (FractionRing R)ˣ} (hx : IsTauCoord D a b x) :
    cls x = tq D a b := by
  obtain ⟨u, hu⟩ := GlobalTheory.TauCoordQuot.main R D a b x _ _ _ hx (psiCoord_spec D (a + b)) (psiCoord_spec D a)
    (psiCoord_spec D b)
  have : x = Units.map (algebraMap R (FractionRing R)).toMonoidHom u *
      (psiCoord D (a + b) * (psiCoord D a)⁻¹ * (psiCoord D b)⁻¹) := by
    ext; rw [hu]; simp <;> ring
  rw [this, map_mul, cls_unit, _root_.one_mul, tq, map_mul, map_mul, map_inv, map_inv]

theorem tq_symm (D : DegPre R) (a b : D.X) : tq D a b = tq D b a := by
  simp only [tq, add_comm a b]; exact mul_right_comm _ _ _

theorem tq_add_left (D : DegPre R) (hB : D.TauBimult) (a z b : D.X) : tq D (a + z) b = tq D a b * tq D z b := by
  obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D a b
  obtain ⟨x', hx'⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D z b
  obtain ⟨x'', hx''⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D (a + (1 : ℕ) • z) b
  obtain ⟨u, hu⟩ := GlobalTheory.TauShift.main R D hB a z b 1 x x' x'' hx hx' hx''
  rw [one_smul] at hx''
  rw [← cls_tauCoord hx'', ← cls_tauCoord hx, ← cls_tauCoord hx', hu, map_mul, cls_unit, _root_.one_mul, pow_one, map_mul]

def tqHom (D : DegPre R) (hB : D.TauBimult) (a : D.X) : D.X →+ Additive (QR R) :=
  AddMonoidHom.mk' (fun b => Additive.ofMul (tq D a b)) fun b b' => by
    rw [tq_symm D a (b + b'), tq_add_left D hB, tq_symm D b a, tq_symm D b' a]; rfl

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsDiscreteValuationRing R → ∀ (D D' : DegPre R), D'.TauBimult → D'.PsiEven → D.TauBimult → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (ϖ : R) (β : LinearMap.BilinForm ℤ D.X), (∀ a b, β a b = β b a) → (∀ a, 0 ≤ β a a) → (∀ a b' (x : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D a b' x → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * algebraMap R (FractionRing R) ϖ ^ (β a b')) → ∀ (c : Fin 8 → (D.X →+ D'.X)) (e : D'.X ≃+ (Fin 8 → D.X)), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → (∀ v a' b (x x' : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D (e a' v) b x → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D' a' (c v b) x' → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * (x' : FractionRing R)) → ∀ y r, PsiCoord D' y r → 0 ≤ qW W β (e y) ∧ Associated r (ϖ ^ (qW W β (e y)).toNat) := by
  intro R _ _ _ hR D D' hB' hE' hB W hW ϖ β hs hp hτ c e hsum hcomp y r hr
  haveI := hR
  have hq : 0 ≤ qW W β (e y) := GlobalTheory.Poinc.qW_nonneg_of_posW W hW.1 β hs hp (e y)
  refine ⟨hq, ?_⟩
  obtain ⟨s, hsd⟩ : ∃ s, s = e y := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : Fin 8 → D.X, t = fun v => ∑ u, (W + W.transpose) v u • s u := ⟨_, rfl⟩
  rw [← hsd] at hq ⊢
  have hsum2 : ∑ v, β (s v) (-(t v)) = -(2 * qW W β s) := by
    subst ht
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_neg, map_sum, map_zsmul, smul_eq_mul, Finset.sum_neg_distrib, neg_inj]
    simp only [Matrix.add_apply, Matrix.transpose_apply, add_mul, Finset.sum_add_distrib, qW, two_mul]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by rw [hs]
  have h1 : ∑ v, c v (t v) = y := by rw [ht, hsd]; exact hsum y
  have hy : -y = ∑ v, c v (-(t v)) := by
    rw [← h1]; simp only [map_neg, Finset.sum_neg_distrib]
  obtain ⟨x', hx'⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D' y (-y)
  have hcl : cls x' = tq D' y (-y) := cls_tauCoord hx'
  have hterm : ∀ v, tq D' y (c v (-(t v))) = tq D (s v) (-(t v)) := by
    intro v
    obtain ⟨a, ha⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D (e y v) (-(t v))
    obtain ⟨b, hb⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D' y (c v (-(t v)))
    obtain ⟨u, hu⟩ := hcomp v y (-(t v)) a b ha hb
    rw [← cls_tauCoord hb, hsd, ← cls_tauCoord ha]
    exact ((cls_eq_iff _ _).2 ⟨u, by rw [hu, mul_comm]⟩).symm
  have hprod : Additive.ofMul (tq D' y (-y)) = ∑ v, Additive.ofMul (tq D (s v) (-(t v))) := by
    have := map_sum (tqHom D' hB' y) (fun v => c v (-(t v))) Finset.univ
    rw [← hy] at this
    refine this.trans ?_
    exact Finset.sum_congr rfl fun v _ => congrArg Additive.ofMul (hterm v)
  obtain ⟨w0, hw0⟩ := GlobalTheory.PsiFromTauEven.tauCoord_mul_sq R D' hB' hE' y r hr x' hx'
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_pow two_ne_zero, mul_zero] at hw0
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 w0.ne_zero hw0.symm
  let ru : (FractionRing R)ˣ := toUnitK r hr0
  have hru : x' * ru ^ 2 = Units.map (algebraMap R (FractionRing R)).toMonoidHom w0 := by
    ext; simp [ru, toUnitK, hw0]
  have hcr : cls ru ^ 2 = (cls x')⁻¹ := by
    have := congrArg cls hru
    rw [map_mul, map_pow, cls_unit] at this
    exact eq_inv_of_mul_eq_one_right this
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hq
  rw [hn, Int.toNat_natCast]
  have final : ∀ ρ : (FractionRing R)ˣ, (ρ : FractionRing R) = algebraMap R (FractionRing R) (ϖ ^ n) →
      cls ru ^ 2 = cls ρ ^ 2 → Associated r (ϖ ^ n) := by
    intro ρ hρ h
    rw [← map_pow, ← map_pow] at h
    obtain ⟨u, hu⟩ := (cls_eq_iff _ _).1 h
    simp only [Units.val_pow_eq_pow_val, hρ, ru, toUnitK, Units.val_mk0, ← map_pow, ← map_mul] at hu
    have hsq : Associated ((ϖ ^ n) ^ 2) (r ^ 2) := ⟨u, (IsFractionRing.injective R (FractionRing R) hu).symm⟩
    exact (associated_of_dvd_dvd ((IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 hsq.dvd)
      ((IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 hsq.symm.dvd)).symm
  by_cases hϖ : ϖ = 0
  · have hβ0 : ∀ a b, β a b = 0 := by
      intro a b
      obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D a b
      obtain ⟨u, hu⟩ := hτ a b x hx
      by_contra h
      rw [hϖ, map_zero, zero_zpow _ h, mul_zero] at hu
      exact x.ne_zero hu
    have hq0 : qW W β s = 0 := by simp [qW, hβ0]
    have htq : ∀ a b, tq D a b = 1 := by
      intro a b
      obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D a b
      obtain ⟨u, hu⟩ := hτ a b x hx
      rw [← cls_tauCoord hx]
      have : x = Units.map (algebraMap R (FractionRing R)).toMonoidHom u := by
        ext; rw [hu, hβ0, zpow_zero, _root_.mul_one]; rfl
      rw [this, cls_unit]
    have h1' : tq D' y (-y) = 1 := by
      apply Additive.ofMul.injective
      rw [hprod]; simp [htq]
    have hn0 : n = 0 := by omega
    subst hn0
    refine final 1 (by simp) ?_
    rw [hcr, hcl, h1']; simp
  · let ϖu : (FractionRing R)ˣ := toUnitK ϖ hϖ
    have htq : ∀ a b, tq D a b = cls ϖu ^ β a b := by
      intro a b
      obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D a b
      obtain ⟨u, hu⟩ := hτ a b x hx
      rw [← cls_tauCoord hx, ← map_zpow]
      exact (cls_eq_iff _ _).2 ⟨u, by rw [hu, Units.val_zpow_eq_zpow_val]; simp [ϖu, toUnitK, mul_comm]⟩
    have hx'cl : cls x' = cls ϖu ^ (-(2 * qW W β s)) := by
      rw [hcl]; apply Additive.ofMul.injective; rw [hprod]
      simp only [htq, ofMul_zpow]
      rw [← Finset.sum_smul, hsum2]
    refine final (ϖu ^ n) (by simp [ϖu, toUnitK]) ?_
    rw [hcr, hx'cl, hn, map_pow, ← zpow_neg, neg_neg, show (2 * (n : ℤ)) = ((n * 2 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast, pow_mul]

end GlobalTheory.Poinc.E8Order
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpFormEqZeroOfTangent
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LieInjField


open GlobalTheory.CechDR in
theorem cmpForm_surjective (hC : GlobalTheory.Published.CrystallineSmoothLift) (hH : GlobalTheory.Published.AbelianHodgeDeRham)
    (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hab : IsAbelianScheme A)
    (hdim : SmoothOfRelativeDimension g A.hom) : Function.Surjective (cmpForm (A.hom ≫ 𝟙 (Sp R))) := by
  have hsm : Smooth (A.hom ≫ 𝟙 (Sp R)) := by haveI := hab.smooth; infer_instance
  have hsep : IsSeparated (A.hom ≫ 𝟙 (Sp R)) := by haveI := hab.proper; infer_instance
  have hqc : QuasiCompact (A.hom ≫ 𝟙 (Sp R)) := by haveI := hab.proper; infer_instance
  have hcmp := (cechDeRham_comparison_bijective_cup_smooth hC R A.left _ hsm hsep hqc).1
  have hcl : Function.Injective (clForm (A.hom ≫ 𝟙 (Sp R))) := (hH R A g hab hdim).2.2.2.2.1.2.1
  intro ω
  obtain ⟨c, hc⟩ := hcmp.2 (clForm _ ω)
  have hF : clForm _ ω ∈ CechHodgeFiltration (A.hom ≫ 𝟙 (Sp R)) := by rw [cechHodgeFiltration_eq_range]; exact ⟨ω, rfl⟩
  have h1 : c ∈ F1 (A.hom ≫ 𝟙 (Sp R)) := by
    change toH1O _ c = 0
    apply _root_.GlobalTheory.CechDR.cmpO_injective R A.left _
    rw [← structureSheaf_comparison_comm, map_zero, hc]
    exact hF
  rw [hodgeFiltration_eq_range] at h1
  obtain ⟨f, rfl⟩ := h1
  rw [comparison_formClass] at hc
  exact ⟨f, hcl hc⟩

theorem cmpForm_eq_zero_of_tangent (hC : GlobalTheory.Published.CrystallineSmoothLift) (hH : GlobalTheory.Published.AbelianHodgeDeRham)
    (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B] (g : ℕ) (hab : IsAbelianScheme B)
    (hdim : SmoothOfRelativeDimension g B.hom) (f : Form (B.hom ≫ 𝟙 (Sp K)))
    (hf : ∀ v : epsR K ⟶ B, IsTangent v → tanVal v f = 0) :
    GlobalTheory.CechDR.cmpForm (B.hom ≫ 𝟙 (Sp K)) f = 0 := by
  haveI := hab.comm
  have hsm : Smooth B.hom := hab.smooth
  obtain ⟨y, hy⟩ := _root_.GlobalTheory.LieField.exists_isLieBasis_field K B g hdim
  refine _root_.GlobalTheory.PtVanish.cmpForm_eq_zero_of_tanVal K B hsm f fun L _ σ ↦ ?_
  letI : GrpObj ((Over.pullback (spMap σ)).obj B) := Functor.grpObjObj
  have hG := isGrpPullback_pullback B (spMap σ)
  have hab' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hab hG
  haveI := hab'.comm
  have hdim' : SmoothOfRelativeDimension g ((Over.pullback (spMap σ)).obj B).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hG.1 hdim
  have m : IsMor (dp0 K) (B.hom ≫ 𝟙 (Sp K)) (dp0 L) (((Over.pullback (spMap σ)).obj B).hom ≫ 𝟙 (Sp L)) σ
      (Limits.pullback.fst B.hom (spMap σ)) := IsMor.of_dividedPowersZeroIdeal _ (by simpa using hG.1.w)
  refine ⟨_, _, m, hG.1, fun u ↦ ?_⟩
  let c : epsR L ⟶ (Over.pullback (spMap σ)).obj B := GlobalTheory.GrpTangent.epsScale 0 ≫ u
  have hc : tanVal c (m.pullForm f) = 0 := by
    rw [tanVal_epsScale, zero_mul]
  have ht : IsTangent (c⁻¹ * u) := by
    rw [GlobalTheory.GrpTangent.isTangent_iff, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
      GlobalTheory.GrpTangent.epsZero_epsScale, inv_mul_cancel]
  have e : u = c * (c⁻¹ * u) := (mul_inv_cancel_left c u).symm
  rw [e, GlobalTheory.T.crystallineForm_tangentValue_mul_abelianScheme hC hH L _ g hab' hdim', hc, zero_add]
  exact _root_.GlobalTheory.LieDual.tanVal_pullForm_eq_zero_of_lieBasis K B hsm g y hy f (fun i ↦ hf _ (hy.1 i)) L σ _ _ hG m _ ht

def lieVal (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] :
    Serre.Lie (Serre.intAct B) →ₗ[K] Module.Dual K (Form (B.hom ≫ 𝟙 (Sp K))) where
  toFun v := tanVal v.hom
  map_add' v w := LinearMap.ext fun f ↦ tanVal_mul v.isTangent w.isTangent f
  map_smul' r v := LinearMap.ext fun f ↦ tanVal_epsScale r v.hom f

theorem eq_of_tanVal_eq : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → ∀ (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∀ v w : epsR K ⟶ B, IsTangent v → IsTangent w → (∀ f : Form (B.hom ≫ 𝟙 (Sp K)), tanVal v f = tanVal w f) → v = w := by
  intro hC hH K _ B _ g hab hdim v w hv hw h
  haveI := hab.comm
  obtain ⟨y, hy⟩ := _root_.GlobalTheory.LieField.exists_isLieBasis_field K B g hdim
  let b := Serre.Lie.basis (Serre.intAct B) hy
  haveI := Module.Finite.of_basis b
  have hL : Module.finrank K (Serre.Lie (Serre.intAct B)) = g := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have htop : GlobalTheory.CechDR.ClosedForm (B.hom ≫ 𝟙 (Sp K)) = ⊤ := (hH K B g hab hdim).2.2.2.2.1.1
  obtain ⟨hfin, -, hrk⟩ : Module.Finite K (GlobalTheory.CechDR.GlobForm (B.hom ≫ 𝟙 (Sp K))) ∧
      Module.Projective K (GlobalTheory.CechDR.GlobForm (B.hom ≫ 𝟙 (Sp K))) ∧
      ∀ p : PrimeSpectrum K, Module.rankAtStalk (GlobalTheory.CechDR.GlobForm (B.hom ≫ 𝟙 (Sp K))) p = g :=
    (hH K B g hab hdim).2.2.1
  have hG : Module.finrank K (GlobalTheory.CechDR.GlobForm (B.hom ≫ 𝟙 (Sp K))) = g := by
    have h' := hrk (IsLocalRing.closedPoint K)
    rwa [Module.rankAtStalk_eq_finrank_of_free] at h'
  let eC : GlobalTheory.CechDR.ClosedForm (B.hom ≫ 𝟙 (Sp K)) ≃ₗ[K] GlobalTheory.CechDR.GlobForm (B.hom ≫ 𝟙 (Sp K)) := LinearEquiv.ofTop _ htop
  haveI : Module.Finite K (GlobalTheory.CechDR.ClosedForm (B.hom ≫ 𝟙 (Sp K))) := Module.Finite.equiv eC.symm
  have hC' : Module.finrank K (GlobalTheory.CechDR.ClosedForm (B.hom ≫ 𝟙 (Sp K))) = g := by rw [eC.finrank_eq, hG]
  let c := GlobalTheory.CechDR.cmpForm (B.hom ≫ 𝟙 (Sp K))
  have hcs : Function.Surjective c := cmpForm_surjective hC hH K B g hab hdim
  let P := lieVal K B
  have hker : LinearMap.ker c ≤ LinearMap.ker P.flip := fun f hf ↦
    LinearMap.ext fun u ↦ _root_.GlobalTheory.TanVanish.tanVal_eq_zero_of_cmpForm_eq_zero K B u.hom f hf
  let T : GlobalTheory.CechDR.ClosedForm (B.hom ≫ 𝟙 (Sp K)) →ₗ[K] Module.Dual K (Serre.Lie (Serre.intAct B)) :=
    (LinearMap.ker c).liftQ P.flip hker ∘ₗ (c.quotKerEquivOfSurjective hcs).symm.toLinearMap
  have hT : ∀ f, T (c f) = P.flip f := fun f ↦ by
    have : (c.quotKerEquivOfSurjective hcs).symm (c f) = Submodule.Quotient.mk f :=
      (c.quotKerEquivOfSurjective hcs).symm_apply_eq.2 rfl
    change (LinearMap.ker c).liftQ P.flip hker ((c.quotKerEquivOfSurjective hcs).symm (c f)) = _
    rw [this]; rfl
  have hTi : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro ω hω
    obtain ⟨f, rfl⟩ := hcs ω
    rw [LinearMap.mem_ker, hT] at hω
    exact cmpForm_eq_zero_of_tangent hC hH K B g hab hdim f fun v hv ↦
      LinearMap.congr_fun hω (Serre.Lie.mk (Serre.intAct B) v hv)
  have hTs : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Subspace.dual_finrank_eq, hL, hC'])).1 hTi
  let V := Serre.Lie.mk (Serre.intAct B) v hv
  let W := Serre.Lie.mk (Serre.intAct B) w hw
  have hsurj : Function.Surjective (T ∘ₗ c) := hTs.comp hcs
  have key : ∀ φ : Module.Dual K (Serre.Lie (Serre.intAct B)), φ V = φ W := fun φ ↦ by
    obtain ⟨f, rfl⟩ := hsurj φ
    rw [LinearMap.comp_apply, hT]
    exact h f
  have hVW : V - W = 0 :=
    (Module.forall_dual_apply_eq_zero_iff K (V - W)).1 fun φ ↦ by rw [map_sub, key φ, sub_self]
  exact congrArg Serre.Lie.hom (sub_eq_zero.1 hVW)

end GlobalTheory.LieInjField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientGermsZeroFiniteFreeBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FreeCoord

open GlobalTheory.BoxIndep TensorProduct

theorem eq_zero_of_germOf_max {B : CommRingCat.{0}} (a : B)
    (h : ∀ z : Spec B, z.asIdeal.IsMaximal → germOf (𝟙 (Spec B)) z a = 0) : a = 0 := by
  have : (Ideal.span {a}).annihilator = ⊤ := by
    by_contra hne
    obtain ⟨p, hp, hI⟩ := Ideal.exists_le_maximal _ hne
    let z : Spec B := ⟨p, hp.isPrime⟩
    have h1 : algebraMap B ((Spec.structureSheaf B).presheaf.stalk z) a = 0 := h z hp
    have := StructureSheaf.IsLocalization.to_stalk B z
    obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff z.asIdeal.primeCompl _ _).1 h1
    exact c.2 (hI (Submodule.mem_annihilator_span_singleton _ _ |>.2 hc))
  have h1 : (1 : B) ∈ (Ideal.span {a}).annihilator := this ▸ Submodule.mem_top
  exact (one_smul B _).symm.trans ((Submodule.mem_annihilator_span_singleton _ _).1 h1)

theorem gs_comp' {Z Y X : Scheme.{0}} (r : Z ⟶ Y) (F : Y ⟶ X) (z : Z) (U : X.Opens) (h : F (r z) ∈ U) (f : Γ(X, U)) :
    gs (r ≫ F) z U f = (r.stalkMap z).hom (gs F (r z) U f) := by
  rw [← gs_pull r F z U h, gs_stalkMap r z _ h, gs_pull (𝟙 _) F (r z) U h, Category.id_comp]

theorem germ_eq_zero : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁), (∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) → ∀ (X : Scheme.{0}) (f : X ⟶ Sp R) (U : X.Opens) (a : Fin d → Γ(X, U)) (x : X), x ∈ U → (∀ z : (pullback f (spMap ρ₁) : Scheme.{0}), (pullback.fst f (spMap ρ₁)) z = x → ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z U (a l) = 0) → ∀ l, gs (𝟙 X) x U (a l) = 0 := by
  intro R R₁ _ _ ρ₁ d b hb X f U a x hx h
  let _ : Algebra R R₁ := ρ₁.toAlgebra
  let A : CommRingCat.{0} := X.presheaf.stalk x
  let _ : Algebra R A := (germOf (B := CommRingCat.of R) f x).toAlgebra
  have hli : LinearIndependent R b := Fintype.linearIndependent_iff.2 fun c hc =>
    congrFun ((hb 0).unique (y₁ := c) (y₂ := 0) (by simp only [Algebra.smul_def] at hc; exact hc.symm) (by simp))
  have hsp : ⊤ ≤ Submodule.span R (Set.range b) := fun r _ => by
    obtain ⟨c, hc, -⟩ := hb r
    rw [hc]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ (c l) (Submodule.subset_span ⟨l, rfl⟩)
  let β := Module.Basis.mk hli hsp
  have : Module.Finite R R₁ := Module.Finite.of_basis β
  let B : CommRingCat.{0} := CommRingCat.of (A ⊗[R] R₁)
  let iA : A ⟶ B := CommRingCat.ofHom (algebraMap A (A ⊗[R] R₁))
  let iR : CommRingCat.of R₁ ⟶ B := CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := R₁)).toRingHom
  have w : (Spec.map iA ≫ X.fromSpecStalk x) ≫ f = Spec.map iR ≫ spMap ρ₁ := by
    rw [Category.assoc, fromSpecStalk_comp (B := CommRingCat.of R)]
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_comp _ _))
    ext r
    exact (IsScalarTower.algebraMap_apply R A (A ⊗[R] R₁) r).symm.trans
      ((Algebra.TensorProduct.includeRight (R := R) (A := A) (B := R₁)).commutes r).symm
  let r : Spec B ⟶ pullback f (spMap ρ₁) := pullback.lift _ _ w
  have r1 : r ≫ pullback.fst f (spMap ρ₁) = Spec.map iA ≫ X.fromSpecStalk x := pullback.lift_fst _ _ _
  have r2 : r ≫ pullback.snd f (spMap ρ₁) = Spec.map iR := pullback.lift_snd _ _ _
  have key : (∑ l, iR.hom (b l) * iA.hom (gs (𝟙 X) x U (a l)) : B) = 0 := by
    refine eq_zero_of_germOf_max _ fun z hz => ?_
    letI : z.asIdeal.IsMaximal := hz
    have hm : (z.asIdeal.comap (algebraMap A (A ⊗[R] R₁))).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) z.asIdeal
    have hc : Spec.map iA z = closedPoint A := PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hm)
    have hzx : pullback.fst f (spMap ρ₁) (r z) = x := by
      have : (r ≫ pullback.fst f (spMap ρ₁)) z = X.fromSpecStalk x (Spec.map iA z) := by rw [r1]; rfl
      rw [hc, Scheme.fromSpecStalk_closedPoint] at this
      exact this
    have e := congrArg (r.stalkMap z).hom (h (r z) hzx)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum] at e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, map_mul, ← gs_comp' r _ z ⊤ trivial, ← gs_comp' r _ z U (hzx ▸ hx), r1, r2,
      gs_fromSpecStalk x hx, ← germOf_apply, ← germOf_map, ← germOf_map, Category.id_comp, Category.id_comp]
  have hli' := (Algebra.TensorProduct.basis A β).linearIndependent
  refine Fintype.linearIndependent_iff.1 hli' (fun l => gs (𝟙 X) x U (a l)) ?_
  refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) key
  rw [Algebra.smul_def, _root_.mul_comm, Algebra.TensorProduct.basis_apply, Module.Basis.mk_apply]
  rfl

end GlobalTheory.Mum.FreeCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsOverRingHomIsHomeomorphBaseChange
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.Mix

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX isPushout_sections)

theorem isHomeomorph_bcPt (k K : Type) [CommRing k] [CommRing K] (ρ : k →+* K) (X G : Scheme.{0})
    (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap ρ)) (τ : K →+* ℂ) :
    IsHomeomorph (bcPt hp.w τ) := by
  let E : CxPts q τ ≃ CxPts p (τ.comp ρ) := Equiv.ofBijective (bcPt hp.w τ) (CxPts.bijective_bcMap hp τ)
  have hm : ∀ z, (bcPt hp.w τ z).1 = z.1 ≫ j := fun _ => rfl
  have hE : ∀ y, bcPt hp.w τ (E.symm y) = y := E.apply_symm_apply
  have hc : Continuous E.symm := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    obtain ⟨U, hyU⟩ := CxPts.exists_mem_ptsIn (iSup_affineOpens_eq_top X) y
    have hU : IsAffineOpen U.1 := U.2
    have hW : IsAffineOpen (j ⁻¹ᵁ U.1 ⊓ q ⁻¹ᵁ ⊤) := by
      rw [show j ⁻¹ᵁ U.1 ⊓ q ⁻¹ᵁ ⊤ = j ⁻¹ᵁ U.1 from inf_top_eq _]
      exact GlobalTheory.TopForm.isAffineOpen_preimage_of_isPullback hp hU
    have hin : ∀ w ∈ ptsIn p (τ.comp ρ) U.1, E.symm w ∈ ptsIn q τ (j ⁻¹ᵁ U.1 ⊓ q ⁻¹ᵁ ⊤) := fun w hw =>
      mem_ptsIn_inf.2 ⟨(mem_ptsIn_preimage hm).2 (by rw [hE]; exact hw), mem_ptsIn_top⟩
    have hnb : ptsIn p (τ.comp ρ) U.1 ∈ 𝓝 y := (isOpen_ptsIn _).mem_nhds hyU
    have hev : ∀ᶠ w in 𝓝 y, E.symm w ∈ ptsIn q τ (j ⁻¹ᵁ U.1 ⊓ q ⁻¹ᵁ ⊤) := eventually_of_mem hnb hin
    letI := ρ.toAlgebra
    have hgen := CommRingCat.closure_range_union_range_eq_top_of_isPushout (isPushout_sections p q j hp U.1 hU)
    refine tendsto_subtype_rng.2 ((Points.tendsto_iff_of_generators hW (hin y hyU) hgen).2 ⟨hev, ?_⟩)
    rintro f (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · have e : ∀ w ∈ ptsIn p (τ.comp ρ) U.1, ev p (τ.comp ρ) U.1 a w =
          valR (E.symm w).1 _ ((j.appLE U.1 (j ⁻¹ᵁ U.1 ⊓ q ⁻¹ᵁ ⊤) inf_le_left).hom a) := fun w hw => by
        have := CxPts.ev_appLE_of_comp hm inf_le_left a (hin w hw)
        rw [hE] at this
        exact this.symm
      have h := ((continuousOn_ev a).continuousAt hnb).tendsto
      rw [e y hyU] at h
      exact h.congr' (eventually_of_mem hnb e)
    · have e : ∀ w ∈ ptsIn p (τ.comp ρ) U.1, τ b =
          valR (E.symm w).1 _ (algX q (j ⁻¹ᵁ U.1 ⊓ q ⁻¹ᵁ ⊤) b) := fun w hw => (ev_algX (hin w hw) b).symm
      have h : Tendsto (fun _ : CxPts p (τ.comp ρ) => τ b) (𝓝 y) (𝓝 (τ b)) := tendsto_const_nhds
      have h' := h.congr' (eventually_of_mem hnb e)
      rw [e y hyU] at h'
      exact h'
  exact (Homeomorph.mk E (continuous_bcPt hp.w τ) hc).isHomeomorph

end GlobalTheory.Mix
end

