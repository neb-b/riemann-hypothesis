module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2166
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PotentiallyKnownOfSameLambdaBundle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2164
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2172
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PowObjSmoothOfRelativeDimensionMul
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1906
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0553
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0602
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0550
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointwiseLineBundleGeneratorOfTrivialPullb
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PtExt

theorem le_pull_chart {X Y : Scheme.{0}} (L : LB X) (q : Y ⟶ X) {D : Type} [CommRing D] (x : Sp D ⟶ Y)
    (i : L.ι) (h : ⊤ ≤ (x ≫ q) ⁻¹ᵁ L.U i) : ⊤ ≤ x ⁻¹ᵁ (L.pull q).U (fun _ ↦ i) :=
  fun _ hp ↦ Set.mem_iInter.2 fun _ ↦ h hp

theorem evU_mul {Y : Scheme.{0}} {D : Type} [CommRing D] (x : Sp D ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (a b : Γ(Y, U)) : evU x U (a * b) = evU x U a * evU x U b := by
  simpa only [evU, dite_eq_left h] using map_mul (evalAt x U h) a b

theorem exists_isPtGen : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (L : LB X.left), L.IsLB →
    ∀ q : Y ⟶ X, GlobalTheory.AbLaw.Triv (L.pull q.left) → ∃ t, IsPtGen L q t := by
  intro R _ X Y L _ q hT
  obtain ⟨s, hs⟩ := hT
  refine ⟨fun E _ _ z i ↦ evU z.left ((L.pull q.left).U (fun _ ↦ i)) (s.s (fun _ ↦ i)).val, ?_, ?_, ?_⟩
  · intro E _ _ z i hi
    have hz := le_pull_chart L q.left z.left i hi
    simpa only [evU, dite_eq_left hz] using
      (s.s (fun _ ↦ i)).isUnit.map (evalAt z.left _ hz)
  · intro E _ _ E' _ _ ψ z i hi
    have hz := le_pull_chart L q.left z.left i hi
    exact evalSectionAtPointOrZero_specMap_comp _ E E' (ψ : E →+* E') z.left _ _ hz
  · intro E _ _ z i j hi hj
    have hzi := le_pull_chart L q.left z.left i hi
    have hzj := le_pull_chart L q.left z.left j hj
    have hV : ⊤ ≤ z.left ⁻¹ᵁ ((L.pull q.left).U (fun _ ↦ i) ⊓ (L.pull q.left).U (fun _ ↦ j)) :=
      fun p hp ↦ ⟨hzi hp, hzj hp⟩
    have hij : ⊤ ≤ (z.left ≫ q.left) ⁻¹ᵁ (L.U i ⊓ L.U j) := fun p hp ↦ ⟨hi hp, hj hp⟩
    have e := congrArg (fun u ↦ evU z.left _ (Units.val u)) (hs (fun _ ↦ i) (fun _ ↦ j))
    simp only [Units.val_mul] at e
    rw [evU_mul _ _ hV] at e
    have e1 : evU z.left _ (ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_left : (L.pull q.left).U (fun _ ↦ i) ⊓
        (L.pull q.left).U (fun _ ↦ j) ≤ (L.pull q.left).U (fun _ ↦ i)) (s.s (fun _ ↦ i))).val =
        evU z.left _ (s.s (fun _ ↦ i)).val := evalSectionAtPointOrZero_restriction _ _ _ _ _ _ _ hV
    have e2 : evU z.left _ (ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_right : (L.pull q.left).U (fun _ ↦ i) ⊓
        (L.pull q.left).U (fun _ ↦ j) ≤ (L.pull q.left).U (fun _ ↦ j)) (s.s (fun _ ↦ j))).val =
        evU z.left _ (s.s (fun _ ↦ j)).val := evalSectionAtPointOrZero_restriction _ _ _ _ _ _ _ hV
    have e3 : evU z.left _ ((L.pull q.left).g (fun _ ↦ i) (fun _ ↦ j)).val =
        evU (z ≫ q).left (L.U i ⊓ L.U j) (L.g i j).val := by
      rw [Over.comp_left]
      simpa only [evU, dite_eq_left hV, dite_eq_left hij] using
        (evalAt_pull_g L q.left z.left (fun _ ↦ i) (fun _ ↦ j) hij hV).symm
    rw [e1, e2, e3] at e
    exact e

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedAbelianGenericFibreTraitUniformis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TraitGeneric

theorem exists_polAV_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G), IsSemiAbelian G → UnifTrait D G P.L.L →
    ∃ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom ∧
      LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) := by
  intro R _ _ _ _ D G _ _ P _ hU
  obtain ⟨W, _, _, _, φ, G', _, _, β, D', A', U', -, hinj, -, hGP, hLβ, -⟩ := hU
  have hnz : nonZeroDivisors R ≤ (nonZeroDivisors W).comap φ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hinj
  let ga : FractionRing R →+* FractionRing W := IsLocalization.map (FractionRing W) φ hnz
  have hga : ga.comp (algebraMap R (FractionRing R)) = (algebraMap W (FractionRing W)).comp φ :=
    IsLocalization.map_comp hnz
  have hsq : jK W ≫ spMap φ = spMap ga ≫ jK R := by
    simp only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hga]
  let GK := (Over.pullback (jK R)).obj G
  let L : LB GK.left := P.L.L.pull (pullback.fst G.hom (jK R))
  have hL : L.IsLB := pull_isLB P.L.isLB _
  have hS : Out.Sym GK L :=
    GlobalTheory.PolBaseChange.sym_pull (isGrpPullback_pullback G (jK R)) (GlobalTheory.WtPoint.sym_of_cp P)
  have := U'.gen_hom
  set ψ₀ := U'.gen.inv.left ≫ pullback.fst G'.hom (jK W) with hψ₀
  have g₀ : IsGrpPullback A'.A G' (jK W) ψ₀ := by
    have : IsMonHom U'.gen.symm.hom := by show IsMonHom U'.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso U'.gen.symm).comp (isGrpPullback_pullback G' (jK W))).congr
      (Category.id_comp _) rfl
  have g₁ : IsGrpPullback A'.A G (spMap ga ≫ jK R) (ψ₀ ≫ β) := (g₀.comp hGP).congr hsq rfl
  have gb := isGrpPullback_pullback G (jK R)
  have w₁ : (ψ₀ ≫ β) ≫ G.hom = (A'.A.hom ≫ spMap ga) ≫ jK R :=
    g₁.1.w.trans (Category.assoc _ _ _).symm
  obtain ⟨α, e₁, e₂⟩ : ∃ α : A'.A.left ⟶ GK.left, α ≫ pullback.fst G.hom (jK R) = ψ₀ ≫ β ∧
      α ≫ GK.hom = A'.A.hom ≫ spMap ga :=
    ⟨gb.1.lift _ _ w₁, gb.1.lift_fst _ _ _, gb.1.lift_snd _ _ _⟩
  have gα : IsGrpPullback A'.A GK (spMap ga) α := gb.cancel (g₁.congr rfl e₁.symm) e₂
  have hgi : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hext : LBIso (A'.L.pull U'.gen.hom.left) (U'.LG.L.pull (pullback.fst G'.hom (jK W))) := U'.ext
  have h1 : LBIso (A'.L.pull (U'.gen.inv.left ≫ U'.gen.hom.left)) (U'.LG.L.pull ψ₀) :=
    LBIso.chartPull (Geo.Tor.chartPullSame A'.L _ (fun _ => U'.gen.hom.left) _ U'.gen.inv.left fun _ => rfl)
      (Geo.Tor.chartPullSame U'.LG.L _ (fun _ => pullback.fst G'.hom (jK W)) _ U'.gen.inv.left fun _ => rfl) hext
  have l₁ : LBIso A'.L (U'.LG.L.pull ψ₀) :=
    LBIso.chartPull (Geo.Tor.chartPullUnpull A'.L _ hgi)
      (Geo.Tor.chartPullSame U'.LG.L _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h1
  have l₂ : LBIso (U'.LG.L.pull ψ₀) (P.L.L.pull (ψ₀ ≫ β)) := GlobalTheory.Ex.GenericFibre.lbIso_pull hLβ ψ₀ rfl
  have l₃ : LBIso (L.pull α) (P.L.L.pull (ψ₀ ≫ β)) :=
    GlobalTheory.Ex.GenericFibre.lbIso_pull (GlobalTheory.PolBaseChange.lbIso_refl hL) α e₁.symm
  have hw : LBIso A'.L (L.pull α) :=
    LBIso.trans A'.isLB (pull_isLB P.L.isLB _) (pull_isLB hL _)
      (LBIso.trans A'.isLB (pull_isLB U'.LG.isLB _) (pull_isLB P.L.isLB _) l₁ l₂) l₃.symm
  exact GlobalTheory.PolFieldDescent.exists_polAV _ _ ga GK L hL hS A' α gα hw

end GlobalTheory.Mum.TraitGeneric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedAbelianSemiAbelianSiegelPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.CExtGen

theorem exists_polAV_semiAbelian : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V],
    GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ y : Sp (FractionRing V) ⟶ F.X,
      ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : V →+* V₁)
        (fK : FractionRing V →+* FractionRing V₁), GlobalTheory.LN.CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
        (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (f a)) ∧
        ∃ (A : PolAV (Sp (FractionRing V₁))) (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
          IsGrpPullback A.A F.univ.A (spMap fK ≫ y) α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) ∧
          ∃ (G : Over (Sp V₁)) (_ : GrpObj G) (_ : IsCommMonObj G) (gen : (Over.pullback (jK V₁)).obj G ≅ A.A),
            IsSemiAbelian G ∧ IsMonHom gen.hom := by
  intro g n o _ ζ F V _ _ _ hB hV y
  have hC : GlobalTheory.LN.CDvr V := ⟨hV, hB.1.2.2.2, hB.2⟩
  haveI : CharZero V := hB.2
  haveI : CharZero (FractionRing V) := inferInstance
  obtain ⟨R₁, _, _, hfin, hnt, P, α, α₂, hα, hsq, hlam⟩ := _root_.GlobalTheory.SiegelSqrtField.exists_sqrt_field g n o ζ F.X F.s F.univ F.princ (FractionRing V) y
  obtain ⟨W₁, _, _, _, f₁, ψ, hW₁, hi₁, hl₁, hf₁, hc₁⟩ := _root_.GlobalTheory.CdvrFiniteAlgebra.exists_cdvr_map_of_finite V hC R₁ hfin hnt
  obtain ⟨P₁, φ₁, hP₁, -, hL₁⟩ := GlobalTheory.KeyFam.SameLam.exists_polPB P ψ
  obtain ⟨β₂, hβ₂, hΛ₁⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ _ P.A P₁.A φ₁ hP₁
  have lam₁ := hΛ₁ P.L P₁.L _ F.univ.P α₂ P.isLB P₁.isLB F.univ.isLB hL₁ hlam
  obtain ⟨V₁, _, _, _, f₂, fK₂, hV₁, hi₂, hl₂, hf₂, hc₂, A, β, hβ, hLA, G, _, _, gen, hG, hgen⟩ := _root_.GlobalTheory.PolSemiAbModel.exists_model W₁ hW₁ P₁
  obtain ⟨γ₂, hγ₂, hΛ₂⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ _ P₁.A A.A β hβ
  have lam₂ := hΛ₂ P₁.L A.L _ F.univ.P (β₂ ≫ α₂) P₁.isLB A.isLB F.univ.isLB hLA lam₁
  refine ⟨V₁, inferInstance, inferInstance, inferInstance, f₂.comp f₁, fK₂.comp (ψ.comp (algebraMap _ R₁)), hV₁,
    hi₂.comp hi₁, ?_, hf₂.comp hf₁, ?_, A, β ≫ φ₁ ≫ α, γ₂ ≫ β₂ ≫ α₂, ?_, ?_, ?_, G, inferInstance, inferInstance, gen, hG,
    hgen⟩
  · exact RingHom.isLocalHom_comp f₂ f₁
  · intro a
    simp [hc₁, hc₂]
  · refine (hβ.comp (hP₁.comp hα)).congr ?_ rfl
    simp [spMap, Spec.map_comp]
  · exact GlobalTheory.ZM.SiegPull.isSquare_comp hγ₂ (GlobalTheory.ZM.SiegPull.isSquare_comp hβ₂ hsq)
  · simpa [Category.assoc] using lam₂

end GlobalTheory.CExtGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowPolAV
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.PowPol

open GlobalTheory.CechPic GlobalTheory.SiegelOfPolarised GlobalTheory.PrimNorm GlobalTheory.SiegelPower

def siegLam (hG : Out.GlobalFnsSt) {R : Type} [CommRing R] (P : PolAV (Sp R)) [IsCommMonObj P.A] :
    SiegPre 0 1 (1 : R) (𝟙 (Sp R)) where
  A := P.A
  ab := P.isAb
  P := abelian₂ P.A P.L
  isLB := LB.isLB_linComb P.isLB _ _
  rig₁ := hasGen_lam_pull P.isLB _ _ (by simp [diff₂])
  rig₂ := hasGen_lam_pull P.isLB _ _ (by simp [diff₂])
  symm := lbIso_lam_pull P.isLB _ _ (diff₂_comm _ _)
  lev := fun _ => 1
  lev_add := fun _ _ => (_root_.mul_one _).symm
  lev_tors := fun _ => one_pow _
  geom := by
    intro K _ _ x β z _ hz
    obtain rfl : z = 1 := Units.ext (by simpa using hz)
    refine ⟨fun a => ⟨fun _ => ⟨a, (one_smul _ _).symm⟩, fun _ => MonObj.comp_one _⟩,
      fun y hy => ⟨0, (MonObj.comp_one _).trans ((pow_one y).symm.trans hy).symm⟩, fun a b => ?_⟩
    rw [MonObj.comp_one, one_zpow, show unitOn (1 : Kˣ) = 1 from map_one _]
    exact GlobalTheory.EighthPowerFactor.weilIs_one_one hG P.isAb (pull_isLB (LB.isLB_linComb P.isLB _ _) _) _

theorem det_eq_one {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (hpd : ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef)
    (hdet : IsUnit (W + W.transpose).det) : (W + W.transpose).det = 1 := by
  have h₁ := hpd.det_pos
  have h₂ : ((W + W.transpose).map (Int.cast : ℤ → ℝ)).det = (((W + W.transpose).det : ℤ) : ℝ) :=
    ((Int.castRingHom ℝ).map_det _).symm
  rw [h₂] at h₁
  rcases Int.isUnit_iff.1 hdet with h | h
  · exact h
  · rw [h] at h₁; norm_num at h₁

theorem exists_pow_polAV : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (P : PolAV (Sp R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∃ (P' : PolAV (Sp R)) (pr : Fin r → (P'.A ⟶ P.A)), (∀ i, IsMonHom (pr i)) ∧ Nonempty (IsLimit (Fan.mk P'.A pr)) ∧ P'.g = r * P.g ∧ LBIso P'.L (LB.LinComb P.L (tensφ pr) (tensε W)) := by
  intro R _ _ _ _ P r W hpd hdet
  have := P.isAb.comm
  obtain ⟨L₁, -⟩ := abelianSchemeLaws_all
  have hG := L₁.globalFns
  let c := siegLam hG P
  have hP : c.P.IsLB := c.isLB
  have hD : c.diag.IsLB := pull_isLB hP _
  have hfin : IsFinite (𝟙 P.A : P.A ⟶ P.A).left := inferInstanceAs (IsFinite (𝟙 P.A.left))
  have hamp : RelAmple c.A c.diag := by
    have e := lbIso_diag L₁ P
    have h := relAmple_finite_pow_iso (Sp R) P.A P.A (𝟙 _) P.L 2 two_pos P.isAb P.isAb P.isLB hfin
    exact (relAmple_finite_pow_iso (Sp R) P.A P.A (𝟙 _) (lbPow P.L 2) 1 one_pos P.isAb P.isAb
      (LB.isLB_linComb P.isLB _ _) hfin).2.2.2 _ hD e (h.2.1.2 P.ample)
  let G := Out.powObj P.A r
  let pr : Fin r → (G ⟶ P.A) := Out.powPr P.A
  have hpr : ∀ u, IsMonHom (pr u) := fun u => inferInstance
  have hu : ∀ (T : Over (Sp R)) (y : Fin r → (T ⟶ P.A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u := fun T y =>
    ⟨(Out.powIsLimit P.A r).lift (Fan.mk T y), fun u => (Out.powIsLimit P.A r).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit P.A r).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hB : ∀ (T : Over (Sp R)) (x x' y : T ⟶ c.A), bi hP (x * x') y = bi hP x y + bi hP x' y := fun T x x' y => by
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2
      (GlobalTheory.T.biadditive_of_trivial_on_axes hG (Sp R) c.A c.diag c.ab hD hamp c.P hP c.rig₁ c.rig₂ T x x' y).1
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    simp only [bi]
    abel
  have hs : ∀ (T : Over (Sp R)) (x y : T ⟶ c.A), bi hP x y = bi hP y x := fun T x y => by
    have e : cls c.P hP = bi hP (snd c.A c.A) (fst c.A c.A) := (cls_eq_iff hP (pull_isLB hP _)).2 c.symm
    rw [bi, e, pull_bi, lift_fst, lift_snd]
  have hLB : (sharp c.P pr W).IsLB := LB.isLB_linComb hP _ _
  refine ⟨{ A := G
            isAb := isAbelianScheme_powObj_of_isAbelianScheme P.A P.isAb r
            g := r * P.g
            smoothDim := powObj_smoothOfRelativeDimension_mul _ _ _ r P.smoothDim
            L := sharp c.P pr W
            isLB := hLB
            rigid := rigidified_sharp hP pr W hpr hB
            sym := sym_sharp hP pr W hpr hB hs
            ample := GlobalTheory.T.relAmple_formBundle_power_of_posDef hG 0 1 r R 1 (Sp R) (𝟙 _) c G pr W hpr hu hamp hpd
            ktriv := kTriv_sharp hP pr W hpr hB hs hu (det_eq_one W hpd hdet)
              (fun T x hx => eq_one_of_lam P.isLB P.ktriv x hx) }, pr, hpr, ⟨Out.powIsLimit P.A r⟩, rfl, ?_⟩
  refine lbIso_nested P.isLB _ _ (fun uv : Fin r × Fin r => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2) _ _ ?_
  simp only [prod_lam (pr _) (pr _) (PrimNorm.cls P.L)]
  rw [Fintype.prod_prod_type (f := fun k : (Fin r × Fin r) × Fin 4 => PrimNorm.cls P.L (tensφ pr k) ^ tensε W k)]
  refine Finset.prod_congr rfl fun uv _ => ?_
  simp only [Fin.prod_univ_four, tensφ, tensε, GlobalTheory.PolDeg.lamPts, Oε, diff₂, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, zpow_mul]
  simp only [zpow_one, zpow_neg, mul_zpow, inv_zpow]

end GlobalTheory.Mum.PowPol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverSourceOfBirational
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

namespace GlobalTheory.Discrepancy

theorem DivOver.exists_over_complex : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp ℂ) (s : Y ⟶ X) [IsDominant s],
    Function.Bijective (functionFieldMap s) → ∀ E : DivOver p, ∃ E' : DivOver (s ≫ p), DivOver.Over s E' E := by
  intro X Y _ _ p s _ hs E
  exact DivOver.exists_over ℂ X Y p s hs E

end GlobalTheory.Discrepancy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverTargetOfBirational
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Discrepancy

theorem DivOver.exists_over_of_bijective_complex : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp ℂ) (s : Y ⟶ X) [IsDominant s],
    Function.Bijective (functionFieldMap s) → ∀ E' : DivOver (s ≫ p), ∃ E : DivOver p, DivOver.Over s E' E :=
  fun p s _ hb E' => DivOver.exists_over_of_bijective ℂ _ _ p s hb E'

end GlobalTheory.Discrepancy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProperNormalFlagSchemeOfAffineCover
section
noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

namespace GlobalTheory.FlagMod.FieldFlag

theorem exists_properFlag : ∀ (K : Type) [Field K] (X : Scheme.{0}) (s : X ⟶ Sp K) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsCover (RingHom.id K) s V α c D → (∀ x : X, ∃ b, x ∈ (V b).1) → ∃ (Z : Scheme.{0}) (π : Z ⟶ X) (g : ∀ en : En m, Z ⟶ PSpace K (plN M en.1)) (κ : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ Z)), IsProper π ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z ∧ HasPlk (RingHom.id K) V α c π g κ ∧ (∀ b w, IsOpenImmersion (κ b w)) ∧ (∀ z : Z, ∃ b w, z ∈ Set.range (κ b w)) ∧ ∀ (W : Scheme.{0}) (a a' : W ⟶ Z), a ≫ π = a' ≫ π → (∀ en, a ≫ g en = a' ≫ g en) → a = a' := by
  intro K _ X s T _ m M B _ V α c D hP hN hC hV
  obtain ⟨P, p0, p, h, hPlk⟩ := _root_.GlobalTheory.FlagEmb.exists_isPlk K K (RingHom.id K) X s T m M B V α c D hP hC
  obtain ⟨F, f, i, hf, hi, hif, hcov⟩ := _root_.GlobalTheory.FlagEmb.cells_glue K K (RingHom.id K) X s T m M B V α c D P p0 p h hP hN hC hPlk
  have hXn : IsLocallyNoetherian X := by
    obtain ⟨N, ι, _, rfl⟩ := hP
    exact LocallyOfFiniteType.isLocallyNoetherian (ι ≫ PSpace.str K N)
  obtain ⟨hFc, hFn, hFnoe⟩ := _root_.GlobalTheory.FlagEmb.compact_normal_noetherian_of_cells X T m B V F i hN hi hcov
  have hPp : IsProper (p0 ≫ s) := by
    obtain ⟨N, ι, hι, e⟩ := hPlk.proj
    have := isProper_str K N
    rw [← e]
    infer_instance
  have hsp : IsProper s := by
    obtain ⟨N, ι, hι, rfl⟩ := hP
    have := isProper_str K N
    infer_instance
  have hp0 : IsProper p0 := IsProper.of_comp p0 s
  have : LocallyOfFiniteType (f ≫ p0 ≫ s) := inferInstance
  have : IsLocallyNoetherian F := LocallyOfFiniteType.isLocallyNoetherian (f ≫ p0 ≫ s)
  have : IsNoetherian F := {}
  have hqc : QuasiCompact f := inferInstance
  have hsep : IsSeparated (f.imageι ≫ p0) := inferInstance
  have hpre := _root_.GlobalTheory.FlagEmb.preimage_iUnion_eq_range_cells K K (RingHom.id K) X s T m M B V α c D P p0 p h hC hPlk F f.image f i f.toImage f.imageι
    hf hi hif hcov inferInstance f.toImage_imageι f.toImage.denseRange hFnoe hsep
  have huniv : (⋃ b, ((V b).1 : Set X)) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨b, hb⟩ := hV x
    exact Set.mem_iUnion.2 ⟨b, hb⟩
  have hsurj : Function.Surjective f.toImage := by
    rw [← Set.range_eq_univ, ← hpre, huniv, Set.preimage_univ]
  have : Surjective f.toImage := ⟨hsurj⟩
  have : IsIso f.toImage := IsOpenImmersion.isIso f.toImage
  have hfc : IsClosedImmersion f := by
    rw [← f.toImage_imageι]
    infer_instance
  refine ⟨F, f ≫ p0, fun en => f ≫ p en, i, inferInstance, hFn, ⟨?_, ?_⟩, hi, hcov, ?_⟩
  · intro b w
    rw [← Category.assoc, hif, hPlk.base]
  · intro b w en
    obtain ⟨hu, e⟩ := hPlk.plk b w en
    exact ⟨hu, by rw [← Category.assoc, hif, e]⟩
  · intro W a a' e1 e2
    have key : a ≫ f = a' ≫ f := by
      refine hPlk.ext _ _ _ ?_ fun en => ?_
      · simpa only [Category.assoc] using e1
      · simpa only [Category.assoc] using e2 en
    exact (cancel_mono f).1 key

end GlobalTheory.FlagMod.FieldFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalPointOfPointOverFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_pt_of_pt_ext : ∀ (H Q : Scheme.{0}) (φ : H ⟶ Q), LocallyOfFiniteType φ → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (ν : Sp Ω ⟶ Q) (Ω' : Type) [Field Ω'] (io : Ω →+* Ω') (q : Sp Ω' ⟶ H), q ≫ φ = spMap io ≫ ν →
    ∃ p : Sp Ω ⟶ H, p ≫ φ = ν := by
  intro H Q φ hφ Ω _ _ ν Ω' _ io q hq
  have : JacobsonSpace ↥(pullback φ ν) := LocallyOfFiniteType.jacobsonSpace (pullback.snd φ ν)
  have hne : (Set.univ : Set ↥(pullback φ ν)).Nonempty :=
    ⟨pullback.lift q (spMap io) hq (IsLocalRing.closedPoint Ω'), trivial⟩
  obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints hne isOpen_univ.isLocallyClosed
  have hc' : IsClosed ({c} : Set ↥(pullback φ ν)) := hc
  refine ⟨pointOfClosedPoint (pullback.snd φ ν) c hc' ≫ pullback.fst φ ν, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]

end GlobalTheory.Mum
end

