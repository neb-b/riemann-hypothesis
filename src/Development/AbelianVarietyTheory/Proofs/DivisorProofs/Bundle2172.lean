module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianVarietyPotentialSemiAbelianModel
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PotentiallyKnownOfSameLambdaBundle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2092
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianModelFiniteExtCompleteDVR
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.PolSemiAbModel

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp]

theorem exists_model : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (P : PolAV (Sp (FractionRing W))),
    ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : W →+* V₁)
      (fK : FractionRing W →+* FractionRing V₁), GlobalTheory.LN.CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
      (∀ a, fK (algebraMap W _ a) = algebraMap V₁ _ (f a)) ∧
      ∃ (A : PolAV (Sp (FractionRing V₁))) (β : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap fK) β ∧
        LBIso A.L (P.L.pull β) ∧
        ∃ (G : Over (Sp V₁)) (_ : GrpObj G) (_ : IsCommMonObj G) (gen : (Over.pullback (jK V₁)).obj G ≅ A.A),
          IsSemiAbelian G ∧ IsMonHom gen.hom := by
  intro W _ _ _ hW P
  obtain ⟨hdvr, hcomp, hchar⟩ := (GlobalTheory.LN.cDvr_iff W).1 hW
  haveI : CharZero (FractionRing W) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective W (FractionRing W))
  obtain ⟨W', L, _, _, _, _, _, _, _, _, hsq, hfin, hloc, hcompl, G, _, ⟨e, he⟩, hG⟩ :=
    GlobalTheory.SS.potModel_isSemiAbelian W (FractionRing W) P.A P.isAb
  have hinj : Function.Injective (algebraMap W W') := by
    have h2 : Function.Injective ((algebraMap (FractionRing W) L).comp (algebraMap W (FractionRing W))) :=
      (algebraMap (FractionRing W) L).injective.comp (IsFractionRing.injective W (FractionRing W))
    rw [← hsq] at h2
    exact Function.Injective.of_comp h2
  haveI : CharZero W' := charZero_of_injective_algebraMap hinj
  let ε : FractionRing W' ≃ₐ[W'] L := IsLocalization.algEquiv (nonZeroDivisors W') (FractionRing W') L
  let fK : FractionRing W →+* FractionRing W' := (ε.symm : L →+* FractionRing W').comp (algebraMap (FractionRing W) L)
  have hε : (ε.symm : L →+* FractionRing W').comp (algebraMap W' L) = algebraMap W' (FractionRing W') := by
    ext x; exact ε.symm.commutes x
  obtain ⟨A, β, hpb, -, hLB⟩ := GlobalTheory.KeyFam.SameLam.exists_polPB P fK
  haveI : IsCommMonObj G := hG.comm
  refine ⟨W', inferInstance, inferInstance, inferInstance, algebraMap W W', fK,
    (GlobalTheory.LN.cDvr_iff W').2 ⟨inferInstance, hcompl, inferInstance⟩, hinj, hloc,
    RingHom.finite_algebraMap.2 hfin, ?_, A, β, hpb, hLB, ?_⟩
  · intro a
    show ε.symm (algebraMap (FractionRing W) L (algebraMap W _ a)) = _
    rw [← RingHom.comp_apply, ← hsq, RingHom.comp_apply]
    exact ε.symm.commutes _
  · let X := (Over.pullback (spMap (algebraMap W' L))).obj G
    let T := (Over.pullback (spMap (ε.symm : L →+* FractionRing W'))).obj X
    have h₁ := isGrpPullback_pullback G (jK W')
    have hTX := isGrpPullback_pullback X (spMap (ε.symm : L →+* FractionRing W'))
    have hXG := isGrpPullback_pullback G (spMap (algebraMap W' L))
    have hTG := (hTX.comp hXG).congr (by rw [spMap_comp', hε]) rfl
    obtain ⟨e₁, he₁, -⟩ := grpPullback_iso h₁ hTG
    have hXY := isGrpPullback_of_iso e
    have hYP := isGrpPullback_pullback P.A (spMap (algebraMap (FractionRing W) L))
    have hTP := (hTX.comp (hXY.comp hYP)).congr (by rw [Category.id_comp, spMap_comp']) rfl
    obtain ⟨e₂, he₂, -⟩ := grpPullback_iso hTP hpb
    exact ⟨G, inferInstance, inferInstance, e₁ ≪≫ e₂, hG, by simp only [Iso.trans_hom]; infer_instance⟩

end GlobalTheory.PolSemiAbModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearCochainOfDegreeOneObstructionZer
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Obs

theorem exists_cochain_of_isOb1_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Module.Projective R₀ (GlobForm s₀) → ∀ (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π (OAff s₀)) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) (OAff s₀) F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), (∀ w, L.IsOb1 L' n l α w 0) → ∃ (κ : ∀ (T T' : C') (_ : T ⟶ T'), Ω[(OAff s₀).obj (n.G.obj T)⁄R₀] →+ L'.B T') (u : GlobForm s₀ →+ ∀ T : C', L'.B T), (∀ (T T' : C') (a : T ⟶ T'), IsTheta I (L.p (n.G.obj T)) ((L'.ρ a).comp (l T)) ((l T').comp (L.ρ (n.G.map a))) (κ T T' a)) ∧ (∀ (r : R) w, u (π r • w) = r • u w) ∧ (∀ w T, u w T ∈ I.map (algebraMap R (L'.B T))) ∧ ∀ (w : GlobForm s₀) (T T' : C') (a : T ⟶ T'), κ T T' a (w.1 (n.G.obj T)) = u w T' - L'.ρ a (u w T) := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ hP C' _ F' L L' n l h
  obtain ⟨κ, -, -, hκ, -, -, -⟩ := h 0
  let W : Submodule R (∀ T : C', L'.B T) :=
    { carrier := {m | ∀ T, m T ∈ I.map (algebraMap R (L'.B T))}
      add_mem' := fun {m m'} hm hm' T ↦ Ideal.add_mem _ (hm T) (hm' T)
      zero_mem' := fun T ↦ Ideal.zero_mem _
      smul_mem' := fun r m hm T ↦ by
        show r • m T ∈ _
        rw [Algebra.smul_def]
        exact Ideal.mul_mem_left _ _ (hm T) }
  have hW : ∀ r, π r = 0 → ∀ m ∈ W, r • m = 0 := by
    intro r hr m hm
    funext T
    show r • m T = 0
    have hrI : r ∈ I := hk ▸ RingHom.mem_ker.2 hr
    have h2 := Ideal.mul_mem_mul (Ideal.mem_map_of_mem (algebraMap R (L'.B T)) hrI) (hm T)
    rw [← sq, map_sq hI] at h2
    rw [Algebra.smul_def]
    simpa using h2
  let q : (∀ T : C', L'.B T) →ₗ[R] (∀ (T T' : C') (_ : T ⟶ T'), L'.B T') :=
    { toFun := fun m T T' a ↦ m T' - L'.ρ a (m T)
      map_add' := fun m m' ↦ by funext T T' a; simp only [Pi.add_apply, map_add (f := _)]; abel
      map_smul' := fun r m ↦ by
        funext T T' a; simp only [Pi.smul_apply, map_smul, smul_sub, RingHom.id_apply] }
  let v : GlobForm s₀ →+ (∀ (T T' : C') (_ : T ⟶ T'), L'.B T') :=
    { toFun := fun w T T' a ↦ κ T T' a (w.1 (n.G.obj T))
      map_zero' := by funext T T' a; exact map_zero (κ T T' a)
      map_add' := fun w w' ↦ by funext T T' a; exact map_add (κ T T' a) _ _ }
  have hv : ∀ (r : R) w, v (π r • w) = r • v w := by
    intro r w
    funext T T' a
    show κ T T' a (π r • w.1 (n.G.obj T)) = r • κ T T' a (w.1 (n.G.obj T))
    have hp : L.p (n.G.obj T) (algebraMap R (L.B (n.G.obj T)) r) = algebraMap R₀ _ (π r) := by
      have h1 := L.semi (n.G.obj T) r 1
      rw [← Algebra.algebraMap_eq_smul_one, map_one] at h1
      rw [h1, Algebra.algebraMap_eq_smul_one]
    have h3 := (hκ T T' a).smul (algebraMap R _ r) (w.1 (n.G.obj T))
    rw [hp, algebraMap_smul, AlgHom.commutes] at h3
    rw [h3, Algebra.smul_def]
  have hq : ∀ w, ∃ m ∈ W, q m = v w := by
    intro w
    obtain ⟨κw, σw, zw, hκw, hσw, hc, hz⟩ := h w
    obtain ⟨f, hf⟩ := H1.mk_eq_zero.1 hc.symm
    have hκκ : ∀ T T' (a : T ⟶ T'), κ T T' a = κw T T' a := fun T T' a ↦
      (isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) (L'.B T') _ _ ((l T').comp (L.ρ (n.G.map a))) _ _
        (hκ T T' a)).2.2.1 (hκw T T' a)
    refine ⟨fun T ↦ σw T (f T), fun T ↦ (sig_basic R R₀ I hI π hπ hk R₁ α _ _ (L'.p T) (L'.semi T) (L'.surj T)
      (L'.ker T) (σw T) (hσw T)).1 (f T), ?_⟩
    funext T T' a
    have hn := (sig_natural R R₀ I hI π hπ hk R₁ α _ _ (L'.p T) (L'.semi T) (L'.surj T) (L'.ker T) _ _ (L'.p T')
      (L'.semi T') (L'.surj T') (L'.ker T') (L'.ρ a) (mp F' a) (L'.nat a) (σw T) (σw T') (hσw T) (hσw T')).1 (f T)
    have hzf : zw.1 T T' a = f T' - extHom R₁ (mp F' a) (f T) := by
      rw [← hf]; rfl
    show σw T' (f T') - L'.ρ a (σw T (f T)) = κ T T' a (w.1 (n.G.obj T))
    rw [hκκ, ← (hz T T' a).2, hzf, map_sub, hn]
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_semilinear_lift_of_projective R R₀ π hπ (GlobForm s₀) hP _ _ W hW q v hv hq
  exact ⟨κ, u, hκ, hu1, hu2, fun w T T' a ↦ (congrFun (congrFun (congrFun (hu3 w) T) T') a).symm⟩

end GlobalTheory.Obs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSharpPowOf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.EighthPowerLocal

open GlobalTheory.SS GlobalTheory.CechPic GlobalTheory.MatrixBundle

theorem relAmple_diag_lam {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {B : Over (Sp R)} [GrpObj B]
    [IsCommMonObj B] (hB : IsAbelianScheme B) {M : LB B.left} (hM : M.IsLB) (hΘ : ∃ t : LB.Gen (Theta B M), t.IsGen)
    (ha : Out.RelAmple B M) : Out.RelAmple B ((abelian₂ B M).pull (lift (𝟙 B) (𝟙 B)).left) := by
  have hlam : (abelian₂ B M).IsLB := LB.isLB_linComb hM _ _
  let q := Out.powIsPowGrp B 2
  have hG : IsAbelianScheme (Out.powObj B 2) := (PowGrp.powers _ _ B 2 q).2.2.2.1 hB
  let ψ : B ⟶ Out.powObj B 2 := (Out.powIsLimit B 2).lift (Fan.mk B ![𝟙 B, (𝟙 B)⁻¹])
  have hψ : ∀ u, ψ ≫ q.pr u = ![𝟙 B, (𝟙 B)⁻¹] u := fun u => (Out.powIsLimit B 2).fac _ ⟨u⟩
  have hbox : (Out.boxLB M q.pr).IsLB := LB.isLB_linComb hM _ _
  have hfin : IsFinite ψ.left := by
    have := hB.proper
    have := hG.proper
    have : IsSeparated ((q.pr 0).left ≫ B.hom) := by rw [Over.w]; infer_instance
    have : IsSeparated (q.pr 0).left := IsSeparated.of_comp _ B.hom
    have : IsFinite (ψ.left ≫ (q.pr 0).left) := by
      rw [← Over.comp_left, hψ]
      exact inferInstanceAs (IsFinite (𝟙 B.left))
    exact IsFinite.of_comp _ (q.pr 0).left
  have hid : IsFinite (𝟙 B : B ⟶ B).left := inferInstanceAs (IsFinite (𝟙 B.left))
  have a₁ := (relAmple_finite_pow_iso _ B _ ψ _ 1 one_pos hB hG hbox hfin).1
    (relAmple_boxLB _ _ B 2 q M hM ha)
  refine (relAmple_finite_pow_iso _ B B (𝟙 B) _ 1 one_pos hB hB (pull_isLB hbox _) hid).2.2.2 _
    (pull_isLB hlam _) ((cls_eq_iff (pull_isLB hbox _) (pull_isLB hlam _)).1 ?_) a₁
  have h₀ : pull (1 : B ⟶ B).left (cls M hM) = 0 := by
    rw [Hom.one_def, Over.comp_left, pull_comp]
    obtain ⟨N, hN, e⟩ := cls_surj (pull (η[B]).left (cls M hM))
    have z : cls N hN = 0 := (cls_eq_zero_iff hN).2 (DVR.exists_gen_of_isLB_local (V := R) N hN)
    rw [← e, z, map_zero]
  have h₁ : cls _ hlam = lam (cls M hM) (fst B B) (snd B B) := cls_cube_two hM _ _ hlam
  have h₂ := lam_mul_left hM hΘ (𝟙 B) (𝟙 B)⁻¹ (𝟙 B)
  rw [mul_inv_cancel, lam_one_left, lam.eq_1 _ (𝟙 B)⁻¹, inv_mul_cancel, h₀] at h₂
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cls_pull hbox, cls_pull hlam, h₁, pull_lam, lift_fst, lift_snd, cls_linComb hM, map_sum, Fin.sum_univ_two,
    one_smul, one_smul, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, hψ, hψ]
  refine Eq.trans ?_ (eq_neg_of_add_eq_zero_left h₂.symm).symm
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  abel


end GlobalTheory.EighthPowerLocal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShiftSemicharactersNestedLattices
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemicharShift

def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun y w => (hermForm Hm y w).im)
    (fun a b w => by simp [hermForm, add_dotProduct])
    (fun c a w => by simp [hermForm, smul_dotProduct, Complex.smul_im])
    (fun y a b => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c y a => by
      simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im])

theorem imForm_apply {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (y w : Fin g → ℂ) :
    imForm Hm y w = (hermForm Hm y w).im := rfl

theorem imForm_surjective {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) :
    Function.Surjective (imForm Hm) := by
  have hinj : Function.Injective (imForm Hm) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    by_contra hz0
    have h1 : imForm Hm z (Complex.I • z) = 0 := by rw [hz]; rfl
    have h2 : imForm Hm z (Complex.I • z) = -(hermForm Hm z z).re := by
      rw [imForm_apply]
      simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Matrix.mulVec_neg,
        dotProduct_neg, smul_eq_mul, Complex.mul_im]
    have := hpos z hz0
    linarith
  have hdim : Module.finrank ℝ (Fin g → ℂ) = Module.finrank ℝ ((Fin g → ℂ) →ₗ[ℝ] ℝ) :=
    (Subspace.dual_finrank_eq).symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj

end GlobalTheory.SemicharShift

namespace GlobalTheory.SemicharShift

theorem exists_linear_of_char {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hsp : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (ρ : Λ → ℂ) (hn : ∀ l, ‖ρ l‖ = 1)
    (hmul : ∀ l m, ρ (l + m) = ρ l * ρ m) :
    ∃ φ : (Fin g → ℂ) →ₗ[ℝ] ℝ, ∀ l : Λ,
      ρ l = Complex.exp (2 * Real.pi * Complex.I * (φ (l : Fin g → ℂ) : ℂ)) := by
  haveI : IsZLattice ℝ Λ := ⟨hsp⟩
  let b := Module.Free.chooseBasis ℤ Λ
  let B := b.ofZLatticeBasis ℝ Λ
  let φ : (Fin g → ℂ) →ₗ[ℝ] ℝ := B.constr ℝ (fun j => Complex.arg (ρ (b j)) / (2 * Real.pi))
  refine ⟨φ, ?_⟩
  have hφb : ∀ j, φ (b j : Fin g → ℂ) = Complex.arg (ρ (b j)) / (2 * Real.pi) := by
    intro j
    have : (b j : Fin g → ℂ) = B j := by simp [B, Module.Basis.ofZLatticeBasis_apply]
    rw [this]
    exact B.constr_basis ℝ _ j
  have hne : ∀ l, ρ l ≠ 0 := fun l h => by simpa [h] using hn l
  have h0 : ρ 0 = 1 := by
    have := hmul 0 0
    rw [add_zero] at this
    have h := hne 0
    field_simp at this
    exact this.symm
  let S : AddSubgroup Λ :=
    { carrier := {l | ρ l = Complex.exp (2 * Real.pi * Complex.I * (φ (l : Fin g → ℂ) : ℂ))}
      add_mem' := by
        intro l m hl hm
        simp only [Set.mem_setOf_eq] at hl hm ⊢
        rw [hmul, hl, hm, ← Complex.exp_add]
        congr 1
        simp only [Submodule.coe_add, map_add (f := _)]
        push_cast; ring
      zero_mem' := by
        simp only [Set.mem_setOf_eq, ZeroMemClass.coe_zero, map_zero]
        simp [h0]
      neg_mem' := by
        intro l hl
        simp only [Set.mem_setOf_eq] at hl ⊢
        have h1 : ρ (-l) * ρ l = 1 := by rw [← hmul, neg_add_cancel, h0]
        have h2 : ρ (-l) = (ρ l)⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [h2, hl, ← Complex.exp_neg]
        congr 1
        simp only [Submodule.coe_neg, map_neg]
        push_cast; ring }
  have htop : (⊤ : Submodule ℤ Λ) ≤ S.toIntSubmodule := by
    rw [← b.span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show ρ (b j) = Complex.exp (2 * Real.pi * Complex.I * (φ (b j : Fin g → ℂ) : ℂ))
    rw [hφb]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have : 2 * (Real.pi : ℂ) * Complex.I * ((Complex.arg (ρ (b j)) / (2 * Real.pi) : ℝ) : ℂ)
        = (Complex.arg (ρ (b j)) : ℂ) * Complex.I := by
      push_cast; field_simp
    rw [this]
    have h := Complex.norm_mul_exp_arg_mul_I (ρ (b j))
    rw [hn, Complex.ofReal_one, _root_.one_mul] at h
    exact h.symm
  intro l
  exact htop (Submodule.mem_top : l ∈ ⊤)

end GlobalTheory.SemicharShift

namespace GlobalTheory.SemicharShift

theorem exists_shift_of_semichar : ∀ (g : ℕ) (Λ Λ₁ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (χ₁ : Λ₁ → ℂ)
    (h : Λ ≤ Λ₁), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ l, ‖χ l‖ = 1) → (∀ l, ‖χ₁ l‖ = 1) →
    (∀ l m : Λ, χ (l + m) = χ l * χ m * Complex.exp (Real.pi * Complex.I * (hermForm Hm l m).im)) →
    (∀ l m : Λ₁, χ₁ (l + m) = χ₁ l * χ₁ m * Complex.exp (Real.pi * Complex.I * (hermForm Hm l m).im)) →
    ∃ a : Fin g → ℂ, ∀ l : Λ,
      χ l = χ₁ (Submodule.inclusion h l) * Complex.exp (2 * Real.pi * Complex.I * (hermForm Hm a l).im) := by
  intro g Λ Λ₁ Hm χ χ₁ h hdisc hsp _hH hpos hχ hχ₁ hc hc₁
  haveI := hdisc
  have hne : ∀ l, χ₁ l ≠ 0 := fun l e => by simpa [e] using hχ₁ l
  have hne' : ∀ l, χ l ≠ 0 := fun l e => by simpa [e] using hχ l
  let ρ : Λ → ℂ := fun l => χ l / χ₁ (Submodule.inclusion h l)
  have hn : ∀ l, ‖ρ l‖ = 1 := fun l => by simp [ρ, norm_div, hχ, hχ₁]
  have hmul : ∀ l m, ρ (l + m) = ρ l * ρ m := by
    intro l m
    simp only [ρ]
    rw [map_add (f := _), hc, hc₁]
    simp only [Submodule.coe_inclusion]
    have e1 := hne (Submodule.inclusion h l)
    have e2 := hne (Submodule.inclusion h m)
    have e3 : Complex.exp (Real.pi * Complex.I * (hermForm Hm l m).im) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  obtain ⟨φ, hφ⟩ := exists_linear_of_char Λ hsp ρ hn hmul
  obtain ⟨a, ha⟩ := imForm_surjective Hm hpos φ
  refine ⟨a, fun l => ?_⟩
  have h1 := hφ l
  rw [← ha, imForm_apply] at h1
  rw [← h1]
  simp only [ρ]
  field_simp [hne (Submodule.inclusion h l)]

end GlobalTheory.SemicharShift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSimSys
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.TateCompare

variable {p : ℕ} [Fact p.Prime] {D : Datum p}
variable {k : Type} [Field k] {Q : Type} [Group Q] {act : D.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem ev_zsmul (I : TateIsoO D k Q act e) (n : ℕ) (c : ℤ) (x : D.La) : I.ev n (c • x) = I.ev n x ^ c := by
  let φ : Multiplicative D.La →* Q := MonoidHom.mk' (fun y => I.ev n y.toAdd) (fun a b => I.add n _ _)
  exact map_zpow φ (Multiplicative.ofAdd x) c

theorem ev_eq_iff (I : TateIsoO D k Q act e) {n : ℕ} (hn : 0 < n) (hc : n.Coprime p) {x y : D.La} :
    I.ev n x = I.ev n y ↔ ∃ z, x = y + n • z := by
  constructor
  · intro h
    have h₁ : I.ev n y * I.ev n (x - y) = I.ev n y * 1 := by
      rw [← I.add, add_sub_cancel, h, _root_.mul_one]
    obtain ⟨z, hz⟩ := (I.ker n hn hc _).1 (mul_left_cancel h₁)
    exact ⟨z, by rw [← hz, add_sub_cancel]⟩
  · rintro ⟨z, rfl⟩
    exact I.ev_add_nsmul hn hc _ _

theorem exists_lift (I₁ I₂ : TateIsoO D k Q act e) (n : ℕ) :
    ∃ g : D.La →+ D.La, 0 < n → n.Coprime p → ∀ y, I₁.ev n (g y) = I₂.ev n y := by
  by_cases h : 0 < n ∧ n.Coprime p
  swap
  · exact ⟨0, fun h₁ h₂ => (h ⟨h₁, h₂⟩).elim⟩
  obtain ⟨hn, hc⟩ := h
  have := D.freeLa
  let b := Module.Free.chooseBasis ℤ D.La
  have hpre : ∀ y, ∃ x, I₁.ev n x = I₂.ev n y := fun y =>
    (I₁.onto n hn hc _).1 ((I₂.onto n hn hc _).2 ⟨y, rfl⟩)
  choose f hf using hpre
  let g : D.La →ₗ[ℤ] D.La := b.constr ℤ (fun i => f (b i))
  refine ⟨g.toAddMonoidHom, fun _ _ y => ?_⟩
  show I₁.ev n (g y) = I₂.ev n y
  have hy : y ∈ Submodule.span ℤ (Set.range b) := by rw [b.span_eq]; trivial
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    simp only [g, Module.Basis.constr_basis, hf]
  | zero =>
    rw [map_zero, (I₁.ker n hn hc 0).2 ⟨0, (smul_zero _).symm⟩, (I₂.ker n hn hc 0).2 ⟨0, (smul_zero _).symm⟩]
  | add x y _ _ hx hy => rw [map_add (f := _), I₁.add, I₂.add, hx, hy]
  | smul c x _ hx => rw [map_zsmul, ev_zsmul, ev_zsmul, hx]

theorem exists_mult (I₁ I₂ : TateIsoO D k Q act e) (n : ℕ) :
    ∃ u : ℕ, 0 < n → n.Coprime p → I₁.ζ n ^ u = I₂.ζ n := by
  by_cases h : 0 < n ∧ n.Coprime p
  swap
  · exact ⟨0, fun h₁ h₂ => (h ⟨h₁, h₂⟩).elim⟩
  obtain ⟨hn, hc⟩ := h
  have : NeZero n := ⟨hn.ne'⟩
  have h₁ : IsPrimitiveRoot ((I₁.ζ n : kˣ) : k) n := IsPrimitiveRoot.coe_units_iff.2 (I₁.ζ_prim n hn hc)
  have h₂ : ((I₂.ζ n : kˣ) : k) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, (I₂.ζ_prim n hn hc).pow_eq_one, Units.val_one]
  obtain ⟨u, -, hu⟩ := h₁.eq_pow_of_pow_eq_one h₂
  exact ⟨u, fun _ _ => Units.ext (by rw [Units.val_pow_eq_pow_val, hu])⟩

end GlobalTheory.UPel.HT.TateCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSquareEquivFibreSquareSectionsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensorSquare_equiv_fibreSquare_sections : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (V₀ : Y.Opens), IsAffineOpen V₀ →
    ∀ (h : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀),
    letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
    ∃ e : Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀) ≃+* Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀),
      ∀ a b : Γ(X, f ⁻¹ᵁ V₀), e (a ⊗ₜ b) =
        ((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom a * ((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) _ h).hom b := by
  first | exact @GlobalTheory.LBDescent.exists_tensorSquare_equiv_sections | exact GlobalTheory.LBDescent.exists_tensorSquare_equiv_sections | (intros; apply GlobalTheory.LBDescent.exists_tensorSquare_equiv_sections <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfDvrLiftThroughFiniteCorrespondenceStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_dvr_lift_through_finite_correspondence : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y₀ Y : Scheme.{0}) (τ : X ⟶ Sp R) (s t : Y ⟶ X) (i : Y₀ ⟶ Y), IsQProjOver τ → IsFinite s → IsOpenImmersion i → IsDominant i → t ≫ τ = s ≫ τ → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ i ≫ t → ∃ z : Sp V ⟶ X, spMap (algebraMap V K) ≫ z = x ≫ i ≫ s) → IsProper t := by
  first | (exact @GlobalTheory.FiniteCoverProper.isProper_of_lift_through_finite) | (exact GlobalTheory.FiniteCoverProper.isProper_of_lift_through_finite) | (intros; apply GlobalTheory.FiniteCoverProper.isProper_of_lift_through_finite  <;> assumption)
end

