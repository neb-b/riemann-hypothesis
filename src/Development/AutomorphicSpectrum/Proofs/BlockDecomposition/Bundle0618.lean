module

public import Mathlib
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0561
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0598
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0589

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevelCharacter
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate

open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RankinSelberg.LiftLevel

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace F] [BorelSpace F] in
theorem mem_integer_iff_ord {x : F} (hx : x ≠ 0) : x ∈ 𝒪[F] ↔ 0 ≤ ord x := by
  rw [← mem_valBall_zero_iff, mem_valBall_iff_le_ord hx]


omit [MeasurableSpace F] [BorelSpace F] in
theorem inv_mul_mem_of_ord_le {m y : F} (hm : m ≠ 0) (hy : y ≠ 0 → ord m ≤ ord y) :
    m⁻¹ * y ∈ 𝒪[F] := by
  rcases eq_or_ne y 0 with rfl | h0
  · simp
  · have := hy h0
    rw [mem_integer_iff_ord (mul_ne_zero (inv_ne_zero hm) h0), ord_mul (inv_ne_zero hm) h0,
      ord_inv hm]
    omega

omit [MeasurableSpace F] [BorelSpace F] in
theorem le_ord_of_mem {n : ℕ} {y : F} (h0 : y ≠ 0)
    (hc : (((unifUnit F)⁻¹ ^ n : Fˣ) : F) * y ∈ 𝒪[F]) : (n : ℤ) ≤ ord y := by
  have e : ((unifUnit F)⁻¹ ^ n : Fˣ) = unifUnit F ^ (-(n : ℤ)) := by
    rw [inv_pow, _root_.zpow_neg, zpow_natCast]
  have h := (mem_integer_iff_ord (mul_ne_zero (Units.ne_zero _) h0)).1 hc
  rw [ord_mul (Units.ne_zero _) h0, e, ord_unifUnit_zpow] at h
  omega


omit [MeasurableSpace F] [BorelSpace F] in
theorem ord_lower_right {n : ℕ} (hn : 1 ≤ n) {x : GL (Fin 2) F} {d : Fˣ} (h : GammaZeroLevelMembership n x d) :
    ord (d : F) = 0 := by
  obtain ⟨hx, hc, hd⟩ := h
  have hxi := ((GLnLocal.mem_integralGL_iff F 2).1 hx).1
  have hπ : ((unifUnit F : Fˣ) : F) ≠ 0 := Units.ne_zero _
  have h0 : 0 ≤ ord (d : F) := (mem_integer_iff_ord d.ne_zero).1 (hd ▸ hxi 1 1)
  by_contra hne
  have h1 : ord ((unifUnit F : Fˣ) : F) ≤ ord (x 1 1) := by
    rw [ord_unifUnit, ← hd]; omega
  have hd' := inv_mul_mem_of_ord_le hπ (y := x 1 1) fun _ => h1
  have hc' := inv_mul_mem_of_ord_le hπ (y := x 1 0) fun h0 => by
    have := le_ord_of_mem h0 hc
    rw [ord_unifUnit]; omega
  have hdet : ((unifUnit F : Fˣ) : F)⁻¹ * (Matrix.GeneralLinearGroup.det x : F) ∈ 𝒪[F] := by
    have : ((unifUnit F : Fˣ) : F)⁻¹ * (Matrix.GeneralLinearGroup.det x : F) =
        x 0 0 * (((unifUnit F : Fˣ) : F)⁻¹ * x 1 1) -
          x 0 1 * (((unifUnit F : Fˣ) : F)⁻¹ * x 1 0) := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
      ring
    rw [this]
    exact sub_mem (mul_mem (hxi 0 0) hd') (mul_mem (hxi 0 1) hc')
  have hz : ord (Matrix.GeneralLinearGroup.det x : F) = 0 := GodementSectionLocal.ord_det_eq_zero hx
  have hdn : (Matrix.GeneralLinearGroup.det x : F) ≠ 0 := Units.ne_zero _
  have := (mem_integer_iff_ord (mul_ne_zero (inv_ne_zero hπ) hdn)).1 hdet
  rw [ord_mul (inv_ne_zero hπ) hdn, ord_inv hπ, ord_unifUnit, hz] at this
  omega

end Local

theorem mem_Gamma0Level_of_places (N : ℕ) [NeZero N] (u : AdelicGLn.FiniteAdelicGL ℚ 2)
    (hint : ∀ v : Pl, glAt v u ∈ integralGL (Qv v) 2)
    (hlev : ∀ v : Pl, ((N : Qv v))⁻¹ * glAt v u 1 0 ∈ 𝒪[Qv v]) : u ∈ Gamma0Level N := by
  refine ⟨(AdelicGLn.mem_integralFiniteGL_iff_forall ℚ 2).2 fun v => ?_, ?_⟩
  · have e : (AdelicGLn.finiteRestrictedEquiv ℚ 2 u v : GL (Fin 2) (Qv v)) = glAt v u :=
      Units.ext (Matrix.ext fun a b => rfl)
    rw [e]
    exact hint v
  · rw [GL2Classical.mem_levelIdeal_iff, mem_integralFiniteAdeles]
    intro v
    have hw : adeleAt v ((((GL2Classical.levelUnit N)⁻¹ : Afˣ)) : Af) = ((N : Qv v))⁻¹ := by
      have h1 : ((((GL2Classical.levelUnit N)⁻¹ : Afˣ)) : Af) * (N : Af) = 1 := by
        rw [← GL2Classical.coe_levelUnit N, Units.inv_mul]
      have h2 := congrArg (adeleAt v) h1
      rw [map_mul, map_natCast, map_one] at h2
      exact eq_inv_of_mul_eq_one_left h2
    have e : (((((GL2Classical.levelUnit N)⁻¹ : Afˣ)) : Af) *
        (u : Matrix (Fin 2) (Fin 2) Af) 1 0) v = ((N : Qv v))⁻¹ * glAt v u 1 0 := by
      rw [← hw]
      exact map_mul (adeleAt v) _ _
    rw [e]
    exact (mem_valuationInteger_iff v _).1 (hlev v)

theorem exists_finEmb (h : G2) (hinf : ∀ w, infAt w h = 1) :
    ∃ u : AdelicGLn.FiniteAdelicGL ℚ 2, h = finEmb ℚ 2 u ∧ ∀ v : Pl, glAt v u = finAt v h := by
  refine ⟨(AdelicGLn.prodEquiv ℚ 2 h).2, ?_, fun v => Units.ext (Matrix.ext fun a b => rfl)⟩
  apply (AdelicGLn.prodEquiv ℚ 2).injective
  rw [prodEquiv_finEmb]
  refine Prod.ext ?_ rfl
  apply (AdelicGLn.infiniteEquiv ℚ 2).injective
  funext w
  rw [map_one]
  exact hinf w

theorem lift_right {k N : ℕ} [NeZero N] {f : UpperHalfPlane → ℂ} {ω : HeckeCharacter ℚ} {φ : G2 → ℂ}
    (hL : Lift k N f ω φ) {h : G2} (hinf : ∀ w, infAt w h = 1)
    (hint : ∀ v : Pl, finAt v h ∈ integralGL (Qv v) 2)
    (hlev : ∀ v : Pl, ((N : Qv v))⁻¹ * finAt v h 1 0 ∈ 𝒪[Qv v])
    (D : Afˣ) (hD : ∀ v, ord (lf v D : Qv v) = 0)
    (hD' : ∀ v, pOf v ∣ N → (lf v D : Qv v) = finAt v h 1 1) (g : G2) :
    φ (g * h) = (ω.toIdele (IdeleGroup.ofFinite D) : ℂ) * φ g := by
  obtain ⟨u, rfl, hu⟩ := exists_finEmb h hinf
  refine hL.level u (mem_Gamma0Level_of_places N u (fun v => ?_) fun v => ?_) D hD (fun v hv => ?_) g
  · rw [hu v]; exact hint v
  · rw [hu v]; exact hlev v
  · rw [hu v]; exact hD' v hv

theorem natCast_ne_zero_at (N : ℕ) [NeZero N] (v : Pl) : (N : Qv v) ≠ 0 := by
  have h : (algebraMap ℚ (Qv v)) (N : ℚ) ≠ 0 :=
    (map_ne_zero _).2 (Nat.cast_ne_zero.2 (NeZero.ne N))
  rwa [map_natCast] at h

theorem lf_one (v : Pl) : (lf v (1 : Afˣ) : Qv v) = 1 := by
  simp [lf]

theorem lift_right_good {k N : ℕ} [NeZero N] {f : UpperHalfPlane → ℂ} {ω : HeckeCharacter ℚ}
    {φ : G2 → ℂ} (hord : ∀ v : Pl, ¬ pOf v ∣ N → ord (N : Qv v) = 0)
    (hL : Lift k N f ω φ) {h : G2} (hinf : ∀ w, infAt w h = 1)
    (hint : ∀ v : Pl, finAt v h ∈ integralGL (Qv v) 2)
    (hbad : ∀ v : Pl, pOf v ∣ N → finAt v h = 1) (g : G2) : φ (g * h) = φ g := by
  have key := lift_right hL hinf hint (fun v => ?_) 1 (fun v => ?_) (fun v hv => ?_) g
  · simpa using key
  · by_cases hv : pOf v ∣ N
    · rw [hbad v hv]; simp
    · refine inv_mul_mem_of_ord_le (natCast_ne_zero_at N v) fun h0 => ?_
      rw [hord v hv]
      exact (mem_integer_iff_ord h0).1 (((GLnLocal.mem_integralGL_iff _ 2).1 (hint v)).1 1 0)
  · rw [lf_one]; exact ord_one
  · rw [lf_one, hbad v hv]; simp

theorem ofFinite_toFinite_of_inf {a' d' : Jd} (h3 : ∀ w, infAt w (dg2 a' d' : G2) = 1) :
    IdeleGroup.ofFinite (IdeleGroup.toFinite ℚ d') = d' := by
  apply (IdeleGroup.prodEquiv ℚ).injective
  refine Prod.ext ?_ ?_
  · have e : (IdeleGroup.prodEquiv ℚ d').1 = 1 := by
      apply Units.ext
      funext w
      have h := congrArg (fun M : GL (Fin 2) _ => M 1 1) (h3 w)
      show (d' : 𝔸[ℚ]).1 w = 1
      simpa [dg2] using h
    rw [e]
    exact IdeleGroup.toInfinite_ofFinite _
  · exact IdeleGroup.toFinite_ofFinite _

theorem lift_local_invariance : Ad3.R.B0 → Ad3.R.AutomorphicLevelEquivariance := by
  intro hB k N _ hk χ hχ f a hf he ω φ hω hL
  obtain ⟨hloc, -, -, -, -, -, -, hid⟩ := hB
  have hordN : ∀ v : Pl, ord (N : Qv v) = N.factorization (pOf v) :=
    fun v => (hloc v).2.2.2.2.1 N (NeZero.ne N)
  have hgood : ∀ v : Pl, ¬ pOf v ∣ N → ord (N : Qv v) = 0 := fun v hv => by
    rw [hordN v, Nat.factorization_eq_zero_of_not_dvd hv]; rfl
  refine ⟨fun v hv x hx h hh g => ?_, fun v hv x d hxd h hh g => ?_, fun κ hκ hκ' g => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hh
    refine lift_right_good hgood hL h3 (fun v' => ?_) (fun v' hv' => ?_) g
    · by_cases e : v' = v
      · subst e; rw [h1]; exact hx
      · rw [h2 v' e]; exact one_mem _
    · refine h2 v' fun e => hv (e ▸ hv')
  · obtain ⟨h1, h2, h3⟩ := hh
    have hn : 1 ≤ N.factorization (pOf v) :=
      (hloc v).2.2.1.factorization_pos_of_dvd (NeZero.ne N) hv
    have hu : ord (d : Qv v) = 0 := ord_lower_right hn hxd
    obtain ⟨x', a', d', -, ⟨e1, e2, e3⟩, -, -, hc⟩ := hid v 0 1 d
    have hcomp : ∀ v' : Pl, (lf v' (IdeleGroup.toFinite ℚ d') : Qv v') =
        finAt v' (dg2 a' d' : G2) 1 1 := fun v' => rfl
    have hdv : (lf v (IdeleGroup.toFinite ℚ d') : Qv v) = d := by
      rw [hcomp v, e1]; simp [dg2]
    have hov : ∀ v' : Pl, v' ≠ v → (lf v' (IdeleGroup.toFinite ℚ d') : Qv v') = 1 := fun v' hv' => by
      rw [hcomp v', e2 v' hv']; simp
    have key := lift_right hL h3 (fun v' => ?_) (fun v' => ?_) (IdeleGroup.toFinite ℚ d')
      (fun v' => ?_) (fun v' hv' => ?_) g
    · rw [ofFinite_toFinite_of_inf e3, (hc ω).2] at key
      exact key
    · by_cases e : v' = v
      · subst e; rw [h1]; exact hxd.1
      · rw [h2 v' e]; exact one_mem _
    · by_cases e : v' = v
      · subst e
        rw [h1]
        refine inv_mul_mem_of_ord_le (natCast_ne_zero_at N v') fun h0 => ?_
        rw [hordN v']
        exact le_ord_of_mem h0 hxd.2.1
      · rw [h2 v' e]; simp
    · by_cases e : v' = v
      · subst e; rw [hdv]; exact hu
      · rw [hov v' e]; exact ord_one
    · by_cases e : v' = v
      · subst e; rw [hdv, h1]; exact hxd.2.2
      · rw [hov v' e, h2 v' e]; simp
  · exact lift_right_good hgood hL hκ (fun v' => κ.2.2 v') hκ' g

end GlobalTheory.CompanionTheory.RankinSelberg.LiftLevel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneFormMapEqKaehlerDifferentialMap
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge.FormBC

theorem subsingleton_of_tensor {R : Type} [CommRing R] {Q : Type} [AddCommGroup Q] [Module R Q] [Module.Finite R Q]
    {J : Type} (B : J → Type) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (hcov : ∀ p : PrimeSpectrum R, ∃ (i : J) (q : PrimeSpectrum (B i)), PrimeSpectrum.comap (algebraMap R (B i)) q = p)
    (h : ∀ i, Subsingleton (B i ⊗[R] Q)) : Subsingleton Q := by
  by_contra hQ
  rw [not_subsingleton_iff_nontrivial] at hQ
  obtain ⟨p, hp⟩ := Module.nonempty_support_of_nontrivial (R := R) (M := Q)
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hp
  obtain ⟨i, q, hq⟩ := hcov p
  have := h i
  let κ := q.asIdeal.ResidueField
  have h1 : Subsingleton (κ ⊗[R] Q) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R (B i) κ κ Q).symm.subsingleton
  have hpq : p.asIdeal = q.asIdeal.comap (algebraMap R (B i)) := by rw [← hq]; rfl
  letI : Algebra p.asIdeal.ResidueField κ :=
    (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R (B i)) hpq).toAlgebra
  haveI : IsScalarTower R p.asIdeal.ResidueField κ := .of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R (B i) κ]
    exact (Ideal.ResidueField.map_algebraMap p.asIdeal q.asIdeal (algebraMap R (B i)) hpq r).symm
  have h2 : Nontrivial (κ ⊗[p.asIdeal.ResidueField] (p.asIdeal.ResidueField ⊗[R] Q)) :=
    Module.FaithfullyFlat.lTensor_nontrivial _ _ _
  exact not_subsingleton _
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField κ κ Q).subsingleton

theorem bijective_of_lTensor {R : Type} [CommRing R] {N M : Type} [AddCommGroup N] [Module R N] [AddCommGroup M]
    [Module R M] [Module.Finite R N] [Module.Finite R M] [Module.Projective R M] (T : N →ₗ[R] M)
    {J : Type} (B : J → Type) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (hcov : ∀ p : PrimeSpectrum R, ∃ (i : J) (q : PrimeSpectrum (B i)), PrimeSpectrum.comap (algebraMap R (B i)) q = p)
    (h : ∀ i, Function.Bijective (T.lTensor (B i))) : Function.Bijective T := by
  have hs : Function.Surjective T := by
    have hQ : Subsingleton (M ⧸ LinearMap.range T) := subsingleton_of_tensor B hcov fun i ↦ by
      refine ⟨fun a b ↦ ?_⟩
      have key : ∀ x : B i ⊗[R] (M ⧸ LinearMap.range T), x = 0 := fun x ↦ by
        obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective (B i) (Submodule.mkQ_surjective (LinearMap.range T)) x
        obtain ⟨z, rfl⟩ := (h i).2 y
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, show (LinearMap.range T).mkQ ∘ₗ T = 0 from
          LinearMap.range_mkQ_comp T, LinearMap.lTensor_zero, LinearMap.zero_apply]
      rw [key a, key b]
    exact fun m ↦ LinearMap.mem_range.1 ((Submodule.Quotient.mk_eq_zero (LinearMap.range T)).1 (Subsingleton.elim (Submodule.Quotient.mk m) 0))
  obtain ⟨u, hu⟩ := Module.projective_lifting_property T LinearMap.id hs
  let r : N →ₗ[R] LinearMap.ker T := LinearMap.codRestrict _ (LinearMap.id - u ∘ₗ T) fun x ↦ by
    have := LinearMap.congr_fun hu (T x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp [this]
  have hr : r ∘ₗ (LinearMap.ker T).subtype = LinearMap.id := by
    ext x
    simp [r]
  have hrs : Function.Surjective r := fun x ↦ ⟨x.1, LinearMap.congr_fun hr x⟩
  haveI : Module.Finite R (LinearMap.ker T) := Module.Finite.of_surjective r hrs
  have hK : Subsingleton (LinearMap.ker T) := subsingleton_of_tensor B hcov fun i ↦ by
    have key : ∀ x : B i ⊗[R] LinearMap.ker T, x = 0 := fun x ↦ by
      have e : (LinearMap.ker T).subtype.lTensor (B i) x = 0 := (h i).1 <| by
        rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
          show T ∘ₗ (LinearMap.ker T).subtype = 0 from LinearMap.ext fun x ↦ x.2, LinearMap.lTensor_zero,
          LinearMap.zero_apply]
      have e2 := congrArg (r.lTensor (B i)) e
      rwa [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hr, LinearMap.lTensor_id, LinearMap.id_apply, map_zero] at e2
    exact ⟨fun a b ↦ by rw [key a, key b]⟩
  exact ⟨(injective_iff_map_eq_zero T).2 fun x hx ↦ congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : LinearMap.ker T) 0), hs⟩

theorem exists_grp {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) {X' : Scheme.{0}} (s' : X' ⟶ Sp R')
    (φ : X' ⟶ A.left) (h : IsPullback φ s' A.hom (spMap (algebraMap R R'))) :
    ∃ _ : GrpObj (Over.mk s'), IsAbelianScheme (Over.mk s') ∧ SmoothOfRelativeDimension g s' := by
  have abelian_pull {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'}
      [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left} (hG : IsAbelianScheme G)
      (h : IsGrpPullback G' G f φ) : IsAbelianScheme G' := by
    have comm : IsCommMonObj G' := by
      have := hG.comm
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
        ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨comm, MorphismProperty.of_isPullback (P := @Smooth) h.1 hG.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) h.1 hG.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hG.geomConnected⟩
  obtain ⟨C, _, ψ, hψ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A (spMap (algebraMap R R'))
  let e : C ≅ Over.mk s' := Over.isoMk (hψ.1.isoIsPullback _ _ h) (by simp)
  let _ : GrpObj (Over.mk s') := GrpObj.ofIso e
  have : IsMonHom e.hom := inferInstance
  have hC := abelian_pull hA hψ
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  exact ⟨inferInstance, abelian_pull hC (GlobalTheory.SymExtendDvr.isGrpPullback_of_iso e.symm),
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) h hg⟩

theorem lTensor_bijective_of_isBaseChange {S B N M P : Type} [CommRing S] [CommRing B] [Algebra S B]
    [AddCommGroup N] [Module S N] [AddCommGroup M] [Module S M] [AddCommGroup P] [Module S P] [Module B P]
    [IsScalarTower S B P] (T : N →ₗ[S] M) (ev : M →ₗ[S] P) (h₁ : IsBaseChange B ev)
    (h₂ : IsBaseChange B (ev ∘ₗ T)) : Function.Bijective (T.lTensor B) := by
  have e : ∀ x, h₁.equiv (T.lTensor B x) = h₂.equiv x := fun x ↦ by
    induction x with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul b n => simp [IsBaseChange.equiv_tmul]
  refine (Function.Bijective.of_comp_iff' h₁.equiv.bijective _).1 ?_
  have e' : (h₁.equiv ∘ T.lTensor B) = h₂.equiv := funext e
  rw [e']
  exact h₂.equiv.bijective

theorem oneFormMap_eq_kaehlerDifferential_map {R R' B B' : Type} [CommRing R] [CommRing R'] [CommRing B] [CommRing B'] [Algebra R R'] [Algebra R B]
    [Algebra R' B'] [Algebra B B'] [Algebra R B'] [IsScalarTower R R' B'] [IsScalarTower R B B']
    (hα : SemiHom (algebraMap R R') (algebraMap B B')) (x : Ω[B⁄R]) :
    hα.m1 x = KaehlerDifferential.map R R' B B' x := by
  induction x using ind1 with
  | h b c =>
    rw [SemiHom.oneFormMap_smul_semilinear, SemiHom.m1_D, map_smul, KaehlerDifferential.map_D, algebraMap_smul]
  | h0 => simp
  | ha x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem isBaseChange_of_isPushout {R R' B B' W : Type} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    [Algebra R R'] [Algebra R B] [Algebra R' B'] [Algebra B B'] [Algebra R B'] [IsScalarTower R R' B']
    [IsScalarTower R B B'] [Algebra.IsPushout R R' B B'] [AddCommGroup W] [Module R W] (ev : W →ₗ[R] Ω[B⁄R])
    (hev : IsBaseChange B ev) (hα : SemiHom (algebraMap R R') (algebraMap B B'))
    (u : R' ⊗[R] W →ₗ[R'] Ω[B'⁄R']) (hu : ∀ c, u (1 ⊗ₜ c) = hα.m1 (ev c)) : IsBaseChange B' u := by
  have h₁ : IsBaseChange B' (KaehlerDifferential.map R R' B B') :=
    IsBaseChange.of_equiv (KaehlerDifferential.tensorKaehlerEquiv R R' B B') fun x ↦ by
      have hx : x ∈ Submodule.span B (Set.range (KaehlerDifferential.D R B)) :=
        (KaehlerDifferential.span_range_derivation R B).ge Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        simp
      | zero => simp
      | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), hx, hy]
      | smul a x _ hx =>
        rw [TensorProduct.tmul_smul, ← algebraMap_smul B', map_smul, hx, map_smul, algebraMap_smul]
  have h₂ := IsBaseChange.comp hev h₁
  refine IsBaseChange.of_comp (TensorProduct.isBaseChange R W R') ?_
  convert h₂ using 1
  refine LinearMap.ext fun c ↦ ?_
  exact (hu c).trans (oneFormMap_eq_kaehlerDifferential_map hα _)

section Main

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'}
  {φ : X' ⟶ X}

def pairOf (h : IsPullback φ s' s (spMap (algebraMap R R'))) (U : X.affineOpens) : Pair φ :=
  ⟨(⟨φ ⁻¹ᵁ U.1, GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback h U.2⟩, U), le_rfl⟩

theorem isBaseChange_at (h : IsPullback φ s' s (spMap (algebraMap R R'))) (hP : Par (OAff s)) (U : X.affineOpens)
    (u : R' ⊗[R] GlobForm s →ₗ[R'] Ω[Sec s' (φ ⁻¹ᵁ U.1)⁄R'])
    (hu : ∀ c : GlobForm s, u (1 ⊗ₜ c) = (semiHom_secPull h.w (pairOf h U)).m1 (c.1 (op U))) :
    IsBaseChange (Sec s' (φ ⁻¹ᵁ U.1)) u := by
  letI : Algebra (Sec s U.1) (Sec s' (φ ⁻¹ᵁ U.1)) := (CechDR.secPull s s' (pairOf h U)).toAlgebra
  letI : Algebra R (Sec s' (φ ⁻¹ᵁ U.1)) :=
    ((algebraMap R' (Sec s' (φ ⁻¹ᵁ U.1))).comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' (Sec s' (φ ⁻¹ᵁ U.1)) := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower R (Sec s U.1) (Sec s' (φ ⁻¹ᵁ U.1)) :=
    .of_algebraMap_eq fun r ↦ ((semiHom_secPull h.w (pairOf h U)).map_algebraMap r).symm
  haveI : Algebra.IsPushout R R' (Sec s U.1) (Sec s' (φ ⁻¹ᵁ U.1)) :=
    CommRingCat.isPushout_iff_isPushout.mp (GlobalTheory.AbLaw.isPushout_cst h U.2 rfl)
  exact isBaseChange_of_isPushout (B := Sec s U.1) (B' := Sec s' (φ ⁻¹ᵁ U.1)) (evForm (OAff s) (op U)) (hP (op U))
    (semiHom_secPull h.w (pairOf h U)) u hu

theorem exists_prime (h : IsPullback φ s' s (spMap (algebraMap R R'))) (e : Sp R' ⟶ X') (he : e ≫ s' = 𝟙 _)
    (p : PrimeSpectrum R') : ∃ (U : X.affineOpens) (q : PrimeSpectrum (Sec s' (φ ⁻¹ᵁ U.1))),
      PrimeSpectrum.comap (algebraMap R' (Sec s' (φ ⁻¹ᵁ U.1))) q = p := by
  let y : Sp R' := p
  obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := φ (e y)) trivial
  have hU' := GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback h hV
  refine ⟨⟨V, hV⟩, hU'.primeIdealOf ⟨e y, hx⟩, ?_⟩
  have e₁ := hU'.fromSpec_primeIdealOf ⟨e y, hx⟩
  have e₂ := affPt_w s' ⟨φ ⁻¹ᵁ V, hU'⟩
  have e₃ := congrArg (fun f ↦ f (hU'.primeIdealOf ⟨e y, hx⟩)) e₂
  have e₄ : s' (e y) = y := by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  have e₅ : s' (hU'.fromSpec (hU'.primeIdealOf ⟨e y, hx⟩)) =
      spMap (algebraMap R' (Sec s' (φ ⁻¹ᵁ V))) (hU'.primeIdealOf ⟨e y, hx⟩) :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans e₃
  exact ((congrArg (fun z ↦ s' z) e₁).symm.trans e₅).symm.trans e₄

end Main

theorem formBC : SteinSt → ParSt → FormBCSt := by
  intro _ hPar R _ A _ g hA hg R' _ _ X' s' φ h
  obtain ⟨_, hA', hg'⟩ := exists_grp A g hA hg s' φ h
  obtain ⟨hP, hV⟩ := hPar R A g hA hg
  obtain ⟨hP', hV'⟩ := hPar R' (Over.mk s') g hA' hg'
  replace hP' : Par (OAff s') := hP'
  replace hV' : VB R' (GlobForm s') g := hV'
  obtain ⟨f₁, f₂, -⟩ := hV'
  obtain ⟨f₃, -, -⟩ := hV
  let _ : Module R (GlobForm s') := Module.compHom _ (algebraMap R R')
  have : IsScalarTower R R' (GlobForm s') := .of_algebraMap_smul fun _ _ ↦ rfl
  let T : R' ⊗[R] GlobForm A.hom →ₗ[R'] GlobForm s' := LinearMap.liftBaseChange R'
    { toFun := pullForm h.w
      map_add' := map_add _
      map_smul' := (pullForm h.w).map_smulₛₗ }
  have hT : ∀ c : GlobForm A.hom, T (1 ⊗ₜ c) = pullForm h.w c := fun c ↦ by simp [T]
  let e : Sp R' ⟶ X' := (η[Over.mk s'] : 𝟙_ (Over (Sp R')) ⟶ Over.mk s').left
  have he : e ≫ s' = 𝟙 _ := Over.w (η[Over.mk s'] : 𝟙_ (Over (Sp R')) ⟶ Over.mk s')
  have hb : Function.Bijective T :=
    bijective_of_lTensor T (fun U : A.left.affineOpens ↦ Sec s' (φ ⁻¹ᵁ U.1)) (exists_prime h e he) fun U ↦ ?_
  · exact ⟨LinearEquiv.ofBijective T hb, fun c ↦ by
      have : LinearEquiv.ofBijective T hb (1 ⊗ₜ c) = pullForm h.w c := hT c
      rw [this]
      exact isPullForm_pullForm h.w c⟩
  · refine lTensor_bijective_of_isBaseChange T (evForm (OAff s') (op ⟨φ ⁻¹ᵁ U.1, GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback h U.2⟩)) (hP' _) ?_
    refine isBaseChange_at h hP U _ fun c ↦ ?_
    have k := isPullForm_iff.1 (isPullForm_pullForm h.w c) (pairOf h U)
    exact (congrArg (fun z : GlobForm s' ↦ z.1 (op (pairOf h U).1.1)) (hT c)).trans k.symm

end GlobalTheory.CompanionTheory.Hodge.FormBC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatSplit
section
noncomputable section

open NumberField IsDedekindDomain Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SatSplitAt

theorem satSplit : PositivityTheory.Rg.BcB.F.RS.SatSplit := by
  rintro E _ _ _ n π D w B ⟨σ, hc, hs⟩ ⟨b, hb, rfl⟩
  obtain ⟨P, hsub, -, hsat⟩ := GlobalTheory.PfBCI.unram_component D.h w (D.σ · w) b hb
  obtain ⟨α, hα, hσ⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ _).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hs⟩)
  obtain ⟨y, hy⟩ := hsat.exists_vec
  have hP : GlobalTheory.SmGL.HasSatake P.ρ α :=
    GlobalTheory.CompanionTheory.SatComp.hasSatake_of_isSatVecGL ⟨P.smooth, P.irred⟩ α (hα ▸ hy)
  obtain ⟨e⟩ := GlobalTheory.SmGL.SphUniq.equiv_of_parInd _ _ hP.1 hσ.1 hP.2.2 hσ.2.2 hP.2.1 hσ.2.1
  exact ⟨σ, (GlobalTheory.SmGL.IsSubquotient.of_surjective e.toIntertwiningMap e.toLinearEquiv.surjective).trans hsub, hc⟩

end GlobalTheory.CompanionTheory.SatSplitAt

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportSubschemeEmbedding
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.SubEmb

theorem subEmbedding : Ysupp.SubEmbedding :=
  subEmbedding_of_stage GlobalTheory.T.product_irreducible_append_equiv

end GlobalTheory.CompanionTheory.SubEmb
end

