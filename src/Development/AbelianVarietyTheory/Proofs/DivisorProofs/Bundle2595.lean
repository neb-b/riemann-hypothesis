module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2504
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedIsoPulledBackPeriodRelation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackPeriodConstantsMultiplicative
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2556
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2418
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2521
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalNoetherianStalkFactorOfFieldPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

namespace GlobalTheory.Poinc.Sep.Spz

theorem exists_stalk_factor : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (R : Subalgebra o Ω) (K : Type) [Field K] (x : Sp K ⟶ M.Z) (yK : R →+* K), (∀ a ∈ R, a ∈ M.O (x (closedPoint K))) → (∀ a : R, yK a = M.val x a) → ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsNoetherianRing O) (_ : IsIntegrallyClosed O) (_ : Algebra O Ω) (_ : IsFractionRing O Ω) (xO : Sp O ⟶ M.Z) (u : R →+* O) (v : O →+* K), spMap (algebraMap O Ω) ≫ xO = M.pt ∧ (algebraMap O Ω).comp u = R.val.toRingHom ∧ spMap v ≫ xO = x ∧ v.comp u = yK := by
  intro o Ω _ _ _ _ M hN R K _ x yK hR hy
  haveI := ArithBase.ded (o := o) (Ω := Ω)
  haveI := M.lft
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  haveI : IsIntegrallyClosed (M.O (x (closedPoint K))) := RatModel.isIntegrallyClosed_O (M := M) hN _
  haveI : IsNoetherianRing (M.O (x (closedPoint K))) :=
    isNoetherianRing_of_ringEquiv _ (M.stalkEquiv (x (closedPoint K)))
  have h1 : CommRingCat.ofHom (M.stalkEquiv (x (closedPoint K))).toRingHom ≫
      CommRingCat.ofHom (algebraMap (M.O (x (closedPoint K))) Ω) =
      M.Z.presheaf.stalkSpecializes (M.pt_specializes (closedPoint Ω) (x (closedPoint K))) ≫
        Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt := by
    ext a; rfl
  have h3 : CommRingCat.ofHom (M.stalkEquiv (x (closedPoint K))).toRingHom ≫
      CommRingCat.ofHom (RatModel.valLoc x (x (closedPoint K)) specializes_rfl) =
      M.Z.presheaf.stalkSpecializes (specializes_rfl (x := x (closedPoint K))) ≫
        Scheme.stalkClosedPointTo (R := CommRingCat.of K) x := by
    ext a; simp [RatModel.valLoc]
  refine ⟨M.O (x (closedPoint K)), inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, spMap (M.stalkEquiv (x (closedPoint K))).toRingHom ≫ M.Z.fromSpecStalk (x (closedPoint K)),
    (Subalgebra.inclusion (fun a ha => hR a ha) : R →ₐ[o] M.O (x (closedPoint K))).toRingHom,
    RatModel.valLoc x (x (closedPoint K)) specializes_rfl, ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, spMap, spMap, ← Spec.map_comp, h1, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · ext a; rfl
  · rw [← Category.assoc, spMap, spMap, ← Spec.map_comp, h3, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · ext a
    simp [RatModel.valLoc_eq_val, hy]

end GlobalTheory.Poinc.Sep.Spz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenImmersionBigCellBaseAffineCoords
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

noncomputable section

namespace GlobalTheory.LogPole.CellBir

theorem spMap_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem isIso_spMap_of_inverse {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : B →+* A)
    (h₁ : f.comp g = RingHom.id B) (h₂ : g.comp f = RingHom.id A) : IsIso (spMap f) :=
  inferInstanceAs (IsIso (Spec.map (RingEquiv.toCommRingCatIso (RingEquiv.ofRingHom f g h₁ h₂)).hom))

theorem isOpenImmersion_spMap_away {R : Type} [CommRing R] (g : R) :
    IsOpenImmersion (spMap (algebraMap R (Localization.Away g))) := IsOpenImmersion.of_isLocalization g


set_option maxHeartbeats 3000000 in
theorem exists_isOpenImmersion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N), Nonempty W → ∃ V : (Spec (CommRingCat.of Γ(Y₀ TF.X Z, W))).Opens, Nonempty V ∧ IsOpenImmersion (V.ι ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)))) := by

  intro E _ _ _ H Dw l Xo c TF Z hF U n e v hv W k L N h hW
  obtain ⟨g, hnil, hU0, z, hz, hzU, hC, hX⟩ := GlobalTheory.T.exists_bigCell_point_basicOpen_affineSpace_coords E H Dw l Xo c TF Z hF U n e v hv W k L N h hW
  obtain ⟨φ, hφ⟩ : ∃ φ : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1) →+* Γ(Y₀ TF.X Z, W),
    φ = MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N) := ⟨_, rfl⟩
  rw [← hφ] at hnil hU0 ⊢
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = ev z W hz := ⟨_, rfl⟩
  have hψφ : ψ.comp φ = algebraMap _ (Localization.Away g) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, hφ, MvPolynomial.eval₂Hom_C, hψ]
      exact hC r
    · intro i
      simp only [RingHom.comp_apply, hφ, MvPolynomial.eval₂Hom_X', hψ]
      exact hX i
  have hψu : IsUnit (ψ (φ g)) := by
    rw [← RingHom.comp_apply, hψφ]
    exact IsLocalization.Away.algebraMap_isUnit g
  obtain ⟨ψ', hψ'c⟩ : ∃ ψ' : Localization.Away (φ g) →+* Localization.Away g, ψ'.comp (algebraMap _ _) = ψ :=
    ⟨_, IsLocalization.Away.lift_comp (φ g) hψu⟩
  obtain ⟨θ, hθc⟩ : ∃ θ : Localization.Away g →+* Localization.Away (φ g),
      θ.comp (algebraMap _ _) = (algebraMap _ (Localization.Away (φ g))).comp φ :=
    ⟨Localization.awayMap φ g, IsLocalization.map_comp _⟩

  have hz₀ : ⊤ ≤ (spMap (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g))) ≫ GlobalTheory.FlagMod.tau h.1) ⁻¹ᵁ W :=
    GlobalTheory.FlagMod.le_preimage_comp _ (GlobalTheory.FlagMod.tau_le h.1 le_rfl)
  have ev₀ := GlobalTheory.FlagMod.ev_spMap_tau h.1 (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g))) hz₀
  have hz' : ⊤ ≤ (spMap θ ≫ z) ⁻¹ᵁ W := GlobalTheory.FlagMod.le_preimage_comp _ hz
  have ev' : ev (spMap θ ≫ z) W hz' = θ.comp ψ := by rw [hψ]; exact GlobalTheory.FlagMod.ev_spMap θ z W hz hz'
  have hcomp : ∀ p, θ (ψ (φ p)) = algebraMap _ (Localization.Away (φ g)) (φ p) := fun p => by
    rw [← RingHom.comp_apply ψ φ, hψφ, ← RingHom.comp_apply θ, hθc, RingHom.comp_apply]
  have heq : spMap θ ≫ z = spMap (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g))) ≫ GlobalTheory.FlagMod.tau h.1 := by
    refine GlobalTheory.T.bigCell_point_eq_of_base_and_cellCoordinates_eq E H Dw l Xo c TF Z hF U n e v hv W k L N h _ _ _ hz' hz₀
      (GlobalTheory.FlagMod.le_preimage_comp _ hzU) (hU0 _ _ hz₀ (by
        rw [ev₀]; exact IsLocalization.Away.algebraMap_isUnit _)) (fun r => ?_) (fun i => ?_)
    · have := hcomp (MvPolynomial.C r)
      simp only [hφ, MvPolynomial.eval₂Hom_C] at this
      rw [ev', ev₀, RingHom.comp_apply]
      exact this
    · have := hcomp (MvPolynomial.X i)
      simp only [hφ, MvPolynomial.eval₂Hom_X'] at this
      rw [ev', ev₀, RingHom.comp_apply]
      exact this
  have hθψ : θ.comp ψ = algebraMap _ (Localization.Away (φ g)) := by
    exact ev'.symm.trans ((GlobalTheory.FlagMod.ev_congr heq W hz' hz₀).trans ev₀)
  have h1 : ψ'.comp θ = RingHom.id _ :=
    IsLocalization.ringHom_ext (Submonoid.powers g)
      ((congrArg (ψ'.comp ·) hθc).trans ((congrArg (·.comp φ) hψ'c).trans hψφ))
  have h2 : θ.comp ψ' = RingHom.id _ :=
    IsLocalization.ringHom_ext (Submonoid.powers (φ g)) ((congrArg (θ.comp ·) hψ'c).trans hθψ)
  haveI : Nontrivial (Localization.Away (φ g)) := OreLocalization.nontrivial_iff.mpr hnil
  haveI : IsOpenImmersion (spMap (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g)))) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g))))))
  refine ⟨(spMap (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g)))).opensRange, ?_, ?_⟩
  · have x : Sp (Localization.Away (φ g)) :=
      (inferInstance : Nonempty (PrimeSpectrum (Localization.Away (φ g)))).some
    exact ⟨⟨_, Set.mem_range_self x⟩⟩
  · have key : ((spMap (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g)))).opensRange).ι =
        (spMap (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g)))).isoOpensRange.inv ≫
          spMap (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g))) := by
      exact (Iso.eq_inv_comp _).2 (Scheme.Hom.isoOpensRange_hom_ι _)
    have hfac : spMap (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g))) ≫ spMap φ =
        spMap θ ≫ spMap (algebraMap _ (Localization.Away g)) :=
      (spMap_comp_ringHom φ _).trans ((congrArg spMap hθc.symm).trans (spMap_comp_ringHom _ θ).symm)
    haveI : IsIso (spMap θ) := isIso_spMap_of_inverse θ ψ' h2 h1
    haveI := isOpenImmersion_spMap_away g
    have hoi : IsOpenImmersion ((spMap (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g)))).isoOpensRange.inv ≫
        spMap θ ≫ spMap (algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) (Localization.Away g))) := inferInstance
    rw [← hfac, ← Category.assoc, ← key] at hoi
    exact hoi

end GlobalTheory.LogPole.CellBir
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointsFramesThetaSectionGenericFibreMemberStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_points_frames_thetaSection_genericFibre_member : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∃ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1) (ρ : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ∧ (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) ∧ (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) ∧ ρ.IsGen ∧ ∀ a, IsTorsFrame 𝔪.A ρ (X₁.S.r * X₁.S.N) (x a) (fr a) := by
  first | exact @GlobalTheory.Poinc.IntTerm.exists_points_frames_theta | exact GlobalTheory.Poinc.IntTerm.exists_points_frames_theta | (intros; apply GlobalTheory.Poinc.IntTerm.exists_points_frames_theta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedE8ThetaPowerOverModuliStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polarised_E8ThetaPower_over_moduli : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∃ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))), P.g = 8 * g ∧ GlobalTheory.Poinc.SharpOver F W P (𝟙 F.X) ∧ rig.IsGen ∧ (letI := P.isAb.comm; HypS P.A P.L) := by
  first | exact @GlobalTheory.SiegEighth.exists_polAV_sharpOver | exact GlobalTheory.SiegEighth.exists_polAV_sharpOver | (intros; apply GlobalTheory.SiegEighth.exists_polAV_sharpOver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosDefGrD
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2.SchurRow

theorem schur {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (M : Matrix (A ⊕ B) (A ⊕ B) ℂ)
    (hM : M.PosDef) : ∃ Q : Matrix B B ℂ, Q.PosDef ∧ Q.det * M.toBlocks₁₁.det = M.det ∧ ∀ w : B → ℂ,
      (Matrix.fromBlocks (1 : Matrix A A ℂ) 0 0 (Matrix.of fun (_ : Unit) b => w b) * M *
        (Matrix.fromBlocks (1 : Matrix A A ℂ) 0 0 (Matrix.of fun (_ : Unit) b => w b))ᴴ).det =
        M.toBlocks₁₁.det * ∑ a, ∑ b, w a * Q a b * star (w b) := by
  have h11 : M.toBlocks₁₁.PosDef := hM.submatrix Sum.inl_injective
  have e : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₁₂ᴴ M.toBlocks₂₂ := by
    ext (a | a) (b | b) <;> try rfl
    exact (hM.isHermitian.apply _ _).symm
  generalize M.toBlocks₁₁ = P at h11 e
  generalize M.toBlocks₁₂ = R at e
  generalize M.toBlocks₂₂ = S at e
  subst e
  have := h11.isUnit.invertible
  have hd := Matrix.det_fromBlocks₁₁ P R Rᴴ S
  rw [Matrix.invOf_eq_nonsing_inv] at hd
  refine ⟨S - Rᴴ * P⁻¹ * R, ?_, by rw [hd, mul_comm], fun w => ?_⟩
  · refine ((h11.fromBlocks₁₁ R S).1 hM.posSemidef).posDef_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 ?_)
    have := hM.det_pos.ne'
    rw [hd] at this
    exact (right_ne_zero_of_mul this).isUnit
  · generalize hW : (Matrix.of fun (_ : Unit) b => w b) = W
    have : Matrix.fromBlocks (1 : Matrix A A ℂ) 0 0 W * Matrix.fromBlocks P R Rᴴ S *
        (Matrix.fromBlocks (1 : Matrix A A ℂ) 0 0 W)ᴴ = Matrix.fromBlocks P (R * Wᴴ) (W * Rᴴ) (W * S * Wᴴ) := by
      simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    rw [this, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
    have e2 : W * S * Wᴴ - W * Rᴴ * P⁻¹ * (R * Wᴴ) = W * (S - Rᴴ * P⁻¹ * R) * Wᴴ := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    rw [e2]
    congr 1
    rw [Matrix.det_unique, Finset.sum_comm]
    subst hW
    generalize S - Rᴴ * P⁻¹ * R = Q
    simp [Matrix.mul_apply, Finset.sum_mul]

noncomputable def ixA {s : ℕ} (i : Fin s) : {a : Fin s // (a : ℕ) < i} ⊕ Option {j : Low s // j.1.2 = i} ≃ Fin s :=
  Equiv.ofBijective (Sum.elim Subtype.val fun b => Option.elim b i fun j => j.1.1.1) (by
    constructor
    · rintro (⟨a, ha⟩ | _ | ⟨⟨⟨a, a'⟩, ha⟩, h'⟩) (⟨b, hb⟩ | _ | ⟨⟨⟨b, b'⟩, hb⟩, h⟩) e <;>
        simp only [Sum.elim_inl, Sum.elim_inr, Option.elim] at e <;> (try dsimp only at h) <;>
        (try dsimp only at h') <;> (try dsimp only at ha) <;> (try dsimp only at hb) <;> subst_vars <;>
        first | rfl | (exfalso; omega)
    · intro c
      rcases lt_trichotomy c i with h | h | h
      exacts [⟨.inl ⟨c, h⟩, rfl⟩, ⟨.inr none, h.symm⟩, ⟨.inr (some ⟨⟨(c, i), h⟩, rfl⟩), rfl⟩])

noncomputable def ixB {s : ℕ} (i : Fin s) : {a : Fin s // (a : ℕ) < i} ⊕ Unit ≃ {a : Fin s // (a : ℕ) < i + 1} :=
  Equiv.ofBijective (Sum.elim (fun a => ⟨a.1, a.2.trans (Nat.lt_succ_self _)⟩) fun _ => ⟨i, Nat.lt_succ_self _⟩) (by
    constructor
    · rintro (⟨a, ha⟩ | _) (⟨b, hb⟩ | _) e <;>
        simp only [Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at e <;> subst_vars <;>
        first | rfl | (exfalso; omega)
    · rintro ⟨c, hc⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with h | h
      exacts [⟨.inl ⟨c, h⟩, rfl⟩, ⟨.inr (), Subtype.ext (Fin.ext h.symm)⟩])

theorem det_upU {s : ℕ} (y : Low s → ℂ) : (upU y).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [upU]
  · intro a b h
    have h : b < a := h
    simp [upU, h.not_gt, h.ne']

theorem row_lt {s : ℕ} {i : Fin s} {y y' : Low s → ℂ} (h : ∀ j : Low s, j.1.2 < i → y' j = y j) {a : Fin s}
    (ha : a < i) : upU y' a = upU (fun j => if j.1.2 < i then y j else 0) a := by
  funext c
  simp only [upU, Matrix.of_apply]
  split_ifs with h1
  · exact h _ ha
  all_goals rfl

theorem row_ge {s : ℕ} {i : Fin s} (y : Low s → ℂ) {a : Fin s} (ha : i ≤ a) (c : Fin s) :
    upU (fun j => if j.1.2 < i then y j else 0) a c = if a = c then 1 else 0 := by
  simp only [upU, Matrix.of_apply, ha.not_gt, if_false]
  split_ifs with h1 h2
  · exact absurd h2 h1.ne
  all_goals rfl

theorem rows_eq {s : ℕ} {i : Fin s} {y y' : Low s → ℂ} (h : ∀ j : Low s, j.1.2 < i → y' j = y j) :
    (upU y').submatrix (fun a => (ixB i a).1) id =
      Matrix.fromBlocks 1 0 0 (Matrix.of fun (_ : Unit) (b : Option {j : Low s // j.1.2 = i}) =>
        (Option.elim b 1 (fun b => y' b.1) : ℂ)) *
        (upU (fun j => if j.1.2 < i then y j else 0)).submatrix (ixA i) id := by
  refine Matrix.ext ?_
  rintro (a | a) c <;> refine Eq.trans ?_ Matrix.mul_apply.symm
  · simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, Matrix.one_apply, ite_mul, one_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.submatrix_apply, id]
    exact congrFun (row_lt h a.2) c
  · simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, Matrix.submatrix_apply, id, Matrix.of_apply]
    have hr : ∀ b, upU (fun j => if j.1.2 < i then y j else 0) (ixA i (.inr b)) c =
        if ixA i (.inr b) = c then 1 else 0 := by
      rintro (_ | ⟨j, rfl⟩)
      exacts [row_ge y le_rfl c, row_ge y (le_of_lt j.2) c]
    simp only [hr]
    change upU y' i c = _
    obtain ⟨c | c, rfl⟩ := (ixA i).surjective c
    · have h1 : ixA i (.inl c) < i := c.2
      simp [upU, h1.not_gt, h1.ne']
    · simp only [EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      obtain _ | ⟨⟨⟨b, a⟩, hab⟩, rfl⟩ := c
      · change upU y' i i = 1
        simp [upU]
      · exact dif_pos hab

theorem conj_mul {A B C : Type} [Fintype B] [Fintype C] (W : Matrix A B ℂ) (R : Matrix B C ℂ) (G : Matrix C C ℂ) :
    W * R * G * (W * R)ᴴ = W * (R * G * Rᴴ) * Wᴴ := by
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

end GlobalTheory.FlagCell2.SchurRow


open GlobalTheory.FlagCell2.SchurRow in
theorem GlobalTheory.FlagCell2.exists_posDef_grD : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ), G.PosDef → ∀ (y : Low s → ℂ) (i : Fin s), ∃ Q : Matrix (Option {j : Low s // j.1.2 = i}) (Option {j : Low s // j.1.2 = i}) ℂ, Q.PosDef ∧ Q.det * leadMinor (upU y * G * (upU y)ᴴ) i = G.det ∧ ∀ y' : Low s → ℂ, (∀ j : Low s, j.1.2 < i → y' j = y j) → grD (upU y' * G * (upU y')ᴴ) i = (∑ a, ∑ b, Option.elim a 1 (fun a => y' a.1) * Q a b * star (Option.elim b 1 (fun b => y' b.1))).re := by
  intro s G hG y i
  set U := upU (fun j : Low s => if j.1.2 < i then y j else 0) with hU
  have hdU : U.det = 1 := det_upU _
  have hM0 : (U * G * Uᴴ).PosDef := hG.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (by simp [hdU])))
  have hM : ((U * G * Uᴴ).submatrix (ixA i) (ixA i)).PosDef := hM0.submatrix (ixA i).injective
  obtain ⟨Q, hQ, hdet, hw⟩ := schur _ hM
  have hpos : 0 < ((U * G * Uᴴ).submatrix (ixA i) (ixA i)).toBlocks₁₁.det := (hM.submatrix Sum.inl_injective).det_pos
  have h11 : ∀ y' : Low s → ℂ, (∀ j : Low s, j.1.2 < i → y' j = y j) → leadMinor (upU y' * G * (upU y')ᴴ) i =
      ((U * G * Uᴴ).submatrix (ixA i) (ixA i)).toBlocks₁₁.det := fun y' h => by
    unfold leadMinor
    congr 1
    ext a b
    change (upU y' * G * (upU y')ᴴ) a b = (U * G * Uᴴ) a b
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, row_lt h a.2, row_lt h b.2, hU]
  refine ⟨Q, hQ, ?_, fun y' h => ?_⟩
  · rw [h11 y fun _ _ => rfl, hdet, Matrix.det_submatrix_equiv_self]
    simp [hdU]
  · have e := hw fun b => Option.elim b 1 (fun b => y' b.1)
    replace e : leadMinor (upU y' * G * (upU y')ᴴ) (i + 1) = _ := Eq.trans (by
      unfold leadMinor
      rw [← Matrix.det_submatrix_equiv_self (ixB i)]
      congr 1
      have e1 : (U * G * Uᴴ).submatrix (ixA i) (ixA i) = U.submatrix (ixA i) id * G * (U.submatrix (ixA i) id)ᴴ := rfl
      have e2 : ((upU y' * G * (upU y')ᴴ).submatrix (Subtype.val : {a : Fin s // (a : ℕ) < i + 1} → Fin s)
          Subtype.val).submatrix (ixB i) (ixB i) =
          (upU y').submatrix (fun a => (ixB i a).1) id * G * ((upU y').submatrix (fun a => (ixB i a).1) id)ᴴ := rfl
      rw [e1, e2, rows_eq h]
      exact conj_mul _ _ _) e
    rw [grD, e, h11 y' h]
    generalize ((U * G * Uᴴ).submatrix (ixA i) (ixA i)).toBlocks₁₁.det = d at hpos
    obtain ⟨h1, h2⟩ := Complex.pos_iff.1 hpos
    rw [Complex.mul_re, ← h2, zero_mul, sub_zero, mul_div_cancel_left₀ _ h1.ne']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPulledBackPeriodsBasePeriodsConstForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem exists_periods_of_pull : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → LBIso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂') → (∀ a : Fin L.T.r → ℤ, ∃ x : Sp V₁ ⟶ B'.left, x ≫ B'.hom = 𝟙 _ ∧ x ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ x ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∃ q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ, (∀ a b, q a b = q b a) ∧ (∀ a a' b, q (a + a') b = q a b * q a' b) ∧ (∀ a, a ≠ 0 → ∃ w ∈ maximalIdeal V₁, w ≠ 0 ∧ (q a a : FractionRing V₁) = algebraMap V₁ _ w) ∧ ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (f₂ : V₁ →+* V₂) (fK : FractionRing V₁ →+* FractionRing V₂) {I : Type} [Fintype I] (s : I → V₂) (ε : I → LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)), IsCN V₂ → Function.Injective f₂ → f₂.Finite → IsLocalHom f₂ → (∀ a, fK (algebraMap V₁ _ a) = algebraMap V₂ _ (f₂ a)) → (∀ a b, fK (q a b : FractionRing V₁) = ∏ k, algebraMap V₂ _ (s k) ^ ((n : ℤ) * ε k a b)) → ∀ (D' : DegData V₂ (maximalIdeal V₂)) (hD : IsPullDeg (f₂.comp f₁) D.toPre D'.toPre), DegFrom L.T (f₂.comp κ₁) s ε n D'.toPre (hD.xe.trans (e₀.symm.trans e.symm)) := by
  intro n V _ _ _ D r e₀ L V₁ _ _ _ f₁ κ₁ e B' _ β' β'' β₂ β₂' hV hVd h1 h1d hi hf hl hκ p₁ p₂ s₁ s₂ lb pts
  choose x hx using pts
  let y : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B') := fun a => Over.homMk (x a) (hx a).1
  have hy : ∀ a, (y a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧
      (y a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left := fun a => ⟨(hx a).2.1, (hx a).2.2⟩
  obtain ⟨w₁, q, hg, hn, hP⟩ :=
    _root_.GlobalTheory.TChart.Ratio.exists_normIso_periodRel n V D r e₀ L V₁ f₁ κ₁ e B' β' β'' β₂ β₂' hV hVd h1 h1d hi hf hl hκ p₁ p₂ s₁ s₂ lb y hy
  exact ⟨q, _root_.GlobalTheory.TChart.periodConst_symm n V D r e₀ L V₁ f₁ κ₁ e B' β' β'' β₂ β₂' hV hVd h1 h1d hi hf hl hκ p₁ p₂ s₁ s₂ y hy w₁ q hg hP hn,
    _root_.GlobalTheory.TChart.PeriodAdd.period_add n V D r e₀ L V₁ f₁ κ₁ e B' β' β'' β₂ β₂' hV hVd h1 h1d hi hf hl hκ p₁ p₂ s₁ s₂ y hy w₁ q hg hP hn,
    _root_.GlobalTheory.PeriodPos.periods_pos_diag n V D r e₀ L V₁ f₁ κ₁ e B' β' β'' β₂ β₂' hV hVd h1 h1d hi hf hl hκ p₁ p₂ s₁ s₂ y hy w₁ q hg hP,
    _root_.GlobalTheory.PullFrom.degFrom_of_periodRel n V D r e₀ L V₁ f₁ κ₁ e B' β' β'' β₂ β₂' hV hVd h1 h1d hi hf hl hκ p₁ p₂ s₁ s₂ y hy w₁ q hg hP⟩

end GlobalTheory.TChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientKernelPolarisationDescendedBundle
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualQuot

theorem exists_quotient_lam : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∃ (B : Over (Sp R)) (P : LB (A ⊗ B).left) (q : A ⟶ B) (hP : Fam A P), Good g B.hom ∧ FinAff B.left ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧ (∀ (Y : Over (Sp R)) (a x : Y ⟶ A), evc hP.isLB a (x ≫ q) = GlobalTheory.CechPic.pull (a * x).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) - GlobalTheory.CechPic.pull x.left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL)) ∧ (∀ (Y : Over (Sp R)) (x y : Y ⟶ A), x ≫ q = y ≫ q ↔ GlobalTheory.MemKL A L (x * y⁻¹)) := by
  intro R _ _ A _ g hA hg L hL hamp
  obtain ⟨H, _, i, hi, hmono, hHf, hHfl, hrep⟩ := _root_.GlobalTheory.kernel_finiteFlat_subgroup R A hA L hL hamp
  obtain ⟨B, _, q, π, hB, hq, hqf, hqfl, hqs, hπ, hpb⟩ := _root_.GlobalTheory.AbQuotientAny.exists_quotient_abelianScheme R A H i hA hi hmono hHf hHfl
  obtain ⟨P₀, hP₀, hform⟩ := _root_.GlobalTheory.QuotDesc.exists_descent_lam R A hA L hL H i hi hmono hHf hHfl hrep B q hB hq hqf hqfl hqs hpb
  have hc := hA.comm
  let c : A ⊗ B ⟶ A ⊗ B := snd A B ≫ lift (1 : B ⟶ A) (𝟙 B)
  let P : LB (A ⊗ B).left := tens P₀ (dual (P₀.pull c.left))
  have hP : P.IsLB := isLB_tens hP₀ (isLB_dual (pull_isLB hP₀ _))
  have hcls : cls P hP = cls P₀ hP₀ - GlobalTheory.CechPic.pull c.left (cls P₀ hP₀) := by
    rw [cls_tens hP₀ (isLB_dual (pull_isLB hP₀ _)), cls_dual (pull_isLB hP₀ _), cls_pull hP₀, sub_eq_add_neg]
  have hev : ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ B), evc hP a t = evc hP₀ a t - evc hP₀ 1 t := by
    intro Y a t
    have e : lift a t ≫ c = lift (1 : Y ⟶ A) t := by
      simp only [c, lift_snd_assoc, comp_lift, MonObj.comp_one, Category.comp_id, lift_snd]
    simp only [evc]
    rw [hcls, map_sub, ← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, e]
  have hform' : ∀ (Y : Over (Sp R)) (a x : Y ⟶ A), evc hP a (x ≫ q) = GlobalTheory.CechPic.pull (a * x).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) - GlobalTheory.CechPic.pull x.left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL) := by
    intro Y a x
    rw [hev, hform, hform, _root_.one_mul]
    abel
  have h0l : Triv (ev P (1 : B ⟶ A) (𝟙 B)) := by
    rw [triv_ev_iff hP, hev, sub_self]
  have h0r : Triv (ev P (𝟙 A) (1 : A ⟶ B)) := by
    have e : (1 : A ⟶ B) = (1 : A ⟶ A) ≫ q := (MonObj.one_comp q).symm
    rw [triv_ev_iff hP, e, hform', _root_.mul_one]
    abel
  have hadd : IsAdditive P := GlobalTheory.CubeNoeth.isAdditive_of_triv_axes hA hB hP h0l h0r
  have hBsm := hB.smooth
  have hAfa := _root_.GlobalTheory.DualCon.FinAffNoeth.finAff_of_relAmple_noetherian R A hA L hL hamp
  refine ⟨B, P, q, ⟨hP, hadd⟩, ⟨hB.proper, _root_.GlobalTheory.FiniteSurjRelDim.smoothOfRelativeDimension_of_finite_surjective _ A B g q hg hBsm hqf hqfl hqs, hB.geomConnected⟩, ?_, hqf, hqfl, hqs, hform', ?_⟩
  · intro F
    classical
    obtain ⟨U, hU, hF⟩ := hAfa (F.image π.left)
    exact ⟨π.left ⁻¹ᵁ U, hU.preimage π.left, fun x hx ↦ hF _ (Finset.mem_image_of_mem _ hx)⟩
  · intro Y x y
    constructor
    · intro h
      refine (hrep Y (x * y⁻¹)).2 ⟨hpb.lift x y h ≫ fst H A, ?_⟩
      have h1 := hpb.lift_fst x y h
      rw [comp_mul, hpb.lift_snd] at h1
      rw [eq_mul_inv_iff_mul_eq, Category.assoc, h1]
    · intro h
      obtain ⟨z, hz⟩ := (hrep Y (x * y⁻¹)).1 h
      have hx : x = lift z y ≫ ((fst H A ≫ i) * snd H A) := by
        rw [comp_mul, lift_fst_assoc, lift_snd, hz, inv_mul_cancel_right]
      rw [hx, Category.assoc, hpb.w, lift_snd_assoc]

end GlobalTheory.DualQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalTatePairsUnitaryTypeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_tate_pairs_unitaryType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F), Function.Injective β → ∀ (T : Formalism.L2.Pj.CDVR) (b : O →+* T.V), Function.Injective b → ∀ (D : DegData T.V (maximalIdeal T.V)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), PelOK Dm D.toPre o → (∀ k : ℕ, k ∣ l.M' → ∀ q : QkPt D.toPre (AlgebraicClosure (FractionRing T.V)) k, ∃ p : QkPt D.toPre (FractionRing T.V) k, QkExt (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) p q) → ∃ (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A) (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M), ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing T.V) F] (z : O), ((β z : c.F) : ℂ) = zeta l.A → ∃ I : (letI := H.starRing; TateIsoQ Dm D.toPre o F), (I.ζ l.A : F) = algebraMap (FractionRing T.V) F (algebraMap T.V _ (b z)) ∧ (∀ a q, QkExt (algebraMap _ F) (pA a) q → QkPt.Equiv D.toPre F q (I.ev l.A a)) ∧ ∀ a q, QkExt (algebraMap _ F) (pM a) q → QkPt.Equiv D.toPre F q (I.ev l.M a) := by
  first | exact @GlobalTheory.TraitTate.exists_tate | exact GlobalTheory.TraitTate.exists_tate | (intros; apply GlobalTheory.TraitTate.exists_tate <;> assumption)
end

