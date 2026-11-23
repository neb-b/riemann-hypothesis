module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsDenomOfIsAffineOpen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InjectiveOfFlatLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1509
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0529
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProperSemiAbelianFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1944
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtMapDualBCLeft

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFibrewiseNonvanishingThetaSectionOfSmoothMode
section
open AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open CategoryTheory Limits IsLocalRing

namespace GlobalTheory.ThetaNormal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.Models
open scoped CategoryTheory.Obj

theorem exists_theta_of_flat {X : Scheme.{0}} {G : Over X} [GrpObj G] (hG : IsSemiAbelian G) {L : LB G.left}
    (hL : L.IsLB) (x : X) {R : Type} [CommRing R] [IsLocalRing R] (ψ : X.presheaf.stalk x →+* R) (hψ : ψ.Flat)
    [IsLocalHom ψ] {G' : Over (Sp R)} {φ : G'.left ⟶ G.left}
    (hφ : IsPullback φ G'.hom G.hom (spMap ψ ≫ X.fromSpecStalk x)) {L' : LB G'.left} (hL' : L'.IsLB)
    (hw : LBIso L' (L.pull φ)) (hθ : LN.ThetaNZ G' L') :
    ∃ V : X.Opens, x ∈ V ∧ ∃ θ ∈ secOn L (G.hom ⁻¹ᵁ V),
      ∀ y ∈ V, ∃ (g : G.left) (i : L.ι), G.hom g = y ∧ g ∈ G.left.basicOpen (θ i) := by
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
  let ι := pullback.fst G.hom hU.fromSpec
  let f := pullback.snd G.hom hU.fromSpec
  let gm : Γ(X, U) →+* R := ψ.comp (X.presheaf.germ U x hx).hom
  have hξ : spMap gm ≫ hU.fromSpec = spMap ψ ≫ X.fromSpecStalk x := by
    rw [← hU.fromSpecStalk_eq_fromSpecStalk hx]
    show Spec.map (CommRingCat.ofHom (X.presheaf.germ U x hx).hom ≫ CommRingCat.ofHom ψ) ≫ _ = _
    rw [Spec.map_comp, Category.assoc]
    rfl
  let π : G'.left ⟶ pullback G.hom hU.fromSpec := pullback.lift φ (G'.hom ≫ spMap gm)
    (by rw [Category.assoc, hξ, hφ.w])
  have hπ : π ≫ ι = φ := pullback.lift_fst _ _ _
  have hP : IsPullback π G'.hom f (spMap gm) :=
    IsPullback.of_right (by rw [hπ, hξ]; exact hφ) (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  have : CompactSpace (pullback G.hom hU.fromSpec : Scheme.{0}) := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace (pullback G.hom hU.fromSpec : Scheme.{0}) := quasiSeparatedSpace_of_quasiSeparated f
  have hflat : gm.Flat := by
    have h₀ : (X.presheaf.germ U x hx).hom.Flat := by
      letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
      have := hU.isLocalization_stalk ⟨x, hx⟩
      exact RingHom.flat_algebraMap_iff.2
        (IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
    exact RingHom.Flat.comp h₀ hψ
  have hM := pull_isLB hL ι
  obtain ⟨w, hw'⟩ : LBIso ((L.pull ι).pull π) (L'.pull (𝟙 _)) :=
    LBIso.chartPull (chartPullLinComb L ι (fun _ : PUnit => π) (fun _ => φ) (fun _ => 1) (𝟙 _)
      fun _ => hπ.trans (Category.id_comp _).symm) (Geo.Tor.chartPullPull L' _ _ rfl) hw.symm
  obtain ⟨θ', hθ'⟩ := hθ
  obtain ⟨σ, hσ⟩ := ThetaLocal.exists_sec_pull hL' (pull_isLB hM π) (𝟙 _) w hw' (O := ⊤) le_top _
    (SecSpread.res_mem_secOn θ' ⊤)
  obtain ⟨z, i, hz, hi⟩ := hθ' (IsLocalRing.closedPoint _)
  obtain ⟨k, hk⟩ := hσ z i ((ThetaLocal.mem_basicOpen_resG _ _ _).2 ⟨⟨trivial, G'.left.basicOpen_le _ hi⟩, hi⟩)
  obtain ⟨k, rfl⟩ : ∃ j, k = fun _ => j := ⟨k PUnit.unit, rfl⟩
  have hk₁ := G'.left.basicOpen_le _ hk
  have hk₂ : π z ∈ (L.pull ι).U k := mem_pull.1 hk₁
  obtain ⟨n, a, u, hu⟩ := FlatSec.exists_comb_of_flat _ _ gm hflat _ f _ π G'.hom hP _ hM σ
  obtain ⟨j, hj⟩ : ∃ j, π z ∈ Scheme.basicOpen _ ((u j).f k) := by
    by_contra hn
    have h₁ := (AbLocusPull.isUnit_gs_iff (𝟙 _) z _ hk₁ _).2 hk
    rw [hu z k hk₂] at h₁
    refine (IsLocalRing.mem_maximalIdeal _).1 (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ ?_) h₁
    exact fun h₂ => hn ⟨j, (AbLocusPull.isUnit_gs_iff π z _ hk₂ _).1 h₂⟩
  let V : X.Opens := ⟨(ι ≫ G.hom) '' Scheme.basicOpen _ ((u j).f k),
    (ι ≫ G.hom).isOpenMap _ (Scheme.basicOpen _ ((u j).f k)).isOpen⟩
  have hr : G.hom ⁻¹ᵁ V ≤ ι.opensRange := by
    rintro g ⟨y, -, e⟩
    obtain ⟨q, hq, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback G.hom hU.fromSpec) g (f y)
      (e.symm.trans (congrArg (fun r : pullback G.hom hU.fromSpec ⟶ X => r y) pullback.condition))
    exact ⟨q, hq⟩
  obtain ⟨θ, hθ, hb⟩ := ThetaLocal.exists_secOn_push hL hM (lbIso_refl hM) hr le_top
    (SecSpread.res_mem_secOn (u j) ⊤)
  refine ⟨V, ⟨π z, hj, ?_⟩, θ, hθ, ?_⟩
  · rw [← Scheme.Hom.comp_apply, ← Category.assoc, hπ, hφ.w, Scheme.Hom.comp_apply, hz]
    show X.fromSpecStalk x (spMap ψ (IsLocalRing.closedPoint R)) = x
    have hc : spMap ψ (IsLocalRing.closedPoint R) = IsLocalRing.closedPoint _ := IsLocalRing.comap_closedPoint ψ
    rw [hc]
    exact Scheme.fromSpecStalk_closedPoint
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨i', hi'⟩ := exists_chart hL (ι y)
    exact ⟨ι y, i', rfl, hb y ⟨y, hy, rfl⟩ i' k hi'
      ((ThetaLocal.mem_basicOpen_resG _ _ _).2 ⟨⟨trivial, Scheme.basicOpen_le _ _ hy⟩, hy⟩)⟩

theorem hasTheta_of_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension Dw.dim Y.s → GlobalTheory.Models.HasTheta Y.t.G Y.t.PP.L := by
  intro E _ _ _ H Dw _ l Xo c Y hsm x
  have : Smooth Y.s := SmoothOfRelativeDimension.smooth Dw.dim _
  haveI hAr : IsRegularRing (Y.X.presheaf.stalk x) :=
    ExtendRig.isRegularRing_stalk isRegularRing_of_smooth c.F Y.s x
  haveI : IsRegularLocalRing (Y.X.presheaf.stalk x) :=
    IsRegularLocalRing.of_isRegularRing_of_isLocalRing _
  haveI : IsRegularLocalRing (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) :=
    RegularCompletion.isRegularLocalRing_adicCompletion _
  obtain ⟨hdC, hnC⟩ := isDomain_and_isIntegrallyClosed_of_isRegularLocalRing
    (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x))

  haveI hκ : CharZero (Y.X.residueField x) := by
    let φ : c.F →+* Y.X.residueField x := (Y.X.evaluation ⊤ x trivial).hom.comp (GlobalTheory.QCoh.structureRingHom Y.s)
    exact charZero_of_injective_ringHom φ.injective
  obtain ⟨k, _, _, hk, S', hS'⟩ := CoveringCompare.exists_finite_splitOver Y.t.G Y.t.semi x

  haveI : Algebra.IsSeparable (Y.X.residueField x) k := inferInstance
  obtain ⟨R, _, _, _, _, j, _, _, hj⟩ := LocM.Bdy.exists_etale_local
    (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) (Y.X.residueField x) k
    (ResidueField.map (algebraMap (Y.X.presheaf.stalk x)
      (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x))))
  have : IsLocalization.AtPrime R (maximalIdeal R) :=
    IsLocalization.self fun a ha => by_contra fun h => ha h
  obtain ⟨hd, hn⟩ := isDomain_and_isIntegrallyClosed_atPrime_of_etale
    (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) (maximalIdeal R) R
  have hNR : IsNoetherianRing R :=
    IsNoetherianRing.of_finite (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) R
  have hc := CompleteFiniteExtension.isAdicComplete_of_finite_local
    (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) R
  have f₁ := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.X.presheaf.stalk x)
    (B := AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x))
  have f₂ := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) (B := R)
  let ψ : Y.X.presheaf.stalk x →+* R := (algebraMap (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x))
    (Y.X.presheaf.stalk x)) R).comp (algebraMap (Y.X.presheaf.stalk x) (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)))
  have hinj : Function.Injective ψ :=
    (FaithfulSMul.algebraMap_injective _ _).comp (FaithfulSMul.algebraMap_injective _ _)
  haveI : CharZero (ResidueField (Y.X.presheaf.stalk x)) := hκ
  haveI : CharZero (Y.X.presheaf.stalk x) := RingHom.charZero (residue (Y.X.presheaf.stalk x))
  haveI : CharZero R := charZero_of_injective_ringHom hinj
  have hadm := isAdmissibleCompleteLocalDomainPrime_maximalIdeal R hNR hn hc
  have hψf : ψ.Flat := RingHom.Flat.comp (RingHom.flat_algebraMap_iff.2 inferInstance)
    (RingHom.flat_algebraMap_iff.2 inferInstance)
  haveI : IsLocalHom ψ := inferInstance

  obtain ⟨t, ⟨m⟩⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_sab (spMap ψ ≫ Y.X.fromSpecStalk x) Y.t
  haveI : IsProper Y.s := ProperFamily.isProper_of_isProjOver Y.proj
  haveI : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  haveI : CompactSpace Y.X := QuasiCompact.compactSpace_of_compactSpace Y.s
  haveI : IsNoetherian Y.X := {}
  have hjo := GenFan.Tri.isOpenImmersion_j_id Y
  have hopen : IsOpen (Set.range Y.j) := Y.j.isOpenEmbedding.isOpen_range
  have hdense : Dense (Set.range Y.j) := by
    have : IsIso (pullback.fst Y.s (spMap (RingHom.id c.F))) := by
      have : IsIso (spMap (RingHom.id c.F)) := by
        show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
        rw [show CommRingCat.ofHom (RingHom.id c.F) = 𝟙 (CommRingCat.of c.F) from rfl, Spec.map_id]
        infer_instance
      infer_instance
    have e : Set.range Y.j = (pullback.fst Y.s (spMap (RingHom.id c.F))) '' Set.range Y.jQ := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        exact ⟨Y.jQ w, ⟨w, rfl⟩, (Scheme.Hom.comp_apply _ _ _).symm⟩
      · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
        exact ⟨w, Scheme.Hom.comp_apply _ _ _⟩
    rw [e]
    exact ((pullback.fst Y.s (spMap (RingHom.id c.F))).surjective.denseRange).dense_image
      (pullback.fst Y.s (spMap (RingHom.id c.F))).continuous Y.jQ_dense
  let ξ : Sp R := (⊥ : PrimeSpectrum R)
  have hgen : (spMap ψ ≫ Y.X.fromSpecStalk x) ξ ∈ Set.range Y.j :=
    LocM.SharedLaws.mem_of_maximal (fun y hy => LocM.Bdy.generic_image x ψ hinj ξ rfl y hy) hopen hdense
  have hr : Set.range (jK R ≫ spMap ψ ≫ Y.X.fromSpecStalk x) ⊆ Set.range Y.j := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact LN.GenericPoint.jK_mem (U := (spMap ψ ≫ Y.X.fromSpecStalk x) ⁻¹' Set.range Y.j)
      (hopen.preimage (Scheme.Hom.continuous _)) ⟨ξ, hgen⟩ q
  have hpol : LN.PolAt t (jK R) :=
    GoodTrait.polAt_of_point Y m (jK R) (IsOpenImmersion.lift Y.j _ hr) (IsOpenImmersion.lift_fac _ _ _)
  have h₁ := LocM.Bdy.residue_comp (R := R) x
  have e : spMap (algebraMap (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) R) ≫
      fromSpecCompletedStalk Y.X x = spMap ψ ≫ Y.X.fromSpecStalk x := by
    rw [spMap_comp, Category.assoc]; rfl
  have h₂ : spMap j ≫ spMap (algebraMap (Y.X.residueField x) k) =
      spMap ((ResidueField.map (algebraMap (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x))
        (Y.X.presheaf.stalk x)) R)).comp (ResidueField.map (algebraMap (Y.X.presheaf.stalk x)
          (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x))))) :=
    (spMap_comp _ _).symm.trans (congrArg spMap hj)
  obtain ⟨S₁, hS₁⟩ := LocM.Bdy.split_pull _ hS' j (ι := spMap ψ ≫ Y.X.fromSpecStalk x) (by
    rw [← Category.assoc]
    refine (congrArg (· ≫ Y.X.fromSpecResidueField x) h₂).trans ?_
    exact h₁.trans (congrArg (spMap (residue R) ≫ ·) e)) m
  have hsplit : LN.SplitOver t.G (maximalIdeal R) := ⟨S₁, hS₁⟩
  have hθ := thetaNZ_of_polAt E H R hadm t hpol hsplit
  exact exists_theta_of_flat Y.t.semi Y.t.PP.isLB x ψ hψf m.cart.1 t.PP.isLB (m.lin.imp fun _ h => h.1) hθ

end GlobalTheory.ThetaNormal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasMarkingTransportOfCmTypeEmbedding
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.GoodTransport

theorem exists_equiv_of_lattices {La : Type} [AddCommGroup La] {g : ℕ} (P P' : La →+ (Fin g → ℂ))
    (hi : Function.Injective P) (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤)
    (hi' : Function.Injective P') (hd' : DiscreteTopology P'.range) (hs' : Submodule.span ℝ (Set.range P') = ⊤) :
    ∃ φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ), ∀ a, φ (P a) = P' a := by
  let L : Submodule ℤ (Fin g → ℂ) := LinearMap.range P.toIntLinearMap
  let L' : Submodule ℤ (Fin g → ℂ) := LinearMap.range P'.toIntLinearMap
  haveI : DiscreteTopology L := hd
  haveI : DiscreteTopology L' := hd'
  haveI : IsZLattice ℝ L := ⟨hs⟩
  haveI : IsZLattice ℝ L' := ⟨hs'⟩
  let e : La ≃ₗ[ℤ] L := LinearEquiv.ofInjective P.toIntLinearMap hi
  let e' : La ≃ₗ[ℤ] L' := LinearEquiv.ofInjective P'.toIntLinearMap hi'
  let b := Module.Free.chooseBasis ℤ L
  let b₀ := b.map e.symm
  let b' := b₀.map e'
  let φ := (b.ofZLatticeBasis ℝ L).equiv (b'.ofZLatticeBasis ℝ L') (Equiv.refl _)
  have key : (φ.toLinearMap.restrictScalars ℤ).comp P.toIntLinearMap = P'.toIntLinearMap := by
    refine b₀.ext fun k => ?_
    have h1 : P (b₀ k) = b.ofZLatticeBasis ℝ L k := by
      rw [Module.Basis.ofZLatticeBasis_apply]
      exact congrArg Subtype.val (e.apply_symm_apply (b k))
    have h2 : P' (b₀ k) = b'.ofZLatticeBasis ℝ L' k := by
      rw [Module.Basis.ofZLatticeBasis_apply]
      rfl
    change φ (P (b₀ k)) = P' (b₀ k)
    rw [h1, h2, Module.Basis.equiv_apply]
    rfl
  exact ⟨φ, fun a => LinearMap.congr_fun key a⟩

theorem ex_eq_iff {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (z w : Fin g → ℂ) :
    u.ex z = u.ex w ↔ z - w ∈ u.Λ := by
  have := u.ex_add (z - w) w
  rw [sub_add_cancel] at this
  rw [← u.ker, this]
  exact mul_eq_right

def imHerm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (herm Hm z w).im)
    (fun _ _ _ => by simp [herm])
    (fun r z w => by
      rw [herm, herm, smul_dotProduct, Complex.smul_im])
    (fun _ _ _ => by simp [herm, Matrix.mulVec_add])
    (fun r z w => by
      rw [herm, herm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im, star_trivial])

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}

theorem fibre_marks {Xo : Moduli D l} {σ : KA l →+* ℂ} {g₀ : ℕ} {ty : Fin g₀ → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty)
    (i : Fin Fu.n) {P : (Fu.Di i).La →+ (Fin g₀ → ℂ)} (hP : IsPeriod (Fu.Di i) ty P) {y₀ : Sp ℂ ⟶ Xo.X}
    (hy : y₀ = Fu.u i P) {s' : Sp ℂ ⟶ Sp (KA l)} {o : Obj D l (baseKA l) s'} (m : ObjMap o Xo.univ y₀) {g : ℕ}
    (u : HolUnif o.t.G o.t.PP.L g) (h : (Fin g₀ → ℂ) → (Fin g → ℂ))
    (hh : ∀ z, (u.ex (h z)).left ≫ m.toSABMap.φ = (Fu.ex i P z).left) :
    (∀ (a : 𝓞 E) z, u.ex (h z) ≫ o.t.act.act a = u.ex (h fun k => ty k (a : E) * z k)) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
        o.eta a = u.ex (h ((l.M : ℂ)⁻¹ • P (Fu.t i a)))) ∧
      ∀ a, o.etaA a = u.ex (h ((l.A : ℂ)⁻¹ • P (Fu.t i a))) := by
  subst hy
  have inj : ∀ x y : 𝟙_ (Over (Sp ℂ)) ⟶ o.t.G, x.left ≫ m.toSABMap.φ = y.left ≫ m.toSABMap.φ → x = y :=
    fun x y h => Over.OverMorphism.ext (m.cart.1.hom_ext h (by rw [Over.w x, Over.w y]))
  refine ⟨fun a z => inj _ _ ?_, fun a ha => inj _ _ ?_, fun a => inj _ _ ?_⟩
  · rw [hh, Fu.ex_lin i P hP, Over.comp_left, Over.comp_left, ← hh, Category.assoc, Category.assoc]
    exact congrArg _ (m.act a)
  · rw [hh, ← Fu.ex_eta i P hP a ha]
    exact m.eta a
  · rw [hh, ← Fu.ex_etaA i P hP a]
    exact m.etaA a

theorem exists_eta_eq (a : D.La) : ∃ a₁ ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
    ∀ {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s),
      o.eta a = o.eta a₁ := by
  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [l.coprime]; trivial
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
  refine ⟨y • a, Submodule.smul_mem_smul hy trivial, fun o => ?_⟩
  have : a = x • a + y • a := by rw [← add_smul, hxy, one_smul]
  conv_lhs => rw [this]
  rw [o.eta_add, o.eta_ker _ (Submodule.smul_mem_smul hx trivial), _root_.one_mul]

theorem exists_transport {Xo : Moduli D l} {σ : KA l →+* ℂ} {g₀ : ℕ} {ty : Fin g₀ → (E →+* ℂ)}
    (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) {P P' : (Fu.Di i).La →+ (Fin g₀ → ℂ)} (hP : IsPeriod (Fu.Di i) ty P)
    (hP' : IsPeriod (Fu.Di i) ty P') {y₀ y₀' : Sp ℂ ⟶ Xo.X} (hy : y₀ = Fu.u i P) (hy' : y₀' = Fu.u i P')
    {s s' : Sp ℂ ⟶ Sp (KA l)} {o : Obj D l (baseKA l) s} {o' : Obj D l (baseKA l) s'} (m : ObjMap o Xo.univ y₀)
    (m' : ObjMap o' Xo.univ y₀') {g g' : ℕ} (u : HolUnif o.t.G o.t.PP.L g) (u' : HolUnif o'.t.G o'.t.PP.L g')
    {Hm : Matrix (Fin g) (Fin g) ℂ} {Hm' : Matrix (Fin g') (Fin g') ℂ} {κ : u.Λ → ℂ} {κ' : u'.Λ → ℂ}
    (hAH : u.IsAH Hm κ) (hAH' : u'.IsAH Hm' κ') : ∃ φ, IsTransport o o' u u' Hm Hm' φ := by
  obtain ⟨h, hex, hΛ, hE, -⟩ := FibreCmp.exists_equiv_of_isAH E H D l Xo σ g₀ ty Fu i P y₀ s o m g u Hm κ hP hy hAH
  obtain ⟨h', hex', hΛ', hE', -⟩ :=
    FibreCmp.exists_equiv_of_isAH E H D l Xo σ g₀ ty Fu i P' y₀' s' o' m' g' u' Hm' κ' hP' hy' hAH'
  obtain ⟨a1, a2, a3⟩ := fibre_marks Fu i hP hy m u h hex
  obtain ⟨b1, b2, b3⟩ := fibre_marks Fu i hP' hy' m' u' h' hex'
  obtain ⟨φ₀, hφ₀⟩ := exists_equiv_of_lattices P P' hP.2.1 hP.2.2.1 hP.2.2.2.1 hP'.2.1 hP'.2.2.1 hP'.2.2.2.1
  let φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g' → ℂ) :=
    ((h.symm.restrictScalars ℝ).trans φ₀).trans (h'.restrictScalars ℝ)
  have hφ : ∀ z, φ (h z) = h' (φ₀ z) := fun z => congrArg (fun t => h' (φ₀ t)) (h.symm_apply_apply z)
  have lat : ∀ z, φ z ∈ u'.Λ ↔ z ∈ u.Λ := fun z => by
    obtain ⟨z, rfl⟩ := h.surjective z
    rw [hφ, hΛ, hΛ']
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, φ₀.injective ((hφ₀ a).trans ha)⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, (hφ₀ a).symm⟩
  have exq : ∀ z w, u.ex z = u.ex w → u'.ex (φ z) = u'.ex (φ w) := fun z w hzw => by
    rw [ex_eq_iff] at hzw ⊢
    rw [← map_sub, lat]
    exact hzw
  have lin : ∀ (a : 𝓞 E) z, φ₀ (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * φ₀ z k := fun a z => by
    let T : (Fin g₀ → ℂ) →ₗ[ℝ] (Fin g₀ → ℂ) :=
      LinearMap.pi fun k => (LinearMap.mulLeft ℝ (ty k (a : E))).comp (LinearMap.proj k)
    have : φ₀.toLinearMap.comp T = T.comp φ₀.toLinearMap := by
      refine LinearMap.ext_on_range hP.2.2.2.1 fun x => ?_
      have e1 : T (P x) = P (a • x) := funext fun k => (hP.1 a x k).symm
      have e2 : T (P' x) = P' (a • x) := funext fun k => (hP'.1 a x k).symm
      change φ₀ (T (P x)) = T (φ₀ (P x))
      rw [e1, hφ₀, hφ₀, e2]
    exact LinearMap.congr_fun this z
  have dv : ∀ (n : ℕ) x, φ₀ ((n : ℂ)⁻¹ • P x) = (n : ℂ)⁻¹ • P' x := fun n x => by
    have e : ∀ v : Fin g₀ → ℂ, (n : ℂ)⁻¹ • v = (n : ℝ)⁻¹ • v := fun v => by
      rw [← Complex.coe_smul]; simp
    rw [e, e, map_smul, hφ₀]
  refine ⟨φ, lat, fun a z w hw => ?_, fun z w => ?_, fun a z hz => ?_, fun a z hz => ?_⟩
  · obtain ⟨z, rfl⟩ := h.surjective z
    rw [a1] at hw
    rw [exq _ _ hw, hφ, hφ, b1, lin]
  · obtain ⟨z, rfl⟩ := h.surjective z
    obtain ⟨w, rfl⟩ := h.surjective w
    let j := (h.restrictScalars ℝ).toLinearMap
    have : (imHerm Hm').compl₁₂ (φ.toLinearMap.comp j) (φ.toLinearMap.comp j) = (imHerm Hm).compl₁₂ j j := by
      refine LinearMap.ext_on_range hP.2.2.2.1 fun x => LinearMap.ext_on_range hP.2.2.2.1 fun y => ?_
      change (herm Hm' (φ (h (P x))) (φ (h (P y)))).im = (herm Hm (h (P x)) (h (P y))).im
      rw [hφ, hφ, hφ₀, hφ₀, hE, hE']
    exact LinearMap.congr_fun (LinearMap.congr_fun this z) w
  · obtain ⟨a₁, ha₁, e⟩ := exists_eta_eq (l := l) a
    rw [e o, a2 a₁ ha₁] at hz
    rw [exq _ _ hz, e o', b2 a₁ ha₁, hφ, dv]
  · rw [a3] at hz
    rw [exq _ _ hz, b3, hφ, dv]

theorem hasTransport_of_goodEmb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens) (e : c.F →+* ℂ) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y), IsClosed (U : Set (Xo.XF c)) → IsOpenImmersion io → Set.range io = compactOf Y U → io ≫ genStr Y = B.str → 1 ≤ D.p + D.q → Formalism.L2.PjFree.GoodEmb c e → HasTransport Xo c U e := by
  intro E _ _ _ H D l Xo c O _ β Y U e B io hU hio hr hs hpq he y y' hy hy' hyU hyU' o o' ⟨m⟩ ⟨m'⟩ g g' u u' Hm Hm'
    κ κ' hAH hAH'
  let e₀ : Fin (Fintype.card (Pad.Letter D)) ≃ Pad.Letter D := (Fintype.equivFin _).symm
  have hty := (GlobalTheory.Relab.relab_good E H l c e he).2.2.2 D _ e₀
  obtain ⟨Fu⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H D l Xo (e.comp (IntermediateField.inclusion c.le).toRingHom) _
    (fun j => Formalism.L2.PjFree.relab c e (e₀ j).1) hpq he hty
  have ov : ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ toF Xo c = spMap e →
      (x ≫ toX Xo c) ≫ Xo.s = spMap (e.comp (IntermediateField.inclusion c.le).toRingHom) := fun x hx => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx, DetExtendZero.spMap_comp]
  obtain ⟨i, P, hP, hu⟩ := Fu.onto _ (ov y hy)
  obtain ⟨i', P', hP', hu'⟩ := Fu.onto _ (ov y' hy')
  obtain rfl : i = i' := _root_.GlobalTheory.DetLine.SameIndex.index_eq E H D l Xo c O β Y U e _ _ Fu i i' P P' y y' B io hU hio hr hs hy hy' hyU hyU'
    hP hP' hu.symm hu'.symm
  exact exists_transport Fu i hP hP' hu.symm hu'.symm m m' u u' hAH hAH'

end GlobalTheory.DetLine.GoodTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateDifferenceSection
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))

theorem aH_left_π_ptMap {G' : Over (Sp O)} {π : G'.left ⟶ t.G.left}
    (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)) {D : Type} [CommRing D] [Algebra O D]
    (a : Bt P' x0 hu →ₐ[O] D) :
    (ptMap a ≫ aH P' x0 hu hπ).left ≫ π = spMap (a.toRingHom.comp (inB P' x0 hu)) ≫ P'.u.left := by
  rw [Over.comp_left, Category.assoc, aH_left_π]
  change spMap a.toRingHom ≫ spMap (inB P' x0 hu) ≫ P'.u.left = _
  rw [GlobalTheory.HTMap.spc_assoc]

theorem str_of_alg {D : Type} [CommRing D] [Algebra O D] (a : Bt P' x0 hu →ₐ[O] D) :
    (a.toRingHom.comp (inB P' x0 hu)).comp P'.str = (algebraMap O D).comp x0 := by
  rw [RingHom.comp_assoc, inB_str, ← RingHom.comp_assoc]
  congr 1
  exact a.comp_algebraMap

theorem at_alg {D : Type} [CommRing D] [Algebra O D] (a : Bt P' x0 hu →ₐ[O] D) :
    P'.At ((algebraMap O D).comp x0) (spMap (a.toRingHom.comp (inB P' x0 hu)) ≫ P'.u.left)
      (a.toRingHom.comp (inB P' x0 hu)) :=
  ⟨str_of_alg P' x0 hu a, rfl⟩

theorem exists_mul_affine {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ t.G.left}
    (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) {D : Type} [CommRing D] [Algebra O D]
    (a b : Bt P' x0 hu →ₐ[O] D) :
    ∃ z : specO O D ⟶ Hs P' x0 hu, z ≫ aH P' x0 hu hg.1 =
      (ptMap a ≫ aH P' x0 hu hg.1) * (ptMap b ≫ aH P' x0 hu hg.1) := by
  have ha := at_alg P' x0 hu a
  have hb := at_alg P' x0 hu b
  let w₁ : Over.mk ((specO O D).hom ≫ spMap x0 ≫ ξ) ⟶ t.G :=
    GlobalTheory.HTMap.mkPt _ (ha.over.trans (GlobalTheory.HTMap.spc_assoc _ _ _).symm)
  let w₂ : Over.mk ((specO O D).hom ≫ spMap x0 ≫ ξ) ⟶ t.G :=
    GlobalTheory.HTMap.mkPt _ (hb.over.trans (GlobalTheory.HTMap.spc_assoc _ _ _).symm)
  obtain ⟨β'', h''⟩ := GlobalTheory.HTMap.FP.At.mul (w := w₁) (w' := w₂) ha hb
  refine ⟨ptOf P' x0 hu β'' h''.1, ?_⟩
  refine Over.OverMorphism.ext (hg.1.hom_ext ?_ ?_)
  · rw [ptOf_aH_π, h''.2]
    exact hg.2 (specO O D) _ _ w₁ w₂ (aH_left_π_ptMap P' x0 hu hg.1 a).symm
      (aH_left_π_ptMap P' x0 hu hg.1 b).symm
  · rw [Over.w, Over.w]

end GlobalTheory.FinPartAt

namespace GlobalTheory.FinPartAt

theorem exists_mul_factor {O : Type} [CommRing O] {C : Type} [CommRing C] [Algebra O C] (S : Over (Sp O))
    (x y : S ⟶ specO O C) :
    ∃ c : S ⟶ specO O (C ⊗[O] C),
      c ≫ ptMap (Algebra.TensorProduct.includeLeft : C →ₐ[O] C ⊗[O] C) = x ∧
      c ≫ ptMap (Algebra.TensorProduct.includeRight : C →ₐ[O] C ⊗[O] C) = y := by
  have hxy : x.left ≫ (specO O C).hom = y.left ≫ (specO O C).hom := by rw [Over.w, Over.w]
  let l := pullback.lift x.left y.left hxy ≫ (pullbackSpecIso O C C).hom
  have hl : l ≫ (specO O (C ⊗[O] C)).hom = S.hom := by
    change (pullback.lift x.left y.left hxy ≫ (pullbackSpecIso O C C).hom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap O (C ⊗[O] C))) = _
    rw [Category.assoc, pullbackSpecIso_hom_base, ← Category.assoc]
    erw [pullback.lift_fst]
    exact Over.w x
  refine ⟨Over.homMk l hl, ?_, ?_⟩
  · refine Over.OverMorphism.ext ?_
    change (pullback.lift x.left y.left hxy ≫ (pullbackSpecIso O C C).hom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom)) = _
    rw [Category.assoc, pullbackSpecIso_hom_fst]
    erw [pullback.lift_fst]
  · refine Over.OverMorphism.ext ?_
    change (pullback.lift x.left y.left hxy ≫ (pullbackSpecIso O C C).hom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom)) = _
    rw [Category.assoc]
    erw [pullbackSpecIso_hom_snd]
    erw [pullback.lift_snd]

theorem exists_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) (G' : Over (Sp O)) [GrpObj G'] (π : G'.left ⟶ t.G.left) (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) (S : Over (Sp O)) (x y : S ⟶ Hs P' x0 hu), ∃ z : S ⟶ Hs P' x0 hu, z ≫ aH P' x0 hu hg.1 = (x ≫ aH P' x0 hu hg.1) * (y ≫ aH P' x0 hu hg.1) := by
  intro E _ _ _ H X t R _ ξ q P' O _ x0 hu G' _ π hg S x y
  obtain ⟨c, hc₁, hc₂⟩ := exists_mul_factor S x y
  obtain ⟨z₀, hz₀⟩ := exists_mul_affine P' x0 hu hg
    (Algebra.TensorProduct.includeLeft : Bt P' x0 hu →ₐ[O] Bt P' x0 hu ⊗[O] Bt P' x0 hu)
    Algebra.TensorProduct.includeRight
  refine ⟨c ≫ z₀, ?_⟩
  rw [Category.assoc, hz₀, MonObj.comp_mul, ← Category.assoc, hc₁, ← Category.assoc, hc₂]

end GlobalTheory.FinPartAt
end
end

