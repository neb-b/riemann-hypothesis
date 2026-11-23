module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
public import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0529
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualTangentVectorsGenericFibreDetEqDetOmegaTrans
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyVals.LieRel

open GlobalTheory.VB GlobalTheory.LieVB
open GlobalTheory.Twist (resM resM_self)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO ptMap LieG dualScale)

section Lie

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [QuasiSeparated G.hom]

theorem exists_prod (l : List (LieG G)) :
    ∃ z : LieG G, z.1 = (l.map fun x => x.1).prod ∧ tangent z = (l.map tangent).sum := by
  induction l with
  | nil =>
    have h1 : ptMap (TrivSqZeroExt.fstHom R R R) ≫ (1 : specO R (DualNumber R) ⟶ G) = 1 := MonObj.comp_one _
    refine ⟨⟨1, h1⟩, rfl, ?_⟩
    have h2 := tangent_mul (G := G) ⟨1, h1⟩ ⟨1, h1⟩ (OmegaGlobal.fst_mul _ _)
    have h3 : (⟨_, OmegaGlobal.fst_mul (G := G) ⟨1, h1⟩ ⟨1, h1⟩⟩ : LieG G) = ⟨1, h1⟩ :=
      Subtype.ext (_root_.mul_one _)
    rw [h3] at h2
    simpa using h2
  | cons x l ih =>
    obtain ⟨z, hz, hz'⟩ := ih
    refine ⟨⟨_, OmegaGlobal.fst_mul x z⟩, ?_, ?_⟩
    · rw [List.map_cons, List.prod_cons, ← hz]
    · rw [tangent_mul, hz', List.map_cons, List.sum_cons]

theorem isLieComb_of_tangent {n : ℕ} (a : Fin n → R) (v : Fin n → LieG G) (w : LieG G)
    (h : tangent w = ∑ m, cst R (a m) • tangent (v m)) : IsLieComb a (fun m => (v m).1) w.1 := by
  let u : Fin n → LieG G := fun m => ⟨_, OmegaGlobal.fst_scale (a m) (v m)⟩
  obtain ⟨z, hz, hz'⟩ := exists_prod (List.ofFn u)
  have e : w = z := tangent_injective R G (by
    rw [h, hz', List.map_ofFn, List.sum_ofFn]
    exact Finset.sum_congr rfl fun m _ => (tangent_scale _ _ _).symm)
  refine ⟨fun m => (u m).1, fun m => ?_, ?_⟩
  · have ha : (dualScale (a m)).toRingHom = epsScaleR (a m) := by
      ext y <;> simp [dualScale, epsScaleR]
    exact congrArg (fun r => spMap r ≫ (v m).1.left) ha
  · rw [e, hz, List.map_ofFn]
    rfl

theorem exists_matrix {g : ℕ} {e e' : Fin g → Γ(omega G, ⊤)} (he : IsFrame e) (he' : IsFrame e') (v v' : Fin g → LieG G)
    (hv : ∀ j k, dualApp (tangent (v j)) le_top (e k) = if j = k then 1 else 0)
    (hv' : ∀ j k, dualApp (tangent (v' j)) le_top (e' k) = if j = k then 1 else 0) :
    ∃ M : Matrix (Fin g) (Fin g) R, (∀ j, IsLieComb (M j) (fun m => (v' m).1) (v j).1) ∧
      M.det = (Scheme.ΓSpecIso (.of R)).hom (he.detUnit he' le_rfl le_rfl : Γ(Sp R, ⊤)) := by
  refine ⟨fun j m => (Scheme.ΓSpecIso (.of R)).hom (dualApp (tangent (v j)) le_top (e' m)), fun j => ?_, ?_⟩
  · refine isLieComb_of_tangent _ _ _ (he'.dual_ext le_rfl fun k => ?_)
    rw [resM_self, dualApp_sum, LinearMap.sum_apply]
    simp only [dualApp_smul, LinearMap.smul_apply, smul_eq_mul, LB.resG_self]
    rw [Finset.sum_congr rfl fun m _ => congrArg (cst R _ * ·) (hv' m k)]
    simp
  · have hc (j : Fin g) : dualApp (tangent (v j)) le_rfl = (he.basis le_rfl).coord j := by
      apply (he.basis le_rfl).ext
      intro k
      have hb : (he.basis le_rfl) k = e k := by rw [he.basis_apply, resM_self]
      rw [hb, hv, ← hb, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      simp only [eq_comm]
    rw [IsFrame.val_detUnit, Module.Basis.det_apply]
    refine Eq.trans ?_ (RingHom.map_det (Scheme.ΓSpecIso (.of R)).hom.hom _).symm
    congr 1
    ext j m
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Module.Basis.toMatrix_apply, resM_self]
    exact congrArg _ (congrFun (congrArg DFunLike.coe (hc j)) (e' m))

end Lie

variable {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] [QuasiSeparated G.hom] {g : ℕ}

theorem pfr_eq (c : Chart (omega G) g) (ξ : Sp R ⟶ S) (hc : ⊤ ≤ ξ ⁻¹ᵁ c.U) :
    pfr c ξ hc = fun k => (omegaBase (isGrpPullback_pullback G ξ)).app ⊤
      (resM _ hc (QCoh.pullbackSections ξ (omega G) (le_refl (ξ ⁻¹ᵁ c.U)) (c.e k))) :=
  funext fun _ => congrArg _ (QCoh.res_pullbackSections ξ _ _ _ _).symm

theorem isFrame_pfr (c : Chart (omega G) g) (ξ : Sp R ⟶ S) (hc : ⊤ ≤ ξ ⁻¹ᵁ c.U) : IsFrame (pfr c ξ hc) := by
  rw [pfr_eq]
  exact ((c.isFrame.pullback ξ).res hc).map_iso _

theorem val_detUnit_pfr (c c' : Chart (omega G) g) (ξ : Sp R ⟶ S) (hc : ⊤ ≤ ξ ⁻¹ᵁ c.U) (hc' : ⊤ ≤ ξ ⁻¹ᵁ c'.U)
    (h : ⊤ ≤ ξ ⁻¹ᵁ (c.U ⊓ c'.U)) :
    ((isFrame_pfr c ξ hc).detUnit (isFrame_pfr c' ξ hc') le_rfl le_rfl : Γ(Sp R, ⊤)) =
      (ξ.appLE (c.U ⊓ c'.U) ⊤ h).hom (c.isFrame.detUnit c'.isFrame inf_le_left inf_le_right : Γ(S, c.U ⊓ c'.U)) := by
  have key {e e' f f' : Fin g → Γ(omega (bG G ξ), ⊤)} (he : IsFrame e) (he' : IsFrame e') (hf : IsFrame f)
      (hf' : IsFrame f') (h₁ : e = f) (h₂ : e' = f') :
      he.detUnit he' le_rfl le_rfl = hf.detUnit hf' le_rfl le_rfl := by
    subst h₁ h₂; rfl
  rw [key _ _ (((c.isFrame.pullback ξ).res hc).map_iso (omegaBase (isGrpPullback_pullback G ξ)))
    (((c'.isFrame.pullback ξ).res hc').map_iso (omegaBase (isGrpPullback_pullback G ξ))) (pfr_eq c ξ hc) (pfr_eq c' ξ hc'),
    IsFrame.detUnit_map_iso ((c.isFrame.pullback ξ).res hc) ((c'.isFrame.pullback ξ).res hc'),
    IsFrame.detUnit_res (c.isFrame.pullback ξ) (c'.isFrame.pullback ξ)]
  exact c.isFrame.val_detUnit_pullback c'.isFrame ξ inf_le_left inf_le_right h

theorem genPt_appLE [IsIntegral S] (U : S.Opens) (hU : genericPoint S ∈ U) (a : Γ(S, U)) :
    (Scheme.ΓSpecIso (.of (FF S))).hom (((genPt S).appLE U ⊤ (genPt_le U hU)).hom a) =
      S.presheaf.germ U (genericPoint S) hU a := by
  have k : ⊤ ≤ S.fromSpecStalk (genericPoint S) ⁻¹ᵁ U := genPt_le U hU
  have e : (S.fromSpecStalk (genericPoint S)).appLE U ⊤ k =
      S.presheaf.germ U _ hU ≫ (Scheme.ΓSpecIso (S.presheaf.stalk (genericPoint S))).inv := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hU]
    simp only [Category.assoc, ← Functor.map_comp]
    have e : ((homOfLE le_top).op ≫ (homOfLE k).op :
      Opposite.op (⊤ : (Spec (S.presheaf.stalk (genericPoint S))).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
    rw [e, CategoryTheory.Functor.map_id, Category.comp_id]
  have e' : (S.fromSpecStalk (genericPoint S)).appLE U ⊤ k ≫
      (Scheme.ΓSpecIso (S.presheaf.stalk (genericPoint S))).hom = S.presheaf.germ U _ hU := by
    rw [e, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congr($e' a)

theorem lieRel : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsSemiAbelian G →
    SmoothOfRelativeDimension g G.hom → ∀ (c c' : VB.Chart (LieVB.omega G) g)
    (h1 : genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')
    (y y' : Fin g → (epsR (KeyVals.FF S) ⟶ KeyVals.bG G (KeyVals.genPt S))),
    KeyVals.IsDual c (KeyVals.genPt S) y → KeyVals.IsDual c' (KeyVals.genPt S) y' →
    ∃ M : Matrix (Fin g) (Fin g) (KeyVals.FF S), (∀ j, IsLieComb (M j) y' (y j)) ∧
      M.det = S.presheaf.germ _ (genericPoint S) h1
        ((VB.det (LieVB.omega G) g).g c c' : Γ(S, (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')) := by
  intro S _ G _ _ g hG _ c c' h1 y y' ⟨hc, hy⟩ ⟨hc', hy'⟩
  choose v hv hv₁ using hy
  choose v' hv' hv₁' using hy'
  have : QuasiSeparated (bG G (genPt S)).hom :=
    MorphismProperty.of_isPullback (isGrpPullback_pullback G (genPt S)).1 inferInstance
  obtain ⟨M, hM, hd⟩ := exists_matrix (isFrame_pfr c _ hc) (isFrame_pfr c' _ hc') v v' hv₁ hv₁'
  obtain rfl : (fun j => (v j).1) = y := funext hv
  obtain rfl : (fun j => (v' j).1) = y' := funext hv'
  refine ⟨M, hM, hd.trans ?_⟩
  rw [val_detUnit_pfr c c' _ hc hc' (genPt_le _ h1)]
  exact genPt_appLE _ h1 _

end GlobalTheory.KeyVals.LieRel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallCompleteDvrDominating
section
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem dvd_of_map_dvd_of_valuationRing {V T : Type} [CommRing V] [IsDomain V] [ValuationRing V]
    [CommRing T] [IsDomain T] (ψ : V →+* T) (hψ : Function.Injective ψ) [IsLocalHom ψ] {a b : V}
    (ha : a ≠ 0) (h : ψ a ∣ ψ b) : a ∣ b := by
  rcases ValuationRing.dvd_total a b with hab | hba
  · exact hab
  · obtain ⟨c, hc⟩ := hba
    obtain ⟨d, hd⟩ := h
    have hb : b ≠ 0 := by rintro rfl; exact ha (by simpa using hc)
    have hψb : ψ b ≠ 0 := fun e => hb (hψ (e.trans (map_zero ψ).symm))
    have h1 : ψ b * (ψ c * d) = ψ b * 1 := by
      rw [mul_one]; nth_rewrite 2 [hd]; rw [hc, map_mul]; ring
    have hcu : IsUnit (ψ c) := IsUnit.of_mul_eq_one _ (mul_left_cancel₀ hψb h1)
    have hc' : IsUnit c := isUnit_of_map_unit ψ c hcu
    exact (Units.dvd_mul_right (u := hc'.unit)).mp (by rw [IsUnit.unit_spec, ← hc])

theorem dvd_of_forall_complete_dvr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [CharZero R] (f g : R), g ≠ 0 →
    (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V →
      ∀ ρ : R →+* V, Function.Injective ρ → IsLocalHom ρ → ρ g ∣ ρ f) → g ∣ f := by
  intro R _ _ _ _ _ _ f g hg H
  let K := FractionRing R
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hg' : algebraMap R K g ≠ 0 := fun e => hg (hinj (e.trans (map_zero _).symm))
  by_contra hnd
  have hx : ¬ ∀ V : ValuationSubring K, IsDiscreteValuationRing V → (∀ r, algebraMap R K r ∈ V) →
      (∀ r ∈ maximalIdeal R, algebraMap R K r ∈ V.nonunits) →
      algebraMap R K f / algebraMap R K g ∈ V := by
    intro hall
    obtain ⟨r, hr⟩ := GlobalTheory.exists_algebraMap_eq_of_forall_discreteValuationSubring (R := R) (K := K) hall
    apply hnd
    refine ⟨r, hinj ?_⟩
    rw [map_mul, hr, mul_div_cancel₀ _ hg']
  push_neg at hx
  obtain ⟨V, hV, h1, h2, hxV⟩ := hx
  have hdom : LocalSubring.range (algebraMap R K) ≤ V.toLocalSubring :=
    (GlobalTheory.localSubring_range_le_valuationSubring_iff _ _).mpr ⟨h1, h2⟩
  obtain ⟨-, hc, -, h, hρi, hρl⟩ :=
    (GlobalTheory.discreteValuationRing_dominating_noetherian_local R K K).2.2 V hdom
  have hd := H (AdicCompletion (maximalIdeal V) V) hc _ hρi hρl
  let a : V := ⟨algebraMap R K g, h g⟩
  let b : V := ⟨algebraMap R K f, h f⟩
  have ha : a ≠ 0 := fun e => hg' (congrArg Subtype.val e)
  obtain ⟨c, hcab⟩ := dvd_of_map_dvd_of_valuationRing (algebraMap V (AdicCompletion (maximalIdeal V) V))
    (GlobalTheory.algebraMap_adicCompletion_injective_of_dvr V) ha hd
  apply hxV
  have : algebraMap R K f = algebraMap R K g * (c : K) := congrArg Subtype.val hcab
  rw [this, mul_div_cancel_left₀ _ hg']
  exact c.2

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffCartierComapOfIdlAlong
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

namespace GlobalTheory.NormBlLift

theorem effCartier_comap_of_idlAlong {X : Scheme.{0}} (J : X.IdealSheafData) {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] (a : Sp R ⟶ X) (f : R) (hf : f ≠ 0) (hJ : idlAlong J a = Ideal.span {f}) :
    FinalTheorems.EffCartier (J.comap a) := by
  rw [idlAlong_eq_idealAlong, GlobalTheory.IndefiniteRowSideFullHecke.NormalisedBlowupCone.idealAlong] at hJ
  set e := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv with he
  have hI : (J.comap a).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {e.symm f} := by
    have h2 := congrArg (Ideal.map e.symm.toRingHom) hJ
    rw [Ideal.map_span, Set.image_singleton, Ideal.map_map] at h2
    have : e.symm.toRingHom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom = RingHom.id _ := by
      ext x; exact e.symm_apply_apply x
    rw [this, Ideal.map_id] at h2
    exact h2
  intro x
  refine ⟨⟨⊤, isAffineOpen_top _⟩, e.symm f, trivial, ?_, hI⟩
  rw [mem_nonZeroDivisors_iff]
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · apply e.injective
    have := congrArg e hz
    rw [map_mul, map_zero, e.apply_symm_apply] at this
    rw [map_zero]; exact (mul_eq_zero.1 this).resolve_left hf
  · apply e.injective
    have := congrArg e hz
    rw [map_mul, map_zero, e.apply_symm_apply] at this
    rw [map_zero]; exact (mul_eq_zero.1 this).resolve_right hf

end GlobalTheory.NormBlLift

namespace GlobalTheory.NormBlLift

theorem lift_normBl : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z S : Scheme.{0}) (i : F.X ⟶ Z) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] [IsOpenImmersion i] (J : Z.IdealSheafData), IsNormBl π J → j ≫ π = i → π ⁻¹' Set.range i = Set.range j → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (a : Sp R ⟶ Z) (y : Sp (FractionRing R) ⟶ F.X), jK R ≫ a = y ≫ i → ∀ f : R, f ≠ 0 → idlAlong J a = Ideal.span {f} → ∃! ξ : Sp R ⟶ S, ξ ≫ π = a := by
  intro g n F Z S i π j _ _ J hN hji hpre R _ _ _ _ _ a y hy f hf hJ
  obtain ⟨-, S₀, π₀, ν, U, hB, hνπ, hfin, -, -, -⟩ := hN
  have hE : FinalTheorems.EffCartier (J.comap a) := effCartier_comap_of_idlAlong J a f hf hJ
  have hEK : FinalTheorems.EffCartier (J.comap (jK R ≫ a)) := by
    refine effCartier_comap_of_idlAlong J (jK R ≫ a) (algebraMap R (FractionRing R) f) ?_ ?_
    · exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hf
    · rw [show jK R = spMap (algebraMap R (FractionRing R)) from rfl, GlobalTheory.TraitOrder.idlAlong_comp, hJ,
        Ideal.map_span, Set.image_singleton]
  obtain ⟨b, hb, hbu⟩ := hB.2 _ a hE
  have hK : (y ≫ j) ≫ ν = jK R ≫ b := by
    refine (hB.2 _ _ hEK).unique ?_ ?_
    · rw [Category.assoc, Category.assoc, hνπ, hji, hy]
    · rw [Category.assoc, hb]
  have L := GlobalTheory.existsUnique_lift_spec_of_isLocalization (nonZeroDivisors R) le_rfl ν (y ≫ j) b hK
  obtain ⟨c, ⟨hc1, hc2⟩, -⟩ := L
  refine ⟨c, by show c ≫ π = a; rw [← hνπ, ← Category.assoc, hc2, hb], fun c' hc' => ?_⟩
  have h1 : c' ≫ ν = b := hbu _ (by show (c' ≫ ν) ≫ π₀ = a; rw [Category.assoc, hνπ]; exact hc')
  have hr : Set.range (jK R ≫ c') ⊆ Set.range j := by
    rintro _ ⟨w, rfl⟩
    rw [← hpre]
    show π ((jK R ≫ c') w) ∈ Set.range i
    rw [← Scheme.Hom.comp_apply, Category.assoc, hc', hy, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have h2 : jK R ≫ c' = y ≫ j := by
    have hl := IsOpenImmersion.lift_fac j (jK R ≫ c') hr
    rw [← hl]
    congr 1
    rw [← cancel_mono i, ← hji, ← Category.assoc, hl, Category.assoc, hc', hy, hji]
  exact (GlobalTheory.existsUnique_lift_spec_of_isLocalization (nonZeroDivisors R) le_rfl ν (y ≫ j) b hK).unique ⟨h2, h1⟩ ⟨hc1, hc2⟩

end GlobalTheory.NormBlLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffectiveCartierIdealSheafLeOfClosedPoints
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.EffCartierData

theorem idealSheaf_le_of_closedPoints : ∀ (X : Scheme.{0}) [CompactSpace X] (D : EffCartierData X)
    (K : X.IdealSheafData), (∀ x : X, IsClosed ({x} : Set X) → ∃ (W : X.affineOpens) (i : D.ι)
      (h : W.1 ≤ D.U i), x ∈ W.1 ∧ resG X h (D.f i) ∈ K.ideal W) → D.idealSheaf ≤ K := by
  intro X _ D K hK
  have hc : ∀ y : X, ∃ x : X, IsClosed ({x} : Set X) ∧ y ⤳ x := fun y => by
    obtain ⟨x, hx, hxc⟩ := (isClosed_closure (s := ({y} : Set X))).exists_closed_singleton
      ⟨y, subset_closure rfl⟩
    exact ⟨x, hxc, specializes_iff_mem_closure.2 hx⟩
  choose x hxc hyx using hc
  choose W i h hxW hmem using fun y => hK (x y) (hxc y)
  refine Scheme.IdealSheafData.le_of_iSup_eq_top W
    (eq_top_iff.2 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, (hyx y).mem_open (W y).1.isOpen (hxW y)⟩)
    fun y => ?_
  rw [D.ideal_idealSheaf (W y) (i y) (h y), Ideal.span_singleton_le_iff_mem]
  exact hmem y

end GlobalTheory.EffCartierData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffectiveGenerationCanonicalNefNumberFieldStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.effective_generation_canonical_nef_numberField : GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.NefNumerics → ∀ (F : Type) [Field F] [NumberField F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (D : ℕ) [SmoothOfRelativeDimension D p], IsProjOver p → GeometricallyConnected p → 1 ≤ D → letI := algebraΓOfHom p; ∀ (K : CanonLB p D) (N N' B : LB Y) (hN : N.IsLB) (hN' : N'.IsLB) (hB : B.IsLB) (a m : ℕ) (y : Y), IsNef F N → IsNef F N' → (D + 1).choose 2 < m → (∃ (N₁ N₂ : LB Y) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB), 0 < a ∧ a • cls N hN = cls N₁ h₁ + cls N₂ h₂ ∧ AmpleAt N₁ y ∧ IsNef F N₂) → cls B hB = m • cls N hN + cls N' hN' → ∃ s : (tens K.bundle B).Sec, y ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.EffGen.effective_generation | exact GlobalTheory.EffGen.effective_generation | (intros; apply GlobalTheory.EffGen.effective_generation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFrameCoordinatesLocallyConstantUpToUnits
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.FrameSpread

open GlobalTheory.Toroidal (gen genι genStr)
open GlobalTheory.ShFam

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem isMap_trans {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {φ'' : c.F →+* R''} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} {x'' : Sp R'' ⟶ Z.X} {F : EigFrame Z φ x}
    {F' : EigFrame Z φ' x'} {F'' : EigFrame Z φ'' x''} {a : R →+* R'} {b : R' →+* R''} (h1 : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v F embτ basisIdx) a F')
    (h2 : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v F embτ basisIdx) (b.comp a) F'') : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v F' embτ basisIdx) b F'' := fun τ i => by
  rw [h2 τ i, h1 τ i, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.dualMap_comp]

end

theorem unitAt_det_co : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] (x : X₀ TF.Y Z) (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((X₀ TF.Y Z).fromSpecStalk x ≫ (barComp TF.Y Z).ι)), (X₀ TF.Y Z).fromSpecStalk x ≫ s₀ TF.Y Z = spMap φ → ∃ U : (X₀ TF.Y Z).Opens, x ∈ U ∧ ∀ y ∈ U, ∀ (φ' : c.F →+* (X₀ TF.Y Z).presheaf.stalk y) (f' : GlobalTheory.ShFam.EigFrame TF.Y φ' ((X₀ TF.Y Z).fromSpecStalk y ≫ (barComp TF.Y Z).ι)) (φK : c.F →+* (X₀ TF.Y Z).functionField) (fK fK' : GlobalTheory.ShFam.EigFrame TF.Y φK ((X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι)), (X₀ TF.Y Z).fromSpecStalk y ≫ s₀ TF.Y Z = spMap φ' → (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ s₀ TF.Y Z = spMap φK → (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) (algebraMap _ (X₀ TF.Y Z).functionField) fK → (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f' embτ basisIdx) (algebraMap _ (X₀ TF.Y Z).functionField) fK' → ∀ τ, UnitAt y (fK'.co fK τ).det := by
  intro E _ _ _ H Dw l Xo c TF Z _ x φ f hφ
  haveI : IsIso (genι TF.Y) := GlobalTheory.VarFlag.isIso_genι
  let e : X₀ TF.Y Z ⟶ gen TF.Y := (barComp TF.Y Z).ι ≫ inv (genι TF.Y)
  have he : e ≫ genι TF.Y = (barComp TF.Y Z).ι := by simp [e]
  have hstrY : genStr TF.Y = genι TF.Y ≫ TF.Y.s := by
    have h0 : genι TF.Y ≫ TF.Y.s = genStr TF.Y ≫ spMap (RingHom.id c.F) := pullback.condition
    have h1 : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
    rw [h1, Category.comp_id] at h0
    exact h0.symm
  obtain ⟨U, hU, φU, F, hxU, hUstr, -⟩ :=
    GlobalTheory.ShFam.EigSpread.exists_stable_eigFrame E H Dw l Xo c c.F (RingHom.id c.F) TF.Y (e x)
  let ψ : ∀ p : X₀ TF.Y Z, e p ∈ U → (Γ(gen TF.Y, U) →+* (X₀ TF.Y Z).presheaf.stalk p) := fun p hp =>
    (e.stalkMap p).hom.comp ((gen TF.Y).presheaf.germ U (e p) hp).hom
  have hψ : ∀ p hp, (X₀ TF.Y Z).fromSpecStalk p ≫ e = spMap (ψ p hp) ≫ hU.fromSpec := by
    intro p hp
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← hU.fromSpecStalk_eq_fromSpecStalk hp, IsAffineOpen.fromSpecStalk,
      ← Category.assoc, ← Spec.map_comp]
    rfl
  have hmono : ∀ {R : Type} [CommRing R] (a b : Γ(gen TF.Y, U) →+* R),
      spMap a ≫ hU.fromSpec = spMap b ≫ hU.fromSpec → a = b := fun a b h =>
    GlobalTheory.ShFam.EigLoc.spMap_inj ((cancel_mono hU.fromSpec).1 h)
  have hring : ∀ {R : Type} [CommRing R] (q : Sp R ⟶ X₀ TF.Y Z) (ρ : c.F →+* R) (a : Γ(gen TF.Y, U) →+* R),
      q ≫ s₀ TF.Y Z = spMap ρ → q ≫ e = spMap a ≫ hU.fromSpec → ρ = a.comp φU := by
    intro R _ q ρ a h1 h2
    apply GlobalTheory.ShFam.EigLoc.spMap_inj
    rw [← h1, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hUstr, ← Category.assoc (spMap a), ← h2, hstrY]
    simp only [Category.assoc]
    rw [← Category.assoc e, he]
  have hpt : ∀ p hp, (X₀ TF.Y Z).fromSpecStalk p ≫ (barComp TF.Y Z).ι = spMap (ψ p hp) ≫ hU.fromSpec ≫ genι TF.Y := by
    intro p hp
    rw [← he, ← Category.assoc, hψ p hp, Category.assoc]
  have hgen : ∀ p : X₀ TF.Y Z, (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) =
      spMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk p) (X₀ TF.Y Z).functionField) ≫ (X₀ TF.Y Z).fromSpecStalk p :=
    fun p =>
      (Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec (X₀ TF.Y Z)).specializes (Set.mem_univ p))).symm
  obtain ⟨Fx, hFx⟩ := F.exists_isMap (ψ x hxU) (hring _ φ _ hφ (hψ x hxU)) (hpt x hxU)
  have hWx : ∀ τ, UnitAt x (algebraMap _ (X₀ TF.Y Z).functionField (Fx.co f τ).det) :=
    fun τ => ⟨_, EigFrame.isUnit_det_co Fx f τ, rfl⟩
  choose W hxW hW using fun τ => (hWx τ).exists_nhds
  refine ⟨⟨(e ⁻¹ᵁ U : Set (X₀ TF.Y Z)) ∩ ⋂ τ, (W τ : Set (X₀ TF.Y Z)),
    (e ⁻¹ᵁ U).isOpen.inter (isOpen_iInter_of_finite fun τ => (W τ).isOpen)⟩,
    ⟨hxU, Set.mem_iInter.2 hxW⟩, ?_⟩
  rintro y ⟨hyU, hyW⟩ φ' f' φK fK fK' hφ' hφK hfK hfK' τ
  rw [Set.mem_iInter] at hyW
  have hyU' : e y ∈ U := hyU
  obtain ⟨Fy, hFy⟩ := F.exists_isMap (ψ y hyU') (hring _ φ' _ hφ' (hψ y hyU')) (hpt y hyU')
  have hKp : ∀ p hp, spMap ((algebraMap ((X₀ TF.Y Z).presheaf.stalk p) (X₀ TF.Y Z).functionField).comp (ψ p hp)) ≫
      hU.fromSpec = (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ e := by
    intro p hp
    rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk p) (X₀ TF.Y Z).functionField)
      (ψ p hp), Category.assoc, ← hψ, ← Category.assoc, ← hgen]
  have hK : (algebraMap ((X₀ TF.Y Z).presheaf.stalk y) (X₀ TF.Y Z).functionField).comp (ψ y hyU') =
      (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField).comp (ψ x hxU) :=
    hmono _ _ ((hKp y hyU').trans (hKp x hxU).symm)
  have hKpt := (hKp y hyU').symm
  obtain ⟨FK, hFK⟩ := F.exists_isMap
    ((algebraMap ((X₀ TF.Y Z).presheaf.stalk y) (X₀ TF.Y Z).functionField).comp (ψ y hyU'))
    (x' := (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι)
    (hring _ φK _ hφK hKpt) (by rw [← he]; exact (reassoc_of% hKpt) (genι TF.Y))
  have hFyK : Fy.IsMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk y) (X₀ TF.Y Z).functionField) FK :=
    isMap_trans hFy hFK
  have hFxK : Fx.IsMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField) FK :=
    isMap_trans hFx (by rw [← hK]; exact hFK)
  have hy : (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι =
      spMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk y) (X₀ TF.Y Z).functionField) ≫ (X₀ TF.Y Z).fromSpecStalk y ≫ (barComp TF.Y Z).ι := by
    rw [hgen y, Category.assoc]
  have hx : (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι =
      spMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField) ≫ (X₀ TF.Y Z).fromSpecStalk x ≫ (barComp TF.Y Z).ι := by
    rw [hgen x, Category.assoc]
  have e1 := EigFrame.IsMap.co (τ := τ) hfK' hFyK hy
  have e2 := EigFrame.IsMap.co (τ := τ) hFxK hfK hx
  have dmap : ∀ {R S : Type} [CommRing R] [CommRing S] (g : R →+* S) {n : ℕ} (M : Matrix (Fin n) (Fin n) R),
      (M.map g).det = g M.det := fun g _ M => (RingHom.map_det g M).symm
  rw [← EigFrame.co_mul fK' FK fK τ, Matrix.det_mul, e1, dmap]
  refine UnitAt.mul ⟨_, EigFrame.isUnit_det_co f' Fy τ, rfl⟩ ?_
  convert hW τ y (hyW τ) using 1
  erw [e2]
  exact dmap _ _

end GlobalTheory.FrameSpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenTopFormFrameOfStalkKaehlerBasisStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_topFormFrame_of_stalkKaehlerBasis : ∀ (k : Type) [Field k] (X : Scheme.{0}) (p : X ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n p] (U : X.affineOpens) (x₀ : X) (hx : x₀ ∈ U.1) (x : Fin n → Γ(X, U.1)), (letI := ((X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1)).toAlgebra; ∃ bs : Module.Basis (Fin n) (X.presheaf.stalk x₀) Ω[X.presheaf.stalk x₀⁄k], ∀ i, bs i = KaehlerDifferential.D k (X.presheaf.stalk x₀) ((X.presheaf.germ U.1 x₀ hx).hom (x i))) → ∃ s : Γ(X, U.1), x₀ ∈ X.basicOpen s ∧ GlobalTheory.TopForm.IsFrame (GlobalTheory.TopForm.dOn p fun i => resG X (X.basicOpen_le s) (x i)) := by
  first | exact @GlobalTheory.FrameSpread.exists_basicOpen_isFrame_dOn | exact GlobalTheory.FrameSpread.exists_basicOpen_isFrame_dOn | (intros; apply GlobalTheory.FrameSpread.exists_basicOpen_isFrame_dOn <;> assumption)
end

