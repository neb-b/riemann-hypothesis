module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericInvariantsGeneratedByRatios
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfTorusBased

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPointOfRingHom
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

theorem exists_point_of_ringHom {o Ω K : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Field K] (M : RatModel o Ω)
    {U : M.Z.Opens} (hU : IsAffineOpen U) (hne : (U : Set M.Z).Nonempty) (φ : M.ringOn U →+* K) :
    ∃ x : Sp K ⟶ M.Z, Set.range x ⊆ U ∧ (∀ a : M.ringOn U, φ a = M.val x a) ∧
      x ≫ M.s = spMap (φ.comp (algebraMap o _)) := by
  let ψ : Γ(M.Z, U) ⟶ CommRingCat.of K := CommRingCat.ofHom (φ.comp (M.sectionsEquiv U hne).toRingHom)
  have hx := le_preimage_specMap_fromSpec hU ψ
  have hv : ∀ f, valR (Spec.map ψ ≫ hU.fromSpec) U f = φ (M.sectionsEquiv U hne f) := fun f => by
    rw [valR_eq _ U hx, valMap_specMap_fromSpec]
    rfl
  have hr := (top_le_preimage_iff _ _).1 hx
  refine ⟨Spec.map ψ ≫ hU.fromSpec, hr, fun a => ?_, ?_⟩
  · obtain ⟨f, rfl⟩ := (M.sectionsEquiv U hne).surjective a
    rw [coe_sectionsEquiv, val_valF hr]
    exact (hv f).symm
  · rw [← Spec.map_preimage ((Spec.map ψ ≫ hU.fromSpec) ≫ M.s)]
    refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun b => ?_))
    rw [← valR_constFn M.s _ U hx, hv]
    exact congrArg φ (Subtype.ext ((coe_sectionsEquiv U hne _).trans (M.valF_constFn hne b)))

theorem exists_cen_of_ringHom : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (U : M.Z.Opens), IsProper M.s → IsAffineOpen U → (U : Set M.Z).Nonempty → ∀ (p : ℕ) [Fact p.Prime]
    (y' : M.ringOn U →+* PadicAlgCl p), (∀ b : o, ‖y' (algebraMap o _ b)‖ ≤ 1) →
    ∃ (z : M.Z) (y : Sp (OO p) ⟶ M.Z), M.Cen U z y ∧ ∀ a : M.ringOn U, y' a = M.val (gPt p ≫ y) a := by
  intro o Ω _ _ _ M U hs hU hne p _ y' hy'
  obtain ⟨x, hx, hv, hxs⟩ := M.exists_point_of_ringHom hU hne y'
  let σ : o →+* OO p := (y'.comp (algebraMap o _)).codRestrict (OO p).toSubring
    fun b => (mem_OO_iff _).2 (hy' b)
  obtain ⟨y, hy, -⟩ := exists_valuativeExtension (V := OO p) (K := PadicAlgCl p) M.s (spMap σ) x (by
    rw [hxs, ← Spec.map_comp]
    rfl)
  have hy2 : gPt p ≫ y = x := hy
  exact ⟨_, y, ⟨rfl, hy2 ▸ hx⟩, hy2 ▸ hv⟩

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveClosureIsProjOver
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH

open GlobalTheory.Points GlobalTheory.ProjSpace GlobalTheory.TuplePoint

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {n : ℕ} {t : Fin (n + 1) → Ω}

theorem exists_div_of_closure_ratios_eq_top
    (h : Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i}) = ⊤) {i : Fin (n + 1)}
    (hi : t i ≠ 0) (x : Ω) : ∃ a ∈ Algebra.adjoin o (Set.range fun j => t j / t i),
      ∃ b ∈ Algebra.adjoin o (Set.range fun j => t j / t i), a / b = x := by
  have hle : Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i}) ≤
      Subfield.closure ((Algebra.adjoin o (Set.range fun j => t j / t i)).toSubring : Set Ω) := by
    refine Subfield.closure_le.2 ?_
    rintro _ (⟨a, rfl⟩ | ⟨k, j, rfl⟩)
    · exact Subfield.subset_closure (Subalgebra.algebraMap_mem _ a)
    · rw [← div_div_div_cancel_right₀ hi]
      exact div_mem (Subfield.subset_closure (Algebra.subset_adjoin ⟨j, rfl⟩))
        (Subfield.subset_closure (Algebra.subset_adjoin ⟨k, rfl⟩))
  have hx := hle (h ▸ Subfield.mem_top x)
  rwa [Subfield.mem_closure_iff, Subring.closure_eq] at hx

section Closed

variable {ht : t ≠ 0} {Z : Scheme.{0}} {ξ : Sp Ω ⟶ Z} {π : Z ⟶ PSpace o n} (hπ : ξ ≫ π = point o t ht)

include hπ

theorem exists_valF_preimage_chart_iff [IsClosedImmersion π] {i : Fin (n + 1)} (hi : t i ≠ 0) (x : Ω) :
    (∃ f : Γ(Z, π ⁻¹ᵁ chart o n i), valF ξ _ f = x) ↔ x ∈ Algebra.adjoin o (Set.range fun j => t j / t i) := by
  have h := (le_point_preimage_iff (o := o) (ht := ht) i).2 hi
  have key : ∀ g, valF ξ _ ((π.app (chart o n i)).hom g) = (valMap (point o t ht) _ h).hom g := fun g => by
    rw [← valR_eq, ← hπ]
    exact (valR_comp ξ π _ g).symm
  rw [← SetLike.mem_coe, ← range_valMap_point h]
  constructor
  · rintro ⟨f, rfl⟩
    obtain ⟨g, rfl⟩ := π.app_surjective _ (isAffineOpen_chart o n i) f
    exact ⟨g, (key g).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨_, key g⟩

end Closed

theorem exists_valF_eq_div {Z : Scheme.{0}} (ξ : Sp Ω ⟶ Z) {U : Z.Opens} (hU : ⊤ ≤ ξ ⁻¹ᵁ U) (a b : Γ(Z, U))
    (hb : valF ξ U b ≠ 0) : ⊤ ≤ ξ ⁻¹ᵁ Z.basicOpen b ∧
      ∃ f : Γ(Z, Z.basicOpen b), valF ξ _ f = valF ξ U a / valF ξ U b := by
  have hle : ⊤ ≤ ξ ⁻¹ᵁ Z.basicOpen b := (le_preimage_basicOpen_iff _ hU b).2 (isUnit_iff_ne_zero.2 hb)
  have hu : IsUnit (resG _ (Z.basicOpen_le b) b) :=
    RingedSpace.isUnit_res_basicOpen Z.toLocallyRingedSpace.toRingedSpace b
  obtain ⟨c, hc⟩ := hu.exists_right_inv
  have h1 : valR ξ (Z.basicOpen b) (resG _ (Z.basicOpen_le b) b * c) = 1 :=
    (congrArg _ hc).trans (valR_one _ _ hle)
  rw [valR_mul _ _ hle] at h1
  have h2 : ∀ s, valR ξ (Z.basicOpen b) (resG _ (Z.basicOpen_le b) s) = valF ξ U s :=
    fun s => valR_res _ _ hle _
  refine ⟨hle, resG _ (Z.basicOpen_le b) a * c, (valR_mul _ _ hle _ _).trans ?_⟩
  rw [h2 b] at h1
  rw [h2 a, eq_inv_of_mul_eq_one_right h1, div_eq_mul_inv]

theorem RatModel.isCl_of_isClosedImmersion (M : RatModel o Ω) {ht : t ≠ 0} (π : M.Z ⟶ PSpace o n)
    [IsClosedImmersion π] (hπ : M.pt ≫ π = point o t ht) : M.IsCl t := by
  have h1 : ∀ (k : Fin (n + 1)) (z : M.Z), z ∈ π ⁻¹ᵁ chart o n k → M.Div t k z := fun k z hz =>
    have hW := M.top_le_preimage_pt ⟨z, hz⟩
    ⟨ne_zero_of_le hπ hW le_rfl, fun j => ⟨_, pullRatio π _ k le_rfl j, hz, valR_pullRatio hπ hW le_rfl j⟩⟩
  have h2 : ∀ (i : Fin (n + 1)) (z : M.Z), M.Div t i z → z ∈ π ⁻¹ᵁ chart o n i := fun i z hz => by
    obtain ⟨k, hk⟩ := exists_mem_chart o n (π z)
    have hk' : z ∈ π ⁻¹ᵁ chart o n k := hk
    have hu := ((h1 k z hk').div_iff_isUnit i).1 hz
    have e : (⟨t i / t k, (h1 k z hk').2 i⟩ : M.O z) =
        ⟨_, RatModel.valF_mem_O hk' (pullRatio π _ k le_rfl i)⟩ :=
      Subtype.ext (valR_pullRatio hπ (M.top_le_preimage_pt ⟨z, hk'⟩) le_rfl i).symm
    rw [e, RatModel.isUnit_valF_iff hk', basicOpen_pullRatio] at hu
    exact hu.2
  refine ⟨fun z => (exists_mem_chart o n (π z)).imp fun k hk => h1 k z hk, fun i hi => ?_⟩
  refine ⟨π ⁻¹ᵁ chart o n i, (isAffineOpen_chart o n i).preimage π,
    Set.ext fun z => ⟨h1 i z, h2 i z⟩, ?_⟩
  ext x
  rw [RatModel.mem_ringOn_iff_exists ⟨_, h2 i _ (RatModel.div_genericPoint hi)⟩,
    exists_valF_preimage_chart_iff hπ hi]

theorem exists_isCl_isProjOver : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] (n : ℕ) (t : Fin (n + 1) → Ω), (∃ i, t i ≠ 0) → Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i}) = ⊤ → ∃ M : RatModel o Ω, M.IsCl t ∧ IsProjOver M.s := by
  intro o Ω _ _ _ _ n t ⟨i, hi⟩ h
  have ht : t ≠ 0 := Function.ne_iff.2 ⟨i, hi⟩
  let φ := point o t ht
  have hsep : IsProper (PSpace.str o n) :=
    projProper o _ _ ⟨n, 𝟙 _, inferInstance, Category.id_comp _⟩
  have hqc : QuasiCompact φ := by
    have : QuasiCompact (φ ≫ PSpace.str o n) := by
      rw [point_str]
      infer_instance
    exact QuasiCompact.of_comp φ (PSpace.str o n)
  have hπ : φ.toImage ≫ φ.imageι = point o t ht := φ.toImage_imageι
  have hW := le_preimage_chart hπ hi
  let M : RatModel o Ω :=
    { Z := φ.image
      s := φ.imageι ≫ PSpace.str o n
      sep := inferInstance
      lft := inferInstance
      qc := inferInstance
      pt := φ.toImage
      pt_s := by rw [← Category.assoc, hπ, point_str]
      gen := by
        have e : Set.range φ.toImage = {φ.toImage (IsLocalRing.closedPoint Ω)} :=
          Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, rfl⟩, by
            rintro _ ⟨w, rfl⟩
            rw [Subsingleton.elim w (IsLocalRing.closedPoint Ω)]⟩
        have hd : IsGenericPoint (φ.toImage (IsLocalRing.closedPoint Ω)) Set.univ := by
          rw [isGenericPoint_def, ← e]
          exact φ.toImage.denseRange.closure_range
        rw [e, hd.eq (genericPoint_spec _)]
      onto := fun x => by
        obtain ⟨_, ha, _, hb, rfl⟩ := exists_div_of_closure_ratios_eq_top h hi x
        obtain ⟨a, rfl⟩ := (exists_valF_preimage_chart_iff hπ hi _).2 ha
        obtain ⟨b, rfl⟩ := (exists_valF_preimage_chart_iff hπ hi _).2 hb
        by_cases h0 : valF φ.toImage _ b = 0
        · exact ⟨_, b, ⟨_, hW (x := IsLocalRing.closedPoint Ω) trivial⟩, by rw [h0, div_zero]⟩
        · obtain ⟨hle, f, hf⟩ := exists_valF_eq_div _ hW a b h0
          exact ⟨_, f, ⟨_, hle (x := IsLocalRing.closedPoint Ω) trivial⟩, hf⟩ }
  exact ⟨M, M.isCl_of_isClosedImmersion φ.imageι hπ, n, φ.imageι, inferInstance, rfl⟩

end GlobalTheory.ZH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRatioOfWeightSums
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.WtRat

section
variable {k : Type} [Field k] {X : Type} [AddCommGroup X] {R : Type} [CommRing R] {s : Sp R ⟶ Sp k}

def chr (t : Over.mk s ⟶ splitTorus (Sp k) X) (χ : X) : R :=
  ev (R := R) t.left ⊤ le_top (charUnit (Sp k) X χ).val

theorem chr_eq (t : Over.mk s ⟶ splitTorus (Sp k) X) (χ : X) :
    chr t χ = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      (splitTorusPointsEquiv (Sp k) X (Over.mk s) t (Multiplicative.ofAdd χ)).val := by
  rw [splitTorusPointsEquiv_val]
  exact ev_top (R := R) t.left le_top _

theorem chr_mul (t t' : Over.mk s ⟶ splitTorus (Sp k) X) (χ : X) :
    chr (t * t') χ = chr t χ * chr t' χ := by
  rw [chr_eq, chr_eq, chr_eq, map_mul, MonoidHom.mul_apply, Units.val_mul]
  exact map_mul _ _ _

theorem chr_one (χ : X) : chr (1 : Over.mk s ⟶ splitTorus (Sp k) X) χ = 1 := by
  rw [chr_eq, map_one, MonoidHom.one_apply, Units.val_one]
  exact map_one _

theorem chr_add (t : Over.mk s ⟶ splitTorus (Sp k) X) (χ χ' : X) :
    chr t (χ + χ') = chr t χ * chr t χ' := by
  rw [chr_eq, chr_eq, chr_eq, ofAdd_add, map_mul, Units.val_mul]
  exact map_mul _ _ _

theorem chr_zero (t : Over.mk s ⟶ splitTorus (Sp k) X) : chr t 0 = 1 := by
  rw [chr_eq, ofAdd_zero, map_one, Units.val_one]
  exact map_one _

theorem chr_ext {t t' : Over.mk s ⟶ splitTorus (Sp k) X} (h : ∀ χ, chr t χ = chr t' χ) : t = t' := by
  refine (splitTorusPointsEquiv (Sp k) X _).injective (MonoidHom.ext fun χ => Units.ext ?_)
  refine (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1 ?_
  exact (chr_eq t χ.toAdd).symm.trans ((h _).trans (chr_eq t' χ.toAdd))

theorem chr_comp {R' : Type} [CommRing R'] {s' : Sp R' ⟶ Sp k} (e : R →+* R') (he : spMap e ≫ s = s')
    (t : Over.mk s ⟶ splitTorus (Sp k) X) (χ : X) :
    chr ((Over.homMk (spMap e) he : Over.mk s' ⟶ Over.mk s) ≫ t) χ = e (chr t χ) :=
  ev_spMap e t.left ⊤ le_top le_top _

theorem exists_chr (s : Sp R ⟶ Sp k) (u : Multiplicative X →* R) :
    ∃ t : Over.mk s ⟶ splitTorus (Sp k) X, ∀ χ, chr t χ = u (Multiplicative.ofAdd χ) := by
  refine ⟨(splitTorusPointsEquiv (Sp k) X (Over.mk s)).symm
    (MonoidHom.toHomUnits ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom.comp u)), fun χ => ?_⟩
  rw [chr_eq, MulEquiv.apply_symm_apply]
  exact congrArg (fun q => CommRingCat.Hom.hom q (u (Multiplicative.ofAdd χ)))
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id
end

theorem exists_rel {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] {X : Type} [AddCommGroup X]
    (i : splitTorus (Sp k) X ⟶ G) {F : Type} [Field F] {s : Sp F ⟶ Sp k} (g : Over.mk s ⟶ G)
    (U : G.left.Opens) (f : Γ(G.left, U)) (h₁ : ⊤ ≤ (((1 : Over.mk s ⟶ splitTorus (Sp k) X) ≫ i) * g).left ⁻¹ᵁ U) :
    ∃ (S : Finset X) (p q : X → F), ∑ χ ∈ S, p χ ≠ 0 ∧
      ∀ (t : Over.mk s ⟶ splitTorus (Sp k) X) (h : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ U),
        ev (R := F) ((t ≫ i) * g).left U h f * ∑ χ ∈ S, chr t χ * p χ = ∑ χ ∈ S, chr t χ * q χ := by
  classical
  let R := AddMonoidAlgebra F X
  let sR : Sp R ⟶ Sp k := spMap (algebraMap F R) ≫ s
  let π : Over.mk sR ⟶ Over.mk s := Over.homMk (spMap (algebraMap F R)) rfl
  obtain ⟨tR, htR⟩ := exists_chr (X := X) sR (AddMonoidAlgebra.of F X)
  let a : Over.mk sR ⟶ G := (tR ≫ i) * (π ≫ g)
  let cH (t : Over.mk s ⟶ splitTorus (Sp k) X) : Multiplicative X →* F :=
    { toFun := fun χ => chr t χ.toAdd, map_one' := chr_zero t, map_mul' := fun x y => chr_add t _ _ }
  let e (t : Over.mk s ⟶ splitTorus (Sp k) X) : R →+* F := (AddMonoidAlgebra.lift F F X (cH t)).toRingHom
  have hid (t) : spMap (e t) ≫ spMap (algebraMap F R) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    exact (AddMonoidAlgebra.lift F F X (cH t)).commutes x
  have he (t) : spMap (e t) ≫ sR = s := by
    rw [← Category.assoc, hid, Category.id_comp]
  have ha (t) : (Over.homMk (spMap (e t)) (he t) : Over.mk s ⟶ Over.mk sR) ≫ a = (t ≫ i) * g := by
    have h1 : (Over.homMk (spMap (e t)) (he t) : Over.mk s ⟶ Over.mk sR) ≫ tR = t := by
      refine chr_ext fun χ => ?_
      rw [chr_comp, htR]
      exact AddMonoidAlgebra.lift_of (cH t) (Multiplicative.ofAdd χ)
    have h2 : (Over.homMk (spMap (e t)) (he t) : Over.mk s ⟶ Over.mk sR) ≫ π = 𝟙 _ :=
      Over.OverMorphism.ext (hid t)
    rw [MonObj.comp_mul, ← Category.assoc, h1, ← Category.assoc, h2, Category.id_comp]
  have ha' (t) : spMap (e t) ≫ a.left = ((t ≫ i) * g).left := congrArg CommaMorphism.left (ha t)
  have hx : spMap (e 1) (IsLocalRing.closedPoint F) ∈ a.left ⁻¹ᵁ U := by
    have := h₁ (show IsLocalRing.closedPoint F ∈ (⊤ : (Sp F).Opens) from trivial)
    rw [← ha'] at this
    exact this
  obtain ⟨α, β, hβ, hαβ⟩ := GlobalTheory.T.exists_fraction_evalSection_affine_near_point R (a.left ⁻¹ᵁ U) ((a.left.appLE U _ le_rfl).hom f) _ hx
  have hsum (t) (w : R) (S : Finset X) (hS : w.coeff.support ⊆ S) : e t w = ∑ χ ∈ S, chr t χ * w.coeff χ := by
    show AddMonoidAlgebra.lift F F X (cH t) w = _
    rw [AddMonoidAlgebra.lift_apply, Finsupp.sum_of_support_subset _ hS _ (by simp)]
    exact Finset.sum_congr rfl fun χ _ => mul_comm _ _
  refine ⟨α.coeff.support ∪ β.coeff.support, β.coeff, α.coeff, ?_, fun t h => ?_⟩
  · have h2 := hsum 1 β _ (Finset.subset_union_right (s₁ := α.coeff.support))
    simp only [chr_one, _root_.one_mul] at h2
    rw [← h2]
    intro h0
    refine hβ ?_
    show e 1 β ∈ IsLocalRing.maximalIdeal F
    rw [h0]; exact zero_mem _
  · rw [← hsum t β _ Finset.subset_union_right, ← hsum t α _ Finset.subset_union_left]
    have h' : ⊤ ≤ (spMap (e t) ≫ a.left) ⁻¹ᵁ U := by rw [ha']; exact h
    refine Eq.trans ?_ (hαβ F (e t) h')
    congr 1
    exact (ev_congr (ha' t).symm U h h' f).trans (ev_appLE (spMap (e t)) a.left U _ le_rfl h' h' f).symm

theorem exists_ratio_of_weight_sums : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G), IsMonHom i → ∀ (U : G.left.Opens) (f : Γ(G.left, U)), (U : Set G.left).Nonempty → ∃ (U' : G.left.Opens) (h : U' ≤ U) (n : ℕ) (a b : Fin n → Γ(G.left, U')) (χ : Fin n → X), (U' : Set G.left).Nonempty ∧ (∀ j, Wt i U' (a j) (χ j) ∧ Wt i U' (b j) (χ j) ∧ (a j = 0 ∨ IsUnit (a j)) ∧ (b j = 0 ∨ IsUnit (b j))) ∧ IsUnit (∑ j, b j) ∧ (G.left.presheaf.map (homOfLE h).op).hom f * ∑ j, b j = ∑ j, a j := by
  intro k _ _ G _ hG X _ _ _ i hi U f hU
  obtain ⟨hc, hs, -, -, hgc⟩ := hG
  have : IsIntegral G.left := isIntegral_of_smooth_of_geometricallyConnected G.hom
  obtain ⟨F, _, g₀, hg, hinj, hσ, hsec⟩ := _root_.GlobalTheory.SS.WtRat.exists_generic_field_point G.left
  let s : Sp F ⟶ Sp k := g₀ ≫ G.hom
  let g : Over.mk s ⟶ G := Over.homMk g₀ rfl
  let pt (t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) : Over.mk s ⟶ splitTorus (Sp k) X := toUnit _ ≫ t
  have pt_mul (t t') : pt (t * t') = pt t * pt t' := MonObj.comp_mul _ _ _
  have pt_one : pt 1 = 1 := MonObj.comp_one _
  have hτ (t) : g₀ ≫ (transl (t ≫ i)).hom.left = ((pt t ≫ i) * g).left := by
    have : g ≫ (transl (t ≫ i)).hom = (pt t ≫ i) * g := by
      show g ≫ ((toUnit G ≫ t ≫ i) * 𝟙 G) = _
      rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit, ← Category.assoc]
    exact congrArg CommaMorphism.left this
  choose σ hσ' using fun t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X =>
    hσ ((Over.forget _).mapIso (transl (t ≫ i)))
  replace hσ' (t) : spMap (σ t) ≫ g₀ = ((pt t ≫ i) * g).left := (hσ' t).trans (hτ t)
  have hσs (t) : spMap (σ t) ≫ s = s := by
    show spMap (σ t) ≫ g₀ ≫ G.hom = s
    rw [← Category.assoc, hσ']
    exact Over.w _
  have hσpt (t t') : (Over.homMk (spMap (σ t)) (hσs t) : Over.mk s ⟶ Over.mk s) ≫ pt t' = pt t' := by
    show _ ≫ toUnit _ ≫ t' = _
    rw [← Category.assoc, comp_toUnit]
  have hσg (t t') : spMap (σ t) ≫ ((pt t' ≫ i) * g).left = ((pt (t' * t) ≫ i) * g).left := by
    have h1 : (Over.homMk (spMap (σ t)) (hσs t) : Over.mk s ⟶ Over.mk s) ≫ g = (pt t ≫ i) * g :=
      Over.OverMorphism.ext (hσ' t)
    have : (Over.homMk (spMap (σ t)) (hσs t) : Over.mk s ⟶ Over.mk s) ≫ ((pt t' ≫ i) * g) =
        (pt (t' * t) ≫ i) * g := by
      rw [MonObj.comp_mul, ← Category.assoc, hσpt, h1, pt_mul, MonObj.mul_comp, _root_.mul_assoc]
    exact congrArg CommaMorphism.left this
  have hgt (t) (V : G.left.Opens) (hV : (V : Set G.left).Nonempty) : ⊤ ≤ ((pt t ≫ i) * g).left ⁻¹ᵁ V := by
    rw [← hτ]
    obtain ⟨x, hx⟩ := hV
    obtain ⟨y, rfl⟩ := ((Over.forget _).mapIso (transl (t ≫ i))).hom.surjective x
    exact hg ((transl (t ≫ i)).hom.left ⁻¹ᵁ V) ⟨y, hx⟩
  have hone : ((pt 1 ≫ i) * g).left = g₀ := by
    rw [pt_one, MonObj.one_comp, _root_.one_mul]; rfl
  obtain ⟨S, p, q, hp, hrel⟩ := exists_rel i g U f (pt_one ▸ hgt 1 U hU)
  obtain ⟨χ₀, p', q', hp', hφ, hw⟩ := _root_.GlobalTheory.SS.exists_weighted_relation F _ X (fun t χ => chr (pt t) χ) σ
    (fun t => ev (R := F) ((pt t ≫ i) * g).left U (hgt t U hU) f) S p q
    (fun t t' χ => by rw [pt_mul, chr_mul]) (fun χ => by rw [pt_one, chr_one])
    (fun t t' χ => by rw [← chr_comp (σ t) (hσs t), hσpt])
    (fun t t' => (ev_spMap (σ t) _ U _ (hσg t t' ▸ hgt (t' * t) U hU) f).symm.trans
      (ev_congr (hσg t t') U _ _ f))
    (fun t => hrel (pt t) _) hp
  let ε := S.equivFin.symm
  have hε (r : X → F) : ∑ j, r (ε j) = ∑ χ ∈ S, r χ := by
    rw [← Finset.sum_coe_sort S r]
    exact Equiv.sum_comp ε fun x : S => r x
  obtain ⟨U', hU', u, hle, hu⟩ := hsec U hU (Option (Fin S.card ⊕ Fin S.card))
    (fun o => o.elim (∑ χ ∈ S, p' χ) (Sum.elim (fun j => q' (ε j)) fun j => p' (ε j)))
  have hwt (v : Γ(G.left, U')) (χ : X) (r : F) (hv : ev g₀ U' (hg U' hU') v = r)
      (hr : ∀ t, σ t r * chr (pt t) χ₀ = chr (pt t) χ * r) : Wt i U' v (χ - χ₀) := by
    refine GlobalTheory.T.splitTorusWeight_test_genericPoint_rationalPoints k G hs X i F s g hg U' v _ fun t h₁ h₂ => ?_
    have h3 : ev (R := F) ((pt t ≫ i) * g).left U' h₁ v = σ t r :=
      (ev_congr (hσ' t).symm U' h₁ (hσ' t ▸ h₁) v).trans
        ((ev_spMap (σ t) g₀ U' (hg U' hU') _ v).trans (congrArg (σ t) hv))
    have h4 : chr (pt t) χ₀ * chr (pt t) (-χ₀) = 1 := by rw [← chr_add, add_neg_cancel, chr_zero]
    refine h3.trans (Eq.trans ?_ (congrArg (chr (pt t) (χ - χ₀) * ·) hv.symm))
    rw [sub_eq_add_neg, chr_add]
    linear_combination chr (pt t) (-χ₀) * hr t - σ t r * h4
  have hun (o) : u o = 0 ∨ IsUnit (u o) := by
    refine (eq_or_ne _ 0).imp (fun h => hinj U' hU' ?_) (hu o).2
    rw [(hu o).1, h, map_zero]
  have hb : ev g₀ U' (hg U' hU') (∑ j, u (some (Sum.inr j))) = ∑ χ ∈ S, p' χ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← hε]
    exact Finset.sum_congr rfl fun j _ => (hu _).1
  refine ⟨U', hle, S.card, fun j => u (some (Sum.inl j)), fun j => u (some (Sum.inr j)), fun j => ε j - χ₀, hU',
    fun j => ⟨hwt _ _ _ (hu _).1 fun t => (hw t _ (ε j).2).2, hwt _ _ _ (hu _).1 fun t => (hw t _ (ε j).2).1,
      hun _, hun _⟩, ?_, hinj U' hU' ?_⟩
  · rw [hinj U' hU' (hb.trans (hu none).1.symm)]
    exact (hu none).2 hp'
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, hb, ev_res g₀ hle _ (hg U hU), ← ev_congr hone U (hgt 1 U hU), hφ, map_sum, ← hε]
    exact Finset.sum_congr rfl fun j _ => (hu (some (Sum.inl j))).1.symm

end GlobalTheory.SS.WtRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericInvariantsGeneratedByRatiosStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_invariants_generated_by_ratios : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → ∀ (a) (j : Fin d → C.I), C.Based c a j → ∀ i : splitTorus (Sp (FractionRing R)) (Fin d → ℤ) ⟶ ((Over.pullback (Out.jK R)).obj G), Charts.KerIs (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) a j i → (∀ a', Stable i ((C.pull (pullback.fst G.hom (Out.jK R))).W a')) → ∀ a' (u : Γ(((Over.pullback (Out.jK R)).obj G).left, (C.pull (pullback.fst G.hom (Out.jK R))).W a')), HasWt i _ u 0 → u ∈ Subring.closure (Set.range (((Over.pullback (Out.jK R)).obj G).hom.appLE ⊤ ((C.pull (pullback.fst G.hom (Out.jK R))).W a') le_top).hom ∪ {v | ∃ j', C.wt j' = C.c₀ ∧ v = (C.pull (pullback.fst G.hom (Out.jK R))).r a' j'}) := by
  first | exact @GlobalTheory.ZJ.GenericInv.generic_invariants | exact GlobalTheory.ZJ.GenericInv.generic_invariants | (intros; apply GlobalTheory.ZJ.GenericInv.generic_invariants <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsNmOfIsClVeronese
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem isNm_of_isCl_veronese : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (J : Type) [Fintype J] (t : J → Ω) (e n : ℕ) (z : Fin (n + 1) → Ω), 1 ≤ e → M.IsCl z → (∀ i, ∃ k, z k = t i ^ e) → (∀ i, t i ≠ 0 → ∀ x, x ∈ Algebra.adjoin o (Set.range fun k => z k / t i ^ e) ↔ IsIntegral (Algebra.adjoin o (Set.range fun j => t j / t i)) x) → (∀ k, z k ≠ 0 → ∃ c : J → Algebra.adjoin o (Set.range fun l => z l / z k), ∑ i, (c i : Ω) * (t i ^ e / z k) = 1) → M.IsNm t := by
  intro o Ω _ _ _ M J _ t e n z he hcl hk hint hsum
  choose κ hκ using hk
  have hle : ∀ k p, M.Div z k p → Algebra.adjoin o (Set.range fun l => z l / z k) ≤ M.O p :=
    fun k p h => Algebra.adjoin_le (by rintro _ ⟨l, rfl⟩; exact h.2 l)
  have hA : ∀ i p, M.Div z (κ i) p → M.Div t i p := by
    intro i p h
    have h0 : t i ≠ 0 := fun h0 => h.1 (by rw [hκ, h0, zero_pow (by omega)])
    refine ⟨h0, fun j => hle _ _ h ?_⟩
    rw [hκ, hint i h0]
    exact isIntegral_algebraMap (R := Algebra.adjoin o (Set.range fun j => t j / t i))
      (x := ⟨t j / t i, Algebra.subset_adjoin ⟨j, rfl⟩⟩)
  have hB : ∀ p, ∃ i, M.Div z (κ i) p := by
    intro p
    obtain ⟨k, hk⟩ := hcl.1 p
    obtain ⟨c, hc⟩ := hsum k hk.1
    have h1 : IsUnit (∑ i, (⟨c i, hle _ _ hk (c i).2⟩ : M.O p) * ⟨z (κ i) / z k, hk.2 _⟩) := by
      convert isUnit_one
      apply Subtype.ext
      simpa [hκ] using hc
    obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum h1
    exact ⟨i, (hk.div_iff_isUnit _).2 (isUnit_of_mul_isUnit_right hi)⟩
  have hC : ∀ i p, M.Div t i p → M.Div z (κ i) p := by
    intro i p h
    obtain ⟨i', hi'⟩ := hB p
    have h0 : z (κ i) ≠ 0 := by rw [hκ]; exact pow_ne_zero _ h.1
    refine ⟨h0, fun l => ?_⟩
    have h1 := mul_mem (hi'.2 l) (pow_mem (h.2 i') e)
    rwa [div_pow, ← hκ, ← hκ, div_mul_div_cancel₀ hi'.1] at h1
  refine ⟨fun p => (hB p).imp fun i hi => hA i p hi, fun i hi => ?_⟩
  obtain ⟨U, hU, hD, hR⟩ := hcl.2 (κ i) (by rw [hκ]; exact pow_ne_zero _ hi)
  refine ⟨U, hU, hD.trans (Set.ext fun p => ⟨hA i p, hC i p⟩), fun x => ?_⟩
  rw [hR, hκ]
  exact hint i hi x

end GlobalTheory.ZH
end

