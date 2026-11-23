module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsDenomOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAwaySurjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymmOfKsCoc
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0116
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsAffineOpenPreimageBasicOpen
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open TopologicalSpace

namespace GlobalTheory.AmpleSpread

open GlobalTheory.SecSpread GlobalTheory.LBGerm

variable {R : Type} [CommRing R] [IsDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  {X X' : Scheme.{0}} {p : X ⟶ Sp R} {φ : X' ⟶ X} {π : X' ⟶ Sp K}

theorem exists_const_mul_eq_zero (H : IsPullback φ π p (spMap (algebraMap R K))) {U : X.Opens}
    (hU : IsAffineOpen U) (a : Γ(X, U)) (h : ∀ z, φ z ∈ U → gs φ z U a = 0) :
    ∃ d : R, d ≠ 0 ∧ ∀ y ∈ U, cst p y d * gs (𝟙 X) y U a = 0 := by
  have e : (φ.app U).hom a = 0 := fn_ext fun z hz => by
    have hz' : φ z ∈ U := hz
    refine (gs_pull (𝟙 X') φ z U hz' _).trans ?_
    rw [Category.id_comp, h z hz', gs_zero (𝟙 X') z _ hz]
  let _ := (φ.app U).hom.toAlgebra
  have hl := GlobalTheory.QCoh.Qcqs.isLocalization_app (R := .of R) (L := .of K) (nonZeroDivisors R) H hU
  obtain ⟨⟨_, d, hd, rfl⟩, hm⟩ := (@IsLocalization.map_eq_zero_iff _ _ _ _ _ _ hl a).1 e
  refine ⟨d, nonZeroDivisors.ne_zero hd, fun y hy => ?_⟩
  have e' := congrArg (gs (𝟙 X) y U) (show constFn p U d * a = 0 from hm)
  rwa [gs_mul _ y _ hy, gs_constFn p U _ y hy, Category.id_comp, gs_zero _ y _ hy] at e'

theorem exists_sec_preimage_nonzeroLocus_eq (H : IsPullback φ π p (spMap (algebraMap R K))) [CompactSpace X]
    [X.IsSeparated] {L : LB X} (hL : L.IsLB) (s : (L.pull φ).Sec) :
    ∃ θ : L.Sec, φ ⁻¹ᵁ Out.nonzeroLocus θ = Out.nonzeroLocus s := by
  classical
  obtain ⟨α, _, V, c, hV, hle, hc⟩ := exists_finite_affine_refinement hL
  have loc : ∀ x : α, ∃ (d : R) (_ : d ≠ 0) (a : Γ(X, V x)), ∀ z, φ z ∈ V x → gs φ z (V x) a =
      cst (φ ≫ p) z d * gs (𝟙 X') z ((L.pull φ).U (fun _ => c x)) (s.f (fun _ => c x)) := by
    intro x
    have hle' : φ ⁻¹ᵁ V x ≤ (L.pull φ).U (fun _ => c x) := fun z hz => mem_pull.2 (hle x hz)
    obtain ⟨d, hd, a, ha⟩ := exists_denom_of_isAffineOpen H (hV x) (resG X' hle' (s.f (fun _ => c x)))
    refine ⟨d, hd, a, fun z hz => ?_⟩
    have e := congrArg (gs (𝟙 X') z _) ha
    have hz' : (𝟙 X' : X' ⟶ X') z ∈ φ ⁻¹ᵁ V x := hz
    rw [gs_mul _ z _ hz', gs_res _ z hle' hz', gs_pull (𝟙 X') φ z _ hz, gs_pull (𝟙 X') φ z _ hz,
      Category.id_comp, gs_constFn p _ φ z hz] at e
    exact e.symm
  choose d hd a ha using loc
  obtain ⟨b, hb⟩ : ∃ b : ∀ x, Γ(X, V x), ∀ x z, φ z ∈ V x → gs φ z (V x) (b x) =
      cst (φ ≫ p) z (∏ x, d x) * gs (𝟙 X') z ((L.pull φ).U (fun _ => c x)) (s.f (fun _ => c x)) :=
    ⟨fun x => constFn p _ (∏ w ∈ Finset.univ.erase x, d w) * a x, fun x z hz => by
      rw [gs_mul φ z _ hz, gs_constFn p _ φ z hz, ha x z hz, ← Finset.mul_prod_erase _ d (Finset.mem_univ x), cst_mul]
      ring⟩
  have kill : ∀ q : α × α, ∃ e : R, e ≠ 0 ∧ ∀ y ∈ V q.1 ⊓ V q.2, cst p y e * (gs (𝟙 X) y _ (b q.1) -
      (gm (𝟙 X) y (L.U (c q.1) ⊓ L.U (c q.2)) (L.g (c q.1) (c q.2))).val * gs (𝟙 X) y _ (b q.2)) = 0 := by
    rintro ⟨x, w⟩
    have l : V x ⊓ V w ≤ L.U (c x) ⊓ L.U (c w) := inf_le_inf (hle x) (hle w)
    have hx : ∀ {Z : Scheme.{0}} (r : Z ⟶ X) (y : Z), r y ∈ V x ⊓ V w → gs r y (V x ⊓ V w) (resG X inf_le_left (b x) -
        resG X l (L.g (c x) (c w)).val * resG X inf_le_right (b w)) =
        gs r y _ (b x) - (gm r y (L.U (c x) ⊓ L.U (c w)) (L.g (c x) (c w))).val * gs r y _ (b w) := fun r y hy => by
      rw [gs_sub _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy, gs_unit r y _ (l hy)]
    obtain ⟨e, he, h⟩ := exists_const_mul_eq_zero H ((hV x).inf (hV w)) _ fun z hz => (hx φ z hz).trans (by
      rw [hb x z hz.1, hb w z hz.2, pull_sec_trans s z (l hz).1 (l hz).2]
      ring)
    exact ⟨e, he, fun y hy => (congrArg _ (hx (𝟙 X) y hy)).symm.trans (h y hy)⟩
  choose e he hk using kill
  obtain ⟨θ, hθ⟩ := exists_sec_of_refinement hL V c hle hc (fun x => constFn p _ (∏ q, e q) * b x)
    fun y x w hx hw => by
      have h := hk (x, w) y ⟨hx, hw⟩
      rw [gs_mul _ y _ hx, gs_mul _ y _ hw, gs_constFn p _ _ y hx, gs_constFn p _ _ y hw, Category.id_comp,
        ← Finset.mul_prod_erase _ e (Finset.mem_univ (x, w)), cst_mul]
      linear_combination cst p y (∏ q ∈ Finset.univ.erase (x, w), e q) * h
  refine ⟨θ, Opens.ext (Set.ext fun z => ?_)⟩
  obtain ⟨x, hx⟩ := hc (φ z)
  have h₁ := congrArg (φ.stalkMap z).hom (hθ (φ z) (c x) x (hle x hx) hx)
  rw [map_mul, ← gs_stalkMap φ z _ (hle x hx), ← gs_stalkMap φ z _ hx, gs_mul φ z _ hx, gs_constFn p _ φ z hx,
    hb x z hx] at h₁
  refine (mem_nonzeroLocus_iff_pull θ φ z (hle x hx)).trans (Iff.trans ?_
    (mem_nonzeroLocus_iff_isUnit s (k := fun _ => c x) (mem_pull.2 (hle x hx))).symm)
  rw [h₁, IsUnit.mul_iff, IsUnit.mul_iff, IsUnit.mul_iff]
  exact ⟨fun h => h.2.2.2, fun h => ⟨(Units.isUnit _).map _,
    isUnit_cst H.w z (Finset.prod_ne_zero_iff.2 fun q _ => he q),
    isUnit_cst H.w z (Finset.prod_ne_zero_iff.2 fun q _ => hd q), h⟩⟩

theorem exists_basicOpen_le {V : (Sp R).Opens} (hV : genericPoint (Sp R) ∈ V) :
    ∃ f : R, f ≠ 0 ∧ PrimeSpectrum.basicOpen f ≤ V := by
  obtain ⟨_, ⟨f, rfl⟩, hf, hle⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hV V.isOpen
  refine ⟨f, ?_, hle⟩
  rintro rfl
  exact (PrimeSpectrum.mem_basicOpen _ _).1 hf (Ideal.zero_mem _)


omit [IsDomain R] in
theorem isAffineOpen_inf_preimage_basicOpen (p : X ⟶ Sp R) {U : X.Opens} (hU : IsAffineOpen U) (f : R) :
    IsAffineOpen (U ⊓ p ⁻¹ᵁ PrimeSpectrum.basicOpen f) := by
  have := hU.basicOpen (constFn p U f)
  have e := Scheme.basicOpen_appLE p U ⊤ le_top ((Scheme.ΓSpecIso (CommRingCat.of R)).inv f)
  rw [basicOpen_eq_of_affine] at e
  exact e ▸ this


set_option backward.isDefEq.respectTransparency false in
theorem exists_isAffineOpen_preimage_basicOpen (H : IsPullback φ π p (spMap (algebraMap R K))) [QuasiCompact p]
    [QuasiSeparated p] [IsAffine X'] : ∃ f : R, f ≠ 0 ∧ IsAffineOpen (p ⁻¹ᵁ PrimeSpectrum.basicOpen f) := by
  obtain ⟨e, he⟩ := IsGenericPointHom.fractionField R K
  have H' : IsPullback φ (π ≫ e.hom) p ((Sp R).fromSpecStalk (genericPoint (Sp R))) := by
    have h₀ : IsPullback (spMap (algebraMap R K)) e.hom (𝟙 _) ((Sp R).fromSpecStalk (genericPoint (Sp R))) :=
      IsPullback.of_vert_isIso ⟨(Category.comp_id _).trans he.symm⟩
    have := H.paste_vert h₀
    rwa [Category.comp_id] at this
  obtain ⟨hc⟩ := StalkLimit.nonempty_isLimit H'
  have (V : StalkLimit.AffNhd (genericPoint (Sp R))) : CompactSpace ((StalkLimit.diagram _ p).obj V) := by
    have : IsAffine V.1.toScheme := V.2.2
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd p V.1.ι)
  have (V : StalkLimit.AffNhd (genericPoint (Sp R))) : QuasiSeparatedSpace ((StalkLimit.diagram _ p).obj V) := by
    have : IsAffine V.1.toScheme := V.2.2
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd p V.1.ι)
  have : IsAffine (StalkLimit.cone H').pt := ‹IsAffine X'›
  obtain ⟨V, hV⟩ := Scheme.exists_isAffine_of_isLimit _ _ hc
  have : IsAffine (pullback p V.1.ι) := hV
  have h₁ : IsAffineOpen (p ⁻¹ᵁ V.1) := IsAffine.of_isIso (pullbackRestrictIsoRestrict p V.1).inv
  obtain ⟨f, hf, hle⟩ := exists_basicOpen_le V.2.1
  refine ⟨f, hf, ?_⟩
  have h₂ := isAffineOpen_inf_preimage_basicOpen p h₁ f
  rwa [inf_eq_right.2 (p.preimage_mono hle)] at h₂

theorem exists_preimage_basicOpen_le (H : IsPullback φ π p (spMap (algebraMap R K))) [UniversallyClosed p]
    {U : X.Opens} (hU : φ ⁻¹ᵁ U = ⊤) : ∃ f : R, f ≠ 0 ∧ p ⁻¹ᵁ PrimeSpectrum.basicOpen f ≤ U := by
  have hc : IsClosed (p '' (U : Set X)ᶜ) := p.isClosedMap _ U.isOpen.isClosed_compl
  obtain ⟨f, hf, hle⟩ := exists_basicOpen_le (V := ⟨_, hc.isOpen_compl⟩) (by
    rintro ⟨x, hx, e⟩
    obtain ⟨y, hy⟩ : genericPoint (Sp R) ∈ Set.range (spMap (algebraMap R K)) :=
      (IsGenericPointHom.fractionField R K).range_eq.ge rfl
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback H x y (e.trans hy.symm)
    exact hx (hU.ge (Set.mem_univ z)))
  exact ⟨f, hf, fun x hx => by_contra fun h => hle hx ⟨x, h, rfl⟩⟩

theorem exists_cover (H : IsPullback φ π p (spMap (algebraMap R K))) [IsProper p] {L : LB X} (hL : L.IsLB)
    (h : IsAmpleLB (L.pull φ)) :
    ∃ f : R, f ≠ 0 ∧ ∃ n, 1 ≤ n ∧ ∃ (N : ℕ) (θ : Fin (N + 1) → (lbPow L n).Sec),
      p ⁻¹ᵁ PrimeSpectrum.basicOpen f ≤ ⨆ i, Out.nonzeroLocus (θ i) ∧
      ∀ i, IsAffineOpen (Out.nonzeroLocus (θ i) ⊓ p ⁻¹ᵁ PrimeSpectrum.basicOpen f) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  obtain ⟨n, hn, N, s, hs, ha⟩ := h.exists_cover
  have hP := isLB_lbPow hL n
  choose t ht using fun i => exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_pull hP φ) (isLB_lbPow h.isLB n)
    (lbIso_lbPow_pull hL φ n).symm (s i)
  choose θ hθ using fun i => exists_sec_preimage_nonzeroLocus_eq H hP (t i)
  obtain ⟨f₀, hf₀, h₀⟩ := exists_preimage_basicOpen_le H (U := ⨆ i, Out.nonzeroLocus (θ i)) (by
    rw [Scheme.Hom.preimage_iSup, ← hs]
    exact iSup_congr fun i => (hθ i).trans (ht i))
  have aff : ∀ i, ∃ g : R, g ≠ 0 ∧ IsAffineOpen (Out.nonzeroLocus (θ i) ⊓ p ⁻¹ᵁ PrimeSpectrum.basicOpen g) := fun i => by
    have := isAffineHom_nonzeroLocus_ι hP (θ i)
    have : IsAffine (φ ⁻¹ᵁ Out.nonzeroLocus (θ i)) := by
      rw [hθ, ht]; exact ha i
    obtain ⟨g, hg, h₁⟩ := exists_isAffineOpen_preimage_basicOpen
      ((isPullback_morphismRestrict φ (Out.nonzeroLocus (θ i))).paste_vert H)
    refine ⟨g, hg, ?_⟩
    have h₂ : IsAffineOpen ((Out.nonzeroLocus (θ i)).ι ''ᵁ (Out.nonzeroLocus (θ i)).ι ⁻¹ᵁ
        p ⁻¹ᵁ PrimeSpectrum.basicOpen g) := h₁.image_of_isOpenImmersion (Out.nonzeroLocus (θ i)).ι
    rwa [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι] at h₂
  choose g hg hga using aff
  refine ⟨f₀ * ∏ i, g i, mul_ne_zero hf₀ (Finset.prod_ne_zero_iff.2 fun i _ => hg i), n, hn, N, θ,
    (p.preimage_mono (PrimeSpectrum.basicOpen_mul_le_left _ _)).trans h₀, fun i => ?_⟩
  have h₁ := isAffineOpen_inf_preimage_basicOpen p (hga i) (f₀ * ∏ i, g i)
  have hle : PrimeSpectrum.basicOpen (f₀ * ∏ i, g i) ≤ PrimeSpectrum.basicOpen (g i) := by
    rw [← Finset.mul_prod_erase _ g (Finset.mem_univ i), mul_left_comm]
    exact PrimeSpectrum.basicOpen_mul_le_left _ _
  rwa [inf_assoc, inf_eq_right.2 (p.preimage_mono hle)] at h₁

theorem relAmple_spread : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp R)) (M : LB A.left), IsProper A.hom → M.IsLB → Out.RelAmple (Over.mk (pullback.snd A.hom (spMap (algebraMap R K)))) (M.pull (pullback.fst A.hom (spMap (algebraMap R K)))) → ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → Out.RelAmple (Over.mk (pullback.snd A.hom (spMap φ))) (M.pull (pullback.fst A.hom (spMap φ))) := by
  intro R K _ _ _ _ _ _ A M _ hM h
  obtain ⟨f, hf, n, hn, N, θ, hc, ha⟩ := exists_cover (IsPullback.of_hasPullback A.hom (spMap (algebraMap R K))) hM
    (isAmpleLB_of_relAmple_of_isAffine _ (LB.isLB_pull hM _) h)
  refine ⟨f, hf, fun R' _ φ hu => ?_⟩
  let ψ := pullback.fst A.hom (spMap φ)
  have : IsProper (Over.mk (pullback.snd A.hom (spMap φ))).hom := inferInstanceAs (IsProper (pullback.snd _ _))
  have : IsAffineHom ψ := MorphismProperty.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_hasPullback A.hom (spMap φ)).flip inferInstance
  have hD : ∀ z, ψ z ∈ A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen f := fun z => by
    have e : A.hom (ψ z) = spMap φ (pullback.snd A.hom (spMap φ) z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    show A.hom (ψ z) ∈ PrimeSpectrum.basicOpen f
    rw [e]
    exact fun hm => (pullback.snd A.hom (spMap φ) z).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)
  have hs : ⨆ i, Out.nonzeroLocus (secPowPull (θ i) ψ) = ⊤ := top_le_iff.1 fun z _ => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hc (hD z))
    exact Opens.mem_iSup.2 ⟨i, (nonzeroLocus_secPowPull (θ i) ψ).ge hi⟩
  have ha' : ∀ i, IsAffineOpen (Out.nonzeroLocus (secPowPull (θ i) ψ)) := fun i => by
    have e : ψ ⁻¹ᵁ (Out.nonzeroLocus (θ i) ⊓ A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen f) =
        Out.nonzeroLocus (secPowPull (θ i) ψ) :=
      (le_antisymm (fun z hz => hz.1) fun z hz => ⟨hz, hD z⟩).trans (nonzeroLocus_secPowPull (θ i) ψ).symm
    exact e ▸ (ha i).preimage ψ
  refine (relAmple_iff_isAmpleLB_of_isAffine _ (LB.isLB_pull hM _)).2 ?_
  refine ⟨LB.isLB_pull hM _, ⟨?_⟩, ?_⟩
  · have e : (Set.univ : Set (pullback A.hom (spMap φ) : Scheme)) = ⋃ i, (Out.nonzeroLocus (secPowPull (θ i) ψ) : Set (pullback A.hom (spMap φ) : Scheme)) := by
      rw [← Opens.coe_iSup, hs, Opens.coe_top]
    rw [e]
    exact isCompact_iUnion fun i => (ha' i).isCompact
  · intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ x))
    exact ⟨n, hn, secPowPull (θ i) ψ, hi, ha' i⟩

end GlobalTheory.AmpleSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsClosedImmersionRestrict
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.FiniteImage

open GlobalTheory.DenseFibreIso

theorem exists_isClosedImmersion_restrict {R : Type} [CommRing R] {U Z : Scheme.{0}}
    (s : Z ⟶ Sp R) (u : U ⟶ Z) [IsFinite u] (K : Type) [Field K] [Algebra R K]
    (hc : IsClosedImmersion (pullback.snd u (pullback.fst s (spMap (algebraMap R K)))))
    (x : Z) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    ∃ V : Z.Opens, x ∈ V ∧ IsClosedImmersion (u ∣_ V) := by
  obtain ⟨A, B, ψ, φ, j, j', _, ⟨y, rfl⟩, H, hj⟩ := exists_chart s u x
  let : Algebra R A := ψ.hom.toAlgebra
  let : Algebra A B := φ.hom.toAlgebra
  replace H : IsPullback (spMap (algebraMap A B)) j' j u := H
  replace hj : j ≫ s = spMap (algebraMap R A) := hj
  have H₁ := isPullback_tensor R A K
  obtain ⟨m, hm, -⟩ := Scheme.exists_preimage_of_isPullback H₁ y (⊥ : PrimeSpectrum K) (by
    rw [← hj, Scheme.Hom.comp_apply]
    exact PrimeSpectrum.ext hx.symm)
  have H₂ := (isPullback_tensor A (A ⊗[R] K) B).paste_vert H
  have H₀ := (IsPullback.of_hasPullback u (pullback.fst s (spMap (algebraMap R K)))).flip
  have hw : (spMap (algebraMap A (A ⊗[R] K)) ≫ j) ≫ s =
      spMap (Algebra.TensorProduct.includeRight.toRingHom : K →+* A ⊗[R] K) ≫
        spMap (algebraMap R K) := by
    rw [Category.assoc, hj]; exact H₁.w
  have e : pullback.lift _ _ hw ≫ pullback.fst s _ = _ := pullback.lift_fst _ _ _
  have H₃ := IsPullback.of_bot' (v₁₂ := pullback.lift _ _ hw) (by rw [e]; exact H₂) H₀
  have hi := MorphismProperty.of_isPullback (P := @IsClosedImmersion) H₃.flip hc
  have hs : Function.Surjective
      (Algebra.TensorProduct.includeLeftRingHom : (A ⊗[R] K) →+* (A ⊗[R] K) ⊗[A] B) := by
    have h2 := (IsClosedImmersion.isAffine_surjective_of_isAffine (spMap
      (Algebra.TensorProduct.includeLeftRingHom : (A ⊗[R] K) →+* (A ⊗[R] K) ⊗[A] B))).2
    have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : (A ⊗[R] K) →+* (A ⊗[R] K) ⊗[A] B))
    have h3 := (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of ((A ⊗[R] K) ⊗[A] B))).hom).2.comp h2
    rw [← ConcreteCategory.coe_comp, e, ConcreteCategory.coe_comp] at h3
    exact h3.of_comp
  have h1 : IsFinite (spMap (algebraMap A B)) :=
    MorphismProperty.of_isPullback (P := @IsFinite) H.flip ‹_›
  have : Module.Finite A B := RingHom.finite_algebraMap.1 ((IsFinite.SpecMap_iff _).1 h1)
  obtain ⟨a, ha, ha'⟩ := exists_away_surjective (A ⊗[R] K) hs m
  have hQ := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom _) ha'
  have H₄ := (isPullback_tensor A (Localization.Away a) B).paste_vert H
  let g := spMap (algebraMap A (Localization.Away a)) ≫ j
  refine ⟨g.opensRange, ?_, ?_⟩
  · have hy : y ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away a))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away a) a, ← hm]
      exact ha
    obtain ⟨z, rfl⟩ := hy
    exact ⟨z, Scheme.Hom.comp_apply _ _ _⟩
  · have H' := H₄.of_iso (Iso.refl _) g.isoOpensRange (Iso.refl _) (Iso.refl _)
      (fst' := _ ≫ g.isoOpensRange.hom) (snd' := _) (f' := g.opensRange.ι) (g' := u)
      (Category.id_comp _).symm ((Category.comp_id _).trans (Category.id_comp _).symm)
      (by simp [g]) (by simp)
    have H'' := isPullback_morphismRestrict u g.opensRange
    rw [← H''.isoIsPullback_hom_fst _ _ H',
      MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion,
      MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion]
    exact hQ

theorem restrict_sSup (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q]
    {U Z : Scheme.{0}} (u : U ⟶ Z) :
    Q (u ∣_ sSup {V : Z.Opens | Q (u ∣_ V)}) := by
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict fun x => ?_
  obtain ⟨V, hV, hx⟩ := TopologicalSpace.Opens.mem_sSup.1 x.2
  refine ⟨(sSup {V : Z.Opens | Q (u ∣_ V)}).ι ⁻¹ᵁ V, hx, ?_⟩
  rw [Q.arrow_mk_iso_iff (morphismRestrictRestrict _ _ _)]
  refine (Q.arrow_mk_iso_iff (morphismRestrictEq u ?_)).2 hV
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.2 (le_sSup hV)

theorem dense_of_flat {O : Type} [CommRing O] [IsDomain O] {T : Scheme.{0}} (t : T ⟶ Sp O)
    [Flat t] (W : Set T) (hW : ∀ x : T, (t x).asIdeal = ⊥ → x ∈ W) : Dense W := by
  intro x
  have hsp : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) ⤳ t x :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (show (⊥ : Ideal O) ≤ _ from bot_le)
  obtain ⟨y, hy, hy'⟩ := Flat.generalizingMap t hsp
  exact hy.mem_closed isClosed_closure (subset_closure (hW y (by rw [hy'])))

theorem main : ∀ (O F : Type) [CommRing O] [IsDedekindDomain O] [Field F] [Algebra O F] [IsFractionRing O F] (U Z : Scheme.{0}) (u : U ⟶ Z) (s : Z ⟶ Sp O), IsFinite u → IsReduced U → Flat (u ≫ s) → LocallyOfFiniteType s → QuasiCompact s → IsClosedImmersion (pullback.snd u (pullback.fst s (spMap (algebraMap O F)))) → ∃ (XX : Scheme.{0}) (u' : U ⟶ XX) (i : XX ⟶ Z) (W : XX.Opens), u' ≫ i = u ∧ IsClosedImmersion i ∧ IsFinite u' ∧ Surjective u' ∧ Dense (W : Set XX) ∧ IsIso (u' ∣_ W) ∧ Dense ((u' ⁻¹ᵁ W : U.Opens) : Set U) ∧ IsReduced XX ∧ Flat (i ≫ s) := by
  intro O F _ _ _ _ _ U Z u s _ _ _ _ _ hc
  let W₀ : Z.Opens := sSup {V : Z.Opens | IsClosedImmersion (u ∣_ V)}
  have hW₀ : IsClosedImmersion (u ∣_ W₀) := restrict_sSup @IsClosedImmersion u
  have hmem : ∀ z : Z, (s z).asIdeal = ⊥ → z ∈ W₀ := fun z hz => by
    obtain ⟨V, hV, hV'⟩ := exists_isClosedImmersion_restrict s u F hc z (by
      rw [hz]; exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective O F))
    exact TopologicalSpace.Opens.mem_sSup.2 ⟨V, hV', hV⟩
  have hfl : Flat (u.imageι ≫ s) := flat_image_of_isDedekindDomain (O := CommRingCat.of O) u s
  have : IsFinite (u.toImage ≫ u.imageι) := by rw [u.toImage_imageι]; infer_instance
  have hfin : IsFinite u.toImage := IsFinite.of_comp _ u.imageι
  refine ⟨u.image, u.toImage, u.imageι, u.imageι ⁻¹ᵁ W₀, u.toImage_imageι, inferInstance, hfin,
    surjective_of_isDominant_of_isClosed_range _ u.toImage.isClosedMap.isClosed_range,
    dense_of_flat (u.imageι ≫ s) _ fun x hx => hmem _ (by rwa [← Scheme.Hom.comp_apply]), ?_,
    dense_of_flat (u ≫ s) _ fun x hx => ?_, inferInstance, hfl⟩
  · have h1 : IsClosedImmersion ((u.toImage ≫ u.imageι) ∣_ W₀) := by
      have : ∀ v : U ⟶ Z, v = u → IsClosedImmersion (v ∣_ W₀) := by rintro _ rfl; exact hW₀
      exact this _ u.toImage_imageι
    rw [morphismRestrict_comp] at h1
    have h2 : IsClosedImmersion (u.toImage ∣_ u.imageι ⁻¹ᵁ W₀) :=
      @IsClosedImmersion.of_comp _ _ _ _ (u.imageι ∣_ W₀) h1 _
    have h3 : IsSchemeTheoreticallyDominant (u.toImage ∣_ u.imageι ⁻¹ᵁ W₀) :=
      IsSchemeTheoreticallyDominant.of_isPullback
        (isPullback_morphismRestrict u.toImage (u.imageι ⁻¹ᵁ W₀)).flip
    exact isIso_of_isClosedImmersion_of_schemeDominant _
  · change u.imageι (u.toImage x) ∈ W₀
    rw [← Scheme.Hom.comp_apply, u.toImage_imageι]
    exact hmem _ (by rwa [← Scheme.Hom.comp_apply])

end GlobalTheory.FiniteImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsConstOfKsRelZero
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem isDer_snd_of_ringHom {R : Type} [CommRing R] (xD : R →+* DualNumber ℂ) :
    IsDer ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp xD) (fun r => (xD r).snd) := by
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · simp only [map_add (f := _), TrivSqZeroExt.snd_add]
  · simp only [map_mul, TrivSqZeroExt.snd_mul, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, TrivSqZeroExt.fstHom_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    ring

theorem spMap_fst_comp_algebraMap :
    spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (algebraMap ℂ (DualNumber ℂ)) = 𝟙 (Sp ℂ) := by
  unfold spMap Sp
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

theorem exists_isConst_of_ksRel_zero :
    Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (xD : R →+* DualNumber ℂ) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (φ : A'.left ⟶ A.left) (j : P₀.A.left ⟶ A'.left) (s : (Fin P₀.g → ℂ) → ∀ W : A.left.Opens, Γ(A.left, W) → ℂ), IsAbelianScheme A → IsAbelianScheme A' → IsGrpPullback A' A (spMap xD) φ → IsGrpPullback P₀.A A' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j → KSRel u A.hom (j ≫ φ) (fun r => (xD r).snd) 0 s → ∃ ρ, IsConst A' P₀.A ρ j := by
  intro hL P₀ u Hm χ hU R _ xD A _ A' _ φ j s hA hA' hφ hj hKS

  have hcomp : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap xD =
      spMap ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp xD) := by
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hsq : IsPullback (j ≫ φ) P₀.A.hom A.hom
      (spMap ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp xD)) := by
    rw [← hcomp]
    exact hj.1.paste_horiz hφ.1

  obtain ⟨d, hd⟩ := _root_.GlobalTheory.exists_locDer_top_of_ksRel_zero hL P₀ u Hm χ hU R _ A.left A.hom (j ≫ φ) hA.smooth hsq
    (fun r => (xD r).snd) s (isDer_snd_of_ringHom xD) hKS

  obtain ⟨Y', ρ, π, hpb⟩ : ∃ (Y' : Scheme.{0}) (ρ : Y' ⟶ P₀.A.left) (π : Y' ⟶ Sp (DualNumber ℂ)),
      IsPullback ρ π P₀.A.hom (spMap (algebraMap ℂ (DualNumber ℂ))) :=
    ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  have hw : 𝟙 P₀.A.left ≫ P₀.A.hom =
      (P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ spMap (algebraMap ℂ (DualNumber ℂ)) := by
    rw [Category.assoc, spMap_fst_comp_algebraMap, Category.comp_id, Category.id_comp]
  obtain ⟨i, hiρ, hiπ⟩ := hpb.exists_lift (𝟙 _) (P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) hw

  have hm : (j ≫ φ) ≫ A.hom =
      P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap xD := by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, hj.1.w, Category.assoc]
  obtain ⟨Φ, hiΦ, hΦ⟩ :=
    _root_.GlobalTheory.KS.DerMor.exists_mor P₀.A.left Y' P₀.A.hom π ρ i hpb hiρ hiπ R xD A.left A.hom (j ≫ φ) d hm hd

  obtain ⟨e, heφ, heπ⟩ := hφ.1.exists_lift Φ π hΦ
  have hie : i ≫ e = j := by
    refine hφ.1.hom_ext ?_ ?_
    · rw [Category.assoc, heφ, hiΦ]
    · rw [Category.assoc, heπ, hiπ, hj.1.w]

  have hpb' := (_root_.GlobalTheory.EpsThick.thickening_functions P₀.A.left Y' P₀.A.hom π ρ i hpb hiρ hiπ).2.1
  have := P₀.isAb.smooth
  have hfl : Flat π := MorphismProperty.of_isPullback (P := @Flat) hpb inferInstance
  have he : IsIso e := _root_.GlobalTheory.ThickeningIso.isIso_of_mod_eps P₀.A.left Y' A'.left P₀.A.hom π A'.hom i j e hpb' hj.1 hfl heπ hie

  have hsq2 : IsPullback (inv e) A'.hom π (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, IsIso.inv_comp_eq, heπ]⟩
  have hρ₀ : IsPullback (inv e ≫ ρ) A'.hom P₀.A.hom (spMap (algebraMap ℂ (DualNumber ℂ))) := by
    have h := hsq2.paste_horiz hpb
    rwa [Category.id_comp] at h
  have hjρ : j ≫ inv e ≫ ρ = 𝟙 _ := by
    rw [← hie, Category.assoc, IsIso.hom_inv_id_assoc, hiρ]
  exact exists_isConst_of_isPullback hL P₀.A A' (inv e ≫ ρ) j P₀.isAb hA' hj hρ₀ hjρ

end GlobalTheory.KS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsKsMatrix
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem GlobalTheory.KSField.exists_ksMatrix : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (P : Out.PolAV (Sp (TrivSqZeroExt K (Fin r → K)))) (P₀ : Out.PolAV (Sp K)) (φ₀ : P₀.A.left ⟶ P.A.left) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)), IsGrpPullback P₀.A P.A (spMap (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom) φ₀ → LBIso P₀.L (P.L.pull φ₀) → IsLieBasis v → ∃ Θ : ((Fin r → K) →ₗ[K] K) →ₗ[K] Matrix (Fin g) (Fin g) K, (∀ lam, (Θ lam).IsSymm) ∧ (∀ (f f' : P.A ⟶ P.A) (f₀ f₀' : P₀.A ⟶ P₀.A) (F F' : Matrix (Fin g) (Fin g) K), IsMonHom f → IsMonHom f' → f₀.left ≫ φ₀ = φ₀ ≫ f.left → f₀'.left ≫ φ₀ = φ₀ ≫ f'.left → LBIso (cubeLB P.A ![fst P.A P.A ≫ f, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ f'] P.L) → (∀ j, IsLieComb (fun i => F i j) v (v j ≫ f₀)) → (∀ j, IsLieComb (fun i => F' i j) v (v j ≫ f₀')) → ∀ lam, F * Θ lam = Θ lam * F'.transpose) ∧ ∀ lam, Θ lam = 0 → ∀ (G : Over (Sp (DualNumber K))) [GrpObj G] (ψ : G.left ⟶ P.A.left), IsGrpPullback G P.A (spMap (dirMap lam)) ψ → ∃ ψ₀ : G.left ⟶ P₀.A.left, IsGrpPullback G P₀.A (spMap (algebraMap K (DualNumber K))) ψ₀ ∧ ∀ io : P₀.A.left ⟶ G.left, io ≫ ψ = φ₀ → io ≫ G.hom = P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom → io ≫ ψ₀ = 𝟙 _ :=
  GlobalTheory.KSField.exists_ksMatrix_of GlobalTheory.FinAffineCharts.exists_finite_affine_charts GlobalTheory.KS.InvField.main GlobalTheory.KS.DlogPol.dlog_independent GlobalTheory.KS.Cocycle.exists_ksCoc GlobalTheory.KS.LinDir.ksCoc_linear GlobalTheory.KS.Sym.exists_symm_of_ksCoc GlobalTheory.KS.matrix_intertwines_adjoint GlobalTheory.KS.exists_global_locDer_of_isCob GlobalTheory.KS.exists_isConstK_of_locDerK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverCompFinite
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem isProjOver_comp_of_finite :
    ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (f : Y ⟶ X) (s : X ⟶ Sp R), IsFinite f → IsProjOver s → IsProjOver (f ≫ s) := by
  intro R _ X Y f s hf hs
  exact GlobalTheory.isProjOver_comp_of_isFinite f hs

end GlobalTheory
end

