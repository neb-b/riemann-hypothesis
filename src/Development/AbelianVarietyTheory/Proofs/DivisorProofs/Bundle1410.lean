module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0565
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0540
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntegralFramedPointBaseChangeCdvrTransitiv
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFunctionFactorizableSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1370
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeEndomorphismFiniteOfGeometricFibresStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_endomorphism_finite_of_geometric_fibres : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (φ : A ⟶ A),
    (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), IsFinite ((Over.pullback t).map φ).left) →
    IsFinite φ.left := by
  first | (exact @GlobalTheory.AbEnd.isFinite_of_isFinite_geomFibres) | (exact GlobalTheory.AbEnd.isFinite_of_isFinite_geomFibres) | (intros; apply GlobalTheory.AbEnd.isFinite_of_isFinite_geomFibres <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsProjectiveRank
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem smooth_of_openImm {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {X : Scheme.{0}} (s : X ⟶ Sp R)
    (g : ℕ) (hs : SmoothOfRelativeDimension g s) (x : Sp B ⟶ X) (hx : x ≫ s = spMap (algebraMap R B))
    [IsOpenImmersion x] :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g) (algebraMap R B) ∧ Algebra.Smooth R B := by
  have h : SmoothOfRelativeDimension g (x ≫ s) := by
    have := smoothOfRelativeDimension_comp 0 g x s
    simpa using this
  rw [hx] at h
  constructor
  · exact (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension g)).1 h
  · have h2 : Smooth (spMap (algebraMap R B)) := SmoothOfRelativeDimension.smooth g _
    exact RingHom.smooth_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Smooth)).1 h2)

theorem rankAtStalk_kaehler_of_locally {R B : Type} [CommRing R] [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    (g : ℕ) (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g) (algebraMap R B))
    (p : PrimeSpectrum B) : Module.rankAtStalk Ω[B⁄R] p = g := by
  obtain ⟨s, hs, H⟩ := h
  obtain ⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ p.asIdeal := by
    by_contra! hc
    exact p.2.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 hc))
  let Bt := Localization.Away t
  have hstd : Algebra.IsStandardSmoothOfRelativeDimension g R Bt :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap g).1
      (by rw [IsScalarTower.algebraMap_eq R B Bt]; exact H t ht)
  have : Algebra.FormallyEtale B Bt := .of_isLocalization (Submonoid.powers t)
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B Bt
  obtain ⟨q, hq⟩ : ∃ q : PrimeSpectrum Bt, PrimeSpectrum.comap (algebraMap B Bt) q = p := by
    have : p ∈ Set.range (PrimeSpectrum.comap (algebraMap B Bt)) := by
      rw [PrimeSpectrum.localization_away_comap_range Bt t]
      exact htp
    exact this
  have : Nontrivial Bt := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨q⟩
  have : Algebra.IsStandardSmooth R Bt := hstd.isStandardSmooth
  have : Module.Free Bt Ω[Bt⁄R] := Algebra.IsStandardSmooth.free_kaehlerDifferential
  have h1 := Module.rankAtStalk_baseChange (R := B) (S := Bt) (M := Ω[B⁄R]) q
  rw [hq] at h1
  rw [← h1, Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_eq_finrank_of_free]
  have hf : Module.finrank Bt Ω[Bt⁄R] = g := by
    rw [Module.finrank, Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := R) (S := Bt) g]
    simp
  simp [hf]

theorem globForm_FP : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → FP R (GlobForm A.hom) g := by
  intro R _ A _ g hA hg
  obtain ⟨hF, h0, -⟩ := _root_.GlobalTheory.AbCoh.basic_of_isAbelianScheme R A g hA hg
  obtain ⟨hfin, hproj⟩ := _root_.GlobalTheory.AbCoh.compatibleGlobalOneForms_finite_projective R _ (OAff A.hom) hF h0
  refine ⟨hfin, hproj, fun p ↦ ?_⟩

  have hη : (η[A]).left ≫ A.hom = 𝟙 _ := by simpa using Over.w η[A]
  let x : A.left := (η[A]).left.base p
  have hxp : A.hom.base x = p := by
    change ((η[A]).left ≫ A.hom).base p = p
    rw [hη]; rfl
  obtain ⟨U, hU⟩ : ∃ U : A.left.affineOpens, x ∈ U.1 := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := A.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x)
      isOpen_univ
    exact ⟨⟨V, hV⟩, hxV⟩
  let T : AffOp A.left := Opposite.op U
  let B := (OAff A.hom).obj T
  have hUa : IsAffineOpen U.1 := U.2
  obtain ⟨q, hq⟩ : ∃ q : Sp (Sec A.hom U.1), (affPt A.hom U).base q = x := by
    have : x ∈ Set.range hUa.fromSpec.base := by
      rw [hUa.range_fromSpec]; exact hU
    obtain ⟨q, hq⟩ := this
    exact ⟨q, hq⟩
  have hqp : PrimeSpectrum.comap (algebraMap R (Sec A.hom U.1)) q = p := by
    have := congrArg (fun f ↦ f.base q) (affPt_w A.hom U)
    change A.hom.base ((affPt A.hom U).base q) = _ at this
    rw [hq, hxp] at this
    exact this.symm
  haveI : IsOpenImmersion (affPt A.hom U) := IsAffineOpen.isOpenImmersion_fromSpec hUa
  obtain ⟨hloc, hsm⟩ := smooth_of_openImm A.hom g hg (affPt A.hom U) (affPt_w A.hom U)
  have hrk := rankAtStalk_kaehler_of_locally g hloc q
  let e : Glob1 (OAff A.hom) →ₗ[R] Ω[B⁄R] := (LinearMap.proj T).comp (Glob1 (OAff A.hom)).subtype
  have he : IsBaseChange B e := GlobalTheory.T.isBaseChange_compatibleGlobalOneForms R _ (OAff A.hom) hF h0 T e (fun _ ↦ rfl)
  have h1 := Module.rankAtStalk_baseChange (R := R) (M := Glob1 (OAff A.hom)) (S := B) q
  rw [Module.rankAtStalk_eq_of_equiv he.equiv] at h1
  rw [← hqp]
  exact h1.symm.trans hrk

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsoLineBundleSectionsTransfer
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.BasisMatch
open GlobalTheory.AbLaw GlobalTheory.Cartier TensorProduct

theorem topEquiv_pull {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] {f : X ⟶ Sp R}
    {f' : X' ⟶ Sp R'} {π : X' ⟶ X} {g : R →+* R'} (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g))
    (M : LB X) (x : SecOnR f M ⊤) :
    SecOnR.topEquiv f' (M.pull π) (SecOnR.pull M w ⊤ ⊤ le_top x) = secPull (SecOnR.topEquiv f M x) π := by
  refine DVR.SecOps.sec_ext fun i => ?_
  refine (congrArg (rs X' _) (SecOn.coord_pullLE π le_top x i)).trans ?_
  change (π.appLE _ _ _ ≫ X'.presheaf.map _).hom _ = (X.presheaf.map _ ≫ π.appLE _ _ _).hom _
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  rfl

theorem secMaps_congr {Y : Scheme.{0}} {L N : LB Y} (hL : L.IsLB) (hN : N.IsLB) (w : LB.Iso L N)
    (hw : w.IsGen) (a : L.Sec) :
    SecMaps w a (SecOn.topEquiv N (SecOn.congr hL hN w hw ⊤ ((SecOn.topEquiv L).symm a))) := by
  intro p
  have e := SecOn.coord_congr hL hN w hw ((SecOn.topEquiv L).symm a) p.1 p.2 (O := N.U p.1 ⊓ L.U p.2)
    (le_inf le_top inf_le_left) (le_inf le_top inf_le_right) le_rfl
  rw [SecOn.topEquiv_symm_apply, GlobalTheory.LB.coord_ofSec, rs_self, rs_rs] at e
  rw [SecOn.topEquiv_f]
  exact (rs_rs _ _ _).trans e

theorem topEquiv_sum {X : Scheme.{0}} {R : Type} [CommRing R] (f : X ⟶ Sp R) (M : LB X) {n : ℕ}
    (c : Fin n → R) (x : Fin n → SecOnR f M ⊤) :
    SecOnR.topEquiv f M (∑ j, c j • x j) = ∑ j, cst f ⊤ (c j) • SecOnR.topEquiv f M (x j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, SecOnR.smul_def, map_smul]

theorem sum_f {X : Scheme.{0}} {H : LB X} {m : ℕ} (s : Fin m → H.Sec) (k : H.ι) :
    (∑ j, s j).f k = ∑ j, (s j).f k :=
  map_sum ({ toFun := fun s : H.Sec => s.f k, map_zero' := rfl, map_add' := fun _ _ => rfl } :
    H.Sec →+ Γ(X, H.U k)) s Finset.univ

theorem veryAmpleBy_of_span {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) [UniversallyClosed f]
    (H : LB X) {m n : ℕ} (s₁ : Fin (m + 1) → H.Sec) (s : Fin (n + 1) → H.Sec) (hs₁ : VeryAmpleBy f H s₁)
    (hsp : ∀ i, ∃ c : Fin (n + 1) → R, s₁ i = ∑ k, cst f ⊤ (c k) • s k) : VeryAmpleBy f H s := by
  have E : ∀ {p : ℕ} (u : Fin (p + 1) → H.Sec), VeryAmpleBy f H u ↔ AmpleSpan.EmbedsBy f u :=
    fun u => (AmpleSpan.embedsBy_spec_iff f u).symm
  refine (E s).2 (((E s₁).1 hs₁).of_inSpan fun i => ?_)
  obtain ⟨c, hc⟩ := hsp i
  refine ⟨fun k => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c k), fun k' => ?_⟩
  rw [hc, sum_f]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [GlobalTheory.LB.smul_f]
  congr 1
  change rs X le_top (cst f ⊤ (c k)) = _
  rw [rs_cst]
  simp only [AbLaw.cst, RingHom.comp_apply, Scheme.Hom.appLE, CommRingCat.hom_comp, Scheme.Hom.appTop]
  rfl

end GlobalTheory.BasisMatch

namespace GlobalTheory.BasisMatch
open GlobalTheory.AbLaw GlobalTheory.Cartier TensorProduct

def basisOfExistsUnique {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ} (v : Fin n → V)
    (h : ∀ x, ∃! c : Fin n → R, x = ∑ j, c j • v j) : Module.Basis (Fin n) R V :=
  Module.Basis.mk (v := v)
    (Fintype.linearIndependent_iff.2 fun g hg i => by
      obtain ⟨c, -, hc⟩ := h 0
      exact congrFun ((hc g hg.symm).trans (hc 0 (by simp)).symm) i)
    (fun x _ => (Submodule.mem_span_range_iff_exists_fun R).2 (by
      obtain ⟨c, hc, -⟩ := h x
      exact ⟨c, hc.symm⟩))

theorem basisOfExistsUnique_apply {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}
    (v : Fin n → V) (h : ∀ x, ∃! c : Fin n → R, x = ∑ j, c j • v j) (j : Fin n) :
    basisOfExistsUnique v h j = v j := Module.Basis.mk_apply _ _ _

theorem core {K W K' : Type} [Field K] [CommRing W] [Field K'] [Algebra W K'] [Algebra K K']
    [Module.Flat W K'] {XA XG Y : Scheme.{0}} (fA : XA ⟶ Sp K) (fG : XG ⟶ Sp W) (fY : Y ⟶ Sp K')
    (πA : Y ⟶ XA) (πG : Y ⟶ XG) [CompactSpace XA] [CompactSpace XG] [IsSeparated fA] [IsSeparated fG]
    [UniversallyClosed fA]
    (PA : IsPullback πA fY fA (spMap (algebraMap K K'))) (PG : IsPullback πG fY fG (spMap (algebraMap W K')))
    (H : LB XA) (M : LB XG) (w : LB.Iso (M.pull πG) (H.pull πA)) {m : ℕ} (s₁ : Fin (m + 1) → H.Sec)
    {N : ℕ} (t : Fin (N + 1) → M.Sec) (hH : H.IsLB) (hs₁ : VeryAmpleBy fA H s₁) (hM : M.IsLB)
    (hw : w.IsGen) (ht : ∀ u : M.Sec, ∃! c : Fin (N + 1) → W, u = ∑ j, cst fG ⊤ (c j) • t j) :
    ∃ (s : Fin (N + 1) → H.Sec) (g : Matrix (Fin (N + 1)) (Fin (N + 1)) K'),
      VeryAmpleBy fA H s ∧ IsUnit g.det ∧
      (∀ j, SecMaps w (secPull (t j) πG) (∑ k, cst fY ⊤ (g j k) • secPull (s k) πA)) ∧
      ∀ c c' : Fin (N + 1) → K', ∑ k, cst fY ⊤ (c k) • secPull (s k) πA =
        ∑ k, cst fY ⊤ (c' k) • secPull (s k) πA → c = c' := by
  have hLy : (M.pull πG).IsLB := LB.isLB_pull hM _
  have hHy : (H.pull πA).IsLB := LB.isLB_pull hH _
  let bcA := LinearEquiv.ofBijective _ (GlobalTheory.PlaceInt.Ext.baseChangeHom_top_bijective hH PA)
  let bcG := LinearEquiv.ofBijective _ (GlobalTheory.PlaceInt.Ext.baseChangeHom_top_bijective hM PG)
  let ψ := SecOnR.linEquiv fY (R := K') (SecOn.congr hLy hHy w hw ⊤)
  have htt : ∀ x : SecOnR fG M ⊤, ∃! c : Fin (N + 1) → W,
      x = ∑ j, c j • (SecOnR.topEquiv fG M).symm (t j) := by
    intro x
    refine (existsUnique_congr fun c => ?_).1 (ht (SecOnR.topEquiv fG M x))
    refine Iff.trans ?_ (SecOnR.topEquiv fG M).injective.eq_iff
    rw [topEquiv_sum]
    simp only [LinearEquiv.apply_symm_apply]
  let bt := basisOfExistsUnique _ htt
  let tY := ((bt.baseChange K').map bcG).map ψ
  have hfr : Module.finrank K (SecOnR fA H ⊤) = N + 1 := by
    rw [← Module.finrank_baseChange (R := K') (S := K), Module.finrank_eq_card_basis (tY.map bcA.symm),
      Fintype.card_fin]
  haveI : Module.Finite K (SecOnR fA H ⊤) := Module.finite_of_finrank_eq_succ hfr
  let bs := Module.finBasisOfFinrankEq K _ hfr
  let s : Fin (N + 1) → H.Sec := fun k => SecOnR.topEquiv fA H (bs k)
  let bV := (bs.baseChange K').map bcA
  have hbV : ∀ k, SecOnR.topEquiv fY (H.pull πA) (bV k) = secPull (s k) πA := fun k => by
    simp only [bV, bcA, Module.Basis.map_apply, Module.Basis.baseChange_apply, LinearEquiv.ofBijective_apply]
    exact (congrArg (SecOnR.topEquiv fY (H.pull πA)) (one_smul K' (SecOnR.pull H PA.w ⊤ ⊤ le_top (bs k)))).trans
      (topEquiv_pull PA.w H _)
  have htY : ∀ j, SecOnR.topEquiv fY (H.pull πA) (tY j) =
      SecOn.topEquiv (H.pull πA) (SecOn.congr hLy hHy w hw ⊤ ((SecOn.topEquiv (M.pull πG)).symm
        (secPull (t j) πG))) := fun j => by
    have e1 : SecOnR.topEquiv fY (M.pull πG) (bcG (1 ⊗ₜ bt j)) = secPull (t j) πG := by
      simp only [bcG, LinearEquiv.ofBijective_apply]
      refine (congrArg (SecOnR.topEquiv fY (M.pull πG))
        (one_smul K' (SecOnR.pull M PG.w ⊤ ⊤ le_top (bt j)))).trans ?_
      rw [topEquiv_pull]
      show secPull (SecOnR.topEquiv fG M (basisOfExistsUnique _ htt j)) πG = _
      rw [basisOfExistsUnique_apply, LinearEquiv.apply_symm_apply]
    rw [← e1]
    simp only [tY, Module.Basis.map_apply, Module.Basis.baseChange_apply]
    show SecOn.topEquiv _ (SecOn.congr hLy hHy w hw ⊤ (bcG (1 ⊗ₜ bt j))) =
      SecOn.topEquiv _ (SecOn.congr hLy hHy w hw ⊤ ((SecOn.topEquiv _).symm (SecOn.topEquiv _ (bcG (1 ⊗ₜ bt j)))))
    exact congrArg (fun z => SecOn.topEquiv (H.pull πA) (SecOn.congr hLy hHy w hw ⊤ z))
      ((SecOn.topEquiv (M.pull πG)).symm_apply_apply _).symm
  let g : Matrix (Fin (N + 1)) (Fin (N + 1)) K' := fun j k => bV.repr (tY j) k
  have hsum : ∀ c : Fin (N + 1) → K', ∑ k, cst fY ⊤ (c k) • secPull (s k) πA =
      SecOnR.topEquiv fY (H.pull πA) (∑ k, c k • bV k) := fun c => by
    rw [topEquiv_sum]
    simp only [hbV]
  refine ⟨s, g, ?_, ?_, fun j => ?_, fun c c' h => ?_⟩
  · refine veryAmpleBy_of_span fA H s₁ s hs₁ fun i => ⟨bs.repr ((SecOnR.topEquiv fA H).symm (s₁ i)), ?_⟩
    conv_lhs => rw [← (SecOnR.topEquiv fA H).apply_symm_apply (s₁ i),
      ← bs.sum_repr ((SecOnR.topEquiv fA H).symm (s₁ i))]
    rw [topEquiv_sum]
  · have : g = Matrix.transpose (bV.toMatrix tY) := by
      ext j k
      rfl
    rw [this, Matrix.det_transpose]
    letI := bV.invertibleToMatrix tY
    exact Matrix.isUnit_det_of_invertible _
  · rw [hsum, bV.sum_repr (tY j), htY]
    exact secMaps_congr hLy hHy w hw _
  · rw [hsum, hsum] at h
    have h3 : bV.equivFun.symm c = bV.equivFun.symm c' := by
      simpa only [Module.Basis.equivFun_symm_apply] using (SecOnR.topEquiv fY (H.pull πA)).injective h
    exact bV.equivFun.symm.injective h3

end GlobalTheory.BasisMatch


open GlobalTheory.AbLaw GlobalTheory.Cartier in
theorem GlobalTheory.BasisMatch.exists_basis_match : ∀ (K W K' : Type) [Field K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra K K'], ∀ (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, ∀ (H : LB A.left) (m : ℕ) (s₁ : Fin (m + 1) → H.Sec) (M : LB G.left) (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) (H.pull (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))))) (N : ℕ) (t : Fin (N + 1) → M.Sec), H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy A.hom H s₁ → M.IsLB → w.IsGen → (∀ u : M.Sec, ∃! c : Fin (N + 1) → W, u = ∑ j, GlobalTheory.AbLaw.cst G.hom ⊤ (c j) • t j) → ∃ (s : Fin (N + 1) → H.Sec) (g : Matrix (Fin (N + 1)) (Fin (N + 1)) K'), GlobalTheory.AbLaw.VeryAmpleBy A.hom H s ∧ IsUnit g.det ∧ (∀ j, GlobalTheory.Cartier.SecMaps w (GlobalTheory.Cartier.secPull (t j) (pullback.fst G.hom (spMap (algebraMap W K')))) (∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (g j k) • GlobalTheory.Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))))) ∧ ∀ c c' : Fin (N + 1) → K', ∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (c k) • GlobalTheory.Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) = ∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (c' k) • GlobalTheory.Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) → c = c' := by
  intro K W K' _ _ _ _ _ _ _ _ A _ hA G _ hG e H m s₁ M w N t hH hs₁ hM hw ht
  haveI := hA.proper
  haveI := hG.proper
  haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  haveI : Module.Flat W K' := IsLocalization.flat K' (nonZeroDivisors W)
  have PG : IsPullback (pullback.fst G.hom (spMap (algebraMap W K'))) (pullback.snd G.hom (spMap (algebraMap W K')))
      G.hom (spMap (algebraMap W K')) := IsPullback.of_hasPullback _ _
  have PA : IsPullback (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))
      (pullback.snd G.hom (spMap (algebraMap W K'))) A.hom (spMap (algebraMap K K')) := by
    refine (IsPullback.of_hasPullback A.hom (spMap (algebraMap K K'))).of_iso
      ((Over.forget _).mapIso e).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp only [Functor.mapIso_symm, Iso.symm_hom, Functor.mapIso_inv, Over.forget_map, Iso.refl_hom,
        Category.comp_id]
      rw [← Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left]
      exact (Category.id_comp _).symm
    · have := Over.w e.inv
      simp only [Functor.mapIso_symm, Iso.symm_hom, Functor.mapIso_inv, Over.forget_map, Iso.refl_hom,
        Category.comp_id]
      exact this.symm
    · simp
    · simp
  exact GlobalTheory.BasisMatch.core A.hom G.hom _ _ _ PA PG H M w s₁ t hH hs₁ hM hw ht
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTorsionPointTrivialOfGeometricStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_torsionPoint_trivial_of_geometric : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (T : Over S) (x : T ⟶ A) (c : ℕ), IsUnit (c : Γ(T.left, ⊤)) → x ^ c = 1 → (∀ (k : Type) [Field k] [IsAlgClosed k], (c : k) ≠ 0 → ∀ (z : Sp k ⟶ S) (g : Over.mk z ⟶ T), g ≫ x = 1) → x = 1 := by
  first | (exact @GlobalTheory.TorsionRigid.eq_one_of_geometric) | (exact GlobalTheory.TorsionRigid.eq_one_of_geometric) | (intros; apply GlobalTheory.TorsionRigid.eq_one_of_geometric  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietySepClosedPointDivisible
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SepClosedDiv

theorem exists_section_of_etale {Ω : Type} [Field Ω] [IsSepClosed Ω] {X : Scheme.{0}} (f : X ⟶ Sp Ω)
    [Etale f] (x : X) : ∃ s : Sp Ω ⟶ X, s ≫ f = 𝟙 _ := by
  let i := X.affineCover.idx x
  obtain ⟨y, -⟩ := X.affineCover.covers x
  obtain ⟨R, e⟩ : ∃ R : CommRingCat, X.affineCover.X i = Spec R := ⟨_, rfl⟩
  let φ : CommRingCat.of Ω ⟶ R := Spec.preimage (eqToHom e.symm ≫ X.affineCover.f i ≫ f)
  have hφ : Spec.map φ = eqToHom e.symm ≫ X.affineCover.f i ≫ f := Spec.map_preimage _
  have hg : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  have hr : φ.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).1 hg
  letI := φ.hom.toAlgebra
  have : Algebra.Etale Ω R := hr
  let q : PrimeSpectrum R := (eqToHom e).base y
  obtain ⟨ψ⟩ := GlobalTheory.nonempty_algHom_of_etale_of_isSepClosed (R := Ω) (A := R) (K := Ω) q.asIdeal
    (by
      rw [(Ideal.comap (algebraMap Ω R) q.asIdeal).eq_bot_of_prime]
      exact ((RingHom.injective_iff_ker_eq_bot _).1 (algebraMap Ω Ω).injective).symm)
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ eqToHom e.symm ≫ X.affineCover.f i, ?_⟩
  simp only [Category.assoc]
  rw [← hφ, ← Spec.map_comp]
  rw [← Spec.map_id]
  congr 1
  ext a
  exact ψ.commutes a

theorem exists_pow_eq : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] (A : Over (Sp K)) [GrpObj A]
    [IsCommMonObj A], IsAbelianScheme A → ∀ n : ℕ, (n : K) ≠ 0 → ∀ x : ptOver K Ω ⟶ A, ∃ y, y ^ n = x := by
  intro K Ω _ _ _ _ A _ _ hA n hn x
  have := hA.smooth
  have hu : IsUnit (n : Γ(Sp K, ⊤)) := by
    simpa using (isUnit_iff_ne_zero.2 hn).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have he : Etale (mulN A n).left := GlobalTheory.GrpTangent.etale_mulN A hu
  have hs : Surjective (mulN A n).left := GlobalTheory.surjective_mulN_of_isAbelianScheme K A hA n hn
  let m := (mulN A n).left
  have he' : Etale (pullback.snd m x.left) := inferInstance
  obtain ⟨z, -⟩ := (pullback.snd m x.left).surjective (IsLocalRing.closedPoint Ω)
  obtain ⟨s, hs'⟩ := exists_section_of_etale (pullback.snd m x.left) z
  have h : (s ≫ pullback.fst m x.left) ≫ m = x.left := by
    rw [Category.assoc, pullback.condition, reassoc_of% hs']
  refine ⟨Over.homMk (s ≫ pullback.fst m x.left) ?_, ?_⟩
  · change (s ≫ pullback.fst m x.left) ≫ A.hom = _
    rw [← Over.w (mulN A n), ← Category.assoc, h]
    exact Over.w x
  · rw [← GlobalTheory.GrpTangent.comp_mulN]
    exact Over.OverMorphism.ext h

end GlobalTheory.SepClosedDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFixedBySmallHeisenbergLattice
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.FinSuppHeis

theorem norm_le_of_finDiv {F : Type} [Field F] [NumberField F] {N : ℕ} {a : AF F} (h : GlobalTheory.FinSupp.FinDiv F N a)
    (v : HeightOneSpectrum (𝓞 F)) : ‖evFin F v a‖ ≤ ‖(N : Fv F v)‖ := by
  obtain ⟨b, hb, e⟩ := h v
  rw [e, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) ((GlobalTheory.SuppDen.norm_le_one_iff_mem v b).mpr hb)

theorem heis_fix_finDiv : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ Φ ∈ schA F κ, ∃ N : ℕ, 1 ≤ N ∧ ∀ w : (κ → AF F) × (κ → AF F),
      (∀ i, (w.1 i).1 = 0 ∧ GlobalTheory.FinSupp.FinDiv F N (w.1 i) ∧ (w.2 i).1 = 0 ∧ GlobalTheory.FinSupp.FinDiv F N (w.2 i)) →
      schr ψ w Φ = Φ := by
  intro F _ _ κ _ ψ hψ Φ hΦ
  obtain ⟨m₀, hm₀, h⟩ := GlobalTheory.ThetaLevel.heis_fix (F := F) (κ := κ) ψ hψ Φ hΦ
  refine ⟨m₀, hm₀, fun w hw => ?_⟩
  exact h w.1 w.2 ⟨fun i => (hw i).1, fun v i => norm_le_of_finDiv (hw i).2.1 v⟩
    ⟨fun i => (hw i).2.2.1, fun v i => norm_le_of_finDiv (hw i).2.2.2 v⟩

end GlobalTheory.FinSuppHeis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFunctionFactorizableSumStatement
section
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblEval
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_schwartz_function_factorizable_sum : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (a : (κ → Af F) → ℂ), a ∈ SB (κ → Af F) → ∃ (m : ℕ) (φ : Fin m → ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ j v, φ j v ∈ SB (κ → Fv F v)) ∧ (∀ j, ∀ᶠ v in cofinite, φ j v = stdInd F κ v) ∧ ∀ x, a x = ∑ j, ∏ᶠ v, φ j v fun i => evalV F v (x i) := by
  first | exact @GlobalTheory.SBRestrProd.sb_eq_sum_restrProd | exact GlobalTheory.SBRestrProd.sb_eq_sum_restrProd | (intros; apply GlobalTheory.SBRestrProd.sb_eq_sum_restrProd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSlabOpenUnitCubeHaarPosFiniteStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanSlab_open_unitCube_haar_pos_finite : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], (∀ m : ℕ, 0 < m → IsOpen (slab F κ m)) ∧ ∀ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → 0 < μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1) ∧ ∀ A : Set (Fin (dimA F κ) → ℝ), IsCompact A → μ (archOut F κ ⁻¹' A ∩ slab F κ 1) ≠ ⊤ := by
  first | exact @GlobalTheory.ArchDecay.slab_open_cube_pos_finite | exact GlobalTheory.ArchDecay.slab_open_cube_pos_finite | (intros; apply GlobalTheory.ArchDecay.slab_open_cube_pos_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTraceSymplecticFormOrthonormalFramesStatement
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanTrace_symplecticForm_orthonormalFrames : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {P Q R S : ℕ} (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → Framed τ JA JB a b A C →
    ∀ (u u' : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (c c' : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ), At (evI F) u → At (evI F) u' →
    (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → (∀ w, u'.map (piInf (τ w)) = A w * c' w * (C w)ᵀ) →
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) JA JB u u')) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := by
  first | exact @GlobalTheory.SympFrames.symp_frames | exact GlobalTheory.SympFrames.symp_frames | (intros; apply GlobalTheory.SympFrames.symp_frames <;> assumption)
end

