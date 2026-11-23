module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0080
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionRegularLocalRing
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0092
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0007
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterAlgRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductConjugate
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptAwayFromPrimes
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSymplecticCoordinatesOfIsPeriod
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0073
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0068
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0110
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteTorusTranslatesCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.ChartCover

private lemma eval_eq_zero_of_mem_mcPts' {K : Type} {J : K → Type}
    (P : Ideal (MRing J)) (z : (Σ k, J k) → ℂ) (hz : z ∈ mcPts P) :
    ∀ g ∈ pC P, MvPolynomial.eval z g = 0 := by
  intro g hg
  simp only [mcPts, Set.mem_ofPred_eq] at hz
  have hle : pC P ≤ RingHom.ker (MvPolynomial.eval z) := by
    unfold pC
    rw [Ideal.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact RingHom.mem_ker.mpr (hz.2 f hf)
  exact RingHom.mem_ker.mp (hle hg)

private lemma torusSmul_mem_mcPts' {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
    (P : Ideal (MRing J)) (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC P))
    (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, J k) → ℂ) (hz : z ∈ mcPts P) :
    torusSmul c z ∈ mcPts P := by
  have hv := eval_eq_zero_of_mem_mcPts' P z hz
  simp only [mcPts, Set.mem_ofPred_eq] at hz ⊢
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, mul_ne_zero (hc k) hi⟩
  · have hmem : MvPolynomial.map (Int.castRingHom ℂ) f ∈ pC P := by
      unfold pC
      exact Ideal.subset_span ⟨f, hf, rfl⟩
    exact ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul hP c z hv _ hmem

theorem mcPts_finite_cover_up_to_torus :
    ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J))
    (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC P)) (C : Type) (O : C → Set ((Σ k, J k) → ℂ)),
    (∀ i, IsOpen (O i)) → (∀ z ∈ mcPts P, ∃ i, z ∈ O i) →
    ∃ (m : ℕ) (e : Fin m → C), ∀ z ∈ mcPts P, ∃ (a : Fin m) (c : K → ℂ), (∀ k, c k ≠ 0) ∧
      torusSmul c z ∈ O (e a) ∧ torusSmul c z ∈ mcPts P := by
  intro K _ J _ P hP C O hO hcov
  classical
  set S : Set ((Σ k, J k) → ℂ) :=
    {w | (∀ k, ∑ i, ‖w ⟨k, i⟩‖ ^ 2 = 1) ∧
      ∀ f ∈ P, MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) f) = 0} with hS
  have hSsub : S ⊆ mcPts P := by
    intro w hw
    simp only [hS, Set.mem_ofPred_eq] at hw
    simp only [mcPts, Set.mem_ofPred_eq]
    refine ⟨fun k => ?_, hw.2⟩
    by_contra h
    push Not at h
    have h1 := hw.1 k
    simp [h] at h1
  have hScl : IsClosed S := by
    rw [hS]
    simp only [Set.ofPred_and, Set.ofPred_forall]
    refine IsClosed.inter (isClosed_iInter fun k => ?_)
      (isClosed_iInter fun f => isClosed_iInter fun _ => ?_)
    · exact isClosed_eq (continuous_finsetSum _ fun i _ =>
        (continuous_norm.comp (continuous_apply _)).pow 2) continuous_const
    · exact isClosed_eq (MvPolynomial.continuous_eval _) continuous_const
  have hSb : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := (0 : (Σ k, J k) → ℂ)) (r := 1)).subset ?_
    intro w hw
    simp only [hS, Set.mem_ofPred_eq] at hw
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    rintro ⟨k, i⟩
    have h2 : ‖w ⟨k, i⟩‖ ^ 2 ≤ 1 := by
      rw [← hw.1 k]
      exact Finset.single_le_sum (f := fun j => ‖w ⟨k, j⟩‖ ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)
    nlinarith [norm_nonneg (w ⟨k, i⟩)]
  have hScpt : IsCompact S := Metric.isCompact_of_isClosed_isBounded hScl hSb
  obtain ⟨t, ht⟩ := hScpt.elim_finite_subcover O hO
    (fun w hw => Set.mem_iUnion.2 (hcov w (hSsub hw)))
  refine ⟨t.card, fun a => (t.equivFin.symm a : C), ?_⟩
  intro z hz
  have hz0 := hz
  simp only [mcPts, Set.mem_ofPred_eq] at hz0
  have hpos : ∀ k, 0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
    intro k
    obtain ⟨i, hi⟩ := hz0.1 k
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hi) 2)
      (Finset.single_le_sum (f := fun j => ‖z ⟨k, j⟩‖ ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i))
  set c : K → ℂ := fun k => (((Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2))⁻¹ : ℝ) : ℂ) with hcdef
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    rw [hcdef]
    simp only [ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact (Real.sqrt_pos.2 (hpos k)).ne'
  have hck : ∀ k, ‖c k‖ ^ 2 = (∑ i, ‖z ⟨k, i⟩‖ ^ 2)⁻¹ := by
    intro k
    rw [hcdef]
    simp only
    rw [Complex.norm_real, norm_inv, Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt (hpos k).le]
  have hmem := torusSmul_mem_mcPts' P hP c hc z hz
  have hw : torusSmul c z ∈ S := by
    have hm := hmem
    simp only [mcPts, Set.mem_ofPred_eq] at hm
    simp only [hS, Set.mem_ofPred_eq]
    refine ⟨fun k => ?_, hm.2⟩
    have e1 : ∀ i, ‖torusSmul c z ⟨k, i⟩‖ ^ 2 = ‖c k‖ ^ 2 * ‖z ⟨k, i⟩‖ ^ 2 := fun i => by
      show ‖c k * z ⟨k, i⟩‖ ^ 2 = _
      rw [norm_mul, mul_pow]
    rw [Finset.sum_congr rfl (fun i _ => e1 i), ← Finset.mul_sum, hck k,
      inv_mul_cancel₀ (hpos k).ne']
  have hcov' := ht hw
  simp only [Set.mem_iUnion] at hcov'
  obtain ⟨i, hi, hiO⟩ := hcov'
  refine ⟨t.equivFin ⟨i, hi⟩, c, hc, ?_, hmem⟩
  show torusSmul c z ∈ O ((t.equivFin.symm (t.equivFin ⟨i, hi⟩) : C))
  rw [Equiv.symm_apply_apply]
  exact hiO

end GlobalTheory.CompanionTheory.Ar.ChartCover
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixConjugation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric.ConjPoint

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (φ : R →+* R') (ψ : R' →+* R'') :
    dualMap (ψ.comp φ) = (dualMap ψ).comp (dualMap φ) :=
  RingHom.ext fun a => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

theorem dualMap_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (a : R) :
    dualMap φ (algebraMap R (DualNumber R) a) = algebraMap R' (DualNumber R') (φ a) := by
  change dualMap φ (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl (φ a)
  exact TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

theorem centre_conj (z : Spec (CommRingCat.of ℂ) ⟶ X) : centre (spMap (starRingEnd ℂ) ≫ z) = centre z := by
  have h : (spMap (starRingEnd ℂ)) (IsLocalRing.closedPoint ℂ) = IsLocalRing.closedPoint ℂ :=
    Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact congrArg (fun p => z p) h

theorem extends_conj (M : LieModel G ξ E) {x x' : X} (hx : x = x') (h : genPt ξ ⤳ x) (h' : genPt ξ ⤳ x') (e : E)
    (v : epsAt (X.fromSpecStalk x) ⟶ G) (hv : M.Extends ⟨x, h⟩ e v)
    (φ : X.presheaf.stalk x ⟶ CommRingCat.of ℂ) (φ' : X.presheaf.stalk x' ⟶ CommRingCat.of ℂ)
    (H : Spec.map φ' ≫ X.fromSpecStalk x' = spMap (starRingEnd ℂ) ≫ Spec.map φ ≫ X.fromSpecStalk x) :
    ∃ v' : epsAt (X.fromSpecStalk x') ⟶ G, M.Extends ⟨x', h'⟩ e v' ∧
      Spec.map (CommRingCat.ofHom (dualMap φ'.hom)) ≫ v'.left =
        spMap (dualMap (starRingEnd ℂ)) ≫ Spec.map (CommRingCat.ofHom (dualMap φ.hom)) ≫ v.left := by
  subst hx
  refine ⟨v, hv, ?_⟩
  have h1 : Spec.map φ' = Spec.map (φ ≫ CommRingCat.ofHom (starRingEnd ℂ)) := by
    rw [← cancel_mono (X.fromSpecStalk x), H, Spec.map_comp, Category.assoc]
  have h2 : φ' = φ ≫ CommRingCat.ofHom (starRingEnd ℂ) := Spec.map_injective h1
  subst h2
  have h3 : dualMap (φ ≫ CommRingCat.ofHom (starRingEnd ℂ)).hom =
      (dualMap (starRingEnd ℂ)).comp (dualMap φ.hom) := dualMap_comp _ _
  rw [h3, CommRingCat.ofHom_comp, Spec.map_comp]
  exact Category.assoc _ _ _

def conjVec (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : epsAt z ⟶ G) : epsAt (spMap (starRingEnd ℂ) ≫ z) ⟶ G :=
  Over.homMk (spMap (dualMap (starRingEnd ℂ)) ≫ w.left) (by
    have h1 : w.left ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) ≫ z := Over.w w
    have h2 : CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) ≫ CommRingCat.ofHom (dualMap (starRingEnd ℂ)) =
        CommRingCat.ofHom (starRingEnd ℂ) ≫ CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) :=
      CommRingCat.hom_ext (RingHom.ext fun a => dualMap_algebraMap (starRingEnd ℂ) a)
    have h3 := congrArg Spec.map h2
    simp only [Spec.map_comp] at h3
    simp only [Over.mk_hom, Category.assoc, h1]
    rw [← Category.assoc, h3, Category.assoc])

theorem valAt_conj (M : LieModel G ξ E) (z : Spec (CommRingCat.of ℂ) ⟶ X) (e : E) (w : epsAt z ⟶ G)
    (hw : M.ValAt z e w) : M.ValAt (spMap (starRingEnd ℂ) ≫ z) e (conjVec z w) := by
  obtain ⟨h, v, hv, hl⟩ := hw
  have hc := centre_conj z
  have h' : genPt ξ ⤳ centre (spMap (starRingEnd ℂ) ≫ z) := hc ▸ h
  obtain ⟨v', hv', hl'⟩ := extends_conj M hc.symm h h' e v hv (Scheme.stalkClosedPointTo z)
    (Scheme.stalkClosedPointTo (spMap (starRingEnd ℂ) ≫ z)) (by
      refine (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (spMap (starRingEnd ℂ) ≫ z)).trans ?_
      exact congrArg (spMap (starRingEnd ℂ) ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).symm)
  refine ⟨h', v', hv', ?_⟩
  have : (conjVec z w).left = spMap (dualMap (starRingEnd ℂ)) ≫ w.left := rfl
  rw [this, hl]
  exact hl'.symm

theorem gramAt_conj_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), 𝔐.M.GramAt 𝔐.t.PP.L z b Γ → 𝔐.M.GramAt 𝔐.t.PP.L (spMap (starRingEnd ℂ) ≫ z) b (Γ.map (starRingEnd ℂ)) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 z r b Γ ⟨v, hv, hG⟩
  refine ⟨fun i => conjVec z (v i), fun i => valAt_conj 𝔐.M z (b i) (v i) (hv i), fun p q => ?_⟩
  exact _root_.GlobalTheory.CompanionTheory.Ar.HodgeConj.hodgeInnerProduct_conj_abelianScheme E H 𝔐.X 𝔐.t z (v p) (v q) (conjVec z (v p)) (conjVec z (v q)) (Γ p q) rfl rfl (hG p q)

end GlobalTheory.CompanionTheory.Ar.HodgeMetric.ConjPoint
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGeneratedSumSpecialization
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameLat

theorem not_inFibre_of_complex {Ω : Type} [Field Ω] [CharZero Ω] {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {z : Spec (CommRingCat.of ℂ) ⟶ X} (hz : genPt ξ ⤳ centre z) {p : ℕ} (hp : p.Prime) :
    ¬ InFibre ξ p ⟨centre z, hz⟩ := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hs : (Scheme.stalkClosedPointTo z).hom (p : X.presheaf.stalk (centre z)) ≠ 0 := fun h0 =>
    hp0 ((map_natCast (Scheme.stalkClosedPointTo z).hom p).symm.trans h0)
  obtain ⟨u, hu⟩ := CxVal.isUnit _ hs
  have hg : genMap ξ ⟨centre z, hz⟩ (p : X.presheaf.stalk (centre z)) = (p : Ω) := map_natCast _ _
  intro h
  refine h ⟨Nat.cast_ne_zero.2 hp.ne_zero, ⟨_, hg⟩, ⟨((u⁻¹ : (X.presheaf.stalk (centre z))ˣ) : X.presheaf.stalk (centre z)), ?_⟩⟩
  have h1 : genMap ξ ⟨centre z, hz⟩ (u : X.presheaf.stalk (centre z)) = (p : Ω) := by rw [hu, hg]
  have h2 : genMap ξ ⟨centre z, hz⟩ ((u⁻¹ : (X.presheaf.stalk (centre z))ˣ) : X.presheaf.stalk (centre z)) *
      genMap ξ ⟨centre z, hz⟩ (u : X.presheaf.stalk (centre z)) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [h1] at h2
  exact eq_inv_of_mul_eq_one_left h2

theorem frame_mem_lat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (a b : CMType H ⊕ CMType H) (N : ℕ) (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (h : genPt 𝔐.ξ ⤳ centre z), (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre z, h⟩ → ∀ k, ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li) ∈ 𝔐.M.lat ⟨centre z, h⟩ := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 a b N bb z hgen hfr k
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := NumberField.RingOfIntegers.coe_injective
  obtain ⟨hV, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeChar0.lattices_of_char_zero E H D l Xo c _ _ Y S Ω K J y 𝔐 hβ ⟨centre z, hgen⟩
    fun r hr => not_inFibre_of_complex hgen hr
  have hm : bb k ∈ (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype) ⟨centre z, hgen⟩ := by
    rw [hfr.2]
    exact Submodule.subset_span ⟨k, rfl⟩
  have hm' : ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li) ∈ 𝔐.V a ⟨centre z, hgen⟩ ⊔ 𝔐.V b ⟨centre z, hgen⟩ := hm
  rw [hV, hV] at hm'
  refine (sup_le ?_ ?_ : 𝔐.dR a ⟨centre z, hgen⟩ ⊔ 𝔐.dR b ⟨centre z, hgen⟩ ≤ 𝔐.M.lat ⟨centre z, hgen⟩) hm'
  · exact fun x hx => hx.1
  · exact fun x hx => hx.1

end GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameLat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramPullbackIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem lbIso_pull_gram {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (chartPullPull M j j rfl) (chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem hodgeGram_iff_of_sabMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (x' : Sp ℂ ⟶ S') (x : Sp ℂ ⟶ S) (k : ℕ) (v' : Fin k → (epsAt x' ⟶ t'.G)) (v : Fin k → (epsAt x ⟶ t.G)) (Γ : Matrix (Fin k) (Fin k) ℂ), x = x' ≫ f → (∀ a, (v' a).left ≫ m.φ = (v a).left) → (IsHodgeGram t'.G t'.PP.L x' v' Γ ↔ IsHodgeGram t.G t.PP.L x v Γ) := by
  intro E _ _ _ H S S' t t' f m x' x k v' v Γ hx hv
  subst hx
  have hL : LBIso t'.PP.L (t.PP.L.pull m.φ) := m.lin.imp fun _ h => h.1
  constructor
  · rintro ⟨Q, ψ, w, u, Hm, χ, W, hp, hl, hu, hw, hΓ⟩
    refine ⟨Q, ψ ≫ m.φ, w, u, Hm, χ, W, hp.comp m.cart, ?_, hu, fun i => ⟨?_, (hw i).2⟩, hΓ⟩
    · exact LBIso.trans (pull_isLB t.PP.isLB _) (pull_isLB t'.PP.isLB _) Q.isLB (lbIso_pull_gram hL ψ rfl).symm hl
    · rw [← Category.assoc, (hw i).1, hv]
  · rintro ⟨Q, ψ, w, u, Hm, χ, W, hp, hl, hu, hw, hΓ⟩
    have sq : ψ ≫ t.G.hom = (Q.A.hom ≫ x') ≫ f := by
      rw [Category.assoc]; exact hp.1.w
    let ψ' : Q.A.left ⟶ t'.G.left := m.cart.1.lift ψ (Q.A.hom ≫ x') sq
    have h1 : ψ' ≫ m.φ = ψ := m.cart.1.lift_fst _ _ sq
    have h2 : ψ' ≫ t'.G.hom = Q.A.hom ≫ x' := m.cart.1.lift_snd _ _ sq
    have hp' : IsGrpPullback Q.A t'.G x' ψ' := m.cart.cancel (hp.congr rfl h1.symm) h2
    refine ⟨Q, ψ', w, u, Hm, χ, W, hp', ?_, hu, fun i => ⟨?_, (hw i).2⟩, hΓ⟩
    · exact LBIso.trans (pull_isLB t'.PP.isLB _) (pull_isLB t.PP.isLB _) Q.isLB (lbIso_pull_gram hL ψ' h1.symm) hl
    · apply m.cart.1.hom_ext
      · rw [Category.assoc, h1, (hw i).1, hv]
      · rw [Category.assoc, h2, ← Category.assoc, Over.w (w i), Over.w (v' i)]
        rfl

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFrameSubBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.SubFrame

theorem isFrameAt_comp : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (V' : Submodule Ω E) (q : Cpt ξ) (g n : ℕ) (b : Fin g → E) (ix : Fin n → Fin g), Function.Injective ix → LinearIndependent Ω b → L q = Submodule.span (regAt ξ q) (Set.range b) → V' = Submodule.span Ω (Set.range (b ∘ ix)) → (L.inter V').IsFrameAt (b ∘ ix) q := by
  intro X Ω _ ξ E _ _ L V' q g n b ix hix hb hL hV
  subst hV
  refine And.intro (hb.comp ix hix) ?_
  show L q ⊓ Submodule.restrictScalars (regAt ξ q) (Submodule.span Ω (Set.range (b ∘ ix))) = _
  rw [hL]
  apply le_antisymm
  · rintro x ⟨hx1, hx2⟩
    have hx2' : x ∈ Submodule.span Ω (Set.range (b ∘ ix)) := hx2
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx1
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 hx2'
    have hc' : ∑ i, (c i : Ω) • b i = x := hc
    have hD : ∑ i, (∑ j, if ix j = i then d j else 0) • b i = x := by
      rw [← hd]
      simp only [Finset.sum_smul, ite_smul, zero_smul]
      rw [Finset.sum_comm]
      simp [Finset.sum_ite_eq]
    have key : ∀ i, (c i : Ω) = ∑ j, if ix j = i then d j else 0 := by
      have h0 := Fintype.linearIndependent_iff.1 hb
        (fun i => (c i : Ω) - ∑ j, if ix j = i then d j else 0) (by
          simp only [sub_smul, Finset.sum_sub_distrib]
          rw [hc', hD, sub_self])
      intro i
      exact sub_eq_zero.1 (h0 i)
    rw [← hc]
    apply Submodule.sum_mem
    intro i _
    by_cases h : ∃ j, ix j = i
    · obtain ⟨j, rfl⟩ := h
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · simp only [not_exists] at h
      have hci : c i = 0 := by
        apply Subtype.ext
        rw [key i]
        simp [h]
      rw [hci, zero_smul]
      exact Submodule.zero_mem _
  · apply le_inf
    · exact Submodule.span_mono (Set.range_comp_subset_range _ _)
    · exact Submodule.span_le_restrictScalars _ _ _

end GlobalTheory.CompanionTheory.Ar.SubFrame
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeIntersectionFrameSubspace
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.LocalFrames

theorem span_eq_of_saturated : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (V' : Submodule Ω E) (p : Cpt ξ) (g : ℕ) (b : Fin g → E) (S : Finset (Fin g)), IsCptGen ξ → Submodule.span Ω (Set.range b) = ⊤ → L p = Submodule.span (regAt ξ p) (Set.range b) → (L.inter V') p = Submodule.span (regAt ξ p) (b '' S) → V' = Submodule.span Ω (b '' S) := by
  intro X Ω _ ξ E _ _ L V' p g b S h hspan hL hI
  haveI hfr : IsFractionRing (regAt ξ p) Ω := (RegAtRing.regAt_ring X Ω ξ h p).1
  have sm : ∀ (c : regAt ξ p) {m : E}, m ∈ L p → (c : Ω) • m ∈ L p := fun c _ hm => (L p).smul_mem c hm
  have key : ∀ x : E, ∃ d : regAt ξ p, (d : Ω) ≠ 0 ∧ (d : Ω) • x ∈ L p := by
    intro x
    have hx : x ∈ Submodule.span Ω (Set.range b) := hspan ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      refine ⟨1, by simp, ?_⟩
      rw [hL]
      simpa using Submodule.subset_span hy
    | zero => exact ⟨1, by simp, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨d, hd, hdy⟩ := hy
      obtain ⟨e, he, hez⟩ := hz
      refine ⟨d * e, by rw [Subring.coe_mul]; exact mul_ne_zero hd he, ?_⟩
      have : ((d * e : regAt ξ p) : Ω) • (y + z) = (e : Ω) • ((d : Ω) • y) + (d : Ω) • ((e : Ω) • z) := by
        simp only [Subring.coe_mul, smul_add, smul_smul, mul_comm]
      rw [this]
      exact (L p).add_mem (sm e hdy) (sm d hez)
    | smul a y _ hy =>
      obtain ⟨d, hd, hdy⟩ := hy
      obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := regAt ξ p) a
      have hv0 : (v : Ω) ≠ 0 := by
        have := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := Ω) hv
        simpa using this
      refine ⟨v * d, by rw [Subring.coe_mul]; exact mul_ne_zero hv0 hd, ?_⟩
      have : ((v * d : regAt ξ p) : Ω) • ((algebraMap (regAt ξ p) Ω u / algebraMap (regAt ξ p) Ω v) • y) =
          (u : Ω) • ((d : Ω) • y) := by
        have hu : algebraMap (regAt ξ p) Ω u = (u : Ω) := rfl
        have hv' : algebraMap (regAt ξ p) Ω v = (v : Ω) := rfl
        rw [hu, hv', smul_smul, smul_smul, Subring.coe_mul]
        congr 1
        field_simp
      rw [this]
      exact sm u hdy
  apply le_antisymm
  · intro x hx
    obtain ⟨d, hd, hdx⟩ := key x
    have h1 : (d : Ω) • x ∈ (L.inter V') p := ⟨hdx, V'.smul_mem _ hx⟩
    rw [hI] at h1
    have h2 : (d : Ω) • x ∈ Submodule.span Ω (b '' S) :=
      Submodule.span_subset_span (regAt ξ p) Ω (b '' S) h1
    exact (Submodule.smul_mem_iff _ hd).1 h2
  · rw [Submodule.span_le]
    intro y hy
    have h1 : y ∈ (L.inter V') p := by
      rw [hI]
      exact Submodule.subset_span hy
    exact h1.2

end GlobalTheory.CompanionTheory.Ar.LocalFrames
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeRankTwoG
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.PeriodRank

theorem finrank_la_eq_two_mul :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ)
      (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)), IsPeriod D ty P →
      Module.finrank ℤ D.La = 2 * g :=
  fun _ _ _ _ _ _ _ _ _ hP => (GlobalTheory.FibreExp.free_finite_finrank_of_isPeriod hP).2.2

end GlobalTheory.CompanionTheory.Ar.Flat.PeriodRank
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusOverLieModelBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_over_lie_model_base_change : ∀ (L L' : Type) [Field L] [Field L'] (e : L →+* L') (G : Over (Sp L)) (G' : Over (Sp L')) [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left) (τ : TorusExtension G) (τ' : TorusExtension G'), IsGrpPullback G' G (spMap e) φ → GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.TorusOver e τ τ' φ → ∀ (V V' : Type) [AddCommGroup V] [Module L V] [AddCommGroup V'] [Module L' V'] (MV : LieModel G (𝟙 (Sp L)) V) (MV' : LieModel G' (𝟙 (Sp L')) V') (j : V →+ V'), (∀ x, (MV'.pt (j x)).left ≫ φ = spMap (dualMap e) ≫ (MV.pt x).left) → ∀ I : AddSubgroup V, (letI := τ.addCommGroup; ∃ MT : LieModel (splitTorus (Sp L) τ.X) (𝟙 _) (τ.X →+ L), IsCocharLie MT ∧ ∀ x, x ∈ I ↔ ∃ δ : τ.X →+ ℤ, MV.pt x = MT.pt ((Int.castAddHom L).comp δ) ≫ τ.i) → (letI := τ'.addCommGroup; ∃ MT : LieModel (splitTorus (Sp L') τ'.X) (𝟙 _) (τ'.X →+ L'), IsCocharLie MT ∧ ∀ x, x ∈ I.map j ↔ ∃ δ : τ'.X →+ ℤ, MV'.pt x = MT.pt ((Int.castAddHom L').comp δ) ≫ τ'.i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.CocharsBC.cochars_baseChange | exact GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.CocharsBC.cochars_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.CocharsBC.cochars_baseChange <;> assumption)
end

