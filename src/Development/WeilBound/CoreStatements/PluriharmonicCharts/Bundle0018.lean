module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0105
public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.FderivValueZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open scoped Matrix ComplexOrder

noncomputable section

namespace PositivityTheory.Xgp.c_bm_exists_period

theorem exists_embedding (K k : Type) [Field K] [Field k] [Countable K] [Countable k] (β : K →+* k) (s : K →+* ℂ) :
    ∃ j : k →+* ℂ, j.comp β = s := by
  letI := β.toAlgebra
  letI := s.toAlgebra
  obtain ⟨I₁, x, hx⟩ := exists_isTranscendenceBasis' K k
  obtain ⟨κ, z, hz⟩ := exists_isTranscendenceBasis' K ℂ
  have hI₁ : Countable I₁ := hx.1.injective.countable
  have hκ : Cardinal.mk ℂ = Cardinal.mk κ := by
    have := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' z hz
      (Cardinal.mk_le_aleph0_iff.2 inferInstance) (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum)
    exact this
  have hle : Cardinal.mk I₁ ≤ Cardinal.mk κ := by
    rw [← hκ, Cardinal.mk_complex]
    exact (Cardinal.mk_le_aleph0_iff.2 hI₁).trans Cardinal.aleph0_le_continuum
  obtain ⟨e⟩ := hle
  have hz' : AlgebraicIndependent K (z ∘ e) := hz.1.comp e e.injective
  letI : Algebra (MvPolynomial I₁ K) k := (MvPolynomial.aeval x : MvPolynomial I₁ K →ₐ[K] k).toRingHom.toAlgebra
  letI : Algebra (MvPolynomial I₁ K) ℂ := (MvPolynomial.aeval (z ∘ e) : MvPolynomial I₁ K →ₐ[K] ℂ).toRingHom.toAlgebra
  haveI : FaithfulSMul (MvPolynomial I₁ K) k := (faithfulSMul_iff_algebraMap_injective _ _).2 hx.1
  haveI : FaithfulSMul (MvPolynomial I₁ K) ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2 hz'
  haveI : Algebra.IsAlgebraic (MvPolynomial I₁ K) k := by
    haveI := hx.isAlgebraic
    exact Algebra.IsAlgebraic.of_ringHom_of_comp_eq (S := Algebra.adjoin K (Set.range x)) (B := k) hx.1.aevalEquiv
      (RingHom.id k) hx.1.aevalEquiv.surjective Function.injective_id
      (RingHom.ext fun p => hx.1.algebraMap_aevalEquiv p)
  let j : k →ₐ[MvPolynomial I₁ K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨j.toRingHom, RingHom.ext fun a => ?_⟩
  have h := j.commutes (MvPolynomial.C a)
  have h1 : algebraMap (MvPolynomial I₁ K) k (MvPolynomial.C a) = β a := MvPolynomial.aeval_C x a
  have h2 : algebraMap (MvPolynomial I₁ K) ℂ (MvPolynomial.C a) = s a := MvPolynomial.aeval_C (z ∘ e) a
  rw [h1, h2] at h
  exact h

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem genMap_bij (hξ : IsCptGen ξ) (q : X) (hq : q = genPt ξ) (h : genPt ξ ⤳ q) :
    Function.Bijective (genMap ξ ⟨q, h⟩) := by
  subst hq
  have : X.presheaf.stalkSpecializes h = 𝟙 _ := TopCat.Presheaf.stalkSpecializes_refl _ _
  refine ⟨hξ.inj _, ?_⟩
  unfold genMap
  simp only [this]
  exact hξ.bij.2

theorem countable_of_tie {κ : Type} [Finite κ] {x : κ → Ω} (h : CoordTie ℤ ξ x) : Countable Ω := by
  obtain ⟨c, hc⟩ := h.cover ⟨genPt ξ, specializes_rfl⟩
  haveI : Countable (MvPolynomial κ ℤ) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact MvPolynomial.cardinalMk_le_max.trans (max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl)
  refine Function.Surjective.countable (f := fun a : MvPolynomial κ ℤ × MvPolynomial κ ℤ =>
    MvPolynomial.aeval (fun j => x j / x c) a.1 / MvPolynomial.aeval (fun j => x j / x c) a.2) fun a => ?_
  obtain ⟨s, hs, hu, hsa⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.regAt_iff_exists_chart_fraction X Ω ξ ℤ κ x h c _ hc a).1 ((genMap_bij h.gen _ rfl _).2 a)
  rw [Algebra.adjoin_range_eq_range_aeval] at hs hsa
  obtain ⟨f, hf⟩ := hs
  obtain ⟨g, hg⟩ := hsa
  refine ⟨(g, f), ?_⟩
  have hf' : MvPolynomial.aeval (fun j => x j / x c) f = s := hf
  have hg' : MvPolynomial.aeval (fun j => x j / x c) g = s * a := hg
  simp only [hf', hg']
  exact mul_div_cancel_left₀ _ hu.1

theorem cancel_gen (hξ : IsCptGen ξ) {R : Type} [CommRing R] {a b : Ω →+* R} (h : spMap a ≫ ξ = spMap b ≫ ξ) :
    a = b := by
  have e := LieTangent.spec_genMap ξ ⟨genPt ξ, specializes_rfl⟩
  have h' : (spMap a ≫ Spec.map (CommRingCat.ofHom (genMap ξ ⟨genPt ξ, specializes_rfl⟩))) ≫ X.fromSpecStalk _ =
      (spMap b ≫ Spec.map (CommRingCat.ofHom (genMap ξ ⟨genPt ξ, specializes_rfl⟩))) ≫ X.fromSpecStalk _ := by
    rw [Category.assoc, Category.assoc, e, h]
  rw [cancel_mono, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp] at h'
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h')
  refine RingHom.ext fun t => ?_
  obtain ⟨s, rfl⟩ := (genMap_bij hξ _ rfl specializes_rfl).2 t
  exact DFunLike.congr_fun h2 s

theorem factor_gen (hξ : IsCptGen ξ) {R : Type} [CommRing R] [IsLocalRing R] (V : Sp R ⟶ X)
    (hV : centre V = genPt ξ) : ∃ δ : Ω →+* R, spMap δ ≫ ξ = V := by
  have h : genPt ξ ⤳ centre V := hV ▸ specializes_rfl
  let e := RingEquiv.ofBijective _ (genMap_bij hξ _ hV h)
  refine ⟨(Scheme.stalkClosedPointTo V).hom.comp e.symm.toRingHom, ?_⟩
  have e1 := LieTangent.spec_genMap ξ ⟨centre V, h⟩
  have e2 := LieTangent.spec_centre V
  refine (congrArg (spMap _ ≫ ·) e1.symm).trans (Eq.trans ?_ e2)
  rw [← Category.assoc, spMap, ← Spec.map_comp]
  congr 2
  ext s
  exact congrArg (Scheme.stalkClosedPointTo V).hom (e.symm_apply_apply s)

theorem hom_dual_ext {F₀ F : Type} [Field F₀] [Field F] [CharZero F] (i : F₀ →+* F)
    (hfin : 0 < (letI := i.toAlgebra; Module.finrank F₀ F)) {δ δ' : F →+* DualNumber ℂ} (h : δ.comp i = δ'.comp i)
    (h' : ∀ x, (δ x).fst = (δ' x).fst) : δ = δ' := by
  letI := i.toAlgebra
  letI := (δ.comp i).toAlgebra
  haveI : CharZero F₀ := i.charZero
  haveI : Module.Finite F₀ F := Module.finite_of_finrank_pos hfin
  have hu : Algebra.FormallyUnramified F₀ F := Algebra.FormallyUnramified.of_isSeparable F₀ F
  have h := Algebra.FormallyUnramified.ext' (R := F₀) (A := F) (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom
    ⟨2, by
      rw [Submodule.zero_eq_bot, eq_bot_iff, sq, Ideal.mul_le]
      intro a ha b hb
      have ha' : a.fst = 0 := ha
      have hb' : b.fst = 0 := hb
      rw [Ideal.mem_bot]
      ext <;> simp [ha', hb']⟩
    { δ with commutes' := fun _ => rfl } { δ' with commutes' := fun r => (DFunLike.congr_fun h r).symm } h'
  exact RingHom.ext fun x => DFunLike.congr_fun h x

theorem const_of_finite {Y : Scheme.{0}} {Ω₀ : Type} [Field Ω₀] [CharZero Ω] {ξ₀ : Sp Ω₀ ⟶ Y} (hξ : IsCptGen ξ)
    (hξ₀ : IsCptGen ξ₀) {f : X ⟶ Y} {i : Ω₀ →+* Ω} (hf : ξ ≫ f = spMap i ≫ ξ₀)
    (hfin : 0 < (letI := i.toAlgebra; Module.finrank Ω₀ Ω)) {φ : Ω →+* ℂ} {V : Sp (DualNumber ℂ) ⟶ X}
    (h1 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ V = spMap φ ≫ ξ)
    (h2 : V ≫ f = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (spMap φ ≫ ξ) ≫ f) :
    V = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap φ ≫ ξ := by
  have hc : centre V = genPt ξ := by
    have a1 : centre (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ V) = centre V := by
      exact congrArg V (Spec_closedPoint (f := CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom))
    rw [← a1, h1]
    exact SheetDecomposition.CovSch.centre_spMap φ ξ
  obtain ⟨δ, rfl⟩ := factor_gen hξ V hc
  have sc : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap (g.comp f) = spMap g ≫ spMap f := fun f g => Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)
  have e1 : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp δ = φ := cancel_gen hξ (by rw [sc, Category.assoc, h1])
  have e2 : δ.comp i = ((algebraMap ℂ (DualNumber ℂ)).comp φ).comp i := cancel_gen hξ₀ (by
    rw [sc, sc _ ((algebraMap ℂ (DualNumber ℂ)).comp φ), sc φ, Category.assoc, Category.assoc, Category.assoc, ← hf]
    simpa only [Category.assoc] using h2)
  rw [hom_dual_ext i hfin e2 fun x => by
    simpa [TrivSqZeroExt.algebraMap_eq_inl] using DFunLike.congr_fun e1 x, sc, Category.assoc]

theorem fderiv_value_zero (hξ : IsCptGen ξ) (hall : ∀ q : X, genPt ξ ⤳ q) {n : ℕ} {B : Set (Fin n → ℂ)}
    {p : (Fin n → ℂ) → (Sp ℂ ⟶ X)} (hp : IsHolTo B p) (h0 : 0 ∈ B) (hc : centre (p 0) = centre ξ) {v : Fin n → ℂ}
    (hv : IsDerivAt0 p v (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p 0)) {a : Ω} {r : (Fin n → ℂ) → ℂ}
    (hr : ∀ᶠ u in nhds 0, ValAt ξ (p u) a (r u)) : fderiv ℂ r 0 v = 0 := by
  obtain ⟨g, rfl⟩ := hξ.bij.2 a
  obtain ⟨U, hU, s, rfl⟩ := X.presheaf.exists_germ_eq g
  have hU0 : ⊤ ≤ p 0 ⁻¹ᵁ U := (SheetDecomposition.CovSch.top_le_iff _ _).2 (hc ▸ hU)
  have he : r =ᶠ[nhds 0] fun u => valAt' (p u) U s := by
    filter_upwards [hr, GlobalTheory.LocalLift.hol_eventually_mem hp h0 hU0] with u h1 h2
    have h3 := (SheetDecomposition.CovSch.top_le_iff _ _).1 h2.2
    rw [SheetDecomposition.CovSch.valAt'_eq _ _ h3]
    exact SheetDecomposition.CovSch.v_unique hξ h1 (SheetDecomposition.CovSch.valAt_sec (hall _) U h3 hU s)
  have h1 : ⊤ ≤ (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p 0) ⁻¹ᵁ U := fun q _ => hU0 (Set.mem_univ _)
  rw [he.fderiv_eq, ← hv.2 U h1 s]
  have := GlobalTheory.TangentOrigin.evalPt_spMap_comp (algebraMap ℂ (DualNumber ℂ)) (p 0) U hU0 h1 s
  refine (congrArg TrivSqZeroExt.snd this).trans ?_
  simp [TrivSqZeroExt.algebraMap_eq_inl]

end PositivityTheory.Xgp.c_bm_exists_period
end
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.InBlockChartOfInChart
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.c_bm_exists_local

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

def HoldsOff (Q₀ : Ideal (MRing J)) (G : Ideal (MRing J) → Prop) : Prop :=
  ∃ (d : K → ℕ) (h : MRing J), IsMultiHomog h d ∧ h ∉ Q₀ ∧ ∀ Q : Ideal (MRing J), h ∉ Q → G Q

variable {Q₀ : Ideal (MRing J)}

theorem HoldsOff.mono {G G' : Ideal (MRing J) → Prop} (h : HoldsOff Q₀ G) (hG : ∀ Q, G Q → G' Q) :
    HoldsOff Q₀ G' :=
  let ⟨d, f, h1, h2, h3⟩ := h
  ⟨d, f, h1, h2, fun Q hQ => hG Q (h3 Q hQ)⟩

theorem holdsOff_of_forall (hQ : Q₀.IsPrime) {G : Ideal (MRing J) → Prop} (h : ∀ Q, G Q) : HoldsOff Q₀ G :=
  ⟨0, 1, GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_one, (Ideal.ne_top_iff_one _).1 hQ.ne_top, fun Q _ => h Q⟩

theorem HoldsOff.and (hQ : Q₀.IsPrime) {G G' : Ideal (MRing J) → Prop} (h : HoldsOff Q₀ G) (h' : HoldsOff Q₀ G') :
    HoldsOff Q₀ fun Q => G Q ∧ G' Q := by
  obtain ⟨d, f, h1, h2, h3⟩ := h
  obtain ⟨d', f', h1', h2', h3'⟩ := h'
  exact ⟨d + d', f * f', GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_mul h1 h1', fun h => (hQ.mem_or_mem h).elim h2 h2',
    fun Q h => ⟨h3 Q fun a => h (Q.mul_mem_right _ a), h3' Q fun a => h (Q.mul_mem_left _ a)⟩⟩

theorem holdsOff_forall (hQ : Q₀.IsPrime) {α : Type} [Finite α] {G : α → Ideal (MRing J) → Prop}
    (h : ∀ a, HoldsOff Q₀ (G a)) : HoldsOff Q₀ fun Q => ∀ a, G a Q := by
  classical
  haveI := Fintype.ofFinite α
  have key : ∀ s : Finset α, HoldsOff Q₀ fun Q => ∀ a ∈ s, G a Q := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact holdsOff_of_forall hQ (by simp)
    | insert a s _ ih =>
      refine (HoldsOff.and hQ (h a) ih).mono fun Q hh b hb => ?_
      rcases Finset.mem_insert.1 hb with rfl | hb
      · exact hh.1
      · exact hh.2 b hb
  exact (key Finset.univ).mono fun Q hh a => hh a (Finset.mem_univ a)

theorem holdsOff_regAt {Ω : Type} [Field Ω] {x : (Σ k, J k) → Ω} {s : Ω} (h : RegAt x Q₀ s) :
    HoldsOff Q₀ fun Q => RegAt x Q s :=
  let ⟨d, g, t, hg, ht, h0, e⟩ := h
  ⟨d, t, ht, h0, fun _ hQ => ⟨d, g, t, hg, ht, hQ, e⟩⟩

theorem inBlockChart_of_inChart {Z : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ Z}
    {x : (Σ k, J k) → Ω} {c : ∀ k, J k} {q : Cpt ξ} (h : InChart ξ (segreCoord x) c q) : InBlockChart ξ x c q := by
  classical
  obtain ⟨h0, hc⟩ := h
  have h1 : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 h0 k (Finset.mem_univ k)
  refine fun k => ⟨h1 k, fun i => ?_⟩
  convert hc (Function.update c k i) using 1
  unfold segreCoord
  rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
  · simp
  · intro k' _ hk
    rw [Function.update_of_ne hk, div_self (h1 k')]
  · simp

theorem exists_frameDomain {Z : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ Z}
    {x : (Σ k, J k) → Ω} (tie : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, x ⟨k, c' k⟩)
    {z : Spec (CommRingCat.of ℂ) ⟶ Z} {w : (Σ k, J k) → ℂ} (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ x z w)
    {c : ∀ k, J k} (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) {G : Ideal (MRing J) → Prop} (hG : HoldsOff (mCoordIdeal w) G) :
    ∃ f : Ω, InFrameDomain x c f w ∧
      ∀ p : Cpt ξ, InChart ξ (segreCoord x) c p → unitAt ξ p f → InBlockChart ξ x c p ∧ G (ptIdeal ξ x p) := by
  obtain ⟨d, h, hd, h0, hG⟩ := hG
  refine ⟨MvPolynomial.aeval x h / ∏ k, x ⟨k, c k⟩ ^ d k, ⟨hc, _,
    (_root_.GlobalTheory.CompanionTheory.Ar.valAt_iff_isValueAt_coords Z Ω ξ K J x tie z w hz hw _ _).1 (valAt_form hw hz hc hd), ?_⟩, fun p hp hu => ?_⟩
  · rw [form_mem_mCoordIdeal_iff w hd] at h0
    exact div_ne_zero h0 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k))
  · have hb := inBlockChart_of_inChart hp
    refine ⟨hb, hG _ ?_⟩
    obtain ⟨R, _, z', w', e, hw', -⟩ := exists_ptIdeal_eq tie p
    have hz' : genPt ξ ⤳ centre z' := e ▸ p.2
    obtain rfl : p = ⟨centre z', hz'⟩ := Subtype.ext e.symm
    have hc' := (inBlockChart_centre_iff hw' hz' c).1 hb
    rw [ptIdeal_centre hw' hz', form_mem_mCoordIdeal_iff w' hd]
    rw [unitAt_iff_of_valAt (valAt_form hw' hz' hc' hd) hz'] at hu
    intro h1
    exact hu (by rw [h1, zero_div])

theorem exists_goodDomain {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
    {y : (Σ k, ι k) → Φ} {Ψ : Type} [Finite Ψ] {N j : ℕ} (M : FlagModel y Ψ N j)
    (F : FrameData ι Ψ N M.Ω M.blk) {Z : Scheme.{0}} {ξ : Spec (CommRingCat.of M.Ω) ⟶ Z}
    (tie : CoordTie ℤ ξ fun c' : (k : NonPluckerBlocks M.blk) → baseIdx ι M.blk k => ∏ k, M.x ⟨k, c' k⟩)
    {z : Spec (CommRingCat.of ℂ) ⟶ Z} {w : (Σ k, baseIdx ι M.blk k) → ℂ} (hz : genPt ξ ⤳ centre z)
    (hw : CoordsAt ξ M.x z w) (hF : M.GoodAt F (mCoordIdeal w)) :
    ∃ f : M.Ω, InFrameDomain M.x F.c f w ∧
      ∀ p : Cpt ξ, InChart ξ (segreCoord M.x) F.c p → unitAt ξ p f → M.GoodAt F (ptIdeal ξ M.x p) := by
  have hP : (mCoordIdeal w).IsPrime := RingHom.ker_isPrime _
  have hc : ∀ k, w ⟨k, F.c k⟩ ≠ 0 := by
    refine (inBlockChart_centre_iff hw hz F.c).1 ((inBlockChart_iff_X_notMem tie _ F.c).2 ?_)
    rw [ptIdeal_centre hw hz]
    exact hF.1
  have h1 : HoldsOff (mCoordIdeal w) fun Q => ∀ q I, RegAt M.x Q (F.u q I) ∧ RegAt M.x Q (F.u' I q) :=
    holdsOff_forall hP fun q => holdsOff_forall hP fun I =>
      HoldsOff.and hP (holdsOff_regAt (hF.2.1 q I).1) (holdsOff_regAt (hF.2.1 q I).2)
  have h2 : HoldsOff (mCoordIdeal w) fun Q => ∀ p, M.blk p = none →
      F.υ p ≠ 0 ∧ RegAt M.x Q (F.υ p) ∧ RegAt M.x Q (F.υ p)⁻¹ := by
    refine holdsOff_forall hP fun p => ?_
    by_cases hp : M.blk p = none
    · obtain ⟨a, b, c⟩ := hF.2.2 p hp
      exact (HoldsOff.and hP (holdsOff_regAt b) (holdsOff_regAt c)).mono fun Q h _ => ⟨a, h⟩
    · exact holdsOff_of_forall hP fun Q h => absurd h hp
  obtain ⟨f, hf, hg⟩ := exists_frameDomain tie hz hw hc (HoldsOff.and hP h1 h2)
  exact ⟨f, hf, fun p a b => ⟨(inBlockChart_iff_X_notMem tie p F.c).1 (hg p a b).1, (hg p a b).2⟩⟩

end PositivityTheory.Xgp.c_bm_exists_local
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.IsOpenDet
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option linter.unusedSectionVars false

namespace PositivityTheory.Xgp.c_bm_exists_period

section Hol
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {I J K : Type} [Fintype I] [Fintype J] [Fintype K]

def HolM (s : Set X) (A : X → Matrix I J ℂ) : Prop := ∀ a b, DifferentiableOn ℂ (fun x => A x a b) s

theorem HolM.const (s : Set X) (A : Matrix I J ℂ) : HolM s fun _ => A := fun _ _ => differentiableOn_const _

theorem HolM.mono {s t : Set X} {A : X → Matrix I J ℂ} (h : HolM s A) (ht : t ⊆ s) : HolM t A :=
  fun a b => (h a b).mono ht

theorem HolM.mul {s : Set X} {A : X → Matrix I J ℂ} {B : X → Matrix J K ℂ} (hA : HolM s A) (hB : HolM s B) :
    HolM s fun x => A x * B x := fun a b => by
  simp only [Matrix.mul_apply]
  exact DifferentiableOn.fun_sum fun k _ => (hA a k).mul (hB k b)

theorem HolM.det [DecidableEq I] {s : Set X} {A : X → Matrix I I ℂ} (hA : HolM s A) :
    DifferentiableOn ℂ (fun x => (A x).det) s := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  apply DifferentiableOn.fun_sum
  intro σ _
  refine (differentiableOn_const _).mul ?_
  have key : ∀ t : Finset I, DifferentiableOn ℂ (fun x => ∏ i ∈ t, A x (σ i) i) s := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · simp only [Finset.prod_empty]
      exact differentiableOn_const _
    · intro j t hj ih
      simp only [Finset.prod_insert hj]
      exact (hA (σ j) j).mul ih
  exact key Finset.univ

theorem HolM.inv [DecidableEq I] {s : Set X} {A : X → Matrix I I ℂ} (hA : HolM s A) (hd : ∀ x ∈ s, (A x).det ≠ 0) :
    HolM s fun x => (A x)⁻¹ := by
  intro a b
  have hu : HolM s fun x => (A x).updateRow b (Pi.single a 1) := by
    intro i k
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact differentiableOn_const _
    · exact hA i k
  simp only [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact (hA.det.inv hd).mul hu.det

theorem HolM.isOpen_det [DecidableEq I] {s : Set X} {A : X → Matrix I I ℂ} (hA : HolM s A) (hs : IsOpen s) :
    IsOpen {x ∈ s | (A x).det ≠ 0} :=
  hA.det.continuousOn.isOpen_inter_preimage hs isOpen_ne

noncomputable def dM (A : X → Matrix I J ℂ) (u v : X) : Matrix I J ℂ :=
  Matrix.of fun a b => fderiv ℂ (fun x => A x a b) u v

theorem dM_mul {s : Set X} {A : X → Matrix I J ℂ} {B : X → Matrix J K ℂ} (hA : HolM s A) (hB : HolM s B) {u : X}
    (hu : s ∈ nhds u) (v : X) : dM (fun x => A x * B x) u v = dM A u v * B u + A u * dM B u v := by
  have hd : ∀ a b, DifferentiableAt ℂ (fun x => A x a b) u := fun a b => (hA a b).differentiableAt hu
  have he : ∀ a b, DifferentiableAt ℂ (fun x => B x a b) u := fun a b => (hB a b).differentiableAt hu
  ext a c
  simp only [dM, Matrix.of_apply, Matrix.mul_apply, Matrix.add_apply]
  have key : HasFDerivAt (fun x => ∑ j, A x a j * B x j c)
      (∑ j, (A u a j • fderiv ℂ (fun x => B x j c) u + B u j c • fderiv ℂ (fun x => A x a j) u)) u :=
    HasFDerivAt.fun_sum fun j _ => (hd a j).hasFDerivAt.mul (he j c).hasFDerivAt
  rw [key.fderiv]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1 <;> refine Finset.sum_congr rfl fun j _ => by ring

theorem dM_const {A : X → Matrix I J ℂ} {C : Matrix I J ℂ} {u : X} (h : ∀ᶠ x in nhds u, A x = C) (v : X) :
    dM A u v = 0 := by
  ext a b
  simp only [dM, Matrix.of_apply, Matrix.zero_apply]
  have he : (fun x => A x a b) =ᶠ[nhds u] fun _ => C a b := h.mono fun x hx => by simp [hx]
  rw [he.fderiv_eq]
  simp

end Hol

end PositivityTheory.Xgp.c_bm_exists_period
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.PullDegSome
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section
namespace PositivityTheory.Xgp.c_algsq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def κ₁ (k₀ : K) (k : K) : Option K := if k = k₀ then none else some k

theorem κ₁_self (k₀ : K) : κ₁ k₀ k₀ = none := if_pos rfl

theorem κ₁_ne {k₀ k : K} (h : k ≠ k₀) : κ₁ k₀ k = some k := if_neg h

theorem κ₁_inj (k₀ : K) : Function.Injective (κ₁ k₀) := by
  intro a b h
  unfold κ₁ at h
  split_ifs at h with ha hb hb <;>
    first
    | exact ha.trans hb.symm
    | (cases h; rfl)
    | cases h
    | exact Option.some_injective _ h

theorem isBlockMap_v₁ (k₀ : K) :
    IsBlockMap (ι := ι) (ι' := fun o : Option K => ι (o.getD k₀)) (κ₁ k₀) (v₁ k₀) := by
  have h3 : ∀ p : (k : K) × ι k, (v₁ k₀ p).fst = κ₁ k₀ p.fst := fun p => by
    unfold v₁ κ₁
    split_ifs <;> rfl
  refine ⟨κ₁_inj k₀, ?_, h3, ?_⟩
  · rintro ⟨a, x⟩ ⟨b, y⟩ h
    have hfst : κ₁ k₀ a = κ₁ k₀ b := by
      have e := congrArg Sigma.fst h
      rwa [h3, h3] at e
    have hab : a = b := κ₁_inj k₀ hfst
    subst hab
    unfold v₁ at h
    split_ifs at h with ha
    · have h2 := (Sigma.mk.inj_iff.mp h).2
      obtain rfl := eq_of_heq ((cast_heq _ x).symm.trans (h2.trans (cast_heq _ y)))
      rfl
    · have h2 := (Sigma.mk.inj_iff.mp h).2
      obtain rfl := eq_of_heq h2
      rfl
  · rintro ⟨o, x⟩ ⟨j, hj⟩
    cases o with
    | none =>
      refine ⟨⟨k₀, x⟩, ?_⟩
      unfold v₁
      rw [dite_eq_left rfl]
      rfl
    | some k =>
      have hk : k ≠ k₀ := by
        intro hk
        unfold κ₁ at hj
        split_ifs at hj with h1 <;>
          first
          | (cases hj; exact h1 hk)
          | cases hj
          | exact h1 ((Option.some_injective _ hj).trans hk)
      refine ⟨⟨k, x⟩, ?_⟩
      unfold v₁
      rw [dite_eq_right hk]

theorem pullDeg_some (xi : K → ℤ) (o : Option K) : pullDeg (some : K → Option K) xi o = o.elim 0 xi := by
  unfold pullDeg
  cases o with
  | none =>
    have hn : ¬∃ a : K, some a = (none : Option K) := by
      rintro ⟨a, ha⟩
      cases ha
    rw [Function.extend_apply' _ _ _ hn]
    rfl
  | some k =>
    exact (Option.some_injective K).extend_apply xi 0 k

theorem pullDeg_κ₁ (k₀ : K) (xi : K → ℤ) (o : Option K) :
    pullDeg (κ₁ k₀) xi o = o.elim (xi k₀) fun k => if k = k₀ then 0 else xi k := by
  unfold pullDeg
  cases o with
  | none =>
    have e := (κ₁_inj k₀).extend_apply xi 0 k₀
    rw [κ₁_self] at e
    exact e
  | some k =>
    by_cases hk : k = k₀
    · have hn : ¬∃ j : K, κ₁ k₀ j = some k := by
        rintro ⟨j, hj⟩
        unfold κ₁ at hj
        split_ifs at hj with h1 <;>
          first
          | (cases hj; exact h1 hk)
          | cases hj
          | exact h1 ((Option.some_injective _ hj).trans hk)
      rw [Function.extend_apply' _ _ _ hn]
      simp [hk]
    · have e := (κ₁_inj k₀).extend_apply xi 0 k
      rw [κ₁_ne hk] at e
      rw [e]
      simp [hk]

end PositivityTheory.Xgp.c_algsq
end
end

