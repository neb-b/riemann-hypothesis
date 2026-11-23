module

public import Mathlib
public import Development.WeilBound.CoreStatements.HodgeTatePoints.GfForms
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0033
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.EmbEquivSymmApply
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.CommGroupMulMulEqMulInvMulMulMul
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0034

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.AevalZeroOfMem
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo PositivityTheory.HtPt
open GroundTheory.Heights₂.Heights.CoordinateConeArithVar

namespace LevelTowerAlt

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem aeval_zero_of_mem {Ω : Type} [Field Ω] {x : (Σ k, J k) → Ω} {f : MRing J} (hf : f ∈ mCoordIdeal x) :
    aeval x f = 0 := by
  have h0 : mConeMap x f = 0 := hf
  have e : ((MvPolynomial.eval fun _ : K => (1 : Ω)).comp (mConeMap x).toRingHom) =
      (aeval x : MRing J →ₐ[ℤ] Ω).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro p
      simp [mConeMap]
  have h1 : (aeval x : MRing J →ₐ[ℤ] Ω) f = (MvPolynomial.eval fun _ : K => (1 : Ω)) ((mConeMap x) f) :=
    (congrArg (fun g => g f) e).symm
  rw [h1, h0, map_zero]

theorem hom_X (p : Σ k, J k) : ∃ d, IsMultiHomog (X p : MRing J) d := by
  classical
  exact ⟨_, (Gf.hom_iff _ _).2 (isWeightedHomogeneous_X ℤ _ p)⟩

theorem exists_homog (c : ∀ k, J k) (f : MRing J) : ∃ (d : K → ℕ) (h : MRing J), IsMultiHomog h d ∧
    ∀ (Ω : Type) [Field Ω] (z : (Σ k, J k) → Ω), (∀ k, z ⟨k, c k⟩ = 1) → aeval z h = aeval z f := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, (Gf.hom_iff _ _).2 (isWeightedHomogeneous_C _ _), fun _ _ _ _ => rfl⟩
  | add f g hf hg =>
    obtain ⟨d, h, hh, e⟩ := hf
    obtain ⟨d', h', hh', e'⟩ := hg
    refine ⟨d + d', h * Gf.mon c d' + Gf.mon c d * h',
      Gf.hom_add (Gf.hom_mul hh (Gf.hom_mon c d')) (Gf.hom_mul (Gf.hom_mon c d) hh'), fun Ω _ z hz => ?_⟩
    simp only [map_add (f := _), map_mul, Gf.aeval_mon, hz, one_pow, Finset.prod_const_one, mul_one, one_mul, e Ω z hz,
      e' Ω z hz]
  | mul_X f p hf =>
    obtain ⟨d, h, hh, e⟩ := hf
    obtain ⟨d', h'⟩ := hom_X p
    exact ⟨_, h * X p, Gf.hom_mul hh h', fun Ω _ z hz => by rw [map_mul, map_mul, e Ω z hz]⟩

theorem le_mCoordIdeal {Ω : Type} [Field Ω] {P : Ideal (MRing J)} (hP : IsMultiHomogIdeal P) {w : (Σ k, J k) → Ω}
    (h : ∀ g ∈ P, aeval w g = 0) : P ≤ mCoordIdeal w := by
  obtain ⟨S, hS, rfl⟩ := hP
  refine Ideal.span_le.2 fun g hg => ?_
  obtain ⟨d, hd⟩ := hS g hg
  exact Gf.mem_mCoordIdeal hd (h g (Ideal.subset_span hg))

theorem aeval_hom {A B : Type} [CommRing A] [CommRing B] (σ : A →+* B) (z : (Σ k, J k) → A) (g : MRing J) :
    σ (aeval z g) = aeval (fun p => σ (z p)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p q hp => simp [hp]

theorem hom_eq_aeval {B : Type} [CommRing B] (F : MRing J →+* B) (z : (Σ k, J k) → B) (h : ∀ p, F (X p) = z p)
    (g : MRing J) : F g = aeval z g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p q hp => simp [hp, h]

theorem exists_val {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {T : Type} [Finite T] (y : T → Ω)
    (h : ∃ x, y x ≠ 0) : ∃ x₀, y x₀ ≠ 0 ∧ ∀ x, y x / y x₀ ∈ A :=
  _root_.UpperTheory.Reformulated.B.Yla8.main A y h

variable {K' : Type} [Fintype K'] {J' : K' → Type} [∀ k, Fintype (J' k)]

theorem exists_lift_blk {Ω L : Type} [Field Ω] [Field L] (y' : (Σ k, J' k) → Ω) (bk : K → K')
    (bx : ∀ k, J k ≃ J' (bk k)) (hbk : Function.Injective bk) (hy' : ∀ k, ∃ x, y' ⟨k, x⟩ ≠ 0)
    (w : (Σ k, J k) → L) (c : ∀ k, J k) (hc : ∀ k, w ⟨k, c k⟩ = 1)
    (hle : mCoordIdeal (fun p : Σ k, J k => y' ⟨bk p.1, bx p.1 p.2⟩) ≤ mCoordIdeal w) :
    ∃ (k₀ L₁ : Type) (_ : Field k₀) (_ : Field L₁) (σ : k₀ →+* L) (_ : Algebra k₀ L₁) (_ : Module.Finite k₀ L₁)
      (w₀ : (Σ k, J k) → k₀) (w' : (Σ k, J' k) → L₁), (∀ p, σ (w₀ p) = w p) ∧
      (∀ p : Σ k, J k, w' ⟨bk p.1, bx p.1 p.2⟩ = algebraMap k₀ L₁ (w₀ p)) ∧ (∀ k, ∃ x, w' ⟨k, x⟩ ≠ 0) ∧
      mCoordIdeal y' ≤ mCoordIdeal w' := by
  classical
  set z : (Σ k, J k) → Ω := fun p => y' ⟨bk p.1, bx p.1 p.2⟩ with hz
  have hzc : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k h0 => by
    obtain ⟨d, hd⟩ := hom_X (J := J) ⟨k, c k⟩
    have := aeval_zero_of_mem (hle (Gf.mem_mCoordIdeal hd (by rw [aeval_X, h0])))
    rw [aeval_X, hc] at this
    exact one_ne_zero this
  let φ : MRing J →+* Ω := (aeval (ratioPt z c) : MRing J →ₐ[ℤ] Ω)
  let ψ : MRing J →+* L := (aeval w : MRing J →ₐ[ℤ] L)
  have hker : ∀ f, φ f = 0 → ψ f = 0 := fun f hf => by
    obtain ⟨d, h, hh, e⟩ := exists_homog c f
    have h1 : aeval (ratioPt z c) h = 0 := (e Ω _ fun k => div_self (hzc k)).trans hf
    have h2 := Gf.mem_mCoordIdeal hh h1
    rw [← mCoordIdeal_ratioPt z c hzc] at h2
    exact (e L w hc).symm.trans (aeval_zero_of_mem (hle h2))
  let q : Ideal (MRing J) := RingHom.ker ψ
  have : q.IsPrime := RingHom.ker_isPrime ψ
  have hu : ∀ s : q.primeCompl, IsUnit (φ s) := fun s => IsUnit.mk0 _ fun h => s.2 (hker _ h)
  let f : Localization.AtPrime q →+* Ω := IsLocalization.lift hu
  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  have hf : ∀ g, f (algebraMap _ _ g) = φ g := fun g => IsLocalization.lift_eq hu g
  have hφA : ∀ g, φ g ∈ A := fun g => hf g ▸ hA _
  let φA : MRing J →+* A := φ.codRestrict A.toSubring hφA
  have hφA' : ∀ g, φA g = f.codRestrict A.toSubring hA (algebraMap _ _ g) := fun g => Subtype.ext (hf g).symm
  let θ : MRing J →+* IsLocalRing.ResidueField A := (IsLocalRing.residue A).comp φA
  have hθ : ∀ g, θ g = 0 ↔ g ∈ q := fun g => by
    change IsLocalRing.residue A (φA g) = 0 ↔ _
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hφA']
    have h1 : IsUnit (f.codRestrict A.toSubring hA (algebraMap _ _ g)) ↔
        IsUnit (algebraMap _ (Localization.AtPrime q) g) := ⟨fun h => hloc.1 _ h, fun h => h.map _⟩
    refine (not_congr h1).trans ?_
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q) q g]
    exact not_not
  let τ : q.ResidueField →+* IsLocalRing.ResidueField A := Ideal.ResidueField.lift q θ
    (fun g hg => (hθ g).2 hg) fun g hg => IsUnit.mk0 _ fun h => hg ((hθ g).1 h)
  let σ : q.ResidueField →+* L := Ideal.ResidueField.lift q ψ le_rfl fun g hg => IsUnit.mk0 _ hg
  have hch : ∀ k', ∃ x₀ : J' k', y' ⟨k', x₀⟩ ≠ 0 ∧ (∀ x, y' ⟨k', x⟩ / y' ⟨k', x₀⟩ ∈ A) ∧
      ∀ k, bk k = k' → y' ⟨k', x₀⟩ = z ⟨k, c k⟩ := by
    intro k'
    by_cases hk : k' ∈ Set.range bk
    · obtain ⟨k, rfl⟩ := hk
      refine ⟨bx k (c k), hzc k, fun x => ?_, fun k₁ h => ?_⟩
      · have := hφA (X ⟨k, (bx k).symm x⟩)
        simpa [φ, ratioPt, hz] using this
      · obtain rfl := hbk h
        rfl
    · obtain ⟨x₀, h1, h2⟩ := exists_val A (fun x => y' ⟨k', x⟩) (hy' k')
      exact ⟨x₀, h1, h2, fun k h => absurd ⟨k, h⟩ hk⟩
  choose c' hc'0 hc'A hc'z using hch
  let u : (Σ k, J' k) → A := fun p => ⟨ratioPt y' c' p, hc'A p.1 p.2⟩
  let ub : (Σ k, J' k) → IsLocalRing.ResidueField A := fun p => IsLocalRing.residue A (u p)
  let E : MvPolynomial (Σ k, J' k) q.ResidueField →+* IsLocalRing.ResidueField A := eval₂Hom τ ub
  obtain ⟨m, hm, hEm⟩ := Ideal.exists_le_maximal (RingHom.ker E) (RingHom.ker_ne_top E)
  let _ : Field (MvPolynomial (Σ k, J' k) q.ResidueField ⧸ m) := Ideal.Quotient.field m
  refine ⟨q.ResidueField, MvPolynomial (Σ k, J' k) q.ResidueField ⧸ m, inferInstance, inferInstance, σ, inferInstance,
    finite_of_finite_type_of_isJacobsonRing _ _, fun p => algebraMap _ _ (X p : MRing J),
    fun p => Ideal.Quotient.mk m (X p), fun p => ?_, fun p => ?_, fun k => ⟨c' k, ?_⟩, ?_⟩
  · exact (Ideal.ResidueField.lift_algebraMap q ψ _ _ (X p)).trans (aeval_X _ _)
  · change Ideal.Quotient.mk m _ = Ideal.Quotient.mk m (C _)
    rw [Ideal.Quotient.eq]
    refine hEm ?_
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    simp only [E, coe_eval₂Hom, eval₂_X, eval₂_C]
    refine Eq.trans ?_ (Ideal.ResidueField.lift_algebraMap q θ _ _ (X p)).symm
    change IsLocalRing.residue A _ = IsLocalRing.residue A _
    congr 1
    apply Subtype.ext
    change y' _ / y' ⟨bk p.1, c' (bk p.1)⟩ = φ (X p)
    rw [hc'z _ p.1 rfl]
    simp [φ, ratioPt, hz]
  · have h1 : Ideal.Quotient.mk m (X ⟨k, c' k⟩) = Ideal.Quotient.mk m 1 := by
      rw [Ideal.Quotient.eq]
      refine hEm ?_
      rw [RingHom.mem_ker, map_sub, sub_eq_zero, map_one]
      simp only [E, coe_eval₂Hom, eval₂_X]
      have : u ⟨k, c' k⟩ = 1 := Subtype.ext (div_self (hc'0 k))
      simp only [ub, this, map_one]
    intro h0
    exact one_ne_zero ((map_one _).symm.trans (h1.symm.trans h0))
  · refine le_mCoordIdeal (isMultiHomogIdeal y') fun g hg => ?_
    rw [mCoordIdeal_ratioPt y' c' hc'0] at hg
    have h1 : aeval u g = 0 := by
      apply Subtype.ext
      exact (aeval_hom A.subtype u g).trans (aeval_zero_of_mem hg)
    have h3 : IsLocalRing.residue A (aeval u g) = 0 := by rw [h1, map_zero]
    have h4 := hom_eq_aeval (E.comp (MvPolynomial.map (Int.castRingHom q.ResidueField))) ub
      (fun p => by simp only [RingHom.comp_apply, map_X, E, coe_eval₂Hom, eval₂_X]) g
    have h2 : E (MvPolynomial.map (Int.castRingHom q.ResidueField) g) = 0 :=
      h4.trans ((aeval_hom (IsLocalRing.residue A) u g).symm.trans h3)
    have h5 := hom_eq_aeval ((Ideal.Quotient.mk m).comp (MvPolynomial.map (Int.castRingHom q.ResidueField)))
      (fun p => Ideal.Quotient.mk m (X p)) (fun p => by simp only [RingHom.comp_apply, map_X]) g
    exact h5.symm.trans (Ideal.Quotient.eq_zero_iff_mem.2 (hEm h2))

end LevelTowerAlt
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.EigenProjectionConjugateInner
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace LevelTowerAlt

theorem eigen_projection_conjugate_inner : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (I : Submodule (𝓞 E) Λ), IsIsoSub R.form I → ∀ s : 𝓞 E →+* ℂ, (∀ v ∈ I, ∀ w ∈ I, R.ip (eigComp R.B ((starRingEnd ℂ).comp s) (R.P v)) (eigComp R.B ((starRingEnd ℂ).comp s) (R.P w)) = starRingEnd ℂ (R.ip (eigComp R.B s (R.P v)) (eigComp R.B s (R.P w)))) ∧ ∀ (r : ℕ) (v : Fin r → Λ), (∀ a, v a ∈ I) → LinearIndependent (𝓞 E) v → LinearIndependent ℂ fun a => eigComp R.B s (R.P (v a)) := by
  intro E _ _ _ g Λ _ _ Ψ _ R I hI s
  simp only [LevelTowerAlt.eigComp_eq]
  exact ⟨fun v hv w hw => gram_conj R hI s hv hw, fun r v hv hli => proj_indep R hI s hv hli⟩

end LevelTowerAlt
end
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.IsotropicQuotientLattice
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace LevelTowerAlt

section

open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
  (R : RiemLat E g Λ)

theorem exists_compl (W : Submodule ℂ (Fin g → ℂ)) :
    ∃ (g' : ℕ) (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (j : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      (∀ z, q (j z) = z) ∧ LinearMap.ker q = W ∧ (∀ w ∈ W, ∀ z, R.ip w (j z) = 0) ∧ g' + Module.finrank ℂ W = g := by
  let b := Module.finBasis ℂ W
  let L : (Fin g → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) := LinearMap.pi fun a => ipR R (b a)
  have hL : ∀ w ∈ W, ∀ x ∈ LinearMap.ker L, R.ip w x = 0 := fun w hw x hx => by
    have h1 := congrArg Subtype.val (b.sum_repr ⟨w, hw⟩)
    rw [Submodule.coe_sum] at h1
    have h2 : ∑ a, b.repr ⟨w, hw⟩ a • (b a : Fin g → ℂ) = w := h1
    rw [← h2, ip_sum_left]
    refine Finset.sum_eq_zero fun a _ => ?_
    have h3 : R.ip (b a) x = 0 := congrFun (LinearMap.mem_ker.1 hx) a
    rw [ip_smul_left, h3, mul_zero]
  have hd : Disjoint (LinearMap.ker L) W := Submodule.disjoint_def.2 fun x hx hw =>
    eq_zero_of_re R (by rw [hL x hw x hx, Complex.zero_re])
  have hc : IsCompl (LinearMap.ker L) W := ⟨hd, codisjoint_iff.2 (Submodule.eq_top_of_disjoint _ _ (by
    have h1 := L.finrank_range_add_finrank_ker
    have h2 := (LinearMap.range L).finrank_le
    rw [Module.finrank_fin_fun] at h2
    omega) hd)⟩
  let ψ := (Module.finBasis ℂ (LinearMap.ker L)).equivFun
  refine ⟨_, ψ.toLinearMap ∘ₗ (LinearMap.ker L).projectionOnto W hc, (LinearMap.ker L).subtype ∘ₗ ψ.symm.toLinearMap,
    fun z => ?_, ?_, fun w hw z => hL w hw _ (ψ.symm z).2, ?_⟩
  · show ψ ((LinearMap.ker L).projectionOnto W hc (ψ.symm z)) = z
    rw [Submodule.projectionOnto_apply_left, ψ.apply_symm_apply]
  · rw [LinearEquiv.ker_comp, Submodule.ker_projectionOnto]
  · rw [Submodule.finrank_add_eq_of_isCompl hc, Module.finrank_fin_fun]

variable {I : Submodule (𝓞 E) Λ}

theorem imB_span {z : Fin g → ℂ} (h : ∀ v ∈ I, imB R (R.P v) z = 0) {u : Fin g → ℂ}
    (hu : u ∈ Submodule.span ℝ (R.P '' I)) : imB R u z = 0 := by
  have h1 : Submodule.span ℝ (R.P '' I) ≤ LinearMap.ker ((imB R).flip z) :=
    Submodule.span_le.2 (by rintro _ ⟨v, hv, rfl⟩; exact h v hv)
  exact h1 hu

theorem imB_iso (hI : IsIsoSub R.form I) {u u' : Fin g → ℂ} (hu : u ∈ Submodule.span ℝ (R.P '' I))
    (hu' : u' ∈ Submodule.span ℝ (R.P '' I)) : imB R u u' = 0 := by
  refine imB_span R (fun v hv => ?_) hu
  have h1 : Submodule.span ℝ (R.P '' I) ≤ LinearMap.ker (imB R (R.P v)) :=
    Submodule.span_le.2 (by
      rintro _ ⟨w, hw, rfl⟩
      show imB R (R.P v) (R.P w) = 0
      rw [imB_P, hI w hw v hv, Int.cast_zero])
  exact h1 hu'

theorem im_part_zero (hI : IsIsoSub R.form I) {u u' : Fin g → ℂ} (hu : u ∈ Submodule.span ℝ (R.P '' I))
    (hu' : u' ∈ Submodule.span ℝ (R.P '' I)) (h : imB R u' (u + Complex.I • u') = 0) : u' = 0 := by
  rw [map_add (f := _), imB_iso R hI hu' hu, zero_add, imB_apply, ip_smul_right, Complex.I_mul_im] at h
  exact eq_zero_of_re R h

theorem span_split {T : Set (Fin g → ℂ)} {w : Fin g → ℂ} (hw : w ∈ Submodule.span ℂ T) :
    ∃ u ∈ Submodule.span ℝ T, ∃ u' ∈ Submodule.span ℝ T, w = u + Complex.I • u' :=
  _root_.UpperTheory.Reformulated.B.Yhc5.main hw

theorem complex_indep (hI : IsIsoSub R.form I) {k : ℕ} {i : Fin k → Λ} (hi : ∀ b, i b ∈ I)
    (hli : LinearIndependent ℤ i) : LinearIndependent ℂ fun b => R.P (i b) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hm : ∀ r : Fin k → ℝ, ∑ b, r b • R.P (i b) ∈ Submodule.span ℝ (R.P '' I) := fun r =>
    Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i b, hi b, rfl⟩)
  have h1 : ∑ b, (c b).re • R.P (i b) + Complex.I • ∑ b, (c b).im • R.P (i b) = 0 := by
    rw [← hc, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul, mul_comm, Complex.re_add_im]
  have h2 := im_part_zero R hI (hm fun b => (c b).re) (hm fun b => (c b).im) (by rw [h1, map_zero])
  rw [h2, smul_zero, add_zero] at h1
  have h3 := Fintype.linearIndependent_iff.1 (real_indep R hli)
  exact fun b => Complex.ext (h3 _ h1 b) (h3 _ h2 b)

theorem dot_pull {g' : ℕ} (j : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (z z' : Fin g' → ℂ) :
    z ⬝ᵥ (Matrix.of fun a b => R.ip (j fun c => if b = c then 1 else 0) (j fun c => if a = c then 1 else 0)) *ᵥ
      star z' = R.ip (j z') (j z) := by
  rw [LinearMap.pi_apply_eq_sum_univ j z, LinearMap.pi_apply_eq_sum_univ j z', ip_sum_right]
  simp only [dotProduct, mulVec, Matrix.of_apply, ip_smul_right, ip_sum_left, ip_smul_left, Pi.star_apply,
    Complex.star_def, mul_comm]

end

theorem isotropic_quotient_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (I : Submodule (𝓞 E) Λ), IsSaturated I → IsIsoSub R.form I → ∃ (g' : ℕ) (Λ' : Type) (_ : AddCommGroup Λ') (_ : Module (𝓞 E) Λ') (R' : RiemLat E g' Λ') (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), Function.Surjective q ∧ LinearMap.ker q = Submodule.span ℂ (R.P '' I) ∧ (∀ a x, q (R.B a x) = R'.B a (q x)) ∧ Set.range R'.P = q '' (R.P '' {x | ∀ y ∈ I, R.form x y = 0}) ∧ ∀ x y, (∀ v ∈ I, R.ip (R.P v) x = 0) → R'.ip (q x) (q y) = R.ip x y := by
  intro E _ _ _ g Λ _ _ Ψ _ R I hsat hI
  have := R.free
  have := R.fin
  obtain ⟨Λ', _, _, k, i, s, hli, hi, hsp, hfree, hfin, hrk, hs1, hs2, hs3, hbij⟩ :=
    exists_quot R.unimod R.alt hsat hI fun a => ⟨_, R.adj a _ (IsCMField.coe_ringOfIntegersComplexConj E a)⟩
  obtain ⟨g', q, j, hqj, hker, horth, hg⟩ := exists_compl R (Submodule.span ℂ (R.P '' I))
  have hW : Submodule.span ℂ (R.P '' I) = Submodule.span ℂ (Set.range fun b => R.P (i b)) := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨c, rfl⟩ := hsp x hx
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Submodule.sum_mem _ fun b _ => ?_
      rw [map_zsmul]
      have h : R.P (i b) ∈ Submodule.span ℂ (Set.range fun b => R.P (i b)) := Submodule.subset_span ⟨b, rfl⟩
      exact zsmul_mem h _
    · rintro _ ⟨b, rfl⟩
      exact ⟨i b, hi b, rfl⟩
  have hk : Module.finrank ℂ (Submodule.span ℂ (R.P '' I)) = k := by
    rw [hW, finrank_span_eq_card (complex_indep R hI hi hli), Fintype.card_fin]
  have hmem : ∀ x, x ∈ Submodule.span ℂ (R.P '' I) ↔ q x = 0 := fun x => by rw [← hker, LinearMap.mem_ker]
  have hsub : ∀ x, x - j (q x) ∈ Submodule.span ℂ (R.P '' I) := fun x => by
    rw [hmem, map_sub, hqj, sub_self]
  have hstab : ∀ a, Submodule.span ℂ (R.P '' I) ≤ (Submodule.span ℂ (R.P '' I)).comap (R.B a) := fun a =>
    Submodule.span_le.2 (by
      rintro _ ⟨v, hv, rfl⟩
      exact Submodule.subset_span ⟨a • v, I.smul_mem a hv, R.act a v⟩)
  have hcomm : ∀ a x, q (R.B a (j (q x))) = q (R.B a x) := fun a x => by
    have h := (hmem _).1 (hstab a (hsub x))
    rw [map_sub, map_sub, sub_eq_zero] at h
    exact h.symm
  have hq : ∀ x x', x - x' ∈ I → q (R.P x) = q (R.P x') := fun x x' h => by
    rw [← sub_eq_zero, ← map_sub, ← map_sub, ← hmem]
    exact Submodule.subset_span ⟨_, h, rfl⟩
  have hSW : ∀ u ∈ Submodule.span ℝ (R.P '' I), u ∈ Submodule.span ℂ (R.P '' I) := fun u hu =>
    Submodule.span_le_restrictScalars ℝ ℂ _ hu
  have hS : ∀ x, (∀ y ∈ I, R.form x y = 0) → R.P x - j (q (R.P x)) ∈ Submodule.span ℝ (R.P '' I) := fun x hx => by
    obtain ⟨u, hu, u', hu', h⟩ := span_split (hsub (R.P x))
    have h1 : u' = 0 := im_part_zero R hI hu hu' (by
      rw [← h, map_sub, imB_span R (fun v hv => by rw [imB_P, hx v hv, Int.cast_zero]) hu', imB_apply,
        horth _ (hSW _ hu'), Complex.zero_im, sub_zero])
    rw [h, h1, smul_zero, add_zero]
    exact hu
  have horth' : ∀ w ∈ Submodule.span ℂ (R.P '' I), ∀ z, R.ip (j z) w = 0 := fun w hw z => by
    rw [← ip_conj, horth w hw, map_zero]
  have him : ∀ x y, (∀ v ∈ I, R.form x v = 0) → (∀ v ∈ I, R.form y v = 0) →
      imB R (j (q (R.P y))) (j (q (R.P x))) = R.form x y := fun x y hx hy => by
    have h1 := imB_iso R hI (hS y hy) (hS x hx)
    have h2 : imB R (R.P y - j (q (R.P y))) (j (q (R.P x))) = 0 := by
      rw [imB_apply, horth _ (hsub _), Complex.zero_im]
    have h3 : imB R (j (q (R.P y))) (R.P x - j (q (R.P x))) = 0 := by
      rw [imB_apply, horth' _ (hsub _), Complex.zero_im]
    rw [← imB_P]
    simp only [map_sub, LinearMap.sub_apply] at h1 h2 h3
    linarith
  have hfr : ∀ x y y', (∀ v ∈ I, R.form x v = 0) → y - y' ∈ I → R.form x y = R.form x y' := fun x y y' hx h => by
    rw [← sub_eq_zero, ← map_sub, hx _ h]
  have skew : ∀ x y, R.form x y = -R.form y x := fun x y => (LinearMap.IsAlt.neg R.alt y x).symm
  let B' : 𝓞 E →+* Module.End ℂ (Fin g' → ℂ) :=
    { toFun := fun a => q ∘ₗ R.B a ∘ₗ j
      map_one' := LinearMap.ext fun z => by
        show q (R.B 1 (j z)) = z
        rw [map_one, Module.End.one_apply, hqj]
      map_mul' := fun a b => LinearMap.ext fun z => by
        show q (R.B (a * b) (j z)) = q (R.B a (j (q (R.B b (j z)))))
        rw [hcomm, map_mul, Module.End.mul_apply]
      map_zero' := LinearMap.ext fun z => by
        show q (R.B 0 (j z)) = 0
        rw [map_zero, LinearMap.zero_apply, map_zero]
      map_add' := fun a b => LinearMap.ext fun z => by
        show q (R.B (a + b) (j z)) = q (R.B a (j z)) + q (R.B b (j z))
        rw [map_add (f := _), LinearMap.add_apply, map_add (f := _)] }
  let R' : RiemLat E g' Λ' :=
    { free := hfree
      fin := hfin
      rank := by
        have h := R.rank
        omega
      form := R.form.compl₁₂ s s
      alt := fun z => R.alt (s z)
      unimod := hbij
      adj := fun a a' h x y => by
        show R.form (s (a • x)) (s y) = R.form (s x) (s (a' • y))
        rw [hfr _ _ _ (hs1 x) (hs3 a' y), ← R.adj a a' h, skew, hfr _ _ _ (hs1 y) (hs3 a x), ← skew]
      P := q.toAddMonoidHom.comp (R.P.comp s.toAddMonoidHom)
      Hm := Matrix.of fun a b => R.ip (j fun c => if b = c then 1 else 0) (j fun c => if a = c then 1 else 0)
      herm := by
        ext a b
        exact ip_conj R _ _
      pos := fun z hz => by
        rw [dot_pull]
        exact R.pos (j z) fun h => hz (by rw [← hqj z, h, map_zero])
      im := fun x y => by
        rw [dot_pull]
        exact him _ _ (hs1 x) (hs1 y)
      B := B'
      act := fun a z => by
        show q (R.P (s (a • z))) = q (R.B a (j (q (R.P (s z)))))
        rw [hcomm, ← R.act, hq _ _ (hs3 a z)] }
  refine ⟨g', Λ', inferInstance, inferInstance, R', q, fun z => ⟨j z, hqj z⟩, hker, fun a x => (hcomm a x).symm, ?_,
    fun x y hx => ?_⟩
  · ext w
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨_, ⟨s z, hs1 z, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      obtain ⟨z, hz⟩ := hs2 x hx
      exact ⟨z, hq _ _ hz⟩
  · have h1 : ∀ w ∈ Submodule.span ℂ (R.P '' I), R.ip x w = 0 := fun w hw => by
      have h : Submodule.span ℂ (R.P '' I) ≤ LinearMap.ker (ipR R x) := Submodule.span_le.2 (by
        rintro _ ⟨v, hv, rfl⟩
        show R.ip x (R.P v) = 0
        rw [← ip_conj, hx v hv, map_zero])
      exact h hw
    have h2 : x - j (q x) = 0 := by
      apply eq_zero_of_re R
      have h : R.ip (x - j (q x)) (x - j (q x)) = R.ip (x - j (q x)) x - R.ip (x - j (q x)) (j (q x)) :=
        map_sub (ipR R _) _ _
      rw [h, horth _ (hsub x), ← ip_conj R x, h1 _ (hsub x), map_zero, sub_zero, Complex.zero_re]
    refine (dot_pull R j (q y) (q x)).trans ?_
    have h3 : R.ip x y - R.ip x (j (q y)) = 0 := (map_sub (ipR R x) _ _).symm.trans (h1 _ (hsub y))
    rw [← sub_eq_zero.1 h2, sub_eq_zero.1 h3]

end LevelTowerAlt
end
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.RiemannLatticeEigenProjections
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace LevelTowerAlt

theorem riemann_lattice_eigen_projections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ), Function.Injective R.P ∧ Submodule.span ℝ (Set.range R.P) = ⊤ ∧ (∀ s : 𝓞 E →+* ℂ, (∀ x, eigComp R.B s x ∈ eigSp R.B s) ∧ (∀ x ∈ eigSp R.B s, eigComp R.B s x = x) ∧ (∀ (c : ℂ) x y, eigComp R.B s (c • x + y) = c • eigComp R.B s x + eigComp R.B s y) ∧ ∀ a x, eigComp R.B s (R.B a x) = s a • eigComp R.B s x) ∧ (∀ x, ∑ s : E →+* ℂ, eigComp R.B (s.comp (algebraMap (𝓞 E) E)) x = x) ∧ ∀ s s' : 𝓞 E →+* ℂ, s ≠ s' → ∀ x ∈ eigSp R.B s, ∀ y ∈ eigSp R.B s', R.ip x y = 0 := by
  intro E _ _ _ g Λ _ _ Ψ _ R
  refine ⟨LevelTowerAlt.precomp_injective R, LevelTowerAlt.span_top R,
    fun s => ⟨fun x => ?_, fun x hx => ?_, fun c x y => ?_, fun a x => ?_⟩, fun x => ?_,
    fun s s' hss' x hx y hy => LevelTowerAlt.ip_orth R hss' hx hy⟩
  · rw [LevelTowerAlt.eigComp_eq]
    exact LevelTowerAlt.proj_mem _ _ _
  · rw [LevelTowerAlt.eigComp_eq]
    exact LevelTowerAlt.proj_eig_self hx
  · simp only [LevelTowerAlt.eigComp_eq, map_add (f := _), map_smul]
  · simp only [LevelTowerAlt.eigComp_eq]
    exact LevelTowerAlt.proj_act _ _ _ _
  · simp only [LevelTowerAlt.eigComp_eq]
    conv_rhs => rw [← LevelTowerAlt.sum_proj R.B x]
    exact Fintype.sum_equiv (LevelTowerAlt.embEquiv E) _ _ (fun _ => rfl)

end LevelTowerAlt
end
end

