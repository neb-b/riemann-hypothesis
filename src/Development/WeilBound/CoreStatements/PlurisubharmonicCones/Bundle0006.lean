module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.HolomorphicFamilySmoothHermitian
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeGramDeterminant
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0004
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0001
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PBlockRatioAlg
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0047

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.CuspsLocallyFiniteFamily
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace LevelTowerAlt.LocFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

noncomputable def rg (R : RiemLat E g Λ) {N : ℕ} (e : Fin N → Λ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun k l => (R.ip (R.P (e k)) (R.P (e l))).re

theorem conj_ip (R : RiemLat E g Λ) (x y : Fin g → ℂ) : star (R.ip y x) = R.ip x y := by
  show star (x ⬝ᵥ R.Hm *ᵥ star y) = y ⬝ᵥ R.Hm *ᵥ star x
  rw [← star_dotProduct_star, star_mulVec, star_star, R.herm.eq, dotProduct_mulVec]

theorem rg_symm (R : RiemLat E g Λ) {N : ℕ} (e : Fin N → Λ) : (rg R e)ᵀ = rg R e := by
  ext k l
  simp only [rg, transpose_apply, of_apply]
  rw [← conj_ip R (R.P (e l)) (R.P (e k))]
  simp

theorem ip_sum (R : RiemLat E g Λ) {N : ℕ} (u : Fin N → Fin g → ℂ) (x y : Fin N → ℝ) :
    (R.ip (∑ k, (x k : ℂ) • u k) (∑ l, (y l : ℂ) • u l)).re = ∑ k, ∑ l, x k * (R.ip (u k) (u l)).re * y l := by
  have : R.ip (∑ k, (x k : ℂ) • u k) (∑ l, (y l : ℂ) • u l) =
      ∑ k, ∑ l, (x k : ℂ) * R.ip (u k) (u l) * (y l : ℂ) := by
    unfold RiemLat.ip
    rw [star_sum, mulVec_sum, dotProduct_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sum_dotProduct]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    rw [show star (x k : ℂ) = (x k : ℂ) from Complex.conj_ofReal _]
    ring
  rw [this, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp

theorem rg_pos (R : RiemLat E g Λ) {N : ℕ} (e : Module.Basis (Fin N) ℤ Λ) (x : Fin N → ℝ) (hx : x ≠ 0) :
    0 < x ⬝ᵥ rg R e *ᵥ x := by
  have h1 : x ⬝ᵥ rg R e *ᵥ x =
      (R.ip (∑ k, (x k : ℂ) • R.P (e k)) (∑ l, (x l : ℂ) • R.P (e l))).re := by
    rw [ip_sum]
    simp only [dotProduct, mulVec, rg, of_apply, Finset.mul_sum, mul_assoc]
  rw [h1]
  refine R.pos _ fun h0 => hx ?_
  funext k
  obtain ⟨w, hw⟩ := R.unimod.2 (e.coord k)
  have h2 : ∀ l, R.form (e l) w = -(if l = k then 1 else 0) := by
    intro l
    have ha := R.alt (e l + w)
    simp only [map_add (f := _), LinearMap.add_apply, R.alt] at ha
    have hb : R.form w (e l) = if l = k then 1 else 0 := by
      rw [hw]; simp [Finsupp.single_apply]
    linarith
  have h3 : ((∑ l, (x l : ℂ) • R.P (e l)) ⬝ᵥ R.Hm *ᵥ star (R.P w)).im = ∑ l, x l * (R.form (e l) w : ℝ) := by
    rw [sum_dotProduct, Complex.im_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_dotProduct, smul_eq_mul, Complex.im_ofReal_mul, R.im]
  rw [h0] at h3
  simp only [h2] at h3
  simpa using h3

theorem rg_coords (R : RiemLat E g Λ) {N m : ℕ} (e : Module.Basis (Fin N) ℤ Λ) (v : Fin m → Λ) :
    rg R v = (coords e v).map (Int.castRingHom ℝ) * rg R e * ((coords e v).map (Int.castRingHom ℝ))ᵀ := by
  have h : ∀ i, R.P (v i) = ∑ k, (((e.repr (v i) k : ℤ) : ℝ) : ℂ) • R.P (e k) := by
    intro i
    conv_lhs => rw [← e.sum_repr (v i)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, Complex.ofReal_intCast, Int.cast_smul_eq_zsmul]
  ext i j
  have : rg R v i j = ∑ k, ∑ l, ((e.repr (v i) k : ℤ) : ℝ) * (R.ip (R.P (e k)) (R.P (e l))).re *
      ((e.repr (v j) l : ℤ) : ℝ) := by
    rw [← ip_sum, ← h, ← h]
    rfl
  rw [this, Finset.sum_comm]
  simp only [Matrix.mul_apply, Finset.sum_mul, map_apply, transpose_apply, coords, rg, of_apply, eq_intCast]

end LevelTowerAlt.LocFin

open LevelTowerAlt.LocFin in
theorem LevelTowerAlt.cusps_locally_finite_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ), IsOpen U → IsHolFam U R → IsCMFam σ → (∀ t ∈ U, (R t).HasRank σ m) → ∀ t₀ ∈ U, ∃ (ε : ℝ) (F : Finset (Submodule (𝓞 E) Λ)), 0 < ε ∧ ∀ t ∈ U ∩ Metric.ball t₀ ε, (∀ I ∈ F, (R t).IsCusp I) ∧ ∀ I, (R t).IsCusp I → (R t).nz σ I ≤ 1 → I ∈ F := by
  intro E _ _ _ g Λ _ _ Ψ _ n U R σ m hU hHol hCM _ t₀ ht₀
  classical
  haveI := (R t₀).free
  haveI := (R t₀).fin
  let e := Module.finBasis ℤ Λ
  have hHm : ∀ i j, ContinuousOn (fun t => (R t).Hm i j) U := by
    intro i j
    obtain ⟨h1, h2⟩ := (_root_.LevelTowerAlt.holomorphic_family_smooth_hermitian E g Λ Ψ n U R hU hHol).1 i j
    have e : (fun t => (R t).Hm i j) = fun t => (((R t).Hm i j).re : ℂ) + (((R t).Hm i j).im : ℂ) * Complex.I := by
      funext t; exact (Complex.re_add_im _).symm
    rw [e]
    exact (Complex.continuous_ofReal.comp_continuousOn h1.continuousOn).add
      ((Complex.continuous_ofReal.comp_continuousOn h2.continuousOn).mul continuousOn_const)
  have hip : ∀ x y, ContinuousOn (fun t => (R t).ip ((R t).P x) ((R t).P y)) U := by
    intro x y
    unfold RiemLat.ip
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
    refine continuousOn_finsetSum _ fun i _ => ((continuousOn_pi.1 (hHol.2 y).continuousOn i)).mul ?_
    refine continuousOn_finsetSum _ fun j _ => (hHm i j).mul ?_
    exact (continuous_star.comp_continuousOn (continuousOn_pi.1 (hHol.2 x).continuousOn j))
  have hS : ContinuousOn (fun t => rg (R t) e) U :=
    continuousOn_pi.2 fun k => continuousOn_pi.2 fun l =>
      Complex.continuous_re.comp_continuousOn (hip (e k) (e l))
  obtain ⟨c, hc, hev⟩ := unif_pos (rg (R t₀) e) (rg_pos (R t₀) e)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
    ((hS.continuousAt (hU.mem_nhds ht₀)).eventually hev)
  obtain ⟨Dk, hDk⟩ : ∃ Dk : ℝ, Dk = |(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ)) := ⟨_, rfl⟩
  have hD0 : 0 ≤ Dk := hDk ▸ Real.rpow_nonneg (abs_nonneg _) _
  have hfin := (finite_sat e ⌈(max 1 (Dk / c)) ^ Module.finrank ℤ Λ⌉).preimage
    (SetLike.coe_injective (A := Submodule (𝓞 E) Λ)).injOn
  have hcusp : ∀ t ∈ U, ∀ t' ∈ U, ∀ I, (R t).IsCusp I → (R t').IsCusp I := fun t ht t' ht' I h =>
    ⟨h.1, h.2.1, hHol.1 t ht t' ht' ▸ h.2.2⟩
  refine ⟨ε, hfin.toFinset.filter fun I => (R t₀).IsCusp I, hε, fun t ht =>
    ⟨fun I hI => hcusp t₀ ht₀ t ht.1 I (Finset.mem_filter.1 hI).2, fun I hI hnz => ?_⟩⟩
  refine Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ?_, hcusp t ht.1 t₀ ht₀ I hI⟩
  have hinj : Function.Injective (I.subtype.toAddMonoidHom.toIntLinearMap) := Subtype.val_injective
  haveI : Module.Finite ℤ I := Module.Finite.of_injective _ hinj
  haveI : Module.IsTorsionFree ℤ I := Function.Injective.moduleIsTorsionFree _ hinj (fun _ _ => map_smul _ _ _)
  haveI : Module.Free ℤ I := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ I
  have hli : LinearIndependent ℤ fun i => (b i : Λ) :=
    b.linearIndependent.map' (I.subtype.toAddMonoidHom.toIntLinearMap) (LinearMap.ker_eq_bot.2 hinj)
  obtain ⟨hm, hdet⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.IsoCovol.det_re_gram_eq E g Λ Ψ (R t) σ I hCM hI.2.2 hI.1 _ b
  obtain ⟨⟨r, v, hv⟩, hN⟩ := _root_.LevelTowerAlt.isotropic_submodule_nonzero_family E g Λ Ψ (R t) σ I hCM hI.2.2 hI.1
  have hnz0 := (hN r v hv).2.1
  obtain ⟨hd0, hd1⟩ := det_bound (coords e fun i => (b i : Λ)) (det_ne_zero e hli) (rg (R t) e)
    (rg_symm _ _) hc (hball t ht.2)
  rw [← rg_coords] at hd1
  have hle : Module.finrank ℤ I ≤ Module.finrank ℤ Λ := by
    simpa using hli.fintype_card_le_finrank
  refine ⟨_, fun i => (b i : Λ), fun x => ⟨fun hx => ⟨fun i => b.repr ⟨x, hx⟩ i, ?_⟩, ?_⟩,
    fun x k hk hx => hI.2.1 x k hk hx, hd0, ?_⟩
  · have := congrArg (I.subtype.toAddMonoidHom.toIntLinearMap) (b.sum_repr ⟨x, hx⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    simpa using this
  · rintro ⟨y, rfl⟩
    exact I.sum_mem fun i _ => zsmul_mem (b i).2 _
  · have h1 : (rg (R t) fun i => (b i : Λ)).det ≤ Dk ^ Module.finrank ℤ I := by
      refine hdet.le.trans ?_
      rw [← hDk, hm, mul_assoc, mul_comm 2, pow_mul Dk _ 2]
      have h0 : 0 ≤ Dk ^ (Fintype.card Ψ * Module.finrank (𝓞 E) I) := pow_nonneg hD0 _
      exact pow_le_pow_left₀ (mul_nonneg hnz0.le h0) (mul_le_of_le_one_left h0 hnz) 2
    have h2 : (((coords e fun i => (b i : Λ)) * (coords e fun i => (b i : Λ))ᵀ).det : ℝ) ≤
        (Dk / c) ^ Module.finrank ℤ I := by
      rw [div_pow, le_div_iff₀ (pow_pos hc _), mul_comm]
      exact hd1.trans h1
    have h3 : (Dk / c) ^ Module.finrank ℤ I ≤ (max 1 (Dk / c)) ^ Module.finrank ℤ Λ :=
      (pow_le_pow_left₀ (div_nonneg hD0 hc.le) (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) hle)
    exact_mod_cast (h2.trans h3).trans (Int.le_ceil _)
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsCurvePoint
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo PositivityTheory.HtPt GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.CoordinateConeArithVar

namespace LevelTowerAlt

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime]

theorem ker_red_le {W : Ideal (MRing J)} (hpW : (C (p : ℤ) : MRing J) ∈ W) :
    RingHom.ker (Bridge.GeoNum.red (ι := J) p) ≤ W := by
  classical
  rw [Bridge.GeoNum.ker_red, Ideal.span_le, Set.singleton_subset_iff]
  exact hpW

theorem map_red_prime [DecidableEq K] {W : Ideal (MRing J)} (hW : IsMultiProjPrime W)
    (hpW : (C (p : ℤ) : MRing J) ∈ W) : NumbersDVR.IsMultiProjPrime (W.map (Bridge.GeoNum.red p)) := by
  have hker := ker_red_le p hpW
  have hcm : (W.map (Bridge.GeoNum.red p)).comap (Bridge.GeoNum.red p) = W :=
    Bridge.GeoNum.comap_map_eq p hker
  have : W.IsPrime := hW.1
  refine ⟨Ideal.map_isPrime_of_surjective (Bridge.GeoNum.red_surjective p) hker, ?_, ?_⟩
  · rw [Bridge.isMultiHomogIdeal_iff]
    obtain ⟨S, hS, hWS⟩ := hW.2.1
    refine ⟨Bridge.GeoNum.red p '' S, ?_, by rw [hWS, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨b, hb⟩ := hS f hf
    exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
  · rw [← Bridge.GeoNum.isRelevant_comap_iff p, hcm]
    exact hW.2.2

theorem exists_curve_point {W : Ideal (MRing J)} (hW : IsMultiProjPrime W) (hpW : (C (p : ℤ) : MRing J) ∈ W)
    (hdim : ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra (ZMod p) L) (w : (Σ k, J k) → L) (c : ∀ k, J k),
      Algebra.trdeg (ZMod p) L = 1 ∧ (∀ k, w ⟨k, c k⟩ = 1) ∧ mCoordIdeal w = W := by
  classical
  obtain ⟨hQ, hQd⟩ := NefAddBlock.map_red p hW hpW 1 hdim
  have hcm := Bridge.GeoNum.comap_map_eq p (ker_red_le p hpW)
  set Q := W.map (Bridge.GeoNum.red p)
  have := hQ.isPrime
  obtain ⟨n, hn, hrn⟩ := FieldNumbers.FunctionFieldFinite.relDim_eq_trdeg FieldNumbers.MChartDehomog.proof
    (FieldNumbers.MChartTrdeg.proof FieldNumbers.MChartHomog.proof) Q hQ
  have hn1 : n = 1 := by
    rw [hQd] at hrn
    exact_mod_cast (WithTop.coe_injective (WithBot.coe_injective hrn)).symm
  choose c hc using hQ.relevant
  let π : NumbersDVR.MRing J (ZMod p) →+* FractionRing (NumbersDVR.MRing J (ZMod p) ⧸ Q) :=
    (algebraMap (NumbersDVR.MRing J (ZMod p) ⧸ Q) _).comp (Ideal.Quotient.mk Q)
  have hπ : ∀ g, π g = 0 ↔ g ∈ Q := fun g => by
    change algebraMap (NumbersDVR.MRing J (ZMod p) ⧸ Q) _ (Ideal.Quotient.mk Q g) = 0 ↔ _
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  let y₀ : (Σ k, J k) → FractionRing (NumbersDVR.MRing J (ZMod p) ⧸ Q) := fun x => π (X x)
  have hy₀ := hom_eq_aeval (π.comp (Bridge.GeoNum.red p)) y₀ fun x => by simp only [RingHom.comp_apply, map_X, y₀]
  have hyc : ∀ k, y₀ ⟨k, c k⟩ ≠ 0 := fun k h => hc k ((hπ _).1 h)
  have hW₀ : mCoordIdeal y₀ = W := by
    refine le_antisymm (fun g hg => ?_) (le_mCoordIdeal hW.2.1 fun g hg => ?_)
    · rw [← hcm]
      exact (hπ _).1 ((hy₀ g).trans (aeval_zero_of_mem hg))
    · exact (hy₀ g).symm.trans ((hπ _).2 (Ideal.mem_map_of_mem _ hg))
  have hmem : ∀ x, ratioPt y₀ c x ∈ FieldNumbers.homFracDegZero Q := fun x =>
    IntermediateField.subset_adjoin _ _ ⟨_, X x, X ⟨x.1, c x.1⟩, isWeightedHomogeneous_X _ _ x,
      isWeightedHomogeneous_X _ _ (⟨x.1, c x.1⟩ : Σ k, J k), hc x.1, rfl⟩
  refine ⟨FieldNumbers.homFracDegZero Q, inferInstance, inferInstance, fun x => ⟨_, hmem x⟩, c,
    by rw [hn, hn1, Nat.cast_one], fun k => Subtype.ext (div_self (hyc k)), ?_⟩
  rw [← hW₀, mCoordIdeal_ratioPt y₀ c hyc]
  exact (mCoordIdeal_comp (FieldNumbers.homFracDegZero Q).val.toRingHom fun x => ⟨_, hmem x⟩).symm

theorem dim_le {L : Type} [Field L] [Algebra (ZMod p) L] (hL : Algebra.trdeg (ZMod p) L ≤ 1) (w : (Σ k, J k) → L) :
    (C (p : ℤ) : MRing J) ∈ mCoordIdeal w ∧ ∃ m : ℕ, m ≤ 1 + Fintype.card K ∧
      ringKrullDim (NumbersDVR.MRing J (ZMod p) ⧸ (mCoordIdeal w).map (Bridge.GeoNum.red p)) = m := by
  classical
  let Φ : NumbersDVR.MRing J (ZMod p) →ₐ[ZMod p] MvPolynomial K L := aeval fun x => C (w x) * X x.1
  have hΦ : ∀ g : MRing J, mConeMap w g = Φ (Bridge.GeoNum.red p g) := fun g => by
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add f g hf hg => simp only [map_add (f := _), hf, hg]
    | mul_X f x hf => simp only [map_mul, hf, map_X]; simp [mConeMap, Φ]
  have hcm : mCoordIdeal w = (RingHom.ker Φ).comap (Bridge.GeoNum.red p) := by
    ext g
    rw [Ideal.mem_comap, RingHom.mem_ker, ← hΦ]
    rfl
  have hm : (mCoordIdeal w).map (Bridge.GeoNum.red p) = RingHom.ker Φ := by
    rw [hcm, Ideal.map_comap_of_surjective _ (Bridge.GeoNum.red_surjective p)]
  refine ⟨?_, ?_⟩
  · rw [hcm]
    refine Bridge.GeoNum.ker_le_comap p _ ?_
    rw [Bridge.GeoNum.ker_red]
    exact Ideal.mem_span_singleton_self _
  · rw [hm]
    have : (RingHom.ker Φ).IsPrime := RingHom.ker_isPrime _
    obtain ⟨m, h1, h2⟩ := GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg (k := ZMod p)
      (A := NumbersDVR.MRing J (ZMod p) ⧸ RingHom.ker Φ)
    refine ⟨m, ?_, h1⟩
    have h3 := trdeg_le_of_injective (Ideal.kerLiftAlg Φ) (Ideal.kerLiftAlg_injective Φ)
    rw [h2, ← trdeg_add_eq (ZMod p) L, MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype, Cardinal.lift_natCast] at h3
    have h4 : (m : Cardinal) ≤ 1 + (Fintype.card K : Cardinal) := h3.trans (by gcongr)
    exact_mod_cast h4

end LevelTowerAlt
end

