module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0050
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0049
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0057
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0051
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0054
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCoordArithOfFnField
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.CoordinateConeArithVar

noncomputable section

namespace CoordArithOfFnField

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ratioField_eq (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField y c = blockFnField y := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨p, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, c p.1⟩, rfl, rfl⟩
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨p, q, hpq, rfl⟩
    have hp : y p / y ⟨p.1, c p.1⟩ ∈ GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField y c :=
      IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩
    have hq : y q / y ⟨q.1, c q.1⟩ ∈ GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField y c :=
      IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩
    have he : y p / y q = (y p / y ⟨p.1, c p.1⟩) / (y q / y ⟨q.1, c q.1⟩) := by
      rw [← hpq, div_div_div_cancel_right₀ (hc p.1)]
    rw [he]
    exact div_mem hp hq

theorem dim_eq (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ringKrullDim (MRing ι ⧸ mCoordIdeal y) =
      (((Algebra.trdeg ℤ (blockFnField y)).toENat + Fintype.card K + 1 : ℕ∞) : WithBot ℕ∞) := by
  have hhor : IsHorizontal (mCoordIdeal y) := horizontal y
  have : (mCoordIdeal y).IsPrime := RingHom.ker_isPrime _
  have htr := ConeTrdeg.proof K ι (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField y c) (ratioPtL y c) (birational y c hc)
    (fun k ↦ ⟨c k, fun h0 ↦ by
      have h1 := congrArg Subtype.val h0
      simp [ratioPtL, ratioPt, hc] at h1⟩)
    (by rw [mCoordIdeal_ratioPtL y c hc]; exact hhor)
  rw [mCoordIdeal_ratioPtL y c hc, ratioField_eq y c hc] at htr
  have hA := IntDomainDim.proof (MRing ι ⧸ mCoordIdeal y)
    (CoordinateConeArithVar.algebraMap_injective _ hhor)
  rw [hA, htr]
  simp only [map_add (f := _), map_natCast]


omit [Fintype K] [∀ k, Fintype (ι k)] [CharZero Ω] in
theorem nonzero_of_relevant (y : (Σ k, ι k) → Ω) (h : ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant (mCoordIdeal y)) :
    ∃ c : ∀ k, ι k, ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  choose c hc using h
  refine ⟨c, fun k h0 ↦ hc k ?_⟩
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul]

end CoordArithOfFnField


open CoordArithOfFnField in
theorem CoordArithOfFnField.proof : CoordArithOfFnField.Statement := by
  intro K _ ι _ K' _ ι' _ Ω _ _ y y' d hK' hy' hF hA
  obtain ⟨_, ⟨_, _, hrel⟩, _, hdim⟩ := hA
  obtain ⟨c, hc⟩ := nonzero_of_relevant y hrel
  choose c' hc' using hy'
  refine ⟨hK', ⟨RingHom.ker_isPrime _, isMultiHomogIdeal y', relevant y' c' hc'⟩, horizontal y', ?_⟩
  rw [dim_eq y c hc, hF] at hdim
  rw [dim_eq y' c' hc']
  generalize (Algebra.trdeg ℤ (blockFnField y')).toENat = e at hdim ⊢
  induction e using ENat.recTopCoe with
  | top =>
    exfalso
    simp only [top_add] at hdim
    norm_cast at hdim
  | coe n =>
    norm_cast at hdim ⊢
    omega

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDefectMetricChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem top_sub_top_mixPot (I : AllFam) (hI : I.IsFamily) {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type}
    [Fintype κ] {x : Ix κ → Ω} {m₀ m₁ : ConeMetric ℂ (Ix κ)}
    (hP : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1)) (hs₀ : IsSmoothMetric m₀)
    (hs₁ : IsSmoothMetric m₁) :
    top I x m₁ D - top I x m₀ D = ∑ i ∈ Finset.range (D + 1),
      ptsIntegral (ι := GlobalTheory κ) (coordIdeal ℤ x) (mixPot m₀ m₁ D i) (logRatio m₀ m₁) := by
  classical
  have hB := tele_smooth_ratio hs₀ hs₁
  have hsymm := (hI Unit (GlobalTheory κ)).1
  have hadd := (hI Unit (GlobalTheory κ)).2.1
  have htel := Finset.sum_range_sub
    (fun i => I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (tele_fam m₀ m₁ (D + 1) i)) (D + 1)
  have hT0 : tele_fam m₀ m₁ (D + 1) 0 = fun _ => HermLine.ofCone m₀ := by
    funext j
    simp [tele_fam]
  have hT1 : tele_fam m₀ m₁ (D + 1) (D + 1) = fun _ => HermLine.ofCone m₁ := by
    funext j
    simp [tele_fam, j.isLt]
  simp only [hT0, hT1] at htel
  unfold top
  rw [← htel]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have e1 : I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (tele_fam m₀ m₁ (D + 1) (i + 1)) =
      I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1)
        (Fin.snoc (tele_fam m₀ m₁ D i) (HermLine.ofCone m₁)) := by
    rw [← tele_fam_succAbove m₀ m₁ D i hi (i + 1) (Or.inr rfl)]
    have : HermLine.ofCone m₁ = tele_fam m₀ m₁ (D + 1) (i + 1) ⟨i, hi⟩ := by
      simp [tele_fam]
    rw [this, ← tele_comp_perm]
    exact (hsymm _ _ _ _ hP (tele_fam_smooth hs₀ hs₁ _ _)).symm
  have e0 : I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (tele_fam m₀ m₁ (D + 1) i) =
      I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1)
        (Fin.snoc (tele_fam m₀ m₁ D i) (HermLine.ofCone m₀)) := by
    rw [← tele_fam_succAbove m₀ m₁ D i hi i (Or.inl rfl)]
    have : HermLine.ofCone m₀ = tele_fam m₀ m₁ (D + 1) i ⟨i, hi⟩ := by
      simp [tele_fam]
    rw [this, ← tele_comp_perm]
    exact (hsymm _ _ _ _ hP (tele_fam_smooth hs₀ hs₁ _ _)).symm
  rw [e1, e0, tele_ofCone_tensor m₀ m₁,
    hadd _ _ _ _ _ hP (tele_fam_smooth hs₀ hs₁ _ _) (tele_smooth_ofCone hs₀) hB,
    add_sub_cancel_left, fam_degZero I hI hP _ (tele_fam_smooth hs₀ hs₁ _ _) _ hB rfl]
  have hpot : pot (tele_fam m₀ m₁ D i) = mixPot m₀ m₁ D i := by
    funext j z
    simp only [pot, mixPot, tele_fam]
    split_ifs <;> rfl
  rw [hpot]
  rfl

theorem DefectMetricChange.proof (hR : RealGramComparison.Statement)
    (hC : ComplexGramMetricChange.Statement) (hM : ResolutionMixedIntegral.Statement) :
    DefectMetricChange.Statement := by
  intro D Ω _ _ κ _ I d m₁ P0₁ hs hc hle hp e hI he
  have h₁ := hR D Ω κ (d.withMetric m₁ P0₁ hs hc hle hp) e he
  have h₀ := hR D Ω κ d e he
  have hc₁ := hC D Ω κ d m₁ P0₁ hs hc hle hp e he
  have htop : top I d.x m₁ D = top I d.x d.m D + ((D : ℝ) + 1) * resMetricInt d m₁ := by
    rw [← hM D Ω κ d m₁ hs, ← top_sub_top_mixPot I hI d.arith d.smooth hs]
    ring
  have hlog := isLittleO_pow_mul_log D
  refine (((h₁.trans_isLittleO hlog).sub (h₀.trans_isLittleO hlog)).add hc₁).congr_left fun n => ?_
  simp only [hsDefect, htop, Nat.factorial_succ]
  push_cast
  field_simp
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEuclideanSectionsPower
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter MeasureTheory

theorem EuclideanSectionsPower.proof (hL : SectionL2Lattice.Statement) (hP : TensorPowerL2Degree.Statement) :
    EuclideanSectionsPower.Statement := by
  intro K _ ι _ Ω _ _ y D A P0 II hD hII har hb hA hc
  obtain ⟨μ, m, hμ, hcon, hZ, hm, hdeg⟩ := hP K ι Ω y D A P0 II hD hII har hb hA hc
  obtain ⟨r, φ, hinj, hdisc, hlat, hsup, hmul, hrank, hnorm⟩ :=
    hL K ι Ω y D A har hb hA.semipos.1.continuousOn μ hμ hcon hZ
  refine ⟨r, φ, hinj, hdisc, hlat, hsup, hmul, hrank, m, hm, fun ε hε => ?_⟩
  filter_upwards [hdeg ε hε] with q hq
  intro _ _
  exact hq (r (m * q)) (φ (m * q)) (hinj _) (hnorm _)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormPullback
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace FibreNormPullback

theorem charZero_of_isArithVar {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {d : ℕ} (hV : IsArithVar (mCoordIdeal y) d) : CharZero Ω := by
  refine charZero_of_inj_zero fun m hm => ?_
  have hmem : (m : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    show mConeMap y (C (m : ℤ)) = 0
    simp only [mConeMap, eq_intCast, Int.cast_natCast]
    rw [map_natCast, ← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hm, map_zero]
  rw [hV.2.2.1, Ideal.mem_bot] at hmem
  exact_mod_cast hmem

theorem isHomogeneous_of_map {σ : Type} {F : MvPolynomial σ ℤ} {m : ℕ}
    (h : (map (Int.castRingHom ℚ) F).IsHomogeneous m) : F.IsHomogeneous m := fun {d} hd =>
  h (by rw [coeff_map, eq_intCast, ne_eq, Int.cast_eq_zero]; exact hd)

theorem norm_prod_le_pow {B : ℝ} (hB : 0 ≤ B) (m : Multiset ℂ) (h : ∀ x ∈ m, ‖x‖ ≤ B) :
    ‖m.prod‖ ≤ B ^ Multiset.card m := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ']
    exact mul_le_mul (h a (Multiset.mem_cons_self a m)) (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))
      (norm_nonneg _) hB

theorem norm_last_le {n : ℕ} (a : ℕ → ℂ) (ha : a 0 = 1) {B : ℝ} (hB : 0 ≤ B)
    (hroot : ∀ w : ℂ, ∑ i ∈ Finset.range (n + 1), a i * w ^ (n - i) = 0 → ‖w‖ ≤ B) :
    ‖a n‖ ≤ B ^ n := by
  classical
  set p : Polynomial ℂ := ∑ i ∈ Finset.range (n + 1), Polynomial.C (a i) * Polynomial.X ^ (n - i) with hp
  have hcoeff : ∀ k, p.coeff k = ∑ i ∈ Finset.range (n + 1), if k = n - i then a i else 0 := by
    intro k
    rw [hp, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
  have hdeg : p.natDegree ≤ n :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ =>
      (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le n i)
  have hlead : p.coeff n = 1 := by
    rw [hcoeff, Finset.sum_eq_single 0]
    · simp [ha]
    · intro i hi hi0
      rw [Finset.mem_range] at hi
      rw [if_neg]
      omega
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h
  have hmon : p.Monic := Polynomial.monic_of_degree_le n (Polynomial.degree_le_of_natDegree_le hdeg) hlead
  have hnat : p.natDegree = n :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg (by rw [hlead]; exact one_ne_zero)
  have hzero : p.coeff 0 = a n := by
    rw [hcoeff, Finset.sum_eq_single n]
    · simp
    · intro i hi hin
      rw [Finset.mem_range] at hi
      rw [if_neg]
      omega
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) h
  have hsplit : p.Splits := IsAlgClosed.splits p
  have hcard : Multiset.card p.roots = n := by rw [Polynomial.splits_iff_card_roots.mp hsplit, hnat]
  have hprod := hsplit.coeff_zero_eq_prod_roots_of_monic hmon
  rw [hzero, hnat] at hprod
  rw [hprod, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, ← hcard]
  refine norm_prod_le_pow hB _ fun w hw => hroot w ?_
  have hw' := (Polynomial.mem_roots hmon.ne_zero).mp hw
  rw [Polynomial.IsRoot.def, hp, Polynomial.eval_finsetSum] at hw'
  simpa using hw'

end FibreNormPullback

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreRelLift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace FibreRelLift

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (ℓ : ℕ)

def ratio (p : Σ k, ι k) : chartRingZ y c :=
  ⟨y p / y ⟨p.1, c p.1⟩, Algebra.subset_adjoin ⟨p, rfl⟩⟩

def dehom : MRing ι →ₐ[ℤ] chartRingZ y c := aeval (ratio y c)

theorem coe_dehom (f : MRing ι) :
    ((dehom y c f : chartRingZ y c) : Ω) = aeval (fun k => (y ⟨k, c k⟩)⁻¹) (mConeMap y f) := by
  show ((chartRingZ y c).val.toRingHom.comp (dehom y c).toRingHom) f =
    ((aeval (fun k => (y ⟨k, c k⟩)⁻¹) : MvPolynomial K Ω →ₐ[Ω] Ω).toRingHom.comp (mConeMap y).toRingHom) f
  refine RingHom.congr_fun (MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)) f
  · simp
  · simp [dehom, ratio, mConeMap, div_eq_mul_inv]

theorem coe_dehom_of_homog {f : MRing ι} {d : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f d) :
    ((dehom y c f : chartRingZ y c) : Ω) = aeval y f * ∏ k, (y ⟨k, c k⟩)⁻¹ ^ d k := by
  rw [coe_dehom, ProjLine.mConeMap_eq_of_isMultiHomog y hf, map_mul, aeval_C, map_prod]
  simp only [map_pow, aeval_X, Algebra.algebraMap_self, RingHom.id_apply]

theorem dehom_eq_zero {f : MRing ι} (hf : f ∈ mCoordIdeal y) : dehom y c f = 0 := by
  have h0 : mConeMap y f = 0 := RingHom.mem_ker.mp hf
  apply Subtype.ext
  rw [coe_dehom, h0]
  simp

abbrev ChartQ := chartRingZ y c ⧸ Ideal.span {((ℓ : ℕ) : chartRingZ y c)}

theorem natCast_chartQ : ((ℓ : ℕ) : ChartQ y c ℓ) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : chartRingZ y c)})) ℓ]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

def dehomMod : MRingOver (ZMod ℓ) ι →+* ChartQ y c ℓ :=
  eval₂Hom (ZMod.castHom (ringChar.dvd (natCast_chartQ y c ℓ)) (ChartQ y c ℓ))
    (fun p => Ideal.Quotient.mk _ (ratio y c p))

theorem dehomMod_map (f : MRing ι) :
    dehomMod y c ℓ (MvPolynomial.map (Int.castRingHom (ZMod ℓ)) f) =
      Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : chartRingZ y c)}) (dehom y c f) := by
  show ((dehomMod y c ℓ).comp (MvPolynomial.map (Int.castRingHom (ZMod ℓ)))) f =
    ((Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : chartRingZ y c)})).comp (dehom y c).toRingHom) f
  refine RingHom.congr_fun (MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)) f
  · simp [dehomMod]
  · simp [dehomMod, dehom]

theorem idealOver_le_ker : GenOnFibres.idealOver y (ZMod ℓ) ≤ RingHom.ker (dehomMod y c ℓ) := by
  refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
  rw [Ideal.mem_comap, RingHom.mem_ker, dehomMod_map, dehom_eq_zero y c hf, map_zero]

def dehomQuot : MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ) →+* ChartQ y c ℓ :=
  Ideal.Quotient.lift _ (dehomMod y c ℓ) fun _ hf => RingHom.mem_ker.mp (idealOver_le_ker y c ℓ hf)

theorem dehomQuot_smul (r : MRingOver (ZMod ℓ) ι) (m : MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ)) :
    dehomQuot y c ℓ (r • m) = dehomMod y c ℓ r * dehomQuot y c ℓ m := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [GenOnFibres.smul_mk, dehomQuot, Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk, map_mul]

theorem dehomMod_cellMon (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {I : ∀ k, Finset (ι k)} (hI : ∀ k, ∀ i ∈ I k, i = c k)
    {t : MRingOver (ZMod ℓ) ι} (ht : t ∈ KH.cellMon (ZMod ℓ) I) : dehomMod y c ℓ t = 1 := by
  have hle : KH.cellMon (ZMod ℓ) I ≤ (⊥ : Submonoid (ChartQ y c ℓ)).comap (dehomMod y c ℓ).toMonoidHom := by
    unfold KH.cellMon
    refine Submonoid.closure_le.mpr ?_
    rintro f ⟨k, i, hi, rfl⟩
    obtain rfl := hI k i hi
    have h1 : ratio y c ⟨k, c k⟩ = 1 := Subtype.ext (by simp [ratio, div_self (hc k)])
    rw [SetLike.mem_coe, Submonoid.mem_comap, Submonoid.mem_bot]
    simp [dehomMod, h1]
  exact Submonoid.mem_bot.mp (hle ht)

variable {y c ℓ}

def dehomLocFun (T : Submonoid (MRingOver (ZMod ℓ) ι)) (hT : ∀ t ∈ T, dehomMod y c ℓ t = 1)
    (x : LocalizedModule T (MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ))) : ChartQ y c ℓ :=
  x.liftOn (fun p => dehomQuot y c ℓ p.1) (by
    rintro ⟨m, s⟩ ⟨m', s'⟩ ⟨u, hu⟩
    have h := congrArg (dehomQuot y c ℓ) hu
    simp only [Submonoid.smul_def, dehomQuot_smul, hT _ u.2, hT _ s.2, hT _ s'.2, one_mul] at h
    exact h)

theorem dehomLocFun_mk (T : Submonoid (MRingOver (ZMod ℓ) ι)) (hT : ∀ t ∈ T, dehomMod y c ℓ t = 1)
    (m : MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ)) (t : T) :
    dehomLocFun T hT (LocalizedModule.mk m t) = dehomQuot y c ℓ m := by
  unfold dehomLocFun
  rw [LocalizedModule.liftOn_mk]

def dehomLoc (T : Submonoid (MRingOver (ZMod ℓ) ι)) (hT : ∀ t ∈ T, dehomMod y c ℓ t = 1) :
    LocalizedModule T (MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ)) →+* ChartQ y c ℓ where
  toFun := dehomLocFun T hT
  map_one' := by
    rw [show (1 : LocalizedModule T (MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ))) =
      LocalizedModule.mk 1 1 by rw [OreLocalization.one_def], dehomLocFun_mk, map_one]
  map_mul' x x' := by
    induction x, x' using LocalizedModule.induction_on₂ with
    | h m m' s s' =>
      rw [LocalizedModule.mk_mul_mk, dehomLocFun_mk, dehomLocFun_mk, dehomLocFun_mk, map_mul]
  map_zero' := by
    rw [← LocalizedModule.zero_mk 1, dehomLocFun_mk, map_zero]
  map_add' x x' := by
    induction x, x' using LocalizedModule.induction_on₂ with
    | h m m' s s' =>
      rw [LocalizedModule.mk_add_mk, dehomLocFun_mk, dehomLocFun_mk, dehomLocFun_mk,
        (dehomQuot y c ℓ).map_add,
        Submonoid.smul_def, Submonoid.smul_def, dehomQuot_smul, dehomQuot_smul, hT _ s.2, hT _ s'.2,
        one_mul, one_mul]

theorem dehomLoc_mk (T : Submonoid (MRingOver (ZMod ℓ) ι)) (hT : ∀ t ∈ T, dehomMod y c ℓ t = 1)
    (m : MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ)) (t : T) :
    dehomLoc T hT (LocalizedModule.mk m t) = dehomQuot y c ℓ m :=
  dehomLocFun_mk T hT m t

end FibreRelLift


open FibreRelLift in
theorem FibreRelLift.proof : FibreRelLift.Statement := by
  intro K _ _ ι _ _ Ω _ y ℓ a r s J u hs hc _ hrel
  set c := GenOnFibres.cellChart J with hcdef
  have hI : ∀ k, ∀ i ∈ J.1 k, i = c k := by
    intro k i hi
    have h1 : (J.1 k).card - 1 = 0 := (Finset.sum_eq_zero_iff.mp J.2.2) k (Finset.mem_univ k)
    exact Finset.card_le_one.mp (by omega) i hi (c k) (GenOnFibres.cellChart_mem J k)
  have hT : ∀ t ∈ KH.cellMon (ZMod ℓ) J.1, dehomMod y c ℓ t = 1 := fun t ht =>
    dehomMod_cellMon y c ℓ hc hI ht
  have hw : ∀ j, s j * ∏ k, y ⟨k, c k⟩ ^ (-a k) ∈ chartRingZ y c := fun j => by
    simpa using hs j c hc
  have hz : ∀ j, dehomLoc _ hT (GenOnFibres.secCoch y (ZMod ℓ) (s j) a J) =
      Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : chartRingZ y c)}) ⟨_, hw j⟩ := by
    intro j
    obtain ⟨e, F, ⟨d, hF, hd, hv⟩, h, he⟩ := GenOnFibres.secCoch_spec (S := ZMod ℓ) (hs j) J hc
    rw [he, dehomLoc_mk, dehomQuot, Ideal.Quotient.lift_mk, dehomMod_map]
    congr 1
    apply Subtype.ext
    rw [coe_dehom_of_homog y c hF, hv, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ (hc k)]
    congr 1
    have := hd k
    omega
  have h1 := congrArg (dehomLoc _ hT) hrel
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_one] at h1
  simp only [map_mul, hz] at h1
  choose b hb using fun j => Ideal.Quotient.mk_surjective (dehomLoc _ hT (u j))
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← hb, ← map_mul, ← map_sum] at h1
  rw [← map_one (Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : chartRingZ y c)})), Ideal.Quotient.eq,
    Ideal.mem_span_singleton'] at h1
  obtain ⟨q, hq⟩ := h1
  refine ⟨fun j => (b j : Ω), -(q : Ω), fun j => (b j).2, neg_mem q.2, ?_⟩
  have h2 := congrArg (fun x : chartRingZ y c => (x : Ω)) hq
  push_cast at h2
  linear_combination (-1 : Ω) * h2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartLatQCech
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ChartLatQCech.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (d : ℕ) (b : K → ℤ),
    IsArithVar (mCoordIdeal y) d →
    Nonempty (chartLatQ y b 1 ≃ₗ[ℚ]
      KH.cechHc ι (KH.quotPart ℚ ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)))) b 0)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

