module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0003
public import Mathlib
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0039

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ExistsNeZeroMemNormSqLeGramDetDivRelIndex
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open Module Submodule Matrix

theorem relIndex_nsmul_mem {E : Type*} [AddCommGroup E] (H L : AddSubgroup E) {x : E}
    (hx : x ∈ L) : H.relIndex L • x ∈ H := by
  exact AddSubgroup.nsmul_relIndex_mem H hx

theorem exists_ne_zero_mem_norm_sq_le_gram_det_div_relIndex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : ℕ}
    (hN : 0 < N) (w : Fin N → E) (hw : LinearIndependent ℝ w) (Λ : AddSubgroup E)
    (hΛ : ∀ i, w i ∈ Λ) (hI : (span ℤ (Set.range w)).toAddSubgroup.relIndex Λ ≠ 0) :
    ∃ v ∈ Λ, v ≠ 0 ∧ ‖v‖ ^ 2 ≤ N * ((gram ℝ w).det /
      ((span ℤ (Set.range w)).toAddSubgroup.relIndex Λ : ℝ) ^ 2) ^ (1 / (N : ℝ)) := by
  classical
  set S : AddSubgroup E := (span ℤ (Set.range w)).toAddSubgroup with hS
  set I : ℕ := S.relIndex Λ with hIdef
  have hI0 : (I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hI
  set V : Submodule ℝ E := Submodule.span ℝ (Set.range w) with hV
  have hSV : ∀ x ∈ S, x ∈ V := by
    intro x hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hΛV : ∀ x ∈ Λ, x ∈ V := by
    intro x hx
    have h1 : I • x ∈ S := relIndex_nsmul_mem S Λ hx
    have h2 : (I : ℝ) • x ∈ V := by rw [Nat.cast_smul_eq_nsmul]; exact hSV _ h1
    have h3 := V.smul_mem ((I : ℝ)⁻¹) h2
    rwa [smul_smul, inv_mul_cancel₀ hI0, one_smul] at h3
  have hSΛ : S ≤ Λ := by
    intro x hx
    have hle : span ℤ (Set.range w) ≤ Λ.toIntSubmodule :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hΛ i)
    exact hle hx
  have hfin : Module.finrank ℝ V = N := by rw [finrank_span_eq_card hw, Fintype.card_fin]
  haveI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range w)
  let f : OrthonormalBasis (Fin N) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hfin)
  let wV : Fin N → V := fun i => ⟨w i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hwV : LinearIndependent ℝ wV := LinearIndependent.of_comp V.subtype hw
  let φ : V ≃ₗ[ℝ] (Fin N → ℝ) := f.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ (Fin N → ℝ))
  have hφ : ∀ v : V, φ v = (f.repr v).ofLp := fun v => rfl
  let vb : Fin N → (Fin N → ℝ) := fun i => φ (wV i)
  have hvb : LinearIndependent ℝ vb := hwV.map' φ.toLinearMap (LinearEquiv.ker _)
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let b : Module.Basis (Fin N) ℝ (Fin N → ℝ) :=
    basisOfLinearIndependentOfCardEqFinrank hvb (by simp)
  have hb : ∀ i, b i = φ (wV i) := fun i => by simp [b, vb]
  set d := (Matrix.of ⇑b).det with hd
  have hgram : (gram ℝ w).det = d ^ 2 := by
    have hG : gram ℝ w = Matrix.of ⇑b * (Matrix.of ⇑b).transpose := by
      ext i j
      rw [Matrix.gram_apply, Matrix.mul_apply]
      simp only [Matrix.of_apply, Matrix.transpose_apply, hb, hφ]
      have e1 : inner ℝ (w i) (w j) = inner ℝ (f.repr (wV i)) (f.repr (wV j)) := by
        rw [LinearIsometryEquiv.inner_map_map]
        rfl
      rw [e1, PiLp.inner_apply]
      simp [mul_comm]
    rw [hG, Matrix.det_mul, Matrix.det_transpose, sq]
  have hnorm : ∀ v : V, ‖(v : E)‖ ^ 2 = ∑ j, (φ v j) ^ 2 := by
    intro v
    change ‖v‖ ^ 2 = _
    rw [← f.repr.norm_map, EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp [Real.norm_eq_abs, sq_abs, hφ]
  let χ : V →+ (Fin N → ℝ) := φ.toLinearMap.toAddMonoidHom
  have hχ : Function.Injective χ := φ.injective
  let ι : V →+ E := V.subtype.toAddMonoidHom
  let L2g : AddSubgroup (Fin N → ℝ) := (Λ.comap ι).map χ
  let L1 : Submodule ℤ (Fin N → ℝ) := span ℤ (Set.range b)
  have hL1g : L1.toAddSubgroup = (S.comap ι).map χ := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map, AddSubgroup.mem_comap]
    constructor
    · intro hx
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
      refine ⟨∑ i, c i • wV i, ?_, ?_⟩
      · show ((∑ i, c i • wV i : V) : E) ∈ S
        rw [hS, Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun ℤ]
        exact ⟨c, by simp [wV]⟩
      set_option synthInstance.maxHeartbeats 100000 in
        · simp [χ, hb, map_sum]
    · rintro ⟨v, hv, rfl⟩
      have hv' : (v : E) ∈ span ℤ (Set.range w) := hv
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hv'
      have hvc : v = ∑ i, c i • wV i := Subtype.ext (by simp [wV, ← hc])
      rw [hvc]
      exact (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, by simp [χ, hb, map_sum]⟩
  have hΛr : Λ ≤ ι.range := fun x hx => ⟨⟨x, hΛV x hx⟩, rfl⟩
  have hrel : L1.toAddSubgroup.relIndex L2g = I := by
    rw [hL1g, AddSubgroup.relIndex_map_map_of_injective _ _ hχ, AddSubgroup.relIndex_comap,
      AddSubgroup.map_comap_eq_self hΛr]
  let L2 : Submodule ℤ (Fin N → ℝ) := L2g.toIntSubmodule
  have hL12 : L1 ≤ L2 := by
    intro x hx
    have h1 : x ∈ L1.toAddSubgroup := hx
    rw [hL1g] at h1
    exact AddSubgroup.map_mono (AddSubgroup.comap_mono hSΛ) h1
  let b' : Module.Basis (Fin N) ℝ (Fin N → ℝ) := b.unitsSMul (fun _ => Units.mk0 ((I : ℝ)⁻¹) (inv_ne_zero hI0))
  have hb' : ∀ i, b' i = (I : ℝ)⁻¹ • b i := fun i => by
    show (b.unitsSMul _) i = _
    rw [Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0]
  have hL2sub : (L2 : Set (Fin N → ℝ)) ⊆ span ℤ (Set.range b') := by
    intro x hx
    have h1 : L1.toAddSubgroup.relIndex L2g • x ∈ L1.toAddSubgroup := relIndex_nsmul_mem _ _ hx
    rw [hrel] at h1
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h1
    refine (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, ?_⟩
    have hx' : x = (I : ℝ)⁻¹ • (I • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hI0, one_smul]
    rw [hx', ← hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb', smul_comm]
  haveI : DiscreteTopology L2 := DiscreteTopology.of_subset (inferInstance :
    DiscreteTopology (span ℤ (Set.range b'))) hL2sub
  haveI : IsZLattice ℝ L2 := ⟨by
    rw [eq_top_iff, ← b.span_eq]
    exact Submodule.span_le.mpr fun x hx => Submodule.subset_span (hL12 (Submodule.subset_span hx))⟩
  have hcov1 : ZLattice.covolume L1 MeasureTheory.volume = |d| := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L1 MeasureTheory.volume
      (ZSpan.isAddFundamentalDomain b MeasureTheory.volume), MeasureTheory.Measure.real,
      ZSpan.volume_fundamentalDomain, ENNReal.toReal_ofReal (abs_nonneg _)]
  have hcov2 : ZLattice.covolume L2 MeasureTheory.volume = |d| / I := by
    have h := ZLattice.covolume_div_covolume_eq_relIndex L1 L2 hL12
    have h' : L1.toAddSubgroup.relIndex L2.toAddSubgroup = I := hrel
    rw [h', hcov1] at h
    have hpos : 0 < ZLattice.covolume L2 MeasureTheory.volume := ZLattice.covolume_pos L2 _
    field_simp at h ⊢
    linarith
  let b2 := (Module.Free.chooseBasis ℤ L2).ofZLatticeBasis ℝ L2
  have hspan2 : span ℤ (Set.range b2) = L2 := Module.Basis.ofZLatticeBasis_span ℝ L2 _
  have hF2 : MeasureTheory.IsAddFundamentalDomain L2 (ZSpan.fundamentalDomain b2) MeasureTheory.volume := by
    have := ZSpan.isAddFundamentalDomain b2 MeasureTheory.volume
    rwa [hspan2] at this
  have hvolF2 : MeasureTheory.volume (ZSpan.fundamentalDomain b2) = ENNReal.ofReal (|d| / I) := by
    rw [← hcov2, ZLattice.covolume_eq_measure_fundamentalDomain L2 MeasureTheory.volume hF2,
      MeasureTheory.Measure.real, ENNReal.ofReal_toReal
        (ZSpan.fundamentalDomain_isBounded b2).measure_lt_top.ne]
  haveI : Countable ↥L2.toAddSubgroup := by
    have hc : ((L2.toAddSubgroup : AddSubgroup (Fin N → ℝ)) : Set (Fin N → ℝ)) ⊆
        Set.range (fun c : Fin N → ℤ => ∑ i, c i • b' i) := by
      intro z hz
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hL2sub hz)
      exact ⟨c, hc⟩
    exact ((Set.countable_range _).mono hc).to_subtype
  haveI : DiscreteTopology ↥L2.toAddSubgroup := inferInstanceAs (DiscreteTopology L2)
  set t : ℝ := (|d| / I) ^ ((N : ℝ)⁻¹) with ht
  have hq : 0 ≤ |d| / I := div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
  have ht0 : 0 ≤ t := Real.rpow_nonneg hq _
  have htN : t ^ N = |d| / I := Real.rpow_inv_natCast_pow hq (by omega)
  obtain ⟨x, hx0, hxs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (μ := MeasureTheory.volume) (L := L2.toAddSubgroup)
    (s := Set.Icc (-(fun _ : Fin N => t)) (fun _ : Fin N => t))
    hF2 (fun z hz => ⟨neg_le_neg hz.2, by simpa using neg_le_neg hz.1⟩) (convex_Icc _ _) isCompact_Icc
    (by
      rw [hvolF2, Real.volume_Icc_pi, Module.finrank_fin_fun]
      have e2 : ∏ i : Fin N, ENNReal.ofReal ((fun _ : Fin N => t) i - (-(fun _ : Fin N => t)) i) =
          2 ^ N * ENNReal.ofReal (|d| / I) := by
        simp only [Pi.neg_apply, sub_neg_eq_add, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
        rw [← ENNReal.ofReal_pow (by positivity), show t + t = 2 * t by ring, mul_pow, htN,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
        simp
      rw [e2, mul_comm])
  have hxL2 : (x : Fin N → ℝ) ∈ L2g := x.2
  obtain ⟨v, hv, hvx⟩ := AddSubgroup.mem_map.mp hxL2
  have hxj : ∀ j, |(x : Fin N → ℝ) j| ≤ t := fun j =>
    abs_le.mpr ⟨by simpa using hxs.1 j, hxs.2 j⟩
  refine ⟨(v : E), hv, ?_, ?_⟩
  · intro h0
    apply hx0
    have hv0 : v = 0 := Subtype.ext h0
    apply Subtype.ext
    rw [← hvx, hv0, map_zero]
    rfl
  have hxv : ∀ j, φ v j = (x : Fin N → ℝ) j := fun j => by rw [← hvx]; rfl
  rw [hnorm v]
  calc ∑ j, (φ v j) ^ 2 ≤ ∑ _j : Fin N, t ^ 2 := Finset.sum_le_sum fun j _ => by
        have := pow_le_pow_left₀ (abs_nonneg _) (hxj j) 2
        rwa [sq_abs, ← hxv j] at this
    _ = N * ((gram ℝ w).det / (I : ℝ) ^ 2) ^ (1 / (N : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hgram, ht, one_div]
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul hq, mul_comm, Real.rpow_mul hq, Real.rpow_natCast,
          div_pow, sq_abs]

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion

open IsLocalRing Polynomial

theorem isPrecomplete_finite_module {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  first | exact UpperTheory.Reformulated.B.Qk17.isPrecomplete_finite_module .. | (apply UpperTheory.Reformulated.B.Qk17.isPrecomplete_finite_module <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk17.isPrecomplete_finite_module <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk17.isPrecomplete_finite_module <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qk17.isPrecomplete_finite_module <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk17.isPrecomplete_finite_module <;> first | assumption | infer_instance)

theorem isAdicComplete_finite_algebra {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (S : Type*) [CommRing S] [Algebra R S] [Module.Finite R S] :
    IsAdicComplete ((maximalIdeal R).map (algebraMap R S)) S := by
  rw [IsAdicComplete.map_algebraMap_iff]
  have := isPrecomplete_finite_module (maximalIdeal R) S
  exact ⟨⟩

theorem map_maximalIdeal_le_maximal {R : Type*} [CommRing R] [IsLocalRing R] (S : Type*) [CommRing S]
    [Algebra R S] [Module.Finite R S] (n : Ideal S) (hn : n.IsMaximal) :
    (maximalIdeal R).map (algebraMap R S) ≤ n := by
  rw [Ideal.map_le_iff_le_comap]
  have : (n.comap (algebraMap R S)).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal n
  exact (IsLocalRing.eq_maximalIdeal this).ge

theorem finite_maximal_ideals_of_finite {R : Type*} [CommRing R] [IsLocalRing R] (S : Type*) [CommRing S]
    [Algebra R S] [Module.Finite R S] : {n : Ideal S | n.IsMaximal}.Finite := by
  let J := (maximalIdeal R).map (algebraMap R S)
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  have : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ J) := Module.Finite.of_restrictScalars_finite R _ _
  have : IsArtinianRing (S ⧸ J) := IsArtinianRing.of_finite (R ⧸ maximalIdeal R) (S ⧸ J)
  refine ((IsArtinianRing.setOfPred_isMaximal_finite (S ⧸ J)).image
    (Ideal.comap (Ideal.Quotient.mk J))).subset ?_
  intro n hn
  refine ⟨n.map (Ideal.Quotient.mk J), ?_, ?_⟩
  · have hJ : J ≤ n := map_maximalIdeal_le_maximal S n hn
    have : n.IsMaximal := hn
    exact Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by simpa using hJ)
  · have hJ : J ≤ n := map_maximalIdeal_le_maximal S n hn
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hJ

theorem exists_pow_mem_map_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] (S : Type*) [CommRing S]
    [Algebra R S] [Module.Finite R S] (b : S) (hb : ∀ n : Ideal S, n.IsMaximal → b ∈ n) :
    ∃ N : ℕ, 0 < N ∧ b ^ N ∈ (maximalIdeal R).map (algebraMap R S) := by
  let J := (maximalIdeal R).map (algebraMap R S)
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  have : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ J) := Module.Finite.of_restrictScalars_finite R _ _
  have : IsArtinianRing (S ⧸ J) := IsArtinianRing.of_finite (R ⧸ maximalIdeal R) (S ⧸ J)
  obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := S ⧸ J)
  have hmem : Ideal.Quotient.mk J b ∈ (⊥ : Ideal (S ⧸ J)).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro q ⟨-, hq⟩
    have := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective (K := q)
    exact hb _ this
  have h1 : Ideal.Quotient.mk J (b ^ (k + 1)) = 0 := by
    have := Ideal.pow_mem_pow hmem k
    rw [hk, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    rw [pow_succ, map_mul, map_pow, this, zero_mul]
  exact ⟨k + 1, k.succ_pos, Ideal.Quotient.eq_zero_iff_mem.mp h1⟩

theorem exists_idempotent_henselian {S : Type*} [CommRing S] (J : Ideal S) [HenselianRing S J] (x : S) (N : ℕ)
    (hN : (x * x - x) ^ (N + 1) ∈ J) : ∃ e s : S, e * e = e ∧ e - x = s * (x * x - x) := by
  have hnil : (Ideal.Quotient.mk J x - Ideal.Quotient.mk J x ^ 2) ^ (N + 1) = 0 := by
    have : Ideal.Quotient.mk J x - Ideal.Quotient.mk J x ^ 2 = -(Ideal.Quotient.mk J (x * x - x)) := by
      simp only [map_sub, map_mul, pow_two, neg_sub]
    rw [this, neg_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 hN, mul_zero]
  have hid := isIdempotentElem_one_sub_one_sub_pow_pow _ (N + 1) hnil
  have hq : Ideal.Quotient.mk J (1 - (1 - x ^ (N + 1)) ^ (N + 1)) =
      1 - (1 - Ideal.Quotient.mk J x ^ (N + 1)) ^ (N + 1) := by simp
  have hid' : Ideal.Quotient.mk J (1 - (1 - x ^ (N + 1)) ^ (N + 1)) *
      Ideal.Quotient.mk J (1 - (1 - x ^ (N + 1)) ^ (N + 1)) =
      Ideal.Quotient.mk J (1 - (1 - x ^ (N + 1)) ^ (N + 1)) := by rw [hq]; exact hid.eq
  have hxW : IsIdempotentElem (Ideal.Quotient.mk (Ideal.span {x * x - x}) x) := by
    rw [IsIdempotentElem, ← map_mul, Ideal.Quotient.eq]
    exact Ideal.subset_span rfl
  have hqW : Ideal.Quotient.mk (Ideal.span {x * x - x}) (1 - (1 - x ^ (N + 1)) ^ (N + 1)) =
      Ideal.Quotient.mk (Ideal.span {x * x - x}) x := by
    simp only [map_sub, map_one, map_pow, hxW.pow_succ_eq, hxW.one_sub.pow_succ_eq, sub_sub_cancel]
  generalize 1 - (1 - x ^ (N + 1)) ^ (N + 1) = e0 at hid' hqW
  have h3 : e0 - x ∈ Ideal.span {x * x - x} := Ideal.Quotient.eq.1 hqW
  have h4 : e0 * e0 - e0 ∈ Ideal.span {x * x - x} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hqW, hxW.eq, sub_self]
  have h1 : (X ^ 2 - X : S[X]).eval e0 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [eval_sub, eval_pow, eval_X, map_sub, map_pow, pow_two, hid', sub_self]
  have hd : (X ^ 2 - X : S[X]).derivative.eval e0 = 2 * e0 - 1 := by
    simp; ring
  have h2 : IsUnit (Ideal.Quotient.mk J ((X ^ 2 - X : S[X]).derivative.eval e0)) := by
    rw [hd]
    refine isUnit_iff_exists_inv.2 ⟨Ideal.Quotient.mk J (2 * e0 - 1), ?_⟩
    simp only [map_sub, map_mul, map_ofNat, map_one]
    linear_combination 4 * hid'
  have hmon : (X ^ 2 - X : S[X]).Monic :=
    monic_X_pow_sub (lt_of_le_of_lt degree_X_le (by norm_num))
  obtain ⟨e, he, hee⟩ := HenselianRing.is_henselian _ hmon e0 h1 h2
  have hee' : e * e = e := by
    have := he.eq_zero
    simp only [eval_sub, eval_pow, eval_X] at this
    linear_combination this
  have hu2 : (2 * e - 1) * (2 * e - 1) = 1 := by linear_combination 4 * hee'
  have hdu : IsUnit (e - e0 - (2 * e - 1)) := by
    have : e - e0 - (2 * e - 1) = (-(2 * e - 1)) * ((e - e0) * (-(2 * e - 1)) + 1) := by
      linear_combination (-(e - e0)) * hu2
    rw [this]
    exact (isUnit_iff_exists_inv.2 ⟨-(2 * e - 1), by linear_combination hu2⟩).mul
      (Ring.mem_jacobson_iff.1 (HenselianRing.jac hee) _)
  have hdW : e - e0 ∈ Ideal.span {x * x - x} := by
    obtain ⟨v, hv⟩ := hdu.exists_left_inv
    have hdd : (e - e0) * (e - e0 - (2 * e - 1)) = e0 * e0 - e0 := by
      linear_combination (-1 : S) * hee'
    have : e - e0 = v * (e0 * e0 - e0) := by
      linear_combination (-(e - e0)) * hv + v * hdd
    rw [this]; exact Ideal.mul_mem_left _ _ h4
  have h5 : e - x ∈ Ideal.span {x * x - x} := by
    have : e - x = (e - e0) + (e0 - x) := by ring
    rw [this]; exact Ideal.add_mem _ hdW h3
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 h5
  exact ⟨e, s, hee', hs.symm⟩

theorem isLocalRing_finite_domain {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (S : Type*) [CommRing S] [IsDomain S] [Algebra R S]
    [Module.Finite R S] : IsLocalRing S := by
  classical
  by_contra hloc
  obtain ⟨M1, hM1⟩ := Ideal.exists_maximal S
  have hex : ∃ M2 : Ideal S, M2.IsMaximal ∧ M2 ≠ M1 := by
    by_contra h
    push Not at h
    exact hloc (IsLocalRing.of_unique_max_ideal ⟨M1, hM1, fun M hM => h M hM⟩)
  obtain ⟨M2, hM2, h12⟩ := hex
  set F := (finite_maximal_ideals_of_finite (R := R) S).toFinset.filter (· ≠ M1) with hF
  have hmemF : ∀ N : Ideal S, N.IsMaximal → N ≠ M1 → N ∈ F := by
    intro N hN hN1
    rw [hF, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨hN, hN1⟩
  have hcop : M1 ⊔ F.inf id = ⊤ := by
    by_contra hne
    have hle : F.inf id ≤ M1 := by
      rw [hM1.eq_of_le hne le_sup_left]; exact le_sup_right
    obtain ⟨N, hN, hNle⟩ := (hM1.isPrime.inf_le').1 hle
    rw [hF, Finset.mem_filter, Set.Finite.mem_toFinset] at hN
    exact hN.2 ((hN.1 : N.IsMaximal).eq_of_le hM1.ne_top hNle)
  have h1 : (1 : S) ∈ M1 ⊔ F.inf id := by rw [hcop]; exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
  have hx1 : ∀ N : Ideal S, N.IsMaximal → N ≠ M1 → x - 1 ∈ N := by
    intro N hN hN1
    have : y ∈ N := Finset.inf_le (f := id) (hmemF N hN hN1) hy
    have : x - 1 = -y := by rw [← hxy]; ring
    rw [this]; exact N.neg_mem (by assumption)
  have hall : ∀ N : Ideal S, N.IsMaximal → x * x - x ∈ N := by
    intro N hN
    by_cases hN1 : N = M1
    · subst hN1; exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hx) hx
    · have := hx1 N hN hN1
      have e : x * x - x = x * (x - 1) := by ring
      rw [e]; exact Ideal.mul_mem_left _ _ this
  obtain ⟨k, hk, hkJ⟩ := exists_pow_mem_map_maximalIdeal (R := R) S _ hall
  have : IsAdicComplete ((maximalIdeal R).map (algebraMap R S)) S := isAdicComplete_finite_algebra S
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  obtain ⟨e, s, hee, hes⟩ := exists_idempotent_henselian ((maximalIdeal R).map (algebraMap R S)) x k' hkJ
  have hxx1 : x * x - x ∈ M1 := hall M1 hM1
  have hxx2 : x * x - x ∈ M2 := hall M2 hM2
  rcases (IsIdempotentElem.iff_eq_zero_or_one.1 hee) with h0 | h0
  · apply hM2.ne_top
    rw [Ideal.eq_top_iff_one]
    have ha : -x ∈ M2 := by
      have : -x = s * (x * x - x) := by rw [← hes, h0]; ring
      rw [this]; exact Ideal.mul_mem_left _ _ hxx2
    have hb := hx1 M2 hM2 h12
    have : (1 : S) = -(x - 1) + -(-x) := by ring
    rw [this]; exact M2.add_mem (M2.neg_mem hb) (M2.neg_mem ha)
  · apply hM1.ne_top
    rw [Ideal.eq_top_iff_one]
    have : (1 : S) = s * (x * x - x) + x := by rw [← hes, h0]; ring
    rw [this]; exact M1.add_mem (Ideal.mul_mem_left _ _ hxx1) hx

section

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (L : Type*) [Field L] [Algebra R L] [FaithfulSMul R L] [Module.Finite R (integralClosure R L)]

theorem cl_inj : Function.Injective (algebraMap R (integralClosure R L)) := by
  intro x y h
  apply FaithfulSMul.algebraMap_injective R L
  exact congrArg Subtype.val h

theorem cl_isLocalRing [IsAdicComplete (maximalIdeal R) R] : IsLocalRing (integralClosure R L) :=
  isLocalRing_finite_domain (R := R) (integralClosure R L)

theorem cl_isLocalHom : IsLocalHom (algebraMap R (integralClosure R L)) :=
  RingHom.IsIntegral.isLocalHom (fun x => (Algebra.IsIntegral.isIntegral x : IsIntegral R x))
    (cl_inj R L)

end

section

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  (L : Type*) [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L]

include K

theorem cl_faithful : FaithfulSMul R L :=
  (faithfulSMul_iff_algebraMap_injective R L).2 (by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K))

variable [Module.Finite R (integralClosure R L)]

theorem cl_dvr [IsAdicComplete (maximalIdeal R) R] :
    IsDiscreteValuationRing (integralClosure R L) := by
  have := cl_faithful R K L
  have : IsLocalRing (integralClosure R L) := cl_isLocalRing R L
  have : IsFractionRing (integralClosure R L) L := integralClosure.isFractionRing_of_finite_extension K L
  have : Algebra.IsIntegral R (integralClosure R L) := IsIntegralClosure.isIntegral_algebra R L
  have : IsNoetherianRing (integralClosure R L) :=
    isNoetherianRing_iff.mpr (isNoetherian_of_tower R inferInstance)
  have hD : IsDedekindDomain (integralClosure R L) :=
    { ‹IsNoetherianRing (integralClosure R L)›,
      Ring.DimensionLEOne.of_isIntegral R (integralClosure R L),
      (isIntegrallyClosed_iff L).mpr fun {x} hx =>
        ⟨IsIntegralClosure.mk' (integralClosure R L) x (isIntegral_trans (R := R) _ hx),
          IsIntegralClosure.algebraMap_mk' _ _ _⟩ with : IsDedekindDomain (integralClosure R L) }
  have hnf : ¬ IsField (integralClosure R L) := fun h =>
    (isField_iff_maximalIdeal_eq.not.mpr IsDiscreteValuationRing.not_a_field')
      (isField_of_isIntegral_of_isField (cl_inj R L) h)
  exact ((IsDiscreteValuationRing.TFAE (integralClosure R L) hnf).out 1 3).mpr hD

end

end ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
end
end

