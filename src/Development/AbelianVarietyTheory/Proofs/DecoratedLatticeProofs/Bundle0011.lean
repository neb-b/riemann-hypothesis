module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LinearIndependentWave

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinsetNormOne
section
noncomputable section

open NumberField IsDedekindDomain Topology Filter

namespace GlobalTheory.HeckeSplitAll.Approx

variable {F : Type} [Field F] [NumberField F]

theorem norm_alg_inf (w : InfinitePlace F) (x : F) : ‖algebraMap F w.Completion x‖ = w x := by
  rw [AbsoluteValue.Completion.algebraMap_def, AbsoluteValue.Completion.norm_coe]
  rfl

theorem norm_le_one_iff_int (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers F := by
  rw [Valued.toNormedField.norm_le_one_iff, HeightOneSpectrum.mem_adicCompletionIntegers]

theorem norm_nat_le_one (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) : ‖(m : v.adicCompletion F)‖ ≤ 1 :=
  (norm_le_one_iff_int v _).2 (natCast_mem _ m)

theorem norm_int_le_one (v : HeightOneSpectrum (𝓞 F)) (o : 𝓞 F) :
    ‖algebraMap F (v.adicCompletion F) (o : F)‖ ≤ 1 :=
  (norm_le_one_iff_int v _).2 (PI.UnipApproxD.IntegersDenseFiniteAdeles.int_R v o)

theorem norm_int_eq_one (v : HeightOneSpectrum (𝓞 F)) (o : 𝓞 F) (ho : o ∉ v.asIdeal) :
    ‖algebraMap F (v.adicCompletion F) (o : F)‖ = 1 := by
  refine le_antisymm (norm_int_le_one v o) (not_lt.1 fun h => ho ?_)
  rw [Valued.toNormedField.norm_lt_one_iff] at h
  have e := PI.UnipApproxD.IntegersDenseFiniteAdeles.val_R (K := F) v o
  rw [show algebraMap F (v.adicCompletion F) (o : F) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F o) from rfl,
    e] at h
  exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v o).1 h

theorem nat_ne_zero_fin (v : HeightOneSpectrum (𝓞 F)) {m : ℕ} (hm : m ≠ 0) : (m : v.adicCompletion F) ≠ 0 := by
  have h := (algebraMap F (v.adicCompletion F)).injective.ne (Nat.cast_ne_zero.2 hm : (m : F) ≠ 0)
  rwa [map_natCast, map_zero] at h

theorem norm_natCast_lt_one (v : HeightOneSpectrum (𝓞 F)) (c : ℕ) (hc : Ideal.absNorm v.asIdeal ∣ c) :
    ‖(c : v.adicCompletion F)‖ < 1 := by
  have hmem : (c : 𝓞 F) ∈ v.asIdeal := by
    obtain ⟨k, hk⟩ := hc
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  have hval := (HeightOneSpectrum.intValuation_lt_one_iff_mem v (c : 𝓞 F)).2 hmem
  rw [Valued.toNormedField.norm_lt_one_iff]
  have e := PI.UnipApproxD.IntegersDenseFiniteAdeles.val_R (K := F) v (c : 𝓞 F)
  rw [map_natCast, map_natCast] at e
  rw [e]
  exact hval

theorem exists_finset_norm_one (x : F) (hx : x ≠ 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, ‖algebraMap F (v.adicCompletion F) x‖ = 1 := by
  classical
  have h1 := Filter.eventually_cofinite.mp (algebraMap F (FiniteAdeleRing (𝓞 F) F) x).2
  have h2 := Filter.eventually_cofinite.mp (algebraMap F (FiniteAdeleRing (𝓞 F) F) x⁻¹).2
  refine ⟨(h1.union h2).toFinset, fun v hv => ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hv
  obtain ⟨ha, hb⟩ := hv
  have ha' : ‖algebraMap F (v.adicCompletion F) x‖ ≤ 1 := (norm_le_one_iff_int v _).2 ha
  have hb' : ‖algebraMap F (v.adicCompletion F) x⁻¹‖ ≤ 1 := (norm_le_one_iff_int v _).2 hb
  rw [map_inv₀, norm_inv] at hb'
  have hpos : 0 < ‖algebraMap F (v.adicCompletion F) x‖ := norm_pos_iff.2 ((map_ne_zero _).2 hx)
  have hm := mul_inv_cancel₀ hpos.ne'
  refine le_antisymm ha' ?_
  nlinarith [mul_nonneg hpos.le (sub_nonneg.2 hb')]

theorem exists_nat_small (x : F) (hx : x ≠ 0) : ∃ P : ℕ, P ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 F),
    ‖algebraMap F (v.adicCompletion F) x‖ ≠ 1 → ‖(P : v.adicCompletion F)‖ < 1 := by
  classical
  obtain ⟨B, hB⟩ := exists_finset_norm_one x hx
  refine ⟨∏ v ∈ B, Ideal.absNorm v.asIdeal, ?_, fun v hv => ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro v _
    exact (lt_trans zero_lt_one (HeightOneSpectrum.one_lt_absNorm v)).ne'
  · exact norm_natCast_lt_one v _ (Finset.dvd_prod_of_mem _ (by_contra fun h => hv (hB v h)))

theorem exists_int_near (F : Type) [Field F] [NumberField F] : ∃ C : ℝ, 0 < C ∧ ∀ t : InfiniteAdeleRing F,
    ∃ o : 𝓞 F, ∀ w : InfinitePlace F, ‖algebraMap F w.Completion (o : F) - t w‖ < C := by
  classical
  set b := integralBasis F with hb
  refine ⟨1 + ∑ w : InfinitePlace F, ∑ i, w (b i), by positivity, fun t => ?_⟩
  have hopen : IsOpen {y : InfiniteAdeleRing F | ∀ w, ‖y w - t w‖ < 1} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun w =>
      isOpen_lt (((continuous_apply w : Continuous fun y : InfiniteAdeleRing F => y w).sub
        continuous_const).norm) continuous_const
  obtain ⟨f, hf⟩ := (InfiniteAdeleRing.denseRange_algebraMap F).exists_mem_open hopen
    ⟨t, fun w => by
      show ‖t w - t w‖ < 1
      rw [sub_self, norm_zero]; exact one_pos⟩
  have hf' : ∀ w, ‖algebraMap F w.Completion f - t w‖ < 1 := hf
  refine ⟨∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i, fun w => ?_⟩
  have e : ((∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i : 𝓞 F) : F) - f =
      ∑ i, (((⌊b.repr f i⌋ : ℚ) - b.repr f i : ℚ) : F) * b i := by
    conv_lhs => arg 2; rw [← b.sum_repr f]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show ((∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i : 𝓞 F) : F) =
      algebraMap (𝓞 F) F (∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i) from rfl, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, ← integralBasis_apply, ← hb, Rat.smul_def, zsmul_eq_mul]
    push_cast
    ring
  have h2 : ‖algebraMap F w.Completion (((∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i : 𝓞 F) : F) - f)‖ ≤
      ∑ i, w (b i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_alg_inf, map_mul]
    refine mul_le_of_le_one_left (apply_nonneg _ _) ?_
    rw [← InfinitePlace.norm_embedding_eq, map_ratCast, Complex.norm_ratCast, ← Rat.cast_abs, ← Rat.cast_one, Rat.cast_le,
      abs_le]
    constructor <;> linarith [Int.floor_le (b.repr f i), Int.lt_floor_add_one (b.repr f i)]
  have h3 : ∑ i, w (b i) ≤ ∑ w : InfinitePlace F, ∑ i, w (b i) :=
    Finset.single_le_sum (f := fun w : InfinitePlace F => ∑ i, w (b i))
      (fun _ _ => Finset.sum_nonneg fun _ _ => apply_nonneg _ _) (Finset.mem_univ w)
  have h4 := norm_add_le (algebraMap F w.Completion (((∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i : 𝓞 F) : F) - f))
    (algebraMap F w.Completion f - t w)
  rw [map_sub, sub_add_sub_cancel, ← map_sub] at h4
  linarith [hf' w]


open NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory ENNReal Module in
open scoped nonZeroDivisors in
theorem exists_small_elt (v₀ : HeightOneSpectrum (𝓞 F)) (η : ℝ) (hη : 0 < η) :
    ∃ x : F, x ≠ 0 ∧ (∀ w : InfinitePlace F, w x < η) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ≠ v₀ → ‖algebraMap F (v.adicCompletion F) x‖ ≤ 1 := by
  classical
  let f : InfinitePlace F → NNReal := fun _ => ⟨η, hη.le⟩
  have hV : volume (convexBodyLT F f) ≠ ⊤ := by
    rw [convexBodyLT_volume]; exact mul_ne_top coe_ne_top coe_ne_top
  have hV0 : 0 < (volume (convexBodyLT F f)).toReal := by
    rw [convexBodyLT_volume, toReal_mul, coe_toReal, coe_toReal]
    have h1 : (1 : ℝ) ≤ convexBodyLTFactor F := by exact_mod_cast one_le_convexBodyLTFactor F
    refine mul_pos (by linarith) ?_
    rw [NNReal.coe_prod]
    exact Finset.prod_pos fun w _ => by rw [NNReal.coe_pow]; exact pow_pos hη _
  set B : ℝ := (volume (ZSpan.fundamentalDomain (latticeBasis F))).toReal * 2 ^ finrank ℝ (mixedSpace F) with hB
  have hq : (1 : ℝ) < Ideal.absNorm v₀.asIdeal := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v₀
  have ht : Tendsto (fun k : ℕ => ((Ideal.absNorm v₀.asIdeal : ℝ)⁻¹) ^ k * B) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (Ideal.absNorm v₀.asIdeal : ℝ)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ hq)).mul_const B
    rwa [zero_mul] at this
  obtain ⟨k, hk⟩ := (ht.eventually (Iio_mem_nhds hV0)).exists
  have hI : ((v₀.asIdeal ^ k : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (pow_ne_zero k v₀.ne_bot)
  let J : (FractionalIdeal (𝓞 F)⁰ F)ˣ := Units.mk0 _ (inv_ne_zero hI)
  have h : minkowskiBound F J < volume (convexBodyLT F f) := by
    rw [← ENNReal.toReal_lt_toReal (minkowskiBound_lt_top F J).ne hV]
    refine lt_of_eq_of_lt ?_ hk
    rw [minkowskiBound, volume_fundamentalDomain_fractionalIdealLatticeBasis, toReal_mul, toReal_mul, toReal_pow,
      ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _)), hB]
    simp only [J, Units.val_mk0, map_inv₀, FractionalIdeal.coeIdeal_absNorm, map_pow, toReal_ofNat]
    push_cast
    rw [inv_pow]
    ring
  obtain ⟨a, ha, hne, hlt⟩ := exists_ne_zero_mem_ideal_lt F J h
  refine ⟨a, hne, fun w => hlt w, fun v hv => ?_⟩
  obtain ⟨p, hp0, hpv⟩ : ∃ p ∈ v₀.asIdeal, p ∉ v.asIdeal := by
    by_contra hc
    push Not at hc
    exact hv (HeightOneSpectrum.ext (v₀.isMaximal.eq_of_le v.isPrime.ne_top hc).symm)
  have hm : a * algebraMap (𝓞 F) F (p ^ k) ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [← inv_mul_cancel₀ hI]
    exact FractionalIdeal.mul_mem_mul ha (FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.pow_mem_pow hp0 k))
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hm
  have h1 := norm_int_le_one v o
  rw [show (o : F) = algebraMap (𝓞 F) F o from rfl, ho, map_mul, norm_mul, map_pow, map_pow, norm_pow] at h1
  have h2 := norm_int_eq_one v p hpv
  rw [show (p : F) = algebraMap (𝓞 F) F p from rfl] at h2
  rwa [h2, one_pow, mul_one] at h1

theorem strong_approx (v₀ : HeightOneSpectrum (𝓞 F)) (t : InfiniteAdeleRing F) (s : FiniteAdeleRing (𝓞 F) F)
    (M : ℕ) (hM : M ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : F, c ≠ 0 ∧ (∀ w : InfinitePlace F, ‖algebraMap F w.Completion c - t w‖ < ε) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ≠ v₀ →
        ‖algebraMap F (v.adicCompletion F) c - s v‖ ≤ ‖(M : v.adicCompletion F)‖ := by
  have hMF : (M : F) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hMR : (0 : ℝ) < M := Nat.cast_pos.2 (Nat.pos_of_ne_zero hM)
  obtain ⟨u, hu⟩ := PI.UnipApproxD.IntegersDenseFiniteAdeles.exists_approx_adele
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) (M : F)⁻¹ * s)
  obtain ⟨C, hC, hCt⟩ := exists_int_near F
  obtain ⟨x, hx0, hxw, hxv⟩ := exists_small_elt v₀ (ε / (M * (C + 1))) (by positivity)
  obtain ⟨o, ho⟩ := hCt fun w => (t w - algebraMap F w.Completion (M * u)) / algebraMap F w.Completion (M * x)
  have key : ∀ o' : 𝓞 F, (∀ w : InfinitePlace F, ‖algebraMap F w.Completion (o' : F) -
      (t w - algebraMap F w.Completion (M * u)) / algebraMap F w.Completion (M * x)‖ < C + 1) →
      (∀ w : InfinitePlace F, ‖algebraMap F w.Completion (M * u + M * x * o') - t w‖ < ε) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ≠ v₀ →
        ‖algebraMap F (v.adicCompletion F) (M * u + M * x * o') - s v‖ ≤ ‖(M : v.adicCompletion F)‖ := by
    intro o' ho'
    refine ⟨fun w => ?_, fun v hv => ?_⟩
    · have h0 : algebraMap F w.Completion (M * x) ≠ 0 := (map_ne_zero _).2 (mul_ne_zero hMF hx0)
      have e : algebraMap F w.Completion (M * u + M * x * o') - t w = algebraMap F w.Completion (M * x) *
          (algebraMap F w.Completion (o' : F) -
            (t w - algebraMap F w.Completion (M * u)) / algebraMap F w.Completion (M * x)) := by
        rw [map_add (f := _), map_mul _ (M * x), mul_sub, mul_div_cancel₀ _ h0]; ring
      rw [e, norm_mul, norm_alg_inf, map_mul, InfinitePlace.map_natCast]
      calc _ ≤ (M * w x) * (C + 1) := mul_le_mul_of_nonneg_left (ho' w).le (by positivity)
        _ < (M * (ε / (M * (C + 1)))) * (C + 1) := by gcongr; exact hxw w
        _ = ε := by field_simp
    · have h0 := nat_ne_zero_fin v hM
      have hu' : ‖algebraMap F (v.adicCompletion F) (M : F)⁻¹ * s v - algebraMap F (v.adicCompletion F) u‖ ≤ 1 :=
        (norm_le_one_iff_int v _).2 (hu v)
      have e : algebraMap F (v.adicCompletion F) (M * u + M * x * o') - s v = (M : v.adicCompletion F) *
          (-(algebraMap F (v.adicCompletion F) (M : F)⁻¹ * s v - algebraMap F (v.adicCompletion F) u) +
            algebraMap F (v.adicCompletion F) x * algebraMap F (v.adicCompletion F) (o' : F)) := by
        simp only [map_add (f := _), map_mul, map_inv₀, map_natCast]
        field_simp
        ring
      rw [e, norm_mul]
      refine mul_le_of_le_one_right (norm_nonneg _) ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_))
      · rwa [norm_neg]
      · rw [norm_mul]; exact mul_le_one₀ (hxv v hv) (norm_nonneg _) (norm_int_le_one v o')
  by_cases hc : (M : F) * u + M * x * o = 0
  · refine ⟨M * u + M * x * (o + 1 : 𝓞 F), ?_, key (o + 1) fun w => ?_⟩
    · have : (M : F) * u + M * x * (o + 1 : 𝓞 F) = M * x := by push_cast; linear_combination hc
      rw [this]; exact mul_ne_zero hMF hx0
    · have h1 := norm_add_le (1 : w.Completion) (algebraMap F w.Completion (o : F) -
        (t w - algebraMap F w.Completion (M * u)) / algebraMap F w.Completion (M * x))
      have e : ((o + 1 : 𝓞 F) : F) = 1 + o := by push_cast; ring
      rw [e, map_add (f := _), map_one, add_sub_assoc]
      rw [norm_one] at h1
      linarith [ho w]
  · exact ⟨_, hc, key o fun w => (ho w).trans (lt_add_one C)⟩

end GlobalTheory.HeckeSplitAll.Approx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
section
noncomputable section
open ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.PlaceModel Filter
open scoped Topology

namespace GlobalTheory.LocMod.Inhab

theorem exists_fixed {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℂ V] {χ : G → G → ℂ} (h : IsBichar χ)
    (ρ σ : G → V →ₗ[ℂ] V) (hρ : ∀ x x' f, ρ x (ρ x' f) = ρ (x + x') f) (hσ : ∀ y f, σ y f = 0 → f = 0)
    (hc : ∀ x y f, ρ x (σ y f) = χ x y • σ y (ρ x f)) (L K : AddSubgroup G) [Finite (L ⧸ K.addSubgroupOf L)]
    (hsep : ∀ u ∈ L, u ∉ K → ∃ y, (∀ κ ∈ K, χ κ y = 1) ∧ χ u y ≠ 1) (P : Submodule ℂ V)
    (hP : ∀ u ∈ L, ∀ f ∈ P, ρ u f ∈ P) (hP' : ∀ y, ∀ f ∈ P, σ y f ∈ P) {f : V} (hf : f ∈ P) (f0 : f ≠ 0)
    (hK : ∀ κ ∈ K, ρ κ f = f) : ∃ g ∈ P, g ≠ 0 ∧ ∀ u ∈ L, ρ u g = g := by
  classical
  letI : Fintype (L ⧸ K.addSubgroupOf L) := Fintype.ofFinite _
  let A : AddSubgroup G :=
    { carrier := {y | ∀ κ ∈ K, χ κ y = 1}
      zero_mem' := fun κ _ => h.zero_right κ
      add_mem' := fun {a b} ha hb κ hκ => by rw [h.right, ha κ hκ, hb κ hκ, mul_one]
      neg_mem' := fun {a} ha κ hκ => by
        have := h.right κ a (-a)
        rwa [add_neg_cancel, h.zero_right, ha κ hκ, one_mul, eq_comm] at this }
  have hcl : ∀ g : V, (∀ κ ∈ K, ρ κ g = g) → ∀ a b : L,
      (QuotientAddGroup.mk a : L ⧸ K.addSubgroupOf L) = QuotientAddGroup.mk b → ρ a g = ρ b g := fun g hg a b hab => by
    have : -(a : G) + b ∈ K := (QuotientAddGroup.eq (s := K.addSubgroupOf L)).1 hab
    rw [← hg _ this, hρ, add_neg_cancel_left, hg _ this]
  by_contra hcon
  have hz : ∀ y ∈ A, ∑ q : L ⧸ K.addSubgroupOf L, χ (q.out : L) y • ρ (q.out : L) f = 0 := fun y hy => by
    have hfix : ∀ κ ∈ K, ρ κ (σ y f) = σ y f := fun κ hκ => by rw [hc, hy κ hκ, hK κ hκ, one_smul]
    refine hσ y _ ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, ← hc]
    by_contra hne
    refine hcon ⟨_, P.sum_mem fun q _ => hP _ (q.out : L).2 _ (hP' y f hf), hne, fun u hu => ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Fintype.sum_equiv (Equiv.addLeft (QuotientAddGroup.mk (⟨u, hu⟩ : L))) _ _ fun q => ?_
    rw [hρ]
    refine hcl _ hfix (⟨u, hu⟩ + q.out) _ ?_
    simp
  let ch : (L ⧸ K.addSubgroupOf L) → (Multiplicative A →* ℂ) := fun q =>
    { toFun := fun y => χ (q.out : L) (y.toAdd : A)
      map_one' := h.zero_right _
      map_mul' := fun a b => h.right _ _ _ }
  have hinj : Function.Injective ch := by
    intro q q' hq
    rw [← q.out_eq', ← q'.out_eq', QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    by_contra hn
    obtain ⟨y, hy, hne⟩ := hsep _ (-q.out + q'.out : L).2 hn
    have e : χ (q.out : L) y = χ (q'.out : L) y := DFunLike.congr_fun hq (Multiplicative.ofAdd ⟨y, hy⟩)
    rw [AddSubgroup.coe_add, AddSubgroup.coe_neg, h.left, ← e, h.neg_mul] at hne
    exact hne rfl
  have hli := (linearIndependent_monoidHom (Multiplicative A) ℂ).comp ch hinj
  rw [Fintype.linearIndependent_iff] at hli
  refine f0 ((Module.forall_dual_apply_eq_zero_iff ℂ f).1 fun ℓ => ?_)
  have := hli (fun q => ℓ (ρ (q.out : L) f)) (by
    funext y
    have := congrArg ℓ (hz _ y.toAdd.2)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, map_zero] at this
    rw [Finset.sum_apply]
    refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) this
    simp [ch, mul_comm]) (QuotientAddGroup.mk 0)
  rwa [hcl f hK _ 0 (QuotientAddGroup.out_eq' _), hK ((0 : L) : G) K.zero_mem] at this

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

variable (Y Y') in
def box (a : kˣ) : AddSubgroup (Matrix Y Y' k) where
  carrier := {x | ∀ r q, valuation k (x r q) ≤ valuation k (a : k)}
  zero_mem' := fun r q => by simp
  add_mem' := fun ha hb r q => Valuation.map_add_le _ (ha r q) (hb r q)
  neg_mem' := fun ha r q => by simpa using ha r q

theorem box_eq (a : kˣ) :
    (box Y Y' a : Set (Matrix Y Y' k)) = Set.pi Set.univ fun _ : Y => Set.pi Set.univ fun _ : Y' => cball a := by
  ext x
  exact ⟨fun h r _ q _ => h r q, fun h r q => h r trivial q trivial⟩

theorem isCompact_box (a : kˣ) : IsCompact (box Y Y' a : Set (Matrix Y Y' k)) := by
  rw [box_eq]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_cball a

theorem isOpen_box (a : kˣ) : IsOpen (box Y Y' a : Set (Matrix Y Y' k)) := by
  rw [box_eq]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball a

theorem finite_box (a b : kˣ) : Finite (box Y Y' a ⧸ (box Y Y' b).addSubgroupOf (box Y Y' a)) := by
  haveI : CompactSpace (box Y Y' a) := isCompact_iff_compactSpace.1 (isCompact_box a)
  exact AddSubgroup.quotient_finite_of_isOpen _ ((isOpen_box b).preimage continuous_subtype_val)

theorem exists_box_subset {U : Set (Matrix Y Y' k)} (hU : U ∈ 𝓝 0) : ∃ a : kˣ, ∀ x ∈ box Y Y' a, x ∈ U := by
  have h := (isCompact_box (Y := Y) (Y' := Y') (1 : kˣ)).eventually_forall_of_forall_eventually (x₀ := (0 : k))
    (P := fun c x => c • x ∈ U) fun x _ =>
      (continuous_smul.tendsto' ((0 : k), x) 0 (zero_smul _ _)).eventually hU
  obtain ⟨s, hs⟩ := exists_cball_subset h
  refine ⟨s, fun x hx => ?_⟩
  have := hs (show (s : k) ∈ cball s from le_refl (valuation k (s : k))) ((s : k)⁻¹ • x) fun r q => by
    have h0 : valuation k (s : k) ≠ 0 := by simp
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, Units.val_one, map_one]
    exact inv_mul_le_one_of_le₀ (hx r q) zero_le'
  rwa [smul_inv_smul₀ s.ne_zero] at this

def pairing (ψ : AddChar k Circle) (t b : Matrix Y Y' k) : ℂ := ψ (∑ r, ∑ q, b r q * t r q)

theorem pairing_comm (ψ : AddChar k Circle) (t b : Matrix Y Y' k) : pairing ψ t b = pairing ψ b t := by
  simp only [pairing, mul_comm]

theorem isBichar_pairing (ψ : AddChar k Circle) : IsBichar (pairing (Y := Y) (Y' := Y') ψ) := by
  constructor
  · intro a b y
    simp [pairing, Matrix.add_apply, mul_add, Finset.sum_add_distrib, AddChar.map_add_eq_mul]
  · intro a y z
    simp [pairing, Matrix.add_apply, add_mul, Finset.sum_add_distrib, AddChar.map_add_eq_mul]
  · intro y
    simp [pairing]
  · intro a
    simp [pairing]

theorem pairing_single (ψ : AddChar k Circle) (t : Matrix Y Y' k) (r : Y) (q : Y') (c : k) :
    pairing ψ t (Matrix.single r q c) = ψ (c * t r q) := by
  unfold pairing
  rw [Finset.sum_eq_single r, Finset.sum_eq_single q]
  · simp
  · intro q' _ h; simp [h.symm]
  · simp
  · intro r' _ h; simp [h.symm]
  · simp

theorem pairing_eq_one {ψ : AddChar k Circle} {d : kˣ} (hd : HasConductor ψ d) {t b : Matrix Y Y' k}
    (h : ∀ r q, valuation k (b r q * t r q) ≤ valuation k (d : k)) : pairing ψ t b = 1 := by
  rw [pairing, (hd d).2 le_rfl _ (Valuation.map_sum_le _ fun r _ => Valuation.map_sum_le _ fun q _ => h r q)]
  rfl

theorem exists_sep {ψ : AddChar k Circle} {d : kˣ} (hd : HasConductor ψ d) (a : kˣ) {u : Matrix Y Y' k}
    (hu : u ∉ box Y Y' a) : ∃ y ∈ box Y Y' (d / a), pairing ψ u y ≠ 1 := by
  obtain ⟨r, q, h⟩ : ∃ r q, valuation k (a : k) < valuation k (u r q) := by
    by_contra hh
    push Not at hh
    exact hu hh
  have ha : 0 < valuation k (a : k) := zero_lt_iff.2 (by simp)
  have hd0 : 0 < valuation k (d : k) := zero_lt_iff.2 (by simp)
  have hu0 : 0 < valuation k (u r q) := ha.trans h
  have hne : u r q ≠ 0 := fun e => by simp [e] at hu0
  have : ¬ ∀ z : k, valuation k z ≤ valuation k (u r q * (d / a)) → ψ z = 1 := fun hh => by
    have := (hd _).1 hh
    rw [map_mul, map_div₀, mul_div_left_comm, mul_le_iff_le_one_right hd0, div_le_one₀ ha] at this
    exact absurd h (not_lt.2 this)
  push Not at this
  obtain ⟨z, hz, hz1⟩ := this
  refine ⟨Matrix.single r q (z / u r q), fun r' q' => ?_, ?_⟩
  · rw [Matrix.single_apply]
    split_ifs
    · rw [map_div₀, div_le_iff₀ hu0, mul_comm, ← map_mul]
      simpa using hz
    · simp
  · rw [pairing_single, div_mul_cancel₀ _ hne]
    exact fun e => hz1 (Subtype.ext e)

theorem pairing_box {ψ : AddChar k Circle} {d : kˣ} (hd : HasConductor ψ d) {a : kˣ} {u y : Matrix Y Y' k}
    (hu : u ∈ box Y Y' a) (hy : y ∈ box Y Y' (d / a)) : pairing ψ u y = 1 :=
  pairing_eq_one hd fun r q => by
    rw [map_mul]
    refine (mul_le_mul' (hy r q) (hu r q)).trans_eq ?_
    rw [← map_mul, ← Units.val_mul, div_mul_cancel]

theorem exists_vacuum {V : Type} [AddCommGroup V] [Module ℂ V] {ψ : AddChar k Circle} (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (ρ σ : Matrix Y Y' k → V →ₗ[ℂ] V) (hρ : ∀ x x' f, ρ x (ρ x' f) = ρ (x + x') f)
    (hσ : ∀ x x' f, σ x (σ x' f) = σ (x + x') f) (ρ0 : ∀ f, ρ 0 f = f) (σ0 : ∀ f, σ 0 f = f)
    (hc : ∀ x y f, ρ x (σ y f) = pairing ψ x y • σ y (ρ x f)) (P : Submodule ℂ V)
    (hP : ∀ x, ∀ f ∈ P, ρ x f ∈ P) (hP' : ∀ y, ∀ f ∈ P, σ y f ∈ P)
    (sm : ∀ f ∈ P, ∀ᶠ x in 𝓝 0, ρ x f = f) (sm' : ∀ f ∈ P, ∀ᶠ x in 𝓝 0, σ x f = f) {f : V} (hf : f ∈ P) (f0 : f ≠ 0) :
    ∃ g ∈ P, g ≠ 0 ∧ (∀ x ∈ box Y Y' (1 : kˣ), ρ x g = g) ∧
      ∀ y, (∀ x ∈ box Y Y' (1 : kˣ), pairing ψ x y = 1) → σ y g = g := by
  obtain ⟨d, hd⟩ := exists_hasConductor_of_continuous ψ hψ h1
  have hb := isBichar_pairing (Y := Y) (Y' := Y') ψ
  obtain ⟨a, ha⟩ := exists_box_subset (sm f hf)
  haveI := finite_box (Y := Y) (Y' := Y') 1 a
  obtain ⟨g, hg, g0, hg1⟩ := exists_fixed hb ρ σ hρ
    (fun y f h => by rw [← σ0 f, ← neg_add_cancel y, ← hσ, h, map_zero]) hc (box Y Y' 1) (box Y Y' a)
    (fun u _ hu => let ⟨y, hy, hne⟩ := exists_sep hd a hu; ⟨y, fun κ hκ => pairing_box hd hκ hy, hne⟩)
    P (fun u _ => hP u) hP' hf f0 ha
  obtain ⟨b, hb'⟩ := exists_box_subset (sm' g hg)
  haveI := finite_box (Y := Y) (Y' := Y') (d / 1) b
  let Q : Submodule ℂ V :=
    { carrier := {v | v ∈ P ∧ ∀ x ∈ box Y Y' (1 : kˣ), ρ x v = v}
      zero_mem' := ⟨P.zero_mem, fun _ _ => map_zero _⟩
      add_mem' := fun h h' => ⟨P.add_mem h.1 h'.1, fun x hx => by rw [map_add (f := _), h.2 x hx, h'.2 x hx]⟩
      smul_mem' := fun c _ h => ⟨P.smul_mem c h.1, fun x hx => by rw [map_smul, h.2 x hx]⟩ }
  have hb2 : IsBichar fun y x : Matrix Y Y' k => pairing ψ (-x) y :=
    ⟨fun a b y => hb.right _ _ _, fun a y z => by rw [neg_add, hb.left], fun y => hb.zero_right _,
      fun a => by rw [neg_zero, hb.zero_left]⟩
  obtain ⟨g', hg', g0', hg2⟩ := exists_fixed hb2 σ ρ hσ
    (fun y f h => by rw [← ρ0 f, ← neg_add_cancel y, ← hρ, h, map_zero])
    (fun y x f => by rw [hc, smul_smul, hb.neg_mul, one_smul]) (box Y Y' (d / 1)) (box Y Y' b)
    (fun u _ hu => by
      obtain ⟨y, hy, hne⟩ := exists_sep hd b hu
      refine ⟨-y, fun κ hκ => ?_, ?_⟩
      · rw [neg_neg, pairing_comm]
        exact pairing_box hd hκ hy
      · rwa [neg_neg, pairing_comm])
    Q (fun u hu v hv => ⟨hP' u v hv.1, fun x hx => by rw [hc, pairing_box hd hx hu, hv.2 x hx, one_smul]⟩)
    (fun y v hv => ⟨hP y v hv.1, fun x hx => by rw [hρ, add_comm, ← hρ, hv.2 x hx]⟩) ⟨hg, hg1⟩ g0 hb'
  refine ⟨g', hg'.1, g0', hg'.2, fun y hy => hg2 y ?_⟩
  by_contra hn
  obtain ⟨x, hx, hne⟩ := exists_sep hd _ hn
  rw [div_one, div_self'] at hx
  exact hne ((pairing_comm ψ y x).trans (hy x hx))

end GlobalTheory.LocMod.Inhab
end
end

