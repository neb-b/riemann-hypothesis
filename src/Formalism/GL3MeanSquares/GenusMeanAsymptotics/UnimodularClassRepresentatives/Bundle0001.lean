module

public import Mathlib

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardFilterResCharLe
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.IdealNormInequalities

variable {K : Type} [Field K] [NumberField K]

def resChar (P : Ideal (𝓞 K)) : ℕ := Ideal.absNorm (P.under ℤ)

theorem span_resChar (P : Ideal (𝓞 K)) : Ideal.span {(resChar P : ℤ)} = P.under ℤ := Int.ideal_span_absNorm_eq_self _

theorem under_ne_bot {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : P.under ℤ ≠ ⊥ := by
  intro h
  have hPb : P = ⊥ := Ideal.eq_bot_of_comap_eq_bot h
  exact Ring.ne_bot_of_isMaximal_of_not_isField hP (NumberField.RingOfIntegers.not_isField K) hPb

theorem under_isMaximal {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : (P.under ℤ).IsMaximal := by
  haveI := hP
  exact Ideal.IsMaximal.under ℤ P

theorem resChar_prime {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : (resChar P).Prime := by

  have h1 := span_resChar P
  have hmax := under_isMaximal hP
  rw [← h1] at hmax
  have hne : ((resChar P : ℕ) : ℤ) ≠ 0 := by
    intro h0
    apply under_ne_bot hP
    rw [← h1, h0]
    simp
  have hpr := (Ideal.span_singleton_prime hne).mp hmax.isPrime
  exact Nat.prime_iff_prime_int.mpr hpr

theorem exists_absNorm_eq_pow {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    ∃ k : ℕ, 1 ≤ k ∧ Ideal.absNorm P = resChar P ^ k := by

  have hp := resChar_prime hP
  haveI : P.LiesOver (Ideal.span {((resChar P : ℕ) : ℤ)}) := ⟨span_resChar P⟩
  have h1 := Ideal.absNorm_eq_pow_inertiaDeg P (Nat.prime_iff_prime_int.mp hp)
  rw [show (((resChar P : ℕ) : ℤ)).natAbs = resChar P by simp] at h1
  refine ⟨_, ?_, h1⟩
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rw [h0, pow_zero, Ideal.absNorm_eq_one_iff] at h1
  exact hP.ne_top h1

theorem resChar_le_absNorm {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    resChar P ≤ Ideal.absNorm P := by

  obtain ⟨k, hk, hk2⟩ := exists_absNorm_eq_pow hP
  rw [hk2]
  exact Nat.le_self_pow (by omega) _

theorem resChar_le_of_sq {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {q : ℕ}
    (hq : Ideal.absNorm P = q ^ 2) : resChar P ≤ q := by

  obtain ⟨k, hk, hk2⟩ := exists_absNorm_eq_pow hP
  have hp := resChar_prime hP
  have hdvd : resChar P ∣ q ^ 2 := by
    rw [← hq, hk2]
    exact dvd_pow_self _ (by omega)
  have hq0 : q ≠ 0 := by
    rintro rfl
    have h0 : resChar P ^ k = 0 := by rw [← hk2, hq]; simp
    exact hp.ne_zero (pow_eq_zero_iff (by omega) |>.mp h0)
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) (hp.dvd_of_dvd_pow hdvd)

set_option linter.deprecated false in
theorem card_filter_resChar_le (s : Finset {P : Ideal (𝓞 K) // P.IsMaximal}) (n : ℕ) :
    (s.filter (fun P => resChar P.1 = n)).card ≤ finrank ℚ K := by

  classical
  by_cases hn : ∃ P ∈ s, resChar P.1 = n
  · obtain ⟨P0, -, hP0⟩ := hn
    have hJ : Ideal.span {((n : ℕ) : ℤ)} = P0.1.under ℤ := by
      rw [← hP0]
      exact span_resChar P0.1
    haveI : (Ideal.span {((n : ℕ) : ℤ)}).IsMaximal := by
      rw [hJ]
      exact under_isMaximal P0.2
    have hJne : Ideal.span {((n : ℕ) : ℤ)} ≠ ⊥ := by
      rw [hJ]
      exact under_ne_bot P0.2
    calc (s.filter (fun P => resChar P.1 = n)).card
        ≤ (IsDedekindDomain.primesOverFinset (Ideal.span {((n : ℕ) : ℤ)}) (𝓞 K)).card := by
          refine Finset.card_le_card_of_injOn (fun P => P.1) (by
            intro P hP
            rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hJne]
            obtain ⟨-, hPn⟩ := Finset.mem_filter.mp hP
            refine ⟨P.2.isPrime, ⟨?_⟩⟩
            rw [← hPn]
            exact span_resChar P.1) (fun a _ b _ h => Subtype.ext h)
      _ ≤ finrank ℚ K := Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hJne
  · push_neg at hn
    rw [Finset.filter_false_of_mem (fun P hP => hn P hP)]
    simp

theorem summable_resChar_sq :
    Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => ((resChar P.1 : ℝ) ^ 2)⁻¹) := by

  classical
  have hs : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := Real.summable_nat_pow_inv.mpr (by norm_num)
  refine summable_of_sum_le (c := (finrank ℚ K : ℝ) * ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹) (fun P => by positivity)
    (fun u => ?_)
  calc ∑ P ∈ u, ((resChar P.1 : ℝ) ^ 2)⁻¹
      = ∑ n ∈ u.image (fun P => resChar P.1),
          ∑ P ∈ u.filter (fun P => resChar P.1 = n), ((resChar P.1 : ℝ) ^ 2)⁻¹ :=
        (Finset.sum_fiberwise_of_maps_to (fun P hP => Finset.mem_image_of_mem _ hP) _).symm
    _ = ∑ n ∈ u.image (fun P => resChar P.1),
          ((u.filter (fun P => resChar P.1 = n)).card : ℝ) * ((n : ℝ) ^ 2)⁻¹ := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [Finset.sum_congr rfl (fun P hP => by rw [(Finset.mem_filter.mp hP).2]), Finset.sum_const,
          nsmul_eq_mul]
    _ ≤ ∑ n ∈ u.image (fun P => resChar P.1), (finrank ℚ K : ℝ) * ((n : ℝ) ^ 2)⁻¹ := by
        refine Finset.sum_le_sum (fun n _ => ?_)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast card_filter_resChar_le u n
    _ = (finrank ℚ K : ℝ) * ∑ n ∈ u.image (fun P => resChar P.1), ((n : ℝ) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ (finrank ℚ K : ℝ) * ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hs.sum_le_tsum _ (fun n _ => by positivity)

end Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DiscreteTopologyOfZsmul
section
open MeasureTheory Module ZSpan Filter Topology Pointwise Bornology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (μ : Measure E) [μ.IsAddHaarMeasure]

private theorem volume_image_equivFun_eq_map_symm {ι : Type*} [Fintype ι] (B : Basis ι ℝ E)
    (s : Set E) : volume (B.equivFun '' s) = Measure.map B.equivFunL.symm volume s := by
  rw [LinearEquiv.image_eq_preimage_symm]
  exact (B.equivFunL.symm.toHomeomorph.toMeasurableEquiv.map_apply s).symm

private theorem volume_image_equivFun_fundamentalDomain_eq_one {ι : Type*} [Fintype ι] (B : Basis ι ℝ E) :
    volume (B.equivFun '' fundamentalDomain B) = 1 := by
  have h : B.equivFun '' fundamentalDomain B = Set.univ.pi fun _ : ι ↦ Set.Ico (0 : ℝ) 1 := by
    ext x
    simp only [Set.mem_image, mem_fundamentalDomain, Set.mem_univ_pi]
    constructor
    · rintro ⟨m, hm, rfl⟩ i
      simpa [Basis.equivFun_apply] using hm i
    · intro hx
      refine ⟨B.equivFun.symm x, fun i ↦ ?_, B.equivFun.apply_symm_apply x⟩
      have hxi := congrFun (B.equivFun.apply_symm_apply x) i
      rw [Basis.equivFun_apply] at hxi
      rw [hxi]
      exact hx i
  rw [h, volume_pi_pi]
  simp

private theorem covolume_eq_addHaarScalarFactor_mul_covolume (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ν ν' : Measure E) [ν.IsAddHaarMeasure] [ν'.IsAddHaarMeasure] :
    ZLattice.covolume Λ ν =
      (Measure.addHaarScalarFactor ν ν' : ℝ) * ZLattice.covolume Λ ν' := by
  have h := Measure.isAddLeftInvariant_eq_smul ν ν'
  let b := Module.Free.chooseBasis ℤ Λ
  rw [ZLattice.covolume_eq_measure_fundamentalDomain Λ ν (ZLattice.isAddFundamentalDomain b ν),
    ZLattice.covolume_eq_measure_fundamentalDomain Λ ν' (ZLattice.isAddFundamentalDomain b ν')]
  generalize Measure.addHaarScalarFactor ν ν' = c at h ⊢
  rw [h]
  exact measureReal_nnreal_smul_apply _

theorem volume_image_equivFun {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) (s : Set E) :
    volume ((b.ofZLatticeBasis ℝ L).equivFun '' s) =
      μ s / ENNReal.ofReal (ZLattice.covolume L μ) := by
  obtain ⟨ν, hν⟩ : ∃ ν : Measure E,
      ν = Measure.map (b.ofZLatticeBasis ℝ L).equivFunL.symm volume := ⟨_, rfl⟩
  have : ν.IsAddHaarMeasure := hν ▸ inferInstance
  have hcov : ZLattice.covolume L ν = 1 := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L ν (ZLattice.isAddFundamentalDomain b ν),
      measureReal_def, hν, ← volume_image_equivFun_eq_map_symm, volume_image_equivFun_fundamentalDomain_eq_one,
      ENNReal.toReal_one]
  rw [volume_image_equivFun_eq_map_symm, ← hν, covolume_eq_addHaarScalarFactor_mul_covolume L μ ν, hcov, mul_one,
    ENNReal.ofReal_coe_nnreal]
  have hc := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν
  have h := Measure.isAddLeftInvariant_eq_smul μ ν
  generalize Measure.addHaarScalarFactor μ ν = c at hc h ⊢
  have hc0 : (c : ENNReal) ≠ 0 := by simpa using hc.ne'
  rw [h, Measure.coe_nnreal_smul_apply, mul_comm, ENNReal.mul_div_cancel_right hc0 ENNReal.coe_ne_top]

theorem tendsto_card_div_pow {s : Set E} (hs₁ : IsBounded s) (hs₂ : MeasurableSet s)
    (hs₃ : μ (frontier s) = 0) :
    Tendsto (fun n : ℕ ↦ (Nat.card (s ∩ (n : ℝ)⁻¹ • L : Set E) : ℝ) / n ^ finrank ℝ E)
      atTop (𝓝 (μ.real s / ZLattice.covolume L μ)) := by
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = finrank ℝ E := by
    rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]
  have hfr : frontier (((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).equivFun '' s) =
      ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).equivFun '' frontier s :=
    (((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).equivFunL.toHomeomorph.image_frontier
      s).symm
  have hlim : volume.real (((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).equivFun '' s) =
      μ.real s / ZLattice.covolume L μ := by
    rw [measureReal_def, volume_image_equivFun L μ, ENNReal.toReal_div,
      ENNReal.toReal_ofReal (ZLattice.covolume_pos L μ).le, measureReal_def]
  have key := ZLattice.covolume.tendsto_card_div_pow'' (Module.Free.chooseBasis ℤ L) hs₁ hs₂
    (by rw [hfr, volume_image_equivFun L μ, hs₃, ENNReal.zero_div])
  rw [hlim, hcard] at key
  exact key

set_option backward.isDefEq.respectTransparency.types false in
theorem covolume_div_covolume (L₁ L₂ : Submodule ℤ E) [DiscreteTopology L₁] [IsZLattice ℝ L₁]
    [DiscreteTopology L₂] [IsZLattice ℝ L₂] (h : L₁ ≤ L₂) :
    ZLattice.covolume L₁ μ / ZLattice.covolume L₂ μ =
      L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by
  obtain ⟨ν, hν⟩ : ∃ ν : Measure E,
      ν = Measure.map (Module.finBasis ℝ E).equivFunL.symm volume := ⟨_, rfl⟩
  have : ν.IsAddHaarMeasure := hν ▸ inferInstance
  have he : MeasurePreserving (Module.finBasis ℝ E).equivFunL.symm volume ν := by
    rw [hν]
    exact (Module.finBasis ℝ E).equivFunL.symm.continuous.measurable.measurePreserving _
  have hc := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν
  rw [covolume_eq_addHaarScalarFactor_mul_covolume L₁ μ ν, covolume_eq_addHaarScalarFactor_mul_covolume L₂ μ ν,
    mul_div_mul_left _ _ (NNReal.coe_pos.mpr hc).ne', ← ZLattice.covolume_comap L₁ ν volume he,
    ← ZLattice.covolume_comap L₂ ν volume he,
    ZLattice.covolume_div_covolume_eq_relIndex _ _ (fun _ h' ↦ h h'),
    ZLattice.comap_toAddSubgroup, ZLattice.comap_toAddSubgroup, Nat.cast_inj,
    LinearEquiv.toAddMonoidHom_commutes, AddSubgroup.comap_equiv_eq_map_symm',
    AddSubgroup.comap_equiv_eq_map_symm',
    AddSubgroup.relIndex_map_map_of_injective _ _ (Module.finBasis ℝ E).equivFunL.injective]

theorem discreteTopology_of_zsmul {Λ₁ Λ : Submodule ℤ E} [DiscreteTopology Λ₁] {N : ℤ}
    (hN : N ≠ 0) (h : ∀ y ∈ Λ, N • y ∈ Λ₁) : DiscreteTopology Λ := by
  refine DiscreteTopology.of_continuous_injective (β := Λ₁)
    (f := fun y : Λ ↦ (⟨N • (y : E), h y y.2⟩ : Λ₁)) ?_ ?_
  · exact ((continuous_zsmul N).comp continuous_subtype_val).subtype_mk _
  · intro y z hyz
    have h' : N • (y : E) = N • (z : E) := congrArg Subtype.val hyz
    rw [← Int.cast_smul_eq_zsmul ℝ N (y : E), ← Int.cast_smul_eq_zsmul ℝ N (z : E)] at h'
    exact Subtype.ext (smul_right_injective E (Int.cast_ne_zero.mpr hN) h')

theorem tendsto_card_of_le (Λ₁ Λ : Submodule ℤ E) [DiscreteTopology Λ₁] [IsZLattice ℝ Λ₁]
    (hle : Λ₁ ≤ Λ) {N : ℤ} (hN : N ≠ 0) (h : ∀ y ∈ Λ, N • y ∈ Λ₁) {s : Set E}
    (hs₁ : IsBounded s) (hs₂ : MeasurableSet s) (hs₃ : Convex ℝ s) :
    Λ₁.toAddSubgroup.relIndex Λ.toAddSubgroup ≠ 0 ∧
    Tendsto (fun n : ℕ ↦ (Nat.card (s ∩ (n : ℝ)⁻¹ • Λ : Set E) : ℝ) / n ^ finrank ℝ E)
      atTop (𝓝 (μ.real s * (Λ₁.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) /
        ZLattice.covolume Λ₁ μ)) := by
  have : DiscreteTopology Λ := discreteTopology_of_zsmul hN h
  have : IsZLattice ℝ Λ := ⟨by
    rw [eq_top_iff, ← IsZLattice.span_top (K := ℝ) (L := Λ₁)]
    exact Submodule.span_mono hle⟩
  have hidx := covolume_div_covolume μ Λ₁ Λ hle
  have h₁ := (ZLattice.covolume_pos Λ₁ μ).ne'
  have h₂ := (ZLattice.covolume_pos Λ μ).ne'
  have hne : (Λ₁.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) ≠ 0 := by
    rw [← hidx]
    exact div_ne_zero h₁ h₂
  refine ⟨by exact_mod_cast hne, ?_⟩
  have key := tendsto_card_div_pow Λ μ hs₁ hs₂ (hs₃.addHaar_frontier μ)
  convert key using 2
  rw [← hidx]
  field_simp

end Formalism.HermitianLattices.Ext.L3.BallA
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsMulSubOneMemPow
section
open Module

set_option linter.deprecated false

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.MeanA

theorem exists_mul_sub_one_mem_pow {R : Type*} [CommRing R] {𝔭 : Ideal R} (h𝔭 : 𝔭.IsMaximal) {t : R}
    (ht : t ∉ 𝔭) (k : ℕ) : ∃ u : R, u * t - 1 ∈ 𝔭 ^ k := by
  obtain ⟨y, i, hi, hyi⟩ := h𝔭.exists_inv ht
  refine ⟨(∑ j ∈ Finset.range k, i ^ j) * y, ?_⟩
  have h1 : (∑ j ∈ Finset.range k, i ^ j) * (i - 1) = i ^ k - 1 := geom_sum_mul i k
  have h2 : (∑ j ∈ Finset.range k, i ^ j) * y * t - 1 = -(i ^ k) := by
    linear_combination (∑ j ∈ Finset.range k, i ^ j) * hyi - h1
  rw [h2]
  exact (𝔭 ^ k).neg_mem (Ideal.pow_mem_pow hi k)

theorem mem_pow_of_mul_mem {R : Type*} [CommRing R] {𝔭 : Ideal R} (h𝔭 : 𝔭.IsMaximal) {t c : R}
    (ht : t ∉ 𝔭) {k : ℕ} (h : t * c ∈ 𝔭 ^ k) : c ∈ 𝔭 ^ k := by
  obtain ⟨u, hu⟩ := exists_mul_sub_one_mem_pow h𝔭 ht k
  have e : c = u * (t * c) - (u * t - 1) * c := by ring
  rw [e]
  exact Ideal.sub_mem _ (Ideal.mul_mem_left _ u h) (Ideal.mul_mem_right c _ hu)

variable {R F V : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F]
  [IsFractionRing R F] [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
  [FiniteDimensional F V]

theorem exists_local_basis (M : Submodule R V) (hfg : M.FG)
    (hspan : Submodule.span F (M : Set V) = ⊤) {𝔭 : Ideal R} (h𝔭 : 𝔭.IsMaximal) :
    ∃ (x : Fin (finrank F V) → M) (s : R), s ∉ 𝔭 ∧ LinearIndependent R x ∧
      ∀ v : M, s • v ∈ Submodule.span R (Set.range x) := by
  have := h𝔭
  let : Field (R ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  have : Module.Finite R M := Module.Finite.iff_fg.2 hfg
  let Q := M ⧸ (𝔭 • ⊤ : Submodule R M)
  have : Module.Finite (R ⧸ 𝔭) Q := Module.Finite.of_restrictScalars_finite R _ _
  let b := Module.finBasis (R ⧸ 𝔭) Q
  choose x hx using fun i => Submodule.Quotient.mk_surjective _ (b i)
  have hli : LinearIndependent F (M.subtype ∘ x) := by
    refine Ideal.FinrankQuotientMap.linearIndependent_of_nontrivial (S := R ⧸ 𝔭) F ?_ M.subtype
      M.injective_subtype (Submodule.mkQ (𝔭 • ⊤ : Submodule R M)) ?_
    · rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]; exact h𝔭.ne_top
    · have : (Submodule.mkQ (𝔭 • ⊤ : Submodule R M)) ∘ x = b := by
        funext i; exact hx i
      rw [this]; exact b.linearIndependent
  have hsup : (⊤ : Submodule R M) ≤ Submodule.span R (Set.range x) ⊔ 𝔭 • ⊤ := by
    intro v _
    have hv : (Submodule.Quotient.mk v : Q) ∈ Submodule.span (R ⧸ 𝔭) (Set.range b) := b.mem_span _
    rw [← @Submodule.restrictScalars_mem R,
      Submodule.restrictScalars_span R (R ⧸ 𝔭) Ideal.Quotient.mk_surjective] at hv
    have hb : Set.range b = (Submodule.mkQ (𝔭 • ⊤ : Submodule R M)) '' Set.range x := by
      rw [← Set.range_comp]; congr 1; funext i; exact (hx i).symm
    rw [hb, ← Submodule.map_span] at hv
    obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 hv
    rw [Submodule.mkQ_apply, Submodule.Quotient.eq] at e
    have : v = y - (y - v) := by abel
    rw [this]
    exact sub_mem (Submodule.mem_sup_left hy) (Submodule.mem_sup_right e)
  obtain ⟨s, hs1, hs⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (Module.Finite.fg_top (R := R) (M := M)) le_rfl hsup
  have hs𝔭 : s ∉ 𝔭 := fun h => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 (by
    have := sub_mem h hs1; simpa using this))
  have hsv : ∀ v : M, s • v ∈ Submodule.span R (Set.range x) := fun v =>
    hs (Submodule.smul_mem_pointwise_smul v s ⊤ trivial)
  have hs0 : algebraMap R F s ≠ 0 := by
    intro h0
    have : s = 0 := (IsFractionRing.injective R F) (by rw [h0, map_zero])
    exact hs𝔭 (this ▸ 𝔭.zero_mem)
  have hsp : ⊤ ≤ Submodule.span F (Set.range (M.subtype ∘ x)) := by
    rw [← hspan, Submodule.span_le]
    intro v hv
    have h1 := hsv ⟨v, hv⟩
    have h2 : (s • v : V) ∈ Submodule.span F (Set.range (M.subtype ∘ x)) := by
      have h3 : M.subtype (s • ⟨v, hv⟩) ∈ (Submodule.span R (Set.range x)).map M.subtype :=
        Submodule.mem_map_of_mem h1
      rw [Submodule.map_span, ← Set.range_comp] at h3
      exact Submodule.span_le_restrictScalars R F _ h3
    have h4 : v = (algebraMap R F s)⁻¹ • (s • v) := by
      rw [← algebraMap_smul F s v, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [h4]
    exact Submodule.smul_mem _ _ h2
  have hcard : finrank (R ⧸ 𝔭) Q = finrank F V := by
    have := finrank_eq_card_basis (Basis.mk hli hsp)
    simpa using this.symm
  have hliR : LinearIndependent R x := by
    have := hli.restrict_scalars (R := R) (by
      intro a b hab
      simpa [Algebra.smul_def] using hab |> fun h => (IsFractionRing.injective R F) (by simpa [Algebra.smul_def] using h))
    exact LinearIndependent.of_comp M.subtype this
  refine ⟨x ∘ Fin.cast hcard.symm, s, hs𝔭, hliR.comp _ (Fin.cast_injective _), fun v => ?_⟩
  have : Set.range (x ∘ Fin.cast hcard.symm) = Set.range x :=
    (Fin.castOrderIso hcard.symm).surjective.range_comp x
  rw [this]; exact hsv v

theorem card_quot_pow_smul_top (M : Submodule R V) (hfg : M.FG)
    (hspan : Submodule.span F (M : Set V) = ⊤) {𝔭 : Ideal R} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    Nat.card (M ⧸ (𝔭 ^ k • ⊤ : Submodule R M)) = Nat.card (R ⧸ 𝔭 ^ k) ^ finrank F V := by
  obtain ⟨x, s, hs, hli, hsx⟩ := exists_local_basis M hfg hspan h𝔭
  let φ : (Fin (finrank F V) → R) →ₗ[R] M :=
    { toFun := fun c => ∑ i, c i • x i
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by simp [Finset.smul_sum, smul_smul] }
  have hφ : ∀ c, φ c = ∑ i, c i • x i := fun c => rfl
  let ψ := (𝔭 ^ k • ⊤ : Submodule R M).mkQ ∘ₗ φ
  have hP : ∀ v ∈ (𝔭 ^ k • ⊤ : Submodule R M), ∃ d : Fin (finrank F V) → R,
      (∀ i, d i ∈ 𝔭 ^ k) ∧ s • v = ∑ i, d i • x i := by
    intro v hv
    refine Submodule.smul_induction_on hv ?_ ?_
    · intro a ha m _
      obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp (hsx m)
      refine ⟨fun i => a * r i, fun i => Ideal.mul_mem_right _ _ ha, ?_⟩
      rw [smul_comm s a m, ← hr, Finset.smul_sum]
      simp only [smul_smul]
    · intro v w hv hw
      obtain ⟨d, hd, hd'⟩ := hv
      obtain ⟨d', hd2, hd2'⟩ := hw
      refine ⟨d + d', fun i => Ideal.add_mem _ (hd i) (hd2 i), ?_⟩
      rw [smul_add, hd', hd2']
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨u, hu⟩ := exists_mul_sub_one_mem_pow h𝔭 hs k
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp (hsx m)
    refine ⟨fun i => u * r i, ?_⟩
    show Submodule.Quotient.mk (φ (fun i => u * r i)) = Submodule.Quotient.mk m
    rw [hφ, Submodule.Quotient.eq]
    have e : ∑ i, (u * r i) • x i - m = (u * s - 1) • m := by
      simp only [mul_smul, ← Finset.smul_sum, hr, sub_smul, one_smul]
    rw [e]
    exact Submodule.smul_mem_smul hu Submodule.mem_top
  have hker : LinearMap.ker ψ = Submodule.pi Set.univ (fun _ => 𝔭 ^ k) := by
    ext c
    rw [LinearMap.mem_ker, Submodule.mem_pi]
    show Submodule.Quotient.mk (φ c) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, hφ]
    constructor
    · intro hc i _
      obtain ⟨d, hd, hsd⟩ := hP _ hc
      have h0 : ∑ i, (s * c i - d i) • x i = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, ← hsd, sub_self]
      have h1 := Fintype.linearIndependent_iff.mp hli _ h0 i
      exact mem_pow_of_mul_mem h𝔭 hs (by rw [sub_eq_zero.mp h1]; exact hd i)
    · intro hc
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem_smul (hc i (Set.mem_univ i)) Submodule.mem_top
  have e := ((LinearMap.quotKerEquivOfSurjective ψ hsurj).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans (Submodule.quotientPi (fun _ => 𝔭 ^ k))))
  rw [Nat.card_congr e.toEquiv, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Formalism.HermitianLattices.Ext.L3.MeanA
end
end

