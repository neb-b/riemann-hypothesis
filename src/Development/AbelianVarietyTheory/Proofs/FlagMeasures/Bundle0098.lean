module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.MinkowskiNumberDvdFactorial
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardEmbeddedDataWithGivenFixedLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0097
public import Formalism.HyperbolicPlaceProducts.SecondLevelArithmeticNorm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStarStableIdealAbsorbingMinors
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0092
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0094

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardSublatticesDefiniteQuotientNormalFormLe
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt

theorem count_index_fg {K Q : Type} [Field K] [NumberField K] [AddCommGroup Q] [Module K Q]
    [Module (𝓞 K) Q] [IsScalarTower (𝓞 K) K Q] [FiniteDimensional K Q] (M : Submodule (𝓞 K) Q) (hM : M.FG)
    (S : Submodule K Q) (hS : M ≤ S.restrictScalars (𝓞 K)) (k : ℕ) (hk : Module.finrank K S ≤ k)
    (x : ℕ) (hx : 1 ≤ x) :
    {N : Submodule (𝓞 K) M | N.toAddSubgroup.index = x}.Finite ∧
      (({N : Submodule (𝓞 K) M | N.toAddSubgroup.index = x}.ncard : ℕ) : ℝ) ≤ (x : ℝ) ^ ((k : ℝ) + cf K) := by
  have : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.2 hM
  have : Module.IsTorsionFree (𝓞 K) Q := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K Q
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  obtain ⟨h1, h2⟩ := Formalism.SLP.Final.submoduleIndexCountO K M x hx
  refine ⟨h1, ?_⟩
  have hr : Module.finrank (𝓞 K) M ≤ k := by
    refine le_trans ?_ hk
    apply Module.finrank_le_of_rank_le
    have h3 : Module.rank (𝓞 K) M ≤ Module.rank (𝓞 K) S := Submodule.rank_mono hS
    have h5 : Module.rank K S = Module.rank (𝓞 K) S := IsLocalization.rank_eq K (nonZeroDivisors (𝓞 K)) le_rfl
    rw [Module.finrank_eq_rank, h5]
    exact h3
  have hn : 1 ≤ Module.finrank ℚ K := Module.finrank_pos
  have hx1 : (1:ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0:ℝ) < x := by linarith
  have h4 := Formalism.SLP.Final.omegaPow (Module.finrank ℚ K) x hn hx
  have h3 : (({N : Submodule (𝓞 K) M | N.toAddSubgroup.index = x}.ncard : ℕ) : ℝ) ≤
      ((Module.finrank ℚ K : ℕ) : ℝ) ^ (Nat.primeFactorsList x).length *
        (x : ℝ) ^ Module.finrank (𝓞 K) M := by exact_mod_cast h2
  have hr' : (Module.finrank (𝓞 K) M : ℝ) ≤ k := by exact_mod_cast hr
  calc _ ≤ _ := h3
    _ ≤ (x : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (x : ℝ) ^ Module.finrank (𝓞 K) M :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = (x : ℝ) ^ ((Module.finrank (𝓞 K) M : ℝ) + Real.logb 2 (Module.finrank ℚ K)) := by
        rw [Real.rpow_add hx0, Real.rpow_natCast, mul_comm]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by unfold cf; linarith)

theorem count_index_latMod {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] (W I : Submodule K V)
    (La : Submodule (𝓞 K) V) (h : IsLatMod La (W ⊔ I) I) (x : ℕ) (hx : 1 ≤ x) :
    ((({Th : Submodule (𝓞 K) V | rs (𝓞 K) I ≤ Th ∧ Th ≤ La ∧ idx La Th = x}).encard : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal ((x : ℝ) ^ ((Module.finrank K W : ℝ) + cf K)) := by
  obtain ⟨⟨N, hN, hLa⟩, hsp⟩ := h
  let q : V →ₗ[𝓞 K] (V ⧸ I) := I.mkQ.restrictScalars (𝓞 K)
  have hker : LinearMap.ker q = rs (𝓞 K) I := by
    ext v; simp [q]
  have hM : (La.map q).FG := by
    have : (rs (𝓞 K) I).map q = ⊥ := by
      rw [← hker]; exact LinearMap.le_ker_iff_map.1 le_rfl
    rw [hLa, Submodule.map_sup, this, sup_bot_eq]
    exact hN.map q
  have hS : La.map q ≤ (W.map I.mkQ).restrictScalars (𝓞 K) := by
    rintro _ ⟨v, hv, rfl⟩
    have : v ∈ W ⊔ I := hsp ▸ Submodule.subset_span hv
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.1 this
    refine ⟨w, hw, ?_⟩
    have : I.mkQ u = 0 := by simpa using hu
    change I.mkQ w = I.mkQ (w + u)
    rw [map_add (f := _), this, add_zero]
  obtain ⟨h1, h2⟩ := count_index_fg (La.map q) hM (W.map I.mkQ) hS _ (Submodule.finrank_map_le _ _) x hx
  have hle : {Th : Submodule (𝓞 K) V | rs (𝓞 K) I ≤ Th ∧ Th ≤ La ∧ idx La Th = x}.encard ≤
      {N : Submodule (𝓞 K) (La.map q) | N.toAddSubgroup.index = x}.encard := by
    refine Set.encard_le_encard_of_injOn (f := fun Th => (Th.map q).comap (La.map q).subtype) ?_ ?_
    · rintro Th ⟨hI, hL, hi⟩
      have e : (Th.map q).comap q = Th := Submodule.comap_map_eq_self (hker ▸ hI)
      have e2 : idx La ((Th.map q).comap q) = idx (La.map q) (Th.map q) :=
        AddSubgroup.relIndex_comap (Th.map q).toAddSubgroup q.toAddMonoidHom La.toAddSubgroup
      rw [e, hi] at e2
      exact e2.symm
    · rintro Th ⟨hI, hL, -⟩ Th' ⟨hI', hL', -⟩ he
      have he2 : Th.map q = Th'.map q := by
        have := congrArg (Submodule.map (La.map q).subtype) he
        simp only [Submodule.map_comap_subtype] at this
        rwa [inf_eq_right.2 (Submodule.map_mono hL), inf_eq_right.2 (Submodule.map_mono hL')] at this
      rw [← Submodule.comap_map_eq_self (f := q) (p := Th) (hker ▸ hI), he2,
        Submodule.comap_map_eq_self (hker ▸ hI')]
  refine le_trans (ENat.toENNReal_le.2 hle) ?_
  rw [← h1.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal h2

theorem count_sublattices_definite : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (La : Submodule (𝓞 K) V) (i : ℕ), 1 ≤ i → IsLatMod La (wSp N.F N.F') (II N.F N.F') → ((({Th : Submodule (𝓞 K) V | rs (𝓞 K) (II N.F N.F') ≤ Th ∧ Th ≤ La ∧ idx La Th = i}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((i : ℝ) ^ ((Module.finrank K N.Wt : ℝ) + cf K)) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N La i hi h
  have hw := (GlobalTheory.DegCnt.NF.geometry K V H hK r N).2.2.2.2.2.2.1
  rw [hw] at h
  exact count_index_latMod N.Wt _ La h i hi

end GlobalTheory.DegCnt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardEmbeddedHermDataIndexLe
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt

theorem finrank_sub_le {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) :
    Module.finrank (𝓞 K) L ≤ Module.finrank K V := by
  apply Module.finrank_le_of_rank_le
  apply rank_le
  intro s hs
  have h := hs.map' L.subtype (Submodule.ker_subtype L)
  rw [LinearIndependent.iff_fractionRing (R := 𝓞 K) (K := K)] at h
  simpa using h.fintype_card_le_finrank

theorem sublat_count {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) (hL : L.FG) (x : ℕ) (hx : 1 ≤ x) :
    {N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x}.Finite ∧
      (({N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x}.ncard : ℕ) : ℝ) ≤
        (x : ℝ) ^ (((Module.finrank K V) : ℝ) + cf K) := by
  have : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.2 hL
  have : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  have : Module.Flat (𝓞 K) L := inferInstance
  have : Module.FinitePresentation (𝓞 K) L := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) L := Module.Flat.projective_of_finitePresentation
  obtain ⟨h1, h2⟩ := Formalism.SLP.Final.submoduleIndexCountO K L x hx
  have hsub : {N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x} ⊆
      (Submodule.map L.subtype) '' {N : Submodule (𝓞 K) L | N.toAddSubgroup.index = x} := by
    rintro N ⟨hN, hi⟩
    refine ⟨N.comap L.subtype, ?_, ?_⟩
    · exact hi
    · rw [Submodule.map_comap_subtype, inf_eq_right.2 hN]
  refine ⟨(h1.image _).subset hsub, ?_⟩
  have h3 := (Set.ncard_le_ncard hsub (h1.image _)).trans (Set.ncard_image_le h1)
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have h4 := Formalism.SLP.Final.omegaPow (Module.finrank ℚ K) x Module.finrank_pos hx
  have h5 : ((Module.finrank (𝓞 K) L : ℕ) : ℝ) ≤ (Module.finrank K V : ℝ) := by
    exact_mod_cast finrank_sub_le L
  calc (({N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x}.ncard : ℕ) : ℝ)
      ≤ ((Module.finrank ℚ K : ℕ) : ℝ) ^ (Nat.primeFactorsList x).length * (x : ℝ) ^ Module.finrank (𝓞 K) L := by
        exact_mod_cast h3.trans h2
    _ ≤ (x : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (x : ℝ) ^ Module.finrank (𝓞 K) L :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = (x : ℝ) ^ (((Module.finrank (𝓞 K) L : ℕ) : ℝ) + Real.logb 2 (Module.finrank ℚ K)) := by
        rw [Real.rpow_add hx0, Real.rpow_natCast, mul_comm]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by unfold cf; linarith)

theorem encard_isDat_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ x : ℕ, 1 ≤ x → ((({d | IsDat H g L₀ j x d}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((x : ℝ) ^ (((Module.finrank K V) : ℝ) + cf K) * ((x : ℝ) * D₀) ^ (3 * (2 * j + 1))) := by
  intro K V _ _ _ _ _ _ _ _ H hK hP L₀ g j D₀ hL hD hG hg x hx
  have hfib := GlobalTheory.DegCnt.DatCount.main K V H hK hP L₀ g j D₀ hL hD hG hg
  obtain ⟨hfin, hcnt⟩ := sublat_count L₀ hL.1.fg x hx
  set S := {N : Submodule (𝓞 K) V | N ≤ L₀ ∧ idx L₀ N = x} with hS
  have hsub : {d | IsDat H g L₀ j x d} ⊆
      ⋃ La ∈ hfin.toFinset, {d | IsDat H g L₀ j x d ∧ fixLat d.2 = La} := by
    intro d hd
    simp only [Set.mem_iUnion, Set.Finite.mem_toFinset]
    refine ⟨fixLat d.2, ⟨?_, hd.2.2.2.1⟩, hd, rfl⟩
    intro y hy
    exact (hd.2.2.1.1 hy).2
  have h1 := (Set.encard_le_encard hsub).trans (Finset.set_encard_biUnion_le _ _)
  have h2 : ((({d | IsDat H g L₀ j x d}).encard : ℕ∞) : ℝ≥0∞) ≤
      ∑ La ∈ hfin.toFinset, ((({d | IsDat H g L₀ j x d ∧ fixLat d.2 = La}).encard : ℕ∞) : ℝ≥0∞) := by
    refine (ENat.toENNReal_le.2 h1).trans (le_of_eq ?_)
    exact map_sum ENat.toENNRealRingHom _ _
  refine h2.trans ((Finset.sum_le_card_nsmul _ _ _ fun La _ => hfib La x).trans ?_)
  rw [nsmul_eq_mul, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  gcongr
  rw [← ENNReal.ofReal_natCast, ← Set.ncard_eq_toFinset_card S hfin]
  exact ENNReal.ofReal_le_ofReal hcnt

end GlobalTheory.DegCnt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardSublatticesIndexFixedTraceLe
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.TraceCount

theorem exists_gen_mod {R W : Type} [CommRing R] [IsDomain R] [AddCommGroup W] [Module R W] (C : Submodule R W)
    [Module.Finite R C] [Module.Projective R C] (m : ℕ) [Finite (R ⧸ Ideal.span {(m : R)})] :
    ∃ c : Fin (Module.finrank R C) → W, (∀ i, c i ∈ C) ∧
      ∀ y ∈ C, ∃ (r : Fin (Module.finrank R C) → R) (d : W), d ∈ C ∧ y = ∑ i, r i • c i + m • d := by
  obtain ⟨⟨v, hv⟩, -⟩ := GlobalTheory.CongIndex.quot_smul_top_span_card (R := R) (N := C) (Ideal.span {(m : R)})
  choose c hc using fun i => Submodule.Quotient.mk_surjective _ (v i)
  refine ⟨fun i => c i, fun i => (c i).2, fun y hy => ?_⟩
  have h1 : (Submodule.Quotient.mk ⟨y, hy⟩ : C ⧸ (Ideal.span {(m : R)} • (⊤ : Submodule R C))) ∈
      Submodule.span R (Set.range v) := hv ▸ Submodule.mem_top
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 h1
  have h2 : (Submodule.Quotient.mk (∑ i, r i • c i) : C ⧸ (Ideal.span {(m : R)} • (⊤ : Submodule R C))) =
      Submodule.Quotient.mk ⟨y, hy⟩ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hr, ← Submodule.mkQ_apply, map_sum]
    simp [hc]
  have h3 := (Submodule.Quotient.eq _).1 h2.symm
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h3
  obtain ⟨d, -, hd⟩ := h3
  refine ⟨r, d, d.2, ?_⟩
  have h4 := congrArg Subtype.val hd
  simp only [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_sum, Nat.cast_smul_eq_nsmul] at h4
  rw [eq_sub_iff_add_eq] at h4
  rw [← h4, add_comm]
  simp

theorem fibre_count {R V W : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (f : V →ₗ[R] W) (L M : Submodule R V) (C : Submodule R W) (m s : ℕ)
    (hm : M.toAddSubgroup.relIndex (L ⊓ LinearMap.ker f).toAddSubgroup = m) (hm0 : m ≠ 0)
    (c : Fin s → W) (hc : ∀ i, c i ∈ C)
    (hgen : ∀ y ∈ C, ∃ (r : Fin s → R) (d : W), d ∈ C ∧ y = ∑ i, r i • c i + m • d) :
    {La : Submodule R V | La ≤ L ∧ La.map f = C ∧ La ⊓ LinearMap.ker f = M}.encard ≤ (m ^ s : ℕ) := by
  set S := {La : Submodule R V | La ≤ L ∧ La.map f = C ∧ La ⊓ LinearMap.ker f = M} with hS
  rcases S.eq_empty_or_nonempty with h0 | ⟨L₁, hL₁⟩
  · simp [h0]
  have hlift : ∀ La : S, ∀ y ∈ C, ∃ a ∈ La.1, f a = y := fun La y hy => by
    have : y ∈ La.1.map f := La.2.2.1.symm ▸ hy
    exact this
  choose a ha hfa using fun (La : S) (i : Fin s) => hlift La (c i) (hc i)
  set K₀ := (L ⊓ LinearMap.ker f).toAddSubgroup with hK₀
  have hmem : ∀ (La : S) i, a La i - a ⟨L₁, hL₁⟩ i ∈ K₀ := fun La i =>
    ⟨sub_mem (La.2.1 (ha La i)) (hL₁.1 (ha ⟨L₁, hL₁⟩ i)), by simp [hfa]⟩
  let Φ : S → (Fin s → K₀ ⧸ M.toAddSubgroup.addSubgroupOf K₀) := fun La i => QuotientAddGroup.mk ⟨_, hmem La i⟩
  have hle : ∀ La La' : S, Φ La = Φ La' → La.1 ≤ La'.1 := by
    intro La La' h y hy
    have hML : M ≤ La'.1 := La'.2.2.2 ▸ inf_le_left
    have h1 : ∀ i, a La i ∈ La'.1 := fun i => by
      have h2 := QuotientAddGroup.eq.1 (congrFun h i)
      rw [AddSubgroup.mem_addSubgroupOf] at h2
      have h3 : -(a La i - a ⟨L₁, hL₁⟩ i) + (a La' i - a ⟨L₁, hL₁⟩ i) ∈ La'.1 := hML h2
      have h4 := sub_mem (ha La' i) h3
      convert h4 using 1
      abel
    have hfy : f y ∈ C := La.2.2.1 ▸ Submodule.mem_map_of_mem hy
    obtain ⟨r, d, hd, hyd⟩ := hgen _ hfy
    obtain ⟨b, hb, hfb⟩ := hlift La d hd
    obtain ⟨b', hb', hfb'⟩ := hlift La' d hd
    have h5 : y - (∑ i, r i • a La i + m • b) ∈ M := by
      rw [← La.2.2.2]
      refine ⟨sub_mem hy (add_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (ha La i))
        (nsmul_mem hb _)), ?_⟩
      simp [hfa, hfb, ← hyd]
    have h6 : m • (b - b') ∈ M := by
      have h7 : b - b' ∈ K₀ := ⟨sub_mem (La.2.1 hb) (La'.2.1 hb'), by simp [hfb, hfb']⟩
      have h8 := AddSubgroup.nsmul_index_mem (M.toAddSubgroup.addSubgroupOf K₀) ⟨_, h7⟩
      rw [AddSubgroup.mem_addSubgroupOf] at h8
      have h9 : (M.toAddSubgroup.addSubgroupOf K₀).index = m := hm
      rw [h9] at h8
      exact h8
    have h10 := add_mem (hML h5) (add_mem (Submodule.sum_mem _ fun i (_ : i ∈ Finset.univ) =>
      Submodule.smul_mem _ (r i) (h1 i)) (add_mem (hML h6) (nsmul_mem hb' m)))
    convert h10 using 1
    rw [smul_sub]
    abel
  have hΦ : Function.Injective Φ := fun La La' h => Subtype.ext (le_antisymm (hle _ _ h) (hle _ _ h.symm))
  have hcard : Nat.card (K₀ ⧸ M.toAddSubgroup.addSubgroupOf K₀) = m := hm
  have : Finite (K₀ ⧸ M.toAddSubgroup.addSubgroupOf K₀) := Nat.finite_of_card_ne_zero (hcard ▸ hm0)
  have hfin : Finite S := Finite.of_injective Φ hΦ
  have h11 := Nat.card_le_card_of_injective Φ hΦ
  rw [Nat.card_fun, hcard, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin] at h11
  rw [← (Set.toFinite S).cast_ncard_eq]
  exact_mod_cast h11

theorem relIndex_eq_mul {V W : Type} [AddCommGroup V] [AddCommGroup W] (f : V →+ W) (A L : AddSubgroup V)
    (h : A ≤ L) : A.relIndex L = (A ⊓ f.ker).relIndex (L ⊓ f.ker) * (A.map f).relIndex (L.map f) := by
  have h1 := AddSubgroup.relIndex_mul_relIndex A (A ⊔ (L ⊓ f.ker)) L le_sup_left (sup_le h inf_le_left)
  rw [← h1, AddSubgroup.relIndex_sup_left, AddSubgroup.relIndex_map_map]
  congr 1
  · rw [← AddSubgroup.inf_relIndex_right A, ← AddSubgroup.inf_relIndex_right (A ⊓ f.ker), inf_assoc,
      inf_eq_right.2 (inf_le_right : L ⊓ f.ker ≤ f.ker)]
  · have h2 : L ⊔ f.ker = L ⊔ (A ⊔ f.ker) := by rw [← sup_assoc, sup_eq_left.2 h]
    rw [h2, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right (A ⊔ f.ker), sup_inf_assoc_of_le _ h,
      inf_comm]

theorem encard_le_mul {α β : Type} (g : α → β) (S : Set α) (T : Set β) (hT : T.Finite) (k : ℕ)
    (hg : ∀ a ∈ S, g a ∈ T) (hk : ∀ b ∈ T, {a | a ∈ S ∧ g a = b}.encard ≤ k) :
    S.encard ≤ (T.ncard * k : ℕ) := by
  have hfin : S.Finite := by
    refine (hT.biUnion fun b hb => Set.finite_of_encard_le_coe (hk b hb)).subset fun a ha => ?_
    exact Set.mem_biUnion (hg a ha) ⟨ha, rfl⟩
  rw [← hfin.cast_ncard_eq, Nat.cast_le, Set.ncard_eq_toFinset_card _ hfin, Set.ncard_eq_toFinset_card _ hT,
    mul_comm]
  refine Finset.card_le_mul_card_image_of_maps_to (f := g) (fun a ha => by simpa using hg a (by simpa using ha)) k
    fun b hb => ?_
  have h1 := hk b (by simpa using hb)
  have h2 : {a | a ∈ S ∧ g a = b} = ((hfin.toFinset.filter fun a => g a = b : Finset α) : Set α) := by
    ext a; simp
  rw [h2, Set.encard_coe_eq_coe_finsetCard] at h1
  exact_mod_cast h1

theorem proj_rank {K W : Type} [Field K] [NumberField K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (C : Submodule (𝓞 K) W) (hC : C.FG) :
    Module.Finite (𝓞 K) C ∧ Module.Projective (𝓞 K) C ∧ Module.finrank (𝓞 K) C ≤ Module.finrank K W := by
  have : Module.Finite (𝓞 K) C := Module.Finite.iff_fg.2 hC
  have : Module.IsTorsionFree (𝓞 K) W := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K W
  have : Module.Flat (𝓞 K) C := inferInstance
  have : Module.FinitePresentation (𝓞 K) C := Module.finitePresentation_of_finite _ _
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation,
    (GlobalTheory.CongIndex.finrank_le_finrank_span C).trans (Submodule.finrank_le _)⟩

theorem sub_count {K W : Type} [Field K] [NumberField K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (C : Submodule (𝓞 K) W) (hC : C.FG) (j : ℕ) (hj : 1 ≤ j) :
    {N : Submodule (𝓞 K) W | N ≤ C ∧ N.toAddSubgroup.relIndex C.toAddSubgroup = j}.Finite ∧
    (({N : Submodule (𝓞 K) W | N ≤ C ∧ N.toAddSubgroup.relIndex C.toAddSubgroup = j}.ncard : ℕ) : ℝ) ≤
      (j : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (j : ℝ) ^ Module.finrank K W := by
  obtain ⟨h1, h2, h3⟩ := proj_rank C hC
  obtain ⟨h4, h5⟩ := Formalism.SLP.Final.submoduleIndexCountO K C j hj
  have h6 := Formalism.SLP.Final.omegaPow (Module.finrank ℚ K) j Module.finrank_pos hj
  have hsub : {N : Submodule (𝓞 K) W | N ≤ C ∧ N.toAddSubgroup.relIndex C.toAddSubgroup = j} ⊆
      (fun N : Submodule (𝓞 K) C => N.map C.subtype) '' {N | N.toAddSubgroup.index = j} := by
    rintro N ⟨hN, hNj⟩
    refine ⟨N.comap C.subtype, hNj, ?_⟩
    simp only [Submodule.map_comap_subtype]
    exact inf_eq_right.2 hN
  refine ⟨(h4.image _).subset hsub, ?_⟩
  have h7 := ((Set.ncard_le_ncard hsub (h4.image _)).trans (Set.ncard_image_le h4)).trans h5
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  calc _ ≤ ((Module.finrank ℚ K : ℕ) : ℝ) ^ (Nat.primeFactorsList j).length * (j : ℝ) ^ Module.finrank (𝓞 K) C := by
        exact_mod_cast h7
    _ ≤ _ := mul_le_mul h6 (pow_le_pow_right₀ hj1 h3) (by positivity) (by positivity)

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L₀ M : Submodule (𝓞 K) V) (U : Submodule K V) (x : ℕ), Submodule.IsLattice K L₀ → 1 ≤ x → ((({La : Submodule (𝓞 K) V | La ≤ L₀ ∧ idx L₀ La = x ∧ La ⊓ rs (𝓞 K) U = M}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((x : ℝ) ^ (2 * (((Module.finrank K V) - Module.finrank K U : ℕ) : ℝ) + cf K)) := by
  intro K V _ _ _ _ _ _ _ _ L₀ M U x hL hx
  set S := {La : Submodule (𝓞 K) V | La ≤ L₀ ∧ idx L₀ La = x ∧ La ⊓ rs (𝓞 K) U = M} with hS
  rcases S.eq_empty_or_nonempty with h0 | ⟨L₁, hL₁⟩
  · simp [h0]
  let f : V →ₗ[𝓞 K] (V ⧸ U) := U.mkQ.restrictScalars (𝓞 K)
  have hker : LinearMap.ker f = rs (𝓞 K) U := by
    ext v
    simp [f]
  have hker' : f.toAddMonoidHom.ker = (LinearMap.ker f).toAddSubgroup := rfl
  set m := M.toAddSubgroup.relIndex (L₀ ⊓ LinearMap.ker f).toAddSubgroup with hm
  have hidx : ∀ La ∈ S, x = m * (La.map f).toAddSubgroup.relIndex (L₀.map f).toAddSubgroup := by
    intro La hLa
    have h1 := relIndex_eq_mul f.toAddMonoidHom La.toAddSubgroup L₀.toAddSubgroup hLa.1
    have h2 : La.toAddSubgroup.relIndex L₀.toAddSubgroup = x := hLa.2.1
    have h3 : La ⊓ LinearMap.ker f = M := hker ▸ hLa.2.2
    rw [← h2, h1, hm, ← h3]
    rfl
  set j := (L₁.map f).toAddSubgroup.relIndex (L₀.map f).toAddSubgroup with hj
  have hxj : x = m * j := hidx L₁ hL₁
  have hm0 : m ≠ 0 := fun h => by rw [h] at hxj; omega
  have hj0 : j ≠ 0 := fun h => by rw [h] at hxj; omega
  have hC : (L₀.map f).FG := (Submodule.IsLattice.fg (self := hL)).map f
  have hs : Module.finrank K (V ⧸ U) = Module.finrank K V - Module.finrank K U := by
    have := U.finrank_quotient_add_finrank
    omega
  set s := Module.finrank K V - Module.finrank K U with hsdef
  obtain ⟨hT, hTc⟩ := sub_count (L₀.map f) hC j (Nat.one_le_iff_ne_zero.2 hj0)
  rw [hs] at hTc
  have hfinq : Finite (𝓞 K ⧸ Ideal.span {(m : 𝓞 K)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hm0)
  have hcount := encard_le_mul (fun La : Submodule (𝓞 K) V => La.map f) S _ hT (m ^ s)
    (fun La hLa => ⟨Submodule.map_mono hLa.1,
      Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm0) ((hidx La hLa).symm.trans hxj)⟩)
    (fun N hN => by
      have hCf : Module.Finite (𝓞 K) (L₀.map f) := Module.Finite.iff_fg.2 hC
      have hNfg : N.FG := Submodule.FG.of_le_of_isNoetherian hN.1
      obtain ⟨h1, h2, h3⟩ := proj_rank N hNfg
      obtain ⟨c, hc, hgen⟩ := exists_gen_mod N m
      have h4 := fibre_count f L₀ M N m _ hm.symm hm0 c hc hgen
      refine le_trans (Set.encard_le_encard ?_) (h4.trans ?_)
      · rintro La ⟨hLa, hN'⟩
        exact ⟨hLa.1, hN', hker ▸ hLa.2.2⟩
      · exact_mod_cast Nat.pow_le_pow_right (Nat.pos_of_ne_zero hm0) (hs ▸ h3))
  refine le_trans (ENat.toENNReal_le.2 hcount) ?_
  rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  refine ENNReal.ofReal_le_ofReal ?_
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hjx : (j : ℝ) ≤ x := by exact_mod_cast hxj ▸ Nat.le_mul_of_pos_left j (Nat.pos_of_ne_zero hm0)
  have hlog : 0 ≤ Real.logb 2 (Module.finrank ℚ K) :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K))
  have hxr : (x : ℝ) = m * j := by exact_mod_cast hxj
  push_cast
  calc _ ≤ ((j : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (j : ℝ) ^ s) * (m : ℝ) ^ s :=
        mul_le_mul_of_nonneg_right hTc (by positivity)
    _ = (j : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (x : ℝ) ^ s := by rw [hxr, mul_pow]; ring
    _ ≤ (x : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (x : ℝ) ^ s :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) hjx hlog) (by positivity)
    _ = (x : ℝ) ^ (Real.logb 2 (Module.finrank ℚ K) + (s : ℝ)) := by
        rw [Real.rpow_add (by positivity), Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by
        have : (0 : ℝ) ≤ s := Nat.cast_nonneg _
        unfold cf
        linarith)

end GlobalTheory.TraceCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStarStableIdealAbsorbingMinorsStatement
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_star_stable_ideal_absorbing_minors : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∃ 𝔠 : Ideal (𝓞 K), (Ideal.absNorm 𝔠 : ℝ) ≤ (N.Db * N.NT) ^ 2 ∧ 1 ≤ N.Db ∧ 1 ≤ N.Del ∧ ∀ Q : Prop, (𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → Q) → Q := by
  first | exact @GlobalTheory.DegCnt.Absorb.exists_absorbing_ideal | exact GlobalTheory.DegCnt.Absorb.exists_absorbing_ideal | (intros; apply GlobalTheory.DegCnt.Absorb.exists_absorbing_ideal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSymmInvariantKernelHermitianFrames
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem exists_symm_invariant_kernel : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (P : Submodule L.O S.V → Prop), (∀ Λ, P Λ ↔ (S.IsTerm d Λ ∧ S.InFF β (j + 1) βJ d Λ)) → ∃ m : Submodule L.O S.V → Submodule L.O S.V → ℝ, (∀ h ∈ S.St, ∀ x y, P x → P y → m (h • x) (h • y) = m x y) ∧ ∀ x, P x → {y | P y ∧ m x y ≠ 0}.Finite ∧ (∀ y, P y → 0 ≤ m x y ∧ m x y = m y x) ∧ |(∑ᶠ y : {y // P y}, m x y) - 1| ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) ∧ ‖∑ᶠ y : {y // P y}, (m x y : ℂ) * S.om d y‖ ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk j β βJ d P hP
  have hPe : P = fun Λ => S.IsTerm d Λ ∧ S.InFF β (j + 1) βJ d Λ :=
    funext fun Λ => propext (hP Λ)
  subst hPe
  refine ⟨fun x y => S.kern β (j + 1) βJ d x y, ?_, ?_⟩
  · intro h hh x y hx _
    exact GlobalTheory.T.frameMovesKernel_commonStabilizer_smul_eq L r k S d x hx.1 β (j + 1) βJ y h hh
  · intro x hx
    have base := _root_.GlobalTheory.HL.moves_split_by_target L r k S j β βJ d x hx.1 hx.2
    refine ⟨?_, ?_, GlobalTheory.T.hermitianDoubleCoset_kernel_row_sum_near_one L r k S hk j β βJ d x hx.1 hx.2,
      _root_.GlobalTheory.HL.KernelWeight.kernel_weight L r k S hk j β βJ d x hx.1 hx.2⟩
    · exact base.2.2.1.subset fun y hy => hy.2
    · intro y hy
      exact ⟨base.2.2.2.1 y, _root_.GlobalTheory.HL.KernSym.kern_symm L r k S j β βJ d x hx.1 hx.2 y hy.1 hy.2⟩

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummaryStatement
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermFramePairNormalForm_geometry_summary : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), NFFull N.F N.F' N.j N.j_le N.c ∧ IsLift N.F N.F' N.Wt ∧ IsCompl N.Wt N.Pi ∧ Module.finrank K N.Wt + 2 * r + 1 = Module.finrank K V ∧ N.Wn = N.Wt ⊔ Submodule.span K {N.F.z} ∧ uPerp N.F N.F' = N.Wn ⊔ II N.F N.F' ∧ wSp N.F N.F' = N.Wt ⊔ II N.F N.F' ∧ wSp N.F' N.F = wSp N.F N.F' ∧ GlobalTheory.Mass.PD (GlobalTheory.Mass.hRes H.B.flip N.Wt) ∧ 1 ≤ N.T ∧ N.nD N.j ≠ 0 ∧ N.Pi = V0 N.F N.F' ⊔ N.Ist := by
  first | exact @GlobalTheory.DegCnt.NF.geometry | exact GlobalTheory.DegCnt.NF.geometry | (intros; apply GlobalTheory.DegCnt.NF.geometry <;> assumption)
end

