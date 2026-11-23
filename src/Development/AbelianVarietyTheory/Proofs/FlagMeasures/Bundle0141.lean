module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.SubquotientSizeInequality
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.PDescentCutA
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFramesSubspace
section
open Formalism.HN Matrix NumberField Finset GlobalTheory.IndefiniteRowSideFullHecke.SubquotientSizeInequality

noncomputable section

namespace GlobalTheory.SizeSubToQuot

theorem norm_proj_le_infDist {ι : Type} [Fintype ι] (P Q : Submodule ℂ (EuclideanSpace ℂ ι)) (h : Q ≤ P)
    (x : EuclideanSpace ℂ ι) :
    ‖Pᗮ.starProjection x‖ ≤ Metric.infDist x (Q : Set (EuclideanSpace ℂ ι)) := by
  rw [Metric.le_infDist ⟨0, Q.zero_mem⟩]
  intro y hy
  have h0 : Pᗮ.starProjection y = 0 := Submodule.starProjection_orthogonal_apply_eq_zero (h hy)
  rw [dist_eq_norm, ← sub_zero (Pᗮ.starProjection x), ← h0, ← map_sub]
  exact Submodule.norm_starProjection_apply_le _ _

section General

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
  [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)


omit [_root_.NumberField.IsTotallyComplex K] in
theorem le_of_subset_span (hX : ∀ v, IsUnit (X v).det) {L S N : Submodule (𝓞 K) V} (hL : L.FG)
    (hS : IsSat (Formalism.HermitianLatticesTheory.realize b X) L S) (hN : N ≤ L)
    (h : (N : Set V) ⊆ Submodule.span K (S : Set V)) : N ≤ S := by
  have hle : S ⊔ N ≤ L := sup_le hS.1 hN
  have hsp : Submodule.span K ((S ⊔ N : Submodule (𝓞 K) V) : Set V) = Submodule.span K (S : Set V) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro y hy
      obtain ⟨s, hs, n, hn, rfl⟩ := Submodule.mem_sup.1 hy
      exact Submodule.add_mem _ (Submodule.subset_span hs) (h hn)
    · exact Submodule.span_mono (SetLike.coe_subset_coe.2 le_sup_left)
  have h1 := (plLat K V ι b X hX _ (Submodule.FG.of_le hL hle)).2.1
  have h2 := (plLat K V ι b X hX _ (Submodule.FG.of_le hL hS.1)).2.1
  have h3 : rkK (S ⊔ N) = rkK S := by unfold rkK; rw [hsp]
  have h4 := (satBasic _ _ _ (Formalism.HermitianLatticesTheory.realize b X) L (plLat K V ι b X hX L hL).1).2.2.1 S (S ⊔ N) hS
    le_sup_left hle (by rw [h1, h2, h3])
  exact sup_eq_left.1 h4

theorem exists_frames_subspace (hX : ∀ v, IsUnit (X v).det) (U : Submodule K V) :
    ∃ (m : ℕ) (e : Module.Basis (Fin m) K U) (Y : InfinitePlace K → Matrix (Fin m) (Fin m) ℂ),
      (∀ v, IsUnit (Y v).det) ∧
      ∀ v (x : U), Formalism.HermitianLatticesTheory.normAt b X v (U.subtype x) = Formalism.HermitianLatticesTheory.normAt e Y v x := by
  have hfinV : FiniteDimensional K V := Module.Finite.of_basis b
  let e := Module.finBasis K U
  let T : InfinitePlace K → ((Fin (Module.finrank K U) → ℂ) →ₗ[ℂ] EuclideanSpace ℂ ι) := fun v =>
    Fintype.linearCombination ℂ (fun k => WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v (e k : V)))
  have hT : ∀ v (x : U), (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v (x : V)) : EuclideanSpace ℂ ι) =
      T v (fun k => v.embedding (e.repr x k)) := by
    intro v x
    have hx : (x : V) = ∑ k, e.repr x k • (e k : V) := by
      have h := congrArg U.subtype (e.sum_repr x)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h
      exact h.symm
    rw [hx, PlaceDecomposition.fcoord_lincomb, WithLp.toLp_sum]
    simp only [T, Fintype.linearCombination_apply, WithLp.toLp_smul]
  have hinj : ∀ v, Function.Injective (T v) := by
    intro v
    have hle : QuotientRealization.pv b X U v ≤ LinearMap.range (T v) := by
      rw [QuotientRealization.pv, Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨_, (hT v ⟨y, hy⟩).symm⟩
    have h1 := Submodule.finrank_mono hle
    rw [QuotientRealization.finrank_pv b X hX] at h1
    have h4 := LinearMap.finrank_range_add_finrank_ker (T v)
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h4
    have h5 : Module.finrank ℂ (LinearMap.ker (T v)) = 0 := by omega
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.finrank_eq_zero.1 h5
  have hM := fun v => QuotientRealization.exists_mat (T v) (hinj v)
  choose M hMu hMn using hM
  refine ⟨_, e, fun v => (M v)⁻¹, fun v => Matrix.isUnit_nonsing_inv_det _ (hMu v), fun v x => ?_⟩
  rw [Formalism.HermitianLatticesTheory.normAt, PlaceOperatorNorms.cnorm_eq, Submodule.subtype_apply, hT, ← hMn v]
  simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord, Matrix.nonsing_inv_nonsing_inv _ (hMu v)]
  rfl

theorem ptAt_mem_spanAt (S : Submodule (𝓞 K) V) (v : InfinitePlace K) {y : V}
    (hy : y ∈ Submodule.span K (S : Set V)) : ptAt b X v y ∈ spanAt b X v S := by
  have h := Submodule.mem_map_of_mem
    (f := ((WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm : (ι → ℂ) →ₗ[ℂ] EuclideanSpace ℂ ι))
    (QuotientRealization.fcoord_mem_span b X S v hy)
  rw [Submodule.map_span, Set.image_image] at h
  exact h

theorem size_ineq_to_quot (hX : ∀ v, IsUnit (X v).det) (φ : V →ₗ[K] V) {A B B' : Submodule (𝓞 K) V}
    (hA : A.FG) (hB : B.FG) (hS : IsSat (Formalism.HermitianLatticesTheory.realize b X) B B') (hAB : ∀ y ∈ A, φ y ∈ B)
    (hne : ∃ y ∈ A, φ y ∉ B') {lo hi : ℝ} (hlo : 0 < lo)
    (hl : ∀ N, B' < N → N ≤ B → lo ≤ sizeQ b X N B') (hh : largestSize b X A ≤ hi)
    (c : InfinitePlace K → ℝ) (hc : ∀ v, 0 ≤ c v)
    (hn : ∀ v, ∀ y ∈ Submodule.span K (A : Set V),
      distAt b X v B' (φ y) ≤ c v * Formalism.HermitianLatticesTheory.normAt b X v y) :
    lo / hi ≤ (∏ v, c v) ^ ((1 : ℝ) / (nPl K : ℝ)) := by
  have hQ := quotRealize K V ι b X hX B B' hB hS
  set W := Submodule.span K (B' : Set V) with hW
  obtain ⟨κ, _, _, b', X', hX', hnorm, hq⟩ := hQ
  set U := Submodule.span K (A : Set V) with hU
  obtain ⟨m, e, Y, hY, hiso⟩ := exists_frames_subspace b X hX U
  set A₀ : Submodule (𝓞 K) U := A.comap (U.subtype.restrictScalars (𝓞 K)) with hA₀
  have hmapA : A₀.map (U.subtype.restrictScalars (𝓞 K)) = A := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩; exact hy
    · intro y hy
      exact ⟨⟨y, Submodule.subset_span hy⟩, hy, rfl⟩
  have hA₀fg : A₀.FG := by
    refine Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars (𝓞 K)) U.injective_subtype ?_
    rw [hmapA]; exact hA
  have hre := (rerealize K U (Fin m) V ι e Y b X U.subtype hY hX U.injective_subtype hiso A₀ hA₀fg).2.2.2.2.2.2
  rw [hmapA] at hre
  set ψ : U →ₗ[K] V ⧸ W := W.mkQ ∘ₗ φ ∘ₗ U.subtype with hψ
  set Bq := B.map (W.mkQ.restrictScalars (𝓞 K)) with hBq
  have hBfg : Bq.FG := hB.map _
  have hABq : A₀.map (ψ.restrictScalars (𝓞 K)) ≤ Bq := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨φ y, hAB _ hy, rfl⟩
  obtain ⟨y₀, hy₀, hy₀'⟩ := hne
  have h0 : A₀.map (ψ.restrictScalars (𝓞 K)) ≠ ⊥ := by
    intro h0
    have h1 : ψ.restrictScalars (𝓞 K) ⟨y₀, Submodule.subset_span hy₀⟩ ∈
        A₀.map (ψ.restrictScalars (𝓞 K)) := Submodule.mem_map_of_mem hy₀
    rw [h0, Submodule.mem_bot] at h1
    have h2 : φ y₀ ∈ W := (Submodule.Quotient.mk_eq_zero W).1 h1
    have h3 : B ⊓ W.restrictScalars (𝓞 K) ≤ B' :=
      le_of_subset_span b X hX hB hS inf_le_left fun z hz => hz.2
    exact hy₀' (h3 ⟨hAB _ hy₀, h2⟩)
  have hA0 : A₀ ≠ ⊥ := fun h => h0 (by rw [h, Submodule.map_bot])
  have hB0 : Bq ≠ ⊥ := fun h => h0 (le_bot_iff.1 (h ▸ hABq))
  have hM := sizeIneq K U (Fin m) _ κ e Y b' X' hY hX' ψ A₀ Bq hA₀fg hBfg hABq h0
  have hop : ∀ v, opNormAt e Y b' X' v ψ ≤ c v := by
    intro v
    refine Formalism.L2.Geo.ExtensionFiltration.opNormAt_le_of_points e Y b' X' hY _ v (c v) (hc v) fun y => ?_
    rw [← hiso]
    refine le_trans ?_ (hn v y y.2)
    rw [hψ, LinearMap.comp_apply, hnorm]
    refine norm_proj_le_infDist _ _ ?_ _
    refine Submodule.span_mono ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, Submodule.subset_span hz, rfl⟩
  have hP : (∏ v, opNormAt e Y b' X' v ψ) ^ ((1 : ℝ) / (nPl K : ℝ)) ≤
      (∏ v, c v) ^ ((1 : ℝ) / (nPl K : ℝ)) :=
    Real.rpow_le_rpow (Finset.prod_nonneg fun v _ => norm_nonneg _)
      (Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v _ => hop v) (by positivity)
  have hleast : lo ≤ leastSize b' X' Bq := by
    refine le_csInf ⟨_, Bq, le_rfl, hB0, rfl⟩ ?_
    rintro _ ⟨N, hNB, hN0, rfl⟩
    set N' := B ⊓ N.comap (W.mkQ.restrictScalars (𝓞 K)) with hN'
    have hS0 : ∀ s ∈ B', W.mkQ s = 0 := fun s hs =>
      (Submodule.Quotient.mk_eq_zero W).2 (Submodule.subset_span hs)
    have hSN : B' ≤ N' := by
      intro s hs
      refine ⟨hS.1 hs, ?_⟩
      show W.mkQ s ∈ N
      rw [hS0 s hs]; exact N.zero_mem
    have hmap : N'.map (W.mkQ.restrictScalars (𝓞 K)) = N := by
      apply le_antisymm
      · rintro _ ⟨y, hy, rfl⟩; exact hy.2
      · intro z hz
        obtain ⟨y, hy, rfl⟩ := hNB hz
        exact ⟨y, ⟨hy, hz⟩, rfl⟩
    have hne : B' ≠ N' := by
      intro h
      apply hN0
      rw [← hmap, ← h, eq_bot_iff]
      rintro _ ⟨s, hs, rfl⟩
      exact hS0 s hs
    have hlt := hl N' (lt_of_le_of_ne hSN hne) inf_le_left
    rwa [(hq N' hSN inf_le_left).2, hmap] at hlt
  have hpos : 0 < largestSize e Y A₀ := by
    rw [(sizeMu K U (Fin m) e Y hY A₀ hA₀fg hA0).2.2.2.2.1]; exact Real.exp_pos _
  refine le_trans ?_ (hM.trans hP)
  exact div_le_div₀ (hlo.le.trans hleast) hleast hpos (hre ▸ hh)

end General

theorem size_ineq_sub_to_quot : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (X v).det) → ∀ (φ : Matrix (Fin n) (Fin n) K) (A B B' : Submodule (𝓞 K) (Fin n → K)), A.FG → B.FG → IsSat (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) X) B B' → (∀ y ∈ A, φ *ᵥ y ∈ B) → (∃ y ∈ A, φ *ᵥ y ∉ B') → ∀ lo hi : ℝ, 0 < lo → (∀ N, B' < N → N ≤ B → lo ≤ sizeQ (Pi.basisFun K (Fin n)) X N B') → largestSize (Pi.basisFun K (Fin n)) X A ≤ hi → ∀ c : InfinitePlace K → ℝ, (∀ v, 0 ≤ c v) → (∀ v, ∀ u ∈ spanAt (Pi.basisFun K (Fin n)) X v A, Metric.infDist (Matrix.toEuclideanLin ((X v)⁻¹ * φ.map v.embedding * X v) u) (spanAt (Pi.basisFun K (Fin n)) X v B' : Set (EuclideanSpace ℂ (Fin n))) ≤ c v * ‖u‖) → lo / hi ≤ (∏ v, c v) ^ ((1 : ℝ) / (nPl K : ℝ)) := by
  intro K _ _ _ _ n X hX φ A B B' hA hB hS hAB hne lo hi hlo hl hh c hc hn
  refine size_ineq_to_quot (Pi.basisFun K (Fin n)) X hX (Matrix.toLin' φ) hA hB hS hAB hne hlo hl hh c hc
    fun v y hy => ?_
  have h := hn v _ (ptAt_mem_spanAt (Pi.basisFun K (Fin n)) X A v hy)
  rw [norm_ptAt] at h
  refine le_trans (le_of_eq ?_) h
  unfold distAt ptAt
  rw [PlaceOperatorNorms.fcoord_map (Pi.basisFun K (Fin n)) X (Pi.basisFun K (Fin n)) X hX v,
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  rfl

end GlobalTheory.SizeSubToQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableCutoffFibreIntegralOneSubgroup
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem exists_measurable_cutoff_fibre_integral_one (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (N : Subgroup G) (ν : Measure G)
    (_hN : IsClosed (N : Set G)) (hν : IsHaarSub (N : Set G) ν) :
    ∃ β : G → ENNReal, Measurable β ∧ (∀ y, β y ≠ ⊤) ∧ ∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1 := by
  classical
  obtain ⟨hne, hfin, hcompl, hinv⟩ := hν

  have hae : ∀ᵐ m ∂ν, m ∈ (N : Set G) := by
    rw [ae_iff]; exact hcompl

  have horb : ∀ (h : G → ENNReal) (a : G), a ∈ N → ∀ y,
      ∫⁻ z, h (z⁻¹ * (a⁻¹ * y)) ∂ν = ∫⁻ z, h (z⁻¹ * y) ∂ν := by
    intro h a ha y
    have hmap : ν.map (MeasurableEquiv.mulLeft a) = ν := hinv a ha
    calc ∫⁻ z, h (z⁻¹ * (a⁻¹ * y)) ∂ν
        = ∫⁻ z, h ((MeasurableEquiv.mulLeft a z)⁻¹ * y) ∂ν := by
          congr 1; ext z; simp [_root_.mul_inv_rev, mul_assoc]
      _ = ∫⁻ z, h (z⁻¹ * y) ∂(ν.map (MeasurableEquiv.mulLeft a)) :=
          (lintegral_map_equiv (fun z => h (z⁻¹ * y)) _).symm
      _ = ∫⁻ z, h (z⁻¹ * y) ∂ν := by rw [hmap]

  have hpos : ∀ O : Set G, IsOpen O → ∀ x ∈ O, x ∈ N → 0 < ν O := by
    intro O hO x hxO hxN
    rw [pos_iff_ne_zero]
    intro h0
    apply hne
    set U : G → Set G := fun n => (fun z => (x * n⁻¹) * z) ⁻¹' O with hU
    have hUo : ∀ n ∈ (N : Set G), IsOpen (U n) := fun n _ =>
      hO.preimage (continuous_const.mul continuous_id)
    have hU0 : ∀ n ∈ (N : Set G), ν (U n) = 0 := by
      intro n hn
      have hxn : x * n⁻¹ ∈ N := N.mul_mem hxN (N.inv_mem hn)
      have := hinv _ hxn
      rw [← this] at h0
      rwa [Measure.map_apply (measurable_const_mul _) hO.measurableSet] at h0
    obtain ⟨T, hTN, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable (N : Set G) U hUo
    have hNsub : (N : Set G) ⊆ ⋃ n ∈ T, U n := by
      rw [hTU]
      intro n hn
      exact Set.mem_biUnion hn (by simpa [hU, mul_assoc] using hxO)
    have hN0 : ν (N : Set G) = 0 :=
      measure_mono_null hNsub ((measure_biUnion_null_iff hTc).2 fun n hn => hU0 n (hTN hn))
    rw [← Measure.measure_univ_eq_zero, ← Set.union_compl_self (N : Set G)]
    exact measure_union_null hN0 hcompl

  let E := CompactExhaustion.choice G
  let F : ℕ → G → ENNReal := fun k y => ∫⁻ m, (E k).indicator 1 (m⁻¹ * y) ∂ν
  have hFm : ∀ k, Measurable (F k) := by
    intro k
    refine Measurable.lintegral_prod_right' (f := fun p : G × G => (E k).indicator 1 (p.2⁻¹ * p.1)) ?_
    exact (measurable_one.indicator (E.isCompact k).isClosed.measurableSet).comp
      (measurable_snd.inv.mul measurable_fst)
  have hFeq : ∀ k y, F k y = ν ((fun m => m⁻¹ * y) ⁻¹' E k) := by
    intro k y
    rw [← lintegral_indicator_one
      ((E.isCompact k).isClosed.measurableSet.preimage (measurable_inv.mul_const y))]
    rfl
  have hFtop : ∀ k y, F k y ≠ ⊤ := by
    intro k y
    rw [hFeq]
    refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_)
      (((E.isCompact k).image (f := fun u : G => y * u⁻¹)
        (continuous_const.mul continuous_inv)).measure_lt_top (μ := ν)))
    intro m hm
    exact ⟨m⁻¹ * y, hm, by simp⟩
  have hFpos : ∀ y, ∃ k, 0 < F k y := by
    intro y
    obtain ⟨k, hk⟩ := E.exists_mem_nhds y
    refine ⟨k, ?_⟩
    rw [hFeq]
    refine lt_of_lt_of_le (hpos ((fun m => m⁻¹ * y) ⁻¹' interior (E k))
      (isOpen_interior.preimage (continuous_inv.mul continuous_const)) 1 ?_ N.one_mem)
      (measure_mono (Set.preimage_mono interior_subset))
    simpa [mem_interior_iff_mem_nhds] using hk
  have hFinv : ∀ k y, ∀ᵐ m ∂ν, F k (m⁻¹ * y) = F k y := by
    intro k y
    filter_upwards [hae] with m hm
    exact horb ((E k).indicator 1) m hm y

  let w : ℕ → G → ENNReal := fun k y => (2⁻¹ : ENNReal) ^ k * (E k).indicator 1 y * (1 + F k y)⁻¹
  have hwm : ∀ k, Measurable (w k) := fun k =>
    (measurable_const.mul (measurable_one.indicator (E.isCompact k).isClosed.measurableSet)).mul
      (measurable_const.add (hFm k)).inv
  let f : G → ENNReal := fun y => ∑' k, w k y
  have hfm : Measurable f := Measurable.tsum hwm
  let T : G → ENNReal := fun y => ∫⁻ m, f (m⁻¹ * y) ∂ν
  have hTm : Measurable T :=
    Measurable.lintegral_prod_right' (f := fun p : G × G => f (p.2⁻¹ * p.1))
      (hfm.comp (measurable_snd.inv.mul measurable_fst))
  have hTinv : ∀ y, ∀ᵐ m ∂ν, T (m⁻¹ * y) = T y := by
    intro y
    filter_upwards [hae] with m hm
    exact horb f m hm y
  have hTsum : ∀ y, T y = ∑' k, (2⁻¹ : ENNReal) ^ k * (1 + F k y)⁻¹ * F k y := by
    intro y
    show ∫⁻ m, ∑' k, w k (m⁻¹ * y) ∂ν = _
    rw [lintegral_tsum (f := fun k m => w k (m⁻¹ * y)) fun k => ((hwm k).comp (measurable_inv.mul_const y)).aemeasurable]
    congr 1; ext k
    calc ∫⁻ m, w k (m⁻¹ * y) ∂ν
        = ∫⁻ m, (2⁻¹ : ENNReal) ^ k * (1 + F k y)⁻¹ * (E k).indicator 1 (m⁻¹ * y) ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [hFinv k y] with m hm
          simp only [w, hm]
          ring
      _ = (2⁻¹ : ENNReal) ^ k * (1 + F k y)⁻¹ * F k y := by
          rw [lintegral_const_mul]
          exact (measurable_one.indicator (E.isCompact k).isClosed.measurableSet).comp
            (measurable_inv.mul_const y)
  have hgeom : ∑' k : ℕ, (2⁻¹ : ENNReal) ^ k ≠ ⊤ := by
    rw [ENNReal.tsum_geometric]
    rw [ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  have hTtop : ∀ y, T y ≠ ⊤ := by
    intro y
    rw [hTsum]
    refine ne_top_of_le_ne_top hgeom (ENNReal.tsum_le_tsum fun k => ?_)
    rw [mul_assoc]
    refine mul_le_of_le_one_right' ?_
    rw [mul_comm, ← div_eq_mul_inv]
    exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact le_add_self)
  have hT0 : ∀ y, T y ≠ 0 := by
    intro y
    obtain ⟨k, hk⟩ := hFpos y
    rw [hTsum]
    refine (lt_of_lt_of_le ?_ (ENNReal.le_tsum k)).ne'
    rw [mul_assoc, mul_comm ((1 + F k y)⁻¹), ← div_eq_mul_inv]
    refine ENNReal.mul_pos (pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)) ?_
    exact (ENNReal.div_pos_iff.2 ⟨hk.ne', ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hFtop k y⟩⟩).ne'
  have hfle : ∀ y, f y ≠ ⊤ := by
    intro y
    refine ne_top_of_le_ne_top hgeom (ENNReal.tsum_le_tsum fun k => ?_)
    show (2⁻¹ : ENNReal) ^ k * (E k).indicator 1 y * (1 + F k y)⁻¹ ≤ _
    rw [mul_assoc]
    refine mul_le_of_le_one_right' ?_
    refine mul_le_one' ?_ (ENNReal.inv_le_one.2 le_self_add)
    by_cases hy : y ∈ E k <;> simp [hy]
  refine ⟨fun y => f y * (T y)⁻¹, hfm.mul hTm.inv, fun y => ?_, fun y => ?_⟩
  · exact ENNReal.mul_ne_top (hfle y) (ENNReal.inv_ne_top.2 (hT0 y))
  · calc ∫⁻ m, f (m⁻¹ * y) * (T (m⁻¹ * y))⁻¹ ∂ν
        = ∫⁻ m, f (m⁻¹ * y) * (T y)⁻¹ ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [hTinv y] with m hm
          rw [hm]
      _ = T y * (T y)⁻¹ := lintegral_mul_const _ (hfm.comp (measurable_inv.mul_const y))
      _ = 1 := ENNReal.mul_inv_cancel (hT0 y) (hTtop y)

end GlobalTheory.Dec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalFrameOfFlag
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem starProjection_eq_add_inf_orthogonal {n : ℕ}
    (U V : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (h : U ≤ V) (x : EuclideanSpace ℂ (Fin n)) :
    V.starProjection x = U.starProjection x + (Uᗮ ⊓ V).starProjection x := by
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact V.add_mem (h (U.starProjection_apply_mem x))
      (((Uᗮ ⊓ V).starProjection_apply_mem x).2)
  · rw [← Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection h, ← Submodule.inf_orthogonal,
      Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection h]
    refine ⟨?_, ?_⟩
    · rw [← sub_sub]
      exact Uᗮ.sub_mem (U.sub_starProjection_mem_orthogonal x)
        (((Uᗮ ⊓ V).starProjection_apply_mem x).1)
    · rw [add_comm, ← sub_sub]
      refine (Uᗮ ⊓ V)ᗮ.sub_mem ((Uᗮ ⊓ V).sub_starProjection_mem_orthogonal x) ?_
      exact Submodule.orthogonal_le (inf_le_left (a := Uᗮ) (b := V))
        (U.le_orthogonal_orthogonal (U.starProjection_apply_mem x))

theorem starProjection_flag_eq_sum {n a : ℕ}
    (W : Fin (a + 1) → Submodule ℂ (EuclideanSpace ℂ (Fin n))) (h0 : W 0 = ⊥) (hm : Monotone W)
    (l : Fin (a + 1)) (x : EuclideanSpace ℂ (Fin n)) :
    (W l).starProjection x = ∑ i ∈ univ.filter (fun i : Fin a => i.val < l.val),
      ((W i.castSucc)ᗮ ⊓ W i.succ).starProjection x := by
  induction l using Fin.induction with
  | zero =>
    have := (W 0).starProjection_apply_mem x
    have h2 : (W 0).starProjection x = 0 := by
      have h3 : (W 0).starProjection x ∈ (⊥ : Submodule ℂ _) := h0 ▸ this
      simpa using h3
    simp [h2]
  | succ i ih =>
    have hf : univ.filter (fun k : Fin a => k.val < i.succ.val)
        = insert i (univ.filter (fun k : Fin a => k.val < i.castSucc.val)) := by
      ext k
      simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.val_succ, Fin.val_castSucc,
        Fin.ext_iff]
      omega
    rw [hf, Finset.sum_insert (by simp), ← ih, add_comm]
    exact starProjection_eq_add_inf_orthogonal _ _ (hm (Fin.castSucc_le_succ i)) x

theorem exists_orthonormal_frame_of_flag (n a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (h0 : W 0 = ⊥) (hm : Monotone W)
    (hj : ∀ i : Fin a, Module.finrank ℂ (W i.succ) = Module.finrank ℂ (W i.castSucc) + j i) :
    ∃ T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ, (∀ i, (T i)ᴴ * T i = 1) ∧
      (∀ i k, i ≠ k → (T i)ᴴ * T k = 0) ∧ ∀ (l : Fin (a + 1)) (y : Fin n → ℂ),
        y ∈ W l ↔ (∑ i ∈ univ.filter (fun i : Fin a => i.val < l.val), T i * (T i)ᴴ) *ᵥ y = y := by
  let e : (Fin n → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) := (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm
  let V : Fin (a + 1) → Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
    fun l => (W l).map e.toLinearMap
  have hV0 : V 0 = ⊥ := by simp [V, h0]
  have hVm : Monotone V := fun l k h => Submodule.map_mono (hm h)
  have hVr : ∀ l, Module.finrank ℂ (V l) = Module.finrank ℂ (W l) :=
    fun l => LinearEquiv.finrank_map_eq e (W l)
  let P : Fin a → Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
    fun i => (V i.castSucc)ᗮ ⊓ V i.succ
  have hP : ∀ i, Module.finrank ℂ (P i) = j i := by
    intro i
    have h1 := Submodule.finrank_add_inf_finrank_orthogonal (hVm (Fin.castSucc_le_succ i))
    have h2 := hj i
    rw [hVr, hVr] at h1
    change Module.finrank ℂ ↥((V i.castSucc)ᗮ ⊓ V i.succ) = j i
    omega
  let b : ∀ i, OrthonormalBasis (Fin (j i)) ℂ (P i) :=
    fun i => (stdOrthonormalBasis ℂ (P i)).reindex (finCongr (hP i))
  let T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ :=
    fun i => Matrix.of fun r c => (b i c : EuclideanSpace ℂ (Fin n)) r
  have hT : ∀ i k c d, ((T i)ᴴ * T k) c d
      = inner ℂ (b i c : EuclideanSpace ℂ (Fin n)) (b k d : EuclideanSpace ℂ (Fin n)) := by
    intro i k c d
    simp only [Matrix.mul_apply, conjTranspose_apply, T, of_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply]
    exact Finset.sum_congr rfl fun r _ => mul_comm _ _
  have hlt : ∀ i k : Fin a, i < k → ∀ c d,
      inner ℂ (b i c : EuclideanSpace ℂ (Fin n)) (b k d : EuclideanSpace ℂ (Fin n)) = 0 := by
    intro i k h c d
    have h1 : (b i c : EuclideanSpace ℂ (Fin n)) ∈ V k.castSucc :=
      hVm (Fin.succ_le_castSucc_iff.2 h) (b i c).2.2
    exact Submodule.inner_right_of_mem_orthogonal h1 (b k d).2.1
  have hproj : ∀ i y, (T i * (T i)ᴴ) *ᵥ y = ((P i).starProjection (e y)).ofLp := by
    intro i y
    rw [(b i).starProjection_eq_sum_rankOne, ← Matrix.mulVec_mulVec]
    ext r
    simp only [_root_.sum_apply, InnerProductSpace.rankOne_apply, WithLp.ofLp_sum,
      Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
      EuclideanSpace.inner_eq_star_dotProduct]
    simp only [Matrix.mulVec, dotProduct, T, of_apply, conjTranspose_apply, Pi.star_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm]
    congr 1
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  refine ⟨T, ?_, ?_, ?_⟩
  · intro i
    ext c d
    rw [hT, ← Submodule.coe_inner, orthonormal_iff_ite.1 (b i).orthonormal, Matrix.one_apply]
  · intro i k hik
    ext c d
    rw [hT, Matrix.zero_apply]
    rcases lt_or_gt_of_ne hik with h | h
    · exact hlt i k h c d
    · rw [inner_eq_zero_symm]
      exact hlt k i h d c
  · intro l y
    have h1 : y ∈ W l ↔ e y ∈ V l := by
      simp [V]
    rw [h1, ← Submodule.starProjection_eq_self_iff, starProjection_flag_eq_sum V hV0 hVm,
      Matrix.sum_mulVec]
    simp only [hproj]
    constructor
    · intro h
      have h2 := congrArg WithLp.ofLp h
      rw [WithLp.ofLp_sum] at h2
      exact h2
    · intro h
      apply WithLp.ofLp_injective 2
      rw [WithLp.ofLp_sum]
      exact h

end GlobalTheory
end

