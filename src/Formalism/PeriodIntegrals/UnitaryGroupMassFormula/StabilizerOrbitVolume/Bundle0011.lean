module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0010
public import Formalism.PeriodIntegrals.Bundle0019
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVGlue
section
noncomputable section

namespace PI.VolStabSW

open MeasureTheory Topology Set

theorem densCos_of_filt (hP1 : HenselCount) (hP2 : CosDens) {V X Y : Type} [AddCommGroup V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V]
    [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [μ.IsAddHaarMeasure]
    [ν.IsAddHaarMeasure] (f : V → Y) (ι : X → Y) (hι : Function.Injective ι) (G : V → X)
    (hG : Continuous G) (hfG : ∀ v, f v = ι (G v)) (y : V) (Λ : ℕ → AddSubgroup V)
    (H : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set V)) (hΛc : ∀ n, IsCompact (Λ n : Set V))
    (hΛa : Antitone Λ) (hHo : ∀ n, IsOpen (H n : Set X)) (hHc : ∀ n, IsCompact (H n : Set X))
    (hHb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N) (D : V →+ X) (hD : ∀ n, (Λ n).map D = H n)
    (hyp : ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1)) :
    ∃ g : X → ℝ, Continuous g ∧ ∀ S : Set X, IsCompact S →
      ∫ v in f ⁻¹' (ι '' S), {z | z - y ∈ Λ 0}.indicator (fun _ => (1 : ℝ)) v ∂μ =
        ∫ b in S, g b ∂ν := by
  classical
  have hHa : Antitone H := by
    intro a b hab
    rw [← hD a, ← hD b]
    exact AddSubgroup.map_mono (hΛa hab)
  have hΦ : Continuous (fun Z : V => G (y + Z)) := hG.comp (continuous_const.add continuous_id)
  have hΦm : Measurable (fun Z : V => G (y + Z)) := hΦ.measurable
  have hΛ0m : MeasurableSet (Λ 0 : Set V) := (hΛo 0).measurableSet
  set m : Measure X := (μ.restrict (Λ 0 : Set V)).map (fun Z : V => G (y + Z)) with hm
  haveI : IsFiniteMeasure (μ.restrict (Λ 0 : Set V)) :=
    isFiniteMeasure_restrict.mpr (hΛc 0).measure_lt_top.ne
  haveI : IsFiniteMeasure m := by rw [hm]; infer_instance
  have hmT : ∀ T : Set X, MeasurableSet T → m T = μ {Z | Z ∈ Λ 0 ∧ G (y + Z) ∈ T} := by
    intro T hT
    rw [hm, Measure.map_apply hΦm hT, Measure.restrict_apply' hΛ0m]
    congr 1
    ext Z
    simp [and_comm]
  have hopen : ∀ (h : X) (k : ℕ), IsOpen {z : X | z - h ∈ H k} := fun h k =>
    (hHo k).preimage (continuous_sub_right h)
  have hν0 : ν (H 0 : Set X) ≠ 0 := ((hHo 0).measure_pos ν ⟨0, (H 0).zero_mem⟩).ne'
  have hνt : ν (H 0 : Set X) ≠ ⊤ := (hHc 0).measure_lt_top.ne
  have htrans : ∀ (h : X) (k : ℕ), ν {z : X | z - h ∈ H k} = ν (H k : Set X) := by
    intro h k
    have he : {z : X | z - h ∈ H k} = (fun z => -h + z) ⁻¹' (H k : Set X) := by
      ext z
      simp [sub_eq_neg_add]
    rw [he, measure_preimage_add]
  set κ : ENNReal := μ (Λ 0 : Set V) / ν (H 0 : Set X) with hκ
  have hdens : ∀ k (h : X), h - G y ∈ H 0 →
      m {z | z - h ∈ H k} = κ * ν {z | z - h ∈ H k} := by
    intro k h hh
    have hH := hP1 V X μ ν inferInstance inferInstance Λ H hΛo hΛc hΛa hHo hHc D hD G y hyp k h hh
    rw [hmT _ (hopen h k).measurableSet, htrans, hκ, div_eq_mul_inv, mul_right_comm,
      ← div_eq_mul_inv, ENNReal.eq_div_iff hν0 hνt, mul_comm]
    exact hH
  have hcompl : m {z | z - G y ∈ H 0}ᶜ = 0 := by
    rw [hmT _ (hopen (G y) 0).measurableSet.compl]
    refine (congrArg (fun s : Set V => μ s) (Set.ext fun Z => ?_)).trans measure_empty
    constructor
    · rintro ⟨hZ, hZ'⟩
      have h1 := hyp 0 0 (Λ 0).zero_mem Z hZ
      simp only [add_zero, zero_add] at h1
      have h2 : D Z ∈ H 0 := by
        rw [← hD 0]
        exact AddSubgroup.mem_map_of_mem D hZ
      have hmem : G (y + Z) - G y ∈ H 0 := by
        simpa using (H 0).add_mem (hHa (Nat.zero_le 1) h1) h2
      exact hZ' hmem
    · intro hZ
      exact False.elim hZ
  have hcos := hP2 X ν m inferInstance H hHo hHc hHa hHb (G y) κ hcompl hdens
  set C : Set X := {z | z - G y ∈ H 0} with hC
  have hCo : IsOpen C := hopen (G y) 0
  have hCc : IsClosed C := (hHc 0).isClosed.preimage (continuous_sub_right (G y))
  refine ⟨C.indicator (fun _ => κ.toReal), ?_, ?_⟩
  · refine continuous_indicator ?_ continuousOn_const
    intro a ha
    rw [hCc.frontier_eq, hCo.interior_eq, Set.diff_self] at ha
    simp at ha
  · intro S hS
    have hSm : MeasurableSet S := hS.isClosed.measurableSet
    have hpre : f ⁻¹' (ι '' S) = G ⁻¹' S := by
      ext v
      simp [hfG, hι.mem_set_image]
    have hCV : MeasurableSet {z : V | z - y ∈ Λ 0} :=
      ((hΛo 0).preimage (continuous_sub_right y)).measurableSet
    have key : m S = μ ({z : V | z - y ∈ Λ 0} ∩ G ⁻¹' S) := by
      rw [hmT S hSm, ← measure_preimage_add μ y ({z : V | z - y ∈ Λ 0} ∩ G ⁻¹' S)]
      congr 1
      ext Z
      simp
    rw [hpre, integral_indicator_const _ hCV, integral_indicator_const _ hCo.measurableSet]
    simp only [Measure.real, smul_eq_mul, mul_one]
    rw [Measure.restrict_apply hCV, Measure.restrict_apply hCo.measurableSet, ← key, hcos S hS,
      ENNReal.toReal_mul, Set.inter_comm, mul_comm]

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVNA
section
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology Filter
open scoped TensorProduct

private theorem exists_pow_smul_mem_nhds_of_isCompact' {𝕜 V : Type} [Field 𝕜] [TopologicalSpace 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [TopologicalSpace V] [ContinuousSMul 𝕜 V] (L : Set V) (hLc : IsCompact L)
    (π : 𝕜) (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0)) (N : Set V) (hN : N ∈ 𝓝 (0 : V)) :
    ∃ k : ℕ, ∀ y ∈ L, π ^ k • y ∈ N := by
  have h : ∀ᶠ c in 𝓝 (0 : 𝕜), ∀ y ∈ L, c • y ∈ N := by
    refine hLc.eventually_forall_of_forall_eventually fun y _ => ?_
    have ht : Tendsto (fun z : 𝕜 × V => z.1 • z.2) (𝓝 ((0 : 𝕜), y)) (𝓝 ((0 : 𝕜) • y)) :=
      continuous_smul.continuousAt
    rw [zero_smul] at ht
    exact ht hN
  exact (hπ.eventually h).exists

theorem hasCOSub_of_lat {𝕜 V : Type} [Field 𝕜] [TopologicalSpace 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [TopologicalSpace V] [ContinuousSMul 𝕜 V] (L : AddSubgroup V)
    (hLo : IsOpen (L : Set V)) (hLc : IsCompact (L : Set V)) (π : 𝕜) (h0 : π ≠ 0)
    (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0)) : HasCOSub V := by
  intro N hN
  obtain ⟨k, hk⟩ := exists_pow_smul_mem_nhds_of_isCompact' (L : Set V) hLc π hπ N hN
  have hc : π ^ k ≠ 0 := pow_ne_zero k h0
  have himg : ((L.map (DistribSMul.toAddMonoidHom V (π ^ k)) : AddSubgroup V) : Set V) =
      (fun x => π ^ k • x) '' (L : Set V) := by
    ext x
    simp
  refine ⟨L.map (DistribSMul.toAddMonoidHom V (π ^ k)), ?_, ?_, ?_⟩
  · rw [himg]
    exact isOpenMap_smul₀ hc _ hLo
  · rw [himg]
    exact hLc.image (continuous_const_smul _)
  · rw [himg]
    rintro _ ⟨y, hy, rfl⟩
    exact hk y hy

theorem exists_pow_tendsto_zero_Fv {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : Fv F v, π ≠ 0 ∧ Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hv : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    rw [v.valuedAdicCompletion_eq_valuation' π, hπ]
  refine ⟨π, fun h => ?_, ?_⟩
  · rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  · have h1 : Valued.v (π : v.adicCompletion F) < 1 := by
      rw [hv]
      decide
    have hlt : ‖(π : v.adicCompletion F)‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 h1
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt

def latSub {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (a M : ℕ) :
    AddSubgroup (Fin a → Fin M → Fv F v ⊗[F] E) where
  carrier := latV (M := M) (n := a) b v
  add_mem' := by
    intro x y hx hy
    simp only [latV, Set.mem_setOf_eq] at hx hy ⊢
    intro i j k
    simp only [Pi.add_apply, map_add (f := _), Finsupp.add_apply]
    exact add_mem (hx i j k) (hy i j k)
  zero_mem' := by
    simp only [latV, Set.mem_setOf_eq]
    intro i j k
    simp only [Pi.zero_apply, map_zero, Finsupp.zero_apply]
    exact zero_mem _
  neg_mem' := by
    intro x hx
    simp only [latV, Set.mem_setOf_eq] at hx ⊢
    intro i j k
    simp only [Pi.neg_apply, map_neg, Finsupp.neg_apply]
    exact neg_mem (hx i j k)

def scaledB (𝕜 : Type) {V : Type} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] (L : AddSubgroup V)
    (Λ : AddSubgroup V) : Prop :=
  ∃ c : 𝕜, c ≠ 0 ∧ Λ = L.map (DistribSMul.toAddMonoidHom V c)

theorem isCOBasis_scaled {𝕜 V : Type} [Field 𝕜] [TopologicalSpace 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [TopologicalSpace V] [ContinuousSMul 𝕜 V] (L : AddSubgroup V)
    (hLo : IsOpen (L : Set V)) (hLc : IsCompact (L : Set V)) (π : 𝕜) (h0 : π ≠ 0)
    (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0)) : IsCOBasis (scaledB 𝕜 L) := by
  intro N hN
  obtain ⟨k, hk⟩ := exists_pow_smul_mem_nhds_of_isCompact' (L : Set V) hLc π hπ N hN
  have hc : π ^ k ≠ 0 := pow_ne_zero k h0
  have himg : ((L.map (DistribSMul.toAddMonoidHom V (π ^ k)) : AddSubgroup V) : Set V) =
      (fun x => π ^ k • x) '' (L : Set V) := by
    ext x
    simp
  refine ⟨L.map (DistribSMul.toAddMonoidHom V (π ^ k)), ⟨π ^ k, hc, rfl⟩, ?_, ?_, ?_⟩
  · rw [himg]
    exact isOpenMap_smul₀ hc _ hLo
  · rw [himg]
    exact hLc.image (continuous_const_smul _)
  · rw [himg]
    rintro _ ⟨y, hy, rfl⟩
    exact hk y hy

theorem isCOBasis_latSub {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (a M : ℕ) :
    IsCOBasis (scaledB (Fv F v) (latSub b v a M)) := by
  obtain ⟨π, h0, hπ⟩ := exists_pow_tendsto_zero_Fv v
  exact isCOBasis_scaled (latSub b v a M)
    (PositiveNearLattice.isClopen_latV (b := b) (v := v) a M).isOpen
    (PositiveNearLattice.isCompact_latV (b := b) (v := v) a M) π h0 hπ

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibTop
section
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct

theorem tensFacts_of_fib {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (a : ℕ) (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R]
    [SecondCountableTopology R] (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j)
    (hfree : IsOpen {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X}) :
    TensFacts F E σ M J a R := ⟨inferInstance, inferInstance, inferInstance, isClosed_HermR (R := R) σ a,
  continuous_gramR (R := R) σ J, fun X => gramR_mem (R := R) σ hσ J hJ X, hfree⟩

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensVolT
section
noncomputable section

namespace PI.VolStabSW

namespace VolAAW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW

theorem eq_one_of_pow (z : ℂ) (hz : ‖z‖ = 1) (h : ∀ k : ℕ, 1 / 2 < (z ^ (2 ^ k)).re) : z = 1 := by
  have hsq : ∀ w : ℂ, ‖w‖ = 1 → w.re ^ 2 + w.im ^ 2 = 1 := by
    intro w hw
    have h1 := Complex.sq_norm w
    rw [hw, Complex.normSq_apply] at h1
    nlinarith
  have hre : ∀ w : ℂ, ‖w‖ = 1 → (w ^ 2).re = 2 * w.re ^ 2 - 1 := by
    intro w hw
    have := hsq w hw
    rw [sq, Complex.mul_re]
    nlinarith
  have hn : ∀ k : ℕ, ‖z ^ (2 ^ k)‖ = 1 := fun k => by rw [norm_pow, hz, one_pow]
  have hle : ∀ k : ℕ, (z ^ (2 ^ k)).re ≤ 1 := fun k => (Complex.re_le_norm _).trans (hn k).le
  have key : ∀ k : ℕ, (3 : ℝ) ^ k * (1 - z.re) ≤ 1 - (z ^ (2 ^ k)).re := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : z ^ (2 ^ (k + 1)) = (z ^ (2 ^ k)) ^ 2 := by rw [pow_succ, pow_mul]
      rw [e, hre _ (hn k)]
      have h1 := h k
      have h2 := hle k
      rw [pow_succ]
      nlinarith [mul_nonneg (sub_nonneg.2 h2) (by linarith : (0 : ℝ) ≤ 2 * (z ^ 2 ^ k).re - 1)]
  have hz1 : z.re ≤ 1 := by simpa using hle 0
  have hre1 : z.re = 1 := by
    by_contra hne
    have hε : 0 < 1 - z.re := by
      rcases lt_or_eq_of_le hz1 with h' | h'
      · linarith
      · exact absurd h' hne
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / (1 - z.re)) (by norm_num : (1 : ℝ) < 3)
    have h1 := key k
    have h2 := h k
    have h3 : 1 < (3 : ℝ) ^ k * (1 - z.re) := by
      rw [div_lt_iff₀ hε] at hk
      linarith
    linarith
  have him : z.im = 0 := by
    have := hsq z hz
    rw [hre1] at this
    nlinarith
  exact Complex.ext (by simp [hre1]) (by simp [him])

variable {F : Type} [Field F] [NumberField F]

theorem psiV_nsmul (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (y : Fv F v) :
    psiV F ψ v (n • y) = psiV F ψ v y ^ n := by
  induction n with
  | zero =>
    simp only [zero_smul, pow_zero, psiV]
    have : pairA F 0 (singleV F v 0) = 0 := by
      have h := singleV_add (F := F) v 0 0
      rw [add_zero] at h
      have h0 : singleV F v 0 = 0 := by
        have := congrArg (fun x => x - singleV F v 0) h
        exact (by simpa using this : (0 : Af F) = singleV F v 0).symm
      rw [h0]
      rfl
    rw [this, AddChar.map_zero_eq_one]
  | succ n ih => rw [succ_nsmul, psiV_add, ih, pow_succ]

theorem ev_triv (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) :
    ∀ᶠ v in cofinite, ∀ y ∈ v.adicCompletionIntegers F, psiV F ψ v y = 1 := by
  classical
  set U : Set (AF F) := {x | 1 / 2 < (ψ x).re} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const (Complex.continuous_re.comp hψ.1)
  let Φ : (∀ v : HeightOneSpectrum (𝓞 F),
      ((v.adicCompletionIntegers F : Set (v.adicCompletion F)))) → AF F :=
    fun x => pairA F 0 (RestrictedProduct.structureMap _ _ Filter.cofinite x)
  have hΦ : Continuous Φ :=
    continuous_const.prodMk RestrictedProduct.isEmbedding_structureMap.continuous
  let x0 : ∀ v : HeightOneSpectrum (𝓞 F), ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun v => ⟨0, zero_mem _⟩
  have hx0 : Φ x0 = 0 := by
    show pairA F 0 _ = 0
    have : (RestrictedProduct.structureMap _ _ Filter.cofinite x0 : Af F) = 0 := by
      apply RestrictedProduct.ext
      intro j
      rfl
    rw [this]
    rfl
  have hx0U : x0 ∈ Φ ⁻¹' U := by
    simp only [Set.mem_preimage, hx0, hUdef, Set.mem_setOf_eq, AddChar.map_zero_eq_one,
      Complex.one_re]
    norm_num
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 (hU.preimage hΦ) x0 hx0U
  filter_upwards [(I.finite_toSet).eventually_cofinite_notMem] with v hv
  have hbig : ∀ y ∈ v.adicCompletionIntegers F, 1 / 2 < (psiV F ψ v y).re := by
    intro y hy
    have hmem : Function.update x0 v ⟨y, hy⟩ ∈ (I : Set _).pi u := by
      intro w hw
      have hwv : w ≠ v := fun h => hv (h ▸ hw)
      rw [Function.update_of_ne hwv]
      exact (hu w hw).2
    have e : Φ (Function.update x0 v ⟨y, hy⟩) = pairA F 0 (singleV F v y) := by
      show pairA F 0 _ = _
      congr 1
      apply RestrictedProduct.ext
      intro j
      show ((Function.update x0 v ⟨y, hy⟩ j : _) : Fv F j) =
        (Pi.single v y : ∀ w : HeightOneSpectrum (𝓞 F), Fv F w) j
      by_cases hj : j = v
      · subst hj
        simp
      · rw [Function.update_of_ne hj, Pi.single_eq_of_ne hj]
    have := hsub hmem
    simp only [Set.mem_preimage, e, hUdef, Set.mem_setOf_eq] at this
    exact this
  intro y hy
  refine eq_one_of_pow (psiV F ψ v y) (hψ.2.1 _) ?_
  intro k
  rw [← psiV_nsmul]
  apply hbig
  rw [nsmul_eq_mul]
  exact mul_mem (by exact_mod_cast (natCast_mem (v.adicCompletionIntegers F) (2 ^ k))) hy

def CondExact : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ᶠ v in cofinite, ∀ t : Fv F v,
      (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (s * t) = 1) → t ∈ v.adicCompletionIntegers F

theorem condAA_of (hE : CondExact) : CondAA := by
  intro F _ _ ψ hψ
  filter_upwards [hE F ψ hψ, ev_triv ψ hψ] with v h1 h2
  intro t
  refine ⟨h1 t, fun ht s hs => h2 _ (mul_mem hs ht)⟩

end VolAAW

end PI.VolStabSW
end
end

