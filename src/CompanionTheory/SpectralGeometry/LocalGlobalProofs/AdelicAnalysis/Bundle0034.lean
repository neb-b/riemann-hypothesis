module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0020
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0030
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0031
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianOrbitLocalSectionSubgroup

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductFold
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem sigR_scalar_tmul (σ : E →ₐ[F] E) (α : R) :
    sigR R σ (α ⊗ₜ[F] (1 : E)) = α ⊗ₜ[F] (1 : E) := by
  simp [sigR]

theorem gramR_scl_tmul (σ : E →ₐ[F] E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (α : R)
    (y : Fin 1 → Fin N → R ⊗[F] E) (i j : Fin 1) :
    gramR R σ J (scl (α ⊗ₜ[F] (1 : E)) y) i j =
      (α ⊗ₜ[F] (1 : E)) * (α ⊗ₜ[F] (1 : E)) * gramR R σ J y i j := by
  simp only [gramR, hR, hform, scl, map_mul, sigR_scalar_tmul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem corner_half_trace_of_pure_tensor [CharZero F] {d : ℕ} (b : Module.Basis (Fin d) F E) (hd : Module.finrank F E = 2)
    (x : R) (S : Matrix (Fin (0 + 1)) (Fin (0 + 1)) (R ⊗[F] E)) (h : S 0 0 = x ⊗ₜ[F] (1 : E)) :
    s0 R S = x := by
  have hd2 : d = 2 := by
    rw [← hd, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd2
  have e : x ⊗ₜ[F] (1 : E) = algebraMap R (R ⊗[F] E) x := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [s0, h, e, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b), Fintype.card_fin,
    two_nsmul, ← two_mul, ← mul_assoc]
  have : algebraMap F R (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap F R) 2, ← map_mul]
    simp
  rw [this, one_mul]

end Alg

theorem chi_at_fibre : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ x ∈ B₀, ∀ y₀ : Fin 1 → Fin (M + 1) → R ⊗[F] E, gramR R σ (blockOne (algebraMap F E t) J) y₀ = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → chi σ J t s a b lam ((Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) = ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S' in Unt σ R n, ∫⁻ X, φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) c X)) ∂(m' S') ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ x hx y₀ hy₀
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id D.hR
  have hJt := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap F E σ M J D.hJ t D.ht
  obtain ⟨-, -, -, -, -, -, -, hBor, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ D.hCM R
  obtain ⟨-, -, -, -, -, hact⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ D.hCM (M + 1) _ hJt R
  obtain ⟨-, -, -, hBH, hliftn⟩ := _root_.GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ D.hCM R n
  obtain ⟨-, -, -, -, hlift⟩ := _root_.GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ D.hCM R (n + 1)
  obtain ⟨hUo, -, hoff, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm'
  obtain ⟨g, -, hg⟩ := hlift (M + 1) _ hJt
  have hcoord := (_root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.GramCoord.coords F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D).1 x hx
  have hd : Module.finrank F E = 2 := D.hCM.2.2.1
  set u : R := ((a x : Rˣ) : R) with hu

  have hy00 : gramR R σ (blockOne (algebraMap F E t) J) y₀ 0 0 = algebraMap F R t ⊗ₜ[F] (1 : E) := by
    rw [hy₀]; rfl
  have hG : gramR R σ (blockOne (algebraMap F E t) J) (scl (u ⊗ₜ[F] (1 : E)) y₀) 0 0 =
      x ⊗ₜ[F] (1 : E) := by
    rw [gramR_scl_tmul, hy00, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    have hq : u ^ 2 * algebraMap F R t = x := (D.hsq x hx).symm
    rw [mul_one, mul_one, ← pow_two, hq]
  have hs0 : s0 R (gramR R σ (blockOne (algebraMap F E t) J) (scl (u ⊗ₜ[F] (1 : E)) y₀)) = x :=
    corner_half_trace_of_pure_tensor R b hd x _ hG
  have hsT : sTil σ J t s a (scl (u ⊗ₜ[F] (1 : E)) y₀) = s y₀ := by
    unfold sTil
    rw [hs0]
    congr 1
    funext i j
    simp only [scl, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [hu, Units.mul_inv]
    exact mul_one _
  have hsec := congrFun (D.hsec y₀ hy₀) 0
  have hcons : ∀ (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E),
      (Fin.cons (scl (u ⊗ₜ[F] (1 : E)) y₀ 0)
        (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (fun j => Fin.cons (c j) (X j))) :
          Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =
      actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X) := by
    intro c X
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have e : (Fin.cons (u ⊗ₜ[F] (1 : E)) (fun _ => 0) : Fin (M + 1) → R ⊗[F] E) =
          (u ⊗ₜ[F] (1 : E)) • (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E) := by
        funext k
        refine Fin.cases ?_ (fun l => ?_) k <;> simp
      simp only [Fin.cons_zero, vec, actW, actTup]
      rw [e, Matrix.mulVec_smul]
      simp only [actW, actTup] at hsec
      rw [hsec]
      funext k
      simp [scl, mul_comm]
    · simp [vec, actW, actTup]
  have hmem : ∀ (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E),
      actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X) ∈
        (Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) ↔
      X ∈ {X : Fin n → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det} := by
    intro c X
    have hinv := (hact (n + 1)).2.2.2 (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X)
    simp only [Uset, Set.mem_preimage, hinv, Set.mem_setOf_eq]
    constructor
    · rintro ⟨S, ⟨-, hSu⟩, hS⟩
      have := (hcoord c X S hS).2.2
      rwa [this] at hSu
    · intro hX
      have h3 := hcoord c X (g (vec (u ⊗ₜ[F] (1 : E)) c X)) (hg _).symm
      refine ⟨g (vec (u ⊗ₜ[F] (1 : E)) c X), ⟨?_, ?_⟩, (hg _).symm⟩
      · rw [h3.1]; exact hx
      · rw [h3.2.2]; exact hX
  haveI := hBor n M
  haveI := hBor (n + 1) (M + 1)
  have hUt : MeasurableSet (Unt σ R n) := hUo.measurableSet
  have hUd : MeasurableSet {X : Fin n → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det} := by
    obtain ⟨g', hg'c, hg'⟩ := hliftn M J D.hJ
    have e : {X : Fin n → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det} = g' ⁻¹' Unt σ R n := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Unt, hg' X]
    rw [e]
    exact (hUo.preimage hg'c).measurableSet
  have hψ : ∀ c : Fin n → R ⊗[F] E, Measurable fun X : Fin n → Fin M → R ⊗[F] E =>
      φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X)) := by
    intro c
    have hv : Continuous fun X : Fin n → Fin M → R ⊗[F] E => vec (u ⊗ₜ[F] (1 : E)) c X := by
      refine continuous_pi fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · exact continuous_const
      · refine continuous_pi fun k => ?_
        refine Fin.cases ?_ (fun l => ?_) k
        · exact continuous_const
        · exact (continuous_apply l).comp (continuous_apply j)
    have hc : Continuous fun X : Fin n → Fin M → R ⊗[F] E =>
        actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X) :=
      (hact (n + 1)).1.comp (continuous_const.prodMk hv)
    exact hφ.comp hc.measurable
  unfold chi
  rw [hsT]
  refine lintegral_congr fun c => ?_
  calc _ = ∫⁻ X : Fin n → Fin M → R ⊗[F] E,
        {X : Fin n → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det}.indicator (fun X =>
          φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X))) X
        ∂(coordW R b lam n M) := by
        refine lintegral_congr fun X => ?_
        rw [hcons c X]
        by_cases h : X ∈ {X : Fin n → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det}
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hmem c X).2 h)]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hmem c X).1 h'))]
    _ = ∫⁻ X in {X : Fin n → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det},
          φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X))
        ∂(coordW R b lam n M) := lintegral_indicator hUd _
    _ = ∫⁻ S', ∫⁻ X, φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀)
            (vec (u ⊗ₜ[F] (1 : E)) c X)) ∂(m' S') ∂(coordHerm R σ b lam n) :=
        D.hm'.2.1 _ (hψ c)
    _ = _ := by
        rw [← lintegral_indicator hUt]
        refine lintegral_congr fun S' => ?_
        by_cases h : S' ∈ Unt σ R n
        · rw [Set.indicator_of_mem h]
        · rw [Set.indicator_of_notMem h, hoff S' h, lintegral_zero_measure]

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductFubini
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology ProbabilityTheory
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

theorem isSFiniteKernel_of_forall_univ_lt_top {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (η : Kernel α β) (h : ∀ a, η a Set.univ < ⊤) : IsSFiniteKernel η := by
  classical
  have hmeas : Measurable fun a => η a Set.univ := η.measurable_coe MeasurableSet.univ
  let g : α → ℕ := fun a => ⌊(η a Set.univ).toReal⌋₊
  have hg : Measurable g := Nat.measurable_floor.comp hmeas.ennreal_toReal
  have hB : ∀ j : ℕ, MeasurableSet (g ⁻¹' {j}) := fun j => hg (measurableSet_singleton j)
  let ηs : ℕ → Kernel α β := fun j => Kernel.piecewise (hB j) η 0
  have hfin : ∀ j, IsFiniteKernel (ηs j) := by
    intro j
    refine ⟨⟨(j : ℝ≥0∞) + 1, by simp [ENNReal.add_lt_top], fun a => ?_⟩⟩
    by_cases ha : a ∈ g ⁻¹' {j}
    · have hj : g a = j := ha
      have h1 : (η a Set.univ).toReal < (j : ℝ) + 1 := by
        have := Nat.lt_floor_add_one (η a Set.univ).toReal
        simpa [g, hj] using this
      have h2 : η a Set.univ = ENNReal.ofReal (η a Set.univ).toReal :=
        (ENNReal.ofReal_toReal (h a).ne).symm
      simp only [ηs, Kernel.piecewise_apply, if_pos ha]
      rw [h2]
      refine ENNReal.ofReal_le_of_le_toReal ?_
      rw [ENNReal.toReal_add (by simp) (by simp)]
      simpa using h1.le
    · have ha' : ¬ g a = j := ha
      simp [ηs, Kernel.piecewise_apply, ha']
  have hsum : η = Kernel.sum ηs := by
    ext a s hs
    rw [Kernel.sum_apply, Measure.sum_apply _ hs, tsum_eq_single (g a)]
    · simp [ηs, Kernel.piecewise_apply]
    · intro j hj
      have ha' : ¬ g a = j := fun h' => hj h'.symm
      simp [ηs, Kernel.piecewise_apply, ha']
  rw [hsum]
  exact ⟨⟨fun j => ηs j, hfin, rfl⟩⟩

theorem isSFiniteKernel_of_locallyFinite {α β : Type} [MeasurableSpace α] [TopologicalSpace β]
    [MeasurableSpace β] [BorelSpace β] [T2Space β] [SigmaCompactSpace β]
    (κ : Kernel α β) (h : ∀ a, IsLocallyFiniteMeasure (κ a)) : IsSFiniteKernel κ := by
  let C : ℕ → Set β := disjointed (compactCovering β)
  have hCm : ∀ k, MeasurableSet (C k) := fun k =>
    MeasurableSet.disjointed (fun i => (isCompact_compactCovering β i).measurableSet) k
  have hCd : Pairwise (Function.onFun Disjoint C) := disjoint_disjointed _
  have hCu : ⋃ k, C k = Set.univ := by
    simp only [C, iUnion_disjointed]
    exact iUnion_compactCovering β
  have hCf : ∀ a k, κ a (C k) < ⊤ := fun a k => by
    haveI := h a
    exact (measure_mono (disjointed_subset _ k)).trans_lt
      (isCompact_compactCovering β k).measure_lt_top
  have hk : ∀ k, IsSFiniteKernel (Kernel.restrict κ (hCm k)) := fun k =>
    isSFiniteKernel_of_forall_univ_lt_top _ (fun a => by
      rw [Kernel.restrict_apply]
      simpa using hCf a k)
  have hsum : κ = Kernel.sum fun k => Kernel.restrict κ (hCm k) := by
    ext a s hs
    rw [Kernel.sum_apply]
    simp only [Kernel.restrict_apply]
    rw [← Measure.restrict_iUnion hCd hCm, hCu, Measure.restrict_univ]
  rw [hsum]
  infer_instance

theorem measurable_vec_triple {K : Type} [Zero K] [MeasurableSpace K] {M n : ℕ} :
    Measurable (fun p : K × (Fin n → K) × (Fin n → Fin M → K) =>
      (vec p.1 p.2.1 p.2.2 : Fin (n + 1) → Fin (M + 1) → K)) := by
  refine Measurable.of_eval fun a => Measurable.of_eval fun i => ?_
  induction a using Fin.cases with
  | zero =>
    induction i using Fin.cases with
    | zero => simpa [vec] using measurable_fst
    | succ i => simpa [vec] using measurable_const
  | succ j =>
    induction i using Fin.cases with
    | zero =>
      simp only [vec, Fin.cons_succ, Fin.cons_zero]
      exact (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)
    | succ i =>
      simp only [vec, Fin.cons_succ]
      exact (measurable_pi_apply i).comp
        ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))

theorem measurable_Pint (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ)
    (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E))
    (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J))
    (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0)
    (D : StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm)
    (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) (hφ : Measurable φ) :
    Measurable (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n =>
      Pint σ J t m₁ m' s φ z.1 z.2.1 z.2.2) := by
  obtain ⟨iTR, iLR, iSR, iTR2, -⟩ := D.hR
  haveI := iTR
  haveI := iLR
  haveI := iSR
  haveI := iTR2
  obtain ⟨iTK, iLK, iSK, iT2K, -, -, -, iBor, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ D.hCM R
  haveI := iTK
  haveI := iLK
  haveI := iSK
  haveI := iT2K
  have hJ' := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap F E σ M J D.hJ t D.ht
  obtain ⟨-, hloc, -, hmeas, -, -⟩ :=
    _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm'
  obtain ⟨-, hloc₁, -⟩ :=
    _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁
  obtain ⟨-, -, iSH, -, iBH, hH⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ D.hCM (M + 1) _ hJ' R
  haveI := iSH
  haveI := iBH
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := iBor n M
  haveI : BorelSpace (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := iBor (n + 1) (M + 1)
  haveI : BorelSpace (Fin 1 → Fin (M + 1) → R ⊗[F] E) := iBor 1 (M + 1)
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have hact := (hH (n + 1)).1
  have hten : Measurable (fun r : R => r ⊗ₜ[F] (1 : E)) := by
    haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)
    have hc : Continuous (fun r : R => r • (1 : R ⊗[F] E)) :=
      Continuous.smul (f := fun r : R => r) (g := fun _ : R => (1 : R ⊗[F] E))
        continuous_id continuous_const
    have he : (fun r : R => r ⊗ₜ[F] (1 : E)) = fun r : R => r • (1 : R ⊗[F] E) := by
      funext r
      simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
    rw [he]
    exact hc.measurable
  let κ : Kernel (HermR R σ n) (Fin n → Fin M → R ⊗[F] E) :=
    ⟨m', Measure.measurable_of_measurable_coe _ hmeas⟩
  haveI : IsSFiniteKernel κ := isSFiniteKernel_of_locallyFinite κ hloc
  let κ' : Kernel ((R × (Fin n → R ⊗[F] E) × HermR R σ n) × (Fin 1 → Fin (M + 1) → R ⊗[F] E))
      (Fin n → Fin M → R ⊗[F] E) :=
    κ.comap (fun p => p.1.2.2) (measurable_snd.comp (measurable_snd.comp measurable_fst))
  haveI := hloc₁ (hermScal R σ (algebraMap F R t))
  have hvec : Measurable (fun q : ((R × (Fin n → R ⊗[F] E) × HermR R σ n) ×
      (Fin 1 → Fin (M + 1) → R ⊗[F] E)) × (Fin n → Fin M → R ⊗[F] E) =>
        (vec (q.1.1.1 ⊗ₜ[F] (1 : E)) q.1.1.2.1 q.2 : Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) :=
    measurable_vec_triple.comp ((hten.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
      (((measurable_fst.comp (measurable_snd.comp (measurable_fst.comp measurable_fst)))).prodMk
        measurable_snd))
  have hΦ : Measurable (fun q : ((R × (Fin n → R ⊗[F] E) × HermR R σ n) ×
      (Fin 1 → Fin (M + 1) → R ⊗[F] E)) × (Fin n → Fin M → R ⊗[F] E) =>
        actW R σ (blockOne (algebraMap F E t) J) (s q.1.2)
          (vec (q.1.1.1 ⊗ₜ[F] (1 : E)) q.1.1.2.1 q.2)) :=
    hact.measurable.comp ((D.hs.comp (measurable_snd.comp measurable_fst)).prodMk hvec)
  have hinner := Measurable.lintegral_kernel_prod_right' (κ := κ') (hφ.comp hΦ)
  exact Measurable.lintegral_prod_right' (ν := m₁ (hermScal R σ (algebraMap F R t))) hinner

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductNormalization
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

theorem measurable_vec {K : Type} [Zero K] [MeasurableSpace K] {M n : ℕ} (α : K) (c : Fin n → K) :
    Measurable (fun X : Fin n → Fin M → K => vec α c X) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun k => ?_
  induction i using Fin.cases with
  | zero => simpa [vec] using (measurable_const : Measurable fun _ : Fin n → Fin M → K =>
      (Fin.cons α (fun _ => 0) : Fin (M + 1) → K) k)
  | succ i =>
    induction k using Fin.cases with
    | zero => simpa [vec] using (measurable_const : Measurable fun _ : Fin n → Fin M → K => c i)
    | succ k =>
      have h : Measurable fun X : Fin n → Fin M → K => X i k :=
        (measurable_pi_apply k).comp (measurable_pi_apply i)
      simpa [vec] using h

theorem fibS_support : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ S : HermR R σ (n + 1), fibS σ J t m₁ m' s B₀ a κ₁ cm S (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩ gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' (Bset R σ t a B₀ : Set (HermR R σ (n + 1)))))ᶜ = 0 := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D S
  by_cases hS : S ∈ Bset R σ t a B₀
  swap
  · simp [fibS, hS]
  obtain ⟨h1, h2, h3, h4, -⟩ := id D.hR
  have hk := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ D.hCM R
  have hJ' := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap F E σ M J D.hJ t D.ht
  have hH := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ D.hCM (M + 1) _ hJ' R
  obtain ⟨-, -, hscH, -, hbH, hactH⟩ := hH
  obtain ⟨-, -, hscK, hT2K, -, -, -, hbor, -, hgram⟩ := hk
  obtain ⟨hcont, -, -, hpres⟩ := hactH (n + 1)
  have hcoord := (_root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.GramCoord.coords F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D).2
  have hker' := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm'
  have hker₁ := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁
  obtain ⟨-, hlf', -, -, -, hfib'⟩ := hker'
  obtain ⟨-, hlf₁, -⟩ := hker₁
  haveI := hbor (n + 1) (M + 1)
  haveI := hbor n M
  haveI := hbor 1 (M + 1)
  haveI := hlf₁ (hermScal R σ (algebraMap F R t))
  haveI := hlf' (schur R σ t a S)
  let α : R ⊗[F] E := ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E)
  let c := cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))
  let f : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) → (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) :=
    fun p => actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec α c p.2)
  have hfm : Measurable f := by
    have := hcont.measurable.comp
      ((D.hs.comp measurable_fst).prodMk ((measurable_vec α c).comp measurable_snd))
    exact this
  have hcl : MeasurableSet ((gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))})ᶜ) :=
    ((isClosed_singleton.preimage (hgram (n + 1) (M + 1) (blockOne (algebraMap F E t) J))).measurableSet).compl
  have hae : ∀ᵐ p ∂((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))),
      gramR R σ (blockOne (algebraMap F E t) J) (f p) = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) := by
    have h := (Measure.quasiMeasurePreserving_snd (μ := m₁ (hermScal R σ (algebraMap F R t)))
      (ν := m' (schur R σ t a S))).ae (hfib' (schur R σ t a S))
    filter_upwards [h] with p hp
    change gramR R σ (blockOne (algebraMap F E t) J)
      (actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec α c p.2)) = _
    rw [hpres]
    exact hcoord S p.2 hS.1 hp
  have hsub : (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩
      gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' (Bset R σ t a B₀ : Set (HermR R σ (n + 1)))))ᶜ ⊆
      (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))})ᶜ := by
    intro x hx hxS
    exact hx ⟨hxS, ⟨S, hS, (Set.mem_singleton_iff.1 hxS).symm⟩⟩
  refine measure_mono_null hsub ?_
  have hmap : (((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))).map f)
      ((gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))})ᶜ) = 0 := by
    rw [Measure.map_apply hfm hcl]
    refine measure_mono_null ?_ (ae_iff.1 hae)
    intro p hp hpS
    exact hp hpS
  unfold fibS
  rw [Set.indicator_of_mem hS, Measure.smul_apply]
  change _ • (((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))).map f) _ = 0
  rw [hmap, smul_zero]

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianLocalContinuousCongruenceSection
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.SW

theorem exists_local_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (S : HermR R σ n), IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det → ∃ (B : Set (HermR R σ n)) (g : HermR R σ n → GL (Fin n) (R ⊗[F] E)), IsOpen B ∧ S ∈ B ∧ ContinuousOn g B ∧ g S = 1 ∧ ∀ S' ∈ B, (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) (g S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (g S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ hR n S hS
  obtain ⟨Q, o, -, -, ho, hform⟩ := _root_.GlobalTheory.CompanionTheory.SW.tri_slice F E σ hσ R hR n S hS
  have hc : cT (sigR R σ) (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = 1 := by
    ext i j
    by_cases h : i = j
    · subst h; simp [cT]
    · simp [cT, Matrix.one_apply, h, Ne.symm h]
  have ho1 : o 1 = S := by
    apply Subtype.ext
    rw [hform]
    simp [hc]
  have hinv : Function.LeftInverse (Function.invFun o) o := Function.leftInverse_invFun ho.injective
  refine ⟨Set.range o, fun S' => ((Function.invFun o S' : Q) : GL (Fin n) (R ⊗[F] E)),
    ho.isOpen_range, ⟨1, ho1⟩, ?_, ?_, ?_⟩
  · have hcont : ContinuousOn (Function.invFun o) (Set.range o) := by
      rw [continuousOn_iff_continuous_restrict]
      have h1 : (fun y : Set.range o => Function.invFun o y.1) = ho.isEmbedding.toHomeomorph.symm := by
        funext y
        obtain ⟨_, x, rfl⟩ := y
        show Function.invFun o (o x) = _
        rw [hinv x]
        exact ho.isEmbedding.toHomeomorph.eq_symm_apply.2 (Subtype.ext rfl)
      have h2 : Continuous (fun y : Set.range o => Function.invFun o y.1) := by
        rw [h1]
        exact Homeomorph.continuous _
      exact h2
    exact continuous_subtype_val.comp_continuousOn hcont
  · show ((Function.invFun o S : Q) : GL (Fin n) (R ⊗[F] E)) = 1
    rw [← ho1, hinv 1]
    rfl
  · rintro _ ⟨x, rfl⟩
    simp only [hinv x]
    exact hform x

end GlobalTheory.CompanionTheory.SW
end
end

