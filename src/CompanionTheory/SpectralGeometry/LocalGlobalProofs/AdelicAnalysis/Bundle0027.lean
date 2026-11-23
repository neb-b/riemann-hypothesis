module

public import Mathlib
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LintegralMulRightOfMem
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ProperActionOrbitMeasure
section
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.AbsUniq

def stabilizerOf {G V : Type} [Group G] (act : G → V → V) (h1 : ∀ x, act 1 x = x)
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V) : Subgroup G where
  carrier := {g | act g x₀ = x₀}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [hm, hb, ha]
  one_mem' := h1 x₀
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h : act a⁻¹ (act a x₀) = x₀ := by rw [← hm, inv_mul_cancel, h1]
    rwa [ha] at h

def orbitQuot {G V : Type} [Group G] (act : G → V → V) (h1 : ∀ x, act 1 x = x)
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V) :
    G ⧸ stabilizerOf act h1 hm x₀ → V :=
  Quotient.lift (fun g => act g x₀) (by
    intro a b hab
    have h : a⁻¹ * b ∈ stabilizerOf act h1 hm x₀ := QuotientGroup.leftRel_apply.1 hab
    have h' : act (a⁻¹ * b) x₀ = x₀ := h
    show act a x₀ = act b x₀
    conv_lhs => rw [← h']
    rw [← hm, mul_inv_cancel_left])

theorem orbitQuot_mk {G V : Type} [Group G] (act : G → V → V) (h1 : ∀ x, act 1 x = x)
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V) (g : G) :
    orbitQuot act h1 hm x₀ (g : G ⧸ stabilizerOf act h1 hm x₀) = act g x₀ := rfl

theorem orbitQuot_injective {G V : Type} [Group G] (act : G → V → V) (h1 : ∀ x, act 1 x = x)
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V) :
    Function.Injective (orbitQuot act h1 hm x₀) := by
  intro a b
  induction a using QuotientGroup.induction_on with | _ a => ?_
  induction b using QuotientGroup.induction_on with | _ b => ?_
  intro hab
  rw [orbitQuot_mk, orbitQuot_mk] at hab
  refine QuotientGroup.eq.2 ?_
  show act (a⁻¹ * b) x₀ = x₀
  rw [hm, ← hab, ← hm, inv_mul_cancel, h1]

theorem orbitQuot_smul {G V : Type} [Group G] (act : G → V → V) (h1 : ∀ x, act 1 x = x)
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V) (g : G)
    (y : G ⧸ stabilizerOf act h1 hm x₀) :
    orbitQuot act h1 hm x₀ (g • y) = act g (orbitQuot act h1 hm x₀ y) := by
  induction y using QuotientGroup.induction_on with | _ a => ?_
  show act (g * a) x₀ = act g (act a x₀)
  rw [hm]

theorem range_orbitQuot {G V : Type} [Group G] (act : G → V → V) (h1 : ∀ x, act 1 x = x)
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V) (Z : Set V) (hx : x₀ ∈ Z)
    (hinv : ∀ g, ∀ x ∈ Z, act g x ∈ Z) (htr : ∀ x ∈ Z, ∀ y ∈ Z, ∃ g, act g x = y) :
    Set.range (orbitQuot act h1 hm x₀) = Z := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    induction a using QuotientGroup.induction_on with | _ a => ?_
    exact hinv a x₀ hx
  · intro hy
    obtain ⟨g, rfl⟩ := htr x₀ hx y hy
    exact ⟨(g : G ⧸ stabilizerOf act h1 hm x₀), rfl⟩

theorem continuous_orbitQuot {G V : Type} [Group G] [TopologicalSpace G]
    [TopologicalSpace V] (act : G → V → V) (hc : Continuous fun p : G × V => act p.1 p.2)
    (h1 : ∀ x, act 1 x = x)
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V) :
    Continuous (orbitQuot act h1 hm x₀) :=
  Continuous.quotient_lift (hc.comp (continuous_id.prodMk continuous_const)) _

theorem measurableEmbedding_orbitQuot {G V : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    [TopologicalSpace V] [T2Space V] [SecondCountableTopology V] [MeasurableSpace V]
    [BorelSpace V] (act : G → V → V) (hc : Continuous fun p : G × V => act p.1 p.2)
    (h1 : ∀ x, act 1 x = x)
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V) (Z : Set V) (hZ : IsClosed Z)
    (hx : x₀ ∈ Z) (hinv : ∀ g, ∀ x ∈ Z, act g x ∈ Z)
    (htr : ∀ x ∈ Z, ∀ y ∈ Z, ∃ g, act g x = y) :
    MeasurableEmbedding (orbitQuot act h1 hm x₀) := by
  have hcont : Continuous fun g : G => act g x₀ :=
    hc.comp (continuous_id.prodMk continuous_const)
  refine ⟨orbitQuot_injective act h1 hm x₀, ?_, ?_⟩
  · intro A hA
    rw [measurableSet_quotient]
    exact hcont.measurable hA
  · intro S hS
    have hS' : MeasurableSet ((fun g : G => (g : G ⧸ stabilizerOf act h1 hm x₀)) ⁻¹' S) :=
      measurableSet_quotient.1 hS
    let o : G → Z := fun g => ⟨act g x₀, hinv g x₀ hx⟩
    have hoc : Continuous o := hcont.subtype_mk _
    have hos : Function.Surjective o := by
      rintro ⟨y, hy⟩
      obtain ⟨g, rfl⟩ := htr x₀ hx y hy
      exact ⟨g, rfl⟩
    haveI : PolishSpace G := PI.AprimeInfA.polish_of_lcsc G
    have hb := hoc.map_eq_borel hos
    let T : Set Z := Subtype.val ⁻¹' (orbitQuot act h1 hm x₀ '' S)
    have hT : MeasurableSet T := by
      have hpre : o ⁻¹' T = (fun g : G => (g : G ⧸ stabilizerOf act h1 hm x₀)) ⁻¹' S := by
        ext g
        constructor
        · rintro ⟨y, hy, hyg⟩
          have : y = (g : G ⧸ stabilizerOf act h1 hm x₀) :=
            orbitQuot_injective act h1 hm x₀ hyg
          simpa [this] using hy
        · intro hg
          exact ⟨_, hg, rfl⟩
      have hm' : MeasurableSet[MeasurableSpace.map o ‹MeasurableSpace G›] T := by
        show MeasurableSet (o ⁻¹' T)
        rw [hpre]
        exact hS'
      rw [hb, ← BorelSpace.measurable_eq] at hm'
      exact hm'
    have himg : orbitQuot act h1 hm x₀ '' S = Subtype.val '' T := by
      rw [Subtype.image_preimage_coe, Set.inter_eq_right.2]
      rintro _ ⟨y, -, rfl⟩
      rw [← range_orbitQuot act h1 hm x₀ Z hx hinv htr]
      exact ⟨y, rfl⟩
    rw [himg]
    exact (MeasurableEmbedding.subtype_coe hZ.measurableSet).measurableSet_image.2 hT

theorem comap_orbitQuot_invariant {G V : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    [TopologicalSpace V] [T2Space V] [SecondCountableTopology V] [MeasurableSpace V]
    [BorelSpace V] (act : G → V → V) (hc : Continuous fun p : G × V => act p.1 p.2)
    (h1 : ∀ x, act 1 x = x)
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V)
    (hφ : MeasurableEmbedding (orbitQuot act h1 hm x₀)) (μ : Measure V)
    (hμ : ∀ g, μ.map (act g) = μ) (g : G) (s : Set (G ⧸ stabilizerOf act h1 hm x₀))
    (hs : MeasurableSet s) :
    μ.comap (orbitQuot act h1 hm x₀) ((fun y => g • y) ⁻¹' s) =
      μ.comap (orbitQuot act h1 hm x₀) s := by
  have hact : Measurable (act g) :=
    (hc.comp (continuous_const.prodMk continuous_id)).measurable
  rw [hφ.comap_apply, hφ.comap_apply]
  have himg : orbitQuot act h1 hm x₀ '' ((fun y => g • y) ⁻¹' s) =
      act g ⁻¹' (orbitQuot act h1 hm x₀ '' s) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨g • y, hy, orbitQuot_smul act h1 hm x₀ g y⟩
    · rintro ⟨y, hy, hyx⟩
      refine ⟨g⁻¹ • y, ?_, ?_⟩
      · show g • g⁻¹ • y ∈ s
        simpa using hy
      · rw [orbitQuot_smul, hyx, ← hm, inv_mul_cancel, h1]
  rw [himg]
  conv_rhs => rw [← hμ g]
  rw [Measure.map_apply hact (hφ.measurableSet_image.2 hs)]

theorem invariant_measure_unique :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
      [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
      (V : Type) [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V]
      [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (act : G → V → V),
      (Continuous fun p : G × V => act p.1 p.2) → (∀ x, act 1 x = x) →
      (∀ g h x, act (g * h) x = act g (act h x)) → ∀ Z : Set V, IsClosed Z →
      (∀ g, ∀ x ∈ Z, act g x ∈ Z) → (∀ x ∈ Z, ∀ y ∈ Z, ∃ g, act g x = y) →
      ∀ (μ ν : Measure V), IsLocallyFiniteMeasure μ → IsLocallyFiniteMeasure ν → μ Zᶜ = 0 →
      ν Zᶜ = 0 → (∀ g, μ.map (act g) = μ) → (∀ g, ν.map (act g) = ν) → ν ≠ 0 →
      ∃ c : ℝ≥0, μ = c • ν := by
  intro G _ _ _ _ _ _ _ _ V _ _ _ _ _ _ act hc h1 hm Z hZ hinv htr μ ν hμf hνf hμZ hνZ hμ hν hν0

  have hne : Z.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    apply hν0
    rw [← Measure.measure_univ_eq_zero]
    simpa [hemp] using hνZ
  obtain ⟨x₀, hx⟩ := hne
  set H := stabilizerOf act h1 hm x₀ with hH
  have hcont : Continuous fun g : G => act g x₀ :=
    hc.comp (continuous_id.prodMk continuous_const)
  have hHc : IsClosed (H : Set G) := by
    have : (H : Set G) = (fun g : G => act g x₀) ⁻¹' {x₀} := rfl
    rw [this]
    exact isClosed_singleton.preimage hcont
  set φ := orbitQuot act h1 hm x₀ with hφdef
  have hφc : Continuous φ := continuous_orbitQuot act hc h1 hm x₀
  have hφ : MeasurableEmbedding φ :=
    measurableEmbedding_orbitQuot act hc h1 hm x₀ Z hZ hx hinv htr
  have hr : Set.range φ = Z := range_orbitQuot act h1 hm x₀ Z hx hinv htr
  have hfin : ∀ (m : Measure V), IsLocallyFiniteMeasure m → ∀ K : Set (G ⧸ H), IsCompact K →
      m.comap φ K < ⊤ := by
    intro m _ K hK
    rw [hφ.comap_apply]
    exact (hK.image hφc).measure_lt_top
  have hrec : ∀ (m : Measure V), m Zᶜ = 0 → (m.comap φ).map φ = m := by
    intro m hm0
    rw [hφ.map_comap, hr]
    exact Measure.restrict_eq_self_of_ae_mem (by
      rw [ae_iff]; exact hm0)
  have hρ0 : ν.comap φ ≠ 0 := by
    intro h0
    apply hν0
    rw [← hrec ν hνZ, h0, Measure.map_zero]
  obtain ⟨c, hcc⟩ := PI.wqUnique G H hHc (ν.comap φ) (μ.comap φ) hρ0 (hfin ν hνf)
    (comap_orbitQuot_invariant act hc h1 hm x₀ hφ ν hν) (hfin μ hμf)
    (comap_orbitQuot_invariant act hc h1 hm x₀ hφ μ hμ)
  have hμν : μ = c • ν := by
    have hφν : AEMeasurable φ (ν.comap φ) := hφ.measurable.aemeasurable
    rw [← hrec μ hμZ, hcc, Measure.map_smul, hrec ν hνZ]
    exact hφν

  have hct : c ≠ ⊤ := by
    rintro rfl
    have hK : ∃ K : Set V, IsCompact K ∧ ν K ≠ 0 := by
      by_contra hno
      push_neg at hno
      apply hν0
      rw [← Measure.measure_univ_eq_zero, ← iUnion_compactCovering V]
      exact measure_iUnion_null fun n => hno _ (isCompact_compactCovering V n)
    obtain ⟨K, hKc, hK0⟩ := hK
    have h := hKc.measure_lt_top (μ := μ)
    rw [hμν, Measure.smul_apply, smul_eq_mul, ENNReal.top_mul hK0] at h
    exact lt_irrefl _ h
  refine ⟨c.toNNReal, ?_⟩
  rw [hμν]
  ext s hs
  simp [Measure.smul_apply, ENNReal.smul_def, ENNReal.coe_toNNReal hct]

end GlobalTheory.CompanionTheory.SW.AbsUniq
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ScalarHermitianTraceAndUnit
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB.ScalTrace

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem hermScal_entry {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (R : Type) [CommRing R] [Algebra F R] (s : R) :
    (hermScal R σ s : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 = algebraMap R (R ⊗[F] E) s := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem trace_det : ∀ (F E : Type) [Field F] [Field E] [Algebra F E], (1 / 2 : F) ≠ 0 → Module.finrank F E = 2 → ∀ (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] (β : F), algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((hermScal R σ (algebraMap F R β) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) = algebraMap F R β ∧ (β ≠ 0 → IsUnit ((hermScal R σ (algebraMap F R β) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E))).det) := by
  intro F E _ _ _ h2 hf σ R _ _ β
  have hfin : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hf
  have hent := hermScal_entry σ R (algebraMap F R β)
  refine ⟨?_, fun hβ => ?_⟩
  · rw [hent, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b) (algebraMap F R β)]
    have h20 : (2 : F) ≠ 0 := by
      intro h
      apply h2
      simp [h]
    have hhalf : algebraMap F R (1 / 2) * algebraMap F R 2 = 1 := by
      rw [← map_mul, one_div, inv_mul_cancel₀ h20, map_one]
    rw [Fintype.card_fin, nsmul_eq_mul]
    have h2R : ((2 : ℕ) : R) = algebraMap F R 2 := by
      rw [map_ofNat]
      norm_num
    rw [h2R, ← mul_assoc, hhalf, one_mul]
  · rw [Matrix.det_fin_one, hent]
    exact ((isUnit_iff_ne_zero.2 hβ).map (algebraMap F R)).map (algebraMap R (R ⊗[F] E))

end GlobalTheory.CompanionTheory.SW.BB.ScalTrace
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SizeFunctionRapidDecayIntegrable
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.SizeInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def compReal (hF : IsTotallyReal F) (v : InfinitePlace F) : v.Completion ≃+* ℝ :=
  InfinitePlace.Completion.ringEquivRealOfIsReal (hF.isReal v)

theorem continuous_compReal (hF : IsTotallyReal F) (v : InfinitePlace F) :
    Continuous (compReal hF v) :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal (hF.isReal v)).continuous

theorem continuous_compReal_symm (hF : IsTotallyReal F) (v : InfinitePlace F) :
    Continuous (compReal hF v).symm :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal (hF.isReal v)).symm.continuous

theorem norm_compReal (hF : IsTotallyReal F) (v : InfinitePlace F) (x : v.Completion) :
    ‖compReal hF v x‖ = ‖x‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (hF.isReal v)).norm_map_of_map_zero
    (map_zero _) x

theorem secondCountable_Ainf (hF : IsTotallyReal F) : SecondCountableTopology (Ainf F) := by
  haveI : ∀ v : InfinitePlace F, SecondCountableTopology v.Completion := fun v =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (hF.isReal v)).toHomeomorph.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology (∀ v : InfinitePlace F, v.Completion))

section Coord

variable {d : ℕ} (hF : IsTotallyReal F) (b : Module.Basis (Fin d) F E)

def ainfEquiv : Ainf F ≃+ (InfinitePlace F → ℝ) where
  toFun x v := compReal hF v (x v)
  invFun w := (fun v => (compReal hF v).symm (w v) : ∀ v : InfinitePlace F, v.Completion)
  left_inv x := by funext v; exact (compReal hF v).symm_apply_apply _
  right_inv w := by funext v; exact (compReal hF v).apply_symm_apply _
  map_add' x y := by funext v; exact map_add (compReal hF v) (x v) (y v)

theorem continuous_ainfEquiv : Continuous (ainfEquiv hF) :=
  continuous_pi fun v => (continuous_compReal hF v).comp (continuous_apply (A := fun v : InfinitePlace F => v.Completion) v)

theorem continuous_ainfEquiv_symm : Continuous (ainfEquiv hF).symm := by
  have h : Continuous fun (w : InfinitePlace F → ℝ) (v : InfinitePlace F) =>
      ((compReal hF v).symm (w v) : v.Completion) :=
    continuous_pi fun v => (continuous_compReal_symm hF v).comp (continuous_apply v)
  exact h

def coordEquiv : Ainf F ⊗[F] E ≃+ (Fin d → InfinitePlace F → ℝ) :=
  (Algebra.TensorProduct.basis (Ainf F) b).equivFun.toAddEquiv.trans
    (AddEquiv.piCongrRight fun _ => ainfEquiv hF)

theorem abs_coordEquiv (y : Ainf F ⊗[F] E) (k : Fin d) (v : InfinitePlace F) :
    ‖coordEquiv hF b y k v‖ = ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y k v‖ :=
  norm_compReal hF v _

def tupEquiv (n M : ℕ) :
    (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin n → Fin M → Fin d → InfinitePlace F → ℝ) :=
  AddEquiv.piCongrRight fun _ => AddEquiv.piCongrRight fun _ => coordEquiv hF b

theorem tupEquiv_apply (n M : ℕ) (X : Fin n → Fin M → Ainf F ⊗[F] E) (a : Fin n) (i : Fin M) :
    tupEquiv hF b n M X a i = coordEquiv hF b (X a i) := rfl

theorem norm_tupEquiv_le (n M : ℕ) (X : Fin n → Fin M → Ainf F ⊗[F] E) :
    ‖tupEquiv hF b n M X‖ ≤ sizeTup b X := by
  have h0 : ∀ (y : Ainf F ⊗[F] E) (k : Fin d) (v : InfinitePlace F),
      0 ≤ ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y k v‖ := fun _ _ _ => norm_nonneg _
  have hI : ∀ y : Ainf F ⊗[F] E, 0 ≤ sizeInf b y := fun y =>
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun v _ => h0 y k v
  have hT : 0 ≤ sizeTup b X := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => hI _
  refine (pi_norm_le_iff_of_nonneg hT).2 fun a => (pi_norm_le_iff_of_nonneg hT).2 fun i =>
    (pi_norm_le_iff_of_nonneg hT).2 fun k => (pi_norm_le_iff_of_nonneg hT).2 fun v => ?_
  rw [tupEquiv_apply, abs_coordEquiv]
  calc ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X a i) k v‖
      ≤ ∑ v', ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X a i) k v'‖ :=
        Finset.single_le_sum (f := fun v' => ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X a i) k v'‖)
          (fun v' _ => norm_nonneg _) (Finset.mem_univ v)
    _ ≤ sizeInf b (X a i) :=
        Finset.single_le_sum (f := fun k' => ∑ v', ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X a i) k' v'‖)
          (fun k' _ => Finset.sum_nonneg fun v' _ => norm_nonneg _) (Finset.mem_univ k)
    _ ≤ ∑ i', sizeInf b (X a i') :=
        Finset.single_le_sum (f := fun i' => sizeInf b (X a i')) (fun i' _ => hI _) (Finset.mem_univ i)
    _ ≤ sizeTup b X :=
        Finset.single_le_sum (f := fun a' => ∑ i', sizeInf b (X a' i'))
          (fun a' _ => Finset.sum_nonneg fun i' _ => hI _) (Finset.mem_univ a)

theorem continuous_coordEquiv
    (hc : IsHomeomorph fun (y : Ainf F ⊗[F] E) (k : Fin d) =>
      (Algebra.TensorProduct.basis (Ainf F) b).repr y k) :
    Continuous (coordEquiv hF b) :=
  continuous_pi fun k => (continuous_ainfEquiv hF).comp ((continuous_apply k).comp hc.continuous)

theorem continuous_coordEquiv_symm
    (hc : IsHomeomorph fun (y : Ainf F ⊗[F] E) (k : Fin d) =>
      (Algebra.TensorProduct.basis (Ainf F) b).repr y k) :
    Continuous (coordEquiv hF b).symm := by
  have h1 : Continuous fun w : Fin d → InfinitePlace F → ℝ => fun k => (ainfEquiv hF).symm (w k) :=
    continuous_pi fun k => (continuous_ainfEquiv_symm hF).comp (continuous_apply k)
  have h2 := (hc.homeomorph _).symm.continuous.comp h1
  convert h2 using 1
  funext w
  apply (hc.homeomorph _).injective
  rw [Function.comp_apply, Homeomorph.apply_symm_apply]
  funext k
  show (Algebra.TensorProduct.basis (Ainf F) b).repr ((coordEquiv hF b).symm w) k = _
  apply (ainfEquiv hF).injective
  rw [AddEquiv.apply_symm_apply]
  have := congrFun ((coordEquiv hF b).apply_symm_apply w) k
  exact this

end Coord

theorem size_neg_pow_integrable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (n M : ℕ) (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)), μ.IsAddHaarMeasure → Continuous (sizeTup b : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ) ∧ (∀ X : Fin n → Fin M → Ainf F ⊗[F] E, 0 ≤ sizeTup b X) ∧ ∃ N : ℕ, ∫⁻ X, ENNReal.ofReal (((1 + sizeTup b X) ^ N)⁻¹) ∂μ < ⊤ := by
  intro F E _ _ _ _ _ σ hCM d b n M μ hμ
  have hF : IsTotallyReal F := hCM.1
  haveI : SecondCountableTopology (Ainf F) := secondCountable_Ainf hF
  haveI : T2Space (Ainf F) := inferInstanceAs (T2Space (∀ v : InfinitePlace F, v.Completion))
  obtain ⟨hring, -, -, -, -, -, hhom, hborel, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Ainf F)
  haveI := hring
  haveI := hborel n M
  have hc := hhom d b
  have hce := continuous_coordEquiv hF b hc
  have hcs := continuous_coordEquiv_symm hF b hc
  have hnorm : ∀ y : Ainf F ⊗[F] E, sizeInf b y = ∑ k, ∑ v, ‖coordEquiv hF b y k v‖ := fun y => by
    simp only [abs_coordEquiv, sizeInf]
  have hcontI : Continuous (sizeInf b : Ainf F ⊗[F] E → ℝ) := by
    have : (sizeInf b : Ainf F ⊗[F] E → ℝ) = fun y => ∑ k, ∑ v, ‖coordEquiv hF b y k v‖ := funext hnorm
    rw [this]
    refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun v _ => ?_
    exact ((continuous_apply v).comp ((continuous_apply k).comp hce)).norm
  have hcontT : Continuous (sizeTup b : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ) := by
    unfold sizeTup
    refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun i _ => ?_
    exact hcontI.comp ((continuous_apply i).comp (continuous_apply a))
  have hI0 : ∀ y : Ainf F ⊗[F] E, 0 ≤ sizeInf b y := fun y =>
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun v _ => norm_nonneg _
  have hT0 : ∀ X : Fin n → Fin M → Ainf F ⊗[F] E, 0 ≤ sizeTup b X := fun X =>
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => hI0 _
  refine ⟨hcontT, hT0, ?_⟩
  let e := tupEquiv hF b n M
  have he : Continuous e :=
    continuous_pi fun a => continuous_pi fun i => hce.comp ((continuous_apply i).comp (continuous_apply a))
  have hes : Continuous e.symm :=
    continuous_pi fun a => continuous_pi fun i => hcs.comp ((continuous_apply i).comp (continuous_apply a))
  let W := Fin n → Fin M → Fin d → InfinitePlace F → ℝ
  haveI b1 : BorelSpace (Fin d → InfinitePlace F → ℝ) := inferInstance
  haveI s1 : SecondCountableTopology (Fin d → InfinitePlace F → ℝ) := inferInstance
  haveI b2 : BorelSpace (Fin M → Fin d → InfinitePlace F → ℝ) := Pi.borelSpace
  haveI s2 : SecondCountableTopology (Fin M → Fin d → InfinitePlace F → ℝ) := inferInstance
  haveI b3 : BorelSpace W := Pi.borelSpace
  haveI : (Measure.map e μ).IsAddHaarMeasure := e.isAddHaarMeasure_map μ he hes
  obtain ⟨N, hN⟩ := exists_nat_gt (Module.finrank ℝ W : ℝ)
  refine ⟨N, ?_⟩
  have hfin := finite_integral_one_add_norm (μ := Measure.map e μ) (E := W) (r := (N : ℝ)) hN
  have hmeas : Measurable fun y : W => ENNReal.ofReal ((1 + ‖y‖) ^ (-(N : ℝ))) := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact (Continuous.rpow_const (by fun_prop) fun y => Or.inl (by positivity)).measurable
  rw [lintegral_map hmeas he.measurable] at hfin
  refine lt_of_le_of_lt (lintegral_mono fun X => ?_) hfin
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : (0 : ℝ) < 1 + ‖e X‖ := by positivity
  rw [Real.rpow_neg h1.le, Real.rpow_natCast]
  have h2 : 1 + ‖e X‖ ≤ 1 + sizeTup b X := by
    have := norm_tupEquiv_le hF b n M X
    linarith
  exact inv_anti₀ (pow_pos h1 N) (pow_le_pow_left₀ h1.le h2 N)

end GlobalTheory.CompanionTheory.SW.SizeInt
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryActionConsTupleMeasurable
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.Fact

theorem continuous_consTup {K : Type} [Zero K] [One K] [TopologicalSpace K] (n M : ℕ) :
    Continuous (fun X : Fin n → Fin M → K => (consTup X : Fin (n + 1) → Fin (M + 1) → K)) := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun a => ?_) a
  · exact continuous_const
  · refine Fin.cases ?_ (fun i => ?_) i
    · exact continuous_const
    · exact (continuous_apply i).comp (continuous_apply a)

theorem measurable_actW_consTup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (g : HA R σ J), Measurable (fun X : Fin n → Fin M → R ⊗[F] E => actW R σ J g (consTup X)) := by
  intro F E _ _ _ _ _ σ hCM R _ _ _ _ _ hR n M J g
  obtain ⟨h1, h2, h3, h4, -⟩ := hR
  have hk := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  haveI : IsTopologicalRing (R ⊗[F] E) := hk.1
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := hk.2.2.2.2.2.2.2.1 n M
  haveI : BorelSpace (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := hk.2.2.2.2.2.2.2.1 (n + 1) (M + 1)
  have hc : Continuous (fun X : Fin n → Fin M → R ⊗[F] E => actW R σ J g (consTup X)) := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    simp only [actW, actTup, Matrix.mulVec, dotProduct]
    refine continuous_finsetSum _ fun j _ => continuous_const.mul ?_
    exact (continuous_apply j).comp ((continuous_apply a).comp (continuous_consTup n M))
  exact hc.measurable

end GlobalTheory.CompanionTheory.SW.Fact
end

