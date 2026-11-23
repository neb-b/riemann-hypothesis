module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0044
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0042
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0043
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0039
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0036

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleHaarEqProductLocalMeasures
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.WBox

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def cK (R : Type) [CommRing R] [Algebra F R] {d : ℕ} (b : Module.Basis (Fin d) F E) (y : R ⊗[F] E)
    (k : Fin d) : R :=
  (Algebra.TensorProduct.basis R b).repr y k

theorem cK_map {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (f : R →ₐ[F] R') (y : R ⊗[F] E) (k : Fin d) :
    cK R' b (Algebra.TensorProduct.map f (AlgHom.id F E) y) k = f (cK R b y k) := by
  induction y with
  | add x y hx hy =>
    simp only [cK] at hx hy ⊢
    simp [map_add (f := _), hx, hy]
  | tmul r e =>
    simp [cK, Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]

variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [SecondCountableTopology R]
  [MeasurableSpace R] [BorelSpace R] {d : ℕ} {b : Module.Basis (Fin d) F E}

def eK (hK : IsHomeomorph (cK (F := F) (E := E) R b)) : (R ⊗[F] E) ≃ᵐ (Fin d → R) :=
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  (hK.homeomorph _).toMeasurableEquiv

def eW (hK : IsHomeomorph (cK (F := F) (E := E) R b)) (n M : ℕ) :
    (Fin n → Fin M → R ⊗[F] E) ≃ᵐ (Fin n × Fin M × Fin d → R) where
  toFun X p := eK R hK (X p.1 p.2.1) p.2.2
  invFun Y a i := (eK R hK).symm fun k => Y (a, i, k)
  left_inv X := by
    funext a i
    simp
  right_inv Y := by
    funext p
    simp
  measurable_toFun := Measurable.of_eval fun p =>
    (measurable_pi_apply p.2.2).comp ((eK R hK).measurable.comp
      ((measurable_pi_apply p.2.1).comp (measurable_pi_apply p.1)))
  measurable_invFun := Measurable.of_eval fun a => Measurable.of_eval fun i =>
    (eK R hK).symm.measurable.comp (Measurable.of_eval fun k => measurable_pi_apply (a, i, k))

theorem eW_apply (hK : IsHomeomorph (cK (F := F) (E := E) R b)) (n M : ℕ)
    (X : Fin n → Fin M → R ⊗[F] E) (p : Fin n × Fin M × Fin d) :
    eW R hK n M X p = cK R b (X p.1 p.2.1) p.2.2 := rfl

theorem coordK_eq (hK : IsHomeomorph (cK (F := F) (E := E) R b)) (lam : Measure R) :
    coordK R b lam = (Measure.pi fun _ : Fin d => lam).map (eK R hK).symm := by
  rw [MeasurableEquiv.map_symm]
  rfl

theorem sigmaFinite_coordK (hK : IsHomeomorph (cK (F := F) (E := E) R b)) (lam : Measure R)
    [SigmaFinite lam] : SigmaFinite (coordK R b lam) := by
  rw [coordK_eq R hK lam]
  exact (eK R hK).symm.measurableEmbedding.sigmaFinite_map

theorem map_coordW (hK : IsHomeomorph (cK (F := F) (E := E) R b)) (lam : Measure R) [SigmaFinite lam]
    (n M : ℕ) :
    MeasurePreserving (eW R hK n M) (coordW R b lam n M)
      (Measure.pi fun _ : Fin n × Fin M × Fin d => lam) := by
  haveI := sigmaFinite_coordK R hK lam
  refine ⟨(eW R hK n M).measurable, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (eW R hK n M).measurable (MeasurableSet.univ_pi hs)]
  have hset : (eW R hK n M) ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ fun a => Set.pi Set.univ fun i =>
        (eK R hK) ⁻¹' Set.pi Set.univ fun k => s (a, i, k) := by
    ext X
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    exact ⟨fun h a i k => h (a, i, k), fun h p => h p.1 p.2.1 p.2.2⟩
  have hK1 : ∀ t : Fin d → Set R, (∀ k, MeasurableSet (t k)) →
      coordK R b lam ((eK R hK) ⁻¹' Set.pi Set.univ t) = ∏ k, lam (t k) := by
    intro t ht
    rw [coordK_eq R hK lam, Measure.map_apply (eK R hK).symm.measurable
      ((eK R hK).measurable (MeasurableSet.univ_pi ht))]
    have : (eK R hK).symm ⁻¹' ((eK R hK) ⁻¹' Set.pi Set.univ t) = Set.pi Set.univ t := by
      ext x
      simp
    rw [this, Measure.pi_pi]
  rw [hset, coordW, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  simp_rw [hK1 _ (fun k => hs _)]
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Fintype.prod_prod_type]

end Gen

theorem coordW_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (lf : Measure (Af F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (n M : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, MeasurableSet (A v)) → coordW (Af F) b lf n M {X | (∀ v ∈ S, projV v X ∈ A v) ∧ ∀ v, v ∉ S → projV v X ∈ latV b v} = ∏ v ∈ S, coordW (Fv F v) b (lam v) n M (A v) := by
  intro F E _ _ _ _ _ σ hσ d b lam hlam lf hlf h1 n M S A hA
  obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have hloc := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : ∀ v, IsTopologicalRing (Fv F v) := fun v => (hloc v).1
  haveI : ∀ v, LocallyCompactSpace (Fv F v) := fun v => (hloc v).2.1
  haveI : ∀ v, SecondCountableTopology (Fv F v) := fun v => (hloc v).2.2.1
  haveI : ∀ v, T2Space (Fv F v) := fun v => (hloc v).2.2.2.1
  haveI : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  have hKf : IsHomeomorph (cK (F := F) (E := E) (Af F) b) :=
    (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Af F)).2.2.2.2.2.2.1 d b
  have hKv : ∀ v, IsHomeomorph (cK (F := F) (E := E) (Fv F v) b) := fun v =>
    (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)).2.2.2.2.2.2.1 d b
  have mf := map_coordW (Af F) hKf lf n M
  have mv := fun v => map_coordW (Fv F v) (hKv v) (lam v) n M
  let A' : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n × Fin M × Fin d → Fv F v) := fun v =>
    (eW (Fv F v) (hKv v) n M).symm ⁻¹' A v
  have hA' : ∀ v, MeasurableSet (A' v) := fun v => (eW (Fv F v) (hKv v) n M).symm.measurable (hA v)
  have hcomm : ∀ (v : HeightOneSpectrum (𝓞 F)) (X : Fin n → Fin M → Af F ⊗[F] E)
      (p : Fin n × Fin M × Fin d),
      evalV F v (eW (Af F) hKf n M X p) = eW (Fv F v) (hKv v) n M (projV v X) p := by
    intro v X p
    rw [eW_apply, eW_apply, projV, cK_map]
  have hset : {X : Fin n → Fin M → Af F ⊗[F] E | (∀ v ∈ S, projV v X ∈ A v) ∧
      ∀ v, v ∉ S → projV v X ∈ latV b v} =
      (eW (Af F) hKf n M) ⁻¹' {x | (∀ v ∈ S, (fun i => evalV F v (x i)) ∈ A' v) ∧
        ∀ v, v ∉ S → ∀ i, evalV F v (x i) ∈ v.adicCompletionIntegers F} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hcomm]
    refine and_congr (forall₂_congr fun v _ => ?_) (forall₂_congr fun v _ => ?_)
    · simp [A']
    · exact ⟨fun h p => h p.1 p.2.1 p.2.2, fun h a i k => h (a, i, k)⟩
  rw [hset, mf.measure_preimage_equiv,
    GlobalTheory.CompanionTheory.SW.AfBox.pi_box F lam hlam lf hlf h1 (Fin n × Fin M × Fin d) S A' hA']
  exact Finset.prod_congr rfl fun v _ => (mv v).symm.measure_preimage_equiv (A v)

end GlobalTheory.CompanionTheory.SW.WBox
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopology
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core.AfTop

variable (F : Type) [Field F] [NumberField F]

theorem isCompact_Oh : IsCompact (Oh F) :=
  (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).1

theorem isOpen_Oh : IsOpen (Oh F) := by
  haveI : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  exact RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Fact.out

theorem natCast_mul_mem_Oh (N : ℕ) {x : A F} (hx : x ∈ Oh F) : (N : A F) * x ∈ Oh F := by
  induction N with
  | zero =>
    intro v
    rw [Nat.cast_zero, zero_mul]
    exact zero_mem (v.adicCompletionIntegers F)
  | succ n ih =>
    intro v
    rw [Nat.cast_succ, add_mul, one_mul]
    exact add_mem (ih v) (hx v)

theorem algebraMap_mem_Oh_iff (b : F) : algebraMap F (A F) b ∈ Oh F ↔ ∃ r : 𝓞 F, (r : F) = b := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 b h
    exact ⟨y, hy.symm⟩
  · rintro ⟨r, rfl⟩ v
    exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v r

theorem exists_mul_Oh_subset (U : Set (A F)) (hU : U ∈ 𝓝 (0 : A F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Oh F, (N : A F) * x ∈ U := by
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F
  let V : ℕ+ → Set (A F) := fun N => {a | ∃ c ∈ Oh F, a = ((N : ℕ) : A F) * c}
  have hV : Directed (· ⊇ ·) V := by
    intro M N
    refine ⟨M * N, ?_, ?_⟩
    · rintro _ ⟨c, hc, rfl⟩
      exact ⟨_, natCast_mul_mem_Oh F N hc, by push_cast; ring⟩
    · rintro _ ⟨c, hc, rfl⟩
      exact ⟨_, natCast_mul_mem_Oh F M hc, by push_cast; ring⟩
  have hc : ∀ N, IsCompact (V N) := by
    intro N
    have : V N = (fun c => ((N : ℕ) : A F) * c) '' Oh F := by
      ext a
      simp only [V, Set.mem_setOf_eq, Set.mem_image, eq_comm]
    rw [this]
    exact (isCompact_Oh F).image (continuous_const.mul continuous_id)
  obtain ⟨N, hN⟩ := exists_subset_nhds_of_isCompact' hV hc (fun N => h2 N N.pos) (U := U) (by
    apply mem_nhdsSet_iff_forall.mpr
    intro x hx
    have : x = 0 := h3 x fun M hM => Set.mem_iInter.1 hx ⟨M, hM⟩
    rwa [this])
  exact ⟨N, N.pos, fun x hx => hN ⟨x, hx, rfl⟩⟩

theorem exists_mul_mem_Oh_of_isCompact (K : Set (A F)) (hK : IsCompact K) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ K, (N : A F) * x ∈ Oh F := by
  let V : ℕ+ → Set (A F) := fun N => {a | ((N : ℕ) : A F) * a ∈ Oh F}
  have hV : Directed (· ⊆ ·) V := by
    intro M N
    refine ⟨M * N, fun a ha => ?_, fun a ha => ?_⟩
    · have := natCast_mul_mem_Oh F N ha
      show (((M * N : ℕ+) : ℕ) : A F) * a ∈ Oh F
      convert this using 1
      push_cast; ring
    · have := natCast_mul_mem_Oh F M ha
      show (((M * N : ℕ+) : ℕ) : A F) * a ∈ Oh F
      convert this using 1
      push_cast; ring
  obtain ⟨N, hN⟩ := hK.elim_directed_cover V
    (fun N => (isOpen_Oh F).preimage (continuous_const.mul continuous_id)) (fun a _ => by
      obtain ⟨M, hM, h⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.2.1 a
      exact Set.mem_iUnion.2 ⟨⟨M, hM⟩, h⟩) hV
  exact ⟨N, N.pos, fun x hx => hN hx⟩

theorem isOpen_mul_Oh (N : ℕ) (hN : 0 < N) :
    IsOpen {x : A F | ∃ y ∈ Oh F, x = (N : A F) * y} := by
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have h1 : (N : A F) * algebraMap F (A F) (N : F)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap F (A F)), ← map_mul, mul_inv_cancel₀ hN', map_one]
  have : {x : A F | ∃ y ∈ Oh F, x = (N : A F) * y} =
      (fun x => algebraMap F (A F) (N : F)⁻¹ * x) ⁻¹' Oh F := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show _ * (_ * y) ∈ Oh F
      rwa [← mul_assoc, mul_comm _ (N : A F), h1, one_mul]
    · intro hx
      exact ⟨_, hx, by rw [← mul_assoc, h1, one_mul]⟩
  rw [this]
  exact (isOpen_Oh F).preimage (continuous_const.mul continuous_id)

theorem denseRange_algebraMap : DenseRange (algebraMap F (A F)) := by
  intro y
  rw [mem_closure_iff_nhds]
  intro U hU
  have hc : Continuous fun z : A F => y - z := continuous_const.sub continuous_id
  have hU' : (fun z : A F => y - z) ⁻¹' U ∈ 𝓝 (0 : A F) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨N, hN, h⟩ := exists_mul_Oh_subset F _ hU'
  obtain ⟨x, a, ha, hy⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F N hN).1 y
  refine ⟨algebraMap F (A F) x, ?_, x, rfl⟩
  have h2 : y - (N : A F) * a ∈ U := h a ha
  have h3 : y - (N : A F) * a = algebraMap F (A F) x := by
    rw [sub_eq_iff_eq_add, ← nsmul_eq_mul]
    exact hy
  rwa [h3] at h2

theorem finiteAdele_topology : ∀ (F : Type) [Field F] [NumberField F], LocallyCompactSpace (A F) ∧ SecondCountableTopology (A F) ∧ T2Space (A F) ∧ IsCompact (Oh F) ∧ IsOpen (Oh F) ∧ DenseRange (algebraMap F (A F)) ∧ (∀ b : F, algebraMap F (A F) b ∈ Oh F ↔ ∃ r : 𝓞 F, (r : F) = b) ∧ (∀ U ∈ 𝓝 (0 : A F), ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Oh F, (N : A F) * x ∈ U) ∧ (∀ K : Set (A F), IsCompact K → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ K, (N : A F) * x ∈ Oh F) ∧ ∀ N : ℕ, 0 < N → IsOpen {x : A F | ∃ y ∈ Oh F, x = (N : A F) * y} :=
  fun F _ _ => ⟨GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F,
    GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F, GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F,
    isCompact_Oh F, isOpen_Oh F, denseRange_algebraMap F, algebraMap_mem_Oh_iff F,
    exists_mul_Oh_subset F, exists_mul_mem_Oh_of_isCompact F, isOpen_mul_Oh F⟩

end GlobalTheory.CompanionTheory.SW.Core.AfTop
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarScalingUnderFlow
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Flow

theorem map_eq_of_conj {G H : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [MeasurableSpace H] [BorelSpace H] (e : G ≃+ H) (he : Continuous e) (hs : Continuous e.symm)
    (L : G → G) (L' : H → H) (hL' : Continuous L') (hc : ∀ X, e (L X) = L' (e X)) (c : ℝ≥0∞)
    (hH : ∀ ν : Measure H, ν.IsAddHaarMeasure → ν.map L' = c • ν)
    (μ : Measure G) [μ.IsAddHaarMeasure] : μ.map L = c • μ := by
  have hL : Continuous L := by
    have : L = fun X => e.symm (L' (e X)) := by
      funext X; rw [← hc, AddEquiv.symm_apply_apply]
    rw [this]
    exact hs.comp (hL'.comp he)
  have hν := hH (μ.map e) (e.isAddHaarMeasure_map μ he hs)
  have h1 : (μ.map L).map e = (c • μ).map e := by
    rw [Measure.map_map he.measurable hL.measurable, Measure.map_smul c he.measurable.aemeasurable, ← hν,
      Measure.map_map hL'.measurable he.measurable]
    congr 1
    funext X
    exact hc X
  have h2 : ((μ.map L).map e).map e.symm = ((c • μ).map e).map e.symm := by rw [h1]
  rw [Measure.map_map hs.measurable he.measurable, Measure.map_map hs.measurable he.measurable] at h2
  have hid : (e.symm ∘ e : G → G) = id := by funext X; simp
  rwa [hid, Measure.map_id, Measure.map_id] at h2

section Coord

variable {F E A : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A]

def coordEquiv {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ) :
    (Fin n → Fin M → A ⊗[F] E) ≃+ (Fin n × Fin M × Fin d → A) where
  toFun X p := (Algebra.TensorProduct.basis A b).repr (X p.1 p.2.1) p.2.2
  invFun Y a i := (Algebra.TensorProduct.basis A b).equivFun.symm (fun k => Y (a, i, k))
  left_inv X := by
    funext a i
    have := (Algebra.TensorProduct.basis A b).equivFun.symm_apply_apply (X a i)
    simpa using this
  right_inv Y := by
    funext ⟨a, i, k⟩
    have := (Algebra.TensorProduct.basis A b).equivFun.apply_symm_apply (fun k => Y (a, i, k))
    exact congrFun this k
  map_add' X Y := by
    funext p
    simp

theorem coordEquiv_smul {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ) (a : A)
    (X : Fin n → Fin M → A ⊗[F] E) :
    coordEquiv b n M ((a ⊗ₜ[F] (1 : E)) • X) = fun p => a * coordEquiv b n M X p := by
  funext p
  have h : (a ⊗ₜ[F] (1 : E)) * X p.1 p.2.1 = a • X p.1 p.2.1 := by
    rw [Algebra.smul_def]; rfl
  simp [coordEquiv, h]

end Coord

theorem modulus_flow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (n M : ℕ) (μ : Measure (Fin n → Fin M → AF F ⊗[F] E)), μ.IsAddHaarMeasure → ∀ x : ℝ, μ.map (fun X => ((τ (Multiplicative.ofAdd (x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • X) = ENNReal.ofReal (Real.exp (-(2 * Module.finrank ℚ F * n * M * x))) • μ := by
  intro F E _ _ _ _ _ σ hcm τ hτ n M μ hμ x
  obtain ⟨⟨hAlc, hAsc, hAt2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := hAlc
  haveI := hAsc
  haveI := hAt2
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  obtain ⟨hTR, -, -, -, -, -, hHom, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (AF F)
  haveI := hTR
  haveI := hBor n M
  have hd : Module.finrank F E = 2 := hcm.2.2.1
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hd
  obtain ⟨-, θ, hθ, hτx⟩ := hτ
  have hh := hHom 2 b
  let hm := hh.homeomorph
  have he : Continuous (coordEquiv (A := AF F) b n M) := by
    refine continuous_pi fun p => ?_
    have h1 : Continuous fun X : Fin n → Fin M → AF F ⊗[F] E => X p.1 p.2.1 :=
      (continuous_apply p.2.1).comp (continuous_apply p.1)
    exact (continuous_apply p.2.2).comp (hh.continuous.comp h1)
  have hs : Continuous (coordEquiv (A := AF F) b n M).symm := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    have h1 : Continuous fun Y : Fin n × Fin M × Fin 2 → AF F => fun k => Y (a, i, k) :=
      continuous_pi fun k => continuous_apply _
    have h2 : (fun Y : Fin n × Fin M × Fin 2 → AF F => (coordEquiv (A := AF F) b n M).symm Y a i) =
        fun Y => hm.symm (fun k => Y (a, i, k)) := by
      funext Y
      apply hm.injective
      rw [Homeomorph.apply_symm_apply]
      funext k
      have := (Algebra.TensorProduct.basis (AF F) b).equivFun.apply_symm_apply (fun k => Y (a, i, k))
      exact congrFun this k
    rw [h2]
    exact hm.symm.continuous.comp h1
  have ht : 0 < Real.exp x := Real.exp_pos x
  refine map_eq_of_conj (coordEquiv (A := AF F) b n M) he hs _
    (fun y p => (show AF F from (θ (Real.exp x), 1)) * y p) ?_ ?_ _ ?_ μ
  · exact continuous_pi fun p => continuous_const.mul (continuous_apply p)
  · intro X
    rw [hτx x]
    exact coordEquiv_smul b n M _ X
  · intro ν hν
    have := GlobalTheory.CompanionTheory.AdelicFlow.map_scalar F hcm.1 θ hθ (Fin n × Fin M × Fin 2) ν (Real.exp x) ht
    rw [this]
    congr 2
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    simp only [Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring

end GlobalTheory.CompanionTheory.SW.Flow
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberMeasuresAgreeAlmostAll
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem lattice_mass_fibre_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (J' : Matrix (Fin M) (Fin M) E), IsHermND σ J' → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ n : ℕ, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam, IsStdV v lam → ∀ m m', IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m → IsGramFib (Fv F v) σ J' n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m' → ∀ S, m S (latV b v) = m' S (latV b v) := by
  intro F E _ _ _ _ _ σ hσ M J hJ J' hJ' d b n
  filter_upwards [_root_.GlobalTheory.CompanionTheory.SW.GoodIso.good_iso F E σ hσ M J hJ J' hJ' d b] with v hv
  intro lam hlam m m' hm hm' S
  obtain ⟨g, hg, hlat⟩ := hv
  have hL := _root_.GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  obtain ⟨h1, h2, h3, h4, -⟩ := id hL
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 n M
  haveI := hlam.1
  obtain ⟨-, c2, c3⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lam hlam.1
  haveI := c2 n M
  obtain ⟨a1, a2, a3, -⟩ := GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hσ d b n M v
  have hcont : ∀ k : GL (Fin M) (Fv F v ⊗[F] E),
      Continuous (actTup (Fv F v) (n := n) k) := by
    intro k
    refine continuous_pi fun a => ?_
    exact Continuous.matrix_mulVec continuous_const ((continuous_apply a))
  have hinv : ∀ (k l : GL (Fin M) (Fv F v ⊗[F] E)), k * l = 1 → ∀ X : Fin n → Fin M → Fv F v ⊗[F] E,
      actTup (Fv F v) k (actTup (Fv F v) l X) = X := by
    intro k l hkl X
    funext a
    have h : (k : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) * (l : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) = 1 := by
      rw [← Units.val_mul, hkl, Units.val_one]
    simp only [actTup, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  let e : (Fin n → Fin M → Fv F v ⊗[F] E) ≃+ (Fin n → Fin M → Fv F v ⊗[F] E) :=
    { toFun := actTup (Fv F v) g
      invFun := actTup (Fv F v) g⁻¹
      left_inv := hinv g⁻¹ g (inv_mul_cancel g)
      right_inv := hinv g g⁻¹ (mul_inv_cancel g)
      map_add' := by
        intro X Y
        funext a
        simp only [actTup, Pi.add_apply, Matrix.mulVec_add] }
  have hmap : (coordW (Fv F v) b lam n M).map e = coordW (Fv F v) b lam n M :=
    (GlobalTheory.T.map_addHaar_addEquiv_eq_smul_and_eq_of_compact_open _ _ (coordW (Fv F v) b lam n M) (coordW (Fv F v) b lam n M) e (hcont g)
      (hcont g⁻¹)).2 (latV b v) (latV b v) a1 a2 ⟨0, a3⟩ (hlat n) rfl
  have hfib := _root_.GlobalTheory.CompanionTheory.SW.LocIsom.fibre_map_isometry F E σ hσ M J hJ J' hJ' (Fv F v) hL n (coordW (Fv F v) b lam n M)
    (coordHerm (Fv F v) σ b lam n) m (c2 n M) (c3 n) hm (coordW (Fv F v) b lam n M) m' (c2 n M) hm' g hg 1
    (by rw [one_smul]; exact hmap) S
  have hval := congrArg (fun μ => μ (latV b v)) hfib
  simp only [one_smul] at hval
  rw [Measure.map_apply (hcont g).measurable a2.measurableSet] at hval
  have hpre : actTup (Fv F v) (n := n) g ⁻¹' latV (M := M) (n := n) b v = latV b v := by
    ext X
    exact hlat n X
  rw [hpre] at hval
  exact hval.symm

end GlobalTheory.CompanionTheory.SW
end

