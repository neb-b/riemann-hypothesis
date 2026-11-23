module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0549
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1743
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0253
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0687
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0695
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0693
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0017
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableSetBox
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SigL

section Abstract

variable {M X : Type} [MeasurableSpace M] [MeasurableSpace X]

theorem abs_integral (f : M → X) (hf : Measurable f) {B : Set M} (hB : MeasurableSet B) (P : Measure M)
    (u : X → ℂ) (hu : AEStronglyMeasurable u ((P.restrict B).map f)) (Ξ : M → ℂ)
    (h1 : ∀ z ∈ B, Ξ z = u (f z)) (h2 : ∀ z, z ∉ B → Ξ z = 0) :
    (Integrable Ξ P → Integrable u ((P.restrict B).map f)) ∧ ∫ z, Ξ z ∂P = ∫ z, u z ∂((P.restrict B).map f) := by
  refine ⟨fun hi => ?_, ?_⟩
  · rw [integrable_map_measure hu hf.aemeasurable]
    refine (hi.integrableOn (s := B)).congr ?_
    filter_upwards [ae_restrict_mem hB] with z hz
    exact h1 z hz
  · rw [integral_map hf.aemeasurable hu, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B) h2]
    exact setIntegral_congr_fun hB h1

theorem abs_map (f : M → X) (hf : Measurable f) {B : Set M} (hB : MeasurableSet B) (P : Measure M)
    (T : M → M) (hT : Measurable T) (k : ℝ≥0) (Θ : X → X) (hΘ : Measurable Θ) (hBT : T ⁻¹' B = B)
    (hc : ∀ z, Θ (f z) = f (T z)) (hP : P.map T = k • P) :
    ((P.restrict B).map f).map Θ = k • (P.restrict B).map f := by
  rw [Measure.map_map hΘ hf]
  have e1 : Θ ∘ f = f ∘ T := funext hc
  rw [e1, ← Measure.map_map hf hT]
  have h1 : (P.restrict B).map T = k • P.restrict B := by
    have e2 := Measure.restrict_map (μ := P) hT hB
    rw [hBT, hP] at e2
    rw [← e2, Measure.restrict_smul]
  rw [h1, Measure.map_smul k hf.aemeasurable]

open Pointwise in
theorem abs_finite [AddCommGroup M] [TopologicalSpace M] [ContinuousAdd M] [TopologicalSpace X] [T2Space X]
    [OpensMeasurableSpace X] [OpensMeasurableSpace M] [T2Space M]
    (f : M → X) (hf : Measurable f) (ι : X → M) (hι : Continuous ι) {B : Set M} (hB : MeasurableSet B) (P : Measure M)
    [IsFiniteMeasureOnCompacts P] (T : Set M) (hT : IsCompact T) (h : ∀ z ∈ B, z - ι (f z) ∈ T) :
    IsFiniteMeasureOnCompacts ((P.restrict B).map f) := by
  refine ⟨fun C hC => ?_⟩
  have hCm : MeasurableSet C := hC.measurableSet
  have hK : IsCompact ((ι '' C) + T) := (hC.image hι).add hT
  rw [Measure.map_apply hf hCm, Measure.restrict_apply (hf hCm)]
  refine lt_of_le_of_lt (measure_mono ?_) hK.measure_lt_top
  rintro z ⟨hz, hzB⟩
  exact Set.mem_add.2 ⟨ι (f z), ⟨_, hz, rfl⟩, z - ι (f z), h z hzB, by abel⟩

theorem rh_one {A R : Type} [Ring A] [Ring R] (f : A →+* R) {e : A} (he : f e = 1) (y : A) : f ((1 - e) * y) = 0 := by
  rw [map_mul, map_sub, map_one, he, sub_self, zero_mul]

theorem rh_zero {A R : Type} [Ring A] [Ring R] (f : A →+* R) {e : A} (he : f e = 0) (y : A) : f ((1 - e) * y) = f y := by
  rw [map_mul, map_sub, map_one, he, sub_zero, one_mul]

theorem rh_map_zero {A R : Type} [Ring A] [Ring R] (f : A →+* R) : f 0 = 0 := map_zero f

end Abstract

end GlobalTheory.CompanionTheory.SigL

namespace GlobalTheory.CompanionTheory.SigL

variable {D : D7} {a b c r t : ℕ}

theorem topRing (D : D7) : IsTopologicalRing (AE D) :=
  isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)

def offS (S : Finset (Pl D)) : AddSubgroup (AE D) where
  carrier := {z | ∀ v ∉ S, cv D v z ∈ intLoc D.host.F D.host.E v}
  add_mem' := fun hx hy v hv => by rw [RingHom.map_add (f := _)]; exact add_mem (hx v hv) (hy v hv)
  zero_mem' := fun v _ => by rw [RingHom.map_zero]; exact zero_mem _
  neg_mem' := fun hx v hv => by rw [RingHom.map_neg]; exact neg_mem (hx v hv)

theorem isOpen_offS (S : Finset (Pl D)) : IsOpen (offS S : Set (AE D)) := by
  haveI := topRing D
  have h0 : IsOpen {z : AE D | ∀ v : Pl D, cv D v z ∈ intLoc D.host.F D.host.E v} :=
    GlobalTheory.ThK.ConeEuler.UnitsOpen.isOpen_integral_everywhere
  refine AddSubgroup.isOpen_of_mem_nhds _ (g := 0) (Filter.mem_of_superset (h0.mem_nhds ?_) ?_)
  · intro v
    rw [rh_map_zero]
    exact zero_mem _
  · intro z hz v _
    exact hz v

theorem isOpen_intOff (S : Finset (Pl D)) : IsOpen {x : Mx D a b | IntOff S x} := by
  have h : {x : Mx D a b | IntOff S x} = ⋂ i, ⋂ j, (fun x : Mx D a b => x i j) ⁻¹' (offS S : Set (AE D)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    exact ⟨fun h i j v hv => h v hv i j, fun h v hv i j => h i j v hv⟩
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_offS S).preimage (continuous_id.matrix_elem i j)

theorem measurableSet_box (S : Finset (Pl D)) :
    MeasurableSet {z : Mx D a r × Mx D a t | IntOff S z.1 ∧ IntOff S z.2} := by
  obtain ⟨g1, g2⟩ := top_pair (D := D) a r t
  have o : OpensMeasurableSpace (Mx D a r × Mx D a t) := g1.opensMeasurable
  exact (((isOpen_intOff S).preimage continuous_fst).inter ((isOpen_intOff S).preimage continuous_snd)).measurableSet


open Classical in
theorem exists_box (S : Finset (Pl D)) {e : AE D} (hS : IsIdem S e) (a b : ℕ) :
    ∃ T : Set (Mx D a b), IsCompact T ∧ ∀ x, IntOff S x → (1 - e) • x ∈ T := by
  have hL : ∀ v : Pl D, IsCompact (if v ∈ S then ({0} : Set (Fv D.host.F v ⊗[D.host.F] D.host.E))
      else (intLoc D.host.F D.host.E v : Set (Fv D.host.F v ⊗[D.host.F] D.host.E))) := fun v => by
    by_cases h : v ∈ S
    · rw [if_pos h]; exact isCompact_singleton
    · rw [if_neg h]; exact (GlobalTheory.ThK.isCompact_isOpen_intLoc v).1
  have hfin : ∀ᶠ v : Pl D in Filter.cofinite, (if v ∈ S then ({0} : Set (Fv D.host.F v ⊗[D.host.F] D.host.E))
      else (intLoc D.host.F D.host.E v : Set (Fv D.host.F v ⊗[D.host.F] D.host.E))) ⊆
        (intLoc D.host.F D.host.E v : Set (Fv D.host.F v ⊗[D.host.F] D.host.E)) := by
    refine Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)
    by_contra h
    apply hv
    have h' : v ∉ S := h
    rw [if_neg h']
  obtain ⟨K, hK, hz⟩ := GlobalTheory.IdeleCyl.exists_isCompact_box D.host.F D.host.E (fun _ => {0}) _
    (fun _ => isCompact_singleton) hL hfin
  refine ⟨{x | ∀ i j, x i j ∈ K}, ?_, fun x hx i j => ?_⟩
  · have e1 : {x : Mx D a b | ∀ i j, x i j ∈ K} = Set.univ.pi fun _ => Set.univ.pi fun _ => K := by
      ext x
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    rw [e1]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK
  · refine hz _ (fun w => ?_) (fun v => ?_)
    · change compInf D.host.F D.host.E w ((1 - e) * x i j) ∈ ({0} : Set _)
      rw [rh_one _ (hS.1 w)]
      exact rfl
    · change cv D v ((1 - e) * x i j) ∈ _
      have hv := hS.2 v
      by_cases h : v ∈ S
      · rw [if_pos h] at hv
        rw [rh_one _ hv, if_pos h]
        exact rfl
      · rw [if_neg h] at hv
        rw [rh_zero _ hv, if_neg h]
        exact hx v h i j

theorem measurable_toX {e : AE D} (he : e * e = e) : Measurable (toX (a := a) (r := r) (t := t) he) := by
  haveI := topRing D
  obtain ⟨g1, g2⟩ := top_pair (D := D) a r t
  have o : OpensMeasurableSpace (Mx D a r × Mx D a t) := g1.opensMeasurable
  exact Measurable.subtype_mk
    ((continuous_fst.const_smul e).prodMk (continuous_snd.const_smul e)).measurable

end GlobalTheory.CompanionTheory.SigL
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneThetaIntegralRayFormula
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitBd

def cnt {F : Type} [Field F] [NumberField F] (θ : ℝ →+* Ainf F) (ι : Type) (K : Set (ι → Ainf F)) (ε : ℝ) : ℝ≥0∞ :=
  ∑' _y : {y : ι → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧
    (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ K}, (1 : ℝ≥0∞)

theorem count : PositivityTheory.Rg.Mass.Equi → ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ →
    ∀ (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) →
    ∀ (ι : Type) [Fintype ι] (K : Set (ι → Ainf F)), IsCompact K → ∃ B : ℝ≥0, ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ENNReal.ofReal (ε ^ (Module.finrank ℚ F * Fintype.card ι)) * cnt θ ι K ε ≤ B := by
  intro hEq F _ _ hF θ hθ li lam hli hlam ι _ K hK
  obtain ⟨_, _, _, _, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hF
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI := hli.1
  obtain ⟨f, hf1, -, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact
    (hK.union (isCompact_singleton (x := (0 : ι → Ainf F)))) isClosed_empty (Set.disjoint_empty _)
  have hL := hEq F hF θ hθ li lam hli hlam ι ∅ (f : (ι → Ainf F) → ℝ) (fun _ _ => 0) f.continuous hfc (by simp)
  simp only [Finset.prod_empty, mul_one] at hL
  set L := ∫ y, f y ∂(Measure.pi fun _ : ι => li) with hLdef
  have hLpos : 0 < L := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero f.continuous hfc (fun x => (hf01 x).1)
      (x := 0) ?_
    rw [hf1 (Or.inr rfl)]
    exact one_ne_zero
  refine ⟨Real.toNNReal (L + 1), ?_⟩
  filter_upwards [hL.eventually (lt_mem_nhds (half_lt_self hLpos)), hL.eventually (gt_mem_nhds (lt_add_one L)),
    self_mem_nhdsWithin] with ε h1 h2 h3
  set u : {x : ι → F // ∀ v, v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 F))) → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} → ℝ :=
    fun x => f fun i => θ ε * algebraMap F (Ainf F) (x.1 i) with hu
  have hu0 : ∀ x, 0 ≤ u x := fun x => (hf01 _).1
  have hsum : Summable u := by
    by_contra hns
    have e0 : ∑' x, u x = 0 := tsum_eq_zero_of_not_summable hns
    simp only [hu] at e0
    rw [e0, mul_zero] at h1
    linarith
  have hle : cnt θ ι K ε ≤ ∑' x, ENNReal.ofReal (u x) := by
    have hinj : Function.Injective fun y : {y : ι → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧
      (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ K} =>
        (⟨y.1, fun v _ i => y.2.1 v i⟩ : {x : ι → F // ∀ v, v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 F))) → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F}) :=
      fun y y' e => Subtype.ext (Subtype.mk.inj e)
    refine le_trans (le_of_eq (tsum_congr fun y => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hinj fun x => ENNReal.ofReal (u x))
    simp only [hu]
    rw [hf1 (Or.inl y.2.2)]
    simp
  rw [← ENNReal.ofReal_tsum_of_nonneg hu0 hsum] at hle
  have hpos : 0 ≤ ε ^ (Module.finrank ℚ F * Fintype.card ι) := pow_nonneg (le_of_lt h3) _
  calc _ ≤ ENNReal.ofReal (ε ^ (Module.finrank ℚ F * Fintype.card ι)) * ENNReal.ofReal (∑' x, u x) := mul_le_mul' le_rfl hle
    _ = ENNReal.ofReal (ε ^ (Module.finrank ℚ F * Fintype.card ι) * ∑' x, u x) := (ENNReal.ofReal_mul hpos).symm
    _ ≤ ENNReal.ofReal (L + 1) := ENNReal.ofReal_le_ofReal (le_of_lt h2)
    _ = _ := rfl

def box (F : Type) [Field F] [NumberField F] (ι : Type) (ρ : ℝ) : Set (ι → Ainf F) :=
  {x | ∀ i w, ‖x i w‖ ≤ ρ}

theorem cnt_anti {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F) (θ : ℝ →+* Ainf F) (hθ : Continuous θ)
    (r : ℝ → (AF F)ˣ) (hr : IsRay θ r) (ι : Type) (ρ : ℝ) {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ ≤ ε) :
    cnt θ ι (box F ι ρ) ε ≤ cnt θ ι (box F ι ρ) δ := by
  have hn := (_root_.GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.MdRay.norm_md_ray F hF θ hθ r hr).1
  have hm : ∀ y : ι → F, (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ box F ι ρ →
      (fun i => θ δ * algebraMap F (Ainf F) (y i)) ∈ box F ι ρ := fun y h i w => by
    have e : ∀ t : ℝ, ‖(θ t * algebraMap F (Ainf F) (y i)) w‖ = |t| * ‖algebraMap F (Ainf F) (y i) w‖ := fun t => by
      change ‖θ t w * algebraMap F (Ainf F) (y i) w‖ = _
      rw [norm_mul, hn]
    have h1 : ‖(θ ε * algebraMap F (Ainf F) (y i)) w‖ ≤ ρ := h i w
    change ‖(θ δ * algebraMap F (Ainf F) (y i)) w‖ ≤ ρ
    rw [e] at h1 ⊢
    rw [abs_of_pos hδ]
    rw [abs_of_pos (hδ.trans_le hδε)] at h1
    exact (mul_le_mul_of_nonneg_right hδε (norm_nonneg _)).trans h1
  have hinj : Function.Injective fun y : {y : ι → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧
      (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ box F ι ρ} =>
      (⟨y.1, y.2.1, hm y.1 y.2.2⟩ : {y : ι → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧
      (fun i => θ δ * algebraMap F (Ainf F) (y i)) ∈ box F ι ρ}) :=
    fun y y' e => Subtype.ext (Subtype.mk.inj e)
  exact ENNReal.tsum_comp_le_tsum_of_injective hinj fun _ => (1 : ℝ≥0∞)

theorem isCompact_box {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F) (ι : Type) (ρ : ℝ) :
    IsCompact (box F ι ρ) := by
  obtain ⟨_, _, _, _, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hF
  have e : box F ι ρ = Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall 0 ρ := by
    ext x
    exact ⟨fun h i _ w _ => mem_closedBall_zero_iff.2 (h i w),
      fun h i w => mem_closedBall_zero_iff.1 (h i (Set.mem_univ _) w (Set.mem_univ _))⟩
  rw [e]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun w => isCompact_closedBall _ _

theorem Th_le {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (b : Module.Basis (Fin 2) F E)
    (θ : ℝ →+* Ainf F) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) (B0 : ℝ) (hB0 : ∀ x, ‖φ x‖ ≤ B0)
    (N : ℕ) (hN : 0 < N) (ρ ε : ℝ) (y : (AF F ⊗[F] E)ˣ)
    (hbox : ∀ X : Fin 1 → Fin 1 → E, Psi φ A (fun a i => (y : AF F ⊗[F] E) * inclR (AF F) (X a i)) ≠ 0 →
      (∀ (p : Fin 1 × Fin 1 × Fin 2) (v : HeightOneSpectrum (𝓞 F)),
        algebraMap F (Fv F v) ((N : F) * b.repr (X p.1 p.2.1) p.2.2) ∈ v.adicCompletionIntegers F) ∧
      ∀ (p : Fin 1 × Fin 1 × Fin 2) (w : InfinitePlace F),
        ‖(θ ε * algebraMap F (Ainf F) ((N : F) * b.repr (X p.1 p.2.1) p.2.2)) w‖ ≤ ρ) :
    Th φ A y ≤ Real.toNNReal B0 * cnt θ (Fin 1 × Fin 1 × Fin 2) (box F _ ρ) ε := by
  have hN0 : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  set Y := fun X : Fin 1 → Fin 1 → E => fun p : Fin 1 × Fin 1 × Fin 2 => (N : F) * b.repr (X p.1 p.2.1) p.2.2 with hY
  have hYi : Function.Injective Y := fun X X' e => by
    funext a i
    refine b.repr.injective (Finsupp.ext fun k => ?_)
    have h1 := congrFun e (a, i, k)
    exact mul_left_cancel₀ hN0 h1
  set g : ({X : Fin 1 → Fin 1 → E | X ≠ 0} : Set _) → ℝ≥0∞ :=
    fun X => Psi φ A (fun a i => (y : AF F ⊗[F] E) * inclR (AF F) (X.1 a i)) with hg
  set T : Set ({X : Fin 1 → Fin 1 → E | X ≠ 0} : Set _) := {X | g X ≠ 0} with hTdef
  have hPsi : ∀ Z : Fin 1 → Fin 1 → AF F ⊗[F] E, Psi φ A Z ≤ Real.toNNReal B0 := fun Z => by
    unfold Psi
    refine (Set.indicator_le_self' (fun _ _ => bot_le) _).trans ?_
    rw [ENNReal.ofReal, ENNReal.coe_le_coe]
    exact Real.toNNReal_le_toNNReal ((le_abs_self _).trans (hB0 _))
  have e1 : Th φ A y = ∑' X : T, g X.1 := by
    rw [tsum_subtype T g]
    refine tsum_congr fun X => ?_
    by_cases hX : X ∈ T
    · rw [Set.indicator_of_mem hX]
    · rw [Set.indicator_of_notMem hX]
      exact not_not.1 hX
  rw [e1, cnt, ← ENNReal.tsum_mul_left]
  have hmap : ∀ X : T, (∀ v : HeightOneSpectrum (𝓞 F), ∀ i,
      algebraMap F (Fv F v) (Y X.1.1 i) ∈ v.adicCompletionIntegers F) ∧
        (fun i => θ ε * algebraMap F (Ainf F) (Y X.1.1 i)) ∈ box F _ ρ := fun X => by
    obtain ⟨h2, h3⟩ := hbox X.1.1 X.2
    exact ⟨fun v i => h2 i v, fun i w => h3 i w⟩
  have hinj : Function.Injective fun X : T => (⟨Y X.1.1, hmap X⟩ : {y : Fin 1 × Fin 1 × Fin 2 → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i,
      algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧
        (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ box F _ ρ}) := fun X X' e =>
    Subtype.ext (Subtype.ext (hYi (congrArg Subtype.val e)))
  refine le_trans (ENNReal.tsum_le_tsum fun X => ?_) (ENNReal.tsum_comp_le_tsum_of_injective hinj
    fun _ => (Real.toNNReal B0 : ℝ≥0∞) * 1)
  rw [mul_one]
  exact hPsi _

theorem unit_bound : PositivityTheory.Rg.Mass.Equi → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ r, IsRay θ r → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∀ K : Set (AF F ⊗[F] E)ˣ, IsCompact K → ∀ ε₁ : ℝ, ∃ C : ℝ≥0, ∀ k ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ → ENNReal.ofReal (ε ^ (2 * Module.finrank ℚ F)) * Th φ A (k * ofF (r ε)) ≤ C := by
  intro hEq F E _ _ _ _ _ σ hcm J hJ d b li lam hli hlam θ hθ r hr S φ A hT K hK ε₁
  obtain ⟨N, ρ, hN, hbox⟩ := _root_.GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Box.unit_box F E σ hcm J hJ d b θ r hr S φ A hT K hK
  have hd : d = 2 := by
    have := Module.finrank_eq_card_basis b
    rw [hcm.2.2.1] at this
    simpa using this.symm
  subst hd
  obtain ⟨B, hB⟩ := count hEq F hcm.1 θ hθ li lam hli hlam (Fin 1 × Fin 1 × Fin 2) (box F _ ρ) (isCompact_box hcm.1 _ ρ)
  obtain ⟨B0, hB0⟩ := hT.2.1.exists_bound_of_continuous hT.1
  have e2 : Module.finrank ℚ F * Fintype.card (Fin 1 × Fin 1 × Fin 2) = 2 * Module.finrank ℚ F := by
    rw [show Fintype.card (Fin 1 × Fin 1 × Fin 2) = 2 from rfl, mul_comm]
  rw [e2] at hB
  set m := 2 * Module.finrank ℚ F with hm
  set c : ℝ → ℝ≥0∞ := cnt θ (Fin 1 × Fin 1 × Fin 2) (box F _ ρ) with hc
  obtain ⟨ε₀, hε₀, hI⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hB
  have hε₀' : (0 : ℝ) < ε₀ := hε₀
  set ε₂ := ε₀ / 2 with hε₂
  have h2pos : 0 < ε₂ := half_pos hε₀'
  have h2 : ENNReal.ofReal (ε₂ ^ m) * c ε₂ ≤ B := hI ⟨h2pos, half_lt_self hε₀'⟩
  set E2 : ℝ≥0 := Real.toNNReal (ε₂ ^ m) with hE2
  have hE2pos : E2 ≠ 0 := by
    simp only [hE2, ne_eq, Real.toNNReal_eq_zero, not_le]
    exact pow_pos h2pos _
  set D : ℝ≥0 := B + Real.toNNReal (ε₁ ^ m) * (E2⁻¹ * B) with hD
  refine ⟨Real.toNNReal B0 * D, fun k hk ε hε hε1 => ?_⟩
  have hTh := Th_le b θ φ A B0 hB0 N hN ρ ε (k * ofF (r ε)) fun X h => hbox k hk X ε hε h
  have hcD : ENNReal.ofReal (ε ^ m) * c ε ≤ D := by
    by_cases hlt : ε < ε₀
    · have h1 : ENNReal.ofReal (ε ^ m) * c ε ≤ B := hI ⟨hε, hlt⟩
      refine h1.trans ?_
      rw [ENNReal.coe_le_coe, hD]
      exact le_self_add
    · have hle : ε₂ ≤ ε := (half_le_self hε₀'.le).trans (not_lt.1 hlt)
      have h3 : c ε ≤ c ε₂ := cnt_anti hcm.1 θ hθ r hr _ ρ h2pos hle
      have h4 : c ε₂ ≤ ((E2⁻¹ * B : ℝ≥0) : ℝ≥0∞) := by
        have e : c ε₂ = (E2 : ℝ≥0∞)⁻¹ * ((E2 : ℝ≥0∞) * c ε₂) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.2 hE2pos) ENNReal.coe_ne_top, one_mul]
        rw [e, ENNReal.coe_mul, ENNReal.coe_inv hE2pos]
        exact mul_le_mul' le_rfl h2
      have h5 : ENNReal.ofReal (ε ^ m) ≤ (Real.toNNReal (ε₁ ^ m) : ℝ≥0∞) :=
        ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hε.le hε1 m)
      calc ENNReal.ofReal (ε ^ m) * c ε ≤ (Real.toNNReal (ε₁ ^ m) : ℝ≥0∞) * ((E2⁻¹ * B : ℝ≥0) : ℝ≥0∞) :=
            mul_le_mul' h5 (h3.trans h4)
        _ ≤ D := by
            rw [← ENNReal.coe_mul, ENNReal.coe_le_coe, hD]
            exact le_add_self
  calc ENNReal.ofReal (ε ^ m) * Th φ A (k * ofF (r ε))
      ≤ ENNReal.ofReal (ε ^ m) * ((Real.toNNReal B0 : ℝ≥0∞) * c ε) := mul_le_mul' le_rfl hTh
    _ = (Real.toNNReal B0 : ℝ≥0∞) * (ENNReal.ofReal (ε ^ m) * c ε) := by ring
    _ ≤ (Real.toNNReal B0 : ℝ≥0∞) * D := mul_le_mul' le_rfl hcD
    _ = ((Real.toNNReal B0 * D : ℝ≥0) : ℝ≥0∞) := by rw [ENNReal.coe_mul]

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitBd

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatVMapMulChi
section
open scoped Classical

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Rs.SatakeVectors PositivityTheory.Rg.Rs.SatakeVectors.SatakeVectorEventually PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.JoinSatPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem satV_of_comp {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {w : HeightOneSpectrum (𝓞 E)}
    {σ : SmIrr (GL (Fin N) (w.adicCompletion E))} (h : IsLocCompGL V w σ) {B : Multiset ℂˣ}
    (hs : HasSatGL w σ.ρ B) : SatV V w B := by
  have hmem : ∀ ψ ∈ V, ψ ∈ ⨆ f : MapsD V w σ, LinearMap.range f.1 := fun ψ hψ => by
    rw [iSup_range_eq hV w σ h]; exact hψ
  refine ⟨?_, fun ψ hψ hψK hψ0 =>
    GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup σ.irred hs (fun f : MapsD V w σ => f.1) (fun f => f.2.2)
      (hmem ψ hψ) (GlobalTheory.LGrp.mem_fixed.2 hψK) hψ0⟩
  obtain ⟨x, hx⟩ := hs.exists_vec
  obtain ⟨f, h0, hfV, hf⟩ := h
  haveI := σ.irred
  have hi : Function.Injective f := by
    rcases Representation.IsIrreducible.injective_or_eq_zero
      (f.intertwiningMap_of_isIntertwiningMap σ.ρ ((finRep E N).comp (locGL E N w)) hf) with hi | hz
    · exact hi
    · exact absurd (LinearMap.ext fun s => DFunLike.congr_fun hz s) h0
  exact ⟨f x, hfV x, hx.map f hf fun e => hx.1 (hi (by rw [e, map_zero]))⟩

theorem hasSat_of_satV {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {w : HeightOneSpectrum (𝓞 E)}
    {σ : SmIrr (GL (Fin N) (w.adicCompletion E))} (h : IsLocCompGL V w σ) {B : Multiset ℂˣ}
    (hs : SatV V w B) : HasSatGL w σ.ρ B := by
  obtain ⟨⟨φ, hφ, hφs⟩, -⟩ := hs
  have hfix : ∀ k ∈ KGL w (n := N), finRep E N (locGL E N w k) φ = φ := fun k hk =>
    GlobalTheory.LGrp.mem_fixed.1 hφs.2.1 k hk
  have hmem : φ ∈ ⨆ f : MapsD V w σ, LinearMap.range f.1 := by
    rw [iSup_range_eq hV w σ h]; exact hφ
  obtain ⟨v, hv0, hv⟩ := LocSph.exists_fixed_of_mem_iSup ((finRep E N).comp (locGL E N w)) σ.ρ σ.irred
    (fun f : MapsD V w σ => f.1) (fun f => f.2.2) (KGL w (n := N) : Set _) φ hφs.1 hfix hmem
  have hsph : GlobalTheory.LGrp.IsSpherical σ.ρ (KGL w (n := N)) :=
    (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 hv, hv0⟩
  obtain ⟨B', hB'⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred hsph
  have e : B' = B := ((satV_of_comp hV h hB').2 φ hφ hfix hφs.1).unique hφs
  exact e ▸ hB'

theorem satV_map_mulChi {m : ℕ} {V : Submodule ℂ (Sm E m)} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    {χ : HChar E} (hχ : χ.UnrAt w) (h : SatV V w B) :
    SatV (V.map (mulChi m χ).toLinearMap) w (B.map (· * χ.val w)) := by
  have L := satLike_map_mulChi hχ (satLike_of_satV h)
  refine ⟨?_, L⟩
  obtain ⟨⟨φ, hφ, hs⟩, -⟩ := h
  have hm : (mulChi m χ) φ ∈ V.map (mulChi m χ).toLinearMap := Submodule.mem_map_of_mem hφ
  refine ⟨_, hm, L _ hm (fun k hk => ?_) fun e => hs.1 ((mulChi m χ).injective (by rw [e, map_zero]))⟩
  rw [finRep_mulChi, hχ _ (GlobalTheory.SphGal.isUnitAt_det_of_mem hk), Units.val_one, one_smul]
  exact congrArg _ (GlobalTheory.LGrp.mem_fixed.1 hs.2.1 k hk)

def PartSat (w : HeightOneSpectrum (𝓞 E)) (x : Σ M : ℕ, Submodule ℂ (Sm E M)) (B : Multiset ℂˣ) : Prop :=
  SatV x.2 w B

variable {n a b : ℕ}

theorem pre_sat_iff (D : Pre E n) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) :
    D.Sat w B ↔ ∃ l : List (Multiset ℂˣ), List.Forall₂ (PartSat w) (parts D) l ∧ l.sum = B := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨List.ofFn c, ?_, List.sum_ofFn⟩
    refine List.forall₂_iff_get.2 ⟨by simp [parts], fun i h₁ h₂ => ?_⟩
    simp only [parts, List.get_eq_getElem, List.getElem_ofFn]
    exact satV_of_comp (D.discrete _) (D.loc _ w) (hc _).2
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨hlen, hg⟩ := List.forall₂_iff_get.1 hl
    have hlen' : D.c = l.length := by simpa [parts] using hlen
    have hS : ∀ i : Fin D.c, HasSatGL w (D.σ i w).ρ (l.get (i.cast hlen')) := fun i => by
      have := hg i.1 (by simp [parts]) (by simpa [hlen'] using i.2)
      simp only [parts, List.get_eq_getElem, List.getElem_ofFn] at this
      exact hasSat_of_satV (D.discrete i) (D.loc i w) this
    refine ⟨fun i => l.get (i.cast hlen'), fun i => ⟨(hS i).1, hS i⟩, ?_⟩
    have e : List.ofFn (fun i : Fin D.c => l.get (i.cast hlen')) = l :=
      List.ext_get (by simp [hlen']) fun i h₁ h₂ => by simp
    rw [← List.sum_ofFn, e]

theorem sum_map_map (f : ℂˣ → ℂˣ) (l : List (Multiset ℂˣ)) :
    (l.map (Multiset.map f)).sum = l.sum.map f := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

theorem forall₂_tw {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (hχ : χ.UnrAt w)
    {p : List (Σ M : ℕ, Submodule ℂ (Sm E M))} {l : List (Multiset ℂˣ)} (h : List.Forall₂ (PartSat w) p l) :
    List.Forall₂ (PartSat w) (p.map (twPart χ)) (l.map (Multiset.map (· * χ.val w))) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons h _ ih => exact List.Forall₂.cons (satV_map_mulChi hχ h) ih

theorem joinSat : PositivityTheory.Rg.BcB.F.RS.JoinSat := by
  intro E _ _ _ n a b χ₁ χ₂ Pa Pb D w Ba Bb hJ h1 h2 sa sb
  obtain ⟨la, fa, rfl⟩ := (pre_sat_iff Pa w Ba).1 sa
  obtain ⟨lb, fb, rfl⟩ := (pre_sat_iff Pb w Bb).1 sb
  refine (pre_sat_iff D w _).2 ⟨la.map (Multiset.map (· * χ₁.val w)) ++ lb.map (Multiset.map (· * χ₂.val w)), ?_, ?_⟩
  · rw [hJ]
    exact List.rel_append (forall₂_tw h1 fa) (forall₂_tw h2 fb)
  · rw [List.sum_append, sum_map_map, sum_map_map]

end GlobalTheory.CompanionTheory.JoinSatPf

end
end

