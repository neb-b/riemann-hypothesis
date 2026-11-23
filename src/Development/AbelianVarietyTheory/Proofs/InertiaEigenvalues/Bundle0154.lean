module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Formalism.GaloisCohomology.Statement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0083
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumInvEqZeroOfUnramifiedCocycle
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory

theorem exists_descend_pair_quotient {Γ M : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [TopologicalSpace M] (N : Subgroup Γ) (w : Γ × Γ → M)
    (hw : Continuous w) (h : ∀ g h : Γ, ∀ n ∈ N, ∀ n' ∈ N, w (g * n, h * n') = w (g, h)) :
    ∃ W : (Γ ⧸ N) × (Γ ⧸ N) → M, Continuous W ∧
      ∀ g h : Γ, W ((g : Γ ⧸ N), (h : Γ ⧸ N)) = w (g, h) := by
  refine ⟨fun p => Quotient.liftOn₂' p.1 p.2 (fun a b => w (a, b)) ?_, ?_, fun g h => rfl⟩
  · intro a b a' b' ha hb
    have e := h a b _ (QuotientGroup.leftRel_apply.1 ha) _ (QuotientGroup.leftRel_apply.1 hb)
    simpa using e.symm
  · rw [((QuotientGroup.isOpenQuotientMap_mk (N := N)).prodMap
      (QuotientGroup.isOpenQuotientMap_mk (N := N))).isQuotientMap.continuous_iff]
    exact hw

theorem sum_inv_eq_zero_of_unramified_cocycle : PoitouTateTotallyComplex → ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ζ : Ω), IsPrimitiveRoot ζ (l ^ 1) → ∃ inv : InvFam F Ω l 1, IsLocalInvariants ζ inv ∧ ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ContainsAbove S l → ∀ Av : HeightOneSpectrum (𝓞 F) → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v) → ∀ w : Z2 (muRep F Ω l 1), (∀ g h : G F Ω, ∀ n ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))), ∀ n' ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))), w.1 (g * n, h * n') = w.1 (g, h)) → ∀ wl : ∀ v, Z2 (muLoc F l 1 (Av v)), (∀ v (g h : Dec (F := F) (Av v)), (wl v).1 (g, h) = w.1 ((g : G F Ω), (h : G F Ω))) → ∑ v ∈ S, inv (Av v) (Submodule.Quotient.mk (wl v)) = 0 := by
  intro hPT F Ω _ _ _ _ _ _ l _ ζ hζ
  obtain ⟨inv, hinv, H⟩ := hPT.annihilators F Ω l 1 one_pos ζ hζ
  refine ⟨inv, hinv, fun S hS Av hA w hw wl hwl => ?_⟩
  obtain ⟨μ, hμ⟩ := exists_lift_cycMod (Ω := Ω) (r := 1) hS
  obtain ⟨W, hWc, hW⟩ := exists_descend_pair_quotient _ w.1 w.2.1 hw
  have hmem : W ∈ Z2 (charRep μ) := by
    refine ⟨hWc, fun g h k => ?_⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective h
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective k
    have e := w.2.2 g h k
    have e2 : μ (g : G F Ω ⧸ _) = cycMod F Ω l 1 g := DFunLike.congr_fun hμ g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hW, hW, hW, hW, charRep_apply, e2]
    exact e
  have e := (H S hS (fun v => Av v.1) (fun v => hA v.1) μ hμ).1
    (Submodule.Quotient.mk ⟨W, hmem⟩)
  rw [← Finset.sum_coe_sort]
  refine Eq.trans (Finset.sum_congr rfl fun v _ => ?_) e
  refine congrArg (inv (Av v.1)) ?_
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun p => ?_))
  exact (hwl v.1 p.1 p.2).trans (hW _ _).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TruncatedWhittakerIntegralEqVolumeMulIntegralPer
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.WhitCollapse

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem continuous_normF (A : Et F E) : Continuous (fun t : A.K => Algebra.norm F t) := by
  classical
  let b := Module.finBasis F A.K
  have h : (fun t : A.K => Algebra.norm F t) = fun t => (Algebra.leftMulMatrix b t).det := by
    funext t; exact Algebra.norm_eq_matrix_det b t
  rw [h]
  refine Continuous.matrix_det ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have : (fun t : A.K => Algebra.leftMulMatrix b t i j) =
      fun t => (b.coord i) (LinearMap.mulRight F (b j) t) := by
    funext t; simp [Algebra.leftMulMatrix_eq_repr_mul]
  rw [this]
  exact IsModuleTopology.continuous_of_linearMap ((b.coord i).comp (LinearMap.mulRight F (b j)))

theorem norm_eta (x : F) : ‖eta x‖ = 1 := by
  unfold eta; split_ifs <;> simp

theorem measurable_etaK [Unram F E] (A : Et F E) : Measurable A.etaK := by
  letI : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  obtain ⟨-, -, -, hlc⟩ := _root_.GlobalTheory.EtaChar.main F E
  have hc : ContinuousOn (eta : F → ℂ) {0}ᶜ := by
    rw [continuousOn_iff_continuous_restrict]
    exact hlc.continuous
  have hm : Measurable (eta : F → ℂ) := measurable_of_continuousOn_compl_singleton 0 hc
  exact hm.comp (continuous_normF A).measurable

theorem collapse : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (φ' : A.K × A.K → ℂ), IsTest φ' → ∀ (a : A.K) (c : F), c ≠ 0 → ∫ z in {z : A.K | c • z ∈ A.OK}, (∫ t, (∫ b, φ' (b, t) * A.psiK ψ (t * z * b) ∂μK) * A.etaK t ∂μK) * A.psiK ψ (-(a * z)) ∂μK = (((μK {z : A.K | c • z ∈ A.OK}).toReal : ℝ) : ℂ) * ∫ t, (∫ b, φ' (b, t) * Set.indicator {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} (fun _ => (1 : ℂ)) (t * b - a) ∂μK) * A.etaK t ∂μK := by
  intro F E _ _ _ _ U A ψ hψ μK hμ φ' hφ a c hc
  have := U.charZero; have := U.ultraF; have := U.lcF
  haveI := GlobalTheory.FourKFub.secondCountableK A
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.JR.EtMeas.top_facts F A.K
  obtain ⟨-, -, hnd, -, -, -, -, -, -, hOKo, hOKc, R, hR⟩ := _root_.GlobalTheory.JR.EtFacts.main F E A
  have hψc := GlobalTheory.FourKFub.psiK_continuous A ψ hψ
  have hηm := measurable_etaK A
  have hφc : Continuous φ' := hφ.1.continuous
  let M : AddSubgroup A.K := R.toAddSubgroup.comap (DistribSMul.toAddMonoidHom A.K c)
  have hMset : (M : Set A.K) = {z : A.K | c • z ∈ A.OK} := by
    ext z
    show c • z ∈ (R : Set A.K) ↔ c • z ∈ A.OK
    rw [hR]
  have hMo : IsOpen (M : Set A.K) := by rw [hMset]; exact hOKo.preimage (continuous_const_smul c)
  have hMc : IsCompact (M : Set A.K) := by
    rw [hMset]
    have : {z : A.K | c • z ∈ A.OK} = (fun z : A.K => c⁻¹ • z) '' A.OK := by
      ext z; constructor
      · intro h; exact ⟨c • z, h, by simp [smul_smul, inv_mul_cancel₀ hc]⟩
      · rintro ⟨w, hw, rfl⟩
        show c • c⁻¹ • w ∈ A.OK
        simpa [smul_smul, mul_inv_cancel₀ hc] using hw
    rw [this]; exact hOKc.image (continuous_const_smul _)
  have hMm : MeasurableSet (M : Set A.K) := hMo.measurableSet
  have hMcl : IsClosed (M : Set A.K) := hMc.isClosed
  set χ : A.K → ℂ := (M : Set A.K).indicator (fun _ => 1) with hχdef
  have hχc : Continuous χ := IsClopen.continuous_indicator ⟨hMcl, hMo⟩ continuous_const
  let K0 : A.K × (A.K × A.K) → ℂ := fun q =>
    χ q.1 * φ' (q.2.2, q.2.1) * A.psiK ψ (q.2.1 * q.1 * q.2.2) * A.psiK ψ (-(a * q.1))
  have hK0c : Continuous K0 := by fun_prop
  have hK0s : HasCompactSupport K0 := by
    refine HasCompactSupport.intro (hMc.prod (hφ.2.isCompact.image continuous_swap)) ?_
    rintro ⟨z, t, b⟩ hq
    simp only [Set.mem_prod, not_and_or] at hq
    rcases hq with hz | hp
    · simp [K0, χ, hz]
    · have : φ' (b, t) = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp ⟨(b, t), h, rfl⟩)
      simp [K0, this]
  have hK0i : Integrable K0 (μK.prod (μK.prod μK)) := hK0c.integrable_of_hasCompactSupport hK0s
  let H : A.K × (A.K × A.K) → ℂ := fun q => K0 q * A.etaK q.2.1
  have hH : Integrable H (μK.prod (μK.prod μK)) :=
    hK0i.mul_bdd (c := 1) (hηm.comp (measurable_fst.comp measurable_snd)).aestronglyMeasurable
      (Eventually.of_forall fun q => (norm_eta _).le)

  have hsymm : (Algebra.traceForm F A.K).IsSymm := ⟨fun x y => by simp [mul_comm]⟩
  have hI := fun y => ((_root_.GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel F E ψ hψ A.K (Algebra.traceForm F A.K) hsymm hnd μK hμ).1 M hMo hMc).2 y
  set N : Set A.K := {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} with hNdef
  have hN : {y | ∀ x ∈ M, ψ (Algebra.traceForm F A.K x y) = 1} = N := by
    ext y
    simp only [Set.mem_setOf_eq, N, Algebra.traceForm_apply]
    constructor
    · intro h x hx; exact h x (by rw [← SetLike.mem_coe, hMset]; exact hx)
    · intro h x hx; exact h x (by rw [← SetLike.mem_coe, hMset] at hx; exact hx)
  set vol : ℂ := (((μK (M : Set A.K)).toReal : ℝ) : ℂ) with hvol
  let Q : A.K × A.K → ℂ := fun p => vol * (φ' (p.2, p.1) * N.indicator (fun _ => (1 : ℂ)) (p.1 * p.2 - a) * A.etaK p.1)
  have h3 : ∀ p : A.K × A.K, ∫ z, H (z, p) ∂μK = Q p := by
    rintro ⟨t, b⟩
    have e1 : ∀ z, H (z, (t, b)) = (φ' (b, t) * A.etaK t) *
        (M : Set A.K).indicator (fun z => ψ (Algebra.traceForm F A.K z (t * b - a))) z := by
      intro z
      by_cases hz : z ∈ (M : Set A.K)
      · rw [Set.indicator_of_mem hz]
        simp only [H, K0, χ, Set.indicator_of_mem hz, Algebra.traceForm_apply]
        have : A.psiK ψ (t * z * b) * A.psiK ψ (-(a * z)) = ψ (Algebra.trace F A.K (z * (t * b - a))) := by
          rw [← GlobalTheory.FourKFub.psiK_add]; simp only [Et.psiK]; congr 2; ring
        linear_combination (φ' (b, t) * A.etaK t) * this
      · simp [H, K0, χ, hz]
    simp_rw [e1]
    rw [integral_const_mul, integral_indicator hMm, hI, hN]
    simp only [Q]
    by_cases hy : t * b - a ∈ N
    · simp [Set.indicator_of_mem hy, vol]; ring
    · simp [Set.indicator_of_notMem hy]
  have hQi : Integrable Q (μK.prod μK) :=
    (hH.integral_prod_right (f := H)).congr (Eventually.of_forall h3)
  rw [← hMset, ← integral_indicator hMm]
  trans ∫ z, ∫ p, H (z, p) ∂(μK.prod μK) ∂μK
  · refine integral_congr_ae ?_
    filter_upwards [hH.prod_right_ae] with z hz
    rw [integral_prod _ hz]
    by_cases hzM : z ∈ (M : Set A.K)
    · rw [Set.indicator_of_mem hzM, ← integral_mul_const]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [H, K0, χ, Set.indicator_of_mem hzM]
      rw [← integral_mul_const, ← integral_mul_const]
      refine integral_congr_ae (Eventually.of_forall fun b => ?_)
      simp only
      ring
    · simp [Set.indicator_of_notMem hzM, H, K0, χ]
  rw [integral_integral_swap (f := fun z p => H (z, p)) hH]
  simp_rw [h3]
  rw [integral_prod Q hQi, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [Q, vol]
  rw [← integral_mul_const, ← integral_const_mul]

end GlobalTheory.WhitCollapse
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOrbitalIntegralLiftLastBasisReduce
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step.OrbULift
theorem actU_uEmb_liftH : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (s : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) (ν : E) (l : F), actU (GlobalTheory.JR.Step.uEmb r E s) (GlobalTheory.JR.Step.liftH X ν l) = GlobalTheory.JR.Step.liftH (actU s X) ν l := _root_.GlobalTheory.JR.Step.actU_uEmb_liftH
theorem unitU_liftH : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F), ‖ν‖ ≤ 1 → unitU (r + 1) F E (GlobalTheory.JR.Step.liftH X ν l) = (if ‖l‖ ≤ 1 then 1 else 0) * unitU r F E X := GlobalTheory.T.unitIndicatorHermitianBlock_liftLastBasis_of_norm_le_one
theorem support_sub : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F), ‖ν‖ = 1 → ∀ g : Matrix.unitaryGroup (Fin (r + 1)) E, unitU (r + 1) F E (actU g (GlobalTheory.JR.Step.liftH X ν l)) ≠ 0 → ∃ k ∈ uO (r + 1) E, ∃ s, g = k * GlobalTheory.JR.Step.uEmb r E s := _root_.GlobalTheory.JR.Step.actU_liftH_mem_uO_mul_uEmb
theorem support_bounded : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {n : ℕ} (Y : Hn n F E), Delta (inv Y.toGl) ≠ 0 → ∃ K : Set (Matrix.unitaryGroup (Fin n) E), IsCompact K ∧ ∀ g, unitU n F E (actU g Y) ≠ 0 → g ∈ K := _root_.GlobalTheory.JR.SuppBdd.exists_compact_of_integral
theorem uEmb_isClosedEmbedding : ∀ (r : ℕ) (E : Type) [NormedField E] [StarRing E] [ContinuousStar E], Topology.IsClosedEmbedding (GlobalTheory.JR.Step.uEmb r E) := _root_.GlobalTheory.JR.Step.isClosedEmbedding_uEmb

section Reformulated
variable {E : Type} [NormedField E]

theorem entries_mul_le {n : ℕ} [IsUltrametricDist E] {P Q : Matrix (Fin n) (Fin n) E}
    (hP : ∀ i j, ‖P i j‖ ≤ 1) (hQ : ∀ i j, ‖Q i j‖ ≤ 1) : ∀ i j, ‖(P * Q) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hP i k) (norm_nonneg _) (hQ k j)

theorem entries_mulVec_le {n : ℕ} [IsUltrametricDist E] {P : Matrix (Fin n) (Fin n) E} {v : Fin n → E}
    (hP : ∀ i j, ‖P i j‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1) : ∀ i, ‖(P *ᵥ v) i‖ ≤ 1 := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hP i k) (norm_nonneg _) (hv k)

variable [StarRing E]

theorem entries_star_le {n : ℕ} [NormedStarGroup E] {P : Matrix (Fin n) (Fin n) E}
    (hP : ∀ i j, ‖P i j‖ ≤ 1) : ∀ i j, ‖(star P) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.star_apply, norm_star]
  exact hP j i

theorem uO_mul {n : ℕ} [IsUltrametricDist E]
    {a b : Matrix.unitaryGroup (Fin n) E} (ha : a ∈ uO n E) (hb : b ∈ uO n E) : a * b ∈ uO n E :=
  entries_mul_le (P := a.1) (Q := b.1) ha hb

theorem uO_one {n : ℕ} : (1 : Matrix.unitaryGroup (Fin n) E) ∈ uO n E := by
  intro i j
  show ‖(1 : Matrix (Fin n) (Fin n) E) i j‖ ≤ 1
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem uO_inv {n : ℕ} [NormedStarGroup E]
    {a : Matrix.unitaryGroup (Fin n) E} (ha : a ∈ uO n E) : a⁻¹ ∈ uO n E :=
  entries_star_le (P := a.1) ha

theorem uO_isOpen {n : ℕ} [IsUltrametricDist E] : IsOpen (uO n E) := by
  have e : uO n E = ⋂ i, ⋂ j, (fun g : Matrix.unitaryGroup (Fin n) E => g.1 i j) ⁻¹' Metric.closedBall 0 1 := by
    ext g; simp [uO]
  rw [e]
  have hc : ∀ i j, Continuous (fun g : Matrix.unitaryGroup (Fin n) E => g.1 i j) := fun i j =>
    (continuous_subtype_val (p := fun M => M ∈ Matrix.unitaryGroup (Fin n) E)).matrix_elem i j
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (IsUltrametricDist.isOpen_closedBall (0 : E) one_ne_zero).preimage (hc i j)

theorem isClosed_unitaryGroup' {n : ℕ} [ContinuousStar E] :
    IsClosed (Matrix.unitaryGroup (Fin n) E : Set (Matrix (Fin n) (Fin n) E)) := by
  have e : (Matrix.unitaryGroup (Fin n) E : Set (Matrix (Fin n) (Fin n) E)) = {M | star M * M = 1} := by
    ext M; exact Matrix.mem_unitaryGroup_iff'
  rw [e]
  exact isClosed_eq (continuous_star.matrix_mul continuous_id) continuous_const

theorem uO_isCompact {n : ℕ} [ProperSpace E] [ContinuousStar E] : IsCompact (uO n E) := by
  let B : Set (Matrix (Fin n) (Fin n) E) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => Metric.closedBall (0 : E) 1
  have hB : IsCompact B := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have e : uO n E = Subtype.val ⁻¹' B := by
    ext g
    show (∀ i j, ‖g.1 i j‖ ≤ 1) ↔
      (∀ i ∈ (Set.univ : Set (Fin n)), ∀ j ∈ (Set.univ : Set (Fin n)), g.1 i j ∈ Metric.closedBall (0 : E) 1)
    simp
  rw [e]
  exact (isClosed_unitaryGroup' (n := n)).isClosedEmbedding_subtypeVal.isCompact_preimage hB

theorem preimage_uO (r : ℕ) : uEmb r E ⁻¹' uO (r + 1) E = uO r E := by
  ext s
  simp only [Set.mem_preimage, uO, Set.mem_setOf_eq]
  constructor
  · intro h i j
    have := h (Fin.castSucc i) (Fin.castSucc j)
    simpa [uEmb, embHom, Matrix.reindex_apply] using this
  · intro h i j
    show ‖(embHom r E s.1) i j‖ ≤ 1
    simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindex_apply, Matrix.submatrix_apply]
    generalize finSumFinEquiv.symm i = a
    generalize finSumFinEquiv.symm j = b
    rcases a with a | a <;> rcases b with b | b
    · simpa using h a b
    · simp
    · simp
    · rw [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]; split_ifs <;> simp

theorem actU_mul {F : Type} [CommRing F] [Algebra F E] {n : ℕ} (k g : Matrix.unitaryGroup (Fin n) E)
    (Y : Hn n F E) : actU (k * g) Y = actU k (actU g Y) := by
  unfold actU
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ rfl)
  · show (k.1 * g.1) * Y.1.1 * star (k.1 * g.1) = k.1 * (g.1 * Y.1.1 * star g.1) * star k.1
    rw [star_mul]; simp only [Matrix.mul_assoc]
  · show (k.1 * g.1) *ᵥ Y.2.1 = k.1 *ᵥ (g.1 *ᵥ Y.2.1)
    rw [Matrix.mulVec_mulVec]

theorem actU_one {F : Type} [CommRing F] [Algebra F E] {n : ℕ} (Y : Hn n F E) :
    actU (1 : Matrix.unitaryGroup (Fin n) E) Y = Y := by
  unfold actU
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ rfl)
  · show (1 : Matrix (Fin n) (Fin n) E) * Y.1.1 * star (1 : Matrix (Fin n) (Fin n) E) = Y.1.1
    simp
  · show (1 : Matrix (Fin n) (Fin n) E) *ᵥ Y.2.1 = Y.2.1
    simp

theorem integral_actU {F : Type} [NormedField F] [Algebra F E] [IsUltrametricDist E] [NormedStarGroup E] {n : ℕ}
    (k : Matrix.unitaryGroup (Fin n) E) (hk : k ∈ uO n E) (Y : Hn n F E)
    (hY : Y ∈ {X : Hn n F E | (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1}) :
    actU k Y ∈ {X : Hn n F E | (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1} := by
  obtain ⟨h1, h2, h3⟩ := hY
  refine ⟨?_, ?_, h3⟩
  · exact entries_mul_le (entries_mul_le hk h1) (entries_star_le hk)
  · exact entries_mulVec_le hk h2

end Reformulated

theorem unitU_actU_mul {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [IsUltrametricDist E] [NormedStarGroup E] {n : ℕ} (k g : Matrix.unitaryGroup (Fin n) E) (hk : k ∈ uO n E)
    (Y : Hn n F E) : unitU n F E (actU (k * g) Y) = unitU n F E (actU g Y) := by
  rw [actU_mul]
  have hiff : ∀ Z : Hn n F E, actU k Z ∈ {X : Hn n F E | (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1} ↔
      Z ∈ {X : Hn n F E | (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1} := fun Z =>
    ⟨fun h => by
      have := integral_actU k⁻¹ (uO_inv hk) _ h
      rwa [← actU_mul, inv_mul_cancel, actU_one] at this, fun h => integral_actU k hk Z h⟩
  unfold unitU
  by_cases h : actU g Y ∈ {X : Hn n F E | (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1}
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hiff _).2 h)]; rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hiff _).1 h'))]

theorem compact_support {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F)
    (hΔ : Delta (inv (liftH X ν l).toGl) ≠ 0) :
    HasCompactSupport (fun s => unitU (r + 1) F E (actU (uEmb r E s) (liftH X ν l))) := by
  haveI : NormedStarGroup E := ⟨fun x => (Unram.norm_star (F := F) x).le⟩
  obtain ⟨K, hK, hsub⟩ := support_bounded (liftH X ν l) hΔ
  refine HasCompactSupport.intro ((uEmb_isClosedEmbedding r E).isCompact_preimage hK) ?_
  intro s hs
  by_contra h
  exact hs (hsub _ h)

theorem orbU_liftH (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas (r + 1) F E) (M' : Meas r F E) (X : Hn r F E) (ν : E) (l : F) (hν : ‖ν‖ = 1) (hΔ : Delta (inv (GlobalTheory.JR.Step.liftH X ν l).toGl) ≠ 0) :
  orbU M (unitU (r + 1) F E) (GlobalTheory.JR.Step.liftH X ν l) = (if ‖l‖ ≤ 1 then 1 else 0) * orbU M' (unitU r F E) X := by
  haveI : IsUltrametricDist E := Unram.ultraE (F := F)
  haveI : NormedStarGroup E := ⟨fun x => (Unram.norm_star (F := F) x).le⟩
  haveI : LocallyCompactSpace E := Unram.lcE (F := F)
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : SecondCountableTopology (Matrix (Fin (r+1)) (Fin (r+1)) E) :=
    inferInstanceAs (SecondCountableTopology (Fin (r+1) → Fin (r+1) → E))
  haveI : SecondCountableTopology (Matrix.unitaryGroup (Fin (r+1)) E) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace (Matrix.unitaryGroup (Fin (r+1)) E) := by
    exact IsCompact.locallyCompactSpace_of_mem_nhds_of_group (uO_isCompact (n := r + 1))
      (uO_isOpen.mem_nhds uO_one)
  let R₀ : Subgroup (Matrix.unitaryGroup (Fin (r+1)) E) :=
    { carrier := uO (r+1) E, mul_mem' := uO_mul, one_mem' := uO_one, inv_mem' := uO_inv }
  unfold orbU
  letI := M.mU; haveI := M.bU; letI := M'.mU; haveI := M'.bU
  haveI := M.haarU; haveI := M'.haarU
  haveI := (GlobalTheory.T.unitaryGroup_positiveCharacter_trivial_and_unimodular F E (r+1)).2 M
  haveI := (GlobalTheory.T.unitaryGroup_positiveCharacter_trivial_and_unimodular F E r).2 M'
  rw [GlobalTheory.CosetIntegral.integral_eq_of_coset_support _ _ (uEmb r E) (uEmb_isClosedEmbedding r E) M.μU M'.μU R₀
    uO_isOpen uO_isCompact M.volU (by
      show M'.μU (uEmb r E ⁻¹' uO (r + 1) E) = 1
      rw [preimage_uO]; exact M'.volU)
    _ (fun k hk g => unitU_actU_mul k g hk _) (support_sub X ν l hν) (compact_support X ν l hΔ)]
  simp_rw [actU_uEmb_liftH, unitU_liftH _ ν l hν.le]
  rw [integral_const_mul]
end GlobalTheory.JR.Step.OrbULift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitsAdicCompletionHomExtOfIsOpenKer
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem units_adicCompletion_hom_ext (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (B : Type) [Group B] (f g : (v.adicCompletion F)ˣ →* B)
    (hf : IsOpen (f.ker : Set (v.adicCompletion F)ˣ))
    (hg : IsOpen (g.ker : Set (v.adicCompletion F)ˣ))
    (hc : ∀ c : Fˣ, f (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c) =
      g (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c)) :
    ∀ x, f x = g x := by
  intro x
  set S : Set (v.adicCompletion F)ˣ :=
    (fun y => x⁻¹ * y) ⁻¹' ((f.ker : Set (v.adicCompletion F)ˣ) ∩ g.ker) with hS
  have hSo : IsOpen S := (hf.inter hg).preimage (continuous_const.mul continuous_id)
  have hxS : x ∈ S := by simp [hS, MonoidHom.mem_ker]
  obtain ⟨U, hU, hUS⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hSo
  have hxU : (x : v.adicCompletion F) ∈ U := by
    rw [← hUS] at hxS; exact hxS
  have hU0 : IsOpen (U ∩ {0}ᶜ) := hU.inter isOpen_compl_singleton
  obtain ⟨k, hk⟩ := (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F v).exists_mem_open
    hU0 ⟨x, hxU, by simp⟩
  have hk0 : k ≠ 0 := by
    rintro rfl; exact hk.2 (by simp)
  set c : Fˣ := Units.mk0 k hk0
  have hcS : Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c ∈ S := by
    rw [← hUS]; simpa [c] using hk.1
  simp only [hS, Set.mem_preimage, Set.mem_inter_iff, SetLike.mem_coe, MonoidHom.mem_ker,
    map_mul, map_inv] at hcS
  have h1 : f (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c) = f x := by
    have := hcS.1; rw [inv_mul_eq_one] at this; exact this.symm
  have h2 : g (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c) = g x := by
    have := hcS.2; rw [inv_mul_eq_one] at this; exact this.symm
  rw [← h1, ← h2, hc]

end GlobalTheory
end

