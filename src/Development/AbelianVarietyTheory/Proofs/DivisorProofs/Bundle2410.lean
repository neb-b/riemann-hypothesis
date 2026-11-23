module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0983
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1534
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2123
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeMeasureUnitaryDetOneFactorNearIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2327
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0803
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2360

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntegrableRegularVariety
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MeasureTheory Set Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ChartGlue
open scoped ENNReal

namespace GlobalTheory.LogNormInt

theorem integrableOn_of_chart {M : Type} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] {n : ℕ}
    (e : OpenPartialHomeomorph M (V n)) {μ : Measure M} {ρ : V n → ℝ≥0∞}
    (hμ : ∀ A, MeasurableSet A → A ⊆ e.source → μ A = ∫⁻ v in e '' A, ρ v)
    {A : Set M} (hA : MeasurableSet A) (hAs : A ⊆ e.source) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hρ : ∀ v ∈ e '' A, ρ v ≤ C) {f : M → ℝ} (hf : ContinuousOn f A)
    (hi : IntegrableOn (f ∘ e.symm) (e '' A)) : IntegrableOn f A μ := by
  have hm := measurableSet_image e hA hAs
  have hsub : e '' A ⊆ e.target := fun _ ⟨y, hy, h⟩ => h ▸ e.map_source (hAs hy)
  have hs : AEMeasurable e.symm (volume.restrict (e '' A)) :=
    (e.continuousOn_symm.mono hsub).aemeasurable hm
  have hle : μ.restrict A ≤ C • Measure.map e.symm (volume.restrict (e '' A)) := by
    refine Measure.le_iff.2 fun B hB => ?_
    have hBA := hB.inter hA
    have hm' := measurableSet_image e hBA (inter_subset_right.trans hAs)
    rw [Measure.restrict_apply hB, hμ _ hBA (inter_subset_right.trans hAs), Measure.smul_apply,
      Measure.map_apply_of_aemeasurable hs hB, Measure.restrict_apply' hm, smul_eq_mul]
    refine (setLIntegral_mono' hm' fun v hv => hρ v (image_mono inter_subset_right hv)).trans ?_
    rw [setLIntegral_const]
    gcongr
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨by rw [mem_preimage, e.left_inv (hAs hy.2)]; exact hy.1, mem_image_of_mem _ hy.2⟩
  refine ⟨hf.aestronglyMeasurable hA, ?_⟩
  refine (lintegral_mono' hle le_rfl).trans_lt ?_
  rw [lintegral_smul_measure, smul_eq_mul]
  exact ENNReal.mul_lt_top hC.lt_top ((lintegral_map_le _ hs).trans_lt hi.2)

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem continuousAt_ratVal {f : X.functionField} {y : CxPts p σ} (hf : RegAt (under y) f) :
    ContinuousAt (fun z : CxPts p σ => ratVal f z) y := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  have hn := (isOpen_ptsIn (p := p) (σ := σ) U).mem_nhds (mem_ptsIn.2 hU)
  refine ((continuousOn_ev a).continuousAt hn).congr ?_
  filter_upwards [hn] with z hz
  exact (ratVal_fnOf hz _ a).symm

theorem frequently_ne_zero (hσ : Function.Injective σ) (c : AlgChart p σ D) {U : X.Opens}
    {a : Γ(X, U)} (ha : a ≠ 0) {y : CxPts p σ} (hy : y ∈ c.e.source) (hU : y ∈ ptsIn p σ U) :
    ∃ᶠ v in 𝓝 (c.e y), (ev p σ U a ∘ c.e.symm) v ≠ 0 := by
  have : IsDomain k := hσ.isDomain σ
  have hg := gen_mem (mem_ptsIn.1 hU)
  have hb : genericPoint X ∈ X.basicOpen a := (unitAt_fnOf_iff hg hg a).1
    (unitAt_genericPoint ((map_ne_zero_iff _ (fnOf_injective U hg)).2 ha))
  have h := Measure.dense_of_ae (SemiPosBir.ae_mem hσ c (U := X.basicOpen a) ⟨_, hb⟩)
  have h₁ := mem_closure_iff_frequently.1 (h (c.e y))
  refine (h₁.and_eventually ((isOpen_over c.e (isOpen_ptsIn U)).mem_nhds (mem_over c.e hy hU))).mono ?_
  rintro v ⟨h₂, h₃⟩
  exact (mem_ptsIn_basicOpen h₃.2 a).1 (h₂ h₃.1)

theorem exists_integrableOn [SecondCountableTopology (CxPts p σ)] (hσ : Function.Injective σ)
    {A B : LB X} {ψ : Weight p σ A} (hψ : ψ.IsCInf) {φ : Weight p σ B} (hφ : φ.IsCInf)
    {r : B.ι → X.functionFieldˣ} (hr : IsRatSec B r) (ε : ℤˣ) (c : AlgChart p σ D) {y : CxPts p σ}
    (hy : y ∈ c.e.source) : ∃ O ∈ 𝓝 y, IntegrableOn (logNorm φ r)
      (offSupp p σ (divOfRatSec φ.isLB hr) ∩ O) (ψ.chernPart D ε) := by
  set i := pick φ.isLB y
  have hi : y ∈ ptsIn p σ (B.U i) := mem_pick _ y
  have hyU := c.source_subset hy
  have hg := gen_mem (mem_ptsIn.1 hyU)
  have : Nonempty c.U := ⟨⟨_, hg⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X c.U c.affine
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(X, c.U)) (r i : X.functionField)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  change fnOf c.U hg a / fnOf c.U hg b = _ at hab
  have hb1 : fnOf c.U hg b ≠ 0 := (map_ne_zero_iff _ (fnOf_injective _ hg)).2 hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hab
    exact (r i).ne_zero hab.symm
  have hT := (isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) c.U)).mem_nhds (mem_over c.e hy hyU)
  have hd (s : Γ(X, c.U)) : ∀ᶠ v in 𝓝 (c.e y), DifferentiableAt ℂ (ev p σ c.U s ∘ c.e.symm) v :=
    (c.holo _ s).eventually_differentiableAt hT
  obtain ⟨δ, hδ, hae, hint⟩ := exists_integrableOn_log_norm_div volume (hd a) (hd b)
    (frequently_ne_zero hσ c ha0 hy hyU) (frequently_ne_zero hσ c hb0 hy hyU)
  have hT' := (isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i))).mem_nhds (mem_over c.e hy hi)
  obtain ⟨η, hη, hηs⟩ := nhds_basis_closedBall.mem_iff.1 (inter_mem hT' (ball_mem_nhds _ hδ))
  have hcont : ContinuousOn (fun v => c.chernDens ψ (c.e.symm v)) c.e.target :=
    continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
      ((Continuous.matrix_det continuous_id).comp_continuousOn
        ((GlobalTheory.MixDens.chernMat_isForm k X p σ D _ ψ hψ).2.1 c)))
  obtain ⟨C, hC⟩ := (isCompact_closedBall (c.e y) η).exists_bound_of_continuousOn
    (hcont.mono fun v hv => (hηs hv).1.1)
  set O := c.e.source ∩ c.e ⁻¹' ball (c.e y) η
  have hO : IsOpen O := c.e.continuousOn.isOpen_inter_preimage c.e.open_source isOpen_ball
  set S := offSupp p σ (divOfRatSec φ.isLB hr) ∩ O
  have hS : IsOpen S := (isOpen_offSupp _).inter hO
  have hSs : S ⊆ c.e.source := fun z hz => hz.2.1
  have him : c.e '' S ⊆ closedBall (c.e y) η := by
    rintro _ ⟨z, hz, rfl⟩
    exact ball_subset_closedBall hz.2.2
  have hSi (z) (hz : z ∈ S) : z ∈ ptsIn p σ (B.U i) := by
    have := (hηs (him (mem_image_of_mem _ hz))).1.2
    rwa [mem_preimage, c.e.left_inv (hSs hz)] at this
  have hm := measurableSet_image c.e hS.measurableSet hSs
  refine ⟨O, hO.mem_nhds ⟨hy, by exact Set.mem_preimage.mpr (mem_ball_self hη)⟩, integrableOn_of_chart c.e
    (fun A hA hAs => Weight.chernPart_apply hψ ε c hA hAs) hS.measurableSet hSs
    (C := ENNReal.ofReal C) ENNReal.ofReal_ne_top (fun v hv => ENNReal.ofReal_le_ofReal ?_) ?_ ?_⟩
  · have h := hC v (him hv)
    rw [Real.norm_eq_abs, abs_le] at h
    rcases Int.units_eq_one_or ε with rfl | rfl
    · simpa using h.2
    · simpa [neg_le] using h.1
  · refine ContinuousOn.congr (f := fun z => Real.log ‖ratVal (r i : X.functionField) z‖ - φ.φ i z / 2)
      (fun z hz => ContinuousAt.continuousWithinAt ?_) fun z hz => logNorm_eq φ hr hz.1 (hSi z hz)
    have hu := hr.unitAt φ.isLB hz.1 (hSi z hz)
    exact ((continuousAt_ratVal hu.regAt).norm.log (norm_ne_zero_iff.2 (ratVal_ne_zero hu))).sub
      ((hφ i z (hSi z hz)).continuousAt.div_const 2)
  · have hsub : c.e '' S ⊆ ball (c.e y) δ := fun v hv => (hηs (him hv)).2
    have h₁ : IntegrableOn (fun v => (φ.φ i ∘ c.e.symm) v / 2) (c.e '' S) :=
      (((((contDiffOn_chart (hφ i) c).continuousOn.mono fun v hv => (hηs hv).1).div_const
        2).integrableOn_compact (isCompact_closedBall _ _)).mono_set him)
    refine ((hint.mono_set hsub).sub h₁).congr ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hae, ae_restrict_mem hm] with v hv hv'
    obtain ⟨z, hz, rfl⟩ := hv'
    have hzU := c.source_subset (hSs hz)
    have hu := hr.unitAt φ.isLB hz.1 (hSi z hz)
    have e := ratVal_mul hu.regAt (regAt_fnOf (mem_ptsIn.1 hzU) hg b)
    rw [← hab, div_mul_cancel₀ _ hb1, hab, ratVal_fnOf hzU, ratVal_fnOf hzU] at e
    simp only [Function.comp_apply, Pi.sub_apply, c.e.left_inv (hSs hz)] at hv ⊢
    rw [logNorm_eq φ hr hz.1 (hSi z hz), e, mul_div_cancel_right₀ _ hv.2]

end GlobalTheory.LogNormInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMassProductLowerBoundUnitaryPq
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp.MassLow

theorem perm_conj' {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ} (e : ι ≃ Fin r) (M : Matrix (Fin r) (Fin r) ℂ) :
    permM e * M * (permM e)ᵀ = M.submatrix e e := by
  ext i j
  simp [Matrix.mul_apply, permM]

theorem det_lift {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {κ : Type} {p q : κ → ℕ}
    {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {x : Frame Ψ r} {σ : κ ≃ Ψ}
    {A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ} {e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r}
    (hI : IsIdent p q Ψ G x σ A e) (ρ : κ) (s : realSU Ψ G) (u : UpqT (p ρ) (q ρ))
    (hu : UpqT.mat u * A ρ = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) :
    (UpqT.mat u).det = 1 := by
  obtain ⟨h1, h2, h3, -⟩ := MassUp.inv_facts hI ρ
  set S := ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)
  set P := permM (e ρ)
  have hS : S.det = 1 := (s.2 (σ ρ)).1
  set M := (Pᵀ * A ρ) * S * mat x (σ ρ) with hM
  have hx : mat x (σ ρ) * M = S * mat x (σ ρ) := by
    rw [hM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hu' : UpqT.mat u = P * M * Pᵀ := by
    calc UpqT.mat u = UpqT.mat u * (A ρ * (mat x (σ ρ) * Pᵀ)) := by rw [h3, Matrix.mul_one]
      _ = A ρ * (S * mat x (σ ρ)) * Pᵀ := by
        rw [← Matrix.mul_assoc, hu]; simp only [Matrix.mul_assoc]
      _ = P * M * Pᵀ := by
        rw [← hx, ← Matrix.mul_assoc, (hI ρ).2]
  rw [hu', perm_conj', Matrix.det_submatrix_equiv_self, hM, Matrix.det_mul, Matrix.det_mul, hS, mul_one,
    ← Matrix.det_mul, h1, Matrix.det_one]

theorem arith (f r : ℕ) (ε : ℝ) (hr : 1 ≤ r) (hε : 0 < ε) :
    (1 / 16 : ℝ) ^ (f * r ^ 2) * (8 * ε) ^ (f * (r ^ 2 - 1)) ≤ (ε ^ (r ^ 2 - 1) / (r : ℝ) ^ (r - 1)) ^ f := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have key : (1 / 16 : ℝ) ^ (r ^ 2) * (8 * ε) ^ (r ^ 2 - 1) ≤ ε ^ (r ^ 2 - 1) / (r : ℝ) ^ (r - 1) := by
    have hrp : (r : ℝ) ^ (r - 1) ≤ 2 ^ (r ^ 2) := by
      have h1 : (r : ℝ) ≤ 2 ^ r := by exact_mod_cast (Nat.lt_two_pow_self).le
      calc (r : ℝ) ^ (r - 1) ≤ ((2 : ℝ) ^ r) ^ (r - 1) := pow_le_pow_left₀ hr0.le h1 _
        _ = 2 ^ (r * (r - 1)) := by rw [← pow_mul]
        _ ≤ 2 ^ (r ^ 2) := pow_le_pow_right₀ (by norm_num) (by rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    have h8 : (8 : ℝ) ^ (r ^ 2 - 1) ≤ 8 ^ (r ^ 2) := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    rw [le_div_iff₀ (pow_pos hr0 _), mul_pow]
    have hε' : 0 ≤ ε ^ (r ^ 2 - 1) := pow_nonneg hε.le _
    calc (1 / 16 : ℝ) ^ (r ^ 2) * (8 ^ (r ^ 2 - 1) * ε ^ (r ^ 2 - 1)) * (r : ℝ) ^ (r - 1)
        ≤ (1 / 16 : ℝ) ^ (r ^ 2) * (8 ^ (r ^ 2) * ε ^ (r ^ 2 - 1)) * 2 ^ (r ^ 2) := by gcongr
      _ = ((1 / 16 : ℝ) * 8 * 2) ^ (r ^ 2) * ε ^ (r ^ 2 - 1) := by rw [mul_pow, mul_pow]; ring
      _ = ε ^ (r ^ 2 - 1) := by norm_num
  have e1 : (1 / 16 : ℝ) ^ (f * r ^ 2) = ((1 / 16 : ℝ) ^ (r ^ 2)) ^ f := by rw [← pow_mul, mul_comm f]
  have e2 : (8 * ε) ^ (f * (r ^ 2 - 1)) = ((8 * ε) ^ (r ^ 2 - 1)) ^ f := by rw [← pow_mul, mul_comm f]
  rw [e1, e2, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) key f

theorem massLow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) [Fintype κ] (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ)) (π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G) (m : ∀ ρ, Measure (UpqT (p ρ) (q ρ))) (ρ₀ : κ), 1 ≤ r → IsIdent p q Ψ G x σ A e → Continuous π → IsProj p q Ψ G σ A a₀ π → (∀ (s : realSU Ψ G) (b₀ : ∀ ρ, UpqT (p ρ) (q ρ)), (∀ ρ, UpqT.mat (b₀ ρ) * A ρ = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → ∀ b, π (b₀ * b) = s * π b) → (∀ ρ, IsMinf (m ρ)) → ∀ S : Set (realSU Ψ G), MeasurableSet S → ENNReal.ofReal ((1 / 16 : ℝ) ^ (Ψ.card * r ^ 2)) * riemHaar Ψ G x S ≤ Measure.pi m (π ⁻¹' S ∩ {b | 0 < (UpqT.mat (b ρ₀)).det.im}) := by
  intro E _ _ _ r κ _ p q Ψ G x σ A e a₀ π m ρ₀ hr hI hπc hP hT hm S hS
  classical
  haveI : ∀ ρ, IsTopologicalGroup (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).1
  haveI : ∀ ρ, LocallyCompactSpace (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.1
  haveI : ∀ ρ, SecondCountableTopology (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.2.1
  haveI : ∀ ρ, BorelSpace (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.2.2.1
  haveI : ∀ ρ, (m ρ).IsHaarMeasure := fun ρ => (hm ρ).1
  have hcard : Fintype.card κ = Ψ.card := by
    rw [Fintype.card_congr σ]; simp
  have hΨ : 1 ≤ Ψ.card := by
    rw [← hcard]; exact Fintype.card_pos_iff.2 ⟨ρ₀⟩
  have hG : G.det ≠ 0 := MassUp.det_ne hI ρ₀
  have hx : ∀ τ, (mat x τ).det ≠ 0 := by
    intro τ
    obtain ⟨ρ, rfl⟩ := σ.surjective τ
    exact Matrix.det_ne_zero_of_right_inverse (MassUp.inv_facts hI ρ).2.1
  have hpq : ∀ ρ, p ρ + q ρ = r := by
    intro ρ; simpa using Fintype.card_congr (e ρ)
  have hπm : Measurable π := hπc.measurable
  set μ := Measure.pi m with hμ
  set T : Set (∀ ρ, UpqT (p ρ) (q ρ)) := {b | 0 < (UpqT.mat (b ρ₀)).det.im} with hTdef
  have hTo : IsOpen T := isOpen_lt continuous_const
    (Complex.continuous_im.comp ((GlobalTheory.UpqTopology.continuous_mat.comp (continuous_apply ρ₀)).matrix_det))
  have hTm : MeasurableSet T := hTo.measurableSet
  set ν := (μ.restrict T).map π with hν

  haveI hinv : ν.IsMulLeftInvariant := by
    constructor
    intro s
    obtain ⟨b₀, hb₀⟩ := MassUp.exists_lift E r κ p q Ψ G x σ A e hI s
    have hd : (UpqT.mat (b₀ ρ₀)).det = 1 := det_lift hI ρ₀ s (b₀ ρ₀) (hb₀ ρ₀)
    have hpre : (fun b => b₀ * b) ⁻¹' T = T := by
      ext b
      simp only [Set.mem_preimage, hTdef, Set.mem_setOf_eq, Pi.mul_apply]
      rw [show UpqT.mat (b₀ ρ₀ * b ρ₀) = UpqT.mat (b₀ ρ₀) * UpqT.mat (b ρ₀) from rfl, Matrix.det_mul, hd, one_mul]
    rw [hν, Measure.map_map (measurable_const_mul s) hπm]
    have h : (fun y => s * y) ∘ π = π ∘ (fun b => b₀ * b) := funext fun b => (hT s b₀ hb₀ b).symm
    rw [h, ← Measure.map_map hπm (measurable_const_mul b₀)]
    congr 1
    calc (μ.restrict T).map (fun b => b₀ * b)
        = (μ.restrict ((fun b => b₀ * b) ⁻¹' T)).map (fun b => b₀ * b) := by rw [hpre]
      _ = (μ.map (fun b => b₀ * b)).restrict T := (Measure.restrict_map (measurable_const_mul b₀) hTm).symm
      _ = μ.restrict T := by rw [map_mul_left_eq_self]
  haveI hH : (riemHaar Ψ G x).IsHaarMeasure :=
    (GlobalTheory.SUVol.DensOne.tangentHaar_riemLie (Ψ := Ψ) (G := G) (hG := hG) (x := x) (hx := hx)).1

  have hup := MassUp.massUp E r κ p q Ψ G x σ A e a₀ π m hr hΨ hI hπc hP hT hm
  haveI : IsFiniteMeasureOnCompacts ν := by
    constructor
    intro K hK
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    rw [hν, Measure.map_apply hπm hKm]
    calc μ.restrict T (π ⁻¹' K) ≤ μ (π ⁻¹' K) := Measure.restrict_le_self _
      _ ≤ _ := hup K hKm
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top
  have hc := Measure.isMulLeftInvariant_eq_smul ν (riemHaar Ψ G x)
  set c := ν.haarScalarFactor (riemHaar Ψ G x) with hcdef

  have hplace := fun ρ => _root_.GlobalTheory.CovTop.VolLow.OneMeasure.le_measure_sMat_near (p ρ) (q ρ) (a₀ ρ) (m ρ) (hm ρ)
  choose εp hεp hbp using hplace
  obtain ⟨εu, hεu, hbu⟩ := _root_.GlobalTheory.CovTop.VolUp.UpBall.riemHaar_frBall_le E r κ p q Ψ G x σ A e hr hI
  set δ := Finset.univ.inf' ⟨ρ₀, Finset.mem_univ _⟩ εp with hδdef
  have hδ : 0 < δ := (Finset.lt_inf'_iff _).2 fun ρ _ => hεp ρ
  set ε := min δ εu / 2 with hεdef
  have hεm : ε < min δ εu := half_lt_self (lt_min hδ hεu)
  have hε : 0 < ε := half_pos (lt_min hδ hεu)
  have hεδ : ∀ ρ, ε < εp ρ := fun ρ =>
    lt_of_lt_of_le (lt_of_lt_of_le hεm (min_le_left _ _)) (Finset.inf'_le _ (Finset.mem_univ ρ))
  have hεu' : ε < εu := lt_of_lt_of_le hεm (min_le_right _ _)
  have hopen : IsOpen (frBall Ψ G x ε) := by
    have hc' : ∀ τ a b, Continuous fun s : realSU Ψ G =>
        ‖((mat x τ)⁻¹ * ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ - 1) a b‖ := by
      intro τ a b
      have h1 : Continuous fun s : realSU Ψ G => ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) :=
        Units.continuous_val.comp ((continuous_apply τ).comp continuous_subtype_val)
      exact ((((continuous_const.matrix_mul h1).matrix_mul continuous_const).sub continuous_const).matrix_elem a b).norm
    have : frBall Ψ G x ε = ⋂ τ, ⋂ a, ⋂ b, {s : realSU Ψ G |
        ‖((mat x τ)⁻¹ * ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ - 1) a b‖ < ε} := by
      ext s; simp [frBall]
    rw [this]
    exact isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun a =>
      isOpen_iInter_of_finite fun b => isOpen_lt (hc' τ a b) continuous_const
  set L := ε ^ (r ^ 2 - 1) / (r : ℝ) ^ (r - 1) with hL
  have hlow : ENNReal.ofReal (L ^ Ψ.card) ≤ ν (frBall Ψ G x ε) := by
    rw [hν, Measure.map_apply hπm hopen.measurableSet, Measure.restrict_apply (hπm hopen.measurableSet),
      MassUp.preimage_frBall E r κ p q Ψ G x σ A e a₀ π hI hP ε]
    have hsub : Set.univ.pi (fun ρ => {u : UpqT (p ρ) (q ρ) | (∀ a b, ‖(sMat (a₀ ρ) u - 1) a b‖ < ε) ∧
        0 < (UpqT.mat u).det.im}) ⊆ Set.univ.pi (fun ρ => {u : UpqT (p ρ) (q ρ) |
          ∀ a b, ‖(sMat (a₀ ρ) u - 1) a b‖ < ε}) ∩ T := by
      intro b hb
      simp only [Set.mem_univ_pi, Set.mem_setOf_eq] at hb
      exact ⟨fun ρ _ => (hb ρ).1, (hb ρ₀).2⟩
    refine le_trans ?_ (measure_mono hsub)
    rw [hμ, Measure.pi_pi]
    calc ENNReal.ofReal (L ^ Ψ.card) = ∏ _ρ : κ, ENNReal.ofReal L := by
          rw [Finset.prod_const, Finset.card_univ, hcard, ENNReal.ofReal_pow (by positivity)]
      _ ≤ _ := Finset.prod_le_prod' fun ρ _ => by
          have := hbp ρ ε hε (hεδ ρ)
          rw [hpq ρ] at this
          exact this
  have hupB := hbu ε hε hεu'
  set U := (8 * ε) ^ (Ψ.card * (r ^ 2 - 1)) with hU
  have hcU : L ^ Ψ.card ≤ (c : ℝ) * U := by
    have h1 : ENNReal.ofReal (L ^ Ψ.card) ≤ ENNReal.ofReal ((c : ℝ) * U) := by
      calc ENNReal.ofReal (L ^ Ψ.card) ≤ ν (frBall Ψ G x ε) := hlow
        _ = (c : ℝ≥0∞) * riemHaar Ψ G x (frBall Ψ G x ε) := by
          conv_lhs => rw [hc]
          rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
        _ ≤ (c : ℝ≥0∞) * ENNReal.ofReal U := mul_le_mul_of_nonneg_left hupB (zero_le)
        _ = ENNReal.ofReal ((c : ℝ) * U) := by
          rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (NNReal.coe_nonneg _) (by positivity))).1 h1
  have hK := arith Ψ.card r ε hr hε
  have hUpos : 0 < U := by positivity
  have hcK : (1 / 16 : ℝ) ^ (Ψ.card * r ^ 2) ≤ c :=
    le_of_mul_le_mul_right (hK.trans hcU) hUpos
  calc ENNReal.ofReal ((1 / 16 : ℝ) ^ (Ψ.card * r ^ 2)) * riemHaar Ψ G x S
      ≤ (c : ℝ≥0∞) * riemHaar Ψ G x S := by
        gcongr
        rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal hcK
    _ = ν S := by
        conv_rhs => rw [hc]
        rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    _ = μ (π ⁻¹' S ∩ T) := by
        rw [hν, Measure.map_apply hπm hS, Measure.restrict_apply (hπm hS)]

end GlobalTheory.CovTop.VolUp.MassLow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelAffineCoverRadical
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

namespace GlobalTheory.BlowArith

theorem exists_isArithVar_effCartier_isIso (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    [IsIntegral X] (D : ℕ) (hX : IsArithVar p D) (J : X.IdealSheafData)
    (hJ : genericPoint X ∉ J.support) :
    ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X), IsArithVar (ρ ≫ p) D ∧
      ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap ρ) ∧
      ∀ V : X.Opens, (∀ x ∈ V, x ∉ J.support) → IsIso (ρ ∣_ V) := by
  have := hX.isNoetherianRing
  obtain ⟨Y, b, hb, hproj, hiso⟩ := ProjBlowup.exists_blowup p hX.isProjOver J
  let V : X.Opens := J.support.compl
  have hbV : IsIso (b ∣_ V) := hiso V fun _ hx => hx
  have : Nonempty V.toScheme := ⟨⟨genericPoint X, hJ⟩⟩
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : Nonempty (b ⁻¹ᵁ V).toScheme := ⟨inv (b ∣_ V) (Classical.arbitrary _)⟩
  have : IsIntegral (b ⁻¹ᵁ V).toScheme := isIntegral_of_isOpenImmersion (b ∣_ V)
  have hU : (J.comap b).support.compl = b ⁻¹ᵁ V := by
    ext y
    exact not_congr (ProjBlowup.mem_support_comap J b y)
  have hdom : IsSchemeTheoreticallyDominant (b ⁻¹ᵁ V).ι :=
    hU ▸ ProjBlowup.isSchemeTheoreticallyDominant_compl_of_effCartier Y _ hb.1
  have : IsNoetherian Y := isNoetherian_of_isProjOver hproj
  have : IsIntegral Y := by
    have : IsReduced Y := IsSchemeTheoreticallyDominant.isReduced (b ⁻¹ᵁ V).ι
    have h := ((IrreducibleSpace.isIrreducible_univ (b ⁻¹ᵁ V).toScheme).image _
      (b ⁻¹ᵁ V).ι.continuous.continuousOn).closure
    rw [Set.image_univ, (b ⁻¹ᵁ V).ι.denseRange.closure_range] at h
    have : IrreducibleSpace Y := (irreducibleSpace_def _).2 h
    exact isIntegral_of_irreducibleSpace_of_isReduced Y
  have hfac : (b ⁻¹ᵁ V).ι ≫ b = b ∣_ V ≫ V.ι := (morphismRestrict_ι b V).symm
  have hoi : IsOpenImmersion ((b ⁻¹ᵁ V).ι ≫ b) := by rw [hfac]; infer_instance
  have hg : (b ⁻¹ᵁ V).ι (genericPoint _) = genericPoint Y := genericPoint_eq_of_isOpenImmersion _
  have hgen : b (genericPoint Y) = genericPoint X := by
    rw [← hg, ← Scheme.Hom.comp_apply]
    exact genericPoint_eq_of_isOpenImmersion _
  have hdeg : b.residueDegree (genericPoint Y) ≠ 0 := by
    intro h0
    have h1 := CurveDegreesCompare.residueDegree_comp (b ⁻¹ᵁ V).ι b (genericPoint _)
    rw [CurveDegreesCompare.residueDegree_of_isOpenImmersion, hg, h0, zero_mul] at h1
    exact one_ne_zero h1
  have hflat : Flat ((b ≫ p) ≫ spMap (Int.castRingHom k)) := by
    rw [flat_int_iff_charZero]
    have := hX.charZero
    have : IsDominant b := ⟨by
      rw [DenseRange, dense_iff_closure_eq, ← Set.univ_subset_iff, ← genericPoint_closure]
      exact closure_mono (Set.singleton_subset_iff.2 ⟨_, hgen⟩)⟩
    have := IsSchemeTheoreticallyDominant.of_isDominant b
    have hinj' : Function.Injective b.appTop := Scheme.Hom.app_injective b ⊤
    exact charZero_of_injective_ringHom (f := b.appTop.hom) hinj'
  exact ⟨Y, b, ⟨hX.isDomain, hX.finite, ‹_›, hproj, hflat,
    DimCover.topologicalKrullDim_eq k X Y p (b ≫ p) D hX hproj hflat b rfl hgen hdeg⟩, hb.1, hiso⟩

end GlobalTheory.BlowArith

namespace GlobalTheory.ArLieBase

end GlobalTheory.ArLieBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangePullSumMulPointValueEqStatement
section
theorem GlobalTheory.T.baseChangePull_sum_mul_pointValue_eq :
    type_of% (@GlobalTheory.PtExt.bcPull_sumMul_fv) :=
  @GlobalTheory.PtExt.bcPull_sumMul_fv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgebraPullbackTwoVariablesResCocycleEqStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.bialgebraPullbackTwoVariables_res_cocycle_eq
    (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (n : ℕ) :
    pullbackTwo (G.res n) (d.coc (n + 1)) = d.coc n :=
  Dat.pullTwo_res_coc R A p G t c d n
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterGroupSubsingletonOfBoundedRamificationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterGroup_subsingleton_of_bounded_ramification : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (D : DegData W (maximalIdeal W)) (Q : PolAV (Sp (FractionRing W))) (H : Over (Sp W)) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ U : Unif (maximalIdeal W) D Q H, GlobalTheory.LN.ToATotal U.toUnifPre → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing W) F] (n N : ℕ), 2 ≤ n → (∀ j : ℕ, ∃ (T : Subring F) (_ : IsDiscreteValuationRing T) (g : W →+* T) (e : ℕ), (∀ w, (g w : F) = algebraMap (FractionRing W) F (algebraMap W _ w)) ∧ 1 ≤ e ∧ e ≤ N ∧ (∀ π, Irreducible π → ∃ ϖ : T, Irreducible ϖ ∧ Associated (g π) (ϖ ^ e)) ∧ ∀ σ : F ≃+* F, (∀ z ∈ T, σ z = z) → ∀ x : TF (R := W) F ⟶ H, x ^ (n ^ j) = 1 → spMap σ.toRingHom ≫ x.left = x.left) → Subsingleton D.toPre.X := by
  first | exact @GlobalTheory.TorsRam.subsingleton_of_bounded_ramification | exact GlobalTheory.TorsRam.subsingleton_of_bounded_ramification | (intros; apply GlobalTheory.TorsRam.subsingleton_of_bounded_ramification <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompLinearEquivIntertwiningStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comp_linearEquiv_intertwining : ∀ (O : Type) [Ring O] (bar : O → O) (D : PLat O bar) (g : ℕ) (ρ ρ₂ : O →+* Matrix (Fin g) (Fin g) ℂ) (P : D.La →+ (Fin g → ℂ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), IsPeriod D ρ P → (∀ a z, h (ρ a *ᵥ z) = ρ₂ a *ᵥ h z) → IsPeriod D ρ₂ (h.toLinearMap.toAddMonoidHom.comp P) := by
  first | exact @GlobalTheory.PELU.IsPeriod.comp_linearEquiv | exact GlobalTheory.PELU.IsPeriod.comp_linearEquiv | (intros; apply GlobalTheory.PELU.IsPeriod.comp_linearEquiv <;> assumption)
end

