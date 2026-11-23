module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIncidenceZeroLocus

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeSheetAreaLintegral
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Filter Topology Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre segre)

open scoped ENNReal

theorem gramVol_congr {e n : ℕ} {v v' : (Fin e → ℂ) → (Fin n → ℂ)} {y : Fin e → ℂ}
    (h : v =ᶠ[𝓝 y] v') : gramVol v y = gramVol v' y := by
  unfold gramVol
  rw [h.eq_of_nhds, h.fderiv_eq]

def gramForm {e n : ℕ} (p : (Fin n → ℂ) × ((Fin e → ℂ) →L[ℂ] (Fin n → ℂ))) : ℝ :=
  let w : Fin (e + 1) → Fin n → ℂ := Fin.cons p.1 fun j => p.2 (Pi.single j 1)
  (Matrix.det (Matrix.of fun a b => ∑ i, star (w a i) * w b i)).re

theorem gramVol_eq_gramForm {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (y : Fin e → ℂ) :
    gramVol v y = gramForm (v y, fderiv ℂ v y) := rfl

theorem continuous_gramForm {e n : ℕ} :
    Continuous (gramForm : (Fin n → ℂ) × ((Fin e → ℂ) →L[ℂ] (Fin n → ℂ)) → ℝ) := by
  have hw : Continuous fun p : (Fin n → ℂ) × ((Fin e → ℂ) →L[ℂ] (Fin n → ℂ)) =>
      (Fin.cons p.1 fun j => p.2 (Pi.single j 1) : Fin (e + 1) → Fin n → ℂ) := by
    refine continuous_pi fun a => ?_
    refine Fin.cases ?_ (fun j => ?_) a
    · simpa using continuous_fst
    · simpa using continuous_snd.clm_apply continuous_const
  refine Complex.continuous_re.comp (Continuous.matrix_det ?_)
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.of_apply]
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((continuous_apply i).comp ((continuous_apply a).comp hw)).star.mul
    ((continuous_apply i).comp ((continuous_apply b).comp hw))

theorem aemeasurable_coneTerm {e n : ℕ} {U D : Set (Fin e → ℂ)} {v : (Fin e → ℂ) → (Fin n → ℂ)}
    {F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞} (hU : IsOpen U) (hDU : D ⊆ U)
    (hv : DifferentiableOn ℂ v U) (hF : Measurable F) :
    AEMeasurable (fun x => ∫⁻ t : ℂ, F (t • WithLp.toLp 2 (v x)) *
      ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol v x)) (volume.restrict D) := by
  have ha : AEMeasurable v (volume.restrict D) :=
    (hv.continuousOn.aemeasurable hU.measurableSet).mono_measure (Measure.restrict_mono hDU le_rfl)
  have hg : AEMeasurable (fun x => gramVol v x) (volume.restrict D) := by
    have h := continuous_gramForm.measurable.comp_aemeasurable
      (ha.prodMk (measurable_fderiv ℂ v).aemeasurable)
    simpa only [Function.comp_def, ← gramVol_eq_gramForm] using h
  have hmeas : Measurable fun p : (Fin e → ℂ) × ℂ => F (p.2 • WithLp.toLp 2 (ha.mk v p.1)) *
      ENNReal.ofReal (‖p.2‖ ^ (2 * e) * hg.mk _ p.1) := by
    refine (hF.comp (measurable_snd.smul ((PiLp.continuous_toLp 2 _).measurable.comp
      (ha.measurable_mk.comp measurable_fst)))).mul ?_
    exact ENNReal.measurable_ofReal.comp
      ((measurable_snd.norm.pow_const _).mul (hg.measurable_mk.comp measurable_fst))
  refine ⟨_, hmeas.lintegral_prod_right' (ν := (volume : Measure ℂ)), ?_⟩
  filter_upwards [ha.ae_eq_mk, hg.ae_eq_mk] with x h1 h2
  simp only [h1, h2]

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIncIdealNeBotDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem IncIdealNeBotDim.proof (h₁ : IncIdealDim.Statement) : IncIdealNeBotDim.Statement := by
  intro F _ n k Q hQ hI
  have := hQ.isPrime
  obtain ⟨j, -⟩ := hQ.isRelevant
  have hn : 0 < n := j.pos

  have hle : ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) ≤ ((n : ℕ) : WithBot ℕ∞) := by
    have h := ringKrullDim_le_of_surjective (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
    rwa [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = ((m : ℕ) : WithBot ℕ∞) := by
    have hbot : ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) ≠ ⊥ :=
      ne_bot_of_le_ne_bot (by simp) ringKrullDim_nonneg_of_nontrivial
    generalize ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = D at hle hbot ⊢
    induction D using WithBot.recBotCoe with
    | bot => exact absurd rfl hbot
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        exfalso
        have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hle
        exact ENat.natCast_ne_top n (top_le_iff.mp (WithBot.coe_le_coe.mp h'))
      | coe m => exact ⟨m, rfl⟩
  have hm1 : 1 ≤ m := one_le_of_isProjPrime hQ hm
  rw [hm]
  by_contra hlt
  have hkm : k < m := by
    by_contra h
    exact hlt (by exact_mod_cast Nat.le_of_not_lt h)

  have hdim := h₁ F n k (m - 1) Q hQ (by rw [Nat.sub_add_cancel hm1]; exact hm)
  have hmin : min k (m - 1) = k := min_eq_left (by omega)
  have hkn : k ≤ k * n := Nat.le_mul_of_pos_right k hn
  rw [hmin, Nat.sub_add_cancel hkn] at hdim

  obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hgnz : g ∈ nonZeroDivisors (MvPolynomial (Fin k × Fin n) F) := mem_nonZeroDivisors_of_ne_zero hg0
  have h2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hgnz
  have h3 : ringKrullDim (MvPolynomial (Fin k × Fin n) F ⧸ incIdeal Q k) ≤
      ringKrullDim (MvPolynomial (Fin k × Fin n) F ⧸ Ideal.span {g}) :=
    ringKrullDim_le_of_surjective
      (Ideal.Quotient.factor ((Ideal.span_singleton_le_iff_mem _).mpr hg))
      (Ideal.Quotient.factor_surjective _)
  have hS : ringKrullDim (MvPolynomial (Fin k × Fin n) F) = ((k * n : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, zero_add]
  rw [hdim] at h3
  rw [hS] at h2
  have h4 : (((k * n : ℕ) : WithBot ℕ∞)) + 1 ≤ ((k * n : ℕ) : WithBot ℕ∞) :=
    le_trans (add_le_add h3 le_rfl) h2
  have h5 : ((k * n + 1 : ℕ) : WithBot ℕ∞) ≤ ((k * n : ℕ) : WithBot ℕ∞) := by exact_mod_cast h4
  have h6 : k * n + 1 ≤ k * n := by exact_mod_cast h5
  omega

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIncIdealSeparate
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem IncIdealSeparate.proof (hZ : IncidenceZeroLocus.Statement) (hT : FormsThroughPoint.Statement)
    (hD : IncIdealNeBotDim.Statement) : IncIdealSeparate.Statement := by
  intro F _ n k P Q hP hQ hne hle q hqQ
  by_contra hqP
  have := hP.isPrime

  obtain ⟨φ, hφ⟩ : ∃ φ : (MvPolynomial (Fin n) F ⧸ P) →ₐ[F] AlgebraicClosure F,
      φ (Ideal.Quotient.mk P q) ≠ 0 := by
    by_contra h
    push Not at h
    exact hqP (Ideal.Quotient.eq_zero_iff_mem.mp
      (FGNullstellensatz.proof F (MvPolynomial (Fin n) F ⧸ P) (Ideal.Quotient.mk P q) h))
  let x : Fin n → AlgebraicClosure F := fun j => φ (Ideal.Quotient.mk P (X j))
  have hev : ∀ g, aeval x g = φ (Ideal.Quotient.mk P g) := by
    intro g
    have h : (aeval x : MvPolynomial (Fin n) F →ₐ[F] AlgebraicClosure F) =
        φ.comp (Ideal.Quotient.mkₐ F P) := by
      ext j
      simp [x]
    rw [h]
    rfl
  have hxq : aeval x q ≠ 0 := by rw [hev]; exact hφ
  have hx0 : x ≠ 0 := by
    intro h0
    apply hxq
    have hc : constantCoeff q = 0 := by
      by_contra hc
      have hmem := hQ.isHomog q hqQ 0
      rw [homogeneousComponent_zero, ← constantCoeff_eq] at hmem
      exact hQ.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem ((Ne.isUnit hc).map C))
    rw [h0, aeval_zero, hc, map_zero]

  obtain ⟨u, hux, huQ⟩ := hT F n k Q hQ (hD F n k Q hQ hne) x hx0 ⟨q, hqQ, hxq⟩
  apply huQ
  refine hZ F n k Q hQ.isHomog (AlgebraicClosure F) u fun g hg => ?_
  have hgP := hle hg
  simp only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hgP
  refine hgP u ⟨x, hx0, fun g' hg' => ?_, hux⟩
  rw [hev, Ideal.Quotient.eq_zero_iff_mem.mpr hg', map_zero]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PLocalSectionLengthSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module Submodule
open scoped Pointwise

namespace LocalSectionLengthSum

theorem length_quot_smul_top_eq {B : Type*} [CommRing B] (I : Ideal B) (f : B) :
    Module.length B ((B ⧸ I) ⧸ (f • ⊤ : Submodule B (B ⧸ I))) =
      Module.length B (B ⧸ (I ⊔ Ideal.span {f})) := by
  let g : B →ₗ[B] (B ⧸ I) ⧸ (f • ⊤ : Submodule B (B ⧸ I)) :=
    (f • ⊤ : Submodule B (B ⧸ I)).mkQ ∘ₗ I.mkQ
  have hg : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)
  have hker : LinearMap.ker g = I ⊔ Ideal.span {f} := by
    ext x
    simp only [g, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, mkQ_apply,
      Quotient.mk_eq_zero, mem_smul_pointwise_iff_exists, mem_top, true_and]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, smul_eq_mul] at hy
      have hx : x = f * b - (f * b - x) := by ring
      rw [hx]
      exact sub_mem (mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)))
        (mem_sup_left hy)
    · intro hx
      obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.mp hx
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hz
      refine ⟨Submodule.Quotient.mk a, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, smul_eq_mul]
      have h : f * a - (y + a * f) = -y := by ring
      rw [h]
      exact neg_mem hy
  rw [← hker, (g.quotKerEquivOfSurjective hg).length_eq]

theorem length_pi_quot_smul_top_eq {B ι : Type*} [CommRing B] [Fintype ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module B (M i)] (f : B) :
    Module.length B ((Π i, M i) ⧸ (f • ⊤ : Submodule B (Π i, M i))) =
      ∑ i, Module.length B (M i ⧸ (f • ⊤ : Submodule B (M i))) := by
  let g : (Π i, M i) →ₗ[B] (Π i, M i ⧸ (f • ⊤ : Submodule B (M i))) :=
    LinearMap.pi fun i => (f • ⊤ : Submodule B (M i)).mkQ ∘ₗ LinearMap.proj i
  have hg : Function.Surjective g := by
    intro y
    choose x hx using fun i => Submodule.Quotient.mk_surjective _ (y i)
    exact ⟨x, funext fun i => by simp [g, hx i]⟩
  have hker : LinearMap.ker g = f • ⊤ := by
    ext x
    simp only [LinearMap.mem_ker, mem_smul_pointwise_iff_exists, mem_top, true_and]
    constructor
    · intro h
      have hx : ∀ i, ∃ y : M i, f • y = x i := fun i => by
        have h' := congrFun h i
        simpa [g, mem_smul_pointwise_iff_exists] using h'
      choose y hy using hx
      exact ⟨y, funext hy⟩
    · rintro ⟨y, rfl⟩
      funext i
      exact (Quotient.mk_eq_zero _).mpr (smul_mem_pointwise_smul (y i) f ⊤ mem_top)
  rw [← hker, (g.quotKerEquivOfSurjective hg).length_eq, Module.length_pi_of_fintype]

end LocalSectionLengthSum

theorem LocalSectionLengthSum.proof (hPi : PiQuotCokerFiniteLength.Statement) :
    LocalSectionLengthSum.Statement := by
  intro B _ _ _ J f hJ hf hQ
  obtain ⟨hinj, hfin⟩ := hPi B J hJ hQ
  have hfinite := J.finite_minimalPrimes_of_isNoetherianRing B
  let _ : Fintype J.minimalPrimes := hfinite.fintype
  have hreg : Function.Injective fun x : ((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) => f • x := by
    intro x y hxy
    funext P
    have : (P : Ideal B).IsPrime := P.2.1.1
    have h : f • x P = f • y P := congrFun hxy P
    rw [Algebra.smul_def, Algebra.smul_def] at h
    refine mul_left_cancel₀ ?_ h
    rw [Ne, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hf P P.2
  have e1 := Model.TorsionFreeQuotientLength.length_quot_smul_eq (quotToPiMinimalPrimes J) hinj
    hreg hfin
  rw [← LocalSectionLengthSum.length_quot_smul_top_eq J f, ← e1,
    LocalSectionLengthSum.length_pi_quot_smul_top_eq]
  simp_rw [LocalSectionLengthSum.length_quot_smul_top_eq]
  exact (Finset.sum_subtype (p := (· ∈ J.minimalPrimes)) hfinite.toFinset
    (fun P => hfinite.mem_toFinset)
    (fun P : Ideal B => Module.length B (B ⧸ (P ⊔ Ideal.span {f})))).symm

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PProjChowNonzero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ProjChowNonzero

theorem aeval_smul_of_isHomogeneous {Ω : Type*} [Field Ω] [Algebra ℂ Ω] {n m : ℕ}
    {φ : MvPolynomial (Fin n) ℂ} (hφ : φ.IsHomogeneous m) (c : Ω) (x : Fin n → Ω) :
    aeval (c • x) φ = c ^ m * aeval x φ := by
  simp only [aeval_def, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg := hφ.degree_eq_sum_deg_support hd
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hdeg]
  ring

theorem aeval_smul_eq_zero {Ω : Type*} [Field Ω] [Algebra ℂ Ω] {n : ℕ}
    {W : Ideal (MvPolynomial (Fin n) ℂ)} (hW : IsHomogIdeal W) {x : Fin n → Ω}
    (hx : ∀ q ∈ W, aeval x q = 0) (c : Ω) : ∀ q ∈ W, aeval (c • x) q = 0 := by
  intro q hq
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← sum_homogeneousComponent q, map_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [aeval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous d q), hx _ (hW q hq d), mul_zero]

theorem eq_zero_of_isFiniteProjection {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [Algebra ℂ Ω] {n d : ℕ}
    {W : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} (hW : IsHomogIdeal W)
    (hA : ComplexSets.IsFiniteProjection W A) {x : Fin n → Ω} (hx : ∀ q ∈ W, aeval x q = 0)
    (hAx : ∀ i, aeval x (ComplexSets.linPoly A i) = 0) : x = 0 := by
  funext j
  by_contra hj
  obtain ⟨p, hpm, hp⟩ := hA.finite.to_isIntegral (Ideal.Quotient.mk W (X j))
  set q := Polynomial.eval₂ (ComplexSets.pullback A).toRingHom (X j) p with hq_def
  have hq : q ∈ W := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hq_def, Polynomial.hom_eval₂]
    exact hp

  set ψ : MvPolynomial (Fin d) ℂ →+* Ω := (algebraMap ℂ Ω).comp (eval 0) with hψ
  have hcomp : ∀ c : Ω, ((aeval (c • x) : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Ω) : MvPolynomial (Fin n) ℂ →+* Ω).comp
      (ComplexSets.pullback A).toRingHom = ψ := by
    intro c
    refine MvPolynomial.ringHom_ext (fun a => by simp [hψ, ComplexSets.pullback]) fun i => ?_
    have h1 := aeval_smul_of_isHomogeneous (Ω := Ω) (m := 1) ?_ c x (φ := ComplexSets.linPoly A i)
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        ComplexSets.pullback, aeval_X, hψ, eval_X, Pi.zero_apply, map_zero]
      rw [h1, hAx i, mul_zero]
    · exact IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_C_mul_X _ _)
  have hroot : ∀ c : Ω, (p.map ψ).eval (c * x j) = 0 := by
    intro c
    have h := aeval_smul_eq_zero hW hx c q hq
    rw [hq_def, ← AlgHom.coe_toRingHom, Polynomial.hom_eval₂, hcomp c] at h
    simpa [Polynomial.eval_map] using h
  have hzero : p.map ψ = 0 := Polynomial.funext fun r => by
    have := hroot (r / x j)
    rw [div_mul_cancel₀ r hj] at this
    simpa using this
  exact (hpm.map ψ).ne_zero hzero

theorem aeval_ne_zero_of_not_incidence {n k : ℕ} {W : Ideal (MvPolynomial (Fin n) ℂ)}
    {f : MvPolynomial (Fin k × Fin n) ℂ} (hW : IsHomogIdeal W) (hf : IsChowForm W k f)
    (v : Fin k × Fin n → AlgebraicClosure ℂ)
    (hv : ∀ y : Fin n → AlgebraicClosure ℂ, (∀ q ∈ W, aeval y q = 0) →
      (∀ i, ∑ j, v (i, j) * y j = 0) → y = 0) :
    aeval v f ≠ 0 := by
  intro h0
  have hinc : ∀ g ∈ incIdeal W k, aeval v g = 0 := by
    intro g hg
    have hmem : ∀ u ∈ incidence W k, aeval u g = 0 := by
      simpa only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker] using hg
    obtain ⟨h, rfl⟩ := (hf.2 g).mp hmem
    rw [map_mul, h0, zero_mul]
  obtain ⟨y, hy0, hyW, hyv⟩ := IncidenceZeroLocus.proof ℂ n k W hW (AlgebraicClosure ℂ) v hinc
  exact hy0 (hv y hyW hyv)

abbrev Loc (e : ℕ) : Type := Localization.Away (X 0 : MvPolynomial (Fin (e + 1)) ℂ)

theorem projVar_zero_ne (e : ℕ) : projVar e 0 ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Fin (e + 1)) ℂ) _)).mpr (X_ne_zero 0)

def toK (e : ℕ) : Loc e →+* FractionRing (MvPolynomial (Fin (e + 1)) ℂ) :=
  IsLocalization.Away.lift (X 0) (g := algebraMap _ _) (IsUnit.mk0 _ (projVar_zero_ne e))

def pt (e : ℕ) : Fin (e + 1) → ℂ := fun i => if i = 0 then 1 else 0

def atPt (e : ℕ) : Loc e →+* AlgebraicClosure ℂ :=
  IsLocalization.Away.lift (X 0) (g := (algebraMap ℂ (AlgebraicClosure ℂ)).comp (eval (pt e)))
    (by simp [pt])

def locPar {n e : ℕ} (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (ij : Fin (e + 1) × Fin n) : Loc e :=
  Fin.cases (motive := fun _ => Loc e)
    (algebraMap ℂ (Loc e) (A 0 ij.2) * IsLocalization.Away.invSelf (X 0 : MvPolynomial (Fin (e + 1)) ℂ))
    (fun i => algebraMap (MvPolynomial (Fin (e + 1)) ℂ) (Loc e)
      (X i.succ * C (A 0 ij.2) - X 0 * C (A i.succ ij.2))) ij.1

theorem toK_injective (e : ℕ) : Function.Injective (toK e) := by
  have h1 : Function.Injective (algebraMap (MvPolynomial (Fin (e + 1)) ℂ) (Loc e)) :=
    IsLocalization.injective (Loc e) (powers_le_nonZeroDivisors_of_noZeroDivisors (X_ne_zero 0))
  have h2 := IsFractionRing.injective (MvPolynomial (Fin (e + 1)) ℂ)
    (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))
  exact (IsLocalization.lift_injective_iff _).mpr fun a b => h1.eq_iff.trans h2.eq_iff.symm

theorem toK_invSelf (e : ℕ) :
    toK e (IsLocalization.Away.invSelf (X 0 : MvPolynomial (Fin (e + 1)) ℂ)) = (projVar e 0)⁻¹ := by
  have h := congrArg (toK e) (IsLocalization.Away.mul_invSelf (S := Loc e) (X 0 : MvPolynomial (Fin (e + 1)) ℂ))
  rw [map_mul, map_one, toK, IsLocalization.Away.lift_eq] at h
  exact (eq_inv_of_mul_eq_one_right h)

theorem atPt_invSelf (e : ℕ) :
    atPt e (IsLocalization.Away.invSelf (X 0 : MvPolynomial (Fin (e + 1)) ℂ)) = 1 := by
  have h := congrArg (atPt e) (IsLocalization.Away.mul_invSelf (S := Loc e) (X 0 : MvPolynomial (Fin (e + 1)) ℂ))
  rw [map_mul, map_one] at h
  unfold atPt at h ⊢
  rw [IsLocalization.Away.lift_eq] at h
  simpa [pt] using h

theorem toK_algebraMap (e : ℕ) (a : ℂ) :
    toK e (algebraMap ℂ (Loc e) a) = algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) a := by
  rw [IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin (e + 1)) ℂ) (Loc e), toK,
    IsLocalization.Away.lift_eq, ← IsScalarTower.algebraMap_apply]

theorem atPt_algebraMap (e : ℕ) (a : ℂ) :
    atPt e (algebraMap ℂ (Loc e) a) = algebraMap ℂ (AlgebraicClosure ℂ) a := by
  rw [IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin (e + 1)) ℂ) (Loc e), atPt,
    IsLocalization.Away.lift_eq]
  simp

theorem value_eq {n e : ℕ} (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) :
    eval (fun j => projPar A (.inr j))
        (Vertical.specRest (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))) f (projPar A)) =
      toK e (aeval (locPar A) f) := by
  rw [Vertical.specRest, eval₂_comp_left, aeval_def, eval₂_comp_left]
  congr 1
  · ext a
    simp [toK_algebraMap]
  · funext ⟨i, j⟩
    cases i using Fin.cases with
    | zero => simp [locPar, projPar, map_mul, toK_algebraMap, toK_invSelf, div_eq_mul_inv]
    | succ i =>
      simp [locPar, projPar, toK, IsLocalization.Away.lift_eq, projVar,
        IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin (e + 1)) ℂ)
          (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)), mul_comm]

theorem atPt_aeval {n e : ℕ} (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) :
    atPt e (aeval (locPar A) f) =
      aeval (fun ij : Fin (e + 1) × Fin n => Fin.cases (motive := fun _ => AlgebraicClosure ℂ)
        (algebraMap ℂ _ (A 0 ij.2)) (fun i => -algebraMap ℂ _ (A i.succ ij.2)) ij.1) f := by
  rw [aeval_def, eval₂_comp_left, aeval_def]
  congr 1
  · ext a
    simp [atPt_algebraMap]
  · funext ⟨i, j⟩
    cases i using Fin.cases with
    | zero => simp [locPar, atPt_algebraMap, atPt_invSelf]
    | succ i => simp [locPar, atPt, IsLocalization.Away.lift_eq, pt, Fin.succ_ne_zero]

end ProjChowNonzero

theorem ProjChowNonzero.proof : ProjChowNonzero.Statement := by
  intro n e W f A hW hf hA
  rw [ProjChowNonzero.value_eq]
  intro h0
  have h1 : aeval (ProjChowNonzero.locPar A) f = 0 :=
    (map_eq_zero_iff _ (ProjChowNonzero.toK_injective e)).mp h0
  have h2 := congrArg (ProjChowNonzero.atPt e) h1
  rw [map_zero, ProjChowNonzero.atPt_aeval] at h2
  refine ProjChowNonzero.aeval_ne_zero_of_not_incidence hW.isHomog hf _ (fun y hyW hyv => ?_) h2
  refine ProjChowNonzero.eq_zero_of_isFiniteProjection hW.isHomog hA hyW fun i => ?_
  have hi := hyv i
  cases i using Fin.cases with
  | zero => simpa [ComplexSets.linPoly] using hi
  | succ i =>
    simp only [Fin.cases_succ, neg_mul, Finset.sum_neg_distrib, neg_eq_zero] at hi
    simpa [ComplexSets.linPoly] using hi

end

end GroundTheory.Heights₂.Heights
end

