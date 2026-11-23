module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.UnipotentAdelicQuotients.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIntegralSplitIdempotentOverTwo
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitIdem

theorem idem_alg {T : Type} [CommRing T] (p U R w m : T) (hU : p * U = U) (hR : R * R - R + m * p = 0)
    (hδ : U - 2 * (U * R) = p) (hw : w * w - w + m = 0) :
    (U * w - U * R) * (U * w - U * R) = U * w - U * R ∧
      (U * w - U * R) * (U * (1 - w) - U * R) = 0 ∧
      (U * w - U * R) + (U * (1 - w) - U * R) = p := by
  have h2 : (U * w - U * R) * (U * (1 - w) - U * R) = 0 := by
    linear_combination U * U * hR - U * U * hw - m * U * hU
  refine ⟨?_, h2, by linear_combination hδ⟩
  linear_combination (U * w - U * R) * hδ - h2 + (w - R) * hU

theorem idem_tensor {F A E K : Type} [Field F] [CommRing A] [Algebra F A] [CommRing E] [Algebra F E]
    [CommRing K] (φ : K →ₙ+* A) (c : A ⊗[F] E →+* A ⊗[F] E) (ω : E) (m : ℕ) (r u : K)
    (hc1 : ∀ a : A, c (a ⊗ₜ 1) = a ⊗ₜ 1) (hcω : ∀ a : A, c (a ⊗ₜ ω) = a ⊗ₜ (1 - ω))
    (hω : ω * ω - ω + m = 0) (hr : r * r - r + m = 0) (hu : u * (1 - 2 * r) = 1)
    (e : A ⊗[F] E) (he : e = φ u ⊗ₜ ω + φ (-(u * r)) ⊗ₜ 1) :
    e * e = e ∧ e * c e = 0 ∧ e + c e = algebraMap A (A ⊗[F] E) (φ 1) := by
  let j : A →+* A ⊗[F] E := algebraMap A _
  let k : E →+* A ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] A ⊗[F] E)
  have hjk : ∀ a x, a ⊗ₜ[F] x = j a * k x := fun a x => by
    simp [j, k, Algebra.TensorProduct.tmul_mul_tmul]
  have h1 : e = j (φ u) * k ω - j (φ u) * j (φ r) := by
    rw [he, hjk, hjk, map_neg, map_mul, map_neg, map_mul, map_one]; ring
  have h2 : c e = j (φ u) * (1 - k ω) - j (φ u) * j (φ r) := by
    rw [he, map_add (f := _), hc1, hcω, hjk, hjk, map_neg, map_mul, map_neg, map_mul, map_one, map_sub, map_one]; ring
  rw [h2, h1]
  refine idem_alg (j (φ 1)) _ _ _ (m : A ⊗[F] E) ?_ ?_ ?_ ?_
  · rw [← map_mul, ← map_mul, one_mul]
  · have : φ r * φ r - φ r + m * φ 1 = 0 := by
      rw [← nsmul_eq_mul, ← map_nsmul, ← map_mul, ← map_sub, ← map_add (f := _), nsmul_eq_mul, mul_one, hr, map_zero]
    simpa using congrArg j this
  · have : φ u - 2 * (φ u * φ r) = φ 1 := by
      rw [two_mul, ← map_mul, ← map_add (f := _), ← map_sub, ← hu]; congr 1; ring
    have h := congrArg j this
    rwa [map_sub, map_mul, map_mul, map_ofNat] at h
  · have h := congrArg k hω
    rwa [map_add, map_sub, map_mul, map_natCast, map_zero] at h

section Local

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem evalV_singleV_same (y : Fv F v) : evalV F v (singleV F v y) = y := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y

theorem evalV_singleV_ne (y : Fv F v) {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    evalV F w (singleV F v y) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) y hw

theorem af_ext {a b : Af F} (h : ∀ w, evalV F w a = evalV F w b) : a = b :=
  RestrictedProduct.ext _ _ h

def placeHom : Fv F v →ₙ+* AF F where
  toFun y := pairA F 0 (singleV F v y)
  map_zero' := Prod.ext rfl (af_ext F fun w => by
    change evalV F w (singleV F v 0) = evalV F w 0
    by_cases hw : w = v
    · subst hw; rw [evalV_singleV_same, map_zero]
    · rw [evalV_singleV_ne F v _ hw, map_zero])
  map_add' x y := Prod.ext (add_zero _).symm (af_ext F fun w => by
    change evalV F w (singleV F v (x + y)) = evalV F w (singleV F v x + singleV F v y)
    by_cases hw : w = v
    · subst hw; simp only [map_add (f := _), evalV_singleV_same]
    · simp only [map_add (f := _), evalV_singleV_ne F v _ hw, add_zero])
  map_mul' x y := Prod.ext (mul_zero _).symm (af_ext F fun w => by
    change evalV F w (singleV F v (x * y)) = evalV F w (singleV F v x * singleV F v y)
    by_cases hw : w = v
    · subst hw; simp only [map_mul, evalV_singleV_same]
    · simp only [map_mul, evalV_singleV_ne F v _ hw, mul_zero])

theorem singleV_mem_intAf (y : v.adicCompletionIntegers F) : singleV F v (y : Fv F v) ∈ intAf F := fun w => by
  by_cases hw : w = v
  · subst hw; rw [evalV_singleV_same]; exact y.2
  · rw [evalV_singleV_ne F v _ hw]; exact zero_mem _

theorem exists_root (h2 : (2 : 𝓞 F) ∈ v.asIdeal) (k : ℕ) :
    ∃ r u : v.adicCompletionIntegers F, r * r - r + ((2 * k : ℕ) : v.adicCompletionIntegers F) = 0 ∧
      u * (1 - 2 * r) = 1 := by
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  have hm : (2 : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      ← map_ofNat (algebraMap (𝓞 F) (v.adicCompletionIntegers F)) 2, GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff]
    exact fun h => h h2
  obtain ⟨r, hr, -⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))
    (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C ((2 * k : ℕ) : v.adicCompletionIntegers F)) (by monicity!) 0
    (by simpa using Ideal.mul_mem_right _ _ hm) (by simp)
  have hunit : IsUnit (1 - 2 * r) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (Ideal.mul_mem_right r _ hm)
  obtain ⟨u, hu⟩ := hunit.exists_left_inv
  refine ⟨r, u, ?_, hu⟩
  simpa [Polynomial.IsRoot, pow_two] using hr

end Local

theorem exists_omega (D : D7) : ∃ (ω : 𝓞 D.host.E) (k : ℕ),
    (ω : D.host.E) * ω - ω + ((2 * k : ℕ) : D.host.E) = 0 ∧ D.host.conj ω = 1 - ω := by
  obtain ⟨k, hm⟩ : ∃ k : ℕ, D.host.d + 1 = 4 * (2 * k) := ⟨(D.host.d + 1) / 8, by have := D.host.hyp.2.2.2.1; omega⟩
  generalize hmm : 2 * k = m at hm
  set c : D.host.E := (1 + D.host.sqrtMinusD) / 2
  have hc : c ^ 2 - c + (m : D.host.E) = 0 := by
    have e : ((D.host.d : ℕ) : D.host.E) + 1 = 4 * (m : D.host.E) := by exact_mod_cast hm
    have hs := D.host.sqrtMinusD_sq
    simp only [c]
    linear_combination (1 / 4 : D.host.E) * hs - (1 / 4 : D.host.E) * e
  have hint : IsIntegral ℤ c := ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), by monicity!, by
    simp [Polynomial.eval₂_sub, Polynomial.eval₂_add, hc]⟩
  refine ⟨⟨c, hint⟩, k, ?_, ?_⟩
  · show c * c - c + _ = 0
    rw [hmm, ← pow_two, hc]
  · show D.host.conj c = 1 - c
    simp only [c, map_div₀, map_add (f := _), map_one, D.host.conj_sqrtMinusD, map_ofNat]
    ring

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  have h1 : D.host.φ₀ (D.host.conj x) = starRingEnd ℂ (D.host.φ₀ x) := D.host.conjE_apply _ _
  rw [h1]
  haveI := D.host.isCMField_hostE
  exact IsCMField.complexEmbedding_complexConj _ _ _

theorem exists_split_idempotent : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)), (2 : 𝓞 D.host.F) ∈ v.asIdeal → ∃ e : Formalism.L2.Theta.AE D, e * e = e ∧ e * cA D e = 0 ∧ e + cA D e = algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) ∧ ∃ α ∈ intAf D.host.F, ∃ β ∈ intAf D.host.F, ∃ ω : 𝓞 D.host.E, e = pairA D.host.F 0 α ⊗ₜ[D.host.F] (ω : D.host.E) + pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E) := by
  intro D v h2
  obtain ⟨ω, k, hω, hc⟩ := exists_omega D
  obtain ⟨r, u, hr, hu⟩ := exists_root D.host.F v h2 k
  have hcA : ∀ (a : AF D.host.F) (x : D.host.E), cA D (a ⊗ₜ[D.host.F] x) = a ⊗ₜ[D.host.F] star x := fun _ _ => rfl
  have key := idem_tensor (placeHom D.host.F v) (cA D) (ω : D.host.E) (2 * k) (r : Fv D.host.F v) (u : Fv D.host.F v)
    (fun a => by rw [hcA, star_one]) (fun a => by rw [hcA, star_eq_conj, hc]) hω
    (congrArg Subtype.val hr) (congrArg Subtype.val hu) _ rfl
  exact ⟨_, key.1, key.2.1, key.2.2, _, singleV_mem_intAf D.host.F v u, _,
    singleV_mem_intAf D.host.F v (-(u * r)), ω, rfl⟩

end GlobalTheory.SplitIdem

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsClosedZeroLocusGL
section
open NumberField IsDedekindDomain

namespace GlobalTheory.LocusOpenCompact

theorem continuous_aeval_comp {F A X σ : Type} [CommRing F] [CommRing A] [Algebra F A]
    [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace X] (f : X → σ → A)
    (hf : ∀ i, Continuous fun x => f x i) (P : MvPolynomial σ F) :
    Continuous fun x => MvPolynomial.aeval (f x) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using continuous_const
  | add p q hp hq => simp only [map_add (f := _)]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, MvPolynomial.aeval_X]; exact hp.mul (hf i)

theorem isClosed_zeroLocusGL {F : Type} [Field F] {n : ℕ}
    (S : Set (MvPolynomial (Fin n × Fin n) F)) (A : Type) [CommRing A] [Algebra F A]
    [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] :
    IsClosed (HeckeCharacterZeroLocus.zeroLocusGL S A) := by
  have e : HeckeCharacterZeroLocus.zeroLocusGL S A = ⋂ P ∈ S, {g : GL (Fin n) A | MvPolynomial.aeval
      (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) A) ij.1 ij.2) P = 0} := by
    ext g; simp only [HeckeCharacterZeroLocus.zeroLocusGL, Set.mem_iInter]; rfl
  rw [e]
  refine isClosed_biInter fun P _ => isClosed_eq ?_ continuous_const
  have hv : Continuous fun g : GL (Fin n) A => (g : Matrix (Fin n) (Fin n) A) :=
    Units.continuous_val
  exact continuous_aeval_comp (X := GL (Fin n) A)
    (fun g (ij : Fin n × Fin n) => (g : Matrix (Fin n) (Fin n) A) ij.1 ij.2)
    (fun ij => hv.matrix_elem ij.1 ij.2) P

theorem exists_isOpen_isCompact : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)) (hS : HeckeCharacterZeroLocus.IsGroupLocus S), ∃ U : Subgroup (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)), IsOpen (U : Set (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))) ∧ IsCompact (U : Set (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))) := by
  intro F _ _ n S hS
  have : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
  obtain ⟨U, hUo, hUc⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact F n
  refine ⟨U.subgroupOf _, hUo.preimage continuous_subtype_val, ?_⟩
  exact (isClosed_zeroLocusGL S (FiniteAdeleRing (𝓞 F) F)).isClosedEmbedding_subtypeVal.isCompact_preimage hUc

end GlobalTheory.LocusOpenCompact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsCompactIntegralPointsFiniteAdelicAlgebraicGrou
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.IntegralPointsCompact

theorem continuous_aeval_family {F A X σ : Type} [CommRing F] [CommRing A] [Algebra F A]
    [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace X] (f : X → σ → A)
    (hf : ∀ s, Continuous fun x => f x s) (P : MvPolynomial σ F) :
    Continuous fun x => MvPolynomial.aeval (f x) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using continuous_const
  | add p q hp hq => simp only [map_add (f := _)]; exact hp.add hq
  | mul_X p s hp => simp only [map_mul, MvPolynomial.aeval_X]; exact hp.mul (hf s)

theorem isClosed_of_equations {F A ι : Type} [CommRing F] [CommRing A] [Algebra F A]
    [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] [Fintype ι] [DecidableEq ι]
    (S : Set (MvPolynomial (ι × ι) F)) (H : Subgroup (GL ι A))
    (hH : ∀ g, g ∈ H ↔ ∀ P ∈ S, MvPolynomial.aeval
      (fun ij : ι × ι => ((g : GL ι A) : Matrix ι ι A) ij.1 ij.2) P = 0) :
    IsClosed (H : Set (GL ι A)) := by
  have e : (H : Set (GL ι A)) = ⋂ P ∈ S, {g : GL ι A | MvPolynomial.aeval
      (fun ij : ι × ι => (g : Matrix ι ι A) ij.1 ij.2) P = 0} := by
    ext g
    simp only [Set.mem_iInter, SetLike.mem_coe]
    exact hH g
  rw [e]
  refine isClosed_biInter fun P _ => isClosed_eq ?_ continuous_const
  exact continuous_aeval_family (fun (g : GL ι A) (ij : ι × ι) => (g : Matrix ι ι A) ij.1 ij.2)
    (fun s => Units.continuous_val.matrix_elem s.1 s.2) P

theorem isCompact_integral_points : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)) (H : Subgroup (GL (Fin n) (FiniteAdeleRing (𝓞 F) F))), (∀ g, g ∈ H ↔ (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0)) → IsCompact {u : H | (∀ i j, (∀ v, (((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ (∀ v, ((((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F))⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v))} := by
  intro F _ _ n S H hH
  have : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
  have hK := GlobalTheory.GLIntegral.isCompact_glSub (ι := Fin n) (GlobalTheory.GLIntegral.intSubring F)
    (GlobalTheory.AdeleCocompact.isCompact_integral F)
  have hc := isClosed_of_equations S H hH
  have h := hc.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  refine (congrArg IsCompact (Set.ext fun u => ?_)).mpr h
  exact ⟨fun hu => ⟨fun i j => (hu i j).1, fun i j => (hu i j).2⟩,
    fun hu i j => ⟨hu.1 i j, hu.2 i j⟩⟩

end GlobalTheory.IntegralPointsCompact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacUnique

open GlobalTheory.FockCompare

variable {D : D7}

def hAt (S T : HSp D) (τ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) : ℂ :=
  ((gramAt D S τ)⁻¹ * yᴴ * gramAt D T τ * x).trace

def omAt (S T : HSp D) (τ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) : ℝ :=
  2 * (tauE D τ D.host.xi0 * hAt S T τ x y).re

theorem omAt_add_left (S T : HSp D) (τ : D.what₂.Tau) (x x' y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omAt S T τ (x + x') y = omAt S T τ x y + omAt S T τ x' y := by
  simp only [omAt, hAt, Matrix.mul_add, Matrix.trace_add, mul_add, Complex.add_re]

theorem omAt_add_right (S T : HSp D) (τ : D.what₂.Tau) (x y y' : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omAt S T τ x (y + y') = omAt S T τ x y + omAt S T τ x y' := by
  simp only [omAt, hAt, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, mul_add,
    Complex.add_re]

theorem omAt_smul_left (S T : HSp D) (τ : D.what₂.Tau) (c : ℝ) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omAt S T τ (c • x) y = c * omAt S T τ x y := by
  simp only [omAt, hAt, Matrix.mul_smul, Matrix.trace_smul, mul_smul_comm, Complex.smul_re, smul_eq_mul]
  ring

theorem omAt_smul_right (S T : HSp D) (τ : D.what₂.Tau) (c : ℝ) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omAt S T τ x (c • y) = c * omAt S T τ x y := by
  simp only [omAt, hAt, Matrix.conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
    mul_smul_comm, Complex.smul_re, smul_eq_mul]
  ring

def omO (S T : HSp D) : RW T S →ₗ[ℝ] RW T S →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ τ, omAt S T τ (x τ) (y τ))
    (fun x x' y => by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun τ _ => omAt_add_left S T τ _ _ _)
    (fun c x y => by rw [smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => omAt_smul_left S T τ c _ _)
    (fun x y y' => by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun τ _ => omAt_add_right S T τ _ _ _)
    (fun c x y => by rw [smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => omAt_smul_right S T τ c _ _)

theorem omO_apply (S T : HSp D) (x y : RW T S) : omO S T x y = ∑ τ, omAt S T τ (x τ) (y τ) := rfl

theorem cplxO_add {m n : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ)
    (x y : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (x + y) = cplxO s t x + cplxO s t y := by
  simp only [cplxO, Matrix.mul_add, Matrix.add_mul, smul_add]

theorem cplxO_smul {m n : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ) (c : ℝ)
    (x : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (c • x) = c • cplxO s t x := by
  simp only [cplxO, Matrix.mul_smul, Matrix.smul_mul]
  exact smul_comm _ _ _

def jO (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) : RW T S →ₗ[ℝ] RW T S where
  toFun x := fun τ => cplxO (sS τ) (sT τ) (x τ)
  map_add' x y := by funext τ; exact cplxO_add _ _ _ _
  map_smul' c x := by funext τ; exact cplxO_smul _ _ c _

theorem jO_apply (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (x : RW T S) (τ : D.what₂.Tau) :
    jO S T sS sT x τ = cplxO (sS τ) (sT τ) (x τ) := rfl

def infRat (S T : HSp D) : Matrix (Fin T.rank) (Fin S.rank) D.host.E →+ RW T S where
  toFun γ := fun τ i j => tauE D τ (γ i j)
  map_zero' := by funext τ i j; exact (tauE D τ).map_zero
  map_add' x y := by funext τ i j; exact (tauE D τ).map_add _ _

def finRat (S T : HSp D) : Matrix (Fin T.rank) (Fin S.rank) D.host.E →+ WO S T where
  toFun γ := Matrix.of fun i j => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (γ i j)
  map_zero' := by funext i j; exact TensorProduct.tmul_zero _ _
  map_add' x y := by funext i j; exact TensorProduct.tmul_add _ _ _

theorem finRat_inf (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (finRat S T γ).map (infPart D) = 0 := by
  funext i j
  show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (γ i j) = 0
  exact TensorProduct.zero_tmul _ _

theorem finRat_fin (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (finRat S T γ).map (finPart D) = (ratW T S γ).map (finPart D) := rfl

theorem piW_of_inf (θ : InfFam D) {S T : HSp D} {u : WO S T} (hu : u.map (infPart D) = 0) :
    piW θ T S u = 0 := by
  funext τ i j
  have : infPart D (u i j) = 0 := congrFun (congrFun hu i) j
  show θ τ (infPart D (u i j)) = 0
  rw [this, RingHom.map_zero]

theorem piW_ratW {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : piW θ T S (ratW T S γ) = infRat S T γ := by
  funext τ i j
  exact comp_incA hθ τ _

theorem ratW_eq {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ) (S T : HSp D)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ratW T S γ = iotaW σ T S (infRat S T γ) + finRat S T γ := by
  have e : (ratW T S γ - finRat S T γ : WA T S) = iotaW σ T S (infRat S T γ) := by
    refine h.real_ext ?_ (h.real_iota T S _) ?_
    · funext i j
      have e1 : finPart D (finRat S T γ i j) = finPart D (ratW T S γ i j) := rfl
      show finPart D (ratW T S γ i j - finRat S T γ i j) = 0
      rw [RingHom.map_sub, e1, sub_self]
    · rw [AddMonoidHom.map_sub, piW_of_inf θ (finRat_inf S T γ), piW_ratW h.inf, h.pi_iota, sub_zero]
  exact sub_eq_iff_eq_add.1 e

theorem latO_inf (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) {u : WO S T} (hu : u ∈ latO S T LS LT P) :
    u.map (infPart D) = 0 := by
  have : latO S T LS LT P ≤ ((infPart D).toAddMonoidHom.mapMatrix (m := Fin T.rank) (n := Fin S.rank)).ker := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, -, -, a, -, s, -, t, -, rfl⟩
    funext i j
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] _ = 0
    exact TensorProduct.zero_tmul _ _
  exact this hu

end GlobalTheory.VacUnique

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OneEqSumPlaceIdempotentsOverTwoAddTwoMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatVac

theorem evalV_singleV_same (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    evalV F v (singleV F v 1) = 1 := by
  classical
  exact RestrictedProduct.single_eq_same
    (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v 1

theorem evalV_singleV_ne (F : Type) [Field F] [NumberField F] (v v' : HeightOneSpectrum (𝓞 F))
    (h : v' ≠ v) : evalV F v' (singleV F v 1) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne
    (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) 1 h

theorem half_mem_adicCompletionIntegers (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (h : (2 : 𝓞 F) ∉ v.asIdeal) : algebraMap F (Fv F v) (2 : F)⁻¹ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.valuation F (algebraMap (𝓞 F) F 2) = 1 := (v.valuation_eq_one_iff_notMem (K := F)).2 h
  rw [map_ofNat] at h1
  have h2 : Valued.v (algebraMap F (Fv F v) (2 : F)⁻¹) = v.valuation F (2 : F)⁻¹ :=
    v.valuedAdicCompletion_eq_valuation' _
  rw [h2, map_inv₀, h1, inv_one]

theorem one_eq_sum_singleV_add_two_mul : ∀ (F : Type) [Field F] [NumberField F], ∃ P : Finset (HeightOneSpectrum (𝓞 F)), (∀ v ∈ P, (2 : 𝓞 F) ∈ v.asIdeal) ∧ (∀ v : HeightOneSpectrum (𝓞 F), singleV F v 1 ∈ intAf F ∧ evalV F v (singleV F v 1) = 1 ∧ ∀ v', v' ≠ v → evalV F v' (singleV F v 1) = 0) ∧ ∃ β ∈ intAf F, (1 : Af F) = ∑ v ∈ P, singleV F v 1 + 2 * β := by
  intro F _ _
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | (2 : 𝓞 F) ∈ v.asIdeal}.Finite := by
    have h := Ideal.finite_factors (I := Ideal.span {(2 : 𝓞 F)}) (by simp)
    refine h.subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  refine ⟨hfin.toFinset, fun v hv => by simpa using hv, fun v => ⟨fun w => ?_, evalV_singleV_same F v,
    evalV_singleV_ne F v⟩, algebraMap F (Af F) (2 : F)⁻¹ * (1 - ∑ v ∈ hfin.toFinset, singleV F v 1),
    fun w => ?_, ?_⟩
  · by_cases hw : w = v
    · subst hw
      rw [evalV_singleV_same]; exact one_mem _
    · rw [evalV_singleV_ne F v w hw]; exact zero_mem _
  · set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, map_sub, map_one, map_sum, AlgHom.commutes]
    by_cases hw : w ∈ hfin.toFinset
    · rw [Finset.sum_eq_single_of_mem w hw fun b _ hb => evalV_singleV_ne F b w hb.symm,
        evalV_singleV_same, sub_self, mul_zero]
      exact zero_mem _
    · rw [Finset.sum_eq_zero fun b hb => evalV_singleV_ne F b w fun h => hw (h ▸ hb), sub_zero, mul_one]
      exact half_mem_adicCompletionIntegers F w (by simpa using hw)
  · have h2 : (2 : Af F) * algebraMap F (Af F) (2 : F)⁻¹ = 1 := by
      rw [← map_ofNat (algebraMap F (Af F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
    rw [← mul_assoc, h2, one_mul, add_sub_cancel]

end GlobalTheory.LatVac
end

