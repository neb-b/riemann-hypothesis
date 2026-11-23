module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0045
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0058
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0044
public import Formalism.FlagUnipotentLattices.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardFrameGramDetNeZero
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.FrameGram

theorem std_frame_gram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → (gramE σ J (tupH P)).det ≠ 0 ∧ (∀ i j, σ (gramE σ J (tupH P) j i) = gramE σ J (tupH P) i j) ∧ (∀ i j, σ (gramE σ J (F0 P) j i) = gramE σ J (F0 P) i j) ∧ (∀ i j, gramE σ J (F0 P) i j = if i = Fin.last r ∧ j = Fin.last r then algebraMap F E (-T) else 0) ∧ ∀ v : HeightOneSpectrum (𝓞 F), LinearIndependent (Fv F v ⊗[F] E) (ratTup (F := F) (Fv F v) (F0 P)) := by
  intro F E _ _ _ _ _ σ hσ n J hJ r P T hP
  obtain ⟨he, _, hf, hez, _, hz, hT⟩ := hP
  obtain ⟨h1, h2, h3, h4, h5⟩ := frame_gram_snoc hσ hJ P.e P.f P.z T hT he hez hz hf
    (F0 P) rfl (tupH P) rfl
  exact ⟨h1, h2, h3, h4, fun v => h5 _⟩

end GlobalTheory.FrameGram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SubMemDifferentIdeal
section
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal

namespace GlobalTheory.CMDiscrSq

open Polynomial

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

open NumberField Module Matrix in
open scoped ENNReal in
open Polynomial in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] in
private lemma sub_mem_differentIdeal_of_eq_star (h : _root_.Formalism.BasicNotions.CMData F E) (θ t : 𝓞 E)
    (ht : algebraMap (𝓞 E) E t = star (algebraMap (𝓞 E) E θ)) :
    θ - t ∈ differentIdeal (𝓞 F) (𝓞 E) := by
  change (t : E) = star (θ : E) at ht
  have hst : star (t : E) = θ := by rw [ht, star_star]
  by_cases hθ : (θ : E) ∈ (algebraMap F E).range
  · have : t = θ := RingOfIntegers.coe_injective (by
      change (t : E) = θ
      rw [ht]
      exact (h.fixed _).2 hθ)
    rw [this, sub_self]
    exact zero_mem _
  have hF : ∀ x : 𝓞 E, star (x : E) = x → ∃ s : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) s = x := by
    intro x hx
    obtain ⟨a, ha⟩ := (h.fixed _).1 hx
    have hai : IsIntegral ℤ a :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F E) (algebraMap F E).injective).1
        (by rw [IsScalarTower.coe_toAlgHom', ha]; exact x.isIntegral_coe)
    exact ⟨⟨a, hai⟩, RingOfIntegers.coe_injective ha⟩
  obtain ⟨s, hs⟩ := hF (θ + t) (by
    change star ((θ : E) + t) = (θ : E) + t
    rw [star_add, hst, ht, add_comm])
  obtain ⟨n, hn⟩ := hF (θ * t) (by
    change star ((θ : E) * t) = (θ : E) * t
    rw [star_mul, hst, ht])
  set p : (𝓞 F)[X] := X ^ 2 - C s * X + C n with hp_def
  have hpdeg : p.natDegree = 2 := by rw [hp_def]; compute_degree!
  have hpm : p.Monic := by rw [hp_def]; monicity!
  have hroot : aeval θ p = 0 := by
    simp only [hp_def, map_add (f := _), map_sub, map_mul, map_pow, aeval_X, aeval_C, hs, hn]
    ring
  have hint : IsIntegral (𝓞 F) θ := Algebra.IsIntegral.isIntegral θ
  have hdvd := minpoly.isIntegrallyClosed_dvd hint hroot
  have hmdeg : (minpoly (𝓞 F) θ).natDegree = 2 := by
    have hle : (minpoly (𝓞 F) θ).natDegree ≤ 2 := hpdeg ▸ natDegree_le_of_dvd hdvd hpm.ne_zero
    have hne1 : (minpoly (𝓞 F) θ).natDegree ≠ 1 := by
      intro h1
      obtain ⟨s', hs'⟩ := minpoly.natDegree_eq_one_iff.1 h1
      exact hθ ⟨(s' : F), by rw [← hs']; rfl⟩
    have hpos := minpoly.natDegree_pos hint
    omega
  have hmin : minpoly (𝓞 F) θ = p :=
    (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hpm hdvd (by omega)).symm
  have hint' : IsIntegral (𝓞 F) (θ : E) := hint.algebraMap
  have hFdeg : (minpoly F (θ : E)).natDegree = 2 := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' F hint',
      minpoly.algebraMap_eq RingOfIntegers.coe_injective, natDegree_map_eq_of_injective
        (IsFractionRing.injective (𝓞 F) F), hmdeg]
  have htop : IntermediateField.adjoin F {(θ : E)} = ⊤ := IntermediateField.eq_of_le_of_finrank_eq le_top (by
    rw [IntermediateField.finrank_top', IntermediateField.adjoin.finrank
      (Algebra.IsIntegral.isIntegral _), hFdeg, h.deg2])
  have hgen : Algebra.adjoin F {algebraMap (𝓞 E) E θ} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic _)]
    change (IntermediateField.adjoin F {(θ : E)}).toSubalgebra = ⊤
    rw [htop, IntermediateField.top_toSubalgebra]
  have hd := aeval_derivative_mem_differentIdeal (𝓞 F) F E θ hgen
  rw [hmin] at hd
  convert hd using 1
  simp [hp_def, hs]
  ring


open NumberField Module Matrix in
open scoped ENNReal in
open Polynomial in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] in
theorem _root_.GlobalTheory.CMDiscrSq.differentIdeal_eq_top (h : _root_.Formalism.BasicNotions.CMData F E) : differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨θ, t, ht, hθt⟩ := h.cmUnram.2.2 P hP
  exact hθt (hle (sub_mem_differentIdeal_of_eq_star h θ t ht))

end GlobalTheory.CMDiscrSq


open NumberField Module Matrix in
open scoped ENNReal in
theorem _root_.GlobalTheory.cm_discr_sq : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [StarRing E] [Algebra F E], _root_.Formalism.BasicNotions.CMData F E → |discr E| = discr F ^ 2 ∧
      Ideal.absNorm (Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (differentIdeal ℤ (𝓞 F))) =
        (discr F).natAbs ^ 2 := by
  intro F E _ _ _ _ _ _ h
  have hd := _root_.GlobalTheory.CMDiscrSq.differentIdeal_eq_top h
  have hE := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) E (𝓞 E)
  rw [hd, Ideal.absNorm_top, one_mul, h.deg2] at hE
  refine ⟨?_, ?_⟩
  · rw [Int.abs_eq_natAbs, hE]
    push_cast
    exact sq_abs _
  · have hmul := differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E)
    rw [hd, Ideal.top_mul] at hmul
    rw [← hmul, absNorm_differentIdeal E (𝓞 E), hE]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceEqSumLocalTracesAbovePrime
section
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors

namespace GlobalTheory.LocalTraceSum

open Filter Topology TensorProduct

section Local

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem isOpen_lt (γ : ValueGroupWithZero K) : IsOpen {x : K | valuation K x < γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hγ : γ ≠ 0 := (lt_of_le_of_lt zero_le hx).ne'
  refine (IsValuativeTopology.hasBasis_nhds' x).mem_iff.2 ⟨γ, hγ, fun y hy => ?_⟩
  have := (valuation K).map_add_lt (x := y - x) (y := x) hy hx
  simpa using this

theorem tendsto_pow {x : K} (h : valuation K x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' K).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero K) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

variable {l : ℕ} [Fact l.Prime] [Algebra ℚ_[l] K]

variable {Ω : Type} [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]

end Local

section Place

variable {F : Type} [Field F] [NumberField F] {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω]

end Place

section Ext

variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime]
  {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra ℚ_[l] K] {Ω : Type} [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]

end Ext

end GlobalTheory.LocalTraceSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularCloseToOneInverseCloseStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitriangular_close_to_one_inverse_close : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (n : ℕ) (M : Matrix (Fin n) (Fin n) E) (t : E), t ∈ L.O → (∀ i j, j < i → M i j = 0) → (∀ i, M i i = 1) → (∀ i j, ∃ o ∈ L.O, (M - 1) i j = t * o) → ∃ Mi : Matrix (Fin n) (Fin n) E, Mi * M = 1 ∧ M * Mi = 1 ∧ ∀ i j, ∃ o ∈ L.O, (Mi - 1) i j = t * o := by
  first | exact @GlobalTheory.unitriangular_inv_close | exact GlobalTheory.unitriangular_inv_close | (intros; apply GlobalTheory.unitriangular_inv_close <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.XClassesDenom
section
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal

namespace GlobalTheory

theorem xClasses_index {K : Type} [Field K] [NumberField K] (I J : Ideal (𝓞 K)) (a : 𝓞 K)
    (ha : a ≠ 0) (h : Ideal.span {a} = I * J) :
    ((Ideal.span {a}).toAddSubgroup.addSubgroupOf J.toAddSubgroup).index = Ideal.absNorm I := by
  have hle : Ideal.span {a} ≤ J := by rw [h]; exact Ideal.mul_le_right
  have hJ : J ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at h
    exact ha h
  have hNJ : Ideal.absNorm J ≠ 0 := fun h0 => hJ (Ideal.absNorm_eq_zero_iff.mp h0)
  have key := AddSubgroup.relIndex_mul_index
    (H := (Ideal.span {a}).toAddSubgroup) (K := J.toAddSubgroup) hle
  have e1 : J.toAddSubgroup.index = Ideal.absNorm J := (Ideal.absNorm_eq_index J).symm
  have e2 : (Ideal.span {a}).toAddSubgroup.index = Ideal.absNorm I * Ideal.absNorm J := by
    rw [← map_mul, ← h, Ideal.absNorm_eq_index]
  rw [e1, e2] at key
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hNJ) key

theorem xClasses_mem {K : Type} [Field K] [NumberField K] (I J : Ideal (𝓞 K)) (a : 𝓞 K)
    (hI : I ≠ ⊥) (haI : a ∈ I) (h : Ideal.span {a} = I * J) (z : K)
    (hz : ∀ α ∈ I, ∃ o : 𝓞 K, (o : K) = (α : K) * z) :
    ∃ o : J.toAddSubgroup, ((o : 𝓞 K) : K) = (a : K) * z := by
  obtain ⟨o, ho⟩ := hz a haI
  have hmem : o ∈ J := by
    have hle : Ideal.span {o} * I ≤ J * I := by
      rw [Ideal.span_singleton_mul_le_iff]
      intro α hα
      obtain ⟨p, hp⟩ := hz α hα
      have hop : o * α = a * p := by
        apply IsFractionRing.injective (𝓞 K) K
        simp only [map_mul]
        change (o : K) * (α : K) = (a : K) * (p : K)
        rw [ho, hp]; ring
      rw [hop, mul_comm J I, ← h]
      exact Ideal.mul_mem_right p _ (Ideal.mem_span_singleton_self a)
    have hdvd : J * I ∣ Ideal.span {o} * I := Ideal.dvd_iff_le.mpr hle
    rw [mul_dvd_mul_iff_right hI] at hdvd
    exact Ideal.dvd_span_singleton.mp hdvd
  exact ⟨⟨o, hmem⟩, ho⟩

theorem xClasses_denom {K : Type} [Field K] [NumberField K] (A : Ideal (𝓞 K)) {r : ℕ}
    (Y : Matrix (Fin r) (Fin (r + 1)) (𝓞 K)) (f : Fin r → Fin (r + 1))
    (S : Matrix (Fin r) (Fin r) K)
    (hx : ∀ a b, ∀ α ∈ A, ∃ o : 𝓞 K,
      (o : K) = (α : K) * (S * Y.map (algebraMap (𝓞 K) K)) a b) (i j : Fin r) :
    ∀ α ∈ Ideal.span {(Y.submatrix id f).det} * A, ∃ o : 𝓞 K, (o : K) = (α : K) * S i j := by
  classical
  intro α hα
  obtain ⟨β, hβ, rfl⟩ := Ideal.mem_span_singleton_mul.mp hα
  set φ := algebraMap (𝓞 K) K with hφ
  set B := Y.submatrix id f with hB
  have hM : B.map φ * (B.map φ).adjugate = (φ B.det) • (1 : Matrix (Fin r) (Fin r) K) := by
    rw [Matrix.mul_adjugate, RingHom.map_det]; rfl
  have e1 : ∀ k, (S * Y.map φ) i (f k) = (S * B.map φ) i k := by
    intro k; simp [Matrix.mul_apply, B]
  have e2 : ∀ k, φ (B.adjugate k j) = (B.map φ).adjugate k j := by
    intro k; exact congrFun (congrFun (RingHom.map_adjugate φ B) k) j
  have hkey : ∑ k, (S * Y.map φ) i (f k) * φ (B.adjugate k j) = φ B.det * S i j := by
    simp_rw [e1, e2]
    rw [← Matrix.mul_apply, Matrix.mul_assoc, hM]
    simp [Matrix.mul_apply, Matrix.one_apply, mul_comm]
  choose g hg using fun k => hx i (f k) β hβ
  refine ⟨∑ k, g k * B.adjugate k j, ?_⟩
  have hc : ∀ u : 𝓞 K, (u : K) = φ u := fun u => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hc, map_sum, map_mul] at hg ⊢
  simp_rw [hg]
  rw [mul_comm (φ B.det) (φ β), mul_assoc, ← hkey, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem xClasses : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (A : Ideal (𝓞 K)) (r : ℕ) (Y : Matrix (Fin r) (Fin (r + 1)) (𝓞 K)) (b₀ : Fin (r + 1)), A ≠ ⊥ → (Y.submatrix id b₀.succAbove).det ≠ 0 → ∃ reps : Finset (Matrix (Fin r) (Fin (r + 1)) K), reps.card ≤ Ideal.absNorm (Ideal.span {(Y.submatrix id b₀.succAbove).det} * A) ^ (r ^ 2) ∧ ∀ x : Matrix (Fin r) (Fin (r + 1)) K, (∀ a b, ∀ α ∈ A, ∃ o : 𝓞 K, (o : K) = (α : K) * x a b) → xᴴ * Y.map (algebraMap (𝓞 K) K) + (Y.map (algebraMap (𝓞 K) K))ᴴ * x = 0 → ∃ x₀ ∈ reps, ∃ c : Matrix (Fin r) (Fin r) (𝓞 K), (c.map (algebraMap (𝓞 K) K))ᴴ = -c.map (algebraMap (𝓞 K) K) ∧ x = x₀ + c.map (algebraMap (𝓞 K) K) * Y.map (algebraMap (𝓞 K) K) := by
  classical
  intro K _ _ _ A r Y b₀ hA hdet
  set f := b₀.succAbove with hf
  set φ := algebraMap (𝓞 K) K with hφ
  set D := (Y.submatrix id f).det with hD
  set I := Ideal.span {D} * A with hI
  set YK := Y.map φ with hYK
  have hφinj : Function.Injective φ := IsFractionRing.injective (𝓞 K) K
  have hc : ∀ u : 𝓞 K, (u : K) = φ u := fun u => rfl
  have hI0 : I ≠ ⊥ := by
    intro h0
    rcases mul_eq_zero.mp (show Ideal.span {D} * A = 0 from h0) with h1 | h1
    · exact hdet (Ideal.span_singleton_eq_bot.mp h1)
    · exact hA h1
  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
  obtain ⟨J, hJ⟩ : I ∣ Ideal.span {a} := Ideal.dvd_span_singleton.mpr haI
  have haK : φ a ≠ 0 := fun h0 => ha0 (hφinj (h0.trans (map_zero φ).symm))

  let C : Matrix (Fin (r + 1)) (Fin r) K :=
    (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) K).submatrix id f
  have hC : ∀ M : Matrix (Fin r) (Fin (r + 1)) K, M * C = M.submatrix id f := fun M => by
    simpa [C] using Matrix.mul_submatrix_one (Equiv.refl (Fin (r + 1))) f M
  have hYf : YK * C = (Y.submatrix id f).map φ := by
    rw [hC, hYK, Matrix.submatrix_map]
  have hdetYf : IsUnit (YK * C).det := by
    rw [hYf, show ((Y.submatrix id f).map φ).det = φ D from (RingHom.map_det φ _).symm]
    exact isUnit_iff_ne_zero.mpr (fun h0 => hdet (hφinj (h0.trans (map_zero φ).symm)))
  have hdetYfH : IsUnit (YK * C)ᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr (isUnit_iff_ne_zero.mp hdetYf))
  obtain ⟨Good, hGood⟩ : ∃ G : Matrix (Fin r) (Fin (r + 1)) K → Prop, ∀ x, G x ↔
      (∀ p q, ∀ α ∈ A, ∃ o : 𝓞 K, (o : K) = (α : K) * x p q) ∧ xᴴ * YK + YKᴴ * x = 0 :=
    ⟨_, fun _ => Iff.rfl⟩

  obtain ⟨Sx, hSx⟩ : ∃ Sx : Matrix (Fin r) (Fin (r + 1)) K → Matrix (Fin r) (Fin r) K,
      ∀ x, Good x → x = Sx x * YK ∧ (Sx x)ᴴ = -Sx x := by
    refine ⟨fun x => x * C * (YK * C)⁻¹, fun x hG => ?_⟩
    have hxY := ((hGood x).mp hG).2
    set Yf := YK * C with hYfdef
    set S := x * C * Yf⁻¹ with hS
    have hSYf : S * Yf = x * C := Matrix.nonsing_inv_mul_cancel_right _ _ hdetYf
    set P := x - S * YK with hP
    have hxP : x = S * YK + P := by rw [hP]; abel
    have hPC : P * C = 0 := by
      rw [hP, Matrix.sub_mul, Matrix.mul_assoc, ← hYfdef, hSYf, sub_self]
    have h1 : Cᴴ * xᴴ = Yfᴴ * Sᴴ := by
      rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul, hSYf]
    have h2 : Cᴴ * YKᴴ = Yfᴴ := by rw [← Matrix.conjTranspose_mul]
    have h3 : Yfᴴ * Sᴴ * YK + Yfᴴ * x = 0 := by
      have h0 : Cᴴ * (xᴴ * YK + YKᴴ * x) = 0 := by rw [hxY, Matrix.mul_zero]
      rwa [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, h2] at h0
    have h4 : Yfᴴ * ((Sᴴ + S) * YK + P) = 0 := by
      calc Yfᴴ * ((Sᴴ + S) * YK + P) = Yfᴴ * Sᴴ * YK + Yfᴴ * (S * YK + P) := by
            simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]; abel
        _ = 0 := by rw [← hxP]; exact h3
    have h5 : (Sᴴ + S) * YK + P = 0 := by
      have h0 := congrArg (fun M => Yfᴴ⁻¹ * M) h4
      rwa [Matrix.nonsing_inv_mul_cancel_left _ _ hdetYfH, Matrix.mul_zero] at h0
    have h6 : Sᴴ + S = 0 := by
      have h0 := congrArg (fun M => M * C * Yf⁻¹) h5
      rwa [Matrix.add_mul, hPC, add_zero, Matrix.mul_assoc ((Sᴴ + S)) YK C, ← hYfdef,
        Matrix.mul_nonsing_inv_cancel_right _ _ hdetYf, Matrix.zero_mul, Matrix.zero_mul] at h0
    have h7 : P = 0 := by rwa [h6, Matrix.zero_mul, zero_add] at h5
    rw [h7, add_zero] at hxP
    exact ⟨hxP, eq_neg_of_add_eq_zero_left h6⟩

  have hent : ∀ x, Good x → ∀ i j, ∃ o : J.toAddSubgroup, ((o : 𝓞 K) : K) = (a : K) * Sx x i j := by
    intro x hG i j
    have hx := ((hGood x).mp hG).1
    have h1 := (hSx x hG).1
    apply xClasses_mem I J a hI0 haI hJ
    have hx' : ∀ p q, ∀ α ∈ A, ∃ o : 𝓞 K, (o : K) = (α : K) * (Sx x * Y.map φ) p q := by
      intro p q α hα; rw [← hYK, ← h1]; exact hx p q α hα
    exact xClasses_denom A Y f (Sx x) hx' i j
  set Q := ↥J.toAddSubgroup ⧸ (Ideal.span {a}).toAddSubgroup.addSubgroupOf J.toAddSubgroup
  have hcardQ : Nat.card Q = Ideal.absNorm I := xClasses_index I J a ha0 hJ
  have : Finite Q := Nat.finite_of_card_ne_zero (by
    rw [hcardQ]; exact fun h0 => hI0 (Ideal.absNorm_eq_zero_iff.mp h0))
  let _ : Fintype Q := Fintype.ofFinite Q
  obtain ⟨key, hkey⟩ : ∃ key : Matrix (Fin r) (Fin (r + 1)) K → (Fin r → Fin r → Q),
      ∀ x, Good x → ∀ i j, ∃ o : J.toAddSubgroup,
        ((o : 𝓞 K) : K) = (a : K) * Sx x i j ∧ key x i j = (o : Q) := by
    refine ⟨fun x i j => if h : ∃ o : J.toAddSubgroup, ((o : 𝓞 K) : K) = (a : K) * Sx x i j
      then ((Classical.choose h : J.toAddSubgroup) : Q) else 0, fun x hG i j => ?_⟩
    have h := hent x hG i j
    exact ⟨Classical.choose h, Classical.choose_spec h, by simp only [dif_pos h]⟩
  obtain ⟨g, hg⟩ : ∃ g : (Fin r → Fin r → Q) → Matrix (Fin r) (Fin (r + 1)) K,
      ∀ q, (∃ x, Good x ∧ key x = q) → Good (g q) ∧ key (g q) = q := by
    refine ⟨fun q => if h : ∃ x, Good x ∧ key x = q then Classical.choose h else 0,
      fun q h => ?_⟩
    simp only [dif_pos h]
    exact Classical.choose_spec h
  refine ⟨Finset.univ.image g, ?_, ?_⟩
  · calc (Finset.univ.image g).card ≤ (Finset.univ : Finset (Fin r → Fin r → Q)).card :=
          Finset.card_image_le
      _ = Fintype.card Q ^ (r ^ 2) := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, ← pow_mul, sq]
      _ = Ideal.absNorm I ^ (r ^ 2) := by rw [← Nat.card_eq_fintype_card, hcardQ]
  · intro x hx hxY
    have hG : Good x := (hGood x).mpr ⟨hx, hxY⟩
    obtain ⟨hG', hk⟩ := hg (key x) ⟨x, hG, rfl⟩
    set x' := g (key x) with hx'
    have hdiff : ∀ i j, ∃ t : 𝓞 K, φ t = Sx x i j - Sx x' i j := by
      intro i j
      obtain ⟨o, ho, hko⟩ := hkey x hG i j
      obtain ⟨o', ho', hko'⟩ := hkey x' hG' i j
      have e : ((o' : J.toAddSubgroup) : Q) = (o : Q) := by
        rw [← hko, ← hko', hk]
      have hm := QuotientAddGroup.eq.mp e
      rw [AddSubgroup.mem_addSubgroupOf] at hm
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hm
      refine ⟨t, ?_⟩
      have ht' : φ t * φ a = φ a * (Sx x i j - Sx x' i j) := by
        rw [← map_mul, ht]
        simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, map_add (f := _), map_neg]
        rw [← hc, ← hc, ho, ho']; ring
      exact mul_left_cancel₀ haK (by rw [mul_comm]; exact ht')
    obtain ⟨c, hcc⟩ : ∃ c : Matrix (Fin r) (Fin r) (𝓞 K), ∀ i j, φ (c i j) = Sx x i j - Sx x' i j :=
      ⟨fun i j => Classical.choose (hdiff i j), fun i j => Classical.choose_spec (hdiff i j)⟩
    have hcm : c.map φ = Sx x - Sx x' := by
      ext i j; simp [hcc]
    refine ⟨x', Finset.mem_image_of_mem _ (Finset.mem_univ _), c, ?_, ?_⟩
    · rw [hcm, Matrix.conjTranspose_sub, (hSx x hG).2, (hSx x' hG').2]; abel
    · rw [hcm, Matrix.sub_mul, ← (hSx x hG).1, ← (hSx x' hG').1]; abel

end GlobalTheory
end

