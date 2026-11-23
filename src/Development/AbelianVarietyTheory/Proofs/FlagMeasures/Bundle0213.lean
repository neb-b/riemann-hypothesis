module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0002
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceFormDualTranslatedLatticeEqInverseTranspose
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.MeanDual

namespace GlobalTheory.MeanDual.LatticeDual

variable {E : Type} [Field E] [NumberField E]

theorem sum_embeddings_pairs (hE : IsTotallyComplex E) (f : (E →+* ℂ) → ℂ) :
    ∑ φ : E →+* ℂ, f φ =
      ∑ w : InfinitePlace E, (f w.embedding + f (ComplexEmbedding.conjugate w.embedding)) := by
  classical
  rw [← Finset.sum_fiberwise (s := univ) (g := fun φ : E →+* ℂ => InfinitePlace.mk φ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
    intro h
    have hc := IsTotallyComplex.isComplex (K := E) w
    rw [InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff] at hc
    exact hc h.symm
  rw [← Finset.sum_pair hne]
  congr 1
  ext φ
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  conv_lhs => rw [← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      rw [← h]; ext x; simp
  · rintro (h | h)
    · exact Or.inl h
    · right
      rw [h]; ext x; simp

theorem sum_re_embedding (hE : IsTotallyComplex E) (e : E) :
    ∑ w : InfinitePlace E, (w.embedding e).re = ((Algebra.trace ℚ E e : ℚ) : ℝ) / 2 := by
  have h1 := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := e)
  have h2 : ∑ σ : E →ₐ[ℚ] ℂ, σ e = ∑ φ : E →+* ℂ, φ e :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _ (fun φ => rfl)).symm
  rw [h2, sum_embeddings_pairs hE] at h1
  have h3 := congrArg Complex.re h1
  simp only [eq_ratCast, Complex.ratCast_re, Complex.re_sum, Complex.add_re,
    ComplexEmbedding.conjugate_coe_eq, Complex.conj_re] at h3
  rw [h3, Finset.sum_add_distrib]; ring

theorem eq_zero_of_sum_re (hE : IsTotallyComplex E) (c : InfinitePlace E → ℂ)
    (h : ∀ e : E, ∑ w : InfinitePlace E, (w.embedding e * c w).re = 0) : c = 0 := by
  classical
  have hli : LinearIndependent ℂ (fun φ : E →+* ℂ => (φ : E → ℂ)) :=
    (linearIndependent_monoidHom E ℂ).comp (fun φ : E →+* ℂ => φ.toMonoidHom)
      (fun a b hab => by ext x; exact DFunLike.congr_fun hab x)
  let d : (E →+* ℂ) → ℂ := fun φ =>
    if φ = (InfinitePlace.mk φ).embedding then c (InfinitePlace.mk φ)
    else (starRingEnd ℂ) (c (InfinitePlace.mk φ))
  have hd1 : ∀ w : InfinitePlace E, d w.embedding = c w := by
    intro w; simp [d]
  have hd2 : ∀ w : InfinitePlace E,
      d (ComplexEmbedding.conjugate w.embedding) = (starRingEnd ℂ) (c w) := by
    intro w
    have hc := IsTotallyComplex.isComplex (K := E) w
    rw [InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff] at hc
    simp [d, InfinitePlace.mk_conjugate_eq, hc]
  have hz := Fintype.linearIndependent_iff.1 hli d (by
    funext e
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [sum_embeddings_pairs hE (fun φ => d φ * φ e)]
    have : ∀ w : InfinitePlace E, d w.embedding * w.embedding e +
        d (ComplexEmbedding.conjugate w.embedding) * ComplexEmbedding.conjugate w.embedding e
        = ((2 * (w.embedding e * c w).re : ℝ) : ℂ) := by
      intro w
      rw [hd1, hd2, ComplexEmbedding.conjugate_coe_eq, ← map_mul, Complex.add_conj, mul_comm (c w)]
    simp only [this]
    rw [← Complex.ofReal_sum, ← Finset.mul_sum, h e]; simp)
  funext w
  rw [← hd1 w]; exact hz _

theorem exists_int_smul_mem {j : ℕ} (Λ : Submodule (𝓞 E) (Fin j → E))
    (hΛ : Submodule.IsFullLattice E Λ) (x : Fin j → E) : ∃ n : ℤ, n ≠ 0 ∧ (n : E) • x ∈ Λ := by
  exact _root_.GlobalTheory.IntegralMultiple.main Λ hΛ x

theorem pairing_rational (hE : IsTotallyComplex E) {j : ℕ} (x y : Fin j → E) :
    ∑ w : InfinitePlace E,
      ((fun a => w.embedding (x a)) ⬝ᵥ (fun a => w.embedding (y a))).re =
      ((Algebra.trace ℚ E (x ⬝ᵥ y) : ℚ) : ℝ) / 2 := by
  rw [← sum_re_embedding hE]
  refine Finset.sum_congr rfl fun w _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, map_sum, map_mul]

theorem exists_trDual (hE : IsTotallyComplex E) {j : ℕ} (Λ : Submodule (𝓞 E) (Fin j → E))
    (hΛ : Submodule.IsFullLattice E Λ) (u : InfinitePlace E → Fin j → ℂ)
    (hu : ∀ x ∈ Λ, ∃ z : ℤ, ∑ w : InfinitePlace E, ((fun a => w.embedding (x a)) ⬝ᵥ u w).re = z) :
    ∃ y ∈ trDual E j Λ, ∀ w a, u w a = w.embedding (y a) := by
  classical
  let φ : (Fin j → E) →+ ℝ :=
    { toFun := fun x => ∑ w : InfinitePlace E, ((fun a => w.embedding (x a)) ⬝ᵥ u w).re
      map_zero' := by simp [dotProduct]
      map_add' := by
        intro x y
        simp [dotProduct, add_mul, Finset.sum_add_distrib] }
  have hq : ∀ x, ∃ q : ℚ, φ x = q := by
    intro x
    obtain ⟨n, hn, hx⟩ := exists_int_smul_mem Λ hΛ x
    obtain ⟨z, hz⟩ := hu _ hx
    have h1 : φ (n • x) = z := by
      rw [← Int.cast_smul_eq_zsmul E]; exact hz
    rw [map_zsmul, zsmul_eq_mul] at h1
    refine ⟨z / n, ?_⟩
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    push_cast
    field_simp
    linarith
  choose q hq using hq
  let ψ : (Fin j → E) →+ ℚ :=
    { toFun := q
      map_zero' := by
        apply Rat.cast_injective (α := ℝ)
        rw [← hq]; simp
      map_add' := by
        intro x y
        apply Rat.cast_injective (α := ℝ)
        rw [Rat.cast_add, ← hq, ← hq, ← hq, map_add (f := _)] }
  have hy : ∀ a : Fin j, ∃ y : E, ∀ e : E,
      Algebra.trace ℚ E (y * e) = 2 * q (Pi.single a e) := by
    intro a
    obtain ⟨y, hy⟩ := ((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).surjective
      ((2 : ℚ) • (ψ.toRatLinearMap ∘ₗ LinearMap.single ℚ (fun _ => E) a))
    refine ⟨y, fun e => ?_⟩
    have := LinearMap.congr_fun hy e
    rw [LinearMap.BilinForm.toDual_def] at this
    simpa [ψ] using this
  choose y hy using hy
  have key : ∀ w a, u w a = w.embedding (y a) := by
    intro w a
    have := eq_zero_of_sum_re hE (fun w => u w a - w.embedding (y a)) (by
      intro e
      have h1 : φ (Pi.single a e) = ∑ w : InfinitePlace E, (w.embedding e * u w a).re := by
        refine Finset.sum_congr rfl fun w _ => ?_
        congr 1
        simp only [dotProduct]
        rw [Finset.sum_eq_single a]
        · simp
        · intro b _ hb; simp [hb]
        · simp
      have h2 := sum_re_embedding hE (y a * e)
      rw [hy] at h2
      simp only [mul_sub, Complex.sub_re, Finset.sum_sub_distrib, ← map_mul]
      rw [← h1, hq, mul_comm e, h2]; push_cast; ring)
    exact sub_eq_zero.1 (congrFun this w)
  refine ⟨y, ?_, key⟩
  intro x hx
  obtain ⟨z, hz⟩ := hu x hx
  refine ⟨z, ?_⟩
  have h1 := pairing_rational hE x y
  have h2 : ∀ w, u w = fun a => w.embedding (y a) := fun w => funext (key w)
  simp only [h2] at hz
  rw [hz] at h1
  apply Rat.cast_injective (α := ℝ)
  push_cast
  linarith

end GlobalTheory.MeanDual.LatticeDual

namespace GlobalTheory.MeanDual
open LatticeDual

theorem dualAt_latAt_eq_latAt_trDual : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)), Submodule.IsFullLattice E Λ → ∀ g : MatInf E j, 0 < detNorm E j g → dualAt E j (latAt E j Λ g) = latAt E j (trDual E j Λ) (invT E j g) := by
  intro E _ _ hE j Λ hΛ g hg
  have hdet : ∀ w, IsUnit (of (g w)).det := fun w =>
    isUnit_iff_ne_zero.2 ((detNorm_pos_iff E j g).1 hg w)
  have hinv : ∀ w, (of (invT E j g w))⁻¹ = (of (g w))ᵀ := by
    intro w
    rw [of_invT, ← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ (hdet w)]
  have hadj : ∀ (w : InfinitePlace E) (v v' : Fin j → ℂ),
      ((of (g w))⁻¹ *ᵥ v) ⬝ᵥ v' = v ⬝ᵥ ((of (g w))⁻¹ᵀ *ᵥ v') := by
    intro w v v'
    rw [Matrix.mulVec_transpose, dotProduct_comm v, ← Matrix.dotProduct_mulVec, dotProduct_comm]
  have hc1 : ∀ (w : InfinitePlace E) (v : Fin j → ℂ),
      (of (g w))⁻¹ᵀ *ᵥ ((of (g w))ᵀ *ᵥ v) = v := by
    intro w v
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ (hdet w)]; simp
  have hc2 : ∀ (w : InfinitePlace E) (v : Fin j → ℂ),
      (of (g w))ᵀ *ᵥ ((of (g w))⁻¹ᵀ *ᵥ v) = v := by
    intro w v
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ (hdet w)]; simp
  apply le_antisymm
  · refine Submodule.span_le.2 fun v hv => ?_
    obtain ⟨y, hy, hyv⟩ := exists_trDual hE Λ hΛ (fun w => (of (g w))⁻¹ᵀ *ᵥ v w) (by
      intro x hx
      obtain ⟨z, hz⟩ := hv _ (Submodule.subset_span ⟨x, hx, rfl⟩)
      refine ⟨z, ?_⟩
      rw [← hz]
      exact Finset.sum_congr rfl fun w _ => by rw [← hadj])
    refine Submodule.subset_span ⟨y, hy, ?_⟩
    funext w
    have : (fun a => w.embedding (y a)) = (of (g w))⁻¹ᵀ *ᵥ v w := funext fun a => (hyv w a).symm
    simp only [hinv, this, hc2]
  · refine Submodule.span_mono ?_
    rintro _ ⟨y, hy, rfl⟩ v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨x, hx, rfl⟩ := hv
      obtain ⟨z, hz⟩ := hy x hx
      refine ⟨z, ?_⟩
      simp only [hinv, hadj, hc1]
      rw [pairing_rational hE, hz]; push_cast; ring
    | zero => exact ⟨0, by simp⟩
    | add v v' _ _ h h' =>
      obtain ⟨z, hz⟩ := h
      obtain ⟨z', hz'⟩ := h'
      refine ⟨z + z', ?_⟩
      push_cast
      rw [← hz, ← hz', ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [← Complex.add_re, ← add_dotProduct]; rfl
    | smul n v _ h =>
      obtain ⟨z, hz⟩ := h
      refine ⟨n * z, ?_⟩
      push_cast
      rw [← hz, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      have : (n • v) w = n • v w := rfl
      rw [this, smul_dotProduct]; simp

end GlobalTheory.MeanDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TrivialModChosenPrimesIffMemKg
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev

open Inhab GlobalTheory.Mem.RowsBundle

theorem hAf_add_left (I : AutInst) (x x' y : Fin I.n → (I.E ⊗[I.F] Af I.F)) :
    hAf I (x + x') y = hAf I x y + hAf I x' y := by
  unfold hAf Formalism.UG.hform
  simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hAf_smul_left (I : AutInst) (a : I.E ⊗[I.F] Af I.F) (x y : Fin I.n → (I.E ⊗[I.F] Af I.F)) :
    hAf I (a • x) y = Formalism.UG.sigR I.cm.sig (Af I.F) a * hAf I x y := by
  unfold hAf Formalism.UG.hform
  simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]

theorem mapsTo_conj_of_adjoint (I : AutInst) (w w' : HeightOneSpectrum (𝓞 I.E))
    (T T' : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (hc : IsConj I w w')
    (hadj : ∀ x y, hAf I (T' *ᵥ x) y = hAf I x (T *ᵥ y))
    (hT' : ∀ y ∈ I.Lf, T' *ᵥ y ∈ extId I w.asIdeal • I.Lf) :
    ∀ y ∈ I.Lf, T *ᵥ y ∈ extId I w'.asIdeal • I.Lf := by
  intro y hy
  rw [DualIdeal.mem_extId_smul_iff I _ w'.ne_bot]
  intro y' hy'
  rw [← hadj]
  have key : ∀ u ∈ extId I w.asIdeal • I.Lf, ∃ z ∈ extId I w'.asIdeal,
      (z : I.E ⊗[I.F] Af I.F) = hAf I u y := by
    intro u hu
    refine Submodule.smul_induction_on hu (fun a ha l hl => ?_) (fun u u' hu hu' => ?_)
    · obtain ⟨a', ha', e⟩ := (extId_mul_sup_natCast_conj I).2.2.2.2.2.2 w w' hc a ha
      refine ⟨a' * ⟨_, (GlobalTheory.AdelicLattice.adelicLattice_selfDual I y).1 hy l hl⟩, Ideal.mul_mem_right _ _ ha', ?_⟩
      rw [Subring.coe_mul, e]
      show _ = hAf I ((a : I.E ⊗[I.F] Af I.F) • l) y
      rw [hAf_smul_left]
    · obtain ⟨z, hz, e⟩ := hu
      obtain ⟨z', hz', e'⟩ := hu'
      exact ⟨z + z', add_mem hz hz', by rw [Subring.coe_add, e, e', hAf_add_left]⟩
  exact key _ (hT' y' hy')

theorem PlFrame.trivial_iff {I : AutInst} {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w)
    {x : I.Gf} (hx : x ∈ I.Kset) :
    (∀ (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf), fr.c ⟨_, h⟩ = fr.c y) ↔
      ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ extId I w.asIdeal • I.Lf := by
  have key : ∀ (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf), fr.c ⟨_, h⟩ = fr.c y ↔
      (I.fmat x - 1) *ᵥ (y : Fin I.n → _) ∈ extId I w.asIdeal • I.Lf := by
    intro y h
    rw [← sub_eq_zero, ← map_sub, fr.c_ker, Matrix.sub_mulVec, Matrix.one_mulVec]
    rfl
  exact ⟨fun H y hy => (key ⟨y, hy⟩ (mulVec_mem hx hy)).1 (H _ _), fun H y h => (key y h).2 (H y.1 y.2)⟩

theorem IsChoice.isRadical_mul {I : AutInst} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type}
    {w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)} (hC : IsChoice I g Pl w) :
    (Ideal.span {((g 0 * g 1 : ℕ) : 𝓞 I.E)}).IsRadical := by
  have hc : Nat.Coprime (g 0) (g 1) := (Nat.coprime_primes (hC.1 0) (hC.1 1)).2 hC.2.1
  have hc' : IsCoprime ((g 0 : ℕ) : 𝓞 I.E) ((g 1 : ℕ) : 𝓞 I.E) := Nat.Coprime.cast hc
  rw [Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton,
    Ideal.mul_eq_inf_of_isCoprime ((Ideal.isCoprime_span_singleton_iff _ _).2 hc')]
  exact (hC.2.2.1 0).inf (hC.2.2.1 1)

theorem trivial_iff_mem_Kg : ∀ (I : AutInst) (N : ℕ) (g : Fin 2 → ℕ) (Pl : Fin 2 → Type)
    (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)) (fr : ∀ k v, PlFrame I N (g k) (w k v)), I.n = N →
    IsChoice I g Pl w → ∀ x ∈ I.Kset, (∀ k v (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf),
      (fr k v).c ⟨_, h⟩ = (fr k v).c y) ↔ x ∈ I.Kg (g 0 * g 1) := by
  intro I N g Pl w fr _ hC x hx
  have hx' : x⁻¹ ∈ I.Kset := (Ksub I).inv_mem hx
  have hone : 1 ≤ g 0 * g 1 := Nat.mul_pos (hC.1 0).pos (hC.1 1).pos
  have hmem : ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ I.Lf := fun y hy => by
    simpa using sub_one_pow_mem hx 1 hy
  have crt := fun y hy => GlobalTheory.RowLev.SqfCrt.mem_extId_smul_forall_iff I (g 0 * g 1) hone hC.isRadical_mul _ (hmem y hy)
  constructor
  · intro H
    have H1 := fun k v => ((fr k v).trivial_iff hx).1 (H k v)
    have H2 : ∀ k v, ∀ y ∈ I.Lf, (I.fmat x⁻¹ - 1) *ᵥ y ∈ extId I (w k v).asIdeal • I.Lf := by
      intro k v y hy
      have h1 : I.fmat x * I.fmat x⁻¹ = 1 := by rw [← fmat_mul, mul_inv_cancel, fmat_one]
      have h := neg_mem (H1 k v _ (mulVec_mem hx' hy))
      rw [Matrix.mulVec_mulVec, sub_mul, h1, one_mul, ← Matrix.neg_mulVec, neg_sub] at h
      exact h
    refine ⟨hx, fun y hy => (crt y hy).1 fun u hu => ?_⟩
    have hk : ∃ k, ((g k : ℕ) : 𝓞 I.E) ∈ u.asIdeal := by
      rw [Nat.cast_mul] at hu
      exact (u.isPrime.mem_or_mem hu).elim (fun h => ⟨0, h⟩) fun h => ⟨1, h⟩
    obtain ⟨k, hk⟩ := hk
    obtain ⟨v, rfl | hv⟩ := hC.2.2.2.2.2.2 k u hk
    · exact H1 k v y hy
    · refine mapsTo_conj_of_adjoint I _ _ _ _ hv (fun a b => ?_) (H2 k v) y hy
      simpa only [pow_one] using hAf_pow_adjoint x 1 a b
  · intro H k v
    refine ((fr k v).trivial_iff hx).2 fun y hy => (crt y hy).2 (H.2 y hy) _ ?_
    have h := (hC.2.2.2.1 k v).1
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ h
    · exact Ideal.mul_mem_left _ _ h

end GlobalTheory.RowLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ZlatticeCovolumeEqOfCoprimeScalars
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.CovScal

theorem abs_det_mul_covolume_eq_nat_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (A B : Submodule ℤ E) [DiscreteTopology A] [IsZLattice ℝ A]
    [DiscreteTopology B] [IsZLattice ℝ B] (T : E →ₗ[ℝ] E) (hT : ∀ y ∈ A, T y ∈ B) :
    ∃ n : ℕ, |LinearMap.det T| * ZLattice.covolume A μ = n * ZLattice.covolume B μ := by
  classical

  let bA := Module.Free.chooseBasis ℤ A
  let bB := Module.Free.chooseBasis ℤ B
  let b₀ := bA.ofZLatticeBasis ℝ A
  let e := (bB.ofZLatticeBasis ℝ B).indexEquiv b₀
  let bB' := bB.reindex e
  let c := bB'.ofZLatticeBasis ℝ B
  let M : Matrix (Module.Free.ChooseBasisIndex ℤ A) (Module.Free.ChooseBasisIndex ℤ A) ℤ :=
    fun i j => bB'.repr ⟨T (bA j), hT _ (bA j).2⟩ i
  have hb₀ : ((↑) : A → E) ∘ bA = b₀ := funext fun i => (bA.ofZLatticeBasis_apply ℝ A i).symm
  have hc : ((↑) : B → E) ∘ bB' = c := funext fun i => (bB'.ofZLatticeBasis_apply ℝ B i).symm

  have hM : c.toMatrix (T ∘ b₀) = M.map (Int.cast : ℤ → ℝ) := by
    ext i j
    rw [Module.Basis.toMatrix_apply, Matrix.map_apply, Function.comp_apply,
      show b₀ j = ((bA j : A) : E) from bA.ofZLatticeBasis_apply ℝ A j]
    exact bB'.ofZLatticeBasis_repr_apply ℝ B ⟨T (bA j), hT _ (bA j).2⟩ i
  have hdet : LinearMap.det T = b₀.det c * (M.det : ℝ) := by
    have h1 : b₀.det (T ∘ b₀) = LinearMap.det T := by
      rw [b₀.det_comp T b₀, b₀.det_self, mul_one]
    rw [← h1, b₀.det_apply, ← b₀.toMatrix_mul_toMatrix c (T ∘ b₀), Matrix.det_mul,
      ← b₀.det_apply, hM, Int.cast_det]
  have hcA := ZLattice.covolume_eq_det_mul_measureReal A μ bA b₀
  have hcB := ZLattice.covolume_eq_det_mul_measureReal B μ bB' b₀
  rw [hb₀, b₀.det_self, abs_one, one_mul] at hcA
  rw [hc] at hcB
  refine ⟨M.det.natAbs, ?_⟩
  rw [hcA, hcB, hdet, Nat.cast_natAbs, Int.cast_abs, abs_mul]
  ring

noncomputable def blockScal {ι : Type} (κ : Type) (d : ι → ℝ) : (ι → κ → ℝ) →ₗ[ℝ] (ι → κ → ℝ) :=
  LinearMap.pi fun v => (d v • (LinearMap.id : (κ → ℝ) →ₗ[ℝ] (κ → ℝ))).comp (LinearMap.proj v)

theorem blockScal_apply {ι κ : Type} (d : ι → ℝ) (y : ι → κ → ℝ) :
    blockScal κ d y = fun v i => d v * y v i := by
  funext v i
  simp [blockScal]

theorem det_blockScal {ι κ : Type} [Fintype ι] [Fintype κ] (d : ι → ℝ) :
    LinearMap.det (blockScal κ d) = ∏ v, d v ^ Fintype.card κ := by
  unfold blockScal
  rw [LinearMap.det_pi]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_fintype_fun_eq_card]

theorem eq_one_of_forall_prime {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ p : ℕ, p.Prime → ∃ a b : ℕ, ¬ p ∣ a * b ∧ ρ ^ 2 * b = a) : ρ = 1 := by
  obtain ⟨a₀, b₀, h2, hab₀⟩ := h 2 Nat.prime_two
  have ha₀ : a₀ ≠ 0 := by rintro rfl; simp at h2
  have hb₀ : b₀ ≠ 0 := by rintro rfl; simp at h2

  have key : a₀ = b₀ := by
    refine Nat.eq_of_factorization_eq ha₀ hb₀ fun p => ?_
    by_cases hp : p.Prime
    · obtain ⟨a, b, hp', hab⟩ := h p hp
      have ha : a ≠ 0 := by rintro rfl; simp at hp'
      have hb : b ≠ 0 := by rintro rfl; simp at hp'
      have hcast : ((a₀ * b : ℕ) : ℝ) = ((a * b₀ : ℕ) : ℝ) := by
        push_cast
        rw [← hab₀, ← hab]
        ring
      have hnat : a₀ * b = a * b₀ := by exact_mod_cast hcast
      have hpa : a.factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd fun hd => hp' (dvd_mul_of_dvd_left hd b)
      have hpb : b.factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd fun hd => hp' (dvd_mul_of_dvd_right hd a)
      have hf := congrArg (fun n => n.factorization p) hnat
      simp only [Nat.factorization_mul ha₀ hb, Nat.factorization_mul ha hb₀, Finsupp.add_apply,
        hpa, hpb] at hf
      omega
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  rw [key] at hab₀
  have hb₀' : (b₀ : ℝ) ≠ 0 := by exact_mod_cast hb₀
  have hsq : ρ ^ 2 = 1 := mul_right_cancel₀ hb₀' (by rw [hab₀, one_mul])
  have hfac : (ρ - 1) * (ρ + 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfac with h' | h' <;> linarith

theorem covolume_eq_of_scalars : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (A B : Submodule ℤ (ι → κ → ℝ)) [DiscreteTopology A] [IsZLattice ℝ A] [DiscreteTopology B] [IsZLattice ℝ B], (∀ p : ℕ, p.Prime → ∃ (d : ι → ℝ) (N : ℕ), ¬ p ∣ N ∧ ∏ v, d v ^ 2 = N ∧ (∀ y ∈ A, (fun v i => d v * y v i) ∈ B) ∧ ∀ y ∈ B, (fun v i => d v * y v i) ∈ A) → ZLattice.covolume A volume = ZLattice.covolume B volume := by
  intro ι κ _ _ A B _ _ _ _ h
  have hA : 0 < ZLattice.covolume A volume := ZLattice.covolume_pos A volume
  have hB : 0 < ZLattice.covolume B volume := ZLattice.covolume_pos B volume
  set cA := ZLattice.covolume A volume
  set cB := ZLattice.covolume B volume
  suffices key : cA / cB = 1 from (div_eq_one_iff_eq hB.ne').mp key
  refine eq_one_of_forall_prime (div_pos hA hB) fun p hp => ?_
  obtain ⟨d, N, hpN, hN, hAB, hBA⟩ := h p hp
  have hT : ∀ y ∈ A, blockScal κ d y ∈ B := fun y hy => by rw [blockScal_apply]; exact hAB y hy
  have hT' : ∀ y ∈ B, blockScal κ d y ∈ A := fun y hy => by rw [blockScal_apply]; exact hBA y hy
  obtain ⟨n, hn⟩ := abs_det_mul_covolume_eq_nat_mul volume A B (blockScal κ d) hT
  obtain ⟨m, hm⟩ := abs_det_mul_covolume_eq_nat_mul volume B A (blockScal κ d) hT'
  set D := |LinearMap.det (blockScal κ d)|

  have hD2 : D ^ 2 = (N : ℝ) ^ Fintype.card κ := by
    rw [sq_abs, det_blockScal, ← hN, Finset.prod_pow, Finset.prod_pow]
    ring
  have hnm : ((n * m : ℕ) : ℝ) = ((N ^ Fintype.card κ : ℕ) : ℝ) := by
    push_cast
    have h0 : ((n : ℝ) * m - D ^ 2) * (cA * cB) = 0 := by
      linear_combination (-(D * cB)) * hn - (n * cB) * hm
    rcases mul_eq_zero.mp h0 with h0 | h0
    · rw [← hD2]; linarith
    · exact absurd h0 (mul_pos hA hB).ne'
  have hnat : n * m = N ^ Fintype.card κ := by exact_mod_cast hnm
  refine ⟨n, m, ?_, ?_⟩
  · rw [hnat]
    exact fun hd => hpN (hp.dvd_of_dvd_pow hd)
  · rw [div_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 hB.ne')]
    linear_combination (-cA) * hm + cB * hn

end GlobalTheory.CovScal
end

