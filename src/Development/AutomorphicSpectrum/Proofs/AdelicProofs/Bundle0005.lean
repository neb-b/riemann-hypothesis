module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.GramMat

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.GramMatrixPosDefConjugate
section
open NumberField TensorProduct GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.Lines Matrix
open scoped ComplexOrder nonZeroDivisors

namespace GlobalTheory.CompanionTheory.Ar.Lines

theorem gramMat_eq_gram {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    (σ : L →+* ℂ) {i : ℕ} (f : Fin i → B.carrier) :
    gramMat B σ f = Matrix.gram ℂ (fun a => fibreVec B.metric σ (f a)) := by
  rfl

private theorem flat_complex_at {L : Type} [Field L] [NumberField L] (σ : L →+* ℂ) :
    Module.Flat (𝓞 L) (ComplexAt σ) := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
  intro z hz
  obtain ⟨⟨r, hr⟩, hrz⟩ := (Submodule.mem_torsion_iff z).mp hz
  rw [Submodule.mem_bot]
  have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
  have hrL : (r : L) ≠ 0 := by
    intro h
    apply hr0
    first
      | exact RingOfIntegers.coe_eq_zero_iff.mp h
      | exact_mod_cast h
  have hσ : σ (r : L) ≠ 0 := (map_ne_zero σ).mpr hrL
  change r • z = 0 at hrz
  rw [ComplexAt.smul_def] at hrz
  have h2 := congrArg (ComplexAt.ofComplex σ).symm hrz
  rw [map_mul, AlgEquiv.symm_apply_apply, map_zero] at h2
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h hσ
  · exact (ComplexAt.ofComplex σ).symm.injective (h.trans (map_zero _).symm)

private theorem linear_independent_one_tmul {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    (σ : L →+* ℂ) {i : ℕ} (f : Fin i → B.carrier) (hf : LinearIndependent (𝓞 L) f) :
    LinearIndependent ℂ (fun a => ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] f a : Fibre σ B.carrier)) := by
  haveI := flat_complex_at σ
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := ComplexAt σ)
    (Finsupp.linearCombination (𝓞 L) f) hf
  rw [Fintype.linearIndependent_iff]
  intro g hg a
  have hterm : ∀ b, g b • ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] f b : Fibre σ B.carrier) =
      (ComplexAt.ofComplex σ (g b)) ⊗ₜ[𝓞 L] f b := by
    intro b
    rw [TensorProduct.smul_tmul', ComplexAt.complex_smul_def, mul_one]
  simp only [hterm] at hg
  set T : ComplexAt σ ⊗[𝓞 L] (Fin i →₀ 𝓞 L) :=
    ∑ b, (ComplexAt.ofComplex σ (g b)) ⊗ₜ[𝓞 L] Finsupp.single b (1 : 𝓞 L) with hT
  have hT0 : LinearMap.lTensor (ComplexAt σ) (Finsupp.linearCombination (𝓞 L) f) T = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hT, map_sum]
    simp only [LinearMap.lTensor_tmul, Finsupp.linearCombination_single, one_smul]
    exact hg
  have hT1 : T = 0 := hinj (hT0.trans (map_zero _).symm)
  have h3 := congrArg (fun t => TensorProduct.rid (𝓞 L) (ComplexAt σ)
    (LinearMap.lTensor (ComplexAt σ) (Finsupp.lapply a) t)) hT1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hT, map_sum, LinearMap.lTensor_tmul, Finsupp.lapply_apply, TensorProduct.rid_tmul,
    Finsupp.single_apply, map_zero, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true] at h3
  exact (ComplexAt.ofComplex σ).injective (h3.trans (map_zero _).symm)

theorem gramMat_posDef_and_conj : ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    (i : ℕ) (f : Fin i → B.carrier), LinearIndependent (𝓞 L) f →
    (∀ σ, (gramMat B σ f).PosDef) ∧
      ∀ σ, gramMat B (ComplexEmbedding.conjugate σ) f = (gramMat B σ f).map (starRingEnd ℂ) := by
  intro L _ _ B i f hf
  refine ⟨fun σ => ?_, fun σ => ?_⟩
  · rw [gramMat_eq_gram]
    refine Matrix.posDef_gram_iff_linearIndependent.mpr ?_
    exact linear_independent_one_tmul B σ f hf
  · ext a b
    have hc : ∀ e : B.carrier, conjFS B.metric σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e) =
        (1 : ComplexAt (ComplexEmbedding.conjugate σ)) ⊗ₜ[𝓞 L] e := by
      intro e
      show conjMap σ B.carrier ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e) = _
      rw [conjMap_tmul, map_one]
    have h2 := conjFS_inner B.metric σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] f a) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] f b)
    rw [hc, hc] at h2
    simp only [gramMat, Matrix.of_apply, Matrix.map_apply]
    exact h2

end GlobalTheory.CompanionTheory.Ar.Lines
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.HermitianLatticeDegreeEqBundleDegree
section
namespace GlobalTheory.CompanionTheory.Ar.Lines

open NumberField TensorProduct GroundTheory.Heights₂.Heights Matrix
open scoped ComplexOrder nonZeroDivisors

noncomputable section

theorem gramAt_standard {L : Type} [Field L] {i : ℕ} (h : Matrix (Fin i) (Fin i) ℂ) (σ : L →+* ℂ) :
    gramAt h σ (fun j : Fin i => (Pi.single j 1 : Fin i → L)) = h := by
  have he : ∀ j : Fin i, embVec σ (Pi.single j 1 : Fin i → L) = Pi.single j 1 := by
    intro j
    funext k
    by_cases hk : k = j
    · subst hk; simp [embVec]
    · simp [embVec, Pi.single_eq_of_ne hk]
  ext a b
  simp [gramAt, he, Matrix.mulVec_single_one, Matrix.col_apply]

theorem degree_eq_degreeWith (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    (F : Submodule (𝓞 L) B.carrier) (i : ℕ) (f : Fin i → F) (c : F →ₗ[𝓞 L] (Fin i → L))
    (Fl : HermLattice L i) (hf : LinearIndependent (𝓞 L) f) (hi : i = B.rank F)
    (hc : Function.Injective c) (hcf : ∀ j, c (f j) = Pi.single j 1)
    (hlat : Fl.lattice = LinearMap.range c)
    (hmet : ∀ σ, Fl.metric σ = gramMat B σ (fun j => (f j : B.carrier))) :
    Fl.degree = B.degreeWith F f := by
  have hspanK : Submodule.span L (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → L)) = ⊤ := by
    have h : (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → L)) =
        Set.range (Pi.basisFun L (Fin i)) := by
      congr 1; funext j; exact (Pi.basisFun_apply _ _ _).symm
    rw [h]
    exact (Pi.basisFun L (Fin i)).span_eq
  have hS : (Submodule.span (𝓞 L) (Set.range f)).map c =
      Submodule.span (𝓞 L) (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → L)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact congrArg _ (congrArg Set.range (funext hcf))
  have hA : (Fl.lattice ⊓ (Submodule.span L (Set.range fun j : Fin i =>
      (Pi.single j 1 : Fin i → L))).restrictScalars (𝓞 L)) = LinearMap.range c := by
    rw [hspanK, hlat, Submodule.restrictScalars_top, inf_top_eq]
  have hidx : genIndex
      (Fl.lattice ⊓ (Submodule.span L (Set.range fun j : Fin i =>
        (Pi.single j 1 : Fin i → L))).restrictScalars (𝓞 L)).toAddSubgroup
      (Submodule.span (𝓞 L) (Set.range fun j : Fin i =>
        (Pi.single j 1 : Fin i → L))).toAddSubgroup =
      (Nat.card (F ⧸ Submodule.span (𝓞 L) (Set.range f)) : ℝ) := by
    rw [hA, ← hS, genIndex]
    have hle : ((Submodule.span (𝓞 L) (Set.range f)).map c).toAddSubgroup ≤
        (LinearMap.range c).toAddSubgroup := by
      rintro _ ⟨x, -, rfl⟩
      exact ⟨x, rfl⟩
    rw [AddSubgroup.relIndex_eq_one.mpr hle, LinearMap.range_eq_map, Submodule.map_toAddSubgroup,
      Submodule.map_toAddSubgroup, AddSubgroup.relIndex_map_map_of_injective _ _ hc,
      Submodule.top_toAddSubgroup, AddSubgroup.relIndex_top_right]
    simp
    rfl
  have hgram : ∀ σ : L →+* ℂ,
      (gramAt (Fl.metric σ) σ fun j : Fin i => (Pi.single j 1 : Fin i → L)).det.re =
        ‖HermitianBundle.gramDet B σ (fun j => (f j : B.carrier))‖ := by
    intro σ
    have hd : HermitianBundle.gramDet B σ (fun j => (f j : B.carrier)) = (Fl.metric σ).det := by
      rw [hmet σ]
      rfl
    rw [gramAt_standard, hd]
    have hp : 0 < (Fl.metric σ).det := (Fl.posDef σ).det_pos
    have hre : ((Fl.metric σ).det.re : ℂ) = (Fl.metric σ).det := by
      apply Complex.ext
      · simp
      · simpa using (Complex.lt_def.mp hp).2.symm ▸ rfl
    rw [← hre, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    exact (Complex.lt_def.mp hp).1
  simp only [HermLattice.degree, subDegree, HermitianBundle.degreeWith, hidx, hgram]

end

end GlobalTheory.CompanionTheory.Ar.Lines
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.LinearIndependentCoordinatesDenominator
section
open NumberField TensorProduct GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.Lines Matrix
open scoped ComplexOrder nonZeroDivisors

namespace GlobalTheory.CompanionTheory.Ar.Lines.Coords

variable {R : Type*} [CommRing R] [IsDomain R] {M : Type*} [AddCommGroup M] [Module R M]

theorem exists_relation [Module.Finite R M] {i : ℕ} {f : Fin i → M}
    (hf : LinearIndependent R f) (hi : i = Module.finrank R M) (x : M) :
    ∃ (D : R) (a : Fin i → R), D ≠ 0 ∧ D • x = ∑ j, a j • f j := by
  classical
  have hnot : ¬ LinearIndependent R (Fin.cons x f : Fin (i + 1) → M) := fun hli => by
    have := hli.fintype_card_le_finrank
    rw [Fintype.card_fin] at this
    omega
  obtain ⟨g, hg, k, hk⟩ := Fintype.not_linearIndependent_iff.mp hnot
  rw [Fin.sum_univ_succ] at hg
  simp only [Fin.cons_zero, Fin.cons_succ] at hg
  have h0 : g 0 ≠ 0 := by
    intro h0
    rw [h0, zero_smul, zero_add] at hg
    have hz := Fintype.linearIndependent_iff.mp hf _ hg
    apply hk
    induction k using Fin.cases with
    | zero => exact h0
    | succ j => exact hz j
  refine ⟨g 0, fun j => -g j.succ, h0, ?_⟩
  simp only [neg_smul, Finset.sum_neg_distrib]
  exact eq_neg_of_add_eq_zero_left hg

theorem relation_cross {i : ℕ} {f : Fin i → M} (hf : LinearIndependent R f) {x : M}
    {D D' : R} {a a' : Fin i → R} (h : D • x = ∑ j, a j • f j)
    (h' : D' • x = ∑ j, a' j • f j) (j : Fin i) : D' * a j = D * a' j := by
  have key : ∑ j, (D' * a j - D * a' j) • f j = 0 := by
    simp only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, ← h, ← h']
    rw [smul_comm D' D x, sub_self]
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hf _ key j)

private theorem coord_lemma (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] {i : ℕ}
    {f : Fin i → M} (hf : LinearIndependent R f) {x : M} {D D' : R} {a a' : Fin i → R}
    (hD : D ≠ 0) (hD' : D' ≠ 0) (h : D • x = ∑ j, a j • f j) (h' : D' • x = ∑ j, a' j • f j)
    (j : Fin i) :
    algebraMap R K (a j) / algebraMap R K D = algebraMap R K (a' j) / algebraMap R K D' := by
  have hne : ∀ {E : R}, E ≠ 0 → algebraMap R K E ≠ 0 := fun hE h0 =>
    hE (IsFractionRing.injective R K (by rw [h0, map_zero]))
  rw [div_eq_div_iff (hne hD) (hne hD'), ← map_mul, ← map_mul, mul_comm (a j),
    relation_cross hf h h' j, mul_comm]

theorem exists_coordinates (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    [Module.Finite R M] [Module.IsTorsionFree R M] {i : ℕ} {f : Fin i → M}
    (hf : LinearIndependent R f) (hi : i = Module.finrank R M) :
    ∃ c : M →ₗ[R] (Fin i → K), Function.Injective c ∧ (∀ j, c (f j) = Pi.single j 1) ∧
      ∀ x, ∃ (D : R) (a : Fin i → R), D ≠ 0 ∧ D • x = ∑ j, a j • f j ∧
        ∀ j, algebraMap R K D * c x j = algebraMap R K (a j) := by
  classical
  choose Dx ax hDx hax using fun x => exists_relation hf hi x
  have hne : ∀ {D : R}, D ≠ 0 → algebraMap R K D ≠ 0 := fun hD h0 =>
    hD (IsFractionRing.injective R K (by rw [h0, map_zero]))
  have key : ∀ x (D : R) (a : Fin i → R), D ≠ 0 → D • x = ∑ j, a j • f j → ∀ j,
      algebraMap R K (ax x j) / algebraMap R K (Dx x) =
        algebraMap R K (a j) / algebraMap R K D :=
    fun x D a hD h j => coord_lemma K hf (hDx x) hD (hax x) h j
  let c : M →ₗ[R] (Fin i → K) :=
    { toFun := fun x j => algebraMap R K (ax x j) / algebraMap R K (Dx x)
      map_add' := fun x y => by
        funext j
        have hrel : (Dx x * Dx y) • (x + y) = ∑ j, (Dx y * ax x j + Dx x * ax y j) • f j := by
          rw [smul_add, mul_smul, mul_smul, smul_comm (Dx x) (Dx y) x, hax x, hax y,
            Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
          simp only [add_smul, mul_smul]
        dsimp only [Pi.add_apply]
        rw [key (x + y) _ _ (mul_ne_zero (hDx x) (hDx y)) hrel j,
          div_add_div _ _ (hne (hDx x)) (hne (hDx y))]
        simp only [map_add (f := _), map_mul]
        ring
      map_smul' := fun r x => by
        funext j
        have hrel : Dx x • (r • x) = ∑ j, (r * ax x j) • f j := by
          rw [smul_comm, hax x, Finset.smul_sum]
          simp only [mul_smul]
        dsimp only [Pi.smul_apply, RingHom.id_apply]
        rw [key (r • x) _ _ (hDx x) hrel j, Algebra.smul_def, map_mul]
        ring }
  have hc : ∀ x j, c x j = algebraMap R K (ax x j) / algebraMap R K (Dx x) := fun _ _ => rfl
  refine ⟨c, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have ha : ∀ j, ax x j = 0 := fun j => by
      have := congrFun hx j
      rw [hc, Pi.zero_apply, div_eq_zero_iff] at this
      rcases this with h | h
      · exact IsFractionRing.injective R K (by rw [h, map_zero])
      · exact absurd h (hne (hDx x))
    have h0 : Dx x • x = 0 := by
      rw [hax x]
      simp [ha]
    exact (smul_eq_zero_iff_right (hDx x)).mp h0
  · intro j
    funext k
    have hrel : (1 : R) • f j = ∑ l, (Pi.single j (1 : R) : Fin i → R) l • f l := by
      rw [one_smul]
      simp [Pi.single_apply]
    rw [hc, key (f j) 1 _ one_ne_zero hrel k]
    by_cases hk : k = j
    · subst hk
      simp
    · simp [hk]
  · intro x
    exact ⟨Dx x, ax x, hDx x, hax x, fun j => by
      rw [hc]
      exact mul_div_cancel₀ _ (hne (hDx x))⟩

theorem coordinates_of_maximal_independent (L : Type) [Field L] [NumberField L] (M : Type)
    [AddCommGroup M] [Module (𝓞 L) M] [Module.Finite (𝓞 L) M] [Module.IsTorsionFree (𝓞 L) M]
    (i : ℕ) (f : Fin i → M) (hf : LinearIndependent (𝓞 L) f)
    (hi : i = Module.finrank (𝓞 L) M) :
    ∃ c : M →ₗ[𝓞 L] (Fin i → L), Function.Injective c ∧ (∀ j, c (f j) = Pi.single j 1) ∧
      ∀ x, ∃ (D : 𝓞 L) (a : Fin i → 𝓞 L), D ≠ 0 ∧ D • x = ∑ j, a j • f j ∧
        ∀ j, (D : L) * c x j = a j := by
  obtain ⟨c, h1, h2, h3⟩ := exists_coordinates L hf hi
  exact ⟨c, h1, h2, h3⟩

end GlobalTheory.CompanionTheory.Ar.Lines.Coords
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.SpanBaseChangeCoordinates
section
open NumberField TensorProduct GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.Lines Matrix
open scoped ComplexOrder nonZeroDivisors

namespace GlobalTheory.CompanionTheory.Ar.Lines.Lift

open ComplexAt

noncomputable section

variable {L : Type} [Field L] [NumberField L] {K : Type} [Field K] [NumberField K] [Algebra L K]
  {E : Type} [AddCommGroup E] [Module (𝓞 L) E]

theorem coord_one_tmul (τ : K →+* ℂ) (b : 𝓞 K) (e : E) :
    baseChangeCoord τ ((1 : ComplexAt τ) ⊗ₜ[𝓞 K] (b ⊗ₜ[𝓞 L] e)) =
      τ (b : K) • ((1 : ComplexAt (τ.comp (algebraMap L K))) ⊗ₜ[𝓞 L] e) := by
  rw [baseChangeCoord_tmul, TensorProduct.smul_tmul']
  congr 1

theorem coord_smul (τ : K →+* ℂ) (b : 𝓞 K) (X : 𝓞 K ⊗[𝓞 L] E) :
    baseChangeCoord τ ((1 : ComplexAt τ) ⊗ₜ[𝓞 K] (b • X)) =
      τ (b : K) • baseChangeCoord τ ((1 : ComplexAt τ) ⊗ₜ[𝓞 K] X) := by
  induction X using TensorProduct.induction_on with
  | zero => simp
  | tmul c e =>
    rw [TensorProduct.smul_tmul', coord_one_tmul, coord_one_tmul, smul_eq_mul, smul_smul]
    simp
  | add X Y hX hY => rw [smul_add, tmul_add, map_add (f := _), hX, hY, tmul_add, map_add (f := _), smul_add]

theorem one_tmul_smul (σ : L →+* ℂ) (a : 𝓞 L) (e : E) :
    (1 : ComplexAt σ) ⊗ₜ[𝓞 L] (a • e) = σ (a : L) • ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e) := by
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_def, complex_smul_def]

theorem exists_lift (F : Submodule (𝓞 L) E) {i : ℕ} (f : Fin i → F) (c : F →ₗ[𝓞 L] (Fin i → L))
    (hc : ∀ x, ∃ (D : 𝓞 L) (a : Fin i → 𝓞 L), D ≠ 0 ∧ D • x = ∑ j, a j • f j ∧
      ∀ j, (D : L) * c x j = a j)
    (x : Fin i → K)
    (hx : x ∈ Submodule.span (𝓞 K) ((fun (w : Fin i → L) j => algebraMap L K (w j)) ''
      (LinearMap.range c : Submodule (𝓞 L) (Fin i → L)))) :
    ∃ X : 𝓞 K ⊗[𝓞 L] E, ∀ τ : K →+* ℂ,
      baseChangeCoord τ ((1 : ComplexAt τ) ⊗ₜ[𝓞 K] X) =
        ∑ j, τ (x j) • ((1 : ComplexAt (τ.comp (algebraMap L K))) ⊗ₜ[𝓞 L] (f j : E)) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, ⟨y, rfl⟩, rfl⟩ := hx
    obtain ⟨D, a, hD, hDy, ha⟩ := hc y
    refine ⟨(1 : 𝓞 K) ⊗ₜ[𝓞 L] (y : E), fun τ => ?_⟩
    rw [coord_one_tmul]
    have hD' : ((D : 𝓞 L) : L) ≠ 0 := by exact_mod_cast hD
    have hσ : (τ.comp (algebraMap L K)) (D : L) ≠ 0 := (map_ne_zero _).2 hD'
    have h1 : D • (y : E) = ∑ j, a j • (f j : E) := by
      have := congrArg Subtype.val hDy
      simpa using this
    have H : (τ.comp (algebraMap L K)) (D : L) •
        ((1 : ComplexAt (τ.comp (algebraMap L K))) ⊗ₜ[𝓞 L] (y : E)) =
        (τ.comp (algebraMap L K)) (D : L) •
          ∑ j, τ (algebraMap L K (c y j)) •
            ((1 : ComplexAt (τ.comp (algebraMap L K))) ⊗ₜ[𝓞 L] (f j : E)) := by
      rw [← one_tmul_smul, h1, tmul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [one_tmul_smul, smul_smul, ← ha j, map_mul]
      rfl
    have H2 := congrArg (fun v => ((τ.comp (algebraMap L K)) (D : L))⁻¹ • v) H
    simp only [inv_smul_smul₀ hσ] at H2
    simpa using H2
  | zero => exact ⟨0, fun τ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨X, hX⟩ := hx
    obtain ⟨Y, hY⟩ := hy
    refine ⟨X + Y, fun τ => ?_⟩
    rw [tmul_add, map_add (f := _), hX, hY, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.add_apply, map_add (f := _), add_smul]
  | smul b x _ hx =>
    obtain ⟨X, hX⟩ := hx
    refine ⟨b • X, fun τ => ?_⟩
    rw [coord_smul, hX, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, Pi.smul_apply, Algebra.smul_def, map_mul]

theorem lift_length : ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (F : Submodule (𝓞 L) B.carrier) (i : ℕ) (f : Fin i → F) (c : F →ₗ[𝓞 L] (Fin i → L)), (∀ x, ∃ (D : 𝓞 L) (a : Fin i → 𝓞 L), D ≠ 0 ∧ D • x = ∑ j, a j • f j ∧ ∀ j, (D : L) * c x j = a j) → ∀ (K : Type) [Field K] [NumberField K] [Algebra L K] (x : Fin i → K), x ∈ Submodule.span (𝓞 K) ((fun (w : Fin i → L) j => algebraMap L K (w j)) '' (LinearMap.range c : Submodule (𝓞 L) (Fin i → L))) → ∃ X : (B.baseChange K).carrier, ∀ τ : K →+* ℂ, ((B.baseChange K).metric.form τ).inner ((1 : ComplexAt τ) ⊗ₜ[𝓞 K] X) ((1 : ComplexAt τ) ⊗ₜ[𝓞 K] X) = star (fun j => τ (x j)) ⬝ᵥ (gramMat B (τ.comp (algebraMap L K)) (fun j => (f j : B.carrier)) *ᵥ fun j => τ (x j)) := by
  intro L _ _ B F i f c hc K _ _ _ x hx
  obtain ⟨X, hX⟩ := exists_lift F f c hc x hx
  refine ⟨X, fun τ => ?_⟩
  change inner ℂ (FibreSpace.equiv B.metric (τ.comp (algebraMap L K))
      (baseChangeCoord τ ((1 : ComplexAt τ) ⊗ₜ[𝓞 K] X)))
    (FibreSpace.equiv B.metric (τ.comp (algebraMap L K))
      (baseChangeCoord τ ((1 : ComplexAt τ) ⊗ₜ[𝓞 K] X))) = _
  rw [hX τ]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [starRingEnd_apply]
  have e : gramMat B (τ.comp (algebraMap L K)) (fun j => (f j : B.carrier)) a b =
      inner ℂ (FibreSpace.equiv B.metric (τ.comp (algebraMap L K))
          ((1 : ComplexAt (τ.comp (algebraMap L K))) ⊗ₜ[𝓞 L] (f a : B.carrier)))
        (FibreSpace.equiv B.metric (τ.comp (algebraMap L K))
          ((1 : ComplexAt (τ.comp (algebraMap L K))) ⊗ₜ[𝓞 L] (f b : B.carrier))) := rfl
  rw [e]
  ring

end

end GlobalTheory.CompanionTheory.Ar.Lines.Lift
end

