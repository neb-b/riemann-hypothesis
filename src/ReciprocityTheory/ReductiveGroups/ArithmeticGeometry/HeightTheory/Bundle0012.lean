module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0010
public import ReciprocityTheory.SemistableReduction.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0008
public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.KTFiniteDimensional
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem KTtoS_fieldRange (h : d.S1) (c : ι) :
    (d.KTtoS h c).fieldRange = (d.KT c).toSubfield := by
  have hval : ∀ p : (KTp K d.D d.N), d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) p) =
      MvPolynomial.aeval (sImg (d.jc c) (d.x c)) p := by
    intro p
    simp only [KTtoS]
    rw [IsFractionRing.lift_algebraMap]
    rfl
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := (KTp K d.D d.N)) z
    have hmem : ∀ p : (KTp K d.D d.N), d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) p) ∈ (d.KT c).toSubfield := by
      intro p
      rw [hval]
      show _ ∈ IntermediateField.adjoin K (Set.range (sImg (d.jc c) (d.x c)))
      apply IntermediateField.algebra_adjoin_le_adjoin
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨p, rfl⟩
    rw [map_div₀]
    exact (d.KT c).toSubfield.div_mem (hmem a) (hmem b)
  · intro y hy
    have hE : IntermediateField.adjoin K (Set.range (sImg (d.jc c) (d.x c))) ≤
        { (d.KTtoS h c).fieldRange with
          algebraMap_mem' := fun k => (d.KTtoS h c).mem_fieldRange.2
            ⟨algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (MvPolynomial.C k), by rw [hval, MvPolynomial.aeval_C]⟩ } := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨v, rfl⟩
      exact (d.KTtoS h c).mem_fieldRange.2
        ⟨algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (MvPolynomial.X v), by rw [hval, MvPolynomial.aeval_X]⟩
    exact hE hy

theorem KT_finiteDimensional (hd : d.AxH 𝒜) (c : ι) :
    FiniteDimensional (d.KT c) (OmS (Ω c) d.D d.N) := by
  have hfs := ReciprocityTheory.MultiplicativeHeights.Closed.fieldOfS K (Ω c) d.D d.N (d.x c) (hd.fg c) (hd.trdeg c) (hd.a1 c)
  let e : TVar d.D d.N ≃ TVar d.D d.N :=
    Equiv.prodCongr (Equiv.refl _) (Fin.cycleRange (d.jc c)).symm
  have key : (ReciprocityTheory.MultiplicativeHeights.sImage (D := d.D) (d.x c)) = (sImg (D := d.D) (d.jc c) (d.x c)) ∘ e := by
    funext p
    obtain ⟨i, j⟩ := p
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [e, ReciprocityTheory.MultiplicativeHeights.sImage, sImg, Fin.cycleRange_symm_zero]
    · simp [e, ReciprocityTheory.MultiplicativeHeights.sImage, sImg, Fin.cycleRange_symm_succ]
  have hrange : Set.range (ReciprocityTheory.MultiplicativeHeights.sImage (D := d.D) (d.x c)) =
      Set.range (sImg (D := d.D) (d.jc c) (d.x c)) := by
    rw [key, EquivLike.range_comp]
  have h2 := hfs.2
  rw [hrange] at h2
  exact h2

theorem omS_finite (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra;
    FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) ∧
      Module.finrank (KTf K d.D d.N) (OmS (Ω c) d.D d.N) = d.delc c := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  haveI := d.KT_finiteDimensional hd c
  have hfr := d.KTtoS_fieldRange h c
  let e : (KTf K d.D d.N) ≃+* (d.KT c) :=
    ((d.KTtoS h c).rangeRestrictFieldEquiv).trans (RingEquiv.subfieldCongr hfr)
  have he : ∀ z, ((e z : d.KT c) : (OmS (Ω c) d.D d.N)) = d.KTtoS h c z := fun z => rfl
  have hc : (algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)).comp e.symm.toRingHom =
      (RingEquiv.refl (OmS (Ω c) d.D d.N)).toRingHom.comp (algebraMap (d.KT c) (OmS (Ω c) d.D d.N)) := by
    refine RingHom.ext fun y => ?_
    show d.KTtoS h c (e.symm y) = (y : (OmS (Ω c) d.D d.N))
    rw [← he, RingEquiv.apply_symm_apply]
  refine ⟨Module.Finite.of_equiv_equiv e.symm (RingEquiv.refl _) hc, ?_⟩
  rw [show d.delc c = Module.finrank (d.KT c) (OmS (Ω c) d.D d.N) from rfl]
  exact (Algebra.finrank_eq_of_equiv_equiv e.symm (RingEquiv.refl _) hc).symm

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.OffBaseSubstitution
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

namespace FractionFieldVariableLift

def eT (D N : ℕ) : TVar D N ≃ Fin (N + 1) ⊕ {v : TVar D N // v.1 ≠ 0} where
  toFun v := if h : v.1 = 0 then Sum.inl v.2 else Sum.inr ⟨v, h⟩
  invFun := Sum.elim (fun j => ((0 : Fin (D + 1)), j)) Subtype.val
  left_inv v := by
    by_cases h : v.1 = 0
    · simp only [h, dite_true, Sum.elim_inl]; exact Prod.ext h.symm rfl
    · simp [h]
  right_inv s := by
    rcases s with j | ⟨v, hv⟩
    · simp
    · simp [hv]

noncomputable def eS (D N : ℕ) (j0 : Fin (N + 1)) :
    SVar D N ≃ Fin (N + 1) ⊕ ({i : Fin (D + 1) // i ≠ 0} × Fin N) where
  toFun s := match s with
    | Sum.inl _ => Sum.inl j0
    | Sum.inr p => if h : p.1 = 0 then Sum.inl (j0.succAbove p.2) else Sum.inr (⟨p.1, h⟩, p.2)
  invFun t := match t with
    | Sum.inl j => if h : j = j0 then Sum.inl () else Sum.inr (0, (Fin.exists_succAbove_eq h).choose)
    | Sum.inr q => Sum.inr (q.1.1, q.2)
  left_inv s := by
    rcases s with u | ⟨i, k⟩
    · simp
    · by_cases h : i = 0
      · subst h
        have hne : j0.succAbove k ≠ j0 := Fin.succAbove_ne j0 k
        simp only [dite_true, hne, dite_false]
        congr
        exact Fin.succAbove_right_injective (Fin.exists_succAbove_eq hne).choose_spec
      · simp [h]
  right_inv t := by
    rcases t with j | ⟨⟨i, hi⟩, k⟩
    · by_cases h : j = j0
      · subst h; simp
      · simp only [h, dite_false, dite_true]
        exact congrArg Sum.inl (Fin.exists_succAbove_eq h).choose_spec
    · simp [hi]

noncomputable def hL (K : Type) [Field K] (D N : ℕ) :
    KTp K D N ≃+* MvPolynomial (Fin (N + 1)) (MvPolynomial {v : TVar D N // v.1 ≠ 0} K) :=
  (MvPolynomial.renameEquiv K (eT D N)).toRingEquiv.trans (MvPolynomial.sumRingEquiv K _ _)

noncomputable def hE (Ω : Type) [Field Ω] (D N : ℕ) (j0 : Fin (N + 1)) :
    MvPolynomial (SVar D N) Ω ≃+*
      MvPolynomial (Fin (N + 1)) (MvPolynomial ({i : Fin (D + 1) // i ≠ 0} × Fin N) Ω) :=
  (MvPolynomial.renameEquiv Ω (eS D N j0)).toRingEquiv.trans (MvPolynomial.sumRingEquiv Ω _ _)

variable {K : Type} [Field K] {Ω : Type} [Field Ω] {D N : ℕ}

theorem hL_C (r : K) : hL K D N (MvPolynomial.C r) = MvPolynomial.C (MvPolynomial.C r) := by
  simp [hL, MvPolynomial.sumRingEquiv_C, MvPolynomial.sumRingEquiv_X_inl, MvPolynomial.sumRingEquiv_X_inr]

theorem hL_X (v : TVar D N) : hL K D N (MvPolynomial.X v) =
    if h : v.1 = 0 then MvPolynomial.X v.2 else MvPolynomial.C (MvPolynomial.X ⟨v, h⟩) := by
  by_cases h : v.1 = 0
  · simp [hL, eT, h, MvPolynomial.sumRingEquiv_C, MvPolynomial.sumRingEquiv_X_inl, MvPolynomial.sumRingEquiv_X_inr]
  · simp [hL, eT, h, MvPolynomial.sumRingEquiv_C, MvPolynomial.sumRingEquiv_X_inl, MvPolynomial.sumRingEquiv_X_inr]

theorem hL_rename (p : MvPolynomial {v : TVar D N // v.1 ≠ 0} K) :
    hL K D N (MvPolynomial.rename Subtype.val p) = MvPolynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.rename_C, hL_C]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p n hp => rw [map_mul, map_mul, hp, MvPolynomial.rename_X, hL_X, dif_neg n.2, map_mul]

theorem hE_C (j0 : Fin (N + 1)) (r : Ω) :
    hE Ω D N j0 (MvPolynomial.C r) = MvPolynomial.C (MvPolynomial.C r) := by
  simp [hE, MvPolynomial.sumRingEquiv_C, MvPolynomial.sumRingEquiv_X_inl, MvPolynomial.sumRingEquiv_X_inr]

end FractionFieldVariableLift

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def offBaseSubstitution (c : ι) :
    MvPolynomial {v : TVar d.D d.N // v.1 ≠ 0} K →ₐ[K]
      MvPolynomial ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (Ω c) :=
  MvPolynomial.aeval fun v =>
    Fin.succAboveCases (α := fun _ => MvPolynomial ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (Ω c))
      (d.jc c) (-∑ k, MvPolynomial.X (⟨v.1.1, v.2⟩, k) * MvPolynomial.C (d.x c k))
      (fun k => MvPolynomial.X (⟨v.1.1, v.2⟩, k)) v.1.2

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.OrthogonalProjectorMulVecConjugate
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open Matrix NumberField ComplexConjugate NumberField.ComplexEmbedding
open scoped ComplexOrder Kronecker

section Gram

variable {K : Type} [Field K] [NumberField K] {r k m : ℕ}

theorem embeddingColumns_conjugate (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    hBm (conjugate σ) b = (hBm σ b).map (starRingEnd ℂ) := by
  ext l j
  simp [hBm, NumberField.ComplexEmbedding.conjugate_coe_eq]

private lemma map_star_inv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    A⁻¹.map (starRingEnd ℂ) = (A.map (starRingEnd ℂ))⁻¹ := by
  have h : ∀ M : Matrix (Fin n) (Fin n) ℂ, M.map (starRingEnd ℂ) = Mᴴᵀ := by
    intro M
    ext i j
    simp [conjTranspose_apply]
  rw [h, h, ← transpose_nonsing_inv, conjTranspose_nonsing_inv]

theorem orthogonalProjector_conjugate (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b) :
    hPm (conjugate σ) b = (hPm σ b).map (starRingEnd ℂ) := by
  unfold hPm
  rw [embeddingColumns_conjugate σ b]
  have h1 : ((hBm σ b).map (starRingEnd ℂ))ᴴ = (hBm σ b)ᴴ.map (starRingEnd ℂ) := by
    ext i j
    simp [conjTranspose_apply]
  rw [h1, ← Matrix.map_mul, ← map_star_inv, Matrix.map_sub _ (map_sub _),
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul, Matrix.map_mul]

theorem orthogonalProjector_mulVec_conjugate (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (x : Fin r → K) :
    (hPm (conjugate σ) b *ᵥ fun l => (conjugate σ) (x l)) = star (hPm σ b *ᵥ fun l => σ (x l)) := by
  rw [orthogonalProjector_conjugate σ hb]
  ext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, NumberField.ComplexEmbedding.conjugate_coe_eq, map_sum,
    mul_comm]

theorem conj_sum_projected_inner (b : Fin k → Fin r → K) (hb : LinearIndependent K b) (a a' : K)
    (x y : Fin r → K) :
    conj (∑ σ : K →+* ℂ, conj (σ a) * σ a' *
        (star (hPm σ b *ᵥ fun l => σ (x l)) ⬝ᵥ (hPm σ b *ᵥ fun l => σ (y l)))) =
      ∑ σ : K →+* ℂ, conj (σ a) * σ a' *
        (star (hPm σ b *ᵥ fun l => σ (x l)) ⬝ᵥ (hPm σ b *ᵥ fun l => σ (y l))) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  have hinv : Function.Involutive (NumberField.ComplexEmbedding.conjugate (K := K)) := by
    intro σ
    ext z
    simp [NumberField.ComplexEmbedding.conjugate_coe_eq]
  refine Fintype.sum_bijective _ hinv.bijective _ _ (fun σ => ?_)
  rw [orthogonalProjector_mulVec_conjugate σ hb x, orthogonalProjector_mulVec_conjugate σ hb y,
    NumberField.ComplexEmbedding.conjugate_coe_eq, NumberField.ComplexEmbedding.conjugate_coe_eq]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [dotProduct, map_sum, mul_comm, mul_left_comm]

theorem quotientGram_conjTranspose (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (c : Fin m → Fin r → K) : (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c)ᴴ = ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c := by
  unfold ReciprocityTheory.MultiplicativeHeights.quotGramC
  simp only [gramMatrix_eq_embeddingColumns, crossGram_eq_embeddingColumns, conjTranspose_sub, conjTranspose_mul,
    conjTranspose_conjTranspose, conjTranspose_nonsing_inv, Matrix.mul_assoc]

theorem quotientGram_det_re_eq (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (c : Fin m → Fin r → K) :
    (((ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det.re : ℝ) : ℂ) = (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det := by
  have h := quotientGram_conjTranspose σ hb c
  have h2 : star (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det = (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det := by
    rw [← det_conjTranspose, h]
  exact Complex.conj_eq_iff_re.mp h2

end Gram

section GramDet

variable {K : Type} [Field K] [NumberField K] {r k m : ℕ}

noncomputable def hwv (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) :
    Fin m × Module.Free.ChooseBasisIndex ℤ (𝓞 K) → EuclideanSpace ℝ (hIdx K r) :=
  fun p => hpv b (integralBasis K p.2 • c p.1)

theorem det_gram_projectedLatticeVectors (b : Fin k → Fin r → K) (hb : LinearIndependent K b)
    (c : Fin m → Fin r → K) :
    (gram ℝ (hwv b c)).det =
      |(discr K : ℝ)| ^ m * ∏ σ : K →+* ℂ, (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det.re := by
  classical
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = Fintype.card (K →+* ℂ) := by
    rw [NumberField.Embeddings.card, ← NumberField.RingOfIntegers.rank,
      Module.finrank_eq_card_chooseBasisIndex]
  obtain ⟨e⟩ : Nonempty (Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ (K →+* ℂ)) :=
    ⟨Fintype.equivOfCardEq hcard⟩
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 K))
      (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) ℂ, Ω = Matrix.of fun q p => e q (integralBasis K p) :=
    ⟨_, rfl⟩

  have hent : ∀ j p j' p', ((gram ℝ (hwv b c) (j, p) (j', p') : ℝ) : ℂ) =
      ∑ q, star (Ω q p) * ReciprocityTheory.MultiplicativeHeights.quotGramC 1 (e q) b c j j' * Ω q p' := by
    intro j p j' p'
    rw [Matrix.gram_apply]
    simp only [hwv]
    rw [inner_projectedVector_smul, Complex.conj_eq_iff_re.mp (conj_sum_projected_inner b hb _ _ _ _)]
    symm
    refine Fintype.sum_equiv e _ _ (fun q => ?_)
    rw [quotientGram_eq_projector (e q) hb c j j', hΩ]
    simp only [Matrix.of_apply]
    rw [show star ((e q) (integralBasis K p)) = conj ((e q) (integralBasis K p)) from rfl]
    ring
  have hmat : (gram ℝ (hwv b c)).map Complex.ofRealHom =
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Ω)ᴴ *
        Matrix.blockDiagonal (fun q => ReciprocityTheory.MultiplicativeHeights.quotGramC 1 (e q) b c) *
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Ω) := by
    ext ⟨j, p⟩ ⟨j', p'⟩
    rw [Matrix.map_apply, Complex.ofRealHom_eq_coe, hent]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.blockDiagonal_apply, Matrix.one_apply, ite_mul, mul_ite,
      Finset.sum_ite_eq, Finset.sum_ite_eq', apply_ite (starRingEnd ℂ), map_zero]
  have hdet : ((gram ℝ (hwv b c)).det : ℂ) =
      star ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Ω).det *
        (Matrix.blockDiagonal (fun q => ReciprocityTheory.MultiplicativeHeights.quotGramC 1 (e q) b c)).det *
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Ω).det := by
    have h := RingHom.map_det Complex.ofRealHom (gram ℝ (hwv b c))
    rw [Complex.ofRealHom_eq_coe] at h
    rw [h, RingHom.mapMatrix_apply, hmat, det_mul, det_mul, det_conjTranspose]
  have hT : ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Ω).det = Ω.det ^ m := by
    simp [Matrix.det_kronecker]
  have hdisc : Ω.det ^ 2 = (discr K : ℂ) := by
    have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ (integralBasis K)
      (e.trans (RingHom.equivRatAlgHom K ℂ))
    rw [← NumberField.coe_discr] at h1
    have h2 : Algebra.embeddingsMatrixReindex ℚ ℂ (integralBasis K)
        (e.trans (RingHom.equivRatAlgHom K ℂ)) = Ωᵀ := by
      ext i j
      simp [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, hΩ, RingHom.equivRatAlgHom]
    rw [h2, det_transpose] at h1
    rw [← h1]
    simp
  have hnorm : star Ω.det * Ω.det = ((|(discr K : ℝ)| : ℝ) : ℂ) := by
    rw [show star Ω.det = conj Ω.det from rfl, Complex.conj_mul', ← Complex.ofReal_pow, ← norm_pow,
      hdisc, Complex.norm_intCast]
  apply Complex.ofReal_injective
  rw [hdet, hT, Matrix.det_blockDiagonal]
  push_cast
  rw [← Equiv.prod_comp e (fun σ => (((ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det.re : ℝ) : ℂ))]
  simp_rw [quotientGram_det_re_eq _ hb c]
  rw [star_pow, ← hnorm]
  ring

end GramDet

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegVert
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open IsLocalRing

theorem regVert_eq_of_le_height_one {A : Type*} [CommRing A] [IsDomain A] {Q P : Ideal A} [Q.IsPrime]
    [P.IsPrime] (hQ : Q ≠ ⊥) (hQP : Q ≤ P) (hP : P.height = 1) : Q = P := by
  by_contra hne
  have hlt : Q < P := lt_of_le_of_ne hQP hne
  have hbot : (⊥ : Ideal A) < Q := bot_lt_iff_ne_bot.mpr hQ
  have hQle : Q.height ≤ 1 := hP ▸ Ideal.height_mono hQP
  have hQfin : Q.height ≠ ⊤ := ne_top_of_le_ne_top (by simp) hQle
  haveI : Q.FiniteHeight := ⟨Or.inr hQfin⟩
  haveI : (⊥ : Ideal A).FiniteHeight := ⟨Or.inr (by simp)⟩
  have h1 : (⊥ : Ideal A).height + 1 ≤ Q.height := by
    first
    | exact ENat.add_one_le_of_lt (Ideal.height_strict_mono_of_isPrime hbot)
    | exact Order.add_one_le_of_lt (Ideal.height_strict_mono_of_isPrime hbot)
  have h2 : Q.height + 1 ≤ P.height := by
    first
    | exact ENat.add_one_le_of_lt (Ideal.height_strict_mono_of_isPrime hlt)
    | exact Order.add_one_le_of_lt (Ideal.height_strict_mono_of_isPrime hlt)
  rw [hP] at h2
  have h3 : (2 : ℕ∞) ≤ 1 := by
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ (⊥ : Ideal A).height + 1 + 1 := by gcongr; simp
      _ ≤ Q.height + 1 := by gcongr
      _ ≤ 1 := h2
  exact absurd h3 (by norm_num)

theorem regVert_valuationRing {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (P : Ideal A) [P.IsPrime] (hP : P.height = 1) :
    ValuationRing (Localization.AtPrime P) := by
  have hPne : P ≠ ⊥ := by
    rintro rfl
    have h0 : (⊥ : Ideal A).height = 0 := by
      first
      | exact Ideal.height_bot
      | simp
    rw [h0] at hP
    exact zero_ne_one hP
  haveI : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime P)) :=
    IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors
  have hmax : Ideal.map (algebraMap A (Localization.AtPrime P)) P =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
    Localization.AtPrime.map_eq_maximalIdeal
  have hcm : Ideal.comap (algebraMap A (Localization.AtPrime P))
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) = P := by
    first
    | exact Localization.AtPrime.under_maximalIdeal
    | exact IsLocalization.AtPrime.comap_maximalIdeal _ P
  have hmne : IsLocalRing.maximalIdeal (Localization.AtPrime P) ≠ ⊥ := by
    rw [← hmax]
    intro h
    exact hPne ((Ideal.map_eq_bot_iff_of_injective hinj).mp h)
  have hnf : ¬ IsField (Localization.AtPrime P) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq]
    exact hmne
  haveI : IsDomain (Localization.AtPrime P) := by
    first
    | infer_instance
    | exact IsLocalization.isDomain_localization P.primeCompl_le_nonZeroDivisors
  haveI hic : IsIntegrallyClosed (Localization.AtPrime P) := by
    first
    | exact isIntegrallyClosed_of_isLocalization P.primeCompl P.primeCompl_le_nonZeroDivisors
    | exact isIntegrallyClosed_of_isLocalization (S := Localization.AtPrime P) P.primeCompl
        P.primeCompl_le_nonZeroDivisors
    | exact IsIntegrallyClosed.of_isLocalization (Localization.AtPrime P) P.primeCompl
        P.primeCompl_le_nonZeroDivisors
    | exact isIntegrallyClosed_of_isLocalization (Localization.AtPrime P) P.primeCompl
        P.primeCompl_le_nonZeroDivisors
  have huniq : ∃! Q' : Ideal (Localization.AtPrime P), Q' ≠ ⊥ ∧ Q'.IsPrime := by
    refine ⟨IsLocalRing.maximalIdeal _, ⟨hmne, inferInstance⟩, ?_⟩
    rintro Q' ⟨hQ'ne, hQ'p⟩
    haveI := hQ'p
    have hc : Q'.under A ≤ P := by
      exact (Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ'p.ne_top)).trans hcm.le
    have hcne : Q'.under A ≠ ⊥ := by
      intro h
      apply hQ'ne
      rw [← IsLocalization.map_under P.primeCompl (Localization.AtPrime P) Q', h, Ideal.map_bot]
    have heq := regVert_eq_of_le_height_one hcne hc hP
    rw [← IsLocalization.map_under P.primeCompl (Localization.AtPrime P) Q', heq, hmax]
  first
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 3).mpr (And.intro hic huniq)
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 4).mpr (And.intro hic huniq)
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 2).mpr (And.intro hic huniq)
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 5).mpr (And.intro hic huniq)
  | exact @ValuationRing.of_isDiscreteValuationRing _ _ _ (((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 4).mpr (And.intro hic huniq))
  | exact @ValuationRing.of_isDiscreteValuationRing _ _ _ (((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 5).mpr (And.intro hic huniq))
  | exact @ValuationRing.of_isDiscreteValuationRing _ _ _ (((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 3).mpr (And.intro hic huniq))
  | exact @ValuationRing.of_isDiscreteValuationRing _ _ _ (((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 6).mpr (And.intro hic huniq))
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 2 3).mpr (And.intro hic huniq)
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 2 4).mpr (And.intro hic huniq)
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 2 5).mpr (And.intro hic huniq)

end ReciprocityTheory.ChartRestriction.G.T0
end

