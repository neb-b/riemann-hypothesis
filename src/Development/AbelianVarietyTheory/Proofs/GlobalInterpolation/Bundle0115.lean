module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraMapMemMaximalRealSubfieldIff
section
open NumberField IsDedekindDomain GlobalTheory.UnitaryBC

namespace GlobalTheory

theorem algebraMap_mem_maximalRealSubfield_iff {K L : Type} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (x : K) :
    algebraMap K L x ∈ maximalRealSubfield L ↔ x ∈ maximalRealSubfield K := by
  simp only [mem_maximalRealSubfield_iff]
  constructor
  · intro hL ψ
    let : Algebra K ℂ := ψ.toAlgebra
    let φ : L →ₐ[K] ℂ := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    have hφ : φ (algebraMap K L x) = ψ x := φ.commutes x
    rw [← hφ]
    exact hL φ.toRingHom
  · intro hK φ
    exact hK (φ.comp (algebraMap K L))

theorem isCMField_of_sq_eq_totallyPositive :
    ∀ (K L : Type) [Field K] [NumberField K] [IsCMField K] [Field L] [NumberField L] [Algebra K L], Module.finrank K L = 2 → ∀ (d : maximalRealSubfield K) (t : L), t ^ 2 = algebraMap K L d → t ∉ Set.range (algebraMap K L) → (∀ φ : maximalRealSubfield K →+* ℝ, 0 < φ d) → IsCMField L ∧ t ∈ maximalRealSubfield L ∧ ∀ x : K, algebraMap K L x ∈ maximalRealSubfield L ↔ x ∈ maximalRealSubfield K := by
  intro K L _ _ _ _ _ _ hKL d t ht2 htK hpos
  have : Module.Finite K L := Module.finite_of_finrank_pos (by omega)
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L

  have htR : t ∈ maximalRealSubfield L := by
    rw [mem_maximalRealSubfield_iff]
    intro φ
    let ρ : maximalRealSubfield K →+* ℂ :=
      (φ.comp (algebraMap K L)).comp (maximalRealSubfield K).subtype
    have hρ : ComplexEmbedding.IsReal ρ := IsTotallyReal.complexEmbedding_isReal ρ
    have hr : (0 : ℝ) < hρ.embedding d := hpos _
    have hsq : φ t * φ t = ((hρ.embedding d : ℝ) : ℂ) := by
      rw [ComplexEmbedding.IsReal.coe_embedding_apply, ← map_mul, ← pow_two, ht2]
      rfl
    have him : (φ t).im = 0 := by
      have h1 := congrArg Complex.re hsq
      have h2 := congrArg Complex.im hsq
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at h1 h2
      by_contra hne
      have hre : (φ t).re = 0 := by
        have h3 : (φ t).re * (φ t).im = 0 := by linarith
        rcases mul_eq_zero.mp h3 with h | h
        · exact h
        · exact absurd h hne
      rw [hre] at h1
      nlinarith [sq_nonneg (φ t).im]
    exact Complex.conj_eq_iff_im.mpr him

  have : IsScalarTower (maximalRealSubfield K) K L := inferInstance
  have hKp : Module.finrank (maximalRealSubfield K) K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have h4 : Module.finrank (maximalRealSubfield K) L = 4 := by
    rw [← Module.finrank_mul_finrank (maximalRealSubfield K) K L, hKp, hKL]
  have : Module.Finite (maximalRealSubfield K) L := Module.finite_of_finrank_pos (by omega)
  have hint : IsIntegral (maximalRealSubfield K) t := IsIntegral.of_finite _ t

  have hmin : (minpoly (maximalRealSubfield K) t).natDegree = 2 := by
    have hle : (minpoly (maximalRealSubfield K) t).degree ≤ ((2 : ℕ) : WithBot ℕ) := by
      have h := minpoly.degree_le_of_ne_zero (maximalRealSubfield K) t
        (Polynomial.X_pow_sub_C_ne_zero (n := 2) (by norm_num) d)
        (by rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, ht2]; exact sub_self _)
      rwa [Polynomial.degree_X_pow_sub_C (by norm_num)] at h
    have hne1 : (minpoly (maximalRealSubfield K) t).natDegree ≠ 1 := by
      rw [Ne, minpoly.natDegree_eq_one_iff]
      rintro ⟨y, hy⟩
      exact htK ⟨(y : K), hy⟩
    have hpos' := minpoly.natDegree_pos hint
    have h2 := Polynomial.natDegree_le_of_degree_le hle
    omega
  have hbase : ∀ y : maximalRealSubfield K,
      algebraMap (maximalRealSubfield K) L y ∈ maximalRealSubfield L :=
    fun y => (algebraMap_mem_maximalRealSubfield_iff (L := L) (y : K)).mpr y.2

  have hFdeg : Module.finrank (maximalRealSubfield K)
      (IntermediateField.adjoin (maximalRealSubfield K) ({t} : Set L)) = 2 := by
    rw [IntermediateField.adjoin.finrank hint, hmin]
  have hFle' : IntermediateField.adjoin (maximalRealSubfield K) ({t} : Set L) ≤
      (maximalRealSubfield L).toIntermediateField hbase :=
    IntermediateField.adjoin_simple_le_iff.mpr htR
  have hFle : ∀ y ∈ IntermediateField.adjoin (maximalRealSubfield K) ({t} : Set L),
      y ∈ maximalRealSubfield L := fun y hy => hFle' hy
  generalize IntermediateField.adjoin (maximalRealSubfield K) ({t} : Set L) = F at hFdeg hFle
  have hFL : Module.finrank F L = 2 := by
    have h := Module.finrank_mul_finrank (maximalRealSubfield K) F L
    rw [hFdeg, h4] at h
    omega
  have : Module.Finite F L := Module.finite_of_finrank_pos (by omega)
  let ι : F →+* maximalRealSubfield L :=
    { toFun := fun y => ⟨y.1, hFle y.1 y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let : Algebra F (maximalRealSubfield L) := ι.toAlgebra
  have : IsScalarTower F (maximalRealSubfield L) L := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsAlgebraic F L := Algebra.IsAlgebraic.of_finite F L
  have : Algebra.IsAlgebraic F (maximalRealSubfield L) :=
    Algebra.IsAlgebraic.tower_bot F (maximalRealSubfield L) L
  have : IsTotallyReal F := IsTotallyReal.of_algebra F (maximalRealSubfield L)
  have : Algebra.IsQuadraticExtension F L := ⟨hFL⟩
  have : IsTotallyComplex L := ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mp fun h =>
    InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex _)
      (InfinitePlace.IsReal.comap (algebraMap K L) h)⟩
  exact ⟨IsCMField.ofCMExtension F L, htR, fun x => algebraMap_mem_maximalRealSubfield_iff x⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousOfMem
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.CoordinateEmbeddingSplits

section General

variable {G : Type} [Mul G]

def Splits (A : Subalgebra ℂ (G → ℂ)) (p : G → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a b : ι → G → ℂ), (∀ i, a i ∈ A ∧ b i ∈ A) ∧
    ∀ x k, p (x * k) = ∑ i, a i x * b i k

theorem splits_adjoin (S : Set (G → ℂ)) (hS : ∀ p ∈ S, Splits (Algebra.adjoin ℂ S) p) :
    ∀ p ∈ Algebra.adjoin ℂ S, Splits (Algebra.adjoin ℂ S) p := by
  intro p hp
  induction hp using Algebra.adjoin_induction with
  | mem p hp => exact hS p hp
  | algebraMap c =>
    exact ⟨Unit, inferInstance, fun _ => algebraMap ℂ _ c, fun _ => 1,
      fun _ => ⟨Subalgebra.algebraMap_mem _ c, one_mem _⟩, fun x k => by simp⟩
  | add p q _ _ hp hq =>
    obtain ⟨ι, _, a, b, hab, h⟩ := hp
    obtain ⟨κ, _, c, d, hcd, h'⟩ := hq
    refine ⟨ι ⊕ κ, inferInstance, Sum.elim a c, Sum.elim b d, ?_, fun x k => ?_⟩
    · rintro (i | i)
      · exact hab i
      · exact hcd i
    · rw [Pi.add_apply, h, h', Fintype.sum_sum_type]
      rfl
  | mul p q _ _ hp hq =>
    obtain ⟨ι, _, a, b, hab, h⟩ := hp
    obtain ⟨κ, _, c, d, hcd, h'⟩ := hq
    refine ⟨ι × κ, inferInstance, fun t => a t.1 * c t.2, fun t => b t.1 * d t.2,
      fun t => ⟨mul_mem (hab _).1 (hcd _).1, mul_mem (hab _).2 (hcd _).2⟩, fun x k => ?_⟩
    rw [Pi.mul_apply, h, h', Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.mul_apply]
    ring

theorem Splits.fin {A : Subalgebra ℂ (G → ℂ)} {p : G → ℂ} (h : Splits A p) :
    ∃ (m : ℕ) (a b : Fin m → G → ℂ), (∀ i, a i ∈ A ∧ b i ∈ A) ∧
      ∀ x k, p (x * k) = ∑ i, a i x * b i k := by
  obtain ⟨ι, _, a, b, hab, h⟩ := h
  refine ⟨Fintype.card ι, fun i => a ((Fintype.equivFin ι).symm i), fun i => b ((Fintype.equivFin ι).symm i),
    fun i => hab _, fun x k => ?_⟩
  rw [h]
  exact (Equiv.sum_comp (Fintype.equivFin ι).symm fun i => a i x * b i k).symm

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

omit [NumberField E] [IsCMField E] in
theorem coord_star (τ : E →+* ℂ) (a : Cinf E) : coord τ (star a) = star (coord τ a) := by
  unfold coord
  split_ifs <;> rfl

omit [NumberField E] [IsCMField E] in
theorem continuous_coord (τ : E →+* ℂ) : Continuous (coord τ) := by
  unfold coord
  split_ifs
  · exact continuous_apply (InfinitePlace.mk τ)
  · exact Complex.continuous_conj.comp (continuous_apply (InfinitePlace.mk τ))

omit [NumberField E] [IsCMField E] in
theorem coord_embedding (w : InfinitePlace E) (a : Cinf E) : coord w.embedding a = a w := by
  unfold coord
  rw [InfinitePlace.mk_embedding, if_pos rfl]
  rfl

theorem coord_conjugate (τ : E →+* ℂ) (a : Cinf E) :
    coord (ComplexEmbedding.conjugate τ) a = star (coord τ a) := by
  have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
    (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ)))
      ⟨τ, ComplexEmbedding.isReal_iff.2 h, rfl⟩
  unfold coord
  rw [InfinitePlace.mk_conjugate_eq]
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · rw [if_pos h, if_neg (fun h' => hne (h'.symm.trans h))]
    rfl
  · rw [if_pos h, if_neg (fun h' => hne (h.symm.trans h'))]
    exact (star_star _).symm

theorem continuous_pInf : Continuous (pInf E) := by
  have : Continuous (infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (IsTotallyComplex.isComplex w)).continuous.comp (continuous_apply w)
  exact this.comp continuous_fst

theorem pInf_conj (a : Ad E) : pInf E (conjAd E a) = star (pInf E a) := by
  change (infEq E).symm (infEq E _) = _
  rw [RingEquiv.symm_apply_apply]
  rfl

theorem cEmb_apply (τ : E →+* ℂ) (x : UA E n) (i j : Fin n) :
    (cEmb τ x).val i j = coord τ (pInf E (x.1.val i j)) := rfl

theorem cEmb_inv (τ : E →+* ℂ) (x : UA E n) (i j : Fin n) :
    (cEmb τ x⁻¹).val i j = star ((cEmb τ x).val j i) := by
  have h : (x.1.val.map (conjAd E))ᵀ * 1 * x.1.val = 1 := x.2
  rw [Matrix.mul_one] at h
  have h2 : (x.1⁻¹).val = (x.1.val.map (conjAd E))ᵀ := Units.inv_eq_of_mul_eq_one_left h
  rw [cEmb_apply, cEmb_apply, ← coord_star, ← pInf_conj]
  exact congrArg (fun M : Matrix (Fin n) (Fin n) (Ad E) => coord τ (pInf E (M i j))) h2


variable (E n) in
abbrev coeffs : Set (infU E n → ℂ) :=
  {f | ∃ (τ : E →+* ℂ) (i : Fin n) (j : Fin n), f = fun x : infU E n => (cEmb τ x.val).val i j}

theorem continuous_of_mem (p : infU E n → ℂ) (hp : p ∈ Algebra.adjoin ℂ (coeffs E n)) : Continuous p := by
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨τ, i, j, rfl⟩ := hp
    have h : Continuous fun x : infU E n => x.1.1.val i j :=
      (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_elem i j
    exact (continuous_coord τ).comp (continuous_pInf.comp h)
  | algebraMap c => exact continuous_const
  | add p q _ _ hp hq => exact hp.add hq
  | mul p q _ _ hp hq => exact hp.mul hq

theorem star_mem_of_mem (p : infU E n → ℂ) (hp : p ∈ Algebra.adjoin ℂ (coeffs E n)) :
    star p ∈ Algebra.adjoin ℂ (coeffs E n) := by
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨τ, i, j, rfl⟩ := hp
    exact Algebra.subset_adjoin ⟨ComplexEmbedding.conjugate τ, i, j, funext fun x => (coord_conjugate τ _).symm⟩
  | algebraMap c => exact Subalgebra.algebraMap_mem _ (star c)
  | add p q _ _ hp hq => rw [star_add]; exact add_mem hp hq
  | mul p q _ _ hp hq => rw [star_mul]; exact mul_mem hq hp

theorem separates (x y : infU E n) (hxy : x ≠ y) : ∃ p ∈ Algebra.adjoin ℂ (coeffs E n), p x ≠ p y := by
  by_contra hcon
  refine hxy (Subtype.ext (Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))))
  have h1 : pInf E (x.1.1.val i j) = pInf E (y.1.1.val i j) := by
    funext w
    refine (coord_embedding w _).symm.trans (Eq.trans ?_ (coord_embedding w _))
    by_contra hne
    exact hcon ⟨_, Algebra.subset_adjoin ⟨w.embedding, i, j, rfl⟩, hne⟩
  have hx : GeneralLinearGroup.map (pFin E) x.1.1 = 1 := x.2
  have hy : GeneralLinearGroup.map (pFin E) y.1.1 = 1 := y.2
  have h2 := congrArg (fun g : GL (Fin n) (Af E) => g.val i j) (hx.trans hy.symm)
  exact Prod.ext ((infEq E).symm.injective h1) h2

theorem inv_mem_of_mem (p : infU E n → ℂ) (hp : p ∈ Algebra.adjoin ℂ (coeffs E n)) :
    (fun x => p x⁻¹) ∈ Algebra.adjoin ℂ (coeffs E n) := by
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨τ, i, j, rfl⟩ := hp
    have h := star_mem_of_mem (E := E) (n := n) _ (Algebra.subset_adjoin ⟨τ, j, i, rfl⟩)
    have e : (fun x : infU E n => (cEmb τ (x⁻¹).val).val i j) =
        star fun x : infU E n => (cEmb τ x.val).val j i := funext fun x => cEmb_inv τ x.1 i j
    exact e ▸ h
  | algebraMap c => exact Subalgebra.algebraMap_mem _ c
  | add p q _ _ hp hq => exact add_mem hp hq
  | mul p q _ _ hp hq => exact mul_mem hp hq

theorem splits_of_mem : ∀ p ∈ Algebra.adjoin ℂ (coeffs E n), Splits (Algebra.adjoin ℂ (coeffs E n)) p := by
  refine splits_adjoin _ ?_
  rintro _ ⟨τ, i, j, rfl⟩
  refine ⟨Fin n, inferInstance, fun l x => (cEmb τ x.val).val i l, fun l x => (cEmb τ x.val).val l j,
    fun l => ⟨Algebra.subset_adjoin ⟨τ, i, l, rfl⟩, Algebra.subset_adjoin ⟨τ, l, j, rfl⟩⟩, fun x k => ?_⟩
  change (cEmb τ (x.val * k.val)).val i j = _
  rw [map_mul, Units.val_mul, Matrix.mul_apply]

theorem main (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    (∀ p ∈ Algebra.adjoin ℂ (coeffs E n), Continuous p) ∧
    (∀ p ∈ Algebra.adjoin ℂ (coeffs E n), star p ∈ Algebra.adjoin ℂ (coeffs E n)) ∧
    (∀ x y : infU E n, x ≠ y → ∃ p ∈ Algebra.adjoin ℂ (coeffs E n), p x ≠ p y) ∧
    (∀ p ∈ Algebra.adjoin ℂ (coeffs E n), (fun x => p x⁻¹) ∈ Algebra.adjoin ℂ (coeffs E n)) ∧
    ∀ p ∈ Algebra.adjoin ℂ (coeffs E n), ∃ (m : ℕ) (a b : Fin m → infU E n → ℂ),
      (∀ i, a i ∈ Algebra.adjoin ℂ (coeffs E n) ∧ b i ∈ Algebra.adjoin ℂ (coeffs E n)) ∧
        ∀ x k : infU E n, p (x * k) = ∑ i, a i x * b i k :=
  ⟨continuous_of_mem, star_mem_of_mem, separates, inv_mem_of_mem, fun p hp => (splits_of_mem p hp).fin⟩

end GlobalTheory.CoordinateEmbeddingSplits

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CountableOfNumberField
section
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal Pointwise

noncomputable section

namespace GlobalTheory.SWQ

theorem countable_of_numberField (F : Type) [Field F] [NumberField F] : Countable F :=
  Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm

theorem map_unit_mul_eq (F : Type) [Field F] [NumberField F] (ν : Measure (AF F)) [ν.IsAddHaarMeasure]
    (w : (AF F)ˣ) : ν.map (fun x => w • x) = (distribHaarChar (AF F) w⁻¹ : ℝ≥0∞) • ν := by
  ext S hS
  rw [Measure.map_apply (measurable_const_smul w) hS, Set.preimage_smul, Measure.smul_apply, smul_eq_mul,
    distribHaarChar_mul]

theorem modrat_main : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ν : Measure (AF F)), IsCov1 ν →
    ∀ t : F, t ≠ 0 → ν.map (fun x => (algebraMap F (AF F) t) * x) = ν := by
  intro F _ _ _ ν hν t ht
  obtain ⟨hH, D, _, hD, hD1⟩ := hν
  haveI := hH
  haveI := countable_of_numberField F
  set K := (algebraMap F (AF F)).range.toAddSubgroup with hK
  haveI : Countable K := by
    refine Function.Surjective.countable (f := fun r : F => (⟨algebraMap F (AF F) r, ⟨r, rfl⟩⟩ : K)) ?_
    rintro ⟨x, ⟨r, rfl⟩⟩
    exact ⟨r, rfl⟩
  have htu : IsUnit (algebraMap F (AF F) t) := (isUnit_iff_ne_zero.mpr ht).map _
  set u : (AF F)ˣ := htu.unit with hu
  have hmul : (fun x : AF F => (algebraMap F (AF F) t) * x) = fun x => u • x := by
    funext x; rfl
  rw [hmul]

  let e : K ≃ K :=
    { toFun := fun g => ⟨algebraMap F (AF F) t⁻¹ * g, by
        obtain ⟨r, hr⟩ := g.2; exact ⟨t⁻¹ * r, by rw [map_mul, hr]⟩⟩
      invFun := fun g => ⟨algebraMap F (AF F) t * g, by
        obtain ⟨r, hr⟩ := g.2; exact ⟨t * r, by rw [map_mul, hr]⟩⟩
      left_inv := fun g => by
        ext; simp only; rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]
      right_inv := fun g => by
        ext; simp only; rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ht, map_one, one_mul] }
  have hqmp : Measure.QuasiMeasurePreserving (MulAction.toPerm u).symm ν ν := by
    refine ⟨(measurable_const_smul u⁻¹).aemeasurable, ?_⟩
    have : ⇑(MulAction.toPerm u).symm = fun x : AF F => u⁻¹ • x := rfl
    rw [this, map_unit_mul_eq F ν u⁻¹]
    exact Measure.AbsolutelyContinuous.smul_left (Measure.AbsolutelyContinuous.refl _) _
  have hD' : IsAddFundamentalDomain K (MulAction.toPerm u '' D) ν := by
    refine hD.image_of_equiv (MulAction.toPerm u) hqmp e ?_
    intro g x
    change u • ((e g : AF F) + x) = (g : AF F) + u • x
    change algebraMap F (AF F) t * (algebraMap F (AF F) t⁻¹ * (g : AF F) + x) = (g : AF F) + algebraMap F (AF F) t * x
    rw [mul_add, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]
  have himg : (MulAction.toPerm u '' D) = u • D := rfl
  have h1 : ν (u • D) = 1 := by rw [← himg, hD'.measure_eq hD, hD1]
  have hchar : distribHaarChar (AF F) u = 1 := by
    have := distribHaarChar_mul ν u D
    rw [h1, hD1, mul_one] at this
    exact_mod_cast this
  rw [map_unit_mul_eq F ν u, map_inv, hchar, inv_one, ENNReal.coe_one, one_smul]

end GlobalTheory.SWQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAdelesHaarMeasureCovolumeOne
section
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.SWQ

theorem exists_adeles_haarMeasure_covolume_one : ∀ (F : Type) [Field F] [NumberField F], ∃ ν : Measure (AF F), IsCov1 ν := by
  intro F _ _
  let Γ : AddSubgroup (AF F) := (algebraMap F (AF F)).range.toAddSubgroup
  have hdisc : DiscreteTopology Γ := by
    obtain ⟨U, hU, hU0⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
    obtain ⟨V, hVU, hVo, h0V⟩ := mem_nhds_iff.1 hU
    rw [discreteTopology_iff_isOpen_singleton_zero]
    have : ({0} : Set Γ) = ((↑) : Γ → AF F) ⁻¹' V := by
      ext ⟨x, hx⟩
      obtain ⟨y, rfl⟩ := hx
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · intro h
        have : algebraMap F (AF F) y = 0 := congrArg Subtype.val h
        rw [this]; exact h0V
      · intro h
        have := hU0 y (hVU h)
        subst this
        ext; simp
    rw [this]
    exact hVo.preimage continuous_subtype_val
  letI : MeasurableSpace (Multiplicative (AF F)) := borel _
  haveI : BorelSpace (Multiplicative (AF F)) := ⟨rfl⟩
  haveI : SecondCountableTopology (Multiplicative (AF F)) := inferInstanceAs (SecondCountableTopology (AF F))
  haveI : DiscreteTopology (AddSubgroup.toSubgroup Γ) := hdisc
  obtain ⟨hc, D, hDm, hD⟩ := GlobalTheory.discreteSubgroup_countable_and_exists_strict_fundamentalDomain (AddSubgroup.toSubgroup Γ)
  haveI : Countable Γ := hc
  let D' : Set (AF F) := Multiplicative.ofAdd ⁻¹' D
  have hDm' : MeasurableSet D' := hDm
  have hfd : ∀ m : Measure (AF F), IsAddFundamentalDomain Γ D' m := by
    intro m
    refine IsAddFundamentalDomain.mk' hDm'.nullMeasurableSet ?_
    intro x
    obtain ⟨γ, hγ, huniq⟩ := hD (Multiplicative.ofAdd x)
    refine ⟨⟨γ.1.toAdd, γ.2⟩, hγ, ?_⟩
    intro g hg
    have := huniq ⟨Multiplicative.ofAdd g.1, g.2⟩ hg
    ext
    exact congrArg (fun s => Multiplicative.toAdd s.1) this
  let μ : Measure (AF F) := Measure.addHaar
  have hμD := hfd μ
  obtain ⟨K, hK, hKx⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  have hfin : μ D' < ∞ := by
    calc μ D' ≤ μ (⋃ γ : Γ, (γ +ᵥ K) ∩ D') := by
          apply measure_mono
          intro d hd
          obtain ⟨x, hx⟩ := hKx d
          refine Set.mem_iUnion.2 ⟨⟨algebraMap F (AF F) x, x, rfl⟩, ?_, hd⟩
          refine ⟨_, hx, ?_⟩
          show algebraMap F (AF F) x + (d - algebraMap F (AF F) x) = d
          abel
      _ ≤ ∑' γ : Γ, μ ((γ +ᵥ K) ∩ D') := measure_iUnion_le _
      _ = μ K := (hμD.measure_eq_tsum K).symm
      _ < ∞ := hK.measure_lt_top
  have hpos : μ D' ≠ 0 := by
    intro h0
    have := hμD.measure_eq_tsum' Set.univ
    simp only [Set.univ_inter] at this
    have h2 : ∀ g : Γ, μ (g +ᵥ D') = 0 := fun g => by
      rw [measure_vadd]; exact h0
    simp only [h2, tsum_zero] at this
    exact (Measure.measure_univ_ne_zero.2 (NeZero.ne μ)) this
  refine ⟨(μ D')⁻¹ • μ, ?_, D', hDm', hfd _, ?_⟩
  · exact Measure.IsAddHaarMeasure.smul (μ := μ) (ENNReal.inv_ne_zero.2 hfin.ne) (ENNReal.inv_ne_top.2 hpos)
  · rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hpos hfin.ne]

end GlobalTheory.SWQ
end

