module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0035
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientS
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0042
public import Formalism.LocalToGlobal.HermitianForms.TiedSym
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualLatticeDifferentIndex
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex GlobalTheory.Idele WithZero
open scoped nonZeroDivisors

namespace GlobalTheory.StdDual

variable (F : Type) [Field F] [NumberField F]

theorem traceInf_algebraMap (x : F) :
    traceInf F (algebraMap F (Ainf F) x) = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  first
  | exact @_root_.GlobalTheory.TraceSumRealEmbeddings.traceInf_algebraMap
  | exact _root_.GlobalTheory.TraceSumRealEmbeddings.traceInf_algebraMap
  | (apply _root_.GlobalTheory.TraceSumRealEmbeddings.traceInf_algebraMap <;> assumption)
  | (intros; apply _root_.GlobalTheory.TraceSumRealEmbeddings.traceInf_algebraMap <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TraceSumRealEmbeddings.traceInf_algebraMap <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TraceSumRealEmbeddings.traceInf_algebraMap ..)

variable {F}

theorem char_fin_algebraMap {ψ : AddChar (AF F) ℂ} (h : IsStdChar F ψ) (x : F) :
    ψ (pairA F 0 (algebraMap F (Af F) x)) =
      Complex.exp (((Algebra.trace ℚ F x : ℚ) : ℂ) * (2 * Real.pi * Complex.I)) := by
  have e : pairA F 0 (algebraMap F (Af F) x) =
      algebraMap F (AF F) x + pairA F (algebraMap F (Ainf F) (-x)) 0 := by
    refine Prod.ext ?_ (add_zero _).symm
    show (0 : Ainf F) = algebraMap F (Ainf F) x + algebraMap F (Ainf F) (-x)
    rw [map_neg, add_neg_cancel]
  have h2 := h.2 (algebraMap F (Ainf F) (-x))
  rw [psiInf] at h2
  rw [e, AddChar.map_add_eq_mul, h.1.2.2.1, one_mul, h2, stdInf, traceInf_algebraMap, map_neg]
  congr 1
  push_cast
  ring

theorem char_fin_algebraMap_eq_one_iff {ψ : AddChar (AF F) ℂ} (h : IsStdChar F ψ) (x : F) :
    ψ (pairA F 0 (algebraMap F (Af F) x)) = 1 ↔
      Algebra.trace ℚ F x ∈ (algebraMap ℤ ℚ).range := by
  rw [char_fin_algebraMap h, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have := mul_right_cancel₀ Complex.two_pi_I_ne_zero hn
    rw [eq_intCast]
    exact_mod_cast this.symm
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [← hn, eq_intCast, Rat.cast_intCast]⟩


variable (F) in
abbrev codiff : FractionalIdeal (𝓞 F)⁰ F := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)

theorem codiff_ne_zero : codiff F ≠ 0 :=
  FractionalIdeal.dual_ne_zero ℤ ℚ (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))

theorem one_le_codiff : 1 ≤ codiff F := FractionalIdeal.one_le_dual_one ℤ ℚ

theorem mem_codiff_iff {ψ : AddChar (AF F) ℂ} (h : IsStdChar F ψ) (x : F) :
    x ∈ codiff F ↔ ∀ a : 𝓞 F, ψ (pairA F 0 (algebraMap F (Af F) ((a : F) * x))) = 1 := by
  rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))]
  simp_rw [char_fin_algebraMap_eq_one_iff h, Algebra.traceForm_apply]
  constructor
  · intro H a
    rw [mul_comm]
    exact H _ ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)
  · intro H a ha
    obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [mul_comm]
    exact H a

theorem char_fin_add (ψ : AddChar (AF F) ℂ) (y z : Af F) :
    ψ (pairA F 0 (y + z)) = ψ (pairA F 0 y) * ψ (pairA F 0 z) := by
  rw [← AddChar.map_add_eq_mul]
  exact congrArg ψ (Prod.ext (add_zero (0 : Ainf F)).symm rfl)

theorem mem_adelicIdeal_codiff_iff {ψ : AddChar (AF F) ℂ} (h : IsStdChar F ψ) (y : Af F) :
    y ∈ adelicIdeal (codiff F) ↔
      ∀ α : Af F, (∀ v, α v ∈ v.adicCompletionIntegers F) → ψ (pairA F 0 (α * y)) = 1 := by
  have key : ∀ x : F, x ∈ codiff F ↔ ∀ α : Af F, (∀ v, α v ∈ v.adicCompletionIntegers F) →
      ψ (pairA F 0 (α * algebraMap F (Af F) x)) = 1 := fun x => by
    rw [mem_codiff_iff h]
    refine ⟨fun H α hα => GlobalTheory.IntDense.addChar_eq_one_of_integral F ψ h.1.1 x H α hα,
      fun H a => ?_⟩
    rw [map_mul]
    refine H _ fun v => ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, adele_algebraMap_apply, valued_algebraMap]
    exact v.valuation_le_one a
  have hint : ∀ α : Af F, (∀ v, α v ∈ v.adicCompletionIntegers F) → ψ (pairA F 0 α) = 1 :=
    fun α hα => by
      have := (key 1).1 (one_le_codiff (FractionalIdeal.one_mem_one _)) α hα
      rwa [map_one, mul_one] at this
  obtain ⟨x, hx⟩ := exists_sub_mem_adelicIdeal (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F)) y
  have hx1 := mem_adelicIdeal_one_iff.1 hx
  have hx2 : y - algebraMap F (Af F) x ∈ adelicIdeal (codiff F) := by
    refine (mem_adelicIdeal_iff codiff_ne_zero).2 fun v => (hx1 v).trans ?_
    have := FractionalIdeal.count_mono F v (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))
      (one_le_codiff (F := F))
    rw [FractionalIdeal.count_one] at this
    rw [← exp_zero, exp_le_exp]
    omega
  have e : y = algebraMap F (Af F) x + (y - algebraMap F (Af F) x) := by ring
  rw [e, (adelicIdeal (codiff F)).add_mem_iff_left hx2, algebraMap_mem_adelicIdeal codiff_ne_zero, key]
  refine forall_congr' fun α => forall_congr' fun hα => ?_
  rw [mul_add, char_fin_add, hint (α * (y - algebraMap F (Af F) x))
    fun v => mul_mem (hα v) (hx1 v), mul_one]

theorem singleV_self (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) : singleV F v t v = t := by
  classical
  exact RestrictedProduct.single_eq_same _ v t

theorem singleV_of_ne {v w : HeightOneSpectrum (𝓞 F)} (t : Fv F v) (h : w ≠ v) :
    singleV F v t w = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne _ t h

theorem mul_singleV (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) (α : Af F) :
    α * singleV F v t = singleV F v (t * α v) := by
  ext1 w
  rw [adele_mul_apply]
  by_cases h : w = v
  · subst h
    rw [singleV_self, singleV_self, mul_comm]
  · rw [singleV_of_ne _ h, singleV_of_ne _ h, mul_zero]

theorem mem_dualV_iff_valued {ψ : AddChar (AF F) ℂ} (h : IsStdChar F ψ)
    (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) :
    t ∈ dualV F ψ v ↔ Valued.v t ≤ exp (-FractionalIdeal.count F v (codiff F)) := by
  have h1 : t ∈ dualV F ψ v ↔ singleV F v t ∈ adelicIdeal (codiff F) := by
    rw [mem_adelicIdeal_codiff_iff h]
    constructor
    · intro H α hα
      rw [mul_singleV]
      exact H _ (hα v)
    · intro H s hs
      have := H (singleV F v s) fun w => by
        by_cases hw : w = v
        · subst hw; rwa [singleV_self]
        · rw [singleV_of_ne _ hw]; exact zero_mem _
      rwa [mul_singleV, singleV_self] at this
  rw [h1, mem_adelicIdeal_iff codiff_ne_zero]
  refine ⟨fun H => by simpa only [singleV_self] using H v, fun H w => ?_⟩
  by_cases hw : w = v
  · subst hw; rwa [singleV_self]
  · rw [singleV_of_ne _ hw, map_zero]; exact zero_le'

theorem exists_generator_differentV (v : HeightOneSpectrum (𝓞 F)) :
    ∃ y : v.adicCompletionIntegers F,
      Valued.v (y : Fv F v) = exp (FractionalIdeal.count F v (codiff F)) ∧
        differentV F v = Ideal.span {y} := by
  have hD : ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = (codiff F)⁻¹ :=
    coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
  have hne : (codiff F)⁻¹ ≠ 0 := inv_ne_zero codiff_ne_zero
  obtain ⟨y, hy, hv⟩ := exists_mem_valuation_eq hne v
  rw [← hD] at hy
  obtain ⟨y, hyD, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
  have hc : ∀ r : 𝓞 F, Valued.v ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) r :
      v.adicCompletionIntegers F) : Fv F v) = v.valuation F (algebraMap (𝓞 F) F r) :=
    fun r => valued_algebraMap v _
  refine ⟨algebraMap (𝓞 F) _ y, by rw [hc, hv, FractionalIdeal.count_inv, neg_neg], ?_⟩
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun r hr => ?_)
    ((Ideal.span_singleton_le_iff_mem _).2 (Ideal.mem_map_of_mem _ hyD))
  have hr' : algebraMap (𝓞 F) F r ∈ (codiff F)⁻¹ := by
    rw [← hD]; exact (FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩
  have h2 := (mem_iff_valuation_le hne _).1 hr' v
  rw [← hv, ← hc, ← hc] at h2
  rw [Ideal.mem_comap, Ideal.mem_span_singleton]
  exact (Valuation.Integers.le_iff_dvd (Valuation.valuationSubring.integers _)).1 h2

theorem dualV_eq_inv_different {ψ : AddChar (AF F) ℂ} (h : IsStdChar F ψ)
    (v : HeightOneSpectrum (𝓞 F)) :
    (∀ t : Fv F v, t ∈ dualV F ψ v ↔
      ∀ d ∈ differentV F v, t * (d : Fv F v) ∈ v.adicCompletionIntegers F) ∧
    dualIndex F ψ v = normDifferentV F v := by
  obtain ⟨y, hy, hD⟩ := exists_generator_differentV v
  have hy0 : (y : Fv F v) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hy
    exact exp_ne_zero hy.symm
  have h1 : ∀ t : Fv F v, t ∈ dualV F ψ v ↔ t * y ∈ v.adicCompletionIntegers F := fun t => by
    rw [mem_dualV_iff_valued h, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hy, exp_neg,
      ← one_div, le_div_iff₀ (zero_lt_iff.2 exp_ne_zero)]
  refine ⟨fun t => ?_, ?_⟩
  · rw [h1, hD]
    refine ⟨fun H d hd => ?_, fun H => H y (Ideal.mem_span_singleton_self y)⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hd
    rw [MulMemClass.coe_mul, ← mul_assoc]
    exact mul_mem H c.2
  · have hle : intV F v ≤ dualV F ψ v := fun t ht => (h1 t).2 (mul_mem ht y.2)
    have hinj : Function.Injective (AddMonoidHom.mulRight (y : Fv F v)) :=
      mul_left_injective₀ hy0
    let j : v.adicCompletionIntegers F →+ Fv F v :=
      (v.adicCompletionIntegers F).subtype.toAddMonoidHom
    have hj : Function.Injective j := Subtype.val_injective
    have e1 : (dualV F ψ v).map (AddMonoidHom.mulRight (y : Fv F v)) = (⊤ : AddSubgroup _).map j := by
      ext z
      simp only [AddSubgroup.mem_map, AddSubgroup.mem_top, true_and, AddMonoidHom.mulRight_apply]
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨⟨_, (h1 t).1 ht⟩, rfl⟩
      · rintro ⟨c, rfl⟩
        have : (c : Fv F v) / y * y = c := div_mul_cancel₀ _ hy0
        exact ⟨c / y, (h1 _).2 (this.symm ▸ c.2), this⟩
    have e2 : (intV F v).map (AddMonoidHom.mulRight (y : Fv F v)) =
        (differentV F v).toAddSubgroup.map j := by
      ext z
      simp only [AddSubgroup.mem_map, AddMonoidHom.mulRight_apply, hD,
        Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨_, ⟨⟨t, ht⟩, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
        exact ⟨c, c.2, rfl⟩
    rw [dualIndex, AddSubgroup.relIndex_eq_one.2 hle, Nat.cast_one, div_one,
      ← AddSubgroup.relIndex_map_map_of_injective _ _ hinj, e1, e2,
      AddSubgroup.relIndex_map_map_of_injective _ _ hj, AddSubgroup.relIndex_top_right]
    rfl

theorem dualV_eq_inv_different_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ ψ₀, IsStdChar F ψ₀ → ∀ v : HeightOneSpectrum (𝓞 F), (∀ t : Fv F v, t ∈ dualV F ψ₀ v ↔ ∀ d ∈ differentV F v, t * (d : Fv F v) ∈ v.adicCompletionIntegers F) ∧ dualIndex F ψ₀ v = normDifferentV F v :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ h v => dualV_eq_inv_different h v

end GlobalTheory.StdDual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDenOfValLeOne
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
open scoped Matrix

namespace GlobalTheory.HAtBasis

variable {K : Type} [Field K] [NumberField K]


open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.HAtBasis.isLattice_of_basisAt {n : ℕ} (w : HeightOneSpectrum (𝓞 K))
    {M : Submodule (𝓞 K) (Fin n → K)} (hM : M.FG)
    {B : GL (Fin n) K} (hB : _root_.Formalism.L2.DIV.IsBasisAt w M B) : Submodule.IsFullLattice K M := by
  haveI : Submodule.IsLattice K M := ⟨hM, fun s hs hli =>
    (LinearIndependent.iff_fractionRing _ _).mp hli⟩
  refine ⟨?_⟩
  have hcol : ∀ j, (fun i => (B : Matrix (Fin n) (Fin n) K) i j) ∈
      Submodule.span K (M : Set (Fin n → K)) := by
    intro j
    have h1 : (fun i => (B : Matrix (Fin n) (Fin n) K) i j) ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M := by
      unfold _root_.Formalism.L2.DIV.IsBasisAt at hB
      rw [hB]
      apply _root_.Formalism.HermitianLatticesTheory.locBasic_le_locS
      exact Submodule.subset_span ⟨j, rfl⟩
    obtain ⟨s, hs, hsx⟩ := (_root_.PI.LocGlobInclWork.mem_localization_iff w.asIdeal M _).1 h1
    have hs0 : (s : K) ≠ 0 := by
      intro h0
      apply hs
      have hs' : s = 0 := by exact_mod_cast h0
      rw [hs']
      exact w.asIdeal.zero_mem
    have h2 := Submodule.smul_mem (Submodule.span K (M : Set (Fin n → K))) ((s : K)⁻¹)
      (Submodule.subset_span hsx)
    convert h2 using 1
    funext i
    simp [Algebra.smul_def, hs0]
  apply top_unique
  intro x hx
  have hrange : LinearMap.range (B : Matrix (Fin n) (Fin n) K).mulVecLin ≤
      Submodule.span K (M : Set (Fin n → K)) := by
    rw [Matrix.range_mulVecLin]
    exact Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hcol j)
  apply hrange
  refine ⟨(B⁻¹ : GL (Fin n) K).val *ᵥ x, ?_⟩
  change B.val *ᵥ ((B⁻¹).val *ᵥ x) = x
  rw [Matrix.mulVec_mulVec, show B.val * (B⁻¹).val = 1 from B.mul_inv, Matrix.one_mulVec]
variable {ι : Type} [Fintype ι] {a : ℕ}


open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
variable {ι : Type} [Fintype ι] {a : ℕ} in
omit [NumberField K] in
theorem _root_.GlobalTheory.HAtBasis.polyAction_invTranspose_inv (lam : ι → _root_.Formalism.BasicNotions.DomWeight a)
    (B : ι → GL (Fin a) K) (F : _root_.Formalism.L2.DIV.Pol K ι a) :
    _root_.Formalism.L2.DIV.actP lam (fun τ => _root_.Formalism.BasicNotions.inside₂ K a (B τ))⁻¹ F =
      (∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ (lam τ).detShift) •
        _root_.Formalism.GradedWeylDivisibility.blockAct K (fun τ => (B τ : Matrix (Fin a) (Fin a) K)) F := by
  have hg : ∀ τ, (((fun τ => _root_.Formalism.BasicNotions.inside₂ K a (B τ))⁻¹ τ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) =
      (B τ : Matrix (Fin a) (Fin a) K)ᵀ := fun τ => rfl
  simp only [_root_.Formalism.L2.DIV.actP, _root_.Formalism.L2.DIV.trAct, _root_.Formalism.L2.DIV.detTw_eq, LinearMap.smul_apply, AlgHom.toLinearMap_apply, hg,
    Matrix.det_transpose, Matrix.transpose_transpose]

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
variable {ι : Type} [Fintype ι] {a : ℕ} in
private theorem valuation_coe_eq_one_of_notMem {K : Type} [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∉ w.asIdeal) : w.valuation K (s : K) = 1 := by
  rw [show (s : K) = algebraMap (𝓞 K) K s from rfl, HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl w s).2 hs

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
variable {ι : Type} [Fintype ι] {a : ℕ} in
private theorem exists_notMem_mul_eq_integer_of_valuation_le_one {K : Type} [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) (x : K) (hx : w.valuation K x ≤ 1) :
    ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∃ c : 𝓞 K, (s : K) * x = (c : K) := by
  have h1 : x ∈ (w.valuation K).valuationSubring := hx
  rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at h1
  have h3 : x ∈ (HeightOneSpectrum.valuationSubringAtPrime K w).toSubring := h1
  rw [HeightOneSpectrum.valuationSubringAtPrime_toSubring] at h3
  have h2 : x ∈ _root_.GlobalTheory.LatBasisAt.locRing w := by
    unfold _root_.GlobalTheory.LatBasisAt.locRing
    exact h3
  obtain ⟨c, s, hs, rfl⟩ := (_root_.GlobalTheory.LatBasisAt.mem_locRing w x).1 h2
  refine ⟨s, hs, c, ?_⟩
  have hs0 : algebraMap (𝓞 K) K s ≠ 0 := _root_.GlobalTheory.LatBasisAt.algebraMap_ne_zero w hs
  change algebraMap (𝓞 K) K s * (algebraMap (𝓞 K) K c * (algebraMap (𝓞 K) K s)⁻¹) =
    algebraMap (𝓞 K) K c
  field_simp


open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
variable {ι : Type} [Fintype ι] {a : ℕ} in
theorem _root_.GlobalTheory.HAtBasis.mem_HAt_iff : ∀ (K : Type) [Field K]
    [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (ι : Type) [Fintype ι] (a : ℕ)
    (lam : ι → _root_.Formalism.BasicNotions.DomWeight a) (M : ι → Submodule (𝓞 K) (Fin a → K)) (B : ι → GL (Fin a) K),
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.LatWithBasis w M B → ∀ F : _root_.Formalism.L2.DIV.VV K lam,
      F ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.HAt w lam M ↔
        ∀ m, w.valuation K (((∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ (lam τ).detShift) •
          _root_.Formalism.GradedWeylDivisibility.blockAct K (fun τ => (B τ : Matrix (Fin a) (Fin a) K)) (F : _root_.Formalism.L2.DIV.Pol K ι a)).coeff m) ≤ 1 := by
  intro K _ _ w ι _ a lam M B hMB F
  have hB' : ∀ τ, _root_.Formalism.L2.DIV.IsBasisAt w (_root_.Formalism.L2.DIV.dualFr (M τ)) (_root_.Formalism.BasicNotions.inside₂ K a (B τ)) :=
    fun τ => _root_.GlobalTheory.DualWeylDual.isBasisAt_dualFr w (hMB τ).1 (hMB τ).2
  have hlat : ∀ τ, Submodule.IsFullLattice K (_root_.Formalism.L2.DIV.dualFr (M τ)) := fun τ =>
    _root_.GlobalTheory.DualLat.isLattice_dualFr _ (_root_.GlobalTheory.HAtBasis.isLattice_of_basisAt w (hMB τ).1 (hMB τ).2)
  have hloc := (_root_.GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 K ι a lam
    (fun τ => _root_.Formalism.L2.DIV.dualFr (M τ)) hlat w (fun τ => _root_.Formalism.BasicNotions.inside₂ K a (B τ)) hB').1
  have step1 : F ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.HAt w lam M ↔
      (F : _root_.Formalism.L2.DIV.Pol K ι a) ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (_root_.Formalism.L2.DIV.nabP lam fun τ => _root_.Formalism.L2.DIV.dualFr (M τ)) := by
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.HAt _root_.Formalism.L2.DIV.nabK
    rw [_root_.PI.LocGlobInclWork.mem_localization_iff, _root_.PI.LocGlobInclWork.mem_localization_iff]
    rfl
  rw [step1, hloc, _root_.GlobalTheory.TransLoc.mem_map_actP, _root_.GlobalTheory.HAtBasis.polyAction_invTranspose_inv]
  set G : _root_.Formalism.L2.DIV.Pol K ι a := (∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ (lam τ).detShift) •
    _root_.Formalism.GradedWeylDivisibility.blockAct K (fun τ => (B τ : Matrix (Fin a) (Fin a) K)) (F : _root_.Formalism.L2.DIV.Pol K ι a) with hG
  have hcoeff : ∀ (s : 𝓞 K) m, AddMonoidAlgebra.coeff (s • G) m = (s : K) * AddMonoidAlgebra.coeff G m := by
    intro s m
    erw [Algebra.smul_def, MvPolynomial.algebraMap_apply, coeff_C_mul]
  constructor
  · intro hGm m
    obtain ⟨s, hs, hsG⟩ := (_root_.PI.LocGlobInclWork.mem_localization_iff _ _ _).1 hGm
    obtain ⟨P, hP⟩ := _root_.GlobalTheory.LocInt.exists_map_eq_of_mem_nabStd lam hsG
    have hc : AddMonoidAlgebra.coeff (s • G) m = ((AddMonoidAlgebra.coeff P m : 𝓞 K) : K) := by
      have h' : AddMonoidAlgebra.coeff (_root_.Formalism.L2.DIV.toK K _ P) m = AddMonoidAlgebra.coeff (s • G) m := congrArg (AddMonoidAlgebra.coeff · m) hP
      rw [← h']
      simp [_root_.Formalism.L2.DIV.toK, coeff_map]
    rw [hcoeff] at hc
    have hs0 : (s : K) ≠ 0 := _root_.GlobalTheory.LatBasisAt.algebraMap_ne_zero w hs
    have e : AddMonoidAlgebra.coeff G m = (s : K)⁻¹ * ((AddMonoidAlgebra.coeff P m : 𝓞 K) : K) := by
      rw [← hc, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
    rw [e, map_mul, map_inv₀, valuation_coe_eq_one_of_notMem w hs, inv_one, one_mul]
    exact HeightOneSpectrum.valuation_le_one w _
  · intro hint
    choose sf hsf c hc using fun m => exists_notMem_mul_eq_integer_of_valuation_le_one w _ (hint m)
    refine (_root_.PI.LocGlobInclWork.mem_localization_iff _ _ _).2 ⟨∏ m ∈ G.support, sf m, ?_, ?_⟩
    · intro hmem
      obtain ⟨m, _, hm⟩ := Ideal.IsPrime.prod_mem_iff.1 hmem
      exact hsf m hm
    · have hGV : G ∈ _root_.Formalism.L2.DIV.VV K lam :=
        Submodule.smul_mem _ _ (_root_.Formalism.L2.DIV.ps_blockAct_mem_VV lam _ F.2)
      refine _root_.GlobalTheory.DetSat.mem_nabStd_of_det_mul_integral K ι a lam (fun _ => 0) _
        (Submodule.smul_of_tower_mem _ _ hGV) fun m => ?_
      simp only [pow_zero, Finset.prod_const_one, one_mul]
      change IsIntegral ℤ (AddMonoidAlgebra.coeff ((∏ m ∈ G.support, sf m) • G) m)
      rw [hcoeff]
      by_cases hm : m ∈ G.support
      · rw [← Finset.mul_prod_erase _ _ hm]
        push_cast
        rw [mul_comm ((sf m : 𝓞 K) : K), mul_assoc, hc m]
        have hI := RingOfIntegers.isIntegral_coe ((∏ i ∈ G.support.erase m, sf i) * c m)
        convert hI using 1
        simp
      · rw [notMem_support_iff.1 hm, mul_zero]
        exact isIntegral_zero

end GlobalTheory.HAtBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelCharacterNoBlocksPthRootOfUnity
section
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem lamJ_zero_blocks_mem_range_and_pow_eq_one :
    ∀ (k K : Type) [Field k] [Field K] (s : K →+* ℂ) (p : ℕ), p.Prime → (p : k) = 0 → (∃ ζ : K, IsPrimitiveRoot ζ p) → ∀ (n : ℕ) (ψ : AddChar k ℂ) (χ : ℕ → MulChar k ℂ) (a t skip : ℕ) (M : Matrix (Fin n) (Fin n) k), (∃ r : K, s r = lamJ ψ χ a t 0 skip M) ∧ lamJ ψ χ a t 0 skip M ^ p = 1 := by
  intro k K _ _ s p hp hk ⟨ζ, hζ⟩ n ψ χ a t skip M
  have hψ : ∀ x : k, ψ x ^ p = 1 := fun x => by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, hk, zero_mul, AddChar.map_zero_eq_one]
  have h : lamJ ψ χ a t 0 skip M ^ p = 1 := by
    unfold Formalism.L2.Forms.lamJ
    simp [hψ]
  exact ⟨complex_rootOfUnity_mem_range_of_isPrimitiveRoot K s p ζ hp.pos hζ _ h, h⟩

end GlobalTheory
end

