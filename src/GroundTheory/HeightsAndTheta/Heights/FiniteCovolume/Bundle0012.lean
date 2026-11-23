module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0005

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PAdelicLatticeDictionary
section
set_option linter.unusedSectionVars false

noncomputable section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module Matrix TensorProduct NumberField IsDedekindDomain GroundTheory.Automorphic
open scoped Pointwise

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

section Span

variable {κ : Type*} [Fintype κ] (b : Basis κ F E) (v : Basis ι E W)

def coordSpan (c : F) : (ι × κ → 𝓞 F) →ₗ[ℤ] W :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun z => ∑ a : ι × κ, (algebraMap F E (c⁻¹ * algebraMap (𝓞 F) F (z a)) * b a.2) • v a.1
      map_zero' := by simp
      map_add' := fun z z' => by
        simp only [Pi.add_apply, map_add (f := _), mul_add, add_mul, add_smul, Finset.sum_add_distrib] }

theorem mem_range_coordSpan {c : F} (hc : c ≠ 0) {x : W}
    (hx : ∀ i k, IsIntegral ℤ (c * b.repr (v.repr x i) k)) :
    x ∈ LinearMap.range (coordSpan b v c) := by
  choose z hz using fun a : ι × κ =>
    (⟨⟨_, hx a.1 a.2⟩, rfl⟩ : ∃ z : 𝓞 F, algebraMap (𝓞 F) F z = c * b.repr (v.repr x a.1) a.2)
  refine ⟨z, ?_⟩
  show ∑ a : ι × κ, (algebraMap F E (c⁻¹ * algebraMap (𝓞 F) F (z a)) * b a.2) • v a.1 = x
  simp only [hz, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [Fintype.sum_prod_type]
  conv_rhs => rw [← v.sum_repr x]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  rw [← Finset.sum_smul]
  congr 1
  conv_rhs => rw [← b.sum_repr (v.repr x i)]
  simp only [Algebra.smul_def]

end Span

theorem isTorsionFree_int_of_module (K' V' : Type*) [Field K'] [CharZero K'] [AddCommGroup V']
    [Module K' V'] : Module.IsTorsionFree ℤ V' :=
  Module.IsTorsionFree.comap (S := K') (fun n : ℤ => (n : K'))
    (fun r hr => isRegular_iff_ne_zero.2 (Int.cast_ne_zero.2 (isRegular_iff_ne_zero.1 hr)))
    (fun r m => Int.cast_smul_eq_zsmul K' r m)

section DIntegral

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ F E) (h : HermitianForm F E W)
  (v : Basis ι E W)

theorem repr_repr_smul_inv_int (d : ℤ) (x : W) (i : ι) (k : κ) :
    b.repr (v.repr ((d : E)⁻¹ • x) i) k = (d : F)⁻¹ * b.repr (v.repr x i) k := by
  have : (d : E)⁻¹ = algebraMap F E (d : F)⁻¹ := by rw [map_inv₀, map_intCast]
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, this, ← Algebra.smul_def, map_smul,
    Finsupp.smul_apply, smul_eq_mul]

theorem repr_repr_nsmul (n : ℕ) (x : W) (i : ι) (k : κ) :
    b.repr (v.repr (n • x) i) k = n * b.repr (v.repr x i) k := by
  rw [map_nsmul, Finsupp.smul_apply, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]

theorem isDIntegral_dictLattice {d : ℤ} (hd0 : d ≠ 0)
    (hd : ∀ (g : unitaryPoints F E (gram h.toSesq v) (FinAdele F)) (x y : ι → F ⊗[F] E),
      x ∈ coreLattice b (gram h.toSesq v) g → y ∈ coreLattice b (gram h.toSesq v) g →
        IsIntegral ℤ ((d : E) * pairE (gram h.toSesq v) x y))
    {m : ℤ} (hm0 : m ≠ 0)
    (hm : ∀ (g : unitaryPoints F E (gram h.toSesq v) (FinAdele F)) (y : ι → F ⊗[F] E),
      (∀ x ∈ coreLattice b (gram h.toSesq v) g, IsIntegral ℤ (pairE (gram h.toSesq v) y x)) →
        (m : F) • y ∈ coreLattice b (gram h.toSesq v) g)
    (g : unitaryPoints F E (gram h.toSesq v) (FinAdele F)) :
    IsDIntegral h ((m * d * d).natAbs ^ finrank ℤ (ι × κ → 𝓞 F)) (dictLattice b h v d g) := by
  classical
  haveI : Module.IsTorsionFree ℤ W := isTorsionFree_int_of_module E W
  have hdE : (d : E) ≠ 0 := by exact_mod_cast hd0
  have hdF : (d : F) ≠ 0 := by exact_mod_cast hd0
  have hsmulL : ∀ (c : E) (x y : W), h.toSesq (c • x) y = conj F E c * h.toSesq x y := by
    intro c x y
    rw [LinearMap.map_smulₛₗ₂, smul_eq_mul]
    rfl
  have hsmulR : ∀ (c : E) (x y : W), h.toSesq x (c • y) = c * h.toSesq x y := by
    intro c x y
    rw [map_smul, smul_eq_mul]
  have hconjd : conj F E (d : E) = d := map_intCast _ _
  have hdI : IsIntegral ℤ (d : E) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := d))

  have hint : ∀ x ∈ dictLattice b h v d g, ∀ y ∈ dictLattice b h v d g, IsIntegral ℤ (h.toSesq x y) := by
    intro x hx y hy
    have e : h.toSesq x y = (d : E) * ((d : E) * pairE (gram h.toSesq v) (coordEquiv F v ((d : E)⁻¹ • x))
        (coordEquiv F v ((d : E)⁻¹ • y))) := by
      rw [pairE_coordEquiv, hsmulL, hsmulR, map_inv₀, hconjd]
      field_simp
    rw [e]
    exact hdI.mul (hd g _ _ hx hy)

  obtain ⟨m', hm'0, hm'⟩ := exists_int_isIntegral_coords b (isUnit_det_gram h v) g
  set c : F := (m' : F) * (d : F)⁻¹ with hcdef
  have hc : c ≠ 0 := mul_ne_zero (by exact_mod_cast hm'0) (inv_ne_zero hdF)
  have hcoordL : ∀ x ∈ dictLattice b h v d g, ∀ i k, IsIntegral ℤ (c * b.repr (v.repr x i) k) := by
    intro x hx i k
    have hx' : coordEquiv F v ((d : E)⁻¹ • x) ∈ coreLattice b (gram h.toSesq v) g := hx
    have := hm' _ (coreLattice_le_adelicLattice b g hx') (i, k)
    rw [vecCoords_coordEquiv, repr_repr_smul_inv_int] at this
    rw [hcdef, mul_assoc]
    exact this
  have hLQ : (dictLattice b h v d g).toIntSubmodule ≤ LinearMap.range (coordSpan b v c) :=
    fun x hx => mem_range_coordSpan b v hc (hcoordL x hx)

  set M : ℤ := m * d * d with hMdef
  have hM0 : M.natAbs ≠ 0 := Int.natAbs_ne_zero.2 (mul_ne_zero (mul_ne_zero hm0 hd0) hd0)
  have hLP : dictLattice b h v d g ≤ dualLattice h (dictLattice b h v d g) := fun x hx y hy => (mem_integralClosure_iff ℤ E).2 (hint x hx y hy)
  have hnL : ∀ y ∈ dualLattice h (dictLattice b h v d g), M.natAbs • y ∈ dictLattice b h v d g := by
    intro y hy
    have h1 : (m : F) • coordEquiv F v ((d : E) • y) ∈ coreLattice b (gram h.toSesq v) g := by
      refine hm g _ fun X hX => ?_
      set x0 := (coordEquiv F v).symm X
      have hx0 : (d : E) • x0 ∈ dictLattice b h v d g := by
        rw [mem_dictLattice, inv_smul_smul₀ hdE, AddEquiv.apply_symm_apply]
        exact hX
      have h2 := (mem_integralClosure_iff ℤ E).1 (hy _ hx0)
      rw [show X = coordEquiv F v x0 from (AddEquiv.apply_symm_apply _ X).symm, pairE_coordEquiv,
        hsmulL, hconjd, ← hsmulR]
      exact h2
    have hMy : M • y ∈ dictLattice b h v d g := by
      rw [mem_dictLattice]
      have e : (d : E)⁻¹ • (M • y) = m • ((d : E) • y) := by
        rw [← Int.cast_smul_eq_zsmul E M, ← Int.cast_smul_eq_zsmul E m, smul_smul, smul_smul, hMdef]
        congr 1
        push_cast
        field_simp
      rw [e, map_zsmul, ← Int.cast_smul_eq_zsmul F]
      exact h1
    have : (M.natAbs : ℤ) • y ∈ dictLattice b h v d g := by
      rcases Int.natAbs_eq M with hM | hM
      · rwa [← hM]
      · rw [show (M.natAbs : ℤ) = -M by omega, neg_smul]
        exact neg_mem hMy
    rwa [natCast_zsmul] at this
  have hcn : c * (M.natAbs : F) ≠ 0 := mul_ne_zero hc (by exact_mod_cast hM0)
  have hPQ : (dualLattice h (dictLattice b h v d g)).toIntSubmodule ≤ LinearMap.range (coordSpan b v (c * M.natAbs)) := by
    intro y hy
    refine mem_range_coordSpan b v hcn fun i k => ?_
    have := hcoordL _ (hnL y hy) i k
    rw [repr_repr_nsmul] at this
    rw [mul_assoc]
    exact this
  obtain ⟨hne, hle⟩ := relIndex_ne_zero_and_le_of_nsmul_mem hLP hPQ hM0 hnL
  refine ⟨⟨fun a x hx => ?_, ?_, ?_⟩, fun x hx y hy => (mem_integralClosure_iff ℤ E).2 (hint x hx y hy),
    hne, hle.trans (Nat.pow_le_pow_right (Nat.pos_of_ne_zero hM0)
      (LinearMap.finrank_range_le (coordSpan b v (c * M.natAbs))))⟩
  ·
    rw [mem_dictLattice, smul_comm, coordEquiv_smul]
    exact smul_mem_coreLattice b hx a
  ·
    haveI : Module.Finite ℤ (dictLattice b h v d g).toIntSubmodule :=
      Module.Finite.of_injective (Submodule.inclusion hLQ) (Submodule.inclusion_injective hLQ)
    have := Module.Finite.iff_fg.1 (inferInstance : Module.Finite ℤ (dictLattice b h v d g).toIntSubmodule)
    exact (Submodule.fg_iff_addSubgroup_fg _).1 this
  ·
    rw [eq_top_iff, ← v.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨n, hn0, hn⟩ := exists_int_smul_single_mem_coreLattice b g i
    have hmem : (d * n) • v i ∈ dictLattice b h v d g := by
      rw [mem_dictLattice]
      have e1 : (d : E)⁻¹ • ((d * n) • v i) = n • v i := by
        rw [← Int.cast_smul_eq_zsmul E (d * n), ← Int.cast_smul_eq_zsmul E n, smul_smul]
        congr 1
        push_cast
        field_simp
      have e2 : coordEquiv F v (v i) = Pi.single i (1 : F ⊗[F] E) := by
        funext j
        rw [coordEquiv_apply, Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
        by_cases hij : i = j
        · subst hij
          simp [Algebra.TensorProduct.one_def]
        · rw [if_neg hij, if_neg (Ne.symm hij), TensorProduct.tmul_zero]
      rw [e1, map_zsmul, e2, ← Int.cast_smul_eq_zsmul F]
      exact hn
    have hvi : v i = ((d * n : ℤ) : E)⁻¹ • ((d * n) • v i) := by
      rw [← Int.cast_smul_eq_zsmul E (d * n), inv_smul_smul₀ (by exact_mod_cast mul_ne_zero hd0 hn0)]
    rw [SetLike.mem_coe, hvi]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end DIntegral

variable [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

theorem AdelicLatticeDictionary.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    AdelicLatticeDictionary.Statement h v := by
  classical
  obtain ⟨d, hd0, hd⟩ := exists_int_isIntegral_pairE (Module.finBasis F E) (gram h.toSesq v)
  obtain ⟨m, hm0, hm⟩ := exists_int_smul_mem_coreLattice_of_dual (Module.finBasis F E)
    (isUnit_det_gram h v)
  exact ⟨coreStabilizer (Module.finBasis F E) (gram h.toSesq v), _,
    dictLattice (Module.finBasis F E) h v d,
    isCompact_coreStabilizer (Module.finBasis F E) _ (isUnit_det_gram h v),
    isOpen_coreStabilizer (Module.finBasis F E) _,
    fun g => isDIntegral_dictLattice (Module.finBasis F E) h v hd0 hd hm0 hm g,
    fun γ g => dictLattice_diagonal_mul d γ g,
    fun g g' => dictLattice_eq_iff hd0⟩

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchCovolumeBound
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module MeasureTheory

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [IsTotallyReal F] [DecidableEq ι] in
theorem ArchCovolumeBound.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : CoordEmbedBasis.Statement E ι)
    (h₂ : IntegralFormCovolume.Statement (ι → E) (InfinitePlace E → ι → ℂ)
      (Σ _ : ι, Free.ChooseBasisIndex ℤ (𝓞 E)))
    (h₃ : TraceHermNondegenerate.Statement h v) (h₄ : DualLatticeMultiple.Statement h)
    (h₅ : CoordLatticeFullRank.Statement v) : ArchCovolumeBound.Statement h v := by
  intro D
  obtain ⟨k, hk0, hk⟩ := h₄ D
  let e := Pi.basis fun _ : ι => integralBasis E
  obtain ⟨C, hC⟩ := h₂ (coordEmbed E ι) e (traceHerm h v) volume (Measure.pi.isAddHaarMeasure _) h₃ h₁.1
    (by rw [h₁.2, finrank_eq_card_basis e])
  refine ⟨Real.sqrt (C * |(k : ℝ)| ^ Fintype.card (Σ _ : ι, Free.ChooseBasisIndex ℤ (𝓞 E))),
    fun La hLa => ?_⟩
  let φ : W →+ (ι → E) := (v.equivFun : W →ₗ[E] ι → E).toAddMonoidHom
  have hφ : ∀ x, v.equivFun.symm (φ x) = x := fun x => v.equivFun.symm_apply_apply x
  have hmem : ∀ y, y ∈ La.map φ ↔ v.equivFun.symm y ∈ La := by
    intro y
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rwa [hφ]
    · intro hy
      exact ⟨_, hy, v.equivFun.apply_symm_apply y⟩
  have harch : archLattice v La = AddSubgroup.toIntSubmodule ((La.map φ).map (coordEmbed E ι)) := by
    rw [archLattice, AddSubgroup.map_map]
    rfl
  obtain ⟨hfg, hspan⟩ := h₅ La hLa.isLattice
  obtain ⟨hint, hdual⟩ := hk La hLa
  obtain ⟨hD, hZ, hcov⟩ := hC (La.map φ) k hk0 hfg hspan
    (fun x hx y hy => hint _ ((hmem x).1 hx) _ ((hmem y).1 hy))
    (fun y hy => by
      rw [hmem, map_zsmul]
      refine hdual _ fun x hx => ?_
      obtain ⟨n, hn⟩ := hy (φ x) (AddSubgroup.mem_map_of_mem φ hx)
      exact ⟨n, by rw [traceHerm_apply, hφ] at hn; exact hn⟩)
  rw [harch]
  exact ⟨hD, hZ, (le_abs_self _).trans (Real.abs_le_sqrt hcov)⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArithmeticCovolumeFinite
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_len_invApply {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (y : InfinitePlace E → ι → ℂ) : Continuous fun g : archUnitary h v => M.len (invApply g y) := by
  have hw : ∀ w, Continuous fun g : archUnitary h v => invApply g y w := fun w =>
    (Units.continuous_val.comp ((continuous_apply w).comp
      (continuous_subtype_val.comp continuous_inv))).matrix_mulVec continuous_const
  refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun w _ => Complex.continuous_re.comp ?_)
  exact (hw w).star.dotProduct (continuous_const.matrix_mulVec (hw w))

theorem ArithmeticCovolumeFinite.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : ScalingLaw.Statement h v) (h₂ : MahlerCompactness.Statement h v)
    (h₃ : ShortVectorIsotropic.Statement h v) (h₄ : ShortestVectorIndex.Statement h v)
    (h₅ : IntegralFamilyBound.Statement E) (h₆ : MajorantExists.Statement h v)
    (h₈ : ArchLatticeDiscrete.Statement h v) (h₉ : LatticePointsBelowFinite.Statement h v) :
    ArithmeticCovolumeFinite.Statement h v := by
  classical
  intro μ _ D La hLa
  obtain ⟨M⟩ := h₆

  obtain ⟨r, a, ha, har⟩ := h₅
  have hdeg : finrank ℚ E = 2 * finrank ℚ F := by
    rw [← Module.finrank_mul_finrank ℚ F E, Algebra.IsQuadraticExtension.finrank_eq_two F E,
      mul_comm]
  have ha' : ∃ b : Fin (2 * finrank ℚ F) → 𝓞 E, LinearIndependent ℚ (fun i => (b i : E)) ∧
      ∀ i (σ : E →+* ℂ), ‖σ (b i)‖ ≤ r :=
    ⟨a ∘ Fin.cast hdeg.symm, ha.comp _ (Fin.cast_injective _), fun i σ => har _ σ⟩
  set C₀ : ℕ := ⌊(r * Real.sqrt (2 * finrank ℚ F)) ^ (2 * finrank ℚ F)⌋₊ with hC₀

  set VV : Set W := {x | x ∈ La ∧ x ≠ 0 ∧ h.toSesq x x = 0 ∧ lineIndex E La x ≤ C₀} with hVV
  have hstable : ∀ γ ∈ latticeStab h La, ∀ x ∈ VV, γ • x ∈ VV := by
    intro γ hγ x hx
    have hγ' : γ • La = La := MulAction.mem_stabilizer_iff.1 hγ
    refine ⟨?_, fun h0 => hx.2.1 ((smul_eq_zero_iff_eq γ).1 h0), ?_, ?_⟩
    · have h1 : γ • x ∈ γ • La := AddSubgroup.smul_mem_pointwise_smul _ _ _ hx.1
      rwa [hγ'] at h1
    · rw [← hx.2.2.1]
      exact HermitianForm.mem_unitaryGroup.1 γ.2 x x
    · rw [GaussianPlane.lineIndex_smul hγ']
      exact hx.2.2.2
  obtain ⟨FD, hFD, hm⟩ := h₁ M μ D La VV hLa (fun x hx => hx.1) (fun x hx => ⟨hx.2.1, hx.2.2.1⟩)
    hstable ⟨C₀, fun x hx => hx.2.2.2⟩
  refine ⟨FD, hFD, ?_⟩

  set B : Set (archUnitary h v) :=
    ⋃ x : W, ⋃ (_ : x ∈ La ∧ x ≠ 0), {g | M.len (invApply g (vecAt v x)) < 1} with hB
  have hBmeas : MeasurableSet B :=
    (isOpen_iUnion fun x => isOpen_iUnion fun _ =>
      isOpen_lt (continuous_len_invApply M _) continuous_const).measurableSet
  have hBle : μ (FD ∩ B) ≤ massBelow M μ FD VV 1 := by
    rw [Set.inter_comm, ← Measure.restrict_apply hBmeas, ← lintegral_indicator_one hBmeas]
    refine lintegral_mono fun g => ?_
    by_cases hg : g ∈ B
    · rw [Set.indicator_of_mem hg, Pi.one_apply]
      obtain ⟨x₁, hx₁⟩ := Set.mem_iUnion.1 hg
      obtain ⟨⟨hx₁La, hx₁0⟩, hx₁lt⟩ := Set.mem_iUnion.1 hx₁
      set S : Set W := {x | x ∈ La ∧ M.len (invApply g (vecAt v x)) < 1} ∩ {x | x ≠ 0}
      have hSfin : S.Finite := (h₉ M La g 1 hLa.isLattice).inter_of_left _
      obtain ⟨x, hxS, hxmin⟩ := Set.exists_min_image S (fun x => M.len (invApply g (vecAt v x)))
        hSfin ⟨x₁, ⟨hx₁La, hx₁lt⟩, hx₁0⟩
      obtain ⟨⟨hxLa, hxlt⟩, hx0⟩ := hxS
      have hshort : ∀ y ∈ La, y ≠ 0 →
          M.len (invApply g (vecAt v x)) ≤ M.len (invApply g (vecAt v y)) := by
        intro y hy hy0
        by_cases hylt : M.len (invApply g (vecAt v y)) < 1
        · exact hxmin y ⟨⟨hy, hylt⟩, hy0⟩
        · exact hxlt.le.trans (not_lt.1 hylt)
      have hxVV : x ∈ VV := by
        refine ⟨hxLa, hx0, h₃ M D La g x hLa hxLa hxlt, ?_⟩
        exact Nat.le_floor (h₄ M r ha' D La g x hLa hxLa hx0 hshort)
      have hne : ({y ∈ VV | M.len (invApply g (vecAt v y)) < 1}).Nonempty := ⟨x, hxVV, hxlt⟩
      unfold countBelow
      rw [← ENat.toENNReal_one, ENat.toENNReal_le]
      exact Set.one_le_encard_iff_nonempty.2 hne
    · rw [Set.indicator_of_notMem hg]
      exact bot_le

  obtain ⟨S, hS, K, hK, hMah⟩ := h₂ M D 1 one_pos
  have : DiscreteTopology (archLatticeGroup h v La) := h₈ La hLa.isLattice
  have : Countable (archLatticeGroup h v La) :=
    TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  let c : AddSubgroup W → h.unitaryGroup := fun L =>
    if hL : ∃ γ : h.unitaryGroup, γ • La = L then hL.choose else 1
  set K' : Set (archUnitary h v) :=
    ⋃ L ∈ S, (fun k => (archEmbed h v (c L))⁻¹ * k) '' K with hK'
  have hK'c : IsCompact K' :=
    hS.isCompact_biUnion fun L _ => hK.image (continuous_const.mul continuous_id)
  have hcover : FD ∩ Bᶜ ⊆ ⋃ δ : archLatticeGroup h v La, δ • K' ∩ FD := by
    rintro g ⟨hgFD, hgB⟩
    have hlam : ∀ x ∈ La, x ≠ 0 → (1 : ℝ) ≤ M.len (invApply g (vecAt v x)) := by
      intro x hx hx0
      by_contra hlt
      exact hgB (Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨⟨hx, hx0⟩, not_le.1 hlt⟩⟩)
    obtain ⟨γ, hγS, hγK⟩ := hMah La g hLa hlam
    have hL : ∃ γ' : h.unitaryGroup, γ' • La = γ • La := ⟨γ, rfl⟩
    have hcL : c (γ • La) • La = γ • La := by
      simp only [c, dif_pos hL]
      exact hL.choose_spec
    have hstab : γ⁻¹ * c (γ • La) ∈ latticeStab h La := by
      change (γ⁻¹ * c (γ • La)) • La = La
      rw [mul_smul, hcL, inv_smul_smul]
    refine Set.mem_iUnion.2 ⟨⟨archEmbed h v (γ⁻¹ * c (γ • La)), Subgroup.mem_map_of_mem _ hstab⟩,
      ?_, hgFD⟩
    refine Set.mem_smul_set.2 ⟨(archEmbed h v (c (γ • La)))⁻¹ * (archEmbed h v γ * g),
      Set.mem_biUnion hγS ⟨_, hγK, rfl⟩, ?_⟩
    rw [Subgroup.smul_def, smul_eq_mul]
    simp only [map_mul, map_inv]
    group
  have hAlt : μ (FD ∩ Bᶜ) < ⊤ := by
    calc μ (FD ∩ Bᶜ) ≤ μ (⋃ δ : archLatticeGroup h v La, δ • K' ∩ FD) := measure_mono hcover
      _ ≤ ∑' δ : archLatticeGroup h v La, μ (δ • K' ∩ FD) := measure_iUnion_le _
      _ = μ K' := (hFD.measure_eq_tsum K').symm
      _ < ⊤ := hK'c.measure_lt_top
  calc μ FD = μ ((FD ∩ B) ∪ (FD ∩ Bᶜ)) := by rw [Set.inter_union_compl]
    _ ≤ μ (FD ∩ B) + μ (FD ∩ Bᶜ) := measure_union_le _ _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hBle.trans_lt (hm 1 one_pos).1, hAlt⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PBoundedIndexSubgroupsFinite
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

theorem BoundedIndexSubgroupsFinite.proof (G : Type*) [AddCommGroup G] :
    BoundedIndexSubgroupsFinite.Statement G := by
  intro A B hB hAB C
  classical

  have : Module.Finite ℤ B :=
    Module.Finite.iff_addGroup_fg.mpr ((AddGroup.fg_iff_addSubgroup_fg B).mpr hB)
  have : Module.Finite ℤ A :=
    Module.Finite.of_injective (AddSubgroup.inclusion hAB).toIntLinearMap
      (AddSubgroup.inclusion_injective hAB)

  set n := C.factorial with hn
  let K : AddSubgroup A := (nsmulAddMonoidHom n : A →+ A).range

  have : Module.Finite ℤ (A ⧸ K) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' K).toIntLinearMap
      (QuotientAddGroup.mk'_surjective K)
  have htors : Module.IsTorsion ℤ (A ⧸ K) := by
    intro x
    refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (Nat.factorial_pos C).ne')⟩, ?_⟩
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      show (n : ℤ) • (QuotientAddGroup.mk a : A ⧸ K) = 0
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, natCast_zsmul]
      exact ⟨a, rfl⟩
  have : Finite (A ⧸ K) := Module.finite_of_fg_torsion _ htors

  have hK : ∀ H ∈ {H : AddSubgroup G | H ≤ A ∧ H.relIndex A ≠ 0 ∧ H.relIndex A ≤ C},
      K ≤ H.addSubgroupOf A := by
    rintro H ⟨-, h0, hC⟩ _ ⟨a, rfl⟩
    obtain ⟨k, hk⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero h0) hC
    rw [AddSubgroup.mem_addSubgroupOf]
    show n • (a : G) ∈ H
    rw [hn, hk, mul_nsmul]
    exact H.nsmul_mem (H.nsmul_relIndex_mem a.2) k

  refine Set.Finite.of_finite_image (f := fun H : AddSubgroup G =>
    (QuotientAddGroup.mk '' ((H.addSubgroupOf A : AddSubgroup A) : Set A) : Set (A ⧸ K)))
    (Set.toFinite _) ?_
  have key : ∀ H₁ ∈ {H : AddSubgroup G | H ≤ A ∧ H.relIndex A ≠ 0 ∧ H.relIndex A ≤ C},
      ∀ H₂ ∈ {H : AddSubgroup G | H ≤ A ∧ H.relIndex A ≠ 0 ∧ H.relIndex A ≤ C},
      (QuotientAddGroup.mk '' ((H₁.addSubgroupOf A : AddSubgroup A) : Set A) : Set (A ⧸ K)) =
        QuotientAddGroup.mk '' ((H₂.addSubgroupOf A : AddSubgroup A) : Set A) → H₁ ≤ H₂ := by
    intro H₁ h₁ H₂ h₂ he x hx
    have hxA : x ∈ A := h₁.1 hx
    have hmem : (QuotientAddGroup.mk (⟨x, hxA⟩ : A) : A ⧸ K) ∈
        QuotientAddGroup.mk '' ((H₁.addSubgroupOf A : AddSubgroup A) : Set A) :=
      ⟨⟨x, hxA⟩, AddSubgroup.mem_addSubgroupOf.mpr hx, rfl⟩
    rw [he] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have hd : -y + ⟨x, hxA⟩ ∈ H₂.addSubgroupOf A := hK H₂ h₂ (QuotientAddGroup.eq.mp hyx)
    have : (⟨x, hxA⟩ : A) ∈ H₂.addSubgroupOf A := by
      simpa using (H₂.addSubgroupOf A).add_mem hy hd
    exact AddSubgroup.mem_addSubgroupOf.mp this
  exact fun H₁ h₁ H₂ h₂ he => le_antisymm (key H₁ h₁ H₂ h₂ he) (key H₂ h₂ H₁ h₁ he.symm)

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

