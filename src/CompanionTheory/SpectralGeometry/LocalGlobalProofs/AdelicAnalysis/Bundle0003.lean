module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Mathlib

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompactSubgroupAndLevel
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core

theorem compact_open_sup {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    {L₁ L₂ : AddSubgroup V} (h₁ : IsCompact (L₁ : Set V)) (o₁ : IsOpen (L₁ : Set V))
    (h₂ : IsCompact (L₂ : Set V)) :
    IsCompact ((L₁ ⊔ L₂ : AddSubgroup V) : Set V) ∧ IsOpen ((L₁ ⊔ L₂ : AddSubgroup V) : Set V) := by
  refine ⟨?_, AddSubgroup.isOpen_mono le_sup_left o₁⟩
  rw [AddSubgroup.add_normal]
  exact h₁.add h₂

theorem compact_subgroup_and_level :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → (∀ K : Set V, IsCompact K → ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ K ⊆ L) ∧ ∀ φ : V → ℂ, SB φ → ∃ L L' : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ IsCompact (L' : Set V) ∧ IsOpen (L' : Set V) ∧ L' ≤ L ∧ (∀ x, x ∉ L → φ x = 0) ∧ ∀ x, ∀ l ∈ L', φ (x + l) = φ x := by
  intro V _ _ _ χ μ h
  obtain ⟨hG, hT, -, -, -, -, hnb, hcov, -⟩ := h
  haveI := hG
  haveI := hT
  have cover : ∀ K : Set V, IsCompact K →
      ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ K ⊆ L := by
    intro K hK
    refine hK.induction_on (p := fun s => ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧
      IsOpen (L : Set V) ∧ s ⊆ L) ?_ ?_ ?_ ?_
    · obtain ⟨L, c, o, -⟩ := hcov 0
      exact ⟨L, c, o, Set.empty_subset _⟩
    · rintro s t hst ⟨L, c, o, hL⟩
      exact ⟨L, c, o, hst.trans hL⟩
    · rintro s t ⟨L₁, c₁, o₁, h₁⟩ ⟨L₂, c₂, o₂, h₂⟩
      obtain ⟨c, o⟩ := compact_open_sup c₁ o₁ c₂
      refine ⟨L₁ ⊔ L₂, c, o, Set.union_subset ?_ ?_⟩
      · exact h₁.trans (SetLike.coe_subset_coe.2 le_sup_left)
      · exact h₂.trans (SetLike.coe_subset_coe.2 le_sup_right)
    · intro x _
      obtain ⟨L, c, o, hx⟩ := hcov x
      exact ⟨L, mem_nhdsWithin_of_mem_nhds (o.mem_nhds hx), L, c, o, subset_rfl⟩
  refine ⟨cover, ?_⟩
  rintro φ ⟨hlc, hcs⟩
  obtain ⟨L, c, o, hL⟩ := cover _ hcs
  have hzero : ∀ x, x ∉ L → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hm => hx (hL hm))
  have hg : IsLocallyConstant (fun p : V × V => (φ (p.1 + p.2), φ p.1)) :=
    (hlc.comp_continuous continuous_add).prodMk (hlc.comp_continuous continuous_fst)
  have hW : IsOpen {p : V × V | φ (p.1 + p.2) = φ p.1} := hg {q : ℂ × ℂ | q.1 = q.2}
  have hsub : (L : Set V) ×ˢ ({0} : Set V) ⊆ {p : V × V | φ (p.1 + p.2) = φ p.1} := by
    rintro ⟨x, y⟩ ⟨-, hy⟩
    have hy' : y = 0 := hy
    simp [hy']
  obtain ⟨u, v, -, ov, hu, hv, huv⟩ := generalized_tube_lemma c isCompact_singleton hW hsub
  obtain ⟨L₀, c₀, o₀, h₀⟩ := hnb v (ov.mem_nhds (hv rfl))
  refine ⟨L, L₀ ⊓ L, c, o, ?_, ?_, inf_le_right, hzero, ?_⟩
  · have := c₀.inter_right c.isClosed
    simpa using this
  · simpa using o₀.inter o
  · intro x l hl
    have hl₀ : l ∈ L₀ := hl.1
    have hlL : l ∈ L := hl.2
    by_cases hx : x ∈ L
    · exact huv (Set.mk_mem_prod (hu hx) (h₀ hl₀))
    · rw [hzero x hx, hzero _ (fun hm => hx ?_)]
      simpa using L.sub_mem hm hlL

end GlobalTheory.CompanionTheory.SW.Core
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CuspRepresentativesFinite
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open nonZeroDivisors

namespace GlobalTheory.CompanionTheory.SW.Core.RowCompletion

variable {F : Type} [Field F] [NumberField F]

def Adapted (A : FractionalIdeal (𝓞 F)⁰ F) (g : SL(2, F)) : Prop :=
  g 0 0 ∈ A⁻¹ ∧ g 0 1 ∈ A⁻¹ ∧ g 1 0 ∈ A ∧ g 1 1 ∈ A

theorem integral_of_mem {A : FractionalIdeal (𝓞 F)⁰ F} (hA : A ≠ 0) {x y : F} (hx : x ∈ A)
    (hy : y ∈ A⁻¹) : ∃ z : 𝓞 F, (z : F) = x * y := by
  have h : x * y ∈ A * A⁻¹ := FractionalIdeal.mul_mem_mul hx hy
  rw [mul_inv_cancel₀ hA, FractionalIdeal.mem_one_iff] at h
  exact h

theorem exists_bezout {A : FractionalIdeal (𝓞 F)⁰ F} (hA : A ≠ 0) {p q : F}
    (h : A = FractionalIdeal.spanSingleton _ p + FractionalIdeal.spanSingleton _ q) :
    ∃ a ∈ A⁻¹, ∃ b ∈ A⁻¹, a * q - b * p = 1 := by
  have h1 : (1 : F) ∈ A * A⁻¹ := by
    rw [mul_inv_cancel₀ hA]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, by simp⟩
  have h2 : A * A⁻¹ = FractionalIdeal.spanSingleton _ p * A⁻¹ +
      FractionalIdeal.spanSingleton _ q * A⁻¹ := by
    calc A * A⁻¹ = (FractionalIdeal.spanSingleton _ p + FractionalIdeal.spanSingleton _ q) * A⁻¹ := by
          rw [← h]
      _ = _ := add_mul _ _ _
  rw [h2, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_add, Submodule.add_eq_sup,
    Submodule.mem_sup] at h1
  obtain ⟨s, hs, t, ht, hst⟩ := h1
  obtain ⟨s', hs', rfl⟩ := FractionalIdeal.mem_singleton_mul.1 (FractionalIdeal.mem_coe.1 hs)
  obtain ⟨t', ht', rfl⟩ := FractionalIdeal.mem_singleton_mul.1 (FractionalIdeal.mem_coe.1 ht)
  refine ⟨t', ht', -s', ?_, ?_⟩
  · exact FractionalIdeal.mem_coe.1 (neg_mem (FractionalIdeal.mem_coe.2 hs'))
  · linear_combination hst

theorem exists_adapted {A : FractionalIdeal (𝓞 F)⁰ F} (hA : A ≠ 0) {p q : F}
    (h : A = FractionalIdeal.spanSingleton _ p + FractionalIdeal.spanSingleton _ q) :
    ∃ g : SL(2, F), Adapted A g ∧ g 1 0 = p ∧ g 1 1 = q := by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_bezout hA h
  have hp : p ∈ A := by
    rw [h, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_add, Submodule.add_eq_sup]
    exact Submodule.mem_sup_left (FractionalIdeal.mem_coe.2
      (FractionalIdeal.mem_spanSingleton_self _ _))
  have hq : q ∈ A := by
    rw [h, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_add, Submodule.add_eq_sup]
    exact Submodule.mem_sup_right (FractionalIdeal.mem_coe.2
      (FractionalIdeal.mem_spanSingleton_self _ _))
  refine ⟨⟨!![a, b; p, q], by simpa [Matrix.det_fin_two] using hab⟩, ?_, by simp, by simp⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simpa

theorem integral_inv_mul {A : FractionalIdeal (𝓞 F)⁰ F} (hA : A ≠ 0) {r g : SL(2, F)}
    (hr : Adapted A r) (hg : Adapted A g) (i j : Fin 2) :
    ∃ z : 𝓞 F, (z : F) = (r⁻¹ * g) i j := by
  obtain ⟨r0, r1, r2, r3⟩ := hr
  obtain ⟨g0, g1, g2, g3⟩ := hg
  obtain ⟨z1, e1⟩ := integral_of_mem hA r3 g0
  obtain ⟨z2, e2⟩ := integral_of_mem hA r3 g1
  obtain ⟨z3, e3⟩ := integral_of_mem hA r2 g0
  obtain ⟨z4, e4⟩ := integral_of_mem hA r2 g1
  obtain ⟨z5, e5⟩ := integral_of_mem hA g2 r1
  obtain ⟨z6, e6⟩ := integral_of_mem hA g3 r1
  obtain ⟨z7, e7⟩ := integral_of_mem hA g2 r0
  obtain ⟨z8, e8⟩ := integral_of_mem hA g3 r0
  have hinv : ((r⁻¹ * g : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      !![r 1 1, -r 0 1; -r 1 0, r 0 0] * (g : Matrix (Fin 2) (Fin 2) F) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl]
    rfl
  rw [hinv]
  fin_cases i <;> fin_cases j
  · refine ⟨z1 - z5, ?_⟩
    simp only [map_sub, RingOfIntegers.map_mk, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast [e1, e5]
    simp
    ring
  · refine ⟨z2 - z6, ?_⟩
    push_cast [e2, e6]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · refine ⟨z7 - z3, ?_⟩
    push_cast [e7, e3]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · refine ⟨z8 - z4, ?_⟩
    push_cast [e8, e4]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring

theorem exists_scale (J I : (Ideal (𝓞 F))⁰) (h : ClassGroup.mk0 I = ClassGroup.mk0 J)
    {c d : 𝓞 F} (hI : (I : Ideal (𝓞 F)) = Ideal.span {c, d}) :
    ∃ l : F, l ≠ 0 ∧ |((Algebra.norm ℚ l : ℚ) : ℝ)| ≤ (Ideal.absNorm (J : Ideal (𝓞 F)) : ℝ) ∧
      ((J : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) =
        FractionalIdeal.spanSingleton _ (l * (c : F)) +
          FractionalIdeal.spanSingleton _ (l * (d : F)) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 h
  have hxF : (x : F) ≠ 0 := by simpa using hx
  have hyF : (y : F) ≠ 0 := by simpa using hy
  refine ⟨(x : F) / (y : F), div_ne_zero hxF hyF, ?_, ?_⟩
  · have hn := congrArg Ideal.absNorm hxy
    rw [map_mul, map_mul, Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton] at hn
    have key : ∀ w : 𝓞 F, (((Algebra.norm ℤ w).natAbs : ℕ) : ℝ) =
        |((Algebra.norm ℚ (w : F) : ℚ) : ℝ)| := by
      intro w
      rw [← Algebra.coe_norm_int]
      simp [Nat.cast_natAbs]
    have hmul : Algebra.norm ℚ (x : F) = Algebra.norm ℚ (y : F) * Algebra.norm ℚ ((x : F) / (y : F)) := by
      rw [← map_mul, mul_div_cancel₀ _ hyF]
    have hnR : (((Algebra.norm ℤ x).natAbs : ℕ) : ℝ) * (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) =
        (((Algebra.norm ℤ y).natAbs : ℕ) : ℝ) * (Ideal.absNorm (J : Ideal (𝓞 F)) : ℝ) := by
      exact_mod_cast hn
    rw [key, key, hmul] at hnR
    have hb : |((Algebra.norm ℚ (y : F) : ℚ) : ℝ)| ≠ 0 := by
      have : Algebra.norm ℚ (y : F) ≠ 0 := Algebra.norm_ne_zero_iff.2 hyF
      simpa using this
    have hI1 : (1 : ℝ) ≤ (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) := by
      have : Ideal.absNorm (I : Ideal (𝓞 F)) ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]
        exact nonZeroDivisors.ne_zero I.2
      exact_mod_cast Nat.one_le_iff_ne_zero.2 this
    set t := |((Algebra.norm ℚ ((x : F) / (y : F)) : ℚ) : ℝ)| with ht
    have h3 : t * (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) = (Ideal.absNorm (J : Ideal (𝓞 F)) : ℝ) := by
      apply mul_left_cancel₀ hb
      rw [← hnR]
      push_cast
      rw [abs_mul]
      ring
    have ht0 : 0 ≤ t := abs_nonneg _
    calc t = t * 1 := (mul_one t).symm
      _ ≤ t * (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) := mul_le_mul_of_nonneg_left hI1 ht0
      _ = _ := h3
  · have hF := congrArg (fun K : Ideal (𝓞 F) => (K : FractionalIdeal (𝓞 F)⁰ F)) hxy
    simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton] at hF
    rw [hI, Ideal.span_insert, FractionalIdeal.coeIdeal_sup,
      FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton] at hF
    simp only [← RingOfIntegers.coe_eq_algebraMap] at hF
    calc ((J : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
        = FractionalIdeal.spanSingleton _ (y : F)⁻¹ * (FractionalIdeal.spanSingleton _ (y : F) *
            ((J : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)) := by
          rw [← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hyF,
            FractionalIdeal.spanSingleton_one, one_mul]
      _ = FractionalIdeal.spanSingleton _ (y : F)⁻¹ * (FractionalIdeal.spanSingleton _ (x : F) *
            (FractionalIdeal.spanSingleton _ (c : F) + FractionalIdeal.spanSingleton _ (d : F))) := by
          rw [hF]
      _ = _ := by
          simp only [mul_add, FractionalIdeal.spanSingleton_mul_spanSingleton]
          congr 2 <;> field_simp

end GlobalTheory.CompanionTheory.SW.Core.RowCompletion


open GlobalTheory.CompanionTheory.SW.Core.RowCompletion in
open nonZeroDivisors GlobalTheory.CompanionTheory.SW.Core.RowCompletion in
theorem GlobalTheory.CompanionTheory.SW.Core.exists_finset_row_completion :
    ∀ (F : Type) [Field F] [NumberField F], ∃ (s : Finset SL(2, F)) (C : ℝ), ∀ c d : 𝓞 F, (c ≠ 0 ∨ d ≠ 0) → ∃ l : F, l ≠ 0 ∧ |((Algebra.norm ℚ l : ℚ) : ℝ)| ≤ C ∧ ∀ u : (𝓞 F)ˣ, ∃ r ∈ s, ∃ k : SL(2, F), (∀ i j, ∃ z : 𝓞 F, (z : F) = k i j) ∧ (r * k) 1 0 = ((u : 𝓞 F) : F) * l * (c : F) ∧ (r * k) 1 1 = ((u : 𝓞 F) : F) * l * (d : F) := by
  intro F _ _
  classical
  let J : ClassGroup (𝓞 F) → (Ideal (𝓞 F))⁰ := fun g => (ClassGroup.mk0_surjective g).choose
  have hJ : ∀ g, ClassGroup.mk0 (J g) = g := fun g => (ClassGroup.mk0_surjective g).choose_spec
  let A : ClassGroup (𝓞 F) → FractionalIdeal (𝓞 F)⁰ F :=
    fun g => ((J g : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
  have hA : ∀ g, A g ≠ 0 := by
    intro g
    simpa [A] using nonZeroDivisors.ne_zero (J g).2
  let r : ClassGroup (𝓞 F) → SL(2, F) := fun g =>
    if h : ∃ r, Adapted (A g) r then h.choose else 1
  have hr : ∀ g, (∃ r, Adapted (A g) r) → Adapted (A g) (r g) := by
    intro g h
    simp only [r, dif_pos h]
    exact h.choose_spec
  refine ⟨Finset.univ.image r, ∑ g, (Ideal.absNorm (J g : Ideal (𝓞 F)) : ℝ), ?_⟩
  intro c d hcd
  have hI : Ideal.span {c, d} ∈ (Ideal (𝓞 F))⁰ := by
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro h0
    have h1 : c ∈ Ideal.span {c, d} := Ideal.subset_span (by simp)
    have h2 : d ∈ Ideal.span {c, d} := Ideal.subset_span (by simp)
    rw [h0] at h1 h2
    rcases hcd with h | h
    · exact h (by simpa using h1)
    · exact h (by simpa using h2)
  let g := ClassGroup.mk0 ⟨Ideal.span {c, d}, hI⟩
  obtain ⟨l, hl0, hln, hlA⟩ := exists_scale (F := F) (J g) ⟨Ideal.span {c, d}, hI⟩ (hJ g).symm rfl
  refine ⟨l, hl0, hln.trans ?_, ?_⟩
  · exact Finset.single_le_sum (f := fun g => (Ideal.absNorm (J g : Ideal (𝓞 F)) : ℝ))
      (fun _ _ => by positivity) (Finset.mem_univ g)
  intro u
  have hu : FractionalIdeal.spanSingleton (𝓞 F)⁰ ((u : 𝓞 F) : F) = 1 := by
    have := FractionalIdeal.coeIdeal_span_singleton (S := (𝓞 F)⁰) (P := F) (u : 𝓞 F)
    rw [Ideal.span_singleton_eq_top.2 u.isUnit] at this
    simpa using this.symm
  have hAu : A g = FractionalIdeal.spanSingleton _ (((u : 𝓞 F) : F) * l * (c : F)) +
      FractionalIdeal.spanSingleton _ (((u : 𝓞 F) : F) * l * (d : F)) := by
    have : A g = FractionalIdeal.spanSingleton (𝓞 F)⁰ ((u : 𝓞 F) : F) * A g := by rw [hu, one_mul]
    rw [this]
    change _ * ((J g : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = _
    rw [hlA, mul_add, FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton, mul_assoc, mul_assoc]
  obtain ⟨γ, hγ, h10, h11⟩ := exists_adapted (hA g) hAu
  have hrg := hr g ⟨γ, hγ⟩
  refine ⟨r g, Finset.mem_image_of_mem _ (Finset.mem_univ g), (r g)⁻¹ * γ,
    integral_inv_mul (hA g) hrg hγ, ?_, ?_⟩
  · rw [mul_inv_cancel_left]; exact h10
  · rw [mul_inv_cancel_left]; exact h11
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsCuspReductionBound
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.SmallPair

theorem exists_realBasis {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F)
    (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) :
    ∃ (κ : Type) (_ : Fintype κ) (b : Module.Basis κ ℝ (InfinitePlace F → ℝ)),
      ∀ i, ∃ a : 𝓞 F, ∀ w, b i w = ρ w (a : F) := by
  classical
  have hc : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mpr w.2 (hF.isReal w.1)⟩
  let e : mixedEmbedding.mixedSpace F ≃ₗ[ℝ] (InfinitePlace F → ℝ) :=
    { toFun := fun z w => z.1 ⟨w, hF.isReal w⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun v => (fun w => v w.1, fun w => (hc.false w).elim)
      left_inv := fun z => by
        refine Prod.ext rfl ?_
        funext w
        exact (hc.false w).elim
      right_inv := fun v => rfl }
  refine ⟨_, inferInstance, (mixedEmbedding.latticeBasis F).map e, fun i =>
    ⟨RingOfIntegers.basis F i, fun w => ?_⟩⟩
  have h1 : ((mixedEmbedding.latticeBasis F).map e) i w
      = InfinitePlace.embedding_of_isReal (hF.isReal w) (integralBasis F i) := by
    rw [Module.Basis.map_apply, mixedEmbedding.latticeBasis_apply]
    exact mixedEmbedding.mixedEmbedding_apply_isReal F _ ⟨w, hF.isReal w⟩
  rw [h1, integralBasis_apply]
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, hρ]

noncomputable def block (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![√τ.im, 0; τ.re / √τ.im, 1 / √τ.im]

theorem det_block (τ : ℂ) (h : 0 < τ.im) : (block τ).det = 1 := by
  have : √τ.im ≠ 0 := (Real.sqrt_pos.mpr h).ne'
  simp [block, det_fin_two]
  field_simp

noncomputable def bigM {ι : Type} [Fintype ι] [DecidableEq ι] (τ : ι → ℂ) :
    Matrix (Fin 2 × ι) (Fin 2 × ι) ℝ :=
  blockDiagonal fun w => block (τ w)

theorem bigM_mulVec {ι : Type} [Fintype ι] [DecidableEq ι] (τ : ι → ℂ)
    (v : Fin 2 × ι → ℝ) (k : Fin 2) (w : ι) :
    (bigM τ *ᵥ v) (k, w) = ∑ j, block (τ w) k j * v (j, w) := by
  simp only [bigM, mulVec, dotProduct, Fintype.sum_prod_type, blockDiagonal_apply]
  rw [Finset.sum_comm]
  simp

theorem det_bigM {ι : Type} [Fintype ι] [DecidableEq ι] (τ : ι → ℂ)
    (h : ∀ w, 0 < (τ w).im) : (bigM τ).det = 1 := by
  simp [bigM, det_blockDiagonal, det_block _ (h _)]

theorem exists_small {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type} [Fintype κ]
    [Nonempty ι]
    (b : Module.Basis κ ℝ (ι → ℝ)) (S : AddSubgroup (ι → ℝ)) (hS : ∀ i, b i ∈ S) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ τ : ι → ℂ, (∀ w, 0 < (τ w).im) →
      ∃ u ∈ S, ∃ v ∈ S, (u ≠ 0 ∨ v ≠ 0) ∧ ∀ w,
        |√(τ w).im * u w| ≤ R ∧ |(τ w).re / √(τ w).im * u w + 1 / √(τ w).im * v w| ≤ R := by
  classical
  let b₂ : Module.Basis ((_ : Fin 2) × κ) ℝ (Fin 2 × ι → ℝ) :=
    (Pi.basis fun _ : Fin 2 => b).map (LinearEquiv.curry ℝ ℝ (Fin 2) ι).symm
  have hb₂ : ∀ (ji : (_ : Fin 2) × κ) (k : Fin 2) (w : ι),
      b₂ ji (k, w) = (Pi.single ji.1 (b ji.2) : Fin 2 → ι → ℝ) k w := by
    intro ji k w
    simp [b₂, Module.Basis.map_apply, Pi.basis_apply]
  have hfund := ZSpan.isAddFundamentalDomain' b₂ (volume : Measure (Fin 2 × ι → ℝ))
  have hfin : volume (ZSpan.fundamentalDomain b₂) ≠ ∞ :=
    (ZSpan.fundamentalDomain_isBounded b₂).measure_lt_top.ne
  set V : ℝ := (volume (ZSpan.fundamentalDomain b₂)).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hproj : ∀ z ∈ Submodule.span ℤ (Set.range b₂), ∀ k : Fin 2,
      (fun w => z (k, w)) ∈ S := by
    intro z hz k
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ji, rfl⟩ := hx
      by_cases hk : k = ji.1
      · subst hk
        have : (fun w => b₂ ji (ji.1, w)) = b ji.2 := by
          funext w; simp [hb₂]
        rw [this]; exact hS _
      · have : (fun w => b₂ ji (k, w)) = 0 := by
          funext w; simp [hb₂, Pi.single_eq_of_ne hk]
        rw [this]; exact S.zero_mem
    | zero => exact S.zero_mem
    | add x y _ _ hx hy => exact S.add_mem hx hy
    | smul a x _ hx =>
      have : (fun w => (a • x) (k, w)) = a • (fun w => x (k, w)) := by
        funext w; simp
      rw [this]; exact S.zsmul_mem hx a
  refine ⟨V + 1, by positivity, fun τ hτ => ?_⟩
  let f : (Fin 2 × ι → ℝ) →ₗ[ℝ] (Fin 2 × ι → ℝ) := Matrix.toLin' (bigM τ)
  have hdet : LinearMap.det f = 1 := by
    simp only [f, LinearMap.det_toLin', det_bigM τ hτ]
  let s : Set (Fin 2 × ι → ℝ) := f ⁻¹' Metric.closedBall 0 (V + 1)
  have hsymm : ∀ x ∈ s, -x ∈ s := by
    intro x hx
    simpa [s, map_neg] using hx
  have hconv : Convex ℝ s := (convex_closedBall _ _).linear_preimage f
  have hcard : 1 ≤ Fintype.card (Fin 2 × ι) := Fintype.card_pos
  have hvol : volume (ZSpan.fundamentalDomain b₂) * 2 ^ Module.finrank ℝ (Fin 2 × ι → ℝ)
      < volume s := by
    rw [Measure.addHaar_preimage_linearMap _ (by rw [hdet]; exact one_ne_zero),
      hdet, Real.volume_pi_closedBall _ (by positivity), Module.finrank_fintype_fun_eq_card]
    have h1 : volume (ZSpan.fundamentalDomain b₂) = ENNReal.ofReal V :=
      (ENNReal.ofReal_toReal hfin).symm
    rw [h1]
    simp only [inv_one, abs_one, ENNReal.ofReal_one, one_mul]
    have h2 : (2 : ℝ≥0∞) ^ Fintype.card (Fin 2 × ι)
        = ENNReal.ofReal (2 ^ Fintype.card (Fin 2 × ι)) := by
      rw [ENNReal.ofReal_pow (by norm_num)]; simp
    rw [h2, ← ENNReal.ofReal_mul hV0]
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    rw [mul_pow, mul_comm]
    have h3 : V < (V + 1) ^ Fintype.card (Fin 2 × ι) :=
      calc V < V + 1 := by linarith
        _ = (V + 1) ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ (by linarith) hcard
    exact mul_lt_mul_of_pos_left h3 (by positivity)
  have hcount : Countable (Submodule.span ℤ (Set.range b₂)).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range b₂))
    infer_instance
  obtain ⟨⟨x, hx⟩, hne, hmem⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hfund hsymm hconv hvol
  have hx' : x ∈ Submodule.span ℤ (Set.range b₂) := hx
  refine ⟨_, hproj x hx' 0, _, hproj x hx' 1, ?_, fun w => ?_⟩
  · by_contra hcon
    push_neg at hcon
    apply hne
    apply Subtype.ext
    funext ⟨k, w⟩
    fin_cases k
    · exact congrFun hcon.1 w
    · exact congrFun hcon.2 w
  · have hball : ‖f x‖ ≤ V + 1 := by
      simpa [s] using hmem
    have hco : ∀ k, |f x (k, w)| ≤ V + 1 := fun k => by
      have := (pi_norm_le_iff_of_nonneg (by positivity)).mp hball (k, w)
      simpa using this
    have e : ∀ k, f x (k, w) = ∑ j, block (τ w) k j * x (j, w) := fun k => by
      simp only [f, Matrix.toLin'_apply]
      exact bigM_mulVec τ x k w
    have h0 := hco 0
    have h1 := hco 1
    rw [e] at h0 h1
    simpa [block, Fin.sum_univ_two] using And.intro h0 h1

theorem exists_small_pair : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) →
    ∃ C : ℝ, ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∃ c d : 𝓞 F, (c ≠ 0 ∨ d ≠ 0) ∧
      ∀ w, ‖((ρ w (c : F) : ℝ) : ℂ) * τ w + (ρ w (d : F) : ℝ)‖ ^ 2 ≤ C * (τ w).im := by
  intro F _ _ hF ρ hρ
  classical
  obtain ⟨κ, _, b, hb⟩ := exists_realBasis hF ρ hρ
  let Φ : 𝓞 F →+ (InfinitePlace F → ℝ) :=
    { toFun := fun a w => ρ w (a : F)
      map_zero' := by funext w; simp
      map_add' := fun x y => by funext w; simp }
  obtain ⟨R, hR, H⟩ := exists_small b Φ.range (fun i => by
    obtain ⟨a, ha⟩ := hb i
    exact ⟨a, funext fun w => (ha w).symm⟩)
  refine ⟨2 * R ^ 2, fun τ hτ => ?_⟩
  obtain ⟨u, ⟨c, rfl⟩, v, ⟨d, rfl⟩, hne, hbd⟩ := H τ hτ
  refine ⟨c, d, ?_, fun w => ?_⟩
  · rcases hne with h | h
    · left; rintro rfl; exact h (map_zero Φ)
    · right; rintro rfl; exact h (map_zero Φ)
  · obtain ⟨h1, h2⟩ := hbd w
    set y := (τ w).im with hy
    set X := (τ w).re with hX
    have hy0 : 0 < y := hτ w
    have hs : 0 < √y := Real.sqrt_pos.mpr hy0
    have hss : √y * √y = y := Real.mul_self_sqrt hy0.le
    set a : ℝ := ρ w (c : F) with ha
    set e : ℝ := ρ w (d : F) with he
    have h1' : |√y * a| ≤ R := h1
    have h2' : |X / √y * a + 1 / √y * e| ≤ R := h2
    have q1 : (√y * a) ^ 2 ≤ R ^ 2 := sq_le_sq' (abs_le.mp h1').1 (abs_le.mp h1').2
    have q2 : (X / √y * a + 1 / √y * e) ^ 2 ≤ R ^ 2 :=
      sq_le_sq' (abs_le.mp h2').1 (abs_le.mp h2').2
    have r1 : y * a ^ 2 ≤ R ^ 2 := by
      have : (√y * a) ^ 2 = y * a ^ 2 := by rw [mul_pow, Real.sq_sqrt hy0.le]
      linarith
    have r2 : (X * a + e) ^ 2 ≤ R ^ 2 * y := by
      have : (X / √y * a + 1 / √y * e) ^ 2 * y = (X * a + e) ^ 2 := by
        have : X / √y * a + 1 / √y * e = (X * a + e) / √y := by field_simp
        rw [this, div_pow, Real.sq_sqrt hy0.le]
        field_simp
      rw [← this]
      exact mul_le_mul_of_nonneg_right q2 hy0.le
    have nrm : ‖((a : ℝ) : ℂ) * τ w + (e : ℝ)‖ ^ 2 = (a * X + e) ^ 2 + (a * y) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [hX, hy]
      ring
    rw [nrm]
    have r3 : (a * y) ^ 2 ≤ R ^ 2 * y := by
      have : (a * y) ^ 2 = (y * a ^ 2) * y := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right r1 hy0.le
    have r4 : (a * X + e) ^ 2 = (X * a + e) ^ 2 := by ring
    rw [r4]
    nlinarith

end GlobalTheory.CompanionTheory.SW.SmallPair
end

