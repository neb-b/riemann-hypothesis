module

public import Formalism.FilteredPoleLength.ReducedBasisBounds.Bundle0002
public import Formalism.LogFactorialIndices.LogProductFormula
public import Lemmata.MiscLemmasO.Imports
public import Formalism.GelfandTransference.HadamardGelfand.Hadamard
public import Formalism.FilteredPoleLength.ReducedBasisBounds.LengthBaseChangeLocal
public import Formalism.FilteredPoleLength.LocalDescentLevels.MemSpanBasisFun

@[expose] public section

-- bundled from Formalism.FilteredPoleLength.LocalDescentLevels.ExistsSmulMemOfMemSpan
section
noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module

theorem exists_smul_mem_of_mem_span_alt (O K V : Type) [CommRing O] [IsDomain O]
    [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (M : Submodule O V) (v : V) (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ c : O, c ≠ 0 ∧ c • v ∈ M := by
  first | exact Bl.SecondBlockLemmaP.goal1 .. | (apply Bl.SecondBlockLemmaP.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaP.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaP.goal1 <;> assumption) | (intros; apply @Bl.SecondBlockLemmaP.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaP.goal1 <;> first | assumption | infer_instance) | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› M v hv | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› M v | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› M | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V | exact @Bl.SecondBlockLemmaP.goal1 O K | exact @Bl.SecondBlockLemmaP.goal1 O

theorem exists_adapted_basis_alt (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    (M : Submodule O V) (V' : Submodule K V) (hM : Formalism.LatticeIndexTer.IsLat O K V M) :
    ∃ (b : Basis (Fin (finrank K V)) K V) (s : Set (Fin (finrank K V))),
      M ≤ Submodule.span O (Set.range b) ∧ (∀ i ∈ s, b i ∈ M ∧ b i ∈ V') ∧
        V' ≤ Submodule.span K (b '' s) := by
  obtain ⟨b0, hb0⟩ := Formalism.LatticeIndexTer.latBasis O K V M hM
  have hli0 : LinearIndependent O b0 :=
    (LinearIndependent.iff_fractionRing O K).mpr b0.linearIndependent
  let bO : Basis (Fin (finrank K V)) O M :=
    (Basis.span hli0).map (LinearEquiv.ofEq _ _ hb0.symm)
  obtain ⟨n, bM, bN, f, a, snf⟩ :=
    Submodule.smithNormalForm bO ((V'.restrictScalars O).comap M.subtype)
  have hliO : LinearIndependent O (fun i => (bM i : V)) :=
    bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hliK : LinearIndependent K (fun i => (bM i : V)) :=
    (LinearIndependent.iff_fractionRing O K).mp hliO
  have hspanO : M ≤ Submodule.span O (Set.range (fun i => (bM i : V))) := by
    intro m hm
    have h1 : (⟨m, hm⟩ : M) ∈ Submodule.span O (Set.range bM) := by
      rw [bM.span_eq]; trivial
    have h2 := Submodule.mem_map_of_mem (f := M.subtype) h1
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact h2
  have hspanK : ⊤ ≤ Submodule.span K (Set.range (fun i => (bM i : V))) := by
    rw [← hM.2]
    apply Submodule.span_le.mpr
    intro m hm
    exact Submodule.span_le_restrictScalars O K _ (hspanO hm)
  let b : Basis (Fin (finrank K V)) K V := Basis.mk hliK hspanK
  have hb : ∀ i, b i = (bM i : V) := fun i => by simp [b]
  have hrange : Set.range b = Set.range (fun i => (bM i : V)) := by
    ext x; simp [hb]
  refine ⟨b, Set.range f, ?_, ?_, ?_⟩
  · rw [hrange]; exact hspanO
  · rintro _ ⟨k, rfl⟩
    rw [hb]
    refine ⟨(bM (f k)).2, ?_⟩
    have hmem : ((bN k : M) : V) ∈ V' := (bN k).2
    rw [snf k] at hmem
    have ha : a k ≠ 0 := by
      intro h0
      have : (bN k : M) = 0 := by rw [snf k, h0, zero_smul]
      exact bN.ne_zero k (Subtype.ext this)
    have haK : algebraMap O K (a k) ≠ 0 := by
      simpa using (IsFractionRing.injective O K).ne ha
    have h3 : algebraMap O K (a k) • ((bM (f k) : M) : V) ∈ V' := by
      rw [algebraMap_smul]; simpa using hmem
    exact (V'.smul_mem_iff haK).mp h3
  · intro v hv
    have hv' : v ∈ Submodule.span K (M : Set V) := by rw [hM.2]; trivial
    obtain ⟨c, hc, hcv⟩ := exists_smul_mem_of_mem_span_alt O K V M v hv'
    have hcK : algebraMap O K c ≠ 0 := by
      simpa using (IsFractionRing.injective O K).ne hc
    have hcV : c • v ∈ V' := by
      rw [← algebraMap_smul K c]; exact V'.smul_mem _ hv
    let w : ((V'.restrictScalars O).comap M.subtype : Submodule O M) := ⟨⟨c • v, hcv⟩, hcV⟩
    have hw : w ∈ Submodule.span O (Set.range bN) := by rw [bN.span_eq]; trivial
    have key : ∀ u ∈ Submodule.span O (Set.range bN),
        ((u : M) : V) ∈ Submodule.span K (b '' Set.range f) := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        rw [snf k]
        have : ((a k • bM (f k) : M) : V) = algebraMap O K (a k) • b (f k) := by
          rw [hb, algebraMap_smul]; rfl
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f k, ⟨k, rfl⟩, rfl⟩)
      | zero => simp
      | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
      | smul r x _ hx =>
        have : (((r • x : _) : M) : V) = algebraMap O K r • ((x : M) : V) := by
          rw [algebraMap_smul]; rfl
        rw [this]
        exact Submodule.smul_mem _ _ hx
    have h4 : algebraMap O K c • v ∈ Submodule.span K (b '' Set.range f) := by
      rw [algebraMap_smul]; exact key w hw
    exact (Submodule.smul_mem_iff _ hcK).mp h4

theorem inter_baseChange_lattice : SpanImageInf := by
  intro O O' K K' V V₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj M V' hM
  obtain ⟨b, s, hMb, hs, hV'⟩ := exists_adapted_basis_alt O K V M V' hM
  let b' : Basis (Fin (finrank K V)) K' V₁ := hj.basis b
  have hb' : ∀ i, b' i = j (b i) := fun i => hj.basis_apply b i
  have hjO : ∀ (o : O) (v : V), j (o • v) = algebraMap O O' o • j v := by
    intro o v
    rw [← algebraMap_smul K o v, map_smul, ← algebraMap_smul K' (algebraMap O K o) (j v),
      ← algebraMap_smul K' (algebraMap O O' o) (j v), ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  have hjK : ∀ (k : K) (v : V), j (k • v) = algebraMap K K' k • j v := by
    intro k v
    rw [map_smul, algebraMap_smul]
  have hO : ∀ y ∈ Submodule.span O (Set.range b), j y ∈ Submodule.span O' (Set.range b') := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Submodule.subset_span ⟨i, hb' i⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [hjO]; exact Submodule.smul_mem _ _ hy
  have hK : ∀ y ∈ Submodule.span K (b '' s), j y ∈ Submodule.span K' (b' '' s) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact Submodule.subset_span ⟨i, hi, hb' i⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [hjK]; exact Submodule.smul_mem _ _ hy
  apply le_antisymm
  · rintro x ⟨hx1, hx2⟩
    have h1 : x ∈ Submodule.span O' (Set.range b') := by
      refine (Submodule.span_le.mpr ?_) hx1
      rintro _ ⟨m, hm, rfl⟩
      exact hO m (hMb hm)
    have h2 : x ∈ Submodule.span K' (b' '' s) := by
      refine (Submodule.span_le.mpr ?_) hx2
      rintro _ ⟨m, hm, rfl⟩
      exact hK m (hV' hm)
    rw [b'.mem_span_iff_repr_mem O'] at h1
    rw [b'.mem_span_image] at h2
    rw [← b'.sum_repr x]
    refine Submodule.sum_mem _ ?_
    intro i _
    by_cases hi : i ∈ s
    · obtain ⟨c, hc⟩ := h1 i
      rw [← hc, algebraMap_smul, hb']
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b i, hs i hi, rfl⟩)
    · have : b'.repr x i = 0 := by
        by_contra h0
        exact hi (h2 (by simpa using h0))
      rw [this, zero_smul]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨m, ⟨hm1, hm2⟩, rfl⟩
    exact ⟨Submodule.subset_span ⟨m, hm1, rfl⟩, Submodule.subset_span ⟨m, hm2, rfl⟩⟩

end Formalism.LatticeBaseChangeAlt
end
end

-- bundled from Formalism.FilteredPoleLength.LocalDescentLevels.InvFromBlocksApplyZero
section
noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module Matrix MeasureTheory

theorem complexHadamard : ComplexHadamard := by
  intro n M A hA
  have h1 := Formalism.HadamardInequality.P.hadamard_inequality_holds n M.transpose
  rw [Matrix.det_transpose] at h1
  simp only [Matrix.transpose_apply] at h1
  have hprod : (∏ j, Real.sqrt (∑ i, ‖M i j‖ ^ 2)) ^ 2 = ∏ j, ∑ i, ‖M i j‖ ^ 2 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun j _ =>
      Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)
  refine ⟨?_, ?_⟩
  · refine (pow_le_pow_iff_left₀ (norm_nonneg _)
      (Finset.prod_nonneg fun j _ => Real.sqrt_nonneg _) two_ne_zero).1 ?_
    rw [hprod]
    exact h1
  · have h2 := Formalism.HadamardInequality.P.hadamard_maximum_holds n M A hA
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hA0 : 0 ≤ A := le_trans (norm_nonneg _) (hA ⟨0, hn⟩ ⟨0, hn⟩)
    have h3 : ((Real.sqrt n * A) ^ n) ^ 2 = ((n : ℝ) * A ^ 2) ^ n := by
      rw [← pow_mul, mul_comm n 2, pow_mul, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [h3]
    exact h2

end Formalism.LatticeBaseChangeAlt
end
end

-- bundled from Formalism.FilteredPoleLength.LocalDescentLevels.LatticeDescent
section
noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module

namespace LatticeDescentAlt

variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

theorem span_inf_eq (M : Submodule O V) (hM : Formalism.LatticeIndexTer.IsLat O K V M) (V' : Submodule K V) :
    Submodule.span K ((M ⊓ V'.restrictScalars O : Submodule O V) : Set V) = V' := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact hx.2
  · intro v hv
    obtain ⟨d, hd, hdv⟩ := Formalism.LatticeIndexTer.LatticeIndexLength.exists_smul_mem_of_span (K := K) M hM.2 v
    have hd' : (algebraMap O K d) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hd
    have hmem : d • v ∈ (M ⊓ V'.restrictScalars O : Submodule O V) := by
      refine ⟨hdv, ?_⟩
      show d • v ∈ V'
      rw [← algebraMap_smul K d v]
      exact V'.smul_mem _ hv
    have hsp := Submodule.subset_span (R := K) hmem
    have : v = (algebraMap O K d)⁻¹ • (d • v) := by
      rw [← algebraMap_smul K d v, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hsp

theorem fg_inf (M : Submodule O V) (hM : Formalism.LatticeIndexTer.IsLat O K V M) (N : Submodule O V) :
    (M ⊓ N).FG := by
  have : IsNoetherian O M := isNoetherian_of_fg_of_noetherian M hM.1
  have h := IsNoetherian.noetherian (N.comap M.subtype)
  have := h.map M.subtype
  rwa [Submodule.map_comap_subtype] at this

end LatticeDescentAlt

theorem localStepDescent_of (h2 : FinrankSpanImage) (h3 : SpanImageInf) (h4 : RelIndexSpanImage) :
    LocalStepDescent := by
  intro O O' K K' V V₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj ϖ hϖ hϖ' M Θ V'
    hM hΘ d Y Z e h
  rw [h3 O O' K K' V V₁ j hj M V' hM, h3 O O' K K' V V₁ j hj Θ V' hΘ,
    h2 O O' K K' V V₁ j hj V',
    h4 O O' K K' V V₁ j hj ϖ hϖ hϖ' _ _ (LatticeDescentAlt.fg_inf M hM _) (LatticeDescentAlt.fg_inf Θ hΘ _)
      (by rw [LatticeDescentAlt.span_inf_eq M hM V', LatticeDescentAlt.span_inf_eq Θ hΘ V'])] at h
  exact h

end Formalism.LatticeBaseChangeAlt
end
end

-- bundled from Formalism.FilteredPoleLength.LocalDescentLevels.LengthBaseChange
section
noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module TensorProduct

namespace LengthBaseChangeAlt

theorem length_baseChange_eq_mul {O O₁ : Type} [CommRing O] [CommRing O₁] [Algebra O O₁]
    [Module.Flat O O₁] (ε : ℕ∞)
    (hs : ∀ (S : Type) [AddCommGroup S] [Module O S], IsSimpleModule O S →
      Module.length O₁ (TensorProduct O O₁ S) = ε)
    (Q : Type) [AddCommGroup Q] [Module O Q] (h : IsFiniteLength O Q) :
    Module.length O₁ (TensorProduct O O₁ Q) = ε * Module.length O Q := by
  induction h with
  | of_subsingleton =>
    rw [Module.length_eq_zero (R := O), mul_zero, Module.length_eq_zero_iff]
    refine ⟨fun x y => ?_⟩
    rw [← sub_eq_zero]
    generalize x - y = z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul a b => rw [Subsingleton.elim b 0, TensorProduct.tmul_zero]
    | add u v hu hv => rw [hu, hv, add_zero]
  | of_simple_quotient hN ih =>
    rename_i M _ _ N hS
    have e1 := Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N)
    have e2 := Module.length_eq_add_of_exact ((N.subtype).baseChange O₁) ((N.mkQ).baseChange O₁)
      (by
        rw [LinearMap.baseChange_eq_ltensor]
        exact Module.Flat.lTensor_preserves_injective_linearMap (M := O₁) _ N.injective_subtype)
      (by
        rw [LinearMap.baseChange_eq_ltensor]
        exact LinearMap.lTensor_surjective O₁ N.mkQ_surjective)
      (by
        rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
        exact Module.Flat.lTensor_exact (M := O₁) (LinearMap.exact_subtype_mkQ N))
    rw [e1, e2, ih, hs _ hS, Module.length_eq_one_iff.mpr hS]
    ring

end LengthBaseChangeAlt

theorem lengthBaseChangeLocal : LengthBaseChangeLocal := by
  intro O O₁ Q _ _ _ _ _ _ _ _ _ ϖ ϖ₁ u ε hϖ hϖ₁ hu hQ
  have hinj : Function.Injective (algebraMap O O₁) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨k, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
    rw [map_mul, map_pow, hu] at hx
    rcases mul_eq_zero.1 hx with h | h
    · exact ((v.isUnit.map (algebraMap O O₁)).ne_zero) h
    · exact (pow_ne_zero _ (mul_ne_zero u.ne_zero (pow_ne_zero _ hϖ₁.ne_zero))) h
  have : Module.IsTorsionFree O O₁ := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
  have : Module.Flat O O₁ := inferInstance
  rw [Module.length_ne_top_iff] at hQ
  refine LengthBaseChangeAlt.length_baseChange_eq_mul (ε : ℕ∞) ?_ Q hQ
  intro S _ _ hS
  obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hS
  obtain rfl := IsLocalRing.eq_maximalIdeal hm
  rw [(TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl O₁ O₁) e).length_eq,
    ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot O₁
      (IsLocalRing.maximalIdeal O)).toLinearEquiv.length_eq,
    hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hu]
  change Ring.ord O₁ _ = _
  rw [Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_uniformizer hϖ₁]
  simp

namespace LengthBaseChangeAlt

open BQuot

section Ext

variable {O K K₁ V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [Field K₁] [Algebra K K₁] [FiniteDimensional K K₁]
  [Algebra.IsSeparable K K₁] [Algebra O K₁] [IsScalarTower O K K₁]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

end Ext

end LengthBaseChangeAlt


end Formalism.LatticeBaseChangeAlt
end
end

