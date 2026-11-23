module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Statements

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PAENeighbourhoods
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

namespace AENeighbourhoods

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]

def intBasis (E : Type) [Field E] [NumberField E] (l : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) : E :=
  algebraMap (𝓞 E) E (RingOfIntegers.basis E l)

theorem nhds_zero_finiteAdele {W : Set (FiniteAdeleRing (𝓞 F) F)} (hW : W ∈ 𝓝 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ x : FiniteAdeleRing (𝓞 F) F,
      (∀ v ∈ S, x v = 0) → (∀ v ∉ S, x v ∈ v.adicCompletionIntegers F) → x ∈ W := by
  have hopen : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => Valued.isOpen_valuationSubring _
  let W' : Set (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite) := W
  have h2 : W' ∈ Filter.map (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) =>
      v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      Filter.cofinite) (𝓝 0) := by
    rw [← RestrictedProduct.nhds_eq_map_structureMap hopen 0]
    exact hW
  have h1 := Filter.mem_map.1 h2
  rw [nhds_pi, Filter.mem_pi] at h1
  obtain ⟨I, hI, t, ht, hsub⟩ := h1
  refine ⟨hI.toFinset, fun x hx0 hxI => ?_⟩
  have hmem : ∀ v, x v ∈ v.adicCompletionIntegers F := fun v => by
    by_cases hv : v ∈ hI.toFinset
    · rw [hx0 v hv]; exact zero_mem _
    · exact hxI v hv
  let x' : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => ⟨x v, hmem v⟩
  have hx' : x' ∈ I.pi t := fun v hv => by
    have : x' v = 0 := Subtype.ext (hx0 v (hI.mem_toFinset.2 hv))
    rw [this]; exact mem_of_mem_nhds (ht v)
  have := hsub hx'
  exact this

theorem intAt_repr (v : HeightOneSpectrum (𝓞 F)) {z : Kv E v} (hz : z ∈ intAt E v) :
    ∃ y : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletion F,
      (∀ l, y l ∈ v.adicCompletionIntegers F) ∧ z = ∑ l, y l ⊗ₜ[F] intBasis E l := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, rfl⟩ := hx
    refine ⟨fun l => (RingOfIntegers.basis E).repr b l • a, fun l => zsmul_mem ha _, ?_⟩
    conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr b]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, tmul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_zsmul, ← smul_tmul]
    rfl
  | zero => exact ⟨0, fun l => zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨y₁, h₁, rfl⟩ := hx
    obtain ⟨y₂, h₂, rfl⟩ := hy
    exact ⟨y₁ + y₂, fun l => add_mem (h₁ l) (h₂ l), by simp [add_tmul, Finset.sum_add_distrib]⟩
  | neg x _ hx =>
    obtain ⟨y₁, h₁, rfl⟩ := hx
    exact ⟨-y₁, fun l => neg_mem (h₁ l), by simp [neg_tmul, Finset.sum_neg_distrib]⟩

theorem compAt_sum (v : HeightOneSpectrum (𝓞 F))
    (X : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → FiniteAdeleRing (𝓞 F) F) :
    compAt E v (∑ l, X l ⊗ₜ[F] intBasis E l) = ∑ l, X l v ⊗ₜ[F] intBasis E l := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]; rfl

theorem exists_repr (a : AE F E) :
    ∃ X : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → FiniteAdeleRing (𝓞 F) F,
      a = ∑ l, X l ⊗ₜ[F] intBasis E l := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul x y =>
    refine ⟨fun l => algebraMap ℚ F ((integralBasis E).repr y l) • x, ?_⟩
    conv_lhs => rw [← (integralBasis E).sum_repr y]
    rw [tmul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integralBasis_apply, ← IsScalarTower.algebraMap_smul F, tmul_smul, smul_tmul']
    rfl
  | add x y hx hy =>
    obtain ⟨X₁, rfl⟩ := hx
    obtain ⟨X₂, rfl⟩ := hy
    exact ⟨X₁ + X₂, by simp [add_tmul, Finset.sum_add_distrib]⟩

theorem exists_repr_of_int
    (hsep : ∀ a b : AE F E, (∀ v, compAt E v a = compAt E v b) → a = b)
    (S : Finset (HeightOneSpectrum (𝓞 F))) {m : AE F E} (h0 : ∀ v ∈ S, compAt E v m = 0)
    (hI : ∀ v ∉ S, compAt E v m ∈ intAt E v) :
    ∃ X : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → FiniteAdeleRing (𝓞 F) F,
      (∀ l, ∀ v ∈ S, X l v = 0) ∧ (∀ l, ∀ v ∉ S, X l v ∈ v.adicCompletionIntegers F) ∧
      m = ∑ l, X l ⊗ₜ[F] intBasis E l := by
  classical
  have hr : ∀ v, v ∉ S → ∃ y : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletion F,
      (∀ l, y l ∈ v.adicCompletionIntegers F) ∧ compAt E v m = ∑ l, y l ⊗ₜ[F] intBasis E l :=
    fun v hv => intAt_repr v (hI v hv)
  choose y hyI hyeq using hr
  let Y : ∀ v : HeightOneSpectrum (𝓞 F), Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletion F :=
    fun v => if hv : v ∈ S then 0 else y v hv
  have hYI : ∀ v l, Y v l ∈ v.adicCompletionIntegers F := fun v l => by
    by_cases hv : v ∈ S
    · simp only [Y, dif_pos hv, Pi.zero_apply]; exact zero_mem _
    · simp only [Y, dif_neg hv]; exact hyI v hv l
  let X : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → FiniteAdeleRing (𝓞 F) F :=
    fun l => ⟨fun v => Y v l, Filter.Eventually.of_forall fun v => hYI v l⟩
  refine ⟨X, fun l v hv => ?_, fun l v _ => hYI v l, hsep _ _ fun v => ?_⟩
  · change Y v l = 0
    simp only [Y, dif_pos hv, Pi.zero_apply]
  · rw [compAt_sum]
    change compAt E v m = ∑ l, Y v l ⊗ₜ[F] intBasis E l
    by_cases hv : v ∈ S
    · simp only [Y, dif_pos hv, Pi.zero_apply, zero_tmul, Finset.sum_const_zero]; exact h0 v hv
    · simp only [Y, dif_neg hv]; exact hyeq v hv

theorem int_cofinite (a : AE F E) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, compAt E v a ∈ intAt E v := by
  obtain ⟨X, rfl⟩ := exists_repr a
  have hev : ∀ᶠ v in Filter.cofinite, ∀ l, X l v ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun l => (X l).2
  refine ⟨(Filter.eventually_cofinite.1 hev).toFinset, fun v hv => ?_⟩
  have hv' : ∀ l, X l v ∈ v.adicCompletionIntegers F := by
    by_contra h
    exact hv ((Filter.eventually_cofinite.1 hev).mem_toFinset.2 h)
  rw [compAt_sum]
  exact AddSubgroup.sum_mem _ fun l _ => AddSubgroup.subset_closure ⟨X l v, hv' l, _, rfl⟩

theorem nhds_of_sep [TopologicalSpace (AE F E)] [IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (AE F E)]
    (hsep : ∀ a b : AE F E, (∀ v, compAt E v a = compAt E v b) → a = b) (N : ℕ)
    (U : Set (Matrix (Fin N) (Fin N) (AE F E))) (hU : U ∈ 𝓝 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ M : Matrix (Fin N) (Fin N) (AE F E),
      (∀ i j, (∀ v ∈ S, compAt E v (M i j) = 0) ∧ ∀ v ∉ S, compAt E v (M i j) ∈ intAt E v) →
      M ∈ U := by
  classical
  have := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (AE F E)
  let ι := Fin N × Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let Ψ : (ι → FiniteAdeleRing (𝓞 F) F) → Matrix (Fin N) (Fin N) (AE F E) :=
    fun X => Matrix.of fun i j => ∑ l, X (i, j, l) • ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] intBasis E l)
  have hΨ : Continuous Ψ :=
    continuous_pi fun i => continuous_pi fun j =>
      continuous_finsetSum _ fun l _ => (continuous_apply (i, j, l)).smul
        (continuous_const : Continuous fun _ : ι → FiniteAdeleRing (𝓞 F) F =>
          ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] intBasis E l))
  have hΨ0 : Ψ 0 = 0 := by ext i j; simp [Ψ]
  have hpre : Ψ ⁻¹' U ∈ 𝓝 (0 : ι → FiniteAdeleRing (𝓞 F) F) :=
    hΨ.continuousAt.preimage_mem_nhds (by rw [hΨ0]; exact hU)
  rw [nhds_pi, Filter.mem_pi] at hpre
  obtain ⟨I, -, t, ht, hsub⟩ := hpre
  obtain ⟨S, hS⟩ := nhds_zero_finiteAdele (Filter.iInter_mem.2 fun k : ι => ht k)
  refine ⟨S, fun M hM => ?_⟩
  choose X hX0 hXI hXeq using fun i j => exists_repr_of_int hsep S (hM i j).1 (hM i j).2
  have hmem : (fun k : ι => X k.1 k.2.1 k.2.2) ∈ I.pi t := fun k _ =>
    Set.mem_iInter.1 (hS _ (hX0 _ _ _) (hXI _ _ _)) k
  have hM' : Ψ (fun k : ι => X k.1 k.2.1 k.2.2) = M := by
    ext i j
    rw [hXeq i j]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_tmul', smul_eq_mul, mul_one]
  have hfin := hsub hmem
  rw [Set.mem_preimage, hM'] at hfin
  exact hfin

theorem of_placeMaps (hP : PlaceMaps.Statement) : AENeighbourhoods.Statement := by
  intro F E _ _ _ _ _ c h2 hc _ _
  exact ⟨fun N U hU => nhds_of_sep (hP F E c h2 hc).1 N U hU, int_cofinite⟩

theorem proof (_hT : AETopologicalRing.Statement) (hP : PlaceMaps.Statement) :
    AENeighbourhoods.Statement :=
  of_placeMaps hP

end AENeighbourhoods

end StrongApprox

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PAETopologicalRing
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem AETopologicalRing.aut_mul_self (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) :
    c * c = 1 := by
  classical
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  by_contra h
  have hc2 : c * c ≠ c := fun h' => hc (by simpa using congrArg (c⁻¹ * ·) h')
  have hcard : ({1, c, c * c} : Finset (E ≃ₐ[F] E)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hc2)]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hc, Ne.symm h⟩
  have hle := Finset.card_le_univ ({1, c, c * c} : Finset (E ≃ₐ[F] E))
  have := AlgEquiv.card_le (F := F) (K := E)
  omega

theorem AETopologicalRing.exists_anti (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) :
    ∃ δ : E, c δ = -δ ∧ δ ≠ 0 := by
  have hcc := AETopologicalRing.aut_mul_self c h2 hc
  obtain ⟨x, hx⟩ : ∃ x, c x ≠ x := by
    by_contra h
    push Not at h
    exact hc (AlgEquiv.ext h)
  refine ⟨x - c x, ?_, sub_ne_zero.2 (Ne.symm hx)⟩
  have hx2 : c (c x) = x := by rw [← AlgEquiv.mul_apply, hcc, AlgEquiv.one_apply]
  rw [map_sub, hx2]
  ring


omit [NumberField F] in
theorem AETopologicalRing.linearIndependent_one_anti (c : E ≃ₐ[F] E) {δ : E} (hδ : c δ = -δ)
    (h0 : δ ≠ 0) : LinearIndependent F ![(1 : E), δ] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
  have h' := congrArg c hst
  simp only [map_add (f := _), map_mul, AlgEquiv.commutes, hδ, map_zero] at h'
  have ht : algebraMap F E t = 0 := by
    have : (2 * δ) * algebraMap F E t = 0 := by linear_combination hst - h'
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero h0)
  have ht' : t = 0 := (map_eq_zero_iff _ (algebraMap F E).injective).1 ht
  subst ht'
  simp only [map_zero, zero_mul, add_zero] at hst
  exact ⟨(map_eq_zero_iff _ (algebraMap F E).injective).1 hst, rfl⟩

def AETopologicalRing.sigALinear (c : E ≃ₐ[F] E) :
    AE F E →ₗ[FiniteAdeleRing (𝓞 F) F] AE F E :=
  LinearMap.baseChange (FiniteAdeleRing (𝓞 F) F) c.toLinearMap

omit [NumberField E] in
theorem AETopologicalRing.sigALinear_apply (c : E ≃ₐ[F] E) (a : AE F E) :
    AETopologicalRing.sigALinear c a = sigA c a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

end


open scoped RestrictedProduct in
theorem AETopologicalRing.t2Space_finiteAdeleRing (F : Type) [Field F] [NumberField F] :
    T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
    [v.adicCompletion F, v.adicCompletionIntegers F]))

theorem AETopologicalRing.proof : AETopologicalRing.Statement := by
  intro F E _ _ _ _ _ c h2 hc _ _
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  have : IsTopologicalRing (AE F E) :=
    IsModuleTopology.isTopologicalRing (FiniteAdeleRing (𝓞 F) F) (AE F E)
  have hσ : Continuous (sigA c) := by
    have := IsModuleTopology.continuous_of_linearMap (R := FiniteAdeleRing (𝓞 F) F)
      (AETopologicalRing.sigALinear c)
    convert this using 1
    funext a
    exact (AETopologicalRing.sigALinear_apply c a).symm
  obtain ⟨δ, hδ, h0⟩ := AETopologicalRing.exists_anti c h2 hc
  let b : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank (AETopologicalRing.linearIndependent_one_anti c hδ h0)
      (by simp [h2])
  let B := Algebra.TensorProduct.basis (FiniteAdeleRing (𝓞 F) F) b
  have hB0 : B 0 = (1 : AE F E) := by
    simp [B, b, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.one_def]
  have hB1 : B 1 = inclA F E δ := by
    simp [B, b, Algebra.TensorProduct.basis_apply]
    rfl
  have := AETopologicalRing.t2Space_finiteAdeleRing F
  have : T2Space (AE F E) := T2Space.of_injective_continuous B.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap (R := FiniteAdeleRing (𝓞 F) F) B.equivFun.toLinearMap)
  refine ⟨inferInstance, hσ, ⟨δ, hδ, fun a => ⟨(B.repr a 0, B.repr a 1), ?_, ?_⟩⟩, fun N J => ?_⟩
  · have := B.sum_repr a
    rw [Fin.sum_univ_two, hB0, hB1] at this
    exact this.symm
  · rintro ⟨p₁, p₂⟩ hp
    rw [hp, ← hB0, ← hB1]
    simp
  · have hmul : Continuous (fun p : Matrix (Fin N) (Fin N) (AE F E) × Matrix (Fin N) (Fin N) (AE F E) =>
        p.1 * p.2) := continuous_fst.matrix_mul continuous_snd
    have hform : Continuous (fun g : Matrix (Fin N) (Fin N) (AE F E) => gᵀ * J * g.map (sigA c)) :=
      (continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul (continuous_id.matrix_map hσ)
    have hdet : Continuous (fun g : Matrix (Fin N) (Fin N) (AE F E) => g.det) := continuous_id.matrix_det
    exact ⟨hmul, hform, hdet, (isClosed_eq hdet continuous_const).inter (isClosed_eq hform continuous_const)⟩

end StrongApprox

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PClosureIsSubmonoid
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

theorem invol_of_quadratic {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E)
    (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (x : E) : c (c x) = x := by
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hle : Fintype.card (E ≃ₐ[F] E) ≤ 2 := h2 ▸ AlgEquiv.card_le
  have hge : 2 ≤ Fintype.card (E ≃ₐ[F] E) :=
    Fintype.one_lt_card_iff.2 ⟨c, 1, hc⟩
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := le_antisymm hle hge
  have hsq : c ^ 2 = 1 := hcard ▸ pow_card_eq_one
  have := congrArg (fun g : E ≃ₐ[F] E => g x) hsq
  simpa [pow_two] using this

theorem sigA_inclA_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) (x : E) : sigA c (inclA F E x) = inclA F E (c x) := by
  simp [sigA, inclA, Algebra.TensorProduct.map_tmul]

theorem map_mem_SU_AE {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) {γ : Matrix (Fin N) (Fin N) E}
    (hγ : γ ∈ SU c.toRingHom J) :
    γ.map (inclA F E) ∈ SU (sigA c) (J.map (inclA F E)) := by
  obtain ⟨hdet, hJ⟩ := hγ
  refine ⟨?_, ?_⟩
  · have h := (RingHom.map_det (inclA F E) γ).symm
    rw [hdet, map_one] at h
    exact h
  · have hmap : (γ.map (inclA F E)).map (sigA c) = (γ.map c.toRingHom).map (inclA F E) := by
      ext i j; simp [sigA_inclA_gen]
    rw [hmap, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hJ]

theorem ClosureIsSubmonoid.proof (h₁ : AETopologicalRing.Statement) (h₂ : EichlerDense.Statement) :
    ClosureIsSubmonoid.Statement := by
  intro F E _ _ _ _ _ c h2 hc N J hJ _ e f he hff hef _ _
  have hσ : ∀ x, c.toRingHom (c.toRingHom x) = x := invol_of_quadratic c h2 hc
  have hJ' : Jᵀ = J.map c.toRingHom := hJ
  obtain ⟨-, -, -, hmat⟩ := h₁ F E c h2 hc
  obtain ⟨hmul, -, -, hclosed⟩ := hmat N (J.map (inclA F E))
  obtain ⟨hde, hdf⟩ := h₂ F E c h2 hc N J hJ e f he hff hef
  set ι : Matrix (Fin N) (Fin N) E → Matrix (Fin N) (Fin N) (AE F E) := fun γ => γ.map (inclA F E)
  have himg : ι '' SU c.toRingHom J ⊆ SU (sigA c) (J.map (inclA F E)) := by
    rintro _ ⟨γ, hγ, rfl⟩; exact map_mem_SU_AE c J hγ
  refine ⟨closure_minimal himg hclosed, ?_, ?_, ?_⟩
  · apply subset_closure
    exact ⟨1, one_mem_SU, by simp⟩
  · intro a ha b hb
    refine map_mem_closure₂ hmul ha hb ?_
    rintro _ ⟨γ, hγ, rfl⟩ _ ⟨δ, hδ, rfl⟩
    exact ⟨γ * δ, mul_mem_SU hγ hδ, by simp [Matrix.map_mul]⟩
  · have hsub : ∀ {a b : Fin N → E}, hf c.toRingHom J a a = 0 →
        closure (ι '' eichAlong c.toRingHom J a b) ⊆ Cl c J := fun ha =>
      closure_mono (Set.image_mono (eichAlong_sub hσ hJ' ha))
    rintro M (hM | hM)
    · exact hsub he (hde hM)
    · exact hsub hff (hdf hM)

end StrongApprox

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PEDenseInAE
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

theorem EDenseInAE.proof (hT : AETopologicalRing.Statement) : EDenseInAE.Statement := by
  intro F E _ _ _ _ _ c h2 hc _ _
  obtain ⟨-, -, ⟨δ, -, hδ⟩, -⟩ := hT F E c h2 hc
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (AE F E)
  let φ : FiniteAdeleRing (𝓞 F) F × FiniteAdeleRing (𝓞 F) F → AE F E :=
    fun p => p.1 • (1 : AE F E) + p.2 • inclA F E δ
  have hφc : Continuous φ :=
    by unfold φ; fun_prop
  have hφs : Function.Surjective φ := fun a => by
    obtain ⟨p, hp, -⟩ := hδ a
    exact ⟨p, hp.symm⟩
  have hK : DenseRange (algebraMap F (FiniteAdeleRing (𝓞 F) F)) :=
    denseRange_finiteAdele (R := 𝓞 F) (K := F)
  have hD : DenseRange (φ ∘ Prod.map (algebraMap F (FiniteAdeleRing (𝓞 F) F))
      (algebraMap F (FiniteAdeleRing (𝓞 F) F))) :=
    hφs.denseRange.comp (hK.prodMap hK) hφc
  refine hD.mono ?_
  rintro _ ⟨⟨x, y⟩, rfl⟩
  refine ⟨algebraMap F E x + algebraMap F E y * δ, ?_⟩
  simp only [Function.comp_apply, Prod.map_apply, φ, algebraMap_smul, map_add (f := _), map_mul]
  have hinc : ∀ z : F, inclA F E (algebraMap F E z) = z • (1 : AE F E) := fun z => by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] AE F E).commutes z
  rw [hinc, hinc, smul_one_mul]

end StrongApprox

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PHypPairExists
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix ReciprocityTheory.ChartRestriction.G.SA

theorem HypPairExists.proof : HypPairExists.Statement := by
  intro E _ σ hσ h2 N J hJ hdet e he0 hee

  have hw : ∃ j, ∑ i, e i * J i j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have h0 : e ᵥ* J = 0 := by
      ext j
      simpa [vecMul, dotProduct] using h j
    apply he0
    calc e = e ᵥ* (J * J⁻¹) := by rw [mul_nonsing_inv J hdet, vecMul_one]
      _ = (e ᵥ* J) ᵥ* J⁻¹ := by rw [vecMul_vecMul]
      _ = 0 := by rw [h0, zero_vecMul]
  obtain ⟨j, hj⟩ := hw
  have hsingle : hf σ J e (Pi.single j 1) = ∑ i, e i * J i j := by
    simp only [hf]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [hk]
    · simp

  obtain ⟨a, hea⟩ : ∃ a : Fin N → E, hf σ J e a = 1 :=
    ⟨σ (∑ i, e i * J i j)⁻¹ • Pi.single j 1, by
      rw [hf_smul_right, hsingle, hσ, inv_mul_cancel₀ hj]⟩
  have hae : hf σ J a e = 1 := by
    rw [← hf_symm hσ hJ, hea, map_one]
  have haa : σ (hf σ J a a) = hf σ J a a := hf_symm hσ hJ a a
  set t : E := -(hf σ J a a) / 2 with ht_def
  have hσ2 : σ 2 = 2 := map_ofNat σ 2
  have ht : t + σ t = -(hf σ J a a) := by
    rw [ht_def, map_div₀, map_neg, haa, hσ2]
    field_simp
    ring
  refine ⟨a + t • e, ?_, ?_⟩
  · rw [hf_add_left, hf_add_right, hf_add_right, hf_smul_left, hf_smul_left, hf_smul_right,
      hf_smul_right, hea, hae, hee]
    linear_combination ht
  · rw [hf_add_right, hf_smul_right, hea, hee, mul_zero, add_zero]

end StrongApprox

end GroundTheory.Heights₂.Heights
end
end

