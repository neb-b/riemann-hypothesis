module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBasisTensor
section
noncomputable section

open scoped TensorProduct
open Module

namespace GlobalTheory.SemilinearExt

open GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases

section

variable {O K K'' : Type} [CommRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [Field K''] [Algebra O K''] [Algebra K K''] [IsScalarTower O K K'']
  {Fm : Type} [AddCommGroup Fm] [Module K Fm] [Module O Fm] [IsScalarTower O K Fm]

theorem algebraMap_tmul (c : K) (m : Fm) :
    algebraMap K K'' c ⊗ₜ[O] m = (1 : K'') ⊗ₜ[O] (c • m) := by
  obtain ⟨⟨a, b⟩, hc⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) c
  dsimp only at hc
  subst hc
  have hb : algebraMap O K (b : O) ≠ 0 := (IsLocalization.map_units K b).ne_zero
  set m₀ : Fm := (algebraMap O K (b : O))⁻¹ • m with hm₀
  have h1 : (b : O) • m₀ = m := by
    rw [← algebraMap_smul K (b : O) m₀, hm₀, smul_smul, mul_inv_cancel₀ hb, one_smul]
  have h2 : IsLocalization.mk' K a b • m = (a : O) • m₀ := by
    rw [← algebraMap_smul K a m₀, hm₀, smul_smul, ← div_eq_mul_inv, IsFractionRing.mk'_eq_div]
  have h3 : (b : O) • algebraMap K K'' (IsLocalization.mk' K a b) = (a : O) • (1 : K'') := by
    rw [Algebra.smul_def, Algebra.smul_def, mul_one, IsScalarTower.algebraMap_apply O K K'' (b : O),
      IsScalarTower.algebraMap_apply O K K'' a, ← map_mul, IsLocalization.mk'_spec']
  calc algebraMap K K'' (IsLocalization.mk' K a b) ⊗ₜ[O] m
      = algebraMap K K'' (IsLocalization.mk' K a b) ⊗ₜ[O] ((b : O) • m₀) := by rw [h1]
    _ = ((b : O) • algebraMap K K'' (IsLocalization.mk' K a b)) ⊗ₜ[O] m₀ :=
        (TensorProduct.smul_tmul _ _ _).symm
    _ = ((a : O) • (1 : K'')) ⊗ₜ[O] m₀ := by rw [h3]
    _ = (1 : K'') ⊗ₜ[O] ((a : O) • m₀) := TensorProduct.smul_tmul _ _ _
    _ = (1 : K'') ⊗ₜ[O] (IsLocalization.mk' K a b • m) := by rw [h2]

theorem exists_basis_tensor {ι : Type} (b : Basis ι K Fm) :
    ∃ c : Basis ι K'' (K'' ⊗[O] Fm), ∀ i, c i = (1 : K'') ⊗ₜ[O] b i := by
  have : TensorProduct.CompatibleSMul O K K'' Fm := ⟨fun c x m => by
    rw [Algebra.smul_def, mul_comm, ← smul_eq_mul x, ← TensorProduct.smul_tmul', algebraMap_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]⟩
  refine ⟨(Algebra.TensorProduct.basis K'' b).map (TensorProduct.equivOfCompatibleSMul O K K'' K'' Fm),
    fun i => ?_⟩
  rw [Basis.map_apply, Algebra.TensorProduct.basis_apply]
  rfl

end

def extOfBasis {L L' V V' : Type} [Field L] [Field L'] [AddCommGroup V] [Module L V] [AddCommGroup V'] [Module L' V']
    (σ : L →+* L') {n : ℕ} (B : Basis (Fin n) L V) (w : Fin n → V') : V →ₛₗ[σ] V' where
  toFun x := ∑ k, σ (B.repr x k) • w k
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [mul_smul, Finset.smul_sum]

theorem extOfBasis_basis {L L' V V' : Type} [Field L] [Field L'] [AddCommGroup V] [Module L V] [AddCommGroup V']
    [Module L' V'] (σ : L →+* L') {n : ℕ} (B : Basis (Fin n) L V) (w : Fin n → V') (k : Fin n) :
    extOfBasis σ B w (B k) = w k := by
  show ∑ j, σ (B.repr (B k) j) • w j = w k
  rw [B.repr_self, Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem carries_of_basis {L L' V V' : Type} [Field L] [Field L'] [AddCommGroup V] [Module L V] [AddCommGroup V']
    [Module L' V'] {σ : L →+* L'} (e : V →ₛₗ[σ] V') {n : ℕ} (B : Basis (Fin n) L V) (C : Basis (Fin n) L' V')
    (h : ∀ k, e (B k) = C k) {ι : Type} (b : Basis ι L V) : ∃ c : Basis ι L' V', ∀ i, c i = e (b i) := by
  classical
  have : Module.Finite L V := Module.Finite.of_basis B
  have : Module.Finite L' V' := Module.Finite.of_basis C
  have : Finite ι := Module.Finite.finite_basis b
  haveI : Fintype ι := Fintype.ofFinite ι
  have hspan : ⊤ ≤ Submodule.span L' (Set.range fun i => e (b i)) := by
    rw [← C.span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h k, ← b.sum_repr (B k), map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hcard : Fintype.card ι = finrank L' V' := by
    rw [finrank_eq_card_basis C, ← finrank_eq_card_basis B, finrank_eq_card_basis b]
  exact ⟨basisOfTopLeSpanOfCardEqFinrank _ hspan hcard, fun i => by simp⟩

theorem semilinearExtension : SemilinearExtension := by
  intro Ks LL WL _ _ _ _ _ _ _ WK hForm O K K'' _ _ _ _ _ _ _ _ _ _ emb hemb Fm _ _ _ _ eF
  obtain ⟨n, bv, -, hKs, hspanK, hLL, hspanL⟩ := hForm
  let B : Basis (Fin n) LL WL := Basis.mk hLL hspanL.ge
  have hB : ∀ k, B k = bv k := fun k => Basis.mk_apply _ _ _
  let BK : Basis (Fin n) Ks WK := (Basis.span hKs).map (LinearEquiv.ofEq _ _ hspanK)
  have hBK : ∀ k, (BK k : WL) = bv k := fun k => by simp [BK, Basis.span_apply]
  let bF : Basis (Fin n) K Fm := (Algebra.TensorProduct.basis K BK).map eF.symm
  obtain ⟨c, hc⟩ := exists_basis_tensor (O := O) (K'' := K'') bF
  have hck : ∀ k, c k = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k) := fun k => by
    rw [hc, Basis.map_apply, Algebra.TensorProduct.basis_apply]
  have hscal : ∀ (a : Ks) (m : Fm),
      emb (algebraMap Ks LL a) ⊗ₜ[O] m = (1 : K'') ⊗ₜ[O] (algebraMap Ks K a • m) := by
    intro a m
    rw [← RingHom.comp_apply emb (algebraMap Ks LL) a, hemb, RingHom.comp_apply, algebraMap_tmul]
  have hf : ∀ e : WL →ₛₗ[emb] K'' ⊗[O] Fm,
      (∀ k, e (bv k) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k)) →
      ∀ f : WK, e f = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] f) := by
    intro e he f
    have hterm : ∀ (r : Ks) (j : Fin n),
        e (r • bv j) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] (r • BK j)) := by
      intro r j
      rw [← algebraMap_smul LL r (bv j), map_smulₛₗ, he, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
        hscal, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    have hsum : (f : WL) = ∑ j, BK.repr f j • bv j := by
      conv_lhs => rw [← BK.sum_repr f]
      simp only [Submodule.coe_sum, Submodule.coe_smul, hBK]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum]
    simp_rw [hterm]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← TensorProduct.tmul_sum, ← map_sum eF.symm, ← TensorProduct.tmul_sum, BK.sum_repr]
  have hext : ∀ e : WL →ₛₗ[emb] K'' ⊗[O] Fm,
      (∀ k, e (bv k) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k)) → IsExt O emb eF e := by
    intro e he ι _ a f
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ, hf e he, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hval : ∀ e : WL →ₛₗ[emb] K'' ⊗[O] Fm, IsExt O emb eF e →
      ∀ k, e (bv k) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k) := by
    intro e he k
    rw [← hBK]
    exact he.apply_coe (BK k)
  let e₀ : WL →ₛₗ[emb] K'' ⊗[O] Fm :=
    extOfBasis emb B fun k => (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k)
  have he₀ : ∀ k, e₀ (bv k) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k) := fun k => by
    rw [← hB]
    exact extOfBasis_basis emb B _ k
  refine ⟨⟨e₀, hext e₀ he₀, fun e' he' => B.ext fun k => ?_⟩, fun e he => ?_, fun a m => ?_⟩
  · rw [hB, hval e' he' k, he₀ k]
  · exact fun ι b => carries_of_basis e B c (fun k => by rw [hB, hval e he k, hck k]) b
  · exact hscal a m

end GlobalTheory.SemilinearExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsHilbertSchmidtOrthonormalApply
section
open scoped InnerProductSpace

namespace GlobalTheory

theorem exists_isHilbertSchmidt_orthonormal_apply : ∀ (H K : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (J : Type) (u : J → H) (w : J → K), Orthonormal ℂ u → Summable (fun j => ‖w j‖ ^ 2) → ∃ G : H →L[ℂ] K, (∀ j, G (u j) = w j) ∧ (∀ v, (∀ j, inner ℂ (u j) v = 0) → G v = 0) ∧ GlobalTheory.OpTrace.IsHilbertSchmidt G := by
  intro H K _ _ _ _ _ _ J u w hu hw
  classical
  set S : ℝ := ∑' j, ‖w j‖ ^ 2
  have hbes : ∀ v : H, Summable fun j => ‖⟪u j, v⟫_ℂ‖ ^ 2 := fun v => hu.inner_products_summable v
  have hbes_le : ∀ v : H, ∑' j, ‖⟪u j, v⟫_ℂ‖ ^ 2 ≤ ‖v‖ ^ 2 := fun v => hu.tsum_inner_products_le v
  have hsn : ∀ v : H, Summable fun j => ‖⟪u j, v⟫_ℂ‖ * ‖w j‖ := fun v =>
    Summable.of_nonneg_of_le (fun j => by positivity)
      (fun j => by nlinarith [sq_nonneg (‖⟪u j, v⟫_ℂ‖ - ‖w j‖)]) (((hbes v).add hw).div_const 2)
  have hsn' : ∀ v : H, Summable fun j => ‖⟪u j, v⟫_ℂ • w j‖ := fun v =>
    (hsn v).congr fun j => (norm_smul _ _).symm
  have hs : ∀ v : H, Summable fun j => ⟪u j, v⟫_ℂ • w j := fun v => (hsn' v).of_norm
  let L : H →ₗ[ℂ] K :=
    { toFun := fun v => ∑' j, ⟪u j, v⟫_ℂ • w j
      map_add' := fun v v' => by
        simp only [inner_add_right, add_smul]
        exact (hs v).tsum_add (hs v')
      map_smul' := fun c v => by
        simp only [inner_smul_right, mul_smul, RingHom.id_apply]
        exact (hs v).tsum_const_smul c }
  have hbound : ∀ v, ‖L v‖ ≤ ((1 + S) / 2) * ‖v‖ := by
    intro v
    by_cases hv : v = 0
    · subst hv; simp
    set t := ‖v‖ with htdef
    have ht : 0 < t := norm_pos_iff.2 hv
    set A : ℝ := ∑' j, ‖⟪u j, v⟫_ℂ‖ ^ 2
    have key : ∀ a b : ℝ, a * b ≤ (a ^ 2 * t⁻¹ + t * b ^ 2) / 2 := by
      intro a b
      have h : a ^ 2 * t⁻¹ + t * b ^ 2 - 2 * (a * b) = t⁻¹ * (a - t * b) ^ 2 := by
        field_simp; ring
      have : 0 ≤ t⁻¹ * (a - t * b) ^ 2 := by positivity
      linarith
    have h1 : ‖L v‖ ≤ ∑' j, ‖⟪u j, v⟫_ℂ‖ * ‖w j‖ := by
      refine (norm_tsum_le_tsum_norm (hsn' v)).trans_eq ?_
      simp only [norm_smul]
    have hA : HasSum (fun j => (‖⟪u j, v⟫_ℂ‖ ^ 2 * t⁻¹ + t * ‖w j‖ ^ 2) / 2) ((A * t⁻¹ + t * S) / 2) :=
      (((hbes v).hasSum.mul_right t⁻¹).add (hw.hasSum.mul_left t)).div_const 2
    have h2 : ∑' j, ‖⟪u j, v⟫_ℂ‖ * ‖w j‖ ≤ (A * t⁻¹ + t * S) / 2 :=
      hasSum_le (fun j => key _ _) (hsn v).hasSum hA
    have h3 : A * t⁻¹ ≤ t := by
      have : A * t⁻¹ ≤ t ^ 2 * t⁻¹ := mul_le_mul_of_nonneg_right (hbes_le v) (inv_nonneg.2 ht.le)
      have e : t ^ 2 * t⁻¹ = t := by field_simp
      linarith
    have : (A * t⁻¹ + t * S) / 2 ≤ (1 + S) / 2 * t := by nlinarith
    linarith
  let G : H →L[ℂ] K := L.mkContinuous ((1 + S) / 2) hbound
  have hG : ∀ v, G v = ∑' j, ⟪u j, v⟫_ℂ • w j := fun v => rfl
  have hval : ∀ j, G (u j) = w j := by
    intro j
    rw [hG, tsum_eq_single j (fun k hk => by rw [orthonormal_iff_ite.1 hu k j, if_neg hk, zero_smul]),
      orthonormal_iff_ite.1 hu j j, if_pos rfl, one_smul]
  have hvan : ∀ v, (∀ j, inner ℂ (u j) v = 0) → G v = 0 := by
    intro v h
    rw [hG]
    simp [h]
  refine ⟨G, hval, hvan, ?_⟩
  obtain ⟨W, b, hsub, hb⟩ :=
    ((orthonormal_subtype_range hu.linearIndependent.injective).2 hu).exists_hilbertBasis_extension
  rw [GlobalTheory.OpTrace.isHilbertSchmidt_iff b]
  let e : J → W := fun j => ⟨u j, hsub ⟨j, rfl⟩⟩
  have hbe : ∀ j, b (e j) = u j := fun j => congrFun hb (e j)
  have he : Function.Injective e := fun j k hjk =>
    hu.linearIndependent.injective (congrArg Subtype.val hjk)
  refine (he.summable_iff fun i hi => ?_).1 (hw.congr fun j => ?_)
  · have : G (b i) = 0 := hvan _ fun j => by
      rw [← hbe j]
      exact b.orthonormal.2 fun h => hi ⟨j, h⟩
    simp [this]
  · simp only [Function.comp_apply, hbe, hval]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMemSBEqOneOnCompact
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx

theorem exists_mem_SB_eq_one_on_compact (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (C : Set (n → k)) (hC : IsCompact C) :
    ∃ χ ∈ SB (n → k), ∀ u ∈ C, χ u = 1 := by
  classical
  haveI : T2Space k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  have ho : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
  have hc : IsCompact (𝒪[k] : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall k 1
  let B : Set (n → k) := Set.univ.pi fun _ => (𝒪[k] : Set k)
  have hBo : IsOpen B := isOpen_set_pi Set.finite_univ fun _ _ => ho
  have hBc : IsCompact B := isCompact_univ_pi fun _ => hc
  let U : (n → k) → Set (n → k) := fun x => (Homeomorph.addLeft x) '' B
  have hUo : ∀ x, IsOpen (U x) := fun x => (Homeomorph.addLeft x).isOpenMap _ hBo
  have hUc : ∀ x, IsCompact (U x) := fun x => hBc.image (Homeomorph.addLeft x).continuous
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover U hUo fun x _ =>
    Set.mem_iUnion.mpr ⟨x, 0, fun _ _ => zero_mem _, by simp⟩
  set K : Set (n → k) := ⋃ x ∈ t, U x with hK
  have hKo : IsOpen K := isOpen_biUnion fun x _ => hUo x
  have hKc : IsCompact K := t.isCompact_biUnion fun x _ => hUc x
  have hcl : IsClopen K := ⟨hKc.isClosed, hKo⟩
  refine ⟨K.indicator fun _ => (1 : ℂ), ⟨?_, ?_⟩, fun u hu => Set.indicator_of_mem (ht hu) _⟩
  · refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
    by_cases hx : x ∈ K
    · filter_upwards [hKo.mem_nhds hx] with y hy
      simp [hx, hy]
    · filter_upwards [hcl.compl.isOpen.mem_nhds hx] with y hy
      simp [hx, Set.notMem_of_mem_compl hy]
  · exact HasCompactSupport.intro hKc fun x hx => Set.indicator_of_notMem hx _

end GlobalTheory.RootEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeakIntegralOfIsLocallyConstantOfIsCompact
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory


open MeasureTheory ValuativeRel Matrix in
theorem _root_.GlobalTheory.exists_weakIntegral_of_isLocallyConstant_of_isCompact :
    ∀ (U : Type) [TopologicalSpace U] [T2Space U] [MeasurableSpace U] [OpensMeasurableSpace U] (m : Measure U) [IsFiniteMeasureOnCompacts m] (V : Type) [AddCommGroup V] [Module ℂ V] (T : U → V) (_ : IsLocallyConstant T) (K : Set U) (_ : IsCompact K) (_ : ∀ u, u ∉ K → T u = 0), ∃ w : V, ∀ l : V →ₗ[ℂ] ℂ, l w = ∫ u, l (T u) ∂m := by
  intro U _ _ _ _ m _ V _ _ T hT K hK hzero
  classical
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun v : V => T ⁻¹' {v})
    (fun v => hT.isOpen_fiber v) (fun u _ => Set.mem_iUnion.2 ⟨T u, rfl⟩)
  have hS : ∀ u, T u ∈ insert 0 t := by
    intro u
    by_cases hu : u ∈ K
    · have h := ht hu
      simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff] at h
      obtain ⟨v, hv, huv⟩ := h
      rw [huv]
      exact Finset.mem_insert_of_mem hv
    · rw [hzero u hu]
      exact Finset.mem_insert_self 0 t
  have hmeas : ∀ v, MeasurableSet (T ⁻¹' {v}) := fun v => (hT.isOpen_fiber v).measurableSet
  refine ⟨∑ v ∈ insert 0 t, ((m.real (T ⁻¹' {v}) : ℂ)) • v, fun l => ?_⟩
  have hpt : ∀ u, l (T u) = ∑ v ∈ insert 0 t, (T ⁻¹' {v}).indicator (fun _ => l v) u := by
    intro u
    rw [Finset.sum_eq_single_of_mem (T u) (hS u)]
    · simp
    · intro v _ hv
      exact Set.indicator_of_notMem
        (show u ∉ T ⁻¹' {v} from fun h => hv (Set.mem_singleton_iff.1 h).symm) (fun _ => l v)
  have hint : ∀ v ∈ insert 0 t, Integrable ((T ⁻¹' {v}).indicator fun _ => l v) m := by
    intro v _
    by_cases hv : v = 0
    · subst hv
      simp
    · have hsub : T ⁻¹' {v} ⊆ K := by
        intro u hu
        by_contra hK'
        exact hv (by rw [← Set.mem_singleton_iff.1 hu, hzero u hK'])
      have hfin : m (T ⁻¹' {v}) ≠ ⊤ := ((measure_mono hsub).trans_lt hK.measure_lt_top).ne
      exact (integrable_indicator_iff (hmeas v)).2 (integrableOn_const (C := l v) hfin)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [integral_congr_ae (ae_of_all _ hpt), MeasureTheory.integral_finsetSum _ hint, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [integral_indicator_const _ (hmeas v), map_smul, smul_eq_mul, Complex.real_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierCoeffMulCharConvAndHasDerivAt
section
open MeasureTheory

namespace GlobalTheory

open MeasureTheory in
open scoped Pointwise in
private lemma exists_norm_le_of_continuous_periodic_compact_cover {G : Type} [AddCommGroup G] [TopologicalSpace G]
    (Γ : AddSubgroup G) {K : Set G} (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K)
    {Φ : G → ℂ} (hΦ : Continuous Φ) (hper : ∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) :
    ∃ M, ∀ x, ‖Φ x‖ ≤ M := by
  obtain ⟨M, hM⟩ := (hK.image hΦ.norm).bddAbove
  refine ⟨M, fun x => ?_⟩
  obtain ⟨γ, hγ, hx⟩ := hcov x
  rw [← hper γ hγ x]
  exact hM ⟨_, hx, rfl⟩


open MeasureTheory in
open scoped Pointwise in
theorem _root_.GlobalTheory.fourierCoeff_mul_char_conv_and_hasDerivAt :
    ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → ∀ χ : G → ℂ, Continuous χ → (∀ x y, χ (x + y) = χ x * χ y) → (∀ x, ‖χ x‖ = 1) → (∀ γ ∈ Γ, χ γ = 1) → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → (∀ z, (∫ y in 𝓕, Φ y * starRingEnd ℂ (χ y) ∂μ) * χ z = ∫ y in 𝓕, Φ (z + y) * starRingEnd ℂ (χ y) ∂μ) ∧ ∀ (L : ℝ →+ G) (Φ' : G → ℂ), Continuous Φ' → (∀ γ ∈ Γ, ∀ x, Φ' (γ + x) = Φ' x) → (∀ x, HasDerivAt (fun t : ℝ => Φ (x + L t)) (Φ' x) 0) → ∀ x, HasDerivAt (fun t : ℝ => (∫ y in 𝓕, Φ y * starRingEnd ℂ (χ y) ∂μ) * χ (x + L t)) ((∫ y in 𝓕, Φ' y * starRingEnd ℂ (χ y) ∂μ) * χ x) 0 := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov μ 𝓕 hμ h𝓕 χ hχ hmul hnorm hχΓ Φ hΦ hper
  haveI : Countable Γ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have hcc : ∀ x, starRingEnd ℂ (χ x) * χ x = 1 := by
    intro x
    rw [Complex.conj_mul', hnorm x]
    simp
  have conv : ∀ Ψ : G → ℂ, (∀ γ ∈ Γ, ∀ x, Ψ (γ + x) = Ψ x) → ∀ z,
      (∫ y in 𝓕, Ψ y * starRingEnd ℂ (χ y) ∂μ) * χ z = ∫ y in 𝓕, Ψ (z + y) * starRingEnd ℂ (χ y) ∂μ := by
    intro Ψ hΨ z
    set g : G → ℂ := fun y => Ψ y * starRingEnd ℂ (χ y) with hg
    have hgper : ∀ (γ : Γ) (y : G), g (γ +ᵥ y) = g y := by
      intro γ y
      simp only [hg, AddSubgroup.vadd_def, vadd_eq_add, hmul, map_mul, hχΓ γ γ.2, map_one, one_mul,
        hΨ γ γ.2]
    have hpt : ∀ y, Ψ (z + y) * starRingEnd ℂ (χ y) = g (z + y) * χ z := by
      intro y
      simp only [hg, hmul, map_mul]
      linear_combination -(Ψ (z + y) * starRingEnd ℂ (χ y)) * hcc z
    have hS : IsAddFundamentalDomain Γ ((fun y => -z + y) ⁻¹' 𝓕) μ := by
      have hset : (fun y => -z + y) ⁻¹' 𝓕 = z +ᵥ 𝓕 := by
        ext y
        simp only [Set.mem_preimage, Set.mem_vadd_set, vadd_eq_add]
        constructor
        · intro h
          exact ⟨_, h, add_neg_cancel_left z y⟩
        · rintro ⟨w, hw, rfl⟩
          simpa using hw
      rw [hset]
      exact h𝓕.vadd_of_comm z
    have hpre : (fun y => z + y) ⁻¹' ((fun y => -z + y) ⁻¹' 𝓕) = 𝓕 := by
      ext y; simp
    calc (∫ y in 𝓕, g y ∂μ) * χ z
        = (∫ y in (fun y => -z + y) ⁻¹' 𝓕, g y ∂μ) * χ z := by rw [h𝓕.setIntegral_eq hS hgper]
      _ = (∫ y in 𝓕, g (z + y) ∂μ) * χ z := by
          rw [← (measurePreserving_add_left μ z).setIntegral_preimage_emb
            (measurableEmbedding_addLeft z), hpre]
      _ = ∫ y in 𝓕, g (z + y) * χ z ∂μ := (integral_mul_const _ _).symm
      _ = ∫ y in 𝓕, Ψ (z + y) * starRingEnd ℂ (χ y) ∂μ := by simp_rw [hpt]
  refine ⟨conv Φ hper, ?_⟩
  intro L Φ' hΦ' hper' hderiv x
  obtain ⟨M, hM⟩ := exists_norm_le_of_continuous_periodic_compact_cover Γ hK hcov hΦ hper
  obtain ⟨M', hM'⟩ := exists_norm_le_of_continuous_periodic_compact_cover Γ hK hcov hΦ' hper'
  have hfin : μ 𝓕 < ⊤ := _root_.GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact Γ hK hcov μ h𝓕
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.mpr hfin.ne
  have hfun : (fun t : ℝ => (∫ y in 𝓕, Φ y * starRingEnd ℂ (χ y) ∂μ) * χ (x + L t)) =
      fun t : ℝ => ∫ y in 𝓕, Φ (x + L t + y) * starRingEnd ℂ (χ y) ∂μ := by
    funext t; exact conv Φ hper (x + L t)
  rw [hfun, conv Φ' hper' x]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (𝕜 := ℝ)
    (F := fun (t : ℝ) y => Φ (x + L t + y) * starRingEnd ℂ (χ y))
    (F' := fun (t : ℝ) y => Φ' (x + L t + y) * starRingEnd ℂ (χ y)) (x₀ := 0) (s := Set.univ)
    (bound := fun _ => M') Filter.univ_mem
    (Filter.Eventually.of_forall fun t => by fun_prop)
    (Integrable.of_bound (by fun_prop) M (Filter.Eventually.of_forall fun y => by
      simp [hnorm, hM]))
    (by fun_prop)
    (Filter.Eventually.of_forall fun y t _ => by simp [hnorm, hM'])
    (integrable_const _)
    (Filter.Eventually.of_forall fun y t _ => by
      have h := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact hderiv (x + L t + y))
      have h' : HasDerivAt (fun s : ℝ => Φ (x + L s + y)) (Φ' (x + L t + y)) t := by
        have e : (fun s : ℝ => Φ (x + L s + y)) = fun s : ℝ => Φ (x + L t + y + L (s - t)) := by
          funext s
          congr 1
          rw [show L s = L t + L (s - t) by rw [← map_add (f := _)]; congr 1; ring]
          abel
        rw [e]
        exact h
      exact h'.mul_const _)
  simpa using key.2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarMapMulRightEqOfFiniteFundamentalDomainStatement
section
open MeasureTheory Function
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_map_mul_right_eq_of_finite_fundamentalDomain : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (Γ N : Subgroup H), Countable Γ → IsClosed (N : Set H) → ∀ (κ : Measure N) (𝓝 : Set N), κ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ → κ 𝓝 ≠ ⊤ → ∀ n₀ : N, κ.map (· * n₀) = κ := by
  first | exact @GlobalTheory.haar_map_mul_right_eq_of_fundamentalDomain | exact GlobalTheory.haar_map_mul_right_eq_of_fundamentalDomain | (intros; apply GlobalTheory.haar_map_mul_right_eq_of_fundamentalDomain <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumTupleProdOfSummableNormComplex
section
open scoped InnerProductSpace

namespace GlobalTheory

open Filter Topology

theorem hasSum_pi_prod_of_summable_norm : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (J : ι → Type) (f : ∀ i, J i → ℂ), (∀ i, Summable (fun j => ‖f i j‖)) → HasSum (fun j : ∀ i, J i => ∏ i, f i (j i)) (∏ i, ∑' j, f i j) := by
  intro ι _ _ J f hf
  classical
  have hnorm : Summable fun j : ∀ i, J i => ‖∏ i, f i (j i)‖ := by
    have := splitHeight_summable_pi_prod (α := J) (f := fun i x => ‖f i x‖)
      (fun i x => norm_nonneg (f i x)) hf
    refine this.congr fun j => ?_
    exact (norm_prod _ _).symm
  have hs : Summable fun j : ∀ i, J i => ∏ i, f i (j i) := hnorm.of_norm
  have hcof : Tendsto (fun S : ∀ i, Finset (J i) => Fintype.piFinset S) atTop atTop := by
    refine Filter.tendsto_atTop_atTop.2 fun t => ⟨fun i => t.image (· i), fun S hS => ?_⟩
    intro x hx
    exact Fintype.mem_piFinset.2 fun i => hS i (Finset.mem_image_of_mem _ hx)
  have h1 : Tendsto (fun S : ∀ i, Finset (J i) => ∑ x ∈ Fintype.piFinset S, ∏ i, f i (x i))
      atTop (𝓝 (∑' j : ∀ i, J i, ∏ i, f i (j i))) := hs.hasSum.comp hcof
  have hproj : ∀ i, Tendsto (fun S : ∀ i, Finset (J i) => S i) atTop atTop := by
    intro i
    refine Filter.tendsto_atTop_atTop.2 fun b =>
      ⟨Function.update (fun j => (∅ : Finset (J j))) i b, fun S hS => ?_⟩
    have := hS i
    simpa using this
  have h2 : Tendsto (fun S : ∀ i, Finset (J i) => ∏ i, ∑ x ∈ S i, f i x)
      atTop (𝓝 (∏ i, ∑' j, f i j)) :=
    tendsto_finsetProd _ fun i _ => ((hf i).of_norm.hasSum).comp (hproj i)
  have h3 : (fun S : ∀ i, Finset (J i) => ∑ x ∈ Fintype.piFinset S, ∏ i, f i (x i)) =
      fun S => ∏ i, ∑ x ∈ S i, f i x := by
    funext S; exact (Finset.prod_univ_sum S fun i x => f i x).symm
  rw [h3] at h1
  have := tendsto_nhds_unique h1 h2
  rw [← this]; exact hs.hasSum

end GlobalTheory
end

