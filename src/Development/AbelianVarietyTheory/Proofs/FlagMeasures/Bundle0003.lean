module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetUpdateRowLastSingle
section
namespace GlobalTheory

open Matrix

theorem det_updateRow_last_single {K : Type} [CommRing K] (r : ℕ)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    (Z.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).det
      = (Z.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [← Matrix.adjugate_apply, Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp [← two_mul, pow_mul]

theorem det_fromBlocks_corner {K : Type} [CommRing K] (r : ℕ)
    (Z W : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (a b : K) :
    (Matrix.fromBlocks Z (Matrix.diagonal fun i => if i = Fin.last r then a else 0)
      (Matrix.diagonal fun i => if i = Fin.last r then b else 0) W).det
      = Z.det * W.det - a * b * ((Z.submatrix Fin.castSucc Fin.castSucc).det
          * (W.submatrix Fin.castSucc Fin.castSucc).det) := by
  set l := Fin.last r with hl
  set D : K → Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
    fun c => Matrix.diagonal fun i => if i = l then c else 0 with hD
  have h1 : Matrix.fromBlocks Z (D a) (D b) W
      = (Matrix.fromBlocks Z 0 (D b) W).updateRow (Sum.inl l)
          (Matrix.fromBlocks Z 0 (D b) W (Sum.inl l) + a • Pi.single (Sum.inr l) 1) := by
    ext (i | i) (j | j) <;> by_cases hi : i = l <;> by_cases hj : j = l <;>
      simp [Matrix.updateRow_apply, hD, Matrix.diagonal_apply, Pi.single_apply, hi, hj, eq_comm] <;> grind
  have h2 : (Matrix.fromBlocks Z 0 (D b) W).updateRow (Sum.inl l) (Pi.single (Sum.inr l) 1)
      = (Matrix.fromBlocks (Z.updateRow l 0) (D 1) 0 W).updateRow (Sum.inr l)
          (Matrix.fromBlocks (Z.updateRow l 0) (D 1) 0 W (Sum.inr l)
            + b • Pi.single (Sum.inl l) 1) := by
    ext (i | i) (j | j) <;> by_cases hi : i = l <;> by_cases hj : j = l <;>
      simp [Matrix.updateRow_apply, hD, Matrix.diagonal_apply, Pi.single_apply, hi, hj, eq_comm] <;> grind
  have h3 : (Matrix.fromBlocks (Z.updateRow l 0) (D 1) 0 W).updateRow (Sum.inr l)
        (Pi.single (Sum.inl l) 1)
      = (Matrix.fromBlocks (Z.updateRow l (Pi.single l 1)) 0 0
          (W.updateRow l (Pi.single l 1))).submatrix (Equiv.swap (Sum.inl l) (Sum.inr l)) id := by
    ext (i | i) (j | j) <;> by_cases hi : i = l <;> by_cases hj : j = l <;>
      simp [Matrix.updateRow_apply, hD, Matrix.diagonal_apply, Pi.single_apply, hi, hj, eq_comm,
        Equiv.swap_apply_def] <;> grind
  have h0 : (Z.updateRow l 0).det = 0 :=
    Matrix.det_eq_zero_of_row_eq_zero l (by simp)
  change (Matrix.fromBlocks Z (D a) (D b) W).det = _
  rw [h1, Matrix.det_updateRow_add, Matrix.updateRow_eq_self, Matrix.det_updateRow_smul, h2,
    Matrix.det_updateRow_add, Matrix.updateRow_eq_self, Matrix.det_updateRow_smul, h3,
    Matrix.det_permute, Equiv.Perm.sign_swap (by simp), Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁, h0, hl,
    det_updateRow_last_single, det_updateRow_last_single]
  simp
  ring

theorem det_gram_two_frames {K : Type} [CommRing K] (r : ℕ)
    (Z W : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (T T' : K) :
    (Matrix.fromBlocks (Matrix.diagonal fun i => if i = Fin.last r then -T else 0) Z W
      (Matrix.diagonal fun i => if i = Fin.last r then -T' else 0)).det
      = (-1) ^ (r + 1) * (Z.det * W.det - T * T' * ((Z.submatrix Fin.castSucc Fin.castSucc).det
          * (W.submatrix Fin.castSucc Fin.castSucc).det)) := by
  have hs : (Matrix.fromBlocks 0 1 1 0 :
      Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) K).det = (-1) ^ (r + 1) := by
    have h : (Matrix.fromBlocks 0 1 1 0 :
        Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) K)
        = Matrix.fromBlocks 1 (-1) 0 1 * Matrix.fromBlocks 1 1 1 0 := by
      simp [Matrix.fromBlocks_multiply]
    rw [h, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_one₁₁]
    simp [Matrix.det_neg]
  have hm : Matrix.fromBlocks (Matrix.diagonal fun i => if i = Fin.last r then -T else 0) Z W
      (Matrix.diagonal fun i => if i = Fin.last r then -T' else 0)
      = Matrix.fromBlocks Z (Matrix.diagonal fun i => if i = Fin.last r then -T else 0)
        (Matrix.diagonal fun i => if i = Fin.last r then -T' else 0) W
        * Matrix.fromBlocks 0 1 1 0 := by
    simp [Matrix.fromBlocks_multiply]
  rw [hm, Matrix.det_mul, hs, det_fromBlocks_corner]
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DifferentSmulMemOfTraceIntegral
section
open NumberField
namespace GlobalTheory.TraceDualHom

theorem exists_linear_trace_eq (E : Type) [Field E] [NumberField E] (a : ℕ)
    (φ : (Fin a → E) →ₗ[ℚ] ℚ) :
    ∃ l : (Fin a → E) →ₗ[E] E, ∀ x, Algebra.trace ℚ E (l x) = φ x := by
  classical
  have h : ∀ i : Fin a, ∃ t : E, ∀ c : E, Algebra.trace ℚ E (t * c) = φ (Pi.single i c) := by
    intro i
    refine ⟨((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).symm
      (φ ∘ₗ LinearMap.single ℚ (fun _ => E) i), fun c => ?_⟩
    have := LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_nondegenerate ℚ E)
      (φ ∘ₗ LinearMap.single ℚ (fun _ => E) i) c
    exact this
  choose t ht using h
  refine ⟨∑ i, t i • LinearMap.proj i, fun x => ?_⟩
  conv_rhs => rw [← Finset.univ_sum_single x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [ht, map_sum]

theorem different_mul_mem (E : Type) [Field E] [NumberField E] (x : E)
    (hx : ∀ c : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (x * c) = m)
    (δ : 𝓞 E) (hδ : δ ∈ differentIdeal ℤ (𝓞 E)) : ∃ o : 𝓞 E, (o : E) = δ * x := by
  have h1 : (δ : E) ∈ IsLocalization.coeSubmodule E (differentIdeal ℤ (𝓞 E)) :=
    (IsLocalization.mem_coeSubmodule _ _).2 ⟨δ, hδ, rfl⟩
  rw [coeSubmodule_differentIdeal ℤ ℚ, Submodule.mem_div_iff_forall_mul_mem] at h1
  have h2 : x ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual]
    intro c hc
    obtain ⟨o, rfl⟩ := Submodule.mem_one.1 hc
    obtain ⟨m, hm⟩ := hx o
    exact ⟨m, by simpa using hm.symm⟩
  exact Submodule.mem_one.1 (h1 x h2)

theorem rat_span_eq_top (E : Type) [Field E] [NumberField E] (a : ℕ)
    (A : Submodule (𝓞 E) (Fin a → E)) (hA : Submodule.span E (A : Set (Fin a → E)) = ⊤) :
    Submodule.span ℚ (A : Set (Fin a → E)) = ⊤ := by
  have key : ∀ (e : E), ∀ x ∈ Submodule.span ℚ (A : Set (Fin a → E)),
      e • x ∈ Submodule.span ℚ (A : Set (Fin a → E)) := by
    intro e x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rw [← (integralBasis E).sum_repr e, Finset.sum_smul]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [smul_assoc]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      rw [integralBasis_apply, algebraMap_smul]
      exact A.smul_mem _ hx
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul q x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Submodule.span E (A : Set (Fin a → E)) := hA ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => simp
  | add x y _ _ hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
  | smul e x _ hx => exact key e x (hx trivial)

theorem mem_of_forall_rat_functional (E : Type) [Field E] [NumberField E] (a : ℕ)
    (A : Submodule (𝓞 E) (Fin a → E)) (hfg : A.FG)
    (hA : Submodule.span E (A : Set (Fin a → E)) = ⊤) (z : Fin a → E)
    (hz : ∀ φ : (Fin a → E) →ₗ[ℚ] ℚ, (∀ x ∈ A, ∃ m : ℤ, φ x = m) → ∃ m : ℤ, φ z = m) :
    z ∈ A := by
  haveI : Module.Finite (𝓞 E) A := Module.Finite.iff_fg.2 hfg
  haveI : Module.Finite ℤ A := Module.Finite.trans (𝓞 E) A
  haveI : Module.Free ℤ A := inferInstance
  let b := Module.Free.chooseBasis ℤ A
  let f : A →ₗ[ℤ] (Fin a → E) := A.subtype.restrictScalars ℤ
  have hli : LinearIndependent ℤ (f ∘ b) :=
    b.linearIndependent.map' f (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  have hliQ : LinearIndependent ℚ (f ∘ b) := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hli
  have hsp : ∀ x, x ∈ Submodule.span ℤ (Set.range (f ∘ b)) ↔ x ∈ A := by
    intro x
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top]
    constructor
    · rintro ⟨y, rfl⟩; exact y.2
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  have htop : ⊤ ≤ Submodule.span ℚ (Set.range (f ∘ b)) := by
    rw [← rat_span_eq_top E a A hA, Submodule.span_le]
    intro x hx
    exact Submodule.span_le_restrictScalars ℤ ℚ _ ((hsp x).2 hx)
  let B := Module.Basis.mk hliQ htop
  have hB : Set.range B = Set.range (f ∘ b) := by simp [B]
  rw [← hsp, ← hB, Module.Basis.mem_span_iff_repr_mem]
  intro i
  obtain ⟨m, hm⟩ := hz (B.coord i) (fun x hx => by
    rw [← hsp, ← hB, Module.Basis.mem_span_iff_repr_mem] at hx
    obtain ⟨m, hm⟩ := hx i
    exact ⟨m, by simpa using hm.symm⟩)
  exact ⟨m, by simpa using hm.symm⟩

theorem different_smul_mem_of_trace_integral : ∀ (E : Type) [Field E] [NumberField E] (a b : ℕ) (A : Submodule (𝓞 E) (Fin a → E)) (Bm : Submodule (𝓞 E) (Fin b → E)), A.FG → Bm.FG → Submodule.span E (A : Set (Fin a → E)) = ⊤ → Submodule.span E (Bm : Set (Fin b → E)) = ⊤ → ∀ ψ : (Fin b → E) →ₗ[E] (Fin a → E), (∀ T : (Fin a → E) →ₗ[E] (Fin b → E), (∀ x ∈ A, T x ∈ Bm) → ∃ m : ℤ, Algebra.trace ℚ E (LinearMap.trace E _ (T ∘ₗ ψ)) = m) → ∀ δ ∈ differentIdeal ℤ (𝓞 E), ∀ y ∈ Bm, δ • ψ y ∈ A := by
  intro E _ _ a b A Bm hA _ hAs _ ψ hψ δ hδ y hy
  refine mem_of_forall_rat_functional E a A hA hAs _ fun φ hφ => ?_
  obtain ⟨l, hl⟩ := exists_linear_trace_eq E a φ
  obtain ⟨m, hm⟩ := hψ (((δ : E) • l).smulRight y) (fun x hx => by
    obtain ⟨o, ho⟩ := different_mul_mem E (l x) (fun c => by
      obtain ⟨m, hm⟩ := hφ (c • x) (A.smul_mem c hx)
      refine ⟨m, ?_⟩
      rw [← hm, ← hl, ← algebraMap_smul E c x, map_smul, smul_eq_mul, mul_comm]) δ hδ
    rw [LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul, ← ho]
    exact Bm.smul_mem o hy)
  refine ⟨m, ?_⟩
  have e : (((δ : E) • l).smulRight y) ∘ₗ ψ = ((((δ : E) • l) ∘ₗ ψ).smulRight y) := rfl
  rw [e, LinearMap.trace_smulRight] at hm
  rw [← hm, ← hl, ← algebraMap_smul E δ (ψ y), map_smul]
  rfl

end GlobalTheory.TraceDualHom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSubgroupCountableAndExistsStrictFundamen
section
open MeasureTheory Set TopologicalSpace

namespace GlobalTheory

theorem discreteSubgroup_countable_and_exists_strict_fundamentalDomain : ∀ {G : Type} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ],
    Countable Γ ∧ ∃ D : Set G, MeasurableSet D ∧ ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ D := by
  intro G _ _ _ _ _ _ Γ _
  refine ⟨TopologicalSpace.separableSpace_iff_countable.1 inferInstance, ?_⟩

  obtain ⟨U, hUo, hU⟩ := isOpen_induced_iff.1 (isOpen_discrete ({1} : Set Γ))
  have hU1 : (1 : G) ∈ U := by
    have : (1 : Γ) ∈ Subtype.val ⁻¹' U := by rw [hU]; rfl
    simpa using this
  have hUΓ : ∀ x : G, x ∈ U → x ∈ Γ → x = 1 := by
    intro x hx hxΓ
    have : (⟨x, hxΓ⟩ : Γ) ∈ Subtype.val ⁻¹' U := hx
    rw [hU] at this
    simpa using congrArg Subtype.val (show (⟨x, hxΓ⟩ : Γ) = 1 from this)
  obtain ⟨V, hVo, hV1, hVU⟩ := exists_open_nhds_one_split (hUo.mem_nhds hU1)

  let P : Set G → Prop := fun W => ∀ x ∈ W, ∀ y ∈ W, x * y⁻¹ ∈ Γ → x = y
  let S : Set (Set G) := {W | W ∈ countableBasis G ∧ P W}
  have hcover : ∀ g : G, ∃ W ∈ S, g ∈ W := by
    intro g
    let N : Set G := (fun x => x * g⁻¹) ⁻¹' (V ∩ (fun x => x⁻¹) ⁻¹' V)
    have hNo : IsOpen N :=
      (hVo.inter (hVo.preimage continuous_inv)).preimage (continuous_mul_const g⁻¹)
    have hgN : g ∈ N := by simp [N, hV1]
    obtain ⟨W, hWb, hgW, hWN⟩ := (isBasis_countableBasis G).exists_subset_of_mem_open hgN hNo
    refine ⟨W, ⟨hWb, ?_⟩, hgW⟩
    intro x hx y hy hxy
    have hx' := hWN hx
    have hy' := hWN hy
    simp only [N, mem_preimage, mem_inter_iff] at hx' hy'
    have h1 : (x * g⁻¹) * (y * g⁻¹)⁻¹ ∈ U := hVU _ hx'.1 _ hy'.2
    have h2 : (x * g⁻¹) * (y * g⁻¹)⁻¹ = x * y⁻¹ := by group
    rw [h2] at h1
    have := hUΓ _ h1 hxy
    exact mul_inv_eq_one.1 this
  have hSc : S.Countable := (countable_countableBasis G).mono fun W hW => hW.1
  have hSne : S.Nonempty := by
    obtain ⟨W, hW, -⟩ := hcover 1
    exact ⟨W, hW⟩
  obtain ⟨f, hf⟩ := hSc.exists_eq_range hSne
  have hfS : ∀ n, f n ∈ S := fun n => hf ▸ mem_range_self n

  let Sat : ℕ → Set G := fun m => {x | ∃ γ : Γ, (γ : G) * x ∈ f m}
  have hSat : ∀ m, IsOpen (Sat m) := by
    intro m
    have : Sat m = ⋃ γ : Γ, (fun x => (γ : G) * x) ⁻¹' f m := by
      ext x; simp [Sat]
    rw [this]
    exact isOpen_iUnion fun γ => ((isBasis_countableBasis G).isOpen (hfS m).1).preimage
      (continuous_const_mul _)
  let D : Set G := ⋃ n, (f n ∩ ⋂ m ∈ Finset.range n, (Sat m)ᶜ)
  refine ⟨D, ?_, ?_⟩
  · refine MeasurableSet.iUnion fun n => ?_
    refine (((isBasis_countableBasis G).isOpen (hfS n).1).measurableSet).inter ?_
    exact Finset.measurableSet_biInter _ fun m _ => (hSat m).measurableSet.compl
  · intro g
    have hex : ∃ n, ∃ γ : Γ, (γ : G) * g ∈ f n := by
      obtain ⟨W, hW, hgW⟩ := hcover g
      rw [hf] at hW
      obtain ⟨n, rfl⟩ := hW
      exact ⟨n, 1, by simpa using hgW⟩
    classical
    obtain ⟨γ, hγ⟩ := Nat.find_spec hex
    have hmem : ∀ (δ : Γ) n, (δ : G) * g ∈ f n → (∀ m < n, (δ : G) * g ∉ Sat m) → (δ : G) * g ∈ D := by
      intro δ n h1 h2
      refine mem_iUnion.2 ⟨n, h1, ?_⟩
      simp only [mem_iInter, Finset.mem_range, mem_compl_iff]
      exact h2
    refine ⟨γ, hmem γ _ hγ fun m hm hS => ?_, ?_⟩
    · obtain ⟨δ, hδ⟩ := hS
      refine Nat.find_min hex hm ⟨δ * γ, ?_⟩
      simpa [mul_assoc] using hδ
    · intro δ hδ
      have hD : ∀ (ε : Γ), (ε : G) * g ∈ D → ∃ n, (ε : G) * g ∈ f n ∧ ∀ m < n, (ε : G) * g ∉ Sat m := by
        intro ε hε
        obtain ⟨n, h1, h2⟩ := mem_iUnion.1 hε
        refine ⟨n, h1, fun m hm => ?_⟩
        simp only [mem_iInter, Finset.mem_range, mem_compl_iff] at h2
        exact h2 m hm
      obtain ⟨n1, h11, h12⟩ := hD δ hδ
      obtain ⟨n2, h21, h22⟩ := hD γ (hmem γ _ hγ fun m hm hS => by
        obtain ⟨δ', hδ'⟩ := hS
        exact Nat.find_min hex hm ⟨δ' * γ, by simpa [mul_assoc] using hδ'⟩)
      have hn : n1 = n2 := by
        rcases lt_trichotomy n1 n2 with h | h | h
        · exact absurd ⟨δ * γ⁻¹, by simpa [mul_assoc] using h11⟩ (h22 n1 h)
        · exact h
        · exact absurd ⟨γ * δ⁻¹, by simpa [mul_assoc] using h21⟩ (h12 n2 h)
      subst hn
      have hP := (hfS n1).2 _ h11 _ h21 (by
        have : ((δ : G) * g) * ((γ : G) * g)⁻¹ = ((δ * γ⁻¹ : Γ) : G) := by simp [mul_assoc]
        rw [this]; exact (δ * γ⁻¹).2)
      exact Subtype.ext (mul_right_cancel hP)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConsecutiveRatioLeRpow
section
open Matrix Finset Real

namespace GlobalTheory

theorem exists_consecutive_ratio_le_rpow :
    ∀ (a q : ℕ) (τ : ℕ → ℝ), 1 ≤ a → a ≤ q → (∀ i ≤ a, 0 < τ i) → (∀ i < a, τ i < τ (i + 1)) →
      τ a = 1 / 2 → ∃ b < a, τ b / τ (b + 1) ≤ (2 * τ 0) ^ ((1 : ℝ) / q) ∧
        τ b ^ 2 ≤ (2 * τ 0) ^ ((1 : ℝ) / q) / 4 := by
  intro a q τ ha haq hpos hinc hta

  have hmono : ∀ j, j ≤ a → ∀ i, i ≤ j → τ i ≤ τ j := by
    intro j
    induction j with
    | zero => intro _ i hi; rw [Nat.le_zero.mp hi]
    | succ n ih =>
      intro hn i hi
      rcases Nat.lt_or_ge i (n + 1) with h | h
      · exact (ih (by omega) i (by omega)).trans (hinc n (by omega)).le
      · rw [le_antisymm hi h]
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  set x := 2 * τ 0 with hx
  have hx0 : 0 < x := by linarith [hpos 0 (Nat.zero_le _)]
  have hx1 : x ≤ 1 := by linarith [hmono a le_rfl 0 (Nat.zero_le _)]
  set r := x ^ ((1 : ℝ) / q) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hx0 _
  have hr1 : r ≤ 1 := Real.rpow_le_one hx0.le hx1 (by positivity)

  have hrq : r ^ q = x := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, one_div_mul_cancel hqpos.ne',
      Real.rpow_one]
  have hra : x ≤ r ^ a := by rw [← hrq]; exact pow_le_pow_of_le_one hr0.le hr1 haq

  obtain ⟨b, hb, hbr⟩ : ∃ b < a, τ b / τ (b + 1) ≤ r := by
    by_contra hne
    push_neg at hne
    have hstep : ∀ b < a, r * τ (b + 1) < τ b := fun b hb => by
      have h1 := hne b hb
      have h2 := hpos (b + 1) (by omega)
      rwa [lt_div_iff₀ h2] at h1
    have hind : ∀ i, i ≤ a → r ^ i * τ i ≤ τ 0 := by
      intro i
      induction i with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        calc r ^ (n + 1) * τ (n + 1) = r ^ n * (r * τ (n + 1)) := by ring
          _ ≤ r ^ n * τ n :=
            mul_le_mul_of_nonneg_left (hstep n (by omega)).le (pow_nonneg hr0.le _)
          _ ≤ τ 0 := ih (by omega)
    obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
    have hlast : r ^ (c + 1) * τ (c + 1) < τ 0 := by
      calc r ^ (c + 1) * τ (c + 1) = r ^ c * (r * τ (c + 1)) := by ring
        _ < r ^ c * τ c := mul_lt_mul_of_pos_left (hstep c (by omega)) (pow_pos hr0 _)
        _ ≤ τ 0 := hind c (by omega)
    rw [hta] at hlast
    linarith
  refine ⟨b, hb, hbr, ?_⟩
  have hb1 : 0 < τ (b + 1) := hpos (b + 1) (by omega)
  have hb0 : 0 < τ b := hpos b (by omega)
  have hle : τ b ≤ r * τ (b + 1) := by rwa [div_le_iff₀ hb1] at hbr
  have hhalf : τ (b + 1) ≤ 1 / 2 := by rw [← hta]; exact hmono a le_rfl (b + 1) (by omega)
  have htb : τ b ≤ r / 2 := by nlinarith [mul_le_mul_of_nonneg_left hhalf hr0.le]
  nlinarith [mul_le_mul htb htb hb0.le (by linarith), mul_le_mul_of_nonneg_left hr1 hr0.le]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHaarMapProdEq
section
open MeasureTheory Measure
open scoped NNReal ENNReal

namespace GlobalTheory.St.HaarSplit

theorem exists_haar_map_prod_eq {A B C : Type*} [Group A] [Group B] [Group C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup C]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [BorelSpace A] [BorelSpace B] [BorelSpace C]
    [LocallyCompactSpace A] [LocallyCompactSpace B] [LocallyCompactSpace C]
    [SecondCountableTopology A] [SecondCountableTopology B] [SecondCountableTopology C]
    (e : (A × B) ≃ₜ* C) (μA : Measure A) [μA.IsHaarMeasure] (μC : Measure C) [μC.IsHaarMeasure] :
    ∃ μB : Measure B, μB.IsHaarMeasure ∧ (μA.prod μB).map e = μC := by
  let ν : Measure B := Measure.haar
  have : ((μA.prod ν).map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map (μA.prod ν) e
  have h := isMulLeftInvariant_eq_smul μC ((μA.prod ν).map e)
  have hc : 0 < haarScalarFactor μC ((μA.prod ν).map e) := haarScalarFactor_pos_of_isHaarMeasure _ _
  refine ⟨haarScalarFactor μC ((μA.prod ν).map e) • ν, IsHaarMeasure.nnreal_smul _ hc.ne', ?_⟩
  conv_rhs => rw [h]
  generalize haarScalarFactor μC ((μA.prod ν).map e) = c
  have he : AEMeasurable (e : A × B → C) (μA.prod ν) :=
    e.continuous.measurable.aemeasurable
  rw [← Measure.map_smul c he]
  congr 1
  rw [ENNReal.smul_def, ENNReal.smul_def, Measure.prod_smul_right]

end GlobalTheory.St.HaarSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntSmulEqInteger
section
namespace GlobalTheory.IntSmulIntegerEq

theorem exists_int_smul_eq_integer {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ M : ℤ, M ≠ 0 ∧ ∃ a : NumberField.RingOfIntegers E,
      algebraMap (NumberField.RingOfIntegers E) E a = M • c := by
  have hQ : IsAlgebraic ℚ c := Algebra.IsAlgebraic.isAlgebraic c
  have hZ : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr hQ
  obtain ⟨M, hM, hint⟩ := hZ.exists_integral_multiple
  exact ⟨M, hM, ⟨M • c, hint⟩, rfl⟩

theorem exists_int_smul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsFullLattice E L)
    (w : Fin n → E) : ∃ (N : ℤ), N ≠ (0 : ℤ) ∧ N • w ∈ L := by
  have hw : w ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N₁, h₁, hx⟩ := hx
    obtain ⟨N₂, h₂, hy⟩ := hy
    refine ⟨N₁ * N₂, mul_ne_zero h₁ h₂, ?_⟩
    have e : (N₁ * N₂) • (x + y) = N₂ • (N₁ • x) + N₁ • (N₂ • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm N₂ N₁]
    rw [e]
    exact L.add_mem (zsmul_mem hx N₂) (zsmul_mem hy N₁)
  | smul c x _ hx =>
    obtain ⟨N, hN, hx⟩ := hx
    obtain ⟨M, hM, a, ha⟩ := exists_int_smul_eq_integer c
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    have e : (M * N) • (c • x) = a • (N • x) := by
      rw [← algebraMap_smul E a, ha, smul_assoc, mul_smul, smul_comm N c x]
    rw [e]
    exact L.smul_mem a hx

end GlobalTheory.IntSmulIntegerEq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntSmulIsIntegral
section
namespace GlobalTheory.IntSmulIsIntegral

theorem exists_int_smul_isIntegral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ (d • a) := by
  have h : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
  exact h.exists_integral_multiple

theorem exists_int_smul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (M : Submodule (NumberField.RingOfIntegers E) (Fin n → E))
    (hM : Submodule.span E (↑M : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ (c : ℤ), c ≠ (0 : ℤ) ∧ c • x ∈ M := by
  have hx : x ∈ Submodule.span E (↑M : Set (Fin n → E)) := hM ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨c, hc, hcy⟩ := hy
    obtain ⟨d, hd, hdz⟩ := hz
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    have e : (c * d) • (y + z) = d • (c • y) + c • (d • z) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm d c]
    rw [e]
    exact M.add_mem (zsmul_mem hcy d) (zsmul_mem hdz c)
  | smul a y _ hy =>
    obtain ⟨c, hc, hcy⟩ := hy
    obtain ⟨d, hd, hda⟩ := exists_int_smul_isIntegral a
    refine ⟨d * c, mul_ne_zero hd hc, ?_⟩
    have h := M.smul_mem (⟨d • a, hda⟩ : NumberField.RingOfIntegers E) hcy
    have e : (d * c) • (a • y) =
        (⟨d • a, hda⟩ : NumberField.RingOfIntegers E) • (c • y) := by
      change _ = (d • a) • (c • y)
      rw [smul_assoc, smul_comm a c y, smul_smul d c]
    rw [e]
    exact h

end GlobalTheory.IntSmulIsIntegral
end

