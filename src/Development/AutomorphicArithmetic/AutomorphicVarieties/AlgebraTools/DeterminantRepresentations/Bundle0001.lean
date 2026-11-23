module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.FlagKill
section
open Polynomial Matrix

private theorem UpperTheory.V.AlgebraTools.Det.flag_product_maps_into {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]
    (W : ℕ → Submodule R V) :
    ∀ (n : ℕ) (f : Fin n → Module.End R V),
    (∀ j : Fin n, ∀ v ∈ W (j + 1), f j v ∈ W j) → ∀ v ∈ W n, (List.ofFn f).prod v ∈ W 0 := by
  intro n
  induction n generalizing W with
  | zero =>
    intro f _ v hv
    simpa using hv
  | succ n ih =>
    intro f hf v hv
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
    have h0 := hf 0
    simp only [Fin.val_zero, zero_add] at h0
    apply h0
    have ht := ih (fun k => W (k + 1)) (fun i => f i.succ) (fun j w hw => by
      have hj := hf j.succ w (by simpa [Fin.val_succ] using hw)
      simpa [Fin.val_succ] using hj) v hv
    simpa using ht

theorem UpperTheory.V.AlgebraTools.Det.flagKill :
    ∀ {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (n : ℕ) (W : ℕ → Submodule R V) (f : Fin n → Module.End R V),
    W 0 = ⊥ → W n = ⊤ → (∀ j : Fin n, ∀ v ∈ W (j + 1), f j v ∈ W j) → (List.ofFn f).prod = 0 := by
  intro R V _ _ _ n W f h0 hn hf
  ext v
  have h := UpperTheory.V.AlgebraTools.Det.flag_product_maps_into W n f hf v (by rw [hn]; exact Submodule.mem_top)
  rw [h0, Submodule.mem_bot] at h
  simpa using h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.GramIff
section
open Polynomial Matrix

private theorem linearIndependent_iff_det_trace_gram_ne_zero {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι]
    (v : ι × ι → Matrix ι ι K) :
    LinearIndependent K v ↔ (Matrix.of fun a b => (v a * v b).trace).det ≠ 0 := by
  have hrow : ∀ (c : ι × ι → K) a,
      (v a * ∑ b, c b • v b).trace = ((Matrix.of fun a b => (v a * v b).trace) *ᵥ c) a := by
    intro c a
    rw [Finset.mul_sum, Matrix.trace_sum]
    simp [Matrix.mulVec, dotProduct, Matrix.trace_smul, mul_comm]
  constructor
  · intro hv hdet
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have htop : Submodule.span K (Set.range v) = ⊤ :=
      hv.span_eq_top_of_card_eq_finrank' (by simp [Module.finrank_matrix, Fintype.card_prod])
    have hall : ∀ X ∈ Submodule.span K (Set.range v), (X * ∑ b, c b • v b).trace = 0 := by
      intro X hX
      induction hX using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        rw [hrow, hc]
        rfl
      | zero => simp
      | add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.trace_add, hx, hy, add_zero]
      | smul r x _ hx => rw [Matrix.smul_mul, Matrix.trace_smul, hx, smul_zero]
    have hY : ∑ b, c b • v b = 0 := by
      ext i j
      have h := hall (Matrix.single j i 1) (htop ▸ Submodule.mem_top)
      rw [Matrix.trace_single_mul, one_smul] at h
      simpa using h
    exact hc0 (funext (Fintype.linearIndependent_iff.1 hv c hY))
  · intro hdet
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hne
    push_neg at hne
    obtain ⟨i, hi⟩ := hne
    apply hdet
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨c, fun h => hi (congrFun h i), ?_⟩
    funext a
    rw [← hrow, hc, Matrix.mul_zero, Matrix.trace_zero]
    rfl

theorem UpperTheory.V.AlgebraTools.Det.gramIff :
    ∀ {K G ι : Type} [Field K] [Monoid G] [Fintype ι] [DecidableEq ι] (ρ : G →* Matrix ι ι K),
    Submodule.span K (Set.range ρ) = ⊤ ↔ ∃ g : ι × ι → G, (Matrix.of fun a b => (ρ (g a * g b)).trace).det ≠ 0 := by
  intro K G ι _ _ _ _ ρ
  have hcard : Fintype.card (ι × ι) = Module.finrank K (Matrix ι ι K) := by
    simp [Module.finrank_matrix, Fintype.card_prod]
  constructor
  · intro hspan
    obtain ⟨s, hsr, hss, hli⟩ := exists_linearIndependent K (Set.range ρ)
    have hs_top : Submodule.span K s = ⊤ := hss.trans hspan
    let bs := Module.Basis.mk hli (by rw [Subtype.range_coe]; exact hs_top.ge)
    haveI : Fintype s := (hli.setFinite).fintype
    have hcs : Fintype.card (ι × ι) = Fintype.card s := hcard.trans (Module.finrank_eq_card_basis bs)
    let e : ι × ι ≃ s := Fintype.equivOfCardEq hcs
    have hmem : ∀ a, ∃ y, ρ y = (e a : Matrix ι ι K) := fun a => hsr (e a).2
    refine ⟨fun a => (hmem a).choose, ?_⟩
    have hv : (fun a => ρ (hmem a).choose) = fun a => ((e a : s) : Matrix ι ι K) :=
      funext fun a => (hmem a).choose_spec
    have hvli : LinearIndependent K (fun a => ρ (hmem a).choose) := by
      rw [hv]
      exact hli.comp e e.injective
    simpa only [map_mul] using (linearIndependent_iff_det_trace_gram_ne_zero _).1 hvli
  · rintro ⟨g, hg⟩
    have hvli : LinearIndependent K (fun a => ρ (g a)) :=
      (linearIndependent_iff_det_trace_gram_ne_zero (fun a => ρ (g a))).2 (by simpa only [map_mul] using hg)
    have htop := hvli.span_eq_top_of_card_eq_finrank' hcard
    rw [eq_top_iff, ← htop]
    exact Submodule.span_mono (Set.range_comp_subset_range g ρ)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.SignLemma
section
open Polynomial Matrix

theorem UpperTheory.V.AlgebraTools.Det.signLemma :
    ∀ {K G ι : Type} [Field K] [Group G] [Fintype ι] [DecidableEq ι] (ρ : G →* Matrix ι ι K) (σ : G →* G) (μ : G → K)
    (B : Matrix ι ι K), Submodule.span K (Set.range ρ) = ⊤ → (∀ s, σ (σ s) = s) → (∀ s, μ (σ s) = μ s) → IsUnit B →
    (∀ s, (ρ s)ᵀ * B * ρ (σ s) = μ s • B) → Bᵀ = B ∨ Bᵀ = -B := by
  intro K G ι _ _ _ _ ρ σ μ B hspan hσ hμ hB hlaw
  have hlaw' : ∀ s, (ρ s)ᵀ * Bᵀ * ρ (σ s) = μ s • Bᵀ := by
    intro s
    have h := congrArg Matrix.transpose (hlaw (σ s))
    rw [hσ, hμ, transpose_mul, transpose_mul, transpose_transpose, transpose_smul] at h
    rw [Matrix.mul_assoc]
    exact h
  obtain ⟨C, hC⟩ : ∃ C : Matrix ι ι K, Bᵀ = B * C := by
    obtain ⟨u, rfl⟩ := hB
    exact ⟨((u⁻¹ : (Matrix ι ι K)ˣ) : Matrix ι ι K) * (↑u : Matrix ι ι K)ᵀ, by rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]⟩
  have hcomm : ∀ t, C * ρ t = ρ t * C := by
    intro t
    have h1 := hlaw (σ t)
    have h2 := hlaw' (σ t)
    rw [hσ] at h1 h2
    have hA : IsUnit ((ρ (σ t))ᵀ * B) := by
      refine IsUnit.mul ?_ hB
      rw [Matrix.isUnit_transpose]
      exact (Group.isUnit (σ t)).map ρ
    apply hA.mul_left_cancel
    rw [← Matrix.mul_assoc _ (ρ t) C, h1, Matrix.smul_mul, ← hC, ← h2, hC]
    simp only [Matrix.mul_assoc]
  have hall : ∀ M : Matrix ι ι K, C * M = M * C := by
    intro M
    have hM : M ∈ Submodule.span K (Set.range ρ) := by rw [hspan]; trivial
    induction hM using Submodule.span_induction with
    | mem x hx => obtain ⟨t, rfl⟩ := hx; exact hcomm t
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul, hx, hy]
    | smul a x _ hx => rw [Matrix.mul_smul, Matrix.smul_mul, hx]
  obtain ⟨c, hc⟩ : C ∈ Set.range (Matrix.scalar ι) :=
    Matrix.mem_range_scalar_of_commute_single (fun i j _ => (hall _).symm)
  have hBc : Bᵀ = c • B := by
    rw [hC, ← hc]
    ext i j
    simp [Matrix.mul_diagonal, mul_comm]
  have h2 : B = (c * c) • B := by
    have h := congrArg Matrix.transpose hBc
    rw [transpose_transpose, transpose_smul, hBc, smul_smul] at h
    exact h
  by_cases hcc : c * c = 1
  · rcases mul_self_eq_one_iff.mp hcc with h | h
    · left; rw [hBc, h, one_smul]
    · right; rw [hBc, h, neg_one_smul]
  · have h0 : B = 0 := by
      have h3 : (1 - c * c) • B = 0 := by rw [sub_smul, one_smul, ← h2, sub_self]
      rcases smul_eq_zero.mp h3 with h | h
      · exact absurd (sub_eq_zero.mp h).symm hcc
      · exact h
    left; rw [h0, transpose_zero]
end

