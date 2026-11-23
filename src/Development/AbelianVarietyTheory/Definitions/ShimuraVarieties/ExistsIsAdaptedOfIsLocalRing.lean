module

public import Mathlib

@[expose] public section

open Module TensorProduct

namespace GlobalTheory

noncomputable section

section Dual

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

def basisOfDual (v : ι → M) (c : ι → Dual R M) (h₁ : ∀ i j, c i (v j) = if i = j then 1 else 0)
    (h₂ : ∀ x, ∑ i, c i x • v i = x) : Basis ι R M :=
  Basis.ofEquivFun <| LinearEquiv.ofLinear (LinearMap.pi c) (Fintype.linearCombination R v)
    (by
      refine LinearMap.ext fun a => funext fun i => ?_
      simp [Fintype.linearCombination_apply, h₁])
    (by
      refine LinearMap.ext fun x => ?_
      simp [Fintype.linearCombination_apply, h₂])

end Dual

section Action

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

def basisMulGL (b : Basis ι R M) (g : GL ι R) : Basis ι R M :=
  b.map (Matrix.toLinOfInv b b g.mul_inv g.inv_mul)

theorem basisMulGL_apply (b : Basis ι R M) (g : GL ι R) (j : ι) :
    basisMulGL b g j = ∑ i, (g : Matrix ι ι R) i j • b i := by
  simp [basisMulGL, Matrix.toLinOfInv, Matrix.toLin_self]

end Action

section Triangular

variable (ι R : Type*) [CommRing R] [Fintype ι] [LinearOrder ι]

variable {ι R}

variable {M : Type*} [AddCommGroup M] [Module R M] {n : ℕ}

theorem mem_basis_flag_iff (b : Basis (Fin n) R M) (k : Fin (n + 1)) (x : M) :
    x ∈ b.flag k ↔ ∀ i : Fin n, k ≤ i.castSucc → b.repr x i = 0 := by
  refine ⟨fun hx i hi => b.flag_le_ker_coord hi hx, fun h => ?_⟩
  rw [← b.sum_repr x]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : i.castSucc < k
  · exact Submodule.smul_mem _ _ (b.self_mem_flag hi)
  · simp [h i (not_lt.mp hi)]

end Triangular

section Flag

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

abbrev SubQuot (P Q : Submodule R M) : Type _ := Q ⧸ P.submoduleOf Q

def subQuotEquivOfSplitting {L : Type*} [AddCommGroup L] [Module R L] {P Q : Submodule R M}
    (π : M →ₗ[R] L) (σ : L →ₗ[R] M) (h₁ : ∀ l, π (σ l) = l) (h₂ : ∀ x ∈ P, π x = 0)
    (h₃ : ∀ l, σ l ∈ Q) (h₄ : ∀ x ∈ Q, x - σ (π x) ∈ P) : SubQuot P Q ≃ₗ[R] L :=
  (Submodule.quotEquivOfEq _ (LinearMap.ker (π ∘ₗ Q.subtype)) (by
    ext x
    refine ⟨fun hx => h₂ _ hx, fun hx => ?_⟩
    have hx' : π x = 0 := hx
    have := h₄ x x.2
    rwa [hx', map_zero, sub_zero] at this)).trans
    ((π ∘ₗ Q.subtype).quotKerEquivOfSurjective fun l => ⟨⟨σ l, h₃ l⟩, h₁ l⟩)


variable (R M) in
@[ext] structure FullFlag (n : ℕ) where

  sub : Fin (n + 1) → Submodule R M
  sub_zero : sub 0 = ⊥
  sub_last : sub (Fin.last n) = ⊤
  castSucc_le_succ : ∀ i : Fin n, sub i.castSucc ≤ sub i.succ
  invertible_step : ∀ i : Fin n, Module.Invertible R (SubQuot (sub i.castSucc) (sub i.succ))

namespace FullFlag

variable {n : ℕ}

abbrev Step (F : FullFlag (R := R) (M := M) n) (i : Fin n) : Type _ := SubQuot (F.sub i.castSucc) (F.sub i.succ)

instance (F : FullFlag (R := R) (M := M) n) (i : Fin n) : Module.Invertible R (F.Step i) := F.invertible_step i

theorem monotone (F : FullFlag (R := R) (M := M) n) : Monotone F.sub :=
  Fin.monotone_iff_le_succ.2 F.castSucc_le_succ

def basisStepEquiv (b : Basis (Fin n) R M) (i : Fin n) :
    SubQuot (b.flag i.castSucc) (b.flag i.succ) ≃ₗ[R] R :=
  subQuotEquivOfSplitting (b.coord i) (LinearMap.toSpanSingleton R M (b i)) (by simp)
    (fun _ hx => b.flag_le_ker_coord le_rfl hx)
    (fun l => Submodule.smul_mem _ _ (b.self_mem_flag Fin.castSucc_lt_succ))
    (fun x hx => by
      rw [mem_basis_flag_iff] at hx ⊢
      intro j hj
      rcases (Fin.castSucc_le_castSucc_iff.mp hj).eq_or_lt with rfl | h
      · simp
      · simp [hx j (Fin.succ_le_castSucc_iff.mpr h), Finsupp.single_apply, h.ne])

def ofBasis (b : Basis (Fin n) R M) : FullFlag (R := R) (M := M) n where
  sub := b.flag
  sub_zero := b.flag_zero
  sub_last := b.flag_last
  castSucc_le_succ _ := b.flag_mono Fin.castSucc_lt_succ.le
  invertible_step i := Module.Invertible.congr (basisStepEquiv b i).symm

def IsAdapted (F : FullFlag (R := R) (M := M) n) (b : Basis (Fin n) R M) : Prop := b.flag = F.sub

theorem isAdapted_iff {F : FullFlag (R := R) (M := M) n} {b : Basis (Fin n) R M} :
    F.IsAdapted b ↔ ofBasis b = F := ⟨fun h => FullFlag.ext h, fun h => h ▸ rfl⟩

theorem exists_retraction (F : FullFlag (R := R) (M := M) n) (k : Fin (n + 1)) :
    ∃ r : M →ₗ[R] M, (∀ x, r x ∈ F.sub k) ∧ ∀ x ∈ F.sub k, r x = x := by
  induction k using Fin.reverseInduction with
  | last => exact ⟨LinearMap.id, fun x => by simp [F.sub_last], fun _ _ => rfl⟩
  | cast i ih =>
    obtain ⟨r, hr₁, hr₂⟩ := ih
    obtain ⟨s, hs⟩ := Module.projective_lifting_property
      ((F.sub i.castSucc).submoduleOf (F.sub i.succ)).mkQ (LinearMap.id (R := R) (M := F.Step i))
      (Submodule.mkQ_surjective _)
    let r' : M →ₗ[R] F.sub i.succ := r.codRestrict _ hr₁
    refine ⟨r - (F.sub i.succ).subtype ∘ₗ s ∘ₗ Submodule.mkQ _ ∘ₗ r', fun x => ?_, fun x hx => ?_⟩
    · have : r' x - s (Submodule.mkQ _ (r' x)) ∈ (F.sub i.castSucc).submoduleOf (F.sub i.succ) := by
        rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub]
        exact sub_eq_zero.mpr (congr($hs _)).symm
      exact this
    · have hx' := F.castSucc_le_succ i hx
      have : Submodule.mkQ ((F.sub i.castSucc).submoduleOf (F.sub i.succ)) (r' x) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        change r x ∈ F.sub i.castSucc
        rwa [hr₂ x hx']
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, this, map_zero, hr₂ x hx']
      exact _root_.sub_zero x

theorem exists_splitting (F : FullFlag (R := R) (M := M) n) (i : Fin n) :
    ∃ (π : M →ₗ[R] F.Step i) (σ : F.Step i →ₗ[R] M), (∀ l, π (σ l) = l) ∧
      (∀ x ∈ F.sub i.castSucc, π x = 0) ∧ (∀ l, σ l ∈ F.sub i.succ) ∧
      (∀ x ∈ F.sub i.succ, x - σ (π x) ∈ F.sub i.castSucc) := by
  obtain ⟨r, hr₁, hr₂⟩ := F.exists_retraction i.succ
  obtain ⟨s, hs⟩ := Module.projective_lifting_property
    ((F.sub i.castSucc).submoduleOf (F.sub i.succ)).mkQ (LinearMap.id (R := R) (M := F.Step i))
    (Submodule.mkQ_surjective _)
  let r' : M →ₗ[R] F.sub i.succ := r.codRestrict _ hr₁
  have hr' : ∀ y : F.sub i.succ, r' y = y := fun y => Subtype.ext (hr₂ y y.2)
  refine ⟨Submodule.mkQ _ ∘ₗ r', (F.sub i.succ).subtype ∘ₗ s, fun l => ?_, fun x hx => ?_,
    fun l => (s l).2, fun x hx => ?_⟩
  · simp only [LinearMap.comp_apply, Submodule.subtype_apply, hr']
    exact congr($hs l)
  · rw [LinearMap.comp_apply, hr' ⟨x, F.castSucc_le_succ i hx⟩, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact hx
  · have : (⟨x, hx⟩ : F.sub i.succ) - s (Submodule.mkQ _ ⟨x, hx⟩) ∈
        (F.sub i.castSucc).submoduleOf (F.sub i.succ) := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub]
      exact sub_eq_zero.mpr (congr($hs _)).symm
    simp only [LinearMap.comp_apply, hr' ⟨x, hx⟩]
    exact this

theorem exists_isAdapted_of_free (F : FullFlag (R := R) (M := M) n) (h : ∀ i, Module.Free R (F.Step i)) :
    ∃ b : Basis (Fin n) R M, F.IsAdapted b := by
  choose π σ h₁ h₂ h₃ h₄ using F.exists_splitting
  have e : ∀ i, F.Step i ≃ₗ[R] R := fun i => (Module.Invertible.free_iff_linearEquiv.mp (h i)).some
  let v : Fin n → M := fun i => σ i ((e i).symm 1)
  have hv : ∀ (i) (l : F.Step i), σ i l = e i l • v i := fun i l => by
    simp only [v, ← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  have hspan : ∀ k, Submodule.span R (v '' {i | i.castSucc < k}) = F.sub k := by
    intro k
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact F.monotone (Fin.castSucc_lt_iff_succ_le.mp hi) (h₃ i _)
    · induction k using Fin.induction with
      | zero => rw [F.sub_zero]; exact bot_le
      | succ i ih =>
        intro x hx
        rw [← sub_add_cancel x (σ i (π i x))]
        refine add_mem (Submodule.span_mono (Set.image_mono ?_) (ih (h₄ i x hx))) ?_
        · exact fun j hj => lt_trans hj Fin.castSucc_lt_succ
        · rw [hv]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Fin.castSucc_lt_succ, rfl⟩)
  have hli : LinearIndependent R v := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    by_contra hne
    push Not at hne
    classical
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun i => a i ≠ 0) id
      (by obtain ⟨i, hi⟩ := hne; exact ⟨i, by simpa using hi⟩)
    have h0 : e i (π i (∑ j, a j • v j)) = a i := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum, Finset.sum_eq_single i _ (by simp)]
      · simp [v, h₁]
      · intro j _ hj
        by_cases haj : a j = 0
        · simp [haj]
        have hji : j < i := lt_of_le_of_ne (hmax j (by simpa using haj)) hj
        rw [map_smul, h₂ i (v j) (F.monotone (Fin.succ_le_castSucc_iff.mpr hji) (h₃ j _))]
        simp
    rw [ha] at h0
    simp only [map_zero] at h0
    exact (Finset.mem_filter.mp hi).2 h0.symm
  refine ⟨Basis.mk hli ?_, funext fun k => ?_⟩
  · have := hspan (Fin.last n)
    rw [F.sub_last] at this
    exact this.ge.trans (Submodule.span_mono (Set.image_subset_range _ _))
  · rw [Basis.flag, Basis.coe_mk]
    exact hspan k

theorem exists_isAdapted_of_isLocalRing [IsLocalRing R] (F : FullFlag (R := R) (M := M) n) :
    ∃ b : Basis (Fin n) R M, F.IsAdapted b :=
  F.exists_isAdapted_of_free fun _ => Module.free_of_flat_of_isLocalRing

end FullFlag

end Flag

end

end GlobalTheory
