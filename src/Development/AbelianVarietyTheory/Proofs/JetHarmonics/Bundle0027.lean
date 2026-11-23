module

public import Mathlib
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialFirstColumn.FirstColumnSplitBijective
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0005
public import Formalism.HermitianCurvature.StatementM
public import Formalism.HermitianCurvature.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliLeftComatrix
section
open Formalism.REAL Finset

namespace GlobalTheory

theorem capelli_left_comatrix :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A), GlRel E →
      ∀ (u : ℂ) (j l : Fin (m + 1)),
        ∑ a : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ))) •
            (Tm E u a l * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1)) =
          if l = j then qdet E u else 0 := by
  intro A _ _ m E hE u j l
  set b : Fin (m + 1) → Fin (m + 1) := Fin.cons l (Fin.succAbove j) with hb
  have hexp := PI.QmColExpWork.expFirst E id b u
  have hbc : b ∘ Fin.succ = Fin.succAbove j := by
    funext k; simp [hb]
  have hb0 : b 0 = l := by simp [hb]
  rw [hbc, hb0] at hexp
  have hcast : ∀ (k : ℕ) (x : A), (((-1 : ℤ) ^ k : ℤ) : A) * x = ((-1 : ℂ) ^ k) • x := by
    intro k x
    rw [Algebra.smul_def]
    push_cast
    simp
  have hL : ∑ a : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ))) •
      (Tm E u a l * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1)) =
      ((-1 : ℂ) ^ (j : ℕ)) • qminor E id b u := by
    rw [hexp, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcast, smul_smul, ← pow_add, add_comm (j : ℕ) (a : ℕ)]
    rfl
  rw [hL]
  by_cases hlj : l = j
  · subst hlj
    have hbcyc : b = id ∘ PI.QmColExpWork.cyc0 m l := by
      funext k
      refine Fin.cases ?_ (fun k => ?_) k
      · simp [hb, PI.QmColExpWork.cycle_perm_zero]
      · simp [hb, PI.QmColExpWork.cycle_perm_succ]
    rw [if_pos rfl, hbcyc, qSkewCol A (m + 1) (m + 1) E hE id id _ u, PI.QmColExpWork.sign_cycle_perm,
      Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, hcast, smul_smul, ← mul_pow]
    simp [qdet]
  · rw [if_neg hlj]
    obtain ⟨k0, hk0⟩ := Fin.exists_succAbove_eq hlj
    have hfix : b ∘ Equiv.swap (0 : Fin (m + 1)) k0.succ = b := by
      funext k
      have h0 : b 0 = b k0.succ := by simp [hb, hk0]
      simp only [Function.comp, Equiv.swap_apply_def]
      split_ifs with h1 h2
      · rw [h1, h0]
      · rw [h2, h0]
      · rfl
    have hs := qSkewCol A (m + 1) (m + 1) E hE id b (Equiv.swap 0 k0.succ) u
    rw [hfix, Equiv.Perm.sign_swap (Fin.succ_ne_zero k0).symm] at hs
    have h2 : (2 : ℂ) • qminor E id b u = 0 := by
      rw [two_smul]
      nth_rewrite 1 [hs]
      simp
    have hz : qminor E id b u = 0 := by
      have h3 := congrArg (fun x => (2 : ℂ)⁻¹ • x) h2
      simpa [smul_smul] using h3
    rw [hz, smul_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirLeSubspaceMonotone
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem casK_mem_of_compact_stable {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ M) (S : Submodule ℂ M)
    (hS : ∀ a b, ε a = ε b → ∀ x ∈ S, E a b x ∈ S) : ∀ x ∈ S, CasK ε E x ∈ S := by
  intro x hx
  unfold CasK
  simp only [LinearMap.sum_apply]
  refine S.sum_mem fun a _ => S.sum_mem fun b _ => ?_
  split_ifs with h
  · exact hS _ _ h _ (hS _ _ h.symm _ hx)
  · simp

theorem quadForm_le_on_sup {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] (B : M →ₗ[ℂ] M)
    (hB : B.IsSymmetric) (C : ℝ) (S₁ S₂ : Submodule ℂ M) [FiniteDimensional ℂ S₁] [FiniteDimensional ℂ S₂]
    (h₁ : ∀ x ∈ S₁, B x ∈ S₁) (h₂ : ∀ x ∈ S₂, B x ∈ S₂)
    (b₁ : ∀ x ∈ S₁, (⟪x, B x⟫_ℂ).re ≤ C * ‖x‖ ^ 2) (b₂ : ∀ x ∈ S₂, (⟪x, B x⟫_ℂ).re ≤ C * ‖x‖ ^ 2) :
    ∀ x ∈ S₁ ⊔ S₂, (⟪x, B x⟫_ℂ).re ≤ C * ‖x‖ ^ 2 := by
  let e := WithLp.linearEquiv 2 ℂ (S₁ × S₂)
  let Φ : WithLp 2 (S₁ × S₂) →ₗ[ℂ] M := (S₁.subtype.coprod S₂.subtype) ∘ₗ e.toLinearMap
  let A : WithLp 2 (S₁ × S₂) →ₗ[ℂ] WithLp 2 (S₁ × S₂) :=
    e.symm.toLinearMap ∘ₗ ((B.restrict h₁).prodMap (B.restrict h₂)) ∘ₗ e.toLinearMap
  have hA1 : ∀ z, ((A z).fst : M) = B z.fst := fun z => rfl
  have hA2 : ∀ z, ((A z).snd : M) = B z.snd := fun z => rfl
  have hΦ : ∀ z, Φ z = (z.fst : M) + (z.snd : M) := fun z => rfl
  have key := _root_.GlobalTheory.re_inner_le_on_image_of_intertwining (WithLp 2 (S₁ × S₂)) M Φ A B C
    (by
      intro z w
      simp only [WithLp.prod_inner_apply, Submodule.coe_inner]
      change ⟪((A z).fst : M), (w.fst : M)⟫_ℂ + ⟪((A z).snd : M), (w.snd : M)⟫_ℂ =
        ⟪(z.fst : M), ((A w).fst : M)⟫_ℂ + ⟪(z.snd : M), ((A w).snd : M)⟫_ℂ
      rw [hA1, hA2, hA1, hA2, hB, hB])
    hB
    (by
      intro z
      rw [hΦ, hΦ, hA1, hA2, map_add (f := _)])
    (by
      intro z
      rw [WithLp.prod_norm_sq_eq_of_L2]
      simp only [WithLp.prod_inner_apply, Submodule.coe_inner]
      change (⟪(z.fst : M), ((A z).fst : M)⟫_ℂ + ⟪(z.snd : M), ((A z).snd : M)⟫_ℂ).re ≤
        C * (‖(z.fst : M)‖ ^ 2 + ‖(z.snd : M)‖ ^ 2)
      rw [hA1, hA2, Complex.add_re, mul_add]
      exact add_le_add (b₁ _ z.fst.2) (b₂ _ z.snd.2))
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  exact key (WithLp.toLp 2 (⟨y, hy⟩, ⟨z, hz⟩))

theorem casKLe_subspace_mono : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M), KUnit ε E → (∀ c, CasKLe ε E c 0) ∧ (∀ c x y, CasKLe ε E c x → CasKLe ε E c y → CasKLe ε E c (x + y)) ∧ (∀ c (a : ℂ) x, CasKLe ε E c x → CasKLe ε E c (a • x)) ∧ ∀ c c' x, 0 ≤ c → c ≤ c' → CasKLe ε E c x → CasKLe ε E c' x := by
  intro M _ _ n ε E hU
  refine ⟨fun c => ⟨⊥, inferInstance, ?_, Submodule.zero_mem _, ?_⟩, ?_, ?_, ?_⟩
  · intro a b _ x hx
    rw [Submodule.mem_bot] at hx
    simp [hx]
  · intro x hx
    rw [Submodule.mem_bot] at hx
    simp [hx]
  · rintro c x y ⟨S₁, f₁, s₁, hx, b₁⟩ ⟨S₂, f₂, s₂, hy, b₂⟩
    refine ⟨S₁ ⊔ S₂, inferInstance, ?_, Submodule.add_mem_sup hx hy, ?_⟩
    · intro a b hab w hw
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hw
      rw [map_add (f := _)]
      exact Submodule.add_mem_sup (s₁ a b hab u hu) (s₂ a b hab v hv)
    · exact quadForm_le_on_sup _ (_root_.GlobalTheory.casK_isSymmetric_and_form M n ε E hU).1 _ S₁ S₂
        (casK_mem_of_compact_stable ε E S₁ s₁) (casK_mem_of_compact_stable ε E S₂ s₂) b₁ b₂
  · rintro c a x ⟨S, f, s, hx, b⟩
    exact ⟨S, f, s, S.smul_mem a hx, b⟩
  · rintro c c' x hc hcc ⟨S, f, s, hx, b⟩
    refine ⟨S, f, s, hx, fun y hy => (b y hy).trans ?_⟩
    gcongr

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirLeTensorOperatorRaise
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.TensOp

def tensAct {V ι : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Fintype ι]
    (E : Module.End ℂ V) (A : Matrix ι ι ℂ) : Module.End ℂ (PiLp 2 (fun _ : ι => V)) where
  toFun x := WithLp.toLp 2 (fun i => E (x i) + ∑ j, A i j • x j)
  map_add' x y := by
    ext i
    simp [Finset.sum_add_distrib]
    abel
  map_smul' r x := by
    ext i
    simp [Finset.smul_sum, smul_smul, mul_comm]

theorem tensAct_apply {V ι : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Fintype ι]
    (E : Module.End ℂ V) (A : Matrix ι ι ℂ) (x : PiLp 2 (fun _ : ι => V)) (i : ι) :
    tensAct E A x i = E (x i) + ∑ j, A i j • x j := rfl

def sumMap {V N ι : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Fintype ι]
    [NormedAddCommGroup N] [InnerProductSpace ℂ N] (φ : ι → V →ₗ[ℂ] N) :
    PiLp 2 (fun _ : ι => V) →ₗ[ℂ] N where
  toFun x := ∑ j, φ j (x j)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.smul_sum]

theorem sumMap_apply {V N ι : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Fintype ι]
    [NormedAddCommGroup N] [InnerProductSpace ℂ N] (φ : ι → V →ₗ[ℂ] N) (x : PiLp 2 (fun _ : ι => V)) :
    sumMap φ x = ∑ j, φ j (x j) := rfl

theorem kunit_tensAct {V ι : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Fintype ι] {n : ℕ}
    (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (A : Fin n → Fin n → Matrix ι ι ℂ)
    (hE : KUnit ε E) (hA : ∀ a b, ε a = ε b → (A a b).conjTranspose = A b a) :
    KUnit ε (fun a b => tensAct (E a b) (A a b)) := by
  intro a b hab x y
  simp only [PiLp.inner_apply, tensAct_apply, inner_add_left, inner_add_right, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Finset.sum_add_distrib, hE a b hab]
  congr 1
  rw [Finset.sum_comm, ← hA a b hab]
  simp [Matrix.conjTranspose_apply]

theorem core (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ)
    (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (N ι : Type) [NormedAddCommGroup N]
    [InnerProductSpace ℂ N] [Fintype ι] [DecidableEq ι] (F : Fin n → Fin n → Module.End ℂ N)
    (φ : ι → V →ₗ[ℂ] N) (A : Fin n → Fin n → Matrix ι ι ℂ) (c s : ℝ) (hE : KUnit ε E) (hF : KUnit ε F)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hA : ∀ a b, ε a = ε b → (A a b).conjTranspose = A b a)
    (hAs : ∀ x : ι → V, ∑ a, ∑ b, (if ε a = ε b then ∑ i, ‖∑ j, A a b i j • x j‖ ^ 2 else 0)
      ≤ s ^ 2 * ∑ j, ‖x j‖ ^ 2)
    (hφ : ∀ a b, ε a = ε b → ∀ j w, F a b (φ j w) = φ j (E a b w) + ∑ i, A a b i j • φ i w)
    (hb : ∀ x : V, (∑ a, ∑ b, if ε a = ε b then ‖E a b x‖ ^ 2 else 0) ≤ c ^ 2 * ‖x‖ ^ 2)
    (w : V) (j : ι) : CasKLe ε F (c + s) (φ j w) := by
  set K : Fin n → Fin n → Module.End ℂ (PiLp 2 (fun _ : ι => V)) := fun a b => tensAct (E a b) (A a b) with hK
  have hKu : KUnit ε K := kunit_tensAct ε E A hE hA
  have hint : ∀ a b, ε a = ε b → ∀ x, F a b (sumMap φ x) = sumMap φ (K a b x) := by
    intro a b hab x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hK, sumMap_apply, tensAct_apply, map_sum, map_add (f := _), map_smul, hφ a b hab,
      Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
  have hcas : ∀ x, sumMap φ (CasK ε K x) = CasK ε F (sumMap φ x) := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [CasK, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs with hab
    · simp only [Module.End.mul_apply]
      rw [hint b a hab.symm, hint a b hab]
    · simp
  have hbound : ∀ x, (⟪x, CasK ε K x⟫_ℂ).re ≤ (c + s) ^ 2 * ‖x‖ ^ 2 := by
    intro x
    rw [(_root_.GlobalTheory.casK_isSymmetric_and_form _ n ε K hKu).2 x]
    have h := _root_.GlobalTheory.sum_norm_add_sq_le_of_bounds V (Fin n × Fin n × ι)
      (fun p => if ε p.1 = ε p.2.1 then E p.1 p.2.1 (x p.2.2) else 0)
      (fun p => if ε p.1 = ε p.2.1 then ∑ j, A p.1 p.2.1 p.2.2 j • x j else 0) c s (‖x‖ ^ 2) hc hs
      (by positivity) ?_ ?_
    · refine le_trans (le_of_eq ?_) h
      simp only [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      split_ifs with hab
      · rw [PiLp.norm_sq_eq_of_L2]; rfl
      · simp
    · rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
      refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun i _ => hb (x i))
      simp only [Fintype.sum_prod_type]
      rw [Finset.sum_comm (s := (univ : Finset ι))]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm (s := (univ : Finset ι))]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    · rw [PiLp.norm_sq_eq_of_L2]
      refine le_trans (le_of_eq ?_) (hAs (fun i => x i))
      simp only [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      split_ifs <;> simp
  refine ⟨LinearMap.range (sumMap φ), inferInstance, ?_, ?_, ?_⟩
  · rintro a b hab _ ⟨x, rfl⟩
    exact ⟨K a b x, (hint a b hab x).symm⟩
  · refine ⟨WithLp.toLp 2 (Pi.single j w), ?_⟩
    rw [sumMap_apply, Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      simp [Pi.single_eq_of_ne hi]
    · simp
  · rintro _ ⟨x, rfl⟩
    exact _root_.GlobalTheory.re_inner_le_on_image_of_intertwining _ N (sumMap φ) (CasK ε K) (CasK ε F) _ (_root_.GlobalTheory.casK_isSymmetric_and_form _ n ε K hKu).1
      (_root_.GlobalTheory.casK_isSymmetric_and_form _ n ε F hF).1 hcas hbound x

theorem casKLe_tensor_operator : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N ι : Type) [NormedAddCommGroup N] [InnerProductSpace ℂ N] [Fintype ι] [DecidableEq ι] (F : Fin n → Fin n → Module.End ℂ N) (φ : ι → M →ₗ[ℂ] N) (A : Fin n → Fin n → Matrix ι ι ℂ) (c s : ℝ), KUnit ε E → KUnit ε F → 0 ≤ c → 0 ≤ s → (∀ a b, ε a = ε b → (A a b).conjTranspose = A b a) → (∀ x : ι → M, ∑ a, ∑ b, (if ε a = ε b then ∑ i, ‖∑ j, A a b i j • x j‖ ^ 2 else 0) ≤ s ^ 2 * ∑ j, ‖x j‖ ^ 2) → (∀ a b, ε a = ε b → ∀ j w, F a b (φ j w) = φ j (E a b w) + ∑ i, A a b i j • φ i w) → ∀ w, CasKLe ε E c w → ∀ j, CasKLe ε F (c + s) (φ j w) := by
  intro M _ _ n ε E N ι _ _ _ _ F φ A c s hE hF hc hs hA hAs hφ w hw j
  obtain ⟨S, hfd, hst, hwS, hb⟩ := hw
  let E' : Fin n → Fin n → Module.End ℂ S := fun a b =>
    if h : ε a = ε b then (E a b).restrict (hst a b h) else 0
  have hE' : ∀ a b, ε a = ε b → ∀ x : S, (E' a b x : M) = E a b x := by
    intro a b h x
    simp [E', h]
  have := core S n ε E' N ι F (fun i => (φ i).comp S.subtype) A c s ?_ hF hc hs hA ?_ ?_ ?_ ⟨w, hwS⟩ j
  · exact this
  · intro a b h x y
    rw [Submodule.coe_inner, Submodule.coe_inner, hE' a b h, hE' b a h.symm, hE a b h]
  · intro x
    have h := hAs (fun i => (x i : M))
    simpa only [Submodule.coe_norm, Submodule.coe_sum, Submodule.coe_smul] using h
  · intro a b h i x
    simp [hE' a b h, hφ a b h]
  · intro x
    have h := hb x x.2
    rw [(_root_.GlobalTheory.casK_isSymmetric_and_form _ n ε E hE).2] at h
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs with hab
    · rw [← hE' a b hab]; rfl
    · rfl

end GlobalTheory.TensOp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsEigenSplitOfResolventIdentity
section
open Formalism.REAL Finset

namespace GlobalTheory

theorem exists_sum_eigen_split_of_resolvent : ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (n : ℕ) (Ω : Module.End ℂ N) (X : ℂ → Module.End ℂ N) (d : ℕ) (c : ℕ → Module.End ℂ N) (ν : Fin n → ℂ), Function.Injective ν → (∀ u, X u = ∑ i ∈ Finset.range d, u ^ i • c i) → (∀ (u : ℂ) (w : N), u • X u w + Ω (X u w) = (∏ s, (u + ν s)) • w) → ∀ w : N, ∃ v : Fin n → N, w = ∑ s, v s ∧ ∀ s (u : ℂ), X u (v s) = (∏ t ∈ Finset.univ.erase s, (u + ν t)) • v s := by
  intro N _ _ n Ω X d c ν hν hX hres w
  have key := _root_.GlobalTheory.aeval_neg_eq_zero_and_eigen_of_resolvent_identity N Ω X d c (∏ s, (Polynomial.X + Polynomial.C (ν s))) hX (by
    intro u w
    rw [hres u w, Polynomial.eval_prod]
    simp)
  obtain ⟨v, hv, hw⟩ := _root_.GlobalTheory.sum_eigenvectors_of_aeval_prod_linear_eq_zero N n Ω ν hν key.1 w
  refine ⟨v, hw, fun s u => ?_⟩
  have h := key.2 (ν s) (v s) (hv s)
    (∏ t ∈ Finset.univ.erase s, (Polynomial.X + Polynomial.C (ν t)))
    (Finset.mul_prod_erase Finset.univ (fun t => Polynomial.X + Polynomial.C (ν t))
      (Finset.mem_univ s)).symm u
  rw [h, Polynomial.eval_prod]
  simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGridFiveApartOnCut
section
open Formalism.FourierDecayAlt Finset

namespace GlobalTheory

theorem exists_grid_five_apart_on_cut :
    (∀ (u u' : ℕ → ℝ) (l M₀ : ℕ), 5 * (M₀ : ℝ) ≤ |u l - u' l| → ∃ Y : Finset ℝ, M₀ ≤ Y.card ∧
      (∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 5 ≤ |y - y'|) ∧
      ∀ y ∈ Y, I.OnCut u u' l y ∧ I.OnCut u u' l (y + 1)) ∧
    ∀ r : ℕ, 5 * (3 * (r + 1) * (2 * r + 1)) ≤ 30 * (r + 1) ^ 2 + 6 := by
  refine ⟨fun u u' l M₀ h => ?_, fun r => by nlinarith [Nat.zero_le r]⟩
  have hmax : min (u l) (u' l) + 5 * (M₀ : ℝ) ≤ max (u l) (u' l) := by
    have := max_sub_min_eq_abs (u l) (u' l)
    rw [abs_sub_comm] at h
    linarith
  refine ⟨(range M₀).image (fun i : ℕ => -(min (u l) (u' l) + 3 + 5 * (i : ℝ))), ?_, ?_, ?_⟩
  · rw [card_image_of_injective, card_range]
    intro i j hij
    have : (i : ℝ) = j := by
      simp only at hij
      linarith
    exact_mod_cast this
  · intro y hy y' hy' hne
    obtain ⟨i, -, rfl⟩ := mem_image.1 hy
    obtain ⟨j, -, rfl⟩ := mem_image.1 hy'
    have hij : i ≠ j := fun e => hne (by rw [e])
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hlt
      exact le_trans (by linarith) (le_abs_self _)
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast hlt
      exact le_trans (by linarith) (neg_le_abs _)
  · intro y hy
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hy
    have h1 : (i : ℝ) + 1 ≤ M₀ := by exact_mod_cast mem_range.1 hi
    have h0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    unfold I.OnCut
    rcases le_total (u l) (u' l) with hle | hle
    · rw [min_eq_left hle, max_eq_right hle] at hmax
      rw [min_eq_left hle]
      exact ⟨Or.inl ⟨by linarith, by linarith⟩, Or.inl ⟨by linarith, by linarith⟩⟩
    · rw [min_eq_right hle, max_eq_left hle] at hmax
      rw [min_eq_right hle]
      exact ⟨Or.inr ⟨by linarith, by linarith⟩, Or.inr ⟨by linarith, by linarith⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLinearEquivOfIrreducibleIsHW
section
open Formalism.REAL

namespace GlobalTheory

theorem stable_submodule_proj_bijective {U V₁ V₂ : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ U) (E₁ : Fin n → Fin n → Module.End ℂ V₁)
    (E₂ : Fin n → Fin n → Module.End ℂ V₂) (ν : Fin n → ℂ) (v : U)
    (p : U →ₗ[ℂ] V₁) (q : U →ₗ[ℂ] V₂)
    (hp : ∀ a b x, p (E a b x) = E₁ a b (p x)) (hq : ∀ a b x, q (E a b x) = E₂ a b (q x))
    (hpq : ∀ x, p x = 0 → q x = 0 → x = 0)
    (h₁ : ∀ S : Submodule ℂ V₁, (∀ a b, ∀ x ∈ S, E₁ a b x ∈ S) → S = ⊥ ∨ S = ⊤)
    (h₂ : ∀ S : Submodule ℂ V₂, (∀ a b, ∀ x ∈ S, E₂ a b x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hw : ∀ a, E₁ a a (p v) = ν a • p v) (hv₁ : p v ≠ 0) (hv₂ : q v ≠ 0)
    (S : Submodule ℂ U) (hS : ∀ a b, ∀ x ∈ S, E a b x ∈ S) (hvS : v ∈ S)
    (htop : ∀ x ∈ S, (∀ a, E a a x = ν a • x) → ∃ c : ℂ, x = c • v) :
    Function.Bijective (q.comp S.subtype) := by
  constructor
  · have hK := h₁ ((S ⊓ LinearMap.ker q).map p) (by
      rintro a b _ ⟨x, ⟨hxS, hxq⟩, rfl⟩
      refine ⟨E a b x, ⟨hS a b x hxS, ?_⟩, hp a b x⟩
      have hxq' : q x = 0 := hxq
      show q (E a b x) = 0
      rw [hq, hxq', map_zero])
    rcases hK with hK | hK
    · rw [injective_iff_map_eq_zero]
      intro x hx
      have hx' : q x = 0 := hx
      have hm : p x ∈ (S ⊓ LinearMap.ker q).map p := ⟨x, ⟨x.2, hx'⟩, rfl⟩
      rw [hK, Submodule.mem_bot] at hm
      exact Subtype.ext (hpq _ hm hx')
    · exfalso
      have hm : p v ∈ (S ⊓ LinearMap.ker q).map p := by rw [hK]; trivial
      obtain ⟨x, ⟨hxS, hxq⟩, hxp⟩ := hm
      have hxq' : q x = 0 := hxq
      obtain ⟨c, hc⟩ := htop x hxS (fun a => by
        rw [← sub_eq_zero]
        apply hpq
        · rw [map_sub, hp, map_smul, hxp, hw, sub_self]
        · rw [map_sub, hq, map_smul, hxq', map_zero, smul_zero, sub_self])
      rw [hc, map_smul, smul_eq_zero] at hxq'
      rcases hxq' with h0 | h0
      · apply hv₁
        rw [← hxp, hc, h0, zero_smul, map_zero]
      · exact hv₂ h0
  · have hK := h₂ (S.map q) (by
      rintro a b _ ⟨x, hxS, rfl⟩
      exact ⟨E a b x, hS a b x hxS, hq a b x⟩)
    rcases hK with hK | hK
    · exfalso
      have hm : q v ∈ S.map q := ⟨v, hvS, rfl⟩
      rw [hK, Submodule.mem_bot] at hm
      exact hv₂ hm
    · intro y
      have hm : y ∈ S.map q := by rw [hK]; trivial
      obtain ⟨x, hxS, rfl⟩ := hm
      exact ⟨⟨x, hxS⟩, rfl⟩

theorem exists_linearEquiv_of_irreducible_isHW :
    ∀ (V₁ : Type) [AddCommGroup V₁] [Module ℂ V₁] (V₂ : Type) [AddCommGroup V₂] [Module ℂ V₂] (n : ℕ) (E₁ : Fin n → Fin n → Module.End ℂ V₁) (E₂ : Fin n → Fin n → Module.End ℂ V₂) (ν : Fin n → ℂ) (v₁ : V₁) (v₂ : V₂), GlRel E₁ → GlRel E₂ → (∀ S : Submodule ℂ V₁, (∀ a b, ∀ x ∈ S, E₁ a b x ∈ S) → S = ⊥ ∨ S = ⊤) → (∀ S : Submodule ℂ V₂, (∀ a b, ∀ x ∈ S, E₂ a b x ∈ S) → S = ⊥ ∨ S = ⊤) → IsHW E₁ ν v₁ → IsHW E₂ ν v₂ → v₁ ≠ 0 → v₂ ≠ 0 → ∃ T : V₁ ≃ₗ[ℂ] V₂, ∀ a b x, T (E₁ a b x) = E₂ a b (T x) := by
  intro V₁ _ _ V₂ _ _ n E₁ E₂ ν v₁ v₂ hE₁ hE₂ h₁ h₂ hw₁ hw₂ hv₁ hv₂
  let E : Fin n → Fin n → Module.End ℂ (V₁ × V₂) := fun a b => (E₁ a b).prodMap (E₂ a b)
  have hEap : ∀ a b (x : V₁ × V₂), E a b x = (E₁ a b x.1, E₂ a b x.2) := fun _ _ _ => rfl
  have hE : GlRel E := by
    intro a b c d
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hEap]
    rw [glRel_apply_comm hE₁ a b c d, glRel_apply_comm hE₂ a b c d]
    split_ifs <;> simp [hEap]
    all_goals (constructor <;> abel)
  have hw : IsHW E ν (v₁, v₂) := by
    refine ⟨fun a => ?_, fun a b h => ?_⟩
    · rw [hEap, hw₁.1, hw₂.1]; rfl
    · rw [hEap, hw₁.2 a b h, hw₂.2 a b h]; rfl
  obtain ⟨S, hS, hvS, htop⟩ := exists_stable_submodule_topWeight_line _ n E ν _ hE hw
  have b₂ := stable_submodule_proj_bijective E E₁ E₂ ν (v₁, v₂) (LinearMap.fst ℂ V₁ V₂)
    (LinearMap.snd ℂ V₁ V₂) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun x h h' => Prod.ext h h') h₁ h₂ hw₁.1 hv₁ hv₂ S hS hvS htop
  have b₁ := stable_submodule_proj_bijective E E₂ E₁ ν (v₁, v₂) (LinearMap.snd ℂ V₁ V₂)
    (LinearMap.fst ℂ V₁ V₂) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun x h h' => Prod.ext h' h) h₂ h₁ hw₂.1 hv₂ hv₁ S hS hvS htop
  refine ⟨(LinearEquiv.ofBijective _ b₁).symm.trans (LinearEquiv.ofBijective _ b₂), ?_⟩
  intro a b x
  obtain ⟨y, rfl⟩ := (LinearEquiv.ofBijective _ b₁).surjective x
  have h : E₁ a b (LinearEquiv.ofBijective _ b₁ y)
      = LinearEquiv.ofBijective _ b₁ ⟨E a b y, hS a b y y.2⟩ := rfl
  rw [h]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorCommOfCommColumnsStatement
section
open Formalism.REAL Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qminor_commute_of_commute_columns : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (x : A) (a b : Fin t → Fin n) (u : ℂ), (∀ (c : Fin n) (i : Fin t), E c (b i) * x = x * E c (b i)) → qminor E a b u * x = x * qminor E a b u := by
  first | exact @GlobalTheory.qminor_comm_of_comm_columns | exact GlobalTheory.qminor_comm_of_comm_columns | (intros; apply GlobalTheory.qminor_comm_of_comm_columns <;> assumption)
end

