module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0003
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.AntisymmetrizedProductEqFactorialSmulQdet

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Topology Matrix MeasureTheory Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.CuspRep Formalism.L2.Host
open GlobalTheory.ContraPair (barK invTOp Paired)
open scoped ContDiff

namespace UpperTheory.V.TC

open InvT

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem infGL_invT (y : GL (Fin a) (Cinf E)) : infGL E a (invT a _ y) = invT a (Ad E) (infGL E a y) := cornerGL_invT _ y

theorem chart_invT (φ : GA E a → ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (fun y => φ (invT a (Ad E) y)) g x = chart φ (invT a (Ad E) g) (invTL x) := by
  obtain ⟨u, hu⟩ := id hx
  have e : x = toL u.val := hu.symm
  subst e
  rw [invTL_val, chart_val, chart_val, map_mul, infGL_invT]

theorem invT_mem_Sm {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) : (fun y => φ (invT a (Ad E) y)) ∈ Sm E a := fun g =>
  ((hφ (invT a (Ad E) g)).comp (fun _ hx => (contDiffAt_invTL hx).contDiffWithinAt) fun _ hx => isUnit_invTL hx).congr
    fun _ hx => chart_invT φ g hx


variable (E a) in
def dualFn : Sm E a ≃ₗ[ℂ] Sm E a where
  toFun φ := ⟨fun y => φ.1 (invT a (Ad E) y), invT_mem_Sm φ.2⟩
  invFun φ := ⟨fun y => φ.1 (invT a (Ad E) y), invT_mem_Sm φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv φ := Subtype.ext <| funext fun x => congrArg φ.1 (invT_invT x)
  right_inv φ := Subtype.ext <| funext fun x => congrArg φ.1 (invT_invT x)

@[simp] theorem dualFn_apply (φ : Sm E a) (g : GA E a) : (dualFn E a φ).1 g = φ.1 (invT a (Ad E) g) := rfl

theorem rt_dualFn (h : GA E a) (φ : Sm E a) : rt E a h (dualFn E a φ) = dualFn E a (rt E a (invT a (Ad E) h) φ) :=
  Subtype.ext <| funext fun g => congrArg φ.1 (map_mul (invT a (Ad E)) g h)

theorem lie_dualFn (X : Lie E a) (φ : Sm E a) :
    lie E a X (dualFn E a φ) = dualFn E a (lie E a (toL (-(Matrix.of X)ᵀ)) φ) := by
  refine Subtype.ext <| funext fun g => ?_
  have e : chart (dualFn E a φ).1 g =ᶠ[𝓝 (oneL E a)] chart φ.1 (invT a (Ad E) g) ∘ invTL :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => chart_invT φ.1 g hx
  have e1 : invTL (oneL E a) = oneL E a := invTL_one
  change fderiv ℝ _ _ X = fderiv ℝ _ _ _
  rw [e.fderiv_eq, fderiv_comp _ (by rw [e1]; exact differentiableAt_chart φ.2 _)
    ((contDiffAt_invTL (x := oneL E a) isUnit_one).differentiableAt (by simp)), e1, ContinuousLinearMap.comp_apply]
  exact congrArg _ (fderiv_invTL_one X)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem invTOp_invTOp (o : Op E a) : invTOp (invTOp o) = o := by
  cases o with
  | fin k => exact congrArg Op.fin (invT_invT k)
  | cpt k => exact congrArg Op.cpt (Subtype.ext (Matrix.ext fun i j => star_star (k.1 i j)))
  | lie X => exact congrArg Op.lie (funext fun i => funext fun j => neg_neg (X i j))


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem invT_toUnits (k : Kinf E a) : invT a (Cinf E) (Unitary.toUnits k) = Unitary.toUnits (barK k) := Units.ext rfl

theorem act_dualFn (o : Op E a) (φ : Sm E a) : act o (dualFn E a φ) = dualFn E a (act (invTOp o) φ) := by
  cases o with
  | fin k => exact (rt_dualFn (finGL E a k) φ).trans (by rw [← finGL_invT]; rfl)
  | cpt k => exact (rt_dualFn (infGL E a (Unitary.toUnits k)) φ).trans (by rw [← infGL_invT, invT_toUnits]; rfl)
  | lie X => exact lie_dualFn X φ

theorem Eop_dualFn (τ : E →+* ℂ) (i j : Fin a) (φ : Sm E a) :
    Eop τ i j (dualFn E a φ) = dualFn E a ((-Eop τ j i) φ) := by
  have h : ∀ x, lieS E a i j x (dualFn E a φ) = -dualFn E a (lieS E a j i x φ) := fun x => by
    rw [lieS_apply, lie_dualFn, lieS_apply, ← map_neg, ← LinearMap.neg_apply, ← map_neg]
    exact congrArg (fun m : Matrix (Fin a) (Fin a) (Cinf E) => dualFn E a (lie E a (toL (-m)) φ))
      (Matrix.transpose_single i j x)
  simp only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.neg_apply, h, map_neg, map_smul, map_sub]
  module

private theorem qdet_conj {V : Type} [AddCommGroup V] [Module ℂ V] (e : V ≃ₗ[ℂ] V) (X Y : Fin a → Fin a → Module.End ℂ V)
    (h : ∀ i j φ, X i j (e φ) = e (Y i j φ)) (u : ℂ) (φ : V) :
    Formalism.REAL.qdet X u (e φ) = e (Formalism.REAL.qdet Y u φ) := by
  have h0 : ∀ (z : Module.End ℂ V) ψ, (e.conjAlgEquiv ℂ).toAlgHom z (e ψ) = e (z ψ) := fun z ψ =>
    congrArg (fun x => e (z x)) (e.symm_apply_apply ψ)
  have e1 : (fun i j => (e.conjAlgEquiv ℂ).toAlgHom (Y i j)) = X := by
    funext i j
    refine LinearMap.ext fun ψ => ?_
    obtain ⟨ψ, rfl⟩ := e.surjective ψ
    rw [h0, h]
  rw [← h0, map_qdet, e1]

open Formalism.REAL Finset in
open Formalism.HermitianLatticeCounting.P (list_prod_ofFn_update_adjacent mul_signed_four_sum_mul_eq) in
private theorem qdet_dual {V : Type} [AddCommGroup V] [Module ℂ V] (e : V ≃ₗ[ℂ] V) (X : Fin a → Fin a → Module.End ℂ V)
    (hX : Formalism.REAL.GlRel X) (h : ∀ i j φ, X i j (e φ) = e ((-X j i) φ)) (u : ℂ) (φ : V) :
    Formalism.REAL.qdet X (u + ((a : ℂ) - 1) / 2) (e φ) =
      (-1 : ℂ) ^ a • e (Formalism.REAL.qdet X (-u + ((a : ℂ) - 1) / 2) φ) := by
  -- Antisymmetrize over both index permutations to exchange the rows and columns.
  let orderedTermProduct {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (arg : Fin n → ℂ)
      (σ τ : Equiv.Perm (Fin n)) : A :=
    (List.ofFn fun k : Fin n => Tm E (arg k) (σ k) (τ k)).prod
  let doublyAntisymmetrizedProduct {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (arg : Fin n → ℂ) : A :=
    ∑ τ : Equiv.Perm (Fin n), ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign τ : ℤ) : A) * (((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E arg σ τ)
  have term_two_by_two_exchange {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (x y : ℂ) (p q c d : Fin n) :
      Tm E x p c * Tm E y q d - Tm E x q c * Tm E y p d - Tm E x p d * Tm E y q c + Tm E x q d * Tm E y p c =
      Tm E y p c * Tm E x q d - Tm E y q c * Tm E x p d - Tm E y p d * Tm E x q c + Tm E y q d * Tm E x p c := by
    simp only [Tm, Algebra.algebraMap_eq_smul_one]
    split_ifs <;>
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, zero_add] <;>
      module
  have orderedProduct_adjacent_swap_identity {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → A) (i : Fin m)
      (arg : Fin (m + 1) → ℂ) (σ τ : Equiv.Perm (Fin (m + 1))) :
      orderedTermProduct E arg σ τ - orderedTermProduct E arg (σ * Equiv.swap i.castSucc i.succ) τ - orderedTermProduct E arg σ (τ * Equiv.swap i.castSucc i.succ)
          + orderedTermProduct E arg (σ * Equiv.swap i.castSucc i.succ) (τ * Equiv.swap i.castSucc i.succ) =
      orderedTermProduct E (arg ∘ Equiv.swap i.castSucc i.succ) σ τ
          - orderedTermProduct E (arg ∘ Equiv.swap i.castSucc i.succ) (σ * Equiv.swap i.castSucc i.succ) τ
          - orderedTermProduct E (arg ∘ Equiv.swap i.castSucc i.succ) σ (τ * Equiv.swap i.castSucc i.succ)
          + orderedTermProduct E (arg ∘ Equiv.swap i.castSucc i.succ) (σ * Equiv.swap i.castSucc i.succ)
              (τ * Equiv.swap i.castSucc i.succ) := by
    have hi : (i : ℕ) + 1 < m + 1 := by omega
    have hfix : ∀ k : Fin (m + 1), (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → Equiv.swap i.castSucc i.succ k = k := by
      intro k h1 h2
      refine Equiv.swap_apply_of_ne_of_ne (fun h => h1 ?_) (fun h => h2 ?_)
      · subst h
        simp
      · subst h
        simp

    have hM : ∀ (a : Fin (m + 1) → ℂ) (σ' τ' : Equiv.Perm (Fin (m + 1))),
        (∀ k : Fin (m + 1), (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → a k = arg k ∧ σ' k = σ k ∧ τ' k = τ k) →
        orderedTermProduct E a σ' τ' = ((List.ofFn fun k => Tm E (arg k) (σ k) (τ k)).take i).prod *
          (Tm E (a ⟨i, by omega⟩) (σ' ⟨i, by omega⟩) (τ' ⟨i, by omega⟩) *
            Tm E (a ⟨i + 1, hi⟩) (σ' ⟨i + 1, hi⟩) (τ' ⟨i + 1, hi⟩)) *
          ((List.ofFn fun k => Tm E (arg k) (σ k) (τ k)).drop (i + 2)).prod := by
      intro a σ' τ' hk
      unfold orderedTermProduct
      exact list_prod_ofFn_update_adjacent (fun k => Tm E (arg k) (σ k) (τ k)) (fun k => Tm E (a k) (σ' k) (τ' k)) i hi
        (fun k h1 h2 => by obtain ⟨e1, e2, e3⟩ := hk k h1 h2; rw [e1, e2, e3])
    have hc : ∀ k : Fin (m + 1), (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 →
        (arg ∘ Equiv.swap i.castSucc i.succ) k = arg k ∧ (σ * Equiv.swap i.castSucc i.succ) k = σ k ∧
          (τ * Equiv.swap i.castSucc i.succ) k = τ k := by
      intro k h1 h2
      simp [Equiv.Perm.mul_apply, hfix k h1 h2]
    rw [hM arg σ τ (fun k _ _ => ⟨rfl, rfl, rfl⟩),
      hM arg (σ * Equiv.swap i.castSucc i.succ) τ (fun k h1 h2 => ⟨rfl, (hc k h1 h2).2.1, rfl⟩),
      hM arg σ (τ * Equiv.swap i.castSucc i.succ) (fun k h1 h2 => ⟨rfl, rfl, (hc k h1 h2).2.2⟩),
      hM arg (σ * Equiv.swap i.castSucc i.succ) (τ * Equiv.swap i.castSucc i.succ)
        (fun k h1 h2 => ⟨rfl, (hc k h1 h2).2.1, (hc k h1 h2).2.2⟩),
      hM (arg ∘ Equiv.swap i.castSucc i.succ) σ τ (fun k h1 h2 => ⟨(hc k h1 h2).1, rfl, rfl⟩),
      hM (arg ∘ Equiv.swap i.castSucc i.succ) (σ * Equiv.swap i.castSucc i.succ) τ
        (fun k h1 h2 => ⟨(hc k h1 h2).1, (hc k h1 h2).2.1, rfl⟩),
      hM (arg ∘ Equiv.swap i.castSucc i.succ) σ (τ * Equiv.swap i.castSucc i.succ)
        (fun k h1 h2 => ⟨(hc k h1 h2).1, rfl, (hc k h1 h2).2.2⟩),
      hM (arg ∘ Equiv.swap i.castSucc i.succ) (σ * Equiv.swap i.castSucc i.succ)
        (τ * Equiv.swap i.castSucc i.succ) (fun k h1 h2 => hc k h1 h2)]
    have e0 : (⟨i, by omega⟩ : Fin (m + 1)) = i.castSucc := Fin.ext rfl
    have e1 : (⟨i + 1, hi⟩ : Fin (m + 1)) = i.succ := Fin.ext rfl
    simp only [e0, e1, Equiv.Perm.mul_apply, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right]
    rw [mul_signed_four_sum_mul_eq, mul_signed_four_sum_mul_eq, term_two_by_two_exchange]
  have antisymmetrizedProduct_adjacent_swap {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → A) (i : Fin m)
      (arg : Fin (m + 1) → ℂ) : doublyAntisymmetrizedProduct E (arg ∘ Equiv.swap i.castSucc i.succ) = doublyAntisymmetrizedProduct E arg := by
    have hne : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ (i := i)).ne
    have key := orderedProduct_adjacent_swap_identity E i arg
    generalize hs : Equiv.swap i.castSucc i.succ = s at key ⊢
    have hsg : Equiv.Perm.sign s = -1 := by rw [← hs]; exact Equiv.Perm.sign_swap hne

    have hre : ∀ F : Equiv.Perm (Fin (m + 1)) → A,
        ∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) * F (σ * s) = -∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) * F σ := by
      intro F
      rw [← Equiv.sum_comp (Equiv.mulRight s) (fun σ => ((Equiv.Perm.sign σ : ℤ) : A) * F σ)]
      simp [Equiv.Perm.sign_mul, hsg]
    have q1 : ∀ a : Fin (m + 1) → ℂ, ∑ τ, ∑ σ, ((Equiv.Perm.sign τ : ℤ) : A) *
        (((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a (σ * s) τ) = -doublyAntisymmetrizedProduct E a := by
      intro a
      simp only [doublyAntisymmetrizedProduct, ← Finset.mul_sum]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      have h := hre (fun σ => orderedTermProduct E a σ τ)
      rw [h, mul_neg]
    have q2 : ∀ a : Fin (m + 1) → ℂ, ∑ τ, ∑ σ, ((Equiv.Perm.sign τ : ℤ) : A) *
        (((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a σ (τ * s)) = -doublyAntisymmetrizedProduct E a := by
      intro a
      simp only [doublyAntisymmetrizedProduct, ← Finset.mul_sum]
      have h := hre (fun τ => ∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a σ τ)
      exact h
    have q3 : ∀ a : Fin (m + 1) → ℂ, ∑ τ, ∑ σ, ((Equiv.Perm.sign τ : ℤ) : A) *
        (((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a (σ * s) (τ * s)) = doublyAntisymmetrizedProduct E a := by
      intro a
      simp only [← Finset.mul_sum]
      have h1 : ∀ τ, ∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a (σ * s) (τ * s) =
          -∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a σ (τ * s) := by
        intro τ
        have h := hre (fun σ => orderedTermProduct E a σ (τ * s))
        exact h
      simp only [h1, mul_neg, Finset.sum_neg_distrib]
      have h := hre (fun τ => ∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a σ τ)
      rw [h, neg_neg]
      simp only [doublyAntisymmetrizedProduct, Finset.mul_sum]
    have T_eq : ∀ a : Fin (m + 1) → ℂ, ∑ τ, ∑ σ, ((Equiv.Perm.sign τ : ℤ) : A) *
        (((Equiv.Perm.sign σ : ℤ) : A) * (orderedTermProduct E a σ τ - orderedTermProduct E a (σ * s) τ - orderedTermProduct E a σ (τ * s) +
          orderedTermProduct E a (σ * s) (τ * s))) = 4 • doublyAntisymmetrizedProduct E a := by
      intro a
      simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [q1 a, q2 a, q3 a]
      simp only [doublyAntisymmetrizedProduct]
      abel
    have h4 : 4 • doublyAntisymmetrizedProduct E arg = 4 • doublyAntisymmetrizedProduct E (arg ∘ s) := by
      rw [← T_eq arg, ← T_eq (arg ∘ s)]
      exact Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun σ _ => by rw [key σ τ]
    have h4' : (4 : ℂ) • doublyAntisymmetrizedProduct E arg = (4 : ℂ) • doublyAntisymmetrizedProduct E (arg ∘ s) := by
      rw [show (4 : ℂ) = ((4 : ℕ) : ℂ) by norm_num, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
      exact h4
    exact (smul_right_injective A (by norm_num : (4 : ℂ) ≠ 0) h4').symm
  have antisymmetrizedProduct_perm_invariant {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (π : Equiv.Perm (Fin n))
      (arg : Fin n → ℂ) : doublyAntisymmetrizedProduct E (arg ∘ π) = doublyAntisymmetrizedProduct E arg := by
    cases n with
    | zero =>
      have h : arg ∘ π = arg := funext fun k => k.elim0
      rw [h]
    | succ m =>
      have hπ : π ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
        rw [Equiv.Perm.mclosure_swap_castSucc_succ]
        trivial
      revert arg
      induction hπ using Submonoid.closure_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        intro arg
        exact antisymmetrizedProduct_adjacent_swap E i arg
      | one =>
        intro arg
        rfl
      | mul x y _ _ hx hy =>
        intro arg
        show doublyAntisymmetrizedProduct E ((arg ∘ x) ∘ y) = _
        rw [hy (arg ∘ x), hx arg]
  have antisymmetrizedProduct_eq_factorial_smul_qdet {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (u : ℂ) :
      doublyAntisymmetrizedProduct E (fun k => u - (k : ℂ)) = (n.factorial : ℂ) • qdet E u := by

    have hcol : ∀ (b : Fin n → Fin n) (τ : Equiv.Perm (Fin n)),
        qminor E id (b ∘ τ) u = ((Equiv.Perm.sign τ : ℤ) : A) * qminor E id b u := by
      cases n with
      | zero =>
        intro b τ
        rw [Subsingleton.elim τ 1]
        simp
      | succ m =>
        intro b τ
        have hτ : τ ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
          rw [Equiv.Perm.mclosure_swap_castSucc_succ]
          trivial
        revert b
        induction hτ using Submonoid.closure_induction with
        | mem x hx =>
          obtain ⟨i, rfl⟩ := hx
          intro b
          rw [quantumMinor_adjacent_col_swap E hE id b i u, Equiv.Perm.sign_swap (Fin.castSucc_lt_succ (i := i)).ne]
          simp
        | one =>
          intro b
          simp
        | mul x y _ _ hx hy =>
          intro b
          show qminor E id ((b ∘ x) ∘ y) u = _
          rw [hy (b ∘ x), hx b]
          simp only [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul, ← mul_assoc]
          congr 1
          exact (Int.cast_commute _ _).eq
    simp only [doublyAntisymmetrizedProduct, ← Finset.mul_sum]
    have hin : ∀ τ : Equiv.Perm (Fin n), ∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) *
        orderedTermProduct E (fun k => u - (k : ℂ)) σ τ = qminor E id (id ∘ τ) u := fun τ => rfl
    have hsq : ∀ τ : Equiv.Perm (Fin n), ((Equiv.Perm.sign τ : ℤ) : A) *
        (((Equiv.Perm.sign τ : ℤ) : A) * qminor E id id u) = qminor E id id u := by
      intro τ
      rw [← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one,
        one_mul]
    simp only [hin, hcol, hsq, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℂ]
    rfl
  have term_neg_transpose {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (y : ℂ) (a b : Fin n) :
      Tm (fun a b => -E b a) y a b = -Tm E (-y) b a := by
    simp only [Tm]
    by_cases h : a = b
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl, map_neg]
      abel
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
      simp
  have orderedTermProduct_neg_transpose {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (arg : Fin n → ℂ)
      (σ τ : Equiv.Perm (Fin n)) :
      orderedTermProduct (fun a b => -E b a) arg σ τ = (-1) ^ n * orderedTermProduct E (fun k => -arg k) τ σ := by
    simp only [orderedTermProduct]
    have h : (fun k : Fin n => Tm (fun a b => -E b a) (arg k) (σ k) (τ k)) =
        fun k => -(Tm E (-arg k) (τ k) (σ k)) := funext fun k => term_neg_transpose E (arg k) (σ k) (τ k)
    rw [h, show (List.ofFn fun k => -(Tm E (-arg k) (τ k) (σ k))) =
        (List.ofFn fun k => Tm E (-arg k) (τ k) (σ k)).map Neg.neg by rw [List.map_ofFn]; rfl,
      List.prod_map_neg, List.length_ofFn]
  have antisymmetrizedProduct_neg_transpose {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (arg : Fin n → ℂ) :
      doublyAntisymmetrizedProduct (fun a b => -E b a) arg = (-1) ^ n * doublyAntisymmetrizedProduct E (fun k => -arg k) := by
    simp only [doublyAntisymmetrizedProduct, orderedTermProduct_neg_transpose]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun κ _ => ?_

    rw [show ((-1 : A)) ^ n = (((-1 : ℤ) ^ n : ℤ) : A) by push_cast; rfl]
    simp only [← zsmul_eq_mul, smul_smul]
    congr 1
    ring
  have quantumDet_neg_transpose {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (x : ℂ) :
      qdet (fun a b => -E b a) x = ((-1 : ℂ) ^ n) • qdet E ((n : ℂ) - 1 - x) := by
    have hE' : GlRel (fun a b => -E b a) := by
      intro a b c d
      have h := hE b a d c
      simp only [neg_mul_neg]
      rw [h]
      by_cases h1 : a = d <;> by_cases h2 : c = b
      · subst h1 h2
        simp
        abel
      · subst h1
        simp [h2, Ne.symm h2]
      · subst h2
        simp [h1, Ne.symm h1]
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
    have h1 := antisymmetrizedProduct_eq_factorial_smul_qdet (fun a b => -E b a) hE' x
    have h2 := antisymmetrizedProduct_neg_transpose E (fun k => x - (k : ℂ))
    have h3 : (fun k : Fin n => -(x - (k : ℂ))) = (fun k : Fin n => ((n : ℂ) - 1 - x) - (k : ℂ)) ∘ Fin.revPerm := by
      funext k
      simp only [Function.comp_apply, Fin.revPerm_apply, Fin.val_rev]
      rw [Nat.cast_sub (Nat.succ_le_of_lt k.isLt)]
      push_cast
      ring
    have h4 := antisymmetrizedProduct_perm_invariant E Fin.revPerm (fun k : Fin n => ((n : ℂ) - 1 - x) - (k : ℂ))
    have h5 := antisymmetrizedProduct_eq_factorial_smul_qdet E hE ((n : ℂ) - 1 - x)
    refine smul_right_injective A (by exact_mod_cast n.factorial_ne_zero : ((n.factorial : ℕ) : ℂ) ≠ 0) ?_
    show ((n.factorial : ℕ) : ℂ) • qdet (fun a b => -E b a) x = ((n.factorial : ℕ) : ℂ) • (((-1 : ℂ) ^ n) • qdet E ((n : ℂ) - 1 - x))
    rw [← h1, h2, h3, h4, h5, smul_comm, Algebra.smul_def ((-1 : ℂ) ^ n)]
    simp
  rw [qdet_conj e X (fun i j => -X j i) h, quantumDet_neg_transpose X hX,
    show (a : ℂ) - 1 - (u + ((a : ℂ) - 1) / 2) = -u + ((a : ℂ) - 1) / 2 by ring, LinearMap.smul_apply, map_smul]

theorem cap_dualFn (τ : E →+* ℂ) (u : ℂ) (φ : Sm E a) :
    cap τ u (dualFn E a φ) = (-1 : ℂ) ^ a • dualFn E a (cap τ (-u) φ) :=
  qdet_dual (dualFn E a) (Eop τ) (glRel_Eop τ) (Eop_dualFn τ) u φ

theorem Zalg_dualFn {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    ∃ z' ∈ Zalg E a, ∀ φ, z (dualFn E a φ) = dualFn E a (z' φ) := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, u, rfl⟩ := hx
    have h : cap τ (-u) ∈ Zalg E a := Algebra.subset_adjoin ⟨τ, -u, rfl⟩
    exact ⟨_, Subalgebra.smul_mem (Zalg E a) h ((-1 : ℂ) ^ a), fun φ => by
      rw [cap_dualFn, LinearMap.smul_apply, map_smul]⟩
  | algebraMap c => exact ⟨_, Subalgebra.algebraMap_mem _ c, fun φ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' + y', add_mem h1 h3, fun φ => by simp [h2, h4]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' * y', mul_mem h1 h3, fun φ => by simp [h2, h4]⟩


omit [_root_.NumberField.IsTotallyComplex E] in
theorem height_invT (y : GL (Fin a) (Cinf E)) : height (invT a _ y) = height y := by
  unfold height
  rw [invT_val, invT_inv_val, InvT.norm_transpose, InvT.norm_transpose, add_right_comm]

theorem isAutForm_dualFn {φ : Sm E a} (h : IsAutForm φ) : IsAutForm (dualFn E a φ) := by
  refine { left := ?_, level := ?_, kfin := ?_, zfin := ?_, growth := ?_ }
  · intro γ g
    rw [dualFn_apply, dualFn_apply, map_mul, ← ratGL_invT, h.left]
  · convert h.level.preimage (continuous_invT (R := Af E) (a := a)) using 1
    ext k
    exact (Iff.of_eq (congrArg (· = dualFn E a φ) (act_dualFn (.fin k) φ))).trans (dualFn E a).injective.eq_iff
  · have := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map
      (dualFn E a).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨_, rfl⟩, (act_dualFn (.cpt k) φ).symm⟩
  · have := h.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) ''
      Zalg E a)).map (dualFn E a).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨z', h1, h2⟩ := Zalg_dualFn hz
    exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩
  · intro g
    obtain ⟨C, N, h1⟩ := h.growth (invT a (Ad E) g)
    refine ⟨C, N, fun y => ?_⟩
    rw [dualFn_apply, map_mul, ← infGL_invT, ← height_invT]
    exact h1 _

theorem isCuspForm_dualFn {φ : Sm E a} (h : IsCuspForm φ) : IsCuspForm (dualFn E a φ) :=
  ⟨isAutForm_dualFn h.1, isCuspidal_invT h.1.left h.2⟩

variable (π : CuspSub E a)

def dual : CuspSub E a where
  V := π.V.map (dualFn E a).toLinearMap
  cusp := by rintro _ ⟨φ, hφ, rfl⟩; exact isCuspForm_dualFn (π.cusp φ hφ)
  stable := by
    rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, π.stable _ φ hφ, (act_dualFn o φ).symm⟩
  ne_bot h := π.ne_bot ((Submodule.map_eq_bot_iff (e := dualFn E a)).1 h)
  irred W hW hs := by
    have h := π.irred (W.comap (dualFn E a).toLinearMap) (fun φ hφ => by
      obtain ⟨ψ, h1, h2⟩ := hW hφ
      rwa [← (dualFn E a).injective h2]) fun o φ hφ => by
      have h1 := hs (invTOp o) _ hφ
      change act _ (dualFn E a φ) ∈ W at h1
      rw [act_dualFn, invTOp_invTOp] at h1
      exact h1
    have e := Submodule.map_comap_eq_of_surjective (f := (dualFn E a).toLinearMap) (dualFn E a).surjective W
    exact h.imp (fun h => by rw [← e, h, Submodule.map_bot]) fun h => by rw [← e, h]

def toDual : π.V ≃ₗ[ℂ] (dual π).V := (dualFn E a).submoduleMap π.V

theorem op_toDual (o : Op E a) (φ : π.V) : (dual π).op o (toDual π φ) = toDual π (π.op (invTOp o) φ) :=
  Subtype.ext (act_dualFn o φ.1)

theorem finPart_toDual (k : GL (Fin a) (Af E)) (φ : π.V) :
    (dual π).finPart k (toDual π φ) = toDual π (π.finPart (invT a (Af E) k) φ) := op_toDual π (.fin k) φ

theorem locRep_toDual (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) (φ : π.V) :
    (dual π).locRep w g (toDual π φ) = toDual π (π.locRep w (invT a _ g) φ) :=
  (finPart_toDual π (locGL E a w g) φ).trans (by rw [← locGL_invT]; rfl)

variable {π} {π' : CuspSub E a}

theorem hasSatGL_dual {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : GlobalTheory.LFun.HasSatGL w (π.locRep w) B) :
    GlobalTheory.LFun.HasSatGL w ((dual π).locRep w) (B.map (·⁻¹)) :=
  hasSatGL_invT (toDual π) (locRep_toDual π w) h

end UpperTheory.V.TC
