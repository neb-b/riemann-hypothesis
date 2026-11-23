module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasimirSplitting
section
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckCasSplit

open Formalism.FourierDecayAlt.ThreeDimData CompanionTheory.D.Upq.Sm
open PI.UpqRep (InLieHpk)

variable {k r : ℕ}

theorem hpk_herm (k r : ℕ) : (Formalism.QuantumDeterminants.Hpk k r)ᴴ = Formalism.QuantumDeterminants.Hpk k r := by
  ext i j
  have hi := i.2
  have hj := j.2
  simp only [Matrix.conjTranspose_apply, Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  split_ifs <;> first | omega | simp

theorem hpk_row (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    ∃ (j₀ : Fin (2 * r + k + 1)) (s : ℂ), s * s = 1 ∧ (∀ j, Formalism.QuantumDeterminants.Hpk k r i j = if j = j₀ then s else 0) ∧
      ∀ j, Formalism.QuantumDeterminants.Hpk k r j₀ j = if j = i then s else 0 := by
  have hi := i.2
  by_cases h : r ≤ i.1 ∧ i.1 ≤ r + k
  · refine ⟨i, if i.1 = r + k then -1 else 1, by split_ifs <;> simp, fun j => ?_, fun j => ?_⟩ <;>
    · have hj := j.2
      simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
      split_ifs <;> first | rfl | omega
  · refine ⟨⟨2 * r + k - i.1, by omega⟩, 1, by simp, fun j => ?_, fun j => ?_⟩ <;>
    · have hj := j.2
      simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
      split_ifs <;> first | rfl | omega

theorem hpk_sq (k r : ℕ) : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := by
  ext i j
  obtain ⟨j₀, s, hs, h1, h2⟩ := hpk_row k r i
  simp only [Matrix.mul_apply, h1, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, h2,
    Matrix.one_apply]
  by_cases hij : i = j
  · simp [hij, hs]
  · simp [hij, Ne.symm hij]

theorem flip_facts {n : ℕ} (Hm Y : Matrix (Fin n) (Fin n) ℂ) (h1 : Hmᴴ = Hm) (h2 : Hm * Hm = 1) :
    (Hm * Yᴴ * Hm)ᴴ * Hm = Hm * Y ∧ Hm * (Hm * Yᴴ * Hm) = Yᴴ * Hm := by
  constructor
  · simp only [Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, h2,
      Matrix.mul_one]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem reH_lie (Y : Mx k r) : InLieHpk k r (reH k r Y) := by
  obtain ⟨h3, h4⟩ := flip_facts _ Y (hpk_herm k r) (hpk_sq k r)
  show (reH k r Y)ᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * reH k r Y = 0
  simp only [reH, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, h3, h4]
  have : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [this, ← smul_add]
  abel_nf
  simp

theorem imH_lie (Y : Mx k r) : InLieHpk k r (imH k r Y) := by
  obtain ⟨h3, h4⟩ := flip_facts _ Y (hpk_herm k r) (hpk_sq k r)
  show (imH k r Y)ᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * imH k r Y = 0
  simp only [imH, sub_neg_eq_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, h3, h4]
  have : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
    simp
  rw [this, neg_smul, add_comm (Yᴴ * _), neg_add_cancel]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem diff_entry {F : FRep k r} (hF : F.OK) {X : Mx k r} (hX : InLieHpk k r X) (c d : F.ι) :
    HasDerivAt (fun t : ℝ => F.ρ (NormedSpace.exp ((t : ℂ) • X)) c d) (F.dR X c d) 0 := by
  have h1 : PI.UpqRep.inUH (PI.UpqRep.Hpk k r) 1 := by simp [PI.UpqRep.inUH]
  obtain ⟨U, G, hU, h1U, hG, hfG⟩ := hF.smooth c d 1 h1
  have hd : HasDerivAt (fun t => ex X t) X 0 := by
    simpa using hasDerivAt_mul_ex 1 X
  exact (hasDerivAt_local (A := {g | PI.UpqRep.inUH (PI.UpqRep.Hpk k r) g}) (f := fun g => F.ρ g c d)
    (ex_mem_of_lie hX) (ex_zero X) hd hU h1U hG hfG).differentiableAt.hasDerivAt

theorem dR_tens {F F' : FRep k r} (hF : F.OK) (hF' : F'.OK) {X : Mx k r} (hX : InLieHpk k r X) :
    (F.tens F').dR X = F.dR X ⊗ₖ (1 : Matrix F'.ι F'.ι ℂ) + (1 : Matrix F.ι F.ι ℂ) ⊗ₖ F'.dR X := by
  ext ⟨c, c'⟩ ⟨d, d'⟩
  have h := ((diff_entry hF hX c d).mul (diff_entry hF' hX c' d')).deriv
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hF.one, hF'.one] at h
  exact h

theorem dC_tens {F F' : FRep k r} (hF : F.OK) (hF' : F'.OK) (Y : Mx k r) :
    (F.tens F').dC Y = F.dC Y ⊗ₖ (1 : Matrix F'.ι F'.ι ℂ) + (1 : Matrix F.ι F.ι ℂ) ⊗ₖ F'.dC Y := by
  simp only [FRep.dC, dR_tens hF hF' (reH_lie Y), dR_tens hF hF' (imH_lie Y), Matrix.add_kronecker,
    Matrix.kronecker_add, Matrix.smul_kronecker, Matrix.kronecker_smul, smul_add]
  abel

section Lin

set_option linter.unusedSectionVars false

variable {ι κ V : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [AddCommGroup V] [Module ℂ V]

theorem mAct_apply (A : Matrix κ ι ℂ) (x : ι → V) (c : κ) : mAct A x c = ∑ d, A c d • x d := by
  simp [mAct]

theorem mAct_add (A B : Matrix ι ι ℂ) : (mAct (A + B) : Module.End ℂ (ι → V)) = mAct A + mAct B := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [mAct_apply, add_smul, Finset.sum_add_distrib]

theorem mAct_sum {α : Type} (s : Finset α) (A : α → Matrix ι ι ℂ) :
    (mAct (∑ a ∈ s, A a) : Module.End ℂ (ι → V)) = ∑ a ∈ s, mAct (A a) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp only [mAct_apply, Matrix.sum_apply, LinearMap.sum_apply, Finset.sum_apply, Finset.sum_smul]
  exact Finset.sum_comm

theorem mAct_mul (A B : Matrix ι ι ℂ) : (mAct A * mAct B : Module.End ℂ (ι → V)) = mAct (A * B) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp only [Module.End.mul_apply, mAct_apply, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

theorem dOp_mul (S T : Module.End ℂ V) : (dOp ι (S * T) : Module.End ℂ (ι → V)) = dOp ι S * dOp ι T := rfl

theorem dOp_sum {α : Type} (s : Finset α) (T : α → Module.End ℂ V) :
    (dOp ι (∑ a ∈ s, T a) : Module.End ℂ (ι → V)) = ∑ a ∈ s, dOp ι (T a) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [dOp]

theorem left_factor_action_mul (f g : Module.End ℂ (ι → V)) :
    (on1 (f * g) : Module.End ℂ (ι × κ → V)) = on1 f * on1 g := rfl

theorem right_factor_action_mul (f g : Module.End ℂ (κ → V)) :
    (on2 (f * g) : Module.End ℂ (ι × κ → V)) = on2 f * on2 g := rfl

theorem left_factor_action_add (f g : Module.End ℂ (ι → V)) :
    (on1 (f + g) : Module.End ℂ (ι × κ → V)) = on1 f + on1 g := rfl

theorem right_factor_action_add (f g : Module.End ℂ (κ → V)) :
    (on2 (f + g) : Module.End ℂ (ι × κ → V)) = on2 f + on2 g := rfl

theorem left_factor_action_sum {α : Type} (s : Finset α) (T : α → Module.End ℂ (ι → V)) :
    (on1 (∑ a ∈ s, T a) : Module.End ℂ (ι × κ → V)) = ∑ a ∈ s, on1 (T a) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [on1]

theorem right_factor_action_sum {α : Type} (s : Finset α) (T : α → Module.End ℂ (κ → V)) :
    (on2 (∑ a ∈ s, T a) : Module.End ℂ (ι × κ → V)) = ∑ a ∈ s, on2 (T a) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [on2]

theorem left_factor_action_diag_op (T : Module.End ℂ V) : (on1 (dOp ι T) : Module.End ℂ (ι × κ → V)) = dOp (ι × κ) T := rfl

theorem right_factor_action_diag_op (T : Module.End ℂ V) : (on2 (dOp κ T) : Module.End ℂ (ι × κ → V)) = dOp (ι × κ) T := rfl

theorem left_factor_action_kronecker (A : Matrix ι ι ℂ) :
    (on1 (mAct A) : Module.End ℂ (ι × κ → V)) = mAct (A ⊗ₖ (1 : Matrix κ κ ℂ)) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [on1, mAct_apply, Fintype.sum_prod_type, Matrix.one_apply, LinearMap.funLeft_apply, kroneckerMap]

theorem right_factor_action_kronecker (A : Matrix κ κ ℂ) :
    (on2 (mAct A) : Module.End ℂ (ι × κ → V)) = mAct ((1 : Matrix ι ι ℂ) ⊗ₖ A) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [on2, mAct_apply, Fintype.sum_prod_type, Matrix.one_apply, LinearMap.funLeft_apply, kroneckerMap]

theorem expand {R α : Type} [Ring R] [Fintype α] (E A B : α → α → R) (Q : R)
    (h1 : ∑ a, ∑ b, A a b * B b a = Q) (h2 : ∑ a, ∑ b, B a b * A b a = Q) :
    ∑ a, ∑ b, (E a b + (A a b + B a b)) * (E b a + (A b a + B b a)) =
      ∑ a, ∑ b, (E a b + A a b) * (E b a + A b a) + ∑ a, ∑ b, (E a b + B a b) * (E b a + B b a)
        - ∑ a, ∑ b, E a b * E b a + (Q + Q) := by
  nth_rewrite 1 [← h1]
  rw [← h2]
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  abel

end Lin

theorem casSplit : CasSplit := by
  intro k r F F' U hF hF'
  simp only [cas, cas1, cas2, casR, L, left_factor_action_sum, right_factor_action_sum, left_factor_action_mul, right_factor_action_mul, left_factor_action_add, right_factor_action_add, left_factor_action_diag_op, right_factor_action_diag_op,
    left_factor_action_kronecker, right_factor_action_kronecker, dC_tens hF hF', mAct_add, dOp_sum, dOp_mul, two_smul]
  refine expand (fun a b => dOp (F.ι × F'.ι) (U.dC (Matrix.single a b 1)))
    (fun a b => mAct (F.dC (Matrix.single a b 1) ⊗ₖ (1 : Matrix F'.ι F'.ι ℂ)))
    (fun a b => mAct ((1 : Matrix F.ι F.ι ℂ) ⊗ₖ F'.dC (Matrix.single a b 1))) _ ?_ ?_
  · simp only [mAct_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, qMat, mAct_sum]
  · rw [Finset.sum_comm]
    simp only [mAct_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, qMat, mAct_sum]

end GlobalTheory.CompanionTheory.ZuckCasSplit

end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CountingBound
section
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

namespace GlobalTheory.CompanionTheory.ZuckCount

theorem casG_polar {n : ℕ} (μ : Fin n → ℝ) (J : Finset (Fin n)) (s : Fin n) :
    casG (addSet μ J) + casG (μ + Pi.single s 1) + (2 - casG μ) - casG (addSet μ J + Pi.single s 1)
      = if s ∈ J then 0 else 2 := by
  have h : ∑ a, ((addSet μ J a) ^ 2 + ((μ + Pi.single s 1 : Fin n → ℝ) a) ^ 2 - μ a ^ 2
      - ((addSet μ J + Pi.single s 1 : Fin n → ℝ) a) ^ 2) = if s ∈ J then -2 else 0 := by
    rw [Finset.sum_eq_single s]
    · simp only [addSet, Pi.add_apply, Pi.single_eq_same]
      split_ifs <;> ring
    · intro b _ hb
      simp only [addSet, Pi.add_apply, Pi.single_eq_of_ne hb]
      ring
    · simp
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at h
  unfold casG
  split_ifs at h ⊢ <;> linarith

theorem addSet_insert {n : ℕ} (μ : Fin n → ℝ) (J : Finset (Fin n)) (s : Fin n) (hs : s ∉ J) :
    addSet μ J + Pi.single s 1 = addSet μ (insert s J) := by
  funext a
  by_cases ha : a = s
  · subst ha
    simp [addSet, hs]
  · simp [addSet, ha]

theorem addSet_eq_iff {n : ℕ} (μ : Fin n → ℝ) (J I : Finset (Fin n)) (s : Fin n) :
    addSet μ J + Pi.single s 1 = addSet μ I ↔ s ∉ J ∧ I = insert s J := by
  constructor
  · intro h
    have hs : s ∉ J := by
      intro hs
      have := congrFun h s
      simp only [addSet, Pi.add_apply, Pi.single_eq_same, if_pos hs] at this
      split_ifs at this <;> linarith
    refine ⟨hs, ?_⟩
    rw [addSet_insert μ J s hs] at h
    ext a
    have := congrFun h a
    simp only [addSet, add_right_inj] at this
    by_cases h1 : a ∈ I <;> by_cases h2 : a ∈ insert s J <;> simp_all
  · rintro ⟨hs, rfl⟩
    exact addSet_insert μ J s hs

theorem casG_polar_complex {n : ℕ} (μ : Fin n → ℝ) (J : Finset (Fin n)) (s : Fin n) :
    (casG (addSet μ J) : ℂ) + (casG (μ + Pi.single s 1) : ℂ) + (2 - (casG μ : ℂ))
      - (casG (addSet μ J + Pi.single s 1) : ℂ) = if s ∈ J then 0 else 2 := by
  have h := congrArg (fun x : ℝ => (x : ℂ)) (casG_polar μ J s)
  split_ifs at h ⊢ <;> (push_cast at h; exact h)

theorem count : Count := by
  intro n m μ _ par w
  have hw : ∀ p, w p (par p) = if p.2 ∈ p.1.1 then 0 else 2 := fun p => casG_polar_complex μ p.1.1 p.2
  refine ⟨fun I => ?_, fun ν hν => ?_⟩
  · have h1 : ∀ p ∈ univ.filter (fun p => par p = addSet μ I.1), w p (addSet μ I.1) = 2 := by
      intro p hp
      have hp' := (Finset.mem_filter.1 hp).2
      rw [← hp', hw, if_neg ((addSet_eq_iff μ p.1.1 I.1 p.2).1 hp').1]
    rw [Finset.sum_congr rfl h1, Finset.sum_const]
    have hc : (univ.filter (fun p => par p = addSet μ I.1)).card = I.1.card := by
      refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
      · intro p hp
        have := (addSet_eq_iff μ p.1.1 I.1 p.2).1 (Finset.mem_filter.1 hp).2
        rw [this.2]; exact Finset.mem_insert_self _ _
      · intro p hp q hq hpq
        have h1 := (addSet_eq_iff μ p.1.1 I.1 p.2).1 (Finset.mem_filter.1 hp).2
        have h2 := (addSet_eq_iff μ q.1.1 I.1 q.2).1 (Finset.mem_filter.1 hq).2
        have hpq' : p.2 = q.2 := hpq
        refine Prod.ext (Subtype.ext ?_) hpq'
        rw [← Finset.erase_insert h1.1, ← Finset.erase_insert h2.1, ← h1.2, ← h2.2, hpq']
      · intro s hs
        refine ⟨(⟨I.1.erase s, ?_⟩, s), Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, rfl⟩
        · rw [Finset.card_erase_of_mem hs, I.2]; rfl
        · exact (addSet_eq_iff μ _ I.1 s).2 ⟨Finset.notMem_erase _ _, (Finset.insert_erase hs).symm⟩
    rw [hc, I.2, nsmul_eq_mul]
    push_cast
    ring
  · refine Finset.sum_eq_zero fun p hp => ?_
    have hp' := (Finset.mem_filter.1 hp).2
    rw [← hp', hw, if_pos]
    by_contra hs
    refine hν ⟨insert p.2 p.1.1, ?_⟩ ?_
    · rw [Finset.card_insert_of_notMem hs, p.1.2]
    · rw [← hp']; exact (addSet_insert μ _ _ hs).symm

end GlobalTheory.CompanionTheory.ZuckCount
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfTensorFromHomLaws
section
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckDecTens

section Lin

universe u

variable {O : Type u} {N : O → Type} [∀ o, AddCommGroup (N o)] [∀ o, Module ℂ (N o)]

theorem dec_comp {Hom : ∀ a b, (N a →ₗ[ℂ] N b) → Prop} (hc : IsLinCat N Hom) {A B P : Type} [Fintype A] [Fintype B]
    [Fintype P] (e : P ≃ A × B) {X : O} {Z : A → O} {S : A → B → O}
    {j : ∀ a, N (Z a) →ₗ[ℂ] N X} {q : ∀ a, N X →ₗ[ℂ] N (Z a)} (h : IsDec Hom X Z j q)
    {io : ∀ a b, N (S a b) →ₗ[ℂ] N (Z a)} {pr : ∀ a b, N (Z a) →ₗ[ℂ] N (S a b)}
    (h2 : ∀ a, IsDec Hom (Z a) (S a) (io a) (pr a)) :
    IsDec Hom X (fun p => S (e p).1 (e p).2) (fun p => j (e p).1 ∘ₗ io (e p).1 (e p).2)
      (fun p => pr (e p).1 (e p).2 ∘ₗ q (e p).1) := by
  exact {
    io_hom p := hc.comp _ _ _ _ _ ((h2 _).io_hom _) (h.io_hom _)
    pr_hom p := hc.comp _ _ _ _ _ (h.pr_hom _) ((h2 _).pr_hom _)
    sum := by
      rw [Equiv.sum_comp e (fun p : A × B => (j p.1 ∘ₗ io p.1 p.2) ∘ₗ (pr p.1 p.2 ∘ₗ q p.1)),
        Fintype.sum_prod_type, ← h.sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      ext x
      have := congrArg (fun f => j a (f (q a x))) (h2 a).sum
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum] using this
    pr_io p := by
      ext x
      have h1 := LinearMap.congr_fun (h.pr_io (e p).1) (io (e p).1 (e p).2 x)
      have h3 := LinearMap.congr_fun ((h2 (e p).1).pr_io (e p).2) x
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1 h3 ⊢
      rw [h1, h3]
    pr_io_ne p p' hne := by
      have hne' : e p ≠ e p' := fun hh => hne (e.injective hh)
      generalize e p = s at hne'
      generalize e p' = s' at hne'
      obtain ⟨a, b⟩ := s
      obtain ⟨a', b'⟩ := s'
      ext x
      by_cases ha : a = a'
      · subst ha
        have hb : b ≠ b' := fun hh => hne' (by rw [hh])
        have h1 := LinearMap.congr_fun (h.pr_io a) (io a b' x)
        have h3 := LinearMap.congr_fun ((h2 a).pr_io_ne b b' hb) x
        simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply] at h1 h3 ⊢
        rw [h1, h3]
      · have h1 := LinearMap.congr_fun (h.pr_io_ne a a' ha) (io a' b' x)
        simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h1 ⊢
        rw [h1, map_zero]
  }

end Lin

variable {k r : ℕ}

theorem mAct_reindex {ι ι' V : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℂ V] (e : ι' → ι) :
    (mAct ((1 : Matrix ι ι ℂ).submatrix e id) : (ι → V) →ₗ[ℂ] (ι' → V)) = LinearMap.funLeft ℂ V e := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [mAct, LinearMap.funLeft_apply, Matrix.one_apply]

theorem hom_reindex (hM : MatHom) (F F' : FRep k r) (U : URep k r) (e : F'.ι ≃ F.ι)
    (h : ∀ g, F'.ρ g = (F.ρ g).submatrix e e) :
    IsHom (F, U) (F', U) (LinearMap.funLeft ℂ U.R.smSub e) := by
  have := hM k r F F' U ((1 : Matrix F.ι F.ι ℂ).submatrix e id) (fun g _ => by
    rw [h g, Matrix.submatrix_mul_equiv, Matrix.mul_one]
    have := Matrix.submatrix_mul_equiv (1 : Matrix F.ι F.ι ℂ) (F.ρ g) e (Equiv.refl _) id
    simpa using this)
  rwa [mAct_reindex] at this

theorem hom_cas (hL : HomLie) {X Y : Obj k r} {f : M X →ₗ[ℂ] M Y} (hX : X.1.OK) (hY : Y.1.OK) (hf : IsHom X Y f) :
    cas Y ∘ₗ f = f ∘ₗ cas X := by
  refine LinearMap.ext fun x => ?_
  have h := fun Z y => LinearMap.congr_fun (hL k r X Y f hX hY hf Z) y
  simp only [LinearMap.comp_apply] at h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cas, LinearMap.comp_apply, LinearMap.sum_apply, map_sum, mul_apply_eq_comp, h]

theorem dec1 (hC : HomCat) (hM : MatHom) (hT : TensHom) (F F' : FRep k r) (U : URep k r) {A : Type} [Fintype A]
    (T : A → URep k r) {io : ∀ a, M (one (T a)) →ₗ[ℂ] M (F, U)} {pr : ∀ a, M (F, U) →ₗ[ℂ] M (one (T a))}
    (h : IsDec (N := M) IsHom (F, U) (fun a => one (T a)) io pr) :
    IsDec (N := M) IsHom (F.tens F', U) (fun a => (F', T a))
      (fun a => on1 (io a) ∘ₗ LinearMap.funLeft ℂ _ (Prod.snd : Unit × F'.ι → F'.ι))
      (fun a => LinearMap.funLeft ℂ _ (fun c : F'.ι => ((), c)) ∘ₗ on1 (pr a)) := by
  exact {
    io_hom a := (hC k r).comp _ ((triv k r).tens F', T a) _ _ _
      (hom_reindex hM F' ((triv k r).tens F') (T a) (Equiv.punitProd _) (fun g => by
        ext c d; simp))
      (hT k r _ _ F' _ _ _ (h.io_hom a)).1
    pr_hom a := (hC k r).comp _ ((triv k r).tens F', T a) _ _ _
      (hT k r _ _ F' _ _ _ (h.pr_hom a)).1
      (hom_reindex hM ((triv k r).tens F') F' (T a) (Equiv.punitProd _).symm (fun g => by
        ext c d; simp))
    sum := by
      refine LinearMap.ext fun x => funext fun p => ?_
      have := congrFun (LinearMap.congr_fun h.sum (fun c => x (c, p.2))) p.1
      rw [LinearMap.sum_apply, Finset.sum_apply] at this ⊢
      exact this
    pr_io a := by
      refine LinearMap.ext fun x => funext fun c => ?_
      exact congrFun (LinearMap.congr_fun (h.pr_io a) (fun _ => x c)) ()
    pr_io_ne a a' hne := by
      refine LinearMap.ext fun x => funext fun c => ?_
      exact congrFun (LinearMap.congr_fun (h.pr_io_ne a a' hne) (fun _ => x c)) ()
  }

theorem dec2 (hC : HomCat) (hM : MatHom) (hT : TensHom) (F F' : FRep k r) (U : URep k r) {A : Type} [Fintype A]
    (T : A → URep k r) {io : ∀ a, M (one (T a)) →ₗ[ℂ] M (F', U)} {pr : ∀ a, M (F', U) →ₗ[ℂ] M (one (T a))}
    (h : IsDec (N := M) IsHom (F', U) (fun a => one (T a)) io pr) :
    IsDec (N := M) IsHom (F.tens F', U) (fun a => (F, T a))
      (fun a => on2 (io a) ∘ₗ LinearMap.funLeft ℂ _ (Prod.fst : F.ι × Unit → F.ι))
      (fun a => LinearMap.funLeft ℂ _ (fun c : F.ι => (c, ())) ∘ₗ on2 (pr a)) := by
  exact {
    io_hom a := (hC k r).comp _ (F.tens (triv k r), T a) _ _ _
      (hom_reindex hM F (F.tens (triv k r)) (T a) (Equiv.prodPUnit _) (fun g => by
        ext c d; simp))
      (hT k r _ _ F _ _ _ (h.io_hom a)).2
    pr_hom a := (hC k r).comp _ (F.tens (triv k r), T a) _ _ _
      (hT k r _ _ F _ _ _ (h.pr_hom a)).2
      (hom_reindex hM (F.tens (triv k r)) F (T a) (Equiv.prodPUnit _).symm (fun g => by
        ext c d; simp))
    sum := by
      refine LinearMap.ext fun x => funext fun p => ?_
      have := congrFun (LinearMap.congr_fun h.sum (fun c => x (p.1, c))) p.2
      rw [LinearMap.sum_apply, Finset.sum_apply] at this ⊢
      exact this
    pr_io a := by
      refine LinearMap.ext fun x => funext fun c => ?_
      exact congrFun (LinearMap.congr_fun (h.pr_io a) (fun _ => x c)) ()
    pr_io_ne a a' hne := by
      refine LinearMap.ext fun x => funext fun c => ?_
      exact congrFun (LinearMap.congr_fun (h.pr_io_ne a a' hne) (fun _ => x c)) ()
  }

theorem decTens : HomCat → MatHom → TensHom → HomLie → OKTriv → DecTens := by
  intro hC hM hT hL hO k r F F' U hF hF'
  refine ⟨fun A B _ _ T S c ⟨io, pr, h⟩ h2 hc => ?_, fun A B _ _ T S c ⟨io, pr, h⟩ h2 hc => ?_⟩
  · choose io2 pr2 h2 using h2
    refine ⟨_, _, dec_comp (hC k r) (Equiv.refl (A × B)) (S := fun a b => one (S (a, b)))
      (dec1 hC hM hT F F' U T h) h2, fun p => ?_⟩
    have h3 := hom_cas hL (X := one (T p.1)) (Y := (F, U)) (hO k r) hF (h.io_hom p.1)
    rw [hc, LinearMap.comp_smul, LinearMap.comp_id] at h3
    refine LinearMap.ext fun x => funext fun s => ?_
    exact congrFun (LinearMap.congr_fun h3 (fun _ => io2 p.1 p.2 x s.2)) s.1
  · choose io2 pr2 h2 using h2
    refine ⟨_, _, dec_comp (hC k r) (Equiv.prodComm A B) (S := fun b a => one (S (a, b)))
      (dec2 hC hM hT F F' U T h) h2, fun p => ?_⟩
    have h3 := hom_cas hL (X := one (T p.2)) (Y := (F', U)) (hO k r) hF' (h.io_hom p.2)
    rw [hc, LinearMap.comp_smul, LinearMap.comp_id] at h3
    refine LinearMap.ext fun x => funext fun s => ?_
    exact congrFun (LinearMap.congr_fun h3 (fun _ => io2 p.2 p.1 x s.1)) s.2

end GlobalTheory.CompanionTheory.ZuckDecTens

end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesLinear
section
open CompanionTheory.Bmu CompanionTheory.D.Upq.Sm

namespace GlobalTheory.CompanionTheory.BesselMapSm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem dsLin : DsLin := by
  intro n Hm H _ _ _ σ hσ u hu
  have h1 : (1 : Mat n) ∈ Formalism.QuantumDeterminants.UH Hm := hσ.grp.2.1
  obtain ⟨U, F, hUo, h1U, hF, hfF⟩ := hu 1 h1
  refine ⟨fderiv ℝ F 1, fun X hX => ?_⟩
  have hmem : ∀ t : ℝ, ex X t ∈ Formalism.QuantumDeterminants.UH Hm := fun t => ex_mem_of_lie hX t
  have hd : HasDerivAt (fun t : ℝ => ex X t) X 0 := by
    simpa using hasDerivAt_mul_ex (1 : Mat n) X
  have hl := hasDerivAt_local (f := fun g => σ g u) hmem (ex_zero X) hd hUo h1U hF hfF
  exact hl.deriv

end GlobalTheory.CompanionTheory.BesselMapSm
end

