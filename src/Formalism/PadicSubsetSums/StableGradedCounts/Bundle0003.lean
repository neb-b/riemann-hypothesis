module

public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0002
public import Lemmata.GeneralBFactRightRest.Imports

@[expose] public section

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.IRRCentralIdempotent
section
open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

section

variable {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem isIrreducible_of [Nontrivial V] (ρ : Representation ℂ G V)
    (h : ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤) :
    ρ.IsIrreducible := by
  unfold Representation.IsIrreducible
  refine { exists_pair_ne := ⟨⊥, ⊤, fun heq => ?_⟩, eq_bot_or_eq_top := fun W => ?_ }
  · have h1 := congrArg Subrepresentation.toSubmodule heq
    exact bot_ne_top (show (⊥ : Submodule ℂ V) = ⊤ from h1)
  · obtain ⟨S, hS⟩ := W
    rcases h S (fun g x hx => hS g hx) with h1 | h1
    · left
      subst h1
      rfl
    · right
      subst h1
      rfl

theorem schur_scalar [Nontrivial V] (ρ : Representation ℂ G V)
    (h : ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤)
    (a : G → ℂ) (ha : ∀ g k, a (k * g * k⁻¹) = a g) :
    ∃ μ : ℂ, (∑ g, a g • ρ g) = μ • (1 : Module.End ℂ V) := by
  set T : Module.End ℂ V := ∑ g, a g • ρ g with hT
  have hcomm : ∀ k, ρ k * T = T * ρ k := by
    intro k
    rw [hT, Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (MulAut.conj k).toEquiv _ _ (fun g => ?_)
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, ha, mul_smul_comm,
      smul_mul_assoc, ← map_mul, inv_mul_cancel_right]
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
  refine ⟨μ, ?_⟩
  have hW : ∀ g, ∀ x ∈ Module.End.eigenspace T μ, ρ g x ∈ Module.End.eigenspace T μ := by
    intro g x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [← Module.End.mul_apply, ← hcomm g, Module.End.mul_apply, hx, map_smul]
  rcases h _ hW with h0 | h0
  · exfalso
    first
      | exact Module.End.hasEigenvalue_iff.1 hμ h0
      | exact hμ h0
      | (obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
         have hv1 := hv.1
         rw [h0] at hv1
         exact hv.2 ((Submodule.mem_bot ℂ).1 hv1))
  · refine LinearMap.ext fun x => ?_
    have hx : x ∈ Module.End.eigenspace T μ := by
      rw [h0]
      exact Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at hx
    rw [hx]
    simp

theorem conv_char [Nontrivial V] (ρ : Representation ℂ G V)
    (h : ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤)
    (a : G → ℂ) (ha : ∀ g k, a (k * g * k⁻¹) = a g) :
    ∃ μ : ℂ, ∀ k, ∑ g, a g * ρ.character (g * k) = μ * ρ.character k := by
  obtain ⟨μ, hμ⟩ := schur_scalar ρ h a ha
  refine ⟨μ, fun k => ?_⟩
  have h2 := congrArg (fun T : Module.End ℂ V => LinearMap.trace ℂ V (T * ρ k)) hμ
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_mul, smul_mul_assoc, ← map_mul, map_sum, map_smul, one_mul, smul_eq_mul] at h2
  exact h2

theorem sum_of_mul_sum_of (A B : G → ℂ) :
    (∑ g, A g • MonoidAlgebra.of ℂ G g) * (∑ g, B g • MonoidAlgebra.of ℂ G g) =
      ∑ k, (∑ g, A g * B (g⁻¹ * k)) • MonoidAlgebra.of ℂ G k := by
  rw [Finset.sum_mul_sum]
  have key : ∀ g, ∑ h, (A g • MonoidAlgebra.of ℂ G g) * (B h • MonoidAlgebra.of ℂ G h) =
      ∑ k, (A g * B (g⁻¹ * k)) • MonoidAlgebra.of ℂ G k := by
    intro g
    refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun h => ?_)
    simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, smul_mul_smul_comm, ← map_mul]
  rw [Finset.sum_congr rfl (fun g _ => key g), Finset.sum_comm]
  simp_rw [Finset.sum_smul]

end

theorem centralIdem_mul {G V W : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (h : ∀ U : Submodule ℂ W, (∀ g, ∀ x ∈ U, σ g x ∈ U) → U = ⊥ ∨ U = ⊤) :
    ∃ μ : ℂ, μ * (Module.finrank ℂ W : ℂ) = ∑ g, ρ.character g⁻¹ * σ.character g ∧
      centralIdem ρ * centralIdem σ =
        ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * μ) • centralIdem σ := by
  have ha : ∀ g k : G, ρ.character (k * g * k⁻¹)⁻¹ = ρ.character g⁻¹ := by
    intro g k
    simpa [mul_assoc] using ρ.char_conj g⁻¹ k
  obtain ⟨μ, hconv⟩ := conv_char σ h (fun g => ρ.character g⁻¹) ha
  have hone : σ.character 1 = (Module.finrank ℂ W : ℂ) := by
    first
      | exact σ.char_one
      | (unfold Representation.character; simp)
  refine ⟨μ, ?_, ?_⟩
  · have h1 := hconv 1
    simp only [mul_one, hone] at h1
    exact h1.symm
  · unfold centralIdem
    rw [sum_of_mul_sum_of, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [smul_smul]
    congr 1
    have hcm : ∀ g : G, σ.character (k⁻¹ * g) = σ.character (g * k⁻¹) := fun g => by
      simpa [mul_assoc] using (σ.char_conj (k⁻¹ * g) g).symm
    have e1 : ∀ g : G, ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * ρ.character g⁻¹) *
        ((Module.finrank ℂ W : ℂ) / (Fintype.card G : ℂ) * σ.character (g⁻¹ * k)⁻¹) =
        ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * ((Module.finrank ℂ W : ℂ) / (Fintype.card G : ℂ))) *
        (ρ.character g⁻¹ * σ.character (g * k⁻¹)) := by
      intro g
      rw [mul_inv_rev, inv_inv, hcm]
      ring
    calc _ = ∑ g, ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) *
            ((Module.finrank ℂ W : ℂ) / (Fintype.card G : ℂ))) *
            (ρ.character g⁻¹ * σ.character (g * k⁻¹)) := Finset.sum_congr rfl (fun g _ => e1 g)
      _ = _ := by
        rw [← Finset.mul_sum, hconv k⁻¹]
        ring

theorem centralIdem_comm_of {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (k : G) :
    centralIdem ρ * MonoidAlgebra.of ℂ G k = MonoidAlgebra.of ℂ G k * centralIdem ρ := by
  have hc : ∀ h : G, ρ.character (k⁻¹ * (h * k)) = ρ.character h := by
    first
      | exact fun h => by simpa [mul_assoc] using ρ.char_conj h k⁻¹
      | (intro h; unfold Representation.character; done)
  unfold centralIdem
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Fintype.sum_equiv (MulAut.conj k⁻¹).toEquiv _ _ (fun g => ?_)
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv, smul_mul_assoc,
    mul_smul_comm, ← map_mul, mul_inv_rev, mul_assoc, hc, mul_inv_cancel_left]

theorem central_idempotent_holds : CentralIdempotent := by
  intro G V _ _ _ _ _ _ ρ h
  constructor
  · obtain ⟨μ, h1, h2⟩ := centralIdem_mul ρ ρ h
    have hirr : ρ.IsIrreducible := isIrreducible_of ρ h
    have hc0 : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have : Invertible (Nat.card G : ℂ) :=
      invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact hc0)
    have horth := Representation.char_orthonormal ρ ρ
    rw [if_pos ⟨Representation.Equiv.refl ρ⟩, Nat.card_eq_fintype_card] at horth
    have h3 : ∑ g, ρ.character g⁻¹ * ρ.character g = (Fintype.card G : ℂ) := by
      have : ∑ g, ρ.character g⁻¹ * ρ.character g = ∑ g, ρ.character g * ρ.character g⁻¹ :=
        Finset.sum_congr rfl fun g _ => mul_comm _ _
      rw [this]
      field_simp at horth
      simpa using horth
    rw [h2]
    have h4 : (Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * μ = 1 := by
      rw [h3] at h1
      field_simp
      rw [mul_comm]; exact h1
    rw [h4, one_smul]
  · intro x
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [mul_add, add_mul, ha, hb]
    | single g c =>
      have : MonoidAlgebra.single g c = c • MonoidAlgebra.of ℂ G g := by
        simp [MonoidAlgebra.of_apply]
      rw [this, mul_smul_comm, smul_mul_assoc, centralIdem_comm_of]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.IRRCycleProbPrime
section
open Equiv Equiv.Perm Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem card_disjoint_perm {α : Type} [Fintype α] [DecidableEq α] (c : Perm α)
    (B : Finset (Perm α)) (hB : ∀ τ, τ ∈ B ↔ c.Disjoint τ) :
    B.card = (Fintype.card α - c.support.card).factorial := by
  classical
  have hB' : B = Finset.univ.filter (fun τ => c.Disjoint τ) := by
    ext τ
    simp [hB]
  rw [hB', ← Fintype.card_subtype]

  have e : {τ : Perm α // c.Disjoint τ} ≃ {f : Perm α // ∀ a, ¬ (a ∉ c.support) → f a = a} :=
    Equiv.subtypeEquivRight fun τ => by
      constructor
      · intro h a ha
        rcases h a with h1 | h1
        · exact absurd (Perm.mem_support.1 (not_not.1 ha)) (not_not.2 h1)
        · exact h1
      · intro h a
        by_cases ha : a ∈ c.support
        · exact Or.inr (h a (not_not.2 ha))
        · left
          by_contra h1
          exact ha (Perm.mem_support.2 h1)
  rw [Fintype.card_congr (e.trans (Equiv.Perm.subtypeEquivSubtypePerm _).symm), Fintype.card_perm,
    Fintype.card_subtype_compl, Fintype.card_coe]

theorem prime_cycle_perm_count (N p : ℕ) (hp : p.Prime) (hpN : p ≤ N) (hN2 : N < 2 * p)
    (S : Finset (Perm (Fin N))) (hS : ∀ σ, σ ∈ S ↔ p ∈ σ.cycleType) :
    p * S.card = N.factorial := by
  classical
  have hp2 : 2 ≤ p := hp.two_le
  obtain ⟨C, hCdef⟩ : ∃ C : Finset (Perm (Fin N)), C = Finset.univ.filter (fun g => g.cycleType = {p}) :=
    ⟨_, rfl⟩
  have hmemT : ∀ σ : Perm (Fin N), p ∈ σ.cycleType ↔ ∃ c ∈ σ.cycleFactorsFinset, c.support.card = p := by
    intro σ
    rw [Equiv.Perm.cycleType_def, Multiset.mem_map]
    simp only [Finset.mem_val, Function.comp_apply]

  have hCsupp : ∀ c ∈ C, c.IsCycle ∧ c.support.card = p := by
    intro c hc
    rw [hCdef, Finset.mem_filter] at hc
    have h2 : c.support.card = p := by rw [← Equiv.Perm.sum_cycleType, hc.2, Multiset.sum_singleton]
    refine ⟨?_, h2⟩
    rw [← Equiv.Perm.card_cycleType_eq_one, hc.2, Multiset.card_singleton]
  have hmemC : ∀ c : Perm (Fin N), c.IsCycle → c.support.card = p → c ∈ C := by
    intro c hc hs
    rw [hCdef, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [hc.cycleType, hs]⟩

  have hSU : S = C.biUnion (fun c => S.filter (fun σ => c ∈ σ.cycleFactorsFinset)) := by
    ext σ
    constructor
    · intro hσ
      obtain ⟨c, hc, hcp⟩ := (hmemT σ).1 ((hS σ).1 hσ)
      exact Finset.mem_biUnion.2 ⟨c, hmemC c (Equiv.Perm.mem_cycleFactorsFinset_iff.1 hc).1 hcp,
        Finset.mem_filter.2 ⟨hσ, hc⟩⟩
    · intro h
      obtain ⟨c, _, hσ⟩ := Finset.mem_biUnion.1 h
      exact (Finset.mem_filter.1 hσ).1

  have hdisj : (C : Set (Perm (Fin N))).PairwiseDisjoint
      (fun c => S.filter (fun σ => c ∈ σ.cycleFactorsFinset)) := by
    intro c hc c' hc' hne
    show _root_.Disjoint _ _
    rw [Finset.disjoint_left]
    intro σ h1 h2
    have hd := Equiv.Perm.cycleFactorsFinset_pairwise_disjoint σ
      (Finset.mem_coe.2 (Finset.mem_filter.1 h1).2) (Finset.mem_coe.2 (Finset.mem_filter.1 h2).2) hne
    have hcard := Finset.card_le_univ (c.support ∪ c'.support)
    rw [Finset.card_union_of_disjoint hd.disjoint_support, (hCsupp c (Finset.mem_coe.1 hc)).2,
      (hCsupp c' (Finset.mem_coe.1 hc')).2, Fintype.card_fin] at hcard
    omega

  have hF : ∀ c ∈ C, (S.filter (fun σ => c ∈ σ.cycleFactorsFinset)).card = (N - p).factorial := by
    intro c hc
    obtain ⟨hcyc, hcs⟩ := hCsupp c hc
    have hB := card_disjoint_perm c (Finset.univ.filter fun τ => c.Disjoint τ) (fun τ => by simp)
    rw [Fintype.card_fin, hcs] at hB
    rw [← hB]
    symm
    refine Finset.card_bij (fun τ _ => c * τ) ?_ ?_ ?_
    · intro τ hτ
      have hd : c.Disjoint τ := (Finset.mem_filter.1 hτ).2
      have hmem : c ∈ (c * τ).cycleFactorsFinset := by
        rw [hd.cycleFactorsFinset_mul_eq_union, hcyc.cycleFactorsFinset_eq_singleton]
        exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
      exact Finset.mem_filter.2 ⟨(hS _).2 ((hmemT _).2 ⟨c, hmem, hcs⟩), hmem⟩
    · intro τ _ τ' _ h
      exact mul_left_cancel h
    · intro σ hσ
      have hmem := (Finset.mem_filter.1 hσ).2
      have hd : c.Disjoint (σ * c⁻¹) := (Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hmem).symm
      refine ⟨σ * c⁻¹, Finset.mem_filter.2 ⟨Finset.mem_univ _, hd⟩, ?_⟩
      rw [hd.commute.eq, inv_mul_cancel_right]
  have hcard : S.card = C.card * (N - p).factorial := by
    rw [hSU, Finset.card_biUnion hdisj, Finset.sum_congr rfl hF, Finset.sum_const, smul_eq_mul]
  have hC : C.card = (p - 1).factorial * N.choose p := by
    have h := Equiv.Perm.card_of_cycleType_singleton (α := Fin N) hp2 (by rw [Fintype.card_fin]; exact hpN)
    rw [Fintype.card_fin] at h
    rw [hCdef]
    exact h
  rw [hcard, hC]
  calc p * ((p - 1).factorial * N.choose p * (N - p).factorial)
      = N.choose p * (p * (p - 1).factorial) * (N - p).factorial := by ring
    _ = N.factorial := by
      rw [Nat.mul_factorial_pred hp.ne_zero, Nat.choose_mul_factorial_mul_factorial hpN]

theorem prime_cycle_probability : CycleProbPrime := by
  intro N p hp hpN hN2
  exact prime_cycle_perm_count N p hp hpN hN2 _ (fun σ => by simp)

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.IRRCycleTypeProb
section
open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

private def typeMultiset (s : Finset ℕ) (n : ℕ → ℕ) : Multiset ℕ :=
  ∑ d ∈ s, Multiset.replicate (n d) d

private theorem typeMultiset_count (s : Finset ℕ) (n : ℕ → ℕ) (a : ℕ) :
    (typeMultiset s n).count a = if a ∈ s then n a else 0 := by
  classical
  unfold typeMultiset
  rw [Multiset.count_sum']
  simp [Multiset.count_replicate]

private theorem typeMultiset_sum (s : Finset ℕ) (n : ℕ → ℕ) :
    (typeMultiset s n).sum = ∑ d ∈ s, d * n d := by
  classical
  unfold typeMultiset
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.sum_add, ih, Multiset.sum_replicate,
      smul_eq_mul, mul_comm]

private theorem typeMultiset_prod (s : Finset ℕ) (n : ℕ → ℕ) :
    (typeMultiset s n).prod = ∏ d ∈ s, d ^ n d := by
  classical
  unfold typeMultiset
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Multiset.prod_add, ih, Multiset.prod_replicate]

private theorem typeMultiset_fact (s : Finset ℕ) (n : ℕ → ℕ) :
    ∏ a ∈ (typeMultiset s n).toFinset, ((typeMultiset s n).count a).factorial =
      ∏ d ∈ s, (n d).factorial := by
  classical
  rw [Finset.prod_subset (s₁ := (typeMultiset s n).toFinset) (s₂ := s) ?_ ?_]
  · refine Finset.prod_congr rfl fun d hd => ?_
    rw [typeMultiset_count, if_pos hd]
  · intro a ha
    rw [Multiset.mem_toFinset, ← Multiset.count_pos, typeMultiset_count] at ha
    by_contra h
    rw [if_neg h] at ha
    exact lt_irrefl 0 ha
  · intro a _ ha
    rw [Multiset.mem_toFinset, ← Multiset.count_eq_zero] at ha
    rw [ha, Nat.factorial_zero]

theorem cycle_type_probability : CycleTypeProb := by
  unfold CycleTypeProb
  intro N n hN
  classical
  have hsumle : (typeMultiset (Finset.Icc 2 N) n).sum ≤ N := by
    rw [typeMultiset_sum]
    exact le_trans (Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc_left (by norm_num : 1 ≤ 2))) hN.le
  have htwo : ∀ a ∈ typeMultiset (Finset.Icc 2 N) n, 2 ≤ a := by
    intro a ha
    rw [← Multiset.count_pos, typeMultiset_count] at ha
    split_ifs at ha with h
    · exact (Finset.mem_Icc.1 h).1
    · exact absurd ha (lt_irrefl 0)
  have key := Equiv.Perm.card_of_cycleType_mul_eq (Fin N) (typeMultiset (Finset.Icc 2 N) n)
  rw [if_pos ⟨by simpa using hsumle, htwo⟩, Fintype.card_fin, typeMultiset_prod, typeMultiset_fact] at key
  have hprod : ∏ d ∈ Finset.Icc 1 N, (d ^ n d * (n d).factorial) =
      (N - (typeMultiset (Finset.Icc 2 N) n).sum).factorial * (∏ d ∈ Finset.Icc 2 N, d ^ n d) *
        ∏ d ∈ Finset.Icc 2 N, (n d).factorial := by
    rw [typeMultiset_sum]
    rcases Nat.eq_zero_or_pos N with rfl | hN1
    · simp
    · have hI : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := (Finset.insert_Icc_add_one_left_eq_Icc hN1).symm
      rw [hI, Finset.prod_insert (by simp)]
      rw [hI, Finset.sum_insert (by simp)] at hN
      have h1 : N - ∑ d ∈ Finset.Icc 2 N, d * n d = n 1 := by omega
      rw [h1, one_pow, one_mul, Finset.prod_mul_distrib]
      ring
  rw [hprod]
  convert key using 3
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    ext a
    rw [typeMultiset_count]
    split_ifs with ha
    · exact h a ha
    · rw [Multiset.count_eq_zero]
      intro hmem
      apply ha
      rw [Finset.mem_Icc]
      refine ⟨Equiv.Perm.two_le_of_mem_cycleType hmem, ?_⟩
      calc a ≤ σ.support.card := Equiv.Perm.le_card_support_of_mem_cycleType hmem
        _ ≤ Fintype.card (Fin N) := Finset.card_le_univ _
        _ = N := Fintype.card_fin N
  · intro h d hd
    rw [h, typeMultiset_count, if_pos hd]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.IRRDivisorDegreeSubSum
section
open Polynomial UniqueFactorizationMonoid

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open Formalism.GaloisIrreducibility (IsSubSum)

theorem exists_le_map_eq {α β : Type*} [DecidableEq β] (f : α → β) (t : Multiset α) :
    ∀ s : Multiset β, s ≤ t.map f → ∃ u ≤ t, u.map f = s := by
  first | exact Bl.general_b_fact_right_rest.goal1 .. | (apply Bl.general_b_fact_right_rest.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_rest.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_rest.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right_rest.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_rest.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_right_rest.goal1 α β ‹_› f t s ‹_› | exact @Bl.general_b_fact_right_rest.goal1 α β ‹_› f t s | exact @Bl.general_b_fact_right_rest.goal1 α β ‹_› f t | exact @Bl.general_b_fact_right_rest.goal1 α β ‹_› f | exact @Bl.general_b_fact_right_rest.goal1 α β ‹_› | exact @Bl.general_b_fact_right_rest.goal1 α β | exact @Bl.general_b_fact_right_rest.goal1 α

theorem divisor_degree_subsum : DivisorDegreeSubSum := by
  classical
  intro K _ f a hf
  have hdeg : ∀ t : Multiset K[X], t ≤ normalizedFactors f →
      t.prod.natDegree = (t.map natDegree).sum := by
    intro t ht
    apply natDegree_multiset_prod
    intro h0
    exact zero_notMem_normalizedFactors f (Multiset.mem_of_le ht h0)
  constructor
  · rintro ⟨h, hdvd, rfl⟩
    have hh : h ≠ 0 := fun h0 => hf (by rw [h0] at hdvd; exact zero_dvd_iff.mp hdvd)
    have hle : normalizedFactors h ≤ normalizedFactors f :=
      (dvd_iff_normalizedFactors_le_normalizedFactors hh hf).mp hdvd
    refine ⟨(normalizedFactors h).map natDegree, Multiset.map_le_map hle, ?_⟩
    rw [← hdeg _ hle]
    exact natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (prod_normalizedFactors hh))
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨u, hu, rfl⟩ := exists_le_map_eq natDegree _ s hs
    refine ⟨u.prod, ?_, hdeg u hu⟩
    exact (Multiset.prod_dvd_prod_of_le hu).trans (prod_normalizedFactors hf).dvd

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.IRRJoints
section
open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem cycleProbSum_of_cycleProbPrime : CycleProbPrime → CycleProbSum := by
  unfold CycleProbPrime CycleProbSum
  intro h N
  classical
  have hdisj : ∀ p ∈ (range (N + 1)).filter (fun p => Nat.Prime p ∧ N < 2 * p ∧ p + 3 ≤ N),
      ∀ q ∈ (range (N + 1)).filter (fun p => Nat.Prime p ∧ N < 2 * p ∧ p + 3 ≤ N), p ≠ q →
      Disjoint (univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.cycleType)
        (univ.filter fun σ : Equiv.Perm (Fin N) => q ∈ σ.cycleType) := by
    intro p hp q hq hpq
    simp only [mem_filter, mem_range] at hp hq
    rw [Finset.disjoint_left]
    intro σ h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    have hq' : q ∈ σ.cycleType.erase p := (Multiset.mem_erase_of_ne hpq.symm).2 h2
    have hsum : σ.cycleType.sum ≤ N := by
      rw [Equiv.Perm.sum_cycleType]
      exact (Finset.card_le_univ _).trans (by simp)
    have hsplit : σ.cycleType.sum = p + (σ.cycleType.erase p).sum := by
      conv_lhs => rw [← Multiset.cons_erase h1]
      rw [Multiset.sum_cons]
    have hle : q ≤ (σ.cycleType.erase p).sum := Multiset.le_sum_of_mem hq'
    omega
  have hset : (univ.filter fun σ : Equiv.Perm (Fin N) => ∃ p ∈ σ.cycleType, Nat.Prime p ∧ N < 2 * p ∧ p + 3 ≤ N) =
      ((range (N + 1)).filter fun p => Nat.Prime p ∧ N < 2 * p ∧ p + 3 ≤ N).biUnion
        (fun p => univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.cycleType) := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_range]
    constructor
    · rintro ⟨p, hp, hpr, h2, h3⟩
      exact ⟨p, ⟨by omega, hpr, h2, h3⟩, hp⟩
    · rintro ⟨p, ⟨-, hpr, h2, h3⟩, hp⟩
      exact ⟨p, hp, hpr, h2, h3⟩
  rw [hset, Finset.card_biUnion hdisj, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  simp only [mem_filter, mem_range] at hp
  obtain ⟨hpN, hpr, h2, h3⟩ := hp
  have hk := h N p hpr (by omega) h2
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpr.ne_zero
  rw [eq_div_iff hp0, ← hk]
  push_cast
  ring

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

