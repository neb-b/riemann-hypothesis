module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.CapelliCentralStatement
public import Formalism.FormalDegreeBessel.StatementDS
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.KhwLowKSubRootEqZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CapelliQdetStatement
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

universe u

def CapelliQdetStatement : Prop :=
  (∀ (𝒰 : Type u) [Ring 𝒰] [Algebra ℂ 𝒰] (n : ℕ) (E : Fin n → Fin n → 𝒰) (x : ℂ),
    Capelli.capelliC E x = Formalism.REAL.qdet E x) ∧
  ∀ (n : ℕ) (lam : Fin n → ℝ) (ω : ℂ),
    Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) (ω - ((n : ℂ) - 1) / 2) = ∏ t, (ω + ((thV lam t : ℝ) : ℂ))

def CentralCharStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (V : Submodule ℂ D),
    IsURepOn (UJset ε) σ → IsDerivedOn ε σ D E → IsKIrrHW ε E (lowK ε lam) V →
      (∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) →
      (∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) →
      (∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) → StrictAnti lam →
      GapLap ε lam h → 1 ≤ pOf ε → 1 ≤ qOf ε →
      ∀ (ω : ℂ), ∀ y ∈ genSub E V, Capelli.capelliC E ω y = (∏ t, (ω + ((thV lam t : ℝ) : ℂ))) • y

def GapCentralStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ), GapLap ε lam h →
    GapAtLeast ε lam h ∧ (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h ∧
      8 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) < h ∧
      8 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) * Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℝ)) < h

def HcVStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (V : Submodule ℂ D),
    IsURepOn (UJset ε) σ → IsDerivedOn ε σ D E → IsKIrrHW ε E (lowK ε lam) V →
      (∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) →
      (∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) →
      (∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) → StrictAnti lam →
      GapLap ε lam h → 1 ≤ pOf ε → 1 ≤ qOf ε →
      ∀ (ω : ℂ), ∀ y ∈ V, Capelli.capelliC E ω y = (∏ t, (ω + ((thV lam t : ℝ) : ℂ))) • y

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CasimirTensVd
section
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS Finset

namespace TensK

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem tensV_apply' (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensV E a b f c = E a b (f c) + (if c = a then f b else 0) := by
  by_cases h : c = a <;> simp [tensV, prj, h]

theorem tensVd_apply' (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensVd E a b f c = E a b (f c) - (if c = b then f a else 0) := by
  by_cases h : c = b <;> simp [tensVd, prj, h]

theorem eeV_apply' (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeV E f d = ∑ c, E c d (f c) := by
  simp [eeV, prj, LinearMap.sum_apply]

theorem eeVd_apply' (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeVd E f d = -∑ c, E d c (f c) := by
  simp [eeVd, prj, LinearMap.sum_apply]

theorem casimir_apply' (E : Fin n → Fin n → Module.End ℂ M) (x : M) :
    casimir E x = ∑ a, ∑ b, E a b (E b a x) := by
  simp [casimir, LinearMap.sum_apply, Module.End.mul_apply]

theorem isGlRep_tensV (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) : IsGlRep (tensV E) := by
  intro a b c d
  refine LinearMap.ext fun f => funext fun e => ?_
  have key := LinearMap.congr_fun (hE a b c d) (f e)
  have key' : E a b (E c d (f e)) = E c d (E a b (f e)) +
      ((if b = c then E a d (f e) else 0) - (if d = a then E c b (f e) else 0)) := by
    by_cases h3 : b = c <;> by_cases h4 : d = a <;>
      simp only [h3, h4, if_true, if_false, LinearMap.sub_apply, Module.End.mul_apply,
        LinearMap.zero_apply] at key ⊢ <;> rw [← key] <;> abel
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply,
    tensV_apply', map_add, apply_ite (E a b), apply_ite (E c d), map_zero, key']
  by_cases h3 : b = c <;> by_cases h4 : d = a <;>
    simp only [h3, h4, if_true, if_false, LinearMap.zero_apply, Pi.zero_apply, tensV_apply'] <;>
    split_ifs <;> subst_vars <;> (try simp) <;> first | exact absurd rfl h4 | exact absurd rfl h3 | abel

theorem isGlRep_tensVd (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) : IsGlRep (tensVd E) := by
  intro a b c d
  refine LinearMap.ext fun f => funext fun e => ?_
  have key := LinearMap.congr_fun (hE a b c d) (f e)
  have key' : E a b (E c d (f e)) = E c d (E a b (f e)) +
      ((if b = c then E a d (f e) else 0) - (if d = a then E c b (f e) else 0)) := by
    by_cases h3 : b = c <;> by_cases h4 : d = a <;>
      simp only [h3, h4, if_true, if_false, LinearMap.sub_apply, Module.End.mul_apply,
        LinearMap.zero_apply] at key ⊢ <;> rw [← key] <;> abel
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply,
    tensVd_apply', map_sub, apply_ite (E a b), apply_ite (E c d), map_zero, key']
  by_cases h3 : b = c <;> by_cases h4 : d = a <;>
    simp only [h3, h4, if_true, if_false, LinearMap.zero_apply, Pi.zero_apply, tensVd_apply'] <;>
    split_ifs <;> subst_vars <;> (try simp) <;> first | exact absurd rfl h4 | exact absurd rfl h3 | abel

theorem casimir_tensV' (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) :
    casimir (tensV E) f = (fun c => casimir E (f c)) + (n : ℂ) • f + (2 : ℂ) • eeV E f := by
  funext e
  simp only [casimir_apply', Finset.sum_apply, tensV_apply', map_add (f := _), apply_ite (E _ _), map_zero,
    Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, eeV_apply', if_true, ite_add_zero]
  simp [Finset.sum_ite_eq, Finset.sum_ite_irrel, two_smul]
  rw [Nat.cast_smul_eq_nsmul]
  abel

theorem casimir_tensVd' (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) :
    casimir (tensVd E) f = (fun c => casimir E (f c)) + (n : ℂ) • f + (2 : ℂ) • eeVd E f := by
  funext e
  simp only [casimir_apply', Finset.sum_apply, tensVd_apply', map_sub, apply_ite (E _ _), map_zero,
    Finset.sum_sub_distrib, Pi.add_apply, Pi.smul_apply, eeVd_apply', if_true]
  simp [Finset.sum_ite_eq, Finset.sum_ite_irrel, two_smul]
  rw [Nat.cast_smul_eq_nsmul]
  abel

end TensK

theorem tens_statement (n : ℕ) : TensStatement n := by
  intro M _ _ E hE
  exact ⟨TensK.isGlRep_tensV E hE, TensK.isGlRep_tensVd E hE, TensK.casimir_tensV' E, TensK.casimir_tensVd' E⟩

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CompRevRev
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TwistedDualLemmas

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap.LemK

variable {n : ℕ}

def sg (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε a then 1 else -1

theorem sg_sq (ε : Fin n → Bool) (a : Fin n) : sg ε a * sg ε a = 1 := by
  unfold sg
  split_ifs <;> norm_num

theorem sg_ne (ε : Fin n → Bool) (a : Fin n) : sg ε a ≠ 0 := by
  unfold sg
  split_ifs <;> norm_num

theorem sg_comp (ε : Fin n → Bool) (a : Fin n) : sg (ε ∘ Fin.rev) a = sg ε (Fin.rev a) := rfl

theorem sum_rev {X : Type*} [AddCommMonoid X] (f : Fin n → X) : ∑ a, f (Fin.rev a) = ∑ a, f a :=
  Equiv.sum_comp Fin.revPerm f

section Alg

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

def twE (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) : Fin n → Fin n → Module.End ℂ M :=
  fun a b => (-(sg ε (Fin.rev a) * sg ε (Fin.rev b))) • E (Fin.rev b) (Fin.rev a)

theorem twE_apply (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (v : M) :
    twE ε E a b v = (-(sg ε (Fin.rev a) * sg ε (Fin.rev b))) • E (Fin.rev b) (Fin.rev a) v := rfl

theorem comp_rev_rev (ε : Fin n → Bool) : (ε ∘ Fin.rev) ∘ Fin.rev = ε := by
  funext a
  simp [Fin.rev_rev]

theorem twE_twE (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) :
    twE (ε ∘ Fin.rev) (twE ε E) = E := by
  funext a b
  simp only [twE, sg_comp, Fin.rev_rev, smul_smul]
  convert one_smul ℂ (E a b) using 2
  linear_combination (sg ε b * sg ε b) * sg_sq ε a + sg_sq ε b

theorem twE_gl {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) :
    IsGlRep (twE ε E) := by
  intro a b c d
  have h := hE (Fin.rev b) (Fin.rev a) (Fin.rev d) (Fin.rev c)
  rw [sub_eq_iff_eq_add] at h
  simp only [twE, smul_mul_smul_comm, h, Fin.rev_inj]
  simp only [@eq_comm (Fin n) b c, @eq_comm (Fin n) d a]
  split_ifs <;> subst_vars <;> simp only [sg] <;> split_ifs <;> module

theorem casimir_twE (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) :
    casimir (twE ε E) = casimir E := by
  unfold casimir
  simp only [twE, smul_mul_smul_comm]
  have hs : ∀ a b : Fin n,
      (-(sg ε (Fin.rev a) * sg ε (Fin.rev b)) * -(sg ε (Fin.rev b) * sg ε (Fin.rev a))) = 1 := by
    intro a b
    linear_combination (sg ε (Fin.rev b) * sg ε (Fin.rev b)) * sg_sq ε (Fin.rev a) + sg_sq ε (Fin.rev b)
  simp only [hs, one_smul]
  have h1 : ∀ a : Fin n, ∑ b, E (Fin.rev b) (Fin.rev a) * E (Fin.rev a) (Fin.rev b) =
      ∑ b, E b (Fin.rev a) * E (Fin.rev a) b :=
    fun a => sum_rev (fun b => E b (Fin.rev a) * E (Fin.rev a) b)
  simp only [h1]
  exact (sum_rev (fun a => ∑ b, E b a * E a b)).trans Finset.sum_comm

theorem kst_tw {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {S : Submodule ℂ M}
    (h : IsKStableSub ε E S) : IsKStableSub (ε ∘ Fin.rev) (twE ε E) S := by
  intro a b hab v hv
  rw [twE_apply]
  exact S.smul_mem _ (h _ _ hab.symm v hv)

theorem kst_tw_iff {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {S : Submodule ℂ M} :
    IsKStableSub (ε ∘ Fin.rev) (twE ε E) S ↔ IsKStableSub ε E S := by
  refine ⟨fun h => ?_, kst_tw⟩
  have h' := kst_tw (ε := ε ∘ Fin.rev) h
  rwa [twE_twE, comp_rev_rev] at h'

theorem khw_tw {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {μ : Fin n → ℝ} {v : M}
    (h : IsKHWVec ε E μ v) : IsKHWVec (ε ∘ Fin.rev) (twE ε E) (fun a => -μ (Fin.rev a)) v := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · rw [twE_apply, h1, sg_sq, smul_smul]
    congr 1
    push_cast
    ring
  · rw [twE_apply, h2 _ _ (Fin.rev_lt_rev.2 hab) he.symm, smul_zero]

theorem genSub_tw (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (S : Submodule ℂ M) :
    genSub (twE ε E) S = genSub E S := by
  unfold genSub
  congr 1
  ext T
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun _ => ⟨fun hT a b v hv => ?_, fun hT a b v hv => ?_⟩
  · rw [← twE_twE ε E, twE_apply]
    exact T.smul_mem _ (hT _ _ v hv)
  · rw [twE_apply]
    exact T.smul_mem _ (hT _ _ v hv)

theorem kirr_tw {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {Λ : Fin n → ℝ}
    {S : Submodule ℂ M} (h : IsKIrrHW ε E Λ S) :
    IsKIrrHW (ε ∘ Fin.rev) (twE ε E) (fun a => -Λ (Fin.rev a)) S := by
  obtain ⟨h1, h2, h3, w, hw, hw0, hw1⟩ := h
  exact ⟨h1, kst_tw h2, fun S' hS' hk => h3 S' hS' (kst_tw_iff.1 hk), w, hw, hw0, khw_tw hw1⟩

end Alg

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TwistedDualLemmas
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ConeNorm
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

theorem cone_norm_dot_root {n : ℕ} (l : Fin n → ℝ) (a b : Fin n) (c : ℝ) :
    ∑ i, l i * (c • root a b) i = c * (l a - l b) := by
  unfold root
  simp [Pi.single_apply, mul_sub, Finset.sum_sub_distrib]
  try ring

theorem cone_norm_dot_nonneg {n : ℕ} (l β : Fin n → ℝ) (hl : Antitone l) (hβ : InRootCone β) :
    0 ≤ dot l β := by
  unfold dot
  obtain ⟨m, rfl⟩ := hβ
  have hsw : ∑ i, l i * (∑ a, ∑ b, if a < b then (m a b : ℝ) • root a b else 0) i
      = ∑ a, ∑ b, ∑ i, l i * ((if a < b then (m a b : ℝ) • root a b else 0) i) := by
    simp only [Finset.sum_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
  rw [hsw]
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  split_ifs with hab
  · rw [cone_norm_dot_root]
    exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hl hab.le))
  · simp

theorem cone_norm_eq_zero {n : ℕ} (β : Fin n → ℝ) (h : nsq β ≤ 0) : β = 0 := by
  unfold nsq dot at h
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ β i * β i := fun i _ => mul_self_nonneg _
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp (le_antisymm h (Finset.sum_nonneg hnn))
  funext i
  exact mul_self_eq_zero.mp (h0 i (Finset.mem_univ _))

theorem cone_norm (n : ℕ) : ConeNormStatement n := by
  intro lam β hl hβ h
  apply cone_norm_eq_zero
  have hd := cone_norm_dot_nonneg lam β hl hβ
  have hexp : nsq (lam + β) = nsq lam + 2 * dot lam β + nsq β := by
    unfold nsq dot
    simp only [Pi.add_apply]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  linarith

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CoordinateEqPartialSumDifference
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem root_cone_functional_natural (ℓ : (Fin n → ℝ) →ₗ[ℝ] ℝ) (hℓ : ∀ a b : Fin n, a < b → ∃ N : ℕ, ℓ (root a b) = N)
    {β : Fin n → ℝ} (hβ : InRootCone β) : ∃ N : ℕ, ℓ β = N := by
  classical
  obtain ⟨m, rfl⟩ := hβ
  choose! N hN using hℓ
  refine ⟨∑ a, ∑ b, if a < b then m a b * N a b else 0, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Nat.cast_sum, Nat.cast_ite, Nat.cast_mul, Nat.cast_zero]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rw [map_smul, hN a b h, smul_eq_mul]
  · simp

def weightPowerSumFunctional (k : ℕ) : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ a ∈ univ.filter (fun a : Fin n => a.val < k), LinearMap.proj a

theorem k3vdPs_apply (k : ℕ) (μ : Fin n → ℝ) : weightPowerSumFunctional k μ = kirrPs k μ := by
  simp [weightPowerSumFunctional, kirrPs, LinearMap.sum_apply]

theorem partial_sum_of_basis_vector (k : ℕ) (a : Fin n) :
    kirrPs k (Pi.single a (1 : ℝ)) = if a.val < k then 1 else 0 := by
  simp [kirrPs, Pi.single_apply, Finset.sum_ite_eq', Finset.mem_filter]

theorem partial_sum_of_root (k : ℕ) (a b : Fin n) :
    kirrPs k (root a b) = (if a.val < k then 1 else 0) - (if b.val < k then 1 else 0) := by
  rw [← partial_sum_of_basis_vector, ← partial_sum_of_basis_vector]
  simp [kirrPs, root, Finset.sum_sub_distrib]

theorem root_cone_partial_sum_natural {β : Fin n → ℝ} (hβ : InRootCone β) (k : ℕ) : ∃ N : ℕ, kirrPs k β = N := by
  have hℓ : ∀ a b : Fin n, a < b → ∃ N : ℕ, weightPowerSumFunctional k (root a b) = N := by
    intro a b hab
    have hv := Fin.lt_def.1 hab
    rw [k3vdPs_apply, partial_sum_of_root]
    by_cases ha : a.val < k <;> by_cases hb : b.val < k
    · exact ⟨0, by simp [ha, hb]⟩
    · exact ⟨1, by simp [ha, hb]⟩
    · omega
    · exact ⟨0, by simp [ha, hb]⟩
  obtain ⟨N, hN⟩ := root_cone_functional_natural (weightPowerSumFunctional k) hℓ hβ
  exact ⟨N, by rw [← k3vdPs_apply]; exact hN⟩

def weightHeightFunctional : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ c : Fin n, ((n : ℝ) - (c : ℕ)) • LinearMap.proj c

theorem k3vdHt_root (a b : Fin n) : weightHeightFunctional (root a b) = ((b : ℕ) : ℝ) - (a : ℕ) := by
  simp only [weightHeightFunctional, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    root, Pi.sub_apply, Pi.single_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem root_cone_height_natural {β : Fin n → ℝ} (hβ : InRootCone β) : ∃ N : ℕ, weightHeightFunctional β = N := by
  have hℓ : ∀ a b : Fin n, a < b → ∃ N : ℕ, weightHeightFunctional (root a b) = N := by
    intro a b hab
    refine ⟨b.val - a.val, ?_⟩
    rw [k3vdHt_root, Nat.cast_sub (le_of_lt (Fin.lt_def.1 hab))]
  exact root_cone_functional_natural weightHeightFunctional hℓ hβ

theorem coordinate_eq_partial_sum_difference (γ : Fin n → ℝ) (a : Fin n) :
    γ a = kirrPs ((a : ℕ) + 1) γ - kirrPs (a : ℕ) γ := by
  unfold kirrPs
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib, Finset.sum_eq_single a]
  · simp
  · intro c _ hc
    have : c.val ≠ a.val := fun h => hc (Fin.ext h)
    by_cases h1 : c.val < a.val
    · simp [h1, show c.val < a.val + 1 by omega]
    · simp [h1, show ¬ c.val < a.val + 1 by omega]
  · simp

theorem coordinate_difference_le_two (γ : Fin n → ℝ) (hγ : ∀ k, -1 ≤ kirrPs k γ ∧ kirrPs k γ ≤ 0) (a b : Fin n) :
    |γ a - γ b| ≤ 2 := by
  have h1 := coordinate_eq_partial_sum_difference γ a
  have h2 := coordinate_eq_partial_sum_difference γ b
  have a1 := hγ ((a : ℕ) + 1)
  have a0 := hγ (a : ℕ)
  have b1 := hγ ((b : ℕ) + 1)
  have b0 := hγ (b : ℕ)
  rw [abs_le]
  constructor <;> linarith [a1.1, a1.2, a0.1, a0.2, b1.1, b1.2, b0.1, b0.2]

theorem strictAnti_of_consecutive_lt {f : Fin n → ℝ} (h : ∀ a b : Fin n, b.val = a.val + 1 → f b < f a) :
    StrictAnti f := by
  intro a b hab
  have key : ∀ d : ℕ, ∀ b : Fin n, b.val = a.val + d + 1 → f b < f a := by
    intro d
    induction d with
    | zero => intro b hb; exact h a b (by omega)
    | succ d ih =>
      intro b hb
      have hc : a.val + d + 1 < n := by have := b.isLt; omega
      exact lt_trans (h ⟨a.val + d + 1, hc⟩ b (by show b.val = a.val + d + 1 + 1; omega))
        (ih ⟨a.val + d + 1, hc⟩ rfl)
  exact key (b.val - a.val - 1) b (by have := Fin.lt_def.1 hab; omega)

theorem rho_consecutive_compact_pair (ε : Fin n → Bool) (a b : Fin n) (hb : b.val = a.val + 1) (he : ε a = ε b) :
    rhoC ε a = rhoC ε b + 1 ∧ rhoN ε a = rhoN ε b := by
  have hab : ∀ c : Fin n, a < c ↔ c = b ∨ b < c := by
    intro c; rw [Fin.lt_def, Fin.lt_def, Fin.ext_iff]; omega
  have hba : ∀ c : Fin n, c < b ↔ c = a ∨ c < a := by
    intro c; rw [Fin.lt_def, Fin.lt_def, Fin.ext_iff]; omega
  have e1 : (univ.filter fun c => a < c ∧ ε c = ε a) =
      insert b (univ.filter fun c => b < c ∧ ε c = ε b) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, mem_insert, hab c, he]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h2⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨Or.inl rfl, rfl⟩
      · exact ⟨Or.inr h1, h2⟩
  have e2 : (univ.filter fun c => c < b ∧ ε c = ε b) =
      insert a (univ.filter fun c => c < a ∧ ε c = ε a) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, mem_insert, hba c, he]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h2⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨Or.inl rfl, he⟩
      · exact ⟨Or.inr h1, h2⟩
  have e3 : (univ.filter fun c => a < c ∧ ε c ≠ ε a) = (univ.filter fun c => b < c ∧ ε c ≠ ε b) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, hab c, he]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd (h1 ▸ rfl) h2
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inr h1, h2⟩
  have e4 : (univ.filter fun c => c < b ∧ ε c ≠ ε b) = (univ.filter fun c => c < a ∧ ε c ≠ ε a) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, hba c, he]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd (h1 ▸ he) h2
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inr h1, h2⟩
  have nb : b ∉ univ.filter fun c => b < c ∧ ε c = ε b := by simp
  have na : a ∉ univ.filter fun c => c < a ∧ ε c = ε a := by simp
  refine ⟨?_, ?_⟩
  · unfold rhoC
    rw [e1, e2, card_insert_of_notMem nb, card_insert_of_notMem na]
    push_cast
    ring
  · unfold rhoN
    rw [e3, e4]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

