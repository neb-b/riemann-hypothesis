module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0379
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0368
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1089

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignAntisymmetric
section
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RealMult.Short

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open Formalism.REAL (dot nsq)

variable {n : ℕ}

theorem dL_add (u v w : Fin n → ℝ) : dot (u + v) w = dot u w + dot v w := by
  simp [dot, add_mul, sum_add_distrib]

theorem dL_sub (u v w : Fin n → ℝ) : dot (u - v) w = dot u w - dot v w := by
  simp [dot, sub_mul, sum_sub_distrib]

theorem dL_smul (c : ℝ) (u w : Fin n → ℝ) : dot (c • u) w = c * dot u w := by
  simp [dot, mul_sum, mul_assoc]

theorem d_comm (u v : Fin n → ℝ) : dot u v = dot v u := by
  simp [dot, mul_comm]

theorem dR_add (u v w : Fin n → ℝ) : dot u (v + w) = dot u v + dot u w := by
  simp [dot, mul_add, sum_add_distrib]

theorem dR_sub (u v w : Fin n → ℝ) : dot u (v - w) = dot u v - dot u w := by
  simp [dot, mul_sub, sum_sub_distrib]

theorem dR_smul (c : ℝ) (u w : Fin n → ℝ) : dot u (c • w) = c * dot u w := by
  rw [d_comm, dL_smul, d_comm]

theorem d_perm (u v : Fin n → ℝ) (w : Equiv.Perm (Fin n)) : dot (u ∘ w) (v ∘ w) = dot u v := by
  simpa [dot] using Equiv.sum_comp w (fun a => u a * v a)

theorem d_self_nonneg (u : Fin n → ℝ) : 0 ≤ dot u u :=
  sum_nonneg fun a _ => mul_self_nonneg _

theorem rho_sub (a b : Fin n) : rhoV n a - rhoV n b = (b : ℕ) - (a : ℕ) := by
  simp only [rhoV]; ring

theorem rho_anti : StrictAnti (rhoV n) := by
  intro a b h
  have h' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast h
  have := rho_sub a b
  linarith

theorem rearr (u : Fin n → ℝ) (hu : Antitone u) (σ : Equiv.Perm (Fin n)) :
    dot u (rhoV n ∘ σ) ≤ dot u (rhoV n) :=
  Monovary.sum_mul_comp_perm_le_sum_mul (hu.monovary rho_anti.antitone)

def s0 (a b : Fin n) : ℝ := if a < b then 1 else if b < a then -1 else 0

def mB (B : Finset (Fin n × Fin n)) (a b : Fin n) : ℝ := if (a, b) ∈ B then 1 else 0

def sg (B : Finset (Fin n × Fin n)) (a b : Fin n) : ℝ := s0 a b - 2 * mB B a b + 2 * mB B b a

theorem sign_antisymmetric_alt (a b : Fin n) : s0 b a = -s0 a b := by
  unfold s0
  rcases lt_trichotomy a b with h | h | h
  · simp [h, asymm h]
  · simp [h]
  · simp [h, asymm h]

theorem sg_anti (B : Finset (Fin n × Fin n)) (a b : Fin n) : sg B b a = -sg B a b := by
  unfold sg; rw [sign_antisymmetric_alt a b]; ring

theorem sign_self_eq_zero (a : Fin n) : s0 a a = 0 := by simp [s0]

theorem sum_sign_eq_two_rho (a : Fin n) : ∑ b, s0 a b = 2 * rhoV n a := by
  have h : ∀ b, s0 a b = (if a < b then (1 : ℝ) else 0) - (if b < a then (1 : ℝ) else 0) := by
    intro b
    unfold s0
    rcases lt_trichotomy a b with h | h | h
    · simp [h, asymm h]
    · simp [h]
    · simp [h, asymm h]
  simp only [h, sum_sub_distrib, sum_boole]
  rw [Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio]
  have ha := a.2
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  simp [rhoV]
  ring

theorem sum_row_count (B : Finset (Fin n × Fin n)) (a : Fin n) :
    ∑ b, mB B a b = ((B.filter fun p => p.1 = a).card : ℝ) := by
  have : B.filter (fun p => p.1 = a) = (univ.filter fun b => (a, b) ∈ B).image (fun b => (a, b)) := by
    ext ⟨x, y⟩
    simp only [mem_filter, mem_image, mem_univ, true_and, Prod.mk.injEq]
    constructor
    · rintro ⟨h, rfl⟩; exact ⟨y, h, rfl, rfl⟩
    · rintro ⟨c, h, rfl, rfl⟩; exact ⟨h, rfl⟩
  rw [this, card_image_of_injective _ (fun x y h => (Prod.mk.inj h).2)]
  simp [mB]

theorem sum_column_count (B : Finset (Fin n × Fin n)) (a : Fin n) :
    ∑ b, mB B b a = ((B.filter fun p => p.2 = a).card : ℝ) := by
  have : B.filter (fun p => p.2 = a) = (univ.filter fun b => (b, a) ∈ B).image (fun b => (b, a)) := by
    ext ⟨x, y⟩
    simp only [mem_filter, mem_image, mem_univ, true_and, Prod.mk.injEq]
    constructor
    · rintro ⟨h, rfl⟩; exact ⟨x, h, rfl, rfl⟩
    · rintro ⟨c, h, rfl, rfl⟩; exact ⟨h, rfl⟩
  rw [this, card_image_of_injective _ (fun x y h => (Prod.mk.inj h).1)]
  simp [mB]

theorem sum_sg (B : Finset (Fin n × Fin n)) (a : Fin n) :
    ∑ b, sg B a b = 2 * (rhoV n a - wtB B a) := by
  simp only [sg, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_sign_eq_two_rho, sum_row_count, sum_column_count, wtB]
  ring

theorem sg_val (B : Finset (Fin n × Fin n)) (hB : ∀ p ∈ B, p.1 < p.2) {a b : Fin n} (hab : a ≠ b) :
    sg B a b = 1 ∨ sg B a b = -1 := by
  have key : ∀ a b : Fin n, a < b → sg B a b = 1 ∨ sg B a b = -1 := by
    intro a b h
    have h1 : (b, a) ∉ B := fun hm => asymm h (hB _ hm)
    by_cases hm : (a, b) ∈ B
    · right; simp [sg, s0, mB, h, h1, hm]; norm_num
    · left; simp [sg, s0, mB, h, h1, hm]
  rcases lt_or_gt_of_ne hab with h | h
  · exact key a b h
  · rw [sg_anti B b a]
    rcases key b a h with h' | h' <;> simp [h']

end GlobalTheory.CompanionTheory.RealMult.Short

namespace GlobalTheory.CompanionTheory.RealMult

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open Formalism.REAL (dot nsq)
open Short

end GlobalTheory.CompanionTheory.RealMult
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleLoweringPowMemIdeal
section
set_option maxSynthPendingDepth 1

noncomputable section

open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

variable {n : ℕ}

def adL (F u : U n) : U n := F * u - u * F

theorem adL_zero (F : U n) : adL F 0 = 0 := by simp [adL]

theorem adL_sub (F u v : U n) : adL F (u - v) = adL F u - adL F v := by
  simp only [adL, mul_sub, sub_mul]; abel

theorem adL_neg (F u : U n) : adL F (-u) = - adL F u := by
  simp only [adL, mul_neg, neg_mul]; abel

theorem adL_e (i j c d : Fin n) :
    adL (e (j, i)) (e (c, d)) =
      (if i = c then e (j, d) else 0) - (if d = j then e (c, i) else 0) :=
  e_mul_sub_mul (j, i) (c, d)

theorem adL_iter_e {i j : Fin n} (hij : i ≠ j) (a : Fin n × Fin n) :
    (adL (e (j, i)))^[3] (e a) = 0 := by
  obtain ⟨c, d⟩ := a
  show adL (e (j, i)) (adL (e (j, i)) (adL (e (j, i)) (e (c, d)))) = 0
  have hji : j ≠ i := hij.symm
  by_cases h1 : i = c <;> by_cases h2 : d = j
  · subst h1; subst h2
    simp [adL_e, adL_sub, adL_neg, adL_zero, hij, hji]
  · subst h1
    simp [adL_e, adL_sub, adL_neg, adL_zero, hij, hji, h2]
  · subst h2
    simp [adL_e, adL_sub, adL_neg, adL_zero, hij, hji, h1]
  · simp [adL_e, adL_sub, adL_neg, adL_zero, h1, h2]

theorem pow_mul_mem_Jp_of_le {F w : U n} {N N' : ℕ} (h : N ≤ N') (hw : F ^ N * w ∈ Jp n) :
    F ^ N' * w ∈ Jp n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h
  rw [pow_add, mul_assoc]
  exact mul_mem_Jp _ hw

theorem exists_pow_mul_mul_mem (F : U n) (s : ℕ) :
    ∀ (r M : ℕ) (u y : U n), r + M = s → (adL F)^[r] u = 0 → F ^ M * y ∈ Jp n →
      ∃ N : ℕ, F ^ N * (u * y) ∈ Jp n := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro r M u y hs hu hy
    rcases M with _ | M
    · refine ⟨0, ?_⟩
      rw [pow_zero, one_mul] at hy ⊢
      exact mul_mem_Jp u hy
    rcases r with _ | r
    · refine ⟨0, ?_⟩
      have : u = 0 := hu
      simp [this]
    obtain ⟨N₁, h₁⟩ := ih (r + 1 + M) (by omega) (r + 1) M u (F * y) rfl hu
      (by rw [← mul_assoc, ← pow_succ]; exact hy)
    obtain ⟨N₂, h₂⟩ := ih (r + (M + 1)) (by omega) r (M + 1) (adL F u) y rfl
      (by rw [← Function.iterate_succ_apply]; exact hu) hy
    refine ⟨max N₁ N₂ + 1, ?_⟩
    have key : F ^ (max N₁ N₂ + 1) * (u * y) =
        F ^ max N₁ N₂ * (u * (F * y)) + F ^ max N₁ N₂ * (adL F u * y) := by
      rw [pow_succ, ← mul_add, mul_assoc]
      congr 1
      simp only [adL, sub_mul, mul_assoc]
      abel
    rw [key]
    exact Submodule.add_mem _ (pow_mul_mem_Jp_of_le (le_max_left _ _) h₁)
      (pow_mul_mem_Jp_of_le (le_max_right _ _) h₂)

theorem lower_locally_nilpotent {n : ℕ} (i j : Fin n) (x : U n) (hij : (j : ℕ) = i + 1) :
    ∃ N : ℕ, e (j, i) ^ N * x ∈ Jp n := by
  have hne : i ≠ j := by
    intro h
    rw [h] at hij
    omega
  have step : ∀ v : U n, ∀ y : U n, (∃ N : ℕ, e (j, i) ^ N * y ∈ Jp n) →
      ∃ N : ℕ, e (j, i) ^ N * (v * y) ∈ Jp n := by
    intro v
    induction v using U.induction with
    | halg r =>
      rintro y ⟨N, hN⟩
      refine ⟨N, ?_⟩
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm]
      exact Submodule.smul_mem _ r hN
    | hι X =>
      intro y hy
      obtain ⟨M, hM⟩ := hy
      have hsum : ∀ t : Finset (Fin n × Fin n), ∃ N : ℕ, e (j, i) ^ N *
          ((∑ a ∈ t, X a.1 a.2 • e (n := n) a) * y) ∈ Jp n := by
        intro t
        induction t using Finset.induction_on with
        | empty => exact ⟨0, by simp⟩
        | insert a t ha ih =>
          obtain ⟨N₁, h₁⟩ := ih
          obtain ⟨N₂, h₂⟩ := exists_pow_mul_mul_mem (e (j, i)) (3 + M) 3 M (e a) y rfl
            (adL_iter_e hne a) hM
          refine ⟨max N₁ N₂, ?_⟩
          rw [Finset.sum_insert ha, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
          exact Submodule.add_mem _
            (Submodule.smul_mem _ _ (pow_mul_mem_Jp_of_le (le_max_right _ _) h₂))
            (pow_mul_mem_Jp_of_le (le_max_left _ _) h₁)
      rw [ι_eq_sum_e]
      exact hsum Finset.univ
    | hmul a b ha hb =>
      intro y hy
      rw [mul_assoc]
      exact ha _ (hb _ hy)
    | hadd a b ha hb =>
      intro y hy
      obtain ⟨N₁, h₁⟩ := ha y hy
      obtain ⟨N₂, h₂⟩ := hb y hy
      refine ⟨max N₁ N₂, ?_⟩
      rw [add_mul, mul_add]
      exact Submodule.add_mem _ (pow_mul_mem_Jp_of_le (le_max_left _ _) h₁)
        (pow_mul_mem_Jp_of_le (le_max_right _ _) h₂)
  have h1 : ∃ N : ℕ, e (j, i) ^ N * (1 : U n) ∈ Jp n :=
    ⟨2, by simpa using mul_sq_mem_Jp (1 : U n) hij⟩
  simpa using step x 1 h1

end GlobalTheory.CompanionTheory.PresRho
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpectralTraceOfModelAlgebra
section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open PositivityTheory.Rg.BcB.F.Eig
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SpecModel

theorem twTr_unit (hL : LocAlg) {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E}
    (σ : SmIrr (UL n w)) (hlev : IsLevel (MonoidHom.id _) (KL n w) (KL n w))
    (h1 : Module.finrank ℂ (fixed σ.ρ (KL n w)) = 1) {f : UL n w → ℂ} (hf : IsHecke (KL n w) f) :
    twTr σ.ρ (KL n w) (KL n w) ((KL n w : Set (UL n w)).indicator 1) LinearMap.id = 1 := by
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := hL E n w σ _ hlev f f hf hf
  obtain ⟨h8, -, -, -, -, -, -, h9⟩ := hL E n w σ _ hlev _ _ h7 h7
  have e : ((KL n w : Set (UL n w)).indicator fun _ => (((KL n w).relIndex (KL n w) : ℕ) : ℂ)) =
      (KL n w : Set (UL n w)).indicator 1 := by
    rw [Subgroup.relIndex_self]
    congr 1
    funext x
    simp
  rw [e] at h8 h9
  have : FiniteDimensional ℂ (fixed σ.ρ (KL n w)) := Module.finite_of_finrank_pos (by omega)
  rw [h8, h9, LinearMap.trace_one, h1]
  simp

theorem finprod_split {P : Type} (S : Set P) (B : Finset P) (hB : (↑B : Set P) ⊆ S) (F G : P → ℂ)
    (T : {w // w ∈ B} → ℂ) (hT : ∀ w, T w = F w.1) (hG : ∀ w ∈ S, w ∉ B → F w = G w)
    (hfin : ((S \ ↑B) ∩ Function.mulSupport F).Finite) :
    ∏ᶠ w ∈ S, F w = (∏ᶠ w ∈ S \ ↑B, G w) * ∏ w, T w := by
  have hon : ((↑B : Set P) ∩ Function.mulSupport F).Finite := B.finite_toSet.inter_of_left _
  have hB' : ∏ᶠ w ∈ (↑B : Set P), F w = ∏ w, T w := by
    rw [finprod_mem_coe_finset, ← Finset.prod_coe_sort]
    exact Finset.prod_congr rfl fun w _ => (hT w).symm
  have hC : ∏ᶠ w ∈ S \ ↑B, F w = ∏ᶠ w ∈ S \ ↑B, G w :=
    finprod_mem_congr rfl fun w hw => hG w hw.1 hw.2
  have hS : ↑B ∪ (S \ ↑B) = S := Set.union_sdiff_cancel hB
  rw [← hS, finprod_mem_union' Set.disjoint_sdiff_right hon hfin, hS, hB', hC, mul_comm]

theorem specTrace : UModel → LocAlg → SpecTrace := by
  intro hU hL E _ _ _ n S B hB K' hK' hKB ι _ σ hfd hone g
  have : ∀ (i : ι) (w : {w // w ∈ B}), FiniteDimensional ℂ (fixed (σ i w.1).ρ (K' w.1)) :=
    fun i w => hfd i w.1 (hB w.2)
  obtain ⟨d, blk, u, h1, h2, h3⟩ := hU ι {w // w ∈ B} (fun i w => ↥(fixed (σ i w.1).ρ (K' w.1)))
    (fun i w => locOp (σ i w.1) (K' w.1) (g w.1))
  refine ⟨d, blk, u, h1, ?_, ?_⟩
  · intro k f hf hloc
    rw [h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hoff : ((S \ ↑B) ∩ Function.mulSupport
        fun w => twTr (σ i w).ρ (KL n w) (K' w) (f w) LinearMap.id).Finite := by
      have hev := hK'.2.and hf.2
      rw [Filter.eventually_cofinite] at hev
      refine hev.subset ?_
      rintro w ⟨⟨hwS, hwB⟩, hne⟩ ⟨e1, e2⟩
      apply hne
      have hlev := hK'.1 w
      have hH := hf.1 w
      rw [e1] at hlev hH
      show twTr (σ i w).ρ (KL n w) (K' w) (f w) LinearMap.id = 1
      rw [e1, e2]
      exact twTr_unit hL (σ i w) hlev (hone i w hwS hwB) hH
    refine finprod_split S B hB (fun w => twTr (σ i w).ρ (KL n w) (K' w) (f w) LinearMap.id)
      (fun w => twTr (σ i w).ρ (KL n w) (KL n w) (f w) LinearMap.id)
      (fun w => LinearMap.trace ℂ _ (locOp (σ i w.1) (K' w.1) (g w.1) ^ k)) ?_ ?_ hoff
    · intro w
      show LinearMap.trace ℂ _ (locOp (σ i w.1) (K' w.1) (g w.1) ^ k) =
        twTr (σ i w.1).ρ (KL n w.1) (K' w.1) (f w.1) LinearMap.id
      rw [← hloc i w.1 w.2]
      exact (hL E n w.1 (σ i w.1) (K' w.1) (hK'.1 w.1) (f w.1) (f w.1) (hf.1 w.1) (hf.1 w.1)).1.symm
    · intro w hwS hwB
      show twTr (σ i w).ρ (KL n w) (K' w) (f w) LinearMap.id =
        twTr (σ i w).ρ (KL n w) (KL n w) (f w) LinearMap.id
      rw [hKB w hwS hwB]
  · intro i₀ hi
    exact h3 i₀ fun w => hi w.1 w.2

end GlobalTheory.CompanionTheory.SpecModel

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitDictionaryHolds
section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SplitPlace

section Generic

variable {G : Type} [Group G]

def toFull (H : Subgroup G) (hH : ∀ g, g ∈ H) : G →* H where
  toFun g := ⟨g, hH g⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def quotEquiv (H : Subgroup G) (hH : ∀ g, g ∈ H) (K : Subgroup H) : H ⧸ K ≃ G ⧸ K.map H.subtype :=
  Quotient.congr (Equiv.ofBijective H.subtype ⟨Subtype.val_injective, fun g => ⟨⟨g, hH g⟩, rfl⟩⟩) fun a b => by
    change QuotientGroup.leftRel K a b ↔ QuotientGroup.leftRel (K.map H.subtype) a.1 b.1
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨x, hx, hxe⟩
      have : x = a⁻¹ * b := Subtype.ext hxe
      exact this ▸ hx

theorem finite_cosets [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G) (hK : IsOpen (K : Set G)) (f : G → ℂ)
    (hc : HasCompactSupport f) : {q : G ⧸ K | f q.out ≠ 0}.Finite := by
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK
  have h1 : IsCompact ((QuotientGroup.mk : G → G ⧸ K) '' tsupport f) := hc.image continuous_quotient_mk'
  refine h1.finite_of_discrete.subset fun q hq => ?_
  exact ⟨q.out, subset_tsupport _ hq, QuotientGroup.out_eq' q⟩

theorem hasCompactSupport_val [TopologicalSpace G] (H : Subgroup G) (hH : ∀ g, g ∈ H) (e : G → ℂ)
    (hc : HasCompactSupport e) : HasCompactSupport fun x : H => e x.1 := by
  have hcl : IsClosed {a : G | a ∈ H} := by
    have : {a : G | a ∈ H} = Set.univ := Set.eq_univ_of_forall hH
    rw [this]
    exact isClosed_univ
  exact hc.comp_isClosedEmbedding (Topology.IsClosedEmbedding.subtypeVal hcl)

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem levOp_full [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G) (hH : ∀ g, g ∈ H)
    (ρ : Representation ℂ H V) (K K' : Subgroup H) (hK' : IsOpen (K' : Set H)) (hr : K'.relIndex K ≠ 0) (e : G → ℂ)
    (hc : HasCompactSupport e) (hinv : ∀ k ∈ K'.map H.subtype, ∀ g, e (g * k) = e g) (y : V) (hy : y ∈ fixed ρ K') :
    levOp ρ K K' (fun x => ((K'.relIndex K : ℕ) : ℂ) * e x.1) LinearMap.id y =
      ∑ᶠ q : G ⧸ K'.map H.subtype, e q.out • (ρ.comp (toFull H hH)) q.out y := by
  have hr' : ((K'.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hr
  have hfin := finite_cosets K' hK' _ (hasCompactSupport_val H hH e hc)
  have hs : (Function.support fun q : H ⧸ K' =>
      ((fun x : H => ((K'.relIndex K : ℕ) : ℂ) * e x.1) q.out • (ρ q.out ∘ₗ LinearMap.id) : V →ₗ[ℂ] V)).Finite := by
    refine hfin.subset fun q hq h0 => hq ?_
    have h0' : e q.out.1 = 0 := h0
    simp [h0']
  have h1 : levOp ρ K K' (fun x => ((K'.relIndex K : ℕ) : ℂ) * e x.1) LinearMap.id y =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ • (LinearMap.applyₗ y : (V →ₗ[ℂ] V) →ₗ[ℂ] V).toAddMonoidHom
        (∑ᶠ q : H ⧸ K', (fun x : H => ((K'.relIndex K : ℕ) : ℂ) * e x.1) q.out • (ρ q.out ∘ₗ LinearMap.id)) := rfl
  rw [h1, AddMonoidHom.map_finsum _ hs, smul_finsum, ← finsum_comp_equiv (quotEquiv H hH K')]
  refine finsum_congr fun q => ?_
  have hq : quotEquiv H hH K' q = ((q.out.1 : G) : G ⧸ K'.map H.subtype) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (K'.map H.subtype) q.out.1
  rw [hq, hk, hinv k.1 k.2]
  have hk' : (toFull H hH k.1) ∈ K' := by
    obtain ⟨x, hx, hxe⟩ := k.2
    have : toFull H hH k.1 = x := Subtype.ext hxe.symm
    exact this ▸ hx
  have hfix := (GlobalTheory.TwTrLin.mem_fixed_iff ρ K' y).1 hy _ hk'
  have h2 : (ρ.comp (toFull H hH)) (q.out.1 * k.1) y = ρ q.out y := by
    have : toFull H hH (q.out.1 * k.1) = q.out * toFull H hH k.1 := Subtype.ext rfl
    rw [MonoidHom.comp_apply, this, map_mul, Module.End.mul_apply, hfix]
  rw [h2]
  simp [smul_smul, hr']

def fullIrr [TopologicalSpace G] (H : Subgroup G) (hH : ∀ g, g ∈ H) (σ : SmIrr H) : SmIrr G where
  V := σ.V
  ρ := σ.ρ.comp (toFull H hH)
  smooth v := (σ.smooth v).preimage (Continuous.subtype_mk continuous_id hH)
  irred := by
    obtain ⟨h0, h⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 σ.irred
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g v hv => ?_⟩
    exact hW g.1 v hv

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_UL {w : Pl E} (hw : IsSplitAt w) (g : GLw n w) : g ∈ UL n w := by
  unfold UL
  rw [if_pos hw]
  exact Subgroup.mem_top g

theorem splitDict : PositivityTheory.Rg.BcB.F.Eig.SplitDict := by
  intro E _ _ _ n w hw σ
  have hH := mem_UL (n := n) hw
  refine ⟨fullIrr (UL n w) hH σ, LinearEquiv.refl ℂ σ.V, fun _ _ => rfl, ?_, ?_⟩
  · rintro π ⟨p, hp, -, f, hf0, hfm, hfe⟩
    refine ⟨(fullIrr (UL n w) hH σ).irred, f, hf0, hfm, fun x v => ?_⟩
    have hpx : toFull (UL n w) hH (((cLoc w).comp (locU n w).subtype) x) = p x := Subtype.ext (hp x).symm
    change f (σ.ρ (toFull (UL n w) hH (((cLoc w).comp (locU n w).subtype) x)) v) = _
    rw [hpx]
    exact hfe x v
  · intro K' hlev e hk
    obtain ⟨-, -, hcs, hinv⟩ := hk
    have hKK : ∀ k ∈ K', ∀ x : UL n w, (k.1 * x.1 * 1 : GLw n w) = (k * x).1 := fun k _ x => by simp
    refine ⟨⟨hasCompactSupport_val _ hH e hcs, fun k hk x => ⟨?_, ?_⟩⟩, fun y hy => ⟨?_, ?_⟩⟩
    · have := hinv k.1 ⟨k, hk, rfl⟩ 1 (by simp) x.1
      simpa using this
    · have := hinv 1 (by simp) k.1 ⟨k, hk, rfl⟩ x.1
      simpa using this
    · refine (GlobalTheory.TwTrLin.mem_fixed_iff _ _ _).2 ?_
      rintro _ ⟨k, hk, rfl⟩
      exact (GlobalTheory.TwTrLin.mem_fixed_iff σ.ρ K' y).1 hy k hk
    · have hr := (GlobalTheory.TwTrUnit.twTr_unit E n w K' hlev σ).2.1
      exact levOp_full (UL n w) hH σ.ρ (KL n w) K' hlev.1 hr e hcs
        (fun k hk g => by simpa using hinv 1 (by simp) k hk g) y hy

end GlobalTheory.CompanionTheory.SplitPlace

end
end

