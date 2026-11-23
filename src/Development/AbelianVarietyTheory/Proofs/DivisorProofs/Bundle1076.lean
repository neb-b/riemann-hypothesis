module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0545
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsSubspaceStableSobolevFormDeriv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0982
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactTypeInCompactStableSubmodule
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKtypeHolomorphicKilledByLoweringRoots
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNcardUnitBallLeOfIndependentLevelBound
section
open Filter Topology
open GlobalTheory GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem log_ncard_unit_ball_le_of_indep_bound :
    ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B →
      (B 1).Finite → ∀ (q : ℕ) (T : ℝ), 3 ≤ q → 0 ≤ T →
      (∀ (r : ℕ) (e : Fin r → G) (n : Fin r → ℕ), LinearIndependent ℤ e → (∀ j, e j ∈ B ((2 / q : ℝ) ^ n j)) →
        ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ T) → Real.log ((B 1).ncard : ℝ) ≤ Real.log q * T := by
  classical
  intro G _ _ Λ B hB hfin q T hq hT hbound
  set S : ℕ → Set G := fun i => B ((2 / q : ℝ) ^ i) with hS
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hmono := (isBallFam_mono_neg_add G Λ B hB).1
  have hSdec : ∀ i, S (i + 1) ⊆ S i := by
    intro i
    apply hmono
    have h0 : (0 : ℝ) ≤ 2 / q := by positivity
    have h1 : (2 / q : ℝ) ≤ 1 := by
      rw [div_le_one hqpos]; exact_mod_cast (by omega : 2 ≤ q)
    exact pow_le_pow_of_le_one h0 h1 (Nat.le_succ i)
  set K : ℕ := ⌊T⌋₊ with hK

  have hsize : ∀ i m (e : Fin m → G), LinearIndependent ℤ e → (∀ j, e j ∈ S i) → m ≤ K := by
    intro i m e he hmem
    have h := hbound m e (fun _ => i) he hmem
    apply Nat.le_floor
    refine le_trans ?_ h
    have : m ≤ ∑ _j : Fin m, (i + 1) := by simp; exact Nat.le_mul_of_pos_right m (Nat.succ_pos i)
    exact_mod_cast this
  let P : ℕ → ℕ → Prop := fun i m => ∃ e : Fin m → G, LinearIndependent ℤ e ∧ ∀ j, e j ∈ S i
  let r : ℕ → ℕ := fun i => Nat.findGreatest (P i) K
  have hP0 : ∀ i, P i 0 := fun i => ⟨Fin.elim0, linearIndependent_empty_type, fun j => j.elim0⟩
  have hrspec : ∀ i, P i (r i) := fun i => Nat.findGreatest_spec (Nat.zero_le K) (hP0 i)
  have hrmax : ∀ i m (e : Fin m → G), LinearIndependent ℤ e → (∀ j, e j ∈ S i) → m ≤ r i := by
    intro i m e he hmem
    exact Nat.le_findGreatest (hsize i m e he hmem) ⟨e, he, hmem⟩
  have hrdec : ∀ i, r (i + 1) ≤ r i := by
    intro i
    obtain ⟨e, he, hmem⟩ := hrspec (i + 1)
    exact hrmax i _ e he (fun j => hSdec i (hmem j))

  have hstep : ∀ i, (S i).encard ≤ ((q ^ r i : ℕ) : ℕ∞) * (S (i + 1)).encard := by
    intro i
    have h := _root_.GlobalTheory.VolBr.encard_ball_le_pow_mul G Λ B hB ((2 / q : ℝ) ^ i) q (r i) (by omega)
      (fun n e he hmem => hrmax i n e he hmem)
    have heq : 2 * (2 / q : ℝ) ^ i / q = (2 / q : ℝ) ^ (i + 1) := by
      rw [pow_succ]; ring
    simpa [hS, heq] using h
  have hiter : ∀ k, (S 0).encard ≤ ((q ^ (∑ i ∈ Finset.range k, r i) : ℕ) : ℕ∞) * (S k).encard := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      refine ih.trans ?_
      rw [Finset.sum_range_succ, pow_add, Nat.cast_mul, mul_assoc]
      gcongr
      exact hstep k

  have hSK : S K ⊆ {0} := by
    intro x hx
    by_contra hx0
    have hli : LinearIndependent ℤ (fun _ : Fin 1 => x) := by
      letI : HasUniqueDiv G := ⟨by
        intro n hn a b h
        exact eq_of_nsmul_eq_nsmul_of_addCommute hn (AddCommute.all _ _) h⟩
      rw [linearIndependent_unique_iff]; exact hx0
    have h := hbound 1 (fun _ => x) (fun _ => K) hli (fun _ => hx)
    have hlt : T < (K : ℝ) + 1 := Nat.lt_floor_add_one T
    simp at h
    linarith
  have hSK1 : (S K).encard ≤ 1 := by
    calc (S K).encard ≤ ({0} : Set G).encard := Set.encard_le_encard hSK
      _ = 1 := Set.encard_singleton 0

  obtain ⟨e, n, he, hmem, hsum⟩ := _root_.GlobalTheory.exists_linearIndependent_adapted_to_decreasing_chain G S hSdec K r hrspec hrdec
  have hM : ((∑ i ∈ Finset.range K, r i : ℕ) : ℝ) ≤ T := by
    have h1 := hbound (r 0) e n he hmem
    have h2 : ∑ i ∈ Finset.range K, r i ≤ ∑ i ∈ Finset.range (K + 1), r i :=
      Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (Nat.le_succ K))
    have h3 : ((∑ i ∈ Finset.range K, r i : ℕ) : ℝ) ≤ ((∑ j, (n j + 1) : ℕ) : ℝ) := by
      exact_mod_cast h2.trans hsum
    linarith
  set M := ∑ i ∈ Finset.range K, r i with hMdef
  have hS0 : S 0 = B 1 := by simp [hS]
  have hcard : (B 1).encard ≤ ((q ^ M : ℕ) : ℕ∞) := by
    rw [← hS0]
    calc (S 0).encard ≤ ((q ^ M : ℕ) : ℕ∞) * (S K).encard := hiter K
      _ ≤ ((q ^ M : ℕ) : ℕ∞) * 1 := by gcongr
      _ = _ := mul_one _
  have hncard : (B 1).ncard ≤ q ^ M := by
    rw [← hfin.cast_ncard_eq] at hcard
    exact_mod_cast hcard
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  rcases Nat.eq_zero_or_pos (B 1).ncard with h0 | hpos
  · rw [h0]; simp; positivity
  · have hpos' : (0 : ℝ) < (B 1).ncard := by exact_mod_cast hpos
    calc Real.log ((B 1).ncard : ℝ) ≤ Real.log ((q ^ M : ℕ) : ℝ) :=
          Real.log_le_log hpos' (by exact_mod_cast hncard)
      _ = M * Real.log q := by rw [Nat.cast_pow, Real.log_pow]
      _ ≤ T * Real.log q := by gcongr
      _ = Real.log q * T := mul_comm _ _

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowIrreducibleKStable
section
open MvPolynomial Formalism.BasicNotions.TH

namespace GlobalTheory.LowStable

theorem X_mul_pderiv_totalDegree_le {σ : Type} (u v : σ) (g : MvPolynomial σ ℂ) :
    (X u * pderiv v g).totalDegree ≤ g.totalDegree := by
  classical
  have key : ∀ m ∈ (pderiv v g).support, (m.sum fun _ e => e) + 1 ≤ g.totalDegree := by
    intro m hm
    have hc : AddMonoidAlgebra.coeff g (m + Finsupp.single v 1) ≠ 0 := by
      rw [mem_support_iff, coeff_pderiv] at hm
      intro h
      rw [h, zero_mul] at hm
      exact hm rfl
    have h1 := le_totalDegree (mem_support_iff.2 hc)
    have h2 : ((m + Finsupp.single v 1).sum fun _ e => e) = (m.sum fun _ e => e) + 1 := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
    rw [h2] at h1
    exact h1
  by_cases h0 : pderiv v g = 0
  · rw [h0, mul_zero, totalDegree_zero]; exact Nat.zero_le _
  · obtain ⟨m, hm⟩ := (support_nonempty).2 h0
    have hm1 := key m hm
    have hle : (pderiv v g).totalDegree ≤ g.totalDegree - 1 :=
      Finset.sup_le fun m' hm' => by have := key m' hm'; show (m'.sum fun _ e => e) ≤ _; omega
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X]
    omega

theorem omE_mem_restrictTotalDegree {P Q R S : ℕ} (D : ℕ) (u v : Ln P Q R S) (h : linePos u = linePos v)
    (g : Pol P Q R S) (hg : g ∈ restrictTotalDegree (Ln P Q R S) ℂ D) :
    omE u v g ∈ restrictTotalDegree (Ln P Q R S) ℂ D := by
  have hN := (mem_restrictTotalDegree _ _ _).1 hg
  have hXd : ∀ a b : Ln P Q R S, X a * pderiv b g ∈ restrictTotalDegree (Ln P Q R S) ℂ D :=
    fun a b => (mem_restrictTotalDegree _ _ _).2 ((X_mul_pderiv_totalDegree_le a b g).trans hN)
  cases hu : linePos u
  · rw [GlobalTheory.CompactHarm.omE_nn u v hu (h ▸ hu) g]
    exact Submodule.sub_mem _ (Submodule.neg_mem _ (hXd v u)) (Submodule.smul_mem _ _ hg)
  · rw [GlobalTheory.CompactHarm.omE_pp u v hu (h ▸ hu) g]
    exact Submodule.add_mem _ (hXd u v) (Submodule.smul_mem _ _ hg)

theorem fockAct2_apply_eq {P Q R S : ℕ} (Z : Mat R S) (g : Pol P Q R S) :
    fockAct2 P Q R S Z g = ∑ c, ∑ d, Z c d • ∑ a, omE (a, c) (a, d) g := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  have : Matrix.single c d (Z c d) = Z c d • (Eab c d : Mat R S) := by
    rw [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this, map_smul, LinearMap.smul_apply, fockAct2_Eab, LinearMap.sum_apply]

theorem fockAct2_mem_restrictTotalDegree {P Q R S : ℕ} (D : ℕ) (Z : Mat R S) (hZ : IsKC Z)
    (g : Pol P Q R S) (hg : g ∈ restrictTotalDegree (Ln P Q R S) ℂ D) :
    fockAct2 P Q R S Z g ∈ restrictTotalDegree (Ln P Q R S) ℂ D := by
  rw [fockAct2_apply_eq]
  refine Submodule.sum_mem _ fun c _ => Submodule.sum_mem _ fun d _ => ?_
  by_cases hcd : sameBlock c d
  · refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => ?_)
    refine omE_mem_restrictTotalDegree D _ _ ?_ g hg
    rcases a with a | a <;> rcases c with c | c <;> rcases d with d | d <;>
      first | rfl | exact absurd hcd (by simp [sameBlock])
  · rw [hZ c d hcd, zero_smul]
    exact Submodule.zero_mem _

theorem lowOne_stable : ∀ (P Q R S : ℕ) (x : ℚ) (k k' : ℕ), x - Formalism.BasicNotions.TH.cPair R S = k →
    x + Formalism.BasicNotions.TH.cPair R S = k' → ∀ Z : Formalism.BasicNotions.TH.Mat R S, Formalism.BasicNotions.TH.IsKC Z →
    ∀ f ∈ GlobalTheory.KFixIrr.lowOne P Q R S x (P * k + Q * k'),
    Formalism.BasicNotions.TH.fockAct2 P Q R S Z f ∈ GlobalTheory.KFixIrr.lowOne P Q R S x (P * k + Q * k') := by
  intro P Q R S x k k' _ _ Z hZ f hf
  rw [GlobalTheory.KFixIrr.lowOne, Submodule.mem_inf] at hf ⊢
  refine ⟨?_, fockAct2_mem_restrictTotalDegree _ Z hZ f hf.2⟩
  rw [GlobalTheory.KFixIrr.mem_chiOne] at hf ⊢
  intro X hX
  have hc := LinearMap.congr_fun ((GlobalTheory.FockAlg.fock_lie_and_commute P Q R S).2.2.2 X Z) f
  rw [Module.End.mul_apply, Module.End.mul_apply] at hc
  rw [hc, hf.1 X hX, map_smul]

end GlobalTheory.LowStable
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypeKilledByNegativeNoncompactRoots
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowestKilled

open Formalism.REAL GlobalTheory.HolDict GlobalTheory.HolDict.Lowering

variable {n : ℕ}

lemma vNormSq_congr (ε ε' : Fin n → Bool) (h : ∀ i j, ε i = ε j ↔ ε' i = ε' j) (μ : Fin n → ℝ) :
    vNormSq ε μ = vNormSq ε' μ := by
  have : rhoC ε = rhoC ε' := by
    funext a
    simp only [rhoC, h]
  simp only [vNormSq, this]

lemma vNormSq_lt_of_blocks (p : ℕ) (s : Bool) (ε : Fin n → Bool) (hε : ∀ a : Fin n, ε a = if (a : ℕ) < p then s else !s)
    (lam μ : Fin n → ℝ) (hlam : StrictAnti lam)
    (hΛ : ∀ i j, i < j → ε i = ε j → Formalism.QuantumDeterminants.lowK ε lam j ≤ Formalism.QuantumDeterminants.lowK ε lam i)
    (hμ : ∀ i j, i < j → ε i = ε j → μ j ≤ μ i)
    (a c : Fin n) (ha : ε a = s) (hc : ε c = !s) (hd : CDom ε (μ + root a c) (Formalism.QuantumDeterminants.lowK ε lam)) :
    vNormSq ε μ < vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam) := by
  let ε' : Fin n → Bool := fun a => decide ((a : ℕ) < p)
  have h : ∀ i j, ε i = ε j ↔ ε' i = ε' j := by
    intro i j
    rw [hε i, hε j]
    by_cases hi : (i : ℕ) < p <;> by_cases hj : (j : ℕ) < p <;> cases s <;> simp [ε', hi, hj]
  rw [vNormSq_congr ε ε' h, vNormSq_congr ε ε' h]
  refine vNormSq_lt p ε' (fun _ => rfl) _ μ (fun i j hij e => hΛ i j hij ((h i j).2 e))
    (fun i j hij e => hμ i j hij ((h i j).2 e)) ?_ a c ?_ ?_ ?_
  · intro a c ha hc
    rw [← vNormSq_congr ε ε' h, ← vNormSq_congr ε ε' h]
    refine GlobalTheory.HolDict.VoganRoot.vNormSq_lowK_sub_root_lt ε hlam ?_
    simp only [ε', decide_eq_true_eq, decide_eq_false_iff_not] at ha hc
    exact Fin.lt_def.mpr (by omega)
  · rw [hε] at ha
    by_cases hi : (a : ℕ) < p <;> cases s <;> simp_all [ε']
  · rw [hε] at hc
    by_cases hi : (c : ℕ) < p <;> cases s <;> simp_all [ε']
  · obtain ⟨co, hco, hd⟩ := hd
    exact ⟨co, fun i j e => ⟨(hco i j e).1, (h i j).1 (hco i j e).2⟩, hd⟩

lemma conjH_single_ne {ε : Fin n → Bool} (a c : Fin n) (hac : ε a ≠ ε c) :
    conjH (Formalism.REAL.Jm ε) (Matrix.single c a (1 : ℂ)) = Matrix.single a c 1 := by
  unfold conjH
  rw [Matrix.inv_eq_left_inv (Jm_mul_self ε)]
  ext i j
  simp only [Formalism.REAL.Jm, Matrix.neg_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply,
    Matrix.single_apply]
  by_cases h : a = i ∧ c = j
  · obtain ⟨rfl, rfl⟩ := h
    cases ha : ε a <;> cases hc : ε c <;> simp_all
  · have h' : ¬(c = j ∧ a = i) := fun h' => h ⟨h'.2, h'.1⟩
    simp [h, h']

theorem dRepC_single_eq_zero (p : ℕ) (s : Bool) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Mt n → (H →L[ℂ] H)) (hlam : StrictAnti lam)
    (hε : ∀ a : Fin n, ε a = if (a : ℕ) < p then s else !s) (hDS : IsDS ε lam σ) (v : H) (hv : v ∈ lowKSub ε lam σ)
    (hsm : SmoothVec (lieH (Formalism.REAL.Jm ε)) σ v) (a c : Fin n) (ha : ε a = s) (hc : ε c = !s) :
    dRepC (Formalism.REAL.Jm ε) σ (Matrix.single c a 1) v = 0 := by
  obtain ⟨hcomp, -, hσ, -, -, ⟨S₀, hS₀⟩, hmin⟩ := hDS
  have hH : (Formalism.REAL.Jm ε).IsHermitian := Jm_conjTranspose ε
  have hdet : (Formalism.REAL.Jm ε).det ≠ 0 := (Matrix.isUnit_det_of_left_inverse (Jm_mul_self ε)).ne_zero
  have hU : IsURepOn (Formalism.QuantumDeterminants.UH (Formalism.REAL.Jm ε)) σ := hσ
  obtain ⟨hspan, hsmv⟩ := GlobalTheory.UnitarySmVec.smoothVec_basic n _ H σ hH hdet hU
  have hlie := GlobalTheory.HolDict.LieAct.main n _ H σ hH hdet hU
  obtain ⟨W, hWf, hWK, hWle, hvW⟩ := exists_fin_stable lam hv
  set J := Formalism.REAL.Jm ε with hJ
  let u₀ : ℂ := if s then 1 else -1
  let V : Submodule ℂ H := W ⊓ Submodule.span ℂ {w | SmoothVec (lieH J) σ w}
  have hVs : ∀ w ∈ V, SmoothVec (lieH J) σ w := fun w hw => hspan w hw.2
  haveI : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le inf_le_left
  have hVK : ∀ g ∈ Kset ε, ∀ w ∈ V, σ g w ∈ V := fun g hg w hw =>
    ⟨hWK g hg w hw.1, Submodule.subset_span ((hsmv w (hVs w hw)).1 g (kset_sub hg))⟩
  have hs0 : SmoothVec (lieH J) σ 0 := hspan 0 (Submodule.zero_mem _)
  have hz1 : ∀ w, SmoothVec (lieH J) σ w → dRepC J σ 0 w = 0 := by
    intro w hw
    have := ((hlie w w hw hw).1 1 0 0).1
    simpa using this
  have hz2 : ∀ Z, dRepC J σ Z 0 = 0 := by
    intro Z
    have := ((hlie 0 0 hs0 hs0).1 1 Z Z).2.1
    simpa using this
  have hsm1 : ∀ w, SmoothVec (lieH J) σ w → ∀ (t : ℂ) Z, dRepC J σ (t • Z) w = t • dRepC J σ Z w := by
    intro w hw t Z
    have := ((hlie w w hw hw).1 t Z 0).1
    rwa [add_zero, hz1 w hw, add_zero] at this
  let B : Mt n →ₗ[ℂ] V →ₗ[ℂ] H := LinearMap.mk₂ ℂ (fun Z w => dRepC J σ Z w)
    (fun Z Z' w => by simpa using ((hlie w w (hVs _ w.2) (hVs _ w.2)).1 1 Z Z').1)
    (fun t Z w => hsm1 w (hVs _ w.2) t Z)
    (fun Z w w' => by simpa using ((hlie w w' (hVs _ w.2) (hVs _ w'.2)).1 1 Z Z).2.1)
    (fun t Z w => by
      have := ((hlie w 0 (hVs _ w.2) hs0).1 t Z Z).2.1
      rwa [add_zero, hz2, add_zero] at this)
  let G : Set H := {x | ∃ Z : Mt n, (Z * J = u₀ • Z ∧ J * Z = -(u₀ • Z)) ∧ ∃ w ∈ V, x = dRepC J σ Z w}
  let S : Submodule ℂ H := Submodule.span ℂ G
  have hSf : FiniteDimensional ℂ S := by
    refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (TensorProduct.lift B)) ?_
    refine Submodule.span_le.2 ?_
    rintro x ⟨Z, -, w, hw, rfl⟩
    exact ⟨Z ⊗ₜ ⟨w, hw⟩, rfl⟩
  have hSK : IsKStableOn ε σ S := by
    intro g hg
    have : S ≤ S.comap (σ g : H →ₗ[ℂ] H) := by
      refine Submodule.span_le.2 ?_
      rintro x ⟨Z, ⟨hZ1, hZ2⟩, w, hw, rfl⟩
      refine Submodule.subset_span ⟨g * Z * g⁻¹, ⟨?_, ?_⟩, σ g w, hVK g hg w hw,
        (hlie w w (hVs w hw) (hVs w hw)).2.2.1 g (kset_sub hg) Z⟩
      · rw [kset_inv hg, Matrix.mul_assoc, (kset_star hg).2, ← Matrix.mul_assoc, Matrix.mul_assoc g Z, hZ1]
        simp
      · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hg.2, Matrix.mul_assoc g _ Z, hZ2]
        simp
    exact fun x hx => this hx
  have hSs : ∀ x ∈ S, SmoothVec (lieH J) σ x := by
    intro x hx
    refine hspan x (Submodule.span_mono ?_ hx)
    rintro x ⟨Z, -, w, hw, rfl⟩
    exact (hsmv w (hVs w hw)).2.2.1 Z
  by_contra hne
  have hS0 : S ≠ ⊥ := by
    intro h0
    refine hne ((Submodule.mem_bot ℂ).1 (h0 ▸ Submodule.subset_span
      ⟨Matrix.single c a 1, ⟨?_, ?_⟩, v, ⟨hvW, Submodule.subset_span hsm⟩, rfl⟩))
    · ext i j
      simp only [hJ, Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.single_apply, Matrix.smul_apply]
      by_cases h : c = i ∧ a = j
      · obtain ⟨rfl, rfl⟩ := h
        cases s <;> simp [ha, u₀]
      · simp [h]
    · ext i j
      simp only [hJ, Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.neg_apply, Matrix.single_apply, Matrix.smul_apply]
      by_cases h : c = i ∧ a = j
      · obtain ⟨rfl, rfl⟩ := h
        cases s <;> simp [hc, u₀]
      · simp [h]
  obtain ⟨μ, S', hS'le, hS'⟩ := GlobalTheory.KTypeExists.exists_kType n ε H σ hσ S hSf hSK hS0
  obtain ⟨u, huS', hu0, hu⟩ := hS'.2.2.2.1
  have huS := hS'le huS'
  have hus := hSs u huS
  have hex : ∃ a' c' : Fin n, ε a' = s ∧ ε c' = !s ∧ ∃ w ∈ V,
      ⟪dRepC J σ (Matrix.single c' a' 1) w, u⟫_ℂ ≠ 0 := by
    by_contra hn
    push Not at hn
    have h : S ≤ (ℂ ∙ u)ᗮ := by
      refine Submodule.span_le.2 ?_
      rintro x ⟨Z, ⟨hZ1, hZ2⟩, w, hw, rfl⟩
      have h1 : dRepC J σ Z w = ∑ i, ∑ j, Z i j • dRepC J σ (Matrix.single i j 1) w := by
        have : B Z ⟨w, hw⟩ = ∑ i, ∑ j, Z i j • B (Matrix.single i j 1) ⟨w, hw⟩ := by
          conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, LinearMap.sum_apply]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [← LinearMap.smul_apply, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
        exact this
      rw [SetLike.mem_coe, h1]
      refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
      by_cases hij : Z i j = 0
      · rw [hij, zero_smul]
        exact Submodule.zero_mem _
      · refine Submodule.smul_mem _ _ (Submodule.mem_orthogonal_singleton_iff_inner_left.2 (hn j i ?_ ?_ w hw))
        · have := congrFun (congrFun hZ1 i) j
          simp only [hJ, Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, u₀] at this
          by_contra hj
          cases s
          · rw [if_pos (by simpa using hj), if_neg (by simp)] at this
            exact hij (by linear_combination (1 / 2 : ℂ) * this)
          · rw [if_neg hj, if_pos rfl] at this
            exact hij (by linear_combination (-1 / 2 : ℂ) * this)
        · have := congrFun (congrFun hZ2 i) j
          simp only [hJ, Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul,
            u₀] at this
          by_contra hi
          cases s
          · rw [if_neg (by simpa using hi), if_neg (by simp)] at this
            exact hij (by linear_combination (-1 / 2 : ℂ) * this)
          · rw [if_pos (by simpa using hi), if_pos rfl] at this
            exact hij (by linear_combination (1 / 2 : ℂ) * this)
    exact hu0 (inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_left.1 (h huS)))
  obtain ⟨a', c', ha', hc', w, hw, hwu⟩ := hex
  rw [(hlie w u (hVs w hw) hus).2.2.2, neg_ne_zero, hJ, conjH_single_ne a' c' (by rw [ha', hc']; cases s <;> simp), ← hJ] at hwu
  have hy : IsWtOn (Kset ε) σ (μ + root a' c') (dRepC J σ (Matrix.single a' c' 1) u) := by
    intro θ hθ
    have h1 := (hlie u u hus hus).2.2.1 _ (kset_sub hθ) (Matrix.single a' c' 1)
    have h2 := ((hlie u 0 hus hs0).1 (Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I))
      (Matrix.single a' c' 1) 0).2.1
    rw [add_zero, hz2, add_zero] at h2
    rw [h1, tor_conj, hsm1 _ ((hsmv u hus).1 _ (kset_sub hθ)), hu θ hθ, h2, smul_smul, ← Complex.exp_add]
    congr 2
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, sum_root_mul]
    push_cast
    ring
  have hd := cdom_of_inner_ne hσ lam hy (hWle hw.1) hwu
  exact absurd (hmin μ S' hS') (not_le.2 (vNormSq_lt_of_blocks p s ε hε lam μ hlam (dominant_of_isKTypeOf hσ hS₀)
    (dominant_of_isKTypeOf hσ hS') a' c' ha' hc' hd))

theorem lowK_killed : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool) (lam : Fin n → ℝ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (p : ℕ) (s : Bool), (∀ a : Fin n, ε a = if (a : ℕ) < p then s else !s) → StrictAnti lam → IsDS ε lam π → ∀ v ∈ lowKSub ε lam π, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0} π v → ∀ a b : Fin n, ε a ≠ ε b → b < a → ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0}, ∀ Y ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0}, X + Complex.I • Y = Matrix.single a b 1 → dRep π X v + Complex.I • dRep π Y v = 0 := by
  intro n H _ _ ε lam π p s hε hlam hDS v hv hsm a b hab hba X hX Y hY hXY
  have hb : ε b = s ∧ ε a = !s := by
    rw [hε a, hε b] at hab ⊢
    rw [Fin.lt_def] at hba
    by_cases ha : (a : ℕ) < p
    · rw [if_pos ha, if_pos (hba.trans ha)] at hab
      exact absurd rfl hab
    · by_cases hb : (b : ℕ) < p
      · simp [ha, hb]
      · rw [if_neg ha, if_neg hb] at hab
        exact absurd rfl hab
  have h := dRepC_single_eq_zero p s ε lam H π hlam hε hDS v hv hsm b a hb.1 hb.2
  rw [← hXY] at h
  exact (GlobalTheory.HolDict.LieAct.dRepC_parts (Matrix.isUnit_det_of_left_inverse (Jm_mul_self ε)).ne_zero hX hY v).symm.trans h

end GlobalTheory.LowestKilled
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompactPartCentralizerIffLocal
section
open Filter GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.BCT

theorem mem_cptPart_iff_local (ι G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : ι → Type)
    [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, T2Space (H i)]
    (p : ∀ i, G →* H i) (KH : ∀ i, Subgroup (H i)) (T : Subgroup G) (TH : ∀ i, Subgroup (H i)) :
    (∀ i, Continuous (p i)) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) →
    (∀ C : ∀ i, Set (H i), (∀ i, IsCompact (C i)) → (∀ᶠ i in cofinite, C i = KH i) →
      IsCompact {x : G | ∀ i, p i x ∈ C i}) →
    (∀ i, IsCompact (KH i : Set (H i))) → (∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i) →
    (∀ i, ∀ a ∈ TH i, ∀ b ∈ TH i, a * b = b * a) →
    ∀ x, x ∈ cptPart T ↔ x ∈ T ∧ ∀ i, p i x ∈ cptPart (TH i) := by
  intro hp hcof hcpt hKH hT hcomm x
  constructor
  · intro hx
    have hle : cptPart T ≤ T ⊓ ⨅ i, (cptPart (TH i)).comap (p i) := by
      rw [cptPart, Subgroup.closure_le]
      intro t ht
      obtain ⟨htT, htc⟩ := ht
      rw [SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_iInf]
      refine ⟨htT, fun i => ?_⟩
      rw [Subgroup.mem_comap]
      refine Subgroup.subset_closure (k := {s | s ∈ TH i ∧ IsCompact (closure (Subgroup.zpowers s : Set (H i)))})
        ⟨(hT t).1 htT i, ?_⟩
      have himc : IsCompact (p i '' closure (Subgroup.zpowers t : Set G)) := htc.image (hp i)
      refine himc.of_isClosed_subset isClosed_closure (closure_minimal ?_ himc.isClosed)
      rintro _ ⟨k, rfl⟩
      exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩
    have := hle hx
    simp only [Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap] at this
    exact this
  · rintro ⟨hxT, hxi⟩
    have hloc : ∀ i, IsCompact (closure (Subgroup.zpowers (p i x) : Set (H i))) := fun i =>
      (GlobalTheory.LocFinU.cptPart_subset_of_comm (TH i) (hcomm i) (hxi i)).2
    set C : ∀ i, Set (H i) := fun i => if p i x ∈ KH i then (KH i : Set (H i))
      else closure (Subgroup.zpowers (p i x) : Set (H i)) with hC
    have hCc : ∀ i, IsCompact (C i) := by
      intro i
      simp only [hC]
      split_ifs
      · exact hKH i
      · exact hloc i
    have hCf : ∀ᶠ i in cofinite, C i = KH i := by
      filter_upwards [hcof x] with i hi
      simp [hC, hi]
    have hS := hcpt C hCc hCf
    have hScl : IsClosed {y : G | ∀ i, p i y ∈ C i} := by
      have : {y : G | ∀ i, p i y ∈ C i} = ⋂ i, p i ⁻¹' C i := by ext; simp
      rw [this]
      exact isClosed_iInter fun i => (hCc i).isClosed.preimage (hp i)
    have hsub : (Subgroup.zpowers x : Set G) ⊆ {y : G | ∀ i, p i y ∈ C i} := by
      rintro _ ⟨k, rfl⟩ i
      simp only [hC, map_zpow]
      split_ifs with h
      · exact (KH i).zpow_mem h k
      · exact subset_closure ⟨k, rfl⟩
    refine Subgroup.subset_closure (k := {s | s ∈ T ∧ IsCompact (closure (Subgroup.zpowers s : Set G))}) ⟨hxT, ?_⟩
    exact hS.of_isClosed_subset isClosed_closure (closure_minimal hsub hScl)

end GlobalTheory.BCT
end

