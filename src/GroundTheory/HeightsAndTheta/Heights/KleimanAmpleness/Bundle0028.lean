module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StepTwoFiltGraded
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0012

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperDevissage
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w u₁ v₁ w₁

namespace Cech

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u₁} [CommRing R]
  {G : Cell U → Type v₁} [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)]
  {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
  {G' : Cell U → Type w₁} [∀ I, AddCommGroup (G' I)] [∀ I, Module R (G' I)]
  {ρ' : ∀ I J : Cell U, I.1 ⊆ J.1 → G' I →ₗ[R] G' J}

def mapH (φ : ∀ I, G I →ₗ[R] G' I) (hφ : ∀ I J h m, φ J (ρ I J h m) = ρ' I J h (φ I m)) (i : ℕ) :
    H G ρ i →ₗ[R] H G' ρ' i :=
  Submodule.mapQ _ _ ((mapC φ i).restrict (p := LinearMap.ker (d G ρ i)) (q := LinearMap.ker (d G' ρ' i))
      (fun s hs => by
        change d G' ρ' i (mapC φ i s) = 0
        rw [← mapC_d φ hφ, show d G ρ i s = 0 from hs, map_zero]))
    (by
      intro s hs
      cases i with
      | zero =>
        change (s : Cochain G 0) ∈ (⊥ : Submodule R _) at hs
        rw [Submodule.mem_bot] at hs
        change (mapC φ 0 s : Cochain G' 0) ∈ (⊥ : Submodule R _)
        rw [hs, map_zero]; exact Submodule.zero_mem _
      | succ i =>
        obtain ⟨t, hts⟩ := hs
        refine ⟨mapC φ i t, ?_⟩
        change d G' ρ' i (mapC φ i t) = mapC φ (i + 1) s
        rw [← mapC_d φ hφ, hts]
        rfl)

def hEquivOfEquiv (φ : ∀ I, G I ≃ₗ[R] G' I) (hφ : ∀ I J h m, φ J (ρ I J h m) = ρ' I J h (φ I m)) (i : ℕ) :
    H G ρ i ≃ₗ[R] H G' ρ' i :=
  have hψ : ∀ I J h m, (φ J).symm (ρ' I J h m) = ρ I J h ((φ I).symm m) := fun I J h m => by
    rw [LinearEquiv.symm_apply_eq, hφ, LinearEquiv.apply_symm_apply]
  LinearEquiv.ofLinearMap (mapH (fun I => (φ I).toLinearMap) hφ i)
    (mapH (fun I => (φ I).symm.toLinearMap) hψ i)
    (by
      refine Submodule.linearMap_qext _ (LinearMap.ext fun z => ?_)
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1
      exact Subtype.ext (funext fun I => (φ I.1).apply_symm_apply _))
    (by
      refine Submodule.linearMap_qext _ (LinearMap.ext fun z => ?_)
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1
      exact Subtype.ext (funext fun I => (φ I.1).symm_apply_apply _))

end Cech

section Zero

variable (k : Type u) [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} (x : Fin (N + 1) → Ω)
  (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]

def zeroFamily : SubFamily k x E where
  sub _ := ⊥
  mono _ _ _ _ hy := hy
  mem_iff I J h y := by
    simp only [Submodule.mem_bot]
    constructor
    · rintro rfl
      exact ⟨1, by simp, by simp⟩
    · rintro ⟨a, ha, hay⟩
      obtain ⟨b, hb⟩ := ha.exists_right_inv
      have hne : (a : Ω) ≠ 0 := by
        intro h0
        have h1 := congrArg (fun z : chartRing k x J => (z : Ω)) hb
        change (a : Ω) * _ = 1 at h1
        rw [h0, zero_mul] at h1
        exact zero_ne_one h1
      exact (smul_eq_zero.mp hay).resolve_left hne

end Zero

section Lemmas

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]


omit [Module k E] [IsScalarTower k Ω E] in
theorem twist_sub_eq_bot {F : SubSystem k x E} (hF : ∀ I, F.sub I = ⊥) (Q : SubSystem k x Ω) (I : Chart x) :
    (F.twist Q).sub I = ⊥ := by
  refine Submodule.span_eq_bot.mpr ?_
  rintro _ ⟨q, -, y, hy, rfl⟩
  rw [hF I, Submodule.mem_bot] at hy
  rw [hy, smul_zero]


omit [Module k E] [IsScalarTower k Ω E] in
theorem twistPows_sub_eq_bot {F : SubSystem k x E} (hF : ∀ I, F.sub I = ⊥) :
    ∀ (t : ℕ) (L : Fin t → SubSystem k x Ω) (n : Fin t → ℕ) (I : Chart x), (F.twistPows t L n).sub I = ⊥
  | 0, _, _, I => hF I
  | t + 1, _, _, I => twist_sub_eq_bot (fun I => twistPows_sub_eq_bot hF t _ _ I) _ I


omit [Module k E] [IsScalarTower k Ω E] in
theorem twist_idealSys_primeOf_sub (F : SubSystem k x E) (I : Chart x) :
    (F.twist (idealSys x (primeOf (S := k) x))).sub I = ⊥ := by
  refine Submodule.span_eq_bot.mpr ?_
  rintro _ ⟨q, hq, y, -, rfl⟩
  have hq0 : q = 0 := by
    have h0 : idealMod (primeOf (S := k) x) I = ⊥ := by
      refine Submodule.span_eq_bot.mpr ?_
      rintro _ ⟨f, s, e, hf, _, hfe, _, rfl⟩
      rw [(mem_primeOf_of_isHomogeneous x hfe).mp hf, zero_div]
    have hq' : q ∈ (⊥ : Submodule (chartRing k x I) Ω) := h0 ▸ hq
    exact (Submodule.mem_bot _).mp hq'
  rw [hq0, zero_smul]

theorem eulerCharQuot_of_bot (F₁ F₂ : SubSystem k x E) (h : ∀ I, F₂.sub I = ⊥) :
    eulerCharQuot k F₁ F₂ = eulerChar k F₁ := by
  have hq : ∀ I, SubSystem.quotSub F₁ F₂ I = ⊥ := fun I => by
    refine (Submodule.eq_bot_iff _).mpr fun y hy => Subtype.ext ?_
    have hy' : (y : E) ∈ F₂.sub I := hy
    rw [h I, Submodule.mem_bot] at hy'
    exact hy'
  let φ : ∀ I, F₁.sub I ≃ₗ[k] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) := fun I =>
    (Submodule.quotEquivOfEqBot _ (hq I)).symm
  have hφ : ∀ I J h m, φ J (F₁.res I J h m) = SubSystem.quotRes F₁ F₂ I J h (φ I m) := fun _ _ _ _ => rfl
  unfold eulerCharQuot eulerChar
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  exact ((Cech.hEquivOfEquiv φ hφ i).finrank_eq).symm

end Lemmas

theorem SnapperDevissage.proof (hQ : SnapperQuotDevissage.Statement.{u, v, w}) :
    SnapperDevissage.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F hF
  obtain ⟨r, pp, a, hpp, heq⟩ := hQ k Ω N x E F (zeroFamily k x E) hF (fun _ => bot_le)
    (primeOf (S := k) x) (fun f hf d => homogeneousComponent_mem_primeOf x hf d) le_rfl
    (fun I => (twist_idealSys_primeOf_sub F.toSubSystem I).le)
  refine ⟨r, pp, a, hpp, fun t L n c => ?_⟩
  rw [← heq t L n c]
  exact (eulerCharQuot_of_bot _ _ fun I =>
    twist_sub_eq_bot (twistPows_sub_eq_bot (fun _ => rfl) t _ n) _ I).symm

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperDiffPoly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

namespace SnapperDiffPoly

def numPt {t : ℕ} (n : Fin t → ℕ) (c : ℤ) : Fin (t + 1) → ℚ :=
  Fin.snoc (α := fun _ => ℚ) (fun j => (n j : ℚ)) (c : ℚ)

theorem eval_aeval_eq {K : Type} (x : K → ℚ) (σ : K → MvPolynomial K ℚ) (P : MvPolynomial K ℚ) :
    eval x (aeval σ P) = eval (fun k => eval x (σ k)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => rw [map_add (f := _), map_add (f := _), hp, hr, map_add (f := _)]
  | mul_X p j hp => simp only [map_mul, hp, aeval_X, eval_X]

theorem numPt_succ {t : ℕ} (n : Fin t → ℕ) (c : ℤ) :
    numPt n (c + 1) = numPt n c + Pi.single (Fin.last t) 1 := by
  funext k
  induction k using Fin.lastCases with
  | last => simp [numPt]
  | cast i => simp [numPt, Fin.castSucc_ne_last]

theorem numPt_update {t : ℕ} (n : Fin t → ℕ) (c : ℤ) (j : Fin t) :
    numPt (Function.update n j (n j + 1)) c = numPt n c + Pi.single j.castSucc 1 := by
  funext k
  induction k using Fin.lastCases with
  | last => simp [numPt, (Fin.castSucc_ne_last j).symm]
  | cast i =>
    by_cases h : i = j
    · subst h; simp [numPt]
    · simp [numPt, h, Function.update_apply]

theorem exists_fwd_antideriv {K : Type} [DecidableEq K] (D : ℕ) (k : K) (q : MvPolynomial K ℚ)
    (hq : q = 0 ∨ q.totalDegree < D) : ∃ P : MvPolynomial K ℚ, P.totalDegree ≤ D ∧
      ∀ x : K → ℚ, eval (x + Pi.single k 1) P - eval x P = eval x q := by
  rcases hq with rfl | hq
  · exact ⟨0, by simp, fun x => by simp⟩
  obtain ⟨P₀, hd, he⟩ := FieldNumbers.PolyOfDiffs.exists_antideriv k q
  refine ⟨aeval (fun i => X i - C ((Pi.single k (1 : ℚ) : K → ℚ) i)) P₀, ?_, fun x => ?_⟩
  · refine (FieldNumbers.PolyOfDiffs.totalDegree_aeval_le _ (fun i => ?_) P₀).trans (by omega)
    refine (totalDegree_sub _ _).trans ?_
    simp [totalDegree_X, totalDegree_C]
  · have h1 : (fun i => eval (x + Pi.single k 1) (X i - C ((Pi.single k (1 : ℚ) : K → ℚ) i))) = x := by
      funext i; simp
    have h2 : (fun i => eval x (X i - C ((Pi.single k (1 : ℚ) : K → ℚ) i))) = x - Pi.single k 1 := by
      funext i; simp
    rw [eval_aeval_eq, eval_aeval_eq, h1, h2, he x]

theorem isNumPolyLT_comp {t D : ℕ} {F G : (Fin t → ℕ) → ℤ → ℚ} (σ : Fin (t + 1) → MvPolynomial (Fin (t + 1)) ℚ)
    (hσ : ∀ i, (σ i).totalDegree ≤ 1) (a : (Fin t → ℕ) → ℤ → (Fin t → ℕ)) (b : (Fin t → ℕ) → ℤ → ℤ)
    (hab : ∀ n c, (fun i => eval (numPt n c) (σ i)) = numPt (a n c) (b n c))
    (hG : ∀ n c, G n c = F (a n c) (b n c)) (hF : IsNumPolyLT t D F) : IsNumPolyLT t D G := by
  obtain ⟨Q, hQ, hE⟩ := hF
  refine ⟨aeval σ Q, ?_, fun n c => ?_⟩
  · rcases hQ with rfl | hQ
    · left; simp
    · exact Or.inr ((FieldNumbers.PolyOfDiffs.totalDegree_aeval_le σ hσ Q).trans_lt hQ)
  · rw [hG, hE]
    change _ = eval (numPt n c) (aeval σ Q)
    rw [eval_aeval_eq, hab]
    rfl

theorem isNumPolyLT_shear {t D : ℕ} (ν : Fin t → ℤ) {F : (Fin t → ℕ) → ℤ → ℚ} (hF : IsNumPolyLT t D F) :
    IsNumPolyLT t D (fun n c => F n (c + ∑ i, ν i * (n i : ℤ))) := by
  refine isNumPolyLT_comp (Fin.snoc (α := fun _ => MvPolynomial (Fin (t + 1)) ℚ) (fun i => X i.castSucc)
    (X (Fin.last t) + ∑ i, C (ν i : ℚ) * X i.castSucc)) (fun k => ?_) (fun n _ => n)
    (fun n c => c + ∑ i, ν i * (n i : ℤ)) (fun n c => ?_) (fun n c => rfl) hF
  · induction k using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      refine (totalDegree_add _ _).trans (max_le (by rw [totalDegree_X]) ?_)
      refine totalDegree_finsetSum_le fun i _ => (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, totalDegree_X]
    | cast i => simp [totalDegree_X]
  · funext k
    induction k using Fin.lastCases with
    | last => simp [numPt]
    | cast i => simp [numPt]

theorem unit_steps {t D : ℕ} (g : (Fin t → ℕ) → ℤ → ℚ)
    (hc : IsNumPolyLT t D (fun n c => g n (c + 1) - g n c))
    (hj : ∀ j, IsNumPolyLT t D (fun n c => g (Function.update n j (n j + 1)) c - g n c)) :
    IsNumPolyLT t (D + 1) g := by
  classical
  obtain ⟨Qc, hQc, hcE⟩ := hc
  choose Q hQ hjE using hj
  obtain ⟨Pc, hPcd, hPc⟩ := exists_fwd_antideriv D (Fin.last t) Qc hQc
  choose P hPd hP using fun j : Fin t => exists_fwd_antideriv D j.castSucc (Q j) (hQ j)

  have hcol : ∀ c : ℤ, g 0 c - g 0 0 = eval (numPt 0 c) Pc - eval (numPt 0 0) Pc := by
    have step : ∀ c : ℤ, g 0 (c + 1) - g 0 c = eval (numPt 0 (c + 1)) Pc - eval (numPt 0 c) Pc := by
      intro c
      have h1 : g 0 (c + 1) - g 0 c = eval (numPt 0 c) Qc := hcE 0 c
      rw [h1, numPt_succ, hPc]
    intro c
    induction c using Int.induction_on with
    | zero => simp
    | succ i ih => have := step i; linarith
    | pred i ih =>
      have := step (-(i : ℤ) - 1)
      rw [sub_add_cancel] at this
      linarith

  have hrow : ∀ (i : Fin t) (v : Fin t → ℕ) (c : ℤ) (m : ℕ),
      g (Function.update v i m) c - g (Function.update v i 0) c =
        eval (numPt (Function.update v i m) c) (P i) - eval (numPt (Function.update v i 0) c) (P i) := by
    intro i v c m
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 : g (Function.update (Function.update v i m) i (Function.update v i m i + 1)) c -
          g (Function.update v i m) c = eval (numPt (Function.update v i m) c) (Q i) := hjE i _ c
      have h2 := hP i (numPt (Function.update v i m) c)
      rw [← numPt_update] at h2
      simp only [Function.update_self, Function.update_idem] at h1 h2
      linarith

  let tr : Finset (Fin t) → (Fin t → ℕ) → (Fin t → ℕ) := fun s n i => if i ∈ s then n i else 0
  let σ : Finset (Fin t) → Fin (t + 1) → MvPolynomial (Fin (t + 1)) ℚ := fun s =>
    Fin.snoc (α := fun _ => MvPolynomial (Fin (t + 1)) ℚ) (fun i => if i ∈ s then X i.castSucc else 0)
      (X (Fin.last t))
  have hσd : ∀ s k, (σ s k).totalDegree ≤ 1 := by
    intro s k
    induction k using Fin.lastCases with
    | last => simp [σ, totalDegree_X]
    | cast i => simp only [σ, Fin.snoc_castSucc]; split_ifs <;> simp [totalDegree_X]
  have hσe : ∀ s n c, (fun k => eval (numPt n c) (σ s k)) = numPt (tr s n) c := by
    intro s n c
    funext k
    induction k using Fin.lastCases with
    | last => simp [σ, numPt]
    | cast i => simp only [σ, tr, numPt, Fin.snoc_castSucc]; split_ifs <;> simp
  have key : ∀ s : Finset (Fin t), ∃ Γ : MvPolynomial (Fin (t + 1)) ℚ, Γ.totalDegree ≤ D ∧
      ∀ n c, g (tr s n) c = eval (numPt n c) Γ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨aeval (σ ∅) Pc + C (g 0 0 - eval (numPt 0 0) Pc), ?_, fun n c => ?_⟩
      · refine (totalDegree_add _ _).trans (max_le ?_ (by rw [totalDegree_C]; exact Nat.zero_le _))
        exact (FieldNumbers.PolyOfDiffs.totalDegree_aeval_le _ (hσd ∅) _).trans hPcd
      · have h0 : tr ∅ n = 0 := by funext i; simp [tr]
        rw [map_add (f := _), eval_C, eval_aeval_eq, hσe, h0]
        linarith [hcol c]
    | insert i s hi ih =>
      obtain ⟨Γ, hΓd, hΓ⟩ := ih
      refine ⟨Γ + (aeval (σ (insert i s)) (P i) - aeval (σ s) (P i)), ?_, fun n c => ?_⟩
      · refine (totalDegree_add _ _).trans (max_le hΓd ((totalDegree_sub _ _).trans (max_le ?_ ?_)))
        · exact (FieldNumbers.PolyOfDiffs.totalDegree_aeval_le _ (hσd _) _).trans (hPd i)
        · exact (FieldNumbers.PolyOfDiffs.totalDegree_aeval_le _ (hσd _) _).trans (hPd i)
      · have e1 : tr (insert i s) n = Function.update (tr s n) i (n i) := by
          funext k
          by_cases hk : k = i
          · subst hk; simp [tr]
          · simp [tr, hk]
        have e2 : tr s n = Function.update (tr s n) i 0 := by
          funext k
          by_cases hk : k = i
          · subst hk; simp [tr, hi]
          · simp [hk]
        have h := hrow i (tr s n) c (n i)
        rw [← e1, ← e2] at h
        rw [map_add (f := _), map_sub, eval_aeval_eq, eval_aeval_eq, hσe, hσe, ← hΓ n c]
        linarith
  obtain ⟨Γ, hΓd, hΓ⟩ := key Finset.univ
  refine ⟨Γ, Or.inr (by omega), fun n c => ?_⟩
  have h := hΓ n c
  have hu : tr Finset.univ n = n := by funext i; simp [tr]
  rw [hu] at h
  exact h

end SnapperDiffPoly

theorem SnapperDiffPoly.proof : SnapperDiffPoly.Statement := by
  intro t D f μ hc hj
  classical
  let L : (Fin t → ℕ) → ℤ := fun n => ∑ i, μ i * (n i : ℤ)
  have hL : ∀ n j, L (Function.update n j (n j + 1)) = L n + μ j := by
    intro n j
    simp only [L]
    have : ∀ i, μ i * ((Function.update n j (n j + 1) i : ℕ) : ℤ) =
        μ i * (n i : ℤ) + if i = j then μ j else 0 := by
      intro i
      by_cases h : i = j
      · subst h; simp; ring
      · simp [h]
    rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  let g : (Fin t → ℕ) → ℤ → ℚ := fun n c => f n (c + L n)
  have hgc : IsNumPolyLT t D (fun n c => g n (c + 1) - g n c) := by
    obtain ⟨Q, hQ, hE⟩ := SnapperDiffPoly.isNumPolyLT_shear μ hc
    refine ⟨Q, hQ, fun n c => ?_⟩
    rw [← hE n c]
    simp only [g, L]
    rw [add_right_comm]
  have hgj : ∀ j, IsNumPolyLT t D (fun n c => g (Function.update n j (n j + 1)) c - g n c) := by
    intro j
    obtain ⟨Q, hQ, hE⟩ := SnapperDiffPoly.isNumPolyLT_shear μ (hj j)
    refine ⟨Q, hQ, fun n c => ?_⟩
    rw [← hE n c]
    simp only [g]
    rw [hL n j, ← add_assoc]
  obtain ⟨Q, hQ, hE⟩ := SnapperDiffPoly.isNumPolyLT_shear (-μ) (SnapperDiffPoly.unit_steps g hgc hgj)
  refine ⟨Q, hQ, fun n c => ?_⟩
  rw [← hE n c]
  simp only [g, L, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  congr 1
  ring

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepTwoFilt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

theorem StepTwo.Filt.proof (h : PrimeFiltration.Exists.Statement.{u, v, w}) :
    StepTwo.Filt.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ M₁ M₂ hle J hJ
  classical
  obtain ⟨⟨F⟩, -⟩ := h S Ω N x (quotLaurent M₁ M₂) (quotLaurentGraded M₁ M₂) (quotLaurent_finite M₁ M₂)
    fun p hp y => quotLaurent_smul_eq_zero M₁ M₂ hp y
  have hrep : ∀ k, ∃ g : M₁.piece (F.deg k), quotIota M₁ M₂ (F.deg k) g = F.gen k :=
    fun k => LinearMap.mem_range.mp (F.gen_mem k)
  choose g hg using hrep
  have hstab : ∀ k : Fin (F.n + 1), IsProjStable M₁ M₂ (F.step k) := by
    intro k
    induction k using Fin.induction with
    | zero => rw [F.step_zero]; exact isProjStable_bot
    | succ k ih => rw [F.step_succ k, ← hg k]; exact isProjStable_sup ih (g k)
  have hfg : ∀ k : Fin (F.n + 1), ∃ (n : ℕ) (deg : Fin n → ℤ) (gen : Fin n → E),
      (∀ j, gen j ∈ filtPiece M₁ M₂ (F.step k) (deg j)) ∧
      ∀ c, filtPiece M₁ M₂ (F.step k) c ≤ Submodule.span S {z | ∃ (j : Fin n) (f : Poly S N) (e : ℕ),
        f.IsHomogeneous e ∧ (e : ℤ) + deg j = c ∧ z = aeval x f • gen j} := by
    intro k
    induction k using Fin.induction with
    | zero =>
      rw [F.step_zero]
      simp only [filtPiece_bot hle]
      exact M₂.fg
    | succ k ih =>
      obtain ⟨n, deg, gen, hmem, hspan⟩ := ih
      have hsup := filtPiece_sup (hstab k.castSucc) (g k)
      rw [F.step_succ k, ← hg k]
      refine ⟨n + 1, Fin.cons (F.deg k) deg, Fin.cons (g k : E) gen, fun j => ?_, fun c => ?_⟩
      · refine Fin.cases ?_ (fun j => ?_) j
        · rw [Fin.cons_zero, Fin.cons_zero, hsup]
          refine Submodule.mem_sup_right (Submodule.subset_span ⟨1, 0, isHomogeneous_one _ _, by simp, ?_⟩)
          rw [map_one, one_smul]
        · rw [Fin.cons_succ, Fin.cons_succ]
          exact filtPiece_mono le_sup_left _ (hmem j)
      · rw [hsup]
        refine sup_le ((hspan c).trans (Submodule.span_mono ?_)) (Submodule.span_mono ?_)
        · rintro _ ⟨j, f, e, hf, he, rfl⟩
          exact ⟨j.succ, f, e, hf, by rw [Fin.cons_succ]; exact he, by rw [Fin.cons_succ]⟩
        · rintro _ ⟨f, d, hf, hd, rfl⟩
          exact ⟨0, f, d, hf, by rw [Fin.cons_zero]; omega, by rw [Fin.cons_zero]⟩
  refine ⟨F.n, fun k => filtSub M₁ M₂ (F.step k) (hfg k), fun k => (g k : E), F.deg, F.prime, ?_, ?_,
    fun k => ⟨F.isPrime k, F.isHomogeneous k, ?_, ?_, ?_, ?_, ?_⟩⟩
  · refine FinGradedSub.eq_of_piece_eq (funext fun c => ?_)
    change filtPiece M₁ M₂ (F.step 0) c = _
    rw [F.step_zero, filtPiece_bot hle]
  · refine FinGradedSub.eq_of_piece_eq (funext fun c => ?_)
    change filtPiece M₁ M₂ (F.step (Fin.last F.n)) c = _
    rw [F.step_last, filtPiece_top]
  · exact fun p hp => F.ann_le k
      (Module.mem_annihilator.mpr fun y => quotLaurent_smul_eq_zero M₁ M₂ hp y)
  · exact fun f e hf he => F.ann_le k
      (Module.mem_annihilator.mpr fun y => quotLaurent_smul_eq_zero_of M₁ M₂ he (hJ f e hf he) y)
  · change ((g k : M₁.piece (F.deg k)) : E) ∈ filtPiece M₁ M₂ (F.step k.succ) (F.deg k)
    rw [coe_mem_filtPiece, hg k, F.step_succ]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · intro c
    change filtPiece M₁ M₂ (F.step k.succ) c = filtPiece M₁ M₂ (F.step k.castSucc) c ⊔ _
    rw [F.step_succ, ← hg k, filtPiece_sup (hstab k.castSucc) (g k) c]
  · intro f d hf
    rw [F.mem_prime, ← hg k, smul_quotIota M₁ M₂ hf]
    exact (coe_mem_filtPiece _).symm

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleEmbedNumbers
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

theorem VeryAmpleEmbed.Numbers.proof (hSecs : VeryAmpleSecs.Statement.{u, w})
    (hHilb : VeryAmpleHilbert.Statement.{u, w}) : VeryAmpleEmbed.Numbers.Statement.{u, w} := by
  intro k _ Ω _ _ N y Q r h hV n hZ
  exact ⟨VeryAmpleDim.proof k Ω N y n Q r h hZ hV,
    VeryAmpleDegree.proof VeryAmpleDim.proof hSecs hHilb k Ω N y n Q r h hZ hV⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

