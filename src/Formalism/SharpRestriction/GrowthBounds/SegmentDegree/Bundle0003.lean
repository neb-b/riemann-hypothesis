module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0002

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FactorialMulChooseEqProdRange
section
noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Finset

theorem sum_card_tuples (k n : ℕ) (hk : 0 < k) :
    (Finset.piAntidiag (Finset.univ : Finset (Fin k)) n).card = (n + k - 1).choose (k - 1) := by
  have h1 : (Finset.piAntidiag (Finset.univ : Finset (Fin k)) n).card =
      ((Finset.univ : Finset (Fin k)).finsuppAntidiag n).card := by
    refine Finset.card_bij' (fun f _ => Finsupp.equivFunOnFinite.symm f) (fun f _ => ⇑f) ?_ ?_ ?_ ?_ <;>
      simp [Finset.mem_finsuppAntidiag]
  rw [h1, Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Fintype.card_fin]
  have h2 : k + n - 1 = n + (k - 1) := by omega
  have h3 : n + k - 1 = n + (k - 1) := by omega
  rw [h2, h3]
  exact Nat.choose_symm_add

theorem sum_digit_count (k n P : ℕ) (hk : 0 < k) (hP : 0 < P) (S : Finset (Fin k → ℕ))
    (hS : ∀ v : Fin k → ℕ, (∀ c, v c < P) → ∑ c, v c ≤ n → (∑ c, v c) % P = n % P → v ∈ S) :
    (n + k - 1).choose (k - 1) ≤ ∑ v ∈ S, ((n - ∑ c, v c) / P + k - 1).choose (k - 1) := by
  classical
  rw [← sum_card_tuples k n hk]
  have hdec : ∀ w : Fin k → ℕ, ∑ c, w c = P * ∑ c, w c / P + ∑ c, w c % P := by
    intro w
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => (Nat.div_add_mod (w c) P).symm
  have hmaps : ∀ w ∈ Finset.piAntidiag (Finset.univ : Finset (Fin k)) n, (fun c => w c % P) ∈ S := by
    intro w hw
    have hw' : ∑ c, w c = n := by simpa using hw
    have hd := hdec w
    refine hS _ (fun c => Nat.mod_lt _ hP) ?_ ?_
    · rw [← hw', hd]; exact Nat.le_add_left _ _
    · rw [← hw', hd, Nat.mul_add_mod]
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_le_sum fun v _ => ?_
  rw [← sum_card_tuples k _ hk]
  refine Finset.card_le_card_of_injOn (fun w c => w c / P) ?_ ?_
  · intro w hw
    have hw1 := Finset.mem_filter.mp (Finset.mem_coe.mp hw)
    have hw' : ∑ c, w c = n := by simpa using hw1.1
    have hv : (fun c => w c % P) = v := hw1.2
    have hd := hdec w
    have hv' : ∑ c, w c % P = ∑ c, v c := by rw [← hv]
    simp only [Finset.mem_coe, Finset.mem_piAntidiag, Finset.mem_univ, implies_true, and_true]
    rw [← hw', hd, hv', Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hP]
  · intro w hw w' hw' hww
    have hw1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hw)).2
    have hw2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hw')).2
    funext c
    have e1 := congrFun hww c
    have e2 := congrFun (hw1.trans hw2.symm) c
    simp only at e1 e2
    rw [← Nat.div_add_mod (w c) P, ← Nat.div_add_mod (w' c) P, e1, e2]

theorem sum_label_count (k n P : ℕ) (hk : 0 < k) (hP : 0 < P) (hn : k * P ≤ n) (S : Finset (Fin k → ℕ))
    (hS : ∀ v : Fin k → ℕ, (∀ c, v c < P) → ∑ c, v c ≤ n → (∑ c, v c) % P = n % P → v ∈ S) :
    P ^ (k - 1) ≤ S.card := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have hc : (Finset.univ : Finset (Fin m → Fin P)).card = P ^ (m + 1 - 1) := by
    simp
  rw [← hc]
  let g : (Fin m → Fin P) → (Fin (m + 1) → ℕ) := fun u =>
    Fin.cons ((n + (P - 1) * ∑ i, (u i : ℕ)) % P) (fun i => (u i : ℕ))
  refine Finset.card_le_card_of_injOn g ?_ ?_
  · intro u _
    have hlt : ∀ c, g u c < P := by
      intro c
      refine Fin.cases ?_ (fun i => ?_) c
      · simp only [g, Fin.cons_zero]; exact Nat.mod_lt _ hP
      · simp only [g, Fin.cons_succ]; exact (u i).isLt
    refine Finset.mem_coe.mpr (hS _ hlt ?_ ?_)
    · calc ∑ c, g u c ≤ ∑ _c : Fin (m + 1), P := Finset.sum_le_sum fun c _ => (hlt c).le
        _ = (m + 1) * P := by simp
        _ ≤ n := hn
    · rw [Fin.sum_univ_succ]
      simp only [g, Fin.cons_zero, Fin.cons_succ]
      set s := ∑ i, (u i : ℕ)
      rw [Nat.mod_add_mod]
      have : n + (P - 1) * s + s = n + P * s := by
        obtain ⟨P', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hP.ne'
        simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
        ring
      rw [this, Nat.add_mul_mod_self_left]
  · intro u _ u' _ huu
    funext i
    have := congrFun huu i.succ
    simp only [g, Fin.cons_succ] at this
    exact Fin.ext this

theorem factorial_mul_choose_eq_prod_range (x M : ℕ) :
    ((M.factorial : ℕ) : ℝ) * (((x + M).choose M : ℕ) : ℝ) = ∏ l ∈ Finset.range M, ((x : ℝ) + 1 + l) := by
  have h := Nat.ascFactorial_eq_factorial_mul_choose x M
  rw [Nat.ascFactorial_eq_prod_range] at h
  have h' : ((∏ i ∈ Finset.range M, (x + 1 + i) : ℕ) : ℝ) = ((M.factorial * (x + M).choose M : ℕ) : ℝ) := by
    rw [h]
  push_cast at h'
  rw [← h']

theorem choose_add_mul_one_sub_le_pow_mul_choose_add (x y M : ℕ) (s θ : ℝ) (h1 : θ ≤ 1)
    (h : ∀ l < M, ((y : ℝ) + 1 + l) * (1 - θ) ≤ s * ((x : ℝ) + 1 + l)) :
    (((y + M).choose M : ℕ) : ℝ) * (1 - M * θ) ≤ s ^ M * (((x + M).choose M : ℕ) : ℝ) := by
  have hf : (0 : ℝ) < (M.factorial : ℝ) := by exact_mod_cast M.factorial_pos
  have hb : 1 - (M : ℝ) * θ ≤ (1 - θ) ^ M := by
    have := one_add_mul_le_pow (a := -θ) (by linarith) M
    calc 1 - (M : ℝ) * θ = 1 + (M : ℝ) * (-θ) := by ring
      _ ≤ (1 + -θ) ^ M := this
      _ = (1 - θ) ^ M := by ring_nf
  have hy : (0 : ℝ) ≤ (((y + M).choose M : ℕ) : ℝ) := Nat.cast_nonneg _
  refine le_trans (mul_le_mul_of_nonneg_left hb hy) ?_
  refine le_of_mul_le_mul_left ?_ hf
  have e1 : (M.factorial : ℝ) * ((((y + M).choose M : ℕ) : ℝ) * (1 - θ) ^ M) =
      ∏ l ∈ Finset.range M, (((y : ℝ) + 1 + l) * (1 - θ)) := by
    rw [← mul_assoc, factorial_mul_choose_eq_prod_range, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have e2 : (M.factorial : ℝ) * (s ^ M * (((x + M).choose M : ℕ) : ℝ)) =
      ∏ l ∈ Finset.range M, (s * ((x : ℝ) + 1 + l)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← factorial_mul_choose_eq_prod_range]
    ring
  rw [e1, e2]
  refine Finset.prod_le_prod₀ (fun l _ => ?_) fun l hl => h l (Finset.mem_range.mp hl)
  have : (0 : ℝ) ≤ (y : ℝ) + 1 + l := by positivity
  exact mul_nonneg this (by linarith)

theorem prod_range_shift_of_periodic (φ : ℤ → ℝ) (J : ℕ) (hJ : 1 ≤ J) (hφ : ∀ j, φ (j + J) = φ j) :
    ∏ j ∈ Finset.range J, φ ((j : ℤ) + 1) = ∏ j ∈ Finset.range J, φ (j : ℤ) := by
  obtain ⟨J', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : J ≠ 0)
  rw [Finset.prod_range_succ, Finset.prod_range_succ' (fun j : ℕ => φ (j : ℤ))]
  have h := hφ 0
  push_cast at h ⊢
  rw [zero_add] at h
  rw [h]

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.GoodPathWeight
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)


open Classical in
def restr (j : ℤ) (b : ℤ → ℕ) : ℤ → ℕ := fun x => if x ∈ X.toLate j then b x else 0


open Classical in
def Bdeg (j : ℤ) (b : ℤ → ℕ) (x : ℤ) : ℕ :=
  if X.F.IsW j x then (X.Bw p K j x - (X.m0 K : ℤ)).toNat else b x

def beS (j : ℤ) (b : ℤ → ℕ) : ℕ := ∑ x ∈ (X.F.letters j).filter (· < X.F.fr j 0), X.Bdeg p K j b x

structure IsPATH (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ)
    (dd : Fin (segN X.F j) → ℕ) : Prop where
  path : ∃ P : PPath (r + K) (segN X.F j) (segLL X.F j) dd, P.mu = μ
  degs : ∀ i, segE X.F j i < X.F.fr j 0 → dd i = X.Bdeg p K j b (segE X.F j i)
  head : ∀ (i : Fin (segN X.F j)) (i' : Fin r), segE X.F j i = X.F.fr j i'.val →
    ∀ m : Fin (r + K), m.val ≤ i'.val → μ i.succ m = (X.beS p K j b : ℤ)

def IsGood [NeZero r] (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ) : Prop :=
  ∀ i : Fin (segN X.F j), ¬ X.F.IsW j (segE X.F j i) →
    X.thc p K j b (segE X.F j i) ≤ ((plPart μ i.castSucc (lastIdx r) : ℤ) : ℝ) ∧
    (Even (segE X.F j i) →
      ((∑ c, (tanPart μ i.succ c - tanPart μ i.castSucc c) : ℤ) : ℝ) ≤ X.oc p K j (segE X.F j i)) ∧
    (¬ Even (segE X.F j i) →
      ((∑ c, (plPart μ i.castSucc c - plPart μ i.succ c) : ℤ) : ℝ) ≤ X.oc p K j (segE X.F j i))

def Tset [NeZero r] (j : ℤ) (b : ℤ → ℕ) : Type :=
  {q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) //
    ∃ dd, X.IsPATH p K j b q.1 dd ∧ X.IsGood p K j b q.1 ∧ IsSt (tanPart q.1) q.2}

def Idx [NeZero r] (j : ℤ) (b : ℤ → ℕ) : Type :=
  {q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ) //
    ∃ dd, X.IsPATH p K j b q.1 dd ∧ X.IsGood p K j b q.1 ∧ IsSt (tanPart q.1) q.2.1 ∧
      (∀ v, q.2.2 v + 2 * X.beS p K j b < X.Qc p K j) ∧
      ∀ (i : Fin (segN X.F j)) (i' : Fin r), segE X.F j i = X.F.fr j i'.val →
        dd i + ∑ c, q.2.2 (i', c) = b (X.F.fr j i'.val)}


omit [NeZero n'] in
def Dw (O : Type) [CommRing O] (j : ℤ) : MvPolynomial (ℤ × Fin r) O :=
  Matrix.det (Matrix.of fun a c : Fin r => (MvPolynomial.X (X.F.fr (j - 1) a.val, c) : MvPolynomial (ℤ × Fin r) O))

def famEl [NeZero r] (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ)) : SegRing O r K :=
  plEmb O r K (X.Dw O j ^ X.m0 K *
      (∏ i : Fin r, MvPolynomial.X (X.F.fr (j - 1) i.val, (0 : Fin r)) ^
        ((b (X.F.fr (j - 1) i.val) : ℤ) - X.Bw p K j (X.F.fr (j - 1) i.val)).toNat) *
      ∏ v : Fin r × Fin r, MvPolynomial.X (X.F.fr j v.1.val, v.2) ^ q.2.2 v) *
    segRen X.F j O (r + K) (PsiPl O (plPart q.1) (Ican (plPart q.1)) * PsiTan O (tanPart q.1) q.2.1)

def BOK (j : ℤ) (b : ℤ → ℕ) : Prop :=
  (∀ x, x ∉ X.F.letters j → b x = 0) ∧
  (∀ x ∈ X.F.letters j, X.F.IsW j x → X.Bw p K j x ≤ (b x : ℤ)) ∧ X.AdmLL p K j b

end Dat

def RestMem (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b → ∀ q : X.Idx p K j (X.restr j b), X.famEl p K O j b q.1 ∈ X.Mj p K O j b

def RestInd (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b →
      LinearIndependent O fun q : X.Idx p K j (X.restr j b) => X.famEl p K O j b q.1

def RestFin : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (j : ℤ) (b : ℤ → ℕ), (∀ x, x ∉ X.F.letters j → b x = 0) →
    Module.Finite O (X.Mj p K O j b)

def GoodPathWeight (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r),
    X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.AdmLL p K j b → Finite (X.Tset p K j (X.restr j b)) ∧
      (1 - 1 / X.a ^ (X.Ns ^ 2)) *
        (∏ x ∈ X.F.LLset j, ((Nat.choose (b x + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)) *
        (∏ i : Fin r, ((Nat.choose ((X.Bw p K j (X.F.fr (j - 1) i.val) - (X.m0 K : ℤ)).toNat + (r + K) - 1)
          (r + K - 1) : ℕ) : ℝ)) ≤ (Nat.card (X.Tset p K j (X.restr j b)) : ℝ)


open Classical in
def RestMon (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r),
    X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.AdmLL p K j b → Finite (X.Tset p K j (X.restr j b)) → ∀ ρ : Fin r → ℕ,
      (Nat.card (X.Tset p K j (X.restr j b)) : ℝ) *
          (((X.Qc p K j : ℕ) : ℝ) ^ (r - 1) * max 0 (1 - (r : ℝ) / (2 * X.Y))) ^ r ≤
        ∑ e ∈ Fintype.piFinset fun i : Fin r =>
          (Finset.range (r * X.Qc p K j)).filter fun e => e % X.Qc p K j = ρ i % X.Qc p K j,
            (Nat.card (X.Idx p K j (X.restr j (X.setTau j b e))) : ℝ)

theorem restSeg_of (C₀ : ℝ) (hM : RestMem C₀) (hI : RestInd C₀) (hF : RestFin) (hT : GoodPathWeight C₀) (hN : RestMon C₀) :
    RestSeg C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j
  refine ⟨fun b => (Nat.card (X.Idx p K j (X.restr j b)) : ℝ), fun b => Nat.cast_nonneg _, ?_, ?_, ?_⟩
  · intro b b' hbb
    have : X.restr j b = X.restr j b' := by
      funext x
      unfold Dat.restr
      split_ifs with hx
      · exact hbb x hx
      · rfl
    simp only [this]
  · intro b h0 hW hA
    have hB : X.BOK p K j b := ⟨h0, hW, hA⟩
    have hfin := hF p n' r K X O j b h0
    have hli := hI p n' r K X O S hX hLa hk j b hB
    have hmem := hM p n' r K X O S hX hLa hk j b hB
    have hli' : LinearIndependent O
        (fun q : X.Idx p K j (X.restr j b) => (⟨X.famEl p K O j b q.1, hmem q⟩ : X.Mj p K O j b)) := by
      refine LinearIndependent.of_comp (X.Mj p K O j b).subtype ?_
      exact hli
    have hfinI : Finite (X.Idx p K j (X.restr j b)) := hli'.finite
    have := Fintype.ofFinite (X.Idx p K j (X.restr j b))
    have h := hli'.fintype_card_le_finrank
    beta_reduce
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast h
  · intro b hA ρ
    obtain ⟨hfin, hT1⟩ := hT p n' r K X hX hLa hk j b hA
    refine le_trans ?_ (hN p n' r K X hX hLa hk j b hA hfin ρ)
    unfold Dat.segBound
    exact mul_le_mul_of_nonneg_right hT1 (by positivity)

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SegmentReductionOfColumnWords
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

def ColumnWordReductionLifts (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ) (e : ℤ × Fin (r + K) →₀ ℕ), X.IsEll p K j e → X.Step2 p K j b →
    ∀ q ∈ segPairs X.F j K (fun _ => (X.m0 K : ℤ)) (X.thc p K j b) (X.oc p K j),
    ∀ I' I'', IsSt q.1 I' → IsSt q.2 I'' →
      ∃ x ∈ X.XXs p K O j, MvPolynomial.map (IsLocalRing.residue O) x =
        MvPolynomial.map (IsLocalRing.residue O)
          (X.zSeg p K O j (segRen X.F j O (r + K) (PsiPl O q.1 I' * PsiTan O q.2 I'')) e)

theorem map_suppProj {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {σ : Type} (s : Set (σ →₀ ℕ))
    (A : MvPolynomial σ R) : MvPolynomial.map f (suppProj R s A) = suppProj S s (MvPolynomial.map f A) := by
  classical
  ext m
  rw [coeff_map, coeff_suppProj, coeff_suppProj, coeff_map]
  split_ifs <;> simp

theorem plEmb_Pol {R : Type} [CommRing R] (r K : ℕ) {d : ℤ → ℕ} {A : MvPolynomial (ℤ × Fin r) R}
    (hA : A ∈ Pol R r d) : plEmb R r K A ∈ Pol R (r + K) d := by
  classical
  have hf : Function.Injective (fun v : ℤ × Fin r => (v.1, Fin.castAdd K v.2)) := by
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Fin.castAdd_injective _ _ h.2)
  rw [mem_Pol_iff] at hA ⊢
  intro m hm i
  unfold plEmb at hm
  rw [support_rename_of_injective hf] at hm
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hm
  rw [← hA u hu i]
  unfold multideg
  rw [Fin.sum_univ_add]
  have z1 : ∀ c : Fin r, Finsupp.mapDomain (fun v : ℤ × Fin r => (v.1, Fin.castAdd K v.2)) u (i, Fin.castAdd K c)
      = u (i, c) := fun c => Finsupp.mapDomain_apply_of_injective hf u (i, c)
  have z2 : ∀ c : Fin K, Finsupp.mapDomain (fun v : ℤ × Fin r => (v.1, Fin.castAdd K v.2)) u (i, Fin.natAdd r c)
      = 0 := by
    intro c
    refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨v, hv⟩
    simp only [Prod.mk.injEq] at hv
    have := congrArg Fin.val hv.2
    simp at this
    omega
  simp only [z1, z2, Finset.sum_const_zero, add_zero]

theorem nmEmb_Pol {R : Type} [CommRing R] (r K : ℕ) {d : ℤ → ℕ} {A : MvPolynomial (ℤ × Fin K) R}
    (hA : A ∈ Pol R K d) : nmEmb R r K A ∈ Pol R (r + K) d := by
  classical
  have hf : Function.Injective (fun v : ℤ × Fin K => (v.1, Fin.natAdd r v.2)) := by
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Fin.natAdd_injective _ _ h.2)
  rw [mem_Pol_iff] at hA ⊢
  intro m hm i
  unfold nmEmb at hm
  rw [support_rename_of_injective hf] at hm
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hm
  rw [← hA u hu i]
  unfold multideg
  rw [Fin.sum_univ_add]
  have z1 : ∀ c : Fin K, Finsupp.mapDomain (fun v : ℤ × Fin K => (v.1, Fin.natAdd r v.2)) u (i, Fin.natAdd r c)
      = u (i, c) := fun c => Finsupp.mapDomain_apply_of_injective hf u (i, c)
  have z2 : ∀ c : Fin r, Finsupp.mapDomain (fun v : ℤ × Fin K => (v.1, Fin.natAdd r v.2)) u (i, Fin.castAdd K c)
      = 0 := by
    intro c
    refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨v, hv⟩
    simp only [Prod.mk.injEq] at hv
    have := congrArg Fin.val hv.2
    simp at this
    omega
  simp only [z1, z2, Finset.sum_const_zero, zero_add]

theorem geR_mono {v v' : WithTop ℤ} {t : ℝ} (h : geR v t) (hv : v ≤ v') : geR v' t := by
  intro z hz
  rw [hz] at hv
  induction v using WithTop.recTopCoe with
  | top => simp at hv
  | coe z0 =>
    have h1 : z0 ≤ z := WithTop.coe_le_coe.mp hv
    exact (h z0 rfl).trans (by exact_mod_cast h1)

theorem XX'_polComp (O : Type) [CommRing O] (r K : ℕ) [NeZero r] [NeZero K] {n' : ℕ} [NeZero n'] (F : Frames n' r)
    (j : ℤ) (m : ℤ → ℤ) (th o : ℤ → ℝ) (β : ℤ → ℕ) {x : SegRing O r K} (hx : x ∈ XX' O r K F j m th o) :
    polComp O (r + K) β x ∈ XX' O r K F j m th o := by
  classical
  obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
  have hx2' := hx2
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · clear hx hx2 hx2'
    induction hx1 using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨A, G, M, hA, hG, hc, rfl⟩ := hy
      obtain ⟨T', hT'⟩ := exists_sum_polComp O r A
      obtain ⟨T'', hT''⟩ := exists_sum_polComp O K G
      have hsum : plEmb O r K A * nmEmb O r K G = ∑ d' ∈ T', ∑ d'' ∈ T'',
          plEmb O r K (polComp O r d' A) * nmEmb O r K (polComp O K d'' G) := by
        conv_lhs => rw [hT', hT'']
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, map_sum, Finset.sum_mul_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hsum, map_sum]
      refine Submodule.sum_mem _ fun d' _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Submodule.sum_mem _ fun d'' _ => ?_
      have hP : plEmb O r K (polComp O r d' A) * nmEmb O r K (polComp O K d'' G) ∈ Pol O (r + K) (d' + d'') :=
        hom_Pol_mul O (plEmb_Pol r K (polComp_mem_Pol O r d' A)) (nmEmb_Pol r K (polComp_mem_Pol O K d'' G))
      by_cases hd : β = d' + d''
      · rw [hd, polComp_of_mem O _ _ _ hP]
        refine Submodule.subset_span ⟨_, _, M, polComp_mem_supported O r d' A _ hA,
          polComp_mem_supported O K d'' G _ hG, fun x hx hW => ?_, rfl⟩
        obtain ⟨cE, cO, cR⟩ := hc x hx hW
        exact ⟨fun he => ⟨(lowest_degree_compose_le _ _ d'' G).trans (cE he).1, (cE he).2.trans (valS_le_polComp _ _ d' A)⟩,
          fun he => ⟨(lowest_degree_compose_le _ _ d'' G).trans (cO he).1, (cO he).2.trans (valS_le_polComp _ _ d' A)⟩,
          geR_mono cR (valS_le_polComp _ _ d' A)⟩
      · rw [polComp_of_ne O _ _ _ _ hP hd]
        exact Submodule.zero_mem _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy
  · rw [mem_restrictSupport_iff] at hx2 ⊢
    intro mm hmm
    exact hx2 (Finset.mem_coe.mpr (suppProj_support_subset O _ x (Finset.mem_coe.mp hmm)))

theorem zSeg_add {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) (O : Type) [CommRing O] (j : ℤ)
    (y1 y2 : SegRing O r K) (e : ℤ × Fin (r + K) →₀ ℕ) :
    X.zSeg p K O j (y1 + y2) e = X.zSeg p K O j y1 e + X.zSeg p K O j y2 e := by
  unfold Dat.zSeg; rw [map_add (f := _)]; ring

theorem zSeg_smul {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) (O : Type) [CommRing O] (j : ℤ) (c : O)
    (y : SegRing O r K) (e : ℤ × Fin (r + K) →₀ ℕ) :
    X.zSeg p K O j (c • y) e = c • X.zSeg p K O j y e := by
  unfold Dat.zSeg; rw [map_smul, mul_smul_comm, smul_mul_assoc]

theorem segment_reduction_of_column_words (D : Formalism.BasicNotions.D7) (hB12 : NestedTypeBound D) (C₀ : ℝ) (hW : ColumnWordReductionLifts C₀) : SegmentReductionLiftsMultihomogeneous C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b y e hy he h2 β hβ
  have : Fact p.Prime := ⟨hX.prime⟩
  have hseg : segN X.F j + r ≤ K := le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK
  have h1 := (hB12 p O S n' r K X.F X.L₁ X.N₁ j (fun _ => (X.m0 K : ℤ)) (X.thc p K j b) (X.oc p K j) hX.valid hseg
    (fun _ => Int.natCast_nonneg _)).1
  have hy1 : y ∈ XX' O r K X.F j (fun _ => (X.m0 K : ℤ)) (X.thc p K j b) (X.oc p K j) := hy.1.1
  rw [h1] at hy1
  unfold Formalism.MainNotions.CovariantDegrees.XXZ at hy1
  rw [Submodule.map_span] at hy1
  have key : ∃ x ∈ X.XXs p K O j, MvPolynomial.map (IsLocalRing.residue O) x =
      MvPolynomial.map (IsLocalRing.residue O) (X.zSeg p K O j y e) := by
    clear hβ hy
    induction hy1 using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨_, ⟨q, hq, I', I'', hI', hI'', rfl⟩, rfl⟩ := hy
      exact hW p n' r K X O S hX hLa hk j b e he h2 q hq I' I'' hI' hI''
    | zero => exact ⟨0, Submodule.zero_mem _, by simp [Dat.zSeg]⟩
    | add y z _ _ hy hz =>
      obtain ⟨x1, hx1, e1⟩ := hy
      obtain ⟨x2, hx2, e2⟩ := hz
      exact ⟨x1 + x2, Submodule.add_mem _ hx1 hx2, by rw [zSeg_add, map_add (f := _), map_add (f := _), e1, e2]⟩
    | smul c y _ hy =>
      obtain ⟨x1, hx1, e1⟩ := hy
      refine ⟨c • x1, Submodule.smul_mem _ c hx1, ?_⟩
      rw [zSeg_smul, smul_eq_C_mul, smul_eq_C_mul, map_mul, map_mul, e1]
  obtain ⟨x, hx, hxe⟩ := key
  refine ⟨polComp O (r + K) β x, XX'_polComp O r K X.F j _ _ _ β hx, polComp_mem_Pol O _ β x, ?_⟩
  unfold polComp
  rw [map_suppProj, hxe, ← map_suppProj]
  congr 1
  exact polComp_of_mem O _ β _ hβ

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

