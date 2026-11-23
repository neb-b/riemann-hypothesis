module

public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0012
public import Formalism.SharpRestriction.GrowthBounds.PolBridge

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.RestSegCore
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def segMon (O : Type) [CommRing O] [IsDomain O] (X : Loc) (j : Fin (numSeg X.TT)) (A : MonH X) : RHH O X :=
  (∏ i : Fin (segS X.TT j), ∏ c : Fin (X.m + 1),
    (MvPolynomial.X ((topOdd X j i, true), c) ^ A ((topOdd X j i, true), c) *
      MvPolynomial.X ((topOdd X j i, false), c) ^ A ((topOdd X j i, false), c))) *
  ∏ c : Fin (X.m + 1), (MvPolynomial.X ((topEnd X j, true), c) ^ A ((topEnd X j, true), c) *
      MvPolynomial.X ((topEnd X j, false), c) ^ A ((topEnd X j, false), c))

def chW {s : ℕ} (i : Fin s) : Fin (2 * s + 1) := ⟨2 * i.val, by omega⟩
def chE {s : ℕ} (i : Fin s) : Fin (2 * s + 1) := ⟨2 * i.val + 1, by omega⟩
def chU (s : ℕ) : Fin (2 * s + 1) := ⟨2 * s, by omega⟩

def nuSeg (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (ju : Fin (X.seg C0 CE1 CE2 j).t → ℕ) (jp : ℕ)
    (du : Fin (2 * segS X.TT j + 1) → ℕ) (A : MonH X) : ℕ :=
  (∑ i : Fin (segS X.TT j), ((X.seg C0 CE1 CE2 j).P X.p i * (jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i)) +
    (∑ c : Fin X.m, A ((topOdd X j i, true), c.succ)) + A ((topOdd X j i, false), 0))) +
  (jp + du (chU _) + ∑ c : Fin X.m, A ((topEnd X j, true), c.succ))

def SegCoreAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) →
    ∀ n : ℕ, 1 ≤ n → n ≤ X.c →
    ∀ β : GlobalTheory X, (∀ j, BLk C0 Cde CE1 CE2 X (((X.c - n : ℕ) : ℝ) * ka1 X) j (β j)) →
    ∀ (L : LvDat C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β),
    ∀ e : ℕ, 1 ≤ e → e < n →
    ∀ (j : Fin (numSeg X.TT)) (ju : Fin (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.t → ℕ), (∀ i, ju i ≤ L.lv j i) →
    ∀ (Gu : MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)) (du : Fin (2 * segS X.TT j + 1) → ℕ),
      Gu ∈ IntPol O (Fin (2 * segS X.TT j + 1) × Fin X.m) →
      Gu ∈ Pol (KK O) X.m du → (∀ a, du a ≤ (L.LL j).deg a) →
      (∀ k, Gu ∈ YCond (KK O) (r := X.m) (L.LL j) ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.J k)
        ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.thr k + (((X.N1 * e : ℕ) : ℤ) : WithTop ℤ))) →
    ∀ A : MonH X,

      (∀ i : Fin (segS X.TT j), (β j).rz i 0 + (X.seg C0 CE1 CE2 j).P X.p i *
          (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i -
            (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).w i else (β j).o i)) ≤
          A ((topOdd X j i, true), 0) + X.p ^ X.G' * e) →
      (∀ i : Fin (segS X.TT j), ∑ c : Fin X.m, (A ((topOdd X j i, true), c.succ) - (β j).rz i c.succ) ≤ X.p ^ X.G' * e) →
      (∀ i : Fin (segS X.TT j), A ((topOdd X j i, false), 0) ≤ (β j).ry i 0 + (X.seg C0 CE1 CE2 j).P X.p i *
          (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).sg i else 0) + X.p ^ X.G' * e) →
      (∑ c : Fin X.m, A ((topEnd X j, true), c.succ) ≤ X.p ^ X.G' * e) →
      A ((topEnd X j, false), 0) = 0 → (∀ c : Fin X.m, A ((topEnd X j, false), c.succ) = L.γ j c) →

      (∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).P X.p i * (jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i)) +
        ∑ c, A ((topOdd X j i, true), c) = (X.seg C0 CE1 CE2 j).bTop i) →
      (∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).P X.p i * (jE (X.seg C0 CE1 CE2 j) ju i.val + du (chE i)) +
        ∑ c, A ((topOdd X j i, false), c) = segATop X.TT X.aT j i) →
      (L.jp j + du (chU _) + ∑ c, A ((topEnd X j, true), c) = segAPlus X.TT X.aT j) →
      ∃ b' : SegBlock (segS X.TT j) X.m,
        BLk C0 Cde CE1 CE2 X (((X.c - (n - e) : ℕ) : ℝ) * ka1 X) j b' ∧
        blockOrd X.p (X.seg C0 CE1 CE2 j) b' = nuSeg C0 CE1 CE2 X j ju (L.jp j) du A ∧
        ∃ u ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j)
            (mm + ((n - e : ℕ) : ℝ) * ka1 X) b').SSZ O (r := X.m),
          L.head O j ju Gu * segMon O X j A = ioBlock (KK O) X.p C0 CE1 CE2 X j b' u

def RestSegCore : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => SegCoreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.YcondFactor
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def mdHom (X : Loc) (l : X.TT × Bool) : MonH X →+ ℕ where
  toFun := fun m => multideg m l
  map_zero' := by simp [multideg]
  map_add' := fun a b => multideg_add a b l

def ndHom (X : Loc) : MonH X →+ ℕ where
  toFun := ndM X
  map_zero' := Formalism.MainNotions.LemmaBAlt.degUS_zero _ _
  map_add' := ndM_add X

section Hom

variable {X : Loc} {O : Type} [CommRing O] [IsDomain O]

def HomW (φ : MonH X →+ ℕ) (d : ℕ) (P : RHH O X) : Prop := ∀ m ∈ P.support, φ m = d

theorem HomW.mul {φ : MonH X →+ ℕ} {d d' : ℕ} {P Q : RHH O X} (hP : HomW φ d P) (hQ : HomW φ d' Q) :
    HomW φ (d + d') (P * Q) := by
  classical
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul P Q hm)
  rw [map_add (f := _), hP a ha, hQ b hb]

theorem HomW.one (φ : MonH X →+ ℕ) : HomW φ 0 (1 : RHH O X) := by
  classical
  intro m hm
  rw [mem_support_iff, coeff_one] at hm
  by_cases h : 0 = m
  · rw [← h, map_zero]
  · rw [if_neg h] at hm; exact absurd rfl hm

theorem HomW.pow {φ : MonH X →+ ℕ} {d : ℕ} {P : RHH O X} (hP : HomW φ d P) (u : ℕ) : HomW φ (u * d) (P ^ u) := by
  induction u with
  | zero => simpa using HomW.one (O := O) φ
  | succ u ih =>
    rw [pow_succ, Nat.succ_mul]
    exact ih.mul hP

theorem HomW.prod {φ : MonH X →+ ℕ} {κ : Type} (s : Finset κ) (d : κ → ℕ) (P : κ → RHH O X)
    (h : ∀ a ∈ s, HomW φ (d a) (P a)) : HomW φ (∑ a ∈ s, d a) (∏ a ∈ s, P a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HomW.one (O := O) φ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem HomW.monomial (φ : MonH X →+ ℕ) (M : MonH X) (c : KK O) : HomW φ (φ M) (monomial M c : RHH O X) := by
  classical
  intro m hm
  have := support_monomial_subset hm
  rw [Finset.mem_singleton] at this
  rw [this]

theorem mem_Pol_iffW {d : X.TT × Bool → ℕ} {P : RHH O X} :
    P ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) d ↔ ∀ l, HomW (mdHom X l) (d l) P := by
  unfold Pol
  rw [mem_restrictSupport_iff]
  constructor
  · intro h l m hm
    exact h (Finset.mem_coe.2 hm) l
  · intro h m hm l
    exact h l m (Finset.mem_coe.1 hm)

theorem mono_sum {ι : Type} (s : Finset ι) (n : ι → ℕ) (a : ι → MonH X) :
    (monomial (∑ i ∈ s, n i • a i) (1 : KK O) : RHH O X) = ∏ i ∈ s, (monomial (a i) (1 : KK O) : RHH O X) ^ n i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, ← ih, monomial_pow, one_pow, monomial_mul, one_mul]

theorem hom_total (φ : MonH X →+ ℕ) {κ : Type} [Fintype κ] (sg : κ → RHH O X) (d : κ → ℕ) (h : ∀ a, HomW φ (d a) (sg a))
    {sgR : RHH O X} {dR : ℕ} (hR : HomW φ dR sgR) (mult u : κ → ℕ) (M : MonH X) :
    HomW φ (dR + ∑ a, (mult a - u a) * d a + φ M) (sgR * (∏ a, sg a ^ (mult a - u a)) * monomial M 1) :=
  (hR.mul (HomW.prod _ _ _ fun a _ => (h a).pow _)).mul (HomW.monomial φ M 1)

end Hom


open Formalism.MainNotions.G.PolBridge Formalism.MainNotions.G.GLWeightTheory in
theorem ycond_factor (D : Formalism.BasicNotions.D7) {K : Type} [Field K] [CharZero K] {N r : ℕ} [NeZero r] (LL : ChainLetters N) (jj : ℕ)
    (M : WithTop ℤ) (Gu Gr : MvPolynomial (Fin N × Fin r) K) (dr : Fin N → ℕ) (hr : Gr ∈ Pol K r dr) (hne : Gr ≠ 0)
    (h : Gu * Gr ∈ YCond K (r := r) LL jj M) (cov : ℕ) (hcov : ∑ i, (if LL.vec i then 0 else dr i) ≤ cov) :
    Gu ∈ YCond K (r := r) LL jj (M + ((cov : ℤ) : WithTop ℤ)) := by
  classical
  cases M with
  | top => rw [WithTop.top_add, ycond_top]; exact Submodule.mem_top
  | coe Mz =>
    rw [← WithTop.coe_add, mem_ycond_iff D]
    rw [mem_ycond_iff D, (valuationsAdditive_D7 D K (Fin N) (⟨LL.vec⟩ : Letters (Fin N)) r {i : Fin N | (i : ℕ) < jj}).2.2.1] at h
    have hlow : ¬ lam1S (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < jj} Gr ≤ ((-(cov : ℤ) - 1 : ℤ) : WithBot ℤ) := by
      intro hle
      have h1 := ycond_le (K := K) (r := r) LL jj ((-(cov : ℤ) - 1 : ℤ) : WithTop ℤ) ((mem_ycond_iff D LL jj _ Gr).2 hle)
      rw [MvPolynomial.mem_restrictSupport_iff] at h1
      obtain ⟨m, hm⟩ : Gr.support.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; intro h0; exact hne (MvPolynomial.support_eq_empty.1 h0)
      have h2 : ((chWt LL jj 0 m : ℤ) : WithTop ℤ) ≤ ((-(cov : ℤ) - 1 : ℤ) : WithTop ℤ) := h1 (Finset.mem_coe.2 hm)
      have h3 : chWt LL jj 0 m ≤ -(cov : ℤ) - 1 := by exact_mod_cast h2
      have hdeg : ∀ i, multideg m i = dr i := by
        unfold Pol at hr
        rw [MvPolynomial.mem_restrictSupport_iff] at hr
        exact hr (Finset.mem_coe.2 hm)
      have h4 : -((∑ i, (if LL.vec i then 0 else dr i) : ℕ) : ℤ) ≤ chWt LL jj 0 m := by
        unfold chWt
        rw [Nat.cast_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_le_sum fun i _ => ?_
        have hm0 : m (i, 0) ≤ dr i := by
          rw [← hdeg i]
          exact Finset.single_le_sum (f := fun c => m (i, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
        have hm0' : (m (i, 0) : ℤ) ≤ (dr i : ℤ) := by exact_mod_cast hm0
        by_cases hv : LL.vec i = true
        · simp only [hv, if_true]
          split_ifs <;> simp
        · simp only [hv]
          split_ifs <;> simp <;> omega
      have h5 : ((∑ i, (if LL.vec i then 0 else dr i) : ℕ) : ℤ) ≤ (cov : ℤ) := by exact_mod_cast hcov
      omega
    induction hGr : lam1S (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < jj} Gr using WithBot.recBotCoe with
    | bot => rw [hGr] at hlow; exact absurd bot_le hlow
    | coe v =>
      rw [hGr] at hlow h
      have hv : -(cov : ℤ) - 1 < v := by
        by_contra hc
        exact hlow (by exact_mod_cast (not_lt.1 hc))
      induction hGu : lam1S (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < jj} Gu using WithBot.recBotCoe with
      | bot => exact bot_le
      | coe a =>
        rw [hGu] at h
        have h6 : a + v ≤ Mz := by exact_mod_cast h
        have : a ≤ Mz + (cov : ℤ) := by omega
        exact_mod_cast this

end Formalism.MainNotions.ColumnSystems.Pf
end
end

