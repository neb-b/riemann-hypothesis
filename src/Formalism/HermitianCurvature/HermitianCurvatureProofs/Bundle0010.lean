module

public import Formalism.RealPlaceAnalysis.Bundle0003
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.GroupTheory.Perm.Support
public import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRTopActAlg
section
open Polynomial Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

open Formalism.REAL

def QTopAlg : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) (h : ℂ),
    ∃ d : ℕ → A, (∀ Y : ℂ, qminor E id id (Y + h) = ∑ j ∈ Finset.range (n + 1), Y ^ j • d j) ∧
      (1 ≤ n → d (n - 1) = ∑ a, E a a + algebraMap ℂ A ((n : ℂ) * h - (n : ℂ) * ((n : ℂ) - 1) / 2))

namespace TopAlg

variable {A : Type*} [Ring A] [Algebra ℂ A]

def fac (lin : Prop) [Decidable lin] (B : A) : A[X] := (if lin then X else 0) + C B

theorem natDegree_fac (lin : Prop) [Decidable lin] (B : A) :
    (fac lin B).natDegree ≤ if lin then 1 else 0 := by
  unfold fac
  split_ifs
  · exact (natDegree_add_le _ _).trans (by simp [natDegree_X_le])
  · simp

def prodP {m : ℕ} (lin : Fin m → Prop) [DecidablePred lin] (B : Fin m → A) : A[X] :=
  (List.ofFn fun l => fac (lin l) (B l)).prod

theorem natDegree_prodP : ∀ {m : ℕ} (lin : Fin m → Prop) [DecidablePred lin] (B : Fin m → A),
    (prodP lin B).natDegree ≤ ∑ l, (if lin l then 1 else 0)
  | 0, lin, _, B => by simp [prodP]
  | m + 1, lin, _, B => by
    unfold prodP
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    refine (natDegree_mul_le).trans (add_le_add (natDegree_fac _ _) ?_)
    exact natDegree_prodP (fun l => lin l.succ) (fun l => B l.succ)

theorem eval_prodP {m : ℕ} (lin : Fin m → Prop) [DecidablePred lin] (B : Fin m → A) (Y : ℂ) :
    eval₂ (RingHom.id A) (algebraMap ℂ A Y) (prodP lin B) =
      (List.ofFn fun l => (if lin l then algebraMap ℂ A Y else 0) + B l).prod := by
  unfold prodP
  rw [eval₂_list_prod_noncomm]
  · rw [List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun l => ?_))
    simp only [Function.comp, fac, eval₂_add, eval₂_C, RingHom.id_apply]
    split_ifs <;> simp
  · intro p _ k
    exact (Algebra.commutes Y _).symm

theorem coeff_all : ∀ {m : ℕ} (B : Fin m → A),
    (List.ofFn fun l => (X + C (B l) : A[X])).prod.coeff m = 1 ∧
      (1 ≤ m → (List.ofFn fun l => (X + C (B l) : A[X])).prod.coeff (m - 1) = ∑ l, B l) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    intro B
    specialize ih (fun l => B l.succ)
    have hdeg : (List.ofFn fun l : Fin m => (X + C (B l.succ) : A[X])).prod.natDegree ≤ m := by
      have := natDegree_prodP (fun _ : Fin m => True) (fun l => B l.succ)
      simp only [if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this
      simpa [prodP, fac] using this
    rw [List.ofFn_succ, List.prod_cons]
    set Q := (List.ofFn fun l : Fin m => (X + C (B l.succ) : A[X])).prod with hQ
    refine ⟨?_, fun _ => ?_⟩
    · rw [add_mul, coeff_add, coeff_X_mul, ih.1, coeff_C_mul,
        coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < m + 1), mul_zero, add_zero]
    · rw [Fin.sum_univ_succ, add_mul, coeff_add, coeff_C_mul, Nat.add_sub_cancel, ih.1, mul_one]
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        simp
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        rw [coeff_X_mul, add_comm]
        congr 1
        have := ih.2 (by omega)
        simpa using this

end TopAlg

open TopAlg in
theorem quadratic_top_algebra_holds : QTopAlg := by
  intro A _ _ n E h
  classical

  let lin : Equiv.Perm (Fin n) → Fin n → Prop := fun σ l => σ l = l
  let B : Equiv.Perm (Fin n) → Fin n → A := fun σ l =>
    (if σ l = l then algebraMap ℂ A (h - ((l : ℕ) : ℂ)) else 0) + E (σ l) l
  let Pσ : Equiv.Perm (Fin n) → A[X] := fun σ => prodP (lin σ) (B σ)
  refine ⟨fun j => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : A) * (Pσ σ).coeff j, fun Y => ?_, fun hn => ?_⟩
  ·
    have hfac : ∀ σ : Equiv.Perm (Fin n),
        (List.ofFn fun k : Fin n => Tm E (Y + h - (k : ℂ)) (id (σ k)) (id k)).prod =
          ∑ j ∈ Finset.range (n + 1), Y ^ j • (Pσ σ).coeff j := by
      intro σ
      have e1 : (List.ofFn fun k : Fin n => Tm E (Y + h - (k : ℂ)) (id (σ k)) (id k)) =
          List.ofFn fun l => (if lin σ l then algebraMap ℂ A Y else 0) + B σ l := by
        refine congrArg List.ofFn (funext fun l => ?_)
        simp only [Tm, id_eq, lin, B]
        split_ifs
        · rw [add_sub_assoc, map_add, add_assoc]
        · simp only [zero_add]
      rw [e1, ← eval_prodP]
      have hdeg : (Pσ σ).natDegree < n + 1 := by
        have := natDegree_prodP (lin σ) (B σ)
        have h2 : ∑ l : Fin n, (if lin σ l then 1 else 0) ≤ n := by
          calc ∑ l : Fin n, (if lin σ l then 1 else 0) ≤ ∑ _l : Fin n, 1 :=
                Finset.sum_le_sum fun l _ => by split_ifs <;> simp
            _ = n := by simp
        show (prodP (lin σ) (B σ)).natDegree < n + 1
        omega
      rw [eval₂_eq_sum_range' (RingHom.id A) hdeg]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [RingHom.id_apply, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def]
    unfold qminor
    simp_rw [hfac, Finset.mul_sum, mul_smul_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.smul_sum]
  ·
    dsimp only
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul]
      have e1 : Pσ 1 = (List.ofFn fun l => (X + C (B 1 l) : A[X])).prod := by
        show prodP (lin 1) (B 1) = _
        unfold prodP fac
        congr 1
        congr 1
        funext l
        rw [if_pos (show lin 1 l from rfl)]
      rw [e1, (coeff_all (B 1)).2 hn]
      simp only [B, Equiv.Perm.one_apply, if_true]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_add_distrib, add_comm, ← map_sum]
      congr 1
      congr 1
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hs : ∑ l : Fin n, ((l : ℕ) : ℂ) = (n : ℂ) * ((n : ℂ) - 1) / 2 := by
        rw [Fin.sum_univ_eq_sum_range (fun l => ((l : ℕ) : ℂ)) n]
        have := Finset.sum_range_id_mul_two n
        have hc : ((∑ i ∈ Finset.range n, i : ℕ) : ℂ) * 2 = (n : ℂ) * ((n : ℂ) - 1) := by
          rw [← Nat.cast_ofNat, ← Nat.cast_mul, this]
          rcases Nat.eq_zero_or_pos n with h0 | h0
          · subst h0; simp
          · rw [Nat.cast_mul, Nat.cast_sub (by omega)]
            simp
        push_cast at hc
        linear_combination hc / 2
      rw [hs]
    · intro σ _ hσ
      have h2 : 2 ≤ σ.support.card := Equiv.Perm.two_le_card_support_of_ne_one hσ
      have hdeg := natDegree_prodP (lin σ) (B σ)
      have hcount : ∑ l : Fin n, (if lin σ l then 1 else 0) + σ.support.card = n := by
        have hsupp : σ.support.card = ∑ l : Fin n, (if ¬ lin σ l then 1 else 0) := by
          rw [Finset.sum_boole, Nat.cast_id]
          rfl
        rw [hsupp, ← Finset.sum_add_distrib]
        calc ∑ l : Fin n, ((if lin σ l then 1 else 0) + (if ¬lin σ l then 1 else 0)) = ∑ _l : Fin n, 1 :=
              Finset.sum_congr rfl fun l _ => by split_ifs <;> simp_all
          _ = n := by simp
      have : (Pσ σ).coeff (n - 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by show (prodP (lin σ) (B σ)).natDegree < n - 1; omega)
      rw [this, mul_zero]
    · intro h1
      exact absurd (Finset.mem_univ _) h1

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FiniteClassesPositiveSums
section
noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology Finset
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums

section gen

variable {α : Type}

theorem psd_congr {F : Finset α} {k k' : α → α → ℂ} (h : IsPSD F k)
    (e : ∀ x ∈ F, ∀ y ∈ F, k x y = k' x y) : IsPSD F k' := by
  intro a
  have : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k' x y = ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y :=
    sum_congr rfl fun x hx => sum_congr rfl fun y hy => by rw [e x hx y hy]
  rw [this]; exact h a

theorem psd_zero (F : Finset α) : IsPSD F (fun _ _ => (0 : ℂ)) := by
  intro a; simp

theorem psd_add {F : Finset α} {k k' : α → α → ℂ} (h : IsPSD F k) (h' : IsPSD F k') :
    IsPSD F (fun x y => k x y + k' x y) := by
  intro a
  have : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * (k x y + k' x y) =
      ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y + ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k' x y := by
    simp only [mul_add, sum_add_distrib]
  rw [this, Complex.add_im, Complex.add_re, (h a).1, (h' a).1]
  exact ⟨by simp, add_nonneg (h a).2 (h' a).2⟩

theorem psd_sum {ι : Type} {F : Finset α} (s : Finset ι) (k : ι → α → α → ℂ)
    (h : ∀ i ∈ s, IsPSD F (k i)) : IsPSD F (fun x y => ∑ i ∈ s, k i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using psd_zero F
  | insert i s hi ih =>
    have := psd_add (h i (mem_insert_self i s)) (ih fun j hj => h j (mem_insert_of_mem hj))
    exact psd_congr this fun x _ y _ => by rw [sum_insert hi]

end gen

section classes

variable {K : Type} [CommRing K] (R : Subring K)

theorem out_mk (x : K) :
    ∃ r ∈ R, (Quotient.out ((x : K) : K ⧸ R.toAddSubgroup) : K) = x + r := by
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_out_eq_add R.toAddSubgroup x
  exact ⟨r.1, r.2, hr⟩

theorem periodic_out {β : Type} (f : K → β) (h1 : ∀ x, ∀ r ∈ R, f (x + r) = f x) (x : K) :
    f (Quotient.out ((x : K) : K ⧸ R.toAddSubgroup)) = f x := by
  obtain ⟨r, hr, e⟩ := out_mk R x
  rw [e, h1 x r hr]

theorem finite_classes [TopologicalSpace K] [IsTopologicalRing K] (hR : IsOpen (R : Set K))
    (Lc : Set K) (hLc : IsCompact Lc) :
    {y : K ⧸ R.toAddSubgroup | (Quotient.out y : K) ∈ Lc}.Finite := by
  have : DiscreteTopology (K ⧸ R.toAddSubgroup) := QuotientAddGroup.discreteTopology hR
  have h := (hLc.image (QuotientAddGroup.continuous_mk (N := R.toAddSubgroup))).finite_of_discrete
  refine h.subset ?_
  intro y hy
  exact ⟨Quotient.out y, hy, Quotient.out_eq' y⟩

variable {R} {F : Finset (Point K)} {Lc : Set K} {S : Finset (K ⧸ R.toAddSubgroup)}

theorem finsum_classes (hS : ∀ y : K ⧸ R.toAddSubgroup, (Quotient.out y : K) ∈ Lc → y ∈ S)
    {Θ : K → Point K → Point K → ℂ}
    (h3 : ∀ x, x ∉ Lc → ∀ h ∈ F, ∀ h' ∈ F, Θ x h h' = 0) {h h' : Point K} (hh : h ∈ F)
    (hh' : h' ∈ F) :
    ∑ᶠ y : K ⧸ R.toAddSubgroup, Θ (Quotient.out y) h h' = ∑ y ∈ S, Θ (Quotient.out y) h h' := by
  apply finsum_eq_sum_of_support_subset
  intro y hy
  by_contra hyS
  exact hy (h3 _ (fun hc => hyS (hS y hc)) h hh h' hh')

theorem psd_single (hS : ∀ y : K ⧸ R.toAddSubgroup, (Quotient.out y : K) ∈ Lc → y ∈ S)
    {M : Point K → Point K → ℂ} {Θ : K → Point K → Point K → ℂ}
    (h1 : ∀ x, ∀ r ∈ R, Θ (x + r) = Θ x) (h2 : ∀ x, IsPSD F (Θ x))
    (h3 : ∀ x, x ∉ Lc → ∀ h ∈ F, ∀ h' ∈ F, Θ x h h' = 0)
    (h5 : IsPSD F (fun h h' => M h h' - ∑ᶠ y : K ⧸ R.toAddSubgroup, Θ (Quotient.out y) h h'))
    (x : K) : IsPSD F (fun h h' => M h h' - Θ x h h') := by
  classical
  have key := psd_add h5 (psd_sum (S.erase ((x : K) : K ⧸ R.toAddSubgroup))
    (fun y => Θ (Quotient.out y)) (fun y _ => h2 _))
  refine psd_congr key ?_
  intro h hh h' hh'
  have e1 := finsum_classes hS h3 hh hh'
  have e2 : Θ (Quotient.out ((x : K) : K ⧸ R.toAddSubgroup)) = Θ x := periodic_out R Θ h1 x
  simp only [e1]
  by_cases hx : ((x : K) : K ⧸ R.toAddSubgroup) ∈ S
  · rw [← add_sum_erase S (fun y => Θ (Quotient.out y) h h') hx, e2]
    ring
  · rw [erase_eq_of_notMem hx]
    have : Θ x h h' = 0 := by
      rw [← e2]
      exact h3 _ (fun hc => hx (hS _ hc)) h hh h' hh'
    rw [this]; ring

theorem limit_core (hEntry : PSDEntryBound) (hSubseq : BoundedSubseq)
    (hS : ∀ y : K ⧸ R.toAddSubgroup, (Quotient.out y : K) ∈ Lc → y ∈ S)
    (M : Point K → Point K → ℂ) (Th : ℕ → K → Point K → Point K → ℂ)
    (h1 : ∀ j x, ∀ r ∈ R, Th j (x + r) = Th j x) (h2 : ∀ j x, IsPSD F (Th j x))
    (h3 : ∀ j x, x ∉ Lc → ∀ h ∈ F, ∀ h' ∈ F, Th j x h h' = 0)
    (h5 : ∀ j, IsPSD F (fun h h' => M h h' -
      ∑ᶠ y : K ⧸ R.toAddSubgroup, Th j (Quotient.out y) h h')) :
    ∃ (φ : ℕ → ℕ) (Θ : K → Point K → Point K → ℂ), StrictMono φ ∧
      (∀ x, ∀ r ∈ R, Θ (x + r) = Θ x) ∧
      ∀ x, ∀ h ∈ F, ∀ h' ∈ F, Tendsto (fun j => Th (φ j) x h h') atTop (𝓝 (Θ x h h')) := by
  classical
  let T : Finset ((K ⧸ R.toAddSubgroup) × Point K × Point K) := S ×ˢ F ×ˢ F
  let θ : ℕ → T → ℂ := fun j i => Th j (Quotient.out i.1.1) i.1.2.1 i.1.2.2
  let B : ℝ := ∑ h ∈ F, |(M h h).re|
  have hB0 : 0 ≤ B := sum_nonneg fun _ _ => abs_nonneg _
  have hBh : ∀ h ∈ F, |(M h h).re| ≤ B := fun h hh =>
    single_le_sum (f := fun h => |(M h h).re|) (fun _ _ => abs_nonneg _) hh
  have hb : ∀ j i, ‖θ j i‖ ≤ B := by
    rintro j ⟨⟨y, h, h'⟩, hi⟩
    simp only [T, mem_product] at hi
    have hE := hEntry _ F (Th j (Quotient.out y)) M (h2 j _)
      (psd_single hS (h1 j) (h2 j) (h3 j) (h5 j) _) h hi.2.1 h' hi.2.2
    have hle : (M h h).re * (M h' h').re ≤ B ^ 2 := by
      calc (M h h).re * (M h' h').re ≤ |(M h h).re * (M h' h').re| := le_abs_self _
        _ = |(M h h).re| * |(M h' h').re| := abs_mul _ _
        _ ≤ B * B := mul_le_mul (hBh h hi.2.1) (hBh h' hi.2.2) (abs_nonneg _) hB0
        _ = B ^ 2 := (sq B).symm
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hB0 two_ne_zero).1 (hE.trans hle)
  obtain ⟨φ, l, hφ, hl⟩ := hSubseq T θ B hb
  refine ⟨φ, fun x h h' => if hx : (((x : K) : K ⧸ R.toAddSubgroup), h, h') ∈ T then l ⟨_, hx⟩
    else 0, hφ, ?_, ?_⟩
  · intro x r hr
    have e : (((x + r : K)) : K ⧸ R.toAddSubgroup) = ((x : K) : K ⧸ R.toAddSubgroup) := by
      rw [QuotientAddGroup.eq]
      have : -(x + r) + x = -r := by ring
      rw [this]
      exact neg_mem hr
    funext h h'
    simp only [e]
  · intro x h hh h' hh'
    have e2 : ∀ j, Th j (Quotient.out ((x : K) : K ⧸ R.toAddSubgroup)) = Th j x :=
      fun j => periodic_out R (Th j) (h1 j) x
    by_cases hx : (((x : K) : K ⧸ R.toAddSubgroup), h, h') ∈ T
    · simp only [dif_pos hx]
      have := hl ⟨_, hx⟩
      simp only [θ, e2] at this
      exact this
    · simp only [dif_neg hx]
      have hxS : ((x : K) : K ⧸ R.toAddSubgroup) ∉ S := by
        intro hc
        exact hx (by simp only [T, mem_product]; exact ⟨hc, hh, hh'⟩)
      have : ∀ j, Th (φ j) x h h' = 0 := by
        intro j
        rw [← e2]
        exact h3 _ _ (fun hc => hxS (hS _ hc)) h hh h' hh'
      simp only [this]
      exact tendsto_const_nhds

end classes

end Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums

theorem thetaExistsStepOfSteps : Formalism.FourierDecayAlt.A6.ThetaExistenceInductive := by
  intro hThOm hSupp hNsS hCOne hExh _hLF hEntry hClosed hSubseq hA2 hN1 K _ _ _ R ψ hD hch s hs hAt
    n₀ F hF
  classical
  obtain ⟨Lc, hcut, hGL⟩ := hSupp hNsS K R ψ hD (s + 1) F (by omega)
  obtain ⟨Om, hOm, hmono, hex⟩ := hExh K R ψ hD hch (s + 1) (by omega)
  choose Th hTh using fun j => hThOm hA2 hN1 K R ψ hD hch s hs hAt n₀ F Lc (Om j) hF hcut (hOm j)
  obtain ⟨hLo, hLk, -, -⟩ := hcut
  have hfin := finite_classes R hD.isOpen (Lc : Set K) hLk
  have hS : ∀ y : K ⧸ R.toAddSubgroup, (Quotient.out y : K) ∈ (Lc : Set K) → y ∈ hfin.toFinset :=
    fun y hy => hfin.mem_toFinset.2 hy
  let M : Point K → Point K → ℂ := fun h h' =>
    ((cSize R h ^ (s + 1) * cSize R h' ^ (s + 1) : ℝ) : ℂ) * N0 R ψ h h'
  obtain ⟨φ, Θ, hφ, h1, hlim⟩ := limit_core hEntry hSubseq hS M Th (fun j => (hTh j).1)
    (fun j => (hTh j).2.1) (fun j => (hTh j).2.2.1) (fun j => (hTh j).2.2.2.2.1)
  have h2 : ∀ x, IsPSD F (Θ x) := fun x =>
    hClosed _ F (fun j => Th (φ j) x) (Θ x) (fun j => (hTh _).2.1 x) (hlim x)
  have h3 : ∀ x, x ∉ (Lc : Set K) → ∀ h ∈ F, ∀ h' ∈ F, Θ x h h' = 0 := by
    intro x hx h hh h' hh'
    have := hlim x h hh h' hh'
    simp only [(hTh _).2.2.1 x hx h hh h' hh'] at this
    exact tendsto_nhds_unique tendsto_const_nhds this |>.symm
  have h4 : ∀ t : Kˣ, IsPSD F (fun h h' => Θ (t : K) h h' - Ns R ψ (s + 1) h h' t t) := by
    intro t
    obtain ⟨j0, hj0⟩ := hex t
    have hmono' : ∀ j, j0 ≤ j → (t : K) ∈ Om j := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => exact hj0
      | succ j _ ih => exact hmono j ih
    refine hClosed _ F (fun j h h' => Th (φ (j + j0)) (t : K) h h' - Ns R ψ (s + 1) h h' t t) _
      (fun j => (hTh _).2.2.2.1 t (hmono' _ ((Nat.le_add_left _ _).trans hφ.le_apply))) ?_
    intro h hh h' hh'
    exact ((hlim (t : K) h hh h' hh').comp (tendsto_add_atTop_nat j0)).sub tendsto_const_nhds
  have h5 : IsPSD F (fun h h' => M h h' -
      ∑ᶠ y : K ⧸ R.toAddSubgroup, Θ (Quotient.out y) h h') := by
    refine hClosed _ F (fun j h h' => M h h' -
      ∑ᶠ y : K ⧸ R.toAddSubgroup, Th (φ j) (Quotient.out y) h h') _
      (fun j => (hTh _).2.2.2.2.1) ?_
    intro h hh h' hh'
    simp only [finsum_classes hS h3 hh hh', finsum_classes hS ((hTh _).2.2.1) hh hh']
    exact tendsto_const_nhds.sub (tendsto_finsetSum _ fun y _ => hlim _ h hh h' hh')
  have h6 : ∀ x, ∀ h ∈ F, ∀ h' ∈ F, modK R (pt h.1 h.2).det ≠ modK R (pt h'.1 h'.2).det →
      Θ x h h' = 0 := by
    intro x h hh h' hh' hne
    have := hlim x h hh h' hh'
    simp only [(hTh _).2.2.2.2.2 x h hh h' hh' hne] at this
    exact tendsto_nhds_unique tendsto_const_nhds this |>.symm
  refine ⟨Θ, h1, h2, ⟨Lc, hLo, hLk, h3⟩, h4, h5, h6, ?_⟩
  intro hG x
  by_cases hx : x ∈ R
  · simp only [if_pos hx]
    refine psd_congr (psd_single hS h1 h2 h3 h5 x) ?_
    intro h hh h' hh'
    simp only [M, hCOne K R ψ hD h (hG h hh), hCOne K R ψ hD h' (hG h' hh')]
    simp
  · simp only [if_neg hx]
    refine psd_congr (psd_zero F) ?_
    intro h hh h' hh'
    rw [h3 x (fun hc => hx ((hGL hG x).1 hc)) h hh h' hh']
    simp

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FiniteSumSwap
section
noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.FiniteSumSwap

theorem finsum_swap {I J : Type} (P : I → Prop) [DecidablePred P] (T : J → Prop) [DecidablePred T]
    (hP : {q | P q}.Finite) (hT : {z | T z}.Finite) (a : ℂ) (g : J → ℂ) (F : J → I → ℂ)
    (e : I → ℂ) :
    ∑ᶠ q : I, (if P q then a * ∑ᶠ z : J, (if T z then g z * F z q else 0) else 0) * e q =
      a * ∑ᶠ z : J, (if T z then g z * ∑ᶠ q : I, (if P q then F z q else 0) * e q else 0) := by
  have h1 : ∀ f : I → ℂ, ∑ᶠ q : I, (if P q then f q else 0) * e q =
      ∑ q ∈ hP.toFinset, f q * e q := by
    intro f
    rw [finsum_eq_sum_of_support_subset (s := hP.toFinset)]
    · refine Finset.sum_congr rfl fun q hq => ?_
      rw [if_pos (by simpa using hq)]
    · intro q hq
      by_contra hq'
      have : ¬ P q := by simpa using hq'
      simp [this] at hq
  have h2 : ∀ f : J → ℂ, ∑ᶠ z : J, (if T z then f z else 0) = ∑ z ∈ hT.toFinset, f z := by
    intro f
    rw [finsum_eq_sum_of_support_subset (s := hT.toFinset)]
    · refine Finset.sum_congr rfl fun z hz => ?_
      rw [if_pos (by simpa using hz)]
    · intro z hz
      by_contra hz'
      have : ¬ T z := by simpa using hz'
      simp [this] at hz
  rw [h1, h2]
  simp_rw [h1, h2]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun q _ => ?_
  ring

end Formalism.FourierDecayAlt.P.FiniteSumSwap

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.FiniteSumSwap

theorem germExpansionKernelOfSteps : Formalism.FourierDecayAlt.A6.GermKernelAssemble := by
  intro hGerm hKp hInt hRoots K _ _ _ R ψ hD hn m hm γ hγ h Q hQ hQu
  obtain ⟨V, hV, H⟩ := hGerm K R ψ hD hn m hm γ hγ h Q hQ hQu
  refine ⟨V, hV, fun t c ht hc w' => ?_⟩
  have := hD.artin
  have := hD.red
  have hT : {z : Kˣ | z ^ (m + 1) = (-t) ^ m * c}.Finite :=
    hRoots K (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) ((-t) ^ m * c)
  have hP : {q : Cos R w' | IsInt R (orbZ w' (rep R q))}.Finite := hInt K R ψ hD w'
  rw [hKp K R ψ hD (pt2 h m t c) w']
  simp_rw [H t c ht hc]
  unfold germSum
  simp_rw [hKp K R ψ hD (addBlock h (m + 1) _) w']
  classical
  convert finsum_swap (fun q : Cos R w' => IsInt R (orbZ w' (rep R q)))
    (fun z : Kˣ => z ^ (m + 1) = (-t) ^ m * c) hP hT _ (germCoef R ψ m γ t)
    (fun z q => bbZ R ψ (addBlock h (m + 1) z) (orbZ w' (rep R q)))
    (fun q => conj (phase ψ (rep R q)))

end Formalism.FourierDecayAlt.P
end
end

