module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0007
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0006
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0001

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.DivDerZero
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.CovariantDegrees

section Y

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero (KK O)] {N r : ℕ} [NeZero r]

theorem ycond_op (D : Formalism.BasicNotions.D7) (LL LL' : ChainLetters N) (hv : LL'.vec = LL.vec) (j : ℕ) {M M' : WithTop ℤ} (n : ℕ)
    (hM : M + ((n : ℤ) : WithTop ℤ) ≤ M') (al be : Fin N × Fin r →₀ ℕ)
    (hn : vecDeg (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} al +
      covDeg (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} be ≤ n)
    {y : MvPolynomial (Fin N × Fin r) (KK O)} (hy : y ∈ YCond (KK O) (r := r) LL j M) :
    monomial al 1 * divDer be y ∈ YCond (KK O) (r := r) LL' j M' := by
  cases M' with
  | top => rw [PolBridge.ycond_top]; exact Submodule.mem_top
  | coe M' =>
    cases M with
    | top => simp at hM
    | coe M =>
      rw [PolBridge.mem_ycond_iff D] at hy ⊢
      rw [hv]
      have h1 := flt_op_lam1S (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} y al be n hn
      refine h1.trans ?_
      have h2 : M + (n : ℤ) ≤ M' := by exact_mod_cast hM
      calc lam1S (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} y + ((n : ℤ) : WithBot ℤ)
          ≤ ((M : ℤ) : WithBot ℤ) + ((n : ℤ) : WithBot ℤ) := by gcongr
        _ = ((M + (n : ℤ) : ℤ) : WithBot ℤ) := by norm_cast
        _ ≤ _ := by exact_mod_cast h2

theorem divDer_zero {R : Type} [CommSemiring R] {σ : Type} (F : MvPolynomial σ R) : divDer 0 F = F := by
  unfold divDer
  conv_rhs => rw [F.as_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp

theorem intPol_cth {σ : Type} (v : σ) (n : ℕ) {y : MvPolynomial σ (KK O)} (hy : y ∈ IntPol O σ) :
    cth v n y ∈ IntPol O σ := by
  rw [mem_integral_poly_iff_coeff] at hy ⊢
  intro m
  obtain ⟨o, ho⟩ := hy m
  exact ⟨o * (((m v).choose n : ℕ) : O), by rw [coeff_cth, ho, map_mul, map_natCast]⟩

theorem intPol_mul {σ : Type} {x y : MvPolynomial σ (KK O)} (hx : x ∈ IntPol O σ) (hy : y ∈ IntPol O σ) :
    x * y ∈ IntPol O σ := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a * b, by simp⟩

theorem intPol_X {σ : Type} (v : σ) : (X v : MvPolynomial σ (KK O)) ∈ IntPol O σ := ⟨X v, by simp⟩

theorem yjtZ_cth (D : Formalism.BasicNotions.D7) (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ) {thr thr' : Fin q → WithTop ℤ} (n : ℕ)
    (hthr : ∀ k, thr k + ((n : ℤ) : WithTop ℤ) ≤ thr' k) (v : Fin N × Fin r)
    {y : MvPolynomial (Fin N × Fin r) (KK O)} (hy : y ∈ YjtZ O (r := r) LL J thr) :
    cth v n y ∈ YjtZ O (r := r) LL J thr' := by
  classical
  obtain ⟨⟨hy1, hy2⟩, hy3⟩ := hy
  refine ⟨⟨?_, ?_⟩, intPol_cth v n hy3⟩
  · unfold chPol Formalism.MainNotions.G.Pol at hy1 ⊢
    rw [SetLike.mem_coe, mem_restrictSupport_iff] at hy1 ⊢
    intro m hm
    apply hy1
    rw [Finset.mem_coe, mem_support_iff] at hm ⊢
    intro h0
    exact hm (by rw [coeff_cth, h0, zero_mul])
  · rw [SetLike.mem_coe, Submodule.mem_iInf] at hy2 ⊢
    intro k
    refine ycond_op D LL LL rfl (J k) n (hthr k) _ _ ?_ (hy2 k)
    by_cases hn : n = 0
    · subst hn; simp [vecDeg, covDeg]
    · simp only [vecDeg, covDeg, Finsupp.support_single_ne_zero _ hn, Finset.sum_singleton, Finsupp.single_eq_same]
      split_ifs with h1 h2 <;> first | omega | (exfalso; simp_all)

theorem yjtZ_X (D : Formalism.BasicNotions.D7) (LL LL' : ChainLetters N) (hv : LL'.vec = LL.vec) (a : Fin N) (c : Fin r)
    (hd : ∀ i, LL'.deg i = LL.deg i + if i = a then 1 else 0)
    {q : ℕ} (J : Fin q → ℕ) {thr thr' : Fin q → WithTop ℤ} (n : ℕ) (hn : LL.vec a = true → 1 ≤ n)
    (hthr : ∀ k, thr k + ((n : ℤ) : WithTop ℤ) ≤ thr' k)
    {y : MvPolynomial (Fin N × Fin r) (KK O)} (hy : y ∈ YjtZ O (r := r) LL J thr) :
    X (a, c) * y ∈ YjtZ O (r := r) LL' J thr' := by
  classical
  obtain ⟨⟨hy1, hy2⟩, hy3⟩ := hy
  refine ⟨⟨?_, ?_⟩, intPol_mul (intPol_X _) hy3⟩
  · unfold chPol Formalism.MainNotions.G.Pol at hy1 ⊢
    rw [SetLike.mem_coe, mem_restrictSupport_iff] at hy1 ⊢
    intro m hm
    rw [Finset.mem_coe, support_X_mul, Finset.mem_map] at hm
    obtain ⟨m0, hm0, rfl⟩ := hm
    have h0 := hy1 hm0
    intro i
    have h1 := h0 i
    simp only [multideg, addLeftEmbedding_apply, Finsupp.add_apply] at h1 ⊢
    rw [Finset.sum_add_distrib, h1, hd i, add_comm]
    congr 1
    by_cases hi : i = a
    · subst hi
      simp [Finsupp.single_apply]
    · have : ∀ x : Fin r, (Finsupp.single (a, c) 1 : Fin N × Fin r →₀ ℕ) (i, x) = 0 := by
        intro x
        rw [Finsupp.single_apply, if_neg]
        intro h
        exact hi (congrArg Prod.fst h).symm
      simp [this, hi]
  · rw [SetLike.mem_coe, Submodule.mem_iInf] at hy2 ⊢
    intro k
    have h := ycond_op D LL LL' hv (J k) n (hthr k) (Finsupp.single (a, c) 1) 0 ?_ (hy2 k)
    · rwa [divDer_zero] at h
    · simp only [vecDeg, covDeg, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
        Finsupp.single_eq_same, Finsupp.support_zero, Finset.sum_empty, add_zero]
      split_ifs with h1
      · exact hn h1.2
      · omega

end Y

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.ExpFactIoExp
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees MvPolynomial

theorem rat_int {O K : Type} [CommRing O] [IsLocalRing O] [Field K] [CharZero K] [Algebra O K] {p : ℕ} (hp : p.Prime)
    (hpO : ¬ IsUnit (p : O)) (x : ℚ) (c : ℕ) (hx : PadicGe p x c) :
    ∃ y : O, (x : K) = (p : K) ^ c * algebraMap O K y := by
  by_cases hx0 : x = 0
  · exact ⟨0, by simp [hx0]⟩
  rcases hx with hx | hv
  · exact absurd hx hx0
  haveI : Fact p.Prime := ⟨hp⟩
  have hv' : (c : ℤ) ≤ padicValRat p x := by exact_mod_cast hv
  simp only [padicValRat] at hv'
  have hden : ¬ p ∣ x.den := by
    intro hd
    have hnum : ¬ (p : ℤ) ∣ x.num := by
      intro hn
      have h1 : p ∣ x.num.natAbs := Int.ofNat_dvd_left.mp hn
      have h2 := Nat.dvd_gcd h1 hd
      rw [x.reduced.gcd_eq_one] at h2
      exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
    have h0 : padicValInt p x.num = 0 := padicValInt.eq_zero_of_not_dvd hnum
    have h1 : 1 ≤ multiplicity p x.den := one_le_padicValNat_of_dvd x.den_nz hd
    rw [h0] at hv'
    omega
  have hpv0 : multiplicity p x.den = 0 := padicValNat.eq_zero_of_not_dvd hden
  rw [hpv0] at hv'
  have hdvd : (p : ℤ) ^ c ∣ x.num := by
    have := (padicValInt_dvd_iff (p := p) c x.num).mpr (Or.inr (by omega))
    exact_mod_cast this
  obtain ⟨n, hn⟩ := hdvd
  have hcop : Nat.Coprime p x.den := (Nat.Prime.coprime_iff_not_dvd hp).mpr hden
  have hb := Nat.gcd_eq_gcd_ab p x.den
  rw [hcop.gcd_eq_one, Nat.cast_one] at hb
  have hb' : (p : O) * (Nat.gcdA p x.den : O) + (x.den : O) * (Nat.gcdB p x.den : O) = 1 := by
    have := congrArg (Int.cast : ℤ → O) hb
    push_cast at this
    exact this.symm
  have hdu : IsUnit (x.den : O) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hb' with h | h
    · exact absurd (isUnit_of_mul_isUnit_left h) hpO
    · exact isUnit_of_mul_isUnit_left h
  have hinv : algebraMap O K (↑hdu.unit⁻¹ : O) * (x.den : K) = 1 := by
    rw [← map_natCast (algebraMap O K), ← map_mul, IsUnit.val_inv_mul, map_one]
  have hainv : algebraMap O K (↑hdu.unit⁻¹ : O) = (x.den : K)⁻¹ := eq_inv_of_mul_eq_one_left hinv
  refine ⟨(n : O) * ↑hdu.unit⁻¹, ?_⟩
  rw [map_mul, map_intCast, hainv, Rat.cast_def, hn]
  push_cast
  ring

def Rblk (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m) : ℕ :=
  open Classical in
  ∏ x ∈ Finset.univ \ (Finset.univ.image (symVar C0 CE1 CE2 X j)), (baseExp C0 CE1 CE2 X j b x).factorial

theorem expFact_ioExp (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (μ : BV C0 CE1 CE2 X j →₀ ℕ) :
    expFact (ioExp C0 CE1 CE2 X j b μ) = Rblk C0 CE1 CE2 X j b *
      ∏ v : BV C0 CE1 CE2 X j, (baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v) +
        symLev X.p C0 CE1 CE2 X j v * μ v).factorial := by
  classical
  have hinj := symVar_inj C0 CE1 CE2 X j
  have hsumv : ∀ x, (μ.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * n)) x =
      ∑ v ∈ μ.support, if symVar C0 CE1 CE2 X j v = x then symLev X.p C0 CE1 CE2 X j v * μ v else 0 := by
    intro x
    rw [Finsupp.sum_apply]
    exact Finset.sum_congr rfl fun v _ => Finsupp.single_apply
  have hout : ∀ x ∉ Finset.univ.image (symVar C0 CE1 CE2 X j),
      ioExp C0 CE1 CE2 X j b μ x = baseExp C0 CE1 CE2 X j b x := by
    intro x hx
    rw [ioExp, Finsupp.add_apply, hsumv, Finset.sum_eq_zero, add_zero]
    intro v _
    rw [if_neg]
    intro h
    exact hx (Finset.mem_image.2 ⟨v, Finset.mem_univ _, h⟩)
  have hin : ∀ v, ioExp C0 CE1 CE2 X j b μ (symVar C0 CE1 CE2 X j v) =
      baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v) + symLev X.p C0 CE1 CE2 X j v * μ v := by
    intro v
    rw [ioExp, Finsupp.add_apply, hsumv]
    congr 1
    rw [Finset.sum_eq_single v]
    · rw [if_pos rfl]
    · intro v' _ hne
      rw [if_neg]
      exact fun h => hne (hinj h)
    · intro hv
      have h0 : μ v = 0 := by simpa using hv
      rw [if_pos rfl, h0, mul_zero]
  rw [expFact, Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero)]
  rw [← Finset.prod_sdiff (Finset.subset_univ (Finset.univ.image (symVar C0 CE1 CE2 X j)))]
  rw [Finset.prod_image (fun a _ c _ h => hinj h)]
  congr 1
  · unfold Rblk
    exact Finset.prod_congr rfl fun x hx => by rw [hout x (Finset.mem_sdiff.1 hx).2]
  · exact Finset.prod_congr rfl fun v _ => by rw [hin v]

theorem baseExp_odd (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (i0 : Fin (segS X.TT j)) (β0 : Bool) (c0 : Fin (X.m + 1)) :
    baseExp C0 CE1 CE2 X j b ((topOdd X j i0, β0), c0) = (if β0 then b.rz i0 c0 else b.ry i0 c0) +
      (if (i0 : ℕ) < (X.seg C0 CE1 CE2 j).sigma ∧ c0 = 0 then (X.seg C0 CE1 CE2 j).P X.p i0 *
        (if β0 then coarseA X.p (X.seg C0 CE1 CE2 j) b i0 - b.w i0 else b.sg i0) else 0) := by
  classical
  have hinj := topOdd_inj X j
  have hite : ∀ (Q : Prop) [Decidable Q] (f : ((X.TT × Bool) × Fin (X.m + 1)) →₀ ℕ) (y),
      (if Q then f else 0) y = if Q then f y else 0 := by
    intro Q _ f y
    split_ifs <;> rfl
  have hne : ∀ (i : Fin (segS X.TT j)) (β : Bool) (c : Fin (X.m + 1)), i ≠ i0 →
      ((topOdd X j i, β), c) ≠ ((topOdd X j i0, β0), c0) := by
    intro i β c hi h
    exact hi (hinj (congrArg (fun y => y.1.1) h))
  rw [baseExp, Finsupp.add_apply]
  congr 1
  · rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i0]
    · rw [Finsupp.finsetSum_apply, Finset.sum_eq_single c0]
      · rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
        cases β0 <;> simp
      · intro c _ hc
        rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply, if_neg, if_neg]
        · rfl
        · intro h
          exact hc (congrArg (fun y => y.2) h)
        · intro h
          exact hc (congrArg (fun y => y.2) h)
      · intro h
        exact absurd (Finset.mem_univ c0) h
    · intro i _ hi
      rw [Finsupp.finsetSum_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply, if_neg (hne i true c hi),
        if_neg (hne i false c hi)]
      rfl
    · intro h
      exact absurd (Finset.mem_univ i0) h
  · rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i0]
    · rw [hite]
      by_cases h1 : (i0 : ℕ) < (X.seg C0 CE1 CE2 j).sigma
      · by_cases hc : c0 = 0
        · subst hc
          rw [if_pos h1, if_pos ⟨h1, rfl⟩, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
          cases β0 <;> simp
        · rw [if_pos h1, if_neg (fun h => hc h.2), Finsupp.add_apply, Finsupp.single_apply,
            Finsupp.single_apply, if_neg, if_neg]
          · rfl
          · intro h
            exact hc (congrArg (fun y => y.2) h).symm
          · intro h
            exact hc (congrArg (fun y => y.2) h).symm
      · rw [if_neg h1, if_neg (fun h => h1 h.1)]
    · intro i _ hi
      rw [hite]
      split_ifs
      · rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply, if_neg (hne i true 0 hi),
          if_neg (hne i false 0 hi)]
        rfl
      · rfl
    · intro h
      exact absurd (Finset.mem_univ i0) h

theorem baseExp_end (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (β0 : Bool) (c0 : Fin (X.m + 1)) : baseExp C0 CE1 CE2 X j b ((topEnd X j, β0), c0) = 0 := by
  classical
  have hite : ∀ (Q : Prop) [Decidable Q] (f : ((X.TT × Bool) × Fin (X.m + 1)) →₀ ℕ) (y),
      (if Q then f else 0) y = if Q then f y else 0 := by
    intro Q _ f y
    split_ifs <;> rfl
  simp [baseExp, Finsupp.finsetSum_apply, Finsupp.single_apply, topOdd_ne_end, hite]

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.IoBlockWh
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

def TD (b : SegBlock (segS X.TT j) X.m) (ω : (X.TT × Bool) × Fin (X.m + 1) → ℕ) : ℕ :=
  (∑ i : Fin (segS X.TT j),
    ((∑ c : Fin (X.m + 1), (b.rz i c * ω ((topOdd X j i, true), c) + b.ry i c * ω ((topOdd X j i, false), c))) +
     (X.seg C0 CE1 CE2 j).P X.p i *
      (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i) * ω ((topOdd X j i, true), 0) +
          b.sg i * ω ((topOdd X j i, false), 0) + b.w i * ω ((topOdd X j i, true), Fin.succ 0) +
          (coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i - b.sg i) * ω ((topOdd X j i, false), Fin.succ 0)
       else
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i) * ω ((topOdd X j i, true), 0) +
          b.o i * ω ((topOdd X j i, true), Fin.succ 0) +
          coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i * ω ((topOdd X j i, false), Fin.succ 0)))) +
  (segAPlus X.TT X.aT j - b.oPlus) * ω ((topEnd X j, true), 0) + b.oPlus * ω ((topEnd X j, true), Fin.succ 0) +
    (X.seg C0 CE1 CE2 j).bPlus * ω ((topEnd X j, false), Fin.succ 0)

theorem ioBlock_wh (O : Type) [CommRing O] [IsDomain O] (mm : ℝ) (b : SegBlock (segS X.TT j) X.m)
    (ω : (X.TT × Bool) × Fin (X.m + 1) → ℕ) (hc : ∀ x (c c' : Fin X.m), ω (x, c.succ) = ω (x, c'.succ))
    (hU : ∀ l : Fin (X.seg C0 CE1 CE2 j).t,
      ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), true), 0) + ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), false), 0) =
      ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), true), Fin.succ 0) +
        ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), false), Fin.succ 0))
    (hP : ω ((topEnd X j, true), 0) + ω ((topEnd X j, false), 0) =
      ω ((topEnd X j, true), Fin.succ 0) + ω ((topEnd X j, false), Fin.succ 0))
    (s : MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O))
    (hs : s ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mm b).SSZ O (r := X.m)) :
    IsWeightedHomogeneous ω (ioBlock (KK O) X.p C0 CE1 CE2 X j b s) (TD C0 CE1 CE2 X j b ω) := by
  let ω' : BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t → ℕ := fun v => symLev X.p C0 CE1 CE2 X j v * ω (symVar C0 CE1 CE2 X j v)
  let ωL : Fin (2 * segS X.TT j + 1 + 1) → ℕ := fun a => ω' (Sum.inl (a, 0))
  have h1 : ∀ a c, ω' (Sum.inl (a, c)) = ωL a := by
    intro a c
    simp only [ω', ωL, symLev, symVar]
    split_ifs <;> rw [hc _ c 0]
  have e0 : ∀ i : Fin (segS X.TT j), finPos (2 * segS X.TT j + 1) (2 * (i : ℕ)) =
      Fin.castSucc (⟨2 * i.val, by omega⟩ : Fin (2 * segS X.TT j + 1)) := by
    intro i
    have := i.2
    apply Fin.ext
    show min (2 * i.val) (2 * segS X.TT j + 1) = 2 * i.val
    omega
  have e1 : ∀ i : Fin (segS X.TT j), finPos (2 * segS X.TT j + 1) (2 * (i : ℕ) + 1) =
      Fin.castSucc (⟨2 * i.val + 1, by omega⟩ : Fin (2 * segS X.TT j + 1)) := by
    intro i
    have := i.2
    apply Fin.ext
    show min (2 * i.val + 1) (2 * segS X.TT j + 1) = 2 * i.val + 1
    omega
  have hW : ∀ i : Fin (segS X.TT j), ωL (Fin.castSucc (⟨2 * i.val, by omega⟩ : Fin (2 * segS X.TT j + 1))) =
      (X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), Fin.succ 0) := by
    intro i
    simp only [ωL, ω']
    rw [symbol_variable_lower_letter, symbol_level_lower_letter]
  have hE : ∀ i : Fin (segS X.TT j), ωL (Fin.castSucc (⟨2 * i.val + 1, by omega⟩ : Fin (2 * segS X.TT j + 1))) =
      (X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, false), Fin.succ 0) := by
    intro i
    simp only [ωL, ω']
    rw [sv_E, sl_E]
  have hUU : ωL (Fin.castSucc (⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1))) =
      ω ((topEnd X j, true), Fin.succ 0) := by
    simp only [ωL, ω']
    rw [sv_U, sl_U, one_mul]
  have hXi : ωL (Fin.last _) = ω ((topEnd X j, false), Fin.succ 0) := by
    simp only [ωL, ω']
    rw [sv_xi, sl_xi, one_mul]
  have hZ : ∀ (l : Fin (X.seg C0 CE1 CE2 j).t) (β : Bool), ω' (Sum.inr (Fin.castSucc l, β)) =
      (X.seg C0 CE1 CE2 j).P X.p (uTop (X.seg C0 CE1 CE2 j) l) * ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), !β), 0) := by
    intro l β
    simp only [ω']
    rw [sv_Z, sl_Z]
  have hx : ∀ β : Bool, ω' (Sum.inr (Fin.last (X.seg C0 CE1 CE2 j).t, β)) = ω ((topEnd X j, !β), 0) := by
    intro β
    simp only [ω']
    rw [symbol_variable_last, symbol_level_last, one_mul]
  have h2 : ∀ l : Fin (X.seg C0 CE1 CE2 j).t, ω' (Sum.inr (Fin.castSucc l, false)) + ω' (Sum.inr (Fin.castSucc l, true)) =
      ωL (finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ))) + ωL (finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1)) := by
    intro l
    rw [hZ, hZ, e0, e1, hW, hE, ← mul_add, ← mul_add]
    congr 1
    exact hU l
  have h3 : ω' (Sum.inr (Fin.last (X.seg C0 CE1 CE2 j).t, false)) + ω' (Sum.inr (Fin.last (X.seg C0 CE1 CE2 j).t, true)) =
      ωL (Fin.castSucc ⟨2 * segS X.TT j, by omega⟩) + ωL (Fin.last _) := by
    rw [hx, hx, hUU, hXi]
    exact hP
  have hS := ssz_wh O X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mm b ω' ωL h1 h2 h3 s hs
  have hA := wh_aeval ω (symVar C0 CE1 CE2 X j) (symLev X.p C0 CE1 CE2 X j) s _ hS
  have hDg : IsWeightedHomogeneous ω (digitMon (KK O) C0 CE1 CE2 X j b)
      (∑ i : Fin (segS X.TT j), ∑ c : Fin (X.m + 1),
        (b.rz i c • ω ((topOdd X j i, true), c) + b.ry i c • ω ((topOdd X j i, false), c))) :=
    IsWeightedHomogeneous.prod _ _ _ (fun i _ => IsWeightedHomogeneous.prod _ _ _ (fun c _ =>
      ((isWeightedHomogeneous_X _ ω _).pow _).mul ((isWeightedHomogeneous_X _ ω _).pow _)))
  have hSt : IsWeightedHomogeneous ω (sTopMon (KK O) X.p C0 CE1 CE2 X j b)
      (∑ i : Fin (segS X.TT j), if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i)) • ω ((topOdd X j i, true), 0) +
          ((X.seg C0 CE1 CE2 j).P X.p i * b.sg i) • ω ((topOdd X j i, false), 0) else 0) := by
    refine IsWeightedHomogeneous.prod _ _ _ (fun i _ => ?_)
    split_ifs
    · exact ((isWeightedHomogeneous_X _ ω _).pow _).mul ((isWeightedHomogeneous_X _ ω _).pow _)
    · exact isWeightedHomogeneous_one _ _
  have hall := (hDg.mul hSt).mul hA
  refine wh_congr hall ?_
  have E1 : ∑ l : Fin (X.seg C0 CE1 CE2 j).t, (coarseA X.p (X.seg C0 CE1 CE2 j) b (uTop (X.seg C0 CE1 CE2 j) l) - b.o (uTop (X.seg C0 CE1 CE2 j) l)) * ω' (Sum.inr (Fin.castSucc l, false)) =
      ∑ i : Fin (segS X.TT j), if (X.seg C0 CE1 CE2 j).sigma ≤ i.val then
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), 0)) else 0 := by
    rw [← sum_uTop (X.seg C0 CE1 CE2 j) (fun i => (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), 0)))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hZ]
    rfl
  have E3 : ∑ a : Fin (2 * segS X.TT j + 1), (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a * ωL (Fin.castSucc a) =
      ∑ i : Fin (segS X.TT j), ((if i.val < (X.seg C0 CE1 CE2 j).sigma then b.w i else b.o i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), Fin.succ 0)) +
        (if i.val < (X.seg C0 CE1 CE2 j).sigma then coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i - b.sg i
          else coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, false), Fin.succ 0))) +
      b.oPlus * ω ((topEnd X j, true), Fin.succ 0) := by
    rw [sum_chain, hUU, chain_deg_U X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b _ rfl]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hW, hE, segment_chain_degree_even X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b _ i rfl, chain_deg_E X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b _ i rfl]
  unfold OmB TD
  rw [E1, E3, hx, hXi]
  simp only [smul_eq_mul, Bool.not_false]
  have key : ∀ i : Fin (segS X.TT j),
      ((∑ c : Fin (X.m + 1), (b.rz i c * ω ((topOdd X j i, true), c) + b.ry i c * ω ((topOdd X j i, false), c))) +
     (X.seg C0 CE1 CE2 j).P X.p i *
      (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i) * ω ((topOdd X j i, true), 0) +
          b.sg i * ω ((topOdd X j i, false), 0) + b.w i * ω ((topOdd X j i, true), Fin.succ 0) +
          (coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i - b.sg i) * ω ((topOdd X j i, false), Fin.succ 0)
       else
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i) * ω ((topOdd X j i, true), 0) +
          b.o i * ω ((topOdd X j i, true), Fin.succ 0) +
          coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i * ω ((topOdd X j i, false), Fin.succ 0))) =
      (∑ c : Fin (X.m + 1), (b.rz i c * ω ((topOdd X j i, true), c) + b.ry i c * ω ((topOdd X j i, false), c))) +
      (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        (X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i) * ω ((topOdd X j i, true), 0) +
          (X.seg C0 CE1 CE2 j).P X.p i * b.sg i * ω ((topOdd X j i, false), 0) else 0) +
      (if (X.seg C0 CE1 CE2 j).sigma ≤ i.val then
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), 0)) else 0) +
      ((if i.val < (X.seg C0 CE1 CE2 j).sigma then b.w i else b.o i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), Fin.succ 0)) +
        (if i.val < (X.seg C0 CE1 CE2 j).sigma then coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i - b.sg i
          else coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, false), Fin.succ 0))) := by
    intro i
    by_cases h : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma
    · rw [if_pos h, if_pos h, if_neg (not_le.2 h), if_pos h, if_pos h]
      ring
    · rw [if_neg h, if_neg h, if_pos (not_lt.1 h), if_neg h, if_neg h]
      ring
  rw [Finset.sum_congr rfl fun i _ => key i]
  simp only [Finset.sum_add_distrib]
  ring

end Formalism.MainNotions.ColumnSystems.Pf
end
end

