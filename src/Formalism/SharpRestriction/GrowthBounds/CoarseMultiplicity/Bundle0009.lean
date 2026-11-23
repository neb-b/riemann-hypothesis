module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0008
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.RestRawTail1Of

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BlockWithThresholds
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.CovariantDegrees

section GlobalTheory

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero (KK O)] {N r : ℕ} [NeZero r]

abbrev blockWithThresholds (D : BlockData N) (thr : Fin D.T.q → WithTop ℤ) : BlockData N :=
  { D with T := { D.T with thr := thr } }

abbrev SSt (O : Type) [CommRing O] [IsDomain O] (r : ℕ) [NeZero r] (D : BlockData N) (thr : Fin D.T.q → WithTop ℤ) :
    Submodule O (MvPolynomial (BVar N r D.T.t) (KK O)) :=
  (blockWithThresholds D thr).SSZ O (r := r)

structure TieOK (D : BlockData N) : Prop where
  lt : ∀ i, D.T.pos i + 1 < N
  inj : ∀ i i', D.T.pos i = D.T.pos i' → i = i'
  sep : ∀ i i', D.T.pos i + 1 ≠ D.T.pos i'
  uW : ∀ i, D.T.pos i ≠ (D.uPos : ℕ) ∧ D.T.pos i + 1 ≠ (D.uPos : ℕ)
  vecE : ∀ i (h : D.T.pos i + 1 < N), D.LL.vec ⟨D.T.pos i + 1, h⟩ = false

def tailP (O : Type) [CommRing O] [IsDomain O] (r : ℕ) (D : BlockData N) (jp : ℕ)
    (y : MvPolynomial (Fin N × Fin r) (KK O)) (g : MvPolynomial (BVar N r D.T.t) (KK O)) :
    MvPolynomial (BVar N r D.T.t) (KK O) :=
  D.Eplus O (r := r) ^ jp * (∏ i, X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i) *
    X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus * rename (chainEmb N r D.T.t) y * g

theorem gen_mem (D : BlockData N) (thr : Fin D.T.q → WithTop ℤ) {j : Fin D.T.t → ℕ} {jp : ℕ} (hL : D.LevelOK j jp)
    {y : MvPolynomial (Fin N × Fin r) (KK O)} (hy : y ∈ YjtZ O (r := r) (D.lettersAt j jp) D.T.J thr)
    {g : MvPolynomial (BVar N r D.T.t) (KK O)} (hg : g ∈ XiPolZ O N r D.T.t (D.B - jp)) :
    (∏ i, D.Ehat O (r := r) i ^ j i) * tailP O r D jp y g ∈ SSt O r D thr := by
  unfold SSt BlockData.SSZ
  apply Submodule.subset_span
  refine Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨jp, Set.mem_iUnion.2 ⟨hL, ⟨y, hy, g, hg, ?_⟩⟩⟩⟩
  unfold tailP
  simp only [mul_assoc]
  rfl

theorem SSt_mono (D : BlockData N) {thr thr' : Fin D.T.q → WithTop ℤ} (h : ∀ k, thr k ≤ thr' k) :
    SSt O r D thr ≤ SSt O r D thr' := by
  unfold SSt BlockData.SSZ
  apply Submodule.span_mono
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨j, jp, hL, hx⟩ := hx
  obtain ⟨y, hy, g0, hg0, rfl⟩ := hx
  exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨jp, Set.mem_iUnion.2 ⟨hL,
    ⟨y, ⟨yjt_mono' _ _ h hy.1, hy.2⟩, g0, hg0, rfl⟩⟩⟩⟩

def IsMult (O : Type) [CommRing O] [IsDomain O] (r : ℕ) [NeZero r] (vec : Fin N → Bool) {q : ℕ} (J : Fin q → ℕ)
    (aW aE : Fin N) (q0 : MvPolynomial (Fin N × Fin r) (KK O)) : Prop :=
  ∀ (deg : Fin N → ℕ) (thr : Fin q → WithTop ℤ) (y : MvPolynomial (Fin N × Fin r) (KK O)),
    y ∈ YjtZ O (r := r) ⟨vec, deg⟩ J thr →
    q0 * y ∈ YjtZ O (r := r) ⟨vec, fun a => deg a + if a = aW ∨ a = aE then 1 else 0⟩ J
      (fun k => thr k + ((1 : ℤ) : WithTop ℤ))

theorem IsMult.pow {vec : Fin N → Bool} {q : ℕ} {J : Fin q → ℕ} {aW aE : Fin N}
    {q0 : MvPolynomial (Fin N × Fin r) (KK O)} (h : IsMult O r vec J aW aE q0) (l : ℕ) (deg : Fin N → ℕ)
    (thr : Fin q → WithTop ℤ) (y : MvPolynomial (Fin N × Fin r) (KK O)) (hy : y ∈ YjtZ O (r := r) ⟨vec, deg⟩ J thr) :
    q0 ^ l * y ∈ YjtZ O (r := r) ⟨vec, fun a => deg a + if a = aW ∨ a = aE then l else 0⟩ J
      (fun k => thr k + ((l : ℤ) : WithTop ℤ)) := by
  induction l with
  | zero =>
    simpa using hy
  | succ l ih =>
    have h1 := h _ _ _ ih
    rw [pow_succ', mul_assoc]
    have e1 : (fun a => (deg a + if a = aW ∨ a = aE then l else 0) + if a = aW ∨ a = aE then 1 else 0) =
        fun a => deg a + if a = aW ∨ a = aE then l + 1 else 0 := by
      funext a
      split_ifs <;> omega
    have e2 : (fun k => thr k + ((l : ℤ) : WithTop ℤ) + ((1 : ℤ) : WithTop ℤ)) =
        fun k => thr k + (((l + 1 : ℕ) : ℤ) : WithTop ℤ) := by
      funext k
      rw [add_assoc]
      norm_cast
    rw [e1, e2] at h1
    exact h1

theorem isMult_XX (D7 : Formalism.BasicNotions.D7) (vec : Fin N → Bool) {q : ℕ} (J : Fin q → ℕ) (aW aE : Fin N) (hne : aW ≠ aE)
    (hE : vec aE = false) (c c' : Fin r) : IsMult O r vec J aW aE (X (aW, c) * X (aE, c')) := by
  intro deg thr y hy
  have h1 := yjtZ_X (O := O) D7 ⟨vec, deg⟩ ⟨vec, fun a => deg a + if a = aE then 1 else 0⟩ rfl aE c' (fun _ => rfl) J
    (thr := thr) (thr' := thr) 0 (fun h => by simp [hE] at h) (fun k => by simp) hy
  have h2 := yjtZ_X (O := O) D7 ⟨vec, fun a => deg a + if a = aE then 1 else 0⟩
    ⟨vec, fun a => deg a + if a = aW ∨ a = aE then 1 else 0⟩ rfl aW c
    (fun i => by
      show deg i + _ = deg i + _ + _
      by_cases h1 : i = aW
      · subst h1; simp [hne]
      · simp [h1]) J (thr := thr) (thr' := fun k => thr k + ((1 : ℤ) : WithTop ℤ)) 1 (fun _ => le_rfl)
    (fun k => by norm_cast) h1
  rw [mul_assoc]
  exact h2

theorem IsMult.neg {vec : Fin N → Bool} {q : ℕ} {J : Fin q → ℕ} {aW aE : Fin N}
    {q0 : MvPolynomial (Fin N × Fin r) (KK O)} (h : IsMult O r vec J aW aE q0) : IsMult O r vec J aW aE (-q0) := by
  intro deg thr y hy
  rw [neg_mul]
  exact Submodule.neg_mem _ (h deg thr y hy)

theorem IsMult.sum {vec : Fin N → Bool} {q : ℕ} {J : Fin q → ℕ} {aW aE : Fin N} {ι : Type} (s : Finset ι)
    {q0 : ι → MvPolynomial (Fin N × Fin r) (KK O)} (h : ∀ i ∈ s, IsMult O r vec J aW aE (q0 i)) :
    IsMult O r vec J aW aE (∑ i ∈ s, q0 i) := by
  intro deg thr y hy
  rw [Finset.sum_mul]
  exact Submodule.sum_mem _ fun i hi => h i hi deg thr y hy

end GlobalTheory

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.CharZeroOfW
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees MvPolynomial

theorem p_not_unit {O : Type} [CommRing O] {p : ℕ} {w : O} (hw : Irreducible w) (hpw : w ^ 2 = (p : O)) :
    ¬ IsUnit (p : O) := by
  rw [← hpw]
  intro h
  exact hw.not_isUnit (isUnit_of_mul_isUnit_left (by rwa [pow_two] at h))

theorem charZero_of_w {O : Type} [CommRing O] [IsDomain O] {p : ℕ} (hp : p.Prime) {w : O} (hw : Irreducible w)
    (hpw : w ^ 2 = (p : O)) : CharZero O := by
  have hp0 : (p : O) ≠ 0 := by rw [← hpw]; exact pow_ne_zero _ hw.ne_zero
  have hpu := p_not_unit hw hpw
  obtain ⟨c, hc⟩ := CharP.exists O
  rcases CharP.char_is_prime_or_zero O c with h | h
  · exfalso
    have hc0 : (c : O) = 0 := CharP.cast_eq_zero O c
    by_cases hcp : c = p
    · exact hp0 (hcp ▸ hc0)
    · have hcop : Nat.Coprime c p := (Nat.coprime_primes h hp).2 hcp
      obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
      have h1 : ((a * c + b * p : ℤ) : O) = 1 := by rw [hab]; simp
      push_cast at h1
      rw [hc0, mul_zero, zero_add] at h1
      exact hpu (IsUnit.of_mul_eq_one_right _ h1)
  · subst h
    exact CharP.charP_to_charZero O

def KapAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (w : O),
    Irreducible w → w ^ 2 = (X.p : O) → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
      ∃ κ : O, κ ≠ 0 ∧ vLEO X.p κ (((X.m + 2) * lgSeg X j : ℕ) : ℝ) ∧
        ∀ μ, HomExp C0 CE1 CE2 X j b μ →
          zSeg (KK O) X j * (X.p : KK O) ^ padicValNat X.p (Nblk C0 CE1 CE2 X j b) * (Rblk C0 CE1 CE2 X j b : KK O) *
            (∏ v : BV C0 CE1 CE2 X j, ((baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)).factorial : KK O) *
              ((symLev X.p C0 CE1 CE2 X j v).factorial : KK O) ^ (μ v)) =
          algebraMap O (KK O) κ * (specConst X.p (X.seg C0 CE1 CE2 j) b : KK O)

theorem lev_pow (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    ∃ t, (X.seg C0 CE1 CE2 j).P X.p i = X.p ^ (t + 1) := by
  obtain ⟨s, ⟨-, -, -, h4⟩, h5⟩ := get_spec X.TT j i
  have hlt : (segDists X.TT j).get i < segG X.TT j := h5 ▸ h4
  refine ⟨segG X.TT j - (segDists X.TT j).get i - 1, ?_⟩
  show X.p ^ (segG X.TT j - (segDists X.TT j).get i) = _
  congr 1
  omega

theorem oddVar_data (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (hb : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) (v : BV C0 CE1 CE2 X j)
    (hv : IsOddVar C0 CE1 CE2 X j v) :
    (∃ t, symLev X.p C0 CE1 CE2 X j v = X.p ^ (t + 1)) ∧
      baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v) < symLev X.p C0 CE1 CE2 X j v := by
  rcases v with ⟨a, c⟩ | ⟨l, bo⟩
  · have h : (a : ℕ) < 2 * segS X.TT j := hv
    simp only [symLev, symVar, dif_pos h]
    refine ⟨lev_pow C0 CE1 CE2 X j _, ?_⟩
    rw [baseExp_odd]
    simp only [Fin.succ_ne_zero, and_false, if_false, add_zero]
    split_ifs
    · exact (hb.1.1 _ _).1
    · exact (hb.1.1 _ _).2
  · have h : (l : ℕ) < (X.seg C0 CE1 CE2 j).t := hv
    simp only [symLev, symVar, dif_pos h]
    refine ⟨lev_pow C0 CE1 CE2 X j _, ?_⟩
    rw [baseExp_odd]
    have hz : ¬ ((uTop (X.seg C0 CE1 CE2 j) ⟨l, h⟩ : ℕ) < (X.seg C0 CE1 CE2 j).sigma) := by
      show ¬ ((X.seg C0 CE1 CE2 j).sigma + (l : ℕ) < (X.seg C0 CE1 CE2 j).sigma)
      omega
    simp only [hz, false_and, if_false, add_zero]
    split_ifs
    · exact (hb.1.1 _ _).1
    · exact (hb.1.1 _ _).2

theorem endVar_data (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (v : BV C0 CE1 CE2 X j) (hv : ¬ IsOddVar C0 CE1 CE2 X j v) :
    symLev X.p C0 CE1 CE2 X j v = 1 ∧ baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v) = 0 := by
  rcases v with ⟨a, c⟩ | ⟨l, bo⟩
  · have h : ¬ (a : ℕ) < 2 * segS X.TT j := hv
    simp only [symLev, symVar, dif_neg h]
    exact ⟨trivial, baseExp_end C0 CE1 CE2 X j b _ _⟩
  · have h : ¬ (l : ℕ) < (X.seg C0 CE1 CE2 j).t := hv
    simp only [symLev, symVar, dif_neg h]
    exact ⟨trivial, baseExp_end C0 CE1 CE2 X j b _ _⟩

theorem factAt_of {D : Formalism.BasicNotions.D7} (h52 : Formalism.MainNotions.CovariantDegrees.FactorialUnitDecomposition D) {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ}
    (hK : KapAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) : FactAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  classical
  intro X _ O _ _ _ w hw h2 hD1 hH hc j b hb
  have hp : X.p.Prime := hD1.1
  have hpO := p_not_unit hw h2
  have hO : CharZero O := charZero_of_w hp hw h2
  have : CharZero (KK O) := charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))
  obtain ⟨κ, hκ0, hκv, hκ⟩ := hK X O w hw h2 hD1 hH hc j b hb
  have ht : ∀ v : BV C0 CE1 CE2 X j, ∃ t, IsOddVar C0 CE1 CE2 X j v → symLev X.p C0 CE1 CE2 X j v = X.p ^ (t + 1) := by
    intro v
    by_cases hv : IsOddVar C0 CE1 CE2 X j v
    · obtain ⟨t, ht⟩ := (oddVar_data C0 CE1 CE2 X j b hb v hv).1
      exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose t ht using ht
  obtain ⟨T, q, hT, hfa⟩ := fact_abs h52 hp hD1.2.1 (BV C0 CE1 CE2 X j) (IsOddVar C0 CE1 CE2 X j) t
    (fun v => baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)) (fun v => symLev X.p C0 CE1 CE2 X j v)
    (fun v hv => ⟨ht v hv, (oddVar_data C0 CE1 CE2 X j b hb v hv).2⟩)
    (fun v hv => endVar_data C0 CE1 CE2 X j b v hv) X.c
  have hq : ∀ ν, ∃ y : O, ν ∈ T → ((q ν : ℚ) : KK O) = algebraMap O (KK O) y := by
    intro ν
    by_cases hν : ν ∈ T
    · obtain ⟨y, hy⟩ := rat_int (O := O) (K := KK O) hp hpO (q ν) 0 (by simpa using (hT ν hν).2.2)
      exact ⟨y, fun _ => by rw [hy, pow_zero, one_mul]⟩
    · exact ⟨0, fun h => absurd h hν⟩
  choose qO hqO using hq
  refine ⟨κ, T, qO, hκ0, hκv, fun ν hν => ⟨(hT ν hν).1, (hT ν hν).2.1⟩, ?_⟩
  intro μ hμ
  obtain ⟨h, hh, heq⟩ := hfa μ
  obtain ⟨y, hy⟩ := rat_int (O := O) (K := KK O) hp hpO h X.c hh
  refine ⟨w ^ X.c * y, ?_⟩
  have hg : algebraMap O (KK O) (gEv T qO μ) =
      ((∑ ν ∈ T, q ν * ((ν.prod fun k i => (μ k).choose i : ℕ) : ℚ) : ℚ) : KK O) := by
    unfold gEv
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Rat.cast_sum]
    refine Finset.sum_congr rfl fun ν hν => ?_
    rw [map_mul, ← hqO ν hν, map_natCast, Rat.cast_mul, Rat.cast_natCast]
  have heqK := congrArg (fun x : ℚ => (x : KK O)) heq
  simp only [Rat.cast_mul, Rat.cast_prod, Rat.cast_natCast, Rat.cast_add, Rat.cast_one, Rat.cast_pow] at heqK
  have hsplit : (∏ x : BV C0 CE1 CE2 X j,
      ((baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j x)).factorial : KK O) * ((μ x).factorial : KK O) *
        ((symLev X.p C0 CE1 CE2 X j x).factorial : KK O) ^ (μ x)) =
      (∏ v : BV C0 CE1 CE2 X j, ((baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)).factorial : KK O) *
        ((symLev X.p C0 CE1 CE2 X j v).factorial : KK O) ^ (μ v)) * ∏ v : BV C0 CE1 CE2 X j, ((μ v).factorial : KK O) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => by ring
  have hmu : (expFact μ : KK O) = ∏ v : BV C0 CE1 CE2 X j, ((μ v).factorial : KK O) := by
    unfold expFact
    rw [Finsupp.prod_fintype _ _ (fun _ => rfl)]
    push_cast
    rfl
  have hW : (algebraMap O (KK O) (w ^ X.c)) ^ 2 = (X.p : KK O) ^ X.c := by
    rw [← map_pow, ← pow_mul, mul_comm, pow_mul, h2, map_pow, map_natCast]
  have hk := hκ μ hμ
  rw [expFact_ioExp, hg, hmu, map_add (f := _), map_one, map_mul, map_mul, Nat.cast_mul, Nat.cast_prod]
  rw [hsplit] at heqK
  linear_combination (zSeg (KK O) X j * (X.p : KK O) ^ padicValNat X.p (Nblk C0 CE1 CE2 X j b) *
      (Rblk C0 CE1 CE2 X j b : KK O)) * heqK +
    ((∏ v : BV C0 CE1 CE2 X j, ((μ v).factorial : KK O)) * (1 + (h : KK O))) * hk +
    (algebraMap O (KK O) κ * (specConst X.p (X.seg C0 CE1 CE2 j) b : KK O) *
      (∏ v : BV C0 CE1 CE2 X j, ((μ v).factorial : KK O))) * hy -
    (algebraMap O (KK O) κ * (specConst X.p (X.seg C0 CE1 CE2 j) b : KK O) *
      (∏ v : BV C0 CE1 CE2 X j, ((μ v).factorial : KK O)) * algebraMap O (KK O) y) * hW

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.KeyOne
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

theorem liftSubst_one_X {p f : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p f) O] (w : O) (r : ℕ)
    {ι : Type} {k : ℕ} (LL : LiftLetters ι) (v : ι × Fin k) :
    liftSubst p f O w r LL (1 : Matrix (Fin k) (Fin k) (WF p f)) (X v) =
      C (algebraMap O (KK O) (dW O w LL r v.1 v.2)) * X v := by
  unfold liftSubst
  rw [MvPolynomial.aeval_X, sigMat_one, inv_one]
  by_cases hv : LL.vec v.1 <;> simp [hv, Matrix.one_apply, dW] <;> split_ifs <;> simp_all

theorem liftSubst_one_hh {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (x : X.TT × Bool) (b : Fin (X.m + 1)) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
        (MvPolynomial.X (x, b)) =
      (if (x.2 = true ∧ 1 ≤ (b : ℕ)) ∨ (x.2 = false ∧ (b : ℕ) < 1) then
        C (algebraMap O (KK O) w) * MvPolynomial.X (x, b) else MvPolynomial.X (x, b)) := by
  rw [liftSubst_one_X]
  have hd : dW O w (hhLetters X.TT) 1 x b =
      if (x.2 = true ∧ 1 ≤ (b : ℕ)) ∨ (x.2 = false ∧ (b : ℕ) < 1) then w else 1 := rfl
  rw [hd]
  split_ifs <;> simp

private theorem liftSubst_X_true_zero_eq_X {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [Algebra (WF X.p X.n') O] (w : O) (y : X.TT) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
      (MvPolynomial.X ((y, true), (0 : Fin (X.m + 1)))) = MvPolynomial.X ((y, true), 0) := by
  rw [liftSubst_one_hh]
  simp

private theorem liftSubst_X_true_succ_eq_C_mul_X {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [Algebra (WF X.p X.n') O] (w : O) (y : X.TT) (c : Fin X.m) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
      (MvPolynomial.X ((y, true), c.succ)) =
        C (algebraMap O (KK O) w) * MvPolynomial.X ((y, true), c.succ) := by
  rw [liftSubst_one_hh]
  simp

private theorem liftSubst_X_false_zero_eq_C_mul_X {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [Algebra (WF X.p X.n') O] (w : O) (y : X.TT) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
      (MvPolynomial.X ((y, false), (0 : Fin (X.m + 1)))) =
        C (algebraMap O (KK O) w) * MvPolynomial.X ((y, false), 0) := by
  rw [liftSubst_one_hh]
  simp

private theorem liftSubst_X_false_succ_eq_X {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [Algebra (WF X.p X.n') O] (w : O) (y : X.TT) (c : Fin X.m) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
      (MvPolynomial.X ((y, false), c.succ)) = MvPolynomial.X ((y, false), c.succ) := by
  rw [liftSubst_one_hh]
  simp

theorem key3One_S {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 (kSkey O X j i) =
      w • (MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) * MvPolynomial.X ((topOdd X j i, false), 0) +
        w ^ (X.p ^ (segDists X.TT j).get i - 1) • (∑ c : Fin X.m,
          MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ (segDists X.TT j).get i) *
            MvPolynomial.X ((topOdd X j i, false), c.succ) : RHH O X) : RHH O X) := by
  have hq1 : 1 ≤ X.p ^ (segDists X.TT j).get i := Nat.one_le_pow _ _ (Fact.out : X.p.Prime).pos
  unfold kSkey
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Fin.sum_univ_succ]
  simp only [map_mul, map_pow, liftSubst_X_true_zero_eq_X, liftSubst_X_true_succ_eq_C_mul_X, liftSubst_X_false_zero_eq_C_mul_X, liftSubst_X_false_succ_eq_X]
  rw [Algebra.smul_def, Algebra.smul_def, MvPolynomial.algebraMap_apply,
    MvPolynomial.algebraMap_apply, map_pow, map_pow]
  obtain ⟨q', hq'⟩ : ∃ q', X.p ^ (segDists X.TT j).get i = q' + 1 :=
    ⟨_, (Nat.sub_add_cancel hq1).symm⟩
  rw [hq', Nat.add_sub_cancel]
  have hsum : ∑ c : Fin X.m, (C (algebraMap O (KK O) w) * MvPolynomial.X ((topStart X j, true), c.succ)) ^
      (q' + 1) * MvPolynomial.X ((topOdd X j i, false), c.succ) =
      C (algebraMap O (KK O) w) ^ (q' + 1) * ∑ c : Fin X.m,
        MvPolynomial.X ((topStart X j, true), c.succ) ^ (q' + 1) * MvPolynomial.X ((topOdd X j i, false), c.succ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hsum]
  ring

theorem key_lift_identity_lower {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) (c : Fin X.m) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 (kWkey O X j i c.succ) =
      w • (MvPolynomial.X ((topOdd X j i, true), c.succ) * MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) -
        w ^ (X.p ^ (segDists X.TT j).get i - 1) •
          (MvPolynomial.X ((topOdd X j i, true), 0) *
            MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ (segDists X.TT j).get i) : RHH O X) : RHH O X) := by
  have hq1 : 1 ≤ X.p ^ (segDists X.TT j).get i := Nat.one_le_pow _ _ (Fact.out : X.p.Prime).pos
  unfold kWkey
  simp only [map_sub, map_mul, map_pow, liftSubst_X_true_zero_eq_X, liftSubst_X_true_succ_eq_C_mul_X]
  rw [Algebra.smul_def, Algebra.smul_def, MvPolynomial.algebraMap_apply,
    MvPolynomial.algebraMap_apply, map_pow, map_pow]
  obtain ⟨q', hq'⟩ : ∃ q', X.p ^ (segDists X.TT j).get i = q' + 1 :=
    ⟨_, (Nat.sub_add_cancel hq1).symm⟩
  rw [hq', Nat.add_sub_cancel]
  ring

theorem loc4One {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (c : Fin X.m) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 (locC O X c.succ) =
      ∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ segG X.TT j - 1) -
        w ^ (∑ j : Fin (numSeg X.TT), (X.p ^ segG X.TT j - 1)) •
          (∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ segG X.TT j - 1) : RHH O X) := by
  unfold locC
  simp only [map_sub, map_prod, map_pow, liftSubst_X_true_zero_eq_X, liftSubst_X_true_succ_eq_C_mul_X]
  rw [Algebra.smul_def, MvPolynomial.algebraMap_apply, map_pow, map_pow,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl fun j _ => mul_pow _ _ _

def CoarseMultiplicityOrderBound : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X →
    ∀ (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)),
      ∀ g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g →
        InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (kSkey O X j i) 1 ∧
        ∀ c : Fin X.m, InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (kWkey O X j i c.succ) 1

def LocalOrderBound : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → 2 ≤ numSeg X.TT →
    ∀ (j0 : Fin (numSeg X.TT)) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')), IsGLW g →
      ratPlane X.p X.n' 1 g ≠ ratPlane X.p X.n' 1 1 →
      InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (locR O X j0) 1

theorem third_key_of_order (h : CoarseMultiplicityOrderBound) : CoarseMultiplicityBoundAtIdentity := by
  intro X _ O _ _ _ _ S hSq hD j i
  exact ⟨fun g hg => h X O S hSq hD j i g hg, key3One_S S.w j i, fun c => key_lift_identity_lower S.w j i c⟩

theorem local_fourth_of_order (h : LocalOrderBound) : LocalBoundAtIdentity := by
  intro X _ O _ _ _ _ S hSq hD hn
  exact ⟨fun j0 g hg hr => h X O S hSq hD hn j0 g hg hr, fun c => loc4One S.w c⟩

end Formalism.MainNotions.ColumnSystems.Pf
end
end

