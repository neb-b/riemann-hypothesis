module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.RestBlockForm
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0003

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.CoarseMultiplicityAtIdentity
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def ka1 (X : Loc) : ℝ := 13 * X.k * X.N1 * X.Q

def localOrderCap (C0 : ℝ) (X : Loc) : ℝ :=
  (X.a : ℝ) / (X.p : ℝ) ^ 2 + 3 * X.b' / X.p + (X.La C0 / X.k + 4 / (X.p : ℝ) ^ 2) * (4 * (X.a : ℝ) / X.p) +
    2 * X.La C0 * X.b' / X.k

def BLk (C0 Cde CE1 CE2 : ℝ) (X : Loc) (E : ℝ) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m) : Prop :=
  DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b ∧
  (∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).sigma ≤ (i : ℕ) →
    b.o i ≤ coarseA X.p (X.seg C0 CE1 CE2 j) b i ∧
    (b.o i : ℝ) ≤ (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) * (1 - X.de C0 Cde / 4) + E ∧
    b.w i = 0 ∧ b.sg i = 0) ∧
  (∀ i : Fin (segS X.TT j), (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma →
    b.o i = 0 ∧ b.w i ≤ coarseA X.p (X.seg C0 CE1 CE2 j) b i ∧
    b.sg i ≤ coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i ∧
    (b.sg i : ℝ) ≤ 2 * X.La C0 * ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) / X.k + E) ∧
  b.oPlus ≤ segAPlus X.TT X.aT j ∧ (b.oPlus : ℝ) ≤ localOrderCap C0 X + E

def genSet (O : Type) [CommRing O] [IsDomain O] {N r : ℕ} [NeZero r] (D : BlockData N) :
    Set (MvPolynomial (BVar N r D.T.t) (KK O)) :=
  ⋃ (j : Fin D.T.t → ℕ) (jp : ℕ) (_ : D.LevelOK j jp), D.gens O (r := r) j jp

def InGen (O : Type) [CommRing O] [IsDomain O] (C0 CE1 CE2 mm : ℝ) (X : Loc) [NeZero X.m] (β : GlobalTheory X)
    (s : Syms O C0 CE1 CE2 X) : Prop :=
  ∀ j, s j ∈ genSet O (r := X.m)
    (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mm (β j))

def ordFam (C0 CE1 CE2 : ℝ) (X : Loc) (β : GlobalTheory X) : ℕ := ∑ j, blockOrd X.p (X.seg C0 CE1 CE2 j) (β j)

def SSg (O : Type) [CommRing O] [IsDomain O] (C0 Cde CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (mu E : ℝ) (o : ℕ) :
    Submodule O (MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)) :=
  Submodule.span O {σ | ∃ β : GlobalTheory X, (∀ j, BLk C0 Cde CE1 CE2 X E j (β j)) ∧ ordFam C0 CE1 CE2 X β ≤ o ∧
    ∃ s : Syms O C0 CE1 CE2 X, InGen O C0 CE1 CE2 mu X β s ∧ σ = symFam (KK O) X.p C0 CE1 CE2 X β s}

def IsCleanAwayFromPlane (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (o : ℕ)
    (F : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)) : Prop :=
  F ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (hhDegs X.TT X.aT X.bT) ∧
    InA (C (algebraMap O (KK O) (w ^ o)) * F) ∧
    ∀ g' : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g' →
      ratPlane X.p X.n' 1 g' ≠ ratPlane X.p X.n' 1 g → InWjRg X.p X.n' O w 1 (hhLetters X.TT) g' F X.c

def RawTailBody (C0 Cde CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O]
    [Algebra (WF X.p X.n') O] (w : O) (mm : ℝ) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) : Prop :=
    ∀ n : ℕ, 1 ≤ n → n ≤ X.c →
    ∀ β : GlobalTheory X, (∀ j, BLk C0 Cde CE1 CE2 X (((X.c - n : ℕ) : ℝ) * ka1 X) j (β j)) →
    ∀ s : Syms O C0 CE1 CE2 X, InGen O C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β s →
      ∃ (raw : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O))
        (τ : ℕ → MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)),
        IsCleanAwayFromPlane X O w g (ordFam C0 CE1 CE2 X β) raw ∧
        (∀ ε ∈ Finset.Ico 1 n, τ ε ∈ SSg O C0 Cde CE1 CE2 X (mm + ((n - ε : ℕ) : ℝ) * ka1 X)
          (((X.c - (n - ε) : ℕ) : ℝ) * ka1 X) (ordFam C0 CE1 CE2 X β + ε)) ∧
        InWj w (liftSubst X.p X.n' O w 1 (hhLetters X.TT) g raw - symFam (KK O) X.p C0 CE1 CE2 X β s -
          ∑ ε ∈ Finset.Ico 1 n, (w ^ ε) • τ ε) n

def RawTailAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) →
    ∀ g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g →
      RawTailBody C0 Cde CE1 CE2 X O S.w mm g

def RawTailAt1 (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) → RawTailBody C0 Cde CE1 CE2 X O S.w mm 1

def RestRawTail1 : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => RawTailAt1 C0 CYb Cde Ck CD Cb CE1 CE2 Cc

def CoarseMultiplicityAtIdentity (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) →
    ∀ β : ∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m,
      (∀ j, Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (β j)) →
    ∀ s : ∀ j : Fin (numSeg X.TT), MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O),
      (∀ j, s j ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j)
        (13 * X.k * X.N1 * X.Q * (X.c : ℝ) + mm) (β j)).SSZ O (r := X.m)) →
      ∃ F ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (hhDegs X.TT X.aT X.bT),
        InA (C (algebraMap O (KK O) (S.w ^ (∑ j, blockOrd X.p (X.seg C0 CE1 CE2 j) (β j)))) * F) ∧
        InWj S.w (liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) 1 F - symFam (KK O) X.p C0 CE1 CE2 X β s) X.c ∧
        ∀ g' : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g' →
          ratPlane X.p X.n' 1 g' ≠ ratPlane X.p X.n' 1 1 → InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g' F X.c

def KeptBLAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc), D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b → BLk C0 Cde CE1 CE2 X 0 j b

def RestKeptBL : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => KeptBLAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.FTDefs
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory MvPolynomial

def OrthAt (C0 CE1 CE2 : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (O : Type) [CommRing O] [IsDomain O] (mm : ℝ), D1num X →
    ∀ (j : Fin (numSeg X.TT)) (b b' : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b' → b ≠ b' →
      ∀ s ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mm b).SSZ O (r := X.m),
      ∀ s' ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mm b').SSZ O (r := X.m),
        fock (ioBlock (KK O) X.p C0 CE1 CE2 X j b s) (ioBlock (KK O) X.p C0 CE1 CE2 X j b' s') = 0

def ProdAt (C0 CE1 CE2 : ℝ) : Prop :=
  ∀ (X : Loc) (K : Type) [Field K], 2 ≤ numSeg X.TT → ∀ (β β' : GlobalTheory X)
    (s s' : ∀ j : Fin (numSeg X.TT), MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) K),
    fock (symFam K X.p C0 CE1 CE2 X β s) (symFam K X.p C0 CE1 CE2 X β' s') =
      ∏ j, fock (ioBlock K X.p C0 CE1 CE2 X j (β j) (s j)) (ioBlock K X.p C0 CE1 CE2 X j (β' j) (s' j))

def SymPolAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (O : Type) [CommRing O] [IsDomain O], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (mm : ℝ) (β : GlobalTheory X), KeptAll C0 CE1 CE2 X β → ∀ s : Syms O C0 CE1 CE2 X, InSSZ O C0 CE1 CE2 mm X β s →
      symFam (KK O) X.p C0 CE1 CE2 X β s ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (hhDegs X.TT X.aT X.bT)

def IntAt : Prop :=
  ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O], p.Prime → UniformizedDVR p O → ∀ (w : O)
    (n' m : ℕ) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ),
    ∀ P ∈ Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT),
    ∀ (Q : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O)) (i : ℕ), InWj w P i → InA (O := O) Q →
      ∃ y : O, zTen (KK O) p m TT aT bT * fock P Q = algebraMap O (KK O) (w ^ i * y)

def NumAt (C0 Cde CE1 CE2 : ℝ) : Prop :=
  ∀ X : Loc, Std C0 Cde CE1 CE2 1 X → ∑ j : Fin (numSeg X.TT), (((X.m + 2) * lgSeg X j : ℕ) : ℝ) ≤ 4 * X.kap0

def ZProdAt : Prop :=
  ∀ (X : Loc) (K : Type) [Field K], 2 ≤ numSeg X.TT → zTen K X.p X.m X.TT X.aT X.bT = ∏ j, zSeg K X j

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Kummer
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem multinomial_val (p : ℕ) {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ) :
    (Nat.multinomial s f).factorization p ≤ (s.card - 1) * Nat.log p (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Nat.multinomial_insert ha, Nat.factorization_mul (Nat.choose_pos (Nat.le_add_right _ _)).ne'
      (Nat.multinomial_pos _ _).ne', Finsupp.add_apply, Finset.card_insert_of_notMem ha, Finset.sum_insert ha,
      Nat.add_sub_cancel]
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    · have h1 := @Nat.factorization_choose_le_log p (f a + ∑ i ∈ s, f i) (f a)
      have h2 : Nat.log p (∑ i ∈ s, f i) ≤ Nat.log p (f a + ∑ i ∈ s, f i) :=
        Nat.log_mono_right (Nat.le_add_left _ _)
      obtain ⟨k, hk⟩ : ∃ k, s.card = k + 1 := ⟨s.card - 1, (Nat.succ_pred_eq_of_pos hs.card_pos).symm⟩
      rw [hk, Nat.add_sub_cancel] at ih
      rw [hk, add_mul, one_mul]
      have h3 := ih.trans (Nat.mul_le_mul_left k h2)
      omega

theorem expFact_eq {ι : Type*} [Fintype ι] {n : ℕ} (μ : ι × Fin n →₀ ℕ) :
    expFact μ = ∏ x : ι, ∏ c : Fin n, (μ (x, c)).factorial := by
  rw [expFact, Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero), Fintype.prod_prod_type]

theorem expFact_mul {ι : Type*} [Fintype ι] {n : ℕ} (p : ℕ) (d : ι → ℕ) (μ : ι × Fin n →₀ ℕ)
    (hμ : ∀ x, multideg μ x = d x) :
    ∃ M : ℕ, M ≠ 0 ∧ expFact μ * M = ∏ x, (d x).factorial ∧
      M.factorization p ≤ ∑ x, (n - 1) * Nat.log p (d x) := by
  classical
  refine ⟨∏ x : ι, Nat.multinomial Finset.univ (fun c : Fin n => μ (x, c)), ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun x _ => (Nat.multinomial_pos _ _).ne'
  · rw [expFact_eq, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [Nat.multinomial_spec, ← hμ x]
    rfl
  · rw [Nat.factorization_prod fun x _ => (Nat.multinomial_pos _ _).ne', Finsupp.finsetSum_apply]
    refine Finset.sum_le_sum fun x _ => ?_
    have := multinomial_val p Finset.univ (fun c : Fin n => μ (x, c))
    rw [Finset.card_univ, Fintype.card_fin] at this
    rw [← hμ x]
    exact this

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.SegFormZeroRight
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem famOK_zero {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {C0 CE1 CE2 Cm : ℝ} {X : Loc}
    [NeZero X.m] {β : GlobalTheory X} {u : Vecs O C0 CE1 CE2 X} (h : FamOK O C0 CE1 CE2 Cm X β u) {j : Fin (numSeg X.TT)}
    (hj : ¬ Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (β j)) : u j = 0 := by
  obtain ⟨hL, hz⟩ := h j
  funext b
  by_cases hb : b = β j
  · subst hb
    have hm := (Submodule.mem_pi.mp hL) (β j) (Set.mem_univ _)
    rw [if_neg hj] at hm
    simpa using hm
  · exact hz b hb

theorem segForm_zero_left {O : Type} [CommRing O] [IsDomain O] {p r s : ℕ} (S : SegData s)
    (g : SegVs O r s S.t) : segForm O p r S 0 g = 0 := by
  unfold segForm fock
  simp

end Formalism.MainNotions.ColumnSystems.Pf
end
end

