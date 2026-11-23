module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.RestBlockForm
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0008
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0009
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0002
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0004
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LiftSubstitutionCoeffDivisible
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0003
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0014

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BFDefs
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

abbrev BV (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) :=
  BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t

abbrev bD (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (mm : ℝ) (b : SegBlock (segS X.TT j) X.m) :
    BlockData (2 * segS X.TT j + 1) :=
  blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mm b

abbrev sszB (O : Type) [CommRing O] [IsDomain O] (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT)) (mm : ℝ)
    (b : SegBlock (segS X.TT j) X.m) : Submodule O (MvPolynomial (BV C0 CE1 CE2 X j) (KK O)) :=
  (bD C0 CE1 CE2 X j mm b).SSZ O (r := X.m)

def baseExp (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m) :
    ((X.TT × Bool) × Fin (X.m + 1)) →₀ ℕ :=
  (∑ i : Fin (segS X.TT j), ∑ c : Fin (X.m + 1),
    (Finsupp.single ((topOdd X j i, true), c) (b.rz i c) + Finsupp.single ((topOdd X j i, false), c) (b.ry i c))) +
  ∑ i : Fin (segS X.TT j), if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
    Finsupp.single ((topOdd X j i, true), (0 : Fin (X.m + 1)))
        ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i)) +
      Finsupp.single ((topOdd X j i, false), (0 : Fin (X.m + 1))) ((X.seg C0 CE1 CE2 j).P X.p i * b.sg i)
  else 0

def ioExp (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (μ : BV C0 CE1 CE2 X j →₀ ℕ) : ((X.TT × Bool) × Fin (X.m + 1)) →₀ ℕ :=
  baseExp C0 CE1 CE2 X j b +
    μ.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * n)

def gOp {O : Type} [CommRing O] [IsDomain O] {σ : Type} (T : Finset (σ →₀ ℕ)) (q : (σ →₀ ℕ) → O)
    (u : MvPolynomial σ (KK O)) : MvPolynomial σ (KK O) :=
  ∑ ν ∈ T, q ν • (monomial ν (1 : KK O) * divDer ν u)

def gEv {O : Type} [CommRing O] {σ : Type} (T : Finset (σ →₀ ℕ)) (q : (σ →₀ ℕ) → O) (μ : σ →₀ ℕ) : O :=
  ∑ ν ∈ T, q ν * ((ν.prod fun k i => (μ k).choose i : ℕ) : O)

def Balanced {s : ℕ} (r : ℕ) (S : SegData s) (ω : BVar (2 * s + 1) r S.t → ℕ) (ωL : Fin (2 * s + 1 + 1) → ℕ) : Prop :=
  (∀ a c, ω (Sum.inl (a, c)) = ωL a) ∧
  (∀ l : Fin S.t, ω (Sum.inr (Fin.castSucc l, false)) + ω (Sum.inr (Fin.castSucc l, true)) =
      ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ))) + ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ) + 1))) ∧
  ω (Sum.inr (Fin.last S.t, false)) + ω (Sum.inr (Fin.last S.t, true)) =
      ωL (Fin.castSucc ⟨2 * s, by omega⟩) + ωL (Fin.last _)

def HomExp (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (μ : BV C0 CE1 CE2 X j →₀ ℕ) : Prop :=
  ∀ (ω : BV C0 CE1 CE2 X j → ℕ) (ωL : Fin (2 * segS X.TT j + 1 + 1) → ℕ), Balanced X.m (X.seg C0 CE1 CE2 j) ω ωL →
    ∑ v, μ v * ω v = OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b ω ωL

def letterOf (X : Loc) (j : Fin (numSeg X.TT)) (a : Fin (2 * segS X.TT j + 1 + 1)) : X.TT × Bool :=
  if h : (a : ℕ) < 2 * segS X.TT j then (topOdd X j ⟨(a : ℕ) / 2, by omega⟩, decide ((a : ℕ) % 2 = 0))
  else (topEnd X j, decide ((a : ℕ) = 2 * segS X.TT j))


open Classical in
def lamW (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (x : X.TT × Bool) : BV C0 CE1 CE2 X j → ℕ :=
  fun v => if (symVar C0 CE1 CE2 X j v).1 = x then 1 else 0

open Classical in
def lamL (X : Loc) (j : Fin (numSeg X.TT)) (x : X.TT × Bool) : Fin (2 * segS X.TT j + 1 + 1) → ℕ :=
  fun a => if letterOf X j a = x then 1 else 0

def cdeg (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m) (x : X.TT × Bool) : ℕ :=
  OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b (lamW C0 CE1 CE2 X j x) (lamL X j x)

def Nblk (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m) : ℕ :=
  (∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial) * specConst X.p (X.seg C0 CE1 CE2 j) b

def IsOddVar (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) : BV C0 CE1 CE2 X j → Prop
  | Sum.inl (a, _) => (a : ℕ) < 2 * segS X.TT j
  | Sum.inr (l, _) => (l : ℕ) < (X.seg C0 CE1 CE2 j).t

def IoFockAt : Prop :=
  ∀ (C0 CE1 CE2 : ℝ) (X : Loc) (K : Type) [Field K], 0 < X.p → ∀ (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) (u u' : MvPolynomial (BV C0 CE1 CE2 X j) K),
    fock (ioBlock K X.p C0 CE1 CE2 X j b u) (ioBlock K X.p C0 CE1 CE2 X j b u') =
      ∑ μ ∈ u.support, u.coeff μ * u'.coeff μ * (expFact (ioExp C0 CE1 CE2 X j b μ) : K)

def EigAt : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (σ : Type) (T : Finset (σ →₀ ℕ)) (q : (σ →₀ ℕ) → O)
    (u : MvPolynomial σ (KK O)) (μ : σ →₀ ℕ),
    (gOp T q u).coeff μ = algebraMap O (KK O) (gEv T q μ) * u.coeff μ

def HomAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (O : Type) [CommRing O] [IsDomain O], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b → ∀ (mm : ℝ),
      ∀ u ∈ Submodule.span (KK O) (sszB O C0 CE1 CE2 X j mm b : Set (MvPolynomial (BV C0 CE1 CE2 X j) (KK O))),
      ∀ μ ∈ u.support, HomExp C0 CE1 CE2 X j b μ

def DvdAt : Prop :=
  ∀ (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
    Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
    ∀ μ, HomExp C0 CE1 CE2 X j b μ → expFact μ * specConst X.p (X.seg C0 CE1 CE2 j) b ∣ Nblk C0 CE1 CE2 X j b

def SatAt : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N r : ℕ) [NeZero r] (D : BlockData N),
    ∀ x ∈ Submodule.span (KK O) ((D.SSZ O (r := r) : Submodule O (MvPolynomial (BVar N r D.T.t) (KK O))) :
        Set (MvPolynomial (BVar N r D.T.t) (KK O))),
      x ∈ IntPol O (BVar N r D.T.t) → x ∈ D.SSZ O (r := r)

def GThetaAt : Prop :=
  ∀ (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero (KK O)] (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
    Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
    ∀ (c : ℕ) (T : Finset (BV C0 CE1 CE2 X j →₀ ℕ)) (q : (BV C0 CE1 CE2 X j →₀ ℕ) → O),
      (∀ ν ∈ T, (ν.sum fun _ n => n) ≤ 4 * c ∧ ∀ v ∈ ν.support, IsOddVar C0 CE1 CE2 X j v) →
      ∀ (mm : ℝ), ∀ u ∈ sszB O C0 CE1 CE2 X j mm b, gOp T q u ∈ sszB O C0 CE1 CE2 X j (mm - 4 * (c : ℝ)) b

def FactAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (w : O),
    Irreducible w → w ^ 2 = (X.p : O) → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
      ∃ (κ : O) (T : Finset (BV C0 CE1 CE2 X j →₀ ℕ)) (q : (BV C0 CE1 CE2 X j →₀ ℕ) → O),
        κ ≠ 0 ∧ vLEO X.p κ (((X.m + 2) * lgSeg X j : ℕ) : ℝ) ∧
        (∀ ν ∈ T, (ν.sum fun _ n => n) ≤ 4 * X.c ∧ ∀ v ∈ ν.support, IsOddVar C0 CE1 CE2 X j v) ∧
        ∀ μ, HomExp C0 CE1 CE2 X j b μ → ∃ h : O,
          zSeg (KK O) X j * (X.p : KK O) ^ padicValNat X.p (Nblk C0 CE1 CE2 X j b) *
              (expFact (ioExp C0 CE1 CE2 X j b μ) : KK O) * algebraMap O (KK O) (gEv T q μ) =
            algebraMap O (KK O) κ * ((expFact μ : KK O) * (specConst X.p (X.seg C0 CE1 CE2 j) b : KK O)) *
              algebraMap O (KK O) (1 + w ^ X.c * h)

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.HookKeyOrderGeOne
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

section Order

variable {O : Type} [CommRing O] [IsDomain O] {σ : Type}

theorem inWj_mul {w : O} {P Q : MvPolynomial σ (KK O)} {a b : ℕ} (hP : InWj w P a) (hQ : InWj w Q b) :
    InWj w (P * Q) (a + b) := by
  classical
  intro m
  choose cp hcp using hP
  choose cq hcq using hQ
  refine ⟨∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, cp x.1 * cq x.2, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeff_mul, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hcp, hcq, ← map_mul]
  congr 1
  ring

theorem inWj_one (w : O) : InWj w (1 : MvPolynomial σ (KK O)) 0 := by
  classical
  intro m
  rw [coeff_one]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

theorem inWj_pow {w : O} {P : MvPolynomial σ (KK O)} {a : ℕ} (hP : InWj w P a) (n : ℕ) : InWj w (P ^ n) (n * a) := by
  induction n with
  | zero => simpa using inWj_one w
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact inWj_mul ih hP

theorem inWj_prod {w : O} {ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ (KK O)) (a : ι → ℕ)
    (h : ∀ i ∈ s, InWj w (P i) (a i)) : InWj w (∏ i ∈ s, P i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using inWj_one w
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact inWj_mul (h i (Finset.mem_insert_self _ _)) (ih fun l hl => h l (Finset.mem_insert_of_mem hl))

end Order

section Rg

variable {p f : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (WF p f) O]
  {k : ℕ} {ι : Type}

theorem inWjRg_mul {w : O} {r : ℕ} {LL : LiftLetters ι} {g : Matrix (Fin k) (Fin k) (WF p f)}
    {F G : MvPolynomial (ι × Fin k) (KK O)} {a b : ℕ} (hF : InWjRg p f O w r LL g F a)
    (hG : InWjRg p f O w r LL g G b) : InWjRg p f O w r LL g (F * G) (a + b) := by
  unfold InWjRg at *
  rw [map_mul]
  exact inWj_mul hF hG

theorem inWjRg_pow {w : O} {r : ℕ} {LL : LiftLetters ι} {g : Matrix (Fin k) (Fin k) (WF p f)}
    {F : MvPolynomial (ι × Fin k) (KK O)} {a : ℕ} (hF : InWjRg p f O w r LL g F a) (n : ℕ) :
    InWjRg p f O w r LL g (F ^ n) (n * a) := by
  unfold InWjRg at *
  rw [map_pow]
  exact inWj_pow hF n

theorem inWjRg_prod {w : O} {r : ℕ} {LL : LiftLetters ι} {g : Matrix (Fin k) (Fin k) (WF p f)} {κ : Type}
    (s : Finset κ) (F : κ → MvPolynomial (ι × Fin k) (KK O)) (a : κ → ℕ)
    (h : ∀ i ∈ s, InWjRg p f O w r LL g (F i) (a i)) : InWjRg p f O w r LL g (∏ i ∈ s, F i) (∑ i ∈ s, a i) := by
  unfold InWjRg at *
  rw [map_prod]
  exact inWj_prod s _ a h

def hKey (O : Type) [CommRing O] [IsDomain O] {ι : Type} (k : ℕ) (l l' : ι) : MvPolynomial (ι × Fin k) (KK O) :=
  ∑ a : Fin k, X (l, a) * X (l', a)

theorem hook_key_lift_exact (w : O) (LL : LiftLetters ι) (r : ℕ) (g : Matrix (Fin k) (Fin k) (WF p f)) (hg : IsGLW g) (l l' : ι)
    (hl : LL.vec l = true) (hl' : LL.vec l' = false) (hpos : LL.pos l = LL.pos l') :
    liftSubst p f O w r LL g (hKey O k l l') = C (algebraMap O (KK O) w) * hKey O k l l' := by
  classical
  unfold hKey
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_mul, liftSubst_X_vec p f O w LL r g hg l _ hl, liftSubst_X_cov p f O w LL r g l' _ hl']
  have hinv : ∀ b b' : Fin k, ∑ a : Fin k, sigMat p f O g⁻¹ (LL.pos l) b a * sigMat p f O g (LL.pos l') a b' =
      if b = b' then 1 else 0 := by
    intro b b'
    rw [← hpos, ← Matrix.mul_apply, ← sigMat_mul, Matrix.nonsing_inv_mul g hg, sigMat_one, Matrix.one_apply]
  have hd : ∀ b : Fin k, dW O w LL r l b * dW O w LL r l' b = w := by
    intro b
    by_cases hb : b.val < r
    · have hb' : ¬ r ≤ b.val := by omega
      simp [dW, hl, hl', hb, hb']
    · have hb' : r ≤ b.val := by omega
      simp [dW, hl, hl', hb, hb']
  calc ∑ a : Fin k, (∑ b : Fin k, C (algebraMap O (KK O) (dW O w LL r l b)) * X (l, b) *
          C (sigMat p f O g⁻¹ (LL.pos l) b a)) *
        (∑ b' : Fin k, C (algebraMap O (KK O) (dW O w LL r l' b')) * X (l', b') * C (sigMat p f O g (LL.pos l') a b'))
      = ∑ b : Fin k, ∑ b' : Fin k, C (algebraMap O (KK O) (dW O w LL r l b)) * X (l, b) *
          (C (algebraMap O (KK O) (dW O w LL r l' b')) * X (l', b')) *
          C (∑ a : Fin k, sigMat p f O g⁻¹ (LL.pos l) b a * sigMat p f O g (LL.pos l') a b') := by
        simp only [Finset.sum_mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b' _ => ?_
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [map_mul]
        ring
    _ = ∑ b : Fin k, C (algebraMap O (KK O) (dW O w LL r l b)) * X (l, b) *
          (C (algebraMap O (KK O) (dW O w LL r l' b)) * X (l', b)) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [hinv]
        rw [Finset.sum_eq_single b]
        · simp
        · intro b' _ hne
          rw [if_neg (Ne.symm hne)]
          simp
        · intro h; exact absurd (Finset.mem_univ b) h
    _ = C (algebraMap O (KK O) w) * ∑ a : Fin k, X (l, a) * X (l', a) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        have hC : (C (algebraMap O (KK O) w) : MvPolynomial (ι × Fin k) (KK O)) =
            C (algebraMap O (KK O) (dW O w LL r l b)) * C (algebraMap O (KK O) (dW O w LL r l' b)) := by
          rw [← map_mul, ← map_mul, hd b]
        rw [hC]
        ring

theorem hook_key_order_ge_one (w : O) (LL : LiftLetters ι) (r : ℕ) (g : Matrix (Fin k) (Fin k) (WF p f)) (hg : IsGLW g) (l l' : ι)
    (hl : LL.vec l = true) (hl' : LL.vec l' = false) (hpos : LL.pos l = LL.pos l') :
    InWjRg p f O w r LL g (hKey O k l l') 1 := by
  classical
  unfold InWjRg
  rw [hook_key_lift_exact w LL r g hg l l' hl hl' hpos, C_mul_eq_smul]
  have h0 : InWj w (hKey O k l l') 0 := by
    unfold hKey
    refine (wjSub w 0).sum_mem fun a _ => ?_
    have hX : ∀ v : ι × Fin k, InWj w (X v : MvPolynomial (ι × Fin k) (KK O)) 0 := by
      intro v m
      rw [coeff_X]
      split_ifs
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩
    exact inWj_mul (hX _) (hX _)
  have := wj_smul_pow h0 1
  rwa [pow_one, zero_add] at this

end Rg

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.MulMatQOne
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.ColumnSystems.Pf.TF

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility
open Formalism.MainNotions.G.LatticeSystems (la_tw lb_D la_tw_det lb_D_det H0_eq_twisted_nabla la_indep)
open Formalism.L2.G.Model (Lin Th0 Aa Lin_comp Lin_one Lin_Pol Lin_smul Th0_inj mem_tens_nabla mem_tens_dw map_Pol mem_Pol VS
  letterWt_anti tensor_lattice_twist_eq tens_Le edgeLat_of la_tw_mul la_tw_transpose la_tw_inv dE invT_mul_D dual_edgeBasis w_ne p_eq
  pQ_ne kapR kapR_alg lift_eq Bm Bm_eq Mx Mx_det Avec pol_iff thF gen_equiv gen_A gen_R mem_scale2 edgePlane)
open Formalism.L2.G.Model.TS

section

variable {p n' : ℕ} [Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {jO : W →+* O} {w : O}

theorem Avec_eq {m : ℕ} (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) :
    (Avec (vecH TT) (hhDegs TT aT bT) : ℤ) = AHH TT aT bT := by
  unfold Avec AHH
  push_cast
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, vecH, hhDegs, if_true, Bool.false_eq_true, if_false, add_zero]
  exact Finset.sum_coe_sort TT (fun s => (hhDeg aT bT s true : ℤ))

theorem flatTheta (hS : HidaSetting p n' W Qq O Kf ι σ jO w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ) (m : ℕ)
    (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) (hm : 1 ≤ m) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)
    (hh : IsUnit h.det) :
    ∃ Θ : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O) ≃ₗ[O]
        ↥(VHH (m := m) Kf TT aT bT),
      IsFlatTheta ι σ jO w φ TT aT bT h Θ ∧
      ∀ F, ((Θ F : ↥(VHH (m := m) Kf TT aT bT)) : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) =
        thF hS m (vecH TT) (fun x => la_tw ι σ x.1.val.val h) F.1 := by
  letI : Algebra (WF p n') O := algOfIdent jO φ
  have hw := w_ne hS
  obtain ⟨Θ0, hΘ0⟩ := gen_equiv hS m hm (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT)
    (fun x => la_tw ι σ x.1.val.val h) (fun x => la_tw_det _ _ _ _ hh)
  have hV : VS Kf m (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) = VHH (m := m) Kf TT aT bT := rfl
  let Θ : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT)).restrictScalars O) ≃ₗ[O]
      ↥(VHH (m := m) Kf TT aT bT) := Θ0.trans ((LinearEquiv.ofEq _ _ hV).restrictScalars O)
  have hΘ : ∀ F, ((Θ F : ↥(VHH (m := m) Kf TT aT bT)) :
      MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) =
      thF hS m (fun x : TT × Bool => x.2) (fun x => la_tw ι σ x.1.val.val h) F.1 := fun F => hΘ0 F
  refine ⟨Θ, ⟨?_, ?_, ?_⟩, hΘ⟩
  · intro F
    rw [gen_A hS m hm (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT)
      (fun x => la_tw ι σ x.1.val.val h) (fun x => la_tw_det _ _ _ _ hh) F.1 F.2, ← hΘ F,
      ← tensor_lattice_twist_eq hS m (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) (fun x => x.1.val) h hh]
    rfl
  · intro g hg e he F i
    have h1 : InWjRg p n' O w 1 (Formalism.MainNotions.ColumnSystems.hhLetters TT) g F.1 i ↔
        ∃ y ∈ tensorLat O Kf (fun s : TT × Bool => nablaLTw O Kf m
            (letterWt m (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT s) s.2) (Mx ι σ w φ 1 (fun x : TT × Bool => x.1.val) h g s)),
          thF hS m (fun x : TT × Bool => x.2) (fun x => la_tw ι σ x.1.val.val h) F.1 =
            (algebraMap O Kf w ^ ((i : ℤ) -
              (Avec (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) : ℤ))) • y :=
      gen_R hS φ hφ m hm 1 (Formalism.MainNotions.ColumnSystems.hhLetters TT) (fun x => x.1.val) (fun _ => rfl)
        (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) h hh g hg F.1 F.2 i
    rw [h1, ← hΘ F, ← tens_Le hS φ m 1 (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) (fun x => x.1.val)
      h hh g hg e he]
    have hA : (Avec (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) : ℤ) = AHH TT aT bT :=
      Avec_eq (m := m) TT aT bT
    have h2 := mem_scale2 (O := O) (VHH (m := m) Kf TT aT bT)
      (HHten O TT aT bT fun s => LeAt p ι σ w s.val e) (algebraMap O Kf w ^ (i : ℤ))
      (algebraMap O Kf w ^ (-AHH TT aT bT)) (zpow_ne_zero _ hw) (zpow_ne_zero _ hw) (Θ F)
    have e1 : algebraMap O Kf w ^ (i : ℤ) * algebraMap O Kf w ^ (-AHH TT aT bT) = algebraMap O Kf w ^
        ((i : ℤ) - (Avec (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) : ℤ)) := by
      rw [← zpow_add₀ hw, ← sub_eq_add_neg, ← hA]
    rw [e1] at h2
    exact h2.symm
  · intro e he hsrc
    exact (edgePlane p n' W Qq O Kf ι σ jO w hS φ hφ m 1 h hh).1 e he hsrc

theorem matQ_one (φ : WF p n' ≃+* W) (k : ℕ) : matQ (Qq := Qq) φ (1 : Matrix (Fin k) (Fin k) (WF p n')) = 1 := by
  ext a b
  simp only [matQ, Matrix.one_apply]
  split_ifs <;> simp

theorem mul_matQ_one (φ : WF p n' ≃+* W) {k : ℕ} (h : Matrix (Fin k) (Fin k) Qq) :
    h * ((matQ φ (1 : Matrix (Fin k) (Fin k) (WF p n')))⁻¹).transpose = h := by
  rw [matQ_one]
  simp

theorem isGLW_one (k : ℕ) : IsGLW (1 : Matrix (Fin k) (Fin k) (WF p n')) := by
  simp [IsGLW]

theorem Aa_dual' {K : Type} [Field K] {m : ℕ} (vec : Bool) (M : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hM : IsUnit M.det) : Aa vec ((M⁻¹).transpose) * (Aa vec M).transpose = 1 := by
  cases vec
  · simp [Aa, Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hM, Matrix.mul_nonsing_inv _ hM]
  · simp [Aa, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hM]

theorem lift_Pol (hS : HidaSetting p n' W Qq O Kf ι σ jO w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ) (m : ℕ)
    (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) (hg : IsGLW g)
    (F : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O)) (hF : F ∈ Pol (KK O) (m + 1) (hhDegs TT aT bT)) :
    letI : Algebra (WF p n') O := algOfIdent jO φ
    liftSubst p n' O w 1 (hhLetters TT) g F ∈ Pol (KK O) (m + 1) (hhDegs TT aT bT) := by
  letI : Algebra (WF p n') O := algOfIdent jO φ
  rw [pol_iff hS, lift_eq hS φ hφ 1 (hhLetters TT) (fun x => x.1.val) (fun _ => rfl) g hg F]
  exact Lin_Pol _ _ ((pol_iff hS _ _ _).1 hF)

theorem lift_one (hS : HidaSetting p n' W Qq O Kf ι σ jO w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ) (m : ℕ)
    (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hh : IsUnit h.det)
    (F : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O)) (hF : F ∈ Pol (KK O) (m + 1) (hhDegs TT aT bT)) :
    letI : Algebra (WF p n') O := algOfIdent jO φ
    map (kapR hS) (liftSubst p n' O w 1 (hhLetters TT) (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) F) =
      (algebraMap O Kf w ^ Avec (vecH TT) (hhDegs TT aT bT)) •
        Lin (fun x : TT × Bool => Aa x.2 (la_tw ι σ x.1.val.val h * lb_D (m + 1) 1 (algebraMap O Kf w)))
          (Lin (fun x : TT × Bool => Aa x.2 (la_tw ι σ x.1.val.val h)⁻¹) (map (kapR hS) F)) := by
  letI : Algebra (WF p n') O := algOfIdent jO φ
  have hw := w_ne hS
  set c := algebraMap O Kf w with hc
  have hF' := (pol_iff hS _ _ _).1 hF
  rw [lift_eq hS φ hφ 1 (hhLetters TT) (fun x => x.1.val) (fun _ => rfl) 1 (isGLW_one _) F]
  have hB : Bm ι σ w φ 1 (hhLetters TT).vec (fun x : TT × Bool => x.1.val) (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) =
      fun x => (if (hhLetters TT).vec x then c else 1) •
      (Aa ((hhLetters TT).vec x) (la_tw ι σ x.1.val.val h)⁻¹ *
        Aa ((hhLetters TT).vec x) (Mx ι σ w φ 1 (fun x : TT × Bool => x.1.val) h 1 x)) :=
    funext fun x => Bm_eq hw φ 1 (hhLetters TT).vec (fun x : TT × Bool => x.1.val) h hh 1 (isGLW_one _) x
  rw [hB, Lin_smul _ _ _ hF', Lin_comp]
  have hprod : ∏ x : TT × Bool, (if (hhLetters TT).vec x then c else 1) ^ hhDegs TT aT bT x =
      c ^ Avec (vecH TT) (hhDegs TT aT bT) := by
    unfold Avec
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro x _
    show (if x.2 = true then c else 1) ^ _ = c ^ (if x.2 = true then _ else 0)
    split_ifs <;> simp
  rw [hprod]
  have hfun : (fun x : TT × Bool => Aa ((hhLetters TT).vec x) (la_tw ι σ x.1.val.val h)⁻¹ *
        Aa ((hhLetters TT).vec x) (Mx ι σ w φ 1 (fun x : TT × Bool => x.1.val) h 1 x)) =
      fun x : TT × Bool => Aa x.2 (la_tw ι σ x.1.val.val h)⁻¹ * Aa x.2 (la_tw ι σ x.1.val.val h * lb_D (m + 1) 1 c) := by
    funext x
    unfold Mx
    rw [mul_matQ_one]
    rfl
  rw [hfun]

end

end Formalism.MainNotions.ColumnSystems.Pf.TF
end
end

