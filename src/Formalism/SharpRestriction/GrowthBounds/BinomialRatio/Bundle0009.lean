module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0008
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegmentChainDegreeEven

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.MapFloorMono
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem ycond_mono' {K : Type*} [CommRing K] {N r : ℕ} [NeZero r] (LL : ChainLetters N) (j : ℕ) {M M' : WithTop ℤ}
    (h : M' ≤ M) : YCond K (r := r) LL j M' ≤ YCond K (r := r) LL j M := by
  unfold YCond
  apply sSup_le_sSup
  rintro S ⟨hS1, hS2⟩
  refine ⟨le_trans hS1 ?_, hS2⟩
  intro x hx
  rw [MvPolynomial.mem_restrictSupport_iff] at hx ⊢
  exact fun m hm => le_trans (hx hm) h

theorem yjt_mono' {K : Type*} [CommRing K] {N r : ℕ} [NeZero r] (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ)
    {M M' : Fin q → WithTop ℤ} (h : ∀ k, M' k ≤ M k) : Yjt K (r := r) LL J M' ≤ Yjt K (r := r) LL J M :=
  inf_le_inf_left _ (iInf_mono fun k => ycond_mono' (K := K) (r := r) LL (J k) (h k))

theorem map_floor_mono (x : WithTop ℤ) {m m' : ℝ} (h : m ≤ m') :
    x.map (fun y : ℤ => ⌊(y : ℝ) - m'⌋) ≤ x.map (fun y : ℤ => ⌊(y : ℝ) - m⌋) := by
  cases x with
  | top => simp
  | coe y =>
    simp only [WithTop.map_coe, WithTop.coe_le_coe]
    exact Int.floor_mono (by linarith)

theorem monoAt : MonoAt := by
  intro O _ _ p r _ s S aTop aPlus b m m' hmm
  unfold BlockData.SSZ
  apply Submodule.span_mono
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨j, jp, hL, hx⟩ := hx
  obtain ⟨y, hy, g0, hg0, rfl⟩ := hx
  exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨jp, Set.mem_iUnion.2 ⟨hL,
    ⟨y, ⟨yjt_mono' _ _ (fun k => map_floor_mono _ hmm) hy.1, hy.2⟩, g0, hg0, rfl⟩⟩⟩⟩

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.NotKept
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem nk_b_up (r y : ℕ) : (sdXi r y : ℝ) ≤ ((y : ℝ) + r) ^ (r - 1) * ((r - 1).factorial : ℝ)⁻¹ := by
  unfold sdXi
  have h := Nat.choose_le_pow_div (α := ℝ) (r - 1) (y + r - 1)
  rw [div_eq_mul_inv] at h
  refine h.trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  have h1 : ((y + r - 1 : ℕ) : ℝ) ≤ ((y + r : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
  exact h1.trans_eq (by push_cast; ring)

theorem nk_b_low (r y : ℕ) (hr : 1 ≤ r) : (y : ℝ) ^ (r - 1) * ((r - 1).factorial : ℝ)⁻¹ ≤ (sdXi r y : ℝ) := by
  unfold sdXi
  have h := Nat.pow_le_choose (α := ℝ) (r - 1) (y + r - 1)
  have e : y + r - 1 + 1 - (r - 1) = y + 1 := by omega
  rw [e, div_eq_mul_inv] at h
  refine le_trans ?_ h
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  push_cast
  linarith

theorem nk_sdXi_le_sd (m y : ℕ) (hm : 1 ≤ m) : sdXi m y ≤ sd m y := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  unfold sdXi sd
  have e1 : y + (n + 1) - 1 = y + n := by omega
  have e2 : n + 1 - 1 = n := by omega
  have e3 : y + (n + 1) = y + n + 1 := by omega
  rw [e1, e2, e3, Nat.choose_succ_succ]
  exact Nat.le_add_right _ _

theorem nk_core {s : ℕ} (r : ℕ) (hr : 1 ≤ r) (L A : ℕ) (R n Ai Ci : Fin s → ℕ) (θ : ℝ) (hθ : 0 ≤ θ)
    (H : ((L : ℝ) + r) * (∏ i, ((R i : ℝ) + r)) * (∏ i, ((n i : ℝ) + r)) ≤
      θ * ((A : ℝ) * (∏ i, (Ai i : ℝ)) * ∏ i, (Ci i : ℝ))) :
    (sdXi r L : ℝ) * (∏ i, (sdXi r (R i) : ℝ)) * (∏ i, (sdXi r (n i) : ℝ)) ≤
      θ ^ (r - 1) * ((sdXi r A : ℝ) * (∏ i, (sdXi r (Ai i) : ℝ)) * ∏ i, (sdXi r (Ci i) : ℝ)) := by
  set f : ℝ := ((r - 1).factorial : ℝ)⁻¹ with hf
  have hf0 : 0 ≤ f := by positivity
  have up : (sdXi r L : ℝ) * (∏ i, (sdXi r (R i) : ℝ)) * (∏ i, (sdXi r (n i) : ℝ)) ≤
      (((L : ℝ) + r) ^ (r - 1) * f) * (∏ i, (((R i : ℝ) + r) ^ (r - 1) * f)) *
        (∏ i, (((n i : ℝ) + r) ^ (r - 1) * f)) := by
    apply mul_le_mul (mul_le_mul (nk_b_up r L)
      (Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => nk_b_up r (R i))) (by positivity) (by positivity))
      (Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => nk_b_up r (n i))) (by positivity) (by positivity)
  have low : (((A : ℝ)) ^ (r - 1) * f) * (∏ i, ((Ai i : ℝ) ^ (r - 1) * f)) * (∏ i, ((Ci i : ℝ) ^ (r - 1) * f)) ≤
      (sdXi r A : ℝ) * (∏ i, (sdXi r (Ai i) : ℝ)) * ∏ i, (sdXi r (Ci i) : ℝ) := by
    apply mul_le_mul (mul_le_mul (nk_b_low r A hr)
      (Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => nk_b_low r (Ai i) hr)) (by positivity) (by positivity))
      (Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => nk_b_low r (Ci i) hr)) (by positivity) (by positivity)
  have e1 : (((L : ℝ) + r) ^ (r - 1) * f) * (∏ i, (((R i : ℝ) + r) ^ (r - 1) * f)) *
        (∏ i, (((n i : ℝ) + r) ^ (r - 1) * f)) =
      (((L : ℝ) + r) * (∏ i, ((R i : ℝ) + r)) * (∏ i, ((n i : ℝ) + r))) ^ (r - 1) *
        (f * (∏ _i : Fin s, f) * ∏ _i : Fin s, f) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow, mul_pow, mul_pow]
    ring
  have e2 : (((A : ℝ)) ^ (r - 1) * f) * (∏ i, ((Ai i : ℝ) ^ (r - 1) * f)) * (∏ i, ((Ci i : ℝ) ^ (r - 1) * f)) =
      ((A : ℝ) * (∏ i, (Ai i : ℝ)) * ∏ i, (Ci i : ℝ)) ^ (r - 1) * (f * (∏ _i : Fin s, f) * ∏ _i : Fin s, f) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow, mul_pow, mul_pow]
    ring
  have hc : 0 ≤ f * (∏ _i : Fin s, f) * ∏ _i : Fin s, f := by positivity
  have hP : 0 ≤ ((L : ℝ) + r) * (∏ i, ((R i : ℝ) + r)) * (∏ i, ((n i : ℝ) + r)) := by positivity
  have hpow := pow_le_pow_left₀ hP H (r - 1)
  rw [mul_pow θ] at hpow
  calc _ ≤ _ := up
    _ = _ := e1
    _ ≤ (θ ^ (r - 1) * ((A : ℝ) * (∏ i, (Ai i : ℝ)) * ∏ i, (Ci i : ℝ)) ^ (r - 1)) *
        (f * (∏ _i : Fin s, f) * ∏ _i : Fin s, f) := mul_le_mul_of_nonneg_right hpow hc
    _ = θ ^ (r - 1) * (((A : ℝ)) ^ (r - 1) * f * (∏ i, ((Ai i : ℝ) ^ (r - 1) * f)) *
        (∏ i, ((Ci i : ℝ) ^ (r - 1) * f))) := by rw [e2]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left low (by positivity)

def WtBoundAt : Prop :=
  ∀ (s r : ℕ) [NeZero r] (A : ℕ) (Ai Ci : Fin s → ℕ) (mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ) (lam : Fin r → ℤ),
    2 * s + 1 ≤ r → IsPair A Ai Ci mu lam →
    wdim lam ≤ (sdXi r (lam 0).toNat : ℚ) * (∏ i : Fin s, (sdXi r (pairRho mu i).toNat : ℚ)) *
      ∏ i : Fin s, (sdXi r (pairN (s := s) lam i).toNat : ℚ)

def BracketAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ),
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ A : ℕ, ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 - X.N1 * X.La C0 / X.k) ≤ (A : ℝ) →
        (A : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) →
        ∀ mu lam, IsPair A (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) mu lam →
          ¬ KeptPair X.p (X.La C0) (r := X.m) (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) mu lam →
          ∃ θ : ℝ, 0 ≤ θ ∧ θ ^ (X.m - 1) ≤ Real.exp (2 - X.La C0 / 5) ∧
            (((lam 0).toNat : ℝ) + X.m) * (∏ i : Fin (segS X.TT j), (((pairRho mu i).toNat : ℝ) + X.m)) *
                (∏ i : Fin (segS X.TT j), (((pairN (s := segS X.TT j) lam i).toNat : ℝ) + X.m)) ≤
              θ * ((A : ℝ) * (∏ i, (clA C0 CE1 CE2 X j rz ry i : ℝ)) * ∏ i, (clC C0 CE1 CE2 X j rz ry i : ℝ))

def RestBracket : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => BracketAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

theorem nk_prod_le_dimMM {s : ℕ} (m : ℕ) (hm : 1 ≤ m) (A : ℕ) (Ai Ci : Fin s → ℕ) :
    (sdXi m A : ℝ) * (∏ i, (sdXi m (Ai i) : ℝ)) * (∏ i, (sdXi m (Ci i) : ℝ)) ≤ (dimMM (m + 1) (A : ℤ) Ai Ci : ℝ) := by
  unfold dimMM
  simp only [tl_symDim_nat]
  push_cast
  rw [Finset.prod_mul_distrib, ← mul_assoc]
  have h : ∀ y : ℕ, (sdXi m y : ℝ) ≤ (sd m y : ℝ) := fun y => by exact_mod_cast nk_sdXi_le_sd m y hm
  apply mul_le_mul (mul_le_mul (h A) (Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => h (Ai i)))
    (by positivity) (by positivity)) (Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => h (Ci i)))
    (by positivity) (by positivity)

theorem notKeptWt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hW : WtBoundAt)
    (hB : BracketAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) : NotKeptWtAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ hD hI hc j rz ry hd A hA1 hA2 mu lam hp hk
  obtain ⟨θ, hθ, hθp, hbr⟩ := hB X hD hI hc j rz ry hd A hA1 hA2 mu lam hp hk
  have hm1 : 1 ≤ X.m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne X.m)
  have hroom : 2 * segS X.TT j + 1 ≤ X.m := by
    obtain ⟨⟨-, -, -, -, h5, -, h7, -⟩, -⟩ := hI
    have := (h5 j).2
    omega
  have h1 := hW (segS X.TT j) X.m A _ _ mu lam hroom hp
  have h1' : ((wdim lam : ℚ) : ℝ) ≤ (sdXi X.m (lam 0).toNat : ℝ) *
      (∏ i : Fin (segS X.TT j), (sdXi X.m (pairRho mu i).toNat : ℝ)) *
      ∏ i : Fin (segS X.TT j), (sdXi X.m (pairN (s := segS X.TT j) lam i).toNat : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr h1
    push_cast at this
    exact this
  have h2 := nk_core X.m hm1 (lam 0).toNat A (fun i => (pairRho mu i).toNat)
    (fun i => (pairN (s := segS X.TT j) lam i).toNat) (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) θ hθ hbr
  have h3 := nk_prod_le_dimMM X.m hm1 A (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry)
  have hT0 : (0 : ℝ) ≤ (sdXi X.m A : ℝ) * (∏ i, (sdXi X.m (clA C0 CE1 CE2 X j rz ry i) : ℝ)) *
      (∏ i, (sdXi X.m (clC C0 CE1 CE2 X j rz ry i) : ℝ)) := by positivity
  have hbig : (1 : ℝ) ≤ (8 * (X.a : ℝ) + X.k) ^ ((2 * X.N1 + 2) ^ 2) := by
    apply one_le_pow₀
    have : (0 : ℝ) ≤ (X.a : ℝ) := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ (X.m : ℝ) := Nat.cast_nonneg _
    unfold Loc.k
    linarith
  have hexp : 0 < Real.exp (2 - X.La C0 / 5) := Real.exp_pos _
  have hdim : (0 : ℝ) ≤ (dimMM (X.m + 1) (A : ℤ) (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) : ℝ) :=
    Nat.cast_nonneg _
  calc ((wdim lam : ℚ) : ℝ) ≤ _ := h1'
    _ ≤ _ := h2
    _ ≤ Real.exp (2 - X.La C0 / 5) * ((sdXi X.m A : ℝ) * (∏ i, (sdXi X.m (clA C0 CE1 CE2 X j rz ry i) : ℝ)) *
        (∏ i, (sdXi X.m (clC C0 CE1 CE2 X j rz ry i) : ℝ))) := mul_le_mul_of_nonneg_right hθp hT0
    _ ≤ Real.exp (2 - X.La C0 / 5) *
        (dimMM (X.m + 1) (A : ℤ) (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) : ℝ) :=
        mul_le_mul_of_nonneg_left h3 hexp.le
    _ ≤ Real.exp (2 - X.La C0 / 5) * (8 * (X.a : ℝ) + X.k) ^ ((2 * X.N1 + 2) ^ 2) *
        (dimMM (X.m + 1) (A : ℤ) (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hdim
        nlinarith [hexp, hbig]

theorem restNotKeptWt_of (hW : WtBoundAt) (hB : RestBracket) : RestNotKeptWt :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => notKeptWt_of hW h) hB

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.RestCountUpOfSTop
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Function

variable {s r : ℕ}

theorem floor_sub_le (x : ℤ) {m : ℝ} (hm : 0 ≤ m) : ⌊(x : ℝ) - m⌋ ≤ x := by
  have h := Int.floor_mono (sub_le_self (x : ℝ) hm)
  rwa [Int.floor_intCast] at h

theorem thr_U [NeZero r] (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) {m : ℝ} (hm : 0 ≤ m) (b : SegBlock s r)
    (ka : Fin (2 * s + 1 + 1) → Fin r → ℤ)
    (hOK : ChainOK (blockData p S aTop aPlus m b).T.J (blockData p S aTop aPlus m b).T.thr ka) (i : Fin s)
    (hi : S.sigma ≤ i.val) : ka ⟨2 * i.val + 1, by omega⟩ 0 ≤ cap p S b i.val := by
  have hit : i.val - S.sigma < S.t := by unfold SegData.t; have := i.2; omega
  obtain ⟨k, hk⟩ : ∃ k : Fin (blockData p S aTop aPlus m b).T.q, k.val = i.val - S.sigma :=
    ⟨⟨i.val - S.sigma, by show i.val - S.sigma < S.t + 1; omega⟩, rfl⟩
  have hkt : k.val < S.t := by omega
  have h := hOK k
  have e1 : finPos (2 * s + 1) ((blockData p S aTop aPlus m b).T.J k) = ⟨2 * i.val + 1, by omega⟩ := by
    apply Fin.ext
    show min (if h : k.val < S.t then 2 * (uTop S ⟨k.val, h⟩ : ℕ) + 1 else 2 * s + 1) (2 * s + 1) = 2 * i.val + 1
    rw [dite_eq_left hkt]
    show min (2 * (S.sigma + k.val) + 1) (2 * s + 1) = 2 * i.val + 1
    omega
  have e3 : (blockData p S aTop aPlus m b).T.thr k = ((⌊((cap p S b i.val : ℤ) : ℝ) - m⌋ : ℤ) : WithTop ℤ) := by
    show WithTop.map (fun x : ℤ => ⌊(x : ℝ) - m⌋) (if h : k.val < S.t then ((cap p S b (uTop S ⟨k.val, h⟩) : ℤ) : WithTop ℤ)
      else ((cap p S b s : ℤ) : WithTop ℤ)) = _
    rw [dite_eq_left hkt, WithTop.map_coe]
    have hu : ((uTop S ⟨k.val, hkt⟩ : Fin s) : ℕ) = i.val := by
      show S.sigma + k.val = i.val
      omega
    rw [hu]
  rw [e1, e3] at h
  exact (WithTop.coe_le_coe.mp h).trans (floor_sub_le _ hm)

theorem thr_last [NeZero r] (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) {m : ℝ} (hm : 0 ≤ m)
    (b : SegBlock s r) (ka : Fin (2 * s + 1 + 1) → Fin r → ℤ)
    (hOK : ChainOK (blockData p S aTop aPlus m b).T.J (blockData p S aTop aPlus m b).T.thr ka) :
    ka (Fin.last _) 0 ≤ cap p S b s := by
  obtain ⟨k, hk⟩ : ∃ k : Fin (blockData p S aTop aPlus m b).T.q, k.val = S.t :=
    ⟨⟨S.t, by show S.t < S.t + 1; omega⟩, rfl⟩
  have hkt : ¬ (k.val < S.t) := by omega
  have h := hOK k
  have e1 : finPos (2 * s + 1) ((blockData p S aTop aPlus m b).T.J k) = Fin.last _ := by
    apply Fin.ext
    show min (if h : k.val < S.t then 2 * (uTop S ⟨k.val, h⟩ : ℕ) + 1 else 2 * s + 1) (2 * s + 1) = 2 * s + 1
    rw [dite_eq_right hkt]
    exact min_self _
  have e3 : (blockData p S aTop aPlus m b).T.thr k = ((⌊((cap p S b s : ℤ) : ℝ) - m⌋ : ℤ) : WithTop ℤ) := by
    show WithTop.map (fun x : ℤ => ⌊(x : ℝ) - m⌋) (if h : k.val < S.t then ((cap p S b (uTop S ⟨k.val, h⟩) : ℤ) : WithTop ℤ)
      else ((cap p S b s : ℤ) : WithTop ℤ)) = _
    rw [dite_eq_right hkt, WithTop.map_coe]
  rw [e1, e3] at h
  exact (WithTop.coe_le_coe.mp h).trans (floor_sub_le _ hm)

def STopRowsAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (m : ℝ), 0 ≤ m →
    ∀ rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ,
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ z, SrcOK C0 CE1 CE2 X j m rz ry z →
        ∀ i : Fin (segS X.TT j), i.val < (X.seg C0 CE1 CE2 j).sigma →
          z.2.2 ⟨2 * i.val + 1, by omega⟩ 0 ≤ cap X.p (X.seg C0 CE1 CE2 j) z.1 i.val ∧
          z.2.2 ⟨2 * i.val + 1, by omega⟩ 0 ≤ cap X.p (X.seg C0 CE1 CE2 j) z.1 (i.val + 1)

theorem firstRows_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hS : STopRowsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    FirstRowsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  unfold FirstRowsAt
  intro X _ hD hI hc j m hm rz ry hdig z hz
  have hS' := hS X hD hI hc j m hm rz ry hdig z hz
  obtain ⟨b, ⟨jl, jp⟩, ka⟩ := z
  obtain ⟨⟨hK, -, -⟩, -, -, hok⟩ := hz
  dsimp only at hS' hK hok ⊢
  refine ⟨fun i c hc0 => ?_, fun c hc0 => ?_⟩
  · have c0 : c = 0 := Fin.ext (by simp [hc0])
    subst c0
    by_cases hi : i.val < (X.seg C0 CE1 CE2 j).sigma
    · exact hS' i hi
    · have h1 := thr_U X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) hm b ka hok i
        (by omega)
      refine ⟨h1, ?_⟩
      rw [cap_succ]
      have h2 := (hK.2.1 i (by omega)).1
      have h3 : oEff (X.seg C0 CE1 CE2 j) b i = b.o i := by
        unfold oEff
        rw [if_neg hi]
      omega
  · have c0 : c = 0 := Fin.ext (by simp [hc0])
    subst c0
    exact thr_last X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) hm b ka hok

def RestSTopRows : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => STopRowsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

theorem restFirstRows_of (h : RestSTopRows) : RestFirstRows := by
  unfold RestSTopRows TransportedAlt at h
  unfold RestFirstRows TransportedAlt
  intro Cc hCc
  obtain ⟨U0, hU0, h0⟩ := h Cc hCc
  refine ⟨U0, hU0, fun C0 hC0 => ?_⟩
  obtain ⟨U1, hU1, h1⟩ := h0 C0 hC0
  refine ⟨U1, hU1, fun CE1 CE2 Cm a1 a2 a3 => ?_⟩
  obtain ⟨U2, hU2, h2⟩ := h1 CE1 CE2 Cm a1 a2 a3
  exact ⟨U2, hU2, fun CYb Cde Ck CD Cb b1 b2 b3 b4 b5 => firstRows_of (h2 CYb Cde Ck CD Cb b1 b2 b3 b4 b5)⟩

theorem restCountUp_of_STop (hCD : ChainDimAt) (hNB : NumBranchAt) (h : RestSTopRows) : RestCountUp := restCountUp_of_rows hCD hNB (restFirstRows_of h)

end Formalism.MainNotions.ColumnSystems.Pf
end
end

