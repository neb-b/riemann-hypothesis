module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LValEtaBounds
public import Formalism.HermitianLattices.HermitianLatticesProofs.MassTelescope

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SignedBlockAntidiagWithLeadingMinorsEncardLe
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.SignedBlockCount
open Formalism.MainNotions.S.Loc

variable {K : Type} [Field K]

noncomputable def minor (bs : List (Kˣ × ℕ+)) (l : ℕ) : K :=
  (Matrix.of fun a b : Fin l => ptEntryL bs a b).det

theorem minor_zero (bs : List (Kˣ × ℕ+)) : minor bs 0 = 1 := by simp [minor]

theorem minor_lt (t : Kˣ) (s : ℕ+) (bs : List (Kˣ × ℕ+)) (l : ℕ) (h0 : 0 < l) (hl : l < s) :
    minor ((t, s) :: bs) l = 0 := by
  refine Matrix.det_eq_zero_of_row_eq_zero ⟨0, h0⟩ fun b => ?_
  have hb := b.2
  simp only [Matrix.of_apply, ptEntryL]
  split_ifs <;> first | rfl | omega

theorem minor_add (t : Kˣ) (s : ℕ+) (bs : List (Kˣ × ℕ+)) (l : ℕ) :
    minor ((t, s) :: bs) (s + l) =
      (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤˣ) : ℤ) *
        (t : K) ^ (s : ℕ)) * minor bs l := by
  have key : (Matrix.of fun a b : Fin (s + l) => ptEntryL ((t, s) :: bs) a b).submatrix
      finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks ((Matrix.diagonal (fun _ : Fin s => (t : K))).submatrix id
          (Fin.revPerm : Equiv.Perm (Fin s))) 0 0
        (Matrix.of fun a b : Fin l => ptEntryL bs a b) := by
    ext (a | a) (b | b)
    · have ha := a.2
      have hb := b.2
      simp only [Matrix.submatrix_apply, Matrix.of_apply, ptEntryL, finSumFinEquiv_apply_left,
        Fin.val_castAdd, Matrix.fromBlocks_apply₁₁, id, Matrix.diagonal_apply, Fin.revPerm_apply,
        Fin.ext_iff, Fin.val_rev]
      split_ifs <;> first | rfl | omega
    · simp [ptEntryL]
    · simp [ptEntryL]
    · simp [ptEntryL]
  rw [minor, ← Matrix.det_submatrix_equiv_self finSumFinEquiv, key, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_permute', Matrix.det_diagonal]
  simp [minor]

theorem sign_ne (u : ℤˣ) : ((u : ℤ) : K) ≠ 0 := by
  rcases Int.units_eq_one_or u with e | e <;> simp [e]

theorem minor_self (t : Kˣ) (s : ℕ+) (bs : List (Kˣ × ℕ+)) :
    minor ((t, s) :: bs) s =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤˣ) : ℤ) * (t : K) ^ (s : ℕ) := by
  have := minor_add t s bs 0
  rwa [minor_zero, mul_one, Nat.add_zero] at this

theorem minor_self_ne (t : Kˣ) (s : ℕ+) (bs : List (Kˣ × ℕ+)) : minor ((t, s) :: bs) s ≠ 0 := by
  rw [minor_self]
  exact mul_ne_zero (sign_ne _) (pow_ne_zero _ t.ne_zero)

theorem count_lists (n : ℕ) : ∀ η : ℕ → K, ∃ T : Finset (List (Kˣ × ℕ+)), T.card ≤ 2 ^ n ∧
    ∀ bs : List (Kˣ × ℕ+), (bs.map (fun b => (b.2 : ℕ))).sum = n →
      (∀ l ≤ n, minor bs l = η l) → bs ∈ T := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro η
  by_cases hex : ∃ (t : Kˣ) (s : ℕ+) (bs : List (Kˣ × ℕ+)),
      (s : ℕ) + (bs.map (fun b => (b.2 : ℕ))).sum = n ∧ ∀ l ≤ n, minor ((t, s) :: bs) l = η l
  · obtain ⟨t₀, s, bs₀, hs, h₀⟩ := hex
    have hsp := s.pos
    obtain ⟨T, hT, hT'⟩ := ih (n - s) (by omega) (fun l => η (s + l) / η s)
    let c : K := ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤˣ) : ℤ)
    have hc : c ≠ 0 := sign_ne _
    let R := (Polynomial.nthRoots s (η s / c)).toFinset
    have hR : R.card ≤ s := (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
    refine ⟨Finset.image₂ (fun x bs => ((if h : x = 0 then 1 else Units.mk0 x h), s) :: bs) R T,
      ?_, ?_⟩
    · refine (Finset.card_image₂_le _ _ _).trans ?_
      calc R.card * T.card ≤ 2 ^ (s : ℕ) * 2 ^ (n - s) :=
            Nat.mul_le_mul (hR.trans (Nat.lt_two_pow_self).le) hT
        _ = 2 ^ n := by rw [← pow_add]; congr 1; omega
    · rintro (_ | ⟨⟨t, s'⟩, bs⟩) hsum h
      · simp only [List.map_nil, List.sum_nil] at hsum
        omega
      simp only [List.map_cons, List.sum_cons] at hsum
      have hsp' := s'.pos
      have e : s' = s := by
        apply PNat.eq
        rcases lt_trichotomy (s' : ℕ) s with h1 | h1 | h1
        · exact absurd ((h s' (by omega)).trans ((h₀ s' (by omega)).symm.trans
            (minor_lt _ _ _ _ hsp' h1))) (minor_self_ne _ _ _)
        · exact h1
        · exact absurd ((h₀ s (by omega)).trans ((h s (by omega)).symm.trans
            (minor_lt _ _ _ _ hsp h1))) (minor_self_ne _ _ _)
      subst e
      have h1 := h s' (by omega)
      refine Finset.mem_image₂.2 ⟨t, ?_, bs, hT' bs (by omega) fun l hl => ?_, ?_⟩
      · simp only [R, Multiset.mem_toFinset, Polynomial.mem_nthRoots hsp]
        rw [← h1, minor_self, eq_div_iff hc, mul_comm]
      · rw [← h _ (by omega), ← h1, minor_add, ← minor_self t s' bs,
          mul_div_cancel_left₀ _ (minor_self_ne _ _ _)]
      · simp [t.ne_zero]
  · refine ⟨{[]}, by simpa using Nat.one_le_two_pow, ?_⟩
    rintro (_ | ⟨⟨t, s⟩, bs⟩) hsum h
    · simp
    · exact absurd ⟨t, s, bs, by simpa using hsum, h⟩ hex

end GlobalTheory.SignedBlockCount

namespace GlobalTheory


open Formalism.MainNotions.S.Loc SignedBlockCount in
theorem signed_block_count : ∀ (K : Type) [Field K] (j : ℕ) (δ : ℕ → K), (({P : Matrix (Fin j) (Fin j) K | (∃ (w : Formalism.MainNotions.S.Loc.Pt K j) (sgn : Fin j → ℤˣ), ∀ a b, P a b = w.mat a b * ((sgn b : ℤ) : K)) ∧ ∀ (l : ℕ) (hl : l ≤ j), (P.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = δ l}).encard : ℕ∞) ≤ 8 ^ j := by
  intro K _ j δ
  choose T hT hT' using count_lists (K := K) j
  let η : (Fin j → ℤˣ) → ℕ → K := fun sgn l =>
    if hl : l ≤ j then δ l / ∏ b : Fin l, ((sgn (Fin.castLE hl b) : ℤ) : K) else 0
  let U : Finset (Matrix (Fin j) (Fin j) K) := Finset.univ.biUnion fun sgn : Fin j → ℤˣ =>
    (T (η sgn)).image fun bs => Matrix.of fun a b => ptEntryL bs a b * ((sgn b : ℤ) : K)
  have hU : U.card ≤ 8 ^ j := by
    refine (Finset.card_biUnion_le_card_mul _ _ (2 ^ j)
      fun sgn _ => Finset.card_image_le.trans (hT _)).trans ?_
    simp only [Finset.card_univ, Fintype.card_pi, Fintype.card_units_int, Finset.prod_const,
      Fintype.card_fin]
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by norm_num) _
  refine (Set.encard_le_encard (t := (U : Set _)) ?_).trans ?_
  · rintro P ⟨⟨w, sgn, hP⟩, hδ⟩
    refine Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨sgn, Finset.mem_univ _,
      Finset.mem_image.2 ⟨w.blocks, hT' _ _ w.size fun l hl => ?_, ?_⟩⟩)
    · simp only [η, dif_pos hl]
      rw [eq_div_iff (Finset.prod_ne_zero_iff.2 fun b _ => sign_ne _), ← hδ l hl, mul_comm, minor,
        ← Matrix.det_mul_row]
      congr 1
      ext a b
      simp [hP, Pt.mat, mul_comm]
    · ext a b
      simp [hP, Pt.mat]
  · rw [Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast hU

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularHermitianMassMulLeMass
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.MassRatioBound

lemma core_two (ms m : ℕ → ℝ) (D B Mb : ℝ) (hD : 1 ≤ D) (hB : 1 ≤ B) (hpos : ∀ n, 0 < ms n)
    (hrec : ∀ n, 2 ≤ n → ms (n + 1) = ms n * m (n + 1))
    (hlow : ∀ i, 3 ≤ i → 1 ≤ m i * D * B ^ i)
    (hcmp : ∀ i t, 3 ≤ i → 1 ≤ t → m i ≤ m (i + t) * B ^ t)
    (h2 : ms 2 ≤ Mb) (t : ℕ) (ht : 2 ≤ t) (s : ℕ) (hs : 2 ≤ s) :
    ms s * ms t ≤ ms (s + t) * (Mb * (D * D) * B ^ (s * (s + t))) := by
  have hMb : 0 < Mb := (hpos 2).trans_le h2
  have hB0 : 0 < B := by linarith
  have hD0 : 0 < D := by linarith
  have hm : ∀ n, 2 ≤ n → 0 < m (n + 1) := by
    intro n hn
    have := hpos (n + 1)
    rw [hrec n hn] at this
    exact (mul_pos_iff_of_pos_left (hpos n)).mp this
  induction s, hs using Nat.le_induction with
  | base =>
    have e : 2 + t = t + 1 + 1 := by omega
    have a1 := hlow (t + 1) (by omega)
    have a2 := hlow (t + 1 + 1) (by omega)
    have p1 := hm t ht
    have p2 := hm (t + 1) (by omega)
    have a3 : 1 ≤ (m (t + 1) * D * B ^ (t + 1)) * (m (t + 1 + 1) * D * B ^ (t + 1 + 1)) :=
      one_le_mul_of_one_le_of_one_le a1 a2
    have a4 : B ^ (t + 1) * B ^ (t + 1 + 1) ≤ B ^ (2 * (t + 1 + 1)) := by
      rw [← pow_add]; exact pow_le_pow_right₀ hB (by omega)
    rw [e, hrec (t + 1) (by omega), hrec t ht]
    have pt := hpos t
    calc ms 2 * ms t ≤ Mb * ms t := by gcongr
      _ ≤ Mb * ms t * ((m (t + 1) * D * B ^ (t + 1)) * (m (t + 1 + 1) * D * B ^ (t + 1 + 1))) :=
        le_mul_of_one_le_right (by positivity) a3
      _ = ms t * m (t + 1) * m (t + 1 + 1) * (Mb * (D * D) * (B ^ (t + 1) * B ^ (t + 1 + 1))) := by
        ring
      _ ≤ _ := by gcongr
  | succ s hs ih =>
    have e : s + 1 + t = s + t + 1 := by omega
    have a1 := hcmp (s + 1) t (by omega) (by omega)
    have p1 := hm s hs
    have p2 := hm (s + t) (by omega)
    have p3 := hpos (s + t)
    have a4 : B ^ (s * (s + t)) * B ^ t ≤ B ^ ((s + 1) * (s + t + 1)) := by
      rw [← pow_add]; exact pow_le_pow_right₀ hB (by nlinarith)
    rw [e] at a1
    rw [e, hrec s hs, hrec (s + t) (by omega)]
    calc ms s * m (s + 1) * ms t = (ms s * ms t) * m (s + 1) := by ring
      _ ≤ (ms (s + t) * (Mb * (D * D) * B ^ (s * (s + t)))) * (m (s + t + 1) * B ^ t) := by
        gcongr
      _ = ms (s + t) * m (s + t + 1) * (Mb * (D * D) * (B ^ (s * (s + t)) * B ^ t)) := by ring
      _ ≤ _ := by gcongr

lemma core_one (ms m : ℕ → ℝ) (D B Mb : ℝ) (hD : 1 ≤ D) (hB : 1 ≤ B) (hpos : ∀ n, 0 < ms n)
    (hrec : ∀ n, 2 ≤ n → ms (n + 1) = ms n * m (n + 1))
    (hlow : ∀ i, 3 ≤ i → 1 ≤ m i * D * B ^ i)
    (h1 : ms 1 ≤ Mb) (t : ℕ) (ht : 2 ≤ t) (e : ℕ) (he : t + 1 ≤ e) :
    ms 1 * ms t ≤ ms (t + 1) * (Mb * (D * D) * B ^ e) := by
  have hMb : 0 < Mb := (hpos 1).trans_le h1
  have hB0 : 0 < B := by linarith
  have hD0 : 0 < D := by linarith
  have p1 : 0 < m (t + 1) := by
    have := hpos (t + 1)
    rw [hrec t ht] at this
    exact (mul_pos_iff_of_pos_left (hpos t)).mp this
  have a1 := hlow (t + 1) (by omega)
  have a4 : B ^ (t + 1) ≤ B ^ e := pow_le_pow_right₀ hB he
  have a5 : D ≤ D * D := le_mul_of_one_le_right hD0.le hD
  have pt := hpos t
  rw [hrec t ht]
  calc ms 1 * ms t ≤ Mb * ms t := by gcongr
    _ ≤ Mb * ms t * (m (t + 1) * D * B ^ (t + 1)) := le_mul_of_one_le_right (by positivity) a1
    _ = ms t * m (t + 1) * (Mb * D * B ^ (t + 1)) := by ring
    _ ≤ _ := by gcongr

lemma core (ms m : ℕ → ℝ) (D B Mb : ℝ) (hD : 1 ≤ D) (hB : 1 ≤ B) (hpos : ∀ n, 0 < ms n)
    (hrec : ∀ n, 2 ≤ n → ms (n + 1) = ms n * m (n + 1))
    (hlow : ∀ i, 3 ≤ i → 1 ≤ m i * D * B ^ i)
    (hcmp : ∀ i t, 3 ≤ i → 1 ≤ t → m i ≤ m (i + t) * B ^ t)
    (h1 : ms 1 ≤ Mb) (h2 : ms 2 ≤ Mb) (k s : ℕ) (hk : 3 ≤ k) (hs : 1 ≤ s) (hsk : s < k) :
    ms s * ms (k - s) ≤ ms k * (Mb * (D * D) * B ^ (s * k)) := by
  obtain ⟨t, rfl⟩ : ∃ t, k = s + t := ⟨k - s, by omega⟩
  rw [Nat.add_sub_cancel_left]
  by_cases hs1 : s = 1
  · subst hs1
    rw [add_comm 1 t]
    exact core_one ms m D B Mb hD hB hpos hrec hlow h1 t (by omega) _ (by omega)
  by_cases ht1 : t = 1
  · subst ht1
    rw [mul_comm (ms s)]
    exact core_one ms m D B Mb hD hB hpos hrec hlow h1 s (by omega) _ (by nlinarith)
  exact core_two ms m D B Mb hD hB hpos hrec hlow hcmp h2 t (by omega) s (by omega)

lemma low_base (v : ℝ) (hv : 1 ≤ v) (i : ℕ) (hi : 1 ≤ i) :
    2 ≤ ((Nat.factorial (i - 1) : ℕ) : ℝ) * (v / Real.pi) ^ i * 16 ^ i := by
  have hf : (1 : ℝ) ≤ ((Nat.factorial (i - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hp := Real.pi_pos
  have h4 := Real.pi_le_four
  have h : 2 ≤ v / Real.pi * 16 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hp]; linarith
  have h' : (2 : ℝ) ≤ (v / Real.pi * 16) ^ i :=
    h.trans (le_self_pow₀ (by linarith) (by omega))
  rw [mul_assoc, ← mul_pow]
  nlinarith

lemma cmp_base (v : ℝ) (hv : 1 ≤ v) (i t : ℕ) (ht : 1 ≤ t) :
    ((Nat.factorial (i - 1) : ℕ) : ℝ) * (v / Real.pi) ^ i * 4 ≤
      ((Nat.factorial (i + t - 1) : ℕ) : ℝ) * (v / Real.pi) ^ (i + t) * 16 ^ t := by
  have hf : ((Nat.factorial (i - 1) : ℕ) : ℝ) ≤ ((Nat.factorial (i + t - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hp := Real.pi_pos
  have h4 := Real.pi_le_four
  have h : 4 ≤ v / Real.pi * 16 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hp]; linarith
  have h' : (4 : ℝ) ≤ (v / Real.pi * 16) ^ t :=
    h.trans (le_self_pow₀ (by linarith) (by omega))
  have hv0 : 0 < v := by linarith
  calc _ ≤ ((Nat.factorial (i + t - 1) : ℕ) : ℝ) * (v / Real.pi) ^ i * (v / Real.pi * 16) ^ t := by
        gcongr
    _ = _ := by rw [mul_pow, pow_add]; ring

theorem mass_mul_mass_le : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → ∀ (k s : ℕ) (Mb : ℝ) (ms : ℕ → ℝ), 3 ≤ k → 1 ≤ s → s < k → (∀ (n : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (h : W →ₗ⋆[K] W →ₗ[K] K) (I : Submodule (𝓞 K) W), h.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h I n → Formalism.HermitianLatticesTheory.mass h I = ms n) → ms 1 ≤ Mb → ms 2 ≤ Mb → 1 ≤ Mb → ms s * ms (k - s) ≤ ms k * (Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (Formalism.HermitianLatticesTheory.fDeg K) * 16 ^ (s * k * (Formalism.HermitianLatticesTheory.fDeg K))) := by
  intro hS K _ _ _ hCM hv k s Mb ms hk hs hsk hms h1 h2 _
  have hstd : ∀ n, Formalism.HermitianLatticesTheory.mass (Formalism.HermitianLatticesTheory.massTelescope_form K n)
      (Formalism.HermitianLatticesTheory.massTelescope_lat K n) = ms n := fun n =>
    hms n _ _ _ (Formalism.HermitianLatticesTheory.massTelescope_symm K n) (Formalism.HermitianLatticesTheory.massTelescope_ortho K n)
  have hL := _root_.GlobalTheory.EtaValueBound.lValEta_bounds K hCM
  set v := Formalism.HermitianLatticesTheory.vInv K with hvdef
  set f := Formalism.HermitianLatticesTheory.fDeg K with hfdef
  have hX : (1 : ℝ) ≤ (2 * v) ^ f := one_le_pow₀ (by linarith)
  have hD : 1 ≤ Real.sqrt ((2 * v) ^ f) := Real.one_le_sqrt.mpr hX
  have hDD : Real.sqrt ((2 * v) ^ f) * Real.sqrt ((2 * v) ^ f) = (2 * v) ^ f :=
    Real.mul_self_sqrt (by linarith)
  have hv0 : 0 < v := by linarith
  have hp := Real.pi_pos
  have key := core ms (Formalism.HermitianLatticesTheory.massRatioRightSide K) (Real.sqrt ((2 * v) ^ f)) (16 ^ f) Mb hD
    (one_le_pow₀ (by norm_num))
    (fun n => hstd n ▸ Formalism.HermitianLatticesTheory.massTelescope_std_pos K hCM n)
    (fun n hn => by
      rw [← hstd, ← hstd]; exact Formalism.HermitianLatticesTheory.massTelescope_step K hS hCM n hn)
    ?_ ?_ h1 h2 k s hk hs hsk
  · rw [hDD, ← pow_mul, mul_comm f] at key
    exact key
  · intro i hi
    have a := pow_le_pow_left₀ (by norm_num) (low_base v hv i (by omega)) f
    have b := (hL i (by omega)).1
    unfold Formalism.HermitianLatticesTheory.massRatioRightSide
    rw [← hvdef, ← hfdef]
    set D := Real.sqrt ((2 * v) ^ f)
    have hD0 : 0 < D := by linarith
    set A := ((Nat.factorial (i - 1) : ℕ) : ℝ) * (v / Real.pi) ^ i
    have e : A ^ f / D * Formalism.HermitianLatticesTheory.lValEta K i * D * (16 ^ f) ^ i
        = (A * 16 ^ i) ^ f * Formalism.HermitianLatticesTheory.lValEta K i := by
      rw [mul_pow A, ← pow_mul, ← pow_mul, mul_comm f i]; field_simp
    rw [e]
    calc (1 : ℝ) = 2 ^ f * (2 ^ f)⁻¹ := by field_simp
      _ ≤ _ := by
        refine mul_le_mul a b (by positivity) (le_trans (by positivity) a)
  · intro i t hi ht
    have a := pow_le_pow_left₀ (by positivity) (cmp_base v hv i t ht) f
    have b := (hL i (by omega)).2
    have c := (hL (i + t) (by omega)).1
    unfold Formalism.HermitianLatticesTheory.massRatioRightSide
    rw [← hvdef, ← hfdef]
    set D := Real.sqrt ((2 * v) ^ f)
    have hD0 : 0 < D := by linarith
    have hA : 0 ≤ ((Nat.factorial (i - 1) : ℕ) : ℝ) * (v / Real.pi) ^ i := by positivity
    have hA' : 0 ≤ ((Nat.factorial (i + t - 1) : ℕ) : ℝ) * (v / Real.pi) ^ (i + t) := by positivity
    set A := ((Nat.factorial (i - 1) : ℕ) : ℝ) * (v / Real.pi) ^ i
    set A' := ((Nat.factorial (i + t - 1) : ℕ) : ℝ) * (v / Real.pi) ^ (i + t)
    have e4 : (4 : ℝ) ^ f = 2 ^ f * 2 ^ f := by rw [← mul_pow]; norm_num
    calc A ^ f / D * Formalism.HermitianLatticesTheory.lValEta K i ≤ A ^ f / D * 2 ^ f := by gcongr
      _ = (A * 4) ^ f / D * (2 ^ f)⁻¹ := by rw [mul_pow A, e4]; field_simp
      _ ≤ (A' * 16 ^ t) ^ f / D * Formalism.HermitianLatticesTheory.lValEta K (i + t) := by gcongr
      _ = _ := by rw [mul_pow A', ← pow_mul, ← pow_mul, mul_comm f t]; ring

end GlobalTheory.MassRatioBound
end

