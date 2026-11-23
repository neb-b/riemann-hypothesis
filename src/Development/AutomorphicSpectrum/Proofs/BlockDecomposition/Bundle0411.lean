module

public import Mathlib
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0399
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0394
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapTop
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0204

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameStabilizerFlagCriterion
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.CFin.Tri

theorem cnt_le {r : ℕ} (S : Finset (Fin r)) (i : Fin r) : cnt S i ≤ S.card := by
  unfold cnt
  exact_mod_cast Finset.card_filter_le _ _

theorem exists_least {r : ℕ} {S : Finset (Fin r)} {i : Fin r} (h : cnt S i < S.card) :
    ∃ j ∈ S, i ≤ j ∧ ∀ j' ∈ S, i ≤ j' → j ≤ j' := by
  have hne : (S.filter (i ≤ ·)).Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hn
    have : S.filter (· < i) = S := Finset.filter_true_of_mem fun x hx => not_le.mp (hn hx)
    simp [cnt, this] at h
  refine ⟨(S.filter (i ≤ ·)).min' hne, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).1
  · exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
  · intro j' hj' hij'
    exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hj', hij'⟩)

theorem exists_between {r : ℕ} {S : Finset (Fin r)} {i k : Fin r} (h : cnt S i < cnt S k) :
    ∃ t ∈ S, i ≤ t ∧ t < k := by
  by_contra hn
  push_neg at hn
  have hsub : S.filter (· < k) ⊆ S.filter (· < i) := by
    intro t ht
    obtain ⟨htS, htk⟩ := Finset.mem_filter.mp ht
    refine Finset.mem_filter.mpr ⟨htS, ?_⟩
    by_contra hti
    exact absurd htk (not_lt.mpr (hn t htS (not_lt.mp hti)))
  have := Finset.card_le_card hsub
  unfold cnt at h
  omega

theorem inv_neg_tri {ι : Type} [Fintype ι] [DecidableEq ι] {L : Type} [Field L] (lv : ι → ℤ)
    {M M' : Matrix ι ι L} (h : M * M' = 1)
    (hM : ∀ u v, lv v < lv u → lv v < 0 → M u v = 0) :
    ∀ u v, lv v < lv u → lv v < 0 → M' u v = 0 := by
  intro u v huv hv
  letI : Invertible M := ⟨M', mul_eq_one_comm.mp h, h⟩
  have hinv : M⁻¹ = M' := Matrix.inv_eq_right_inv h
  have hb : M.BlockTriangular (fun w => if lv w ≤ lv v then (0 : ℤ) else 1) := by
    intro a b hab
    by_cases hb' : lv b ≤ lv v
    · by_cases ha' : lv a ≤ lv v
      · simp [hb', ha'] at hab
      · exact hM a b (by omega) (by omega)
    · by_cases ha' : lv a ≤ lv v <;> simp [hb', ha'] at hab
  have := Matrix.blockTriangular_inv_of_blockTriangular hb
  rw [hinv] at this
  apply this
  have h1 : ¬ lv u ≤ lv v := by omega
  simp [h1]

theorem col_zero {L : Type} [Field L] {n r m : ℕ} (X Y : Matrix (Fin n) (Fin r) L)
    (Z : Matrix (Fin n) (Fin m) L) (Qi : Matrix (Idx r m) (Fin n) L)
    (hQ : Qi * frm X Z Y = 1) (S : Finset (Fin r)) (g : Matrix (Fin n) (Fin n) L)
    (hst : ∀ j ∈ S, StabUpTo X g j) (u v : Idx r m)
    (huv : lev m S v < lev m S u) (hv : lev m S v < 0) : (Qi * g * frm X Z Y) u v = 0 := by
  rcases v with i | k | i
  · have hi : cnt S i < S.card := by simpa [lev] using hv
    obtain ⟨j, hjS, hij, hmin⟩ := exists_least hi
    obtain ⟨b, hb, hbz⟩ := hst j hjS i hij
    have hc : X *ᵥ b = frm X Z Y *ᵥ (Sum.elim b (fun _ => 0)) := by
      ext a
      simp [frm, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    have hcol : (fun w => (Qi * g * frm X Z Y) w (Sum.inl i)) = Sum.elim b (fun _ => 0) := by
      have e1 : (fun w => (Qi * g * frm X Z Y) w (Sum.inl i))
          = Qi *ᵥ (g *ᵥ (fun a => X a i)) := by
        ext w
        rw [Matrix.mul_assoc]
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, frm]
      rw [e1, hb, hc, Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec]
    have hval : (Qi * g * frm X Z Y) u (Sum.inl i) = Sum.elim b (fun _ => 0) u := congrFun hcol u
    rw [hval]
    rcases u with k | w
    · simp only [Sum.elim_inl]
      have hc' : cnt S i < cnt S k := by simpa [lev] using huv
      obtain ⟨t, htS, hit, htk⟩ := exists_between hc'
      exact hbz k (lt_of_le_of_lt (hmin t htS hit) htk)
    · simp
  · simp [lev] at hv
  · have := cnt_le S i
    simp only [lev] at hv
    omega

theorem cT_mul' {L : Type} [Field L] (s : L →+* L) {a b c : Type} [Fintype b]
    (A : Matrix a b L) (B : Matrix b c L) : cT s (A * B) = cT s B * cT s A := by
  simp [cT, Matrix.transpose_mul, Matrix.map_mul]

theorem cT_one' {L : Type} [Field L] (s : L →+* L) {a : Type} [DecidableEq a] :
    cT s (1 : Matrix a a L) = 1 := by
  simp [cT]

theorem block_tri (L : Type) [Field L] (s : L →+* L) (n r m : ℕ)
    (J : Matrix (Fin n) (Fin n) L) (X Y : Matrix (Fin n) (Fin r) L)
    (Z : Matrix (Fin n) (Fin m) L) (Qi : Matrix (Idx r m) (Fin n) L)
    (hXX : cT s X * J * X = 0) (hXY : cT s X * J * Y = 1) (hXZ : cT s X * J * Z = 0)
    (hQ : Qi * frm X Z Y = 1) (hQ' : frm X Z Y * Qi = 1) (S : Finset (Fin r))
    (g : Matrix (Fin n) (Fin n) L) (hg : IsUnit g) (hJ : cT s g * J * g = J)
    (hst : ∀ j ∈ S, StabUpTo X g j) :
    (Qi * g * frm X Z Y).BlockTriangular (lev m S) := by
  obtain ⟨gi, h1⟩ := hg.exists_right_inv
  have hrow0 : cT s X * J * frm X Z Y = Matrix.fromCols (0 : Matrix (Fin r) (Fin r) L)
        (Matrix.fromCols (0 : Matrix (Fin r) (Fin m) L) (1 : Matrix (Fin r) (Fin r) L)) := by
    rw [frm, Matrix.mul_fromCols, Matrix.mul_fromCols, hXX, hXZ, hXY]
  set Q := frm X Z Y with hQdef
  set M := Qi * g * Q with hMdef
  set M' := Qi * gi * Q with hM'def
  have hMM' : M * M' = 1 := by
    calc M * M' = Qi * g * (Q * Qi) * gi * Q := by simp only [hMdef, hM'def, Matrix.mul_assoc]
      _ = Qi * (g * gi) * Q := by rw [hQ']; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, hQ]
  have A1 : ∀ u v, lev m S v < lev m S u → lev m S v < 0 → M u v = 0 :=
    fun u v huv hv => col_zero X Y Z Qi hQ S g hst u v huv hv
  have A2 := inv_neg_tri (lev m S) hMM' A1
  set H := cT s Q * J * Q with hHdef
  have hgJ : cT s gi * J = J * g := by
    have e : cT s gi * cT s g = 1 := by
      rw [← cT_mul', h1, cT_one']
    calc cT s gi * J = cT s gi * (cT s g * J * g) := by rw [hJ]
      _ = (cT s gi * cT s g) * J * g := by simp only [Matrix.mul_assoc]
      _ = J * g := by rw [e, Matrix.one_mul]
  have hHM : H * M = cT s M' * H := by
    have e : cT s Qi * cT s Q = 1 := by rw [← cT_mul', hQ', cT_one']
    calc H * M = cT s Q * J * (Q * Qi) * g * Q := by simp only [hHdef, hMdef, Matrix.mul_assoc]
      _ = cT s Q * (J * g) * Q := by rw [hQ']; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = cT s Q * (cT s gi * J) * Q := by rw [hgJ]
      _ = cT s Q * cT s gi * (cT s Qi * cT s Q) * J * Q := by rw [e]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = cT s M' * H := by simp only [hM'def, hHdef, cT_mul', Matrix.mul_assoc]
  have hrow : ∀ l w, H (Sum.inl l) w = (Matrix.fromCols (0 : Matrix (Fin r) (Fin r) L)
      (Matrix.fromCols (0 : Matrix (Fin r) (Fin m) L) (1 : Matrix (Fin r) (Fin r) L))) l w := by
    intro l w
    rw [← hrow0]
    simp only [hHdef, hQdef, Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, frm,
      Matrix.fromCols_apply_inl]
  have lx : ∀ i, lev m S (Sum.inl i) = cnt S i - S.card := fun _ => rfl
  have lz : ∀ k, lev m S (Sum.inr (Sum.inl k)) = 0 := fun _ => rfl
  have ly : ∀ i, lev m S (Sum.inr (Sum.inr i)) = S.card - cnt S i := fun _ => rfl
  intro u v huv
  by_cases hv : lev m S v < 0
  · exact A1 u v huv hv
  push_neg at hv
  rcases u with i | k | l
  · have := cnt_le S i
    rw [lx] at huv
    omega
  · rw [lz] at huv
    omega
  have hl0 : lev m S (Sum.inl l) < 0 := by
    have := cnt_le S l
    rw [ly] at huv; rw [lx]; omega
  have hlv : lev m S v < - lev m S (Sum.inl l) := by rw [ly] at huv; rw [lx]; omega
  have e1 : M (Sum.inr (Sum.inr l)) v = (H * M) (Sum.inl l) v := by
    simp [Matrix.mul_apply, Fintype.sum_sum_type, hrow, Matrix.one_apply]
  rw [e1, hHM, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun w _ => ?_
  by_cases hw : lev m S (Sum.inl l) < lev m S w
  · have : M' w (Sum.inl l) = 0 := A2 w _ hw hl0
    simp [cT, this]
  push_neg at hw
  rcases w with l' | k | l'
  · rcases v with a | b | c
    · simp [hrow]
    · simp [hrow]
    · by_cases hc : l' = c
      · subst hc
        have := cnt_le S l'
        simp only [lx, ly] at hw hlv
        omega
      · simp [hrow, Matrix.one_apply, hc]
  · rw [lz] at hw
    omega
  · have := cnt_le S l'
    rw [ly] at hw
    omega

theorem witt_blockTriangular : ∀ (L : Type) [Field L] (s : L →+* L), (∀ x, s (s x) = x) → ∀ (n r m : ℕ) (J : Matrix (Fin n) (Fin n) L) (X Y : Matrix (Fin n) (Fin r) L) (Z : Matrix (Fin n) (Fin m) L) (Qi : Matrix (Idx r m) (Fin n) L), cT s J = J → cT s X * J * X = 0 → cT s Y * J * Y = 0 → cT s X * J * Y = 1 → cT s X * J * Z = 0 → cT s Y * J * Z = 0 → Qi * frm X Z Y = 1 → frm X Z Y * Qi = 1 → ∀ (S : Finset (Fin r)) (g : Matrix (Fin n) (Fin n) L), IsUnit g → cT s g * J * g = J → (∀ j ∈ S, StabUpTo X g j) → (Qi * g * frm X Z Y).BlockTriangular (lev m S) := by
  intro L _ s _ n r m J X Y Z Qi _ hXX _ hXY hXZ _ hQ hQ' S g hg hJ hst
  exact block_tri L s n r m J X Y Z Qi hXX hXY hXZ hQ hQ' S g hg hJ hst

end GlobalTheory.CompanionTheory.CFin.Tri
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianSplitRankOne
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

namespace GlobalTheory.CompanionTheory.KFin

section SwapHerm

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {c : R →+* R} {h : V → V → R}

theorem swapHerm_zero_right (hH : IsHerm c h) (x : V) : h x 0 = 0 := by
  have := hH.smul_right 0 x 0
  simpa using this

theorem swapHerm_add_left (hH : IsHerm c h) (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [hH.symm z (x + y), hH.add_right, map_add (f := _), ← hH.symm z x, ← hH.symm z y]

theorem swapHerm_smul_left (hH : IsHerm c h) (a : R) (x y : V) : h (a • x) y = c a * h x y := by
  rw [hH.symm y (a • x), hH.smul_right, map_mul, ← hH.symm y x]

theorem swapHerm_sub_right (hH : IsHerm c h) (x y z : V) : h x (y - z) = h x y - h x z := by
  have := hH.add_right x (y - z) z
  rw [sub_add_cancel] at this
  exact eq_sub_of_add_eq this.symm

theorem swapHerm_part {e e' : R} (hce : c e = e') (hH : IsHerm c h) {a : V} (ha : e • a = a) (z : V) :
    h a z = e' * h a z := by
  calc h a z = h (e • a) z := by rw [ha]
    _ = e' * h a z := by rw [swapHerm_smul_left hH, hce]

theorem swapHerm_self {e e' : R} (hee : e * e' = 0) (hce : c e = e') (hH : IsHerm c h) {a : V}
    (ha : e • a = a) : h a a = 0 := by
  have h1 : h a a = e * h a a := by
    calc h a a = h a (e • a) := by rw [ha]
      _ = e * h a a := hH.smul_right e a a
  have h2 := swapHerm_part hce hH ha a
  rw [h1, h2, ← mul_assoc, hee, zero_mul]

theorem swapHerm_exists_ne (hP : IsPerfect h) {a : V} (ha : a ≠ 0) : ∃ y, h a y ≠ 0 := by
  by_contra hne
  push_neg at hne
  exact ha (hP.nondeg a hne)

theorem swapHerm_pair_ne {e e' : R} (hee : e * e' = 0) (hce : c e = e') (hce' : c e' = e)
    (hu : ∀ u, e * u ≠ 0 → e' * u ≠ 0 → IsUnit u) (hH : IsHerm c h) (hP : IsPerfect h)
    (hno : ∀ x y, h x x = 0 → h x y ≠ 1) {a b : V} (ha : e • a = a) (hb : e' • b = b)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) : h a b ≠ 0 := by
  intro hab
  have hee' : e' * e = 0 := by rw [mul_comm]; exact hee
  have haa : h a a = 0 := swapHerm_self hee hce hH ha
  have hbb : h b b = 0 := swapHerm_self hee' hce' hH hb
  have hba : h b a = 0 := by rw [hH.symm a b, hab, map_zero]
  have hxx : h (a + b) (a + b) = 0 := by
    rw [swapHerm_add_left hH, hH.add_right, hH.add_right, haa, hab, hba, hbb]; ring
  obtain ⟨y1, hy1⟩ := swapHerm_exists_ne hP ha0
  obtain ⟨y2, hy2⟩ := swapHerm_exists_ne hP hb0
  have hex : ∃ y, h a y ≠ 0 ∧ h b y ≠ 0 := by
    by_cases h1 : h b y1 = 0
    · by_cases h2 : h a y2 = 0
      · refine ⟨y1 + y2, ?_, ?_⟩
        · rw [hH.add_right, h2, add_zero]; exact hy1
        · rw [hH.add_right, h1, zero_add]; exact hy2
      · exact ⟨y2, h2, hy2⟩
    · exact ⟨y1, hy1, h1⟩
  obtain ⟨y, hya, hyb⟩ := hex
  have hpa : h a y = e' * h a y := swapHerm_part hce hH ha y
  have hpb : h b y = e * h b y := swapHerm_part hce' hH hb y
  have hunit : IsUnit (h (a + b) y) := by
    apply hu
    · rw [swapHerm_add_left hH, mul_add, hpa, ← mul_assoc, hee, zero_mul, zero_add, ← hpb]; exact hyb
    · rw [swapHerm_add_left hH, mul_add, hpb, ← mul_assoc, hee', zero_mul, add_zero, ← hpa]; exact hya
  obtain ⟨U, hU⟩ := hunit
  apply hno (a + b) ((↑U⁻¹ : R) • y) hxx
  rw [hH.smul_right, ← hU, Units.inv_mul]

theorem swapHerm_partner {e e' : R} (he : e + e' = 1) (hee : e * e' = 0) (hce : c e = e')
    (hH : IsHerm c h) (hP : IsPerfect h) {a : V} (ha : e • a = a) (ha0 : a ≠ 0) :
    ∃ b : V, e' • b = b ∧ b ≠ 0 := by
  obtain ⟨y, hy⟩ := swapHerm_exists_ne hP ha0
  have hidem : e' * e' = e' := by
    have h0 : e' * e = 0 := by rw [mul_comm]; exact hee
    calc e' * e' = e' * (e + e') - e' * e := by ring
      _ = e' := by rw [he, h0, mul_one, sub_zero]
  refine ⟨e' • y, by rw [← mul_smul, hidem], fun h0 => hy ?_⟩
  have h1 : h a (e' • y) = h a y := by rw [hH.smul_right, ← swapHerm_part hce hH ha y]
  rw [← h1, h0, swapHerm_zero_right hH]

theorem swapHerm_coord {e e' : R} (he : e + e' = 1) (hee : e * e' = 0) (hce : c e = e') (hce' : c e' = e)
    (hu : ∀ u, e * u ≠ 0 → e' * u ≠ 0 → IsUnit u) (hH : IsHerm c h) (hP : IsPerfect h)
    (hno : ∀ x y, h x x = 0 → h x y ≠ 1) {a b : V} (ha : e • a = a) (hb : e' • b = b)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) {z : V} (hz : e' • z = z) : ∃ ρ : R, z = ρ • b := by
  have hβ := swapHerm_pair_ne hee hce hce' hu hH hP hno ha hb ha0 hb0
  have hee' : e' * e = 0 := by rw [mul_comm]; exact hee
  have hidem : e * e = e := by
    calc e * e = e * (e + e') - e * e' := by ring
      _ = e := by rw [he, hee, mul_one, sub_zero]
  have he0 : e ≠ 0 := by
    intro h0; apply ha0; rw [← ha, h0, zero_smul]
  have hpβ : h a b = e' * h a b := swapHerm_part hce hH ha b
  have hpγ : h a z = e' * h a z := swapHerm_part hce hH ha z
  have hunit : IsUnit (e + h a b) := by
    apply hu
    · rw [mul_add, hidem, hpβ, ← mul_assoc, hee, zero_mul, add_zero]; exact he0
    · rw [mul_add, hee', zero_add, ← hpβ]; exact hβ
  obtain ⟨U, hU⟩ := hunit
  have hβU : h a b = e' * ↑U := by rw [hU, mul_add, hee', zero_add, ← hpβ]
  refine ⟨h a z * ↑U⁻¹, ?_⟩
  by_contra hne
  have hw : e' • (z - (h a z * ↑U⁻¹) • b) = z - (h a z * ↑U⁻¹) • b := by
    rw [smul_sub, hz, smul_comm, hb]
  have hw0 : z - (h a z * ↑U⁻¹) • b ≠ 0 := sub_ne_zero.mpr hne
  apply swapHerm_pair_ne hee hce hce' hu hH hP hno ha hw ha0 hw0
  rw [swapHerm_sub_right hH, hH.smul_right, hβU,
    show h a z * ↑U⁻¹ * (e' * ↑U) = h a z * e' * (↑U⁻¹ * ↑U) by ring, Units.inv_mul, mul_one,
    mul_comm, ← hpγ, sub_self]

theorem swapHerm_gen {e e' : R} (he : e + e' = 1) (hee : e * e' = 0) (hce : c e = e') (hce' : c e' = e)
    (hu : ∀ u, e * u ≠ 0 → e' * u ≠ 0 → IsUnit u) (hH : IsHerm c h) (hP : IsPerfect h)
    (hno : ∀ x y, h x x = 0 → h x y ≠ 1) {a b : V} (ha : e • a = a) (hb : e' • b = b)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    (∀ x, ∃ r : R, x = r • (a + b)) ∧ IsUnit (h (a + b) (a + b)) := by
  have hee' : e' * e = 0 := by rw [mul_comm]; exact hee
  have he' : e' + e = 1 := by rw [add_comm]; exact he
  have hidem : e * e = e := by
    calc e * e = e * (e + e') - e * e' := by ring
      _ = e := by rw [he, hee, mul_one, sub_zero]
  have hidem' : e' * e' = e' := by
    calc e' * e' = e' * (e + e') - e' * e := by ring
      _ = e' := by rw [he, hee', mul_one, sub_zero]
  have he'a : e' • a = 0 := by rw [← ha, ← mul_smul, hee', zero_smul]
  have heb : e • b = 0 := by rw [← hb, ← mul_smul, hee, zero_smul]
  refine ⟨fun x => ?_, ?_⟩
  · obtain ⟨ρ', hρ'⟩ := swapHerm_coord he hee hce hce' hu hH hP hno ha hb ha0 hb0 (z := e' • x)
      (by rw [← mul_smul, hidem'])
    obtain ⟨ρ, hρ⟩ := swapHerm_coord he' hee' hce' hce (fun u h1 h2 => hu u h2 h1) hH hP hno hb ha hb0 ha0
      (z := e • x) (by rw [← mul_smul, hidem])
    refine ⟨ρ * e + ρ' * e', ?_⟩
    rw [smul_add, add_smul, add_smul, mul_smul, mul_smul, mul_smul, mul_smul, ha, hb, he'a, heb,
      smul_zero, smul_zero, add_zero, zero_add, ← hρ, ← hρ', ← add_smul, he, one_smul]
  · have hβ := swapHerm_pair_ne hee hce hce' hu hH hP hno ha hb ha0 hb0
    have haa : h a a = 0 := swapHerm_self hee hce hH ha
    have hbb : h b b = 0 := swapHerm_self hee' hce' hH hb
    have hpβ : h a b = e' * h a b := swapHerm_part hce hH ha b
    have hpβ' : h b a = e * h b a := swapHerm_part hce' hH hb a
    have hβ' : h b a ≠ 0 := by
      intro h0; apply hβ; rw [hH.symm b a, h0, map_zero]
    rw [swapHerm_add_left hH, hH.add_right, hH.add_right, haa, hbb, zero_add, add_zero]
    apply hu
    · rw [mul_add, hpβ, ← mul_assoc, hee, zero_mul, zero_add, ← hpβ']; exact hβ'
    · rw [mul_add, hpβ', ← mul_assoc, hee', zero_mul, add_zero, ← hpβ]; exact hβ

end SwapHerm

theorem hermitian_split_rank_one_struct {k R V : Type} [Field k] [CommRing R] [AddCommGroup V] [Module R V]
    (φ : R ≃+* k × k) (c : R →+* R) (hc : ∀ r, φ (c r) = (φ r).swap) (h : V → V → R)
    (hH : IsHerm c h) (hP : IsPerfect h) (hno : ∀ x y, h x x = 0 → h x y ≠ 1) :
    Subsingleton V ∨ ∃ w₀ : V, (∀ x, ∃ r : R, x = r • w₀) ∧ IsUnit (h w₀ w₀) := by
  obtain ⟨e, he_def⟩ : ∃ e : R, e = φ.symm (1, 0) := ⟨_, rfl⟩
  obtain ⟨e', he'_def⟩ : ∃ e' : R, e' = φ.symm (0, 1) := ⟨_, rfl⟩
  have hφe : φ e = (1, 0) := by rw [he_def]; simp
  have hφe' : φ e' = (0, 1) := by rw [he'_def]; simp
  have he : e + e' = 1 := φ.injective (by rw [map_add (f := _), hφe, hφe', map_one]; ext <;> simp)
  have hee : e * e' = 0 := φ.injective (by rw [map_mul, hφe, hφe', map_zero]; ext <;> simp)
  have hce : c e = e' := φ.injective (by rw [hc, hφe, hφe']; rfl)
  have hce' : c e' = e := φ.injective (by rw [hc, hφe, hφe']; rfl)
  have hu : ∀ u : R, e * u ≠ 0 → e' * u ≠ 0 → IsUnit u := by
    intro u h1 h2
    have h1' : (φ u).1 ≠ 0 := by
      intro h0; apply h1; apply φ.injective
      rw [map_mul, hφe, map_zero]; ext <;> simp [h0]
    have h2' : (φ u).2 ≠ 0 := by
      intro h0; apply h2; apply φ.injective
      rw [map_mul, hφe', map_zero]; ext <;> simp [h0]
    rw [← isUnit_map_iff φ, Prod.isUnit_iff]
    exact ⟨isUnit_iff_ne_zero.mpr h1', isUnit_iff_ne_zero.mpr h2'⟩
  have hee' : e' * e = 0 := by rw [mul_comm]; exact hee
  have he' : e' + e = 1 := by rw [add_comm]; exact he
  have hidem : e * e = e := by
    calc e * e = e * (e + e') - e * e' := by ring
      _ = e := by rw [he, hee, mul_one, sub_zero]
  have hidem' : e' * e' = e' := by
    calc e' * e' = e' * (e + e') - e' * e := by ring
      _ = e' := by rw [he, hee', mul_one, sub_zero]
  rcases subsingleton_or_nontrivial V with hs | hs
  · exact Or.inl hs
  right
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hv' : v = e • v + e' • v := by rw [← add_smul, he, one_smul]
  by_cases hev : e • v = 0
  · have hb0 : e' • v ≠ 0 := by intro h0; apply hv; rw [hv', hev, h0, add_zero]
    have hb : e' • (e' • v) = e' • v := by rw [← mul_smul, hidem']
    obtain ⟨a, ha, ha0⟩ := swapHerm_partner he' hee' hce' hH hP hb hb0
    exact ⟨_, swapHerm_gen he hee hce hce' hu hH hP hno ha hb ha0 hb0⟩
  · have ha : e • (e • v) = e • v := by rw [← mul_smul, hidem]
    obtain ⟨b, hb, hb0⟩ := swapHerm_partner he hee hce hH hP ha hev
    exact ⟨_, swapHerm_gen he hee hce hce' hu hH hP hno ha hb hev hb0⟩

theorem hermSwap_struct : ∀ {k R V : Type} [Field k] [CommRing R] [AddCommGroup V] [Module R V]
    (φ : R ≃+* k × k) (c : R →+* R), (∀ r, φ (c r) = (φ r).swap) → ∀ h : V → V → R, IsHerm c h →
    IsPerfect h → (∀ x y, h x x = 0 → h x y ≠ 1) →
    Subsingleton V ∨ ∃ w₀ : V, (∀ x, ∃ r : R, x = r • w₀) ∧ IsUnit (h w₀ w₀) := by
  intro k R V _ _ _ _ φ c hc h hH hP hno
  exact hermitian_split_rank_one_struct φ c hc h hH hP hno

end GlobalTheory.CompanionTheory.KFin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralPointsOpenCompact
section
open NumberField IsDedekindDomain Matrix

namespace GlobalTheory.CompanionTheory.IntegralPoints

theorem isOpen_isCompact_intGL {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (O : Subring R) (ho : IsOpen (O : Set R)) (hc : IsCompact (O : Set R)) (n : ℕ) :
    IsOpen {g : GL (Fin n) R | (∀ i j, (g : Matrix (Fin n) (Fin n) R) i j ∈ O) ∧
        ∀ i j, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j ∈ O} ∧
    IsCompact {g : GL (Fin n) R | (∀ i j, (g : Matrix (Fin n) (Fin n) R) i j ∈ O) ∧
        ∀ i j, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j ∈ O} := by
  constructor
  · have e : {g : GL (Fin n) R | (∀ i j, (g : Matrix (Fin n) (Fin n) R) i j ∈ O) ∧
        ∀ i j, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j ∈ O} =
        (⋂ i, ⋂ j, (fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R) i j) ⁻¹' (O : Set R)) ∩
        (⋂ i, ⋂ j, (fun g : GL (Fin n) R => ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j) ⁻¹' (O : Set R)) := by
      ext g
      simp [Set.mem_iInter]
    rw [e]
    refine IsOpen.inter ?_ ?_
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        ho.preimage (Units.continuous_val.matrix_elem i j)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        ho.preimage (Units.continuous_coe_inv.matrix_elem i j)
  · have hM : IsCompact {A : Matrix (Fin n) (Fin n) R | ∀ i j, A i j ∈ O} := by
      have := isCompact_univ_pi fun _ : Fin n => isCompact_univ_pi fun _ : Fin n => hc
      have e : {A : Matrix (Fin n) (Fin n) R | ∀ i j, A i j ∈ O} =
          Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => (O : Set R) :=
        Set.ext fun A => ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
      exact e ▸ this
    have := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) R)).isCompact_preimage
      (hM.prod (hM.image MulOpposite.continuous_op))
    convert this using 1
    ext g
    exact ⟨fun h => ⟨h.1, _, h.2, rfl⟩, fun ⟨h1, A, hA, e⟩ => ⟨h1, fun i j => by
      have : A = ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := MulOpposite.op_injective e
      exact this ▸ hA i j⟩⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem coe_Kf (n : ℕ) : (PositivityTheory.Rg.BcB.G8.Kf E n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) =
    {g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E) | (∀ i j, (g : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j ∈ Formalism.UG.intAd E) ∧
      ∀ i j, ((g⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j ∈
        Formalism.UG.intAd E} := by
  ext g
  simp only [SetLike.mem_coe, PositivityTheory.Rg.BcB.G8.Kf, Subgroup.mem_iInf, Subgroup.mem_comap, Set.mem_setOf_eq]
  constructor
  · intro h
    refine ⟨fun i j w => ?_, fun i j w => ?_⟩
    · have h1 := h w
      rw [← SetLike.mem_coe, GlobalTheory.LFun.KGL, GlobalTheory.LFun.IntPtsUnitary.coe_GLint] at h1
      exact h1.1 i j
    · have h1 := h w
      rw [← SetLike.mem_coe, GlobalTheory.LFun.KGL, GlobalTheory.LFun.IntPtsUnitary.coe_GLint] at h1
      have h2 := h1.2 i j
      rw [← map_inv] at h2
      exact h2
  · rintro ⟨h1, h2⟩ w
    rw [← SetLike.mem_coe, GlobalTheory.LFun.KGL, GlobalTheory.LFun.IntPtsUnitary.coe_GLint]
    refine ⟨fun i j => h1 i j w, fun i j => ?_⟩
    rw [← map_inv]
    exact h2 i j w

theorem kfOC : PositivityTheory.Rg.BcB.G8.KfOC := by
  intro E _ _ _ n
  haveI : T2Space (FiniteAdeleRing (𝓞 E) E) := Formalism.MainNotions.Gaps.LevGap.t2Space_adeleRing_numberField
  rw [coe_Kf]
  exact isOpen_isCompact_intGL (Formalism.UG.intAd E) Formalism.MainNotions.Gaps.LevGap.isOpen_intAd
    Formalism.MainNotions.Gaps.LevGap.isCompact_intAd n

end GlobalTheory.CompanionTheory.IntegralPoints
end

