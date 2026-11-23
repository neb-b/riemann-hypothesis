module

public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0008
public import Formalism.SatakeDualWeyl.Bundle0001
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeC
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0004

@[expose] public section

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawaC
section
open Formalism.UG Matrix

namespace Formalism.UG.P

section FIwasawaRed

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}

def fIwasawaTri (r : ℕ) (M : Matrix (Fin n) (Fin n) L) : Prop :=
  ∀ i j : Fin n, j.val < r → j < i → M i j = 0

def fIwasawaKm (M : Matrix (Fin n) (Fin n) L) : Prop := fIwasawaUn σ M ∧ fIwasawaInt M

private theorem antiJ_apply_adelic_iwasawa_hecke (i j : Fin n) :
    antiJ L n i j = if (i : ℕ) + j + 1 = n then 1 else 0 := rfl

private theorem mul_antiJ_apply' (N : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (N * antiJ L n) i j = N i (Fin.rev j) := by
  have hj := j.isLt
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev j)]
  · rw [antiJ_apply_adelic_iwasawa_hecke, if_pos (by rw [Fin.val_rev]; omega), mul_one]
  · intro k _ hk
    have hk' := k.isLt
    rw [antiJ_apply_adelic_iwasawa_hecke, if_neg, mul_zero]
    intro h
    apply hk
    ext
    rw [Fin.val_rev]
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem cT_apply_eq_sigma_transpose (N : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    cT σ N i j = σ (N j i) := rfl

private theorem cT_mul_reverse (A B : Matrix (Fin n) (Fin n) L) :
    cT σ (A * B) = cT σ B * cT σ A := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

private theorem cT_one_eq_one : cT σ (1 : Matrix (Fin n) (Fin n) L) = 1 := by
  ext i j
  rw [cT_apply_eq_sigma_transpose]
  by_cases h : i = j
  · subst h
    simp
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h), map_zero]

theorem fIwasawa_Km_mul {A B : Matrix (Fin n) (Fin n) L} (hA : fIwasawaKm σ A) (hB : fIwasawaKm σ B) :
    fIwasawaKm σ (A * B) := by
  unfold fIwasawaKm fIwasawaUn fIwasawaInt at *
  obtain ⟨hAu, hAi⟩ := hA
  obtain ⟨hBu, hBi⟩ := hB
  refine ⟨?_, fun i j => ?_⟩
  · calc cT σ (A * B) * antiJ L n * (A * B) = cT σ B * (cT σ A * antiJ L n * A) * B := by
          rw [cT_mul_reverse]
          simp only [Matrix.mul_assoc]
      _ = antiJ L n := by rw [hAu, hBu]
  · rw [Matrix.mul_apply]
    apply Valuation.map_sum_le
    intro k _
    rw [map_mul]
    exact mul_le_one' (hAi i k) (hBi k j)

theorem fIwasawa_Km_one : fIwasawaKm σ (1 : Matrix (Fin n) (Fin n) L) := by
  unfold fIwasawaKm fIwasawaUn fIwasawaInt
  refine ⟨by rw [cT_one_eq_one, Matrix.one_mul, Matrix.mul_one], fun i j => ?_⟩
  by_cases h : i = j
  · subst h
    simp
  · rw [Matrix.one_apply_ne h, map_zero]
    exact zero_le'

theorem fIwasawa_gram_un (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) (a b : Fin n) :
    ∑ j, σ (M (Fin.rev j) a) * M j b = if b = Fin.rev a then 1 else 0 := by
  unfold fIwasawaUn at hM
  have h := congrFun (congrFun hM a) b
  rw [Matrix.mul_apply] at h
  simp only [mul_antiJ_apply', cT_apply_eq_sigma_transpose, antiJ_apply_adelic_iwasawa_hecke] at h
  rw [h]
  have ha := a.isLt
  have hb := b.isLt
  by_cases hab : b = Fin.rev a
  · rw [if_pos, if_pos hab]
    rw [hab, Fin.val_rev]
    omega
  · rw [if_neg, if_neg hab]
    intro h'
    apply hab
    ext
    rw [Fin.val_rev]
    omega

private theorem sigma_diag_mul_rev_diag_and_rev_entries_zero (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) (r : ℕ)
    (hT : fIwasawaTri r M) (m : ℕ) : ∀ s : Fin n, s.val = m → s.val < r →
      σ (M s s) * M (Fin.rev s) (Fin.rev s) = 1 ∧
        ∀ b : Fin n, b < Fin.rev s → M (Fin.rev s) b = 0 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro s hsm hs
    have key : ∀ b : Fin n, b ≤ Fin.rev s →
        σ (M s s) * M (Fin.rev s) b = if b = Fin.rev s then 1 else 0 := by
      intro b hb
      rw [← fIwasawa_gram_un σ M hM s b, Finset.sum_eq_single (Fin.rev s)]
      · rw [Fin.rev_rev]
      · intro j _ hj
        have hne : Fin.rev j ≠ s := fun h => hj (by rw [← h, Fin.rev_rev])
        rcases lt_or_gt_of_ne hne with h | h
        · have hjs : (Fin.rev j).val < m := by
            rw [← hsm]
            exact h
          have hjr : (Fin.rev j).val < r := by omega
          have hjb : b < Fin.rev (Fin.rev j) := by
            have := b.isLt
            have := j.isLt
            have := s.isLt
            rw [Fin.rev_rev]
            rw [Fin.le_def, Fin.val_rev] at hb
            rw [Fin.lt_def, Fin.val_rev] at h
            rw [Fin.lt_def]
            omega
          have h0 := (ih _ hjs (Fin.rev j) rfl hjr).2 b hjb
          rw [Fin.rev_rev] at h0
          rw [h0, mul_zero]
        · rw [hT (Fin.rev j) s hs h, map_zero, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have h1 := key (Fin.rev s) le_rfl
    rw [if_pos rfl] at h1
    refine ⟨h1, fun b hb => ?_⟩
    have h2 := key b hb.le
    rw [if_neg (ne_of_lt hb)] at h2
    exact (mul_eq_zero.mp h2).resolve_left (left_ne_zero_of_mul_eq_one h1)

theorem fIwasawa_rows (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) (r : ℕ)
    (hT : fIwasawaTri r M) (s : Fin n) (hs : s.val < r) :
    σ (M s s) * M (Fin.rev s) (Fin.rev s) = 1 ∧
      ∀ b : Fin n, b < Fin.rev s → M (Fin.rev s) b = 0 := by
  exact sigma_diag_mul_rev_diag_and_rev_entries_zero σ M hM r hT s.val s rfl hs

theorem fIwasawa_col_zero (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) (r : ℕ)
    (hT : fIwasawaTri r M) (ρ : Fin n) (hρr : ρ.val = r) (hρ : ρ < Fin.rev ρ) :
    ∀ i, Fin.rev ρ < i → M i ρ = 0 := by
  intro i hi
  have hi' := i.isLt
  have hρ' := ρ.isLt
  have hs : (Fin.rev i).val < r := by
    rw [Fin.val_rev, ← hρr]
    rw [Fin.lt_def, Fin.val_rev] at hi
    omega
  have h := (fIwasawa_rows σ M hM r hT (Fin.rev i) hs).2 ρ (by rw [Fin.rev_rev]; exact lt_trans hρ hi)
  rwa [Fin.rev_rev] at h

theorem fIwasawa_iso (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) (ρ : Fin n)
    (hρ : ρ < Fin.rev ρ) : ∑ j, σ (M (Fin.rev j) ρ) * M j ρ = 0 := by
  rw [fIwasawa_gram_un σ M hM ρ ρ, if_neg (ne_of_lt hρ)]

theorem fIwasawa_perm (ρ a : Fin n) (hρ : ρ < Fin.rev ρ) (ha1 : ρ ≤ a) (ha2 : a ≤ Fin.rev ρ)
    (haa : a ≠ Fin.rev a) :
    ∃ π : Equiv.Perm (Fin n), π ρ = a ∧ (∀ i, π (Fin.rev i) = Fin.rev (π i)) ∧
      (∀ i, (i < ρ ∨ Fin.rev ρ < i) → π i = i) := by
  have hρn := ρ.isLt
  have han := a.isLt
  have haa' : a.val ≠ (Fin.rev a).val := fun h => haa (Fin.ext h)
  clear haa
  have harn := (Fin.rev a).isLt
  by_cases haρ : a = Fin.rev ρ
  · subst haρ
    refine ⟨Equiv.swap ρ (Fin.rev ρ), Equiv.swap_apply_left _ _, fun i => ?_, fun i hi => ?_⟩
    · have hin := i.isLt
      simp only [Equiv.swap_apply_def]
      split_ifs <;> (simp only [Fin.rev_rev, Fin.ext_iff, Fin.val_rev, Fin.lt_def, Fin.le_def] at * <;> omega)
    · have hin := i.isLt
      simp only [Equiv.swap_apply_def]
      split_ifs <;> (simp only [Fin.rev_rev, Fin.ext_iff, Fin.val_rev, Fin.lt_def, Fin.le_def] at * <;> omega)
  · refine ⟨Equiv.swap ρ a * Equiv.swap (Fin.rev ρ) (Fin.rev a), ?_, fun i => ?_, fun i hi => ?_⟩
    · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
      split_ifs <;> (simp only [Fin.rev_rev, Fin.ext_iff, Fin.val_rev, Fin.lt_def, Fin.le_def] at * <;> (try simp only [not_true_eq_false] at *) <;> omega)
    · have hin := i.isLt
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
      split_ifs <;> (simp only [Fin.rev_rev, Fin.ext_iff, Fin.val_rev, Fin.lt_def, Fin.le_def] at * <;> omega)
    · have hin := i.isLt
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
      split_ifs <;> (simp only [Fin.rev_rev, Fin.ext_iff, Fin.val_rev, Fin.lt_def, Fin.le_def] at * <;> omega)

end FIwasawaRed

end Formalism.UG.P
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatake
section
open Formalism.UG

noncomputable section

namespace Formalism.UG.P

theorem finsum_mul_eq_sum_over_classes {X Y : Type} (S : Finset X) (g φv : X → ℂ) (c : Y → ℂ) (φ1 : ℂ)
    (P : Y → X → Prop) {_ : ∀ y x, Decidable (P y x)}
    (hS : ∀ x, g x ≠ 0 → x ∈ S) (huniq : ∀ x y y', P y x → P y' x → y = y')
    (hφ : ∀ x y, P y x → φv x = c y * φ1) (hnone : ∀ x, (∀ y, ¬ P y x) → φv x = 0) :
    ∑ᶠ x, g x * φv x = (∑ᶠ y, c y * ∑ᶠ x, if P y x then g x else 0) * φ1 := by
  classical
  have hsl : Function.support (fun x => g x * φv x) ⊆ (S : Set X) :=
    fun x hx => hS x (left_ne_zero_of_mul hx)
  have hin : ∀ y, (∑ᶠ x, if P y x then g x else 0) = ∑ x ∈ S, if P y x then g x else 0 := by
    intro y
    apply finsum_eq_sum_of_support_subset
    intro x hx
    by_cases hP : P y x
    · exact hS x (by simpa [hP] using hx)
    · exact absurd (by simp [hP]) hx
  have hTfin : (⋃ x ∈ (S : Set X), {y | P y x}).Finite :=
    S.finite_toSet.biUnion fun x _ => Set.Subsingleton.finite fun y hy y' hy' => huniq x y y' hy hy'
  have hout : (∑ᶠ y, c y * ∑ x ∈ S, if P y x then g x else 0) =
      ∑ y ∈ hTfin.toFinset, c y * ∑ x ∈ S, if P y x then g x else 0 := by
    apply finsum_eq_sum_of_support_subset
    intro y hy
    rw [Set.Finite.coe_toFinset]
    have hne : (∑ x ∈ S, if P y x then g x else 0) ≠ 0 := right_ne_zero_of_mul hy
    obtain ⟨x, hxS, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    refine Set.mem_biUnion (Finset.mem_coe.mpr hxS) ?_
    by_contra hP
    exact hx (if_neg hP)
  rw [finsum_eq_sum_of_support_subset _ hsl]
  simp only [hin]
  rw [hout, Finset.sum_mul]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hxS => ?_
  by_cases hex : ∃ y, P y x
  · obtain ⟨y0, hy0⟩ := hex
    have hy0T : y0 ∈ hTfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact Set.mem_biUnion (Finset.mem_coe.mpr hxS) hy0
    rw [Finset.sum_eq_single y0, if_pos hy0, hφ x y0 hy0]
    · ring
    · intro y _ hy
      rw [if_neg (fun h => hy (huniq x y y0 h hy0))]
      ring
    · intro h
      exact absurd hy0T h
  · push_neg at hex
    rw [hnone x hex, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro y _
    rw [if_neg (hex y)]
    ring

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem fSatake_chiDelta_one {q m : ℕ} (α : Fin m → ℂ) :
    chiDeltaU (σ := σ) (n := n) q α 1 = 1 := by
  unfold chiDeltaU
  refine Finset.prod_eq_one fun i _ => ?_
  split_ifs with h
  · simp [fSatake_ord_one]
  · rfl

theorem fSatake_key (hSph : SphericalExistsU) [CompleteSpace L] {ϖ : L} {q m : ℕ}
    (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n) (hm' : n ≤ 2 * m + 1) {α : Fin m → ℂ}
    (hα : ∀ i, α i ≠ 0) {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n)) {φ : GU σ n → ℂ}
    (hφ : IsSphericalU q α φ) :
    ∑ᶠ x : GU σ n ⧸ KU σ n, h x.out * φ x.out = SatU ϖ q h α * φ 1 := by
  classical
  have hfin := finite_supp (KU σ n) (isCommensurated_integral_unitary_of_unramified hU n) h hh
  unfold SatU
  exact finsum_mul_eq_sum_over_classes (S := hfin.toFinset) (g := fun x => h x.out) (φv := fun x => φ x.out)
    (c := fun a : Fin m → ℤ =>
      ∏ i : Fin m, α i ^ (a i) * (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ))))
    (φ1 := φ 1)
    (P := fun a x => ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n,
      (((x.out : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n m a * (((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (((k : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))
    (fun x hx => hfin.mem_toFinset.mpr hx)
    (fun x a a' ⟨u, hu, k, hk, e⟩ ⟨u', hu', k', hk', e'⟩ =>
      fSatake_cell_unique hU hm hu hu' hk hk' (e.symm.trans e'))
    (fun x a ⟨u, hu, k, hk, e⟩ => fSatake_phi_cell hU hm hφ hu hk e)
    (fun x hx => fSatake_vanish hSph hU hm hm' hα hφ x.out (by
      rintro ⟨b, k, hb, hk, e⟩
      obtain ⟨a, u, hu, k', hk', e'⟩ := fSatake_cell_exists (m := m) hU hm hm' hb hk
      exact hx a ⟨u, hu, k', hk', e ▸ e'⟩))

theorem fSatake_hAct_sph {q m : ℕ} {α : Fin m → ℂ} {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n))
    {φ : GU σ n → ℂ} (hφ : IsSphericalU q α φ) : IsSphericalU q α (hAct (KU σ n) h φ) := by
  intro b g k hb hk
  have hb1 : IsBorelU (1 : GU σ n) := fun i j hij => by
    simp [Matrix.one_apply_ne (ne_of_lt hij).symm]
  have hr : ∀ (y κ : GU σ n), κ ∈ KU σ n → φ (y * κ) = φ y := fun y κ hκ => by
    have := hφ 1 y κ hb1 hκ
    simpa [fSatake_chiDelta_one] using this
  have hl : ∀ y : GU σ n, φ (b * y) = chiDeltaU q α b * φ y := fun y => by
    have := hφ b y 1 hb (KU σ n).one_mem
    simpa using this
  obtain ⟨hbi, -⟩ := hh
  unfold hAct
  calc ∑ᶠ x : GU σ n ⧸ KU σ n, h x.out • φ (b * g * k * x.out)
      = ∑ᶠ x : GU σ n ⧸ KU σ n, chiDeltaU q α b * (h x.out • φ (g * (k * x.out))) := by
        refine finsum_congr fun x => ?_
        rw [show b * g * k * x.out = b * (g * (k * x.out)) by group, hl, smul_eq_mul, smul_eq_mul]
        ring
    _ = chiDeltaU q α b * ∑ᶠ x : GU σ n ⧸ KU σ n, h x.out • φ (g * (k * x.out)) :=
        (mul_finsum _ _).symm
    _ = chiDeltaU q α b * ∑ᶠ x : GU σ n ⧸ KU σ n, h x.out • φ (g * x.out) := by
        congr 1
        symm
        rw [← finsum_comp_equiv (MulAction.toPerm k : (GU σ n ⧸ KU σ n) ≃ (GU σ n ⧸ KU σ n))]
        refine finsum_congr fun x => ?_
        obtain ⟨κ, hκ⟩ := out_smul (KU σ n) k x
        simp only [MulAction.toPerm_apply]
        rw [hκ]
        have e1 : h (k * x.out * κ) = h x.out := hbi ⟨k, hk⟩ κ x.out
        rw [e1, show g * (k * x.out * κ) = g * (k * x.out) * κ by group, hr _ _ κ.2]

theorem satake_transform_inert_prime (hSphericalExistsU : Formalism.UG.SphericalExistsU) : Formalism.UG.SatakeInert := by
  intro L _ _ _ ϖ σ q n m hU hm hm' α hα h hh φ hφ
  obtain ⟨φ0, -, -, huniq⟩ := hSphericalExistsU L ϖ σ q n m hU hm hm' α hα
  have h1 := huniq _ (fSatake_hAct_sph hh hφ)
  have h2 := huniq _ hφ
  have hv : hAct (KU σ n) h φ 1 = SatU ϖ q h α * φ 1 := by
    unfold hAct
    simp only [one_mul, smul_eq_mul]
    exact fSatake_key hSphericalExistsU hU hm hm' hα hh hφ
  rw [h1, hv]
  conv_rhs => rw [h2]
  funext g
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem satake_transform_multiplicative (hSphericalExistsU : Formalism.UG.SphericalExistsU) : Formalism.UG.SatMul := by
  intro L _ _ _ ϖ σ q n m hU hm hm' α hα h₁ hh₁ h₂ hh₂
  obtain ⟨φ0, hφ0, hφ01, -⟩ := hSphericalExistsU L ϖ σ q n m hU hm hm' α hα
  have hSI := satake_transform_inert_prime hSphericalExistsU L ϖ σ q n m hU hm hm' α hα
  have hh₁' := hh₁
  have hh₂' := hh₂
  obtain ⟨hb₁, hs₁⟩ := hh₁'
  obtain ⟨hb₂, hs₂⟩ := hh₂'
  have hconv : conv (KU σ n) h₁ h₂ ∈ Hecke ℂ (KU σ n) := by
    show _ ∧ _
    exact ⟨conv_biInv _ _ _ hb₁ hb₂, conv_finDosetSupp (isCommensurated_integral_unitary_of_unramified hU n) _ _ hs₁ hs₂⟩
  have hb1 : IsBorelU (1 : GU σ n) := fun i j hij => by
    simp [Matrix.one_apply_ne (ne_of_lt hij).symm]
  have hamf : φ0 ∈ AMF ℂ (⊥ : Subgroup (GU σ n)) (KU σ n)
      (1 : Representation ℂ (⊥ : Subgroup (GU σ n)) ℂ) := by
    intro γ g κ
    have hγ : (γ : GU σ n) = 1 := Subgroup.mem_bot.mp γ.2
    rw [hγ, one_mul]
    have := hφ0 1 g κ hb1 κ.2
    simpa [fSatake_chiDelta_one] using this
  have hmul := hecke_act_mul (GU σ n) ⊥ (KU σ n) ℂ ℂ 1 (isCommensurated_integral_unitary_of_unramified hU n) h₁ hh₁ h₂ hh₂ φ0 hamf
  have hs2 : IsSphericalU q α (SatU ϖ q h₂ α • φ0) := fun b g k hb hk => by
    simp only [Pi.smul_apply, smul_eq_mul, hφ0 b g k hb hk]
    ring
  rw [hSI _ hconv _ hφ0, hSI _ hh₂ _ hφ0, hSI _ hh₁ _ hs2] at hmul
  have := congrFun hmul 1
  simp only [Pi.smul_apply, smul_eq_mul, hφ01, mul_one] at this
  rw [this]

end Formalism.UG.P
end
end

