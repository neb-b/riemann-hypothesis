module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.SharpRestriction.Divisibility.StatementFT.PeriodPointConditions

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField

namespace Formalism.MainNotions.DIV.HookProducts.AdmPerTw

variable {D : D7}

theorem vAdd_dvd_le (w : D.what₂.places.Pl) {n N : ℕ} (hN : N ≠ 0) (hd : n ∣ N) :
    (vAdd (D.plEq w) (n : D.what₂.LL) : ℝ) ≤ ur D w (padicValNat (D.what₂.places.resChar w) N : ℝ) := by
  have hpp := D.what₂.places.resChar_prime w
  have hn : n ≠ 0 := fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ hd))
  set p := D.what₂.places.resChar w with hp
  set k := padicValNat p n with hk
  obtain ⟨n', hn'⟩ : ∃ n', n' = n / p ^ n.factorization p := ⟨_, rfl⟩
  have hfac : n.factorization p = k := by rw [hk, Nat.factorization_def n hpp, Nat.padicValNat_def]
  have hprod : p ^ k * n' = n := by
    rw [hn', ← hfac]; exact Nat.ordProj_mul_ordCompl_eq_self n _
  have hcop : Nat.Coprime n' p := by
    rw [hn']; exact (Nat.coprime_ordCompl hpp hn).symm
  have hn'0 : n' ≠ 0 := by rintro rfl; simp at hprod; exact hn hprod.symm
  have hv' : vAdd (D.plEq w) ((n' : ℕ) : D.what₂.LL) = 0 := by
    have h := OrbitPlaces.val_coprime w n' hcop
    rw [D.val_eq w _ (Nat.cast_ne_zero.2 hn'0)] at h
    exact_mod_cast h
  have hpk : ((p : ℕ) : D.what₂.LL) ^ k ≠ 0 := pow_ne_zero _ (OrbitPlaces.p_ne w)
  have hv : vAdd (D.plEq w) (n : D.what₂.LL) = (k : ℤ) * (D.what₂.places.ramIdx w : ℤ) := by
    rw [← hprod, Nat.cast_mul, Nat.cast_pow, OrbitPlaces.vAdd_mul w hpk (Nat.cast_ne_zero.2 hn'0), OrbitPlaces.vAdd_pow, hv', add_zero]
  have hkN : k ≤ padicValNat p N := ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hN).1 ((_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _)).trans hd)
  rw [hv]
  unfold ur
  push_cast
  have h0 : (0 : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) := Nat.cast_nonneg _
  have h1 : (k : ℝ) ≤ (padicValNat p N : ℝ) := by exact_mod_cast hkN
  nlinarith

theorem card_stabilizer_dvd₂ (hD : DGamDef D) (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (c : (T.fm u μ).clsP) :
    Nat.card ((T.fm u μ).stabilizer₂ c) ∣ (D.mem u).C.DGam := by
  rw [← DGamDef.one hD u u μ]
  refine dvd_trans ?_ ((D.chTw u μ).dvd_DGam D.R.m le_rfl ((T.fm u μ).til c))
  rw [Nat.card_congr (MonoidHom.ofInjective ((T.fm u μ).stabMap_inj c)).toEquiv]
  exact Subgroup.card_subgroup_dvd_card _

end Formalism.MainNotions.DIV.HookProducts.AdmPerTw
