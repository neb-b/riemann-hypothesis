module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0015
public import Formalism.MahlerMeasure.MahlerMeasureProofs.PhiInt
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0002
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0016

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockValuationOverZpHolds
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem loss_num (s t r Λ L1 U k0 : ℝ) (ht0 : 0 ≤ t) (hts : t ≤ s) (hr : 4 ≤ r) (hΛ : 1 ≤ Λ) (hL0 : 0 ≤ L1)
    (hL : L1 ≤ Λ) (hU : U ≤ (t + 1) * ((r + 1) * (Λ + 1) + 1)) (hk : 0 ≤ k0) :
    ((((2 * s + 1) + 1) * r + (t + 1) * 2) + (t + 1)) * L1 + 2 * U ≤ 10 * (s + 1) * (r + 1) * Λ + k0 := by
  have hs0 : 0 ≤ s := le_trans ht0 hts
  have hA : 0 ≤ (((2 * s + 1) + 1) * r + (t + 1) * 2) + (t + 1) := by nlinarith
  have e1 : ((((2 * s + 1) + 1) * r + (t + 1) * 2) + (t + 1)) * L1 ≤
      ((2 * s + 2) * r + 3 * (s + 1)) * Λ := by
    calc ((((2 * s + 1) + 1) * r + (t + 1) * 2) + (t + 1)) * L1
        ≤ ((((2 * s + 1) + 1) * r + (t + 1) * 2) + (t + 1)) * Λ := mul_le_mul_of_nonneg_left hL hA
      _ ≤ ((2 * s + 2) * r + 3 * (s + 1)) * Λ := by nlinarith
  have e2 : U ≤ (s + 1) * ((r + 1) * (Λ + 1) + 1) := by
    have : 0 ≤ (r + 1) * (Λ + 1) + 1 := by nlinarith
    nlinarith
  have e3 : (s + 1) * ((r + 1) * (Λ + 1) + 1) ≤ (s + 1) * ((2 * r + 3) * Λ) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    nlinarith
  nlinarith

section Inst

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

theorem restValNum_proved {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1) (hCE2 : 0 ≤ CE2)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) : RestValNum C0 CE1 CE2 X := by
  classical
  intro aTop hT aPlus hP b hK l hl j' jp' hl' μ hw
  obtain ⟨hA1, h2, h3, h4, h5⟩ := gB_deg_le C0 CE1 CE2 X hCYb hCE1 hCE2 hH aTop hT aPlus hP b hK
  have hF := hiFacts C0 CYb Cde Ck CD Cb Cc X hCYb hH
  have hlok : (gB C0 CE1 CE2 X aTop aPlus b).LevelOK l.1 l.2 := (Finset.mem_filter.1 hl).2
  have hv := val_gen X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (gB_blockOK C0 CE1 CE2 X aTop aPlus b) (aBig X)
    h2 h3 h4 h5 l.1 l.2 hlok j' jp' hl' μ hw
  have hvR : (padicValNat X.p (lvC (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2 *
      degFact (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2) : ℝ) ≤
      (padicValNat X.p (μ.prod fun _ k => k.factorial) : ℝ) +
        (((((2 * (X.s : ℝ) + 1) + 1) * (X.r : ℝ) + (((X.S C0 CE1 CE2).t : ℝ) + 1) * 2) +
          (((X.S C0 CE1 CE2).t : ℝ) + 1)) * (Nat.log X.p (8 * aBig X + X.r) : ℝ)) := by
    have := (Nat.cast_le (α := ℝ)).2 hv
    push_cast at this
    exact this

  have hmR : (4 : ℝ) ≤ (X.r : ℝ) := by exact_mod_cast hF.m4
  have hp25 : (25 : ℝ) ≤ (X.p : ℝ) := by nlinarith [hF.p_ge]
  have hp1 : (1 : ℝ) < (X.p : ℝ) := by linarith
  have hs0 : (0 : ℝ) ≤ (X.s : ℝ) := Nat.cast_nonneg _
  have ha1 : (1 : ℝ) ≤ (X.L.a : ℝ) := hF.a1
  have hsm : 2 * (X.s : ℝ) + 2 ≤ (X.r : ℝ) := by exact_mod_cast hF.s_le
  have hsp : 3 * (X.s : ℝ) + 2 ≤ (X.p : ℝ) := by nlinarith [hF.p_ge]
  have hbase : (0 : ℝ) < 8 * (X.L.a : ℝ) + (X.r : ℝ) := by linarith
  have hΛ : 1 ≤ lgA X.p X.L.a X.r := by
    unfold lgA
    have : 0 ≤ Real.logb X.p (8 * (X.L.a : ℝ) + (X.r : ℝ)) := Real.logb_nonneg hp1 (by linarith)
    linarith
  have hbig : Real.logb X.p (8 * (aBig X : ℝ) + (X.r : ℝ)) ≤ lgA X.p X.L.a X.r := by
    have e1 : 8 * (aBig X : ℝ) + (X.r : ℝ) ≤ (3 * (X.s : ℝ) + 2) * (8 * (X.L.a : ℝ) + (X.r : ℝ)) := by
      unfold aBig; push_cast; nlinarith
    have e0 : (0 : ℝ) < 8 * (aBig X : ℝ) + (X.r : ℝ) := by
      have : (0 : ℝ) ≤ (aBig X : ℝ) := Nat.cast_nonneg _
      linarith
    have e2 := Real.logb_le_logb_of_le hp1 e0 e1
    rw [Real.logb_mul (by linarith) hbase.ne'] at e2
    have e3 : Real.logb X.p (3 * (X.s : ℝ) + 2) ≤ 1 := by
      rw [Real.logb_le_iff_le_rpow hp1 (by linarith), Real.rpow_one]
      exact hsp
    unfold lgA
    linarith
  have hL1 : (Nat.log X.p (8 * aBig X + X.r) : ℝ) ≤ lgA X.p X.L.a X.r := by
    have := Real.natLog_le_logb (8 * aBig X + X.r) X.p
    push_cast at this
    exact this.trans hbig
  have hU : (expU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (aBig X) : ℝ) ≤
      (((X.S C0 CE1 CE2).t : ℝ) + 1) * (((X.r : ℝ) + 1) * (lgA X.p X.L.a X.r + 1) + 1) := by
    have e1 : (expU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (aBig X) : ℝ) =
        (((X.S C0 CE1 CE2).t : ℝ) + 1) * (⌈((X.r : ℝ) + 1) * Formalism.GM.lgV2 X.p (aBig X) X.r⌉₊ : ℝ) := by
      unfold expU
      push_cast
      rfl
    rw [e1]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have e2 : Formalism.GM.lgV2 X.p (aBig X) X.r ≤ lgA X.p X.L.a X.r + 1 := by
      unfold Formalism.GM.lgV2
      linarith
    have e3 : 0 ≤ Formalism.GM.lgV2 X.p (aBig X) X.r := by
      unfold Formalism.GM.lgV2
      have : 0 ≤ Real.logb X.p (8 * (aBig X : ℝ) + (X.r : ℝ)) := by
        apply Real.logb_nonneg hp1
        have : (0 : ℝ) ≤ (aBig X : ℝ) := Nat.cast_nonneg _
        linarith
      linarith
    have e4 := (Nat.ceil_lt_add_one (show 0 ≤ ((X.r : ℝ) + 1) * Formalism.GM.lgV2 X.p (aBig X) X.r by positivity)).le
    refine e4.trans ?_
    have : ((X.r : ℝ) + 1) * Formalism.GM.lgV2 X.p (aBig X) X.r ≤ ((X.r : ℝ) + 1) * (lgA X.p X.L.a X.r + 1) :=
      mul_le_mul_of_nonneg_left e2 (by positivity)
    linarith
  have hk0 : 0 ≤ kappaZeroExponent X.p X.L.a X.Nt X.r := by
    unfold kappaZeroExponent
    have : 0 ≤ Real.logb X.p (X.L.a : ℝ) := Real.logb_nonneg hp1 ha1
    positivity
  have hts : ((X.S C0 CE1 CE2).t : ℝ) ≤ (X.s : ℝ) := by
    have : (X.S C0 CE1 CE2).t ≤ X.s := Nat.sub_le _ _
    exact_mod_cast this
  have hfin := loss_num (X.s : ℝ) ((X.S C0 CE1 CE2).t : ℝ) (X.r : ℝ) (lgA X.p X.L.a X.r)
    (Nat.log X.p (8 * aBig X + X.r) : ℝ) (expU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (aBig X) : ℝ)
    (kappaZeroExponent X.p X.L.a X.Nt X.r) (Nat.cast_nonneg _) hts hmR hΛ (Nat.cast_nonneg _) hL1 hU hk0
  unfold levelPassageLoss
  linarith

theorem block_valuation_over_Zp_holds {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1) (hCE2 : 0 ≤ CE2)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) : BlockBoundIntegers C0 CE1 CE2 X :=
  block_valuation_Zp_of_numeric_bound C0 CE1 CE2 X hCYb hCE1 hCE2 hH (restValNum_proved C0 CE1 CE2 X hCYb hCE1 hCE2 hH)

end Inst

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.CommuteEPderiv
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset

section Comm

variable {p : ℕ} [Fact p.Prime] {σ : Type} {r : ℕ}

theorem pderiv_mul_free (v : σ) (g f : MvPolynomial σ ℚ_[p]) (hg : pderiv v g = 0) :
    pderiv v (g * f) = g * pderiv v f := by
  rw [Derivation.leibniz, hg, smul_zero, add_zero, smul_eq_mul]

theorem pderiv_pair_free (w e : Fin r → σ) (v : σ) (hw : ∀ c, w c ≠ v) (he : ∀ c, e c ≠ v) :
    pderiv v (∑ c, X (w c) * X (e c) : MvPolynomial σ ℚ_[p]) = 0 := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [Derivation.leibniz, pderiv_X, pderiv_X, Pi.single_eq_of_ne (he c), Pi.single_eq_of_ne (hw c)]
  simp

theorem commute_E_pderiv (w e : Fin r → σ) (v : σ) (hw : ∀ c, w c ≠ v) (he : ∀ c, e c ≠ v) :
    Commute (Formalism.GM.tieE (k := ℚ_[p]) w e) (pderiv v : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap := by
  refine LinearMap.ext fun f => ?_
  show (∑ c, X (w c) * X (e c)) * pderiv v f = pderiv v ((∑ c, X (w c) * X (e c)) * f)
  rw [pderiv_mul_free v _ f (pderiv_pair_free w e v hw he)]

theorem commute_E_F (w e w' e' : Fin r → σ) (h1 : ∀ c c', w c ≠ w' c') (h2 : ∀ c c', e c ≠ w' c')
    (h3 : ∀ c c', w c ≠ e' c') (h4 : ∀ c c', e c ≠ e' c') :
    Commute (Formalism.GM.tieE (k := ℚ_[p]) w e) (Formalism.GM.tieF (k := ℚ_[p]) w' e') := by
  unfold Formalism.GM.tieF
  refine Commute.sum_right _ _ _ fun c' _ => ?_
  rw [← Module.End.mul_eq_comp]
  exact (commute_E_pderiv w e (w' c') (fun c => h1 c c') (fun c => h2 c c')).mul_right
    (commute_E_pderiv w e (e' c') (fun c => h3 c c') (fun c => h4 c c'))

theorem commute_E_E (w e w' e' : Fin r → σ) :
    Commute (Formalism.GM.tieE (k := ℚ_[p]) w e) (Formalism.GM.tieE (k := ℚ_[p]) w' e') := by
  refine LinearMap.ext fun f => ?_
  show (∑ c, X (w c) * X (e c)) * ((∑ c, X (w' c) * X (e' c)) * f) =
    (∑ c, X (w' c) * X (e' c)) * ((∑ c, X (w c) * X (e c)) * f)
  ring

set_option maxHeartbeats 1000000 in
theorem commute_F_F (w e w' e' : Fin r → σ) :
    Commute (Formalism.GM.tieF (k := ℚ_[p]) w e) (Formalism.GM.tieF (k := ℚ_[p]) w' e') := by
  unfold Formalism.GM.tieF
  refine Commute.sum_left _ _ _ fun c _ => Commute.sum_right _ _ _ fun c' _ => ?_
  rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
  have h1 : Commute (pderiv (w c) : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap
      ((pderiv (w' c')).toLinearMap * (pderiv (e' c')).toLinearMap) :=
    (Formalism.GM.M.PhiIntegrality.commute_pderiv (w c) (w' c')).mul_right (Formalism.GM.M.PhiIntegrality.commute_pderiv (w c) (e' c'))
  have h2 : Commute (pderiv (e c) : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap
      ((pderiv (w' c')).toLinearMap * (pderiv (e' c')).toLinearMap) :=
    (Formalism.GM.M.PhiIntegrality.commute_pderiv (e c) (w' c')).mul_right (Formalism.GM.M.PhiIntegrality.commute_pderiv (e c) (e' c'))
  exact h1.mul_left h2

theorem commute_tiePhi (w e w' e' : Fin r → σ) (h1 : ∀ c c', w c ≠ w' c') (h2 : ∀ c c', e c ≠ w' c')
    (h3 : ∀ c c', w c ≠ e' c') (h4 : ∀ c c', e c ≠ e' c') (o n z o' n' z' : ℕ) (x : MvPolynomial σ ℚ_[p]) :
    Formalism.GM.tiePhi w e o n z (Formalism.GM.tiePhi w' e' o' n' z' x) = Formalism.GM.tiePhi w' e' o' n' z' (Formalism.GM.tiePhi w e o n z x) := by
  have cEE := commute_E_E (p := p) w e w' e'
  have cFF := commute_F_F (p := p) w e w' e'
  have cEF := commute_E_F (p := p) w e w' e' h1 h2 h3 h4
  have cFE := (commute_E_F (p := p) w' e' w e (fun c c' => (h1 c' c).symm) (fun c c' => (h3 c' c).symm)
    (fun c c' => (h2 c' c).symm) (fun c c' => (h4 c' c).symm)).symm
  have cP : Commute (Formalism.GM.tiePhi (k := ℚ_[p]) w e o n z) (Formalism.GM.tiePhi (k := ℚ_[p]) w' e' o' n' z') := by
    unfold Formalism.GM.tiePhi
    refine Commute.sum_left _ _ _ fun j _ => Commute.sum_right _ _ _ fun j' _ => ?_
    refine (Commute.smul_left ?_ _).smul_right _
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
    exact ((cEE.pow_pow j j').mul_right (cEF.pow_pow j j')).mul_left ((cFE.pow_pow j j').mul_right (cFF.pow_pow j j'))
  exact LinearMap.congr_fun cP.eq x

end Comm

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.GoodLeSmallMat
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset


open Classical in
def GoodLeSmallMat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n m : ℕ) (X Y : Fin n → Fin m → ℤ_[p]) (c : Fin m → ℚ_[p]) (D : ℤ),
    (∀ i j, ∑ a, (X i a : ℚ_[p]) * c a * (Y j a : ℚ_[p]) = if i = j then (p : ℚ_[p]) ^ D else 0) →
    n ≤ (Finset.univ.filter (fun a : Fin m => c a ≠ 0 ∧ (c a).valuation ≤ D)).card

theorem B_sum_left {p : ℕ} [Fact p.Prime] {σ ι : Type} (B : MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p])
    (hsm : ∀ (c : ℚ_[p]) u v, B (c • u) v = c * B u v) (hadd : ∀ u u' v, B (u + u') v = B u v + B u' v)
    (s : Finset ι) (g : ι → MvPolynomial σ ℚ_[p]) (v : MvPolynomial σ ℚ_[p]) :
    B (∑ i ∈ s, g i) v = ∑ i ∈ s, B (g i) v := by
  classical
  have h0 : B 0 v = 0 := by
    have := hsm 0 0 v
    simpa using this
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih => rw [Finset.sum_insert ha, hadd, ih, Finset.sum_insert ha]

theorem goodLeSmall_of (h : GoodLeSmallMat) : GoodLeSmall := by
  intro p _ σ B L W D _ _ hsm hadd hsy m f hf _ hspan horth
  obtain ⟨x, y, hx, hy, hxy⟩ := goodCount_mem p B L D
  have hcoord : ∀ v ∈ L, ∃ X : Fin m → ℤ_[p], ∑ a, X a • f a = v := by
    intro v hv
    rw [← hspan] at hv
    exact (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).1 hv
  choose! X hX using hcoord
  have hsmZ : ∀ (c : ℤ_[p]) (u : MvPolynomial σ ℚ_[p]), c • u = (c : ℚ_[p]) • u :=
    fun c u => (algebraMap_smul ℚ_[p] c u).symm
  have hexp : ∀ v ∈ L, ∀ w, B v w = ∑ a, (X v a : ℚ_[p]) * B (f a) w := by
    intro v hv w
    conv_lhs => rw [← hX v hv]
    rw [B_sum_left B hsm hadd]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hsmZ, hsm]
  have hfy : ∀ a j, B (f a) (y j) = (X (y j) a : ℚ_[p]) * B (f a) (f a) := by
    intro a j
    rw [hsy _ (hf a) _ (hy j), hexp _ (hy j)]
    rw [Finset.sum_eq_single a]
    · intro b _ hb
      rw [horth b a hb, mul_zero]
    · intro ha; exact absurd (Finset.mem_univ a) ha
  exact h p _ m (fun i => X (x i)) (fun j => X (y j)) (fun a => B (f a) (f a)) D (fun i j => by
    rw [← hxy i j, hexp _ (hx i)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hfy]
    ring)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.LowerBoundInitialMultiplicity
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

section N0

variable (hS : SegFacts C0 CE1 CE2 X)
include hS

theorem cast_sub_ge (w j : ℕ) : (w : ℝ) - j ≤ ((w - j : ℕ) : ℝ) := by
  rcases le_total j w with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]
    have : (w : ℝ) ≤ j := by exact_mod_cast h
    linarith

theorem lower_bound_initial_multiplicity {dl : DCl X} {a : Fin X.s → ℕ} (ha : a ∈ cbox C0 CE1 CE2 X dl)
    {x : Σ _ : SegBlock X.s X.r, Lv C0 CE1 CE2 X} (hx : x ∈ idx C0 CE1 CE2 X dl a) (i : Fin (X.S C0 CE1 CE2).t) :
    (X.L.a : ℝ) - ((X.r : ℝ) + 1) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) - 5 / 2 * X.L.b' ≤
      ((XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
  obtain ⟨hK, hdl, hlv⟩ := digits_of_idx hx
  have hK' := hK
  obtain ⟨hDig, hK1, -, -⟩ := hK'
  set u := uTop (X.S C0 CE1 CE2) i with hu
  have hσu : (X.S C0 CE1 CE2).sigma ≤ (u : ℕ) := by
    simp [hu, uTop]
  set P := SegData.P X.p (X.S C0 CE1 CE2) u with hPdef
  have hPpos : 0 < P := twoPow_pos C0 CE1 CE2 X u
  have hj : x.2.1 i ≤ x.1.o u := (((mem_lv _ _ _).mp hlv).1 i).1
  have hA : coarseA X.p (X.S C0 CE1 CE2) x.1 u ≤ (X.S C0 CE1 CE2).bTop u / P :=
    Nat.div_le_div_right (Nat.sub_le _ _)
  have hjP : x.2.1 i * P ≤ (X.S C0 CE1 CE2).bTop u :=
    (Nat.mul_le_mul_right _ ((hj.trans (hK1 u hσu).1).trans hA)).trans (Nat.div_mul_le_self _ _)
  have hry : x.1.ry = dl.2 := by rw [← hdl]
  have hne : (Nl C0 CE1 CE2 X dl x.2 i).Nonempty := (Wl_ne ha u).image _
  have hn0 : (XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i = sInf (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ) := rfl
  have hmem : sInf (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ) ∈ (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ) :=
    Nat.sInf_mem (Finset.coe_nonempty.mpr hne)
  rw [Finset.mem_coe] at hmem
  obtain ⟨v, hv, hcm⟩ := Finset.mem_image.mp hmem
  simp only [Wl, Finset.mem_filter, flipOneThree.Inst.winA, Finset.mem_Icc] at hv
  obtain ⟨⟨hav, -⟩, hsv, hdvd⟩ := hv
  rw [← hu] at hsv hdvd
  rw [hn0, ← hcm]
  have hsum : ∑ c : Fin (X.r + 1), dl.2 u c ≤ (X.r + 1) * P := by
    calc ∑ c : Fin (X.r + 1), dl.2 u c ≤ ∑ _c : Fin (X.r + 1), P := by
          apply Finset.sum_le_sum
          intro c _
          rw [← hry]
          exact le_of_lt (hDig.1 u c).2
      _ = (X.r + 1) * P := by simp
  have hQ : (v - ∑ c : Fin (X.r + 1), dl.2 u c) / P * P = v - ∑ c : Fin (X.r + 1), dl.2 u c :=
    Nat.div_mul_cancel hdvd
  have hc1 := cast_sub_ge hS ((v - ∑ c : Fin (X.r + 1), dl.2 u c) / P) (x.2.1 i)
  have hcm' : cm C0 CE1 CE2 X dl x.2 i v = (v - ∑ c : Fin (X.r + 1), dl.2 u c) / P - x.2.1 i := rfl
  rw [hcm']
  have hQr : (((v - ∑ c : Fin (X.r + 1), dl.2 u c) / P : ℕ) : ℝ) * (P : ℝ) =
      (v : ℝ) - (∑ c : Fin (X.r + 1), dl.2 u c : ℕ) := by
    rw [← Nat.cast_sub hsv, ← Nat.cast_mul, hQ]
  have hsumR : ((∑ c : Fin (X.r + 1), dl.2 u c : ℕ) : ℝ) ≤ ((X.r : ℝ) + 1) * (P : ℝ) := by
    exact_mod_cast hsum
  have hjPR : ((x.2.1 i : ℕ) : ℝ) * (P : ℝ) ≤ 5 / 2 * X.L.b' := by
    have h1 : (((x.2.1 i * P : ℕ)) : ℝ) ≤ (X.S C0 CE1 CE2).bTop u := by exact_mod_cast hjP
    push_cast at h1
    linarith [hS.bTop u]
  have havR : (X.L.a : ℝ) ≤ v := by exact_mod_cast hav
  have hPR : (0 : ℝ) ≤ (P : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem restSI_proved (hFree : RestFree C0 CE1 CE2 X) : RestSI (C0 := C0) (CE1 := CE1) (CE2 := CE2) (X := X) := by
  intro dl hdl a ha x hx i
  have hF := hS.hF
  have hinj : Function.Injective (uTop (X.S C0 CE1 CE2)) := by
    intro k k' h
    simp only [uTop, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  set n : Fin (X.S C0 CE1 CE2).t → ℕ := fun k => topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) k) with hn
  set a' := ovr (uTop (X.S C0 CE1 CE2)) a n with haeq
  have ha' : a' ∈ cbox C0 CE1 CE2 X dl := by
    have hb := cbox_eq C0 CE1 CE2 X dl a ha
    rw [hb]
    apply ovr_mem _ hinj
    · rw [← hb]
      exact ha
    · exact Fintype.mem_piFinset.mpr (fun k => topA_mem_Wl ha _)
  have hx' : x ∈ idx C0 CE1 CE2 X dl a' := by
    rw [← hFree dl hdl a ha a' ha']
    exact hx
  obtain ⟨hK', -, -⟩ := digits_of_idx hx'
  obtain ⟨-, hdl0, -⟩ := digits_of_idx hx
  have hry : x.1.ry = dl.2 := by rw [← hdl0]
  have hT' := (mem_cbox' ha').1
  have hSb := S_bound hS a' hT' x.1 hK' x.2 i
  have hn0 := lower_bound_initial_multiplicity hS ha hx i
  have htop : (XMof C0 CE1 CE2 X dl a x.1 x.2).top = fun k =>
      (n k - ∑ c : Fin (X.r + 1), x.1.ry (uTop (X.S C0 CE1 CE2) k) c) /
        SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) k) - x.2.1 k := by
    funext k
    have hne : (Nl C0 CE1 CE2 X dl x.2 k).Nonempty := (Wl_ne ha _).image _
    have h1 := cm_top (dl := dl) x.2 k (Wl_ne ha _)
    have h2 : sInf (↑(Nl C0 CE1 CE2 X dl x.2 k) : Set ℕ) ≤ (Nl C0 CE1 CE2 X dl x.2 k).sup id := by
      have hm := Nat.sInf_mem (Finset.coe_nonempty.mpr hne)
      exact Finset.le_sup (f := id) hm
    rw [hry]
    show sInf (↑(Nl C0 CE1 CE2 X dl x.2 k) : Set ℕ) +
        1 * ((Nl C0 CE1 CE2 X dl x.2 k).sup id - sInf (↑(Nl C0 CE1 CE2 X dl x.2 k) : Set ℕ) + 1 - 1) =
      cm C0 CE1 CE2 X dl x.2 k (n k)
    rw [h1]
    omega
  have hL : (XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies (XMof C0 CE1 CE2 X dl a x.1 x.2).T
      (XMof C0 CE1 CE2 X dl a x.1 x.2).top = lLL C0 CE1 CE2 X a' x.1 x.2 := by
    rw [htop, haeq, lLL_ovr]
    rfl
  have hP : (0 : ℝ) < (SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
    exact_mod_cast twoPow_pos C0 CE1 CE2 X _
  have hkP := hS.kP (uTop (X.S C0 CE1 CE2) i)
  have hm' : (4 : ℝ) ≤ X.L.m := by exact_mod_cast hF.m4
  have hsm : (2 * (X.s : ℝ) + 2) ≤ X.L.m := by exact_mod_cast hF.s_le
  have hpm := hF.p_ge
  have hp0 : (0 : ℝ) < X.p := by
    show (0 : ℝ) < X.L.p
    nlinarith
  have h48 : (4 * (X.s : ℝ) + 8) ≤ X.p := by
    show (4 * (X.s : ℝ) + 8) ≤ X.L.p
    nlinarith
  have hb'p : X.L.b' ≤ (X.L.a : ℝ) / X.p := by
    rw [le_div_iff₀ hp0]
    have := hF.b_lt
    show X.L.b' * X.L.p ≤ X.L.a
    linarith
  have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
  have hsum : (2 * (X.s : ℝ) + 1) * (2 * X.L.a / X.p) + 6 * ((X.L.a : ℝ) / X.p) ≤ X.L.a := by
    calc (2 * (X.s : ℝ) + 1) * (2 * X.L.a / X.p) + 6 * ((X.L.a : ℝ) / X.p)
        = (4 * (X.s : ℝ) + 8) * ((X.L.a : ℝ) / X.p) := by ring
      _ ≤ (X.p : ℝ) * ((X.L.a : ℝ) / X.p) := mul_le_mul_of_nonneg_right h48 (by positivity)
      _ = X.L.a := by field_simp
  have hreal : ((GM.M.TieData.S (lLL C0 CE1 CE2 X a' x.1 x.2) (gT C0 CE1 CE2 X x.1) i : ℕ) : ℝ) *
        (SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
      ((XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i : ℝ) *
        (SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
    linarith
  have hnat : GM.M.TieData.S (lLL C0 CE1 CE2 X a' x.1 x.2) (gT C0 CE1 CE2 X x.1) i ≤
      (XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i := by
    exact_mod_cast le_of_mul_le_mul_right hreal hP
  rw [hL]
  exact hnat

theorem restTMSize_proved (hFree : RestFree C0 CE1 CE2 X) : RestTMSize C0 CE1 CE2 X :=
  restTMSize_of hS hFree (restSI_proved hS hFree)

end N0

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

