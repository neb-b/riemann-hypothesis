module

public import Formalism.SharpRestriction.Divisibility.OrbitPlaces

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.AdmissibleOfJetBounds
section
noncomputable section

open scoped BigOperators
open Classical
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.OrbitPlaces

namespace PI.OrbBoundFW

variable {D : D7} {L : SizeData₂ D}

theorem admissible_of_jet_bounds {E : Ent D} {p : ℕ} [Fact p.Prime] (h : OrbOK D p) (u : D.what₂.Word) (i : ℕ) (z : Pl D)
    (Th : MvPowerSeries (ZMod (nP D p) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[p])
    (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]) (hep : ‖ep‖ = 1) (hsg : sg = 1 ∨ sg = -1)
    (h1 : Formalism.MainNotions.product_zeroth_first_parts.B1 p (nP D p) be) (h2 : Formalism.MainNotions.product_zeroth_first_parts.B2 p (nP D p) be) (h3 : Formalism.MainNotions.product_zeroth_first_parts.B3 p (nP D p) be)
    (h4 : Formalism.MainNotions.product_zeroth_first_parts.B4 p (nP D p) be) (h0 : OrbitThetaExpansion (orbLoc E p h u i z Th) ep sg be) :
    (orbLoc E p h u i z Th).AdmB := by
  obtain ⟨U, hU, hT⟩ := h0
  exact ⟨ep, hep, be, ⟨sg, hsg, U, hU, hT⟩, h1, h2, h3, h4⟩

theorem kvalGe_mono {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 N1 l : ℕ} [Fact l.Prime]
    {nu : Lt → YoungDiagram} {Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]} {B B' : ℝ}
    (hK : Formalism.MainNotions.product_zeroth_first_parts.KvalGe N0 N1 l nu Th B) (hB : B' ≤ B) : Formalism.MainNotions.product_zeroth_first_parts.KvalGe N0 N1 l nu Th B' := by
  unfold Formalism.MainNotions.product_zeroth_first_parts.KvalGe at hK ⊢
  intro I m
  refine (hK I m).trans ?_
  have hl : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast (Fact.out : l.Prime).one_lt.le
  exact Real.rpow_le_rpow_of_exponent_le hl (neg_le_neg hB)

end PI.OrbBoundFW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.HidaSetting
section
noncomputable section

open scoped BigOperators
open Classical
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.OrbitPlaces

namespace PI.OrbBoundFW

variable {D : D7} {L : SizeData₂ D}

def wOrb (D : D7) (p i : ℕ) (z : Pl D) (s : ZMod (nP D p)) : ℝ := wPl D (i + 1) (orbMap D p z s)

def eOrb (E : Ent D) (p : ℕ) (u : D.what₂.Word) (i : ℕ) (z : Pl D) (s : ZMod (nP D p)) : ℝ :=
  if IsTopPl D (orbMap D p z s) then
    E.size u i (orbMap D p z s) - E.row u i (orbMap D p z s) 0 -
      (((D.R.k : ℝ) - 1) * wOrb D p i z s - 2 * wOrb D p i z s)
  else E.size u i (orbMap D p z s) - ((D.R.k : ℝ) - 1) * wOrb D p i z s

theorem three_le_k (D : D7) : 3 ≤ D.R.k := by
  have h := D.R.m_add_three_le_k
  omega

theorem setting_sq {X : Inst D L} {E : Ent D} (hS : Shape D L X E) {p : ℕ} [Fact p.Prime] (h : OrbOK D p)
    (hp : (p : ℝ) ≤ L.sc.X'' D.R.n) (u : D.what₂.Word) {i : ℕ} (hi : i < D.R.m) (z : Pl D)
    (Th : MvPowerSeries (ZMod (nP D p) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[p]) :
    (orbLoc E p h u i z Th).HidaSetting (L.sc.a ^ 2) := by
  have hxa := hS.xa
  have ha1 : 1 < L.sc.a := hxa.2
  have hp5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h.five
  refine ⟨?_, ?_, ?_⟩
  · show (p : ℝ) ≤ L.sc.a ^ 2
    nlinarith [hxa.1]
  · intro s
    exact hS.sizeA u i hi _
  · show 2 * Real.logb p (L.sc.a ^ 2) + 2 ≤ ((D.R.N i : ℕ) : ℝ) - 1
    have hk := hS.rankA
    have hx : 1 ≤ L.sc.a ^ 2 := by nlinarith
    have hlog : Real.logb p (L.sc.a ^ 2) ≤ Real.logb 5 (L.sc.a ^ 2) := by
      unfold Real.logb
      have hl5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
      have hlp : Real.log 5 ≤ Real.log p := Real.log_le_log (by norm_num) hp5
      have hx0 : 0 ≤ Real.log (L.sc.a ^ 2) := Real.log_nonneg hx
      rw [div_le_div_iff₀ (by linarith) hl5]
      nlinarith
    have hN : (D.R.k : ℝ) ≤ (D.R.N i : ℝ) := by
      have : D.R.k ≤ D.R.N i := by
        unfold Formalism.BasicNotions.Ranks.N
        exact Nat.le_add_right _ _
      exact_mod_cast this
    linarith

theorem wOrb_pos {X : Inst D L} {E : Ent D} (hS : Shape D L X E) (p : ℕ) {i : ℕ} (hi : i < D.R.m) (z : Pl D)
    (s : ZMod (nP D p)) : 0 < wOrb D p i z s := by
  unfold wOrb
  exact hS.wpos i hi _

theorem eOrb_bounds {X : Inst D L} {E : Ent D} (hS : Shape D L X E) (p : ℕ) (u : D.what₂.Word) {i : ℕ}
    (hi : i < D.R.m) (z : Pl D) (s : ZMod (nP D p)) :
    0 ≤ eOrb E p u i z s ∧ eOrb E p u i z s ≤ 4 * wOrb D p i z s := by
  unfold eOrb wOrb
  split_ifs with ht
  · exact hS.top u i hi _ ht
  · exact hS.low u i hi _ ht

theorem dl_off {E : Ent D} {p : ℕ} [Fact p.Prime] (h : OrbOK D p) (u : D.what₂.Word) (i : ℕ) (z : Pl D)
    (Th : MvPowerSeries (ZMod (nP D p) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[p])
    (s : ZMod (nP D p)) (hs : s ∉ (orbLoc E p h u i z Th).TT) :
    ((orbLoc E p h u i z Th).Dl s : ℝ) = ((D.R.k : ℝ) - 1) * wOrb D p i z s + eOrb E p u i z s := by
  have ht : ¬ IsTopPl D (orbMap D p z s) := fun ht => hs (Finset.mem_filter.2 ⟨Finset.mem_univ _, ht⟩)
  have hsz : ((orbLoc E p h u i z Th).Dl s : ℝ) = E.size u i (orbMap D p z s) := by
    have h1 : (orbLoc E p h u i z Th).Dl s = (E.nu u i (orbMap D p z s)).cells.card := by
      unfold Formalism.MainNotions.product_zeroth_first_parts.Loc.Dl
      split_ifs with hh
      · exact absurd hh hs
      · rfl
    rw [h1]
    rfl
  rw [hsz]
  unfold eOrb
  rw [if_neg ht]
  ring

theorem dl_on {E : Ent D} {p : ℕ} [Fact p.Prime] (h : OrbOK D p) (u : D.what₂.Word) (i : ℕ) (z : Pl D)
    (Th : MvPowerSeries (ZMod (nP D p) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[p])
    (s : ZMod (nP D p)) (hs : s ∈ (orbLoc E p h u i z Th).TT) :
    ((orbLoc E p h u i z Th).Dl s : ℝ) =
      ((D.R.k : ℝ) - 1) * wOrb D p i z s - 2 * wOrb D p i z s + eOrb E p u i z s := by
  have ht : IsTopPl D (orbMap D p z s) := (Finset.mem_filter.1 hs).2
  have hA : (E.nu u i (orbMap D p z s)).rowLen 0 ≤ (E.nu u i (orbMap D p z s)).cells.card := by
    calc (E.nu u i (orbMap D p z s)).rowLen 0
        = ((Finset.range ((E.nu u i (orbMap D p z s)).rowLen 0)).map
            ⟨fun j => ((0 : ℕ), j), fun a b hab => by simpa using hab⟩).card := by simp
      _ ≤ (E.nu u i (orbMap D p z s)).cells.card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk] at hx
          obtain ⟨j, hj, rfl⟩ := hx
          exact YoungDiagram.mem_iff_lt_rowLen.2 hj
  have hsz : ((orbLoc E p h u i z Th).Dl s : ℝ) =
      E.size u i (orbMap D p z s) - E.row u i (orbMap D p z s) 0 := by
    have h1 : (orbLoc E p h u i z Th).Dl s =
        (E.nu u i (orbMap D p z s)).cells.card - (E.nu u i (orbMap D p z s)).rowLen 0 := by
      unfold Formalism.MainNotions.product_zeroth_first_parts.Loc.Dl
      split_ifs with hh
      · rfl
      · exact absurd hs hh
    rw [h1, Nat.cast_sub hA]
    rfl
  rw [hsz]
  unfold eOrb
  rw [if_pos ht]
  ring

end PI.OrbBoundFW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.LossLe
section
noncomputable section

open scoped BigOperators
open Classical
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.OrbitPlaces

namespace PI.OrbBoundFW

variable {D : D7} {L : SizeData₂ D}

theorem loss_le {X : Inst D L} {E : Ent D} (hS : Shape D L X E) {C6 C : ℝ} {K : Consts} {ce : ErrC}
    (hC : CLarge C6 C K ce) {p : ℕ} [Fact p.Prime] (h : OrbOK D p) (hp : (p : ℝ) ≤ L.sc.X'' D.R.n) {i : ℕ}
    (hi : i < D.R.m) (r : Pl D) :
    C * ((nP D p : ℝ) * (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) * (Real.logb p (L.sc.a ^ 2) + 1)) ≤
      (nP D p : ℝ) * (D.R.N (i + 1 - 1) : ℝ) * (D.R.N (i + 1) : ℝ) *
          (Real.logb p (4 * (nP D p : ℝ) * Nm D * L.sc.a) + 1) +
        (K.dl1 * (nP D p : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a) +
          K.dl2 * (topsOrb D p r : ℝ) * Real.logb p (2 * L.sc.a) ^ 2) := by
  have hi1 : i + 1 - 1 = i := by omega
  rw [hi1]
  have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast h.five
  have ha1 : 1 < L.sc.a := hS.xa.2
  have hpa : (p : ℝ) ≤ L.sc.a := hp.trans hS.xa.1
  have hlp : 0 < Real.log p := Real.log_pos (by linarith)
  have hla : Real.log p ≤ Real.log L.sc.a := Real.log_le_log (by linarith) hpa
  have hLa : 1 ≤ Real.logb p L.sc.a := by
    rw [Real.logb, le_div_iff₀ hlp]; linarith
  have hL2 : Real.logb p (L.sc.a ^ 2) = 2 * Real.logb p L.sc.a := by
    simp only [Real.logb, Real.log_pow]; push_cast; ring
  have hL2a : Real.logb p L.sc.a ≤ Real.logb p (2 * L.sc.a) :=
    Real.logb_le_logb_of_le (by linarith) (by linarith) (by linarith)
  have hmono : ∀ j j' : ℕ, j ≤ j' → (D.R.N j : ℝ) ≤ (D.R.N j' : ℝ) := by
    intro j j' hjj
    have : D.R.N j ≤ D.R.N j' := by
      simp only [Formalism.BasicNotions.Ranks.N]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hjj) _
    exact_mod_cast this
  have hNm : Nm D = (D.R.N D.R.m : ℝ) := rfl
  have hN0 : (D.R.N i : ℝ) ≤ Nm D := hNm ▸ hmono _ _ (by omega)
  have hN1 : (D.R.N (i + 1) : ℝ) ≤ Nm D := hNm ▸ hmono _ _ (by omega)
  have hk1 : (1 : ℝ) ≤ D.R.N 0 := by
    have : 1 ≤ D.R.N 0 := by
      simp only [Formalism.BasicNotions.Ranks.N]; have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hNm1 : (1 : ℝ) ≤ Nm D := hk1.trans (hNm ▸ hmono _ _ (Nat.zero_le _))
  have hn2 : (2 : ℝ) ≤ nP D p := by exact_mod_cast h.two
  have hN0p : (0 : ℝ) ≤ D.R.N i := Nat.cast_nonneg _
  have hN1p : (0 : ℝ) ≤ D.R.N (i + 1) := Nat.cast_nonneg _
  have hC0 := hC.nonneg
  have hprod : (nP D p : ℝ) * (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) ≤ (nP D p : ℝ) * Nm D ^ 2 := by
    rw [mul_assoc, sq]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hN0 hN1 hN1p (by linarith)) (by linarith)
  have hprod0 : 0 ≤ (nP D p : ℝ) * (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) := by positivity

  have hL4 : Real.logb p L.sc.a ≤ Real.logb p (4 * (nP D p : ℝ) * Nm D * L.sc.a) := by
    apply Real.logb_le_logb_of_le (by linarith) (by linarith)
    have h21 : (2 : ℝ) * 1 ≤ (nP D p : ℝ) * Nm D := mul_le_mul hn2 hNm1 (by norm_num) (by linarith)
    nlinarith

  have hcl : C * (2 * Real.logb p L.sc.a + 1) ≤ (1 + K.dl1) * Real.logb p L.sc.a := by
    have e1 : C * (2 * Real.logb p L.sc.a + 1) ≤ 3 * C * Real.logb p L.sc.a := by
      nlinarith [mul_nonneg hC0 (sub_nonneg.2 hLa)]
    have e2 : 3 * C * Real.logb p L.sc.a ≤ (1 + K.dl1) * Real.logb p L.sc.a :=
      mul_le_mul_of_nonneg_right hC.dl1 (by linarith)
    linarith
  have hA : C * ((nP D p : ℝ) * (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) * (Real.logb p (L.sc.a ^ 2) + 1)) ≤
      (nP D p : ℝ) * (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) * ((1 + K.dl1) * Real.logb p L.sc.a) := by
    rw [hL2]
    have := mul_le_mul_of_nonneg_left hcl hprod0
    linarith
  have hB : (nP D p : ℝ) * (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) * Real.logb p L.sc.a ≤
      (nP D p : ℝ) * (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) * (Real.logb p (4 * (nP D p : ℝ) * Nm D * L.sc.a) + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hprod0
  have hD : K.dl1 * ((nP D p : ℝ) * (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) * Real.logb p L.sc.a) ≤
      K.dl1 * ((nP D p : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hprod hL2a (by linarith) (by positivity)) hC.dl1nn
  have hT2 : 0 ≤ K.dl2 * (topsOrb D p r : ℝ) * Real.logb p (2 * L.sc.a) ^ 2 := by
    have := hC.dl2; positivity
  nlinarith [hA, hB, hD, hT2]

end PI.OrbBoundFW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.SumWcLe
section
noncomputable section

open scoped BigOperators
open Classical
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.OrbitPlaces

namespace PI.OrbBoundFW

variable {D : D7} {L : SizeData₂ D}

theorem sum_Wc_le {X : Inst D L} {E : Ent D} (hS : Shape D L X E) {p : ℕ} [Fact p.Prime] (h : OrbOK D p)
    (u : D.what₂.Word) {i : ℕ} (hi : i < D.R.m) (z : Pl D)
    (Th : MvPowerSeries (ZMod (nP D p) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[p]) :
    ∑ s ∈ (orbLoc E p h u i z Th).TT, ((orbLoc E p h u i z Th).Wc s : ℝ) ≤
      (topsOrb D p z : ℝ) * (L.sc.b + L.etaSz + 1 + 3 * L.Sc) := by
  have hcap : ∀ s, (((orbLoc E p h u i z Th).cap s : ℕ) : ℝ) ≤ L.sc.b + L.etaSz + 1 + 3 * L.Sc := by
    intro s
    have hc := hS.capW u i hi (orbMap D p z s)
    unfold Formalism.MainNotions.OrbitPlaces.Ent.cap at hc
    unfold Formalism.MainNotions.product_zeroth_first_parts.Loc.cap
    by_cases ht : IsTopPl D (orbMap D p z s)
    · have hs : s ∈ (orbLoc E p h u i z Th).TT := Finset.mem_filter.2 ⟨Finset.mem_univ _, ht⟩
      rw [if_pos ht] at hc
      split_ifs
      exact hc
    · have hs : s ∉ (orbLoc E p h u i z Th).TT := fun hs => ht (Finset.mem_filter.1 hs).2
      rw [if_neg ht] at hc
      split_ifs
      exact hc
  have hB0 : 0 ≤ L.sc.b + L.etaSz + 1 + 3 * L.Sc := le_trans (Nat.cast_nonneg _) (hcap 0)
  have hW : ∀ s, (((orbLoc E p h u i z Th).Wc s : ℕ) : ℝ) ≤ L.sc.b + L.etaSz + 1 + 3 * L.Sc := by
    intro s
    have h1 : (orbLoc E p h u i z Th).Wc s ≤ ⌊L.sc.b + L.etaSz + 1 + 3 * L.Sc⌋₊ := by
      unfold Formalism.MainNotions.product_zeroth_first_parts.Loc.Wc
      apply csSup_le'
      rintro c ⟨j, -, -, rfl⟩
      exact Nat.le_floor (hcap _)
    exact (Nat.cast_le.2 h1).trans (Nat.floor_le hB0)
  calc ∑ s ∈ (orbLoc E p h u i z Th).TT, (((orbLoc E p h u i z Th).Wc s : ℕ) : ℝ)
      ≤ ∑ s ∈ (orbLoc E p h u i z Th).TT, (L.sc.b + L.etaSz + 1 + 3 * L.Sc) := Finset.sum_le_sum (fun s _ => hW s)
    _ = ((orbLoc E p h u i z Th).TT.card : ℝ) * (L.sc.b + L.etaSz + 1 + 3 * L.Sc) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = (topsOrb D p z : ℝ) * (L.sc.b + L.etaSz + 1 + 3 * L.Sc) := by
      unfold topsOrb
      rfl

end PI.OrbBoundFW
end
end

