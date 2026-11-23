module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0238
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellMulVecBasis
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermPartsCompactSupport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0239

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVRules
section
open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx3 Formalism.FourierDecayAlt.P.WeylCellAction

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section diff

variable {r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem pbOp_line {F₁ F₂ : (Fin r → ℂ) → E} {c : Fin r → ℂ} (l : Fin r) (h₁ : DifferentiableAt ℝ F₁ c)
    (h₂ : DifferentiableAt ℝ F₂ c) (h : ∀ c' : Fin r → ℂ, (∀ a, a ≠ l → c' a = c a) → F₁ c' = F₂ c') :
    pbOp l F₁ c = pbOp l F₂ c := by
  have hv : ∀ w : ℂ, fderiv ℝ F₁ c (Pi.single l w) = fderiv ℝ F₂ c (Pi.single l w) := fun w =>
    fderiv_line h₁ h₂ fun t => h _ fun a ha => by simp [ha]
  simp only [pbOp, wirtBar, hv]

end diff

theorem mirror_right_rule_holds : RightRuleEv := by
  intro E _ _ k r z' D f hz' hD hS hR g hg a b hab
  have ha := a.isLt
  have hc : Continuous fun x : Mx k r => g * x := cont_lmul g
  have hD' : IsOpen {x : Mx k r | g * x ∈ D} := hD.preimage hc
  have hS' : SmoothLev k r b.castSucc {x | g * x ∈ D} (fun x => f (g * x)) :=
    smooth_left g (fun x hx => glev0 hg.1 hx) hS
  have hR' : RightEq k r z' b.castSucc {x | g * x ∈ D} (fun x => f (g * x)) := by
    intro x hx n hn
    have := hR (g * x) ⟨glev0 hg.1 hx.1, hx.2⟩ n (nlev_mono (zero_le' _) hn)
    simpa [Matrix.mul_assoc] using this
  have h1 : (1 : Mx k r) ∈ Glev k r b.castSucc ∩ {x | g * x ∈ D} :=
    ⟨glev_one _, by simpa using hg.2⟩
  have hrule := (Formalism.FourierDecayAlt.P.right_action_rule E k r z' b {x | g * x ∈ D} (fun x => f (g * x)) hz' hD' hS' hR'
    1 h1).2.1
  have hjlt : 2 * r + k - a.val - b.val - 1 < mdim k r b.succ := by simp [mdim]; omega
  have hpos : posL k r b.succ ⟨2 * r + k - a.val - b.val - 1, hjlt⟩ = esI k r a := by
    simp [posL, esI, Fin.ext_iff]; omega
  have h := hrule ⟨2 * r + k - a.val - b.val - 1, hjlt⟩
  rw [hpos, eH_left, Matrix.mul_one] at h
  rw [h]
  congr 1
  simp only [xbv, fvec, hpos, Fin.val_succ]
  rw [dif_pos (show b.val + 1 < r by omega)]
  rw [Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_bvec_eI]
  by_cases hh : a.val = b.val + 1
  · simp [hh, bvec, esI]
  · rw [if_neg hh]
    simp only [bvec, Pi.single_apply, esI, Fin.ext_iff]
    rw [if_neg (by omega)]

theorem mirror_torus_cell_holds : TorusCellv := by
  intro E _ _ k r D f hD hS c hc g hg hWD l
  have hcne : ∀ a, c a ≠ 0 := hc
  have hl := l.isLt
  have hW0 : wCell k r l.castSucc c ∈ Glev k r 0 := wlist_glev hc _
  have htail : ∀ n : ℕ, ∀ i : Fin (r + 1), i.val = l.val + 1 + n →
      ∃ T : Mx k r, T ∈ Glev k r l.succ ∧
        ∀ c' : Fin r → ℂ, (∀ a : Fin r, l.val < a.val → c' a = c a) →
          wCell k r i c' = wCell k r l.succ c' * T := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have : i = l.succ := Fin.ext (by simpa using hi)
      subst i
      exact ⟨1, glev_one _, fun _ _ => by simp⟩
    | succ n ih =>
      intro i hi
      let j : Fin r := ⟨l.val + 1 + n, by have := i.isLt; omega⟩
      rw [show i = j.succ from Fin.ext (by simpa [j, Nat.add_assoc] using hi)]
      obtain ⟨T, hTG, hTc⟩ := ih j.castSucc (by simp [j])
      have hlj : l.val < j.val := by simp [j]; omega
      refine ⟨T * w1 k r j (c j), glev_mul hTG ?_, ?_⟩
      · exact glev_mono (by simpa [Fin.le_def] using hlj)
          (Formalism.FourierDecayAlt.P.weyl_level_element_properties k r j (c j) (hcne j)).1
      · intro c' hc'
        rw [Formalism.FourierDecayAlt.P.Qx6.wCell_succ, hTc c' hc', hc' j hlj, Matrix.mul_assoc]
  obtain ⟨T, hTG, hTc⟩ := htail (r - l.val - 1) (Fin.last r) (by simp; omega)
  have hT := hTc c (fun _ _ => rfl)
  have hg₁ : T * g ∈ Glev k r l.succ := glev_mul hTG (glev_mono (Fin.le_last _) hg)
  have hsplit : wCell k r (Fin.last r) c * g = wCell k r l.castSucc c * (w1 k r l (c l) * (T * g)) := by
    simp only [hT, Formalism.FourierDecayAlt.P.Qx6.wCell_succ, Matrix.mul_assoc]
  have hWx : ∀ x ∈ Glev k r l.castSucc, wCell k r l.castSucc c * x ∈ Glev k r 0 := fun x hx => glev0 hW0 hx
  have hS' := smooth_left (E := E) (f := f) (D := D) (wCell k r l.castSucc c) hWx hS
  have hD' : IsOpen {x : Mx k r | wCell k r l.castSucc c * x ∈ D} := hD.preimage (cont_lmul _)
  have hpt : w1 k r l (c l) * (T * g) ∈ {x | wCell k r l.castSucc c * x ∈ D} := by
    show _ ∈ D
    rw [← hsplit]; exact hWD
  have hrule := (Formalism.FourierDecayAlt.P.torus_action_rule E k r l {x | wCell k r l.castSucc c * x ∈ D}
    (fun x => f (wCell k r l.castSucc c * x)) hD' hS' c hc (T * g) hg₁ hpt).2
  rw [eH_left, ← hsplit] at hrule
  rw [hrule]
  have hd₂ : DifferentiableAt ℝ (fun c' => f (wCell k r (Fin.last r) c' * g)) c := by
    refine diff_comp hS (φ := fun c' => wCell k r (Fin.last r) c' * g)
      (cdo_mul (wlist_smooth _) contDiffOn_const)
      (fun _ hc' => glev_mul (wlist_glev hc' _) (glev_mono (zero_le' _) hg)) hc hWD
  have hd₁ : DifferentiableAt ℝ (fun c' => f (wCell k r l.castSucc c * (w1 k r l (c' l) * (T * g)))) c := by
    refine diff_comp hS (φ := fun c' => wCell k r l.castSucc c * (w1 k r l (c' l) * (T * g)))
      (Formalism.FourierDecayAlt.P.Qx6.cd_matmul contDiffOn_const
        (Formalism.FourierDecayAlt.P.Qx6.cd_matmul (Formalism.FourierDecayAlt.P.Qx6.contDiffOn_weyl_cell l) contDiffOn_const)) (fun c' hc' => ?_) hc ?_
    · refine glev_mul hW0 (glev_mul (glev_mono (zero_le' _) (Formalism.FourierDecayAlt.P.weyl_level_element_properties k r l (c' l) (hc' l)).1)
        (glev_mono (zero_le' _) hg₁))
    · rw [← hsplit]; exact hWD
  congr 1
  refine pbOp_line l hd₁ hd₂ fun c' hc' => ?_
  have hlow : wCell k r l.castSucc c' = wCell k r l.castSucc c :=
    Formalism.FourierDecayAlt.P.Qx6.wCell_congr fun a ha => hc' a (fun h => by subst h; simp at ha)
  have hup := hTc c' fun a ha => hc' a (fun h => by subst h; omega)
  show f (wCell k r l.castSucc c * (w1 k r l (c' l) * (T * g))) = f (wCell k r (Fin.last r) c' * g)
  rw [hup, Formalism.FourierDecayAlt.P.Qx6.wCell_succ, hlow, Matrix.mul_assoc, Matrix.mul_assoc]

theorem herm_smul_right' {k r : ℕ} (v w : Fin (2 * r + k + 1) → ℂ) (s : ℂ) :
    herm (Hpk k r) v (s • w) = star s * herm (Hpk k r) v w := by
  unfold herm
  rw [star_smul, smul_dotProduct, smul_eq_mul]

theorem mirror_left_rule_cell_holds : LeftRuleCellv := by
  intro E _ _ k r z D f hz hD hDN hS hL c hc g hg hWD a b hba
  have ha := a.isLt
  have hcne : ∀ l, c l ≠ 0 := hc
  have hW0 : wCell k r b.castSucc c ∈ Glev k r 0 := wlist_glev hc _
  have hWcomm (n : Mx k r) (hn : n ∈ Glev k r b.castSucc) :
      wCell k r b.castSucc c * n = n * wCell k r b.castSucc c :=
    wlist_comm b.castSucc c _ (fun _ ha => of_decide_eq_true (List.mem_filter.mp ha).2) hn
  have htail : ∀ n : ℕ, ∀ i : Fin (r + 1), i.val = b.val + 1 + n →
      ∃ T : Mx k r, wCell k r i c = wCell k r b.succ c * T ∧ T ∈ Glev k r b.succ ∧
        (∀ a : Fin r, b.val < a.val →
          T *ᵥ bvec (eI k r a) = if a.val < i.val then c a • bvec (esI k r a) else bvec (eI k r a)) ∧
        (∀ a : Fin r, i.val ≤ a.val → T *ᵥ bvec (esI k r a) = bvec (esI k r a)) := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have : i = b.succ := Fin.ext (by simpa using hi)
      subst i
      refine ⟨1, by simp, glev_one _, fun a ha => ?_, fun _ _ => by simp⟩
      rw [ite_eq_right (by simp; omega), Matrix.one_mulVec]
    | succ n ih =>
      intro i hi
      let j : Fin r := ⟨b.val + 1 + n, by have := i.isLt; omega⟩
      rw [show i = j.succ from Fin.ext (by simpa [j, Nat.add_assoc] using hi)]
      obtain ⟨T, hT, hTG, hTe, hTs⟩ := ih j.castSucc (by simp [j])
      have hbj : b.val + 1 ≤ j.val := by simp [j]
      refine ⟨T * w1 k r j (c j), ?_, glev_mul hTG ?_, ?_, ?_⟩
      · rw [Formalism.FourierDecayAlt.P.Qx6.wCell_succ, hT, Matrix.mul_assoc]
      · exact glev_mono (by simpa [Fin.le_def] using hbj)
          (Formalism.FourierDecayAlt.P.weyl_level_element_properties k r j (c j) (hcne j)).1
      · intro a ha
        rw [← Matrix.mulVec_mulVec, weyl_cell_mulVec_basis]
        by_cases haj : a = j
        · subst a
          rw [sw_e, dd_e, Matrix.mulVec_smul, hTs _ (by simp), ite_eq_left (by simp)]
        · have hne : a.val ≠ j.val := fun h => haj (Fin.ext h)
          have h₁ : eI k r a ≠ eI k r j := by simpa [eI, Fin.ext_iff] using hne
          have h₂ : eI k r a ≠ esI k r j := by simp [eI, esI, Fin.ext_iff]; have := j.isLt; omega
          have hlt : a.val < j.castSucc.val ↔ a.val < j.succ.val := by simp; omega
          rw [sw_o j h₁ h₂, dd_o j _ h₁ h₂, one_smul, hTe a ha]
          simp only [hlt]
      · intro a ha
        have h₁ : esI k r a ≠ eI k r j := by simp [eI, esI, Fin.ext_iff]; have := a.isLt; omega
        have h₂ : esI k r a ≠ esI k r j := by
          have ha' := a.isLt
          have hja : j.val < a.val := ha
          intro h
          have hv := congrArg Fin.val h
          change 2 * r + k - a.val = 2 * r + k - j.val at hv
          omega
        rw [← Matrix.mulVec_mulVec, weyl_cell_mulVec_basis, sw_o j h₁ h₂, dd_o j _ h₁ h₂, one_smul,
          hTs a (by simp at ha ⊢; omega)]
  obtain ⟨T, hT, hTG, hTe, -⟩ := htail (r - b.val - 1) (Fin.last r) (by simp; omega)
  have hg₁ : T * g ∈ Glev k r b.succ := glev_mul hTG (glev_mono (Fin.le_last _) hg)
  have hsplit : wCell k r (Fin.last r) c * g = wCell k r b.castSucc c * (w1 k r b (c b) * (T * g)) := by
    simp only [hT, Formalism.FourierDecayAlt.P.Qx6.wCell_succ, Matrix.mul_assoc]
  have hWx : ∀ x ∈ Glev k r b.castSucc, wCell k r b.castSucc c * x ∈ Glev k r 0 := fun x hx => glev0 hW0 hx
  have hS' := smooth_left (E := E) (f := f) (D := D) (wCell k r b.castSucc c) hWx hS
  have hcont : Continuous fun x : Mx k r => wCell k r b.castSucc c * x := cont_lmul _
  have hD' : IsOpen {x : Mx k r | wCell k r b.castSucc c * x ∈ D} := hD.preimage hcont
  have hN' : ∀ x ∈ Glev k r b.castSucc ∩ {x | wCell k r b.castSucc c * x ∈ D}, ∀ n ∈ Nlev k r b.castSucc,
      n * x ∈ {x | wCell k r b.castSucc c * x ∈ D} := by
    intro x hx n hn
    show wCell k r b.castSucc c * (n * x) ∈ D
    rw [← Matrix.mul_assoc, hWcomm n hn.2, Matrix.mul_assoc]
    exact hDN _ ⟨hWx x hx.1, hx.2⟩ n (nlev_mono (zero_le' _) hn)
  have hL' : LeftEq k r z b.castSucc {x | wCell k r b.castSucc c * x ∈ D} (fun x => f (wCell k r b.castSucc c * x)) := by
    intro x hx n hn
    show f (wCell k r b.castSucc c * (n * x)) = _ • f (wCell k r b.castSucc c * x)
    rw [← Matrix.mul_assoc, hWcomm n hn.2, Matrix.mul_assoc]
    exact hL _ ⟨hWx x hx.1, hx.2⟩ n (nlev_mono (zero_le' _) hn)
  have hpt : w1 k r b (c b) * (T * g) ∈ {x | wCell k r b.castSucc c * x ∈ D} := by
    show _ ∈ D
    rw [← hsplit]; exact hWD
  have hrule := (Formalism.FourierDecayAlt.P.left_action_rule E k r z b {x | wCell k r b.castSucc c * x ∈ D}
    (fun x => f (wCell k r b.castSucc c * x)) hz hD' hS' hN' hL' (c b) (hcne b) (T * g) hg₁ hpt).2.1
  have hjlt : 2 * r + k - a.val - b.val - 1 < mdim k r b.succ := by simp [mdim]; omega
  have hpos : posL k r b.succ ⟨2 * r + k - a.val - b.val - 1, hjlt⟩ = esI k r a := by
    simp [posL, esI, Fin.ext_iff]; omega
  have h := hrule ⟨2 * r + k - a.val - b.val - 1, hjlt⟩
  rw [hpos, eH_left, ← hsplit] at h
  rw [h]
  congr 1
  have hb1 : (b.succ : Fin (r + 1)).val < r := by simp; omega
  have hga : g *ᵥ bvec (eI k r a) = bvec (eI k r a) := (hg.2 a (by simp)).1
  have hTa := hTe a hba
  rw [if_pos (by simp)] at hTa
  have hU : T * g ∈ UH (Hpk k r) := hg₁.1
  have key : ((T * g)⁻¹ *ᵥ bvec (eI k r ⟨b.val + 1, by omega⟩)) (esI k r a) =
      if a.val = b.val + 1 then star (c a) else 0 := by
    rw [← Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_bvec_eI ((T * g)⁻¹ *ᵥ bvec (eI k r ⟨b.val + 1, by omega⟩)) a,
      ← Formalism.FourierDecayAlt.P.Qx2.herm_uh hU, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hU), Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hga, hTa,
      herm_smul_right', ← Formalism.FourierDecayAlt.P.Qx2.herm_star, Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_bvec_eI]
    by_cases hh : a.val = b.val + 1
    · rw [if_pos hh]
      have : (bvec (esI k r a) : Fin (2 * r + k + 1) → ℂ) (esI k r ⟨b.val + 1, by omega⟩) = 1 := by
        simp [bvec, esI, hh]
      rw [this, star_one, mul_one]
    · rw [if_neg hh]
      have : (bvec (esI k r a) : Fin (2 * r + k + 1) → ℂ) (esI k r ⟨b.val + 1, by omega⟩) = 0 := by
        simp only [bvec, Pi.single_apply, esI, Fin.ext_iff]
        rw [if_neg (by omega)]
      rw [this, star_zero, mul_zero]
  have hy : yv k r z b.succ (T * g) ⟨2 * r + k - a.val - b.val - 1, hjlt⟩ =
      if a.val = b.val + 1 then star (c a) else 0 := by
    simp only [yv, hpos, fvec, dif_pos hb1]
    exact key
  rw [hy]
  by_cases hh : a.val = b.val + 1
  · rw [if_pos hh, if_pos hh, div_eq_inv_mul]
  · rw [if_neg hh, if_neg hh, mul_zero]

end Formalism.FourierDecayAlt.P.CutMP.TVG
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.EntrywiseClassWordTransfer
section
open MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.LevelPointCoordinates

section pr

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X]
  [BorelSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (ℓ : X → E →L[ℂ] E)

def PG (x : Q.Pr (V1 E)) : Prop := OK μ ℓ x.1 ∧ OK μ ℓ x.2.unop

variable {μ ℓ}

theorem pg_zero : PG μ ℓ (0 : Q.Pr (V1 E)) := ⟨ok_zero, ok_zero⟩

theorem pg_one : PG μ ℓ (1 : Q.Pr (V1 E)) := ⟨ok_one, ok_one⟩

theorem pg_add (hℓ : Continuous ℓ) {x y : Q.Pr (V1 E)} (hx : PG μ ℓ x) (hy : PG μ ℓ y) : PG μ ℓ (x + y) :=
  ⟨ok_add hℓ hx.1 hy.1, ok_add hℓ hx.2 hy.2⟩

theorem pg_mul {x y : Q.Pr (V1 E)} (hx : PG μ ℓ x) (hy : PG μ ℓ y) : PG μ ℓ (x * y) :=
  ⟨ok_mul hx.1 hy.1, ok_mul hy.2 hx.2⟩

theorem pg_neg {x : Q.Pr (V1 E)} (hx : PG μ ℓ x) : PG μ ℓ (-x) := ⟨ok_neg hx.1, ok_neg hx.2⟩

theorem pg_star {x : Q.Pr (V1 E)} (hx : PG μ ℓ x) : PG μ ℓ (star x) := ⟨hx.2, hx.1⟩

theorem pg_alg (c : ℂ) : PG μ ℓ (algebraMap ℂ (Q.Pr (V1 E)) c) := ⟨ok_alg c, ok_alg (conj c)⟩

theorem pg_sum (hℓ : Continuous ℓ) {ι : Type*} (s : Finset ι) (f : ι → Q.Pr (V1 E)) (h : ∀ i ∈ s, PG μ ℓ (f i)) :
    PG μ ℓ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (pg_zero : PG μ ℓ (0 : Q.Pr (V1 E)))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact pg_add hℓ (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

variable {S : Type} [Fintype S] [DecidableEq S]


variable (μ ℓ) in
def EntrywiseClass (M : Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E))) : Prop := ∀ a b, PG μ ℓ (M a b)

theorem entrywise_class_mul (hℓ : Continuous ℓ) {M N : Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E))} (hM : EntrywiseClass μ ℓ M) (hN : EntrywiseClass μ ℓ N) :
    EntrywiseClass μ ℓ (M * N) := fun a b => by
  rw [Matrix.mul_apply]
  exact pg_sum hℓ _ _ fun c _ => pg_mul (hM a c) (hN c b)

theorem entrywise_class_sum (hℓ : Continuous ℓ) {ι : Type*} (s : Finset ι) (M : ι → Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E)))
    (h : ∀ i ∈ s, EntrywiseClass μ ℓ (M i)) : EntrywiseClass μ ℓ (∑ i ∈ s, M i) := fun a b => by
  rw [Matrix.sum_apply]
  exact pg_sum hℓ _ _ fun i hi => h i hi a b

theorem entrywise_class_one : EntrywiseClass μ ℓ (1 : Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E))) := fun a b => by
  rw [Matrix.one_apply]
  split_ifs
  · exact pg_one
  · exact pg_zero

theorem entrywise_class_unit_matrix (a : S) (i j : Fin 2) : EntrywiseClass μ ℓ (Wd.eU a i j : Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E))) := fun x y => by
  unfold Wd.eU
  rw [Matrix.of_apply]
  split_ifs
  · exact pg_one
  · exact pg_zero

theorem entrywise_class_scalar {x : Q.Pr (V1 E)} (hx : PG μ ℓ x) : EntrywiseClass μ ℓ (Wd.io x : Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E))) := fun a b => by
  unfold Wd.io
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact hx
  · exact pg_zero

theorem entrywise_class_insert (hℓ : Continuous ℓ) (a : S) {M : Wd.M2 (Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E)))} (hM : ∀ i j, EntrywiseClass μ ℓ (M i j)) :
    EntrywiseClass μ ℓ (Wd.ins a M) := by
  unfold Wd.ins
  exact entrywise_class_sum hℓ _ _ fun i _ => entrywise_class_sum hℓ _ _ fun j _ => entrywise_class_mul hℓ (entrywise_class_unit_matrix a i j) (hM i j)

theorem pg_Ts (hℓ : Continuous ℓ) (σ : Wd.Site (Q.Pr (V1 E))) (hp : PG μ ℓ σ.p) (hc : PG μ ℓ σ.c)
    (hci : PG μ ℓ σ.ci) (Y : ℂ) : ∀ i j, PG μ ℓ (Wd.Ts σ Y i j) := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact pg_add hℓ (pg_alg Y) hp
  · exact pg_neg hc
  · exact hci
  · exact pg_zero

theorem entrywise_class_letter (hℓ : Continuous ℓ) (σ : Wd.Site (Q.Pr (V1 E))) (hp : PG μ ℓ σ.p) (hc : PG μ ℓ σ.c)
    (hci : PG μ ℓ σ.ci) (l : Wd.Letter ℂ S) : EntrywiseClass μ ℓ (Wd.vlet σ l) := by
  unfold Wd.vlet
  refine entrywise_class_insert hℓ _ fun i j => ?_
  unfold Wd.lift0
  rw [Matrix.map_apply]
  refine entrywise_class_scalar ?_
  split_ifs
  · exact pg_Ts hℓ σ hp hc hci _ i j
  · rw [Matrix.map_apply]
    exact pg_star (pg_Ts hℓ σ hp hc hci _ i j)

theorem entrywise_class_word_transfer (hℓ : Continuous ℓ) (σ : Wd.Site (Q.Pr (V1 E))) (hp : PG μ ℓ σ.p) (hc : PG μ ℓ σ.c)
    (hci : PG μ ℓ σ.ci) : ∀ w : List (Wd.Letter ℂ S), EntrywiseClass μ ℓ (Wd.bT σ w)
  | [] => by rw [Wd.bT]; exact entrywise_class_one
  | l :: w => by
      rw [Wd.bT]
      exact entrywise_class_mul hℓ (entrywise_class_letter hℓ σ hp hc hci l) (entrywise_class_word_transfer hℓ σ hp hc hci w)

theorem entrywise_class_site_one (hℓ : Continuous ℓ) (κ : ℂ) (w : List (Wd.Letter ℂ S)) :
    EntrywiseClass μ ℓ (Wd.bT (site1 (E := E) κ) w) :=
  entrywise_class_word_transfer hℓ _ ⟨ok_opP hℓ κ, ok_neg (ok_opPb hℓ κ)⟩ ⟨ok_opM _ cd_id, ok_opM _ cd_conj⟩
    ⟨ok_opM _ cd_inv, ok_opM _ cd_conjinv⟩ w

theorem oneBT_int (hℓ : Continuous ℓ) (κ : ℂ) (w : List (Wd.Letter ℂ S)) (Φ : X → Wd.Ix S → V1 E)
    (x : Wd.Ix S → V1 E) (hG : ∀ b, Good (fun v => Φ v b)) (hI : ∀ b, IsInt μ ℓ (fun v => Φ v b) (x b))
    (a : Wd.Ix S) :
    Good (fun v => oneBT κ w (Φ v) a) ∧ IsInt μ ℓ (fun v => oneBT κ w (Φ v) a) (oneBT κ w x a) := by
  have hB := entrywise_class_site_one (μ := μ) (ℓ := ℓ) hℓ κ w
  unfold oneBT act1
  exact ⟨good_sum _ _ fun b _ => ((hB a b).1 _ _ (hG b) (hI b)).1,
    int_sum hℓ _ _ _ (fun b _ => ((hB a b).1 _ _ (hG b) (hI b)).1) fun b _ => ((hB a b).1 _ _ (hG b) (hI b)).2⟩

end pr

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRateSplit
section
namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBK Formalism.FourierDecayAlt.P.GermRealisation Formalism.FourierDecayAlt.P.GermFibreKernels Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def GermRateLow (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Prop :=
  ∀ ε, 0 < ε → ∀ b s, 1 ≤ b → 2 ≤ s → b + s ≤ S.G.r + 1 → ∀ a, D.AdmAt S v a →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Vec : C.LPt → H),
    (∀ P Q, KB.gN S v ε (b + s - 1) a P Q = ⟪Vec P, Vec Q⟫_ℂ) →
    ∃ (ε' : ℂ) (φ : ℂ → ℂ), ‖ε'‖ = 1 ∧ (∀ z, ‖φ z‖ = 1) ∧ ContinuousOn φ {0}ᶜ ∧
      ∀ h : C.LPt, D.ptSize h = b - 1 → ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 → ∀ D ∈ K,
        ‖utOf s (vOf (KB.dlB S (b + s - 1) 1) Vec) h x D -
          mainD s (betaL S) ε' (fun z => φ z • btOf s (KB.dlB S b s) Vec h z) x D‖ ≤ C * ‖x‖⁻¹

def GermRateTop (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Prop :=
  ∀ ε, 0 < ε → ∀ b s, 1 ≤ b → 2 ≤ s → b + s = S.G.r + 2 → ∀ a, D.AdmAt S v a →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Vec : C.LPt → H),
    (∀ P Q, KB.gN S v ε (b + s - 1) a P Q = ⟪Vec P, Vec Q⟫_ℂ) →
    ∃ (ε' : ℂ) (φ : ℂ → ℂ), ‖ε'‖ = 1 ∧ (∀ z, ‖φ z‖ = 1) ∧ ContinuousOn φ {0}ᶜ ∧
      ∀ h : C.LPt, D.ptSize h = b - 1 → ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 → ∀ D ∈ K,
        ‖utOf s (vOf (KB.dlB S (b + s - 1) 1) Vec) h x D -
          mainD s (betaL S) ε' (fun z => φ z • btOf s (KB.dlB S b s) Vec h z) x D‖ ≤ C * ‖x‖⁻¹

theorem germRate_of (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (hL : GermRateLow S v) (hT : GermRateTop S v) :
    GermRate S v := by
  intro ε hε b s hb hs hbs
  rcases Nat.lt_or_ge (b + s) (S.G.r + 2) with h | h
  · exact hL ε hε b s hb hs (by omega)
  · exact hT ε hε b s hb hs (by omega)

end loc

def GermRateLowB : Prop :=
  P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ → ∀ n v, GermRateLow (PBL.setC S p (PBASM.cutSeq S p f χ n)) v

def GermRateTopB : Prop :=
  P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ → ∀ n v, GermRateTop (PBL.setC S p (PBASM.cutSeq S p f χ n)) v

theorem germRateB_of (hL : GermRateLowB) (hT : GermRateTopB) : GermRateB := by
  intro hA Cb
  obtain ⟨c1, h1⟩ := hL hA Cb
  obtain ⟨c2, h2⟩ := hT hA Cb
  refine ⟨max c1 c2, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB n v
  exact germRate_of _ v (h1 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place (le_max_left _ _) hB) n v)
    (h2 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place (le_max_right _ _) hB) n v)

end

end Formalism.FourierDecayAlt.P.GermRateSplit

theorem Formalism.FourierDecayAlt.P.germ_rate_bound_of_split :
    Formalism.FourierDecayAlt.P.GermRateSplit.GermRateLowB → Formalism.FourierDecayAlt.P.GermRateSplit.GermRateTopB → Formalism.FourierDecayAlt.P.GermFibreKernels.GermRateB :=
  Formalism.FourierDecayAlt.P.GermRateSplit.germRateB_of
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.UniformDecayOfParts
section
noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.FourierDecayAlt

def DecayUnifOfHeads : Prop := KB.RadHead → KB.HeadTop → DecayUnif

theorem decayUnifOfHeads : DecayUnifOfHeads := fun hRH hHT =>
  decayUnif_of hRH hHT Formalism.FourierDecayAlt.P.wave_difference_form

end Formalism.FourierDecayAlt.P.PBO

theorem Formalism.FourierDecayAlt.P.uniform_decay_of_heads : Formalism.FourierDecayAlt.P.PBO.DecayUnifOfHeads := Formalism.FourierDecayAlt.P.PBO.decayUnifOfHeads
end
end

