module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0199
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FourTermExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FiniteSumLocalExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0197
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GroupEquationsPostHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieDecompositionLocal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCoef
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace TVCoefPf

variable {k r : ℕ}

theorem castLE_self (h : r ≤ r) (a : Fin r) : Fin.castLE h a = a := Fin.ext rfl

theorem esI_inj (a b : Fin r) : esI k r a = esI k r b ↔ a = b := by
  have := a.isLt
  have := b.isLt
  constructor
  · intro h
    apply Fin.ext
    have h' := congrArg Fin.val h
    simp only [esI] at h'
    omega
  · intro h; rw [h]

theorem keyS_esI (a : Fin r) : C3.keyS k r (esI k r a) = a.val := by
  have := a.isLt
  unfold C3.keyS esI
  simp only
  split_ifs with h <;> omega

theorem w1_mulVec_bvec_esI (l : Fin r) (s : ℂ) : Q.w1 k r l s *ᵥ bvec (esI k r l) = (star s)⁻¹ • bvec (eI k r l) := by
  funext p
  simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  rw [Formalism.FourierDecayAlt.P.Qx3.w1_apply, Formalism.FourierDecayAlt.P.Qx3.sw_es, Formalism.FourierDecayAlt.P.Qx3.dd_es]
  split_ifs <;> simp

theorem ne_of_ne {a b : Fin r} (hab : ¬ a = b) {q : Fin (2 * r + k + 1)} (hq : q = eI k r a ∨ q = esI k r a) :
    q ≠ eI k r b ∧ q ≠ esI k r b := by
  have h1 : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have := a.isLt
  have := b.isLt
  rcases hq with rfl | rfl
  · constructor <;> intro h <;> have h' := congrArg Fin.val h <;> simp only [eI, esI] at h' <;> omega
  · constructor <;> intro h <;> have h' := congrArg Fin.val h <;> simp only [eI, esI] at h' <;> omega

theorem wlist_fix (c : Fin r → ℂ) (a : Fin r) {q : Fin (2 * r + k + 1)} (hq : q = eI k r a ∨ q = esI k r a) :
    ∀ L : List (Fin r), a ∉ L → (L.map fun b => Q.w1 k r b (c b)).prod *ᵥ bvec q = bvec q := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons b L ih =>
    intro ha
    rw [List.mem_cons, not_or] at ha
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih ha.2]
    obtain ⟨h1, h2⟩ := ne_of_ne ha.1 hq
    exact Formalism.FourierDecayAlt.P.Qx3.reflection_fixes_basis_vector b (c b) h1 h2

theorem wlist_main {c : Fin r → ℂ} (hc : c ∈ OmX r) (a : Fin r) :
    ∀ L : List (Fin r), L.Nodup → a ∈ L →
      (L.map fun b => Q.w1 k r b (c b)).prod *ᵥ (star (c a) • bvec (esI k r a)) = bvec (eI k r a) := by
  have hc' : ∀ l, c l ≠ 0 := hc
  intro L
  induction L with
  | nil => intro _ h; simp at h
  | cons b L ih =>
    intro hnd ha
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec]
    by_cases hab : b = a
    · subst hab
      rw [Matrix.mulVec_smul, wlist_fix c b (Or.inr rfl) L hnd.1, Matrix.mulVec_smul, w1_mulVec_bvec_esI, smul_smul,
        mul_inv_cancel₀ (star_ne_zero.2 (hc' b)), one_smul]
    · have haL : a ∈ L := by
        rcases List.mem_cons.1 ha with h | h
        · exact absurd h.symm hab
        · exact h
      rw [ih hnd.2 haL]
      obtain ⟨h1, h2⟩ := ne_of_ne (fun h => hab h.symm) (Or.inl rfl)
      exact Formalism.FourierDecayAlt.P.Qx3.reflection_fixes_basis_vector b (c b) h1 h2

theorem wcell_es {c : Fin r → ℂ} (hc : c ∈ OmX r) (a : Fin r) :
    Q.wCell k r (Fin.last r) c *ᵥ (star (c a) • bvec (esI k r a)) = bvec (eI k r a) := by
  unfold Q.wCell
  refine wlist_main hc a _ ((List.nodup_finRange r).filter _) ?_
  rw [List.mem_filter]
  exact ⟨List.mem_finRange a, by simp⟩

theorem inv_e {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r)) (a : Fin r) :
    (Q.wCell k r (Fin.last r) c * g)⁻¹ *ᵥ bvec (eI k r a) = star (c a) • bvec (esI k r a) := by
  have hW : Q.wCell k r (Fin.last r) c ∈ Q.Glev k r 0 := Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _
  have hu : IsUnit (Q.wCell k r (Fin.last r) c * g).det := by
    rw [Matrix.det_mul]
    exact (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hW.1).mul (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg.1)
  have ha : a.val < (Fin.last r).val := by rw [Fin.val_last]; exact a.isLt
  have hv : (Q.wCell k r (Fin.last r) c * g) *ᵥ (star (c a) • bvec (esI k r a)) = bvec (eI k r a) := by
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_smul, (hg.2 a ha).2]
    exact wcell_es hc a
  rw [← hv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

theorem det_entry {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r))
    (B : Fin r → Fin (2 * r + k + 1)) :
    (Matrix.of fun a l : Fin r =>
        ((Q.wCell k r (Fin.last r) c * g)⁻¹ *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) (B l)) =
      Matrix.of fun a l : Fin r => star (c a) * (if B l = esI k r a then (1 : ℂ) else 0) := by
  ext a l
  simp only [Matrix.of_apply]
  rw [castLE_self, inv_e hc hg a]
  simp [bvec, Pi.single_apply]

theorem sm_ge {n : ℕ} {τ : Fin n → Fin n} (h : StrictMono τ) : ∀ m (j : Fin n), j.val = m → m ≤ (τ j).val := by
  intro m
  induction m with
  | zero => intro j _; omega
  | succ m ih =>
    intro j hj
    have hm : m < n := by have := j.isLt; omega
    have h1 := ih ⟨m, hm⟩ rfl
    have h2 : τ ⟨m, hm⟩ < τ j := h (by rw [Fin.lt_def]; simp only; omega)
    rw [Fin.lt_def] at h2
    omega

theorem sm_eq_id {n : ℕ} {τ : Fin n → Fin n} (h : StrictMono τ) : τ = id := by
  have hρ : StrictMono fun j : Fin n => Fin.rev (τ (Fin.rev j)) := by
    intro a b hab
    rw [Fin.rev_lt_rev]
    exact h (Fin.rev_lt_rev.2 hab)
  funext j
  apply Fin.ext
  have e1 := sm_ge h j.val j rfl
  have e2 := sm_ge hρ (Fin.rev j).val (Fin.rev j) rfl
  simp only [Fin.rev_rev, Fin.val_rev] at e2
  have := j.isLt
  have := (τ j).isLt
  simp only [id]
  omega

theorem det_zero {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r))
    (B : Fin r → Fin (2 * r + k + 1)) (hm : StrictMono fun l => C3.keyS k r (B l)) (hB : B ≠ C3.sR k r r le_rfl) :
    (Matrix.of fun a l : Fin r =>
        ((Q.wCell k r (Fin.last r) c * g)⁻¹ *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) (B l)).det = 0 := by
  rw [det_entry hc hg B]
  by_cases hcol : ∃ l, ∀ a, B l ≠ esI k r a
  · obtain ⟨l, hl⟩ := hcol
    exact Matrix.det_eq_zero_of_column_eq_zero l (fun a => by simp [hl a])
  · push Not at hcol
    choose τ hτ using hcol
    have hτm : StrictMono τ := by
      intro a b hab
      have := hm hab
      simp only [hτ, keyS_esI] at this
      exact Fin.lt_def.2 this
    have hid := sm_eq_id hτm
    exact absurd (funext fun l => by rw [hτ l, hid]; rfl) hB

theorem det_sR {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r)) :
    (Matrix.of fun a l : Fin r =>
        ((Q.wCell k r (Fin.last r) c * g)⁻¹ *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) (C3.sR k r r le_rfl l)).det =
      drbF r c := by
  rw [det_entry hc hg]
  have e : (Matrix.of fun a l : Fin r => star (c a) * (if C3.sR k r r le_rfl l = esI k r a then (1 : ℂ) else 0)) =
      Matrix.diagonal fun a => star (c a) := by
    ext a l
    simp only [Matrix.of_apply, Matrix.diagonal_apply, C3.sR, castLE_self, esI_inj]
    by_cases h : a = l
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [e, Matrix.det_diagonal]
  simp [drbF, map_prod]

theorem colsVm_eq : colsVm k r r = C3.sR k r r le_rfl ∘ Fin.revPerm := by
  funext j
  apply Fin.ext
  have := j.isLt
  simp [colsVm, C3.sR, esI, Fin.val_rev]
  omega

theorem kv_rev {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {x : Q.Mx k r} (hx : x ∈ B.GV k r)
    {J : Q.Mx k r → E} (hloc : Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc ((r : ℕ) : ℕ∞) J x) (w : ℂ) :
    kvM k r r w J x = qminorOp (Q.EH k r) (C3.sR k r r le_rfl) (C3.sR k r r le_rfl) w J x := by
  unfold kvM
  rw [colsVm_eq, Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.skewRow, Formalism.FourierDecayAlt.P.FourTermExpansion.skewCol (C3.sR k r r le_rfl) w J x hx hloc, smul_smul,
    ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one, one_smul]

theorem coef_gen {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {c : Fin r → ℂ} (hc : c ∈ OmX r)
    {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r)) (hx : Q.wCell k r (Fin.last r) c * g ∈ B.GV k r)
    {J : Q.Mx k r → E} (hloc : Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc ((r : ℕ) : ℕ∞) J (Q.wCell k r (Fin.last r) c * g)) (y : ℂ) :
    capAv k r y J (Q.wCell k r (Fin.last r) c * g) =
      drbF r c • kvM k r r (kvTop k r y) J (Q.wCell k r (Fin.last r) c * g) := by
  rw [kv_rev hx hloc, ← det_sR hc hg]
  simp only [capAv, C3.AAvop]
  rw [Fintype.sum_eq_single (C3.sR k r r le_rfl)]
  · have hmono : StrictMono fun l => C3.keyS k r (C3.sR k r r le_rfl l) := by
      intro a b hab
      simp only [C3.sR, castLE_self, keyS_esI]
      exact hab
    rw [if_pos hmono]
    rfl
  · intro B hB
    split_ifs with hm
    · rw [det_zero hc hg B hm hB, zero_smul]
    · rfl

end TVCoefPf

theorem toda_coefficient_holds : TVCoef := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk y J hJ c hc g hg hcg
  obtain ⟨hGV, hCk⟩ := capa_J_ck P Bs hJ hc hg hcg ((P.r : ℕ) : ℕ∞)
  exact TVCoefPf.coef_gen hc hg hGV (hCk _ (Set.mem_singleton _)) y

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCrdAlg
section
noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVCrdAlg

variable {R : Type*} [Ring R]

def cont (D e : ℕ → R) (a : ℕ) : ℕ → R
  | 0 => 1
  | 1 => D a
  | n + 2 => D (a + n + 1) * cont D e a (n + 1) - e (a + n + 1) * cont D e a n

theorem cont_zero (D e : ℕ → R) (a : ℕ) : cont D e a 0 = 1 := rfl

theorem cont_one (D e : ℕ → R) (a : ℕ) : cont D e a 1 = D a := rfl

theorem cont_two (D e : ℕ → R) (a n : ℕ) :
    cont D e a (n + 2) = D (a + n + 1) * cont D e a (n + 1) - e (a + n + 1) * cont D e a n := rfl

theorem cont_top (D e : ℕ → R) (hDe : ∀ i j, i + 1 ≤ j → D j * e i = e i * D j)
    (hee : ∀ i j, e i * e j = e j * e i) :
    ∀ n a, cont D e a (n + 2) = cont D e (a + 1) (n + 1) * D a - e (a + 1) * cont D e (a + 2) n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    intro a
    rfl
  | one =>
    intro a
    change D (a + 2) * (D (a + 1) * D a - e (a + 1) * 1) - e (a + 2) * D a =
      (D (a + 2) * D (a + 1) - e (a + 2) * 1) * D a - e (a + 1) * D (a + 2)
    have hc := hDe (a + 1) (a + 2) (by omega)
    simp only [mul_one, mul_sub, sub_mul, ← mul_assoc, hc]
    abel
  | more n ih0 ih1 =>
    intro a
    have eA : cont D e a (n + 2 + 2) =
        D (a + n + 3) * cont D e a (n + 1 + 2) - e (a + n + 3) * cont D e a (n + 2) := rfl
    have eB : cont D e (a + 1) (n + 2 + 1) =
        D (a + n + 3) * cont D e (a + 1) (n + 2) - e (a + n + 3) * cont D e (a + 1) (n + 1) := by
      rw [show n + 2 + 1 = (n + 1) + 2 by omega, cont_two, show a + 1 + (n + 1) + 1 = a + n + 3 by omega]
    have eC : cont D e (a + 2) (n + 2) =
        D (a + n + 3) * cont D e (a + 2) (n + 1) - e (a + n + 3) * cont D e (a + 2) n := by
      rw [cont_two, show a + 2 + n + 1 = a + n + 3 by omega]
    rw [eA, eB, eC, ih1 a, ih0 a]
    have hc1 := hDe (a + 1) (a + n + 3) (by omega)
    have hc2 := hee (a + n + 3) (a + 1)
    simp only [mul_sub, sub_mul, ← mul_assoc, hc1, hc2]
    abel

def topK (Dt e : ℕ → R) (r : ℕ) : ℕ → R × R
  | 0 => (1, 0)
  | m + 1 => ((topK Dt e r m).1 * Dt m - e (r - m) * (topK Dt e r m).2, (topK Dt e r m).1)

theorem topK_eq (D e : ℕ → R) (hDe : ∀ i j, i + 1 ≤ j → D j * e i = e i * D j)
    (hee : ∀ i j, e i * e j = e j * e i) (r : ℕ) (Dt : ℕ → R) (hDt : ∀ m < r, Dt m = D (r - m - 1)) :
    ∀ m, m ≤ r → (topK Dt e r m).1 = cont D e (r - m) m ∧
      (topK Dt e r m).2 = if m = 0 then 0 else cont D e (r - m + 1) (m - 1) := by
  intro m
  induction m with
  | zero => simp [topK, cont_zero]
  | succ m ih =>
    intro hm
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    simp only [topK]
    refine ⟨?_, ?_⟩
    · rw [ih1, ih2, hDt m (by omega)]
      rcases m with _ | m
      · simp only [ite_true, mul_zero, sub_zero, cont_zero, one_mul, Nat.sub_zero]
        rfl
      · obtain ⟨a, rfl⟩ : ∃ a, r = a + m + 2 := ⟨r - m - 2, by omega⟩
        rw [ite_eq_right (by omega), show a + m + 2 - (m + 1) = a + 1 by omega,
          show a + 1 - 1 = a by omega, show a + 1 + 1 = a + 2 by omega,
          show a + m + 2 - (m + 1 + 1) = a by omega, show m + 1 - 1 = m by omega, cont_top D e hDe hee m a]
    · rw [ih1, ite_eq_right (by omega), show m + 1 - 1 = m by omega, show r - (m + 1) + 1 = r - m by omega]

theorem topK_conj (G : R) (Dw Dy e : ℕ → R) (r : ℕ) (hG : ∀ m < r, G * Dw m = Dy m * G)
    (hGe : ∀ j, G * e j = e j * G) :
    ∀ m, m ≤ r → G * (topK Dw e r m).1 = (topK Dy e r m).1 * G ∧
      G * (topK Dw e r m).2 = (topK Dy e r m).2 * G := by
  intro m
  induction m with
  | zero => simp [topK]
  | succ m ih =>
    intro hm
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    simp only [topK]
    refine ⟨?_, ih1⟩
    rw [mul_sub, ← mul_assoc, ih1, mul_assoc, hG m (by omega), ← mul_assoc G (e (r - m)), hGe,
      mul_assoc (e (r - m)) G, ih2, sub_mul, mul_assoc, mul_assoc]

def botA (D Cb Cbi : ℕ → R) (r : ℕ) : ℕ → R × R
  | 0 => (1, 0)
  | i + 1 => if i < r then
      (D i * (botA D Cb Cbi r i).1 - Cb i * (botA D Cb Cbi r i).2, Cbi i * (botA D Cb Cbi r i).1)
      else botA D Cb Cbi r i

theorem botA_eq (D Cb Cbi : ℕ → R) (r : ℕ) :
    ∀ i, i ≤ r → (botA D Cb Cbi r i).1 = cont D (fun j => Cb j * Cbi (j - 1)) 0 i ∧
      (botA D Cb Cbi r i).2 =
        if i = 0 then 0 else Cbi (i - 1) * cont D (fun j => Cb j * Cbi (j - 1)) 0 (i - 1) := by
  intro i
  induction i with
  | zero => simp [botA, cont_zero]
  | succ i ih =>
    intro hi
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    simp only [botA, ite_eq_left (show i < r by omega)]
    refine ⟨?_, ?_⟩
    · rw [ih1, ih2]
      rcases i with _ | i
      · simp only [ite_true, mul_zero, sub_zero, cont_zero, mul_one]
        rfl
      · rw [ite_eq_right (by omega), cont_two, show 0 + i + 1 = i + 1 by omega, show i + 1 - 1 = i by omega,
          mul_assoc]
    · rw [ih1, ite_eq_right (by omega), show i + 1 - 1 = i by omega]

end Formalism.FourierDecayAlt.P.CutMP.TVCrdAlg
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivativeLocalRepresentative
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem derivative_local_representative : RdVRep := by
  intro k r E _ _ X U F f hX hU hc he h hh hhG
  have hc' : ContDiffOn ℝ (((1 : ℕ∞) : WithTop ℕ∞)) F U := by exact_mod_cast hc
  refine ⟨LieDecompositionLocal.rdV_eq_fderiv (m := 1) le_rfl hU hh hhG hc' he hX, ?_⟩
  have hd : DifferentiableAt ℝ F h :=
    (hc.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hh)
  have hloc : Q.LdV X f h = Q.LdV X F h := by
    show deriv (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * h)) 0 =
      deriv (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • X) * h)) 0
    apply Filter.EventuallyEq.deriv_eq
    have hcont : Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * h) := by
      have h1 := (gpMulR h).continuous.comp (B5.curve_contDiff (1 : B.Mat k r) X).continuous
      refine h1.congr fun t => ?_
      simp [gpMulR_apply]
    have hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), NormedSpace.exp ((t : ℂ) • X) * h ∈ U := by
      apply hcont.continuousAt.preimage_mem_nhds
      have h0 : NormedSpace.exp (((0 : ℝ) : ℂ) • X) * h = h := by simp
      rw [h0]
      exact hU.mem_nhds hh
    filter_upwards [hev] with t ht
    exact he _ ht (WeylGroupFacts.uh_mul (B5.exp_mem hX t) hhG)
  rw [hloc]
  exact gp_ldV X h F hd

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ExponentialDegreeHolds
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

theorem exponential_degree_holds : FExpDeg := by
  intro k r gens
  induction gens with
  | nil =>
    intro _ t ht
    simp only [fexp, List.mem_singleton] at ht
    subst ht
    simp
  | cons gn gs ih =>
    intro hdeg t ht
    have hgn : gn.1.natDegree ≤ 1 := hdeg gn (by simp)
    have ih' := ih (fun g hg => hdeg g (List.mem_cons_of_mem _ hg))
    simp only [fexp, List.mem_append, List.mem_map, List.mem_flatMap] at ht
    rcases ht with ⟨t', ht', rfl⟩ | ⟨dX, hdX, t', ht', rfl⟩
    · obtain ⟨h1, h2⟩ := ih' t' ht'
      refine ⟨?_, ?_⟩
      · have := Polynomial.natDegree_mul_le (p := gn.1) (q := t'.1)
        simp only [List.length_cons]
        omega
      · intro X hX
        obtain ⟨g, hg, d, hd⟩ := h2 X hX
        exact ⟨g, List.mem_cons_of_mem _ hg, d, hd⟩
    · obtain ⟨h1, h2⟩ := ih' t' ht'
      refine ⟨?_, ?_⟩
      · have := Polynomial.natDegree_C_mul_le dX.1 t'.1
        simp only [List.length_cons]
        omega
      · intro X hX
        rcases List.mem_cons.1 hX with rfl | hX
        · exact ⟨gn, by simp, dX.1, hdX⟩
        · obtain ⟨g, hg, d, hd⟩ := h2 X hX
          exact ⟨g, List.mem_cons_of_mem _ hg, d, hd⟩

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftCapelliAsGenerators
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem clag_list {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) (w : ℂ) (σ : Equiv.Perm (Fin k)) :
    (List.ofFn fun i : Fin k => fun y : Q.Mx k r → E =>
      (if id (σ i) = id i then (w - ((i : ℕ) : ℂ)) • y else 0) +
        Q.LZ (Hpk k r) (Q.unitB (Hpk k r) Bs (id (σ i)) (id i)) y) =
      (capGens (zgB Bs) σ).map (fun gn => genOpL (E := E) gn w) := by
  unfold capGens
  rw [List.map_ofFn]
  congr 1
  funext i F h
  simp only [Function.comp_apply, genOpL, capGen, zgB, Q.LZ, id, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, one_smul, add_zero, Pi.add_apply]
  split_ifs <;> simp

theorem left_capelli_as_generators : CapLAsGens := by
  intro k r E _ _ Bs w f g
  simp only [Q.capLft, Q.qmFrev, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [List.map_reverse, List.foldr_reverse, clag_list]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

