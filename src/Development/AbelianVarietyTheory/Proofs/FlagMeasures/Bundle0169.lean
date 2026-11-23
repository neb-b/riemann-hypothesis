module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoProdSmallBallAsymptotics
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0137

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdMaxInvLeProdMax
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

theorem prod_max_inv_le_prod_max {ι : Type} [Fintype ι] (x : ι → ℝ) (hx : ∀ v, 0 < x v) (h1 : 1 ≤ ∏ v, x v) :
    ∏ v, max 1 (x v)⁻¹ ≤ ∏ v, max 1 (x v) := by
  have key : ∀ v, max 1 (x v) = x v * max 1 (x v)⁻¹ := by
    intro v
    rcases le_total 1 (x v) with h | h
    · rw [max_eq_right h, max_eq_left (inv_le_one_of_one_le₀ h), mul_one]
    · rw [max_eq_left h, max_eq_right ((one_le_inv₀ (hx v)).2 h), mul_inv_cancel₀ (hx v).ne']
  have h0 : 0 ≤ ∏ v, max 1 (x v)⁻¹ :=
    Finset.prod_nonneg fun v _ => le_trans zero_le_one (le_max_left _ _)
  calc ∏ v, max 1 (x v)⁻¹ = 1 * ∏ v, max 1 (x v)⁻¹ := (one_mul _).symm
    _ ≤ (∏ v, x v) * ∏ v, max 1 (x v)⁻¹ := mul_le_mul_of_nonneg_right h1 h0
    _ = ∏ v, max 1 (x v) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun v _ => (key v).symm

theorem fold_max_le_prod_max {n : ℕ} (x : Fin n → ℝ) :
    Finset.univ.fold max 1 x ≤ ∏ l, max 1 (x l) := by
  have hge : ∀ l, (1 : ℝ) ≤ max 1 (x l) := fun l => le_max_left _ _
  have hone : ∀ s : Finset (Fin n), (1 : ℝ) ≤ ∏ l ∈ s, max 1 (x l) := by
    intro s
    calc (1 : ℝ) = ∏ _l ∈ s, (1 : ℝ) := Finset.prod_const_one.symm
      _ ≤ ∏ l ∈ s, max 1 (x l) := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun l _ => hge l)
  refine (Finset.fold_max_le _).2 ⟨hone _, fun l _ => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ l)]
  calc x l ≤ max 1 (x l) * 1 := by rw [mul_one]; exact le_max_right _ _
    _ ≤ max 1 (x l) * ∏ m ∈ Finset.univ.erase l, max 1 (x m) :=
      mul_le_mul_of_nonneg_left (hone _) (le_trans zero_le_one (hge l))

theorem prod_fold_inv_le {ι : Type} [Fintype ι] {n : ℕ} (P : ℝ) (hP : 1 ≤ P) (Dm : ι → Fin n → ℝ) (De sg : ι → ℝ)
    (hD : ∀ l, (∀ v, Dm v l = 0) ∨ ((∀ v, 0 < Dm v l) ∧ 1 ≤ ∏ v, Dm v l))
    (hDe : ∀ v, De v = Finset.univ.fold max 1 fun l => (Dm v l)⁻¹)
    (hsg : ∀ v, sg v = Finset.univ.fold max 1 fun l => Dm v l / P) :
    ∏ v, De v ≤ ∏ v, (P * sg v) ^ n := by
  have hP0 : 0 < P := lt_of_lt_of_le one_pos hP
  have hsg1 : ∀ v, 1 ≤ sg v := fun v => by
    rw [hsg v]; exact (Finset.le_fold_max _).2 (Or.inl le_rfl)
  have hPsg : ∀ v, 1 ≤ P * sg v := fun v => one_le_mul_of_one_le_of_one_le hP (hsg1 v)
  have hcol : ∀ l, ∏ v, max 1 (Dm v l)⁻¹ ≤ ∏ v, P * sg v := by
    intro l
    rcases hD l with h0 | ⟨hpos, hprod⟩
    · calc ∏ v, max 1 (Dm v l)⁻¹ = ∏ _v : ι, (1 : ℝ) :=
            Finset.prod_congr rfl fun v _ => by simp [h0 v]
        _ ≤ ∏ v, P * sg v := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun v _ => hPsg v)
    · calc ∏ v, max 1 (Dm v l)⁻¹ ≤ ∏ v, max 1 (Dm v l) :=
            prod_max_inv_le_prod_max (fun v => Dm v l) hpos hprod
        _ ≤ ∏ v, P * sg v := by
          refine Finset.prod_le_prod₀ (fun _ _ => le_trans zero_le_one (le_max_left _ _)) (fun v _ => ?_)
          have h1 : Dm v l / P ≤ sg v := by
            rw [hsg v]; exact (Finset.le_fold_max _).2 (Or.inr ⟨l, Finset.mem_univ _, le_rfl⟩)
          refine max_le (hPsg v) ?_
          calc Dm v l = P * (Dm v l / P) := by field_simp
            _ ≤ P * sg v := mul_le_mul_of_nonneg_left h1 hP0.le
  calc ∏ v, De v ≤ ∏ v, ∏ l, max 1 (Dm v l)⁻¹ := by
        refine Finset.prod_le_prod₀ (fun v _ => ?_) (fun v _ => ?_)
        · rw [hDe v]; exact le_trans zero_le_one ((Finset.le_fold_max _).2 (Or.inl le_rfl))
        · rw [hDe v]; exact fold_max_le_prod_max (fun l => (Dm v l)⁻¹)
    _ = ∏ l, ∏ v, max 1 (Dm v l)⁻¹ := Finset.prod_comm
    _ ≤ ∏ _l : Fin n, ∏ v, P * sg v :=
        Finset.prod_le_prod₀ (fun l _ => Finset.prod_nonneg fun v _ => le_trans zero_le_one (le_max_left _ _))
          (fun l _ => hcol l)
    _ = ∏ v, (P * sg v) ^ n := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_pow]

theorem const_loss_le (r : ℕ) (hr : 1 ≤ r) (H : ℝ) (hH : 1 ≤ H) :
    16 * (4 * r + 4 : ℝ) * (4 * r : ℝ) ^ (4 * r ^ 2) * (2 * H) ^ (16 * r ^ 3 + 4 * r) *
      ((2 * H) ^ (2 * r)) ^ ((r + 1) * (8 * r ^ 2 + 2)) ≤ (8 * r * H) ^ (80 * r ^ 4) := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hB8 : (8 : ℝ) ≤ 8 * r * H := by nlinarith
  have hB1 : (1 : ℝ) ≤ 8 * r * H := by linarith
  have hH0 : (0 : ℝ) ≤ 2 * H := by linarith
  have e1 : (16 : ℝ) ≤ (8 * r * H) ^ 2 := by nlinarith
  have e2 : (4 * r + 4 : ℝ) ≤ (8 * r * H) ^ 1 := by rw [pow_one]; nlinarith
  have e3 : (4 * r : ℝ) ≤ 8 * r * H := by nlinarith
  have e4 : 2 * H ≤ 8 * r * H := by nlinarith
  have hexp : 2 + 1 + 4 * r ^ 2 + (16 * r ^ 3 + 4 * r) + 2 * r * ((r + 1) * (8 * r ^ 2 + 2)) ≤ 80 * r ^ 4 := by
    have p1 : r ^ 1 ≤ r ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have p2 : r ^ 2 ≤ r ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have p3 : r ^ 3 ≤ r ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have p0 : 1 ≤ r ^ 4 := Nat.one_le_pow _ _ (by omega)
    rw [pow_one] at p1
    nlinarith
  calc 16 * (4 * r + 4 : ℝ) * (4 * r : ℝ) ^ (4 * r ^ 2) * (2 * H) ^ (16 * r ^ 3 + 4 * r) *
        ((2 * H) ^ (2 * r)) ^ ((r + 1) * (8 * r ^ 2 + 2))
      ≤ (8 * r * H) ^ 2 * (8 * r * H) ^ 1 * (8 * r * H) ^ (4 * r ^ 2) * (8 * r * H) ^ (16 * r ^ 3 + 4 * r) *
        ((8 * r * H) ^ (2 * r)) ^ ((r + 1) * (8 * r ^ 2 + 2)) := by
        have a1 := mul_le_mul e1 e2 (by positivity) (by positivity)
        have a2 := mul_le_mul a1 (pow_le_pow_left₀ (by positivity) e3 (4 * r ^ 2)) (by positivity) (by positivity)
        have a3 := mul_le_mul a2 (pow_le_pow_left₀ hH0 e4 (16 * r ^ 3 + 4 * r)) (pow_nonneg hH0 _) (by positivity)
        exact mul_le_mul a3 (pow_le_pow_left₀ (pow_nonneg hH0 _) (pow_le_pow_left₀ hH0 e4 _) _)
          (pow_nonneg (pow_nonneg hH0 _) _) (by positivity)
    _ = (8 * r * H) ^ (2 + 1 + 4 * r ^ 2 + (16 * r ^ 3 + 4 * r) + 2 * r * ((r + 1) * (8 * r ^ 2 + 2))) := by
        rw [← pow_mul]; simp only [← pow_add]
    _ ≤ (8 * r * H) ^ (80 * r ^ 4) := pow_le_pow_right₀ hB1 hexp

theorem size_loss_le (C' : ℝ) (C₁ k r : ℕ) (hC : C' + 2 ≤ C₁) (hr : 1 ≤ r) (hk : 40 * r ^ 4 ≤ k) (s : ℝ) (hs : 1 ≤ s) :
    s ^ ((r + 1) * (8 * r ^ 2 + 2)) * s ^ (-((((C₁ * k * r : ℕ) : ℝ) - 16 * r ^ 3 - 4 * r - 1) / r)) ≤ s ^ (-(C' * k)) := by
  have hs0 : 0 < s := by linarith
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hk' : 40 * (r : ℝ) ^ 4 ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [← Real.rpow_natCast, ← Real.rpow_add hs0]
  apply Real.rpow_le_rpow_of_exponent_le hs
  push_cast
  have hsplit : ((C₁ : ℝ) * k * r - 16 * r ^ 3 - 4 * r - 1) / r = C₁ * k - 16 * r ^ 2 - 4 - 1 / r := by
    field_simp
  have hinv : 1 / (r : ℝ) ≤ 1 := by rw [div_le_one hr0]; exact hr'
  have hCk : (C' + 2) * k ≤ C₁ * k := mul_le_mul_of_nonneg_right hC hk0
  have q1 : (r : ℝ) ≤ r ^ 2 := by nlinarith
  have q2 : (r : ℝ) ^ 2 ≤ r ^ 3 := by nlinarith
  have q3 : (r : ℝ) ^ 3 ≤ r ^ 4 := by nlinarith
  nlinarith

end GlobalTheory.Amp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RepresentativeValuesVectorVariationUnipotentOrbi
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.PathVar

theorem uMat_inj {n : ℕ} {ε : Fin n → Bool} {a b : Formalism.REAL.UJ ε} (h : uMat a = uMat b) : a = b :=
  Subtype.ext (Units.ext h)

theorem uMat_mul' {n : ℕ} {ε : Fin n → Bool} (a b : Formalism.REAL.UJ ε) : uMat (a * b) = uMat a * uMat b := rfl

theorem expU_add {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) (s t : ℝ) :
    expU ((s + t) • X) = expU (s • X) * expU (t • X) := by
  apply uMat_inj
  rw [uMat_mul', uMat_expU, uMat_expU, uMat_expU, add_smul, Submodule.coe_add]
  apply Matrix.exp_add_of_commute
  simp only [Submodule.coe_smul]
  exact ((Commute.refl (X : Matrix (Fin n) (Fin n) ℂ)).smul_left s).smul_right t

theorem expU_zero {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) : expU ((0 : ℝ) • X) = 1 := by
  apply uMat_inj
  rw [uMat_expU, zero_smul, Submodule.coe_zero, NormedSpace.exp_zero]
  rfl

noncomputable def pt (B : RowsAut) (E : gInf B) (z : B.I.GA) (t : ℝ) : B.I.GA :=
  z * ((fun v => expU (t • E v)), 1)

theorem pt_add (B : RowsAut) (E : gInf B) (z : B.I.GA) (s t : ℝ) :
    pt B E z (s + t) = pt B E z s * ((fun v => expU (t • E v)), 1) := by
  unfold pt
  rw [mul_assoc]
  congr 1
  refine Prod.ext ?_ (by simp)
  funext v
  exact expU_add _ _ _

theorem pt_zero (B : RowsAut) (E : gInf B) (z : B.I.GA) : pt B E z 0 = z := by
  unfold pt
  have : (((fun v => expU ((0 : ℝ) • E v)), 1) : B.I.GA) = 1 := by
    refine Prod.ext ?_ rfl
    funext v
    exact expU_zero _
  rw [this, mul_one]

theorem hasDerivAt_vv (B : RowsAut) {D : ℕ} (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund))
    (Fr : Fin D → B.Hs → B.I.GA → ℂ) (h : ∀ i, IsReps B (T i) (Fr i)) {P : ℕ} {u : B.Hs} (hu : u ∈ VP B P)
    (E : gInf B) (z : B.I.GA) (s : ℝ) :
    HasDerivAt (fun t => vv B Fr u (pt B E z t)) (vv B Fr (dAct B E u) (pt B E z s)) s := by
  have h1 : ∀ i, HasDerivAt (fun t => Fr i u (pt B E z t)) (Fr i (dAct B E u) (pt B E z s)) s := by
    intro i
    have h0 := (h i P u hu).2.2 E (pt B E z s)
    rw [← sub_self s] at h0
    have h2 := h0.comp_sub_const s s
    simp only [← pt_add, add_sub_cancel] at h2
    exact h2
  have h2 : HasDerivAt (fun t => fun i => Fr i u (pt B E z t)) (fun i => Fr i (dAct B E u) (pt B E z s)) s :=
    hasDerivAt_pi.2 h1
  exact ((EuclideanSpace.equiv (Fin D) ℂ).symm.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h2

theorem hs_smul_le {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    Formalism.REAL.hs (s • X) ≤ Formalism.REAL.hs X := by
  unfold Formalism.REAL.hs
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  rw [Matrix.smul_apply, norm_smul, Real.norm_of_nonneg h0]
  exact pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_left (norm_nonneg _) h1) 2

theorem pt_mem_omega (B : RowsAut) (x : B.I.GA) (W : Submodule B.I.E (Fin B.I.n → B.I.E)) (ρ : ℝ)
    (A Z : gInf B)
    (hρ : Real.sqrt (∑ v, Formalism.REAL.hs (A v).1) + Real.sqrt (∑ v, Formalism.REAL.hs (Z v).1) ≤ ρ)
    (hN : ∀ s t : ℝ, ∃ m : B.I.Ginf, ((m, 1) : B.I.GA) ∈ B.I.NA W ∧
      ∀ v, uMat (m v) * uMat (x.1 v) =
        uMat (x.1 v) * NormedSpace.exp ((s : ℂ) • (A v).1) * NormedSpace.exp ((t : ℂ) • (Z v).1))
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    pt B Z (pt B A x s) t ∈ omega B.I x W ρ := by
  refine ⟨by simp [pt], fun v => (s • A v).1, fun v => (t • Z v).1, fun v => ⟨(s • A v).2, (t • Z v).2⟩, ?_,
    fun v => rfl, fun s' t' => ?_⟩
  · refine le_trans (add_le_add (Real.sqrt_le_sqrt ?_) (Real.sqrt_le_sqrt ?_)) hρ
    · exact Finset.sum_le_sum fun v _ => hs_smul_le _ hs.1 hs.2
    · exact Finset.sum_le_sum fun v _ => hs_smul_le _ ht.1 ht.2
  · obtain ⟨m, hm, hm'⟩ := hN (s' * s) (t' * t)
    refine ⟨m, hm, fun v => ?_⟩
    rw [hm' v]
    simp only [Submodule.coe_smul, Complex.coe_smul, smul_smul]

theorem leg (B : RowsAut) (b M : ℝ) (P : ℕ) {D : ℕ} (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund))
    (Fr : Fin D → B.Hs → B.I.GA → ℂ) (hS : StepBoundAt B b P) (h : ∀ i, IsReps B (T i) (Fr i)) (hM : 0 ≤ M)
    (E : gInf B) (z : B.I.GA)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ VP B (P + 1), ‖vv B Fr u (pt B E z t)‖ ≤ M * ‖u‖)
    {u : B.Hs} (hu : u ∈ VP B P) :
    ‖vv B Fr u (pt B E z 1) - vv B Fr u z‖ ≤
      Real.sqrt (∑ v, Formalism.REAL.hs (E v).1) * (Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖) := by
  have := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun t => vv B Fr u (pt B E z t)) (f' := fun s => vv B Fr (dAct B E u) (pt B E z s))
    (C := Real.sqrt (∑ v, Formalism.REAL.hs (E v).1) * (Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖))
    (fun s _ => (hasDerivAt_vv B T Fr h hu E z s).hasDerivWithinAt)
    (fun s hs => by
      refine (hb s (Set.Ico_subset_Icc_self hs) _ (hS.2.2.2.2.2.2 E u hu)).trans ?_
      refine (mul_le_mul_of_nonneg_left (hS.2.2.2.2.2.1 E u hu) hM).trans (le_of_eq ?_)
      ring)
  simpa only [pt_zero] using this

theorem path_variation : ∀ (B : RowsAut) (b ρ M : ℝ) (P : ℕ) (D : ℕ) (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) (Fr : Fin D → B.Hs → B.I.GA → ℂ) (x : B.I.GA) (W : Submodule B.I.E (Fin B.I.n → B.I.E)), StepBoundAt B b P → (∀ i, IsReps B (T i) (Fr i)) → 0 ≤ M → (∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B (P + 1), ‖vv B Fr u y‖ ≤ M * ‖u‖) → ∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B P, ‖vv B Fr u y - vv B Fr u x‖ ≤ ρ * Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ := by
  intro B b ρ M P D T Fr x W hS h hM hb y hy u hu
  obtain ⟨hy2, A0, Z0, hg, hρ, hy1, hN⟩ := hy
  let A : gInf B := fun v => ⟨A0 v, (hg v).1⟩
  let Z : gInf B := fun v => ⟨Z0 v, (hg v).2⟩
  have hmem := fun s t hs ht => pt_mem_omega B x W ρ A Z hρ hN (s := s) (t := t) hs ht
  have hyeq : y = pt B Z (pt B A x 1) 1 := by
    refine Prod.ext ?_ (by simp [pt, hy2])
    funext v
    apply uMat_inj
    rw [hy1 v]
    simp only [pt, one_smul]
    rfl
  have h1 := leg B b M P T Fr hS h hM A x (fun t ht w hw => by
    have := hb _ (hmem t 0 ht (by simp)) w hw
    rwa [pt_zero] at this) hu
  have h2 := leg B b M P T Fr hS h hM Z (pt B A x 1) (fun t ht w hw => hb _ (hmem 1 t (by simp) ht) w hw) hu
  have hK : 0 ≤ Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ := by
    unfold beP; positivity
  rw [← hyeq] at h2
  calc _ ≤ ‖vv B Fr u y - vv B Fr u (pt B A x 1)‖ + ‖vv B Fr u (pt B A x 1) - vv B Fr u x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (Real.sqrt (∑ v, Formalism.REAL.hs (A0 v)) + Real.sqrt (∑ v, Formalism.REAL.hs (Z0 v))) *
        (Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖) := by
        rw [add_mul, add_comm]; exact add_le_add h1 h2
    _ ≤ ρ * (Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖) := mul_le_mul_of_nonneg_right hρ hK
    _ = _ := by ring

end GlobalTheory.PathVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallBallAsymptoticsPiWeighted
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem smallBall_pi_fin (n : ℕ) : ∀ (X : Fin n → Type) [∀ i, MeasurableSpace (X i)]
    (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)] (ρ : ∀ i, X i → ℝ) (d : Fin n → ℕ)
    (C : Fin n → ℝ), (∀ i, Measurable (ρ i)) → (∀ i x, 0 ≤ ρ i x) → (∀ i, 0 < C i) →
    (∀ i, Filter.Tendsto (fun r : ℝ => ν i {x | Real.sqrt (ρ i x) ≤ r} / ENNReal.ofReal (r ^ d i))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (ENNReal.ofReal (C i) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d i))) 1)))) →
    Filter.Tendsto (fun r : ℝ => Measure.pi ν {x | Real.sqrt (∑ i, ρ i (x i)) ≤ r} /
        ENNReal.ofReal (r ^ ∑ i, d i)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (ENNReal.ofReal (∏ i, C i) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (∑ i, d i))) 1))) := by
  induction n with
  | zero =>
    intro X _ ν _ ρ d C _ _ _ _
    have hball : ∀ m : ℕ, m = 0 →
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1) = 1 := by
      rintro m rfl
      rw [volume_euclideanSpace_eq_dirac]
      exact Measure.dirac_apply_of_mem (Metric.mem_ball_self one_pos)
    rw [hball _ (Fin.sum_univ_zero d), Fin.prod_univ_zero, ENNReal.ofReal_one, mul_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : (0 : ℝ) ≤ r := le_of_lt hr
    have hset : {x : ∀ i : Fin 0, X i | Real.sqrt (∑ i, ρ i (x i)) ≤ r} = Set.univ := by
      ext x
      simp [hr']
    rw [hset, Measure.pi_univ]
    simp
  | succ n ih =>
    intro X _ ν _ ρ d C hρm hρ0 hC h
    have hmp := measurePreserving_piFinSuccAbove ν 0
    have h2 := ih (fun j => X (Fin.succAbove 0 j)) (fun j => ν (Fin.succAbove 0 j))
      (fun j => ρ (Fin.succAbove 0 j)) (fun j => d (Fin.succAbove 0 j))
      (fun j => C (Fin.succAbove 0 j)) (fun j => hρm _) (fun j => hρ0 _) (fun j => hC _)
      (fun j => h _)
    have hmeas2 : Measurable fun y : (∀ j : Fin n, X (Fin.succAbove 0 j)) =>
        ∑ j, ρ (Fin.succAbove 0 j) (y j) :=
      Finset.measurable_sum _ fun j _ => (hρm _).comp (measurable_pi_apply j)
    have key := _root_.GlobalTheory.SmallBallProd.tendsto_prod_smallBall (X 0) (∀ j : Fin n, X (Fin.succAbove 0 j)) (ν 0)
      (Measure.pi fun j => ν (Fin.succAbove 0 j)) (ρ 0)
      (fun y => ∑ j, ρ (Fin.succAbove 0 j) (y j)) (d 0) (∑ j, d (Fin.succAbove 0 j))
      (C 0) (∏ j, C (Fin.succAbove 0 j)) (hρm 0) hmeas2 (hρ0 0)
      (fun y => Finset.sum_nonneg fun j _ => hρ0 _ _) (hC 0)
      (Finset.prod_pos fun j _ => hC _) (h 0) h2
    have hsumd : d 0 + ∑ j, d (Fin.succAbove 0 j) = ∑ i, d i :=
      (Fin.sum_univ_succAbove d 0).symm
    have hprodC : C 0 * ∏ j, C (Fin.succAbove 0 j) = ∏ i, C i :=
      (Fin.prod_univ_succAbove C 0).symm
    rw [hsumd, hprodC] at key
    refine key.congr' (Filter.Eventually.of_forall fun r => ?_)
    congr 1
    rw [← hmp.measure_preimage_equiv]
    congr 1
    ext x
    change Real.sqrt (ρ 0 (x 0) + ∑ j, ρ (Fin.succAbove 0 j) (x (Fin.succAbove 0 j))) ≤ r ↔
      Real.sqrt (∑ i, ρ i (x i)) ≤ r
    rw [Fin.sum_univ_succAbove (fun i => ρ i (x i)) 0]

theorem smallBall_weight {X : Type} [MeasurableSpace X] (ν : Measure X) (ρ : X → ℝ) (d : ℕ)
    (w : ℝ) (hw : 0 < w) (V : ENNReal)
    (h : Filter.Tendsto (fun r : ℝ => ν {x | Real.sqrt (ρ x) ≤ r} / ENNReal.ofReal (r ^ d))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds V)) :
    Filter.Tendsto (fun r : ℝ => ν {x | Real.sqrt (w * ρ x) ≤ r} / ENNReal.ofReal (r ^ d))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (w ^ (-((d : ℝ) / 2))) * V)) := by
  have hs : 0 < Real.sqrt w := Real.sqrt_pos.2 hw
  have hmap : Filter.Tendsto (fun r : ℝ => r / Real.sqrt w) (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h0 : Filter.Tendsto (fun r : ℝ => r / Real.sqrt w) (nhds 0)
          (nhds (0 / Real.sqrt w)) := (continuous_id.div_const _).tendsto 0
      rw [zero_div] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact div_pos hr hs
  have key := ENNReal.Tendsto.mul_const (h.comp hmap)
    (b := ENNReal.ofReal (w ^ (-((d : ℝ) / 2)))) (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_comm]
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : (0 : ℝ) < r := hr
  have hrs : 0 < r / Real.sqrt w := div_pos hr' hs
  have hset : {x | Real.sqrt (w * ρ x) ≤ r} = {x | Real.sqrt (ρ x) ≤ r / Real.sqrt w} := by
    ext x
    simp only [Set.mem_ofPred_eq, Real.sqrt_mul hw.le, le_div_iff₀' hs]
  have hc : w ^ (-((d : ℝ) / 2)) = (Real.sqrt w ^ d)⁻¹ := by
    rw [Real.rpow_neg hw.le, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hw.le]
    congr 2
    ring
  have hrd : r ^ d = (r / Real.sqrt w) ^ d * Real.sqrt w ^ d := by
    rw [div_pow, div_mul_cancel₀]
    exact pow_ne_zero _ hs.ne'
  have ha0 : ENNReal.ofReal ((r / Real.sqrt w) ^ d) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos hrs d
  simp only [Function.comp_apply]
  rw [hset, hc, hrd, ENNReal.ofReal_mul (pow_nonneg hrs.le d),
    ENNReal.ofReal_inv_of_pos (pow_pos hs d)]
  simp only [ENNReal.div_eq_inv_mul]
  rw [ENNReal.mul_inv (Or.inl ha0) (Or.inl ENNReal.ofReal_ne_top)]
  ring

theorem smallBall_pi_weight : ∀ (ι : Type) [Fintype ι] (X : ι → Type) [∀ i, MeasurableSpace (X i)] (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)] (ρ : ∀ i, X i → ℝ) (d : ι → ℕ) (w : ι → ℝ), (∀ i, Measurable (ρ i)) → (∀ i x, 0 ≤ ρ i x) → (∀ i, 0 < w i) → (∀ i, Filter.Tendsto (fun r : ℝ => ν i {x | Real.sqrt (ρ i x) ≤ r} / ENNReal.ofReal (r ^ d i)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d i))) 1)))) → Filter.Tendsto (fun r : ℝ => Measure.pi ν {x | Real.sqrt (∑ i, w i * ρ i (x i)) ≤ r} / ENNReal.ofReal (r ^ ∑ i, d i)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (∏ i, w i ^ (-((d i : ℝ) / 2))) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (∑ i, d i))) 1))) := by
  intro ι _ X _ ν _ ρ d w hρm hρ0 hw h
  have hw' : ∀ i, Filter.Tendsto
      (fun r : ℝ => ν i {x | Real.sqrt (w i * ρ i x) ≤ r} / ENNReal.ofReal (r ^ d i))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (ENNReal.ofReal (w i ^ (-((d i : ℝ) / 2))) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d i))) 1))) :=
    fun i => smallBall_weight (ν i) (ρ i) (d i) (w i) (hw i) _ (h i)
  let f : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have key := smallBall_pi_fin (Fintype.card ι) (fun j => X (f j)) (fun j => ν (f j))
    (fun j x => w (f j) * ρ (f j) x) (fun j => d (f j))
    (fun j => w (f j) ^ (-((d (f j) : ℝ) / 2))) (fun j => (hρm _).const_mul _)
    (fun j x => mul_nonneg (hw _).le (hρ0 _ x)) (fun j => Real.rpow_pos_of_pos (hw _) _)
    (fun j => hw' _)
  have hS : ∑ j, d (f j) = ∑ i, d i := Equiv.sum_comp f d
  have hP : ∏ j, w (f j) ^ (-((d (f j) : ℝ) / 2)) = ∏ i, w i ^ (-((d i : ℝ) / 2)) :=
    Equiv.prod_comp f (fun i => w i ^ (-((d i : ℝ) / 2)))
  rw [hS, hP] at key
  have hmp := measurePreserving_piCongrLeft ν f
  refine key.congr' (Filter.Eventually.of_forall fun r => ?_)
  congr 1
  rw [← hmp.measure_preimage_equiv]
  congr 1
  ext g
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  have hsum : ∑ i, w i * ρ i (MeasurableEquiv.piCongrLeft X f g i) =
      ∑ j, w (f j) * ρ (f j) (g j) := by
    rw [← Equiv.sum_comp f (fun i => w i * ρ i (MeasurableEquiv.piCongrLeft X f g i))]
    simp only [MeasurableEquiv.piCongrLeft_apply_apply]
  rw [hsum]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoBallMeanBigCellWeight
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellDens

theorem tendsto_mean_ball_of_continuousAt {r : ℕ} (c : Fin r → ℂ) (f : (Fin r → ℂ) → ℝ≥0∞)
    (hf : ContinuousAt f c) (h1 : f c = 1) :
    Tendsto (fun ρ : ℝ => (∫⁻ x in Metric.ball c ρ, f x) / volume (Metric.ball (0 : Fin r → ℂ) ρ))
      (𝓝[>] 0) (𝓝 1) := by
  rw [ENNReal.tendsto_nhds ENNReal.one_ne_top]
  intro ε hε
  have hfc : Tendsto f (𝓝 c) (𝓝 1) := by rw [← h1]; exact hf
  have hev := (ENNReal.tendsto_nhds ENNReal.one_ne_top).1 hfc ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  filter_upwards [Ioo_mem_nhdsGT hδ] with ρ hρ
  have hV : volume (Metric.ball c ρ) = volume (Metric.ball (0 : Fin r → ℂ) ρ) :=
    Measure.addHaar_ball_center volume c ρ
  have hpos : volume (Metric.ball c ρ) ≠ 0 := (Metric.measure_ball_pos volume c hρ.1).ne'
  have hfin : volume (Metric.ball c ρ) ≠ ⊤ := measure_ball_lt_top.ne
  have hsub : ∀ x ∈ Metric.ball c ρ, f x ∈ Set.Icc (1 - ε) (1 + ε) := fun x hx =>
    hball x (Metric.ball_subset_ball hρ.2.le hx)
  have hlo : (1 - ε) * volume (Metric.ball c ρ) ≤ ∫⁻ x in Metric.ball c ρ, f x := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' measurableSet_ball fun x hx => (hsub x hx).1
  have hhi : ∫⁻ x in Metric.ball c ρ, f x ≤ (1 + ε) * volume (Metric.ball c ρ) := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' measurableSet_ball fun x hx => (hsub x hx).2
  rw [← hV]
  constructor
  · calc 1 - ε = (1 - ε) * volume (Metric.ball c ρ) / volume (Metric.ball c ρ) :=
          (ENNReal.mul_div_cancel_right hpos hfin).symm
      _ ≤ _ := ENNReal.div_le_div_right hlo _
  · calc _ ≤ (1 + ε) * volume (Metric.ball c ρ) / volume (Metric.ball c ρ) :=
          ENNReal.div_le_div_right hhi _
      _ = 1 + ε := ENNReal.mul_div_cancel_right hpos hfin

theorem tendsto_mean_cWeight : ∀ (k r : ℕ), Tendsto (fun ρ : ℝ => (∫⁻ x in Metric.ball (fun _ => 1 : Fin r → ℂ) ρ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r x)) / volume (Metric.ball (0 : Fin r → ℂ) ρ)) (𝓝[>] 0) (𝓝 1) := by
  intro k r
  apply tendsto_mean_ball_of_continuousAt
  · refine (ENNReal.continuous_ofReal.comp ?_).continuousAt
    unfold Formalism.FourierDecayAlt.B2.cWeight
    fun_prop
  · unfold Formalism.FourierDecayAlt.B2.cWeight
    simp

end GlobalTheory.CellDens
end

