module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0048
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0049

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfSolApprox
section
noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

namespace Formalism.L2.SG.Pf.RationalApproximateSolutions

variable {ι K L : Type*} [Fintype ι] [DecidableEq ι] [Field K] [Field L]

def condMat (lv : ι → ℕ) (k : ℕ) (G G' : Matrix ι ι K) : Matrix ((ι × ι) ⊕ (ι × ι)) (ι × ι) K :=
  Matrix.of fun r q => Sum.elim (fun p : ι × ι => if lv p.2 < lv p.1 + k ∧ q = p then (1 : K) else 0)
    (fun p => if lv p.2 < lv p.1 + 1 then G' p.1 q.1 * G q.2 p.2 else 0) r

def matOf (z : ι × ι → L) : Matrix ι ι L := Matrix.of fun a b => z (a, b)

theorem condMat_inl (lv : ι → ℕ) (k : ℕ) (G G' : Matrix ι ι K) (f : K →+* L) (z : ι × ι → L) (i j : ι) :
    ((condMat lv k G G').map f *ᵥ z) (Sum.inl (i, j)) = if lv j < lv i + k then z (i, j) else 0 := by
  first
    | simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, condMat, Matrix.of_apply, Sum.elim_inl]
    | simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.map_apply, condMat, Matrix.of_apply, Sum.elim_inl]
  by_cases h : lv j < lv i + k
  · rw [if_pos h, Finset.sum_eq_single (i, j)]
    · simp [h]
    · intro q _ hq
      simp [hq]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rw [if_neg h]
    simp [h]

theorem condMat_inr (lv : ι → ℕ) (k : ℕ) (G G' : Matrix ι ι K) (f : K →+* L) (z : ι × ι → L) (i j : ι) :
    ((condMat lv k G G').map f *ᵥ z) (Sum.inr (i, j)) =
      if lv j < lv i + 1 then (G'.map f * matOf z * G.map f) i j else 0 := by
  first
    | simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, condMat, Matrix.of_apply, Sum.elim_inr]
    | simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.map_apply, condMat, Matrix.of_apply, Sum.elim_inr]
  by_cases h : lv j < lv i + 1
  · simp only [h, ↓reduceIte, map_mul]
    rw [Fintype.sum_prod_type]
    simp only [Matrix.mul_apply, Matrix.map_apply, matOf, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  · simp [h]

theorem cond_iff (lv : ι → ℕ) (k : ℕ) (G G' : Matrix ι ι K) (f : K →+* L) (z : ι × ι → L) :
    (condMat lv k G G').map f *ᵥ z = 0 ↔
      InPat lv k (matOf z) ∧ InPat lv 1 (G'.map f * matOf z * G.map f) := by
  constructor
  · intro hz
    refine ⟨?_, ?_⟩
    · intro i j hij
      have := congrFun hz (Sum.inl (i, j))
      rw [condMat_inl, if_pos hij] at this
      simpa [matOf] using this
    · intro i j hij
      have := congrFun hz (Sum.inr (i, j))
      rw [condMat_inr, if_pos hij] at this
      simpa using this
  · rintro ⟨h1, h2⟩
    funext r
    rcases r with ⟨i, j⟩ | ⟨i, j⟩
    · rw [condMat_inl]
      split_ifs with hij
      · simpa [matOf] using h1 i j hij
      · rfl
    · rw [condMat_inr]
      split_ifs with hij
      · simpa using h2 i j hij
      · rfl

end Formalism.L2.SG.Pf.RationalApproximateSolutions

namespace Formalism.L2.SG.TermOp.Vanish

open Formalism.L2.SG.Pf.RationalApproximateSolutions

theorem ratSolApprox_holds : RatSolApprox := by
  intro D X G G' k N hN
  obtain ⟨P0, hMP0, hfix0⟩ :=
    Formalism.L2.SG.Pf.RCoc.kerBaseChange_holds X.B.I.E X.B.I.E (RingHom.id _) _ _ (condMat (lvk X) k G G')
  have hfixE : ∀ w : Kap X × Kap X → X.B.I.E, condMat (lvk X) k G G' *ᵥ w = 0 → P0 *ᵥ w = w := by
    intro w hw
    have e := hfix0 w (by simpa using hw)
    simpa using e
  have hfixV : ∀ v (z : Kap X × Kap X → ℂ), (condMat (lvk X) k G G').map (X.B.I.φ v) *ᵥ z = 0 →
      P0.map (X.B.I.φ v) *ᵥ z = z := by
    intro v z hz
    obtain ⟨Pv, hMPv, hfixv⟩ :=
      Formalism.L2.SG.Pf.RCoc.kerBaseChange_holds X.B.I.E ℂ (X.B.I.φ v) _ _ (condMat (lvk X) k G G')
    have hPP : P0 * Pv = Pv := by
      refine Matrix.ext_of_mulVec_single fun q => ?_
      rw [← Matrix.mulVec_mulVec]
      apply hfixE
      rw [Matrix.mulVec_mulVec, hMPv, Matrix.zero_mulVec]
    have e := hfixv z hz
    calc P0.map (X.B.I.φ v) *ᵥ z = P0.map (X.B.I.φ v) *ᵥ (Pv.map (X.B.I.φ v) *ᵥ z) := by rw [e]
      _ = (P0 * Pv).map (X.B.I.φ v) *ᵥ z := by rw [Matrix.mulVec_mulVec, Matrix.map_mul]
      _ = z := by rw [hPP, e]
  obtain ⟨c, hc, hcI⟩ := exists_common_den (E := X.B.I.E)
    (fun q : (Kap X × Kap X) × (Kap X × Kap X) => P0 q.1 q.2)
  let Q : Matrix (Kap X × Kap X) (Kap X × Kap X) (𝓞 X.B.I.E) :=
    Matrix.of fun a b => ⟨(c : X.B.I.E) * P0 a b, hcI (a, b)⟩
  have hQ : ∀ a b, algebraMap (𝓞 X.B.I.E) X.B.I.E (Q a b) = (c : X.B.I.E) * P0 a b := fun a b => rfl
  obtain ⟨R0, hR0⟩ := Formalism.L2.SG.Pf.oeApprox_holds X.B.I.F X.B.I.E X.B.I.cm.totReal X.B.I.cm.cmUnram.1
    X.B.I.cm.deg2 X.B.I.φ X.B.I.φ_over
  obtain ⟨Nc, hNcd⟩ : ∃ Nc : ℕ, Nc = N * c := ⟨_, rfl⟩
  have hNc0 : (Nc : ℂ) ≠ 0 := by
    rw [hNcd]
    exact Nat.cast_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  refine ⟨((Nc : ℝ) * max R0 0) * ∑ v, ∑ q, ∑ r, ‖X.B.I.φ v (P0 q r)‖, fun P hP => ?_⟩
  choose y hy using fun q : Kap X × Kap X => hR0 (fun v => P v q.1 q.2 / (Nc : ℂ))
  set Yv : Kap X × Kap X → X.B.I.E := (Nc : X.B.I.E) • (P0 *ᵥ fun q => (y q : X.B.I.E)) with hYvd
  have hYv : condMat (lvk X) k G G' *ᵥ Yv = 0 := by
    rw [hYvd, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hMP0, Matrix.zero_mulVec, smul_zero]
  have hcond := (cond_iff (lvk X) k G G' (RingHom.id X.B.I.E) Yv).1 (by simpa using hYv)
  refine ⟨matOf Yv, hcond.1, by simpa using hcond.2, ?_, ?_⟩
  · refine ⟨Matrix.of fun a b => (Q *ᵥ y) (a, b), ?_⟩
    ext a b
    have e := RingHom.map_mulVec (algebraMap (𝓞 X.B.I.E) X.B.I.E) Q y (a, b)
    simp only [matOf, hYvd, Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, Pi.smul_apply, smul_eq_mul]
    change _ = (N : X.B.I.E) * algebraMap (𝓞 X.B.I.E) X.B.I.E ((Q *ᵥ y) (a, b))
    rw [e]
    simp only [mulVec, dotProduct, Matrix.map_apply, Function.comp_apply, hQ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hNcd]
    rw [show algebraMap (𝓞 X.B.I.E) X.B.I.E (y r) = (y r : X.B.I.E) from rfl]
    push_cast
    ring
  · intro v i j
    have hm : matOf (fun q : Kap X × Kap X => P v q.1 q.2) = P v := by
      ext a b
      rfl
    have hz : (condMat (lvk X) k G G').map (X.B.I.φ v) *ᵥ (fun q : Kap X × Kap X => P v q.1 q.2) = 0 :=
      (cond_iff (lvk X) k G G' (X.B.I.φ v) _).2 (by rw [hm]; exact ⟨(hP v).1, (hP v).2⟩)
    have hfz := congrFun (hfixV v _ hz) (i, j)
    simp only [mulVec, dotProduct, Matrix.map_apply] at hfz
    have key : ((matOf Yv).map (X.B.I.φ v) - P v) i j =
        ∑ r, X.B.I.φ v (P0 (i, j) r) * ((Nc : ℂ) * X.B.I.φ v (y r : X.B.I.E) - P v r.1 r.2) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.sub_apply, Matrix.map_apply, matOf, Matrix.of_apply, hYvd, Pi.smul_apply, smul_eq_mul,
        mulVec, dotProduct, map_mul, map_sum, map_natCast]
      conv_lhs => rw [← hfz]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    have hM0 : 0 ≤ (Nc : ℝ) * max R0 0 := mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)
    rw [key]
    calc ‖∑ r, X.B.I.φ v (P0 (i, j) r) * ((Nc : ℂ) * X.B.I.φ v (y r : X.B.I.E) - P v r.1 r.2)‖
        ≤ ∑ r, ‖X.B.I.φ v (P0 (i, j) r)‖ * ((Nc : ℝ) * max R0 0) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have h1 : ‖P v r.1 r.2 / (Nc : ℂ) - X.B.I.φ v (y r : X.B.I.E)‖ ≤ R0 := hy r v
          have h2 : (Nc : ℂ) * (P v r.1 r.2 / (Nc : ℂ)) = P v r.1 r.2 := by field_simp
          have e2 : (Nc : ℂ) * X.B.I.φ v (y r : X.B.I.E) - P v r.1 r.2 =
              -((Nc : ℂ) * (P v r.1 r.2 / (Nc : ℂ) - X.B.I.φ v (y r : X.B.I.E))) := by
            rw [mul_sub, h2]
            ring
          rw [e2, norm_neg, norm_mul, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_left (h1.trans (le_max_left _ _)) (Nat.cast_nonneg _)
      _ = ((Nc : ℝ) * max R0 0) * ∑ r, ‖X.B.I.φ v (P0 (i, j) r)‖ := by
          rw [← Finset.sum_mul, mul_comm]
      _ ≤ ((Nc : ℝ) * max R0 0) * ∑ v, ∑ q, ∑ r, ‖X.B.I.φ v (P0 q r)‖ := by
          refine mul_le_mul_of_nonneg_left ?_ hM0
          calc ∑ r, ‖X.B.I.φ v (P0 (i, j) r)‖ ≤ ∑ q, ∑ r, ‖X.B.I.φ v (P0 q r)‖ :=
                Finset.single_le_sum (f := fun q => ∑ r, ‖X.B.I.φ v (P0 q r)‖)
                  (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ (i, j))
            _ ≤ ∑ v', ∑ q, ∑ r, ‖X.B.I.φ v' (P0 q r)‖ :=
                Finset.single_le_sum (f := fun v' => ∑ q, ∑ r, ‖X.B.I.φ v' (P0 q r)‖)
                  (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
                  (Finset.mem_univ v)

end Formalism.L2.SG.TermOp.Vanish
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SkewHermitianApproximation
section
noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.SlabNDensePf

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip Formalism.L2.SG.Pf.UnipB

section KgPart

theorem cg_Lf_step (I : AutInst) {d₁ d₂ g : ℕ}
    (H₁ : ∀ y ∈ I.Lf, ∀ i, (d₁ : I.E ⊗[I.F] Af I.F) * y i ∈ IntAf I.F I.E)
    (H₂ : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ i, y i ∈ IntAf I.F I.E) →
      (d₂ : I.E ⊗[I.F] Af I.F) • y ∈ I.Lf)
    {M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hM : cg_C (IntAf I.F I.E) (g * d₁ * d₂) M)
    (y : Fin I.n → I.E ⊗[I.F] Af I.F) (hy : y ∈ I.Lf) :
    ∃ z ∈ I.Lf, M *ᵥ y = (g : I.E ⊗[I.F] Af I.F) • z := by
  choose t ht e using hM
  refine ⟨(d₂ : I.E ⊗[I.F] Af I.F) • fun i => ∑ j, t i j * ((d₁ : I.E ⊗[I.F] Af I.F) * y j),
    H₂ _ fun i => sum_mem fun j _ => mul_mem (ht i j) (H₁ y hy j), ?_⟩
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [e i j]; push_cast; ring

theorem cg_Kg (I : AutInst) (k : I.Gf) (g : ℕ)
    (hk : ∀ y ∈ I.Lf, ∃ z ∈ I.Lf, (I.fmat k - 1) *ᵥ y = (g : I.E ⊗[I.F] Af I.F) • z) : k ∈ I.Kg g := by
  have fwd : ∀ v ∈ I.Lf, I.fmat k *ᵥ v ∈ I.Lf := by
    intro v hv
    obtain ⟨z, hz, e⟩ := hk v hv
    have e2 : I.fmat k *ᵥ v = v + (I.fmat k - 1) *ᵥ v := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [e2, e, Nat.cast_smul_eq_nsmul]
    exact add_mem hv (nsmul_mem hz g)
  have inv : ∀ w ∈ I.Lf, I.fmat k⁻¹ *ᵥ w ∈ I.Lf := by
    intro w hw
    refine PIW.AdelClassFin.dual_hat_lattice I _ fun y' hy' => ?_
    have e : PIW.AdelClassFin.hhat I y' (I.fmat k⁻¹ *ᵥ w) = PIW.AdelClassFin.hhat I (I.fmat k *ᵥ y') w := by
      rw [← PIW.AdelClassFin.dictTop_hhat_unit I k y' (I.fmat k⁻¹ *ᵥ w), Matrix.mulVec_mulVec,
        PIW.AdelClassFin.dictTop_mul_inv, Matrix.one_mulVec]
    rw [e]
    exact PIW.AdelClassFin.dual_hat_integral I _ (fwd y' hy') w hw
  refine ⟨?_, hk⟩
  show ∀ v, v ∈ I.Lf ↔ I.fmat k *ᵥ v ∈ I.Lf
  intro v
  refine ⟨fwd v, fun h => ?_⟩
  have h2 := inv _ h
  rwa [Matrix.mulVec_mulVec, PIW.AdelClassFin.dictTop_inv_mul, Matrix.one_mulVec] at h2

variable {D : D7} (X : HidaSetting D)

theorem cg_BB : Bf X * Bf' X = 1 := by
  unfold Bf Bf'
  rw [← Matrix.map_mul, Bm_mul_Bm']
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem cg_conj (y : X.B.I.Gf) : Bf X * Mf X y * Bf' X = X.B.I.fmat y := by
  simp only [Mf, ← Matrix.mul_assoc, cg_BB, Matrix.one_mul]
  rw [Matrix.mul_assoc, cg_BB, Matrix.mul_one]

theorem cg_fmat_eq (x y : X.B.I.Gf) :
    X.B.I.fmat (x⁻¹ * y) - 1 = X.B.I.fmat x⁻¹ * Bf X * (Mf X y - Mf X x) * Bf' X := by
  have key : Bf X * (Mf X y - Mf X x) * Bf' X = X.B.I.fmat y - X.B.I.fmat x := by
    rw [Matrix.mul_sub, Matrix.sub_mul, cg_conj, cg_conj]
  have h1 : X.B.I.fmat (x⁻¹ * y) = X.B.I.fmat x⁻¹ * X.B.I.fmat y := rfl
  have h2 : X.B.I.fmat x⁻¹ * X.B.I.fmat x = 1 := by
    rw [show X.B.I.fmat x⁻¹ * X.B.I.fmat x = X.B.I.fmat (x⁻¹ * x) from rfl, inv_mul_cancel]
    rfl
  rw [Matrix.mul_assoc (X.B.I.fmat x⁻¹) (Bf X), Matrix.mul_assoc (X.B.I.fmat x⁻¹), key, Matrix.mul_sub, h1, h2]

end KgPart

theorem level_of_close_element : KgOfClose := by
  intro D X x g hg
  obtain ⟨d₁, hd₁, H₁⟩ := Formalism.L2.SG.Pf.Tau.TraceIntegralityAlt.Lf_upper X.B.I
  obtain ⟨d₂, hd₂, H₂⟩ := Formalism.L2.SG.Pf.Tau.TraceIntegralityAlt.Lf_lower X.B.I
  obtain ⟨mP, hmP, hP⟩ := cg_D_exists (X.B.I.fmat x⁻¹ * Bf X)
  obtain ⟨mQ, hmQ, hQ⟩ := cg_D_exists (Bf' X)
  refine ⟨g * d₁ * d₂ * mQ * mP,
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hg hd₁) hd₂) hmQ) hmP, fun y hy => ?_⟩
  have hΔ : cg_C (IntAf X.B.I.F X.B.I.E) (g * d₁ * d₂) (X.B.I.fmat (x⁻¹ * y) - 1) := by
    rw [cg_fmat_eq X x y]
    exact cg_C_mul_right (cg_C_mul_left hP hy) hQ
  exact cg_Kg X.B.I _ g fun y' hy' => cg_Lf_step X.B.I H₁ H₂ hΔ y' hy'

section Approx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cg_approx (k : ℕ) (hk : 1 ≤ k) (z : E ⊗[F] Af F) :
    ∃ a : E, ∃ t ∈ IntAf F E, Formalism.UG.inclE (F := F) (Af F) a - z = (k : E ⊗[F] Af F) * t := by
  obtain ⟨m, hm, hmz⟩ := PIW.AdelClassFin.dual_denominator F E z
  obtain ⟨a, r', hr', e⟩ := PIW.AdelClassFin.dual_dense F E (k * m) (Nat.mul_pos hk hm) _ hmz
  refine ⟨(a : E) / m, -r', neg_mem hr', ?_⟩
  have hm' : (m : E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have h2 : Formalism.UG.inclE (F := F) (Af F) ((1 : E) / m) * (m : E ⊗[F] Af F) = 1 := by
    rw [← map_natCast (Formalism.UG.inclE (F := F) (Af F)) m, ← map_mul, div_mul_cancel₀ _ hm', map_one]
  have hz : z = Formalism.UG.inclE (F := F) (Af F) ((1 : E) / m) * ((m : E ⊗[F] Af F) * z) := by
    rw [← mul_assoc, h2, one_mul]
  have ha : Formalism.UG.inclE (F := F) (Af F) ((a : E) / m) =
      Formalism.UG.inclE (F := F) (Af F) ((1 : E) / m) * Formalism.UG.inclE (F := F) (Af F) (a : E) := by
    rw [← map_mul]; congr 1; ring
  rw [ha]
  rw [hz]
  rw [e]
  push_cast
  linear_combination (-(k : E ⊗[F] Af F) * r') * h2

theorem cg_approx_mat {ι : Type} [Fintype ι] (lv : ι → ℕ) (Z : Matrix ι ι (E ⊗[F] Af F))
    (hZ : InPat lv 1 Z) (k : ℕ) (hk : 1 ≤ k) :
    ∃ W : Matrix ι ι E, InPat lv 1 W ∧ cg_C (IntAf F E) k (W.map (Formalism.UG.inclE (F := F) (Af F)) - Z) := by
  choose a t ht e using fun i j => cg_approx (F := F) k hk (Z i j)
  refine ⟨Matrix.of fun i j => if lv j < lv i + 1 then 0 else a i j, fun i j h => ?_, fun i j => ?_⟩
  · simp only [Matrix.of_apply, if_pos h]
  · by_cases h : lv j < lv i + 1
    · refine ⟨0, zero_mem _, ?_⟩
      simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply, if_pos h, map_zero, hZ i j h,
        sub_zero, mul_zero]
    · refine ⟨t i j, ht i j, ?_⟩
      simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply, if_neg h]
      exact e i j

end Approx

section Skew

variable {D : D7} (X : HidaSetting D)

theorem cg_C_cT (I : AutInst) {α β : Type} {c : ℕ} {A : Matrix α β (I.E ⊗[I.F] Af I.F)}
    (h : cg_C (IntAf I.F I.E) c A) :
    cg_C (IntAf I.F I.E) c (Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) A) := by
  have hle : IntAf I.F I.E ≤ (IntAf I.F I.E).comap (Formalism.UG.sigR I.cm.sig (Af I.F)) := by
    show Formalism.UG.tensInt (F := I.F) (Af I.F) (Formalism.UG.intOE I.E) (Formalism.UG.intAd I.F) ≤ _
    unfold Formalism.UG.tensInt
    rw [Subring.closure_le]
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨z, rfl⟩ := hx
      rw [SetLike.mem_coe, Subring.mem_comap]
      apply Subring.subset_closure
      left
      exact ⟨⟨algebraMap (𝓞 I.E) I.E (NumberField.RingOfIntegers.mapRingHom (I.cm.sig : I.E →+* I.E) z),
        ⟨_, rfl⟩⟩, rfl⟩
    · rw [SetLike.mem_coe, Subring.mem_comap]
      apply Subring.subset_closure
      right
      exact ⟨⟨y, hy⟩, by simp [Formalism.UG.sigR]⟩
  intro i j
  obtain ⟨t, ht, hA⟩ := h j i
  refine ⟨Formalism.UG.sigR I.cm.sig (Af I.F) t, hle ht, ?_⟩
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hA, map_mul, map_natCast]

theorem cg_cT_sub (I : AutInst) {α β : Type} (A B : Matrix α β (I.E ⊗[I.F] Af I.F)) :
    Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (A - B) =
      Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) A - Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) B := by
  ext i j
  simp [Formalism.UG.cT, map_sub]

theorem cg_map_cT {α β : Type} (M : Matrix α β X.B.I.E) :
    (Mᴴ).map (ic X) = Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) (M.map (ic X)) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.conjTranspose_apply, Formalism.UG.cT, Matrix.transpose_apply]
  rfl

theorem cg_half : ic X (⅟2 : X.B.I.E) = (⅟2 : RA X) := by
  refine (invOf_eq_right_inv ?_).symm
  rw [← map_ofNat (ic X) 2, ← map_mul, mul_invOf_self, map_one]

theorem cg_JJ : (JB' X).map (ic X) * JBf X = 1 := by
  unfold JBf
  rw [← Matrix.map_mul, JB'_mul_JB]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem cg_proj_map (W : Matrix (Kap X) (Kap X) X.B.I.E) :
    (proj (JB X) (JB' X) W).map (ic X) = (⅟2 : RA X) • (W.map (ic X) - (JB' X).map (ic X) *
      Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) (W.map (ic X)) * JBf X) := by
  have e1 : (JB' X * Wᴴ * JB X).map (ic X) =
      (JB' X).map (ic X) * Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) (W.map (ic X)) * JBf X := by
    rw [Matrix.map_mul, Matrix.map_mul, cg_map_cT]
    unfold JBf
    rfl
  ext i j
  have e2 := congrFun (congrFun e1 i) j
  simp only [Matrix.map_apply] at e2
  simp only [proj, sharp, Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, map_mul,
    map_sub, cg_half, e2]

end Skew

theorem skew_hermitian_approximation : SkewApprox := by
  intro D X Z hZ hskew c hc
  obtain ⟨mJ, hmJ, hJ⟩ := cg_D_exists (JBf X)
  obtain ⟨mJ', hmJ', hJ'⟩ := cg_D_exists ((JB' X).map (ic X))
  obtain ⟨W, hW, hWZ⟩ := cg_approx_mat (lvk X) Z hZ (2 * c * mJ * mJ')
    (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos two_pos hc) hmJ) hmJ')
  refine ⟨proj (JB X) (JB' X) W, inPat_proj (JB_graded X) (JB'_graded X) hW,
    proj_skew (JB_herm X) (JB'_herm X) (JB'_mul_JB X) (JB_mul_JB' X) W, ?_⟩
  have hJZ : (JB' X).map (ic X) * Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) Z * JBf X = -Z := by
    rw [Matrix.mul_assoc, hskew, Matrix.mul_neg, ← Matrix.mul_assoc, cg_JJ, Matrix.one_mul]
  have habel : ∀ P Q S : Matrix (Kap X) (Kap X) (RA X), P - S - (Q - -S) = (P - Q) - (S + S) := by
    intro P Q S; abel
  have hhalf : (⅟2 : RA X) • (Z + Z) = Z := by
    rw [← two_smul (RA X) Z, smul_smul, invOf_mul_self, one_smul]
  have e : (proj (JB X) (JB' X) W).map (ic X) - Z = (⅟2 : RA X) • ((W.map (ic X) - Z) -
      (JB' X).map (ic X) * Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) (W.map (ic X) - Z) * JBf X) := by
    rw [cg_proj_map, cg_cT_sub, Matrix.mul_sub, Matrix.sub_mul, hJZ, habel, smul_sub _ _ (Z + Z), hhalf]
  show cg_C (IntAf X.B.I.F X.B.I.E) c _
  rw [e]
  refine cg_C_half (cg_C_sub (cg_C_dvd (k := mJ) (cg_C_dvd (k := mJ') hWZ)) ?_)
  exact cg_C_mul_right (cg_C_mul_left hJ' (cg_C_cT X.B.I hWZ)) hJ

end Formalism.L2.SG.Pf.SlabNDensePf
end
end

