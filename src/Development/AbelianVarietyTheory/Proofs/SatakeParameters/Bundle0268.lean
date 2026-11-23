module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteOrderValuation.WeakApprox
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0261
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiAtCongInvariant
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MomentsCosetSum
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaMovedCosetIndicatorVacuumShape
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0172
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetsRightTranslateInFramesTypePrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CplCosetPt

section Gen

variable {E : Type} [Field E] [NumberField E]

theorem intAt_of_val_le (P : HeightOneSpectrum (𝓞 E)) (x : E) (h : P.valuation E x ≤ 1) :
    Formalism.L2.Col.IntAt P x := by
  obtain ⟨n, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer x h
  exact ⟨n, d, d.2, by rw [mul_comm]; exact h⟩

theorem lin_apply_eq_sum {n : ℕ} (g : (Fin n → E) →ₗ[E] (Fin n → E)) (w : Fin n → E) (l : Fin n) :
    g w l = ∑ k, w k * g (Pi.single k 1) l := by
  conv_lhs => rw [LinearMap.pi_apply_eq_sum_univ g w]
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  rw [show (fun j => if k = j then (1 : E) else 0) = Pi.single k 1 by funext j; simp [Pi.single_apply, eq_comm]]

theorem exists_approx_at (T : Finset (HeightOneSpectrum (𝓞 E))) {n : ℕ} (g : T → (Fin n → E) →ₗ[E] (Fin n → E))
    (c : T → E) (t : T → Fin n → E) :
    ∃ d : Fin n → E, ∀ P : T, ∀ l, (P.1).valuation E (c P * g P (d - t P) l) ≤ 1 := by
  classical
  have hb : ∀ P : T, ∃ b : WithZero (Multiplicative ℤ), 1 ≤ b ∧
      ∀ l k, (P.1).valuation E (c P * g P (Pi.single k 1) l) ≤ b := by
    intro P
    obtain ⟨b, hb⟩ := (Set.finite_range fun lk : Fin n × Fin n =>
      (P.1).valuation E (c P * g P (Pi.single lk.2 1) lk.1)).bddAbove
    exact ⟨max b 1, le_max_right _ _, fun l k => (hb ⟨(l, k), rfl⟩).trans (le_max_left _ _)⟩
  choose B hB1 hBle using hb
  have hB0 : ∀ P, B P ≠ 0 := fun P => (lt_of_lt_of_le zero_lt_one (hB1 P)).ne'
  have hk : ∀ k : Fin n, ∃ a : E, ∀ P : T, (P.1).valuation E (a - t P k) < (B P)⁻¹ := by
    intro k
    obtain ⟨a, -, ha, -⟩ := PI.FinOrdValD.WA.weakApprox T
      (fun v => if h : v ∈ T then algebraMap E (v.adicCompletion E) (t ⟨v, h⟩ k) else 0)
      (fun v => if h : v ∈ T then (B ⟨v, h⟩)⁻¹ else 1)
      (fun v hv => by simp only [dif_pos hv]; exact inv_ne_zero (hB0 _))
    refine ⟨a, fun P => ?_⟩
    have h := ha P.1 P.2
    simp only [dif_pos P.2, Subtype.coe_eta] at h
    rw [← map_sub, PI.FinOrdValD.WA.val_alg] at h
    exact h
  choose a ha using hk
  refine ⟨a, fun P l => ?_⟩
  rw [lin_apply_eq_sum, Finset.mul_sum]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [show c P * ((a - t P) k * g P (Pi.single k 1) l) = (a - t P) k * (c P * g P (Pi.single k 1) l) by ring,
    map_mul, Pi.sub_apply]
  calc (P.1).valuation E (a k - t P k) * (P.1).valuation E (c P * g P (Pi.single k 1) l)
      ≤ (B P)⁻¹ * B P := mul_le_mul' (ha k P).le (hBle P l k)
    _ = 1 := inv_mul_cancel₀ (hB0 P)

end Gen

theorem exists_sameCoset_frames {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {n : ℕ} (f : rowSG Pr sel mu → (Sp X.E n ≃ₗ[X.E] Sp X.E n))
    (y0 : rowSG Pr sel mu → Sp X.E n) :
    ∃ y : Sp X.E n, ∀ P, SameCoset sel mu cst P ((f P).symm y) (y0 P) := by
  classical
  obtain ⟨d, hd⟩ := exists_approx_at (rowSG Pr sel mu) (fun P => ((f P).symm : Sp X.E n →ₗ[X.E] Sp X.E n))
    (fun P => (((qOf P.1 : ℕ) : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹) (fun P => f P (y0 P))
  refine ⟨d, fun P l => intAt_of_val_le _ _ ?_⟩
  have h := hd P l
  have e : (f P).symm d - y0 P = (f P).symm (d - f P (y0 P)) := by
    rw [map_sub, LinearEquiv.symm_apply_apply]
  rw [e]
  exact h

end GlobalTheory.CplCosetPt

namespace GlobalTheory.CplCosetPt

theorem sameCoset_loc {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (e₀ e D : ℕ) (c g : Sp E n ≃ₗ[E] Sp E n) (k : GLint E n P) (hc : c ∈ GLint E n P) (hg : g ∈ GLint E n P)
    (hk : k ∈ GlobalTheory.TopStep.prinCong n P D) (hck : c⁻¹ = g * k.1) (hD : e + e₀ ≤ D) (y₀ : Sp E n)
    (hy₀ : ∀ l, IntAt P ((qOf P : E) ^ e * y₀ l)) (hgy : ∀ l, IntAt P (((qOf P : E) ^ e₀)⁻¹ * (g y₀ - y₀) l)) (y : Sp E n) :
    (∀ l, IntAt P (((qOf P : E) ^ e₀)⁻¹ * (c y - y₀) l)) ↔ (∀ l, IntAt P (((qOf P : E) ^ e₀)⁻¹ * (y - y₀) l)) := by
  have hq : ((qOf P : ℕ) : E) ≠ 0 := by
    have : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  set q : E := ((qOf P : ℕ) : E) with hqdef
  have hsm : ∀ (a : E) (v : Sp E n), (∀ l, IntAt P (a * v l)) ↔ a • v ∈ stdAt E n P := by
    intro a v
    rw [GlobalTheory.TopStep.mem_stdAt]
    rfl
  have hpow : ∀ (m : ℕ) (v : Sp E n), v ∈ stdAt E n P → q ^ m • v ∈ stdAt E n P := by
    intro m v hv
    have : q ^ m • v = ((qOf P : 𝓞 E) ^ m) • v := by
      rw [← algebraMap_smul E ((qOf P : 𝓞 E) ^ m) v]
      congr 1 <;> simp [hqdef]
    rw [this]
    exact Submodule.smul_mem _ _ hv
  have hw : q ^ e • y₀ ∈ stdAt E n P := (hsm _ _).1 hy₀
  have hkw := hk _ hw
  have hky : (q ^ e₀)⁻¹ • (k.1 y₀ - y₀) ∈ stdAt E n P := by
    obtain ⟨d, hd⟩ : ∃ d, D = d + e + e₀ := ⟨D - e - e₀, by omega⟩
    have e1 : (q ^ e₀)⁻¹ • (k.1 y₀ - y₀) = q ^ d • ((q ^ D)⁻¹ • (k.1 (q ^ e • y₀) - q ^ e • y₀)) := by
      rw [map_smul, ← smul_sub, smul_smul, smul_smul]
      congr 1
      rw [hd, pow_add, pow_add]
      field_simp
    rw [e1]
    exact hpow _ _ hkw
  have hcy : (q ^ e₀)⁻¹ • (c⁻¹ y₀ - y₀) ∈ stdAt E n P := by
    have e2 : c⁻¹ y₀ - y₀ = g (k.1 y₀ - y₀) + (g y₀ - y₀) := by
      rw [hck, LinearEquiv.mul_apply, map_sub]
      abel
    rw [e2, smul_add, ← map_smul]
    exact add_mem ((hg _).2 hky) ((hsm _ _).1 hgy)
  have hcc : ∀ x, c (c⁻¹ x) = x := fun x => by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  rw [hsm, hsm]
  have e3 : (q ^ e₀)⁻¹ • (c y - y₀) = c ((q ^ e₀)⁻¹ • (y - y₀) - (q ^ e₀)⁻¹ • (c⁻¹ y₀ - y₀)) := by
    rw [← smul_sub, map_smul]
    simp only [map_sub, hcc]
    congr 1
    abel
  rw [e3, hc]
  exact Submodule.sub_mem_iff_left _ hcy

theorem mem_prinCong_one_of_redGL {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (j : GLint E n P) (hj : redGL n P j = 1) : j ∈ prinCong n P 1 := by
  intro x hx
  rw [mem_stdAt]
  intro i
  have hjx := mem_stdAt.1 (glint_mem j hx) i
  have hxi := mem_stdAt.1 hx i
  have hr : redP P (j.1 x i) = redP P (x i) := by
    have h := congrFun (redV_redGL j hx) i
    rw [hj, Units.val_one, Matrix.one_mulVec] at h
    exact h
  have hred : redP P (j.1 x i - x i) = 0 := by
    rw [reduction_sub hjx hxi, hr, sub_self]
  have h := intAt_div_of_redP hq (intAt_sub hjx hxi) hred
  have e : (((qOf P : E) ^ 1)⁻¹ • (j.1 x - x)) i = (j.1 x i - x i) / (qOf P : E) := by
    simp [div_eq_inv_mul]
  rw [e]
  exact h

theorem cosetOf_frames_vG : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1))
    (P : SB t μ), P.1 ∈ t.Pr.vGs → ∀ (Gg k : GLint t.X.E (D.R.N (t.m2 + 1)) P.1) z, A.cplRel β P Gg.1 z →
    redGL _ P.1 k = redGL _ P.1 Gg → frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k.1 →
    (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) l)) ∧
    (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * (frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) l)) ∧
    k.1 ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁))) -
      (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) ∈ stdAt t.X.E _ P.1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin H hi β p p₁ P hP Gg k z hrel hred _hfr
  classical
  have hne : ∀ q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1),
      repY (cosetOf A (t.m2 + 1) hi β q) ∈ cosetOf A (t.m2 + 1) hi β q := by
    intro q
    obtain ⟨y, hy⟩ := exists_sameCoset_frames t.sel (t.tup μ) (t.cst μ) (fun P => frsF t.sel (t.tup μ) q P)
      (fun P => y0At A (t.m2 + 1) hi β P)
    exact Classical.epsilon_spec (p := fun y => y ∈ cosetOf A (t.m2 + 1) hi β q) ⟨y, hy⟩
  have hyy : y0At A (t.m2 + 1) hi β P = A.y0 β P := by
    unfold y0At
    rw [dif_pos rfl]
  have hloc : ∀ q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1), ∀ l,
      IntAt P.1 (((qOf P.1 : t.X.E) ^ 0)⁻¹ * ((frsF t.sel (t.tup μ) q P).symm (repY (cosetOf A (t.m2 + 1) hi β q)) - A.y0 β P) l) := by
    intro q
    have h := hne q P
    unfold SameCoset at h
    simpa only [hP, if_true, hyy] using h
  have hy₀ : ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) ^ 1 * A.y0 β P l) := by
    intro l
    have h := GlobalTheory.T.intAt_scaled_baseCosetRep_of_adTie D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin H β P l
    simpa only [hP, if_true] using h
  have hqI : IntAt P.1 (qOf P.1 : t.X.E) := by
    simpa using IntAt.coe P.1 ((qOf P.1 : ℕ) : 𝓞 t.X.E)
  have hint : ∀ q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1), ∀ l,
      IntAt P.1 ((qOf P.1 : t.X.E) * (frsF t.sel (t.tup μ) q P).symm (repY (cosetOf A (t.m2 + 1) hi β q)) l) := by
    intro q l
    have h1 := hqI.mul (hloc q l)
    have e : (qOf P.1 : t.X.E) * (frsF t.sel (t.tup μ) q P).symm (repY (cosetOf A (t.m2 + 1) hi β q)) l =
        (qOf P.1 : t.X.E) * (((qOf P.1 : t.X.E) ^ 0)⁻¹ * ((frsF t.sel (t.tup μ) q P).symm (repY (cosetOf A (t.m2 + 1) hi β q)) - A.y0 β P) l) +
          (qOf P.1 : t.X.E) ^ 1 * A.y0 β P l := by
      simp only [pow_zero, inv_one, one_mul, pow_one, Pi.sub_apply]
      ring
    rw [e]
    exact h1.add (hy₀ l)
  refine ⟨hint p, hint p₁, ?_⟩
  have hgy : ∀ l, IntAt P.1 (((qOf P.1 : t.X.E) ^ 0)⁻¹ * (Gg.1 (A.y0 β P) - A.y0 β P) l) := by
    have h := hrel.2
    unfold SameCoset at h
    simpa only [hP, if_true] using h
  have hj : Gg⁻¹ * k ∈ prinCong _ P.1 1 := by
    refine mem_prinCong_one_of_redGL (qOf_notMem_sq hPin.fields.ok t.pr_ok hP) _ ?_
    rw [map_mul, map_inv, hred, inv_mul_cancel]
  have hck : (k.1⁻¹)⁻¹ = Gg.1 * (Gg⁻¹ * k).1 := by
    rw [inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  have key := (sameCoset_loc P.1 0 1 1 k.1⁻¹ Gg.1 (Gg⁻¹ * k) (inv_mem k.2) Gg.2 hj hck (by omega) (A.y0 β P) hy₀ hgy
    (k.1 ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁))))).1 (by
      intro l
      have e : (k.1⁻¹) (k.1 ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)))) =
          (frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) := k.1.symm_apply_apply _
      rw [e]
      exact hloc p₁ l)
  rw [mem_stdAt]
  intro l
  have e : (k.1 ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁))) -
      (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p))) l =
      ((qOf P.1 : t.X.E) ^ 0)⁻¹ * (k.1 ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁))) - A.y0 β P) l -
      ((qOf P.1 : t.X.E) ^ 0)⁻¹ * ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) - A.y0 β P) l := by
    simp only [pow_zero, inv_one, one_mul, Pi.sub_apply]
    ring
  rw [e]
  exact intAt_sub (key l) (hloc p l)

end GlobalTheory.CplCosetPt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetInvMulFrameReadingCongruentOneModNorm
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
open GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.FramesDet

open Matrix
open scoped TensorProduct

section Cong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
  {P : HeightOneSpectrum (𝓞 E)}

def intAtSub (P : HeightOneSpectrum (𝓞 E)) :
    Subring (E ⊗[F] FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | IntAtA (F := F) P a}
  mul_mem' := GlobalTheory.CplPt.intAtA_mul
  one_mem' := by simpa using GlobalTheory.CplPt.intAtA_int (F := F) (P := P) 1
  add_mem' := GlobalTheory.CplPt.intAtA_add
  zero_mem' := by simpa using GlobalTheory.CplPt.intAtA_int (F := F) (P := P) 0
  neg_mem' := by
    intro a ha
    have := GlobalTheory.CplPt.intAtA_mul (GlobalTheory.CplPt.intAtA_int (F := F) (P := P) (-1)) ha
    simpa using this

theorem det_congAt {d : ℕ} (hd : 1 ≤ d) {k : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (h : CongAt P d k) :
    IntAtA (F := F) P (iA F E ((qOf P : ℕ) : E)⁻¹ *
      (((Matrix.GeneralLinearGroup.det k : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) - 1)) := by
  classical
  set S := intAtSub (F := F) P with hS
  have hq : ((qOf P : ℕ) : E) ≠ 0 := by
    have : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  set Q := iA F E ((qOf P : ℕ) : E) with hQ
  have hcQ : iA F E ((qOf P : ℕ) : E)⁻¹ * Q = 1 := by rw [hQ, ← map_mul, inv_mul_cancel₀ hq, map_one]
  have hQS : Q ∈ S := by
    have := GlobalTheory.CplPt.intAtA_int (F := F) (P := P) ((qOf P : ℕ) : 𝓞 E)
    simpa [hQ] using this
  have hZ : ∀ a b, Q ^ (d - 1) * (iA F E (((qOf P : ℕ) : E) ^ d)⁻¹ *
      ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b) ∈ S :=
    fun a b => S.mul_mem (S.pow_mem hQS _) (h a b)
  have hZe : ∀ a b, Q * (Q ^ (d - 1) * (iA F E (((qOf P : ℕ) : E) ^ d)⁻¹ *
      ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b)) =
      ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b := by
    intro a b
    have e : Q * Q ^ (d - 1) * iA F E (((qOf P : ℕ) : E) ^ d)⁻¹ = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hd, hQ, ← map_pow, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one]
    rw [← mul_assoc, ← mul_assoc, e, one_mul]
  let Z : Matrix (Fin N) (Fin N) S := fun a b => ⟨_, hZ a b⟩
  let q' : S := ⟨Q, hQS⟩
  let M : Matrix (Fin N) (Fin N) S := 1 + q' • Z
  have hM : M.map S.subtype = (k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := by
    ext a b
    have e1 : S.subtype ((1 : Matrix (Fin N) (Fin N) S) a b) = (1 : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [Matrix.map_apply]
    simp only [M]
    rw [Matrix.add_apply, map_add (f := _), e1, Matrix.smul_apply, smul_eq_mul, map_mul]
    show _ + Q * (Q ^ (d - 1) * _) = _
    rw [hZe, Matrix.sub_apply]
    ring_nf
  set I : Ideal S := Ideal.span {q'}
  have hMI : M.map (Ideal.Quotient.mk I) = 1 := by
    ext a b
    have hq0 : Ideal.Quotient.mk I q' = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    rw [Matrix.map_apply]
    simp only [M]
    rw [Matrix.add_apply, map_add (f := _), Matrix.smul_apply, smul_eq_mul, map_mul, hq0, zero_mul, add_zero,
      Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : Ideal.Quotient.mk I M.det = Ideal.Quotient.mk I 1 := by
    rw [RingHom.map_det, map_one]
    show (M.map (Ideal.Quotient.mk I)).det = 1
    rw [hMI, Matrix.det_one]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hdet)
  have hk : ((Matrix.GeneralLinearGroup.det k : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) =
      S.subtype M.det := by
    rw [RingHom.map_det, Matrix.GeneralLinearGroup.val_det_apply]
    exact congrArg Matrix.det hM.symm
  have e2 : iA F E ((qOf P : ℕ) : E)⁻¹ *
      (((Matrix.GeneralLinearGroup.det k : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) - 1) = (w : _) := by
    rw [hk, show S.subtype M.det - 1 = S.subtype (M.det - 1) by simp, ← hw, map_mul]
    show iA F E ((qOf P : ℕ) : E)⁻¹ * ((w : _) * Q) = _
    rw [mul_comm (w : E ⊗[F] FiniteAdeleRing (𝓞 F) F), ← mul_assoc, hcQ, one_mul]
  rw [e2]
  exact w.2

end Cong

section Rat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem det_ratA (g : GL (Fin n) E) :
    ((Matrix.GeneralLinearGroup.det (ratA F g) : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) =
      iA F E ((Matrix.GeneralLinearGroup.det g : Eˣ) : E) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rfl

end Rat

section Frame

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Fields} (s : Seam D X)

theorem det_seamGL {n : ℕ} (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) :
    ((Matrix.GeneralLinearGroup.det (seamGL s g) : D.host.Eˣ) : D.host.E) = s.iE ((LinearEquiv.det g : X.Eˣ) : X.E) := by
  have h : ((seamGL s g : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) =
      (LinearMap.toMatrix' g.toLinearMap).map (s.iE : X.E →+* D.host.E) := rfl
  rw [Matrix.GeneralLinearGroup.val_det_apply, h, ← RingHom.mapMatrix_apply, ← RingHom.map_det, LinearMap.det_toMatrix',
    LinearEquiv.coe_det]
  rfl

variable {i : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} (fb : SB → GL (Fin (D.R.N i)) D.host.E) (dep : SB → ℕ)

theorem det_inFrame {P : SB} {κ : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    {g : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)} (hd : 1 ≤ dep P) (h : InFrame s fb dep P κ g) :
    IntAtA (F := D.host.F) (seamP s P.1) (iA D.host.F D.host.E ((qOf (seamP s P.1) : D.host.E))⁻¹ *
      ((((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det g : X.Eˣ) : X.E)) - 1)) := by
  have H := det_congAt hd h
  have e : ((Matrix.GeneralLinearGroup.det (((ratA D.host.F (fb P))⁻¹ * κ * ratA D.host.F (fb P))⁻¹ *
      ratA D.host.F (seamGL s g)) : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) =
      (((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det g : X.Eˣ) : X.E)) := by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, Units.val_mul, det_ratA, det_seamGL]
    congr 2
    rw [mul_comm, mul_inv_cancel_left]
  rw [← e]
  exact H

theorem det_inFrame_mul {P : SB} (hd : 1 ≤ dep P)
    (κ : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (g C : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)) (h : InFrame s fb dep P κ g)
    (hC : CongAt (F := D.host.F) (seamP s P.1) (dep P) (ratA D.host.F (seamGL s C))) :
    IntAtA (F := D.host.F) (seamP s P.1) (iA D.host.F D.host.E ((qOf (seamP s P.1) : D.host.E))⁻¹ *
      ((((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det (g * C) : X.Eˣ) : X.E)) - 1)) := by
  have hα := det_inFrame s fb dep hd h
  have hβ := det_congAt hd hC
  rw [det_ratA, det_seamGL] at hβ
  set U := (((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E)
  set G := iA D.host.F D.host.E (s.iE ((LinearEquiv.det g : X.Eˣ) : X.E))
  set W := iA D.host.F D.host.E (s.iE ((LinearEquiv.det C : X.Eˣ) : X.E))
  set qi := iA D.host.F D.host.E ((qOf (seamP s P.1) : D.host.E))⁻¹
  set Q := iA D.host.F D.host.E ((qOf (seamP s P.1) : D.host.E))
  have hq : ((qOf (seamP s P.1) : ℕ) : D.host.E) ≠ 0 := by
    have : qOf (seamP s P.1) ≠ 0 := fun h0 => (seamP s P.1).ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  have hcQ : qi * Q = 1 := by
    simp only [qi, Q]; rw [← map_mul, inv_mul_cancel₀ hq, map_one]
  have hQ : IntAtA (F := D.host.F) (seamP s P.1) Q := by
    have := GlobalTheory.CplPt.intAtA_int (F := D.host.F) (P := seamP s P.1) ((qOf (seamP s P.1) : ℕ) : 𝓞 D.host.E)
    simpa [Q] using this
  have hdet : iA D.host.F D.host.E (s.iE ((LinearEquiv.det (g * C) : X.Eˣ) : X.E)) = G * W := by
    simp only [G, W]; rw [map_mul, Units.val_mul, map_mul, map_mul]
  have hW : W = Q * (qi * (W - 1)) + 1 := by
    linear_combination (1 - W) * hcQ
  have hWi : IntAtA (F := D.host.F) (seamP s P.1) W := by
    rw [hW]
    exact GlobalTheory.CplPt.intAtA_add (GlobalTheory.CplPt.intAtA_mul hQ hβ) (by simpa using GlobalTheory.CplPt.intAtA_int (F := D.host.F) (P := seamP s P.1) 1)
  have e : qi * (U * (G * W) - 1) = qi * (U * G - 1) * W + qi * (W - 1) := by ring
  rw [hdet, e]
  exact GlobalTheory.CplPt.intAtA_add (GlobalTheory.CplPt.intAtA_mul hα hWi) hβ

end Frame

end GlobalTheory.FramesDet

theorem GlobalTheory.FramesDet.det_frame_mul_congAt : ∀ {D : D7} {X : Fields} (s : Seam D X) {i : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 X.E))}
    (fb : SB → GL (Fin (D.R.N i)) D.host.E) (dep : SB → ℕ) (P : SB), 1 ≤ dep P →
    ∀ (κ : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (g C : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)), InFrame s fb dep P κ g →
    CongAt (F := D.host.F) (seamP s P.1) (dep P) (ratA D.host.F (seamGL s C)) →
    IntAtA (F := D.host.F) (seamP s P.1) (iA D.host.F D.host.E ((qOf (seamP s P.1) : D.host.E))⁻¹ *
      ((((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det (g * C) : X.Eˣ) : X.E)) - 1)) := by
  intro D X s i SB fb dep P hd κ g C h hC
  exact GlobalTheory.FramesDet.det_inFrame_mul s fb dep hd κ g C h hC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetLossOfFamilyFacts
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.MomT
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recSeam HostTie AnTie badS)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver)
open GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable (jetSum RatIdx)
open GlobalTheory.LiftTypePrime.Jets (intAt_mul intAt_sum intAt_of_isIntegral isIntegral_exp)
open GlobalTheory.MomT.CosetSum

noncomputable section

namespace GlobalTheory.DatumJets

section Int

variable {p : ℕ} [Fact p.Prime] {lam : TaylorLogMetric.Qbar →+* ℂ_[p]}

end Int

section Idx

variable {X : Fields} {a b : ℕ}

end Idx

theorem map_jetSum {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E))) {cA c : ℕ}
    {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)} (hN : IsSdLat N) (hN' : IsSdLat N')
    (hcA0 : 0 < cA) (hc0 : 0 < c) (Ξ : HomE X.E a b → X.K) {e : DVar X.Tau a b →₀ ℕ} (he : e ∈ RatIdx A S cA c N N' Ξ) :
    A.σ₀ (jetSum A S cA c N N' Ξ e) = (A.chiF a b N N')⁻¹ *
      latSum (divLat cA (homAt S N N')) (mulLat c (homAt S N N')) fun x => A.σ₀ (Ξ x) * jetC A.cD (A.thInd S N N' c x) e := by
  have := GlobalTheory.MomT.finite_quot_divLat_mulLat_homAt X.E a b S N N' cA c hN.1 hN'.1 hcA0 hc0
  have := Fintype.ofFinite (↥(divLat cA (homAt S N N')) ⧸ (mulLat c (homAt S N N')).comap (divLat cA (homAt S N N')).subtype)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [jetSum, latSum, latSum, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  generalize Function.surjInv (Submodule.Quotient.mk_surjective _) z = x
  by_cases h0 : Ξ x = 0
  · simp [h0]
  · have h := he x x.2 h0
    rw [map_mul, Amb.jetK, desc, dite_eq_left h, h.choose_spec]
    ring

end GlobalTheory.DatumJets
end
end

