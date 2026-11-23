module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0084
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TendstoRatioPow
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0085

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepPolyFinish
section
open Polynomial

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC

theorem pf_conj_eval' (q : ℂ[X]) (x : ℝ) :
    (q.map (starRingEnd ℂ)).eval (x : ℂ) = starRingEnd ℂ (q.eval (x : ℂ)) := by
  rw [Polynomial.eval_map]
  have hx : (x : ℂ) = starRingEnd ℂ (x : ℂ) := (Complex.conj_ofReal x).symm
  conv_lhs => rw [hx]
  exact Polynomial.eval₂_at_apply _ _

theorem pf_id (q : ℂ[X]) (n : ℕ) (a C : ℝ)
    (h : ∀ x : ℝ, a < x → Complex.normSq (q.eval (x : ℂ)) = C * (x - a) ^ (2 * n)) :
    q * q.map (starRingEnd ℂ) = Polynomial.C (C : ℂ) * (X - Polynomial.C (a : ℂ)) ^ (2 * n) := by
  have hroots : Set.Infinite {z : ℂ | IsRoot (q * q.map (starRingEnd ℂ) -
      Polynomial.C (C : ℂ) * (X - Polynomial.C (a : ℂ)) ^ (2 * n)) z} := by
    refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => ((a + 1 + m : ℝ) : ℂ)) ?_ ?_
    · intro s t hst
      have := Complex.ofReal_injective hst
      exact_mod_cast (by linarith : (s : ℝ) = t)
    · intro m
      simp only [Set.mem_ofPred_eq, IsRoot, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
      have hx : a < a + 1 + (m : ℝ) := by have := m.cast_nonneg (α := ℝ); linarith
      rw [pf_conj_eval', Complex.mul_conj, h _ hx]
      push_cast
      ring
  exact sub_eq_zero.1 (Polynomial.eq_zero_of_infinite_isRoot _ hroots)

theorem polynomial_finish_holds : PolyFinish := by
  intro q n a C h
  have hid := pf_id q n a C h
  by_cases hq : q = 0
  · exact ⟨0, by simp [hq]⟩
  have hqb : q.map (starRingEnd ℂ) ≠ 0 := by
    rwa [Ne, Polynomial.map_eq_zero_iff (RingHom.injective _)]
  have hC : (C : ℂ) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.C_0, zero_mul] at hid
    exact mul_ne_zero hq hqb hid
  have hroot : ∀ b ∈ q.roots, b = (a : ℂ) := by
    intro b hb
    have hb0 : q.eval b = 0 := (Polynomial.mem_roots hq).1 hb
    have := congrArg (Polynomial.eval b) hid
    simp only [eval_mul, hb0, zero_mul, eval_C, eval_pow, eval_sub, eval_X] at this
    have h2 := (mul_eq_zero.1 this.symm).resolve_left hC
    exact sub_eq_zero.1 (pow_eq_zero_iff'.1 h2).1
  have hcard : Multiset.card q.roots = q.natDegree := by
    first
      | exact (Polynomial.natDegree_eq_card_roots' (IsAlgClosed.splits q)).symm
      | exact IsAlgClosed.card_roots_eq_natDegree
  have hrep : q.roots = Multiset.replicate q.natDegree (a : ℂ) := by
    rw [← hcard]; exact Multiset.eq_replicate.2 ⟨rfl, hroot⟩
  have hform : q = Polynomial.C q.leadingCoeff * (X - Polynomial.C (a : ℂ)) ^ q.natDegree := by
    conv_lhs => rw [← Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard]
    rw [hrep, Multiset.map_replicate, Multiset.prod_replicate]
  have hdeg : q.natDegree = n := by
    have h1 := congrArg Polynomial.natDegree hid
    rw [Polynomial.natDegree_mul hq hqb, Polynomial.natDegree_map_eq_of_injective (RingHom.injective _),
      Polynomial.natDegree_C_mul hC, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C] at h1
    omega
  exact ⟨q.leadingCoeff, by rw [← hdeg]; exact hform⟩

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThConstAsm
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC

noncomputable section

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem tc_hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  ext i
  simp

theorem tc_hsVec_eq_zero {A : Wq →L[ℂ] Wp} (h : B.hsVec A = 0) : A = 0 := by
  have h' : ∀ i, A (stdOrthonormalBasis ℂ Wq i) = 0 := fun i => by
    have := congrArg (fun w => w i) h
    simpa [B.hsVec] using this
  have hl : A.toLinearMap = (0 : Wq →ₗ[ℂ] Wp) :=
    (stdOrthonormalBasis ℂ Wq).toBasis.ext fun i => by simpa using h' i
  ext v
  exact LinearMap.congr_fun hl v

end hs

theorem tc_up_unique {P : M.Par} {l : ℕ} {π ρ ρ' : M.Ty P} (h : M.Up P l π ρ) (h' : M.Up P l π ρ') : ρ = ρ' := by
  funext i
  apply Fin.ext
  rw [h i, h' i]

theorem theta_constancy_assembly : ThConstOfCut := by
  intro hPR hMC hLN hPF
  intro Wp Wq _ _ _ _ _ _ P Bs hk X d hAct l hl S hS Pr hPr Bw Bw' hBw hBw'
  have main : ∀ π ρ : M.Ty P, M.Up P l π ρ → ∃ c : ℂ, ∀ ζ ∈ Gauge.GC.Ann P,
      ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
        (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf →
        (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Xf) =
          c • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp
            (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf) := by
    intro π ρ hup
    obtain ⟨n, q, hq⟩ := hPR Wp Wq P Bs hk X d hAct l hl S hS Pr hPr Bw Bw' hBw hBw' π ρ hup
    obtain ⟨c₁, c₂, hc⟩ := hMC Wp Wq P Bs hk X d hAct l hl S hS Pr hPr Bw Bw' hBw hBw' π ρ hup
    have hGG : ∀ ζ ∈ Gauge.GC.Ann P, (((Complex.normSq ζ - P.TT : ℝ) : ℂ) ^ n) ≠ 0 := by
      intro ζ hζ
      have : (0 : ℝ) < Complex.normSq ζ - P.TT := by
        have := hζ; simp only [Gauge.GC.Ann, Set.mem_ofPred_eq] at this; linarith
      exact pow_ne_zero _ (by exact_mod_cast this.ne')
    by_cases hc2 : c₂ = 0
    · refine ⟨0, fun ζ hζ Xf hXf hfix => ?_⟩
      have hB0 := (hc ζ hζ Xf hXf hfix).2
      rw [hc2, zero_mul, sq_eq_zero_iff, norm_eq_zero] at hB0
      have hB0' := tc_hsVec_eq_zero hB0
      have h1 := hq ζ hζ Xf hXf hfix
      rw [hB0', smul_zero] at h1
      rw [zero_smul]
      exact (smul_eq_zero.1 h1).resolve_left (hGG ζ hζ)
    ·
      have hTT : 0 ≤ P.TT := by
        have := hAct.1.1
        exact mul_nonneg this.T_pos.le this.T'_pos.le
      have hmod : ∀ x : ℝ, P.TT < x → Complex.normSq (q.eval (x : ℂ)) = (c₁ / c₂) * (x - P.TT) ^ (2 * n) := by
        intro x hx
        have hx0 : 0 ≤ x := le_trans hTT hx.le
        set ζ : ℂ := ((Real.sqrt x : ℝ) : ℂ) with hζdef
        have hnz : Complex.normSq ζ = x := by
          rw [hζdef, Complex.normSq_ofReal, ← sq, Real.sq_sqrt hx0]
        have hζ : ζ ∈ Gauge.GC.Ann P := by
          show P.TT < Complex.normSq ζ
          rw [hnz]; exact hx
        obtain ⟨Xf, hXf, hfix, hne⟩ := hLN Wp Wq P Bs hAct.1 hk Pr hPr π ζ hζ
        obtain ⟨hS1, hB1⟩ := hc ζ hζ Xf hXf hfix
        have h1 := congrArg (fun w => ‖B.hsVec w‖ ^ 2) (hq ζ hζ Xf hXf hfix)
        simp only [tc_hsVec_smul, norm_smul, mul_pow] at h1
        rw [hS1, hB1, hnz] at h1
        have hX : 0 < ‖B.hsVec Xf‖ ^ 2 := by
          have : B.hsVec Xf ≠ 0 := fun h0 => hne (tc_hsVec_eq_zero h0)
          positivity
        have hnq : ‖q.eval ((x : ℝ) : ℂ)‖ ^ 2 = Complex.normSq (q.eval (x : ℂ)) := by
          rw [Complex.normSq_eq_norm_sq]
        have hng : ‖((x - P.TT : ℝ) : ℂ) ^ n‖ ^ 2 = (x - P.TT) ^ (2 * n) := by
          rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < x - P.TT), ← pow_mul,
            mul_comm]
        rw [hng] at h1
        have h2 : (‖q.eval ((x : ℝ) : ℂ)‖ ^ 2 * c₂ - (x - P.TT) ^ (2 * n) * c₁) * ‖B.hsVec Xf‖ ^ 2 = 0 := by
          linear_combination (-1 : ℝ) * h1
        have h3 := sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hX.ne')
        rw [← hnq, div_mul_eq_mul_div, eq_div_iff hc2]
        linarith [h3]
      obtain ⟨c, hcq⟩ := hPF q n P.TT (c₁ / c₂) hmod
      refine ⟨c, fun ζ hζ Xf hXf hfix => ?_⟩
      have h1 := hq ζ hζ Xf hXf hfix
      rw [hcq] at h1
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X] at h1
      have he : ((Complex.normSq ζ : ℝ) : ℂ) - (P.TT : ℂ) = (((Complex.normSq ζ - P.TT : ℝ)) : ℂ) := by push_cast; ring
      rw [he, mul_comm, mul_smul] at h1
      exact smul_right_injective _ (hGG ζ hζ) h1
  classical
  refine ⟨fun π => if h : ∃ ρ, M.Up P l π ρ then (main π h.choose h.choose_spec).choose else 0, ?_⟩
  intro ζ hζ π ρ hup Xf hXf hfix
  have hex : ∃ ρ, M.Up P l π ρ := ⟨ρ, hup⟩
  have hρ : hex.choose = ρ := tc_up_unique hex.choose_spec hup
  simp only [dif_pos hex]
  have := (main π hex.choose hex.choose_spec).choose_spec ζ hζ Xf hXf hfix
  subst hρ
  exact this

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCModConstCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

noncomputable section

def Line {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (Pr : M.Ty P → (Fin (2 * P.r + P.k + 1) → ℂ) → (Wp →L[ℂ] Wp)) (π : M.Ty P) (ζ : ℂ) : Set (Wq →L[ℂ] Wp) :=
  {X | X ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ ∧ (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp X = X}

def LineAtMost : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ (π : M.Ty P), ∀ ζ ∈ Gauge.GC.Ann P, ∀ X ∈ Line P Bs Pr π ζ, ∀ Y ∈ Line P Bs Pr π ζ, X ≠ 0 → ∃ c : ℂ, Y = c • X

def DatumTransit : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    2 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsSection k r z z' μsec →
    ∀ ζ₁ ζ₂ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ₁ → Tz k r z * Tz k r z' < Complex.normSq ζ₂ →
    ∃ h ∈ UWset k r z, ∃ h' ∈ UWset k r z',
      h *ᵥ SSn.nu0 k r z z' μsec ζ₁ = SSn.nu0 k r z z' μsec ζ₂ ∧
      h' *ᵥ SSn.nu0' k r z z' μsec ζ₁ = SSn.nu0' k r z z' μsec ζ₂ ∧
      h * SSn.io0 k r z z' μsec ζ₁ * h'⁻¹ = SSn.io0 k r z z' μsec ζ₂ ∧
      ∀ p ∈ NF.Stab k r z z' μsec ζ₂, (h⁻¹ * p.1 * h, h'⁻¹ * p.2 * h') ∈ NF.Stab k r z z' μsec ζ₁

def SRaise : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ S, IsSSPt P Bs d l S →
    ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr → ∀ π ρ : M.Ty P, M.Up P l π ρ →
    ∀ ζ ∈ Gauge.GC.Ann P, ∀ Xf ∈ Line P Bs Pr π ζ, S ζ Xf ∈ Line P Bs Pr ρ ζ

def SNorm : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ S, IsSSPt P Bs d l S →
    ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr → ∀ π : M.Ty P,
    ∀ ζ ∈ Gauge.GC.Ann P, ∀ Xf ∈ Line P Bs Pr π ζ, ‖B.hsVec (S ζ Xf)‖ ^ 2 = M.Nrm P l π * ‖B.hsVec Xf‖ ^ 2

def ModConstOfCut : Prop :=
  LineNonzero → LineAtMost → DatumTransit → SRaise → SNorm → SSn.Rep.ThtFacts → ModConst

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GenCapRepIntertwine
section
noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Topx1

namespace Formalism.FourierDecayAlt.P.PBI

section gen

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def GrpInt (S : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (V : Wq →L[ℂ] Wp) : Prop :=
  ∀ hB ∈ UWset k r S.z', hB *ᵥ ν' = ν' → (S.π (m₀ * hB * m₀⁻¹)).comp (V.comp (S.π' hB⁻¹)) = V

theorem gen_dOp_intertwine (S : B.RealPlaceData k r Wp Wq) {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ : B.Mat k r}
    (hbase : D.IsBaseFrame S ν' m₀) (V : Wq →L[ℂ] Wp) (hV : GrpInt S ν' m₀ V) {X : B.Mat k r}
    (hX : QrD.InLieW k r S.z' X) (hXν : X *ᵥ ν' = 0) (hY : QrD.InLieW k r S.z (m₀ * X * m₀⁻¹)) :
    (QrD.dOp S.π (m₀ * X * m₀⁻¹)).comp V = V.comp (QrD.dOp S.π' X) := by
  obtain ⟨hmU, -, hiU, -, um, -, -⟩ := vecw_base_parts S hbase
  have key : ∀ t : ℝ, (S.π (NormedSpace.exp ((t : ℂ) • (m₀ * X * m₀⁻¹)))).comp V =
      V.comp (S.π' (NormedSpace.exp ((t : ℂ) • X))) := by
    intro t
    have hhB := QrD.exp_uw hX t
    have hBν := Qx8.exp_fix hXν t
    set hB := NormedSpace.exp ((t : ℂ) • X) with hhBdef
    have hconj : NormedSpace.exp ((t : ℂ) • (m₀ * X * m₀⁻¹)) = m₀ * hB * m₀⁻¹ := by
      have h := LeftDerivativeCurves.exp_swap hiU X t
      rw [Matrix.nonsing_inv_nonsing_inv _ um] at h
      calc NormedSpace.exp ((t : ℂ) • (m₀ * X * m₀⁻¹))
          = m₀ * (m₀⁻¹ * NormedSpace.exp ((t : ℂ) • (m₀ * X * m₀⁻¹))) := by
            rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ um, Matrix.one_mul]
        _ = m₀ * hB * m₀⁻¹ := by rw [h, Matrix.mul_assoc]
    have h := hV hB hhB hBν
    have hinv := WeylGroupFacts.uw_inv hhB
    have uB := WeylGroupFacts.isUnit_of_uh hhB.1
    rw [hconj]
    calc (S.π (m₀ * hB * m₀⁻¹)).comp V
        = ((S.π (m₀ * hB * m₀⁻¹)).comp (V.comp (S.π' hB⁻¹))).comp (S.π' hB) := by
          rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc, ← S.π'_rep.2 _ hinv _ hhB,
            Matrix.nonsing_inv_mul _ uB, S.π'_rep.1]
          rfl
      _ = V.comp (S.π' hB) := by rw [h]
  have hd1 := QrD.dOp_hasDeriv S.π'_rep S.π'_cont hX
  have hd2 := QrD.dOp_hasDeriv S.π_rep S.π_cont hY
  let L1 : (Wq →L[ℂ] Wq) →L[ℂ] (Wq →L[ℂ] Wp) := ContinuousLinearMap.compL ℂ Wq Wq Wp V
  let L2 : (Wp →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) := (ContinuousLinearMap.compL ℂ Wq Wp Wp).flip V
  have h1 := (L1.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd1
  have h2 := (L2.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd2
  have hfun : ((L2.restrictScalars ℝ) ∘ fun t : ℝ => S.π (NormedSpace.exp ((t : ℂ) • (m₀ * X * m₀⁻¹)))) =
      ((L1.restrictScalars ℝ) ∘ fun t : ℝ => S.π' (NormedSpace.exp ((t : ℂ) • X))) := by
    funext t
    exact key t
  rw [hfun] at h2
  exact h2.unique h1

theorem gen_ecOp_intertwine (S : B.RealPlaceData k r Wp Wq) {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ : B.Mat k r}
    (hbase : D.IsBaseFrame S ν' m₀) (V : Wq →L[ℂ] Wp) (hV : GrpInt S ν' m₀ V) {m : ℕ}
    {Bs' : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : Q.IsFrameOf k r [S.z', ν'] Bs') (a b : Fin m) :
    (QrD.ecOp S.π (Q.unitB (Hpk k r) (fun a => m₀ *ᵥ Bs' a) a b)).comp V =
      V.comp (QrD.ecOp S.π' (Q.unitB (Hpk k r) Bs' a b)) := by
  obtain ⟨hmU, -, -, -, um, -, -⟩ := vecw_base_parts S hbase
  have hBz : Q.IsFrameOf k r [S.z] (fun a => m₀ *ᵥ Bs' a) :=
    vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) (vecw_frame_fwd S hbase hB)
  have hBz' : Q.IsFrameOf k r [S.z'] Bs' := vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) hB
  have hBν : Q.IsFrameOf k r [ν'] Bs' := vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) hB
  obtain ⟨e1, e2, e3⟩ := vecw_conj_eq hmU um Bs' a b
  have lY := QrD.frame_lie hBz a b
  have lX := QrD.frame_lie hBz' a b
  have lν := QrD.frame_lie hBν a b
  rw [e1, e2, e3] at lY
  unfold QrD.ecOp
  rw [e1, e2, e3, ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_smul, gen_dOp_intertwine S hbase V hV lX.1 lν.1.2 lY.1,
    gen_dOp_intertwine S hbase V hV lX.2 lν.2.2 lY.2]

theorem gen_capRep_intertwine (S : B.RealPlaceData k r Wp Wq) {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ : B.Mat k r}
    (hbase : D.IsBaseFrame S ν' m₀) (V : Wq →L[ℂ] Wp) (hV : GrpInt S ν' m₀ V) {m : ℕ}
    {Bs' : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : Q.IsFrameOf k r [S.z', ν'] Bs') (w : ℂ) (v : Wq) :
    Q.capRep k r S.π (fun a => m₀ *ᵥ Bs' a) w (V v) = V (Q.capRep k r S.π' Bs' w v) := by
  have hBz : Q.IsFrameOf k r [S.z] (fun a => m₀ *ᵥ Bs' a) :=
    vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) (vecw_frame_fwd S hbase hB)
  have hBz' : Q.IsFrameOf k r [S.z'] Bs' := vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) hB
  unfold Q.capRep
  refine vecw_qmF V.toLinearMap _ _ (fun i j y => ?_) id id w v
  have lY := QrD.frame_lie hBz i j
  have lX := QrD.frame_lie hBz' i j
  simp only [ContinuousLinearMap.coe_coe]
  rw [QrD.ecRep_eq S.π_rep S.π_cont lY.1 lY.2, QrD.ecRep_eq S.π'_rep S.π'_cont lX.1 lX.2]
  have h := congrArg (fun L : Wq →L[ℂ] Wp => L y) (gen_ecOp_intertwine S hbase V hV hB i j)
  simpa using h

end gen

open Finset

theorem types_of_grpInt {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (S : B.RealPlaceData P.k P.r Wp Wq) (ν' : Fin (2 * P.r + P.k + 1) → ℂ) (m₀ : B.Mat P.k P.r)
    (TP : Formalism.FourierDecayAlt.Top.TypeProj P S.π S.z (m₀ *ᵥ ν')) (hPl : Q.IsPlace P S.z S.z' S.π S.π')
    (hbase : D.IsBaseFrame S ν' m₀) (V : Wq →L[ℂ] Wp) (hV : GrpInt S ν' m₀ V) :
    ∑ ρ : M.Ty P, (TP.E ρ).comp V = V := by
  obtain ⟨hOK, hz, hz', -, -, hty, hty'⟩ := hPl
  obtain ⟨hmU, hmW, -, -, -, hzeq, -⟩ := vecw_base_parts S hbase
  obtain ⟨hν, hνz, hνν, -, -⟩ := id hbase
  have he : inWb P.k P.r (m₀ *ᵥ ν') := hmW ν' hν
  have hee : herm (Hpk P.k P.r) (m₀ *ᵥ ν') (m₀ *ᵥ ν') = 1 := by rw [Dx2.DF.herm_m0_mulVec_invariant m₀ hmU]; exact hνν
  have hez : herm (Hpk P.k P.r) (m₀ *ᵥ ν') S.z = 0 := by
    rw [hzeq, Qx8.herm_smul_right', Dx2.DF.herm_m0_mulVec_invariant m₀ hmU, hνz, mul_zero]
  obtain ⟨Bs₀', hB₀'⟩ := vecw_frame_exists P.k P.r hOK.k_pos S.z' ν' hz' S.T'_pos hν hνz hνν
  have hB₀ := vecw_frame_fwd S hbase hB₀'
  obtain ⟨S', hInt', -, heig⟩ := branching_proof Wq (parametersUPrimeForU P) (parameters_u_prime_for_u_ok hOK) rfl S.z' ν' S.π' hz'
    S.T'_pos hty' hν hνz hνν
  have heig' : ∀ (σ : M.Ty (parametersUPrimeForU P)) (w : ℂ), ∀ v ∈ S' σ,
      Q.capRep P.k P.r S.π' Bs₀' w v = M.xC (parametersUPrimeForU P) σ (w - ((P.k : ℂ) - 2) / 2) • v :=
    fun σ w v hv => heig Bs₀' hB₀' σ w v hv
  refine ContinuousLinearMap.ext fun f => ?_
  rw [_root_.sum_apply]
  simp only [ContinuousLinearMap.comp_apply]
  have hf : f ∈ ⨆ σ, S' σ := by rw [hInt'.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction S' (motive := fun f => ∑ ρ, TP.E ρ (V f) = V f) hf ?_ ?_ ?_
  · intro σ v hv
    refine vecw_good_of_eig hOK hz S.T_pos hty he hez hee TP hB₀ σ _ fun w => ?_
    rw [gen_capRep_intertwine S hbase V hV hB₀' w v, heig' σ w v hv, map_smul]
  · simp
  · intro a b ha hb
    simp only [map_add (f := _), Finset.sum_add_distrib, ha, hb]

end Formalism.FourierDecayAlt.P.PBI
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GermLocTail
section
namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type} {s : ℕ} {β ε : ℂ} {Y : Finset ι} {ut : ι → ℂ → ℂ → H} {bt : ι → ℂ → H} {SS : ℝ}

theorem GermD.germLoc_tail (hG : GermD s β ε Y ut bt SS) (Gk : ι × ℂ → ι × ℂ → ℂ)
    (hGk : ∀ h ∈ Y, ∀ h' ∈ Y, ∀ x x' : ℂ, x ≠ 0 → x' ≠ 0 →
      Gk (h, x) (h', x') = gramL volume (Uc s ut) (Uc s ut) (h, x) (h', x'))
    (hatB : ℂ → ι → ι → ℂ) (hN : ∀ σ : ℂ, ∀ h ∈ Y, ∀ h' ∈ Y, Nhat s β bt σ h h' = hatB σ h h') :
    (∀ h ∈ Y, ∀ h' ∈ Y, Integrable (fun z => ⟪bz s (bt h) z, bz s (bt h') z⟫_ℂ)) ∧
    ∃ Pua Paa : ι × ℂ → ι × ℂ → ℂ,
      (∀ Xs : Finset ℂ, (∀ x ∈ Xs, x ≠ 0) → KB.BlockPSD (Y ×ˢ Xs) (Y ×ˢ Xs) Gk Pua Paa) ∧
      (∃ B' : ℝ, ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → ‖Paa (h, x) (h, x)‖ ≤ B') ∧
      ∀ h ∈ Y, ∀ h' ∈ Y, ∀ σ : ℂ,
        Tendsto (fun x => Paa (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (hatB σ h h')) ∧
        Tendsto (fun x => Pua (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (hatB σ h h')) ∧
        Tendsto (fun x => conj (Pua (h', x + σ) (h, x))) (cocompact ℂ) (𝓝 (hatB σ h h')) := by
  obtain ⟨h0, h1, h2, h3⟩ := hG.propG
  refine ⟨fun h hh h' hh' => integrable_inner_of_memLp (h0 h hh).1 (h0 h' hh').1,
    gramL volume (Uc s ut) (Ac s β ε bt), gramL volume (Ac s β ε bt) (Ac s β ε bt),
    fun Xs hXs => ?_, h2, fun h hh h' hh' σ => ?_⟩
  · have hb := h1 Xs hXs
    unfold KB.BlockPSD TB.PSDOn at hb ⊢
    open scoped ComplexOrder in
    refine (congrArg Matrix.PosSemidef ?_).mpr hb
    ext i j
    obtain ⟨x, hx⟩ := i
    obtain ⟨y, hy⟩ := j
    rcases x with p | q <;> rcases y with p' | q'
    · have hp := Finset.mem_product.mp (Finset.inl_mem_disjSum.mp hx)
      have hp' := Finset.mem_product.mp (Finset.inl_mem_disjSum.mp hy)
      show Gk p p' = gramL volume (Uc s ut) (Uc s ut) p p'
      exact hGk p.1 hp.1 p'.1 hp'.1 p.2 p'.2 (hXs _ hp.2) (hXs _ hp'.2)
    · rfl
    · rfl
    · rfl
  · rw [← hN σ h hh h' hh']
    exact h3 h hh h' hh' σ

end

end Formalism.FourierDecayAlt.P.PBK
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCGlob
section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

def Good {f : ℕ} (x : crystallineComparison.V f) : Prop := ∀ v, x v ≠ 0

def blk {α : Type} (a w b : α → α → ℂ) : α ⊕ α → α ⊕ α → ℂ := fun x y =>
  match x, y with
    | .inl p, .inl q => a p q
    | .inl p, .inr q => w p q
    | .inr q, .inl p => conj (w p q)
    | .inr p, .inr q => b p q

theorem blockPSD_iff {α : Type} (Y : Finset α) (a w b : α → α → ℂ) :
    KB.BlockPSD Y Y a w b ↔ TB.PSDOn (Y.disjSum Y) (blk a w b) := by
  unfold KB.BlockPSD
  constructor <;> intro h <;> convert h using 1 <;> funext x y <;>
    rcases x with p | p <;> rcases y with q | q <;> rfl

variable {H : Type} {f : ℕ}

def phi (Y : Finset H) (κ : H → H → ℂ) (K : Fin f → H × ℂ → H × ℂ → ℂ) (x x' : crystallineComparison.V f) : ℂ :=
  ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, K v (h, x v) (h', x' v)

def phiR (Y : Finset H) (κ : H → H → ℂ) (U P Q : Fin f → H × ℂ → H × ℂ → ℂ) (x x' : crystallineComparison.V f) : ℂ :=
  phi Y κ U x x' - phi Y κ P x x' - conj (phi Y κ P x' x) + phi Y κ Q x x'

def hd : (H × crystallineComparison.V f) ⊕ (H × crystallineComparison.V f) → H := Sum.elim (fun p => p.1) (fun p => p.1)

end

end Formalism.FourierDecayAlt.P.PBC
end

