module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.FormalDegreeBessel.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LinMulti
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KFiniteSmoothVectors.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BesselDerivatives.ExpSup
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRep
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.PiUnitary

open Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ}

theorem ellA_mul (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) {g h : Mat k r}
    (hg : col k r g) (hh : col k r h) (a : Fin r) :
    ellA k r z (g * h) a = ellA k r z g a + ellA k r z h a := by
  unfold ellA
  by_cases ha : a.val + 1 < r
  · rw [dite_eq_left ha, dite_eq_left ha, dite_eq_left ha]
    exact mul_apply_add hg hh _ _ (by simp only [eI]; omega) (by simp only [eI]; omega)
      (by simp only [eI]; omega) (by simp only [eI]; omega)
  · rw [dite_eq_right ha, dite_eq_right ha, dite_eq_right ha]
    simp only [Matrix.mulVec, dotProduct]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hzj : z j = 0
    · rw [hzj, mul_zero, mul_zero, mul_zero, add_zero]
    · have hjW : r ≤ j.val ∧ j.val ≤ r + k := by
        by_contra hc
        apply hzj
        apply hz
        omega
      rw [mul_apply_add hg hh _ _ (by simp only [eI]; omega) (by omega)
        (by simp only [eI]; omega) (by simp only [eI]; omega), add_mul]

theorem psiGen_mul_N (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (hz : inWb k r z) {g h : Mat k r}
    (hg : g ∈ Nset k r) (hh : h ∈ Nset k r) :
    psiGen k r z c (g * h) = psiGen k r z c g * psiGen k r z c h := by
  have hs : (∑ a, c a * ellA k r z (g * h) a) =
      (∑ a, c a * ellA k r z g a) + ∑ a, c a * ellA k r z h a := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [ellA_mul z hz ((nset_iff g).1 hg).2 ((nset_iff h).1 hh).2 a, mul_add]
  unfold psiGen
  rw [hs, Complex.add_re, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem norm_psiGen (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (g : Mat k r) :
    ‖psiGen k r z c g‖ = 1 := by
  unfold psiGen
  rw [mul_comm Complex.I]
  exact Complex.norm_exp_ofReal_mul_I _

theorem ellA_block (z : Fin (2 * r + k + 1) → ℂ) {h h' g : Mat k r}
    (hh : block k r h) (hh' : block k r h') (hz : h' *ᵥ z = z) (a : Fin r) :
    ellA k r z (h * g * h') a = ellA k r z g a := by
  unfold ellA
  have hrow : ∀ p, h (eI k r a) p = if eI k r a = p then 1 else 0 :=
    fun p => hh.2 _ p (by simp only [eI]; omega)
  by_cases ha : a.val + 1 < r
  · rw [dite_eq_left ha, dite_eq_left ha, mul_apply_of_col _ _ _ (fun q => hh'.1 q _ (by simp only [eI]; omega)),
      mul_apply_of_row _ _ _ hrow]
  · rw [dite_eq_right ha, dite_eq_right ha, ← Matrix.mulVec_mulVec, hz, ← Matrix.mulVec_mulVec,
      mulVec_apply_of_row _ _ hrow]

theorem psiGen_block (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) {h h' g : Mat k r}
    (hh : block k r h) (hh' : block k r h') (hz : h' *ᵥ z = z) :
    psiGen k r z c (h * g * h') = psiGen k r z c g := by
  simp only [psiGen, ellA_block z hh hh' hz]

theorem block_one : block k r (1 : Mat k r) :=
  ⟨fun _ _ _ => Matrix.one_apply, fun _ _ _ => Matrix.one_apply⟩

theorem psiGen_uw_mul (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) {h g : Mat k r}
    (hh : h ∈ UWset k r z) : psiGen k r z c (h * g) = psiGen k r z c g := by
  have := psiGen_block (g := g) z c (uw_block hh) block_one (Matrix.one_mulVec z)
  rwa [Matrix.mul_one] at this

theorem ellA_continuous (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    Continuous (fun g : Mat k r => ellA k r z g a) := by
  by_cases h : a.val + 1 < r
  · have e : (fun g : Mat k r => ellA k r z g a) =
        fun g => g (eI k r a) (eI k r ⟨a.val + 1, h⟩) := by
      funext g; unfold ellA; rw [dite_eq_left h]
    rw [e]
    exact (continuous_apply _).comp (continuous_apply _)
  · have e : (fun g : Mat k r => ellA k r z g a) = fun g => (g *ᵥ z) (eI k r a) := by
      funext g; unfold ellA; rw [dite_eq_right h]
    rw [e]
    exact (continuous_apply (eI k r a)).comp
      (continuous_id.matrix_mulVec continuous_const : Continuous fun g : Mat k r => g *ᵥ z)

theorem psiGen_continuous (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) :
    Continuous (psiGen k r z c) := by
  unfold psiGen
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_finsetSum _ fun a _ =>
      continuous_const.mul (ellA_continuous z a)))))

theorem block_entry {h : Mat k r} (hh : block k r h) {i j : Fin (2 * r + k + 1)}
    (H : ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k))) :
    h i j = if i = j then 1 else 0 := by
  by_cases hj : j.val < r ∨ r + k < j.val
  · exact hh.1 i j hj
  · exact hh.2 i j (by omega)

theorem hPart_mul {z : Fin (2 * r + k + 1) → ℂ} {h m : Mat k r} (hh : h ∈ UWset k r z)
    (hm : m ∈ Nset k r) : hPart k r (h * m) = h := by
  have hb := uw_block hh
  have hc := ((nset_iff m).1 hm).2
  ext i j
  unfold hPart
  by_cases H1 : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)
  · rw [if_pos H1]
    exact block_mul_col hb hc i j H1.2.2 (Or.inr H1.1.1)
  · rw [if_neg H1, block_entry hb H1]

theorem PiS_mul {Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (ψ : Mat k r → ℂ)
    (π : Mat k r → (Wp →L[ℂ] Wp)) {z : Fin (2 * r + k + 1) → ℂ} {h m : Mat k r}
    (hh : h ∈ UWset k r z) (hm : m ∈ Nset k r) : PiS ψ π (h * m) = ψ m • π h := by
  unfold PiS
  rw [hPart_mul hh hm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_of_uh hh.1), Matrix.one_mul]

theorem hPart_continuous : Continuous (hPart k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun s : Mat k r => hPart k r s i j
  by_cases H1 : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)
  · simp only [hPart, if_pos H1]
    exact (continuous_apply j).comp (continuous_apply i)
  · simp only [hPart, if_neg H1]
    exact continuous_const

theorem adjoint_eq_of_isometry {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A B : E →L[ℂ] E) (hA : ∀ v, ‖A v‖ = ‖v‖) (hAB : A.comp B = 1) :
    ContinuousLinearMap.adjoint A = B := by
  have h1 : (ContinuousLinearMap.adjoint A).comp A = 1 := (A.norm_map_iff_adjoint_comp_self).1 hA
  ext v
  have e1 := congrArg (fun T : E →L[ℂ] E => T (B v)) h1
  have e2 := congrArg (fun T : E →L[ℂ] E => T v) hAB
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at e1 e2
  rw [e2] at e1
  exact e1

end GlobalTheory.SgInf.PiUnitary

namespace GlobalTheory.SgInf.PiUnitary

open Formalism.QuantumDeterminants.WeylGroupFacts

theorem piS_unitary : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (π : Mat k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → IsURepOn (UWset k r z) π →
    (∀ h ∈ UWset k r z, ∀ m ∈ Nset k r, hPart k r (h * m) = h ∧
        PiS (psiGen k r z c) π (h * m) = psiGen k r z c m • π h) ∧
      IsURepOn (Sset k r z) (PiS (psiGen k r z c) π) ∧
      (∀ s ∈ Sset k r z, ‖PiS (psiGen k r z c) π s‖ ≤ 1 ∧
        ContinuousLinearMap.adjoint (PiS (psiGen k r z c) π s) = PiS (psiGen k r z c) π s⁻¹) ∧
      ContinuousOn (PiS (psiGen k r z c) π) (Sset k r z) ∧
      (∀ m ∈ Nset k r, ‖psiGen k r z c m‖ = 1 ∧
        ∀ m' ∈ Nset k r, psiGen k r z c (m * m') = psiGen k r z c m * psiGen k r z c m') := by
  intro k r Wp _ _ _ _ z c π hz _ hπ
  have hchar : ∀ m ∈ Nset k r, ‖(psiGen k r z c) m‖ = 1 ∧ ∀ m' ∈ Nset k r, (psiGen k r z c) (m * m') = (psiGen k r z c) m * (psiGen k r z c) m' :=
    fun m hm => ⟨norm_psiGen z c m, fun m' hm' => psiGen_mul_N z c hz hm hm'⟩
  have hpsi1 : (psiGen k r z c) 1 = 1 := by
    have e := psiGen_mul_N z c hz (mem_n_one (k := k) (r := r)) (mem_n_one (k := k) (r := r))
    rw [Matrix.one_mul] at e
    have hne : (psiGen k r z c) 1 ≠ 0 := by
      intro h0
      have := norm_psiGen (k := k) (r := r) z c 1
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    have e' : (psiGen k r z c) 1 * 1 = (psiGen k r z c) 1 * (psiGen k r z c) 1 := by rw [mul_one]; exact e
    exact (mul_left_cancel₀ hne e').symm
  have hrep : IsURepOn (Sset k r z) (PiS (psiGen k r z c) π) := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [PiS_one, hpsi1, one_smul]
      exact hπ.1.1
    · rintro _ ⟨h, hh, m, hm, rfl⟩ _ ⟨h', hh', m', hm', rfl⟩
      have hu' := isUnit_of_uh hh'.1
      have hn : h'⁻¹ * m * h' ∈ Nset k r := by
        have := (uWNormal k r z hz h'⁻¹ (uw_inv hh') m hm).1
        rwa [Matrix.nonsing_inv_nonsing_inv _ hu'] at this
      have e : h * m * (h' * m') = (h * h') * ((h'⁻¹ * m * h') * m') := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc h' h'⁻¹, Matrix.mul_nonsing_inv _ hu', Matrix.one_mul]
      rw [e, PiS_mul (psiGen k r z c) π (uw_mul hh hh') (mem_n_mul hn hm'), PiS_mul (psiGen k r z c) π hh hm, PiS_mul (psiGen k r z c) π hh' hm',
        psiGen_mul_N z c hz hn hm',
        psiGen_block z c (uw_block (uw_inv hh')) (uw_block hh') hh'.2.2, hπ.1.2 h hh h' hh',
        ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul]
    · rintro _ ⟨h, hh, m, hm, rfl⟩ v
      rw [PiS_mul (psiGen k r z c) π hh hm, ContinuousLinearMap.smul_apply, norm_smul, norm_psiGen, one_mul,
        hπ.2.1 h hh v]
    · intro v
      have hmaps : Set.MapsTo (hPart k r) (Sset k r z) (UWset k r z) := by
        rintro _ ⟨h, hh, m, hm, rfl⟩
        rw [hPart_mul hh hm]
        exact hh
      have hc : ContinuousOn (fun s => (psiGen k r z c) s • π (hPart k r s) v) (Sset k r z) :=
        (psiGen_continuous z c).continuousOn.smul
          ((hπ.2.2 v).comp hPart_continuous.continuousOn hmaps)
      refine hc.congr ?_
      rintro _ ⟨h, hh, m, hm, rfl⟩
      show PiS (psiGen k r z c) π (h * m) v = (psiGen k r z c) (h * m) • π (hPart k r (h * m)) v
      rw [PiS_mul (psiGen k r z c) π hh hm, hPart_mul hh hm, psiGen_uw_mul z c hh, ContinuousLinearMap.smul_apply]
  have hiso : ∀ s ∈ Sset k r z, ∀ v, ‖PiS (psiGen k r z c) π s v‖ = ‖v‖ := hrep.2.1
  refine ⟨fun h hh m hm => ⟨hPart_mul hh hm, PiS_mul (psiGen k r z c) π hh hm⟩, hrep, fun s hs => ⟨?_, ?_⟩, ?_, hchar⟩
  · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [hiso s hs v, one_mul]
  · apply adjoint_eq_of_isometry _ _ (hiso s hs)
    have hsU : s ∈ UH (Hpk k r) := by
      obtain ⟨h, hh, m, hm, rfl⟩ := hs
      exact uh_mul hh.1 hm.1
    have hsi : s⁻¹ ∈ Sset k r z := (sGroup k r z hz).2.2 s hs
    rw [← hrep.1.2 s hs s⁻¹ hsi, Matrix.mul_nonsing_inv _ (isUnit_of_uh hsU)]
    exact hrep.1.1
  · exact continuousOn_clm_apply.2 hrep.2.2

end GlobalTheory.SgInf.PiUnitary
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CentredCapelliOperatorFormsAgree
section
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory.ThA

theorem qminorOp_eq_qdetOp_of_val {n t : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (h : t = n) (p : Fin t → Fin n) (hp : ∀ j, (p j).val = j.val) (u : ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) : qminorOp Eop p p u f = qdetOp Eop u f := by
  subst h
  have e : p = id := funext fun j => Fin.ext (hp j)
  rw [e]
  rfl

theorem centredCapelli_forms_agree :
    ∀ (k r : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (Y : ℂ) (F : B.Mat k r → V),
      Q.CV k r Y F = PI.CapelliEig.capC (k := k) (r := r) Y F ∧
        Q.CV k r Y F = Formalism.MainNotions.S.capC (k := k) (r := r) Y F := by
  intro k r V _ _ Y F
  have hm : Q.mdim k r 0 = 2 * r + k + 1 := by simp [Q.mdim]
  have hu : Q.uC k r 0 Y = Y + ((2 * r + k : ℕ) : ℂ) / 2 := by
    unfold Q.uC
    rw [hm]
    push_cast
    ring
  have key : Q.CV k r Y F = capelliH (Hpk k r) (Y + ((2 * r + k : ℕ) : ℂ) / 2) F := by
    unfold Q.CV Q.capL capelliH
    rw [hu]
    exact qminorOp_eq_qdetOp_of_val _ hm _ (fun j => by simp [Q.posL]) _ _
  exact ⟨key, key⟩

end GlobalTheory.ThA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DKerHasCompactSupport
section
noncomputable section

open MeasureTheory Matrix Filter Topology Set Metric
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.SmLinSub

section Smoothing

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PI.UpqRep PI.KFinSmoothW

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem expS_mul_neg (Z : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • Z) * NormedSpace.exp (t • -Z) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Z).neg_right.smul_left t).smul_right t)]
  simp [smul_neg]

theorem expS_neg_mul (Z : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • -Z) * NormedSpace.exp (t • Z) = 1 := by
  have h := expS_mul_neg (-Z) t
  rwa [neg_neg] at h

end Smoothing

end GlobalTheory.SmLinSub

namespace GlobalTheory.SmLinSub

section Rep

open Formalism.MainNotions.S GlobalTheory.Ell

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {G : Matrix (Fin n) (Fin n) ℂ} {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem lie_smulR (c : ℝ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieOf G) : c • X ∈ lieOf G := by
  have h1 : Xᴴ * G + G * X = 0 := hX
  show (c • X)ᴴ * G + G * (c • X) = 0
  rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, h1, smul_zero]

theorem exp_mem {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieOf G) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH G :=
  CCRuleCW.exp_mem_UH G (t • X) (lie_smulR t hX)

theorem listProd_mem : ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ g ∈ l, g ∈ Formalism.QuantumDeterminants.UH G) →
    l.prod ∈ Formalism.QuantumDeterminants.UH G
  | [], _ => by
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * G * 1 = G
    simp
  | g :: l, h => by
    rw [List.prod_cons]
    exact CCRuleCW.UH_mul G _ _ (h g (by simp)) (listProd_mem l fun x hx => h x (by simp [hx]))

theorem expProd_mem {k : ℕ} {Xs : Fin k → Matrix (Fin n) (Fin n) ℂ} (hX : ∀ i, Xs i ∈ lieOf G)
    (t : Fin k → ℝ) : (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod ∈ Formalism.QuantumDeterminants.UH G :=
  listProd_mem _ fun g hg => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    exact exp_mem (hX i) _

theorem isUnit_of_mem (hG : IsUnit G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G) : IsUnit g := by
  have h : gᴴ * G * g = G := hg
  exact isUnit_of_mul_isUnit_right (h.symm ▸ hG : IsUnit (gᴴ * G * g))

theorem conj_mem_lie (hG : IsUnit G) {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    (hX : X ∈ lieOf G) : g⁻¹ * X * g ∈ lieOf G := by
  have h : gᴴ * G * g = G := hg
  have hX' : Xᴴ * G + G * X = 0 := hX
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 (isUnit_of_mem hG hg)
  have h1 : G * g⁻¹ = gᴴ * G := by
    conv_lhs => rw [← h]
    rw [Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.mul_one]
  have h2 : (g⁻¹)ᴴ * G = G * g := by
    conv_lhs => rw [← h]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, mul_nonsing_inv _ hd]; simp
  show (g⁻¹ * X * g)ᴴ * G + G * (g⁻¹ * X * g) = 0
  calc (g⁻¹ * X * g)ᴴ * G + G * (g⁻¹ * X * g) = gᴴ * Xᴴ * ((g⁻¹)ᴴ * G) + (G * g⁻¹) * X * g := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = gᴴ * (Xᴴ * G + G * X) * g := by rw [h1, h2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX']; simp

theorem rep_mul (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ) {g g' : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH G) (hg' : g' ∈ Formalism.QuantumDeterminants.UH G) (w : H) : ρ (g * g') w = ρ g (ρ g' w) := by
  rw [hπ.1.2 g hg g' hg']; rfl

theorem exp_conj_inv {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (g⁻¹ * X * g)) = g⁻¹ * NormedSpace.exp (t • X) * g := by
  rw [← Matrix.exp_conj' _ _ hg, Matrix.mul_smul, Matrix.smul_mul]

theorem hasDerivAt_dR {w : H} (hw : SmV (lieOf G) ρ w) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieOf G) :
    HasDerivAt (fun t : ℝ => ρ (NormedSpace.exp (t • X)) w) (dR ρ X w) 0 := by
  have h1 := hw 1 (fun _ => X) (fun _ => hX)
  have h2 : ContDiff ℝ ∞ fun t : ℝ => fun _ : Fin 1 => t := contDiff_pi.2 fun _ => contDiff_id
  have h3 : ContDiff ℝ ∞ fun t : ℝ => ρ (NormedSpace.exp (t • X)) w := by
    simpa [Function.comp_def] using h1.comp h2
  exact (h3.differentiable (by simp) 0).hasDerivAt

theorem contDiff_deriv_snoc {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    {F : (Fin (k + 1) → ℝ) → E} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => deriv (fun s : ℝ => F (Fin.snoc t s)) 0 := by
  have hs : ContDiff ℝ ∞ fun p : (Fin k → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (k + 1) → ℝ) := by
    refine contDiff_pi.2 fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using contDiff_snd
    · simp only [Fin.snoc_castSucc]
      fun_prop
  have h1 : ContDiff ℝ ∞ (Function.uncurry fun (t : Fin k → ℝ) (s : ℝ) => F (Fin.snoc t s)) := hF.comp hs
  have h2 := ContDiff.fderiv (𝕜 := ℝ) (m := ∞) (n := ∞) (g := fun _ : Fin k → ℝ => (0 : ℝ)) h1 contDiff_const
    (le_of_eq rfl)
  exact h2.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem dR_mem (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ) {w : H} (hw : SmV (lieOf G) ρ w)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieOf G) : SmV (lieOf G) ρ (dR ρ X w) := by
  intro k Xs hXs
  have h1 := hw (k + 1) (Fin.snoc Xs X) (fun i => by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hX
    · simpa using hXs j)
  convert contDiff_deriv_snoc h1 using 2 with t
  have h2 := (((ρ _).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dR hw hX) :
    HasDerivAt (fun s : ℝ => ρ (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod
      (ρ (NormedSpace.exp (s • X)) w)) _ 0)
  refine h2.deriv.symm.trans ?_
  congr 1
  funext s
  show ρ _ (ρ _ w) = _
  rw [← rep_mul hπ (expProd_mem hXs t) (exp_mem hX s)]
  simp [List.ofFn_succ', -List.ofFn_succ]

theorem prod_conj {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    g * (l.map fun x => g⁻¹ * x * g).prod = l.prod * g := by
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 hg
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, Matrix.mul_assoc x, ← ih]
    simp only [← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul]

theorem rep_mem (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ) {w : H} (hw : SmV (lieOf G) ρ w)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G) : SmV (lieOf G) ρ (ρ g w) := by
  intro k Xs hXs
  have hu := isUnit_of_mem hG hg
  have hY : ∀ i, g⁻¹ * Xs i * g ∈ lieOf G := fun i => conj_mem_lie hG hg (hXs i)
  have h1 := ((ρ g).restrictScalars ℝ).contDiff.comp (hw k _ hY)
  convert h1 using 2 with t
  show _ = ρ g _
  rw [← rep_mul hπ (expProd_mem hXs t) hg, ← rep_mul hπ hg (expProd_mem hY t), ← prod_conj hu,
    List.map_ofFn]
  simp only [exp_conj_inv hu, Function.comp_def]

theorem dR_rep (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ) {w : H} (hw : SmV (lieOf G) ρ w)
    {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G) (hX : X ∈ lieOf G) :
    dR ρ X (ρ g w) = ρ g (dR ρ (g⁻¹ * X * g) w) := by
  have hu := isUnit_of_mem hG hg
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 hu
  have hY := conj_mem_lie hG hg hX
  have h2 := (((ρ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dR hw hY) :
    HasDerivAt (fun s : ℝ => ρ g (ρ (NormedSpace.exp (s • (g⁻¹ * X * g))) w)) _ 0)
  refine Eq.trans ?_ h2.deriv
  unfold dR
  congr 1
  funext s
  show _ = ρ g (ρ _ w)
  rw [← rep_mul hπ hg (exp_mem hY s), ← rep_mul hπ (exp_mem hX s) hg, exp_conj_inv hu]
  simp only [← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul]

end Rep

end GlobalTheory.SmLinSub
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FolnerSingleTranslateProportionTendstoOne
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem folner_single_translate : ∀ (k r : ℕ) (S : Set (Mat k r)) (μ : Measure (Mt k r))
    (Om : ℕ → Set (Mt k r)), IsFolner S μ Om → ∀ p ∈ S,
    Filter.Tendsto (fun j => μ {s | s ∈ Om j ∧ lmulM p s ∈ Om j} / μ (Om j)) Filter.atTop (nhds 1) := by
  intro k r S μ Om h p hp
  obtain ⟨_, hC⟩ := h
  obtain ⟨Oc, hOc, hlim⟩ := hC {p} isCompact_singleton (Set.singleton_subset_iff.2 hp)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds (fun j => ?_) (fun j => ?_)
  · refine ENNReal.div_le_div_right (measure_mono fun x hx => ?_) _
    exact ⟨(hOc j).2.1 hx, (hOc j).2.2 p rfl x hx⟩
  · exact (ENNReal.div_le_div_right (measure_mono fun x (hx : x ∈ {s | s ∈ Om j ∧ lmulM p s ∈ Om j}) => hx.1) _).trans ENNReal.div_self_le_one

end GlobalTheory.SgInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.Ia
section
noncomputable section

open NumberField

namespace GlobalTheory.RowLatXS

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T : E}

def Ia (Λ : Submodule (𝓞 E) S.V) (F : Formalism.MainNotions.S.FlagG S r T) (a : Fin r) : Submodule (𝓞 E) E :=
  Submodule.span (𝓞 E) {t | ∃ x ∈ Λ, x ∈ F.Xa (a.val + 1) ∧ F.coefX x a = t}

end GlobalTheory.RowLatXS
end
end

