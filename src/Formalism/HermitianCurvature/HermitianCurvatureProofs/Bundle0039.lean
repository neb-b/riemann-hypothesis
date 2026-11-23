module

public import Formalism.HermitianCurvature.Bundle0006
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0035
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0031
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0036

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SumPairAtStarMul
section
open MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Gen

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem form_last (μ : Measure (Mt k r)) (x y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) :
    form μ (Fin.last r) x y c = ∑ a, pairAt μ (x a) (y a) c := by
  have : IsEmpty {l : Fin r // (Fin.last r).val ≤ l.val} := ⟨fun l => absurd l.2 (not_le.mpr l.1.isLt)⟩
  have hg : ∀ c' : Cf r (Fin.last r), glue (Fin.last r) c c' = c :=
    fun c' => funext fun l => dif_neg (not_le.mpr l.isLt)
  have hp : ∀ c' : Cf r (Fin.last r), ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) = 1 := fun c' => by
    rw [Fintype.prod_empty, Complex.ofReal_one]
  have h1 : (volume : Measure (Cf r (Fin.last r))) Set.univ = 1 := by
    rw [MeasureTheory.volume_pi, Measure.pi_univ, Fintype.prod_empty]
  unfold form
  simp only [hg, hp, one_mul]
  rw [integral_const]
  simp [measureReal_def, h1]

def IntOn (μ : Measure (Mt k r)) (U : Submodule ℂ (RadSp k r z z' π π')) : Prop :=
  ∀ c ∈ OmX r, ∀ Φ ∈ U, ∀ Ψ ∈ U, Integrable (fun g : Mt k r =>
    B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) μ

def AdjOn (μ : Measure (Mt k r)) (U : Submodule ℂ (RadSp k r z z' π π')) (a : Pr (RadSp k r z z' π π')) : Prop :=
  (∀ Φ ∈ U, a.1 Φ ∈ U) ∧ (∀ Φ ∈ U, a.2.unop Φ ∈ U) ∧
    ∀ c ∈ OmX r, ∀ Φ ∈ U, ∀ Ψ ∈ U, pairAt μ (a.1 Φ) Ψ c = pairAt μ Φ (a.2.unop Ψ) c

theorem hsInner_swap (A C : Wq →L[ℂ] Wp) : B.hsInner C A = conj (B.hsInner A C) := by
  simp only [B.hsInner]
  rw [inner_conj_symm]

private theorem hsVec_zero_hermitian_curvature : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
  ext i
  simp [B.hsVec]

theorem hsInner_zero_left (C : Wq →L[ℂ] Wp) : B.hsInner 0 C = 0 := by
  simp only [B.hsInner, hsVec_zero_hermitian_curvature, inner_zero_right]

private theorem hsVec_smul_hermitian_curvature' (a : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (a • A) = a • B.hsVec A := by
  ext i
  simp [B.hsVec]

theorem hsInner_smul_left' (A C : Wq →L[ℂ] Wp) (a : ℂ) : B.hsInner (a • A) C = a * B.hsInner A C := by
  simp only [B.hsInner, hsVec_smul_hermitian_curvature', inner_smul_right]

theorem hsInner_smul_right' (A C : Wq →L[ℂ] Wp) (a : ℂ) : B.hsInner A (a • C) = conj a * B.hsInner A C := by
  simp only [B.hsInner, hsVec_smul_hermitian_curvature', inner_smul_left]

theorem pairAt_swap (μ : Measure (Mt k r)) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ Ψ Φ c = conj (pairAt μ Φ Ψ c) := by
  simp only [pairAt]
  rw [← integral_conj]
  congr 1
  funext g
  exact hsInner_swap _ _

theorem pairAt_smul_left (μ : Measure (Mt k r)) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) (a : ℂ) :
    pairAt μ (a • Φ) Ψ c = a * pairAt μ Φ Ψ c := by
  simp only [pairAt, Submodule.coe_smul, Pi.smul_apply, hsInner_smul_left']
  exact integral_const_mul a _

theorem pairAt_smul_right (μ : Measure (Mt k r)) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) (a : ℂ) :
    pairAt μ Φ (a • Ψ) c = conj a * pairAt μ Φ Ψ c := by
  simp only [pairAt, Submodule.coe_smul, Pi.smul_apply, hsInner_smul_right']
  exact integral_const_mul _ _

variable {μ : Measure (Mt k r)} {U : Submodule ℂ (RadSp k r z z' π π')}

private theorem hsInner_add_left' (A A' C : Wq →L[ℂ] Wp) :
    B.hsInner (A + A') C = B.hsInner A C + B.hsInner A' C := by
  have h : B.hsVec (A + A') = B.hsVec A + B.hsVec A' := by
    ext i
    simp [B.hsVec]
  simp only [B.hsInner, h, inner_add_right]

theorem pairAt_add_left (hU : IntOn μ U) {c : Fin r → ℂ} (hc : c ∈ OmX r) {Φ Φ' Ψ : RadSp k r z z' π π'}
    (hΦ : Φ ∈ U) (hΦ' : Φ' ∈ U) (hΨ : Ψ ∈ U) :
    pairAt μ (Φ + Φ') Ψ c = pairAt μ Φ Ψ c + pairAt μ Φ' Ψ c := by
  simp only [pairAt, Submodule.coe_add, Pi.add_apply, hsInner_add_left']
  exact integral_add (hU c hc Φ hΦ Ψ hΨ) (hU c hc Φ' hΦ' Ψ hΨ)

private theorem hsInner_add_right' (A C C' : Wq →L[ℂ] Wp) :
    B.hsInner A (C + C') = B.hsInner A C + B.hsInner A C' := by
  have h : B.hsVec (C + C') = B.hsVec C + B.hsVec C' := by
    ext i
    simp [B.hsVec]
  simp only [B.hsInner, h, inner_add_left]

theorem pairAt_add_right (hU : IntOn μ U) {c : Fin r → ℂ} (hc : c ∈ OmX r) {Φ Ψ Ψ' : RadSp k r z z' π π'}
    (hΦ : Φ ∈ U) (hΨ : Ψ ∈ U) (hΨ' : Ψ' ∈ U) :
    pairAt μ Φ (Ψ + Ψ') c = pairAt μ Φ Ψ c + pairAt μ Φ Ψ' c := by
  simp only [pairAt, Submodule.coe_add, Pi.add_apply, hsInner_add_right']
  exact integral_add (hU c hc Φ hΦ Ψ hΨ) (hU c hc Φ hΦ Ψ' hΨ')

private theorem pairAt_zero_left' (Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) : pairAt μ 0 Ψ c = 0 := by
  simp only [pairAt, Submodule.coe_zero, Pi.zero_apply, hsInner_zero_left, integral_zero]

theorem pairAt_sum_left (hU : IntOn μ U) {c : Fin r → ℂ} (hc : c ∈ OmX r) {ι : Type} (s : Finset ι)
    (Φ : ι → RadSp k r z z' π π') (hΦ : ∀ i, Φ i ∈ U) {Ψ : RadSp k r z z' π π'} (hΨ : Ψ ∈ U) :
    pairAt μ (∑ i ∈ s, Φ i) Ψ c = ∑ i ∈ s, pairAt μ (Φ i) Ψ c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, pairAt_zero_left']
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      pairAt_add_left hU hc (hΦ j) (U.sum_mem fun i _ => hΦ i) hΨ, ih]

private theorem pairAt_zero_right' (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) : pairAt μ Φ 0 c = 0 := by
  rw [pairAt_swap, pairAt_zero_left', map_zero]

theorem pairAt_sum_right (hU : IntOn μ U) {c : Fin r → ℂ} (hc : c ∈ OmX r) {ι : Type} (s : Finset ι)
    {Φ : RadSp k r z z' π π'} (hΦ : Φ ∈ U) (Ψ : ι → RadSp k r z z' π π') (hΨ : ∀ i, Ψ i ∈ U) :
    pairAt μ Φ (∑ i ∈ s, Ψ i) c = ∑ i ∈ s, pairAt μ Φ (Ψ i) c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, pairAt_zero_right']
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      pairAt_add_right hU hc hΦ (hΨ j) (U.sum_mem fun i _ => hΨ i), ih]

theorem pr_alg_fst (a : ℂ) : (algebraMap ℂ (Pr (RadSp k r z z' π π')) a).1 = algebraMap ℂ _ a := rfl

theorem pr_alg_snd (a : ℂ) : (algebraMap ℂ (Pr (RadSp k r z z' π π')) a).2.unop = algebraMap ℂ _ (conj a) := rfl

def adjAlg (μ : Measure (Mt k r)) (U : Submodule ℂ (RadSp k r z z' π π')) (hU : IntOn μ U) :
    StarSubalgebra ℂ (Pr (RadSp k r z z' π π')) where
  carrier := {a | AdjOn μ U a}
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha⟩ ⟨hb1, hb2, hb⟩
    refine ⟨fun Φ hΦ => ha1 _ (hb1 Φ hΦ), fun Φ hΦ => hb2 _ (ha2 Φ hΦ), fun c hc Φ hΦ Ψ hΨ => ?_⟩
    change pairAt μ (a.1 (b.1 Φ)) Ψ c = pairAt μ Φ (b.2.unop (a.2.unop Ψ)) c
    rw [ha c hc _ (hb1 Φ hΦ) Ψ hΨ, hb c hc Φ hΦ _ (ha2 Ψ hΨ)]
  add_mem' := by
    rintro a b ⟨ha1, ha2, ha⟩ ⟨hb1, hb2, hb⟩
    refine ⟨fun Φ hΦ => U.add_mem (ha1 Φ hΦ) (hb1 Φ hΦ), fun Φ hΦ => U.add_mem (ha2 Φ hΦ) (hb2 Φ hΦ),
      fun c hc Φ hΦ Ψ hΨ => ?_⟩
    change pairAt μ (a.1 Φ + b.1 Φ) Ψ c = pairAt μ Φ (a.2.unop Ψ + b.2.unop Ψ) c
    rw [pairAt_add_left hU hc (ha1 Φ hΦ) (hb1 Φ hΦ) hΨ, pairAt_add_right hU hc hΦ (ha2 Ψ hΨ) (hb2 Ψ hΨ),
      ha c hc Φ hΦ Ψ hΨ, hb c hc Φ hΦ Ψ hΨ]
  algebraMap_mem' := by
    intro a
    refine ⟨fun Φ hΦ => ?_, fun Φ hΦ => ?_, fun c hc Φ hΦ Ψ hΨ => ?_⟩
    · rw [pr_alg_fst, Module.algebraMap_end_apply]; exact U.smul_mem a hΦ
    · rw [pr_alg_snd, Module.algebraMap_end_apply]; exact U.smul_mem _ hΦ
    · rw [pr_alg_fst, pr_alg_snd, Module.algebraMap_end_apply, Module.algebraMap_end_apply, pairAt_smul_left,
        pairAt_smul_right, Complex.conj_conj]
  star_mem' := by
    rintro a ⟨ha1, ha2, ha⟩
    refine ⟨ha2, ha1, fun c hc Φ hΦ Ψ hΨ => ?_⟩
    change pairAt μ (a.2.unop Φ) Ψ c = pairAt μ Φ (a.1 Ψ) c
    rw [pairAt_swap μ Ψ, ← ha c hc Ψ hΨ Φ hΦ, ← pairAt_swap]

theorem mem_adjAlg {hU : IntOn μ U} {a : Pr (RadSp k r z z' π π')} : a ∈ adjAlg μ U hU ↔ AdjOn μ U a := by
  exact Iff.rfl

theorem pairAt_snd_left {hU : IntOn μ U} {a : Pr (RadSp k r z z' π π')} (ha : a ∈ adjAlg μ U hU) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) {Φ Ψ : RadSp k r z z' π π'} (hΦ : Φ ∈ U) (hΨ : Ψ ∈ U) :
    pairAt μ (a.2.unop Φ) Ψ c = pairAt μ Φ (a.1 Ψ) c := by
  have h := (mem_adjAlg.mp ha).2.2 c hc Ψ hΨ Φ hΦ
  rw [pairAt_swap μ Ψ (a.2.unop Φ) c, ← h]
  exact (pairAt_swap μ (a.1 Ψ) Φ c).symm

theorem act_mem {hU : IntOn μ U} (M : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (hM : ∀ a b, M a b ∈ adjAlg μ U hU)
    (x : Ix S → RadSp k r z z' π π') (hx : ∀ a, x a ∈ U) (a : Ix S) : act M x a ∈ U := by
  show (∑ b, (M a b).1 (x b)) ∈ U
  exact U.sum_mem fun b _ => (mem_adjAlg.mp (hM a b)).1 _ (hx b)

theorem mul_mem_entries {hU : IntOn μ U} (M N : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (hM : ∀ a b, M a b ∈ adjAlg μ U hU)
    (hN : ∀ a b, N a b ∈ adjAlg μ U hU) (a b : Ix S) : (M * N) a b ∈ adjAlg μ U hU := by
  rw [Matrix.mul_apply]
  exact sum_mem fun e _ => Subalgebra.mul_mem _ (hM a e) (hN e b)

theorem sum_pairAt_star_mul {hU : IntOn μ U} (M N : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π')))
    (hM : ∀ a b, M a b ∈ adjAlg μ U hU) (hN : ∀ a b, N a b ∈ adjAlg μ U hU)
    (x y : Ix S → RadSp k r z z' π π') (hx : ∀ a, x a ∈ U) (hy : ∀ a, y a ∈ U) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    ∑ a, pairAt μ (act (star M * N) x a) (y a) c = ∑ e, pairAt μ (act N x e) (act M y e) c := by
  have hu : ∀ e, act N x e ∈ U := act_mem N hN x hx
  have hL : ∀ a, act (star M * N) x a = ∑ e, (M e a).2.unop (act N x e) := by
    intro a
    rw [act_mul]
    rfl
  calc ∑ a, pairAt μ (act (star M * N) x a) (y a) c
      = ∑ a, ∑ e, pairAt μ (act N x e) ((M e a).1 (y a)) c := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hL a, pairAt_sum_left hU hc _ _ (fun e => (mem_adjAlg.mp (hM e a)).2.1 _ (hu e)) (hy a)]
        exact Finset.sum_congr rfl fun e _ => pairAt_snd_left (hM e a) hc (hu e) (hy a)
    _ = ∑ e, ∑ a, pairAt μ (act N x e) ((M e a).1 (y a)) c := Finset.sum_comm
    _ = ∑ e, pairAt μ (act N x e) (act M y e) c := by
        refine Finset.sum_congr rfl fun e _ => ?_
        exact (pairAt_sum_right hU hc _ (hu e) _ (fun a => (mem_adjAlg.mp (hM e a)).1 _ (hy a))).symm

end Gen

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem adjTop_of_adjAlg (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (U : Submodule ℂ (RadSp P.k P.r z z' π π')) (hU : IntOn μ U) (hK : K (Fin.last P.r) ≤ U)
    (hF : ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ e e',
      (Fr.ofWord L st w).F e e' ∈ adjAlg μ U hU ∧ (Fr.ofWord L st w).d L e e' ∈ adjAlg μ U hU) :
    AdjTop (S := S) P z z' π π' μ L st K l0 := by
  intro w hw x y hx hy c hc
  have hFF : ∀ e e', (Fr.ofWord L st w).F e e' ∈ adjAlg μ U hU := fun e e' => (hF w hw e e').1
  have hFd : ∀ e e', (Fr.ofWord L st w).d L e e' ∈ adjAlg μ U hU := fun e e' => (hF w hw e e').2
  have hxU : ∀ a, x a ∈ U := fun a => hK (hx a)
  have hyU : ∀ a, y a ∈ U := fun a => hK (hy a)
  have hDF := mul_mem_entries _ _ hFd hFF
  have hu := act_mem _ hDF x hxU
  have hv := act_mem _ hFF y hyU
  have hint := fun e => hU c hc _ (hu e) _ (hv e)
  refine ⟨?_, ?_⟩
  · simp only [topDens]
    exact integrable_finsetSum Finset.univ fun e _ => hint e
  · rw [form_last, mul_assoc, sum_pairAt_star_mul _ _ hFF hDF x y hxU hyU hc]
    simp only [topDens]
    rw [integral_finsetSum Finset.univ fun e _ => hint e]
    rfl

end Top

end Formalism.FourierDecayAlt.P5.HerA
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

set_option maxHeartbeats 1600000

namespace Formalism.FourierDecayAlt.P.DDSmoothness

open Formalism.FourierDecayAlt.ThreeDimData

section Meas

variable {k r : ℕ}

theorem uh_mul {a b : Mx k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    a * b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
  show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
  calc (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by rw [ha', hb']

theorem uh_cancel {a x : Mx k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hax : a * x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hax' : (a * x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * x) = Formalism.QuantumDeterminants.Hpk k r := hax
  show xᴴ * Formalism.QuantumDeterminants.Hpk k r * x = Formalism.QuantumDeterminants.Hpk k r
  calc xᴴ * Formalism.QuantumDeterminants.Hpk k r * x = xᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * x := by rw [ha']
    _ = (a * x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * x) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := hax'

theorem uh_measurableSet :
    MeasurableSet {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := by
  have hc : IsClosed {x : Formalism.QuantumDeterminants.Mt k r | (Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of x = Formalism.QuantumDeterminants.Hpk k r} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  exact hc.measurableSet.compl

theorem ae_UH_of_quot {μG μS νq : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hG : μG {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0)
    (hS0 : μS ≠ 0) (hS : μS {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0)
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG μS νq) :
    ∀ᵐ x ∂νq, Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  classical
  set B : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} with hBdef
  have hBm : MeasurableSet B := uh_measurableSet
  have key := hq (B.indicator 1) (measurable_one.indicator hBm)
  rw [lintegral_indicator_one hBm, hG] at key
  have hc : μS Bᶜ ≠ 0 := by
    intro h0
    apply hS0
    rw [← Measure.measure_univ_eq_zero]
    refine le_antisymm ?_ zero_le
    calc μS Set.univ = μS (B ∪ Bᶜ) := by rw [Set.union_compl_self]
      _ ≤ μS B + μS Bᶜ := measure_union_le _ _
      _ = 0 := by rw [hS, h0, add_zero]
  have hle : ∀ x, μS Bᶜ * B.indicator 1 x ≤
      ∫⁻ s, B.indicator 1 (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one, ← lintegral_indicator_one hBm.compl]
      refine lintegral_mono fun s => ?_
      by_cases hs : Matrix.of s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)
      · have hsx : (fun i j => (Matrix.of s * Matrix.of x) i j) ∈ B := fun hmem =>
          hx (uh_cancel (x := Matrix.of x) hs hmem)
        have hsB : s ∈ Bᶜ := fun h => h hs
        rw [Set.indicator_of_mem hsB, Set.indicator_of_mem hsx]
        exact le_rfl
      · have hsB : s ∉ Bᶜ := fun h => h hs
        rw [Set.indicator_of_notMem hsB]
        exact zero_le
    · rw [Set.indicator_apply, if_neg hx, mul_zero]
      exact zero_le
  have h0 : μS Bᶜ * νq B = 0 := by
    rw [← lintegral_indicator_one hBm, ← lintegral_const_mul _ (measurable_one.indicator hBm)]
    refine le_antisymm ?_ zero_le
    calc ∫⁻ x, μS Bᶜ * B.indicator 1 x ∂νq
        ≤ ∫⁻ x, ∫⁻ s, B.indicator 1 (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS ∂νq := lintegral_mono hle
      _ = 0 := key.symm
  have hνB : νq B = 0 := (mul_eq_zero.mp h0).resolve_left hc
  rw [ae_iff]
  exact hνB

theorem muSof_facts {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) :
    muSof μW μN ≠ 0 ∧ muSof μW μN {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0 := by
  obtain ⟨hWs, hW0, hWb, -⟩ := hW
  obtain ⟨hNs, hN0, hNb, -⟩ := hN
  haveI := hWs
  haveI := hNs
  have hcont : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  have hmeas := hcont.measurable
  refine ⟨?_, ?_⟩
  · intro h0
    unfold muSof at h0
    rw [Measure.map_eq_zero_iff hmeas.aemeasurable] at h0
    have h1 : (μW.prod μN) Set.univ = 0 := by rw [h0, Measure.coe_zero, Pi.zero_apply]
    rw [← Set.univ_prod_univ, Measure.prod_prod, mul_eq_zero] at h1
    rcases h1 with h | h
    · exact hW0 (Measure.measure_univ_eq_zero.mp h)
    · exact hN0 (Measure.measure_univ_eq_zero.mp h)
  · unfold muSof
    rw [Measure.map_apply hmeas uh_measurableSet]
    refine measure_mono_null (t := {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UWset k r z} ×ˢ Set.univ ∪
      Set.univ ×ˢ {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.Nset k r}) ?_ ?_
    · rintro ⟨a, b⟩ hab
      by_contra hno
      simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, and_true, true_and, Set.mem_setOf_eq, not_or,
        not_not] at hno
      exact hab (uh_mul hno.1.1 hno.2.1)
    · refine measure_union_null ?_ ?_
      · rw [Measure.prod_prod, hWb, zero_mul]
      · rw [Measure.prod_prod, hNb, mul_zero]

end Meas

section Deg

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem fdeg_eq {σ : Mx k r → (H →L[ℂ] H)} {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} {d : ℝ} (hd : 0 < d)
    (hS : ∀ v w v' w' : H,
      Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ))
    {u : H} (hu : u ≠ 0) : PI.BesselPeriodGGP.fdegH μG σ u = d := by
  obtain ⟨-, hI⟩ := hS u u u u
  have hpt : ∀ x : Formalism.QuantumDeterminants.Mt k r, ⟪u, σ (Matrix.of x) u⟫_ℂ * star ⟪u, σ (Matrix.of x) u⟫_ℂ =
      ((‖⟪u, σ (Matrix.of x) u⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [hpt] at hI
  rw [integral_complex_ofReal] at hI
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hu4 : (0 : ℝ) < ‖u‖ ^ 4 := pow_pos hn 4
  have huu : ⟪u, u⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]
      exact inner_self_eq_norm_sq (𝕜 := ℂ) u
    · rw [Complex.ofReal_im]
      exact inner_self_im (𝕜 := ℂ) u
  have hreal : ∫ x, ‖⟪u, σ (Matrix.of x) u⟫_ℂ‖ ^ 2 ∂μG = ‖u‖ ^ 4 / d := by
    apply Complex.ofReal_injective
    rw [hI, huu]
    push_cast
    ring
  unfold PI.BesselPeriodGGP.fdegH
  rw [hreal]
  field_simp

end Deg

section Bessel

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

theorem bessel_smul {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mx k r → ℂ} {σ : Mx k r → (H →L[ℂ] H)}
    {π : Mx k r → (Wp →L[ℂ] Wp)} {B : H → Wp}
    (hB : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π B) (κ : ℂ) :
    PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π (fun x => κ • B x) := by
  obtain ⟨hadd, hsm, heq, C, Ws, hWs, hbd⟩ := hB
  refine ⟨fun v hv w hw => ?_, fun c v hv => ?_, fun h hh m hm v hv => ?_, ‖κ‖ * C, Ws, hWs, fun v hv => ?_⟩
  · simp only [hadd v hv w hw, smul_add]
  · simp only [hsm c v hv]
    exact smul_comm κ c (B v)
  · simp only [heq h hh m hm v hv, map_smul]
    exact smul_comm κ (ψ m) _
  · rw [norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbd v hv) (norm_nonneg κ)

theorem bessel_zero {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mx k r → ℂ} {σ : Mx k r → (H →L[ℂ] H)}
    {π : Mx k r → (Wp →L[ℂ] Wp)} :
    PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π (fun _ => (0 : Wp)) := by
  refine ⟨fun _ _ _ _ => by simp, fun _ _ _ => by simp, fun _ _ _ _ _ _ => by simp, 0, [], by simp,
    fun _ _ => by simp⟩

theorem jsz_line (hU : PI.BesselMapUniq.BesselMapUniq) (hPsi : PsiConst)
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hc : c ≠ 0) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {B0 B : H → Wp}
    (h0 : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (Formalism.QuantumDeterminants.psi k r z c) σ π B0)
    (h : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (Formalism.QuantumDeterminants.psi k r z c) σ π B)
    {x0 : H} (hx0 : x0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) (hne : B0 x0 ≠ 0) :
    ∃ κ : ℂ, ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, B x = κ • B0 x := by
  have hfun : Formalism.QuantumDeterminants.psi k r z c = PI.BesselMapUniq.psiGen k r z (fun _ => c) :=
    funext fun g => hPsi k r z c g
  rw [hfun] at h0 h
  obtain ⟨a, b, hab, hlin⟩ := hU k r ε lam H σ z (fun _ => c) u Wp π hl hσ hz hT (fun _ => hc) hπ B0 B h0 h
  have hb : b ≠ 0 := by
    rintro rfl
    have ha : a ≠ 0 := hab.resolve_right (fun h => h rfl)
    have h2 := hlin x0 hx0
    rw [zero_smul, add_zero, smul_eq_zero] at h2
    exact h2.elim ha hne
  refine ⟨-(a / b), fun x hx => ?_⟩
  have h1 : b • B x = -(a • B0 x) := eq_neg_of_add_eq_zero_right (hlin x hx)
  calc B x = b⁻¹ • (b • B x) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
    _ = -(a / b) • B0 x := by rw [h1, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

end Bessel

end Formalism.FourierDecayAlt.P.DDSmoothness
end
end

