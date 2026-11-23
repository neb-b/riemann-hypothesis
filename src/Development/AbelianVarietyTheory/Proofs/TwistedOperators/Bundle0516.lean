module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0473
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NablaUnipotentMemIntegralDoubledUnipotent
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitDblNab

open Matrix

section Generic

variable {A : Type} [CommRing A] {ι : Type} [Fintype ι] [DecidableEq ι]

def blkN (N : Matrix ι ι A) : Matrix (ι ⊕ ι) (ι ⊕ ι) A := fromBlocks (1 + N) N (-N) (1 - N)

theorem blkN_mul_neg (N : Matrix ι ι A) : blkN N * blkN (-N) = 1 := by
  rw [blkN, blkN, fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;> noncomm_ring

theorem neg_mul_blkN (N : Matrix ι ι A) : blkN (-N) * blkN N = 1 := by
  have h := blkN_mul_neg (-N)
  rwa [neg_neg] at h

theorem blkN_eq (N : Matrix ι ι A) :
    1 + (fromRows (1 : Matrix ι ι A) (-1) * N) * (fromRows (1 : Matrix ι ι A) 1)ᵀ = blkN N := by
  rw [fromRows_mul, transpose_fromRows, fromRows_mul_fromCols, ← fromBlocks_one, fromBlocks_add, blkN]
  simp [sub_eq_add_neg]

-- Select matrix multiplication explicitly to avoid the `CStarMatrix` default instance.
local infixl:70 " ⬝ₘ " => @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem blkN_anti (N : Matrix ι ι A) : blkN N ⬝ₘ fromRows (1 : Matrix ι ι A) (-1) = fromRows 1 (-1) := by
  rw [blkN, fromBlocks_mul_fromRows]
  congr 1 <;> noncomm_ring

theorem blkN_diag (N : Matrix ι ι A) :
    blkN N ⬝ₘ fromRows (1 : Matrix ι ι A) 1 = fromRows 1 1 + fromRows (1 : Matrix ι ι A) (-1) ⬝ₘ (N + N) := by
  rw [blkN, fromBlocks_mul_fromRows, fromRows_mul]
  ext (i | i) j <;> simp <;> ring

theorem blkN_unitary (s : A →+* A) (J N : Matrix ι ι A) (h : Nᵀ * J + J * N.map s = 0) :
    (blkN N)ᵀ * dbl J * (blkN N).map s = dbl J := by
  have h1 : (1 + N).map s = 1 + N.map s := by
    rw [Matrix.map_add _ (map_add s), Matrix.map_one _ (map_zero s) (map_one s)]
  have h2 : (1 - N).map s = 1 - N.map s := by
    rw [Matrix.map_sub _ (map_sub s), Matrix.map_one _ (map_zero s) (map_one s)]
  have h3 : (-N).map s = - N.map s := by ext i j; simp
  rw [blkN, fromBlocks_map, fromBlocks_transpose, dbl, fromBlocks_multiply, fromBlocks_multiply, h1, h2, h3,
    transpose_add, transpose_sub, transpose_neg, transpose_one]
  generalize Nᵀ = P at h ⊢
  generalize N.map s = Q at h ⊢
  congr 1
  · calc _ = J + (P * J + J * Q) := by noncomm_ring
      _ = J := by rw [h, add_zero]
  · calc _ = P * J + J * Q := by noncomm_ring
      _ = 0 := h
  · calc _ = P * J + J * Q := by noncomm_ring
      _ = 0 := h
  · calc _ = -J + (P * J + J * Q) := by noncomm_ring
      _ = -J := by rw [h, add_zero]

theorem skew_block (s : A →+* A) (J K K' : Matrix ι ι A) (a c : A) (ha : s a = a) (hc : s c = -c)
    (hKK : K * K' = 1) (hKK' : K' * K = 1) (hK : Kᵀ * J * K.map s = J) (hK' : K'ᵀ * J * K'.map s = J) :
    (a • ((1 - c) • (K - 1) - (1 + c) • (K' - 1)))ᵀ * J +
      J * (a • ((1 - c) • (K - 1) - (1 + c) • (K' - 1))).map s = 0 := by
  have e1 : J * K.map s = K'ᵀ * J := by
    calc J * K.map s = (K * K')ᵀ * J * K.map s := by rw [hKK, transpose_one, Matrix.one_mul]
      _ = K'ᵀ * (Kᵀ * J * K.map s) := by rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hK]
  have e2 : J * K'.map s = Kᵀ * J := by
    calc J * K'.map s = (K' * K)ᵀ * J * K'.map s := by rw [hKK', transpose_one, Matrix.one_mul]
      _ = Kᵀ * (K'ᵀ * J * K'.map s) := by rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hK']
  have e3 : (a • ((1 - c) • (K - 1) - (1 + c) • (K' - 1))).map s =
      a • ((1 + c) • (K.map s - 1) - (1 - c) • (K'.map s - 1)) := by
    ext i j
    have h1 : s ((1 : Matrix ι ι A) i j) = (1 : Matrix ι ι A) i j :=
      congrFun (congrFun (Matrix.map_one s (map_zero _) (map_one _)) i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, map_mul, map_sub, map_add (f := _), map_one,
      ha, hc, h1]
    ring
  rw [e3]
  simp only [transpose_smul, transpose_sub, transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, e1, e2]
  rw [← smul_add]
  simp

theorem blkN_mulVec_inl (N : Matrix ι ι A) (z : ι ⊕ ι → A) :
    (fun i => (blkN N *ᵥ z) (Sum.inl i)) =
      (fun i => z (Sum.inl i)) + N *ᵥ (fun i => z (Sum.inl i)) + N *ᵥ (fun i => z (Sum.inr i)) := by
  rw [blkN, fromBlocks_mulVec, add_mulVec, one_mulVec]
  rfl

theorem blkN_mulVec_inr (N : Matrix ι ι A) (z : ι ⊕ ι → A) :
    (fun i => (blkN N *ᵥ z) (Sum.inr i)) =
      -(N *ᵥ (fun i => z (Sum.inl i))) + ((fun i => z (Sum.inr i)) - N *ᵥ (fun i => z (Sum.inr i))) := by
  rw [blkN, fromBlocks_mulVec, sub_mulVec, one_mulVec, neg_mulVec]
  rfl

theorem blkN_sub_one (N : Matrix ι ι A) : blkN N - 1 = fromBlocks N N (-N) (-N) := by
  ext (i | i) (j | j) <;> simp [blkN, Matrix.one_apply]

end Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem smul_mem_latAt_of_int {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) {x : AF F}
    (hx : evFin F v x ∈ v.adicCompletionIntegers F) {y : Fin d → AE F E}
    (hy : y ∈ GlobalTheory.InertSph.latAt W v) : x • y ∈ GlobalTheory.InertSph.latAt W v := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, y, hy, rfl⟩ := hz
    rw [smul_smul]
    refine AddSubgroup.subset_closure ⟨x * a, ?_, ?_, y, hy, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
    · rw [map_mul]
      exact mul_mem hx hv
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem evFin_invTwo_mem (v : Pl (F := F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := by
  have h : evFin F v (⅟(2 : AF F)) * algebraMap F (Fv F v) (algebraMap (𝓞 F) F 2) = 1 := by
    rw [map_ofNat, map_ofNat, ← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
  have hv : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F 2)) = 1 := by
    have := v.valuedAdicCompletion_eq_valuation' (K := F) (algebraMap (𝓞 F) F 2)
    rw [HeightOneSpectrum.valuation_of_algebraMap, (HeightOneSpectrum.intValuation_eq_one_iff).2 h2] at this
    exact this
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h' := congrArg (Valued.v : v.adicCompletion F → _) h
  rw [map_mul, map_one, hv, mul_one] at h'
  exact h'.le

theorem half_smul_mem {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) {y : Fin d → AE F E}
    (hy : y ∈ GlobalTheory.InertSph.latAt W v) : (GlobalTheory.SplitDblGen.half : AE F E) • y ∈ GlobalTheory.InertSph.latAt W v := by
  rw [GlobalTheory.SplitDblGen.half, algebraMap_smul]
  exact smul_mem_latAt_of_int W v (evFin_invTwo_mem v h2) hy

theorem nMat_mem_NabD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ c : AE F E, cA σ c = -c → (∀ z ∈ GlobalTheory.InertSph.latAt W v, c • z ∈ GlobalTheory.InertSph.latAt W v) →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, ∃ n ∈ GlobalTheory.InertDbl.NabD σ W v,
      GlobalTheory.InertDbl.matD n = GlobalTheory.SplitDblGen.nMat c (mat k) (mat k⁻¹) := by
  intro F E _ _ _ _ _ σ d W v h2 c hc hcL k hk
  set N := GlobalTheory.SplitDblGen.splitDoublingNBlock c (mat k) (mat k⁻¹) with hN
  have hKK : mat k * mat k⁻¹ = 1 := congrArg Units.val (mul_inv_cancel (k : GL (Fin d) (AE F E)))
  have hKK' : mat k⁻¹ * mat k = 1 := congrArg Units.val (inv_mul_cancel (k : GL (Fin d) (AE F E)))
  have hhalf : (cA σ) (GlobalTheory.SplitDblGen.half : AE F E) = GlobalTheory.SplitDblGen.half := (cA σ).commutes _
  have hsk : Nᵀ * incM F W.J + incM F W.J * N.map (cA σ : AE F E →+* AE F E) = 0 :=
    skew_block (cA σ : AE F E →+* AE F E) (incM F W.J) (mat k) (mat k⁻¹) _ c
      (by simp only [RingHom.coe_coe, map_mul, hhalf]) hc hKK hKK' k.2 (k⁻¹).2
  have hNL : ∀ z ∈ GlobalTheory.InertSph.latAt W v, N *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
    intro z hz
    have a1 : (mat k - 1) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
      rw [sub_mulVec, one_mulVec]; exact sub_mem (hk.2 z hz).1 hz
    have a2 : (mat k⁻¹ - 1) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
      rw [sub_mulVec, one_mulVec]; exact sub_mem (hk.2 z hz).2 hz
    rw [hN, GlobalTheory.SplitDblGen.splitDoublingNBlock, smul_mulVec, mul_smul, mul_smul, sub_mulVec, smul_mulVec, smul_mulVec, sub_smul,
      add_smul, one_smul, one_smul]
    exact half_smul_mem W v h2 (half_smul_mem W v h2 (half_smul_mem W v h2
      (sub_mem (sub_mem a1 (hcL _ a1)) (add_mem a2 (hcL _ a2)))))
  have hblk : ∀ M : Matrix (Fin d) (Fin d) (AE F E), (∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
      ∀ z ∈ GlobalTheory.InertDbl.latAtD W v, blkN M *ᵥ z ∈ GlobalTheory.InertDbl.latAtD W v := by
    intro M hM z hz
    refine ⟨?_, ?_⟩
    · rw [blkN_mulVec_inl]; exact add_mem (add_mem hz.1 (hM _ hz.1)) (hM _ hz.2)
    · rw [blkN_mulVec_inr]; exact add_mem (neg_mem (hM _ hz.1)) (sub_mem hz.2 (hM _ hz.2))
  refine ⟨⟨⟨blkN N, blkN (-N), blkN_mul_neg N, neg_mul_blkN N⟩,
    blkN_unitary (cA σ : AE F E →+* AE F E) _ N hsk⟩, ⟨⟨fun u hu => ?_, fun z hz => ⟨hblk N hNL z hz, ?_⟩⟩,
      blkN_anti N, N + N, blkN_diag N⟩, (blkN_eq N).symm⟩
  · have b1 : u • (mat k - 1) = 0 := hk.1 u hu
    have b2 : u • (mat k⁻¹ - 1) = 0 := by
      have e1 : mat k⁻¹ - 1 = -(mat k⁻¹ * (mat k - 1)) := by
        rw [Matrix.mul_sub, hKK', Matrix.mul_one, neg_sub]
      rw [e1, smul_neg, ← Matrix.mul_smul, b1, Matrix.mul_zero, neg_zero]
    have b3 : u • N = 0 := by
      rw [hN, GlobalTheory.SplitDblGen.splitDoublingNBlock, smul_comm u, smul_sub u, smul_comm u, smul_comm u (1 + c), b1, b2, smul_zero,
        smul_zero, sub_zero, smul_zero]
    show u • (blkN N - 1) = 0
    rw [blkN_sub_one, fromBlocks_smul, smul_neg, b3, neg_zero, fromBlocks_zero]
  · exact hblk (-N) (fun y hy => by rw [neg_mulVec]; exact neg_mem (hNL y hy)) z hz

end GlobalTheory.SplitDblNab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OffIdempotentScaleMemCompletedTensorLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.OffIdemLat

open GlobalTheory.IdemSupport GlobalTheory.OffIdemDen

variable {D : D7}

abbrev conjProd (SS : Finset (Formalism.L2.DIV.Pl D.host.E)) : Ideal (𝓞 D.host.E) := ∏ PP ∈ SS, conjI PP.asIdeal

theorem cP_mem_of_le {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} {Q : HeightOneSpectrum (𝓞 D.host.E)}
    (h : conjProd SS ≤ Q.asIdeal) : cP Q ∈ SS := by
  obtain ⟨PP, hPP, hle⟩ := (Ideal.IsPrime.prod_le Q.isPrime).1 h
  have : PP = cP Q := eq_of_le fun x hx => by
    rw [mem_cP]
    exact hle (Ideal.subset_span ⟨x, hx, rfl⟩)
  exact this ▸ hPP

theorem conjProd_ne_bot (SS : Finset (Formalism.L2.DIV.Pl D.host.E)) : conjProd SS ≠ ⊥ := by
  rw [← Ideal.zero_eq_bot]
  refine Finset.prod_ne_zero_iff.2 fun PP _ => ?_
  rw [Ne, Ideal.zero_eq_bot, GlobalTheory.LiftIdeal.conjI_eq_map,
    Ideal.map_eq_bot_iff_of_injective (f := (GlobalTheory.LiftIdeal.conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E))
      (GlobalTheory.LiftIdeal.conjO D).injective]
  exact PP.ne_bot

end GlobalTheory.OffIdemLat

namespace GlobalTheory.OffIdemLat
open GlobalTheory.IdemSupport GlobalTheory.OffIdemDen
variable {D : D7}

theorem finPart_mul_mem (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)) (he : IsIdemSum e SS) (x : D.host.E)
    (hx : ∀ j ∈ conjProd SS, ∃ o : 𝓞 D.host.E, (o : D.host.E) = x * (j : D.host.E)) :
    finPart D ((1 - e - cA D e) * incA D x) ∈ intAE D := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨⟨es, hes, rfl⟩, horth⟩ := he
  have hd : ∀ P ∈ SS, IsDelta Φ P (es P) := fun P hP => delta_of_isIdemAt hΦ (hes P hP)
  have hdc : ∀ P ∈ SS, IsDelta Φ (cP P) (cA D (es P)) := fun P hP => delta_conj hΦ (hd P hP)
  have hE : ∀ Q, Φ (∑ P ∈ SS, es P) Q = ∑ P ∈ SS, Φ (es P) Q := fun Q => map_sum (evQ Φ Q) _ _
  have hC : ∀ Q, Φ (cA D (∑ P ∈ SS, es P)) Q = ∑ P ∈ SS, Φ (cA D (es P)) Q := fun Q => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; exact map_sum (evQ Φ Q) _ _
  have hO : ∀ Q, Φ (1 - ∑ P ∈ SS, es P - cA D (∑ P ∈ SS, es P)) Q =
      1 - Φ (∑ P ∈ SS, es P) Q - Φ (cA D (∑ P ∈ SS, es P)) Q := fun Q => by
    change evQ Φ Q _ = _
    rw [map_sub, map_sub, map_one]; rfl
  have hprod : ∀ Q, Φ (∑ P ∈ SS, es P) Q * Φ (cA D (∑ P ∈ SS, es P)) Q = 0 := fun Q => by
    rw [← ev_mul, horth, ev_zero]
  rw [hΦ.int]
  intro Q
  rw [ev_mul, hΦ.inc]
  by_cases hQ : Q ∈ SS ∨ cP Q ∈ SS
  · have h0 : Φ (1 - ∑ P ∈ SS, es P - cA D (∑ P ∈ SS, es P)) Q = 0 := by
      rw [hO]
      rcases hQ with hQ | hQ
      · have h1 : Φ (∑ P ∈ SS, es P) Q = 1 := by
          rw [hE, Finset.sum_eq_single Q (fun P hP hne => (hd P hP).2.2 Q (Ne.symm hne))
            (fun h => absurd hQ h), (hd Q hQ).2.1]
        have h2 := hprod Q
        rw [h1, one_mul] at h2
        rw [h1, h2, sub_self, sub_zero]
      · have h1 : Φ (cA D (∑ P ∈ SS, es P)) Q = 1 := by
          rw [hC, Finset.sum_eq_single (cP Q) (fun P hP hne => (hdc P hP).2.2 Q (fun h => hne (by
              rw [h, cP_cP])))
            (fun h => absurd hQ h)]
          have := (hdc (cP Q) hQ).2.1
          rwa [cP_cP] at this
        have h2 := hprod Q
        rw [h1, mul_one] at h2
        rw [h1, h2, sub_zero, sub_self]
    rw [h0, zero_mul]
    exact (Q.adicCompletionIntegers D.host.E).zero_mem
  · push_neg at hQ
    refine mul_mem ?_ ?_
    · rw [hO, hE, hC]
      exact sub_mem (sub_mem (Q.adicCompletionIntegers D.host.E).one_mem
        (sum_mem fun P hP => delta_mem (hd P hP) Q)) (sum_mem fun P hP => delta_mem (hdc P hP) Q)
    · have hnle : ¬ conjProd SS ≤ Q.asIdeal := fun h => hQ.2 (cP_mem_of_le h)
      obtain ⟨j, hj, hjQ⟩ := Set.not_subset.1 hnle
      obtain ⟨o, ho⟩ := hx j hj
      have hj0 : j ≠ 0 := fun h => hjQ (h ▸ zero_mem _)
      have hj0' : ((j : 𝓞 D.host.E) : D.host.E) ≠ 0 := fun h => hj0 (RingOfIntegers.ext (h.trans rfl))
      have hxe : x = (o : D.host.E) * ((j : D.host.E))⁻¹ := by
        rw [ho, mul_assoc, mul_inv_cancel₀ hj0', mul_one]
      have hinv := (inv_mem_iff Q hj0).2 hjQ
      have ho' : algebraMap D.host.E (Q.adicCompletion D.host.E) (o : D.host.E) ∈
          Q.adicCompletionIntegers D.host.E := HeightOneSpectrum.coe_mem_adicCompletionIntegers Q o
      change algebraMap D.host.E (Q.adicCompletion D.host.E) x ∈ Q.adicCompletionIntegers D.host.E
      rw [hxe, map_mul]
      exact mul_mem ho' hinv

end GlobalTheory.OffIdemLat

namespace GlobalTheory.OffIdemLat
open GlobalTheory.IdemSupport
variable {D : D7}

theorem fin_smul_mem {S T : HSp D} {J : Ideal (𝓞 D.host.E)} {M N : Lt D.host.E T.rank} (hMN : J • M ≤ N)
    {j : 𝓞 D.host.E} (hj : j ∈ J) {u : WO S T} (hu : u ∈ hatA S T (tens (stdL D.host.E S.rank) M)) :
    (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((j : 𝓞 D.host.E) : D.host.E) : AE D) • u ∈
      hatA S T (tens (stdL D.host.E S.rank) N) := by
  refine GlobalTheory.Ker.SignVac.hatA_induction (p := fun u => (pairA D.host.F 0 1 ⊗ₜ[D.host.F]
      ((j : 𝓞 D.host.E) : D.host.E) : AE D) • u ∈ hatA S T (tens (stdL D.host.E S.rank) N)) ?_ ?_ ?_ ?_ hu
  · intro α hα y hy
    rw [GlobalTheory.LatVac.tmul_smul_finTens, one_mul, ← Matrix.transpose_smul]
    exact GlobalTheory.Ker.SignVac.finTens_mem hα
      (GlobalTheory.LiftLevel.smul_mem_tens _ (fun v hv => hMN (Submodule.smul_mem_smul hj hv)) hy)
  · rw [smul_zero]; exact zero_mem _
  · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
  · intro x hx; rw [smul_neg]; exact neg_mem hx

theorem partAt_off_mem : ∀ (D : D7) (S T : HSp D) (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (M N : Lt D.host.E T.rank), (∏ PP ∈ SS, conjI PP.asIdeal) • M ≤ N → ∀ u ∈ hatA S T (tens (stdL D.host.E S.rank) M), GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u ∈ hatA S T (tens (stdL D.host.E S.rank) N) := by
  intro D S T e SS he M N hMN u hu
  have hA : ∀ o : 𝓞 D.host.E, ∀ y ∈ tens (stdL D.host.E S.rank) N,
      (o : D.host.E) • y ∈ tens (stdL D.host.E S.rank) N :=
    fun o y hy => GlobalTheory.LiftLevel.smul_mem_tens o (fun v hv => Submodule.smul_mem _ o hv) hy
  have hJ : ((conjProd SS : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (conjProd_ne_bot SS)
  have h1 : (1 : D.host.E) ∈ ((conjProd SS : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) *
      ((conjProd SS : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ := by
    rw [mul_inv_cancel₀ hJ]
    exact FractionalIdeal.one_mem_one _
  have key : ((1 - e - cA D e) * incA D 1) • u ∈ hatA S T (tens (stdL D.host.E S.rank) N) := by
    refine FractionalIdeal.mul_induction_on (C := fun z => ((1 - e - cA D e) * incA D z) • u ∈
      hatA S T (tens (stdL D.host.E S.rank) N)) h1 ?_ ?_
    · intro i hi x hx
      obtain ⟨i', hi', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hi
      have hxJ : ∀ j ∈ conjProd SS, ∃ o : 𝓞 D.host.E, (o : D.host.E) = x * (j : D.host.E) := by
        intro j hj
        obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff hJ).1 hx
          (algebraMap (𝓞 D.host.E) D.host.E j) ((FractionalIdeal.mem_coeIdeal _).2 ⟨j, hj, rfl⟩))
        exact ⟨o, ho⟩
      have hint := finPart_mul_mem e SS he x hxJ
      have e1 : ((1 - e - cA D e) * incA D (algebraMap (𝓞 D.host.E) D.host.E i' * x)) • u =
          ((1 - e - cA D e) * incA D x) •
            (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((i' : 𝓞 D.host.E) : D.host.E) : AE D) • u := by
        have e2 : (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((i' : 𝓞 D.host.E) : D.host.E) : AE D) =
            incA D ((i' : 𝓞 D.host.E) : D.host.E) * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)) := by
          change _ = ((1 : AF D.host.F) ⊗ₜ[D.host.F] ((i' : 𝓞 D.host.E) : D.host.E)) * _
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
        rw [e2, mul_smul (incA D ((i' : 𝓞 D.host.E) : D.host.E)), GlobalTheory.Ker.SignVac.one_smul_hatA hu, smul_smul,
          mul_assoc, ← map_mul, mul_comm x]
      rw [e1]
      exact GlobalTheory.LiftLevel.smul_mem_hatA_of_int hA hint (fin_smul_mem hMN hi' hu)
    · intro x y hx hy
      rw [map_add (f := _), mul_add, add_smul]
      exact add_mem hx hy
  rw [map_one, mul_one] at key
  rw [GlobalTheory.LiftLevel.partAt_eq_smul]
  exact key

end GlobalTheory.OffIdemLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowPt0InvMemStdLatIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv GlobalTheory.LastVertexMove GlobalTheory.FirstRowVertex
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.FirstRowLat

variable {D : D7}

theorem givenLevel_zero_le_KO {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E)
    (k : ℕ) (hk : 1 ≤ k) (g : GL (Fin ((locGrid G t w).rank (0, k))) (Kw w)) (hg : g ∈ givenLevel G t w (0, k)) :
    g ∈ GlobalTheory.SplitWeil.KO (Kw w) (Fin ((locGrid G t w).rank (0, k))) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  change g ∈ (stepGroup L t w (j + 1)).map (GlobalTheory.StepData.reGL (ixFin G t w (j + 1))).toMonoidHom at hg
  by_cases hP : w ∈ L.Pg
  · exact ((GlobalTheory.Adopt.thetaGridBlockCongruence_typePrime_description G t w hP (j + 1) g).1 hg).1
  · exact ((GlobalTheory.Adopt.thetaGridBlockCongruence_offTypePrime_description G t w hP (j + 1) g).1 hg).1

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem levRow_zero_stab (S : GridChoice W U) {μ₀ : T} (hL : L.Is μ₀) (t : T) (k : FinPt G (.grid 0 D.R.m))
    (hk : finG (G.V (.grid 0 D.R.m)) k ∈ S.levRow t 0 (Nat.zero_le _)) :
    Lev.finE (G.V (.grid 0 D.R.m)) k.1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.grid 0 D.R.m))) := by
  have hβ : IsFrame (S.B.β 0 D.R.m) (G.Λ (.grid 0 D.R.m)) := S.B.isFrame_β hL (Nat.zero_le _) le_rfl
  have hsd : IsSelfDualC (G.V (.grid 0 D.R.m)) (G.Λ (.grid 0 D.R.m)) := by
    have key : ∀ X : LSp D, X = ⟨D.sp.X', L.ΛX⟩ → IsSelfDualC X.sp X.lat := by
      rintro X rfl
      exact GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hL.βX
    exact key _ (colY_m L)
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have e := GlobalTheory.FunObj.LevRowSucc.prodLev_inf_UA hβ hsd (locPl G t)
    (fun w => rank_vertex G t w (X := (0, D.R.m)) ⟨Nat.zero_le _, le_rfl⟩) (fun w => GlobalTheory.SplitWeil.KO (Kw w.1) _) (fun _ => rfl)
  have hle : S.levRow t 0 (Nat.zero_le _) ≤ prodLev (S.B.β 0 D.R.m) (locPl G t)
      (fun w => rank_vertex G t w (X := (0, D.R.m)) ⟨Nat.zero_le _, le_rfl⟩) (fun w => GlobalTheory.SplitWeil.KO (Kw w.1) _) := by
    refine inf_le_inf_right _ (iInf_mono fun w => Subgroup.comap_mono ?_)
    intro g hg
    exact givenLevel_zero_le_KO G t w.1 D.R.m hm g hg
  have hmem : finG (G.V (.grid 0 D.R.m)) k ∈ prodLev (S.B.β 0 D.R.m) (locPl G t)
      (fun w => rank_vertex G t w (X := (0, D.R.m)) ⟨Nat.zero_le _, le_rfl⟩) (fun w => GlobalTheory.SplitWeil.KO (Kw w.1) _) ⊓
        UA D.sp.cm (G.V (.grid 0 D.R.m)).gram :=
    Subgroup.mem_inf.2 ⟨hle hk, GlobalTheory.LevSplit.finE_mem_UA _ _⟩
  rw [e, congLev_top] at hmem
  exact (Subgroup.mem_inf.1 hmem).2

end GlobalTheory.FirstRowLat

theorem GlobalTheory.FirstRowLat.rowPt0_inv_mem_stdLat_iff : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ₀ : T}, L.Is μ₀ → ∀ {t : T}, t ∈ U → ∀ k : FinPt G (.grid 0 D.R.m), finG (G.V (.grid 0 D.R.m)) k ∈ S.levRow t 0 (Nat.zero_le _) →
    ∀ x : WO (G.pS (.chi (firstIx D) D.R.m : Pair T)) (G.pT (.chi (firstIx D) D.R.m : Pair T)),
      actO _ _ (G.toPair (.chi (firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ x ∈ stdLat S (.chi (firstIx D) D.R.m : Pair T) ↔ x ∈ stdLat S (.chi (firstIx D) D.R.m : Pair T) := by
  intro D T L sc G W U S μ₀ hL t _ k hk x
  have h1 := GlobalTheory.FirstRowLat.levRow_zero_stab S hL t k hk
  have h2 := GlobalTheory.LastColLat.conj_stab S.N (X := .grid 0 D.R.m) (by simp [DefNode]) k h1
  have e : G.toPair (.chi (firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1 =
      (1, ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1) := by
    show (negGA _ 1, _) = _
    rw [map_one]
    rfl
  rw [e]
  exact GlobalTheory.LastColLat.actO_inv_mem_latO_iff _ _ _ _ _ h2 x

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitDoublingTMatrixMulInverseEqOne
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.SplitDblGen

theorem tMat_mul_tMat_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (K K' : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    K * K' = 1 → (c * c) • (K - 1) = K - 1 →
    GlobalTheory.SplitDblGen.tMat c K * GlobalTheory.SplitDblGen.tMat c K' = 1 := by
  intro F E _ _ _ _ _ d c K K' hKK hc
  have h2 : (half : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) * 2 = 1 := by
    unfold half
    rw [show (2 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) 2 from (map_ofNat _ 2).symm, ← map_mul, invOf_mul_self, map_one]
  have hP : (c * c) • ((K - 1) * (K' - 1)) = (K - 1) * (K' - 1) := by rw [← smul_mul_assoc, hc]
  have hsum : (K - 1) + (K' - 1) + (K - 1) * (K' - 1) = 0 := by
    rw [sub_mul, mul_sub, mul_sub, hKK]; noncomm_ring
  have hff : ((half * (1 + c)) * (half * (1 + c))) • ((K - 1) * (K' - 1))
      = (half * (1 + c)) • ((K - 1) * (K' - 1)) := by
    rw [show (half * (1 + c)) * (half * (1 + c)) = half * half * (1 + 2 * c) + half * half * (c * c) by ring,
      add_smul, ← smul_smul (half * half) (c * c), hP, ← add_smul]
    congr 1
    linear_combination (half * (1 + c)) * h2
  unfold tMat
  generalize half * (1 + c) = f at hff ⊢
  have e : (1 + f • (K - 1)) * (1 + f • (K' - 1))
      = 1 + f • ((K - 1) + (K' - 1)) + (f * f) • ((K - 1) * (K' - 1)) := by
    rw [add_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, smul_add]; abel
  rw [e, hff, add_assoc, ← smul_add, hsum, smul_zero, add_zero]

end GlobalTheory.SplitDblGen
end

