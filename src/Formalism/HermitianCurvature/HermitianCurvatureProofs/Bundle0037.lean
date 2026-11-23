module

public import Formalism.HermitianCurvature.StatementJF
public import Formalism.FormalDegreeBessel.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0034
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0035
public import Formalism.HermitianCurvature.Bundle0007
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0029
public import Formalism.HermitianCurvature.Bundle0006
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0028
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0032
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0031
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0024
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagScalarCommuteTransposedRMatrix
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvOther
public import Formalism.HermitianCurvature.Bundle0005
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0021

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
section
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.BigCellHermitian

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.TwoByOneBlock

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma bigCell_mulVec_jV (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (u : Fin (k + 1) → ℂ) :
    bigCell k r c μ *ᵥ jV k r u = jV k r (μ *ᵥ u) := by
  rw [← emb_mulVec_jV (r := r) μ u]
  ext i
  simp only [mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
  · have hj1 : ¬ j.val < r := by omega
    have e : bigCell k r c μ i j = Formalism.FourierDecayAlt.B2.embWb k r μ i j := by
      simp only [bigCell, Formalism.FourierDecayAlt.B2.embWb, dif_neg hj1, dif_pos hj.2]
      by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
      · rw [dif_pos hi, dif_pos ⟨hi, hj⟩]
      · rw [dif_neg hi, dif_neg (fun h => hi h.1)]
        rw [if_neg]
        rintro ⟨rfl, h2⟩
        exact h2 hj
    rw [e]
  · have h0 : jV k r u j = 0 := by simp only [jV, dif_neg hj]
    rw [h0, mul_zero, mul_zero]

lemma herm_bigCell (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {z z' : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) (hz' : inWb k r z') :
    herm (Hpk k r) (bigCell k r c μ *ᵥ z') z = herm (Hb k) (μ *ᵥ wbPart k r z') (wbPart k r z) := by
  conv_lhs => rw [← jV_wbPart hz', ← jV_wbPart hz]
  rw [bigCell_mulVec_jV, herm_jV]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem gqDom (D : RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ QDom k r D.z D.z') :
    gq D q ∈ Om k r D.z D.z' := by
  obtain ⟨hc, hζ⟩ := hq
  have hsec := D.sec.2 q.2 hζ
  have hmin := big_cell_minors_holds k r D.z D.z' q.1 (D.μsec q.2) D.z_mem D.z'_mem
  refine ⟨big_cell_mem_holds k r q.1 _ hc hsec.1, ?_, ?_⟩
  · intro l hl
    have h := hmin.1 ⟨l.val, by omega⟩
    have hl' : (⟨(⟨l.val, by omega⟩ : Fin (r + 1)).val, by omega⟩ : Fin (r + 2)) = l := Fin.ext rfl
    show Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) l ≠ 0
    rw [← hl', h]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
  · have hz := hmin.2.2 hc
    rw [herm_bigCell _ _ D.z_mem D.z'_mem, hsec.2] at hz
    have hr := hmin.1 (Fin.last r)
    set P := Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) ⟨r, by omega⟩ with hP
    have hP0 : P ≠ 0 := by
      have : P = ∏ a : Fin r with a.val < (Fin.last r).val, q.1 a := hr
      rw [this]; exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
    have hlast : Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) (Fin.last (r + 1)) = q.2 * P := by
      unfold zeta at hz
      rw [← hP] at hz
      have h2 := div_mul_cancel₀ (Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) (Fin.last (r + 1))) hP0
      rw [hz] at h2
      exact h2.symm
    show 0 < Gf k r D.z D.z' (gq D q)
    unfold Gf gq
    rw [hlast, ← hP, Complex.normSq_mul]
    have h1 : 0 < Complex.normSq P := Complex.normSq_pos.2 hP0
    nlinarith

theorem _root_.Formalism.FourierDecayAlt.P.big_cell_domain : GqDom := fun _ _ _ _ _ _ _ _ D _ hq => gqDom D hq

end Formalism.FourierDecayAlt.P.BigCellHermitian
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockTwist
section
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

namespace TwistedTransfer

section Ring

end Ring

section Frame

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

structure WaveHyp (L : R.LevelData A r) (st : Fr.Start A) (f fi : A) (s : ℂ) : Prop where
  f_fi : f * fi = 1
  fi_f : fi * f = 1
  star_f : star f = fi
  fn : ∀ g ∈ Fr.zfns L, Commute f g
  x : ∀ Y, Commute f (st.x Y)
  l : ∀ Y ∈ st.inv, fi * (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y) * f =
    L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y - algebraMap ℂ A s

theorem mem_zfns (L : R.LevelData A r) : L.ζ ∈ Fr.zfns L ∧ L.ζi ∈ Fr.zfns L ∧ L.ζb ∈ Fr.zfns L ∧
    L.ζbi ∈ Fr.zfns L ∧ L.GG ∈ Fr.zfns L ∧ L.GGi ∈ Fr.zfns L := by
  simp [Fr.zfns]

theorem lowering_constant_sub (L : R.LevelData A r) (Y Y' : ℂ) :
    L.l0 Y - L.l0 Y' = algebraMap ℂ A (Y' - Y) * (L.ζb * L.GGi) := by
  simp only [R.LevelData.l0, map_sub, map_add (f := _)]
  noncomm_ring

theorem embed_lowering_constant (L : R.LevelData A r) (Y : ℂ) :
    (io (L.l0 Y) : SlopeTestRemainingChoices S A) = -io L.nab - ((Y + 1 / 2) • (1 : SlopeTestRemainingChoices S A)) * (io L.ζb * io L.GGi) := by
  simp only [R.LevelData.l0, io_sub', io_neg', io_mul', io_algebraMap]

theorem wti_wt (L : R.LevelData A r) : L.GG * L.ζi * L.ζbi * (L.ζ * L.ζb * L.GGi) = 1 := by
  have h1 : L.ζbi * L.ζ = L.ζ * L.ζbi := L.fns_comm _ (by simp) _ (by simp)
  calc L.GG * L.ζi * L.ζbi * (L.ζ * L.ζb * L.GGi) = L.GG * L.ζi * (L.ζbi * L.ζ) * L.ζb * L.GGi := by
        simp only [mul_assoc]
    _ = L.GG * (L.ζi * L.ζ) * (L.ζbi * L.ζb) * L.GGi := by rw [h1]; simp only [mul_assoc]
    _ = 1 := by rw [L.ζi_ζ, L.ζbi_ζb, mul_one, mul_one, L.GG_GGi]

theorem wt_wti (L : R.LevelData A r) : L.ζ * L.ζb * L.GGi * (L.GG * L.ζi * L.ζbi) = 1 := by
  have h2 : L.ζb * L.ζi = L.ζi * L.ζb := L.fns_comm _ (by simp) _ (by simp)
  calc L.ζ * L.ζb * L.GGi * (L.GG * L.ζi * L.ζbi) = L.ζ * L.ζb * (L.GGi * L.GG) * L.ζi * L.ζbi := by
        simp only [mul_assoc]
    _ = L.ζ * (L.ζb * L.ζi) * L.ζbi := by rw [L.GGi_GG, mul_one]; simp only [mul_assoc]
    _ = (L.ζ * L.ζi) * (L.ζb * L.ζbi) := by rw [h2]; simp only [mul_assoc]
    _ = 1 := by rw [L.ζ_ζi, L.ζb_ζbi, mul_one]

theorem di_d (L : R.LevelData A r) (fr : Fr.FrameData S A) (hc : fr.ci * fr.c = 1) : fr.di L * fr.d L = 1 := by
  have h1 : (Fr.wti L : SlopeTestRemainingChoices S A) * Fr.wt L = 1 := by
    rw [Fr.wti, Fr.wt, ← io_mul', wti_wt, io_one']
  have h2 : (Fr.wt L : SlopeTestRemainingChoices S A) * Fr.wti L = 1 := by
    rw [Fr.wti, Fr.wt, ← io_mul', wt_wti, io_one']
  have hc' : Commute (Fr.wti L : SlopeTestRemainingChoices S A) (Fr.wt L) := by
    show _ = _; rw [h1, h2]
  have hp : (Fr.wti L : SlopeTestRemainingChoices S A) ^ fr.N * Fr.wt L ^ fr.N = 1 := by
    rw [← hc'.mul_pow, h1, one_pow]
  unfold Fr.FrameData.di Fr.FrameData.d
  calc fr.ci * Fr.wti L ^ fr.N * (Fr.wt L ^ fr.N * fr.c) = fr.ci * (Fr.wti L ^ fr.N * Fr.wt L ^ fr.N) * fr.c := by
        simp only [mul_assoc]
    _ = 1 := by rw [hp, mul_one, hc]

variable {L : R.LevelData A r} {st : Fr.Start A} {f fi : A} {s : ℂ}

theorem WaveHyp.io_fn (hW : WaveHyp L st f fi s) {g : A} (hg : g ∈ Fr.zfns L) :
    Commute (io f : SlopeTestRemainingChoices S A) (io g) :=
  commute_io_io (hW.fn g hg)

theorem WaveHyp.kap (hW : WaveHyp L st f fi s) : Commute (io f : SlopeTestRemainingChoices S A) (Fr.kapL L) := by
  obtain ⟨-, h1, h2, -, -, h5⟩ := mem_zfns L
  unfold Fr.kapL
  exact commute_io_io (((hW.fn _ h2).mul_right (hW.fn _ h1)).mul_right (hW.fn _ h5))

theorem WaveHyp.tz (hW : WaveHyp L st f fi s) : Commute (io f : SlopeTestRemainingChoices S A) (Fr.tz L) := by
  obtain ⟨-, -, -, h3, -, -⟩ := mem_zfns L
  unfold Fr.tz
  exact commute_io_io ((hW.fn _ h3).smul_right _)

theorem WaveHyp.wt (hW : WaveHyp L st f fi s) : Commute (io f : SlopeTestRemainingChoices S A) (Fr.wt L) := by
  obtain ⟨h0, -, h2, -, -, h5⟩ := mem_zfns L
  unfold Fr.wt
  exact commute_io_io (((hW.fn _ h0).mul_right (hW.fn _ h2)).mul_right (hW.fn _ h5))

theorem WaveHyp.wti (hW : WaveHyp L st f fi s) : Commute (io f : SlopeTestRemainingChoices S A) (Fr.wti L) := by
  obtain ⟨-, h1, -, h3, h4, -⟩ := mem_zfns L
  unfold Fr.wti
  exact commute_io_io (((hW.fn _ h4).mul_right (hW.fn _ h1)).mul_right (hW.fn _ h3))

theorem WaveHyp.lowering_constant_sub (hW : WaveHyp L st f fi s) (Y Y' : ℂ) : Commute f (L.l0 Y - L.l0 Y') := by
  obtain ⟨-, -, h2, -, -, h5⟩ := mem_zfns L
  rw [TwistedTransfer.lowering_constant_sub L Y Y']
  exact (Algebra.commute_algebraMap_right _ f).mul_right ((hW.fn _ h2).mul_right (hW.fn _ h5))

theorem frame_step (hW1 : f * fi = 1) (a : S) (t : ℂ) (D : M2 (SlopeTestRemainingChoices S A)) (Fw UU : SlopeTestRemainingChoices S A) (hD : FreeOf2 a D)
    (hFw : FreeOf a Fw) (hIH : Fw * (io f * UU) = io f * Fw)
    (hE : (D * lift0 (Uinv (A := A) t)).map (cj f fi) = D) :
    ins a D * Fw * (io f * (ins a (lift0 (Uinv (A := A) t)) * UU)) = io f * (ins a D * Fw) := by
  have hcent : ∀ z : SlopeTestRemainingChoices S A, ∀ i j, Commute z ((lift0 (Uinv (A := A) t) : M2 (SlopeTestRemainingChoices S A)) i j) := by
    intro z i j
    rw [lift_unipotent_inverse]
    fin_cases i <;> fin_cases j <;> simp [commute_smul_one]
  have hUf : Commute (io f) (ins a (lift0 (Uinv (A := A) t))) :=
    Formalism.FourierDecayAlt.P.Wd1.ins_comm a _ _ (Formalism.FourierDecayAlt.P.Fr4.free_io a f) (hcent _)
  have hUF : Commute Fw (ins a (lift0 (Uinv (A := A) t))) := Formalism.FourierDecayAlt.P.Wd1.ins_comm a _ _ hFw (hcent _)
  have hins : ins a D * ins a (lift0 (Uinv (A := A) t)) = ins a (D * lift0 (Uinv (A := A) t)) :=
    (Formalism.FourierDecayAlt.P.Wd1.ins_mul a D _ hD).symm
  have hcj : ins a (D * lift0 (Uinv (A := A) t)) * io f = io f * ins a D := by
    have h := cj_ins (f := f) (fi := fi) a (D * lift0 (Uinv (A := A) t))
    rw [hE] at h
    calc ins a (D * lift0 (Uinv (A := A) t)) * io f
        = (io f * io fi) * ins a (D * lift0 (Uinv (A := A) t)) * io f := by rw [io_f_fi hW1, one_mul]
      _ = io f * cj f fi (ins a (D * lift0 (Uinv (A := A) t))) := by simp only [cj, mul_assoc]
      _ = io f * ins a D := by rw [h]
  calc ins a D * Fw * (io f * (ins a (lift0 (Uinv (A := A) t)) * UU))
      = ins a D * (Fw * ((io f * ins a (lift0 (Uinv (A := A) t))) * UU)) := by simp only [mul_assoc]
    _ = ins a D * (Fw * ((ins a (lift0 (Uinv (A := A) t)) * io f) * UU)) := by rw [hUf.eq]
    _ = ins a D * ((Fw * ins a (lift0 (Uinv (A := A) t))) * (io f * UU)) := by simp only [mul_assoc]
    _ = ins a D * ((ins a (lift0 (Uinv (A := A) t)) * Fw) * (io f * UU)) := by rw [hUF.eq]
    _ = ins a D * ins a (lift0 (Uinv (A := A) t)) * (Fw * (io f * UU)) := by simp only [mul_assoc]
    _ = ins a (D * lift0 (Uinv (A := A) t)) * io f * Fw := by rw [hIH, hins]; simp only [mul_assoc]
    _ = io f * (ins a D * Fw) := by rw [hcj, mul_assoc]

theorem block_twist (hW1 : f * fi = 1) (hW2 : fi * f = 1) (t : ℂ) (p q g l : SlopeTestRemainingChoices S A) (hp : Commute (io f) p)
    (hq : Commute (io f) q) (hg : Commute (io f) g) (hl : Tw f fi t l) :
    ((!![p, 0; 0, q] * !![1, 0; g * l, g]) * lift0 (Uinv (A := A) t)).map (cj f fi) =
      !![p, 0; 0, q] * !![1, 0; g * l, g] := by
  rw [lift_unipotent_inverse]
  simp only [Matrix.mul_fin_two, mul_one, mul_zero, zero_mul, add_zero, zero_add]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  · simp [cj_of_comm hW2 hp]
  · simp [cj_zero]
  · simp only [Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.mk_one, Fin.zero_eta]
    unfold Tw at hl
    rw [cj_add, cj_mul hW1, cj_mul hW1, cj_mul hW1, cj_mul hW1, cj_of_comm hW2 hq, cj_of_comm hW2 hg, hl,
      cj_of_comm hW2 (commute_smul_one t _), mul_sub, mul_sub, mul_assoc q g, sub_add_cancel]
  · simp [cj_of_comm hW2 (hq.mul_right hg)]

end Frame

end TwistedTransfer

end Formalism.FourierDecayAlt.P5
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliUnderIntegral
section
open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.CapelliUnderIntegral

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem glev0 {k r : ℕ} (g : Mat k r) : g ∈ Q.Glev k r 0 ↔ g ∈ GV k r := by
  simp only [Q.Glev, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h, -⟩
    exact h
  · intro h
    exact ⟨h, fun a ha => by simp at ha⟩

theorem integrable_map_sum {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} (L : List ι) (φ : ι → α → E) (h : ∀ i ∈ L, Integrable (φ i) μ) :
    Integrable (fun x => (L.map (fun i => φ i x)).sum) μ := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h i (by simp)).add (ih (fun j hj => h j (by simp [hj])))

theorem integral_map_sum {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} (L : List ι) (φ : ι → α → E) (h : ∀ i ∈ L, Integrable (φ i) μ) :
    ∫ x, (L.map (fun i => φ i x)).sum ∂μ = (L.map (fun i => ∫ x, φ i x ∂μ)).sum := by
  induction L with
  | nil => simp
  | cons i L ih =>
    have hi := h i (by simp)
    have hL : ∀ j ∈ L, Integrable (φ j) μ := fun j hj => h j (by simp [hj])
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add hi (integrable_map_sum L φ hL), ih hL]

end Formalism.FourierDecayAlt.P.CapelliUnderIntegral

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivativeRulesA1
section
open Matrix Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma one_le_gN {g : Mat k r} (hg : g ∈ GV k r) : 1 ≤ gN g := (Formalism.FourierDecayAlt.P.norm_of_inverse k r g hg).2

lemma gN_pos {g : Mat k r} (hg : g ∈ GV k r) : 0 < gN g := lt_of_lt_of_le one_pos (one_le_gN hg)

lemma top_ge_nat (m : ℕ) : (((m : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ (((⊤ : ℕ∞)) : WithTop ℕ∞) :=
  WithTop.coe_le_coe.2 le_top

lemma ckOn_top_nat {f : Mat k r → E} (hf : CkOn (⊤ : ℕ∞) (GV k r) f) (m : ℕ) :
    CkOn ((m : ℕ) : ℕ∞) (GV k r) f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hf g₀ hg₀
  exact ⟨U, f', hU, hgU, hc.of_le (top_ge_nat m), hff⟩

lemma top_ne_zero' : (((⊤ : ℕ∞)) : WithTop ℕ∞) ≠ 0 := by simp

lemma top_succ_le : (((⊤ : ℕ∞)) : WithTop ℕ∞) + 1 ≤ (((⊤ : ℕ∞)) : WithTop ℕ∞) := by
  exact_mod_cast (le_top : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ ⊤)

lemma ckOn_op_top {f : Mat k r → E} {X : Mat k r} (b : Bool) (hf : CkOn (⊤ : ℕ∞) (GV k r) f)
    (hX : inLie k r X) : CkOn (⊤ : ℕ∞) (GV k r) (op b X f) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hf g₀ hg₀
  refine ⟨U, op' b X f', hU, hgU, ?_, ?_⟩
  · exact (hc.fderiv_of_isOpen hU top_succ_le).clm_apply (vf b X).contDiff.contDiffOn
  · intro g hg hgG
    have hd : DifferentiableAt ℝ f' g :=
      (hc.differentiableOn top_ne_zero').differentiableAt (hU.mem_nhds hg)
    exact (hasDerivAt_ext b hU hg hgG hd hff hX).deriv

lemma chart_rho {g0 x : Mat k r} (hg0 : g0 ∈ GV k r) (hx : x ∈ Sr g0) (hxG : x ∈ GV k r) :
    chart g0 (rho g0 x) = x := by
  have hgu : IsUnit g0.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0
  have hh : x * g0⁻¹ ∈ GV k r := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hxG (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hg0)
  obtain ⟨hl, -, hk⟩ := iot_facts hh hx
  show kap (prj (Mv (co (iot (x * g0⁻¹))))) * g0 = x
  rw [Mv_co, prj_of_lie hl, hk, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hgu, Matrix.mul_one]

lemma rho_self {g0 : Mat k r} (hg0 : g0 ∈ GV k r) : rho g0 g0 = 0 := by
  have hgu : IsUnit g0.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0
  have hg1 : g0 * g0⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  funext i
  simp only [Ux10.rho, hg1, iot, sub_self, Matrix.zero_mul]
  exact co_zero i

lemma self_mem_Sr {g0 : Mat k r} (hg0 : g0 ∈ GV k r) : g0 ∈ Sr g0 := by
  have hgu : IsUnit g0.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0
  have hg1 : g0 * g0⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  have h2 : (1 + 1 : Mat k r) = (2 : ℂ) • (1 : Mat k r) := by rw [two_smul]
  show IsUnit (g0 * g0⁻¹ + 1).det
  rw [hg1, h2, Matrix.det_smul, Matrix.det_one, mul_one]
  exact (isUnit_iff_ne_zero.2 two_ne_zero).pow _

lemma chart_comp_cd {F : Mat k r → E} {g0 : Mat k r} (hg0 : g0 ∈ GV k r) (m : ℕ)
    (hF : CkOn ((m : ℕ) : ℕ∞) (GV k r) F) :
    ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞) (fun Y => F (chart g0 Y)) (Dom k r) := by
  intro Y hY
  apply ContDiffAt.contDiffWithinAt
  obtain ⟨U, f', hU, hcU, hcd, hff⟩ := hF _ (chart_mem hg0 hY)
  have hchc : ContinuousAt (chart g0) Y := (chart_diff g0 hY).continuousAt
  have h1 : ContDiffAt ℝ ((m : ℕ) : WithTop ℕ∞) (fun Y' => f' (chart g0 Y')) Y :=
    (hcd.contDiffAt (hU.mem_nhds hcU)).comp Y
      (((chart_cd g0).contDiffAt (dom_open.mem_nhds hY)).of_le (top_ge_nat m))
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hchc.preimage_mem_nhds (hU.mem_nhds hcU), dom_open.mem_nhds hY] with Y' h1 h2
  exact hff _ h1 (chart_mem hg0 h2)

theorem ckOn_top_of_all {F : Mat k r → E} (hF : ∀ m : ℕ, CkOn ((m : ℕ) : ℕ∞) (GV k r) F) :
    CkOn (⊤ : ℕ∞) (GV k r) F := by
  intro g0 hg0
  have hAL : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Y => F (chart g0 Y)) (Dom k r) :=
    contDiffOn_infty.2 fun m => chart_comp_cd hg0 m (hF m)
  set U := Sr g0 ∩ rho g0 ⁻¹' Dom k r with hUdef
  have hUo : IsOpen U := (rho_cd g0).continuousOn.isOpen_inter_preimage (sr_open g0) dom_open
  have hg0U : g0 ∈ U := ⟨self_mem_Sr hg0, by show rho g0 g0 ∈ Dom k r; rw [rho_self hg0]; exact zero_mem_dom⟩
  refine ⟨U, fun x => F (chart g0 (rho g0 x)), hUo, hg0U, ?_, ?_⟩
  · exact hAL.comp ((rho_cd g0).mono Set.inter_subset_left) (fun x hx => hx.2)
  · intro x hx hxG
    show F x = F (chart g0 (rho g0 x))
    rw [chart_rho hg0 hx.1 hxG]

end Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvSelf
section
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

section PairNeg

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem pr_neg_fst (a : Pr V) : (-a).1 = -a.1 := rfl
theorem pr_neg_snd (a : Pr V) : (-a).2.unop = -a.2.unop := rfl

end PairNeg

end Formalism.FourierDecayAlt.P5
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HerClassesOfParts
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

section Struct

variable {V : Type} [AddCommGroup V] [Module ℂ V] {S : Type} [Fintype S] [DecidableEq S]

theorem inK_act_span {G G' : Set V} (M : SlopeTestRemainingChoices S (Pr V)) (hM : ∀ a b, ∀ Φ ∈ G, (M a b).1 Φ ∈ Submodule.span ℂ G')
    (x : Ix S → V) (hx : ∀ a, x a ∈ Submodule.span ℂ G) : ∀ a, ∑ b, (M a b).1 (x b) ∈ Submodule.span ℂ G' := by
  intro a
  refine Submodule.sum_mem _ (fun b _ => ?_)
  have hle : Submodule.span ℂ G ≤ (Submodule.span ℂ G').comap (M a b).1 :=
    Submodule.span_le.mpr (fun Φ hΦ => hM a b Φ hΦ)
  exact hle (hx b)

end Struct

section Classes

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable {S : Type} [Fintype S] [DecidableEq S]
variable {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r}
  {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ} {D : B.RealPlaceData P.k P.r Wp Wq}

end Classes

end Formalism.FourierDecayAlt.P5
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.XiYZhatIdentity
section
theorem Formalism.FourierDecayAlt.P.xi_Y_zhat_identity : Formalism.FourierDecayAlt.C3.XiYZhat :=
  covector_entries
end

