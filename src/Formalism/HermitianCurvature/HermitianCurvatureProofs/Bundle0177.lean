module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0170
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0124
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0167
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0052
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferSquareIntegrableHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0051
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0053
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0114

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASASecRad
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSTr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem radial_section_holds : SARadSec := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl e he U
  classical
  let g : (Fin P.r → ℂ) × ℂ → (Wq →L[ℂ] Wp) := fun x =>
    (((Real.sqrt (MA.wq P.k x P.TT))⁻¹ : ℝ) : ℂ) • ∑ ρ, MA.ext (U ρ : MA.Qp P.r P.TT → ℂ) x • e ρ x.2
  let φ := (NF.QR P.k P.r Bs.z Bs.z').indicator g
  have hQR : NF.QR P.k P.r Bs.z Bs.z' = MA.Qset P.r P.TT := Set.ext (qr_iff P Bs hpl)
  have hg : ContDiffOn ℝ ∞ g (MA.Qset P.r P.TT) := by
    have hw : ContDiffOn ℝ ∞ (fun x : MA.E P.r => (((Real.sqrt (MA.wq P.k x P.TT))⁻¹ : ℝ) : ℂ))
        (MA.Qset P.r P.TT) := by
      refine Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_ofReal ?_
      refine ContDiffOn.inv ?_ fun x hx => (Real.sqrt_pos.2 (Formalism.FourierDecayAlt.P.CutMP.En.wq_pos hx)).ne'
      exact (Formalism.FourierDecayAlt.P.CutMP.En.wq_contDiff P.k P.r P.TT).contDiffOn.sqrt fun x hx =>
        (Formalism.FourierDecayAlt.P.CutMP.En.wq_pos hx).ne'
    refine hw.smul (ContDiffOn.sum fun ρ _ => ?_)
    have hF : ContDiffOn ℝ ∞ (MA.ext (U ρ : MA.Qp P.r P.TT → ℂ)) (MA.Qset P.r P.TT) := (U ρ).2
    have he' : ContDiffOn ℝ ∞ (fun x : MA.E P.r => e ρ x.2) (MA.Qset P.r P.TT) :=
      (he.1 ρ).comp contDiff_snd.contDiffOn fun x hx => hx.2
    exact hF.smul he'
  have hφ : φ ∈ NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    refine ⟨?_, fun x hx => ?_, fun x hx => ?_⟩
    · rw [hQR]
      exact hg.congr fun x hx => by simp only [φ, hQR, Set.indicator_of_mem hx]
    · simp only [φ, Set.indicator_of_mem hx, g]
      have hx' : P.TT < Complex.normSq x.2 := ((qr_iff P Bs hpl x).1 hx).2
      have h1 := fib_sum_smul P Bs x.2 (fun ρ => MA.ext (U ρ : MA.Qp P.r P.TT → ℂ) x) (fun ρ => e ρ x.2) fun ρ => (he.2 x.2 hx').1 ρ
      by_cases hne : Nonempty (M.Ty P)
      · obtain ⟨ρ0⟩ := hne
        intro p hp
        have h3 := fib_sum_smul P Bs x.2 (fun ρ => if ρ = ρ0 then (((Real.sqrt (MA.wq P.k x P.TT))⁻¹ : ℝ) : ℂ) else 0)
          (fun _ => ∑ ρ, MA.ext (U ρ : MA.Qp P.r P.TT → ℂ) x • e ρ x.2) (fun _ => h1) p hp
        simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h3
        exact h3
      · have : ∑ ρ, MA.ext (U ρ : MA.Qp P.r P.TT → ℂ) x • e ρ x.2 = 0 := by
          rw [Finset.univ_eq_empty_iff.2 (not_nonempty_iff.1 hne)]; simp
        rw [this, smul_zero]
        intro p hp
        ext v
        simp
    · simp [φ, Set.indicator_of_notMem hx]
  obtain ⟨Φ, hΦ, hrad⟩ := Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π'
    (radBase P Bs hpl) φ hφ
  refine ⟨Φ, hΦ, fun q => ?_⟩
  have hq : q.1 ∈ NF.QR P.k P.r Bs.z Bs.z' := (qr_iff P Bs hpl q.1).2 q.2
  have h := congrFun hrad q.1
  simp only [NF.radR, Set.indicator_of_mem hq, φ] at h
  rw [h]
  simp only [g]
  congr 1
  refine Finset.sum_congr rfl fun ρ _ => ?_
  congr 1
  simp [MA.ext, q.2]

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDQQ
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

def JDHatOpQQ : Prop :=
  ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGauge S T v e → IsGaugeQQ S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      ∀ X ∈ MA.hatSet (D.parOf S v) L,
        ∃ ts : List (MA.A (D.parOf S v) (MA.DQ (D.parOf S v)) × B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))),
          (∀ t ∈ ts, t.1 ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L) ∧ B.SmoothCoef (B.GPos (T v).base) t.2 ∧
            B.Commutes (T v).base (B.GPos (T v).base) t.2 ∧
            GlobCoef t.2 (Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) ∧ (B.opOrder t.2 : ℝ) ≤ Cc * nDim S.G.k S.G.r) ∧
          ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
            MA.actA (D.parOf S v) X (trJ S T v e J) =
              (ts.map fun t => MA.actA (D.parOf S v) t.1 (trJ S T v e (B.opApply t.2 J))).sum

def JDecayTrQQd : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGauge S T v e → IsGaugeQQ S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      B.JF (T v).base (f v) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
      MA.JDecay (D.parOf S v) L (trJ S T v e (B.JF (T v).base (f v))) (2 * S.Ntop + 2)

theorem jDecayTrQQd_of_leaves (h1 : JDHatBdd) (h2 : JDHatOpQQ) (h3 : JDJComm) (h4 : JDCCLower) (h5 : TransferSquareIntegrable)
    (h6 : BoundedOperatorsSquareIntegrable) : JDecayTrQQd := by
  obtain ⟨C2, hC2, H2⟩ := h2
  obtain ⟨C3, H3⟩ := h3
  obtain ⟨C5, H5⟩ := h5
  unfold JDecayTrQQd
  refine ⟨8 * C2 + |C3| + |C5|, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL hJf
  have hmono : ∀ c, c ≤ 8 * C2 + |C3| + |C5| → BuiltOW c S T f χ ν' m₀ top A₀ := fun c hc =>
    ⟨isBuiltPlace_mono hc hB.1, hB.2⟩
  have hB2 := hmono C2 (by linarith [abs_nonneg C3, abs_nonneg C5])
  have hB3 := hmono C3 (by linarith [le_abs_self C3, abs_nonneg C5])
  have hB5 := hmono C5 (by linarith [le_abs_self C5, abs_nonneg C3])
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  have hTTpos : 0 < (D.parOf S v).TT := by rw [hTT]; exact mul_pos (T v).base.T_pos (T v).base.T'_pos
  have hInCC : ∀ m : ℕ, B.InCC A₀ m (f v) := (hB.1.2.2.2.1.2 v).2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, hCk, -, hA, -⟩ := hB.1

  have hR : (0 : ℝ) ≤ (S.G.r : ℝ) := Nat.cast_nonneg _
  have hnE : nDim S.G.k S.G.r = 2 * (S.G.r : ℝ) + S.G.k + 1 := by unfold nDim; push_cast; ring
  have hn : (1 : ℝ) ≤ nDim S.G.k S.G.r := by
    rw [hnE]; have := Nat.cast_nonneg (α := ℝ) S.G.k; linarith
  have hA' : (8 * C2 + |C3| + |C5|) * ((S.G.r : ℝ) + 1) ^ 4 *
      ((S.Ntop : ℝ) * nDim S.G.k S.G.r ^ 2 + nDim S.G.k S.G.r ^ 3) ≤ A₀ := by rw [hnE]; exact hA
  obtain ⟨hK3', hK5'⟩ := jd_arith C2 C3 C5 _ _ _ A₀ hC2 hR hn (Nat.cast_nonneg _) hA'
  have hdm0 : 0 ≤ C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r := by
    have := le_trans zero_le_one hn; positivity
  have hK3 : ∀ i : ℕ, i ≤ 2 * S.Ntop + 1 → ∀ o : ℝ, o ≤ C2 * nDim S.G.k S.G.r →
      C3 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * o +
      C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ≤ A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) := by
    intro i hi o ho
    refine hK3' _ _ ?_ ho
    have : ((i : ℕ) : ℝ) ≤ ((2 * S.Ntop + 1 : ℕ) : ℝ) := by exact_mod_cast hi
    push_cast at this; linarith
  have hK5 : ∀ i : ℕ, i ≤ 2 * S.Ntop + 2 → C5 * ((S.G.r : ℝ) + 1) ^ 2 * nDim S.G.k S.G.r ≤
      A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) := by
    intro i hi
    refine hK5' _ ?_
    have : ((i : ℕ) : ℝ) ≤ ((2 * S.Ntop + 2 : ℕ) : ℝ) := by exact_mod_cast hi
    push_cast at this; linarith

  let Good : ℕ → (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → Prop := fun i F =>
    B.CkOn ⊤ (B.GV S.G.k S.G.r) F ∧ (∀ m : ℕ, B.InCC (A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r)) m F) ∧
      B.JF (T v).base F ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)
  let tr : (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → M.Ty (D.parOf S v) →
      MA.SmQ (D.parOf S v).r (D.parOf S v).TT := fun F => trJ S T v e (B.JF (T v).base F)
  have hStep : ∀ i, i < 2 * S.Ntop + 2 → ∀ F, Good i F → ∀ X ∈ MA.hatSet (D.parOf S v) L,
      ∃ ts : List (MA.A (D.parOf S v) (MA.DQ (D.parOf S v)) × (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))),
        (∀ t ∈ ts, t.1 ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L) ∧ Good (i + 1) t.2) ∧
        MA.actA (D.parOf S v) X (tr F) = (ts.map fun t => MA.actA (D.parOf S v) t.1 (tr t.2)).sum := by
    intro i hi F hF X hX
    obtain ⟨hCkF, hCCF, hFF⟩ := hF
    obtain ⟨ts, hts, hid⟩ := H2 E Wp Wq S T f χ ν' m₀ top A₀ hB2 v e L hFr hGa hQQ hL X hX
    have hthr : ∀ t ∈ ts, C3 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder t.2 : ℝ) +
        C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ≤ A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) :=
      fun t ht => hK3 i (by omega) _ (hts t ht).2.2.2.2
    have l3 : ∀ t ∈ ts, _ := fun t ht =>
      H3 E Wp Wq S T f χ ν' m₀ top A₀ hB3 v t.2 (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) (A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r)) hdm0
        (hts t ht).2.1 (hts t ht).2.2.1 (hts t ht).2.2.2.1 (hthr t ht) F hCkF hCCF hFF
    refine ⟨ts.map fun t => (t.1, B.opApply t.2 F), ?_, ?_⟩
    · intro t ht
      obtain ⟨t0, ht0, rfl⟩ := List.mem_map.1 ht
      have l4 := h4 _ _ _ _ t0.2 (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) (A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r)) hdm0 (hts t0 ht0).2.2.2.1 F hCkF hCCF
      refine ⟨(hts t0 ht0).1, l4.1, fun m => ?_, (l3 t0 ht0).1⟩
      have e : A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) - (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) = A₀ - ((i + 1 : ℕ) : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) := by push_cast; ring
      rw [← e]; exact l4.2 m
    · rw [hid (B.JF (T v).base F) hFF, List.map_map]
      congr 1
      refine List.map_congr_left fun t ht => ?_
      simp only [Function.comp]
      congr 1
      exact trJ_congr S T v e _ _ (l3 t ht).2
  intro w hw hwh π
  have hG0 : Good 0 (f v) := ⟨hCk v, fun m => by simpa using hInCC m, hJf⟩
  have hmem := jd_word_span L Good tr (2 * S.Ntop + 2) (h1 _ L hTTpos.le hL) hStep w hw hwh (f v) hG0
  have hgen : ∀ u ∈ {u | ∃ b ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L), ∃ F', Good w.length F' ∧
      u = MA.actA (D.parOf S v) b (tr F')}, componentwiseL2 (D.parOf S v) u := by
    rintro u ⟨b, hb, F', ⟨hCk', hCC', hFF'⟩, rfl⟩
    have l5 := H5 E Wp Wq S T f χ ν' m₀ top A₀ hB5 v e hFr (A₀ - (w.length : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r)) (hK5 _ hw) F' hCk' hCC' hFF'
    exact (componentwiseL2_iff_integrable _ _).2 (h6 _ L hTTpos hL b hb _ l5)
  exact (componentwiseL2_iff_integrable _ _).1 (componentwiseL2_of_span _ _ hgen _ hmem) π

theorem jDecayTrQQd_of_open (h2 : JDHatOpQQ) : JDecayTrQQd :=
  jDecayTrQQd_of_leaves hat_bounded_decay_holds h2 transfer_commutation_holds class_lower_decay_holds transfer_square_integrable_holds bounded_operators_square_integrable

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJfSSymExp
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

lemma expS_summable {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Summable (fun m : ℕ => ((m.factorial : ℂ))⁻¹ • X ^ m) := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  exact NormedSpace.expSeries_summable' X

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def mvL {n : ℕ} (y : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] (Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M *ᵥ y
      map_add' := fun M N => Matrix.add_mulVec M N y
      map_smul' := fun c M => Matrix.smul_mulVec c M y }

lemma mvL_apply {n : ℕ} (y : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) : mvL y M = M *ᵥ y := rfl

lemma exp_mulVec_sq {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) (h : X *ᵥ (X *ᵥ y) = 0) :
    NormedSpace.exp X *ᵥ y = y + X *ᵥ y := by
  have hs := expS_summable X
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  show (∑' m : ℕ, ((m.factorial : ℂ))⁻¹ • X ^ m) *ᵥ y = y + X *ᵥ y
  rw [← mvL_apply y, ContinuousLinearMap.map_tsum (mvL y) hs]
  rw [tsum_eq_sum (s := Finset.range 2) ?_]
  · simp [Finset.sum_range_succ, mvL_apply, Matrix.smul_mulVec]
  · intro m hm
    simp only [Finset.mem_range, not_lt] at hm
    rw [mvL_apply, Matrix.smul_mulVec]
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
    rw [pow_add, ← Matrix.mulVec_mulVec, pow_two, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero, smul_zero]

lemma exp_smul_mulVec_sq {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) (h : X *ᵥ (X *ᵥ y) = 0)
    (c : ℂ) : NormedSpace.exp (c • X) *ᵥ y = y + c • (X *ᵥ y) := by
  have h' : (c • X) *ᵥ ((c • X) *ᵥ y) = 0 := by
    rw [Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul, h, smul_zero, smul_zero]
  rw [exp_mulVec_sq (c • X) y h', Matrix.smul_mulVec]

lemma exp_smul_mulVec_fix {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) (h : X *ᵥ y = 0)
    (c : ℂ) : NormedSpace.exp (c • X) *ᵥ y = y := by
  have h2 : X *ᵥ (X *ᵥ y) = 0 := by rw [h, Matrix.mulVec_zero]
  rw [exp_smul_mulVec_sq X y h2 c, h, smul_zero, add_zero]

variable {k r : ℕ}

lemma hpk_star (i j : Fin (2 * r + k + 1)) : star (Hpk k r i j) = Hpk k r i j := by
  unfold Hpk
  split_ifs <;> simp

lemma hpk_symm (i j : Fin (2 * r + k + 1)) : Hpk k r i j = Hpk k r j i := by
  by_cases hij : i = j
  · subst hij
    rfl
  · have hji : ¬ j = i := fun h => hij h.symm
    unfold Hpk
    simp only [hij, hji, and_false, if_false]
    split_ifs <;> first | rfl | (exfalso; omega)

lemma herm_conj (y w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) y w = star (herm (Hpk k r) w y) := by
  simp only [herm, dotProduct, mulVec, star_sum, star_mul', star_star, Pi.star_apply, hpk_star,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hpk_symm j i]
  ring

lemma vmv_mulVec {n : ℕ} (u w y : Fin n → ℂ) : vecMulVec u w *ᵥ y = (w ⬝ᵥ y) • u := by
  ext i
  simp only [vecMulVec, mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma star_hpk_dot (v y : Fin (2 * r + k + 1) → ℂ) : star (Hpk k r *ᵥ v) ⬝ᵥ y = herm (Hpk k r) y v := by
  simp only [herm, dotProduct, mulVec, star_sum, star_mul', Pi.star_apply, hpk_star, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hpk_symm j i]
  ring

theorem xuv_mulVec (u v y : Fin (2 * r + k + 1) → ℂ) :
    Xuv k r u v *ᵥ y = herm (Hpk k r) y v • u - herm (Hpk k r) y u • v := by
  unfold Xuv
  rw [Matrix.sub_mulVec, vmv_mulVec, vmv_mulVec, star_hpk_dot, star_hpk_dot]

theorem xuv_inLie (u v : Fin (2 * r + k + 1) → ℂ) : B.inLie k r (Xuv k r u v) := by
  have hH : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1
  have e1 : star (Hpk k r *ᵥ u) = star u ᵥ* Hpk k r := by rw [Matrix.star_mulVec, hH]
  have e2 : star (Hpk k r *ᵥ v) = star v ᵥ* Hpk k r := by rw [Matrix.star_mulVec, hH]
  unfold B.inLie Xuv
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_vecMulVec, Matrix.conjTranspose_vecMulVec,
    star_star, star_star, Matrix.sub_mul, Matrix.mul_sub, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul,
    Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, e1, e2]
  abel

lemma mat_eq_mulVec_bvec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : M i j = (M *ᵥ bvec j) i := by
  simp [bvec, Matrix.mulVec_single]

lemma herm_bvec_left (p : Fin (2 * r + k + 1)) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (bvec p) w = ∑ i, star (w i) * Hpk k r i p := by
  simp [herm, bvec, dotProduct, Matrix.mulVec_single]

lemma herm_bvec_bvec (p q : Fin (2 * r + k + 1)) : herm (Hpk k r) (bvec p) (bvec q) = Hpk k r q p := by
  rw [herm_bvec_left]
  simp [bvec, Pi.single_apply]

lemma hpk_col_eI (c : Fin r) (i : Fin (2 * r + k + 1)) :
    Hpk k r i (eI k r c) = if i = esI k r c then 1 else 0 := by
  have hc := c.isLt
  have hi := i.isLt
  unfold Hpk
  simp only [eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma hpk_col_esI (c : Fin r) (i : Fin (2 * r + k + 1)) :
    Hpk k r i (esI k r c) = if i = eI k r c then 1 else 0 := by
  have hc := c.isLt
  have hi := i.isLt
  unfold Hpk
  simp only [eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma herm_eI_left (c : Fin r) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (bvec (eI k r c)) w = star (w (esI k r c)) := by
  rw [herm_bvec_left]
  simp [hpk_col_eI]

lemma herm_esI_left (c : Fin r) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (bvec (esI k r c)) w = star (w (eI k r c)) := by
  rw [herm_bvec_left]
  simp [hpk_col_esI]

lemma hpk_eI_row_block (a : Fin r) (j : Fin (2 * r + k + 1)) (hj : r ≤ j.val) (hj' : j.val ≤ r + k) :
    Hpk k r (eI k r a) j = 0 := by
  have ha := a.isLt
  unfold Hpk
  simp only [eI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma hpk_eI_eI (a c : Fin r) : Hpk k r (eI k r a) (eI k r c) = 0 := by
  have ha := a.isLt
  have hc := c.isLt
  unfold Hpk
  simp only [eI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma one_mem_UWset (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ UWset k r z := by
  refine ⟨?_, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩
  show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r
  simp

theorem xuv_lieN (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) (v : Fin (2 * r + k + 1) → ℂ)
    (hv : ∀ b : Fin r, b.val ≤ a.val → v (esI k r b) = 0) :
    Xuv k r (bvec (eI k r a)) v ∈ lieOf (Sset k r z) := by
  intro t
  set X := Xuv k r (bvec (eI k r a)) v with hX
  have hXa : X *ᵥ bvec (eI k r a) = 0 := by
    rw [hX, xuv_mulVec, herm_eI_left, hv a le_rfl, herm_bvec_bvec, hpk_eI_eI]
    simp
  have hXc : ∀ c : Fin r, X *ᵥ bvec (eI k r c) = star (v (esI k r c)) • bvec (eI k r a) := by
    intro c
    rw [hX, xuv_mulVec, herm_eI_left, herm_bvec_bvec, hpk_eI_eI]
    simp
  have hXj : ∀ j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k →
      X *ᵥ bvec j = herm (Hpk k r) (bvec j) v • bvec (eI k r a) := by
    intro j hj hj'
    rw [hX, xuv_mulVec, herm_bvec_bvec, hpk_eI_row_block a j hj hj']
    simp
  refine ⟨1, one_mem_UWset z, NormedSpace.exp ((t : ℂ) • X), ⟨Formalism.FourierDecayAlt.P.B5.exp_mem (xuv_inLie _ _) t, ?_, ?_⟩,
    (Matrix.one_mul _).symm⟩
  · intro c i hci
    have e := exp_smul_mulVec_sq X (bvec (eI k r c)) (by rw [hXc, Matrix.mulVec_smul, hXa, smul_zero]) (t : ℂ)
    rw [show NormedSpace.exp ((t : ℂ) • X) i (eI k r c) = (NormedSpace.exp ((t : ℂ) • X) *ᵥ bvec (eI k r c)) i
      from mat_eq_mulVec_bvec _ _ _, e, hXc]
    have hz : star (v (esI k r c)) * bvec (eI k r a) i = 0 := by
      by_cases hca : c.val ≤ a.val
      · rw [hv c hca]; simp
      · have : i ≠ eI k r a := by
          intro h; rw [h] at hci; simp only [eI] at hci; omega
        simp [bvec, Pi.single_apply, this]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hz, mul_zero, add_zero]
    simp [bvec, Pi.single_apply]
  · intro i j hj hj' hi
    have e := exp_smul_mulVec_sq X (bvec j) (by rw [hXj j hj hj', Matrix.mulVec_smul, hXa, smul_zero]) (t : ℂ)
    rw [show NormedSpace.exp ((t : ℂ) • X) i j = (NormedSpace.exp ((t : ℂ) • X) *ᵥ bvec j) i
      from mat_eq_mulVec_bvec _ _ _, e, hXj j hj hj']
    have : i ≠ eI k r a := by
      intro h; rw [h] at hi; simp only [eI] at hi; omega
    simp [bvec, Pi.single_apply, this]

theorem xuv_lieW (z u v : Fin (2 * r + k + 1) → ℂ) (hu : inWb k r u) (hv : inWb k r v)
    (huz : herm (Hpk k r) u z = 0) (hvz : herm (Hpk k r) v z = 0) :
    Xuv k r u v ∈ lieOf (UWset k r z) := by
  intro t
  set X := Xuv k r u v with hX
  have hes : ∀ (w : Fin (2 * r + k + 1) → ℂ), inWb k r w → ∀ c : Fin r, w (esI k r c) = 0 := by
    intro w hw c; exact hw _ (Or.inr (by simp only [esI]; omega))
  have hei : ∀ (w : Fin (2 * r + k + 1) → ℂ), inWb k r w → ∀ c : Fin r, w (eI k r c) = 0 := by
    intro w hw c; exact hw _ (Or.inl (by simp only [eI]; omega))
  refine ⟨Formalism.FourierDecayAlt.P.B5.exp_mem (xuv_inLie _ _) t, fun c => ⟨?_, ?_⟩, ?_⟩
  · refine exp_smul_mulVec_fix X _ ?_ _
    rw [hX, xuv_mulVec, herm_eI_left, herm_eI_left, hes v hv, hes u hu]; simp
  · refine exp_smul_mulVec_fix X _ ?_ _
    rw [hX, xuv_mulVec, herm_esI_left, herm_esI_left, hei v hv, hei u hu]; simp
  · refine exp_smul_mulVec_fix X _ ?_ _
    rw [hX, xuv_mulVec, herm_conj z v, herm_conj z u, hvz, huz]; simp

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
end

