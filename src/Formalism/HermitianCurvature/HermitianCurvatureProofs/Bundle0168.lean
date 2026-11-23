module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0129
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0160
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0046
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0045
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0093
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0155
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InsertUnitMatrixZeroApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0163
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVnice

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDGaugeQQAsm
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

def GaugeExistsQQ : Prop :=
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
    ∀ v, ∃ e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
      IsFrame S T v e ∧ IsGauge S T v e ∧ IsGaugeQQ S T v e

def JDecayTrQQ : Prop :=
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

def JAdjTrQQ : Prop :=
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
      MA.JAdj (D.parOf S v) L (trJ S T v e (B.JF (T v).base (f v))) (2 * S.Ntop + 2)

theorem gaugeExistsQQ_of_gCore (hK : Gauge.GCore) : GaugeExistsQQ := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v
  exact jdg_exists_of_gCore hK 0 E Wp Wq S T f χ ν' m₀ top A₀ hB v

theorem modelPlaceBuilt3_of_leavesQQ (hMF : MA.ModelFrameAn) (h1 : LamCfgInterlaces) (h2 : AdmInCut)
    (h3 : GaugeExistsQQ) (h4 : RegFF3) (h5 : CVPresFF) (h6 : BesselEigen) (h7 : EnergyTr) (h8 : CutTr)
    (h9 : EnergyReal) (h10 : JDecayTrQQ) (h11 : JAdjTrQQ) : ModelPlaceBuilt3 := by
  obtain ⟨K3, g3⟩ := h3
  obtain ⟨K4, g4⟩ := h4
  obtain ⟨K5, g5⟩ := h5
  obtain ⟨K6, g6⟩ := h6
  obtain ⟨K7, g7⟩ := h7
  obtain ⟨K8, g8⟩ := h8
  obtain ⟨K9, g9⟩ := h9
  obtain ⟨K10, g10⟩ := h10
  obtain ⟨LastRowCutoff, g11⟩ := h11
  refine ⟨max 1 (max K3 (max K4 (max K5 (max K6 (max K7 (max K8 (max K9 (max K10 LastRowCutoff)))))))), ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB hJ hOk hW hW' c hc v
  have hOW : ∀ C', C' ≤ max 1 (max K3 (max K4 (max K5 (max K6 (max K7 (max K8 (max K9 (max K10 LastRowCutoff)))))))) →
      BuiltOW C' S T f χ ν' m₀ top A₀ := fun C' h => ⟨isBuiltPlace_mono h hB, hOk, hW, hW'⟩
  obtain ⟨_, _, _, hIB, hl1, hlk, hGr, hLC, _, _, hk2, _, hOn⟩ := hB
  obtain ⟨e, hF, hG, hQQ⟩ := g3 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K3 (by simp)) v
  have hR := g4 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K4 (by simp)) hJ v
  have hP := g5 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K5 (by simp)) v
  have hE := g6 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K6 (by simp)) v
  have hPOK : (D.parOf S v).OK := (hIB.2 v).2.2.2.1.1
  obtain ⟨L, hL, -⟩ := hMF (D.parOf S v) hPOK (S.l + 1) (by omega) (show S.l + 1 ≤ S.G.k by omega)
  have hI := h1 E Wp Wq S hk2 hOk hW hW' v
  have hlt : S.cutLo v < S.cutHi v := by
    have hv := hLC v
    have hN : (0 : ℝ) < S.Ntop := by unfold C.HidaSetting.Ntop C.Kst; positivity
    have hX : 0 < (S.G.k : ℝ) * S.Ntop * ((S.G.r : ℝ) + 1) ^ 2 + (S.Ntop : ℝ) ^ 2 * ((S.G.r : ℝ) + 1) ^ 2 +
        (S.Ntop : ℝ) ^ 3 := by positivity
    have h1le : (1 : ℝ) ≤ max 1 (max K3 (max K4 (max K5 (max K6 (max K7 (max K8 (max K9 (max K10 LastRowCutoff)))))))) :=
      le_max_left _ _
    nlinarith
  refine ⟨L, trJ S T v e (B.JF (T v).base (f v)), lamCfg S v, 1, 1, hc, one_pos, one_pos,
    ⟨hPOK, by omega, show S.l + 1 ≤ S.G.k by omega, hL, hI.1, hI.2, hlt, hOn v⟩,
    g10 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K10 (by simp)) v e L hF hG hQQ hL hR.1,
    g11 E Wp Wq S T f χ ν' m₀ top A₀ (hOW LastRowCutoff (by simp)) v e L hF hG hQQ hL hR.1, ?_, ?_, ?_⟩
  ·
    intro Y
    rw [← hG _ hR.1 Y, trJ_congr S T v e _ (((S.P v Y : ℝ) : ℂ) • B.JF (T v).base (f v)) (hE Y), trJ_smul]
    funext π
    rw [Pi.smul_apply, ← prod_lamCfg S v Y]
    push_cast
    rfl
  ·
    intro ε hε a ha
    have key : C7.principalHermitianLattice (T v).base (M.sgn (D.parOf S v) (S.l + 1)) a (D.cutF (T v).base χ (f v) ε) =
        MA.ipA (D.parOf S v)
          (MA.actA (D.parOf S v) ((a.reverse.map fun x => Wd.C0 (MA.startM (D.parOf S v) (MA.DQ (D.parOf S v))
            (S.l + 1)).QQ (MA.sites (D.parOf S v) (MA.DQ (D.parOf S v))) (x.2 : ℂ)).prod)
            (MA.chiJ (D.parOf S v) (trJ S T v e (B.JF (T v).base (f v))) c ε))
          (MA.chiJ (D.parOf S v) (trJ S T v e (B.JF (T v).base (f v))) c ε) := by
      rw [g7 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K7 (by simp)) v e hF hP ε hε (hR.2 ε hε) a ha,
        (trJ_foldr S T v e hG hP a.reverse _ (hR.2 ε hε)).2,
        g8 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K8 (by simp)) v e hF hR.1 c hc ε hε]
    have hre := g9 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K9 (by simp)) v ε hε a ha
    rw [key] at hre
    rw [key]
    clear g3 g4 g5 g6 g7 g8 g9 g10 g11 hOW key hE hP hR hG hF hI hQQ
    unfold MA.cutoffEnergyForm
    simp only [one_mul]
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simp only [Complex.ofReal_im]
      exact hre
  ·
    intro Lb a ha
    exact level_system_admissible_size S v a ha (h2 E Wp Wq S hGr v a ha) (S.l + 1) L _ c Lb

theorem modelPlaceBuilt3_of_openQQ (h3 : GaugeExistsQQ) (h7 : EnergyTr) (h9 : EnergyReal) (h10 : JDecayTrQQ)
    (h11 : JAdjTrQQ) : ModelPlaceBuilt3 :=
  modelPlaceBuilt3_of_leavesQQ Formalism.FourierDecayAlt.Final.ma_modelFrameAn eigenvalue_configuration_interlaces admissible_in_truncation_holds h3
    regularity_smooth_forms_holds coefficient_vector_preserves_form bessel_eigenvalue_equation_holds h7 cutoff_transport_to_model h9 h10 h11

theorem modelPlaceBuilt3_of_openGC (hK : Gauge.GCore) (h7 : EnergyTr) (h9 : EnergyReal) (h10 : JDecayTrQQ)
    (h11 : JAdjTrQQ) : ModelPlaceBuilt3 :=
  modelPlaceBuilt3_of_openQQ (gaugeExistsQQ_of_gCore hK) h7 h9 h10 h11

theorem modelPlaceBuilt2_of_openQQ (hJ : JfSmoothDS) (hK : Gauge.GCore) (h7 : EnergyTr) (h9 : EnergyReal)
    (h10 : JDecayTrQQ) (h11 : JAdjTrQQ) : JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_3 hJ (modelPlaceBuilt3_of_openGC hK h7 h9 h10 h11)

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FormZeroEqSlotPairingOfLe
section
namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

theorem pairJ_rel {X Y : Type} {w : List C.Letter} (R : X → Y → Prop) (c : ℂ)
    (Ξ1 : (Ix (Fin w.length) → X) → (Ix (Fin w.length) → X) → ℂ)
    (Ξ2 : (Ix (Fin w.length) → Y) → (Ix (Fin w.length) → Y) → ℂ)
    (h : ∀ x x' y y', (∀ e, R (x e) (y e)) → (∀ e, R (x' e) (y' e)) → Ξ1 x x' = c * Ξ2 y y') :
    ∀ (ys : List ℝ) (x : Ix (Fin (KB.plusW ys w).length) → X) (x' : Ix (Fin (KB.minusW ys w).length) → X)
      (y : Ix (Fin (KB.plusW ys w).length) → Y) (y' : Ix (Fin (KB.minusW ys w).length) → Y),
      (∀ e, R (x e) (y e)) → (∀ e, R (x' e) (y' e)) → KB.pairJ Ξ1 ys x x' = c * KB.pairJ Ξ2 ys y y'
  | [], x, x', y, y', hx, hx' => h x x' y y' hx hx'
  | _ :: ys, x, x', y, y', hx, hx' => by
    show KB.pairJ Ξ1 ys _ _ - KB.pairJ Ξ1 ys _ _ = c * (KB.pairJ Ξ2 ys _ _ - KB.pairJ Ξ2 ys _ _)
    have a1 := pairJ_rel R c Ξ1 Ξ2 h ys (fun e => x (Fin.cons 1 e)) (fun e => x' (Fin.cons 0 e))
      (fun e => y (Fin.cons 1 e)) (fun e => y' (Fin.cons 0 e)) (fun e => hx _) (fun e => hx' _)
    have a2 := pairJ_rel R c Ξ1 Ξ2 h ys (fun e => x (Fin.cons 0 e)) (fun e => x' (Fin.cons 1 e))
      (fun e => y (Fin.cons 0 e)) (fun e => y' (Fin.cons 1 e)) (fun e => hx _) (fun e => hx' _)
    exact (congrArg₂ (· - ·) a1 a2).trans (mul_sub _ _ _).symm

theorem prod_real (zs : List ℂ) (h : ∀ z ∈ zs, z.im = 0) : zs.prod.im = 0 ∧ zs.prod.re = (zs.map Complex.re).prod := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    have hz := h z (by simp)
    obtain ⟨h1, h2⟩ := ih fun z' hz' => h z' (by simp [hz'])
    simp only [List.prod_cons, List.map_cons, Complex.mul_im, Complex.mul_re, hz, h1, mul_zero, zero_mul,
      add_zero, sub_zero, h2]
    exact ⟨trivial, trivial⟩

theorem form_castIx {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : MeasureTheory.Measure (Mt k r))
    {n m : ℕ} (h : n = m) (U V : Ix (Fin n) → RadSp k r z z' π π') (c : Fin r → ℂ) :
    form μ 0 (fun z => U (z ∘ Fin.cast h)) (fun z => V (z ∘ Fin.cast h)) c = form μ 0 U V c := by
  subst h
  rfl

theorem form_embed {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : MeasureTheory.Measure (Mt k r))
    {S S' : Type} [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S'] (ι : Ix S' → Ix S)
    (hι : Function.Injective ι) (x y : Ix S' → RadSp k r z z' π π') (c : Fin r → ℂ) :
    form μ 0 (Function.extend ι x 0) (Function.extend ι y 0) c = form μ 0 x y c := by
  unfold form
  congr 1
  funext c'
  congr 1
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image ι)), Finset.sum_image (fun a _ b _ h => hι h)]
  · simp only [hι.extend_apply]
  · intro z _ hz
    have : ¬ ∃ a, ι a = z := fun ⟨a, ha⟩ => hz (Finset.mem_image.2 ⟨a, Finset.mem_univ a, ha⟩)
    rw [Function.extend_apply' _ _ _ this, Pi.zero_apply, pairAt_zero_left]

theorem pairS_embed {V : Type} [AddCommGroup V] [Module ℂ V] {S S' : Type} [Fintype S] [DecidableEq S] [Fintype S']
    [DecidableEq S'] (β : V → V → ℂ) (hβ : ∀ v, β 0 v = 0) (ι : Ix S' → Ix S) (hι : Function.Injective ι)
    (x y : Ix S' → V) : pairS β (Function.extend ι x 0) (Function.extend ι y 0) = pairS β x y := by
  unfold pairS
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image ι)), Finset.sum_image (fun a _ b _ h => hι h)]
  · simp only [hι.extend_apply]
  · intro z _ hz
    have : ¬ ∃ a, ι a = z := fun ⟨a, ha⟩ => hz (Finset.mem_image.2 ⟨a, Finset.mem_univ a, ha⟩)
    rw [Function.extend_apply' _ _ _ this, Pi.zero_apply, hβ]

def ixEmb {m n : ℕ} (h : m ≤ n) (e : Ix (Fin m)) : Ix (Fin n) := fun t => if ht : t.val < m then e ⟨t, ht⟩ else 0

theorem ixEmb_inj {m n : ℕ} (h : m ≤ n) : Function.Injective (ixEmb h) := by
  intro e e' he
  funext t
  have := congrFun he ⟨t.val, by omega⟩
  simpa [ixEmb, t.isLt] using this

theorem bet_neg {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : MeasureTheory.Measure (Mt k r))
    (v v' : RadSp k r z z' π π') : bet μ (-v) v' = -bet μ v v' := by
  unfold bet
  have := pairLev_smul_left (μ := μ) (i := 0) v v' (fun _ => 1) (-1)
  have e : ((-1 : ℂ) • v) = -v := neg_one_smul ℂ v
  rw [e, neg_one_mul] at this
  exact this

theorem bet_zero {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : MeasureTheory.Measure (Mt k r))
    (v : RadSp k r z z' π π') : bet μ 0 v = 0 := by
  unfold bet; exact pairLev_zero_left v _

section EmbData

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {n : ℕ}
  {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {μ : MeasureTheory.Measure (Mt P.k P.r)}
  {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r} {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ}
  {K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')}

theorem form_zero_eq_position_pairing_of_le (hThm : ThmPOn (S := Fin n) P z z' π π' μ L st K l0) {m : ℕ} (hmn : m ≤ n)
    (Y₁ Y₂ : Ix (Fin m) → RadSp P.k P.r z z' π π') (h₁ : ∀ a, Y₁ a ∈ K 0) (h₂ : ∀ a, Y₂ a ∈ K 0) :
    form μ 0 Y₁ Y₂ 0 = pairS (bet μ) Y₁ Y₂ := by
  have extK : ∀ v : Ix (Fin m) → RadSp P.k P.r z z' π π', (∀ a, v a ∈ K 0) →
      ∀ z, Function.extend (ixEmb hmn) v 0 z ∈ K 0 := by
    intro v hv z
    by_cases hz : ∃ a, ixEmb hmn a = z
    · obtain ⟨a, rfl⟩ := hz
      rw [(ixEmb_inj hmn).extend_apply]; exact hv a
    · rw [Function.extend_apply' _ _ _ hz]; exact (K 0).zero_mem
  have e1 := form_embed μ (ixEmb hmn) (ixEmb_inj hmn) Y₁ Y₂ 0
  have e2 := form_zero_eq_position_pairing hThm (Function.extend (ixEmb hmn) Y₁ 0) (Function.extend (ixEmb hmn) Y₂ 0)
    (extK _ h₁) (extK _ h₂)
  have e3 := pairS_embed (V := RadSp P.k P.r z z' π π') (bet μ) (fun v => bet_zero μ v) (ixEmb hmn) (ixEmb_inj hmn) Y₁ Y₂
  exact e1.symm.trans (e2.trans e3)

end EmbData

theorem final_ineq (Cst : ℝ) (A B P0 Q : ℂ) (qs : List ℂ) (hQ : Q = qs.prod)
    (hqs : ∀ z ∈ qs, 0 < z.re ∧ z.im = 0) (hAi : A.im = 0) (hBi : B.im = 0) (hdk : ‖P0‖ ^ 2 ≤ (A * B / Q).re) :
    ‖(Cst : ℂ) * P0‖ ^ 2 * (qs.map Complex.re).prod ≤ ((Cst : ℂ) * A).re * ((Cst : ℂ) * B).re := by
  obtain ⟨hQi, hQr⟩ := prod_real qs fun z hz => (hqs z hz).2
  have hpos : 0 < (qs.map Complex.re).prod := List.prod_pos fun x hx => by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
    exact (hqs z hz).1
  have eA : A = (A.re : ℂ) := Complex.ext (by simp) (by simp [hAi])
  have eB : B = (B.re : ℂ) := Complex.ext (by simp) (by simp [hBi])
  have eQ : Q = ((qs.map Complex.re).prod : ℂ) := by
    rw [hQ]; exact Complex.ext (by simp [hQr]) (by simp [hQi])
  have h1 : (A * B / Q).re = A.re * B.re / (qs.map Complex.re).prod := by
    rw [eA, eB, eQ, ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]
    simp
  rw [h1, le_div_iff₀ hpos] at hdk
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.re_ofReal_mul, Complex.re_ofReal_mul, mul_pow, sq_abs]
  nlinarith [sq_nonneg Cst]

theorem cast_map_pred {n m : ℕ} (h : n = m) (Q : ∀ k, List (Letter ℂ (Fin k)) → Prop) (u : List (Letter ℂ (Fin n)))
    (hu : Q n u) : Q m (u.map (castL h)) := by
  subst h; rwa [castL_rfl]

theorem Lw_qw (q : ℂ → ℂ) (ys : List ℝ) (w : List C.Letter) :
    ((Lw ys w).map fun l => qw q (Ww ys w) l.pt) = ys.map fun y : ℝ => qw q (D.positionted w) (y : ℂ) := by
  apply List.ext_getElem
  · simp [Lw_length]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_map, Lw_getElem, qw_Ww]

end

end Formalism.FourierDecayAlt.P.PBF

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NormExpMulISubOne
section
noncomputable section

open Complex

namespace Formalism.FourierDecayAlt.P.StandardPairingDecay

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem norm_exp_mul_I_sub_one (y : ℝ) : ‖Complex.exp ((y : ℂ) * I) - 1‖ ≤ |y| := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hc : 1 - y ^ 2 / 2 ≤ Real.cos y := Real.one_sub_sq_div_two_le_cos
  have hs := Real.sin_sq_add_cos_sq y
  have e : (↑(Real.cos y) + ↑(Real.sin y) * I - 1 : ℂ) = ↑(Real.cos y - 1) + ↑(Real.sin y) * I := by
    push_cast; ring
  rw [e]
  have h2 : ‖(↑(Real.cos y - 1) + ↑(Real.sin y) * I : ℂ)‖ ^ 2 ≤ |y| ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I, sq_abs]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (abs_nonneg _) two_ne_zero).1 h2

theorem norm_exp_sub_one_of_re (z : ℂ) (hz : z.re = 0) : ‖Complex.exp z - 1‖ ≤ ‖z‖ := by
  have hz' : z = (z.im : ℂ) * I := by
    apply Complex.ext <;> simp [hz]
  rw [hz']
  refine (norm_exp_mul_I_sub_one z.im).trans (le_of_eq ?_)
  rw [Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem iter_add_const {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (i : ℕ) (f : E → F) (c : F) (x : E) :
    iteratedFDeriv ℝ (i + 1) (fun y => f y + c) x = iteratedFDeriv ℝ (i + 1) f x := by
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  congr 2
  funext y
  exact fderiv_add_const c

variable {k r : ℕ}

theorem mult_phase {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (m : ℕ) (D : Mat k r →L[ℝ] ℂ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℂ, ‖σ‖ ≤ 2 → ∀ (A : ℝ) (F : Mat k r → E) (c : ℝ),
      CCle (A + ((m + 1 : ℕ) : ℝ)) m F c →
      CCle A m (fun g => (Complex.exp (PBFV.phaseL σ D g) - 1) • F g) (K * ‖σ‖ * c) := by
  obtain ⟨C1, hC1, hdlr⟩ := Formalism.FourierDecayAlt.P.JCx4.dlr_bound (k := k) (r := r) (E := E →L[ℂ] E) m
  obtain ⟨K0, hK0⟩ : ∃ K : ℝ, ∀ M : Mat k r, ‖D M‖ ≤ K * ‖M‖ := ⟨_, D.le_opNorm⟩
  set KD : ℝ := max K0 0 with hKDdef
  have hKD0 : 0 ≤ KD := le_max_right _ _
  have hKD : ∀ M : Mat k r, ‖D M‖ ≤ KD * ‖M‖ := fun M =>
    (hK0 M).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  set Lid : ℂ →L[ℝ] (E →L[ℂ] E) :=
    ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℂ) (ContinuousLinearMap.id ℂ E) with hLid
  set L : ℝ := 1 + 4 * KD with hLdef
  have hL1 : 1 ≤ L := by rw [hLdef]; linarith
  set K : ℝ := 2 ^ m * (C1 * (2 ^ m * (((m + 1 : ℕ) : ℝ) * (‖Lid‖ * (2 * KD * (1 + L ^ m)))))) with hKdef
  refine ⟨K, by positivity, ?_⟩
  intro σ hσ A F c hF
  have hc0 : 0 ≤ c := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hF
  set θ : Mat k r →L[ℝ] ℂ := PBFV.phaseL σ D with hθdef
  have hθ0 : ∀ g, (θ g).re = 0 := PBFV.phaseL_re σ D
  set t : ℝ := 2 * ‖σ‖ * KD with htdef
  have ht0 : 0 ≤ t := by positivity
  have htL : t ≤ L := by
    rw [htdef, hLdef]
    have : ‖σ‖ * KD ≤ 2 * KD := mul_le_mul_of_nonneg_right hσ hKD0
    linarith
  have hθM : ∀ M : Mat k r, ‖θ M‖ ≤ t * ‖M‖ := by
    intro M
    rw [hθdef, PBFV.phaseL_apply]
    calc ‖σ * D M - (starRingEnd ℂ) (σ * D M)‖ ≤ ‖σ * D M‖ + ‖(starRingEnd ℂ) (σ * D M)‖ := norm_sub_le _ _
      _ = 2 * (‖σ‖ * ‖D M‖) := by rw [Complex.norm_conj, norm_mul]; ring
      _ ≤ 2 * (‖σ‖ * (KD * ‖M‖)) := by gcongr; exact hKD M
      _ = t * ‖M‖ := by rw [htdef]; ring
  have hθK := θ.opNorm_le_bound ht0 hθM
  have hexp : ContDiff ℝ ⊤ Complex.exp := Complex.contDiff_exp
  set f0 : Mat k r → ℂ := fun g => Complex.exp (θ g) with hf0def
  have hf0 : ContDiff ℝ ⊤ f0 := hexp.comp θ.contDiff
  have hit0 : ∀ i g, ‖iteratedFDeriv ℝ i f0 g‖ ≤ t ^ i := by
    intro i g
    have h2 : iteratedFDeriv ℝ i f0 g =
        (iteratedFDeriv ℝ i Complex.exp (θ g)).compContinuousLinearMap (fun _ => θ) :=
      θ.iteratedFDeriv_comp_right (f := Complex.exp) hexp g (by exact_mod_cast le_top)
    have h3 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ i Complex.exp (θ g)) (fun _ : Fin i => θ)
    have h5 := h3.trans (mul_le_mul (le_of_eq (by rw [PBFV.norm_iter_cexp, hθ0, Real.exp_zero]))
      (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun _ _ => hθK))
      (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one)
    rw [one_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h5
    rw [h2]; exact h5
  set f1 : Mat k r → ℂ := fun g => f0 g + (-1 : ℂ) with hf1def
  have hf1 : ContDiff ℝ ⊤ f1 := hf0.add contDiff_const
  set Λ : Mat k r → (E →L[ℂ] E) := fun g => Lid (f1 g) with hΛdef
  have hΛ : ∀ g, Λ g = (Complex.exp (θ g) - 1) • ContinuousLinearMap.id ℂ E := fun g => by
    simp [Λ, Lid, f1, f0, sub_eq_add_neg]
  have hΛc : ContDiff ℝ ⊤ Λ := Lid.contDiff.comp hf1
  have hitΛ : ∀ i, i ≤ m → ∀ g, ‖iteratedFDeriv ℝ i Λ g‖ ≤ ‖Lid‖ * (t * (‖g‖ + L ^ m)) := by
    intro i hi g
    have h1 := Lid.norm_iteratedFDeriv_comp_left (f := f1) (x := g) (N := ⊤) (n := i)
      hf1.contDiffAt (by exact_mod_cast le_top)
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rcases i with _ | j
    · rw [norm_iteratedFDeriv_zero]
      have e1 : f1 g = Complex.exp (θ g) - 1 := by simp [f1, f0, sub_eq_add_neg]
      rw [e1]
      calc ‖Complex.exp (θ g) - 1‖ ≤ ‖θ g‖ := norm_exp_sub_one_of_re _ (hθ0 g)
        _ ≤ t * ‖g‖ := hθM g
        _ ≤ t * (‖g‖ + L ^ m) := by
          have : 0 ≤ L ^ m := by positivity
          nlinarith
    · rw [show f1 = fun y => f0 y + (-1 : ℂ) from rfl, iter_add_const]
      calc ‖iteratedFDeriv ℝ (j + 1) f0 g‖ ≤ t ^ (j + 1) := hit0 _ g
        _ = t * t ^ j := by ring
        _ ≤ t * L ^ m := by
          refine mul_le_mul_of_nonneg_left ?_ ht0
          calc t ^ j ≤ L ^ j := pow_le_pow_left₀ ht0 htL j
            _ ≤ L ^ m := pow_le_pow_right₀ hL1 (by omega)
        _ ≤ t * (‖g‖ + L ^ m) := by
          have : 0 ≤ ‖g‖ := norm_nonneg _
          nlinarith
  set Cm : ℝ := C1 * (2 ^ m * (((m + 1 : ℕ) : ℝ) * (‖Lid‖ * (t * (1 + L ^ m))))) with hCm
  have hab : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
      u.length + v.length ≤ m → ∀ g ∈ GV k r, g ∉ (∅ : Set (Mat k r)) →
        ‖dLR u v Λ g‖ ≤ Cm * gN g ^ (((m + 1 : ℕ) : ℕ) : ℝ) := by
    intro u v hu hv hl g hg _
    rw [Real.rpow_natCast]
    have h1 := hdlr Λ (hΛc.of_le (by exact_mod_cast le_top)) u v hu hv hl g
    have hg1 : 1 ≤ gN g := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
    have hng : ‖g‖ ≤ gN g := Formalism.FourierDecayAlt.P.JCx2.mn_norm_le_gN g
    have hsum : ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i Λ g‖ ≤
        ((m + 1 : ℕ) : ℝ) * (‖Lid‖ * (t * (‖g‖ + L ^ m))) := by
      calc ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i Λ g‖
          ≤ ∑ _i ∈ Finset.range (m + 1), ‖Lid‖ * (t * (‖g‖ + L ^ m)) :=
            Finset.sum_le_sum fun i hi => hitΛ i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) g
        _ = ((m + 1 : ℕ) : ℝ) * (‖Lid‖ * (t * (‖g‖ + L ^ m))) := by simp
    have hpow : (1 + ‖g‖) ^ m ≤ 2 ^ m * gN g ^ m := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) m
    have hgL : ‖g‖ + L ^ m ≤ (1 + L ^ m) * gN g := by
      have : 0 ≤ L ^ m := by positivity
      nlinarith
    have hS0 : 0 ≤ ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i Λ g‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hLid0 : 0 ≤ ‖Lid‖ := norm_nonneg _
    calc ‖dLR u v Λ g‖ ≤ C1 * (1 + ‖g‖) ^ m * ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i Λ g‖ := h1
      _ ≤ C1 * (2 ^ m * gN g ^ m) * (((m + 1 : ℕ) : ℝ) * (‖Lid‖ * (t * ((1 + L ^ m) * gN g)))) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hpow hC1) (hsum.trans ?_) hS0
          · exact mul_nonneg hC1 (by positivity)
          · gcongr
      _ = Cm * gN g ^ (m + 1) := by rw [hCm]; ring
  have ha : CkOn (m : ℕ∞) Set.univ Λ := fun g₀ _ =>
    ⟨Set.univ, Λ, isOpen_univ, trivial, (hΛc.of_le (by exact_mod_cast le_top)).contDiffOn, fun _ _ _ => rfl⟩
  have hb' := Formalism.FourierDecayAlt.P.BetaSesquilinearity.prodBound (O := ∅) (UU := Set.univ) isOpen_empty (fun g _ => Or.inr trivial)
    (A := A) (d := (((m + 1 : ℕ) : ℕ) : ℝ)) ha hab hF (fun g _ h => h.elim)
  have e : (fun g => (Complex.exp (PBFV.phaseL σ D g) - 1) • F g) = Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap Λ F := by
    funext g
    simp [Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap, hΛ, θ]
  rw [e]
  refine Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c hb' (le_of_eq ?_)
  have hCm0 : 0 ≤ Cm := by rw [hCm]; positivity
  rw [abs_of_nonneg hCm0, abs_of_nonneg hc0, hCm, hKdef, htdef]
  ring

end Formalism.FourierDecayAlt.P.StandardPairingDecay
end
end

