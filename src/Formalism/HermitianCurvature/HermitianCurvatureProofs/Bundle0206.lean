module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0200
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0003
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleRecOfAdmissibleWord
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0203
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0197
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0198
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0069
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0199
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
public import Formalism.FormalDegreeBessel.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0191
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0190
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMStepA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0201
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0168
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0174
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0124
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MatrixUnitZeroZeroEqInsert
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0129

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleOfRange
section
noncomputable section

open Finset MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.PBI

theorem interlaces_rho {P : M.Par} (h : P.OK) (ρ : M.Ty P) : I.Interlaces P.k P.u P.u' (M.rho P ρ) := by
  intro i hi
  obtain ⟨h1, h2⟩ := Formalism.FourierDecayAlt.P.Topx1.vecw_rho_bounds h ρ hi
  unfold M.Par.lo at h1
  unfold M.Par.hi at h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [min_le_left (P.u i) (P.u' i)]
  · linarith [min_le_right (P.u i) (P.u' i)]
  · linarith [le_max_left (P.u (i + 1)) (P.u' (i + 1))]
  · linarith [le_max_right (P.u (i + 1)) (P.u' (i + 1))]

theorem xC_ofReal (P : M.Par) (ρ : M.Ty P) (y : ℝ) :
    M.xC P ρ (y : ℂ) = ((I.xpoly P.k (M.rho P ρ) y : ℝ) : ℂ) := by
  simp [M.xC, I.xpoly]

theorem qC_ofReal (P : M.Par) (y : ℝ) : M.qC P (y : ℂ) = ((I.qpoly P.k P.T P.T' P.u P.u' y : ℝ) : ℂ) := by
  simp [M.qC, I.qpoly]

def AdmOfCutRange : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq))
    (X : Q.ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r z z' π π')))
    (l0 : ℕ) (w : List C.Letter), 1 ≤ l0 → l0 ≤ P.k →
    P5.IsData P z z' π π' X μ L st l0 → KB.CutWord P l0 w → Fr.admitted st (D.positionted w)

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

theorem admissible_of_range : PBI.AdmOfCutRange := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 w hl1 hl2 hD hcut
  obtain ⟨hPl, -, -, -, hq, hinv, -, -⟩ := hD
  have hOK : P.OK := hPl.1
  let ρ0 : M.Ty P := fun _ => 0
  have hint0 := PBI.interlaces_rho hOK ρ0
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [D.positionted, List.map_ofFn]
    exact List.nodup_ofFn.2 (fun a b h => h)
  · intro l hl
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hl
    simp [Complex.conj_ofReal]
  · intro l hl
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hl
    set y := (w.get a).2 with hy
    have hca : I.OnCut P.u P.u' l0 y := hcut.1 a
    have hx : ∀ ρ : M.Ty P, ∀ e ∈ ({-1, 0, 1} : Finset ℝ), I.xpoly P.k (M.rho P ρ) (y + e) ≠ 0 := by
      intro ρ e he h0
      have := Formalism.FourierDecayAlt.P.interlacing_sign P.k P.u P.u' (M.rho P ρ) l0 y hl1 hl2 (PBI.interlaces_rho hOK ρ) hca e he
      rw [h0, mul_zero] at this
      exact lt_irrefl _ this
    rw [hinv, hq]
    simp only [Set.mem_setOf_eq]
    refine ⟨fun ρ => ?_, fun ρ => ?_, fun ρ => ?_, ?_, ?_⟩
    · rw [PBI.xC_ofReal]
      have := hx ρ 0 (by simp)
      rw [add_zero] at this
      exact_mod_cast this
    · have e : ((y : ℝ) : ℂ) + 1 = ((y + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [e, PBI.xC_ofReal]
      exact_mod_cast hx ρ 1 (by simp)
    · have e : ((y : ℝ) : ℂ) - 1 = ((y + -1 : ℝ) : ℂ) := by push_cast; ring
      rw [e, PBI.xC_ofReal]
      exact_mod_cast hx ρ (-1) (by simp)
    · rw [PBI.qC_ofReal]
      have := Formalism.FourierDecayAlt.P.q_positive_interlacing P.k P.u P.u' (M.rho P ρ0) l0 y P.T P.T' hl1 hl2 hint0 hca hOK.T_pos hOK.T'_pos
      exact_mod_cast this.ne'
    · have e : ((y : ℝ) : ℂ) - 1 = ((y - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [e, PBI.qC_ofReal]
      have := Formalism.FourierDecayAlt.P.q_positive_shift P.k P.u P.u' (M.rho P ρ0) l0 y P.T P.T' hl1 hl2 hint0 hca
        hOK.T_pos hOK.T'_pos
      exact_mod_cast this.ne'
  · simp only [D.positionted]
    rw [List.pairwise_ofFn]
    intro i j hij n hn h
    have hne : i ≠ j := ne_of_lt hij
    have hd := hcut.2 i j hne
    have h' : (w.get i).2 - (w.get j).2 = (n : ℝ) := by
      have h2 := h
      simp only at h2
      exact_mod_cast h2
    rw [h'] at hd
    have : |((n : ℤ) : ℝ)| ≤ 2 := by exact_mod_cast hn
    linarith

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockKWave
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem prod_ofFn_map {K : ℕ} (f : Fin K → ℝ) (g : ℝ → ℝ) : ((List.ofFn f).map g).prod = ∏ b, g (f b) := by
  rw [List.map_ofFn, List.prod_ofFn]; rfl

section blockK

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem sW_eq (S : C.HidaSetting E Wp Wq) (j : ℕ) (l : ℂ) :
    sW S j l = Complex.I * (((2 * Real.pi / ((S.g : ℝ) * lamS S j)) : ℝ) : ℂ) * l := rfl

end blockK

end

end Formalism.FourierDecayAlt.P.PBL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliVectorAsGenerators
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem cvag_posL_iff {k r : ℕ} (a b : Fin (Q.mdim k r 0)) : Q.posL k r 0 a = Q.posL k r 0 b ↔ a = b := by
  simp [Q.posL, Fin.ext_iff]

theorem cvag_list {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (u : ℂ)
    (σ : Equiv.Perm (Fin (Q.mdim k r 0))) :
    (List.ofFn fun i : Fin (Q.mdim k r 0) =>
      Top (Q.EH (E := E) k r) (u - ((i : ℕ) : ℂ)) (Q.posL k r 0 (σ i)) (Q.posL k r 0 i)) =
      (capGens (zgCV k r) σ).map (fun gn => genOpR (E := E) gn u) := by
  unfold capGens
  rw [List.map_ofFn]
  congr 1
  funext i F h
  simp only [Function.comp_apply, Formalism.QuantumDeterminants.Top, genOpR, capGen, zgCV, Q.EH, EabH, cvag_posL_iff, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, one_smul, add_zero]
  split_ifs <;> simp

theorem capelli_vector_as_generators : CVAsGens := by
  intro k r E _ _ Y f g
  simp only [Q.CV, Q.capL, qminorOp, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [cvag_list]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CoefficientInterpolationHolds
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

theorem coefficient_interpolation_holds : CoeffInterp := by
  intro N m _hm
  refine ⟨fun i => ((i : ℕ) : ℝ),
    fun i => (Lagrange.basis (Finset.univ : Finset (Fin (N + 1))) (fun j => ((j : ℕ) : ℂ)) i).coeff m, ?_⟩
  intro q hq
  have hinj : Set.InjOn (fun j : Fin (N + 1) => ((j : ℕ) : ℂ)) ((Finset.univ : Finset (Fin (N + 1))) : Set (Fin (N + 1))) := by
    intro a _ b _ hab
    simp only at hab
    exact Fin.ext (by exact_mod_cast hab)
  have hdeg : q.degree < ((Finset.univ : Finset (Fin (N + 1))).card : WithBot ℕ) := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hq) (by exact_mod_cast Nat.lt_succ_self N)
  have h := Lagrange.eq_interpolate hinj hdeg
  conv_rhs => rw [h]
  rw [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.coeff_C_mul]
  simp only [Complex.ofReal_natCast]
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationAlgebraicHolds
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix Polynomial
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem gv_facts {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    g⁻¹ * g = 1 ∧ g * g⁻¹ = 1 ∧ Hpk k r * g = (g⁻¹)ᴴ * Hpk k r ∧ gᴴ * Hpk k r = Hpk k r * g⁻¹ := by
  obtain ⟨-, hHH, -⟩ := Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r
  have hg0 : gᴴ * Hpk k r * g = Hpk k r := hg
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    calc (Hpk k r * gᴴ * Hpk k r) * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg0, hHH]
  have hr : g * (Hpk k r * gᴴ * Hpk k r) = 1 := mul_eq_one_comm.mp hl
  have hinv : g⁻¹ = Hpk k r * gᴴ * Hpk k r := Matrix.inv_eq_left_inv hl
  have hgi : g⁻¹ * g = 1 := by rw [hinv]; exact hl
  have hig : g * g⁻¹ = 1 := by rw [hinv]; exact hr
  refine ⟨hgi, hig, ?_, ?_⟩
  · calc Hpk k r * g = ((g⁻¹)ᴴ * gᴴ) * Hpk k r * g := by
          rw [← Matrix.conjTranspose_mul, hig, Matrix.conjTranspose_one, Matrix.one_mul]
      _ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
      _ = (g⁻¹)ᴴ * Hpk k r := by rw [hg0]
  · calc gᴴ * Hpk k r = gᴴ * Hpk k r * (g * g⁻¹) := by rw [hig, Matrix.mul_one]
      _ = (gᴴ * Hpk k r * g) * g⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Hpk k r * g⁻¹ := by rw [hg0]

theorem conjugation_algebraic_holds : ConjAlg := by
  intro k r g hg
  obtain ⟨hgi, hig, hHg, hgH⟩ := gv_facts hg
  refine ⟨fun A hA => ?_, fun A hA => ?_, fun A h0 => ?_, fun A X => ?_⟩
  · unfold B.inLie at hA ⊢
    have e1 : (g * A * g⁻¹)ᴴ * Hpk k r = (g⁻¹)ᴴ * (Aᴴ * Hpk k r) * g⁻¹ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
      rw [hgH]
    have e2 : Hpk k r * (g * A * g⁻¹) = (g⁻¹)ᴴ * (Hpk k r * A) * g⁻¹ := by
      simp only [← Matrix.mul_assoc]
      rw [hHg]
    rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hA, Matrix.mul_zero, Matrix.zero_mul]
  · obtain ⟨n, hn⟩ := hA
    refine ⟨n, ?_⟩
    have hp : ∀ m : ℕ, (g * A * g⁻¹) ^ m = g * A ^ m * g⁻¹ := by
      intro m
      induction m with
      | zero => simp [hig]
      | succ m ih =>
        rw [pow_succ, ih, pow_succ]
        calc g * A ^ m * g⁻¹ * (g * A * g⁻¹) = g * A ^ m * (g⁻¹ * g) * A * g⁻¹ := by
              simp only [Matrix.mul_assoc]
          _ = g * (A ^ m * A) * g⁻¹ := by rw [hgi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [hp, hn, Matrix.mul_zero, Matrix.zero_mul]
  · intro h
    apply h0
    calc A = (g⁻¹ * g) * A * (g⁻¹ * g) := by rw [hgi, Matrix.one_mul, Matrix.mul_one]
      _ = g⁻¹ * (g * A * g⁻¹) * g := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]
  · have e : (g * A * g⁻¹) * (g * X * g⁻¹) = g * (A * X * g⁻¹) := by
      calc (g * A * g⁻¹) * (g * X * g⁻¹) = g * A * (g⁻¹ * g) * X * g⁻¹ := by simp only [Matrix.mul_assoc]
        _ = g * (A * X * g⁻¹) := by rw [hgi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, hgi, Matrix.mul_one]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableFormAdj
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory Filter Topology

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem rw_eq_zero_of_not_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (h : B.Mat k r → E) :
    ∀ (w : List (B.Mat k r)) (x : B.Mat k r), x ∉ tsupport h → B.Rw w h x = 0 := by
  intro w
  induction w with
  | nil =>
    intro x hx
    show h x = 0
    by_contra hne
    exact hx (subset_tsupport _ hne)
  | cons X w ih =>
    intro x hx
    show RdV X (B.Rw w h) x = 0
    have hO : IsOpen (tsupport h)ᶜ := (isClosed_tsupport h).isOpen_compl
    have hc : Continuous (fun t : ℝ => x * NormedSpace.exp ((t : ℂ) • X)) :=
      (Formalism.FourierDecayAlt.P.B5.curve_contDiff x X).continuous
    have h0 : (fun t : ℝ => x * NormedSpace.exp ((t : ℂ) • X)) 0 ∈ (tsupport h)ᶜ := by
      show x * NormedSpace.exp (((0 : ℝ) : ℂ) • X) ∈ _
      rw [Formalism.FourierDecayAlt.P.B5.curve_zero]
      exact hx
    have hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), x * NormedSpace.exp (((t : ℝ) : ℂ) • X) ∈ (tsupport h)ᶜ :=
      hc.continuousAt.preimage_mem_nhds (hO.mem_nhds h0)
    have heq : (fun t : ℝ => B.Rw w h (x * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 (0 : ℝ)] fun _ : ℝ => (0 : E) :=
      hev.mono fun t ht => ih _ ht
    unfold RdV
    rw [heq.deriv_eq]
    simp

theorem integrable_nn {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (B.GV k r) μ) {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    {A : B.Mat k r → E₁} {C : B.Mat k r → E₂} (hA : ContinuousOn A (B.GV k r)) (hC : ContinuousOn C (B.GV k r))
    {K : Set (B.Mat k r)} (hK : IsCompact K) (hAz : ∀ x, x ∉ K → A x = 0) :
    Integrable (fun g : Mt k r => ‖A (Matrix.of g)‖ * ‖C (Matrix.of g)‖) μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨hμ.finite_compact⟩
  have hu : ContinuousOn (fun x => ‖A x‖ * ‖C x‖) (B.GV k r) :=
    (continuous_norm.comp_continuousOn hA).mul (continuous_norm.comp_continuousOn hC)
  have hKG : IsCompact (K ∩ B.GV k r) := hK.inter_right Formalism.FourierDecayAlt.P.B5.GV_closed
  obtain ⟨M, hM⟩ := hKG.exists_bound_of_continuousOn (hu.mono Set.inter_subset_right)
  have hmeas : AEStronglyMeasurable (fun g : Mt k r => ‖A (Matrix.of g)‖ * ‖C (Matrix.of g)‖) μ := by
    have h1 := Formalism.FourierDecayAlt.P.B5.aesm_of_continuousOn hμ (f := fun x => ((‖A x‖ * ‖C x‖ : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp_continuousOn hu)
    exact (Complex.continuous_re.comp_aestronglyMeasurable h1).congr (Eventually.of_forall fun g => by simp)
  have hKm : IsCompact (Matrix.of ⁻¹' K : Set (Mt k r)) := hK
  refine Integrable.mono' ((integrableOn_const hKm.measure_lt_top.ne).integrable_indicator
    hKm.isClosed.measurableSet) hmeas ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.haar_ae hμ] with g hg
  by_cases hgK : Matrix.of g ∈ K
  · have hg' : g ∈ (Matrix.of ⁻¹' K : Set (Mt k r)) := hgK
    rw [Set.indicator_of_mem hg']
    exact hM _ ⟨hgK, hg⟩
  · have hg' : g ∉ (Matrix.of ⁻¹' K : Set (Mt k r)) := hgK
    simp only [Set.indicator, hg', if_false, hAz _ hgK, norm_zero, zero_mul, le_refl]

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem form_adjoint_holds : FormAdj := by
  intro k r Wp Wq _ _ _ _ _ _ D Θ hs hc F F' hF hFc hFs hF' hF'c hF's
  have e1 : (Matrix.of (Matrix.of.symm (1 : B.Mat k r)) : B.Mat k r) = 1 := Equiv.apply_symm_apply _ _
  have hp0 : D.inSS ((Matrix.of.symm 1, Matrix.of.symm 1), (Matrix.of.symm 1, Matrix.of.symm 1)) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [e1]
    · exact Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z
    · exact (Formalism.QuantumDeterminants.nSubgroup k r).1
    · exact Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z'
    · exact (Formalism.QuantumDeterminants.nSubgroup k r).1
  have hrho : ∀ A : B.Mat k r → (Wq →L[ℂ] Wp),
      B.rho D ((Matrix.of.symm 1, Matrix.of.symm 1), (Matrix.of.symm 1, Matrix.of.symm 1)) A = A := by
    intro A
    funext g
    simp only [B.rho, B.sgs, e1, inv_one, mul_one, one_mul, D.π_rep.1, D.π'_rep.1]
    ext v
    simp
  have hI : B.IntClause D Θ F F' := by
    intro p hp T hT i j _ _
    have hcA : B.CkOn ⊤ (B.GV k r) (fun x => T.coefAdj x (F' x)) :=
      Formalism.FourierDecayAlt.P.B5.ckOn_coef (hs T hT).2 hF' hF's
    have hK : IsCompact (tsupport (fun x => T.coefAdj x (F' x))) :=
      IsCompact.of_isClosed_subset hF'c (isClosed_tsupport _)
        (closure_mono fun x hx h0 => hx (by show T.coefAdj x (F' x) = 0; rw [h0, map_zero]))
    exact integrable_nn D.haarG
      (Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (Formalism.FourierDecayAlt.P.JFxI.ckOn_Rw_top' hcA _ fun X hX =>
        T.word_lie X (List.mem_of_mem_take (List.mem_reverse.1 hX))))
      (Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (Formalism.FourierDecayAlt.P.JFxI.ckOn_Rw_top' (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hF) _
        fun X hX => T.word_lie X (List.mem_of_mem_drop hX)))
      hK (fun x hx => rw_eq_zero_of_not_mem _ _ x hx)
  have key := Formalism.FourierDecayAlt.P.phase_function_adjoint k r Wp Wq D (B.GPos D) Θ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gPos_stable D) hs hc F F'
    (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF) (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF') hFs hF's hI _ hp0
  unfold B.Ph at key
  rwa [hrho, hrho] at key

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLExhAll
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

theorem avgCutoff_of_smooth (h : ACSmooth) : Formalism.FourierDecayAlt.P.JFxI.AvgCutoff :=
  avgCutoff_of_parts averaging_bump_holds averaging_invariance_holds averaging_integrability_holds averaging_haar_positivity h

theorem sAExh_of_smooth (h : ACSmooth) : SAExh :=
  sAExh_of_avgCutoff (avgCutoff_of_smooth h)

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMStepAPf
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.GrpMA

theorem lvlA_last : LvlA := by
  intro Wp Wq _ _ _ _ k r hr z z' π π' D' Y hz hz' hD J₀ hJ₀ c hc g hg hgD
  have h := Formalism.FourierDecayAlt.P.Qx6.lvlA (E := Wq →L[ℂ] Wp) hz hz' (TemperedBoundGL3.lr hr) (by show r - 1 + 1 = r; omega) hD hJ₀.1
    hJ₀.2.1 hJ₀.2.2.1 Y hc (by rw [TemperedBoundGL3.lr_succ]; exact hg) hgD
  rw [TemperedBoundGL3.lr_succ] at h
  exact h

theorem mirror_residue_first_move : JDRvStepA := jDRvStepA_of_lvlA lvlA_last

end Formalism.FourierDecayAlt.P.CutMP.GrpMA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutTop
section
namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_genTransfer (hJ : JfSmoothDS) (hG : Gauge.GC.GenTransfer)
    (hD : JDecayTrQQ) (hA : JAdjTrQQ) : Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_openQQ hJ (Gauge.GC.gCore_of_genTransfer hG) energy_trace_identity_holds energy_reality_holds hD hA

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PbTopFirstOf
section
namespace Formalism.FourierDecayAlt.P

theorem pb_degTop_of (hRA : PBN.RadAATop) (hPT : PBN.PolyTop) : Formalism.FourierDecayAlt.KB.DegTop :=
  degree_top_of_parts word_recursion hRA hPT density_constant

end Formalism.FourierDecayAlt.P
end

