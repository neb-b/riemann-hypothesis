module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0061
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0062
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0053
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0058
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0057
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0051
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0060
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0047

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ']
  {y' : (Σ k, ι' k) → Φ'}

def pairV {R : Type} (a : (Σ k, ι k) → R) (b : (Σ k, ι' k) → R) : (Σ k, Sum.elim ι ι' k) → R
  | ⟨.inl k, i⟩ => a ⟨k, i⟩
  | ⟨.inr k, i⟩ => b ⟨k, i⟩

theorem pairV_inl {R : Type} (a : (Σ k, ι k) → R) (b : (Σ k, ι' k) → R) (p : Σ k, ι k) :
    pairV a b (inlV p) = a p := rfl

theorem pairV_inr {R : Type} (a : (Σ k, ι k) → R) (b : (Σ k, ι' k) → R) (p : Σ k, ι' k) :
    pairV a b (inrV p) = b p := rfl

def stepOf (M : FlagModel y Ψ N j) (k : K) (h : ¬ ∀ p, M.blk p ≠ some k) : Ψ × Fin N :=
  Classical.choose (not_forall_not.1 (by simpa using h) : ∃ p, M.blk p = some k)

theorem blk_stepOf (M : FlagModel y Ψ N j) (k : K) (h : ¬ ∀ p, M.blk p ≠ some k) :
    M.blk (stepOf M k h) = some k := by
  unfold stepOf
  exact Classical.choose_spec (p := fun p => M.blk p = some k) _

def transPt {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M) : (Σ k, ι k) → Φ' := fun q =>
  if h : ∀ p, M.blk p ≠ some q.1 then algebraMap M'.Ω Φ' (Cv.φ (M.x ⟨⟨q.1, h⟩, q.2⟩))
  else ∑ I, algebraMap M'.Ω Φ' (Cv.φ (M.coef q I)) *
    minorIJ (M'.g (stepOf M q.1 h).1) I (stepCols N j (stepOf M q.1 h).2)

theorem transPt_base {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (q : Σ k, baseIdx ι M.blk k) :
    transPt Cv ⟨q.1.1, q.2⟩ = algebraMap M'.Ω Φ' (Cv.φ (M.x q)) :=
  dif_pos q.1.2

theorem transPt_step {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (p : Ψ × Fin N) (k : K) (hp : M.blk p = some k) (m : ι k) :
    transPt Cv ⟨k, m⟩ = ∑ I, algebraMap M'.Ω Φ' (Cv.φ (M.coef ⟨k, m⟩ I)) * minorIJ (M'.g p.1) I (stepCols N j p.2) := by
  have h : ¬ ∀ p, M.blk p ≠ some k := fun H => H p hp
  have e : stepOf M k h = p := M.blk_inj _ _ k (blk_stepOf M k h) hp
  rw [transPt, dite_eq_right h, e]

def trMat {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (τ : Ψ) : Matrix (Fin N) (Fin N) M'.Ω :=
  ((F.T τ).map Cv.φ)⁻¹ * F'.T τ

def coE {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (p : Ψ × Fin N)
    (q : Σ k, ι k) (r : Σ k, ι' k) : M'.Ω :=
  ∑ I, ∑ I' ∈ Finset.univ.filter (IsStepRows N j p.2),
    Cv.φ (F.u q I) * minorIJ (trMat Cv F' F p.1) I I' * F'.u' I' r

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartFifth
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem fibre_member_potential : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ (p : Ψ × Fin N) (z : Fin (d + 1) → ℂ), Fin.tail z ∈ Un → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ((FA.S.comap some).potH p).φ (ΦYn z) (ΦYn z') = potAt BM l p (bp (Fin.tail z')) (flagAt H τ ca cb (z' 0) (Fin.tail z') p.1) + (Hh z').re := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb hb hab hca hcb X q Un Gn ΦYn ΦWn l H bp hUn hF p z hz
  have hV : IsOpen {u : Fin (d + 1) → ℂ | Fin.tail u ∈ Un} := by
    have hc : Continuous (fun u : Fin (d + 1) → ℂ => (Fin.tail u : Fin d → ℂ)) :=
      continuous_pi fun i => continuous_apply _
    exact hUn.preimage hc
  obtain ⟨zex, hzan, hzex⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.exact_points_holomorphic K ι Φ y Ψ N j M n d BM FA τ a ca cb X q Un Gn ΦYn ΦWn l H bp hUn hF
  have hbij := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.realis_bijective_of_degree_one K ι (d + 1) (Option (Ψ × Fin N)) FA.S (mCoordIdeal y) FA.Re FA.deg_one FA.br_empty
  obtain ⟨Hh, hHh, hev⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.ref_pot_along_exact_family K ι (d + 1) (Option (Ψ × Fin N)) FA.S (mCoordIdeal y) FA.Re (some p) (d + 1)
    {u : Fin (d + 1) → ℂ | Fin.tail u ∈ Un} ΦYn zex z FA.J_top FA.deg_one FA.br_empty hV hz hzan
    (fun u hu => (hzex u hu).1) (fun u hu x₀ hx => ((hzex u hu).2 x₀ hx).1)
  refine ⟨Hh, hHh, ?_⟩
  filter_upwards [hev, hV.mem_nhds hz] with z' h1 hz'
  obtain ⟨x₀, hx₀⟩ := hbij.2 (ΦYn z')
  obtain ⟨h2, h3, h4⟩ := (hzex z' hz').2 x₀ hx₀
  obtain ⟨hbO, hH⟩ := hF.2.2.2.1 _ hz'
  obtain ⟨hsb, hsd, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.Shear.shear_main N j a b ca cb (z' 0) M.j_le hb hab hca hcb
  have hflag : IsBlockDiag j (flagAt H τ ca cb (z' 0) (Fin.tail z') p.1) ∧
      (flagAt H τ ca cb (z' 0) (Fin.tail z') p.1).det ≠ 0 := by
    unfold flagAt
    split_ifs with hp
    · subst hp
      refine ⟨(hH p.1).1.mul hsb, ?_⟩
      rw [Matrix.det_mul, hsd, mul_one]
      exact (hH p.1).2
    · exact hH p.1
  have hline := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_fsHerm_add_ph_eq_potAt K ι Φ y Ψ N j M n d BM FA l x₀ (zex z') (bp (Fin.tail z')) p
    (flagAt H τ ca cb (z' 0) (Fin.tail z') p.1) hbO h2 h3 (h4 p.1 p.2) hflag.1 hflag.2
  have hphi : ((FA.S.comap some).potH p).φ (ΦYn z) (ΦYn z') =
      (FA.S.th (some p)).φ (ΦYn z) (ΦYn z') + FA.S.ph (some p) (ΦYn z') := rfl
  rw [hphi, h1, FA.ref_some, ← hline, hx₀]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end

