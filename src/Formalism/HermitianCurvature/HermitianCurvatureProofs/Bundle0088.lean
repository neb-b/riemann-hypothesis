module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0069
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0084
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameEntries
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0045
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0070

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLLieGrp
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

namespace KLR

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem exp_intertwine {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) (D' : Wq →L[ℂ] Wq)
    (D : Wp →L[ℂ] Wp) (h : A.comp D' = D.comp A) :
    A.comp (NormedSpace.exp D') = (NormedSpace.exp D).comp A := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have : CompleteSpace Wq := FiniteDimensional.complete ℂ Wq
  have hp : ∀ n : ℕ, A.comp (D' ^ n) = (D ^ n).comp A := by
    intro n
    induction n with
    | zero => ext v; simp
    | succ n ih =>
      ext v
      have e1 := congrArg (fun T : Wq →L[ℂ] Wp => T (D' v)) ih
      have e2 := congrArg (fun T : Wq →L[ℂ] Wp => T v) h
      simp only [ContinuousLinearMap.comp_apply] at e1 e2 ⊢
      rw [pow_succ, pow_succ, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, e1, e2]
  have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) D'
  have h2 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) D
  have g1 := h1.map (ContinuousLinearMap.compL ℂ Wq Wq Wp A) (ContinuousLinearMap.continuous _)
  have g2 := h2.map ((ContinuousLinearMap.compL ℂ Wq Wp Wp).flip A) (ContinuousLinearMap.continuous _)
  have e : ((ContinuousLinearMap.compL ℂ Wq Wq Wp A) ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • D' ^ n) =
      (((ContinuousLinearMap.compL ℂ Wq Wp Wp).flip A) ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • D ^ n) := by
    funext n
    simp only [Function.comp_apply, ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, hp]
  rw [e] at g1
  exact g1.unique g2

theorem exp_conj {g : Mx k r} (hg : IsUnit g.det) (X : Mx k r) :
    NormedSpace.exp (g * X * g⁻¹) = g * NormedSpace.exp X * g⁻¹ := by
  have h := HermitianFormRankFour.exp_semiconj (g * X * g⁻¹) X g (by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hg, Matrix.mul_one])
  calc NormedSpace.exp (g * X * g⁻¹) = NormedSpace.exp (g * X * g⁻¹) * g * g⁻¹ := by
        rw [Matrix.mul_assoc (NormedSpace.exp (g * X * g⁻¹)) g g⁻¹, Matrix.mul_nonsing_inv _ hg, Matrix.mul_one]
    _ = g * NormedSpace.exp X * g⁻¹ := by rw [h]

theorem pi_exp_frame {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)} (hπ : Qr.IsRepW k r z π) {m : ℕ}
    {Bs : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : IsFrameOf k r [z] Bs) (B : Matrix (Fin m) (Fin m) ℂ)
    (hBs : Bᴴ = -B) :
    InLieW k r z (∑ p : Fin m × Fin m, B p.1 p.2 • unitB (Hpk k r) Bs p.1 p.2) ∧
    π (NormedSpace.exp (∑ p : Fin m × Fin m, B p.1 p.2 • unitB (Hpk k r) Bs p.1 p.2)) =
      NormedSpace.exp (∑ p : Fin m × Fin m, B p.1 p.2 • ecOp π (unitB (Hpk k r) Bs p.1 p.2)) := by
  obtain ⟨X, hX⟩ : ∃ X, X = ∑ p : Fin m × Fin m, B p.1 p.2 • unitB (Hpk k r) Bs p.1 p.2 := ⟨_, rfl⟩
  rw [← hX]
  have hsk : Xᴴ * Hpk k r + Hpk k r * X = 0 := by
    rw [hX, ← KLG.sum_unitB]
    exact HermitianFormRankFour.skew_of Qx8.hpk_herm hBs
  have hs := HermitianFormSums.ec_sum elementary_lie_elements hπ Finset.univ (fun p : Fin m × Fin m => B p.1 p.2)
    (fun p => unitB (Hpk k r) Bs p.1 p.2) (fun p => frame_lie hB p.1 p.2) 0 (SkewHermitianParts.inGl_zero z)
  beta_reduce at hs
  rw [← hX] at hs
  have hL : InLieW k r z X := by
    have := hs.1.1
    rwa [SkewHermitianParts.hpart1_skew hsk] at this
  have he : ecOp π X = dOp π X := by
    unfold ecOp
    rw [SkewHermitianParts.hpart1_skew hsk, SkewHermitianParts.hpart2_skew hsk, SkewHermitianParts.dOp_zero, smul_zero, add_zero]
  refine ⟨hL, ?_⟩
  have h2 := representation_exp W k r z π hπ X hL 1
  simp only [Complex.ofReal_one, one_smul] at h2
  rw [h2, ← he, hs.2]

end KLR

open KLR in
theorem lie_group_realization : KLLieGrp := by
  intro Wp Wq _ _ _ _ _ _ k r z z' π π' hz hz' hT hT' hπ hπ' g hg hGG Fr hFr A hA h hh h' hh' hgh
  have hgu := hg.1
  have hgU : IsUnit g.det := WeylGroupFacts.isUnit_of_uh hgu
  have hhU : IsUnit h.det := WeylGroupFacts.isUnit_of_uh hh.1
  have cancel : ∀ M : Mx k r, IsUnit M.det → ∀ v, M⁻¹ *ᵥ (M *ᵥ v) = v := fun M hM v => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM, Matrix.one_mulVec]
  obtain ⟨y, hy⟩ : ∃ y, y = g⁻¹ *ᵥ z := ⟨_, rfl⟩
  rw [← hy] at hFr
  have hgy : g *ᵥ y = z := by rw [hy]; exact Qx8.inv_mulVec_uh hgu z
  have hginv : g⁻¹ ∈ Glev k r (Fin.last r) := FrameEntries.glev_inv hg
  have hyW : inWb k r y := by rw [hy]; exact Qx8.inWb_mulVec hginv hz
  have hyy : herm (Hpk k r) y y = -((Tz k r z : ℝ) : ℂ) := by
    rw [← Qx8.herm_self', ← hgy, Qx8.herm_UH hgu]
  have hζ : herm (Hpk k r) z' y = zetaL k r z z' (Fin.last r) g := by
    unfold zetaL
    rw [Qx8.fvec_last, Qx8.fvec_last, ← hgy, Qx8.herm_UH hgu]
  have hpos := Qx8.GGl_pos hz hz' hT hT' hg hGG
  have hG2 : 0 < Complex.normSq (herm (Hpk k r) y z') - Tz k r z * Tz k r z' := by
    rw [← Qx8.herm_conj, hζ]
    have hc : Complex.normSq (star (zetaL k r z z' (Fin.last r) g)) = Complex.normSq (zetaL k r z z' (Fin.last r) g) :=
      Complex.normSq_conj _
    rw [hc]
    exact hpos
  obtain ⟨e', s, c, hs, he', he'W, he'z, he'e⟩ := Qx8.orth_unit hyW hz' hT' hyy (Qx8.herm_self' z') hG2
  have hFz' : ∀ a, herm (Hpk k r) (Fr a) z' = 0 := fun a => hFr.2.2 a z' (by simp)
  have hFy : ∀ a, herm (Hpk k r) (Fr a) y = 0 := fun a => hFr.2.2 a y (by simp)
  have hFe : ∀ a, herm (Hpk k r) (Fr a) e' = 0 := by
    intro a
    rw [he', Qx8.herm_smul_right', Qx8.herm_add_right', Qx8.herm_smul_right', hFy, hFz']
    simp
  have hFr2 : IsFrameOf k r [z', e'] Fr := ⟨hFr.1, hFr.2.1, fun a v hv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hFz' a
    · exact hFe a⟩
  have hFz'1 : IsFrameOf k r [z'] Fr := ⟨hFr.1, hFr.2.1, fun a v hv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    subst hv
    exact hFz' a⟩

  have e1 : h *ᵥ (g *ᵥ (h' *ᵥ y)) = h *ᵥ z := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hgh, hgy, hh.2.2]
  have e2 : g *ᵥ (h' *ᵥ y) = z := by
    rw [← cancel h hhU (g *ᵥ (h' *ᵥ y)), e1, cancel h hhU z]
  have hh'y : h' *ᵥ y = y := by
    calc h' *ᵥ y = g⁻¹ *ᵥ (g *ᵥ (h' *ᵥ y)) := (cancel g hgU _).symm
      _ = y := by rw [e2, hy]
  have hh'e : h' *ᵥ e' = e' := by
    rw [he', Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, hh'y, hh'.2.2]

  obtain ⟨B, hBs, hBe⟩ := KLG.stab_exp hz' hT' he'W he'z he'e hFr2 hh' hh'e
  rw [KLG.sum_unitB] at hBe
  obtain ⟨-, hE'⟩ := pi_exp_frame hπ' hFz'1 B hBs
  have hgF : IsFrameOf k r [z] (fun a => g *ᵥ Fr a) := ⟨fun a => Qx8.inWb_mulVec hg (hFr.1 a), fun a b => by
    rw [Qx8.herm_UH hgu]; exact hFr.2.1 a b, fun a v hv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    subst hv
    rw [← hgy, Qx8.herm_UH hgu]
    exact hFy a⟩
  obtain ⟨hL, hE⟩ := pi_exp_frame hπ hgF B hBs
  have hconj : g * h' * g⁻¹ = NormedSpace.exp
      (∑ p : Fin (k - 1) × Fin (k - 1), B p.1 p.2 • unitB (Hpk k r) (fun a => g *ᵥ Fr a) p.1 p.2) := by
    have hsum : (∑ p : Fin (k - 1) × Fin (k - 1), B p.1 p.2 • unitB (Hpk k r) (fun a => g *ᵥ Fr a) p.1 p.2) =
        g * (∑ p : Fin (k - 1) × Fin (k - 1), B p.1 p.2 • unitB (Hpk k r) Fr p.1 p.2) * g⁻¹ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul, Qx8.unitB_conj Fr p.1 p.2 hgu]
    rw [hsum, ← hBe]
    exact (exp_conj hgU _).symm
  have hD : A.comp (∑ p : Fin (k - 1) × Fin (k - 1), B p.1 p.2 • ecOp π' (unitB (Hpk k r) Fr p.1 p.2)) =
      (∑ p : Fin (k - 1) × Fin (k - 1), B p.1 p.2 • ecOp π (unitB (Hpk k r) (fun a => g *ᵥ Fr a) p.1 p.2)).comp A := by
    ext v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      map_sum, map_smul]
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
    exact hA p.1 p.2 v
  have hX := exp_intertwine A _ _ hD
  rw [← hE', ← hE, hBe, ← hconj] at hX
  have hmem : g * h' * g⁻¹ ∈ UWset k r z := by
    rw [hconj]
    have := exp_uw hL 1
    simpa using this
  have hone : h * (g * h' * g⁻¹) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hgh, Matrix.mul_nonsing_inv _ hgU]
  rw [hX, ← ContinuousLinearMap.comp_assoc, ← hπ.1.2 h hh _ hmem, hone, hπ.1.1]
  ext v
  simp

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeGRawSmooth
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem raw_gauge_smoothness_holds : GRawSmooth := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl _ e he Dc Φ hF ρ
  obtain ⟨-, -, hM, hS, -⟩ := hF
  have hT : Tz P.k P.r Bs.z = P.T := hpl.2.2.2.1
  have hT' : Tz P.k P.r Bs.z' = P.T' := hpl.2.2.2.2.1
  set Qs := MA.Qset P.r P.TT with hQs
  have hζ : ∀ x ∈ Qs, Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq x.2 := by
    intro x hx
    rw [hT, hT']
    exact hx.2
  have hmZ : ContDiffOn ℝ ∞ (fun x : MA.E P.r => NF.muZ P.k P.r Bs.μsec x.2) Qs :=
    (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_contDiffOn Bs.sec).comp contDiff_snd.contDiffOn fun x hx => hζ x hx
  have hm : ContDiffOn ℝ ∞ (fun x : MA.E P.r => (x.1, NF.muZ P.k P.r Bs.μsec x.2)) Qs :=
    contDiffOn_fst.prodMk hmZ
  have hGl : ∀ x ∈ Qs, NF.muZ P.k P.r Bs.μsec x.2 ∈ Q.Glev P.k P.r (Fin.last P.r) := fun x hx =>
    Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_uwb Bs.sec (hζ x hx))
  have hU0 : ∀ x ∈ Qs, (x.1, NF.muZ P.k P.r Bs.μsec x.2) ∈
      {y : (Fin P.r → ℂ) × Q.Mx P.k P.r | y.1 ∈ OmX P.r ∧ y.2 ∈ Dc y.1} :=
    fun x hx => ⟨hx.1, hM ⟨x, hx⟩⟩
  have hΦq : ContDiffOn ℝ ∞ (fun x : MA.E P.r => Φ x.1 (NF.muZ P.k P.r Bs.μsec x.2)) Qs := by
    refine contDiffOn_of_locally_contDiffOn fun x₀ hx₀ => ?_
    obtain ⟨U, F, hU, hx₀U, hF, hΦF⟩ := hS _ (hU0 x₀ hx₀) (hGl x₀ hx₀)
    refine ⟨Qs ∩ (fun x : MA.E P.r => (x.1, NF.muZ P.k P.r Bs.μsec x.2)) ⁻¹' U,
      hm.continuousOn.isOpen_inter_preimage (MA.Qset_open P.r P.TT) hU, ⟨hx₀, hx₀U⟩, ?_⟩
    have hc : ContDiffOn ℝ ∞ (fun x : MA.E P.r => F (x.1, NF.muZ P.k P.r Bs.μsec x.2))
        (Qs ∩ (Qs ∩ (fun x : MA.E P.r => (x.1, NF.muZ P.k P.r Bs.μsec x.2)) ⁻¹' U)) :=
      hF.comp (hm.mono fun x hx => hx.1) fun x hx => hx.2.2
    exact hc.congr fun x hx => hΦF _ hx.2.2 (hGl x hx.1)
  have he' : ContDiffOn ℝ ∞ (fun x : MA.E P.r => e ρ x.2) Qs :=
    (he.1 ρ).comp contDiff_snd.contDiffOn fun x hx => hx.2
  have hw : ContDiffOn ℝ ∞ (fun x : MA.E P.r => ((wR P.k P.TT x.2 : ℝ) : ℂ)) Qs := by
    refine Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_ofReal ?_
    unfold wR
    refine (((Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_normSq.comp contDiff_snd).sub contDiff_const).pow _).contDiffOn.sqrt
      fun x hx => ?_
    have h2 : P.TT < Complex.normSq x.2 := hx.2
    exact (pow_pos (show (0 : ℝ) < Complex.normSq x.2 - P.TT by linarith) _).ne'
  have hin : ContDiffOn ℝ ∞ (fun x : MA.E P.r =>
      inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (Φ x.1 (NF.muZ P.k P.r Bs.μsec x.2)))) Qs :=
    (Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.comp_contDiffOn he').inner ℂ
      (Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.comp_contDiffOn hΦq)
  have hall := hw.mul hin
  show ContDiffOn ℝ MA.sm (MA.ext _) Qs
  refine hall.congr fun x hx => ?_
  exact dif_pos hx

end Formalism.FourierDecayAlt.P.CutMP.Gauge
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLinesCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL

noncomputable section

def GLRight : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → Gauge.IsFrameB P Bs e →
    (∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Φ →
      ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
        MA.toSm P (Gauge.rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
          MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ) →
    ∀ ζ : ℂ, P.TT < Complex.normSq ζ → ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ,
      Q.IsFrameOf P.k P.r [(NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Bs.z, Bs.z'] Fr →
    ∀ X ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, ∀ (Y : ℝ) (X' : Wq →L[ℂ] Wp),
      (∀ v, X' v = X (Q.capRep P.k P.r Bs.π' Fr ((Y : ℂ) + ((P.k : ℂ) - 2) / 2) v)) →
      ∀ ρ : M.Ty P, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X') = M.xC P ρ (Y : ℂ) * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X)

def GLLeft : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ ζ : ℂ, P.TT < Complex.normSq ζ → ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ,
      Q.IsFrameOf P.k P.r [Bs.z, SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ] Fr →
      Q.IsFrameOf P.k P.r [(NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Bs.z, Bs.z'] (fun a => (NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Fr a) ∧
      ∀ X ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, ∀ (w : ℂ) (v : Wq),
        Q.capRep P.k P.r Bs.π Fr w (X v) =
          X (Q.capRep P.k P.r Bs.π' (fun a => (NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Fr a) w v)

def GaugeLinesOfCut : Prop := GLRight → GLLeft → GaugeLines

end

end Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoLagrange
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut

open Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

namespace LagrangeInterpolation

theorem aeval_eig {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (C : E →L[ℂ] E) (d : ℂ) (v : E)
    (hv : C v = d • v) (p : Polynomial ℂ) : Polynomial.aeval C p v = p.eval d • v := by
  have hpow : ∀ n : ℕ, (C ^ n) v = d ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_smul, hv, smul_smul, pow_succ]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), ContinuousLinearMap.add_apply, hp, hq, Polynomial.eval_add, add_smul]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, ContinuousLinearMap.mul_apply, hpow,
      Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_smul]

def lagP {ι κ : Type*} (c : ι → ℂ) (d : κ → ℂ) (bad : ι → Finset κ) (ρ : ι) : Polynomial ℂ :=
  ∏ σ ∈ bad ρ, (Polynomial.C (c ρ - d σ)⁻¹ * (Polynomial.X - Polynomial.C (d σ)))

theorem lagrangePoly_eval_eq_zero_of_mem {ι κ : Type*} (c : ι → ℂ) (d : κ → ℂ) (bad : ι → Finset κ) {ρ : ι} {σ : κ}
    (hb : σ ∈ bad ρ) : (lagP c d bad ρ).eval (d σ) = 0 := by
  rw [lagP, Polynomial.eval_prod]
  exact Finset.prod_eq_zero hb (by simp)

theorem lagrangePoly_eval_eq_one {ι κ : Type*} (c : ι → ℂ) (d : κ → ℂ) (bad : ι → Finset κ) {ρ : ι} {σ : κ}
    (h : d σ = c ρ) (hne : ∀ τ ∈ bad ρ, d τ ≠ c ρ) : (lagP c d bad ρ).eval (d σ) = 1 := by
  rw [lagP, Polynomial.eval_prod]
  refine Finset.prod_eq_one fun τ hτ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  rw [h]
  exact inv_mul_cancel₀ (sub_ne_zero.mpr (hne τ hτ).symm)

def qP (P : M.Par) (ρ : M.Ty P) : Polynomial ℂ :=
  ∏ i ∈ Finset.Icc 1 (P.k - 1), (Polynomial.X + Polynomial.C ((M.rho P ρ i : ℝ) : ℂ))

theorem eval_qP (P : M.Par) (ρ : M.Ty P) (Y : ℂ) : (qP P ρ).eval Y = M.xC P ρ Y := by
  rw [qP, Polynomial.eval_prod]
  simp [M.xC]

theorem generic (P : M.Par) : ∃ Y : ℂ, ∀ (ρ : M.Ty P) (σ : M.Ty (Qx8.P2 P)),
    (∃ Y', M.xC (Qx8.P2 P) σ Y' ≠ M.xC P ρ Y') → M.xC (Qx8.P2 P) σ Y ≠ M.xC P ρ Y := by
  classical
  let D : Polynomial ℂ := ∏ ρ : M.Ty P, ∏ σ : M.Ty (Qx8.P2 P),
    (if qP (Qx8.P2 P) σ = qP P ρ then 1 else qP (Qx8.P2 P) σ - qP P ρ)
  have hD : D ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun ρ _ => Finset.prod_ne_zero_iff.mpr fun σ _ => ?_
    split_ifs with h
    · exact one_ne_zero
    · exact sub_ne_zero.mpr h
  obtain ⟨Y, hY⟩ : ∃ Y, D.eval Y ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hD (Polynomial.funext fun y => by rw [hcon y, Polynomial.eval_zero])
  refine ⟨Y, fun ρ σ hex hEq => ?_⟩
  obtain ⟨Y', hY'⟩ := hex
  have hne : qP (Qx8.P2 P) σ ≠ qP P ρ := fun h => hY' (by rw [← eval_qP, ← eval_qP, h])
  apply hY
  rw [Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ ρ) ?_
  rw [Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ σ) ?_
  rw [if_neg hne, Polynomial.eval_sub, eval_qP, eval_qP, hEq, sub_self]

end LagrangeInterpolation

open LagrangeInterpolation in
theorem lagrange_annihilation : Lagrange := by
  classical
  intro hE P hOK hk
  have hOK2 : (Qx8.P2 P).OK := by
    unfold Qx8.P2
    refine ⟨hOK.k_pos, hOK.T_pos, hOK.T'_pos, hOK.int_u, hOK.int_u, fun i hmem => ?_⟩
    have g := hOK.gap i hmem
    simp only [M.Par.lo, M.Par.hi, max_self, min_self] at g ⊢
    linarith [le_max_left (P.u (i + 1)) (P.u' (i + 1)), min_le_left (P.u i) (P.u' i)]
  obtain ⟨Y, hY⟩ := generic P
  refine ⟨Y + ((P.k : ℂ) - 2) / 2, fun ρ => lagP (fun ρ => M.xC P ρ Y) (fun σ => M.xC (Qx8.P2 P) σ Y)
    (fun ρ => Finset.univ.filter fun σ => M.xC (Qx8.P2 P) σ Y ≠ M.xC P ρ Y) ρ, ?_⟩
  intro Wp _ _ _ z e π hz hT hπ he hez hee Fr hFr C hC ρ
  obtain ⟨S, hSi, -, hSc⟩ := branching_proof Wp (Qx8.P2 P) hOK2 rfl z e π hz hT hπ he hez hee
  have hSv : ∀ σ, ∀ v ∈ S σ, ∀ Fr' : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ, IsFrameOf P.k P.r [z, e] Fr' →
      ∀ w', capRep P.k P.r π Fr' w' v = M.xC (Qx8.P2 P) σ (w' - ((P.k : ℂ) - 2) / 2) • v :=
    fun σ v hv Fr' hFr' w' => hSc Fr' hFr' σ w' v hv
  have hCv : ∀ σ, ∀ v ∈ S σ, C v = M.xC (Qx8.P2 P) σ Y • v := by
    intro σ v hv
    rw [hC, hSv σ v hv Fr hFr, add_sub_cancel_right]
  have hKs : ∀ σ, ∀ v ∈ S σ,
      v ∈ Kset P.k P.r z e π (fun w' => M.xC (Qx8.P2 P) σ (w' - ((P.k : ℂ) - 2) / 2)) :=
    fun σ v hv Fr' hFr' w' => hSv σ v hv Fr' hFr' w'
  have hRep : Qr.IsRepW P.k P.r z π := ⟨hπ.2.1, hπ.2.2.1⟩
  have hOrth : ∀ σ, M.xC (Qx8.P2 P) σ Y ≠ M.xC P ρ Y → ∀ v ∈ S σ,
      v ∈ (K P.k P.r z e π (fun w' => M.xC P ρ (w' - ((P.k : ℂ) - 2) / 2)))ᗮ := by
    intro σ hne v hv
    rw [Submodule.mem_orthogonal]
    intro u hu
    refine Submodule.span_induction (fun x hx => ?_) ?_ (fun x y _ _ hx hy => ?_) (fun a x _ hx => ?_) hu
    · exact hE Wp P.k P.r z e π hz hT hRep hπ.2.2.2.1 ⟨Fr, hFr⟩ _ _ x v hx (hKs σ v hv)
        ⟨Y + ((P.k : ℂ) - 2) / 2, by simpa using hne.symm⟩
    · exact inner_zero_left _
    · rw [inner_add_left, hx, hy, add_zero]
    · rw [inner_smul_left, hx, mul_zero]
  have hIn : ∀ σ, M.xC (Qx8.P2 P) σ Y = M.xC P ρ Y → ∀ v ∈ S σ,
      v ∈ K P.k P.r z e π (fun w' => M.xC P ρ (w' - ((P.k : ℂ) - 2) / 2)) := by
    intro σ heq v hv
    have hfun : ∀ Y', M.xC (Qx8.P2 P) σ Y' = M.xC P ρ Y' := by
      by_contra hc
      push_neg at hc
      exact hY ρ σ hc heq
    refine Submodule.subset_span (fun Fr' hFr' w' => ?_)
    show capRep P.k P.r π Fr' w' v = M.xC P ρ (w' - ((P.k : ℂ) - 2) / 2) • v
    rw [hSv σ v hv Fr' hFr' w', hfun]
  ext v
  have hv : v ∈ ⨆ σ, S σ := by
    rw [hSi.submodule_iSup_eq_top]
    exact Submodule.mem_top
  refine Submodule.iSup_induction S (motive := fun x =>
    (Polynomial.aeval C) (lagP (fun ρ => M.xC P ρ Y) (fun σ => M.xC (Qx8.P2 P) σ Y)
      (fun ρ => Finset.univ.filter fun σ => M.xC (Qx8.P2 P) σ Y ≠ M.xC P ρ Y) ρ) x =
    (K P.k P.r z e π (fun w' => M.xC P ρ (w' - ((P.k : ℂ) - 2) / 2))).starProjection x) hv ?_ ?_ ?_
  · intro σ x hx
    rw [aeval_eig C _ x (hCv σ x hx)]
    by_cases hb : M.xC (Qx8.P2 P) σ Y = M.xC P ρ Y
    · rw [lagrangePoly_eval_eq_one (fun ρ => M.xC P ρ Y) (fun σ => M.xC (Qx8.P2 P) σ Y)
        (fun ρ => Finset.univ.filter fun σ => M.xC (Qx8.P2 P) σ Y ≠ M.xC P ρ Y) hb (fun τ hτ => (Finset.mem_filter.mp hτ).2), one_smul]
      exact ((Submodule.starProjection_eq_self_iff).mpr (hIn σ hb x hx)).symm
    · rw [lagrangePoly_eval_eq_zero_of_mem (fun ρ => M.xC P ρ Y) (fun σ => M.xC (Qx8.P2 P) σ Y)
        (fun ρ => Finset.univ.filter fun σ => M.xC (Qx8.P2 P) σ Y ≠ M.xC P ρ Y) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩), zero_smul]
      exact ((Submodule.starProjection_apply_eq_zero_iff _).mpr (hOrth σ hb x hx)).symm
  · simp only [map_zero]
  · intro x y hx hy
    rw [map_add (f := _), map_add (f := _), hx, hy]

end Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThConstS
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC

noncomputable section

def PolyRadialS : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ S, IsSSPt P Bs d l S →
    ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∀ π ρ : M.Ty P, M.Up P l π ρ → ∃ (n : ℕ) (q : Polynomial ℂ), ∀ ζ ∈ Gauge.GC.Ann P,
      ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
        (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf →
        (((Complex.normSq ζ - P.TT : ℝ) : ℂ) ^ n) • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Xf) =
          q.eval ((Real.sqrt (Complex.normSq ζ - P.TT) : ℝ) : ℂ) • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp
            (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf)

def ThConstOfCutS : Prop := PolyRadialS → ModConst → LineNonzero → PolyFinish → ThConst

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC
end

