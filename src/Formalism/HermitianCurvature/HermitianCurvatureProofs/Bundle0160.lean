module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0041
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0157
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0074
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0093
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0069
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0156
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NfRadOrder0OfRadRed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0102
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0129
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0155

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutAsm
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

section asm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem isBuiltPlace_mono {Cc₁ Cc₂ : ℝ} (h : Cc₁ ≤ Cc₂) {S : C.HidaSetting E Wp Wq}
    {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ}
    {ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ} {m₀ : Fin S.f → B.Mat S.G.k S.G.r}
    {top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ}
    {A₀ : ℝ} (hB : JCT.IsBuiltPlace Cc₂ S T f χ ν' m₀ top A₀) : JCT.IsBuiltPlace Cc₁ S T f χ ν' m₀ top A₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hB
  refine ⟨h1, h2, h3, h4, h5, h6, h7, fun v => le_trans ?_ (h8 v), le_trans h h9, h10, h11, le_trans ?_ h12, h13⟩
  · exact mul_le_mul_of_nonneg_right h (by positivity)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (by positivity)) (by positivity)

theorem toSm_smul (P : M.Par) (c : ℂ) (u : MA.Qp P.r P.TT → ℂ) : MA.toSm P (c • u) = c • MA.toSm P u := by
  unfold Formalism.FourierDecayAlt.MA.toSm
  by_cases hu : u ∈ MA.smSub P.r P.TT
  · rw [dite_eq_left hu, dite_eq_left (Subalgebra.smul_mem _ hu c)]
    rfl
  · rw [dite_eq_right hu, smul_zero]
    by_cases hc : c = 0
    · subst hc
      rw [dite_eq_left (by rw [zero_smul]; exact Subalgebra.zero_mem _)]
      exact Subtype.ext (by simp)
    · rw [dite_eq_right]
      intro h
      apply hu
      have h2 := Subalgebra.smul_mem _ h c⁻¹
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2

theorem hsVec_smul {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (c : ℂ) (A : W →L[ℂ] V) : B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  rfl

theorem trJ_smul (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (c : ℂ) (J : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) :
    trJ S T v e (c • J) = c • trJ S T v e J := by
  funext ρ
  simp only [trJ, Pi.smul_apply, hsVec_smul, inner_smul_right]
  rw [← toSm_smul]
  congr 1
  funext q
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem trJ_congr (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (J J' : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (h : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, J (B.gq (T v).base x) = J' (B.gq (T v).base x)) :
    trJ S T v e J = trJ S T v e J' := by
  funext ρ
  simp only [trJ]
  congr 1
  funext q
  rw [h q.1 q.2]

def prFst (P : M.Par) : (MA.DQ P).Pr →+ (MA.DQ P).Op where
  toFun p := p.1
  map_zero' := rfl
  map_add' _ _ := rfl

theorem pr_fst_sum (P : M.Par) {ι : Type} (s : Finset ι) (g : ι → (MA.DQ P).Pr) :
    (∑ i ∈ s, g i).1 = ∑ i ∈ s, (g i).1 := by
  exact map_sum (prFst P) g s

theorem pr_fst_smul (P : M.Par) (c : ℂ) (a : (MA.DQ P).Pr) : (c • a).1 = c • a.1 := by
  rfl

theorem op_sum_apply (P : M.Par) {ι : Type} (s : Finset ι) (g : ι → (MA.DQ P).Op) (y : (MA.DQ P).R) :
    (∑ i ∈ s, g i) y = ∑ i ∈ s, g i y := by
  first
  | exact LinearMap.sum_apply s g y
  | exact ContinuousLinearMap.sum_apply s g y
  | simp

theorem actA_mul (P : M.Par) (a b : MA.A P (MA.DQ P)) (x : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (a * b) x = MA.actA P a (MA.actA P b x) := by
  funext π
  show ∑ π', ((a * b) π π').1 (x π') = ∑ σ, (a π σ).1 (∑ π', (b σ π').1 (x π'))
  have e : ∀ π', ((a * b) π π').1 (x π') = ∑ i, (a π i).1 ((b i π').1 (x π')) := by
    intro π'
    rw [Matrix.mul_apply, pr_fst_sum]
    first
      | exact (LinearMap.sum_apply _ _ _).trans (Finset.sum_congr rfl fun i _ => rfl)
      | exact (ContinuousLinearMap.sum_apply _ _ _).trans (Finset.sum_congr rfl fun i _ => rfl)
      | exact (op_sum_apply P Finset.univ _ _).trans (Finset.sum_congr rfl fun i _ => rfl)
      | (simp; rfl)
  rw [Finset.sum_congr rfl fun π' _ => e π', Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]

theorem actA_smul (P : M.Par) (c : ℂ) (a : MA.A P (MA.DQ P)) (x : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (c • a) x = c • MA.actA P a x := by
  funext π
  simp only [Formalism.FourierDecayAlt.MA.actA, Matrix.smul_apply, pr_fst_smul, Pi.smul_apply]
  rw [eq_comm]
  erw [Finset.smul_sum]
  symm
  refine Finset.sum_congr rfl fun π' _ => ?_
  first
    | exact LinearMap.smul_apply _ _ _
    | exact ContinuousLinearMap.smul_apply _ _ _
    | rfl

theorem actA_one (P : M.Par) (x : M.Ty P → MA.SmQ P.r P.TT) : MA.actA P 1 x = x := by
  classical
  funext π
  simp only [Formalism.FourierDecayAlt.MA.actA, Matrix.one_apply]
  erw [Finset.sum_eq_single π (fun b _ hb => by simp only [if_neg (Ne.symm hb)]; rfl)
    (fun h => absurd (Finset.mem_univ π) h)]
  simp only [if_pos rfl]
  rfl

theorem initial_coefficient_of_start_matrix (P : M.Par) (l : ℕ) (Y : ℂ) :
    Wd.C0 (MA.startM P (MA.DQ P) l).QQ (MA.sites P (MA.DQ P)) Y =
      M.sgn P l • Wd.C0 (MA.QQr P (MA.DQ P)) (MA.sites P (MA.DQ P)) Y := by
  simp only [Formalism.FourierDecayAlt.Wd.C0, Formalism.FourierDecayAlt.MA.startM, Matrix.smul_apply, smul_mul_assoc, mul_smul_comm,
    Finset.smul_sum]

end asm

section main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem trJ_foldr (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (hG : IsGauge S T v e)
    (hP : ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v), ∀ (Y : ℝ) (s : ℂ), s • Q.CV S.G.k S.G.r (Y : ℂ) J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)) :
    ∀ (L : List (Bool × ℝ)) (J₀ : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), J₀ ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
      L.foldr (fun x J => M.sgn (D.parOf S v) (S.l + 1) • Q.CV S.G.k S.G.r (x.2 : ℂ) J) J₀ ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) ∧
      trJ S T v e (L.foldr (fun x J => M.sgn (D.parOf S v) (S.l + 1) • Q.CV S.G.k S.G.r (x.2 : ℂ) J) J₀) =
        MA.actA (D.parOf S v) ((L.map fun x => Wd.C0 (MA.startM (D.parOf S v) (MA.DQ (D.parOf S v)) (S.l + 1)).QQ
          (MA.sites (D.parOf S v) (MA.DQ (D.parOf S v))) (x.2 : ℂ)).prod) (trJ S T v e J₀) := by
  intro L J₀ hJ₀
  induction L with
  | nil =>
    refine ⟨hJ₀, ?_⟩
    simp only [List.foldr_nil, List.map_nil, List.prod_nil]
    rw [actA_one]
  | cons x L ih =>
    obtain ⟨hmem, htr⟩ := ih
    refine ⟨hP _ hmem x.2 _, ?_⟩
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    rw [trJ_smul, hG _ hmem x.2, ← actA_smul, ← initial_coefficient_of_start_matrix, htr, ← actA_mul]

end main

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLMat
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem wRc_smooth (P : M.Par) : ContDiffOn ℝ ∞ (fun ζ : ℂ => ((wR P.k P.TT ζ : ℝ) : ℂ)) (Ann P) := by
  have h1 : ContDiffOn ℝ ∞ (fun ζ : ℂ => (Complex.normSq ζ - P.TT) ^ (P.k - 1)) (Ann P) := by
    have h2 : ContDiff ℝ ∞ (fun ζ : ℂ => Complex.normSq ζ) := by
      have h3 : (fun ζ : ℂ => Complex.normSq ζ) = fun ζ : ℂ => ‖ζ‖ ^ 2 := by
        funext ζ
        rw [Complex.normSq_eq_norm_sq]
      rw [h3]
      exact contDiff_norm_sq ℝ
    exact ((h2.sub contDiff_const).pow _).contDiffOn
  have h4 : ContDiffOn ℝ ∞ (fun ζ : ℂ => wR P.k P.TT ζ) (Ann P) := by
    unfold wR
    refine h1.sqrt fun ζ hζ => ?_
    have h5 : P.TT < Complex.normSq ζ := hζ
    exact (pow_pos (by linarith) _).ne'
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn h4

theorem wRc_ne (P : M.Par) {ζ : ℂ} (hζ : ζ ∈ Ann P) : ((wR P.k P.TT ζ : ℝ) : ℂ) ≠ 0 := by
  have h5 : P.TT < Complex.normSq ζ := hζ
  have h6 : 0 < wR P.k P.TT ζ := by
    unfold wR
    exact Real.sqrt_pos.mpr (pow_pos (by linarith) _)
  exact_mod_cast h6.ne'

section mat

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem tz_TT (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') :
    Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by
  rw [hpl.2.2.2.1, hpl.2.2.2.2.1]
  rfl

theorem radBase_of (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') :
    NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
  exact ⟨Bs.k_pos, Bs.z_mem, Bs.z'_mem, Bs.T_pos, Bs.T'_pos, Bs.sec, Bs.π_rep, Bs.π'_rep, Bs.π_cont,
    Bs.π'_cont⟩

theorem slice_smooth (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) {c : Fin P.r → ℂ} (hc : c ∈ OmX P.r) :
    ContDiffOn ℝ ∞ (fun ζ => inner ℂ (B.hsVec (e ρ ζ))
      (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)))) (Ann P) := by
  have hm : ContDiffOn ℝ ∞ (MA.ext (rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ)) (MA.Qset P.r P.TT) :=
    radial_space_smoothness Wp Wq P Bs hpl hk e he Φ ρ
  have h1 : ContDiffOn ℝ ∞ (fun ζ : ℂ => MA.ext (rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ) (c, ζ))
      (Ann P) :=
    hm.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun ζ hζ => ⟨hc, hζ⟩)
  refine (Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_div h1 (wRc_smooth P) fun ζ hζ => wRc_ne P hζ).congr fun ζ hζ => ?_
  have hq : ((c, ζ) : MA.E P.r) ∈ MA.Qset P.r P.TT := ⟨hc, hζ⟩
  simp only [MA.ext, dif_pos hq, rawR]
  rw [mul_div_cancel_left₀ _ (wRc_ne P hζ)]

theorem key_slice (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e)
    (Ψ : M.Ty P → Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (hΨ : ∀ ρ, ∀ c ∈ OmX P.r, ∀ ζ ∈ Ann P,
      (Ψ ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = e ρ ζ)
    (T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (hT : SliceLoc P Bs T)
    (hC : ∀ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {ζ | P.TT < Complex.normSq ζ} →
      ∀ W : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), NF.IsMulZ W f → Commute T W)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') {c c0 : Fin P.r → ℂ} (hc : c ∈ OmX P.r) (hc0 : c0 ∈ OmX P.r)
    {ζ : ℂ} (hζ : ζ ∈ Ann P) :
    (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) =
      ∑ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ))) •
        (T (Ψ ρ) : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ) := by
  have hTz := tz_TT P Bs hpl
  have hRB := radBase_of P Bs hpl
  let F : M.Ty P → ℂ → ℂ := fun ρ ζ' => inner ℂ (B.hsVec (e ρ ζ'))
    (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ')))
  have hFs : ∀ ρ, ContDiffOn ℝ ∞ (F ρ) {ζ | P.TT < Complex.normSq ζ} := fun ρ =>
    slice_smooth P Bs hpl hk e he Φ ρ hc
  choose W hW using fun ρ => Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl (F ρ) (hFs ρ)
  have hQR : ∀ c' ∈ OmX P.r, ∀ ζ' ∈ Ann P, ((c', ζ') : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' :=
    fun c' hc' ζ' hζ' => ⟨hc', by rw [hTz]; exact hζ'⟩
  have hmul : ∀ (ρ : M.Ty P) (Θ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), ∀ c' ∈ OmX P.r, ∀ ζ' ∈ Ann P,
      ((W ρ Θ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' (NF.muZ P.k P.r Bs.μsec ζ') =
        F ρ ζ' • (Θ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' (NF.muZ P.k P.r Bs.μsec ζ') := by
    intro ρ Θ c' hc' ζ' hζ'
    have hq := hQR c' hc' ζ' hζ'
    rw [hW ρ Θ]
    have h := Formalism.FourierDecayAlt.P.NFRO.radR_mulZ hRB (F ρ) Θ.2 hq
    simp only [NF.radR, Set.indicator_of_mem hq] at h
    exact h
  let Φc : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := ∑ ρ, W ρ (Ψ ρ)
  have hsumv : ∀ (G : M.Ty P → Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c' : Fin P.r → ℂ) (g : Q.Mx P.k P.r),
      ((∑ ρ, G ρ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' g =
        ∑ ρ, (G ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' g := by
    intro G c' g
    rw [Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]
  have hΦv : ∀ ζ' ∈ Ann P, (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ') =
      (Φc : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ') := by
    intro ζ' hζ'
    have hq := hQR c hc ζ' hζ'
    rw [hsumv]
    have hmem := (Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ Φ.2).2.1 (c, ζ') hq
    simp only [NF.radR, Set.indicator_of_mem hq] at hmem
    rw [(he.2 ζ' hζ').2.2 _ hmem]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [hmul ρ (Ψ ρ) c hc ζ' hζ', hΨ ρ c hc ζ' hζ']
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hT Φ Φc c c hc hc hΦv ζ hζ, map_sum, hsumv]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hcomm : T (W ρ (Ψ ρ)) = W ρ (T (Ψ ρ)) := by
    have h := (hC (F ρ) (hFs ρ) (W ρ) (hW ρ)).eq
    exact LinearMap.congr_fun h (Ψ ρ)
  rw [hcomm, hmul ρ (T (Ψ ρ)) c hc ζ hζ]
  congr 1
  exact hT (Ψ ρ) (Ψ ρ) c c0 hc hc0 (fun ζ' hζ' => by rw [hΨ ρ c hc ζ' hζ', hΨ ρ c0 hc0 ζ' hζ']) ζ hζ

end mat

theorem second_shift_matrix_form : GTSSLMat := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH e he hSL
  obtain ⟨hpl, hk, -, hL, hS, hRel, hQQ⟩ := hH
  have hTz := tz_TT P Bs hpl
  have hRB := radBase_of P Bs hpl
  let c0 : Fin P.r → ℂ := fun _ => 1
  have hc0 : c0 ∈ OmX P.r := fun _ => one_ne_zero
  have hsec : ∀ ρ, ((NF.QR P.k P.r Bs.z Bs.z').indicator fun q : (Fin P.r → ℂ) × ℂ => e ρ q.2) ∈
      NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    intro ρ
    refine ⟨((he.1 ρ).comp contDiff_snd.contDiffOn fun q hq => ?_).congr fun q hq => ?_, fun q hq => ?_,
      fun q hq => ?_⟩
    · show P.TT < Complex.normSq q.2
      rw [← hTz]; exact hq.2
    · simp [Set.indicator_of_mem hq]
    · rw [Set.indicator_of_mem hq]
      exact (he.2 q.2 (by rw [← hTz]; exact hq.2)).1 ρ
    · simp [Set.indicator_of_notMem hq]
  choose Ψ0 hΨ0 hΨr using fun ρ =>
    Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ (hsec ρ)
  let Ψ : M.Ty P → Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := fun ρ => ⟨Ψ0 ρ, hΨ0 ρ⟩
  have hΨ : ∀ ρ, ∀ c ∈ OmX P.r, ∀ ζ ∈ Ann P,
      (Ψ ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = e ρ ζ := by
    intro ρ c hc ζ hζ
    have hq : ((c, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, by rw [hTz]; exact hζ⟩
    have h := congrFun (hΨr ρ) (c, ζ)
    simp only [NF.radR, Set.indicator_of_mem hq] at h
    exact h
  have hCom : ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {ζ | P.TT < Complex.normSq ζ} →
      ∀ W : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), NF.IsMulZ W f →
        Commute (d.SS l).1 W ∧ Commute (star (d.SS l)).1 W := by
    intro l hl f hf W hW
    obtain ⟨W₁, hW₁⟩ := Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl (NF.dZ f)
      (Formalism.FourierDecayAlt.P.NFx4.NO.dZ_smooth (Formalism.FourierDecayAlt.P.NFx4.NO.isOpen_U _) hf)
    obtain ⟨W₂, hW₂⟩ := Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl (NF.dZb f)
      (Formalism.FourierDecayAlt.P.NFx4.NO.dZb_smooth (Formalism.FourierDecayAlt.P.NFx4.NO.isOpen_U _) hf)
    exact (Formalism.FourierDecayAlt.P.normal_form_order_zero Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl X d hL hS hRel hQQ f hf W W₁ W₂
      hW hW₁ hW₂).2.1 l hl
  let ent : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') → M.Ty P → M.Ty P → ℂ → ℂ := fun T ρ' ρ ζ =>
    inner ℂ (B.hsVec (e ρ' ζ)) (B.hsVec ((T (Ψ ρ) : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ)))
  have hent : ∀ T ρ' ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ent T ρ' ρ) (Ann P) := fun T ρ' ρ =>
    slice_smooth P Bs hpl hk e he (T (Ψ ρ)) ρ' hc0
  have hmain : ∀ (T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), SliceLoc P Bs T →
      (∀ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {ζ | P.TT < Complex.normSq ζ} →
        ∀ W : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), NF.IsMulZ W f → Commute T W) →
      ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ' : M.Ty P),
        trR P Bs e (T Φ) ρ' = ∑ ρ, fnZ P (ent T ρ' ρ) * trR P Bs e Φ ρ := by
    intro T hT hC Φ ρ'
    have hv : ∀ (Θ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P),
        ((trR P Bs e Θ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) =
          rawR P Bs.μsec e (Θ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ := fun Θ σ =>
      Formalism.FourierDecayAlt.P.CutMP.En.toSm_val_of_mem P (radial_space_smoothness Wp Wq P Bs hpl hk e he Θ σ)
    apply Subtype.ext
    funext q
    rw [hv]
    rw [show (((∑ ρ, fnZ P (ent T ρ' ρ) * trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q) =
        ∑ ρ, ent T ρ' ρ q.1.2 * rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q by
      rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [MulMemClass.coe_mul, Pi.mul_apply, hv, fnZ_eq_mk P (hent T ρ' ρ)]]
    have hc : q.1.1 ∈ OmX P.r := q.2.1
    have hζ : q.1.2 ∈ Ann P := q.2.2
    simp only [rawR]
    rw [key_slice P Bs hpl hk e he Ψ hΨ T hT hC Φ hc hc0 hζ, Formalism.FourierDecayAlt.P.CutMP.En.hsVec_sum_smul, inner_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [inner_smul_right]
    ring
  refine ⟨fun l => ent (d.SS l).1, fun l => ent (star (d.SS l)).1,
    fun l ρ' ρ => ⟨hent _ ρ' ρ, hent _ ρ' ρ⟩, ?_⟩
  intro l hl Φ ρ'
  exact ⟨hmain _ (hSL l hl).1 (fun f hf W hW => (hCom l hl f hf W hW).1) Φ ρ',
    hmain _ (hSL l hl).2 (fun f hf W hW => (hCom l hl f hf W hW).2) Φ ρ'⟩

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRModelV
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

theorem site_vector_eq_tensor_product (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (hL : MA.IsModelLevel P (MA.DQ P) L)
    (y : ℂ) (b : Fin 2) : Wd.v0 (MA.sites P (MA.DQ P)) y b = L.Tprod y b 0 := by
  obtain ⟨hp, -, hc, hci, -⟩ := hL
  have hT : (fun σ => Wd.Ts σ y) ∘ MA.siteA P (MA.DQ P) = L.Tl y := by
    funext l
    simp only [Function.comp_apply]
    unfold R.LevelData.Tl
    rw [hp, hc, hci]
    rfl
  unfold Wd.v0 MA.sites R.LevelData.Tprod
  rw [List.map_reverse, List.map_ofFn, hT]

theorem star_site_vector_eq_tensor (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (hL : MA.IsModelLevel P (MA.DQ P) L)
    (y : ℂ) (a : Fin 2) :
    star (Wd.v0 (MA.sites P (MA.DQ P)) y a) = L.Tvprod (starRingEnd ℂ y) a 0 := by
  have hL' := hL
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := hL'
  have sp : ∀ l, star (L.p l) = -L.pb l := fun l => by
    rw [hp, hpb]
    show star (MA.sc P (MA.DQ P) ((MA.DQ P).pP l)) = -MA.sc P (MA.DQ P) ((MA.DQ P).pbP l)
    rw [Formalism.FourierDecayAlt.P.MAx3.F.star_sc, Formalism.FourierDecayAlt.P.MAx3.F.star_pP]
    unfold MA.sc
    simp
  have sc : ∀ l, star (L.c l) = L.cb l := fun l => by
    rw [hc, hcb]
    show star (MA.sc P (MA.DQ P) ((MA.DQ P).cP l)) = MA.sc P (MA.DQ P) ((MA.DQ P).cbP l)
    rw [Formalism.FourierDecayAlt.P.MAx3.F.star_sc]
    rfl
  have sci : ∀ l, star (L.ci l) = L.cbi l := fun l => by
    rw [hci, hcbi]
    show star (MA.sc P (MA.DQ P) ((MA.DQ P).ciP l)) = MA.sc P (MA.DQ P) ((MA.DQ P).cbiP l)
    rw [Formalism.FourierDecayAlt.P.MAx3.F.star_sc]
    rfl
  have h := congrArg (fun M => M 0 a) (Formalism.FourierDecayAlt.P.TLB.star_Tprod_gen L sp sc sci y)
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply] at h
  rw [site_vector_eq_tensor_product P L hL y a]
  exact h

theorem mirror_residue_model_holds : JDRModelV := by
  intro P L hL y
  refine ⟨fun b => site_vector_eq_tensor_product P L hL (y : ℂ) b, fun a => ?_⟩
  rw [star_site_vector_eq_tensor P L hL (y : ℂ) a, Complex.conj_ofReal]

end

end Formalism.FourierDecayAlt.P.CutMP
end

