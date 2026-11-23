module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0130
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0043
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0088
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0063
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSConst
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0069
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0093
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0102
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0124
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0129

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CsliceContinuous
section
open Matrix MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Cpt

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem cslice_continuous (c : Fin r → ℂ) : Continuous (fun x : Mt k r => (c, Matrix.of x)) :=
  continuous_const.prodMk continuous_id

theorem int_cpt_gen (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    (Φ Θ : RadSp k r z z' π π') (c : Fin r → ℂ) (v : Wq) (K : Set (Mx k r)) (hKc : IsCompact K)
    (hKG : K ⊆ {g | 0 < GGl k r z z' g}) (hc : c ∈ OmX r)
    (f : Mt k r → ℂ) (hf : (f = fun x => ⟪(Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v,
        (Θ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v⟫_ℂ) ∨
      (f = fun x => ⟪(Θ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v,
        (Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v⟫_ℂ))
    (hΦ0 : ∀ g ∈ Glev k r (Fin.last r), g ∉ K → (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0) :
    Integrable f μ := by
  obtain ⟨s, hs⟩ : ∃ s : Set (Mt k r), s = (fun x : Mt k r => (c, Matrix.of x)) ⁻¹' DomR k r z z' := ⟨_, rfl⟩
  have hsm : MeasurableSet s := by
    rw [hs, DomR_eq, Set.preimage_inter]
    exact ((P.Qx5.isOpen_OpR k r z z').preimage (cslice_continuous c)).measurableSet.inter
      (((P.Qx5.Glev_closed (Fin.last r)).preimage continuous_snd).preimage (cslice_continuous c)).measurableSet
  have hA : ∀ Ξ : RadSp k r z z' π π', ContinuousOn (fun x : Mt k r => (Ξ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v) s := by
    intro Ξ
    have h1 := (radSp_continuousOn Ξ).comp ((cslice_continuous c).continuousOn : ContinuousOn _ s) (fun x hx => by rw [hs] at hx; exact hx)
    exact h1.clm_apply continuousOn_const
  have hcont : ContinuousOn f s := by
    rcases hf with rfl | rfl
    · exact (hA Φ).inner (hA Θ)
    · exact (hA Θ).inner (hA Φ)
  have hzero : ∀ x, (c, Matrix.of x) ∉ DomR k r z z' ∨ Matrix.of x ∉ K → f x = 0 := by
    intro x hx
    have hΦx : (Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) = 0 := by
      rcases hx with hx | hx
      · exact radSp_zero_off Φ (x := (c, Matrix.of x)) hx
      · by_cases hg : Matrix.of x ∈ Glev k r (Fin.last r)
        · exact hΦ0 _ hg hx
        · exact radSp_zero_off Φ (x := (c, Matrix.of x)) (fun h => hg h.2.1)
    rcases hf with h | h
    · subst h
      show ⟪(Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v, (Θ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v⟫_ℂ = 0
      rw [hΦx, _root_.zero_apply, inner_zero_left]
    · subst h
      show ⟪(Θ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v, (Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v⟫_ℂ = 0
      rw [hΦx, _root_.zero_apply, inner_zero_right]
  obtain ⟨C, hC⟩ : ∃ C : Set (Mt k r), C = (fun g : Mx k r => (Matrix.of.symm g : Mt k r)) '' (K ∩ Glev k r (Fin.last r)) :=
    ⟨_, rfl⟩
  have hCmem : ∀ x, x ∈ C ↔ Matrix.of x ∈ K ∧ Matrix.of x ∈ Glev k r (Fin.last r) := by
    intro x
    rw [hC]
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [Matrix.of.apply_symm_apply]
      exact hg
    · intro hx; exact ⟨Matrix.of x, hx, rfl⟩
  have hCc : IsCompact C := by
    rw [hC]
    exact (hKc.inter_right (P.Qx5.Glev_closed _)).image continuous_id
  have hCs : C ⊆ s := by
    intro x hx
    rw [hCmem] at hx
    rw [hs]
    exact ⟨hc, hx.2, hKG hx.1⟩
  obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn (hcont.mono hCs)
  have hmeas : Measurable f := measurable_of_continuousOn_zero hsm hcont (fun x hx => hzero x (Or.inl (by rw [hs] at hx; exact hx)))
  have hbound : ∀ x, ‖f x‖ ≤ C.indicator (fun _ => M) x := by
    intro x
    by_cases hx : x ∈ C
    · rw [Set.indicator_of_mem hx]; exact hM x hx
    · rw [Set.indicator_of_notMem hx]
      have : f x = 0 := by
        apply hzero
        by_cases hd : (c, Matrix.of x) ∈ DomR k r z z'
        · right; intro hK; exact hx ((hCmem x).2 ⟨hK, hd.2.1⟩)
        · left; exact hd
      rw [this, norm_zero]
  refine Integrable.mono' ?_ hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  exact (integrable_indicator_iff hCc.measurableSet).mpr
    (integrableOn_const (hμ.finite_compact C hCc).ne)

end Cpt

section Adj

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem pairAt_t_adj_cpt' (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (hP : IsPlace P z z' π π') (X : ActualOps P.k P.r z z' π π')
    (μ : Measure (Mt P.k P.r)) (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ)
    (Φ Ψ : RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r)
    (hK : ∃ K : Set (Mx P.k P.r), IsCompact K ∧ K ⊆ {g | 0 < GGl P.k P.r z z' g} ∧
      ∀ g ∈ Glev P.k P.r (Fin.last P.r), g ∉ K →
        (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0 ∧ (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0)
    (Y : ℂ) (a b : Fin 2) :
    pairAt μ (X.t Y a b Φ) Ψ c = pairAt μ Φ (X.t (star Y) b a Ψ) c := by
  obtain ⟨K, hKc, hKG, hK0⟩ := hK
  refine pairAt_t_adj_cpt P z z' π π' hP X μ hμ Φ Ψ c hc ⟨K, hKc, hKG, hK0⟩ Y a b (fun m => ?_) (fun m => ?_)
  · exact int_cpt_gen μ hμ Ψ (X.t Y a b Φ) c _ K hKc hKG hc _ (Or.inl rfl) (fun g hg hgK => (hK0 g hg hgK).2)
  · exact int_cpt_gen μ hμ Φ (X.t (star Y) b a Ψ) c _ K hKc hKG hc _ (Or.inr rfl) (fun g hg hgK => (hK0 g hg hgK).1)

end Adj

end Formalism.FourierDecayAlt.P5.HerA
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLinesRight
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL

noncomputable section

theorem gauge_right_line_holds : GLRight := by
  intro Wp Wq _ _ _ _ _ _ P Bs e hpl hk he hQQ ζ hζ Fr hFr X hX Y X' hX' ρ
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hT : 0 < Tz P.k P.r Bs.z := Bs.T_pos
  have hT' : 0 < Tz P.k P.r Bs.z' := Bs.T'_pos
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζ
  set c0 : Fin P.r → ℂ := fun _ => 1 with hc0def
  have hq : ((c0, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨fun _ => one_ne_zero, hζ'⟩
  set g := NF.muZ P.k P.r Bs.μsec ζ with hgdef
  let qq : MA.Qp P.r P.TT := ⟨(c0, ζ), ⟨fun _ => one_ne_zero, hζ⟩⟩
  have hw : 0 < Gauge.wR P.k P.TT ζ := Gauge.GC.SSTr.wR_pos P hζ
  set a : M.Ty P → ℂ := fun σ => ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e σ ζ)) (B.hsVec X) with hadef
  obtain ⟨Φs, -, hΦv⟩ := Gauge.GC.SSTr.exists_tr P Bs hpl hk e he (fun σ => algebraMap ℂ (MA.SmQ P.r P.TT) (a σ))
  set Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp) := (Φs : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) with hΦdef
  have hΦ : Φ ∈ Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := Φs.2
  have hval : Φ c0 g = X := by
    have h1 : Φ c0 g = _ := hΦv qq
    rw [h1]
    conv_rhs => rw [(he.2 ζ hζ).2.2 X hX]
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    have hw' : ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
    show (((Gauge.wR P.k P.TT ζ)⁻¹ : ℝ) : ℂ) * ((algebraMap ℂ (MA.SmQ P.r P.TT) (a σ) : MA.SmQ P.r P.TT) :
      MA.Qp P.r P.TT → ℂ) qq = _
    simp only [hadef, Subalgebra.coe_algebraMap, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    push_cast
    field_simp
  have hx : (c0, g) ∈ Q.DomR P.k P.r Bs.z Bs.z' := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq

  set Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r) := fun _ => Formalism.FourierDecayAlt.P.Qx5.Dp P.k P.r Bs.z Bs.z' with hDc
  have hFam : Gauge.FamR P Bs Dc Φ := by
    refine ⟨?_, fun c _ => Formalism.FourierDecayAlt.P.Qx5.Dp_dom P.k P.r Bs.z Bs.z', fun q => ?_, ?_,
      fun c hc => Formalism.FourierDecayAlt.P.Qx5.slice_FF hz hz' hΦ hc⟩
    · have h1 : IsOpen {x : (Fin P.r → ℂ) × Q.Mx P.k P.r | x.1 ∈ OmX P.r} := by
        have : IsOpen (OmX P.r) := by
          have e : OmX P.r = ⋂ l, {x : Fin P.r → ℂ | x l ≠ 0} := by ext x; simp [OmX]
          rw [e]
          exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
        exact this.preimage continuous_fst
      have h2 : IsOpen {x : (Fin P.r → ℂ) × Q.Mx P.k P.r | 0 < Q.GGl P.k P.r Bs.z Bs.z' x.2} :=
        isOpen_lt continuous_const ((Formalism.FourierDecayAlt.P.Qx5.GGl_continuous P.k P.r Bs.z Bs.z').comp continuous_snd)
      exact h1.inter h2
    · have hq' : ((q.1.1, q.1.2) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' :=
        ⟨q.2.1, by rw [hTz, hTz']; exact q.2.2⟩
      exact (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq').2.2
    · intro x₀ hx₀ hgl
      exact hΦ.2.1 x₀ ⟨hx₀.1, hgl, hx₀.2⟩
  have hG := hQQ Dc Φ hFam Y 1 1 ρ
  have hs1 := Gauge.raw_gauge_smoothness_holds Wp Wq P Bs hpl hk e he Dc _
    (Gauge.quadratic_local_family_holds Wp Wq P Bs hpl hk Dc Φ hFam Y 1 1) ρ
  have hs0 := Gauge.raw_gauge_smoothness_holds Wp Wq P Bs hpl hk e he Dc Φ hFam ρ

  have hQ11 : MA.QQr P (MA.DQ P) (Y : ℂ) 1 1 = MA.ggA P (MA.DQ P) * MA.xA P (MA.DQ P) (Y : ℂ) := rfl
  rw [hQ11, Gauge.actA_mul, MA.ggA, Gauge.GC.SSC.actA_sc, MA.xA] at hG
  have hev := congrArg (fun s : MA.SmQ P.r P.TT => (s : MA.Qp P.r P.TT → ℂ) qq) hG
  rw [Gauge.GC.toSm_of_mem P hs1, Gauge.GC.actA_kap] at hev
  have hw' : ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  have hGGv : Q.GGl P.k P.r Bs.z Bs.z' g = Complex.normSq ζ - P.TT := by
    unfold Q.GGl
    rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hz hz' Bs.sec hζ', hTz, hTz']
    rfl
  have hGG0 : ((Complex.normSq ζ - P.TT : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Complex.normSq ζ - P.TT := by linarith
    exact_mod_cast this.ne'
  have hsm : ∀ (c : ℂ) (A : Wq →L[ℂ] Wp), B.hsVec (c • A) = c • B.hsVec A := by
    intro c A; ext i; simp [B.hsVec]
  have hQLg : Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) 1 1 Φ c0 g =
      (((Complex.normSq ζ - P.TT : ℝ) : ℂ)) • X' := by
    ext v
    have ht := Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.top_level_pointwise_identity Formalism.FourierDecayAlt.P.capelli_two_by_two Formalism.FourierDecayAlt.P.right_type_action hz hz'
      (Formalism.FourierDecayAlt.P.Qx5.Dp_dom P.k P.r Bs.z Bs.z') Bs.π'_rep Bs.π'_cont
      (Formalism.FourierDecayAlt.P.Qx5.slice_FF hz hz' hΦ (fun _ => one_ne_zero)) ⟨hx.2.1, hx.2.2⟩ (ne_of_gt hx.2.2) Fr hFr (Y : ℂ) v
    show Q.tL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) 1 1 (Φ c0) g v = _
    rw [ht, hval, ← hX', hGGv, ContinuousLinearMap.smul_apply]
  have hL : Gauge.rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (↑Y) 1 1 Φ) ρ qq =
      ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * (((Complex.normSq ζ - P.TT : ℝ) : ℂ) *
        inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X')) := by
    show ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ ζ))
      (B.hsVec (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (↑Y) 1 1 Φ c0 g)) = _
    rw [hQLg, hsm, inner_smul_right]
  have h0 : Gauge.rawR P Bs.μsec e Φ ρ qq = ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X) := by
    show ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (Φ c0 g)) = _
    rw [hval]
  let Gq : MA.SmQ P.r P.TT := (MA.DQ P).gg P.TT
  let sq : MA.SmQ P.r P.TT := M.xC P ρ ↑Y • MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ)
  change _ = ((Gq * sq : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) qq at hev
  rw [Subalgebra.coe_mul, Pi.mul_apply] at hev
  have hgg : (Gq : MA.Qp P.r P.TT → ℂ) qq = ((Complex.normSq ζ - P.TT : ℝ) : ℂ) := by
    show MA.coordE M.vz qq.1 * MA.coordE M.vzb qq.1 - (P.TT : ℂ) = _
    simp [MA.coordE, MA.zE, M.vz, M.vzb, Complex.mul_conj, qq]
  have hsq : (sq : MA.Qp P.r P.TT → ℂ) qq = M.xC P ρ ↑Y * Gauge.rawR P Bs.μsec e Φ ρ qq := by
    show ((M.xC P ρ ↑Y • MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ) : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) qq = _
    rw [Subalgebra.coe_smul, Pi.smul_apply, Gauge.GC.toSm_of_mem P hs0, smul_eq_mul]
  rw [hgg, hsq, hL, h0] at hev
  have h3 : ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * (((Complex.normSq ζ - P.TT : ℝ) : ℂ) *
        inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X')) =
      ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * (((Complex.normSq ζ - P.TT : ℝ) : ℂ) *
        (M.xC P ρ ↑Y * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X))) := by
    rw [hev]; ring
  exact mul_left_cancel₀ hGG0 (mul_left_cancel₀ hw' h3)

end

end Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapA
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

section defs

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def vABm (r : ℕ) (Y : ℂ) : ℕ → (((Fin r → ℂ) → X) → (Fin r → ℂ) → X) × (((Fin r → ℂ) → X) → (Fin r → ℂ) → X)
  | 0 => (id, fun _ => 0)
  | i + 1 =>
    if h : i < r then
      (fun f => Y • (vABm r Y i).1 f - pbOp ⟨i, h⟩ ((vABm r Y i).1 f) - cbOp ⟨i, h⟩ ((vABm r Y i).2 f),
        fun f => cbiOp ⟨i, h⟩ ((vABm r Y i).1 f))
    else vABm r Y i

end defs

def JDAGrp : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ → ∀ v (y : ℂ),
      ∃ Θ Θv : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)),
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ ∧
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θv ∧
        B.Commutes (T v).base (B.GPos (T v).base) Θ ∧ B.Commutes (T v).base (B.GPos (T v).base) Θv ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          ∀ c ∈ OmX S.G.r, ∀ g ∈ Q.Glev S.G.k S.G.r (Fin.last S.G.r),
            Q.wCell S.G.k S.G.r (Fin.last S.G.r) c * g ∈ OmP S T v →
            Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θ J) c g =
                dMul (drF S.G.r) (Q.crd (Q.cmp (Q.vAB S.G.r y S.G.r) 0)
                  (Q.resG S.G.k S.G.r (Fin.last S.G.r) J)) c g ∧
              Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θv J) c g =
                dMul (drbF S.G.r) (Q.crd (Q.cmp (vABm S.G.r y S.G.r) 0)
                  (Q.resG S.G.k S.G.r (Fin.last S.G.r) J)) c g

def JDAVTr : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e →
    ∀ L : R.LevelData (MA.A P (MA.DQ P)) P.r, MA.IsModelLevel P (MA.DQ P) L →
    ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Φ →
    ∀ y : ℂ,
      (Gauge.FamR P Bs Dc (Q.crd (Q.cmp (Q.vAB P.r y P.r) 0) Φ) ∧
        Gauge.VLem.trR P Bs.μsec e (Q.crd (Q.cmp (Q.vAB P.r y P.r) 0) Φ) =
          MA.actA P (L.Ar y) (Gauge.VLem.trR P Bs.μsec e Φ)) ∧
      (Gauge.FamR P Bs Dc (Q.crd (Q.cmp (vABm P.r y P.r) 0) Φ) ∧
        Gauge.VLem.trR P Bs.μsec e (Q.crd (Q.cmp (vABm P.r y P.r) 0) Φ) =
          MA.actA P (L.Avr y) (Gauge.VLem.trR P Bs.μsec e Φ))

theorem jDCapA_of_parts (hG : JDAGrp) (hV : JDAVTr) (hD : JDRDrTr) : JDCapA := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hL y
  obtain ⟨Θ, Θv, h1, h2, h3, h4, hR⟩ := hG Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v y
  refine ⟨Θ, Θv, h1, h2, h3, h4, fun J hJ => ?_⟩
  obtain ⟨hIB, -, -, -⟩ := hB
  obtain ⟨-, -, -, hIsB, -, -, -, -, -, -, hk, -⟩ := hIB
  have hpl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hIsB.2 v).2.2.2.1
  have hF := Gauge.tc_famR (D.parOf S v) (T v).base hpl J hJ
  obtain ⟨⟨hA, tA⟩, ⟨hAv, tAv⟩⟩ := hV _ _ (D.parOf S v) (T v).base hpl hk e hFr L hL _ _ hF y
  have hJR : trJ S T v e J = Gauge.VLem.trR (D.parOf S v) (T v).base.μsec e
      (Q.resG S.G.k S.G.r (Fin.last S.G.r) J) := by
    funext ρ
    show MA.toSm _ (Gauge.rawJ (D.parOf S v) (T v).base e J ρ) = _
    rw [Gauge.tc_rawJ]
    rfl
  have hpt : ∀ (Θ' : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (F : Q.Fn S.G.k S.G.r (Wq (S.pl v) →L[ℂ] Wp (S.pl v))),
      (∀ c ∈ OmX S.G.r, ∀ g ∈ Q.Glev S.G.k S.G.r (Fin.last S.G.r),
        Q.wCell S.G.k S.G.r (Fin.last S.G.r) c * g ∈ OmP S T v →
        Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θ' J) c g = F c g) →
      trJ S T v e (B.opApply Θ' J) = Gauge.VLem.trR (D.parOf S v) (T v).base.μsec e F := by
    intro Θ' F hF'
    funext ρ
    show MA.toSm _ (Gauge.rawJ (D.parOf S v) (T v).base e (B.opApply Θ' J) ρ) = _
    rw [Gauge.tc_rawJ]
    show MA.toSm _ _ = MA.toSm _ _
    congr 1
    funext q
    have hmu := Gauge.tc_mu (D.parOf S v) (T v).base hpl q
    simp only [Gauge.rawR]
    rw [hF' q.1.1 q.2.1 _ hmu.1 hmu.2]
  constructor
  · rw [hpt Θ _ (fun c hc g hg hcg => (hR J hJ c hc g hg hcg).1), hJR]
    funext ρ
    show MA.toSm _ (Gauge.rawR _ _ e (dMul (drF _) _) ρ) = _
    rw [(hD _ _ (D.parOf S v) (T v).base hpl hk e hFr L hL _ _ hA).2 ρ, R.LevelData.Ahat, Gauge.actA_mul, ← tA]
    rfl
  · rw [hpt Θv _ (fun c hc g hg hcg => (hR J hJ c hc g hg hcg).2), hJR]
    funext ρ
    show MA.toSm _ (Gauge.rawR _ _ e (dMul (drbF _) _) ρ) = _
    rw [(hD _ _ (D.parOf S v) (T v).base hpl hk e hFr L hL _ _ hAv).1 ρ, R.LevelData.Ahatv, Gauge.actA_mul, ← tAv]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRDrTr
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open Gauge Gauge.VLem

noncomputable section

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}
  {Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)}

theorem drtr_actA_cb (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.cbA P (MA.DQ P) l) f = fun ρ => MA.coordQ (TT := P.TT) (M.vcb l) * f ρ := by
  rw [MA.cbA, actA_sc]
  rfl

theorem drtr_actA_c (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.cA P (MA.DQ P) l) f = fun ρ => MA.coordQ (TT := P.TT) (M.vc l) * f ρ := by
  rw [MA.cA, actA_sc]
  rfl

theorem drtr_dMul_one (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) : dMul (fun _ => (1 : ℂ)) Φ = Φ := by
  funext c g
  simp [dMul]

theorem drtr_listb (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e)
    (ls : List (Fin P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (hΦ : FamR P Bs Dc Φ) :
    FamR P Bs Dc (dMul (fun c => (ls.map fun a => star (c a)).prod) Φ) ∧
      trR P Bs.μsec e (dMul (fun c => (ls.map fun a => star (c a)).prod) Φ) =
        MA.actA P (ls.map fun a => MA.cbA P (MA.DQ P) a).prod (trR P Bs.μsec e Φ) := by
  induction ls with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    rw [drtr_dMul_one, actA_one]
    exact ⟨hΦ, rfl⟩
  | cons a ls ih =>
    obtain ⟨hF, hT⟩ := ih
    have eq : dMul (fun c => ((a :: ls).map fun a => star (c a)).prod) Φ =
        Q.crd (cbOp a) (dMul (fun c => (ls.map fun a => star (c a)).prod) Φ) := by
      funext c g
      show _ = star (c a) • ((ls.map fun a => star (c a)).prod • Φ c g)
      simp only [dMul, List.map_cons, List.prod_cons, mul_smul]
    have hcb : FamR P Bs Dc (Q.crd (cbOp a) (dMul (fun c => (ls.map fun a => star (c a)).prod) Φ)) :=
      famR_opL hF a 4
    refine ⟨eq ▸ hcb, ?_⟩
    rw [eq, trR_mul hpl hk he hF _ hcb (fun c => star (c a)) (fun _ _ => rfl) (MA.coordQ (TT := P.TT) (M.vcb a))
      (fun q => coordE_vcb _ _), List.map_cons, List.prod_cons, actA_mul, drtr_actA_cb, hT]

theorem drtr_listc (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e)
    (ls : List (Fin P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (hΦ : FamR P Bs Dc Φ) :
    FamR P Bs Dc (dMul (fun c => (ls.map fun a => c a).prod) Φ) ∧
      trR P Bs.μsec e (dMul (fun c => (ls.map fun a => c a).prod) Φ) =
        MA.actA P (ls.map fun a => MA.cA P (MA.DQ P) a).prod (trR P Bs.μsec e Φ) := by
  induction ls with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    rw [drtr_dMul_one, actA_one]
    exact ⟨hΦ, rfl⟩
  | cons a ls ih =>
    obtain ⟨hF, hT⟩ := ih
    have eq : dMul (fun c => ((a :: ls).map fun a => c a).prod) Φ =
        Q.crd (cOp a) (dMul (fun c => (ls.map fun a => c a).prod) Φ) := by
      funext c g
      show _ = c a • ((ls.map fun a => c a).prod • Φ c g)
      simp only [dMul, List.map_cons, List.prod_cons, mul_smul]
    have hc : FamR P Bs Dc (Q.crd (cOp a) (dMul (fun c => (ls.map fun a => c a).prod) Φ)) :=
      famR_opL hF a 1
    refine ⟨eq ▸ hc, ?_⟩
    rw [eq, trR_mul hpl hk he hF _ hc (fun c => c a) (fun _ _ => rfl) (MA.coordQ (TT := P.TT) (M.vc a))
      (fun q => coordE_vc _ _), List.map_cons, List.prod_cons, actA_mul, drtr_actA_c, hT]

end

theorem residue_derivative_transition : JDRDrTr := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk e he L hL Dc Φ hΦ
  obtain ⟨-, -, hc, -, hcb, -⟩ := hL
  have eb : drbF P.r = fun c => ((List.finRange P.r).map fun a => star (c a)).prod := by
    funext c
    rw [drbF, map_prod, ← List.prod_ofFn, List.ofFn_eq_map]
    rfl
  have ec : drF P.r = fun c => ((List.finRange P.r).map fun a => c a).prod := by
    funext c
    rw [drF, ← List.prod_ofFn, List.ofFn_eq_map]
  have hDrb : L.Drb = ((List.finRange P.r).map fun a => MA.cbA P (MA.DQ P) a).prod := by
    rw [R.LevelData.Drb, hcb, List.ofFn_eq_map]
  have hDr : L.Dr = ((List.finRange P.r).map fun a => MA.cA P (MA.DQ P) a).prod := by
    rw [R.LevelData.Dr, hc, List.ofFn_eq_map]
  refine ⟨fun ρ => ?_, fun ρ => ?_⟩
  · have h := (drtr_listb hpl hk he (List.finRange P.r) Φ hΦ).2
    rw [← eb, ← hDrb] at h
    exact congrFun h ρ
  · have h := (drtr_listc hpl hk he (List.finRange P.r) Φ hΦ).2
    rw [← ec, ← hDr] at h
    exact congrFun h ρ

end

end Formalism.FourierDecayAlt.P.CutMP
end

