module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0107
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0093
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvPoly
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0102
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0108

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactCoefficientAppend
section
open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

open Formalism.FourierDecayAlt.P.PBJ

section lev0

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem ptG_one (TT : ℝ) (ζ : ℂ) : D.ptG TT 0 [(1, ζ)] = Complex.normSq ζ - TT := by
  simp [D.ptG, D.ptMatN, D.ptEntry, Matrix.det_fin_one]

theorem isLocPt_one {ζ : ℂ} (hζ : ζ ≠ 0) : D.IsLocPt [(1, ζ)] (0 + 1) := by
  refine ⟨?_, ?_⟩
  · intro b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact ⟨le_refl _, hζ⟩
  · simp [D.ptSize]

theorem orbJ_one_eq (S : B.RealPlaceData k ρ Wp Wq) {γ : B.Mat k ρ} (hγ : γ ∈ B.GV k ρ)
    (hpos : 0 < Gf k ρ S.z S.z' γ) {d : Fin (ρ + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
    (hZ : Zhat k ρ S.z S.z' γ = C2.monoP 1 d) (F : B.Mat k ρ → (Wq →L[ℂ] Wp)) :
    D.orbJ S γ (D.muR S γ 1) F = B.JF S F γ := by
  have : IsEmpty (C2.Lstidx (1 : Equiv.Perm (Fin (ρ + 1)))) := ⟨fun q => by
    obtain ⟨⟨a, b⟩, h1, h2⟩ := q
    simp only [Equiv.Perm.one_symm, Equiv.Perm.coe_one, id] at h2
    exact absurd h1 (not_lt.2 h2.le)⟩
  have hone : D.rhoOfU S γ 1 = 1 := by
    unfold D.rhoOfU
    split_ifs with hex
    · have h1mem : (1 : B.Mat k ρ) ∈ C6.Rset γ := by
        refine ⟨WeylGroupFacts.mem_n_one, ?_⟩
        rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ (Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hγ)]
        exact WeylGroupFacts.mem_n_one
      exact Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj S hγ hpos hd hZ hex.choose_spec.1 h1mem
        (hex.choose_spec.2.trans (Formalism.FourierDecayAlt.P.Dx2.Rad.uMap_one S.z ⟨S.z_mem, S.T_pos⟩).symm)
    · rfl
  have hlow : C2.lowOf (fun q : C2.Lstidx (1 : Equiv.Perm (Fin (ρ + 1))) => q.1) isEmptyElim = 1 := by
    unfold C2.lowOf
    ext i j
    simp
  have hR : D.muR S γ 1 = Measure.dirac (Matrix.of.symm (1 : B.Mat k ρ)) := by
    unfold D.muR
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty _ isEmptyElim, Measure.map_dirac' Subsingleton.measurable,
      hlow, Matrix.conjTranspose_one, hone]
  have hact : ∀ p, C6.actR γ 1 p = p := by
    intro p
    unfold C6.actR
    rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ (Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hγ), Matrix.one_mul,
      Matrix.one_mul]
    rfl
  have hθ : ∀ θ, D.IsNormCut S γ (D.muR S γ 1) θ → ∀ p, S.inSS p → θ p = 1 := by
    intro θ hθ p hp
    have h := hθ.2.2 p hp
    rw [hR, integral_dirac] at h
    change θ (C6.actR γ (1 : B.Mat k ρ) p) = 1 at h
    rw [hact p] at h
    exact h
  unfold D.orbJ
  split_ifs with hex
  · have h1 := hθ _ hex.choose_spec.1
    calc ∫ p, hex.choose p • D.orbIntegrand S γ F p ∂S.μSS = ∫ p, D.orbIntegrand S γ F p ∂S.μSS := by
          refine integral_congr_ae ?_
          filter_upwards [Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_inSS S] with p hp
          rw [h1 p hp, one_smul]
      _ = B.Jtau S (1, 1) F γ := rfl
      _ = B.JF S F γ := Formalism.FourierDecayAlt.P.bessel_function_trivial_index k ρ Wp Wq S F γ
  · have hni : ¬ Integrable (fun p => D.orbIntegrand S γ F p) S.μSS := by
      intro hI
      apply hex
      refine ⟨fun _ => 1, ⟨measurable_const, fun _ => zero_le_one, fun p _ => ?_⟩, by simpa using hI⟩
      rw [hR, integral_dirac]
    rw [← Formalism.FourierDecayAlt.P.bessel_function_trivial_index k ρ Wp Wq S F γ]
    exact (integral_undef hni).symm

theorem vector_level_zero_eq_jacquet (hρ : ρ = 0) (B0 : B.RealPlaceData k ρ Wp Wq) (ν : Fin (2 * ρ + k + 1) → ℂ) (m : B.Mat k ρ)
    (hb : D.IsBaseFrame B0 ν m) (Φ : B.Mat k ρ → (Wq →L[ℂ] Wp)) (ζ : ℂ)
    (hζ : Tz k ρ B0.z * Tz k ρ B0.z' < Complex.normSq ζ) (γ0 : B.Mat k ρ) (hγ0 : γ0 ∈ B.GV k ρ)
    (hZ : Zhat k ρ B0.z B0.z' γ0 = D.ptMatN [(1, ζ)] (ρ + 1)) (hD : D.IsDFrame B0 ν m γ0) :
    D.vecV B0 ν m Φ [(1, ζ)] = B.JF B0 Φ γ0 := by
  subst hρ
  have hTT : 0 < Tz k 0 B0.z * Tz k 0 B0.z' := mul_pos B0.T_pos B0.T'_pos
  have hζ0 : ζ ≠ 0 := by
    intro h; rw [h, Complex.normSq_zero] at hζ; linarith
  have hloc := isLocPt_one hζ0
  have hG : 0 < D.ptG (Tz k 0 B0.z * Tz k 0 B0.z') 0 [(1, ζ)] := by rw [ptG_one]; linarith
  rw [Formalism.FourierDecayAlt.P.isotropic_vectors_linear_indep k 0 Wp Wq B0 ν m Φ [(1, ζ)] hloc γ0 hb hG hγ0 hZ hD]
  have hw : (hloc.2 ▸ D.ptPerm [(1, ζ)] : Equiv.Perm (Fin (0 + 1))) = 1 := by
    refine Equiv.ext fun a => Fin.ext ?_
    have h1 := a.isLt
    have h2 := ((hloc.2 ▸ D.ptPerm [(1, ζ)] : Equiv.Perm (Fin (0 + 1))) a).isLt
    simp only [Equiv.Perm.coe_one, id]
    omega
  obtain ⟨hmono, hnz⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' [(1, ζ)] (0 + 1) hloc.2 hloc.1
  rw [hw] at hmono
  have hpos : 0 < Gf k 0 B0.z B0.z' γ0 := by
    rw [← Formalism.FourierDecayAlt.P.ptG_spec k 0 _ _ [(1, ζ)] γ0 hloc hZ]; exact hG
  rw [hw]
  exact orbJ_one_eq B0 hγ0 hpos hnz (hZ.trans hmono) Φ

theorem vector_level_zero_degenerate (hρ : ρ = 0) (B0 : B.RealPlaceData k ρ Wp Wq) (ν : Fin (2 * ρ + k + 1) → ℂ) (m : B.Mat k ρ)
    (Φ : B.Mat k ρ → (Wq →L[ℂ] Wp)) (ζ : ℂ) (hζ : Complex.normSq ζ ≤ Tz k ρ B0.z * Tz k ρ B0.z') :
    D.vecV B0 ν m Φ [(1, ζ)] = 0 := by
  subst hρ
  unfold D.vecV
  rw [dite_eq_right]
  rintro ⟨_, h⟩
  rw [ptG_one] at h
  linarith

theorem exists_frame_level_zero (hρ : ρ = 0) (B0 : B.RealPlaceData k ρ Wp Wq) (ν : Fin (2 * ρ + k + 1) → ℂ) (m : B.Mat k ρ)
    (hb : D.IsBaseFrame B0 ν m) (ζ : ℂ) (hζ : Tz k ρ B0.z * Tz k ρ B0.z' < Complex.normSq ζ) :
    ∃ γ0 ∈ B.GV k ρ, Zhat k ρ B0.z B0.z' γ0 = D.ptMatN [(1, ζ)] (ρ + 1) ∧ D.IsDFrame B0 ν m γ0 := by
  subst hρ
  have hTT : 0 < Tz k 0 B0.z * Tz k 0 B0.z' := mul_pos B0.T_pos B0.T'_pos
  have hζ0 : ζ ≠ 0 := by
    intro h; rw [h, Complex.normSq_zero] at hζ; linarith
  have hG : 0 < D.ptG (Tz k 0 B0.z * Tz k 0 B0.z') 0 [(1, ζ)] := by rw [ptG_one]; linarith
  exact Formalism.FourierDecayAlt.P.exists_isotropic_frame k 0 Wp Wq B0 ν m [(1, ζ)] hb (isLocPt_one hζ0) hG

theorem jacquet_integral_level_zero (hρ : ρ = 0) (B0 : B.RealPlaceData k ρ Wp Wq) (hN : B0.μN = D.muN k ρ)
    (Φ : B.Mat k ρ → (Wq →L[ℂ] Wp)) (γ : B.Mat k ρ) :
    B.JF B0 Φ γ = ∫ p : Mt k ρ × Mt k ρ, (B0.π (Matrix.of p.1)).comp
      ((Φ ((Matrix.of p.1)⁻¹ * γ * Matrix.of p.2)).comp (B0.π' (Matrix.of p.2)⁻¹)) ∂(B0.μW.prod B0.μW') := by
  subst hρ
  have : SigmaFinite B0.μW := Formalism.FourierDecayAlt.P.Dx2.MN.sigma_of_haar B0.haarW
  have : SigmaFinite B0.μW' := Formalism.FourierDecayAlt.P.Dx2.MN.sigma_of_haar B0.haarW'
  have hN0 : B0.μN = Measure.dirac (Matrix.of.symm (1 : B.Mat k 0)) := hN
  have hmeas : (B0.μW.prod B0.μN).prod (B0.μW'.prod B0.μN) = (B0.μW.prod B0.μW').map
      (fun p : Mt k 0 × Mt k 0 => ((p.1, Matrix.of.symm (1 : B.Mat k 0)), (p.2, Matrix.of.symm (1 : B.Mat k 0)))) := by
    rw [hN0, Measure.prod_dirac, Measure.prod_dirac,
      Measure.map_prod_map (f := fun x : Mt k 0 => (x, Matrix.of.symm (1 : B.Mat k 0)))
        (g := fun x : Mt k 0 => (x, Matrix.of.symm (1 : B.Mat k 0))) _ _ (by fun_prop) (by fun_prop)]
    rfl
  have hemb : MeasurableEmbedding (fun p : Mt k 0 × Mt k 0 =>
      ((p.1, Matrix.of.symm (1 : B.Mat k 0)), (p.2, Matrix.of.symm (1 : B.Mat k 0)))) :=
    (MeasurableEmbedding.id.prodMk_right _).prodMap (MeasurableEmbedding.id.prodMk_right _)
  have hpsi : ∀ (z : Fin (2 * 0 + k + 1) → ℂ) (g : B.Mat k 0), Formalism.QuantumDeterminants.psi k 0 z cStd g = 1 := by
    intro z g; simp [Formalism.QuantumDeterminants.psi, Formalism.QuantumDeterminants.ell]
  unfold B.JF besselJ
  rw [hmeas, hemb.integral_map]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [hpsi, star_one, mul_one, one_smul, Equiv.apply_symm_apply, inv_one]

end lev0

end Formalism.FourierDecayAlt.P.PBM
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMTC
section
noncomputable section

open Matrix MeasureTheory
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEXMT

open Formalism.FourierDecayAlt

variable {n : ℕ}

theorem upper_utc {M : Matrix (Fin n) (Fin n) ℂ} (hM : M ∈ C2.UTset n) : G.upper (StabilizerDisintegration.utc M) = M := by
  ext i j
  simp only [G.upper, G.strictUpper, StabilizerDisintegration.utc, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [dite_eq_left h, if_neg (ne_of_lt h), zero_add]
  · rw [dite_eq_right (lt_irrefl _), if_pos rfl, hM.2, add_zero]
  · rw [dite_eq_right (not_lt.2 h.le), if_neg (ne_of_gt h), hM.1 i j h, add_zero]

theorem upper_ut (v : G.UT n → ℂ) : G.upper v ∈ C2.UTset n := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · simp [G.upper, G.strictUpper, not_lt.2 h.le, ne_of_gt h]
  · simp [G.upper, G.strictUpper]

section gam

variable {r : ℕ} {X : Type}

def Gam (p : ((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ)) : (Fin r → Fin r → ℂ) × X :=
  (Matrix.of.symm (Matrix.of p.1.1 * Wm (Matrix.of p.1.1) * G.upper p.2), p.1.2)

theorem Gam_det (p : ((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ)) :
    (Matrix.of (Gam p).1).det = (Matrix.of p.1.1).det := by
  simp only [Gam, Equiv.apply_symm_apply]
  rw [Matrix.det_mul, Matrix.det_mul, C2x2.ut_det (Wm_ut _), C2x2.ut_det (upper_ut p.2), mul_one, mul_one]

theorem Gam_eq (q : (Fin r → Fin r → ℂ) × X) (u : Matrix (Fin r) (Fin r) ℂ) (hdet : (Matrix.of q.1).det ≠ 0)
    (hu : u ∈ C2.UTset r) : Gam ((Matrix.of.symm (Matrix.of q.1 * u), q.2), StabilizerDisintegration.utc (Sm (Matrix.of q.1))) = q := by
  simp only [Gam, Equiv.apply_symm_apply]
  rw [Wm_mul hdet hu, upper_utc (Sm_ut _), Matrix.mul_assoc (Matrix.of q.1) u,
    Matrix.mul_nonsing_inv_cancel_left _ _ (C2x2.ut_unit hu), Matrix.mul_assoc, Wm_mul_Sm, Matrix.mul_one]
  rfl

theorem Gam_cont [TopologicalSpace X] (S : Set (((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ)))
    (hS : ∀ p ∈ S, (Matrix.of p.1.1).det ≠ 0) : ContinuousOn Gam S := by
  have hW : ∀ a b : Fin r, ContinuousOn (fun p : ((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ) => Wm (Matrix.of p.1.1) a b) S :=
    fun a b => (cd_Wm a b).continuousOn.comp (continuous_fst.comp continuous_fst).continuousOn fun p hp => hS p hp
  refine ContinuousOn.prodMk (continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => ?_)
    (continuous_snd.comp continuous_fst).continuousOn
  have e : ∀ p : ((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ),
      (Gam p).1 a b = ∑ c : Fin r, (∑ d : Fin r, p.1.1 a d * Wm (Matrix.of p.1.1) d c) * G.upper p.2 c b := by
    intro p
    simp only [Gam]
    rfl
  have key : ContinuousOn (fun p : ((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ) =>
      ∑ c : Fin r, (∑ d : Fin r, p.1.1 a d * Wm (Matrix.of p.1.1) d c) * G.upper p.2 c b) S := by
    refine continuousOn_finsetSum _ fun c _ => ContinuousOn.mul (continuousOn_finsetSum _ fun d _ => ?_) ?_
    · exact (((continuous_apply_apply a d).comp (continuous_fst.comp continuous_fst)).continuousOn).mul (hW d c)
    · exact ((continuous_apply_apply c b).comp (Formalism.FourierDecayAlt.P.Dx2.SL.cont_upper.comp continuous_snd)).continuousOn
  exact key.congr fun p _ => e p

end gam

theorem top_truncation_construction : MkTopCut := by
  intro r
  let φ : ContDiffBump (0 : G.UT r → ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  set β₀ : (G.UT r → ℂ) → ℝ := φ.normed volume with hβ₀
  have hcont : Continuous β₀ := φ.continuous_normed
  refine ⟨fun Z => β₀ (StabilizerDisintegration.utc (Sm (Matrix.of Z))), ?_, ?_, ?_⟩
  · have hS : ContDiffOn ℝ ∞ (fun Z : Fin r → Fin r → ℂ => StabilizerDisintegration.utc (Sm (Matrix.of Z)))
        {Z | (Matrix.of Z).det ≠ 0} :=
      contDiffOn_pi.2 fun q => cd_Sm q.1.1 q.1.2
    exact (φ.contDiff_normed (n := ⊤)).comp_contDiffOn hS
  · intro Z hZ
    have hmp := Formalism.FourierDecayAlt.P.StabilizerDisintegration.HC.mp_UTleft (Sm_ut (Matrix.of Z))
    have hfun : (fun v : G.UT r → ℂ => β₀ (StabilizerDisintegration.utc (Sm (Matrix.of (Matrix.of.symm (Matrix.of Z * G.upper v)))))) =
        fun v => β₀ (StabilizerDisintegration.utc (Sm (Matrix.of Z) * G.upper v)) := by
      funext v
      simp only [Equiv.apply_symm_apply]
      rw [Sm_mul hZ (upper_ut v)]
    show Integrable (fun v : G.UT r → ℂ => β₀ (StabilizerDisintegration.utc (Sm (Matrix.of (Matrix.of.symm (Matrix.of Z * G.upper v)))))) ∧
      ∫ v : G.UT r → ℂ, β₀ (StabilizerDisintegration.utc (Sm (Matrix.of (Matrix.of.symm (Matrix.of Z * G.upper v))))) = 1
    rw [hfun]
    constructor
    · have hi := (integrable_map_measure hcont.aestronglyMeasurable hmp.measurable.aemeasurable).1
        (by rw [hmp.map_eq]; exact φ.integrable_normed)
      exact hi
    · rw [← integral_map hmp.measurable.aemeasurable hcont.aestronglyMeasurable, hmp.map_eq]
      exact φ.integral_normed
  · intro X _ K hK hKdet
    have hC₀ : IsCompact (tsupport β₀) := φ.hasCompactSupport_normed
    refine ⟨Gam '' (K ×ˢ tsupport β₀), (hK.prod hC₀).image_of_continuousOn (Gam_cont _ fun p hp => hKdet _ hp.1), ?_, ?_⟩
    · rintro q ⟨⟨q', c⟩, ⟨hq', -⟩, rfl⟩
      exact ⟨by rw [Gam_det]; exact hKdet q' hq', q', hq', rfl⟩
    · rintro q hdet hβ ⟨u, hu, hK'⟩
      have huT : u ∈ C2.UTset r := ⟨fun i j h => hu.1 h, hu.2⟩
      exact ⟨((Matrix.of.symm (Matrix.of q.1 * u), q.2), StabilizerDisintegration.utc (Sm (Matrix.of q.1))),
        ⟨hK', subset_tsupport _ hβ⟩, Gam_eq q u hdet huT⟩

end Formalism.FourierDecayAlt.P.CutEXMT
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvFinal
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem curvature_polynomial_holds : GTCCurvPoly := curvature_polynomial_of_scalar curvature_scalar_holds

theorem curvature_identity_holds : GTCCurvId :=
  gTCCurvId_of_cut curvature_polynomial_holds curvature_radial_torus_holds curvature_block_form_holds

theorem top_normal_form_of_curvature : GTRTopNF := gTRTopNF_of_curvPoly curvature_polynomial_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadTAsmB
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTA

noncomputable section

open Classical

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
  {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}
  {Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp)}

theorem fn_eq_of_radR (hB : NF.RadBase k r z z' μs π π') (Ψ : Q.RadSp k r z z' π π') {c c' : Fin r → ℂ}
    (hc : c ∈ OmX r) (hc' : c' ∈ OmX r)
    (h : ∀ ζ, NF.radR k r z z' μs (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) (c, ζ) =
      NF.radR k r z z' μs (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) (c', ζ)) :
    (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c = (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c' := by
  obtain ⟨hk, hz, hz', hT, hT', hsec, -, -, -, -⟩ := hB
  obtain ⟨h0, -, he⟩ := Ψ.2
  funext g
  by_cases hg : g ∈ Q.Glev k r (Fin.last r) ∧ 0 < Q.GGl k r z z' g
  · obtain ⟨hgG, hG'⟩ := hg
    have hζq : Tz k r z * Tz k r z' < Complex.normSq (Q.zetaL k r z z' (Fin.last r) g) := by
      have h1 := hG'
      unfold Q.GGl at h1
      linarith
    obtain ⟨a, ha, b, hb, hgeq⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp hk hz hz' hT hT' hsec hgG hG'
    generalize Q.zetaL k r z z' (Fin.last r) g = ζ at hζq hgeq
    have hq : (c, ζ) ∈ NF.QR k r z z' := ⟨hc, hζq⟩
    have hq' : (c', ζ) ∈ NF.QR k r z z' := ⟨hc', hζq⟩
    have e1 := he (c, NF.muZ k r μs ζ) (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hsec hq) a ha b hb
    have e2 := he (c', NF.muZ k r μs ζ) (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hsec hq') a ha b hb
    have e3 := h ζ
    rw [radR_apply _ hq, radR_apply _ hq'] at e3
    dsimp only at e1 e2 e3
    rw [hgeq, e1, e2, e3]
  · have n1 : (c, g) ∉ Q.DomR k r z z' := fun hx => hg ⟨hx.2.1, hx.2.2⟩
    have n2 : (c', g) ∉ Q.DomR k r z z' := fun hx => hg ⟨hx.2.1, hx.2.2⟩
    exact (h0 (c, g) n1).trans (h0 (c', g) n2).symm

theorem t_slice (hB : NF.RadBase k r z z' μs π π') (X : Q.ActualOps k r z z' π π') (Y : ℂ) (a b : Fin 2)
    (Ψ : Q.RadSp k r z z' π π') {c c' : Fin r → ℂ} (hc : c ∈ OmX r) (hc' : c' ∈ OmX r)
    (h : (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c = (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c') {ζ : ℂ} (hζ : ζ ∈ Ann z z') :
    NF.radR k r z z' μs ((X.t Y a b Ψ : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp)) (c, ζ) =
      NF.radR k r z z' μs ((X.t Y a b Ψ : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp)) (c', ζ) := by
  obtain ⟨-, hz, hz', -, -, hsec, -, -, -, -⟩ := hB
  have hq : (c, ζ) ∈ NF.QR k r z z' := ⟨hc, hζ⟩
  have hq' : (c', ζ) ∈ NF.QR k r z z' := ⟨hc', hζ⟩
  rw [radR_apply _ hq, radR_apply _ hq', X.t_apply Y a b Ψ _ (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hsec hq),
    X.t_apply Y a b Ψ _ (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hsec hq')]
  dsimp only
  rw [h]

def pw (j : ℕ) (s : Fin j → Fin 2) (ζ0 : ℂ) (X : Wq →L[ℂ] Wp) : ℂ → (Wq →L[ℂ] Wp) :=
  fun ζ => (((j.factorial : ℝ)⁻¹ * ∏ i, crd (s i) (ζ - ζ0)) • X)

theorem pw_smooth (j : ℕ) (s : Fin j → Fin 2) (ζ0 : ℂ) (X : Wq →L[ℂ] Wp) : ContDiff ℝ ∞ (pw j s ζ0 X) :=
  (contDiff_const.mul (contDiff_prod fun i _ => (crd (s i)).contDiff.comp (contDiff_id.sub contDiff_const))).smul
    contDiff_const

def wt (j : ℕ) (s : Fin j → Fin 2) (t : Finset (Fin j)) (X : Wq →L[ℂ] Wp) : ℂ → (Wq →L[ℂ] Wp) :=
  fun ζ => (((j.factorial : ℝ)⁻¹ * ∏ i ∈ Finset.univ \ t, crd (s i) ζ) • X)

theorem wt_smooth (j : ℕ) (s : Fin j → Fin 2) (t : Finset (Fin j)) (X : Wq →L[ℂ] Wp) : ContDiff ℝ ∞ (wt j s t X) :=
  (contDiff_const.mul (contDiff_prod fun i _ => (crd (s i)).contDiff)).smul contDiff_const

theorem pw_expand (j : ℕ) (s : Fin j → Fin 2) (ζ0 : ℂ) (X : Wq →L[ℂ] Wp) :
    pw j s ζ0 X = fun ζ => ∑ t ∈ (Finset.univ : Finset (Fin j)).powerset,
      (∏ i ∈ t, -crd (s i) ζ0) • wt j s t X ζ := by
  funext ζ
  have hp : ∏ i, crd (s i) (ζ - ζ0) = ∏ i, (-crd (s i) ζ0 + crd (s i) ζ) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_sub]
    ring
  simp only [pw, wt, hp, Finset.prod_add, Finset.mul_sum, Finset.sum_smul, smul_smul]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  ring


variable (z z' μs π π' Pr) in
def Bsl (T : Module.End ℂ (Q.RadSp k r z z' π π')) (c0 : Fin r → ℂ) (j : ℕ) (s : Fin j → Fin 2) (ζ0 : ℂ) :
    (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
  if hG : Gd z z' μs π π' Pr then
    LinearMap.toContinuousLinearMap
      { toFun := fun X => VV z z' μs π π' Pr T c0 (pw j s ζ0 X) ζ0
        map_add' := fun X X' => by
          have e : pw j s ζ0 (X + X') = fun ζ => pw j s ζ0 X ζ + pw j s ζ0 X' ζ := by
            funext ζ
            simp only [pw, smul_add]
          rw [e, VV_add hG (pw_smooth j s ζ0 X) (pw_smooth j s ζ0 X')]
        map_smul' := fun c X => by
          have e : pw j s ζ0 (c • X) = fun ζ => c • pw j s ζ0 X ζ := by
            funext ζ
            simp only [pw]
            rw [smul_comm]
          rw [e, VV_smulR hG (pw_smooth j s ζ0 X)]
          rfl }
  else 0

variable {T : Module.End ℂ (Q.RadSp k r z z' π π')} {c0 : Fin r → ℂ}

theorem Bsl_apply (hG : Gd z z' μs π π' Pr) (j : ℕ) (s : Fin j → Fin 2) (ζ0 : ℂ) (X : Wq →L[ℂ] Wp) :
    Bsl z z' μs π π' Pr T c0 j s ζ0 X = VV z z' μs π π' Pr T c0 (pw j s ζ0 X) ζ0 := by
  unfold Bsl
  rw [dite_eq_left hG]
  rfl

theorem Bsl_smooth (hG : Gd z z' μs π π' Pr) (hc0 : c0 ∈ OmX r) (j : ℕ) (s : Fin j → Fin 2) :
    ContDiffOn ℝ ∞ (fun ζ0 => Bsl z z' μs π π' Pr T c0 j s ζ0) (Ann z z') := by
  rw [contDiffOn_clm_apply]
  intro X
  have key : ∀ ζ0, Bsl z z' μs π π' Pr T c0 j s ζ0 X = ∑ t ∈ (Finset.univ : Finset (Fin j)).powerset,
      (∏ i ∈ t, -crd (s i) ζ0) • VV z z' μs π π' Pr T c0 (wt j s t X) ζ0 := by
    intro ζ0
    rw [Bsl_apply hG, pw_expand, VV_sum hG _ _ (fun t => (wt_smooth j s t X).const_smul _)]
    refine Finset.sum_congr rfl fun t _ => ?_
    exact VV_smulR hG (wt_smooth j s t X) _ ζ0
  refine (ContDiffOn.sum fun t _ => ?_).congr fun ζ0 _ => key ζ0
  exact (contDiff_prod fun i _ => (crd (s i)).contDiff.neg).contDiffOn.smul (VV_smooth hG hc0)


variable (z z' μs π π' Pr T c0) in
def AA (j : ℕ) (ζ0 : ℂ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
  ∑ s : Fin j → Fin 2, (Bsl z z' μs π π' Pr T c0 j s ζ0).comp
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp) (fun i => e2 (s i)))

theorem AA_apply (hG : Gd z z' μs π π' Pr) (j : ℕ) (ζ0 : ℂ)
    (m : ContinuousMultilinearMap ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp)) :
    AA z z' μs π π' Pr T c0 j ζ0 m =
      VV z z' μs π π' Pr T c0 (fun ζ => ((j.factorial : ℝ)⁻¹) • m (fun _ => ζ - ζ0)) ζ0 := by
  have e : (fun ζ => ((j.factorial : ℝ)⁻¹) • m (fun _ => ζ - ζ0)) =
      fun ζ => ∑ s : Fin j → Fin 2, pw j s ζ0 (m (fun i => e2 (s i))) ζ := by
    funext ζ
    rw [ml_expand m (ζ - ζ0), Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [pw, smul_smul]
  rw [e, VV_sum hG _ _ (fun s => pw_smooth j s ζ0 _)]
  unfold AA
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.apply_apply, Bsl_apply hG]

theorem AA_smooth (hG : Gd z z' μs π π' Pr) (hc0 : c0 ∈ OmX r) (j : ℕ) :
    ContDiffOn ℝ ∞ (AA z z' μs π π' Pr T c0 j) (Ann z z') := by
  have e : AA z z' μs π π' Pr T c0 j = fun ζ0 => ∑ s : Fin j → Fin 2, (Bsl z z' μs π π' Pr T c0 j s ζ0).comp
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp) (fun i => e2 (s i))) := rfl
  rw [e]
  exact ContDiffOn.sum fun s _ => (Bsl_smooth hG hc0 j s).clm_comp contDiffOn_const

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrablePhiF
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem continuous_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    Continuous fun g : Mt k r => psi k r z c (Matrix.of g) := by
  have hl := B7.continuous_ell (k := k) (r := r) z
  unfold psi
  exact Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_const.mul hl))))

attribute [local instance] B7.properFD

end Formalism.FourierDecayAlt.P.S3dx6
end
end

