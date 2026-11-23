module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermsAbsTsumLeHeightPoly
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0163
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SectionTrace.SecOf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0216
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0217
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0231
public import Development.WeilBound.ThetaLifts.LatticeBasics.FrameConj
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Formalism.PeriodIntegrals.Bundle0016
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0132
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.KFiniteVectorsIrreducibleUnitaryUnitaryGroupPQ

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartSectionExists
section
open ResidueKilled.Tr
open scoped NNReal Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.TChartProof

open Matrix

theorem mat_mul' {D : D7} {n : ℕ} (g h : G D n) : mat (g * h) = mat g * mat h := by
  simp only [mat, map_mul, Units.val_mul]

theorem mat_one' {D : D7} {n : ℕ} : mat (1 : G D n) = 1 := by
  simp only [mat, map_one, Units.val_one]

theorem blkA_mul_of_lowerLeft {R : Type} [CommRing R] {n : ℕ} (X Y : Matrix (Fin (n + n)) (Fin (n + n)) R)
    (hY : ∀ i j : Fin n, Y (Fin.natAdd n i) (Fin.castAdd n j) = 0) : blkA (X * Y) = blkA X * blkA Y := by
  ext i j
  simp only [blkA, Matrix.mul_apply, Fin.sum_univ_add, hY, mul_zero, Finset.sum_const_zero, add_zero,
    toBlocks₁₁, Matrix.of_apply, submatrix_apply, finSumFinEquiv_apply_left]

theorem blkA_one' {R : Type} [CommRing R] {n : ℕ} : blkA (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 := by
  ext i j
  simp [blkA, toBlocks₁₁, Matrix.one_apply]

theorem exists_gl_blkA {D : D7} {n : ℕ} {g : G D n} (hg : g ∈ P D n) :
    ∃ a : GL (Fin n) (AE D), blkA (mat g) = a.1 := by
  have hg' : g⁻¹ ∈ P D n := inv_mem hg
  have e₁ : blkA (mat g) * blkA (mat g⁻¹) = 1 := by
    rw [← blkA_mul_of_lowerLeft _ _ (chart_lowerLeft_zero hg'), ← mat_mul', mul_inv_cancel, mat_one', blkA_one']
  have e₂ : blkA (mat g⁻¹) * blkA (mat g) = 1 := by
    rw [← blkA_mul_of_lowerLeft _ _ (chart_lowerLeft_zero hg), ← mat_mul', inv_mul_cancel, mat_one', blkA_one']
  exact ⟨⟨_, _, e₁, e₂⟩, rfl⟩

theorem tChart : TChart := by
  intro hDict hDI hStd D χ V a hMaj
  obtain ⟨m0, hm0, hp0⟩ := _root_.GlobalTheory.StdUnn.ConjElt.exists_isConj D
  obtain ⟨κ, hκ⟩ := _root_.GlobalTheory.StdUnn.chart_exists D V m0 hm0
  obtain ⟨p, hp⟩ := hp0 V a hMaj κ hκ
  obtain ⟨hc, hc'⟩ := _root_.GlobalTheory.StdUnn.chart_continuous D V m0 hm0 κ hκ
  obtain ⟨Ψ, h1, h2, h3, h4⟩ := hStd hDict hDI D χ V.rank
  have hG := _root_.GlobalTheory.StdUnn.chart_mem_GF_iff D V m0 hm0 κ hκ
  have hP := _root_.GlobalTheory.StdUnn.mem_siegel_iff_chart_mem_P D V m0 hm0 κ hκ
  let κt : GA D (dblSp V) ≃ₜ* G D V.rank :=
    { κ with continuous_toFun := hc, continuous_invFun := hc' }
  have hκt : ∀ g, κt g = κ g := fun _ => rfl
  refine ⟨κt.trans Ψ, p, fun g => ?_, fun g => ?_, fun k => ?_, fun q => ?_, fun x => ?_⟩
  · exact (hG g).trans (h1 (κ g))
  · exact (hP g).trans (h2 (κ g))
  · exact (hp k).trans (h3 _)
  · obtain ⟨b, hb⟩ := exists_gl_blkA ((hP q).1 q.2)
    have e₁ := _root_.GlobalTheory.StdUnn.chart_aP_eq_det D V m0 hm0 κ hκ q b hb
    have e₂ := h4 (κ q) b hb
    rw [e₁]
    exact e₂
  · have e := (hDict D.host.F D.host.E).2.2.2.2 x
    show Real.log _ = _
    rw [e]

end GlobalTheory.CompanionTheory.TChartProof
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousRxSymm
section
noncomputable section

open scoped NNReal Matrix TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open PositivityTheory.RgEis ResidueKilled.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.StdChart

section Gen

variable {R : Type} [CommRing R] {n : ℕ}

def rx : GL (Fin (n + n)) R ≃* GL (Fin n ⊕ Fin n) R :=
  Units.mapEquiv (Matrix.reindexAlgEquiv R R (finSumFinEquiv (m := n) (n := n)).symm).toMulEquiv

theorem rx_val (g : GL (Fin (n + n)) R) : (rx g).1 = g.1.submatrix finSumFinEquiv finSumFinEquiv := rfl

theorem rx_inv_val (g : GL (Fin (n + n)) R) :
    ((rx g)⁻¹ : GL (Fin n ⊕ Fin n) R).1 = (g⁻¹ : GL (Fin (n + n)) R).1.submatrix finSumFinEquiv finSumFinEquiv := by
  rw [← map_inv]; rfl

theorem continuous_rx [TopologicalSpace R] : Continuous (rx : GL (Fin (n + n)) R → GL (Fin n ⊕ Fin n) R) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val.matrix_submatrix _ _)
  · have : (fun g : GL (Fin (n + n)) R => (((rx g)⁻¹ : GL (Fin n ⊕ Fin n) R) : Matrix _ _ R)) =
        fun g => (g⁻¹ : GL (Fin (n + n)) R).1.submatrix finSumFinEquiv finSumFinEquiv := funext rx_inv_val
    rw [this]
    exact (Units.continuous_coe_inv.matrix_submatrix _ _)

theorem continuous_rx_symm [TopologicalSpace R] :
    Continuous (rx.symm : GL (Fin n ⊕ Fin n) R → GL (Fin (n + n)) R) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val.matrix_submatrix _ _)
  · have : (fun g : GL (Fin n ⊕ Fin n) R => (((rx.symm g)⁻¹ : GL (Fin (n + n)) R) : Matrix _ _ R)) =
        fun g => (g⁻¹ : GL (Fin n ⊕ Fin n) R).1.submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
      funext g; rw [← map_inv]; rfl
    rw [this]
    exact (Units.continuous_coe_inv.matrix_submatrix _ _)

theorem form_iff {ι : Type} [Fintype ι] (c : R →+* R) (hc : ∀ x, c (c x) = x) {J : Matrix ι ι R} (hJ : J.map c = J)
    (g : Matrix ι ι R) : Formalism.UG.cT c g * J * g = J ↔ gᵀ * J * g.map c = J := by
  have key : (Formalism.UG.cT c g * J * g).map c = gᵀ * J * g.map c := by
    rw [Matrix.map_mul, Matrix.map_mul, hJ]
    congr 2
    ext i j
    simp [Formalism.UG.cT, hc]
  constructor
  · intro h
    rw [← key, h, hJ]
  · intro h
    have h2 := congrArg (fun M => M.map c) h
    simp only [Matrix.map_mul, hJ] at h2
    have e : (gᵀ).map c = Formalism.UG.cT c g := by ext i j; simp [Formalism.UG.cT]
    have e2 : (g.map c).map c = g := by ext i j; simp [hc]
    rwa [e, e2] at h2

theorem keeps_iff_int {ι : Type} [Fintype ι] [DecidableEq ι] (O : Subring R) (m : GL ι R) :
    (∀ y : ι → R, (∀ i, y i ∈ O) ↔ ∀ i, (m.1 *ᵥ y) i ∈ O) ↔
      ∀ r c, m.1 r c ∈ O ∧ (m⁻¹ : GL ι R).1 r c ∈ O := by
  constructor
  · intro h r c
    have hs : ∀ i, (Pi.single c (1 : R) : ι → R) i ∈ O := fun i => by
      by_cases e : i = c
      · subst e; simp [O.one_mem]
      · simp [e, O.zero_mem]
    refine ⟨by simpa using (h _).1 hs r, ?_⟩
    have h2 := (h (((m⁻¹ : GL ι R).1) *ᵥ Pi.single c 1)).2 (by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]; exact hs) r
    simpa using h2
  · intro h y
    have key : ∀ (M : Matrix ι ι R), (∀ r c, M r c ∈ O) → ∀ y : ι → R, (∀ i, y i ∈ O) → ∀ i, (M *ᵥ y) i ∈ O :=
      fun M hM y hy i => O.sum_mem fun j _ => O.mul_mem (hM i j) (hy j)
    refine ⟨key _ (fun r c => (h r c).1) y, fun hy => ?_⟩
    have := key _ (fun r c => (h r c).2) _ hy
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

end Gen

section Sub

variable {R : Type} {n : ℕ}

theorem sub_inj {X Y : Matrix (Fin (n + n)) (Fin (n + n)) R} :
    X.submatrix finSumFinEquiv finSumFinEquiv = Y.submatrix finSumFinEquiv finSumFinEquiv ↔ X = Y := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  ext i j
  have := congrFun (congrFun h (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
  simpa using this

end Sub

section Std

variable (D : D7) {n : ℕ}

theorem sig_sig (x : D.host.E) : D.sp.cm.sig (D.sp.cm.sig x) = x := by
  have h := isCMExt_host D
  obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ]
  simp

theorem sigR_sigR (z : AE D) : sigR (AF D.host.F) D.sp.cm.sig (sigR (AF D.host.F) D.sp.cm.sig z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    change a ⊗ₜ[D.host.F] D.sp.cm.sig (D.sp.cm.sig e) = _
    rw [sig_sig]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem sigR_inclR (x : D.host.E) :
    sigR (AF D.host.F) D.sp.cm.sig (inclR (AF D.host.F) x) = inclR (AF D.host.F) (D.sp.cm.sig x) := rfl

theorem Jst_map : (GlobalTheory.StdUnn.Jst D n).map D.sp.cm.sig = GlobalTheory.StdUnn.Jst D n := by
  ext i j
  simp only [Matrix.map_apply, GlobalTheory.StdUnn.Jst, GlobalTheory.StdUnn.blk4, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.one_apply] <;> split_ifs <;> simp

theorem JR_map : (JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n)).map (sigR (AF D.host.F) D.sp.cm.sig) =
    JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n) := by
  ext i j
  simp only [Matrix.map_apply, JR, sigR_inclR]
  rw [← Matrix.map_apply (f := D.sp.cm.sig), Jst_map]

theorem J_eq : (JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n)).submatrix finSumFinEquiv finSumFinEquiv =
    Ad.J (AE D) (-1) (Fin n) := by
  have key : ∀ x y, (JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n)).submatrix finSumFinEquiv finSumFinEquiv x y =
      inclR (F := D.host.F) (E := D.host.E) (AF D.host.F) ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) D.host.E) x y) := fun x y => by
    simp only [JR, GlobalTheory.StdUnn.Jst, GlobalTheory.StdUnn.blk4, Matrix.submatrix_apply, Matrix.map_apply, Equiv.symm_apply_apply]
  ext x y
  rw [key]
  rcases x with a | a <;> rcases y with b | b <;> simp [Ad.J, Matrix.one_apply, apply_ite (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F))]

variable (χ : (AE D)ˣ →* Circle)

theorem mem_uSub_iff (g : GL (Fin (n + n)) (AE D)) :
    rx g ∈ (adCM D.sp.cm.sig χ).uSub (-1) (Fin n) ↔ g ∈ HR (AF D.host.F) D.sp.cm.sig (GlobalTheory.StdUnn.Jst D n) := by
  change (rx g).1ᵀ * Ad.J (AE D) (-1) (Fin n) * (rx g).1.map (sigR (AF D.host.F) D.sp.cm.sig) = Ad.J (AE D) (-1) (Fin n) ↔
    Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) g.1 * JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n) * g.1 = JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n)
  rw [form_iff _ (sigR_sigR D) (JR_map D), ← J_eq, rx_val, ← sub_inj (X := _ * _ * _)]
  have : (g.1ᵀ * JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n) * g.1.map (sigR (AF D.host.F) D.sp.cm.sig)).submatrix finSumFinEquiv finSumFinEquiv =
      (g.1.submatrix finSumFinEquiv finSumFinEquiv)ᵀ * (JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n)).submatrix finSumFinEquiv finSumFinEquiv *
        (g.1.submatrix finSumFinEquiv finSumFinEquiv).map (sigR (AF D.host.F) D.sp.cm.sig) := by
    rw [← Matrix.submatrix_mul_equiv _ _ finSumFinEquiv finSumFinEquiv finSumFinEquiv,
      ← Matrix.submatrix_mul_equiv _ _ finSumFinEquiv finSumFinEquiv finSumFinEquiv]
    rfl
  rw [this]

def toU (g : GlobalTheory.StdUnn.G D n) : UD D χ n :=
  ⟨rx (matHom _ D.sp.cm.sig (GlobalTheory.StdUnn.Jst D n) g), (mem_uSub_iff D χ _).2 (Subtype.prop (p := (· ∈ HR _ _ _)) g)⟩

theorem toU_val (g : GlobalTheory.StdUnn.G D n) : (toU D χ g).1 = rx (matHom _ D.sp.cm.sig (GlobalTheory.StdUnn.Jst D n) g) := rfl

def ofU (u : UD D χ n) : GlobalTheory.StdUnn.G D n :=
  (⟨rx.symm u.1, (mem_uSub_iff D χ _).1 (by simpa using u.2)⟩ : HR (AF D.host.F) D.sp.cm.sig (GlobalTheory.StdUnn.Jst D n))

theorem ofU_val (u : UD D χ n) : matHom _ D.sp.cm.sig (GlobalTheory.StdUnn.Jst D n) (ofU D χ u) = rx.symm u.1 := rfl

def Psi (n : ℕ) : GlobalTheory.StdUnn.G D n ≃ₜ* UD D χ n where
  toFun := toU D χ
  invFun := ofU D χ
  left_inv g := matHom_injective _ _ _ (by rw [ofU_val, toU_val]; exact rx.symm_apply_apply _)
  right_inv u := Subtype.ext (by rw [toU_val, ofU_val]; exact rx.apply_symm_apply _)
  map_mul' g h := Subtype.ext (by rw [Subgroup.coe_mul, toU_val, toU_val, toU_val, map_mul, map_mul])
  continuous_toFun := (continuous_rx.comp (isEmbedding_matHom _ _ _).continuous).subtype_mk _
  continuous_invFun := (isEmbedding_matHom _ _ _).continuous_iff.2 (continuous_rx_symm.comp continuous_subtype_val)

theorem Psi_val (g : GlobalTheory.StdUnn.G D n) : (Psi D χ n g).1 = rx (matHom _ D.sp.cm.sig (GlobalTheory.StdUnn.Jst D n) g) := rfl

end Std

end GlobalTheory.CompanionTheory.StdChart

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DivisibilityStatement
section
noncomputable section

open scoped Topology
open Filter Set Metric GlobalTheory.Cont

namespace GlobalTheory.CompanionTheory.DivMult

theorem exists_factor {A : ℂ → ℂ} (hA : Differentiable ℂ A) (hne : ∃ z, A z ≠ 0) (s₀ : ℂ) :
    ∃ (k : ℕ) (u : ℂ → ℂ) (r M : ℝ), 0 < r ∧ DifferentiableOn ℂ u (ball s₀ r) ∧ (∀ s ∈ ball s₀ r, u s ≠ 0) ∧
      (∀ s ∈ ball s₀ r, A s = (s - s₀) ^ k * u s) ∧ ∀ s ∈ ball s₀ r, ‖(u s)⁻¹‖ ≤ M := by
  have hAn : AnalyticOnNhd ℂ A univ := fun z _ => hA.analyticAt z
  have hnz : ¬∀ᶠ z in 𝓝 s₀, A z = 0 := by
    intro hev
    obtain ⟨w, hw⟩ := hne
    have := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ s₀)
      (hev.mono fun z hz => by simp [hz])
    exact hw (by simpa using this (mem_univ w))
  obtain ⟨k, g, hg, hg0, hev⟩ := (hA.analyticAt s₀).exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnz
  have hpos : 0 < ‖g s₀‖ := norm_pos_iff.mpr hg0
  have hcont : ∀ᶠ z in 𝓝 s₀, ‖g z - g s₀‖ < ‖g s₀‖ / 2 := by
    have h2 : ball (g s₀) (‖g s₀‖ / 2) ∈ 𝓝 (g s₀) := ball_mem_nhds _ (by positivity)
    filter_upwards [hg.continuousAt h2] with z hz
    simpa [dist_eq_norm] using hz
  obtain ⟨r, hr, hball⟩ :=
    Metric.eventually_nhds_iff_ball.mp (hev.and (hcont.and hg.eventually_analyticAt))
  refine ⟨k, g, r, 2 / ‖g s₀‖, hr, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (hball z hz).2.2.differentiableAt.differentiableWithinAt
  · intro z hz h0
    have h1 := (hball z hz).2.1
    rw [h0, zero_sub, norm_neg] at h1
    linarith
  · intro z hz
    simpa [smul_eq_mul] using (hball z hz).1
  · intro z hz
    have h1 := (hball z hz).2.1
    have hlow : ‖g s₀‖ / 2 ≤ ‖g z‖ := by
      have h3 := norm_sub_norm_le (g s₀) (g z)
      rw [norm_sub_rev] at h3
      linarith
    calc ‖(g z)⁻¹‖ = ‖g z‖⁻¹ := norm_inv _
      _ ≤ (‖g s₀‖ / 2)⁻¹ := inv_anti₀ (by positivity) hlow
      _ = 2 / ‖g s₀‖ := inv_div _ _

def glue (h F A : ℂ → ℂ) (R : ℝ) (z : ℂ) : ℂ := if R < z.re then h z else F z / A z

variable {h F A : ℂ → ℂ} {R : ℝ}

theorem glue_eq (he : ∀ z : ℂ, R < z.re → F z = A z * h z) {z : ℂ} (hz : A z ≠ 0) : glue h F A R z = F z / A z := by
  unfold glue
  split_ifs with c
  · rw [he z c, mul_div_cancel_left₀ _ hz]
  · rfl

theorem glue_eventuallyEq (hA : Differentiable ℂ A) (hne : ∃ z, A z ≠ 0) (he : ∀ z : ℂ, R < z.re → F z = A z * h z) (s : ℂ) :
    glue h F A R =ᶠ[𝓝[≠] s] fun z => F z / A z := by
  have hAn : AnalyticOnNhd ℂ A univ := fun z _ => hA.analyticAt z
  rcases (hA.analyticAt s).eventually_eq_zero_or_eventually_ne_zero with hev | hev
  · exfalso
    obtain ⟨w, hw⟩ := hne
    have := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ s)
      (hev.mono fun z hz => by simp [hz])
    exact hw (by simpa using this (mem_univ w))
  · filter_upwards [hev] with z hz using glue_eq he hz

theorem isMerExt_glue (hA : Differentiable ℂ A) (hne : ∃ z, A z ≠ 0) (hF : Differentiable ℂ F)
    (he : ∀ z : ℂ, R < z.re → F z = A z * h z) : IsMerExt h univ (glue h F A R) := by
  refine ⟨isRightDomain_univ, fun s _ => ?_, ⟨R, fun z hz => ?_⟩⟩
  · have hm : MeromorphicAt (fun z => F z / A z) s :=
      (hF.analyticAt s).meromorphicAt.div (hA.analyticAt s).meromorphicAt
    exact hm.congr (glue_eventuallyEq hA hne he s).symm
  · have hz' : R < z.re := hz
    simp [glue, hz']

theorem cont_eq_div (hA : Differentiable ℂ A) (hne : ∃ z, A z ≠ 0) (hF : Differentiable ℂ F)
    (he : ∀ z : ℂ, R < z.re → F z = A z * h z) {s : ℂ} (hs : A s ≠ 0) : cont h s = F s / A s := by
  have hM := isMerExt_glue hA hne hF he
  have hE : IsExtAt h s (glue h F A R) := hM.isExtAt (mem_univ s)
  have hcont : ContinuousAt (fun z => F z / A z) s :=
    hF.continuous.continuousAt.div hA.continuous.continuousAt hs
  have ht : Tendsto (glue h F A R) (𝓝[≠] s) (𝓝 (F s / A s)) :=
    Tendsto.congr' (glue_eventuallyEq hA hne he s).symm (hcont.tendsto.mono_left nhdsWithin_le_nhds)
  exact (hE.holValueAt_iff.mpr ht).valueAt.cont_eq

theorem div_multiplier : ResidueKilled.Tr.Div := by
  unfold ResidueKilled.Tr.Div
  intro D T e H A R hA hne hH hHc hmul hbd
  unfold GlobalTheory.EisCont.ContMod GlobalTheory.Cont.Continues
  refine ⟨fun g => ⟨_, isMerExt_glue hA hne (hH g) (fun z hz => hmul z hz g)⟩, fun s₀ => ?_⟩
  obtain ⟨k, u, r, M, hr, hu, hu0, hfac, hM⟩ := exists_factor hA hne s₀
  obtain ⟨C, N, hCN⟩ := hbd (‖s₀‖ + r)
  have hu1 : ContinuousOn (fun x : ℂ × _ => u x.1) (ball s₀ r ×ˢ (univ : Set (Formalism.L2.Theta.GA D T))) :=
    hu.continuousOn.comp continuous_fst.continuousOn (fun x hx => hx.1)
  unfold GlobalTheory.EisCont.RegAt
  refine ⟨k, r, fun s g => H s g * (u s)⁻¹, hr, ?_, ?_, ?_, C * M, N, ?_⟩
  · intro s hs hss g
    have hAs : A s = (s - s₀) ^ k * u s := hfac s hs
    have hus : u s ≠ 0 := hu0 s hs
    have hpow : (s - s₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hss)
    have hA0 : A s ≠ 0 := by rw [hAs]; exact mul_ne_zero hpow hus
    show H s g * (u s)⁻¹ = (s - s₀) ^ k * cont (fun z => e z g) s
    rw [cont_eq_div hA hne (hH g) (fun z hz => hmul z hz g) hA0, hAs]
    field_simp
    try ring
  · intro g
    exact (hH g).differentiableOn.mul (hu.inv hu0)
  · exact hHc.continuousOn.mul (hu1.inv₀ (fun x hx => hu0 x.1 hx.1))
  · intro s hs g
    have hs1 : ‖s - s₀‖ < r := by simpa [dist_eq_norm] using hs
    have hs2 := norm_sub_norm_le s s₀
    have hsr : ‖s‖ ≤ ‖s₀‖ + r := by linarith
    have hH1 := hCN s hsr g
    have hM1 := hM s hs
    show ‖H s g * (u s)⁻¹‖ ≤ C * M * GlobalTheory.Grow.height T g ^ N
    calc ‖H s g * (u s)⁻¹‖ = ‖H s g‖ * ‖(u s)⁻¹‖ := norm_mul _ _
      _ ≤ (C * GlobalTheory.Grow.height T g ^ N) * M := mul_le_mul hH1 hM1 (norm_nonneg _) (le_trans (norm_nonneg _) hH1)
      _ = C * M * GlobalTheory.Grow.height T g ^ N := by ring

end GlobalTheory.CompanionTheory.DivMult

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFinSmoothBoth
section
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.KFinSmoothBoth

theorem kFin_smooth_both : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam →
    Formalism.MainNotions.S.IsDS ε lam σ → ∀ v : H, Formalism.MainNotions.S.IsKFin ε σ v →
    v ∈ GlobalTheory.SmoothVecMod.smoothVec ε σ ∧ v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) σ := by
  intro n ε lam H _ _ σ _ hσ v hv
  have : CompleteSpace H := hσ.1
  have h : Formalism.QuantumDeterminants.SmoothOnH (Formalism.REAL.Jm ε) fun g => σ g v :=
    GlobalTheory.Published.KFiniteVectorsUnitary.smoothOnH
      GlobalTheory.CompanionTheory.Published.kFiniteVectors_irreducibleUnitary_unitaryGroupPQ
      hσ.2.2.1 hσ.2.2.2.1 hv
  exact ⟨h, h⟩

end GlobalTheory.CompanionTheory.KFinSmoothBoth
end

