module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2732
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0179
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0656
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0553
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0552
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0551
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0528
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFormSiegelBound
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0608
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0720
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1743
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0761

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterQuadraticFormIdentity
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RCellP

variable {D : D7} {n r t : ℕ}

theorem maj_mem {θ : InfFam D} {a b : ℕ} {φ : Mx D a b → ℂ} (hφ : φ ∈ schwartzA θ a b) :
    ∃ F ∈ schwartzA θ a b, ∀ x, (F x).im = 0 ∧ ‖φ x‖ ≤ (F x).re := by
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨F₀, hF₀⟩ := _root_.GlobalTheory.CompanionTheory.SchwartzMaj.exists_nonneg_schwartz_majorant _ f
    refine ⟨fun x => F₀ (fun τ i j => compAt θ τ x i j) * (fun u => ((‖g u‖ : ℝ) : ℂ)) (fun i j => finPart D (x i j)),
      Submodule.subset_span ⟨F₀, fun u => ((‖g u‖ : ℝ) : ℂ), ⟨?_, ?_⟩, rfl⟩, fun x => ?_⟩
    · exact hg.1.comp fun z => ((‖z‖ : ℝ) : ℂ)
    · exact hg.2.comp_left (g := fun z => ((‖z‖ : ℝ) : ℂ)) (by simp)
    · have h := hF₀ (fun τ i j => compAt θ τ x i j)
      constructor
      · simp [Complex.mul_im, h.1]
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, norm_mul]
        exact mul_le_mul_of_nonneg_right h.2 (norm_nonneg _)
  | zero => exact ⟨0, Submodule.zero_mem _, fun x => by simp⟩
  | add φ₁ φ₂ _ _ h₁ h₂ =>
    obtain ⟨F₁, m₁, e₁⟩ := h₁
    obtain ⟨F₂, m₂, e₂⟩ := h₂
    refine ⟨F₁ + F₂, Submodule.add_mem _ m₁ m₂, fun x => ⟨?_, ?_⟩⟩
    · simp [(e₁ x).1, (e₂ x).1]
    · simpa using (norm_add_le _ _).trans (add_le_add (e₁ x).2 (e₂ x).2)
  | smul c φ _ h =>
    obtain ⟨F, m, e⟩ := h
    refine ⟨((‖c‖ : ℝ) : ℂ) • F, Submodule.smul_mem _ _ m, fun x => ⟨?_, ?_⟩⟩
    · simp [(e x).1]
    · simpa [norm_smul] using mul_le_mul_of_nonneg_left (e x).2 (norm_nonneg c)

theorem exists_real_schwartz_majorant {θ : InfFam D} {a b : ℕ} (Φ : schwartzA θ a b) :
    ∃ F : schwartzA θ a b, ∀ x, (F.1 x).im = 0 ∧ ‖Φ.1 x‖ ≤ (F.1 x).re :=
  let ⟨F, m, e⟩ := maj_mem Φ.2
  ⟨⟨F, m⟩, e⟩

theorem c_jn_cont (hn : r + t = n) {a : ℕ} : Continuous (fun z : Mx D a r × Mx D a t => jn hn z.1 z.2) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun z : Mx D a r × Mx D a t => Matrix.fromCols z.1 z.2 i ((finSumFinEquiv.trans (finCongr hn)).symm j)
  generalize (finSumFinEquiv.trans (finCongr hn)).symm j = c
  rcases c with c | c
  · exact continuous_fst.matrix_elem i c
  · exact continuous_snd.matrix_elem i c

theorem inner_product_mul_eq_pairing (V : HSp D) (b₀ : HermE D r) (hb : b₀.1.det ≠ 0) (x : Mx D V.rank r) (v : Mx D V.rank t) (y : Mx D r t) :
    ip V (mm x y) v = pr b₀ y (yv V b₀ (x, v)) := by
  have h1 : (b₀.1.map (incA D) : Mx D r r) * rat b₀.1⁻¹ = 1 := by
    show b₀.1.map (incA D) * b₀.1⁻¹.map (incA D) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (Ne.isUnit hb)]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  simp only [ip, pr, yv, mm, adj_mul]
  rw [← Matrix.mul_assoc (b₀.1.map (incA D)), h1, Matrix.one_mul, Matrix.mul_assoc]

theorem conj_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (u : AF D.host.F) : conj (ψ u) = ψ (-u) := by
  have h1 : ψ u * conj (ψ u) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ.2.1 u]
    simp
  have h2 : ψ u * ψ (-u) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h0 : ψ u ≠ 0 := fun h => by simp [h] at h1
  exact mul_left_cancel₀ h0 (h1.trans h2.symm)

theorem character_quadratic_form_identity (V : HSp D) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D r) (b : hermA D t)
    (z : Mx D V.rank r × Mx D V.rank t) :
    pch ψ b.1 (ip V z.2 z.2) * conj (ψ (halfTr (Matrix.trace (mm b.1 (pr b₀ (yv V b₀ z) (yv V b₀ z)))))) = pch ψ b.1 (qv V b₀ z) := by
  rw [conj_psi hψ]
  simp only [pch, qv, mm]
  rw [← AddChar.map_add_eq_mul, Matrix.mul_sub, Matrix.trace_sub]
  congr 1
  simp only [halfTr, trA, map_sub]
  ring

theorem integrable_schwartz_slice {θ : InfFam D} (hθ : IsInfFam θ) {a : ℕ} (hn : r + t = n) (μt : Measure (Mx D a t)) [μt.IsAddHaarMeasure]
    (Φ : schwartzA θ a n) (x : Mx D a r) : Integrable (fun v => Φ.1 (jn hn x v)) μt := _root_.GlobalTheory.CompanionTheory.ColSlice.integrable_slice hθ hn μt Φ x

theorem fub {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure Y} {ν : Measure X} [SFinite μ] [SFinite ν]
    {P : X → ℂ} {e : Y → X → ℂ} {O : Y → ℂ} (hP : Integrable P ν) (hO : Integrable O μ)
    (he : AEStronglyMeasurable (fun q : Y × X => e q.1 q.2) (μ.prod ν)) (hn : ∀ y z, ‖e y z‖ = 1)
    (hem : ∀ y, AEStronglyMeasurable (e y) ν) :
    (∀ y, Integrable (fun z => P z * e y z) ν) ∧
    ∫ y, (∫ z, P z * e y z ∂ν) * O y ∂μ = ∫ z, P z * ∫ y, e y z * O y ∂μ ∂ν := by
  have hIPe : ∀ y, Integrable (fun z => P z * e y z) ν := fun y =>
    hP.mono (hP.aestronglyMeasurable.mul (hem y)) (ae_of_all _ fun z => by simp [hn])
  refine ⟨hIPe, ?_⟩
  have hbase := Integrable.mul_prod hO hP
  have hIF : Integrable (Function.uncurry fun (y : Y) z => P z * e y z * O y) (μ.prod ν) := by
    refine hbase.mono ?_ (ae_of_all _ fun q => ?_)
    · exact (hP.aestronglyMeasurable.comp_snd.mul he).mul hO.aestronglyMeasurable.comp_fst
    · simp [Function.uncurry, hn, mul_comm]
  calc ∫ y, (∫ z, P z * e y z ∂ν) * O y ∂μ = ∫ y, ∫ z, P z * e y z * O y ∂ν ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        beta_reduce
        rw [integral_mul_const]
    _ = ∫ z, ∫ y, P z * e y z * O y ∂μ ∂ν := integral_integral_swap hIF
    _ = _ := by
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        beta_reduce
        simp only [mul_assoc]
        rw [integral_const_mul]

theorem integrable_fib (hP : PartFT) {hn : r + t = n} (M : Maps D hn) (m : Meas D r t) (V : HSp D) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : ResEta D χ V.rank) {θ : InfFam D}
    (hθ : IsInfFam θ) {μ : Measure (Mx D V.rank n)} (hμ : ∃ 𝓕, IsCovolOne (ratMx D V.rank n) μ 𝓕)
    {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    {μr : Measure (Mx D V.rank r)} (hμr : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μr 𝓕)
    {μt : Measure (Mx D V.rank t)} (hμt : ∃ 𝓕, IsCovolOne (ratMx D V.rank t) μt 𝓕)
    (b₀ : HermE D r) {fib : Measure (Mx D V.rank r)} (hfib : IsFib ψ θ V b₀ μr m.lz fib)
    (Φ : schwartzA θ V.rank n) {w : G D t} (hw : IsW w) :
    Integrable (fun z => Φ.1 (jn hn z.1 z.2)) (fib.prod μt) := by
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D V.rank r
  obtain ⟨j1, j2, j3, j4, -⟩ := lattice_Mx D V.rank t
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : BorelSpace (Mx D V.rank t) := ⟨rfl⟩
  haveI := hfib.fin
  haveI := hμt.choose_spec.1
  obtain ⟨F, hF⟩ := exists_real_schwartz_majorant Φ
  have hPa := hP D n r t hn M V ψ hψ χ hχ hη θ hθ μ hμ ω hω μr μt hμr hμt
  have hm : ∀ x, ∫ v, F.1 (jn hn x v) ∂μt = (ω (M.emb w) F).1 (jn hn x 0) := by
    intro x
    rw [(hPa F).2.2 w hw x 0]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    have : ip V (0 : Mx D V.rank t) v = 0 := by
      simp [ip, mm, adj]
    simp [this]
  have hφ := (hPa (ω (M.emb w) F)).2.1
  have hint := (hfib.int _ hφ).1
  have hcF : Continuous fun z : Mx D V.rank r × Mx D V.rank t => F.1 (jn hn z.1 z.2) :=
    (GlobalTheory.RegSch.CentreWeilComm.continuous_of_mem hθ F).comp (c_jn_cont hn)
  have hcΦ : Continuous fun z : Mx D V.rank r × Mx D V.rank t => Φ.1 (jn hn z.1 z.2) :=
    (GlobalTheory.RegSch.CentreWeilComm.continuous_of_mem hθ Φ).comp (c_jn_cont hn)
  have hIF : Integrable (fun z : Mx D V.rank r × Mx D V.rank t => F.1 (jn hn z.1 z.2)) (fib.prod μt) := by
    refine (integrable_prod_iff hcF.aestronglyMeasurable).2 ⟨ae_of_all _ fun x => integrable_schwartz_slice hθ hn μt F x, ?_⟩
    refine (hint.re).congr (ae_of_all _ fun x => ?_)
    have e1 : ∀ v, ‖F.1 (jn hn x v)‖ = (F.1 (jn hn x v)).re := by
      intro v
      have h := hF (jn hn x v)
      have h0 : 0 ≤ (F.1 (jn hn x v)).re := (norm_nonneg _).trans h.2
      rw [← Complex.re_add_im (F.1 (jn hn x v)), h.1]
      simp [abs_of_nonneg h0]
    simp only [e1]
    show (RCLike.re ((ω (M.emb w) F).1 (jn hn x 0))) = _
    rw [← hm x]
    exact (integral_re (integrable_schwartz_slice hθ hn μt F x)).symm
  exact hIF.mono hcΦ.aestronglyMeasurable (ae_of_all _ fun z =>
    (hF _).2.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _)))

theorem core (hP : PartFT) {hn : r + t = n} (M : Maps D hn) (m : Meas D r t) (V : HSp D) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : ResEta D χ V.rank) {θ : InfFam D}
    (hθ : IsInfFam θ) {μ : Measure (Mx D V.rank n)} (hμ : ∃ 𝓕, IsCovolOne (ratMx D V.rank n) μ 𝓕)
    {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    {μr : Measure (Mx D V.rank r)} (hμr : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μr 𝓕)
    {μt : Measure (Mx D V.rank t)} (hμt : ∃ 𝓕, IsCovolOne (ratMx D V.rank t) μt 𝓕)
    (b₀ : HermE D r) (hb : b₀.1.det ≠ 0) {fib : Measure (Mx D V.rank r)} (hfib : IsFib ψ θ V b₀ μr m.lz fib)
    {Ω : G D t → Mx D r t → ℂ} (hΩ : IsTh ψ χ θ b₀ m.μ Ω)
    (Φ : schwartzA θ V.rank n) {nb : hermA D t → G D t} (hnb : IsNMap nb) {w : G D t} (hw : IsW w) (b : hermA D t)
    (hI : Integrable (fun z => Φ.1 (jn hn z.1 z.2)) (fib.prod μt)) :
    Rsec M m ψ b₀ (fun g => (ω g Φ).1 0) 1 Ω (w * nb b) =
        ∫ z, Φ.1 (jn hn z.1 z.2) * conj (Ω 1 (yv V b₀ z)) * pch ψ b.1 (qv V b₀ z) ∂(fib.prod μt) := by
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D V.rank r
  obtain ⟨j1, j2, j3, j4, -⟩ := lattice_Mx D V.rank t
  obtain ⟨k1, k2, k3, k4, -⟩ := lattice_Mx D r t
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : BorelSpace (Mx D V.rank t) := ⟨rfl⟩
  haveI : BorelSpace (Mx D r t) := ⟨rfl⟩
  haveI := hfib.fin
  haveI := hμt.choose_spec.1
  haveI := m.hμ.1
  obtain ⟨hc1, hc2, hc3, hc4, hn1, hn2⟩ := _root_.GlobalTheory.CompanionTheory.RCellCont.continuity_characters_projection (t := t) hψ V b₀ b
  have hcΦ : Continuous fun z : Mx D V.rank r × Mx D V.rank t => Φ.1 (jn hn z.1 z.2) :=
    (GlobalTheory.RegSch.CentreWeilComm.continuous_of_mem hθ Φ).comp (c_jn_cont hn)
  have hcP : Continuous fun z : Mx D V.rank r × Mx D V.rank t => pch ψ b.1 (ip V z.2 z.2) * Φ.1 (jn hn z.1 z.2) := hc1.mul hcΦ
  have hIP : Integrable (fun z : Mx D V.rank r × Mx D V.rank t => pch ψ b.1 (ip V z.2 z.2) * Φ.1 (jn hn z.1 z.2)) (fib.prod μt) :=
    hI.mono hcP.aestronglyMeasurable (ae_of_all _ fun z => by simp [hn1])
  have hcΩ : Continuous (Ω (w * nb b)) := hΩ.cont.comp (continuous_const.prodMk continuous_id)
  have hIΩ : Integrable (fun y => conj (Ω (w * nb b) y)) m.μ :=
    (GlobalTheory.RegSch.CentreWeilComm.integrable_of_mem hθ m.μ ⟨_, hΩ.mem (w * nb b)⟩).mono
      (Complex.continuous_conj.comp hcΩ).aestronglyMeasurable (ae_of_all _ fun y => by simp)
  obtain ⟨hIPe, hsw⟩ := fub (μ := m.μ) (ν := fib.prod μt) (e := fun y z => ψ (trA (Matrix.trace (pr b₀ y (yv V b₀ z))))) hIP hIΩ
    hc3.aestronglyMeasurable (fun y z => hn2 _)
    (fun y => (hc3.comp (Continuous.prodMk_right y)).aestronglyMeasurable)
  have hW : ∀ y, Wz M m ψ b₀ (fun g => (ω g Φ).1 0) (M.sh y * M.emb (w * nb b) * 1) =
      ∫ z, pch ψ b.1 (ip V z.2 z.2) * Φ.1 (jn hn z.1 z.2) * ψ (trA (Matrix.trace (pr b₀ y (yv V b₀ z)))) ∂(fib.prod μt) := by
    intro y
    rw [_root_.GlobalTheory.CompanionTheory.WzFib.wz_eq_fib hP M m V hψ hχ hη hθ hμ hω hμr hμt b₀ hfib Φ, integral_prod _ (hIPe y)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    beta_reduce
    rw [_root_.GlobalTheory.CompanionTheory.CellVal.weil_translate_frame hP M V hψ hχ hη hθ hμ hω hμr hμt Φ hnb hw b y x]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    beta_reduce
    rw [inner_product_mul_eq_pairing V b₀ hb x v y]
  unfold Rsec
  simp only [hW]
  rw [hsw]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  beta_reduce
  rw [_root_.GlobalTheory.CompanionTheory.RCellInv.fourier_inv hψ hχ hΩ hnb hw b (yv V b₀ z), map_mul, ← character_quadratic_form_identity V hψ b₀ b z]
  ring

theorem rcell : WMaj → PartFT → RCell := by
  intro _ hP D n t B W d hn ψ χ θ μB μW ωB ωW hS M m b₀ hb μr μt hμr hμt fib hfib Ω hΩ Φ nb hnb w hw
  obtain ⟨𝓕, h𝓕⟩ := hS.hμB
  have hn0 : 0 < n := by
    have := hS.pos
    have := hS.lt
    omega
  have hη : ResEta D χ B.rank := GlobalTheory.RegSch.JointCont.resEta_of_isWeilSch hn0 hS.hψ hS.hθ h𝓕 hS.hB
  have hI := integrable_fib hP M m B hS.hψ hS.hχ hη hS.hθ ⟨𝓕, h𝓕⟩ hS.hB hμr hμt b₀ hfib Φ hw
  exact ⟨hI, fun b => core hP M m B hS.hψ hS.hχ hη hS.hθ ⟨𝓕, h𝓕⟩ hS.hB hμr hμt b₀ hb hfib hΩ Φ hnb hw b hI⟩

end GlobalTheory.CompanionTheory.RCellP

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFormSiegelBoundStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_form_siegel_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (K : Subgroup (GAd σ J)) (Ω : Set (GAd σ J)) (c : ℝ), IsCompact (K : Set (GAd σ J)) → IsCompact Ω → Ω ⊆ minParOne σ J X → 0 < c → ∃ (C : ℝ≥0) (A : ℕ), ∀ g ∈ siegelSet σ J X Y Ω c K, ∀ γ ∈ ratPts σ J, height σ J g ≤ C * height σ J (γ * g) ^ A := by
  first | exact @GlobalTheory.CompanionTheory.SiegelHt.height_le_pow | exact GlobalTheory.CompanionTheory.SiegelHt.height_le_pow | (intros; apply GlobalTheory.CompanionTheory.SiegelHt.height_le_pow <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHaarUnipotentRadicalConjScaling
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.QKAvg.RadMeas

variable {D : D7} {B W : HSp D} {t : ℕ}

theorem absDet_eq (d : HypDec B W t) (m : GlobalTheory.RegSW.stab d) (g : GA D W) (a : GL (Fin t) (AE D))
    (hm : (m : GA D B) = d.emb0 g * d.levi a) :
    GlobalTheory.RegSW.absDet d m = absA D (Matrix.GeneralLinearGroup.det a) := by
  have h : mt B (m : GA D B) ⬝ d.jX = d.jX ⬝ a.1 := by
    rw [hm, mt_mul, Matrix.mul_assoc, d.levi_jX, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX]
  have e : GlobalTheory.RegSW.onX d m = a :=
    Units.ext ((GlobalTheory.RegSW.eq_of_mul_jX d (GlobalTheory.RegSW.mul_jX d m)).trans (GlobalTheory.RegSW.eq_of_mul_jX d h).symm)
  simp only [GlobalTheory.RegSW.absDet, MonoidHom.comp_apply, e]

theorem regular_of_haar {A : Type} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.IsAddHaarMeasure] : μ.Regular := inferInstance

theorem sFinite_of_haar {A : Type} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.IsAddHaarMeasure] : SFinite μ := inferInstance


set_option maxHeartbeats 1000000 in
theorem map_lr {n : ℕ} (a : GL (Fin t) (AE D)) (h : GL (Fin n) (AE D))
    (hh : absA D (Matrix.GeneralLinearGroup.det h) = 1) (β : Measure (Mx D t n)) (hβ : β.IsAddHaarMeasure) :
    β.map (fun b : Mx D t n => (a.1 ⬝ b ⬝ h.1 : Mx D t n)) =
      ((absA D (Matrix.GeneralLinearGroup.det a) ^ n)⁻¹ : ℝ≥0) • β := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D t n
  haveI : IsTopologicalAddGroup (Mx D t n) := i1
  haveI : LocallyCompactSpace (Mx D t n) := i2
  haveI : SecondCountableTopology (Mx D t n) := i3
  haveI : T2Space (Mx D t n) := i4
  haveI : BorelSpace (Mx D t n) := ⟨rfl⟩
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  let φ := GlobalTheory.ModuLR.lrCE a h
  have hc : addEquivAddHaarChar φ = absA D (Matrix.GeneralLinearGroup.det a) ^ n *
      absA D (Matrix.GeneralLinearGroup.det h) ^ t :=
    GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE D.host.F D.host.E D.sp.cm.sig (isCMExt_host D) t n a h
  rw [hh, one_pow, mul_one] at hc
  have e : (fun b : Mx D t n => (a.1 ⬝ b ⬝ h.1 : Mx D t n)) = φ :=
    funext fun y => (GlobalTheory.ModuLR.lrCE_apply a h y).symm
  have hA : absA D (Matrix.GeneralLinearGroup.det a) ^ n ≠ 0 := pow_ne_zero _ ((Group.isUnit _).map (absA D)).ne_zero
  haveI := regular_of_haar β
  have key := addEquivAddHaarChar_smul_map β φ
  rw [e, ← hc]
  rw [← hc] at hA
  conv_rhs => rw [← key]
  rw [smul_smul, inv_mul_cancel₀ hA, one_smul]


set_option maxHeartbeats 1000000 in
theorem exists_radN_measure (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) [LocallyCompactSpace (radN d)] :
    ∃ νN : Measure (radN d), νN.IsHaarMeasure ∧ νN.IsMulRightInvariant ∧ ∀ m ∈ levM d,
      νN.map (fun n : radN d => MulAut.conjNormal m n) =
        ((GlobalTheory.RegSW.absDet d m ^ (W.rank + t))⁻¹ : ℝ≥0) • νN := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D t W.rank
  obtain ⟨j1, j2, j3, j4, -, -⟩ := lattice_Mx D t t
  haveI : IsTopologicalAddGroup (Mx D t W.rank) := i1
  haveI : LocallyCompactSpace (Mx D t W.rank) := i2
  haveI : SecondCountableTopology (Mx D t W.rank) := i3
  haveI : T2Space (Mx D t W.rank) := i4
  haveI : BorelSpace (Mx D t W.rank) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (Mx D t t) := j1
  haveI : LocallyCompactSpace (Mx D t t) := j2
  haveI : SecondCountableTopology (Mx D t t) := j3
  haveI : T2Space (Mx D t t) := j4
  haveI : BorelSpace (Mx D t t) := ⟨rfl⟩
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hcl : IsClosed (skewA D t : Set (Mx D t t)) := isClosed_eq continuous_adj continuous_neg
  haveI : LocallyCompactSpace (skewA D t) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : BorelSpace (skewA D t) := Subtype.borelSpace _
  haveI : T2Space (skewA D t) := inferInstance
  haveI : SecondCountableTopology (skewA D t) :=
    hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  let κ : Measure (skewA D t) := Measure.addHaar
  let β : Measure (Mx D t W.rank) := Measure.addHaar
  haveI hκ : κ.IsAddHaarMeasure := inferInstance
  haveI hβ : β.IsAddHaarMeasure := inferInstance
  haveI := sFinite_of_haar κ
  haveI := sFinite_of_haar β
  obtain ⟨Ψ, hΨ, hH, hR⟩ := GlobalTheory.T.unipotent_radical_haar_from_product D B W t d κ β hκ hβ
  refine ⟨(κ.prod β).map Ψ, hH, hR, ?_⟩
  rintro m ⟨g, a, hm⟩
  let f₁ : skewA D t → skewA D t := skewConj a.1
  let f₂ : Mx D t W.rank → Mx D t W.rank := fun b => (a.1 ⬝ b ⬝ (matHom W g⁻¹).1 : Mx D t W.rank)
  have hf₁ : Continuous f₁ := Continuous.subtype_mk
    ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _
  have hf₂ : Continuous f₂ := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hL : ∀ n : radN d, (((MulAut.conjNormal m n : radN d) : GlobalTheory.RegSW.stab d) : GA D B) =
      (m : GA D B) * ((n : GlobalTheory.RegSW.stab d) : GA D B) * (m : GA D B)⁻¹ := fun n => by
    rw [MulAut.conjNormal_apply]
    rfl
  have hconj : ∀ p, MulAut.conjNormal m (Ψ p) = Ψ (Prod.map f₁ f₂ p) := by
    rintro ⟨c, b⟩
    apply Subtype.ext
    apply Subtype.ext
    refine (hL _).trans ?_
    rw [hΨ (c, b), hΨ (Prod.map f₁ f₂ (c, b)), hm]
    exact conj_coord d g a c b
  have hcm : Measurable fun n : radN d => MulAut.conjNormal m n := by
    have : (fun n : radN d => MulAut.conjNormal m n) = Ψ ∘ Prod.map f₁ f₂ ∘ Ψ.symm := by
      funext n
      simp only [Function.comp]
      rw [← hconj, Ψ.apply_symm_apply]
    rw [this]
    exact (Ψ.continuous.comp ((hf₁.prodMap hf₂).comp Ψ.symm.continuous)).measurable
  have hk := GlobalTheory.T.haar_skew_matrices_conj_scaling D t κ hκ a
  have hb := map_lr a (matHom W g⁻¹) (GlobalTheory.CompanionTheory.HyperbolicDecompositionLaw.absA_det_matHom g⁻¹) β hβ
  rw [Measure.map_map hcm Ψ.continuous.measurable]
  have hc : (fun n : radN d => MulAut.conjNormal m n) ∘ Ψ = Ψ ∘ Prod.map f₁ f₂ := by
    funext p
    exact hconj p
  rw [hc, ← Measure.map_map Ψ.continuous.measurable (hf₁.prodMap hf₂).measurable,
    ← Measure.map_prod_map κ β hf₁.measurable hf₂.measurable]
  change (((κ.map (skewConj a.1)).prod (β.map _)).map Ψ) = _
  rw [hk, hb, Measure.prod_smul_left, Measure.prod_smul_right, Measure.map_smul, Measure.map_smul, smul_smul,
    absDet_eq d m g a hm, pow_add, mul_inv, mul_comm]
  all_goals exact Ψ.continuous.measurable.aemeasurable

end GlobalTheory.CompanionTheory.QKAvg.RadMeas
end
end

