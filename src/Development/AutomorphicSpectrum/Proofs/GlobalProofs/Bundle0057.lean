module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0052
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviNormalizesUnipotentVariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0429
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NcardRationalPointsTranslatedCompactLePow
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.NormInfLeOfEntries
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0042

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothAutomorphicDerivativeGrowth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.SliceReg

variable {D : D7}

theorem exists_lie_oneP {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ) {V V' : HSp D}
    {ι : V'.V →ₗ[D.host.E] V.V} (hι : HSpace.IsIsomEmb V' V ι) {s : GA D V' →* GA D V} (hs : ∀ h, EmbRel V V' ι (s h) h)
    (τ : D.what₂.Tau) {X : Matrix (Fin V'.rank) (Fin V'.rank) ℂ} (hX : X ∈ lieAt V' τ) :
    ∃ Z ∈ lieAt V τ, ∀ t : ℝ, s (oneP θ V' τ X t) = oneP θ V τ Z t := by
  set c := tauE D τ with hc
  set F : Matrix (Fin V.rank) (Fin V'.rank) ℂ := (frameMat V V' ι).map c with hF
  set H := gramAt D V τ with hH
  set H' := gramAt D V' τ with hH'
  have hFH : Fᴴ * H = (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) * V.gram).map c := by
    rw [Matrix.map_mul]
    congr 1
    ext a b
    simp only [F, Matrix.conjTranspose_apply, Matrix.map_apply, Formalism.UG.cT, Matrix.transpose_apply]
    exact (Formalism.IndefR.Eqv.tauE_star D τ _).symm
  have hG := Formalism.L2.GlobalTheoryTheory.VolumeCarry.gram_frameMat D V V' ι hι
  rw [← Formalism.IndefR.Mi.frameMat_eq_global] at hG
  have hFHF : Fᴴ * H * F = H' := by
    rw [hFH, hF, ← Matrix.map_mul, ← hG]; rfl
  have hHu : IsUnit H'.det := GlobalTheory.SmoothAutCheck.gramAt_unit V' τ
  have hHh : H'ᴴ = H' := GlobalTheory.SmoothForms.RealPts.gramAt_herm V' τ
  have hHV : Hᴴ = H := GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ
  have hR1 : H'⁻¹ * H' = 1 := Matrix.nonsing_inv_mul _ hHu
  have hR2 : H' * H'⁻¹ = 1 := Matrix.mul_nonsing_inv _ hHu
  have hRh : (H'⁻¹)ᴴ = H'⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hHh]
  have hXl : Xᴴ * H' + H' * X = 0 := hX
  set Z : Matrix (Fin V.rank) (Fin V.rank) ℂ := F * X * H'⁻¹ * (Fᴴ * H) with hZ
  have hZF : Z * F = F * X := by
    rw [hZ, Matrix.mul_assoc, hFHF, Matrix.mul_assoc, hR1, Matrix.mul_one]
  have hZl : Z ∈ lieAt V τ := by
    change Zᴴ * H + H * Z = 0
    have e1 : Zᴴ * H = H * F * (H'⁻¹ * (Xᴴ * H') * H'⁻¹) * (Fᴴ * H) := by
      rw [hZ]
      simp only [Matrix.conjTranspose_mul, hHV, hRh, Matrix.conjTranspose_conjTranspose]
      have : H'⁻¹ * (Xᴴ * H') * H'⁻¹ = H'⁻¹ * Xᴴ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, hR2, Matrix.mul_one]
      rw [this]
      simp only [Matrix.mul_assoc]
    have e2 : H * Z = H * F * (H'⁻¹ * (H' * X) * H'⁻¹) * (Fᴴ * H) := by
      have : H'⁻¹ * (H' * X) * H'⁻¹ = X * H'⁻¹ := by
        rw [← Matrix.mul_assoc, hR1, Matrix.one_mul]
      rw [this, hZ]
      simp only [Matrix.mul_assoc]
    rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.add_mul, ← Matrix.mul_add, hXl]
    simp
  refine ⟨Z, hZl, fun t => ?_⟩
  have h1 : NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH H' := GlobalTheory.SmoothAutCheck.exp_mem_UH hHu hX t
  have h2 : NormedSpace.exp (t • Z) ∈ Formalism.QuantumDeterminants.UH H :=
    GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) hZl t
  have hE : GlobalTheory.RealBessel.IsEmb H F (NormedSpace.exp (t • Z)) (NormedSpace.exp (t • X)) := by
    refine ⟨GlobalTheory.matrix_exp_smul_mul_eq_mul_exp_smul_of_intertwine _ _ Z F X hZF t, fun x hx => ?_⟩
    have hZx : Z *ᵥ x = 0 := by
      rw [hZ, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
    let W : Matrix (Fin V.rank) (Fin 1) ℂ := Matrix.of fun i _ => x i
    have hW : Z * W = W * (0 : Matrix (Fin 1) (Fin 1) ℂ) := by
      rw [Matrix.mul_zero]
      ext i j
      have := congrFun hZx i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, W] using this
    have h3 := GlobalTheory.matrix_exp_smul_mul_eq_mul_exp_smul_of_intertwine _ _ Z W 0 hW t
    rw [smul_zero, NormedSpace.exp_zero, Matrix.mul_one] at h3
    funext i
    have := congrFun (congrFun h3 i) 0
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, W] using this
  exact GlobalTheory.AutFunCounterexample.embRel_unique V V' ι hι (hs _)
    (GlobalTheory.EmbAtPlace.embRel_atTau D θ hθ V' V ι τ _ _ h1 h2 hE)

theorem foldr_Rder_eq {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ) {V V' : HSp D}
    {ι : V'.V →ₗ[D.host.E] V.V} (hι : HSpace.IsIsomEmb V' V ι) {s : GA D V' →* GA D V} (hs : ∀ h, EmbRel V V' ι (s h) h)
    {y : GA D V} (hy : ∀ h, s h * y = y * s h) (ψ : GA D V → ℂ)
    (l : List (D.what₂.Tau × Matrix (Fin V'.rank) (Fin V'.rank) ℂ)) (hl : ∀ p ∈ l, p.2 ∈ lieAt V' p.1) :
    ∃ l' : List (ℝ → GA D V), (∀ γ ∈ l', IsRealLine D.sp.cm.sig V.gram γ) ∧
      ∀ h, (l.foldr (fun p f => Rder θ V' p.1 p.2 f) (fun h => ψ (s h * y))) h = l'.foldr lineDer ψ (s h * y) := by
  induction l with
  | nil => exact ⟨[], by simp, fun _ => rfl⟩
  | cons p l ih =>
    obtain ⟨l', h1, h2⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    obtain ⟨Z, hZ, e⟩ := exists_lie_oneP hθ hι hs p.1 (hl p List.mem_cons_self)
    refine ⟨oneP θ V p.1 Z :: l', List.forall_mem_cons.2 ⟨GlobalTheory.SphSmooth.isRealLine_oneP hθ V hZ, h1⟩, fun h => ?_⟩
    rw [List.foldr_cons, List.foldr_cons]
    simp only [Rder, lineDer]
    congr 1
    funext t
    rw [h2, map_mul, mul_assoc, hy, ← mul_assoc, e t]

theorem normInf_s_le (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V V' : HSp D}
    {ι : V'.V →ₗ[D.host.E] V.V} (hι : HSpace.IsIsomEmb V' V ι) {s : GA D V' →* GA D V} (hs : ∀ h, EmbRel V V' ι (s h) h)
    (hV : 0 < V'.rank) : ∃ K : ℝ, 0 ≤ K ∧ ∀ g : GA D V', normInf θ V (s g) ≤ K * normInf θ V' g := by
  obtain ⟨C, hC0, hC⟩ := Formalism.IndefR.Mi.s_entry_le θ hι hs
  refine ⟨Fintype.card D.what₂.Tau * (V.rank * (V.rank * (4 * C))), by positivity, fun g => ?_⟩
  have h1 := GlobalTheory.RatCount.one_le_normInf θ hV g
  set b := normInf θ V' g with hb
  have hb0 : 0 ≤ b := by linarith
  have hE : ∀ τ i j, ‖infMat D.sp.cm.sig V'.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V'.gram (θ τ) g⁻¹ i j‖ ≤ b := fun τ i j =>
    (Formalism.IndefR.Mi.entry_le_sum (fun i j => ‖infMat D.sp.cm.sig V'.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V'.gram (θ τ) g⁻¹ i j‖)
      (fun _ _ => by positivity) i j).trans
    (Finset.single_le_sum (f := fun τ => ∑ i, ∑ j, (‖infMat D.sp.cm.sig V'.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V'.gram (θ τ) g⁻¹ i j‖))
      (fun _ _ => by positivity) (Finset.mem_univ τ))
  have a1 : ∀ τ k l, ‖θ τ (Formalism.L2.Theta.infPart D (Formalism.L2.Theta.mt V' g k l))‖ ≤ b := fun τ k l => by
    rw [← Formalism.IndefR.Eqv.infMat_eq]
    linarith [hE τ k l, norm_nonneg (infMat D.sp.cm.sig V'.gram (θ τ) g⁻¹ k l)]
  have a2 : ∀ τ k l, ‖θ τ (Formalism.L2.Theta.infPart D (Formalism.L2.Theta.mt V' g⁻¹ k l))‖ ≤ b := fun τ k l => by
    rw [← Formalism.IndefR.Eqv.infMat_eq]
    linarith [hE τ k l, norm_nonneg (infMat D.sp.cm.sig V'.gram (θ τ) g k l)]
  have hh := Formalism.IndefR.Mi.normInf_le_of_entries θ V (s g) (C * (b + 1)) fun τ i j =>
    ⟨hC g τ b hb0 (a1 τ) i j, by rw [← map_inv]; exact hC g⁻¹ τ b hb0 (a2 τ) i j⟩
  refine hh.trans ?_
  have h4 : C * (b + 1) + C * (b + 1) ≤ 4 * C * b := by nlinarith
  calc (Fintype.card D.what₂.Tau : ℝ) * (V.rank * (V.rank * (C * (b + 1) + C * (b + 1))))
      ≤ (Fintype.card D.what₂.Tau : ℝ) * (V.rank * (V.rank * (4 * C * b))) := by gcongr
    _ = _ := by ring

theorem slice_regular : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∀ (Γ : Set (GA D V)) (ψ : GA D V → ℂ), IsSmModOn D.sp.cm.sig V.gram Γ ψ → ∀ y : GA D V, (∀ h, s h * y = y * s h) → (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V'.rank) (Fin V'.rank) ℂ), (∀ i, Xs i ∈ lieAt V' (τs i)) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => ψ (s (g * (List.ofFn fun i => oneP θ V' (τs i) (Xs i) (t i)).prod) * y)) ∧ ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V'.rank) (Fin V'.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V' p.1) → ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V', ‖(l.foldr (fun p f => Rder θ V' p.1 p.2 f) (fun h => ψ (s h * y))) (x * g)‖ ≤ C * normInf θ V' g ^ N := by
  intro D θ hθ V V' ι hι s hs Γ ψ hψ y hy
  refine ⟨fun k τs Xs hX g => ?_, ?_⟩
  · choose Z hZ e using fun i => exists_lie_oneP hθ hι hs (τs i) (hX i)
    have key := hψ.smooth k (fun i => oneP θ V (τs i) (Z i))
      (fun i => GlobalTheory.SphSmooth.isRealLine_oneP hθ V (hZ i)) (s g * y)
    have e2 : (fun t : Fin k → ℝ => ψ (s (g * (List.ofFn fun i => oneP θ V' (τs i) (Xs i) (t i)).prod) * y)) =
        fun t => ψ (s g * y * (List.ofFn fun i => oneP θ V (τs i) (Z i) (t i)).prod) := by
      funext t
      have e3 : s (List.ofFn fun i => oneP θ V' (τs i) (Xs i) (t i)).prod =
          (List.ofFn fun i => oneP θ V (τs i) (Z i) (t i)).prod := by
        rw [map_list_prod, List.map_ofFn]
        congr 2
        funext i
        exact e i (t i)
      rw [map_mul, mul_assoc, hy, ← mul_assoc, e3]
    rw [e2]
    exact key
  · obtain ⟨N, hN⟩ := hψ.growth
    rcases Nat.eq_zero_or_pos V'.rank with hV | hV
    · refine ⟨0, fun l _ x => ⟨‖(l.foldr (fun p f => Rder θ V' p.1 p.2 f) (fun h => ψ (s h * y))) x‖, fun g _ => ?_⟩⟩
      have hg1 : g = 1 := Subtype.ext (Units.ext (Matrix.ext fun i j => absurd i.2 (by omega)))
      rw [hg1]
      simp
    · obtain ⟨d, hd⟩ := GlobalTheory.Grow.height_le_normInf_pow (θ := θ) V hθ
      obtain ⟨K, hK0, hK⟩ := normInf_s_le θ hι hs hV
      refine ⟨d * N, fun l hl x => ?_⟩
      obtain ⟨l', h1, h2⟩ := foldr_Rder_eq hθ hι hs hy ψ l hl
      obtain ⟨C, hC⟩ := hN l' h1
      refine ⟨|C| * (GlobalTheory.Grow.height V (s x * y) * K ^ d) ^ N, fun g hg => ?_⟩
      have hn : 1 ≤ normInf θ V' g := GlobalTheory.RatCount.one_le_normInf θ hV g
      have hsg := Formalism.IndefR.Mi.s_mem_GinfC hι hs hg
      have hnn : 0 ≤ normInf θ V (s g) := by unfold Formalism.L2.Theta.normInf; positivity
      have b1 : GlobalTheory.Grow.height V (s g) ≤ (K * normInf θ V' g) ^ d :=
        (hd _ hsg).trans (pow_le_pow_left₀ hnn (hK g) d)
      have b2 : GlobalTheory.Grow.height V (s (x * g) * y) ≤ GlobalTheory.Grow.height V (s x * y) * (K * normInf θ V' g) ^ d := by
        have e : s (x * g) * y = s x * y * s g := by rw [map_mul, mul_assoc, hy, ← mul_assoc]
        rw [e]
        exact (GlobalTheory.Grow.height_mul_le V _ _).trans
          (mul_le_mul_of_nonneg_left b1 (GlobalTheory.Grow.height_pos V _).le)
      have h0 : 0 ≤ GlobalTheory.Grow.height V (s (x * g) * y) := (GlobalTheory.Grow.height_pos V _).le
      rw [h2]
      calc _ ≤ C * GlobalTheory.Grow.height V (s (x * g) * y) ^ N := hC _
        _ ≤ |C| * GlobalTheory.Grow.height V (s (x * g) * y) ^ N :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg h0 N)
        _ ≤ |C| * (GlobalTheory.Grow.height V (s x * y) * (K * normInf θ V' g) ^ d) ^ N :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 b2 N) (abs_nonneg C)
        _ = |C| * (GlobalTheory.Grow.height V (s x * y) * K ^ d) ^ N * normInf θ V' g ^ (d * N) := by
            rw [pow_mul, mul_pow K]
            ring

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.SliceReg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.StandardThreeBlockIndex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.ZFin


open Polynomial in
theorem commute_aeval {M : Type} [AddCommGroup M] [Module ℂ M] {T S : Module.End ℂ M} (h : Commute S T) (q : ℂ[X]) :
    Commute S (aeval T q) := by
  rw [Polynomial.aeval_eq_sum_range]
  exact Commute.sum_right _ _ _ fun i _ => (h.pow_right i).smul_right _


open Polynomial in
theorem aeval_modByMonic {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {p : ℂ[X]} {w : M}
    (hw : aeval T p w = 0) (q : ℂ[X]) : aeval T q w = aeval T (q %ₘ p) w := by
  conv_lhs => rw [← Polynomial.modByMonic_add_div q p]
  rw [map_add (f := _), LinearMap.add_apply, mul_comm, map_mul, Module.End.mul_apply, hw, map_zero, add_zero]


open Polynomial in
theorem exists_step {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {p : ℂ[X]} (hp : p.Monic)
    {W : Submodule ℂ M} (hF : W.FG) (hW : ∀ w ∈ W, aeval T p w = 0) :
    ∃ W' : Submodule ℂ M, W'.FG ∧ W ≤ W' ∧ (∀ w ∈ W', T w ∈ W') ∧
      (∀ S : Module.End ℂ M, Commute S T → (∀ w ∈ W, S w ∈ W) → ∀ w ∈ W', S w ∈ W') ∧
      (∀ S : Module.End ℂ M, Commute S T → (∀ w ∈ W, S w = 0) → ∀ w ∈ W', S w = 0) := by
  let B : ℂ[X] →ₗ[ℂ] M →ₗ[ℂ] M := (aeval T).toLinearMap
  have hB : ∀ q w, B q w = aeval T q w := fun _ _ => rfl
  have hdeg : ∀ q : ℂ[X], q %ₘ p ∈ degreeLT ℂ p.natDegree := fun q => by
    rw [Polynomial.mem_degreeLT, ← Polynomial.degree_eq_natDegree hp.ne_zero]
    exact Polynomial.degree_modByMonic_lt q hp
  have hmem : ∀ q, ∀ w ∈ W, aeval T q w ∈ Submodule.map₂ B (degreeLT ℂ p.natDegree) W := fun q w hw => by
    rw [aeval_modByMonic T (hW w hw) q]
    exact Submodule.apply_mem_map₂ B (hdeg q) hw
  have hfg : (degreeLT ℂ p.natDegree).FG := by
    rw [← Module.Finite.iff_fg]
    exact Module.Finite.equiv (Polynomial.degreeLTEquiv ℂ p.natDegree).symm
  refine ⟨Submodule.map₂ B (degreeLT ℂ p.natDegree) W, Submodule.FG.map₂ _ hfg hF, fun w hw => ?_, ?_, ?_, ?_⟩
  · simpa using hmem 1 w hw
  · have : Submodule.map₂ B (degreeLT ℂ p.natDegree) W ≤
        (Submodule.map₂ B (degreeLT ℂ p.natDegree) W).comap T :=
      Submodule.map₂_le.2 fun q _ w hw => by
        have e : T * aeval T q = aeval T (X * q) := by rw [map_mul, Polynomial.aeval_X]
        rw [Submodule.mem_comap, hB, ← Module.End.mul_apply, e]
        exact hmem _ w hw
    exact fun w hw => this hw
  · intro S hS hSW
    have : Submodule.map₂ B (degreeLT ℂ p.natDegree) W ≤
        (Submodule.map₂ B (degreeLT ℂ p.natDegree) W).comap S :=
      Submodule.map₂_le.2 fun q _ w hw => by
        rw [Submodule.mem_comap, hB, ← Module.End.mul_apply, (commute_aeval hS q).eq, Module.End.mul_apply]
        exact hmem _ _ (hSW w hw)
    exact fun w hw => this hw
  · intro S hS hSW
    have : Submodule.map₂ B (degreeLT ℂ p.natDegree) W ≤ LinearMap.ker S :=
      Submodule.map₂_le.2 fun q _ w hw => by
        rw [LinearMap.mem_ker, hB, ← Module.End.mul_apply, (commute_aeval hS q).eq, Module.End.mul_apply,
          hSW w hw, map_zero]
    exact fun w hw => this hw


open Polynomial in
theorem exists_fg_stable {M ι : Type} [AddCommGroup M] [Module ℂ M] [Fintype ι] (T : ι → Module.End ℂ M)
    (p : ι → ℂ[X]) (hp : ∀ i, (p i).Monic) (hc : ∀ i j, Commute (T i) (T j)) (v : M)
    (hv : ∀ i, aeval (T i) (p i) v = 0) :
    ∃ W : Submodule ℂ M, W.FG ∧ v ∈ W ∧ ∀ i, ∀ w ∈ W, T i w ∈ W := by
  classical
  have key : ∀ s : Finset ι, ∃ W : Submodule ℂ M, W.FG ∧ v ∈ W ∧ (∀ i ∈ s, ∀ w ∈ W, T i w ∈ W) ∧
      ∀ i, ∀ w ∈ W, aeval (T i) (p i) w = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨Submodule.span ℂ {v}, Submodule.fg_span_singleton v, Submodule.mem_span_singleton_self v,
        by simp, fun i w hw => ?_⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
      rw [map_smul, hv, smul_zero]
    | insert j s _ ih =>
      obtain ⟨W, hF, hvW, hs, hk⟩ := ih
      obtain ⟨W', hF', hle, hT, hS, hZ⟩ := exists_step (T j) (hp j) hF (hk j)
      refine ⟨W', hF', hle hvW, fun i hi => ?_, fun i => ?_⟩
      · rcases Finset.mem_insert.1 hi with rfl | hi
        · exact hT
        · exact hS _ (hc i j) (hs i hi)
      · exact hZ _ ((commute_aeval (hc j i) (p i)).symm) (hk i)
  obtain ⟨W, hF, hvW, hs, _⟩ := key Finset.univ
  exact ⟨W, hF, hvW, fun i => hs i (Finset.mem_univ i)⟩

section Main

open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.SmoothForms

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

abbrev unitOp (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) : Fin V.rank → Fin V.rank → Module.End ℂ (SmFun θ V) :=
  fun a b => derEnd hθ τ (Matrix.single a b 1)

theorem commute_derEnd_gelfA (hθ : IsInfFam θ) (τ τ' : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (k : ℕ) :
    Commute (derEnd hθ τ Z) (gelfA (unitOp hθ V τ') k) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  have e1 : ∀ g : SmFun θ V, (gelfA (unitOp hθ V τ') k g).1 = gelf θ V τ' k g.1 := fun g => (gelf_eq hθ τ' k g).symm
  have L := linOnSm_gelf (θ := θ) (V := V) τ' k
  refine LinearMap.ext fun f => Subtype.ext ?_
  change RderC θ V τ Z (gelfA (unitOp hθ V τ') k f).1 = (gelfA (unitOp hθ V τ') k (derEnd hθ τ Z f)).1
  rw [e1, e1]
  change _ = gelf θ V τ' k (RderC θ V τ Z f.1)
  simp only [RderC]
  rw [L.add _ (Rder_mem f.2 h1) _ (Submodule.smul_mem _ _ (Rder_mem f.2 h2)), L.smul,
    GlobalTheory.CuspLie.gelf_Rder hθ h1 f.2, GlobalTheory.CuspLie.gelf_Rder hθ h2 f.2]

theorem commute_gelfA (hθ : IsInfFam θ) (τ τ' : D.what₂.Tau) (k k' : ℕ) :
    Commute (gelfA (unitOp hθ V τ) k) (gelfA (unitOp hθ V τ') k') := by
  refine Commute.sum_left _ _ _ fun idx _ => Commute.list_prod_left _ _ fun x hx => ?_
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hx
  exact commute_derEnd_gelfA hθ τ τ' _ k'


open Polynomial in
theorem foldr_gelf_eq (hθ : IsInfFam θ) (τ : D.what₂.Tau) (k : ℕ) (φ : SmFun θ V) (L : List ℂ) :
    L.foldr (fun a f => gelf θ V τ k f - a • f) φ.1 =
      (aeval (gelfA (unitOp hθ V τ) k) ((L.map fun a => (X - C a : ℂ[X])).prod) φ).1 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    rw [ih, gelf_eq hθ τ k, map_mul, map_sub, aeval_X, aeval_C, Module.End.mul_apply, LinearMap.sub_apply,
      Module.algebraMap_end_apply]
    rfl

open Polynomial in
theorem monic_prod_roots (L : List ℂ) : ((L.map fun a => (X - C a : ℂ[X])).prod).Monic := by
  induction L with
  | nil => simp
  | cons a L ih => simpa using (monic_X_sub_C a).mul ih

end Main

end GlobalTheory.CompanionTheory.ZFin


open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.SmoothForms GlobalTheory.CompanionTheory.ZFin in
open Polynomial in
theorem GlobalTheory.CompanionTheory.ZFin.isAutFunSm_of_gelf_roots : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ), IsAutFun V φ → (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) → (∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V, ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) (x * g)‖ ≤ C * normInf θ V g ^ N) → (∀ τ k, ∃ L : List ℂ, L.foldr (fun a f => gelf θ V τ k f - a • f) φ = 0) → IsAutFunSm θ V φ := by
  intro D θ hθ V φ hA hs hg hz
  choose L hL using hz
  have hsm : φ ∈ SmFun θ V := hs
  obtain ⟨W, hF, hv, hS⟩ := exists_fg_stable (ι := D.what₂.Tau × Fin V.rank)
    (fun i => gelfA (unitOp hθ V i.1) i.2.val)
    (fun i => ((L i.1 i.2.val).map fun a => (X - C a : ℂ[X])).prod)
    (fun i => monic_prod_roots _) (fun i j => commute_gelfA hθ _ _ _ _) ⟨φ, hsm⟩
    (fun i => Subtype.ext ((foldr_gelf_eq hθ i.1 i.2.val ⟨φ, hsm⟩ _).symm.trans (hL _ _)))
  refine { toIsAutFun := hA, smooth := hs, growth := hg,
           zfin := ⟨W.map (SmFun θ V).subtype, Module.Finite.iff_fg.2 (hF.map _), ⟨⟨φ, hsm⟩, hv, rfl⟩, ?_⟩ }
  rintro τ k _ ⟨f, hf, rfl⟩
  have hstab : ∀ x ∈ Algebra.adjoin ℂ (Set.range fun k : Fin V.rank => gelfA (unitOp hθ V τ) k.val),
      ∀ w ∈ W, x w ∈ W := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact hS (τ, j)
    | algebraMap r =>
      intro w hw
      simpa using W.smul_mem r hw
    | add x y _ _ hx hy => exact fun w hw => add_mem (hx w hw) (hy w hw)
    | mul x y _ _ hx hy => exact fun w hw => hx _ (hy w hw)
  exact ⟨_, hstab _ (gelfA_mem_adjoin_low _ _ _ (GlobalTheory.Mem.Lift.glRel_derEnd hθ V τ) k) f hf, (gelf_eq hθ τ k f).symm⟩

end
end

