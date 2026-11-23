module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0191
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveSolutionExistence
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0196
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0203
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0326

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivTwoSmul
section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff Topology
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK GlobalTheory.CompanionTheory.WaveK.Base
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveK.Lin

variable {n : ℕ}

section Ops

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Eu_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (a b : Fin n) :
    ContDiffOn ℝ ∞ (Eu s a b f) (GLs n) := by
  have h := fun X : Mat n => GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hf
  unfold Eu
  exact ((h _).add (contDiffOn_const.smul (h _))).const_smul _

theorem Epow_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, ContDiffOn ℝ ∞ (Epow s m a b f) (GLs n) := by
  induction m with
  | zero =>
    intro a b
    by_cases hab : a = b
    · simpa [Epow, hab] using hf
    · simp only [Epow, if_neg hab]
      exact contDiffOn_const (c := (0 : V))
  | succ m ih =>
    intro a b
    have e : Epow s (m + 1) a b f = fun x => ∑ c, Eu s a c (Epow s m c b f) x := by
      ext x
      simp only [Epow, Finset.sum_apply]
    rw [e]
    exact ContDiffOn.sum fun c _ => Eu_smooth (ih c b) s a c

theorem Eu_add {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n)) (s : Bool)
    (a b : Fin n) : Set.EqOn (Eu s a b (f + f')) (Eu s a b f + Eu s a b f') (GLs n) := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply, GlobalTheory.CompanionTheory.RCalc.Rd_add _ hf hf' hx, smul_add]
  abel

theorem Eu_smul (c : ℂ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (a b : Fin n) :
    Set.EqOn (Eu s a b (c • f)) (c • Eu s a b f) (GLs n) := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply, GlobalTheory.CompanionTheory.RCalc.Rd_smul c _ hf hx]
  module

theorem Epow_add {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n))
    (s : Bool) (m : ℕ) : ∀ a b : Fin n, Set.EqOn (Epow s m a b (f + f')) (Epow s m a b f + Epow s m a b f') (GLs n) := by
  induction m with
  | zero =>
    intro a b x hx
    by_cases hab : a = b <;> simp [Epow, hab]
  | succ m ih =>
    intro a b x hx
    simp only [Epow, Finset.sum_apply, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [GlobalTheory.CompanionTheory.WaveAll.Eu_congr GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs (ih c b) s a c hx]
    exact Eu_add (Epow_smooth hf s m c b) (Epow_smooth hf' s m c b) s a c hx

theorem Epow_smul (k : ℂ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, Set.EqOn (Epow s m a b (k • f)) (k • Epow s m a b f) (GLs n) := by
  induction m with
  | zero =>
    intro a b x hx
    by_cases hab : a = b <;> simp [Epow, hab]
  | succ m ih =>
    intro a b x hx
    simp only [Epow, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [GlobalTheory.CompanionTheory.WaveAll.Eu_congr GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs (ih c b) s a c hx]
    exact Eu_smul k (Epow_smooth hf s m c b) s a c hx

theorem gel_add {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n))
    (s : Bool) (m : ℕ) : Set.EqOn (gel s m (f + f')) (gel s m f + gel s m f') (GLs n) := by
  intro x hx
  simp only [gel, Finset.sum_apply, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => Epow_add hf hf' s m a a hx

theorem gel_smul (k : ℂ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (m : ℕ) :
    Set.EqOn (gel s m (k • f)) (k • gel s m f) (GLs n) := by
  intro x hx
  simp only [gel, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => Epow_smul k hf s m a a hx

theorem Om_add {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n)) :
    Set.EqOn (Om (f + f')) (Om f + Om f') (GLs n) := by
  intro x hx
  simp only [Om, Pi.smul_apply, Pi.add_apply, gel_add hf hf' _ _ hx, smul_add]
  abel

theorem Om_smul (k : ℂ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Om (k • f)) (k • Om f) (GLs n) := by
  intro x hx
  simp only [Om, Pi.smul_apply, Pi.add_apply, gel_smul k hf _ _ hx]
  module

theorem iterated_integral_add {w w' : ℝ → V} (hw : ContDiff ℝ ∞ w) (hw' : ContDiff ℝ ∞ w') (t : ℝ) :
    iteratedDeriv 2 (fun s => w s + w' s) t = iteratedDeriv 2 w t + iteratedDeriv 2 w' t := by
  have h2 : ∀ φ : ℝ → V, iteratedDeriv 2 φ = deriv (deriv φ) := fun φ => by
    rw [iteratedDeriv_eq_iterate]; rfl
  have hd : deriv (fun s => w s + w' s) = fun s => deriv w s + deriv w' s :=
    funext fun s => deriv_fun_add (hw.differentiable (by simp) s) (hw'.differentiable (by simp) s)
  have e1 : Differentiable ℝ (deriv w) := (contDiff_infty_iff_deriv.1 hw).2.differentiable (by simp)
  have e2 : Differentiable ℝ (deriv w') := (contDiff_infty_iff_deriv.1 hw').2.differentiable (by simp)
  rw [h2, h2, h2, hd]
  exact deriv_fun_add (e1 t) (e2 t)

theorem iteratedDeriv_two_smul (k : ℂ) {w : ℝ → V} (hw : ContDiff ℝ ∞ w) (t : ℝ) :
    iteratedDeriv 2 (fun s => k • w s) t = k • iteratedDeriv 2 w t := by
  have h2 : ∀ φ : ℝ → V, iteratedDeriv 2 φ = deriv (deriv φ) := fun φ => by
    rw [iteratedDeriv_eq_iterate]; rfl
  have hd : deriv (fun s => k • w s) = fun s => k • deriv w s :=
    funext fun s => deriv_fun_const_smul k (hw.differentiable (by simp) s)
  have e1 : Differentiable ℝ (deriv w) := (contDiff_infty_iff_deriv.1 hw).2.differentiable (by simp)
  rw [h2, h2, hd]
  exact deriv_fun_const_smul k (e1 t)

end Ops

theorem wave_add {E : KMod n} {u v : ℝ → Mat n → E.V} (hu : IsWave E u) (hv : IsWave E v) :
    IsWave E fun t y => u t y + v t y := by
  refine ⟨hu.1.add hv.1, fun t => ⟨(hu.2.1 t).1.add (hv.2.1 t).1, ?_⟩, fun t g hg => ?_, fun g hg => ?_⟩
  · intro g hg k
    simp only [(hu.2.1 t).2 g hg k, (hv.2.1 t).2 g hg k, map_add (f := _)]
  · rw [iterated_integral_add (GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg) (GlobalTheory.CompanionTheory.WaveAll.wave_line hv hg), hu.2.2.1 t g hg, hv.2.2.1 t g hg]
    exact (Om_add (hu.2.1 t).1 (hv.2.1 t).1 hg).symm
  · have h1 : DifferentiableAt ℝ (fun s => u s g) 0 :=
      ((GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg).differentiable (by simp)).differentiableAt
    have h2 : DifferentiableAt ℝ (fun s => v s g) 0 :=
      ((GlobalTheory.CompanionTheory.WaveAll.wave_line hv hg).differentiable (by simp)).differentiableAt
    rw [deriv_fun_add h1 h2, hu.2.2.2 g hg, hv.2.2.2 g hg, add_zero]

theorem wave_smul (k : ℂ) {E : KMod n} {u : ℝ → Mat n → E.V} (hu : IsWave E u) :
    IsWave E fun t y => k • u t y := by
  refine ⟨hu.1.const_smul k, fun t => ⟨(hu.2.1 t).1.const_smul k, ?_⟩, fun t g hg => ?_, fun g hg => ?_⟩
  · intro g hg k'
    simp only [(hu.2.1 t).2 g hg k', map_smul]
  · rw [iteratedDeriv_two_smul k (GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg), hu.2.2.1 t g hg]
    exact (Om_smul k (hu.2.1 t).1 hg).symm
  · have h1 : DifferentiableAt ℝ (fun s => u s g) 0 :=
      ((GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg).differentiable (by simp)).differentiableAt
    rw [deriv_fun_const_smul k h1, hu.2.2.2 g hg, smul_zero]

end GlobalTheory.CompanionTheory.WaveK.Lin
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelMultiplierOnEigenfunction
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.EigAct

variable {n : ℕ}

section Ops
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_smul (b : ℂ) (X : Mat n) (f : Mat n → V) : Rd X (b • f) = b • Rd X f := by
  funext g
  have : fderiv ℝ (b • f) = b • fderiv ℝ f := fderiv_const_smul_field b
  simp only [Rd, this, Pi.smul_apply]
  rfl

theorem Eu_smul (b : ℂ) (s : Bool) (a c : Fin n) (f : Mat n → V) : Eu s a c (b • f) = b • Eu s a c f := by
  simp only [Eu, Rd_smul]
  module

theorem Epow_smul (b : ℂ) (s : Bool) (m : ℕ) (a c : Fin n) (f : Mat n → V) :
    Epow s m a c (b • f) = b • Epow s m a c f := by
  induction m generalizing a c with
  | zero =>
    simp only [Epow]
    split_ifs <;> simp
  | succ m ih =>
    simp only [Epow, ih, Eu_smul, Finset.smul_sum]

theorem gel_smul (b : ℂ) (s : Bool) (m : ℕ) (f : Mat n → V) : gel s m (b • f) = b • gel s m f := by
  simp only [gel, Epow_smul, Finset.smul_sum]

theorem Om_smul (b : ℂ) (f : Mat n → V) : Om (b • f) = b • Om f := by
  simp only [Om, gel_smul]
  module

theorem zOp_smul (b : ℂ) (w : List (Bool × ℕ)) (f : Mat n → V) : zOp w (b • f) = b • zOp w f := by
  induction w with
  | nil => rfl
  | cons p w ih => simp only [zOp, ih, gel_smul]

theorem zOp_eig {χ : Inf n} {f : Mat n → V} (hf : IsEig χ f) (w : List (Bool × ℕ)) :
    ∀ x ∈ GLs n, zOp w f x = zVal w χ • f x := by
  induction w with
  | nil => intro x _; simp [zOp, zVal]
  | cons p w ih =>
    intro x hx
    have h := GlobalTheory.CompanionTheory.WaveMult.zOp_agree_GLs n [p] (zOp w f) (zVal w χ • f) (fun g hg => by simpa using ih g hg) x hx
    have h1 : zOp (p :: w) f x = gel p.1 p.2 (zVal w χ • f) x := by simpa [zOp] using h
    rw [h1, gel_smul, Pi.smul_apply, hf p.1 p.2 x hx, smul_smul]
    simp [zVal, mul_comm]

theorem Om_eig {χ : Inf n} {f : Mat n → V} (hf : IsEig χ f) : ∀ x ∈ GLs n, Om f x = cas χ • f x := by
  intro x hx
  simp only [Om, Pi.smul_apply, Pi.add_apply, hf _ _ x hx, cas]
  module

end Ops

theorem hasDerivAt_cosh_mul (a : ℂ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => Complex.cosh (r * a)) (Complex.sinh (s * a) * a) s := by
  have e : HasDerivAt (fun r : ℝ => (r : ℂ) * a) a s := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const a
  exact (Complex.hasDerivAt_cosh ((s : ℂ) * a)).comp s e

theorem hasDerivAt_sinh_mul (a : ℂ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => Complex.sinh (r * a)) (Complex.cosh (s * a) * a) s := by
  have e : HasDerivAt (fun r : ℝ => (r : ℂ) * a) a s := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const a
  exact (Complex.hasDerivAt_sinh ((s : ℂ) * a)).comp s e

theorem isWave_cosh (E : KMod n) {χ : Inf n} {f : Mat n → E.V} (hf : f ∈ CE E) (he : IsEig χ f) {a : ℂ}
    (ha : a ^ 2 = cas χ) : IsWave E (fun t x => Complex.cosh (t * a) • f x) := by
  have d1 : ∀ (v : E.V) (s : ℝ), HasDerivAt (fun r : ℝ => Complex.cosh (r * a) • v)
      ((Complex.sinh (s * a) * a) • v) s := fun v s => (hasDerivAt_cosh_mul a s).smul_const v
  have d2 : ∀ (v : E.V) (s : ℝ), HasDerivAt (fun r : ℝ => (Complex.sinh (r * a) * a) • v)
      ((Complex.cosh (s * a) * a * a) • v) s := fun v s =>
    ((hasDerivAt_sinh_mul a s).mul_const a).smul_const v
  refine ⟨?_, fun t => ⟨?_, fun g hg k => ?_⟩, fun t g hg => ?_, fun g _ => ?_⟩
  · have hc : ContDiff ℝ ∞ (fun t : ℝ => Complex.cosh (t * a)) :=
      (Complex.contDiff_cosh.restrict_scalars ℝ).comp (Complex.ofRealCLM.contDiff.mul contDiff_const)
    have h1 : ContDiffOn ℝ ∞ (fun p : ℝ × Mat n => Complex.cosh (p.1 * a)) (Set.univ ×ˢ GLs n) :=
      (hc.comp contDiff_fst).contDiffOn
    have h2 : ContDiffOn ℝ ∞ (fun p : ℝ × Mat n => f p.2) (Set.univ ×ˢ GLs n) :=
      hf.1.comp contDiff_snd.contDiffOn (fun p hp => hp.2)
    exact h1.smul h2
  · exact contDiffOn_const.smul hf.1
  · simp only [hf.2 g hg k, map_smul]
  · have hOm : Om (fun x => Complex.cosh (t * a) • f x) g = Complex.cosh (t * a) • Om f g :=
      congrFun (Om_smul (Complex.cosh (t * a)) f) g
    have D1 : deriv (fun r : ℝ => Complex.cosh (r * a) • f g) = fun r : ℝ => (Complex.sinh (r * a) * a) • f g :=
      funext fun s => (d1 (f g) s).deriv
    rw [hOm, Om_eig he g hg, iteratedDeriv_succ, iteratedDeriv_one, D1, (d2 (f g) t).deriv, ← ha, smul_smul]
    congr 1
    ring
  · rw [(d1 (f g) 0).deriv]
    simp

section Ker
variable [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n)

theorem act_of_isKer {w : List (Bool × ℕ)} {g : ℝ → ℝ} {ks : Mat n → (E.V →L[ℂ] E.V)}
    (hK : IsKer μ E w g ks) {χ : Inf n} {f : Mat n → E.V} (hf : f ∈ CE E) (he : IsEig χ f) {x : Mat n}
    (hx : x ∈ GLs n) : act μ E ks f x = (zVal w χ * coshT g (cas χ)) • f x := by
  have := FiniteDimensional.complete ℂ E.V
  have ha : ((cas χ) ^ (1 / 2 : ℂ)) ^ 2 = cas χ := by
    have := Complex.cpow_nat_inv_pow (cas χ) (n := 2) two_ne_zero
    simpa [one_div] using this
  have hw := hK.2.2.2 _ (isWave_cosh E hf he ha) x hx
  have h0 : (fun x' => Complex.cosh (((0 : ℝ) : ℂ) * (cas χ) ^ (1 / 2 : ℂ)) • f x') = f := by
    funext x'
    simp
  have h1 : (fun x' => ∫ t : ℝ, (g t : ℂ) • (fun t' x'' => Complex.cosh ((t' : ℂ) * (cas χ) ^ (1 / 2 : ℂ)) • f x'') t x') =
      coshT g (cas χ) • f := by
    funext x'
    simp only [smul_smul, Pi.smul_apply, coshT]
    exact integral_smul_const _ _
  rw [h0, h1, zOp_smul, Pi.smul_apply, zOp_eig he w x hx, smul_smul, mul_comm] at hw
  exact hw

end Ker

end GlobalTheory.CompanionTheory.WaveMult.EigAct

namespace GlobalTheory.CompanionTheory.WaveMult

theorem act_eq_val_of_isMult : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) (val : Inf n → ℂ) (T : ℝ), IsMult μ E k val T → ∀ χ, ∀ f ∈ CE E, IsEig χ f → ∀ x ∈ GLs n, act μ E k f x = val χ • f x := by
  rintro hL n _ _ μ _ E k val T ⟨m, c, w, g, ks, h1, h2, h3⟩ χ f hf he x hx
  have h := GlobalTheory.CompanionTheory.WaveMult.act_eq_sum_of_kernel hL n μ E c ks k f (fun i => ⟨(h1 i).2.1.continuousOn, (h1 i).2.2.1⟩) h2
    hf.1.continuousOn x hx
  rw [h, h3 χ, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EigAct.act_of_isKer μ E (h1 i).2 hf he hx, smul_smul, mul_assoc]

end GlobalTheory.CompanionTheory.WaveMult
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabFiniteIndexOfSmooth
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.KAvg

open GlobalTheory.OrbitAvg

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem stab_finiteIndex_of_smooth [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G)
    (hc : IsCompact (K : Set G)) (ρ : Representation ℂ G V) (hs : IsSmooth ρ) (x : V) :
    (stab ρ K x).FiniteIndex := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hc
  have ho : IsOpen (stab ρ K x : Set K) :=
    (hs x).preimage continuous_subtype_val
  haveI : Finite (K ⧸ stab ρ K x) := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.finiteIndex_of_finite_quotient

private theorem normalCore_stab_le_stab_apply (ρ : Representation ℂ G V) (K : Subgroup G) (x : V) (k : K) :
    (stab ρ K x).normalCore ≤ stab ρ K (ρ (k : G) x) := by
  intro n hn
  have hc : k⁻¹ * n * k ∈ stab ρ K x := by
    have h1 := (Subgroup.normalCore_normal (stab ρ K x)).conj_mem n hn k⁻¹
    rw [inv_inv] at h1
    exact Subgroup.normalCore_le _ h1
  rw [mem_stab] at hc ⊢
  have he : (n : G) * (k : G) = (k : G) * ((k⁻¹ * n * k : K) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  calc ρ (n : G) (ρ (k : G) x) = ρ ((n : G) * (k : G)) x := by
        rw [map_mul, Module.End.mul_apply]
    _ = ρ (k : G) (ρ ((k⁻¹ * n * k : K) : G) x) := by
        rw [he, map_mul, Module.End.mul_apply]
    _ = ρ (k : G) x := by rw [hc]

theorem avg_translate (ρ : Representation ℂ G V) (K : Subgroup G) {x : V}
    (hx : (stab ρ K x).FiniteIndex) (k : K) : avg ρ K (ρ (k : G) x) = avg ρ K x := by
  haveI := hx
  have hN1 : (stab ρ K x).normalCore ≤ stab ρ K x := Subgroup.normalCore_le _
  have hN2 : (stab ρ K x).normalCore ≤ stab ρ K (ρ (k : G) x) := normalCore_stab_le_stab_apply ρ K x k
  rw [avg_eq ρ K hN2, avg_eq ρ K hN1]
  unfold avgH
  congr 1
  have key : ∀ q : K ⧸ (stab ρ K x).normalCore,
      cv ρ K (stab ρ K x).normalCore (ρ (k : G) x) q =
        cv ρ K (stab ρ K x).normalCore x (q * (QuotientGroup.mk k)) := by
    intro q
    have hq : q * (QuotientGroup.mk k : K ⧸ (stab ρ K x).normalCore) = QuotientGroup.mk (q.out * k) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [hq, cv_mk ρ K hN1]
    simp only [cv, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  simp_rw [key]
  exact finsum_comp_equiv (Equiv.mulRight (QuotientGroup.mk k : K ⧸ (stab ρ K x).normalCore))

end GlobalTheory.CompanionTheory.KAvg


open GlobalTheory.OrbitAvg GlobalTheory.CompanionTheory.KAvg in
theorem GlobalTheory.CompanionTheory.KAvg.kInvForm : PositivityTheory.SphericalProduct.KInvForm := by
  unfold PositivityTheory.SphericalProduct.KInvForm
  intro G _ _ _ K _ hc V _ _ ρ hs v₀ hv₀ hne
  have hfi : ∀ x : V, (stab ρ K x).FiniteIndex := fun x => stab_finiteIndex_of_smooth K hc ρ hs x
  let A : V →ₗ[ℂ] V :=
    { toFun := fun x => avg ρ K x
      map_add' := fun x y => avg_add ρ K (hfi x) (hfi y)
      map_smul' := fun c x => avg_smul ρ K (hfi x) c }
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ V, f v₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne ((Module.forall_dual_apply_eq_zero_iff ℂ v₀).mp h)
  have hfix : ∀ l ∈ K, ρ l v₀ = v₀ := by
    intro l hl
    have h' : ∀ h : K, ρ h v₀ = ((1 : K →* ℂˣ) h : ℂ) • v₀ := hv₀
    simpa using h' ⟨l, hl⟩
  refine ⟨((f v₀)⁻¹ • f) ∘ₗ A, ?_, ?_⟩
  · intro k hk
    ext v
    show ((f v₀)⁻¹ • f) (avg ρ K (ρ k v)) = ((f v₀)⁻¹ • f) (avg ρ K v)
    rw [avg_translate ρ K (hfi v) ⟨k, hk⟩]
  · show ((f v₀)⁻¹ • f) (avg ρ K v₀) = 1
    rw [avg_fixed ρ K (hfi v₀) hfix, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf]
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientEquivOfIrreducibleImageStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subquotient_equiv_of_irreducible_image : ∀ (G : Type) [Group G] (V Y W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (R : Representation ℂ G Y) (σ : Representation ℂ G W), ρ.IsIrreducible → σ.IsIrreducible →
    (⨆ f : ρ.IntertwiningMap R, LinearMap.range f.toLinearMap = ⊤) → IsSubquotient σ R → Nonempty (σ.Equiv ρ) := by
  first | exact @GlobalTheory.CompanionTheory.IsoSub.equiv_of_isSubquotient | exact GlobalTheory.CompanionTheory.IsoSub.equiv_of_isSubquotient | (intros; apply GlobalTheory.CompanionTheory.IsoSub.equiv_of_isSubquotient <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumLocalDegreesOverL
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.GreenbergWiles

theorem sum_locDeg_eq_finrank : ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime]
    (T : Finset (HeightOneSpectrum (𝓞 F))), (∀ v, v ∈ T ↔ ((l : ℕ) : 𝓞 F) ∈ v.asIdeal) →
    ∑ v ∈ T, locDeg v = Module.finrank ℚ F := by
  intro F _ _ l _ T hT
  let _ : Fintype {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal} := Fintype.subtype T hT
  rw [Finset.sum_subtype T hT]
  exact GlobalTheory.Proof.LocalDegreeSum.sum_locDeg F l

end GlobalTheory.CompanionTheory.GreenbergWiles
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordSmooth
section
noncomputable section

open Matrix Finset Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.WaveK.Base.RwLinPf

open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK
open PositivityTheory.RgTw (Mat G)
open GlobalTheory.CompanionTheory.RCalc (Rd_contDiffOn differentiableAt_of_smooth isOpen_GLs)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem word_smooth {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (w : List (Bool × Fin n × Fin n)) :
    ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact Rd_contDiffOn (bs p) ih

theorem rwLin : RwLin := by
  intro n V W _ _ _ _ ι _ L f hf w
  induction w with
  | nil => intro x _; rfl
  | cons p w ih =>
    intro x hx
    have hs : ∀ i, ContDiffOn ℝ ∞ (Rw w (f i)) (GLs n) := fun i => word_smooth (hf i) w
    have e : Rw w (fun y => ∑ i, L i (f i y)) =ᶠ[𝓝 x] fun y => ∑ i, L i (Rw w (f i) y) :=
      Filter.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hx) fun y hy => ih y hy
    have hd : ∀ i, HasFDerivAt (fun y => L i (Rw w (f i) y))
        ((L i).comp (fderiv ℝ (Rw w (f i)) x)) x := fun i =>
      (L i).hasFDerivAt.comp x (differentiableAt_of_smooth (hs i) hx).hasFDerivAt
    have hsum := (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => hd i).fderiv
    show fderiv ℝ (Rw w fun y => ∑ i, L i (f i y)) x (x * bs p) =
      ∑ i, L i (fderiv ℝ (Rw w (f i)) x (x * bs p))
    rw [e.fderiv_eq]
    refine (DFunLike.congr_fun hsum (x * bs p)).trans ?_
    exact ContinuousLinearMap.sum_apply _ _ _

end GlobalTheory.CompanionTheory.WaveK.Base.RwLinPf
end
end

