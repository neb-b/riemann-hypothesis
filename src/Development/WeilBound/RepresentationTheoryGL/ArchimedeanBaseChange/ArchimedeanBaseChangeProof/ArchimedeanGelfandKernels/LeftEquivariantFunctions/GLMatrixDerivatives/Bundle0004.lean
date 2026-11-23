module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfCactC
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology Metric Set
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cact

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open GlobalTheory.CompanionTheory.LengthGL (isOpen_GLs mem_GLs_val isCompact_G contDiffOn_lg)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem fderiv_eq_zero_of_lg {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {g : Mat n → V} {R : ℝ}
    (hg : ∀ y ∈ GLs n, R < lg y → g y = 0) {y : Mat n} (hy : y ∈ GLs n) (hR : R < lg y) : fderiv ℝ g y = 0 := by
  have hN : IsOpen (GLs n ∩ lg ⁻¹' Ioi R) := contDiffOn_lg.continuousOn.isOpen_inter_preimage isOpen_GLs isOpen_Ioi
  have h0 : g =ᶠ[𝓝 y] fun _ => (0 : V) :=
    eventually_of_mem (hN.mem_nhds ⟨hy, hR⟩) fun w hw => hg w hw.1 hw.2
  rw [h0.fderiv_eq]
  exact fderiv_const_apply 0

theorem continuousOn_Rd {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {g : Mat n → V}
    (hg : ContDiffOn ℝ ∞ g (GLs n)) (X : Mat n) : ContinuousOn (Rd X g) (GLs n) := by
  have h1 : ContinuousOn (fderiv ℝ g) (GLs n) := hg.continuousOn_fderiv_of_isOpen isOpen_GLs (by simp)
  have h2 : ContinuousOn (fun y : Mat n => y * X) (GLs n) := (cdo_mul contDiffOn_id contDiffOn_const).continuousOn
  exact h1.clm_apply h2

theorem ibpAct : IBPAct := by
  intro _hU hRc n _ _ μ _ E k f hk hkc hf X x hx
  have hmap : MapsTo (fun y : Mat n => x * y) (GLs n) (GLs n) := fun y hy => mul_mem hx hy
  have hxy : ContDiffOn ℝ ∞ (fun y : Mat n => x * y) (GLs n) := cdo_mul contDiffOn_const contDiffOn_id
  have hkr : ContDiffOn ℝ ∞ (fun y => (k y).restrictScalars ℝ) (GLs n) :=
    (ContinuousLinearMap.restrictScalarsL ℂ E.V E.V ℝ ℝ).contDiff.comp_contDiffOn hk
  have hF : ContDiffOn ℝ ∞ (fun y : Mat n => k y (f (x * y))) (GLs n) := hkr.clm_apply (hf.comp hxy hmap)
  obtain ⟨R, hR⟩ := hkc
  have hFc : Cpt (fun y : Mat n => k y (f (x * y))) := ⟨R, fun y hy h => by simp [hR y hy h]⟩
  have h0 := (hRc n).2.2 μ E.V (fun y : Mat n => k y (f (x * y))) hF hFc X
  have hdF : ∀ y ∈ GLs n, Rd X (fun y : Mat n => k y (f (x * y))) y =
      Rd X k y (f (x * y)) + k y (Rd X f (x * y)) := by
    intro y hy
    have hk' : HasFDerivAt k (fderiv ℝ k y) y :=
      ((hk.differentiableOn (by simp)).differentiableAt (isOpen_GLs.mem_nhds hy)).hasFDerivAt
    have hk2 : HasFDerivAt (fun y => (k y).restrictScalars ℝ)
        ((ContinuousLinearMap.restrictScalarsL ℂ E.V E.V ℝ ℝ).comp (fderiv ℝ k y)) y :=
      (ContinuousLinearMap.restrictScalarsL ℂ E.V E.V ℝ ℝ).hasFDerivAt.comp y hk'
    have hf' : HasFDerivAt f (fderiv ℝ f (x * y)) (x * y) :=
      ((hf.differentiableOn (by simp)).differentiableAt (isOpen_GLs.mem_nhds (hmap hy))).hasFDerivAt
    have hg : HasFDerivAt (fun y : Mat n => f (x * y)) ((fderiv ℝ f (x * y)).comp (mulL x)) y :=
      hf'.comp y (mulL x).hasFDerivAt
    have hFD := hk2.clm_apply hg
    have e1 : Rd X (fun y : Mat n => k y (f (x * y))) y =
        k y (fderiv ℝ f (x * y) (x * (y * X))) + (fderiv ℝ k y (y * X)) (f (x * y)) := by
      exact (congrArg (fun L => L (y * X)) hFD.fderiv).trans rfl
    rw [e1, ← Matrix.mul_assoc]
    show _ = fderiv ℝ k y (y * X) (f (x * y)) + k y (fderiv ℝ f (x * y) (x * y * X))
    exact add_comm _ _
  have hK := isCompact_G (n := n) R
  have hA : Integrable (fun y : G n => Rd X k y.val (f (x * y.val))) μ := by
    refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.intro hK fun y hy => ?_)
    · have hc : ContinuousOn (fun y : Mat n => Rd X k y (f (x * y))) (GLs n) :=
        (continuousOn_Rd hk X).clm_apply (hf.continuousOn.comp hxy.continuousOn hmap)
      exact hc.comp_continuous Units.continuous_val mem_GLs_val
    · have : fderiv ℝ k y.val = 0 := fderiv_eq_zero_of_lg hR (mem_GLs_val y) (lt_of_not_ge hy)
      simp [Rd, this]
  have hB : Integrable (fun y : G n => k y.val (Rd X f (x * y.val))) μ := by
    refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.intro hK fun y hy => ?_)
    · have hc : ContinuousOn (fun y : Mat n => k y (Rd X f (x * y))) (GLs n) :=
        hk.continuousOn.clm_apply ((continuousOn_Rd hf X).comp hxy.continuousOn hmap)
      exact hc.comp_continuous Units.continuous_val mem_GLs_val
    · simp [hR y.val (mem_GLs_val y) (lt_of_not_ge hy)]
  have hsum : ∫ y : G n, Rd X (fun y : Mat n => k y (f (x * y))) y.val ∂μ =
      ∫ y : G n, Rd X k y.val (f (x * y.val)) ∂μ + ∫ y : G n, k y.val (Rd X f (x * y.val)) ∂μ := by
    rw [← integral_add hA hB]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => hdF y.val (mem_GLs_val y))
  rw [hsum] at h0
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact h0

end PositivityTheory.RgBcC.LfSt.ChainPf.Cact
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfCdc
section
noncomputable section

open Matrix Finset
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cdc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def mulRL (c : Mat n) : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ c)

@[simp] theorem mulRL_apply (c y : Mat n) : mulRL c y = y * c := rfl

def mulLRL (a c : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap ((LinearMap.mulLeft ℝ a).comp (LinearMap.mulRight ℝ c))

theorem mem_GLs_mul {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

theorem unit_mem (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq]
  intro h
  have := congrArg Matrix.det (unit_star_mul k)
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at this
  exact zero_ne_one this

theorem unit_star_mem (k : Matrix.unitaryGroup (Fin n) ℂ) : (k.1)ᴴ ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq]
  intro h
  have := congrArg Matrix.det (unit_mul_star k)
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at this
  exact zero_ne_one this

theorem inv_val (k : Matrix.unitaryGroup (Fin n) ℂ) : (k⁻¹ : Matrix.unitaryGroup (Fin n) ℂ).1 = (k.1)ᴴ := by
  rw [← Matrix.star_eq_conjTranspose]
  rfl

theorem fderiv_right {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (F : Mat n → W) (c g : Mat n) (Φ : W →L[ℝ] W)
    (hF : DifferentiableAt ℝ F (g * c)) (hF' : DifferentiableAt ℝ F g)
    (hEq : (fun y => F (y * c)) =ᶠ[nhds g] fun y => Φ (F y)) (Z : Mat n) :
    fderiv ℝ F (g * c) (Z * c) = Φ (fderiv ℝ F g Z) := by
  have e := hEq.fderiv_eq (𝕜 := ℝ)
  have h1 : HasFDerivAt (fun y => F (y * c)) ((fderiv ℝ F (g * c)).comp (mulRL c)) g := by
    exact hF.hasFDerivAt.comp g (mulRL c).hasFDerivAt
  have h2 : HasFDerivAt (fun y => Φ (F y)) (Φ.comp (fderiv ℝ F g)) g := Φ.hasFDerivAt.comp g hF'.hasFDerivAt
  rw [h1.fderiv, h2.fderiv] at e
  have := congrArg (fun L : Mat n →L[ℝ] W => L Z) e
  simpa using this

section Cx

variable {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)}
  {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}

theorem fr_star (h : CxData lam E Fr ε ι S Γ T) (k : Matrix.unitaryGroup (Fin n) ℂ) : Fr (k.1)ᴴ = E.ρ k⁻¹ := by
  rw [← inv_val, h.onK]

theorem rho_mul_inv (k : Matrix.unitaryGroup (Fin n) ℂ) : E.ρ k * E.ρ k⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

theorem eps_rho_inv (h : CxData lam E Fr ε ι S Γ T) (k : Matrix.unitaryGroup (Fin n) ℂ) (X : Mat n) (hX : X.IsHermitian) :
    ε X * E.ρ k⁻¹ = E.ρ k⁻¹ * ε (k.1 * X * (k.1)ᴴ) := by
  have := h.frε (k.1)ᴴ (unit_star_mem k) X hX
  rwa [fr_star h, Matrix.conjTranspose_conjTranspose] at this

theorem eps_rho (h : CxData lam E Fr ε ι S Γ T) (k : Matrix.unitaryGroup (Fin n) ℂ) (Y : Mat n) (hY : Y.IsHermitian) :
    ε Y * E.ρ k = E.ρ k * ε ((k.1)ᴴ * Y * k.1) := by
  have := h.frε k.1 (unit_mem k) Y hY
  rwa [h.onK] at this

theorem fr_diff (h : CxData lam E Fr ε ι S Γ T) {x : Mat n} (hx : x ∈ GLs n) : DifferentiableAt ℝ Fr x :=
  (h.smooth.differentiableOn (by simp)).differentiableAt (isOpen_GLs.mem_nhds hx)

theorem one_mem_GLs : (1 : Mat n) ∈ GLs n := by
  simp [GLs]

theorem dFr_conj (h : CxData lam E Fr ε ι S Γ T) (k : Matrix.unitaryGroup (Fin n) ℂ) (Y : Mat n) :
    fderiv ℝ Fr 1 ((k.1)ᴴ * (Y * k.1)) = E.ρ k⁻¹ * fderiv ℝ Fr 1 Y * E.ρ k := by
  set L : (E.V →L[ℂ] E.V) →L[ℝ] (E.V →L[ℂ] E.V) :=
    (ContinuousLinearMap.mulLeftRight ℂ (E.V →L[ℂ] E.V) (E.ρ k⁻¹) (E.ρ k)).restrictScalars ℝ with hL
  have hEq : (fun y => Fr ((k.1)ᴴ * (y * k.1))) =ᶠ[nhds (1 : Mat n)] fun y => L (Fr y) := by
    filter_upwards [isOpen_GLs.mem_nhds (one_mem_GLs (n := n))] with y hy
    rw [h.mul _ (unit_star_mem k) _ (mem_GLs_mul hy (unit_mem k)), h.mul _ hy _ (unit_mem k), fr_star h, h.onK]
    simp [hL, ContinuousLinearMap.mulLeftRight_apply, mul_assoc]
  have e := hEq.fderiv_eq (𝕜 := ℝ)
  have hpt : (k.1)ᴴ * ((1 : Mat n) * k.1) = 1 := by rw [Matrix.one_mul, unit_star_mul]
  have h1 : HasFDerivAt (fun y => Fr ((k.1)ᴴ * (y * k.1))) ((fderiv ℝ Fr 1).comp (mulLRL (k.1)ᴴ k.1)) 1 := by
    have hd := (fr_diff h (one_mem_GLs (n := n))).hasFDerivAt
    rw [← hpt] at hd
    have := hd.comp (1 : Mat n) (mulLRL (k.1)ᴴ k.1).hasFDerivAt
    rw [hpt] at this
    exact this
  have h2 : HasFDerivAt (fun y => L (Fr y)) (L.comp (fderiv ℝ Fr 1)) 1 :=
    L.hasFDerivAt.comp (1 : Mat n) (fr_diff h (one_mem_GLs (n := n))).hasFDerivAt
  rw [h1.fderiv, h2.fderiv] at e
  have := congrArg (fun M : Mat n →L[ℝ] (E.V →L[ℂ] E.V) => M Y) e
  simpa [hL, mulLRL, ContinuousLinearMap.mulLeftRight_apply] using this

end Cx

end PositivityTheory.RgBcC.LfSt.ChainPf.Cdc
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfCwave
section
noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cwave

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.RCalc (isOpen_GLs differentiableAt_of_smooth)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private theorem good_smul_bump_of_isWave {n : ℕ} (E : KMod n) (u : ℝ → Mat n → E.V) (hu : IsWave E u)
    (g : ℝ → ℝ) (T : ℝ) (hg : IsBump g T) :
    Good (GLs n) (fun q : ℝ × Mat n => ((g q.1 : ℂ)) • u q.1 q.2) T := by
  refine ⟨?_, ?_⟩
  · have h1 : ContDiff ℝ ∞ (fun q : ℝ × Mat n => ((g q.1 : ℂ))) :=
      Complex.ofRealCLM.contDiff.comp (hg.1.comp contDiff_fst)
    exact h1.contDiffOn.smul hu.1
  · intro t x ht
    simp [hg.2.2 t ht]

theorem paramInt : ParamInt := by
  intro n E u hu g T hg
  have hG := good_smul_bump_of_isWave E u hu g T hg
  refine ⟨good_smooth isOpen_GLs _ T hG, ?_⟩
  intro X x hx
  unfold Rd
  refine (good_fderiv_apply isOpen_GLs hG hx (x * X)).trans ?_
  congr 1
  funext t
  have hd : DifferentiableAt ℝ (u t) x := by
    apply differentiableAt_of_smooth _ hx
    have h2 : ContDiffOn ℝ ∞ (fun y : Mat n => Function.uncurry u (t, y)) (GLs n) :=
      hu.1.comp (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => ⟨mem_univ _, hy⟩)
    exact h2
  have hf : fderiv ℝ (fun y => ((g t : ℂ)) • u t y) x = ((g t : ℂ)) • fderiv ℝ (u t) x :=
    (hd.hasFDerivAt.const_smul ((g t : ℂ))).fderiv
  show (fderiv ℝ (fun y => ((g t : ℂ)) • u t y) x) (x * X) = _
  rw [hf]
  rfl

end PositivityTheory.RgBcC.LfSt.ChainPf.Cwave
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfLoc
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Loc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem isOpen_GLs (n : ℕ) : IsOpen (GLs n) :=
  isOpen_ne_fun (Continuous.matrix_det continuous_id) continuous_const

theorem rd_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : Set.EqOn f f' U) (X : Mat n) :
    Set.EqOn (Rd X f) (Rd X f') U := by
  intro x hx
  simp only [Rd]
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) h)]

theorem eu_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : Set.EqOn f f' U) (s : Bool) (a b : Fin n) :
    Set.EqOn (Eu s a b f) (Eu s a b f') U := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply]
  rw [rd_congr hU h _ hx, rd_congr hU h _ hx]

theorem epow_congr {U : Set (Mat n)} (hU : IsOpen U) (s : Bool) (m : ℕ) : ∀ (a b : Fin n) {f f' : Mat n → V},
    Set.EqOn f f' U → Set.EqOn (Epow s m a b f) (Epow s m a b f') U := by
  induction m with
  | zero =>
    intro a b f f' h x hx
    simp only [Epow]
    split_ifs
    · exact h hx
    · rfl
  | succ m ih =>
    intro a b f f' h x hx
    simp only [Epow, Finset.sum_apply]
    exact Finset.sum_congr rfl fun c _ => eu_congr hU (ih c b h) s a c hx

theorem gel_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : Set.EqOn f f' U) (s : Bool) (m : ℕ) :
    Set.EqOn (gel s m f) (gel s m f') U := by
  intro x hx
  simp only [gel, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => epow_congr hU s m a a h hx

theorem zop_congr {U : Set (Mat n)} (hU : IsOpen U) : ∀ (w : List (Bool × ℕ)) {f f' : Mat n → V},
    Set.EqOn f f' U → Set.EqOn (zOp w f) (zOp w f') U := by
  intro w
  induction w with
  | nil => intro f f' h; exact h
  | cons p w ih => intro f f' h; exact gel_congr hU (ih h) p.1 p.2

theorem integrable_cpt (hL : LgFacts) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (F : Mat n → W) (hF : ContinuousOn F (GLs n))
    (hc : Cpt F) : Integrable (fun y : G n => F y.val) μ := by
  obtain ⟨R, hR⟩ := hc
  have hcont : Continuous fun y : G n => F y.val := by
    refine hF.comp_continuous (Units.continuous_val) fun y => ?_
    show (y.val).det ≠ 0
    exact (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit |>.ne_zero
  have hlg : ContinuousOn (lg (n := n)) (GLs n) := (hL n).2.2.2.1.continuousOn
  have hK : IsCompact {y : G n | lg y.val ≤ R} := (hL n).2.2.2.2.1 R
  have hclosed : IsClosed {y : G n | lg y.val ≤ R} := by
    have : Continuous fun y : G n => lg y.val :=
      hlg.comp_continuous Units.continuous_val fun y => (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit |>.ne_zero
    exact isClosed_le this continuous_const
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro hK ?_
  intro y hy
  simp only [Set.mem_setOf_eq, not_le] at hy
  exact hR _ ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit |>.ne_zero) hy

end PositivityTheory.RgBcC.LfSt.ChainPf.Loc
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.HalfOne
section
noncomputable section

open Matrix Finset
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.Kchain

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def HalfOne : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T →
    ∀ (σ : (Fin n × Fin n → ℝ) → Mat n), ContDiffOn ℝ ∞ σ (cone n) → (∀ v ∈ cone n, σ v * (σ v)ᴴ = hOf v) →
    ∀ (k : Mat n → (E.V →L[ℂ] E.V)), ContDiffOn ℝ ∞ k (GLs n) →
    (∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂) →
    ∀ (d : Mat n), d ∈ GLs n → ∀ c : ℝ, ∀ v ∈ cone n, ∀ w ∈ cone n,
      ∑ i, ε (hb i) * fderiv ℝ (Kc σ c Fr k Γ T d) (v, w) (Pi.single i 1, 0) =
        ((c : ℂ) * ((hOf w).det ^ n)⁻¹) • (Fr (σ v) * ((1 / 2 : ℂ) • ∑ p, ε (hb p) *
          (fderiv ℝ Fr 1 (hb p) * k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹) + Ld (hb p) k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹))) * Γ * T * Fr (σ w)⁻¹)

def HalfTwo : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T →
    ∀ (σ : (Fin n × Fin n → ℝ) → Mat n), ContDiffOn ℝ ∞ σ (cone n) → (∀ v ∈ cone n, σ v * (σ v)ᴴ = hOf v) →
    ∀ (k : Mat n → (E.V →L[ℂ] E.V)), ContDiffOn ℝ ∞ k (GLs n) →
    (∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂) →
    ∀ (d : Mat n), d ∈ GLs n → ∀ c : ℝ, ∀ v ∈ cone n, ∀ w ∈ cone n,
      ∑ i, fderiv ℝ (Kc σ c Fr k Γ T d) (v, w) (0, Pi.single i 1) * ε (hb i) =
        ((c : ℂ) * ((hOf w).det ^ n)⁻¹) • (Fr (σ v) * ((1 / 2 : ℂ) • ∑ p,
          (Rd (hb p) k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹) * ε (hb p) -
            k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹) * ε (hb p) * fderiv ℝ Fr 1 (hb p))) * Γ * T * Fr (σ w)⁻¹)

end PositivityTheory.RgBcC.LfSt.Kchain
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KbBase
section
noncomputable section

open Matrix Finset
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.Kchain.KbBase

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt
open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def entL (a b : Fin n) : Mat n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)

theorem contDiff_entry (a b : Fin n) : ContDiff ℝ ∞ (fun y : Mat n => y a b) := (entL a b).contDiff

theorem contDiffAt_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → Mat n} {x : E}
    (h : ∀ a b, ContDiffAt ℝ ∞ (fun z => F z a b) x) : ContDiffAt ℝ ∞ F x :=
  contDiffAt_pi' fun a => contDiffAt_pi' fun b => h a b

theorem contDiff_det_of {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → Mat n)
    (h : ∀ a b, ContDiff ℝ ∞ (fun z => F z a b)) : ContDiff ℝ ∞ (fun z => (F z).det) := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => h _ _)

theorem contDiff_det : ContDiff ℝ ∞ (fun y : Mat n => y.det) := contDiff_det_of id fun a b => contDiff_entry a b

theorem contDiffAt_inv {x : Mat n} (hx : x.det ≠ 0) : ContDiffAt ℝ ∞ (fun y : Mat n => y⁻¹) x := by
  refine contDiffAt_of_entries fun a b => ?_
  have e : (fun y : Mat n => y⁻¹ a b) = fun y => (y.det)⁻¹ * (y.updateRow b (Pi.single a 1)).det := by
    funext y
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', Matrix.adjugate_apply]
  rw [e]
  refine (contDiff_det.contDiffAt.inv hx).mul (contDiff_det_of _ fun i j => ?_).contDiffAt
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact contDiff_entry _ _

end PositivityTheory.RgBcC.LfSt.Kchain.KbBase
end
end

