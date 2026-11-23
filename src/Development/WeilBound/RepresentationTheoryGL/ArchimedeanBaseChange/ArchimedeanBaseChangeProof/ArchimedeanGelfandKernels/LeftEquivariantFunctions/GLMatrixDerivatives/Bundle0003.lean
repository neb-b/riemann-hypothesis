module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfEq
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Eq

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem rd_equiv (A : V ≃L[ℂ] V) (X : Mat n) (f : Mat n → V) : Rd X (fun x => A (f x)) = fun x => A (Rd X f x) := by
  funext g
  show fderiv ℝ (fun x => A (f x)) g (g * X) = A (fderiv ℝ f g (g * X))
  by_cases hf : DifferentiableAt ℝ f g
  · have h : HasFDerivAt (fun x => A (f x)) ((A.restrictScalars ℝ : V →L[ℝ] V).comp (fderiv ℝ f g)) g :=
      (A.restrictScalars ℝ : V →L[ℝ] V).hasFDerivAt.comp g hf.hasFDerivAt
    rw [h.fderiv]
    rfl
  · have hn : ¬ DifferentiableAt ℝ (fun x => A (f x)) g := by
      intro h
      apply hf
      have h2 : DifferentiableAt ℝ (fun x => A.symm (A (f x))) g :=
        (A.symm.restrictScalars ℝ : V →L[ℝ] V).differentiableAt.comp g h
      simpa using h2
    rw [fderiv_zero_of_not_differentiableAt hn, fderiv_zero_of_not_differentiableAt hf]
    simp

theorem eu_equiv (A : V ≃L[ℂ] V) (s : Bool) (a b : Fin n) (f : Mat n → V) :
    Eu s a b (fun x => A (f x)) = fun x => A (Eu s a b f x) := by
  unfold Eu
  rw [rd_equiv, rd_equiv]
  funext x
  by_cases hs : s = true <;> simp [hs, map_add (f := _), map_smul]

theorem epow_equiv (A : V ≃L[ℂ] V) (s : Bool) (m : ℕ) : ∀ (a b : Fin n) (f : Mat n → V),
    Epow s m a b (fun x => A (f x)) = fun x => A (Epow s m a b f x) := by
  induction m with
  | zero =>
    intro a b f
    rw [Epow.eq_1]
    funext x
    split_ifs <;> simp
  | succ m ih =>
    intro a b f
    rw [Epow.eq_2]
    simp only [ih, eu_equiv]
    funext x
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Finset.sum_apply, map_sum]

theorem gel_equiv (A : V ≃L[ℂ] V) (s : Bool) (m : ℕ) (f : Mat n → V) :
    gel s m (fun x => A (f x)) = fun x => A (gel s m f x) := by
  unfold gel
  simp only [epow_equiv]
  funext x
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Finset.sum_apply, map_sum]

theorem om_equiv (A : V ≃L[ℂ] V) (f : Mat n → V) : Om (fun x => A (f x)) = fun x => A (Om f x) := by
  unfold Om
  rw [gel_equiv, gel_equiv]
  funext x
  simp [map_add (f := _), map_nsmul]

theorem zop_equiv (A : V ≃L[ℂ] V) : ∀ (w : List (Bool × ℕ)) (f : Mat n → V),
    zOp w (fun x => A (f x)) = fun x => A (zOp w f x) := by
  intro w
  induction w with
  | nil =>
    intro f
    simp [zOp.eq_1]
  | cons p w ih =>
    intro f
    rw [zOp.eq_2]
    simp only [ih, gel_equiv]

end PositivityTheory.RgBcC.LfSt.ChainPf.Eq
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ContinuousCoords
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate ComplexOrder

namespace PositivityTheory.RgBcC.LfSt.KSuppPf

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem inv_contAt (A : Mat n) (hA : A.det ≠ 0) : ContinuousAt (fun B : Mat n => B⁻¹) A := by
  apply continuousAt_matrix_inv
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ hA

theorem lg_contAt (A : Mat n) (hA : A.det ≠ 0) : ContinuousAt lg A := by
  have hi := inv_contAt A hA
  unfold lg
  refine ContinuousAt.log ?_ ?_
  · refine continuousAt_const.add ?_
    refine tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ => ?_
    refine ContinuousAt.add (f := fun y : Mat n => ‖y a b‖ ^ 2) (g := fun y : Mat n => ‖y⁻¹ a b‖ ^ 2) ?_ ?_
    · exact ((continuous_norm.comp ((continuous_apply b).comp (continuous_apply a))).continuousAt).pow 2
    · exact (continuous_norm.continuousAt.comp
        (((continuous_apply b).comp (continuous_apply a)).continuousAt.comp hi)).pow 2
  · have : 0 ≤ ∑ a, ∑ b, (‖A a b‖ ^ 2 + ‖A⁻¹ a b‖ ^ 2) :=
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity
    positivity

theorem det_ne_of_posDef (x : Mat n) (h : (x * xᴴ).PosDef) : x.det ≠ 0 := by
  intro h0
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit
  rw [Matrix.det_mul, h0, zero_mul] at hu
  exact not_isUnit_zero hu

theorem det_inv_ne (A : Mat n) (h : A.det ≠ 0) : (A⁻¹).det ≠ 0 := by
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero h

theorem det_ct_ne (A : Mat n) (h : A.det ≠ 0) : (Aᴴ).det ≠ 0 := by
  rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 h

theorem hOf_comb (hb : HbFacts) (s : ℝ) (v : Fin n × Fin n → ℝ) :
    hOf (s • v + (1 - s) • oPt n) = (s : ℂ) • hOf v + (((1 - s : ℝ)) : ℂ) • (1 : Mat n) := by
  have h1 : hOf (oPt n) = 1 := (hb n).2.2.1 1 Matrix.isHermitian_one
  rw [← h1]
  unfold hOf
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul, add_smul, mul_smul,
    Finset.sum_add_distrib, Finset.smul_sum]

def Kset (n : ℕ) (B : ℝ) : Set (Mat n × Mat n) :=
  {p | p.1 * p.2 = 1} ∩ {p | ∑ a, ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2) ≤ B}

theorem isCompact_Kset (B : ℝ) : IsCompact (Kset n B) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · apply IsClosed.inter
    · exact isClosed_eq (continuous_fst.matrix_mul continuous_snd) continuous_const
    · refine isClosed_le (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_) continuous_const
      exact ((continuous_norm.comp ((continuous_apply b).comp ((continuous_apply a).comp continuous_fst))).pow 2).add
        ((continuous_norm.comp ((continuous_apply b).comp ((continuous_apply a).comp continuous_snd))).pow 2)
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨|B| + 1, fun p hp => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hent : ∀ a b, ‖p.1 a b‖ ≤ |B| + 1 ∧ ‖p.2 a b‖ ≤ |B| + 1 := by
      intro a b
      have hle : ‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2 ≤ B := by
        refine le_trans ?_ hp.2
        refine le_trans ?_ (Finset.single_le_sum (f := fun a => ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2))
          (fun a _ => Finset.sum_nonneg fun b _ => by positivity) (Finset.mem_univ a))
        exact Finset.single_le_sum (f := fun b => ‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2)
          (fun b _ => by positivity) (Finset.mem_univ b)
      have h1 : ‖p.1 a b‖ ^ 2 ≤ |B| := le_trans (by nlinarith [sq_nonneg ‖p.2 a b‖]) (le_abs_self B)
      have h2 : ‖p.2 a b‖ ^ 2 ≤ |B| := le_trans (by nlinarith [sq_nonneg ‖p.1 a b‖]) (le_abs_self B)
      constructor
      · nlinarith [norm_nonneg (p.1 a b), abs_nonneg B, sq_nonneg (‖p.1 a b‖ - 1)]
      · nlinarith [norm_nonneg (p.2 a b), abs_nonneg B, sq_nonneg (‖p.2 a b‖ - 1)]
    have hB : 0 ≤ |B| + 1 := by positivity
    rw [Prod.norm_def, max_le_iff]
    exact ⟨(Matrix.norm_le_iff hB).2 fun a b => (hent a b).1, (Matrix.norm_le_iff hB).2 fun a b => (hent a b).2⟩

theorem continuous_coords : Continuous (coords : Mat n → Fin n × Fin n → ℝ) := by
  apply continuous_pi
  intro p
  unfold coords
  exact Complex.continuous_re.comp ((continuous_id.matrix_mul continuous_const).matrix_trace)

theorem ksupp_of (hb : HbFacts) (hc : ConeSt) : KSupp := by
  intro hS n V _ _ σ hσ hσ2 Fr k Γ T R hk z hz hinj c
  obtain ⟨hopen, hconv, -⟩ := hc n
  obtain ⟨R', hR'⟩ := hS n z hz hinj R
  set C : Set (Fin n × Fin n → ℝ) := (fun p : Mat n × Mat n => coords (p.1 * p.1ᴴ)) '' Kset n (Real.exp R') with hCdef
  have hdet : ∀ v ∈ cone n, (σ v).det ≠ 0 := fun v hv =>
    det_ne_of_posDef _ (by rw [hσ2 v hv]; exact hv)
  have hdz : (diagonal z).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun a _ => fun h0 => by have := hz a; rw [h0, norm_zero] at this; exact zero_ne_one this
  refine ⟨C, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    have hd1 : p.1.det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hp.1
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
      exact zero_ne_one this
    have hu : IsUnit p.1 := (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit hd1)
    show (hOf (coords (p.1 * p.1ᴴ))).PosDef
    rw [(hb n).2.2.1 _ (Matrix.isHermitian_mul_conjTranspose_self _)]
    have := (Matrix.IsUnit.posDef_star_right_conjugate_iff (x := (1 : Mat n)) hu).2 Matrix.PosDef.one
    simpa [Matrix.star_eq_conjTranspose] using this
  · exact (isCompact_Kset _).image (continuous_coords.comp (continuous_fst.matrix_mul continuous_fst.matrix_conjTranspose))
  · intro s hs v hv hvC
    have ho : oPt n ∈ cone n := (hb n).2.2.2.2.2.2.2
    have hP1 : s • v + (1 - s) • oPt n ∈ cone n := hconv hv ho hs.1 (by linarith [hs.2]) (by ring)

    have hgt : R < lg ((σ (s • v + (1 - s) • oPt n))⁻¹ * diagonal z * (σ v)ᴴ⁻¹) := by
      by_contra hle
      push Not at hle
      have hyR := hR' s hs (σ (s • v + (1 - s) • oPt n)) (hdet _ hP1) (σ v) (hdet v hv)
        (by rw [hσ2 _ hP1, hσ2 v hv, hOf_comb hb]) hle
      apply hvC
      refine ⟨(σ v, (σ v)⁻¹), ⟨Matrix.mul_nonsing_inv _ (Ne.isUnit (hdet v hv)), ?_⟩, ?_⟩
      · have h1 : 0 ≤ ∑ a, ∑ b, (‖σ v a b‖ ^ 2 + ‖(σ v)⁻¹ a b‖ ^ 2) :=
          Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity
        have h2 : Real.log (1 + ∑ a, ∑ b, (‖σ v a b‖ ^ 2 + ‖(σ v)⁻¹ a b‖ ^ 2)) ≤ R' := hyR
        have h3 := (Real.log_le_iff_le_exp (by positivity)).1 h2
        show ∑ a, ∑ b, (‖σ v a b‖ ^ 2 + ‖(σ v)⁻¹ a b‖ ^ 2) ≤ Real.exp R'
        linarith
      · show coords (σ v * (σ v)ᴴ) = v
        rw [hσ2 v hv]; exact (hb n).2.2.2.1 v

    have hσc : ∀ w ∈ cone n, ContinuousAt σ w := fun w hw =>
      (hσ.continuousOn).continuousAt (hopen.mem_nhds hw)
    have hA : ((σ (s • v + (1 - s) • oPt n))⁻¹ * diagonal z * (σ v)ᴴ⁻¹).det ≠ 0 := by
      rw [Matrix.det_mul, Matrix.det_mul]
      exact mul_ne_zero (mul_ne_zero (det_inv_ne _ (hdet _ hP1)) hdz) (det_inv_ne _ (det_ct_ne _ (hdet v hv)))
    have hf1 : ContinuousAt (fun w : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => (σ w.1)⁻¹)
        (s • v + (1 - s) • oPt n, v) :=
      ContinuousAt.comp (g := fun B : Mat n => B⁻¹) (f := fun w : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => σ w.1)
        (inv_contAt _ (hdet _ hP1))
        (ContinuousAt.comp (g := σ) (f := Prod.fst) (x := (s • v + (1 - s) • oPt n, v)) (hσc _ hP1) continuousAt_fst)
    have hf2 : ContinuousAt (fun w : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => (σ w.2)ᴴ⁻¹)
        (s • v + (1 - s) • oPt n, v) :=
      ContinuousAt.comp (g := fun B : Mat n => B⁻¹) (f := fun w : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => (σ w.2)ᴴ)
        (inv_contAt _ (det_ct_ne _ (hdet v hv)))
        (ContinuousAt.comp (g := fun B : Mat n => Bᴴ) (f := fun w : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => σ w.2)
          (continuous_id.matrix_conjTranspose).continuousAt
          (ContinuousAt.comp (g := σ) (f := Prod.snd) (x := (s • v + (1 - s) • oPt n, v)) (hσc v hv) continuousAt_snd))
    have hΦ : ContinuousAt (fun w : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) =>
        lg ((σ w.1)⁻¹ * diagonal z * (σ w.2)ᴴ⁻¹)) (s • v + (1 - s) • oPt n, v) :=
      ContinuousAt.comp (g := lg) (f := fun w : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) =>
          (σ w.1)⁻¹ * diagonal z * (σ w.2)ᴴ⁻¹) (lg_contAt _ hA) (by
        have h3 : ContinuousAt (fun w : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => (σ w.1)⁻¹ * diagonal z)
            (s • v + (1 - s) • oPt n, v) := hf1.mul continuousAt_const
        exact h3.mul hf2)
    have e1 := hΦ.eventually (Ioi_mem_nhds hgt)
    have e2 : ∀ᶠ w in nhds (s • v + (1 - s) • oPt n, v), w ∈ cone n ×ˢ cone n :=
      (hopen.prod hopen).mem_nhds ⟨hP1, hv⟩
    filter_upwards [e1, e2] with w hw1 hw2
    have hGL : ((σ w.1)⁻¹ * diagonal z * (σ w.2)ᴴ⁻¹) ∈ GLs n := by
      show ((σ w.1)⁻¹ * diagonal z * (σ w.2)ᴴ⁻¹).det ≠ 0
      rw [Matrix.det_mul, Matrix.det_mul]
      exact mul_ne_zero (mul_ne_zero (det_inv_ne _ (hdet _ hw2.1)) hdz) (det_inv_ne _ (det_ct_ne _ (hdet _ hw2.2)))
    have hk0 := hk _ hGL hw1
    simp only [Kc, Kf, hk0, mul_zero, zero_mul, smul_zero]

end PositivityTheory.RgBcC.LfSt.KSuppPf
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.EpowCongr
section
noncomputable section

open MeasureTheory Matrix Finset Set
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainOf2

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt.ChainPf
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem isOpen_GLs (n : ℕ) : IsOpen (GLs n) :=
  isOpen_ne_fun (continuous_id.matrix_det) continuous_const

section Ops

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem rd_congr {f f' : Mat n → V} (h : EqOn f f' (GLs n)) (X : Mat n) : EqOn (Rd X f) (Rd X f') (GLs n) := by
  intro g hg
  have he : f =ᶠ[nhds g] f' := Filter.eventually_of_mem ((isOpen_GLs n).mem_nhds hg) h
  simp only [Rd, he.fderiv_eq]

theorem eu_congr {f f' : Mat n → V} (h : EqOn f f' (GLs n)) (s : Bool) (a b : Fin n) :
    EqOn (Eu s a b f) (Eu s a b f') (GLs n) := by
  intro g hg
  simp only [Eu, Pi.smul_apply, Pi.add_apply, rd_congr h _ hg]

theorem epow_congr {f f' : Mat n → V} (h : EqOn f f' (GLs n)) (s : Bool) (m : ℕ) :
    ∀ a b, EqOn (Epow s m a b f) (Epow s m a b f') (GLs n) := by
  induction m with
  | zero =>
    intro a b g hg
    simp only [Epow]
    split_ifs
    · exact h hg
    · rfl
  | succ m ih =>
    intro a b g hg
    simp only [Epow, Finset.sum_apply]
    exact Finset.sum_congr rfl fun c _ => eu_congr (ih c b) s a c hg

theorem gel_congr {f f' : Mat n → V} (h : EqOn f f' (GLs n)) (s : Bool) (m : ℕ) :
    EqOn (gel s m f) (gel s m f') (GLs n) := by
  intro g hg
  simp only [gel, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => epow_congr h s m a a hg

theorem rd_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) : ContDiffOn ℝ ∞ (Rd X f) (GLs n) :=
  GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hf

end Ops

theorem gel_sum (hG : GelComm) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {ι : Type} [Fintype ι]
    (F : ι → Mat n → V) (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (GLs n)) (s : Bool) (m : ℕ) :
    ∀ g ∈ GLs n, gel s m (fun y => ∑ i, F i y) g = ∑ i, gel s m (F i) g := by
  classical
  intro g hg
  let Φ : Mat n → (ι → V) := fun y i => F i y
  have hΦ : ContDiffOn ℝ ∞ Φ (GLs n) := contDiffOn_pi.2 hF
  have hsum := ((hG n (ι → V) V s m Φ hΦ).2 g hg).2.2 (∑ i, ContinuousLinearMap.proj (R := ℂ) i)
  have hproj : ∀ i, gel s m (F i) g = gel s m Φ g i := by
    intro i
    have := ((hG n (ι → V) V s m Φ hΦ).2 g hg).2.2 (ContinuousLinearMap.proj (R := ℂ) i)
    simpa [Φ] using this
  have e : (fun y => ∑ i, F i y) = fun y => (∑ i, ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => V) i) (Φ y) := by
    funext y; simp [Φ]
  rw [e, hsum]
  simp [hproj]

theorem gel_DC (hG : GelComm) {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)}
    {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)} {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}
    (_h : CxData lam E Fr ε ι S Γ T) (f : Mat n → E.V) (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (m : ℕ) :
    ∀ x ∈ GLs n, gel s m (DC ε Fr f) x = DC ε Fr (gel s m f) x := by
  intro x hx
  have hR : ∀ p, ContDiffOn ℝ ∞ (Rd (hb p) f) (GLs n) := fun p => rd_smooth hf _
  have hD : ∀ p, ContDiffOn ℝ ∞ (fun y => fderiv ℝ Fr 1 (hb p) (f y)) (GLs n) :=
    fun p => ((fderiv ℝ Fr 1 (hb p)).restrictScalars ℝ).contDiff.comp_contDiffOn hf
  have hGp : ∀ p, ContDiffOn ℝ ∞ (fun y => Rd (hb p) f y + fderiv ℝ Fr 1 (hb p) (f y)) (GLs n) :=
    fun p => (hR p).add (hD p)
  have hFp : ∀ p, ContDiffOn ℝ ∞ (fun y => ε (hb p) (Rd (hb p) f y + fderiv ℝ Fr 1 (hb p) (f y))) (GLs n) :=
    fun p => ((ε (hb p)).restrictScalars ℝ).contDiff.comp_contDiffOn (hGp p)
  have e1 : DC ε Fr f = fun y => ∑ p, ε (hb p) (Rd (hb p) f y + fderiv ℝ Fr 1 (hb p) (f y)) := rfl
  rw [e1, gel_sum hG _ hFp s m x hx]
  simp only [DC]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [((hG n E.V E.V s m _ (hGp p)).2 x hx).2.2 (ε (hb p))]
  congr 1
  have h2 := gel_sum hG (fun (i : Fin 2) y => if i = 0 then Rd (hb p) f y else fderiv ℝ Fr 1 (hb p) (f y))
    (fun i => by fin_cases i <;> simp [hR p, hD p]) s m x hx
  simp only [Fin.sum_univ_two, Fin.isValue, if_pos, one_ne_zero, if_false] at h2
  have h2' : gel s m (fun y => Rd (hb p) f y + fderiv ℝ Fr 1 (hb p) (f y)) x =
      gel s m (Rd (hb p) f) x + gel s m (fun y => fderiv ℝ Fr 1 (hb p) (f y)) x := by
    simpa using h2
  rw [h2', ((hG n E.V E.V s m f hf).2 x hx).2.2 (fderiv ℝ Fr 1 (hb p)), ((hG n E.V E.V s m f hf).2 x hx).1 (hb p)]

theorem zopDC : ZopDC := by
  intro hG n lam E Fr ε ι S Γ T hCx h hh w
  induction w with
  | nil => exact ⟨hh, fun x _ => rfl⟩
  | cons p w ih =>
    obtain ⟨ihs, ihc⟩ := ih
    refine ⟨(hG n E.V E.V p.1 p.2 _ ihs).1, fun x hx => ?_⟩
    show gel p.1 p.2 (zOp w (DC ε Fr h)) x = DC ε Fr (gel p.1 p.2 (zOp w h)) x
    rw [gel_congr (fun y hy => ihc y hy) p.1 p.2 hx]
    exact gel_DC hG hCx (zOp w h) ihs p.1 p.2 x hx

end PositivityTheory.RgBcC.LfSt.ChainOf2
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KchainSt
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate ComplexOrder

namespace PositivityTheory.RgBcC.LfSt.Kchain

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def ConeGL : Prop := ∀ (n : ℕ) (σ : (Fin n × Fin n → ℝ) → Mat n), (∀ v ∈ cone n, σ v * (σ v)ᴴ = hOf v) →
  ∀ v ∈ cone n, σ v ∈ GLs n ∧ (hOf v).det ≠ 0

def KcSmooth : Prop :=
  ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (σ : (Fin n × Fin n → ℝ) → Mat n) (c : ℝ)
    (Fr k : Mat n → (V →L[ℂ] V)) (Γ T : V →L[ℂ] V) (d : Mat n), d ∈ GLs n → ContDiffOn ℝ ∞ σ (cone n) →
    (∀ v ∈ cone n, σ v * (σ v)ᴴ = hOf v) → ContDiffOn ℝ ∞ Fr (GLs n) → ContDiffOn ℝ ∞ k (GLs n) →
    ContDiffOn ℝ ∞ (Kc σ c Fr k Γ T d) (cone n ×ˢ cone n)

def FrMul : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T → ∀ x ∈ GLs n, ∀ Y : Mat n,
    fderiv ℝ Fr x (x * Y) = Fr x * fderiv ℝ Fr 1 Y

def FrComm : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T → ∀ X H : Mat n, X.IsHermitian → H.IsHermitian →
    fderiv ℝ Fr 1 X * ε H = ε H * fderiv ℝ Fr 1 X - ε (X * H + H * X) ∧ Γ * fderiv ℝ Fr 1 X = fderiv ℝ Fr 1 X * Γ

def DerOne : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T →
    ∀ (k : Mat n → (E.V →L[ℂ] E.V)), ContDiffOn ℝ ∞ k (GLs n) → ∀ (d y : Mat n), d ∈ GLs n → y ∈ GLs n →
    ∀ x ∈ GLs n, ∀ X : Mat n,
      fderiv ℝ (fun x' => Kf Fr k Γ T d x' y) x (x * X) =
        Fr x * (fderiv ℝ Fr 1 X * k (x⁻¹ * d * yᴴ⁻¹) + Ld X k (x⁻¹ * d * yᴴ⁻¹)) * Γ * T * Fr y⁻¹

def wt (c : ℝ) (y : Mat n) : ℂ := (c : ℂ) * ((y * yᴴ).det ^ n)⁻¹

def DerTwo : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T →
    ∀ (k : Mat n → (E.V →L[ℂ] E.V)), ContDiffOn ℝ ∞ k (GLs n) → ∀ (c : ℝ) (d x : Mat n), d ∈ GLs n → x ∈ GLs n →
    ∀ y ∈ GLs n, ∀ X : Mat n, X.IsHermitian →
      fderiv ℝ (fun y' => wt c y' • Kf Fr k Γ T d x y') y (y * X) =
        wt c y • (Fr x * (((-(2 * n : ℂ)) * X.trace) • k (x⁻¹ * d * yᴴ⁻¹) * Γ * T -
          Rd X k (x⁻¹ * d * yᴴ⁻¹) * Γ * T - k (x⁻¹ * d * yᴴ⁻¹) * Γ * T * fderiv ℝ Fr 1 X) * Fr y⁻¹)

def DualSum : Prop :=
  ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (α β : Mat n →ₗ[ℝ] (V →L[ℂ] V))
    (A A' : Fin n × Fin n → Mat n), (∀ i, (A i).IsHermitian) → (∀ i, (A' i).IsHermitian) →
    (∀ i j, (A i * A' j).trace = if i = j then 1 else 0) →
    ∑ i, α (A i) * β (A' i) = ∑ p, α (hb p) * β (hb p)

end PositivityTheory.RgBcC.LfSt.Kchain
end
end

