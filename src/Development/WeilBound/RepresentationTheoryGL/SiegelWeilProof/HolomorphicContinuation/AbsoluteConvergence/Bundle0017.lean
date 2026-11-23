module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0016
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0014
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0005

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.CompactUnitaryT2Space
section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt.Vac

private theorem vacOut_of'_lemma (n : ℕ) : CompactSpace (KR n) := by
  have hb : ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ, Matrix.conjTranspose g * g = 1 → ∀ i j, ‖g i j‖ ≤ 1 := by
    intro g hg i j
    exact entry_norm_bound_of_unitary (Matrix.mem_unitaryGroup_iff'.mpr hg) i j
  have hS : IsCompact {g : M2 n | InG g ∧ Matrix.conjTranspose g * g = 1} := by
    have hbox : IsCompact (Set.pi univ fun _ : Fin n ⊕ Fin n => Set.pi univ fun _ : Fin n ⊕ Fin n => Metric.closedBall (0 : ℂ) 1) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
    refine hbox.of_isClosed_subset ?_ ?_
    · change IsClosed ({g : M2 n | InG g} ∩ {g : M2 n | Matrix.conjTranspose g * g = 1})
      refine IsClosed.inter ?_ ?_
      · exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const
      · exact isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
    · intro g hg i _ j _
      simpa using hb g hg.2 i j
  have hcl : IsClosed (range fun k : KR n => mR (k : GR n)) := by
    convert hS.isClosed using 1
    ext g
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k.1.2, k.2.2⟩
    · rintro ⟨hG, hg⟩
      let u : GL (Fin n ⊕ Fin n) ℂ := ⟨g, Matrix.conjTranspose g, mul_eq_one_comm.mp hg, hg⟩
      exact ⟨⟨⟨u, hG⟩, ⟨hG, hg⟩⟩, rfl⟩
  constructor
  rw [(kr_inducing n).isCompact_iff, Set.image_univ]
  refine hS.of_isClosed_subset hcl ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨k.1.2, k.2.2⟩

theorem vacOut_of' (hD : CayleyBlocksInvertible) (hLO : LocOp) (hHP : HolParam) (hTS : ThSph) : VacOut := by
  intro m n ε c t p q e sL ρ hL hGS G _ _ _ _ _ _ Pp Γ ι s₀ Ht sec I Λ hG
  haveI := vacOut_of'_lemma n
  letI : MeasurableSpace (KR n) := borel _
  haveI : BorelSpace (KR n) := ⟨rfl⟩
  let μ : Measure (KR n) := Measure.haarMeasure ⊤
  haveI : μ.IsHaarMeasure := by infer_instance
  haveI : IsProbabilityMeasure μ := ⟨by simpa using Measure.haarMeasure_self (G := KR n) (K₀ := ⊤)⟩
  obtain ⟨ψ, a, b, nb, cz, hψ, hnb, hnbc, hcz, hcz0, hid⟩ := hLO n p q e hGS μ
  obtain ⟨U, d, E, σ, hU, hR, hs, hd, hEd, hEc, hEi, hEs⟩ := hG.eis
  have hψc := hψ.1
  have hψs := hψ.2.1
  obtain ⟨d1, hdd, hnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd d hd s₀
  have hd1 : Polynomial.eval s₀ d1 ≠ 0 := fun h => hnd (Polynomial.dvd_iff_isRoot.mpr h)
  set k₀ := d.rootMultiplicity s₀
  have hdeval : ∀ z, Polynomial.eval z d = (z - s₀) ^ k₀ * Polynomial.eval z d1 := by
    intro z
    conv_lhs => rw [hdd]
    simp [Polynomial.eval_mul, Polynomial.eval_pow]
  have hTE : ∀ z ∈ U, ∀ g, Vac.Top μ ι p q e a b nb ψ (E z) g = cz (z - s₀) * E z g :=
    top_E μ hL hG hD hHP hnbc hψc hψs hcz hid hU hR hd hEd hEc hEs
  have hTI : ∀ g, Vac.Top μ ι p q e a b nb ψ (I 1) g = cz 0 * I 1 g :=
    top_theta μ hD hG.ιcont hnbc hψc hψs hid (I 1) hG.Icont
      (fun g y => hTS m n ε c t p q e sL ρ hL G Pp Γ ι s₀ Ht sec I Λ hG μ g y)
  have hloc := lam_local banachHol factorL hG hU hR hs hd hEd hEc hEi (fun z hz g => (hEs z hz).2 g)
  have hloc' : ∀ l ∈ Λ, ∃ H : ℂ → ℂ, ContinuousAt H s₀ ∧ H s₀ = l (I 1) ∧
      ∀ᶠ z in 𝓝[≠] s₀, l (E z) = (z - s₀) ^ k₀ * Polynomial.eval z d1 * H z := by
    intro l hl
    obtain ⟨H, hHa, hH0, hHe⟩ := hloc l hl
    refine ⟨H, hHa.continuousAt, hH0, ?_⟩
    filter_upwards [hHe] with z hz
    rw [hz, hdeval]
  obtain ⟨Ek, hEkc, hEkd, hEk, hEk0⟩ := core Γ Λ (Vac.Top μ ι p q e a b nb ψ) (I 1) s₀ U hU hs E cz k₀
    (fun z => Polynomial.eval z d1) dslopeFam hcz.continuous hcz0 (Polynomial.continuous d1).continuousAt
    hG.Λadd (fun l hl F hFc hFd hFi => lam_cont banachHol factorL hG l hl hU hs F hFc hFd hFi) hloc'
    (fun F hF hFi hΛ g => top_sing μ hG hψ hnb F hF hFi hΛ g)
    (fun a' F F' hF hF' g => top_linear μ hD hG.ιcont hnbc hψc hψs F F' hF hF' a' g)
    hG.Icont hG.Ileft hTI
    (fun F hFc hFd g => (top_hol μ hD hHP hG.ιcont hnbc hψc hψs hU F hFc hFd g).continuousOn)
    hEc hEd hEi hTE
  have hnear : ∀ᶠ z in 𝓝 s₀, z ∈ U ∧ Polynomial.eval z d1 ≠ 0 :=
    (show ∀ᶠ z in 𝓝 s₀, z ∈ U from hU.mem_nhds hs).and
      ((Polynomial.continuous d1).continuousAt.eventually_ne hd1)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hsub : Metric.ball s₀ r ⊆ U := fun z hz => (hball hz).1
  have hFd : ∀ g, DifferentiableOn ℂ (fun z => Ek z g / Polynomial.eval z d1) (Metric.ball s₀ r) :=
    fun g => ((hEkd g).mono hsub).div (Polynomial.differentiable d1).differentiableOn
      (fun z hz => (hball hz).2)
  obtain ⟨σ2, hσ2⟩ := roots_bound d hd
  have hmain : ∀ g, ∀ z ∈ Metric.ball s₀ r, GlobalTheory.Cont.HolValueAt
      (fun w => GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (w - s₀) * sec 1 x) g) z
      (Ek z g / Polynomial.eval z d1) := by
    intro g z hz
    have hext : GlobalTheory.Cont.IsExtAt
        (fun w => GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (w - s₀) * sec 1 x) g) z
        (fun w => E w g / Polynomial.eval w d) := by
      refine ⟨U, hsub hz, hR, ?_, ?_⟩
      · intro w hw
        exact (((hEd g).analyticAt (hU.mem_nhds hw)).meromorphicAt).div
          ((Polynomial.differentiable d).analyticAt w).meromorphicAt
      · refine ⟨max σ σ2, fun w hw => ?_⟩
        have hw1 : σ < w.re := lt_of_le_of_lt (le_max_left _ _) hw
        have hw2 : σ2 < w.re := lt_of_le_of_lt (le_max_right _ _) hw
        show E w g / Polynomial.eval w d = _
        rw [(hEs w hw1).2 g, mul_div_cancel_left₀ _ (hσ2 w hw2)]
    rw [hext.holValueAt_iff]
    have hFc : ContinuousAt (fun w => Ek w g / Polynomial.eval w d1) z :=
      (hFd g).continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hz)
    refine (hFc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    have hev : ∀ᶠ w in 𝓝[≠] z, w ∈ Metric.ball s₀ r ∧ w ≠ s₀ := by
      by_cases hzs : z = s₀
      · subst hzs
        exact eventually_mem_ne z _ Metric.isOpen_ball hz
      · exact nhdsWithin_le_nhds ((Metric.isOpen_ball.inter isOpen_ne).mem_nhds ⟨hz, hzs⟩)
    filter_upwards [hev] with w hw
    have hpow : (w - s₀) ^ k₀ ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hw.2)
    show Ek w g / Polynomial.eval w d1 = E w g / Polynomial.eval w d
    rw [hEk w (hsub hw.1) g, hdeval w, mul_div_mul_left _ _ hpow]
  have hval : ∀ g, Ek s₀ g / Polynomial.eval s₀ d1 = I 1 g := fun g => by
    rw [hEk0 g, mul_div_cancel_left₀ _ hd1]
  refine ⟨r, 0, fun z g => Ek z g / Polynomial.eval z d1, hr, subset_union_right, ?_, hFd, hval, ?_, hmain⟩
  · exact (hEkc.mono (prod_mono hsub subset_rfl)).div
      ((Polynomial.continuous d1).comp continuous_fst).continuousOn (fun y hy => (hball hy.1).2)
  · intro g
    have h0 := hmain g s₀ (Metric.mem_ball_self hr)
    rwa [hval g] at h0

end PositivityTheory.Rg.Sw.AbsSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FarRight
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Far

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n}
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem farId [MeasurableSpace (KR n)] [BorelSpace (KR n)] (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) {ν : Measure (KR n)} {κ : KR n → ℂ} {N : ℕ}
    {yy : Fin N → GR n} {QQ : Fin N → PX m n} {M : ℂ → Matrix (Fin N) (Fin N) ℂ}
    (hν : IsFiniteMeasure ν) (hκ : Continuous κ)
    (hMid : ∀ (w : ℂ) (i : Fin N) (y' : GR n), ∫ k, κ k * ((hLoc (y' * (k : GR n) * yy i) : ℂ) ^ w *
        F0 p q e (y' * (k : GR n) * yy i)) ∂ν = (hLoc y' : ℂ) ^ w * ∑ j, M w i j * sL (QQ j) y')
    {z : ℂ} (hmaj : ∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧
      ∀ g ∈ C, ∀ q', ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z 1) g q'‖ ≤ u q')
    (g : G) (hsum : ∀ j, Summable fun q' => GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z (QQ j)) g q') (i : Fin N) :
    ∫ k, κ k * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z 1) (g * ι ((k : GR n) * yy i)) ∂ν =
      ∑ j, M (z - s₀) i j * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z (QQ j)) g := by
  classical
  haveI := hν
  have hcK : IsCompact (Set.range fun k : KR n => g * ι ((k : GR n) * yy i)) :=
    isCompact_range (continuous_const.mul (hG.ιcont.comp (continuous_subtype_val.mul continuous_const)))
  obtain ⟨u, hu, hbd⟩ := hmaj _ hcK
  obtain ⟨B, hB⟩ := (isCompact_univ (X := KR n)).exists_bound_of_continuousOn hκ.continuousOn
  let F : GlobalTheory.Eis.Cosets Pp Γ → KR n → ℂ := fun q' k =>
    κ k * GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z 1) (g * ι ((k : GR n) * yy i)) q'
  have hcont : ∀ q', Continuous (F q') := by
    intro q'
    have h := Far.cont_hz hD hL hG z (yy i) (GlobalTheory.Eis.term Pp Γ id g q')
    refine hκ.mul ?_
    simpa [GlobalTheory.Eis.term, mul_assoc] using h
  have hbound : ∀ q' k, ‖F q' k‖ ≤ B * u q' := by
    intro q' k
    rw [norm_mul]
    exact mul_le_mul (hB k trivial) (hbd _ ⟨k, rfl⟩ q') (norm_nonneg _)
      (le_trans (norm_nonneg _) (hB k trivial))
  have hint : ∀ q', Integrable (F q') ν := fun q' =>
    Integrable.mono' (integrable_const (B * u q')) (hcont q').aestronglyMeasurable
      (ae_of_all _ (hbound q'))
  have hsumm : Summable fun q' => ∫ k, ‖F q' k‖ ∂ν := by
    refine Summable.of_nonneg_of_le (fun q' => integral_nonneg fun _ => norm_nonneg _)
      (fun q' => integral_mono (hint q').norm (integrable_const (B * u q')) (hbound q'))
      ?_
    simp only [integral_const, smul_eq_mul]
    exact (hu.mul_left B).mul_left _
  have hq : ∀ q', ∫ k, F q' k ∂ν =
      ∑ j, M (z - s₀) i j * GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z (QQ j)) g q' := by
    intro q'
    have h := Far.pointId hD hL hG hMid z i (GlobalTheory.Eis.term Pp Γ id g q')
    simpa [F, GlobalTheory.Eis.term, mul_assoc] using h
  have hzero : ∀ q', u q' = 0 → F q' = fun _ => 0 := by
    intro q' h0
    funext k
    have h1 := hbound q' k
    rw [h0, mul_zero] at h1
    exact norm_le_zero_iff.mp h1
  let S : Set (GlobalTheory.Eis.Cosets Pp Γ) := Function.support u
  haveI : Countable S := hu.countable_support.to_subtype
  have hout : ∀ q', q' ∉ S → u q' = 0 := fun q' h => Function.notMem_support.mp h
  have e1 : ∀ k, ∑' q', F q' k = ∑' q' : S, F q' k := by
    intro k
    refine (tsum_subtype_eq_of_support_subset ?_).symm
    intro q' hq'
    by_contra h
    apply hq'
    show F q' k = 0
    rw [hzero q' (hout q' h)]
  have e2 : ∑' q', ∫ k, F q' k ∂ν = ∑' q' : S, ∫ k, F q' k ∂ν := by
    refine (tsum_subtype_eq_of_support_subset ?_).symm
    intro q' hq'
    by_contra h
    apply hq'
    show ∫ k, F q' k ∂ν = 0
    rw [hzero q' (hout q' h)]
    simp
  have hL1 : ∫ k, κ k * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z 1) (g * ι ((k : GR n) * yy i)) ∂ν =
      ∫ k, ∑' q' : S, F q' k ∂ν := by
    congr 1
    funext k
    rw [← e1 k]
    simp only [F, GlobalTheory.Eis.cosetSum]
    rw [tsum_mul_left]
  have hswap : ∫ k, ∑' q' : S, F q' k ∂ν = ∑' q' : S, ∫ k, F q' k ∂ν :=
    (integral_tsum_of_summable_integral_norm (F := fun (q' : S) k => F q' k)
      (fun q' => hint q') (hsumm.subtype (fun x => x ∈ S))).symm
  rw [hL1, hswap, ← e2]
  simp_rw [hq]
  rw [Summable.tsum_finsetSum (fun j _ => (hsum j).mul_left _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tsum_mul_left]
  rfl

end PositivityTheory.Rg.Sw.AbsSt.Far

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem farRight : Iwa → CayleyBlocksInvertible → Mult → HolParam → FarRight := by
  intro hI hD hM _hH m n ε c t p q e sL ρ hL G _ _ _ _ _ _ Pp Γ ι s₀ Ht sec I Λ hG
  obtain ⟨σ, h1, h2, hmaj⟩ := Far.farHol hI hM hD hL hG
  refine ⟨σ, h1, h2, ?_⟩
  intro _ _ ν κ N yy QQ M hν hκ hMid z hzr g i
  exact Far.farId hD hL hG hν hκ hMid (hmaj z hzr) g (fun j => h2 (QQ j) g z hzr) i

end PositivityTheory.Rg.Sw.AbsSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerM
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.SDM

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.DF

variable {m n : ℕ}

theorem gram_eq (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) :
    gramX ε x = (Matrix.of x)ᴴ * diagonal (sgn ε) * Matrix.of x := by
  ext i j
  rw [gramX_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem gramX_mulR (ε : Fin m → Bool) (A : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) :
    gramX ε (mulR A y) = Aᴴ * gramX ε y * A := by
  have e : Matrix.of (mulR A y) = Matrix.of y * A := by
    ext a j; simp [mulR, Matrix.mul_apply]
  rw [gram_eq, gram_eq, e, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem trace_herm_re {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) : ((H.trace.re : ℝ) : ℂ) = H.trace := by
  have him : H.trace.im = 0 := by
    simp only [Matrix.trace, Matrix.diag, Complex.im_sum]
    exact Finset.sum_eq_zero fun i _ => Complex.conj_eq_iff_im.mp (hH.apply i i)
  exact Complex.ext (by simp) (by simp [him])

def Psi (ε : Fin m → Bool) (c t : ℝ) (H b : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) (σ : ℝ) : ℂ :=
  ∫ y, evX R (mulR (aE H σ) y) * gs c (mulR (aE H σ) y) * Complex.exp (Complex.I * t * (b * gramX ε y).trace)

theorem secN_aE (ε : Fin m → Bool) (c t : ℝ) {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    (b : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) (σ : ℝ) :
    secN ε c t R (aE H (-σ) * b * aE H (-σ)) =
      Complex.exp (((2 * m * σ * H.trace.re : ℝ) : ℂ)) * Psi ε c t H b R σ := by
  have hdet : (aE H σ).det ≠ 0 := by
    rw [det_aE]
    exact Complex.exp_ne_zero _
  have hr : Complex.normSq (aE H σ).det ^ m = Real.exp (2 * m * σ * H.trace.re) := by
    rw [det_aE, Complex.normSq_eq_norm_sq, Complex.norm_exp, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    simp only [Complex.re_ofReal_mul]
    push_cast
    ring
  unfold secN Psi
  rw [coV m n (aE H σ) hdet, hr, Complex.ofReal_exp]
  congr 1
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [gramX_mulR, aE_herm hH]
  have e1 : aE H (-σ) * b * aE H (-σ) * (aE H σ * gramX ε y * aE H σ) =
      aE H (-σ) * (b * gramX ε y * aE H σ) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (aE H (-σ)) (aE H σ), aE_mul_neg, Matrix.one_mul]
  rw [e1, Matrix.trace_mul_comm, Matrix.mul_assoc, aE_mul_neg', Matrix.mul_one]

private theorem continuous_evX_gs_exp_trace_mulR_aE (ε : Fin m → Bool) (c t : ℝ) (H b : Matrix (Fin n) (Fin n) ℂ)
    (P : PX m n) (σ : ℝ) :
    Continuous fun y : Fin m → Fin n → ℂ => evX P (mulR (aE H σ) y) * gs c (mulR (aE H σ) y) *
      Complex.exp (Complex.I * t * (b * gramX ε y).trace) := by
  have hm : Continuous fun y : Fin m → Fin n → ℂ => mulR (aE H σ) y := by
    unfold mulR
    refine continuous_pi fun a => continuous_pi fun j => ?_
    exact continuous_finsetSum _ fun i _ =>
      (((continuous_apply i).comp (continuous_apply a) :
        Continuous fun y : Fin m → Fin n → ℂ => y a i)).mul continuous_const
  refine (((continuous_evX P).comp hm).mul ((continuous_gs c).comp hm)).mul ?_
  exact Complex.continuous_exp.comp
    (continuous_const.mul ((continuous_const.matrix_mul (continuous_gramX ε)).matrix_trace))

private theorem exists_norm_evX_gs_exp_le_polynomial_decay (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (t : ℝ)
    (H : Matrix (Fin n) (Fin n) ℂ) {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (P : PX m n)
    (s : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ, |σ - s| < 1 → ∀ y : Fin m → Fin n → ℂ,
      ‖evX P (mulR (aE H σ) y) * gs c (mulR (aE H σ) y) *
          Complex.exp (Complex.I * t * (b * gramX ε y).trace)‖ ≤
        K * (1 + ‖y‖) ^ (-((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1)) := by
  obtain ⟨K, hK0, hK⟩ := dom_boundE c hc H P s
  refine ⟨K, hK0, fun σ hσ y => ?_⟩
  have hE : ‖Complex.exp (Complex.I * t * (b * gramX ε y).trace)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, trace_im ε y hb]
  rw [norm_mul, hE, mul_one]
  exact hK σ hσ y

theorem hasDerivAt_Psi (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (t : ℝ) {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian) {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (R : PX m n) (s : ℝ) :
    HasDerivAt (Psi ε c t H b R) (Psi ε c t H b (DMp ε c H R) s) s ∧
      ∀ P : PX m n, Integrable fun y => evX P (mulR (aE H s) y) * gs c (mulR (aE H s) y) *
        Complex.exp (Complex.I * t * (b * gramX ε y).trace) := by
  haveI : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have hd : ((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℕ) : ℝ) <
      (Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1 := by linarith
  have hint : ∀ P : PX m n, Integrable fun y => evX P (mulR (aE H s) y) * gs c (mulR (aE H s) y) *
      Complex.exp (Complex.I * t * (b * gramX ε y).trace) := by
    intro P
    obtain ⟨K, hK0, hK⟩ := exists_norm_evX_gs_exp_le_polynomial_decay ε hc t H hb P s
    exact ((integrable_one_add_norm hd).const_mul K).mono'
      (continuous_evX_gs_exp_trace_mulR_aE ε c t H b P s).aestronglyMeasurable
      (ae_of_all _ fun y => hK s (by simp) y)
  refine ⟨?_, hint⟩
  obtain ⟨K, hK0, hK⟩ := exists_norm_evX_gs_exp_le_polynomial_decay ε hc t H hb (DMp ε c H R) s
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun σ y => evX R (mulR (aE H σ) y) * gs c (mulR (aE H σ) y) *
      Complex.exp (Complex.I * t * (b * gramX ε y).trace))
    (F' := fun σ y => evX (DMp ε c H R) (mulR (aE H σ) y) * gs c (mulR (aE H σ) y) *
      Complex.exp (Complex.I * t * (b * gramX ε y).trace))
    (bound := fun y => K * (1 + ‖y‖) ^ (-((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1)))
    (x₀ := s) (s := Metric.ball s 1) (Metric.ball_mem_nhds s one_pos)
    (Eventually.of_forall fun σ => (continuous_evX_gs_exp_trace_mulR_aE ε c t H b R σ).aestronglyMeasurable)
    (hint R) (continuous_evX_gs_exp_trace_mulR_aE ε c t H b (DMp ε c H R) s).aestronglyMeasurable
    (ae_of_all _ fun y σ hσ => hK σ (by rwa [Metric.mem_ball, Real.dist_eq] at hσ) y)
    ((integrable_one_add_norm hd).const_mul K)
    (ae_of_all _ fun y σ _ => (hasDerivAt_phiE c ε hH R y σ).mul_const _)
  exact key.2

theorem evX_DM (ε : Fin m → Bool) (c : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) (z : Fin m → Fin n → ℂ) :
    evX (DM ε c H R) z = ((m : ℂ) * H.trace) * evX R z + evX (DMp ε c H R) z := by
  have h : DM ε c H R = C ((m : ℂ) * H.trace) * R + DMp ε c H R := by
    simp only [DM, DMp]
    ring
  rw [h, evX_eq, evX_eq, evX_eq, map_add (f := _), map_mul, eval_C]

end PositivityTheory.Rg.Sw.AbsSt.SDM

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt.SDM

theorem mDer : MDer := by
  intro m n ε c t p q e sL ρ hL R H hH f hf g hg s
  obtain ⟨C0, -, hcell⟩ := hL.cell
  obtain ⟨y₁, b, hy₁, hb, hdec⟩ := cellM n H hH f hf g hg
  have hpq : (p : ℂ) + q = m := by
    rcases hL.sign with ⟨_, hp, hq⟩ | ⟨_, hp, hq⟩
    · rw [hp, hq]
      exact_mod_cast DF.cnt_add ε
    · rw [hp, hq, add_comm]
      exact_mod_cast DF.cnt_add ε
  have hrep : ∀ (P : PX m n) (σ : ℝ), sL P (g * f σ) =
      F0 p q e y₁ * C0 * (Complex.exp (↑σ * (↑m * H.trace)) * Psi ε c t H b P σ) := by
    intro P σ
    obtain ⟨mA, w, hmA, hF0, hw, hb', heq⟩ := hdec p q e σ
    have hex : Complex.exp (-(↑σ * ↑(p + q) * H.trace)) *
        Complex.exp (((2 * m * σ * H.trace.re : ℝ) : ℂ)) = Complex.exp (↑σ * (↑m * H.trace)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      rw [trace_herm_re hH]
      linear_combination (-(σ : ℂ) * H.trace) * hpq
    rw [heq, mul_assoc y₁ mA w, hL.law P y₁ _ hy₁, hL.law P mA w hmA, hcell P w _ hb' hw,
      secN_aE ε c t hH b P σ, hF0, ← hex]
    ring
  have hΨ := hasDerivAt_Psi ε hL.cpos t hH hb R s
  have hE : HasDerivAt (fun σ : ℝ => Complex.exp (↑σ * (↑m * H.trace)))
      (Complex.exp (↑s * (↑m * H.trace)) * (↑m * H.trace)) s := by
    have h1 := ((hasDerivAt_id s).ofReal_comp.mul_const ((m : ℂ) * H.trace)).cexp
    simpa using h1
  have hfun : (fun σ : ℝ => sL R (g * f σ)) = fun σ =>
      F0 p q e y₁ * C0 * (Complex.exp (↑σ * (↑m * H.trace)) * Psi ε c t H b R σ) := funext (hrep R)
  have hlin : Psi ε c t H b (DM ε c H R) s =
      (↑m * H.trace) * Psi ε c t H b R s + Psi ε c t H b (DMp ε c H R) s := by
    unfold Psi
    rw [← integral_const_mul, ← integral_add ((hΨ.2 R).const_mul _) (hΨ.2 _)]
    congr 1
    funext y
    rw [evX_DM]
    ring
  rw [hfun, hrep (DM ε c H R) s, hlin]
  exact ((hE.mul hΨ.1).const_mul (F0 p q e y₁ * C0)).congr_deriv (by ring)

end PositivityTheory.Rg.Sw.AbsSt
end
end

