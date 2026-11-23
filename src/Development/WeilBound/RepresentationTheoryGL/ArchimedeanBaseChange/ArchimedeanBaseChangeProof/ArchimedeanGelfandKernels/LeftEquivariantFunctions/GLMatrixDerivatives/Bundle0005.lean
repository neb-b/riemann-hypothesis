module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.FderivApplyConst
section
noncomputable section

open MeasureTheory Matrix Finset Set Filter
open scoped ContDiff Topology

namespace PositivityTheory.RgBcC.LfSt.ChainOf2

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt.ChainPf
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Partial

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem fderiv_snd' {U : ℝ × Mat n → W} {s : ℝ} {x : Mat n} (hU : DifferentiableAt ℝ U (s, x)) (v : Mat n) :
    fderiv ℝ (fun y => U (s, y)) x v = fderiv ℝ U (s, x) (0, v) := by
  have h : HasFDerivAt (fun y : Mat n => U (s, y)) ((fderiv ℝ U (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Mat n))) x :=
    hU.hasFDerivAt.comp x (hasFDerivAt_prodMk_right s x)
  rw [h.fderiv]
  rfl

theorem hasDerivAt_fst' {U : ℝ × Mat n → W} {s : ℝ} {x : Mat n} (hU : DifferentiableAt ℝ U (s, x)) :
    HasDerivAt (fun t => U (t, x)) (fderiv ℝ U (s, x) (1, 0)) s := by
  have hp : HasDerivAt (fun t : ℝ => ((t, x) : ℝ × Mat n)) ((1 : ℝ), (0 : Mat n)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  exact hU.hasFDerivAt.comp_hasDerivAt s hp

theorem fderiv_apply_const' {F : ℝ × Mat n → (ℝ × Mat n →L[ℝ] W)} {q : ℝ × Mat n} (hF : DifferentiableAt ℝ F q)
    (w d : ℝ × Mat n) : fderiv ℝ (fun q' => F q' w) q d = fderiv ℝ F q d w := by
  set_option backward.isDefEq.respectTransparency false in
   have h := fderiv_clm_apply hF (show DifferentiableAt ℝ (fun _ : ℝ × Mat n => w) q from differentiableAt_const w)
   rw [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add] at h
   exact congrArg (fun L : ℝ × Mat n →L[ℝ] W => L d) h

theorem mixed' {U : ℝ × Mat n → W} {O : Set (ℝ × Mat n)} (hO : IsOpen O) (hU : ContDiffOn ℝ ∞ U O) {q : ℝ × Mat n}
    (hq : q ∈ O) (a b : ℝ × Mat n) :
    fderiv ℝ (fun q' => fderiv ℝ U q' a) q b = fderiv ℝ (fun q' => fderiv ℝ U q' b) q a := by
  have hd := hU.fderiv_of_isOpen hO (m := ∞) (by simp)
  have hdq : DifferentiableAt ℝ (fderiv ℝ U) q :=
    (hd.contDiffAt (hO.mem_nhds hq)).differentiableAt (by simp)
  have hs := (hU.contDiffAt (hO.mem_nhds hq)).isSymmSndFDerivAt (by simp)
  rw [fderiv_apply_const' hdq, fderiv_apply_const' hdq]
  exact hs b a

theorem pd_smooth {U : ℝ × Mat n → W} {O : Set (ℝ × Mat n)} (hO : IsOpen O) (hU : ContDiffOn ℝ ∞ U O) (a : ℝ × Mat n) :
    ContDiffOn ℝ ∞ (fun q => fderiv ℝ U q a) O :=
  (hU.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const

theorem diffAt_of {U : ℝ × Mat n → W} {O : Set (ℝ × Mat n)} (hO : IsOpen O) (hU : ContDiffOn ℝ ∞ U O) {q : ℝ × Mat n}
    (hq : q ∈ O) : DifferentiableAt ℝ U q :=
  (hU.contDiffAt (hO.mem_nhds hq)).differentiableAt (by simp)

end Partial

theorem dc_add_smul (hG : GelComm) {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)}
    (F₁ F₂ : Mat n → E.V) (h₁ : ContDiffOn ℝ ∞ F₁ (GLs n)) (h₂ : ContDiffOn ℝ ∞ F₂ (GLs n)) (c : ℂ) :
    ∀ x ∈ GLs n, DC ε Fr (c • (F₁ + F₂)) x = c • (DC ε Fr F₁ x + DC ε Fr F₂ x) := by
  intro x hx
  have hs : ContDiffOn ℝ ∞ (F₁ + F₂) (GLs n) := h₁.add h₂
  simp only [DC]
  rw [← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [GlobalTheory.CompanionTheory.RCalc.Rd_smul c (hb p) hs hx, Pi.smul_apply, GlobalTheory.CompanionTheory.RCalc.Rd_add (hb p) h₁ h₂ hx, Pi.add_apply]
  simp only [Pi.smul_apply, Pi.add_apply, map_add (f := _), map_smul, smul_add]
  abel

theorem om_DC (hG : GelComm) {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)}
    {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)} {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}
    (h : CxData lam E Fr ε ι S Γ T) (f : Mat n → E.V) (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ∀ x ∈ GLs n, Om (DC ε Fr f) x = DC ε Fr (Om f) x := by
  intro x hx
  have ht := (hG n E.V E.V true 2 f hf).1
  have hfa := (hG n E.V E.V false 2 f hf).1
  have e : Om f = (2 : ℂ) • (gel true 2 f + gel false 2 f) := rfl
  rw [e, dc_add_smul hG _ _ ht hfa 2 x hx]
  simp only [Om, Pi.smul_apply, Pi.add_apply]
  rw [gel_DC hG h f hf true 2 x hx, gel_DC hG h f hf false 2 x hx]

theorem dCwave_of (hin : DCinCE) : DCwave := by
  intro hG n lam E Fr ε ι S Γ T hCx u hu
  obtain ⟨hsm, hCE, heq, h0⟩ := hu
  set O : Set (ℝ × Mat n) := Set.univ ×ˢ GLs n with hOdef
  have hO : IsOpen O := isOpen_univ.prod GlobalTheory.CompanionTheory.RCalc.isOpen_GLs
  set Ψ : ℝ × Mat n → E.V := Function.uncurry u with hΨ
  have hmem : ∀ s, ∀ x ∈ GLs n, ((s, x) : ℝ × Mat n) ∈ O := fun s x hx => ⟨Set.mem_univ _, hx⟩
  set A : ℝ × Mat n → E.V := fun q => fderiv ℝ Ψ q (1, 0) with hA
  have hAs : ContDiffOn ℝ ∞ A O := pd_smooth hO hsm (1, 0)
  set B : ℝ × Mat n → E.V := fun q => fderiv ℝ A q (1, 0) with hB
  have hBs : ContDiffOn ℝ ∞ B O := pd_smooth hO hAs (1, 0)
  set D : Fin n × Fin n → (E.V →L[ℂ] E.V) := fun p => fderiv ℝ Fr 1 (hb p) with hD

  have hslice : ∀ s, ∀ x ∈ GLs n, DC ε Fr (u s) x =
      ∑ p, ε (hb p) (fderiv ℝ Ψ (s, x) (0, x * hb p) + D p (Ψ (s, x))) := by
    intro s x hx
    simp only [DC, Rd]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [show u s = fun y => Ψ (s, y) from rfl, fderiv_snd' (diffAt_of hO hsm (hmem s x hx))]

  have hΨA : ∀ s, ∀ x ∈ GLs n, HasDerivAt (fun t => u t x) (A (s, x)) s := fun s x hx =>
    hasDerivAt_fst' (U := Ψ) (diffAt_of hO hsm (hmem s x hx))
  have hAB : ∀ s, ∀ x ∈ GLs n, HasDerivAt (fun t => A (t, x)) (B (s, x)) s := fun s x hx =>
    hasDerivAt_fst' (U := A) (diffAt_of hO hAs (hmem s x hx))
  have hBom : ∀ s, ∀ x ∈ GLs n, B (s, x) = Om (u s) x := by
    intro s x hx
    rw [← heq s x hx, iteratedDeriv_succ, iteratedDeriv_one]
    have h1 : deriv (fun t => u t x) = fun t => A (t, x) := funext fun t => (hΨA t x hx).deriv
    rw [h1, (hAB s x hx).deriv]
  have hdpsi : ∀ (w : ℝ × Mat n), ∀ s, ∀ x ∈ GLs n,
      HasDerivAt (fun t => fderiv ℝ Ψ (t, x) w) (fderiv ℝ A (s, x) w) s := by
    intro w s x hx
    have hd : DifferentiableAt ℝ (fun q => fderiv ℝ Ψ q w) (s, x) := diffAt_of hO (pd_smooth hO hsm w) (hmem s x hx)
    have := hasDerivAt_fst' hd
    rwa [mixed' hO hsm (hmem s x hx) w (1, 0)] at this
  have hdA : ∀ (w : ℝ × Mat n), ∀ s, ∀ x ∈ GLs n,
      HasDerivAt (fun t => fderiv ℝ A (t, x) w) (fderiv ℝ B (s, x) w) s := by
    intro w s x hx
    have hd : DifferentiableAt ℝ (fun q => fderiv ℝ A q w) (s, x) := diffAt_of hO (pd_smooth hO hAs w) (hmem s x hx)
    have := hasDerivAt_fst' hd
    rwa [mixed' hO hAs (hmem s x hx) w (1, 0)] at this
  refine ⟨?_, fun t => hin n lam E Fr ε ι S Γ T hCx (u t) (hCE t), ?_, ?_⟩
  ·
    have hsm' : ContDiffOn ℝ ∞ (fun q : ℝ × Mat n =>
        ∑ p, ε (hb p) (fderiv ℝ Ψ q (0, q.2 * hb p) + D p (Ψ q))) O := by
      refine ContDiffOn.sum fun p _ => ?_
      refine ((ε (hb p)).restrictScalars ℝ).contDiff.comp_contDiffOn ?_
      refine ContDiffOn.add ?_ (((D p).restrictScalars ℝ).contDiff.comp_contDiffOn hsm)
      have hv : ContDiff ℝ ∞ (fun q : ℝ × Mat n => ((0 : ℝ), q.2 * hb p)) :=
        contDiff_const.prodMk ((GlobalTheory.CompanionTheory.RCalc.mulR (hb p)).contDiff.comp contDiff_snd)
      exact (hsm.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply hv.contDiffOn
    refine hsm'.congr fun q hq => ?_
    obtain ⟨s, x⟩ := q
    exact hslice s x hq.2
  · intro t g hg
    have hf : ∀ s, (fun s => DC ε Fr (u s) g) s = ∑ p, ε (hb p) (fderiv ℝ Ψ (s, g) (0, g * hb p) + D p (Ψ (s, g))) :=
      fun s => hslice s g hg
    have hf1 : ∀ s, HasDerivAt (fun s => DC ε Fr (u s) g)
        (∑ p, ε (hb p) (fderiv ℝ A (s, g) (0, g * hb p) + D p (A (s, g)))) s := by
      intro s
      have : (fun s => DC ε Fr (u s) g) = fun s => ∑ p, ε (hb p) (fderiv ℝ Ψ (s, g) (0, g * hb p) + D p (Ψ (s, g))) :=
        funext hf
      rw [this]
      refine HasDerivAt.fun_sum fun p _ => ?_
      exact ((ε (hb p)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
        ((hdpsi _ s g hg).add (((D p).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hΨA s g hg)))
    have hf2 : ∀ s, HasDerivAt (fun s => ∑ p, ε (hb p) (fderiv ℝ A (s, g) (0, g * hb p) + D p (A (s, g))))
        (∑ p, ε (hb p) (fderiv ℝ B (s, g) (0, g * hb p) + D p (B (s, g)))) s := by
      intro s
      refine HasDerivAt.fun_sum fun p _ => ?_
      exact ((ε (hb p)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
        ((hdA _ s g hg).add (((D p).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hAB s g hg)))
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have e1 : deriv (fun s => DC ε Fr (u s) g) =
        fun s => ∑ p, ε (hb p) (fderiv ℝ A (s, g) (0, g * hb p) + D p (A (s, g))) := funext fun s => (hf1 s).deriv
    rw [e1, (hf2 t).deriv]
    have hu2 : ContDiffOn ℝ ∞ (u t) (GLs n) := (hCE t).1
    have hom : ContDiffOn ℝ ∞ (Om (u t)) (GLs n) := by
      have ht := (hG n E.V E.V true 2 (u t) hu2).1
      have hfa := (hG n E.V E.V false 2 (u t) hu2).1
      exact (ht.add hfa).const_smul (2 : ℂ)
    rw [om_DC hG hCx (u t) hu2 g hg]
    simp only [DC, Rd]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hBe : EqOn (fun y => B (t, y)) (Om (u t)) (GLs n) := fun y hy => hBom t y hy
    have hev : (fun y => B (t, y)) =ᶠ[𝓝 g] Om (u t) :=
      Filter.eventuallyEq_of_mem (GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds hg) hBe
    rw [← fderiv_snd' (diffAt_of hO hBs (hmem t g hg)), hev.fderiv_eq, hBom t g hg]
  · intro g hg
    have hf1 : HasDerivAt (fun s => DC ε Fr (u s) g)
        (∑ p, ε (hb p) (fderiv ℝ A (0, g) (0, g * hb p) + D p (A (0, g)))) 0 := by
      have : (fun s => DC ε Fr (u s) g) =
          fun s => ∑ p, ε (hb p) (fderiv ℝ Ψ (s, g) (0, g * hb p) + D p (Ψ (s, g))) := funext fun s => hslice s g hg
      rw [this]
      refine HasDerivAt.fun_sum fun p _ => ?_
      exact ((ε (hb p)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
        ((hdpsi _ 0 g hg).add (((D p).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hΨA 0 g hg)))
    rw [hf1.deriv]
    have hA0 : ∀ x ∈ GLs n, A (0, x) = 0 := fun x hx => by rw [← (hΨA 0 x hx).deriv]; exact h0 x hx
    have hev : (fun y => A (0, y)) =ᶠ[𝓝 g] fun _ => (0 : E.V) :=
      Filter.eventuallyEq_of_mem (GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds hg) fun y hy => hA0 y hy
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [← fderiv_snd' (diffAt_of hO hAs (hmem 0 g hg)), hev.fderiv_eq, hA0 g hg]
    simp

end PositivityTheory.RgBcC.LfSt.ChainOf2
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.InvContDiffOn
section
noncomputable section

open Matrix Finset
open scoped ContDiff ComplexConjugate ComplexOrder

namespace PositivityTheory.RgBcC.LfSt.Kchain.KcInv

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.Kchain
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}

theorem entry_contDiff (a b : Fin n) : ContDiff ℝ ∞ (fun y : Mat n => y a b) :=
  contDiff_apply_apply ℝ a b

theorem mat_contDiffOn {F : E → Mat n} (h : ∀ a b, ContDiffOn ℝ ∞ (fun x => F x a b) s) :
    ContDiffOn ℝ ∞ F s := by
  have : ContDiffOn ℝ ∞ (fun x => (F x : Fin n → Fin n → ℂ)) s :=
    contDiffOn_pi.2 fun a => contDiffOn_pi.2 fun b => h a b
  exact this

theorem mat_contDiff {F : E → Mat n} (h : ∀ a b, ContDiff ℝ ∞ (fun x => F x a b)) : ContDiff ℝ ∞ F := by
  rw [← contDiffOn_univ]
  exact mat_contDiffOn fun a b => (h a b).contDiffOn

theorem entry_of {F : E → Mat n} (h : ContDiffOn ℝ ∞ F s) (a b : Fin n) : ContDiffOn ℝ ∞ (fun x => F x a b) s :=
  (entry_contDiff a b).comp_contDiffOn h

theorem det_contDiffOn {F : E → Mat n} (h : ∀ a b, ContDiffOn ℝ ∞ (fun x => F x a b) s) :
    ContDiffOn ℝ ∞ (fun x => (F x).det) s := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)

theorem det_contDiff : ContDiff ℝ ∞ (fun y : Mat n => y.det) := by
  rw [← contDiffOn_univ]
  exact det_contDiffOn fun a b => (entry_contDiff a b).contDiffOn

theorem mul_contDiffOn {F H : E → Mat n} (hF : ContDiffOn ℝ ∞ F s) (hH : ContDiffOn ℝ ∞ H s) :
    ContDiffOn ℝ ∞ (fun x => F x * H x) s := by
  refine mat_contDiffOn fun a b => ?_
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun c _ => (entry_of hF a c).mul (entry_of hH c b)

theorem inv_contDiffOn : ContDiffOn ℝ ∞ (fun y : Mat n => y⁻¹) (GLs n) := by
  refine mat_contDiffOn fun a b => ?_
  have hd : ContDiffOn ℝ ∞ (fun y : Mat n => y.det) (GLs n) := det_contDiff.contDiffOn
  have hadj : ContDiffOn ℝ ∞ (fun y : Mat n => y.adjugate a b) (GLs n) := by
    simp only [Matrix.adjugate_apply]
    refine det_contDiffOn fun i j => ?_
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact contDiffOn_const
    · exact (entry_contDiff _ _).contDiffOn
  have : ContDiffOn ℝ ∞ (fun y : Mat n => (y.det)⁻¹ * y.adjugate a b) (GLs n) :=
    (hd.inv fun y hy => hy).mul hadj
  refine this.congr fun y _ => ?_
  simp [Matrix.inv_def, Ring.inverse_eq_inv]

theorem star_contDiff : ContDiff ℝ ∞ (fun y : Mat n => yᴴ) :=
  mat_contDiff fun a b => by
    simp only [Matrix.conjTranspose_apply]
    exact Complex.conjCLE.contDiff.comp (entry_contDiff b a)

theorem conjT_mem {y : Mat n} (hy : y ∈ GLs n) : yᴴ ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq, Matrix.det_conjTranspose] at *
  exact (star_ne_zero).2 hy

theorem inv_mem {y : Mat n} (hy : y ∈ GLs n) : y⁻¹ ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq, Matrix.det_nonsing_inv] at *
  rw [Ring.inverse_eq_inv]; exact inv_ne_zero hy

theorem mul_mem {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

theorem coneGL : ConeGL := by
  intro n σ hσ v hv
  have hpd : (hOf v).PosDef := hv
  have hd : (hOf v).det ≠ 0 := hpd.det_pos.ne'
  refine ⟨?_, hd⟩
  have h1 := congrArg Matrix.det (hσ v hv)
  rw [Matrix.det_mul] at h1
  intro h0
  exact hd (by rw [← h1, h0, zero_mul])

theorem hOf_contDiff : ContDiff ℝ ∞ (fun v : Fin n × Fin n → ℝ => hOf v) := by
  unfold hOf
  refine ContDiff.sum fun p _ => ?_
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ (fun _ => ℝ) p)).smul contDiff_const

theorem kcSmooth : KcSmooth := by
  intro n V _ _ σ c Fr k Γ T d hd hσs hσ hFr hk
  have hgl := coneGL n σ hσ
  let U := cone n ×ˢ cone n
  have h1 : ContDiffOn ℝ ∞ (fun y : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => σ y.1) U :=
    hσs.comp contDiff_fst.contDiffOn fun y hy => hy.1
  have h2 : ContDiffOn ℝ ∞ (fun y : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => σ y.2) U :=
    hσs.comp contDiff_snd.contDiffOn fun y hy => hy.2
  have m1 : ∀ y ∈ U, σ y.1 ∈ GLs n := fun y hy => (hgl y.1 hy.1).1
  have m2 : ∀ y ∈ U, σ y.2 ∈ GLs n := fun y hy => (hgl y.2 hy.2).1
  have hi1 : ContDiffOn ℝ ∞ (fun y : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => (σ y.1)⁻¹) U :=
    inv_contDiffOn.comp h1 m1
  have hi2 : ContDiffOn ℝ ∞ (fun y : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => (σ y.2)⁻¹) U :=
    inv_contDiffOn.comp h2 m2
  have hs2 : ContDiffOn ℝ ∞ (fun y : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => (σ y.2)ᴴ⁻¹) U :=
    inv_contDiffOn.comp (star_contDiff.comp_contDiffOn h2) fun y hy => conjT_mem (m2 y hy)
  have hw : ContDiffOn ℝ ∞ (fun y : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => (σ y.1)⁻¹ * d * (σ y.2)ᴴ⁻¹) U :=
    mul_contDiffOn (mul_contDiffOn hi1 contDiffOn_const) hs2
  have hwm : ∀ y ∈ U, (σ y.1)⁻¹ * d * (σ y.2)ᴴ⁻¹ ∈ GLs n := fun y hy =>
    mul_mem (mul_mem (inv_mem (m1 y hy)) hd) (inv_mem (conjT_mem (m2 y hy)))
  have hK : ContDiffOn ℝ ∞ (fun y : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) =>
      Kf Fr k Γ T d (σ y.1) (σ y.2)) U := by
    unfold Kf
    refine ContDiffOn.mul (ContDiffOn.mul (ContDiffOn.mul (ContDiffOn.mul (hFr.comp h1 m1) (hk.comp hw hwm))
      contDiffOn_const) contDiffOn_const) (hFr.comp hi2 fun y hy => inv_mem (m2 y hy))
  have hW : ContDiffOn ℝ ∞ (fun y : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) =>
      (c : ℂ) * ((hOf y.2).det ^ n)⁻¹) U := by
    refine contDiffOn_const.mul (ContDiffOn.inv ?_ fun y hy => pow_ne_zero _ (hgl y.2 hy.2).2)
    exact ((det_contDiff.comp hOf_contDiff).comp contDiff_snd).contDiffOn.pow n
  exact hW.smul hK

end PositivityTheory.RgBcC.LfSt.Kchain.KcInv
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KcDual
section
noncomputable section

open Matrix Finset

namespace PositivityTheory.RgBcC.LfSt.Kchain.KcDual

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.Kchain
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem trace_hOf_mul (hH : HbFacts) (u u' : Fin n × Fin n → ℝ) :
    (hOf u * hOf u').trace = ∑ p, ((u p * u' p : ℝ) : ℂ) := by
  obtain ⟨-, horth, -⟩ := hH n
  simp only [hOf, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, horth, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  push_cast
  ring

theorem map_hOf {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (α : Mat n →ₗ[ℝ] (V →L[ℂ] V))
    (u : Fin n × Fin n → ℝ) : α (hOf u) = ∑ p, ((u p : ℝ) : ℂ) • α (hb p) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hOf, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have e : ((u p : ℝ) : ℂ) • (hb p : Mat n) = (u p) • hb p := by
    ext a b
    simp [Complex.real_smul]
  rw [e, map_smul]
  ext v
  simp [Complex.coe_smul]

theorem dualSum (hH : HbFacts) : DualSum := by
  intro n V _ _ α β A A' hA hA' htr
  obtain ⟨-, -, hcoord, -, -, -, -, -⟩ := hH n
  set a : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ := fun i p => coords (A i) p with ha
  set a' : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ := fun i p => coords (A' i) p with ha'
  have eA : ∀ i, A i = hOf (a i) := fun i => (hcoord _ (hA i)).symm
  have eA' : ∀ i, A' i = hOf (a' i) := fun i => (hcoord _ (hA' i)).symm
  have h1 : a * a'ᵀ = 1 := by
    ext i j
    have := htr i j
    rw [eA i, eA' j, trace_hOf_mul hH] at this
    have hre := congrArg Complex.re this
    simp only [Complex.re_sum, Complex.ofReal_re] at hre
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
    rw [hre]
    split_ifs <;> simp
  have h2 : a'ᵀ * a = 1 := mul_eq_one_comm.mp h1
  calc ∑ i, α (A i) * β (A' i)
      = ∑ i, ∑ p, ∑ q, ((a i p * a' i q : ℝ) : ℂ) • (α (hb p) * β (hb q)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [eA i, eA' i, map_hOf α, map_hOf β, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        rw [smul_mul_smul_comm]
        push_cast
        rfl
    _ = ∑ p, ∑ q, ((a'ᵀ * a) q p : ℂ) • (α (hb p) * β (hb q)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← Finset.sum_smul]
        congr 1
        simp only [Matrix.mul_apply, Matrix.transpose_apply]
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = ∑ p, α (hb p) * β (hb p) := by
        rw [h2]
        refine Finset.sum_congr rfl fun p _ => ?_
        simp [Matrix.one_apply]

end PositivityTheory.RgBcC.LfSt.Kchain.KcDual
end
end

