module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0796
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699
public import GroundTheory.AutomorphicForms.MultiplicityOne.Functional
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0846
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0853

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.LFun GlobalTheory.PRep Formalism.UG
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.MultiplicityOne

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem whit_mul_right (F : GA E a → ℂ) (y x : GA E a) : whit F (y * x) = whit (fun z => F (z * x)) y := by
  simp only [whit, whittaker, mul_assoc]

theorem integrableOn_whit {F : GA E a → ℂ} (hc : Continuous F) (y : GA E a) :
    IntegrableOn (fun X => F (uGL X * y) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ))
      (vecDomain E (Pos a)) (vecMeasure E (Pos a)) := by
  have hcont : Continuous fun X : Pos a → Ad E =>
      F (uGL X * y) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
    (hc.comp (continuous_uGL.mul continuous_const)).mul continuous_adelicChar_neg_supSum
  exact (hcont.continuousOn.integrableOn_compact isCompact_closure_vecDomain).mono_set subset_closure

theorem whit_add {F G : GA E a → ℂ} (hF : Continuous F) (hG : Continuous G) (y : GA E a) :
    whit (F + G) y = whit F y + whit G y := by
  unfold whit whittaker
  rw [← integral_add (integrableOn_whit hF y) (integrableOn_whit hG y)]
  congr 1
  funext X
  simp only [Pi.add_apply, add_mul]

theorem whit_smul (c : ℂ) (F : GA E a → ℂ) (y : GA E a) : whit (c • F) y = c * whit F y := by
  unfold whit whittaker
  rw [← integral_const_mul]
  congr 1
  funext X
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

def psiLocChar (w : HeightOneSpectrum (𝓞 E)) : AddChar (w.adicCompletion E) ℂ where
  toFun := psiLoc w
  map_zero_eq_one' := by simp [psiLoc]
  map_add_eq_mul' x y := by simp only [psiLoc, map_add (f := _), AddChar.map_add_eq_mul, Circle.coe_mul]

theorem finGL_locGL_apply (w : HeightOneSpectrum (𝓞 E)) (k : GL (Fin a) (w.adicCompletion E)) (i j : Fin a) :
    ((finGL E a (locGL E a w k) : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) i j =
      (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sFin E (sLoc E w ((1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j))
        + sFin E (sLoc E w ((k : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j)) := by
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j) +
    sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j - sLoc E w ((1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j)
      + sLoc E w ((k : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j)) = _
  rw [map_add (f := _), map_sub]
  abel

end GlobalTheory.JSW

namespace GlobalTheory.JSW
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem GA_ext {x y : GA E a}
    (hinf : GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing E) (Af E)) x =
      GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing E) (Af E)) y)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 E), GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) x =
      GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) y) : x = y := by
  ext i j
  refine Prod.ext ?_ (FiniteAdeleRing.ext _ fun v => ?_)
  · exact congrArg (fun m : GL (Fin a) (InfiniteAdeleRing E) => (m : Matrix (Fin a) (Fin a) (InfiniteAdeleRing E)) i j) hinf
  · exact congrArg (fun m : GL (Fin a) (v.adicCompletion E) => (m : Matrix (Fin a) (Fin a) (v.adicCompletion E)) i j) (hfin v)

theorem commute_finGL_locGL (w : HeightOneSpectrum (𝓞 E)) {g : GA E a}
    (hg : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = 1) (k : GL (Fin a) (w.adicCompletion E)) :
    g * finGL E a (locGL E a w k) = finGL E a (locGL E a w k) * g := by
  have key : ∀ {R : Type} [CommRing R] (c : Ad E →+* R),
      (GeneralLinearGroup.map c g = 1 ∨ GeneralLinearGroup.map c (finGL E a (locGL E a w k)) = 1) →
      GeneralLinearGroup.map c (g * finGL E a (locGL E a w k)) =
        GeneralLinearGroup.map c (finGL E a (locGL E a w k) * g) := by
    intro R _ c h
    rw [map_mul, map_mul]
    rcases h with h | h <;> rw [h] <;> simp
  refine GA_ext (key _ (Or.inr ?_)) fun v => key _ ?_
  · exact map_cornerGL_of_zero _ _ (fun x => rfl) _
  · by_cases hv : v = w
    · subst hv; exact Or.inl hg
    · refine Or.inr ?_
      rw [finGL, map_cornerGL_of_hom (sFin E) ((pLoc E v).comp (pFin E)) (pLoc E v) (fun x => rfl)]
      exact pLoc_locGL_of_ne hv k

end GlobalTheory.JSW

namespace GlobalTheory.JSW
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem finGL_locGL_eq_uGL (w : HeightOneSpectrum (𝓞 E)) {u : GL (Fin a) (w.adicCompletion E)}
    (hu : u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a)) :
    finGL E a (locGL E a w u) =
      uGL (fun p : Pos a => sFin E (sLoc E w ((u : Matrix (Fin a) (Fin a) (w.adicCompletion E)) p.1.1 p.1.2))) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 hu
  ext i j
  rw [finGL_locGL_apply, coe_uGL, uMat_apply]
  by_cases hij : i = j
  · subst hij; simp [h2]
  · rw [if_neg hij, Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero, map_zero, sub_zero, zero_add]
    by_cases hlt : i < j
    · rw [dite_eq_left hlt]
    · rw [dite_eq_right hlt, h1 i j (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hij)), map_zero, map_zero]

theorem sum_pos_superdiag {M : Type} [AddCommMonoid M] (f : Fin a → Fin a → M) :
    ∑ p ∈ Finset.univ.filter (fun p : Pos a => (p.1.2 : ℕ) = p.1.1 + 1 ∧ 0 ≤ (p.1.2 : ℕ)), f p.1.1 p.1.2 =
      ∑ i : Fin a, ∑ j ∈ Finset.univ.filter (fun j : Fin a => (j : ℕ) = (i : ℕ) + 1), f i j := by
  classical
  have hR : ∑ i : Fin a, ∑ j ∈ Finset.univ.filter (fun j : Fin a => (j : ℕ) = (i : ℕ) + 1), f i j =
      ∑ q ∈ Finset.univ.filter (fun q : Fin a × Fin a => (q.2 : ℕ) = q.1 + 1), f q.1 q.2 := by
    simp only [Finset.sum_filter]
    exact (Fintype.sum_prod_type' (fun x y : Fin a => if (y : ℕ) = (x : ℕ) + 1 then f x y else 0)).symm
  rw [hR]
  refine Finset.sum_bij (fun p _ => p.1) (fun p hp => ?_) (fun p _ q _ h => Subtype.ext h) (fun q hq => ?_)
    (fun p _ => rfl)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact hp.1
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    refine ⟨⟨q, ?_⟩, ?_, rfl⟩
    · rw [Fin.lt_def]; omega
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hq, Nat.zero_le _⟩

theorem supSum_sLoc (w : HeightOneSpectrum (𝓞 E)) (u : GL (Fin a) (w.adicCompletion E)) :
    supSum 0 (fun p : Pos a => sFin E (sLoc E w ((u : Matrix (Fin a) (Fin a) (w.adicCompletion E)) p.1.1 p.1.2))) =
      sFin E (sLoc E w (GlobalTheory.Whittaker.superDiag u)) := by
  classical
  let t : w.adicCompletion E →+ Ad E := (sFin E).toAddMonoidHom.comp (sLoc E w).toAddMonoidHom
  change supSum 0 (fun p : Pos a => t ((u : Matrix (Fin a) (Fin a) (w.adicCompletion E)) p.1.1 p.1.2)) =
    t (GlobalTheory.Whittaker.superDiag u)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [GlobalTheory.Whittaker.superDiag, map_sum, supSum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  exact sum_pos_superdiag (fun i j => t ((u : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j))

end GlobalTheory.JSW

namespace GlobalTheory.JSW
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem whit_mul_locGL_diagPow_of_fixed (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E))
    (hψ : ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, psiLoc w (x * y) = 1) ↔ x ∈ Ov E w)
    (α : Fin a → ℂˣ) (hα : HasSatGL w (π.locRep w) (Finset.univ.val.map α))
    (φ : π.V) (hφ : φ ∈ fixed (π.locRep w) (KGL w (n := a)))
    (g : GA E a) (hg : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = 1)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifV E w (ϖ : w.adicCompletion E)) (l : Fin a → ℕ) :
    whit φ.1.1 (g * finGL E a (locGL E a w (diagPow ϖ l))) =
      sphW (qV E w) (fun i => (α i : ℂ)) l * whit φ.1.1 g := by
  classical
  have hcont : ∀ ψ : π.V, Continuous ψ.1.1 := fun ψ => (π.cusp _ ψ.2).1.continuous
  have hleft : AutomorphicForm.IsLeftInvariant φ.1.1 := fun γ y => by
    rw [show AdelicGLn.diagonal E a γ = ratGL E a γ from Units.ext (Matrix.ext fun _ _ => rfl)]
    exact (π.cusp _ φ.2).1.left γ y
  let f : π.V →ₗ[ℂ] (GL (Fin a) (w.adicCompletion E) → ℂ) :=
    { toFun := fun ψ h => whit ψ.1.1 (g * finGL E a (locGL E a w h))
      map_add' := fun ψ ψ' => funext fun h => whit_add (hcont ψ) (hcont ψ') _
      map_smul' := fun c ψ => funext fun h => whit_smul c ψ.1.1 _ }
  have hf : ∀ k (ψ : π.V), f (π.locRep w k ψ) = rightReg ℂ _ ℂ k (f ψ) := by
    intro k ψ
    funext h
    change whit (fun z => ψ.1.1 (z * finGL E a (locGL E a w k))) (g * finGL E a (locGL E a w h)) =
      whit ψ.1.1 (g * finGL E a (locGL E a w (h * k)))
    rw [map_mul, map_mul, ← mul_assoc, whit_mul_right ψ.1.1 (g * finGL E a (locGL E a w h))]
  by_cases h0 : φ = 0
  · subst h0
    have hz : ∀ y, whit ((0 : π.V) : Sm E a).1 y = 0 := fun y => by
      have e := whit_smul 0 (fun _ : GA E a => (0 : ℂ)) y
      rw [zero_mul] at e
      exact (congrArg (fun F => whit F y) (funext fun _ => (zero_mul _).symm)).trans e
    rw [hz, hz, mul_zero]
  have hsat := hα.2 φ hφ h0
  have hmain := GlobalTheory.T.shintani_formula_alt E w a (psiLocChar w) hψ (f φ) α ?_ ?_ ?_ ϖ hϖ l
  · change whit φ.1.1 (g * finGL E a (locGL E a w (diagPow ϖ l))) = _ * whit φ.1.1 (g * finGL E a (locGL E a w 1))
      at hmain
    rwa [map_one, map_one, mul_one] at hmain
  · intro u hu h
    change whit φ.1.1 (g * finGL E a (locGL E a w (u * h))) =
      psiLoc w (GlobalTheory.Whittaker.superDiag u) * whit φ.1.1 (g * finGL E a (locGL E a w h))
    rw [map_mul, map_mul, ← mul_assoc, commute_finGL_locGL w hg u, mul_assoc, finGL_locGL_eq_uGL w hu, whit,
      whittaker_uGL_mul (hcont φ) hleft, supSum_sLoc]
    rfl
  · intro h k hk
    change whit φ.1.1 (g * finGL E a (locGL E a w (h * k))) = whit φ.1.1 (g * finGL E a (locGL E a w h))
    rw [map_mul, map_mul, ← mul_assoc, whit_mul_right]
    congr 1
    funext z
    exact congrArg (fun ψ : π.V => ψ.1.1 z) (GlobalTheory.LGrp.mem_fixed.1 hφ k hk)
  · intro ϖ' hϖ' j hj
    rw [← map_heckeVec (Final.GLintComm E w a) (Tj_mem_hecke hϖ' j) f hf, hsat.2.2.2 ϖ' hϖ' j hj, map_smul]

end GlobalTheory.JSW

namespace GlobalTheory.JSW

theorem whit_mul_locGL_diagPow : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (w : HeightOneSpectrum (𝓞 E)) (α : Fin a → ℂˣ),
    (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) →
    HasSatGL w (π.locRep w) (Finset.univ.val.map α) → ∀ φ ∈ π.V, (∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ) →
    ∀ g : GA E a, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = 1 → ∀ (ϖ : (w.adicCompletion E)ˣ),
    IsUnifV E w (ϖ : w.adicCompletion E) → ∀ l : Fin a → ℕ,
    GlobalTheory.JSW.whit φ.1 (g * finGL E a (locGL E a w (GlobalTheory.JSW.diagPow ϖ l))) =
      GlobalTheory.JSW.sphW (qV E w) (fun i => (α i : ℂ)) l * GlobalTheory.JSW.whit φ.1 g := by
  intro E _ _ _ a π w α hψ hα φ hφV hφ g hg ϖ hϖ l
  exact whit_mul_locGL_diagPow_of_fixed π w hψ α hα ⟨φ, hφV⟩
    (GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (hφ k hk)) g hg ϖ hϖ l

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerBumpArchimedeanFactorContDiffOnInvertib
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump Metric Set
open scoped ContDiff

namespace GlobalTheory.WhitBump

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem contDiff_nu_apply (i k : Fin n) : ContDiff ℝ ∞ fun t : Vp E n => nu t i k := by
  by_cases h : i < k
  · have e : (fun t : Vp E n => nu t i k) = fun t => t ⟨(i, k), h⟩ := funext fun t => by simp [nu, h]
    rw [e]; exact contDiff_apply ℝ _ _
  · have e : (fun t : Vp E n => nu t i k) = fun _ => (if i = k then 1 else 0 : Cinf E) :=
      funext fun t => by simp [nu, h]
    rw [e]; exact contDiff_const

theorem contDiff_nu_mul : ContDiff ℝ ∞ fun q : Lie E n × Vp E n => toL (nu (-q.2) * Matrix.of q.1) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  show ContDiff ℝ ∞ fun q : Lie E n × Vp E n => ∑ k, nu (-q.2) i k * q.1 k j
  refine ContDiff.sum fun k _ => ?_
  exact ((contDiff_nu_apply i k).comp contDiff_snd.neg).mul
    ((contDiff_apply ℝ _ j).comp ((contDiff_apply ℝ _ k).comp contDiff_fst))

variable [_root_.NumberField.IsTotallyComplex E]

theorem continuous_psiInf_sdM : Continuous fun t : Vp E n => psiInf (-sdM (nu t)) := by
  have hs : Continuous (sInf E) :=
    ((continuous_infEq E).prodMk continuous_const : Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  have hd : Continuous fun t : Vp E n => sdM (nu t) :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => (contDiff_nu_apply i j).continuous
  exact continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (hs.comp hd.neg))

theorem bumpInf_contDiffOn_invSet : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (f : Lie E n → ℝ),
    ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ invSet E n → ContDiffOn ℝ ∞ (bumpInf f) (invSet E n) := by
  open scoped Pointwise in
  intro E _ _ _ n f hf hcs hts
  intro x₀ hx₀
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_invSet x₀ hx₀
  set r := ε / 2 with hr
  have hr0 : 0 < r := by positivity
  have hB : closedBall x₀ r ⊆ invSet E n := (closedBall_subset_ball (by linarith)).trans hball

  let Φ : Lie E n × Lie E n → Vp E n := fun q p => (Matrix.of q.1 * Matrix.of (ConstTermSmooth.invM q.2)) p.1.1 p.1.2
  have hΦ : ContinuousOn Φ (tsupport f ×ˢ closedBall x₀ r) := by
    have hinv : ContinuousOn (fun q : Lie E n × Lie E n => ConstTermSmooth.invM q.2) (tsupport f ×ˢ closedBall x₀ r) :=
      ConstTermSmooth.contDiffOn_invM.continuousOn.comp continuous_snd.continuousOn fun q hq => hB hq.2
    refine continuousOn_pi.2 fun p => ?_
    show ContinuousOn (fun q : Lie E n × Lie E n => ∑ k, q.1 p.1.1 k * ConstTermSmooth.invM q.2 k p.1.2) _
    refine continuousOn_finsetSum _ fun k _ => ?_
    have h1 : Continuous fun q : Lie E n × Lie E n => q.1 p.1.1 k :=
      (continuous_apply k).comp ((continuous_apply p.1.1).comp continuous_fst)
    have h2 : ContinuousOn (fun q : Lie E n × Lie E n => ConstTermSmooth.invM q.2 k p.1.2) (tsupport f ×ˢ closedBall x₀ r) :=
      (((continuous_apply p.1.2).comp (continuous_apply k) : Continuous fun m : Lie E n => m k p.1.2)).comp_continuousOn hinv
    exact h1.continuousOn.mul h2
  set K := Φ '' (tsupport f ×ˢ closedBall x₀ r) with hK
  have hKc : IsCompact K := (hcs.isCompact.prod (isCompact_closedBall _ _)).image_of_continuousOn hΦ

  let g : Lie E n → Vp E n → ℂ := fun x y => (f (toL (nu (-y) * Matrix.of x)) : ℂ)
  have hgs : ∀ p, ∀ y, p ∈ ball x₀ r → y ∉ -K → g p y = 0 := by
    intro p y hp hy
    by_contra hne
    have h : f (toL (nu (-y) * Matrix.of p)) ≠ 0 := fun h => hne (by simp [g, h])
    refine hy (Set.mem_neg.2 ⟨(toL (nu (-y) * Matrix.of p), p), ⟨subset_tsupport _ h, ball_subset_closedBall hp⟩, ?_⟩)
    have hu : IsUnit (Matrix.of p).det := (Matrix.isUnit_iff_isUnit_det _).1 (hB (ball_subset_closedBall hp))
    funext q
    have e : Matrix.of (toL (nu (-y) * Matrix.of p)) * Matrix.of (ConstTermSmooth.invM p) = nu (-y) :=
      Matrix.mul_nonsing_inv_cancel_right _ _ hu
    show (Matrix.of (toL (nu (-y) * Matrix.of p)) * Matrix.of (ConstTermSmooth.invM p)) q.1.1 q.1.2 = _
    rw [e]
    simp [nu, q.2]
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (↿g) (ball x₀ r ×ˢ univ) :=
    (Complex.ofRealCLM.contDiff.comp (hf.comp contDiff_nu_mul)).contDiffOn
  have hF : LocallyIntegrable (fun t : Vp E n => psiInf (-sdM (nu t))) volume :=
    continuous_psiInf_sdM.locallyIntegrable
  have hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : Lie E n => (0 : Vp E n)) (ball x₀ r) := contDiffOn_const
  have main := contDiffOn_convolution_right_with_param_comp (μ := volume)
    (ContinuousLinearMap.mul ℝ ℂ) hv isOpen_ball hKc.neg hgs hF hg
  have fin : ContDiffOn ℝ ∞ (bumpInf f) (ball x₀ r) := by
    refine main.congr fun x _ => ?_
    simp only [bumpInf, convolution_def, ContinuousLinearMap.mul_apply', zero_sub, neg_neg, g]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => mul_comm _ _)
  exact fin.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hr0))

end GlobalTheory.WhitBump
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZpowMemOfValOne
section
noncomputable section

namespace GlobalTheory.DoubleCosetDivisors

open Matrix

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem zpow_mem_of_val_one {O : Subring L}
    (hO : ∀ x : L, (Valued.v : L → WithZero (Multiplicative ℤ)) x ≤ 1 → x ∈ O)
    {u : L} (hu : (Valued.v : L → WithZero (Multiplicative ℤ)) u = 1) (k : ℤ) : u ^ k ∈ O := by
  apply hO
  rw [map_zpow₀, hu, _root_.one_zpow]

theorem diag_mem {n : ℕ} {O : Subring L}
    (hO : ∀ x : L, (Valued.v : L → WithZero (Multiplicative ℤ)) x ≤ 1 → x ∈ O)
    {u : L} (hu : (Valued.v : L → WithZero (Multiplicative ℤ)) u = 1) (e : Fin n → ℤ) :
    ∃ U ∈ Formalism.UG.GLint (Fin n) O, (U : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => u ^ e i) := by
  have hu0 : u ≠ 0 := by
    intro h; rw [h, map_zero] at hu; exact zero_ne_one hu
  let Uo : GL (Fin n) O :=
    { val := Matrix.diagonal (fun i => ⟨u ^ e i, zpow_mem_of_val_one hO hu (e i)⟩)
      inv := Matrix.diagonal (fun i => ⟨u ^ (-e i), zpow_mem_of_val_one hO hu (-e i)⟩)
      val_inv := by
        rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1; funext i; apply Subtype.ext
        simp [mul_inv_cancel₀ (zpow_ne_zero _ hu0)]
      inv_val := by
        rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1; funext i; apply Subtype.ext
        simp [inv_mul_cancel₀ (zpow_ne_zero _ hu0)] }
  refine ⟨Formalism.UG.bc (n := Fin n) O.subtype Uo, ⟨Uo, rfl⟩, ?_⟩
  ext i j
  simp [Formalism.UG.bc, Uo, Matrix.diagonal_apply]

theorem sameDiv_doubleCoset {n : ℕ} {O : Subring L}
    (hO : ∀ x : L, (Valued.v : L → WithZero (Multiplicative ℤ)) x ≤ 1 → x ∈ O) {d : List ℤ} {g s : GL (Fin n) L}
    (hg : GlobalTheory.SphPar.HasDiv O d g) (hs : GlobalTheory.SphPar.HasDiv O d s) :
    ∃ (a : ↥(Formalism.UG.GLint (Fin n) O)) (b : ↥(Formalism.UG.GLint (Fin n) O)),
      g = (↑a : GL (Fin n) L) * s * (↑b : GL (Fin n) L) := by
  obtain ⟨ϖ, hϖ, a1, ha1, b1, hb1, hg⟩ := hg
  obtain ⟨ϖ', hϖ', a2, ha2, b2, hb2, hs⟩ := hs
  have hne : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≠ 0 :=
    WithZero.coe_ne_zero
  have h0' : ϖ' ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ'; exact hne hϖ'.symm
  have hu : (Valued.v : L → WithZero (Multiplicative ℤ)) (ϖ / ϖ') = 1 := by
    rw [map_div₀, hϖ, hϖ', div_self hne]
  obtain ⟨U, hU, hUe⟩ := diag_mem hO hu (fun i : Fin n => d.getD i 0)
  have hD : Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i 0) =
      (U : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun i : Fin n => ϖ' ^ d.getD i 0) := by
    rw [hUe, Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    rw [← mul_zpow, div_mul_cancel₀ _ h0']
  refine ⟨⟨a1 * U * a2⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ ha1 hU) (Subgroup.inv_mem _ ha2)⟩,
    ⟨b2⁻¹ * b1, Subgroup.mul_mem _ (Subgroup.inv_mem _ hb2) hb1⟩, ?_⟩
  apply Units.ext
  have e1 : ((a2⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (a2 : Matrix (Fin n) (Fin n) L) = 1 := Units.inv_mul a2
  have e2 : (b2 : Matrix (Fin n) (Fin n) L) * ((b2⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := Units.mul_inv b2
  simp only [Units.val_mul]
  rw [hg, hs, hD]
  calc (a1 : Matrix (Fin n) (Fin n) L) * ((U : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun i : Fin n => ϖ' ^ d.getD i 0)) * (b1 : Matrix (Fin n) (Fin n) L)
      = (a1 : Matrix (Fin n) (Fin n) L) * (U : Matrix (Fin n) (Fin n) L) * (((a2⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (a2 : Matrix (Fin n) (Fin n) L))
          * Matrix.diagonal (fun i : Fin n => ϖ' ^ d.getD i 0) * ((b2 : Matrix (Fin n) (Fin n) L) * ((b2⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) * (b1 : Matrix (Fin n) (Fin n) L) := by
        rw [e1, e2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem main : ∀ {L : Type} [inst : Field L] [inst_1 : Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {O : Subring L}, (∀ (x : L), (Valued.v : L → WithZero (Multiplicative ℤ)) x ≤ (1 : WithZero (Multiplicative ℤ)) → x ∈ O) → ∀ {d : List ℤ} {g s : GL (Fin n) L}, GlobalTheory.SphPar.HasDiv O d g → GlobalTheory.SphPar.HasDiv O d s → ∃ (a : ↥(Formalism.UG.GLint (Fin n) O)) (b : ↥(Formalism.UG.GLint (Fin n) O)), g = (↑a : GL (Fin n) L) * s * (↑b : GL (Fin n) L) :=
  fun hO _ _ _ hg hs => sameDiv_doubleCoset hO hg hs

end GlobalTheory.DoubleCosetDivisors
end
end

