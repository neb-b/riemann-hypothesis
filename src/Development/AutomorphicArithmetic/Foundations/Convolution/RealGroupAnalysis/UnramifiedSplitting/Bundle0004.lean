module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.ConjStep
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.H.conjStep :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (f : GL (Fin 2) (A F) → ℂ) (φ : S4 F) (α : (A E)ˣ),
      Measurable (w1 W f φ (aE α)) → (∀ b g, w1 W f φ (aE α) (nU b * g) = w1 W f φ (aE α) g) → Integrable (iw (w1 W f φ (aE α))) M.ν →
      W1 W M f φ (aE α) = ((ab (ideleNorm F E α) : ℝ) : ℂ) * M.I0 fun g => Wf f (dM (ideleNorm F E α) * gl g) *
        hat (W.Om g φ).1 ![0, ((ideleNorm F E α : (A F)ˣ) : A F), D.co ((α⁻¹ : (A E)ˣ) : A E) 0, D.co ((α⁻¹ : (A E)ˣ) : A E) 1] := by
  intro F E _ _ _ _ _ _ _ D W M f φ α h1 h2 h3
  have hn : nu F (aE α) = ideleNorm F E α := by
    unfold nu
    congr 1
    exact Units.ext (by simp [aE, Matrix.det_fin_two])
  have h4 := ((UpperTheory.ConvolutionTheory.R2.inv F M _ h1 h2 h3).2 (ideleNorm F E α)).2
  have hab : ((ab (ideleNorm F E α) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (IdeleGroup.ideleModule F (ideleNorm F E α)).2.ne'
  have h5 : (fun g => w1 W f φ (aE α) (cD (ideleNorm F E α) g)) = fun g => Wf f (dM (ideleNorm F E α) * gl g) *
      hat (W.Om g φ).1 ![0, ((ideleNorm F E α : (A F)ˣ) : A F), D.co ((α⁻¹ : (A E)ˣ) : A E) 0, D.co ((α⁻¹ : (A E)ˣ) : A E) 1] := by
    funext g
    have e1 : gl (cD (ideleNorm F E α) g) * dM (ideleNorm F E α) = dM (ideleNorm F E α) * gl g := by
      generalize ideleNorm F E α = t
      refine Units.ext ?_
      show (cD t g).1 * (dM t).val = (dM t).val * g.1
      ext i j : 2
      fin_cases i <;> fin_cases j <;> simp [cD, dM, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
    have e2 : W.Om (cD (ideleNorm F E α) g) (W.L (aE α) φ) = W.L (aE α) (W.Om g φ) := by
      have := LinearMap.congr_fun (W.comm (aE α) g) φ
      rw [hn] at this
      exact this.symm
    have e3 : D.mkE 1 0 = 1 := by simp [Dat.mkE]
    rw [w1, hn, e1, e2, (UpperTheory.ConvolutionTheory.R2.hatSt F E D W).aE, e3, mul_one, mul_one]
  rw [← h5, h4, Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hab, one_mul]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.ContMkE
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.R2.H.WhittakerCoefficientEigen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private abbrev Bx (F : Type) [Field F] [NumberField F] : Set (Fin 2 → A F) := Set.univ.pi fun _ => fundamentalSet F

private theorem vn (q : A E) : (nU q).val = !![1, q; 0, 1] := rfl

private theorem n_add (x y : A E) : gl (nU (x + y)) = gl (nU x) * gl (nU y) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem n_zero : gl (nU (0 : A E)) = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn]

private theorem cont_n : Continuous fun q : A E => gl (nU q) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop
  · have e : ∀ q : A E, (gl (nU q))⁻¹ = gl (nU (-q)) := fun q =>
      inv_eq_of_mul_eq_one_right (by rw [← n_add, add_neg_cancel, n_zero])
    simp only [e]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop

private theorem rat_n (k : E) : ∃ γ : GL (Fin 2) E, ratGL E 2 γ = gl (nU (rt k)) := by
  refine ⟨Matrix.SpecialLinearGroup.toGL ⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two]⟩, Units.ext ?_⟩
  ext i j
  change algebraMap E (A E) (!![1, k; 0, 1] i j) = _
  fin_cases i <;> fin_cases j <;> simp [vn]

private theorem ψ_add (x y : A F) : ψ (x + y) = ψ x * ψ y := by simp [ψ, AddChar.map_add_eq_mul]

private theorem ψ_rt (k : F) : ψ (rt k) = 1 := by simp [ψ, adelicChar_algebraMap]

private theorem ψ_neg_mul (x : A F) : ψ (-x) * ψ x = 1 := by
  rw [← ψ_add, neg_add_cancel]
  simpa using ψ_rt (0 : F)

private theorem cont_ψ : Continuous (ψ (F := F)) := continuous_subtype_val.comp continuous_adelicChar

private theorem mkE_add (D : Dat F E) (a b c d : A F) : D.mkE (a + c) (b + d) = D.mkE a b + D.mkE c d := by
  simp only [Dat.mkE, map_add (f := _), add_mul]
  abel

private theorem mkE_rat (D : Dat F E) (x y : F) :
    D.mkE (rt x) (rt y) = rt (algebraMap F E x + algebraMap F E y * D.θ) := by
  simp only [Dat.mkE, rt, AdeleBaseChange.adeleMap_algebraMap, map_add (f := _), map_mul]

private theorem cont_mkE (D : Dat F E) : Continuous fun x : Fin 2 → A F => D.mkE (x 0) (x 1) :=
  (AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 0)).add
    ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 1)).mul continuous_const)

private def Jw (D : Dat F E) (Φ : GL (Fin 2) (A E) → ℂ) (h : GL (Fin 2) (A E)) (x : Fin 2 → A F) : ℂ :=
  Φ (gl (nU (D.mkE (x 0) (x 1))) * h) * ψ (2 * x 0)

private theorem cont_J (D : Dat F E) {Φ : GL (Fin 2) (A E) → ℂ} (hΦ : Continuous Φ) (h : GL (Fin 2) (A E)) :
    Continuous (Jw D Φ h) :=
  (hΦ.comp ((cont_n.comp (cont_mkE D)).mul continuous_const)).mul
    (cont_ψ.comp (continuous_const.mul (continuous_apply 0)))

private theorem int_J (D : Dat F E) {Φ : GL (Fin 2) (A E) → ℂ} (hΦ : Continuous Φ) (h : GL (Fin 2) (A E)) :
    IntegrableOn (Jw D Φ h) (Bx F) (adeleMeasurePi F) := by
  obtain ⟨B, hB, hEB⟩ : ∃ B, IsCompact B ∧ fundamentalSet F ⊆ B :=
    ⟨closure (fundamentalSetInfinite F) ×ˢ _,
      (isCompact_closure_fundamentalSetInfinite F).prod (isCompact_integralFiniteAdeles F),
      fun x hx => ⟨subset_closure hx.1, hx.2⟩⟩
  have hC : IsCompact (Set.univ.pi fun _ : Fin 2 => B) := isCompact_univ_pi fun _ => hB
  exact ((cont_J D hΦ h).continuousOn.integrableOn_compact hC).mono_set
    fun x hx i hi => hEB (hx i hi)

private theorem per_J (D : Dat F E) {Φ : GL (Fin 2) (A E) → ℂ} (hL : ∀ γ g, Φ (ratGL E 2 γ * g) = Φ g)
    (h : GL (Fin 2) (A E)) (η : Fin 2 → F) (x : Fin 2 → A F) :
    Jw D Φ h ((fun i => algebraMap F (A F) (η i)) + x) = Jw D Φ h x := by
  obtain ⟨γ, hγ⟩ := rat_n (algebraMap F E (η 0) + algebraMap F E (η 1) * D.θ)
  have e : (2 : A F) * (algebraMap F (A F) (η 0) + x 0) = rt (2 * η 0) + 2 * x 0 := by
    simp only [rt, map_mul, map_ofNat, mul_add]
  simp only [Jw, Pi.add_apply]
  rw [mkE_add, n_add, e, ψ_add, ψ_rt, one_mul]
  change Φ (gl (nU (D.mkE (rt (η 0)) (rt (η 1)))) * gl (nU (D.mkE (x 0) (x 1))) * h) * _ = _
  rw [mkE_rat, ← hγ, mul_assoc, hL]

private theorem shift_J (D : Dat F E) {Φ : GL (Fin 2) (A E) → ℂ} (hL : ∀ γ g, Φ (ratGL E 2 γ * g) = Φ g)
    (h : GL (Fin 2) (A E)) (a : Fin 2 → A F) :
    ∫ x in Bx F, Jw D Φ h (x + a) ∂(adeleMeasurePi F) = ∫ x in Bx F, Jw D Φ h x ∂(adeleMeasurePi F) :=
  GroundTheory.Automorphic.FourierWhittaker.setIntegral_comp_add a fun ξ hξ x => by
    obtain ⟨η, rfl⟩ := GroundTheory.Automorphic.FourierWhittaker.mem_vecLattice.1 hξ
    exact per_J D hL h η x

private theorem sum_Tj {n : ℕ} {w : HeightOneSpectrum (𝓞 E)} {ϖ : w.adicCompletion E} (hϖ : Formalism.UG.IsUnifV E w ϖ) (j : ℕ) :
    ∃ s : Finset (GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n)),
      ∀ G : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n) → ℂ,
        ∑ᶠ c, Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j c.out * G c =
          ∑ c ∈ s, Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j c.out * G c := by
  have hf := Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm E w n) (GlobalTheory.LFun.Tj_mem_hecke (n := n) hϖ j).2
  refine ⟨hf.toFinset, fun G => finsum_eq_sum_of_support_subset _ fun c hc => ?_⟩
  rw [Set.Finite.coe_toFinset]
  exact left_ne_zero_of_mul hc

private theorem eig_int {n : ℕ} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} {X : Type} [MeasurableSpace X]
    (μ : Measure X) (hB : B.card = n) (G : X → GL (Fin n) (w.adicCompletion E) → ℂ) (a : X → ℂ)
    (h : ∀ x, Eig w B (G x)) (hi : ∀ y, Integrable (fun x => G x y * a x) μ) :
    Eig w B (fun y => ∫ x, G x y * a x ∂μ) := by
  refine ⟨hB, fun g k hk => by simp only [fun x => (h x).inv g k hk], fun ϖ hϖ j hj g => ?_⟩
  obtain ⟨s, hs⟩ := sum_Tj (n := n) hϖ j
  rw [hs]
  simp only [← integral_const_mul]
  rw [← integral_finsetSum _ fun c _ => (hi _).const_mul _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have e := (h x).eig ϖ hϖ j hj g
  rw [hs] at e
  simp only [← mul_assoc, ← e, Finset.sum_mul]

end UpperTheory.ConvolutionTheory.R2.H.WhittakerCoefficientEigen

end

open UpperTheory.ConvolutionTheory.R2.H.WhittakerCoefficientEigen in
theorem UpperTheory.ConvolutionTheory.R2.H.weEig :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (Φ : GL (Fin 2) (A E) → ℂ), Continuous Φ →
      ((∀ γ g, Φ (ratGL E 2 γ * g) = Φ g) → ∀ u t h, WE D Φ (gl (nU (D.mkE u t)) * h) = ψ (-(2 * u)) * WE D Φ h) ∧
      (∀ w B, EigAt w B Φ → EigAt w B (WE D Φ)) ∧
      ∀ (Φ' : GL (Fin 2) (A E) → ℂ) (c : ℂ), Continuous Φ' → ∀ h, WE D (Φ + c • Φ') h = WE D Φ h + c * WE D Φ' h := by
  intro F E _ _ _ _ _ D Φ hΦ
  have eW : ∀ (Ψ : GL (Fin 2) (A E) → ℂ) h, WE D Ψ h = ∫ x in Bx F, Jw D Ψ h x ∂(adeleMeasurePi F) := fun _ _ => rfl
  refine ⟨fun hL u t h => ?_, fun w B hB g => ?_, fun Φ' c hΦ' h => ?_⟩
  · rw [eW, eW, ← shift_J D hL h ![u, t], ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have e : (2 : A F) * (x 0 + u) = 2 * x 0 + 2 * u := mul_add _ _ _
    simp only [Jw, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mkE_add, n_add, e, ψ_add, mul_assoc (gl _)]
    linear_combination (-(Φ (gl (nU (D.mkE (x 0) (x 1))) * (gl (nU (D.mkE u t)) * h))) * ψ (2 * x 0)) * ψ_neg_mul (2 * u)
  · refine eig_int ((adeleMeasurePi F).restrict (Bx F)) (hB 1).card
      (fun x y => Φ (gl (nU (D.mkE (x 0) (x 1))) * (g * finGL E 2 (locGL E 2 w y)))) (fun x => ψ (2 * x 0))
      (fun x => ?_) fun y => int_J D hΦ _
    simpa only [mul_assoc] using hB (gl (nU (D.mkE (x 0) (x 1))) * g)
  · rw [eW, eW, eW, ← integral_const_mul, ← integral_add (int_J D hΦ h) ((int_J D hΦ' h).const_mul c)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Jw, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.FixTr
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.H.fixTr :
    ∀ (K : Type) [Field K] [NumberField K] (v : P K) (f : GL (Fin 2) (A K) → ℂ) (d : GL (Fin 2) (A K)), KAt v d →
      (Fix v f → Fix v fun g => f (g * d)) ∧ ∀ B, EigAt v B f → EigAt v B fun g => f (g * d) := by
  intro K _ _ v f d hd
  have hl := (lcLaws K v).2.2.2.2.2.2 d
  set x := Matrix.GeneralLinearGroup.map (cp v) d with hx
  have hd' : x ∈ GlobalTheory.LFun.KGL v (n := 2) := hd
  refine ⟨fun hf g k hk => ?_, fun B hB g => ?_⟩
  · show f (g * lc v k * d) = f (g * d)
    rw [mul_assoc, hl, ← mul_assoc, hf _ _ (mul_mem (mul_mem (inv_mem hd') hk) hd')]
  · have h := hB (g * d * lc v x⁻¹)
    convert h using 2 with y
    have h1 := h.inv y x hd'
    show f (g * lc v y * d) = f (g * d * lc v x⁻¹ * lc v y)
    change f (g * d * lc v x⁻¹ * lc v (y * x)) = f (g * d * lc v x⁻¹ * lc v y) at h1
    rw [← h1, mul_assoc g, hl, mul_assoc x⁻¹, map_mul]
    simp only [mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.JExExists
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

private theorem sg_zero' {K : Type} [Field K] [NumberField K] (v : P K) : sg v 0 = 0 := by
  have h := (sgLaws K v).1 0 0
  simpa using h

private theorem sg_mul' {K : Type} [Field K] [NumberField K] (v : P K) (x y : Kv v) :
    sg v x * sg v y = sg v (x * y) := by
  have h := (sgLaws K v).2.1 (sg v x) y
  rw [(sgLaws K v).2.2.1] at h
  exact h

private theorem lc_entry {K : Type} [Field K] [NumberField K] (v : P K)
    (x : Matrix.SpecialLinearGroup (Fin 2) (Kv v)) (i k : Fin 2) :
    (lc v (Matrix.SpecialLinearGroup.toGL x)).val i k =
      (1 : Matrix (Fin 2) (Fin 2) (A K)) i k + sg v (x i k - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) i k) :=
  (sgLaws K v).2.2.2.2.1 _ i k

private theorem lc_det {K : Type} [Field K] [NumberField K] (v : P K)
    (x : Matrix.SpecialLinearGroup (Fin 2) (Kv v)) :
    ((lc v (Matrix.SpecialLinearGroup.toGL x)).val).det = 1 := by
  have hadd := (sgLaws K v).1
  have hd := x.det_coe
  rw [Matrix.det_fin_two] at hd
  rw [Matrix.det_fin_two]
  simp only [lc_entry]
  simp only [Matrix.one_apply_eq, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true, Matrix.one_apply_ne, zero_add, sub_zero]
  have e : ∀ a b : Kv v, sg v (a - b) = sg v a - sg v b := fun a b => by
    have := hadd (a - b) b
    rw [sub_add_cancel] at this
    rw [this]; ring
  have key : sg v (x 0 0 - 1) + sg v (x 1 1 - 1) + sg v (x 0 0 - 1) * sg v (x 1 1 - 1) - sg v (x 0 1) * sg v (x 1 0) = 0 := by
    simp only [sg_mul', ← hadd, ← e]
    have : x 0 0 - 1 + (x 1 1 - 1) + (x 0 0 - 1) * (x 1 1 - 1) - x 0 1 * x 1 0 = 0 := by
      have hd' : x 0 0 * x 1 1 - x 0 1 * x 1 0 = 1 := hd
      linear_combination hd'
    rw [this, sg_zero']
  linear_combination key

private theorem jEx_exists {K : Type} [Field K] [NumberField K] (v : P K) : ∃ j, IsJ v j := by
  refine ⟨{ toFun := fun x => ⟨(lc v (Matrix.SpecialLinearGroup.toGL x)).val, lc_det v x⟩, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · apply Subtype.ext
    simp
  · intro x y
    apply Subtype.ext
    simp
    rfl
  · intro x
    apply Units.ext
    rfl

theorem UpperTheory.ConvolutionTheory.R2.H.jEx :
    ∀ (K : Type) [Field K] [NumberField K] (v : P K), (∃ j, IsJ v j) ∧ ∀ j, IsJ v j → Continuous j ∧ (∀ x, At v (j x)) ∧ (∀ x, (∀ i k, IsInt (x i k)) → IntAt v (j x)) ∧
      (∀ x i k, (j x) i k = (1 : Matrix (Fin 2) (Fin 2) (A K)) i k + sg v (x i k - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) i k)) := by
  intro K _ _ v
  refine ⟨jEx_exists v, fun j hj => ?_⟩
  have hent : ∀ x i k, (j x) i k = (1 : Matrix (Fin 2) (Fin 2) (A K)) i k + sg v (x i k - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) i k) := by
    intro x i k
    have h := congrArg (fun g : GL (Fin 2) (A K) => g.val i k) (hj x)
    exact h.trans (lc_entry v x i k)
  have hsg := (sgLaws K v).2.2.2.2.2.2.2.1
  have hcsg := (sgLaws K v).2.2.2.2.2.2.2.2.2
  refine ⟨?_, ?_, ?_, hent⟩
  · have hv : Continuous fun x : Matrix.SpecialLinearGroup (Fin 2) (Kv v) => (j x).1 := by
      refine continuous_matrix fun i k => ?_
      have he : (fun x : Matrix.SpecialLinearGroup (Fin 2) (Kv v) => (j x).1 i k) = fun x =>
          (1 : Matrix (Fin 2) (Fin 2) (A K)) i k + sg v (x i k - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) i k) :=
        funext fun x => hent x i k
      rw [he]
      have hx : Continuous fun x : Matrix.SpecialLinearGroup (Fin 2) (Kv v) => x i k :=
        continuous_subtype_val.matrix_elem i k
      exact continuous_const.add (hcsg.comp (hx.sub continuous_const))
    exact Continuous.subtype_mk hv fun x => (j x).2
  · intro x
    refine ⟨fun i k => ?_, fun v' hv' i k => ?_⟩
    · rw [hent]
      show _ + (sg v _).1 = _
      rw [(hsg _).1, add_zero]
    · rw [hent]
      show _ + (sg v _).2 v' = _
      rw [(hsg _).2 v' hv', add_zero]
      rfl
  · intro x hx i k
    have : (j x i k).2 v = x i k := by
      have h1 : cp v (j x i k) = x i k := by
        rw [hent, map_add (f := _), (sgLaws K v).2.2.1]
        fin_cases i <;> fin_cases k <;> simp
      exact h1
    rw [this]
    exact hx i k
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.WfEig
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.H.wfEig :
    ∀ (K : Type) [Field K] [NumberField K] (f : GL (Fin 2) (A K) → ℂ), Continuous f → (∀ γ g, f (ratGL K 2 γ * g) = f g) →
      (∀ b g, Wf f (gl (nU b) * g) = ψ (-b) * Wf f g) ∧ ∀ v B, EigAt v B f → EigAt v B (Wf f) := by
  intro K _ _ f hc hl
  exact ⟨(UpperTheory.ConvolutionTheory.R2.Pp.wfBasic K f ⟨hc, hl⟩).2.1, UpperTheory.ConvolutionTheory.R2.Pp.wfEig K f ⟨hc, hl⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.WhTorus
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

private lemma dL_mul {K : Type} [Field K] [NumberField K] {v : P K} (a d a' d' : (Kv v)ˣ) :
    dL a d * dL a' d' = dL (a * a') (d * d') := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dL, Matrix.mul_apply, Fin.sum_univ_two]

private lemma dL_one {K : Type} [Field K] [NumberField K] {v : P K} : (dL (1 : (Kv v)ˣ) 1) = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dL]

private lemma dL_nL {K : Type} [Field K] [NumberField K] {v : P K} (a : (Kv v)ˣ) (b : Kv v) :
    dL a 1 * nL b = nL ((a : Kv v) * b) * dL a 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dL, nL, Matrix.mul_apply, Fin.sum_univ_two]

private lemma nL_mem {K : Type} [Field K] [NumberField K] {v : P K} {c : Kv v} (hc : IsInt c) :
    nL c ∈ GlobalTheory.LFun.KGL v (n := 2) := by
  have hc' : c ∈ v.adicCompletionIntegers K := hc
  have hn : -c ∈ v.adicCompletionIntegers K := neg_mem hc'
  rw [GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff]
  have h1 : (1 : Kv v) ∈ Formalism.UG.Ov K v := one_mem _
  have h0 : (0 : Kv v) ∈ Formalism.UG.Ov K v := zero_mem _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j
    · exact h1
    · exact hc'
    · exact h0
    · exact h1
  · fin_cases i <;> fin_cases j
    · exact h1
    · exact hn
    · exact h0
    · exact h1

private lemma not_int_inv {K : Type} [Field K] [NumberField K] {v : P K} {ϖ : (Kv v)ˣ} (hϖ : IsU ϖ) :
    ¬ IsInt ((ϖ⁻¹ : (Kv v)ˣ) : Kv v) := by
  intro h
  have hu : Valued.v (ϖ : Kv v) < 1 := by
    have h' : Valued.v (ϖ : Kv v) = _ := hϖ
    rw [h']
    exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) < 1)
  have hm : Valued.v (ϖ : Kv v) * Valued.v ((ϖ⁻¹ : (Kv v)ˣ) : Kv v) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hle : Valued.v (ϖ : Kv v) * Valued.v ((ϖ⁻¹ : (Kv v)ˣ) : Kv v) ≤ Valued.v (ϖ : Kv v) * 1 :=
    mul_le_mul_right h _
  rw [hm, mul_one] at hle
  exact absurd hu (not_lt.2 hle)

private lemma W_zero {K : Type} [Field K] [NumberField K] {v : P K} {ϖ : (Kv v)ˣ} (hϖ : IsU ϖ)
    {χ : Kv v → ℂ} (hχ : Good χ) {B : Multiset ℂˣ} {W : GL (Fin 2) (Kv v) → ℂ} (hW : Eig v B W)
    (hn : ∀ b y, W (nL b * y) = χ b * W y) : W (dL ϖ⁻¹ 1) = 0 := by
  by_contra h
  refine not_int_inv hϖ (hχ.2.2 _ fun c hc => ?_)
  have e1 := hW.inv (dL ϖ⁻¹ 1) _ (nL_mem hc)
  rw [dL_nL, hn] at e1
  have e2 : χ (((ϖ⁻¹ : (Kv v)ˣ) : Kv v) * c) = 1 := mul_right_cancel₀ h (by rw [e1, one_mul])
  rwa [mul_comm] at e2

theorem UpperTheory.ConvolutionTheory.R2.H.whTorus :
    ∀ (K : Type) [Field K] [NumberField K] (v : P K) (ϖ : (Kv v)ˣ), IsU ϖ → ∀ (χ : Kv v → ℂ), Good χ → ∀ (α β : ℂˣ) (W : GL (Fin 2) (Kv v) → ℂ), Eig v {α, β} W →
      (∀ b y, W (nL b * y) = χ b * W y) →
      q v * W (dL ϖ 1) = q v ^ (1 / 2 : ℂ) * ((α : ℂ) + β) * W 1 ∧
        (α : ℂ) * β * q v * W (dL ϖ ϖ⁻¹) = ((α : ℂ) ^ 2 + α * β + (β : ℂ) ^ 2) * W 1 := by
  intro K _ _ v ϖ hϖ χ hχ α β W hW hn
  obtain ⟨R, hcard, hRint, hR⟩ := UpperTheory.ConvolutionTheory.R2.H.heckeExpl K v ϖ hϖ
  have hsum := fun g => (hR α β W hW g).1
  have hcen := fun g => (hR α β W hW g).2
  have hz := W_zero hϖ hχ hW hn
  have hint : ∀ c : Kv v, IsInt c → ∀ y, W (nL c * y) = W y := fun c hc y => by
    rw [hn, hχ.2.1 c hc, one_mul]
  have hϖint : IsInt (ϖ : Kv v) := by
    have h' : Valued.v (ϖ : Kv v) = _ := hϖ
    show Valued.v (ϖ : Kv v) ≤ 1
    rw [h']
    exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) ≤ 1)
  have hq0 : q v ≠ 0 := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    exact Nat.cast_ne_zero.2 this
  set s : ℂ := q v ^ (1 / 2 : ℂ) with hs
  have hss : s * s = q v := by
    rw [hs, ← Complex.cpow_add _ _ hq0]
    norm_num
  have hs0 : s ≠ 0 := fun h => hq0 (by rw [← hss, h, zero_mul])
  have hconst : ∀ x : ℂ, ∑ _b ∈ R, x = q v * x := fun x => by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    rfl

  have h1 := hsum 1
  have t1 : ∀ b ∈ R, W (1 * nL b * dL ϖ 1) = W (dL ϖ 1) := fun b hb => by
    rw [one_mul, hint b (hRint b hb)]
  rw [Finset.sum_congr rfl t1, hconst, one_mul] at h1
  have t2 : W (dL 1 ϖ) = 0 := by
    have := hcen (dL ϖ⁻¹ 1)
    rw [dL_mul, inv_mul_cancel, one_mul, hz, mul_zero] at this
    exact this
  rw [t2, add_zero] at h1

  have h2 := hsum (dL ϖ 1)
  have t3 : ∀ b ∈ R, W (dL ϖ 1 * nL b * dL ϖ 1) = W (dL ϖ 1 * dL ϖ 1) := fun b hb => by
    rw [dL_nL, mul_assoc, hint _ ?_]
    have hb' : (ϖ : Kv v) * b ∈ v.adicCompletionIntegers K :=
      mul_mem (show (ϖ : Kv v) ∈ v.adicCompletionIntegers K from hϖint)
        (show b ∈ v.adicCompletionIntegers K from hRint b hb)
    exact hb'
  rw [Finset.sum_congr rfl t3, hconst] at h2
  have t4 : W (dL ϖ 1 * dL 1 ϖ) = (α : ℂ) * β * W 1 := by
    have := hcen 1
    rw [one_mul] at this
    rw [dL_mul, mul_one, one_mul]
    exact this
  have t5 : W (dL ϖ 1 * dL ϖ 1) = (α : ℂ) * β * W (dL ϖ ϖ⁻¹) := by
    have := hcen (dL ϖ ϖ⁻¹)
    rw [dL_mul, inv_mul_cancel] at this
    rw [dL_mul, mul_one]
    exact this
  rw [t4, t5] at h2
  refine ⟨h1.symm, ?_⟩
  have h3 : s * W (dL ϖ 1) = ((α : ℂ) + β) * W 1 := by
    refine mul_left_cancel₀ hs0 ?_
    rw [← mul_assoc, hss, ← mul_assoc]
    exact h1.symm
  linear_combination (-1 : ℂ) * h2 + ((α : ℂ) + β) * h3
end

