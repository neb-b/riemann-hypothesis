module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CoefPer
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical
open UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.coefPer :
    DecE → Maj → OrbS → MomKill → OrbFn → CoefPer := by
  intro _ _ _ momKill orbFn E _ _ _ D W M N P φ hφ h0 h
  haveI := N.haar
  obtain ⟨j, -, hj, -⟩ := reps E D
  obtain ⟨hp, hw, hi⟩ := yInt E D W M N P φ hφ
  have hδ : D.δ < 0 := by simpa using D.neg (Rat.castHom ℝ)
  haveI : SFinite (mY D.δ N) := by unfold mY; infer_instance
  have hU := perCont E D W M N P φ hφ
  set U : G1 E → ℂ := fun h : G1 E => UPer D M fun x => φ.1 (x * gl h) with hUd
  have key : ∀ c : G1 E → ℂ, Continuous c → HasCompactSupport c → ∫ y, c y * U y ∂N.μ = 0 := fun c hc hs => by
    obtain ⟨Ψ, hΨ, hΨ'⟩ := orbFn E D M j hj c hc hs
    obtain ⟨h1, h2⟩ := zAll E D W M N P φ hφ j hj c hc hs Ψ hΨ hΨ'
    rw [← h2]
    exact momKill D.δ hδ _ (mY D.δ N) (pY D) _ hp hw hi (fun ph hph => (yEq E D W M N P φ hφ ph hph).symm.trans (h0 ph hph)) Ψ hΨ h1
  by_contra hne
  obtain ⟨χ, h1, -, hs, h01⟩ := exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := h)) isClosed_empty
    (Set.disjoint_empty _)
  have h2 := key (fun y => (χ y : ℂ) * starRingEnd ℂ (U y))
    ((Complex.continuous_ofReal.comp χ.continuous).mul (Complex.continuous_conj.comp hU))
    ((hs.comp_left (g := Complex.ofReal) Complex.ofReal_zero).mul_right)
  have e : ∀ y, (χ y : ℂ) * starRingEnd ℂ (U y) * U y = ((χ y * ‖U y‖ ^ 2 : ℝ) : ℂ) := fun y => by
    rw [mul_assoc, Complex.conj_mul']
    push_cast
    rfl
  simp only [e, integral_complex_ofReal, Complex.ofReal_eq_zero] at h2
  refine (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := N.μ) (x := h) (χ.continuous.mul (hU.norm.pow 2))
    hs.mul_right (fun y => mul_nonneg (h01 y).1 (sq_nonneg ‖U y‖)) ?_).ne' h2
  have : χ h = 1 := h1 rfl
  change χ h * ‖U h‖ ^ 2 ≠ 0
  rw [this, one_mul]
  exact pow_ne_zero _ (norm_ne_zero_iff.2 hne)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThCont
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

private theorem om_L' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {D : Dat ℚ E} (W : Weil D)
    (g : G1 ℚ) (h : GL (Fin 2) (A E)) (hh : nu ℚ h = 1) (φ : S4 ℚ) :
    W.Om g (W.L h φ) = W.L h (W.Om g φ) := by
  have e := congrArg (fun T : Module.End ℂ (S4 ℚ) => T φ) (W.comm h g)
  simp only [Module.End.mul_apply, hh] at e
  rw [e, UpperTheory.ConvolutionTheory.R2.M.cD_one]

private theorem term_eq {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {D : Dat ℚ E} (W : Weil D)
    (g : G1 ℚ) (h : GL (Fin 2) (A E)) (hh : nu ℚ h = 1) (φ : S4 ℚ) (v : V4 ℚ) :
    (W.Om g (W.L h φ)).1 v = (W.Om g φ).1 (D.act h⁻¹ v) := by
  rw [om_L' W g h hh, W.L_apply, hh, ab_one]
  simp

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.thCont :
    ThCont := by
  intro E _ _ _ D W _ _ _ ph hph S p₀ hp₀
  obtain ⟨ρ, hρ, hact, -, -, -⟩ := actCont ℚ E D
  obtain ⟨n, hn⟩ := wtSum ℚ
  obtain ⟨S₁, hS₁, hm₁⟩ := exists_compact_mem_nhds p₀.1
  obtain ⟨S₂, hS₂, hm₂⟩ := exists_compact_mem_nhds p₀.2
  obtain ⟨K, hK, hb⟩ := lDom ℚ E D W (G1 ℚ) S₁ (fun g => W.Om g ph)
    (omCpt ℚ E D W ph hph S₁ hS₁) S₂ hS₂
  obtain ⟨B, hB⟩ := hb n
  obtain ⟨C, hC⟩ := hn K hK 1 one_pos
  obtain ⟨hs, -⟩ := hC 1 (by rw [ab_one])
  have e : (fun ξ : Fin 4 → ℚ => wt K n (sc (1 : (A ℚ)ˣ) ξ)) = fun ξ => wt K n (rp ξ) := by
    funext ξ
    congr 1
    funext i
    change ((1 : (A ℚ)ˣ) : A ℚ) * rt (ξ i) = rt (ξ i)
    rw [Units.val_one, one_mul]
  rw [e] at hs
  have key : ContinuousOn (fun p : G1 ℚ × GL (Fin 2) (A E) => ThOn S (W.Om p.1 (W.L p.2 ph)).1)
      ((S₁ ×ˢ S₂) ∩ {p | nu ℚ p.2 = 1}) := by
    unfold ThOn
    refine continuousOn_tsum (u := fun ξ : S => B * wt K n (rp ξ.1)) (fun ξ => ?_)
      ((hs.mul_left B).subtype (fun x => x ∈ S)) fun ξ p hp => ?_
    · have hc : Continuous fun p : G1 ℚ × GL (Fin 2) (A E) =>
          (W.Om p.1 ph).1 ((ρ p.2⁻¹).val *ᵥ rp ξ.1) :=
        (W.cont ph).comp (continuous_fst.prodMk
          ((Units.continuous_val.comp (hρ.comp (continuous_inv.comp continuous_snd))).matrix_mulVec
            continuous_const))
      refine hc.continuousOn.congr fun p hp => ?_
      rw [term_eq W p.1 p.2 hp.2, hact]
    · have hnorm := hB (p.2, p.1) ⟨hp.1.2, hp.1.1⟩ (rp ξ.1)
      have e' : (W.Om p.1 (W.L p.2 ph)).1 (rp ξ.1) = (W.L p.2 (W.Om p.1 ph)).1 (rp ξ.1) := by
        rw [om_L' W p.1 p.2 hp.2]
      rw [e']
      exact hnorm
  have hT : (S₁ ×ˢ S₂) ∩ {p : G1 ℚ × GL (Fin 2) (A E) | nu ℚ p.2 = 1} ∈
      𝓝[{p : G1 ℚ × GL (Fin 2) (A E) | nu ℚ p.2 = 1}] p₀ :=
    inter_mem (mem_nhdsWithin_of_mem_nhds (prod_mem_nhds hm₁ hm₂)) self_mem_nhdsWithin
  exact (key p₀ ⟨⟨mem_of_mem_nhds hm₁, mem_of_mem_nhds hm₂⟩, hp₀⟩).mono_of_mem_nhdsWithin hT
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.WtNonneg
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

private theorem cD_one' {F : Type} [Field F] [NumberField F] (g : G1 F) : cD (1 : (A F)ˣ) g = g := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cD]

private theorem norm_eta {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {D : Dat ℚ E} (W : Weil D)
    (a : (A ℚ)ˣ) : ‖((W.η.1 a : ℂˣ) : ℂ)‖ = 1 := by
  have h2 : ((W.η.1 a : ℂˣ) : ℂ) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, W.η_sq a, Units.val_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp (by rw [← norm_pow, h2, norm_one])

private theorem om_norm {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {D : Dat ℚ E} (W : Weil D)
    (ph : S4 ℚ) (b : A ℚ) (a : (A ℚ)ˣ) (k' : G1 ℚ) (x : GL (Fin 2) (A E)) (hx : nu ℚ x = 1) (v : V4 ℚ) :
    ‖(W.Om (nU b * mD a * k') (W.L x ph)).1 v‖ =
      ab a ^ 2 * ‖(W.Om k' ph).1 (fun i => (a : A ℚ) * D.act x⁻¹ v i)‖ := by
  have hc : W.Om (nU b * mD a * k') (W.L x ph) = W.L x (W.Om (nU b * mD a * k') ph) := by
    have := W.comm x (nU b * mD a * k')
    rw [hx, cD_one'] at this
    exact (congrArg (fun T : Module.End ℂ (S4 ℚ) => T ph) this).symm
  have hab : ab (1 : (A ℚ)ˣ) = 1 := by simp [ab]
  have hψ : ∀ y : A ℚ, ‖ψ y‖ = 1 := fun y => Circle.norm_coe _
  rw [hc, W.L_apply, hx, hab, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, W.Om_n, W.Om_m]
  simp only [inv_one, Complex.ofReal_one, one_mul, norm_mul, hψ, norm_eta W, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]

private theorem rat_eq {E : Type} [Field E] [NumberField E] (γ : Matrix.SpecialLinearGroup (Fin 2) E) :
    gl (ratS E γ) = ratGL E 2 (Matrix.SpecialLinearGroup.toGL γ) := by
  ext i j
  simp [ratS, ratGL]

private theorem qr_rho {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) (g : G1 E) (ξ ξ' : Fin 4 → ℚ)
    (h : D.act (gl g) (rp ξ) = rp ξ') : qr D.δ ξ' = qr D.δ ξ := by
  have hq : ∀ ζ : Fin 4 → ℚ, q4 D.δ (rp ζ) = rt (qr D.δ ζ) := fun ζ => by simp [q4, qr]
  haveI : Nontrivial (A ℚ) :=
    RingHom.domain_nontrivial (RingHom.fst (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ))
  have := D.quadForm_act (gl g) (rp ξ)
  rw [h, nu_gl, hq, hq, Units.val_one, one_mul] at this
  exact (algebraMap ℚ (A ℚ)).injective this

private theorem sum_tr {Y Y' : Type} (σ : Y ≃ Y') (f : Y → ℝ) (w : Y' → ℝ) (T : ℝ) (hf0 : ∀ y, 0 ≤ f y)
    (hs : Summable w) (h : ∀ y, f y ≤ T * w (σ y)) : Summable f ∧ ∑' y, f y ≤ T * ∑' y', w y' := by
  have hs' : Summable fun y => T * w (σ y) := (σ.summable_iff.2 hs).mul_left T
  have hf : Summable f := Summable.of_nonneg_of_le hf0 h hs'
  refine ⟨hf, (hf.tsum_le_tsum h hs').trans (le_of_eq ?_)⟩
  rw [tsum_mul_left, σ.tsum_eq w]

private theorem wt_nonneg'' (S : Set (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ)) (N : ℕ) (v : V4 ℚ) : 0 ≤ wt S N v := by
  unfold wt
  split_ifs
  · positivity
  · exact le_rfl

private theorem maj_core (hL : LatSum) (hDec : DecE) (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (D : Dat ℚ E) (W : Weil D) (P : CuspSub E 2) (hO : Orb1) (Ω : Set (GL (Fin 2) (A E))) (hΩ : IsCompact Ω)
    (hΩ1 : ∀ k ∈ Ω, nu ℚ k = 1) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hred : ∀ h : G1 E, ∃ (γ : Matrix.SpecialLinearGroup (Fin 2) E) (u : A E) (β : (A E)ˣ), ∃ k₁ ∈ Ω,
      gl (ratS E γ) * gl h = gl (nU u * mD β) * k₁ ∧ c₀ ≤ ab β)
    (ph : S4 ℚ) (hph : ph ∈ Fock D.δ) (φ : ↥(Sm E 2)) (hφP : φ ∈ P.V) (C : Set (GL (Fin 2) (A E))) (hC : IsCompact C)
    (hC1 : ∀ k ∈ C, nu ℚ k = 1) (c : ℝ) (hc : 0 < c) (s : ℕ) :
    ∃ B : ℝ, ∀ b a, ∀ k' ∈ KK ℚ, c ≤ ab a → ∀ h : G1 E, ∀ k ∈ C,
    (Summable fun ξ : Fin 4 → ℚ => ‖(W.Om (nU b * mD a * k') (W.L (gl h * k) ph)).1 (rp ξ)‖) ∧
    (∑' ξ : Fin 4 → ℚ, ‖(W.Om (nU b * mD a * k') (W.L (gl h * k) ph)).1 (rp ξ)‖) * ‖φ.1 (gl h * k)‖ ≤ B * ab a ^ 2 ∧
    (∑' ξ : {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0}, ‖(W.Om (nU b * mD a * k') (W.L (gl h * k) ph)).1 (rp ξ.1)‖) * ‖φ.1 (gl h * k)‖ ≤
      B * (ab a)⁻¹ ^ s := by
  obtain ⟨K₀, hK₀, hdom⟩ := omCpt ℚ E D W ph hph (KK ℚ) (iwa ℚ).1
  set C' : Set (GL (Fin 2) (A E)) := (fun p : GL (Fin 2) (A E) × GL (Fin 2) (A E) => p.1 * p.2) '' (Ω ×ˢ C) with hC'
  have hC'c : IsCompact C' := (hΩ.prod hC).image continuous_mul
  have hC'1 : ∀ k ∈ C', nu ℚ k = 1 := by
    rintro _ ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    change nu ℚ (x * y) = 1
    rw [nu_mul, hΩ1 x hx, hC1 y hy, one_mul]
  set c₁ : ℝ := min c c₀ with hc₁
  have hc₁0 : 0 < c₁ := lt_min hc hc₀
  obtain ⟨n, r, Bl, hlat⟩ := hL E D K₀ C' c₁ (s + 2) hK₀ hC'c hC'1 hc₁0
  obtain ⟨Bn, hBn⟩ := hdom n
  obtain ⟨hLf, -, hdec⟩ := hDec E P φ hφP
  obtain ⟨Bd, hBd⟩ := hdec C' hC'c c₁ hc₁0 r
  refine ⟨|Bn| * (Bl * Bd), fun b a k' hk' hca h k hk => ?_⟩
  obtain ⟨γ, u, β, k₁, hk₁, heq, hβ⟩ := hred h
  obtain ⟨ρ, hρ⟩ := (hO E D).1 γ
  set k₂ : GL (Fin 2) (A E) := k₁ * k with hk₂
  have hk₂C : k₂ ∈ C' := ⟨(k₁, k), ⟨hk₁, hk⟩, rfl⟩
  set x₂ : GL (Fin 2) (A E) := gl (nU u * mD β) * k₂ with hx₂
  have hxx : gl (ratS E γ) * (gl h * k) = x₂ := by
    rw [← mul_assoc, heq, hx₂, hk₂, mul_assoc]
  have hx1 : nu ℚ (gl h * k) = 1 := by rw [nu_mul, nu_gl, hC1 k hk, one_mul]
  have hinv : ∀ ξ, D.act (gl h * k)⁻¹ (rp ξ) = D.act x₂⁻¹ (rp (ρ ξ)) := fun ξ => by
    have hg : (gl h * k)⁻¹ = x₂⁻¹ * gl (ratS E γ) := by
      rw [← hxx, _root_.mul_inv_rev (gl (ratS E γ)) (gl h * k), inv_mul_cancel_right]
    rw [hg, D.act_mul, hρ]
  have hφ : φ.1 (gl h * k) = φ.1 x₂ := by
    rw [← hxx, rat_eq]
    exact (hLf.2 _ _).symm
  have ha0 : 0 < ab a := hc.trans_le hca
  have hβ0 : 0 < ab β := hc₀.trans_le hβ
  set w : (Fin 4 → ℚ) → ℝ := fun ξ => wt K₀ n fun i => (a : A ℚ) * D.act x₂⁻¹ (rp ξ) i with hw
  have hlat' := hlat a u β k₂ hk₂C ((min_le_left _ _).trans hca) ((min_le_right _ _).trans hβ)
  obtain ⟨hws, hw1, hw2⟩ := hlat'
  set f : (Fin 4 → ℚ) → ℝ := fun ξ => ‖(W.Om (nU b * mD a * k') (W.L (gl h * k) ph)).1 (rp ξ)‖ with hf
  set T : ℝ := ab a ^ 2 * |Bn| with hT
  have hT0 : 0 ≤ T := by positivity
  have hfw : ∀ ξ, f ξ ≤ T * w (ρ ξ) := fun ξ => by
    simp only [hf, hw]
    rw [om_norm W ph b a k' _ hx1, hinv, hT, mul_assoc]
    refine mul_le_mul_of_nonneg_left (((hBn k' hk' _)).trans ?_) (by positivity)
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (wt_nonneg'' _ _ _)
  obtain ⟨hfs, hf1⟩ := sum_tr ρ.toEquiv f w T (fun _ => norm_nonneg _) hws hfw
  have hqρ : ∀ ξ, qr D.δ (ρ ξ) = qr D.δ ξ := fun ξ => qr_rho D _ ξ (ρ ξ) (hρ ξ)
  let σ : {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0} ≃ {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0} :=
    ρ.toEquiv.subtypeEquiv fun ξ => by
      change qr D.δ ξ ≠ 0 ↔ qr D.δ (ρ ξ) ≠ 0
      rw [hqρ]
  obtain ⟨-, hf2⟩ := sum_tr σ (fun ξ => f ξ.1) (fun ξ => w ξ.1) T (fun _ => norm_nonneg _) (hws.subtype _)
    (fun ξ => hfw ξ.1)
  have hw0 : ∀ ξ, 0 ≤ w ξ := fun ξ => wt_nonneg'' _ _ _
  have hW0 : 0 ≤ ∑' ξ, w ξ := tsum_nonneg hw0
  have hW0' : 0 ≤ ∑' ξ : {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0}, w ξ.1 := tsum_nonneg fun ξ => hw0 ξ.1
  have hφb := hBd u β k₂ hk₂C ((min_le_right _ _).trans hβ)
  rw [hφ]
  set Φ : ℝ := ‖φ.1 x₂‖ with hΦ
  have hΦ0 : 0 ≤ Φ := norm_nonneg _
  have hcancel : ab β ^ r * (ab β)⁻¹ ^ r = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hβ0.ne', one_pow]
  refine ⟨hfs, ?_, ?_⟩
  · have h1 : (∑' ξ, w ξ) * Φ ≤ (Bl * ab β ^ r) * (Bd * (ab β)⁻¹ ^ r) :=
      mul_le_mul hw1 hφb hΦ0 (hW0.trans hw1)
    calc (∑' ξ, f ξ) * Φ ≤ (T * ∑' ξ, w ξ) * Φ := mul_le_mul_of_nonneg_right hf1 hΦ0
      _ = T * ((∑' ξ, w ξ) * Φ) := by ring
      _ ≤ T * ((Bl * ab β ^ r) * (Bd * (ab β)⁻¹ ^ r)) := mul_le_mul_of_nonneg_left h1 hT0
      _ = |Bn| * (Bl * Bd) * ab a ^ 2 * (ab β ^ r * (ab β)⁻¹ ^ r) := by rw [hT]; ring
      _ = |Bn| * (Bl * Bd) * ab a ^ 2 := by rw [hcancel, mul_one]
  · have h1 : (∑' ξ : {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0}, w ξ.1) * Φ ≤
        (Bl * (ab a)⁻¹ ^ (s + 2) * ab β ^ r) * (Bd * (ab β)⁻¹ ^ r) :=
      mul_le_mul hw2 hφb hΦ0 (hW0'.trans hw2)
    have hca2 : ab a ^ 2 * (ab a)⁻¹ ^ (s + 2) = (ab a)⁻¹ ^ s := by
      rw [pow_add, mul_comm ((ab a)⁻¹ ^ s), ← mul_assoc, ← mul_pow, mul_inv_cancel₀ ha0.ne', one_pow, one_mul]
    calc (∑' ξ : {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0}, f ξ.1) * Φ
        ≤ (T * ∑' ξ : {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0}, w ξ.1) * Φ := mul_le_mul_of_nonneg_right hf2 hΦ0
      _ = T * ((∑' ξ : {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0}, w ξ.1) * Φ) := by ring
      _ ≤ T * ((Bl * (ab a)⁻¹ ^ (s + 2) * ab β ^ r) * (Bd * (ab β)⁻¹ ^ r)) := mul_le_mul_of_nonneg_left h1 hT0
      _ = |Bn| * (Bl * Bd) * (ab a ^ 2 * (ab a)⁻¹ ^ (s + 2)) * (ab β ^ r * (ab β)⁻¹ ^ r) := by rw [hT]; ring
      _ = |Bn| * (Bl * Bd) * (ab a)⁻¹ ^ s := by rw [hcancel, hca2, mul_one]

private theorem cont_gl {E : Type} [Field E] [NumberField E] : Continuous (gl : G1 E → GL (Fin 2) (A E)) := by
  refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
  have h : Continuous fun g : G1 E => ((g⁻¹ : G1 E) : Matrix (Fin 2) (Fin 2) (A E)) :=
    continuous_subtype_val.comp continuous_inv
  exact h

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.maj :
    LatSum → DecE → Maj := by
  intro hL hDec E _ _ _ D W _ _ P ph hph φ hφ C hC hC1 c hc s
  obtain ⟨c₀, K, hc₀, hK, hr⟩ := redE E
  refine maj_core hL hDec E D W P orb1 (gl '' K) (hK.image cont_gl) ?_ c₀ hc₀ ?_ ph hph φ hφ C hC hC1 c hc s
  · rintro _ ⟨g, -, rfl⟩
    exact nu_gl g
  · intro h
    obtain ⟨γ, u, b, k, hk, he, hb⟩ := hr h
    refine ⟨γ, u, b, gl k, ⟨k, hk, rfl⟩, ?_, hb⟩
    rw [← map_mul, he, map_mul]
end

