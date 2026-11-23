module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle0001
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ChirpQ
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C
open GroundTheory.Heights₂.Theta

section ChirpQ

variable {F : Type} [Field F] [NumberField F]

private theorem eval_map_hom {R S ι : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (p : MvPolynomial ι R) (v : ι → R) :
    MvPolynomial.eval (fun i => f (v i)) (p.map f) = f (MvPolynomial.eval v p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

private theorem continuous_eval_poly {R ι : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (p : MvPolynomial ι R) :
    Continuous fun v : ι → R => MvPolynomial.eval v p := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using continuous_const
  | add p q hp hq => simp only [map_add (f := _)]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, MvPolynomial.eval_X]; exact hp.mul (continuous_apply i)


variable (F) in
private noncomputable def lT : mixedEmbedding.mixedSpace F →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (-((mixedTraceForm F).flip 1))

private theorem psi_split (x : A F) :
    ψ x = ((Real.fourierChar (lT F (adeleInfHom x)) : Circle) : ℂ) *
      ((finiteAdelicChar F (adeleFinHom x) : Circle) : ℂ) := by
  have h := adelicChar_mul_eq (K := F) x 1
  rw [mul_one] at h
  have h1 : homeomorphMixedSpace F (1 : A F).1 = 1 := by
    exact map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  rw [h1] at h
  have h2 : x.2 * (1 : A F).2 = adeleFinHom x := by
    change x.2 * 1 = x.2
    rw [mul_one]
  rw [h2] at h
  exact h

private theorem chirp_poly (p : MvPolynomial (Fin 4) (A F)) (φ : V4 F → ℂ)
    (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) :
    (fun v => ψ (MvPolynomial.eval v p) * φ v) ∈ schwartzBruhatPi (K := F) (ι := Fin 4) := by
  refine Submodule.span_induction
    (p := fun f _ => (fun v => ψ (MvPolynomial.eval v p) * f v) ∈ schwartzBruhatPi (K := F) (ι := Fin 4))
    ?_ ?_ ?_ ?_ hφ
  · rintro _ ⟨φ0, g, hg, rfl⟩
    have hT := chirpInf F (Fin 4) (p.map adeleInfHom) (lT F)
    have hloc : IsLocallyConstant fun w : Fin 4 → FiniteAdeleRing (𝓞 F) F =>
        ((finiteAdelicChar F (MvPolynomial.eval w (p.map adeleFinHom)) : Circle) : ℂ) := by
      have h1 := (isLocallyConstant_finiteAdelicChar_mul (K := F) 1).comp_continuous
        (continuous_eval_poly (p.map (adeleFinHom (K := F))))
      simpa [Function.comp_def] using h1
    have hg' : (fun w => ((finiteAdelicChar F (MvPolynomial.eval w (p.map adeleFinHom)) : Circle) : ℂ) * g w)
        ∈ finiteSchwartzBruhatPi F (ι := Fin 4) :=
      ⟨hloc.mul hg.1, hg.2.mul_left⟩
    convert schwartzBruhatTensorPi_mem (SchwartzMap.smulLeftCLM ℂ (fun x : Fin 4 → mixedEmbedding.mixedSpace F =>
      ((Real.fourierChar (lT F (MvPolynomial.eval x (p.map adeleInfHom))) : Circle) : ℂ)) φ0) hg' using 1
    funext v
    simp only [schwartzBruhatTensorPi]
    rw [SchwartzMap.smulLeftCLM_apply_apply hT, psi_split]
    simp only [smul_eq_mul, infPartPi_eq_adeleInfHom, finPartPi_eq_adeleFinHom, eval_map_hom]
    ring
  · convert (schwartzBruhatPi (K := F) (ι := Fin 4)).zero_mem using 1
    funext v
    simp
  · intro f g _ _ hf hg
    convert (schwartzBruhatPi (K := F) (ι := Fin 4)).add_mem hf hg using 1
    funext v
    simp [mul_add]
  · intro a f _ hf
    convert (schwartzBruhatPi (K := F) (ι := Fin 4)).smul_mem a hf using 1
    funext v
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

end ChirpQ

theorem UpperTheory.ConvolutionTheory.R2.C.chirpQ :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (b : A F) (y : V4 F) (φ : V4 F → ℂ), φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4) →
    (fun v => ψ (b * q4 δ v + B4 δ v y) * φ v) ∈ schwartzBruhatPi (K := F) (ι := Fin 4) := by
  intro F _ _ δ b y φ hφ
  open MvPolynomial in
  have h := chirp_poly (F := F)
    (C b * (X 2 ^ 2 - C (rt δ) * X 3 ^ 2 - X 1 * X 0) +
      (2 * (X 2 * C (y 2) - C (rt δ) * (X 3 * C (y 3))) - X 1 * C (y 0) - X 0 * C (y 1))) φ hφ
  convert h using 3 with v
  simp [q4, B4]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.EtaEx
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.etaEx :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E), ∃ η : HChar F, IsQuadCharOf E η ∧ (∀ a, η.1 a ^ 2 = 1) ∧ (∀ z : (A E)ˣ, η.1 (ideleNorm F E z) = 1) ∧
    ∀ a, η.1 a = 1 → ∃ (t : F) (z : (A E)ˣ), t ≠ 0 ∧ (a : A F) = rt t * (ideleNorm F E z : (A F)ˣ) := by
  intro F E _ _ _ _ _ D
  haveI : Algebra.IsQuadraticExtension F E :=
    ⟨by rw [Module.finrank_eq_card_basis D.b]; simp⟩
  have h0 : D.b 0 = 1 := D.b0
  have h1 : D.b 1 * D.b 1 = algebraMap F E D.δ := by
    rw [D.b1, ← pow_two, D.sq]
  obtain ⟨η, hq, hη⟩ := UpperTheory.ConvolutionTheory.R2.C.etaQuad F E
  have hone : ∀ a, GlobalTheory.IdeleNormChar.normSign E a = 1 → η.1 a = 1 := by
    intro a ha
    refine Units.ext ?_
    rw [hη a, ha]
    simp
  have hsign : ∀ a, η.1 a = 1 → GlobalTheory.IdeleNormChar.normSign E a = 1 := by
    intro a ha
    have h := hη a
    rw [ha] at h
    rcases Int.units_eq_one_or (GlobalTheory.IdeleNormChar.normSign E a) with e | e
    · exact e
    · rw [e] at h
      norm_num at h
  have hmem : ∀ z : (A E)ˣ, ideleNorm F E z ∈ GlobalTheory.QuadSymbol.normGroup F E (A F) := by
    intro z
    obtain ⟨s, t, hst⟩ := (UpperTheory.ConvolutionTheory.R2.C.normForm F E D (ideleNorm F E z)).2 ⟨z, rfl⟩
    exact (GlobalTheory.QuadSymbol.mem_normGroup_iff_form D.b h0 h1).2 ⟨s, t, hst⟩
  refine ⟨η, hq, ?_, ?_, ?_⟩
  · intro a
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, hη a]
    rcases Int.units_eq_one_or (GlobalTheory.IdeleNormChar.normSign E a) with e | e <;> rw [e] <;> simp
  · intro z
    exact hone _ (GlobalTheory.IdeleNormChar.normSign_of_mem E (hmem z))
  · intro a ha
    obtain ⟨t, ht⟩ := (GlobalTheory.IdeleNormChar.normSign_eq_one_iff E a).1 (hsign a ha)
    obtain ⟨s, u, hsu⟩ := (GlobalTheory.QuadSymbol.mem_normGroup_iff_form D.b h0 h1).1 ht
    obtain ⟨z, hz⟩ := (UpperTheory.ConvolutionTheory.R2.C.normForm F E D _).1 ⟨s, u, hsu⟩
    refine ⟨(t : F), z, t.ne_zero, ?_⟩
    rw [hz]
    have : a = GlobalTheory.QuadSymbol.toUnits F (A F) t * (a / GlobalTheory.QuadSymbol.toUnits F (A F) t) := by
      rw [mul_div_cancel]
    exact congrArg Units.val this
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.GenRel
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private def upperP (F : Type) [Field F] [NumberField F] : Subgroup (G1 F) where
  carrier := {g | g 1 0 = 0}
  mul_mem' := by
    intro g h hg hh
    have hg' : g.1 1 0 = 0 := hg
    have hh' : h.1 1 0 = 0 := hh
    show (g * h).1 1 0 = 0
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hg', hh']
    simp
  one_mem' := by
    show (1 : G1 _).1 1 0 = 0
    simp
  inv_mem' := by
    intro g hg
    have hg' : g.1 1 0 = 0 := hg
    show (g⁻¹).1 1 0 = 0
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [hg']

private theorem bor {F : Type} [Field F] [NumberField F] {H : Type} [Monoid H]
    {N : A F → H} {M : (A F)ˣ → H} {W : H} (hR : Rel N M W) (b b' : A F) (a a' : (A F)ˣ) :
    (N b * M a) * (N b' * M a') = N (b + (a : A F) ^ 2 * b') * M (a * a') := by
  rw [hR.N_add, hR.M_mul]
  calc N b * M a * (N b' * M a') = N b * (M a * N b') * M a' := by simp only [mul_assoc]
    _ = _ := by rw [hR.MN]; simp only [mul_assoc]

private theorem gen_rel {F : Type} [Field F] [NumberField F] {H : Type} [Monoid H]
    {N : A F → H} {M : (A F)ˣ → H} {W : H} (hR : Rel N M W) (hG : Gauss N M W) (t a : (A F)ˣ) :
    W * (N (t : A F) * M a) * W =
      (N (-((t⁻¹ : (A F)ˣ) : A F)) * M (-t⁻¹)) * W * (N (-((t⁻¹ : (A F)ˣ) : A F)) * M a⁻¹) := by
  have h1 : M a * W = W * M a⁻¹ := by
    have := hR.WM a⁻¹
    rw [inv_inv] at this
    exact this.symm
  calc W * (N (t : A F) * M a) * W = W * N (t : A F) * (M a * W) := by simp only [mul_assoc]
    _ = W * N (t : A F) * W * M a⁻¹ := by rw [h1]; simp only [mul_assoc]
    _ = _ := by rw [hG t]; simp only [mul_assoc]

private theorem w_small {F : Type} [Field F] [NumberField F] {b c : A F} {a d : (A F)ˣ}
    (h : wW F * (nU b * mD a) = nU c * mD d * wW F) : b = 0 ∧ c = 0 ∧ d = a⁻¹ := by
  have h' : !![(0 : A F), 1; -1, 0] * (!![1, b; 0, 1] * !![(a : A F), 0; 0, ((a⁻¹ : (A F)ˣ) : A F)]) =
      !![1, c; 0, 1] * !![(d : A F), 0; 0, ((d⁻¹ : (A F)ˣ) : A F)] * !![(0 : A F), 1; -1, 0] :=
    congrArg Subtype.val h
  have e11 := congrFun (congrFun h' 1) 1
  have e01 := congrFun (congrFun h' 0) 1
  have e00 := congrFun (congrFun h' 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e11 e01 e00
  exact ⟨e11, e00, (Units.ext e01).symm⟩

private theorem w_big {F : Type} [Field F] [NumberField F] {b c c' : A F} {a d d' : (A F)ˣ}
    (h : wW F * (nU b * mD a) * wW F = nU c * mD d * wW F * (nU c' * mD d')) : IsUnit b := by
  have h' : !![(0 : A F), 1; -1, 0] * (!![1, b; 0, 1] * !![(a : A F), 0; 0, ((a⁻¹ : (A F)ˣ) : A F)]) * !![(0 : A F), 1; -1, 0] =
      !![1, c; 0, 1] * !![(d : A F), 0; 0, ((d⁻¹ : (A F)ˣ) : A F)] * !![(0 : A F), 1; -1, 0] *
        (!![1, c'; 0, 1] * !![(d' : A F), 0; 0, ((d'⁻¹ : (A F)ˣ) : A F)]) :=
    congrArg Subtype.val h
  have e := congrFun (congrFun h' 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e
  have hu : IsUnit (b * ((a⁻¹ : (A F)ˣ) : A F)) := by
    rw [e, ← Units.val_mul]
    exact (d⁻¹ * d').isUnit.neg
  exact isUnit_of_mul_isUnit_left hu

theorem UpperTheory.ConvolutionTheory.R2.C.chunk :
    ∀ (F : Type) [Field F] [NumberField F] (H : Type) [Monoid H] (N : A F → H) (M : (A F)ˣ → H) (W : H), Rel N M W → Gauss N M W →
    (∀ s : Finset (G1 F), ∃ u : G1 F, ∀ g ∈ s, IsUnit ((g * u) 1 0)) →
    ∃ Φ : G1 F →* H, (∀ b, Φ (nU b) = N b) ∧ (∀ a, Φ (mD a) = M a) ∧ Φ (wW F) = W := by
  intro F _ _ H _ N M W hR hG hgen
  obtain ⟨gR, gG, gP, gU, gC⟩ := grpRel F
  obtain ⟨N', hN'⟩ : ∃ N' : A F → Hˣ, ∀ b, (N' b : H) = N b :=
    ⟨fun b => ⟨N b, N (-b), by rw [← hR.N_add]; simp [hR.N_zero],
      by rw [← hR.N_add]; simp [hR.N_zero]⟩, fun _ => rfl⟩
  obtain ⟨M', hM'⟩ : ∃ M' : (A F)ˣ → Hˣ, ∀ a, (M' a : H) = M a :=
    ⟨fun a => ⟨M a, M a⁻¹, by rw [← hR.M_mul]; simp [hR.M_one],
      by rw [← hR.M_mul]; simp [hR.M_one]⟩, fun _ => rfl⟩
  obtain ⟨W', hW'⟩ : ∃ W' : Hˣ, (W' : H) = W := hR.W_unit
  have memP : ∀ b a, nU b * mD a ∈ upperP F := fun b a => (gP _).2 ⟨b, a, rfl⟩
  have memN : ∀ b, nU b ∈ upperP F := fun b => (gP _).2 ⟨b, 1, by rw [gR.M_one, mul_one]⟩
  have memM : ∀ a, mD a ∈ upperP F := fun a => (gP _).2 ⟨0, a, by rw [gR.N_zero, one_mul]⟩
  have hex : ∀ p : upperP F, ∃ b a, (p : G1 F) = nU b * mD a := fun p => (gP p).1 p.2
  choose bb aa hba using hex
  have huniq : ∀ (p : upperP F) b a, (p : G1 F) = nU b * mD a → bb p = b ∧ aa p = a :=
    fun p b a h => gU _ _ _ _ ((hba p).symm.trans h)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : upperP F →* Hˣ, ∀ (p : upperP F) b a, (p : G1 F) = nU b * mD a →
      ρ p = N' b * M' a := by
    refine ⟨MonoidHom.mk' (fun p => N' (bb p) * M' (aa p)) ?_, ?_⟩
    · intro p q
      obtain ⟨e1, e2⟩ := huniq (p * q) (bb p + (aa p : A F) ^ 2 * bb q) (aa p * aa q) (by
        rw [Subgroup.coe_mul, hba p, hba q, bor gR])
      rw [e1, e2]
      apply Units.ext
      simp only [Units.val_mul, hN', hM']
      exact (bor hR _ _ _ _).symm
    · intro p b a h
      obtain ⟨e1, e2⟩ := huniq p b a h
      simp [e1, e2]
  have ρv : ∀ (p : upperP F) b a, (p : G1 F) = nU b * mD a → ((ρ p : Hˣ) : H) = N b * M a := by
    intro p b a h
    rw [hρ p b a h, Units.val_mul, hN', hM']
  have c1 : ∀ p q : upperP F, wW F * p = q * wW F → W' * ρ p = ρ q * W' := by
    intro p q h
    rw [hba p, hba q] at h
    obtain ⟨hb, hc, hd⟩ := w_small h
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, ρv p _ _ (hba p), ρv q _ _ (hba q), hb, hc, hd, hW', hR.N_zero,
      one_mul, one_mul]
    exact hR.WM _
  have c2 : ∀ p : upperP F, (∃ p₁ p₂ : upperP F, wW F * p * wW F = p₁ * wW F * p₂) →
      ∃ p₁ p₂ : upperP F, wW F * p * wW F = p₁ * wW F * p₂ ∧ W' * ρ p * W' = ρ p₁ * W' * ρ p₂ := by
    rintro p ⟨p₁, p₂, h⟩
    rw [hba p, hba p₁, hba p₂] at h
    obtain ⟨t, ht⟩ := w_big h
    refine ⟨⟨_, memP (-((t⁻¹ : (A F)ˣ) : A F)) (-t⁻¹)⟩, ⟨_, memP (-((t⁻¹ : (A F)ˣ) : A F)) (aa p)⁻¹⟩, ?_, ?_⟩
    · rw [hba p, ← ht]
      exact gen_rel gR gG t (aa p)
    · apply Units.ext
      simp only [Units.val_mul]
      rw [ρv p _ _ (hba p), ρv ⟨_, memP (-((t⁻¹ : (A F)ˣ) : A F)) (-t⁻¹)⟩ _ _ rfl,
        ρv ⟨_, memP (-((t⁻¹ : (A F)ˣ) : A F)) (aa p)⁻¹⟩ _ _ rfl, hW', ← ht]
      exact gen_rel hR hG t (aa p)
  have c3 : ∀ s : Finset (G1 F), ∃ u : G1 F, ∀ g ∈ s, ∃ p₁ p₂ : upperP F, g * u = p₁ * wW F * p₂ := by
    intro s
    obtain ⟨u, hu⟩ := hgen s
    refine ⟨u, fun g hg => ?_⟩
    obtain ⟨b, a, b', e⟩ := (gC _).1 (hu g hg)
    exact ⟨⟨_, memP b a⟩, ⟨_, memN b'⟩, e⟩
  obtain ⟨Φ, h1, h2⟩ := GlobalTheory.bigCell_hom (G1 F) Hˣ (upperP F) (wW F) ρ W' c1 c2 c3
  refine ⟨(Units.coeHom H).comp Φ, fun b => ?_, fun a => ?_, ?_⟩
  · have := h1 ⟨_, memN b⟩
    simp only [MonoidHom.comp_apply, Units.coeHom_apply]
    rw [show Φ (nU b) = ρ ⟨_, memN b⟩ from this,
      ρv ⟨_, memN b⟩ b 1 (by rw [gR.M_one, mul_one]), hR.M_one, mul_one]
  · have := h1 ⟨_, memM a⟩
    simp only [MonoidHom.comp_apply, Units.coeHom_apply]
    rw [show Φ (mD a) = ρ ⟨_, memM a⟩ from this,
      ρv ⟨_, memM a⟩ 0 a (by rw [gR.N_zero, one_mul]), hR.N_zero, one_mul]
  · simp only [MonoidHom.comp_apply, Units.coeHom_apply]
    rw [h2, hW']
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Generic
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private lemma fieldCase (K : Type) [Field K] [CharZero K] {ι : Type} (s : Finset ι) (c d : ι → K)
    (h : ∀ i ∈ s, c i ≠ 0 ∨ d i ≠ 0) : ∃ t : K, ∀ i ∈ s, c i + d i * t ≠ 0 := by
  have hinf : Infinite (IsLocalRing.ResidueField K) :=
    Infinite.of_injective _ (IsLocalRing.residue K).injective
  have hc : ((s.image fun i => (c i, d i)).card : ℕ∞) < ENat.card (IsLocalRing.ResidueField K) := by
    rw [ENat.card_eq_top_of_infinite]
    exact ENat.coe_lt_top _
  obtain ⟨t, ht⟩ := UpperTheory.ConvolutionTheory.R2.C.genLoc K (s.image fun i => (c i, d i)) (by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    simpa [isUnit_iff_ne_zero] using h i hi) hc
  exact ⟨t, fun i hi => (ht _ (Finset.mem_image_of_mem _ hi)).ne_zero⟩

private lemma rowUnit {R : Type} [CommRing R] [IsLocalRing R] {a b c d : R}
    (h : a * d - b * c = 1) : IsUnit c ∨ IsUnit d := by
  by_contra hn
  push_neg at hn
  have hc : c ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal c).2 hn.1
  have hd : d ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal d).2 hn.2
  have h1 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [← h]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hd) (Ideal.mul_mem_left _ _ hc)
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h1)

private lemma row {F : Type} [Field F] [NumberField F] (g : G1 F) :
    g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

private lemma valUnit {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (x : v.adicCompletionIntegers F) (h : IsUnit x) : Valued.v (x : v.adicCompletion F) = 1 := by
  obtain ⟨u, rfl⟩ := h
  have h1 : Valued.v (((u : v.adicCompletionIntegers F)) : v.adicCompletion F) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 (u : v.adicCompletionIntegers F).2
  have h2 : Valued.v (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F).2
  have h3 : Valued.v (((u : v.adicCompletionIntegers F)) : v.adicCompletion F) *
      Valued.v (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) = 1 := by
    rw [← map_mul]
    have h4 : (((u : v.adicCompletionIntegers F)) : v.adicCompletion F) *
        (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) = 1 := by
      exact_mod_cast congrArg (fun y : v.adicCompletionIntegers F => (y : v.adicCompletion F)) u.mul_inv
    rw [h4, map_one]
  refine le_antisymm h1 ?_
  calc (1 : _) = _ := h3.symm
    _ ≤ _ := mul_le_of_le_one_right' h2

private lemma goodPlace {F : Type} [Field F] [NumberField F] (s : Finset (G1 F))
    (v : HeightOneSpectrum (𝓞 F))
    (hint : ∀ g ∈ s, ∀ i j, (g i j).2 v ∈ v.adicCompletionIntegers F)
    (hbig : (s.card : ℕ∞) < ENat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F))) :
    ∃ t : v.adicCompletion F, t ∈ v.adicCompletionIntegers F ∧
      ∀ g ∈ s, Valued.v ((g 1 0).2 v + (g 1 1).2 v * t) = 1 := by
  let toO : v.adicCompletion F → v.adicCompletionIntegers F :=
    fun x => if h : x ∈ v.adicCompletionIntegers F then ⟨x, h⟩ else 0
  have hto : ∀ x (h : x ∈ v.adicCompletionIntegers F), (toO x : v.adicCompletion F) = x := by
    intro x h
    simp only [toO, dif_pos h]
  let pr : G1 F → v.adicCompletionIntegers F × v.adicCompletionIntegers F :=
    fun g => (toO ((g 1 0).2 v), toO ((g 1 1).2 v))
  obtain ⟨t, ht⟩ := UpperTheory.ConvolutionTheory.R2.C.genLoc (v.adicCompletionIntegers F) (s.image pr) (by
    intro p hp
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hp
    have hdet : (g 0 0).2 v * (g 1 1).2 v - (g 0 1).2 v * (g 1 0).2 v = 1 :=
      congrArg (fun x : A F => x.2 v) (row g)
    refine rowUnit (a := toO ((g 0 0).2 v)) (b := toO ((g 0 1).2 v)) (Subtype.ext ?_)
    push_cast
    rw [hto _ (hint g hg 0 0), hto _ (hint g hg 0 1), hto _ (hint g hg 1 0), hto _ (hint g hg 1 1)]
    exact hdet) (lt_of_le_of_lt (by exact_mod_cast Finset.card_image_le) hbig)
  refine ⟨t, t.2, fun g hg => ?_⟩
  have h := valUnit v _ (ht _ (Finset.mem_image_of_mem pr hg))
  simp only [pr] at h
  push_cast at h
  rwa [hto _ (hint g hg 1 0), hto _ (hint g hg 1 1)] at h

theorem UpperTheory.ConvolutionTheory.R2.C.generic :
    ∀ (F : Type) [Field F] [NumberField F] (s : Finset (G1 F)), ∃ u : G1 F, ∀ g ∈ s, IsUnit ((g * u) 1 0) := by
  intro F _ _ s
  have hI : ∀ w : InfinitePlace F, ∃ t : w.Completion, ∀ g ∈ s, (g 1 0).1 w + (g 1 1).1 w * t ≠ 0 := by
    intro w
    haveI : CharZero w.Completion :=
      charZero_of_injective_algebraMap (algebraMap F w.Completion).injective
    refine fieldCase w.Completion s (fun g => (g 1 0).1 w) (fun g => (g 1 1).1 w) fun g _ => ?_
    have hdet : (g 0 0).1 w * (g 1 1).1 w - (g 0 1).1 w * (g 1 0).1 w = 1 :=
      congrArg (fun x : A F => x.1 w) (row g)
    by_contra hn
    push_neg at hn
    simp only [hn.1, hn.2, mul_zero, sub_zero] at hdet
    exact zero_ne_one hdet
  let G : HeightOneSpectrum (𝓞 F) → Prop := fun v =>
    (∀ g ∈ s, ∀ i j, (g i j).2 v ∈ v.adicCompletionIntegers F) ∧
      (s.card : ℕ∞) < ENat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F))
  have hG : ∀ᶠ v in cofinite, G v := by
    refine Filter.Eventually.and ?_ (UpperTheory.ConvolutionTheory.R2.C.resBig F s.card)
    refine (Filter.eventually_all_finset s).2 fun g _ => ?_
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    exact (g i j).2.2
  have hF : ∀ v : HeightOneSpectrum (𝓞 F), ∃ t : v.adicCompletion F,
      (G v → t ∈ v.adicCompletionIntegers F) ∧
      ∀ g ∈ s, (g 1 0).2 v + (g 1 1).2 v * t ≠ 0 ∧
        (G v → Valued.v ((g 1 0).2 v + (g 1 1).2 v * t) = 1) := by
    intro v
    by_cases hv : G v
    · obtain ⟨t, ht, hu⟩ := goodPlace s v hv.1 hv.2
      refine ⟨t, fun _ => ht, fun g hg => ⟨fun h0 => ?_, fun _ => hu g hg⟩⟩
      have := hu g hg
      rw [h0, map_zero] at this
      exact zero_ne_one this
    · obtain ⟨t, ht⟩ := fieldCase (v.adicCompletion F) s (fun g => (g 1 0).2 v)
        (fun g => (g 1 1).2 v) (fun g _ => by
          have hdet : (g 0 0).2 v * (g 1 1).2 v - (g 0 1).2 v * (g 1 0).2 v = 1 :=
            congrArg (fun x : A F => x.2 v) (row g)
          by_contra hn
          push_neg at hn
          simp only [hn.1, hn.2, mul_zero, sub_zero] at hdet
          exact zero_ne_one hdet)
      exact ⟨t, fun h => absurd h hv, fun g hg => ⟨ht g hg, fun h => absurd h hv⟩⟩
  choose tI htI using hI
  choose tF htF using hF
  let tf : FiniteAdeleRing (𝓞 F) F := ⟨tF, hG.mono fun v hv => (htF v).1 hv⟩
  let t : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F := (tI, tf)
  let t' : A F := t
  let u : G1 F := ⟨!![1, 0; t', 1], by simp [Matrix.det_fin_two]⟩
  refine ⟨u, fun g hg => ?_⟩
  have hu : (g * u) 1 0 = g 1 0 + g 1 1 * t' := by
    show (g.1 * !![1, 0; t', 1]) 1 0 = _
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp
  rw [hu]
  refine (UpperTheory.ConvolutionTheory.R2.C.unitA F _).2 ⟨fun w => htI w g hg, fun v => ((htF v).2 g hg).1, ?_⟩
  exact hG.mono fun v hv => ((htF v).2 g hg).2 hv
end

