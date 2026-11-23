module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0051
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraEigenDecompositionCMSignature
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0259
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1508
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1509
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Lbc
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
public import GroundTheory.AutomorphicForms.MeasuresModulus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeImagesEigenLinesCmUnitaryShimuraObject
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

noncomputable section
namespace GlobalTheory.FlatCM.ImageDeg


open GlobalTheory.HermHom in
theorem form_diff_eq_pair : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P)
  (P' : Out.PolAV (Sp (𝓞 K))) (F' : GenFib P') (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K))
  (f₁ f₂ : P.A ⟶ P'.A) (g : P.A ⟶ P.A) (M₁ M₂ : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K))
  (N : (Fin F.P₀.g → K) →ₗ[K] (Fin F.P₀.g → K)), F.IsHerm h → F'.IsHerm h' → IsMonHom f₁ → IsMonHom f₂ →
  IsMonHom g → LamEq P'.L f₁ f₂ P.L g (𝟙 P.A) → F.IsDiffOf F' f₁ M₁ → F.IsDiffOf F' f₂ M₂ → F.IsDiffOf F g N →
  ∀ s c c', h'.form s (M₂ c) (M₁ c') = h.form s c (N c') := by
  intro hU hL K _ _ P F P' F' h h' f₁ f₂ g M₁ M₂ N hh hh' hf₁ hf₂ hg hlam hM₁ hM₂ hN s c c'
  obtain ⟨Q, φ, t, u, Hm, χ, W, hφ, hA, hW, hform⟩ := hh s
  obtain ⟨Q', φ', t', u', Hm', χ', W', hφ', hA', hW', hform'⟩ := hh' s
  obtain ⟨-, a₀, ha₀, ea₀, da⟩ := _root_.GlobalTheory.CM.DiffCoord.existsUnique_isDiffOf K P F P' F' f₁ hf₁
  obtain ⟨-, b₀, hb₀, eb₀, db⟩ := _root_.GlobalTheory.CM.DiffCoord.existsUnique_isDiffOf K P F P' F' f₂ hf₂
  obtain ⟨-, g₀, hg₀, eg₀, dg⟩ := _root_.GlobalTheory.CM.DiffCoord.existsUnique_isDiffOf K P F P F g hg
  have hlam₀ : LamEq F'.P₀.L a₀ b₀ F.P₀.L g₀ (𝟙 F.P₀.A) :=
    lamEq_baseChange _ _ (spMap (algebraMap (𝓞 K) K)) P.A P.A P'.A P.A F.P₀.A F.P₀.A F'.P₀.A F.P₀.A
      F.φ F.φ F'.φ F.φ F.fib.2.1.1.w F.fib.2.1.1.w F'.fib.2.1 F.fib.2.1
      P'.L P.L F'.P₀.L F.P₀.L P'.isLB P.isLB F'.P₀.isLB F.P₀.isLB F'.fib.2.2 F.fib.2.2 f₁ f₂ g (𝟙 _) a₀ b₀ g₀ (𝟙 _)
      ea₀ eb₀ eg₀ (by simp) hlam
  obtain ⟨a₁, ha₁, ea⟩ := NormHom.exists_monHom_lift hφ.2.1 hφ'.2.1 a₀
  obtain ⟨b₁, hb₁, eb⟩ := NormHom.exists_monHom_lift hφ.2.1 hφ'.2.1 b₀
  obtain ⟨g₁, hg₁, eg⟩ := NormHom.exists_monHom_lift hφ.2.1 hφ.2.1 g₀
  obtain ⟨-, -, -, -, t₁, t₂, -⟩ := AHWeil.tangent_and_weil_of_isAH hU Q Q.g u Hm χ hA
  obtain ⟨-, -, -, -, t₁', t₂', -⟩ := AHWeil.tangent_and_weil_of_isAH hU Q' Q'.g u' Hm' χ' hA'
  obtain ⟨Φ₁, hΦ₁, -, hΦd₁, -⟩ :=
    HomLinear.exists_linear_of_isMonHom Q.A Q'.A Q.isAb Q'.isAb Q.L Q'.L Q.g Q'.g u u' t₁' t₂' a₁ ha₁
  obtain ⟨Φ₂, hΦ₂, -, hΦd₂, -⟩ :=
    HomLinear.exists_linear_of_isMonHom Q.A Q'.A Q.isAb Q'.isAb Q.L Q'.L Q.g Q'.g u u' t₁' t₂' b₁ hb₁
  obtain ⟨G, hG, -, hGd, -⟩ :=
    HomLinear.exists_linear_of_isMonHom Q.A Q.A Q.isAb Q.isAb Q.L Q.L Q.g Q.g u u t₁ t₂ g₁ hg₁
  have hlam₁ : LamEq Q'.L a₁ b₁ Q.L g₁ (𝟙 Q.A) :=
    lamEq_baseChange _ _ (spMap s) F.P₀.A F.P₀.A F'.P₀.A F.P₀.A Q.A Q.A Q'.A Q.A φ φ φ' φ
      hφ.2.1.1.w hφ.2.1.1.w hφ'.2.1 hφ.2.1
      F'.P₀.L F.P₀.L Q'.L Q.L F'.P₀.isLB F.P₀.isLB Q'.isLB Q.isLB hφ'.2.2 hφ.2.2 a₀ b₀ g₀ (𝟙 _) a₁ b₁ g₁ (𝟙 _)
      ea eb eg (by simp) hlam₀
  have hweil := weilEq_of_lamEq hL ℂ Q Q Q' Q a₁ b₁ g₁ (𝟙 _) ha₁ hb₁ hg₁ inferInstance hlam₁
  have hherm := (weilEq_iff_hermForm_eq hU hL Q Q Q' Q u u u' u Hm' Hm χ' χ hA' hA a₁ b₁ g₁ (𝟙 _) Φ₁ Φ₂ G
    LinearMap.id hΦ₁ hΦ₂ hG (fun z => by simp)).1 hweil
  have e₁ := map_comb s hφ.2.1 hφ'.2.1 u u' F.basis.1 F'.basis.1 hW hW' t₁' ea hΦd₁ (da M₁ hM₁ c')
  have e₂ := map_comb s hφ.2.1 hφ'.2.1 u u' F.basis.1 F'.basis.1 hW hW' t₁' eb hΦd₂ (db M₂ hM₂ c)
  have e₃ := map_comb s hφ.2.1 hφ.2.1 u u F.basis.1 F.basis.1 hW hW t₁ eg hGd (dg N hN c')
  rw [form_eq h' s Hm' W' _ hform', form_eq h s Hm W _ hform, ← e₁, ← e₂, ← e₃, hherm, LinearMap.id_apply]

theorem gram_images : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
  [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (FA : GenFib A.pol) (FB : GenFib B.pol)
  (hA : HermFam K (Fin FA.P₀.g → K)) (hB : HermFam K (Fin FB.P₀.g → K)) (f₁ f₂ : A.t.G ⟶ B.t.G)
  (M₁ M₂ : (Fin FA.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)) (g : 𝓞 E), FA.IsHerm hA → FB.IsHerm hB →
  IsMonHom f₁ → IsMonHom f₂ →
  WeilEq B.t.PP.L f₁ f₂ A.t.PP.L (A.t.act.act g) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
  FA.IsDiffOf FB f₁ M₁ → FA.IsDiffOf FB f₂ M₂ → ∀ (τ : 𝓞 E →+* 𝓞 K) (s : K →+* ℂ),
  ∀ c ∈ FA.eigLat A.t.act τ, hB.form s (M₂ c) (M₁ c) = s (τ g : K) * hA.form s c c := by
  intro hU hL E _ _ _ H K _ _ σ₁ A B FA FB hA hB f₁ f₂ M₁ M₂ g hhA hhB hf₁ hf₂ hw hM₁ hM₂ τ s c hc
  obtain ⟨r, hr, he⟩ := _root_.GlobalTheory.CM.GenFib.exists_lieRep_eigLat K A.pol FA (𝓞 E) A.t.act
  have hg : IsMonHom (A.t.act.act g) := A.t.act.hom _
  have hinj : Function.Injective (σ₁.comp (algebraMap (𝓞 K) K)) :=
    σ₁.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  have hlam := (_root_.GlobalTheory.PairingFibre.lamEq_weilEq_over_ring hL (𝓞 K) A.pol A.pol B.pol A.pol f₁ f₂ (A.t.act.act g) (𝟙 _) hf₁ hf₂ hg inferInstance ℂ
    (σ₁.comp (algebraMap (𝓞 K) K))).2 inferInstance hinj hw
  have hf := form_diff_eq_pair hU hL K A.pol FA B.pol FB hA hB f₁ f₂ (A.t.act.act g) M₁ M₂ (r g) hhA hhB hf₁ hf₂ hg
    hlam hM₁ hM₂ (hr _) s c c
  have hev : r g c = (τ g : K) • c := ((he τ c).1.1 hc).2 _
  rw [hf]
  erw [hev]
  rw [HermFam.smul_right]

theorem side (hU : ThetaUnifAV) (hL : Out.Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {K : Type} [Field K] [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (FA : GenFib A.pol)
    (FB : GenFib B.pol) (hA : HermFam K (Fin FA.P₀.g → K)) (hB : HermFam K (Fin FB.P₀.g → K)) {n : ℕ}
    (f : Fin n → (A.t.G ⟶ B.t.G)) (M : Fin n → ((Fin FA.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)))
    (g : Matrix (Fin n) (Fin n) (𝓞 E)) (τ : 𝓞 E →+* 𝓞 K) (Ω : ℝ) (hhA : FA.IsHerm hA) (hhB : FB.IsHerm hB)
    (hf : ∀ a, IsMonHom (f a))
    (hw : ∀ a b, WeilEq B.t.PP.L (f a) (f b) A.t.PP.L (A.t.act.act (g a b)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))))
    (hM : ∀ a, FA.IsDiffOf FB (f a) (M a)) (hr : latRank K (FA.eigLat A.t.act τ) = 1)
    (hi : ∀ a, Function.Injective (M a))
    (hind : iSupIndep (fun a => Submodule.span K
      (((FA.eigLat A.t.act τ).map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) _) : Set (Fin FB.P₀.g → K))))
    (hΩ : 2 * deg hA (FA.eigLat A.t.act τ) = Ω) :
    g.det ≠ 0 ∧ deg hB (⨆ a, (FA.eigLat A.t.act τ).map ((M a).restrictScalars (𝓞 K))) =
      n * (Ω / 2) - Real.log |((Algebra.norm ℚ ((g.det : 𝓞 E) : E) : ℚ) : ℝ)| / (2 * Module.finrank ℚ E) := by
  set y : Matrix (Fin n) (Fin n) K := g.map fun x => (τ x : K) with hy
  have hgr : ∀ (s : K →+* ℂ) a b, ∀ c ∈ FA.eigLat A.t.act τ,
      hB.form s (M b c) (M a c) = s (y a b) * hA.form s c c := fun s a b c hc =>
    gram_images hU hL E H K σ₁ A B FA FB hA hB (f a) (f b) (M a) (M b) (g a b) hhA hhB (hf a) (hf b) (hw a b)
      (hM a) (hM b) τ s c hc
  obtain ⟨hne, hdeg⟩ := _root_.GlobalTheory.deg_iSup_map_of_gram K _ _ hA hB n M _ y (GlobalTheory.CM.DegBound.eigLat_fg FA A.t.act τ) hr hi hind hgr
  have hdet : y.det = ((τ g.det : 𝓞 K) : K) := by
    rw [hy, show (fun x : 𝓞 E => (τ x : K)) = ⇑((algebraMap (𝓞 K) K).comp τ) from rfl, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det]
    rfl
  refine ⟨fun h0 => hne (by rw [hdet, h0, map_zero]; rfl), ?_⟩
  have hn := _root_.GlobalTheory.mean_log_norm_embeddings_ringHom E K τ g.det
  rw [hdeg, ← hΩ, hdet]
  have e : (∑ s : K →+* ℂ, Real.log ‖s ((τ g.det : 𝓞 K) : K)‖) / (2 * (Module.finrank ℚ K : ℝ)) =
      Real.log |((Algebra.norm ℚ ((g.det : 𝓞 E) : E) : ℚ) : ℝ)| / (2 * (Module.finrank ℚ E : ℝ)) := by
    rw [mul_comm (2 : ℝ), ← div_div, hn, div_div, mul_comm]
  rw [e]
  ring

theorem deg_images : CMCurve → ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q), ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ gP gQ, IsGram X gP gQ → ∀ (FP : GenFib (X.A true).pol) (FQ : GenFib (X.A false).pol) (FB : GenFib X.B.pol) (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))) (MQ : Fin q → ((Fin FQ.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))), IsDiffs FP FQ FB MP MQ → ∀ (h : HermFam K (Fin FB.P₀.g → K)), FB.IsHerm h → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → gP.det ≠ 0 ∧ gQ.det ≠ 0 ∧ deg h (subP FP FB MP τ) = p * ((logOm E χ).re / 2) - Real.log |((Algebra.norm ℚ ((gP.det : 𝓞 E) : E) : ℚ) : ℝ)| / (2 * Module.finrank ℚ E) ∧ deg h (subQ FQ FB MQ (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) = q * ((logOm E χ).re / 2) - Real.log |((Algebra.norm ℚ ((gQ.det : 𝓞 E) : E) : ℚ) : ℝ)| / (2 * Module.finrank ℚ E) := by
  intro hC hU hL hE E _ _ _ H K _ _ ρ σ₁ p q X _ χ hχ gP gQ hG FP FQ FB MP MQ hDf h hh τ hτ
  have hD : DegSt := PureDeg.degSt hC hU hL hE
  obtain ⟨hP, hhP⟩ := (LieMetric.exists_unique_isHerm hU hL K _ FP).1
  obtain ⟨hQ, hhQ⟩ := (LieMetric.exists_unique_isHerm hU hL K _ FQ).1
  have hρ : ρ ≠ 0 := fun h0 => by
    have := X.ρ_sq
    rw [h0] at this
    exact H.d_prime.ne_zero (by simpa using this)
  have hτ' : (τ.comp (H.bar : 𝓞 E →+* 𝓞 E)) H.rt = -ρ := by
    have e : (H.bar : 𝓞 E →+* 𝓞 E) H.rt = -H.rt := by simp
    rw [RingHom.comp_apply, e, map_neg, hτ]
  have hne : -ρ ≠ ρ := fun e => hρ (by
    have : (2 : 𝓞 K) * ρ = 0 := by linear_combination -e
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero)
  let FA : ∀ b, GenFib (X.A b).pol := fun b => Bool.rec (motive := fun b => GenFib (X.A b).pol) FQ FP b
  let M : ∀ j : Fin p ⊕ Fin q, (Fin (FA j.isLeft).P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K) := fun j =>
    Sum.rec (motive := fun j => (Fin (FA j.isLeft).P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)) MP MQ j
  have hM : ∀ j, (FA j.isLeft).IsDiffOf FB (X.φ j) (M j) := by
    rintro (a | a)
    exacts [hDf.1 a, hDf.2 a]
  obtain ⟨-, -, hinj, hind, -⟩ := Indep.letters_independent hU hL E H K ρ σ₁ p q X FA FB M hM
  have hrP := (_root_.GlobalTheory.CM.EigDec.eigen_decomposition E H K ρ (X.A true) FP 1 0 X.split X.typeP X.ρ_sq).1 τ
  have hrQ := (_root_.GlobalTheory.CM.EigDec.eigen_decomposition E H K ρ (X.A false) FQ 0 1 X.split X.typeM X.ρ_sq).1 (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))
  rw [if_pos hτ] at hrP
  rw [if_neg (by rw [hτ']; exact hne)] at hrQ
  have hΩP : 2 * deg hP (FP.eigLat (X.A true).t.act τ) = (logOm E χ).re := by
    have := hD E H χ hχ K ρ (X.A true) X.split X.ρ_sq X.typeP FP hP hhP τ hτ
    rw [← this, Complex.ofReal_re]
  have hΩQ := NumInh.deg_conjugate_type hD hχ X FQ hhQ hτ'
  have hindP := iSupIndep.comp (f := fun a : Fin p => ((Sum.inl a : Fin p ⊕ Fin q), τ)) hind
    (fun a b e => Sum.inl_injective (congrArg Prod.fst e))
  have hindQ := iSupIndep.comp (f := fun a : Fin q => ((Sum.inr a : Fin p ⊕ Fin q), τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) hind
    (fun a b e => Sum.inr_injective (congrArg Prod.fst e))
  obtain ⟨h1, h2⟩ := side hU hL σ₁ (X.A true) X.B FP FB hP h (fun a => phiP X a) MP gP τ _ hhP hh
    (fun a => (X.lin (Sum.inl a)).1) hG.1 hDf.1 hrP (fun a => hinj (Sum.inl a)) hindP hΩP
  obtain ⟨h3, h4⟩ := side hU hL σ₁ (X.A false) X.B FQ FB hQ h (fun a => phiQ X a) MQ gQ
    (τ.comp (H.bar : 𝓞 E →+* 𝓞 E)) _ hhQ hh (fun a => (X.lin (Sum.inr a)).1) hG.2 hDf.2 hrQ
    (fun a => hinj (Sum.inr a)) hindQ hΩQ
  exact ⟨h1, h3, h2, h4⟩

end GlobalTheory.FlatCM.ImageDeg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeAlongKodairaSpencerDeformationLift
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

open GlobalTheory.Frames

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CompHS

theorem der_fun_hor : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    {Q : FrPt Xo c K} (hQ : KSIso (psiSet H) Q) (hz : z ≫ toFlag M = X.ptY Q)
    {v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)} (hv : IsTanFrame (psiSet H) Q v)
    {zv : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)} (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b))
    {w : FrPt Xo c (DualNumber K)} (hw : IsDef Q w) {Mx : HIx Dw (psiSet H) → K}
    (hM : GlobalTheory.FlagTan.IsKS (psiSet H) Q w.x Mx) {zw : Sp (DualNumber K) ⟶ M.X} (hlw : zw ≫ toFlag M = X.ptY w), ∃ C : VIx Dw → K, ∀ (O : M.X.Opens) (g : Γ(M.X, O)) (hzw : ⊤ ≤ zw ⁻¹ᵁ O) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O),
      (evalPt zw O hzw g).snd = ∑ k, Mx k * (evalPt (zv (.inl k)) O (hzv _) g).snd +
        ∑ k, C k * (evalPt (zv (.inr k)) O (hzv _) g).snd := by
  intro E _ _ _ H Dw l Xo c Y X Z M K _ _ z ho Q hQ hz v hv zv hl w hw Mx hM zw hlw
  obtain ⟨W, zM, hzM⟩ := hQ.exists_universal
  have hWQ : FrMap (TrivSqZeroExt.fstHom c.F K (HIx Dw (psiSet H) → K)) W Q :=
    GlobalTheory.FlagTan.frMap_comp (hzM 0).1 (hzM 0).2.1 fun a => by simp
  obtain ⟨ZW, hZW⟩ := FunDer.der_dir M hz ho hWQ
  choose zz hzz using fun k : GlobalTheory.FlagTan.FIx Dw => (GlobalTheory.FlagTan.existsUnique_isVert Q (Pi.single k (1 : K))).exists
  choose q hq hqO using fun k => exists_tanLift M (hzz k).isDef hz ho
  have key : ∀ (w' : FrPt Xo c (DualNumber K)) (M' : HIx Dw (psiSet H) → K), IsDef Q w' →
      GlobalTheory.FlagTan.IsKS (psiSet H) Q w'.x M' → ∃ C : VIx Dw → K, ∀ (p : Sp (DualNumber K) ⟶ M.X),
        p ≫ toFlag M = X.ptY w' → ∀ (O : M.X.Opens) (g : Γ(M.X, O)) (hp : ⊤ ≤ p ⁻¹ᵁ O)
        (hzv : ∀ k : VIx Dw, ⊤ ≤ zv (.inr k) ⁻¹ᵁ O), ∃ hZ : ⊤ ≤ ZW ⁻¹ᵁ O,
          (evalPt p O hp g).snd = ∑ k, (evalPt ZW O hZ g).snd k * M' k +
            ∑ k, C k * (evalPt (zv (.inr k)) O (hzv k) g).snd := by
    intro w' M' hw' hM'
    obtain ⟨N, hN⟩ := (hzM M').2.1.exists_isShift hw'
      (hQ.injective hw'.isTanX (hzM M').2.1.isTanX hM' (hzM M').2.2)
    obtain ⟨p₀, hp₀, hp₀O⟩ := exists_tanLift M (hzM M').2.1 hz ho
    refine ⟨fun k => N k.toF, fun p hp O g hpO hzv => ?_⟩
    have hzO : ⊤ ≤ z ⁻¹ᵁ O := by
      rw [← FunDer.red_eq M hz ho hw' hp]
      exact FunDer.top_le_comp _ _ _ hpO
    obtain ⟨hZ, a0⟩ := hZW M' _ p₀ (hzM M').1 hp₀ O g (hp₀O O hzO)
    refine ⟨hZ, ?_⟩
    rw [FunDer.der_shift M hz ho (hzM M').2.1 hN hzz hp₀ hp hq O g (hp₀O O hzO) hpO (fun k => hqO k O hzO), a0,
      GlobalTheory.FlagTan.sum_FIx]
    congr 1
    have hz0 : ∑ k ∈ Finset.univ.filter (fun k => k ∉ Set.range GlobalTheory.FlagTan.VIx.toF),
        N k * (evalPt (q k) O (hqO k O hzO) g).snd = 0 :=
      Finset.sum_eq_zero fun k hk => by
        have hN' : ∀ σ i j, i < j → (Pi.single k (1 : K) : GlobalTheory.FlagTan.FIx Dw → K) (some ⟨σ, i, j⟩) = 0 :=
          fun σ i j hij => by
            refine Pi.single_eq_of_ne ?_ _
            rintro rfl
            exact (Finset.mem_filter.1 hk).2 ⟨⟨σ, (i, j), hij⟩, rfl⟩
        rw [FunDer.der_vert_eq_zero M hz ho (hzz k) hN' (hq k) O g _, mul_zero]
    rw [hz0, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e1 : zz k.toF = v (.inr k) :=
      (GlobalTheory.FlagTan.existsUnique_isVert Q _).unique (hzz k.toF) (hv.2 k)
    have e2 : q k.toF = zv (.inr k) := FunDer.lift_eq M (by rw [hq, hl, e1]) (hqO _ _ ho)
    rw [FunDer.evalPt_eq_of_eq e2 O _ (hzv k) g]
  obtain ⟨C, hC⟩ := key w Mx hw hM
  choose C' hC' using fun k => key _ _ (hv.1 k).1 (hv.1 k).2
  refine ⟨fun j => C j - ∑ k, Mx k * C' k j, fun O g hzw hzvO => ?_⟩
  obtain ⟨hZ, a⟩ := hC zw hlw O g hzw (fun k => hzvO _)
  have b : ∀ k, (evalPt (zv (.inl k)) O (hzvO _) g).snd =
      (evalPt ZW O hZ g).snd k + ∑ j, C' k j * (evalPt (zv (.inr j)) O (hzvO _) g).snd := fun k => by
    obtain ⟨hZ', b⟩ := hC' k (zv (.inl k)) (hl _) O g (hzvO _) (fun j => hzvO _)
    rw [b]
    simp [Pi.single_apply]
  rw [a, Finset.sum_congr rfl fun k _ => congrArg (Mx k * ·) (b k)]
  simp only [mul_add, Finset.sum_add_distrib, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum,
    mul_assoc]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (VIx Dw)))]
  simp only [mul_comm _ (Mx _)]
  ring

end GlobalTheory.CompHS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeAlongVerticalDeformationLift
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c}


open GlobalTheory.FlagTan in
theorem der_fun_ver (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw)) {K : Type} [Field K] [Algebra c.F K]
    (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    {Q : FrPt Xo c K} (hz : z ≫ toFlag M = X.ptY Q)
    {v : VIx Dw → FrPt Xo c (DualNumber K)} (hv : ∀ k : VIx Dw, IsVert Q (Pi.single k.toF (1 : K)) (v k))
    {zv : VIx Dw → (Sp (DualNumber K) ⟶ M.X)} (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b))
    {w : FrPt Xo c (DualNumber K)} {N : FIx Dw → K} (hw : IsVert Q N w)
    {zw : Sp (DualNumber K) ⟶ M.X} (hlw : zw ≫ toFlag M = X.ptY w)
    (O : M.X.Opens) (g : Γ(M.X, O)) (hzw : ⊤ ≤ zw ⁻¹ᵁ O) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O) :
    (evalPt zw O hzw g).snd = ∑ k : VIx Dw, N k.toF * (evalPt (zv k) O (hzv _) g).snd := by
  choose vp hvp using fun m : FIx Dw → K => (existsUnique_isVert Q m).exists
  obtain ⟨y₀, h₀⟩ := GlobalTheory.FlagTan.exists_frMap (cst c K) Q
  obtain ⟨W₀, hW₀⟩ := GlobalTheory.FlagTan.exists_frMap (TrivSqZeroExt.inlAlgHom c.F K (FIx Dw → K)) Q
  let n : FIx Dw → FIx Dw → K := fun k => Pi.single k 1
  obtain ⟨W, hW, -⟩ :=
    GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ W₀ _ (isUnit_unip₀ (K := K) n).unit (isUnit_det_unip n)

  have hWm : ∀ m, FrMap (dir c m) W (vp m) := fun m => by
    obtain ⟨y₁, h₁, hs⟩ := hvp m
    obtain rfl := GlobalTheory.FlagTan.frMap_unique h₁ h₀
    refine (GlobalTheory.FlagTan.frMap_iff_frChg hW (GlobalTheory.FlagTan.frMap_of_comp hW₀ h₀ fun a => by ext <;> simp)).2 ?_
    unfold IsShift at hs
    convert hs using 2 with τ
    · ext i j <;> simp [unip, n, Pi.single_apply]
    · ext <;> simp [unip₀, n, Pi.single_apply]
  have hP : ∀ m, spMap (dir c m).toRingHom ≫ X.ptY W = X.ptY (vp m) := fun m => X.ptY_frMap (hWm m)
  obtain ⟨ZW, hZf, huniq⟩ := exists_thickLift M z ho hz
    (GlobalTheory.FlagTan.frMap_comp (hWm 0) (hvp 0).isDef fun a => by simp)
  have huniq' : ∀ m (x : Sp (DualNumber K) ⟶ M.X), x ≫ toFlag M = X.ptY (vp m) →
      x = spMap (dir c m).toRingHom ≫ ZW := fun m x hx => huniq m x (hx.trans (hP m).symm)
  have ew : zw = spMap (dir c N).toRingHom ≫ ZW :=
    huniq' N zw (by rw [hlw, (existsUnique_isVert Q N).unique hw (hvp N)])
  have hZO : ⊤ ≤ ZW ⁻¹ᵁ O :=
    le_preimage_of_comp primeSpectrum_trivSqZeroExt_eq (dir c N).toRingHom
      ((spMap (red c K).toRingHom) (IsLocalRing.closedPoint K)) ZW O (ew ▸ hzw)

  have hflag : ∀ N' : FIx Dw → K, (∀ σ i j, i < j → N' (some ⟨σ, i, j⟩) = 0) → X.ptY (vp N') = X.ptY y₀ :=
    fun N' hN' => by
      obtain ⟨y₁, h₁, hs⟩ := hvp N'
      obtain rfl := GlobalTheory.FlagTan.frMap_unique h₁ h₀
      exact (X.ptY_frBor (t := fun k => oneAddEps (Multiplicative.ofAdd (diagOf N' k)))
        ((GlobalTheory.Frames.frBor_iff_frChg _ _ _).2 ⟨unip K N', fun σ i j hij => by
          simp [unip, hN' σ i j hij, hij.ne], fun _ _ => by simp [unip, oneAddEps, diagOf], hs⟩)).symm
  have h0 : ∀ j : FIx Dw, j ∉ Set.range VIx.toF → (evalPt ZW O hZO g).snd j = 0 := fun j hj => by
    have hx : ⊤ ≤ (spMap (dir c (Pi.single j 1)).toRingHom ≫ ZW) ⁻¹ᵁ O := fun s _ => hZO (Set.mem_univ _)
    have e1 := huniq 0 (spMap (dir c (Pi.single j 1)).toRingHom ≫ ZW) (by
      rw [Category.assoc, hZf, hP, hP, hflag _ (fun σ i j' hij => Pi.single_eq_of_ne (by
        rintro rfl
        exact hj ⟨⟨σ, (i, j'), hij⟩, rfl⟩) _), hflag 0 fun _ _ _ _ => rfl])
    have a1 := snd_evalPt_dir ZW O hZO (Pi.single j 1) _ hx rfl g
    have a2 := snd_evalPt_dir ZW O hZO 0 _ hx e1 g
    simpa [Pi.single_apply] using a1.symm.trans a2
  have hk : ∀ k : VIx Dw, (evalPt (zv k) O (hzv k) g).snd = (evalPt ZW O hZO g).snd k.toF := fun k => by
    rw [snd_evalPt_dir ZW O hZO _ _ _
      (huniq' _ _ ((hl k).trans (congrArg X.ptY ((existsUnique_isVert Q _).unique (hv k) (hvp _))))) g]
    simp [Pi.single_apply]
  rw [snd_evalPt_dir ZW O hZO N zw hzw ew g]
  simp only [hk]
  have hz0 : ∑ k ∈ Finset.univ.filter (fun k => k ∉ Set.range VIx.toF), (evalPt ZW O hZO g).snd k * N k = 0 :=
    Finset.sum_eq_zero fun k hk => by rw [h0 k (Finset.mem_filter.1 hk).2, zero_mul]
  rw [sum_FIx, hz0, add_zero]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

end GlobalTheory.CompHS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagNeZeroOfLinearIndependent
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt

section Lat

variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {n : ℕ}

theorem diag_ne_zero_of_linearIndependent {w : Fin n → U} {g : Matrix (Fin n) (Fin n) C}
    (hg : ∀ i j, i < j → g i j = 0) (h : LinearIndependent C fun i => ∑ j, g i j • w j) (i : Fin n) : g i i ≠ 0 := by
  have hl : LinearIndependent C g.row := LinearIndependent.of_comp (Fintype.linearCombination C w) h
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hl)
  rw [Matrix.det_of_lowerTriangular _ fun i j hij => hg i j hij] at hu
  exact Finset.prod_ne_zero_iff.1 hu.ne_zero i (Finset.mem_univ i)

theorem IsLatBasis.diag_le {v : Valuation C ℝ≥0} (hv : v.Integers O) {La : Submodule O U} {w : Fin n → U}
    {g g' : Matrix (Fin n) (Fin n) C} (hg : ∀ i j, i < j → g i j = 0) (hg' : ∀ i j, i < j → g' i j = 0)
    (h : IsLatBasis C La fun i => ∑ j, g i j • w j) (i : Fin n) (h' : ∑ j, g' i j • w j ∈ La) :
    v (g' i i) ≤ v (g i i) := by
  have hd : IsUnit g.det := lowerTri_isUnit_det g hg fun i => (diag_ne_zero_of_linearIndependent hg h.1 i).isUnit
  have e : (g' * g⁻¹) * g = g' := Matrix.nonsing_inv_mul_cancel_right _ _ hd
  have e1 : ∑ j, (g' * g⁻¹) i j • ∑ k, g j k • w k = ∑ k, g' i k • w k := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_smul, ← Matrix.mul_apply, e]
  obtain ⟨b, hb⟩ := (h.sum_mem_iff ((g' * g⁻¹) i)).1 (e1 ▸ h') i
  have e2 := lowerTri_mul_diag _ _ (lowerTri_mul _ _ hg' (lowerTri_inv g hg hd)) hg i
  rw [e] at e2
  rw [e2, map_mul, ← hb]
  exact mul_le_of_le_one_left' (hv.map_le_one b)

theorem IsLatBasis.mem {La : Submodule O U} {w : Fin n → U} (h : IsLatBasis C La w) (i : Fin n) : w i ∈ La :=
  (h.2.le (Submodule.subset_span ⟨i, rfl⟩)).1

end Lat

attribute [local instance] algPadicInt algPadicField towerPadic factPadic PadicComplexHost.isAdicComplete

end GlobalTheory.CompHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharNorm
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.FunExt GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LBCNu

open MeasureTheory

theorem distribHaarChar_norm {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k']
    [IsNonarchimedeanLocalField k'] [Algebra k k'] [FiniteDimensional k k'] [IsModuleTopology k k'] (z : k'ˣ) :
    distribHaarChar k (Units.map (Algebra.norm k : k' →* k) z) = distribHaarChar k' z := by
  let b := Module.finBasis k k'
  let e : k' ≃ₗ[k] (Fin (Module.finrank k k') → k) := b.equivFun
  let e' : k' ≃ₜ+ (Fin (Module.finrank k k') → k) :=
    { e.toAddEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }
  let M : k' ≃ₗ[k] k' := LinearEquiv.ofLinear (LinearMap.mulLeft k (z : k')) (LinearMap.mulLeft k ((z⁻¹ : k'ˣ) : k'))
    (by ext x; simp) (by ext x; simp)
  let Lz : (Fin (Module.finrank k k') → k) ≃ₗ[k] (Fin (Module.finrank k k') → k) := (e.symm.trans M).trans e
  have h1 : distribHaarChar (Fin (Module.finrank k k') → k) Lz = distribHaarChar k' z :=
    GlobalTheory.JR.ModuleNorm.distribHaarChar_transport e' z Lz (fun x => by
      show e ((z : k') * x) = e (M (e.symm (e x)))
      simp [M])
  rw [← h1, GroundTheory.Automorphic.Measures.distribHaarChar_pi_eq]
  congr 1
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe, LinearEquiv.coe_det, Lz, Algebra.norm_apply]
  symm
  show LinearMap.det (e.toLinearMap ∘ₗ M.toLinearMap ∘ₗ e.symm.toLinearMap) = _
  rw [LinearMap.det_conj]
  rfl


open GlobalTheory.SmGL GlobalTheory.SplitWeil in
theorem absPow_comp_norm {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k']
    [IsNonarchimedeanLocalField k'] [Algebra k k'] [FiniteDimensional k k'] [IsModuleTopology k k'] (t : ℂ) :
    (absPow k t).comp (Units.map (Algebra.norm k : k' →* k)) = absPow k' t := by
  ext z
  simp only [MonoidHom.comp_apply, val_absPow, nabs, distribHaarChar_norm]

end GlobalTheory.LBCNu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedLocusHomogeneousEquationsSectionsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closed_locus_homogeneous_equations_sections : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A₀ B₀ : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (fB : B₀ ⟶ Sp Rg) (N : LB A₀) (H : LB B₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H), Flat f → GlobalTheory.AbLaw.IsProjBy f → N.IsLB → ∃ (Z : Scheme.{0}) (ιZ : Z ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), IsClosedImmersion ιZ ∧ ∀ (T X' : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X' ⟶ A₀) (p : X' ⟶ T), IsPullback φ p f (g ≫ affπ Rg (mA * mB)) → (GlobalTheory.HomFixUniv.FormsOK a fB b φ p (g ≫ affπ Rg (mA * mB)) (matOf g) ↔ ∃ w : T ⟶ Z, w ≫ ιZ = g) := by
  first | (exact @GlobalTheory.FormsLocus.exists_closed_formsOK) | (exact GlobalTheory.FormsLocus.exists_closed_formsOK) | (intros; apply GlobalTheory.FormsLocus.exists_closed_formsOK <;> assumption)
end

