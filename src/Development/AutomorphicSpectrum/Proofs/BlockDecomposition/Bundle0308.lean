module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0010
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.Linear
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0042
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsGradedMapGlueD

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwCentPreservesFlag
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.FlagCent

variable {K : Type} [Field K] {n : ℕ}

theorem img_mul (g h : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    img (g * h) W = img g (img h W) := by
  simp only [img, Units.val_mul, Matrix.toLin'_mul, Submodule.map_comp]

theorem img_one (W : Submodule K (Fin n → K)) : img (1 : GL (Fin n) K) W = W := by
  simp [img]

theorem mem_img_iff (g : GL (Fin n) K) (W : Submodule K (Fin n → K)) (y : Fin n → K) :
    y ∈ img g W ↔ (g⁻¹ : GL (Fin n) K).val *ᵥ y ∈ W := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : (g⁻¹ : GL (Fin n) K).val * g.val = 1 := by rw [← Units.val_mul]; simp
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, this] using hx
  · intro h
    refine ⟨_, h, ?_⟩
    simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec]

theorem form_mulVec (σ : K →+* K) (A : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    ∑ i, σ ((A *ᵥ x) i) * y i = ∑ j, σ (x j) * ((A.map σ)ᵀ *ᵥ y) j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, transpose_apply,
    map_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem perp_img (σ : K →+* K) (g : GL (Fin n) K) (X : Submodule K (Fin n → K)) :
    perp σ (img g X) = img (thetaR σ n g) (perp σ X) := by
  ext y
  rw [mem_img_iff]
  have hinv : ((thetaR σ n g)⁻¹ : GL (Fin n) K).val = (g.val.map σ)ᵀ := rfl
  rw [hinv]
  constructor
  · intro h x hx
    rw [← form_mulVec]
    exact h _ ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    rw [Matrix.toLin'_apply, form_mulVec]
    exact h x hx

theorem le_perp_perp (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) (W : Submodule K (Fin n → K)) :
    W ≤ perp σ (perp σ W) := fun z hz y hy => by
  have h2 := congrArg σ (hy z hz)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hσ, map_zero] at h2
  simpa [mul_comm] using h2

theorem perp_perp (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) (W : Submodule K (Fin n → K)) :
    perp σ (perp σ W) = W := by
  refine le_antisymm (fun z hz => ?_) (le_perp_perp σ hσ W)
  by_contra hn
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_notMem hn
  let a : Fin n → K := fun i => f fun j => if i = j then 1 else 0
  have hfa : ∀ x, f x = ∑ i, x i * a i := fun x => by
    rw [LinearMap.pi_apply_eq_sum_univ f x]; rfl
  have hy : (fun i => σ (a i)) ∈ perp σ W := fun x hx => by
    have h0 : f x = 0 := hf hx
    rw [hfa] at h0
    have := congrArg σ h0
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, map_mul, map_zero] using this
  have h1 := hz _ hy
  simp only [hσ] at h1
  exact hf0 (by rw [hfa]; simpa [mul_comm] using h1)

theorem perpD_perpD (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) (d : GL (Fin n) K)
    (W : Submodule K (Fin n → K)) :
    perpD σ d (perpD σ d W) = img (d * thetaR σ n d) W := by
  simp only [perpD]
  rw [perp_img, perp_perp σ hσ, img_mul]

theorem thetaR_thetaR (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) (g : GL (Fin n) K) :
    thetaR σ n (thetaR σ n g) = g := by
  apply Units.ext
  rw [thetaR_val]
  have hinv : ((thetaR σ n g)⁻¹ : GL (Fin n) K).val = (g.val.map σ)ᵀ := rfl
  rw [hinv]
  ext i j
  simp [hσ]

theorem commute_norm (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {d t : GL (Fin n) K}
    (ht : t ∈ twCent (thetaR σ n) d) :
    t * (d * thetaR σ n d) = (d * thetaR σ n d) * t := by
  have h1 : t⁻¹ * d * thetaR σ n t = d := ht
  have h2 : thetaR σ n d = (thetaR σ n t)⁻¹ * thetaR σ n d * t := by
    conv_lhs => rw [← h1]
    rw [map_mul, map_mul, map_inv, thetaR_thetaR σ hσ]
  have h3 : t * d = d * thetaR σ n t := by
    calc t * d = t * (t⁻¹ * d * thetaR σ n t) := by rw [h1]
      _ = d * thetaR σ n t := by group
  have h4 : thetaR σ n t * thetaR σ n d = thetaR σ n d * t := by
    calc thetaR σ n t * thetaR σ n d
        = thetaR σ n t * ((thetaR σ n t)⁻¹ * thetaR σ n d * t) := by rw [← h2]
      _ = thetaR σ n d * t := by group
  rw [← mul_assoc, h3, mul_assoc, h4, ← mul_assoc]

theorem map_le_of_commute [IsAlgClosed K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f t : Module.End K V) (hs : LinearMap.charpoly f |>.Separable)
    (hc : Commute f t) (W : Submodule K V) (hW : ∀ x ∈ W, f x ∈ W) : W.map t ≤ W := by
  have hW' : W = ⨆ μ, W ⊓ f.maxGenEigenspace μ := by
    have h := Submodule.inf_iSup_genEigenspace (p := W) (f := f) hW ⊤
    rw [show ⨆ μ, f.genEigenspace μ ⊤ = ⊤ from Module.End.iSup_maxGenEigenspace_eq_top f,
      inf_top_eq] at h
    exact h
  rw [Submodule.map_le_iff_le_comap]
  conv_lhs => rw [hW']
  refine iSup_le fun μ x hx => ?_
  have hdim : Module.finrank K (f.maxGenEigenspace μ) ≤ 1 := by
    rw [LinearMap.finrank_maxGenEigenspace_eq]
    exact Polynomial.rootMultiplicity_le_one_of_separable hs μ
  have htx : t x ∈ f.maxGenEigenspace μ := Module.End.mapsTo_maxGenEigenspace_of_comm hc μ hx.2
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨v, hv⟩ := finrank_le_one_iff.1 hdim
  obtain ⟨a, ha⟩ := hv ⟨x, hx.2⟩
  obtain ⟨b, hb⟩ := hv ⟨t x, htx⟩
  have ha' : a • (v : V) = x := congrArg Subtype.val ha
  have hb' : b • (v : V) = t x := congrArg Subtype.val hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hx0 (by simpa using ha'.symm)
  change t x ∈ W
  rw [← hb', show b • (v : V) = (b / a) • x by rw [← ha', smul_smul, div_mul_cancel₀ _ ha0]]
  exact W.smul_mem _ hx.1

theorem img_eq_of_commute [IsAlgClosed K] (γ t : GL (Fin n) K) (hs : γ.val.charpoly.Separable)
    (hc : t * γ = γ * t) (W : Submodule K (Fin n → K)) (hW : img γ W = W) : img t W = W := by
  have key : ∀ s : GL (Fin n) K, s * γ = γ * s → img s W ≤ W := fun s hcs => by
    refine map_le_of_commute (Matrix.toLin' γ.val) (Matrix.toLin' s.val)
      (by rwa [Matrix.charpoly_toLin']) ?_ W fun x hx => ?_
    · change Matrix.toLin' γ.val * Matrix.toLin' s.val = Matrix.toLin' s.val * Matrix.toLin' γ.val
      rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul,
        ← Units.val_mul, ← Units.val_mul, hcs]
    · rw [← hW]; exact ⟨x, hx, rfl⟩
  refine le_antisymm (key t hc) ?_
  have hinv : t⁻¹ * γ = γ * t⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul, hc]
  calc W = img t (img t⁻¹ W) := by rw [← img_mul, mul_inv_cancel, img_one]
    _ ≤ img t W := Submodule.map_mono (key t⁻¹ hinv)

theorem twCent_preserves_flag [IsAlgClosed K] (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x)
    (d : GL (Fin n) K) (hd : (d * thetaR σ n d).val.charpoly.Separable)
    (W₁ W₂ : Submodule K (Fin n → K)) (h₁ : perpD σ d W₁ = W₂) (h₂ : perpD σ d W₂ = W₁)
    {t : GL (Fin n) K} (ht : t ∈ twCent (thetaR σ n) d) : img t W₁ = W₁ ∧ img t W₂ = W₂ := by
  have hc := commute_norm σ hσ ht
  refine ⟨img_eq_of_commute _ t hd hc _ ?_, img_eq_of_commute _ t hd hc _ ?_⟩
  · rw [← perpD_perpD σ hσ, h₁, h₂]
  · rw [← perpD_perpD σ hσ, h₂, h₁]

end GlobalTheory.CompanionTheory.FlagCent
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedIdealPowerLeSections
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE

attribute [local instance] algebraOfOver

lemma toFunctions_top_eq {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] (a : A) :
    toFunctions (X := X) (A := A) ⊤ a = algebraMap A Γ(X, ⊤) a := by
  change (X.presheaf.map (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤).op).hom _ = _
  rw [show (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ from rfl, op_id, X.presheaf.map_id]
  rfl

lemma twist_map_smulHom_app {X : Scheme.{0}} (L : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (P : X.Modules)
    (r : Γ(X, ⊤)) (c : Γ(GlobalTheory.twist P L, ⊤)) :
    (GlobalTheory.Twist.map L (GroundTheory.Arith.SchemeCoh.smulHom P r)).app ⊤ c = r • c := by
  apply GlobalTheory.Twist.sec_ext
  intro i
  rw [GlobalTheory.Twist.coord_map_app, GroundTheory.Arith.SchemeCoh.smulHom_app_apply, GlobalTheory.Twist.coord_smul]

lemma smul_mem_twSecs {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) (P : X.Modules) (m : ℕ)
    {a : A} (ha : a ∈ I ^ m) (c : Γ(GlobalTheory.twistZ P H n, ⊤)) :
    toFunctions (X := X) (A := A) ⊤ a • c ∈ twSecs H n (powSub I P m) := by
  let g : P ⟶ (powSub I P m : X.Modules) :=
    idealPowOfMem I P a ha ≫ (Subobject.underlyingIso (idealPowι I P m)).inv
  have hg : g ≫ (powSub I P m).arrow = GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a) := by
    simp only [g, powSub, Category.assoc]
    rw [← Subobject.underlyingIso_hom_comp_eq_mk, Iso.inv_hom_id_assoc, idealPowOfMem_ι]
  refine ⟨(GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) g).app ⊤ c, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, ← GlobalTheory.Twist.map_comp, hg,
    twist_map_smulHom_app, toFunctions_top_eq]

def twSecsSub {X : Scheme.{0}} (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) {P : X.Modules}
    (S : Subobject P) : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤) where
  carrier := twSecs H n S
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ _ _⟩
  zero_mem' := ⟨0, map_zero _⟩
  smul_mem' := by
    rintro r _ ⟨x, rfl⟩
    exact ⟨r • x, Scheme.Modules.Hom.app_smul _ _ _⟩

theorem twPow_subset_twSecs : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H →
    ∀ {P : X.Modules}, IsCoherent P → ∀ (n : ℤ) (m : ℕ),
      twPow I H n P m ⊆ twSecs H n (powSub I P m) := by
  intro A _ _ I X _ H _ P _ n m
  have key : (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ m) • ⊤ :
      Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) ≤ twSecsSub H n (powSub I P m) := by
    rw [Submodule.smul_le]
    intro r hr c _
    induction hr using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact smul_mem_twSecs I H n P m ha c
    | zero => rw [zero_smul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [add_smul]; exact Submodule.add_mem _ hx hy
    | smul x y _ hy => rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ _ hy
  exact key

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSectionsCauchyLimit
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

attribute [local instance] algebraOfOver

theorem exists_limit_of_finite {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] (I : Ideal A) (hI : IsPrecomplete I A) (f : ℕ → M)
    (hf : ∀ m, f m - f (m + 1) ∈ (I ^ m • ⊤ : Submodule A M)) :
    ∃ L, ∀ m, f m - L ∈ (I ^ m • ⊤ : Submodule A M) :=
  _root_.UpperTheory.Reformulated.B.LimitOfFinite.exists_limit_of_finite I hI f hf

theorem finite_twisted_sections {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X)
    (hH : GlobalTheory.IsAmpleLB H) {P : X.Modules} (hP : IsCoherent P) (n : ℤ)
    [Module A Γ(GlobalTheory.twistZ P H n, ⊤)]
    (hs : ∀ (a : A) (x : Γ(GlobalTheory.twistZ P H n, ⊤)), a • x = algebraMap A Γ(X, ⊤) a • x) :
    Module.Finite A Γ(GlobalTheory.twistZ P H n, ⊤) := by
  haveI : GlobalTheory.QCoh.IsFiniteQC P := ⟨hP.1, hP.2⟩
  haveI : GlobalTheory.QCoh.IsFiniteQC (GlobalTheory.twistZ P H n) :=
    GlobalTheory.Twist.isFiniteQC_twist (F := P) (GlobalTheory.Twist.isLB_lbZPow hH.isLB n)
  have h0 : Module.Finite A (GlobalTheory.coh (GlobalTheory.twistZ P H n) 0) :=
    GlobalTheory.IsAmpleLB.finite_coh (R := A) (f := X ↘ Spec (.of A)) (fun _ => rfl) _ hH 0
  exact Module.Finite.equiv ((GlobalTheory.cohOn.zeroEquiv A (GlobalTheory.twistZ P H n) ⊤).trans
    (GlobalTheory.sectionsOn.equivOfSMul A (GlobalTheory.twistZ P H n) ⊤ fun a x => by
      rw [hs, GlobalTheory.restrictGlobal_top]))

theorem exists_limit_twPow : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ (n : ℤ) (f : ℕ → Γ(GlobalTheory.twistZ P H n, ⊤)), (∀ m, f m - f (m + 1) ∈ twPow I H n P m) → ∃ L : Γ(GlobalTheory.twistZ P H n, ⊤), ∀ m, f m - L ∈ twPow I H n P m := by
  intro A _ _ I hI X _ _ H hH P hP n f hf
  letI : Module A Γ(GlobalTheory.twistZ P H n, ⊤) := Module.compHom _ (algebraMap A Γ(X, ⊤))
  haveI : IsScalarTower A Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤) :=
    ⟨fun a r x => by
      change (a • r) • x = algebraMap A Γ(X, ⊤) a • (r • x)
      rw [Algebra.smul_def, mul_smul]⟩
  haveI := finite_twisted_sections (A := A) H hH hP n (fun _ _ => rfl)
  have hmem : ∀ (m : ℕ) (y : Γ(GlobalTheory.twistZ P H n, ⊤)),
      y ∈ twPow I H n P m ↔ y ∈ (I ^ m • ⊤ : Submodule A Γ(GlobalTheory.twistZ P H n, ⊤)) := by
    intro m y
    have hfun : toFunctions (X := X) (A := A) ⊤ = algebraMap A Γ(X, ⊤) := by
      ext a
      simp [toFunctions, restrictTop]
    have h := Ideal.smul_restrictScalars (R := A) (S := Γ(X, ⊤))
      (M := Γ(GlobalTheory.twistZ P H n, ⊤)) (I ^ m) ⊤
    rw [Submodule.restrictScalars_top] at h
    rw [← h]
    simp only [twPow, hfun]
    rfl
  obtain ⟨L, hL⟩ := exists_limit_of_finite I hI.toIsPrecomplete f fun m => (hmem m _).1 (hf m)
  exact ⟨L, fun m => (hmem m _).2 (hL m)⟩

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoBasesComparison
section
namespace GlobalTheory.CompanionTheory.LinAlg

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

variable {K : Type} [Field K] {n : ℕ}

theorem exists_li_span (S : Submodule K (Fin n → K)) :
    ∃ (a : ℕ) (f : Fin a → Fin n → K), LinearIndependent K f ∧ Submodule.span K (Set.range f) = S := by
  let b := Module.finBasis K S
  refine ⟨Module.finrank K S, S.subtype ∘ b, ?_, ?_⟩
  · exact b.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  · rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]

theorem exists_compl_le {I W : Submodule K (Fin n → K)} (h : I ≤ W) :
    ∃ P : Submodule K (Fin n → K), P ≤ W ∧ I ⊔ P = W ∧ Disjoint I P := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (I.comap W.subtype)
  have hI : (I.comap W.subtype).map W.subtype = I := by
    rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr h
  refine ⟨Q.map W.subtype, Submodule.map_subtype_le W Q, ?_, ?_⟩
  · rw [← hI, ← Submodule.map_sup, hQ.sup_eq_top, Submodule.map_subtype_top]
  · rw [← hI]
    exact Submodule.disjoint_map W.injective_subtype hQ.disjoint

theorem transpose_fromCols_two {ι κ : Type} (f : ι → Fin n → K) (g : κ → Fin n → K) :
    (fromCols (of f)ᵀ (of g)ᵀ)ᵀ = of (Sum.elim f g) := by
  ext i j
  rcases i with i | i <;> rfl

theorem transpose_fromCols_three {ι κ μ : Type} (f : ι → Fin n → K) (g : κ → Fin n → K)
    (h : μ → Fin n → K) :
    (fromCols (of f)ᵀ (fromCols (of g)ᵀ (of h)ᵀ))ᵀ = of (Sum.elim f (Sum.elim g h)) := by
  ext i j
  rcases i with i | i | i <;> rfl

theorem span_elim {ι κ : Type} (f : ι → Fin n → K) (g : κ → Fin n → K) :
    Submodule.span K (Set.range (Sum.elim f g)) =
      Submodule.span K (Set.range f) ⊔ Submodule.span K (Set.range g) := by
  rw [Set.Sum.elim_range, Submodule.span_union]

theorem twoBases : TwoBases := by
  intro K _ n W W'
  obtain ⟨P, hPW, hIP, hdP⟩ := exists_compl_le (inf_le_left : W ⊓ W' ≤ W)
  obtain ⟨Q, hQW, hIQ, hdQ⟩ := exists_compl_le (inf_le_right : W ⊓ W' ≤ W')
  obtain ⟨a, f, hf, hfs⟩ := exists_li_span (W ⊓ W')
  obtain ⟨b, g, hg, hgs⟩ := exists_li_span P
  obtain ⟨c, h, hh, hhs⟩ := exists_li_span Q
  have hPQ : Disjoint P Q := by
    rw [Submodule.disjoint_def]
    intro x hxP hxQ
    exact (Submodule.disjoint_def.mp hdP) x (Submodule.mem_inf.mpr ⟨hPW hxP, hQW hxQ⟩) hxP
  have hIPQ : Disjoint (W ⊓ W') (P ⊔ Q) := by
    rw [Submodule.disjoint_def]
    intro x hxI hx
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hx
    have hqI : q ∈ W ⊓ W' := by
      refine Submodule.mem_inf.mpr ⟨?_, hQW hq⟩
      have hq' : q = (p + q) - p := by abel
      rw [hq']
      exact W.sub_mem (Submodule.mem_inf.mp hxI).1 (hPW hp)
    have hq0 : q = 0 := (Submodule.disjoint_def.mp hdQ) q hqI hq
    subst hq0
    rw [add_zero] at hxI ⊢
    exact (Submodule.disjoint_def.mp hdP) p hxI hp
  have e2 : ((of f)ᵀ.fromCols (of g)ᵀ)ᵀ = Sum.elim f g := transpose_fromCols_two f g
  have e2' : ((of f)ᵀ.fromCols (of h)ᵀ)ᵀ = Sum.elim f h := transpose_fromCols_two f h
  have e3 : ((of f)ᵀ.fromCols ((of g)ᵀ.fromCols (of h)ᵀ))ᵀ = Sum.elim f (Sum.elim g h) :=
    transpose_fromCols_three f g h
  have e1 : ((of f)ᵀ)ᵀ = f := transpose_transpose (of f)
  refine ⟨a, b, c, (of f)ᵀ, (of g)ᵀ, (of h)ᵀ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e3]
    refine hf.sum_type (hg.sum_type hh ?_) ?_
    · rw [hgs, hhs]; exact hPQ
    · rw [hfs, span_elim, hgs, hhs]; exact hIPQ
  · rw [e1]; exact hfs
  · rw [e2, span_elim, hfs, hgs, hIP]
  · rw [e2', span_elim, hfs, hhs, hIQ]
  · rw [e3, span_elim, span_elim, hfs, hgs, hhs, sup_sup_distrib_left, hIP, hIQ]

end GlobalTheory.CompanionTheory.LinAlg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.XProdPowSmulMemRangeResIter
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

theorem xProd_pow_smul_mem_range_res_iter : ∀ (ι : Type) [LinearOrder ι] (A : Type) [CommRing A] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S'), (∀ S (h : S ⊆ S) a, res S S h a = a) → (∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a) → (∀ (S : Finset ι) (j : ι) (b : P (insert j S)), S.Nonempty → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • b ∈ LinearMap.range (res S (insert j S) (Finset.subset_insert j S))) → (∀ (T S : Finset ι) (b : P (S ∪ T)), S.Nonempty → ∃ l : ℕ, xProd A T ^ l • b ∈ LinearMap.range (res S (S ∪ T) Finset.subset_union_left)) := by
  intro ι _ A _ P _ _ res hid hcomp hstep
  have hA : ∀ (S0 U : Finset ι) (h : S0 ⊆ U) (j : ι), U ⊆ insert j S0 → ∀ b : P U, S0.Nonempty →
      ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • b ∈ LinearMap.range (res S0 U h) := by
    intro S0 U h j hU b hS0
    by_cases hj : j ∈ U
    · obtain rfl : U = insert j S0 := subset_antisymm hU (Finset.insert_subset hj h)
      exact hstep S0 j b hS0
    · have hUS : U ⊆ S0 := by
        intro x hx
        rcases Finset.mem_insert.mp (hU hx) with hx' | hx'
        · subst hx'
          exact absurd hx hj
        · exact hx'
      obtain rfl : U = S0 := subset_antisymm hUS h
      exact ⟨0, LinearMap.mem_range.mpr ⟨b, by rw [hid, pow_zero, one_smul]⟩⟩
  have hQ : ∀ T : Finset ι, ∀ (S U : Finset ι) (h : S ⊆ U), U ⊆ S ∪ T → ∀ b : P U, S.Nonempty →
      ∃ l : ℕ, xProd A T ^ l • b ∈ LinearMap.range (res S U h) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro S U h hU b hS
      obtain rfl : U = S := subset_antisymm (by simpa using hU) h
      exact ⟨0, LinearMap.mem_range.mpr ⟨b, by rw [hid, pow_zero, one_smul]⟩⟩
    | insert j T hj ih =>
      intro S U h hU b hS
      have hSV : S ⊆ S ∪ U.erase j := Finset.subset_union_left
      have hVU : S ∪ U.erase j ⊆ U := Finset.union_subset h (Finset.erase_subset j U)
      have hUV : U ⊆ insert j (S ∪ U.erase j) := by
        intro x hx
        by_cases hxj : x = j
        · subst hxj
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hxj, hx⟩))
      have hVT : S ∪ U.erase j ⊆ S ∪ T := by
        intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact Finset.mem_union_left _ hx
        · obtain ⟨hxj, hxU⟩ := Finset.mem_erase.mp hx
          rcases Finset.mem_union.mp (hU hxU) with h1 | h1
          · exact Finset.mem_union_left _ h1
          · rcases Finset.mem_insert.mp h1 with h2 | h2
            · exact absurd h2 hxj
            · exact Finset.mem_union_right _ h2
      have hVne : (S ∪ U.erase j).Nonempty := hS.mono hSV
      obtain ⟨k, hk⟩ := hA (S ∪ U.erase j) U hVU j hUV b hVne
      obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hk
      obtain ⟨l, hl⟩ := ih S (S ∪ U.erase j) hSV hVT c hS
      obtain ⟨d, hd⟩ := LinearMap.mem_range.mp hl
      refine ⟨k + l, ?_⟩
      have hmem : xProd A T ^ l • (MvPolynomial.X j : MvPolynomial ι A) ^ k • b ∈
          LinearMap.range (res S U h) := by
        refine LinearMap.mem_range.mpr ⟨d, ?_⟩
        rw [← hc, ← (res (S ∪ U.erase j) U hVU).map_smul, ← hd, hcomp]
      have heq : xProd A (insert j T) ^ (k + l) • b =
          ((MvPolynomial.X j : MvPolynomial ι A) ^ l * xProd A T ^ k) •
            (xProd A T ^ l • (MvPolynomial.X j : MvPolynomial ι A) ^ k • b) := by
        rw [smul_smul, smul_smul]
        congr 1
        simp only [GlobalTheory.xProd, Finset.prod_insert hj]
        ring
      rw [heq]
      exact Submodule.smul_mem _ _ hmem
  intro T S b hS
  exact hQ T S (S ∪ T) Finset.subset_union_left (Finset.Subset.refl _) b hS

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue
end

