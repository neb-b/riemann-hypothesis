module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0005
public import GroundTheory.AutomorphicForms.GKModules.Casimir
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
public import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
public import GroundTheory.AutomorphicForms.Bundle0015
public import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0354
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0338
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0350

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryTranslationInvariantPTorsion
section
set_option autoImplicit false

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

namespace PDivGroup

variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

theorem lTensor_transl_comul (n : ℕ) (x : G.A (n + 1)) :
    (G.transl n).toLinearMap.lTensor (G.A (n + 1)) (comul (R := R) x) =
      TensorProduct.assoc R _ _ _ ((comul (R := R)).rTensor (G.A 1) (G.transl n x)) := by
  have h1 : (G.transl n).toLinearMap =
      (G.resOne n : G.A (n + 1) →ₗ[R] G.A 1).lTensor _ ∘ₗ comul :=
    LinearMap.ext fun a => G.transl_apply n a
  have h2 : ∀ t : (G.A (n + 1) ⊗[R] G.A (n + 1)) ⊗[R] G.A (n + 1),
      ((G.resOne n : G.A (n + 1) →ₗ[R] G.A 1).lTensor _).lTensor _ (TensorProduct.assoc R _ _ _ t) =
        TensorProduct.assoc R _ _ _ ((G.resOne n : G.A (n + 1) →ₗ[R] G.A 1).lTensor _ t) := by
    intro t
    induction t with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul u c =>
      induction u with
      | add x y hx hy => simp only [add_tmul, map_add (f := _), hx, hy]
      | tmul a b => simp
  rw [h1, LinearMap.lTensor_comp_apply, ← coassoc_apply, h2, transl_apply]
  congr 1
  generalize comul (R := R) x = t
  induction t with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a b => simp

theorem lTensor_transl_sub_cobOne (n : ℕ) (x : G.A (n + 1)) (b : G.A 1)
    (h : G.transl n x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b) :
    ((G.transl n).toLinearMap - (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).lTensor
      (G.A (n + 1)) (cobOne R (G.A (n + 1)) x) = 0 := by
  have h1 : ∀ t : G.A (n + 1) ⊗[R] G.A (n + 1), TensorProduct.assoc R _ _ _ (t ⊗ₜ (1 : G.A 1)) =
      ((TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).lTensor _ t := fun t => by
    induction t with
    | tmul a b => simp
    | add x y hx hy => simp only [add_tmul, map_add (f := _), hx, hy]
  have h2 : comul (R := R) (1 : G.A (n + 1)) = 1 ⊗ₜ 1 := by simp [Algebra.TensorProduct.one_def]
  have h3 : G.transl n 1 = 1 ⊗ₜ 1 := by rw [map_one, Algebra.TensorProduct.one_def]
  rw [LinearMap.lTensor_sub, LinearMap.sub_apply, cobOne_apply]
  simp only [map_sub, lTensor_transl_comul, h, map_add (f := _), LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul, h1, h2, h3, AlgHom.toLinearMap_apply, LinearMap.flip_apply, mk_apply,
    assoc_tmul, tmul_add]
  abel

theorem cobOne_transl_invariant {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ)
    (x : G.A (n + 1)) (b : G.A 1) (h : G.transl n x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b) :
    ((G.transl n).toLinearMap - (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).rTensor
      (G.A (n + 1)) (cobOne R (G.A (n + 1)) x) = 0 ∧
    ((G.transl n).toLinearMap - (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).lTensor
      (G.A (n + 1)) (cobOne R (G.A (n + 1)) x) = 0 := by
  have h2 := G.lTensor_transl_sub_cobOne n x b h
  refine ⟨?_, h2⟩
  rw [← (mem_symCocycles.1 (cobOne_mem x)).2, LinearMap.rTensor_comm, h2, map_zero]

end PDivGroup

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOfSqZeroAgreePairs
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroAgree

open GlobalTheory.MulUnramified

variable {C C₀ : Type} [CommRing C] [CommRing C₀] (π : C →+* C₀)

lemma spMap_surjective (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = 0) :
    Function.Surjective (spMap π) := by
  intro (p : PrimeSpectrum C)
  change p ∈ Set.range (PrimeSpectrum.comap π)
  rw [range_comap_of_surjective _ _ hπ, PrimeSpectrum.mem_zeroLocus]
  intro a ha
  refine p.isPrime.mem_of_pow_mem 2 ?_
  have : a ^ 2 ∈ RingHom.ker π ^ 2 := Ideal.pow_mem_pow ha 2
  rw [hsq, Submodule.zero_eq_bot, Ideal.mem_bot] at this
  rw [this]
  exact zero_mem _

lemma preimage_eq_of_agree (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = 0)
    {X Y : Over (Sp C)} {f f' : X ⟶ Y}
    (h : ∀ (T₀ : Over (Sp C₀)) (y : Over.mk (T₀.hom ≫ spMap π) ⟶ X), y ≫ f = y ≫ f')
    (V : Y.left.Opens) : f.left ⁻¹ᵁ V = f'.left ⁻¹ᵁ V := by
  have hs : Surjective (spMap π) := ⟨spMap_surjective π hπ hsq⟩
  have hf : Surjective (pullback.fst X.hom (spMap π)) := inferInstance
  have e := congrArg (·.left) (h (Over.mk (pullback.snd X.hom (spMap π)))
    (Over.homMk (pullback.fst X.hom (spMap π)) pullback.condition))
  simp only [Over.comp_left, Over.homMk_left] at e
  exact preimage_eq _ hf.surj e V

noncomputable def alg (X : Over (Sp C)) (V : X.left.Opens) : C →+* Γ(X.left, V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ X.hom.appLE ⊤ V le_top).hom

lemma fromSpec_over (X : Over (Sp C)) {V : X.left.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec ≫ X.hom = spMap (alg X V) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec X.hom (isAffineOpen_top (Spec (CommRingCat.of C))) hV
    (le_top : V ≤ X.hom ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [← h, alg, spMap, CommRingCat.ofHom_hom, Spec.map_comp]

lemma appLE_alg {X Y : Over (Sp C)} (f : X ⟶ Y) (V : Y.left.Opens) (V' : X.left.Opens)
    (hf : V' ≤ f.left ⁻¹ᵁ V) (c : C) : f.left.appLE V V' hf (alg Y V c) = alg X V' c := by
  simp only [alg, CommRingCat.hom_comp, RingHom.comp_apply]
  exact comp_appLE_apply f.left Y.hom (Over.w f) _ _ _ _ _ _ _

lemma sub_mem (hπ : Function.Surjective π) {X Y : Over (Sp C)} {f f' : X ⟶ Y}
    (h : ∀ (T₀ : Over (Sp C₀)) (y : Over.mk (T₀.hom ≫ spMap π) ⟶ X), y ≫ f = y ≫ f')
    {V : Y.left.Opens} (hV : IsAffineOpen V) {V' : X.left.Opens} (hV' : IsAffineOpen V')
    (hf : V' ≤ f.left ⁻¹ᵁ V) (hf' : V' ≤ f'.left ⁻¹ᵁ V) (s : Γ(Y.left, V)) :
    f.left.appLE V V' hf s - f'.left.appLE V V' hf' s ∈ (RingHom.ker π).map (alg X V') := by
  set J := (RingHom.ker π).map (alg X V')
  let q : Γ(X.left, V') →+* Γ(X.left, V') ⧸ J := Ideal.Quotient.mk J
  let ψ : C₀ →+* Γ(X.left, V') ⧸ J :=
    (Ideal.quotientMap J (alg X V') Ideal.le_comap_map).comp
      (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom
  have hψ : ψ.comp π = q.comp (alg X V') := by
    ext c
    have e : (RingHom.quotientKerEquivOfSurjective hπ).symm (π c) = Ideal.Quotient.mk _ c :=
      (RingEquiv.symm_apply_eq _).mpr rfl
    simp only [ψ, q, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e,
      Ideal.quotientMap_mk]
  let y : Over.mk ((Over.mk (spMap ψ)).hom ≫ spMap π) ⟶ X :=
    Over.homMk (spMap q ≫ hV'.fromSpec) (by
      rw [Category.assoc, fromSpec_over]
      simp only [Over.mk_hom, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ])
  have e := congrArg (·.left) (h (Over.mk (spMap ψ)) y)
  simp only [y, Over.comp_left, Over.homMk_left, Category.assoc] at e
  rw [← hV.SpecMap_appLE_fromSpec f.left hV' hf, ← hV.SpecMap_appLE_fromSpec f'.left hV' hf',
    ← Category.assoc, ← Category.assoc, cancel_mono, spMap, ← Spec.map_comp, ← Spec.map_comp,
    Spec.map_inj] at e
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  exact congr($e s)

lemma eq_on_map {B R : Type} [CommRing B] [CommRing R] (I : Ideal C) (hI : I ^ 2 = 0)
    (φB : C →+* B) (φR : C →+* R) (β β' : B →+* R) (hβ : β.comp φB = φR) (hβ' : β'.comp φB = φR)
    (hd : ∀ b, β b - β' b ∈ I.map φR) {x : B} (hx : x ∈ I.map φB) : β x = β' x := by
  have hJ : I.map φR * I.map φR = ⊥ := by
    rw [← Ideal.map_mul, ← pow_two, hI, Submodule.zero_eq_bot, Ideal.map_bot]
  suffices β x = β' x ∧ β x ∈ I.map φR from this.1
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    rw [← RingHom.comp_apply β, hβ, ← RingHom.comp_apply β', hβ']
    exact ⟨rfl, Ideal.mem_map_of_mem _ hc⟩
  | zero => simp
  | add x y _ _ hx hy =>
    exact ⟨by simp only [map_add, hx.1, hy.1], by simpa only [map_add] using add_mem hx.2 hy.2⟩
  | smul a x _ hx =>
    refine ⟨?_, ?_⟩
    · rw [smul_eq_mul, map_mul, map_mul, ← hx.1, ← sub_eq_zero, ← sub_mul, ← Ideal.mem_bot, ← hJ]
      exact Ideal.mul_mem_mul (hd a) hx.2
    · rw [smul_eq_mul, map_mul]
      exact Ideal.mul_mem_left _ _ hx.2

end GlobalTheory.SqZeroAgree

namespace GlobalTheory


open MulUnramified SqZeroAgree in
theorem comp_eq_of_sqZero_agree : ∀ (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀),
    Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (K G : Over (Sp C)) (g g' : K ⟶ G),
    (∀ (T₀ : Over (Sp C₀)) (y : Over.mk (T₀.hom ≫ spMap π) ⟶ K), y ≫ g = y ≫ g') →
    ∀ (T : Over (Sp C)) (w w' : T ⟶ K),
    (∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ T), j ≫ w = j ≫ w') →
    w' ≫ g = w' ≫ g' → w ≫ g = w ≫ g' := by
  intro C C₀ _ _ π hπ hsq K G g g' hg T w w' hw h'
  apply Over.OverMorphism.ext
  simp only [Over.comp_left]
  refine Scheme.hom_ext_of_forall _ _ fun t ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, htV, -⟩ :=
    G.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g.left (w.left t))) isOpen_univ
  obtain ⟨_, ⟨V', hV', rfl⟩, htV', hV'V : V' ≤ g.left ⁻¹ᵁ V⟩ :=
    K.left.isBasis_affineOpens.exists_subset_of_mem_open (a := w.left t) (u := g.left ⁻¹ᵁ V) htV
      (TopologicalSpace.Opens.isOpen _)
  obtain ⟨_, ⟨W, hW, rfl⟩, htW, hWV' : W ≤ w.left ⁻¹ᵁ V'⟩ :=
    T.left.isBasis_affineOpens.exists_subset_of_mem_open (a := t) (u := w.left ⁻¹ᵁ V') htV'
      (TopologicalSpace.Opens.isOpen _)
  have hV'V₂ : V' ≤ g'.left ⁻¹ᵁ V := preimage_eq_of_agree π hπ hsq hg V ▸ hV'V
  have hWV'₂ : W ≤ w'.left ⁻¹ᵁ V' := preimage_eq_of_agree π hπ hsq hw V' ▸ hWV'
  refine ⟨W, htW, ?_⟩
  have key : ∀ s, w.left.appLE V' W hWV' (g.left.appLE V V' hV'V s) =
      w.left.appLE V' W hWV' (g'.left.appLE V V' hV'V₂ s) := by
    intro s
    have hx := sub_mem π hπ hg hV hV' hV'V hV'V₂ s
    have e := eq_on_map (RingHom.ker π) hsq (alg K V') (alg T W) (w.left.appLE V' W hWV').hom
      (w'.left.appLE V' W hWV'₂).hom (RingHom.ext (appLE_alg w V' W hWV'))
      (RingHom.ext (appLE_alg w' V' W hWV'₂)) (sub_mem π hπ hw hV' hW hWV' hWV'₂) hx
    have e' : w'.left.appLE V' W hWV'₂ (g.left.appLE V V' hV'V s) =
        w'.left.appLE V' W hWV'₂ (g'.left.appLE V V' hV'V₂ s) := by
      rw [comp_appLE_apply _ _ rfl _ _ _ _ _ (le_preimage_of_comp _ _ hV'V hWV'₂),
        comp_appLE_apply _ _ rfl _ _ _ _ _ (le_preimage_of_comp _ _ hV'V₂ hWV'₂)]
      have hh : w'.left ≫ g.left = w'.left ≫ g'.left := by rw [← Over.comp_left, h', Over.comp_left]
      rw [appLE_congr hh V W _ (le_preimage_of_comp _ _ hV'V₂ hWV'₂)]
    simp only [map_sub] at e
    rw [← sub_eq_zero, ← sub_eq_zero.mpr e, e', sub_self, sub_zero]
  have fin : (w.left ≫ g.left).appLE V W (le_preimage_of_comp _ _ hV'V hWV') =
      (w.left ≫ g'.left).appLE V W (le_preimage_of_comp _ _ hV'V₂ hWV') := by
    ext s
    rw [← comp_appLE_apply _ _ rfl _ _ _ hV'V hWV', ← comp_appLE_apply _ _ rfl _ _ _ hV'V₂ hWV']
    exact key s
  rw [← hW.isoSpec_hom_fromSpec, Category.assoc, Category.assoc,
    ← hV.SpecMap_appLE_fromSpec _ hW (le_preimage_of_comp _ _ hV'V hWV'), fin,
    hV.SpecMap_appLE_fromSpec _ hW]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftTranslateBoundedDerivFunctional
section
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.HCA

theorem SmFn.continuous_leftTranslate : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ l, ∀ f ∈ S, Continuous fun x : G => Λ l fun y => f (x * y) := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b _ _ μ hμ S hS hL K hK Λ hΛ l f hf
  letI := h.chartedSpace
  haveI : LocallyCompactSpace G := ChartedSpace.locallyCompactSpace 𝔤 G
  haveI : SecondCountableTopology 𝔸ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SecondCountableTopology G := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨C, hC⟩ := hΛ.bdd l
  rw [continuous_iff_continuousAt]
  intro x₀
  have hfc := hS f hf
  have hcont : Continuous fun x : G => ∫ y in K, ‖f (x * y) - f (x₀ * y)‖ ∂μ :=
    continuous_parametric_integral_of_continuous
      (f := fun x y : G => ‖f (x * y) - f (x₀ * y)‖)
      (((hfc.comp (continuous_fst.mul continuous_snd)).sub
        (hfc.comp (continuous_const.mul continuous_snd))).norm) hK
  have h0 : Filter.Tendsto (fun x : G => C * ∫ y in K, ‖f (x * y) - f (x₀ * y)‖ ∂μ) (nhds x₀) (nhds 0) := by
    have := (hcont.const_mul C).tendsto x₀
    simpa using this
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun x => ?_) h0
  have h1 := hΛ.lin l _ (hL f hf x₀) _ (hL f hf x) (-1)
  have h2 := hC _ (S.add_mem (S.smul_mem (-1 : ℂ) (hL f hf x₀)) (hL f hf x))
  rw [h1] at h2
  simpa [neg_add_eq_sub] using h2

end GlobalTheory.HCA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotDComp
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

def invP (q : ℕ) : PSh where
  obj U := PLift (IsUnit (q : Γ(U.unop, ⊤)))
  map f := TypeCat.ofHom fun h => ⟨by simpa using h.down.map f.unop.appTop.hom⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def fibQ (q N : ℕ) : Spc := pullback (trivV N (disc.obj (invP q))) (PGL.pr N)

def lineQ (q N : ℕ) : fibQ q N ⟶ ofCat (glCat 1) := pullback.snd _ _ ≫ PGL.line N

variable (R : Type) [CommRing R]

def cotPre (q N : ℕ) (I : Cx R) (n : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of (ULift.{1} R) (Cochain ((chains R).obj (sch.obj U.unop ⨯ fibQ q N)) I n)
  map f := ModuleCat.ofHom
    { toFun := fun α => (Cochain.ofHom ((chains R).map (prod.map (sch.map f.unop) (𝟙 (fibQ q N))))).comp α (zero_add n)
      map_add' := fun α β => Cochain.comp_add _ _ _ _
      map_smul' := fun r α => Cochain.comp_smul _ _ _ _ }
  map_id U := by
    ext α : 2
    simp
  map_comp f g := by
    ext α : 2
    change (Cochain.ofHom ((chains R).map (prod.map (sch.map (g.unop ≫ f.unop)) (𝟙 (fibQ q N))))).comp α (zero_add n) =
      (Cochain.ofHom ((chains R).map (prod.map (sch.map g.unop) (𝟙 (fibQ q N))))).comp
        ((Cochain.ofHom ((chains R).map (prod.map (sch.map f.unop) (𝟙 (fibQ q N))))).comp α (zero_add n)) (zero_add n)
    rw [show prod.map (sch.map (g.unop ≫ f.unop)) (𝟙 (fibQ q N)) =
      prod.map (sch.map g.unop) (𝟙 (fibQ q N)) ≫ prod.map (sch.map f.unop) (𝟙 (fibQ q N)) by simp,
      Functor.map_comp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

def cotD (q N : ℕ) (I : Cx R) (n : ℤ) : cotPre R q N I n ⟶ cotPre R q N I (n + 1) where
  app U := ModuleCat.ofHom
    { toFun := fun α => δ n (n + 1) α
      map_add' := fun α β => δ_add _ _ _ _
      map_smul' := fun r α => δ_smul _ _ _ _ }
  naturality U U' f := by
    ext α : 2
    revert α
    intro (α : Cochain ((chains R).obj (sch.obj U.unop ⨯ fibQ q N)) I n)
    change δ n (n + 1) ((Cochain.ofHom ((chains R).map (prod.map (sch.map f.unop) (𝟙 (fibQ q N))))).comp α (zero_add n)) =
      (Cochain.ofHom ((chains R).map (prod.map (sch.map f.unop) (𝟙 (fibQ q N))))).comp (δ n (n + 1) α) (zero_add (n + 1))
    rw [δ_zero_cochain_comp _ _ _ rfl, δ_ofHom, Cochain.zero_comp, smul_zero, add_zero]

theorem cotD_comp (q N : ℕ) (I : Cx R) (n : ℤ) : cotD R q N I n ≫ cotD R q N I (n + 1) = 0 := by
  ext U : 2
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  change δ (n + 1) (n + 1 + 1) (δ n (n + 1) α) = 0
  exact δ_δ _ _ _ _

def Jcx (q N : ℕ) (I : Cx R) : Cx R :=
  CochainComplex.of (fun n => (presheafToSheaf Scheme.etaleTopology.{0} _).obj (cotPre R q N I n))
    (fun n => (presheafToSheaf Scheme.etaleTopology.{0} _).map (cotD R q N I n))
    (fun n => by rw [← Functor.map_comp, cotD_comp, Functor.map_zero])

variable {R}

def Jsec {q N : ℕ} {I : Cx R} {n : ℤ} {U : Scheme.{0}} (c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n) :
    Sec ((Jcx R q N I).X n) U :=
  ((toSheafify Scheme.etaleTopology.{0} (cotPre R q N I n)).app (op U)).hom c

def twCast {q : ℕ} {i i' : ℤ} (h : i = i') {s : ℤ} {V : Scheme.{0}} (x : Sec ((res (ZMod q) (tw q i)).X s) V) :
    Sec ((res (ZMod q) (tw q i')).X s) V := h ▸ x

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupEqClassOfIsAW
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem Pair.cup_spec_full : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k), (∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m), ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1) ∧ ∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (γ : Cocycle ((chains R).obj E) K k), μ.IsAW hk α.1 β.1 γ.1 → μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ :=
  fun _ _ _ _ _ μ E _ _ _ hk => ⟨fun α β => μ.aw_exists E hk α β, fun α β γ h => μ.cup_spec E hk α β γ h⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupHypercohomologyPullback
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

namespace CupPull

theorem sub_map {E E' : Spc} (f : E ⟶ E') {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.map f).sub j l h = (x.sub j l h).map f := by
  have := ConcreteCategory.congr_hom (NatTrans.congr_app (f.naturality (SimplexCategory.subinterval j l h).op) (op U)) x
  simp only [NatTrans.comp_app, types_comp_apply, ConcreteCategory.comp_apply] at this
  exact this.symm

theorem isAW_pull {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E E' : Spc} (f : E ⟶ E') {n m k : ℤ}
    (hk : n + m = k) {α : Cochain ((chains R).obj E') I n} {β : Cochain ((chains R).obj E') J m}
    {γ : Cochain ((chains R).obj E') K k} (h : μ.IsAW hk α β γ) :
    μ.IsAW hk ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n))
      ((Cochain.ofHom ((chains R).map f)).comp β (zero_add m))
      ((Cochain.ofHom ((chains R).map f)).comp γ (zero_add k)) := by
  intro N w hw U x
  rw [CupSpec.ev_pull, h N w hw U (x.map f)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [CupSpec.ev_pull, CupSpec.ev_pull, sub_map, sub_map]

end CupPull

theorem Pair.cup_pull : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E E' : Spc} (f : E ⟶ E') {n m k : ℤ}
    (hk : n + m = k) a b, cpull ((chains R).map f) K k (μ.cup E' hk a b) =
      μ.cup E hk (cpull ((chains R).map f) I n a) (cpull ((chains R).map f) J m b) := by
  intro R _ I J K μ E E' f n m k hk a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := Pair.aw_exists μ E' hk α β
  rw [Pair.cup_spec μ E' hk α β γ hγ, cpre_mk, cpre_mk, cpre_mk]
  refine (Pair.cup_spec μ E hk _ _ _ ?_).symm
  have e : ((Cocycle.ofHom ((chains R).map f) : Cocycle _ _ 0) : Cochain _ _ 0) = Cochain.ofHom ((chains R).map f) :=
    Cocycle.ofHom_coe _
  simp only [zcomp, Cocycle.mk_coe, e]
  exact CupPull.isAW_pull μ f hk hγ

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLFiniteFieldFrobeniusPow
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem psiG_gal (F : Type) [Field F] [Finite F] (t : F ≃+* F) (S : F[X] → ℂ) :
    ∀ (n : ℕ) (x : GL (Fin n) F),
      psiG S n (gal (t : F →+* F) n x) = psiG (fun P => S (P.map (t : F →+* F))) n x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x
    rw [GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion F S n (gal (t : F →+* F) n x), GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion F _ n x]
    congr 1
    · simp only [chG, gal]
      congr 1
      rw [← Matrix.charpoly_map]
      rfl
    · refine Finset.sum_congr rfl fun a ha => ?_
      rw [GlobalTheory.T.harishChandraInductionGL_fieldAutomorphism F t a (n - a) n]
      have ha' : a < n := Finset.mem_range.1 ha
      congr 1
      funext y
      exact ih a ha' y

theorem cusp_gal : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (t : F ≃+* F) (j : ℕ),
    (∀ x, t x = x ^ (ringChar F ^ j)) → ∀ (m k : ℕ) (x : GL (Fin m) F),
    cusp θ m k (gal (t : F →+* F) m x) = cusp θ m (k * ringChar F ^ j) x := by
  intro F _ _ θ t j ht m k x
  simp only [cusp]
  rw [psiG_gal F t]
  congr 2
  funext P
  exact GlobalTheory.T.rootSum_map_frobenius_pow_eq_rootSum_mul F θ (t : F →+* F) j (fun y => ht y) k P

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DadjCombinationStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_D_eq_sum_smul_D_of_mem_adjoin : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (n : ℕ) (u : Fin n → F), ∀ v ∈ Algebra.adjoin k (Set.range u), ∃ c : Fin n → F, (∀ j, c j ∈ Algebra.adjoin k (Set.range u)) ∧ D k K (algebraMap F K v) = ∑ j, algebraMap F K (c j) • D k K (algebraMap F K (u j)) := by
  first | (exact @GlobalTheory.dadj_combination) | (exact GlobalTheory.dadj_combination) | (intros; apply GlobalTheory.dadj_combination  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialRelationLocalRingBound
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differential_relation_local_ring_bound : ∀ (k K : Type) [Field k] [CharZero k] [Field K] [Algebra k K] (B : Subalgebra k K) (Q : Ideal B), Q.IsPrime → ∀ (s : B) (m : ℕ) (y : Fin m → K) (T : K) (e : ℕ), 1 ≤ e → s ∈ Q → (∀ v : B, ∃ r : B, r ∉ Q ∧ ∃ c : Fin (m + 1) → B, (r : K) • D k K (v : K) = ∑ l, (c l : K) • (Fin.cons (D k K (s : K)) (fun j => D k K (y j)) : Fin (m + 1) → Ω[K⁄k]) l) → (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * T = a * s ^ e) → ∃ N Dn : B, N ∉ Q ∧ Dn ∉ Q ∧ (Dn : K) • ExteriorAlgebra.ιMulti K (m + 1) (Fin.cons (D k K T) (fun j => D k K (y j)) : Fin (m + 1) → Ω[K⁄k]) = ((N : K) * (s : K) ^ (e - 1)) • ExteriorAlgebra.ιMulti K (m + 1) (Fin.cons (D k K (s : K)) (fun j => D k K (y j)) : Fin (m + 1) → Ω[K⁄k]) := by
  first | (exact @GlobalTheory.wedge_D_eq_pow_mul_wedge_D_of_eq_unit_mul_pow) | (exact GlobalTheory.wedge_D_eq_pow_mul_wedge_D_of_eq_unit_mul_pow) | (intros; apply GlobalTheory.wedge_D_eq_pow_mul_wedge_D_of_eq_unit_mul_pow  <;> assumption)
end

