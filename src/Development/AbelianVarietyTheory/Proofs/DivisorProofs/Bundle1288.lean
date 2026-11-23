module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkGLOneCorner
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1261
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.DblEval

section Blocks

variable {A : Type} {κ κ₁ κ' κ₁' : Type}

def partL (T : ((κ → A) → ℂ) → (κ₁ → A) → ℂ) (Φ : (κ ⊕ κ' → A) → ℂ) : (κ₁ ⊕ κ' → A) → ℂ :=
  fun y => T (fun x => Φ (Sum.elim x (y ∘ Sum.inr))) (y ∘ Sum.inl)

def partR (T : ((κ' → A) → ℂ) → (κ₁' → A) → ℂ) (Φ : (κ ⊕ κ' → A) → ℂ) : (κ ⊕ κ₁' → A) → ℂ :=
  fun y => T (fun x => Φ (Sum.elim (y ∘ Sum.inl) x)) (y ∘ Sum.inr)

def partLₗ (e : ((κ → A) → ℂ) →ₗ[ℂ] (κ₁ → A) → ℂ) : ((κ ⊕ κ' → A) → ℂ) →ₗ[ℂ] (κ₁ ⊕ κ' → A) → ℂ where
  toFun := partL e
  map_add' Φ Ψ := funext fun y => by
    show e ((fun x => Φ _) + fun x => Ψ _) _ = _
    rw [map_add (f := _)]; rfl
  map_smul' c Φ := funext fun y => by
    show e (c • fun x => Φ _) _ = _
    rw [map_smul]; rfl

def partRₗ (e : ((κ' → A) → ℂ) →ₗ[ℂ] (κ₁' → A) → ℂ) : ((κ ⊕ κ' → A) → ℂ) →ₗ[ℂ] (κ ⊕ κ₁' → A) → ℂ where
  toFun := partR e
  map_add' Φ Ψ := funext fun y => by
    show e ((fun x => Φ _) + fun x => Ψ _) _ = _
    rw [map_add (f := _)]; rfl
  map_smul' c Φ := funext fun y => by
    show e (c • fun x => Φ _) _ = _
    rw [map_smul]; rfl

@[simp] theorem partLₗ_apply (e : ((κ → A) → ℂ) →ₗ[ℂ] (κ₁ → A) → ℂ) (Φ : (κ ⊕ κ' → A) → ℂ) :
    partLₗ e Φ = partL e Φ := rfl

@[simp] theorem partRₗ_apply (e : ((κ' → A) → ℂ) →ₗ[ℂ] (κ₁' → A) → ℂ) (Φ : (κ ⊕ κ' → A) → ℂ) :
    partRₗ e Φ = partR e Φ := rfl

end Blocks

def conjLin {X Y : Type} (e : (X → ℂ) →ₗ[ℂ] (Y → ℂ)) : (X → ℂ) →ₗ[ℂ] (Y → ℂ) where
  toFun φ y := starRingEnd ℂ (e (fun x => starRingEnd ℂ (φ x)) y)
  map_add' φ ψ := funext fun y => by
    have h : (fun x => starRingEnd ℂ (φ x + ψ x)) = (fun x => starRingEnd ℂ (φ x)) + fun x => starRingEnd ℂ (ψ x) :=
      funext fun x => map_add _ _ _
    simp only [Pi.add_apply]
    rw [h, map_add (f := _), Pi.add_apply, map_add (f := _)]
  map_smul' c φ := funext fun y => by
    have h : (fun x => starRingEnd ℂ (c * φ x)) = starRingEnd ℂ c • fun x => starRingEnd ℂ (φ x) :=
      funext fun x => by simp
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [h, map_smul, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_conj]

theorem conjLin_apply {X Y : Type} (e : (X → ℂ) →ₗ[ℂ] (Y → ℂ)) (φ : X → ℂ) (y : Y) :
    conjLin e φ y = starRingEnd ℂ (e (fun x => starRingEnd ℂ (φ x)) y) := rfl

section Loc

variable (F : Type) [Field F] [NumberField F]

def stdInd (κ : Type) (v : Pl (F := F)) : (κ → Fv F v) → ℂ := Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1

variable {F}

def IsLocOp {κ κ₁ : Type} [Fintype κ] [Fintype κ₁] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ) : Prop :=
  ∃ (ei : SInf F κ →L[ℂ] SInf F κ₁) (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ₁ → Fv F v) → ℂ),
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ₁ → Fv F v)) ∧
    (∀ᶠ v in cofinite, ev v (stdInd F κ v) = stdInd F κ₁ v) ∧
    ∀ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) →
      (∀ᶠ v in cofinite, φ v = stdInd F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)

end Loc

end GlobalTheory.DblEval

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapApply
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.DoublingEv

def conjMap {X Y : Type} (T : (X → ℂ) →ₗ[ℂ] (Y → ℂ)) : (X → ℂ) →ₗ[ℂ] (Y → ℂ) where
  toFun φ := star (T (star φ))
  map_add' φ φ' := by rw [star_add, map_add (f := _), star_add]
  map_smul' c φ := by rw [star_smul, map_smul, star_smul, star_star]; rfl

theorem conjMap_apply {X Y : Type} (T : (X → ℂ) →ₗ[ℂ] (Y → ℂ)) (φ : X → ℂ) :
    conjMap T φ = star (T (star φ)) := rfl

variable {R : Type}

def partR {κ κ' κ₁' : Type} (T : ((κ' → R) → ℂ) →ₗ[ℂ] ((κ₁' → R) → ℂ)) :
    ((κ ⊕ κ' → R) → ℂ) →ₗ[ℂ] ((κ ⊕ κ₁' → R) → ℂ) where
  toFun Φ s := T (fun x₂ => Φ (Sum.elim (s ∘ Sum.inl) x₂)) (s ∘ Sum.inr)
  map_add' Φ Ψ := by funext s; exact congrFun (map_add T (fun x₂ => Φ (Sum.elim (s ∘ Sum.inl) x₂)) (fun x₂ => Ψ (Sum.elim (s ∘ Sum.inl) x₂))) _
  map_smul' c Φ := by funext s; exact congrFun (map_smul T c (fun x₂ => Φ (Sum.elim (s ∘ Sum.inl) x₂))) _

def partL {κ κ₁ κ' : Type} (T : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) :
    ((κ ⊕ κ' → R) → ℂ) →ₗ[ℂ] ((κ₁ ⊕ κ' → R) → ℂ) where
  toFun Φ s := T (fun x₁ => Φ (Sum.elim x₁ (s ∘ Sum.inr))) (s ∘ Sum.inl)
  map_add' Φ Ψ := by funext s; exact congrFun (map_add T (fun x₁ => Φ (Sum.elim x₁ (s ∘ Sum.inr))) (fun x₁ => Ψ (Sum.elim x₁ (s ∘ Sum.inr)))) _
  map_smul' c Φ := by funext s; exact congrFun (map_smul T c (fun x₁ => Φ (Sum.elim x₁ (s ∘ Sum.inr)))) _

theorem partR_apply {κ κ' κ₁' : Type} (T : ((κ' → R) → ℂ) →ₗ[ℂ] ((κ₁' → R) → ℂ)) (Φ : (κ ⊕ κ' → R) → ℂ)
    (s : κ ⊕ κ₁' → R) : partR (κ := κ) T Φ s = T (fun x₂ => Φ (Sum.elim (s ∘ Sum.inl) x₂)) (s ∘ Sum.inr) := rfl

theorem partL_apply {κ κ₁ κ' : Type} (T : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) (Φ : (κ ⊕ κ' → R) → ℂ)
    (s : κ₁ ⊕ κ' → R) : partL (κ' := κ') T Φ s = T (fun x₁ => Φ (Sum.elim x₁ (s ∘ Sum.inr))) (s ∘ Sum.inl) := rfl

def evDbl {κ κ₁ : Type} (e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) :
    ((κ ⊕ κ → R) → ℂ) →ₗ[ℂ] ((κ₁ ⊕ κ₁ → R) → ℂ) :=
  partL e ∘ₗ partR (conjMap e)

theorem evDbl_apply {κ κ₁ : Type} (e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) (Φ : (κ ⊕ κ → R) → ℂ)
    (s : κ₁ ⊕ κ₁ → R) : evDbl e Φ s =
      e (fun x₁ => conjMap e (fun x₂ => Φ (Sum.elim x₁ x₂)) (s ∘ Sum.inr)) (s ∘ Sum.inl) := by
  simp only [evDbl, LinearMap.comp_apply, partL_apply, partR_apply, Sum.elim_comp_inl, Sum.elim_comp_inr]

theorem evDbl_boxFun {κ κ₁ : Type} (e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) (φ₁ φ₂ : (κ → R) → ℂ) :
    evDbl e (boxFun φ₁ φ₂) = boxFun (e φ₁) (conjMap e φ₂) := by
  funext s
  rw [evDbl_apply]
  have h1 : ∀ x₁ : κ → R, (fun x₂ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) = φ₁ x₁ • φ₂ := fun x₁ => by
    funext x₂; simp [boxFun]
  have h2 : (fun x₁ => conjMap e (fun x₂ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) (s ∘ Sum.inr)) =
      conjMap e φ₂ (s ∘ Sum.inr) • φ₁ := by
    funext x₁; rw [h1, map_smul]; simp [mul_comm]
  rw [h2, map_smul]
  simp [boxFun, mul_comm]

section Tame

open scoped Classical

variable (F : Type) [Field F] [NumberField F]

def IsTame {κ κ' : Type} [Fintype κ] [Fintype κ'] (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) : Prop :=
  ∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ (ι : Type) (_ : Fintype ι)
    (P : ι → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (κ' → mixedEmbedding.mixedSpace F) ℂ)
    (g' : ι → (κ' → FiniteAdeleRing (𝓞 F) F) → ℂ), (∀ j, g' j ∈ SB (κ' → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, T (pureA F f g) = ∑ j, pureA F (P j f) (g' j)

variable {F}

theorem IsTame.comp {κ κ' κ'' : Type} [Fintype κ] [Fintype κ'] [Fintype κ'']
    {T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)} {T' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)}
    (hT : IsTame F T) (hT' : IsTame F T') : IsTame F (T' ∘ₗ T) := by
  intro g hg
  obtain ⟨ι, _, P, g', hg', hP⟩ := hT g hg
  choose ι' inst P' g'' hg'' hP' using fun j => hT' (g' j) (hg' j)
  letI : ∀ j, Fintype (ι' j) := inst
  refine ⟨Σ j, ι' j, inferInstance, fun p => (P' p.1 p.2).comp (P p.1), fun p => g'' p.1 p.2,
    fun p => hg'' p.1 p.2, fun f => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.comp_apply, hP, map_sum, Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun j _ => hP' j (P j f)

theorem IsTame.mapsTo {κ κ' : Type} [Fintype κ] [Fintype κ'] {T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    (hT : IsTame F T) : ∀ φ ∈ schA F κ, T φ ∈ schA F κ' := by
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    obtain ⟨ι, _, P, g', hg', hP⟩ := hT g hg
    rw [hP]
    exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨P j f, g' j, hg' j, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem IsTame.comp_adm {κ κ' : Type} [Fintype κ] [Fintype κ'] {T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    (hT : IsTame F T) {l : ((κ' → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm κ') :
    l ∘ₗ T ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨ι, _, P, g', hg', hP⟩ := hT g hg
  choose L hL using fun j => hl (g' j) (hg' j)
  refine ⟨∑ j, (L j).comp (P j), fun f => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.comp_apply, hP, map_sum, ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => hL j (P j f)

end Tame

end GlobalTheory.DoublingEv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstRelIffTwistFactorAt
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwistFactorCompare

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct

theorem eq_one_of_chrEq_one {D : D7} {χ : (AE D)ˣ →* Circle} (h : ChrEq χ 1) (x : (AE D)ˣ) : χ x = 1 := by
  refine HeckeFinTrivial.eq_one_of_trivial_on_finite D χ h.1 (fun y hy => ?_) x
  obtain ⟨j, h1, h2, h3⟩ := HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := CharLocProd.char_eq_prod_locK D j h1 h2 (PlaceIdem.exists_isPlIdem D j h1 h2 h3) χ 1 h
  obtain ⟨S, k, hS, hS'⟩ := finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom y)
  exact Subtype.ext ((hprod y hy S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS').trans
    (Finset.prod_eq_one fun P _ => rfl))

section Row

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

variable {R i}

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {σ : c.F →+* ℂ}
  {U : Unf Xo c σ D.R.r} {dict : GA D (Wc D i) → Σ k, Frame (U.X k).Ψ D.R.r}
  {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)} {g : ℕ}
  {e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ}
  {th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
  {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}
  {dδ : T0 → DeltaDat Xo c (Vc D i).rank}
  {U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ (σ.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) D.R.r}
  {dict₂ : ∀ t, GA D (Wc D i) → Σ k, Frame ((U₂ t).X k).Ψ D.R.r}
  {xi : T0 → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ}

end Row

end GlobalTheory.TwistFactorCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermSliceLeviModerateGrowth
section
open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.LeviGA

namespace GlobalTheory.SliceTwo.Growth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]


omit [_root_.NumberField.IsTotallyComplex E] in
theorem height_inv {a : ℕ} (y : GL (Fin a) (Cinf E)) : height y⁻¹ = height y := by
  unfold height; rw [inv_inv]; ring


omit [_root_.NumberField.IsTotallyComplex E] in
theorem height_mul_right_le {a : ℕ} (c : GL (Fin a) (Cinf E)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y, height (y * c) ≤ B * height y := by
  obtain ⟨B, hB, h⟩ := GlobalTheory.ConstTermGrowth.height_mul_left_le (E := E) (isCompact_singleton (x := c⁻¹))
  refine ⟨B, hB, fun y => ?_⟩
  have := h _ rfl y⁻¹
  rwa [← _root_.mul_inv_rev, height_inv, height_inv] at this


omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_toL_blkGL_one_le {a r : ℕ} (hr : r ≤ a) (y : GL (Fin (a - r)) (Cinf E)) :
    ‖toL (blkGL hr (1, y)).val‖ ≤ 1 + ‖toL y.val‖ := by
  have h0 : (0 : ℝ) ≤ 1 + ‖toL y.val‖ := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  obtain ⟨i, rfl⟩ := (blkEquiv hr).surjective i
  obtain ⟨j, rfl⟩ := (blkEquiv hr).surjective j
  change ‖(blkGL hr (1, y) : Matrix (Fin a) (Fin a) (Cinf E)) (blkEquiv hr i) (blkEquiv hr j)‖ ≤ _
  rw [blkGL_apply]
  rcases i with i | i <;> rcases j with j | j
  · simp only [Matrix.fromBlocks_apply₁₁, Units.val_one]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq]
      refine ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => ?_).trans (by linarith [norm_nonneg (toL y.val)])
      simp
    · rw [Matrix.one_apply_ne hij, norm_zero]; exact h0
  · simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, norm_zero]; exact h0
  · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, norm_zero]; exact h0
  · simp only [Matrix.fromBlocks_apply₂₂]
    exact ((norm_le_pi_norm (toL y.val i) j).trans (norm_le_pi_norm (toL y.val) i)).trans
      (by linarith)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem height_blkGL_one_le {a r : ℕ} (hr : r ≤ a) (y : GL (Fin (a - r)) (Cinf E)) :
    height (blkGL hr (1, y)) ≤ 3 * height y := by
  have e : (blkGL hr (1, y))⁻¹ = blkGL hr (1, y⁻¹) := by
    rw [← map_inv, Prod.inv_mk, inv_one]
  have h1 := norm_toL_blkGL_one_le hr y
  have h2 := norm_toL_blkGL_one_le hr y⁻¹
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  unfold height
  rw [e]
  linarith

end GlobalTheory.SliceTwo.Growth


open GlobalTheory.SliceTwo.Growth in
theorem GlobalTheory.SliceTwo.Growth.norm_slice_le : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ)
    (hr : r ≤ a) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
    (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ : Sm E a, IsAutForm φ →
    ∀ (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a) (g : GA E (a - r)), ∃ (C : ℝ) (M : ℕ), ∀ y,
      ‖GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ.1 m₁ t κ (g * infGL E (a - r) y)‖ ≤ C * height y ^ M := by
  intro E _ _ _ a r hr _ _ μ 𝓕 hμ hF h1 φ hφ m₁ t κ g
  obtain ⟨C, N, hC⟩ := GlobalTheory.ConstTermGrowth.norm_constTerm_le E a r μ 𝓕 hμ hF h1 φ hφ.left hφ.level hφ.growth
    (blkGL hr (m₁, g) * finGL E a t)
  obtain ⟨B, hB0, hB⟩ := height_mul_right_le (E := E) (Unitary.toUnits κ)
  refine ⟨|C| * (3 * B) ^ N, N, fun y => ?_⟩
  have e : GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ.1 m₁ t κ (g * infGL E (a - r) y) =
      ∫ x in 𝓕, φ.1 (unip x * ((blkGL hr (m₁, g) * finGL E a t) *
        infGL E a (blkGL hr (1, y) * Unitary.toUnits κ))) ∂μ := by
    unfold GlobalTheory.SliceTwo.slice
    congr 1
    funext x
    congr 2
    rw [GlobalTheory.SliceTwo.blkGL_mul_infGL, map_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (infGL E a (blkGL hr (1, y))) (finGL E a t), infGL_comm]
    simp only [mul_assoc]
  rw [e]
  refine (hC _).trans ?_
  have hy := one_le_height y
  have hb := one_le_height (blkGL hr (1, y) * Unitary.toUnits κ)
  have h3 : height (blkGL hr (1, y) * Unitary.toUnits κ) ≤ 3 * B * height y := by
    calc _ ≤ B * height (blkGL hr (1, y)) := hB _
      _ ≤ B * (3 * height y) := mul_le_mul_of_nonneg_left (height_blkGL_one_le hr y) hB0
      _ = 3 * B * height y := by ring
  calc C * height (blkGL hr (1, y) * Unitary.toUnits κ) ^ N
      ≤ |C| * height (blkGL hr (1, y) * Unitary.toUnits κ) ^ N :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by linarith) _)
    _ ≤ |C| * (3 * B * height y) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) h3 _) (abs_nonneg C)
    _ = |C| * (3 * B) ^ N * height y ^ N := by ring

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousInvolutiveLocalTransposeInverse
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.LocTwist

variable {R : Type} [CommRing R]

theorem map_Phi (a : ℕ) (c : R →+* R) : c.mapMatrix (GlobalTheory.Tw.Phi a R) = GlobalTheory.Tw.Phi a R := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem Phi_mul_self (a : ℕ) : GlobalTheory.Tw.Phi a R * GlobalTheory.Tw.Phi a R = ((-1 : R) ^ (a - 1)) • (1 : Matrix (Fin a) (Fin a) R) := by
  ext i k
  simp only [Matrix.mul_apply, GlobalTheory.Tw.Phi, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i.rev]
  · have h1 : (i : ℕ) + (i.rev : ℕ) + 1 = a := by rw [Fin.val_rev]; omega
    rw [if_pos h1]
    by_cases h : k = i
    · subst h
      rw [if_pos (by rw [Fin.val_rev]; omega), Matrix.one_apply_eq, mul_one, ← pow_add]
      congr 1
      rw [Fin.val_rev]; omega
    · rw [if_neg (fun h2 => h (Fin.ext (by rw [Fin.val_rev] at h2; omega))), Matrix.one_apply_ne (Ne.symm h), mul_zero, mul_zero]
  · intro j _ hj
    rw [if_neg (fun h => hj (Fin.ext (by rw [Fin.val_rev]; omega))), zero_mul]
  · simp

theorem thetaGL_val (a : ℕ) (c : R →+* R) (g : GL (Fin a) R) :
    (thetaGL a c g).val = GlobalTheory.Tw.Phi a R * (c.mapMatrix (g⁻¹).val)ᵀ * (GlobalTheory.Tw.Phi a R)ᵀ := rfl

theorem thetaGL_thetaGL (a : ℕ) (c : R →+* R) (hc : ∀ x, c (c x) = x) (g : GL (Fin a) R) :
    thetaGL a c (thetaGL a c g) = g := by
  apply Units.ext
  have hT : ∀ M : Matrix (Fin a) (Fin a) R, c.mapMatrix Mᵀ = (c.mapMatrix M)ᵀ := fun M => rfl
  have hcc : ∀ M : Matrix (Fin a) (Fin a) R, c.mapMatrix (c.mapMatrix M) = M := fun M => by
    ext i j; exact hc _
  rw [thetaGL_val, ← map_inv, thetaGL_val, inv_inv, map_mul, map_mul, map_Phi, hT, hT, map_Phi, hcc]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hP := Phi_mul_self (R := R) a
  have hPt : (GlobalTheory.Tw.Phi a R)ᵀ * (GlobalTheory.Tw.Phi a R)ᵀ = ((-1 : R) ^ (a - 1)) • (1 : Matrix (Fin a) (Fin a) R) := by
    rw [← Matrix.transpose_mul, hP, Matrix.transpose_smul, Matrix.transpose_one]
  have e : ∀ X : Matrix (Fin a) (Fin a) R, GlobalTheory.Tw.Phi a R * (GlobalTheory.Tw.Phi a R * (X * (GlobalTheory.Tw.Phi a R)ᵀ)) * (GlobalTheory.Tw.Phi a R)ᵀ
      = (GlobalTheory.Tw.Phi a R * GlobalTheory.Tw.Phi a R) * X * ((GlobalTheory.Tw.Phi a R)ᵀ * (GlobalTheory.Tw.Phi a R)ᵀ) := by
    intro X; simp only [Matrix.mul_assoc]
  rw [e, hP, hPt, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, ← mul_pow]
  simp

theorem continuous_thetaGL [TopologicalSpace R] [IsTopologicalRing R] (a : ℕ) (c : R →+* R) (hc : Continuous c) :
    Continuous (thetaGL a c) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · change Continuous fun g : GL (Fin a) R => GlobalTheory.Tw.Phi a R * ((g⁻¹).val.map c)ᵀ * (GlobalTheory.Tw.Phi a R)ᵀ
    exact (continuous_const.matrix_mul ((Units.continuous_coe_inv.matrix_map hc).matrix_transpose)).matrix_mul
      continuous_const
  · have : (fun g : GL (Fin a) R => ((thetaGL a c g)⁻¹).val) =
        fun g => GlobalTheory.Tw.Phi a R * (g.val.map c)ᵀ * (GlobalTheory.Tw.Phi a R)ᵀ := by
      funext g
      rw [← map_inv, thetaGL_val, inv_inv]
      rfl
    rw [this]
    exact (continuous_const.matrix_mul ((Units.continuous_val.matrix_map hc).matrix_transpose)).matrix_mul
      continuous_const

end GlobalTheory.LocTwist

theorem GlobalTheory.BCT.thL_continuous_involutive : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E →
    ∀ (n : ℕ) (w : Pl E), Continuous (thL n w) ∧ ∀ g : GLw n w, thL n w (thL n w g) = g := by
  intro E _ _ _ hU n w
  obtain ⟨hcont, hinv, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  unfold thL
  split_ifs
  · exact ⟨continuous_id, fun g => rfl⟩
  · exact ⟨GlobalTheory.LocTwist.continuous_thetaGL n (cj w) hcont, GlobalTheory.LocTwist.thetaGL_thetaGL n (cj w) hinv⟩
end
end

