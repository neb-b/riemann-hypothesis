module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0286
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0289
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0293
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import CompanionTheory.AutomorphicTheory.PlaceSeparation.IsOpenQuotientMapArt0
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0296

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivHermitianFrameNormAtComplexPlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory

theorem ambSpace_map_eq_sum {K : Type} [Field K] [NumberField K] [StarRing K] {σ : K →+* ℂ} (A : HLat K)
    {W : Type} [AddCommGroup W] [Module ℂ W] (j : A.V →ₛₗ[σ] W) (x : A.V) :
    j x = ∑ i, σ (A.b.repr x i) • j (A.b i) := by
  conv_lhs => rw [← A.b.sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [LinearMap.map_smulₛₗ]

private lemma exists_linearEquiv_euclidean_norm_eq_mulVec {ι W : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup W]
    [Module ℂ W] (bW : Module.Basis ι ℂ W) (N : Matrix ι ι ℂ) (hN : IsUnit N.det) :
    ∃ (n : ℕ) (g : W ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n)),
      ∀ w, ‖g w‖ = Real.sqrt (∑ i, ‖(N.mulVec (bW.equivFun w)) i‖ ^ 2) := by
  letI := Matrix.invertibleOfIsUnitDet N hN
  let e₂ : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ) := Matrix.toLinearEquiv' N this
  let e₃ : (ι → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ ι := (WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm
  let e₄ : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (Fintype.card ι)) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fintype.equivFin ι)
  refine ⟨Fintype.card ι, bW.equivFun.trans (e₂.trans (e₃.trans e₄.toLinearEquiv)), fun w => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.norm_map, EuclideanSpace.norm_eq]
  rfl

theorem exists_equiv_normAt_eq_norm : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (A : HLat K) (W : Type) [AddCommGroup W] [Module ℂ W] (j : A.V →ₛₗ[σ] W), (∀ v, IsUnit (A.X v).det) → LinearIndependent ℂ (fun i => j (A.b i)) → Submodule.span ℂ (Set.range fun i => j (A.b i)) = ⊤ → ∃ (n : ℕ) (g : W ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n)), ∀ x, Formalism.HermitianLatticesTheory.normAt A.b A.X (InfinitePlace.mk σ) x = ‖g (j x)‖ := by
  intro K _ _ _ σ A W _ _ j hX hli hsp
  let bW : Module.Basis A.ι ℂ W := Module.Basis.mk hli (by rw [hsp])
  have hc : ∀ x, bW.equivFun (j x) = fun i => σ (A.b.repr x i) := by
    intro x
    have hx : j x = bW.equivFun.symm (fun i => σ (A.b.repr x i)) := by
      rw [Module.Basis.equivFun_symm_apply, ambSpace_map_eq_sum]
      simp [bW, Module.Basis.mk_apply]
    rw [hx, LinearEquiv.apply_symm_apply]
  have hU : IsUnit ((A.X (InfinitePlace.mk σ))⁻¹).det := Matrix.isUnit_nonsing_inv_det _ (hX _)
  have hv : ∀ x, Formalism.HermitianLatticesTheory.vecAt A.b (InfinitePlace.mk σ) x =
      fun i => (InfinitePlace.mk σ).embedding (A.b.repr x i) := fun x => rfl
  rcases InfinitePlace.embedding_mk_eq σ with h | h
  · obtain ⟨n, g, hg⟩ := exists_linearEquiv_euclidean_norm_eq_mulVec bW (A.X (InfinitePlace.mk σ))⁻¹ hU
    refine ⟨n, g, fun x => ?_⟩
    rw [hg, hc]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Formalism.HermitianLatticesTheory.fcoord, hv, h]
  · have hU' : IsUnit (((A.X (InfinitePlace.mk σ))⁻¹).map (starRingEnd ℂ)).det := by
      have e : (((A.X (InfinitePlace.mk σ))⁻¹).map (starRingEnd ℂ)).det =
          starRingEnd ℂ ((A.X (InfinitePlace.mk σ))⁻¹).det := (RingHom.map_det _ _).symm
      rw [e]
      exact hU.map _
    obtain ⟨n, g, hg⟩ := exists_linearEquiv_euclidean_norm_eq_mulVec bW (((A.X (InfinitePlace.mk σ))⁻¹).map (starRingEnd ℂ)) hU'
    refine ⟨n, g, fun x => ?_⟩
    rw [hg, hc]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Formalism.HermitianLatticesTheory.fcoord, hv, h]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [← Complex.norm_conj]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum, ComplexEmbedding.conjugate_coe_eq]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtPointSpecializingOutsideBasicOpen
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.HorizPt

def strHom {R : Type} [CommRing R] {X : Scheme.{0}} (q : X ⟶ Sp R) (U : X.Opens) : CommRingCat.of R ⟶ Γ(X, U) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ q.appLE ⊤ U le_top

theorem fromSpec_str {R : Type} [CommRing R] {X : Scheme.{0}} (q : X ⟶ Sp R) {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ q = Spec.map (strHom q U) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec q (isAffineOpen_top _) hU le_top, IsAffineOpen.fromSpec_top,
    Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

theorem charZero {X : Scheme.{0}} (q : X ⟶ Sp ℤ) [Flat q] {U : X.Opens} (hU : IsAffineOpen U)
    [Nontrivial Γ(X, U)] : CharZero Γ(X, U) := by
  have h₁ : (q.appLE ⊤ U le_top).hom.Flat :=
    HasRingHomProperty.appLE @Flat q inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h₂ : (strHom q U).hom.Flat :=
    RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv)) h₁
  have h₃ : (algebraMap ℤ Γ(X, U)).Flat := by
    rwa [Subsingleton.elim (algebraMap ℤ Γ(X, U)) (strHom q U).hom]
  have := RingHom.flat_algebraMap_iff.1 h₃
  exact charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective ℤ Γ(X, U))

theorem main : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (N : TrueGeo.Model Y) (W : N.X.Opens) (z : N.X) (g : Γ(N.X, W)), z ∈ W → g ≠ 0 → z ∉ N.X.basicOpen g → ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ N.X), spMap e.O.subtype ≫ yt = y.1 ≫ N.j ∧ ⊤ ≤ yt ⁻¹ᵁ W ∧ yt (IsLocalRing.closedPoint e.O) ∉ N.X.basicOpen g ∧ N.j (below y.1) ∈ N.X.basicOpen g := by
  intro F _ _ Y N W z g hz hg hzg
  have := N.ar.isIntegral
  have := N.ar.flat
  have : IsProper N.p := by
    obtain ⟨n, c, hc, h⟩ := N.ar.isProjOver
    have := isProper_str (𝓞 F) n
    rw [← h]
    infer_instance
  obtain ⟨U, hU, hzU, hUW⟩ := exists_isAffineOpen_mem_and_subset hz
  have hle : U ≤ W := hUW
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have : CharZero Γ(N.X, U) := charZero (N.p ≫ spMap (Int.castRingHom (𝓞 F))) hU
  let _ : Algebra (𝓞 F) Γ(N.X, U) := (strHom N.p U).hom.toAlgebra
  have : Algebra.FiniteType (𝓞 F) Γ(N.X, U) :=
    RingHom.FiniteType.comp (N.p.finiteType_appLE (isAffineOpen_top _) hU le_top)
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv).2)
  set g' : Γ(N.X, U) := N.X.presheaf.map (homOfLE hle).op g with hg'
  have hg0 : g' ≠ 0 := fun h => hg (map_injective_of_isIntegral N.X (homOfLE hle) (by rw [← hg', h, map_zero]))
  have hb : ∀ x : PrimeSpectrum Γ(N.X, U), hU.fromSpec x ∈ N.X.basicOpen g ↔ g' ∉ x.asIdeal := by
    intro x
    have h₁ : hU.fromSpec x ∈ U := by
      have := hU.range_fromSpec
      exact (Set.ext_iff.1 this _).1 ⟨x, rfl⟩
    have h₂ : hU.fromSpec x ∈ N.X.basicOpen g' ↔ g' ∉ x.asIdeal := by
      change x ∈ hU.fromSpec ⁻¹ᵁ N.X.basicOpen g' ↔ _
      rw [hU.fromSpec_preimage_basicOpen]
      rfl
    rw [← h₂, hg', Scheme.basicOpen_res]
    exact ⟨fun h => ⟨h₁, h⟩, fun h => h.2⟩
  have hp : g' ∈ (hU.primeIdealOf ⟨z, hzU⟩).asIdeal := by
    by_contra h
    have := (hb _).2 h
    rw [hU.fromSpec_primeIdealOf] at this
    exact hzg this
  obtain ⟨𝔪, h𝔪, hle'⟩ := Ideal.exists_le_maximal _ (hU.primeIdealOf ⟨z, hzU⟩).isPrime.ne_top
  obtain ⟨v, e, φ, h₁, h₂, h₃⟩ := _root_.GlobalTheory.TrueGeo.HorizRing.main F Γ(N.X, U) 𝔪 h𝔪 g' hg0
  let yt : Sp e.O ⟶ N.X := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec
  have hw : (spMap e.O.subtype ≫ yt) ≫ N.p =
      spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) := by
    simp only [yt, Category.assoc]
    rw [fromSpec_str, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact h₁ a
  have hy := N.pb.lift_fst _ _ hw
  refine ⟨v, e, ⟨N.pb.lift _ _ hw, N.pb.lift_snd _ _ hw⟩, yt, hy.symm, ?_, ?_, ?_⟩
  · intro x _
    exact hle ((Set.ext_iff.1 hU.range_fromSpec _).1 ⟨_, rfl⟩)
  · intro h
    refine (hb (PrimeSpectrum.comap φ (IsLocalRing.closedPoint e.O))).1 h ?_
    have := hle' hp
    rw [← h₂] at this
    exact this
  · change (N.pb.lift _ _ hw ≫ N.j) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ _
    rw [hy]
    refine (hb (PrimeSpectrum.comap φ (PrimeSpectrum.comap e.O.subtype
      (IsLocalRing.closedPoint (AlgebraicClosure F))))).2 fun h => h₃ ?_
    have h' : ((φ g' : e.O) : AlgebraicClosure F) ∈ IsLocalRing.maximalIdeal (AlgebraicClosure F) := h
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h'
    exact Subtype.ext h'

end GlobalTheory.TrueGeo.HorizPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolyRepCombinationPurePowerTrace
section
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.PureVirt

variable {ι : Type} [Fintype ι] {m : ι → ℕ} {S : Type} [CommRing S] [Algebra ℝ S]

def Virt (m : ι → ℕ) (g : ℕ → Mat m S → S) : Prop :=
  ∃ (J : Type) (_ : Fintype J) (ρ : J → PolyRep m) (c : J → ℝ),
    ∀ (A : Mat m S) (b : ℕ), ∑ j, c j • (ρ j).ptr b A = g b A

theorem virt_smul (r : ℝ) {g : ℕ → Mat m S → S} (hg : Virt m g) : Virt m (fun b A => r • g b A) := by
  obtain ⟨J, _, ρ, c, hc⟩ := hg
  refine ⟨J, inferInstance, ρ, fun j => r * c j, fun A b => ?_⟩
  simp only [← hc, Finset.smul_sum, smul_smul]

theorem virt_fsum {α : Type} [Fintype α] (g : α → ℕ → Mat m S → S) (hg : ∀ a, Virt m (g a)) :
    Virt m (fun b A => ∑ a, g a b A) := by
  choose J hJ ρ c hc using hg
  refine ⟨Σ a, J a, inferInstance, fun x => ρ x.1 x.2, fun x => c x.1 x.2, fun A b => ?_⟩
  rw [Fintype.sum_sigma]
  simp only [hc]

theorem ptr_tensor_sub_wedge2 (ρ : PolyRep m) (A : Mat m S) (b : ℕ) :
    (ρ.tensor ρ).ptr b A - 2 * ρ.wedge2.ptr b A = 2 ^ b * ρ.ptr b A := by
  have h := _root_.GlobalTheory.GoodMetric.ChernSpan.two_mul_trace_wedge2Lie_pow (ρ.lie A) b
  have e1 : (ρ.tensor ρ).ptr b A = ((kron (ρ.lie A) 1 + kron 1 (ρ.lie A)) ^ b).trace :=
    congrArg (fun L => (L ^ b).trace) (_root_.GlobalTheory.GoodMetric.PolyRep.lie_tensor ρ ρ A)
  have e2 : ρ.wedge2.ptr b A = ((wedge2Lie (ρ.lie A)) ^ b).trace :=
    congrArg (fun L => (L ^ b).trace) (_root_.GlobalTheory.GoodMetric.PolyRep.lie_wedge2 ρ A)
  have e3 : ρ.ptr b A = ((ρ.lie A) ^ b).trace := rfl
  linear_combination e1 - 2 * e2 - h - 2 ^ b * e3

theorem virt_double {g : ℕ → Mat m S → S} (hg : Virt m g) :
    Virt m (fun b A => (2 : ℝ) ^ b • g b A) := by
  obtain ⟨J, _, ρ, c, hc⟩ := hg
  refine ⟨J ⊕ J, inferInstance, Sum.elim (fun j => (ρ j).tensor (ρ j)) (fun j => (ρ j).wedge2),
    Sum.elim c (fun j => -2 * c j), fun A b => ?_⟩
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [← hc, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := ptr_tensor_sub_wedge2 (ρ j) A b
  simp only [Algebra.smul_def, map_mul, map_neg, map_pow, map_ofNat]
  linear_combination (algebraMap ℝ S (c j)) * h

theorem virt_proj (τ : ι) : Virt m (fun b (A : Mat m S) => ((A τ) ^ b).trace) := by
  refine ⟨Unit, inferInstance, fun _ => proj m τ, fun _ => 1, fun A b => ?_⟩
  simp only [PolyRep.ptr, lie_proj_model, one_smul, Finset.univ_unique, Finset.sum_singleton]
  rfl

theorem virt_pow (τ : ι) (a : ℕ) :
    Virt m (fun b (A : Mat m S) => ((2 : ℝ) ^ a) ^ b • ((A τ) ^ b).trace) := by
  induction a with
  | zero => simpa using virt_proj (m := m) (S := S) τ
  | succ a ih =>
    have e : (fun b (A : Mat m S) => ((2 : ℝ) ^ (a + 1)) ^ b • ((A τ) ^ b).trace)
        = fun b A => (2 : ℝ) ^ b • (((2 : ℝ) ^ a) ^ b • ((A τ) ^ b).trace) := by
      funext b A
      rw [smul_smul, pow_succ, mul_pow, mul_comm]
    rw [e]
    exact virt_double ih

theorem exists_vandermonde_solution (n i : ℕ) : ∃ x : Fin (n + 1) → ℝ, ∀ b : Fin (n + 1),
    ∑ a, x a * ((2 : ℝ) ^ (a : ℕ)) ^ (b : ℕ) = if (b : ℕ) = i then 1 else 0 := by
  set V := Matrix.vandermonde (fun a : Fin (n + 1) => (2 : ℝ) ^ (a : ℕ)) with hV
  have hinj : Function.Injective (fun a : Fin (n + 1) => (2 : ℝ) ^ (a : ℕ)) := by
    intro a a' h
    exact Fin.ext ((pow_right_strictMono₀ one_lt_two).injective h)
  have hdet : IsUnit V.det := isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hinj)
  set δ : Fin (n + 1) → ℝ := fun b => if (b : ℕ) = i then 1 else 0 with hδ
  refine ⟨δ ᵥ* V⁻¹, fun b => ?_⟩
  have h : (δ ᵥ* V⁻¹) ᵥ* V = δ := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
  exact congrFun h b

theorem exists_pure_power_trace {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S]
    [Algebra ℝ S] (τ : ι) (i : ℕ) (_hi : 1 ≤ i) :
    ∃ (J : Type) (_ : Fintype J) (ρ : J → PolyRep m) (c : J → ℝ), ∀ (A : Mat m S) (b : ℕ), b ≤ n →
      ∑ j, c j • (ρ j).ptr b A = if b = i then ((A τ) ^ i).trace else 0 := by
  obtain ⟨x, hx⟩ := exists_vandermonde_solution n i
  obtain ⟨J, hJ, ρ, c, hc⟩ := virt_fsum (m := m) (S := S)
    (fun a : Fin (n + 1) => fun b A => x a • (((2 : ℝ) ^ (a : ℕ)) ^ b • ((A τ) ^ b).trace))
    (fun a => virt_smul (x a) (virt_pow τ a))
  refine ⟨J, hJ, ρ, c, fun A b hb => ?_⟩
  rw [hc]
  have h := hx ⟨b, Nat.lt_succ_of_le hb⟩
  simp only [smul_smul, ← Finset.sum_smul] at h ⊢
  rw [h]
  split_ifs with hbi
  · subst hbi; exact one_smul ℝ _
  · exact zero_smul ℝ _

end GlobalTheory.GoodMetric.PureVirt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSphericalEigensystemOfFiniteTypeWithPartsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sphericalEigensystem_of_finiteType_with_parts : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ σ : D.what₂.FT, ∃ c, (∀ b, ∀ U ∈ principalLevelFrame.isotE R.θ Y.PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) R.e0 (principalLevelFrame.rowRepR R.θ (Y.eFT σ)), ∃ x ∈ R.EEc c, R.HE.e x = U) ∧ (∀ i, ∀ U ∈ principalLevelFrame.isotL R.θ (Y.PW i) (R.MW i (sg0 D A3.A)) (levS _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (levChi _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (R.eWf i (sg0 D A3.A)) (principalLevelFrame.rowRepR R.θ (Y.eFT σ)), ∃ x ∈ R.Wc' i c, (R.HW i (sg0 D A3.A)).e x = U) := by
  first | exact @GlobalTheory.Mem.R3.LabEig.eig_parts | exact GlobalTheory.Mem.R3.LabEig.eig_parts | (intros; apply GlobalTheory.Mem.R3.LabEig.eig_parts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupleUnitaryFormsEquivPeriodRowForms
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE
open GlobalTheory.TopStep Formalism.HermitianLatticesTheory
noncomputable section

namespace GlobalTheory.Mem.Df

section General

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (C : ChainIn X.E X.K X.Tau R) (b0 : (C.S R.m).β)
  (til : ∀ b, (stepX Ch sel mu P).D b → (C.S R.m).D b0) (ext : ∀ b, (stepX Ch sel mu P).G b →* (C.S R.m).G b0) (tz : X.E)

@[reducible] def perStepX : PerIn C where
  S' := stepX Ch sel mu P
  b0 := b0
  til := til
  ext := ext
  sg := W.sgW
  tz := tz
  H _ := ⊤

variable (σ : X.K →+* ℂ)

theorem mem_perStepX_Mt (F : ∀ b, (stepX Ch sel mu P).D b → Pol ℂ X.Tau (R.N R.m - 1)) :
    F ∈ (perStepX W Ch sel mu P C b0 til ext tz).Mt X.emb σ ↔
      FrLaw σ W.sgTrue (rowTyG Ch P) (levQX R sel mu) ⊤ fun p : XPt Pr R sel mu => F () (trivPt X _ _ _ _ p) := by
  constructor
  · intro h p
    refine ⟨(h () _).1, fun g hg => ?_⟩
    show F () (trivPt X _ _ _ _ (g • p)) = _
    rw [← stepX_smul_trivPt]
    exact (h () (trivPt X _ _ _ _ p)).2 g hg
  · rintro h ⟨⟩ d
    obtain ⟨p, rfl⟩ := (trivPt X _ ∅ Pr.vGs (QE sel (mu : Chr X.F X.E X.K))).surjective d
    refine ⟨(h p).1, fun g hg => ?_⟩
    exact (congrArg (F ()) (stepX_smul_trivPt Ch sel mu P g p)).trans ((h p).2 g hg)

variable (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K)))

def mtEquivStepX : MtP W Ch sel mu P σ ≃ₗ[ℂ] (perStepX W Ch sel mu P C b0 til ext tz).Mt X.emb σ :=
  LinearEquiv.ofBijective
    { toFun := fun F => ⟨fun _ p => F.1 (toRow sel mu p.1.1),
        (mem_perStepX_Mt W Ch sel mu P C b0 til ext tz σ _).2
          ((frLaw_comp_iff σ W.sgTrue (isSubLev_top (rowTyG Ch P) (levQX R sel mu)) hd F.1).2 F.2)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    ⟨fun F G h => Subtype.ext (funext fun d => by
      obtain ⟨p, rfl⟩ := toRow_surjective sel mu d
      exact congrFun (congrFun (congrArg Subtype.val h) ()) (trivPt X _ _ _ _ p)),
    fun F => by
      obtain ⟨G, hG, e⟩ := ((mem_perStepX_Mt W Ch sel mu P C b0 til ext tz σ F.1).1 F.2).exists_form σ W.sgTrue
        (isSubLev_top (rowTyG Ch P) (levQX R sel mu)) hd
      refine ⟨⟨G, hG⟩, Subtype.ext (funext fun _ => funext fun p => (e p.1.1).trans ?_)⟩
      exact congrArg (F.1 ()) ((trivPt X _ ∅ Pr.vGs (QE sel (mu : Chr X.F X.E X.K))).apply_symm_apply p)⟩

end General

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem disjoint_vGs_Q (hI : I.Ok) (l : I.Laws) (a : I.ι) : Disjoint (B.primes X).vGs (I.Q a) :=
  GlobalTheory.NormOneUnit.disjoint_vGs_QE (I.tup a) l.pr hI.sel_ok (fun i => hI.g_mem i)

theorem mtCx_equiv_per : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok),
    ∀ (u : B.Word) (a : I.ι), ∃ g : MtCx I a ≃ₗ[ℂ] (I.per l u a).Mt, ∀ F, SameForm I l u a F (g F) := by
  intro B X I hI _ l _ u a
  let g := mtEquivStepX B.wts I.Ch I.sel (I.tup a) I.Ps (I.chIn u a) (I.perIn u a).b0 (I.perIn u a).til (I.perIn u a).ext
    (I.perIn u a).tz B.embLL (disjoint_vGs_Q I hI l a)
  exact ⟨g, fun F p => rfl⟩

end GlobalTheory.Mem.Df

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWdSide
section
noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem exists_wdSide : GlobalTheory.Published.DeRhamPotSemistable → ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), Nonempty (WDSide D T) :=
  fun hB D T => nonempty_wdSide_of_tie hB D T

end GlobalTheory.HeightCounting
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteChart
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def Chart (u : B.Word) (a : I.ι) (i : ℕ) : Type :=
  Set.range fun c : (I.stp u a i).Cl => (c.1, cosetIn ((I.stp u a i).rep c))

def chartOf (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) : Chart I u a i :=
  ⟨(c.1, cosetIn ((I.stp u a i).rep c)), c, rfl⟩

structure AdmK (u : B.Word) (a : I.ι) (i : ℕ) {Ch : Type} (k : Ch → GA B (B.R.N i)) : Prop where
  std : ∀ β, ∃ p : DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, PtOf (k β) p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N i)
  off : ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → ¬ I.UnderQ a v →
    (a = I.mu0 ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) → bc (prV (E := B.host.E) v) (k β) = 1
  T : ∀ β (P : (B.primes X).vT u) (r j : Fin (B.R.N i)), r.1 + 1 = B.R.N i →
    HasRes P.1 (adAt B.host.F P.1 (((k β)⁻¹ : GA B (B.R.N i)).1 r j))
      (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0)

theorem finite_chart (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) : Finite (Chart I u a i) := by
  have h := (l.ch u a).step i
  haveI : Finite (I.stp u a i).Cl := @Finite.instSigma _ _ inferInstance h.fin_orb
  exact (Set.finite_range _).to_subtype

end GlobalTheory.Mem.Col2.TC.ChTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
section
theorem GlobalTheory.globalArtinReciprocity_holds : GlobalTheory.Published.GlobalArtinReciprocity := CompanionTheory.FamInh.globalArtin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawsOfOk
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC


set_option maxHeartbeats 1600000 in
theorem laws_of_ok : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → I.Laws := by
  intro B X I h
  have hch := _root_.GlobalTheory.Mem.Col2.TC.ok_chains I h
  have hlev := _root_.GlobalTheory.Mem.Col2.LevelLaw.atIn_ok I h
  have hper := _root_.GlobalTheory.Mem.Col2.PerLaw.perIn_laws I h
  have hall := fun u a => laws_all (I.chIn u a) (I.atIn u a) B.fields.emb B.embLL (B.hcW u) (base_fOk B) (hch u a).1 (hlev u a)
    (I.perIn u a) (hper u a).1 B.places
  exact
    { pr := (base_fields_primes_ok B X).2.1
      ch := fun u a => (hch u a).1
      lev := hlev
      per := fun u a => (hper u a).1
      ovr := fun u a => (hper u a).2
      atL := fun u a => (hall u a).1
      fmL := fun u a => (hall u a).2
      xi0 := h.trueColumnChoices_heckeChar_reference_eq_one
      idx0 := fun a => (hch B.u₀ a).2.1
      bij0 := fun u a b => (_root_.GlobalTheory.Mem.Col2.ClsZero.stepZero_classes_bijective_same_deco I h u a b).1
      lat := fun u a => (hch u a).2.2 }

end GlobalTheory.Mem.Col2.TC
end

