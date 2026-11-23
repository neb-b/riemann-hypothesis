module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ContinuousAevalMvPolynomial
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SpanSingletonEqTopIffIsUnitOfIsBaseChange
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.MemHomogIffIsHomogeneous
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemUnitaryGroupIffIsIsometry
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOpenPartialHomeomorphAnalytic
section
namespace GlobalTheory.AffinePoints

open Topology Filter Set MvPolynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

theorem analyticAt_aevalTower {σ ι : Type*} [Fintype σ] [Fintype ι]
    (q : MvPolynomial ι (MvPolynomial σ 𝕜)) (w : (σ → 𝕜) × (ι → 𝕜)) :
    AnalyticAt 𝕜 (fun w : (σ → 𝕜) × (ι → 𝕜) =>
      (aevalTower (aeval w.1) w.2 : MvPolynomial ι (MvPolynomial σ 𝕜) →ₐ[𝕜] 𝕜) q) w := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    simp only [aevalTower_C]
    exact AnalyticAt.aeval_mvPolynomial (A := 𝕜) (f := fun w : (σ → 𝕜) × (ι → 𝕜) => w.1)
      (fun i => ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : σ => 𝕜) i).comp
        (ContinuousLinearMap.fst 𝕜 (σ → 𝕜) (ι → 𝕜))).analyticAt w) a
  | add P Q hP hQ => simp only [map_add (f := _)]; exact hP.add hQ
  | mul_X P i hP =>
    simp only [map_mul, aevalTower_X]
    exact hP.mul (((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι => 𝕜) i).comp
        (ContinuousLinearMap.snd 𝕜 (σ → 𝕜) (ι → 𝕜))).analyticAt w)

theorem hasDerivAt_aevalTower_line {R ι : Type*} [CommRing R] [Algebra 𝕜 R] [Fintype ι]
    (φ : R →ₐ[𝕜] 𝕜) (q : MvPolynomial ι R) (y v : ι → 𝕜) :
    HasDerivAt (fun t : 𝕜 => (aevalTower φ (y + t • v) : MvPolynomial ι R →ₐ[𝕜] 𝕜) q)
      (∑ i, (aevalTower φ y : MvPolynomial ι R →ₐ[𝕜] 𝕜) (pderiv i q) * v i) 0 := by
  classical
  induction q using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const (0 : 𝕜) (φ a)
  | add P Q hP hQ =>
    simp only [map_add (f := _), add_mul, Finset.sum_add_distrib]
    exact hP.add hQ
  | mul_X P i hP =>
    have hX : HasDerivAt (fun t : 𝕜 => y i + t * v i) (v i) 0 := by
      simpa using ((hasDerivAt_id (0 : 𝕜)).mul_const (v i)).const_add (y i)
    have h := hP.mul hX
    simp only [map_mul, aevalTower_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine HasDerivAt.congr_deriv h ?_
    have h1 : ∀ j, (aevalTower φ y : MvPolynomial ι R →ₐ[𝕜] 𝕜) (pderiv j (P * X i)) * v j =
        (aevalTower φ y : MvPolynomial ι R →ₐ[𝕜] 𝕜) (pderiv j P) * v j * y i +
        if i = j then (aevalTower φ y : MvPolynomial ι R →ₐ[𝕜] 𝕜) P * v j else 0 := by
      intro j
      rw [pderiv_mul, pderiv_X]
      by_cases hij : i = j
      · subst hij; simp; ring
      · simp [hij, Pi.single_eq_of_ne hij]; ring
    simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      ← Finset.sum_mul]
    simp

variable [CompleteSpace 𝕜] {A : Type*} [CommRing A] [Algebra 𝕜 A] {d : ℕ}

theorem exists_openPartialHomeomorph_analytic {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] (hdim : Module.finrank 𝕜 E = Module.finrank 𝕜 F) {Ψ : E → F} {x : E}
    (hΨ : AnalyticAt 𝕜 Ψ x) (hinj : Function.Injective (fderiv 𝕜 Ψ x)) :
    ∃ Φ : OpenPartialHomeomorph E F, (Φ : E → F) = Ψ ∧ x ∈ Φ.source ∧
      AnalyticOnNhd 𝕜 Φ.symm Φ.target := by
  haveI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  haveI : CompleteSpace F := FiniteDimensional.complete 𝕜 F
  have hsurj : Function.Surjective (fderiv 𝕜 Ψ x) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := (fderiv 𝕜 Ψ x : E →ₗ[𝕜] F))).mp hinj
  let Le := ContinuousLinearEquiv.ofBijective (fderiv 𝕜 Ψ x) (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj)
  have hLe : (Le : E →L[𝕜] F) = fderiv 𝕜 Ψ x := ContinuousLinearEquiv.coe_ofBijective _ _ _
  have hφ : HasStrictFDerivAt Ψ (Le : E →L[𝕜] F) x := by rw [hLe]; exact hΨ.hasStrictFDerivAt
  let Φ := hφ.toOpenPartialHomeomorph Ψ
  have hpS : x ∈ Φ.source := hφ.mem_toOpenPartialHomeomorph_source
  have hsymm : AnalyticAt 𝕜 Φ.symm (Φ x) :=
    Φ.analyticAt_symm' (i := Le) hpS hΨ hLe.symm
  obtain ⟨s, hs, hsan⟩ := hsymm.exists_mem_nhds_analyticOnNhd
  obtain ⟨T, hTs, hTo, hTp⟩ := mem_nhds_iff.mp hs
  refine ⟨(Φ.symm.restrOpen T hTo).symm, rfl, ⟨hpS, hTp⟩, fun z hz => hsan z (hTs hz.2)⟩

theorem exists_chart_of_etale (g : MvPolynomial (Fin d) 𝕜 →ₐ[𝕜] A) (hg : g.Etale)
    (p : A →ₐ[𝕜] 𝕜) :
    ∃ e : OpenPartialHomeomorph (A →ₐ[𝕜] 𝕜) (Fin d → 𝕜), p ∈ e.source ∧
      (e : (A →ₐ[𝕜] 𝕜) → Fin d → 𝕜) = coords g ∧
      ∀ a, AnalyticOnNhd 𝕜 (fun z => e.symm z a) e.target := by
  classical
  letI : Algebra (MvPolynomial (Fin d) 𝕜) A := g.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin d) 𝕜) A := hg
  haveI : IsScalarTower 𝕜 (MvPolynomial (Fin d) 𝕜) A :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  obtain ⟨ι, σ, _, _, P, hP⟩ := (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.1
    ‹Algebra.Etale (MvPolynomial (Fin d) 𝕜) A›).out
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite σ
  have hcard : Fintype.card σ = Fintype.card ι := by
    have := P.card_relations_le_card_vars_of_isFinite
    simp only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card] at this hP
    omega
  have hbij : Function.Bijective P.map :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨P.map_inj, hcard⟩
  let π : MvPolynomial ι (MvPolynomial (Fin d) 𝕜) →ₐ[𝕜] A := (aeval P.val).restrictScalars 𝕜
  have hπ : Function.Surjective π := P.aeval_val_surjective
  let ev : (Fin d → 𝕜) × (ι → 𝕜) → (MvPolynomial ι (MvPolynomial (Fin d) 𝕜) →ₐ[𝕜] 𝕜) :=
    fun w => aevalTower (aeval w.1) w.2
  let j : (A →ₐ[𝕜] 𝕜) → (Fin d → 𝕜) × (ι → 𝕜) := fun q => (coords g q, fun i => q (P.val i))
  have hjc : Continuous j :=
    (continuous_coords g).prodMk (continuous_pi fun _ => continuous_eval _)
  have hevj : ∀ q, ev (j q) = comap π q := by
    intro q
    refine MvPolynomial.algHom_ext' ?_ ?_
    · ext i
      simp [ev, j, π, coords, RingHom.algebraMap_toAlgebra]
    · intro i; simp [ev, j, π]
  have hker : ∀ a, π a = 0 ↔ a ∈ Ideal.span (range P.relation) := by
    intro a
    rw [P.span_range_relation_eq_ker]
    rw [P.ker_eq_ker_aeval_val]
    rfl
  have hex : ∀ w, (∀ r, ev w (P.relation r) = 0) → ∃ q, j q = w ∧ comap π q = ev w := by
    intro w hw
    obtain ⟨q, hq⟩ := exists_comap_eq_of_surjective π hπ (ev w) fun a ha => by
      have : Ideal.span (range P.relation) ≤ RingHom.ker (ev w) := by
        rw [Ideal.span_le]; rintro _ ⟨r, rfl⟩; exact hw r
      exact this ((hker a).1 ha)
    refine ⟨q, ?_, hq⟩
    ext i
    · simpa [ev, π, j, coords, RingHom.algebraMap_toAlgebra] using DFunLike.congr_fun hq (C (X i))
    · simpa [ev, π, j] using DFunLike.congr_fun hq (X i)
  have hjinj : Function.Injective j := by
    intro q q' h
    ext a
    obtain ⟨b, rfl⟩ := hπ a
    have := hevj q
    rw [h, hevj] at this
    exact (DFunLike.congr_fun this b).symm
  let Ψ : (Fin d → 𝕜) × (ι → 𝕜) → (Fin d → 𝕜) × (σ → 𝕜) :=
    fun w => (w.1, fun r => ev w (P.relation r))
  have hΨj : ∀ q, Ψ (j q) = (coords g q, 0) := by
    intro q
    ext r
    · rfl
    · change ev (j q) (P.relation r) = 0
      rw [hevj, comap_apply, (hker _).2 (Ideal.subset_span ⟨r, rfl⟩), map_zero]
  have hΨan : AnalyticAt 𝕜 Ψ (j p) :=
    analyticAt_fst.prod (analyticAt_pi_iff.2 fun r => analyticAt_aevalTower _ _)
  have hinj : Function.Injective (fderiv 𝕜 Ψ (j p)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨u, v⟩ huv
    have hline : HasDerivAt (fun t : 𝕜 => Ψ (j p + t • (u, v))) 0 0 := by
      have h1 : HasDerivAt (fun t : 𝕜 => j p + t • (u, v)) (u, v) 0 := by
        simpa using ((hasDerivAt_id (0 : 𝕜)).smul_const (u, v)).const_add (j p)
      have h2 : HasFDerivAt Ψ (fderiv 𝕜 Ψ (j p)) (j p + (0 : 𝕜) • (u, v)) := by
        simpa using hΨan.differentiableAt.hasFDerivAt
      have := h2.comp_hasDerivAt (0 : 𝕜) h1
      rwa [huv] at this
    have hu : u = 0 := by
      have h1 : HasDerivAt (fun t : 𝕜 => (j p).1 + t • u) u 0 := by
        simpa using ((hasDerivAt_id (0 : 𝕜)).smul_const u).const_add (j p).1
      have h2 := (ContinuousLinearMap.fst 𝕜 (Fin d → 𝕜) (σ → 𝕜)).hasFDerivAt.comp_hasDerivAt
        (0 : 𝕜) hline
      exact h1.unique h2
    subst hu
    have hv : ∀ r, ∑ i, ev (j p) (pderiv i (P.relation r)) * v i = 0 := by
      intro r
      have h1 := hasDerivAt_aevalTower_line (aeval (j p).1) (P.relation r) (j p).2 v
      have h2 := (((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : σ => 𝕜) r).comp
        (ContinuousLinearMap.snd 𝕜 (Fin d → 𝕜) (σ → 𝕜))).hasFDerivAt.comp_hasDerivAt (0 : 𝕜) hline)
      refine h1.unique ?_
      simpa [Function.comp_def, Ψ, ev] using h2
    have hdet : ((ev (j p)).toRingHom.mapMatrix P.jacobiMatrix).det ≠ 0 := by
      rw [← RingHom.map_det, hevj]
      have := (P.jacobian_isUnit.map p).ne_zero
      rw [P.jacobian_eq_jacobiMatrix_det, P.algebraMap_apply] at this
      exact this
    have hw : (fun s => v (P.map s)) = 0 := by
      refine Matrix.eq_zero_of_vecMul_eq_zero hdet ?_
      ext r
      rw [Pi.zero_apply, ← hv r, ← hbij.sum_comp]
      simp [Matrix.vecMul, dotProduct, P.jacobiMatrix_apply, mul_comm]
    have : v = 0 := by
      ext i
      obtain ⟨s, rfl⟩ := hbij.2 i
      exact congrFun hw s
    rw [this]; rfl
  obtain ⟨Φ, hΦ, hpS, hsymm⟩ := exists_openPartialHomeomorph_analytic
    (by simp [Module.finrank_prod, hcard]) hΨan hinj
  have hex' : ∀ z : Fin d → 𝕜, ∃ q : A →ₐ[𝕜] 𝕜, (z, 0) ∈ Φ.target →
      j q = Φ.symm (z, 0) ∧ comap π q = ev (Φ.symm (z, 0)) := by
    intro z
    by_cases hz : (z, 0) ∈ Φ.target
    · obtain ⟨q, hq⟩ := hex (Φ.symm (z, 0)) fun r => by
        have := congrFun (congrArg Prod.snd (Φ.right_inv hz)) r
        rwa [hΦ] at this
      exact ⟨q, fun _ => hq⟩
    · exact ⟨p, fun h => absurd h hz⟩
  choose s hs using hex'
  have han : ∀ a, AnalyticOnNhd 𝕜 (fun z => s z a) {z | (z, 0) ∈ Φ.target} := by
    intro a
    obtain ⟨b, rfl⟩ := hπ a
    have hop : IsOpen {z : Fin d → 𝕜 | (z, 0) ∈ Φ.target} :=
      Φ.open_target.preimage (continuous_id.prodMk continuous_const)
    refine AnalyticOnNhd.congr hop (f := fun z => ev (Φ.symm (z, 0)) b) ?_ ?_
    · intro z hz
      have h1 : AnalyticAt 𝕜 (fun z : Fin d → 𝕜 => Φ.symm (z, 0)) z :=
        AnalyticAt.comp (f := fun z : Fin d → 𝕜 => (z, (0 : σ → 𝕜))) (hsymm _ hz)
          (analyticAt_id.prod analyticAt_const)
      exact AnalyticAt.comp (f := fun z : Fin d → 𝕜 => Φ.symm (z, 0))
        (analyticAt_aevalTower b _) h1
    · intro z hz
      exact (DFunLike.congr_fun (hs z hz).2 b).symm
  have hmap : ∀ q, j q ∈ Φ.source → (coords g q, 0) ∈ Φ.target := by
    intro q hq
    have := Φ.map_source hq
    rwa [hΦ, hΨj] at this
  refine ⟨{ toFun := coords g
            invFun := s
            source := j ⁻¹' Φ.source
            target := {z | (z, 0) ∈ Φ.target}
            map_source' := hmap
            map_target' := fun z hz => ?_
            left_inv' := fun q hq => ?_
            right_inv' := fun z hz => ?_
            open_source := Φ.open_source.preimage hjc
            open_target := Φ.open_target.preimage (continuous_id.prodMk continuous_const)
            continuousOn_toFun := (continuous_coords g).continuousOn
            continuousOn_invFun := continuousOn_iff.2 fun a => (han a).continuousOn },
    hpS, rfl, han⟩
  · rw [mem_preimage, (hs z hz).1]; exact Φ.map_target hz
  · apply hjinj
    rw [(hs _ (hmap q hq)).1, ← hΨj, ← hΦ, Φ.left_inv hq]
  · have := Φ.right_inv hz
    rw [← (hs z hz).1, hΦ, hΨj] at this
    exact congrArg Prod.fst this

end GlobalTheory.AffinePoints
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueBaseChangeEqOfMem
section
open TensorProduct

namespace GlobalTheory

namespace FlatDescent

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  {N' : Type*} [AddCommGroup N'] [Module A N'] [Module B N'] [IsScalarTower A B N']

variable (A B N) in
def act : B ⊗[A] N →ₗ[B] N := LinearMap.liftBaseChange B (LinearMap.id : N →ₗ[A] N)

@[simp] theorem act_tmul (b : B) (n : N) : act A B N (b ⊗ₜ n) = b • n := by
  simp [act]

structure IsDescentDatum (θ : N →ₗ[B] B ⊗[A] N) : Prop where
  counit : ∀ n, act A B N (θ n) = n
  coassoc : ∀ n, (θ.restrictScalars A).lTensor B (θ n) = (TensorProduct.mk A B N 1).lTensor B (θ n)

def invariants (θ : N →ₗ[B] B ⊗[A] N) : Submodule A N :=
  LinearMap.ker (θ.restrictScalars A - TensorProduct.mk A B N 1)

@[simp] theorem mem_invariants {θ : N →ₗ[B] B ⊗[A] N} {n : N} :
    n ∈ invariants θ ↔ θ n = 1 ⊗ₜ n := by
  simp [invariants, sub_eq_zero]

variable (B) in
def canonical (M : Type*) [AddCommGroup M] [Module A M] :
    B ⊗[A] M →ₗ[B] B ⊗[A] (B ⊗[A] M) :=
  (TensorProduct.mk A B M 1).baseChange B

variable (B) in
theorem isDescentDatum_canonical (M : Type*) [AddCommGroup M] [Module A M] :
    IsDescentDatum (canonical (A := A) B M) := by
  constructor <;> intro x
  · induction x using TensorProduct.inductionOn with
    | tmul b m => simp [canonical, smul_tmul']
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction x using TensorProduct.inductionOn with
    | tmul b m => simp [canonical]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

variable (B) in
def extend (P : Submodule A N) : B ⊗[A] P →ₗ[B] N := LinearMap.liftBaseChange B P.subtype

@[simp] theorem extend_tmul (P : Submodule A N) (b : B) (n : P) :
    extend B P (b ⊗ₜ n) = b • (n : N) := by
  simp [extend]

theorem act_lTensor_subtype (P : Submodule A N) (x : B ⊗[A] P) :
    act A B N (P.subtype.lTensor B x) = extend B P x := by
  induction x using TensorProduct.inductionOn with
  | tmul b m => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem apply_extend (θ : N →ₗ[B] B ⊗[A] N) (x : B ⊗[A] invariants θ) :
    θ (extend B _ x) = (invariants θ).subtype.lTensor B x := by
  induction x using TensorProduct.inductionOn with
  | tmul b m => simp [mem_invariants.1 m.2, smul_tmul']
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem IsDescentDatum.bijective_extend [Module.Flat A B] {θ : N →ₗ[B] B ⊗[A] N}
    (h : IsDescentDatum θ) : Function.Bijective (extend B (invariants θ)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := B) _
      (invariants θ).injective_subtype
    rw [← apply_extend, hx, map_zero, map_zero]
  · intro n
    have hex := Module.Flat.lTensor_exact B
      (LinearMap.exact_subtype_ker_map (θ.restrictScalars A - TensorProduct.mk A B N 1))
    obtain ⟨x, hx⟩ := (hex (θ n)).1 (by
      rw [LinearMap.lTensor_sub, LinearMap.sub_apply, h.coassoc, sub_self])
    exact ⟨x, (act_lTensor_subtype (invariants θ) x).symm.trans
      ((congrArg (act A B N) hx).trans (h.counit n))⟩

theorem IsDescentDatum.isBaseChange [Module.Flat A B] {θ : N →ₗ[B] B ⊗[A] N}
    (h : IsDescentDatum θ) : IsBaseChange B (invariants θ).subtype :=
  IsBaseChange.of_equiv (LinearEquiv.ofBijective _ h.bijective_extend) fun n => by simp

section Amitsur

variable (B) (M : Type*) [AddCommGroup M] [Module A M]

def toInvariants : M →ₗ[A] invariants (canonical (A := A) B M) :=
  (TensorProduct.mk A B M 1).codRestrict _ fun m => by simp [canonical]

theorem bijective_toInvariants [Module.FaithfullyFlat A B] :
    Function.Bijective (toInvariants (A := A) B M) := by
  rw [← Module.FaithfullyFlat.lTensor_bijective_iff_bijective A B,
    ← Function.Bijective.of_comp_iff' (isDescentDatum_canonical (A := A) B M).bijective_extend]
  convert Function.bijective_id
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul b m => simp [toInvariants, smul_tmul']
  | add x y hx hy => simp_all

def amitsurDiff : B ⊗[A] M →ₗ[A] B ⊗[A] (B ⊗[A] M) :=
  (canonical B M).restrictScalars A - TensorProduct.mk A B (B ⊗[A] M) 1

@[simp] theorem amitsurDiff_tmul (b : B) (m : M) :
    amitsurDiff B M (b ⊗ₜ[A] m) =
      b ⊗ₜ[A] ((1 : B) ⊗ₜ[A] m) - (1 : B) ⊗ₜ[A] (b ⊗ₜ[A] m) := rfl

theorem amitsur_exact [Module.FaithfullyFlat A B] :
    Function.Injective (TensorProduct.mk A B M 1) ∧
      Function.Exact (TensorProduct.mk A B M 1) (amitsurDiff (A := A) B M) := by
  refine ⟨Module.FaithfullyFlat.tensorProduct_mk_injective M, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨m, hm⟩ := (bijective_toInvariants (A := A) B M).2 ⟨x, hx⟩
    exact ⟨m, congrArg Subtype.val hm⟩
  · rintro ⟨m, rfl⟩
    simp

end Amitsur

section Morphisms

variable {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']


variable (B) in
theorem bijective_baseChange_iff [Module.FaithfullyFlat A B] (g : M →ₗ[A] M') :
    Function.Bijective (g.baseChange B) ↔ Function.Bijective g :=
  Module.FaithfullyFlat.lTensor_bijective_iff_bijective A B g

end Morphisms

section Invertible

theorem invertible_of_isBaseChange [Module.FaithfullyFlat A B] {M : Type*} [AddCommGroup M]
    [Module A M] {j : M →ₗ[A] N} (hj : IsBaseChange B j) [Module.Invertible B N] :
    Module.Invertible A M := by
  have : Module.Finite A M := Descent.finite_of_isBaseChange hj
  have : Module.Projective A M := Descent.projective_of_isBaseChange hj
  let e : B ⊗[A] (Module.Dual A M ⊗[A] M) ≃ₗ[B] B ⊗[A] A :=
    AlgebraTensorModule.distribBaseChange A B _ _ ≪≫ₗ
      TensorProduct.congr (SymAlg.isBaseChange_dual hj).equiv hj.equiv ≪≫ₗ
        Module.Invertible.linearEquiv B N ≪≫ₗ (AlgebraTensorModule.rid A B B).symm
  have he : (contractLeft A M).baseChange B = e.toLinearMap := by
    ext ξ m
    apply (AlgebraTensorModule.rid A B B).injective
    simp [e, Module.Invertible.linearEquiv, hj.toDual_comp_apply, Algebra.algebraMap_eq_smul_one]
  refine ⟨(bijective_baseChange_iff B _).1 ?_⟩
  rw [he]
  exact e.bijective

variable (B) in
theorem IsDescentDatum.invertible_invariants [Module.FaithfullyFlat A B]
    {θ : N →ₗ[B] B ⊗[A] N} (h : IsDescentDatum θ) [Module.Invertible B N] :
    Module.Invertible A (invariants θ) :=
  invertible_of_isBaseChange h.isBaseChange


end Invertible

section Gluing



end Gluing

end FlatDescent

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsBigOPowIffIteratedFDerivEqZero
section
open Filter Topology Asymptotics Complex
open scoped Real ComplexConjugate

namespace GlobalTheory.Doubling

noncomputable section

section Rigidity

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup G]
  [NormedSpace ℂ G]

end Rigidity

section Series

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup G]
  [NormedSpace ℂ G]

def quadPart (h : E → G) (z : E) : G := (2 : ℂ)⁻¹ • iteratedFDeriv ℂ 2 h 0 fun _ => z

end Series

section Character

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem eq_cexp_fderiv_of_map_add {f : E → ℂ} (hf : DifferentiableAt ℂ f 0) (h0 : f 0 ≠ 0)
    (hm : ∀ x y, f (x + y) = f x * f y) (z : E) : f z = cexp (fderiv ℂ f 0 z) := by
  first
  | exact @_root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv
  | exact _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv
  | (apply _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv ..)

end Character

section Alternating

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

end Alternating

section Lattice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]

end Lattice

end

end GlobalTheory.Doubling
end

