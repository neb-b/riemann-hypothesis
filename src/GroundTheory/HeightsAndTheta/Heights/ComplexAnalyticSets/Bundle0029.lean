module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreConditions
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0006

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSerreRFlatAscentLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

section FlatLocal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [IsLocalRing S]
  [IsLocalHom (algebraMap R S)]

theorem isLocalRing_closedFibre :
    IsLocalRing (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
  have : Nontrivial (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    Ideal.Quotient.nontrivial_iff.mpr (map_maximalIdeal_lt_top (algebraMap R S)).ne
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

theorem ringKrullDim_eq_add_ringKrullDim_closedFibre [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.Flat R S] :
    ringKrullDim S = ringKrullDim R + ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
  have := isLocalRing_closedFibre (R := R) (S := S)
  have : (maximalIdeal S).LiesOver (maximalIdeal R) := ⟨(maximalIdeal_comap (algebraMap R S)).symm⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal R) (maximalIdeal S)
  rw [map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at h
  rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim,
    ← maximalIdeal_height_eq_ringKrullDim, h, WithBot.coe_add]

theorem isRegularLocalRing_of_flat_of_closedFibre [IsNoetherianRing S] [Module.Flat R S]
    (hR : IsRegularLocalRing R) (hF : IsRegularLocalRing (S ⧸ (maximalIdeal R).map (algebraMap R S))) :
    IsRegularLocalRing S := by
  have : IsNoetherianRing R := by have := hR; infer_instance
  have := isLocalRing_closedFibre (R := R) (S := S)
  set J := (maximalIdeal R).map (algebraMap R S)
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [ringKrullDim_eq_add_ringKrullDim_closedFibre (R := R), ← (isRegularLocalRing_iff R).mp hR,
    ← (isRegularLocalRing_iff (S ⧸ J)).mp hF]
  suffices h : (maximalIdeal S).spanFinrank ≤
      (maximalIdeal R).spanFinrank + (maximalIdeal (S ⧸ J)).spanFinrank by
    exact_mod_cast h
  have fgR := (maximalIdeal R).fg_of_isNoetherianRing
  have fgF := (maximalIdeal (S ⧸ J)).fg_of_isNoetherianRing
  set s := (maximalIdeal R).generators
  set t := (maximalIdeal (S ⧸ J)).generators
  have hsurj : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  let lift : S ⧸ J → S := Function.surjInv hsurj
  set t' := lift '' t
  have ht' : Ideal.Quotient.mk J '' t' = t := by
    rw [Set.image_image]
    simp [lift, Function.surjInv_eq hsurj]
  have : IsLocalHom (Ideal.Quotient.mk J) := IsLocalHom.of_surjective _ hsurj
  have hcomap : (maximalIdeal (S ⧸ J)).comap (Ideal.Quotient.mk J) = maximalIdeal S :=
    maximalIdeal_comap _
  have heq : maximalIdeal S = Ideal.span (algebraMap R S '' s ∪ t') := by
    apply le_antisymm
    · intro x hx
      have hx' : Ideal.Quotient.mk J x ∈ Ideal.map (Ideal.Quotient.mk J) (Ideal.span t') := by
        rw [Ideal.map_span, ht']
        change Ideal.Quotient.mk J x ∈ Submodule.span (S ⧸ J) t
        rw [Submodule.span_generators, ← Ideal.mem_comap, hcomap]
        exact hx
      rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker] at hx'
      rw [Ideal.span_union, sup_comm, ← Ideal.map_span]
      change x ∈ Submodule.span S t' ⊔ Ideal.map (algebraMap R S) (Submodule.span R s)
      rw [Submodule.span_generators]
      exact hx'
    · rw [Ideal.span_le, Set.union_subset_iff]
      constructor
      · rintro _ ⟨y, hy, rfl⟩
        exact map_maximalIdeal_le (algebraMap R S) (Ideal.mem_map_of_mem _ (Submodule.FG.generators_mem _ hy))
      · rintro _ ⟨y, hy, rfl⟩
        rw [SetLike.mem_coe, ← hcomap, Ideal.mem_comap, Function.surjInv_eq hsurj]
        exact Submodule.FG.generators_mem _ hy
  have fins := Submodule.FG.finite_generators fgR
  have fint := Submodule.FG.finite_generators fgF
  rw [heq, ← Submodule.FG.generators_ncard fgR, ← Submodule.FG.generators_ncard fgF]
  refine (Submodule.spanFinrank_span_le_ncard_of_finite ((fins.image _).union (fint.image _))).trans ?_
  exact (Set.ncard_union_le _ _).trans (add_le_add (Set.ncard_image_le fins) (Set.ncard_image_le fint))

end FlatLocal

section Localized

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (P : Ideal B) [P.IsPrime]

theorem map_maximalIdeal_localization_eq :
    letI := Localization.AtPrime.algebraOfLiesOver (P.under A) P
    (maximalIdeal (Localization.AtPrime (P.under A))).map
        (algebraMap (Localization.AtPrime (P.under A)) (Localization.AtPrime P)) =
      Ideal.map (algebraMap B (Localization.AtPrime P))
        (Ideal.map (algebraMap A B) (Ideal.comap (algebraMap A B) P)) := by
  let := Localization.AtPrime.algebraOfLiesOver (P.under A) P
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map]
  congr 1
  ext x
  simp only [RingHom.comp_apply]
  exact Localization.localRingHom_to_map _ _ _ Ideal.LiesOver.over x

end Localized

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceMatricesOpen
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

def sliceDeriv {n k : ℕ} (L : Matrix (Fin k) (Fin n) ℂ) (D : (Fin (k + 1) → ℂ) →L[ℂ] (Fin n → ℂ)) :
    (Fin (k + 1) → ℂ) →L[ℂ] (Fin (k + 1) → ℂ) :=
  (Fin.consEquivL ℂ (fun _ : Fin (k + 1) => ℂ) : _ →L[ℂ] _) ∘L
    ((ContinuousLinearMap.proj 0).prod ((Matrix.mulVecLin L).toContinuousLinearMap ∘L D))

theorem sliceDeriv_apply {n k : ℕ} (L : Matrix (Fin k) (Fin n) ℂ) (D : (Fin (k + 1) → ℂ) →L[ℂ] (Fin n → ℂ))
    (v : Fin (k + 1) → ℂ) : sliceDeriv L D v = vecCons (v 0) (L *ᵥ D v) := rfl

theorem hasFDerivAt_slice {n k : ℕ} {γ : (Fin (k + 1) → ℂ) → Fin n → ℂ} {s : Fin (k + 1) → ℂ}
    (hγ : DifferentiableAt ℂ γ s) (L : Matrix (Fin k) (Fin n) ℂ) :
    HasFDerivAt (fun t => vecCons (t 0) (L *ᵥ γ t)) (sliceDeriv L (fderiv ℂ γ s)) s := by
  have h1 : HasFDerivAt
      (fun t : Fin (k + 1) → ℂ => ((t 0, (Matrix.mulVecLin L).toContinuousLinearMap (γ t)) : ℂ × (Fin k → ℂ)))
      ((ContinuousLinearMap.proj 0).prod ((Matrix.mulVecLin L).toContinuousLinearMap ∘L fderiv ℂ γ s)) s :=
    (hasFDerivAt_apply 0 s).prodMk
      ((Matrix.mulVecLin L).toContinuousLinearMap.hasFDerivAt.comp s hγ.hasFDerivAt)
  exact (Fin.consEquivL ℂ (fun _ : Fin (k + 1) => ℂ)).hasFDerivAt.comp s h1

theorem bijective_iff_det_ne_zero {N : ℕ} (f : (Fin N → ℂ) →L[ℂ] (Fin N → ℂ)) :
    Function.Bijective f ↔ LinearMap.det (f : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ)) ≠ 0 := by
  rw [← isUnit_iff_ne_zero, ← LinearMap.isUnit_iff_isUnit_det, LinearMap.isUnit_iff_ker_eq_bot,
    LinearMap.ker_eq_bot]
  exact ⟨fun h => h.1, fun h => ⟨h, LinearMap.injective_iff_surjective.1 h⟩⟩

theorem SliceMatricesOpen.proof : SliceMatricesOpen.Statement := by
  intro n k m γ s hd hinj
  have hfd : ∀ (L : Matrix (Fin k) (Fin n) ℂ) b,
      fderiv ℂ (fun t => vecCons (t 0) (L *ᵥ γ b t)) (s b) = sliceDeriv L (fderiv ℂ (γ b) (s b)) :=
    fun L b => (hasFDerivAt_slice (hd b) L).fderiv
  constructor
  · have hset : {L : Matrix (Fin k) (Fin n) ℂ |
        ∀ b, Function.Bijective (fderiv ℂ (fun t => vecCons (t 0) (L *ᵥ γ b t)) (s b))} =
        ⋂ b, {L | LinearMap.det
          (sliceDeriv L (fderiv ℂ (γ b) (s b)) : (Fin (k + 1) → ℂ) →ₗ[ℂ] (Fin (k + 1) → ℂ)) ≠ 0} := by
      ext L
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, hfd, bijective_iff_det_ne_zero]
    rw [hset]
    refine isOpen_iInter_of_finite fun b => isOpen_ne_fun ?_ continuous_const
    simp_rw [← LinearMap.det_toMatrix']
    refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
    simp only [LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe, sliceDeriv_apply]
    refine Fin.cases ?_ (fun r => ?_) i
    · simp only [Matrix.cons_val_zero]
      exact continuous_const
    · simp only [Matrix.cons_val_succ]
      exact (continuous_apply r).comp (continuous_id.matrix_mulVec continuous_const)
  · set Lb : Fin m → (Fin k → ℂ) →ₗ[ℂ] (Fin n → ℂ) := fun b =>
      (fderiv ℂ (γ b) (s b) : (Fin (k + 1) → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ
        ((Fin.consEquivL ℂ (fun _ : Fin (k + 1) => ℂ)).toLinearEquiv.toLinearMap ∘ₗ
          LinearMap.inr ℂ ℂ (Fin k → ℂ)) with hLbdef
    have hLapp : ∀ b w, Lb b w = fderiv ℂ (γ b) (s b) (Fin.cons 0 w) := fun b w => rfl
    have hL : ∀ b, Function.Injective (Lb b) := by
      intro b
      refine (injective_iff_map_eq_zero (Lb b)).2 fun w hw => ?_
      rw [hLapp] at hw
      have h0 := hinj b (Fin.cons 0 w) (by simp) hw
      funext i
      simpa using congrFun h0 i.succ
    obtain ⟨π, hπ⟩ := IndefiniteRowSideFullHecke.ComplexSets.GeneralProjection.proof n k m Lb hL
    refine ⟨π, fun b => ?_⟩
    rw [hfd]
    have hΦ : Function.Injective (sliceDeriv π (fderiv ℂ (γ b) (s b))) := by
      refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
      rw [sliceDeriv_apply] at hv
      have hv0 : v 0 = 0 := by simpa using congrFun hv 0
      have hvc : v = Fin.cons 0 (Fin.tail v) := by rw [← hv0, Fin.cons_self_tail]
      have hw : π *ᵥ Lb b (Fin.tail v) = π *ᵥ Lb b 0 := by
        rw [map_zero, Matrix.mulVec_zero, hLapp, ← hvc]
        funext r
        simpa using congrFun hv r.succ
      rw [hvc, hπ b hw]
      funext i
      exact Fin.cases rfl (fun j => rfl) i
    exact ⟨hΦ, (LinearMap.injective_iff_surjective
      (f := (sliceDeriv π (fderiv ℂ (γ b) (s b)) : (Fin (k + 1) → ℂ) →ₗ[ℂ] _))).1 hΦ⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PWeierstrassFiniteness
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem WeierstrassFiniteness.proof (hE : FiniteModuloEliminate.Statement)
    (hI : FiniteModuloIntegral.Statement) : WeierstrassFiniteness.Statement := by
  intro σ _ x k f d A hf hpow g hg
  classical

  let L : Finset σ → (σ → ℂ) →L[ℂ] (Fin d ⊕ σ → ℂ) := fun S =>
    ContinuousLinearMap.pi (Sum.elim (fun j => (ContinuousLinearMap.proj j).comp A)
      (fun l => if l ∈ S then ContinuousLinearMap.proj l else 0))
  have hL : ∀ S z c, L S z c = Sum.elim (fun j => A z j) (fun l => if l ∈ S then z l else 0) c := by
    intro S z c
    rcases c with j | l
    · simp [L]
    · by_cases hl : l ∈ S <;> simp [L, hl]
  have key : ∀ T : Finset σ, IsFiniteModuloOver x f (L (Finset.univ \ T)) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      rw [Finset.sdiff_empty]
      let P : (Fin d ⊕ σ → ℂ) →L[ℂ] (σ → ℂ) :=
        ContinuousLinearMap.pi fun l => ContinuousLinearMap.proj (Sum.inr l)
      have hPL : ∀ z, P (L Finset.univ z) = z := fun z => by
        funext l; simp [P, hL]
      refine ⟨1, fun _ _ => 1, fun _ => analyticAt_const, fun g hg => ?_⟩
      refine ⟨fun _ y => g (P y), fun _ _ => 0, fun _ => ?_, fun _ => analyticAt_const,
        Eventually.of_forall fun z => by simp only [hPL]; simp⟩
      have hg' : AnalyticAt ℂ g (P (L Finset.univ x)) := by rw [hPL]; exact hg
      exact hg'.comp (P.analyticAt _)
    | insert l T hl ih =>
      have heq : L (Finset.univ \ insert l T) = (zeroCoordinate (Sum.inr l)).comp (L (Finset.univ \ T)) := by
        ext z c
        rw [ContinuousLinearMap.comp_apply, zeroCoordinate_apply, hL, hL]
        rcases c with j | l'
        · simp
        · by_cases h1 : l' = l
          · subst h1; simp
          · by_cases h2 : l' ∈ T <;> simp [h1, h2]
      rw [heq]
      obtain ⟨r, h, h', hh, hh', hev⟩ := hpow l
      refine hE σ (Fin d ⊕ σ) x k f _ (Sum.inr l) hf ih
        ⟨r, h, Sum.elim h' (fun _ _ => 0), hh, ?_, ?_⟩
      · rintro (j | l')
        · exact hh' j
        · exact analyticAt_const
      · filter_upwards [hev] with z hz
        simp only [zeroCoordinate_apply, hL, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
          Finset.mem_sdiff, Finset.mem_univ, hl, not_false_eq_true, and_self, if_true,
          reduceCtorEq, if_false, zero_mul, Finset.sum_const_zero, add_zero]
        exact hz
  have hfin := key Finset.univ
  obtain ⟨N, a, h, ha, hh, hev⟩ := hI σ (Fin d ⊕ σ) x k f _ hf hfin g hg

  let J : (Fin d → ℂ) →L[ℂ] (Fin d ⊕ σ → ℂ) :=
    ContinuousLinearMap.pi (Sum.elim (fun j => ContinuousLinearMap.proj j) (fun _ => 0))
  have hJ : ∀ z, J (A z) = L (Finset.univ \ Finset.univ) z := fun z => by
    funext c; rcases c with j | l <;> simp [J, hL]
  refine ⟨N, fun j w => a j (J w), h, fun j => ?_, hh, ?_⟩
  · have haj : AnalyticAt ℂ (a j) (J (A x)) := by rw [hJ]; exact ha j
    exact haj.comp (J.analyticAt _)
  · filter_upwards [hev] with z hz
    simpa only [hJ] using hz

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.ProjDegreeEqFinrankAdjoin
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

noncomputable section

namespace Objects

variable {n d : ℕ}

theorem linPoly_eq (A : Matrix (Fin d) (Fin n) ℂ) (i : Fin d) :
    linPoly A.mulVecLin i = GroundTheory.Heights₂.Heights.ComplexSets.linPoly A i := by
  simp [linPoly, GroundTheory.Heights₂.Heights.ComplexSets.linPoly]

theorem projHom_eq (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) :
    GroundTheory.Heights₂.Heights.ComplexSets.projHom J A = projAlgHom J A.mulVecLin := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [GroundTheory.Heights₂.Heights.ComplexSets.projHom, GroundTheory.Heights₂.Heights.ComplexSets.pullback,
    projAlgHom, linPoly_eq]

theorem isFiniteProjection_iff (J : Ideal (MvPolynomial (Fin n) ℂ))
    (A : Matrix (Fin d) (Fin n) ℂ) :
    GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A ↔
      IsFiniteProjection J A.mulVecLin := by
  rw [IsFiniteProjection, ← projHom_eq]
  exact ⟨fun h => ⟨h.injective, h.finite⟩, fun h => ⟨h.1, h.2⟩⟩

theorem orthoRows_eq (d n : ℕ) :
    GroundTheory.Heights₂.Heights.ComplexSets.orthoRows d n = unitaryRows d n :=
  rfl

section Degree

variable (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime]

end Degree

end Objects

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAreaGraphPiece
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal NNReal

noncomputable section

def AreaGraphPiece.Statement : Prop :=
  ∀ (k m : ℕ) (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m))
    (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) (δ : ℝ≥0)
    (t : Set (EuclideanSpace ℝ (Fin k))), δ < 1 → ApproximatesLinearOn F A t δ →
      μH[(k : ℝ)] (realGraphPt F '' t) ≤
          ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ k *
            ENNReal.ofReal (graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) *
              μH[(k : ℝ)] t ∧
        ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k *
            ENNReal.ofReal (graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) *
              μH[(k : ℝ)] t ≤
          μH[(k : ℝ)] (realGraphPt F '' t)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchFillDimension
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def BranchFillDimension.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial σ ℂ) (w : σ → ℂ)
    (k : ℕ) (r : ℝ) (φ : (Fin k → ℂ) → σ → ℂ) (B : Set (σ → ℂ)),
    I.IsPrime → h ∉ I → w ∈ zeroSetIn I →
    DifferentiableOn ℂ φ (Metric.ball 0 r) → Set.InjOn φ (Metric.ball 0 r) →
    Set.MapsTo φ (Metric.ball 0 r) (zeroSetIn I) → B ∈ 𝓝 w →
    (zeroSetIn I ∩ B) \ {z | eval z h = 0} ⊆ φ '' Metric.ball 0 r →
    ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (k : ℕ)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchInverseHolomorphic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def BranchInverseHolomorphic.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial σ ℂ) (w : σ → ℂ)
    (k : ℕ) (r : ℝ) (φ : (Fin k → ℂ) → σ → ℂ) (B : Set (σ → ℂ)),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → h ∉ I → w ∈ zeroSetIn I →
    DifferentiableOn ℂ φ (Metric.ball 0 r) → Set.InjOn φ (Metric.ball 0 r) →
    Set.MapsTo φ (Metric.ball 0 r) (zeroSetIn I) → B ∈ 𝓝 w →
    (zeroSetIn I ∩ B) \ {z | eval z h = 0} ⊆ φ '' Metric.ball 0 r →
    ∃ ψ : (σ → ℂ) → Fin k → ℂ, HolomorphicOnSubset ψ (φ '' Metric.ball 0 r) ∧
      ∀ t ∈ Metric.ball 0 r, ψ (φ t) = t

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConeAvoidsExists
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def ConeAvoidsExists.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
      ∃ (A : Matrix (Fin d) (Fin n) ℂ) (N : ℕ), ConeAvoids J A N

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConeAvoidsFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def ConeAvoidsFinite.Statement : Prop :=
  ∀ (n d N : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ),
    ConeAvoids J A N → (projHom J A).toRingHom.Finite

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConeAvoidsOpen
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def ConeAvoidsOpen.Statement : Prop :=
  ∀ (n d N : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)),
    IsZariskiOpen {A : Matrix (Fin d) (Fin n) ℂ | ConeAvoids J A N}

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

