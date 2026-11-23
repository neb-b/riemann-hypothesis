module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0012

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PullWMemFibre
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M

namespace IntersectionWithSection

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]


omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem comp_mem_mcPts {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {P' : Ideal (MRing ι')} {z' : (Σ k', ι' k') → ℂ} (hz : z' ∈ mcPts P') :
    (fun p => z' (v p)) ∈ mcPts (imageZ v P') := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i', hi'⟩ := hz.1 (κ k)
    obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
    have h2 : p.1 = k := hv.1 (by rw [← hv.2.2.1 p, hp])
    obtain ⟨pk, pi⟩ := p
    simp only at h2
    subst h2
    exact ⟨pi, show z' (v ⟨pk, pi⟩) ≠ 0 by rw [hp]; exact hi'⟩
  · have h := hz.2 _ (Ideal.mem_comap.mp hf)
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_rename, eval_rename] at h
    exact h

theorem pullW_mem_fibre {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {P' J' : Ideal (MRing ι')} {n : ℕ} (hP : IsArithVar (imageZ v P') (n + 1)) (R : AnLogRes P' J' n)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {x : R.X}
    (h0 : Ψ (segre (pullPt R v x)) 0 ≠ 0) : pullW R v Ψ x ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre (imageZ v P') Ψ (pullQ R v Ψ x) := by
  classical
  obtain ⟨k0⟩ := hP.1
  let c : K → ℂ := Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre (pullPt R v x)) 0)⁻¹
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [c, h0]
    · simp [c, Function.update_of_ne hk]
  have hpc : ∏ k, c k = (Ψ (segre (pullPt R v x)) 0)⁻¹ := by
    simp [c, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  refine ⟨fun p => c p.1 * pullPt R v x p,
    mcPts_smul hP.2.1.2.1 c hc (comp_mem_mcPts hv (R.mem x x (R.mem_U x))), ?_, ?_⟩
  · rw [segre_smul, hpc]; rfl
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [pullW, h0]
    · simp only [pullW, map_smul, Pi.smul_apply, smul_eq_mul, Fin.cons_succ, pullQ]
      rw [div_eq_inv_mul]

end IntersectionWithSection


open IntersectionWithSection in
theorem IntersectionWithSection.proof (hE : ResExistsStatement) (hPush : pullbackPushforward_holds.Statement)
    (hCount : PullbackDegreeCount.Statement) (hDens : pullbackDensity_holds.Statement) : IntersectionWithSection.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G J L L' A A' s hv hP' hP hJ hL hLL' hA hAA' hs
  classical
  have hA' := ArithmeticIntersectionIntegral.isSmoothHerm_pull hv hA hAA'
  have hL' : ∀ j, IsSmoothHerm (L' j) := fun j => ArithmeticIntersectionIntegral.isSmoothHerm_pull hv (hL j) (hLL' j)
  have hs' : IsSectionOn P' A' (rename v s) := by
    obtain ⟨a, hAa, hsa, hsP⟩ := hs
    refine ⟨Function.extend κ a 0, fun k' => ?_, ArithmeticIntersectionIntegral.isMultiHomog_rename hv hsa,
      fun h => hsP (Ideal.mem_comap.mpr h)⟩
    rw [hAA'.1, pullDeg]
    by_cases h : ∃ k, κ k = k'
    · obtain ⟨k, rfl⟩ := h
      rw [hv.1.extend_apply, hv.1.extend_apply, hAa k]
    · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]
      simp
  obtain ⟨J', ⟨R⟩⟩ := exists_anLogRes hE hP'
  obtain ⟨Ψ, hΨ⟩ := goodProjExists K ι (imageZ v P') n hP
  obtain ⟨hnull, hfin⟩ := hPush K ι K' ι' κ v P' J' n R Ψ hv hP' hP hΨ
  rw [ptsIntegral_eq_mInt' hE resBridge R hP' hL' hA' hs', ptsIntegral_eq_at hE resBridge hP hΨ hL hA hs,
    pushForward_null R.A _ (fun j => potOf_isPotential R (L' j) (hL' j)) (pullQ R v Ψ) (pullBad R v Ψ) hnull
      (fun x hx j hj => by
        by_contra h
        exact hx (Or.inr ⟨j, hj, h⟩)) hfin _ (brIntegrable R L' A' (rename v s) hP' hL' hA' hs'),
    ptsIntegralAt, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hCount K ι K' ι' κ v P' J' n G J R Ψ hv hP' hP hJ hΨ,
    hDens K ι K' ι' κ v P' J' n R Ψ L L' A A' s hv hP' hP hΨ hL hLL' hA hAA' hs] with y hc hd
  have hSf := hfin y
  have hFf := fibreFinite K ι (imageZ v P') n Ψ hP hΨ y
  have hmaps : ∀ x ∈ hSf.toFinset, pullW R v Ψ x ∈ hFf.toFinset := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx ⊢
    have h0 : Ψ (segre (pullPt R v x)) 0 ≠ 0 := fun h => hx.2 (Or.inl (Or.inr h))
    have hw := pullW_mem_fibre hv hP R Ψ h0
    rwa [show pullQ R v Ψ x = y from hx.1] at hw
  rw [finsum_mem_eq_finite_toFinset_sum _ hSf, finsum_mem_eq_finite_toFinset_sum _ hFf, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun x hx => hd x ((Set.Finite.mem_toFinset hSf).mp hx)).trans ?_
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hset : ({x | pullQ R v Ψ x = y ∧ pullW R v Ψ x = w} \ pullBad R v Ψ) =
      ↑(hSf.toFinset.filter fun x => pullW R v Ψ x = w) := by
    ext x
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_singleton_iff]
    tauto
  have hcw := hc w ((Set.Finite.mem_toFinset hFf).mp hw)
  rw [hset, Set.ncard_coe_finset] at hcw
  exact_mod_cast hcw

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsBlockRatioAlg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def BlockRatioAlg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    ∀ q c : Σ k', ι' k', q.1 = c.1 → (X c : MRing ι') ∉ P' →
      ∃ (m : ℕ) (A : Fin (m + 1) → MRing ι) (a : K → ℕ), (∀ j, IsMultiHomog (A j) a) ∧
        A (Fin.last m) ∉ imageZ v P' ∧
        ∑ j : Fin (m + 1), rename v (A j) * X q ^ (j : ℕ) * X c ^ (m - j : ℕ) ∈ P'

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFFibreMult
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def PFFibreMult.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d e : ℕ)
    (G : GenFibre v P') (s : MRing ι') (W : Ideal (MRing ι')),
    IsBlockMap κ v → IsArithVar P' e → IsArithVar (imageZ v P') d →
    W ∈ divSupp P' s → IsHorizontal W → imageZ v W = imageZ v P' →
    multAt (fibreIdeal κ G ⊔ Ideal.span {baseSubst κ G s}) (fibreOf κ G W) = multAt (P' ⊔ Ideal.span {s}) W

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocRing
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

section Semiloc

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def semiLocRing (P : Ideal (MRing ι)) (𝒲 : Set (Ideal (MRing ι))) : Subring (FractionRing (MRing ι ⧸ P)) :=
  Subring.closure {x | ∃ (u w : MRing ι) (a : K → ℕ)
    (hw : Ideal.Quotient.mk P w ∈ nonZeroDivisors (MRing ι ⧸ P)),
    (∀ W ∈ 𝒲, w ∉ W) ∧ IsMultiHomog u a ∧ IsMultiHomog w a ∧
      x = IsLocalization.mk' (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) ⟨_, hw⟩}

end Semiloc

section Block

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

def fibreOver (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (W : Ideal (MRing ι)) :
    Set (Ideal (MRing ι')) :=
  {W' | IsMultiProjPrime W' ∧ P' ≤ W' ∧ imageZ v W' = W}


open Classical in
theorem rename_isMultiHomog {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    IsMultiHomog (rename v f) (Function.extend κ a 0) := by
  intro m' hm' k'
  rw [support_rename_of_injective hv.2.1, Finset.mem_image] at hm'
  obtain ⟨m, hm, rfl⟩ := hm'
  have hblock : ∀ (F : (Σ k', ι' k') → ℕ), ∑ i, F ⟨k', i⟩ = ∑ q, if q.1 = k' then F q else 0 := by
    intro F
    rw [Fintype.sum_sigma, Finset.sum_eq_single k']
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  rw [hblock]
  have h1 : (∑ q, if q.1 = k' then Finsupp.mapDomain v m q else 0) =
      ∑ p, if κ p.1 = k' then m p else 0 := by
    have := Finsupp.sum_mapDomain_index_inj (h := fun (q : Σ k', ι' k') (n : ℕ) => if q.1 = k' then n else 0)
      (s := m) hv.2.1
    rw [Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp)] at this
    simpa [hv.2.2.1] using this
  have h2 : (∑ p : Σ k, ι k, if κ p.1 = k' then m p else 0) = ∑ k, if κ k = k' then a k else 0 := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · exact hf m hm k
    · simp
  convert h1.trans h2
  by_cases h : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := h
    rw [hv.1.extend_apply, Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hv.1.ne hb]
    · simp
  · rw [Function.extend_apply' _ _ _ h]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    rw [if_neg fun hk => h ⟨k, hk⟩]

abbrev quotMapZ (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) :
    MRing ι ⧸ imageZ v P' →+* MRing ι' ⧸ P' :=
  Ideal.quotientMap P' (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom le_rfl

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem quotMapZ_injective (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) :
    Function.Injective (quotMapZ v P') :=
  Ideal.quotientMap_injective


omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem imageZ_isPrime_of_prime (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) [P'.IsPrime] :
    (imageZ v P').IsPrime :=
  Ideal.comap_isPrime _ _

def fracMapZ (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) [P'.IsPrime] :
    FractionRing (MRing ι ⧸ imageZ v P') →+* FractionRing (MRing ι' ⧸ P') :=
  haveI := imageZ_isPrime_of_prime v P'
  IsFractionRing.lift (g := (algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P'))).comp (quotMapZ v P'))
    ((IsFractionRing.injective (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P'))).comp (quotMapZ_injective v P'))

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem fracMapZ_algebraMap (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) [P'.IsPrime] (f : MRing ι) :
    fracMapZ v P' (algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') f)) =
      algebraMap _ _ (Ideal.Quotient.mk P' (rename v f)) := by
  have := imageZ_isPrime_of_prime v P'
  unfold fracMapZ
  rw [IsFractionRing.lift_algebraMap]
  rfl

theorem fracMapZ_mem {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (P' : Ideal (MRing ι')) [P'.IsPrime] (W : Ideal (MRing ι)) (x : FractionRing (MRing ι ⧸ imageZ v P'))
    (hx : x ∈ locRing (imageZ v P') W) : fracMapZ v P' x ∈ semiLocRing P' (fibreOver v P' W) := by
  have := imageZ_isPrime_of_prime v P'
  have hle : locRing (imageZ v P') W ≤ (semiLocRing P' (fibreOver v P' W)).comap (fracMapZ v P') := by
    rw [locRing, Subring.closure_le]
    rintro _ ⟨u, w, a, hw, hwW, hu, hwa, rfl⟩
    rw [SetLike.mem_coe, Subring.mem_comap]
    have hw0 : rename v w ∉ P' := by
      intro h
      apply nonZeroDivisors.ne_zero hw
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact h
    have hw' : Ideal.Quotient.mk P' (rename v w) ∈ nonZeroDivisors (MRing ι' ⧸ P') :=
      mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    apply Subring.subset_closure
    refine ⟨rename v u, rename v w, Function.extend κ a 0, hw', ?_, rename_isMultiHomog hv hu,
      rename_isMultiHomog hv hwa, ?_⟩
    · rintro W' ⟨-, -, hW'⟩ hmem
      apply hwW
      rw [← hW']
      exact hmem
    · rw [IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div, map_div₀]
      exact congrArg₂ (· / ·) (fracMapZ_algebraMap v P' u) (fracMapZ_algebraMap v P' w)
  exact hle hx

def locToSemiloc {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (P' : Ideal (MRing ι')) [P'.IsPrime] (W : Ideal (MRing ι)) :
    locRing (imageZ v P') W →+* semiLocRing P' (fibreOver v P' W) :=
  (fracMapZ v P').restrict _ _ (fun x hx => fracMapZ_mem hv P' W x hx)

theorem locToSemiloc_coe {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (P' : Ideal (MRing ι')) [P'.IsPrime] (W : Ideal (MRing ι)) (x : locRing (imageZ v P') W) :
    ((locToSemiloc hv P' W x : semiLocRing P' (fibreOver v P' W)) : FractionRing (MRing ι' ⧸ P')) =
      fracMapZ v P' x :=
  rfl

end Block

namespace SemilocRing

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


open Classical in
def blkW : (Σ k, ι k) → K → ℕ := fun p => Pi.single p.1 1


open Classical in
theorem isMultiHomog_of_wh {s : MRing ι} {a : K → ℕ} (h : IsWeightedHomogeneous (blkW (ι := ι)) s a) :
    IsMultiHomog s a := by
  intro m hm k
  rw [← h (mem_support_iff.mp hm), Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp),
    Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp [blkW]
  · intro b _ hb
    simp [blkW, Ne.symm hb]
  · simp

theorem isMultiHomog_coordPow (i : ∀ k, ι k) (α : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k) α := by
  have h : IsWeightedHomogeneous (blkW (ι := ι)) (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k)
      (∑ k, α k • blkW (ι := ι) ⟨k, i k⟩) :=
    IsWeightedHomogeneous.prod _ _ _ fun k _ => (isWeightedHomogeneous_X ℤ _ _).pow (α k)
  have e : (∑ k, α k • blkW (ι := ι) ⟨k, i k⟩) = α := by
    funext k
    simp only [blkW, Finset.sum_apply]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [e] at h
  exact isMultiHomog_of_wh h

end SemilocRing

theorem exists_form_notMem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {W : Ideal (MRing ι)}
    (hW : IsRelevant W) (hWp : W.IsPrime) (α : K → ℕ) : ∃ t : MRing ι, IsMultiHomog t α ∧ t ∉ W := by
  choose i hi using hW
  refine ⟨∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k, SemilocRing.isMultiHomog_coordPow i α, fun h => ?_⟩
  obtain ⟨k, -, hk⟩ := hWp.prod_mem_iff.mp h
  exact hi k (hWp.mem_of_pow_mem _ hk)

section Example

end Example

end GroundTheory.Heights₂.Heights.Inter
end
end

