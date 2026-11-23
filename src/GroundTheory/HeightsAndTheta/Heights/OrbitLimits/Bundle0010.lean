module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CurveFilt
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0004

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.IntNumCompPerm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.NumbersDVR

universe u v w

theorem intNum_comp_perm {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
    (P : Ideal (MRing ι F)) {n : ℕ} (bs : Fin n → K → ℤ) (σ : Equiv.Perm (Fin n)) :
    intNum F P (bs ∘ σ) = intNum F P bs := by
  unfold intNum
  rw [FieldNumbers.mixedDiff_comp_perm]

theorem SymmStatement.of_type (F : Type u) [Field F] {K : Type} [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] : SymmStatement F ι := by
  classical
  intro I hI V n L σ hV
  have hA : ∀ L' : Fin n → K → ℤ, I V n L' = intNum F V L' := fun L' =>
    Numbers.agree_of FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
      FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full I hI V n L' hV
  rw [hA (L ∘ σ), hA L]
  exact intNum_comp_perm V L σ

theorem SymmStatement.of_found (hR : SymmRelabel.Statement.{u, v, w, 0, 0}) {K : Type v}
    [Fintype K] (F : Type u) [Field F] (ι : K → Type w) [∀ k, Fintype (ι k)] :
    SymmStatement F ι := by
  classical
  let e : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  refine hR F K ι (Fin (Fintype.card K)) (fun j => Fin (Fintype.card (ι (e.symm j)))) e
    (fun k => (Fintype.equivFin (ι k)).trans (finCongr ?_)) (SymmStatement.of_type F _)
  exact congrArg (fun x => Fintype.card (ι x)) (e.symm_apply_apply k).symm

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDehomogPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ChartDehomogPrime.proof : ChartDehomogPrime.Statement := by
  intro F _ n W t hW ht
  have := hW.isPrime
  set a : MvPolynomial (Fin n) F ⧸ W := Ideal.Quotient.mk W (linForm t) with ha_def
  have ha : a ≠ 0 := fun h => ht (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let A := Localization.Away a
  have : IsDomain A := IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  let v : A := IsLocalization.Away.invSelf a
  let φ : MvPolynomial (Fin n) F →ₐ[F] A :=
    (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ W) A).comp (Ideal.Quotient.mkₐ F W)
  have hφ : ∀ g, aeval (fun m => φ (X m)) g = φ g := fun g => by
    rw [← comp_aeval_apply]; simp
  let ψ : MvPolynomial (Fin n) F →ₐ[F] A := aeval fun m => v * φ (X m)
  have hhom : ∀ {g : MvPolynomial (Fin n) F} {k : ℕ}, g.IsHomogeneous k → ψ g = v ^ k * φ g :=
    fun hg => by rw [← hφ]; exact ChartLocDomain.aeval_mul_of_isHomogeneous hg _ _
  have hℓ : (linForm t).IsHomogeneous 1 := ChartLocDomain.linForm_isHomogeneous t
  have hspan : Ideal.span {linForm t - 1} ≤ RingHom.ker ψ := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one,
      hhom hℓ, pow_one]
    have : φ (linForm t) = algebraMap _ A a := rfl
    rw [this, mul_comm, IsLocalization.Away.mul_invSelf, sub_self]
  have hle : W ⊔ Ideal.span {linForm t - 1} ≤ RingHom.ker ψ := by
    refine sup_le (fun g hg => ?_) hspan
    set_option synthInstance.maxHeartbeats 100000 in
      rw [RingHom.mem_ker, ← sum_homogeneousComponent g, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hhom (homogeneousComponent_isHomogeneous k g)]
    have : φ (homogeneousComponent k g) = 0 := by
      simp [φ, Ideal.Quotient.eq_zero_iff_mem.mpr (hW.isHomog g hg k)]
    rw [this, mul_zero]
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin n) F ⧸ W) A) :=
    IsLocalization.injective A (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  have hker : RingHom.ker ψ ≤ W ⊔ Ideal.span {linForm t - 1} := by
    intro g hg
    obtain ⟨G, D, hG, hGg⟩ := ChartHomogenise.exists_homogeneous_sub_mem_span (linForm t) g hℓ
    have hψG : ψ G = 0 := by
      have h1 : ψ (G - g) = 0 := hspan hGg
      rw [map_sub, RingHom.mem_ker.mp hg, sub_zero] at h1
      exact h1
    rw [hhom hG] at hψG
    have h1 : algebraMap _ A (Ideal.Quotient.mk W G) = 0 :=
      calc algebraMap _ A (Ideal.Quotient.mk W G)
          = (algebraMap _ A a * v) ^ D * φ G := by
            rw [IsLocalization.Away.mul_invSelf, one_pow, one_mul]; rfl
        _ = algebraMap _ A a ^ D * (v ^ D * φ G) := by ring
        _ = 0 := by rw [hψG, mul_zero]
    have hGW : G ∈ W := Ideal.Quotient.eq_zero_iff_mem.mp (hinj (h1.trans (map_zero _).symm))
    have e : g = G - (G - g) := by ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left hGW) (Ideal.mem_sup_right hGg)
  rw [← le_antisymm hker hle]
  exact RingHom.ker_isPrime ψ

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartFiniteIrrel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

theorem ChartFiniteIrrel.proof : ChartFiniteIrrel.Statement.{u, v, w} := by
  intro K _ ι _ F _ V f i hV hf hirr
  classical
  let _ := MvPolynomial.weightedGradedAlgebra F (mw (ι := ι))
  let M : Ideal (MRingOver F ι) :=
    Ideal.span (weightedHomogeneousSubmodule F (mw (ι := ι)) (fun _ => 1) : Set (MRingOver F ι))
  have hMrad : M ≤ (V ⊔ Ideal.span {f}).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    refine le_sInf fun W hW => Ideal.span_le.mpr fun x hx => ?_
    have h := hirr W hW
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant, not_forall, not_exists, not_not] at h
    obtain ⟨k, hk⟩ := h
    exact weighted_le_of_irrel (e := fun _ => 1) hk le_rfl hx
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hMrad (IsNoetherian.noetherian M)
  have hA : ∀ t, N ≤ t → weightedHomogeneousSubmodule F (mw (ι := ι)) (fun _ => t) ≤
      (V ⊔ Ideal.span {f}).restrictScalars F := fun t ht _ hh =>
    hN (Ideal.pow_le_pow_right ht (ChartFiniteIrrel.weighted_le_pow t hh))
  have hVh : V.IsHomogeneous (weightedHomogeneousSubmodule F (mw (ι := ι))) := by
    obtain ⟨S₀, hS₀, rfl⟩ := hV
    exact Ideal.homogeneous_span _ S₀ fun x hx =>
      let ⟨a, ha⟩ := hS₀ x hx; ⟨a, mem_weighted_of_isMultiHomog ha⟩
  let π := (Ideal.Quotient.mkₐ F (ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal V i)).toLinearMap
  let B : ℕ → Submodule F (MRingOver F ι ⧸ ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal V i) := fun t =>
    (weightedHomogeneousSubmodule F (mw (ι := ι)) (fun _ => t)).map π
  have hmono : ∀ t, B t ≤ B (t + 1) := by
    rintro t _ ⟨h, hh, rfl⟩
    refine ⟨h * ∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ (fun _ : K => 1) k,
      SetLike.mul_mem_graded hh (mem_weighted_of_isMultiHomog (isMultiHomog_coordProd i _)), ?_⟩
    simp [π, map_prod, mk_chartIdeal_X_self]
  have hstep : ∀ t, N ≤ t + 1 → B (t + 1) ≤ (B t).map (LinearMap.mulLeft F (π f)) := by
    rintro t ht _ ⟨h, hh, rfl⟩
    have h2 : h ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) (fun _ => t + 1) ⊓
        (V ⊔ Ideal.span {f}).restrictScalars F := ⟨hh, hA _ ht hh⟩
    rw [sup_span_inf_eq' hVh (mem_weighted_of_isMultiHomog hf) (d := fun _ => t + 1) (fun _ => Nat.le_add_left 1 t),
      show ((fun _ : K => t + 1) - fun _ => 1) = fun _ => t from funext fun _ => by simp] at h2
    obtain ⟨v, ⟨-, hv⟩, _, ⟨g, hg, rfl⟩, rfl⟩ := Submodule.mem_sup.mp h2
    refine ⟨π g, ⟨g, hg, rfl⟩, ?_⟩
    have hv0 : Ideal.Quotient.mk (ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal V i) v = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left hv)
    simp [π, hv0]
  have heq : ∀ t, N ≤ t → B t = B (t + 1) := fun t ht =>
    Submodule.eq_of_le_of_finrank_le (hmono t)
      ((Submodule.finrank_mono (hstep t (by omega))).trans (Submodule.finrank_map_le _ _))
  have hconst : ∀ t, N ≤ t → B t = B N := fun t ht => by
    induction t, ht using Nat.le_induction with
    | base => rfl
    | succ t ht ih => rw [← heq t ht, ih]
  have htop : B N = ⊤ := by
    refine eq_top_iff.mpr fun a _ => ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨e₀, he₀⟩ := exists_homog_chart V i b
    obtain ⟨b', hb', hbb⟩ := he₀ (fun _ => N + ∑ k, e₀ k) fun k =>
      le_add_left (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))
    rw [← hconst _ (Nat.le_add_right _ _)]
    exact ⟨b', hb', hbb⟩
  rw [Module.finite_def, ← htop]
  exact Module.Finite.iff_fg.mp inferInstance

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ProjContract
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

universe u

namespace ProjContract

theorem finsum_mul_eq_sum {α : Type*} (D : α →₀ ℤ) (J : α → ℤ) :
    ∑ᶠ W, D W * J W = D.sum fun W m => m * J W := by
  classical
  rw [Finsupp.sum, finsum_eq_sum_of_support_subset]
  intro W hW
  rw [Function.mem_support] at hW
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  intro h0
  exact hW (by rw [h0, zero_mul])

section Theory

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]


omit [DecidableEq K] in
theorem ratDiv_eq (P : Ideal (NumbersDVR.MRing ι F)) (f g : NumbersDVR.MRing ι F)
    (W : Ideal (NumbersDVR.MRing ι F)) :
    NumbersDVR.ratDiv P f g W = AI.I1.ratDiv P f g W := by
  simp only [NumbersDVR.ratDiv, AI.I1.ratDiv, Finsupp.sub_apply, Finsupp.mapRange_apply]
  rw [Bridge.divCycle_eq, Bridge.divCycle_eq]

theorem isIntersectionTheory (I : AI.I1.IFamily F ι) (hI : AI.I1.IsFieldIntersection I) :
    FieldNumbers.IsIntersectionTheory F I := by
  constructor
  · intro P hP h0
    choose i hi using hP.relevant
    have hd := (FieldNumbers.relDim_eq_iff_hasRelDim P 0).mp h0
    have hV : AI.I1.IsProjVarF P 0 := ⟨(Bridge.isMultiProjPrime_iff P).mp hP, hd⟩
    have h1 := hI.1 P ![] i hV hi
    have h2 := NumbersDVR.IntNumPoint.proof FieldNumbers.IntNumBase.full F K ι P i hP hd hi
    have h3 := (FieldNumbers.IntNumBase.full F K ι P hP h0).2
    have h4 : FieldNumbers.resDeg P = Module.finrank F
        (@FieldNumbers.homFracDegZero _ _ _ _ _ P hP.isPrime) := by
      rw [FieldNumbers.resDeg, dite_eq_left hP.isPrime]
    rw [h1, ← h2, h3, h4]
  · intro P n hP hn bf bg f g hf hg hfP hgP bs
    have hd := (FieldNumbers.relDim_eq_iff_hasRelDim P (n + 1)).mp hn
    rw [hI.2 P n bs _ f g ⟨(Bridge.isMultiProjPrime_iff P).mp hP, hd⟩
      ⟨bf, bg, (Bridge.isMultiHomog_iff f bf).mp hf, (Bridge.isMultiHomog_iff g bg).mp hg, hfP, hgP,
        fun k => rfl⟩]
    simp only [NumbersDVR.cycEval, AI.I1.cycEval, ratDiv_eq]
    exact (finsum_mul_eq_sum _ _).symm

end Theory

section Image

variable {F : Type u} [Field F] {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}

def emb (hv : AI.I1.IsBlockMap κ v) : K ↪ K' := ⟨κ, hv.1⟩

theorem range_eq (hv : AI.I1.IsBlockMap κ v) :
    Set.range v = Set.range (FieldNumbers.blockIncl (emb hv) ι') := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    have h := hv.2.2.1 p
    revert h
    generalize v p = q
    obtain ⟨a, b⟩ := q
    rintro (rfl : a = κ p.1)
    exact ⟨⟨p.1, b⟩, rfl⟩
  · rintro ⟨⟨k, x⟩, rfl⟩
    exact hv.2.2.2 _ ⟨k, rfl⟩

def blockEquiv (hv : AI.I1.IsBlockMap κ v) : (Σ k, ι k) ≃ (Σ k, ι' (emb hv k)) :=
  (Equiv.ofInjective v hv.2.1).trans ((Set.equivOfEq (range_eq hv)).trans
    (Equiv.ofInjective _ (FieldNumbers.PFContracted.blockIncl_injective_of_embedding (emb hv) ι')).symm)

theorem blockIncl_blockEquiv (hv : AI.I1.IsBlockMap κ v) (p : Σ k, ι k) :
    FieldNumbers.blockIncl (emb hv) ι' (blockEquiv hv p) = v p := by
  simp [blockEquiv, Equiv.apply_ofInjective_symm]

theorem imageVar_eq (hv : AI.I1.IsBlockMap κ v) (V' : Ideal (Geo.MRingOver F ι')) :
    AI.I1.imageVar F v V' = (FieldNumbers.contractPrime (emb hv) V').comap
      (rename (blockEquiv hv) : Geo.MRingOver F ι →ₐ[F] _).toRingHom := by
  ext x
  simp only [AI.I1.imageVar, FieldNumbers.contractPrime, Ideal.mem_comap, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, rename_rename]
  have : (FieldNumbers.blockIncl (emb hv) ι' ∘ blockEquiv hv) = v := funext (blockIncl_blockEquiv hv)
  rw [this]

theorem ringKrullDim_imageVar (hv : AI.I1.IsBlockMap κ v) (V' : Ideal (Geo.MRingOver F ι')) :
    ringKrullDim (Geo.MRingOver F ι ⧸ AI.I1.imageVar F v V') =
      ringKrullDim (NumbersDVR.MRing (fun k => ι' (emb hv k)) F ⧸
        FieldNumbers.contractPrime (emb hv) V') := by
  rw [imageVar_eq hv]
  set J := FieldNumbers.contractPrime (emb hv) V'
  let e := (renameEquiv F (blockEquiv hv)).toRingEquiv
  refine ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ J e ?_)
  exact (Ideal.map_comap_of_surjective _ e.surjective J).symm

end Image

end ProjContract


open ProjContract in
theorem ProjContract.full :
    ∀ (F : Type u) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)],
      ReciprocityTheory.ChartRestriction.G.AI.I1.ProjContractStatement F ι ι' := by
  intro F _ K _ ι _ K' _ ι' _
  classical
  intro I' hI' κ v V' e d L hv hV' hVd hde
  have hrel : FieldNumbers.relDim V' = e := (FieldNumbers.relDim_eq_iff_hasRelDim V' e).mpr hV'.2
  have hV'f : NumbersDVR.IsMultiProjPrime V' := (Bridge.isMultiProjPrime_iff V').mpr hV'.1
  rw [FieldNumbers.IntNumUnique.full F K' ι' I' (isIntersectionTheory I' hI') V' hV'f e hrel]
  have hc : FieldNumbers.relDim (FieldNumbers.contractPrime (emb hv) V') = d := by
    refine (FieldNumbers.relDim_eq_iff_hasRelDim _ d).mpr ?_
    show ringKrullDim _ = _
    rw [← ringKrullDim_imageVar hv]
    exact hVd.2
  exact FieldNumbers.ProjectionFormulaContracted.full F K K' (emb hv) ι' V' hV'f e hrel
    (lt_of_eq_of_lt hc (FieldNumbers.PFContracted.natCast_lt_withBotWithTop hde)) L

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ProjDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers

noncomputable section

universe u

section Relabel

variable {K K' : Type} {ι : K → Type} {ι' : K' → Type} {κ : K → K'}
  {v : (Σ k, ι k) → (Σ k', ι' k')}

def blockVar (hb : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v) (p : Σ k, ι k) : Σ k, ι' (κ k) :=
  ⟨p.1, cast (congrArg ι' (hb.2.2.1 p)) (v p).2⟩

theorem blockIncl_blockVar (hb : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v) (p : Σ k, ι k) :
    blockIncl ⟨κ, hb.1⟩ ι' (blockVar hb p) = v p := by
  refine Sigma.ext (hb.2.2.1 p).symm ?_
  exact (cast_heq _ _)

def blockVarEquiv (hb : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v) : (Σ k, ι k) ≃ (Σ k, ι' (κ k)) :=
  Equiv.ofBijective (blockVar hb) (by
    have hI : Function.Injective (blockIncl ⟨κ, hb.1⟩ ι') := by
      rintro ⟨a, x⟩ ⟨b, y⟩ h
      obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
      cases hb.1 h1
      cases eq_of_heq h2
      rfl
    refine ⟨fun p q h => hb.2.1 ?_, fun ⟨k, a⟩ => ?_⟩
    · rw [← blockIncl_blockVar hb p, ← blockIncl_blockVar hb q, h]
    · obtain ⟨p, hp⟩ := hb.2.2.2 ⟨κ k, a⟩ ⟨k, rfl⟩
      exact ⟨p, hI ((blockIncl_blockVar hb p).trans hp)⟩)

theorem imageVar_eq_comap {F : Type u} [Field F] (hb : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v)
    (V' : Ideal (MRing ι' F)) :
    ReciprocityTheory.ChartRestriction.G.AI.I1.imageVar F v V' =
      (contractPrime ⟨κ, hb.1⟩ V').comap (rename (blockVarEquiv hb)) := by
  ext f
  unfold ReciprocityTheory.ChartRestriction.G.AI.I1.imageVar contractPrime
  simp only [Ideal.mem_comap]
  have hfun : (blockIncl ⟨κ, hb.1⟩ ι' ∘ blockVarEquiv hb) = v := funext (blockIncl_blockVar hb)
  have e : rename (blockIncl ⟨κ, hb.1⟩ ι') (rename (blockVarEquiv hb) f) = rename v f := by
    rw [rename_rename, hfun]
  exact iff_of_eq (congrArg (· ∈ V') e.symm)

end Relabel

theorem ProjDeg.of_found (hPF : ProjectionFormulaDegree.Statement.{u})
    (hFn : FnDegRelDeg.Statement.{u}) {K K' : Type} [Fintype K] [Fintype K'] (F : Type u) [Field F]
    (ι : K → Type) [∀ k, Fintype (ι k)] (ι' : K' → Type) [∀ k, Fintype (ι' k)] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.ProjDegStatement F ι ι' := by
  classical
  intro I I' hI hI' κ v V' e L i' hb hV' hV hc
  have hA' := Numbers.agree_of IntNumBase.full CutRational.full ExistsForm.full
    DivCycleSupport.full I' hI' V' e (fun j => ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg κ (L j)) hV'
  have hA := Numbers.agree_of IntNumBase.full CutRational.full ExistsForm.full
    DivCycleSupport.full I hI _ e L hV
  rw [hA', hA]
  set j : K ↪ K' := ⟨κ, hb.1⟩
  have hP' : IsMultiProjPrime V' := (Objects.isMultiProjPrime_iff V').mpr hV'.1
  have := hP'.isPrime
  have himg := imageVar_eq_comap (F := F) hb V'

  have hRen := RenameIntNum.full F K K (fun k => ι k) (fun k => ι' (κ k)) (Equiv.refl K)
    (blockVarEquiv hb) (fun _ => rfl) (contractPrime j V') e L
  have hdimP : relDim (contractPrime j V') = (e : WithBot (WithTop ℤ)) := by
    refine relDim_eq_of_ringKrullDim _ e ?_
    have eq : MRing ι F ⧸ (contractPrime j V').comap (rename (blockVarEquiv hb)) ≃+*
        MRing (fun k => ι' (κ k)) F ⧸ contractPrime j V' :=
      Ideal.quotientEquiv _ _ (renameEquiv F (blockVarEquiv hb)).toRingEquiv
        (Ideal.map_comap_of_surjective _ (renameEquiv F (blockVarEquiv hb)).surjective _).symm
    have h2 : ringKrullDim (MRing ι F ⧸ (contractPrime j V').comap (rename (blockVarEquiv hb))) =
        ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      rw [← himg]
      exact hV.2
    exact (ringKrullDim_eq_of_ringEquiv eq).symm.trans h2
  obtain ⟨-, hPFe⟩ := hPF F K K' j ι' V' hP' e (relDim_eq_of_ringKrullDim V' e hV'.2) hdimP L
  have hfn := hFn F K K' ι ι' κ v hb V' hP' i' hc
  rw [himg, hRen, hfn]
  exact hPFe

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StLelongWeightLimit
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology Matrix
open GroundTheory.Heights₂.Heights (varInt SmoothNear localMult linEval linForm linForm_single euclPot)

def LelongWeightLimit.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (f k : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    SmoothNear (ComplexSets.zeroSet J) f → HasCompactSupport f →
    (∀ j, SmoothNear (ComplexSets.zeroSet J) (φ j)) →
    SmoothNear (ComplexSets.zeroSet J) k → (∀ x ∈ ComplexSets.zeroSet J, 0 < k x) →
      Tendsto (fun ε : ℝ =>
          varInt J (d + 1) f (vecCons (fun x => Real.log (‖linEval u x‖ ^ 2 + ε * k x ^ 2) / 2) φ))
        (𝓝[>] 0)
        (𝓝 (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
          (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d f φ))

end GroundTheory.Heights₂.Heights.Targets
end
end

