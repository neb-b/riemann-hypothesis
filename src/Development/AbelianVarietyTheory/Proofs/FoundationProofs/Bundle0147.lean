module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0140
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinWronskianNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimitiveQuotientLevelPrimeTo
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SndDualLiftAlgebraMap
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0144
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqOfSmulMkEqZero
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem exists_eq_of_smul_mk_eq_zero {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    (s : integralClosure (O0 p) Ω) (ω : Ω)
    (h : s • (Submodule.Quotient.mk ω : Frac p Ω) = 0) :
    ∃ t : integralClosure (O0 p) Ω, (t : Ω) = (s : Ω) * ω := by
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨t, ht⟩ := h
  exact ⟨t, by simpa [Algebra.smul_def] using ht⟩

theorem dlog_indep_pow_three : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n →
    ∀ x y zi qi : (integralClosure (O0 p) Ω), zS T n * zi = 1 → qS T n * qi = 1 →
    (x * zi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T n) +
      (y * qi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T n) = 0 →
    (∃ t, (p : (integralClosure (O0 p) Ω)) ^ 3 * x = (p : (integralClosure (O0 p) Ω)) ^ (n - 1) * t) ∧
    (∃ t, (p : (integralClosure (O0 p) Ω)) ^ 3 * y = (p : (integralClosure (O0 p) Ω)) ^ n * t) := by
  intro p _ Ω _ _ hp2 hclo T n hn x y zi qi hz hq hrel
  have hpΩ : (p : Ω) ≠ 0 := by
    haveI := GlobalTheory.K5.Basic.charZero_of_isClo hclo
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hrel' : ∑ i, (![x * zi, y * qi] : Fin 2 → integralClosure (O0 p) Ω) i •
      KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω)
        ((![zS T n, qS T n] : Fin 2 → integralClosure (O0 p) Ω) i) = 0 := by
    simpa [Fin.sum_univ_two] using hrel
  obtain ⟨F, hF⟩ := _root_.GlobalTheory.AlmostEt.kaehler_rel_local (O0 p) (integralClosure (O0 p) Ω) 2 _ _ hrel'
  obtain ⟨C, tr, m, a, b, hFC, htr⟩ := _root_.GlobalTheory.AlmostEt.TrTower.exists_trData_towerAlg p Ω hp2 hclo T F
  have hzT : zS T n ∈ towerAlg T := Algebra.subset_adjoin (Or.inl ⟨n, rfl⟩)
  have hqT : qS T n ∈ towerAlg T := Algebra.subset_adjoin (Or.inr ⟨n, rfl⟩)
  have hyC : ∀ i, (![zS T n, qS T n] : Fin 2 → integralClosure (O0 p) Ω) i ∈ C := by
    intro i; fin_cases i
    · exact htr.le hzT
    · exact htr.le hqT
  have hzΩ : T.ζ n * (zi : Ω) = 1 := by
    have := congrArg Subtype.val hz; simpa [zS] using this
  have hqΩ : T.qq n * (qi : Ω) = 1 := by
    have := congrArg Subtype.val hq; simpa [qS] using this
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  constructor
  · obtain ⟨Dz, hDz, hDzv⟩ := _root_.GlobalTheory.AlmostEt.zeta_derivation p Ω hclo T
    obtain ⟨D', hD', hD'v⟩ := _root_.GlobalTheory.AlmostEt.exists_derOn_ext (O0 p) (integralClosure (O0 p) Ω) (Frac p Ω)
      (towerAlg T) C tr m a b _ htr Dz hDz
    have h := hF C hFC hyC (Frac p Ω) D' hD'
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
    rw [hD'v _ hzT, hD'v _ hqT, (hDzv (k + 1)).1, (hDzv (k + 1)).2, smul_zero, smul_zero,
      add_zero, smul_smul] at h
    obtain ⟨t, ht⟩ := exists_eq_of_smul_mk_eq_zero _ _ h
    refine ⟨t, Subtype.ext ?_⟩
    push_cast at ht ⊢
    rw [ht]
    field_simp
    linear_combination (-((x : Ω) * (p : Ω) ^ (k + 1))) * hzΩ
  · obtain ⟨Dq, hDq, hDqv⟩ := GlobalTheory.T.exists_towerUnion_qDerivation_modIntegralClosure p Ω hclo T
    obtain ⟨D', hD', hD'v⟩ := _root_.GlobalTheory.AlmostEt.exists_derOn_ext (O0 p) (integralClosure (O0 p) Ω) (Frac p Ω)
      (towerAlg T) C tr m a b _ htr Dq hDq
    have h := hF C hFC hyC (Frac p Ω) D' hD'
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
    rw [hD'v _ hzT, hD'v _ hqT, (hDqv (k + 1)).1, (hDqv (k + 1)).2, smul_zero, smul_zero,
      zero_add, smul_smul] at h
    obtain ⟨t, ht⟩ := exists_eq_of_smul_mk_eq_zero _ _ h
    refine ⟨t, Subtype.ext ?_⟩
    push_cast at ht ⊢
    rw [ht]
    field_simp
    linear_combination (-(y : Ω)) * hqΩ

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteEtaleLocalSurjectiveOfIsSeparable
section
namespace GlobalTheory

open Polynomial IsLocalRing

open Polynomial IsLocalRing in
private lemma mem_smul_top_iff_of_linearEquiv_pi {V M ι : Type*} [CommRing V] [AddCommGroup M]
    [Module V M] [Fintype ι] [DecidableEq ι] (e : M ≃ₗ[V] (ι → V)) (J : Ideal V) (x : M) :
    x ∈ J • (⊤ : Submodule V M) ↔ ∀ i, e x i ∈ J := by
  constructor
  · intro hx
    have hle : J • (⊤ : Submodule V M) ≤
        (Submodule.pi Set.univ (fun _ : ι => J)).comap e.toLinearMap := by
      refine Submodule.smul_le.mpr fun r hr m _ => ?_
      simp only [Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, true_implies,
        LinearEquiv.coe_coe, map_smul, Pi.smul_apply, smul_eq_mul]
      exact fun i => J.mul_mem_right _ hr
    intro i
    have := hle hx
    simp only [Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, true_implies,
      LinearEquiv.coe_coe] at this
    exact this i
  · intro hx
    have hsum : x = ∑ i, e x i • e.symm (fun j => if i = j then 1 else 0) := by
      apply e.injective
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]
      exact pi_eq_sum_univ (e x)
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

open Polynomial IsLocalRing in
private lemma ideal_smul_top_eq_self {V : Type*} [CommRing V] (J : Ideal V) :
    J • (⊤ : Submodule V V) = J := by
  rw [smul_eq_mul, Ideal.mul_top]

open Polynomial IsLocalRing in
private lemma isAdicComplete_of_linearEquiv_pi {V M ι : Type*} [CommRing V] [AddCommGroup M]
    [Module V M] [Fintype ι] (e : M ≃ₗ[V] (ι → V)) (J : Ideal V) [IsAdicComplete J V] :
    IsAdicComplete J M := by
  classical
  have key : ∀ (n : ℕ) (x y : M), x ≡ y [SMOD J ^ n • (⊤ : Submodule V M)] ↔
      ∀ i, e x i ≡ e y i [SMOD J ^ n • (⊤ : Submodule V V)] := by
    intro n x y
    simp only [SModEq.sub_mem, mem_smul_top_iff_of_linearEquiv_pi e, map_sub, Pi.sub_apply,
      ideal_smul_top_eq_self]
  refine { haus' := fun x hx => ?_, prec' := fun f hf => ?_ }
  · apply e.injective
    funext i
    rw [map_zero]
    exact IsHausdorff.haus' (I := J) (e x i) fun n => by
      simpa using (key n x 0).1 (hx n) i
  · choose L hL using fun i => IsPrecomplete.prec' (I := J) (fun n => e (f n) i)
      (fun {m n} hmn => (key m _ _).1 (hf hmn) i)
    refine ⟨e.symm L, fun n => (key n _ _).2 fun i => ?_⟩
    simpa using hL i n


open Polynomial IsLocalRing in
theorem _root_.GlobalTheory.unramExt : _root_.ReciprocityTheory.ChartRestriction.G.Out.UnramExtSt := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Out.UnramExtSt
  intro V _ _ _ _ k' _ _ _ _
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element (ResidueField V) k'
  have hint : IsIntegral (ResidueField V) θ := .of_finite _ _
  obtain ⟨μ, hμmap, hμdeg, hμ⟩ := lifts_and_degree_eq_and_monic
    (map_surjective _ (residue_surjective (R := V)) (minpoly (ResidueField V) θ))
    (minpoly.monic hint)
  letI : Algebra V k' := ((algebraMap (ResidueField V) k').comp (residue V)).toAlgebra
  haveI : IsScalarTower V (ResidueField V) k' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hroot : eval₂ (algebraMap V k') θ μ = 0 := by
    rw [show algebraMap V k' = (algebraMap (ResidueField V) k').comp (residue V) from rfl,
      ← eval₂_map, hμmap]
    exact minpoly.aeval _ _
  let φ : AdjoinRoot μ →+* k' := AdjoinRoot.lift (algebraMap V k') θ hroot
  have hφ : ∀ g : V[X], φ (AdjoinRoot.mk μ g) = aeval θ g := fun g => by
    simp [φ, AdjoinRoot.lift_mk, aeval_def]
  have hadj : Algebra.adjoin (ResidueField V) {θ} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hθ]; rfl
  have hsurj : Function.Surjective φ := by
    intro y
    have hy : y ∈ Algebra.adjoin (ResidueField V) {θ} := hadj ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨p, rfl⟩ := hy
    obtain ⟨q, rfl⟩ := map_surjective _ (residue_surjective (R := V)) p
    refine ⟨AdjoinRoot.mk μ q, ?_⟩
    rw [hφ]
    simp [aeval_def, eval₂_map, IsScalarTower.algebraMap_eq V (ResidueField V) k']
  haveI : Nontrivial (AdjoinRoot μ) := φ.domain_nontrivial
  have hnon : ∀ w : AdjoinRoot μ, w ∈ nonunits (AdjoinRoot μ) ↔ φ w = 0 := by
    intro w
    refine ⟨fun hw => ?_, fun hw hu => (hu.map φ).ne_zero hw⟩
    by_contra hne
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective w
    rw [hφ] at hne
    exact hw (_root_.GlobalTheory.isUnit_adjoinRoot_mk_of_aeval_ne_zero hint hμ hμmap hne)
  haveI : IsLocalRing (AdjoinRoot μ) := IsLocalRing.of_nonunits_add fun a b ha hb => by
    rw [hnon] at ha hb ⊢
    rw [map_add (f := _), ha, hb, add_zero]
  have hmax : maximalIdeal (AdjoinRoot μ) = RingHom.ker φ := by
    ext w
    rw [mem_maximalIdeal, hnon, RingHom.mem_ker]
  have hCm : (AdjoinRoot.mk μ).comp C = algebraMap V (AdjoinRoot μ) := rfl
  have hker : RingHom.ker φ = (maximalIdeal V).map (algebraMap V (AdjoinRoot μ)) := by
    apply le_antisymm
    · intro w hw
      obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective w
      rw [RingHom.mem_ker, hφ] at hw
      have hdvd : minpoly (ResidueField V) θ ∣ g.map (residue V) := by
        apply minpoly.dvd
        rw [← IsLocalRing.ResidueField.algebraMap_eq, aeval_map_algebraMap]
        exact hw
      obtain ⟨h', hh'⟩ := hdvd
      obtain ⟨h, rfl⟩ := map_surjective _ (residue_surjective (R := V)) h'
      have hcoeff : ∀ n, (g - μ * h).coeff n ∈ maximalIdeal V := by
        intro n
        rw [← residue_eq_zero_iff, ← coeff_map, Polynomial.map_sub, Polynomial.map_mul, hμmap,
          hh', sub_self, coeff_zero]
      have hmk : AdjoinRoot.mk μ g = AdjoinRoot.mk μ (g - μ * h) := by
        simp [AdjoinRoot.mk_self]
      rw [hmk, ← hCm, ← Ideal.map_map]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_C_iff.2 hcoeff)
    · rw [Ideal.map_le_iff_le_comap]
      intro v hv
      rw [Ideal.mem_comap, RingHom.mem_ker, ← hCm, RingHom.comp_apply, hφ, aeval_C,
        IsScalarTower.algebraMap_apply V (ResidueField V) k',
        IsLocalRing.ResidueField.algebraMap_eq, (residue_eq_zero_iff v).2 hv, map_zero]
  have hmW : maximalIdeal (AdjoinRoot μ) = (maximalIdeal V).map (algebraMap V (AdjoinRoot μ)) :=
    hmax.trans hker
  let pb := AdjoinRoot.powerBasis' hμ
  haveI : Module.Finite V (AdjoinRoot μ) := pb.finite
  haveI : Module.Free V (AdjoinRoot μ) := Module.Free.of_basis pb.basis
  haveI : IsNoetherianRing (AdjoinRoot μ) := inferInstance
  have hinj : Function.Injective (algebraMap V (AdjoinRoot μ)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    rw [← hCm, RingHom.comp_apply, AdjoinRoot.mk_eq_zero] at hv
    by_contra hne
    have hle := degree_le_of_dvd hv (C_ne_zero.2 hne)
    rw [degree_C hne, hμdeg] at hle
    exact absurd hle (not_le.2 (minpoly.degree_pos hint))
  haveI hlh : IsLocalHom (algebraMap V (AdjoinRoot μ)) := by
    refine ⟨fun v hv => ?_⟩
    by_contra hnu
    have hvm : v ∈ maximalIdeal V := (mem_maximalIdeal v).2 hnu
    have := Ideal.mem_map_of_mem (algebraMap V (AdjoinRoot μ)) hvm
    rw [← hmW] at this
    exact (mem_maximalIdeal _).1 this hv
  let e : ResidueField (AdjoinRoot μ) ≃+* k' :=
    (Ideal.quotEquivOfEq hmax).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have he : ∀ w, e (residue (AdjoinRoot μ) w) = φ w := fun w => rfl
  have he' : ∀ v : V, e (residue (AdjoinRoot μ) (algebraMap V (AdjoinRoot μ) v)) =
      algebraMap (ResidueField V) k' (residue V v) := by
    intro v
    rw [he, ← hCm, RingHom.comp_apply, hφ, aeval_C]
    rfl
  let eAlg : ResidueField (AdjoinRoot μ) →ₐ[ResidueField V] k' :=
    { e.toRingHom with
      commutes' := fun r => by
        obtain ⟨v, rfl⟩ := residue_surjective r
        simpa using he' v }
  haveI : Algebra.IsSeparable (ResidueField V) (ResidueField (AdjoinRoot μ)) :=
    Algebra.IsSeparable.of_algHom _ _ eAlg
  haveI : Algebra.FormallyUnramified V (AdjoinRoot μ) :=
    Algebra.FormallyUnramified.of_map_maximalIdeal hmW.symm
  obtain ⟨hdom, hdvr⟩ := _root_.GlobalTheory.exists_isDiscreteValuationRing_of_flat V (AdjoinRoot μ) hmW.symm
    (Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal _).ne_top)
  have hcompl : IsAdicComplete (maximalIdeal (AdjoinRoot μ)) (AdjoinRoot μ) := by
    rw [hmW, IsAdicComplete.map_algebraMap_iff]
    exact isAdicComplete_of_linearEquiv_pi pb.basis.equivFun _
  exact ⟨AdjoinRoot μ, inferInstance, hdom, hdvr, hcompl, inferInstance, pb.finite, hinj, hlh,
    inferInstance, e, he'⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelOneSimpleZeroFormAtPoint
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.LevelOneLocal

theorem tendsto_E {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    Tendsto (ModularForm.E hk : ℍ → ℂ) atImInfty (𝓝 1) := by
  have h0 : valueAtInfty (ModularForm.E hk : ℍ → ℂ) = 1 := by
    rw [← qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero (ModularForm.E hk) one_pos one_mem_strictPeriods_SL)
      (SlashInvariantFormClass.periodic_comp_ofComplex (ModularForm.E hk) one_mem_strictPeriods_SL)]
    exact EisensteinSeries.E_qExpansion_coeff_zero hk hk2
  obtain ⟨c, hc, h⟩ := ModularFormClass.exp_decay_sub_atImInfty' (ModularForm.E hk)
  rw [h0] at h
  have h2 : Tendsto (fun τ : ℍ ↦ Real.exp (-c * τ.im)) atImInfty (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    exact Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_comap
  simpa using (h.trans_tendsto h2).add_const 1

theorem tendsto_E₄ : Tendsto (E₄ : ℍ → ℂ) atImInfty (𝓝 1) := tendsto_E _ ⟨2, rfl⟩

theorem tendsto_E₆ : Tendsto (E₆ : ℍ → ℂ) atImInfty (𝓝 1) := tendsto_E _ ⟨3, rfl⟩

theorem cube_sub_sq_ne_zero (τ : ℍ) : E₄ τ ^ 3 - E₆ τ ^ 2 ≠ 0 := by
  intro h
  apply ModularForm.discriminant_ne_zero τ
  rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq, h, zero_div]

theorem isMF_E₄ : IsMF ⊤ 4 (E₄ : ℍ → ℂ) := isMF_coe_top E₄

theorem isMF_E₆ : IsMF ⊤ 6 (E₆ : ℍ → ℂ) := isMF_coe_top E₆

theorem differentiableAt_comp {f : ℍ → ℂ} (hf : MDiff f) (τ : ℍ) :
    DifferentiableAt ℂ (f ∘ ofComplex) τ :=
  mdifferentiableAt_iff.mp (hf τ)

theorem deriv_comb (α β : ℂ) (τ : ℍ) :
    deriv ((α • (E₄ : ℍ → ℂ) ^ 3 - β • (E₆ : ℍ → ℂ) ^ 2) ∘ ofComplex) τ =
      α * (3 * E₄ τ ^ 2 * deriv (⇑E₄ ∘ ofComplex) τ) - β * (2 * E₆ τ * deriv (⇑E₆ ∘ ofComplex) τ) := by
  have h4 := (differentiableAt_comp isMF_E₄.2.1 τ).hasDerivAt
  have h6 := (differentiableAt_comp isMF_E₆.2.1 τ).hasDerivAt
  have h := ((h4.fun_pow 3).const_mul α).fun_sub ((h6.fun_pow 2).const_mul β)
  have e : (α • (E₄ : ℍ → ℂ) ^ 3 - β • (E₆ : ℍ → ℂ) ^ 2) ∘ ofComplex =
      fun x => α * (⇑E₄ ∘ ofComplex) x ^ 3 - β * (⇑E₆ ∘ ofComplex) x ^ 2 := by
    ext x; simp
  rw [e, h.deriv]
  simp

theorem exists_local_data : ∀ τ₀ : ℍ, ∃ (n : ℕ) (a b : ℤ) (E : ℍ → ℂ) (u : SL(2, ℤ)), u • τ₀ = τ₀ ∧ 0 < n ∧ IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) τ₀) n ∧ a < b ∧ Even (b - a) ∧ IsMF ⊤ b E ∧ (∀ τ : ℍ, E τ = 0 → deriv (E ∘ ofComplex) τ ≠ 0 ∧ ∃ γ : SL(2, ℤ), τ = γ • τ₀) ∧ (∃ c : ℂ, c ≠ 0 ∧ Tendsto E atImInfty (𝓝 c)) ∧ ∀ d : ℤ, 0 ≤ d → (n : ℤ) ∣ d → ∃ e : ℍ → ℂ, IsMF ⊤ (d + a) e ∧ e τ₀ ≠ 0 := by
  intro τ₀
  have hD := cube_sub_sq_ne_zero τ₀
  by_cases h6 : E₆ τ₀ = 0
  · obtain ⟨u, hu, hp⟩ := (_root_.GlobalTheory.EllipticZero.elliptic_of_zero τ₀).1 h6
    have h4 : E₄ τ₀ ≠ 0 := fun h => hD (by simp [h, h6])
    refine ⟨4, 0, 6, E₆, u, hu, by norm_num, hp, by norm_num, by decide, isMF_E₆, fun τ hτ => ⟨?_, ?_⟩,
      ⟨1, one_ne_zero, tendsto_E₆⟩, ?_⟩
    · intro h
      exact _root_.GlobalTheory.EisWronskian.wronskian_E₄_E₆_ne_zero τ (by simp [h, hτ])
    · exact _root_.GlobalTheory.JOrbit.exists_smul_of_E₄_E₆ τ τ₀ (by simp [h6, hτ])
    · rintro d hd ⟨m, rfl⟩
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ m by push_cast at hd; omega)
      refine ⟨(E₄ : ℍ → ℂ) ^ m, ?_, by simpa using fun h => absurd h h4⟩
      have := isMF_E₄.pow m
      convert this using 1
      push_cast; ring
  by_cases h4 : E₄ τ₀ = 0
  · obtain ⟨u, hu, hp⟩ := (_root_.GlobalTheory.EllipticZero.elliptic_of_zero τ₀).2 h4
    refine ⟨6, 0, 4, E₄, u, hu, by norm_num, hp, by norm_num, by decide, isMF_E₄, fun τ hτ => ⟨?_, ?_⟩,
      ⟨1, one_ne_zero, tendsto_E₄⟩, ?_⟩
    · intro h
      exact _root_.GlobalTheory.EisWronskian.wronskian_E₄_E₆_ne_zero τ (by simp [h, hτ])
    · exact _root_.GlobalTheory.JOrbit.exists_smul_of_E₄_E₆ τ τ₀ (by simp [h4, hτ])
    · rintro d hd ⟨m, rfl⟩
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ m by push_cast at hd; omega)
      refine ⟨(E₆ : ℍ → ℂ) ^ m, ?_, by simpa using fun h => absurd h h6⟩
      have := isMF_E₆.pow m
      convert this using 1
      push_cast; ring
  refine ⟨2, 4, 12, (E₆ τ₀ ^ 2) • (E₄ : ℍ → ℂ) ^ 3 - (E₄ τ₀ ^ 3) • (E₆ : ℍ → ℂ) ^ 2, -1, ?_, by norm_num, ?_,
    by norm_num, by decide, ?_, fun τ hτ => ?_, ⟨E₆ τ₀ ^ 2 - E₄ τ₀ ^ 3, fun h => hD (by linear_combination -h), ?_⟩,
    ?_⟩
  · rw [ModularGroup.SL_neg_smul, one_smul]
  · have : denom ((-1 : SL(2, ℤ)) : GL (Fin 2) ℝ) τ₀ = -1 := by simp [denom]
    rw [this]
    exact IsPrimitiveRoot.neg_one 0 (by norm_num)
  · exact ((isMF_E₄.pow 3).smul _).sub ((isMF_E₆.pow 2).smul _)
  · have hz : E₆ τ₀ ^ 2 * E₄ τ ^ 3 - E₄ τ₀ ^ 3 * E₆ τ ^ 2 = 0 := by simpa using hτ
    refine ⟨?_, _root_.GlobalTheory.JOrbit.exists_smul_of_E₄_E₆ τ τ₀ (by linear_combination hz)⟩
    have hDτ := cube_sub_sq_ne_zero τ
    have k4 : E₄ τ ≠ 0 := by
      intro h
      have : E₆ τ = 0 := by simpa [h, h4] using hz
      exact hDτ (by simp [h, this])
    rw [deriv_comb]
    intro h
    have hW := _root_.GlobalTheory.EisWronskian.wronskian_E₄_E₆_ne_zero τ
    apply mul_ne_zero (mul_ne_zero (pow_ne_zero 2 h6) (pow_ne_zero 3 k4)) hW
    linear_combination (2 * E₄ τ * deriv (⇑E₆ ∘ ofComplex) τ) * hz - (E₄ τ * E₆ τ) * h
  · have := ((tendsto_E₄.pow 3).const_mul (E₆ τ₀ ^ 2)).sub ((tendsto_E₆.pow 2).const_mul (E₄ τ₀ ^ 3))
    simp only [one_pow, mul_one] at this
    exact this
  · rintro d hd ⟨m, rfl⟩
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ m by push_cast at hd; omega)
    rcases Nat.even_or_odd' m with ⟨p, rfl | rfl⟩
    · refine ⟨(E₄ : ℍ → ℂ) ^ (p + 1), ?_, by simpa using h4⟩
      have := isMF_E₄.pow (p + 1)
      convert this using 1
      push_cast; ring
    · refine ⟨(E₄ : ℍ → ℂ) ^ p * E₆, (isMF_E₄.pow p).mul isMF_E₆ (by push_cast; ring), ?_⟩
      exact mul_ne_zero (pow_ne_zero p h4) h6

end GlobalTheory.LevelOneLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimitiveQuotientLevelPrimeToStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_quotient_level_prime_to : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits → ∀ (k : ℕ) (f : X.K), f ≠ 0 → Lev X (M₀ * l ^ k) f → ∃ (M' : ℕ) (a b : X.K) (c : Ω), 0 < M' ∧ Nat.Coprime q M' ∧ M₀ * l ^ k ∣ M' ∧ Lev X M' a ∧ Lev X M' b ∧ Prim X V a ∧ Prim X V b ∧ c ≠ 0 ∧ f * b = algebraMap Ω X.K c * a := by
  first | exact @GlobalTheory.KZ.ES.Quot.quot_prim | exact GlobalTheory.KZ.ES.Quot.quot_prim | (intros; apply GlobalTheory.KZ.ES.Quot.quot_prim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsQDerivationCompletionZp
section
open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.QDer

variable (p : ℕ) [Fact p.Prime]

abbrev qL : Lau p := HahnSeries.single (1 : ℤ) (1 : ℤ_[p])

def thetaFun (f : Lau p) : Lau p := qL p * Formalism.L2.Th1.A.dL f

theorem thetaFun_qL : thetaFun p (qL p) = qL p := by
  have h := Formalism.L2.Th1.A.dL_uPow (R := ℤ_[p]) 1
  simp only [Formalism.L2.Th1.A.uPow] at h
  simp [thetaFun, h, HahnSeries.single_zero_one]

theorem dL_algebraMap (r : ℤ_[p]) : Formalism.L2.Th1.A.dL (algebraMap ℤ_[p] (Lau p) r) = 0 :=
  (Formalism.L2.Th1.A.dLDR ℤ_[p]).map_algebraMap r

def thetaO :=
  letI : Module ℤ_[p] (Lau p) := Algebra.toModule
  GlobalTheory.BK.complDer (k := ℤ_[p]) (pI p)
    { toFun := thetaFun p
      map_add' := fun a b => by simp only [thetaFun, map_add (f := _), mul_add]
      map_smul' := fun r f => by
        simp only [thetaFun, Algebra.smul_def, RingHom.id_apply]
        rw [Formalism.L2.Th1.A.dL_mul, dL_algebraMap p r]
        ring
      map_one_eq_zero' := by
        show thetaFun p 1 = 0
        simp [thetaFun, Formalism.L2.Th1.A.dL_one]
      leibniz' := fun a b => by
        show thetaFun p (a * b) = a • thetaFun p b + b • thetaFun p a
        simp only [thetaFun, smul_eq_mul, Formalism.L2.Th1.A.dL_mul]
        ring }

theorem thetaO_qO : thetaO p (qO p) = qO p := by
  rw [thetaO, qO, GlobalTheory.BK.complDer_algebraMap]
  exact congrArg _ (thetaFun_qL p)

theorem thetaO_algebraMap (r : ℤ_[p]) : thetaO p (algebraMap ℤ_[p] (O0 p) r) = 0 :=
  (thetaO p).map_algebraMap r

def thetaZ : Derivation ℤ (O0 p) (O0 p) where
  toFun := thetaO p
  map_add' := map_add _
  map_smul' := fun r x => by
    simp [Algebra.smul_def, Derivation.leibniz]
  map_one_eq_zero' := (thetaO p).map_one_eq_zero
  leibniz' := (thetaO p).leibniz

theorem exists_qDer : ∀ (p : ℕ) [Fact p.Prime], ∃ D : Derivation ℤ (O0 p) (O0 p), D (qO p) = qO p ∧
    ∀ r : ℤ_[p], D (algebraMap ℤ_[p] (O0 p) r) = 0 := fun p _ =>
  ⟨thetaZ p, thetaO_qO p, thetaO_algebraMap p⟩

end GlobalTheory.K5.QDer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricGaloisCoboundaryCongZeroModPrimePowStatement
section
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricGalois_coboundary_cong_zero_modPrimePow : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (k N : ℕ) (w o : Ω), IsInt (p := p) w → (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g w = w) →
  (∀ g ∈ Ggeo p Ω, g o = o) → Cong (p := p) k (τ w - w) o → Cong (p := p) k o 0 := by
  first | exact @GlobalTheory.K5.KernLoc.main | exact GlobalTheory.K5.KernLoc.main | (intros; apply GlobalTheory.K5.KernLoc.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelGLengthConjStatement
section
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selG_length_eq_of_conj : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : Formalism.GaloisCohomology.Places E Ω) (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O] (P : LocPrime l) (nb : ∀ w, w ∈ Formalism.BasicNotions.placesOver E l → LocBridge l E Ω (ReciprocityTheory.Gal.Dec (F := E) (A.1 w)) O) (Sig : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))) (k : ℕ) (M M' : Formalism.ConjugateSelfDual.G E Ω →* Matrix (Fin k) (Fin k) O) (U : GL (Fin k) O), (∀ g, M' g * (U : Matrix (Fin k) (Fin k) O) = (U : Matrix (Fin k) (Fin k) O) * M g) → Module.length O (Formalism.MainNotions.N.Br.selG A l P nb Sig M) = Module.length O (Formalism.MainNotions.N.Br.selG A l P nb Sig M') := by
  first | exact @GlobalTheory.SelConj.selG_length_conj | exact GlobalTheory.SelConj.selG_length_conj | (intros; apply GlobalTheory.SelConj.selG_length_conj <;> assumption)
end

