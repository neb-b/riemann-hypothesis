module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0054
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleGlobalGenerators
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsProperIntegralModel
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatesOfCoordsRegular
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0038
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTwistedGenerators
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0055
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0056
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteExtensionCoordsCompare
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsBlockRefinementLines
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LinesDeg

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem block_chart {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {c : (k : K) → J k} {p : Cpt ξ}
    (h : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) :
    InChart ξ (fun i : J k => y ⟨k, i⟩) (c k) p := by
  classical
  obtain ⟨h0, hr⟩ := h
  have hne : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.mp h0) k (Finset.mem_univ k)
  refine ⟨hne k, fun j => ?_⟩
  have hreg := hr (Function.update c k j)
  have e : (∏ k', y ⟨k', Function.update c k j k'⟩) / ∏ k', y ⟨k', c k'⟩ = y ⟨k, j⟩ / y ⟨k, c k⟩ := by
    rw [← Finset.mul_prod_erase Finset.univ (fun k' => y ⟨k', Function.update c k j k'⟩) (Finset.mem_univ k),
      ← Finset.mul_prod_erase Finset.univ (fun k' => y ⟨k', c k'⟩) (Finset.mem_univ k)]
    have hrest : ∏ k' ∈ Finset.univ.erase k, y ⟨k', Function.update c k j k'⟩ =
        ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ :=
      Finset.prod_congr rfl fun k' hk' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')]
    have hP : ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k' _ => hne k'
    simp only [hrest, Function.update_self]
    exact mul_div_mul_right _ _ hP
  rw [← e]
  exact hreg

theorem segre_chart {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {c : (k : K) → J k} {p : Cpt ξ}
    (h : ∀ k, InChart ξ (fun i : J k => y ⟨k, i⟩) (c k) p) :
    InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p := by
  refine ⟨Finset.prod_ne_zero_iff.mpr fun k _ => (h k).1, fun c' => ?_⟩
  show (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩ ∈ regAt ξ p
  rw [← Finset.prod_div_distrib]
  exact prod_mem fun k _ => (h k).2 (c' k)

theorem exists_chart_of_gen {Q : Type} {t : Q → Ω} {d : Ω} (hd : d ≠ 0) {L : Lat ξ Ω} {p : Cpt ξ}
    (hm : ∀ i, t i / d ∈ L p) (hg : ∃ i, L.IsGenAt p (t i / d)) : ∃ i, InChart ξ t i p := by
  obtain ⟨i, hi0, hi⟩ := hg
  have ht : t i ≠ 0 := fun h => hi0 (by simp [h])
  refine ⟨i, ht, fun j => ?_⟩
  have hj := hm j
  rw [hi, Submodule.mem_span_singleton] at hj
  obtain ⟨r, hr⟩ := hj
  rw [Subring.smul_def, smul_eq_mul] at hr
  have : t j / t i = r := by
    field_simp at hr ⊢
    exact hr.symm
  rw [this]
  exact r.2

theorem isGen_of_chart {Q : Type} {t : Q → Ω} {d : Ω} (hd : d ≠ 0) {L : Lat ξ Ω} {p : Cpt ξ} {i₀ : Q}
    (hc : InChart ξ t i₀ p) (hm : ∀ i, t i / d ∈ L p) (hg : ∃ i, L.IsGenAt p (t i / d)) :
    L p = Submodule.span (regAt ξ p) {t i₀ / d} := by
  obtain ⟨i, -, hi⟩ := hg
  refine le_antisymm ?_ ((Submodule.span_singleton_le_iff_mem _ _).mpr (hm i₀))
  rw [hi, Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
  refine ⟨⟨t i / t i₀, hc.2 i⟩, ?_⟩
  rw [Subring.smul_def, smul_eq_mul]
  have := hc.1
  show t i / t i₀ * (t i₀ / d) = t i / d
  field_simp

abbrev joinJ {K I : Type} (J : K → Type) (J₂ : I → Type) : K ⊕ I → Type := Sum.elim J J₂

def joinY {K I : Type} {J : K → Type} {J₂ : I → Type} (y : (Σ k, J k) → Ω) (s : (Σ i, J₂ i) → Ω) :
    (Σ k, joinJ J J₂ k) → Ω
  | ⟨Sum.inl k, j⟩ => y ⟨k, j⟩
  | ⟨Sum.inr i, j⟩ => s ⟨i, j⟩

def joinFintype {K I : Type} {J : K → Type} {J₂ : I → Type} [∀ k, Fintype (J k)] [∀ i, Fintype (J₂ i)] :
    ∀ k, Fintype (joinJ J J₂ k)
  | Sum.inl k => inferInstanceAs (Fintype (J k))
  | Sum.inr i => inferInstanceAs (Fintype (J₂ i))

end GlobalTheory.CompanionTheory.Ar.LinesDeg

namespace GlobalTheory.CompanionTheory.Ar


open LinesDeg in
theorem exists_addBlocks_isDegOn : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (I : Type) [Fintype I] (Λ : I → Lat ξ Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ i, (Λ i).IsVB 1 ⊤) → ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (κ : K → K') (v : ∀ k, J k ≃ J' (κ k)), Function.Injective κ ∧ (∀ k i, y' ⟨κ k, v k i⟩ = y ⟨k, i⟩) ∧ CoordTie ℤ ξ (fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) ∧ ∀ i, ∃ (a : K' → ℤ) (e₀ : Ω), (Λ i).IsDegOn Set.univ y' a e₀ := by
  intro X Ω _ ξ K _ J _ y I _ Λ ht hvb
  classical
  have key := fun i => _root_.GlobalTheory.CompanionTheory.Ar.line_twist_generated X Ω ξ ((k : K) → J k) (fun c' => ∏ k, y ⟨k, c' k⟩) (Λ i) ht (hvb i)
  choose n m s hmem hgen using key
  let J₂ : I → Type := fun i => Fin (m i + 1)
  let s₂ : (Σ i, J₂ i) → Ω := fun q => s q.1 q.2
  have hbpf : ∀ (i : I) (p : Cpt ξ), ∃ j, InChart ξ (fun j' : J₂ i => s₂ ⟨i, j'⟩) j p := by
    intro i p
    obtain ⟨c, hc⟩ := ht.cover p
    exact exists_chart_of_gen (t := s i) (pow_ne_zero _ hc.1) (hmem i p c hc) (hgen i p c hc)
  have hadd := _root_.GlobalTheory.CompanionTheory.Ar.AddBlockMulti.add_block_multi X Ω ξ K J y I J₂ s₂ ht hbpf
  refine ⟨K ⊕ I, inferInstance, joinJ J J₂, joinFintype, joinY y s₂, Sum.inl, fun k => Equiv.refl _,
    Sum.inl_injective, fun k i => rfl, ?_, fun i => ?_⟩
  · have e : (fun c' : (k : K ⊕ I) → joinJ J J₂ k => ∏ k, joinY y s₂ ⟨k, c' k⟩) =
        fun c' : (k : K ⊕ I) → Sum.elim J J₂ k =>
          (∏ k, y ⟨k, c' (Sum.inl k)⟩) * ∏ k, s₂ ⟨k, c' (Sum.inr k)⟩ :=
      funext fun c' => Fintype.prod_sum_type (fun k => joinY y s₂ ⟨k, c' k⟩)
    rw [e]
    exact hadd
  · refine ⟨Sum.elim (fun _ => -(n i : ℤ)) (fun i' => if i' = i then 1 else 0), 1, one_ne_zero, ?_⟩
    intro p _ c hc
    have hb := block_chart hc
    let c₀ : (k : K) → J k := fun k => c (Sum.inl k)
    have hx : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c₀ p :=
      segre_chart fun k => hb (Sum.inl k)
    have hs : InChart ξ (s i) (c (Sum.inr i)) p := hb (Sum.inr i)
    have hP : ∏ k, y ⟨k, c₀ k⟩ ≠ 0 := hx.1
    have hgen' := isGen_of_chart (t := s i) (pow_ne_zero (n i) hP) hs (hmem i p c₀ hx) (hgen i p c₀ hx)
    have hprod : (∏ k : K ⊕ I, joinY y s₂ ⟨k, c k⟩ ^
        (Sum.elim (fun _ => -(n i : ℤ)) (fun i' => if i' = i then 1 else 0) k : ℤ)) • (1 : Ω) =
        s i (c (Sum.inr i)) / (∏ k, y ⟨k, c₀ k⟩) ^ n i := by
      rw [Fintype.prod_sum_type, smul_eq_mul, _root_.mul_one]
      have h1 : ∏ k : K, joinY y s₂ ⟨Sum.inl k, c (Sum.inl k)⟩ ^
          (Sum.elim (fun _ => -(n i : ℤ)) (fun i' => if i' = i then (1 : ℤ) else 0) (Sum.inl k : K ⊕ I) : ℤ) =
          ((∏ k, y ⟨k, c₀ k⟩) ^ n i)⁻¹ := by
        simp only [Sum.elim_inl]
        rw [Finset.prod_zpow, zpow_neg, zpow_natCast]
        rfl
      have h2 : ∏ i' : I, joinY y s₂ ⟨Sum.inr i', c (Sum.inr i')⟩ ^
          (Sum.elim (fun _ => -(n i : ℤ)) (fun i' => if i' = i then (1 : ℤ) else 0) (Sum.inr i' : K ⊕ I) : ℤ) =
          s i (c (Sum.inr i)) := by
        rw [Fintype.prod_eq_single i]
        · simp only [Sum.elim_inr, if_true, zpow_one]
          rfl
        · intro i' hi'
          simp [hi']
      rw [h1, h2, div_eq_mul_inv, _root_.mul_comm]
    rw [hprod]
    exact hgen'

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDvrExtensionField
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.ExtExists

theorem exists_dvr_in_finite_ext (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [CharZero K] [Algebra O K] [IsFractionRing O K]
    (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra O L] [IsScalarTower O K L]
    (z : L) (n : ℕ) (hn : 0 < n) (hz : IsPrimitiveRoot z n) :
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
      (_ : Algebra O O') (_ : IsLocalHom (algebraMap O O')) (_ : Algebra.IsAlgebraic O O')
      (_ : Algebra O' L) (_ : IsScalarTower O O' L) (ζ : O'),
      Function.Injective (algebraMap O' L) ∧ IsPrimitiveRoot ζ n ∧ algebraMap O' L ζ = z := by
  haveI : Algebra.IsSeparable K L := inferInstance
  haveI : IsDedekindDomain (integralClosure O L) := integralClosure.isDedekindDomain O K L
  haveI : IsFractionRing (integralClosure O L) L := integralClosure.isFractionRing_of_finite_extension K L
  haveI : Algebra.IsIntegral O (integralClosure O L) := inferInstance
  have hinjOL : Function.Injective (algebraMap O L) := by
    rw [IsScalarTower.algebraMap_eq O K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective O K)
  have hinjA : Function.Injective (algebraMap O (integralClosure O L)) := fun a b h =>
    hinjOL (congrArg (fun w : integralClosure O L => (w : L)) h)
  have hinjAL : Function.Injective (algebraMap (integralClosure O L) L) := Subtype.val_injective
  obtain ⟨P, hPmax, hPover⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := integralClosure O L) (IsLocalRing.maximalIdeal O)
    (fun x hx => by
      rw [RingHom.mem_ker] at hx
      rw [hinjA (hx.trans (map_zero _).symm)]
      exact Ideal.zero_mem _)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖP : algebraMap O (integralClosure O L) ϖ ∈ P := by
    change ϖ ∈ Ideal.under O P
    rw [hPover, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hϖ.not_isUnit
  have hP0 : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hϖP
    exact hϖ.ne_zero (hinjA (hϖP.trans (map_zero _).symm))
  haveI := hPmax.isPrime
  haveI hdvr : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ hP0 _
  have hAW : Function.Injective (algebraMap (integralClosure O L) (Localization.AtPrime P)) :=
    IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors P)
  have hunit : ∀ y : P.primeCompl, IsUnit (algebraMap (integralClosure O L) L y) := fun y =>
    IsUnit.mk0 _ fun h => y.2 (by
      have : (y : integralClosure O L) = 0 := hinjAL (h.trans (map_zero _).symm)
      rw [this]; exact Ideal.zero_mem _)
  let f : Localization.AtPrime P →+* L := IsLocalization.lift (M := P.primeCompl) hunit
  have hf : ∀ a, f (algebraMap (integralClosure O L) (Localization.AtPrime P) a) =
      algebraMap (integralClosure O L) L a := fun a => IsLocalization.lift_eq hunit a
  have hfinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj P.primeCompl x
    have h1 := congrArg f h
    rw [map_mul, hx, zero_mul, hf] at h1
    have ha : a = 0 := hinjAL (h1.symm.trans (map_zero _).symm)
    rw [ha, map_zero] at h
    have hs : algebraMap (integralClosure O L) (Localization.AtPrime P) s ≠ 0 :=
      (IsLocalization.map_units (Localization.AtPrime P) s).ne_zero
    exact (mul_eq_zero.1 h).resolve_right hs
  letI algWL : Algebra (Localization.AtPrime P) L := f.toAlgebra
  have hOW : ∀ x : O, algebraMap O (Localization.AtPrime P) x =
      algebraMap (integralClosure O L) (Localization.AtPrime P) (algebraMap O (integralClosure O L) x) :=
    fun x => IsScalarTower.algebraMap_apply O (integralClosure O L) (Localization.AtPrime P) x
  have hWL : ∀ x, algebraMap (Localization.AtPrime P) L x = f x := fun _ => rfl
  haveI tower : IsScalarTower O (Localization.AtPrime P) L :=
    IsScalarTower.of_algebraMap_eq (R := O) (S := Localization.AtPrime P) (A := L) fun x => by
      rw [hOW, hWL, hf]; rfl
  have hloc : IsLocalHom (algebraMap O (Localization.AtPrime P)) := ⟨fun x hx => by
    by_contra hxu
    have hxm : x ∈ IsLocalRing.maximalIdeal O := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hxu
    rw [← hPover, Ideal.mem_comap] at hxm
    have hm := (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).2 hxm
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm
    exact hm (by rw [← hOW]; exact hx)⟩
  haveI hOLalg : Algebra.IsAlgebraic O L :=
    (IsFractionRing.comap_isAlgebraic_iff (A := O) (K := K) (C := L)).2 inferInstance
  have halg : Algebra.IsAlgebraic O (Localization.AtPrime P) :=
    ⟨fun x => (isAlgebraic_algebraMap_iff (A := L) hfinj).1 (Algebra.IsAlgebraic.isAlgebraic _)⟩
  have hzint : _root_.IsIntegral O z := IsIntegral.of_pow hn (hz.pow_eq_one ▸ isIntegral_one)
  let zA : integralClosure O L := ⟨z, hzint⟩
  have hfz : f (algebraMap (integralClosure O L) (Localization.AtPrime P) zA) = z := hf zA
  refine ⟨Localization.AtPrime P, inferInstance, inferInstance, hdvr, inferInstance, hloc, halg, algWL, tower,
    algebraMap (integralClosure O L) (Localization.AtPrime P) zA, hfinj, ?_, hfz⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := f) (by rw [hfz]; exact hz) hfinj

theorem exists_dvr_of_generator (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Ω : Type) [Field Ω] [CharZero Ω] [Algebra O Ω] (hinj : Function.Injective (algebraMap O Ω))
    (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra O Ω'] [IsScalarTower O Ω Ω']
    (z : Ω') (n : ℕ) (hn : 0 < n) (hz : IsPrimitiveRoot z n) (htop : Algebra.adjoin Ω {z} = ⊤) :
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
      (_ : Algebra O O') (_ : IsLocalHom (algebraMap O O')) (_ : Algebra.IsAlgebraic O O')
      (_ : Algebra O' Ω') (_ : IsScalarTower O O' Ω') (ζ : O'),
      Function.Injective (algebraMap O' Ω') ∧ IsPrimitiveRoot ζ n ∧
        Algebra.adjoin Ω {algebraMap O' Ω' ζ} = ⊤ := by
  haveI : FaithfulSMul O Ω := (faithfulSMul_iff_algebraMap_injective O Ω).2 hinj
  letI algKΩ : Algebra (FractionRing O) Ω := FractionRing.liftAlgebra O Ω
  haveI towKΩ : IsScalarTower O (FractionRing O) Ω := FractionRing.isScalarTower_liftAlgebra O Ω
  haveI : CharZero (FractionRing O) :=
    ((algebraMap (FractionRing O) Ω).charZero_iff (algebraMap (FractionRing O) Ω).injective).2 inferInstance
  letI algKΩ' : Algebra (FractionRing O) Ω' :=
    ((algebraMap Ω Ω').comp (algebraMap (FractionRing O) Ω)).toAlgebra
  haveI towK : IsScalarTower O (FractionRing O) Ω' := IsScalarTower.of_algebraMap_eq fun x => by
    change _ = algebraMap Ω Ω' (algebraMap (FractionRing O) Ω (algebraMap O (FractionRing O) x))
    rw [← IsScalarTower.algebraMap_apply O (FractionRing O) Ω, ← IsScalarTower.algebraMap_apply O Ω Ω']
  have hzi : _root_.IsIntegral (FractionRing O) z := IsIntegral.of_pow hn (hz.pow_eq_one ▸ isIntegral_one)
  haveI : FiniteDimensional (FractionRing O) (IntermediateField.adjoin (FractionRing O) {z}) :=
    IntermediateField.adjoin.finiteDimensional hzi
  have hgen : IsPrimitiveRoot (IntermediateField.AdjoinSimple.gen (FractionRing O) z) n :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω')
      (by rw [IntermediateField.AdjoinSimple.algebraMap_gen]; exact hz)
      (algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω').injective
  obtain ⟨O', i1, i2, i3, i4, i5, i6, i7, i8, ζ, hinjL, hζ, hζz⟩ :=
    exists_dvr_in_finite_ext O (FractionRing O) (IntermediateField.adjoin (FractionRing O) {z})
      (IntermediateField.AdjoinSimple.gen (FractionRing O) z) n hn hgen
  haveI towL : IsScalarTower O (IntermediateField.adjoin (FractionRing O) {z}) Ω' :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply O (FractionRing O) Ω',
        IsScalarTower.algebraMap_apply O (FractionRing O) (IntermediateField.adjoin (FractionRing O) {z}),
        ← IsScalarTower.algebraMap_apply (FractionRing O) (IntermediateField.adjoin (FractionRing O) {z}) Ω']
  letI algO'Ω' : Algebra O' Ω' :=
    ((algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω').comp
      (algebraMap O' (IntermediateField.adjoin (FractionRing O) {z}))).toAlgebra
  have hO'Ω' : ∀ x : O', algebraMap O' Ω' x =
      algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω'
        (algebraMap O' (IntermediateField.adjoin (FractionRing O) {z}) x) := fun _ => rfl
  haveI tow : IsScalarTower O O' Ω' := IsScalarTower.of_algebraMap_eq fun x => by
    rw [hO'Ω', ← IsScalarTower.algebraMap_apply O O' (IntermediateField.adjoin (FractionRing O) {z}),
      ← IsScalarTower.algebraMap_apply O (IntermediateField.adjoin (FractionRing O) {z}) Ω']
  refine ⟨O', i1, i2, i3, i4, i5, i6, algO'Ω', tow, ζ, ?_, hζ, ?_⟩
  · have : (algebraMap O' Ω' : O' → Ω') =
        (algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω') ∘
          (algebraMap O' (IntermediateField.adjoin (FractionRing O) {z})) := rfl
    rw [this]
    exact (algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω').injective.comp hinjL
  · rw [hO'Ω', hζz, IntermediateField.AdjoinSimple.algebraMap_gen]
    exact htop

end GlobalTheory.CompanionTheory.Ar.Num.ExtExists

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem exists_ext_primitive_root : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [CharZero Ω] [Algebra O Ω], Function.Injective (algebraMap O Ω) → ∀ n : ℕ, 0 < n → ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (_ : Algebra O O') (_ : IsLocalHom (algebraMap O O')) (_ : Algebra.IsAlgebraic O O') (Ω' : Type) (_ : Field Ω') (_ : Algebra Ω Ω') (_ : Algebra O' Ω') (_ : Algebra O Ω') (_ : IsScalarTower O O' Ω') (_ : IsScalarTower O Ω Ω') (ζ : O'), Function.Injective (algebraMap O' Ω') ∧ IsPrimitiveRoot ζ n ∧ Algebra.adjoin Ω {algebraMap O' Ω' ζ} = ⊤ := by
  intro O _ _ _ Ω _ _ _ hinj n hn
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 hn.ne'⟩
  have hz := IsCyclotomicExtension.zeta_spec n Ω (CyclotomicField n Ω)
  obtain ⟨O', i1, i2, i3, i4, i5, i6, i7, i8, ζ, h1, h2, h3⟩ :=
    ExtExists.exists_dvr_of_generator O Ω hinj (CyclotomicField n Ω) _ n hn hz
      (IsCyclotomicExtension.adjoin_primitive_root_eq_top hz)
  exact ⟨O', i1, i2, i3, i4, i5, i6, CyclotomicField n Ω, inferInstance, inferInstance, i7, inferInstance, i8, inferInstance, ζ, h1, h2, h3⟩

end GlobalTheory.CompanionTheory.Ar.Num
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsModelVectorBundles
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

open GlobalTheory.CompanionTheory.Ar.FlagBun in
theorem GlobalTheory.CompanionTheory.Ar.exists_flagBundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) [Finite κ] (x : κ → Ω) (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω E) (L : S → Lat ξ E), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → (∀ s, (L s).IsVB (r s) (V s)) → ∃ (X' : Scheme.{0}) (Ω' : Type) (_ : Field Ω') (_ : Algebra Ω Ω') (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (N : ℕ) (x' : Fin (N + 1) → Ω') (b : ∀ s, Fin (r s) → TensorProduct Ω Ω' E), CoordTie ℤ ξ' x' ∧ (∀ q : X', genPt ξ' ⤳ q) ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω Ω') ∧ Smooth f ∧ Function.Surjective f ∧ IsGenericFlag (Ω' := Ω') (TensorProduct.mk Ω Ω' E 1).toAddMonoidHom V b 1 ∧ ∀ s, ((L s).pull ξ' f (TensorProduct.mk Ω Ω' E 1).toAddMonoidHom).IsFlagVBOn Set.univ (b s) := by
  intro X Ω _ ξ E _ _ κ _ x S _ r V L hx hirr hL
  classical
  have hc : ∀ s, ∃ c : Fin (r s) → E, LinearIndependent Ω c ∧ Submodule.span Ω (Set.range c) = V s := by
    intro s
    obtain ⟨U, hU, b, hb, hfr⟩ := hL s ⟨genPt ξ, specializes_refl _⟩ trivial
    exact ⟨b, (hfr ⟨genPt ξ, specializes_refl _⟩ trivial hU).1, hb⟩
  choose c hc using hc
  have hg : ∀ s, ∃ (m n : ℕ) (φ : Fin n → Module.Dual Ω E), IsTwistGen ξ x (L s) m φ :=
    fun s => _root_.GlobalTheory.CompanionTheory.Ar.FlagBun.Twist.exists_twistGen X Ω ξ E κ x (L s) (r s) (V s) hx hirr (hL s)
  choose m n φ hφ using hg
  obtain ⟨c₀, hc₀⟩ := hx.cover ⟨genPt ξ, specializes_refl _⟩
  have hB : ∀ s, ∃ B : Matrix (Fin (r s)) (Fin (n s)) Ω, B * Matrix.of (fun j l => φ s j (c s l)) = 1 :=
    fun s => GlobalTheory.T.frame_via_twisted_generators X Ω ξ E κ x (L s) (r s) (V s) (m s) (n s) (φ s) (c s) hx (hL s) (hφ s) (hc s).1 (hc s).2
  obtain ⟨J₀, hJ₀, hfrac⟩ := GlobalTheory.T.frame_matrix_chart_ratios Ω E S r n κ x φ c c₀ hc₀.1 (GlobalTheory.T.function_field_ratio_generators X Ω ξ κ x c₀ hx hc₀.1) hB
  haveI : Finite (FlagIx κ n r) := by unfold FlagIx; infer_instance
  obtain ⟨X', ξ', s', hx', hirr', -, hprop, -⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.exists_cl_scheme (GenField Ω r) ℤ (FlagIx κ n r) (flagCoord κ x φ c) J₀ hJ₀ hfrac
  obtain ⟨f, hdom, hch⟩ := _root_.GlobalTheory.CompanionTheory.Ar.CoordMap.exists_dominating_map X Ω ξ ℤ κ x X' (GenField Ω r) ξ' (algebraMap Ω (GenField Ω r)) hx hx'.gen
    hirr' (fun z p' => by simpa using intCast_mem (regAt ξ' p') z) (fun p' => by
      obtain ⟨⟨c1, J⟩, hne, hrat⟩ := hx'.cover p'
      have e1 : ∀ k, flagCoord κ x φ c (k, J) = algebraMap Ω (GenField Ω r) (x k) *
          ∏ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det := fun k => rfl
      rw [e1] at hne
      refine ⟨c1, left_ne_zero_of_mul hne, fun k => ?_⟩
      have := hrat (k, J)
      rwa [e1, e1, mul_div_mul_right _ _ (right_ne_zero_of_mul hne)] at this)
  have hsurj := GlobalTheory.T.proper_dominating_surjective X Ω ξ κ x X' (GenField Ω r) ξ' s' f _ hx hirr hprop hdom
  have hsm := _root_.GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.flag_smooth X Ω ξ E κ x S r V L m n φ c X' ξ' f hx hirr hL hφ hc hx' hirr' hdom hch
  have hfl := _root_.GlobalTheory.CompanionTheory.Ar.FlagBun.Flags.pull_isFlagVB_genB X Ω ξ E κ x S r V L m n φ c X' ξ' f hx hirr hL hφ hc hx' hirr' hdom hch
  have hgen := GlobalTheory.T.generic_flag_over_generic_field Ω E S r V c hc
  have hne : Nonempty (FlagIx κ n r) := ⟨J₀⟩
  have hpos : 0 < Nat.card (FlagIx κ n r) := Nat.card_pos
  let e : Fin (Nat.card (FlagIx κ n r) - 1 + 1) ≃ FlagIx κ n r :=
    (finCongr (Nat.sub_add_cancel hpos)).trans (Finite.equivFin (FlagIx κ n r)).symm
  exact ⟨X', GenField Ω r, inferInstance, inferInstance, ξ', f, _, flagCoord κ x φ c ∘ e, genB c,
    (by convert coordTie_comp_equiv hx' e using 1 <;> first | exact Subsingleton.elim _ _ | skip), hirr', hdom, hsm, hsurj, hgen, hfl⟩
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteExtensionCoordsCompareStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_extension_coords_compare : ∀ (Ω₁ Ω₂ Ω : Type) [Field Ω₁] [Field Ω₂] [Field Ω] [CharZero Ω] (i₁ : Ω₁ →+* Ω) (i₂ : Ω₂ →+* Ω) (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (J₁ : K₁ → Type) (J₂ : K₂ → Type) [∀ k, Fintype (J₁ k)] [∀ k, Fintype (J₂ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (y₂ : (Σ k, J₂ k) → Ω₂) (X₁ X₂ : Scheme.{0}) (ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X₂), (letI := i₁.toAlgebra; Module.Finite Ω₁ Ω) → (∀ q : X₁, genPt ξ₁ ⤳ q) → (∀ q : X₂, genPt ξ₂ ⤳ q) → CoordTie ℤ ξ₁ (fun c' : (k : K₁) → J₁ k => ∏ k, y₁ ⟨k, c' k⟩) → CoordTie ℤ ξ₂ (fun c' : (k : K₂) → J₂ k => ∏ k, y₂ ⟨k, c' k⟩) → ∃ (m : ℕ) (w : Fin m → Ω) (y : (Σ k : K₁ ⊕ K₂ ⊕ Unit, Sum.elim J₁ (Sum.elim J₂ fun _ => Fin m) k) → Ω) (Z : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ Z) (h₁ : Z ⟶ X₁) (h₂ : Z ⟶ X₂), (∀ k a, y ⟨.inl k, a⟩ = i₁ (y₁ ⟨k, a⟩)) ∧ (∀ k a, y ⟨.inr (.inl k), a⟩ = i₂ (y₂ ⟨k, a⟩)) ∧ (∀ a, y ⟨.inr (.inr ()), a⟩ = w a) ∧ (∀ q : Z, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ (fun c' : (k : K₁ ⊕ K₂ ⊕ Unit) → Sum.elim J₁ (Sum.elim J₂ fun _ => Fin m) k => ∏ k, y ⟨k, c' k⟩) ∧ (∀ q : Z, IsDomain (Z.presheaf.stalk q) ∧ IsIntegrallyClosed (Z.presheaf.stalk q)) ∧ Dominates ξ ξ₁ h₁ i₁ ∧ Dominates ξ ξ₂ h₂ i₂ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HtJoin.exists_normal_join | exact GlobalTheory.CompanionTheory.Ar.HtJoin.exists_normal_join | (intros; apply GlobalTheory.CompanionTheory.Ar.HtJoin.exists_normal_join <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagBasisLinIndepSpan
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.FlagBasis

theorem flagStep_full {E : Type} [AddCommGroup E] (Ω : Type) [Field Ω] [Module Ω E] {r : ℕ} (b : Fin r → E) :
    GlobalTheory.CompanionTheory.Ar.flagStep Ω b r = Submodule.span Ω (Set.range b) := by
  unfold GlobalTheory.CompanionTheory.Ar.flagStep
  have : {k : Fin r | (k : ℕ) < r} = Set.univ := by ext k; simp [k.2]
  rw [this, Set.image_univ]

theorem flag_b_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ)
    (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (Fl : 𝔐.Flag) (t : CMType H ⊕ CMType H),
    LinearIndependent Ω (Fl.b t) ∧ Submodule.span Ω (Set.range (Fl.b t)) = 𝔐.Vgen t := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ J y 𝔐 Fl t
  letI := 𝔐.fn.toAlgebra
  obtain ⟨cc, u, hc, _hj, _hjc, hb, _hu1, _hu0, hflag, _⟩ := Fl.generic
  refine ⟨hb t, ?_⟩
  have hle : Submodule.span Ω (Set.range (Fl.b t)) ≤ 𝔐.Vgen t := by
    rw [← flagStep_full, hflag t (labelRk D t), flagStep_full, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ ?_
    exact (Fl.V₀_mem t (cc t l)).1 ((hc t).2 ▸ Submodule.subset_span ⟨l, rfl⟩)
  obtain ⟨U, hpU, b', hspan, hfr⟩ := 𝔐.vb t ⟨GlobalTheory.CompanionTheory.Ar.genPt 𝔐.ξ, 𝔐.all _⟩ trivial
  have hli' : LinearIndependent Ω b' := (hfr _ trivial hpU).1
  have hV : Submodule.span Ω (Set.range b') = 𝔐.Vgen t := hspan
  haveI : FiniteDimensional Ω (𝔐.Vgen t) := by
    rw [← hV]; exact FiniteDimensional.span_of_finite Ω (Set.finite_range b')
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [← hV, finrank_span_eq_card (hb t), finrank_span_eq_card hli']

end GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.FlagBasis
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldDvrExtension
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.FnExt

theorem fnField_top_of_adjoin_root : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω), fnField O y = ⊤ →
    ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] (Ω' : Type) [Field Ω']
      [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω'] [IsScalarTower O O' Ω'] [IsScalarTower O Ω Ω'] (ζ : O'),
      Algebra.adjoin Ω {algebraMap O' Ω' ζ} = ⊤ → fnField O' (fun v => algebraMap Ω Ω' (y v)) = ⊤ := by
  intro O _ _ _ Ω _ _ K J y hy O' _ _ _ _ Ω' _ _ _ _ _ _ ζ hζ
  set L := fnField O' (fun v => algebraMap Ω Ω' (y v)) with hL

  have himg : ∀ a : Ω, algebraMap Ω Ω' a ∈ L := by
    have hmap : (⊤ : Subfield Ω).map (algebraMap Ω Ω') ≤ L := by
      rw [← hy]
      unfold fnField
      rw [Subfield.map_le_iff_le_comap, Subfield.closure_le]
      rintro x (⟨a, rfl⟩ | ⟨q, rfl⟩)
      · show algebraMap Ω Ω' (algebraMap O Ω a) ∈ L
        rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply O O' Ω']
        exact Subfield.subset_closure (Or.inl ⟨_, rfl⟩)
      · show algebraMap Ω Ω' (y ⟨q.1, q.2.1⟩ / y ⟨q.1, q.2.2⟩) ∈ L
        rw [map_div₀]
        exact Subfield.subset_closure (Or.inr ⟨q, rfl⟩)
    intro a
    exact hmap ⟨a, Subfield.mem_top a, rfl⟩
  have hζL : algebraMap O' Ω' ζ ∈ L := Subfield.subset_closure (Or.inl ⟨ζ, rfl⟩)
  let S : Subalgebra Ω Ω' :=
    { L.toSubring with algebraMap_mem' := himg }
  have hle : Algebra.adjoin Ω {algebraMap O' Ω' ζ} ≤ S := by
    rw [Algebra.adjoin_le_iff]
    rw [Set.singleton_subset_iff]
    exact hζL
  rw [hζ] at hle
  rw [eq_top_iff]
  intro x _
  exact hle (Algebra.mem_top (x := x))

end GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.FnExt
end

