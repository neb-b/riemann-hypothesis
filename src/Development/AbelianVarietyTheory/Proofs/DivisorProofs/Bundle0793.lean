module

public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0008
public import Formalism.LocalToGlobal.GlobalTheory.PlacesP
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Formalism.PairingDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0651
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0041
public import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
public import Formalism.PolynomialDimension.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0783
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonnegConstDiscriminantTermLeBudgetFamilyA
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory

theorem exists_nonneg_const_discriminant_term_le_budget_family : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → TuSize Fm → DGamSize Fm →
    ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x,
      Formalism.MainNotions.WeightDegreeSizes.StabiliserLogBound (Fm.D x i) (Fm.L x i) C := by
  intro eps Fm _ _ hT hG
  obtain ⟨Cn, hN⟩ := J.numsL_wtsL_fam Fm hT (Formalism.L2.GlobalTheoryTheory.Places.dlSize eps Fm)
  obtain ⟨x0, hN⟩ := hN Cn le_rfl 3 le_rfl
  obtain ⟨CG, x1, hG⟩ := hG
  refine ⟨4 * max CG 0, max x0 x1, by positivity, fun x hx _ i => ?_⟩
  exact J.gammaDiscriminant_budget_of_sizes (by norm_num) (le_max_right _ _) (hN x (le_trans (le_max_left _ _) hx) i).1
      (J.factDGam_mono (hG x (le_trans (le_max_right _ _) hx) i) (le_max_left _ _))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSummableMajorantAdelicSchwartzLocallyUnifo
section
noncomputable section

open NumberField IsDedekindDomain
open scoped Classical

namespace GlobalTheory.SchwartzMajorant

variable (F : Type) [Field F] [NumberField F]

theorem pureA_add_algebraMap {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (ξ : κ → F) (x : κ → AdeleRing (𝓞 F) F) :
    GlobalTheory.WeilM.pureA F f g (fun j => algebraMap F (AdeleRing (𝓞 F) F) (ξ j) + x j) =
      f ((fun j => mixedEmbedding F (ξ j)) + fun j => InfiniteAdeleRing.ringEquiv_mixedSpace F (x j).1) *
      g ((fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) + fun j => (x j).2) := by
  unfold GlobalTheory.WeilM.pureA
  congr 2
  funext j
  simp only [Pi.add_apply]
  rw [show (algebraMap F (AdeleRing (𝓞 F) F) (ξ j) + x j).1 = (algebraMap F (AdeleRing (𝓞 F) F) (ξ j)).1 + (x j).1 from rfl,
    map_add, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  rfl

theorem norm_le_of_decay {V : Type} [NormedAddCommGroup V] {φ : V → ℂ} {k : ℕ} {C0 Ck : ℝ}
    (h0 : ∀ v, ‖φ v‖ ≤ C0) (hk : ∀ v, ‖v‖ ^ k * ‖φ v‖ ≤ Ck) (w a : V) :
    ‖φ (w + a)‖ * (1 + ‖w‖) ^ k ≤ 2 ^ k * (C0 + Ck) * (1 + ‖a‖) ^ k := by
  set u := w + a with hu
  have hCk : 0 ≤ Ck := le_trans (by positivity) (hk 0)
  have hC0 : 0 ≤ C0 := le_trans (norm_nonneg _) (h0 0)
  have h2k : (0:ℝ) < 2 ^ k := by positivity
  have h1 : ‖φ u‖ * (1 + ‖u‖) ^ k ≤ 2 ^ k * (C0 + Ck) := by
    rcases le_total ‖u‖ 1 with hu1 | hu1
    · calc ‖φ u‖ * (1 + ‖u‖) ^ k ≤ C0 * 2 ^ k :=
            mul_le_mul (h0 u) (pow_le_pow_left₀ (by positivity) (by linarith) k) (by positivity) hC0
        _ ≤ _ := by nlinarith
    · calc ‖φ u‖ * (1 + ‖u‖) ^ k ≤ ‖φ u‖ * (2 * ‖u‖) ^ k :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) k) (norm_nonneg _)
        _ = 2 ^ k * (‖u‖ ^ k * ‖φ u‖) := by rw [mul_pow]; ring
        _ ≤ 2 ^ k * Ck := mul_le_mul_of_nonneg_left (hk u) h2k.le
        _ ≤ _ := by nlinarith
  have h2 : (1 + ‖w‖) ^ k ≤ (1 + ‖a‖) ^ k * (1 + ‖u‖) ^ k := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have : ‖w‖ ≤ ‖u‖ + ‖a‖ := by
      calc ‖w‖ = ‖u - a‖ := by rw [hu, add_sub_cancel_right]
        _ ≤ ‖u‖ + ‖a‖ := norm_sub_le _ _
    nlinarith [norm_nonneg u, norm_nonneg a]
  calc ‖φ u‖ * (1 + ‖w‖) ^ k ≤ ‖φ u‖ * ((1 + ‖a‖) ^ k * (1 + ‖u‖) ^ k) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = (‖φ u‖ * (1 + ‖u‖) ^ k) * (1 + ‖a‖) ^ k := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h1 (by positivity)

theorem summable_one_add_norm_pow_inv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] :
    Summable fun z : L => ((1 + ‖z‖) ^ (Module.finrank ℤ L + 1))⁻¹ := by
  refine Summable.of_norm_bounded_eventually (ZLattice.summable_norm_pow_inv L _ (Nat.lt_succ_self _)) ?_
  refine (Set.finite_singleton (0 : L)).subset fun z hz => ?_
  by_contra h0
  apply hz
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 h0
  show ‖((1 + ‖z‖) ^ (Module.finrank ℤ L + 1))⁻¹‖ ≤ ‖z‖⁻¹ ^ (Module.finrank ℤ L + 1)
  rw [norm_inv, norm_pow, Real.norm_of_nonneg (by positivity), inv_pow]
  exact inv_anti₀ (pow_pos hz0 _) (pow_le_pow_left₀ hz0.le (by linarith) _)

theorem exists_majorant_pureA {κ : Type} [Fintype κ] {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) (x : κ → AdeleRing (𝓞 F) F) :
    ∃ k : ℕ, ∃ M : (κ → F) → ℝ, Summable M ∧ ∀ (C0 Ck : ℝ) (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ),
      (∀ v, ‖φ v‖ ≤ C0) → (∀ v, ‖v‖ ^ k * ‖φ v‖ ≤ Ck) → ∀ ξ : κ → F,
        ‖GlobalTheory.WeilM.pureA F φ g (fun j => algebraMap F (AdeleRing (𝓞 F) F) (ξ j) + x j)‖ ≤ (C0 + Ck) * M ξ := by
  obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  let xf : κ → FiniteAdeleRing (𝓞 F) F := fun j => (x j).2
  let a : κ → mixedEmbedding.mixedSpace F := fun j => InfiniteAdeleRing.ringEquiv_mixedSpace F (x j).1
  have hK : IsCompact ((fun y => y - xf) '' tsupport g) :=
    hg.2.isCompact.image (continuous_id.sub continuous_const)
  obtain ⟨N, hN, hKN⟩ := GlobalTheory.WeilM.exists_nat_mul_integral_of_isCompact F hK
  haveI := GlobalTheory.WeilM.discreteTopology_denomLattice F κ hN
  let v : (κ → F) → (κ → mixedEmbedding.mixedSpace F) := fun ξ j => mixedEmbedding F (ξ j)
  let S : Set (κ → F) := {ξ | v ξ ∈ GlobalTheory.WeilM.denomLattice F κ N}
  let k := Module.finrank ℤ (GlobalTheory.WeilM.denomLattice F κ N) + 1
  refine ⟨k, S.indicator fun ξ => 2 ^ k * (1 + ‖a‖) ^ k * B * ((1 + ‖v ξ‖) ^ k)⁻¹, ?_, ?_⟩
  · rw [← summable_subtype_iff_indicator]
    let j : S → GlobalTheory.WeilM.denomLattice F κ N := fun ξ => ⟨v ξ, ξ.2⟩
    have hj : Function.Injective j := fun p q h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
    exact ((summable_one_add_norm_pow_inv (GlobalTheory.WeilM.denomLattice F κ N)).comp_injective hj).mul_left _
  · intro C0 Ck φ h0 hk ξ
    rw [pureA_add_algebraMap, norm_mul]
    by_cases hξ : ξ ∈ S
    · rw [Set.indicator_of_mem hξ]
      have hd := norm_le_of_decay h0 hk (v ξ) a
      have hpos : 0 < (1 + ‖v ξ‖) ^ k := by positivity
      have h1 : ‖φ (v ξ + a)‖ ≤ 2 ^ k * (C0 + Ck) * (1 + ‖a‖) ^ k * ((1 + ‖v ξ‖) ^ k)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hpos]; exact hd
      calc ‖φ (v ξ + a)‖ * ‖g ((fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) + xf)‖
          ≤ (2 ^ k * (C0 + Ck) * (1 + ‖a‖) ^ k * ((1 + ‖v ξ‖) ^ k)⁻¹) * B :=
            mul_le_mul h1 (hB _) (norm_nonneg _) (le_trans (norm_nonneg _) h1)
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hξ, mul_zero]
      have hz : g ((fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) + xf) = 0 := by
        by_contra h0'
        apply hξ
        have hmem : (fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) ∈ (fun y => y - xf) '' tsupport g :=
          ⟨_, subset_tsupport _ h0', add_sub_cancel_right _ _⟩
        show ∀ i, (N : ℝ) • v ξ i ∈ mixedEmbedding.integerLattice F
        intro i
        obtain ⟨y, hy⟩ := (IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun w => by
          rw [map_mul, map_natCast]
          exact hKN _ hmem i w
        refine ⟨y, ?_⟩
        have h2 := congrArg (mixedEmbedding F) hy
        rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
        exact h2.symm
      show _ * ‖g ((fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) + xf)‖ ≤ 0
      rw [hz, norm_zero, mul_zero]

theorem exists_summable_majorant : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] {P : Type}
    [TopologicalSpace P]
    (Ψ : P → (κ → AdeleRing (𝓞 F) F) → ℂ) (p0 : P) (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (f : P → Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ),
    (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) →
    (∀ᶠ p in nhds p0, Ψ p = ∑ i, GlobalTheory.WeilM.pureA F (f p i) (g i)) →
    (∀ k : ℕ, ∃ C : ℝ, ∀ᶠ p in nhds p0, ∀ i v, ‖v‖ ^ k * ‖f p i v‖ ≤ C) →
    ∀ x : κ → AdeleRing (𝓞 F) F, ∃ M : (κ → F) → ℝ, Summable M ∧
      ∀ᶠ p in nhds p0, ∀ ξ : κ → F, ‖Ψ p (fun j => algebraMap F (AdeleRing (𝓞 F) F) (ξ j) + x j)‖ ≤ M ξ := by
  intro F _ _ κ _ P _ Ψ p0 m g f hg hΨ hC x
  choose k M hM hbound using fun i => exists_majorant_pureA F (hg i) x
  choose C hCev using hC
  refine ⟨fun ξ => ∑ i, (C 0 + C (k i)) * M i ξ, summable_sum fun i _ => (hM i).mul_left _, ?_⟩
  have hall : ∀ᶠ p in nhds p0, ∀ i, (∀ v, ‖v‖ ^ 0 * ‖f p i v‖ ≤ C 0) ∧
      (∀ v, ‖v‖ ^ k i * ‖f p i v‖ ≤ C (k i)) :=
    Filter.eventually_all.2 fun i => ((hCev 0).and (hCev (k i))).mono fun p hp => ⟨hp.1 i, hp.2 i⟩
  filter_upwards [hΨ, hall] with p hp hb ξ
  rw [hp, Finset.sum_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hbound i _ _ _ (fun v => ?_) (hb i).2 ξ)
  simpa using (hb i).1 v

end GlobalTheory.SchwartzMajorant
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal
open scoped nonZeroDivisors

namespace GlobalTheory.CMVal.PicFin

variable {E : Type} [Field E] [NumberField E]

theorem mul_mem_hatO {c : Ideal (OF E)} {n : OF E} (hn : n ∈ c) {y : Af E}
    (hy : ∀ v, y v ∈ v.adicCompletionIntegers E) : algebraMap E (Af E) (algebraMap (OF E) E n) * y ∈ hatO c := by
  refine GlobalTheory.IntDense.mem_of_isClosed E (C := {y | algebraMap E (Af E) (algebraMap (OF E) E n) * y ∈ hatO c})
    ((Subring.isClosed_topologicalClosure _).preimage (continuous_const.mul continuous_id)) (fun b => ?_) y hy
  show _ * _ ∈ hatO c
  rw [← map_mul]
  refine algebraMap_mem_hatO (mem_orderC.2 ⟨0, algebraMap (OF E) (𝓞 E) n * b,
    Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hn), ?_⟩)
  rw [map_zero, zero_add, map_mul]
  rfl

def intR (E : Type) [Field E] [NumberField E] : Subring (Af E) where
  carrier := {y | ∀ v, y v ∈ v.adicCompletionIntegers E}
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
  one_mem' v := one_mem _
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem _
  neg_mem' ha v := neg_mem (ha v)

theorem finite_quot {N : ℕ} (hN : N ≠ 0) : Finite (intR E ⧸ Ideal.span {(N : intR E)}) := by
  have hi : ∀ a : 𝓞 E, algebraMap (𝓞 E) (Af E) a ∈ intR E := fun a v =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
      ((HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans_le (v.valuation_le_one a))
  let f : 𝓞 E →+* intR E := (algebraMap (𝓞 E) (Af E)).codRestrict _ hi
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN)
  refine Finite.of_surjective (Ideal.quotientMap (I := Ideal.span {(N : 𝓞 E)}) (Ideal.span {(N : intR E)}) f
    ((Ideal.span_singleton_le_iff_mem _).2 (by
      rw [Ideal.mem_comap, map_natCast]; exact Ideal.mem_span_singleton_self _))) fun x => ?_
  obtain ⟨α, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨a, β, hβ, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat E N (Nat.pos_of_ne_zero hN)).2 α.1 α.2
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  rw [Ideal.quotientMap_mk, eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  refine ⟨⟨β, hβ⟩, Subtype.ext ?_⟩
  show α.1 - algebraMap (𝓞 E) (Af E) a = (N : Af E) * β
  rw [e, ← nsmul_eq_mul]
  exact add_sub_cancel_left _ _

theorem mem_intR {u : (Af E)ˣ} (h : GlobalTheory.Idele.idealOf u = 1) : (u : Af E) ∈ intR E := fun v => by
  have h1 := (GlobalTheory.Idele.smul_eq_self_iff u (I := 1) one_ne_zero).1 (by rw [GlobalTheory.Idele.smul_one_eq, h]) v
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 h1.le

theorem mem_sup {a : (Af E)ˣ} {x : E} (hx : GlobalTheory.Idele.idealOf a = FractionalIdeal.spanSingleton (𝓞 E)⁰ x) :
    a ∈ ((intR E).toSubmonoid.units ⊔ princ : Subgroup (Af E)ˣ) := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact GlobalTheory.Idele.idealOf_ne_zero _ (hx.trans (FractionalIdeal.spanSingleton_zero))
  obtain ⟨b, hb⟩ : ∃ b : (Af E)ˣ, b = FiniteAdeleRing.unitEmbedding (𝓞 E) E (Units.mk0 x hx0) := ⟨_, rfl⟩
  have h2 : GlobalTheory.Idele.idealOf (a * b⁻¹) = 1 := by
    rw [GlobalTheory.Idele.idealOf_mul, GlobalTheory.Idele.idealOf_inv, hb, GlobalTheory.Idele.idealOf_unitEmbedding, hx]
    exact mul_inv_cancel₀ (FractionalIdeal.spanSingleton_ne_zero_iff.2 hx0)
  have h3 : GlobalTheory.Idele.idealOf (a * b⁻¹)⁻¹ = 1 := by rw [GlobalTheory.Idele.idealOf_inv, h2, inv_one]
  have h4 : a * b⁻¹ ∈ (intR E).toSubmonoid.units := (Submonoid.mem_units_iff _ _).2 ⟨mem_intR h2, mem_intR h3⟩
  have h5 : b ∈ princ := MonoidHom.mem_range.2 ⟨Units.mk0 x hx0, by rw [hb]; exact Units.ext (by simp)⟩
  have h6 := Subgroup.mul_mem_sup h4 h5
  rwa [inv_mul_cancel_right] at h6

theorem finiteIndex_top : ((intR E).toSubmonoid.units ⊔ princ : Subgroup (Af E)ˣ).FiniteIndex := by
  classical
  let g : (Af E)ˣ →* ClassGroup (𝓞 E) := (ClassGroup.mk E).comp (GlobalTheory.Mem.UnitIndex.idealHom E).toHomUnits
  have : g.ker.FiniteIndex := Subgroup.finiteIndex_ker _
  refine Subgroup.finiteIndex_of_le (H := g.ker) fun a ha => ?_
  have h1 : ClassGroup.mk E ((GlobalTheory.Mem.UnitIndex.idealHom E).toHomUnits a) = 1 := ha
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 h1
  exact mem_sup hx

theorem finiteIndex_units {c : Ideal (OF E)} (hc : c ≠ ⊥) :
    ((hatOUnits c).subgroupOf (intR E).toSubmonoid.units).FiniteIndex := by
  have hN : Ideal.absNorm c ≠ 0 := fun h => hc (Ideal.absNorm_eq_zero_iff.1 h)
  have := finite_quot (E := E) hN
  let r : (intR E).toSubmonoid.units →* intR E ⧸ Ideal.span {((Ideal.absNorm c : ℕ) : intR E)} :=
    { toFun := fun u => Ideal.Quotient.mk _ ⟨(u.1 : Af E), u.2.1⟩
      map_one' := map_one (Ideal.Quotient.mk _)
      map_mul' := fun a b => by rw [← map_mul]; rfl }
  have h1 : r.toHomUnits.ker.FiniteIndex := Subgroup.finiteIndex_ker _
  have key : ∀ u ∈ r.toHomUnits.ker, ((u.1 : (Af E)ˣ) : Af E) ∈ hatO c := fun u hu => by
    have h2 : Ideal.Quotient.mk (Ideal.span {((Ideal.absNorm c : ℕ) : intR E)}) ⟨(u.1 : Af E), u.2.1⟩ =
        Ideal.Quotient.mk _ 1 := congrArg Units.val (MonoidHom.mem_ker.1 hu)
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h2
    obtain ⟨β, hβ⟩ := h2
    have h3 : ((u.1 : (Af E)ˣ) : Af E) - 1 = ((Ideal.absNorm c : ℕ) : Af E) * β.1 := congrArg Subtype.val hβ
    have h4 := mul_mem_hatO (Ideal.absNorm_mem c) β.2
    rw [map_natCast, map_natCast, ← h3] at h4
    simpa using add_mem h4 (one_mem _)
  exact Subgroup.finiteIndex_of_le (H := r.toHomUnits.ker) fun u hu => ⟨key u hu, key u⁻¹ (inv_mem hu)⟩

theorem finite_picO : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → Finite (PicO c) := by
  intro E _ _ _ c hc
  let U : Subgroup (Af E)ˣ := (intR E).toSubmonoid.units
  let K : Subgroup (Af E)ˣ := princ ⊔ hatOUnits c
  have h1 := finiteIndex_units hc
  have h2 : (K.subgroupOf U).FiniteIndex :=
    Subgroup.finiteIndex_of_le (H := (hatOUnits c).subgroupOf U) (Subgroup.comap_mono le_sup_right)
  have := finiteIndex_top (E := E)
  have h3 : (U ⊔ K).FiniteIndex := Subgroup.finiteIndex_of_le (H := U ⊔ princ) (sup_le_sup_left le_sup_left _)
  have : K.FiniteIndex := ⟨by
    rw [← Subgroup.relIndex_mul_index (le_sup_right : K ≤ U ⊔ K), Subgroup.relIndex_sup_right]
    exact mul_ne_zero h2.1 h3.1⟩
  exact Subgroup.finite_quotient_of_finiteIndex

end GlobalTheory.CMVal.PicFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPairingLastRowMonomialReadsCoefficient
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

noncomputable section

namespace GlobalTheory.BrCoefFock

variable {K : Type} [Field K] {n : ℕ}

def spl (K : Type) [Field K] (n : ℕ) : BP K n →+* MvPolynomial (Unit × Fin n) (MvPolynomial (Fin n × Fin n) K) :=
  (map (rename (Prod.snd : Unit × Fin n × Fin n → Fin n × Fin n) :
      MvPolynomial (Unit × Fin n × Fin n) K →ₐ[K] MvPolynomial (Fin n × Fin n) K).toRingHom).comp
    ((GlobalTheory.BranchFormula.splitLast K Unit (rfl : n + 1 = n + 1)).toRingHom.comp
      ((rename (fun v : Fin (n + 1) × Fin (n + 1) => (((), v) : Unit × Fin (n + 1) × Fin (n + 1))) :
        _ →ₐ[K] _).toRingHom.comp (incl K n).toRingHom))

theorem coefOne_eq (b : Fin n → ℕ) (x : BP K n) :
    coefOne K n b (incl K n x) = AddMonoidAlgebra.coeff (spl K n x) (GlobalTheory.BranchFormula.expOf fun _ : Unit => b) := by
  unfold coefOne
  rw [GlobalTheory.BranchFormula.coefLast_eq_coeff]
  simp [spl, coeff_map]

theorem spl_C (a : K) : spl K n (C a) = C (C a) := by
  simp [spl, incl, GlobalTheory.BranchFormula.splitLast]

theorem spl_up (a s : Fin n) : spl K n (X (a.castSucc, s)) = C (X (a, s)) := by
  simp [spl, incl, GlobalTheory.BranchFormula.splitLast]

theorem spl_last (s : Fin n) : spl K n (X (Fin.last n, s)) = X ((), s) := by
  simp [spl, incl, GlobalTheory.BranchFormula.splitLast]

def lastV (n : ℕ) (p : Unit × Fin n) : Fin (n + 1) × Fin n := (Fin.last n, p.2)

theorem lastV_inj : Function.Injective (lastV n) := fun _ _ h =>
  Prod.ext rfl (Prod.ext_iff.1 h).2

theorem pderiv_rename_of_ne {σ τ : Type} (e : σ → τ) (v : τ) (h : ∀ u, e u ≠ v) (f : MvPolynomial σ K) :
    pderiv v (rename e f) = 0 := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p u hp => simp [hp, pderiv_X_of_ne (h u)]

theorem fockB_C_left {σ : Type} (a : K) (g : MvPolynomial σ K) : fockB (C a) g = a * constantCoeff g :=
  @fockL_C_left K _ starRingOfComm _ a g

theorem emb_inj : Function.Injective (fun v : Fin n × Fin n => ((v.1.castSucc, v.2) : Fin (n + 1) × Fin n)) :=
  (Fin.castSucc_injective n).prodMap Function.injective_id

theorem key (x : BP K n) (β : Unit × Fin n →₀ ℕ) (p : MvPolynomial (Fin n × Fin n) K) :
    fockB x (rename (lastV n) (monomial β (1 : K)) * emb K n p) =
      ((∏ u, (β u).factorial : ℕ) : K) * fockB (AddMonoidAlgebra.coeff (spl K n x) β) p := by
  classical
  induction x using MvPolynomial.induction_on generalizing β p with
  | C a =>
    rw [fockB_C_left, spl_C, coeff_C, map_mul, constantCoeff_rename, constantCoeff_monomial, emb, constantCoeff_rename]
    by_cases h : β = 0
    · subst h; simp [fockB_C_left]
    · rw [if_neg h, if_neg (Ne.symm h), ← fockBL_apply]; simp
  | add f g hf hg =>
    simp only [← fockBL_apply, map_add (f := _), LinearMap.add_apply, MvPolynomial.coeff_add] at *
    rw [hf, hg, mul_add]
  | mul_X f v hf =>
    obtain ⟨a, s⟩ := v
    rw [mul_comm f, fockB_X_mul, map_mul (spl K n), Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    induction a using Fin.lastCases with
    | cast a =>
      rw [pderiv_rename_of_ne (lastV n) (a.castSucc, s) (fun u h => (Fin.castSucc_lt_last a).ne' (Prod.ext_iff.1 h).1),
        mul_zero, add_zero, spl_up, coeff_C_mul, fockB_X_mul, ← hf]
      congr 2
      exact pderiv_rename emb_inj (a, s) p
    | last =>
      have h1 : pderiv (Fin.last n, s) (emb K n p) = 0 :=
        pderiv_rename_of_ne _ _ (fun u h => (Fin.castSucc_lt_last u.1).ne (congrArg Prod.fst h)) p
      have h2 : pderiv (Fin.last n, s) (rename (lastV n) (monomial β (1 : K))) =
          (β ((), s) : K) • rename (lastV n) (monomial (β - Finsupp.single ((), s) 1) (1 : K)) := by
        have := pderiv_rename (R := K) lastV_inj ((), s) (monomial β (1 : K))
        rw [pderiv_monomial] at this
        rw [← map_smul, smul_monomial, smul_eq_mul, mul_comm]
        exact this
      rw [h1, mul_zero, zero_add, h2, mul_comm, smul_mul_assoc, ← fockBL_apply, map_smul, fockBL_apply, hf,
        spl_last, coeff_X_mul', smul_eq_mul]
      split_ifs with h
      · rw [← mul_assoc, ← Nat.cast_mul]
        congr 2
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ((), s)),
          ← Finset.mul_prod_erase _ (fun u => (β u).factorial) (Finset.mem_univ ((), s)), ← mul_assoc]
        congr 1
        · simpa using Nat.mul_factorial_pred (Finsupp.mem_support_iff.1 h)
        · refine Finset.prod_congr rfl fun u hu => ?_
          simp [Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hu)]
      · rw [Finsupp.notMem_support_iff.1 h, ← fockBL_apply (0 : MvPolynomial (Fin n × Fin n) K)]
        simp

theorem zmon_eq (b : Fin n → ℕ) :
    zmon K n b = rename (lastV n) (monomial (GlobalTheory.BranchFormula.expOf fun _ : Unit => b) (1 : K)) := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp), map_prod, Fintype.prod_prod_type]
  simp [zmon, lastV]

theorem spl_zmon (b : Fin n → ℕ) :
    spl K n (zmon K n b) = monomial (GlobalTheory.BranchFormula.expOf fun _ : Unit => b) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type]
  simp [zmon, spl_last]

theorem spl_emb (q : MvPolynomial (Fin n × Fin n) K) : spl K n (emb K n q) = C q := by
  induction q using MvPolynomial.induction_on with
  | C a => rw [emb, rename_C, spl_C]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp => rw [map_mul, map_mul, hp, bmF_emb_X, spl_up, map_mul]

theorem fockB_zmon_emb : ∀ (K : Type) [Field K] (n : ℕ) (b : Fin n → ℕ), (∀ (x : BP K n) (p : MvPolynomial (Fin n × Fin n) K), fockB x (zmon K n b * emb K n p) = (bfact b : K) * fockB (coefOne K n b (incl K n x)) p) ∧ ∀ p q : MvPolynomial (Fin n × Fin n) K, fockB (zmon K n b * emb K n q) (zmon K n b * emb K n p) = (bfact b : K) * fockB q p := by
  intro K _ n b
  have h1 : ∀ (x : BP K n) (p : MvPolynomial (Fin n × Fin n) K), fockB x (zmon K n b * emb K n p) =
      (bfact b : K) * fockB (coefOne K n b (incl K n x)) p := by
    intro x p
    rw [zmon_eq, key, coefOne_eq, Fintype.prod_prod_type]
    simp [bfact]
  refine ⟨h1, fun p q => ?_⟩
  rw [h1, coefOne_eq, map_mul, spl_zmon, spl_emb, mul_comm (monomial _ _), coeff_C_mul]
  simp

end GlobalTheory.BrCoefFock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCover
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CoverDeg

def GoodCover {k : Type} [CommRing k] {X Y : Scheme.{0}} (p : X ⟶ Sp k) (π : Y ⟶ X) (D δ : ℕ)
    (U : X.Opens) : Prop :=
  IsAffineOpen U ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧
    (∃ t : Fin D → Γ(X, U), (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U) t).Etale) ∧
    (π.app U).hom.Etale ∧ (π.app U).hom.Finite ∧
    (letI := (π.app U).hom.toAlgebra
     Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ Module.finrank Γ(X, U) Γ(Y, π ⁻¹ᵁ U) = δ)

end GlobalTheory.CoverDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGramFrameEmbeddingMatrixNormOfVector
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.DefPt

theorem isGram_matNorm : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] [DecidableEq ι] (Y : (K →+* ℂ) → Matrix ι ι ℂ), (∀ σ, (Y σ).det ≠ 0) → IsGram (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) (matNorm Y) ∧ HasGram (matNorm Y) := by
  intro K _ _ ι _ _ Y hY
  have h : IsGram (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) (matNorm Y) := by
    intro v
    have hu : IsUnit (Y v.embedding).det := (hY _).isUnit
    refine ⟨Matrix.isUnit_nonsing_inv_det _ hu, fun x => ?_⟩
    have hv : Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K ι) v x = fun j => v.embedding (x j) := by
      funext j
      simp [Formalism.HermitianLatticesTheory.vecAt]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Formalism.HermitianLatticesTheory.fcoord, matNorm, Matrix.nonsing_inv_nonsing_inv _ hu, hv]
  exact ⟨h, h.hasGram⟩

end GlobalTheory.DefPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTestHomMatrixOfProportionalGeneratingCombinatiStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTestHomMatrix_of_proportional_generating_combinations : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), L.IsLB → M.IsLB → eA.IsGen → eB.IsGen → (⨆ j, nonzeroLocus (bB j)) = ⊤ → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsTest A B L M t A' B' φA' φB' Φ' → GlobalTheory.HomFixUniv.Generates bA (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom c → GlobalTheory.HomFixUniv.Proport bA bB (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom (Φ'.left ≫ φB' ≫ GlobalTheory.HomFixUniv.θ B) c → GlobalTheory.HomFixUniv.Normal t c αA βB → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c := by
  first | (exact @GlobalTheory.HomFixCond.isMat_of_conditions) | (exact GlobalTheory.HomFixCond.isMat_of_conditions) | (intros; apply GlobalTheory.HomFixCond.isMat_of_conditions  <;> assumption)
end

