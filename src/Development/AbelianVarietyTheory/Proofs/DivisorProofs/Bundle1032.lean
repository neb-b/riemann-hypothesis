module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0985
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0906
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0993
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedAlgebraExists
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

namespace GlobalTheory.FixedCentraliserReg

theorem fixed_algebra_exists : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β Y : G.Cˣ),
    (minpoly G.F (Y : G.C)).Separable → (minpoly G.F (Y : G.C)).natDegree = G.n →
    ∃ (L : Type) (_ : CommRing L) (_ : IsReduced L) (_ : Algebra ℚ L) (_ : FiniteDimensional ℚ L) (ι : L →ₐ[ℚ] G.C), Function.Injective ι ∧
      ∀ c : G.C, c ∈ Set.range ι ↔ Commute c (Y : G.C) ∧ (β : G.C) * sh G c * ((β⁻¹ : G.Cˣ) : G.C) = c := by
  intro p _ G β Y hsep hdeg
  have hcomm : ∀ a b : G.C, Commute a (Y : G.C) → Commute b (Y : G.C) → Commute a b :=
    fun a b ha hb => GlobalTheory.LKCx.ClsReg.commute_of_commute_of_separable G (Y : G.C) hsep hdeg a b ha hb
  have hshmul : ∀ x y : G.C, sh G (x * y) = sh G y * sh G x := by
    intro x y; simp only [sh, map_mul, MulOpposite.unop_mul]
  have hshadd : ∀ x y : G.C, sh G (x + y) = sh G x + sh G y := by
    intro x y; simp only [sh, map_add (f := _), MulOpposite.unop_add]
  have hshalg : ∀ q : ℚ, sh G (algebraMap ℚ G.C q) = algebraMap ℚ G.C q := by
    intro q
    have h := RingHom.congr_fun (RingHom.ext_rat (G.star.comp (algebraMap ℚ G.C)) (algebraMap ℚ G.Cᵐᵒᵖ)) q
    simp only [RingHom.comp_apply, MulOpposite.algebraMap_apply] at h
    simp only [sh, h, MulOpposite.unop_op]
  have hββ : ((β⁻¹ : G.Cˣ) : G.C) * (β : G.C) = 1 := by simp
  let S : Subalgebra ℚ G.C :=
    { carrier := {c | Commute c (Y : G.C) ∧ (β : G.C) * sh G c * ((β⁻¹ : G.Cˣ) : G.C) = c}
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨ha1.mul_left hb1, ?_⟩
        calc (β : G.C) * sh G (a * b) * ((β⁻¹ : G.Cˣ) : G.C)
            = ((β : G.C) * sh G b * ((β⁻¹ : G.Cˣ) : G.C)) * ((β : G.C) * sh G a * ((β⁻¹ : G.Cˣ) : G.C)) := by
              rw [hshmul]
              simp only [mul_assoc]
              rw [← mul_assoc ((β⁻¹ : G.Cˣ) : G.C) (β : G.C), hββ, one_mul]
          _ = b * a := by rw [ha2, hb2]
          _ = a * b := (hcomm a b ha1 hb1).eq.symm
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨ha1.add_left hb1, ?_⟩
        rw [hshadd, mul_add, add_mul, ha2, hb2]
      algebraMap_mem' := by
        intro q
        refine ⟨Algebra.commutes q _, ?_⟩
        rw [hshalg, ← Algebra.commutes q (β : G.C), mul_assoc, Units.mul_inv, mul_one] }
  letI cr : CommRing S :=
    { (inferInstance : Ring S) with
      mul_comm := fun a b => Subtype.ext (hcomm a b a.2.1 b.2.1).eq }
  have hred : IsReduced S := by
    refine ⟨fun x ⟨k, hk⟩ => Subtype.ext ?_⟩
    have hk' : (x : G.C) ^ k = 0 := by
      have := congrArg Subtype.val hk
      simpa using this
    exact GlobalTheory.LKCx.ClsReg.eq_zero_of_commute_of_pow_eq_zero p G (Y : G.C) hsep hdeg x x.2.1 k hk'
  haveI := G.towerC
  haveI := G.finC
  haveI : FiniteDimensional ℚ G.C := Module.Finite.trans G.F G.C
  have hfd : FiniteDimensional ℚ S :=
    Module.Finite.of_injective (S.val.toLinearMap) Subtype.val_injective
  refine ⟨S, cr, hred, S.algebra, hfd, S.val, Subtype.val_injective, fun c => ?_⟩
  constructor
  · rintro ⟨x, rfl⟩; exact x.2
  · intro h; exact ⟨⟨c, h⟩, rfl⟩

end GlobalTheory.FixedCentraliserReg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedUnitEqNormAlmostAllPlaces
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
noncomputable section

namespace GlobalTheory.LocNorm

theorem good_eventually : ∀ (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L) (κ : Type) (bL : Module.Basis κ ℚ L) (θ : L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      Valued.v (2 : v.adicCompletion ℚ) = 1 ∧ IsIntB v bL 1 ∧
      (∀ x y, IsIntB v bL x → IsIntB v bL y → IsIntB v bL (x * y)) ∧
      (∀ x y, IsIntB v bL x → IsSmallB v bL y → IsSmallB v bL (x * y)) ∧
      (∀ x, IsIntB v bL x → IsIntB v bL (Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c x)) ∧
      (∀ x, IsSmallB v bL x → IsSmallB v bL (Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c x)) ∧
      IsIntB v bL ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] θ) ∧ IsIntB v bL ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] θ⁻¹) := by
  intro L _ _ c κ bL θ
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex bL
  have ev := fun (q : ℚ) => rat_mem_adicCompletionIntegers_eventually q
  have hc : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (bL.repr (bL t.1 * bL t.2.1) t.2.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => ev _
  have hs : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (bL.repr (c (bL t.1)) t.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => ev _
  have hl : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : Fin 3 × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (bL.repr (![1, θ, θ⁻¹] t.1) t.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => ev _
  have hfin := Filter.eventually_cofinite.1 (((hc.and hs).and hl).and (ev (1 / 2)))
  refine ⟨hfin.toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  obtain ⟨⟨⟨hcv, hsv⟩, hlv⟩, h2v⟩ := hv
  have hmem : ∀ a : v.adicCompletion ℚ, a ∈ v.adicCompletionIntegers ℚ ↔ Valued.v a ≤ 1 := fun a =>
    HeightOneSpectrum.mem_adicCompletionIntegers ..
  have hint : ∀ ℓ : L, (∀ k, algebraMap ℚ (v.adicCompletion ℚ) (bL.repr ℓ k) ∈ v.adicCompletionIntegers ℚ) →
      IsIntB v bL ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] ℓ) := by
    intro ℓ hℓ k
    rw [repr_tmul_apply, one_mul]; exact hℓ k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hint θ (fun k => hlv (1, k)), hint θ⁻¹ (fun k => hlv (2, k))⟩
  · have hle : Valued.v (2 : v.adicCompletion ℚ) ≤ 1 := by
      have h := (v.adicCompletionIntegers ℚ).add_mem 1 1 (one_mem _) (one_mem _)
      rw [one_add_one_eq_two] at h
      exact (hmem _).1 h
    have hle' : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (1 / 2)) ≤ 1 := (hmem _).1 h2v
    have hprod : Valued.v (2 : v.adicCompletion ℚ) * Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (1 / 2)) = 1 := by
      rw [← map_mul, show (2 : v.adicCompletion ℚ) * algebraMap ℚ (v.adicCompletion ℚ) (1 / 2) = 1 by
        rw [show (2 : v.adicCompletion ℚ) = algebraMap ℚ _ 2 from (map_ofNat _ 2).symm, ← map_mul]; norm_num, map_one]
    refine le_antisymm hle ?_
    calc (1 : _) = _ := hprod.symm
      _ ≤ Valued.v (2 : v.adicCompletion ℚ) * 1 := mul_le_mul' le_rfl hle'
      _ = _ := mul_one _
  · rw [Algebra.TensorProduct.one_def]; exact hint 1 (fun k => hlv (0, k))
  · intro y z hy hz k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum_tmul bL v y, eq_sum_tmul bL v z, Finset.sum_mul_sum, map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun j _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply]
    exact mul_mem (mul_mem (hy i) (hz j)) (hcv (i, j, k))
  · intro y z hy hz k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum_tmul bL v y, eq_sum_tmul bL v z, Finset.sum_mul_sum, map_sum, Finsupp.finsetSum_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finsupp.finsetSum_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply, map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_mul' (mul_le_mul' ((hmem _).1 (hy i)) le_rfl) ((hmem _).1 (hcv (i, j, k))))
      (by simpa using hz j)
  · intro y hy k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum_tmul bL v y, map_sum, map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun i _ => ?_
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, repr_tmul_apply]
    exact mul_mem (hy i) (hsv (i, k))
  · intro y hy k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum_tmul bL v y, map_sum, map_sum, Finsupp.finsetSum_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, repr_tmul_apply, map_mul]
    exact lt_of_le_of_lt (mul_le_mul' le_rfl ((hmem _).1 (hsv (i, k)))) (by simpa using hy i)

theorem unit_fixed_is_norm : ∀ (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L), (∀ x, c (c x) = x) → (∃ x, c x ≠ x) →
    ∀ (κ : Type) (bL : Module.Basis κ ℚ L), ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      ∀ e : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ,
        Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑e = ↑e → IsIntB v bL ↑e →
        IsIntB v bL ↑e⁻¹ → ∃ y : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ,
          (e : v.adicCompletion ℚ ⊗[ℚ] L) = ↑y * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑y := by
  intro L _ _ c hc hne κ bL
  obtain ⟨x, hx⟩ := hne
  set θ : L := x - c x with hθdef
  have hθ : θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hcθ : c θ = -θ := by simp [θ, hc]
  obtain ⟨S, hS⟩ := good_eventually L c κ bL θ
  refine ⟨S, fun v hv e hee hei hei' => ?_⟩
  obtain ⟨h2, h1, hmul, hmulS, hσI, hσS, hθI, hθI'⟩ := hS v hv
  set σ := Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c with hσdef
  have hσσ : ∀ a, σ (σ a) = a := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul r l => simp [σ, hc]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hσinv : ∀ g : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, σ ↑g = ↑g → σ ↑g⁻¹ = ↑g⁻¹ := by
    intro g hg
    calc σ ↑g⁻¹ = σ ↑g⁻¹ * (↑g * ↑g⁻¹) := by simp
      _ = σ (↑g⁻¹ * ↑g) * ↑g⁻¹ := by rw [map_mul, hg]; ring
      _ = ↑g⁻¹ := by simp
  let θu : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ :=
    ⟨1 ⊗ₜ θ, 1 ⊗ₜ θ⁻¹,
      by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hθ, Algebra.TensorProduct.one_def],
      by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, inv_mul_cancel₀ hθ, Algebra.TensorProduct.one_def]⟩
  have hσθ : σ ↑θu = -↑θu := by simp [θu, σ, hcθ, TensorProduct.tmul_neg]
  obtain ⟨z, hzI, hzS⟩ := GlobalTheory.T.exists_twistedNorm_mod_maxIdeal_adicTensor v L c hc κ bL h2 h1 hmul hmulS hσI θu hθI hθI' hσθ e hee hei hei'
  set w := z * σ z with hwdef
  have hwσ : σ w = w := by simp only [w, map_mul, hσσ]; ring
  set u : v.adicCompletion ℚ ⊗[ℚ] L := ↑e⁻¹ * w with hudef
  have huI : IsIntB v bL u := hmul _ _ hei' (hmul _ _ hzI (hσI _ hzI))
  have huS : IsSmallB v bL (u - 1) := by
    have : u - 1 = ↑e⁻¹ * (w - ↑e) := by simp [u, mul_sub]
    rw [this]; exact hmulS _ _ hei' hzS
  obtain ⟨f, hfI, hfI', hf2, hfS, huniq⟩ := GlobalTheory.T.adicIntegralTensorBasis_hensel_exists_unique_sqrt v L κ bL h2 h1 hmul hmulS u huI huS
  have hσu : σ u = u := by simp only [u, map_mul, hσinv e hee, hwσ]
  have hσf : σ ↑f = ↑f := by
    refine huniq _ (hσI _ hfI) (by rw [← map_pow, hf2, hσu]) ?_
    have := hσS _ hfS
    simpa using this
  have hw : w = ↑e * ↑f ^ 2 := by rw [hf2]; simp [u]
  have hzU : IsUnit z := isUnit_of_mul_isUnit_left (x := z) (y := σ z)
    (by rw [← hwdef, hw]; exact e.isUnit.mul (f.isUnit.pow 2))
  obtain ⟨zu, hzu⟩ := hzU
  refine ⟨zu * f⁻¹, ?_⟩
  have hf' := hσinv f hσf
  simp only [Units.val_mul, map_mul, hf', hzu]
  have : (↑e : v.adicCompletion ℚ ⊗[ℚ] L) = w * ↑f⁻¹ * ↑f⁻¹ := by
    rw [hw]; simp [pow_two, mul_assoc]
  rw [this, hwdef]; ring

end GlobalTheory.LocNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOfClassSums
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.AdelicScalar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem form_of_classSums {B X W I κ HV HW : Type} [MeasurableSpace B] [MeasurableSpace X] [Fintype I] [Fintype κ]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [NormedAddCommGroup HV] [InnerProductSpace ℂ HV] [FiniteDimensional ℂ HV]
    [NormedAddCommGroup HW] [InnerProductSpace ℂ HW] [FiniteDimensional ℂ HW]
    (ν : Measure B) (𝓕 : Set B) (μ : Measure X) (𝓖 : Set X) (k : B → X → W → ℂ) (s : I → B) (wt : I → ℂ) (ev : HV → I → W)
    (F : HW → X → ℂ) (N : ℝ) (th : HV →ₗ[ℂ] HW) (Ψ : HW → B → W) (b : OrthonormalBasis κ ℂ W)
    (hV : ∀ x x', inner ℂ x x' = ∑ j, wt j * inner ℂ (ev x j) (ev x' j))
    (hW : ∀ U U', inner ℂ U U' = (N : ℂ) * l2 μ 𝓖 (F U') (F U))
    (hth : ∀ x g, F (th x) g = ∑ j, wt j * k (s j) g (ev x j))
    (hint : ∀ U w h, IntegrableOn (fun g => k h g w * starRingEnd ℂ (F U g)) 𝓖 μ)
    (hΨ : ∀ U h w, inner ℂ (Ψ U h) w = l2 μ 𝓖 (fun g => k h g w) (F U))
    (hex : ∀ U, ∃ a, ∀ j, ev a j = (N : ℂ) • Ψ U (s j)) (U₁ U₂ : HW)
    (hsum : ∫ h in 𝓕, inner ℂ (Ψ U₁ h) (Ψ U₂ h) ∂ν = ∑ j, wt j * inner ℂ (Ψ U₁ (s j)) (Ψ U₂ (s j)))
    (hi : ∀ a, IntegrableOn (fun h => l2 μ 𝓖 (fun g => k h g (b a)) (F U₁) *
      starRingEnd ℂ (l2 μ 𝓖 (fun g => k h g (b a)) (F U₂))) 𝓕 ν) :
    inner ℂ (LinearMap.adjoint th U₁) (LinearMap.adjoint th U₂) = (N : ℂ) ^ 2 *
      ∑ a, l2 ν 𝓕 (fun h => l2 μ 𝓖 (fun g => k h g (b a)) (F U₁)) (fun h => l2 μ 𝓖 (fun g => k h g (b a)) (F U₂)) := by
  have h1 : ∀ U j, ev (LinearMap.adjoint th U) j = (N : ℂ) • Ψ U (s j) := fun U => by
    obtain ⟨a, ha⟩ := hex U
    have : LinearMap.adjoint th U = a := by
      refine ext_inner_right ℂ fun x => ?_
      rw [LinearMap.adjoint_inner_left, hW, hV, l2_sum_eq_sum_norm_sq_of_orthogonal μ 𝓖 wt (fun j g => k (s j) g (ev x j)) _ _ (hth x) fun j => hint U _ _,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ha, inner_smul_left, Complex.conj_ofReal, hΨ, mul_left_comm]
    rwa [this]
  have e2 : ∑ a, l2 ν 𝓕 (fun h => l2 μ 𝓖 (fun g => k h g (b a)) (F U₁)) (fun h => l2 μ 𝓖 (fun g => k h g (b a)) (F U₂)) =
      ∫ h in 𝓕, inner ℂ (Ψ U₁ h) (Ψ U₂ h) ∂ν := by
    refine (integral_finsetSum _ fun a _ => hi a).symm.trans ?_
    congr 1
    funext h
    rw [← b.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hΨ, ← hΨ, inner_conj_symm]
  rw [e2, hsum, hV, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h1, h1, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  ring

theorem inner_law {B W : Type} [Group B] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ρ : B →* Module.End ℂ W)
    (hρ : ∀ h x y, inner ℂ (ρ h x) (ρ h y) = inner ℂ x y) {z : ℂ} (hz : ‖z‖ = 1) (k : B) (a b : W) :
    inner ℂ (z • ρ k a) (z • ρ k b) = inner ℂ a b := by
  rw [inner_smul_left, inner_smul_right, hρ, ← mul_assoc, Complex.conj_mul', hz]
  simp

section Adjoint

variable {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (Datum.WO V W → ℂ)} (hω : Datum.IsWeilDatumO ψ V W χS χT ω)
  (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
  (φ : c.W →ₗ[ℂ] (Datum.WO V W → ℂ)) (hφ : ∀ w, Datum.IsThetaFunO ψ V W (φ w))
  (hinf : ∀ u ∈ GinfC V, ∀ w, ω (u, 1) (φ w) = φ (c.ρ u w))
  (hlev : ∀ κ ∈ Lev.levA V (lev D.sp.cm V.gram β L), ∀ w, ω (κ, 1) (φ w) = (Lev.levChi V β L κ)⁻¹ • φ w)
  {S : D.what₂.Tau → SPar} {M : DSModel W S} {μ : Measure (GA D W)} {𝓖 : Set (GA D W)} (HW : HMod (MMap M)) {N : ℝ}
  (hW : ∀ x y, inner ℂ x y = (N : ℂ) * ipM M μ 𝓖 (HW.e x) (HW.e y))

include hW in
theorem pet_eq (y y' : HW.H) (v w : M.Vec) :
    l2 μ 𝓖 (HW.e y' w) (HW.e y v) = ipM M μ 𝓖 (HW.e y) (HW.e y') * ∏ τ, ⟪(v τ : M.H τ), (w τ : M.H τ)⟫_ℂ := by
  rw [← (isMultiplicityInner_of_model HW hW y y' v w).2, l2_eq_star]

include hW in
theorem inner_eq_pet (y y' : HW.H) (v : M.Vec) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) :
    inner ℂ y y' = (N : ℂ) * l2 μ 𝓖 (HW.e y' v) (HW.e y v) := by
  rw [pet_eq HW hW, hW, Finset.prod_eq_one, mul_one]
  intro τ _
  rw [inner_self_eq_norm_sq_to_K, hv]
  simp

variable {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hν : IsMeasDef V (lev D.sp.cm V.gram β L) ν 𝓕)
  {I : Type} [Fintype I] {y : I → Bridge.Gf V} (hy : Bridge.IsReps (Bridge.ratF V) (grpOf V β L) y)
  (HV : HMod (Bridge.Gf V → c.W))
  (hV : HV.Is (Bridge.AdForms (Bridge.ratF V) c.coef.ρ (grpOf V β L) (chrOf V β L))
    (Bridge.adInner (Bridge.ratF V) (grpOf V β L) y))
  (v : M.Vec) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) (th : HV.H →ₗ[ℂ] HW.H)
  (hth : ∀ x g, HW.e (th x) v g = ∫ h in 𝓕, Datum.thetaKO ω h g (φ (c.ext (HV.e x) h)) ∂ν)
  (hint : ∀ (U : HW.H) w h, IntegrableOn (fun g => Datum.thetaKO ω h g (φ w) * starRingEnd ℂ (HW.e U v g)) 𝓖 μ)

include hc in
theorem upVec_mem (Ψ : GA D V → c.W) (h2 : ∀ γ ∈ GQ V, ∀ k, Lev.finE V k ∈ lev D.sp.cm V.gram β L → ∀ h,
      Ψ (γ * h * k) = Lev.levChi V β L k • c.ρ k⁻¹ (Ψ h)) :
    (fun u => Ψ (finLift V u)) ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (grpOf V β L) (chrOf V β L) :=
  mem_adForms (finHom V).rangeRestrict (GQ V) c.ρ (finLift V) (finLift_spec V) (fun u => hc.1 _ (finLift_mem V u)) Ψ
      fun γ hγ k hk x => h2 γ hγ k ((mem_grpOf V β L k).1 hk) x


include hω hc hφ hinf hlev hW hν hy hV hv hth hint in
theorem form_eq_sum (U₁ U₂ : HW.H) {κ : Type} [Fintype κ] (b : OrthonormalBasis κ ℂ c.W)
    (hi : ∀ k, IntegrableOn (fun h => l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ (b k))) (HW.e U₁ v) *
      starRingEnd ℂ (l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ (b k))) (HW.e U₂ v))) 𝓕 ν) :
    inner ℂ (LinearMap.adjoint th U₁) (LinearMap.adjoint th U₂) = (N : ℂ) ^ 2 *
      ∑ k, l2 ν 𝓕 (fun h => l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ (b k))) (HW.e U₁ v))
        (fun h => l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ (b k))) (HW.e U₂ v)) := by
  have h0 := fun U => exists_upVec hω c hc β L φ hφ hinf hlev μ 𝓖 (HW.e U v) (hint U)
  have h1 := fun U => (h0 U).choose_spec.1
  have h2 := fun U => (h0 U).choose_spec.2
  refine form_of_classSums ν 𝓕 μ 𝓖 (fun h g w => Datum.thetaKO ω h g (φ w)) (fun j => finLift V (y j))
    (fun j => ((Nat.card (Bridge.stab (Bridge.ratF V) (grpOf V β L) (y j)) : ℂ))⁻¹) (fun x j => HV.e x (y j))
    (fun U => HW.e U v) N th (fun U => (h0 U).choose) b hV.2.2 (fun U U' => inner_eq_pet HW hW U U' v hv)
    (fun x g => ?_) hint h1 (fun U => ?_) U₁ U₂ ?_ hi
  · exact (hth x g).trans (theta_classSum hω c hc β L φ hφ hinf hlev hν hy (HMod_mem hV x) g)
  · exact (HMod_onto hV (Submodule.smul_mem _ (N : ℂ) (upVec_mem c hc β L _ (h2 U)))).imp fun a ha j => congrFun ha (y j)
  · refine integral_eq_classSum V β L hν hy _ fun γ hγ k hk x => ?_
    exact (congrArg₂ (inner ℂ) (h2 U₁ γ hγ k hk x) (h2 U₂ γ hγ k hk x)).trans
      (inner_law c.ρ hc.2.1 (norm_levChi β L k) _ _ _)

end Adjoint

theorem tsum_eval {Y : Type} (Z kf p : Y → ℂ) (C s : ℂ) (h1 : ∀ y, Z y = C * kf y * starRingEnd ℂ (p y))
    (h2 : HasSum (fun y => kf y * starRingEnd ℂ (p y)) s) : ∑' y, Z y = C * s := by
  simp only [h1, mul_assoc]
  exact (h2.mul_left C).tsum_eq

theorem integral_pi_eval {ι : Type} [Fintype ι] {X : ι → Type} [∀ ρ, MeasurableSpace (X ρ)] (m : ∀ ρ, Measure (X ρ))
    [∀ ρ, SigmaFinite (m ρ)] (a : ∀ ρ, X ρ → ℂ) (Φ : (∀ ρ, X ρ) → ℂ) (c0 z q : ℂ)
    (h : ∀ b, Φ b = c0 * (∏ ρ, a ρ (b ρ)) * 1 * (z * starRingEnd ℂ (q * ∏ ρ, a ρ (b ρ)))) :
    ∫ b, Φ b ∂(Measure.pi m) = c0 * z * starRingEnd ℂ q * ((∏ ρ, ∫ x, ‖a ρ x‖ ^ 2 ∂(m ρ) : ℝ) : ℂ) := by
  have e : ∀ b, Φ b = c0 * z * starRingEnd ℂ q * ((∏ ρ, ‖a ρ (b ρ)‖ ^ 2 : ℝ) : ℂ) := fun b => by
    have : ((∏ ρ, ‖a ρ (b ρ)‖ ^ 2 : ℝ) : ℂ) = (∏ ρ, a ρ (b ρ)) * starRingEnd ℂ (∏ ρ, a ρ (b ρ)) := by
      rw [Complex.mul_conj', norm_prod]
      push_cast
      rw [Finset.prod_pow]
    rw [h, this, map_mul]
    ring
  simp only [e]
  rw [integral_const_mul, integral_complex_ofReal, integral_fintype_prod_eq_prod fun ρ x => ‖a ρ x‖ ^ 2]

theorem realMat_mem (i : Fin D.R.m) {Fr : Frames (Wc D i)} (hFr : IsFrames (Wc D i) Fr) (ρ : D.what₂.Tau) (b : Upq (Wc D i) ρ) :
    realMat (Wc D i) Fr ρ b ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) ρ) := by
  refine GlobalTheory.AdelicScalar.conjFrame_mem_UH _ _ _ ((sig_add i ρ).trans (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).symm) _ _ (hFr ρ) ?_ b
  rw [gramAt, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact ((map_ne_zero _).2 (GlobalTheory.DefiniteQuotient.gram_hermND (Wc D i)).2).isUnit

theorem rTr_mul (W : HSp D) (a b : GA D W) (F : GA D W → ℂ) : rTr W (a * b) F = rTr W a (rTr W b F) := by
  funext h
  simp only [rTr, mul_assoc]

theorem coef_translate {W : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel W S} {μ : Measure (GA D W)} {𝓖 : Set (GA D W)}
    (HW : HMod (MMap M)) {N : ℝ} (hW : ∀ x y, inner ℂ x y = (N : ℂ) * ipM M μ 𝓖 (HW.e x) (HW.e y)) (θ : Datum.InfFam D)
    {J : Set (GA D W)} {χ : GA D W → ℂ} (U₁ U₂ : HW.H) (hU : HW.e U₁ ∈ Mult θ M J χ)
    (g : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (hg : ∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D W ρ)) (v : M.Vec) :
    ∃ w : M.Vec, rTr W (realElt θ W g) (HW.e U₁ v) = HW.e U₁ w ∧
      l2 μ 𝓖 (HW.e U₁ w) (HW.e U₂ v) =
        ipM M μ 𝓖 (HW.e U₂) (HW.e U₁) * ∏ τ, ⟪(v τ : M.H τ), M.rep τ (g τ) (v τ : M.H τ)⟫_ℂ :=
  ⟨fun ρ => ⟨_, rep_mem_sm M ρ (g ρ) (hg ρ) _ (v ρ).2⟩,
    (GlobalTheory.RealEquiv.mult_realElt D W S θ M J χ _ hU g hg v _ fun _ => rfl).symm, pet_eq HW hW U₂ U₁ v _⟩

theorem eq_of_value {W : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel W S} {μ : Measure (GA D W)} {𝓖 : Set (GA D W)}
    (HW : HMod (MMap M)) {N : ℝ} (hW : ∀ x y, inner ℂ x y = (N : ℂ) * ipM M μ 𝓖 (HW.e x) (HW.e y)) (U₁ U₂ : HW.H) :
    inner ℂ U₁ U₂ = (N : ℂ) * starRingEnd ℂ (ipM M μ 𝓖 (HW.e U₂) (HW.e U₁)) := by
  rw [← inner_conj_symm, hW, map_mul, Complex.conj_ofReal]

end GlobalTheory.AdelicScalar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullAlgebraPartLeSplitHeckePart
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.HeckeSplitPart

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem goodPl (R : RealDat D A Ks) (F : Face D A) (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam)
    {SF : Finset (HeightOneSpectrum (𝓞 D.host.F))} (hSF : IsSF R SF) {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ} (hβ : IsSDFrame V β Λ N)
    (hN : N = 1 ∨ N = D.host.g 0 * D.host.g 1) :
    GlobalTheory.HeckeParts.GoodPl V β R.Pg (A.ok A.μ0) R.pl A.q SF := by
  obtain ⟨hQ, h2, h3, h4⟩ := GlobalTheory.GoodPrimes.good_primes R F hL
  intro P hP
  obtain ⟨hg, hc, hq⟩ := h4 hF _ P hP
  refine ⟨?_, (h3 SF hSF _).2 hg, ?_, fun L hLP hLQ e f hef => ?_⟩
  · rw [hq, Nat.cast_ne_zero]
    exact fun h => (R.pl P).ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  · rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
    exact fun h => hc (HeightOneSpectrum.ext h)
  · obtain ⟨c, hcB⟩ := hβ
    refine (GlobalTheory.LevSplit.lev_split V β Λ _ L hcB).2 (R.pl P) e f hef ?_ ?_
    · intro h
      rw [Nat.cast_pow] at h
      have h' := (R.pl P).isPrime.mem_of_pow_mem _ h
      rcases hN with rfl | rfl
      · exact (R.pl P).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h'))
      · exact (h2 _ _ hg).1 h'
    · rw [hLP, hLQ]
      rintro PP (h | h)
      · exact hg PP (Or.inl h)
      · simp at h

theorem parts_in_hPart : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → ∀ SF, IsSF R SF → ∀ (c : Pl D.host.E → List ℤ → ℂ) (Sg : Pl0 → ℂ[X]), ((∀ P ∈ A.ok A.μ0, Sg P = Formalism.L2.Col.heckePolyOf D.R.r (A.q P) fun k => c (R.pl P) (dualLab (splitLab D.R.r k))) → ∀ x ∈ EEc R SF c, R.HE.e x ∈ hPart (R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv)) (A.ok A.μ0) R.pl A.q Sg) ∧ ∀ i, (∀ P ∈ A.ok A.μ0, Sg P = Formalism.L2.Col.heckePolyOf D.R.r (A.q P) fun k => c (R.pl P) (splitLab D.R.r k)) → ∀ x ∈ Wcc R SF i c, (R.HW i _).e x ∈ hPart (R.MW i (sg0 D A)) (levG _ (R.βW i) (R.datWp i R.triv)) (A.ok A.μ0) R.pl A.q Sg := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s _ hC SF hSF c Sg
  have hY := goodPl R F hC.lev hC.fam hSF (hC.lev.βY 0 (by have := D.R.two_le_m; omega)) (Or.inr rfl)
  have hW := fun i => goodPl R F hC.lev hC.fam hSF (hC.lev.βW i) (Or.inl rfl)
  refine ⟨fun hSg x hx => ?_, fun i hSg x hx => ?_⟩
  · exact GlobalTheory.HeckeParts.mem_hPart_of_partFull (V := Yc D 0) (β := R.βY 0) (r := D.R.r) (t := D.R.t) (hr := r_le_Y 0)
      (Pg := R.Pg) (χ := R.chi) (ξ := fun _ => 1) (c := fun P d => c P (dualLab d)) hY R.triv hx
      (fun P hP => by rw [hSg P hP, GlobalTheory.HeckeParts.rank_zeroth_component_eq])
  · exact GlobalTheory.HeckeParts.mem_hPart_of_partFull (V := Wc D i) (β := R.βW i) (r := D.R.r) (t := D.R.t) (hr := r_le_rank_Wc i)
      (Pg := R.Pg) (χ := fun _ _ => 1) (ξ := fun _ => 1) (c := c) (hW i) R.triv hx.2
      (fun P hP => by rw [hSg P hP, GlobalTheory.HeckeParts.rank_weight_component_eq])

end GlobalTheory.HeckeSplitPart

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockUnitaryFiniteSubspaceComapInjectiveIntertStatement
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBlockUnitaryFiniteSubspace_comap_injective_intertwiner : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (M' : Type) [AddCommGroup M'] [Module ℂ M'] (F' : ι → ι → Module.End ℂ M') (f : M →ₗ[ℂ] M'), Function.Injective f → (∀ a b, s a = s b → ∀ x, f (F a b x) = F' a b (f x)) → (∀ U' : Submodule ℂ M', UnitOn s F' U' → UnitOn s F (U'.comap f)) ∧ (LocU s F' → LocU s F) := by
  first | exact @GlobalTheory.HoweR.unitOn_comap_locU | exact GlobalTheory.HoweR.unitOn_comap_locU | (intros; apply GlobalTheory.HoweR.unitOn_comap_locU <;> assumption)
end

