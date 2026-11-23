module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1555
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1551
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedEqDiagonalLagrangianThetaIntegral
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.LagrThetaAdm

open GlobalTheory.ThetaTrCont
open scoped Classical

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem uniform_majorant {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ (k : ℕ) (c : ℝ), 0 ≤ c ∧ ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (a : κ → AdeleRing (𝓞 F) F),
      ∃ u : (κ → F) → ℝ, Summable u ∧
        ∑' ξ, u ξ ≤ c * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f ∧
        ∀ ξ : κ → F, ‖pureA F f g ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) + a)‖ ≤ u ξ := by
  obtain ⟨KA, hKA, hcov⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  set Kκ : Set (κ → AdeleRing (𝓞 F) F) := Set.univ.pi fun _ => KA
  have hKκ : IsCompact Kκ := isCompact_univ_pi fun _ => hKA
  obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  obtain ⟨R, hR⟩ := hKκ.exists_bound_of_continuousOn (continuous_archV F (κ := κ)).continuousOn
  have hR0 : ∀ b ∈ Kκ, ‖archV F b‖ ≤ max R 0 := fun b hb => (hR b hb).trans (le_max_left _ _)
  set R' := max R 0
  set Kf : Set (κ → FiniteAdeleRing (𝓞 F) F) := (fun p => p.1 - finV F p.2) '' (tsupport g ×ˢ Kκ)
  have hKf : IsCompact Kf := (hg.2.isCompact.prod hKκ).image (continuous_fst.sub ((continuous_finV F).comp continuous_snd))
  obtain ⟨N, hN, hKN⟩ := exists_nat_mul_integral_of_isCompact F hKf
  haveI := discreteTopology_denomLattice F κ hN
  set k := Module.finrank ℤ (denomLattice F κ N) + 1
  set S : Set (κ → F) := {η | (fun i => mixedEmbedding F (η i)) ∈ denomLattice F κ N}
  have hw : Summable (S.indicator fun η => ((1 + ‖(fun i => mixedEmbedding F (η i))‖) ^ k)⁻¹) := by
    rw [← summable_subtype_iff_indicator]
    let j : S → denomLattice F κ N := fun ξ => ⟨_, ξ.2⟩
    have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
    have hs := (summable_one_add_norm_inv (denomLattice F κ N) (k := k) (Nat.lt_succ_self _)).comp_injective hj
    refine hs.congr fun η => ?_
    simp only [Function.comp_apply, j, Submodule.coe_norm]
  set w : (κ → F) → ℝ := S.indicator fun η => ((1 + ‖(fun i => mixedEmbedding F (η i))‖) ^ k)⁻¹ with hwdef
  have hw0 : ∀ η, 0 ≤ w η := fun η => Set.indicator_nonneg (fun _ _ => inv_nonneg.2 (by positivity)) η
  refine ⟨k, B * (1 + R') ^ k * 2 ^ k * ∑' η, w η, by
    have h1 : 0 ≤ ∑' η, w η := tsum_nonneg hw0
    have h2 : 0 ≤ R' := le_max_right _ _
    positivity, fun f a => ?_⟩
  set C := (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  choose y hy using fun i => hcov (a i)
  set b : κ → AdeleRing (𝓞 F) F := fun i => a i - algebraMap F (AdeleRing (𝓞 F) F) (y i)
  have hb : b ∈ Kκ := fun i _ => hy i
  have hab : ∀ ξ : κ → F, (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) + a =
      (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((ξ + y) i)) + b := by
    intro ξ; funext i; simp [b, map_add (f := _)]
  refine ⟨fun ξ => B * ((1 + R') ^ k * (2 ^ k * C)) * w (ξ + y), ?_, ?_, fun ξ => ?_⟩
  · exact ((Equiv.addRight y).summable_iff.2 hw).mul_left _
  · have e : ∑' x, w (x + y) = ∑' η, w η := (Equiv.addRight y).tsum_eq w
    rw [tsum_mul_left, e]
    apply le_of_eq; ring
  · beta_reduce
    rw [hab, pureA_eq, archV_add, finV_add, archV_alg, finV_alg, norm_mul]
    by_cases hξ : ξ + y ∈ S
    · have h1 := schwartz_shift_le f k (fun i => mixedEmbedding F ((ξ + y) i)) (archV F b) (hR0 b hb)
      have e : w (ξ + y) = ((1 + ‖(fun i => mixedEmbedding F ((ξ + y) i))‖) ^ k)⁻¹ := by rw [hwdef, Set.indicator_of_mem hξ]
      rw [e]
      calc _ ≤ ((1 + R') ^ k * (2 ^ k * C) * ((1 + ‖(fun i => mixedEmbedding F ((ξ + y) i))‖) ^ k)⁻¹) * B :=
            mul_le_mul h1 (hB _) (norm_nonneg _) ((norm_nonneg _).trans h1)
        _ = _ := by ring
    · have hg0 : g ((fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) ((ξ + y) i)) + finV F b) = 0 := by
        by_contra h0
        apply hξ
        have hmem : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) ((ξ + y) i)) ∈ Kf :=
          ⟨(_, b), ⟨subset_tsupport _ h0, hb⟩, by simp⟩
        refine fun i => ?_
        obtain ⟨z, hz⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * (ξ + y) i)
          fun v => by
            rw [map_mul, map_natCast]
            exact hKN _ hmem i v
        refine ⟨z, ?_⟩
        have h2 := congrArg (mixedEmbedding F) hz
        rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
        exact h2.symm
      rw [hg0, norm_zero, mul_zero]
      exact mul_nonneg (mul_nonneg hB0 (by have : 0 ≤ R' := le_max_right _ _; positivity)) (hw0 _)

end GlobalTheory.LagrThetaAdm

namespace GlobalTheory.LagrThetaAdm

open GlobalTheory.ThetaTrCont
open scoped Classical

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [Invertible (2 : AdeleRing (𝓞 F) F)]

theorem thetaSum_pure_le (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ (k : ℕ) (c : ℝ), 0 ≤ c ∧ ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
      (p : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)),
      ‖thetaSum F (schr ψ p (pureA F f g))‖ ≤ c * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f := by
  obtain ⟨k, c, hc, h⟩ := uniform_majorant F hg
  refine ⟨k, c, hc, fun f p => ?_⟩
  obtain ⟨u, hu, hsum, hb⟩ := h f p.1
  refine (tsum_of_norm_bounded hu.hasSum fun ξ => ?_).trans hsum
  simp only [schr]
  rw [norm_mul, hψ, one_mul]
  exact hb ξ

theorem thetaSum_schA_bdd (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψc : Continuous ψ) (hψ : ∀ x, ‖ψ x‖ = 1)
    {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    ∃ C : ℝ, ∀ p, ‖thetaSum F (schr ψ p Φ)‖ ≤ C := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨k, c, -, hb⟩ := thetaSum_pure_le F ψ hψ hg
    exact ⟨_, fun p => hb f p⟩
  | zero =>
    refine ⟨0, fun p => ?_⟩
    have e : schr ψ p (0 : (κ → AdeleRing (𝓞 F) F) → ℂ) = 0 := funext fun x => by simp [schr]
    simp [e, thetaSum]
  | add Φ Ψ hΦ hΨ h1 h2 =>
    obtain ⟨C1, hC1⟩ := h1
    obtain ⟨C2, hC2⟩ := h2
    refine ⟨C1 + C2, fun p => ?_⟩
    have e : schr ψ p (Φ + Ψ) = schr ψ p Φ + schr ψ p Ψ := funext fun x => by simp [schr, mul_add]
    have e2 : thetaSum F (schr ψ p (Φ + Ψ)) = thetaSum F (schr ψ p Φ) + thetaSum F (schr ψ p Ψ) := by
      rw [e]
      exact ((schA_cont F ψ hψc hψ hΦ).1 p).tsum_add ((schA_cont F ψ hψc hψ hΨ).1 p)
    rw [e2]
    exact (norm_add_le _ _).trans (add_le_add (hC1 p) (hC2 p))
  | smul a Φ _ h =>
    obtain ⟨C, hC⟩ := h
    refine ⟨‖a‖ * C, fun p => ?_⟩
    have e : schr ψ p (a • Φ) = a • schr ψ p Φ := funext fun x => by
      simp only [schr, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, thetaSum_smul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hC p) (norm_nonneg _)

end GlobalTheory.LagrThetaAdm

namespace GlobalTheory.LagrThetaAdm

open GlobalTheory.ThetaTrCont GlobalTheory.WeilSchrodinger
open scoped Classical

theorem exists_admitted_eq_diagonalLagrangian_thetaIntegral_alt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
      (κ : Type) [Fintype κ]
      (co : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ξ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ),
      (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
        co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∃ l₂ ∈ (adeleClass F).adm κ, ∀ Φ ∈ schA F κ, l₂ Φ = GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JT JB ξ κ _ co hrat ν 𝓕 hν h𝓕
  have hψ : IsCharAF F B.ψ := GlobalTheory.StdCharFromIsStd.isCharAF hB.std
  set Cm : Matrix (Fin (nT + nT)) (Fin nT) (AF F ⊗[F] E) :=
    (diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id with hCm
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hfin : ν 𝓕 < ⊤ :=
    GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc ν h𝓕
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  haveI : IsModuleTopology (AF F) (Matrix (Fin (nT + nT)) (Fin nS) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin (nT + nT) → Fin nS → AE F E))
  have hce : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hCu : Continuous fun u : WOF F E nS nT => Cm * u := continuous_const.matrix_mul continuous_id
  have hcont : ∀ Φ ∈ schA F κ, Continuous fun u : WOF F E nS nT => thetaTr F co B.ψ Φ (Cm * u) :=
    fun Φ hΦ => ((schA_cont F B.ψ hψ.1 hψ.2.1 hΦ).2.comp hce).comp hCu
  have hint : ∀ Φ ∈ schA F κ, Integrable (fun u => thetaTr F co B.ψ Φ (Cm * u)) (ν.restrict 𝓕) := fun Φ hΦ => by
    obtain ⟨C, hC⟩ := thetaSum_schA_bdd F B.ψ hψ.1 hψ.2.1 hΦ
    exact Integrable.of_bound (hcont Φ hΦ).aestronglyMeasurable C (Filter.Eventually.of_forall fun u => hC _)
  have hadd : ∀ Φ ∈ schA F κ, ∀ Ψ ∈ schA F κ, ∀ w,
      thetaTr F co B.ψ (Φ + Ψ) w = thetaTr F co B.ψ Φ w + thetaTr F co B.ψ Ψ w := by
    intro Φ hΦ Ψ hΨ w
    have e : schr B.ψ (co.e w) (Φ + Ψ) = schr B.ψ (co.e w) Φ + schr B.ψ (co.e w) Ψ :=
      funext fun x => by simp [schr, mul_add]
    show thetaSum F (schr B.ψ (co.e w) (Φ + Ψ)) = thetaSum F (schr B.ψ (co.e w) Φ) + thetaSum F (schr B.ψ (co.e w) Ψ)
    rw [e]
    exact ((schA_cont F B.ψ hψ.1 hψ.2.1 hΦ).1 _).tsum_add ((schA_cont F B.ψ hψ.1 hψ.2.1 hΨ).1 _)
  have hsmul : ∀ (a : ℂ) (Φ : (κ → AF F) → ℂ) w, thetaTr F co B.ψ (a • Φ) w = a * thetaTr F co B.ψ Φ w := by
    intro a Φ w
    have e : schr B.ψ (co.e w) (a • Φ) = a • schr B.ψ (co.e w) Φ := funext fun x => by
      simp only [schr, Pi.smul_apply, smul_eq_mul]
      ring
    show thetaSum F (schr B.ψ (co.e w) (a • Φ)) = a * thetaSum F (schr B.ψ (co.e w) Φ)
    rw [e, thetaSum_smul]
  let L : schA F κ →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => GlobalTheory.LagrTheta.lagrInt ν 𝓕 Cm (thetaTr F co B.ψ Φ)
      map_add' := fun Φ Ψ => by
        show ∫ u in 𝓕, thetaTr F co B.ψ (Φ.1 + Ψ.1) (Cm * u) ∂ν =
          ∫ u in 𝓕, thetaTr F co B.ψ Φ.1 (Cm * u) ∂ν + ∫ u in 𝓕, thetaTr F co B.ψ Ψ.1 (Cm * u) ∂ν
        simp_rw [hadd Φ.1 Φ.2 Ψ.1 Ψ.2]
        exact integral_add (hint _ Φ.2) (hint _ Ψ.2)
      map_smul' := fun a Φ => by
        show ∫ u in 𝓕, thetaTr F co B.ψ (a • Φ.1) (Cm * u) ∂ν = a • ∫ u in 𝓕, thetaTr F co B.ψ Φ.1 (Cm * u) ∂ν
        simp_rw [hsmul]
        rw [integral_const_mul, smul_eq_mul] }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend L
  have hlL : ∀ Φ (hΦ : Φ ∈ schA F κ), l Φ = L ⟨Φ, hΦ⟩ := fun Φ hΦ => LinearMap.congr_fun hl ⟨Φ, hΦ⟩
  refine ⟨l, ?_, fun Φ hΦ => hlL Φ hΦ⟩
  intro g hg
  obtain ⟨k, c, hc, hb⟩ := thetaSum_pure_le F B.ψ hψ.2.1 hg
  have hmem : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, pureA F f g ∈ schA F κ := fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hsn : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f =
        ((Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) f := by
    intro f
    rw [Seminorm.finset_sup_apply, Seminorm.finset_sup_apply]
    congr 2
    funext i
    apply NNReal.eq
    simp [schwartzSeminormFamily, SchwartzMap.seminorm_apply]
  refine ⟨SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (fun f => L ⟨pureA F f g, hmem f⟩)
    (fun f f' => ?_) (fun a f => ?_) ⟨Finset.Iic (k, 0), c * ν.real 𝓕, mul_nonneg hc measureReal_nonneg, fun f => ?_⟩,
    fun f => ?_⟩
  · rw [← map_add (f := _)]
    congr 1
    exact Subtype.ext (funext fun x => by simp [pureA, add_mul])
  · rw [RingHom.id_apply, ← map_smul]
    congr 1
    exact Subtype.ext (funext fun x => by simp [pureA, mul_assoc])
  · show ‖∫ u in 𝓕, thetaTr F co B.ψ (pureA F f g) (Cm * u) ∂ν‖ ≤ _
    refine (norm_setIntegral_le_of_norm_le_const hfin fun u _ => hb f (co.e (Cm * u))).trans (le_of_eq ?_)
    rw [hsn]
    ring
  · exact hlL _ (hmem f)

end GlobalTheory.LagrThetaAdm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorStandardCharTrivial
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix nonZeroDivisors

noncomputable section
namespace GlobalTheory.FinSupp

theorem exists_den_of_trace_int (F : Type) [Field F] [NumberField F] :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ t : F, (∀ a : 𝓞 F, ∃ m : ℤ, Algebra.trace ℚ F ((a : F) * t) = m) →
      IsIntegral ℤ ((D : F) * t) := by
  classical
  obtain ⟨c, hc, hfr⟩ := (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)).2
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  refine ⟨Ideal.absNorm (Ideal.span {c}), ?_, fun t ht => ?_⟩
  · rw [Nat.one_le_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc0
  · have hmem : t ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
      have h10 : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
        first | exact one_ne_zero | simp | exact FractionalIdeal.one_ne_zero
      rw [FractionalIdeal.mem_dual h10]
      intro a ha
      obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      obtain ⟨m, hm⟩ := ht b
      refine ⟨m, ?_⟩
      rw [Algebra.traceForm_apply, mul_comm, hm]
      simp
    obtain ⟨y, hy⟩ := hfr t hmem
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {c}))
    have : ((Ideal.absNorm (Ideal.span {c}) : ℕ) : F) * t = ((e * y : 𝓞 F) : F) := by
      have h1 : ((Ideal.absNorm (Ideal.span {c}) : ℕ) : F) = ((e : F) * (c : F)) := by
        have := congrArg (fun z : 𝓞 F => (z : F)) he
        simp only [map_mul, map_natCast] at this
        rw [← this]
      rw [h1, mul_assoc]
      have h2 : (y : F) = (c : F) * t := by
        rw [show (y : F) = algebraMap (𝓞 F) F y from rfl, hy, Algebra.smul_def]
      push_cast
      first | rw [h2] | rw [← h2] | exact congrArg (_ * ·) h2.symm | simp [h2]
    rw [this]
    exact (e * y).isIntegral_coe

theorem trace_int_of_finPart {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (s : F)
    (hs : ψ (finPart F (algebraMap F (AF F) s)) = 1) : ∃ m : ℤ, Algebra.trace ℚ F s = m := by
  set x : AF F := algebraMap F (AF F) s with hx
  set z : AF F := x - finPart F x with hzdef
  have hz : At (evI F) z := by
    intro u hu
    have hu1 : u.1 = 0 := by
      apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
      rw [map_zero]
      exact hu
    show u * z = 0
    refine Prod.ext ?_ ?_
    · change u.1 * (x.1 - (0 : Ainf F)) = 0
      rw [hu1, zero_mul]
    · change u.2 * (x.2 - x.2) = 0
      rw [sub_self, mul_zero]
  have hψz : ψ z = 1 := by
    have h := hψ.2.1 s
    rw [← hx, show x = z + finPart F x by rw [hzdef, sub_add_cancel], AddChar.map_add_eq_mul, hs, mul_one] at h
    exact h
  have hev : evI F z = mixedEmbedding F s := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (x.1 - 0) = _
    rw [sub_zero, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    rfl
  have h := hψ.2.2 z hz
  rw [hψz, hev, GlobalTheory.LatVacArith.trace_mixedEmbedding] at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h.symm
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hq : (((Algebra.trace ℚ F s : ℚ) : ℝ) : ℂ) = -(n : ℂ) := by
    apply mul_right_cancel₀ hne
    linear_combination -hn
  refine ⟨-n, ?_⟩
  push_cast
  exact_mod_cast hq

end GlobalTheory.FinSupp

namespace GlobalTheory.FinSupp.DenStd

theorem exists_den : ∀ (F : Type) [Field F] [NumberField F], ∃ D : ℕ, 1 ≤ D ∧ ∀ ψ : AddChar (AF F) ℂ, IsStd ψ → ∀ t : F,
    (∀ a : 𝓞 F, ψ (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((a : F) * t))) = 1) → IsIntegral ℤ ((D : F) * t) := by
  intro F _ _
  obtain ⟨D, hD, hint⟩ := GlobalTheory.FinSupp.exists_den_of_trace_int F
  exact ⟨D, hD, fun ψ hψ t ht => hint t fun a => GlobalTheory.FinSupp.trace_int_of_finPart hψ _ (ht a)⟩

end GlobalTheory.FinSupp.DenStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivReps
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResLine

theorem exists_equiv_reps {G : Type} [Group G] (Γ Λ : Subgroup G) (T : Set Γ)
    (hT : ∀ γ : Γ, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : Γ) : G) ∈ Λ) (γ : Γ) :
    ∃ π : T ≃ T, ∀ i : T, ((i.1 * γ * (π i).1⁻¹ : Γ) : G) ∈ Λ := by
  choose ρ hρ hu using hT
  have key : ∀ (a b : Γ), a * b = 1 → ∀ i : T, ρ (ρ (i.1 * a) * b) = i.1 := by
    intro a b hab i
    symm
    refine hu _ _ ⟨i.2, ?_⟩
    have := Λ.inv_mem (hρ (i.1 * a)).2
    have e : ρ (i.1 * a) * b * i.1⁻¹ = (i.1 * a * (ρ (i.1 * a))⁻¹)⁻¹ := by
      rw [eq_inv_of_mul_eq_one_right hab]; group
    rw [e, Subgroup.coe_inv]
    exact this
  exact ⟨⟨fun i => ⟨ρ (i.1 * γ), (hρ _).1⟩, fun i => ⟨ρ (i.1 * γ⁻¹), (hρ _).1⟩,
    fun i => Subtype.ext (key γ γ⁻¹ (mul_inv_cancel _) i), fun i => Subtype.ext (key γ⁻¹ γ (inv_mul_cancel _) i)⟩,
    fun i => (hρ _).2⟩

theorem reps_perm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), Data σ J X Y L a h → ∀ T, IsReps σ J (col X) T → (∀ γ ∈ ratPts σ J, ∃ π : T ≃ T, ∀ (i : T) g, h (i.1.1 * (γ * g)) = h ((π i).1.1 * g)) ∧ (∃ i : T, ∀ g, h (i.1.1 * g) = h g) ∧ (∀ γ ∈ (ratPts σ J ⊓ lineGrp σ J (col X)), ∀ g, h (γ * g) = h g) ∧ ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : ratPts σ J) : GAd σ J) ∈ (ratPts σ J ⊓ lineGrp σ J (col X)) := by
  intro F E _ _ _ _ _ σ n J r X Y L a h D T hT
  have h3 : ∀ γ ∈ (ratPts σ J ⊓ lineGrp σ J (col X)), ∀ g, h (γ * g) = h g := by
    rintro γ ⟨hγ, l, hl⟩ g
    rw [(_root_.GlobalTheory.ResLine.iwasawaHeight_isHt F E σ n J r X Y L a h D).2 γ l hl g,
      (_root_.GlobalTheory.ResLine.LeviFacts.levi_facts F E σ n J r X Y D.cm D.herm D.witt).2.2.2.2.2 γ hγ l hl]
    simp
  have h4 : ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : ratPts σ J) : GAd σ J) ∈ (ratPts σ J ⊓ lineGrp σ J (col X)) := by
    intro γ
    obtain ⟨t, ⟨ht, hl⟩, hu⟩ := hT γ
    exact ⟨t, ⟨ht, (γ * t⁻¹).2, hl⟩, fun s hs => hu s ⟨hs.1, hs.2.2⟩⟩
  refine ⟨fun γ hγ => ?_, ?_, h3, h4⟩
  · obtain ⟨π, hπ⟩ := exists_equiv_reps _ _ T h4 ⟨γ, hγ⟩
    refine ⟨π, fun i g => ?_⟩
    rw [← h3 _ (hπ i) ((π i).1.1 * g)]
    congr 1
    simp [mul_assoc]
  · obtain ⟨t, ⟨ht, hl⟩, -⟩ := h4 1
    refine ⟨⟨t, ht⟩, fun g => ?_⟩
    rw [← h3 _ hl (t.1 * g)]
    congr 1
    simp

end GlobalTheory.ResLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicHaarIntegralPointsOne
section
open scoped Matrix GlobalTheory.VacAny ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.FinAdeleHaarNorm

open scoped RestrictedProduct Topology

theorem isCompact_integral (F : Type) [Field F] [NumberField F] :
    IsCompact {b : Af F | ∀ v : HeightOneSpectrum (𝓞 F), evalV F v b ∈ v.adicCompletionIntegers F} := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

theorem isOpen_integral (F : Type) [Field F] [NumberField F] :
    IsOpen {b : Af F | ∀ v : HeightOneSpectrum (𝓞 F), evalV F v b ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)

theorem exists_addHaar_integral_eq_one : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → Af F)] [BorelSpace (κ → Af F)],
    ∃ μf : Measure (κ → Af F), μf.IsAddHaarMeasure ∧ μf {y | ∀ i (v : HeightOneSpectrum (𝓞 F)), evalV F v (y i) ∈ v.adicCompletionIntegers F} = 1 := by
  intro F _ _ κ _ _ _
  set U : Set (κ → Af F) := {y | ∀ i (v : HeightOneSpectrum (𝓞 F)), evalV F v (y i) ∈ v.adicCompletionIntegers F}
  have hU : U = Set.pi Set.univ (fun _ : κ =>
      {b : Af F | ∀ v : HeightOneSpectrum (𝓞 F), evalV F v b ∈ v.adicCompletionIntegers F}) := by
    ext y; simp [U]
  have hc : IsCompact U := hU ▸ isCompact_univ_pi (fun _ => isCompact_integral F)
  have ho : IsOpen U := hU ▸ isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_integral F)
  have h0 : (0 : κ → Af F) ∈ U := fun i v => by simp
  let K₀ : TopologicalSpace.PositiveCompacts (κ → Af F) :=
    ⟨⟨U, hc⟩, ⟨0, ho.interior_eq.symm ▸ h0⟩⟩
  exact ⟨Measure.addHaarMeasure K₀, inferInstance, Measure.addHaarMeasure_self⟩

end GlobalTheory.FinAdeleHaarNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxCoordinatesTensorHermitianStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_darboux_coordinates_tensor_hermitian : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d), ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k)) := by
  first | exact @GlobalTheory.RatDarboux.exists_rational_darboux_of_isGood | exact GlobalTheory.RatDarboux.exists_rational_darboux_of_isGood | (intros; apply GlobalTheory.RatDarboux.exists_rational_darboux_of_isGood <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedPointGenericFibreCoordinatesEqFrameStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedPoint_genericFibre_coordinates_eq_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (T : CDVR) (iK : K →+* T.Fr), letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (t' : SAB H (Sp T.Fr)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x), m1'.φ = n'.φ ≫ m1.φ → ∀ (v' : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G)), IsLieBasis v' → (∀ k, (v' k).left ≫ n'.φ ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ (F.v k).left ≫ F.φ) → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → ∀ (i : Fin (Dw.mult ρ)) (u'' : Sp (DualNumber T.Fr) ⟶ t'.G.left), u'' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) → u'' ≫ m1'.φ = y'.u ρ i → ∃ w'' : epsR T.Fr ⟶ t'.G, w''.left = u'' ∧ IsLieComb (∑ j, C ρ i j • fun k => iK (u j k)) v' w'' := by
  first | exact @GlobalTheory.PtDeg.frame_genFib_coords | exact GlobalTheory.PtDeg.frame_genFib_coords | (intros; apply GlobalTheory.PtDeg.frame_genFib_coords <;> assumption)
end

