module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankZetaSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0935
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1295
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import GroundTheory.GlobalFields.TateThesis.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankCoinvariantInducedIso
section
noncomputable section

open MeasureTheory GlobalTheory.SplitFlip
open scoped Topology Matrix

namespace GlobalTheory.FullRankCoinv

theorem sb_right_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (Ψ : Matrix (Fin n) (Fin d) k → ℂ), Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) →
    ∃ U ∈ nhds (1 : GL (Fin d) k), ∀ u ∈ U, ∀ X : Matrix (Fin n) (Fin d) k, Ψ (X * u.val) = Ψ X := by
  intro k _ _ _ _ n d Ψ hΨ
  have h1 : ∀ᶠ u in 𝓝 (1 : GL (Fin d) k), ∀ X ∈ tsupport Ψ, Ψ (X * u.val) = Ψ X := by
    refine IsCompact.eventually_forall_of_forall_eventually hΨ.2 fun y _ => ?_
    have h2 : IsLocallyConstant fun q : GL (Fin d) k × Matrix (Fin n) (Fin d) k => (Ψ (q.2 * q.1.val), Ψ q.2) :=
      (hΨ.1.comp_continuous (by fun_prop)).prodMk (hΨ.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (1, y)] with q hq
    simp only [Prod.mk.injEq, Units.val_one, Matrix.mul_one] at hq
    rw [hq.1, hq.2]
  have h3 : ∀ᶠ u in 𝓝 (1 : GL (Fin d) k), ∀ X ∈ tsupport Ψ, Ψ (X * (u⁻¹).val) = Ψ X := by
    have ht : Filter.Tendsto (fun u : GL (Fin d) k => u⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv.tendsto (1 : GL (Fin d) k))
    exact ht.eventually h1
  refine ⟨_, h1.and h3, fun u hu X => ?_⟩
  by_cases hX : X ∈ tsupport Ψ
  · exact hu.1 X hX
  by_cases hX' : X * u.val ∈ tsupport Ψ
  · have := hu.2 _ hX'
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hX, image_eq_zero_of_notMem_tsupport hX']

theorem fibre_coinvariants : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∃ Z : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] (GL (Fin d) k → ℂ),
      (∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ ∈ GlobalTheory.FullRankCoinv.indSp k n d ν) ∧
      (∀ f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν, ∃ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ = f) ∧
      (∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ = 0 → Ψ ∈ GlobalTheory.FullRankCoinv.augRk n d ν) ∧
      ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ h₀ : GL (Fin d) k,
        Z (fun Y => Ψ (Y * h₀.1)) = fun h => Z Ψ (h * h₀) := by
  intro k _ _ _ _ n d ν hnd hν
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  let Z₀ : fullRk k n d →ₗ[ℂ] (GL (Fin d) k → ℂ) :=
    { toFun := fun Ψ h => smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ.1 (Y0 k n d * h.val)
      map_add' := fun Ψ Φ => by
        funext h
        simp only [smallF, Submodule.coe_add, Pi.add_apply]
        rw [← integral_add (_root_.GlobalTheory.FullRankCoinv.integrable_fibre_target k n d ν hν Ψ.1 Ψ.2 _) (_root_.GlobalTheory.FullRankCoinv.integrable_fibre_target k n d ν hν Φ.1 Φ.2 _)]
        congr 1; funext g; ring
      map_smul' := fun c Ψ => by
        funext h
        simp only [smallF, SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1; funext g; ring }
  obtain ⟨Z, hZ⟩ := LinearMap.exists_extend Z₀
  have hZΨ : ∀ Ψ (hΨ : Ψ ∈ fullRk k n d),
      Z Ψ = fun h => smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ (Y0 k n d * h.val) :=
    fun Ψ hΨ => LinearMap.congr_fun hZ ⟨Ψ, hΨ⟩
  refine ⟨Z, fun Ψ hΨ => ?_, fun f hf => ?_, fun Ψ hΨ h0 => ?_, fun Ψ hΨ h₀ => ?_⟩
  · rw [hZΨ Ψ hΨ]
    refine ⟨?_, fun b h D hD => ?_⟩
    · obtain ⟨U, hU, hinv⟩ := sb_right_invariant k n d Ψ hΨ.1
      refine ⟨U, hU, fun h u hu => ?_⟩
      simp only [smallF]
      congr 1; funext g
      rw [Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hinv u hu, Matrix.mul_assoc]
    · have e1 : Y0 k n d * (b * h).val = D.val * (Y0 k n d * h.val) := by
        rw [Units.val_mul, ← Matrix.mul_assoc, hD, Matrix.mul_assoc]
      have key := smallF_mul_left (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ D (Y0 k n d * h.val)
      simp only [Fintype.card_fin] at key
      show smallF _ ν Ψ (Y0 k n d * (b * h).val) = _
      rw [e1]
      beta_reduce
      rw [← key, Units.val_inv_eq_inv_val, neg_div, apow_neg]
      have h1 : (ν (gdet D) : ℂ) ≠ 0 := Units.ne_zero _
      have h2 := apow_ne_zero (gdet D) ((d : ℂ) / 2)
      field_simp
  · obtain ⟨Ψ, hΨ, hf'⟩ := _root_.GlobalTheory.FullRankOnto.exists_fullRk_smallF_eq k n d ν hnd hν f hf
    exact ⟨Ψ, hΨ, by rw [hZΨ Ψ hΨ]; funext h; exact hf' h⟩
  · refine _root_.GlobalTheory.FullRankCoinv.mem_augRk_of_fibre_eq_zero k n d ν hnd hν Ψ hΨ fun h => ?_
    have := congrFun h0 h
    rwa [hZΨ Ψ hΨ] at this
  · have hmem : (fun Y => Ψ (Y * h₀.1)) ∈ fullRk k n d := by
      let e : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k :=
        { toFun := fun X => X * h₀.1
          invFun := fun X => X * (h₀⁻¹).1
          left_inv := fun X => by simp [Matrix.mul_assoc]
          right_inv := fun X => by simp [Matrix.mul_assoc]
          continuous_toFun := by fun_prop
          continuous_invFun := by fun_prop }
      refine ⟨⟨hΨ.1.1.comp_continuous e.continuous, hΨ.1.2.comp_homeomorph e⟩, fun Y hY => hΨ.2 _ ?_⟩
      rwa [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units h₀)]
    rw [hZΨ _ hmem, hZΨ _ hΨ]
    funext h
    simp only [smallF, Units.val_mul, Matrix.mul_assoc]

end GlobalTheory.FullRankCoinv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianMulMultilinearDiagonalMemSchwartzSubmodu
section
open MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.ConvSeries

theorem exists_mem_prod_mul_gauss {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : Submodule ℂ (SchwartzMap E ℂ))
    (hM : ∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M)
    (G : SchwartzMap E ℂ) (hG : G ∈ M) :
    ∀ (m : ℕ) (ℓ : Fin m → E →L[ℝ] ℝ), ∃ t ∈ M, ∀ y, t y = (∏ i, ((ℓ i y : ℝ) : ℂ)) * G y := by
  intro m
  induction m with
  | zero => intro ℓ; exact ⟨G, hG, fun y => by simp⟩
  | succ m ih =>
    intro ℓ
    obtain ⟨t, ht, hty⟩ := ih (fun i => ℓ i.succ)
    have hg : (fun x : E => ((ℓ 0 x : ℝ) : ℂ)).HasTemperateGrowth :=
      (Complex.ofRealCLM.comp (ℓ 0)).hasTemperateGrowth
    refine ⟨SchwartzMap.smulLeftCLM ℂ (fun x : E => ((ℓ 0 x : ℝ) : ℂ)) t,
      hM (ℓ 0) t _ ht (fun x => by rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]), fun y => ?_⟩
    rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul, hty, Fin.prod_univ_succ, mul_assoc]

theorem gauss_mul_diag_mem : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Submodule ℂ (SchwartzMap E ℂ)),
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
    ∀ (c : ℝ), 0 < c →
    (∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M) →
    ∀ (k : ℕ) (B : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℂ),
      ∃ t ∈ M, ∀ y, t y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * B (fun _ => y) := by
  intro E _ _ _ M hM c hc hGM k B
  have hin : ∀ x : E, innerSL ℝ x x = ‖x‖ ^ 2 := fun x => by
    first
    | rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
    | simp [real_inner_self_eq_norm_sq]
    | exact real_inner_self_eq_norm_sq x
  obtain ⟨G, hG⟩ := GlobalTheory.GaussSchwartz.exists_schwartz_exp_diag (-c • innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)
    (fun x hx => by
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]; rw [hin]
      have : 0 < ‖x‖ ^ 2 := by positivity
      nlinarith)
  have hG' : ∀ y, G y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) := fun y => by
    rw [hG, Complex.ofReal_exp]
    congr 1
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]; rw [hin]
    push_cast; ring
  have hGmem := hGM G hG'
  let b := stdOrthonormalBasis ℝ E
  have key : ∀ r : Fin k → Fin (Module.finrank ℝ E), ∃ t ∈ M,
      ∀ y, t y = (∏ j, ((innerSL ℝ (b (r j)) y : ℝ) : ℂ)) * G y :=
    fun r => exists_mem_prod_mul_gauss M hM G hGmem k (fun j => innerSL ℝ (b (r j)))
  choose t ht hty using key
  refine ⟨∑ r, B (fun j => b (r j)) • t r, M.sum_mem fun r _ => M.smul_mem _ (ht r), fun y => ?_⟩
  have hy : (fun _ : Fin k => y) = fun _ : Fin k => ∑ i, (inner ℝ (b i) y) • b i := by
    funext _; exact (b.sum_repr' y).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hy, ContinuousMultilinearMap.map_sum, Finset.mul_sum, SchwartzMap.sum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [B.map_smul_univ (fun j => inner ℝ (b (r j)) y) (fun j => b (r j)), SchwartzMap.smul_apply, hty, hG',
    Complex.real_smul, smul_eq_mul]
  have hi : ∀ v : E, innerSL ℝ v y = inner ℝ v y := fun v => rfl
  simp only [hi]
  push_cast
  ring

end GlobalTheory.ConvSeries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericGlLocalComponentExponentLeOne
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ThK.DetProd

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Local

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_isGeneric_of_isLocComp {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}
    {τ : GlobalTheory.CuspRep.CuspSub E n} {w : HeightOneSpectrum (𝓞 E)}
    {ρ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) (w.adicCompletion E))} (h : τ.IsLocComp w ρ) :
    ∃ ψ : AddChar (w.adicCompletion E) Circle, Continuous ψ ∧ ψ ≠ 1 ∧ GlobalTheory.Whittaker.IsGeneric ψ ρ.ρ := by
  obtain ⟨f, hf0, hf⟩ := h
  let S : Subrepresentation (τ.locRep w) := ⟨LinearMap.range f, by
    rintro g _ ⟨v, rfl⟩
    exact ⟨ρ.ρ g v, hf g v⟩⟩
  have hS : S.toSubmodule ≠ ⊥ := fun h => hf0 (LinearMap.range_eq_bot.1 h)
  obtain ⟨ψ, hc, h1, hg⟩ := GlobalTheory.CuspDetBlocks.exists_isGeneric_subrep τ w S hS
  exact ⟨ψ, hc, h1, hg.of_surjective (σ := S.toRepresentation) ⟨f.rangeRestrict, fun g => LinearMap.ext fun v => by exact Subtype.ext (hf g v)⟩
    (LinearMap.surjective_rangeRestrict _)⟩

end GlobalTheory.ThK.DetProd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeomPointsFactorHenselianOfSpecializes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open Polynomial

theorem geomPoints_factor_henselian_of_specializes :
  ∀ {X : Scheme.{0}} {k k' : Type} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] (x : Sp k ⟶ X) (x' : Sp k' ⟶ X) (u : Sp k) (u' : Sp k'), x'.base u' ⤳ x.base u → ∃ (R : Type) (_ : CommRing R) (_ : HenselianLocalRing R) (_ : IsAlgClosed (IsLocalRing.ResidueField R)) (r : Sp R ⟶ X) (i : Sp k ⟶ Sp R) (i' : Sp k' ⟶ Sp R), i ≫ r = x ∧ i' ≫ r = x' := by
  intro X k k' _ _ _ _ x x' u u' hsp
  have hAffine := exists_ringHom_pair_of_specializes x x' u u' hsp
  obtain ⟨B, _, g, g', ρ, hker, hx, hx'⟩ := hAffine
  set q := RingHom.ker g' with hq
  haveI : q.IsPrime := RingHom.ker_isPrime g'
  let D := B ⧸ q
  let h' : D →+* k' := RingHom.kerLift g'
  have h'inj : Function.Injective h' := RingHom.kerLift_injective g'
  let h : D →+* k := Ideal.Quotient.lift q g (fun b hb => hker hb)
  obtain ⟨C, _, _, hCdom, hCint, hCinj, hCroot, hCext⟩ := _root_.GlobalTheory.exists_integral_domain_extension_monic_roots D
  obtain ⟨e', he'inj, he'⟩ := hCext k' h' h'inj
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_ringHom_extend_of_isIntegral_of_isAlgClosed D C k h (by
    intro a ha; rw [RingHom.mem_ker] at ha ⊢
    rw [show a = 0 from hCinj (by rw [ha, map_zero])]; exact map_zero h)
  let P := RingHom.ker ψ
  haveI : P.IsPrime := RingHom.ker_isPrime ψ
  let R := Localization.AtPrime P
  have h0 : (0 : C) ∉ P.primeCompl := fun h0 => h0 P.zero_mem
  have hRloc := (absIntClosed_localization_and_quotient C ⟨hCdom, hCroot⟩).1 P.primeCompl h0
  obtain ⟨hH, hAC, -⟩ := AbsIntClosedLocal.henselian_isAlgClosed_pow_surj R hRloc
  let φ : B →+* R := (algebraMap C R).comp ((algebraMap D C).comp (Ideal.Quotient.mk q))
  let f : R →+* k := IsLocalization.lift (M := P.primeCompl) (g := ψ) (fun s => by
    refine IsUnit.mk0 _ ?_
    exact s.2)
  let f' : R →+* k' := IsLocalization.lift (M := P.primeCompl) (g := e') (fun s => by
    refine IsUnit.mk0 _ ?_
    intro hs
    exact s.2 (by rw [show (s : C) = 0 from he'inj (by rw [hs, map_zero])]; exact P.zero_mem))
  have hf : f.comp φ = g := by
    ext b
    simp only [f, φ, RingHom.comp_apply, IsLocalization.lift_eq]
    rw [← RingHom.comp_apply ψ, hψ]
    rfl
  have hf' : f'.comp φ = g' := by
    ext b
    simp only [f', φ, RingHom.comp_apply, IsLocalization.lift_eq]
    rw [← RingHom.comp_apply e', he']
    rfl
  refine ⟨R, inferInstance, hH, hAC, spMap φ ≫ ρ, spMap f, spMap f', ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hf, hx]
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hf', hx']

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlParabolicOrbitRepresentatives
section
open Matrix

namespace GlobalTheory.OrbitsGLParab

variable {k : Type} [Field k]

variable {n m : ℕ}



end GlobalTheory.OrbitsGLParab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalNormOfLocalNorms
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HasseFld

open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

theorem isValue_of_local {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (Q : SelfRecip E r) {θ : E} (h0 : θ ≠ 0) (hθ : IsCMField.complexConj E θ = -θ) {d : plus Q}
    (hd : (d : Fld Q) = algebraMap E _ θ * algebraMap E _ θ)
    (k : Type) [Field k] [Algebra (maximalRealSubfield E) k]
    (x : plus Q) (hx : x ≠ 0) (z : k ⊗[maximalRealSubfield E] Fld Q)
    (hz : z * involBase Q k z = 1 ⊗ₜ (x : Fld Q)) :
    GlobalTheory.TraceClasses.IsValue (1 ⊗ₜ d) (1 ⊗ₜ x : k ⊗[maximalRealSubfield E] plus Q) := by
  let U : (k ⊗[maximalRealSubfield E] plus Q)ˣ :=
    Units.map (Algebra.TensorProduct.includeRight :
      plus Q →ₐ[maximalRealSubfield E] k ⊗[maximalRealSubfield E] plus Q).toMonoidHom (Units.mk0 x hx)
  have hU : (U : k ⊗[maximalRealSubfield E] plus Q) = 1 ⊗ₜ x := rfl
  have hi : inclPlus Q k (1 ⊗ₜ x) = 1 ⊗ₜ (x : Fld Q) := by simp [inclPlus]
  have hzu : IsUnit z := by
    have : IsUnit (z * involBase Q k z) := by
      rw [hz, ← hi, ← hU]; exact U.isUnit.map _
    exact isUnit_of_mul_isUnit_left this
  have hmem : U ∈ norms Q k := ⟨hzu.unit, Units.ext (by
      change z * involBase Q k z = inclPlus Q k (U : _)
      rw [hz, hU, hi])⟩
  rw [← hU]
  exact (GlobalTheory.TraceClasses.mem_norms_iff Q h0 hθ k hd U).1 hmem

theorem hasse_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (Q : SelfRecip E r) (x : Fld Q), invol Q x = x →
    (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      ∃ z : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] Fld Q,
        z * involBase Q _ z = 1 ⊗ₜ x) →
    (∀ v : InfinitePlace (maximalRealSubfield E),
      ∃ z : v.Completion ⊗[maximalRealSubfield E] Fld Q, z * involBase Q _ z = 1 ⊗ₜ x) →
    ∃ y : Fld Q, y * invol Q y = x := by
  intro E _ _ _ r Q x hxx hf hi
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  obtain ⟨θ, h0, hθ⟩ : ∃ θ : E, θ ≠ 0 ∧ IsCMField.complexConj E θ = -θ := by
    obtain ⟨w, hw⟩ : ∃ w : E, IsCMField.complexConj E w ≠ w := by
      by_contra h
      push_neg at h
      exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h)
    exact ⟨w - IsCMField.complexConj E w, sub_ne_zero.mpr hw.symm, by simp⟩
  let x' : plus Q := ⟨x, hxx⟩
  have hx' : x' ≠ 0 := fun h => hx (congrArg Subtype.val h)
  let d : plus Q := ⟨algebraMap E _ θ * algebraMap E _ θ, by
    show invol Q _ = (AlgHom.id _ _) _
    rw [map_mul, GlobalTheory.TraceClasses.invol_theta Q hθ]
    simp⟩
  have hd : (d : Fld Q) = algebraMap E _ θ * algebraMap E _ θ := rfl
  obtain ⟨e, e0, e1⟩ := GlobalTheory.TraceClasses.exists_basis_theta Q h0 hθ
  have := GlobalTheory.TraceClasses.isQuadraticExtension Q h0 hθ
  have e2 : e 1 * e 1 = algebraMap _ _ d := by rw [e1]; exact hd.symm
  obtain ⟨a, b, hab⟩ := GlobalTheory.TraceClasses.form_of_local (F := maximalRealSubfield E) e e0 e2
    (Units.mk0 x' hx')
    (fun v => by
      obtain ⟨z, hz⟩ := hf v
      exact isValue_of_local Q h0 hθ hd _ x' hx' z hz)
    (fun v => by
      obtain ⟨z, hz⟩ := hi v
      exact isValue_of_local Q h0 hθ hd _ x' hx' z hz)
  refine ⟨a + b * algebraMap E _ θ, ?_⟩
  have hx2 : x = (a : Fld Q) ^ 2 - d * b ^ 2 := by
    have := congrArg Subtype.val hab
    simpa using this
  rw [map_add (f := _), map_mul, GlobalTheory.TraceClasses.invol_coe, GlobalTheory.TraceClasses.invol_coe,
    GlobalTheory.TraceClasses.invol_theta Q hθ, hx2, hd]
  ring

end GlobalTheory.HasseFld
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDetHermitianTotallyPositive
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.UnitaryClasses

theorem gramOn_one_map_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (V : Submodule E (Fin n → E)) (τ : E →+* ℂ) :
    (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).map τ =
      (Matrix.of fun k i => τ ((Module.finBasis E V i).1 k) :
        Matrix (Fin n) (Fin (Module.finrank E V)) ℂ)ᴴ *
      (Matrix.of fun k i => τ ((Module.finBasis E V i).1 k)) := by
  ext i j
  simp [gramOn, hform, Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply,
    IsCMField.complexEmbedding_complexConj, mul_ite, ite_mul, Finset.sum_ite_eq]

theorem gramOn_basis_mulVec_injective {E : Type} [Field E] {n : ℕ}
    (V : Submodule E (Fin n → E)) (τ : E →+* ℂ) :
    Function.Injective (Matrix.of fun k i => τ ((Module.finBasis E V i).1 k) :
        Matrix (Fin n) (Fin (Module.finrank E V)) ℂ).mulVec := by
  first
  | exact @_root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis
  | exact _root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis
  | (apply _root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis <;> assumption)
  | (intros; apply _root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis <;> assumption)
  | (intros; apply @_root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis ..)

theorem gramOn_one_det_totallyPositive : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (V : Submodule E (Fin n → E)), (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det ≠ 0 ∧ ∀ τ : E →+* ℂ, ∃ r : ℝ, 0 < r ∧ τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det = r := by
  intro E _ _ _ n V
  have key : ∀ τ : E →+* ℂ, 0 < τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det := by
    intro τ
    rw [RingHom.map_det]
    have : τ.mapMatrix (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V) =
        (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).map τ := rfl
    rw [this, gramOn_one_map_eq]
    exact (Matrix.PosDef.conjTranspose_mul_self _ (gramOn_basis_mulVec_injective V τ)).det_pos
  refine ⟨fun h0 => ?_, fun τ => ?_⟩
  · have τ0 := (Classical.arbitrary (NumberField.InfinitePlace E)).embedding
    have := key τ0
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  · have h := Complex.lt_def.mp (key τ)
    refine ⟨(τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det).re, h.1, ?_⟩
    apply Complex.ext
    · simp
    · simpa using h.2.symm

end GlobalTheory.UnitaryClasses
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarScalingNormAdditive
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.NormScaleHaar
open Formalism.UG GlobalTheory.AdelicU

theorem ideleModule_norm (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (t : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) :
    ((GroundTheory.Global.IdeleGroup.ideleModule F (Units.map (Algebra.norm (AF F)) t) : ℝ)) = (absE F E t : ℝ) := by
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq, GlobalTheory.Doubling.absE_apply, NNReal.coe_mul, NNReal.coe_prod]
  have h := NNReal.toRealHom.toMonoidHom.map_finprod (GlobalTheory.Doubling.finite_mulSupport_absEv t)
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun w _ => ?_) (Eq.trans ?_ h.symm)
  · rw [GlobalTheory.Doubling.absEw_unitInf, NNReal.coe_pow, coe_nnnorm]
    rfl
  · refine finprod_congr fun v => ?_
    rw [GlobalTheory.Doubling.absEv_unitFin]
    rfl

end GlobalTheory.NormScaleHaar
end
end

