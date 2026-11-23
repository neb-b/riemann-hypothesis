module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0035
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import GroundTheory.GlobalFields.NormResidueSymbol.Bundle0002
public import GroundTheory.GlobalFields.NormResidueSymbol.Bundle0001
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1720
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0234
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedAtValueHeckeCharCompIdeleNorm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0232
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseChangeIsomorphicFields
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0244
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnExistsChainChartsKernelDataForms
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairBaseChangePolarizedSameWeight
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.LiftPolar

theorem conj_algebraMap {E M : Type} [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] (x : E) :
    IsCMField.complexConj M (algebraMap E M x) = algebraMap E M (IsCMField.complexConj E x) := by
  obtain ⟨j⟩ : Nonempty (M →+* ℂ) := inferInstance
  apply j.injective
  rw [IsCMField.complexEmbedding_complexConj M j]
  exact (IsCMField.complexEmbedding_complexConj E (j.comp (algebraMap E M)) x).symm

theorem cPl_asIdeal {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    (UpperTheory.V.Af.Bc.cPl w).asIdeal =
      w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv : 𝓞 E →+* 𝓞 E) :=
  (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w)

theorem cPl_under {E M : Type} [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] (w : HeightOneSpectrum (𝓞 M)) :
    (UpperTheory.V.Af.Bc.cPl w).under (𝓞 E) = UpperTheory.V.Af.Bc.cPl (w.under (𝓞 E)) := by
  apply HeightOneSpectrum.ext
  rw [cPl_asIdeal]
  change (UpperTheory.V.Af.Bc.cPl w).asIdeal.comap (algebraMap (𝓞 E) (𝓞 M)) = (w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 M))).comap _
  rw [cPl_asIdeal, Ideal.comap_comap, Ideal.comap_comap]
  congr 1
  ext x
  exact conj_algebraMap (x : E)

theorem normV_cPl {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    normV (UpperTheory.V.Af.Bc.cPl w) = normV w := by
  show Nat.card (𝓞 E ⧸ (UpperTheory.V.Af.Bc.cPl w).asIdeal) = Nat.card (𝓞 E ⧸ w.asIdeal)
  refine Nat.card_congr (Ideal.quotientEquiv _ _
    (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv) ?_).toEquiv
  rw [cPl_asIdeal]
  exact (Ideal.map_comap_of_surjective
    (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv : 𝓞 E →+* 𝓞 E)
    (RingOfIntegers.mapRingEquiv _).surjective w.asIdeal).symm

theorem tendsto_under {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 L) => w.under (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have h0 : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal ≠ 0 :=
    fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  have e : w.under (𝓞 K) = v := hw
  show w.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← e]
  exact le_rfl

theorem normV_under {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Ideal.absNorm_eq_natCard]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 L) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

theorem val_of_norm {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) (y : (v.adicCompletion K)ˣ) (x : (w.adicCompletion L)ˣ)
    (h : ‖(y : v.adicCompletion K)‖ = ‖(x : w.adicCompletion L)‖) (f : ℕ) (hf : normV w = normV v ^ f) :
    Valued.v (y : v.adicCompletion K) = Valued.v (x : w.adicCompletion L) ^ f := by
  have hf' : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ f := by
    simpa only [normV, ← Ideal.absNorm_eq_natCard] using hf
  have hy : Valued.v (y : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 y.ne_zero
  have hx : Valued.v (x : w.adicCompletion L) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  rw [FinitePlace.norm_def, FinitePlace.norm_def] at h
  rw [WithZeroMulInt.toNNReal_neg_apply _ hy, WithZeroMulInt.toNNReal_neg_apply _ hx, NNReal.coe_inj, hf',
    Nat.cast_pow, ← zpow_natCast, ← zpow_mul] at h
  have h1 := HeightOneSpectrum.one_lt_absNorm_nnreal v
  have h2 := zpow_right_injective₀ (zero_lt_one.trans h1) h1.ne' h
  rw [← WithZero.coe_unzero hy, ← WithZero.coe_unzero hx, ← WithZero.coe_pow]
  refine congrArg _ (Multiplicative.toAdd.injective ?_)
  rw [toAdd_pow, WithZero.toAdd_unzero_eq_log, WithZero.toAdd_unzero_eq_log, nsmul_eq_mul, h2]

def normChar {K : Type} (L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (χ : HChar K) :
    HChar L :=
  ⟨χ.1.comp (GroundTheory.Global.ideleNorm K L), χ.2.1.comp GroundTheory.Global.continuous_ideleNorm, fun k =>
    (congrArg χ.1 (GroundTheory.Global.ideleNorm_diagonal (K := K) k)).trans (χ.2.2 _)⟩

theorem normChar_loc {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (χ : HChar K) (w : HeightOneSpectrum (𝓞 L)) (f : ℕ) (hf : normV w = normV (w.under (𝓞 K)) ^ f)
    (x : (w.adicCompletion L)ˣ) : ∃ y : ((w.under (𝓞 K)).adicCompletion K)ˣ,
      (normChar L χ).loc w x = χ.loc (w.under (𝓞 K)) y ∧
      Valued.v (y : (w.under (𝓞 K)).adicCompletion K) = Valued.v (x : w.adicCompletion L) ^ f := by
  have h := GroundTheory.Global.ideleNorm_finiteEmbedding (K := K) w x
  have hm := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := K)
    (GroundTheory.Global.IdeleGroup.finiteEmbedding w x)
  rw [h] at hm
  have hm' := congrArg Subtype.val hm
  rw [GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding] at hm'
  exact ⟨_, congrArg χ.1 h, val_of_norm _ w _ x hm' f hf⟩

theorem normChar_val {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (χ : HChar K) (w : HeightOneSpectrum (𝓞 L)) (f : ℕ) (hf : normV w = normV (w.under (𝓞 K)) ^ f)
    (hχ : χ.UnrAt (w.under (𝓞 K))) : (normChar L χ).UnrAt w ∧ (normChar L χ).val w = χ.val (w.under (𝓞 K)) ^ f := by
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, hv⟩ := normChar_loc χ w f hf x
    rw [hy]
    apply hχ
    unfold IsUnitAt at *
    rw [hv, hx, one_pow]
  · obtain ⟨y, hy, hv⟩ := normChar_loc χ w f hf (atFin w (unif w))
    have h1 := unif_spec w
    have h2 := unif_spec (w.under (𝓞 K))
    have hu : IsUnitAt (w.under (𝓞 K)) (y * ((atFin _ (unif (w.under (𝓞 K)))) ^ f)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀, map_pow, hv, h1, h2]
      exact mul_inv_cancel₀ (pow_ne_zero _ WithZero.exp_ne_zero)
    have h3 := hχ _ hu
    rw [map_mul, map_inv, mul_inv_eq_one, map_pow] at h3
    exact hy.trans h3

theorem infIdele_eq {K : Type} [Field K] [NumberField K] (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    ReciprocityTheory.Neutral.Bridge.HCFR.infIdele K w x = GroundTheory.Global.IdeleGroup.infiniteEmbedding w x := by
  classical
  refine Units.ext (Prod.ext (funext fun u => ?_) rfl)
  change Pi.mulSingle w (x : w.Completion) u = GroundTheory.Global.IdeleGroup.infiniteAdeleSingle w (x : w.Completion) u
  rw [GroundTheory.Global.IdeleGroup.infiniteAdeleSingle_apply]

theorem normChar_locInf {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (χ : HChar K) (u : InfinitePlace L) (hu : u.IsReal) :
    (normChar L χ).locInf u (-1) = χ.locInf (u.comap (algebraMap K L)) (-1) := by
  have hv := hu.comap (algebraMap K L)
  show χ.1 (GroundTheory.Global.ideleNorm K L (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L u (-1))) =
    χ.1 (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele K (u.comap (algebraMap K L)) (-1))
  rw [infIdele_eq, infIdele_eq, GroundTheory.Global.ideleNorm_infiniteEmbedding]
  congr 2
  apply Units.ext
  apply (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv).injective
  have := GroundTheory.Global.extensionEmbeddingOfIsReal_normUnits (K := K) u hu (-1)
  rw [this]
  simp

theorem normCharGen : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (χ : HChar K) (s : ℂˣ), (∀ v : InfinitePlace K, v.IsReal → χ.locInf v (-1) = s) → ∃ χ' : HChar L, (∀ u : InfinitePlace L, u.IsReal → χ'.locInf u (-1) = s) ∧ ∀ u : HeightOneSpectrum (𝓞 L), χ.UnrAt (u.under (𝓞 K)) → χ'.UnrAt u ∧ ∀ f : ℕ, normV u = normV (u.under (𝓞 K)) ^ f → χ'.val u = χ.val (u.under (𝓞 K)) ^ f := by
  intro K L _ _ _ _ _ χ s hs
  refine ⟨normChar L χ, fun u hu => (normChar_locInf χ u hu).trans (hs _ (hu.comap _)), fun u hu => ?_⟩
  refine ⟨(normChar_val χ u _ (normV_under u) hu).1, fun f hf => (normChar_val χ u f hf hu).2⟩

theorem one_lt_normV {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : 1 < normV v := by
  have h := HeightOneSpectrum.one_lt_absNorm_nnreal v
  simp only [normV, ← Ideal.absNorm_eq_natCard]
  exact_mod_cast h

theorem algebraMap_mem_real {E M : Type} [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] (x : maximalRealSubfield E) : algebraMap E M x ∈ maximalRealSubfield M := by
  refine (IsCMField.complexConj_eq_self_iff M _).1 ?_
  rw [conj_algebraMap, (IsCMField.complexConj_eq_self_iff E _).2 x.2]

def realHom (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] : maximalRealSubfield E →+* maximalRealSubfield M :=
  ((algebraMap E M).comp (maximalRealSubfield E).subtype).codRestrict _ algebraMap_mem_real

theorem charLift : ∀ (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M] [Algebra E M] (a : ℕ) (χ : HChar (maximalRealSubfield E)), (∀ v : InfinitePlace (maximalRealSubfield E), χ.locInf v (-1) = (-1) ^ a) → ∃ χ' : HChar (maximalRealSubfield M), (∀ u : InfinitePlace (maximalRealSubfield M), χ'.locInf u (-1) = (-1) ^ a) ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, (compNorm M χ').UnrAt w ∧ ∀ f : ℕ, normV w = normV (w.under (𝓞 E)) ^ f → (compNorm M χ').val w = (compNorm E χ).val (w.under (𝓞 E)) ^ f := by
  intro E M _ _ _ _ _ _ _ a χ hsign
  letI : Algebra (maximalRealSubfield E) (maximalRealSubfield M) := (realHom E M).toAlgebra
  obtain ⟨χ', hs, hv⟩ := normCharGen (maximalRealSubfield E) (maximalRealSubfield M) χ ((-1) ^ a) (fun v _ => hsign v)
  refine ⟨χ', fun u => hs u (IsTotallyReal.isReal u), ?_⟩
  have hNV := UpperTheory.ideleNorm_valuation_of_local_compatibility UpperTheory.ideleNorm_local_compatibility
  have hfin : ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite,
      χ.UnrAt ((w.under (𝓞 E)).under (𝓞 (maximalRealSubfield E))) :=
    (tendsto_under (K := E) (L := M)).eventually ((tendsto_under (K := maximalRealSubfield E) (L := E)).eventually
      (Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified χ)))
  filter_upwards [hfin] with w hw
  have key : (w.under (𝓞 (maximalRealSubfield M))).under (𝓞 (maximalRealSubfield E)) =
      (w.under (𝓞 E)).under (𝓞 (maximalRealSubfield E)) := by
    apply HeightOneSpectrum.ext
    change (w.asIdeal.comap _).comap _ = (w.asIdeal.comap _).comap _
    rw [Ideal.comap_comap, Ideal.comap_comap]
    congr 1
  obtain ⟨hu1, hu2⟩ := hv (w.under (𝓞 (maximalRealSubfield M))) (by rw [key]; exact hw)
  obtain ⟨hw1, hw2⟩ := hNV M χ' w _ (normV_under w) hu1
  obtain ⟨-, hv2⟩ := hNV E χ (w.under (𝓞 E)) _ (normV_under _) hw
  refine ⟨hw1, fun f hf => ?_⟩
  rw [hw2, hu2 _ (normV_under _), hv2, key, ← pow_mul, ← pow_mul]
  congr 1
  refine Nat.pow_right_injective (one_lt_normV ((w.under (𝓞 E)).under (𝓞 (maximalRealSubfield E)))) ?_
  simp only
  rw [pow_mul, pow_mul, ← key, ← normV_under, ← normV_under, key, ← normV_under, ← hf]

theorem main : AutomorphicFormsFiniteGL → JacquetShalikaRigidity → GelfandKazhdanDual → ∀ (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M] [Algebra E M] (l a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)) (P : CuspSub M a), IsLift π P → InScope .all l π χ → (∃ χ' : HChar (maximalRealSubfield M), InScope .all l P χ') ∧ ∀ wt : ℤ, IsWeight π wt → IsWeight P wt := by
  intro hF hJ hG E M _ _ _ _ _ _ _ l a ha π χ P hL hS
  obtain ⟨hreg, hpol, -⟩ := hS
  refine ⟨?_, fun wt hw τ => ?_⟩
  · obtain ⟨χ', hsign, hev⟩ := charLift E M a χ hpol.sign
    refine ⟨χ', (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, ⟨hsign, ?_⟩, trivial⟩
    · rw [hL.inf τ]
      exact (GlobalTheory.CuspRep.CG.isRegAlg_iff _).1 hreg _
    refine UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse hJ hG M a ha P (compNorm M χ') ?_
    have hsd := _root_.GlobalTheory.PolarizedSat.hasSat_conjPlace hF E a π χ hpol
    have hun := GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hF E a π
    filter_upwards [hev, (tendsto_under (K := E) (L := M)).eventually (hsd.and hun)] with w ⟨hu, hval⟩ ⟨hs, B, hB⟩
    have e1 := cPl_under (E := E) w
    have e2 := normV_cPl w
    have e3 := normV_cPl (w.under (𝓞 E))
    have hf := normV_under (K := E) w
    set f := w.asIdeal.inertiaDeg (𝓞 E)
    have hB0 : (CG.mk π).HasSat (w.under (𝓞 E)) B := (CG.hasSat_mk _ _ _).2 hB
    have h1 := hL.sat w f B hf hB0
    have h2 := hL.sat (UpperTheory.V.Af.Bc.cPl w) f _ (by rw [e1, e2, e3]; exact hf) (e1 ▸ hs B hB0)
    refine ⟨hu, _, _, h1, h2, ?_⟩
    rw [hval f hf]
    simp only [Multiset.map_map, Function.comp_def, mul_pow, inv_pow, mul_inv, inv_inv]
  · rw [hL.inf, hL.inf]
    have e : (τ.comp (IsCMField.complexConj M).toRingEquiv.toRingHom).comp (algebraMap E M) =
        (τ.comp (algebraMap E M)).comp (IsCMField.complexConj E).toRingEquiv.toRingHom :=
      RingHom.ext fun x => congrArg τ (conj_algebraMap x)
    rw [e]
    exact hw _

end GlobalTheory.LiftPolar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanks
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem fills_Pj_m_add_one {p : ℕ} {G : GAtP p} (Fl : Fills G) (j : ℕ) :
    (Fl.Pj j).m + 1 = Formalism.MainNotions.FormalGroupSystem.NN G.P.m Fl.t j := by
  cases j with
  | zero => simp [Fills.Pj, Formalism.MainNotions.FormalGroupSystem.NN]
  | succ j => simp only [Fills.Pj, Places.withWt, Formalism.MainNotions.FormalGroupSystem.NN]; ring

theorem sysS_ranks : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => (sysS H X std).mm = D.R.m ∧ (sysS H X std).t = D.R.t ∧ (∀ j, ((sysS H X std).Pj j).m + 1 = D.R.N j) ∧ ∀ j, RankTie (sysS H X std) D j) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S
  have hk : (D.gat u w hg).P.m + 1 = D.R.N 0 := (lev0At J.Gd u w hg).A.rk
  have ht : (Gl.Fl u w hg).t = D.R.t := X.fl_t
  have hN : ∀ j, D.R.N j = Formalism.MainNotions.FormalGroupSystem.NN (D.gat u w hg).P.m (Gl.Fl u w hg).t j := by
    intro j
    simp only [Formalism.MainNotions.FormalGroupSystem.NN, ht]
    simp only [Formalism.BasicNotions.Ranks.N] at hk ⊢
    omega
  refine ⟨X.fl_m, X.fl_t, fun j => ?_, fun j => ⟨hN j, hN (j + 1)⟩⟩
  exact (fills_Pj_m_add_one (Gl.Fl u w hg) j).trans (hN j).symm

end GlobalTheory.TwV.DelB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SolvableAscentInduction
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.SolvUp

theorem exists_normal_prime_index (Γ : Type) [Group Γ] [Finite Γ] [Nontrivial Γ] [Group.IsSolvable Γ] :
    ∃ H : Subgroup Γ, H.Normal ∧ H.index.Prime := by
  obtain ⟨H, hH, hle⟩ := (eq_top_or_exists_le_coatom (commutator Γ)).resolve_left
    (Group.IsSolvable.commutator_lt_top_of_nontrivial Γ).ne
  have hn : H.Normal := ⟨fun n hn g => by
    have h1 : g * n * g⁻¹ * n⁻¹ ∈ H :=
      hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    simpa using H.mul_mem h1 hn⟩
  refine ⟨H, hn, ?_⟩
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (n := Nat.card (Γ ⧸ H)) (mt Subgroup.index_eq_one.1 hH.1)
  haveI := Fact.mk hp
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hd
  have h1 : (Subgroup.zpowers g).comap (QuotientGroup.mk' H) = ⊤ := by
    refine hH.2 _ (lt_of_le_of_ne (fun x hx => ?_) fun e => ?_)
    · rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
      exact one_mem _
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H g
      have hx : x ∈ H := e ▸ Subgroup.mem_zpowers _
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx, orderOf_one] at hg
      exact hp.one_lt.ne hg
  have h2 : Subgroup.zpowers g = ⊤ :=
    Subgroup.comap_injective (QuotientGroup.mk'_surjective H) (h1.trans (Subgroup.comap_top _).symm)
  rw [Subgroup.index, ← Subgroup.card_top, ← h2, Nat.card_zpowers, hg]
  exact hp

theorem isCMField_of_ringEquiv {A B : Type} [Field A] [NumberField A] [Field B] [NumberField B] [IsCMField A]
    (e : A ≃+* B) : IsCMField B := by
  letI : Algebra A B := e.toRingHom.toAlgebra
  haveI : IsTotallyComplex B := isTotallyComplex_of_algebra A B
  letI : Algebra (maximalRealSubfield A) B :=
    ((e : A →+* B).comp (algebraMap (maximalRealSubfield A) A)).toAlgebra
  let f : A ≃ₐ[maximalRealSubfield A] B := { e with commutes' := fun _ => rfl }
  haveI : Module.Free (maximalRealSubfield A) B := Module.Free.of_equiv f.toLinearEquiv
  haveI : Algebra.IsQuadraticExtension (maximalRealSubfield A) B :=
    ⟨by rw [← f.toLinearEquiv.finrank_eq]; exact Algebra.IsQuadraticExtension.finrank_eq_two _ _⟩
  exact IsCMField.ofCMExtension (maximalRealSubfield A) B

end GlobalTheory.SolvUp

namespace GlobalTheory.SolvUp

theorem isCMField_intermediate (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [Algebra K M]
    [IsScalarTower K M Ω] (L : IntermediateField K M) : IsCMField L := by
  let f := IsScalarTower.toAlgHom K M Ω
  haveI : NumberField f.fieldRange := NumberField.of_ringEquiv M _ (AlgEquiv.ofInjectiveField f).toRingEquiv
  haveI : NumberField (L.map f) := NumberField.of_ringEquiv L _ (IntermediateField.equivMap L f).toRingEquiv
  haveI : IsCMField f.fieldRange := isCMField_of_ringEquiv (AlgEquiv.ofInjectiveField f).toRingEquiv
  have hle : L.map f ≤ f.fieldRange := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := (IntermediateField.mem_map L).1 hy
    exact AlgHom.mem_fieldRange.2 ⟨x, rfl⟩
  haveI : IsCMField (L.map f) := (_root_.GlobalTheory.CMSub.isCMField_sup_le_adjoin Ω K).2.1 f.fieldRange (L.map f) hle inferInstance
  exact isCMField_of_ringEquiv (IntermediateField.equivMap L f).symm.toRingEquiv

end GlobalTheory.SolvUp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepChartsPlacesFirstFactorEqStepZero
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc


set_option maxHeartbeats 4000000 in
theorem chart_places_firstFactor_eq_zero :
    Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
      ∀ j (hj : j + 1 ≤ D.R.m) (β : (I.at' j hj).st.Ch) v, ((I.at' j hj).st.loc β).pl v = (A0 J).pl v ∧
        ∀ x, phiA ((I.at' j hj).st.loc β) v x = phiA (A0 J) v x) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _hD _hS j hj β v
  refine ⟨J.pl j hj β v, ?_⟩
  have h := firstFactor_agree D.host.F D.host.E _ _ (((I.at' j hj).st.loc β).pl v).1 ((A0 J).pl v).1
    (((I.at' j hj).st.loc β).eQ v) ((A0 J).eQ v) (((I.at' j hj).st.loc β).ph v) ((A0 J).ph v)
    (fun c => by
      show ((((I.at' j hj).st.loc β).spl v) ((1 : D.host.E) ⊗ₜ[D.host.F] c)).1 = c
      rw [J.alg j hj β v c])
    (fun c => by
      show (((A0 J).spl v) ((1 : D.host.E) ⊗ₜ[D.host.F] c)).1 = c
      rw [J.alg0 v c])
    ((H.core j hj β).int v) (J.one.int v)
    (fun a => by
      have h1 := RingHom.congr_fun (J.iw j hj β v) a
      exact h1)
  exact h.2

end GlobalTheory.TwV.Xc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroKernelLatticeEqPointKernelLattice
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

theorem GlobalTheory.kerN_zero_eq_latK_pt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (La : (sysS H X std).Lt 0), HEq ((J.fd std).kerN 0 La) (latK D.sp (gramN D 0 (Nat.zero_le _)) J.a (J.pt std 0 (Nat.zero_le _) La).1 ((J.St 0 (Nat.zero_le _)).K (J.chart std 0 (Nat.zero_le _) La)).lev.Lb) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J La
  obtain ⟨⟨hr, hx⟩, -⟩ := _root_.GlobalTheory.TwV.Joint.isPt_pt_zero t std J La
  have hre := GlobalTheory.reindex_rename_point_det_latK D.sp (lev0At J.Gd u w hg).A.rk.symm (gramN D 0 (Nat.zero_le _)) J.a
    (Classical.epsilon fun x => (lev0At J.Gd u w hg).A.IsPt La.1 (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om 0 La.2) x ∧
        x ∈ Formalism.UG.UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (lev0At J.Gd u w hg).Lb
  have hpt : (J.pt std 0 (Nat.zero_le _) La).1 = (Classical.epsilon fun x => (lev0At J.Gd u w hg).A.IsPt La.1 (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om 0 La.2) x ∧
        x ∈ Formalism.UG.UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    rw [hx]
    exact hre.1
  have hLb : ((J.St 0 (Nat.zero_le _)).K (J.chart std 0 (Nat.zero_le _) La)).lev.Lb = (lev0At J.Gd u w hg).Lb := (J.lev0 _).1
  rw [hpt, hLb]
  exact hre.2.2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroPointMemDoubleCosetClassRep
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

theorem GlobalTheory.TwV.Joint.pt_zero_eq_rat_mul_rep_mul : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (La : (sysS H X std).Lt 0), ((sysS H X std).Pj 0).IsLatTup La.2 → ∃ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)), ∃ κ : ((J.St 0 (Nat.zero_le _)).K (J.chart std 0 (Nat.zero_le _) La)).lev.U, (J.pt std 0 (Nat.zero_le _) La).1 = ratA D.host.F γ * ((J.St 0 (Nat.zero_le _)).y (clsAt X H 0 La.1 La.2)).1 * κ.1 := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J La hLa
  obtain ⟨-, hA⟩ := _root_.GlobalTheory.TwV.Joint.isPt_pt_zero t std J La
  have hb := _root_.GlobalTheory.TwV.Joint.basesAt_span t std J 0 La hLa
  obtain ⟨hγ, κ, hκ⟩ := pt00 J.one La.1 La.2 _ hb _ hA
  have hc : clsAt X H 0 La.1 La.2 = J.e0 (levelZeroClass J.one La.1 La.2) := J.cls0 La.1 La.2 hLa

  obtain ⟨κ', hκ'⟩ := (J.y0 (levelZeroClass J.one La.1 La.2)).imp fun _ h => h.1
  have hU := (J.lev0 (J.chart std 0 (Nat.zero_le _) La)).2.2.1
  have hm : κ'.1⁻¹ * κ.1 ∈ (J.Gd.forms u).cls0.lev.U := Subgroup.mul_mem _ (Subgroup.inv_mem _ κ'.2) κ.2
  refine ⟨rationalElementZero J.one La.1 La.2, hγ, ⟨κ'.1⁻¹ * κ.1, by rw [hU]; exact hm⟩, ?_⟩
  rw [hc, hκ', hκ]
  show _ = _ * _ * (κ'.1⁻¹ * κ.1)
  simp only [mul_assoc, mul_inv_cancel_left]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnExistsChainChartsKernelDataFormsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumn_exists_chainCharts_kernelData_forms : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (C : ColsTiedSym (I.rec7 l Z)) (full : ColsFullS C) (g : Formalism.L2.G.GroupCompatibilityAll (I.rec7 l Z) hT ex.cmp), I.IsTw → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → ex.errX.piT = X.piT → I.StdKer l Z t → GlobalTheory.Pdv.StdRd I l Z t → (∀ (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i), (t.rd u a).pin i c ↔ (i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1)) → I.StdC l Z C → I.StdDt l Z full.1.base.dt → g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → (∀ z : (I.rec7 l Z).Dt, ∃ r : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL r = (((I.rec7 l Z).chiD z : ℂˣ) : ℂ)) → ∀ (u : B.Word) (a : I.ι), Nonempty (GlobalTheory.Port.JIn t u a) := by
  first | exact @GlobalTheory.Port.jIn_nonempty_true | exact GlobalTheory.Port.jIn_nonempty_true | (intros; apply GlobalTheory.Port.jIn_nonempty_true <;> assumption)
end

