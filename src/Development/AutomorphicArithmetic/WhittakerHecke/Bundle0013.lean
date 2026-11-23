module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import GroundTheory.GlobalFields.TateThesis.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0003
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
public import GroundTheory.GlobalFields.IdeleGroups.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Bundle0002
public import GroundTheory.GlobalFields.NormResidueSymbol.Bundle0002
public import GroundTheory.AutomorphicForms.Bundle0019
public import GroundTheory.AutomorphicForms.GL2.GJGlobalLattice

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.NormAdmissibleBaseChangeSiegelSetLe
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

namespace UpperTheory.EmbeddingGeneralLinear

variable {E : Type} [Field E] [NumberField E]

private theorem ab_emb (D : Dat ℚ E) (a : (A ℚ)ˣ) :
    ab (ideleEmbedding ℚ E a : (A E)ˣ) = ab a ^ 2 := by
  have hfr : Module.finrank ℚ E = 2 := by
    rw [Module.finrank_eq_card_basis D.b, Fintype.card_fin]
  have h := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := ℚ) (L := E)
    (ideleEmbedding ℚ E a)
  rw [ideleNorm_ideleEmbedding, hfr, map_pow] at h
  simp only [ab]
  rw [← h]
  rfl

private theorem em_gl (b : A ℚ) (a : (A ℚ)ˣ) :
    em E (gl (nU b * mD a)) =
      gl (nU (AdeleBaseChange.adeleMap ℚ E b) * mD (ideleEmbedding ℚ E a : (A E)ˣ)) := by
  have hinv : (((ideleEmbedding ℚ E a : (A E)ˣ)⁻¹ : (A E)ˣ) : A E) =
      AdeleBaseChange.adeleMap ℚ E ((a⁻¹ : (A ℚ)ˣ) : A ℚ) := by
    rw [← map_inv]; rfl
  apply Units.ext
  ext i j
  change AdeleBaseChange.adeleMap ℚ E ((nU b * mD a : G1 ℚ).1 i j) =
    (nU (AdeleBaseChange.adeleMap ℚ E b) * mD (ideleEmbedding ℚ E a : (A E)ˣ) : G1 E).1 i j
  have hL : (nU b * mD a : G1 ℚ).1 = !![1, b; 0, 1] * !![(a : A ℚ), 0; 0, ((a⁻¹ : (A ℚ)ˣ) : A ℚ)] := rfl
  have hR : (nU (AdeleBaseChange.adeleMap ℚ E b) * mD (ideleEmbedding ℚ E a : (A E)ˣ) : G1 E).1 =
      !![1, AdeleBaseChange.adeleMap ℚ E b; 0, 1] *
        !![AdeleBaseChange.adeleMap ℚ E (a : A ℚ), 0; 0, AdeleBaseChange.adeleMap ℚ E ((a⁻¹ : (A ℚ)ˣ) : A ℚ)] := by
    rw [← hinv]; rfl
  rw [hL, hR]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem continuous_em : Continuous (em E) :=
  Continuous.units_map _ (continuous_id.matrix_map AdeleBaseChange.continuous_adeleMap)

end UpperTheory.EmbeddingGeneralLinear

open UpperTheory.EmbeddingGeneralLinear in
theorem UpperTheory.norm_admissible_baseChange_siegelSet_le :
    ∀ {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ →
        ∀ (C : Set (GL (Fin 2) (A ℚ))), IsCompact C → ∀ (c : ℝ), 0 < c → ∀ r : ℕ,
        ∃ B : ℝ, ∀ (b : A ℚ) (a : (A ℚ)ˣ), ∀ k ∈ C, c ≤ ab a → ‖φ (em E (gl (nU b * mD a) * k))‖ ≤ B * (ab a)⁻¹ ^ r := by
  intro E _ _ D ω φ hφ C hC c hc r
  obtain ⟨B, hB⟩ := hφ.decay (em E '' C) (hC.image continuous_em) (c ^ 2) (by positivity) r
  refine ⟨|B| * c⁻¹ ^ r, fun b a k hk hca => ?_⟩
  have ha : 0 < ab a := hc.trans_le hca
  have h1 := hB (AdeleBaseChange.adeleMap ℚ E b) (ideleEmbedding ℚ E a : (A E)ˣ) (em E k) ⟨k, hk, rfl⟩
    (by rw [ab_emb D]; gcongr)
  rw [ab_emb D] at h1
  rw [map_mul, em_gl]
  refine h1.trans ?_
  have h2 : ((ab a ^ 2)⁻¹) ^ r = (ab a)⁻¹ ^ r * (ab a)⁻¹ ^ r := by
    rw [← mul_pow, sq, mul_inv]
  have h3 : (ab a)⁻¹ ^ r ≤ c⁻¹ ^ r := by gcongr
  have h4 : 0 ≤ (ab a)⁻¹ ^ r := by positivity
  rw [h2]
  calc B * ((ab a)⁻¹ ^ r * (ab a)⁻¹ ^ r) ≤ |B| * ((ab a)⁻¹ ^ r * (ab a)⁻¹ ^ r) := by
        gcongr; exact le_abs_self B
    _ ≤ |B| * (c⁻¹ ^ r * (ab a)⁻¹ ^ r) := by gcongr
    _ = |B| * c⁻¹ ^ r * (ab a)⁻¹ ^ r := by ring
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.NormIntegralUnitaryHeckeCharFundDomainLe
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.norm_integral_unitaryHeckeChar_fundDomain_le :
    ∀ (M : Meas ℚ) (U : UMeas) (χ : HChar ℚ) (f : IdeleGroup ℚ → G1 ℚ → ℂ) (B : ℝ), (∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1) → Measurable (Function.uncurry f) →
        (∀ u ∈ UU, ∀ g, ‖f u g‖ ≤ B) →
        (∀ u ∈ UU, IntegrableOn (f u) M.D M.μ) ∧ Integrable (fun u => ((χ.1 u : ℂˣ) : ℂ) * ∫ g in M.D, f u g ∂M.μ) U.υ ∧
          ‖∫ u, ((χ.1 u : ℂˣ) : ℂ) * ∫ g in M.D, f u g ∂M.μ ∂U.υ‖ ≤ B * M.μ.real M.D := by
  intro M U χ f B hχ hf hB
  haveI := U.prob
  have hD : M.μ M.D < ⊤ := UpperTheory.ConvolutionTheory.R2.M.volD ℚ M
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using hD⟩
  have hfu : ∀ u, Measurable (f u) := fun u => hf.comp measurable_prodMk_left
  have hae : ∀ᵐ u ∂U.υ, u ∈ (UU : Set (A ℚ)ˣ) := mem_ae_iff.mpr U.supp
  have hI : StronglyMeasurable (fun u => ∫ g in M.D, f u g ∂M.μ) :=
    (hf.stronglyMeasurable).integral_prod_right
  have hχm : Measurable (fun u : IdeleGroup ℚ => ((χ.1 u : ℂˣ) : ℂ)) :=
    (Units.continuous_val.comp χ.2.1).measurable
  have hbd : ∀ᵐ u ∂U.υ, ‖((χ.1 u : ℂˣ) : ℂ) * ∫ g in M.D, f u g ∂M.μ‖ ≤ B * M.μ.real M.D := by
    filter_upwards [hae] with u hu
    rw [norm_mul, hχ, one_mul]
    exact norm_setIntegral_le_of_norm_le_const hD (fun g _ => hB u hu g)
  refine ⟨fun u hu => Integrable.of_bound (hfu u).aestronglyMeasurable B (Eventually.of_forall (hB u hu)), ?_, ?_⟩
  · exact Integrable.of_bound (hχm.aestronglyMeasurable.mul hI.aestronglyMeasurable) _ hbd
  · simpa using norm_integral_le_of_norm_le_const hbd
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.RatIdeleEqDiagonalMulUnitOfAbsEqOne
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

private lemma eq_one_of_mul {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ}
    (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  have := mul_le_mul' (le_refl a) hb
  rwa [h, mul_one] at this

private lemma ab_pos_eq {p : IdeleGroup ℚ} (hp : p ∈ RationalIdeles.positiveSubgroup) :
    ab p = (RationalIdeles.realPart p : ℝ) := by
  obtain ⟨h1, h2⟩ := RationalIdeles.mem_positiveSubgroup.1 hp
  have hw := RationalIdeles.isReal_infinitePlace (default : InfinitePlace ℚ)
  have hmult : (default : InfinitePlace ℚ).mult = 1 := by
    simp [InfinitePlace.mult, hw]
  have hn : ‖(p : AdeleRing (𝓞 ℚ) ℚ).1 default‖ = (RationalIdeles.realPart p : ℝ) := by
    rw [← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _), ← RationalIdeles.realEquiv_apply, ← RationalIdeles.coe_realPart, Real.norm_eq_abs, abs_of_pos h2]
  unfold ab
  rw [IdeleGroup.ideleModule_apply, IdeleGroup.finiteModule_eq_one_of_mem h1, mul_one, IdeleGroup.infiniteModule,
    Fintype.prod_subsingleton _ (default : InfinitePlace ℚ), hmult, pow_one, hn]

theorem UpperTheory.rat_idele_eq_diagonal_mul_unit_of_abs_eq_one :
    ∀ a : IdeleGroup ℚ, ab a = 1 → ∃ (r : ℚˣ), ∃ u ∈ UU, a = IdeleGroup.diagonal ℚ r * u := by
  intro a ha
  obtain ⟨⟨r, p⟩, hp⟩ := RationalIdeles.mulMap_bijective.2 a
  rw [RationalIdeles.mulMap_apply] at hp
  have hp' : a = IdeleGroup.diagonal ℚ r * (p : IdeleGroup ℚ) := hp.symm
  have hab : ab (p : IdeleGroup ℚ) = 1 := by
    rw [hp', ab_mul, ab_diagonal, one_mul] at ha
    exact ha
  obtain ⟨h1, -⟩ := RationalIdeles.mem_positiveSubgroup.1 p.2
  have hre : RationalIdeles.realEquiv ((p : IdeleGroup ℚ) : AdeleRing (𝓞 ℚ) ℚ).1 = 1 := by
    rw [← RationalIdeles.coe_realPart, ← ab_pos_eq p.2, hab]
  have hone : ((p : IdeleGroup ℚ) : AdeleRing (𝓞 ℚ) ℚ).1 = 1 :=
    RationalIdeles.realEquiv.injective (hre.trans (map_one _).symm)
  refine ⟨r, p, ⟨hone, fun v => ?_⟩, hp'⟩
  obtain ⟨ha', hb'⟩ := (IdeleGroup.mem_standardOpenSubgroup ℚ).1 h1 v
  have hm := IdeleGroup.finite_mul_inv (p : IdeleGroup ℚ) v
  have hmv := congrArg Valued.v hm
  rw [map_mul, map_one] at hmv
  exact eq_one_of_mul ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 ha')
    ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 hb') hmv
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.SatakeParamMulEqCentralCharPowInertiaDeg
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ComplexOrder

private theorem sc_comm {R : Type} [CommRing R] (y : Rˣ) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) y * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) y :=
  Units.ext (Matrix.scalar_commute (y : R) (fun _ => Commute.all _ _) g.val).eq

private theorem val_of_norm {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) (y : (v.adicCompletion K)ˣ) (x : (w.adicCompletion L)ˣ)
    (h : ‖(y : v.adicCompletion K)‖ = ‖(x : w.adicCompletion L)‖) (f : ℕ) (hf : normV w = normV v ^ f) :
    Valued.v (y : v.adicCompletion K) = Valued.v (x : w.adicCompletion L) ^ f := by
  have hn : ∀ {F : Type} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F)),
      normV u = Ideal.absNorm u.asIdeal := by
    intro F _ _ u
    rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hf' : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ f := by
    simpa only [hn] using hf
  have hy : Valued.v (y : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 y.ne_zero
  have hx : Valued.v (x : w.adicCompletion L) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  rw [FinitePlace.norm_def, FinitePlace.norm_def] at h
  rw [WithZeroMulInt.toNNReal_neg_apply _ hy, WithZeroMulInt.toNNReal_neg_apply _ hx, NNReal.coe_inj, hf',
    Nat.cast_pow, ← zpow_natCast, ← _root_.zpow_mul] at h
  have h1 := HeightOneSpectrum.one_lt_absNorm_nnreal v
  have h2 := zpow_right_injective₀ (zero_lt_one.trans h1) h1.ne' h
  rw [← WithZero.coe_unzero hy, ← WithZero.coe_unzero hx, ← WithZero.coe_pow]
  refine congrArg _ (Multiplicative.toAdd.injective ?_)
  rw [toAdd_pow, nsmul_eq_mul, WithZero.toAdd_unzero_eq_log hy,
    WithZero.toAdd_unzero_eq_log hx, h2]

private theorem norm_loc {E : Type} [Field E] [NumberField E] (w : H.P E) (x : (H.Kv w)ˣ) (f : ℕ)
    (hf : normV w = normV (w.under (𝓞 ℚ)) ^ f) :
    ∃ y : (H.Kv (w.under (𝓞 ℚ)))ˣ, ideleNorm ℚ E (localIdele E w x) = localIdele ℚ (w.under (𝓞 ℚ)) y ∧
      Valued.v (y : H.Kv (w.under (𝓞 ℚ))) = Valued.v (x : H.Kv w) ^ f := by
  have h := GroundTheory.Global.ideleNorm_finiteEmbedding (K := ℚ) w x
  have hm := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := ℚ)
    (GroundTheory.Global.IdeleGroup.finiteEmbedding w x)
  rw [h] at hm
  have hm' := congrArg Subtype.val hm
  rw [GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding] at hm'
  exact ⟨_, h, val_of_norm _ w _ x hm' _ hf⟩

private theorem val_nat {K : Type} [Field K] [NumberField K] (v : H.P K) (n : ℕ) (hb : ((n : 𝓞 K)) ∉ v.asIdeal) :
    Valued.v ((n : ℕ) : H.Kv v) = 1 := by
  have h1 : v.valuation K (((n : 𝓞 K)) : K) = 1 := by
    refine le_antisymm (v.valuation_le_one _) (not_lt.1 fun h => hb ?_)
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) v _).1 h
  have h2 : Valued.v (algebraMap K (H.Kv v) (((n : 𝓞 K)) : K)) = v.valuation K (((n : 𝓞 K)) : K) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  rw [h1] at h2
  rw [← h2]
  simp

private theorem unr_of_ok {ω : HChar ℚ} {L : ℕ} (hc : ChOk ω⁻¹ L) {v : H.P ℚ} (hb : ¬ Bad L v) : ω.UnrAt v := by
  intro x hx
  have hL : Valued.v ((L : ℕ) : H.Kv v) = 1 := val_nat v L hb
  have hs : ∀ w : H.P ℚ, w ≠ v → (localIdele ℚ v x).val.2 w = 1 := fun w h => Pi.mulSingle_eq_of_ne h _
  have he : (localIdele ℚ v x).val.2 v = x := Pi.mulSingle_eq_same v _
  have hU : (localIdele ℚ v x : (A ℚ)ˣ) ∈ UU := by
    refine ⟨rfl, fun w => ?_⟩
    by_cases h : w = v
    · subst h
      exact (congrArg Valued.v he).trans hx
    · exact (congrArg Valued.v (hs w h)).trans (map_one _)
  have hD : ∀ w, Dv L w (((localIdele ℚ v x : (A ℚ)ˣ) : A ℚ) - 1) := fun w => by
    unfold Dv
    by_cases h : w = v
    · subst h
      have e : H.cp w (((localIdele ℚ w x : (A ℚ)ˣ) : A ℚ) - 1) = (x : H.Kv w) - 1 := by
        rw [map_sub, map_one]
        exact congrArg (· - 1) he
      rw [e, hL]
      have h1 := Valuation.map_sub (Valued.v (R := H.Kv w)) (x : H.Kv w) 1
      have hx' : Valued.v (x : H.Kv w) = 1 := hx
      rwa [hx', map_one, max_self] at h1
    · have e : H.cp w (((localIdele ℚ v x : (A ℚ)ˣ) : A ℚ) - 1) = 0 := by
        rw [map_sub, map_one, sub_eq_zero]
        exact hs w h
      rw [e, map_zero]
      exact zero_le'
  have h : (ω.1 (localIdele ℚ v x))⁻¹ = 1 := hc _ hU hD
  exact inv_eq_one.1 h

theorem UpperTheory.satake_param_mul_eq_central_char_pow_inertiaDeg :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (P : CuspSub E 2) (ω : HChar ℚ) (L : ℕ), CenN P ω → ChOk ω⁻¹ L →
        ∀ (w : H.P E) (α β : ℂˣ) (f : ℕ), ¬ Bad L (w.under (𝓞 ℚ)) → normV w = normV (w.under (𝓞 ℚ)) ^ f →
          (CG.mk P).HasSat w {α, β} → α * β = ω.val (w.under (𝓞 ℚ)) ^ f := by
  intro E _ _ _ P ω L hC hO w α β f hb hf hS
  have hU := unr_of_ok hO hb
  obtain ⟨p, hp⟩ := GlobalTheory.LFun.exists_isUnifV w
  have hp0 : p ≠ 0 := fun h0 => by simp [Formalism.UG.IsUnifV, h0] at hp
  have hϖ : H.IsU (Units.mk0 p hp0) := hp
  have hB := (CG.hasSat_mk P w _).1 hS
  obtain ⟨x, hx⟩ := GlobalTheory.LFun.HasSatGL.exists_vec hB
  obtain ⟨g, hg⟩ : ∃ g, x.1.1 g ≠ 0 := by
    by_contra! hn
    exact hx.1 (Subtype.ext (Subtype.ext (funext hn)))
  have hfix : ∀ g, ∀ k ∈ GlobalTheory.LFun.KGL w (n := 2), x.1.1 (g * finGL E 2 (locGL E 2 w k)) = x.1.1 g := fun g k hk =>
    congrFun (congrArg (fun y : P.V => y.1.1) (GlobalTheory.LGrp.mem_fixed.1 hx.2.1 k hk)) g
  have hEig : UpperTheory.V.Af.Smo.EigAt w {α, β} x.1.1 := by
    intro g
    refine ⟨hB.card, fun y k hk => ?_, fun ϖ hϖ j hj y => ?_⟩
    · rw [map_mul, map_mul, ← mul_assoc, hfix _ k hk]
    · have he := (hB.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk =>
        Subtype.ext (Subtype.ext (funext fun z => hfix z k hk))) hx.1).2.2.2 ϖ hϖ j hj
      let ev : P.V →+ ℂ :=
        { toFun := fun ψ => ψ.1.1 (g * finGL E 2 (locGL E 2 w y))
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      have hs := ev.map_finsum (GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm E w 2)
        (GlobalTheory.LFun.Tj_mem_hecke hϖ j) (P.locRep w) x)
      refine Eq.trans (finsum_congr fun c => ?_) (hs.symm.trans (congrArg ev he))
      rw [map_mul, map_mul, ← mul_assoc]
      rfl
  obtain ⟨R, -, -, hR⟩ := H.heckeExpl E w _ hϖ
  have hc := (hR α β _ (hEig g) 1).2
  have hc' : x.1.1 (g * Matrix.GeneralLinearGroup.scalar (Fin 2) (H.idl w (Units.mk0 p hp0))) = (α : ℂ) * β * x.1.1 g := by
    simp only [one_mul, map_one, mul_one] at hc
    rw [← (H.lcLaws E w).2.2.2.2.1]
    exact hc
  have h2 := hC x.1 x.2 (H.idl w (Units.mk0 p hp0)) g
  rw [sc_comm, hc'] at h2
  have h3 := mul_right_cancel₀ hg h2
  obtain ⟨y, hy, hv⟩ := norm_loc w (Units.mk0 p hp0) f hf
  have hu : IsUnitAt (w.under (𝓞 ℚ)) (y * (atFin (w.under (𝓞 ℚ)) (unif (w.under (𝓞 ℚ))) ^ f)⁻¹) := by
    have hun := unif_spec (w.under (𝓞 ℚ))
    have hp' : Valued.v ((Units.mk0 p hp0 : (H.Kv w)ˣ) : H.Kv w) = WithZero.exp (-1 : ℤ) := hp
    unfold IsUnitAt
    unfold IsUnifAt at hun
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀, map_pow, hv, hp', hun]
    exact mul_inv_cancel₀ (pow_ne_zero _ WithZero.exp_ne_zero)
  have h4 := hU _ hu
  rw [map_mul, map_inv, map_pow, mul_inv_eq_one] at h4
  have h5 : ω.1 (ideleNorm ℚ E (H.idl w (Units.mk0 p hp0))) = ω.val (w.under (𝓞 ℚ)) ^ f :=
    (congrArg ω.1 hy).trans h4
  rw [h5] at h3
  exact Units.ext (by simpa using h3)
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.SchwartzBruhatTranslateDecayBound
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem abs_re' (x : A ℚ) : |UpperTheory.ConvolutionTheory.RankTwoDescent.re x| = ‖x.1 Rat.infinitePlace‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (IsTotallyReal.isReal Rat.infinitePlace)).norm_map_of_map_zero (map_zero _) (x.1 Rat.infinitePlace)

private theorem re_mul' (a b : A ℚ) :
    UpperTheory.ConvolutionTheory.RankTwoDescent.re (a * b) = UpperTheory.ConvolutionTheory.RankTwoDescent.re a * UpperTheory.ConvolutionTheory.RankTwoDescent.re b := by
  simp only [UpperTheory.ConvolutionTheory.RankTwoDescent.re, map_mul, Pi.mul_apply]

private theorem re_add' (a b : A ℚ) :
    UpperTheory.ConvolutionTheory.RankTwoDescent.re (a + b) = UpperTheory.ConvolutionTheory.RankTwoDescent.re a + UpperTheory.ConvolutionTheory.RankTwoDescent.re b := by
  simp only [UpperTheory.ConvolutionTheory.RankTwoDescent.re, map_add (f := _), Pi.add_apply]

private theorem pInf_id' (u : (TR.Rinf ℚ)ˣ) : TR.pInf ℚ (TR.infId ℚ u).val = u.val := by
  change TR.pInf ℚ (1 - TR.sInf ℚ 1 + TR.sInf ℚ _) = _
  have h : ∀ x, TR.pInf ℚ (TR.sInf ℚ x) = x := fun x => (TR.infEq ℚ).symm_apply_apply x
  simp [h]

private theorem re_iy' {s : ℝ} (hs : s ≠ 0) : UpperTheory.ConvolutionTheory.RankTwoDescent.re (UpperTheory.ConvolutionTheory.RankTwoDescent.iy s : A ℚ) = s := by
  simp only [UpperTheory.ConvolutionTheory.RankTwoDescent.re, UpperTheory.ConvolutionTheory.RankTwoDescent.iy, dite_eq_right hs, pInf_id']

private theorem snd_iy' {s : ℝ} (hs : s ≠ 0) : (UpperTheory.ConvolutionTheory.RankTwoDescent.iy s : A ℚ).2 = 1 := by
  simp only [UpperTheory.ConvolutionTheory.RankTwoDescent.iy, dite_eq_right hs]
  change (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) - 0 + 0 = 1
  simp

theorem UpperTheory.schwartzBruhat_translate_decay_bound :
    ∀ (Φ : (Fin 2 → A ℚ) → ℂ), Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2) → ∀ (C : Set (GL (Fin 2) (A ℚ))), IsCompact C → ∀ N : ℕ,
        ∃ (B κ : ℝ) (L : Set (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ)), 0 ≤ B ∧ 0 < κ ∧ κ ≤ 1 ∧ IsCompact L ∧
          ∀ (t : ℝ), ∀ k ∈ C, ∀ y : Fin 2 → A ℚ,
            ‖Φ fun j => (UpperTheory.ConvolutionTheory.RankTwoDescent.iy (Real.exp t) : A ℚ) * (y ᵥ* k.val) j‖ ≤
                B * ((1 + κ * Real.exp t * (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 1)|)) ^ N)⁻¹ ∧
              (Φ (fun j => (UpperTheory.ConvolutionTheory.RankTwoDescent.iy (Real.exp t) : A ℚ) * (y ᵥ* k.val) j) ≠ 0 → (fun j => (y j).2) ∈ L) := by
  intro Φ hΦ C hC N
  obtain ⟨C0, hC0, L0, hL0, hmaj⟩ := GroundTheory.Automorphic.GJGlobal.exists_majorant_pi hΦ N
  have hinv : Continuous fun k : GL (Fin 2) (A ℚ) => (k⁻¹).val :=
    Units.continuous_val.comp continuous_inv
  have hent : ∀ i j, Continuous fun k : GL (Fin 2) (A ℚ) => (k⁻¹).val i j :=
    fun i j => hinv.matrix_elem i j
  have hnorm : ∀ i j, Continuous fun k : GL (Fin 2) (A ℚ) =>
      ‖((k⁻¹).val i j).1 Rat.infinitePlace‖ := fun i j =>
    (((continuous_apply Rat.infinitePlace).comp continuous_fst).comp (hent i j)).norm
  obtain ⟨B1, hB1⟩ := hC.exists_bound_of_continuousOn
    (f := fun k : GL (Fin 2) (A ℚ) => ∑ i, ∑ j, ‖((k⁻¹).val i j).1 Rat.infinitePlace‖)
    (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => hnorm i j).continuousOn
  have hBk0 : 0 ≤ max B1 0 := le_max_right _ _
  have hBk : ∀ k ∈ C, ∀ i j, |UpperTheory.ConvolutionTheory.RankTwoDescent.re ((k⁻¹).val i j)| ≤ max B1 0 := by
    intro k hk i j
    rw [abs_re']
    have h1 := (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hB1 k hk))
    refine le_trans ?_ (h1.trans (le_max_left _ _))
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖((k⁻¹).val i j).1 Rat.infinitePlace‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ‖((k⁻¹).val i j).1 Rat.infinitePlace‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  generalize max B1 0 = Bk at hBk0 hBk
  have hpos : 0 < 1 + 4 * Bk := by linarith
  let f : (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × GL (Fin 2) (A ℚ) → Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ :=
    fun p j => p.1 0 * ((p.2⁻¹).val 0 j).2 + p.1 1 * ((p.2⁻¹).val 1 j).2
  have hf : Continuous f := by
    refine continuous_pi fun j => ?_
    exact (((continuous_apply 0).comp continuous_fst).mul
        (continuous_snd.comp ((hent 0 j).comp continuous_snd))).add
      (((continuous_apply 1).comp continuous_fst).mul
        (continuous_snd.comp ((hent 1 j).comp continuous_snd)))
  refine ⟨C0, 1 / (1 + 4 * Bk), f '' (L0 ×ˢ C), hC0, by positivity,
    (div_le_one hpos).2 (by linarith), (hL0.prod hC).image hf, fun t k hk y => ?_⟩
  have het : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have hyz : ∀ j, y j = (y ᵥ* k.val) 0 * (k⁻¹).val 0 j + (y ᵥ* k.val) 1 * (k⁻¹).val 1 j := by
    intro j
    have h : (y ᵥ* k.val) ᵥ* (k⁻¹).val = y := by
      rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
    conv_lhs => rw [← h]
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  generalize hz : y ᵥ* k.val = z at hyz ⊢
  generalize hx : (fun j => (UpperTheory.ConvolutionTheory.RankTwoDescent.iy (Real.exp t) : A ℚ) * z j) = x
  have hxj : ∀ j, x j = (UpperTheory.ConvolutionTheory.RankTwoDescent.iy (Real.exp t) : A ℚ) * z j := fun j => by rw [← hx]
  have hxT : ∀ j, Real.exp t * |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z j)| ≤ ‖infPartPi x‖ := by
    intro j
    have e : Real.exp t * |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z j)| = |UpperTheory.ConvolutionTheory.RankTwoDescent.re (x j)| := by
      rw [hxj, re_mul', re_iy' het, abs_mul, abs_of_pos (Real.exp_pos t)]
    rw [e, abs_re']
    exact (GroundTheory.Automorphic.GJGlobal.norm_apply_le_norm_homeomorphMixedSpace _ _).trans
      (norm_le_pi_norm (infPartPi x) j)
  have hyb : ∀ j, |UpperTheory.ConvolutionTheory.RankTwoDescent.re (y j)| ≤
      Bk * (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 1)|) := by
    intro j
    rw [hyz j, re_add', re_mul', re_mul']
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, mul_add, mul_comm Bk, mul_comm Bk]
    exact add_le_add (mul_le_mul_of_nonneg_left (hBk k hk 0 j) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (hBk k hk 1 j) (abs_nonneg _))
  have hT : 0 ≤ ‖infPartPi x‖ := norm_nonneg _
  have hkey : 1 / (1 + 4 * Bk) * Real.exp t *
      (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 1)|) ≤ ‖infPartPi x‖ := by
    have hS : Real.exp t * (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 1)|) ≤
        4 * Bk * ‖infPartPi x‖ := by
      have h0 := mul_le_mul_of_nonneg_left (hyb 0) (Real.exp_pos t).le
      have h1 := mul_le_mul_of_nonneg_left (hyb 1) (Real.exp_pos t).le
      have h2 : Real.exp t * (Bk * (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 1)|)) ≤
          Bk * (‖infPartPi x‖ + ‖infPartPi x‖) := by
        rw [show Real.exp t * (Bk * (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 1)|)) =
          Bk * (Real.exp t * |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 0)| + Real.exp t * |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 1)|) by ring]
        exact mul_le_mul_of_nonneg_left (add_le_add (hxT 0) (hxT 1)) hBk0
      nlinarith
    rw [mul_assoc, one_div, inv_mul_le_iff₀ hpos]
    nlinarith
  have hm := hmaj x
  constructor
  · by_cases hmem : finPartPi x ∈ L0
    · rw [Set.indicator_of_mem hmem, mul_one] at hm
      refine hm.trans (mul_le_mul_of_nonneg_left ?_ hC0)
      have hb : 0 ≤ 1 / (1 + 4 * Bk) * Real.exp t *
          (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 1)|) := by positivity
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) N)
    · rw [Set.indicator_of_notMem hmem, mul_zero] at hm
      exact hm.trans (by positivity)
  · intro hne
    have hmem : finPartPi x ∈ L0 := by
      by_contra hmem
      rw [Set.indicator_of_notMem hmem, mul_zero] at hm
      exact hne (norm_le_zero_iff.1 hm)
    refine ⟨(finPartPi x, k), ⟨hmem, hk⟩, ?_⟩
    have hfin : ∀ j, finPartPi x j = (z j).2 := by
      intro j
      change (x j).2 = _
      rw [hxj]
      change (UpperTheory.ConvolutionTheory.RankTwoDescent.iy (Real.exp t) : A ℚ).2 * (z j).2 = _
      rw [snd_iy' het, one_mul]
    funext j
    simp only [f, hfin]
    rw [hyz j]
    rfl
end

