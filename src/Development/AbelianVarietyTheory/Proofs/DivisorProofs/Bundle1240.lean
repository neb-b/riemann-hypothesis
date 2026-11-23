module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0830
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLaplacianPolynomialKillsHarishChandraFinit
section
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic GlobalTheory.HCAlpha
open scoped ContDiff
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

noncomputable section

namespace GlobalTheory.GLPoly

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem commute_lieS' {z : Module.End ℂ (Sm E a)} (hz : ∀ X, Commute z (lie E a X)) (i j : Fin a) (x : Cinf E) :
    Commute z (lieS E a i j x) := by
  rw [lieS_apply]; exact hz _

theorem commute_casKOp' {z : Module.End ℂ (Sm E a)} (hz : ∀ X, Commute z (lie E a X)) :
    Commute z (casKOp E a) := by
  unfold casKOp
  refine Commute.sum_right _ _ _ fun τ _ => Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => ?_
  refine Commute.smul_right (Commute.add_right (Commute.pow_right ?_ 2) (Commute.pow_right ?_ 2)) _
  · exact (commute_lieS' hz _ _ _).sub_right (commute_lieS' hz _ _ _)
  · exact (commute_lieS' hz _ _ _).add_right (commute_lieS' hz _ _ _)

theorem commute_cas' {z : Module.End ℂ (Sm E a)} (hz : ∀ X, Commute z (lie E a X)) (τ : E →+* ℂ) :
    Commute z (Formalism.REAL.Cas (Eop (a := a) τ)) := by
  have hE : ∀ i j, Commute z (Eop τ i j) := fun i j =>
    Commute.smul_right ((commute_lieS' hz _ _ _).sub_right ((commute_lieS' hz _ _ _).smul_right _)) _
  unfold Formalism.REAL.Cas
  exact Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => (hE i j).mul_right (hE j i)

theorem foldr_replicate' (z : Module.End ℂ (Sm E a)) (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ) (φ : Sm E a) :
    (List.replicate N z).foldr (fun z f => z f - χ z • f) φ =
      Polynomial.aeval z ((Polynomial.X - Polynomial.C (χ z)) ^ N) φ := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.foldr_cons, ih, pow_succ', map_mul, Module.End.mul_apply]
    simp [sub_smul, Polynomial.aeval_X, Polynomial.aeval_C]


variable (E a) in
theorem exists_poly_one (W : Submodule ℂ (Kinf E a → ℂ)) (hW : FiniteDimensional ℂ W)
    (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ) :
    ∃ p : Polynomial ℂ, p ≠ 0 ∧ ∀ φ : Sm E a,
      (∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k φ).1 g) ∈ W) → GlobalTheory.HCF.CentralNilGL χ N φ →
        Polynomial.aeval (lapOp E a) p φ = 0 := by
  obtain ⟨q, hq0, hq⟩ := GlobalTheory.T.exists_poly_maximalCompactCasimir_kills_KType E a W hW
  let A : Option (E →+* ℂ) → Module.End ℂ (Sm E a) := fun o => o.elim (casKOp E a) fun τ => Formalism.REAL.Cas (Eop τ)
  let c : Option (E →+* ℂ) → ℂ := fun o => o.elim 2 fun _ => 4
  let P : Option (E →+* ℂ) → Polynomial ℂ := fun o =>
    o.elim q fun τ => (Polynomial.X - Polynomial.C (χ (Formalism.REAL.Cas (Eop (a := a) τ)))) ^ N
  have hZ : ∀ τ : E →+* ℂ, ∀ X, Commute (Formalism.REAL.Cas (Eop (a := a) τ)) (lie E a X) := fun τ X =>
    GlobalTheory.CuspRep.Zalg_mul_lie E a X _ (GlobalTheory.CasCentre.cas_Eop_mem_Zalg E a τ)
  have hc : ∀ i j, Commute (A i) (A j) := by
    rintro (_ | τ) (_ | τ')
    · exact Commute.refl _
    · exact (commute_casKOp' (hZ τ')).symm
    · exact commute_casKOp' (hZ τ)
    · exact commute_cas' (hZ τ) τ'
  have hP : ∀ i, P i ≠ 0 := by
    rintro (_ | τ)
    · exact hq0
    · exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
  obtain ⟨p, hp0, hp⟩ := GlobalTheory.CommutingPoly.exists_poly_annihilates_linear_combination A hc c P hP
  refine ⟨p, hp0, fun φ hK hN => ?_⟩
  have e : ∑ i, c i • A i = lapOp E a := by
    rw [GlobalTheory.HCAlpha.lapOp_eq_casKOp_add_cas E a, Fintype.sum_option]; rfl
  rw [← e]
  refine hp φ ?_
  rintro (_ | τ)
  · exact hq φ hK
  · have h := hN (List.replicate N (Formalism.REAL.Cas (Eop τ))) (List.length_replicate ..)
      (fun z hz => (List.eq_of_mem_replicate hz) ▸ GlobalTheory.CasCentre.cas_Eop_mem_Zalg E a τ)
    rw [foldr_replicate'] at h
    exact h

theorem exists_poly_formsGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    ∀ (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)), FiniteDimensional ℂ W →
    ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∃ p : Polynomial ℂ, p ≠ 0 ∧
      ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, Polynomial.aeval (lapOp E a) p φ = 0 := by
  intro E _ _ _ a L W hW X hX N
  classical
  choose pχ hpχ0 hpχ using fun χ => exists_poly_one E a W hW χ N
  refine ⟨∏ χ ∈ hX.toFinset, pχ χ, Finset.prod_ne_zero_iff.mpr fun χ _ => hpχ0 χ, fun φ hφ => ?_⟩
  obtain ⟨χ, hχX, hN⟩ := hφ.2.2.2
  have hmem : χ ∈ hX.toFinset := hX.mem_toFinset.mpr hχX
  rw [← Finset.mul_prod_erase _ _ hmem, mul_comm, map_mul, Module.End.mul_apply, hpχ χ φ hφ.2.2.1 hN, map_zero]

end GlobalTheory.GLPoly

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOneParameterSubgroupUnitaryOfRealPlaceLieA
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.HoweD
open GlobalTheory.RealLift.OneParam

theorem exists_line_of_upqD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : InfinitePlace F → ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∀ Y : ∀ w : InfinitePlace F, Mat (R w) (S w), (∀ w, Y w ∈ upq (R w) (S w)) → ∃ γ ∈ RLines (σ := σ) J, IsGenD τ C γ Y := by
  intro F E _ _ _ _ _ σ β _ _ R S τ J b C hCM hC Y hY
  have := hCM.1
  obtain ⟨ξ, hξ⟩ := exists_moved hCM
  have hξ' : ∀ w, ((τ w).1 ξ).im ≠ 0 := fun w => im_ne_zero hCM hξ (τ w).1
  choose C' hC' using fun w => (hC w).2
  have hL : ∀ w, C' w * C w = 1 := fun w => frame_inv (hC w).1 (hC' w)
  set G : InfinitePlace F → ℝ → Matrix β β ℂ := fun w t => C w * NormedSpace.exp (t • Y w) * C' w with hG
  set f : ℝ → Matrix β β (AE F E) := fun t => 1 + liftM τ ξ (fun w => G w t - 1) with hf
  have hfπ : ∀ t w, (f t).map (piInf (τ w)) = G w t := fun t w => by
    rw [hf, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), OneParam.liftM_map τ hξ', add_sub_cancel]
  have hfat : ∀ t, At (evI F) (f t - 1) := fun t => by
    rw [hf, add_sub_cancel_left]
    exact at_liftM τ ξ _
  have hfadd : ∀ s t, f (s + t) = f s * f t := fun s t => by
    refine (eq_of_at hCM τ ?_ fun w => ?_).symm
    · have e : f s * f t - f (s + t) = (f s - 1) * f t + (f t - 1) - (f (s + t) - 1) := by noncomm_ring
      rw [e]
      exact at_sub (at_add (at_mul_right (hfat s) _) (hfat t)) (hfat _)
    · rw [Matrix.map_mul, hfπ, hfπ, hfπ]
      exact (conj_add (hL w) (Y w) s t).symm
  have hf0 : f 0 = 1 := by
    refine eq_of_at hCM τ (hfat 0) fun w => ?_
    rw [hfπ, Matrix.map_one _ (map_zero _) (map_one _)]
    exact conj_zero (hC' w) (Y w)
  have hfU : ∀ t, (f t)ᵀ * J * (f t).map (cA σ) = J := fun t => by
    refine eq_of_at hCM τ ?_ fun w => ?_
    · have e : (f t)ᵀ * J * (f t).map (cA σ) - J =
          (f t - 1)ᵀ * J * (f t).map (cA σ) + J * (f t - 1).map (cA σ) := by
        have e1 : (f t - 1).map (cA σ) = (f t).map (cA σ) - 1 := by
          rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
        rw [e1, Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul,
          Matrix.mul_sub, Matrix.mul_one]
        abel
      rw [e]
      exact at_add (at_mul_right (at_mul_right (at_transpose (hfat t)) _) _)
        (at_mul_left (at_map_cA σ (hfat t)) _)
    · have hc : ((f t).map (cA σ)).map (piInf (τ w)) = (G w t).map star := by
        rw [← hfπ t w, Matrix.map_map, Matrix.map_map]
        congr 1
        funext z
        exact piInf_cA hCM (τ w) z
      rw [Matrix.map_mul, Matrix.map_mul, hc, Matrix.transpose_map, hfπ]
      by_cases hb : b = 0
      · haveI := isEmpty_of_zero (hb ▸ (hC w).1) (hC' w)
        ext i
        exact isEmptyElim i
      · have h1 := conj_unitary (hC w).1 (hC' w) (hY w) t
        rw [Matrix.mul_smul, Matrix.smul_mul] at h1
        exact smul_right_injective _ hb h1
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  have hfc : Continuous f :=
    continuous_const.add ((continuous_liftM τ ξ).comp (continuous_pi fun w =>
      (((continuous_const.matrix_mul (continuous_exp_smul (Y w))).matrix_mul continuous_const).sub continuous_const)))
  let g : ℝ → UG (cA σ) J := fun t => ⟨⟨f t, f (-t), by rw [← hfadd, add_neg_cancel, hf0],
    by rw [← hfadd, neg_add_cancel, hf0]⟩, hfU t⟩
  let γ : Multiplicative ℝ →* UG (cA σ) J :=
    { toFun := fun t => g (Multiplicative.toAdd t)
      map_one' := Subtype.ext (Units.ext hf0)
      map_mul' := fun x y => Subtype.ext (Units.ext (hfadd _ _)) }
  refine ⟨γ, ⟨?_, fun t => hfat _⟩, fun t w => ?_⟩
  · have hu : Continuous fun t : Multiplicative ℝ => ((g (Multiplicative.toAdd t)).1 : GL β (AE F E)) :=
      Units.continuous_iff.2 ⟨hfc.comp continuous_toAdd, (hfc.comp continuous_neg).comp continuous_toAdd⟩
    exact hu.subtype_mk _
  · change (f t).map (piInf (τ w)) * C w = C w * NormedSpace.exp (t • Y w)
    rw [hfπ, hG]
    simp only [Matrix.mul_assoc]
    rw [hL, Matrix.mul_one]

end GlobalTheory.HoweD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatioMemValuationSubringAtGenericPoint
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.Adelic.LinSys

theorem exists_ratio_mem_of_point {F K : Type} [Field F] [Field K] (S : LinSys F) (hS : S.IsVariety) (r e : ℕ)
    (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec) (hcov : ∀ y : S.Y, ∃ i, y ∈ nonzeroLocus (S.comb (u i)))
    (x : Sp K ⟶ S.Y) (V : ValuationSubring K) (hV : ∀ c, S.baseHom x c ∈ V) :
    ∃ i, S.val x (S.comb (u i)) ≠ 0 ∧ S.powVal x th / S.val x (S.comb (u i)) ^ e ∈ V := by
  have hpr : IsProper S.str := GlobalTheory.CommonModel.isProper_of_isProjOver hS.proj
  let φ : F →+* V := (S.baseHom x).codRestrict V hV
  have hsq : x ≫ S.str = specAlgebraMap V K ≫ spMap φ := by
    rw [S.comp_str x, ← Spec.map_comp]
    rfl
  obtain ⟨l, hl, -⟩ := exists_valuativeExtension S.str (spMap φ) x hsq
  have hx : spMap (algebraMap V K) ≫ l = x := hl
  obtain ⟨i, hi⟩ := hcov (l (IsLocalRing.closedPoint V))
  have hyc := S.mem_chartAt (l (IsLocalRing.closedPoint V))
  set c := S.chartAt (l (IsLocalRing.closedPoint V))
  have hU : ⊤ ≤ l ⁻¹ᵁ S.L.U c := (GlobalTheory.ZH.CrdCalc.top_le_iff l _).2 hyc
  have hB : ⊤ ≤ l ⁻¹ᵁ S.Y.basicOpen ((S.comb (u i)).f c) :=
    (GlobalTheory.ZH.CrdCalc.top_le_iff l _).2 ((mem_nonzeroLocus_iff_basicOpen _ hyc).1 hi)
  obtain ⟨w, hw⟩ := (GlobalTheory.ZH.CrdCalc.isUnit_valR_iff l _ hU _).2 hB
  obtain ⟨hU', hval⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (algebraMap V K) l _ hU
  rw [hx] at hU' hval
  obtain ⟨c₀, hc₀, h₁, h₂⟩ := S.exists_frame_change x c ((le_iff_ptOf_mem x _).1 hU')
  have ha := (h₁ (S.comb (u i))).symm.trans (hval _)
  have ht := (h₂ e th).symm.trans (hval _)
  rw [← hw] at ha
  have hw₀ : algebraMap V K (w : V) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 w.ne_zero
  have hv : S.val x (S.comb (u i)) ≠ 0 := fun h => hw₀ (by rw [← ha, h, mul_zero])
  refine ⟨i, hv, ?_⟩
  have key : S.powVal x th / S.val x (S.comb (u i)) ^ e =
      algebraMap V K (valR l _ (Twist.zfun th c) * ((w⁻¹ : Vˣ) : V) ^ e) := by
    have hinv : algebraMap V K ((w⁻¹ : Vˣ) : V) = (algebraMap V K (w : V))⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
    rw [map_mul, map_pow, ← ht, hinv, ← ha, zpow_natCast]
    rw [inv_pow, mul_pow]
    field_simp
  rw [key]
  exact (valR l _ (Twist.zfun th c) * ((w⁻¹ : Vˣ) : V) ^ e).2

theorem exists_ratio_mem_valuationSubring : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → ∀ (r e : ℕ) (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec), (∀ y : S.Y, ∃ i, y ∈ nonzeroLocus (S.comb (u i))) → ∀ η : S.Y, IsGenericPoint η Set.univ → ∀ V : ValuationSubring (S.Y.residueField η), (∀ c, S.baseHom (resPt η) c ∈ V) → ∃ i, S.val (resPt η) (S.comb (u i)) ≠ 0 ∧ S.powVal (resPt η) th / S.val (resPt η) (S.comb (u i)) ^ e ∈ V :=
  fun _ _ S hS r e u th hcov η _ V hV => exists_ratio_mem_of_point S hS r e u th hcov (resPt η) V hV

end GlobalTheory.Adelic.LinSys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalSubBoundedInfiniteSmallFinite
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.AdeleApprox

theorem exists_compact_integral (E : Type) [Field E] [NumberField E] :
    ∃ C : Set (InfiniteAdeleRing E), IsCompact C ∧
      ∀ x : Ad E, ∃ a : E, (x - algebraMap E (Ad E) a).1 ∈ C ∧
        ∀ v, (x - algebraMap E (Ad E) a).2 v ∈ v.adicCompletionIntegers E := by
  obtain ⟨C, hC, hCy⟩ := Formalism.IndefR.Eqv.G5.adl_inf_cocompact (F := E)
  refine ⟨C, hC, fun x => ?_⟩
  obtain ⟨u, hu⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_sub_mem_intAd x.2
  obtain ⟨r, hr⟩ := hCy (x.1 - algebraMap E _ u)
  refine ⟨u + r, ?_, ?_⟩
  · show x.1 - algebraMap E (InfiniteAdeleRing E) (u + r) ∈ C
    rw [map_add (f := _), ← sub_sub]
    exact hr
  · have : x.2 - algebraMap E (Af E) (u + r) =
        (x.2 - algebraMap E _ u) - algebraMap E _ (r : E) := by rw [map_add (f := _), sub_sub]
    show ∀ v, (x.2 - algebraMap E (Af E) (u + r)) v ∈ _
    rw [this]
    exact sub_mem hu (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.algebraMap_mem_intAd r)

theorem exists_rat_sub_bounded_small :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (U : Set (Af E)), U ∈ nhds (0 : Af E) →
      ∃ R : ℝ, 0 ≤ R ∧ ∀ x : Ad E, ∃ ξ : E, ‖pInf E (x - algebraMap E (Ad E) ξ)‖ ≤ R ∧
        pFin E (x - algebraMap E (Ad E) ξ) ∈ U := by
  intro E _ _ _ U hU
  obtain ⟨C, hC, hcov⟩ := exists_compact_integral E
  obtain ⟨N, hN, hNU⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele E U hU
  have hc : Continuous (infEq E).symm := by
    refine continuous_pi fun w => ?_
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (IsTotallyComplex.isComplex w)).continuous.comp (continuous_apply w)
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (hC.image hc).isBounded
  refine ⟨N * max B 0, by positivity, fun x => ?_⟩
  have hN' : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  obtain ⟨a, h1, h2⟩ := hcov (algebraMap E (Ad E) (N : E)⁻¹ * x)
  set k := algebraMap E (Ad E) (N : E)⁻¹ * x - algebraMap E (Ad E) a with hk
  have e : x - algebraMap E (Ad E) ((N : E) * a) = N • k := by
    rw [hk, nsmul_eq_mul, ← map_natCast (algebraMap E (Ad E)) N, mul_sub, ← mul_assoc, ← map_mul,
      mul_inv_cancel₀ hN', map_one, one_mul, map_mul]
  refine ⟨(N : E) * a, ?_, ?_⟩
  · rw [e, map_nsmul]
    have hb : ‖pInf E k‖ ≤ max B 0 := (hB _ ⟨k.1, h1, rfl⟩).trans (le_max_left _ _)
    exact (norm_nsmul_le).trans (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))
  · rw [e, map_nsmul]
    exact hNU _ h2

end GlobalTheory.AdeleApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealDiagonalInfGLEqPositiveIdeleDiagonal
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic
  GroundTheory.Automorphic.Reduction

namespace GlobalTheory.SiegelTorusInf

theorem exists_diag_infGL (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (r : Fin a → ℝ)
    (hr : ∀ i, 0 < r i) : ∃ d : GL (Fin a) (Cinf E), d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) ∧
      diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) = infGL E a d := by
  have h0 : ∀ i, (r i : ℂ) ≠ 0 := fun i => Complex.ofReal_ne_zero.2 (hr i).ne'
  refine ⟨⟨Matrix.diagonal (fun i => fun _ => (r i : ℂ)), Matrix.diagonal (fun i => fun _ => (r i : ℂ)⁻¹), ?_, ?_⟩,
    rfl, ?_⟩
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i w
    exact mul_inv_cancel₀ (h0 i)
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i w
    exact inv_mul_cancel₀ (h0 i)
  · have key : ∀ i, ((posIdele (K := E) (r i) (hr i) : IdeleGroup E) : Ad E) =
        1 - sInf E 1 + sInf E (fun _ => (r i : ℂ)) := fun i => by
      rw [GlobalTheory.CuspBoundSiegel.posIdele_congr (hr i) (Real.exp_pos _) (Real.exp_log (hr i)).symm,
        GlobalTheory.CuspBoundSiegel.posIdele_exp]
      change 1 - sInf E 1 + sInf E _ = _
      congr 2
      funext w
      change Complex.exp (Real.log (r i) : ℂ) = (r i : ℂ)
      rw [← Complex.ofReal_exp, Real.exp_log (hr i)]
    refine Units.ext ?_
    rw [coe_diagUnits]
    refine Matrix.ext fun i j => ?_
    change _ = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) +
      sInf E (Matrix.diagonal (fun i => (fun _ => (r i : ℂ) : Cinf E)) i j)
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Matrix.one_apply_eq]
      exact key i
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h, Matrix.one_apply_ne h,
        map_zero, sub_zero, add_zero]

end GlobalTheory.SiegelTorusInf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSignatureOrthonormalFrameEigenOfCartanInvo
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.HoweD.FrameCartan

open Matrix GlobalTheory.RealLift.HermitianFrameExistence
open scoped ComplexOrder

theorem frame_of_cartan : ∀ (n : ℕ) (M θ : Matrix (Fin n) (Fin n) ℂ), (∀ i j, star (M j i) = M i j) → M.det ≠ 0 →
    IsCartan M θ → ∃ (r s : ℕ) (A : Matrix (Fin n) (Ix r s) ℂ), IsFrame M A ∧ θ * A = A * Jm r s := by
  intro n M θ hM _ hC
  obtain ⟨hθθ, hiso, hpos⟩ := hC
  set G : Matrix (Fin n) (Fin n) ℂ := M.map star with hGdef
  have hJ : ∀ p q : ℕ, (fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).map star =
      fromBlocks 1 0 0 (-1) := by
    intro p q; ext (i | i) (j | j) <;> simp [Matrix.one_apply, apply_ite]
  have Gherm : Gᴴ = G := by
    ext i j
    simp only [hGdef, conjTranspose_apply, map_apply, star_star]
    rw [← hM i j, star_star]
  have hiso' : θᴴ * G * θ = G := by rw [← map_star_trip, hiso]
  have hcomm : θᴴ * G = G * θ := by
    calc θᴴ * G = θᴴ * G * θ * θ := by rw [Matrix.mul_assoc (θᴴ * G), hθθ, Matrix.mul_one]
      _ = G * θ := by rw [hiso']
  have hherm : (G * θ).IsHermitian := by
    unfold IsHermitian; rw [conjTranspose_mul, Gherm, hcomm]
  have hPD : (G * θ).PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hherm, fun x hx => ?_⟩
    have hval : star x ⬝ᵥ (G * θ) *ᵥ x = star ((θ *ᵥ x) ⬝ᵥ M *ᵥ star x) := by
      rw [← hcomm, star_form, ← hGdef, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
    refine Complex.pos_iff.2 ⟨?_, (hherm.im_star_dotProduct_mulVec_self x).symm⟩
    rw [hval, Complex.star_def, Complex.conj_re]; exact hpos x hx
  obtain ⟨p, q, B, B', h1, _, h3, h4⟩ :=
    GlobalTheory.exists_basis_adapted_to_cartan_involution n G θ hθθ hiso' hPD
  refine ⟨p, q, B, ⟨?_, B', h1⟩, h4⟩
  calc Bᵀ * M * B.map star = ((Bᵀ * M * B.map star).map star).map star := by simp [Matrix.map_map, Function.comp_def]
    _ = _ := by rw [map_star_trip, ← hGdef, h3, hJ]; rfl

end GlobalTheory.HoweD.FrameCartan

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumOfSplittingCharacters
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilExist

variable {D : D7}

theorem isHeckeChar_div_pow {χ η : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : IsHeckeChar D η) (n : ℕ) :
    IsHeckeChar D ((η ^ n)⁻¹ * χ) := by
  refine ⟨?_, fun x => ?_⟩
  · have : (((η ^ n)⁻¹ * χ : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => (η x ^ n)⁻¹ * χ x := by
      funext x; simp
    rw [this]
    exact ((hη.1.pow n).inv).mul hχ.1
  · have h1 := hχ.2 x
    have h2 := hη.2 x
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, h1, h2, one_pow, inv_one, mul_one]

theorem resEta_div_pow {χ η : (AE D)ˣ →* Circle} {n : ℕ} (hχ : ResEta D χ n) (hη : ResEta D η 1) :
    ResEta D ((η ^ n)⁻¹ * χ) 0 := by
  refine ⟨hχ.1, fun e he a => ?_⟩
  have h1 := hχ.2 e he a
  have h2 := hη.2 e he a
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, h1, h2, pow_one, pow_zero, inv_mul_cancel]

theorem exists_isWeilDatumO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), (∃ η, IsEtaTilde D η) → IsHeckeChar D χS → IsHeckeChar D χT → ResEta D χS S.rank → ResEta D χT T.rank → ∃ om, IsWeilDatumO ψ S T χS χT om := by
  intro D ψ hψ S T χS χT ⟨η, hη⟩ hS hT rS rT
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨om, hom, -⟩ := _root_.GlobalTheory.WeilProduct.exists_weilDatum_etaTilde D ψ hψ S T θ hθ _ _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S) (GlobalTheory.PlaceModel.isSelfDualC_latFrame T) η hη
  obtain ⟨om', hom', -⟩ := _root_.GlobalTheory.WeilChange.exists_weilDatum_twist D ψ hψ S T _ _ ((η ^ S.rank)⁻¹ * χS) ((η ^ T.rank)⁻¹ * χT) om hom
    (isHeckeChar_div_pow hS hη.1 _) (isHeckeChar_div_pow hT hη.1 _)
    (resEta_div_pow rS hη.2.2.1) (resEta_div_pow rT hη.2.2.1)
  rw [mul_inv_cancel_left, mul_inv_cancel_left] at hom'
  exact ⟨om', hom'⟩

end GlobalTheory.WeilExist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnOffCoordinateHyperplanesOfPoincareBoStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_offCoordinateHyperplanes_of_poincareBound : ∀ {n : ℕ} (S : Finset (Fin n)) (U K : Set (V n)) (g : V n → ℂ) (C : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → ContinuousOn g (offHyp S U) → (∀ v ∈ offHyp S U, v ∉ K → g v = 0) → (∀ v ∈ offHyp S U, v ∈ K → ‖g v‖ ≤ C * ∏ a, (poinWt S v a)⁻¹ ^ 2) → IntegrableOn g (offHyp S U) := by
  first | exact @GlobalTheory.GoodTop.integrableOn_offHyp_of_norm_le_poin | exact GlobalTheory.GoodTop.integrableOn_offHyp_of_norm_le_poin | (intros; apply GlobalTheory.GoodTop.integrableOn_offHyp_of_norm_le_poin <;> assumption)
end

