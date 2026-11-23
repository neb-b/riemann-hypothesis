module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0675
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0838
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0772
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0556
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0811
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0737
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0721
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0784
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0731
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0722
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0839
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0829
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveTateTwistCohomologyTwoSubsingle
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem smoothAffineCurve_tateTwistCohomology_two_subsingleton : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B]
    [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ i : ℤ,
    Subsingleton (Ht q (sp B) 2 i) := by
  intro q _ k B _ _ _ _ _ _ hq i
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q k)
    (Polynomial.degree_cyclotomic_pos q k (NeZero.pos q)).ne'
  have hζ : ∃ ζ : B, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
    refine ⟨algebraMap k B z, ?_⟩
    rw [Polynomial.aeval_algebraMap_apply, Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic,
      hz.eq_zero, map_zero]
  obtain ⟨e⟩ := GlobalTheory.T.tateTwistCohomology_spec_twist_independent q B hqB hζ 2 i 1
  have h0 : ∀ x : Ht q (sp B) 2 1, x = 0 := by
    intro x
    obtain ⟨f, hf, hxf⟩ := GlobalTheory.T.exists_localization_away_pull_eq_zero_Ht_two q k B hq 1 x
    obtain ⟨A', _, _, hA', hxA'⟩ := GlobalTheory.T.exists_etaleNbhd_killing_curveCohomologyClass q k B hq f hf 2 1 (by norm_num) x
    obtain ⟨w, hw⟩ := GlobalTheory.T.etaleExcision_vanishing_under_refinement q B A' f hA' 1 1 x hxf hxA'
    obtain ⟨g, hfg, A₂, C, _, _, _, _, _, _, h2, hg, hC, a, haC, hwa⟩ := GlobalTheory.T.exists_kummerClass_agreeing_near_zeros q k B hq f hf A' hA' w
    exact hw g hfg A₂ C h2 hg hC a haC hwa
  exact ⟨fun a b => e.injective (by rw [h0 (e a), h0 (e b)])⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationNormOneDivisionQuaternion
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

namespace GlobalTheory.QSA.DivAssembly

section Ring

variable {R : Type*} [CommRing R] {a b : R}

theorem nrm_one' : nrm (1 : ℍ[R, a, b]) = 1 := by simp [nrm]

theorem nrm_star' (x : ℍ[R, a, b]) : nrm (star x) = nrm x := by simp [nrm]

theorem star_mul_eq' (x : ℍ[R, a, b]) : star x * x = algebraMap R ℍ[R, a, b] (nrm x) := by
  have h := mul_star_eq (star x)
  rwa [star_star, nrm_star'] at h

theorem nrm_trunc (e : R) (he : e * e = e) (g : ℍ[R, a, b]) :
    nrm (e • (g - 1) + 1) = e * nrm g + (1 - e) := by
  simp only [nrm, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
    QuaternionAlgebra.imK_add, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
    QuaternionAlgebra.imK_smul, QuaternionAlgebra.re_sub, QuaternionAlgebra.imI_sub, QuaternionAlgebra.imJ_sub,
    QuaternionAlgebra.imK_sub, QuaternionAlgebra.re_one, QuaternionAlgebra.imI_one, QuaternionAlgebra.imJ_one,
    QuaternionAlgebra.imK_one, smul_eq_mul]
  linear_combination ((g.re - 1) ^ 2 - a * g.imI ^ 2 - b * g.imJ ^ 2 + a * b * g.imK ^ 2) * he

end Ring

section Alg

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

theorem prod_decomp (e : R) (he : e * e = e) (g : A) :
    ((1 - e) • (g - 1) + 1) * (e • (g - 1) + 1) = g := by
  have h0 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, h0, zero_smul, zero_add]
  rw [← add_assoc, ← add_smul, show e + (1 - e) = 1 by ring, one_smul, sub_add_cancel]

end Alg

variable {F : Type} [Field F] [NumberField F]

theorem isPlacesIdem_idem {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F}
    (h : IsPlacesIdem S₁ S₂ ε) : ε * ε = ε := by
  refine Prod.ext ?_ ?_
  · funext w
    change fstA F ε w * fstA F ε w = fstA F ε w
    by_cases hw : w ∈ S₁
    · rw [h.1 w hw, one_mul]
    · rw [h.2.1 w hw, zero_mul]
  · refine RestrictedProduct.ext _ _ fun u => ?_
    change evalV F u (sndA F (ε * ε)) = evalV F u (sndA F ε)
    rw [map_mul, map_mul]
    by_cases hu : u ∈ S₂
    · rw [h.2.2.1 u hu, one_mul]
    · rw [h.2.2.2 u hu, zero_mul]

theorem rat_mul' {a b : F} (x y : ℍ[F, a, b]) : rat (x * y) = rat x * rat y := by
  ext <;> simp [rat]

theorem rat_one' {a b : F} : rat (1 : ℍ[F, a, b]) = 1 := by
  ext <;> simp [rat]

theorem continuous_smul_const {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {a b : R}
    (x : ℍ[R, a, b]) : Continuous fun t : R => t • x := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  fin_cases i <;> simp [coords, Function.comp_def] <;> fun_prop

end GlobalTheory.QSA.DivAssembly

namespace GlobalTheory.QSA.DivAssembly

variable {F : Type} [Field F] [NumberField F]

theorem conj_mem_normOneIdempotentSubgroup_of_rational_relation {a b : F} (ε : AF F) (w c c' : DA F a b) (l : AF F) (hl : IsUnit l) (δ γ : ℍ[F, a, b])
    (hδ : nrm δ ≠ 0) (hγ : nrm γ = 1) (h : DA F a b) (hh : nrm h = 1) (hhε : ε • (h - 1) = h - 1)
    (hcc' : c * c' = 1)
    (hyw : l • (rat δ * c) * w = rat γ * l • (rat δ * c) * h) : c * w * c' ∈ H0 ε := by
  set δ' : ℍ[F, a, b] := (nrm δ)⁻¹ • star δ with hδ'
  have hδδ : δ' * δ = 1 := by
    rw [hδ', smul_mul_assoc, star_mul_eq', Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hδ, map_one]
  have E1 : rat δ * c * w = rat γ * rat δ * c * h := by
    have h2 : l • (rat δ * c * w) = l • (rat γ * rat δ * c * h) := by
      rw [← smul_mul_assoc, hyw, mul_smul_comm, smul_mul_assoc, mul_assoc (rat γ), mul_assoc (rat γ)]
      simp only [mul_assoc]
    exact hl.smul_left_cancel.1 h2
  refine ⟨δ' * γ * δ, ?_, c * h * c', ?_, ?_, ?_⟩
  · rw [nrm_mul, nrm_mul, hγ, mul_one, ← nrm_mul, hδδ, nrm_one']
  · rw [nrm_mul, nrm_mul, hh, mul_one, ← nrm_mul, hcc', nrm_one']
  · have e1 : c * h * c' - 1 = c * (h - 1) * c' := by
      rw [mul_sub, sub_mul, mul_one, hcc']
    rw [e1, ← smul_mul_assoc, ← mul_smul_comm, hhε]
  · calc c * w * c' = (rat δ' * rat δ) * c * w * c' := by rw [← rat_mul', hδδ, rat_one', one_mul]
      _ = rat δ' * (rat δ * c * w) * c' := by simp only [mul_assoc]
      _ = rat δ' * (rat γ * rat δ * c * h) * c' := by rw [E1]
      _ = rat (δ' * γ * δ) * (c * h * c') := by simp only [rat_mul', mul_assoc]

theorem strongApproximation_normOne_divisionQuaternion : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → (∀ x : ℍ[F, a, b], nrm x = 0 → x = 0) → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → (∀ t : AF F, ∃ h : DA F a b, nrm h = 1 ∧ ε * h.re = ε * t) → ∀ g : DA F a b, nrm g = 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
  intro F _ _ a b ha hb hdiv S₁ S₂ ε hε hS hsurj g hg
  have hee : ε * ε = ε := isPlacesIdem_idem hε
  obtain ⟨hmul, -, -, -⟩ := GlobalTheory.T.closure_normOneProducts_h0_properties F a b ε hee
  obtain ⟨htr, -, -, hT2⟩ := _root_.GlobalTheory.quaternion_isTopologicalRing_nrm_re_t2 (AF F) (algebraMap F (AF F) a) (algebraMap F (AF F) b)
  haveI : IsTopologicalRing (DA F a b) := htr
  haveI : T2Space (AF F) := by
    haveI : T2Space (InfiniteAdeleRing F) := inferInstanceAs (T2Space (∀ w : InfinitePlace F, w.Completion))
    haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := inferInstanceAs (T2Space (RestrictedProduct
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
    exact inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
  haveI : T2Space (DA F a b) := hT2 inferInstance
  obtain ⟨C, hC, hfuj⟩ := _root_.GlobalTheory.QSA.FujisakiQ.fujisaki_mod_centre F a b ha hb hdiv

  have key : ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F),
      IsPlacesIdem T₁ T₂ η → ∀ g : DA F a b, nrm g = 1 → η • (g - 1) = g - 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
    intro T₁ T₂ η hη g hg hgη
    have hee' : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination hee
    set gS : DA F a b := ε • (g - 1) + 1 with hgSdef
    set gN : DA F a b := (1 - ε) • (g - 1) + 1 with hgNdef
    have hprod : gN * gS = g := prod_decomp ε hee g
    have hgS : gS ∈ H0 (a := a) (b := b) ε := by
      refine ⟨1, nrm_one', gS, ?_, ?_, by rw [rat_one', one_mul]⟩
      · rw [hgSdef, nrm_trunc ε hee, hg]; ring
      · rw [hgSdef, add_sub_cancel_right, smul_smul, hee]
    have hgN1 : nrm gN = 1 := by rw [hgNdef, nrm_trunc (1 - ε) hee', hg]; ring
    have hgNε : ε • (gN - 1) = 0 := by
      rw [hgNdef, add_sub_cancel_right, smul_smul, show ε * (1 - ε) = 0 by linear_combination -hee, zero_smul]
    have hgNη : η • (gN - 1) = gN - 1 := by
      rw [hgNdef, add_sub_cancel_right, smul_comm, hgη]
    have hW : ∀ W ∈ 𝓝 gN, ∃ c ∈ C, ∃ c' ∈ C, c * c' = 1 ∧ c' * c = 1 ∧ ∃ w ∈ W, c * w * c' ∈ H0 (a := a) (b := b) ε := by
      intro W hW
      obtain ⟨w, hwW, y, hy, γ, hγ, h, hh, hhε, hyw⟩ :=
        _root_.GlobalTheory.QSAStep.key_step F a b ha hb S₁ S₂ ε hε hS hsurj gN hgN1 hgNε W hW
      obtain ⟨δ, l, c, c', hδ, hl, hc, hc', hcc', hc'c, rfl⟩ := hfuj y hy
      exact ⟨c, hc, c', hc', hcc', hc'c, w, hwW, conj_mem_normOneIdempotentSubgroup_of_rational_relation ε w c c' l hl δ γ hδ hγ h hh hhε hcc' hyw⟩
    obtain ⟨c, -, c', -, hcc', hc'c, hmem⟩ := _root_.GlobalTheory.exists_inverse_conj_mem_closure_of_isCompact (DA F a b) (H0 (a := a) (b := b) ε) C hC gN hW
    have hgN := GlobalTheory.T.mem_closure_rationalNormOne_of_idempotent_conj F a b ha hb T₁ T₂ η hη ε hee gN hgN1 hgNη c c' hcc' hc'c hmem
    rw [← hprod]
    exact hmul _ hgN _ (subset_closure hgS)

  suffices g ∈ closure (closure (H0 (a := a) (b := b) ε)) by rwa [closure_closure] at this
  have hφ : Continuous fun η : AF F => η • (g - 1) + 1 := (continuous_smul_const (g - 1)).add continuous_const
  rw [mem_closure_iff_nhds]
  intro V hV
  have hpre : (fun η : AF F => η • (g - 1) + 1) ⁻¹' V ∈ 𝓝 (1 : AF F) :=
    hφ.continuousAt.preimage_mem_nhds (by rwa [one_smul, sub_add_cancel])
  obtain ⟨T₁, T₂, η, hη, hηV⟩ := _root_.GlobalTheory.placesIdem_tendsto_one F _ hpre
  have hηη : η * η = η := isPlacesIdem_idem hη
  refine ⟨η • (g - 1) + 1, hηV, key T₁ T₂ η hη _ ?_ ?_⟩
  · rw [nrm_trunc η hηη, hg]; ring
  · rw [add_sub_cancel_right, smul_smul, hηη]

end GlobalTheory.QSA.DivAssembly
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairAction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SymplOInv

theorem sum_four_eq_trace {A : Type} [CommRing A] {m n : ℕ} (σ : A →+* A) (P : Matrix (Fin n) (Fin n) A)
    (Q : Matrix (Fin m) (Fin m) A) (x y : Matrix (Fin m) (Fin n) A) :
    ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ (y c b) * Q c d * x d a = (P * (y.map σ)ᵀ * Q * x).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Eq.symm ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]

theorem sum_unitary {A : Type} [CommRing A] {m n : ℕ} (σ : A →+* A) (Q g : Matrix (Fin m) (Fin m) A)
    (P P' k : Matrix (Fin n) (Fin n) A) (hP : P * P' = 1) (hg : (g.map σ)ᵀ * Q * g = Q)
    (hk : (k.map σ)ᵀ * P' * k = P') (x y : Matrix (Fin m) (Fin n) A) :
    ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ ((g * y * k) c b) * Q c d * (g * x * k) d a =
      ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ (y c b) * Q c d * x d a := by
  have h1 : (P * (k.map σ)ᵀ * P') * k = 1 := by
    rw [Matrix.mul_assoc P, Matrix.mul_assoc P, hk, hP]
  have h2 : k * (P * (k.map σ)ᵀ * P') = 1 := mul_eq_one_comm.1 h1
  have hP' : P' * P = 1 := mul_eq_one_comm.1 hP
  have hk' : k * P * (k.map σ)ᵀ = P := by
    calc k * P * (k.map σ)ᵀ = k * P * (k.map σ)ᵀ * (P' * P) := by rw [hP', Matrix.mul_one]
      _ = (k * (P * (k.map σ)ᵀ * P')) * P := by simp only [Matrix.mul_assoc]
      _ = P := by rw [h2, Matrix.one_mul]
  have e : P * ((g * y * k).map σ)ᵀ * Q * (g * x * k) =
      (P * (k.map σ)ᵀ * ((y.map σ)ᵀ * ((g.map σ)ᵀ * Q * g) * x)) * k := by
    simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [sum_four_eq_trace, sum_four_eq_trace, e, hg, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc k, hk']
  simp only [Matrix.mul_assoc]

theorem hO_actO {D : D7} (S T : HSp D) (g : GA D S) (h : GA D T) (x y : WO S T) :
    hO S T (actO S T g h x) (actO S T g h y) = hO S T x y := by
  have h1 : S.gram⁻¹.map (incA D) * S.gram.map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S)]
    exact Matrix.map_one _ (incA D).map_zero (incA D).map_one
  exact sum_unitary (cA D) (T.gram.map (incA D)) (mt T h) (S.gram⁻¹.map (incA D)) (S.gram.map (incA D)) (mt S g⁻¹)
    h1 h.2 (g⁻¹).2 x y

theorem symplO_actO : ∀ (D : D7) (S T : HSp D) (g : GA D S) (h : GA D T) (x y : WO S T), symplO S T (actO S T g h x) (actO S T g h y) = symplO S T x y := by
  intro D S T g h x y
  unfold symplO
  rw [hO_actO]

end GlobalTheory.SymplOInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorObjDualRepresents
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Serre

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HomScheme

variable {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X]

theorem dualTensorHom_lTensor {N N' : Type} [AddCommGroup N] [Module O N] [AddCommGroup N']
    [Module O N'] (g : N →ₗ[O] N') (z : Module.Dual O X ⊗[O] N) (x : X) :
    dualTensorHom O X N' (g.lTensor _ z) x = g (dualTensorHom O X N z x) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f n => simp [dualTensorHom_apply]
  | add z w hz hw => simp [map_add (f := _), hz, hw]

variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]
  {a : OAct O G} {b : OAct O H}

def homEquiv [Module.Finite O X] [Module.Projective O X] (h : IsTensor H b G a (Module.Dual O X))
    (T : Over S) : Pts b T ≃ₗ[O] (X →ₗ[O] Pts a T) :=
  (h.equiv T).symm.trans (dualTensorHomEquiv O X (Pts a T))

theorem homEquiv_pre [Module.Finite O X] [Module.Projective O X]
    (h : IsTensor H b G a (Module.Dual O X)) {T T' : Over S} (u : T' ⟶ T) (y : Pts b T) (x : X) :
    homEquiv h T' (Pts.pre b u y) x = Pts.pre a u (homEquiv h T y x) := by
  simp only [homEquiv, LinearEquiv.trans_apply]
  rw [h.natural_symm]
  exact dualTensorHom_lTensor _ _ x

theorem tensorObj_dual_represents {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B]
    {O : Type} [CommRing O] (a : OAct O B) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Projective O X] :
    ∃ u : X → (tensorObj (Module.Dual O X) a ⟶ B),
      (∀ x, IsMonHom (u x)) ∧ (∀ x y, u (x + y) = u x * u y) ∧
      (∀ (o : O) x, u (o • x) = u x ≫ a.act o) ∧
      ∀ (T : Over S) (f : X → (T ⟶ B)), (∀ x y, f (x + y) = f x * f y) →
        (∀ (o : O) x, f (o • x) = f x ≫ a.act o) →
          ∃! c : T ⟶ tensorObj (Module.Dual O X) a, ∀ x, c ≫ u x = f x := by
  let M := Module.Dual O X
  let C := tensorObj M a
  let b := tensorAct M a
  let h : IsTensor C b B a M := isTensor M a
  let Φ := homEquiv h
  let u : X → (C ⟶ B) := fun x => (Φ C (Pts.mk b (𝟙 C)) x).hom
  have hnat : ∀ (T : Over S) (c : T ⟶ C) (x : X), (Φ T (Pts.mk b c) x).hom = c ≫ u x := by
    intro T c x
    have := congrArg Pts.hom (homEquiv_pre h c (Pts.mk b (𝟙 C)) x)
    rw [Pts.hom_pre] at this
    rw [← this]
    congr 3
  refine ⟨u, fun x => ?_, fun x y => ?_, fun o x => ?_, fun T f hadd hsmul => ?_⟩
  · refine isMonHom_of_mul_comp _ fun T p q => ?_
    rw [← hnat, ← hnat, ← hnat, Pts.mk_mul, map_add (f := _), LinearMap.add_apply, Pts.hom_add]
  · change (Φ C _ (x + y)).hom = _
    rw [map_add (f := _), Pts.hom_add]
  · change (Φ C _ (o • x)).hom = _
    rw [map_smul, Pts.hom_smul]
  · let F : X →ₗ[O] Pts a T :=
      { toFun := fun x => Pts.mk a (f x)
        map_add' := fun x y => by rw [hadd]; rfl
        map_smul' := fun o x => by rw [hsmul]; rfl }
    refine ⟨((Φ T).symm F).hom, fun x => ?_, fun c hc => ?_⟩
    · rw [← hnat, Pts.mk_hom, LinearEquiv.apply_symm_apply]
      rfl
    · have : Φ T (Pts.mk b c) = F := by
        ext1 x
        apply Pts.ext
        rw [hnat, hc]
        rfl
      rw [← this, LinearEquiv.symm_apply_apply]
      rfl

theorem exists_homObj_relDim (S : Scheme.{0}) (B : Over S) [GrpObj B] (hB : IsAbelianScheme B)
    (g : ℕ) (hg : SmoothOfRelativeDimension g B.hom)
    {O : Type} [CommRing O] [IsDomain O] [Module.Finite ℤ O] (a : OAct O B) (X : Type)
    [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] :
    ∃ (C : Over S) (_ : GrpObj C) (u : X → (C ⟶ B)), IsAbelianScheme C ∧
      SmoothOfRelativeDimension (Module.finrank O X * g) C.hom ∧
      (∀ x, IsMonHom (u x)) ∧ (∀ x y, u (x + y) = u x * u y) ∧
      (∀ (o : O) x, u (o • x) = u x ≫ a.act o) ∧
      ∀ (T : Over S) (f : X → (T ⟶ B)), (∀ x y, f (x + y) = f x * f y) →
        (∀ (o : O) x, f (o • x) = f x ≫ a.act o) → ∃! c : T ⟶ C, ∀ x, c ≫ u x = f x := by
  haveI := hB.comm
  obtain ⟨u, h1, h2, h3, h4⟩ := tensorObj_dual_represents B a X
  exact ⟨_, inferInstance, u, (isTensor (Module.Dual O X) a).isAbelianScheme hB,
    _root_.GlobalTheory.TensorDualDim.smoothOfRelativeDimension_tensorObj_dual S B O a X g hg, h1, h2, h3, h4⟩

end GlobalTheory.HomScheme
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThAHeisEntireLinearInjective
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem thA_heis_entire_linear_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r g n : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → Even n → ∀ x ∈ X.dom, ∀ φ : TF n g, GlobalTheory.SW.IsSB φ → (∀ (y : Matrix (Fin n) (Fin r) E) (z : Fin n → Fin g → ℂ), GlobalTheory.SW.IsSB (heisG X bas y φ) ∧ thA X bas idx (heisG X bas y φ) x z = cexp (-(Real.pi * ∑ b, hx X bas idx x (z b + (1 / 2 : ℂ) • pv X idx x (y b)) (pv X idx x (y b)))) * thA X bas idx φ x (fun b => z b + pv X idx x (y b))) ∧ Differentiable ℂ (thA X bas idx φ x) ∧ (∀ φ' : TF n g, GlobalTheory.SW.IsSB φ' → (∀ a b : ℂ, GlobalTheory.SW.IsSB (a • φ + b • φ') ∧ thA X bas idx (a • φ + b • φ') x = a • thA X bas idx φ x + b • thA X bas idx φ' x) ∧ (thA X bas idx φ x = thA X bas idx φ' x → φ = φ')) := by
  intro E _ _ _ r g n X bas idx hs hn x hd φ hφ
  refine ⟨fun y z => ?_, GlobalTheory.SW.ThetaHol.differentiable_thA idx hs hφ hd, fun ψ hψ => ⟨fun a b => ?_, ?_⟩⟩
  · obtain ⟨h1, -, -, -, h2⟩ := (GlobalTheory.SW.heisG_laws E r X g bas idx n hs hn).2.2.2 y φ hφ
    exact ⟨h1, h2 x hd z⟩
  · have h1 : GlobalTheory.SW.IsSB (a • φ) := (_root_.GlobalTheory.SW.isSB_algebra_haar_linear _ _ _ _ _ hφ hφ).2.1 a
    have h2 : GlobalTheory.SW.IsSB (b • ψ) := (_root_.GlobalTheory.SW.isSB_algebra_haar_linear _ _ _ _ _ hψ hψ).2.1 b
    refine ⟨(_root_.GlobalTheory.SW.isSB_algebra_haar_linear _ _ _ _ _ h1 h2).1, ?_⟩
    rw [GlobalTheory.SW.UnAct.thA_add idx hs hd h1 h2, GlobalTheory.SW.UnAct.thA_smul, GlobalTheory.SW.UnAct.thA_smul]
  · exact GlobalTheory.SW.UnAct.eq_of_thA_eq idx hs hd hφ hψ

end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFiresIffThetaMultExists
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct

namespace GlobalTheory.ThetaFiresOfMult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelFiring GlobalTheory.IndefiniteRowSideFullHecke.ThetaMultiplicity

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option maxHeartbeats 1000000 in
theorem exists_isThetaMult_of_firesAt {R : RealDat D A Ks} {i : Fin D.R.m} {t : T}
    (h : ∀ x, FiresAt R i t x) : ∃ y : (R.HV i t).H →ₗ[ℂ] MMap (R.MW i (sg0 D A)), IsThetaMult R i t y :=
  GlobalTheory.ThetaFiresLinear.exists_linear_lift (lowT (R.MW i (sg0 D A))) (R.Wall i (sg0 D A)) (R.νV i t) (R.fdV i t)
    (kernel R i t) (R.ptP i t) (GlobalTheory.ThetaFiresLinear.kernelL R i t)
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) (R.vP i t))
    (fun _ _ _ => rfl) (fun _ => rfl) (R.ioP i) (R.extV i t) h

end GlobalTheory.ThetaFiresOfMult

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrVal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl GlobalTheory.Ex
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

def trVal {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N : NumD F} (ν : NumOf D F N) {k : ℕ} (s : Fam D F k) (gm : GtPt D (TE R F)) (α mu : N.X) : DualNumber F :=
  sE (s.s (ν.eX α))
    ((lift (Over.homMk (spMap (algebraMap F (DualNumber F))) rfl : TE R F ⟶ TF (R := R) F) gm.b).left ≫
      (DegPre.trF D F (ν.eX mu)).left) ν.J

end GlobalTheory.MBLow

end
end

