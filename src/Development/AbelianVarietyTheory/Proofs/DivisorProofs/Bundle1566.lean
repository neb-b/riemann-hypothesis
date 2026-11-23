module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0136
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1526
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareMuDivChiRamifiedAtTwistPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RamTwist

theorem unramAt_of_div {D : D7} {ε : AF D.host.F} {a b c : (AE D)ˣ →* Circle}
    (h : GlobalTheory.WeilParts.UnramAt ε (a * b / c)) (ha : GlobalTheory.WeilParts.UnramAt ε a) (hc : GlobalTheory.WeilParts.UnramAt ε c) :
    GlobalTheory.WeilParts.UnramAt ε b := by
  intro x h1 h2 h3
  have e := h x h1 h2 h3
  rw [MonoidHom.div_apply, MonoidHom.mul_apply, ha x h1 h2 h3, hc x h1 h2 h3, one_mul, div_one] at e
  exact e

theorem not_overP_g {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc)
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∉ G.pl.S0) (PP : HeightOneSpectrum (𝓞 D.host.E))
    (hPP : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v) (k : Fin 2) : ¬ Formalism.L2.Host.OverP D.host (D.host.g k) PP := by
  intro h
  have hk : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
    subst hPP
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal
    rw [map_natCast]
    exact h
  refine hv (G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_)))
  fin_cases k
  · exact Or.inl hk
  · exact Or.inr (Or.inl hk)

end GlobalTheory.RamTwist


open GlobalTheory.RamTwist in
theorem GlobalTheory.SqTop.not_unramAt_twist : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∉ G.pl.S0 → ∀ PP ∈ Lc.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v → ∀ i j : Fin D.R.m, ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) / G.ch.chi (D.R.m - i)) := by
  intro D T Lc sc G μ₀ hμ t v e he hv PP hPP hPv i j hU
  have hmi1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have hmi2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  have hchi : GlobalTheory.WeilParts.UnramAt e (G.ch.chi (D.R.m - i)) :=
    GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (G.ch.chi_eq _ hmi1 hmi2) v e he fun P hP =>
      G.ch.unr _ hmi1 hmi2 P (hP ▸ hv)
  have hmu : GlobalTheory.WeilParts.UnramAt e (Lc.mu0 ((j : ℕ) + 1)) :=
    GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (hμ.mu0 j) v e he fun P hP =>
      (Lc.C.isMu0 j).unr P (not_overP_g G hv P hP)
  have hxi : GlobalTheory.WeilParts.UnramAt e (Lc.xi t) := by
    refine unramAt_of_div (a := Lc.mu0 ((j : ℕ) + 1)) (c := G.ch.chi (D.R.m - i)) ?_ hmu hchi
    exact hU
  have h1 := GlobalTheory.UnrOverPlace.unrAt_of_unramAt D (Lc.xi t) v e he hxi PP hPv
  exact (hμ.Q_ram t PP).2 (Or.inl hPP) ((GlobalTheory.LFun.unrAt_iff_of_chrEq (hμ.xi t) PP).1 h1)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.PsiNontriv

variable {F : Type} [Field F] [NumberField F]

theorem trace_re (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ w : InfinitePlace F, (w.mult : ℝ) * (w.embedding x).re := by
  first
  | exact @_root_.GlobalTheory.TraceRealEmbeddingSum.trace_eq_sum_mult_mul_re
  | exact _root_.GlobalTheory.TraceRealEmbeddingSum.trace_eq_sum_mult_mul_re
  | (apply _root_.GlobalTheory.TraceRealEmbeddingSum.trace_eq_sum_mult_mul_re <;> assumption)
  | (intros; apply _root_.GlobalTheory.TraceRealEmbeddingSum.trace_eq_sum_mult_mul_re <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TraceRealEmbeddingSum.trace_eq_sum_mult_mul_re <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TraceRealEmbeddingSum.trace_eq_sum_mult_mul_re ..)

theorem trace_mixedEmbedding (x : F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (mixedEmbedding F x) = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  rw [trace_re, Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi,
    InfinitePlace.sum_eq_sum_add_sum]
  simp only [Algebra.trace_complex_apply, mixedEmbedding.mixedEmbedding_apply_isReal,
    mixedEmbedding.mixedEmbedding_apply_isComplex, Algebra.trace_self_apply]
  congr 1
  · refine Fintype.sum_congr _ _ fun w => ?_
    rw [InfinitePlace.mult_isReal, Nat.cast_one, one_mul, ← InfinitePlace.embedding_of_isReal_apply w.2,
      Complex.ofReal_re]
  · refine Fintype.sum_congr _ _ fun w => ?_
    rw [InfinitePlace.mult_isComplex]
    push_cast
    rfl

end GlobalTheory.PsiNontriv

namespace GlobalTheory.PsiNontriv

open GlobalTheory.Idele WithZero
open GlobalTheory.StdDual (codiff codiff_ne_zero)

variable {F : Type} [Field F] [NumberField F]

theorem at_pairA_zero (a : Ainf F) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (pairA F a 0) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  refine Prod.ext ?_ ?_
  · change u.1 * a = 0
    rw [h1, zero_mul]
  · change u.2 * 0 = 0
    exact mul_zero _

theorem isStd_fin_rat {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : F) :
    ψ (pairA F 0 (algebraMap F (Af F) x)) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ)) := by
  have e : pairA F 0 (algebraMap F (Af F) x) =
      algebraMap F (AF F) x + pairA F (algebraMap F (Ainf F) (-x)) 0 := by
    refine Prod.ext ?_ (add_zero _).symm
    show (0 : Ainf F) = algebraMap F (Ainf F) x + algebraMap F (Ainf F) (-x)
    rw [map_neg, add_neg_cancel]
  have hev : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (pairA F (algebraMap F (Ainf F) (-x)) 0) = mixedEmbedding F (-x) :=
    (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (K := F)).symm
  rw [e, AddChar.map_add_eq_mul, hψ.2.1, one_mul, hψ.2.2 _ (at_pairA_zero _), hev, map_neg, map_neg,
    trace_mixedEmbedding]
  congr 1
  push_cast
  ring

theorem psiAt_ne_one : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), GlobalTheory.LatVac.psiAt ψ v ≠ 1 := by
  intro F _ _ ψ hψ v h1
  set c := FractionalIdeal.count F v (codiff F) with hc
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  set x : Fv F v := algebraMap F (Fv F v) (π ^ (c - 1)) with hx
  have hmem : GlobalTheory.AdelicU.singleFin v x ∈ adelicIdeal (codiff F) := by
    rw [GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (isStd_fin_rat hψ)]
    intro α hα
    have e : α * GlobalTheory.AdelicU.singleFin v x = GlobalTheory.AdelicU.singleFin v (α v * x) := by
      apply GlobalTheory.AdelicU.af_ext
      intro u
      by_cases hu : u = v
      · subst hu
        rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]
        rfl
      · rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]
    rw [e]
    have := DFunLike.congr_fun h1 (α v * x)
    rw [AddChar.one_apply] at this
    exact this
  have h2 := (mem_adelicIdeal_iff codiff_ne_zero).1 hmem v
  rw [show (GlobalTheory.AdelicU.singleFin v x) v = x from GlobalTheory.AdelicU.evalV_singleFin_self v x, hx, valued_algebraMap,
    map_zpow₀, hπ, ← WithZero.exp_zsmul, WithZero.exp_le_exp, smul_eq_mul] at h2
  omega

end GlobalTheory.PsiNontriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSmulDifferentialMemEigenLattice
section
open NumberField

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM GlobalTheory.CM.IntCoord

set_option autoImplicit false

namespace GlobalTheory.FlatCM.HomLat

theorem sum_smul_diff_mem_eigLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0), ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ∀ τE : E →+* K, (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
          ∀ c ∈ GlobalTheory.FlatCM.HomLat.coords X, ∀ e ∈ FP.eigLat (X.A true).t.act τ,
            ∑ a, τE (c a) • MP a e ∈ FB.eigLat X.B.t.act τ := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p X FP FB MP hMP τ _ τE hτE c hc e he
  obtain ⟨n, hn, x, hx, f, hf, hfn⟩ := hc
  have hcA := integral_tangent_coordinates K _ FP
  have hcB := integral_tangent_coordinates K _ FB
  obtain ⟨u, hu, heig⟩ := (hcA.2.2.2.2.2 _ _ τ e).1 he
  have := hf.isMonHom
  have ht : IsTangent (u ≫ f) := by
    have hv := hu.1
    unfold IsTangent at hv ⊢
    rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, IsMonHom.one_hom]
  obtain ⟨d, hd, -⟩ := hcB.1 _ ht
  have hs : ∀ a, FB.IsCoord (u ≫ ((X.A true).t.act.act (x a) ≫ phiP X a)) (MP a (τ (x a) • e)) := by
    intro a
    rw [← Category.assoc]
    exact hMP a _ _ (isCoord_smul FP hu (heig (x a)))
  have hprod : ∀ s : Finset (Fin p), FB.IsCoord (u ≫ ∏ a ∈ s, ((X.A true).t.act.act (x a) ≫ phiP X a))
      (∑ a ∈ s, MP a (τ (x a) • e)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.sum_empty, comp_one]
      exact isCoord_one FB
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, comp_mul]
      exact isCoord_mul FB (hs a) ih
  have hpow : ∀ m : ℕ, FB.IsCoord ((u ≫ f) ^ m) (m • d) := by
    intro m
    induction m with
    | zero =>
      rw [pow_zero, zero_smul]
      exact isCoord_one FB
    | succ m ih =>
      rw [pow_succ, succ_nsmul]
      exact isCoord_mul FB ih hd
  have heq : n • d = ∑ a, MP a (τ (x a) • e) := by
    have h1 := hpow n
    rw [← comp_pow, hfn] at h1
    exact (hcB.1 _ h1.1).unique h1 (hprod Finset.univ)
  have hdval : d = ∑ a, τE (c a) • MP a e := by
    have hn0 : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    refine smul_right_injective _ hn0 ?_
    show (n : K) • d = (n : K) • ∑ a, τE (c a) • MP a e
    rw [Nat.cast_smul_eq_nsmul, heq, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← algebraMap_smul K (τ (x a)) e, map_smul, smul_smul]
    congr 1
    show ((τ (x a) : 𝓞 K) : K) = (n : K) * τE (c a)
    rw [← hτE, hx a, map_mul, map_natCast]
  rw [← hdval]
  refine (hcB.2.2.2.2.2 _ _ τ _).2 ⟨u ≫ f, hd, fun s => ?_⟩
  rw [isLieComb_one_iff, Category.assoc, ← hf.comm s, ← Category.assoc, (isLieComb_one_iff _ _ _).1 (heig s),
    Category.assoc]

end GlobalTheory.FlatCM.HomLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormBaseChangeMatrix
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory

theorem hTens_eq_trace {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S)
    {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α S) (JB : Matrix β β S) (x y : Matrix α β S) :
    hTens c JA JB x y = Matrix.trace (JAᵀ * (x * JB * (y.map c)ᵀ)) := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => enter [2, k]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem symp_mul_left {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) (ξ : S)
    {α α' β : Type} [Fintype α] [Fintype α'] [Fintype β]
    (JA : Matrix α α S) (JB : Matrix β β S) (P : Matrix α α' S) (z z' : Matrix α' β S) :
    symp c ξ JA JB (P * z) (P * z') = symp c ξ (Pᵀ * JA * P.map c) JB z z' := by
  unfold symp
  congr 2
  rw [hTens_eq_trace, hTens_eq_trace, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]
  conv_rhs => rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormRightMulTranspose
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv

namespace GlobalTheory.SympRight

theorem hTens_eq_trace' {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S)
    {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α S) (JB : Matrix β β S) (x y : Matrix α β S) :
    hTens c JA JB x y = Matrix.trace (xᵀ * JA * y.map c * JBᵀ) := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem symp_mul_transpose_right : ∀ {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) (ξ : S)
    {α β β' : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype β'] [DecidableEq β']
    (JA : Matrix α α S) (JB : Matrix β β S) (Q : Matrix β β' S) (z z' : Matrix α β' S),
    symp c ξ JA JB (z * Qᵀ) (z' * Qᵀ) = symp c ξ JA (Qᵀ * JB * Q.map c) z z' := by
  intro R S _ _ _ c ξ α β β' _ _ _ _ _ _ JA JB Q z z'
  simp only [symp, hTens_eq_trace']
  congr 2
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, Matrix.transpose_map,
    Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm Q]
  simp only [Matrix.mul_assoc]

end GlobalTheory.SympRight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqIntegralSpanGenerato
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

namespace GlobalTheory.LatParam

theorem vecMulVec_sum_zsmul {E : Type} [Field E] {n d kx ky : ℕ} (ex : Fin kx → Fin n → E) (fy : Fin ky → Fin d → E)
    (c : Fin kx → ℤ) (c' : Fin ky → ℤ) :
    Matrix.vecMulVec (∑ i, c i • ex i) (∑ j, c' j • fy j) =
      ∑ m : Fin kx × Fin ky, (c m.1 * c' m.2) • Matrix.vecMulVec (ex m.1) (fy m.2) := by
  ext a b
  simp only [Matrix.vecMulVec_apply, Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply, Matrix.smul_apply,
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [zsmul_eq_mul, Int.cast_mul]; ring

theorem latAtV_param : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (X : Spc F E n)
    (Y : Spc F E d), X.L.IsLattice E → Y.L.IsLattice E → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F),
    ∃ (M : Type) (_ : Fintype M) (g : M → Matrix (Fin n) (Fin d) E), ∀ γ,
      γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v ↔ ∃ a : M → v.adicCompletionIntegers F,
        γ = ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m) := by
  intro F E _ _ _ _ _ n d X Y hX hY v
  obtain ⟨kx, ex, hex⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (hX.fg.restrictScalars (R := ℤ))
  obtain ⟨ky, fy, hfy⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (hY.fg.restrictScalars (R := ℤ))
  let I : Matrix (Fin n) (Fin d) E →+ Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
    (inclR (F := F) (E := E) (AF F)).toAddMonoidHom.mapMatrix
  have hI : ∀ J, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J = I J := fun J => rfl
  refine ⟨Fin kx × Fin ky, inferInstance, fun m => Matrix.vecMulVec (ex m.1) (fy m.2), fun γ => ⟨fun h => ?_, ?_⟩⟩
  · induction h using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hint, x, hx, y, hy, rfl⟩ := hz
      have hx' : x ∈ Submodule.span ℤ (Set.range ex) := by rw [hex]; exact hx
      have hy' : y ∈ Submodule.span ℤ (Set.range fy) := by rw [hfy]; exact hy
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx'
      obtain ⟨c', rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy'
      refine ⟨fun m => ⟨(c m.1 * c' m.2) • GlobalTheory.AdelicU.evFin F v a, zsmul_mem hint _⟩, ?_⟩
      have ha' := GlobalTheory.VacAny.eq_atPlace_of_at v a ha
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hI, vecMulVec_sum_zsmul, map_sum, map_zsmul, Finset.smul_sum, map_zsmul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← ha', smul_comm, smul_assoc]
    | zero => exact ⟨fun _ => 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, by simp only [Pi.add_apply, AddMemClass.coe_add, map_add (f := _), add_smul, Finset.sum_add_distrib]⟩
    | neg x _ hx =>
      obtain ⟨a, rfl⟩ := hx
      exact ⟨-a, by simp only [Pi.neg_apply, NegMemClass.coe_neg, map_neg, neg_smul, Finset.sum_neg_distrib]⟩
  · rintro ⟨a, rfl⟩
    refine AddSubgroup.sum_mem _ fun m _ => AddSubgroup.subset_closure ?_
    refine ⟨_, ?_, ?_, ex m.1, ?_, fy m.2, ?_, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]
    · rw [GlobalTheory.EmbChart.evFin_atPlace]; exact (a m).2
    · have : ex m.1 ∈ Submodule.span ℤ (Set.range ex) := Submodule.subset_span ⟨m.1, rfl⟩
      rw [hex] at this; exact this
    · have : fy m.2 ∈ Submodule.span ℤ (Set.range fy) := Submodule.subset_span ⟨m.2, rfl⟩
      rw [hfy] at this; exact this

end GlobalTheory.LatParam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestPlacesPrimeToLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlacesPrime

theorem not_both_mem {R : Type} [CommRing R] {I : Ideal R} (hI : I.IsPrime) {a b : ℕ} (h : Nat.Coprime a b)
    (ha : (a : R) ∈ I) : (b : R) ∉ I := by
  intro hb
  obtain ⟨u, v, e⟩ := (Nat.isCoprime_iff_coprime.2 h).map (Int.castRingHom R)
  apply hI.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  simp only [eq_intCast, Int.cast_natCast]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)

theorem coprime_level {D : D7} {large₂ : SizeData₂ D} (h : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) {p : ℕ} (hp : p.Prime)
    (hl : p ∈ D.host.levelPrimes) : Nat.Coprime p (D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK) := by
  obtain ⟨⟨P, -, -⟩, -⟩ := h
  exact Nat.Coprime.mul_right (UpperTheory.Ram.Fun.coprime_condN_of_splitK D.host hp (P.level_split p hl))
    (D.host.ccK_coprime p (by simp [hl])).symm

theorem leastSplitAuxiliaryPrime_coprime_host_invariants (D : D7) : Nat.Coprime (q0 D) (D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK) := by
  obtain ⟨hp, hm, hn⟩ := leastSplitAuxiliaryPrimeThetaChain_spec D
  have hM : Nat.Coprime (q0 D) (Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D) := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hm, Nat.gcd_one_left]
  have hdvd : D.host.QS * D.host.q * D.host.d ∣ Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D :=
    Dvd.dvd.mul_left dvd_rfl _
  exact Nat.Coprime.mul_right (hM.coprime_dvd_right hdvd) ((Nat.Prime.coprime_iff_not_dvd hp).2 hn)

theorem places_prime_to_level : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ w ∈ ch.G.pl.W0,
    ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ => ?_⟩⟩
  intro w hw
  classical
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
  have hunder := ch.G.pl.under_w hv

  have lift : ∀ n : ℕ, ((n : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → ((n : ℕ) : 𝓞 D.host.E) ∈ (ch.G.pl.w v).asIdeal := by
    intro n hn
    rw [← hunder] at hn
    have := Ideal.mem_comap.1 hn
    simpa using this
  obtain ⟨p, hp, hcop⟩ : ∃ p : ℕ, ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∧
      Nat.Coprime p (D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK) := by
    rcases ch.G.pl.mem_S0_of_sum_eq.1 hv with rfl | h1
    · exact ⟨q0 D, ch.G.pl.basePlace_over_qZero, leastSplitAuxiliaryPrime_coprime_host_invariants D⟩
    · rcases (S1_mem_OmF D).1 h1 with h | h | h | h
      · exact ⟨_, h, coprime_level hS.size (D.host.g_prime 0) (D.host.g_level 0)⟩
      · exact ⟨_, h, coprime_level hS.size (D.host.g_prime 1) (D.host.g_level 1)⟩
      · exact ⟨_, h, coprime_level hS.size D.host.pde_prime D.host.pde_level.1⟩
      · exact ⟨_, h, coprime_level hS.size D.host.pde'_prime D.host.pde_level.2⟩
  exact not_both_mem (ch.G.pl.w v).isPrime hcop (lift p hp)

end GlobalTheory.PlacesPrime
end

