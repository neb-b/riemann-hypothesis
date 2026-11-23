module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0660
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0661
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0656
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0096
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0063
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalMeasuresOrthogonalSumAlmostAllPlaces
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0494
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0025
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0086
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.DerivSub
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0563
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0349
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0372
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentInduction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0583
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0351
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0353
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0281

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeTwistedSumPeriodic
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

variable {D : D7} {ρ p : ℕ}

theorem rt_add_periodic (ξ ξ' : Matrix (Fin ρ) (Fin p) D.host.E) :
    rt (ξ + ξ') = (rt ξ + rt ξ' : Mx D ρ p) := by
  ext i j
  simp [rt, Matrix.map_apply, Matrix.add_apply, map_add (f := _)]

theorem dsum_add_rt (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ)
    (Φ : Mx D ρ p → ℂ) (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (x y : Mx D ρ p) :
    dsum ψ b₀ Φ x (y + rt ξ) = conj (chv ψ b₀ x (rt ξ)) * dsum ψ b₀ Φ x y := by
  obtain ⟨-, h2, h3, -, -, -⟩ := _root_.GlobalTheory.CompanionTheory.FJE.chv_facts (D := D) (ρ := ρ) (p := p) ψ hψ b₀
  unfold dsum
  rw [← tsum_mul_left, ← (Equiv.addRight ξ).tsum_eq
    (fun η : Matrix (Fin ρ) (Fin p) D.host.E =>
      conj (chv ψ b₀ x (rt ξ)) * (chv ψ b₀ x (rt η) * Φ (rt η + y)))]
  refine tsum_congr fun η => ?_
  have hn : conj (chv ψ b₀ x (rt ξ)) * chv ψ b₀ x (rt ξ) = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h3]
    simp
  simp only [Equiv.coe_addRight]
  rw [rt_add_periodic, h2, show rt η + rt ξ + y = rt η + (y + rt ξ) by abel]
  linear_combination (-(chv ψ b₀ x (rt η) * Φ (rt η + (y + rt ξ)))) * hn

theorem dsum_add_rt_left (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ)
    (Φ : Mx D ρ p → ℂ) (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (x y : Mx D ρ p) :
    dsum ψ b₀ Φ (x + rt ξ) y = dsum ψ b₀ Φ x y := by
  obtain ⟨h1, -, -, -, h5, -⟩ := _root_.GlobalTheory.CompanionTheory.FJE.chv_facts (D := D) (ρ := ρ) (p := p) ψ hψ b₀
  unfold dsum
  refine tsum_congr fun η => ?_
  rw [h1, h5, mul_one]

theorem ap_periodic (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ)
    (Φ φ : Mx D ρ p → ℂ) (ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E)
    (v : Mx D ρ p × Mx D ρ p) :
    Ap ψ b₀ Φ φ (v + (rt ξ₁, rt ξ₂)) = Ap ψ b₀ Φ φ v := by
  obtain ⟨-, -, h3, -, -, -⟩ := _root_.GlobalTheory.CompanionTheory.FJE.chv_facts (D := D) (ρ := ρ) (p := p) ψ hψ b₀
  obtain ⟨y, x⟩ := v
  show dsum ψ b₀ Φ (x + rt ξ₂) (y + rt ξ₁) * conj (dsum ψ b₀ φ (x + rt ξ₂) (y + rt ξ₁)) =
    dsum ψ b₀ Φ x y * conj (dsum ψ b₀ φ x y)
  have hn : conj (chv ψ b₀ x (rt ξ₁)) * chv ψ b₀ x (rt ξ₁) = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h3]
    simp
  rw [dsum_add_rt_left ψ hψ, dsum_add_rt_left ψ hψ, dsum_add_rt ψ hψ, dsum_add_rt ψ hψ, map_mul,
    Complex.conj_conj]
  linear_combination (dsum ψ b₀ Φ x y * conj (dsum ψ b₀ φ x y)) * hn

theorem ap_periodic_all : ∀ {D : D7} {ρ p : ℕ} (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
    ∀ (b₀ : HermE D ρ) (Φ φ : Mx D ρ p → ℂ) (ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E)
      (v : Mx D ρ p × Mx D ρ p),
      GlobalTheory.CompanionTheory.FJE.Ap ψ b₀ Φ φ (v + (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂)) = GlobalTheory.CompanionTheory.FJE.Ap ψ b₀ Φ φ v :=
  fun ψ hψ b₀ Φ φ ξ₁ ξ₂ v => ap_periodic ψ hψ b₀ Φ φ ξ₁ ξ₂ v

end GlobalTheory.CompanionTheory.FJE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalVolumeUnramifiedAlmostAll
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageGoodFree

theorem stage_good_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ n)) m, μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFibFree (Fv F v) σ J n μ ν m → ∀ h : HA (Fv F v) σ (blockOne (algebraMap F E t) J), m (hermOf (Fv F v) σ T hT) {X | actW (Fv F v) σ _ h (consTup X) ∈ latV b v} = (latV b v).indicator (fun _ => m (hermOf (Fv F v) σ T hT) (latV b v)) (actW (Fv F v) σ _ h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n T hT d b
  obtain ⟨hdet, hherm, -, -⟩ := BlockAlg.block_alg F E σ hCM M J t
  have hND : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨hherm hJ.1, by
      rw [hdet]
      exact mul_ne_zero (by simpa using ht) hJ.2⟩
  filter_upwards [GoodTrans.good_trans F E σ hCM (M + 1) _ hND t ht d b,
    (LatRat.latV_rational F E σ hCM d b n M).2.2, (LatRat.latV_rational F E σ hCM d b 0 M).2.2]
    with v hv hv1 hv0
  intro μ ν m hμ hν hm h
  have hLoc := LocFv.isLocR_Fv F v
  obtain ⟨i1, i2, i3, i4, -⟩ := id hLoc
  have : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨-, -, -, -, -, -, -, hBorel, -, -⟩ := TopK.topTens_props F E σ hCM (Fv F v)
  have := hBorel n M
  have hOpen := ((_root_.GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hCM d b n M).2.2.2.1 v).2
  obtain ⟨-, -, -, -, -, hact⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hCM (M + 1) _ hND (Fv F v)
  obtain ⟨-, -, -, -, -, hactJ⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hCM M J hJ (Fv F v)
  obtain ⟨-, hone, hmul, hgram⟩ := hact 1
  by_cases he : actW (Fv F v) σ _ h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) ∈ latV b v
  · rw [Set.indicator_of_mem he]
    have he0 : (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → Fv F v ⊗[F] E)) ∈ latV b v := by
      have h0 := (hv0 (fun a : Fin 0 => a.elim0)).2 (fun a => a.elim0)
      have hc : consTup (fun a : Fin 0 => a.elim0) =
          (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → Fv F v ⊗[F] E)) := by
        funext a
        exact Fin.cases rfl (fun j => j.elim0) a
      rwa [hc] at h0
    obtain ⟨k, hk, hkl⟩ := hv _ _ he0 he (StageGood.gram_first (Fv F v) σ J t) (hgram h _)
    obtain ⟨ι, -, -, hrange, -, hcons⟩ := StabFirst.stab_first F E σ hCM M J hJ t ht (Fv F v)
    have hg : actW (Fv F v) σ _ (k⁻¹ * h) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) =
        (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) := by
      rw [hmul, ← hk, ← hmul, inv_mul_cancel, hone]
    obtain ⟨u, hu⟩ := (hrange _).2 hg
    have hh : h = k * ι u := by rw [hu]; group
    have hset : {X : Fin n → Fin M → Fv F v ⊗[F] E | actW (Fv F v) σ _ h (consTup X) ∈ latV b v} =
        actW (Fv F v) σ J u ⁻¹' latV b v := by
      ext X
      rw [Set.mem_ofPred_eq, Set.mem_preimage, hh]
      have := (hact (n + 1)).2.2.1 k (ι u) (consTup X)
      rw [this, hkl, hcons, hv1]
    have hcont : Continuous (actW (Fv F v) σ J u : (Fin n → Fin M → Fv F v ⊗[F] E) → _) :=
      (hactJ n).1.comp (Continuous.prodMk continuous_const continuous_id)
    rw [hset, ← Measure.map_apply hcont.measurable hOpen.measurableSet,
      _root_.GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreInv.map_actW_fibre_free F E σ hCM M J hJ (Fv F v) hLoc n μ ν m hμ hν hm u]
  · rw [Set.indicator_of_notMem he]
    have hempty : {X : Fin n → Fin M → Fv F v ⊗[F] E | actW (Fv F v) σ _ h (consTup X) ∈ latV b v} = ∅ := by
      ext X
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hX => he (StageGood.first_mem b v σ _ h X hX)
    rw [hempty, measure_empty]

end GlobalTheory.CompanionTheory.SW.StageGoodFree
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixPreservesIntegersAlmostAll
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.MatInt

theorem algebraMap_mem_integers_of_not_mem_support (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (a : F) (h : v ∉ HeightOneSpectrum.Support (𝓞 F) a) :
    algebraMap F (Fv F v) a ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have e : Valued.v (algebraMap F (Fv F v) a) = v.valuation F a :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a
  rw [e]
  simpa [HeightOneSpectrum.Support] using h

theorem mulVec_mem_integers (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι]
    (v : HeightOneSpectrum (𝓞 F)) (B : Matrix ι ι (Fv F v)) (y : ι → Fv F v)
    (hB : ∀ i j, B i j ∈ v.adicCompletionIntegers F)
    (hy : ∀ i, y i ∈ v.adicCompletionIntegers F) (i : ι) :
    B.mulVec y i ∈ v.adicCompletionIntegers F := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => mul_mem (hB i j) (hy j)

theorem exists_finset_mulVec_integral_iff : ∀ (F : Type) [Field F] [NumberField F] (ι : Type)
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 →
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ v, v ∉ T → ∀ x : ι → Fv F v,
      (∀ i, (A.map (algebraMap F (Fv F v))).mulVec x i ∈ v.adicCompletionIntegers F) ↔
        ∀ i, x i ∈ v.adicCompletionIntegers F := by
  intro F _ _ ι _ _ A hA
  classical
  have hfin : ∀ a : F, (HeightOneSpectrum.Support (𝓞 F) a).Finite :=
    HeightOneSpectrum.Support.finite (𝓞 F)
  refine ⟨Finset.univ.biUnion fun p : ι × ι =>
    (hfin (A p.1 p.2)).toFinset ∪ (hfin (A⁻¹ p.1 p.2)).toFinset, fun v hv x => ?_⟩
  have hout : ∀ i j, v ∉ HeightOneSpectrum.Support (𝓞 F) (A i j) ∧
      v ∉ HeightOneSpectrum.Support (𝓞 F) (A⁻¹ i j) := by
    intro i j
    constructor
    · intro h
      exact hv (Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _,
        Finset.mem_union_left _ ((hfin _).mem_toFinset.2 h)⟩)
    · intro h
      exact hv (Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _,
        Finset.mem_union_right _ ((hfin _).mem_toFinset.2 h)⟩)
  have hinv : (A⁻¹.map (algebraMap F (Fv F v))) * (A.map (algebraMap F (Fv F v))) = 1 := by
    have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hA
    have h1 := congrArg (fun M : Matrix ι ι F => M.map (algebraMap F (Fv F v)))
      (Matrix.nonsing_inv_mul A hu)
    simpa [Matrix.map_mul] using h1
  constructor
  · intro h i
    have e : (A⁻¹.map (algebraMap F (Fv F v))).mulVec
        ((A.map (algebraMap F (Fv F v))).mulVec x) = x := by
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    rw [← e]
    exact mulVec_mem_integers F ι v _ _
      (fun i j => algebraMap_mem_integers_of_not_mem_support F v _ (hout i j).2) h i
  · intro h i
    exact mulVec_mem_integers F ι v _ _
      (fun i j => algebraMap_mem_integers_of_not_mem_support F v _ (hout i j).1) h i

end GlobalTheory.CompanionTheory.MatInt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NuPairOfDerivativesJacquet
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace GlobalTheory.CompanionTheory.BZNuPairAsm

section Lemmas

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dualCl_degree (x : IrrGL (k := k)) : (dualCl x).1 = x.1 := by
  unfold dualCl
  split <;> rfl

theorem dual_shift (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (s q : IrrGL (k := k)) (j : ℕ) (h : q = (dualCl s).nu (j : ℂ)) :
    dualCl (q.nu (-(((j : ℂ) + 1) / 2))) = (s.nu (-(((j : ℂ) + 1) / 2))).nu 1 := by
  subst h
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_nu hA, GlobalTheory.CompanionTheory.ZcDual.dualCl_nu hA, GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl hA,
    IrrGL.nu_nu, IrrGL.nu_nu]
  congr 1
  ring

theorem nontrivial_of_irreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (hi : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  apply hi.bot_ne_top
  ext v
  simp [Subsingleton.elim v 0]

theorem continuous_inv (ψ : AddChar k Circle) (hc : Continuous ψ) : Continuous (ψ⁻¹ : AddChar k Circle) := by
  have e : (⇑(ψ⁻¹ : AddChar k Circle)) = fun a => ψ (-a) := by
    funext a
    exact AddChar.inv_apply ψ a
  rw [e]
  exact hc.comp continuous_neg

theorem jm_swap (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hJT : JmTheta k) {N : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (ω : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth ω) (hi : ω.IsIrreducible)
    (a b c : IrrGL (k := k)) (hc : dualCl a = c) (hd : ∑ i, (![a, b] i).1 = N) (h : 1 ≤ jm ![a, b] hd (contra ω)) :
    ∃ hd' : ∑ i, (![dualCl b, c] i).1 = N, 1 ≤ jm ![dualCl b, c] hd' ω := by
  have hfl : HasFiniteLength ω := hasFiniteLength_of_isIrreducible hi
  have hd2 : ∑ i, (![dualCl b, dualCl a] i).1 = N := by
    simpa [Fin.sum_univ_two, dualCl_degree, add_comm] using hd
  have key := hJT N V ω hs hfl a b hd hd2
  have e := GlobalTheory.CompanionTheory.ThetaW.comp_thetaW_equiv_contra (GlobalTheory.CompanionTheory.GKLocalProof.gkLocal hA) N ω hs hi
  rw [GlobalTheory.CompanionTheory.JacquetCongr.jm_congr_of_equiv ![a, b] hd _ _ e] at key
  subst hc
  exact ⟨hd2, key ▸ h⟩

end Lemmas

theorem nuPair : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.DerivJac k → GlobalTheory.BZSeg.JmTheta k → GlobalTheory.BZSeg.DerivSub k →
    GlobalTheory.BZSeg.NuPair k := by
  intro k _ _ _ _ hA hDJ hJT hDS N V _ _ ω hs hi hng
  obtain ⟨ψ, hc, h1⟩ := GlobalTheory.LocGL.exists_continuous_addChar_ne_one k
  have hn : Nontrivial V := nontrivial_of_irreducible ω hi
  have hg : ¬ IsGenericFor ψ ω := fun h => hng ((isGeneric_iff_isGenericFor hc h1 ω).2 h)
  obtain ⟨m, hm0, hmN, hnt, hlow⟩ := GlobalTheory.CompanionTheory.BZCuspPair.exists_highest ψ hc h1 N ω hs hn hg
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, N = n + 1 + j + 1 := ⟨N - n - 2, by omega⟩
  have hfl : HasFiniteLength ω := hasFiniteLength_of_isIrreducible hi
  have hD := GlobalTheory.CompanionTheory.BZCuspPair.deriv_nontrivial ψ n j ω hnt
  obtain ⟨S, f, hf⟩ := hDS ψ n j V ω hs hfl hD
  have hsq : IsSubquotient S.ρ (GlobalTheory.BZMir.deriv k ψ j ω) := IsSubquotient.of_injective f hf
  obtain ⟨β, hdβ, hβ, hjm⟩ := hDJ ψ hc h1 n j V ω hs hfl S hsq
  have hv := GlobalTheory.CompanionTheory.BZCuspPair.phi_vanish ψ hc h1 n j ω hs hlow
  have hs' : IsSmooth (contra ω) := isSmooth_contra _
  have hi' : (contra ω).IsIrreducible := GlobalTheory.CompanionTheory.ZcDual.isIrreducible_contra hA ω hs hi
  have hfl' : HasFiniteLength (contra ω) := hasFiniteLength_of_isIrreducible hi'
  let B : V →ₗ[ℂ] smoothPart ω.dual →ₗ[ℂ] ℂ := ((smoothPart ω.dual).subtype).flip
  have hB : ∀ g v v', B (ω g v) (contra ω g v') = B v v' := by
    intro g v v'
    change (ω.dual g (v' : Module.Dual ℂ V)) (ω g v) = (v' : Module.Dual ℂ V) v
    rw [Representation.dual_apply]
    show (v' : Module.Dual ℂ V) (ω g⁻¹ (ω g v)) = (v' : Module.Dual ℂ V) v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hBn : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0 := by
    intro v hv0
    obtain ⟨l, hl⟩ := GlobalTheory.ContraRefl.exists_smooth_form_ne hs
      (fun U a => GlobalTheory.ThetaLiftGL.compactOpen_basis k (n + 1 + j + 1) U a) hv0
    exact ⟨l, hl⟩
  obtain ⟨B', hB', hB'n⟩ := GlobalTheory.CompanionTheory.BZCuspPair.pair_deriv ψ hc h1 n j ω (contra ω) hs hs' B hB hBn hv
  have hint : ∀ g w, f (S.ρ g w) = GlobalTheory.BZMir.deriv k ψ j ω g (f w) := fun g w =>
    Representation.IntertwiningMap.isIntertwining _ _ f g w
  have hSn : Nontrivial S.V := nontrivial_of_irreducible S.ρ S.irr
  obtain ⟨Q, hQ, hQeq⟩ := GlobalTheory.CompanionTheory.DualQuot.exists_subquotient_dual_nu k (n + 1) j _ S
    (GlobalTheory.BZMir.deriv k ψ⁻¹ j (contra ω)) (GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_deriv ψ⁻¹ j hs')
    (B'.comp f.toLinearMap)
    (by
      intro g w w'
      change B' (f (S.ρ g w)) _ = _ * B' (f w) w'
      rw [hint]
      exact hB' g (f w) w')
    (by
      intro h0
      obtain ⟨w, hw⟩ := exists_ne (0 : S.V)
      have hfw : f w ≠ 0 := fun e => hw (hf (e.trans (map_zero f).symm))
      obtain ⟨w', hw'⟩ := hB'n (f w) hfw
      apply hw'
      have := LinearMap.congr_fun (LinearMap.congr_fun h0 w) w'
      exact this)
  obtain ⟨β₂, hd₂, hβ₂, hjm₂⟩ := hDJ ψ⁻¹ (continuous_inv ψ hc) (inv_ne_one.mpr h1) n j _ (contra ω) hs' hfl' Q hQ
  obtain ⟨hd₃, hjm₃⟩ := jm_swap hA hJT ω hs hi _ β₂ _ rfl hd₂ hjm₂
  have hshift := dual_shift hA (IrrGL.of S.ρ S.smooth S.irr) (IrrGL.of Q.ρ Q.smooth Q.irr) j hQeq
  have hd' : ∑ a, (![dualCl β₂, ((IrrGL.of S.ρ S.smooth S.irr).nu (-(((j : ℂ) + 1) / 2))).nu 1] a).1 =
      n + 1 + j + 1 := by
    rw [← hshift]
    exact hd₃
  refine ⟨(IrrGL.of S.ρ S.smooth S.irr).nu (-(((j : ℂ) + 1) / 2)), β, dualCl β₂, hdβ, hd', ?_, ?_, ?_, hjm, ?_⟩
  · rw [IrrGL.nu_fst]
    exact Nat.succ_pos n
  · rw [hβ]
    exact Nat.succ_pos j
  · rw [dualCl_degree, hβ₂, hβ]
  · rw [← GlobalTheory.CompanionTheory.SegFine.jm_congr (by rw [hshift]) hd₃ hd' ω]
    exact hjm₃

end GlobalTheory.CompanionTheory.BZNuPairAsm

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneMajorant
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

theorem exists_eval_points {X : Type*} (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ W] :
    ∃ (N : ℕ) (x : Fin N → X) (f : Fin N → X → ℂ), (∀ i, f i ∈ W) ∧
      ∀ w ∈ W, ∀ y, w y = ∑ i, w (x i) * f i y := by
  classical
  let ev : X → Module.Dual ℂ W := fun x => (LinearMap.proj x).comp W.subtype
  have hfg : (Submodule.span ℂ (Set.range ev)).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  have hch : ∀ φ : s, ∃ x, ev x = φ.1 := fun φ => hs φ.2
  choose pt hpt using hch
  let e := s.equivFin
  let x : Fin s.card → X := fun i => pt (e.symm i)
  let T : W →ₗ[ℂ] (Fin s.card → ℂ) := LinearMap.pi fun i => ev (x i)
  have hT : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    have hle : Submodule.span ℂ (s : Set (Module.Dual ℂ W)) ≤ LinearMap.ker (Module.Dual.eval ℂ W w) := by
      rw [Submodule.span_le]
      intro φ hφ
      have h1 : T w (e ⟨φ, hφ⟩) = 0 := by rw [hw]; rfl
      have h2 : ev (x (e ⟨φ, hφ⟩)) w = 0 := h1
      have h3 : ev (x (e ⟨φ, hφ⟩)) = φ := by
        show ev (pt (e.symm (e ⟨φ, hφ⟩))) = φ
        rw [Equiv.symm_apply_apply, hpt]
      rw [h3] at h2
      exact h2
    refine Subtype.ext (funext fun y => ?_)
    have hy : ev y ∈ Submodule.span ℂ (s : Set (Module.Dual ℂ W)) :=
      hspan ▸ Submodule.subset_span ⟨y, rfl⟩
    exact hle hy
  obtain ⟨L, hL⟩ := T.exists_leftInverse_of_injective hT
  refine ⟨s.card, x, fun i => (L (Pi.single i 1)).1, fun i => (L _).2, ?_⟩
  intro w hw y
  have h1 : L (T ⟨w, hw⟩) = ⟨w, hw⟩ := LinearMap.congr_fun hL _
  have h2 : T ⟨w, hw⟩ = ∑ i, w (x i) • (Pi.single i (1 : ℂ) : Fin s.card → ℂ) := by
    ext j
    simp [T, ev, Finset.sum_apply, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h2, map_sum] at h1
  have h3 := congrArg (fun v : W => v.1 y) h1
  simp only [map_smul] at h3
  simpa [Submodule.coe_sum, Finset.sum_apply] using h3.symm

theorem rank_one_majorant_of_parts : WeilCont → WeilKFin → OrbitMaj → IwaCpt → FockTranslateSchwartzMajorant := by
  intro hCont hFin hOrb hIwa D n ψ hψ χ hχ hRes θ hθ μ 𝓕 hμ ω hω l hl hl0 Φ hΦ C hC
  have hcart : ∀ τ, IsCartanInv (gramAt D (V1 D) τ)
      ((fun _ => 1 : D.what₂.Tau → Matrix (Fin (V1 D).rank) (Fin (V1 D).rank) ℂ) τ) :=
    fun τ => GlobalTheory.AdForm.VacStd.cartan_of_gram (GlobalTheory.AdForm.VacStd.gram_of_eq _ _ 1 rfl) τ
  obtain ⟨W, hWfd, hWle, hWK⟩ :=
    hFin D n (V1 D) ψ hψ χ hχ hRes θ hθ μ 𝓕 hμ ω hω l hl (fun _ => 1) hcart Φ hΦ
  haveI := hWfd
  obtain ⟨N, x, f, hfW, hrep⟩ := exists_eval_points W
  have hcont := hCont D n (V1 D) ψ hψ χ hχ hRes θ hθ μ 𝓕 hμ ω hω Φ
  have hB : ∀ i, ∃ B : ℝ, 0 ≤ B ∧ ∀ k ∈ K D n, ‖(ω k Φ).1 (x i)‖ ≤ B := by
    intro i
    have hc : Continuous fun k : G D n => (ω k Φ).1 (x i) :=
      hcont.comp (continuous_id.prodMk continuous_const)
    obtain ⟨B, hB⟩ := HeightExists.isCompact_K.exists_bound_of_continuousOn hc.continuousOn
    exact ⟨max B 0, le_max_right _ _, fun k hk => (hB k hk).trans (le_max_left _ _)⟩
  choose B hB0 hB using hB
  obtain ⟨A₁, A₂, R, hA₁, hA₂, hiwa⟩ := hIwa D n C hC
  have hM := fun i => hOrb D n θ hθ l hl0 (f i) (hWle (hfW i)) A₁ A₂ hA₁ hA₂
  choose M hMs hMpos hMle using hM
  have hc0 : 0 ≤ (max R 0) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (le_max_right _ _) _
  refine ⟨(((max R 0) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) • ∑ i, (B i : ℂ) • M i,
    Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hMs i)), ?_⟩
  intro h hh y
  obtain ⟨m, t, k, a, b, hk, rfl, hm, ht, ha1, ha2, hR⟩ := hiwa h hh
  set c : ℝ := (max R 0) ^ ((1 : ℝ) / 2) with hc
  have e1 : ‖(ω (m * t * k) Φ).1 y‖ =
      (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ ((1 : ℝ) / 2) * ‖(ω k Φ).1 (HMul.hMul y a.1 : Mx D (V1 D).rank n)‖ := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hω.levi m a hm, hω.unip t b ht,
      norm_mul, norm_mul, norm_mul, hψ.2.1, norm_npow (hom_pos _ _)]
    have hre : (((V1 D).rank : ℂ) / 2).re = (1 : ℝ) / 2 := by
      show ((((1 : ℕ) : ℂ)) / 2).re = (1 : ℝ) / 2
      norm_num
    rw [hre, Circle.norm_coe, one_mul, one_mul]
  have e2 : ‖(ω k Φ).1 (HMul.hMul y a.1 : Mx D (V1 D).rank n)‖ ≤ ∑ i, B i * ‖M i y‖ := by
    rw [hrep _ (hWK k hk)]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul]
    exact mul_le_mul (hB i k hk) (hMle i a ha1 ha2 y) (norm_nonneg _) (hB0 i)
  have e3 : (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ ((1 : ℝ) / 2) ≤ c :=
    Real.rpow_le_rpow (NNReal.coe_nonneg _) (hR.trans (le_max_left _ _)) (by norm_num)
  have e4 : ∀ i, M i y = ((‖M i y‖ : ℝ) : ℂ) := by
    intro i
    have h1 := hMpos i y
    apply Complex.ext
    · simp only [Complex.ofReal_re]
      rw [show M i y = (((M i y).re : ℝ) : ℂ) from Complex.ext (by simp) (by simp [h1.2])]
      simp [abs_of_nonneg h1.1]
    · simp [h1.2]
  have e5 : ‖((((c : ℝ) : ℂ) • ∑ i, (B i : ℂ) • M i) : Mx D (V1 D).rank n → ℂ) y‖ = c * ∑ i, B i * ‖M i y‖ := by
    have h1 : ((((c : ℝ) : ℂ) • ∑ i, (B i : ℂ) • M i) : Mx D (V1 D).rank n → ℂ) y =
        ((c * ∑ i, B i * ‖M i y‖ : ℝ) : ℂ) := by
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      push_cast
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [← e4 i]
    rw [h1, Complex.norm_real, Real.norm_of_nonneg]
    exact mul_nonneg hc0 (Finset.sum_nonneg fun i _ => mul_nonneg (hB0 i) (norm_nonneg _))
  rw [e1, e5]
  exact mul_le_mul e3 e2 (norm_nonneg _) hc0

end GlobalTheory.CompanionTheory.ThTot

end
end

