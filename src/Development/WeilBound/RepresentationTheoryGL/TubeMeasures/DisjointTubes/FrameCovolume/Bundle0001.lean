module

public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.TubeSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1978
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0189
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0002
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticGroupConjRationalPrincipalCongruence
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0133
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.HostTorsionOrderLe
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.FrameCovolume.MeasTransl
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace MainStatements.Tam.T2

theorem meas_transl (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ))
    (hV : V.SigOK) (hA : IsFrames V A) (hrp : IsRealPart V θ A rp) (μ : Measure (GA D V)) [μ.IsMulLeftInvariant]
    (g : GA D V) (hg : g ∈ GfC V) (S : Set (GA D V)) (B : Set (∀ ρ, Upq V ρ)) :
    μ {y | g⁻¹ * y ∈ S ∧ rp y ∈ B} = μ {z | z ∈ S ∧ rp z ∈ B} := by
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have h1 : rp g = 1 := GlobalTheory.CovTop.VolBox.rp_eq_one V θ A rp hV hA hrp g hg
  rw [← measure_preimage_mul μ g⁻¹ {z | z ∈ S ∧ rp z ∈ B}]
  congr 1
  ext y
  show g⁻¹ * y ∈ S ∧ rp y ∈ B ↔ g⁻¹ * y ∈ S ∧ rp (g⁻¹ * y) ∈ B
  rw [map_mul rp, map_inv rp, h1, inv_one, one_mul]

theorem meas_low (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ))
    (hV : V.SigOK) (hA : IsFrames V A) (hrp : IsRealPart V θ A rp) (μ : Measure (GA D V)) [μ.IsMulLeftInvariant]
    (hidx : IdxSt) (M : ℕ) (hM : 1 ≤ M) (B : Set (∀ ρ, Upq V ρ)) :
    μ {h | h ∈ KM V 1 ∧ rp h ∈ B} ≤ ((M : ℝ≥0∞) ^ (2 * D.R.f * V.rank ^ 2)) * μ {h | h ∈ KM V M ∧ rp h ∈ B} := by
  classical
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have hfd : fdeg D.host.E = D.R.f := (_root_.GlobalTheory.RankHostFacts.main D).2
  obtain ⟨S, hScard, hS⟩ := hidx D.host.E V.rank M (-(V.gram)ᵀ) (GlobalTheory.Member.latC V) hM (_root_.GlobalTheory.Member.selfDualLat_neg_gram_transpose D V)
  set Q : Set (GA D V) := {h | h ∈ KM V M ∧ rp h ∈ B} with hQ
  let P : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E) → Set (GA D V) := fun s => {h | h ∈ KM V 1 ∧ rp h ∈ B ∧
    ∃ k, IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) M k ∧
      ((finHom V h).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) = s * k}
  have hcov : {h | h ∈ KM V 1 ∧ rp h ∈ B} ⊆ ⋃ s ∈ S, P s := by
    intro h ⟨h1, hB⟩
    obtain ⟨s, hsS, -, k, hk, e⟩ := hS _ h1
    exact Set.mem_iUnion₂.2 ⟨s, hsS, h1, hB, k, hk, e⟩
  have hP : ∀ s ∈ S, μ (P s) ≤ μ Q := by
    intro s hsS
    rcases (P s).eq_empty_or_nonempty with he | ⟨z, hz1, hzB, kz, hkz, hzs⟩
    · rw [he, measure_empty]; exact bot_le
    obtain ⟨w, hw, hwz⟩ := GlobalTheory.SplitDec.exists_finPart V z
    have hw1 : rp w = 1 := GlobalTheory.CovTop.VolBox.rp_eq_one V θ A rp hV hA hrp w hw
    have hsu : IsUnit s.det := by
      have hu : IsUnit ((finHom V z).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)).det := Matrix.isUnits_det_units _
      rw [hzs, Matrix.det_mul] at hu
      exact isUnit_of_mul_isUnit_left hu
    refine (measure_mono fun x hx => ?_).trans (measure_preimage_mul μ w⁻¹ Q).le
    obtain ⟨-, hxB, kx, hkx, hxs⟩ := hx
    refine ⟨?_, ?_⟩
    · show IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) M
        ((finHom V (w⁻¹ * x)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E))
      have e1 : ((finHom V (w⁻¹ * x)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) = kz⁻¹ * kx := by
        rw [map_mul, map_inv, ← hwz, Units.val_mul, Matrix.coe_units_inv, hzs, hxs, Matrix.mul_inv_rev,
          Matrix.mul_assoc, ← Matrix.mul_assoc s⁻¹, Matrix.nonsing_inv_mul _ hsu, Matrix.one_mul]
      rw [e1]
      exact isKM_mul (isKM_inv hkz) hkx
    · show rp (w⁻¹ * x) ∈ B
      rw [map_mul, map_inv, hw1, inv_one, one_mul]
      exact hxB
  calc μ {h | h ∈ KM V 1 ∧ rp h ∈ B} ≤ μ (⋃ s ∈ S, P s) := measure_mono hcov
    _ ≤ ∑ s ∈ S, μ (P s) := measure_biUnion_finset_le S P
    _ ≤ ∑ s ∈ S, μ Q := Finset.sum_le_sum hP
    _ = (S.card : ℝ≥0∞) * μ Q := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((M : ℝ≥0∞) ^ (2 * D.R.f * V.rank ^ 2)) * μ Q := by
      gcongr
      rw [← hfd]
      exact_mod_cast hScard

end MainStatements.Tam.T2
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.FrameCovolume.TubeDisj
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace MainStatements.Tam.T2

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem tube_disj (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ))
    (Ψ : Finset (D.host.E →+* ℂ)) (Gm : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (σ : D.what₂.Tau ≃ Ψ)
    (π : (∀ ρ, Upq V ρ) → realSU Ψ Gm) (M : ℕ) (ι : Type) (X : ι → Data D.host.E V.rank) (g : ι → GA D V)
    (F : ι → Set (realSU Ψ Gm))
    (hM : 3 ≤ M) (hGm : Gm = -(V.gram)ᵀ) (hθ : IsInfFam θ) (hrp : IsRealPart V θ A rp)
    (hσ : ∀ ρ, (σ ρ).1 = tauE D ρ)
    (heq : ∀ (s' : realSU Ψ Gm) (b₀ : ∀ ρ, Upq V ρ), (∀ ρ, UpqT.mat (b₀ ρ) * A ρ =
      A ρ * ((s'.1 (σ ρ) : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ)) → ∀ b, π (b₀ * b) = s' * π b)
    (hF : ∀ k, ∀ γ ∈ inReal Ψ Gm (X k).Γ, ∀ y ∈ F k, γ * y ∈ F k → γ = 1)
    (hdist : ∀ k k', UEquiv (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ)
      (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) M
      ((finHom V (g k)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) ((finHom V (g k')).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) → k = k')
    (hXG : ∀ k, (X k).Gm = -(V.gram)ᵀ)
    (hXΛ : ∀ k, ((X k).Λ : Set (Fin V.rank → D.host.E)) = latOf (maximalRealSubfield D.host.E)
      ((finHom V (g k)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)))
    (hXΓ : ∀ k γ, γ ∈ (X k).Γ ↔ IsUStab (X k).Gm (X k).Λ γ ∧ ∀ x ∈ (X k).Λ, ∃ y ∈ (X k).Λ,
      (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ x - x = M • y) :
    ∀ δ ∈ GQ V, ∀ (k k' : ι) (y : GA D V), ((g k)⁻¹ * y ∈ KM V M ∧ π (rp y) ∈ F k) →
      ((g k')⁻¹ * (δ * y) ∈ KM V M ∧ π (rp (δ * y)) ∈ F k') → δ = 1 ∧ k = k' := by
  intro δ hg k k' y hy hgy
  classical
  obtain ⟨δ0, hδU, hδeq⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hg)
  have hmat : matHom V δ = Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) δ0 := hδeq.symm
  have h1 : (matHom V δ).1 = (δ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) := by rw [hmat]; rfl
  have hinf : ∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) δ = (δ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (tauE D ρ) := by
    intro ρ
    have hinc : ((δ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Ainf D.host.F))).map (θ ρ) =
        (δ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (tauE D ρ) := by
      ext a b
      exact (hθ ρ).1 _
    rw [← hinc, ← GlobalTheory.UnitaryGlue.map_map_inclR (fstA D.host.F), ← h1]; rfl
  have hfin : (finHom V δ).1 = (δ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (Af D.host.F)) := by
    rw [← GlobalTheory.UnitaryGlue.map_map_inclR (sndA D.host.F), ← h1]; rfl
  have hfinv : (finHom V δ⁻¹).1 = ((δ0⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map
      (inclR (Af D.host.F)) := by
    rw [map_inv]
    apply Units.inv_eq_of_mul_eq_one_left
    rw [hfin, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)

  have hU : ((δ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map cc)ᵀ * V.gram * δ0.1 = V.gram := by
    change Formalism.UG.cT _ δ0.1 * V.gram * δ0.1 = V.gram at hδU
    convert hδU using 3
    ext a b
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
    congr 1
  have hmatG : δ0.1ᵀ * -(V.gram)ᵀ * δ0.1.map cc = -(V.gram)ᵀ := by
    have := congrArg (fun A => -Aᵀ) hU
    simpa [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg] using this
  have hherm := GlobalTheory.MsRepsFwd.herm_mulVec _ _ hmatG

  have hmulKM : ∀ a b, a ∈ KM V M → b ∈ KM V M → a * b ∈ KM V M := fun a b ha hb => by
    show IsKM _ _ _ _ ((finHom V (a * b)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E))
    rw [map_mul, Units.val_mul]
    exact GlobalTheory.UCls.isKM_mul ha hb
  have hinvKM : ∀ a, a ∈ KM V M → a⁻¹ ∈ KM V M := fun a ha => by
    show IsKM _ _ _ _ ((finHom V a⁻¹).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E))
    rw [map_inv, Matrix.coe_units_inv]
    exact GlobalTheory.UCls.isKM_inv ha
  have hκ : (g k')⁻¹ * δ * g k ∈ KM V M := by
    have e : (g k')⁻¹ * δ * g k = ((g k')⁻¹ * (δ * y)) * ((g k)⁻¹ * y)⁻¹ := by group
    rw [e]; exact hmulKM _ _ hgy.1 (hinvKM _ hy.1)
  have hκ' : (g k)⁻¹ * δ⁻¹ * g k' ∈ KM V M := by
    have e : (g k)⁻¹ * δ⁻¹ * g k' = ((g k)⁻¹ * y) * ((g k')⁻¹ * (δ * y))⁻¹ := by group
    rw [e]; exact hmulKM _ _ hy.1 (hinvKM _ hgy.1)
  have hUA : IsUA (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (ratM (maximalRealSubfield D.host.E) δ0.1) :=
    _root_.GlobalTheory.RatUnit.isUA_ratM D.host.E V.rank _ δ0.1 (Matrix.isUnits_det_units δ0).ne_zero hherm
  have hratM : ratM (maximalRealSubfield D.host.E) δ0.1 = δ0.1.map (inclR (Af D.host.F)) := rfl
  have hkk : k = k' := hdist k k' ⟨δ0.1, hUA, (finHom V ((g k)⁻¹ * δ⁻¹ * g k')).1, hκ', by
    rw [hratM, ← hfin, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
    congr 2
    group⟩
  cases hkk

  haveI : Nontrivial (Af D.host.F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.host.F)
    exact (Formalism.UG.evalV D.host.F ⟨P, hP.isPrime,
      Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField D.host.F)⟩).toRingHom.domain_nontrivial
  haveI : Nontrivial (Af D.host.F ⊗[D.host.F] D.host.E) :=
    (Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F) (A := Af D.host.F) (B := D.host.E)
      (algebraMap D.host.F D.host.E).injective).nontrivial
  have hinj : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)) :=
    (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)).injective
  have he1 : δ0.1.map (inclR (F := D.host.F) (Af D.host.F)) * (finHom V (g k)).1 =
      (finHom V (g k)).1 * (finHom V ((g k)⁻¹ * δ * g k)).1 := by
    rw [← hfin, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
    congr 2
    group
  have he2 : (δ0⁻¹ : GL (Fin V.rank) D.host.E).1.map (inclR (F := D.host.F) (Af D.host.F)) * (finHom V (g k)).1 =
      (finHom V (g k)).1 * (finHom V ((g k)⁻¹ * δ⁻¹ * g k)).1 := by
    rw [← hfinv, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
    congr 2
    group
  have C1 := GlobalTheory.MsRepsFwd.latOf_congr D.host.F D.host.E V.rank M (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
    (finHom V (g k)).1 (finHom V ((g k)⁻¹ * δ * g k)).1 δ0.1 hinj hκ.2.1 he1
  have C2 := GlobalTheory.MsRepsFwd.latOf_congr D.host.F D.host.E V.rank M (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
    (finHom V (g k)).1 (finHom V ((g k)⁻¹ * δ⁻¹ * g k)).1 (δ0⁻¹ : GL (Fin V.rank) D.host.E).1 hinj hκ'.2.1 he2
  have hmem : ∀ x, x ∈ (X k).Λ ↔ x ∈ GlobalTheory.AdLat.latOf D.host.F (finHom V (g k)).1
      (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
    intro x
    rw [← SetLike.mem_coe, hXΛ k]
  have hcong : ∀ x ∈ (X k).Λ, ∃ y ∈ (X k).Λ, δ0.1 *ᵥ x - x = M • y := by
    intro x hx
    obtain ⟨y, hy, e⟩ := C1 x ((hmem x).1 hx)
    exact ⟨y, (hmem y).2 hy, e⟩
  have hcong' : ∀ x ∈ (X k).Λ, ∃ y ∈ (X k).Λ, (δ0⁻¹ : GL (Fin V.rank) D.host.E).1 *ᵥ x - x = M • y := by
    intro x hx
    obtain ⟨y, hy, e⟩ := C2 x ((hmem x).1 hx)
    exact ⟨y, (hmem y).2 hy, e⟩
  have hstab : ∀ x, x ∈ (X k).Λ ↔ δ0.1 *ᵥ x ∈ (X k).Λ := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, e⟩ := hcong x hx
      rw [show δ0.1 *ᵥ x = x + M • y by rw [← e]; abel]
      exact (X k).Λ.add_mem hx (nsmul_mem hy M)
    · intro hx
      obtain ⟨y, hy, e⟩ := hcong' _ hx
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at e
      rw [show x = δ0.1 *ᵥ x + M • y by rw [← e]; abel]
      exact (X k).Λ.add_mem hx (nsmul_mem hy M)
  have hΓ : δ0 ∈ (X k).Γ := (hXΓ k δ0).2 ⟨⟨by rw [hXG k]; exact hherm, hstab⟩, hcong⟩
  have hd1 : (δ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det = 1 :=
    _root_.GlobalTheory.UnitaryCongruenceDet.det_eq_one D.host.E V.rank M (X k) hM (hXΓ k) δ0 hΓ

  have hmemSU : embGL Ψ V.rank δ0 ∈ realSU Ψ Gm := embGL_mem_realSU Ψ Gm δ0 hd1 (by rw [hGm]; exact hherm)
  have hin : (⟨embGL Ψ V.rank δ0, hmemSU⟩ : realSU Ψ Gm) ∈ inReal Ψ Gm (X k).Γ :=
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨δ0, hΓ, rfl⟩)
  have heqv := heq ⟨embGL Ψ V.rank δ0, hmemSU⟩ (rp δ) (fun ρ => by
    rw [hrp δ ρ, hinf ρ]
    show _ = A ρ * (δ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (σ ρ).1
    rw [hσ ρ]) (rp y)
  have hs1 := hF k _ hin (π (rp y)) hy.2 (by rw [← heqv, ← map_mul]; exact hgy.2)
  have hf : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos; omega
  obtain ⟨ρ₀⟩ : Nonempty D.what₂.Tau := by
    rw [← Fintype.card_pos_iff, D.what₂.card_Tau]; omega
  have hδ1 : δ0 = 1 := by
    have h5 := congrArg (fun s : realSU Ψ Gm => ((s.1 (σ ρ₀) : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ)) hs1
    have h6 : (δ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (σ ρ₀).1 =
        (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (σ ρ₀).1 := by
      rw [Matrix.map_one _ (map_zero _) (map_one _)]
      exact h5
    exact Units.ext (Matrix.map_injective (σ ρ₀).1.injective h6)
  refine ⟨Subtype.ext ?_, rfl⟩
  rw [hδ1, map_one] at hmat
  exact hmat

end MainStatements.Tam.T2
end

