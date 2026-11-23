module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IrreducibleSmoothAdmissibleGL
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0029
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0008
public import ReciprocityTheory.Hypotheses.GalCoh
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.Transport
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ExistsApplyEqOfMemDec
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.Inertia
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0004
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0003
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohTate
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicOpenNeighbourhoodProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult MeasureTheory NumberField Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CuspNbhd

open GlobalTheory.AdelicU

theorem real_mul_level_mem_nhds : ∀ (D : D7) (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ N ∈ 𝓝 (1 : GA D V), {g : GA D V | ∃ r k : GA D V, r ∈ GinfC V ∧ r ∈ N ∧ k ∈ U ∧ k ∈ GfC V ∧ g = r * k} ∈ 𝓝 (1 : GA D V) := by
  intro D V U hU N hN
  have hr : Continuous fun g : GA D V =>
      ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram g) :=
    (continuous_ofInf _ _).comp (continuous_projInf _ _)
  have hk : Continuous fun g : GA D V =>
      ofFin D.sp.cm.sig V.gram (projFin D.sp.cm.sig V.gram g) :=
    (continuous_ofFin _ _).comp (continuous_projFin _ _)
  have h1 : ∀ᶠ g : GA D V in 𝓝 1, ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram g) ∈ N := by
    have := hr.continuousAt (x := (1 : GA D V))
    simp only [ContinuousAt, map_one] at this
    exact this hN
  have h2 : ∀ᶠ g : GA D V in 𝓝 1, ofFin D.sp.cm.sig V.gram (projFin D.sp.cm.sig V.gram g) ∈ U := by
    have := hk.continuousAt (x := (1 : GA D V))
    simp only [ContinuousAt, map_one] at this
    exact this (hU.mem_nhds U.one_mem)
  filter_upwards [h1, h2] with g hg1 hg2
  exact ⟨_, _, mem_infPts.2 (by simp), hg1, hg2, mem_finPts.2 (by simp),
    (ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig V.gram g).symm⟩

end GlobalTheory.CompanionTheory.CuspNbhd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
section
namespace GlobalTheory.CompanionTheory.Published

theorem bernsteinZelevinskyFiniteness : GlobalTheory.Published.BernsteinZelevinskyFiniteness :=
  fun k _ _ _ _ => ⟨_root_.GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible k, _root_.GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k, GlobalTheory.T.parabolic_induction_finite_length k, _root_.GlobalTheory.CompanionTheory.Glob.inductionContragredient k⟩

end GlobalTheory.CompanionTheory.Published
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DualityForAbsGal
section
open CategoryTheory MonoidalCategory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel NumberField IsDedekindDomain Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.Hypotheses₂

attribute [local instance 2000] Rep.hV2

theorem dualityFor_absGal (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (hK : FiniteDimensional ℚ_[p] K) (l : ℕ) [Fact l.Prime] (r : ℕ)
    (χ : (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) →* (ZMod (l ^ r))ˣ)
    (hχ : ∀ (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (ζ : PadicAlgCl p), ζ ^ (l ^ r) = 1 →
      σ ζ = ζ ^ ((χ σ : ZMod (l ^ r)).val))
    (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (rho : Representation (ZMod (l ^ r)) (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) M)
    (hrho : ContAction rho) : ReciprocityTheory.Neutral.Bridge.DualityFor χ rho hrho := by
  obtain ⟨hsep, _, _, hloc, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gcField p K hK
  have hl : (l ^ r : ℕ) ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ r) := ⟨hl⟩
  have : CharZero K := algebraRat.charZero K
  have hn : ((l ^ r : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hl
  obtain ⟨e⟩ := nonempty_addEquiv_galRootsOfUnity (K := K) (Ksep := PadicAlgCl p) hn
  have hD : ∀ (g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (m : ZMod (l ^ r)),
      e.symm ((χ g : ZMod (l ^ r)) * m) =
        (galRootsOfUnity.{0} K (PadicAlgCl p) (l ^ r)).ρ g (e.symm m) := by
    intro g m
    have key : ∀ x : Additive (rootsOfUnity (l ^ r) (PadicAlgCl p)),
        (galRootsOfUnity.{0} K (PadicAlgCl p) (l ^ r)).ρ g x =
          (χ g : ZMod (l ^ r)).val • x := by
      intro x
      rw [galRootsOfUnity_ρ_apply]
      apply Additive.toMul.injective
      rw [toMul_ofMul, toMul_nsmul]
      apply Subtype.ext
      apply Units.ext
      rw [coe_galRootsOfUnityHom_apply, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val]
      refine hχ g _ ?_
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 x.toMul.2, Units.val_one]
    refine Eq.trans ?_ (key _).symm
    refine Eq.trans ?_ (map_nsmul e.symm _ m)
    rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
  exact PositivityTheory.LocalTateOrthogonality.Gcoh.tate_core PositivityTheory.LocalTateOrthogonality.Gcoh.gcRep PositivityTheory.LocalTateOrthogonality.Gcoh.gc0
    PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 (galRootsOfUnity.{0} K (PadicAlgCl p) (l ^ r))
    (localDualityHypotheses hn)
    (fun A _ _ hA => finite_cohomology_galois_top K (PadicAlgCl p) hn A hA 1)
    χ e.symm hD M rho hrho

theorem localTateDuality : ReciprocityTheory.Gal.LocalTateDuality := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ A rho v _ hA hrho
  obtain ⟨p, hp, hpv⟩ := exists_prime_mem_asIdeal v
  haveI : Fact p.Prime := ⟨hp⟩
  have hval : A.valuation ((p : ℕ) : Ω) < 1 := by
    have := (hA ((p : ℕ) : 𝓞 F)).2 hpv
    simpa using this
  obtain ⟨ι, h⟩ := ReciprocityTheory.Neutral.Cmp.exists_compat F A hval
  let E : ReciprocityTheory.Neutral.Cmp.GK F ι ≃ₜ* Dec (F := F) A := ReciprocityTheory.Neutral.Cmp.equiv h
  let χ : Dec (F := F) A →* (ZMod (l ^ r))ˣ := (cycMod F Ω l r).comp (Dec (F := F) A).subtype
  have hχ : ∀ (σ : ReciprocityTheory.Neutral.Cmp.GK F ι) (ζ : PadicAlgCl p), ζ ^ (l ^ r) = 1 →
      σ ζ = ζ ^ (((χ.comp (E : ReciprocityTheory.Neutral.Cmp.GK F ι →* Dec (F := F) A)) σ :
        (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := by
    intro σ ζ hζ
    have e1 := ReciprocityTheory.Neutral.Cmp.cycZ_res (F := F) ι l σ
    have e3 : (χ.comp (E : ReciprocityTheory.Neutral.Cmp.GK F ι →* Dec (F := F) A)) σ =
        Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom
          (cyclotomicCharacter (PadicAlgCl p) l (σ : PadicAlgCl p ≃+* PadicAlgCl p)) := by
      rw [← e1]
      rfl
    rw [e3]
    exact cyclotomicCharacter.spec (L := PadicAlgCl p) l (σ : PadicAlgCl p ≃+* PadicAlgCl p) ζ hζ
  have hD := dualityFor_absGal p (ReciprocityTheory.Neutral.Cmp.Kloc F ι)
    (ReciprocityTheory.Neutral.Cmp.finiteDimensional_Kloc ι) l r
    (χ.comp (E : ReciprocityTheory.Neutral.Cmp.GK F ι →* Dec (F := F) A)) hχ M
    (rho.comp (E : ReciprocityTheory.Neutral.Cmp.GK F ι →* Dec (F := F) A))
    (ReciprocityTheory.Neutral.Bridge.contAction_comp E hrho)
  exact ReciprocityTheory.Neutral.Bridge.DualityFor.of_comp E χ hrho hD

end GlobalTheory.CompanionTheory.Hypotheses₂
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ValueFormula
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Eis
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn GlobalTheory.SiegelFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.WeilU

def HermQ (D : D7) (r : ℕ) : Type :=
  {b : Matrix (Fin r) (Fin r) D.host.E // ∀ i j, D.sp.cm.sig (b j i) = b i j}

variable {D : D7}

end GlobalTheory.CompanionTheory.Hypotheses₂.WeilU

namespace GlobalTheory.CompanionTheory.Hypotheses₂.WeilU

end GlobalTheory.CompanionTheory.Hypotheses₂.WeilU

end
end

