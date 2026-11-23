module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.ColumnData
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0003
public import Formalism.PeriodIntegrals.Bundle0003
public import Formalism.PeriodIntegrals.Bundle0004
public import Formalism.PeriodIntegrals.Bundle0012
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0005
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0008
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.ProductThetaMem
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Bundle0002
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
public import Development.AutomorphicArithmetic.WeightCongruences.IsRootOfIntegral
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkThU
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ThIndep
public import Formalism.LocalToGlobal.Columns.WordFin
public import Formalism.LocalToGlobal.Columns.Bundle0031
public import Formalism.LocalToGlobal.Columns.ChainInst
public import Formalism.LocalToGlobal.Columns.Bundle0010
public import Formalism.LocalToGlobal.KernelLattices.ColInst
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
public import Formalism.LocalToGlobal.Columns.ChainInstY

@[expose] public section

-- bundled from Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseExP
section
noncomputable section
open scoped BigOperators ComplexConjugate Pointwise
open NumberField Formalism.BasicNotions Classical IntermediateField

namespace Formalism.L2.Ker.Cd

open Formalism.MainNotions Formalism.FrobeniusOrbits

section Host

variable {R : Ranks} (H : Host R)

theorem phi_b : H.φ₀ (H.sqd) = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem

theorem phi_conj (φ : H.E →+* ℂ) (x : H.E) : φ (H.conj x) = conj (φ x) :=
  H.conjE_apply φ x

theorem d_pos : 0 < H.d := H.hyp.2.1.pos

theorem bE_sq : H.sqd ^ 2 = -(H.d : H.E) := H.sqd_sq

theorem b_mem_K : H.sqd ∈ H.K := mem_adjoin_simple_self ℚ _

def bK : H.K := ⟨H.sqd, b_mem_K H⟩

theorem finrank_K : Module.finrank ℚ H.K = 2 := by
  have hint : IsIntegral ℚ H.sqd := .of_finite ℚ _
  have hp : minpoly ℚ H.sqd = Polynomial.X ^ 2 + Polynomial.C (H.d : ℚ) := by
    symm
    apply minpoly.eq_of_irreducible_of_monic
    · apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
      · rw [Polynomial.natDegree_X_pow_add_C]
        simp
      · intro x hx
        simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_C] at hx
        have hd : (0 : ℚ) < H.d := by exact_mod_cast d_pos H
        nlinarith [sq_nonneg x]
    · simp [bE_sq H]
    · exact Polynomial.monic_X_pow_add_C _ (by norm_num)
  show Module.finrank ℚ ℚ⟮H.sqd⟯ = 2
  rw [IntermediateField.adjoin.finrank hint, hp, Polynomial.natDegree_X_pow_add_C]

theorem K_induction {p : H.E → Prop} (hb : p (H.sqd)) (hq : ∀ r : ℚ, p (algebraMap ℚ H.E r))
    (hadd : ∀ x y, p x → p y → p (x + y)) (hinv : ∀ x, p x → p x⁻¹) (hmul : ∀ x y, p x → p y → p (x * y))
    (k : H.K) : p (k : H.E) := by
  obtain ⟨k, hk⟩ := k
  show p k
  have hk' : k ∈ IntermediateField.adjoin ℚ {H.sqd} := hk
  clear hk
  induction hk' using IntermediateField.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx]
    exact hb
  | algebraMap r => exact hq r
  | add x y _ _ hx hy => exact hadd x y hx hy
  | inv x _ hx => exact hinv x hx
  | mul x y _ _ hx hy => exact hmul x y hx hy

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  apply H.φ₀.injective
  rw [phi_conj, phi_conj, Complex.conj_conj]

theorem emb_on_K (g : R.GG) (hg : g ∈ R.Psi) (k : H.K) : H.emb g (k : H.E) = H.φ₀ (k : H.E) := by
  have hs : (H.sigmaOf g) H.sqd = H.sqd := by
    rw [H.gal_sqd (H.sigmaOf g)]
    have h1 : H.gal (H.sigmaOf g) = g := by
      simp [Formalism.BasicNotions.Host.sigmaOf]
    have h2 : g.1.2 = 1 := hg
    rw [h1, h2]
    simp
  apply K_induction H (p := fun x => H.emb g x = H.φ₀ x)
  · simp [Formalism.BasicNotions.Host.emb, hs]
  · intro r
    simp [Formalism.BasicNotions.Host.emb]
  · intro x y hx hy
    rw [map_add (f := _), map_add (f := _), hx, hy]
  · intro x hx
    rw [map_inv₀, map_inv₀, hx]
  · intro x y hx hy
    rw [map_mul, map_mul, hx, hy]

theorem phi_nonreal : ∃ k : H.K, (H.φ₀ (k : H.E)).im ≠ 0 := by
  refine ⟨bK H, ?_⟩
  show (H.φ₀ H.sqd).im ≠ 0
  rw [phi_b H]
  have hd : (0 : ℝ) < H.d := by exact_mod_cast d_pos H
  simp [(Real.sqrt_pos.mpr hd).ne']

end Host

section Facts

variable (D : Car)

theorem kQuad : KQuad D := finrank_K D.host

theorem embInj : EmbInj D := fun _ _ h => D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem embOnK : EmbOnK D := fun τ k => emb_on_K D.host _ (D.eTau τ).2 k

theorem phiNonReal : PhiNonReal D := phi_nonreal D.host

end Facts

section Exist

variable {D : Car}

theorem periodExists_of (h2 : KQuad D) (hn : PhiNonReal D) : PeriodExists D :=
  fun cc δ hcc hδ =>
    exists_periodPairOfIdeal D.host.K (D.host.φ₀.comp (algebraMap D.host.K D.host.E)) cc δ h2 hn hcc hδ

end Exist

section Final

variable (D : Car)

theorem periodExists : PeriodExists D := periodExists_of (kQuad D) (phiNonReal D)

end Final

namespace Test

open Formalism.BasicNotions.Examples₂

end Test

end Formalism.L2.Ker.Cd
end
end

-- bundled from Formalism.LocalToGlobal.KernelLattices.ColumnData.Family
section
noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.L2.Ker Classical
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

def TaylorCoeffsInNumberField (D : Car) (e : FamE D) : Prop :=
  ∀ N N' L L', admitted D N N' L L' →
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ CoefIn D (e N N' L L') M

def ThetaMeanBound (D : Car) (T : Tor D) (C : ℝ) (e : FamE D) : Prop :=
  ∀ Lsc : ℝ, Real.log D.host.v + |logDerivativeAtOne D| ≤ Lsc →
    ∀ N N' L L', admitted D N N' L L' →
      ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], DataIn D T M → CoefIn D (e N N' L L') M →
        meanLogNormSq D T L L' M (e N N' L L') ≤ C * (fF D : ℝ) * (N : ℝ) * (N' : ℝ) * Lsc

def ThetaNormConjugateIndependent (D : Car) (T : Tor D) (e : FamE D) : Prop :=
  ∀ N N' L₁ L₁' L₂ L₂', admitted D N N' L₁ L₁' → admitted D N N' L₂ L₂' →
    ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], DataIn D T M →
      CoefIn D (e N N' L₁ L₁') M → CoefIn D (e N N' L₂ L₂') M → ∀ ρ : M →ₐ[ℚ] ℂ,
        normSq D (torConj D T M ρ) (La D (torConj D T M ρ) L₁ L₁') (fnConj D M ρ (e N N' L₁ L₁')) =
          normSq D (torConj D T M ρ) (La D (torConj D T M ρ) L₂ L₂') (fnConj D M ρ (e N N' L₂ L₂'))

def EigenvectorPacketProperties {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (C : ℝ) (χ : IdE D → ℂ) : Prop :=
  TaylorCoeffsInNumberField D (B.eNat χ) ∧ ThetaMeanBound D (tor0 D cc δ) C (B.eNat χ) ∧ ThetaNormConjugateIndependent D (tor0 D cc δ) (B.eNat χ) ∧
    B.EqP χ ∧ (_root_.Formalism.L2.Ker.Cd.TaylorLogMetric.int22 D B.tor (B.eNat χ)) ∧ (_root_.Formalism.L2.Ker.Cd.TaylorLogMetric.mom22 D cc δ (B.eNat χ) ∧ _root_.Formalism.L2.Ker.Cd.TaylorLogMetric.LargerSupportMomentCondition D cc δ (B.eNat χ)) ∧ (_root_.Formalism.L2.Ker.Cd.TaylorLogMetric.str22 D B.tor (B.eNat χ))

def LinkBaseNe : Prop :=
  ∀ (D : Car) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Base D cc δ → δ ≠ 0

theorem lamOf_zero (D : Car) (cc : Ideal (𝓞 D.host.K)) : lamOf D cc 0 = ⊥ := by
  unfold lamOf
  rw [AddSubgroup.closure_eq_bot_iff]
  rintro w ⟨c, -, rfl⟩
  simp

theorem base_linkage_nonempty : LinkBaseNe := by
  intro D cc δ B h0
  subst h0
  have h1 : B.L.ω₁ ∈ B.L.lattice.toAddSubgroup := B.L.ω₁_mem_lattice
  rw [B.lat, lamOf_zero, AddSubgroup.mem_bot] at h1
  have h2 := B.L.indep.ne_zero 0
  exact h2 (by simpa using h1)

end Formalism.L2.Ker.Cd.IntegralLatticeDensity

end
end

-- bundled from Formalism.LocalToGlobal.KernelLattices.ColumnData.GlobTied
section
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Sel

variable {X : Fields} (Pr : Primes X)

theorem exists_over (X : Fields) (v : HeightOneSpectrum (𝓞 X.F)) :
    ∃ P : HeightOneSpectrum (𝓞 X.E), P.asIdeal.under (𝓞 X.F) = v.asIdeal := by
  have hinj : Function.Injective (algebraMap (𝓞 X.F) (𝓞 X.E)) := FaithfulSMul.algebraMap_injective (𝓞 X.F) (𝓞 X.E)
  have hv := v.isPrime
  obtain ⟨Q, _, hQ, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 X.E))
    (by rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinj)]; exact bot_le)
  refine ⟨⟨Q, hQ, ?_⟩, hc⟩
  rintro rfl
  exact v.ne_bot (hc ▸ Ideal.comap_bot_of_injective _ hinj)


end Sel

section Fin

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (Gc : ChGlob X R.m)

abbrev chr0 (X : Fields) (S : Set ℕ) : Chr X.F X.E X.K := ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)



end Fin

section Dat

variable (d : ColDat) (S : Set ℕ)

end Dat

end Formalism.L2.Ker
end
end

