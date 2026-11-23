module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices.InstFintypeFlIdx
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.HSClosing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.EqZeroOfSecTraceMulEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PBlockRatioAlg
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesGeo
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0019

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFlZArithVar
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace FlZArithVar

section Rename

variable {K : Type} [Fintype K] {ι ι' : K → Type} [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]


omit [Fintype K] in
theorem isMultiHomog_rename_sigma (e : ∀ k, ι k ≃ ι' k) {g : MRing ι} {a : K → ℕ}
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename (Equiv.sigmaCongrRight e) g : MRing ι') a := by
  classical
  intro m hm k
  rw [support_rename_of_injective (Equiv.sigmaCongrRight e).injective, Finset.mem_image] at hm
  obtain ⟨m0, hm0, rfl⟩ := hm
  have h1 : ∀ i : ι' k, Finsupp.mapDomain (Equiv.sigmaCongrRight e) m0 ⟨k, i⟩ = m0 ⟨k, (e k).symm i⟩ := by
    intro i
    have : (⟨k, i⟩ : Σ k, ι' k) = Equiv.sigmaCongrRight e ⟨k, (e k).symm i⟩ := by simp
    rw [this, Finsupp.mapDomain_apply_of_injective (Equiv.sigmaCongrRight e).injective]
  simp only [h1]
  rw [Equiv.sum_comp (e k).symm (fun j => m0 ⟨k, j⟩)]
  exact hg m0 hm0 k

theorem isArithVar_comap_rename_sigma (e : ∀ k, ι k ≃ ι' k) {P : Ideal (MRing ι')} {d : ℕ}
    (hP : IsArithVar P d) :
    IsArithVar (P.comap (rename (Equiv.sigmaCongrRight e) : MRing ι →ₐ[ℤ] MRing ι')) d := by
  obtain ⟨hne, ⟨hprime, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  let E : MRing ι ≃+* MRing ι' := (renameEquiv ℤ (Equiv.sigmaCongrRight e)).toRingEquiv
  have hQ : P.comap (rename (Equiv.sigmaCongrRight e) : MRing ι →ₐ[ℤ] MRing ι') = P.map E.symm := by
    rw [Ideal.map_symm]
    rfl
  have hEs : ∀ g, E.symm g = rename (Equiv.sigmaCongrRight fun k => (e k).symm) g := by
    intro g
    show (renameEquiv ℤ (Equiv.sigmaCongrRight e)).symm g = _
    rw [renameEquiv_symm, Equiv.sigmaCongrRight_symm]
    rfl
  refine ⟨hne, ⟨?_, ⟨E.symm '' S, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · exact Ideal.comap_isPrime _ _
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨a, ha⟩ := hS g hg
    exact ⟨a, by rw [hEs]; exact isMultiHomog_rename_sigma (fun k => (e k).symm) ha⟩
  · rw [hQ, hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨(e k).symm i, fun hj => hi ?_⟩
    rw [Ideal.mem_comap] at hj
    simpa using hj
  · have h : Ideal.comap (C : ℤ →+* MRing ι)
        (P.comap (rename (Equiv.sigmaCongrRight e) : MRing ι →ₐ[ℤ] MRing ι')) =
        Ideal.comap (C : ℤ →+* MRing ι') P := by
      ext x
      simp only [Ideal.mem_comap, rename_C]
    unfold IsHorizontal
    rw [h]
    exact hhor
  · rw [← hdim]
    refine ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ P E ?_)
    show P = Ideal.map (E : MRing ι →+* MRing ι') (Ideal.comap (E : MRing ι →+* MRing ι') P)
    exact (Ideal.map_comap_of_surjective (E : MRing ι →+* MRing ι') E.surjective P).symm

end Rename

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)



end FlZArithVar

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StNbarLeviChartReg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology
open ReciprocityTheory.AnForm (levi)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E}

def regNbarQ (H : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine H)) (B p q : ℕ) (t : ℝ) :
    ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι :=
  smoothRep (mCoordIdeal D.y)
    (hermOfFun ι ((q : ℤ) • muTwDeg H B + (p : ℤ) • D.a') fun z =>
      (S.ref.h z * Real.exp (S.regWeight t (M.proj z))) ^ q *
        (∏ p' ∈ D.SB B, D.vertFactor p' z) ^ q * D.A'.h z ^ p)

def NbarLeviChartReg.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) (M : XModel D)
    (S : LogLogRegularisationSetting M D.Xo (muLine H)), S.IsTied → ∀ (B p q : ℕ) (t : ℝ),
    M.atlas.Smooth (S.regWeight t) →
    ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ w, IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal D.y) z w →
    ∀ k : Fin S.R.N, M.proj z ∈ S.R.mid k →
      ∃ v : Fin D.n → ℂ, IsChartVel M (S.R.chart k) z w v ∧
        levi (fun y => Real.log ((regNbarQ H M S B p q t).h y)) z w =
          q * levi (S.R.chartFun (S.regWeight t) k) (S.R.chart k (M.proj z)) v +
            p * levi (fun y => Real.log (D.A'.h y)) z w

theorem NbarLeviChart.of_reg (h : NbarLeviChartReg.Statement) : LowerBoundFree.NbarLeviChart.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q t hs z hz w hw k hk
  exact h II Ψ K ι Ω E D X.H X.M X.S X.S_tied B p q t hs z hz w hw k hk

namespace Line

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

end Line

end GroundTheory.Heights₂.Heights.NineStatements
end
end

