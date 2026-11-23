module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import CompanionTheory.EightfoldTheory.VariationTheory.PublishedTheorems.ImportsAlt
public import CompanionTheory.EightfoldTheory.VariationTheory.SelfDualForms.SelfDualWeylChambers.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExistsIdele
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolLin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExpInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.OrthCases
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import GroundTheory.AutomorphicForms.AffineBruhat
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0246
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0244
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0348
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0036

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalOfFiniteSubringFraction
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

theorem finiteDimensional_of_finite_subring_fraction :
    ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (B : Subring K) (B' : Subring L)
      (φ : B →+* B'), (∀ x : B, (φ x : L) = algebraMap K L x) → φ.Finite →
      (∀ y : L, ∃ a ∈ B', ∃ b ∈ B', b ≠ 0 ∧ y * b = a) → FiniteDimensional K L := by
  intro K L _ _ _ B B' φ hφ hfin hfrac
  letI : Algebra B B' := φ.toAlgebra
  have hMF : Module.Finite B B' := hfin
  obtain ⟨s, hs⟩ := hMF.fg_top

  have hB'span : ∀ x : B', (x : L) ∈ Submodule.span K ((fun z : B' => (z : L)) '' (s : Set B')) := by
    intro x
    have hx : x ∈ Submodule.span B (s : Set B') := by rw [hs]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
    | zero => simp
    | add u v _ _ hu hv => simpa using Submodule.add_mem _ hu hv
    | smul b u _ hu =>
      have : ((b • u : B') : L) = (b : K) • (u : L) := by
        rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, Subring.coe_mul, hφ, Algebra.smul_def]
      rw [this]; exact Submodule.smul_mem _ _ hu
  let S : Subalgebra K L := Algebra.adjoin K (B' : Set L)
  have hSsub : Subalgebra.toSubmodule S =
      Submodule.span K ((fun z : B' => (z : L)) '' (s : Set B')) := by
    apply le_antisymm
    · rw [Algebra.adjoin_eq_span]
      apply Submodule.span_le.mpr
      intro y hy
      have hy' : y ∈ B'.toSubmonoid := by
        rw [← Submonoid.closure_eq B'.toSubmonoid]; exact hy
      exact hB'span ⟨y, hy'⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨z, _, rfl⟩
      exact Algebra.subset_adjoin z.2
  have hFG : (Subalgebra.toSubmodule S).FG := by
    rw [hSsub]
    exact Submodule.fg_span ((s.finite_toSet).image _)
  have hB'S : ∀ y ∈ B', y ∈ S := fun y hy => Algebra.subset_adjoin hy
  have htop : ∀ y : L, y ∈ S := by
    intro y
    obtain ⟨a, ha, b, hb, hb0, hyb⟩ := hfrac y
    have hbinv : b⁻¹ ∈ S := by
      have hint : IsIntegral K b := IsIntegral.of_mem_of_fg S hFG b (hB'S b hb)
      exact Subalgebra.inv_mem_of_algebraic (A := S) (x := ⟨b, hB'S b hb⟩) hint.isAlgebraic
    have : y = a * b⁻¹ := by rw [← hyb, mul_assoc, mul_inv_cancel₀ hb0, mul_one]
    rw [this]; exact S.mul_mem (hB'S a ha) hbinv
  refine ⟨?_⟩
  obtain ⟨t, ht⟩ := hFG
  refine ⟨t, ?_⟩
  rw [ht, eq_top_iff]
  intro y _
  exact htop y

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntegrallyClosedSectionsOfSmoothComplex
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

theorem isIntegrallyClosed_sections_of_smooth_complex :
    ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℂ) [Smooth s] (U : Z.Opens), IsAffineOpen U → genericPoint Z ∈ U → IsIntegrallyClosed Γ(Z, U) := by
  intro Z _ s hsm U hU hg
  have hs : (s.appLE ⊤ U le_top).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth s hsm ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  letI : Algebra Γ(Sp ℂ, ⊤) Γ(Z, U) := (s.appLE ⊤ U le_top).hom.toAlgebra
  have : Algebra.Smooth Γ(Sp ℂ, ⊤) Γ(Z, U) := hs
  let e : Γ(Sp ℂ, ⊤) ≃+* ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
  letI : Field Γ(Sp ℂ, ⊤) := (e.toMulEquiv.isField (Field.toIsField ℂ)).toField
  have : Nonempty U := ⟨⟨_, hg⟩⟩
  have : IsDomain Γ(Z, U) := inferInstance
  exact GlobalTheory.isIntegrallyClosed_of_smooth Γ(Sp ℂ, ⊤) Γ(Z, U)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IwahoriSubgroupDefinitionsAgree
section
open ValuativeRel Matrix

namespace GlobalTheory.IwEq

theorem iwahori_eq_glnLocal_iwahori : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a : ℕ),
    GlobalTheory.SmGL.iwahori k (Fin a) = GroundTheory.Automorphic.GLnLocal.iwahori k a := by
  intro k _ _ _ _ a
  ext g
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, GlobalTheory.SmGL.mem_borel] at hu
    refine ⟨u, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, GroundTheory.Automorphic.mem_borel_iff]
      intro i j hij
      rw [GroundTheory.Automorphic.GLnLocal.residueReduction_apply]
      exact hu i j hij
    · ext i j
      rfl
  · rintro ⟨u, hu, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, GroundTheory.Automorphic.mem_borel_iff] at hu
    refine ⟨u, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, GlobalTheory.SmGL.mem_borel]
      intro i j hij
      have h := hu i j hij
      rw [GroundTheory.Automorphic.GLnLocal.residueReduction_apply] at h
      exact h
    · ext i j
      rfl

end GlobalTheory.IwEq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteAwayOfPositivePair
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc.AwayInd


set_option maxHeartbeats 4000000 in
theorem away_of_pos_pair : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    KIn t → S.Pos → S.Pair → S.Away) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hSpl hK hPos hPair
  intro v j hj
  have hgood := J.one.good
  have hint := J.one.int
  have hp : (D.what₂.places.resChar w).Prime := Fact.out
  obtain ⟨hcop, hSS, -, -⟩ := GlobalTheory.T.level_badPrimes_coprime_residueChar S hDict hSpl
  obtain ⟨P, hPof, happ, hpP, hpP2⟩ := _root_.GlobalTheory.TwV.Xc.PrimeAt.exists_primeOf_place _ _ _ _ _ (A0 J) hint hSpl.1 v
  obtain ⟨a, b, hab, ha, hb⟩ := GlobalTheory.XcSplit.prime_not_stable _ _ (sigD D) _ _ _ (A0 J) _ hgood hint hSpl.1 v P hPof
  have hpC : (((D.what₂.places.resChar w : ℕ)) : 𝓞 D.host.E) ∈ (Formalism.L2.Col.conjPrime₂ P).asIdeal := by
    rw [Formalism.L2.Col.mem_conjP, map_natCast]; exact hpP
  have hcopE : IsCoprime (((t.rd u μ).lev : ℕ) : 𝓞 D.host.E) ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.E) := by
    have h := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (𝓞 D.host.E))
    simpa using h
  have hlev : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal →
      (((t.rd u μ).lev : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal := by
    intro Q hpQ hlQ
    obtain ⟨x, y, hxy⟩ := hcopE
    have h1 : (1 : 𝓞 D.host.E) ∈ Q.asIdeal := hxy ▸ Q.asIdeal.add_mem (Q.asIdeal.mul_mem_left x hlQ) (Q.asIdeal.mul_mem_left y hpQ)
    exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hab' : (b : D.host.E) = D.host.conj (a : D.host.E) := by
    rw [hab]
    first | exact Formalism.L2.PairingIndexBounds.F.sig_conj D _ | exact Formalism.L2.Fam.sig_eq_conj D.host D.sp.cm _ | exact Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D _
  refine ⟨P, ⟨a, b, hab', ha, hb⟩, _root_.GlobalTheory.TwV.Xc.inverseHalfDifferent_local_trivial_at_prime_norm D _ hp P hpP hpP2, fun h => hSS P h hpP, fun h => hSS _ h hpC,
    hlev P hpP, hlev _ hpC, hPof, happ, ?_⟩
  by_cases hc : Nonempty ((sysS H X std).Lv.comp j) ∧ Nonempty ((sysS H X std).Lv.comp (j + 1))
  · obtain ⟨⟨c⟩, ⟨c'⟩⟩ := hc
    obtain ⟨π, hπU, hoff, hord⟩ := _root_.GlobalTheory.TwV.Xc.Unif.exists_unif _ _ (sigD D) _ _ _ (A0 J) _ hgood v
    have hU : IsUnifAt J v π := ⟨hπU, hoff, hord⟩
    obtain ⟨x, y, hx0, hy0, hx, hy⟩ := _root_.GlobalTheory.TwV.Xc.two_units S hDict hSpl hK hPos v π hU j hj c c'
    refine ⟨x, y, hx0, hy0, ?_⟩
    intro La Lb La' Lb' h1 h2 h3 h4 haw
    have e1 : La.1 = Lb.1 := congrArg (fun z : (sysS H X std).Lt j × (sysS H X std).Lt (j + 1) => z.1.1) haw
    have e2 : Function.update La.2 ((sysS H X std).vJ j v) ⊥ = Function.update Lb.2 ((sysS H X std).vJ j v) ⊥ :=
      congrArg (fun z : (sysS H X std).Lt j × (sysS H X std).Lt (j + 1) => z.1.2) haw
    have e3 : La'.1 = Lb'.1 := congrArg (fun z : (sysS H X std).Lt j × (sysS H X std).Lt (j + 1) => z.2.1) haw
    have e4 : Function.update La'.2 ((sysS H X std).vJ (j + 1) v) ⊥ = Function.update Lb'.2 ((sysS H X std).vJ (j + 1) v) ⊥ :=
      congrArg (fun z : (sysS H X std).Lt j × (sysS H X std).Lt (j + 1) => z.2.2) haw
    have hA : SameAway (hT := hT) (H := H) (X := X) std v j La Lb := ⟨h1, h3, e1, e2⟩
    have hA' : SameAway (hT := hT) (H := H) (X := X) std v (j + 1) La' Lb' := ⟨h2, h4, e3, e4⟩
    refine ⟨GlobalTheory.T.eqOffPrime_kernelLattices_of_agreeAway S hDict hSpl v P hPof j hj.le La Lb hA, GlobalTheory.T.eqOffPrime_kernelLattices_of_agreeAway S hDict hSpl v P hPof (j + 1) hj La' Lb' hA', ?_, ?_,
      GlobalTheory.T.movedDatum_eq_of_latticeTuples_agreeAway S hDict hSpl v j hj La Lb La' Lb' hA hA', GlobalTheory.T.kernelSite_scalars_agree_awayFromPlace S hDict hSpl hPair v π hU j hj x y hx hy La Lb La' Lb' hA hA'⟩
    · have hLb : Lb = (La.1, Lb.2) := Prod.ext e1.symm rfl
      rw [hLb]
      exact _root_.GlobalTheory.TwV.Xc.frM_fd_comp S hDict hSpl j La.1 La.2 Lb.2
    · have hLb : Lb' = (La'.1, Lb'.2) := Prod.ext e3.symm rfl
      rw [hLb]
      exact _root_.GlobalTheory.TwV.Xc.frM_fd_comp S hDict hSpl (j + 1) La'.1 La'.2 Lb'.2
  · have h1 : (sysS H X std).vEqK 1 0 := GlobalTheory.UnitK.vEqK_zero_of_norm_one _ _ S.E.toCEmb 1 (by simp)
    refine ⟨1, 1, h1, h1, ?_⟩
    intro La Lb La' Lb'
    exact absurd ⟨⟨La.1⟩, ⟨La'.1⟩⟩ hc

end GlobalTheory.TwV.Xc.AwayInd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorPolynomialOfRealisingValue
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem trDY_smul {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ) (D : D7)
    {N N' : ℕ} {ι : ℂ →+* Kc} (e : GL3Theta.Idx D N N' → X.ZA j)
    (Φ₀ : MvPolynomial (GL3Theta.FrV D N') ℂ →ₛₗ[ι] XspC (X.Pj (j + 1)) Kc)
    (R : MvPolynomial (GL3Theta.Idx D N N') (MvPolynomial (GL3Theta.FrV D N') ℂ)) (r : ℂ) :
    trDY X Kc j D e Φ₀ (r • R) = ι r • trDY X Kc j D e Φ₀ R := by
  unfold trDY
  rw [Finset.smul_sum, Finset.sum_subset MvPolynomial.support_smul]
  · refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.coeff_smul, LinearMap.map_smulₛₗ, MvPolynomial.smul_monomial]
  · intro α _ h
    rw [MvPolynomial.notMem_support_iff.1 h, map_zero, MvPolynomial.monomial_zero]

theorem polDY_smul (D : D7) {N N' : ℕ} (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ) (r : ℂ) :
    polDY D s (r • Q) (N' := N') = r • polDY D s Q (N' := N') := by
  unfold polDY
  exact map_smul _ r Q

theorem polDel_realises : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (r : ℂ) (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) (r • Q) Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → ∀ (s : D.what₂.Tau → ℂ), (∀ τ, s τ ≠ 0) → GoodG X Kc j G ∧ OddDeg X j G ∧ ∀ n, AddMonoidAlgebra.coeff (polDel X Kc j G) n = ι (r * cOp X D pos j s) • AddMonoidAlgebra.coeff (trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) n := by
  intro p _ X D pos Kc _ _ ι j hN ν hν Q hQ r Gc G hR hG s hs
  have hQr : r • Q ∈ WtPol ℂ ν := Submodule.smul_mem _ r hQ
  have hop := GlobalTheory.T.detTwistedFrame_operatorIdentity_denominator X D pos Kc ι j hN ν hν (r • Q) hQr Gc G hR hG s hs
  refine ⟨⟨_, hop⟩, _root_.GlobalTheory.TwV.DelA.oddDeg_of_realises X D pos Kc ι j hN ν hν (r • Q) hQr Gc G hR hG, fun n => ?_⟩
  rw [polDel_eq X Kc j G _ hop, polDY_smul, trDY_smul, Formalism.L2.G.Pend.cD, RingHom.comp_apply,
    MvPolynomial.coeff_C_mul, ← Algebra.smul_def, MvPolynomial.coeff_smul, smul_smul, map_mul, mul_comm]

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RatioSpanCotangentChangeDenominator
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj

theorem mem_of_algebraMap_mem_map_away {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (s : R)
    [IsLocalization.Away s S] {I m : Ideal R} (hm : m.IsMaximal) (hI : m ^ 2 ≤ I) (hs : s ∉ m) {x : R}
    (hx : algebraMap R S x ∈ I.map (algebraMap R S)) : x ∈ I := by
  obtain ⟨⟨y, t⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers s) S).1 hx
  rw [← map_mul] at e
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers s) S).1 e
  have hw : ((c : R) * t) * x ∈ I := by
    have : (c : R) * y ∈ I := I.mul_mem_left _ y.2
    rw [← hc] at this
    convert this using 1; ring
  have hwm : (c : R) * t ∉ m := by
    obtain ⟨k, hk⟩ := c.2
    obtain ⟨l, hl⟩ := t.2
    rw [← hk, ← hl, ← pow_add]
    exact fun h => hs (hm.isPrime.mem_of_pow_mem _ h)
  obtain ⟨u, i, hi, h1⟩ := hm.exists_inv hwm
  have hi2 : i ^ 2 ∈ I := hI (Ideal.pow_mem_pow hi 2)
  have hx' : x = (u ^ 2 * ((c : R) * t) + 2 * u * i) * (((c : R) * t) * x) + x * i ^ 2 := by
    linear_combination (-x * (u * ((c : R) * t) + i + 1)) * h1
  rw [hx']
  exact I.add_mem (I.mul_mem_left _ hw) (I.mul_mem_left _ hi2)

theorem ker_le_map_ker_away {R S K : Type} [CommRing R] [CommRing S] [Field K] [Algebra R S] (s : R)
    [IsLocalization.Away s S] (evR : R →+* K) (evS : S →+* K) (h : ∀ x, evS (algebraMap R S x) = evR x) :
    RingHom.ker evS ≤ (RingHom.ker evR).map (algebraMap R S) := by
  intro w hw
  obtain ⟨⟨x, t⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) w
  dsimp only at hw ⊢
  have hx : evR x = 0 := by
    have := congrArg evS (IsLocalization.mk'_spec S x t)
    rw [map_mul, RingHom.mem_ker.1 hw, zero_mul, h] at this
    exact this.symm
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hx)

theorem span_ratio_of_span_ratio (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (N : ℕ) (ι : X ⟶ PSpace ℂ N)
    (hι : IsClosedImmersion ι) (n : ℕ) (hn : 0 < n) (k : ℕ) (f : Fin k → MvPolynomial (Fin (N + 1)) ℂ)
    (a b : MvPolynomial (Fin (N + 1)) ℂ)
    (hf : ∀ j, f j ∈ GlobalTheory.ProjSpace.grading ℂ N n) (ha : a ∈ GlobalTheory.ProjSpace.grading ℂ N n)
    (hb : b ∈ GlobalTheory.ProjSpace.grading ℂ N n) (z : CxPts p (RingHom.id ℂ))
    (hza : z ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι a))
    (hzb : z ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι b))
    (h : RingHom.ker (CxPts.evHom hza) ≤ Ideal.span (Set.range fun j => GlobalTheory.EtProj.fRatio ι (f j) a (hf j) ha) ⊔
          RingHom.ker (CxPts.evHom hza) ^ 2) :
    RingHom.ker (CxPts.evHom hzb) ≤ Ideal.span (Set.range fun j => GlobalTheory.EtProj.fRatio ι (f j) b (hf j) hb) ⊔
          RingHom.ker (CxPts.evHom hzb) ^ 2 := by
  haveI := hι
  set 𝒜 := ProjSpace.grading ℂ N
  set D := Proj.basicOpen 𝒜 a ⊓ Proj.basicOpen 𝒜 b with hDdef
  set W : X.Opens := ι ⁻¹ᵁ D with hWdef
  have hWa : W ≤ fOpen ι a := fun x hx => hx.1
  have hWb : W ≤ fOpen ι b := fun x hx => hx.2
  have hzW : z ∈ CxPts.ptsIn p (RingHom.id ℂ) W :=
    CxPts.mem_ptsIn.2 ⟨CxPts.mem_ptsIn.1 hza, CxPts.mem_ptsIn.1 hzb⟩
  have hUa : IsAffineOpen (fOpen ι a) := (Proj.isAffineOpen_basicOpen 𝒜 a ha hn).preimage ι
  have hUb : IsAffineOpen (fOpen ι b) := (Proj.isAffineOpen_basicOpen 𝒜 b hb hn).preimage ι
  have hres : ∀ {c d : MvPolynomial (Fin (N + 1)) ℂ} (hc : c ∈ 𝒜 n) (hd : d ∈ 𝒜 n) (hW : W ≤ fOpen ι d)
      (hD : D ≤ Proj.basicOpen 𝒜 d),
      resG X hW (fRatio ι c d hc hd) = (ι.app D).hom (ProjFrac.frac 𝒜 D c d hc hd hD) := by
    intro c d hc hd hW hD
    have := congrArg (fun φ => φ.hom (ProjFrac.frac 𝒜 _ c d hc hd le_rfl)) (ι.naturality (homOfLE hD).op)
    simp only [CommRingCat.comp_apply] at this
    rw [← ProjFrac.resG_frac hD]
    exact this.symm

  have hratio : ∀ j, resG X hWa (fRatio ι (f j) a (hf j) ha) =
      resG X hWb (fRatio ι (f j) b (hf j) hb) * (ι.app D).hom (ProjFrac.frac 𝒜 D b a hb ha inf_le_left) := by
    intro j
    rw [hres _ _ hWa inf_le_left, hres _ _ hWb inf_le_right, ← map_mul]
    congr 1
    exact (ProjFrac.frac_mul_eq (by ring)).symm

  set sa := fRatio ι b a hb ha
  set sb := fRatio ι a b ha hb
  have eA : W = X.basicOpen sa := by
    rw [show sa = (ι.app _).hom (ProjFrac.frac 𝒜 _ b a hb ha le_rfl) from rfl]
    refine Eq.trans ?_ (Scheme.preimage_basicOpen ι _)
    rw [ProjFrac.basicOpen_frac]
  have eB : W = X.basicOpen sb := by
    rw [show sb = (ι.app _).hom (ProjFrac.frac 𝒜 _ a b ha hb le_rfl) from rfl]
    refine Eq.trans ?_ (Scheme.preimage_basicOpen ι _)
    rw [ProjFrac.basicOpen_frac]
    exact congrArg (fun U => ι ⁻¹ᵁ U) (inf_comm _ _)
  letI algA : Algebra Γ(X, fOpen ι a) Γ(X, W) := (resG X hWa).toAlgebra
  letI algB : Algebra Γ(X, fOpen ι b) Γ(X, W) := (resG X hWb).toAlgebra
  haveI locA : IsLocalization.Away sa Γ(X, W) := hUa.isLocalization_of_eq_basicOpen sa (homOfLE hWa) eA
  haveI locB : IsLocalization.Away sb Γ(X, W) := hUb.isLocalization_of_eq_basicOpen sb (homOfLE hWb) eB
  have evA : ∀ g, CxPts.evHom hzW (algebraMap Γ(X, fOpen ι a) Γ(X, W) g) = CxPts.evHom hza g := fun g => by
    change CxPts.evHom hzW (resG X hWa g) = _
    rw [← CxPts.ev_eq, ← CxPts.ev_eq]
    exact CxPts.ev_res hWa hzW g
  have evB : ∀ g, CxPts.evHom hzW (algebraMap Γ(X, fOpen ι b) Γ(X, W) g) = CxPts.evHom hzb g := fun g => by
    change CxPts.evHom hzW (resG X hWb g) = _
    rw [← CxPts.ev_eq, ← CxPts.ev_eq]
    exact CxPts.ev_res hWb hzW g
  have h1A := ker_le_map_ker_away sa _ _ evA
  have h1B := ker_le_map_ker_away sb _ _ evB
  have h2A : (RingHom.ker (CxPts.evHom hza)).map (algebraMap Γ(X, fOpen ι a) Γ(X, W)) ≤ RingHom.ker (CxPts.evHom hzW) :=
    Ideal.map_le_iff_le_comap.2 fun x hx => by
      rw [Ideal.mem_comap, RingHom.mem_ker, evA]; exact hx
  have h3 : RingHom.ker (CxPts.evHom hzW) ≤
      Ideal.span ((algebraMap Γ(X, fOpen ι a) Γ(X, W)) '' Set.range fun j => fRatio ι (f j) a (hf j) ha) ⊔
        RingHom.ker (CxPts.evHom hzW) ^ 2 := by
    intro x hx
    have := Ideal.map_mono h (h1A hx)
    rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span] at this
    exact sup_le_sup le_rfl (Ideal.pow_right_mono h2A 2) this
  have h4 : Ideal.span ((algebraMap Γ(X, fOpen ι a) Γ(X, W)) '' Set.range fun j => fRatio ι (f j) a (hf j) ha) ≤
      Ideal.span ((algebraMap Γ(X, fOpen ι b) Γ(X, W)) '' Set.range fun j => fRatio ι (f j) b (hf j) hb) := by
    rw [Ideal.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    change resG X hWa _ ∈ _
    rw [hratio j]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, ⟨j, rfl⟩, rfl⟩)

  have hsurj : Function.Surjective (CxPts.evHom hzb) := fun c =>
    ⟨ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (fOpen ι b) c, by rw [← CxPts.ev_eq]; exact CxPts.ev_algX hzb c⟩
  have hmax : (RingHom.ker (CxPts.evHom hzb)).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  have hs : sb ∉ RingHom.ker (CxPts.evHom hzb) := by
    rw [RingHom.mem_ker, ← CxPts.ev_eq]
    exact (CxPts.mem_ptsIn_basicOpen hzb sb).1 (eB ▸ hzW)
  intro g hg
  refine mem_of_algebraMap_mem_map_away (S := Γ(X, W)) sb hmax le_sup_right hs ?_
  have hgW : algebraMap Γ(X, fOpen ι b) Γ(X, W) g ∈ RingHom.ker (CxPts.evHom hzW) := by
    rw [RingHom.mem_ker, evB]; exact hg
  rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span]
  exact sup_le_sup h4 (Ideal.pow_right_mono h1B 2) (h3 hgW)

end GlobalTheory.EtProj
end
end

