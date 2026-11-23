module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GramMatrixAdjoint
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0255
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0258
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittMixedModelUnipotentFormulas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0235
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUniqueSphericalDoublingSectionUnramified
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Core.Rk.SphSec

section Gen

variable {G : Type} [Group G] (P K : Subgroup G) (f : P →* ℂ)

theorem gen_wd (hK : ∀ p : P, (p : G) ∈ K → f p = 1) (p p' : P) (k k' : G) (hk : k ∈ K) (hk' : k' ∈ K)
    (e : (p : G) * k = p' * k') : f p = f p' := by
  have h1 : ((p'⁻¹ * p : P) : G) = k' * k⁻¹ := by
    have : (p : G) = p' * (k' * k⁻¹) := by rw [← mul_assoc, ← e, mul_inv_cancel_right]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, this, inv_mul_cancel_left]
  have h2 := hK _ (h1 ▸ mul_mem hk' (inv_mem hk))
  calc f p = f (p' * (p'⁻¹ * p)) := by rw [mul_inv_cancel_left]
    _ = f p' := by rw [map_mul, h2, mul_one]

variable (hI : ∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k)

noncomputable def genFun (g : G) : ℂ := f (hI g).choose

variable {P K f hI}

theorem genFun_mul (hK : ∀ p : P, (p : G) ∈ K → f p = 1) (p : P) {k : G} (hk : k ∈ K) :
    genFun P K f hI (p * k) = f p := by
  obtain ⟨k', hk', e⟩ := (hI (p * k)).choose_spec
  exact gen_wd P K f hK _ _ _ _ hk' hk e.symm

theorem genFun_right (hK : ∀ p : P, (p : G) ∈ K → f p = 1) (g : G) {k : G} (hk : k ∈ K) :
    genFun P K f hI (g * k) = genFun P K f hI g := by
  obtain ⟨k₀, hk₀, e⟩ := (hI g).choose_spec
  conv_lhs => rw [e, mul_assoc]
  exact genFun_mul hK _ (mul_mem hk₀ hk)

theorem genFun_left (hK : ∀ p : P, (p : G) ∈ K → f p = 1) (p : P) (g : G) :
    genFun P K f hI (p * g) = f p * genFun P K f hI g := by
  obtain ⟨k₀, hk₀, e⟩ := (hI g).choose_spec
  conv_lhs => rw [e, ← mul_assoc]
  rw [← Subgroup.coe_mul, genFun_mul hK _ hk₀, map_mul]
  rfl

theorem genFun_one (hK : ∀ p : P, (p : G) ∈ K → f p = 1) : genFun P K f hI 1 = 1 := by
  have := genFun_mul (hI := hI) hK 1 (one_mem K)
  rwa [Subgroup.coe_one, mul_one, map_one] at this

theorem genFun_unique (Ψ : G → ℂ) (hΨ : ∀ (p : P) g, Ψ (p * g) = f p * Ψ g) (hΨK : ∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g)
    (g : G) : Ψ g = Ψ 1 * genFun P K f hI g := by
  obtain ⟨k₀, hk₀, e⟩ := (hI g).choose_spec
  have := hΨ (hI g).choose 1
  rw [mul_one] at this
  rw [genFun, mul_comm]
  conv_lhs => rw [e]
  rw [hΨK _ hk₀, this]

theorem continuous_genFun [TopologicalSpace G] [IsTopologicalGroup G] (hK : ∀ p : P, (p : G) ∈ K → f p = 1)
    (ho : IsOpen (K : Set G)) : Continuous (genFun P K f hI) := by
  refine continuous_iff_continuousAt.2 fun g => (continuousAt_const (y := genFun P K f hI g)).congr ?_
  filter_upwards [(ho.preimage (continuous_const_mul g⁻¹)).mem_nhds (by simp [one_mem])] with h hh
  have := genFun_right (hI := hI) hK g (k := g⁻¹ * h) hh
  rwa [mul_inv_cancel_left, eq_comm] at this

theorem gen_exists [TopologicalSpace G] [IsTopologicalGroup G] (P K : Subgroup G) (f : P →* ℂ)
    (hI : ∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k) (hK : ∀ p : P, (p : G) ∈ K → f p = 1) (ho : IsOpen (K : Set G)) :
    ∃ φ : G → ℂ, (∀ (p : P) g, φ (p * g) = f p * φ g) ∧ Continuous φ ∧ (∀ g, ∀ k ∈ K, φ (g * k) = φ g) ∧ φ 1 = 1 ∧
      ∀ Ψ : G → ℂ, (∀ (p : P) g, Ψ (p * g) = f p * Ψ g) → (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∀ g, Ψ g = Ψ 1 * φ g :=
  ⟨genFun P K f hI, genFun_left hK, continuous_genFun hK ho, fun g _ hk => genFun_right hK g hk, genFun_one hK,
    fun Ψ hΨ hΨK g => genFun_unique Ψ hΨ hΨK g⟩

end Gen


set_option maxHeartbeats 1000000 in
theorem exists_isSphSecAt_unique : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ v : FinPl D, (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt μ w) → ∀ s : ℂ, ∃ φ, IsSphSecAt A L v μ s φ ∧ ∀ Ψ : Gv (dblSp A) v → ℂ, (∀ (p : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram) g, Ψ (p * g) = charAt μ v (aH _ D.sp.cm.sig (dblSp A).gram p) * npow (absEv D.host.F D.host.E v (aH _ D.sp.cm.sig (dblSp A).gram p)) (s + (A.rank : ℂ) / 2) * Ψ g) → (∀ k ∈ KFin D.sp.cm.sig (dblSp A).gram L v, ∀ g, Ψ (g * k) = Ψ g) → ∀ g, Ψ g = Ψ 1 * φ g := by
  intro D A L hL μ hμ v hunr s
  haveI : Submodule.IsFullLattice D.host.E L :=
    Formalism.IndefR.Fin.PDA.selfDual_isFullLattice A L hL
  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (KFin D.sp.cm.sig (dblSp A).gram L v) := by
    by_cases hs : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v
    · exact GlobalTheory.T.hasIwasawaDecomposition_doubled_split_place D A L hL v hs
    · exact GlobalTheory.T.iwasawa_doubled_hermitian_space_nonsplit_place D A L hL v hs
  let N : ℝ≥0 →* ℂ := ⟨⟨fun r => npow r (s + (A.rank : ℂ) / 2), one_npow _⟩, fun r r' => GlobalTheory.Doubling.npow_mul r r' _⟩
  let f : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram →* ℂ :=
    (Circle.coeHom.comp ((charAt μ v).comp (aH _ D.sp.cm.sig (dblSp A).gram))) *
      (N.comp ((absEv D.host.F D.host.E v).comp (aH _ D.sp.cm.sig (dblSp A).gram)))
  have hf : ∀ p, f p = (charAt μ v (aH _ D.sp.cm.sig (dblSp A).gram p) : ℂ) *
      npow (absEv D.host.F D.host.E v (aH _ D.sp.cm.sig (dblSp A).gram p)) (s + (A.rank : ℂ) / 2) := fun p => rfl
  have hK : ∀ p : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram,
      (p : Gv (dblSp A) v) ∈ KFin D.sp.cm.sig (dblSp A).gram L v → f p = 1 := by
    intro p hp
    have h1 := _root_.GlobalTheory.Core.Rk.AInt.aH_mem_intLoc D A L hL v p hp
    have h2 : (((aH _ D.sp.cm.sig (dblSp A).gram p)⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) :
        Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intLoc D.host.F D.host.E v := by
      rw [← map_inv]
      exact _root_.GlobalTheory.Core.Rk.AInt.aH_mem_intLoc D A L hL v p⁻¹ (inv_mem hp)
    rw [hf, _root_.GlobalTheory.LFun.charAt_eq_one_of_unrAt_datum D μ v _ h1 h2 hunr,
      abs_aH_eq_one (continuous_absEv v) (isCompact_KFin v) p hp, one_npow, Circle.coe_one, one_mul]
  clear_value f
  obtain ⟨φ, hl, hc, hr, h1, hu⟩ := gen_exists (G := Gv (dblSp A) v) _ _ f hI hK (isOpen_KFin v)
  refine ⟨φ, ⟨mem_degPSH.2 ⟨fun p g => by rw [hl, hf], hc, IsKFinite.of_invariant fun g k hk => hr g k hk⟩,
    fun k hk g => hr g k hk, h1⟩, fun Ψ hΨ hΨK g => hu Ψ (fun p g => by rw [hΨ, hf]) hΨK g⟩

end GlobalTheory.Core.Rk.SphSec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.Iwasawa

theorem exists_mul_of_rank (D : D7) (A : HSp D) (g : GlobalTheory.StdUnn.G D A.rank) :
    ∃ p ∈ GlobalTheory.StdUnn.P D A.rank, ∃ k ∈ GlobalTheory.StdUnn.K D A.rank, g = p * k := by
  obtain ⟨μ, hμ, hconj⟩ := GlobalTheory.StdUnn.ConjElt.exists_isConj D
  obtain ⟨κ, hκ⟩ := GlobalTheory.StdUnn.chart_exists D A μ hμ
  obtain ⟨a, ha⟩ := GlobalTheory.Doubling.exists_isMaj A
  obtain ⟨p, hp⟩ := hconj A a ha κ hκ
  obtain ⟨q, k, hk, hqk⟩ := (GlobalTheory.Eis.isIwasawa_Khat (GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha)).1
    (κ.symm g * (p : GA D (dblSp A))⁻¹)
  refine ⟨κ ((q : GA D (dblSp A)) * p), ?_, κ ((p : GA D (dblSp A))⁻¹ * k * p), (hp k).1 hk, ?_⟩
  · exact (GlobalTheory.StdUnn.mem_siegel_iff_chart_mem_P D A μ hμ κ hκ _).1 (Subgroup.mul_mem _ q.2 p.2)
  · have h1 : κ.symm g = (q : GA D (dblSp A)) * k * p := by
      rw [← hqk, inv_mul_cancel_right]
    have h2 : (q : GA D (dblSp A)) * p * ((p : GA D (dblSp A))⁻¹ * k * p) = (q : GA D (dblSp A)) * k * p := by
      group
    rw [← map_mul, h2, ← h1, MulEquiv.apply_symm_apply]

theorem exists_mul : ∀ (D : D7) (n : ℕ) (g : GlobalTheory.StdUnn.G D n),
    ∃ p ∈ GlobalTheory.StdUnn.P D n, ∃ k ∈ GlobalTheory.StdUnn.K D n, g = p * k :=
  fun D n g => exists_mul_of_rank D (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral n) g

end GlobalTheory.StdUnn.Iwasawa
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastKernelDatumInLastLineFrameAtLevelPrimeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastKernelDatum_in_lastLineFrame_at_levelPrime : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → v.Is → ShapeOff v o → ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ (Λ : ι → Submodule 𝒪[k] (Fin c.T.rank → k)) (hΛ : ∀ i, (Λ i).IsFullLattice k) (u : ι → 𝓀[k]ˣ), (∀ i, (o.γ i).IsLat v.NT (Λ i)) ∧ Reps c.ψ (o.β (j + 1)) (o.γ₀ (j + 1 + 1) h) (c.x (j + 1)).L (c.x (j + 1 + 1)).L (fun i => haveI := hΛ i; phiOne (u i • o.Q (j + 1) i) (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastPair o.q (Λ i))) o.I (· ∈ v.tP) (v.dT (j + 1)) := by
  exact @GlobalTheory.SeeSaw.lastKernel_reps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawThetaIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.SeeLastPf

theorem ofAdj_zero (D : D7) (L S : HSp D) : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S 0 = 0 := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj]

theorem seeLast : ∀ D : D7, SeeLast D := by
  intro D ψ V₀ A L S X T L'' o o'' τ hL hL'' hτ χA χz χS χS' χT om₁ oma omz omX omT omz'' h₁ ha hz hX hT hz'' Ξ Φ₂ hΞ hΦ₂
  have hψ : IsStdChar D ψ (-1) := h₁.std
  have hsrc := _root_.GlobalTheory.TensorSrc.tensorSource D ψ hψ V₀ A L o S
  have htgt := _root_.GlobalTheory.TensorTargetRule.tensorTarget D ψ hψ X T L'' o'' S
  have hτ' : τᴴ ⬝ (L.gram ⬝ τ) = (((-1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L''.gram := by
    rw [hτ]; simp
  have hrk : L.rank = L''.rank := hL.trans hL''.symm
  have hline := fun u => _root_.GlobalTheory.ConjLine.weil_source_line_opposite D ψ L L'' S τ hrk hτ' χz χS χS' omz omz'' hz hz''
    (fun v => Ξ ((o.resS S).symm (u, v))) ((hsrc.slice_theta Ξ hΞ).2 u)
  refine ⟨fun u => (hline u).1, ?_⟩
  intro h₀ h h'
  have e1 : ∀ u, omX (h, o''.emb (h', 1)) (o''.boxT S Φ₂ fun w => Ξ ((o.resS S).symm
      (u, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) ⬝ w)))) 0 =
      omT (h, h') Φ₂ 0 * omz (1, h) (fun v => Ξ ((o.resS S).symm (u, v))) 0 := by
    intro u
    rw [htgt.om_box χS' χT χz⁻¹ omX omT omz'' hX hT hz'' h h' 1 Φ₂ _ hΦ₂ (hline u).1, htgt.box_zero,
      (hline u).2 h]
    beta_reduce
    congr 1
    exact congrArg (omz (1, h) (fun v => Ξ ((o.resS S).symm (u, v))))
      ((congrArg (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S) (Matrix.mul_zero _)).trans (ofAdj_zero D L S))
  have e2 := (hsrc.om_slice χA χz χS om₁ oma omz h₁ ha hz h₀ 1 h Ξ hΞ 0).2 0
  have e0 : (o.resS S).symm (0, 0) = 0 := by
    rw [← Prod.zero_eq_mk, map_zero]
  rw [e0] at e2
  simp only [e1]
  rw [e2]
  have : (fun u => omT (h, h') Φ₂ 0 * omz (1, h) (fun v => Ξ ((o.resS S).symm (u, v))) 0) =
      omT (h, h') Φ₂ 0 • (fun u' => omz (1, h) (fun v' => Ξ ((o.resS S).symm (u', v'))) 0) := by
    funext u; simp
  rw [this, map_smul]
  simp

end GlobalTheory.SeeLastPf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LscSeminormThetaFunctionsLevelLeSobolev
section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace GlobalTheory.SobBaire

open Filter Topology
open scoped Uniformity

theorem exists_bound_of_complete {E : Type} [AddCommGroup E] [Module ℂ E] (p : ℕ → Seminorm ℂ E)
    (hmono : ∀ d x, p d x ≤ p (d + 1) x)
    (hcomp : ∀ u : ℕ → E, (∀ d, ∀ ε > 0, ∃ J, ∀ i ≥ J, ∀ j ≥ J, p d (u i - u j) < ε) →
      ∃ x, ∀ d, Tendsto (fun j => p d (u j - x)) atTop (𝓝 0))
    (q : Seminorm ℂ E) (hq : ∀ (u : ℕ → E) (x : E), (∀ d, Tendsto (fun j => p d (u j - x)) atTop (𝓝 0)) →
      ∀ y : ℝ, (∀ j, q (u j) ≤ y) → q x ≤ y) :
    ∃ (d : ℕ) (C : ℝ≥0), ∀ x, q x ≤ C * p d x := by
  letI t : TopologicalSpace E := (SeminormFamily.moduleFilterBasis (𝕜 := ℂ) p).topology
  have hp : WithSeminorms p := ⟨rfl⟩
  haveI : IsTopologicalAddGroup E := hp.topologicalAddGroup
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  haveI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  haveI : ContinuousSMul ℂ E := hp.continuousSMul
  haveI : FirstCountableTopology E := hp.firstCountableTopology
  haveI : (𝓤 E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  haveI : CompleteSpace E := by
    refine UniformSpace.complete_of_cauchySeq_tendsto fun u hu => ?_
    rw [cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero, tendsto_comap_iff] at hu
    obtain ⟨x, hx⟩ := hcomp u fun d ε hε => by
      have h := (hp.tendsto_nhds _ 0).1 hu d ε hε
      obtain ⟨⟨N₁, N₂⟩, hN⟩ := eventually_atTop.1 h
      refine ⟨max N₁ N₂, fun i hi j hj => ?_⟩
      have := hN (j, i) (Prod.mk_le_mk.2 ⟨le_of_max_le_left hj, le_of_max_le_right hi⟩)
      simpa using this
    refine ⟨x, (hp.tendsto_nhds u x).2 fun d ε hε => ?_⟩
    exact (hx d).eventually (gt_mem_nhds hε)
  haveI : BarrelledSpace ℂ E := inferInstance
  have hlsc : LowerSemicontinuous q := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro y
    refine IsSeqClosed.isClosed fun u x hu hx => ?_
    exact hq u x (fun d => by
      have := ((hp.continuous_seminorm d).tendsto 0).comp ((tendsto_sub_nhds_zero_iff).2 hx)
      simpa [Function.comp_def] using this) y hu
  have hc : Continuous q := Seminorm.continuous_of_lowerSemicontinuous q hlsc
  obtain ⟨s, C, -, hle⟩ := Seminorm.bound_of_continuous hp q hc
  have hmono' : ∀ d d' x, d ≤ d' → p d x ≤ p d' x := fun d d' x h => by
    induction h with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (hmono _ x)
  refine ⟨s.sup id, C, fun x => (hle x).trans ?_⟩
  rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ C.2
  exact Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun i hi => hmono' _ _ _ (Finset.le_sup (f := id) hi)

end GlobalTheory.SobBaire

namespace GlobalTheory.SobBaire

open Filter Topology

theorem le_mul_sobO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ N : (WO S T → ℂ) → ℝ≥0∞, (∀ f ∈ thetaLevel ψ S T U, ∀ g ∈ thetaLevel ψ S T U, N (f + g) ≤ N f + N g) → (∀ (c : ℂ), ∀ f ∈ thetaLevel ψ S T U, N (c • f) = ‖c‖ₑ * N f) → (∀ f ∈ thetaLevel ψ S T U, N f ≠ ⊤) → (∀ (u : ℕ → WO S T → ℂ), (∀ j, u j ∈ thetaLevel ψ S T U) → ∀ f ∈ thetaLevel ψ S T U, (∀ d, Filter.Tendsto (fun j => sobO ψ θ μ 𝓕 d (u j - f)) Filter.atTop (nhds 0)) → N f ≤ Filter.liminf (fun j => N (u j)) Filter.atTop) → ∃ (d : ℕ) (C : ℝ≥0), ∀ f ∈ thetaLevel ψ S T U, N f ≤ C * sobO ψ θ μ 𝓕 d f := by
  intro D ψ hψ θ hθ S T μ 𝓕 hm U hU N hadd hsmul hfin hlsc
  have hB := _root_.GlobalTheory.ThetaComplete.complete D ψ hψ θ hθ S T μ 𝓕 hm U hU
  let E := thetaLevel ψ S T U
  have hsf : ∀ d (f : E), sobO ψ θ μ 𝓕 d (f : WO S T → ℂ) ≠ ⊤ := fun d f =>
    GlobalTheory.Size.sobO_ne_top hψ hθ hm.1 hm.2.1 f.2.1 d
  let p : ℕ → Seminorm ℂ E := fun d => Seminorm.of (fun f => (sobO ψ θ μ 𝓕 d (f : WO S T → ℂ)).toReal)
    (fun f g => by
      rw [← ENNReal.toReal_add (hsf d f) (hsf d g)]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hsf d f, hsf d g⟩)
        (GlobalTheory.Size.sobO_add_le hψ hθ f.2.1 g.2.1 d))
    (fun c f => by
      show (sobO ψ θ μ 𝓕 d (c • (f : WO S T → ℂ))).toReal = _
      rw [GlobalTheory.Size.sobO_smul, ENNReal.toReal_mul, toReal_enorm])
  have hp : ∀ d (f : E), p d f = (sobO ψ θ μ 𝓕 d (f : WO S T → ℂ)).toReal := fun _ _ => rfl
  let q : Seminorm ℂ E := Seminorm.of (fun f => (N f).toReal)
    (fun f g => by
      rw [← ENNReal.toReal_add (hfin f f.2) (hfin g g.2)]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin f f.2, hfin g g.2⟩) (hadd f f.2 g g.2))
    (fun c f => by
      show (N (c • (f : WO S T → ℂ))).toReal = _
      rw [hsmul c f f.2, ENNReal.toReal_mul, toReal_enorm])
  have hq : ∀ f : E, q f = (N f).toReal := fun _ => rfl
  obtain ⟨d, C, hC⟩ := exists_bound_of_complete p
    (fun d f => by
      rw [hp, hp]
      exact ENNReal.toReal_mono (hsf _ f) (GlobalTheory.Size.sobO_mono (Nat.le_succ d)))
    (fun u hu => by
      obtain ⟨f, hf, hlim⟩ := hB (fun j => (u j : WO S T → ℂ)) (fun j => (u j).2) fun d ε hε => by
        rcases eq_or_ne ε ⊤ with rfl | hεt
        · exact ⟨0, fun i _ j _ => lt_top_iff_ne_top.2 (hsf d (u i - u j))⟩
        obtain ⟨J, hJ⟩ := hu d ε.toReal (ENNReal.toReal_pos hε.ne' hεt)
        refine ⟨J, fun i hi j hj => ?_⟩
        have := hJ i hi j hj
        rw [hp] at this
        exact (ENNReal.toReal_lt_toReal (hsf d (u i - u j)) hεt).1 this
      refine ⟨⟨f, hf⟩, fun d => ?_⟩
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hlim d)
      simpa [hp, Function.comp_def] using this)
    q (fun u x hux y hy => by
      have hy0 : 0 ≤ y := (apply_nonneg q (u 0)).trans (hy 0)
      have hconv : ∀ d, Tendsto (fun j => sobO ψ θ μ 𝓕 d ((u j : WO S T → ℂ) - x)) atTop (𝓝 0) := fun d => by
        have h1 := hux d
        simp only [hp] at h1
        rw [← ENNReal.toReal_zero] at h1
        exact (ENNReal.tendsto_toReal_iff (fun j => hsf d (u j - x)) ENNReal.zero_ne_top).1 h1
      have h2 := hlsc (fun j => (u j : WO S T → ℂ)) (fun j => (u j).2) x x.2 hconv
      have h3 : Filter.liminf (fun j => N (u j : WO S T → ℂ)) atTop ≤ ENNReal.ofReal y :=
        Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun j => by
          rw [← ENNReal.ofReal_toReal (hfin _ (u j).2)]
          exact ENNReal.ofReal_le_ofReal ((hq _).symm.trans_le (hy j) |>.trans_eq' rfl))
      rw [hq]
      exact ENNReal.toReal_le_of_le_ofReal hy0 (h2.trans h3))
  refine ⟨d, C, fun f hf => ?_⟩
  have h := hC ⟨f, hf⟩
  rw [hq, hp] at h
  calc N f = ENNReal.ofReal (N f).toReal := (ENNReal.ofReal_toReal (hfin f hf)).symm
    _ ≤ ENNReal.ofReal (C * (sobO ψ θ μ 𝓕 d f).toReal) := ENNReal.ofReal_le_ofReal h
    _ = C * sobO ψ θ μ 𝓕 d f := by
      rw [ENNReal.ofReal_mul (NNReal.coe_nonneg C), ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_toReal (GlobalTheory.Size.sobO_ne_top hψ hθ hm.1 hm.2.1 hf.1 d)]

end GlobalTheory.SobBaire
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLocalLatticeIffOfFiniteAdelicCompletionMapStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_localLattice_iff_of_finiteAdelic_completion_map : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L L' : Submodule (𝓞 E) (Fin n → E)), L.FG → L'.FG → ∀ b : GL (Fin n) (TensorProduct F (Af F) E),
    (∀ w, w ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) ↔
      b.val *ᵥ w ∈ Formalism.MainNotions.StandardLattice.latHat F E (L' : Set (Fin n → E))) →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (z : Fin n → TensorProduct F (Fv F v) E), z ∈ latLoc F L v ↔
      (Formalism.UG.bc (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).toRingHom b).val *ᵥ z ∈ latLoc F L' v := by
  first | exact @GlobalTheory.Core.LocFromGlob.mem_latLoc_iff_of_latHat | exact GlobalTheory.Core.LocFromGlob.mem_latLoc_iff_of_latHat | (intros; apply GlobalTheory.Core.LocFromGlob.mem_latLoc_iff_of_latHat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittSourceProof
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.MixSourceFormulas

theorem mixed_source : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedSource D := by
  intro D ψ S S₀ T ρ d χS χT om om₀ ho ho₀ μ 𝓕 hμ f hf
  have hth : ∀ w f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w f) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ ho.std S T).1
  have hbr : ∀ (f : WO S T → ℂ) x, d.mixS T ψ μ 𝓕 f x = d.mixS T ψ μ 𝓕 (heisO ψ S T (d.extX T x) f) 0 :=
    fun f x => (_root_.GlobalTheory.Bridge.heis_bridge D ψ S S₀ T ρ d).2.2.2.2.2.2.1 μ 𝓕 f x
  have hmv := _root_.GlobalTheory.WMove.main D ψ S S₀ T ρ d χS χT om ho μ 𝓕 hμ f hf
  have hun := _root_.GlobalTheory.MixUnip.mixS_unip D ψ S S₀ T ρ d χS χT om ho μ 𝓕 hμ f hf
  have hlv := fun w => _root_.GlobalTheory.LeviOrigin.value_at_origin D ψ S S₀ T ρ d χS χT om om₀ ho ho₀ μ 𝓕 hμ (heisO ψ S T w f) (hth w f hf)
  unfold I195MixedCoordinates_3601ff04f10fcda6f28caf89.source at hmv
  unfold I195MixedCoordinates_34c45ee3f9864caed77cce75.source at hlv
  unfold HypDec.mixS HypDec.extX HypDec.extY HypDec.ext0 at hbr
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h x
    have hor := _root_.GlobalTheory.ValueAtOrigin.mixS_zero_target D ψ S S₀ T ρ d χS χT om om₀ ho ho₀ μ 𝓕 hμ h (heisO ψ S T (d.extX T (mt T h⁻¹ ⬝ x)) f) (hth _ f hf)
    unfold I195MixedCoordinates_6a77e1566d048881366221d8.source at hor
    unfold I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source
    rw [(hmv x).1 h, hor]
    exact congrArg (om₀ (1, h)) (hbr f (mt T h⁻¹ ⬝ x)).symm
  · intro g x
    have e := (hmv x).2.1 1 g
    rw [map_one, one_mul, Units.val_one, Matrix.mul_one] at e
    unfold I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source
    rw [e, (hlv _).1 g]
    exact congrArg (om₀ (g, 1)) (hbr f x).symm
  · intro a x
    have e := (hmv x).2.1 a 1
    rw [map_one, mul_one] at e
    unfold I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source
    rw [e, (hlv _).2.2 a]
    exact congrArg (fun (z : WO S₀ T → ℂ) => (((χT (Matrix.GeneralLinearGroup.det a) : Circle) : ℂ)⁻¹ * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ)) • z) (hbr f (x ⬝ a.1)).symm
  · intro b x
    exact (hun x).1 b
  · intro c x
    exact (hun x).2 c

end GlobalTheory.MixSourceFormulas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepLinearRelationsPeriodsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_doubleStep_linearRelations_periods : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), DoubleStep D → RapidVal D → ValMove D → PerSum D → c.Is → (∀ s, (t s).Is) → (∀ s, (t s).LocFin) → ValX t → TwoX t → RdX t → StepX t := by
  first | exact @GlobalTheory.SeeSawStep.stepX_of_laws | exact GlobalTheory.SeeSawStep.stepX_of_laws | (intros; apply GlobalTheory.SeeSawStep.stepX_of_laws <;> assumption)
end

