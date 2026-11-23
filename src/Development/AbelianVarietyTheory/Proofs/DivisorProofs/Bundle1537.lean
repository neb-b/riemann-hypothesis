module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0082
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0227
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteCombinationMulLiftByDegree
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.SmallRoute

theorem setIntegral_mul_right_of_left_inv {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] (Γ : Subgroup H) [Countable Γ] (ν : Measure H)
    [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] {fd : Set H} (hfd : IsFundamentalDomain Γ fd ν) {φ : H → ℂ}
    (hφ : ∀ γ ∈ Γ, ∀ u, φ (γ * u) = φ u) (hi : IntegrableOn φ fd ν) (k : H) :
    IntegrableOn (fun u => φ (u * k)) fd ν ∧ ∫ u in fd, φ (u * k) ∂ν = ∫ u in fd, φ u ∂ν := by
  have hmp : MeasurePreserving (· * k) ν ν := measurePreserving_mul_right ν k
  have hme : MeasurableEmbedding (· * k) := (MeasurableEquiv.mulRight k).measurableEmbedding
  have hfd' : IsFundamentalDomain Γ ((· * k⁻¹) ⁻¹' fd) ν := by
    refine hfd.preimage_of_equiv (measurePreserving_mul_right ν k⁻¹).quasiMeasurePreserving (e := id)
      Function.bijective_id ?_
    intro g x
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hinv : ∀ g : Γ, ∀ x, φ (g • x) = φ x := fun g x => hφ g g.2 x
  have hpre : (· * k) ⁻¹' ((· * k⁻¹) ⁻¹' fd) = fd := by
    ext u; simp
  refine ⟨?_, ?_⟩
  · have h1 : IntegrableOn φ ((· * k⁻¹) ⁻¹' fd) ν := (hfd'.integrableOn_iff hfd hinv).2 hi
    have h2 := (hmp.integrableOn_comp_preimage hme (f := φ) (s := (· * k⁻¹) ⁻¹' fd)).2 h1
    rw [hpre] at h2
    exact h2
  · have h3 := hmp.setIntegral_preimage_emb hme φ ((· * k⁻¹) ⁻¹' fd)
    rw [hpre] at h3
    rw [h3]
    exact hfd'.setIntegral_eq hfd hinv

end GlobalTheory.SmallRoute

namespace GlobalTheory.SmallRoute

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem mem_support_tensT (W : G.Weil) {X Y : Node} {p : Path T X Y} {τi : PolT G p →₀ ℂ} {τf : TotT G p} {d : PureT G p}
    (hd : d ∈ (tensT W τi τf).support) :
    ∃ d₀ ∈ τf.support, ∃ P, d = Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d₀ P := by
  classical
  unfold tensT at hd
  obtain ⟨P, -, hP⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hd)
  obtain ⟨d₀, hd₀, h⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hP)
  exact ⟨d₀, hd₀, P, Finset.mem_singleton.1 (Finsupp.support_single_subset h)⟩

end GlobalTheory.SmallRoute

namespace GlobalTheory.SmallRoute

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem theta_of_matched {W : G.Weil} {B : Frames G} {ρ : RealMatch W} {t : T} {i j : Fin D.R.m}
    {Θ : TotT G (routeBig t i j)} {Θ' : TotT G (routeSmall t i j)} (hΘ : IsMatched B t ρ i j Θ Θ')
    {d : PureT G (routeSmall t i j)} (hd : d ∈ Θ'.support) :
    IsThetaFunO W.ψ (G.pS (.chi i j)) (G.pT (.chi i j)) d.2 ∧
      IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) d.1.2 := by
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, ⟨φ₁, φ₂, hloc, -⟩, -⟩, -, rfl⟩ := hΘ
  obtain ⟨d₀, hd₀, P, rfl⟩ := mem_support_tensT W hd
  obtain ⟨h1, h2⟩ := hloc d₀ hd₀
  have v1 := ρ.vT_is t i j i.2.le j.2
  have v2 := ρ.vX_is i j i.2 j.2.le
  have t1 := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h1.2 v1.2.theta
  have t2 := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h2.2 v2.2.theta
  exact ⟨GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t2 _,
    GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t1 _⟩

end GlobalTheory.SmallRoute

namespace GlobalTheory.SmallRoute

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem outer_left (W : G.Weil) (M : Vol G) {t : T} {i j : Fin D.R.m} {d : PureT G (routeSmall t i j)}
    (h2 : IsThetaFunO W.ψ (G.pS (.chi i j)) (G.pT (.chi i j)) d.2)
    (h1 : IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) d.1.2) (F : Fn G (.grid i (j + 1)))
    (g₁ : GA D (G.V (.grid (i + 1) j))) {γ : GA D (G.V (.grid i j))} (hγ : γ ∈ GQ (G.V (.grid i j)))
    (u : GA D (G.V (.grid i j))) : outer W M d F g₁ (γ * u) = outer W M d F g₁ u := by
  have hc := W.om_is (.chi (i : ℕ) j) ⟨i.2, j.2.le⟩
  have hm := W.om_is (.mu t (i : ℕ) j) ⟨i.2.le, j.2⟩
  unfold outer
  congr 1
  · show thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) (γ * u) d.2 = thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) u d.2
    unfold thetaKO
    have e : ((negGA _ g₁, γ * u) : GA D (G.pS (.chi (i : ℕ) j)) × GA D (G.pT (.chi (i : ℕ) j))) =
        (1, γ) * (negGA _ g₁, u) := by simp
    rw [e, map_mul, Module.End.mul_apply]
    exact hc.om_aut 1 (one_mem _) γ hγ _ (hc.om_pres _ _ h2)
  · refine integral_congr_ae (.of_forall fun g => ?_)
    show thetaKO (W.om (.mu t (i : ℕ) j)) (γ * u) g d.1.2 * F g = thetaKO (W.om (.mu t (i : ℕ) j)) u g d.1.2 * F g
    unfold thetaKO
    have e : ((γ * u, g) : GA D (G.pS (.mu t (i : ℕ) j)) × GA D (G.pT (.mu t (i : ℕ) j))) = (γ, 1) * (u, g) := by simp
    rw [e, map_mul, Module.End.mul_apply, hm.om_aut γ hγ 1 (one_mem _) _ (hm.om_pres _ _ h1)]

end GlobalTheory.SmallRoute

namespace GlobalTheory.SmallRoute

theorem zdeg_mul_liftT : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (F : Fn G (.grid i (j + 1))) (hF : IsAutFunSm W.θ _ F) (hB : TotConv W M _ Θ' F) (g₁ : GA D (G.V (.grid (i + 1) j)))
    (z : GA D (G.V (.grid i j)) →₀ ℂ),
    (∀ d ∈ Θ'.support, ∀ k, IntegrableOn (fun u => GlobalTheory.SmallRoute.outer W M d F g₁ (u * k)) (M.fd (.grid i j)) (M.ν (.grid i j))) ∧
    zdeg z * liftT W M (routeSmall t i j) Θ' F g₁ =
      Θ'.sum fun d c => c * ∫ u in M.fd (.grid i j), translates z (GlobalTheory.SmallRoute.outer W M d F g₁) u ∂M.ν (.grid i j) := by
  intro D T L sc G μ₀ hL W B ρ t i j M hM Θ Θ' hΘ F hF hB g₁ z
  obtain ⟨hH, hfd⟩ := (hM.vtx (.grid i j) ⟨i.2.le, j.2.le⟩).haar_fund
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.grid i j))
  haveI := hH
  haveI := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ (M.ν (.grid i j)) hH
  have key : ∀ d ∈ Θ'.support, ∀ k, IntegrableOn (fun u => outer W M d F g₁ (u * k)) (M.fd (.grid i j)) (M.ν (.grid i j)) ∧
      ∫ u in M.fd (.grid i j), outer W M d F g₁ (u * k) ∂M.ν (.grid i j) =
        ∫ u in M.fd (.grid i j), outer W M d F g₁ u ∂M.ν (.grid i j) := fun d hd k => by
    obtain ⟨h2, h1⟩ := theta_of_matched hΘ hd
    refine setIntegral_mul_right_of_left_inv (GQ (G.V (.grid i j))) (M.ν (.grid i j)) hfd
      (fun γ hγ u => outer_left W M h2 h1 F g₁ hγ u) ?_ k
    exact (hB d hd).2 g₁
  refine ⟨fun d hd k => (key d hd k).1, ?_⟩
  rw [liftT_routeSmall, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have e : ∫ u in M.fd (.grid i j), translates z (outer W M d F g₁) u ∂M.ν (.grid i j) =
      zdeg z * ∫ u in M.fd (.grid i j), outer W M d F g₁ u ∂M.ν (.grid i j) := by
    unfold translates zdeg
    simp only [Finsupp.sum]
    rw [integral_finsetSum _ fun k _ => ((key d hd k).1.integrable.const_mul _),
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, (key d hd k).2]
  rw [e]
  ring

end GlobalTheory.SmallRoute
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteSumTranslatedOuterIntegralsEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SmallRoute

theorem sum_integral_translates_outer_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ' : TotT G (routeSmall t i j))
    (F : Fn G (.grid i (j + 1))) (hB : TotConv W M _ Θ' F) (g₁ : GA D (G.V (.grid (i + 1) j))) (z : GA D (G.V (.grid i j)) →₀ ℂ)
    (hI : ∀ d ∈ Θ'.support, ∀ k, IntegrableOn (fun u => GlobalTheory.SmallRoute.outer W M d F g₁ (u * k)) (M.fd (.grid i j)) (M.ν (.grid i j)))
    (hJ : Integrable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) => F p.1 * translates z (kerSmall W Θ' p.1 g₁) p.2)
      (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod ((M.ν (.grid i j)).restrict (M.fd (.grid i j))))),
    (Θ'.sum fun d c => c * ∫ u in M.fd (.grid i j), translates z (GlobalTheory.SmallRoute.outer W M d F g₁) u ∂M.ν (.grid i j)) =
      ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid i j),
        translates z (kerSmall W Θ' g g₁) u ∂M.ν (.grid i j) ∂M.ν (.grid i (j + 1)) := by
  intro D T L sc G μ₀ hL W t i j M hM Θ' F hB g₁ z hI hJ
  classical
  have hσ : ∀ X : Node, X.InRange D.R.m → SigmaFinite (M.ν X) := fun X hX => by
    obtain ⟨h1, h2, -⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D (G.V X)
    haveI := (hM.vtx X hX).haar_fund.1
    infer_instance
  haveI := hσ (.grid i (j + 1)) ⟨i.2.le, j.2⟩
  haveI := hσ (.grid i j) ⟨i.2.le, j.2.le⟩
  have hpt : ∀ u, ∫ g in M.fd (.grid i (j + 1)), F g * translates z (kerSmall W Θ' g g₁) u ∂M.ν (.grid i (j + 1)) =
      Θ'.sum fun d c => c * translates z (outer W M d F g₁) u := by
    intro u
    have hint : ∀ d ∈ Θ'.support, ∀ k, IntegrableOn (fun g => W.kerA (.down t i j) d.1.2 g (u * k) * F g)
        (M.fd (.grid i (j + 1))) (M.ν (.grid i (j + 1))) := fun d hd k => (hB d hd).1.2 (u * k)
    have e : ∀ g, F g * translates z (kerSmall W Θ' g g₁) u = ∑ k ∈ z.support, ∑ d ∈ Θ'.support,
        z k * (Θ' d * (W.kerA (.right i j) d.2 (u * k) g₁ * (W.kerA (.down t i j) d.1.2 g (u * k) * F g))) := by
      intro g
      simp only [translates, kerSmall, Finsupp.sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun d _ => by ring
    simp_rw [e]
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun d hd =>
      (((hint d hd k).const_mul _).const_mul _).const_mul _]
    simp_rw [integral_finsetSum _ fun d hd => (((hint d hd _).const_mul _).const_mul _).const_mul _]
    simp only [integral_const_mul, translates, outer, Finsupp.sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun k _ => by ring
  have hint2 : ∀ d ∈ Θ'.support, Integrable (translates z (outer W M d F g₁))
      ((M.ν (.grid i j)).restrict (M.fd (.grid i j))) := fun d hd =>
    integrable_finsetSum _ fun k _ => (hI d hd k).const_mul _
  symm
  calc ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid i j), translates z (kerSmall W Θ' g g₁) u ∂M.ν (.grid i j)
        ∂M.ν (.grid i (j + 1))
      = ∫ g in M.fd (.grid i (j + 1)), ∫ u in M.fd (.grid i j), F g * translates z (kerSmall W Θ' g g₁) u ∂M.ν (.grid i j)
        ∂M.ν (.grid i (j + 1)) := by simp_rw [integral_const_mul]
    _ = ∫ u in M.fd (.grid i j), ∫ g in M.fd (.grid i (j + 1)), F g * translates z (kerSmall W Θ' g g₁) u
        ∂M.ν (.grid i (j + 1)) ∂M.ν (.grid i j) := integral_integral_swap hJ
    _ = ∫ u in M.fd (.grid i j), (Θ'.sum fun d c => c * translates z (outer W M d F g₁) u) ∂M.ν (.grid i j) := by
        simp_rw [hpt]
    _ = _ := by
        simp only [Finsupp.sum]
        rw [integral_finsetSum _ fun d hd => (hint2 d hd).const_mul _]
        simp_rw [integral_const_mul]

end GlobalTheory.SmallRoute

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemPolarizationIdealOfMemConj
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped nonZeroDivisors

namespace GlobalTheory

open scoped Pointwise

namespace StarAAbar

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x :=
  D.host.φ₀.injective (by
    rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply, Complex.conj_conj])

theorem coe_smul {L : Type} [Field L] [NumberField L] (σ : Gal(L/ℚ)) (X : 𝓞 L) :
    ((σ • X : 𝓞 L) : L) = σ (X : L) := rfl

theorem bb_ne_bot {D : D7} : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h1 := D.host.𝔟_spec.1
  rw [h] at h1
  simp only [Submodule.bot_mul] at h1
  exact differentIdeal_ne_bot h1

theorem conj_bb_ne_bot {D : D7} : D.host.conj • D.host.𝔟 ≠ ⊥ := by
  intro h
  apply bb_ne_bot (D := D)
  have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h
  simpa using this

theorem conj_inv_smul {D : D7} (x : 𝓞 D.host.E) : D.host.conj⁻¹ • x = D.host.conj • x := by
  have h : D.host.conj⁻¹ = D.host.conj := by
    rw [inv_eq_iff_mul_eq_one]
    exact AlgEquiv.ext fun y => conj_conj D y
  rw [h]

end StarAAbar


set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 800000 in
theorem star_mem_AA_of_mem_AAbar : ∀ {D : D7} {c : D.host.E}, c ∈ D.host.AAbar → star c ∈ D.host.AA := by
  intro D c hc
  have hJ : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 StarAAbar.bb_ne_bot
  have hJc : ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 StarAAbar.conj_bb_ne_bot

  have h1 : ∀ y ∈ D.host.conj • D.host.𝔟, c * (y : D.host.E) ∈
      ((D.host.conj • D.host.ccE : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    intro y hy
    have hyJ : (y : D.host.E) ∈ ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :=
      (FractionalIdeal.mem_coeIdeal _).2 ⟨y, hy, rfl⟩
    have := FractionalIdeal.mul_mem_mul hc hyJ
    unfold Host.AAbar at this
    rwa [mul_assoc, inv_mul_cancel₀ hJc, mul_one] at this

  have h2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (star c) *
      ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≤
      ((D.host.ccE : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [FractionalIdeal.mul_le]
    intro i hi j hj
    obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
    obtain ⟨j', hj', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hj
    have hy : D.host.conj • j' ∈ D.host.conj • D.host.𝔟 := Ideal.smul_mem_pointwise_smul _ _ _ hj'
    obtain ⟨x, hx, hxe⟩ := (FractionalIdeal.mem_coeIdeal _).1 (h1 _ hy)
    have hxs : D.host.conj • x ∈ D.host.ccE := by
      have := (Ideal.mem_pointwise_smul_iff_inv_smul_mem).1 hx
      rwa [StarAAbar.conj_inv_smul] at this
    have key : star c * algebraMap (𝓞 D.host.E) D.host.E j' = algebraMap (𝓞 D.host.E) D.host.E (D.host.conj • x) := by
      show star c * (j' : D.host.E) = ((D.host.conj • x : 𝓞 D.host.E) : D.host.E)
      rw [StarAAbar.coe_smul, show ((x : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E x from rfl, hxe,
        map_mul, StarAAbar.coe_smul, StarAAbar.conj_conj, StarAAbar.star_eq_conj]
    rw [smul_mul_assoc, key]
    exact Submodule.smul_mem _ _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, hxs, rfl⟩)
  have h3 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (star c) ≤ D.host.AA := by
    unfold Host.AA Host.AA0
    calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (star c)
        = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (star c) *
          ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) *
          ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hJ, mul_one]
      _ ≤ _ := by gcongr
  exact h3 (FractionalIdeal.mem_spanSingleton_self _ _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstMemAndComm
section
noncomputable section

open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilSchComm

def lmul {R : Type} [CommRing R] {m : ℕ} (n : ℕ) (A : Matrix (Fin m) (Fin m) R) (z : Fin m → Fin n → R) :
    Fin m → Fin n → R := fun i j => ∑ c, A i c * z c j

theorem lmul_lmul {R : Type} [CommRing R] {m n : ℕ} {A B : Matrix (Fin m) (Fin m) R} (h : A * B = 1)
    (z : Fin m → Fin n → R) : lmul n A (lmul n B z) = z := by
  change (A * (B * Matrix.of z) : Matrix (Fin m) (Fin n) R) = Matrix.of z
  rw [← Matrix.mul_assoc, h, Matrix.one_mul]

theorem continuous_lmul {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {m : ℕ} (n : ℕ)
    (A : Matrix (Fin m) (Fin m) R) : Continuous (lmul n A) := by
  unfold lmul
  fun_prop

def lmulHomeo {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {m : ℕ} (n : ℕ)
    {A B : Matrix (Fin m) (Fin m) R} (h : A * B = 1) : (Fin m → Fin n → R) ≃ₜ (Fin m → Fin n → R) where
  toFun := lmul n A
  invFun := lmul n B
  left_inv := lmul_lmul (mul_eq_one_comm.1 h)
  right_inv := lmul_lmul h
  continuous_toFun := continuous_lmul n A
  continuous_invFun := continuous_lmul n B

def lmulFam {T : Type} {m : ℕ} (n : ℕ) {A B : T → Matrix (Fin m) (Fin m) ℂ} (h : ∀ τ, A τ * B τ = 1) :
    (T → Fin m → Fin n → ℂ) ≃ₗ[ℝ] (T → Fin m → Fin n → ℂ) where
  toFun z τ := lmul n (A τ) (z τ)
  invFun z τ := lmul n (B τ) (z τ)
  map_add' z z' := by
    funext τ i j
    simp [lmul, mul_add, Finset.sum_add_distrib]
  map_smul' c z := by
    funext τ i j
    simp [lmul, Finset.mul_sum, mul_left_comm]
  left_inv z := funext fun τ => lmul_lmul (mul_eq_one_comm.1 (h τ)) (z τ)
  right_inv z := funext fun τ => lmul_lmul (h τ) (z τ)

theorem map_mul_entry {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {m n : ℕ} (M : Matrix (Fin m) (Fin m) R)
    (x : Matrix (Fin m) (Fin n) R) : (fun i j => φ ((M * x) i j)) = lmul n (M.map φ) fun i j => φ (x i j) := by
  funext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lmul, Matrix.mul_apply, map_sum, map_mul, Matrix.map_apply]

variable {D : D7} {n : ℕ}

theorem map_cancel {R : Type} [CommRing R] (φ : AE D →+* R) (V : HSp D) (g : GA D V) :
    (mt V g).map φ * (mt V g⁻¹).map φ = 1 := by
  have h : mt V g * mt V g⁻¹ = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [map_inv]
    exact Units.mul_inv _
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero φ) (map_one φ)]

theorem comp_mem (θ : InfFam D) (V : HSp D) (h : GA D V) {Φ : Mx D V.rank n → ℂ} (hΦ : Φ ∈ schwartzA θ V.rank n) :
    (fun x : Mx D V.rank n => Φ (mt V h ⬝ x)) ∈ schwartzA θ V.rank n := by
  induction hΦ using Submodule.span_induction with
  | zero => exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
  | smul c Φ _ h1 => exact Submodule.smul_mem _ c h1
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
    refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      (lmulFam n fun τ => map_cancel ((θ τ).comp (infPart D)) V h).toContinuousLinearEquiv f,
      g ∘ lmulHomeo n (map_cancel (finPart D) V h), ⟨hg.1.comp_continuous (lmulHomeo n _).continuous, hg.2.comp_homeomorph _⟩, funext fun x => ?_⟩
    have e1 := fun τ => map_mul_entry ((θ τ).comp (infPart D)) (mt V h) x
    have e2 := map_mul_entry (finPart D) (mt V h) x
    exact congrArg₂ (· * ·) (congrArg f (funext e1)) (congrArg g e2)

theorem inner_mul (V : HSp D) (h : GA D V) (x y : Mx D V.rank n) :
    StdUnn.inner V (mt V h ⬝ x) (mt V h ⬝ y) = StdUnn.inner V x y := by
  unfold StdUnn.inner
  rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA V), ← Matrix.mul_assoc (adj (mt V h)), mt_unitary]

def subst (θ : InfFam D) (V : HSp D) (n : ℕ) (h : GA D V) : Module.End ℂ (schwartzA θ V.rank n) where
  toFun Φ := ⟨fun x => Φ.1 (mt V h ⬝ x), comp_mem θ V h Φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem subst_mem_and_comm : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D), IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∀ ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n), StdUnn.IsWeilSch ψ χ θ V μ ω → ∀ h : GA D V, (∀ Φ ∈ schwartzA θ V.rank n, (fun x : Mx D V.rank n => Φ (mt V h ⬝ x)) ∈ schwartzA θ V.rank n) ∧ ∀ (g : StdUnn.G D n) (Φ Ψ : schwartzA θ V.rank n), (∀ x, Ψ.1 x = Φ.1 (mt V h ⬝ x)) → ∀ x, (ω g Ψ).1 x = (ω g Φ).1 (mt V h ⬝ x) := by
  intro D n V ψ χ θ _ μ 𝓕 hμ ω hω h
  refine ⟨fun Φ hΦ => comp_mem θ V h hΦ, fun g Φ Ψ hΨ x => ?_⟩
  let S : Subgroup (StdUnn.G D n) :=
    { carrier := {g | Commute (ω g) (subst θ V n h)}
      one_mem' := by
        change Commute (ω 1) _
        rw [map_one]
        exact Commute.one_left _
      mul_mem' := fun {a b} ha hb => by
        change Commute (ω (a * b)) _
        rw [map_mul]
        exact Commute.mul_left ha hb
      inv_mem' := fun {a} ha => Commute.units_inv_left (u := ω.toHomUnits a) ha }
  have hS : S = ⊤ := by
    refine StdUnn.eq_top_of_levi_unip_weyl D n S (fun g a hg => ?_) (fun g b hg => ?_) (fun g hg => ?_) <;>
      refine LinearMap.ext fun Φ => Subtype.ext (funext fun x => ?_) <;>
      change (ω g (subst θ V n h Φ)).1 x = (ω g Φ).1 (mt V h ⬝ x)
    · rw [hω.levi g a hg, hω.levi g a hg, Matrix.mul_assoc]
      rfl
    · rw [hω.unip g b hg, hω.unip g b hg, inner_mul]
      rfl
    · rw [hω.weyl g hg, hω.weyl g hg, ← GlobalTheory.Twist.LeftHaar.integral_left_unitary D V n h μ hμ.1
        (fun y => Φ.1 y * ψ (StdUnn.trA (Matrix.trace (StdUnn.inner V (mt V h ⬝ x) y))))]
      refine congrArg (integral μ) (funext fun y => ?_)
      exact congrArg (fun t => Φ.1 (mt V h ⬝ y) * ψ (StdUnn.trA (Matrix.trace t))) (inner_mul V h x y).symm
  have hg : g ∈ S := hS ▸ Subgroup.mem_top g
  obtain rfl : Ψ = subst θ V n h Φ := Subtype.ext (funext hΨ)
  exact congrFun (congrArg Subtype.val (LinearMap.congr_fun (show Commute (ω g) (subst θ V n h) from hg).eq Φ)) x

end GlobalTheory.WeilSchComm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameUnipotentRadicalClosedFundDomainMassOne
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResidueEisenstein

theorem unipRad_frame_closed_mass_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → IsClosed (unipRad σ J X : Set (GAd σ J)) ∧ ∃ (ν : Measure (unipRad σ J X)) (DN : Set (unipRad σ J X)), ν.IsHaarMeasure ∧ IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J X)) DN ν ∧ ν DN = 1 := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW
  have e : X = X.submatrix id (Fin.castLE (le_refl (r + 1))) := by
    ext i j
    rfl
  have hC : GlobalTheory.UAut.IsIsoCols σ J X := e ▸ GlobalTheory.UAut.isIsoCols_of_isWittFrame hW (sigma_sigma h) hJ _
  haveI := GlobalTheory.UAut.locallyCompact_unipRad h hJ hC
  exact ⟨GlobalTheory.UAut.unipFlag_const (σ := σ) (J := J) X 0 ▸ GlobalTheory.UAut.isClosed_unipFlag hJ (sigma_sigma h) hC _,
    GlobalTheory.UAut.exists_mass_one (GlobalTheory.UAut.cocompact_unipRad h hJ hC)⟩

end GlobalTheory.ResidueEisenstein
end

