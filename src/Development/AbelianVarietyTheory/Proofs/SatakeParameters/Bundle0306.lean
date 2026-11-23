module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0374
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0292
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LatticeDataThicknessBound
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0653
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0644
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0154
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExtensionVectorThetaCompatible
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EigTransport

theorem frame_hyp : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ}
    (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ps → ∀ (sp : SplitPlace D.host.E)
    (κ : Formalism.AUTREP.GAf D.host.E n), Ps.ψ κ ∈ GlobalTheory.Hk3.hyp V sp.w ↔ κ ∈ Umax D.host.E n ∧ TrivOutside {sp.v} κ := _root_.GlobalTheory.FrameHyp.mem_hyp_iff

theorem exists_std : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ}
    (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ps → V.rank = n → ∀ (sp : SplitPlace D.host.E)
    (ϖ : (sp.v).adicCompletion (maximalRealSubfield D.host.E)), Formalism.AUTREP.IsUnif D.host.E sp.v ϖ →
    ∀ k ≤ n, ∃ x₀ ∈ Formalism.AUTREP.tSet D.host.E n sp ϖ k, ∃ (e f : Formalism.L2.Theta.AE D) (ϖ' : 𝓞 D.host.E),
      Formalism.IndefR.Mult.IsPrimeIdem sp.w e f ∧ ϖ' ∈ sp.w.asIdeal ∧ ϖ' ∉ sp.w.asIdeal ^ 2 ∧
        Formalism.IndefR.Mult.SuppF V f (Ps.ψ x₀) ∧
        Formalism.IndefR.Mult.DivAt V e (ϖ' : D.host.E) (List.replicate k 1 ++ List.replicate (n - k) 0) (Ps.ψ x₀) := _root_.GlobalTheory.StdEltLabel.std_elt_label

theorem tSet_dc : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (sp : SplitPlace L)
    (ϖ : (sp.v).adicCompletion (maximalRealSubfield L)) (k : ℕ), ∀ x₀ ∈ Formalism.AUTREP.tSet L n sp ϖ k,
    ∀ κ, κ ∈ Formalism.AUTREP.tSet L n sp ϖ k ↔ ∃ k₁, (k₁ ∈ Umax L n ∧ TrivOutside {sp.v} k₁) ∧
      ∃ k₂, (k₂ ∈ Umax L n ∧ TrivOutside {sp.v} k₂) ∧ κ = k₁ * x₀ * k₂ := _root_.GlobalTheory.TSetDoubleCoset.mem_tSet_iff

theorem pairwise_lab (k m : ℕ) : List.Pairwise (fun a b : ℤ => b ≤ a) (List.replicate k 1 ++ List.replicate m 0) := by
  rw [List.pairwise_append]
  refine ⟨List.pairwise_replicate.2 (Or.inr le_rfl), List.pairwise_replicate.2 (Or.inr le_rfl), ?_⟩
  intro a ha b hb
  rw [List.eq_of_mem_replicate ha, List.eq_of_mem_replicate hb]
  norm_num

end GlobalTheory.EigTransport

namespace GlobalTheory.EigTransport

theorem isLab_std {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ}
    (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n) (hs : GlobalTheory.NJoin.StdFrame hF Ps) (hn : V.rank = n) (sp : SplitPlace D.host.E)
    (ϖ : (sp.v).adicCompletion (maximalRealSubfield D.host.E)) (hϖ : Formalism.AUTREP.IsUnif D.host.E sp.v ϖ)
    (k : ℕ) (hk : k ≤ n) :
    GlobalTheory.Hk3.IsLab V sp.w (List.replicate k 1 ++ List.replicate (n - k) 0) := by
  obtain ⟨x₀, -, e, f, ϖ', h1, h2, h3, h4, h5⟩ := exists_std hF Ps hs hn sp ϖ hϖ k hk
  exact GlobalTheory.SphLabelOps.isLab_of_divAt h1 h2 h3 (pairwise_lab _ _) h4 h5

theorem tSet_iff {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ}
    (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n) (hs : GlobalTheory.NJoin.StdFrame hF Ps) (hn : V.rank = n) (sp : SplitPlace D.host.E)
    (ϖ : (sp.v).adicCompletion (maximalRealSubfield D.host.E)) (hϖ : Formalism.AUTREP.IsUnif D.host.E sp.v ϖ)
    (k : ℕ) (hk : k ≤ n) (κ : Formalism.AUTREP.GAf D.host.E n) :
    κ ∈ Formalism.AUTREP.tSet D.host.E n sp ϖ k ↔
      ∃ γ ∈ GlobalTheory.Hk3.rep V sp.w (List.replicate k 1 ++ List.replicate (n - k) 0),
        γ⁻¹ * Ps.ψ κ ∈ GlobalTheory.Hk3.hyp V sp.w := by
  obtain ⟨x₀, hx₀, e, f, ϖ', h1, h2, h3, h4, h5⟩ := exists_std hF Ps hs hn sp ϖ hϖ k hk
  have hLab := GlobalTheory.SphLabelOps.isLab_of_divAt h1 h2 h3 (pairwise_lab _ _) h4 h5
  obtain ⟨K, hK⟩ := GlobalTheory.SphLabelOps.exists_hyp V sp.w
  have hR := GlobalTheory.SphLabelOps.reps_of_sphOp hK h1 h2 h3 h4 h5 (GlobalTheory.SphLabelOps.sphOp_rep hLab)
  have memK : ∀ l, l ∈ K ↔ l ∈ GlobalTheory.Hk3.hyp V sp.w := fun l => by rw [hK]; rfl
  have pre : ∀ l ∈ K, ∃ m, (m ∈ Umax D.host.E n ∧ TrivOutside {sp.v} m) ∧ Ps.ψ m = l := by
    intro l hl
    have hl' := (memK l).1 hl
    obtain ⟨m, rfl⟩ := Ps.onto l hl'.1.1
    exact ⟨m, (frame_hyp hF Ps hs sp m).1 hl', rfl⟩
  have img : ∀ m, (m ∈ Umax D.host.E n ∧ TrivOutside {sp.v} m) → Ps.ψ m ∈ K := fun m hm =>
    (memK _).2 ((frame_hyp hF Ps hs sp m).2 hm)
  constructor
  · intro hκ
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (tSet_dc n sp ϖ k x₀ hx₀ κ).1 hκ
    obtain ⟨γ, ⟨hγ, hm⟩, -⟩ := hR.2 (Ps.ψ (k₁ * x₀ * k₂))
      ⟨Ps.ψ k₁, img _ hk₁, Ps.ψ k₂, img _ hk₂, by rw [map_mul, map_mul]⟩
    exact ⟨γ, hγ, (memK _).1 hm⟩
  · rintro ⟨γ, hγ, hm⟩
    obtain ⟨l₁, hl₁, l₂, hl₂, hγe⟩ := hR.1 γ hγ
    have hl : γ⁻¹ * Ps.ψ κ ∈ K := (memK _).2 hm
    obtain ⟨m₁, hm₁, e₁⟩ := pre l₁ hl₁
    obtain ⟨m₂, hm₂, e₂⟩ := pre (l₂ * (γ⁻¹ * Ps.ψ κ)) (mul_mem hl₂ hl)
    refine (tSet_dc n sp ϖ k x₀ hx₀ κ).2 ⟨m₁, hm₁, m₂, hm₂, Ps.inj ?_⟩
    rw [map_mul, map_mul, e₁, e₂, ← mul_assoc, ← mul_assoc, ← hγe, mul_inv_cancel, one_mul]

end GlobalTheory.EigTransport

namespace GlobalTheory.EigTransport


open Classical in
theorem finsum_cosets {G W ι : Type} [Group G] [AddCommGroup W] (J : Subgroup G) (T : Set G) (R : Finset ι)
    (x : ι → G) (F : G → W) (h1 : ∀ γ ∈ R, x γ ∈ T) (h2 : ∀ y ∈ T, ∃ γ ∈ R, (x γ)⁻¹ * y ∈ J)
    (h3 : ∀ γ ∈ R, ∀ γ' ∈ R, (x γ)⁻¹ * x γ' ∈ J → γ = γ')
    (hF : ∀ y ∈ T, ∀ y' ∈ T, y⁻¹ * y' ∈ J → ∀ g, F (g * y') = F (g * y)) (g : G) :
    (∑ᶠ c : G ⧸ J, if hc : ∃ y ∈ T, (y : G ⧸ J) = c then F (g * hc.choose) else 0) =
      ∑ γ ∈ R, F (g * x γ) := by
  classical
  have hsupp : (Function.support fun c : G ⧸ J =>
      if hc : ∃ y ∈ T, (y : G ⧸ J) = c then F (g * hc.choose) else 0) ⊆
      ↑(R.image fun γ => (x γ : G ⧸ J)) := by
    intro c hc
    by_cases h : ∃ y ∈ T, (y : G ⧸ J) = c
    · obtain ⟨y, hy, rfl⟩ := h
      obtain ⟨γ, hγ, hm⟩ := h2 y hy
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨γ, hγ, QuotientGroup.eq.2 hm⟩)
    · exact absurd (by simp [h]) hc
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    have hc : ∃ y ∈ T, (y : G ⧸ J) = (x γ : G ⧸ J) := ⟨x γ, h1 γ hγ, rfl⟩
    rw [dif_pos hc]
    obtain ⟨hy, he⟩ := hc.choose_spec
    exact (hF _ hy _ (h1 γ hγ) (QuotientGroup.eq.1 he) g).symm
  · intro γ hγ γ' hγ' e
    exact h3 γ hγ γ' hγ' (QuotientGroup.eq.1 e)

theorem triv_mul {D : D7} {n : ℕ} {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))}
    {x y : Formalism.AUTREP.GAf D.host.E n} (hx : TrivOutside T x) (hy : TrivOutside T y) : TrivOutside T (x * y) :=
  fun v hv => by
    have e : (x * y).1.1 = x.1.1 * y.1.1 := rfl
    show (x * y).1.1.map (compAt D.host.E v) = 1
    rw [e, Matrix.map_mul]
    rw [show x.1.1.map (compAt D.host.E v) = 1 from hx v hv, show y.1.1.map (compAt D.host.E v) = 1 from hy v hv, mul_one]

theorem triv_inv {D : D7} {n : ℕ} {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))}
    {x : Formalism.AUTREP.GAf D.host.E n} (hx : TrivOutside T x) : TrivOutside T x⁻¹ := fun v hv => by
  have e : (x⁻¹).1.1.map (compAt D.host.E v) * x.1.1.map (compAt D.host.E v) = 1 := by
    rw [← Matrix.map_mul]
    have : (x⁻¹).1.1 * x.1.1 = 1 := by
      show (x⁻¹ * x).1.1 = 1
      rw [inv_mul_cancel]
      rfl
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  show (x⁻¹).1.1.map (compAt D.host.E v) = 1
  rwa [show x.1.1.map (compAt D.host.E v) = 1 from hx v hv, mul_one] at e

theorem rep_inj {D : D7} (V : TH.HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    (hd : GlobalTheory.Hk3.IsLab V P d) : ∀ γ ∈ GlobalTheory.Hk3.rep V P d, ∀ γ' ∈ GlobalTheory.Hk3.rep V P d,
      γ⁻¹ * γ' ∈ GlobalTheory.Hk3.hyp V P → γ = γ' := by
  obtain ⟨K, hK⟩ := GlobalTheory.SphLabelOps.exists_hyp V P
  obtain ⟨g₀, -, hR⟩ := GlobalTheory.SphLabelOps.exists_reps hK (GlobalTheory.SphLabelOps.sphOp_rep hd)
  intro γ hγ γ' hγ' hm
  rw [hK] at hm
  exact (hR.2 γ' (hR.1 γ' hγ')).unique ⟨hγ, hm⟩ ⟨hγ', by rw [inv_mul_cancel]; exact one_mem K⟩

end GlobalTheory.EigTransport

namespace GlobalTheory.EigTransport

theorem sum_single {M : Type} [AddCommGroup M] [Module ℂ M] (d : List ℤ) (G : List ℤ → M) :
    ∑ d' ∈ (Finsupp.single d (1 : ℂ)).support, (Finsupp.single d (1 : ℂ)) d' • G d' = G d := by
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]
end GlobalTheory.EigTransport

namespace GlobalTheory.EigTransport

theorem eig_sum {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (X : GlobalTheory.NJoin.RealAt D cf nch tp) {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m)
    (f : D.what₂.Mt μ (j.1 + 1)) (y) (hy : X.R.extV j (X.tupT μ) y = X.fn hμ j f) (h)
    (hOps : GlobalTheory.Hk3.IsOpsV X.R j (X.tupT μ) h) (s : GlobalTheory.DownLift.Sys D)
    (hEig : GlobalTheory.DownLift.IsEigV X.R j (X.tupT μ) h s y) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hG : GlobalTheory.Hk3.Good X.R (X.tupT μ) P) (d : List ℤ) (hd : GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) P d)
    (g : Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Vc D j)) :
    ∑ a ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) P d, X.fn hμ j f (g * a) = s P d • X.fn hμ j f g := by
  have hc : (X.R.cV j).Is := X.given.core.models.cV j
  have e1 := hOps P hG (Finsupp.single d 1) y
  have e2 := hEig P d hG hd
  have e4 : GlobalTheory.Hk3.hkF (Formalism.IndefR.Links.Vc D j) P (Finsupp.single d 1) ((X.R.HV j (X.tupT μ)).e y) =
      s P d • (X.R.HV j (X.tupT μ)).e y :=
    e1.symm.trans ((congrArg (X.R.HV j (X.tupT μ)).e e2).trans (map_smul _ _ _))
  have e3 := ((congrArg (fun F => (X.R.cV j).ext F g) e4).symm.trans
    (GlobalTheory.DefLiftHecke.ext_hkF (X.R.cV j) hc P (Finsupp.single d 1) ((X.R.HV j (X.tupT μ)).e y) g)).trans
    (sum_single d _)
  have hy2 : ∀ x, (X.R.cV j).ext ((X.R.HV j (X.tupT μ)).e y) x = X.fn hμ j f x := fun x =>
    (show X.R.extV j (X.tupT μ) y x = (X.R.cV j).ext ((X.R.HV j (X.tupT μ)).e y) x from rfl).symm.trans (congrFun hy x)
  calc ∑ a ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) P d, X.fn hμ j f (g * a)
      = ∑ a ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) P d, (X.R.cV j).ext ((X.R.HV j (X.tupT μ)).e y) (g * a) :=
        Finset.sum_congr rfl fun a _ => (hy2 _).symm
    _ = (X.R.cV j).ext (s P d • (X.R.HV j (X.tupT μ)).e y) g := e3.symm
    _ = s P d • (X.R.cV j).ext ((X.R.HV j (X.tupT μ)).e y) g :=
        congrFun (map_smul (X.R.cV j).ext (s P d) ((X.R.HV j (X.tupT μ)).e y)) g
    _ = s P d • X.fn hμ j f g := by rw [hy2]

end GlobalTheory.EigTransport

namespace GlobalTheory.EigTransport

end GlobalTheory.EigTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPlaceHeckeEigenMatch
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SummandEig

theorem irrScalar : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (S : Submodule ℂ (Formalism.AUTREP.GAf L n → a.W)), Formalism.L2.NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (α : Formalism.AUTREP.GAf L n), TrivOutside {s.v} α → ∀ (ι : Type) (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n), (∀ γ ∈ R, ∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, r γ = k₁ * α * k₂) → (∀ x, (∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ (r γ)⁻¹ * x ∈ Umax L n) → ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := _root_.GlobalTheory.HeckeScalarDC.dc_scalar

theorem isoScalar : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (S : Submodule ℂ (Formalism.AUTREP.GAf L n → a.W)), Formalism.L2.NG.IsIrrRep a.ρ S → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (ι : Type) (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n) (c : ℂ), (∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f) → ∀ f ∈ Formalism.L2.NG.isoTyp a.ρ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := _root_.GlobalTheory.SumTransIso.sumRt_isoTyp

theorem frameReps : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (Ψ : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ψ → ∀ (Pp : HeightOneSpectrum (𝓞 D.host.E)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → ∀ d, GlobalTheory.Hk3.IsLab V Pp d → ∃ (s : SplitPlace D.host.E) (α : Formalism.AUTREP.GAf D.host.E n), Formalism.L2.NG.OverPl Pp s.v ∧ TrivOutside {s.v} α ∧ (∀ γ ∈ GlobalTheory.Hk3.rep V Pp d, ∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, Formalism.IndefR.principalLevelFrame.pre Ψ γ = k₁ * α * k₂) ∧ ∀ x, (∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ GlobalTheory.Hk3.rep V Pp d ∧ (Formalism.IndefR.principalLevelFrame.pre Ψ γ)⁻¹ * x ∈ Umax D.host.E n := GlobalTheory.T.standardFrame_sphericalDoubleCoset_reps_local

theorem rep_mem {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (Pp : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    {γ : Formalism.L2.Theta.GA D V} (hγ : γ ∈ GlobalTheory.Hk3.rep V Pp d) : γ ∈ Formalism.L2.Theta.GfC V := by
  unfold GlobalTheory.Hk3.rep at hγ
  split_ifs at hγ with hl
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hR⟩ := hl.choose_spec
    exact (hR.1 γ hγ).1
  · simp at hγ

theorem cast_sum {D : D7} (M : MtFam D) (μ : D.what₂.Tup) {j k : ℕ} (e : j = k) (h1 : 1 ≤ k) (h2 : k ≤ D.R.m)
    (h1' : 1 ≤ j) (h2' : j ≤ D.R.m) (f' : D.what₂.Mt μ j) {ι : Type} (R : Finset ι) (r : ι → Formalism.AUTREP.GAf D.host.E D.R.nV)
    (c : ℂ) (h : ∑ γ ∈ R, Formalism.L2.NG.rt D.host.E D.R.nV (r γ) ((M μ k h1 h2).real (e ▸ f')) = c • (M μ k h1 h2).real (e ▸ f')) :
    ∑ γ ∈ R, Formalism.L2.NG.rt D.host.E D.R.nV (r γ) ((M μ j h1' h2').real f') = c • (M μ j h1' h2').real f' := by
  subst e
  exact h

theorem extV_inf {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (j : Fin D.R.m) (t : X.T) (y : (X.R.HV j t).H) {a b : Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Vc D j)}
    (ha : a ∈ Formalism.L2.Theta.GinfC (Formalism.IndefR.Links.Vc D j)) (hb : b ∈ Formalism.L2.Theta.GfC (Formalism.IndefR.Links.Vc D j)) :
    X.R.extV j t y (a * b) = (X.R.cV j).ρ a⁻¹ (X.R.extV j t y b) := by
  have hcv := (X.given.core.models.cV j).1
  have e0 : ∀ g, X.R.extV j t y g = (X.R.cV j).ρ g⁻¹ ((X.R.HV j t).e y ((Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict g)) := fun g => rfl
  have e1 : (Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict a = 1 := by
    apply Subtype.ext
    exact (MonoidHom.mem_ker (f := Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j))).1 ha
  refine (e0 (a * b)).trans (Eq.trans ?_ (congrArg ((X.R.cV j).ρ a⁻¹) (e0 b)).symm)
  have e2 : (Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict (a * b) = (Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict b := by
    rw [map_mul, e1, one_mul]
  have e3 : (X.R.cV j).ρ (a * b)⁻¹ = (X.R.cV j).ρ a⁻¹ := by
    rw [mul_inv_rev, map_mul, hcv _ (inv_mem hb), one_mul]
  have e4 : (X.R.cV j).ρ b⁻¹ = 1 := hcv _ (inv_mem hb)
  have e5 : ∀ x, (X.R.cV j).ρ b⁻¹ x = x := fun x => by rw [e4]; rfl
  have e6 := congr (congrArg DFunLike.coe e3) (congrArg ((X.R.HV j t).e y) e2)
  exact e6.trans (congrArg ((X.R.cV j).ρ a⁻¹) (e5 _)).symm

end GlobalTheory.SummandEig
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LimWUOfSeeds
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

namespace GlobalTheory.CongL

theorem overPl_unique {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (τ : E →+* ℂ)
    {w u : HeightOneSpectrum (𝓞 E)} (hw : OverPl ι τ w) (hu : OverPl ι τ u) : u = w := by
  by_contra hne
  have hI : u.asIdeal ≠ w.asIdeal := fun h => hne (HeightOneSpectrum.ext h)
  have htop : u.asIdeal ⊔ w.asIdeal = ⊤ := Ideal.IsMaximal.coprime_of_ne u.isMaximal w.isMaximal hI
  have h1 : (1 : 𝓞 E) ∈ u.asIdeal ⊔ w.asIdeal := htop ▸ Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp h1
  have hx' := hu x hx
  have hy' := hw y hy
  have hsum : ι.symm (τ ((x : E))) + ι.symm (τ ((y : E))) = 1 := by
    rw [← map_add (f := _), ← map_add (f := _)]
    have : ((x : E) + (y : E)) = 1 := by exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hxy
    rw [this, map_one, map_one]
  have hle := IsUltrametricDist.norm_add_le_max (ι.symm (τ ((x : E)))) (ι.symm (τ ((y : E))))
  rw [hsum, norm_one] at hle
  exact absurd hle (not_le.mpr (max_lt hx' hy'))

end GlobalTheory.CongL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilitySeventh
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StrInert

theorem not_isSplitPl_of_inert (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hin : Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w) : ¬ IsSplitPl D.host w := by
  rw [GlobalTheory.ConjPlaceOff.isSplitPl_iff]
  rintro ⟨x, hx, hcx⟩
  apply hcx
  unfold Formalism.UG.IsInertAt at hin
  rw [← hin] at hx ⊢
  have key : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (w.under (𝓞 D.host.F)).asIdeal ≤
      (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (w.under (𝓞 D.host.F)).asIdeal).comap
        (Formalism.HermitianLattices.Ext.L3.conjO D.host.E) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have e : Formalism.HermitianLattices.Ext.L3.conjO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) =
        algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a := by
      apply RingOfIntegers.ext
      rw [Formalism.HermitianLattices.Ext.L3.conjO_coe]
      have : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) =
          algebraMap D.host.F D.host.E (a : D.host.F) := rfl
      rw [this]
      exact Formalism.IndefR.Eqv.star_algebraMapF D _
    rw [e]
    exact Ideal.mem_map_of_mem _ ha
  exact key hx

theorem not_mem_badPl {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat D A Ks) (t : T)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : GlobalTheory.Hk3.Good R t w)
    (hin : Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w) :
    w.under (𝓞 D.host.F) ∉ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t := by
  classical
  intro h
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl, Finset.mem_image, Finset.mem_union] at h
  obtain ⟨PP, hPP, he⟩ := h
  have hne := (hw PP hPP).1
  apply hne
  unfold Formalism.UG.IsInertAt at hin
  have hle : w.asIdeal ≤ PP.asIdeal := by
    rw [← hin, Ideal.map_le_iff_le_comap]
    intro a ha
    have : ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal = PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := rfl
    rw [← this, he]
    exact ha
  exact (HeightOneSpectrum.ext (w.isMaximal.eq_of_le PP.isPrime.ne_top hle)).symm

end GlobalTheory.StrInert
end

