module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteIteratedCompactAverageApprox
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0534
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathArgsOfNotMem

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalNonvanishing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped ComplexConjugate

namespace GlobalTheory.UpCuspApprox

theorem val_aut_cusp {D : D7} {θ : InfFam D} {N : GlobalTheory.Grid.Node D} {F : N.Maps} (hF : F ∈ N.Cusp θ)
    (v : SmT N.M) : IsAutFunSm θ N.V (F v) ∧ IsCuspFun N.V (F v) := by
  have hT := (GlobalTheory.MultMem.mem_mult_iff D θ N.V N.S N.M ∅ 1 _).1 ((Formalism.IndefR.Mult.mem_multT θ N.M ∅ 1 F).1 hF)
  have e : F = PiTensorProduct.lift (PiTensorProduct.lift.symm F) := (LinearEquiv.apply_symm_apply _ F).symm
  rw [e]
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [map_smul, PiTensorProduct.lift.tprod]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_smul c (hT.aut x), GlobalTheory.MultMem.isCuspFun_smul c (hT.cusp x)⟩
  | add a b ha hb =>
    rw [map_add (f := _)]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add ha.1 hb.1, GlobalTheory.MultMem.isCuspFun_add ha.1.toIsAutFun hb.1.toIsAutFun ha.2 hb.2⟩

end GlobalTheory.UpCuspApprox

namespace GlobalTheory.UpCuspApprox

end GlobalTheory.UpCuspApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalSmoothVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

namespace GlobalTheory.DownApprox

open GlobalTheory.Size

variable {D : D7}

theorem thetaKO_le_unif {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f : WO V W → ℂ}
    (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f)
    {K : Set (GA D W)} (hK : IsCompact K) :
    ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ h ∈ K, ∀ g, ‖thetaKO ω g h f‖ ≤ C * GlobalTheory.Grow.height V g ^ A := by
  obtain ⟨A, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D V.rank W.rank
  obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 hf
  obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne V W
  obtain ⟨C, hC0, hC⟩ := (H V W rfl rfl).real ψ hθ hU
  obtain ⟨B, hB⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact W hK
  have hs : 0 ≤ C * (sobO ψ θ μ 𝓕 d f).toReal := mul_nonneg hC0 ENNReal.toReal_nonneg
  refine ⟨C * (sobO ψ θ μ 𝓕 d f).toReal * max B 1 ^ A, A, mul_nonneg hs (pow_nonneg (by positivity) _),
    fun h hh g => ?_⟩
  have h1 := (hC χS χT ω hω μ 𝓕 hμ f hl).2 g h
  have hW : GlobalTheory.Grow.height W h ≤ max B 1 := (hB h hh).trans (le_max_left _ _)
  have hW0 : 0 ≤ GlobalTheory.Grow.height W h := (GlobalTheory.Grow.height_pos W h).le
  have hV0 : 0 ≤ GlobalTheory.Grow.height V g := (GlobalTheory.Grow.height_pos V g).le
  calc ‖thetaKO ω g h f‖ = ‖ω (g, h) f 0‖ := rfl
    _ ≤ C * (sobO ψ θ μ 𝓕 d f).toReal * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ A := h1
    _ ≤ C * (sobO ψ θ μ 𝓕 d f).toReal * (GlobalTheory.Grow.height V g * max B 1) ^ A :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hV0 hW0)
          (mul_le_mul_of_nonneg_left hW hV0) _) hs
    _ = C * (sobO ψ θ μ 𝓕 d f).toReal * max B 1 ^ A * GlobalTheory.Grow.height V g ^ A := by ring

theorem thetaKO_le_quotHeight {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    (hθ : IsInfFam θ) (ε : Bool) {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {ω : GlobalTheory.Grid.WRep S T}
    (hω : IsWeilDatumO ψ (GlobalTheory.Grid.sgn ε S) T χS χT (ω.toSgn ε)) {Φ : WO S T → ℂ}
    (hΦ : IsThetaFunO ψ (GlobalTheory.Grid.sgn ε S) T Φ) {K : Set (GA D T)} (hK : IsCompact K) :
    ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ h ∈ K, ∀ g, ‖thetaKO ω g h Φ‖ ≤ C * GlobalTheory.Grow.quotHeight S g ^ A := by
  have e : ∀ g h, thetaKO ω g h Φ = thetaKO (ω.toSgn ε) ((GlobalTheory.Grid.ofSgn ε S).symm g) h Φ := fun g h => by
    show ω (g, h) Φ 0 = ω (GlobalTheory.Grid.ofSgn ε S ((GlobalTheory.Grid.ofSgn ε S).symm g), h) Φ 0
    rw [MulEquiv.apply_symm_apply]
  have hinv : ∀ h, ∀ γ ∈ GQ S, ∀ g, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ := fun h γ hγ g => by
    rw [e, e, map_mul]
    refine GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_left_fst hω hΦ h _ ?_ _
    rw [GlobalTheory.SgnIdent.mem_GQ_sgn, MulEquiv.apply_symm_apply]
    exact hγ
  obtain ⟨C, A, hC0, hC⟩ := thetaKO_le_unif hθ hω hΦ hK
  have hC' : ∀ h ∈ K, ∀ g, ‖thetaKO ω g h Φ‖ ≤ C * GlobalTheory.Grow.height S g ^ A := fun h hh g => by
    simp only [e]
    exact hC h hh _
  exact ⟨C * 2 ^ A, A, by positivity, fun h hh g => GlobalTheory.Grow.norm_le_quotHeight_pow (hinv h) (hC' h hh) g⟩

end GlobalTheory.DownApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TotalTensorThetaLiftEqOfSchwartzEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FlipRun

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

theorem kerA_sum_of_grid {t : T} {a : Arrow T} (ha : IsGridArrow D.R.m t a) {ι : Type} (L : Finset ι) (w : ι → ℂ)
    (gs : ι → Sch G a) (g₀ : GA D (G.V a.src)) (h : GA D (G.V a.tgt)) :
    W.kerA a (∑ l ∈ L, w l • gs l) g₀ h = ∑ l ∈ L, w l * W.kerA a (gs l) g₀ h := by
  rcases ha with ⟨i, j, -, -, rfl⟩ | ⟨i, j, -, -, rfl⟩ <;>
    set_option synthInstance.maxHeartbeats 100000 in
      simp [GridData.Weil.kerA, GridData.Weil.ker, thetaKO, map_sum, map_smul, Finset.sum_apply]

theorem liftA_sum_datum (M : Vol G) {t : T} {a : Arrow T} (ha : IsGridArrow D.R.m t a) {ι : Type} (L : Finset ι)
    (w : ι → ℂ) (gs : ι → Sch G a) (F : Fn G a.src) (hc : ∀ l ∈ L, LiftConv W M a (gs l) F) :
    liftA W M a (∑ l ∈ L, w l • gs l) F = ∑ l ∈ L, w l • liftA W M a (gs l) F := by
  funext h
  simp only [liftA_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, kerA_sum_of_grid ha, Finset.sum_mul]
  rw [integral_finsetSum _ fun l hl => ?_]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun x => ?_)
    ring
  · have := (hc l hl h).const_mul (w l)
    refine this.congr (.of_forall fun x => ?_)
    simp only
    ring

theorem liftA_sum_form (M : Vol G) (a : Arrow T) (f : Sch G a) {ι : Type} (s : Finset ι) (w : ι → ℂ)
    (Fs : ι → Fn G a.src) (hc : ∀ k ∈ s, LiftConv W M a f (Fs k)) :
    liftA W M a f (∑ k ∈ s, w k • Fs k) = ∑ k ∈ s, w k • liftA W M a f (Fs k) := by
  funext h
  simp only [liftA_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum _ fun k hk => ?_]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun x => ?_)
    ring
  · have := (hc k hk h).const_mul (w k)
    refine this.congr (.of_forall fun x => ?_)
    simp only
    ring

theorem liftA_zero_form (M : Vol G) (a : Arrow T) (f : Sch G a) : liftA W M a f 0 = 0 := by
  have := liftA_smul W M a f 0 0
  rwa [zero_smul, zero_smul] at this

theorem sum_liftP_eq_zero {μ₀ : T} (hL : L.Is μ₀) (M : Vol G) (ρ : RealMatch W) (t : T) {e : AE D}
    (he : IsIdemSum e (locPl G t)) (hC : CuspStep W M ρ t) {X : Node} :
    ∀ {Y : Node} (p : Path T X Y), OnGrid D.R.m t p → ∀ {ι : Type} (s : Finset ι) (c : ι → ℂ) (φ d : ι → PureT G p),
      (∀ k ∈ s, VecAll ρ e p (φ k) (d k)) → (∀ x : ArgT G p, HalfAll e p x → ∑ k ∈ s, c k * famProd p (φ k) x = 0) →
      ∀ (P : PolT G p) (F : Fn G X), IsCuspListed W.θ X F →
      ∑ k ∈ s, c k • liftP W M p (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) (d k) P) F = 0
  | _, .nil, _, ι, s, c, φ, d, _, hsum, P, F, _ => by
    have h0 : ∑ k ∈ s, c k = 0 := by
      have := hsum () trivial
      simpa [famProd] using this
    show ∑ k ∈ s, c k • F = 0
    rw [← Finset.sum_smul, h0, zero_smul]
  | _, .snoc a p, hg, ι, s, c, φ, d, hv, hsum, P, F, hF => by
    classical
    have ha : IsGridArrow D.R.m t a := hg.last
    have hmodel := GlobalTheory.FlipRun.exists_arrowModel (G := G) (t := t) ρ hL he ha
    rcases hmodel with ⟨Tm, h1, -, h3⟩
    have hmem : ∀ k ∈ s, (φ k).2 ∈ LocTensor.sbSpace e (latA G a) := fun k hk => ((h1 _ _).1 (hv k hk).2).1
    have hd2 : ∀ k ∈ s, (d k).2 = Tm (φ k).2 := fun k hk => ((h1 _ _).1 (hv k hk).2).2
    let b := Module.Basis.ofVectorSpace ℂ (LocTensor.sbSpace e (latA G a))
    let v : ι → LocTensor.sbSpace e (latA G a) := fun k => if h : (φ k).2 ∈ LocTensor.sbSpace e (latA G a) then ⟨_, h⟩ else 0
    have hv' : ∀ k ∈ s, ((v k : LocTensor.sbSpace e (latA G a)) : Sch G a) = (φ k).2 := fun k hk => by
      simp only [v, dite_eq_left (hmem k hk)]
    let r : ι → Module.Basis.ofVectorSpaceIndex ℂ (LocTensor.sbSpace e (latA G a)) → ℂ := fun k l => b.repr (v k) l
    let Ls := s.biUnion fun k => (b.repr (v k)).support
    have hexp : ∀ k ∈ s, (φ k).2 = ∑ l ∈ Ls, r k l • ((b l : LocTensor.sbSpace e (latA G a)) : Sch G a) := by
      intro k hk
      rw [← hv' k hk]
      conv_lhs => rw [← b.linearCombination_repr (v k)]
      rw [Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem (fun k => (b.repr (v k)).support) hk)
          (fun i (x : ℂ) => x • b i) (fun _ _ => zero_smul _ _), Submodule.coe_sum]
      rfl
    let Fk : ι → Fn G a.src := fun k => liftP W M p (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) (d k).1 P.1) F
    have cusp_zip : ∀ {Y : Node} (q : Path T X Y), OnGrid D.R.m t q →
        ∀ (φq dq : PureT G q), VecAll ρ e q φq dq → ∀ Q : PolT G q,
          IsCuspListed W.θ Y
            (liftP W M q (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) dq Q) F) := by
      intro Y q
      induction q with
      | nil =>
        intro _ _ _ _ _
        exact hF
      | snoc b q ih =>
        intro hq φq dq hvq Q
        exact (hC b hq.last e he φq.2 dq.2 hvq.2 Q.2 _ (ih hq.init φq.1 dq.1 hvq.1 Q.1)).2
    have hFk : ∀ k ∈ s, IsCuspListed W.θ a.src (Fk k) := fun k hk =>
      cusp_zip p hg.init (φ k).1 (d k).1 (hv k hk).1 P.1
    let g : Module.Basis.ofVectorSpaceIndex ℂ (LocTensor.sbSpace e (latA G a)) → Sch G a :=
      fun l => W.fock a.pair (Tm (b l)) P.2
    have hconv : ∀ l, ∀ k ∈ s, LiftConv W M a (g l) (Fk k) := fun l k hk =>
      (hC a hg.last e he (b l) (Tm (b l)) ((h1 _ _).2 ⟨(b l).2, rfl⟩) P.2 (Fk k) (hFk k hk)).1
    have hstep : ∀ k ∈ s, W.fock a.pair (d k).2 P.2 = ∑ l ∈ Ls, r k l • g l := by
      intro k hk
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hd2 k hk, hexp k hk, map_sum]
      simp only [map_smul]
      exact GlobalTheory.SpecFac.pureTensorO_sum W.ψ_std W.θ_is _ _ _ _ Ls (r k) (fun l => Tm (b l))
        (fun l _ => h3 _ (b l).2) P.2
    have hIH : ∀ l, ∑ k ∈ s, (c k * r k l) • Fk k = 0 := by
      intro l
      refine sum_liftP_eq_zero hL M ρ t he hC p hg.init s (fun k => c k * r k l) (fun k => (φ k).1) (fun k => (d k).1)
        (fun k hk => (hv k hk).1) (fun x hx => ?_) P.1 F hF
      have hV : ∑ k ∈ s, (c k * famProd p (φ k).1 x) • v k = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        funext y
        rw [Finset.sum_apply]
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Submodule.coe_zero, Pi.zero_apply]
        rw [Finset.sum_congr rfl fun k hk => by rw [hv' k hk]]
        by_cases hy : IsHalf e y
        · have := hsum (x, y) ⟨hx, hy⟩
          rw [← this]
          refine Finset.sum_congr rfl fun k _ => ?_
          show _ = c k * (famProd p (φ k).1 x * (φ k).2 y)
          ring
        · refine Finset.sum_eq_zero fun k hk => ?_
          have : (φ k).2 y = 0 := by
            by_contra h0
            exact hy ((hmem k hk).1 y h0)
          rw [this, mul_zero]
      have := congrArg (fun z => b.repr z l) hV
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
        map_zero, Finsupp.coe_zero, Pi.zero_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [r]
      ring
    have hsum_lift :
        (∑ k ∈ s, c k • liftA W M a (W.fock a.pair (d k).2 P.2) (Fk k)) =
          ∑ k ∈ s, ∑ l ∈ Ls, (c k * r k l) • liftA W M a (g l) (Fk k) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hstep k hk, liftA_sum_datum M ha Ls (r k) g (Fk k) (fun l _ => hconv l k hk),
        Finset.smul_sum]
      simp only [smul_smul]
    show ∑ k ∈ s, c k • liftA W M a (W.fock a.pair (d k).2 P.2) (Fk k) = 0
    rw [hsum_lift, Finset.sum_comm]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← liftA_sum_form M a (g l) s (fun k => c k * r k l) Fk (fun k hk => hconv l k hk),
      hIH l, liftA_zero_form]

theorem liftT_tensE_expand (M : Vol G) {X Y : Node} (p : Path T X Y) (Q : PolE G →₀ ℂ) (τ : TotT G p) (F : Fn G X) :
    liftT W M p (tensE W p Q τ) F =
      ∑ P ∈ (Q.mapDomain fun P => restrictPol P p).support, (Q.mapDomain fun P => restrictPol P p) P •
        ∑ d ∈ τ.support, τ d • liftP W M p (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P) F := by
  unfold tensE tensT
  rw [Finsupp.sum, liftT_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Finsupp.sum, liftT_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [liftT_single, mul_smul]

theorem liftT_tensE_eq_of_famProd : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ {W : G.Weil} (M : Vol G) (ρ : RealMatch W) (t : T) {e : AE D}, IsIdemSum e (locPl G t) → GlobalTheory.FlipRun.CuspStep W M ρ t → ∀ {X Y : Node} (p : Path T X Y), GlobalTheory.FlipRun.OnGrid D.R.m t p → ∀ (τ₁ τ₂ : TotT G p) (φ₁ φ₂ : PureT G p → PureT G p), (∀ d ∈ τ₁.support, GlobalTheory.FlipRun.VecAll ρ e p (φ₁ d) d) → (∀ d ∈ τ₂.support, GlobalTheory.FlipRun.VecAll ρ e p (φ₂ d) d) → (∀ x : GlobalTheory.FlipRun.ArgT G p, GlobalTheory.FlipRun.HalfAll e p x → (τ₁.sum fun d c => c * GlobalTheory.FlipRun.famProd p (φ₁ d) x) = τ₂.sum fun d c => c * GlobalTheory.FlipRun.famProd p (φ₂ d) x) → ∀ F : Fn G X, GlobalTheory.FlipRun.IsCuspListed W.θ X F → ∀ Q : GlobalTheory.FlipRun.PolE G →₀ ℂ, liftT W M p (GlobalTheory.FlipRun.tensE W p Q τ₁) F = liftT W M p (GlobalTheory.FlipRun.tensE W p Q τ₂) F := by
  intro D T L sc G μ₀ hL W M ρ t e he hC X Y p hg τ₁ τ₂ φ₁ φ₂ hv₁ hv₂ heq F hF Q
  classical
  rw [liftT_tensE_expand, liftT_tensE_expand]
  refine Finset.sum_congr rfl fun P _ => ?_
  congr 1
  have key := sum_liftP_eq_zero hL M ρ t he hC p hg (τ₁.support.disjSum τ₂.support)
    (Sum.elim (fun d => τ₁ d) fun d => -τ₂ d) (Sum.elim φ₁ φ₂) (Sum.elim id id)
    (by
      rintro (k | k) hk
      · exact hv₁ k (Finset.inl_mem_disjSum.1 hk)
      · exact hv₂ k (Finset.inr_mem_disjSum.1 hk))
    (fun x hx => by
      rw [Finset.sum_disjSum]
      have := heq x hx
      simp only [Finsupp.sum] at this
      simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, this, add_neg_cancel])
    P F hF
  rw [Finset.sum_disjSum] at key
  simp only [Sum.elim_inl, Sum.elim_inr, id, neg_smul, Finset.sum_neg_distrib] at key
  exact sub_eq_zero.1 ((sub_eq_add_neg _ _).trans key)

end GlobalTheory.FlipRun

end
end

