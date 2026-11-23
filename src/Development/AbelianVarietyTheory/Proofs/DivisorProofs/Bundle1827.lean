module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesSixth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1635
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1715
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1810
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0963
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1812
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1807
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1792
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTripleRealizationSquareClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralBlockTranslateOfFlipDatum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1811
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndMapRangeField
public import Formalism.PieriBlockIdeals.PieriColumnMinors.RealLocalDeltaNabla
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOneOfSerOf
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapPhaseOne


set_option maxHeartbeats 1000000 in
theorem phRat_of_serOf : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.IsGrp F → R.IsThP → TieIn T R κ v₀ → ∀ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), OMPins T R κ v₀ O i → ∀ cc, SerOf (O i) (κ i) (v₀ i (sg0 D A)) cc 1 → (∀ x : (O i).Cl' () → VsV D i (O i).c'.F, ∃ f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (unfBC (O i).hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank, IsThClsD (T.Q.Xo ((i : ℕ) + 1)) (O i).c' ((O i).dδ ()) ((O i).w ()) ((O i).La ()) ((O i).Nc ()) ((O i).gam ()) ((O i).vol ()) ((O i).ep ()) (O i).io x f) → (O i).EquivAt (κ i) cc → (O i).PhRat (κ i) (v₀ i (sg0 D A)) cc 1 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hG hP' t O i hpins cc hser hex hequiv
  obtain ⟨hcc, hph, hs⟩ := hser
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm ⟨1, by simp [Formalism.FrobeniusOrbits.Psi]⟩⟩
  have hn : (κ i).n = (Vc D i).rank :=
    (t.kap i τ).2.2.trans (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm
  refine GlobalTheory.PhaseRationalDegenerate.of_before_projector (O i) (κ i) _ cc hequiv hG.chiW hP'.thG 1 fun x₀ => ?_
  obtain ⟨h, J', hrep, hP, -, -⟩ := (hpins.2.tuple ()).reps
  obtain ⟨x, hx⟩ := hP x₀
  obtain ⟨f, hf, hcl⟩ := hex x
  have hf' : f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (unfBC (O i).hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (κ i).n := by
    rw [hn]; exact hf
  have hBC := GlobalTheory.PhRatCommon.exists_rdU_eq_sum (O i).hle (T.U ((i : ℕ) + 1)) (inC (O i).c') _ _ f hf'
  obtain ⟨m, as, fs, hbc⟩ := hBC
  have hL : ∀ a : (O i).c'.F, ∃ b : D.what₂.LL, D.what₂.embLL b = inC (O i).c' a := fun a => by
    have : (a : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange := hpins.1 ▸ a.2
    exact this
  choose b hb using hL
  refine ⟨m, fun j => b (as j), fs, fun g => ?_⟩
  have := hs () h J' hrep _ x hx f hf.1 hcl g
  have e1 := hbc ((O i).dict g).1 ((O i).dict g).2
  have e2 : ∀ j, (O i).phi cc (fs j : T.R ((i : ℕ) + 1)) g = cc ((O i).dict g).1 * (O i).mu g *
      rdU (T.U ((i : ℕ) + 1) (O i).s0) (fs j : T.R ((i : ℕ) + 1)) ((O i).dict g).1 ((O i).dict g).2 := fun j => rfl
  exact this.trans (GlobalTheory.PhRatCommon.sum_shape e1 (fun j => hb (as j)) e2)


set_option maxHeartbeats 1000000 in
theorem oneMapOf_one_of_serOf : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.IsGrp F → R.IsThP → TieIn T R κ v₀ → ∀ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), OMPins T R κ v₀ O i → ∀ cc, SerOf (O i) (κ i) (v₀ i (sg0 D A)) cc 1 → (∀ x : (O i).Cl' () → VsV D i (O i).c'.F, ∃ f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (unfBC (O i).hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank, IsThClsD (T.Q.Xo ((i : ℕ) + 1)) (O i).c' ((O i).dδ ()) ((O i).w ()) ((O i).La ()) ((O i).Nc ()) ((O i).gam ()) ((O i).vol ()) ((O i).ep ()) (O i).io x f) → (O i).EquivAt (κ i) cc → (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) cc 1 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hG hP' t O i hpins cc hS hE hequiv
  refine ⟨hequiv, ⟨hpins.1.ge, (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ (O i).hle).2 _ _,
    (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ (O i).hle _ _ hpins.2.act.1).2, ?_⟩,
    phRat_of_serOf D G Pl0 T0 A T R F κ v₀ hG hP' t O i hpins cc hS hE hequiv⟩
  refine ⟨hS.1, hS.2.1, 1, Subgroup.one_mem _, fun t => ⟨1, one_mem _, ⟨1, Nat.one_pos, one_pow _⟩, fun x hx => ⟨hE x, ?_⟩⟩⟩
  intro f hf hT q
  obtain ⟨h, J', hR, -, hA, hPl⟩ := (hpins.2.tuple t).reps
  obtain ⟨x₀, hx₀⟩ := (hPl x).1 hx
  have hL := hpins.2.act.2
  have h1 : actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) (O i).c' (O i).lev2 1 f = f :=
    actL_one _ _ _ hL.total hL.func hL.one hf.1
  have h2 := hS.2.2 t h J' hR _ x hx₀ f hf hT q.out
  rw [h1, hA _ x hx₀, one_mul (cc _)]
  refine h2.trans ?_
  rw [mul_assoc (cc _ * _)]
  rfl

end GlobalTheory.OneMapPhaseOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubstDualWeylExpressibleMatrixMulClosed
section
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.GenCoef

theorem rowSubst_mul_comp (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R]
    (Y Y' : Matrix (Fin N) (Fin N) R) (f : MvPolynomial (Fin N × Fin N) O) :
    rowSubst O N R (Y * Y') f = rowSubst R N R Y' (rowSubst O N R Y f) := by
  have h : (rowSubst O N R (Y * Y')) = ((rowSubst R N R Y').restrictScalars O).comp (rowSubst O N R Y) := by
    apply MvPolynomial.algHom_ext
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [rowSubst, AlgHom.comp_apply, AlgHom.restrictScalars_apply, aeval_X, map_sum, map_mul,
      algHom_C, Algebra.algebraMap_self, RingHom.id_apply, Matrix.mul_apply]
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  rw [h]; rfl

theorem rowSubst_self_map (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R]
    (Y' : Matrix (Fin N) (Fin N) R) (q : MvPolynomial (Fin N × Fin N) O) :
    rowSubst R N R Y' (MvPolynomial.map (algebraMap O R) q) = rowSubst O N R Y' q := by
  have h : ((rowSubst R N R Y').restrictScalars O).comp (MvPolynomial.mapAlgHom (Algebra.ofId O R)) = rowSubst O N R Y' := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [rowSubst]
  have := congrArg (fun φ => φ q) h
  simpa using this

theorem expr_mul (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (R : Type) [CommRing R] [Algebra O R]
    (Y Y' : Matrix (Fin N) (Fin N) R) (hY : Expr O N ν R Y) (hY' : Expr O N ν R Y') :
    Expr O N ν R (Y * Y') := by
  obtain ⟨n, r, p, hp, hf⟩ := hY
  obtain ⟨n', r', p', hp', hf'⟩ := hY'
  refine ⟨n * n', fun k => r (finProdFinEquiv.symm k).1 * r' (finProdFinEquiv.symm k).2,
    fun k => p' (finProdFinEquiv.symm k).2 * p (finProdFinEquiv.symm k).1, fun k => Subalgebra.mul_mem _ (hp' _) (hp _), ?_⟩
  intro f
  set_option synthInstance.maxHeartbeats 100000 in
    rw [rowSubst_mul_comp, hf f, map_sum]
  have e := (finProdFinEquiv (m := n) (n := n')).symm.sum_comp
    (fun x : Fin n × Fin n' => (r x.1 * r' x.2) • MvPolynomial.map (algebraMap O R)
      (((p' x.2 * p x.1) f : dualWeyl O N N ν) : MvPolynomial (Fin N × Fin N) O))
  rw [e, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, rowSubst_self_map, hf' (p i f), Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, Module.End.mul_apply]

end GlobalTheory.GenCoef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerIntertwinerScalar
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

noncomputable section
open GroundTheory.Global

namespace GlobalTheory.SubstIntertw

variable (F : Type) [Field F] [NumberField F]

def stdChar : AddChar (AF F) ℂ where
  toFun a := (adelicChar F a : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp [AddChar.map_add_eq_mul]

theorem stdChar_inl (z : InfiniteAdeleRing F) :
    Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (infiniteAdeleInl z : AF F)) : ℝ)) =
      (adelicChar F (infiniteAdeleInl z) : ℂ) := by
  have h2 : adelicChar F (infiniteAdeleInl z) = Real.fourierChar (-infiniteTrace F z) := adelicChar_infinite z
  rw [h2, GlobalTheory.AdelicSvN.Weyl.trace_eq_mixedTrace, ← mixedTrace_homeomorphMixedSpace, homeomorphMixedSpace_apply,
    Real.fourierChar_apply]
  congr 1
  have : evI F (infiniteAdeleInl z) = InfiniteAdeleRing.ringEquiv_mixedSpace F z := rfl
  rw [this]
  push_cast
  ring

theorem isStd_stdChar : IsStd (stdChar F) := by
  refine ⟨continuous_subtype_val.comp continuous_adelicChar, fun x => ?_, fun a ha => ?_⟩
  · show (adelicChar F (algebraMap F (AF F) x) : ℂ) = 1
    rw [adelicChar_algebraMap]; rfl
  · have h0 : evI F ((0, 1) : AF F) = 0 := by
      show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
      exact map_zero _
    have h2 : a.2 = 0 := by
      have := congrArg Prod.snd (ha ((0, 1) : AF F) h0)
      have e : (1 : FiniteAdeleRing (𝓞 F) F) * a.2 = 0 := this
      simpa using e
    obtain ⟨z, rfl⟩ : ∃ z : InfiniteAdeleRing F, a = infiniteAdeleInl z := ⟨a.1, Prod.ext rfl h2⟩
    exact (stdChar_inl F z).symm

end GlobalTheory.SubstIntertw

namespace GlobalTheory.SubstIntertw

open GroundTheory.Global


end GlobalTheory.SubstIntertw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitsCompletelyTypePrime
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem splitsCompletely_typePrime (D : D7) (k : Fin 2) : SplitsCompletely D.host.E (D.host.g k) := by
  refine ⟨D.host.g_prime k, ?_⟩
  have hg0 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.host.g_prime k).ne_zero
  have h := D.nd.g_split k
  rw [← h]
  have : {P : Ideal (𝓞 D.host.E) | P.IsPrime ∧ ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P} =
      (fun v : HeightOneSpectrum (𝓞 D.host.E) => v.asIdeal) '' {v : HeightOneSpectrum (𝓞 D.host.E) | ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal} := by
    ext P
    constructor
    · rintro ⟨hP, hg⟩
      have hne : P ≠ ⊥ := fun h0 => hg0 (by rw [h0] at hg; simpa using hg)
      exact ⟨⟨P, hP, hne⟩, hg, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.isPrime, hv⟩
  rw [this, Set.ncard_image_of_injective _ (fun a b h => HeightOneSpectrum.ext h)]
  rfl

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem half_le_plGw (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (k : Fin 2) (v : D.nd.PlG k) :
    p.T.Q.l.Mb ≤ (D.naut.plGw k v).asIdeal := by
  rw [h.half]
  obtain ⟨plg, -, hplg, -, -, -⟩ := p.grpRecPin
  have hmem : D.naut.plGw k v ∈ (R2 p).Pg := by
    rw [← hplg ⟨k, v⟩]
    exact (plg ⟨k, v⟩).2
  exact (Ideal.prod_le_inf).trans (Finset.inf_le hmem)

theorem levelCondition_restrict_of_halfUnipotent (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (i : Fin D.R.m) {C : Type} [Finite C]
    [MulAction p.P.Gp C] (M : TwoLevels D.host.E D.R.r p.P.Gp C) (ka : Wt M.Ψ D.R.r) (hg : ∀ k : Fin 2, 3 * D.R.r < D.host.g k)
    (hM : RunModel p r h i M ka) : ∀ H : Subgroup p.P.Gp, HalfUnip p H → LevelHyp (sub M H) := by
  intro H hH
  obtain ⟨k, hk⟩ := hH
  obtain ⟨v0, e, -, -, -, hd1, φ, hd2⟩ := hM
  refine ⟨D.host.g k, splitsCompletely_typePrime D k, hg k, ?_⟩
  intro c β hβ P hP hgP
  obtain ⟨u, huc, γ, hγ, rfl⟩ := hβ
  have huc' : (u : p.P.Gp) • c = c := huc
  have hγL : ∀ w, w ∈ (M.comp c).L' ↔ Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w ∈ (M.comp c).L' :=
    M.Γ_L' c γ hγ
  have htL : ∀ w, w ∈ (M.comp c).L' ↔
      Matrix.mulVec (M.tr u c : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w ∈ (M.comp c).L' := by
    intro w
    have := M.tr_L' u c w
    rwa [huc'] at this
  have half : ∀ v : D.nd.PlG k, ∀ w ∈ (M.comp c).L',
      Matrix.mulVec ((((γ * M.tr u c : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) - 1) ^ D.R.r) w ∈
        (D.naut.plGw k v).asIdeal • (M.comp c).L' := by
    intro v w hw
    obtain ⟨n, hn⟩ := hd2 c u huc'
    rw [Units.val_mul]
    exact GlobalTheory.T.unipotent_mod_ideal_of_trivial_mod_half _ _ _ (half_le_plGw p r h k v) (φ c) (r.lev i u) n (_root_.GlobalTheory.ShareOn.UnipLevel.levUnip_mod_place p r h i u k v (hk u u.2 v)) _ _ (fun w hw => (hγL w).1 hw)
      (hd1 c γ hγ) hn w hw
  obtain ⟨v, rfl | rfl⟩ := _root_.GlobalTheory.TypePrimesOnto.prime_eq_plGw_or_conj D k P hP hgP
  · exact half v
  · refine _root_.GlobalTheory.UnipConjIdeal.pow_sub_one_mem_conj_ideal_smul (M.comp c) (γ * M.tr u c) ?_ ?_ _ (half v)
    · intro a b
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ((M.comp c).Γ_stab γ hγ).1, M.comp_Gm c, M.tr_herm]
    · intro a
      rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      exact (htL a).trans (hγL _)

end GlobalTheory.ShareOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareFlipReachesLocalQuotientClasses
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

theorem GlobalTheory.SquareFlipReach.flip_reach_of (G1 : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F _ _) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F _ _),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X om om' R Rf → IsTied t i j e Bs Γ X →
    ∀ w ∈ locPl G t, ∀ v (hv : w.under (𝓞 D.host.F) = v) (hP : v ∈ Bs.P) ιA,
      Γ.M.IsLinW Bs.ψ (Bs.τ ⟨v, hP⟩) (Γ.V.bas v) (Γ.W.bas v) ιA →
    ∃ ι, IsLagrModel Γ.M W.ψ v (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w) ι ∧
    ∃ c : ℂ, c ≠ 0 ∧ ∃ g₀ : GL (Fin (spW G i j).rank) (Fv D.host.F v),
    ∃ c₀ : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fv D.host.F v),
      (∀ n Φ, depthAt G w ≤ n → IsNatDatum (unifAt w) n Φ → ∃ φ ∈ GlobalTheory.WeilM.SB _, ι φ = flipAt W t i j w n Φ ∧
        ∀ Z, ιA φ Z = c * GlobalTheory.SquareFlipReach.sqCore W t i j w n Φ (GlobalTheory.SquareFlipReach.trA t hv e (g₀.1 * Z * c₀.1))) ∧
      ∀ (K₁ : GL (Fin (spV G i j).rank) (Fv D.host.F v)) (K₂ : GL (Fin (spV₁ G i j).rank) (Fv D.host.F v)),
        ∃ g, ∃ c' : ℂ, c' ≠ 0 ∧ ∀ φ ∈ GlobalTheory.WeilM.SB _, ∃ φ₃ ∈ GlobalTheory.WeilM.SB _,
          Acts (evFin D.host.F v) (om (1, blkU _ _ e h.JWW g)) φ φ₃ ∧
          ∀ Z, ιA φ₃ Z = c' * ιA φ (Z * (c₀.1 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e K₁.1 K₂.1 * (c₀⁻¹).1))) (G2 : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F _ _) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F _ _),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X om om' R Rf → IsTied t i j e Bs Γ X →
    ∀ w ∈ locPl G t, ∀ v (hv : w.under (𝓞 D.host.F) = v) (hP : v ∈ Bs.P),
    ∀ g₀ : GL (Fin (spW G i j).rank) (Fv D.host.F v), ∀ c₀ : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fv D.host.F v),
    ∀ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fv D.host.F v)),
    ∀ s : GL (Fin (spV G i j).rank) (Fv D.host.F v) → GL (Fin (spV₁ G i j).rank) (Fv D.host.F v) → ℂ, (∀ K₁ K₂, s K₁ K₂ ≠ 0) →
    ∃ n Φ K₁ K₂, depthAt G w ≤ n ∧ IsNatDatum (unifAt w) n Φ ∧
      bigP (haarVol (KO _ (Fin (spW G i j).rank))) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) finSumFinEquiv (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν (Bs.τ ⟨v, hP⟩))
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.β (Bs.τ ⟨v, hP⟩))
          (fun Z => s K₁ K₂ * GlobalTheory.SquareFlipReach.sqCore W t i j w n Φ
            (GlobalTheory.SquareFlipReach.trA t hv e (g₀.1 * Z * c₀.1 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e K₁.1 K₂.1))) =
        smallP (haarVol (KO _ (Fin (spW₁ G i j).rank))) finSumFinEquiv (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν (Bs.τ ⟨v, hP⟩))
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.α (Bs.τ ⟨v, hP⟩)) Ψ) : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t)
    (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F _ _) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F _ _),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X om om' R Rf → IsTied t i j e Bs Γ X →
    ∀ w ∈ locPl G t, ∀ v, w.under (𝓞 D.host.F) = v → ∀ φ₀ ∈ GlobalTheory.WeilM.SB _,
    ∃ n Φ φ₂ g φ₃, depthAt G w ≤ n ∧ IsNatDatum (unifAt w) n Φ ∧ IsLocFn W B t e Γ w v (flipAt W t i j w n Φ) φ₂ ∧
      φ₃ ∈ GlobalTheory.WeilM.SB _ ∧ Acts (evFin D.host.F v) (om (1, blkU _ _ e h.JWW g)) φ₂ φ₃ ∧ Rf.p v φ₃ = Rf.p v φ₀ := by
  intro D T L sc G μ₀ hL W B t i j M hst e Bs Γ X om om' h R Rf hm hti w hw v ev φ₀ hφ₀
  have hvT : v ∈ X.T := (hti.2.2.1 v).2 ⟨w, hw, ev⟩
  have hP : v ∈ Bs.P := hm.triple.chars.sub hvT
  obtain ⟨ιA, ιB, hA, hB, -, -, hiff⟩ := hm.fin.zeta ⟨v, hP⟩ hvT
  obtain ⟨φ', hφ', e'⟩ : Rf.p v φ₀ ∈ (GlobalTheory.WeilM.SB _).map (Rf.p' v) := hm.fin.onto' v ▸ Submodule.mem_top
  have hΨ : ιB φ' ∈ GlobalTheory.WeilM.SB _ := hB.bij.mapsTo hφ'
  obtain ⟨ι, hι, c, hc, g₀, c₀, hcmp, htr⟩ := G1 hL W B t i j M hst e Bs Γ X om om' h R Rf hm hti w hw v ev hP ιA hA
  choose gK cK hcK hK using htr
  obtain ⟨n, Φ, K₁, K₂, hn, hΦ, hbig⟩ := G2 hL W B t i j M hst e Bs Γ X om om' h R Rf hm hti w hw v ev hP g₀ c₀ (ιB φ') hΨ
    (fun K₁ K₂ => c * cK K₁ K₂) (fun K₁ K₂ => mul_ne_zero hc (hcK K₁ K₂))
  obtain ⟨φ₂, hφ₂, hιφ₂, hc₂⟩ := hcmp n Φ hn hΦ
  obtain ⟨φ₃, hφ₃, hact, hc₃⟩ := hK K₁ K₂ φ₂ hφ₂
  refine ⟨n, Φ, φ₂, gK K₁ K₂, φ₃, hn, hΦ, ⟨hφ₂, ι, hι, hιφ₂⟩, hφ₃, hact, ?_⟩
  have e1 : ιA φ₃ = fun Z => c * cK K₁ K₂ * GlobalTheory.SquareFlipReach.sqCore W t i j w n Φ
      (GlobalTheory.SquareFlipReach.trA t ev e (g₀.1 * Z * c₀.1 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e K₁.1 K₂.1)) := by
    funext Z
    rw [hc₃, hc₂]
    have e2 : g₀.1 * (Z * (c₀.1 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e K₁.1 K₂.1 * (c₀⁻¹).1)) * c₀.1 =
        g₀.1 * Z * c₀.1 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e K₁.1 K₂.1 := by
      simp only [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    rw [e2, mul_comm c (cK K₁ K₂), mul_assoc]
  have e3 := (hiff φ₃ hφ₃ φ' hφ').2 (by rw [e1]; exact hbig)
  exact e3.trans e'

theorem GlobalTheory.SquareFlipReach.flip_reach : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t)
    (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F _ _) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F _ _),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X om om' R Rf → IsTied t i j e Bs Γ X →
    ∀ w ∈ locPl G t, ∀ v, w.under (𝓞 D.host.F) = v → ∀ φ₀ ∈ GlobalTheory.WeilM.SB _,
    ∃ n Φ φ₂ g φ₃, depthAt G w ≤ n ∧ IsNatDatum (unifAt w) n Φ ∧ IsLocFn W B t e Γ w v (flipAt W t i j w n Φ) φ₂ ∧
      φ₃ ∈ GlobalTheory.WeilM.SB _ ∧ Acts (evFin D.host.F v) (om (1, blkU _ _ e h.JWW g)) φ₂ φ₃ ∧ Rf.p v φ₃ = Rf.p v φ₀ :=
  GlobalTheory.SquareFlipReach.flip_reach_of _root_.GlobalTheory.MixCompare.mixed_compare _root_.GlobalTheory.PureMatch.pure_match
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelClassScalarIntegralStandard
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.TwistClassScalar

set_option maxHeartbeats 800000

theorem twist_class_scalar : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → (∀ PP ∈ Ps, (((O i).bad () : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h yd → ∃ c1 : D.what₂.LL, D.what₂.embLL c1 * (((((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 yd : Circle) : ℂ)⁻¹ * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) * ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) : ℂ))⁻¹) = (((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹ * ((Λ.mIdx N D.R.r : ℂ))⁻¹ * ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) : ℂ))⁻¹ * (Λ.zCard N D.R.r : ℂ)) ∧ ∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c1) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hP v hv htm hQ hF hV hdel hMb hRun ℓ hLv hAc χ ξR ω φ hK Λ h N hU hTb hTM hLev hLa e Ps yd hh he hPs hPb hs hy
  have hz := GlobalTheory.ClassScalarValue.zCard_eq Λ N D.R.r hLev.2.2
  have hm : Λ.mIdx N D.R.r ≠ 0 := GlobalTheory.ClassScalarValue.mIdx_ne_zero Λ D.R.r (fun h0 => by
    obtain ⟨k, hk⟩ := hLev.1
    omega)
  by_cases hK0 : Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) ≠ 0
  · obtain ⟨a, ha⟩ := GlobalTheory.TwistScalarField.twist_scalar_mem_range D G Pl0 T0 A T R F κ v₀ fw O hT hC i hP v hv htm hQ hF hV hdel hMb hRun ℓ hLv hAc χ ξR ω φ hK Λ h N hU hTb hTM hLev hLa e Ps yd hh he hPs hPb hs hy hK0
    refine ⟨a, ?_, GlobalTheory.T.twisted_kernel_class_scalar_integral D G Pl0 T0 A T R F κ v₀ fw O hT hC i hP v hv htm hQ hF hV hdel hMb hRun ℓ hLv hAc χ ξR ω φ hK Λ h N hU hTb hTM hLev hLa e Ps yd hh he hPs hs hy hK0 a ha⟩
    rw [ha, hz]
    have hc : (((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 yd : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have hs2 : ((Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℝ) : ℂ) ^ 2 = ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℂ) ^ D.R.r) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
      push_cast; rfl
    have hmC : ((Λ.mIdx N D.R.r : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hm
    push_cast
    rw [GenLat.Ln] at *
    field_simp
    rw [hs2]
  · refine ⟨0, ?_, fun lam _ => ⟨1, fun h1 => lam.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simpa using isIntegral_zero⟩⟩
    rw [not_not] at hK0
    rw [hK0]
    simp

end GlobalTheory.TwistClassScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodularMatricesPreserveFrameLattices
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameRead

theorem exists_gl_preimage {O C : Type} [CommRing O] [CommRing C] (φ : O →+* C) (hφ : Function.Injective φ) {n : ℕ}
    (u : GL (Fin n) C) (h : ∀ a b, u.val a b ∈ Set.range φ ∧ (u⁻¹).val a b ∈ Set.range φ) :
    ∃ u0 : GL (Fin n) O, Matrix.GeneralLinearGroup.map φ u0 = u := by
  choose M hM using fun a b => (h a b).1
  choose M' hM' using fun a b => (h a b).2
  have e1 : φ.mapMatrix (Matrix.of M) = u.val := by ext a b; simp [hM]
  have e2 : φ.mapMatrix (Matrix.of M') = (u⁻¹).val := by ext a b; simp [hM']
  have inj : Function.Injective (φ.mapMatrix : Matrix (Fin n) (Fin n) O →+* Matrix (Fin n) (Fin n) C) := fun A B hAB => by
    ext a b; exact hφ (congrFun (congrFun hAB a) b)
  have h1 : Matrix.of M * Matrix.of M' = 1 := inj (by rw [map_mul, map_one, e1, e2, Units.mul_inv])
  have h2 : Matrix.of M' * Matrix.of M = 1 := inj (by rw [map_mul, map_one, e1, e2, Units.inv_mul])
  refine ⟨⟨Matrix.of M, Matrix.of M', h1, h2⟩, Units.ext ?_⟩
  exact e1

theorem det_map_gl {O C : Type} [CommRing O] [CommRing C] (φ : O →+* C) {n : ℕ} (g : GL (Fin n) O) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map φ g) = Units.map φ.toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
  ext
  simp [Matrix.GeneralLinearGroup.map, RingHom.map_det]

theorem lamG_mem_lattices : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (F : Frame l ι n), Function.Injective F.emb → (∀ τ, Antitone (res n (lamW τ))) → ∀ u : ι → GL (Fin n) (PadicAlgCl l), (∀ τ a b, (u τ).val a b ∈ Set.range F.emb ∧ (u τ)⁻¹.val a b ∈ Set.range F.emb) → ∀ z, (z ∈ F.latN lamW → lamG (PadicAlgCl l) n lamW c u z ∈ F.latN lamW) ∧ (z ∈ F.latD lamW → lamG (PadicAlgCl l) n lamW c u z ∈ F.latD lamW) := by
  intro l _ ι _ _ n lamW c F hinj hlam u hu z
  choose u0 hu0 using fun τ => exists_gl_preimage F.emb hinj (u τ) (hu τ)
  have hu' : u = fun τ => Matrix.GeneralLinearGroup.map F.emb (u0 τ) := funext fun τ => (hu0 τ).symm
  subst hu'
  have hs : ((∏ τ, Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map F.emb (u0 τ)) ^ c τ : (PadicAlgCl l)ˣ) : PadicAlgCl l) =
      F.emb ((∏ τ, Matrix.GeneralLinearGroup.det (u0 τ) ^ c τ : F.Oˣ) : F.O) := by
    simp only [det_map_gl, ← map_zpow, ← map_prod]
    rfl
  have key : ∀ x, lamG (PadicAlgCl l) n lamW c (fun τ => Matrix.GeneralLinearGroup.map F.emb (u0 τ)) (GlobalTheory.LatBC.bc F.emb n lamW x) =
      GlobalTheory.LatBC.bc F.emb n lamW (((∏ τ, Matrix.GeneralLinearGroup.det (u0 τ) ^ c τ : F.Oˣ) : F.O) • grp F.O n lamW u0 x) := by
    intro x
    rw [lamG_apply, hs, ← GlobalTheory.LatBC.bc_grp, LinearMap.map_smulₛₗ]
  constructor
  · intro hz
    obtain ⟨x, rfl⟩ := (GlobalTheory.LatBC.latN_iff F lamW _).1 hz
    exact (GlobalTheory.LatBC.latN_iff F lamW _).2 ⟨_, (key x).symm⟩
  · intro hz
    obtain ⟨x, hx, rfl⟩ := (GlobalTheory.LatBC.latD_iff F lamW hlam _).1 hz
    refine (GlobalTheory.LatBC.latD_iff F lamW hlam _).2 ⟨_, ?_, (key x).symm⟩
    exact Submodule.smul_mem _ _ (Formalism.CohomologicalDescent.RealLocalDeltaNabla.nablaRep_mem_delta F.O ι (fun _ => n) (fun _ => n) (fun _ => le_rfl)
      (fun τ => res n (lamW τ)) u0 x hx)

end GlobalTheory.FrameRead
end
end

