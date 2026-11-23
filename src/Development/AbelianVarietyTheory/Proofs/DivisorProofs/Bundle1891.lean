module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0009
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0855
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0817
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0869
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1821
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransporterMovesNearbyFramesOfDense
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1838
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalGlEmbeddingTheta
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.HostSize

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairLocalSchwartzAction
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.IntertwLocal.local_intertw : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ (v : Pl (F := F)) (x : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (φ φ₁ φ₂ φ₃ φ₄ : (Fin n × Fin d → Fv F v) → ℂ), φ ∈ SB (Fin n × Fin d → Fv F v) → φ₁ ∈ SB (Fin n × Fin d → Fv F v) →
    φ₂ ∈ SB (Fin n × Fin d → Fv F v) → Acts (evFin F v) (M.co.rho B.ψ u) φ φ₁ → Acts (evFin F v) (om x) φ φ₂ →
    Acts (evFin F v) (om x) φ₁ φ₃ → Acts (evFin F v) (M.co.rho B.ψ (mat x.1 * u * (mat x.2)ᵀ)) φ₂ φ₄ → φ₄ = φ₃ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v x u φ φ₁ φ₂ φ₃ φ₄ hφ hφ₁ hφ₂ h1 h2 h3 h4
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hP.weil
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin n × Fin d) v
  have hΦ : tens (evFin F v) φ R ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) := (hR φ hφ).2
  have himpl := hW.impl x u (tens (evFin F v) φ R) hΦ
  have hact : GlobalTheory.WeilM.actAB (cA σ) x u = mat x.1 * u * (mat x.2)ᵀ := rfl
  rw [hact] at himpl
  have key : tens (evFin F v) φ₄ R = tens (evFin F v) φ₃ R := by
    rw [← h4 R (hR φ₂ hφ₂), ← h2 R (hR φ hφ), ← himpl, h1 R (hR φ hφ), h3 R (hR φ₁ hφ₁)]
  funext t
  have hz : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i)) := by
    intro u' hu'; funext i; exact GlobalTheory.LatVac.at_liftV v _ u' hu'
  have hRz : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by
    simpa using (hR φ hφ).1 0 _ hz
  have := congrFun key (fun i => GlobalTheory.LatVac.liftV v (t i))
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hRz] at this
  exact mul_right_cancel₀ hR0 this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRuleBoundedBelow
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ThetaLow
open GlobalTheory.ThetaBound GlobalTheory.PlaceInt

theorem finite_vLa_ne_zero {K : Type} [Field K] [NumberField K] (x : K) :
    {w : HeightOneSpectrum (𝓞 K) | vLa w x ≠ 0}.Finite := by
  by_cases hx : x = 0
  · subst hx
    simpa [vLa] using (Set.finite_empty : (∅ : Set (HeightOneSpectrum (𝓞 K))).Finite)
  · refine (GlobalTheory.QNorm.finite_valuation_ne_one K (Units.mk0 x hx)).subset fun w hw h1 => hw ?_
    simp only [Units.val_mk0] at h1
    simp [vLa, h1]

theorem vLa_natCast_eq_zero {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {g p : ℕ}
    (hg : ((g : ℕ) : 𝓞 K) ∈ w.asIdeal) (hc : Nat.Coprime g p) : vLa w ((p : ℕ) : K) = 0 := by
  have hp : ((p : ℕ) : 𝓞 K) ∉ w.asIdeal := by
    intro hp
    obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 K))
    apply w.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← huv]
    simp only [eq_intCast, Int.cast_natCast]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hg) (Ideal.mul_mem_left _ _ hp)
  have h1 : w.valuation K ((p : ℕ) : K) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 K) K) p, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hp
  simp [vLa, h1]

theorem thetaRule_bounded_below : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (g g' : ℕ) (π π' : 𝓞 D.host.E), HalfSplit l g g' π π' → Nat.Coprime (g * g') (D.host.QS * D.host.q * D.host.d) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∃ m : HeightOneSpectrum (𝓞 c.F) → ℝ, (Function.support m).Finite ∧ (∀ f ∈ thGen Xo c nab a n, ∀ w, ∀ v ∈ valSet Xo c (algCls Xo c) w, ((m w : ℝ) : EReal) ≤ v f) ∧ ∀ w : HeightOneSpectrum (𝓞 c.F), (((g : ℕ) : 𝓞 c.F) ∈ w.asIdeal ∨ ((g' : ℕ) : 𝓞 c.F) ∈ w.asIdeal) → m w = -((vLa w (nrm Dw c a (star π * star π')) : ℤ) : ℝ) := by
  intro D H Dw l Xo c
  letI := H.starRing
  intro nab hnab g g' π π' hs hcop a n
  have hstar : ∀ x : 𝓞 D.host.E, star x = H.bar x := hnab.1
  obtain ⟨hg, hg', hne, hM, hπ, hπ', hMb, -, -⟩ := hs
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hπ
    exact hg.ne_zero (by exact_mod_cast hπ.symm)
  have hπ0' : π' ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hπ'
    exact hg'.ne_zero (by exact_mod_cast hπ'.symm)
  have hb0 : star π * star π' ≠ 0 := by
    rw [hstar, hstar]
    refine mul_ne_zero (fun h => hπ0 ?_) (fun h => hπ0' ?_)
    · rw [← TorsFac.bar_bar (H := H) π, h, map_zero]
    · rw [← TorsFac.bar_bar (H := H) π', h, map_zero]
  let ρ : HeightOneSpectrum (𝓞 c.F) → ℝ := fun w =>
    ∑ p ∈ D.host.condN.primeFactors, ((vLa w ((p : ℕ) : c.F) : ℤ) : ℝ) *
      D.host.vdH p * (Formalism.L2.Pj.DF Dw a : ℝ) / 2
  refine ⟨fun w => -(ρ w + ((vLa w (nrm Dw c a (star π * star π')) : ℤ) : ℝ)), ?_, ?_, ?_⟩
  ·
    have hfin : ((⋃ p ∈ D.host.condN.primeFactors,
        {w : HeightOneSpectrum (𝓞 c.F) | vLa w ((p : ℕ) : c.F) ≠ 0}) ∪
        {w | vLa w (nrm Dw c a (star π * star π')) ≠ 0}).Finite :=
      (Set.Finite.biUnion (Finset.finite_toSet _) fun p _ => finite_vLa_ne_zero _).union (finite_vLa_ne_zero _)
    refine hfin.subset fun w hw => ?_
    by_contra hn
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists, not_not] at hn
    apply hw
    have h0 : ρ w = 0 := Finset.sum_eq_zero fun p hp => by rw [hn.1 p hp]; simp
    simp [h0, hn.2]
  · intro f hf w v hv
    obtain ⟨y, rfl⟩ := hv
    obtain ⟨T, io, e, ho, yI, hy, eta, heta, hq⟩ := y.2
    have hv : vAtV y f = nval T.V e (evI yI f) := by
      show y.1.1 f = _
      rw [hq]
      rfl
    rw [hv]
    refine bound_of_chBound Xo c (star π * star π') hb0 ?_ nab hnab w a n (ρ w) ?_ T io e ho yI hy f hf
    · intro ℓ hp hd
      rw [hM] at hd ⊢
      rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h1
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hg').1 h1
        refine ⟨fun h2 => hne ?_, star π', star π, _root_.mul_comm _ _, ?_, ?_⟩
        · rw [pow_two] at h2
          exact ((Nat.prime_dvd_prime_iff_eq hg' hg).1 (Nat.dvd_of_mul_dvd_mul_left hg'.pos h2)).symm
        · rw [hstar, TorsFac.bar_bar, _root_.mul_comm]; exact hπ'
        · rw [hMb, hstar, TorsFac.bar_bar, Ideal.span_singleton_le_span_singleton]
          exact Dvd.intro_left _ rfl
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hg).1 h1
        refine ⟨fun h2 => hne ?_, star π, star π', rfl, ?_, ?_⟩
        · rw [pow_two] at h2
          exact (Nat.prime_dvd_prime_iff_eq hg hg').1 (Nat.dvd_of_mul_dvd_mul_right hg.pos h2)
        · rw [hstar, TorsFac.bar_bar, _root_.mul_comm]; exact hπ
        · rw [hMb, hstar, TorsFac.bar_bar, Ideal.span_singleton_le_span_singleton]
          exact Dvd.intro _ rfl
    · intro T' io' y' C' e' ho'
      have hc := HostChart.chBound_host D H Dw l Xo c hstar T' io' y' C' e' ho'.1 a n
        (Formalism.L2.Pj.DF Dw a) le_rfl
      convert hc using 1
      refine Finset.sum_congr rfl fun p _ => ?_
      have h1 := ho'.2 ((p : ℕ) : c.F)
      rw [map_natCast] at h1
      have he : (e' : ℝ) ≠ 0 := by exact_mod_cast ho'.1.ne'
      rw [h1]
      push_cast
      rw [mul_div_cancel_left₀ _ he]
  · intro w hw
    have h0 : ρ w = 0 := Finset.sum_eq_zero fun p hp => by
      have hcp : Nat.Coprime (g * g') p := Nat.Coprime.coprime_dvd_right (Nat.dvd_of_mem_primeFactors hp) hcop
      rcases hw with hw | hw
      · rw [vLa_natCast_eq_zero w hw (Nat.Coprime.coprime_dvd_left (dvd_mul_right g g') hcp)]; simp
      · rw [vLa_natCast_eq_zero w hw (Nat.Coprime.coprime_dvd_left (dvd_mul_left g' g) hcp)]; simp
    show -(ρ w + _) = _
    rw [h0, zero_add]
end GlobalTheory.ThetaLow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRulesExistAndCusp
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem thetaRules_exist_and_cusp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), 1 ≤ r → (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (nab : NabV Xo c), IsNab Xo c nab → ThValTot Xo c nab ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → LastPos Dw a → ∀ f ∈ thGen Xo c nab a n, f ∈ cuspW Xo c U (wtZ a n) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro r U hr hU nab hn
  refine ⟨GlobalTheory.thValTot_of_chartIndep GlobalTheory.firstFiveLaws.1 GlobalTheory.chartIndependence_unconditional E H Dw l Xo c nab hn, ?_⟩
  intro a n hd hl f hf
  rw [GlobalTheory.AllWt.cuspW_wtZ, ← Formalism.L2.PjFree.cusp_ofPj]
  exact GlobalTheory.Dict.thInCusp_cusp GlobalTheory.chartIndependence_unconditional E H Dw l Xo c r
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) hr
    (fun σ hσ => (Formalism.L2.PjFree.isUnf_ofPj _).2 (hU σ ((Formalism.L2.PjFree.goodEmb_iff σ).1 hσ))) nab hn a n hd hl f hf

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTraceLevelCompatibleProof
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceLevelPf

variable {D : D7} {S T : HSp D}

theorem series_om_fin {B : Base S T} (hB : B.Good) {χS χT : (AE D)ˣ →* Circle} {ω : PairRep S T}
    (hω : IsWeilDatumO B.F.ψ S T χS χT ω) {f : WO S T → ℂ} (hf : IsThetaFunO B.F.ψ S T f) (h : GA D S)
    (P : PolF D T.rank S.rank) (g : GA D T) {κ : GA D T} (hκ : κ ∈ GfC T) :
    series B.F ω (ω (1, κ) f) h P g = series B.F ω f h P (g * κ) := by
  rw [series_apply, series_apply]
  have e : ((h, g * κ) : GA D S × GA D T) = (h, g) * (1, κ) := Prod.ext (mul_one h).symm rfl
  rw [e, map_mul, Module.End.mul_apply, Frame.fock, Frame.fock,
    GlobalTheory.OrientedHeis.om_fin_pureTensorO B.F.ψ S T χS χT ω hω B.F.θ hB.frame.vac.2.inf 1 (one_mem _) κ hκ _ _ _ _ f P hf]

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}
  {B : Base (Vc D i) (Wc D i)}

theorem rTup_datWp_val (x : GL (Fin (Wc D i).rank) (EAf D)) (PP : ↥(R.datWp i R.triv).Pg) (a b : Fin (R.datWp i R.triv).r) :
    (rTup (R.βW i) (R.datWp i R.triv) x PP).val a b =
      (redFn (R.βW i) PP.1 x).val (Fin.castLE (R.datWp i R.triv).hr a) (Fin.castLE (R.datWp i R.triv).hr b) := by
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hm : redFn (R.βW i) PP.1 x ∈ blockTri (blk2 (R.datWp i R.triv).r) := by
    refine mem_blockTri.2 fun c d hcd => ?_
    have hc : c.val < (R.datWp i R.triv).r := lt_of_lt_of_eq c.2 rW
    have e : blk2 (R.datWp i R.triv).r c = 0 := if_pos hc
    exact absurd (lt_of_lt_of_eq hcd e) (Nat.not_lt_zero _)
  unfold rTup
  rw [upper_block_val_submatrix _ hm]
  rfl

theorem red_of_rTup (hB : BaseOf R i B) (e : G ≃* G0 B.G.Pg (Wc D i).rank)
    (hent : ∀ (g : G) (P : Pl D.host.E) (h : P ∈ B.G.Pg) (h' : P ∈ R.Pg) (a c : Fin (Wc D i).rank),
      (e g ⟨P, h⟩).val a c = (R.eG g ⟨P, h'⟩).val (Fin.cast (rank_Wc i) a) (Fin.cast (rank_Wc i) c)) (g : G) (x : GL (Fin (Wc D i).rank) (EAf D))
    (hx : rTup (R.βW i) (R.datWp i R.triv) x = R.eG g) : ∀ PP : ↥B.G.Pg, e g PP = redFn B.F.βT PP.1 x := by
  intro PP
  have hP : PP.1 ∈ R.Pg := hB.Pg ▸ PP.2
  refine Units.ext (Matrix.ext fun a c => ?_)
  have h1 := congrArg (fun y : G0 (R.datWp i R.triv).Pg (R.datWp i R.triv).r => (y ⟨PP.1, hP⟩).val (Fin.cast (rank_Wc i) a)
    (Fin.cast (rank_Wc i) c)) hx
  simp only at h1
  rw [rTup_datWp_val] at h1
  rw [hent g PP.1 PP.2 hP a c]
  exact h1.symm.trans (by rw [hB.βT]; rfl)

theorem rTup_of_red (hB : BaseOf R i B) (e : G ≃* G0 B.G.Pg (Wc D i).rank)
    (hent : ∀ (g : G) (P : Pl D.host.E) (h : P ∈ B.G.Pg) (h' : P ∈ R.Pg) (a c : Fin (Wc D i).rank),
      (e g ⟨P, h⟩).val a c = (R.eG g ⟨P, h'⟩).val (Fin.cast (rank_Wc i) a) (Fin.cast (rank_Wc i) c)) (g : G) (x : GL (Fin (Wc D i).rank) (EAf D))
    (hx : ∀ PP : ↥B.G.Pg, e g PP = redFn B.F.βT PP.1 x) : rTup (R.βW i) (R.datWp i R.triv) x = R.eG g := by
  funext PP
  have hP : PP.1 ∈ B.G.Pg := hB.Pg ▸ PP.2
  refine Units.ext (Matrix.ext fun a c => ?_)
  have h1 := hent g PP.1 hP PP.2 (Fin.cast (rank_Wc i).symm a) (Fin.cast (rank_Wc i).symm c)
  rw [hx ⟨PP.1, hP⟩, hB.βT] at h1
  rw [rTup_datWp_val]
  exact h1

theorem lifts_of_datWp (hB : BaseOf R i B) (e : G ≃* G0 B.G.Pg (Wc D i).rank)
    (hent : ∀ (g : G) (P : Pl D.host.E) (h : P ∈ B.G.Pg) (h' : P ∈ R.Pg) (a c : Fin (Wc D i).rank),
      (e g ⟨P, h⟩).val a c = (R.eG g ⟨P, h'⟩).val (Fin.cast (rank_Wc i) a) (Fin.cast (rank_Wc i) c)) {g : G} {κ : GA D (Wc D i)}
    (hκ : Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ) : GlobalTheory.ExportType.Lifts B (e g) κ :=
  ⟨hκ.1, hB.βT ▸ parLev_St hκ.2.1, red_of_rTup hB e hent g _ hκ.2.2⟩

theorem exists_lift_datWp (hB0 : B.Good) (hB : BaseOf R i B) (e : G ≃* G0 B.G.Pg (Wc D i).rank)
    (hent : ∀ (g : G) (P : Pl D.host.E) (h : P ∈ B.G.Pg) (h' : P ∈ R.Pg) (a c : Fin (Wc D i).rank),
      (e g ⟨P, h⟩).val a c = (R.eG g ⟨P, h'⟩).val (Fin.cast (rank_Wc i) a) (Fin.cast (rank_Wc i) c)) (g : G) :
    ∃ κ, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ := by
  obtain ⟨κ, hκ, -⟩ := GlobalTheory.TypeSupportLift.exists_lift_supp B hB0 (e g)
  have h1 := GlobalTheory.FlatVecSum.levelLift_isLift_principalLevelDatum_realisation hB hκ
  rw [rTup_of_red hB e hent g _ (GlobalTheory.ExportType.lifts_of_isLiftG0 hκ).red] at h1
  exact ⟨κ, h1⟩

end Real

theorem traceLevel : GlobalTheory.BaseCmp.TraceLevel := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i B hB hBo U ψ e hent hU hchi ω hω hh P
  classical
  have hW : IsWeilDatumO B.F.ψ (Vc D i) (Wc D i) _ _ ω := hω
  have hlift := fun g => exists_lift_datWp hB hBo e hent g
  haveI : Fintype B.G.P.H := Fintype.ofFinite _
  have hfθ : IsThetaFunO B.F.ψ (Vc D i) (Wc D i) (GlobalTheory.FlatVecSum.princ B).vecBase :=
    GlobalTheory.GalLift.Vec.theta_of_thetaAt hB.frame.vac.1 hB.frame.vac.2.inf
      (Base.isThetaAt_vecAt (GlobalTheory.FlatVecSum.princ_good hB) (Base.admissible_empty_of_good (GlobalTheory.FlatVecSum.princ_good hB)) _)
      hB.frame.vac.2.theta
  have hsum : B.vecBase = ∑ p : B.G.P.H, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) •
      ω (1, (hlift (e.symm p)).choose) (GlobalTheory.FlatVecSum.princ B).vecBase := by
    have := GlobalTheory.FlatVecSum.vecFlat_eq_sum_princ hB (D.sp.V_sig _) (Twist.triv_good splitSet_empty) (Base.admissible_empty_of_good hB)
      (ω := ω) hω (fun p => (hlift (e.symm p)).choose) (fun p => by
        have := lifts_of_datWp hBo e hent (hlift (e.symm p)).choose_spec
        rwa [MulEquiv.apply_symm_apply] at this)
    rwa [Base.vecFlat_triv, Base.vecFlat_triv] at this
  funext x
  have hL : levelTrace R i U ψ ((GlobalTheory.FlatVecSum.princ B).theta ω hh P) x =
      ∑ g, (if hg : g ∈ U then D.what₂.embLL (((ψ ⟨g, hg⟩)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) else 0) *
        series B.F ω (GlobalTheory.FlatVecSum.princ B).vecBase hh P (x * (hlift g).choose) := by
    unfold levelTrace gaL
    rw [LinearMap.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    show Lev.actG0 _ _ _ _ _ x = _
    rw [Lev.actG0]
    split_ifs with hk
    · rw [GlobalTheory.CuspMult.EqCut.levChi_flag rfl rfl, inv_one]
      exact one_mul _
    · exact absurd (hlift g) hk
  have hR : B.theta ω hh P x = ∑ p : B.G.P.H, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) *
      series B.F ω (GlobalTheory.FlatVecSum.princ B).vecBase hh P (x * (hlift (e.symm p)).choose) := by
    rw [Base.theta, hsum, GlobalTheory.SpecFac.series_sum hB ω _ _ _ (fun p _ => hW.om_pres _ _ hfθ)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [series_om_fin hB hW hfθ hh P x (hlift (e.symm p)).choose_spec.1]
  rw [hL, hR]
  symm
  refine Fintype.sum_of_injective (fun p : B.G.P.H => e.symm p) (fun p q hpq => Subtype.ext (e.symm.injective hpq)) _ _
    (fun g hg => ?_) (fun p => ?_)
  · rw [dite_eq_right, zero_mul]
    intro hgU
    exact hg ⟨⟨e g, (hU g).2 hgU⟩, e.symm_apply_apply g⟩
  · have hp : e.symm p ∈ U := (hU _).1 (by rw [MulEquiv.apply_symm_apply]; exact p.2)
    have key : ((B.G.P.chi p : ℂˣ) : ℂ) = D.what₂.embLL ((ψ ⟨e.symm p, hp⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
      have hp' : e (e.symm p) ∈ B.G.P.H := by rw [MulEquiv.apply_symm_apply]; exact p.2
      have := hchi ⟨e.symm p, hp⟩ hp'
      have hpe : (⟨e (e.symm p), hp'⟩ : B.G.P.H) = p := Subtype.ext (e.apply_symm_apply p)
      rw [hpe] at this
      exact this
    rw [dite_eq_left hp, Units.val_inv_eq_inv_val, key, Units.val_inv_eq_inv_val, map_inv₀]

end GlobalTheory.TraceLevelPf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransporterMovesAllFramesOfDenseOpen
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem movesAt_of_dense : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∀ (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E) (hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a) (O : Set (Frame ((uAt r v i).X k).Ψ D.R.r)), IsOpen O → O.Nonempty → O ⊆ ((uAt r v i).X k).dom → O ⊆ closure {x | ∃ hx : x ∈ ((uAt r v i).X k).dom, MovesAt p r i v γ k k' a hm x hx} → ∀ (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom), MovesAt p r i v γ k k' a hm x hx := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hp r h hr i v γ k k' a hm O hO hOn hOd hOc x hx
  obtain ⟨o, ho⟩ := hOn
  obtain ⟨h1, k'', c, hc, hM⟩ := _root_.GlobalTheory.ShareOn.movesAt_nhds_of_dense p hp r h hr i v γ k k' a hm o (hOd ho)
  obtain ⟨N, hN, hNM⟩ := h1 (Filter.mem_of_superset (hO.mem_nhds ho) hOc)
  exact _root_.GlobalTheory.ShareOn.movesAt_of_movesAt_open p hp r h hr i v γ k k' k'' a c hm hc (interior N ∩ O) (isOpen_interior.inter hO)
    ⟨o, mem_interior_iff_mem_nhds.2 hN, ho⟩ (fun w hw => hOd hw.2)
    (fun w hw hwW => ⟨hNM w hw (interior_subset hwW.1), hM w hw⟩) x hx (hM x hx)

end GlobalTheory.ShareOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalGlEmbeddingThetaStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_local_gl_embedding_theta : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (K : GL (Fin a') (Fv F v) →* UA σ G.V'.J), (∀ g, K g ∈ UAt σ G.V' (evFin F v) ∧
      (mat (K g)).map (piW t) = g.val ∧
      (mat (K g)).map (piW (t.comp σ)) = (G.V'.J.map t)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map t) →
    ∀ (S : GL (Fin a') (Fv F v) → (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) → ((Fin a' × Fin (a + a')) → Fv F v) → ℂ),
    (∀ g, ∀ φ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), S g φ ∈ SB _ ∧ Acts (evFin F v) (om' (K g, 1)) φ (S g φ)) →
    ∀ (ν α : (Fv F v)ˣ →* ℂˣ) (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι → (∀ g, ∀ φ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ι (S g φ) = GlobalTheory.SplitFlip.omB ν α g 1 (ι φ)) →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) d' dd →
    ∀ (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J)) →* Module.End ℂ (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUSplitting (adeleClass F) B.ψ dd (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) omd →
    (∀ (g : UA σ G.V'.J) (gd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))),
      ((gd : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks (mat g) 0 0 1 →
      ∀ φ₁ ∈ schA F (Fin a' × Fin (a + a')), ∀ φ₂ ∈ schA F (Fin a' × Fin (a + a')), omd gd (boxFun φ₁ φ₂) = boxFun (om' (g, 1) φ₁) φ₂) →
    ∀ (g : GL (Fin a') (Fv F v)) (gd' : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))),
      ((gd' : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks 1 0 0 (mat (K g)) →
    ∀ φ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ φ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
      Acts (evFin F v) (omd gd') (boxFun φ₁ φ₂) (boxFun φ₁ (fun x =>
        ((ν (GlobalTheory.SplitFlip.gdet g) : ℂ) / starRingEnd ℂ (ν (GlobalTheory.SplitFlip.gdet g) : ℂ)) *
          starRingEnd ℂ (S g (fun y => starRingEnd ℂ (φ₂ y)) x))) := by
  first | exact @GlobalTheory.DblSwap.diagR_acts | exact GlobalTheory.DblSwap.diagR_acts | (intros; apply GlobalTheory.DblSwap.diagR_acts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeHermitianRankAndHostDegreeEq
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

namespace GlobalTheory.RankHostFacts

theorem two_le_r_and_fdeg (D : D7) : 2 ≤ D.R.r ∧ ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f := by
  refine ⟨Formalism.L2.Geo.two_le_r D, ?_⟩
  unfold ReciprocityTheory.ChartRestriction.G.FD.fdeg
  rw [Formalism.L2.Pj.hostSize_finrank D]
  omega

theorem main : ∀ D : D7, 2 ≤ D.R.r ∧ ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f :=
  two_le_r_and_fdeg

end GlobalTheory.RankHostFacts
end

