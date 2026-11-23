module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumBasePointUniqueAllTuples
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0655
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLocalGroupsNormalFramesSplitPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0670
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0634
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0673
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1508
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0669
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0446
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0668

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSubgroupOfLocalComponentsSplitPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowAssemble
open GlobalTheory.RowRep GlobalTheory.RowBaseUniq
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {D : D7}

theorem piAt_idemSum {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) :
    infPart D e = 0 ∧ (∀ w ∈ P, piAt w e = 1) ∧ ∀ w ∉ P, piAt w e = 0 :=
  GlobalTheory.FunObj.Comparison₂.cpt_idemSum he

theorem isIdemSum_one {ew : AE D} {w : Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt ew w) : IsIdemSum ew {w} :=
  ⟨⟨fun _ => ew, fun _ hx => by rw [Finset.mem_singleton.1 hx]; exact h, by simp⟩, h.1.2.1⟩

theorem suppAt_one {e : AE D} {V : HSp D} : SuppAt e V 1 := fun i j => by
  change (e + cA D e) * (mt V 1 - 1) i j = (mt V 1 - 1) i j
  rw [show mt V (1 : GA D V) = 1 from rfl, sub_self]
  simp

theorem suppAt_mul {e : AE D} {V : HSp D} {g h : GA D V} (hg : SuppAt e V g) (hh : SuppAt e V h) :
    SuppAt e V (g * h) := by
  intro i j
  have e1 : mt V (g * h) - 1 = (mt V g - 1) * (mt V h - 1) + (mt V g - 1) + (mt V h - 1) := by
    rw [show mt V (g * h) = mt V g * mt V h from rfl]
    noncomm_ring
  have s : (e + cA D e) * ((mt V g - 1) * (mt V h - 1)) i j = ((mt V g - 1) * (mt V h - 1)) i j := by
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [← mul_assoc, hg i k]
  rw [e1, Matrix.add_apply, Matrix.add_apply, mul_add, mul_add, s, hg i j, hh i j]

theorem suppAt_of_le {e e' : AE D} {V : HSp D} {g : GA D V}
    (hf : (e' + cA D e') * (e + cA D e) = e' + cA D e') (h : SuppAt e' V g) : SuppAt e V g := fun i j => by
  linear_combination (1 - (e + cA D e)) * h i j + (mt V g - 1) i j * hf

theorem loc_eq_one {V : HSp D} {a : AE D} {g : GA D V} (h : SuppAt a V g) {u : Pl D.host.E}
    (hu : piAt u (a + cA D a) = 0) : GlobalTheory.StdFrames.loc u (Lev.finE V g) = 1 := by
  refine Units.ext ?_
  change (mt V g).map (piAt u) = (1 : Matrix (Fin V.rank) (Fin V.rank) (Kw u))
  rw [← Matrix.map_one (piAt u) (map_zero _) (map_one _)]
  refine Matrix.ext fun i j => ?_
  have k := congrArg (piAt u) (h i j)
  rw [RingHom.map_mul, hu, zero_mul, Matrix.sub_apply, RingHom.map_sub] at k
  exact sub_eq_zero.1 k.symm

theorem exists_subgroup_elem_localComponents_subset {V : HSp D} {P : Finset (Pl D.host.E)} {e : AE D} (H : Subgroup (GA D V)) (r : GA D V)
    (hw : ∀ w ∈ P, ∃ h ∈ H, SuppAt e V h ∧ GlobalTheory.StdFrames.loc w (Lev.finE V h) = GlobalTheory.StdFrames.loc w (Lev.finE V r) ∧
      ∀ u ∈ P, u ≠ w → GlobalTheory.StdFrames.loc u (Lev.finE V h) = 1) :
    ∀ Q ⊆ P, ∃ y ∈ H, SuppAt e V y ∧ (∀ u ∈ Q, GlobalTheory.StdFrames.loc u (Lev.finE V y) = GlobalTheory.StdFrames.loc u (Lev.finE V r)) ∧
      ∀ u ∈ P, u ∉ Q → GlobalTheory.StdFrames.loc u (Lev.finE V y) = 1 := by
  classical
  intro Q
  refine Finset.induction_on Q ?_ ?_
  · intro _
    exact ⟨1, H.one_mem, suppAt_one, by simp, fun u _ _ => by rw [map_one, map_one]⟩
  · intro w Q hwQ ih hQ
    obtain ⟨y, hy, sy, ly, oy⟩ := ih ((Finset.subset_insert _ _).trans hQ)
    obtain ⟨h, hh, sh, lh, oh⟩ := hw w (hQ (Finset.mem_insert_self _ _))
    refine ⟨y * h, H.mul_mem hy hh, suppAt_mul sy sh, fun u hu => ?_, fun u hu hn => ?_⟩
    · rw [map_mul, map_mul]
      rcases Finset.mem_insert.1 hu with hu | hu
      · rw [hu, oy w (hQ (Finset.mem_insert_self _ _)) hwQ, lh, one_mul]
      · rw [ly u hu, oh u (hQ (Finset.mem_insert_of_mem hu)) (fun h' => hwQ (h' ▸ hu)), mul_one]
    · rw [map_mul, map_mul, oy u hu (fun h' => hn (Finset.mem_insert_of_mem h')),
        oh u hu (fun h' => hn (h' ▸ Finset.mem_insert_self _ _)), one_mul]

theorem mem_of_loc : ∀ {D : D7} (V : HSp D) (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P →
    ∀ (H : Subgroup (GA D V)) (r : GA D V), SuppAt e V r →
    (∀ w ∈ P, ∀ ew : AE D, Formalism.L2.NTheta.IsIdemAt ew w → ∃ h ∈ H, SuppAt ew V h ∧
      GlobalTheory.StdFrames.loc w (Lev.finE V h) = GlobalTheory.StdFrames.loc w (Lev.finE V r)) → r ∈ H := by
  intro D V P e he H r hr hyp
  classical
  obtain ⟨e0, e1, e2⟩ := piAt_idemSum he
  obtain ⟨⟨es, hes, -⟩, hec⟩ := he
  have hce : ∀ u ∈ P, piAt u (cA D e) = 0 := fun u hu => by
    have k := congrArg (piAt u) hec
    rwa [RingHom.map_mul, e1 u hu, one_mul, map_zero] at k
  have key : ∀ w ∈ P, ∃ h ∈ H, SuppAt e V h ∧ GlobalTheory.StdFrames.loc w (Lev.finE V h) = GlobalTheory.StdFrames.loc w (Lev.finE V r) ∧
      ∀ u ∈ P, u ≠ w → GlobalTheory.StdFrames.loc u (Lev.finE V h) = 1 := by
    intro w hw
    obtain ⟨f0, f1, f2⟩ := piAt_idemSum (isIdemSum_one (hes w hw))
    have a : es w * e = es w := ae_ext (by rw [RingHom.map_mul, f0, zero_mul]) fun Q => by
      change piAt Q (es w * e) = piAt Q (es w)
      rw [RingHom.map_mul]
      by_cases hQ : Q = w
      · rw [hQ, f1 w (Finset.mem_singleton_self _), e1 w hw, one_mul]
      · rw [f2 Q (by simpa using hQ), zero_mul]
    have b : es w * cA D e = 0 := by rw [← a, mul_assoc, hec, mul_zero]
    have c : cA D (es w) * e = 0 := by
      have k := congrArg (cA D) b
      rwa [RingHom.map_mul, Formalism.L2.Theta.cA_cA, map_zero] at k
    have d : cA D (es w) * cA D e = cA D (es w) := by rw [← RingHom.map_mul, a]
    have hf : (es w + cA D (es w)) * (e + cA D e) = es w + cA D (es w) := by linear_combination a + b + c + d
    obtain ⟨h, hH, sh, lh⟩ := hyp w hw (es w) (hes w hw)
    refine ⟨h, hH, suppAt_of_le hf sh, lh, fun u hu hne => loc_eq_one sh ?_⟩
    have k := congrArg (piAt u) d
    rw [RingHom.map_mul, hce u hu, mul_zero] at k
    rw [RingHom.map_add (f := _), f2 u (by simpa using hne), ← k, add_zero]
  obtain ⟨y, hy, sy, ly, -⟩ := exists_subgroup_elem_localComponents_subset H r key P subset_rfl
  have k : e • mt V r = e • mt V y := smul_eq_of_loc e0 fun w => by
    by_cases hw : w ∈ P
    · exact .inr (ly w hw).symm
    · exact .inl (e2 w hw)
  have hry : r = y := Subtype.ext (Units.ext (eq_of_halves hr sy k (smul_conj k)))
  rw [hry]
  exact hy

end GlobalTheory.RowAssemble

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAlgebraicLiftedKernel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

namespace GlobalTheory.BotDictAlg

theorem applyAt0_isAlgebraic {D : D7} {N N' : ℕ} {P : MvPolynomial (GL3Theta.Idx D N N') ℂ} {G : TaylorLogMetric.VC D N N' → ℂ}
    (hP : ∀ α, IsAlgebraic ℚ (P.coeff α)) (hG : TaylorLogMetric.CoefIn D G TaylorLogMetric.Qbar) : IsAlgebraic ℚ (GL3Theta.applyAt0 D P G) := by
  rw [← mem_algebraicClosure_iff]
  unfold GL3Theta.applyAt0
  refine sum_mem fun α _ => mul_mem (mul_mem ((mem_algebraicClosure_iff).2 (hP α)) ?_) (hG α)
  exact prod_mem fun _ _ => natCast_mem _ _

theorem even_bot {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) : Even (A'.rank * WW.rank) := by
  refine Even.mul_left ?_ _
  have h1 := hX.rank
  have h2 := hX.rank'
  have h3 := hX.is.rank
  have h4 := SqNum.ranks_exact D i j
  rw [← h3, h1, h2]
  refine ⟨SqNum.halfRank D i j - (D.R.m - (j.1 + 1)) / 2 - (D.R.m - j.1) / 2, ?_⟩
  omega

end GlobalTheory.BotDictAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiEAtS0ColumnPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB

noncomputable section
namespace GlobalTheory.CharXFB.HeisenbergPairBadPlaces

theorem traceCharacter_trivial_heisenbergPair_at_badPlaces : All fun {D} _ _ {sc} {G} W _ => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m) (u : WO (G.V (.grid (2 * σ + 2 + 1) 0)) (G.V (.grid (2 * σ + 2) 0))), u ∈ latRow G (2 * σ + 2) → ∀ (p : Fin (σ + 1)) (v : GlobalTheory.FinPl.Pl D), v ∈ G.pl.S0 → psiE W.ψ (GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * hA _ (ratV fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev))) = 1 := by
  intro D hQ T L μ0 hL sc G W M hM σ h h' u hu p v hv
  have hb := _root_.GlobalTheory.DepthMap.smul_mulVec_mem_latV D hQ T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) u hu v hv
  have hC := _root_.GlobalTheory.CharXFB.PairAt.pair_mem_AA_AAbar G σ h h' u v hb p
  generalize hA _ _ _ = x at hC ⊢
  obtain ⟨-, -, h3, -, h5, -⟩ := GlobalTheory.SeeSaw.idV_props D W.ψ W.ψ_std v
  have hε : GlobalTheory.FinPlLoc.idem D (· = v) ∈ idAt D (· = v) := GlobalTheory.FinPlLoc.idem_mem_idAt _
  have hs : GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * x) ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ hε
  have hx0 : D.host.xi0 ≠ 0 := cmHost_imaginaryGenerator_ne_zero
  have hdI : GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * x) ∈ GlobalTheory.SeeSaw.idV (GlobalTheory.SeeSaw.dI D) v := by
    have e : GlobalTheory.SeeSaw.dI D = FractionalIdeal.spanSingleton _ D.host.xi0 * (D.host.AA * D.host.AAbar) := by
      unfold GlobalTheory.SeeSaw.dI; rw [mul_assoc]
    rw [e, h3 _ _ hx0]
    refine ⟨?_, hs⟩
    have e1 : incA D D.host.xi0⁻¹ * incA D D.host.xi0 = 1 := by rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
    convert hC using 1
    linear_combination (GlobalTheory.FinPlLoc.idem D (· = v) * x) * e1
  have h6 := (h5 _ hs).1 hdI _ (GlobalTheory.FinPlLoc.idem_mem_intAt _)
  have e2 : GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * x) * GlobalTheory.FinPlLoc.idem D (· = v) =
      GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * x) := by
    rw [mul_comm, ← mul_assoc, GlobalTheory.FinPlLoc.idem_mul_self]
  rwa [e2] at h6

end GlobalTheory.CharXFB.HeisenbergPairBadPlaces
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SquareTripleFinitePlacesOfOrientedRoutes
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TripleRam

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem not_nonSplitAt_of_emb {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : ¬ GlobalTheory.WeilParts.NonSplitAt D v ε := by
  intro h
  refine h.2 ⟨GlobalTheory.EmbChart.idem τ, GlobalTheory.EmbChart.isSplitIdem_idem τ, ?_⟩
  have he : ε = GlobalTheory.EmbChart.atPlace v 1 := by
    obtain ⟨α, rfl, h1, h0⟩ := hε
    rw [GlobalTheory.EmbChart.atPlace_apply]
    congr 1
    refine FiniteAdeleRing.ext _ fun u => ?_
    change evalV D.host.F u α = evalV D.host.F u (GlobalTheory.AdelicU.singleFin v 1)
    by_cases e : u = v
    · subst e; rw [GlobalTheory.AdelicU.evalV_singleFin_self, h1]
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne e, h0 u e]
  rw [he, GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.idem, ← LinearMap.map_add (f := _), add_sub_cancel]; rfl

theorem not_unramAt_of_forall {D : D7} {χ : (AE D)ˣ →* Circle} {v : HeightOneSpectrum (𝓞 D.host.F)}
    {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (h : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → ¬ GlobalTheory.LFun.UnrAt χ w) :
    ¬ GlobalTheory.WeilParts.UnramAt ε χ := by
  intro hu
  have := v.isPrime
  obtain ⟨Q, hQ, hl⟩ := (Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 D.host.E)).some
  let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
  have hw : w.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hl.over.symm
  exact h w hw (GlobalTheory.UnrOverPlace.unrAt_of_unramAt D χ v ε hε hu w hw)

theorem ram_clause : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m),
    SquareStanding G t → ∀ (M : Vol G), M.Is t → ∀ (en : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G ↑i ↑j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G ↑i ↑j) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) om om',
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t ↑i ↑j en Bs Γ X → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
      (GlobalTheory.WeilParts.UnramAt ε (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t ↑i ↑j) ∧ GlobalTheory.WeilParts.UnramAt ε (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G ↑i ↑j)) ∨
      (¬ GlobalTheory.WeilParts.NonSplitAt D v ε ∧ ¬ GlobalTheory.WeilParts.UnramAt ε (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t ↑i ↑j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G ↑i ↑j) ∧
        ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F)) := by
  intro D T L sc G μ₀ hL W t i j hS M hM en Bs Γ X om om' hX hT v ε hε
  by_cases hv : v ∈ X.T
  · right
    have hP : v ∈ Bs.P := hT.chars.sub hv
    refine ⟨not_nonSplitAt_of_emb hε (Bs.τ ⟨v, hP⟩), ?_, _root_.GlobalTheory.PsiDifferent.not_dvd_different_of_psiUnr hT.base.std (hT.base.psiP v hP)⟩
    rw [← hX.α, ← hX.β]
    exact not_unramAt_of_forall hε fun w hw => hT.chars.ram w (hw ▸ hv)
  · left
    rw [← hX.α, ← hX.β]
    exact ⟨_root_.GlobalTheory.UnrOverPlaceConv.unramAt_of_unrAt_all hε fun w hw => hT.chars.unrα w (fun h => hv (hw ▸ h)),
      _root_.GlobalTheory.UnrOverPlaceConv.unramAt_of_unrAt_all hε fun w hw => hT.chars.unrβ w (fun h => hv (hw ▸ h))⟩

end GlobalTheory.TripleRam

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TermDatumRowMoveLevelEdgeFactors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.FlatRowMove

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem fill_move (G : Grid k) (hs : 1 ≤ G.s) {j : ℕ} (hj : j + 1 < G.m)
    (κ : GL (Fin (G.rank (j + 1, G.m))) k) (x : ColArgs G) (y : RowArgs G) (e : Vars G) :
    fill hs x (Function.update (Function.update y j (y j * κ.val)) (j + 1) (κ⁻¹.val * y (j + 1))) e =
      G.moveArgs .one (Pi.mulSingle (j + 1, G.m) κ) (fill hs x y e) := by
  funext b
  cases b with
  | theta i l =>
    by_cases hi : i = G.m
    · subst hi
      have h1 : (Pi.mulSingle (j + 1, G.m) κ : G.VertexGroup) (G.m, l) = 1 :=
        Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _
      have h2 : (Pi.mulSingle (j + 1, G.m) κ : G.VertexGroup) (G.m, l + 1) = 1 :=
        Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _
      simp only [Grid.moveArgs, Edge.src, Edge.tgt, h1, h2, map_one, inv_one, Units.val_one,
        Matrix.one_mul, Matrix.mul_one, fill_theta]
    · simp [fill, Grid.moveArgs, hi]
  | ex i l =>
    by_cases hl : l = G.m
    · subst hl
      simp only [Grid.moveArgs, Edge.src, Edge.tgt, fill_ex]
      by_cases hij : i = j
      · subst hij
        have h1 : (Pi.mulSingle (i + 1, G.m) κ : G.VertexGroup) (i, G.m) = 1 :=
          Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h) _
        rw [h1, Pi.mulSingle_eq_same, Function.update_of_ne (by omega), Function.update_self,
          map_one, Units.val_one, Matrix.mul_one, Assignment.read, invT_inv_val, Matrix.transpose_mul]
      · by_cases hij' : i = j + 1
        · subst hij'
          have h1 : (Pi.mulSingle (j + 1, G.m) κ : G.VertexGroup) (j + 1 + 1, G.m) = 1 :=
            Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h) _
          rw [h1, Pi.mulSingle_eq_same, Function.update_self, map_one, inv_one, Units.val_one,
            Matrix.one_mul, Assignment.read, invT_val, Matrix.transpose_mul]
        · have h1 : (Pi.mulSingle (j + 1, G.m) κ : G.VertexGroup) (i, G.m) = 1 :=
            Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _
          have h2 : (Pi.mulSingle (j + 1, G.m) κ : G.VertexGroup) (i + 1, G.m) = 1 :=
            Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _
          rw [h1, h2, Function.update_of_ne hij', Function.update_of_ne hij]
          simp only [map_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
    · simp [fill, Grid.moveArgs, hl]

theorem mulSingle_comm (G : Grid k) {X : ℕ × ℕ} (κ : GL (Fin (G.rank X)) k) (g : G.VertexGroup) (hg : g X = 1) :
    Pi.mulSingle X κ * g = g * Pi.mulSingle X κ := by
  funext Y
  by_cases hY : Y = X
  · subst hY; simp [hg]
  · simp [Pi.mulSingle_eq_of_ne hY]

variable [MeasurableSpace k] [BorelSpace k]

theorem flat_move (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) (keep : Bool)
    (g : G.VertexGroup) (T : G.Args → ℂ) {j : ℕ} (hj : j + 1 < G.m) (κ : GL (Fin (G.rank (j + 1, G.m))) k)
    (hg : g (j + 1, G.m) = 1)
    (hT : G.pathAct .one (oppositePath G.m) (Pi.mulSingle (j + 1, G.m) κ) T = T) (x : ColArgs G) (y : RowArgs G) :
    ((oppositePath G.m).map (G.edgeFactor .one (Pi.mulSingle (j + 1, G.m) κ))).prod *
      flatTensor hs ψ ν (GlobalTheory.FunObj.moved G keep g T) x
        (Function.update (Function.update y j (y j * κ.val)) (j + 1) (κ⁻¹.val * y (j + 1))) =
      flatTensor hs ψ ν (GlobalTheory.FunObj.moved G keep g T) x y := by
  have hF : ∀ z, ((oppositePath G.m).map (G.edgeFactor .one (Pi.mulSingle (j + 1, G.m) κ))).prod *
      GlobalTheory.FunObj.moved G keep g T (G.moveArgs .one (Pi.mulSingle (j + 1, G.m) κ) z) = GlobalTheory.FunObj.moved G keep g T z := by
    intro z
    have h := congrFun (congrArg (G.pathAct .one (oppositePath G.m) g) hT) z
    rw [← Grid.pathAct_mul, ← mulSingle_comm G κ g hg, Grid.pathAct_mul] at h
    simp only [GlobalTheory.FunObj.moved]
    rw [← h]
    simp only [Grid.pathAct]
    ring
  simp only [flatTensor, flatIntegrand, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  simp only [fill_move G hs hj κ x y e, ← mul_assoc, hF]

theorem term_datum_move : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} (β : CosFam G t) {μ₀ : T}, L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → ∀ (w : locPl G t) (j : ℕ), j + 1 < D.R.m →
    ∀ (κ : GL (Fin ((locGrid G t w.1).rank (j + 1, (locGrid G t w.1).m))) (Kw w.1)), κ ∈ givenLevel G t w.1 (j + 1, D.R.m) →
    ∀ (x : ColArgs (locGrid G t w.1)) (y : RowArgs (locGrid G t w.1)),
    ((oppositePath D.R.m).map ((locGrid G t w.1).edgeFactor .one (Pi.mulSingle (j + 1, D.R.m) κ))).prod *
      (S.term t Φ β w).datum x (Function.update (Function.update y j (y j * κ.val)) (j + 1) (κ⁻¹.val * y (j + 1))) =
    (S.term t Φ β w).datum x y := by
  intro D T L sc G W U S t Φ β μ₀ hL hde hc ht w j hj κ hκ x y
  have hT := _root_.GlobalTheory.FlipVertexInv.main S Φ ht hL hde hc w.1 w.2 j hj κ hκ
  have hg : ((repsAt G t w.1).elt (β w)) (j + 1, D.R.m) = 1 := by
    simp only [Reps.elt, onColumn]
    exact dif_neg (by show j + 1 ≠ D.R.m; omega)
  exact flat_move (locGrid G t w.1) _ _ _ _ _ _ hj κ hg hT x y

end GlobalTheory.FlatRowMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumScalarsEqProductEdgeFactorsRowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_scalars_eq_product_edge_factors_row : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ₀ : T}, L.Is μ₀ → ∀ {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)),
    finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ (c₁ c₂ : ℂ),
    W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (S.Z.vac (.chi j D.R.m)) = c₁ • S.Z.vac (.chi j D.R.m) →
    W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (S.Z.vac (.chi (j + 1) D.R.m)) =
      c₂ • S.Z.vac (.chi (j + 1) D.R.m) →
    c₁ * c₂ = ∏ w : locPl G t, ((oppositePath D.R.m).map ((locGrid G t w.1).edgeFactor .one (Pi.mulSingle (j + 1, D.R.m)
      (inBasis (rank_vertex G t w.1 (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w.1
        (finG (G.V (.grid (j + 1) D.R.m)) k))))).prod := by
  first | exact @GlobalTheory.RowVacScalar.scalars_eq_edgeFactors | exact GlobalTheory.RowVacScalar.scalars_eq_edgeFactors | (intros; apply GlobalTheory.RowVacScalar.scalars_eq_edgeFactors <;> assumption)
end

