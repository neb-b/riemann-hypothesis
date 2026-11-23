module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtDivMulEqSqrtMul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameOfRealizationModels
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtaComparisonIffForall
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitProductRescaleDisjointFinsets
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1468
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0515
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2690
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0257

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeTermGeneratorConstantViaFrame
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.HeckeGenConst

open ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues Formalism.IndefR.Datum

theorem eq_zero_of_rat_span {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [Module ℚ V] (M : Submodule ℚ V)
    (hM : Submodule.span ℝ (M : Set V) = ⊤) {f : V → ℂ} (hf : Continuous f) (h0 : ∀ z ∈ M, f z = 0) (z : V) : f z = 0 := by
  have hcl : ∀ z, z ∈ closure (M : Set V) := by
    intro z
    have hz : z ∈ Submodule.span ℝ (M : Set V) := hM ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx => exact subset_closure hx
    | zero => exact subset_closure M.zero_mem
    | add x y _ _ hx hy => exact M.toAddSubgroup.topologicalClosure.add_mem hx hy
    | smul c x _ hx =>
      have h1 : ∀ q : ℚ, (q : ℝ) • x ∈ closure (M : Set V) := fun q =>
        map_mem_closure (f := fun y : V => (q : ℝ) • y) (continuous_const_smul _) hx fun y hy => by
          beta_reduce; rw [Rat.cast_smul_eq_qsmul]; exact M.smul_mem q hy
      exact (Rat.denseRange_cast (𝕜 := ℝ)).induction_on (p := fun c : ℝ => c • x ∈ closure (M : Set V)) c
        (isClosed_closure.preimage (continuous_id.smul continuous_const)) h1
  exact (isClosed_eq hf continuous_const).closure_subset_iff.2 h0 (hcl z)

variable {D : D7}

section Period

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom}

theorem perVec_add (Wt : UnfAt U k x) (v w : Fin r → D.host.E) : perVec Wt (v + w) = perVec Wt v + perVec Wt w := by
  have he : ∀ τ : D.host.E →+* ℂ, Data.emb τ (v + w) = Data.emb τ v + Data.emb τ w := fun τ => by
    funext a; simp [Data.emb]
  funext j
  simp only [perVec, Pi.add_apply]
  unfold perFr
  split_ifs <;> simp [he, Matrix.mulVec_add, hermC, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem perVec_smul (Wt : UnfAt U k x) (q : ℚ) (v : Fin r → D.host.E) : perVec Wt (q • v) = q • perVec Wt v := by
  have he : ∀ τ : D.host.E →+* ℂ, Data.emb τ (q • v) = (q : ℂ) • Data.emb τ v := fun τ => by
    funext a; simp [Data.emb, Rat.smul_def]
  funext j
  simp only [perVec, Pi.smul_apply, Rat.smul_def]
  unfold perFr
  split_ifs
  · rw [he, Matrix.mulVec_smul]; rfl
  · simp
  · simp only [he, hermC, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul, map_ratCast]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  · simp
  · simp

theorem exists_theta_perVec_ne_zero {Wt : UnfAt U k x} (Y : UnitAt Wt) :
    ∃ v : Fin r → D.host.E, Y.θ (perVec Wt v) ≠ 0 := by
  by_contra hne
  push Not at hne
  let L : (Fin r → D.host.E) →ₗ[ℚ] (Fin Wt.g → ℂ) := ⟨⟨perVec Wt, perVec_add Wt⟩, perVec_smul Wt⟩
  have h0 := eq_zero_of_rat_span (LinearMap.range L) (by
    rw [eq_top_iff, ← Wt.per.2.2.2.1]
    refine Submodule.span_mono ?_
    rintro _ ⟨a, rfl⟩
    exact ⟨_, perVec_lat Wt a⟩) (GlobalTheory.EtaPinnedCompare.theta_entire Y).continuous (by
    rintro _ ⟨v, rfl⟩
    exact hne v)
  have h9 := Y.c9
  simp [h0] at h9

end Period

theorem exists_const_of_orth {K : Type} [CommRing K] {n m : ℕ} {b b' g : Fin n → Fin n → K}
    (hb : ∀ a a', ∑ i, ∑ j, b' i a * g i j * b j a' = if a = a' then 1 else 0) (v : Fin m → K) :
    ∃ X : Matrix (Fin m) (Fin n) K, ∀ j a, ∑ n, X j n * b n a = v j := by
  refine ⟨fun j n => v j * ∑ a', ∑ i, b' i a' * g i n, fun j a => ?_⟩
  have h : ∑ n, (∑ a', ∑ i, b' i a' * g i n) * b n a = 1 := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun a' _ => Finset.sum_comm.trans (hb a' a)]
    simp
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [h, mul_one]

theorem exists_map_const {V : HSp D} {b : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (hb : IsONLatBasis V b) {m : ℕ}
    (v : Fin m → D.host.E) : ∃ X : Matrix (Fin m) (Fin V.rank) D.host.E, ∀ j a, ∑ n, X j n * b n a = v j :=
  exists_const_of_orth (b' := fun i a => star (b i a)) (g := V.gram) hb.1 v

theorem exists_frAt {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
    {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    (hM : R.IsModels) (ht : TieIn T R κ v₀) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hσ : σ = T.σ₀)
    (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (h : GA D (Wc D i)) :
    ∃ γ ∈ GQ (Wc D i), FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (dictW T i σ hV) γ h := by
  have e : res T (sg0 D A) = T.σ₀ := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0]
    exact res_embLL T ht.alg ht.laws.pins.2.2.1
  have hg : GoodEmb T.Q.c (res T (sg0 D A)) := e ▸ T.toCore.good_σ₀
  obtain rfl : σ = res T (sg0 D A) := hσ.trans e.symm
  obtain ⟨γ, h1, h2, -⟩ := (GlobalTheory.HolDict.BaseFrame.baseFrT_of_tieIn D G Pl0 T0 A T R κ v₀ hM ht i _ hg hV).2.2 h
  exact ⟨γ, h1, h2⟩

theorem cancel {ι : Type} [Fintype ι] {u ph K K' μ q w : ℂ} {e θ : ι → ℂ} (hph : ph ≠ 0) (hμ : μ ≠ 0) (hθ : ∀ a, θ a ≠ 0)
    (h1 : Complex.exp (Real.pi / 2 * ∑ a, e a) * (μ * q * w) = ph * K' * ∏ a, θ a)
    (h2 : u * (ph * K) * ∏ a, (Complex.exp (-(Real.pi / 2 * e a)) * θ a) = w) : u * (K * q) = μ⁻¹ * K' := by
  have h3 : Complex.exp (Real.pi / 2 * ∑ a, e a) * ∏ a, Complex.exp (-(Real.pi / 2 * e a)) = 1 := by
    rw [← Complex.exp_sum, ← Complex.exp_add, Finset.sum_neg_distrib, Finset.mul_sum, add_neg_cancel, Complex.exp_zero]
  have h4 : ∏ a, θ a ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hθ a
  rw [← h2, Finset.prod_mul_distrib] at h1
  rw [eq_inv_mul_iff_mul_eq₀ hμ]
  refine mul_left_cancel₀ (mul_ne_zero hph h4) ?_
  linear_combination h1 - μ * q * u * ph * K * (∏ a, θ a) * h3

end GlobalTheory.HeckeGenConst


open GlobalTheory.HeckeGenConst GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues in
theorem GlobalTheory.HeckeGenConst.generator_constant : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i))
      (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∀ a ∈ Rc, ∀ (C : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩)) z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
        ∀ (hx' : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1).dom) (t : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
          (∀ j, j ≠ none → t j = 1) → FrBor t ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2, hx'⟩) z →
          toC (t none : CAt σ) ^ (κ i).n *
              ((T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) *
                σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV)) =
            (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.muAt T R i P)⁻¹ ^ k *
              (T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) (h * a)) := by
  intro D hHk hSL hVF G _ _ Pl0 T0 A T _ R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV hpin P p k α Rc hS h hx
    a ha C z hz hx' t ht hb
  obtain ⟨ph, b, hph, hbON, hpin⟩ := hpin
  obtain ⟨γ', hγ', hfr'⟩ := exists_frAt hMod hTie i σ hσ hV (h * a)
  obtain ⟨_, Wt', ⟨Y'⟩⟩ := exists_witness T i σ hV hTie.laws.toLawsM (hσ ▸ T.toCore.good_σ₀) (h * a)
  obtain ⟨rV, e, he, ⟨Δ, hΔ⟩, hall⟩ :=
    GlobalTheory.HeckeVacuum.omega_vacuum_hecke D G Pl0 T0 A T R hLev hFam hThP i P p k α Rc hS a ha
  obtain ⟨-, -, hom⟩ := hall Δ hΔ
  obtain ⟨v, hv⟩ := exists_theta_perVec_ne_zero Y'
  obtain ⟨X, hX⟩ := exists_map_const hbON fun j => v (Fin.cast (rank_Wc i) j)
  have hz' : ∀ a : Fin (Vc D i).rank,
      perVec Wt' v = perVec Wt' fun m => ∑ n, X (Fin.cast (rank_Wc i).symm m) n * b n a := fun a => by
    congr 1
    funext m
    rw [hX]
    rfl
  have h2 := GlobalTheory.HeckeGeoRead.theta_trace_read D hHk hSL hVF G Pl0 T0 A T R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV
    P p k α Rc hS h hx a ha C z hz hx' t ht hb ph b hph hbON hpin γ' hγ' hfr' Wt' Y' e he Δ hΔ X (fun _ => perVec Wt' v) hz'
  have h1 := hpin (h * a) γ' hγ' hfr' hx' Wt' Y' X (fun _ => perVec Wt' v) hz'
  set_option synthInstance.maxHeartbeats 100000 in
    rw [thetaAt_eq, show ((1 : GA D (Vc D i)), γ' * (h * a)) = (1, γ' * h) * (1, a) by simp [mul_assoc], map_mul,
    Module.End.mul_apply, hom, map_smul, map_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul] at h1
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have h3 := cancel (fun h0 => by simp [h0] at hph) (pow_ne_zero k (Units.ne_zero _)) (fun _ => hv) h1 h2
  rw [(hTie.kap i τ).2.2, hkScal, one_mul, map_pow, map_inv₀, map_natCast, inv_pow (muAt T R i P)]
  rw [rV] at h3
  exact h3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOffPartVacuumCommutantActsByScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.CommVac

variable {D : D7}

theorem symplO_add_right (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  unfold symplO hO
  simp only [Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem hO_smul_left (S T : HSp D) (a : AE D) (x y : WO S T) : hO S T (a • x) y = a * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem hO_smul_right (S T : HSp D) (a : AE D) (x y : WO S T) : hO S T x (a • y) = cA D a * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem symplO_smul_comm (S T : HSp D) {a : AE D} (ha : cA D a = a) (x y : WO S T) :
    symplO S T (a • x) y = symplO S T x (a • y) := by
  unfold symplO
  rw [hO_smul_left, hO_smul_right, ha]


set_option maxHeartbeats 1000000 in
theorem heisO_offPart_vac : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ w ∈ Ann W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (depLat G (.chi i 0)), w.map (infPart D) = 0 →
    ∃ c : ℂ, heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) ((1 - e - cA D e) • w) (W.vac i) = c • W.vac i := by
  intro D _ T L μ0 hL sc G W M _ i hi e he w hw hinf
  classical
  obtain ⟨hsdS, hsdT⟩ := GlobalTheory.CosetRow.selfDual_chi hL G i hi
  obtain ⟨h1, -, h3⟩ := _root_.GlobalTheory.LatVac.latO_selfDual_approx_sign D W.ψ _ _ (G.latS (.chi i 0)) (G.latT (.chi i 0)) W.ψ_std hsdS hsdT
  have hlat := (W.vac_is i hi).2.lat
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hec : e * cA D e = 0 := he.2
  have hce : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have hff : (1 - e - cA D e) * (1 - e - cA D e) = 1 - e - cA D e := by
    linear_combination hee + hce + 2 * hec
  have hfc : cA D (1 - e - cA D e) = 1 - e - cA D e := by
    rw [map_sub, map_sub, map_one, Formalism.L2.Theta.cA_cA]; ring
  have hfint : finPart D (1 - e - cA D e) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hff])
  have hef : ∀ e', IsIdemSum e' G.pl.W0 → e' * (1 - e - cA D e) = 0 := fun e' he' => by
    rw [GlobalTheory.StepVecSum.idemSum_eq (G.V (.grid 0 0)) he he']
    linear_combination -hee - hec
  have hdep : ∀ u ∈ latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _)
      (fun _ => True), (1 - e - cA D e) • u ∈ depLat G (.chi i 0) := fun u hu =>
    ⟨GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfint u hu, fun e' he' => by
      rw [smul_smul, hef e' he', zero_smul]; exact AddSubgroup.zero_mem _⟩
  have key : ∀ u ∈ latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _)
      (fun _ => True), W.ψ (symplO _ _ w ((1 - e - cA D e) • u)) = 1 := by
    intro u hu
    obtain ⟨v, hvdef⟩ : ∃ v, v = (1 - e - cA D e) • u := ⟨_, rfl⟩
    rw [← hvdef]
    have hv : v ∈ latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _)
        (fun _ => True) := hvdef ▸ GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfint u hu
    have hpiece : ∀ c : AE D, finPart D c ∈ intAE D → c • v ∈ depLat G (.chi i 0) := fun c hc => by
      rw [hvdef, smul_smul, mul_comm, ← smul_smul]
      exact hdep _ (GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ c hc u hu)
    have hadd : ∀ a b : AE D, W.ψ (symplO _ _ w (a • v)) = 1 → W.ψ (symplO _ _ w (b • v)) = 1 →
        W.ψ (symplO _ _ w ((a + b) • v)) = 1 := fun a b ha hb => by
      rw [add_smul, symplO_add_right, AddChar.map_add_eq_mul, ha, hb, one_mul]
    have hsplit : ∀ e₁, IsSplitIdem D e₁ → W.ψ (symplO _ _ w (e₁ • v)) = 1 := fun e₁ h₁ =>
      hw.2 e₁ h₁ _ (hpiece _ (GlobalTheory.SplitHomLattice.idem_int h₁))
        (fun a b => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, h₁.1])
    have hQ := GlobalTheory.FinPl.FlatFix.finite_two (D := D) (fun _ => True)
    have hmemQ : ∀ x, x ∈ hQ.toFinset ↔ True ∧ (2 : 𝓞 D.host.F) ∈ x.asIdeal := fun x => hQ.mem_toFinset
    have hch : ∀ x, x ∈ hQ.toFinset → ∃ e₁ ε, IsSplitIdem D e₁ ∧ IsPlaceIdem D x ε ∧
        e₁ + cA D e₁ = algebraMap (AF D.host.F) (AE D) ε := by
      intro x hx
      rcases (_root_.GlobalTheory.FinPl.TamePlaces.tame D x).2 with h | h
      · exact absurd ((hmemQ x).1 hx).2 h
      · exact h
    choose! es εs hes hεs hsum using hch
    have hdec := GlobalTheory.FinPl.FlatFix.indicatorIdempotent_eq_add_sum (fun _ => True) hQ.toFinset hmemQ εs hεs
    have hvc : algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (fun _ => True)) • v = v := by
      ext a b
      rw [Matrix.smul_apply, smul_eq_mul]
      exact GlobalTheory.SelfDualAt.algebraMap_placeIdempotent_mul _ _ (GlobalTheory.FinPl.LatMem.latO_mxAt hv a b)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hvc, hdec, map_add (f := _), map_sum]
    refine hadd _ _ ?_ ?_
    · have hβ := GlobalTheory.FinPl.FlatFix.int_alg_pair (D := D) (GlobalTheory.FinPl.FlatFix.halfOff_int (D := D) fun _ => True)
      have e2 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.FinPl.FlatFix.halfOff (fun _ => True) +
          GlobalTheory.FinPl.FlatFix.halfOff (D := D) (fun _ => True))) • v =
          2 • (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.FinPl.FlatFix.halfOff (D := D) (fun _ => True))) • v) := by
        rw [GlobalTheory.FinPl.FlatFix.pair_add, map_add (f := _), add_smul, two_nsmul]
      rw [e2]
      exact hw.1 _ (hpiece _ hβ)
    · refine Finset.sum_induction _ (fun c => W.ψ (symplO _ _ w (c • v)) = 1) hadd ?_ ?_
      · have h0 := symplO_add_right (G.pS (.chi i 0)) (G.pT (.chi i 0)) w 0 0
        rw [add_zero] at h0
        have h0' : symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) w 0 = 0 := by linear_combination -h0
        show W.ψ (symplO _ _ w ((0 : AE D) • v)) = 1
        rw [zero_smul, h0', AddChar.map_zero_eq_one]
      · intro x hx
        rw [← hsum x hx]
        exact hadd _ _ (hsplit _ (hes x hx)) (hsplit _ (GlobalTheory.IdemSumVac.isSplitIdem_cA (hes x hx)))
  have hfin' : ((1 - e - cA D e) • w).map (infPart D) = 0 := by
    ext a b
    have := congrFun (congrFun hinf a) b
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.zero_apply] at this ⊢
    rw [this, mul_zero]
  have hmem : (1 - e - cA D e) • w ∈ latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _)
      (G.latT (.chi i 0) : Set _) (fun _ => True) :=
    (h1 _ hfin').2 fun u' hu' => by rw [symplO_smul_comm _ _ hfc]; exact key u' hu'
  obtain ⟨ε, -, hε⟩ := h3 _ hlat _ hmem
  exact ⟨ε, hε _ hlat⟩

end GlobalTheory.CommVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSBHalfHalfExtensionLatticeIndicatorFn
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.CosetRow.ExtSB

variable {D : D7} {m n : ℕ}

theorem half_of_idem' {b : AE D} (hb : b * b = b) (t : Mx D m n) : IsHalf b (b • t) := fun i j => by
  simp only [Matrix.smul_apply, smul_eq_mul]
  linear_combination (t i j) * hb

theorem half_add_nsmul_iff {e : AE D} {t u : Mx D m n} (hu : IsHalf e u) (k : ℕ) :
    IsHalf e (t + k • u) ↔ IsHalf e t := by
  constructor
  · intro h i j
    have h1 := h i j
    have h2 := hu i j
    simp only [Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul] at h1
    linear_combination h1 - (k : AE D) * h2
  · intro h i j
    have h1 := h i j
    have h2 := hu i j
    simp only [Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]
    linear_combination h1 + (k : AE D) * h2

theorem smul_add_nsmul (e : AE D) (t u : Mx D m n) (k : ℕ) : e • (t + k • u) = e • t + k • (e • u) := by
  rw [smul_add, smul_comm]

theorem isSBHalf_extFn : ∀ {D : D7} {m n : ℕ} {Λ : AddSubgroup (Mx D m n)} {e₀ e₁ : AE D} {Φ : Mx D m n → ℂ}, e₀ * e₀ = e₀ → e₁ * e₁ = e₁ → e₀ * e₁ = 0 → (∀ u ∈ Λ, e₀ • u ∈ Λ) → (∀ u ∈ Λ, e₁ • u ∈ Λ) → IsSBHalf e₀ Λ Φ → IsSBHalf (e₀ + e₁) Λ (GlobalTheory.CosetRow.extFn e₀ e₁ Λ Φ) := by
  intro D m n Λ e₀ e₁ Φ h0 h1 h01 hΛ0 hΛ1 hΦ
  obtain ⟨sΦ, k, hk, iΦ, fΦ⟩ := hΦ
  refine ⟨fun t ht => ?_, k, hk, fun u hu hue t => ?_, fun t ht => ?_⟩
  · unfold GlobalTheory.CosetRow.extFn at ht
    by_contra hc
    exact ht (if_neg hc)
  · have hhalf := half_add_nsmul_iff (t := t) hue k
    have hA : Φ (e₀ • (t + k • u)) = Φ (e₀ • t) := by
      rw [smul_add_nsmul]
      exact iΦ _ (hΛ0 u hu) (half_of_idem' h0 u) _
    have hB : halfInd e₁ Λ (e₁ • (t + k • u)) = halfInd e₁ Λ (e₁ • t) := by
      rw [smul_add_nsmul]
      unfold halfInd
      have hm : e₁ • t + k • (e₁ • u) ∈ Λ ↔ e₁ • t ∈ Λ :=
        Λ.add_mem_cancel_right (AddSubgroup.nsmul_mem Λ (hΛ1 u hu) k)
      have hh : IsHalf e₁ (e₁ • t + k • (e₁ • u)) ↔ IsHalf e₁ (e₁ • t) :=
        half_add_nsmul_iff (half_of_idem' h1 u) k
      by_cases hc : e₁ • t ∈ Λ ∧ IsHalf e₁ (e₁ • t)
      · rw [if_pos (And.intro (hm.2 hc.1) (hh.2 hc.2)), if_pos hc]
      · rw [if_neg (fun h => hc ⟨hm.1 h.1, hh.1 h.2⟩), if_neg hc]
    unfold GlobalTheory.CosetRow.extFn
    rw [hA, hB]
    by_cases hc : IsHalf (e₀ + e₁) t
    · rw [if_pos (hhalf.2 hc), if_pos hc]
    · rw [if_neg (mt hhalf.1 hc), if_neg hc]
  · unfold GlobalTheory.CosetRow.extFn at ht
    by_cases hc : IsHalf (e₀ + e₁) t
    · rw [if_pos hc] at ht
      have hΦt : Φ (e₀ • t) ≠ 0 := left_ne_zero_of_mul ht
      have hI : halfInd e₁ Λ (e₁ • t) ≠ 0 := right_ne_zero_of_mul ht
      have hI' : e₁ • t ∈ Λ := by
        unfold halfInd at hI
        by_contra hn
        exact hI (if_neg (fun h => hn h.1))
      have hkt : k • t = k • (e₀ • t) + k • (e₁ • t) := by
        ext i j
        have := hc i j
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul] at this ⊢
        linear_combination -(k : AE D) * this
      rw [hkt]
      exact Λ.add_mem (fΦ _ hΦt) (AddSubgroup.nsmul_mem Λ hI' k)
    · exact absurd (if_neg hc) ht

end GlobalTheory.CosetRow.ExtSB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetScalarLocalIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.SplitMoveKappa

theorem om_toPair_mul : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R) (p : Pair T) (s x : FinPt ch.G p.small) (s' y : FinPt ch.G p.big) (v : WO (ch.G.pS p) (ch.G.pT p) → ℂ),
    ch.W.om p (ch.G.toPair p ((s * x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((s' * y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) v =
      ch.W.om p (ch.G.toPair p (s : Formalism.L2.Theta.GA D (ch.G.V p.small)) (s' : Formalism.L2.Theta.GA D (ch.G.V p.big)))
        (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) v) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch p s x s' y v
  have e1 : ((s * x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) =
      (s : Formalism.L2.Theta.GA D (ch.G.V p.small)) * ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) := by
    rw [mul_assoc]; rfl
  have e2 : ((s' * y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big)) =
      (s' : Formalism.L2.Theta.GA D (ch.G.V p.big)) * ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big)) := by
    rw [mul_assoc]; rfl
  have e3 : ∀ (a b : Formalism.L2.Theta.GA D (ch.G.V p.small)) (c d : Formalism.L2.Theta.GA D (ch.G.V p.big)),
      ch.G.toPair p (a * b) (c * d) = ch.G.toPair p a c * ch.G.toPair p b d := by
    intro a b c d
    cases p <;> simp [GlobalTheory.ChiGrid.GridData.toPair, map_mul]
  rw [e1, e2, e3, map_mul]
  rfl

end GlobalTheory.SplitMoveKappa
end
end

