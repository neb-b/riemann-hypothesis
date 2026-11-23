module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualSplitLabelOperatorMulScalarOperator
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLift
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0076
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffApplyDPIvOfKvalGe
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0013
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0180

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LiftSplitHeckePolysEqTransferResidualPolys
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.Link

theorem dualPoly_map {K L : Type} [Field K] [Field L] (φ : K →+* L) (s : K) (p : K[X]) :
    (dualPoly s p).map φ = dualPoly (φ s) (p.map φ) := by
  have h : (p.map φ).reverse = p.reverse.map φ := by
    rw [Polynomial.reverse, Polynomial.reverse, natDegree_map, reflect_map]
  rw [dualPoly, dualPoly, h, Polynomial.map_mul, map_C, Polynomial.map_comp, Polynomial.map_mul, map_C, map_X,
    leadingCoeff_map, map_inv₀]

theorem heckePolyOf_congr {L : Type} [Field L] (n q : ℕ) {a b : ℕ → L} (h : ∀ k, k ≤ n → a k = b k) :
    Formalism.L2.Col.heckePolyOf n q a = Formalism.L2.Col.heckePolyOf n q b := by
  unfold Formalism.L2.Col.heckePolyOf
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]

theorem blockPoly_ne_zero {L : Type} [Field L] (ν : L) (q t : ℕ) : Formalism.L2.Col.blockPoly ν q t ≠ 0 := by
  unfold Formalism.L2.Col.blockPoly
  refine Finset.prod_ne_zero_iff.2 fun c _ h => ?_
  have := congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f 0) h
  simp at this

variable {D : D7}

def rt (V : HSp D) : GA D V →* Module.End ℂ (GA D V → ℂ) where
  toFun g := { toFun := fun F h => F (h * g), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  map_one' := by ext F h; simp
  map_mul' g g' := by ext F h; simp [mul_assoc]

theorem opOf_rt (V : HSp D) (P : Pl D.host.E) (c : List ℤ →₀ ℂ) : opOf (rt V) P c = hk V P c := by
  unfold opOf hk
  refine Finsupp.sum_congr fun d _ => ?_
  congr 1
  ext F h
  simp [heckeLin, rt, LinearMap.sum_apply, Finset.sum_apply]

theorem isLab_split (V : HSp D) (P : Pl D.host.E) (hP : conjPl P ≠ P) (j : ℕ) (hj : j ≤ V.rank) :
    IsLab V P (splitLab V.rank j) := by
  refine (_root_.GlobalTheory.LabChar.labels_char V P _).2 ⟨?_, ?_, fun h => absurd h hP⟩
  · simp [splitLab]; omega
  · simp [splitLab, List.pairwise_append, List.pairwise_replicate]

theorem evC_single (V : HSp D) (P : Pl D.host.E) (a : List ℤ → ℂ) (d : List ℤ) (hd : IsLab V P d) :
    evC V P a (Finsupp.single d 1) = a d := by
  unfold evC
  rw [Finsupp.sum_single_index (by simp), ite_eq_left hd, one_mul]

theorem evC_splitC (V : HSp D) (P : Pl D.host.E) (hP : conjPl P ≠ P) (a : List ℤ → ℂ) (z : ℕ → ℂ) :
    evC V P a (splitC V.rank z) = ∑ j ∈ Finset.range (V.rank + 1), z j * a (splitLab V.rank j) := by
  unfold evC splitC
  rw [← Finsupp.sum_finsetSum_index (by simp) (by intro d x y; split_ifs <;> simp [add_mul])]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finsupp.sum_single_index (by simp), ite_eq_left (isLab_split V P hP j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))]

theorem eig_rel (V : HSp D) (P : Pl D.host.E) (hP : conjPl P ≠ P) (u : GA D V → ℂ) (hu : u ≠ 0)
    (hfix : ∀ k ∈ hyp V P, ∀ h, u (h * k) = u h) (c : List ℤ → ℂ)
    (hc : ∀ d, IsLab V P d → hk V P (Finsupp.single d 1) u = c d • u) :
    c (splitLab V.rank 0) = 1 ∧
      ∀ j, j ≤ V.rank → c (dualLab (splitLab V.rank j)) * c (splitLab V.rank V.rank) = c (splitLab V.rank (V.rank - j)) := by
  have hfix' : ∀ k ∈ hyp V P, rt V k u = u := fun k hk => funext (hfix k hk)
  obtain ⟨-, -, ⟨h0, h1⟩, hd, -⟩ := _root_.GlobalTheory.SphLabelOps.label_operators V P
  refine ⟨?_, fun j hj => ?_⟩
  · have e : splitLab V.rank 0 = List.replicate V.rank 0 := by simp [splitLab]
    have := h1 _ (rt V) u hfix'
    rw [opOf_rt, hc _ h0] at this
    rw [e]
    exact smul_left_injective ℂ hu (this.trans (one_smul ℂ u).symm)
  · have := _root_.GlobalTheory.DualSplitRel.dual_rel V P hP j hj _ (rt V) u hfix'
    rw [opOf_rt, opOf_rt, opOf_rt, hc _ (isLab_split V P hP _ le_rfl), map_smul,
      hc _ ((hd _).1.1 (isLab_split V P hP j hj)), hc _ (isLab_split V P hP _ (Nat.sub_le _ _)), smul_smul, mul_comm] at this
    exact smul_left_injective ℂ hu this

theorem mult_lev {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (U : MMap M) (hU : U ∈ Mult θ M J χ) :
    ∀ v, ∀ k ∈ J, ∀ g, U v (g * k) = χ k * U v g := by
  intro v k hk g
  induction hU using Submodule.span_induction with
  | mem x hx => exact hx.lev v k hk g
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy, mul_add]
  | smul a x _ hx => simp [hx, mul_left_comm]


set_option maxHeartbeats 400000 in
theorem hasRes_lift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Chain.LiftInteg D → Core R F → SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ SF, IsSF R SF → ∀ i c (p : Pl0 → D.what₂.LL[X]) (sX : A.ok A.μ0 × ℕ → D.what₂.LL) (sV : A.ok A.μ0 × ℕ → D.what₂.LL), (A.fam.R A.μ0).HasRes p sX → ∀ hX hV, IsOpsX R A.μ0 hX → IsOpsV R i A.μ0 hV → ∀ w ∈ EEc R SF c, LinearMap.adjoint (R.Th A.μ0) w ≠ 0 → (∀ (P : A.ok A.μ0) k, k ≤ D.sp.X'.rank → hX (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1) (LinearMap.adjoint (R.Th A.μ0) w) = D.what₂.embLL (sX (P, k)) • LinearMap.adjoint (R.Th A.μ0) w) → ∀ y, R.thG i A.μ0 y ∈ Wcc R SF i c → R.thG i A.μ0 y ≠ 0 → (∀ (P : A.ok A.μ0) k, k ≤ (Vc D i).rank → hV (R.pl P) (Finsupp.single (splitLab (Vc D i).rank k) 1) y = D.what₂.embLL (sV (P, k)) • y) → (A.fam.L i A.μ0).HasRes (A.fam.tr i p) sV := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hI hC hS hX0 SF hSF i c p sX sV hp hX hV hXo hVo w hw hw0 heX y hy hy0 heV P
  change A.ok A.μ0 at P
  obtain ⟨hG, hcj, hq⟩ := (_root_.GlobalTheory.GoodPrimes.good_primes R F hC.lev).2.2.2 hC.fam A.μ0 P.1 P.2
  have hq0 : (A.q P : ℂ) ≠ 0 := by
    rw [hq, Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact (R.pl P).ne_bot
  obtain ⟨_, _, _, htie⟩ := hC.fam.tie
  obtain ⟨-, hr, ht⟩ := htie.ranks
  have hrX : D.sp.X'.rank = A.r + D.R.m * A.t := by rw [D.sp.X'_rank, hr, ht]; rfl
  have hrV : (Vc D i).rank = A.r + A.t := by rw [D.sp.V_rank _ (Nat.le_add_left _ _) i.2, hr, ht]; rfl
  have hrW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hrY : (Yc D 0).rank = D.R.r := by
    rw [D.sp.Y_rank _ (min_le_right _ _), Nat.zero_min]; simp [Ranks.rankY]
  have hr0 : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r; omega

  obtain ⟨zE, hmE, hpE⟩ := _root_.GlobalTheory.Hk3.SplitChain.exists_transfer R F hI hC hS A.μ0 P
  have hE : (p P).map D.what₂.embLL =
      (Formalism.L2.Col.heckePolyOf D.R.r (A.q P) fun j => c (R.pl P) (dualLab (splitLab D.R.r j))).comp
        (C ((A.q P : ℂ) ^ (D.R.m / 2 * D.R.t)) * X) := by
    have h1 := hpE fun j => c (R.pl P) (dualLab (splitLab (Yc D 0).rank j))
    have h2 : (Formalism.L2.Col.heckePolyOf (A.r + D.R.m * A.t) (A.q P) fun k => sX (P, k)) =
        p P * (A.fam.R A.μ0).blockProd P := hp P
    have h3 := congrArg (Polynomial.map D.what₂.embLL) h2
    rw [Formalism.L2.Col.map_heckePolyOf, Polynomial.map_mul, ← hrX] at h3
    rw [heckePolyOf_congr _ _ (b := fun k => D.what₂.embLL (sX (P, k))) ?_, h3, hrY] at h1
    · refine mul_right_cancel₀ ?_ h1
      rw [Ne, Polynomial.map_eq_zero]
      unfold BlockDat.blockProd
      refine List.prod_ne_zero fun h => ?_
      obtain ⟨ν, -, hν⟩ := List.mem_map.1 h
      exact blockPoly_ne_zero _ _ _ hν
    · intro k hk
      have h4 := (_root_.GlobalTheory.Hk3.SysE.matched_commute R F hC hS SF hSF A.μ0 (R.pl P) hG _ _ (hmE k hk) hX hXo).2 c w hw
      have h5 := smul_left_injective ℂ hw0 ((heX P k hk).symm.trans h4)
      exact ((h5.trans (evC_splitC (Yc D 0) (R.pl P) hcj _ _))).symm

  obtain ⟨zW, hmW, hpW⟩ := GlobalTheory.T.thetaLift_transfer_heckePoly_splitPrime R F hC hS i A.μ0 P
  obtain ⟨h, hWo, -, -, -, -, hev, -⟩ := _root_.GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt R F hC hS hX0 SF hSF i
  have hW : (Formalism.L2.Col.heckePolyOf (A.r + A.t) (A.q P) fun k => sV (P, k)).map D.what₂.embLL =
      (Formalism.L2.Col.heckePolyOf D.R.r (A.q P) fun j => c (R.pl P) (splitLab D.R.r j)).comp
        (C (D.what₂.embLL (A.etaVal P : D.what₂.LL) * (A.q P : ℂ) ^ ((D.R.t + 1) / 2)) * X) *
        ((A.fam.L i A.μ0).blockProd P).map D.what₂.embLL := by
    have h1 := hpW fun j => c (R.pl P) (splitLab (Wc D i).rank j)
    rw [heckePolyOf_congr _ _ (b := fun k => D.what₂.embLL (sV (P, k))) ?_, hrW] at h1
    · rw [Formalism.L2.Col.map_heckePolyOf, ← hrV, h1]
    · intro k hk
      have h4 := (_root_.GlobalTheory.SysW.matched_operators_theta_intertwine R F hC hS hX0 SF hSF i A.μ0 (R.pl P) hG _ _ (hmW k hk) hV hVo).1 h hWo y
      have h5 := ((congrArg (R.thG i A.μ0) (heV P k hk)).trans (map_smul _ _ _)).symm.trans (h4.trans (hev c _ hG _ _ hy))
      exact ((smul_left_injective ℂ hy0 h5).trans (evC_splitC (Wc D i) (R.pl P) hcj _ _)).symm

  have hne : (R.HW i (sg0 D A)).e (R.thG i A.μ0 y) ≠ 0 := fun h0 =>
    hy0 ((hC.models.HW i (sg0 D A)).1 (h0.trans (map_zero _).symm))
  obtain ⟨v, hv⟩ : ∃ v, (R.HW i (sg0 D A)).e (R.thG i A.μ0 y) v ≠ 0 := by
    by_contra hcon
    exact hne (MultilinearMap.ext fun v => not_not.1 fun hv => hcon ⟨v, hv⟩)
  obtain ⟨cc, hβ⟩ := hC.lev.βW i
  have hlev := (_root_.GlobalTheory.LevOp.level_operators (Wc D i) (R.βW i) (R.ΛW i) _ (R.datWp i R.triv) hβ (R.pl P)
    (by rw [one_pow, Nat.cast_one]; exact fun h1 => (R.pl P).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1))
    (fun PP hPP => hG PP (Or.inl (hPP.resolve_right (Finset.notMem_empty _))))).1
  have hm := (Submodule.mem_inf.1 (Submodule.mem_inf.1 (Submodule.mem_comap.1 hy)).2).1
  have hrel := eig_rel (Wc D i) (R.pl P) hcj _ hv (fun k hk g =>
      (mult_lev R.θ _ _ _ _ hm v k (hlev k hk).1 g).trans ((congrArg (fun z : ℂ => z * (R.HW i (sg0 D A)).e (R.thG i A.μ0 y) v g) (hlev k hk).2).trans (one_mul _))) (c (R.pl P)) (fun d hd => by
      have h5 := (hWo (R.pl P) hG (Finsupp.single d 1) (R.thG i A.μ0 y)).symm.trans
        ((congrArg (R.HW i (sg0 D A)).e (hev c _ hG (Finsupp.single d 1) _ hy)).trans (map_smul _ _ _))
      exact congrArg (fun U : MMap (R.MW i (sg0 D A)) => U v) (h5.trans
        (congrArg (fun z : ℂ => z • (R.HW i (sg0 D A)).e (R.thG i A.μ0 y)) (evC_single (Wc D i) (R.pl P) (c (R.pl P)) d hd))))
  rw [hrW] at hrel
  have hdual := _root_.GlobalTheory.Hk3.DualHecke.dualPoly_heckePolyOf_comp ℂ D.R.r (A.q P) (fun j => c (R.pl P) (splitLab D.R.r j))
    (fun j => c (R.pl P) (dualLab (splitLab D.R.r j))) ((A.q P : ℂ) ^ (D.R.m / 2 * D.R.t))
    (D.what₂.embLL (A.etaVal P : D.what₂.LL) * (A.q P : ℂ) ^ ((D.R.t + 1) / 2)) hq0 (pow_ne_zero _ hq0) hr0 hrel.1 hrel.2
  have hsc : D.what₂.embLL (trScale A.r D.R.m A.t A.q A.etaVal P) = (A.q P : ℂ) ^ (D.R.m / 2 * D.R.t) *
      (D.what₂.embLL (A.etaVal P : D.what₂.LL) * (A.q P : ℂ) ^ ((D.R.t + 1) / 2)) * (A.q P : ℂ) ^ (D.R.r - 1) := by
    have he : (2 * A.r + (D.R.m + 1) * A.t - 1) / 2 = D.R.m / 2 * D.R.t + (D.R.t + 1) / 2 + (D.R.r - 1) := by
      obtain ⟨a, ha⟩ := D.R.m_even
      obtain ⟨b, hb⟩ := D.R.t_odd
      rw [hr, ht, ha, show (a + a) / 2 = a by omega, show (a + a + 1) * D.R.t = 2 * (a * D.R.t) + D.R.t by ring]
      omega
    rw [trScale, map_mul, map_pow, map_natCast, he, pow_add, pow_add]
    ring
  apply Polynomial.map_injective D.what₂.embLL D.what₂.embLL.injective
  change (Formalism.L2.Col.heckePolyOf (A.r + A.t) (A.q P) fun k => sV (P, k)).map D.what₂.embLL =
    (dualPoly (trScale A.r D.R.m A.t A.q A.etaVal P) (p P) * (A.fam.L i A.μ0).blockProd P).map D.what₂.embLL
  rw [hW, Polynomial.map_mul, dualPoly_map, hsc, hE, hdual]

end GlobalTheory.Hk3.Link

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalModelBoundPlaceOverSecondEmbedding
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

noncomputable section

namespace GlobalTheory.TwU.LowF

theorem kval_orbit (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC) (E : OrbitPlaces.Ent D)
    (hA : OrbitPlaces.OrbitLetterBoundsAll 11 1) (hS : OrbitPlaces.Shape D L X E) (hC : OrbitPlaces.CLarge 11 1 K ce)
    (p : ℕ) [Fact p.Prime] (h : OrbitPlaces.OrbOK D p) (h0 : IsResidueClassZero D p) (hne : hP D p ≠ 0)
    (hX : (p : ℝ) ≤ L.sc.X'' D.R.n) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (t : HH D)
    [NeZero (nP D p)] (B : OmBasis p (nP D p)) (be : MvPowerSeries (Fin 2) (K0 p)) (hbe : BeProp p be)
    (U : MvPowerSeries (Eidx (nP D p) (D.R.N i) (D.R.N (i + 1)) ⊕ Eidx (nP D p) (D.R.N i) (D.R.N (i + 1))) (K0 p))
    (hU : IntS p (inParam p U)) :
    product_zeroth_first_parts.KvalGe (D.R.N i) (D.R.N (i + 1)) p (fun s : ZMod (nP D p) => E.nu u i (OrbitPlaces.orbMap D p (true, t) s))
      (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters (thOne B be U)))
      (FOrb D (i + 1) p (true, t) - OrbitPlaces.errF L K ce (i + 1) p (true, t)) := by
  obtain ⟨bv, h1, h2, h3, h4, hb⟩ := GlobalTheory.T.exists_letterCoordinates_series_onePlace_alt p h.five (nP D p) h.even B be hbe
  obtain ⟨U', hU', e⟩ := hb _ _ U hU
  exact _root_.GlobalTheory.TwU.orbitBound_overSecondEmbedding_anyBasePoint_alt D L X K ce E 11 1 hA hS hC p h h0 hne hX u i hi t 1 (-1) bv (by simp) (Or.inr rfl) h1 h2 h3 h4 _
    ⟨U', hU', e⟩

theorem kval_general (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC) (E : OrbitPlaces.Ent D)
    (hA : OrbitPlaces.OrbitLetterBoundsAll 11 1) (hS : OrbitPlaces.Shape D L X E) (hC : OrbitPlaces.CLarge 11 1 K ce)
    (p : ℕ) [Fact p.Prime] (h : OrbitPlaces.OrbOK D p) (h0 : IsResidueClassZero D p) (hne : hP D p ≠ 0)
    (hX : (p : ℝ) ≤ L.sc.X'' D.R.n) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (t : HH D)
    (n r0 r1 : ℕ) [NeZero n] (hn : n = nP D p) (h0' : r0 = D.R.N i) (h1' : r1 = D.R.N (i + 1))
    (B : OmBasis p n) (be : MvPowerSeries (Fin 2) (K0 p)) (hbe : BeProp p be)
    (U : MvPowerSeries (Eidx n r0 r1 ⊕ Eidx n r0 r1) (K0 p)) (hU : IntS p (inParam p U)) :
    product_zeroth_first_parts.KvalGe r0 r1 p (fun s : ZMod n => E.nu u i (posPl D p (true, t) s.val))
      (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters (thOne B be U)))
      (FOrb D (i + 1) p (true, t) - OrbitPlaces.errF L K ce (i + 1) p (true, t)) := by
  subst hn h0' h1'
  exact kval_orbit D L X K ce E hA hS hC p h h0 hne hX u i hi t B be hbe U hU

theorem lowBound_of_series_bound_one_place {p : ℕ} [Fact p.Prime] (X : Sys p) (be : MvPowerSeries (Fin 2) (K0 p)) (j : ℕ) (v : X.Pl)
    [NeZero (X.G.P.n' v)] (nu : ZMod (X.G.P.n' v) → YoungDiagram) (g : ℝ)
    (hcc : MvPowerSeries.constantCoeff be = 0)
    (hnu : ∀ s r, (((nu s).rowLen r : ℕ) : ℤ) = X.nuv v (j + 1) (toFin s) (r + 1))
    (hK : ∀ U : MvPowerSeries (Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) ⊕
        Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))) (K0 p), IntS p (inParam p U) →
      product_zeroth_first_parts.KvalGe (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) p nu
        (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters (thOne (X.om v) be U))) g) :
    IsPlaceCofactorValuationLowerBound X be j v g := by
  intro U hU I n
  obtain ⟨hU1, e⟩ := restr_onePlace p X be j v U hcc hU
  refine GlobalTheory.KvalAgree.coeff_applyD_PIv_of_KvalGe p X j v nu hnu _ g ?_ I n
  rw [e]
  exact hK _ hU1

theorem lowAt_F : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D) (K : Consts) (ce : ErrC) (E : OrbitPlaces.Ent D), LatTied hT X Y → FillsAll hT Y → OrbitPlaces.OrbitLetterBoundsAll 11 1 → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge 11 1 K ce → ((D.what₂.places.resChar w) : ℝ) ≤ L.sc.X'' D.R.n → ∀ (Lv : Levels (Y.Fl u w hg)) (Ch : Chain Lv) (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _) (Y5 : FormalGroupSystem.Pend (FormalGroupSystem.Sys.mk (D.gat u w hg) (Y.Fl u w hg) Lv Ch std vp unif eO eO_spec dG dG_spec om)), BeProp (D.what₂.places.resChar w) Y5.be → ∀ (v : Fin (D.gat u w hg).P.nV) (t : HH D), (D.gat u w hg).P.n' v = nP D (D.what₂.places.resChar w) → (∀ s : Fin ((D.gat u w hg).P.n' v), hT.gat_pos u w hg ⟨v, s⟩ = tauPl D (posPl D (D.what₂.places.resChar w) (true, t) s.val)) → ∀ i < D.R.m, Y5.LowAt i v (FOrb D (i + 1) (D.what₂.places.resChar w) (true, t) - OrbitPlaces.errF L K ce (i + 1) (D.what₂.places.resChar w) (true, t)) := by
  intro D u w hg L hT X Y K ce E hTied hFill hA hS hC hX Lv Ch std vp unif eO eO_spec dG dG_spec om Y5 hBe v t hn hpos i hi
  have h0 : IsResidueClassZero D (D.what₂.places.resChar w) := hg.2.2.1
  have hne := (_root_.GlobalTheory.TwU.Served.served_facts D _ hg.1 h0 hg.2.2.2.1).1
  have hstd := std v
  have hOK : OrbitPlaces.OrbOK D (D.what₂.places.resChar w) := ⟨hg.2.1, hn ▸ hstd.even, hn ▸ hstd.two_le⟩
  have hcc : MvPowerSeries.constantCoeff Y5.be = 0 := by
    by_contra hc
    have := (hBe.ab 0 (by simpa using hc)).1
    simp at this
  haveI : NeZero ((D.gat u w hg).P.n' v) := ⟨by have := hstd.two_le; omega⟩
  have ht : (Y.Fl u w hg).t = D.R.t := (hTied u w hg).2.1
  have hk := hT.gat_k u w hg
  have hN : ∀ j, NN (D.gat u w hg).P.m (Y.Fl u w hg).t j = D.R.N j := fun j => by
    simp only [NN, Ranks.N, ht]
    omega
  refine _root_.GlobalTheory.TwU.LowGen.cofactor_lower_bound_of_place_bound_witt _ _ Y5 i v _ hcc ?_
  refine lowBound_of_series_bound_one_place (Sys.mk (D.gat u w hg) (Y.Fl u w hg) Lv Ch std vp unif eO eO_spec dG dG_spec om) Y5.be i v (fun s => E.nu u i (posPl D (D.what₂.places.resChar w) (true, t) s.val)) _ hcc ?_ ?_
  · intro s r
    have h1 := _root_.GlobalTheory.fock_rows_of_fills D u w hg hT Y hFill ht v (toFin s) i hi r
    have h2 := E.nu_row u i hi (posPl D (D.what₂.places.resChar w) (true, t) s.val) r
    have h3 := hpos (toFin s)
    rw [h3] at h1
    have h4 : (((E.nu u i (posPl D (D.what₂.places.resChar w) (true, t) s.val)).rowLen r : ℕ) : ℝ) =
        ((FormalGroupSystem.nu (Y.Fl u w hg).t ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) (i + 1) (toFin s) (r + 1) : ℤ) : ℝ) := by
      rw [h2, h1]; rfl
    exact_mod_cast h4
  · intro U' hU1
    exact kval_general D L X K ce E hA hS hC _ hOK h0 hne hX u i hi t _ _ _ hn
      (hN i) (hN (i + 1)) _ _ hBe _ hU1

end GlobalTheory.TwU.LowF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardBasesHyperbolicPairOrthonormal
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)


open GlobalTheory.KerStd.HypCoord in
theorem GlobalTheory.KerStd.hyp_of_stdBases : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → OrbitPlaces.OrbOK D p → ((IsResidueClassZero D p ∧ hP D p ≠ 0) ∨ IsSg D p) → ∀ (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p), OwOK (nP D p) σ om oms → TrDual (nP D p) σ om oms → ∀ (R : Finset (OrbitPlaces.Pl D)), OrbitPlaces.IsReps D p R → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b → TaylorLogMetric.Orthonormal D b → ∃ f f' : (R × Fin (nP D p / 2)) × Fin N × Fin N' → Fin r → MaximalUnramifiedExtension p, HypPair σ f f' ∧ ∀ (c : ℂ_[p]) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) (stdSer D lam (fun _ => 1) P P' G) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst (hypZ D p σ om oms R f f') (thOrth D lam c b G) := by
  intro D p _ lam σ hσ hO hcl om oms hOw hTr R hR N N' L L' P P' hA hP hP' r b hb ho
  have hcl' : IsResidueClassZero D p ∨ IsSg D p := hcl.elim (fun h => Or.inl h.1) Or.inr
  have hONB : Formalism.L2.KerInert.RepFrame.LamONB D lam b :=
    Formalism.L2.KerInert.RepFrame.lamONB_of_cols D lam b
      (Formalism.L2.KerInert.RepFrame.rank_of_locBasis L L' hA.2.2.1 hA.2.2.2 b hb)
      (Formalism.L2.KerInert.RepFrame.cols_of_trace D (Formalism.L2.KerInert.RepFrame.trace_tau_sum D) lam b ho)
  obtain ⟨hg, hh⟩ := _root_.GlobalTheory.KerStd.HypCoord.FrobMove.frob_moves_coords D p lam σ hσ hcl' N N' L L' P P' hP hP' r b
  have hpair := _root_.GlobalTheory.KerStd.HypCoord.hK_gK_dual D p lam σ hσ hcl' N N' L L' P P' hP hP' r b hONB
  have hiso := norm_sigma_eq p σ hσ
  have hhint := _root_.GlobalTheory.KerStd.HypCoord.norm_hK_le_one D p lam σ hσ hcl' N N' L L' P P' hP hP' r b hb
  have hgint : ∀ z a b₀ i, ‖gK D lam P P' b z a b₀ i‖ ≤ 1 := fun z a b₀ i => by
    rw [← hiso, hg]; exact hhint _ _ _ _
  have hg2 : ∀ z a b₀ i, σ (σ (gK D lam P P' b z a b₀ i)) = gK D lam P P' b (posPl D p z 2) a b₀ i :=
    fun z a b₀ i => by rw [hg, hh, posPl_add]
  obtain ⟨hf1, hf2⟩ := _root_.GlobalTheory.KerStd.HypCoord.fOf_integral_sigma_sq D p σ om oms R N N' r (gK D lam P P' b) hO
    (fun x hx => by rw [hiso]; exact hx) hOw hgint hg2
  obtain ⟨hi1, hi2⟩ := _root_.GlobalTheory.KerStd.HypCoord.fOf_isotropic D p σ om oms R N N' r (gK D lam P P' b) (hK D lam P P' b) hO hR hg hpair
  have hd := _root_.GlobalTheory.KerStd.HypCoord.fOf_fOf'_dual D p σ om oms R N N' r (gK D lam P P' b) (hK D lam P P' b) hO hR hTr hg hpair
  refine ⟨fOf D p σ om R (gK D lam P P' b), fOf' D p σ oms R (gK D lam P P' b), ⟨hf1, hf2, hi1, hi2, hd⟩, ?_⟩
  have hlin := _root_.GlobalTheory.KerStd.HypCoord.linForm_hypZ D p σ om oms R N N' r _ (gK D lam P P' b) (Formalism.L2.KerInert.RepFrame.lamB D lam b)
    (fun k j => chgB D lam P P' k ((0 : ZMod 1), (tauPl D j.1, j.2))) hO hR (_root_.GlobalTheory.KerStd.HypCoord.trDual_expand D p σ om oms hTr)
    (fun q z a b₀ => _root_.GlobalTheory.KerStd.HypCoord.lamB_sum_gK D p lam σ hσ hcl' N N' L L' P P' hP hP' r b hONB q z a b₀)
  refine _root_.GlobalTheory.KerStd.HypCoord.stdSer_scaled_eq_thOrth D p lam N N' r P P' b _ (fun i => ?_) hlin
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hypZ, linEv, linOd, map_sum, map_add (f := _), map_mul, MvPowerSeries.constantCoeff_C, MvPowerSeries.constantCoeff_X,
    mul_zero, apply_ite MvPowerSeries.constantCoeff, map_zero, ite_self, Finset.sum_const_zero, add_zero]
end
end

