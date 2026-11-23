module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0037
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0060
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0022
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0059
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0039

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DivisibleGroupTowerCompatibilityStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi
open Coalgebra Bialgebra PositivityTheory.HtPt.Twpdiv in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisible_group_tower_compatibility :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
      (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C]
      (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O)
      (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La]
      (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L)
      (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate)
      (hre : X.Realises G e τ),
      (∀ (φ : La →+ La) (dφ : L →ₗ[O] L), X.Acts φ dφ → ∃ f : G ⟶ G,
        (∀ a, tateMap G G O f (τ a) = τ (φ a)) ∧ ∀ n (g : G.A n) (a : La),
          (e n (f.app n g)).1 (lev p n a) = (e n g).1 (lev p n (φ a))) ∧
      ∀ (H : PDivGroup p O) (f f' : G ⟶ H),
        (∀ a, tateMap G H O f (τ a) = tateMap G H O f' (τ a)) → f = f' := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO La _ _ _ L _ _ X G e τ hre
  let ev (n : ℕ) (t : LevGrp La p n) : G.A n →ₐ[O] O := (evalAt (X.A n) t).comp (e n).toAlgHom
  have ev_apply (n : ℕ) (t : LevGrp La p n) (g : G.A n) : ev n t g = (e n g).1 t := rfl
  have ev_sep (n : ℕ) : PositivityTheory.HtPt.Twpdiv.Sep (ev n) :=
    fun _ _ h => (e n).injective (Subtype.ext (funext h))
  have ev_lev (n : ℕ) (a : La) : ev n (lev p n a) = (τ a).pt n :=
    AlgHom.ext fun g => (hre.pt a n g).symm
  have tate_pt {H : PDivGroup p O} (f : G ⟶ H) (a : La) (n : ℕ) (g : H.A n) :
      (tateMap G H O f (τ a)).pt n g = (τ a).pt n (f.app n g) := rfl
  constructor
  · intro φ dφ h
    let levMap (n : ℕ) : LevGrp La p n →* LevGrp La p n :=
      AddMonoidHom.toMultiplicative (Submodule.mapQ _ _ φ.toIntLinearMap (by
        rintro _ ⟨b, rfl⟩
        exact ⟨φ b, (map_nsmul φ _ b).symm⟩)).toAddMonoidHom
    have levMap_lev (n : ℕ) (a : La) : levMap n (lev p n a) = lev p n (φ a) := rfl
    have liftable (n : ℕ) (g : G.A n) : ∃ u : G.A n, ∀ t, ev n t u = ev n (levMap n t) g := by
      let pulled (t : LevGrp La p n) : O := (e n g).1 (levMap n t)
      have hpulled : pulled ∈ X.A n :=
        (h n (e n g).1 pulled fun a => congrArg (e n g).1 (levMap_lev n a)).1 (e n g).2
      let u : X.A n := ⟨pulled, hpulled⟩
      refine ⟨(e n).symm u, fun t => ?_⟩
      rw [ev_apply, AlgEquiv.apply_symm_apply, ev_apply]
    let pull (n : ℕ) : G.A n →ₐ[O] G.A n :=
      Ord.liftTo (ev n) (ev_sep n) (fun t => ev n (levMap n t)) (liftable n)
    have ev_pull (n : ℕ) (t : LevGrp La p n) : (ev n t).comp (pull n) = ev n (levMap n t) :=
      Ord.ev_liftTo _ _ _ _ t
    have pull_apply (n : ℕ) (t : LevGrp La p n) (g : G.A n) :
        ev n t (pull n g) = ev n (levMap n t) g := DFunLike.congr_fun (ev_pull n t) g
    have pull_lev (n : ℕ) (a : La) (g : G.A n) :
        ev n (lev p n a) (pull n g) = ev n (lev p n (φ a)) g := by
      rw [pull_apply, levMap_lev]
    have ev_one (n : ℕ) (g : G.A n) : ev n 1 g = counit (R := O) g := by
      rw [← lev_zero p n, ev_lev, map_zero]
      rfl
    have ev_mul (n : ℕ) (s t : LevGrp La p n) (g : G.A n) :
        pair (ev n s) (ev n t) (comul (R := O) g) = ev n (s * t) g := by
      obtain ⟨a, rfl⟩ := lev_surjective p n s
      obtain ⟨b, rfl⟩ := lev_surjective p n t
      rw [← lev_add, ev_lev, ev_lev, ev_lev, map_add]
      exact (AlgHom.convMul_apply ((τ a).conv n) ((τ b).conv n) g).symm
    let app (n : ℕ) : G.A n →ₐc[O] G.A n :=
      BialgHom.ofAlgHom (pull n)
        (AlgHom.ext fun g => by
          change counit (R := O) (pull n g) = counit (R := O) g
          rw [← ev_one, ← ev_one, pull_apply, map_one])
        (AlgHom.ext fun g => (ev_sep n).pair (ev_sep n) _ _ fun z => by
          change pair (ev n z.1) (ev n z.2) (Algebra.TensorProduct.map _ _ (comul (R := O) g)) =
            pair (ev n z.1) (ev n z.2) (comul (R := O) (pull n g))
          rw [pair_map, ev_pull, ev_pull, ev_mul, ev_mul, pull_apply, map_mul])
    let f : G ⟶ G :=
      { app := app
        comm n := BialgHom.ext fun g => ev_sep n _ _ fun t => by
          obtain ⟨a, rfl⟩ := lev_surjective p n t
          calc
            ev n (lev p n a) (G.res n (pull (n + 1) g)) =
                ev (n + 1) (lev p (n + 1) (p • a)) (pull (n + 1) g) := hre.res n _ a
            _ = ev (n + 1) (lev p (n + 1) (φ (p • a))) g := pull_lev (n + 1) (p • a) g
            _ = ev (n + 1) (lev p (n + 1) (p • φ a)) g := by rw [map_nsmul]
            _ = ev n (lev p n (φ a)) (G.res n g) := (hre.res n g (φ a)).symm
            _ = ev n (lev p n a) (pull n (G.res n g)) := (pull_lev n a (G.res n g)).symm }
    refine ⟨f, fun a => TateOver.ext (funext fun n => AlgHom.ext fun g => ?_), fun n g a => pull_lev n a g⟩
    rw [tate_pt, ← ev_lev, ← ev_lev]
    exact pull_lev n a g
  · intro H f f' hf
    refine GlobalTheory.PDivGroup.Hom.ext (funext fun n => BialgHom.ext fun g => ev_sep n _ _ fun t => ?_)
    obtain ⟨a, rfl⟩ := lev_surjective p n t
    rw [ev_lev, ← tate_pt, ← tate_pt, hf]
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderRetractElementary
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.hopf_order_retract_elementary : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (ι : N' →+ N) (π : N →+ N'), (∀ y, π (ι y) = y) → (∀ g ∈ AA.carrier, (fun x => g (ι (π x))) ∈ AA.carrier) → IsTight v p AA.carrier → IsTight v p (AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) := by
  first | exact @PositivityTheory.HtPt.Re.ret_tight | exact PositivityTheory.HtPt.Re.ret_tight
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsMultiHomogIdealMapRedMap
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

abbrev redMap (ι : K → Type*) (p : ℕ) : MRing ι →+* MRingOver (ZMod p) ι :=
  MvPolynomial.map (Int.castRingHom (ZMod p))

theorem redMap_surjective (p : ℕ) : Function.Surjective (redMap ι p) := by
  exact MvPolynomial.map_surjective _ ZMod.intCast_surjective

theorem natCast_charOf_mem (W : Ideal (MRing ι)) : ((charOf W : ℕ) : MRing ι) ∈ W := by
  have hc : charOf W = (Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))).natAbs := rfl
  rw [hc]
  set g := Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) with hgdef
  have hg : C g ∈ W := Ideal.mem_comap.mp (Submodule.IsPrincipal.generator_mem _)
  have h : C (g.natAbs : ℤ) ∈ W := by
    rcases Int.natAbs_eq g with h | h
    · rw [← h]; exact hg
    · have e : (g.natAbs : ℤ) = -g := by linarith
      rw [e, map_neg]; exact W.neg_mem hg
  rw [← map_natCast (C : ℤ →+* MRing ι) g.natAbs]
  exact h

theorem ker_redMap_le {p : ℕ} {W : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ W) :
    RingHom.ker (redMap ι p) ≤ W := by
  rw [redMap, MvPolynomial.ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton,
    Ideal.span_le, Set.singleton_subset_iff]
  simpa using hp

theorem comap_map_redMap {p : ℕ} {W : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ W) :
    (W.map (redMap ι p)).comap (redMap ι p) = W := by
  rw [Ideal.comap_map_of_surjective _ (redMap_surjective p), ← RingHom.ker_eq_comap_bot,
    sup_eq_left.mpr (ker_redMap_le hp)]

theorem isMultiHomog_redMap {p : ℕ} {s : MRing ι} {a : K → ℕ} (h : IsMultiHomog s a) :
    IsMultiHomog (redMap ι p s) a := by
  intro m hm k
  refine h m ?_ k
  rw [MvPolynomial.mem_support_iff] at hm ⊢
  intro h0
  apply hm
  simp [redMap, MvPolynomial.coeff_map, h0]

theorem isMultiHomogIdeal_map_redMap {p : ℕ} {W : Ideal (MRing ι)} (h : IsMultiHomogIdeal W) :
    IsMultiHomogIdeal (W.map (redMap ι p)) := by
  obtain ⟨S, hS, rfl⟩ := h
  refine ⟨redMap ι p '' S, ?_, Ideal.map_span _ _⟩
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨a, isMultiHomog_redMap ha⟩

theorem isRelevant_map_redMap {p : ℕ} {W : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ W)
    (h : IsRelevant W) : IsRelevant (W.map (redMap ι p)) := by
  intro k
  obtain ⟨i, hi⟩ := h k
  refine ⟨i, fun hx => hi ?_⟩
  rw [← comap_map_redMap hp, Ideal.mem_comap]
  simpa [redMap] using hx

def quotRedEquiv {p : ℕ} {W : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ W) :
    (MRing ι ⧸ W) ≃+* (MRingOver (ZMod p) ι ⧸ W.map (redMap ι p)) :=
  (Ideal.quotEquivOfEq (by
      rw [← RingHom.comap_ker, Ideal.mk_ker, comap_map_redMap hp])).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := (Ideal.Quotient.mk (W.map (redMap ι p))).comp (redMap ι p))
      (Ideal.Quotient.mk_surjective.comp (redMap_surjective p)))

theorem isProjVarF_map_redMap {p : ℕ} [Fact p.Prime] {W : Ideal (MRing ι)} {n : ℕ}
    (hp : ((p : ℕ) : MRing ι) ∈ W) (hW : IsMultiProjPrime W)
    (hdim : ringKrullDim (MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (W.map (redMap ι p)) n := by
  obtain ⟨hWp, hWh, hWr⟩ := hW
  refine ⟨⟨?_, isMultiHomogIdeal_map_redMap hWh, isRelevant_map_redMap hp hWr⟩, ?_⟩
  · exact Ideal.map_isPrime_of_surjective (redMap_surjective p) (ker_redMap_le hp)
  · rw [← ringKrullDim_eq_of_ringEquiv (quotRedEquiv hp)]
    exact hdim

theorem fibreComp : ReciprocityTheory.ChartRestriction.G.AI.I2.FibreCompStatement := by
  intro K _ ι _ P n A s W hP hs hW hv
  obtain ⟨hK, ⟨hPp, hPh, -⟩, -, hPdim⟩ := hP
  obtain ⟨a, -, hsa, hsP⟩ := hs
  obtain ⟨hWmin, hWrel⟩ := hW
  have hWp : W.IsPrime := hWmin.1.1
  have hWmh : IsMultiHomogIdeal W := isMultiHomogIdeal_of_mem_minimalPrimes hPh hsa hWmin
  have hmp : IsMultiProjPrime W := ⟨hWp, hWmh, hWrel⟩
  have hp := charOf_prime hWp hv
  have := hPp
  have h1 := dim_quot_minimal_add_one P W s hsP hWmin
  rw [hPdim] at h1
  have hdim : ringKrullDim (MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    withBot_eq_of_add_one (by rw [h1, show n + 1 + Fintype.card K = n + Fintype.card K + 1 by omega])
  refine ⟨hp, natCast_charOf_mem W, hmp, ?_⟩
  haveI : Fact (charOf W).Prime := ⟨hp⟩
  exact isProjVarF_map_redMap (natCast_charOf_mem W) hmp hdim

end GlobalTheory.CompanionTheory.Ar.Pub
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.JoinTwoModels
section
namespace GlobalTheory.CompanionTheory.CommAlg

theorem joinTwoModels : GroundTheory.Heights₂.Heights.NumbersDVR.JoinTwoModels.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.JoinTwoModels.proof
    GroundTheory.Heights₂.Heights.NumbersDVR.ConeTrdegFnField.proof

end GlobalTheory.CompanionTheory.CommAlg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MonomialRatioIntegralModel
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.VertDiv

theorem commensurable_vertical : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d : ℕ, IsModelOver (pointIdeal O x) d → ∀ (b b' : K → ℤ) (u : Ω), u ≠ 0 → (∀ s, mseg x s ≠ 0 → (∃ n : ℕ, ∃ r ∈ chartRing O (mseg x) s, algebraMap O Ω ϖ ^ n * chartMon x s b = r * (u * chartMon x s b')) ∧ ∃ n : ℕ, ∃ r ∈ chartRing O (mseg x) s, algebraMap O Ω ϖ ^ n * (u * chartMon x s b') = r * chartMon x s b) → ∃ f g : MRing ι O, IsVerticalDivisor (pointIdeal O x) ϖ (b - b') f g ∧ aeval x f = u * aeval x g :=
  @PositivityTheory.Xgn.t_vertdiv_commensurable

end GlobalTheory.CompanionTheory.Ar.Num.VertDiv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MultiProjectivePrimeIntersection
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Num.Contract

noncomputable section

theorem rename_liftVar_mem_pointIdeal {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω]
    {K K' : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {ι' : K' → Type}
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) {f : MRing ι R} (hf : f ∈ pointIdeal R x) :
    rename (liftVar ι') f ∈ pointIdeal R (joinCoord x z) := by
  have key : ((rename (Sum.inl : K → K ⊕ K') : MvPolynomial K Ω →ₐ[Ω] _).restrictScalars R).comp
      (pointConeMap R x) =
      (pointConeMap R (joinCoord x z)).comp (rename (liftVar ι')) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [pointConeMap, liftVar, joinCoord]
  have hf0 : pointConeMap R x f = 0 := hf
  have h := congrArg (fun φ => φ f) key
  simp only [AlgHom.comp_apply, hf0, map_zero] at h
  exact h.symm

theorem lowered_lt {a : WithBot ℕ∞} {c d n : ℕ} (h : a < ((d + 1 + c : ℕ) : WithBot ℕ∞)) (hn : d < n) :
    WithBot.map (fun e : ℕ∞ => WithTop.map (fun m : ℕ => (m : ℤ) - c) e) a <
      ((n : ℕ) : WithBot (WithTop ℤ)) := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe b =>
    induction b using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) < (((d + 1 + c : ℕ) : ℕ∞) : WithBot ℕ∞) := h
      exact absurd (WithBot.coe_lt_coe.mp h') (by simp)
    | coe m =>
      have h' : (((m : ℕ) : ℕ∞) : WithBot ℕ∞) < (((d + 1 + c : ℕ) : ℕ∞) : WithBot ℕ∞) := h
      have hm : m < d + 1 + c := by exact_mod_cast WithBot.coe_lt_coe.mp h'
      show ((((m : ℤ) - c : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) <
        (((n : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
      exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by omega))

theorem dim_quot_le {A : Type*} [CommRing A] {I J : Ideal A} (h : I ≤ J) :
    ringKrullDim (A ⧸ J) ≤ ringKrullDim (A ⧸ I) :=
  ringKrullDim_le_of_surjective (Ideal.Quotient.factor h) (Ideal.Quotient.factor_surjective h)

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem vNumL_eq_zero_of_dim_le {ϖ : O} (hϖ : Irreducible ϖ)
    {K' : Type} [Fintype K'] [DecidableEq K'] {ι' : K' → Type} [∀ o, Fintype (ι' o)]
    {W : Ideal (MRing ι' O)} (hW : IsMultiProjPrime W) (hϖW : (C ϖ : MRing ι' O) ∈ W)
    {K : Type} [Fintype K] [DecidableEq K] (j : K ↪ K') {n : ℕ}
    (hdim : ringKrullDim (MRing ι' O ⧸ W) ≤ ((n + Fintype.card K' : ℕ) : WithBot ℕ∞))
    (hcon : GroundTheory.Heights₂.Heights.FieldNumbers.relDim
      (GroundTheory.Heights₂.Heights.FieldNumbers.contractPrime j (specialIdeal W)) <
        ((n : ℕ) : WithBot (WithTop ℤ)))
    (l : List (K' → ℤ)) (hl : l.length = n) (hlj : ∀ b ∈ l, ∀ o, o ∉ Set.range j → b o = 0) :
    vNumL W l = 0 := by
  subst hl
  obtain ⟨hQp, -, hrelIff, -⟩ :=
    SpecialIdealCorresp.full O ϖ hϖ K' ι' ⊥ W hW.isPrime hϖW
  have hQm := SpecialIdealMultiHomog.full O K' ι' W hW.multiHomog
  have hdimQ := SpecialQuotDim.full O ϖ hϖ K' ι' W hϖW
  change intNum (IsLocalRing.ResidueField O) (specialIdeal W) l.get = 0
  by_cases hcase : ringKrullDim (MRing ι' (IsLocalRing.ResidueField O) ⧸ specialIdeal W) <
      ((l.length + Fintype.card K' : ℕ) : WithBot ℕ∞)
  · exact IntNumVanish.full (IsLocalRing.ResidueField O) K' ι' l.length (specialIdeal W) hQp hQm
      (Or.inr hcase) l.get
  · have hdimEq : ringKrullDim (MRing ι' (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
        ((l.length + Fintype.card K' : ℕ) : WithBot ℕ∞) :=
      le_antisymm (hdimQ ▸ hdim) (not_lt.mp hcase)
    have hrelQ : GroundTheory.Heights₂.Heights.FieldNumbers.relDim (specialIdeal W) =
        ((l.length : ℕ) : WithBot (WithTop ℤ)) := by
      rw [GroundTheory.Heights₂.Heights.FieldNumbers.relDim, hdimEq]
      have : (((l.length + Fintype.card K' : ℕ) : ℤ) - Fintype.card K') = l.length := by
        push_cast; ring
      exact congrArg (fun z : ℤ => ((z : WithTop ℤ) : WithBot (WithTop ℤ))) this
    have hz := GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaContracted.full
      (IsLocalRing.ResidueField O) K K' j ι' (specialIdeal W)
      ⟨hQp, hQm, hrelIff.mp hW.relevant⟩ l.length hrelQ hcon (fun i => l.get i ∘ j)
    rw [← hz]
    congr 1
    funext i
    exact (SegreFlagCutContraction.pullDeg_comp_of_eq_zero j _
      (hlj _ (List.get_mem l i))).symm

theorem specialIdeal_le_contract {Ω : Type} [Field Ω] [Algebra O Ω]
    {K K' : Type} [Fintype K] [DecidableEq K] [DecidableEq K'] {ι : K → Type} [∀ k, Fintype (ι k)]
    {ι' : K' → Type} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    {W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι'))} (hW : pointIdeal O (joinCoord x z) ≤ W) :
    specialIdeal (pointIdeal O x) ≤
      (GroundTheory.Heights₂.Heights.FieldNumbers.contractPrime (Function.Embedding.inl : K ↪ K ⊕ K')
        (specialIdeal W) : Ideal (MRing ι (IsLocalRing.ResidueField O))) := by
  refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
  show rename (liftVar ι') (MvPolynomial.map (IsLocalRing.residue O) f) ∈ specialIdeal W
  rw [← MvPolynomial.map_rename]
  exact Ideal.mem_map_of_mem _ (hW (rename_liftVar_mem_pointIdeal x z hf))

theorem relDim_contract_lt {Ω : Type} [Field Ω] [Algebra O Ω] {ϖ : O} (hϖ : Irreducible ϖ)
    {K K' : Type} [Fintype K] [DecidableEq K] [DecidableEq K'] {ι : K → Type} [∀ k, Fintype (ι k)]
    {ι' : K' → Type} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) {d n : ℕ} (hdn : d < n)
    (hV : IsModelOver (pointIdeal O x) d)
    {W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι'))} (hW : pointIdeal O (joinCoord x z) ≤ W) :
    GroundTheory.Heights₂.Heights.FieldNumbers.relDim
      (GroundTheory.Heights₂.Heights.FieldNumbers.contractPrime (Function.Embedding.inl : K ↪ K ⊕ K')
        (specialIdeal W)) < ((n : ℕ) : WithBot (WithTop ℤ)) := by
  have hb := SpecialDimBound.full O ϖ hϖ K ι (pointIdeal O x) d hV
  exact lowered_lt (lt_of_le_of_lt (dim_quot_le (specialIdeal_le_contract x z hW)) hb) hdn

end

end GlobalTheory.CompanionTheory.Ar.Num.Contract

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem vNumL_pull_eq_zero_of_contracted : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d r : ℕ, 0 < r → IsModelOver (pointIdeal O x) d → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (W : Ideal (MRing (Sum.elim ι ι') O)), IsMultiProjPrime W → pointIdeal O (joinCoord x z) ≤ W → (C ϖ : MRing (Sum.elim ι ι') O) ∈ W → ∀ l : List (K → ℤ), l.length = d + r → ringKrullDim (MRing (Sum.elim ι ι') O ⧸ W) ≤ ((d + r + Fintype.card (K ⊕ K') : ℕ) : WithBot ℕ∞) → vNumL W (l.map (pullDeg (K' := K'))) = 0 := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x ϖ hϖ d r hr hV K' _ _ ι' _ z W hW hPW hϖW l hl hdim
  refine Contract.vNumL_eq_zero_of_dim_le hϖ hW hϖW (Function.Embedding.inl : K ↪ K ⊕ K')
    (n := d + r) hdim (Contract.relDim_contract_lt hϖ x z (by omega) hV hPW)
    (l.map (pullDeg (K' := K'))) (by simpa using hl) ?_
  intro b hb o ho
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hb
  cases o with
  | inl k => exact absurd ⟨k, rfl⟩ ho
  | inr k => rfl

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderBasisIdealsStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_basis_ideals : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (cs : Fin n → NNReal) (cN : NNReal), (∀ i : Fin n, HasColen R v (stepOrder AA.carrier (flagSub b i) (b i)) (cs i)) → HasColen R v AA.carrier cN → cN ^ (p ^ f) = (∏ i, cs i) ^ Fintype.card N := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.flag_colen | exact GlobalTheory.CompanionTheory.Ar.GR.flag_colen | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.flag_colen <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupTranslationStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_subgroup_translation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → (∃ S : HopfOrder (C := C) R F, S.carrier = stepOrder AA.carrier K t ∧ FStable (F := F) S.carrier) ∧ stepOrder AA.carrier K t = stepOrderRes AA.carrier K t := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hf N _ _ _ _ AA hst K t ht
  classical
  have : Fintype (N ⧸ K) := Fintype.ofFinite _
  have hsurj : Function.Surjective K.mkQ := K.mkQ_surjective
  have hne : K.mkQ t ≠ 0 := by
    simpa [Submodule.Quotient.mk_eq_zero] using ht
  have heq := PositivityTheory.HtPt.Rc.stepOrder_eq AA.carrier K.mkQ hsurj t
  rw [K.ker_mkQ] at heq
  obtain ⟨AQ, hAQ⟩ := PositivityTheory.HtPt.Rc.exists_quo hv AA K.mkQ.toAddMonoidHom hsurj
  obtain ⟨S, hS⟩ := PositivityTheory.HtPt.Rc.exists_res hv AQ
    (LinearMap.toSpanSingleton F (N ⧸ K) (K.mkQ t)).toAddMonoidHom (PositivityTheory.HtPt.Rc.span_inj hne)
  refine ⟨⟨S, ?_, ?_⟩, ?_⟩
  · rw [hS, hAQ, heq]
    rfl
  · rw [hS, hAQ]
    intro a h hh
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hh
    refine Submodule.mem_map.mpr ⟨fun x => g (a • x), ?_, ?_⟩
    · have hg' : (fun x => g (K.mkQ x)) ∈ AA.carrier := hg
      change (fun x => g (a • K.mkQ x)) ∈ AA.carrier
      simpa only [map_smul] using hst a _ hg'
    · funext x
      change g (a • LinearMap.toSpanSingleton F (N ⧸ K) (K.mkQ t) x) =
        g (LinearMap.toSpanSingleton F (N ⧸ K) (K.mkQ t) (a • x))
      rw [map_smul]
  · unfold stepOrder stepOrderRes
    ext h
    constructor
    · intro hh
      obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hh
      exact ⟨g, hg.1, fun a k hk => hg.2 _ _ hk⟩
    · rintro ⟨g, hg, hgh⟩
      obtain ⟨g', hg', hg'e⟩ := PositivityTheory.HtPt.Rc.invres p C v R hv hp N AA K.toAddSubgroup
        (Submodule.span F {t} ⊔ K).toAddSubgroup
        (by
          intro x hx
          exact Submodule.mem_sup_right hx) g hg
        (by
          intro x hx k hk
          obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
          obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
          rw [add_assoc, hgh a _ (K.add_mem hz hk), hgh a z hz])
      refine Submodule.mem_map.mpr ⟨g', hg', ?_⟩
      funext a
      show g' (a • t) = h a
      rw [hg'e (a • t) (Submodule.mem_sup_left (Submodule.mem_span_singleton.mpr ⟨a, rfl⟩))]
      simpa using hgh a 0 K.zero_mem
end

