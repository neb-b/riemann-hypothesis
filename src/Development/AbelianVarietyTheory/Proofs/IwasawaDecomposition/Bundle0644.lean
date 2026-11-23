module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeries
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0627
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0139
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0628
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0626
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0622
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0623
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0611
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryEtaleStalkForms
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

noncomputable section

namespace GlobalTheory.FarTrait

section Algebra
open Polynomial

theorem exists_coefficientField (S : Type) [CommRing S] [IsLocalRing S] [IsAdicComplete (maximalIdeal S) S]
    [CharZero (ResidueField S)] :
    ∃ Λ : Subring S, IsField Λ ∧ ∀ s : S, ∃ a ∈ Λ, s - a ∈ maximalIdeal S := by
  let T : Set (Subring S) := {Λ | ∀ x ∈ Λ, x ∈ maximalIdeal S → x = 0}
  have hbot : (⊥ : Subring S) ∈ T := by
    intro x hx hm
    obtain ⟨n, rfl⟩ := Subring.mem_bot.1 hx
    rw [← residue_eq_zero_iff, map_intCast, Int.cast_eq_zero] at hm
    simp [hm]
  obtain ⟨Λ, -, hΛ⟩ := zorn_le_nonempty₀ T (fun c hc hch y hy => by
    refine ⟨sSup c, fun x hx => ?_, fun z hz => le_sSup hz⟩
    obtain ⟨K, hK, hxK⟩ := (Subring.mem_sSup_of_directedOn ⟨y, hy⟩ hch.directedOn).1 hx
    exact hc hK x hxK) ⊥ hbot
  have hT : ∀ x ∈ Λ, x ∈ maximalIdeal S → x = 0 := hΛ.prop
  have hF : IsField Λ := by
    refine ⟨exists_pair_ne _, mul_comm, fun {x} hx => ?_⟩
    have hu : IsUnit (x : S) := by
      by_contra h
      exact hx (Subtype.ext (hT _ x.2 h))
    let Λ' : Subring S :=
      { carrier := {s | ∃ n : ℕ, (x : S) ^ n * s ∈ Λ}
        one_mem' := ⟨0, by simp⟩
        zero_mem' := ⟨0, by simp⟩
        mul_mem' := by
          rintro a b ⟨n, hn⟩ ⟨m, hm⟩
          exact ⟨n + m, by convert Λ.mul_mem hn hm using 1; ring⟩
        add_mem' := by
          rintro a b ⟨n, hn⟩ ⟨m, hm⟩
          exact ⟨n + m, by
            convert Λ.add_mem (Λ.mul_mem (Λ.pow_mem x.2 m) hn) (Λ.mul_mem (Λ.pow_mem x.2 n) hm) using 1; ring⟩
        neg_mem' := by
          rintro a ⟨n, hn⟩
          exact ⟨n, by convert Λ.neg_mem hn using 1; ring⟩ }
    have h' : Λ' ∈ T := by
      rintro s ⟨n, hn⟩ hm
      exact (hu.pow n).mul_right_eq_zero.1 (hT _ hn (Ideal.mul_mem_left _ _ hm))
    have hle : Λ' ≤ Λ := hΛ.le_of_ge h' fun s hs => ⟨0, by simpa using hs⟩
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    exact ⟨⟨y, hle ⟨1, by rw [pow_one, hy]; exact Λ.one_mem⟩⟩, Subtype.ext hy⟩
  refine ⟨Λ, hF, fun s => ?_⟩
  letI := hF.toField
  have key : ∀ a : S, (∀ f : Λ[X], aeval a f ∈ maximalIdeal S → aeval a f = 0) → a ∈ Λ := fun a ha => by
    have h' : (aeval (R := Λ) a).toRingHom.range ∈ T := by
      rintro _ ⟨f, rfl⟩ hm
      exact ha f hm
    exact hΛ.le_of_ge h' (fun y hy => ⟨C ⟨y, hy⟩, by simp; rfl⟩) ⟨X, by simp⟩
  have hres : ∀ (a : S) (f : Λ[X]), residue S (aeval a f) = aeval (residue S a) f := fun a f =>
    (aeval_algHom_apply (IsScalarTower.toAlgHom Λ S (ResidueField S)) a f).symm
  by_cases hs : IsAlgebraic Λ (residue S s)
  · have hi := hs.isIntegral
    haveI : CharZero Λ := RingHom.charZero (algebraMap Λ (ResidueField S))
    have hsep : (minpoly Λ (residue S s)).Separable := (minpoly.irreducible hi).separable
    obtain ⟨a, ha, has⟩ := HenselianRing.is_henselian (I := maximalIdeal S)
      ((minpoly Λ (residue S s)).map (algebraMap Λ S)) ((minpoly.monic hi).map _) s
      (by rw [eval_map_algebraMap, ← residue_eq_zero_iff, hres, minpoly.aeval])
      (by
        rw [derivative_map, eval_map_algebraMap]
        have := hsep.aeval_derivative_ne_zero (minpoly.aeval Λ (residue S s))
        rw [← hres] at this
        exact (isUnit_iff_ne_zero (G₀ := ResidueField S)).2 this)
    have e : residue S a = residue S s := by rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact has
    refine ⟨a, key a fun f hf => ?_, by rw [← neg_sub]; exact neg_mem has⟩
    rw [← residue_eq_zero_iff, hres, e] at hf
    obtain ⟨q, rfl⟩ := minpoly.dvd _ _ hf
    rw [IsRoot.def, eval_map_algebraMap] at ha
    rw [map_mul, ha, zero_mul]
  · refine ⟨s, key s fun f hf => ?_, by simp⟩
    rw [← residue_eq_zero_iff, hres] at hf
    by_contra h
    exact hs ⟨f, by rintro rfl; simp at h, hf⟩

end Algebra


open MvPowerSeries GlobalTheory.CohenStructure in
theorem exists_finite_over_normal (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] [CharZero S]
    [IsNoetherianRing S] [hc : IsAdicComplete (maximalIdeal S) S] :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (i : A →+* S),
      Function.Injective i ∧ i.Finite ∧ IsNoetherianRing A ∧ IsIntegrallyClosed A := by
  obtain ⟨p, hp⟩ := CharP.exists (ResidueField S)
  rcases CharP.char_is_prime_or_zero (ResidueField S) p with h | rfl
  · obtain ⟨A, _, _, _, i, h1, h2, h3, h4, -⟩ := exists_finite_injective_of_isAdicComplete S p h
      (by rw [← residue_eq_zero_iff, map_natCast]; exact CharP.cast_eq_zero _ p) inferInstance hc
    exact ⟨A, inferInstance, inferInstance, i, h1, h2, h3, h4⟩
  haveI := CharP.charP_to_charZero (ResidueField S)
  by_cases hm : maximalIdeal S = ⊥
  · letI := (isField_iff_maximalIdeal_eq.2 hm).toField
    exact ⟨S, inferInstance, inferInstance, RingHom.id S, Function.injective_id, RingHom.Finite.id S, inferInstance,
      inferInstance⟩
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  obtain ⟨Λ, hF, h1⟩ := exists_coefficientField S
  letI := hF.toField
  obtain ⟨n, x₀, hx₀, hd, N, hN⟩ := GlobalTheory.exists_systemOfParameters_insert S a ha0 ha
  let x : Fin (n + 1) → S := Fin.cons a x₀
  have hx : ∀ i, x i ∈ maximalIdeal S := fun i => Fin.cases ha hx₀ i
  let A := MvPowerSeries (Fin (n + 1)) Λ
  let φ : A →ₐ[Λ] S := mvEvalAdic Λ (maximalIdeal S) x hx
  letI : Algebra A S := φ.toRingHom.toAlgebra
  have : IsDomain A := isDomain_mvPowerSeries Λ (n + 1)
  have hb : maximalIdeal Λ = ⊥ := isField_iff_maximalIdeal_eq.1 hF
  have : IsAdicComplete (maximalIdeal Λ) Λ := by rw [hb]; infer_instance
  have hA := isAdicComplete_mvPowerSeries Λ (n + 1)
  have hle : (maximalIdeal A).map (algebraMap A S) ≤ maximalIdeal S := by
    refine Ideal.map_le_iff_le_comap.2 fun g hg => ?_
    have h4 := algHom_sub_constantCoeff_mem φ (K := maximalIdeal S)
      (fun j => by simpa [φ] using hx j) g
    have h5 := FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg
    rw [hb, Ideal.mem_bot] at h5
    rwa [h5, map_zero, sub_zero] at h4
  have hge : maximalIdeal S ^ N ≤ (maximalIdeal A).map (algebraMap A S) := by
    refine hN.trans (Ideal.span_le.2 ?_)
    rw [← Fin.range_cons]
    rintro _ ⟨i, rfl⟩
    show x i ∈ _
    rw [← mvEvalAdic_X (A := Λ) (maximalIdeal S) x hx i]
    exact Ideal.mem_map_of_mem (algebraMap A S)
      (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp))
  have : IsHausdorff ((maximalIdeal A).map (algebraMap A S)) S :=
    IsHausdorff.of_isLocalRing _ _ (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hle)
  have : Module.Finite A (S ⧸ (maximalIdeal A).map (algebraMap A S)) := by
    refine finite_quotient_of_pow_le (fun s => ?_) hge
    obtain ⟨a, ha, h⟩ := h1 s
    refine ⟨C ⟨a, ha⟩, ?_⟩
    rwa [show algebraMap A S (C ⟨a, ha⟩) = a from mvEvalAdic_C _ x hx _]
  have hfin : Module.Finite A S := FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal A)
  refine ⟨A, inferInstance, inferInstance, algebraMap A S,
    injective_of_ringKrullDim_eq (n := n + 1) ?_ (by rw [hd]; norm_cast), hfin, inferInstance,
    isIntegrallyClosed_mvPowerSeries Λ (n + 1)⟩
  rw [FormalIsogeny.ringKrullDim_mvPowerSeries, ringKrullDim_eq_zero_of_isField hF,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]

theorem exists_factor {R W : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [CommRing W] [IsDomain W] [IsIntegrallyClosed W] [CharZero W] (g : R →+* W) :
    ∃ (N : Type) (_ : CommRing N) (_ : IsDomain N) (_ : IsLocalRing N) (φ : R →+* N) (g' : N →+* W),
      IsCN N ∧ IsLocalHom φ ∧ Function.Injective g' ∧ ∀ r, g' (φ r) = g r := by
  haveI := RingHom.ker_isPrime g
  let S := R ⧸ RingHom.ker g
  let k : S →+* W := RingHom.kerLift g
  have hk : Function.Injective k := RingHom.kerLift_injective g
  haveI : IsLocalRing S := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R) S
  haveI : IsAdicComplete (maximalIdeal S) S := CompleteFiniteExtension.isAdicComplete_of_finite_local R S
  haveI : CharZero S := RingHom.charZero k
  obtain ⟨A, _, _, i, hi, hfin, _, _⟩ := exists_finite_over_normal S
  letI : Algebra A S := i.toAlgebra
  have : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).2 hi
  have : Module.Finite A S := hfin
  let N := integralClosure S (FractionRing S)
  have hf : Module.Finite S N := finite_normalisation_of_finite_over_normal A S
  haveI : IsLocalRing N := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := S) _
  have j : Function.Injective ((algebraMap W (FractionRing W)).comp k) := (IsFractionRing.injective W _).comp hk
  let K : FractionRing S →+* FractionRing W := IsFractionRing.lift j
  have hK : ∀ s, K (algebraMap S _ s) = algebraMap W _ (k s) := IsFractionRing.lift_algebraMap j
  have hint : ∀ x : N, K x ∈ (algebraMap W (FractionRing W)).range := fun x =>
    IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.map_of_comp_eq k K (RingHom.ext fun s => (hK s).symm) x.2)
  let eW : W ≃+* (algebraMap W (FractionRing W)).range :=
    RingEquiv.ofBijective (algebraMap W (FractionRing W)).rangeRestrict
      ⟨fun a b h => IsFractionRing.injective W (FractionRing W) (congrArg Subtype.val h),
        RingHom.rangeRestrict_surjective _⟩
  let g' : N →+* W := eW.symm.toRingHom.comp ((K.comp N.val.toRingHom).codRestrict _ hint)
  have hg' : ∀ x : N, algebraMap W (FractionRing W) (g' x) = K x := fun x =>
    congrArg Subtype.val (eW.apply_symm_apply ⟨K x, hint x⟩)
  have hinj : Function.Injective g' := fun a b h =>
    Subtype.ext (K.injective ((hg' a).symm.trans ((congrArg _ h).trans (hg' b))))
  haveI : FaithfulSMul S N := (faithfulSMul_iff_algebraMap_injective S N).2 fun a b h =>
    IsFractionRing.injective S (FractionRing S) (congrArg Subtype.val h)
  haveI : IsLocalHom (Ideal.Quotient.mk (RingHom.ker g)) := IsLocalHom.of_surjective (S := S) _ Ideal.Quotient.mk_surjective
  refine ⟨N, inferInstance, inferInstance, inferInstance, (algebraMap S N).comp (Ideal.Quotient.mk _), g',
    ⟨IsNoetherianRing.of_finite S _, integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing S),
      CompleteFiniteExtension.isAdicComplete_of_finite_local S _, RingHom.charZero g'⟩, inferInstance, hinj, fun r => ?_⟩
  exact IsFractionRing.injective W (FractionRing W) ((hg' _).trans (hK _))



end GlobalTheory.FarTrait
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralRationalAtMember
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.CenRatAt

theorem transfer {K G Pl0 V : Type} [Field K] [NumberField K] [StarRing K] [Group G] [Fintype G]
    (B B' : Formalism.L2.DIV.BlockDat K G Pl0) (hB : B = B') (ℓ : Formalism.L2.DIV.Lvl K G) (Q : V → V → Prop)
    (e : (Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K) → V) (e' : (Fin (B'.S.lvlDim B'.r ℓ.P ℓ.ψ) → K) → V)
    (h : GlobalTheory.Mem.Top.Bl.SameOn e e') (a : MonoidAlgebra K G)
    (H : ∀ x, Q (e x) (e ((B.S.lvlOp B.r ℓ.P ℓ.ψ a).mulVec x))) (x' : Fin (B'.S.lvlDim B'.r ℓ.P ℓ.ψ) → K) :
    Q (e' x') (e' ((B'.S.lvlOp B'.r ℓ.P ℓ.ψ a).mulVec x')) := by
  subst hB
  have he : e = e' := funext fun x => h.2 x x fun i i' hi => congrArg x (Fin.ext hi)
  subst he
  exact H x'

theorem famR_L_eq (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (U U' : Set I.ι)
    (Xg : Finset (R3.Gc X.B px → X.B.LL)) (tr tr' : R3.TrI X.B px) (k : Fin X.toD7.R.m) (s : R3.TupU I U) (s' : R3.TupU I U')
    (h : s.1 = s'.1) : (R3.famR X I hX U Xg tr).A.fam.L k s = (R3.famR X I hX U' Xg tr').A.fam.L k s' := by
  obtain ⟨τ, hτ⟩ := s
  obtain ⟨τ', hτ'⟩ := s'
  cases h
  rfl

section Main

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {p0 : BaseLevelRowSide (w.D Z)}


set_option maxHeartbeats 1000000 in
theorem cenRat_of (t : RowsT K w Z Wt p0) (r : RXs t) : GlobalTheory.CenLocAt.CenRat t.r.Y t.r.z.cG := by
  intro s k z a ha x
  have h5 : (tAll w.I (t.r.Y.tup s)).1 = s.1 := (congrArg w.I.tup (t.r.tup_ix s)).trans (R3.tup_ixOf w.I s)
  have h3 := (r.all.cen (t.r.Y.tup s) z a ha).2.2 k
  exact transfer _ _ (famR_L_eq (w.st Z) w.I t.hX _ _ _ _ _ k _ _ h5) _
    (fun u v => (w.st Z).toD7.ntypes.cenMt (t.r.Y.tup s) ((k : ℕ) + 1) z ((w.st Z).toD7.what₂.jMt (t.r.Y.tup s) ((k : ℕ) + 1) u) =
      (w.st Z).toD7.what₂.jMt (t.r.Y.tup s) ((k : ℕ) + 1) v)
    (r.all.eMt k (t.r.Y.tup s)) (t.r.Y.eMt k s) (r.eMt_use k s) a h3 x

end Main

end GlobalTheory.CenRatAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityBoundedDomainModelEqMulOrigin
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

noncomputable section
namespace GlobalTheory.PointChernScale

open Matrix
open scoped ComplexOrder

theorem curv_tau {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ) (w ξ η : ReciprocityTheory.L2DbarEstimates.V n)
    (hw : (1 - (Z w)ᴴ * Z w).PosDef) :
    curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) w ξ η =
      -(Z ξ * (1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹) := GlobalTheory.T.chernCurvature_modelGram_conjMulTranspose_inv Z w ξ η hw

theorem curv_tauBar {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ) (w ξ η : ReciprocityTheory.L2DbarEstimates.V n)
    (hw : (1 - (Z w)ᴴ * Z w).PosDef) :
    curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) w ξ η =
      -((1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹ * Z ξ)ᵀ := _root_.GlobalTheory.PointChern.curv_modelGram_tauBar Z w ξ η hw

theorem exists_factor {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ) (hP : P.PosDef) :
    ∃ A : Matrix (Fin p) (Fin p) ℂ, IsUnit A.det ∧ Aᴴ * A = P := _root_.GlobalTheory.posDef_eq_conjTranspose_mul_self_of_isUnit_det P hP

theorem posDef_swap {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) (h : (1 - zᴴ * z).PosDef) :
    (1 - z * zᴴ).PosDef := _root_.GlobalTheory.PosDefSwap.main z h

theorem chernPoly_conj {n r : ℕ} (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin r) (Fin r) ℂ) (v v' : ReciprocityTheory.L2DbarEstimates.V n)
    (J : Matrix (Fin n) (Fin n) ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (hS : IsUnit S.det)
    (h : ∀ a b, curv F v (coordVec a) (coordVec b) =
      S⁻¹ * (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) • curv F v' (coordVec c) (coordVec d)) * S) (k : ℕ) :
    chernPoly F v k = aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b))
      (chernPoly F v' k) := _root_.GlobalTheory.ChernConj.chernPoly_conj_subst F v v' J S hS h k

theorem chernPoly_reindex {n a b : ℕ} (e : Fin a ≃ Fin b) (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ) : chernPoly (fun u => reindex e e (F u)) v k = chernPoly F v k := _root_.GlobalTheory.ChernReindex.chernPoly_reindex e F v k

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def zLin {H : Host E} {Dw : Datum H} {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q)
    (σ : GlobalTheory.AllWt.Psi H) : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin Dw.p) (Fin Dw.q) ℂ where
  toFun u := coordOf ix u σ
  map_add' u v := by ext i j; simp [coordOf]
  map_smul' c u := by ext i j; simp [coordOf]

theorem zLin_apply {H : Host E} {Dw : Datum H} {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q)
    (σ : GlobalTheory.AllWt.Psi H) (u : ReciprocityTheory.L2DbarEstimates.V n) : zLin ix σ u = coordOf ix u σ := rfl

def jMat {H : Host E} {Dw : Datum H} {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q)
    (A : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.p) ℂ) (B : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.q) (Fin Dw.q) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := fun c a =>
  (A (ix c).1 * coordOf ix (coordVec a) (ix c).1 * B (ix c).1) (ix c).2.1 (ix c).2.2

theorem zLin_jMat {H : Host E} {Dw : Datum H} {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q)
    (A : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.p) ℂ) (B : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.q) (Fin Dw.q) ℂ)
    (σ : GlobalTheory.AllWt.Psi H) (a : Fin n) :
    zLin ix σ (∑ c, jMat ix A B c a • coordVec c) = A σ * zLin ix σ (coordVec a) * B σ := by
  ext i j
  change (∑ c, jMat ix A B c a • coordVec c) (ix.symm (σ, i, j)) = _
  simp [WithLp.ofLp_sum, Finset.sum_apply, jMat, zLin_apply, Pi.single_apply]

theorem conj_tau {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ) (w : ReciprocityTheory.L2DbarEstimates.V n)
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) (J : Matrix (Fin n) (Fin n) ℂ)
    (hw : (1 - (Z w)ᴴ * Z w).PosDef) (hA : IsUnit A.det) (hAA : Aᴴ * A = (1 - Z w * (Z w)ᴴ)⁻¹)
    (hB : B * Bᴴ = (1 - (Z w)ᴴ * Z w)⁻¹) (hJ : ∀ a, Z (∑ c, J c a • coordVec c) = A * Z (coordVec a) * B)
    (a b : Fin n) :
    curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) w (coordVec a) (coordVec b) =
      A⁻¹ * (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) •
        curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) 0 (coordVec c) (coordVec d)) * A := by
  have h0 : (1 - (Z 0)ᴴ * Z 0).PosDef := by simpa using (PosDef.one : (1 : Matrix (Fin q) (Fin q) ℂ).PosDef)
  have hsum : (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) •
      curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) 0 (coordVec c) (coordVec d)) =
      -(Z (∑ c, J c a • coordVec c) * (Z (∑ d, J d b • coordVec d))ᴴ) := by
    have hc : ∀ ξ η, curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) 0 ξ η = -(Z ξ * (Z η)ᴴ) := by
      intro ξ η
      rw [curv_tau Z 0 ξ η h0]
      simp
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hc, map_sum, map_smul, conjTranspose_sum, conjTranspose_smul, Matrix.sum_mul,
      Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_neg, Finset.sum_neg_distrib, neg_inj]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [mul_comm]; rfl
  rw [hsum, hJ, hJ, curv_tau Z w _ _ hw, ← hAA, ← hB]
  simp only [conjTranspose_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc,
    nonsing_inv_mul_cancel_left _ _ hA]

theorem conj_tauBar {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ) (w : ReciprocityTheory.L2DbarEstimates.V n)
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) (J : Matrix (Fin n) (Fin n) ℂ)
    (hw : (1 - (Z w)ᴴ * Z w).PosDef) (hB0 : IsUnit B.det) (hAA : Aᴴ * A = (1 - Z w * (Z w)ᴴ)⁻¹)
    (hB : B * Bᴴ = (1 - (Z w)ᴴ * Z w)⁻¹) (hJ : ∀ a, Z (∑ c, J c a • coordVec c) = A * Z (coordVec a) * B)
    (a b : Fin n) :
    curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) w (coordVec a) (coordVec b) =
      (Bᵀ)⁻¹ * (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) •
        curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) 0 (coordVec c) (coordVec d)) * Bᵀ := by
  have h0 : (1 - (Z 0)ᴴ * Z 0).PosDef := by simpa using (PosDef.one : (1 : Matrix (Fin q) (Fin q) ℂ).PosDef)
  have hsum : (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) •
      curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) 0 (coordVec c) (coordVec d)) =
      -((Z (∑ d, J d b • coordVec d))ᴴ * Z (∑ c, J c a • coordVec c))ᵀ := by
    have hc : ∀ ξ η, curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) 0 ξ η = -((Z η)ᴴ * Z ξ)ᵀ := by
      intro ξ η
      rw [curv_tauBar Z 0 ξ η h0]
      simp
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hc, map_sum, map_smul, conjTranspose_sum, conjTranspose_smul,
      Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_neg,
      Finset.sum_neg_distrib, neg_inj, transpose_sum, transpose_smul]
    simp only [Finset.smul_sum, smul_smul]
    rfl
  rw [hsum, hJ, hJ, curv_tauBar Z w _ _ hw, ← hAA, ← hB, ← transpose_nonsing_inv, Matrix.mul_neg,
    Matrix.neg_mul, neg_inj, ← transpose_mul, ← transpose_mul]
  congr 1
  simp only [conjTranspose_mul, Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hB0]

theorem chernPoly_model_eq_subst {H : Host E} (Dw : Datum H) {n : ℕ}
    (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (w : ReciprocityTheory.L2DbarEstimates.V n) (hw : InDom (coordOf ix w)) :
    ∃ J : Matrix (Fin n) (Fin n) ℂ, ∀ (τ : E →+* ℂ) (k : ℕ),
      chernPoly (fun u => modelGram H Dw (coordOf ix u) τ) w k =
        aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b))
          (chernPoly (fun u => modelGram H Dw (coordOf ix u) τ) 0 k) := by
  have hP : ∀ σ, (1 - coordOf ix w σ * (coordOf ix w σ)ᴴ)⁻¹.PosDef := fun σ => (posDef_swap _ (hw σ)).inv
  have hQ : ∀ σ, (1 - (coordOf ix w σ)ᴴ * coordOf ix w σ)⁻¹.PosDef := fun σ => (hw σ).inv
  choose A hA hAA using fun σ => exists_factor _ (hP σ)
  choose A' hA' hAA' using fun σ => exists_factor _ (hQ σ)
  let B : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.q) (Fin Dw.q) ℂ := fun σ => (A' σ)ᴴ
  have hB : ∀ σ, B σ * (B σ)ᴴ = (1 - (coordOf ix w σ)ᴴ * coordOf ix w σ)⁻¹ := fun σ => by
    simp only [B, conjTranspose_conjTranspose]; exact hAA' σ
  have hB0 : ∀ σ, IsUnit (B σ).det := fun σ => by
    simp only [B, det_conjTranspose]; exact (hA' σ).star
  refine ⟨jMat ix A B, fun τ k => ?_⟩
  by_cases h : τ (H.rt : E) = H.rt0
  · have e : (fun u => modelGram H Dw (coordOf ix u) τ) = fun u =>
        reindex (finCongr (mult_of_mem Dw h).symm) (finCongr (mult_of_mem Dw h).symm)
          ((1 - (zLin ix ⟨τ, h⟩ u).map (starRingEnd ℂ) * (zLin ix ⟨τ, h⟩ u)ᵀ)⁻¹) := by
      funext u; simp only [modelGram, dif_pos h]; rfl
    rw [e, chernPoly_reindex, chernPoly_reindex]
    exact chernPoly_conj _ w 0 _ (A ⟨τ, h⟩) (hA _)
      (conj_tau (zLin ix ⟨τ, h⟩) w (A _) (B _) _ (hw _) (hA _) (hAA _) (hB _) (zLin_jMat ix A B _)) k
  · by_cases h' : conjEmb τ (H.rt : E) = H.rt0
    · have e : (fun u => modelGram H Dw (coordOf ix u) τ) = fun u =>
          reindex (finCongr (mult_of_not_mem Dw h).symm) (finCongr (mult_of_not_mem Dw h).symm)
            ((1 - (zLin ix ⟨conjEmb τ, h'⟩ u)ᴴ * zLin ix ⟨conjEmb τ, h'⟩ u)⁻¹) := by
        funext u; simp only [modelGram, dif_neg h, dif_pos h']; rfl
      rw [e, chernPoly_reindex, chernPoly_reindex]
      exact chernPoly_conj _ w 0 _ (B _)ᵀ (by rw [det_transpose]; exact hB0 _)
        (conj_tauBar (zLin ix ⟨conjEmb τ, h'⟩) w (A _) (B _) _ (hw _) (hB0 _) (hAA _) (hB _)
          (zLin_jMat ix A B _)) k
    · have e : (fun u => modelGram H Dw (coordOf ix u) τ) = fun _ => 1 := by
        funext u; simp only [modelGram, dif_neg h, dif_neg h']
      have hc : ∀ v, chernPoly (fun _ : ReciprocityTheory.L2DbarEstimates.V n => (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)) v k =
          (1 : Polynomial (MvPolynomial (Fin n × Fin n) ℂ)).coeff k := by
        intro v
        have h0 : curvPoly (fun _ : ReciprocityTheory.L2DbarEstimates.V n => (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)) v = 0 := by
          ext i j; simp [curvPoly]
        simp [chernPoly, h0, Matrix.charpolyRev]
      rw [e, hc, hc, Polynomial.coeff_one]
      split_ifs <;> simp

end GlobalTheory.PointChernScale


open GlobalTheory.PointChernScale in
theorem GlobalTheory.PointChern.chernTop_model_eq_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) {n : ℕ}
    (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (w : ReciprocityTheory.L2DbarEstimates.V n), InDom (coordOf ix w) →
    ∃ κ : ℝ, ∀ R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ,
      chernTop R (fun u => modelGram H Dw (coordOf ix u)) w = κ * chernTop R (fun u => modelGram H Dw (coordOf ix u)) 0 := by
  intro E _ _ _ H Dw n ix w hw
  obtain ⟨J, hJ⟩ := chernPoly_model_eq_subst Dw ix w hw
  refine ⟨Complex.normSq J.det, fun R => ?_⟩
  let φ : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
    aeval fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)
  have hR : aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => modelGram H Dw (coordOf ix u) x.1) w x.2) R =
      φ (aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => modelGram H Dw (coordOf ix u) x.1) 0 x.2) R) := by
    have := congrArg (fun f => f R) (MvPolynomial.comp_aeval (R := ℝ)
      (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => modelGram H Dw (coordOf ix u) x.1) 0 x.2) (φ.restrictScalars ℝ))
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at this
    rw [this]
    exact congrArg (fun f => (aeval f R : MvPolynomial (Fin n × Fin n) ℂ)) (funext fun x => hJ x.1 x.2)
  simp only [chernTop]
  rw [hR, GlobalTheory.GoodMetric.topCoeff_subst_conj, Complex.mul_conj, Complex.re_ofReal_mul]
  ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeMatchRaysAfterDroppingZeroCoordsStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_match_rays_after_dropping_zero_coords : ∀ {X : Type} [AddCommGroup X] {m₀ : ℕ} (p : Fin m₀ → LinearMap.BilinForm ℤ X) (t : Fin m₀ → ℝ), (∀ i, 0 ≤ t i) →
  LinearIndependent ℤ (fun i : {i // 0 < t i} => p i) →
  ∀ β : LinearMap.BilinForm ℤ X, toReal β = ∑ i, t i • toReal (p i) →
  ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), LinearIndependent ℤ δ →
  ∀ c : Fin m → ℝ, (∀ j, 0 ≤ c j) → toReal β = ∑ j, c j • toReal (δ j) →
  (∀ i, 0 < t i → InRCone δ (p i)) →
  (∀ j, 0 < c j → ∃ a : Fin m₀ → ℝ, (∀ i, 0 ≤ a i) ∧ (∀ i, t i = 0 → a i = 0) ∧ toReal (δ j) = ∑ i, a i • toReal (p i)) →
  (∀ i, 0 < t i → ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j)) ∧
    (∀ j, 0 < c j → ∃ i, 0 < t i ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j) ∧ c j = t i * d) := by
  first | exact @GlobalTheory.PolFan.cone_match_rays_of_nonneg | exact GlobalTheory.PolFan.cone_match_rays_of_nonneg | (intros; apply GlobalTheory.PolFan.cone_match_rays_of_nonneg <;> assumption)
end

