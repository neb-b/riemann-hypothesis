module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdelicScalarSectionLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0840
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1110
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TransvectionPeriodicity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1089
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1095
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoePolyMapX
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.GraphLocal

variable {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ']

def rightInc (A : Subalgebra ℂ K) : κ' →+* tens (κ' := κ') A :=
  (Algebra.TensorProduct.includeRight : κ' →ₐ[ℂ] K ⊗[ℂ] κ').toRingHom.codRestrict
    (tens (κ' := κ') A).toSubring fun b => tmul_mem (one_mem A) b

def polyMap (A : Subalgebra ℂ K) {m : ℕ} (v : Fin m → A) :
    MvPolynomial (Fin m) κ' →+* tens (κ' := κ') A :=
  MvPolynomial.eval₂Hom (rightInc A) fun i => ⟨(v i : K) ⊗ₜ 1, tmul_mem (v i).2 1⟩

@[simp] theorem coe_polyMap_X (A : Subalgebra ℂ K) {m : ℕ} (v : Fin m → A) (i : Fin m) :
    (polyMap (κ' := κ') A v (MvPolynomial.X i) : K ⊗[ℂ] κ') = (v i : K) ⊗ₜ 1 := by
  simp [polyMap]

@[simp] theorem coe_polyMap_C (A : Subalgebra ℂ K) {m : ℕ} (v : Fin m → A) (b : κ') :
    (polyMap (κ' := κ') A v (MvPolynomial.C b) : K ⊗[ℂ] κ') = 1 ⊗ₜ b := by
  simp [polyMap, rightInc]

end GlobalTheory.GraphLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefInjective
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.LiftScalarCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Places

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem primeToHost (h : R.toLevCh.Is A.μ0) : AdelicScalarSectionLift.PrimeToHost R := by
  intro PP hP
  obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
  refine GlobalTheory.CoverHalf.not_mem_of_coprime PP.isPrime.ne_top (a := D.host.g k) ?_ (R.C.P.overP hk)
  have hc := D.ntypes.g_cond k
  have h1 : Nat.Coprime (D.host.g k) (D.host.QS * D.host.q * D.host.d) := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hc, Nat.gcd_one_left]
  refine Nat.Coprime.mul_right h1 ?_
  refine (D.host.ccK_coprime _ ?_).symm
  simp [D.host.g_level k]

end Places

section Coord

variable {V : HSp D} (c : CoefA V) {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

variable {c}

end Coord

theorem adjoint_idem {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (ρ : Representation ℂ G H) (hu : ∀ g x, ‖ρ g x‖ = ‖x‖) {a : G → ℂ} (ha : GoodBasisCentralIdempotents.IsCentralIdem a) {x : H}
    (hx : (∑ g, a g • ρ g) x = x) (y : H) : ⟪x, (∑ g, a g • ρ g) y⟫_ℂ = ⟪x, y⟫_ℂ := by
  set E : H →ₗ[ℂ] H := ∑ g, a g • ρ g with hE
  have hin : ∀ g u w, ⟪ρ g u, ρ g w⟫_ℂ = ⟪u, w⟫_ℂ := fun g => LinearIsometry.inner_map_map ⟨ρ g, hu g⟩
  have hcomm : ∀ g u, E (ρ g u) = ρ g (E u) := fun g u => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hE, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, ← Module.End.mul_apply, ← map_mul]
    refine (Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ fun h => ?_).symm
    show _ = a (g * h * g⁻¹) • ρ (g * h * g⁻¹ * g) u
    rw [ha.1, inv_mul_cancel_right]
  have hidem : ∀ u, E (E u) = E u := fun u => by
    have h1 : E u = ∑ g, ∑ h, (a h * a (h⁻¹ * g)) • ρ g u := by
      simp only [← Finset.sum_smul, ha.2, hE, LinearMap.sum_apply, LinearMap.smul_apply]
    have h2 : E (E u) = ∑ h, ∑ g, (a h * a g) • ρ h (ρ g u) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hE, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [mul_comm]
    rw [h2, h1, Finset.sum_comm (f := fun g h => (a h * a (h⁻¹ * g)) • ρ g u)]
    refine Finset.sum_congr rfl fun h _ => Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
    simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, Module.End.mul_apply]

  have hadj : ∀ u, LinearMap.adjoint E u = ∑ g, star (a g) • ρ g⁻¹ u := fun u => by
    refine ext_inner_right ℂ fun w => ?_
    rw [LinearMap.adjoint_inner_left, sum_inner, hE, LinearMap.sum_apply, inner_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, inner_smul_right, inner_smul_left, ← hin g (ρ g⁻¹ u), ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]
    simp
  have hfix : E (LinearMap.adjoint E x) = LinearMap.adjoint E x := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hadj, map_sum]
    simp only [map_smul, hcomm, hx]

  have hz : LinearMap.adjoint E x - x = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ)]
    have h1 : E (LinearMap.adjoint E x - x) = LinearMap.adjoint E x - x := by rw [map_sub, hfix, hx]
    rw [inner_sub_left, LinearMap.adjoint_inner_left, h1, sub_self]
  rw [← LinearMap.adjoint_inner_left, sub_eq_zero.1 hz]

end GlobalTheory.LiftScalarCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffMemSubmoduleOfComplexPolyValuesMem
section
namespace GlobalTheory

theorem coeff_mem_of_poly_values_mem : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) (N : ℕ) (c : ℕ → V), (∀ u : ℂ, ∑ k ∈ Finset.range N, u ^ k • c k ∈ S) → ∀ k < N, c k ∈ S := by
  intro V _ _ S N c h k hk
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro f
  set p : Polynomial ℂ := ∑ j ∈ Finset.range N,
    Polynomial.C (f (Submodule.Quotient.mk (c j))) * Polynomial.X ^ j with hpdef
  have hp : p = 0 := by
    apply Polynomial.funext
    intro u
    have h1 : S.mkQ (∑ k ∈ Finset.range N, u ^ k • c k) = 0 :=
      (Submodule.Quotient.mk_eq_zero S).mpr (h u)
    have h0 := congrArg f h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Submodule.mkQ_apply, smul_eq_mul, map_zero] at h0
    simp only [hpdef, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
    rw [← h0]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have hc := congrArg (fun q : Polynomial ℂ => q.coeff k) hp
  simp only [hpdef, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_zero, mul_ite, mul_one, mul_zero] at hc
  rw [Finset.sum_ite_eq] at hc
  simpa [Finset.mem_range.mpr hk] using hc

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactDiscreteSeriesOwnType
section
noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

variable {n : ℕ}

theorem cpt_const {ε : Fin n → Bool} (h : pOf ε = 0 ∨ qOf ε = 0) (a b : Fin n) : ε a = ε b := by
  rcases h with hp | hq
  · have h1 : ∀ c, ε c = false := fun c => by
      have := Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 hp) (Finset.mem_univ c)
      simpa using this
    rw [h1 a, h1 b]
  · have h1 : ∀ c, ε c = true := fun c => by
      have := Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 hq) (Finset.mem_univ c)
      simpa using this
    rw [h1 a, h1 b]

theorem cpt_Jm_comm {ε : Fin n → Bool} (hc : ∀ a b, ε a = ε b) (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Jm ε * M = M * Formalism.REAL.Jm ε := by
  ext i j
  delta Formalism.REAL.Jm
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, hc i j]
  ring

theorem cpt_Kset_eq {ε : Fin n → Bool} (hc : ∀ a b, ε a = ε b) :
    Formalism.REAL.Kset ε = Formalism.MainNotions.S.UJset ε := by
  ext g
  delta Formalism.REAL.Kset Formalism.MainNotions.S.UJset Formalism.REAL.inUJ
  simp only [Set.mem_ofPred_eq, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  constructor
  · rintro ⟨hu, -⟩
    rw [Matrix.mul_assoc, cpt_Jm_comm hc g, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  · intro h
    refine ⟨?_, (cpt_Jm_comm hc g).symm⟩
    have h2 : g.conjTranspose * g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε := by
      rw [Matrix.mul_assoc, ← cpt_Jm_comm hc g, ← Matrix.mul_assoc]
      exact h
    have h3 := congrArg (· * Formalism.REAL.Jm ε) h2
    simp only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one] at h3
    exact h3

theorem compactDiscreteSeries_ownType : CptCase := by
  intro n ε lam h
  have hc := cpt_const h
  refine ⟨fun k => ?_, ?_, ?_⟩
  · have : IsEmpty {x : Fin n × Fin n // IsPhys ε x} :=
      ⟨fun x => by
        have h1 := x.2.1
        have h2 := x.2.2
        rw [hc x.1.1 x.1.2] at h1
        rw [h1] at h2
        exact Bool.noConfusion h2⟩
    unfold physDet
    exact Matrix.det_isEmpty
  · unfold sDeg sModes
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨h1, h2, -⟩
    rw [hc x.1 x.2] at h1
    rw [h1] at h2
    exact Bool.noConfusion h2
  · intro X _ _ D hD
    obtain ⟨hcs, hnt, hU, hirr, -, ⟨S, hS⟩, -⟩ := hD
    have := hcs
    have hKU := cpt_Kset_eq hc
    have : FiniteDimensional ℂ S := hS.1
    have hclosed : IsClosed (S : Set X) := S.isClosed_of_finiteDimensional
    have hstab : ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v ∈ S, D g v ∈ S := fun g hg v hv =>
      hS.2.1 g (hKU ▸ hg) v hv
    have htop : S = ⊤ := by
      rcases hirr S hclosed hstab with h0 | h0
      · exfalso
        obtain ⟨v, hv, hv0, -⟩ := hS.2.2.2.1
        rw [h0] at hv
        exact hv0 ((Submodule.mem_bot ℂ).1 hv)
      · exact h0
    subst htop
    have hga : gaW ε lam = Formalism.QuantumDeterminants.lowK ε lam := by
      funext a
      have hN : Formalism.REAL.rhoN ε a = 0 := by
        unfold Formalism.REAL.rhoN
        have e1 : (Finset.univ.filter fun b => a < b ∧ ε b ≠ ε a) = ∅ :=
          Finset.filter_eq_empty_iff.2 fun b _ hb => hb.2 (hc b a)
        have e2 : (Finset.univ.filter fun b => b < a ∧ ε b ≠ ε a) = ∅ :=
          Finset.filter_eq_empty_iff.2 fun b _ hb => hb.2 (hc b a)
        rw [e1, e2]
        simp
      have hH : rhoHol ε a = 0 := by
        unfold rhoHol
        rcases h with hp | hq
        · have ha : ε a = false := by
            have := Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 hp) (Finset.mem_univ a)
            simpa using this
          simp [ha, hp]
        · have ha : ε a = true := by
            have := Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 hq) (Finset.mem_univ a)
            simpa using this
          simp [ha, hq]
      delta gaW Formalism.QuantumDeterminants.lowK
      simp only [Pi.add_apply, Pi.sub_apply, hN, hH, add_zero]
      rfl
    refine ⟨LinearEquiv.finiteDimensional Submodule.topEquiv, hnt, hKU ▸ hU, ?_⟩
    rw [hga]
    exact hS

end GlobalTheory.PsCo.PcEF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemPrincipalCongruenceSubgroupIffStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_mem_principalCongruenceSubgroup_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n m : ℕ) (h k : GLw n w), k ∈ GlobalTheory.LFun.KGL w (n := n) → (k⁻¹ * h * k ∈ congSet w n m ↔ h ∈ congSet w n m) := by
  first | exact @GlobalTheory.KapOrb.conj_mem_congSet_iff | exact GlobalTheory.KapOrb.conj_mem_congSet_iff | (intros; apply GlobalTheory.KapOrb.conj_mem_congSet_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjQuotNsUnitsEqOne
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ConsEta
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele

theorem under_under_of_compat {F K L : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra F K] [Algebra F L] [alg : Algebra K L]
    (hc : ∀ x : F, algebraMap K L (algebraMap F K x) = algebraMap F L x) (w : HeightOneSpectrum (𝓞 L)) :
    (w.under (𝓞 K)).under (𝓞 F) = w.under (𝓞 F) := by
  ext x
  simp only [HeightOneSpectrum.under_asIdeal, Ideal.mem_under]
  have : algebraMap (𝓞 K) (𝓞 L) (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap (𝓞 F) (𝓞 L) x := by
    apply RingOfIntegers.ext
    exact hc (x : F)
  rw [this]

theorem finEval_ideleMap_localIdele {F K L : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra F K] [Algebra F L] [alg : Algebra K L]
    (hc : ∀ x : F, algebraMap K L (algebraMap F K x) = algebraMap F L x) (w : HeightOneSpectrum (𝓞 L))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.under (𝓞 F) ≠ w.under (𝓞 F)) (a : (v.adicCompletion K)ˣ) :
    Units.map (GlobalTheory.IdeleNormChar.finEval w) (ideleMap K L (Neutral.B1.localIdele K v a)) = 1 := by
  have hne : w.under (𝓞 K) ≠ v := fun h => hv (h ▸ under_under_of_compat hc w)
  apply Units.ext
  show finiteCompletionMap K L w ((Neutral.B1.localIdele K v a : AdeleRing (𝓞 K) K).2 (w.under (𝓞 K))) = 1
  rw [(Neutral.B1.localIdele_isSupportedAt K v a).2 _ hne, map_one]

theorem isSplitAt_of_under_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {v w : HeightOneSpectrum (𝓞 E)}
    (hw : GlobalTheory.UnitaryBC.IsSplitAt w)
    (h : v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) :
    GlobalTheory.UnitaryBC.IsSplitAt v := by
  obtain ⟨u, hu, hu'⟩ := hw
  by_cases hvw : v = w
  · subst hvw; exact ⟨u, hu, hu'⟩
  · exact ⟨w, Ne.symm hvw, h.symm⟩

theorem conjQuot_nsUnits_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)),
    GlobalTheory.UnitaryBC.IsSplitAt w → ∀ u ∈ GlobalTheory.MuExist.nsUnits E, GlobalTheory.ConsEta.conjQuot E w u = 1 := by
  intro E _ _ _ w hw u hu
  have key : GlobalTheory.MuExist.nsUnits E ≤ (conjQuot E w).ker := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨w', a, hw', -, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    have hne : w' ≠ w := fun h => hw' (h ▸ hw)
    have hunder : w'.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) :=
      fun h => hw' (isSplitAt_of_under_eq hw h)
    have h1 : Units.map (GlobalTheory.IdeleNormChar.finEval w) (Neutral.B1.localIdele E w' a) = 1 :=
      Units.ext ((Neutral.B1.localIdele_isSupportedAt E w' a).2 w hne.symm)
    have h2 : Units.map (GlobalTheory.IdeleNormChar.finEval w)
        (ideleConj (maximalRealSubfield E) E (Neutral.B1.localIdele E w' a)) = 1 :=
      finEval_ideleMap_localIdele (F := maximalRealSubfield E)
        (alg := (conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra)
        (fun x => (conj (maximalRealSubfield E) E).commutes x) w w' hunder a
    simp only [conjQuot, MonoidHom.comp_apply, MonoidHom.div_apply, MonoidHom.id_apply, _root_.map_div, h1, h2, div_one]
  exact key hu

end GlobalTheory.ConsEta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtTransgressionTopCoeffComplex
section
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
private lemma continuousAt_dbar_ofReal_of_contDiffAt_one {n : ℕ} {ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n}
    (hρ : ContDiffAt ℝ 1 ρ v) (w : _root_.ReciprocityTheory.L2DbarEstimates.V n) :
    ContinuousAt (fun x => _root_.GlobalTheory.dbar (fun y => (ρ y : ℂ)) x w) v := by
  have h : ContDiffAt ℝ 1 (fun y => (ρ y : ℂ)) v := Complex.ofRealCLM.contDiff.contDiffAt.comp v hρ
  have hf : ContinuousAt (fderiv ℝ (fun y => (ρ y : ℂ))) v :=
    (h.fderiv_right (m := 0) (by norm_num)).continuousAt
  simp only [_root_.GlobalTheory.dbar_apply]
  fun_prop


set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
theorem _root_.GlobalTheory.GoodTop.continuousAt_corrC :
    ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ}
      {G₀ G₁ : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n},
      ContDiffAt ℝ 1 ρ v → _root_.GlobalTheory.HermFrame.MContDiffAt 2 G₀ v → IsUnit (G₀ v).det →
        _root_.GlobalTheory.HermFrame.MContDiffAt 2 G₁ v → IsUnit (G₁ v).det →
        ContinuousAt (_root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁) v := by
  intro n r _ _ ρ G₀ G₁ v hρ h₀ hd₀ h₁ hd₁
  have hcurv : ∀ {G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ}, _root_.GlobalTheory.HermFrame.MContDiffAt 2 G v → IsUnit (G v).det →
      ∀ a b p q, ContinuousAt (fun x => _root_.GlobalTheory.HermFrame.curv G x (_root_.GlobalTheory.GoodMetric.coordVec a)
        (_root_.GlobalTheory.GoodMetric.coordVec b) p q) v :=
    fun hG hdG a b p q =>
      (hG.curv (j := 0) hdG (by norm_num)
        (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) p q).continuousAt
  have hconn : ∀ {G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ}, _root_.GlobalTheory.HermFrame.MContDiffAt 2 G v → IsUnit (G v).det →
      ∀ a p q, ContinuousAt
        (fun x => _root_.GlobalTheory.HermFrame.conn G x (_root_.GlobalTheory.GoodMetric.coordVec a) p q) v :=
    fun hG hdG a p q =>
      (hG.conn (j := 0) hdG (by norm_num)
        (_root_.GlobalTheory.GoodMetric.coordVec a) p q).continuousAt
  have hposition : ∀ j : Fin n, ContinuousAt (fun x => _root_.GlobalTheory.GoodTop.mixTop
      (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one (_root_.GlobalTheory.GoodTop.curvAt G₁ x)
        (_root_.GlobalTheory.GoodTop.cutForm ρ G₀ G₁ x) (_root_.GlobalTheory.GoodTop.curvAt G₀ x) j)) v := by
    intro j
    apply _root_.GlobalTheory.GoodTop.continuousAt_mixTop
    intro i a b p q
    unfold _root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one _root_.GlobalTheory.GoodTop.curvAt _root_.GlobalTheory.GoodTop.cutForm
    split_ifs
    · exact hcurv h₁ hd₁ a b p q
    · exact (continuousAt_dbar_ofReal_of_contDiffAt_one hρ _).mul ((hconn h₁ hd₁ a p q).sub (hconn h₀ hd₀ a p q))
    · exact hcurv h₀ hd₀ a b p q
  have heq : _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ = fun x => ∑ j, _root_.GlobalTheory.GoodTop.mixTop
      (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one (_root_.GlobalTheory.GoodTop.curvAt G₁ x)
        (_root_.GlobalTheory.GoodTop.cutForm ρ G₀ G₁ x) (_root_.GlobalTheory.GoodTop.curvAt G₀ x) j) := by
    funext x
    rfl
  rw [heq]
  exact tendsto_finsetSum _ fun j _ => hposition j

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteFormStabilizerFiniteAwayFromPStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteForm_stabilizer_finite_away_from_p : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level) (K' : Subgroup (Gr G 1)),
  Subgroup.Commensurable K' (KHT p G.m G.n 1 G.Fw) → ∀ (B : GlobalTheory.LKDef.DForm G) (x : G.GAf × Gr G 1),
    Finite (GlobalTheory.LKLoc.locPart B.emb.range (L.K.toSubgroup.prod K') x) := by
  first | (exact @GlobalTheory.DefStab.finite_locPart) | (exact GlobalTheory.DefStab.finite_locPart) | (intros; apply GlobalTheory.DefStab.finite_locPart  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryFinitePartMulInjectiveRangeStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryFinitePart_mul_injective_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ a b : UE E n, finPt (a * b) = finPt a * finPt b) ∧ Function.Injective (finPt : UE E n → finU (E := E) (n := n)) ∧ ∀ x : finU (E := E) (n := n), x ∈ ratFinU E n ↔ ∃ γ : UE E n, finPt γ = x := by
  first | exact @GlobalTheory.BCT.FinPart.finPt_props | exact GlobalTheory.BCT.FinPart.finPt_props | (intros; apply GlobalTheory.BCT.FinPart.finPt_props <;> assumption)
end

