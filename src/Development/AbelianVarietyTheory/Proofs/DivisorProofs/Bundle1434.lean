module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298
public import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasOrbIntTensorOfHasOrbInt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeightedOrbitalIntegralTypeTestVanish
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
public import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1398
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicFactorFiniteMod
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC.QuotMonic

variable {M : Type} [AddCommGroup M] [Module ℂ M] (M' K : Submodule ℂ M)

def stabAlg : Subalgebra ℂ (Module.End ℂ M) where
  carrier := {f | ∀ x ∈ M', f x ∈ M' ∧ (x ∈ K → f x ∈ K)}
  mul_mem' := fun {f g} hf hg x hx => ⟨(hf _ (hg x hx).1).1, fun hk => (hf _ (hg x hx).1).2 ((hg x hx).2 hk)⟩
  add_mem' := fun {f g} hf hg x hx => ⟨M'.add_mem (hf x hx).1 (hg x hx).1, fun hk => K.add_mem ((hf x hx).2 hk) ((hg x hx).2 hk)⟩
  algebraMap_mem' := fun r x hx => ⟨by simpa [Module.algebraMap_end_apply] using M'.smul_mem r hx,
    fun hk => by simpa [Module.algebraMap_end_apply] using K.smul_mem r hk⟩

variable {M' K}

def restrictQ (f : stabAlg M' K) : Module.End ℂ (M' ⧸ K.comap M'.subtype) :=
  (K.comap M'.subtype).mapQ (K.comap M'.subtype) (f.1.restrict fun x hx => (f.2 x hx).1) fun x hx => by
    simp only [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.restrict_apply] at hx ⊢
    exact (f.2 x x.2).2 hx


variable (M' K) in
def quotRep : stabAlg M' K →ₐ[ℂ] Module.End ℂ (M' ⧸ K.comap M'.subtype) where
  toFun := restrictQ
  map_one' := by
    refine LinearMap.ext fun y => Submodule.Quotient.induction_on _ y fun x => ?_
    rfl
  map_mul' f g := by
    refine LinearMap.ext fun y => Submodule.Quotient.induction_on _ y fun x => ?_
    rfl
  map_zero' := by
    refine LinearMap.ext fun y => Submodule.Quotient.induction_on _ y fun x => ?_
    rfl
  map_add' f g := by
    refine LinearMap.ext fun y => Submodule.Quotient.induction_on _ y fun x => ?_
    rfl
  commutes' r := by
    refine LinearMap.ext fun y => Submodule.Quotient.induction_on _ y fun x => ?_
    rfl


variable (M' K) in
def quotIncl : (M' ⧸ K.comap M'.subtype) →ₗ[ℂ] M ⧸ K :=
  (K.comap M'.subtype).liftQ (K.mkQ ∘ₗ M'.subtype) fun x hx => by simpa using hx

theorem quotIncl_injective : Function.Injective (quotIncl M' K) := by
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ fun x hx => by simpa using hx

theorem quotIncl_quotRep (b : stabAlg M' K) (v : M) (hv : v ∈ M') :
    quotIncl M' K (quotRep M' K b (Submodule.Quotient.mk ⟨v, hv⟩)) = K.mkQ (b.1 v) := rfl

end GlobalTheory.LeviHC.QuotMonic

namespace GlobalTheory.LeviHC.QuotMonic


open Algebra in
theorem monicFactorFiniteMod_of (H : MonicFactorFinite) : MonicFactorFiniteMod := by
  intro M _ _ M' K c p q hp hq hpp hqq hpq hM hK hc v hv hfin
  classical
  set S := stabAlg M' K
  have hpB : ∀ u, p u ∈ S := fun u x hx => ⟨(hM u x hx).2.1, fun hk => (hK u x hk).1⟩
  have hqB : ∀ u, q u ∈ S := fun u x hx => ⟨(hM u x hx).2.2, fun hk => (hK u x hk).2⟩
  have hcB : ∀ u, c u ∈ S := fun u x hx => ⟨(hM u x hx).1, fun hk =>
    (K.sub_mem_iff_left (hK u _ (hK u x hk).2).1).1 (hc u x hx)⟩
  let pS : ℂ → S := fun u => ⟨p u, hpB u⟩
  let qS : ℂ → S := fun u => ⟨q u, hqB u⟩
  let cS : ℂ → S := fun u => ⟨c u, hcB u⟩
  let ρ := quotRep M' K

  have poly : ∀ (r : ℂ → Module.End ℂ M) (hr : ∀ u, r u ∈ S),
      (∃ (d : ℕ) (a : ℕ → Module.End ℂ M), a d = 1 ∧ ∀ u, r u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i) →
      ∃ (d : ℕ) (a : ℕ → Module.End ℂ (M' ⧸ K.comap M'.subtype)), a d = 1 ∧
        ∀ u, ρ ⟨r u, hr u⟩ = ∑ i ∈ Finset.range (d + 1), u ^ i • a i := by
    intro r hr ⟨d, a, ha1, hra⟩
    have haB : ∀ i < d + 1, a i ∈ S := fun i hi =>
      (Subalgebra.mem_toSubmodule S).1 ((Submodule.span_le.2 (by rintro _ ⟨u, rfl⟩; exact hr u))
        (coeff_mem_span hra hi))
    let a' : ℕ → S := fun i => if h : a i ∈ S then ⟨a i, h⟩ else 0
    have ha' : ∀ i < d + 1, (a' i).1 = a i := fun i hi => by simp [a', haB i hi]
    refine ⟨d, fun i => ρ (a' i), ?_, fun u => ?_⟩
    · have : a' d = 1 := Subtype.ext ((ha' d (Nat.lt_succ_self d)).trans ha1)
      show ρ (a' d) = 1
      rw [this, map_one]
    · have e : (⟨r u, hr u⟩ : S) = ∑ i ∈ Finset.range (d + 1), u ^ i • a' i := by
        apply Subtype.ext
        change r u = _
        rw [hra u]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [show ((∑ i ∈ Finset.range (d + 1), u ^ i • a' i : S) : Module.End ℂ M) = ∑ i ∈ Finset.range (d + 1), u ^ i • (a' i : Module.End ℂ M) from
          map_sum S.val.toLinearMap (fun i => u ^ i • a' i) _ |>.trans (Finset.sum_congr rfl fun i _ => map_smul S.val.toLinearMap _ _)]
        exact Finset.sum_congr rfl fun i hi => by rw [ha' i (Finset.mem_range.1 hi)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e, map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  have hcS : ∀ u, ρ (cS u) = ρ (pS u) * ρ (qS u) := fun u => by
    rw [← map_mul]
    refine LinearMap.ext fun y => Submodule.Quotient.induction_on _ y fun x => ?_
    obtain ⟨x, hx⟩ := x
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq]
    simpa using hc u x hx

  have hval : ∀ (r : ℂ → Module.End ℂ M) (hr : ∀ u, r u ∈ S),
      (adjoin ℂ (Set.range fun u => (⟨r u, hr u⟩ : S))).map S.val = adjoin ℂ (Set.range r) := by
    intro r hr
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    rfl
  have hrho : ∀ (s : ℂ → S), adjoin ℂ (Set.range fun u => ρ (s u)) = (adjoin ℂ (Set.range s)).map ρ := by
    intro s
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    rfl
  set v' : M' ⧸ K.comap M'.subtype := Submodule.Quotient.mk ⟨v, hv⟩
  have hj := quotIncl_injective (M' := M') (K := K)
  have key := H (M' ⧸ K.comap M'.subtype) (fun u => ρ (pS u)) (fun u => ρ (qS u)) (poly p hpB hp) (poly q hqB hq)
    (fun u u' => (show Commute (pS u) (pS u') from Subtype.ext (hpp u u').eq).map ρ)
    (fun u u' => (show Commute (qS u) (qS u') from Subtype.ext (hqq u u').eq).map ρ)
    (fun u u' => (show Commute (pS u) (qS u') from Subtype.ext (hpq u u').eq).map ρ) v' ?_
  ·
    haveI := key
    unfold FinMod
    refine Submodule.finiteDimensional_of_le (?_ : _ ≤ Submodule.map (quotIncl M' K)
      (Submodule.span ℂ {y | ∃ a ∈ adjoin ℂ (Set.range fun u => ρ (pS u)), y = a v'}))
    rw [Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    rw [← hval p hpB] at ha
    obtain ⟨b, hb, rfl⟩ := Subalgebra.mem_map.1 ha
    refine Submodule.subset_span ⟨ρ b v', ⟨ρ b, ?_, rfl⟩, quotIncl_quotRep b v hv⟩
    rw [hrho pS]
    exact Subalgebra.mem_map.2 ⟨b, hb, rfl⟩
  · haveI : FiniteDimensional ℂ (Submodule.span ℂ {y : M ⧸ K | ∃ a ∈ adjoin ℂ (Set.range c), y = K.mkQ (a v)}) := hfin
    set T := Submodule.span ℂ {y | ∃ a ∈ adjoin ℂ (Set.range fun u => ρ (pS u) * ρ (qS u)), y = a v'}
    have hle : T.map (quotIncl M' K) ≤
        Submodule.span ℂ {y : M ⧸ K | ∃ a ∈ adjoin ℂ (Set.range c), y = K.mkQ (a v)} := by
      rw [Submodule.map_span]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      have e : (fun u => ρ (pS u) * ρ (qS u)) = fun u => ρ (cS u) := funext fun u => (hcS u).symm
      rw [e, hrho cS] at ha
      obtain ⟨b, hb, rfl⟩ := Subalgebra.mem_map.1 ha
      refine Submodule.subset_span ⟨b.1, ?_, quotIncl_quotRep b v hv⟩
      rw [← hval c hcB]
      exact Subalgebra.mem_map.2 ⟨b, hb, rfl⟩
    haveI := Submodule.finiteDimensional_of_le hle
    exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ hj T).symm

end GlobalTheory.LeviHC.QuotMonic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentEqZeroOfCommuteSepAlg
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp

namespace GlobalTheory.RegSSClass

theorem nilpotent_eq_zero_of_commute_sep_alg {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    {A N : Matrix (Fin n) (Fin n) K} (hA : A.charpoly.Separable) (hN : IsNilpotent N) (hc : Commute A N) :
    N = 0 := by
  set f := Matrix.toLin' A
  have hcp : f.charpoly = A.charpoly := Matrix.charpoly_toLin' A
  have hfg : Commute f (Matrix.toLin' N) := hc.map Matrix.toLinAlgEquiv'
  have hNl : IsNilpotent (Matrix.toLin' N) := hN.map Matrix.toLinAlgEquiv'
  obtain ⟨k, hk⟩ := hNl
  have key : ∀ μ, Module.End.maxGenEigenspace f μ ≤ LinearMap.ker (Matrix.toLin' N) := fun μ v hv => by
    have h1 : Module.finrank K (Module.End.maxGenEigenspace f μ) ≤ 1 := by
      rw [LinearMap.finrank_maxGenEigenspace_eq, hcp]; exact Polynomial.rootMultiplicity_le_one_of_separable hA μ
    by_cases h0 : v = 0
    · simp [h0]
    have h2 : Module.finrank K (Module.End.maxGenEigenspace f μ) = 1 := le_antisymm h1
        (Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, hv⟩, fun h => h0 (congrArg Subtype.val h)⟩)
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : Module.End.maxGenEigenspace f μ)
        fun h => h0 (congrArg Subtype.val h)).1 h2 ⟨_, Module.End.mapsTo_maxGenEigenspace_of_comm hfg μ hv⟩
    have hc' : Matrix.toLin' N v = c • v := (congrArg Subtype.val hc).symm
    have hpow : ∀ m : ℕ, (Matrix.toLin' N ^ m) v = c ^ m • v := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hc', smul_smul, pow_succ]
    have h5 : c ^ k • v = 0 := by rw [← hpow, hk]; rfl
    have hc0 : c = 0 := by
      rcases smul_eq_zero.1 h5 with h | h
      · exact pow_eq_zero_iff'.1 h |>.1
      · exact absurd h h0
    rw [LinearMap.mem_ker, hc', hc0, zero_smul]
  have h3 := iSup_le key
  rw [Module.End.iSup_maxGenEigenspace_eq_top, top_le_iff, LinearMap.ker_eq_top] at h3
  exact Matrix.toLin'.injective (by rw [h3, map_zero])

theorem nilpotent_eq_zero_of_commute_sep {K : Type} [Field K] {n : ℕ}
    {A N : Matrix (Fin n) (Fin n) K} (hA : A.charpoly.Separable) (hN : IsNilpotent N) (hc : Commute A N) :
    N = 0 := by
  have h := nilpotent_eq_zero_of_commute_sep_alg (K := AlgebraicClosure K)
    (A := A.map (algebraMap K (AlgebraicClosure K))) (N := N.map (algebraMap K (AlgebraicClosure K)))
    (by rw [Matrix.charpoly_map]; exact hA.map) (hN.map (algebraMap K (AlgebraicClosure K)).mapMatrix)
    (hc.map (algebraMap K (AlgebraicClosure K)).mapMatrix)
  ext i j
  have := congrFun (congrFun h i) j
  simpa using this

theorem isSemisimple_of_charpoly_separable {K : Type} [Field K] {n : ℕ} {A : Matrix (Fin n) (Fin n) K}
    (h : A.charpoly.Separable) : Module.End.IsSemisimple (Matrix.toLin' A) := by
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := A.charpoly) h.squarefree ?_
  have := LinearMap.aeval_self_charpoly (Matrix.toLin' A)
  rwa [Matrix.charpoly_toLin'] at this

theorem charpoly_eq_of_isConj {K : Type} [Field K] {n : ℕ} {G : Subgroup (GL (Fin n) K)} {a b : G}
    (h : IsConj a b) : b.1.1.charpoly = a.1.1.charpoly := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  simpa using Matrix.charpoly_units_conj c.1 a.1.1

end GlobalTheory.RegSSClass

open GlobalTheory.RegSSClass in
theorem GlobalTheory.regSS_conjClass_isSSClass : ∀ {D : D7} {V : HSp D} (γ : GF V), IsRegSS γ.1.1 → IsSSClass {δ : GF V | IsConj γ δ} := by
  intro D V γ hγ
  have hs : γ.1.1.charpoly.Separable := hγ
  refine ⟨γ, isSemisimple_of_charpoly_separable hs, ?_⟩
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hx
    refine ⟨x, ⟨isSemisimple_of_charpoly_separable ?_, Commute.refl _, by simp⟩, hx⟩
    rw [charpoly_eq_of_isConj hx]; exact hs
  · rintro ⟨s, ⟨_, hcomm, hnil⟩, hconj⟩
    have hss : s.1.1.charpoly.Separable := by rw [charpoly_eq_of_isConj hconj]; exact hs
    have h0 := nilpotent_eq_zero_of_commute_sep hss hnil (hcomm.symm.sub_right (Commute.refl _))
    have hxs : x = s := Subtype.ext (Units.ext (sub_eq_zero.1 h0))
    rw [hxs]; exact hconj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAdelicThetaSumSchroedingerRationalPairInvari
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaRatInv

theorem invOf_two_eq' {F : Type} [Field F] [NumberField F] [Invertible (2 : AF F)] :
    ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
  refine invOf_eq_right_inv ?_
  rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
  simp

theorem thetaSum_schr_rat_add {F : Type} [Field F] [NumberField F] [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ)
    (hψ : ∀ a : F, ψ (algebraMap F (AF F) a) = 1) {κ : Type} [Fintype κ] (Φ : (κ → AF F) → ℂ) (a b : κ → F)
    (w : (κ → AF F) × (κ → AF F)) :
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ ((fun i => algebraMap F (AF F) (a i), fun i => algebraMap F (AF F) (b i)) + w) Φ) =
      ψ (⅟(2 : AF F) * (w.1 ⬝ᵥ (fun i => algebraMap F (AF F) (b i)) - (fun i => algebraMap F (AF F) (a i)) ⬝ᵥ w.2)) *
        GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ) := by
  set ra : κ → AF F := fun i => algebraMap F (AF F) (a i) with hra
  set rb : κ → AF F := fun i => algebraMap F (AF F) (b i) with hrb
  simp only [GlobalTheory.WeilM.thetaSum]
  rw [← tsum_mul_left, ← (Equiv.addRight a).tsum_eq (fun ξ : κ → F => ψ (⅟(2 : AF F) * (w.1 ⬝ᵥ rb - ra ⬝ᵥ w.2)) *
    GlobalTheory.WeilM.schr ψ w Φ fun i => algebraMap F (AF F) (ξ i))]
  refine tsum_congr fun ξ => ?_
  set rξ : κ → AF F := fun i => algebraMap F (AF F) (ξ i) with hrξ
  have e1 : (fun i => algebraMap F (AF F) ((Equiv.addRight a ξ) i)) = rξ + ra := by
    funext i; simp [hrξ, hra]
  have e3 : ∀ c d : κ → F, (fun i => algebraMap F (AF F) (c i)) ⬝ᵥ (fun i => algebraMap F (AF F) (d i)) =
      algebraMap F (AF F) (c ⬝ᵥ d) := fun c d => by
    simp [dotProduct]
  rw [e1]
  simp only [GlobalTheory.WeilM.schr, Prod.fst_add, Prod.snd_add, ← mul_assoc, ← AddChar.map_add_eq_mul]
  have hx : rξ + (ra + w.1) = rξ + ra + w.1 := (add_assoc _ _ _).symm
  rw [hx]
  congr 1
  have h1 := hψ (ξ ⬝ᵥ b + 1 / 2 * (a ⬝ᵥ b))
  conv_rhs => rw [← mul_one (ψ _), ← h1, ← AddChar.map_add_eq_mul]
  congr 1
  rw [map_add (f := _), map_mul, ← invOf_two_eq', ← e3, ← e3]
  simp only [add_dotProduct, dotProduct_add]
  have t : ∀ z : AF F, ⅟(2 : AF F) * z + ⅟(2 : AF F) * z = z := fun z => by
    rw [← add_mul, invOf_two_add_invOf_two, one_mul]
  linear_combination t (ra ⬝ᵥ w.2)

theorem norm_thetaSum_schr_ratPair_add : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ] (Φ : (κ → AF F) → ℂ),
    ∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, ∀ w : (κ → AF F) × (κ → AF F),
      ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (γ + w) Φ)‖ = ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)‖ := by
  intro F _ _ ψ hψ κ _ Φ γ hγ w
  obtain ⟨a, b, rfl⟩ := (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff γ).mp hγ
  rw [thetaSum_schr_rat_add ψ hψ.2.2.1 Φ a b w, norm_mul, hψ.2.1, one_mul]

end GlobalTheory.ThetaRatInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotMemDivUniformizerPow
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem not_mem_div_uniformizer_pow : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ π : R, Irreducible π → ∀ x : Ω, x ≠ 0 → ∃ n : ℕ, x / algebraMap K Ω (algebraMap R K π) ^ n ∉ V := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV π hπ x hx
  classical
  letI : Algebra R Ω := ((algebraMap K Ω).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsSeparable K Ω := IsSepClosure.separable

  have hRV : ∀ r : R, algebraMap R Ω r ∈ V := by
    intro r
    have : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := by
      rw [hV]; exact ⟨r, rfl⟩
    exact this

  have hKV : ∀ c : K, algebraMap K Ω c ∈ V → ∃ r : R, algebraMap R K r = c := by
    intro c hc
    have : c ∈ V.toSubring.comap (algebraMap K Ω) := hc
    rw [hV] at this
    exact this
  have halgK : IsAlgebraic K x⁻¹ := Algebra.IsAlgebraic.isAlgebraic _
  have halgR : IsAlgebraic R x⁻¹ := (IsFractionRing.isAlgebraic_iff R K Ω).2 halgK
  obtain ⟨d, hd0, hint⟩ := halgR.exists_integral_multiple
  let f : R →+* V := (algebraMap R Ω).codRestrict V.toSubring hRV
  letI : Algebra R V := f.toAlgebra
  haveI : IsScalarTower R V Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hintV : IsIntegral V (d • x⁻¹) := hint.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hintV
  have hyV : d • x⁻¹ ∈ V := by rw [← hy]; exact y.2

  have hfin : FiniteMultiplicity π d := FiniteMultiplicity.of_not_isUnit hπ.not_isUnit hd0
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ¬ π ^ n ∣ d := by
    obtain ⟨m, hm⟩ := hfin
    exact ⟨m + 1, hm⟩
  refine ⟨n, fun hmem => hn ?_⟩
  have hprod : d • x⁻¹ * (x / algebraMap K Ω (algebraMap R K π) ^ n) ∈ V := V.mul_mem _ _ hyV hmem
  have hπ0 : algebraMap R K π ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hπ.ne_zero
  have heq : d • x⁻¹ * (x / algebraMap K Ω (algebraMap R K π) ^ n) =
      algebraMap K Ω (algebraMap R K d / algebraMap R K π ^ n) := by
    rw [Algebra.smul_def, map_div₀, map_pow]
    change (algebraMap K Ω) (algebraMap R K d) * x⁻¹ * _ = _
    field_simp
  rw [heq] at hprod
  obtain ⟨r, hr⟩ := hKV _ hprod
  refine ⟨r, ?_⟩
  apply IsFractionRing.injective R K
  rw [map_mul, map_pow, hr]
  field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParsevalFundamentalDomainTheta
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaUnfold

open GlobalTheory.WeilM
open scoped Classical

theorem continuous_infToMixed (F : Type) [Field F] [NumberField F] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem adele_nontrivial (F : Type) [Field F] [NumberField F] : Nontrivial (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (Nontrivial (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem schA_continuous (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schA F κ) : Continuous Φ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine (f.continuous.comp ?_).mul (hg.1.continuous.comp ?_)
    · exact continuous_pi fun i =>
        (continuous_infToMixed F).comp (continuous_fst.comp (continuous_apply i))
    · exact continuous_pi fun i => continuous_snd.comp (continuous_apply i)
  | zero => exact continuous_const
  | add Φ Ψ _ _ h1 h2 => exact h1.add h2
  | smul c Φ _ h => exact continuous_const.mul h

def ratEquiv (F : Type) [Field F] [NumberField F] (κ : Type) : (κ → F) ≃ GlobalTheory.ThetaParseval.ratVec F κ :=
  Equiv.ofBijective
    (fun ξ => ⟨fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i), (GlobalTheory.ThetaParseval.mem_ratVec_iff _).2 ⟨ξ, rfl⟩⟩)
    ⟨fun a b h => funext fun i => (haveI := adele_nontrivial F; (algebraMap F (AdeleRing (𝓞 F) F)).injective) (congrFun (congrArg Subtype.val h) i),
     fun y => by
      obtain ⟨ξ, hξ⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff y.1).1 y.2
      exact ⟨ξ, Subtype.ext hξ.symm⟩⟩

theorem unfold : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (𝓕₁ : Set (κ → AF F)), @IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) _ _ _ (borel _) 𝓕₁ μ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
      ∫⁻ x in 𝓕₁, ∑' ξ : κ → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + x)‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ _ μ hμ 𝓕₁ h𝓕 Φ hΦ
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  have hc := schA_continuous F hΦ
  haveI : Countable F := by
    have b := Module.finBasis ℚ F
    exact Countable.of_equiv _ b.equivFun.toEquiv.symm
  haveI : Countable (GlobalTheory.ThetaParseval.ratVec F κ) := Countable.of_equiv _ (ratEquiv F κ)
  have hm : ∀ c : κ → AF F, Measurable fun x : κ → AF F => ‖Φ (c + x)‖ₑ ^ 2 := fun c =>
    ((hc.comp (continuous_const.add continuous_id)).measurable.enorm).pow_const 2
  rw [lintegral_tsum fun ξ => (hm _).aemeasurable, h𝓕.lintegral_eq_tsum' (fun x => ‖Φ x‖ₑ ^ 2)]
  rw [← ((ratEquiv F κ).trans (Equiv.neg _)).tsum_eq]
  refine tsum_congr fun ξ => ?_
  simp only [Equiv.trans_apply, Equiv.neg_apply, neg_neg, AddSubgroup.vadd_def, vadd_eq_add]
  rfl
end GlobalTheory.ThetaUnfold
end
end

