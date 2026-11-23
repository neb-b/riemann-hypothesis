module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0303
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
public import Formalism.SharpRestriction.LevelLetterCocycles.TWSet
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0309
public import GroundTheory.LocalFields.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H0TwDualEqZero
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.LocTwoOnto

theorem H0_twDual_eq_zero {R Γ M : Type} [CommRing R] [Group Γ] [AddCommGroup M] [Module R M]
    (μ : Γ →* Rˣ) (ρ : Representation R Γ M)
    (hc : ∀ φ : M →+ R, (∀ g h m, φ (ρ g (ρ h m)) = φ (ρ h (ρ g m))) → φ = 0)
    (y : H0 (twDual μ ρ)) : y = 0 := by
  obtain ⟨φ, hφ⟩ := y
  have hfix : ∀ g, twDual μ ρ g φ = φ := hφ
  let f : M →ₗ[R] R := φ

  have hmul : ∀ g m, f (ρ g m) = ((μ g : Rˣ) : R) * f m := by
    intro g m
    have h := congrArg (fun ψ : TDual R M => ψ (ρ g m)) (hfix g)
    simp only [twDual_apply, Representation.inv_self_apply] at h
    exact h.symm

  have hzero : f.toAddMonoidHom = 0 :=
    hc _ fun g h m => by
      simp only [LinearMap.toAddMonoidHom_coe, hmul]
      ring
  apply Subtype.ext
  apply DFunLike.ext
  intro m
  have hm := congrArg (fun k : M →+ R => k m) hzero
  simp only [LinearMap.toAddMonoidHom_coe, AddMonoidHom.zero_apply] at hm
  exact hm

theorem loc2_surjective : PoitouTateTotallyComplex → ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (Λ M : Type) [CommRing Λ] [AddCommGroup M] [Module Λ M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (ρ : Representation Λ (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), (∀ m : M, l • m = 0) → ContainsAbove S l → (∀ v, IsPlaceOver (Av v) v.1) → ContAction ρ → (∀ (C : Type) [AddCommGroup C] (φ : M →+ C), (∀ g h m, φ (ρ g (ρ h m)) = φ (ρ h (ρ g m))) → φ = 0) → ∀ x : ∀ v : S, H2 (ρ.comp (locFam S Av v)), ∃ y : H2 ρ, ∀ v, resH2 ρ (locFam S Av v) (continuous_locFam S Av v) y = x v := by
  intro hPT F Ω _ _ _ _ _ _ l _ Λ M _ _ _ _ _ _ S Av ρ hl hS hAv hρ hcomm x
  have hl0 : 0 < l ^ 1 := pow_pos (Fact.out : l.Prime).pos 1
  have : NeZero (l ^ (1 : ℕ)) := ⟨hl0.ne'⟩

  have hl1 : ∀ m : M, (l ^ (1 : ℕ)) • m = 0 := fun m => by rw [pow_one]; exact hl m
  have instZ : Module (ZMod (l ^ (1 : ℕ))) M := AddCommGroup.zmodModule hl1
  have : ContinuousConstSMul (ZMod (l ^ (1 : ℕ))) M := ⟨fun _ => continuous_of_discreteTopology⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective

  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (l ^ (1 : ℕ)) Ω)
    (Polynomial.degree_cyclotomic_pos _ _ hl0).ne'
  have hζ' : IsPrimitiveRoot ζ (l ^ (1 : ℕ)) := (Polynomial.isRoot_cyclotomic_iff_charZero hl0).1 hζ
  obtain ⟨inv, -, hall⟩ := hPT F Ω l 1 one_pos ζ hζ'
  obtain ⟨μ, hμ⟩ := PoitouTate.exists_lift_cycMod (Ω := Ω) (r := 1) hS

  let ρ' : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* Module.End (ZMod (l ^ (1 : ℕ))) M :=
    { toFun := fun g => (ρ g).toAddMonoidHom.toZModLinearMap (l ^ (1 : ℕ))
      map_one' := by ext m; simp
      map_mul' := fun g h => by ext m; simp }
  have hρ' : ContAction ρ' := hρ
  obtain ⟨hNT, -⟩ := hall S hS Av hAv μ hμ M ρ' hρ'
  have hc' : ∀ φ : M →+ ZMod (l ^ (1 : ℕ)), (∀ g h m, φ (ρ' g (ρ' h m)) = φ (ρ' h (ρ' g m))) → φ = 0 :=
    fun φ hφ => hcomm (ZMod (l ^ (1 : ℕ))) φ hφ

  choose z hz using fun v => Submodule.Quotient.mk_surjective _ (x v)
  let z' : ∀ v : S, Z2 (ρ'.comp (locFam S Av v)) := fun v => ⟨(z v).1, (z v).2⟩

  obtain ⟨y', hy'⟩ := LinearMap.mem_range.1
    ((hNT.mem_range_localization_H2_iff (fun v => Submodule.Quotient.mk (z' v))).2 fun y => by
      rw [H0_twDual_eq_zero μ ρ' hc' y]
      simp)
  obtain ⟨w', hw'⟩ := Submodule.Quotient.mk_surjective _ y'
  let w : Z2 ρ := ⟨w'.1, w'.2⟩
  refine ⟨Submodule.Quotient.mk w, fun v => ?_⟩
  have hv := congrFun hy' v
  rw [← hw'] at hv
  change resH2 ρ' (locFam S Av v) (continuous_locFam S Av v) (Submodule.Quotient.mk w') =
    Submodule.Quotient.mk (z' v) at hv
  rw [resH2, Submodule.mapQ_apply, Submodule.Quotient.eq] at hv
  rw [← hz v, resH2, Submodule.mapQ_apply, Submodule.Quotient.eq]
  simp only [Submodule.mem_comap, Submodule.coe_subtype] at hv ⊢

  obtain ⟨c, hc, hcd⟩ := (separated_dvr_second_cohomology_mem _ _).1 hv
  refine (separated_dvr_second_cohomology_mem _ _).2 ⟨c, hc, ?_⟩
  funext p
  have hp := congrFun hcd p
  exact hp

end GlobalTheory.LocTwoOnto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1LatticeIndexGrowth
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.EulerLevel

theorem card_H2_eq (N : ℕ) [NeZero N] (G : Type) [Group G] [TopologicalSpace G]
    (M : Type) [AddCommGroup M] [Module (ZMod N) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (χ : G →* (ZMod N)ˣ) (rho : Representation (ZMod N) G M)
    (e : ReciprocityTheory.Gal.H2 (ReciprocityTheory.Gal.charRep χ) ≃ₗ[ZMod N] ZMod N)
    (hb : Function.Bijective (ReciprocityTheory.Gal.cup20 χ rho (MonoidHom.id _))) :
    Nat.card (ReciprocityTheory.Gal.H2 rho) = Nat.card (ReciprocityTheory.Gal.H0 (ReciprocityTheory.Gal.twDual χ rho)) := by
  have hT := GlobalTheory.CocycleCount.card_linear_le N M
  have hTf : Finite (ReciprocityTheory.Gal.TDual (ZMod N) M) := hT.1
  let A : Type := ReciprocityTheory.Gal.H0 ((ReciprocityTheory.Gal.twDual χ rho).comp (MonoidHom.id G))
  let E : ReciprocityTheory.Gal.H2 rho ≃ (A →ₗ[ZMod N] ZMod N) :=
    (Equiv.ofBijective _ hb).trans (LinearEquiv.congrRight e).toEquiv
  have hA : Finite A := Subtype.finite
  rw [Nat.card_congr E]
  exact GlobalTheory.ZModDual.card_dual_eq N A


set_option maxHeartbeats 1600000 in
theorem core_pos (hT : Formalism.GaloisCohomology.LocalTateDualityK) (hE : Formalism.GaloisCohomology.LocalEulerCharK) (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (hG : GoodO (Qp := ℚ_[l]) LL O) (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL) (hm : IsDualLat1 (P.PD K) LA LA' m) (r : ℕ) (hr : 0 < r) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T))
    (M : Type) [AddCommGroup M] (tM : TopologicalSpace M) (dM : @DiscreteTopology M tM) (e : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) ≃+ M) :
    Nat.card (QuotientCohomology LA _ hI) = Nat.card {x : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) // ∀ g, actQ LA _ hI g x = x} * Nat.card {x : (↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) // ∀ g, actQ LA' _ hI' g x = x} * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * (finrank ℚ_[l] ↥K.1 * finrank LL A.V)) := by
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hp : l.Prime := Fact.out
  obtain ⟨-, -, hfinO, -⟩ := GlobalTheory.GoodCoeff.good_coeff_integers l LL O hG
  have hcO : Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ≠ 0 := by
    have := hfinO 1
    rw [pow_one] at this
    exact Nat.card_pos.ne'
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcM : Nat.card M = Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL A.V) := by
    rw [← Nat.card_congr e.toEquiv]
    exact GlobalTheory.T.card_lattice_quot_prime_pow l _ LL O hG A LA r
  have hcM' : Nat.card (↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) =
      Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL A.V) := by
    rw [GlobalTheory.T.card_lattice_quot_prime_pow l _ LL O hG A' LA' r, ← hm.1.2.2.2]
  haveI : Finite M := Nat.finite_of_card_ne_zero (by rw [hcM]; exact pow_ne_zero _ hcO)
  have htor : ∀ x : M, l ^ r • x = 0 := by
    intro x
    rw [← e.apply_symm_apply x, ← map_nsmul]
    generalize e.symm x = y
    induction y using Submodule.Quotient.induction_on with
    | H t =>
      rw [← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero _).2, map_zero]
      rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  haveI instM : Module (ZMod (l ^ r)) M := AddCommGroup.zmodModule htor
  let φ : ↥(GK K) ≃* Formalism.GaloisCohomology.GK l K.1 := IntermediateField.fixingSubgroupEquiv K.1
  have hφ : Continuous φ ∧ Continuous φ.symm :=
    GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  have hφ1 : φ.symm 1 = 1 := map_one _
  have hφm : ∀ g h, φ.symm (g * h) = φ.symm g * φ.symm h := map_mul _
  have hact1 : ∀ x : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), actQ LA _ hI 1 x = x := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H t =>
      exact congrArg Submodule.Quotient.mk (Subtype.ext (by
        show A.ρ 1 (t : A.V) = t
        rw [map_one]
        rfl))
  have hactm : ∀ (g h : ↥(GK K)) (x : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T))),
      actQ LA _ hI (g * h) x = actQ LA _ hI g (actQ LA _ hI h x) := by
    intro g h x
    induction x using Submodule.Quotient.induction_on with
    | H t =>
      exact congrArg Submodule.Quotient.mk (Subtype.ext (by
        show A.ρ (g * h) (t : A.V) = A.ρ g (A.ρ h t)
        rw [map_mul]
        rfl))
  have hex : ∃ rho : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K.1) M,
      ∀ (g : Formalism.GaloisCohomology.GK l K.1) (x : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T))), rho g (e x) = e (actQ LA _ hI (φ.symm g) x) :=
    ⟨GlobalTheory.CocycleCount.repOfAction _
      (fun g => e.toAddMonoidHom.comp ((actQ LA _ hI (φ.symm g)).toAddMonoidHom.comp e.symm.toAddMonoidHom))
      (fun x => by
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
          AddEquiv.coe_toAddMonoidHom, hφ1, hact1, AddEquiv.apply_symm_apply])
      (fun g h x => by
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
          AddEquiv.coe_toAddMonoidHom, hφm, hactm, AddEquiv.symm_apply_apply]),
      fun g x => congrArg (fun y => e (actQ LA _ hI (φ.symm g) y)) (e.symm_apply_apply x)⟩
  obtain ⟨rho, hcomp⟩ := hex
  have hrho : ReciprocityTheory.Gal.ContAction rho := by
    refine continuous_prod_of_discrete_right.2 fun x => ?_
    have hx : (fun g => rho g x) = fun g => e (actQ LA _ hI (φ.symm g) (e.symm x)) := by
      funext g
      rw [← hcomp, e.apply_symm_apply]
    rw [hx]
    exact ((GlobalTheory.T.lattice_modPow_action_isLocallyConstant l ↥(GK K) LL O hG A LA r hI (e.symm x)).comp e).continuous.comp hφ.2
  have hT1 := hT l K.1 hK r M rho hr hrho
  obtain ⟨⟨eH⟩, -, -, -, hb⟩ := hT1
  have hEu := hE l K.1 hK r M rho hr hrho
  have hTr := GlobalTheory.T.card_H1_H0_transport_lattice l K LL O A LA _ hI (l ^ r) M e rho hcomp
  obtain ⟨h1Q, h0Q⟩ := hTr
  have hTDfin : Finite (ReciprocityTheory.Gal.TDual (ZMod (l ^ r)) M) :=
    (GlobalTheory.CocycleCount.card_linear_le (l ^ r) M).1
  have hH2 := card_H2_eq (l ^ r) _ M _ rho eH hb
  have hD := GlobalTheory.T.exists_trace_form_integral_iff_goodCoeff l LL O hG
  obtain ⟨lam, hlam⟩ := hD
  have hMp := GlobalTheory.T.tracePairing_injective_equivariant_levelMap l P K LL O A A' LA LA' m hm lam hlam r hI hI' (_root_.GlobalTheory.CycLevel.chi_reduces l P K r) M e rho hcomp
  obtain ⟨Ψ, hΨi, hΨe⟩ := hMp
  have hcD : Nat.card (ReciprocityTheory.Gal.TDual (ZMod (l ^ r)) M) = Nat.card M :=
    GlobalTheory.ZModDual.card_dual_eq (l ^ r) M
  have hΨb : Function.Bijective Ψ :=
    hΨi.bijective_of_nat_card_le (by rw [hcD, hcM, hcM'])
  have hfix' : Nat.card {y : (↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) // ∀ g, actQ LA' _ hI' g y = y} =
      Nat.card (ReciprocityTheory.Gal.H0 (ReciprocityTheory.Gal.twDual (Formalism.GaloisCohomology.cycK l K.1 r) rho)) := by
    refine Nat.card_congr ((Equiv.ofBijective _ hΨb).subtypeEquiv fun y => ?_)
    rw [Equiv.ofBijective_apply, ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere]
    constructor
    · intro hy g
      exact (hΨe g y).symm.trans (congrArg Ψ (hy _))
    · intro hy g
      have h := hΨe (φ g) y
      have h2 : (IntermediateField.fixingSubgroupEquiv K.1).symm (φ g) = g := φ.symm_apply_apply g
      rw [h2, hy (φ g)] at h
      exact hΨb.1 h
  rw [h1Q, hEu, ← h0Q, hH2, ← hfix', hcM, ← pow_mul]
  rw [show r * finrank LL A.V * finrank ℚ_[l] ↥K.1 = r * (finrank ℚ_[l] ↥K.1 * finrank LL A.V) by ring]

theorem card_H1Q_eq : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)), Nat.card (QuotientCohomology LA _ hI) = Nat.card {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} * Nat.card {x : ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T) // ∀ g, actQ LA' _ hI' g x = x} * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * (finrank ℚ_[l] ↥K.1 * finrank LL A.V)) := by
  intro hT hE l _ P K LL _ _ _ O _ _ hG A A' LA LA' m hm r hI hI'
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hp : l.Prime := Fact.out
  obtain ⟨-, -, hfinO, -⟩ := GlobalTheory.GoodCoeff.good_coeff_integers l LL O hG
  have hcO : Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ≠ 0 := by
    have := hfinO 1
    rw [pow_one] at this
    exact Nat.card_pos.ne'
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hs : ∀ (X : Type) [AddCommGroup X] [Module O X],
        Subsingleton (X ⧸ (Ideal.span {((l : ℕ) : O) ^ 0} • ⊤ : Submodule O X)) := by
      intro X _ _
      rw [Submodule.Quotient.subsingleton_iff, pow_zero, Ideal.span_singleton_one, Submodule.top_smul]
    haveI := hs ↥LA.T
    haveI := hs ↥LA'.T
    have e1 : Nat.card (QuotientCohomology LA _ hI) = 1 := by
      haveI : Subsingleton (QuotientCohomology LA _ hI) := (Submodule.Quotient.mk_surjective _).subsingleton
      exact Nat.card_unique
    have e2 : Nat.card {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ 0} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} = 1 := by
      haveI : Unique {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ 0} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} :=
        { default := ⟨0, fun g => map_zero _⟩, uniq := fun _ => Subsingleton.elim _ _ }
      exact Nat.card_unique
    have e3 : Nat.card {x : ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ 0} • ⊤ : Submodule O ↥LA'.T) // ∀ g, actQ LA' _ hI' g x = x} = 1 := by
      haveI : Unique {x : ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ 0} • ⊤ : Submodule O ↥LA'.T) // ∀ g, actQ LA' _ hI' g x = x} :=
        { default := ⟨0, fun g => map_zero _⟩, uniq := fun _ => Subsingleton.elim _ _ }
      exact Nat.card_unique
    simp only [e1, e2, e3]
    simp
  · exact core_pos hT hE l P K LL O hG A A' LA LA' m hm r hr hI hI' _ ⊥ (@DiscreteTopology.mk _ ⊥ rfl) (AddEquiv.refl _)

end GlobalTheory.EulerLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1LatticeRankGrowthStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H1_lattice_rank_growth_of_goodO : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), Module.Finite O (LatticeCohomology LA) → Module.Finite LL (H1V A.ρ) ∧ ∃ C : ℕ, 0 < C ∧ ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL (H1V A.ρ)) ≤ Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ∧ Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ≤ C * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL (H1V A.ρ)) := by
  first | exact @GlobalTheory.H1Rank.growth_H1T_dim_H1V | exact GlobalTheory.H1Rank.growth_H1T_dim_H1V | (intros; apply GlobalTheory.H1Rank.growth_H1T_dim_H1V <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelTransportEquiv
section
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT
open Polynomial CategoryTheory

noncomputable section

namespace GlobalTheory.SerOSys.TranspLabel

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def permGL {α : Type} [Fintype α] [DecidableEq α] (π : α ≃ α) : GL α K :=
  ⟨π.symm.toPEquiv.toMatrix, π.toPEquiv.toMatrix, by
    rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j; simp [PEquiv.toMatrix_apply, Matrix.one_apply], by
    rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j; simp [PEquiv.toMatrix_apply, Matrix.one_apply]⟩

theorem glEquiv_perm {α : Type} [Fintype α] [DecidableEq α] (π : α ≃ α) (g : GL α K) :
    glEquiv K π g = permGL π * g * (permGL π)⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show Matrix.reindex π π (g : Matrix α α K) =
    π.symm.toPEquiv.toMatrix * (g : Matrix α α K) * π.toPEquiv.toMatrix
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl

def repIsoOf {G : Type} [Group G] (V W : FDRep ℂ G) (L : (V : Type) ≃ₗ[ℂ] (W : Type))
    (h : ∀ g v, L (V.ρ g v) = W.ρ g (L v)) : V ≅ W :=
  Action.mkIso (LinearEquiv.toFGModuleCatIso L) (fun g => by
    ext v
    exact h g v)

def rhoEquiv {G : Type} [Group G] (σ : FDRep ℂ G) (P : G) : (σ : Type) ≃ₗ[ℂ] (σ : Type) :=
  LinearEquiv.ofLinear (σ.ρ P) (σ.ρ P⁻¹)
    (LinearMap.ext fun v => by
      show (σ.ρ P * σ.ρ P⁻¹) v = v
      rw [← map_mul, mul_inv_cancel, map_one]; rfl)
    (LinearMap.ext fun v => by
      show (σ.ρ P⁻¹ * σ.ρ P) v = v
      rw [← map_mul, inv_mul_cancel, map_one]; rfl)

theorem rho_conj {G : Type} [Group G] (σ : FDRep ℂ G) (P X : G) (w : (σ : Type)) :
    σ.ρ P (σ.ρ X w) = σ.ρ (P * X * P⁻¹) (σ.ρ P w) := by
  rw [show σ.ρ (P * X * P⁻¹) (σ.ρ P w) = σ.ρ (P * X * P⁻¹ * P) w by rw [map_mul σ.ρ (P * X * P⁻¹) P]; rfl,
    inv_mul_cancel_right, map_mul]
  rfl

theorem lab_transp_transp {C : LabelConv K} (O : LabelMap K C) {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (σ : FDRep ℂ (GL α K)) (e : α ≃ β) (d : ℕ) (e₁ : α ≃ Fin d) (e₂ : β ≃ Fin d) :
    O.lab d (transp e₁ σ) = O.lab d (transp e₂ (transp e σ)) := by
  apply O.lab_iso
  let π : α ≃ α := e₁.trans (e.trans e₂).symm
  have hA : ∀ γ : GL (Fin d) K, (glEquiv K e).symm ((glEquiv K e₂).symm γ) =
      glEquiv K π ((glEquiv K e₁).symm γ) := by
    intro γ
    apply Units.ext
    ext i j
    simp [π, Formalism.L2.PT.coe_glEquiv_symm, Formalism.L2.PT.coe_glEquiv]
  refine ⟨repIsoOf _ _ (rhoEquiv σ (permGL π)) fun γ v => ?_⟩
  show σ.ρ (permGL π) (σ.ρ ((glEquiv K e₁).symm γ) v) =
    σ.ρ ((glEquiv K e).symm ((glEquiv K e₂).symm γ)) (σ.ρ (permGL π) v)
  rw [hA, glEquiv_perm]
  exact rho_conj σ _ _ v

theorem labO_transp {C : LabelConv K} (O : LabelMap K C) {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (σ : FDRep ℂ (GL α K)) :
    labO O (transp e σ) = labO O σ := by
  have key : ∀ (d : ℕ) (e₂ : β ≃ Fin d) (d' : ℕ) (e₁ : α ≃ Fin d'),
      O.lab d (transp e₂ (transp e σ)) = O.lab d' (transp e₁ σ) := by
    intro d e₂ d' e₁
    have hd : d = d' := by
      have h1 := Fintype.card_congr e₂
      have h2 := Fintype.card_congr e₁
      have h3 := Fintype.card_congr e
      simp only [Fintype.card_fin] at h1 h2
      omega
    subst hd
    exact (lab_transp_transp O σ e d e₁ e₂).symm
  exact key _ _ _ _

end GlobalTheory.SerOSys.TranspLabel

namespace GlobalTheory.SerOSys.TranspLabel

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

end GlobalTheory.SerOSys.TranspLabel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdeleLogAbsoluteValueEqLogIdeleModule
section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.IdeleLogNormCompare

open GroundTheory.Global GroundTheory.Global.IdeleGroup GlobalTheory.Mem.Chr.CharModel

variable (E : Type) [Field E] [NumberField E]

theorem ord_eq_ord_vw (d : (AdeleRing (𝓞 E) E)ˣ) (v : HeightOneSpectrum (𝓞 E)) :
    GroundTheory.Global.IdeleGroup.ord v d = GlobalTheory.Idele.ord_vw (finPart E d) v := rfl

theorem logInf_eq (d : (AdeleRing (𝓞 E) E)ˣ) :
    logInf E (infPart E d) = Real.log (infiniteModule d) := by
  rw [infiniteModule, Real.log_prod]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [Real.log_pow]
    rfl
  · intro w _
    exact pow_ne_zero _ (norm_ne_zero_iff.2 (infinite_ne_zero d w))

theorem logFin_eq (d : (AdeleRing (𝓞 E) E)ˣ) :
    logFin E (finPart E d) = -Real.log (finiteModule d) := by
  classical
  have hfin := Filter.eventually_cofinite.1 (GlobalTheory.Idele.ord_vw_eventually_zero (finPart E d))
  let S := hfin.toFinset
  have hS : ∀ v, v ∉ S → GlobalTheory.Idele.ord_vw (finPart E d) v = 0 := by
    intro v hv
    by_contra h
    exact hv (hfin.mem_toFinset.2 h)
  have hI : GlobalTheory.Idele.idealOf (finPart E d) =
      ∏ v ∈ S, (v.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ^ GlobalTheory.Idele.ord_vw (finPart E d) v := by
    unfold GlobalTheory.Idele.idealOf
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra h
    exact hv (by show (v.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ^ GlobalTheory.Idele.ord_vw (finPart E d) v = 1
                 rw [hS v h, zpow_zero])
  have hM : finiteModule d = ∏ v ∈ S, ‖(d : AdeleRing (𝓞 E) E).2 v‖ := by
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra h
    refine hv ?_
    change ‖(d : AdeleRing (𝓞 E) E).2 v‖ = 1
    rw [norm_finite_eq_rpow, ord_eq_ord_vw, hS v h, Int.cast_zero, neg_zero, Real.rpow_zero]
  have hN : ∀ v : HeightOneSpectrum (𝓞 E), (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 :=
    fun v => (absNorm_asIdeal_pos v).ne'
  rw [logFin, hI, hM, map_prod, Rat.cast_prod, Real.log_prod, Real.log_prod, ← Finset.sum_neg_distrib]
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow, Rat.cast_natCast, Real.log_zpow,
      norm_finite_eq_rpow, Real.log_rpow (absNorm_asIdeal_pos v), ord_eq_ord_vw]
    ring
  · intro v _
    exact norm_ne_zero_iff.2 (finite_ne_zero d v)
  · intro v _
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow, Rat.cast_natCast]
    exact zpow_ne_zero _ (hN v)

theorem logNorm_eq_log_ideleModule (d : (AdeleRing (𝓞 E) E)ˣ) :
    logNorm E d = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E d : ℝ) := by
  rw [logNorm, logInf_eq, logFin_eq, ideleModule_apply,
    Real.log_mul (infiniteModule_pos d).ne' (finiteModule_pos d).ne']
  ring

end GlobalTheory.IdeleLogNormCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfIsConjPl
section
noncomputable section

open GlobalTheory.TwSys Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.ConjugatePlaceSplitting

theorem isSplitPl_of_isConjPl {D : D7} {P P' : PlE D.host} (hs : IsSplitPl D.host P)
    (hc : IsConjPl D.host P P') : IsSplitPl D.host P' := by
  obtain ⟨x, hx, hy⟩ := hs
  have hc' := GlobalTheory.TwistDet.isConjPl_iff.1 hc
  have h1 : GlobalTheory.TwistDet.conjInt D x ∈ P'.asIdeal := (hc' x).1 hx
  have h2 : x ∉ P'.asIdeal := fun h => hy (GlobalTheory.TwistDet.conjInt D x) rfl
    ((hc' (GlobalTheory.TwistDet.conjInt D x)).2 (by rwa [GlobalTheory.TwistDet.conjInt_conjInt]))
  refine ⟨GlobalTheory.TwistDet.conjInt D x, h1, fun y hy' => ?_⟩
  have : y = x := by
    rw [← GlobalTheory.TwistDet.conjInt_conjInt x]
    exact RingOfIntegers.ext hy'
  rwa [this]

end GlobalTheory.ConjugatePlaceSplitting
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowPrimeMemUnitFiltrationUnitsMinStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_prime_mem_unitFiltrationUnits_min : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p e n : ℕ), OrdIs F p e → ∀ x ∈ unitFiltrationUnits F n, x ^ p ∈ unitFiltrationUnits F (min (2 * n) (n + e)) := by
  first | exact @GlobalTheory.PMon.Ram.pow_mem_unitFiltrationUnits | exact GlobalTheory.PMon.Ram.pow_mem_unitFiltrationUnits | (intros; apply GlobalTheory.PMon.Ram.pow_mem_unitFiltrationUnits <;> assumption)
end

