module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0798
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0795
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0765
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1110
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0758
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleCharacterGoodIdempotentCuspidalProduc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0759
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.ExpDefs
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0696

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeries
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SpecFac

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fock

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem pureTensorO_add (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    {f f' : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') (P : PolF D T.rank S.rank) :
    pureTensorO ψ θ S T sS sT BS BT (f + f') P =
      pureTensorO ψ θ S T sS sT BS BT f P + pureTensorO ψ θ S T sS sT BS BT f' P := by
  have hA : ∀ k g, IsThetaFunO ψ S T g →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k g) :=
    fun k g hg => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ hg
  have hl : ∀ l : List (FVar D T.rank S.rank),
      l.foldr (fun i g => aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g) (f + f') =
        l.foldr (fun i g => aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g) f +
        l.foldr (fun i g => aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g) f' ∧
      IsThetaFunO ψ S T (l.foldr (fun i g => aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g) f) ∧
      IsThetaFunO ψ S T (l.foldr (fun i g => aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g) f') := by
    intro l
    induction l with
    | nil => exact ⟨rfl, hf, hf'⟩
    | cons i l ih =>
      simp only [List.foldr_cons]
      refine ⟨?_, hA i _ ih.2.1, hA i _ ih.2.2⟩
      rw [ih.1]
      exact GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ ih.2.1 ih.2.2
  have e : pureTensorO ψ θ S T sS sT BS BT (f + f') =
      pureTensorO ψ θ S T sS sT BS BT f + pureTensorO ψ θ S T sS sT BS BT f' := by
    refine (MvPolynomial.basisMonomials _ ℂ).ext fun k => ?_
    simp only [pureTensorO, pureTensorL, LinearMap.add_apply, Module.Basis.constr_basis, opPow]
    exact (hl _).1
  rw [e, LinearMap.add_apply]

theorem theta_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → WO S T → ℂ) (hf : ∀ a ∈ s, IsThetaFunO ψ S T (f a)) :
    IsThetaFunO ψ S T (∑ a ∈ s, c a • f a) :=
  Finset.sum_induction _ (IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add) GlobalTheory.OrientedHeis.theta_zero
    fun a ha => GlobalTheory.OrientedHeis.theta_smul _ (hf a ha)

theorem pureTensorO_sum (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → WO S T → ℂ) (hf : ∀ a ∈ s, IsThetaFunO ψ S T (f a))
    (P : PolF D T.rank S.rank) :
    pureTensorO ψ θ S T sS sT BS BT (∑ a ∈ s, c a • f a) P = ∑ a ∈ s, c a • pureTensorO ψ θ S T sS sT BS BT (f a) P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    have := GlobalTheory.FiniteFock.pureTensorO_smul ψ θ S T sS sT BS BT 0 0 P
    rwa [zero_smul, zero_smul] at this
  | insert a s ha ih =>
    have hs : ∀ x ∈ s, IsThetaFunO ψ S T (f x) := fun x hx => hf x (Finset.mem_insert_of_mem hx)
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      pureTensorO_add hψ hθ sS BS sT BT (GlobalTheory.OrientedHeis.theta_smul _ (hf a (Finset.mem_insert_self a s)))
        (theta_sum s c f hs) P,
      GlobalTheory.FiniteFock.pureTensorO_smul, ih hs]

theorem series_sum {B : Base S T} (hB : B.Good) (ω : PairRep S T) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (f : ι → WO S T → ℂ) (hf : ∀ a ∈ s, IsThetaFunO B.F.ψ S T (f a)) (h : GA D S) (P : PolF D T.rank S.rank) (g : GA D T) :
    series B.F ω (∑ a ∈ s, c a • f a) h P g = ∑ a ∈ s, c a * series B.F ω (f a) h P g := by
  simp only [series_apply, Frame.fock]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [pureTensorO_sum hB.frame.vac.1 hB.frame.vac.2.inf _ _ _ _ s c f hf P, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul]

end Fock

section Spec

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem coef_add (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (a a' : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) :
    ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) (a + a'))) : X.Ok i k) =
      ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a)) : X.Ok i k) *
        ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a')) : X.Ok i k) := by
  rw [map_add (f := _), ofAdd_add, map_mul, Units.val_mul, map_mul]


open Classical in
theorem coef_prod (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (a : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) :
    ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a)) : X.Ok i k) =
      ∏ PP, ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) (Pi.single PP (a PP)))) : X.Ok i k) := by
  have e : a = ∑ PP, Pi.single PP (a PP) := (Finset.univ_sum_single a).symm
  conv_lhs => rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ofAdd_sum, map_prod, Units.coe_prod, map_prod]


open Classical in
theorem locFn_specLoc (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) :
    (ρ.B i j b).locFn (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) (specLoc ρ Y i j b k Q M χ) =
      ∑ a, ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a)) : X.Ok i k) •
        (ρ.B i j b).locFn (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) (fun PP y =>
          ((Base.univFam (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (ρ.β j) PP.1 (a PP) y : ℚ) : ℂ)) := by
  funext y
  simp only [Base.locFn, specLoc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.prod_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [coef_prod ρ Y i b k Q M χ a, Finset.prod_mul_distrib]
  ring


open Classical in
theorem vecAt_specLoc (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) :
    (ρ.B i j b).vecAt (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) (specLoc ρ Y i j b k Q M χ) =
      ∑ a, ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a)) : X.Ok i k) •
        (ρ.B i j b).vecFam (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) (Base.univFam (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (ρ.β j)) a := by
  rw [Base.vecAt, locFn_specLoc]
  change (ρ.B i j b).F.vecL (ρ.B i j b).G _ _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul]
  rfl

theorem coord_open (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (Q : Finset (Pl D.host.E)) (M : ℕ) (P : Pl D.host.E) :
    IsOpen ((coord Y i Q M P).ker : Set (G D.host.E N.Om)) := by
  unfold coord
  split_ifs
  · exact Subgroup.isOpen_mono (H₁ := (Y.delU i Q M).ker)
      (fun g hg => by rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hg, map_one])
      (Y.delU_open i Q M)
  · rw [MonoidHom.ker_one]
    exact isOpen_univ

theorem detChar_tw {ρ : Setup X} (hρ : ρ.Good) {Y : NExp D.R D.host D.what₂ D.LL0 N X} (hY : GlobalTheory.UnivChar.IsUnivChar Y)
    (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) (hχ : TwOK i k Q (χ.comp (Y.delU i Q M)))
    (g : GA D (Wc D j)) :
    ((detChar (Wc D j) (ρ.tw i b k Q (χ.comp (Y.delU i Q M))).chi g : Circle) : ℂ) =
      ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) (Multiplicative.toAdd
        (detChar (Wc D j) ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) g)))) :
          X.Ok i k) := by
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym (detRoot (Wc D j) g)
  have hker : IsOpen ((χ.comp (Y.delU i Q M)).ker : Set (G D.host.E N.Om)) :=
    Subgroup.isOpen_mono (H₁ := (Y.delU i Q M).ker)
      (fun g hg => by rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hg, map_one]) (Y.delU_open i Q M)
  have hn : X.l i ^ M ≠ 0 := NeZero.ne _
  have hpow : (χ.comp (Y.delU i Q M)) σ ^ (X.l i ^ M) = 1 := by
    rw [MonoidHom.comp_apply, ← map_pow]
    have e : Y.delU i Q M σ ^ (X.l i ^ M) = 1 := by
      apply Multiplicative.toAdd.injective
      funext v
      rw [toAdd_pow, toAdd_one, Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]
      rfl
    rw [e, map_one]
  have hd : Multiplicative.toAdd
      (detChar (Wc D j) ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) g) =
        fun P => Multiplicative.toAdd (coord Y i (admissibleConjugatePairPlaces X i Q M) M P.1 σ) := by
    funext PP
    change Multiplicative.toAdd (ρ.rc.pull (coord Y i (admissibleConjugatePairPlaces X i Q M) M PP.1) (detRoot (Wc D j) g)) = _
    rw [ρ.rc.pull_eq (coord_open Y i _ M PP.1) hσ]
  change ((charOf ρ.rc (ρ.eOk i b k) (χ.comp (Y.delU i Q M)) (detRoot (Wc D j) g) : Circle) : ℂ) = _
  rw [charOf_eq ρ.rc (ρ.eOk i b k) hker hσ hn hpow, hd, MonoidHom.comp_apply,
    ← ofAdd_toAdd (Y.delU i Q M σ), delU_eq_spread hY (twSet_of_twOK hχ) (hρ.ch i) σ]

end Spec

theorem specXi_eq_specSer : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (ρ : Setup X), ρ.Good →
  ∀ (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y →
  ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    TwOK i k Q (χ.comp (Y.delU i Q M)) →
    ∀ (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      specXi ρ Y i j b k Q M χ h P = specSer ρ Y i j b k Q M χ h P := by
  intro D N X ρ hρ Y hY i j b k Q M χ hχ h P
  classical
  funext g
  have hB := hρ.base i j b
  have hadm : (ρ.B i j b).admitted (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) :=
    GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint D N X ρ hρ i j b _ (fun _ h => isSplit_of_mem_admissibleConjugatePairPlaces h)
      (hχ.2.1.mono_left (admissibleConjugatePairPlaces_subset i Q M))
  have htheta : ∀ a ∈ (Finset.univ : Finset (↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M))),
      IsThetaFunO (ρ.B i j b).F.ψ (Vc D j) (Wc D j) ((ρ.B i j b).vecFam (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))
        (Base.univFam (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (ρ.β j)) a) := fun a _ => by
    have := Base.isThetaFunO_fock_vecAt hB hadm (fun PP y =>
      ((Base.univFam (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (ρ.β j) PP.1 (a PP) y : ℚ) : ℂ)) 1
    rwa [Frame.fock, GlobalTheory.FiniteFock.pureTensorO_one] at this
  unfold specSer
  rw [twistBy_apply, vecAt_specLoc, series_sum hB _ _ _ _ htheta, detChar_tw hρ hY i j b k Q M χ hχ g]
  unfold specXi
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Setup.xi, Base.xiCoef_apply]
  rw [← Equiv.sum_comp (Equiv.addRight (Multiplicative.toAdd (detChar (Wc D j)
    ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) g))), Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Equiv.coe_addRight, add_sub_cancel_right, coef_add]
  ring

end GlobalTheory.SpecFac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SqSmulMulVecMemHat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HatIntSmul

theorem mem_stdLat_coord {E : Type} [Field E] [NumberField E] {n : ℕ} {s : Fin n → E}
    (hs : s ∈ Formalism.L2.Pj.stdLat E n) (j : Fin n) : ∃ o : 𝓞 E, s j = (o : E) := by
  have := (Submodule.mem_pi.mp hs) j (Set.mem_univ _)
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp this
  exact ⟨o, ho.symm⟩

theorem single_mem_stdLat {E : Type} [Field E] [NumberField E] {n : ℕ} (i : Fin n) (o : 𝓞 E) :
    Pi.single i (o : E) ∈ Formalism.L2.Pj.stdLat E n := by
  refine Submodule.mem_pi.mpr fun j _ => ?_
  rw [Submodule.mem_one]
  by_cases h : j = i
  · subst h; exact ⟨o, by simp⟩
  · exact ⟨0, by simp [Pi.single_apply, h]⟩

theorem nsmul_tmul {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
    (a : ℕ) (β : Af F) (x : E) : a • (β ⊗ₜ[F] x) = β ⊗ₜ[F] (((a : 𝓞 E) : E) * x) := by
  have h := map_nsmul (TensorProduct.mk F (Af F) E β) a x
  simp only [TensorProduct.mk_apply] at h
  rw [← h, nsmul_eq_mul]
  simp


set_option maxHeartbeats 2000000 in
theorem sq_smul_mulVec_mem_hat : ∀ (D : D7) (n : ℕ) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (a : ℕ), (∀ x ∈ Formalism.L2.Pj.stdLat D.host.E n, (a : 𝓞 D.host.E) • x ∈ Λ) → (∀ x ∈ Λ, (a : 𝓞 D.host.E) • x ∈ Formalism.L2.Pj.stdLat D.host.E n) → ∀ (M : Matrix (Fin n) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)), (∀ i j, M i j ∈ intAE D) → ∀ y ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)), (a ^ 2) • (M *ᵥ y) ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) := by
  intro D n Λ a h1 h2 M hM y hy
  have mulMem : ∀ {x y : Af D.host.F ⊗[D.host.F] D.host.E}, x ∈ intAE D → y ∈ intAE D → x * y ∈ intAE D := by
    intro x y hx hy
    refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
    · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
      refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
      · rw [map_mul]; exact mul_mem (ha w) (hb w)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
    · intro x _; rw [zero_mul]; exact zero_mem _
    · intro x _; rw [mul_zero]; exact zero_mem _
    · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
    · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
    · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
    · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

  have stepA : ∀ w : Fin n → Af D.host.F ⊗[D.host.F] D.host.E, (∀ i, w i ∈ intAE D) →
      a • w ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) := by
    intro w hw
    have hw' : a • w = ∑ i, a • Pi.single i (w i) := by
      rw [← Finset.smul_sum, Finset.univ_sum_single]
    rw [hw']
    refine sum_mem fun i _ => ?_
    have key : ∀ z ∈ intAE D, a • Pi.single i z ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) := by
      intro z hz
      induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨β, hβ, o, rfl⟩ := hz
        apply AddSubgroup.subset_closure
        refine ⟨β, fun v => hβ v, (a : 𝓞 D.host.E) • Pi.single i (o : D.host.E), h1 _ (single_mem_stdLat i o), ?_⟩
        funext k
        by_cases hk : k = i
        · subst hk
          rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, nsmul_tmul, Algebra.smul_def]
        · simp [Pi.single_apply, hk]
      | zero => simp
      | add x y _ _ hx hy => rw [Pi.single_add, smul_add]; exact add_mem hx hy
      | neg x _ hx => rw [Pi.single_neg, smul_neg]; exact neg_mem hx
    exact key _ (hw i)
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hz
    obtain ⟨o, ho⟩ := Classical.axiomOfChoice (mem_stdLat_coord (h2 x hx))
    have e : (a ^ 2) • (M *ᵥ fun i => α ⊗ₜ[D.host.F] x i) =
        a • (M *ᵥ fun j => α ⊗ₜ[D.host.F] ((o j : 𝓞 D.host.E) : D.host.E)) := by
      rw [pow_two, mul_smul, ← Matrix.mulVec_smul]
      congr 2
      funext j
      rw [Pi.smul_apply, nsmul_tmul, ← ho j]
      simp [Algebra.smul_def]
    rw [e]
    refine stepA _ fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    refine sum_mem fun j _ => mulMem (hM i j) (AddSubgroup.subset_closure ⟨α, fun v => hα v, o j, rfl⟩)
  | zero => simp
  | add y z _ _ hy hz => rw [Matrix.mulVec_add, smul_add]; exact add_mem hy hz
  | neg y _ hy => rw [Matrix.mulVec_neg, smul_neg]; exact neg_mem hy

end GlobalTheory.HatIntSmul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableGoodFormsMeetGenericType
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.MeetsGen.exists_right_inv_generic_central_projector : ∀ (D : D7), GrpSide D → ∀ [Fintype (G0g D.nd)]
    (U : Subgroup (G0g D.nd)) [Fintype U],
    U = Formalism.L2.NX.Uup (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r →
    ∀ ψ : U →* ℂˣ, Formalism.L2.NX.IsStdGeneric (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r ψ →
    2 ≤ D.R.r → ∃ v : MonoidAlgebra ℂ (G0g D.nd),
      GlobalTheory.MeetsGen.uElt U (fun u => (((ψ u)⁻¹ : ℂˣ) : ℂ)) D.ntypes.e0 * v = 1 := by
  intro D S _ U _ hU ψ hψ hr
  obtain ⟨hc, hi⟩ := GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent D
  exact _root_.GlobalTheory.MeetsUnit.exists_rightInv_uElt U ψ D.ntypes.e0 hi (fun a => ((Subalgebra.mem_center_iff.mp hc) a).symm)
    (_root_.GlobalTheory.WhittakerMeets.sum_ne_zero D S U hU ψ hψ hr)


open GlobalTheory.MeetsGen in
theorem GlobalTheory.TwInputs.meetsAll_of_ties : GlobalTheory.Published.GreenCuspidal → ∀ (D : D7), NExpTied D → GrpSide D → MeetsAll D := by
  intro hG D T S i j b W hW hst hfix
  classical
  by_cases hr : D.R.r ≤ 1
  · have hFm0 : Fm0 D.nexp i j b = ⊤ := by
      rw [eq_top_iff]
      intro x _
      simp only [Fm0, Submodule.mem_iInf, LinearMap.mem_ker]
      intro u
      have hu1 : u = 1 := Subtype.ext (GlobalTheory.MeetsGen.uup_eq_one_of_le_one _ _ hr _ (T.U_eq ▸ u.2))
      subst hu1
      simp
    rw [hFm0, inf_top_eq]
    exact hW
  have hr : 2 ≤ D.R.r := by omega
  haveI : ∀ k : Fin 2, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  haveI : Fintype (G0g D.nd) := Fintype.ofFinite _
  haveI : Fintype D.nexp.U := Fintype.ofFinite _
  obtain ⟨θ, hθ, hψ⟩ := T.psiU_gen i b
  let s : ↥D.LL0 →+* FractionRing (D.ntw.O i) :=
    (IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
      (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i)).comp (if b then D.ntw.emb0 i else D.ntw.emb0b i)
  let t : ↥D.LL0 →+* ℂ := D.what₂.embLL.comp D.LL0.val.toRingHom
  let Z : Set (FractionRing (D.ntw.O i)) :=
    {z | ∃ (x : Σ k : Fin 2, D.nd.PlG k) (a : Multiplicative (ZMod (D.host.g x.1))), z = ((θ x a : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i))}
  have hZ : ∀ z ∈ Z, ∃ n : ℕ, 0 < n ∧ z ^ n = 1 := by
    rintro z ⟨x, a, rfl⟩
    haveI : NeZero (D.host.g x.1) := ⟨(D.host.g_prime x.1).ne_zero⟩
    refine ⟨Fintype.card (Multiplicative (ZMod (D.host.g x.1))), Fintype.card_pos, ?_⟩
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
  obtain ⟨E, jE, hsE, hZE, hj⟩ := GlobalTheory.T.exists_subfield_adjoin_rootsOfUnity_embedding_complex s t Z hZ

  let θE : ∀ x : (Σ k : Fin 2, D.nd.PlG k), Multiplicative (ZMod (D.host.g x.1)) →* Eˣ := fun x =>
    { toFun := fun a => ⟨⟨((θ x a : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)), hZE ⟨x, a, rfl⟩⟩,
        ⟨(((θ x a)⁻¹ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)), hZE ⟨x, a⁻¹, by simp⟩⟩,
        Subtype.ext (by simp), Subtype.ext (by simp)⟩
      map_one' := by ext; simp
      map_mul' := fun a a' => by ext; simp }
  have hθE : ∀ x a, (((θE x a : Eˣ) : E) : FractionRing (D.ntw.O i)) = ((θ x a : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) :=
    fun _ _ => rfl
  let θ' : ∀ x : (Σ k : Fin 2, D.nd.PlG k), Multiplicative (ZMod (D.host.g x.1)) →* ℂˣ :=
    fun x => (Units.map jE.toMonoidHom).comp (θE x)
  have hθ' : 2 ≤ D.R.r → ∀ x, θ' x ≠ 1 := by
    intro h x h1
    apply hθ h x
    refine MonoidHom.ext fun a => Units.ext ?_
    have h2 := congrArg (fun φ : Multiplicative (ZMod (D.host.g x.1)) →* ℂˣ => ((φ a : ℂˣ) : ℂ)) h1
    simp only [θ', MonoidHom.comp_apply, Units.coe_map, MonoidHom.one_apply, Units.val_one] at h2
    have h3 : ((θE x a : Eˣ) : E) = 1 := jE.injective (by rw [map_one]; exact h2)
    have h4 : (((θE x a : Eˣ) : E) : FractionRing (D.ntw.O i)) = 1 := by rw [h3]; rfl
    rw [MonoidHom.one_apply, Units.val_one]
    exact (hθE x a).symm.trans h4
  let ψ' : D.nexp.U →* ℂˣ := (Formalism.L2.NX.psiStd _ _ θ').comp (Subgroup.inclusion T.U_eq.le)
  have hψ' : Formalism.L2.NX.IsStdGeneric (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r ψ' :=
    ⟨θ', hθ', fun u => rfl⟩
  obtain ⟨vC, hvC⟩ := GlobalTheory.MeetsGen.exists_right_inv_generic_central_projector D S D.nexp.U T.U_eq ψ' hψ' hr

  have hψE : ∀ u : D.nexp.U, ((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) ∈ E := by
    intro u
    rw [hψ u]
    simp only [Formalism.L2.NX.stdVal, Units.coe_prod]
    exact E.prod_mem fun x _ => hZE ⟨x, _, rfl⟩
  let fE : D.nexp.U → E := fun u => ⟨(((D.nexp.psiU i b u)⁻¹ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)),
    by rw [Units.val_inv_eq_inv_val]; exact E.inv_mem (hψE u)⟩
  let eE : MonoidAlgebra E (G0g D.nd) :=
    MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun g => (⟨s (D.nexp.eLL0 g), hsE _⟩ : E))
  have hψval : ∀ u : D.nexp.U, jE ⟨((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)), hψE u⟩ =
      ((ψ' u : ℂˣ) : ℂ) := by
    intro u
    have e1 : (⟨((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)), hψE u⟩ : E) =
        ∏ x, ((θE x (Multiplicative.ofAdd (Formalism.L2.NX.supSum D.R.r
          (((u : G0g D.nd) x : GL (Fin D.R.r) (ZMod (D.host.g x.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g x.1))))) : Eˣ) : E) := by
      apply Subtype.ext
      simp only [SubmonoidClass.coe_finsetProd, hθE]
      rw [hψ u]
      simp [Formalism.L2.NX.stdVal, Units.coe_prod]
    rw [e1, map_prod]
    simp [ψ', Formalism.L2.NX.psiStd, Formalism.L2.NX.stdVal, θ', Units.coe_prod]
  have hC1 : MonoidAlgebra.mapRingHom (G0g D.nd) jE (uElt D.nexp.U fE eE) =
      uElt D.nexp.U (fun u => (((ψ' u)⁻¹ : ℂˣ) : ℂ)) D.ntypes.e0 := by
    rw [GlobalTheory.MeetsGen.map_uElt]
    congr 1
    · funext u
      have e2 : fE u = (⟨((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)), hψE u⟩ : E)⁻¹ :=
        Subtype.ext (by simp [fE])
      rw [e2, map_inv₀, hψval, Units.val_inv_eq_inv_val]
    · refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
      rw [MonoidAlgebra.coeff_mapRingHom]
      simp only [eE, MonoidAlgebra.coeff_ofCoeff, Finsupp.coe_equivFunOnFinite_symm]
      rw [hj, ← D.nStage_trivialCharacter_coeff_eq]
      rfl
  have hK1 : MonoidAlgebra.mapRingHom (G0g D.nd) E.subtype eE = D.nexp.eAlg i b := by
    refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
    rw [MonoidAlgebra.coeff_mapRingHom, D.nexp.eAlg_def]
    simp only [eE, MonoidAlgebra.coeff_ofCoeff, Finsupp.coe_equivFunOnFinite_symm]
    rfl
  obtain ⟨vE, hvE⟩ := _root_.GlobalTheory.groupAlgebra_exists_right_inv_of_map jE (uElt D.nexp.U fE eE) ⟨vC, by rw [hC1]; exact hvC⟩
  have hvK := congrArg (MonoidAlgebra.mapRingHom (G0g D.nd) E.subtype) hvE
  rw [map_mul, map_one, GlobalTheory.MeetsGen.map_uElt, hK1] at hvK
  have heq := GlobalTheory.MeetsGen.eq_sum_of_uElt_mul D.nexp.U _ (D.nexp.eAlg i b) _ (D.nexp.eAlg_idem i b) (D.nexp.eAlg_central i b) hvK
  exact _root_.GlobalTheory.MeetsTypeVec.meets (D.nexp.actG i j b) D.nexp.U (D.nexp.psiU i b) (D.nexp.eAlg i b) _ heq W hW
    (fun g x hx => hst g x hx) (fun x hx => hfix x hx)

end
end

