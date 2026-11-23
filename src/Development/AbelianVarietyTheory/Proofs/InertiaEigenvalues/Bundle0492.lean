module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LineOfSingleJump
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0374
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarizedGaloisRep
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0454
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0344
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftBlochKatoCocycleIffOrthogonalLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormConstantCoeffEqOneOfEisensteinFrobeniusCycle
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0433
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0447

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalTwistDual
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TwistRead

theorem matRep_apply {F Γ : Type} [CommRing F] [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) F)
    (g : Γ) (v : Fin k → F) : matRep M g v = (M g).mulVec v := by
  simp [matRep, Matrix.toLinAlgEquiv'_apply]

theorem local_twist_dual (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : LocTied l P AI)
    (K LL : FinExt l) (hs : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1) {n : ℕ}
    (R T U : ↥(GK K) →* Matrix (Fin n) (Fin n) ↥LL.1)
    (ν : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1)) (χ : ↥(GK K) → ↥LL.1)
    (hν : ∀ g x, ν g x = χ g • x) (hR : ∀ g, R g = χ g • T g)
    (hU : ∀ g, U g = ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1) • (T g⁻¹).transpose)
    (dR : IsDR (P.PD K) (matRep R)) (dν : IsDR (P.PD K) ν)
    (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (c : ℤ) (hc : ∀ a : ℤ, multV (P.PD K) ν τ a = if a = c then 1 else 0) :
    IsDR (P.PD K) (matRep T) ∧ IsDR (P.PD K) (matRep U) ∧
      ∀ a : ℤ, multV (P.PD K) (matRep T) τ a = multV (P.PD K) (matRep R) τ (a + c) ∧
        multV (P.PD K) (matRep U) τ a = multV (P.PD K) (matRep R) τ (c - a - 1) := by
  have hRT : ∀ g x, matRep R g x = χ g • matRep T g x := by
    intro g x
    rw [matRep_apply, matRep_apply, hR, Matrix.smul_mulVec]
  have dT : IsDR (P.PD K) (matRep T) :=
    (GlobalTheory.TwistDR.isDR_twist_iff l P AI hT K LL _ (matRep T) (matRep R) ν χ hν hRT dν).2 dR
  have jT : ∀ a : ℤ, multV (P.PD K) (matRep R) τ (a + c) = multV (P.PD K) (matRep T) τ a :=
    GlobalTheory.TwistJump.multV_twist_char l P AI hT K LL _ (matRep T) (matRep R) ν χ hν hRT dν τ c hc
  have hb : Function.Bijective (dotProductBilin ↥LL.1 ↥LL.1 :
      (Fin n → ↥LL.1) →ₗ[↥LL.1] (Fin n → ↥LL.1) →ₗ[↥LL.1] ↥LL.1) :=
    (dotProductEquiv ↥LL.1 (Fin n)).bijective
  have hd := _root_.GlobalTheory.DRDual.twisted_dual_deRham l P AI hT K LL _ (matRep T) _ (matRep U) _ 1 hb (by
    intro g x y
    rw [matRep_apply, matRep_apply, hU, zpow_one]
    simp only [dotProductBilin_apply_apply, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec, dotProduct_comm]) dT
  refine ⟨dT, hd.1, fun a => ⟨(jT a).symm, ?_⟩⟩
  have h1 := hd.2 τ (-a - 1) hs
  have h2 := jT (-a - 1)
  rw [show -(-a - 1) - 1 = a by ring] at h1
  rw [show -a - 1 + c = c - a - 1 by ring] at h2
  rw [h1, h2]


set_option maxHeartbeats 1000000 in
theorem twist_dual_mult : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), LocTied (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) → ∀ (LL' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ LL'.1) (τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) (τ : D.host.E →+* Qbar (D.nd.l i)), (∀ x : D.host.E, τ x = ((τ' (Br.cEw D.nbr i w hw x) : ↥LL'.1) : Om (D.nd.l i))) → ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) (χ : GE D.nd →* GL (Fin 1) (D.nd.O i)) (c : ℤ), Continuous (fun g => rO D.nd i r x g) → (∀ g, (χ g : Matrix (Fin 1) (Fin 1) (D.nd.O i)) 0 0 = ((D.nd.chi i 1 g : (D.nd.O i)ˣ) : D.nd.O i)) → D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w → D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) χ) w → D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) χ) τ = {c} → IsDR (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r x)))) ∧ IsDR (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rDuO D.nd i r x)))) ∧ ∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r x)))) τ' a = (((D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (r x)) τ).count (a + c) : ℕ) : ℤ) ∧ multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rDuO D.nd i r x)))) τ' a = (((D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (r x)) τ).count (c - a - 1) : ℕ) : ℤ) := by
  intro D i w hw hT LL' h τ' τ hτ r x χ c hr hχ dr dχ hc
  have tie := D.loc_tie i w hw
  set f : D.nd.O i →+* ↥LL'.1 :=
    (IntermediateField.inclusion h).toRingHom.comp (D.nbr i w hw).toLL with hf
  have hfc : Continuous f := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.comp (continuous_subtype_val.comp (D.nbr i w hw).eO_cont)
  have hmap : ∀ (m : ℕ) (ρ : GE D.nd →* GL (Fin m) (D.nd.O i)),
      mapRep (algebraMap ↥LL'.1 (Qbar (D.nd.l i))) (mapRep f ρ) = mapRep (iotaOQ D.nd D.naut i) ρ := by
    intro m ρ
    ext g a b
    exact (tie.1 _).symm
  have cr : Continuous (fun g => ((mapRep f (r x) g : GL (Fin D.R.nV) ↥LL'.1) :
      Matrix (Fin D.R.nV) (Fin D.R.nV) ↥LL'.1)) := hr.matrix_map hfc
  have cχ : Continuous (fun g => ((mapRep f χ g : GL (Fin 1) ↥LL'.1) : Matrix (Fin 1) (Fin 1) ↥LL'.1)) := by
    refine Continuous.matrix_map (A := fun g => (χ g : Matrix (Fin 1) (Fin 1) (D.nd.O i))) ?_ hfc
    refine continuous_matrix fun a b => ?_
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
    simp only [hχ]
    exact D.nd.chi_cont i 1
  have tr := tie.2.2 LL' h _ _ cr
  have tχ := tie.2.2 LL' h _ _ cχ
  rw [hmap] at tr tχ
  have dr' := tr.2.1.1 dr
  have dχ' := tχ.2.1.1 dχ
  have jr := (tr.2.2.2 τ τ' hτ).2 dr'
  have jχ := (tχ.2.2.2 τ τ' hτ).2 dχ'
  have hs : Nat.card (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) =
      Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 := by
    haveI : FiniteDimensional ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 := (D.nbr i w hw).Kw.2
    have := (GlobalTheory.splits_of_conjugates_mem _ (D.nbr i w hw).Kw LL'
      (fun σ y => h ((D.nbr i w hw).LL_split σ y)) inferInstance).2
    rw [Nat.card_eq_fintype_card]
    exact this
  let ι : Br.G D.nbr i w hw →* GE D.nd := (decS D.nd w).comp (Br.iota D.nbr i w hw)
  have hrep : matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rO D.nd i r x))) =
      (D.nbr i w hw).repE LL' ((mapRep f (r x)).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) := by
    refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
    rw [matRep_apply]
    rfl
  have key := local_twist_dual (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) hT (D.nbr i w hw).Kw LL' hs
    (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rO D.nd i r x)))
    (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r x)))
    (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rDuO D.nd i r x)))
    ((D.nbr i w hw).repE LL' ((mapRep f χ).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype))
    (fun g => f (D.nd.chi i 1 (ι g) : (D.nd.O i)ˣ))
    (by
      intro g v
      funext a
      change Matrix.mulVec ((χ (ι g) : Matrix (Fin 1) (Fin 1) (D.nd.O i)).map f) v a = _
      rw [Subsingleton.elim a 0]
      simp [Matrix.mulVec, dotProduct, hχ])
    (by
      intro g
      ext a b
      congr 1
      change f (rO D.nd i r x (ι g) a b) = f (D.nd.chi i 1 (ι g) : (D.nd.O i)ˣ) *
        f ((((D.nd.chi i 1 (ι g))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (ι g) a b)
      rw [← map_mul, Units.mul_inv_cancel_left])
    (by
      intro g
      have e := congrArg Units.val (GlobalTheory.CycBridge.locChi_epsU D i w hw g)
      have e' : f (epsU D.nd i (ι g) : (D.nd.O i)ˣ) =
          ((cycLL ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) ↥LL'.1 g : (↥LL'.1)ˣ) : ↥LL'.1) :=
        by
        have e2 := congrArg (IntermediateField.inclusion h) e
        exact e2.trans ((IntermediateField.inclusion h).commutes _)
      rw [← e']
      ext a b
      congr 1
      change f ((((D.nd.chi i 1 (ι g)) * epsU D.nd i (ι g) : (D.nd.O i)ˣ) : D.nd.O i) *
          rO D.nd i r x ((ι g)⁻¹ : GE D.nd) b a) = f (epsU D.nd i (ι g) : (D.nd.O i)ˣ) *
        f ((((D.nd.chi i 1 (ι g⁻¹))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (ι g⁻¹) b a)
      rw [← map_mul, map_inv ι g, map_inv (D.nd.chi i 1), inv_inv, Units.val_mul]
      congr 1
      ring)
    (by
      rw [hrep]
      unfold IsDR
      rw [Module.finrank_fin_fun]
      exact dr')
    (by
      unfold IsDR
      rw [Module.finrank_fin_fun]
      exact dχ')
    τ' c
    (by
      intro a
      refine (jχ a).symm.trans ?_
      rw [hc, Multiset.count_singleton]
      split_ifs <;> rfl)
  rw [hrep] at key
  refine ⟨key.1, key.2.1, fun a => ⟨?_, ?_⟩⟩
  · exact (key.2.2 a).1.trans (jr (a + c)).symm
  · exact (key.2.2 a).2.trans (jr (c - a - 1)).symm

end GlobalTheory.TwistRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisationCoefFieldFiniteRange
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.Proof.CoefField

theorem exists_coefField {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (ι : FractionRing O →+* Qbar l)
    (hι : ∀ z : ℤ_[l], ι (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) =
      algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) :
    ∃ K : IntermediateField ℚ_[l] (Qbar l), (∀ z, z ∈ K ↔ ∃ x, ι x = z) ∧ FiniteDimensional ℚ_[l] K ∧
      ∀ x : FractionRing O, ‖ι x‖ ≤ 1 ↔ x ∈ (algebraMap O (FractionRing O)).range := by
  classical
  let φ : O →+* Qbar l := ι.comp (algebraMap O (FractionRing O))
  have hφ : ∀ z : ℤ_[l], φ (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) := hι
  have hQ : ∀ q : ℚ_[l], algebraMap ℚ_[l] (Qbar l) q ∈ ι.fieldRange := by
    intro q
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[l]) q
    rw [map_div₀]
    refine div_mem ?_ ?_
    · exact ⟨_, hι a⟩
    · exact ⟨_, hι b⟩
  let K : IntermediateField ℚ_[l] (Qbar l) := ι.fieldRange.toIntermediateField hQ
  have hK : ∀ z, z ∈ K ↔ ∃ x, ι x = z := fun z => Iff.rfl
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ_[l] O).FG)
  let S : Set (Qbar l) := φ '' (s : Set O)
  have hint : ∀ x ∈ S, IsIntegral ℚ_[l] x := by
    rintro _ ⟨y, -, rfl⟩
    obtain ⟨p, hp, hy⟩ : IsIntegral ℤ_[l] y := Algebra.IsIntegral.isIntegral y
    refine ⟨p.map (algebraMap ℤ_[l] ℚ_[l]), hp.map _, ?_⟩
    have := congrArg φ hy
    rw [map_zero, Polynomial.hom_eval₂] at this
    have e : (algebraMap ℚ_[l] (Qbar l)).comp (algebraMap ℤ_[l] ℚ_[l]) = φ.comp (algebraMap ℤ_[l] O) :=
      RingHom.ext fun z => (hφ z).symm
    rw [Polynomial.eval₂_map, e]
    exact this
  have : Finite S := (s.finite_toSet.image φ).to_subtype
  have hfd : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] S) :=
    IntermediateField.finiteDimensional_adjoin hint
  have hle : K ≤ IntermediateField.adjoin ℚ_[l] S := by
    have hO : ∀ y : O, φ y ∈ IntermediateField.adjoin ℚ_[l] S := by
      intro y
      have hy : y ∈ Submodule.span ℤ_[l] (s : Set O) := hs ▸ Submodule.mem_top
      induction hy using Submodule.span_induction with
      | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x _ hx =>
        rw [Algebra.smul_def, map_mul, hφ]
        exact mul_mem (IntermediateField.algebraMap_mem _ _) hx
    rintro _ ⟨x, rfl⟩
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    rw [map_div₀]
    exact div_mem (hO a) (hO b)
  refine ⟨K, hK, ?_, fun x => (GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.mem_range_iff ι hι x).symm⟩
  have hge : IntermediateField.adjoin ℚ_[l] S ≤ K := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, -, rfl⟩
    exact ⟨_, rfl⟩
  have heq : K = IntermediateField.adjoin ℚ_[l] S := le_antisymm hle hge
  rw [heq]
  exact hfd

theorem coefField_range : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc), ∃ K : IntermediateField ℚ_[N.l i] (Qbar (N.l i)), (∀ z, z ∈ K ↔ ∃ x, A.iotaQ i x = z) ∧ FiniteDimensional ℚ_[N.l i] K ∧ ∀ x : FractionRing (N.O i), ‖A.iotaQ i x‖ ≤ 1 ↔ x ∈ (algebraMap (N.O i) (FractionRing (N.O i))).range := by
  intro R H what₂ N A i
  exact exists_coefField (A.iotaQ i) (A.iotaQ_alg i)

end GlobalTheory.Proof.CoefField

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisationPointEigenSystemMem
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.PointEigen

theorem genAt_iff_splitOut (D : D7) (i : D.nd.Loc) (v : PlE D.host) (k : ℕ) :
    GenAt D (D.nd.l i) (D.nd.Q i) v k ↔ (SplitOut D.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV) := by
  have hS : v ∈ D.nd.S i ↔ v ∈ placesS D (D.nd.l i) := by
    rw [D.nd.S_def]; rfl
  unfold SplitOut GenAt
  rw [hS]
  tauto

theorem ptSys_mem_eigSet : ∀ (D : D7) (M : MtFam D), AVTied D M → ∀ (i : D.nd.Loc) (x : D.nd.X i),
    ptSys D i x ∈ EigSet (M.loc i) (D.nd.l i) (D.nd.Q i) := by
  intro D M A i x
  refine ⟨fun v k h => ?_, ?_⟩
  · simp only [ptSys, if_neg h]
  · obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 (D.naut.typeV_ne i P)
    refine ⟨y, hy0, fun v k s ϖ hg hc hu => ?_⟩
    obtain ⟨hw, k1, k2⟩ := (genAt_iff_splitOut D i v k).1 hg
    simp only [ptSys, if_pos hg]
    exact (A.ptV i P x).1 hP v k s ϖ hw hc hu k1 k2 y hy

end GlobalTheory.PointEigen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBlochKatoQuotientPowIffReduction
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BKTorsionRed

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    {ρ : Representation LL G V}

theorem coboundary_mem_blochKato_cocycles (m : V) (hm : Continuous fun g => ρ g m) : (fun g => ρ g m - m) ∈ finiteCocycles PD ρ := by
  refine ⟨⟨?_, fun g h => ?_⟩, m ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
  · simp_rw [sub_eq_add_neg]
    exact hm.add continuous_const
  · simp only [map_mul, Module.End.mul_apply, map_sub]
    abel
  · simp [actVB, sub_tmul]

def latticeCoboundaryCocycle (L : Lattice (O := O) ρ) (hρ : ∀ m, Continuous fun g => ρ g m) (x : ↥L.T) : ↥(latticeCocycles L) :=
  ⟨fun g => ρ g x - x, Submodule.mem_inf.2 ⟨(coboundary_mem_blochKato_cocycles PD (x : V) (hρ x)).1,
    Submodule.mem_pi.2 fun g _ => L.T.sub_mem (L.stable g x x.2) x.2⟩⟩

theorem lattice_reduction_coboundary_mem_cocycles (L : Lattice (O := O) ρ) (hρ : ∀ m, Continuous fun g => ρ g m) (I : Submodule O ↥L.T)
    (hI : StableSub L I) (x : ↥L.T) :
    redT L I (latticeCoboundaryCocycle PD L hρ x) = LinearMap.pi (fun g => actQ L I hI g - LinearMap.id) (I.mkQ x) := by
  funext g
  simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, Submodule.mkQ_apply, actQ,
    Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub]
  rfl

theorem mem_HfQ_iff (L : Lattice (O := O) ρ) (hρ : ∀ m, Continuous fun g => ρ g m) (I : Submodule O ↥L.T)
    (hI : StableSub L I) (c : G → ↥L.T ⧸ I) :
    c ∈ HfQ PD L I hI ↔ ∃ a : ↥(latticeCocycles L), (a : G → V) ∈ finiteCocycles PD ρ ∧ c = redT L I a := by
  constructor
  · intro h
    obtain ⟨_, ⟨a0, ha0, rfl⟩, _, ⟨xb, rfl⟩, rfl⟩ := Submodule.mem_sup.1 h
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ xb
    refine ⟨a0 + latticeCoboundaryCocycle PD L hρ x, (finiteCocycles PD ρ).add_mem ha0.2 (coboundary_mem_blochKato_cocycles PD (x : V) (hρ x)), ?_⟩
    rw [map_add (f := _), lattice_reduction_coboundary_mem_cocycles PD L hρ I hI x]
    rfl
  · rintro ⟨a, ha, rfl⟩
    exact Submodule.mem_sup_left ⟨a, ⟨a.2, ha⟩, rfl⟩

theorem mem_HfQ_iff_red : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), c ∈ HfQ (P.PD K) LA _ hI ↔ ∃ a : ↥(latticeCocycles LA), (a : ↥(GK K) → A.V) ∈ finiteCocycles (P.PD K) A.ρ ∧ c = redT LA _ a := by
  intro l _ P K LL _ _ _ O _ _ _hO A LA ϖ r hI c
  exact mem_HfQ_iff (P.PD K) LA A.cont _ hI c

end GlobalTheory.BKTorsionRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemDualBlochKatoOfOrthogonalResidual
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual

namespace GlobalTheory.ResDual.Perp

theorem ker_iff {O K : Type} [CommRing O] [IsLocalRing O] [Field K] [Algebra O K]
    (h : ∀ x ∈ IsLocalRing.maximalIdeal O, algebraMap O K x = 0) (x : O) :
    algebraMap O K x = 0 ↔ x ∈ IsLocalRing.maximalIdeal O := by
  refine ⟨fun hx => ?_, h x⟩
  by_contra hn
  have hu : IsUnit x := by simpa using hn
  exact (hu.map (algebraMap O K)).ne_zero hx

theorem eq_iff {O K : Type} [CommRing O] [IsLocalRing O] [Field K] [Algebra O K]
    (h : ∀ x ∈ IsLocalRing.maximalIdeal O, algebraMap O K x = 0) (x y : O) :
    x - y ∈ IsLocalRing.maximalIdeal O ↔ algebraMap O K x = algebraMap O K y := by
  rw [← ker_iff h, map_sub, sub_eq_zero]

def divMap {O : Type} [CommRing O] [IsDomain O] (ϖ : O) : O →ₗ[O] Formalism.BasicNotions.KmodO O :=
  (Submodule.mkQ _) ∘ₗ (LinearMap.mulLeft O (algebraMap O (FractionRing O) ϖ)⁻¹) ∘ₗ Algebra.linearMap O (FractionRing O)

theorem divMap_apply {O : Type} [CommRing O] [IsDomain O] (ϖ a : O) :
    divMap ϖ a = Submodule.Quotient.mk ((algebraMap O (FractionRing O) ϖ)⁻¹ * algebraMap O (FractionRing O) a) := rfl

theorem divMap_eq_zero {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ)
    {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) : divMap ϖ a = 0 := by
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
  obtain ⟨b, rfl⟩ := ha
  have h0 : algebraMap O (FractionRing O) ϖ ≠ 0 := by
    simpa using hϖ.ne_zero
  rw [divMap_apply, Submodule.Quotient.mk_eq_zero, map_mul, inv_mul_cancel_left₀ h0]
  exact ⟨b, rfl⟩

theorem continuous_algebraMap {O K : Type} [CommRing O] [IsLocalRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [Field K] [Algebra O K] [TopologicalSpace K]
    (ha : IsAdic (IsLocalRing.maximalIdeal O))
    (h : ∀ x ∈ IsLocalRing.maximalIdeal O, algebraMap O K x = 0) : Continuous (algebraMap O K) := by
  have ho : IsOpen (IsLocalRing.maximalIdeal O : Set O) := by simpa using (isAdic_iff.1 ha).1 1
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun x => ?_)
  refine ⟨(fun y => y - x) ⁻¹' (IsLocalRing.maximalIdeal O : Set O), ho.preimage (by fun_prop), by simp, fun y hy => ?_⟩
  exact (eq_iff h y x).1 hy

theorem repOn_one_map {G O K : Type} [Group G] [CommRing O] [Field K] [Algebra O K] {r : ℕ} (ρ : G →* GL (Fin r) O)
    (g : G) (y : Fin r → O) (a : Fin r) :
    repOn ρ (1 : G →* Kˣ) K g (fun b => algebraMap O K (y b)) a =
      algebraMap O K (((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).mulVec y a) := by
  simp [repOn, matAct, Matrix.mulVec, dotProduct]

theorem mem_bkOn_of_orthogonal : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → Function.Surjective (algebraMap (X.O0 i) K) → ∀ ρ, IsDual i s ρ → ∀ v ∈ placesOver D.host.E (X.l i), ∀ y : Z1 ((red i K ρ).comp (DecV N v).subtype), (∀ x : Z1 ((red i K (Tgl i s)).comp (DecV N v).subtype), Submodule.Quotient.mk x ∈ bkOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K v → CupCob (fun g : DecV N v => algebraMap (X.O0 i) K ((eps0 X i g.1 : (X.O0 i)ˣ) : X.O0 i)) ((red i K ρ).comp (DecV N v).subtype) (dotProductBilin K K) x.1 y.1) → Submodule.Quotient.mk y ∈ bkOn bkP i ρ (1 : GE N →* Kˣ) K v := by
  intro D N X bkP i s hG K _ _ _ _ hK hs ρ hρ v hv y H
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.O0 i)
  choose lift hlift using hs
  have hy : ∀ g, y.1 g = fun b => algebraMap (X.O0 i) K (lift (y.1 g b)) := fun g => funext fun b => (hlift _).symm
  have hact : ∀ (g h : DecV N v) a, ((red i K ρ).comp (DecV N v).subtype) g (y.1 h) a =
      algebraMap (X.O0 i) K ((Tdual i s g.1).mulVec (fun b => lift (y.1 h b)) a) := fun g h a => by
    rw [← hρ g.1, ← repOn_one_map ρ g.1, ← hy]
    rfl
  have key := (_root_.GlobalTheory.BKLatticeCochain.lift_iff_orthogonal D N X bkP i s hG ρ hρ v hv ϖ hϖ (fun g a => lift (y.1 g a)) (fun a => ?_)
    (fun g h a => ?_)).2 ?_
  · obtain ⟨y', hy', e⟩ := key
    obtain ⟨c, hc, hc'⟩ := isFCoc_iff.1 hy'
    unfold bkOn
    rw [dite_eq_left hv]
    refine Submodule.subset_span ⟨y, c, y', 1, hc, hc', fun g a => ?_, rfl⟩
    rw [smul_eq_mul, mul_one, (eq_iff hK _ _).1 (e g a), hlift]
  · have : IsLocallyConstant fun g => y.1 g a :=
      (IsLocallyConstant.iff_continuous _).2 ((continuous_apply a).comp y.2.1)
    exact this.comp fun k => IsLocalRing.residue (X.O0 i) (lift k)
  · rw [eq_iff hK, map_add (f := _), hlift, hlift, ← hact, y.2.2 g h]
    rfl
  · intro d hd
    let x : Z1 ((red i K (Tgl i s)).comp (DecV N v).subtype) :=
      ⟨fun g a => algebraMap (X.O0 i) K (d g a),
        continuous_pi fun a => (continuous_algebraMap (X.twistBaseCoefficientRing_isAdic i) hK).comp ((continuous_apply a).comp hd.continuous),
        fun g h => funext fun a => by
          beta_reduce
          rw [hd.cocycle g h, Pi.add_apply, map_add (f := _), ← repOn_one_map]
          rfl⟩
    have hx : Submodule.Quotient.mk x ∈ bkOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K v := by
      obtain ⟨c, hc, hc'⟩ := isFCoc_iff.1 hd
      unfold bkOn
      rw [dite_eq_left hv]
      exact Submodule.subset_span ⟨x, c, d, 1, hc, hc', fun g a => by rw [smul_eq_mul, mul_one], rfl⟩
    obtain ⟨f, hf, e⟩ := H x hx
    refine ⟨fun g => divMap ϖ (lift (f g)), hf.comp fun k => divMap ϖ (lift k), fun g h => ?_⟩
    rw [← divMap_apply, ← map_smul, ← map_sub, ← map_add (f := _), ← sub_eq_zero, ← map_sub]
    apply divMap_eq_zero hϖ
    rw [eq_iff hK, map_add (f := _), map_sub, smul_eq_mul, map_mul, hlift, hlift, hlift, ← e g h]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProductBilin_apply_apply, dotProduct, map_sum, map_mul, hact]
    rfl

end GlobalTheory.ResDual.Perp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormConstantCoeffEqOneOfEisensteinFrobeniusCycleStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_constantCoeff_eq_one_of_eisenstein_frobenius_cycle : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (l e a M N : ℕ) [Fact l.Prime] [NeZero a], 0 < e → (l : K) ≠ 0 → ‖(l : K)‖ < 1 → ∀ (Δ k k' : ZMod a → K⟦X⟧), (∀ τ n, ‖coeff n (Δ τ)‖ ≤ 1) → (∀ τ, ∃ n, ‖coeff n (Δ τ)‖ = 1) → (∀ τ n, ‖coeff n (k τ)‖ ≤ 1) → (∀ τ n, ‖coeff n (k' τ)‖ ≤ 1) → (∀ τ, k τ * k' τ = E K l e ^ N) → (∀ τ, Δ τ * k τ = E K l e ^ M * frob K l (Δ (τ - 1))) → ∀ τ, ‖constantCoeff (Δ τ)‖ = 1 := by
  first | exact @GlobalTheory.BK.Cycle.norm_constantCoeff_eq_one_of_cycle | exact GlobalTheory.BK.Cycle.norm_constantCoeff_eq_one_of_cycle | (intros; apply GlobalTheory.BK.Cycle.norm_constantCoeff_eq_one_of_cycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFixAlt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.UnramInertia

theorem norm_sub_lt_one_of_fix : ∀ (l : ℕ) [Fact l.Prime] (σ : GQ l), (∀ x ∈ MaximalUnramifiedExtension l, σ x = x) →
    ∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1 := by
  intro l _ σ hσ x hx
  have hmem : σ ∈ (MaximalUnramifiedExtension l).fixingSubgroup := by
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).2 hσ
  exact GlobalTheory.FrobGen.norm_sub_lt hmem x hx

end GlobalTheory.UnramInertia
end

