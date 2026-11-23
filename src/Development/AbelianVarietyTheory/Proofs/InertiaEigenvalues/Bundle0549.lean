module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0474
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0529
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0530
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0533
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0508
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0375

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompositionSetting
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

theorem mat_mul {Γ k : Type} [Group Γ] [CommRing k] {r : ℕ} (σ : Γ →* GL (Fin r) k) (g h : Γ) :
    mat σ g * mat σ h = mat σ (g * h) := by
  simp [mat]

theorem span_eq_top_of_trace_eq {Γ k : Type} [Group Γ] [Field k] {r : ℕ}
    (σ ρ : Γ →* GL (Fin r) k) (ht : ∀ g, (mat σ g).trace = (mat ρ g).trace)
    (h : Submodule.span k (Set.range (mat ρ)) = ⊤) :
    Submodule.span k (Set.range (mat σ)) = ⊤ := by
  classical
  let L := Finsupp.linearCombination k (mat σ)
  let L0 := Finsupp.linearCombination k (mat ρ)
  have hker : LinearMap.ker L ≤ LinearMap.ker L0 := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    have h1 : ∀ y : Γ, (L0 c * mat ρ y).trace = 0 := by
      intro y
      have e1 : (L c * mat σ y).trace = 0 := by rw [hc]; simp
      rw [← e1]
      simp only [L, L0, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_mul, Matrix.smul_mul,
        Matrix.trace_sum, Matrix.trace_smul, mat_mul, ht]
    have h2 : ∀ Y : Matrix (Fin r) (Fin r) k, (L0 c * Y).trace = 0 := by
      intro Y
      have hY : Y ∈ Submodule.span k (Set.range (mat ρ)) := h ▸ Submodule.mem_top
      induction hY using Submodule.span_induction with
      | mem Y hY => obtain ⟨y, rfl⟩ := hY; exact h1 y
      | zero => simp
      | add Y Z _ _ hY hZ => rw [Matrix.mul_add, Matrix.trace_add, hY, hZ, add_zero]
      | smul a Y _ hY => rw [Matrix.mul_smul, Matrix.trace_smul, hY, smul_zero]
    ext p q
    have := h2 (Matrix.single q p 1)
    simpa [Matrix.trace_mul_single] using this
  have hL0 : LinearMap.range L0 = ⊤ := by
    rw [Finsupp.range_linearCombination]; exact h
  let f : LinearMap.range L →ₗ[k] Matrix (Fin r) (Fin r) k :=
    ((LinearMap.ker L).liftQ L0 hker).comp (L.quotKerEquivRange.symm : LinearMap.range L →ₗ[k] _)
  have hf : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _), Submodule.range_liftQ, hL0]
  have h3 := LinearMap.finrank_range_le f
  rw [hf, finrank_top] at h3
  have h4 : LinearMap.range L = ⊤ :=
    Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) h3)
  rw [← Finsupp.range_linearCombination]; exact h4

theorem absIrrSub_of_span_eq_top {Γ k : Type} [Group Γ] [Field k] {r : ℕ} (hr : 0 < r)
    (σ : Γ →* GL (Fin r) k) (h : Submodule.span k (Set.range (mat σ)) = ⊤) : AbsIrrSub σ ⊤ := by
  refine GlobalTheory.ResAbsIrrGood.absIrrSub_top_of_irred (algebraMap k (AlgebraicClosure k)) hr σ fun W hW => ?_
  refine GlobalTheory.BurnsideIff.eq_bot_or_top_of_span_eq_top (mat σ) h W fun g x hx => ?_
  have e : (mat σ g).map (algebraMap k (AlgebraicClosure k)) =
      ((mapRep (algebraMap k (AlgebraicClosure k)) σ g : GL (Fin r) (AlgebraicClosure k)) :
        Matrix (Fin r) (Fin r) (AlgebraicClosure k)) := by
    ext p q; simp [mat, mapRep]
  rw [e]; exact hW g x hx

theorem pos_of_absIrrSub {Γ k : Type} [Group Γ] [Field k] {r : ℕ} (σ : Γ →* GL (Fin r) k)
    (h : AbsIrrSub σ ⊤) : 0 < r := by
  rcases Nat.eq_zero_or_pos r with h0 | h0
  · subst h0
    exact absurd (Subsingleton.elim _ _) h.1
  · exact h0

end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

theorem mat_mapRep {Γ A B : Type} [Group Γ] [CommRing A] [CommRing B] {k : ℕ} (f : A →+* B)
    (σ : Γ →* GL (Fin k) A) (g : Γ) : mat (mapRep f σ) g = (mat σ g).map f := by
  ext p q; simp [mat, mapRep]

theorem charpoly_eq_of_isHeckeGalois (hC : GlobalTheory.TwSys.Cheb) (D : D7) (i : D.nd.Loc)
    (rep : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i rep) (π : D.nd.X i)
    (r0 : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)) (hr0 : IsHeckeGalois D.nd i π r0) (g : GE D.nd) :
    (mat (rep π) g).charpoly = (mat r0 g).charpoly := by
  classical
  let rep' := Function.update rep π r0
  have hr' : GoodR D.nd i rep' := by
    intro y
    by_cases hy : y = π
    · subst hy; simpa [rep'] using hr0
    · simpa [rep', Function.update_of_ne hy] using hr y
  obtain ⟨Pm, hPm⟩ := GlobalTheory.PointRepConj.main hC D.nd i rep rep' hr hr' π
  have h1 := hPm g
  have h2 : (rO D.nd i rep' π g) = mat r0 g := by simp [rep', rO, mat]
  rw [h2] at h1
  apply Polynomial.map_injective (toK D.nd i) (IsFractionRing.injective (D.nd.O i) (KK D.nd i))
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_map]
  have h1' : (Pm : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) * (mat (rep π) g).map (toK D.nd i) =
      (mat r0 g).map (toK D.nd i) * (Pm : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) := h1
  have h3 : (mat (rep π) g).map (toK D.nd i) =
      ((Pm⁻¹ : GL (Fin D.R.nV) (KK D.nd i)) : Matrix _ _ _) * (mat r0 g).map (toK D.nd i) *
        (Pm : Matrix _ _ _) := by
    rw [Matrix.mul_assoc, ← h1', ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul]
  rw [h3]
  have := Matrix.charpoly_units_conj (Pm⁻¹) ((mat r0 g).map (toK D.nd i))
  rwa [← Matrix.coe_units_inv, inv_inv] at this

end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFramedMatricesOfEtaleRealisationStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_framedMatrices_of_etaleRealisation : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)), Realises K M (ainfObj K) (ainfId K) T ρ j → ∃ (b : Module.Basis (Fin d) ℤ_[l] T) (U : Matrix (Fin d) (Fin d) (WCb l)), MReal S (fun g => LinearMap.toMatrix b b (ρ g)) U ∧ ∀ k, j (M.tr bk.ι (e k)) = ∑ i, U i k ⊗ₜ[ℤ_[l]] b i := by
  intro l _ K bk d S M e hF T _ _ ρ j H
  have h : ∃ (b : Module.Basis (Fin d) ℤ_[l] T) (U : Matrix (Fin d) (Fin d) (WCb l)),
      MReal S (fun g => LinearMap.toMatrix b b (ρ g)) U ∧
        ∀ k, j (M.tr bk.ι (e k)) = ∑ i, U i k ⊗ₜ[ℤ_[l]] b i := by
    have hfin := H.finite
    have hfree := H.free
    obtain ⟨e', he'⟩ := GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ (M.tr bk.ι) (M.tr_bc bk.ι) (Fin d) e
    obtain ⟨c, hc⟩ := GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ j H.bc (Fin d) e'
    have hrank : Module.finrank ℤ_[l] T = d := by
      rw [← Module.finrank_baseChange (R := WCb l), Module.finrank_eq_card_basis c, Fintype.card_fin]
    let b := Module.finBasisOfFinrankEq ℤ_[l] T hrank
    let U : Matrix (Fin d) (Fin d) (WCb l) := (b.baseChange (WCb l)).toMatrix c
    have hck : ∀ k, c k = ∑ i, U i k • (b.baseChange (WCb l)) i := fun k => ((b.baseChange (WCb l)).sum_repr (c k)).symm
    have hcj : ∀ k, c k = j (M.tr bk.ι (e k)) := fun k => by rw [hc, he']
    refine ⟨b, U, ⟨?_, ?_, ?_⟩, fun k => ?_⟩
    · exact @isUnit_of_invertible _ _ U ((b.baseChange (WCb l)).invertibleToMatrix c)
    · have hu : IsUnit (inclW l (bk.ev bk.E)) := isUnit_inclW_of_span bk.span_ev
      let t : ↥(ainfObj K).I := ⟨bk.ι.f bk.E, bk.ι.f_I _ (Ideal.mem_span_singleton_self _)⟩
      have hu' : IsUnit (((inclW l).comp (ainfId K).toRingHom) (t : (ainfObj K).A)) := hu
      have ht0 : (t : (ainfObj K).A) ≠ 0 := fun h => hu'.ne_zero (by rw [h, map_zero])
      have key : ∀ k, inclW l (bk.ev bk.E) ^ S.a • TensorProduct.map (frobW l).toLinearMap LinearMap.id (c k) =
          ∑ i, bk.evW (S.A i k) • c i := by
        intro k
        have hsum : ∑ j', (Pi.single k (1 : (ainfObj K).A) : Fin d → (ainfObj K).A) j' • M.tr bk.ι (e j') = M.tr bk.ι (e k) := by
          simp [Pi.single_apply]
        obtain ⟨m, s, hm⟩ := exists_isFrac (t : (ainfObj K).A)
          (M.Φ (ainfObj K) t (∑ j', (Pi.single k (1 : (ainfObj K).A) : Fin d → (ainfObj K).A) j' • M.tr bk.ι (e j')))
        obtain ⟨r, hr⟩ := GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis l K bk d M e S.a S.A hF.Φ (ainfObj K) bk.ι t _ m s hm
        replace hm : IsFrac (t : (ainfObj K).A) (M.Φ (ainfObj K) t (M.tr bk.ι (e k))) m s := by
          simpa only [hsum] using hm
        have hj : inclW l (bk.ev bk.E) ^ s • TensorProduct.map (frobW l).toLinearMap LinearMap.id
            (j (M.tr bk.ι (e k))) = j m := H.j_φ t ht0 _ m s hm
        have hφ1 : (fun j' => (ainfObj K).D.φ ((Pi.single k (1 : (ainfObj K).A) : Fin d → (ainfObj K).A) j')) =
            (Pi.single k (1 : (ainfObj K).A) : Fin d → (ainfObj K).A) :=
          funext fun j' => by
            by_cases h : j' = k
            · subst h; simp
            · simp [h]
        rw [hφ1] at hr
        have hr3 := (j.map_smulₛₗ ((t : (ainfObj K).A) ^ r) _).symm.trans ((congrArg j hr).trans j.map_zero)
        have hur : IsUnit (((inclW l).comp (ainfId K).toRingHom) ((t : (ainfObj K).A) ^ r)) := by
          rw [map_pow]; exact hu'.pow r
        have hr5 := sub_eq_zero.1 ((j.map_sub _ _).symm.trans (hur.smul_eq_zero.1 hr3))
        have hr7 := (j.map_smulₛₗ _ _).symm.trans (hr5.trans (j.map_smulₛₗ _ _))
        have e1 : ((inclW l).comp (ainfId K).toRingHom) ((BK.hf bk.ι bk.E) ^ S.a) = inclW l (bk.ev bk.E) ^ S.a :=
          map_pow _ _ _
        have e2 : ((inclW l).comp (ainfId K).toRingHom) ((t : (ainfObj K).A) ^ s) = inclW l (bk.ev bk.E) ^ s :=
          map_pow _ _ _
        have hsum2 : j (∑ i, (S.A.map (BK.hf bk.ι)).mulVec (Pi.single k 1) i • M.tr bk.ι (e i)) =
            ∑ i, bk.evW (S.A i k) • c i := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [LinearMap.map_smulₛₗ, ← hcj, Matrix.mulVec_single_one]
          rfl
        apply (hu.pow s).smul_left_cancel.1
        calc inclW l (bk.ev bk.E) ^ s • (inclW l (bk.ev bk.E) ^ S.a •
                TensorProduct.map (frobW l).toLinearMap LinearMap.id (c k))
            = inclW l (bk.ev bk.E) ^ S.a • (inclW l (bk.ev bk.E) ^ s •
                TensorProduct.map (frobW l).toLinearMap LinearMap.id (j (M.tr bk.ι (e k)))) := by
              rw [hcj, smul_smul, smul_smul, mul_comm]
          _ = inclW l (bk.ev bk.E) ^ S.a • j m := congrArg _ hj
          _ = ((inclW l).comp (ainfId K).toRingHom) ((BK.hf bk.ι bk.E) ^ S.a) • j m := congrArg (· • j m) e1.symm
          _ = ((inclW l).comp (ainfId K).toRingHom) ((t : (ainfObj K).A) ^ s) •
                j (∑ i, (S.A.map (BK.hf bk.ι)).mulVec (Pi.single k 1) i • M.tr bk.ι (e i)) := hr7
          _ = inclW l (bk.ev bk.E) ^ s • ∑ i, bk.evW (S.A i k) • c i := by rw [e2, hsum2]
      have hev : ∀ x, bk.evW x = inclW l (bk.ev x) := fun _ => rfl
      refine Matrix.ext fun i k => ?_
      have h := congrArg (fun y => (b.baseChange (WCb l)).repr y i) (key k)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_smul, map_sum, Finsupp.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
        repr_map_baseChange, LinearMap.toMatrix_id, Matrix.one_apply, smul_eq_mul, apply_ite (algebraMap ℤ_[l] (WCb l)),
        map_one, map_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
        AlgHom.toLinearMap_apply] at h
      simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply, smul_eq_mul, hev, U,
        Module.Basis.toMatrix_apply]
      rw [h]
      exact Finset.sum_congr rfl fun x _ => by rw [hev, mul_comm]
    · intro g
      have keyg : ∀ k, TensorProduct.map (galW l (g : GQ l)).toLinearMap (ρ g) (c k) =
          ∑ i, inclW l (S.ε bk.ι ((ainfHom K g).comp bk.ι) i k) • c i := by
        intro k
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hcj, ← H.j_act_of g (ainfHom K g) (fun _ => rfl), ← M.tr_comp, hF.tr bk.ι ((ainfHom K g).comp bk.ι) k,
          map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [LinearMap.map_smulₛₗ, ← hcj]
        rfl
      refine Matrix.ext fun i k => ?_
      have h := congrArg (fun y => (b.baseChange (WCb l)).repr y i) (keyg k)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_smul, map_sum, Finsupp.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
        repr_map_baseChange, smul_eq_mul, AlgEquiv.toLinearMap_apply] at h
      simp only [Matrix.mul_apply, Matrix.map_apply, U, Module.Basis.toMatrix_apply, zW]
      rw [h]
      exact Finset.sum_congr rfl fun x _ => mul_comm _ _
    · rw [← hcj, hck]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  exact h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusMatrixMulEqEPowOfPeriod
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.HeightAprime

theorem dvd_of_dvd_prime_pow_mul {R : Type} [CommRing R] [IsDomain R] {p a b : R} (hp : Prime p)
    (ha : ¬ p ∣ a) : ∀ n : ℕ, a ∣ p ^ n * b → a ∣ b := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro h
    obtain ⟨x, hx⟩ := h
    have hpx : p ∣ a * x := ⟨p ^ n * b, by rw [← hx]; ring⟩
    obtain ⟨y, rfl⟩ := (hp.dvd_or_dvd hpx).resolve_left ha
    refine ih ⟨y, mul_left_cancel₀ hp.ne_zero ?_⟩
    linear_combination hx

theorem C_dvd_iff {R : Type} [CommRing R] (p : R) (f : R⟦X⟧) :
    C p ∣ f ↔ ∀ n, p ∣ coeff n f := by
  constructor
  · rintro ⟨g, rfl⟩ n
    rw [coeff_C_mul]; exact dvd_mul_right _ _
  · intro h
    refine ⟨mk fun n => (h n).choose, ?_⟩
    ext n
    rw [coeff_C_mul, coeff_mk]
    exact (h n).choose_spec

theorem prime_C {R : Type} [CommRing R] [IsDomain R] {p : R} (hp : Prime p) : Prime (C p : R⟦X⟧) := by
  haveI : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  let q : R →+* R ⧸ Ideal.span {p} := Ideal.Quotient.mk _
  have key : ∀ f : R⟦X⟧, C p ∣ f ↔ PowerSeries.map q f = 0 := by
    intro f
    rw [C_dvd_iff]
    constructor
    · intro h; ext n
      rw [coeff_map, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 (h n))
    · intro h n
      have := congrArg (coeff n) h
      rw [coeff_map, map_zero] at this
      exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 this)
  refine ⟨fun h => hp.ne_zero (by simpa using congrArg (constantCoeff) h), fun h => hp.not_unit ?_, ?_⟩
  · simpa using h.map (constantCoeff (R := R))
  · intro f g hfg
    rw [key, key]
    rw [key, map_mul] at hfg
    exact mul_eq_zero.1 hfg

theorem prime_l {l : ℕ} [Fact l.Prime] (a : ℕ) [NeZero a] : Prime (l : (Wq l a)⟦X⟧) := by
  have h : Prime (l : Wq l a) := (WittVector.irreducible l).prime
  have := prime_C h
  simpa using this

end GlobalTheory.BSP.HeightAprime

namespace GlobalTheory.BSP.HeightAprime

variable {l : ℕ} [hl : Fact l.Prime]

theorem not_l_dvd_det {K : FinExt l} (bk : BK K) {d : ℕ} (Y : Matrix (Fin d) (Fin d) (Ainf l))
    (A : Matrix (Fin d) (Fin d) bk.S) (hY : IsUnit (Y.map (inclW l)))
    (hφ : Y.map WittVector.frobenius = Y * A.map bk.ev) : ¬ (l : bk.S) ∣ A.det := by
  rintro ⟨t, ht⟩
  have h2 : WittVector.frobenius Y.det = Y.det * bk.ev A.det := by
    rw [RingHom.map_det, RingHom.map_det, ← det_mul]
    exact congrArg det hφ
  have h0 := congrArg WittVector.constantCoeff h2
  rw [ht, map_mul, map_mul, map_mul, map_natCast, map_natCast, CharP.cast_eq_zero, zero_mul, mul_zero] at h0
  have hc : (WittVector.frobenius Y.det).coeff 0 = Y.det.coeff 0 ^ l :=
    WittVector.coeff_frobenius_charP l _ 0
  have hz : Y.det.coeff 0 = 0 := by
    have : WittVector.constantCoeff (WittVector.frobenius Y.det) = (WittVector.frobenius Y.det).coeff 0 := rfl
    rw [this, hc] at h0
    exact pow_eq_zero_iff hl.out.ne_zero |>.1 h0
  have hu : IsUnit (inclW l Y.det) := by
    rw [RingHom.map_det]; exact (Matrix.isUnit_iff_isUnit_det _).1 hY
  have hu0 := hu.map (WittVector.constantCoeff (p := l) (R := Cb l))
  have : WittVector.constantCoeff (inclW l Y.det) = (inclW l Y.det).coeff 0 := rfl
  rw [this, inclW, WittVector.map_coeff, hz, map_zero] at hu0
  exact not_isUnit_zero hu0

end GlobalTheory.BSP.HeightAprime

theorem GlobalTheory.BSP.HeightAprime.main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (Y S' : Matrix (Fin d) (Fin d) (Ainf l)) (A : Matrix (Fin d) (Fin d) (bk.S)) (k M : ℕ), IsUnit (Y.map (inclW l)) → Y * S' = ((l : Ainf l) ^ k * τ ^ M) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → Y.map WittVector.frobenius = Y * A.map bk.ev → ∃ (b : ℕ) (A' : Matrix (Fin d) (Fin d) (bk.S)), A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) (bk.S)) := by
  intro l _ K bk τ hτ d Y S' A k M hY hYS hφ
  have h1 : Y.det * S'.det = ((l : Ainf l) ^ k * τ ^ M) ^ d := by
    rw [← det_mul, hYS, det_smul, det_one, mul_one, Fintype.card_fin]
  have h2 : WittVector.frobenius Y.det = Y.det * bk.ev A.det := by
    rw [RingHom.map_det, RingHom.map_det, ← det_mul]
    exact congrArg det hφ
  have h3 : bk.ev A.det * (Y.det * WittVector.frobenius S'.det) =
      bk.ev ((l : bk.S) ^ (k * d) * bk.E ^ (M * d)) * τ ^ (M * d) := by
    have := congrArg WittVector.frobenius h1
    rw [map_mul, h2, map_pow, map_mul, map_pow, map_pow, map_natCast, hτ.1] at this
    rw [map_mul, map_pow, map_pow, map_natCast, pow_mul, pow_mul, pow_mul]
    linear_combination this
  obtain ⟨ι, ⟨TB⟩⟩ := _root_.GlobalTheory.BSP.AinfTopBasis.main l K bk
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.BSP.pow_l_mem_span_coeff l K bk τ hτ ι TB (M * d)
  set c : bk.S := (l : bk.S) ^ (k * d) * bk.E ^ (M * d)
  have hdiv : ∀ i, A.det ∣ c * TB.c i (τ ^ (M * d)) := fun i => by
    have := congrArg (TB.c i) h3
    rw [TB.c_mul, TB.c_mul] at this
    exact ⟨_, this.symm⟩
  have hdvd : A.det ∣ c * (l : bk.S) ^ r := by
    refine Submodule.span_induction (p := fun x _ => A.det ∣ c * x) ?_ ?_ ?_ ?_ hr
    · rintro _ ⟨i, rfl⟩; exact hdiv i
    · simp
    · intro x y _ _ hx hy; rw [mul_add]; exact dvd_add hx hy
    · intro a x _ hx; rw [smul_eq_mul, mul_left_comm]; exact dvd_mul_of_dvd_right hx a
  have hdvd' : A.det ∣ (l : bk.S) ^ (k * d + r) * bk.E ^ (M * d) := by
    have e : c * (l : bk.S) ^ r = (l : bk.S) ^ (k * d + r) * bk.E ^ (M * d) := by
      simp only [c]; ring
    rwa [e] at hdvd
  obtain ⟨q, hq⟩ := GlobalTheory.BSP.HeightAprime.dvd_of_dvd_prime_pow_mul (GlobalTheory.BSP.HeightAprime.prime_l bk.a)
    (GlobalTheory.BSP.HeightAprime.not_l_dvd_det bk Y A hY hφ) _ hdvd'
  refine ⟨M * d, q • A.adjugate, ?_⟩
  rw [Matrix.mul_smul, mul_adjugate, smul_smul, mul_comm q, ← hq]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisDecompTameCoverAction
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.TameCoverGen

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e]
    (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
    [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : BKGal.Gl l),
    ∃ h k : BKGal.Gl l, g = h * k ∧ BKGal.sQ l h ∈ GK (ϖ.field a) ∧
      ∃ γ : BK.TameGal K l e a, BKGal.Covers K t ϖ (BKGal.sQ l k) γ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ g
  have he : e + 1 = l ^ a := TameDescentExponentData.succ_eq (K := K)
  obtain ⟨h, hh, k, hk, hg⟩ :=
    _root_.GlobalTheory.NgalDecomp.galQ_eq_GK_mul_GKinf l a e ϖ he (BKGal.sQ l g)
  let h' : BKGal.Gl l :=
    ⟨h, GK_le (K := Formalism.MainNotions.ElementDenominator.qlExt l) (K' := ϖ.field a) bot_le hh⟩
  refine ⟨h', h'⁻¹ * g, by rw [mul_inv_cancel_left], hh, ?_⟩
  have hk' : BKGal.sQ l (h'⁻¹ * g) = k := by
    rw [map_mul, map_inv, show BKGal.sQ l g = h * k from hg]
    change h⁻¹ * (h * k) = k
    rw [inv_mul_cancel_left]
  rw [hk']
  obtain ⟨s, hs⟩ := GlobalTheory.T.galois_action_cyclotomic_power l a k
  obtain ⟨z, hz, hkz⟩ := _root_.GlobalTheory.BKReal.kummer_mem_Fq_of_mem_GKinf l a e ϖ he k hk
  exact _root_.GlobalTheory.CoverGen.exists_covers_of_sigma_teich l a e O K t ϖ k s z hz hs hkz

end GlobalTheory.TameCoverGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerSeriesLiftOfPeriodPowSmulIntegralMatr
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.KisinFF

theorem exists_of_inclW_eq_pow_mul {l : ℕ} [Fact l.Prime] (n : ℕ) : ∀ (a : Ainf l) (w : WCb l),
    inclW l a = (l : WCb l) ^ n * w → ∃ a', a = (l : Ainf l) ^ n * a' ∧ inclW l a' = w := by
  induction n with
  | zero => intro a w h; exact ⟨a, by simp, by simpa using h⟩
  | succ n ih =>
    intro a w h
    obtain ⟨a₁, ha₁⟩ := GlobalTheory.HWL.TensorWitt.ainf_saturated_in_tiltWitt_prime a ((l : WCb l) ^ n * w) (by rw [h]; ring)
    obtain ⟨a', ha', hw'⟩ := ih a₁ w ha₁
    refine ⟨a', ?_, hw'⟩
    have h1 : a = (l : Ainf l) * a₁ := by
      apply GlobalTheory.HWL.TensorWitt.inclW_injective
      rw [map_mul, map_natCast, ha₁, h]; ring
    rw [h1, ha']; ring

theorem scalar {l : ℕ} [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (M : ℕ)
    (w : WCb l) (hw : w ∈ bk.OE) (a : Ainf l) (ha : inclW l a = inclW l τ ^ M * w) :
    ∃ s : bk.S, bk.evW s = w := by
  classical
  obtain ⟨ι, ⟨TB⟩⟩ := _root_.GlobalTheory.BSP.AinfTopBasis.main l K bk
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.BSP.pow_l_mem_span_coeff l K bk τ hτ ι TB M
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hr
  obtain ⟨v, -, hv⟩ := (_root_.GlobalTheory.OEDvr.main l K bk).2.1
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : bk.S, s₀ = c.sum fun i μ => μ * TB.c i a := ⟨_, rfl⟩
  have hev : ∀ t : bk.S, inclW l (bk.ev t) = bk.evW t := fun t => rfl
  have key : ∀ n : ℕ, (l : WCb l) ^ n ∣ bk.evW s₀ - (l : WCb l) ^ r * w := by
    intro n
    obtain ⟨m, s, y, h⟩ := hw n
    have hz : inclW l (bk.ev X ^ m * a - τ ^ M * bk.ev s) = (l : WCb l) ^ n * (inclW l τ ^ M * y) := by
      rw [map_sub, map_mul, map_mul, map_pow, map_pow, hev, hev, ha]
      linear_combination (inclW l τ ^ M) * h
    obtain ⟨z', hz', -⟩ := exists_of_inclW_eq_pow_mul n _ _ hz
    have hci : ∀ i, X ^ m * TB.c i a - s * TB.c i (τ ^ M) = (l : bk.S) ^ n * TB.c i z' := by
      intro i
      have := congrArg (TB.c i) hz'
      rw [map_sub, show bk.ev X ^ m = bk.ev (X ^ m) from (map_pow _ _ _).symm, TB.c_mul, mul_comm (τ ^ M) (bk.ev s), TB.c_mul,
        show ((l : Ainf l) ^ n) = bk.ev ((l : bk.S) ^ n) by simp, TB.c_mul] at this
      exact this
    obtain ⟨t, ht⟩ : ∃ t : bk.S, t = c.sum fun i μ => μ * TB.c i z' := ⟨_, rfl⟩
    have hS : X ^ m * s₀ - s * (l : bk.S) ^ r = (l : bk.S) ^ n * t := by
      rw [← hc, hs₀, ht]
      simp only [Finsupp.sum, Finset.mul_sum, smul_eq_mul]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by linear_combination c i * hci i
    have hW := congrArg bk.evW hS
    simp only [map_sub, map_mul, map_pow, map_natCast] at hW
    have hv' : bk.evW X ^ m * v ^ m = 1 := by rw [← mul_pow, hv, one_pow]
    refine ⟨v ^ m * (bk.evW t - (l : WCb l) ^ r * y), ?_⟩
    linear_combination v ^ m * hW - (l : WCb l) ^ r * v ^ m * h - (bk.evW s₀ - (l : WCb l) ^ r * w) * hv'
  have hd : bk.evW s₀ - (l : WCb l) ^ r * w = 0 := by
    refine IsHausdorff.haus' (I := Ideal.span {(l : WCb l)}) _ fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact key n
  obtain ⟨a', -, ha'⟩ := exists_of_inclW_eq_pow_mul r (bk.ev s₀) w (by rw [hev]; linear_combination hd)
  obtain ⟨s', hs'⟩ := _root_.GlobalTheory.BSP.ainf_inter_OE l K bk w hw a' ha'.symm
  exact ⟨s', by rw [← hev, ← hs', ha']⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d d' M : ℕ) (X : Matrix (Fin d') (Fin d) (WCb l)) (x : Matrix (Fin d') (Fin d) (Ainf l)), (∀ i j, X i j ∈ bk.OE) → x.map (inclW l) = inclW l τ ^ M • X → ∃ Y : Matrix (Fin d') (Fin d) bk.S, Y.map bk.evW = X := by
  intro l _ K bk τ hτ d d' M X x hX hx
  have he : ∀ i j, inclW l (x i j) = inclW l τ ^ M * X i j := fun i j => by
    have := congrFun (congrFun hx i) j
    simpa [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] using this
  choose Y hY using fun i j => scalar K bk τ hτ M (X i j) (hX i j) (x i j) (he i j)
  exact ⟨Y, Matrix.ext fun i j => hY i j⟩

end GlobalTheory.BSP.KisinFF
end

