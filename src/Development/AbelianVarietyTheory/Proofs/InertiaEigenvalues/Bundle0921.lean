module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0800
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0919
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0770
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0644
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsEmptyOfNotAll
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0698
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0707
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0855

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralScalarInverseUniformisersIdempotentSum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CentralScalar

section Alg

variable {R ι : Type} [CommRing R] {s : Finset ι} {p q : ι → R}

def comp (s : Finset ι) (p q u v : ι → R) : R := 1 + ∑ i ∈ s, (p i * (u i - 1) + q i * (v i - 1))

theorem comp_swap (u v : ι → R) : comp s p q u v = comp s q p v u := by
  unfold comp
  congr 1
  exact Finset.sum_congr rfl fun i _ => add_comm _ _

theorem left_mul_comp (h1 : ∀ i ∈ s, p i * p i = p i) (h2 : ∀ i ∈ s, ∀ j ∈ s, j ≠ i → p i * p j = 0)
    (h3 : ∀ i ∈ s, ∀ j ∈ s, p i * q j = 0) (u v : ι → R) {i : ι} (hi : i ∈ s) :
    p i * comp s p q u v = p i * u i := by
  unfold comp
  rw [mul_add, Finset.mul_sum, Finset.sum_eq_single_of_mem i hi]
  · rw [mul_add, ← mul_assoc, ← mul_assoc, h1 i hi, h3 i hi i hi]; ring
  · intro j hj hji
    rw [mul_add, ← mul_assoc, ← mul_assoc, h2 i hi j hj hji, h3 i hi j hj]; ring

theorem comp_mul (hp : ∀ u v : ι → R, ∀ i ∈ s, p i * comp s p q u v = p i * u i)
    (hq : ∀ u v : ι → R, ∀ i ∈ s, q i * comp s p q u v = q i * v i) (u v u' v' : ι → R) :
    comp s p q u v * comp s p q u' v' = comp s p q (fun i => u i * u' i) (fun i => v i * v' i) := by
  have h : comp s p q u v * comp s p q u' v' =
      comp s p q u' v' + ∑ i ∈ s, (p i * u' i * (u i - 1) + q i * v' i * (v i - 1)) := by
    conv_lhs => rw [comp]
    rw [add_mul, one_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← hp u' v' i hi, ← hq u' v' i hi]; ring
  rw [h]
  unfold comp
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem comp_eq_one {u v : ι → R} (hu : ∀ i ∈ s, u i = 1) (hv : ∀ i ∈ s, v i = 1) : comp s p q u v = 1 := by
  unfold comp
  rw [Finset.sum_eq_zero, add_zero]
  intro i hi
  rw [hu i hi, hv i hi]; ring

theorem mul_pow_of_mul_eq {e a w : R} (h : e * a = e * w) (n : ℕ) : e * a ^ n = e * w ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← mul_assoc, ih, mul_right_comm, h, pow_succ]; ring

theorem map_comp (c : R →+* R) (hc : ∀ x, c (c x) = x) (u v : ι → R) :
    c (comp s p (fun i => c (p i)) u v) = comp s p (fun i => c (p i)) (fun i => c (v i)) (fun i => c (u i)) := by
  unfold comp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_one, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_add (f := _), map_mul, map_sub, map_one, hc]
  ring

end Alg

variable {D : D7}

theorem cA_incA (x : D.host.E) : cA D (incA D x) = incA D (star x) := rfl

theorem mt_inj (V : HSp D) {a b : GA D V} (h : Formalism.L2.Theta.mt V a = Formalism.L2.Theta.mt V b) : a = b :=
  Subtype.ext (Units.ext h)

theorem exists_scalar (V : HSp D) (a : AE D) (ha : cA D a * a = 1) :
    ∃ z : GA D V, Formalism.L2.Theta.mt V z = Matrix.diagonal fun _ => a := by
  have h1 : (Matrix.diagonal fun _ : Fin V.rank => a) * (Matrix.diagonal fun _ => cA D a) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, mul_comm, ha, Matrix.diagonal_one]
  have h2 : (Matrix.diagonal fun _ : Fin V.rank => cA D a) * (Matrix.diagonal fun _ => a) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ha, Matrix.diagonal_one]
  refine ⟨⟨⟨_, _, h1, h2⟩, ?_⟩, rfl⟩
  change Formalism.UG.cT (cA D) (Matrix.diagonal fun _ => a) * _ * (Matrix.diagonal fun _ => a) = _
  have h3 : Formalism.UG.cT (cA D) (Matrix.diagonal fun _ : Fin V.rank => a) = Matrix.diagonal fun _ => cA D a := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Formalism.UG.cT]
    · simp [Formalism.UG.cT, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]
  rw [h3]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_right_comm, ha, one_mul]

theorem scalar_central (V : HSp D) {a : AE D} {z : GA D V} (hz : Formalism.L2.Theta.mt V z = Matrix.diagonal fun _ => a) :
    z ∈ Subgroup.center (GA D V) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply mt_inj V
  change Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V z = Formalism.L2.Theta.mt V z * Formalism.L2.Theta.mt V g
  rw [hz]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem scalar_fin (V : HSp D) {a : AE D} (ha : infPart D a = 1) {z : GA D V}
    (hz : Formalism.L2.Theta.mt V z = Matrix.diagonal fun _ => a) : z ∈ GfC V := by
  refine MonoidHom.mem_ker.2 (Units.ext ?_)
  change (Formalism.L2.Theta.mt V z).map (infPart D) = 1
  rw [hz, Matrix.diagonal_map (map_zero _)]
  simp only [ha, Matrix.diagonal_one]

theorem scalar_inv (V : HSp D) {a : AE D} (ha : cA D a * a = 1) {z : GA D V}
    (hz : Formalism.L2.Theta.mt V z = Matrix.diagonal fun _ => a) :
    Formalism.L2.Theta.mt V z⁻¹ = Matrix.diagonal fun _ => cA D a := by
  have h1 : (Matrix.diagonal fun _ : Fin V.rank => a) * (Matrix.diagonal fun _ => cA D a) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, mul_comm, ha, Matrix.diagonal_one]
  have h := Formalism.IndefR.Fin.LevelGroupLemmas.Lat.mt_inv_mul V z
  rw [← Matrix.mul_one (Formalism.L2.Theta.mt V z⁻¹), ← h1, ← Matrix.mul_assoc, ← hz, h, Matrix.one_mul]

theorem scalar_supp (V : HSp D) {e a : AE D} (ha : (e + cA D e) * (a - 1) = a - 1) {z : GA D V}
    (hz : Formalism.L2.Theta.mt V z = Matrix.diagonal fun _ => a) : SuppAt e V z := by
  intro i j
  rw [hz]
  by_cases h : i = j
  · subst h
    simpa only [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] using ha
  · rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h, sub_zero, mul_zero]

theorem centralScalar : ∀ (D : D7) (V : HSp D) (Q : Finset (Pl D.host.E)) (es : Pl D.host.E → AE D) (ϖ : Pl D.host.E → 𝓞 D.host.E), (∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP) → (∑ PP ∈ Q, es PP) * cA D (∑ PP ∈ Q, es PP) = 0 → (∀ PP ∈ Q, ϖ PP ≠ 0) → (∃ z : GA D V, mt V z = Matrix.diagonal fun _ => (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)))) ∧ ∀ z : GA D V, mt V z = Matrix.diagonal (fun _ => (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)))) → z ∈ Subgroup.center (GA D V) ∧ z ∈ GfC V ∧ SuppAt (∑ PP ∈ Q, es PP) V z ∧ (∃ x : (AE D)ˣ, IsDetAt (cA D (∑ PP ∈ Q, es PP)) V z x ∧ (x : AE D) = 1 + ∑ PP ∈ Q, cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) ^ V.rank - 1)) ∧ mt V z⁻¹ = Matrix.diagonal (fun _ => cA D (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)))) ∧ (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) * (∑ PP ∈ Q, es PP) = ∑ PP ∈ Q, es PP * incA D ((ϖ PP : D.host.E)⁻¹) ∧ cA D (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) * (∑ PP ∈ Q, es PP) = ∑ PP ∈ Q, es PP * incA D (ϖ PP : D.host.E) ∧ (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) * cA D (∑ PP ∈ Q, es PP) = cA D (∑ PP ∈ Q, es PP * incA D (ϖ PP : D.host.E)) ∧ cA D (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) * cA D (∑ PP ∈ Q, es PP) = cA D (∑ PP ∈ Q, es PP * incA D ((ϖ PP : D.host.E)⁻¹)) := by
  intro D V Q es ϖ hes hc hϖ
  have h1 : ∀ i ∈ Q, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hx := GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es Q h1 hc
  have h2 : ∀ i ∈ Q, ∀ j ∈ Q, j ≠ i → es i * es j = 0 := fun i hi j hj h =>
    GlobalTheory.PlaceDatum.idemAt_mul (hes i hi) (hes j hj) (hx i hi j hj) (hx j hj i hi) h
  have hp : ∀ u v : Pl D.host.E → AE D, ∀ i ∈ Q,
      es i * comp Q es (fun i => cA D (es i)) u v = es i * u i := fun u v i hi => left_mul_comp h1 h2 hx u v hi
  have hq : ∀ u v : Pl D.host.E → AE D, ∀ i ∈ Q,
      cA D (es i) * comp Q es (fun i => cA D (es i)) u v = cA D (es i) * v i := fun u v i hi => by
    rw [comp_swap]
    refine left_mul_comp (p := fun i => cA D (es i)) (fun i hi => ?_) (fun i hi j hj h => ?_) (fun i hi j hj => ?_) v u hi
    · rw [← map_mul, h1 i hi]
    · rw [← map_mul, h2 i hi j hj h, map_zero]
    · rw [mul_comm]; exact hx j hj i hi
  have hne : ∀ i ∈ Q, (ϖ i : D.host.E) ≠ 0 := fun i hi h => hϖ i hi (RingOfIntegers.coe_eq_zero_iff.1 h)
  set a : AE D := 1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) +
    cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)) with ha
  have ha' : a = comp Q es (fun i => cA D (es i)) (fun PP => incA D ((ϖ PP : D.host.E)⁻¹))
    (fun PP => incA D (star (ϖ PP : D.host.E))) := rfl
  have hca : cA D a = comp Q es (fun i => cA D (es i)) (fun PP => incA D (ϖ PP : D.host.E))
      (fun PP => incA D (star (ϖ PP : D.host.E)⁻¹)) := by
    rw [ha', map_comp (cA D) GlobalTheory.DualPairCheck.cA_cA]
    simp only [cA_incA, star_star]
  have hn : cA D a * a = 1 := by
    rw [hca, ha', comp_mul hp hq]
    refine comp_eq_one (fun i hi => ?_) (fun i hi => ?_)
    · rw [← map_mul, mul_inv_cancel₀ (hne i hi), map_one]
    · rw [← map_mul, ← star_mul, mul_inv_cancel₀ (hne i hi), star_one, map_one]
  refine ⟨exists_scalar V a hn, fun z hz => ⟨scalar_central V hz, scalar_fin V ?_ hz, scalar_supp V ?_ hz, ?_,
    scalar_inv V hn hz, ?_, ?_, ?_, ?_⟩⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [ha, map_add (f := _), map_one, map_sum, Finset.sum_eq_zero, add_zero]
    intro i hi
    have h0 := Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_of_splitIdem (hes i hi).1
    rw [map_add (f := _), map_mul, map_mul, h0, GlobalTheory.PlaceVec.infPart_cA h0, zero_mul, zero_mul, add_zero]
  · have : a - 1 = ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) +
      cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)) := by rw [ha, add_sub_cancel_left]
    conv_rhs => rw [this]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [add_mul, mul_sub, mul_sub, ha', hp _ _ i hi, hq _ _ i hi]
    ring
  · have hu : comp Q es (fun i => cA D (es i)) (fun _ => 1) (fun PP => incA D (star (ϖ PP : D.host.E)) ^ V.rank) *
        comp Q es (fun i => cA D (es i)) (fun _ => 1) (fun PP => incA D (star (ϖ PP : D.host.E)⁻¹) ^ V.rank) = 1 := by
      rw [comp_mul hp hq]
      refine comp_eq_one (fun i _ => one_mul _) (fun i hi => ?_)
      rw [← mul_pow, ← map_mul, ← star_mul, inv_mul_cancel₀ (hne i hi), star_one, map_one, one_pow]
    have hv : comp Q es (fun i => cA D (es i)) (fun _ => 1) (fun PP => incA D (star (ϖ PP : D.host.E)) ^ V.rank) =
        1 + ∑ PP ∈ Q, cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) ^ V.rank - 1) := by
      simp only [comp, sub_self, mul_zero, zero_add]
    refine ⟨Units.mkOfMulEqOne _ _ hu, ?_, hv⟩
    change comp Q es (fun i => cA D (es i)) (fun _ => 1) (fun PP => incA D (star (ϖ PP : D.host.E)) ^ V.rank) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hv, hz, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_sum, Finset.sum_mul]
    have : ∀ i ∈ Q, cA D (es i) * a ^ V.rank = cA D (es i) * incA D (star (ϖ i : D.host.E)) ^ V.rank :=
      fun i hi => mul_pow_of_mul_eq (hq _ _ i hi) _
    rw [Finset.sum_congr rfl this]
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    ring
  · rw [mul_comm, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => hp _ _ i hi
  · rw [mul_comm, Finset.sum_mul, hca]
    exact Finset.sum_congr rfl fun i hi => hp _ _ i hi
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [mul_comm, map_sum, map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => by rw [map_mul, cA_incA]; exact hq _ _ i hi
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [mul_comm, map_sum, map_sum, Finset.sum_mul, hca]
    exact Finset.sum_congr rfl fun i hi => by rw [map_mul, cA_incA]; exact hq _ _ i hi

end GlobalTheory.CentralScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommutantFullOfLocalLanglands
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CommFullLayer

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.IndefR.Cx Formalism.L2.Pj
  GlobalTheory.TwInputs GlobalTheory.CommFullAll
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

section Raw

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (Rl : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) {S : RatDat D.ntw}
  (YS : NExpRealS Rl cG S) (H : NExpRealH Rl cG S YS)

theorem hL_comm_raw (hR : Rl.Char3 F) (hU : Rl.toRealDat.LUnif)
    (hX : NExpHeckeRowX Rl cG S YS H fun _ => LinearMap.id) (i' : Fin D.R.m) (k : ℕ) (P : PlE D.host)
    (hsp : IsSplitPl D.host P) (hso : Bridge.SplitOff P (Rl.Sb : Set (Pl D.host.E))) (hi : ∃ i, P ∉ D.ntw.S0 i)
    (h2 : ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (hkr : k ≤ D.R.r)
    (g : S.G) (x : S.WL ((i' : ℕ) + 1)) :
    H.hL ((i' : ℕ) + 1) k P ((S.A ((i' : ℕ) + 1)).ρ g x) = (S.A ((i' : ℕ) + 1)).ρ g (H.hL ((i' : ℕ) + 1) k P x) := by
  obtain ⟨α, Rc, ha, hRc⟩ := GlobalTheory.HeckeSupSt.exists_heckeElt hR.lev hR.fam i' hso hkr
  have hd : GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.IsHkData Rl.toRealDat i' P k α Rc := ⟨hso, hg, hkr, ha, hRc⟩
  let hL' : (Fin (Rl.nW i') → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (Rl.nW i') → D.what₂.LL) :=
    (YS.fi i').e.toLinearMap ∘ₗ H.hL ((i' : ℕ) + 1) k P ∘ₗ (YS.fi i').e.symm.toLinearMap
  have hH : Formalism.L2.Pj.HeckeJ.IsHkJ (sg0 D A3.A) ((Rl.FW i').j (sg0 D A3.A)) (Rl.HW i' (sg0 D A3.A)).e
      (heckeOn (Rl.MW i' (sg0 D A3.A)) Rc)
      ((((Rl.C.mu0 i').val P : ℂˣ) : ℂ)⁻¹ ^ k * (((Nat.card (Formalism.L2.DIV.kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹) hL' := by
    intro y
    have h := hX.tie i' k P hsp hso hi h2 hkr α Rc ha hRc ((YS.fi i').e.symm y) rfl
    simp only [hL', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h ⊢
    exact h
  have hc := GlobalTheory.HeckeSup.comm_rho_cl (hR.lev.βW i') hR.fam.Sb hR.models.HW hR.models.gW (sg0 D A3.A) hd
    (GlobalTheory.ExportPin.Model.j_injective Rl hU i' _) (hU i' (sg0 D A3.A)).2.2 hH ((YS.fi i').eG g)
  apply (YS.fi i').e.injective
  have h := LinearMap.congr_fun hc ((YS.fi i').e x)
  simp only [hL', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h
  rw [(YS.fi i').rho, ← h, ← (YS.fi i').rho, LinearEquiv.symm_apply_apply]

theorem commAll_fullAll_raw (hR : Rl.Char3 F) (hU : Rl.toRealDat.LUnif) (hI : Rl.toRealDat.LIntegral)
    (hX : NExpHeckeRowX Rl cG S YS H fun _ => LinearMap.id)
    (hS0c : ∀ i P P', P ∈ D.ntw.S0 i → IsConjPl D.host P P' → P' ∈ D.ntw.S0 i)
    (hS02 : ∀ i, placesOver D.host.E 2 ⊆ (D.ntw.S0 i : Set (PlE D.host)))
    (hS0b : ∀ i, ∀ Q ∈ Rl.Sb, Q ∈ D.ntw.S0 i) : CommAll D ∧ FullAll D := by
  have hidx : ∀ j, 1 ≤ j → j ≤ D.R.m → ∃ i' : Fin D.R.m, (i' : ℕ) + 1 = j := fun j h1 h2 =>
    ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  refine ⟨?_, ?_⟩
  · intro i j hj b k P hk g x
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨i', rfl⟩ := hidx j h1 h2
    obtain ⟨-, hkr, hsp, hS0⟩ := hk
    obtain ⟨-, -, -, -, hso, -, h2P, -⟩ :=
      GlobalTheory.ConjPlaceOff.exists_conj_off D (D.ntw.S0 i) Rl.Sb P (hS0c i) (hS02 i) (hS0b i) hsp hS0
    have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
      intro h
      rw [Nat.cast_mul] at h
      rcases P.isPrime.mem_or_mem h with h | h
      · exact hS0 (D.ntw.placesOver_subset_exceptional i 0 h)
      · exact hS0 (D.ntw.placesOver_subset_exceptional i 1 h)
    have hc := hL_comm_raw Rl F cG YS H hR hU hX i' k P hsp hso ⟨i, hS0⟩ h2P hg hkr
    refine (YS.eF i _ b h1 h2).injective ?_
    rw [YS.act, H.hkEq i _ b h1 h2 k P _ hS0 hsp hkr, H.hkEq i _ b h1 h2 k P _ hS0 hsp hkr, YS.act, map_smul,
      hkFR_act S i _ b (H.hL _) (H.hs _ h1 h2) k P (YS.rho _ h1 h2) (YS.chi _ h1 h2) hc]
  · intro i j hj b
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨i', rfl⟩ := hidx j h1 h2
    have hF := iso_span (YS.fi i') (hI i').2.1.2
    have hB := Bsup_span S i ((i' : ℕ) + 1) b hF
    obtain ⟨c, hc0, -, hc2⟩ := YS.bsup i ((i' : ℕ) + 1) b h1 h2
    let e := YS.eF i ((i' : ℕ) + 1) b h1 h2
    have hc0' : algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) c ≠ 0 := by
      intro h0
      apply hc0
      apply IsFractionRing.injective (D.ntw.O i) (FractionRing (D.ntw.O i))
      rw [h0, map_zero]
    have hle : Submodule.span (FractionRing (D.ntw.O i)) (Bsup S i ((i' : ℕ) + 1) b : Set (Fm S i ((i' : ℕ) + 1) b)) ≤
        (Submodule.span (FractionRing (D.ntw.O i)) (D.nexp.Bsup i ((i' : ℕ) + 1) b : Set (D.nexp.Fm i ((i' : ℕ) + 1) b))).comap e.symm.toLinearMap := by
      refine Submodule.span_le.2 fun z hz => ?_
      have hm : c • e.symm z ∈ D.nexp.Bsup i ((i' : ℕ) + 1) b := hc2 _ (by simpa [e] using hz)
      have hm' : algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) c • e.symm z ∈
          Submodule.span (FractionRing (D.ntw.O i)) (D.nexp.Bsup i ((i' : ℕ) + 1) b : Set (D.nexp.Fm i ((i' : ℕ) + 1) b)) := by
        rw [algebraMap_smul]
        exact Submodule.subset_span hm
      have := Submodule.smul_mem _ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) c)⁻¹ hm'
      rw [inv_smul_smul₀ hc0'] at this
      exact this
    refine eq_top_iff.2 fun t _ => ?_
    have ht : e t ∈ Submodule.span (FractionRing (D.ntw.O i)) (Bsup S i ((i' : ℕ) + 1) b : Set (Fm S i ((i' : ℕ) + 1) b)) := by
      rw [hB]; exact Submodule.mem_top
    have := hle ht
    simpa using this

end Raw

end GlobalTheory.CommFullLayer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateHalfPrescribedAdjointFrameMatrix
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.AdjHalfLift

open GlobalTheory.AdelicLatMove

theorem gramInv_mul_gram {D : D7} (S : HSp D) : (S.gram⁻¹).map (eToEAf D) * S.gram.map (eToEAf D) = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S),
    Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]

theorem cF_cF {D : D7} (w : EAf D) : cF D (cF D w) = w := by
  obtain ⟨Z, -, rfl⟩ := GlobalTheory.HalfDuality.exists_lift (D := D) w
  exact GlobalTheory.PlaceVec.cF_cF_toEAf Z


set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_half_frMapAdj : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D), e * e = e → ∀ z : Matrix (Fin S.rank) (Fin T.rank) (EAf D), (∀ i j, toEAf D e * z i j = z i j) → ∃ y : WO S T, IsHalf (cA D e) y ∧ (∀ i j, infPart D (y i j) = 0) ∧ frMapAdj S T βS βT y = z := by
  intro D S T βS βT e hee z hz
  choose L hL0 hL using fun t : EAf D => GlobalTheory.HalfDuality.exists_lift (D := D) t
  let N : Matrix (Fin S.rank) (Fin T.rank) (EAf D) :=
    HMul.hMul (HMul.hMul (HMul.hMul (S.gram.map (eToEAf D)) βS.val) z) (HMul.hMul (βT⁻¹).val ((T.gram⁻¹).map (eToEAf D)))
  let X : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := Matrix.of fun i j => cF D (N j i)
  refine ⟨Matrix.of fun i j => cA D e * L (X i j), fun i j => ?_, fun i j => ?_, ?_⟩
  · simp only [Matrix.of_apply, ← mul_assoc, ← map_mul, hee]
  · simp only [Matrix.of_apply, map_mul, hL0, mul_zero]
  · have hcc : cF D (toEAf D (cA D e)) = toEAf D e := by
      rw [← toEAf_cA, GlobalTheory.DualPairCheck.cA_cA]
    have hY : (((Matrix.of fun i j => cA D e * L (X i j) : WO S T).map (toEAf D)).map (cF D))ᵀ = toEAf D e • N := by
      ext i j
      simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, map_mul, hL, X, cF_cF, hcc,
        Matrix.smul_apply, smul_eq_mul]
    rw [GlobalTheory.PlaceVec.frMapAdj_eq, hY, Matrix.mul_smul, Matrix.smul_mul]
    have e1 : HMul.hMul (HMul.hMul (HMul.hMul (βS⁻¹).val ((S.gram⁻¹).map (eToEAf D))) N)
        (HMul.hMul (T.gram.map (eToEAf D)) βT.val) = z :=
      GlobalTheory.PlaceVec.sandwich_cancel _ _ _ _ _ _ _ _ z (gramInv_mul_gram S) (Units.inv_mul βS)
        (gramInv_mul_gram T) (Units.inv_mul βT)
    rw [e1]
    exact Matrix.ext fun i j => hz i j

end GlobalTheory.AdjHalfLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspParamGoodRow
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.RowCuspFromLift

theorem isoInf_append (D : D7) (L L' : List (Part D.naut.CG)) (τ : D.host.E →+* ℂ) :
    isoInf D.nd D.naut (L ++ L') τ = isoInf D.nd D.naut L τ + isoInf D.nd D.naut L' τ := by
  unfold isoInf
  rw [List.map_append, List.sum_append]

theorem isoInf_perm (D : D7) {L L' : List (Part D.naut.CG)} (h : L.Perm L') (τ : D.host.E →+* ℂ) :
    isoInf D.nd D.naut L τ = isoInf D.nd D.naut L' τ := by
  unfold isoInf
  exact (h.map _).sum_eq

theorem eta_emb (s : Multiset ℂ) (h : s = {1 / 2} ∨ s = {-(1 / 2)}) :
    (s.map (fun z => -z) = {-(1 / 2)} → s = {1 / 2}) ∧ (s.map (fun z => -z) = {1 / 2} → s = {-(1 / 2)}) := by
  rcases h with rfl | rfl
  · refine ⟨fun _ => rfl, fun h' => ?_⟩
    rw [Multiset.map_singleton, Multiset.singleton_inj] at h'
    norm_num at h'
  · refine ⟨fun h' => ?_, fun _ => rfl⟩
    rw [Multiset.map_singleton, Multiset.singleton_inj] at h'
    norm_num at h'

theorem isoInf_one (D : D7) {a : ℕ} (ρ : D.naut.CG a) (τ : D.host.E →+* ℂ) :
    isoInf D.nd D.naut [⟨a, ρ, 1⟩] τ = D.naut.infG ρ τ := by
  simp [isoInf]

end GlobalTheory.RowCuspFromLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraCentreKeepsTypeSpacesAtLocalisations
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CenKeepsTypeLoc

theorem main : ∀ (D : D7) (M : MtFam D), AVTied D M → GlobalTheory.HeightCounting.Up.CenLoc D M → OnMtPreservesTypeV D := by
  intro D M A hC i PI z F hF
  by_cases hz : z ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))
  · obtain ⟨L, -, hL⟩ := hC i
    rw [NTypes.onMt, dite_eq_left hz]
    rw [A.typeV, Submodule.mem_comap] at hF ⊢
    have e : (M.loc i).real (D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) ⟨z, hz⟩ F) =
        actSum D L z ((M.loc i).real F) := hL ⟨z, hz⟩ F
    rw [e]
    unfold actSum Finsupp.sum
    exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (GlobalTheory.CenKeepsType.rt_mem_isoTyp _ _ _ _ hF)
  · rw [NTypes.onMt, dite_eq_right hz]
    exact Submodule.zero_mem _

end GlobalTheory.CenKeepsTypeLoc
end

