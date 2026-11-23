module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DiagonalQuotientEigen
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachDeltaInvariantCoboundaries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0054
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0310
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0290
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubstInvariants
section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.SenLines GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen GlobalTheory.CycFr GlobalTheory.WachTie

namespace GlobalTheory.SenLines

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {l : ℕ}

theorem isUnit_q_of_associated {m : ℕ} (h : Associated W.π₀₁ (X ^ m)) :
    IsUnit (algebraMap (LetA O n) W.EE (W.π₀ + ((PD.p : ℕ) : LetA O n))) := by
  obtain ⟨w, hw⟩ := h.symm
  have e : (W.π₀ : LetA O n) = letπ ^ m * fun _ => (w : O⟦X⟧) := funext fun _ => hw.symm
  have hu : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
    rw [e, map_mul, map_pow]
    exact (W.EE_π.pow _).mul (IsUnit.map _ (Pi.isUnit_iff.2 fun _ => w.isUnit))
  haveI := W.EE_complete
  have hJ := IsAdicComplete.le_jacobson_bot (Ideal.span {((PD.p : ℕ) : W.EE)})
    (Ideal.mem_span_singleton_self _)
  obtain ⟨u, hu⟩ := hu
  have h1 := (Ideal.mem_jacobson_bot.1 hJ (↑u⁻¹ : W.EE)).mul u.isUnit
  rw [map_add (f := _), map_natCast, ← hu]
  convert h1 using 1
  rw [add_mul, mul_assoc, Units.inv_mul]; ring

variable [Fact l.Prime] [IsDomain O] [CharZero O] [Algebra ℤ_[l] O] (hp : PD.p = l)
  (χ : W.Gam →* ℤ_[l]ˣ) (hχ : ∀ g, algebraMap ℤ_[l] O (χ g : ℤ_[l]) = (W.χΓ g : O))
include hp hχ

theorem exists_subst_invariants (ξ : O⟦X⟧) (hξ : Associated ξ (X ^ W.DelF.card))
    (h0 : constantCoeff ξ = 0) (hinv : ∀ δ ∈ W.DelF, W.γ₀ δ ξ = ξ) :
    ∃ j : O⟦X⟧ →ₐ[O] O⟦X⟧, j X = ξ ∧ Function.Injective j ∧
      ∀ a, (∃ b, j b = a) ↔ ∀ δ ∈ W.DelF, W.γ₀ δ a = a := by
  classical
  have hγ := γ₀_eq W hp χ hχ
  have hχi : Function.Injective χ := fun a b hab =>
    W.χΓ_inj (Units.ext (by rw [← hχ, ← hχ, hab]))
  let Δ : Subgroup ℤ_[l]ˣ := (CommGroup.torsion W.Gam).map χ
  have hΔ : (Δ : Set ℤ_[l]ˣ) = ↑(W.DelF.image χ) := by
    ext x
    simp only [Δ, Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, CommGroup.mem_torsion,
      Finset.coe_image, Finset.mem_coe, mem_DelF_iff]
  have hfa : ∀ p : ℤ_[l]ˣ → Prop, (∀ δ ∈ Δ, p δ) ↔ ∀ δ ∈ W.DelF, p (χ δ) := by
    intro p
    simp only [← SetLike.mem_coe, hΔ, Finset.coe_image, Set.forall_mem_image]
  haveI : Finite Δ := by
    change Finite (Δ : Set ℤ_[l]ˣ)
    rw [hΔ]; infer_instance
  have hcard : Nat.card Δ = W.DelF.card := by
    change Nat.card (Δ : Set ℤ_[l]ˣ) = _
    rw [hΔ, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_image_of_injective _ hχi]
  have hs : HasSubst ξ := HasSubst.of_constantCoeff_zero' h0
  have hX : (substAlgHom hs : O⟦X⟧ →ₐ[O] O⟦X⟧) X = ξ := by rw [coe_substAlgHom, subst_X hs]
  obtain ⟨h2, h3⟩ := injective_and_range_eq_invariants Δ (substAlgHom hs : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (by rw [hX, hcard]; exact hξ)
    ((hfa _).2 fun δ hδ => by rw [← hγ, hX]; exact hinv δ hδ)
  refine ⟨_, hX, h2, fun a => ?_⟩
  rw [h3, hfa]; simp only [hγ]

theorem exists_qFrame_of_card [IsNoetherianRing O] (hl : l ≠ 2) (hc : W.DelF.card = l - 1)
    (σ : O⟦X⟧ ≃ₐ[O] O⟦X⟧) (hσ : σ X = X + C (l : O)) (g : W.Gam)
    (hg : (l : ℤ_[l]) ∣ (χ g : ℤ_[l]) - 1) : ∃ J, QFrame W g J := by
  have h2l := (Fact.out : l.Prime).two_le
  have hl0 : (l : O) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨p2, p3, w, hw⟩ := π₀₁_spec W hp χ hχ hl hc
  have hq := (φ₀_eq W hp).2
  have hγ := γ₀_eq W hp χ hχ
  have hX0 : (X : O⟦X⟧) ∣ W.π₀₁ := (dvd_pow_self _ (by omega)).trans p2.symm.dvd
  have h0 := X_dvd_iff.1 hX0
  obtain ⟨j, hj, hji, hjr⟩ := exists_subst_invariants W hp χ hχ _ p2 h0 p3
  let J : O⟦X⟧ →ₐ[O] O⟦X⟧ := j.comp σ
  have hJ : ∀ c, J c = j (σ c) := fun _ => rfl
  have hσ' : σ X = X + (l : O⟦X⟧) := by rw [hσ, map_natCast]
  have hJX : J X = W.π₀₁ + (l : O⟦X⟧) := by rw [hJ, hσ', map_add (f := _), hj, map_natCast]
  have hσl : σ (X - (l : O⟦X⟧)) = X := by rw [map_sub, hσ', map_natCast]; ring
  have hr : ∀ a, (∃ b, J b = a) ↔ ∀ δ ∈ W.DelF, W.γ₀ δ a = a := fun a => by
    rw [← hjr]
    exact ⟨fun ⟨b, hb⟩ => ⟨σ b, hb⟩, fun ⟨b, hb⟩ => ⟨σ.symm b, by rw [hJ, σ.apply_symm_apply, hb]⟩⟩
  have hk : ∀ c, constantCoeff (J c) = 0 → X - (l : O⟦X⟧) ∣ c := fun c h => by
    rw [hJ, constantCoeff_algHom j (hj ▸ hX0)] at h
    rw [← map_dvd_iff σ, hσl, X_dvd_iff, h]
  have hc0 : constantCoeff (J X) = (l : O) := by rw [hJX, map_add (f := _), h0, map_natCast, zero_add]
  have hwu : IsUnit w := by
    have h1 := congrArg constantCoeff hw
    rw [← hJX, hc0, map_mul, show constantCoeff (lvl l O 0) = (l : O) by simp [lvl]] at h1
    rw [isUnit_iff_constantCoeff, ← mul_left_cancel₀ hl0 ((mul_one _).trans h1)]
    exact isUnit_one
  have hass : Associated (J X) (lvl l O 0) := by
    rw [hJX, hw]; exact associated_mul_unit_left _ _ hwu
  have hne : J X ≠ 0 := fun h => hl0 (by rw [← hc0, h, map_zero])
  obtain ⟨y, hy⟩ : J X * X ∣ W.γ₀ g (J X) - J X := by
    have h1 := dvd_act_sub (O := O) 1 (χ g) 1 (by rwa [pow_one]) (J X)
    have h2 := mul_lvl (l := l) (O := O) 0
    rw [pow_zero, pow_one, add_sub_cancel_left, zero_add] at h2
    rw [act_one, ← hγ, ← h2, mul_comm] at h1
    exact (mul_dvd_mul_right hass.dvd _).trans h1
  have hinv := (hr (J X)).1 ⟨X, rfl⟩
  obtain ⟨y', hy'⟩ := (hr (X * y)).2 fun δ hδ => by
    apply mul_left_cancel₀ hne
    have h1 := congrArg (W.γ₀ δ) hy
    rw [mul_assoc, map_mul, map_sub, hinv δ hδ, hγ δ, hγ g, act_comm, ← hγ δ, hinv δ hδ,
      ← hγ g, hy, mul_assoc] at h1
    exact h1.symm
  obtain ⟨z, hz⟩ := hk y' (by rw [hy']; simp)
  have hs : IsUnit (1 + y') := by
    rw [← MulEquiv.isUnit_map σ, hz, map_add (f := _), map_mul, hσl, isUnit_iff_constantCoeff]
    simp
  refine ⟨J, hji.comp σ.injective, hr, by rw [hp, hJX], by rw [hp]; exact hk,
    ⟨hs.unit, ?_, ?_⟩, hq ▸ hass, isUnit_q_of_associated W p2⟩
  · rw [hs.unit_spec, map_add (f := _), map_one, hy']
    linear_combination hy
  · rw [hp, hs.unit_spec, add_sub_cancel_left]
    exact ⟨z, hz⟩

end Generic

theorem exists_qFrame : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ} (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (g : W.Gam), CaseA K LL → ((W.χΓ g : (↥(OL LL))ˣ) : ↥(OL LL)) = 1 + (l : ↥(OL LL)) → IsUnit (W.DelF.card : ↥(OL LL)) ∧ ∃ J, QFrame W g J := by
  intro l _ P K LL n W g ⟨hK, hl, h⟩ hg
  have p1 : Module.finrank ↥(K0 K) ↥K.1 = 1 := by
    rw [Algebra.finrank_eq_one_iff_bijective_algebraMap]
    exact ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x.1, x.2, hK x.2⟩, rfl⟩⟩
  have hc := GlobalTheory.TorsionCard.card_torsion_mul_finrank P K LL W hl h.2.2.1
  rw [p1, mul_one] at hc
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.exists_cyclotomicChar_padicInt_units P K LL W
  obtain ⟨_, _, hu⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  obtain ⟨σ, hσ⟩ := GlobalTheory.NB.LT.exists_algEquiv_X_add_C (IsLocalRing.maximalIdeal ↥(OL LL))
    (l : ↥(OL LL)) hu
  refine ⟨?_, exists_qFrame_of_card W (P.PD_p K) χ hχ hl hc σ hσ g ?_⟩
  · have h1 := IsLocalRing.isUnit_or_isUnit_one_sub_self (l : ↥(OL LL))
    rw [hc, Nat.cast_sub (Fact.out : l.Prime).one_le, Nat.cast_one, ← IsUnit.neg_iff, neg_sub]
    exact h1.resolve_left hu
  · have h1 : (χ g : ℤ_[l]) = 1 + l := GlobalTheory.algebraMap_padicInt_OL_injective LL (by
      rw [hχ, hg, map_add (f := _), map_one, map_natCast])
    rw [h1, add_sub_cancel_left]

end GlobalTheory.SenLines
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineInequalityDcrisFiniteConcreteRings
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

namespace GlobalTheory.Per.FontaineBound

theorem dcris_finite_le_of_tied {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) :
    Module.Finite ↥LL.1 (Dcris (P.PD K) ρ) ∧
      finrank ↥LL.1 (Dcris (P.PD K) ρ) ≤ finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 V := by
  have := isDomain_cris (P.PD K) (isField_of_tied T)
  have := (P.PD K).finK₀
  have := LL.2
  refine finite_finrank_le (P.PD K).actB (fun b b' hb h => _root_.GlobalTheory.Per.FracInv.tied_frac_invariant l P AI T K b' b hb fun g hg => ?_) ρ
  have h1 := h ⟨g, hg⟩
  rw [P.PD_actB, P.PD_actB] at h1
  rw [mul_comm, h1, mul_comm]

theorem fontaineLe_of_tied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ K LL : FinExt l, FontaineLe (P.PD K) ↥LL.1 ∧
      ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
        [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V),
        FiniteDimensional ↥LL.1 ↥(Dcris (P.PD K) ρ) :=
  fun _ _ _ _ T K LL => ⟨fun V _ _ _ _ _ ρ => (dcris_finite_le_of_tied T K LL V ρ).2,
    fun V _ _ _ _ _ ρ => (dcris_finite_le_of_tied T K LL V ρ).1⟩

end GlobalTheory.Per.FontaineBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineInequalityDcrisFiniteConcreteRingsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaine_inequality_dcris_finite_concrete_rings : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K LL : FinExt l, FontaineLe (P.PD K) ↥LL.1 ∧ ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), FiniteDimensional ↥LL.1 ↥(Dcris (P.PD K) ρ) := by
  intro l _ P AI T K LL
  have key : ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
      [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V),
      Module.Finite ↥LL.1 (Dcris (P.PD K) ρ) ∧
        Module.finrank ↥LL.1 (Dcris (P.PD K) ρ) ≤ Module.finrank ℚ_[l] ↥(K0 K) * Module.finrank ↥LL.1 V := by
    intro V _ _ _ _ _ ρ
    have := GlobalTheory.Per.FontaineBound.isDomain_cris (PD := P.PD K) (GlobalTheory.Per.FontaineBound.isField_of_tied T)
    have := (P.PD K).finK₀
    have := LL.2
    refine GlobalTheory.Per.FontaineBound.finite_finrank_le (P.PD K).actB (fun b b' hb h => GlobalTheory.Per.FracInv.tied_frac_invariant l P AI T K b' b hb fun g hg => ?_) ρ
    have h1 := h ⟨g, hg⟩
    rw [P.PD_actB, P.PD_actB] at h1
    rw [mul_comm, h1, mul_comm]
  exact ⟨fun V _ _ _ _ _ ρ => (key V ρ).2, fun V _ _ _ _ _ ρ => (key V ρ).1⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobXiDivPrimeUnitTendstoOne
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.PhiXiUnit

variable {l : ℕ} [Fact l.Prime]

theorem phiA_alg (x : Per.Ainf l) :
    phiA l (algebraMap (Per.Ainf l) (Per.Acris l) x) =
      algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l x) :=
  (GlobalTheory.CrisMaps.phiA_extends l).alg x

theorem φA_tm (x : Per.Fl l) : Per.φA l (Per.tm x) = Per.tm x ^ l := by
  rw [← map_pow]
  exact GlobalTheory.RingIface.phiA_teich l x

theorem φA_tm_root (e : Per.Fl l) :
    Per.φA l (Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e)) = Per.tm e := by
  rw [φA_tm, ← map_pow, ← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]

theorem φA_xi (e : Per.Fl l) :
    Per.φA l (xi e) = ∑ i ∈ Finset.range l, Per.tm e ^ i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [xi, map_sum]
  simp only [map_pow, φA_tm_root]

theorem φA_mu (e : Per.Fl l) : Per.φA l (mu e) = mu e * Per.φA l (xi e) := by
  rw [φA_xi, mu, map_sub, map_one, φA_tm, mul_comm, geom_sum_mul]

theorem φA_xi_sub (e : Per.Fl l) :
    ∃ s : Per.Ainf l, Per.φA l (xi e) - (l : Per.Ainf l) = mu e * s := by
  refine ⟨∑ i ∈ Finset.range l, ∑ j ∈ Finset.range i, Per.tm e ^ j, ?_⟩
  have h : (l : Per.Ainf l) = ∑ i ∈ Finset.range l, (1 : Per.Ainf l) := by simp
  rw [φA_xi, mu, Finset.mul_sum, h, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, geom_sum_mul]

theorem cancel_mu (C : Core l) (x y : Per.Acris l)
    (h : algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε) * x =
      algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε) * y) : x = y := by
  have he := _root_.GlobalTheory.MemLoc.core_isEps l C
  have hU : IsUnit (algebraMap (Per.Acris l) (Per.Bcris l)
      (algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε))) :=
    GlobalTheory.MemLoc.TFil.isUnit_mu he
  apply GlobalTheory.MemLoc.AwayT.acris_injective C
  apply hU.mul_left_cancel
  rw [← map_mul, ← map_mul, h]

theorem exists_unit (C : Core l) : ∃ u : Per.Acris l, IsUnit u ∧
    (l : Per.Acris l) * u = algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l (xi C.ε)) := by
  have he := _root_.GlobalTheory.MemLoc.core_isEps l C
  obtain ⟨t, ρ, ht, hρ, htρ⟩ := _root_.GlobalTheory.MemLoc.exists_isLogA l C.ε he.1
  have h1 : t = C.t := (_root_.GlobalTheory.MemLoc.LogFun.log_fun l C.ε C.t he.1 C.t_log).1 t ht
  have hφt := _root_.GlobalTheory.MemLoc.TPhi.t_phi l C
  rw [← h1, htρ, map_mul, phiA_alg, φA_mu, map_mul, mul_assoc, mul_left_comm (l : Per.Acris l)] at hφt
  have h2 := cancel_mu C _ _ hφt
  have hφρ : IsUnit (phiA l ρ) := hρ.map _
  refine ⟨ρ * ↑hφρ.unit⁻¹, hρ.mul (Units.isUnit _), ?_⟩
  rw [← mul_assoc, ← h2, mul_assoc, IsUnit.mul_val_inv, mul_one]

theorem iterate_sub_one (C : Core l) (u : Per.Acris l)
    (hu : (l : Per.Acris l) * u = algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l (xi C.ε))) :
    ∀ r : ℕ, ∃ M : ℕ, ∀ m ≥ M, (⇑(phiA l))^[m] u - 1 ∈ Ideal.span {(l : Per.Acris l)} ^ r := by
  set a := algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε) with ha_def
  have ha : phiA l a = a * ((l : Per.Acris l) * u) := by
    rw [ha_def, phiA_alg, φA_mu, map_mul, hu]
  have hdvd : ∀ m : ℕ, (l : Per.Acris l) ^ m ∣ (phiA l ^ m) a := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [RingHom.coe_pow, Function.iterate_succ_apply, ha, ← RingHom.coe_pow, map_mul, map_mul,
        map_natCast, pow_succ]
      obtain ⟨c, hc⟩ := ih
      rw [hc]
      exact ⟨c * (phiA l ^ m) u, by ring⟩
  obtain ⟨s, hs⟩ := φA_xi_sub C.ε
  have hls : (l : Per.Acris l) * u - l = a * algebraMap (Per.Ainf l) (Per.Acris l) s := by
    rw [hu, ← map_natCast (algebraMap (Per.Ainf l) (Per.Acris l)) l, ← map_sub, hs, map_mul]
  have key : ∀ m : ℕ, (l : Per.Acris l) * ((phiA l ^ m) u - 1) =
      (phiA l ^ m) a * (phiA l ^ m) (algebraMap (Per.Ainf l) (Per.Acris l) s) := by
    intro m
    rw [← map_mul, ← hls, map_sub, map_mul, map_natCast, mul_sub, mul_one]
  have tf := (GlobalTheory.MemLoc.acris_basic l).2.1
  intro r
  refine ⟨r + 1, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [← RingHom.coe_pow]
  obtain ⟨c, hc⟩ := hdvd (k + 1)
  have h3 : (phiA l ^ (k + 1)) u - 1 =
      (l : Per.Acris l) ^ k * (c * (phiA l ^ (k + 1)) (algebraMap (Per.Ainf l) (Per.Acris l) s)) := by
    rw [← sub_eq_zero]
    apply tf
    rw [mul_sub, key, hc, pow_succ]
    ring
  have h4 : (phiA l ^ (k + 1)) u - 1 ∈ Ideal.span {(l : Per.Acris l)} ^ k := by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, h3]
    exact dvd_mul_right _ _
  exact Ideal.pow_le_pow_right (by omega) h4

end GlobalTheory.MemLoc.PhiXiUnit

theorem GlobalTheory.MemLoc.phi_xi_unit_tendsto : ∀ (l : ℕ) [Fact l.Prime] (C : GlobalTheory.MemLoc.Core l),
    ∃ u : Per.Acris l, IsUnit u ∧
      (l : Per.Acris l) * u = algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l (GlobalTheory.MemLoc.xi C.ε)) ∧
      ∀ r : ℕ, ∃ M : ℕ, ∀ m ≥ M,
        (⇑(GlobalTheory.MemLoc.phiA l))^[m] u - 1 ∈ Ideal.span {(l : Per.Acris l)} ^ r := by
  intro l _ C
  obtain ⟨u, hu, hlu⟩ := GlobalTheory.MemLoc.PhiXiUnit.exists_unit C
  exact ⟨u, hu, hlu, GlobalTheory.MemLoc.PhiXiUnit.iterate_sub_one C u hlu⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEigenFilOneIsUnitExactDegree
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.EigenDegree

theorem abstract {B D : Type} [CommRing B] [CommRing D] [IsDomain D] (ι : B →+* D)
    (hι : Function.Injective ι) (φ : B →+* B) (F : ℤ → D → Prop) (h1 : F 0 1)
    (hmul : ∀ a b x y, F a x → F b y → F (a + b) (x * y)) (p t : B) (hp : IsUnit p) (ht : IsUnit t)
    (hφt : φ t = p * t) (ht2 : ¬ F 2 (ι t)) (hsucc : ∀ y, F 1 y → ∃ z, F 0 z ∧ y = ι t * z)
    (hfund : ∀ b, φ b = b → F 0 (ι b) → b ≠ 0 → ∃ c, c * b = 1 ∧ F 0 (ι c))
    (n : ℕ) (hn : 0 < n) (x : B) (hx : (⇑φ)^[n] x = p * x) (hx0 : x ≠ 0) (hx1 : F 1 (ι x))
    (hj0 : ∀ j, j < n → F 0 (ι ((⇑φ)^[j] x))) :
    IsUnit x ∧ ¬ F 2 (ι x) ∧ ∀ j, 0 < j → j < n → ¬ F 1 (ι ((⇑φ)^[j] x)) := by
  haveI : IsDomain B := hι.isDomain ι
  have hprod : ∀ (d : ℕ → ℤ) (f : ℕ → D) (s : Finset ℕ), (∀ i ∈ s, F (d i) (f i)) →
      F (∑ i ∈ s, d i) (∏ i ∈ s, f i) := by
    intro d f s
    induction s using Finset.induction_on with
    | empty => intro _; simpa using h1
    | insert a s ha ih =>
      intro h
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      exact hmul _ _ _ _ (h a (Finset.mem_insert_self _ _))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
  have hne : ∀ j, j < n → (⇑φ)^[j] x ≠ 0 := by
    intro j hj h
    have e : (⇑φ)^[n] x = 0 := by
      rw [← Nat.sub_add_cancel hj.le, Function.iterate_add_apply, h, iterate_map_zero]
    rw [hx] at e
    exact mul_ne_zero hp.ne_zero hx0 e
  obtain ⟨N, hN⟩ : ∃ N, N = ∏ j ∈ Finset.range n, (⇑φ)^[j] x := ⟨_, rfl⟩
  have hN0 : N ≠ 0 := by
    rw [hN]
    exact Finset.prod_ne_zero_iff.2 fun j hj => hne j (Finset.mem_range.1 hj)
  have hφN : φ N = p * N := by
    apply mul_right_cancel₀ hx0
    have e1 := Finset.prod_range_succ (fun j => (⇑φ)^[j] x) n
    have e2 := Finset.prod_range_succ' (fun j => (⇑φ)^[j] x) n
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply] at e2
    rw [← map_prod, ← hN, e1, ← hN, hx] at e2
    rw [← e2]
    ring
  have hN1 : F 1 (ι N) := by
    have := hprod (fun i => if i = 0 then 1 else 0) (fun i => ι ((⇑φ)^[i] x)) (Finset.range n) (by
      intro i hi
      split_ifs with h
      · subst h; exact hx1
      · exact hj0 i (Finset.mem_range.1 hi))
    rw [← map_prod, ← hN] at this
    simpa [hn] using this
  obtain ⟨s, hs⟩ := ht.exists_right_inv
  obtain ⟨z, hz, hz'⟩ := hsucc _ hN1
  have hb : t * (s * N) = N := by rw [← mul_assoc, hs, one_mul]
  have hφb : φ (s * N) = s * N := by
    apply (hp.mul ht).mul_left_cancel
    rw [← hφt, ← map_mul, hb, hφN, hφt, mul_assoc, hb]
  have hbz : ι (s * N) = z := by
    rw [map_mul, hz', ← mul_assoc, ← map_mul, mul_comm s, hs, map_one, one_mul]
  obtain ⟨c, hc, hc0⟩ := hfund _ hφb (hbz ▸ hz) (fun h => hN0 (by rw [← hb, h, mul_zero]))
  have htc : t = c * N := by
    calc t = t * (c * (s * N)) := by rw [hc, mul_one]
      _ = c * (t * (s * N)) := by ring
      _ = c * N := by rw [hb]
  have hNu : IsUnit N := isUnit_of_mul_isUnit_right (htc ▸ ht)
  have hN2 : ¬ F 2 (ι N) := by
    intro h
    apply ht2
    have := hmul _ _ _ _ hc0 h
    rwa [zero_add, ← map_mul, ← htc] at this
  have key : ∀ j, j < n → ¬ F ((if j = 0 then 1 else 0) + 1) (ι ((⇑φ)^[j] x)) := by
    intro j hj h
    apply hN2
    have := hprod (fun i => (if i = 0 then 1 else 0) + (if i = j then 1 else 0))
      (fun i => ι ((⇑φ)^[i] x)) (Finset.range n) (by
      intro i hi
      by_cases hij : i = j
      · subst hij
        simpa using h
      · by_cases h0 : i = 0
        · subst h0
          simpa [hij] using hx1
        · simpa [hij, h0] using hj0 i (Finset.mem_range.1 hi))
    rw [← map_prod, ← hN, Finset.sum_add_distrib] at this
    simpa [hn, hj, one_add_one_eq_two] using this
  refine ⟨?_, ?_, fun j h0 hj => ?_⟩
  · refine isUnit_of_dvd_unit ?_ hNu
    rw [hN]
    exact Finset.dvd_prod_of_mem (fun j => (⇑φ)^[j] x) (Finset.mem_range.2 hn)
  · simpa [one_add_one_eq_two] using key 0 hn
  · simpa [h0.ne'] using key j hj

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem main : ∀ (l : ℕ) [Fact l.Prime] (C : GlobalTheory.MemLoc.Core l) (n : ℕ), 0 < n → ∀ x : Per.Bcris l,
    (⇑(Per.φB l))^[n] x = (l : Per.Bcris l) * x → x ≠ 0 → C.ι x ∈ Per.FilD l 1 →
    (∀ j : ℕ, j < n → C.ι ((⇑(Per.φB l))^[j] x) ∈ Per.FilD l 0) →
    IsUnit x ∧ C.ι x ∉ Per.FilD l 2 ∧
      ∀ j : ℕ, 0 < j → j < n → C.ι ((⇑(Per.φB l))^[j] x) ∉ Per.FilD l 1 := by
  intro l _ C n hn x hx hx0 hx1 hj0
  obtain ⟨-, h1, hmul, -, -, -, hP⟩ := filD_laws l
  obtain ⟨htu, -, ht2, hlu⟩ := core_t_unit_fil l C
  have he := core_isEps l C
  have hlog := (LogFun.log_fun l C.ε C.t he.1 C.t_log).2.2.2 C.j C.j_cris
  haveI : IsDomain (Per.BdR l) := (BdRField.bdR_isField l).2.2.1.isDomain
  refine abstract C.ι (ULaws.u_laws l C).2.2.2.1 (Per.φB l) (fun a y => y ∈ Per.FilD l a) h1 hmul
    (l : Per.Bcris l) (algebraMap (Per.Acris l) (Per.Bcris l) C.t) hlu htu ?_ ?_ ?_ ?_ n hn x hx hx0 hx1 hj0
  · rw [fund_phiB_alg, TPhi.t_phi l C, map_mul, map_natCast]
  · intro h
    rw [C.ι_j] at h
    exact ht2 ((hP 2 _).1 h)
  · intro y hy
    obtain ⟨z, hz, e⟩ := (TiedUnif.filD_succ he hlog 0 y).1 (by rwa [zero_add])
    exact ⟨z, hz, by rw [C.ι_j]; exact e⟩
  · intro b hb hb0 hne
    obtain ⟨c, rfl⟩ := fundamental_exact l C b hb hb0
    have hc : c ≠ 0 := by
      rintro rfl
      exact hne (by rw [map_zero, map_zero])
    refine ⟨C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c⁻¹), ?_, ?_⟩
    · rw [← map_mul, ← map_mul, inv_mul_cancel₀ hc, map_one, map_one]
    · show C.ι _ ∈ _
      rw [C.ι_u]
      exact TiedUnif.alg_mem_FilD_zero _

end GlobalTheory.MemLoc.EigenDegree
end

