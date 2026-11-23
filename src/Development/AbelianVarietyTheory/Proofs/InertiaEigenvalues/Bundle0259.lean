module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0233
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousFixingSubgroupEquiv
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.TiedUnif

theorem zpow_form {R : Type} [CommRing R] (u : Rˣ) (a : ℤ) (x w : R) :
    x * (u : R) ^ (-a).toNat = (u : R) ^ a.toNat * w ↔ x = ((u ^ a : Rˣ) : R) * w := by
  rcases le_total 0 a with h | h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp
  · obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat h
    simp only [neg_neg, Int.toNat_natCast, Int.toNat_neg_natCast, pow_zero, one_mul, zpow_neg,
      zpow_natCast]
    rw [Units.eq_inv_mul_iff_mul_eq, Units.val_pow_eq_pow_val, mul_comm]

variable {l : ℕ} [Fact l.Prime]

def piOne (e : Per.Fl l) : Per.Ainf l := Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e) - 1

theorem mu_eq (e : Per.Fl l) : mu e = xi e * piOne e := by
  have h : (Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e)) ^ l = Per.tm e := by
    rw [← map_pow, frobeniusEquiv_symm_pow_p]
  rw [mu, piOne, xi, geom_sum_mul, h]

theorem theta_piOne {e : Per.Fl l} (he : IsEps e) : Per.θD l (aDp l (piOne e)) ≠ 0 := by
  rw [(thetaD_props l).2.2.2.1]
  intro h
  apply he.2
  have h' : Per.θ l (piOne e) = 0 := Subtype.ext h
  rw [piOne, map_sub, map_one, WittVector.fontaineTheta_teichmuller, sub_eq_zero] at h'
  exact h'

theorem theta_xi {e : Per.Fl l} (he : IsEps e) : Per.θD l (aDp l (xi e)) = 0 := by
  rw [(thetaD_props l).2.2.2.1, (theta_eq_zero_iff_xi_dvd l e he _).2 dvd_rfl]
  rfl

theorem ev_aDp (n : ℕ) (a : Per.Ainf l) :
    Per.ev l n (aDp l a) = Ideal.Quotient.mk _ (algebraMap (Per.Ainf l) (Per.AinfP l) a) := by
  rw [aDp, RingHom.comp_apply, GlobalTheory.RingIface.ev_alg]

theorem mem_filtration_iff_eval_eq_zero' {e : Per.Fl l} (he : IsEps e) (n : ℕ) (y : Per.BdRp l) :
    y ∈ Per.FilP l n ↔ Per.ev l n y = 0 := by
  obtain ⟨E, hE, hev⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
  rw [(filtration_eq_xi_pow l e he).1, ← hev, FilPrincipal.evalₐ_eq_zero_iff (_root_.GlobalTheory.MemLoc.ker_localizedTheta_eq_span_xi l e he), ← hE,
    ← map_pow E, map_dvd_iff E, aDp, RingHom.comp_apply]

theorem mu_sub_log {e : Per.Fl l} (he : IsEps e) {y : Per.BdRp l} (hy : Per.IsLog l e y) :
    aDp l (mu e) - y ∈ Per.FilP l 2 := by
  have h2 := GlobalTheory.CrisIncl.factorial_mul_ev l e y he.1 hy 2
  have hsq : Per.ev l 2 (aDp l (mu e ^ 2)) = 0 := by
    refine (mem_filtration_iff_eval_eq_zero' he 2 _).1 (((filtration_eq_xi_pow l e he).1 2 _).2 ?_)
    rw [mu_eq, map_pow, map_mul, mul_pow]
    exact dvd_mul_right _ _
  rw [ev_aDp, map_pow, map_pow] at hsq
  have hu : IsUnit (((2 : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ 2)) := by
    have := (GlobalTheory.RingBasics.isUnit_nat l 2 two_ne_zero).map (Ideal.Quotient.mk (Per.kerP l ^ 2))
    rwa [map_natCast] at this
  rw [mem_filtration_iff_eval_eq_zero' he, map_sub, ev_aDp, sub_eq_zero]
  apply hu.mul_left_cancel
  have hf : Nat.factorial 2 = 2 := rfl
  rw [hf] at h2
  rw [h2]
  change _ = Ideal.Quotient.mk _ (∑ k ∈ Finset.range 2, (-1) ^ k * ((2 / (k + 1) : ℕ) : Per.AinfP l) *
      (algebraMap (Per.Ainf l) (Per.AinfP l) (mu e)) ^ (k + 1))
  rw [Finset.sum_range_succ, Finset.sum_range_one, map_add (f := _), map_mul _ _ (_ ^ (1 + 1)), map_pow _ _ (1 + 1),
    show (1 + 1 : ℕ) = 2 from rfl, hsq]
  simp [map_ofNat]

theorem log_eq_xi_mul {e : Per.Fl l} (he : IsEps e) {y : Per.BdRp l} (hy : Per.IsLog l e y) :
    ∃ v : Per.BdRp l, IsUnit v ∧ y = aDp l (xi e) * v := by
  obtain ⟨w, hw⟩ := ((filtration_eq_xi_pow l e he).1 2 _).1 (mu_sub_log he hy)
  refine ⟨aDp l (piOne e) - aDp l (xi e) * w, (thetaD_props l).2.2.1 _ ?_, ?_⟩
  · rw [map_sub, map_mul, theta_xi he, zero_mul, sub_zero]
    exact theta_piOne he
  · rw [mu_eq, map_mul] at hw
    linear_combination -hw

theorem isUnit_xi {e : Per.Fl l} (he : IsEps e) :
    IsUnit (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e))) := by
  obtain ⟨hd, hinj, hF, -⟩ := BdRField.bdR_isField l
  have h0 : algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) ≠ 0 := by
    intro h
    have h1 : aDp l (xi e) = 0 := hinj (by rw [h, map_zero])
    exact one_ne_zero ((filtration_eq_xi_pow l e he).2.1 1 (by rw [h1, zero_mul]))
  obtain ⟨b, hb⟩ := hF.mul_inv_cancel h0
  exact IsUnit.of_mul_eq_one b hb

theorem mem_FilD_iff {e : Per.Fl l} (he : IsEps e) (a : ℤ) (x : Per.BdR l) :
    x ∈ Per.FilD l a ↔ ∃ w : Per.BdRp l,
      x = (((isUnit_xi he).unit ^ a : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) w := by
  rw [mem_FilD_iff_xi_pow l e he]
  refine exists_congr fun w => ?_
  rw [← zpow_form, IsUnit.unit_spec, map_mul, map_pow]

theorem filD_succ {e : Per.Fl l} (he : IsEps e) {y : Per.BdRp l} (hy : Per.IsLog l e y) (a : ℤ)
    (x : Per.BdR l) : x ∈ Per.FilD l (a + 1) ↔
      ∃ z ∈ Per.FilD l a, x = algebraMap (Per.BdRp l) (Per.BdR l) y * z := by
  obtain ⟨v, hv, rfl⟩ := log_eq_xi_mul he hy
  obtain ⟨v', hv'⟩ := hv.exists_right_inv
  have hv2 := congrArg (algebraMap (Per.BdRp l) (Per.BdR l)) hv'
  rw [map_mul, map_one] at hv2
  rw [mem_FilD_iff he, zpow_add_one, Units.val_mul, IsUnit.unit_spec, map_mul]
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨_, (mem_FilD_iff he a _).2 ⟨v' * w, rfl⟩, ?_⟩
    rw [map_mul]
    linear_combination (-((((isUnit_xi he).unit ^ a : (Per.BdR l)ˣ) : Per.BdR l) *
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) * algebraMap (Per.BdRp l) (Per.BdR l) w)) * hv2
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨w, rfl⟩ := (mem_FilD_iff he a _).1 hz
    exact ⟨v * w, by rw [map_mul]; ring⟩

theorem alg_mem_FilD (n : ℕ) {z : Per.BdRp l} (hz : z ∈ Per.FilP l n) :
    algebraMap (Per.BdRp l) (Per.BdR l) z ∈ Per.FilD l n :=
  GlobalTheory.RingIface.alg_mem_FilD_nat l hz

theorem exists_isEps_pt (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, ε, h0, -, h1, h⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  refine ⟨ε, ?_, fun hh => h1 ?_⟩
  · have := h 0
    rw [h0, map_one] at this
    exact Subtype.ext this
  · apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← h 1, map_one]
    exact congrArg Subtype.val hh

theorem alg_mem_FilD_zero (z : Per.BdRp l) :
    algebraMap (Per.BdRp l) (Per.BdR l) z ∈ Per.FilD l 0 := by
  obtain ⟨e, he⟩ := exists_isEps_pt l
  exact alg_mem_FilD 0 (((filtration_eq_xi_pow l e he).1 0 z).2 (by rw [pow_zero]; exact one_dvd z))

theorem eD_ιA {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (a : Ainf l) :
    T.eD (P.ιB (AI.ιA a)) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a) := by
  have h := GlobalTheory.CrisIncl.incl_aB l _ T.incl a
  rw [← T.ιA] at h
  have h2 : T.eD (P.ιB (T.eB.symm (T.eB (AI.ιA a)))) = _ := h
  rw [RingEquiv.symm_apply_apply] at h2
  exact h2

theorem tied_uniformiser : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → (∀ K : FinExt l, P.ιB (AI.ιA AI.μ) - P.ιB P.tB ∈ (P.PD K).Fil 2) ∧ (∀ K : FinExt l, ∃ u ∈ (P.PD K).Fil 0, P.ιB (AI.ιA AI.π₁) * u = 1) ∧ ∀ (K : FinExt l) (a : ℤ) (x : P.R.BdR), x ∈ (P.PD K).Fil (a + 1) ↔ ∃ y ∈ (P.PD K).Fil a, x = P.ιB P.tB * y := by
  intro l _ P AI T
  obtain ⟨C, hC⟩ := FitsEx.exists_fits l P AI T
  have he : IsEps AI.ε := hC.ε ▸ core_isEps l C
  obtain ⟨y, hy, ht⟩ := T.t
  refine ⟨fun K => ?_, fun K => ?_, fun K a x => ?_⟩
  · rw [T.fil, map_sub, eD_ιA T, ht, ← map_sub]
    exact alg_mem_FilD 2 (mu_sub_log he hy)
  · obtain ⟨v, hv⟩ := ((thetaD_props l).2.2.1 _ (theta_piOne he)).exists_right_inv
    refine ⟨T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) v), ?_, T.eD.injective ?_⟩
    · rw [T.fil, RingEquiv.apply_symm_apply]
      exact alg_mem_FilD_zero v
    · rw [map_mul, RingEquiv.apply_symm_apply, eD_ιA T, ← map_mul, map_one]
      exact (congrArg _ hv).trans (map_one _)
  · rw [T.fil, filD_succ he hy]
    constructor
    · rintro ⟨z, hz, e⟩
      refine ⟨T.eD.symm z, ?_, T.eD.injective ?_⟩
      · rwa [T.fil, RingEquiv.apply_symm_apply]
      · rw [map_mul, RingEquiv.apply_symm_apply, ht, e]
    · rintro ⟨z, hz, rfl⟩
      exact ⟨T.eD z, (T.fil K a z).1 hz, by rw [map_mul, ht]⟩

end GlobalTheory.MemLoc.TiedUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLayerIff
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.Cyc.LayerGroup

variable {l : ℕ} [Fact l.Prime]

theorem mem_layer_iff (K : FinExt l) (s : ℕ) (σ : GQ l) :
    σ ∈ Gj K s ↔ (∀ x ∈ K0 K, σ x = x) ∧ ∀ x : Om l, x ^ (l ^ s) = 1 → σ x = x := by

  have key : ∀ x : Om l,
      x ∈ IntermediateField.fixedField (Subgroup.zpowers (σ : Om l ≃ₐ[ℚ_[l]] Om l)) ↔ σ x = x := by
    intro x
    rw [IntermediateField.mem_fixedField_iff]
    refine ⟨fun h => h σ (Subgroup.mem_zpowers σ), fun h f hf => ?_⟩
    have hst : Subgroup.zpowers (σ : Om l ≃ₐ[ℚ_[l]] Om l) ≤
        MulAction.stabilizer (Om l ≃ₐ[ℚ_[l]] Om l) x :=
      Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr h)
    exact MulAction.mem_stabilizer_iff.mp (hst hf)
  unfold Gj Ks
  rw [IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf,
    IntermediateField.mem_fixingSubgroup_iff, ← Subgroup.zpowers_le,
    ← IntermediateField.le_iff_le, IntermediateField.adjoin_le_iff]
  exact and_congr Iff.rfl ⟨fun h x hx => (key x).mp (h hx), fun h x hx => (key x).mpr (h x hx)⟩

private theorem absoluteGalois_apply_eq_self_of_mem_maxUnramified (K : FinExt l) {τ : GQ l} (hτ : τ ∈ GK K) {x : Om l} (hx : x ∈ K0 K) :
    τ x = x := by
  unfold K0 at hx
  exact (IntermediateField.mem_fixingSubgroup_iff K.1 τ).mp hτ x (SetLike.le_def.mp inf_le_left hx)

theorem normal_layer (K : FinExt l) (s : ℕ) : ((Gj K s).subgroupOf (GK K)).Normal := by

  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hg : (g : GQ l) ∈ GK K := g.2
  have hgi : ((g : GQ l))⁻¹ ∈ GK K := inv_mem hg
  rw [mem_layer_iff] at hn ⊢
  obtain ⟨h0, h1⟩ := hn
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · change (g : GQ l) ((n : GQ l) (((g : GQ l))⁻¹ x)) = x
    rw [absoluteGalois_apply_eq_self_of_mem_maxUnramified K hgi hx, h0 x hx, absoluteGalois_apply_eq_self_of_mem_maxUnramified K hg hx]
  · change (g : GQ l) ((n : GQ l) (((g : GQ l))⁻¹ x)) = x
    have hy : (((g : GQ l))⁻¹ x) ^ (l ^ s) = 1 := by rw [← map_pow, hx, map_one]
    rw [h1 _ hy]
    exact AlgEquiv.apply_symm_apply (g : GQ l) x

theorem layer_group : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), K.1 ≤ Ks K s → ((Gj K s).subgroupOf (GK K)).Normal ∧ ((Gj K s).subgroupOf (GK K)).FiniteIndex ∧ IsOpen (((Gj K s).subgroupOf (GK K) : Subgroup ↥(GK K)) : Set ↥(GK K)) ∧ padicValNat l ((Gj K s).subgroupOf (GK K)).index = padicValNat l (Module.finrank ℚ_[l] ↥(Ks K s)) - padicValNat l (Module.finrank ℚ_[l] ↥K.1) := by
  intro l _ K s h
  have : IsGalois ℚ_[l] (Om l) := IsAlgClosure.isGalois ℚ_[l] (AlgebraicClosure ℚ_[l])
  have : FiniteDimensional ℚ_[l] (Ks K s) := GlobalTheory.Cyc.TwistLift.finite_Ks K s
  have : FiniteDimensional ℚ_[l] K.1 := K.2
  have hle : Gj K s ≤ GK K := IntermediateField.fixingSubgroup_le h

  have hKs : Module.finrank ℚ_[l] (Ks K s) = (Gj K s).index :=
    IntermediateField.finrank_eq_fixingSubgroup_index _ (Ks K s)
  have hK : Module.finrank ℚ_[l] K.1 = (GK K).index :=
    IntermediateField.finrank_eq_fixingSubgroup_index _ K.1
  have hmul : ((Gj K s).subgroupOf (GK K)).index * (GK K).index = (Gj K s).index :=
    Subgroup.relIndex_mul_index hle
  have hKpos : 0 < Module.finrank ℚ_[l] K.1 := Module.finrank_pos
  have hKspos : 0 < Module.finrank ℚ_[l] (Ks K s) := Module.finrank_pos
  have hidx : ((Gj K s).subgroupOf (GK K)).index ≠ 0 := by
    intro h0
    rw [h0, zero_mul, ← hKs] at hmul
    omega
  refine ⟨normal_layer K s, ⟨hidx⟩, ?_, ?_⟩
  · exact (IntermediateField.fixingSubgroup_isOpen (Ks K s)).preimage continuous_subtype_val
  · rw [hKs, ← hmul, ← hK, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hidx hKpos.ne']
    omega

end GlobalTheory.Cyc.LayerGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonicIrreducibleInjectRegularCharacterOrbits
section
open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.PrimeLabOrbit

variable {g : ℕ} [hg : Fact g.Prime]

theorem aeval_pow_frob {K : Type} [Field K] [Algebra (ZMod g) K] (n : ℕ) (Q : (ZMod g)[X]) (y : K) :
    aeval (y ^ g ^ n) Q = (aeval y Q) ^ g ^ n := by
  haveI : CharP K g := (Algebra.charP_iff (ZMod g) K g).1 (ZMod.charP g)
  haveI : ExpChar K g := ExpChar.prime hg.out
  rw [← iterateFrobenius_def g n y, ← iterateFrobenius_def g n (aeval y Q), aeval_def, aeval_def, hom_eval₂]
  congr 1
  exact Subsingleton.elim _ _

theorem frob_injective {K : Type} [Field K] [Algebra (ZMod g) K] (n : ℕ) :
    Function.Injective (fun y : K => y ^ g ^ n) := by
  haveI : CharP K g := (Algebra.charP_iff (ZMod g) K g).1 (ZMod.charP g)
  haveI : ExpChar K g := ExpChar.prime hg.out
  intro a b h
  apply (iterateFrobenius K g n).injective
  simpa only [iterateFrobenius_def] using h

theorem card_le_of_gen_fixed {L : Type} [Field L] [Algebra (ZMod g) L] [Fintype L] {k : ℕ} (hk : 0 < k) {x : L}
    (hgen : ∀ y : L, ∃ Q : (ZMod g)[X], aeval x Q = y) (hx : x ^ g ^ k = x) : Fintype.card L ≤ g ^ k := by
  have hq : 1 < g ^ k := Nat.one_lt_pow hk.ne' hg.out.one_lt
  set f : L[X] := X ^ (g ^ k) - X with hf
  have hf0 : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero hq
  have hfix : ∀ y : L, y ^ g ^ k = y := by
    intro y
    obtain ⟨Q, rfl⟩ := hgen y
    rw [← aeval_pow_frob, hx]
  have hsub : (Finset.univ : Finset L) ⊆ f.roots.toFinset := by
    intro y _
    rw [Multiset.mem_toFinset, mem_roots hf0, IsRoot, hf, eval_sub, eval_pow, eval_X, hfix y, sub_self]
  calc Fintype.card L = (Finset.univ : Finset L).card := Finset.card_univ.symm
    _ ≤ f.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := card_roots' f
    _ = g ^ k := Polynomial.natDegree_X_pow_sub_X (R := L) hq

section adjoin

variable {d : ℕ} {P : (ZMod g)[X]} (hP : IsPrimeLab d P)
include hP

theorem finrank_adjoin : haveI := Fact.mk hP.2.1; Module.finrank (ZMod g) (AdjoinRoot P) = d := by
  haveI := Fact.mk hP.2.1
  rw [(AdjoinRoot.powerBasis hP.1.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hP.2.2.2]

theorem adjoin_gen : ∀ y : AdjoinRoot P, ∃ Q : (ZMod g)[X], aeval (AdjoinRoot.root P) Q = y := by
  intro y
  obtain ⟨Q, rfl⟩ := AdjoinRoot.mk_surjective y
  exact ⟨Q, AdjoinRoot.aeval_eq Q⟩

theorem le_of_dvd {k : ℕ} (hk : 0 < k) (hdvd : P ∣ X ^ (g ^ k) - X) : d ≤ k := by
  haveI := Fact.mk hP.2.1
  haveI : Module.Finite (ZMod g) (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.1.ne_zero).finite
  haveI : Finite (AdjoinRoot P) := Module.finite_of_finite (ZMod g)
  letI : Fintype (AdjoinRoot P) := Fintype.ofFinite _
  have hcard : Fintype.card (AdjoinRoot P) = g ^ d := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, finrank_adjoin hP]
  have hx : (AdjoinRoot.root P) ^ g ^ k = AdjoinRoot.root P := by
    obtain ⟨R, hR⟩ := hdvd
    have h0 : aeval (AdjoinRoot.root P) (X ^ (g ^ k) - X : (ZMod g)[X]) = 0 := by
      rw [hR, map_mul, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul]
    rw [map_sub, map_pow, aeval_X, sub_eq_zero] at h0
    exact h0
  have := card_le_of_gen_fixed (L := AdjoinRoot P) (x := AdjoinRoot.root P) hk (adjoin_gen hP) hx
  rw [hcard] at this
  exact (Nat.pow_le_pow_iff_right hg.out.one_lt).1 this

end adjoin

variable {K : Type} [Field K] [Algebra (ZMod g) K]

theorem exists_unit_root {d : ℕ} (hd : 0 < d) (hK : Module.finrank (ZMod g) K = d) {P : (ZMod g)[X]}
    (hP : IsPrimeLab d P) : ∃ u : Kˣ, aeval (u : K) P = 0 := by
  haveI := Fact.mk hP.2.1
  haveI : Module.Finite (ZMod g) (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.1.ne_zero).finite
  haveI : Finite (AdjoinRoot P) := Module.finite_of_finite (ZMod g)
  letI : Fintype (AdjoinRoot P) := Fintype.ofFinite _
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hd)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  letI : Fintype K := Fintype.ofFinite _
  have hc : Fintype.card (AdjoinRoot P) = Fintype.card K := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), Module.card_eq_pow_finrank (K := ZMod g) (V := K),
      finrank_adjoin hP, hK]
  let φ := FiniteField.algEquivOfCardEq g hc
  have hr : aeval (φ (AdjoinRoot.root P)) P = 0 := by
    rw [show φ (AdjoinRoot.root P) = φ.toAlgHom (AdjoinRoot.root P) from rfl, aeval_algHom_apply,
      AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  have hne : φ (AdjoinRoot.root P) ≠ 0 := by
    intro h0
    rw [h0, aeval_def, eval₂_at_zero] at hr
    exact hP.2.2.1 ((algebraMap (ZMod g) K).injective (hr.trans (map_zero _).symm))
  exact ⟨Units.mk0 _ hne, hr⟩

theorem orbit_regular {d : ℕ} {P : (ZMod g)[X]} (hP : IsPrimeLab d P) {u : K} (hu : aeval u P = 0) :
    ∀ i j, i < d → j < d → u ^ g ^ i = u ^ g ^ j → i = j := by
  have key : ∀ i j, i < j → j < d → u ^ g ^ i = u ^ g ^ j → False := by
    intro i j hij hj h
    have hk : 0 < j - i := Nat.sub_pos_of_lt hij
    have hfix : u ^ g ^ (j - i) = u := by
      apply frob_injective (g := g) (K := K) i
      simp only
      rw [h, ← pow_mul, ← pow_add, Nat.sub_add_cancel hij.le]
    have hmin : P = minpoly (ZMod g) u := minpoly.eq_of_irreducible_of_monic hP.2.1 hu hP.1
    have hdvd : P ∣ X ^ (g ^ (j - i)) - X := by
      rw [hmin]
      apply minpoly.dvd
      rw [map_sub, map_pow, aeval_X, hfix, sub_self]
    have := le_of_dvd hP hk hdvd
    omega
  intro i j hi hj h
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (key i j hij hj h).elim
  · exact hij
  · exact (key j i hij hi h.symm).elim

theorem primeLab_to_regularChar : ∀ (g : ℕ) [Fact g.Prime] (d : ℕ), 0 < d → ∀ (K : Type) [Field K] [Algebra (ZMod g) K],
    Module.finrank (ZMod g) K = d → ∃ c : (ZMod g)[X] → (Kˣ →* ℂˣ), (∀ P, IsPrimeLab d P → IsRegularChar g d (c P)) ∧
      ∀ P P', IsPrimeLab d P → IsPrimeLab d P' → (∃ i < d, c P' = c P ^ g ^ i) → P = P' := by
  intro g _ d hd K _ _ hK
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hd)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  let e : Kˣ ≃* (Kˣ →* ℂˣ) := (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity Kˣ ℂ).some.symm
  let c : (ZMod g)[X] → (Kˣ →* ℂˣ) := fun P =>
    if h : ∃ u : Kˣ, aeval (u : K) P = 0 then e h.choose else 1
  have hc : ∀ P, IsPrimeLab d P → ∃ u : Kˣ, aeval (u : K) P = 0 ∧ c P = e u := by
    intro P hP
    have h := exists_unit_root hd hK hP
    exact ⟨h.choose, h.choose_spec, dif_pos h⟩
  refine ⟨c, fun P hP => ?_, fun P P' hP hP' ⟨i, hi, h⟩ => ?_⟩
  · obtain ⟨u, hu, hcu⟩ := hc P hP
    intro i j hi hj h
    rw [hcu, ← map_pow, ← map_pow] at h
    have h' := congrArg Units.val (e.injective h)
    simp only [Units.val_pow_eq_pow_val] at h'
    exact orbit_regular hP hu i j hi hj h'
  · obtain ⟨u, hu, hcu⟩ := hc P hP
    obtain ⟨u', hu', hcu'⟩ := hc P' hP'
    rw [hcu, hcu', ← map_pow] at h
    have h' := congrArg Units.val (e.injective h)
    simp only [Units.val_pow_eq_pow_val] at h'
    have hr : aeval (u' : K) P = 0 := by rw [h', aeval_pow_frob, hu, zero_pow (pow_ne_zero _ (Fact.out : g.Prime).ne_zero)]
    rw [minpoly.eq_of_irreducible_of_monic hP.2.1 hr hP.1, minpoly.eq_of_irreducible_of_monic hP'.2.1 hu' hP'.1]

end GlobalTheory.PrimeLabOrbit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NcardMonicNatDegreeCoeffZeroNeZero
section
open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GrPolys

theorem monic_deg_equiv_card (g : ℕ) [Fact g.Prime] (n : ℕ) :
    Set.ncard {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n} = g ^ n ∧
      Set.Finite {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n} := by
  have e : {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n} ≃ (Fin n → ZMod g) :=
    (monicEquivDegreeLT n).trans (degreeLTEquiv (ZMod g) n).toEquiv
  refine ⟨?_, ?_⟩
  · rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_eq_fintype_card,
      Fintype.card_fun, ZMod.card, Fintype.card_fin]
  · haveI : Finite {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n} := Finite.of_equiv _ e.symm
    exact Set.toFinite _

theorem zero_part_eq (g : ℕ) [Fact g.Prime] (n : ℕ) (hn : 0 < n) :
    {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 = 0} =
      (fun h => X * h) '' {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n - 1} := by
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hm, hd, h0⟩
    obtain ⟨h, rfl⟩ := X_dvd_iff.mpr h0
    have hmh : h.Monic := Monic.of_mul_monic_left monic_X hm
    refine ⟨h, ⟨hmh, ?_⟩, rfl⟩
    rw [natDegree_X_mul hmh.ne_zero] at hd
    omega
  · rintro ⟨h, ⟨hm, hd⟩, rfl⟩
    refine ⟨monic_X.mul hm, ?_, ?_⟩
    · rw [natDegree_X_mul hm.ne_zero]; omega
    · simp [mul_coeff_zero]

end GlobalTheory.GrPolys

theorem GlobalTheory.GrPolys.card_monic_coeff_zero_ne_zero :
    ∀ (g : ℕ) [Fact g.Prime] (n : ℕ), 0 < n → Set.ncard {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0} = g ^ n - g ^ (n - 1) ∧ Set.Finite {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0} := by
  intro g _ n hn
  obtain ⟨hcS, hfS⟩ := GlobalTheory.GrPolys.monic_deg_equiv_card g n
  obtain ⟨hcT, hfT⟩ := GlobalTheory.GrPolys.monic_deg_equiv_card g (n - 1)
  set S := {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n}
  set A := {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0}
  set B := {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 = 0}
  have hAS : A ⊆ S := fun f hf => ⟨hf.1, hf.2.1⟩
  have hBS : B ⊆ S := fun f hf => ⟨hf.1, hf.2.1⟩
  have hfA : A.Finite := hfS.subset hAS
  have hfB : B.Finite := hfS.subset hBS
  have hU : A ∪ B = S := by
    ext f
    simp only [A, B, S, Set.mem_union, Set.mem_setOf_eq]
    tauto
  have hD : Disjoint A B := by
    rw [Set.disjoint_left]
    intro f hA hB
    exact hA.2.2 hB.2.2
  have hB : B.ncard = g ^ (n - 1) := by
    rw [show B = _ from GlobalTheory.GrPolys.zero_part_eq g n hn, Set.ncard_image_of_injective _
      (fun a b h => mul_left_cancel₀ X_ne_zero h), hcT]
  have := Set.ncard_union_eq hD hfA hfB
  rw [hU, hcS, hB] at this
  exact ⟨by omega, hfA⟩
end

