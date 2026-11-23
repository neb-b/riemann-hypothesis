module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfForallXiPowDvd
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.XiHaus
variable {l : ℕ} [Fact l.Prime]

theorem isDomain_Fl : IsDomain (Per.Fl l) :=
  PreTilt.isDomain ℂ_[l] Valued.v (Per.OC l) (PadicComplexInt.integers l) l

theorem coeff_pow_pow (x : Per.Fl l) (k : ℕ) :
    PreTilt.coeff k (x ^ l ^ k) = PreTilt.coeff 0 x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul, map_pow, PreTilt.coeff_pow_p, ih]

theorem xi_coeff_zero (e : Per.Fl l) :
    (xi e).coeff 0 = ∑ i ∈ Finset.range l, ((frobeniusEquiv (Per.Fl l) l).symm e) ^ i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← WittVector.constantCoeff_apply, xi, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

theorem root_pow (e : Per.Fl l) : ((frobeniusEquiv (Per.Fl l) l).symm e) ^ l = e := by
  simp

theorem xi_coeff_zero_ne {e : Per.Fl l} (he : IsEps e) : (xi e).coeff 0 ≠ 0 := by
  intro h
  have h1 := geom_sum_mul ((frobeniusEquiv (Per.Fl l) l).symm e) l
  rw [← xi_coeff_zero, h, zero_mul, root_pow, eq_comm, sub_eq_zero] at h1
  exact he.2 (by rw [h1, map_one, map_one])

theorem eq_zero_of_dvd {e : Per.Fl l} (he : IsEps e) (b : Per.Fl l)
    (hb : ∀ n : ℕ, ((xi e).coeff 0) ^ n ∣ b) : b = 0 := by
  set u := (frobeniusEquiv (Per.Fl l) l).symm e with hu
  have hy : (u - 1) ∣ (xi e).coeff 0 := by
    rw [xi_coeff_zero, ← hu]
    have : ∑ i ∈ Finset.range l, u ^ i = ∑ i ∈ Finset.range l, (u ^ i - 1 ^ i) := by
      simp [Finset.sum_sub_distrib]
    rw [this]
    exact Finset.dvd_sum fun i _ => sub_dvd_pow_sub_pow u 1 i
  have h0 : PreTilt.coeff 0 ((u - 1) ^ l) = 0 := by
    rw [sub_pow_char, hu, root_pow, one_pow, map_sub, ← PreTilt.mk_untilt_eq_coeff_zero, he.1,
      map_one, map_one, sub_self]
  refine Perfection.ext fun k => ?_
  obtain ⟨c, hc⟩ := (pow_dvd_pow_of_dvd hy (l * l ^ k)).trans (hb _)
  change PreTilt.coeff k b = PreTilt.coeff k 0
  rw [hc, map_mul, pow_mul, coeff_pow_pow, h0, zero_mul, map_zero]

theorem xi_sat {e : Per.Fl l} (he : IsEps e) (n : ℕ) (a : Per.Ainf l)
    (h : xi e ^ n ∣ (l : Per.Ainf l) * a) : xi e ^ n ∣ a := by
  have := isDomain_Fl (l := l)
  obtain ⟨c, hc⟩ := h
  have h1 := congrArg WittVector.constantCoeff hc
  rw [map_mul, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, map_pow,
    WittVector.constantCoeff_apply, WittVector.constantCoeff_apply] at h1
  have h2 : c.coeff 0 = 0 :=
    (mul_eq_zero.1 h1.symm).resolve_left (pow_ne_zero _ (xi_coeff_zero_ne he))
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.1
    ((WittVector.mem_span_p_iff_coeff_zero_eq_zero c).2 h2)
  refine ⟨d, mul_left_cancel₀ (WittVector.p_nonzero l (Per.Fl l)) ?_⟩
  rw [hc]; ring

end GlobalTheory.MemLoc.XiHaus

namespace GlobalTheory.MemLoc

open XiHaus in
theorem eq_zero_of_forall_xi_pow_dvd (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (he : IsEps e)
    (a : Per.Ainf l) (ha : ∀ n : ℕ, xi e ^ n ∣ a) : a = 0 := by
  have key : ∀ (k : ℕ) (a : Per.Ainf l), (∀ n : ℕ, xi e ^ n ∣ a) → (l : Per.Ainf l) ^ k ∣ a := by
    intro k
    induction k with
    | zero => intro a _; simp
    | succ k ih =>
      intro a ha
      have h0 : a.coeff 0 = 0 := eq_zero_of_dvd he _ fun n => by
        have := map_dvd WittVector.constantCoeff (ha n)
        rwa [map_pow, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply] at this
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.1
        ((WittVector.mem_span_p_iff_coeff_zero_eq_zero a).2 h0)
      rw [pow_succ']
      exact mul_dvd_mul_left _ (ih d fun n => xi_sat he n d (ha n))
  refine IsHausdorff.haus (I := Ideal.span {(l : Per.Ainf l)}) inferInstance a fun k => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact key k a ha
end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgEquivRootOfUnityEqPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

open IsLocalRing

theorem exists_algEquiv_rootOfUnity_eq_pow (V K : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K]
    (hfin : Finite (V ⧸ maximalIdeal V)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [Algebra V Ω] [IsScalarTower V K Ω] :
    ∃ φ : Ω ≃ₐ[K] Ω, ∀ (x : Ω) (m : ℕ), (m : V) ∉ maximalIdeal V → x ^ m = 1 →
      φ x = x ^ Nat.card (V ⧸ maximalIdeal V) := by
  have : IsGalois K Ω := {}
  have hc : SMulCommClass (Ω ≃ₐ[K] Ω) V Ω := ⟨fun g v x => by
    rw [← IsScalarTower.algebraMap_smul K v x, ← IsScalarTower.algebraMap_smul K v (g • x)]
    exact map_smul g _ _⟩
  let : TopologicalSpace (integralClosure V Ω) := ⊥
  have : DiscreteTopology (integralClosure V Ω) := ⟨rfl⟩
  have : ContinuousSMul (Ω ≃ₐ[K] Ω) (integralClosure V Ω) := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    have := stabilizer_isOpen_of_isIntegral (K := K) (x : Ω)
    convert this using 1
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact Subtype.ext_iff
  have : Algebra.IsInvariant V (integralClosure V Ω) (Ω ≃ₐ[K] Ω) := by
    constructor
    intro b hb
    obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (b : Ω)).2
      fun g => congrArg Subtype.val (hb g)
    have hint : IsIntegral V k := by
      have h2 : IsIntegral V (algebraMap K Ω k) := hk ▸ b.2
      exact (isIntegral_algebraMap_iff ).1 h2
    obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨v, Subtype.ext ?_⟩
    rw [← hk, ← hv, ← IsScalarTower.algebraMap_apply]
    rfl
  have hinj : Function.Injective (algebraMap V Ω) := by
    rw [IsScalarTower.algebraMap_eq V K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective V K)
  have : FaithfulSMul V (integralClosure V Ω) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    exact hinj (congrArg Subtype.val hab)
  obtain ⟨Q, hQ, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := integralClosure V Ω) (maximalIdeal V)
  let : Field (V ⧸ maximalIdeal V) := Ideal.Quotient.field _
  let : Field (integralClosure V Ω ⧸ Q) := Ideal.Quotient.field _
  let : Fintype (V ⧸ maximalIdeal V) := Fintype.ofFinite _
  have : Algebra.IsAlgebraic (V ⧸ maximalIdeal V) (integralClosure V Ω ⧸ Q) := by
    have hi : Algebra.IsIntegral (V ⧸ maximalIdeal V) (integralClosure V Ω ⧸ Q) :=
      Ideal.Quotient.algebra_isIntegral_of_liesOver _ _
    exact hi.isAlgebraic
  obtain ⟨σ, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := Ω ≃ₐ[K] Ω)
    (maximalIdeal V) Q
    (FiniteField.frobeniusAlgEquivOfAlgebraic (V ⧸ maximalIdeal V) _)
  have hu : Q.under V = maximalIdeal V := hQo.over.symm
  have hF : IsArithFrobAt V σ.1 Q := by
    intro x
    have h := DFunLike.congr_fun hσ (Ideal.Quotient.mk _ x)
    rw [← Ideal.Quotient.eq, map_pow, hu, Nat.card_eq_fintype_card]
    exact h
  refine ⟨σ.1, fun x m hm hx => ?_⟩
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (by simp))
  have hxi : IsIntegral V x := IsIntegral.of_pow hm0 (by rw [hx]; exact isIntegral_one)
  have hmQ : ((m : ℕ) : integralClosure V Ω) ∉ Q := by
    intro h
    apply hm
    rw [← hu, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact h
  have h := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hF (ζ := ⟨x, hxi⟩) (m := m)
    (Subtype.ext hx) hmQ
  rw [hu] at h
  exact congrArg Subtype.val h

theorem exists_frobenius_Kur (l : ℕ) [Fact l.Prime] :
    ∃ σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l),
      ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → σ c = c ^ l := by
  have e : (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) ≃+* ZMod l := PadicInt.residueField
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hcard : Nat.card (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) = l := by
    rw [Nat.card_congr e.toEquiv, Nat.card_zmod]
  obtain ⟨φ, hφ⟩ := exists_algEquiv_rootOfUnity_eq_pow ℤ_[l] ℚ_[l]
    (Finite.of_equiv _ e.symm.toEquiv) (Om l)
  rw [hcard] at hφ
  have hφ' : ∀ (x : Om l) (m : ℕ), ¬ l ∣ m → x ^ m = 1 → φ x = x ^ l := by
    intro x m hm hx
    refine hφ x m (fun h => hm ?_) hx
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff] at h
    exact h
  have hle : (MaximalUnramifiedExtension l).map (φ : Om l →ₐ[ℚ_[l]] Om l) ≤ MaximalUnramifiedExtension l := by
    unfold MaximalUnramifiedExtension
    rw [IntermediateField.adjoin_map]
    apply IntermediateField.adjoin.mono
    rintro _ ⟨x, ⟨m, hm, hlm, hx⟩, rfl⟩
    exact ⟨m, hm, hlm, by rw [← map_pow, hx, map_one]⟩
  refine ⟨((φ : Om l →ₐ[ℚ_[l]] Om l).comp (MaximalUnramifiedExtension l).val).codRestrict (MaximalUnramifiedExtension l).toSubalgebra
    (fun x => hle ⟨x, x.2, rfl⟩), fun c m _ hlm hc => Subtype.ext ?_⟩
  exact hφ' c m hlm (congrArg Subtype.val hc)

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompatibleRootsOfUnityAndTiltPadic
section
noncomputable section
namespace GlobalTheory.MemLoc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

theorem zeta_pow_iter {M : Type*} [Monoid M] {p : ℕ} {ζ : ℕ → M} (hζ : ∀ n, ζ (n + 1) ^ p = ζ n)
    (m n : ℕ) : ζ (m + n) ^ p ^ n = ζ m := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, ← add_assoc, hζ, ih]

theorem zeta_exists_system (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] (p : ℕ)
    [hp : Fact p.Prime] :
    ∃ ζ : ℕ → K, ζ 0 = 1 ∧ (∀ m, ζ (m + 1) ^ p = ζ m) ∧ ζ 1 ≠ 1 := by
  have : NeZero (p : K) := ⟨Nat.cast_ne_zero.2 hp.out.ne_zero⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic p K)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos p K hp.out.pos))
  have hzp : IsPrimitiveRoot z p := Polynomial.isRoot_cyclotomic_iff.1 hz
  choose r hr using fun x : K => IsAlgClosed.exists_pow_nat_eq x hp.out.pos
  refine ⟨fun n => Nat.casesOn n 1 (fun m => r^[m] z), rfl, fun n => ?_,
    hzp.ne_one hp.out.one_lt⟩
  cases n with
  | zero => exact hzp.pow_eq_one
  | succ m =>
    show r^[m + 1] z ^ p = r^[m] z
    rw [Function.iterate_succ_apply', hr]

section Tilt

variable {p : ℕ} [hp : Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]

theorem zeta_coeff_root_iterate (x : PreTilt O p) (n m : ℕ) :
    PreTilt.coeff m ((frobeniusEquiv (PreTilt O p) p).symm^[n] x) = PreTilt.coeff (m + n) x := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', PreTilt.coeff_frobeniusEquiv_symm, ih]
    congr 2
    omega

theorem zeta_exists_tilt [IsAdicComplete (Ideal.span {(p : O)}) O] (x : ℕ → O)
    (hx : ∀ n, x (n + 1) ^ p = x n) :
    ∃ e : PreTilt O p, ∀ n, ((frobeniusEquiv (PreTilt O p) p).symm^[n] e).untilt = x n := by
  let e : PreTilt O p := ⟨fun n => Ideal.Quotient.mk (Ideal.span {(p : O)}) (x n), fun n => by
    show (Ideal.Quotient.mk (Ideal.span {(p : O)}) (x (n + 1))) ^ p = _
    rw [← map_pow, hx]⟩
  refine ⟨e, fun n => Perfection.teichmuller_spec fun m => ⟨x (n + m), ?_, by rw [zeta_pow_iter hx]⟩⟩
  have := zeta_coeff_root_iterate e n m
  rw [add_comm] at this
  exact this.symm

end Tilt

theorem exists_zeta_eps (l : ℕ) [hl : Fact l.Prime] :
    ∃ (ζ : ℕ → Om l) (ε : Per.Fl l), ζ 0 = 1 ∧ (∀ m, ζ (m + 1) ^ l = ζ m) ∧ ζ 1 ≠ 1 ∧
      ∀ m, (rootT ε m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (ζ m) := by
  obtain ⟨ζ, h0, hs, h1⟩ := zeta_exists_system (Om l) l
  have hmem : ∀ m, algebraMap (Om l) ℂ_[l] (ζ m) ∈ PadicComplexInt l := fun m => by
    have h : algebraMap (Om l) ℂ_[l] (ζ m) ^ l ^ m = 1 := by
      have := zeta_pow_iter hs 0 m
      rw [zero_add, h0] at this
      rw [← map_pow, this, map_one]
    have h2 : Valued.v (algebraMap (Om l) ℂ_[l] (ζ m)) ^ l ^ m ≤ 1 := by
      rw [← map_pow, h, map_one]
    change Valued.v (algebraMap (Om l) ℂ_[l] (ζ m)) ≤ 1
    exact (pow_le_one_iff_of_nonneg zero_le (pow_ne_zero _ hl.out.ne_zero)).1 h2
  obtain ⟨e, he⟩ := zeta_exists_tilt (p := l) (O := Per.OC l)
    (fun m => ⟨algebraMap (Om l) ℂ_[l] (ζ m), hmem m⟩) (fun m => Subtype.ext (by
      show algebraMap (Om l) ℂ_[l] (ζ (m + 1)) ^ l = algebraMap (Om l) ℂ_[l] (ζ m)
      rw [← map_pow, hs]))
  exact ⟨ζ, e, h0, hs, h1, fun m => congrArg Subtype.val (he m)⟩

end GlobalTheory.MemLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCyclotomicChar
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
namespace GlobalTheory.MemLoc

theorem _root_.GlobalTheory.MemLoc.exists_cyclotomicChar : ∀ (l : ℕ) [Fact l.Prime], ∃ χ : _root_.Formalism.BasicNotions.Loc.GQ l →* ℤ_[l]ˣ,
    ∀ (g : _root_.Formalism.BasicNotions.Loc.GQ l) (m : ℕ) (x : _root_.Formalism.BasicNotions.Loc.Om l), x ^ (l ^ m) = 1 →
      g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val := by
  intro l _
  haveI : ∀ i, HasEnoughRootsOfUnity (_root_.Formalism.BasicNotions.Loc.Om l) (l ^ i) := fun i => by
    unfold _root_.Formalism.BasicNotions.Loc.Om
    infer_instance
  let ρ : _root_.Formalism.BasicNotions.Loc.GQ l →* (_root_.Formalism.BasicNotions.Loc.Om l ≃+* _root_.Formalism.BasicNotions.Loc.Om l) :=
    { toFun := fun g => (g : _root_.Formalism.BasicNotions.Loc.Om l ≃+* _root_.Formalism.BasicNotions.Loc.Om l), map_one' := rfl, map_mul' := fun _ _ => rfl }
  exact ⟨(cyclotomicCharacter (_root_.Formalism.BasicNotions.Loc.Om l) l).comp ρ,
    fun g m x hx => cyclotomicCharacter.spec l (g : _root_.Formalism.BasicNotions.Loc.Om l ≃+* _root_.Formalism.BasicNotions.Loc.Om l) x hx⟩

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsBdRPlusSectionOfTheta
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.MemLoc.SecEx

theorem exists_lift {K L S C : Type} [Field K] [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    [CommRing S] [CommRing C] (q : K →+* S) (T : S →+* C) (hT : Function.Surjective T) (I : Ideal S)
    (hI : I = RingHom.ker T) (f : L →+* C) (hf : ∀ k, f (algebraMap K L k) = T (q k)) :
    ∃ g : L →+* AdicCompletion I S,
      (∀ x, ∃ s, AdicCompletion.evalₐ I 1 (g x) = Ideal.Quotient.mk _ s ∧ T s = f x) ∧
      ∀ k, g (algebraMap K L k) = algebraMap S _ (q k) := by
  subst hI
  letI : Algebra K S := q.toAlgebra
  haveI : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  let e := RingHom.quotientKerEquivOfSurjective hT
  have he : ∀ s, e (Ideal.Quotient.mk _ s) = T s := fun s => rfl
  let f' : L →ₐ[K] S ⧸ RingHom.ker T :=
    { (e.symm : C →+* S ⧸ RingHom.ker T).comp f with
      commutes' := fun k => by
        change e.symm (f (algebraMap K L k)) = Ideal.Quotient.mk _ (q k)
        rw [hf, ← he, RingEquiv.symm_apply_apply] }
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq f'
  refine ⟨g.toRingHom, fun x => ?_, fun k => ?_⟩
  · obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (RingHom.ker T) 1 (g x))
    refine ⟨s, hs.symm, ?_⟩
    have h1 : AdicCompletion.evalOneₐ (RingHom.ker T) (g x) = e.symm (f x) := congr($hg x)
    rw [← AdicCompletion.factorₐ_evalₐ_one, ← hs] at h1
    rw [← he]
    exact (e.eq_symm_apply).1 h1
  · exact g.commutes k

variable (l : ℕ) [Fact l.Prime]

theorem ker_localizedTheta_eq_span_eisenstein : Per.kerP l = RingHom.ker (Per.θP l) := by
  ext a
  refine ⟨fun h => GlobalTheory.RingBasics.fontaineTheta_eq_zero_of_mem_ker l a (by rwa [pow_one]), fun h => ?_⟩
  obtain ⟨⟨x, s⟩, hx⟩ := IsLocalization.surj (Submonoid.powers ((l : ℕ) : Per.Ainf l)) a
  have h0 : Per.θP l a = 0 := h
  have h1 := congrArg (Per.θP l) hx
  rw [map_mul, h0, zero_mul, GlobalTheory.RingIface.fontaineTheta_algebraMap] at h1
  have h2 : Per.θ l x = 0 := Subtype.ext h1.symm
  have h3 := GlobalTheory.RingIface.alg_mem_kerP l h2
  rw [← hx] at h3
  exact (Ideal.mul_unit_mem_iff_mem _ (IsLocalization.map_units (Per.AinfP l) s)).1 h3

theorem fontaineTheta_algebraMap₂ (a : Per.Ainf l) : Per.θP l (algebraMap _ _ a) = (Per.θ l a : ℂ_[l]) :=
  GlobalTheory.RingIface.fontaineTheta_algebraMap l a

theorem θ_surjective : Function.Surjective (Per.θ l) := by
  refine surjective_fontaineTheta fun x => ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (y : ℂ_[l]) (Fact.out : l.Prime).pos
  have hz1 : ‖z‖ ≤ 1 := by
    have := (GlobalTheory.RingBasics.mem_OC _).1 y.2
    rw [← hz, norm_pow] at this
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (Fact.out : l.Prime).ne_zero).1 this
  refine ⟨Ideal.Quotient.mk _ ⟨z, (GlobalTheory.RingBasics.mem_OC _).2 hz1⟩, ?_⟩
  rw [frobenius_def]
  exact (map_pow (Ideal.Quotient.mk _) _ _).symm.trans (congrArg _ (Subtype.ext hz))

theorem fontaineTheta_surjective : Function.Surjective (Per.θP l) := by
  intro c
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖(l : ℂ_[l])‖ ^ n * ‖c‖ ≤ 1 := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (GlobalTheory.RingBasics.norm_p_lt (p := l))).mul_const ‖c‖
    rw [zero_mul] at h
    exact (h.eventually (ge_mem_nhds one_pos)).exists
  obtain ⟨a, ha⟩ := θ_surjective l ⟨(l : ℂ_[l]) ^ n * c, (GlobalTheory.RingBasics.mem_OC _).2 (by rwa [norm_mul, norm_pow])⟩
  obtain ⟨u, hu⟩ := (GlobalTheory.RingBasics.isUnit_l l).exists_right_inv
  have h1 := congrArg (Per.θP l) hu
  rw [map_mul, map_natCast, map_one] at h1
  refine ⟨u ^ n * algebraMap _ _ a, ?_⟩
  rw [map_mul, map_pow, fontaineTheta_algebraMap₂, ha]
  change Per.θP l u ^ n * ((l : ℂ_[l]) ^ n * c) = c
  rw [← mul_assoc, ← mul_pow, mul_comm _ (l : ℂ_[l]), h1, one_pow, one_mul]

theorem θ_zA (z : ℤ_[l]) :
    (Per.θ l (Per.zA l z) : ℂ_[l]) = ((algebraMap ℚ_[l] (Om l) (z : ℚ_[l]) : Om l) : ℂ_[l]) := by
  let F : ℤ_[l] →+* ℂ_[l] := (algebraMap (Per.OC l) ℂ_[l]).comp ((Per.θ l).comp (Per.zA l))
  let G : ℤ_[l] →+* ℂ_[l] :=
    (algebraMap (Om l) ℂ_[l]).comp ((algebraMap ℚ_[l] (Om l)).comp (algebraMap ℤ_[l] ℚ_[l]))
  have hF : ∀ w, ‖F w‖ ≤ 1 := fun w => (GlobalTheory.RingBasics.mem_OC _).1 (Per.θ l (Per.zA l w)).2
  have hG : ∀ w, ‖G w‖ ≤ 1 := fun w => by
    change ‖((algebraMap ℚ_[l] (Om l) (w : ℚ_[l]) : Om l) : ℂ_[l])‖ ≤ 1
    rw [PadicComplex.norm_extends, PadicAlgCl.norm_extends]
    exact w.2
  change F z = G z
  have hb : ∀ n : ℕ, ‖F z - G z‖ ≤ ‖(l : ℂ_[l])‖ ^ n * 2 := fun n => by
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
    have hz : z = (z.appr n : ℤ_[l]) + (l : ℤ_[l]) ^ n * w := by rw [mul_comm, hw]; ring
    have : F z - G z = (l : ℂ_[l]) ^ n * (F w - G w) := by
      rw [hz]
      simp only [map_add (f := _), map_mul, map_pow, map_natCast]
      ring
    rw [this, norm_mul, norm_pow]
    refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (by positivity)
    linarith [hF w, hG w]
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (GlobalTheory.RingBasics.norm_p_lt (p := l))).mul_const 2
  rw [zero_mul] at h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 (ge_of_tendsto' h hb))

theorem isUnit_padicIntMap (y : nonZeroDivisors ℤ_[l]) : IsUnit (Per.zP l y) := by
  have h0 : (y : ℤ_[l]) ≠ 0 := nonZeroDivisors.ne_zero y.2
  have h1 := congrArg (Per.zP l) (PadicInt.unitCoeff_spec h0)
  rw [map_mul, map_pow, map_natCast] at h1
  rw [h1]
  exact ((PadicInt.unitCoeff h0).isUnit.map _).mul ((GlobalTheory.RingBasics.isUnit_l l).pow _)

def qP : ℚ_[l] →+* Per.AinfP l := IsLocalization.lift (isUnit_padicIntMap l)

theorem qP_coe (z : ℤ_[l]) : qP l (z : ℚ_[l]) = Per.zP l z := IsLocalization.lift_eq (isUnit_padicIntMap l) z

theorem algebraMap_eq_fontaineTheta_padicMap (k : ℚ_[l]) :
    algebraMap (Om l) ℂ_[l] (algebraMap ℚ_[l] (Om l) k) = Per.θP l (qP l k) := by
  refine RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l])
    (j := (algebraMap (Om l) ℂ_[l]).comp (algebraMap ℚ_[l] (Om l)))
    (k := (Per.θP l).comp (qP l)) (RingHom.ext fun z => ?_)) k
  change algebraMap (Om l) ℂ_[l] (algebraMap ℚ_[l] (Om l) (z : ℚ_[l])) = Per.θP l (qP l (z : ℚ_[l]))
  rw [qP_coe, GlobalTheory.RingIface.padicIntMap_eq_algebraMap_comp]
  exact ((fontaineTheta_algebraMap₂ l _).trans (θ_zA l z)).symm

theorem exists_isSec (l : ℕ) [Fact l.Prime] : ∃ o : Om l →+* Per.BdRp l, IsSec o := by
  obtain ⟨g, h1, h2⟩ := exists_lift (qP l) (Per.θP l) (fontaineTheta_surjective l) (Per.kerP l) (ker_localizedTheta_eq_span_eisenstein l)
    (algebraMap (Om l) ℂ_[l]) (algebraMap_eq_fontaineTheta_padicMap l)
  obtain ⟨e, he1, he2⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
  refine ⟨(e.symm : _ →+* Per.BdRp l).comp g, fun x => ?_, fun z => ?_⟩
  · obtain ⟨s, hs, hs'⟩ := h1 x
    have h3 : Per.ev l 1 (e.symm (g x)) = Ideal.Quotient.mk _ s := by
      rw [← he2, RingEquiv.apply_symm_apply, hs]
    have h4 : e.symm (g x) - algebraMap (Per.AinfP l) (Per.BdRp l) s ∈ Per.FilP l 1 := by
      rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, map_sub, h3, GlobalTheory.RingIface.ev_alg, sub_self]
    have h5 := GlobalTheory.RingIface.thetaD_of_mem_FilP l h4
    rw [map_sub, GlobalTheory.RingIface.thetaD_alg, sub_eq_zero] at h5
    exact h5.trans hs'
  · have h3 : e.symm (g (algebraMap ℚ_[l] (Om l) (z : ℚ_[l]))) =
        algebraMap (Per.AinfP l) (Per.BdRp l) (algebraMap (Per.Ainf l) (Per.AinfP l) (Per.zA l z)) := by
      rw [h2, qP_coe, GlobalTheory.RingIface.padicIntMap_eq_algebraMap_comp, ← he1, RingEquiv.symm_apply_apply]
    exact h3

end GlobalTheory.MemLoc.SecEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLeGramEqSgn
section
open NumberField

namespace GlobalTheory.HermSignature

theorem exists_le_gram_eq_sgn : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E), (∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (G a b) = G b a) → G.det ≠ 0 → ∀ τ : E →+* ℂ, ∃ p : ℕ, p ≤ r ∧ ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧ ReciprocityTheory.ChartRestriction.G.FD.gram τ G P = Matrix.diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn p (a : ℕ) : ℝ) : ℂ) := by
  intro E _ _ _ r G hG hd τ
  obtain ⟨p, Q, hQ, h⟩ := GlobalTheory.Published.LandherrSt.exists_gram_eq_sgn hG hd τ
  refine ⟨min p r, min_le_right _ _, Q, hQ, ?_⟩
  rw [h]
  congr 1
  funext a
  have ha := a.2
  simp only [ReciprocityTheory.ChartRestriction.G.FD.sgn, lt_min_iff, ha, and_true]

end GlobalTheory.HermSignature
end

