module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0057
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Formalism.LocalToGlobal.Columns.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusFiltrationEqFontaineXiPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.FilPrincipal

section General
variable {R : Type} [CommRing R] {I : Ideal R} {a : R}

theorem evalₐ_eq_zero_iff (h : I = Ideal.span {a}) (n : ℕ) (y : AdicCompletion I R) :
    AdicCompletion.evalₐ I n y = 0 ↔ algebraMap R (AdicCompletion I R) a ^ n ∣ y := by
  have hfg : I.FG := ⟨{a}, by simp [h]⟩
  have e : (I ^ n).map (algebraMap R (AdicCompletion I R)) =
      Ideal.span {algebraMap R (AdicCompletion I R) a ^ n} := by
    have : I ^ n = Ideal.span {a ^ n} := by rw [h, Ideal.span_singleton_pow]
    rw [this, Ideal.map_span, Set.image_singleton, map_pow]
  rw [← Ideal.mem_span_singleton, ← e, ← Submodule.restrictScalars_mem R,
    ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval hfg, LinearMap.mem_ker]
  have h' : (I ^ n • ⊤ : Ideal R) = I ^ n := by ext x; simp
  exact map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq R h').injective

theorem evalₐ_algebraMap (n : ℕ) (r : R) :
    AdicCompletion.evalₐ I n (algebraMap R (AdicCompletion I R) r) = Ideal.Quotient.mk _ r := by
  rw [AlgHom.commutes]; rfl

theorem regular_of_isDomain [IsDomain R] (h : I = Ideal.span {a}) (ha : a ≠ 0) (y : AdicCompletion I R)
    (hy : algebraMap R (AdicCompletion I R) a * y = 0) : y = 0 := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [map_zero, evalₐ_eq_zero_iff h]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) y)
  have h1 : algebraMap R (AdicCompletion I R) a ^ (n + 1) ∣ y - algebraMap R _ r := by
    rw [← evalₐ_eq_zero_iff h, map_sub, evalₐ_algebraMap, hr, sub_self]
  have h2 := congrArg (AdicCompletion.evalₐ I (n + 1)) hy
  rw [map_mul, map_zero, evalₐ_algebraMap, ← hr, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at h2
  have h3 : I ^ (n + 1) = Ideal.span {a ^ (n + 1)} := by rw [h, Ideal.span_singleton_pow]
  rw [h3, Ideal.mem_span_singleton, pow_succ', mul_dvd_mul_iff_left ha] at h2
  have h4 : algebraMap R (AdicCompletion I R) a ^ n ∣ algebraMap R _ r := by
    rw [← map_pow]; exact map_dvd _ h2
  have h5 := dvd_add ((pow_dvd_pow _ (Nat.le_succ n)).trans h1) h4
  rwa [sub_add_cancel] at h5

theorem isAdicComplete_span (h : I = Ideal.span {a}) :
    IsAdicComplete (Ideal.span {algebraMap R (AdicCompletion I R) a}) (AdicCompletion I R) := by
  have hfg : I.FG := ⟨{a}, by simp [h]⟩
  have e : I.map (algebraMap R (AdicCompletion I R)) =
      Ideal.span {algebraMap R (AdicCompletion I R) a} := by
    have : ∀ J : Ideal R, J = Ideal.span {a} → J.map (algebraMap R (AdicCompletion I R)) =
        Ideal.span {algebraMap R (AdicCompletion I R) a} := by
      rintro J rfl
      rw [Ideal.map_span, Set.image_singleton]
    exact this I h
  rw [← e, IsAdicComplete.map_algebraMap_iff]
  exact AdicCompletion.isAdicComplete hfg

end General

theorem xi_ne_zero {l : ℕ} [Fact l.Prime] (e : Per.Fl l) (he : IsEps e) : xi e ≠ 0 := by
  intro h0
  set a := (frobeniusEquiv (Per.Fl l) l).symm e with ha
  have h1 : xi e * (Per.tm a - 1) = Per.tm a ^ l - 1 := geom_sum_mul _ _
  rw [h0, zero_mul, eq_comm, sub_eq_zero, ← map_pow] at h1
  have h2 := congrArg (fun w : Per.Ainf l => w.coeff 0) h1
  simp only [WittVector.teichmuller_coeff_zero, WittVector.one_coeff_zero] at h2
  have h3 : a = 1 := by
    apply (frobeniusEquiv (Per.Fl l) l).injective
    rw [frobeniusEquiv_apply, frobenius_def, h2, map_one]
  apply he.2
  rw [← ha, h3, map_one]

end GlobalTheory.MemLoc.FilPrincipal


open GlobalTheory.MemLoc.FilPrincipal in
theorem GlobalTheory.MemLoc.filtration_eq_xi_pow : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e →
    (∀ (n : ℕ) (y : Per.BdRp l), y ∈ Per.FilP l n ↔ aDp l (xi e) ^ n ∣ y) ∧
    (∀ y : Per.BdRp l, aDp l (xi e) * y = 0 → y = 0) ∧
    IsAdicComplete (Ideal.span {aDp l (xi e)}) (Per.BdRp l) ∧
    (∀ n : ℕ, Function.Surjective (Per.ev l n)) := by
  intro l _ e he
  have hk := _root_.GlobalTheory.MemLoc.ker_localizedTheta_eq_span_xi l e he
  obtain ⟨-, hd, hinj⟩ := _root_.GlobalTheory.MemLoc.ainf_isDomain_and_injective l
  have hne : algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ≠ 0 := fun h =>
    xi_ne_zero e he (hinj (h.trans (map_zero _).symm))
  obtain ⟨E, hE, hev⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
  have ha : E (aDp l (xi e)) = algebraMap (Per.AinfP l) (AdicCompletion (Per.kerP l) (Per.AinfP l))
      (algebraMap (Per.Ainf l) (Per.AinfP l) (xi e)) := by
    rw [aDp, RingHom.comp_apply, hE]
  refine ⟨fun n y => ?_, fun y hy => ?_, ?_, fun n => GlobalTheory.RingIface.ev_surj l n⟩
  · rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, ← hev, evalₐ_eq_zero_iff hk n (E y), ← ha, ← map_pow]
    exact map_dvd_iff E
  · have h1 := congrArg E hy
    rw [map_mul, map_zero, ha] at h1
    exact E.injective ((regular_of_isDomain hk hne (E y) h1).trans (map_zero E).symm)
  · rw [← IsAdicComplete.congr_ringEquiv _ E, Ideal.map_span, Set.image_singleton, ha]
    exact isAdicComplete_span hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CLTateInvariantsFiniteExtensionMem
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem invariants_finExt : ∀ (l : ℕ) [Fact l.Prime], ∀ (K : FinExt l) (x : ℂ_[l]), (∀ g ∈ GK K, Per.σC g x = x) → ∃ y ∈ K.1, ((y : Om l) : ℂ_[l]) = x := by
  intro l _ K x hx
  have h := _root_.GlobalTheory.MemLoc.ax_sen_tate l (GK K) x hx
  have hset : {y : Om l | ∀ g ∈ GK K, g y = y} = (K.1 : Set (Om l)) := by
    ext y
    have h1 := InfiniteGalois.fixedField_fixingSubgroup K.1
    constructor
    · intro hy
      have : y ∈ IntermediateField.fixedField K.1.fixingSubgroup := by
        rw [IntermediateField.mem_fixedField_iff]
        exact hy
      rwa [h1] at this
    · intro hy g hg
      exact (IntermediateField.mem_fixingSubgroup_iff K.1 g).1 hg y hy
  rw [hset] at h
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  haveI : FiniteDimensional ℚ_[l] K.1.toSubalgebra.toSubmodule := K.2
  have hc : IsComplete (K.1 : Set (Om l)) :=
    Submodule.complete_of_finiteDimensional (𝕜 := ℚ_[l]) K.1.toSubalgebra.toSubmodule
  have hc2 : IsComplete ((fun y : Om l => (y : ℂ_[l])) '' (K.1 : Set (Om l))) :=
    (isComplete_image_iff (UniformSpace.Completion.isUniformInducing_coe (Om l))).2 hc
  rw [hc2.isClosed.closure_eq] at h
  obtain ⟨y, hy, rfl⟩ := h
  exact ⟨y, hy, rfl⟩

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalAcrisToBdRPlusUniqueEquivariantApprox
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.CrisUnique

variable {l : ℕ} [Fact l.Prime]

theorem exists_isEps (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, e, h0, -, h1, h⟩ := GlobalTheory.T.exists_compatible_rootsOfUnity_and_tilt_padic l
  refine ⟨e, ?_, fun h' => h1 ?_⟩
  · have := h 0
    rw [h0, map_one] at this
    exact Subtype.ext this
  · have := h 1
    have h2 : rootT e 1 = 1 := h'
    rw [h2] at this
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [map_one, ← this]
    rfl

theorem dvd_of_pow_mul {R : Type} [CommRing R] (x p : R) (h : ∀ a, x ∣ p * a → x ∣ a) (k : ℕ) (a : R)
    (ha : x ∣ p ^ k * a) : x ∣ a := by
  induction k with
  | zero => simpa using ha
  | succ k ih => exact ih (h _ (by rwa [pow_succ', mul_assoc] at ha))

theorem localization_quotient_separated_dvd {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (x p : R) [IsLocalization.Away p S]
    (h : ∀ a, x ∣ p * a → x ∣ a)
    (hc : IsHausdorff (Ideal.span {Ideal.Quotient.mk (Ideal.span {x}) p}) (R ⧸ Ideal.span {x}))
    (q : S) (hq : ∀ r : ℕ, ∃ a : R, algebraMap R S x ∣ q - algebraMap R S (p ^ r * a)) :
    algebraMap R S x ∣ q := by
  have sat : ∀ b : R, algebraMap R S x ∣ algebraMap R S b → x ∣ b := by
    rintro b ⟨c, hc⟩
    obtain ⟨⟨c', ⟨_, m, rfl⟩⟩, hm⟩ := IsLocalization.surj (Submonoid.powers p) c
    have e : algebraMap R S (p ^ m * b) = algebraMap R S (x * c') := by
      rw [map_mul, map_mul, hc, ← hm]; ring
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers p) S).1 e
    refine dvd_of_pow_mul x p h m _ (dvd_of_pow_mul x p h k _ ⟨p ^ k * c', ?_⟩)
    simp only at hk
    rw [hk]; ring
  obtain ⟨a0, h0⟩ := hq 0
  rw [pow_zero, one_mul] at h0
  have h1 : Ideal.Quotient.mk (Ideal.span {x}) a0 = 0 := by
    refine hc.haus _ fun r => ?_
    obtain ⟨a, ha⟩ := hq r
    have h2 : x ∣ a0 - p ^ r * a := sat _ (by
      have := dvd_sub ha h0
      rw [map_sub]
      convert this using 1
      ring)
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [← map_pow, ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact h2
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h1
  have := dvd_add h0 (map_dvd (algebraMap R S) h1)
  simpa using this

theorem sep (n : ℕ) (q : Per.AinfP l ⧸ Per.kerP l ^ n)
    (hq : ∀ r : ℕ, ∃ a : Per.Ainf l, q = (l : Per.AinfP l ⧸ Per.kerP l ^ n) ^ r *
      Ideal.Quotient.mk _ (algebraMap (Per.Ainf l) (Per.AinfP l) a)) : q = 0 := by
  obtain ⟨e, he⟩ := exists_isEps l
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.MemLoc.XiSat.xi_sat l e he n
  have hk : ∀ y : Per.AinfP l, y ∈ Per.kerP l ^ n ↔ algebraMap (Per.Ainf l) (Per.AinfP l) (xi e ^ n) ∣ y := by
    intro y
    rw [_root_.GlobalTheory.MemLoc.ker_localizedTheta_eq_span_xi l e he, Ideal.span_singleton_pow, Ideal.mem_span_singleton, map_pow]
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [Ideal.Quotient.eq_zero_iff_mem, hk]
  refine localization_quotient_separated_dvd (xi e ^ n) (l : Per.Ainf l) h1 ?_ y fun r => ?_
  · rw [map_natCast]
    exact h2.toIsHausdorff
  · obtain ⟨a, ha⟩ := hq r
    refine ⟨a, ?_⟩
    rw [← hk, ← Ideal.Quotient.eq, ha, map_mul, map_pow, map_natCast, map_mul, map_pow, map_natCast]

theorem ev_alg (n : ℕ) (y : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) y) = Ideal.Quotient.mk _ y :=
  GlobalTheory.RingIface.ev_alg l n y

theorem ev_aDp (n : ℕ) (a : Per.Ainf l) :
    Per.ev l n (aDp l a) = Ideal.Quotient.mk _ (algebraMap (Per.Ainf l) (Per.AinfP l) a) :=
  ev_alg n _

theorem ev_ext {x y : Per.BdRp l} (h : ∀ n, Per.ev l n x = Per.ev l n y) : x = y :=
  GlobalTheory.RingIface.ev_ext l x y h

theorem σDp_alg (g : Per.Gq l) (y : Per.AinfP l) :
    Per.σDp g (algebraMap (Per.AinfP l) (Per.BdRp l) y) =
      algebraMap (Per.AinfP l) (Per.BdRp l) (Per.extP (Per.σA g) y) :=
  GlobalTheory.RingIface.sigDp_alg l g y

private theorem ker_evalₐ_fg {A : Type} [CommRing A] (J : Ideal A) (fg : J.FG) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ J n) = (J ^ n).map (algebraMap A (AdicCompletion J A)) := by
  ext a
  rw [RingHom.mem_ker, ← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval fg, LinearMap.mem_ker]
  have hle : (J ^ n • ⊤ : Ideal A) ≤ J ^ n := by intro x hx; simpa using hx
  rw [← AdicCompletion.factor_eval_eq_evalₐ J a hle]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval J A n a)
    rw [← hb] at h ⊢
    have : b ∈ J ^ n := Ideal.Quotient.eq_zero_iff_mem.mp h
    exact (Submodule.Quotient.mk_eq_zero _).mpr (by simpa using this)
  · intro h; rw [h, map_zero]

private theorem mem_map_of_ev (n : ℕ) (w : Per.BdRp l) (h : Per.ev l n w = 0) :
    w ∈ (Per.kerP l ^ n).map (algebraMap (Per.AinfP l) (Per.BdRp l)) := by
  obtain ⟨ε, hε⟩ := exists_isEps l
  have fg : (Per.kerP l).FG := by
    rw [_root_.GlobalTheory.MemLoc.ker_localizedTheta_eq_span_xi l ε hε]
    exact Submodule.fg_span_singleton _
  obtain ⟨e, he, hev⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
  have h1 : e w ∈ RingHom.ker (AdicCompletion.evalₐ (Per.kerP l) n) := by
    rw [RingHom.mem_ker, hev, h]
  rw [ker_evalₐ_fg _ fg] at h1
  have h2 : (Per.kerP l ^ n).map (algebraMap (Per.AinfP l) (AdicCompletion (Per.kerP l) (Per.AinfP l))) ≤
      ((Per.kerP l ^ n).map (algebraMap (Per.AinfP l) (Per.BdRp l))).comap e.symm.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, ← he a]
    have := Ideal.mem_map_of_mem (algebraMap (Per.AinfP l) (Per.BdRp l)) ha
    simpa using this
  have h3 := h2 h1
  rw [Ideal.mem_comap] at h3
  simpa using h3

theorem ev_σDp (g : Per.Gq l) (n : ℕ) (w : Per.BdRp l) (y : Per.AinfP l)
    (h : Per.ev l n w = Ideal.Quotient.mk _ y) :
    Per.ev l n (Per.σDp g w) = Ideal.Quotient.mk _ (Per.extP (Per.σA g) y) := by
  have h0 : Per.ev l n (w - algebraMap (Per.AinfP l) (Per.BdRp l) y) = 0 := by
    rw [map_sub, h, ev_alg, sub_self]
  have h1 := mem_map_of_ev n _ h0
  have h2 : (Per.kerP l ^ n).map (algebraMap (Per.AinfP l) (Per.BdRp l)) ≤
      (RingHom.ker (Per.ev l n)).comap (Per.σDp g) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, σDp_alg, ev_alg, Ideal.Quotient.eq_zero_iff_mem]
    exact ((Ideal.pow_right_mono (GlobalTheory.RingBasics.ker_σ g) n).trans (Ideal.le_comap_pow _ n)) ha
  have h3 := h2 h1
  rw [Ideal.mem_comap, RingHom.mem_ker, map_sub, map_sub, σDp_alg, ev_alg, sub_eq_zero] at h3
  exact h3

theorem sigA_alg (g : Per.Gq l) (s : Per.Acris0 l) :
    sigA g (algebraMap (Per.Acris0 l) (Per.Acris l) s) =
      algebraMap (Per.Acris0 l) (Per.Acris l) ⟨Per.extP (Per.σA g) s, (GlobalTheory.CrisMaps.sigA_extends g).mem _ s.2⟩ :=
  (GlobalTheory.CrisMaps.sigA_extends g).env s

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem ev_eq {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) (n : ℕ) (x : Per.Acris l) (y : Per.BdRp l)
    (h : ∀ r : ℕ, ∃ (s : Per.Acris0 l) (z : Per.Acris l) (a : Per.Ainf l),
      x = algebraMap (Per.Acris0 l) (Per.Acris l) s + (l : Per.Acris l) ^ r * z ∧
      Per.ev l n (y - algebraMap (Per.AinfP l) (Per.BdRp l) (s : Per.AinfP l)) =
        Per.ev l n ((l : Per.BdRp l) ^ r * aDp l a)) : Per.ev l n (j x) = Per.ev l n y := by
  obtain ⟨N, hN⟩ := hj.bdd n
  have hu : IsUnit ((l : Per.AinfP l ⧸ Per.kerP l ^ n) ^ N) := by
    have := (GlobalTheory.RingBasics.isUnit_l l).map (Ideal.Quotient.mk (Per.kerP l ^ n))
    rw [map_natCast] at this
    exact this.pow N
  rw [← sub_eq_zero, ← hu.mul_right_eq_zero]
  refine sep n _ fun r => ?_
  obtain ⟨s, z, a, hx, hy⟩ := h r
  obtain ⟨b, hb⟩ := hN z
  refine ⟨b - (l : Per.Ainf l) ^ N * a, ?_⟩
  rw [map_sub, map_mul, map_pow, map_natCast, ev_aDp] at hy
  rw [map_mul, map_pow, map_natCast] at hb
  simp only [hx, map_add (f := _), map_sub, map_mul, map_pow, map_natCast, hj.on0]
  linear_combination (l : Per.AinfP l ⧸ Per.kerP l ^ n) ^ r * hb -
    (l : Per.AinfP l ⧸ Per.kerP l ^ n) ^ N * hy

theorem unique {j j' : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) (hj' : IsCrisP j') : j' = j := by
  refine RingHom.ext fun x => ev_ext fun n => (ev_eq hj n x _ fun r => ?_).symm
  obtain ⟨N, hN⟩ := hj'.bdd n
  obtain ⟨s, z, hx⟩ := (acris_basic l).2.2.1 x (r + N)
  obtain ⟨a, ha⟩ := hN z
  refine ⟨s, (l : Per.Acris l) ^ N * z, a, by rw [hx, pow_add, mul_assoc], ?_⟩
  rw [map_mul (Per.ev l n), ev_aDp, ← ha, ← map_mul, hx, map_add (f := _), map_mul j', map_pow j', map_natCast, hj'.on0,
    add_sub_cancel_left, pow_add, mul_assoc]

theorem equivariant {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) (g : Per.Gq l) (x : Per.Acris l) :
    j (sigA g x) = Per.σDp g (j x) := by
  refine ev_ext fun n => ev_eq hj n _ _ fun r => ?_
  obtain ⟨N, hN⟩ := hj.bdd n
  obtain ⟨s, z, hx⟩ := (acris_basic l).2.2.1 x (r + N)
  obtain ⟨a, ha⟩ := hN z
  refine ⟨⟨Per.extP (Per.σA g) s, (GlobalTheory.CrisMaps.sigA_extends g).mem _ s.2⟩, (l : Per.Acris l) ^ N * sigA g z, Per.σA g a, ?_, ?_⟩
  · rw [hx, map_add (f := _), sigA_alg, map_mul, map_pow, map_natCast, pow_add, mul_assoc]
  · have hb := ev_σDp g n _ _ ha
    rw [GlobalTheory.RingBasics.awayMap_algebraMap₂, map_mul (Per.σDp g), map_pow (Per.σDp g), map_natCast] at hb
    rw [map_mul (Per.ev l n), ev_aDp, ← hb, ← map_mul, hx, map_add j, map_mul j, map_pow j, map_natCast j, hj.on0,
      map_add (Per.σDp g), σDp_alg, add_sub_cancel_left, map_mul (Per.σDp g), map_pow (Per.σDp g),
      map_natCast (Per.σDp g), pow_add, mul_assoc]

end GlobalTheory.MemLoc.CrisUnique

namespace GlobalTheory.MemLoc

theorem crisP_unique_equivariant : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → (∀ j' : Per.Acris l →+* Per.BdRp l, IsCrisP j' → j' = j) ∧ (∀ (g : Per.Gq l) (x : Per.Acris l), j (sigA g x) = Per.σDp g (j x)) ∧ ∀ (n : ℕ) (x : Per.Acris l) (y : Per.BdRp l), (∀ r : ℕ, ∃ (s : Per.Acris0 l) (z : Per.Acris l) (a : Per.Ainf l), x = algebraMap (Per.Acris0 l) (Per.Acris l) s + (l : Per.Acris l) ^ r * z ∧ Per.ev l n (y - algebraMap (Per.AinfP l) (Per.BdRp l) (s : Per.AinfP l)) = Per.ev l n ((l : Per.BdRp l) ^ r * aDp l a)) → Per.ev l n (j x) = Per.ev l n y :=
  fun _ _ _ hj => ⟨fun _ hj' => CrisUnique.unique hj hj', CrisUnique.equivariant hj, CrisUnique.ev_eq hj⟩

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralIdempotentEqSumCharacterIdempotents
section
open Formalism.L2.DIV

namespace GlobalTheory.IdemExpand

theorem coeff_idemOf_eq {G : Type} [Group G] [Fintype G] (X : Finset (G → ℂ)) (t : G) :
    (idemOf X).coeff t = ∑ χ ∈ X, χ 1 / (Fintype.card G : ℂ) * χ t⁻¹ := by
  classical
  simp only [idemOf, chiIdem, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_apply]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ t]
  simp

theorem sum_coeff_mul {G : Type} [Group G] [Fintype G] (x y : MonoidAlgebra ℂ G) (ψ : G → ℂ) :
    ∑ g, (x * y).coeff g * ψ g = ∑ b, y.coeff b * ∑ a, x.coeff a * ψ (a * b) := by
  have h : ∀ g, (x * y).coeff g = ∑ b, x.coeff (g * b⁻¹) * y.coeff b := by
    intro g
    rw [MonoidAlgebra.coeff_mul_apply_right, Finsupp.sum_fintype]
    intro i; simp
  simp only [h, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Fintype.sum_equiv (Equiv.mulRight b⁻¹) _ _ fun g => ?_
  simp only [Equiv.coe_mulRight, inv_mul_cancel_right]
  ring

theorem eq_idemOf_filter : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] [inst_2 : DecidableEq G] (A : Finset (G → ℂ)) (e : MonoidAlgebra ℂ G), (∀ ψ ∈ A, ψ 1 ≠ 0) → (∀ g : G, ∑ ψ ∈ A, ψ 1 * ψ g = if g = 1 then (Fintype.card G : ℂ) else 0) → (∀ ψ ∈ A, ∀ x : G, ψ 1 * ∑ g, e.coeff g * ψ (g * x) = (∑ g, e.coeff g * ψ g) * ψ x) → e * e = e → e = idemOf (A.filter fun ψ => ∑ g, e.coeff g * ψ g = ψ 1) := by
  intro G _ _ _ A e hone hcol hsc hee
  have hn : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h2 : ∀ ψ ∈ A, (∑ g, e.coeff g * ψ g) = 0 ∨ (∑ g, e.coeff g * ψ g) = ψ 1 := by
    intro ψ hψ
    have h := sum_coeff_mul e e ψ
    rw [hee] at h
    have h' : ψ 1 * ∑ b, e.coeff b * ∑ a, e.coeff a * ψ (a * b)
        = (∑ g, e.coeff g * ψ g) * ∑ g, e.coeff g * ψ g := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [mul_left_comm, hsc ψ hψ b]
      ring
    rw [← h] at h'
    by_cases h0 : (∑ g, e.coeff g * ψ g) = 0
    · exact Or.inl h0
    · exact Or.inr (mul_right_cancel₀ h0 h').symm
  refine MonoidAlgebra.ext (Finsupp.ext fun t => ?_)
  have h1 : (Fintype.card G : ℂ) * e.coeff t = ∑ ψ ∈ A, (∑ g, e.coeff g * ψ g) * ψ t⁻¹ := by
    have a1 : ∑ g, e.coeff g * ∑ ψ ∈ A, ψ 1 * ψ (g * t⁻¹) = (Fintype.card G : ℂ) * e.coeff t := by
      simp only [hcol, mul_inv_eq_one, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq' Finset.univ t]
      simp [mul_comm]
    rw [← a1, ← Finset.sum_congr rfl fun ψ hψ => hsc ψ hψ t⁻¹]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ψ _ => Finset.sum_congr rfl fun g _ => ?_
    ring
  apply mul_left_cancel₀ hn
  rw [h1, coeff_idemOf_eq, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun ψ hψ => ?_
  split_ifs with h
  · rw [h]; field_simp
  · rcases h2 ψ hψ with h0 | h0
    · rw [h0, zero_mul]
    · exact absurd h0 h

end GlobalTheory.IdemExpand
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddValuationNormalised
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem _root_.GlobalTheory.MemLoc.exists_addValuation_normalised : ∀ (l : ℕ) [Fact l.Prime], ∀ LL : _root_.Formalism.BasicNotions.Loc.FinExt l,
    ∃ v : AddValuation ↥LL.1 (WithTop ℚ), v (l : ↥LL.1) = 1 ∧
      ∀ x : ↥LL.1, 0 ≤ v x ↔ x ∈ _root_.Formalism.BasicNotions.Loc.OL LL := by
  intro l _ LL
  have hprime : l.Prime := Fact.out
  have hnorm : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]
  have hl0 : 0 < ‖(l : PadicAlgCl l)‖ := by
    rw [hnorm]
    exact inv_pos.2 (Nat.cast_pos.2 hprime.pos)
  have hl1 : ‖(l : PadicAlgCl l)‖ < 1 := by
    rw [hnorm]
    exact inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 hprime.one_lt)
  have hL : Real.log ‖(l : PadicAlgCl l)‖ < 0 := Real.log_neg hl0 hl1
  obtain ⟨v, hv⟩ := _root_.GlobalTheory.PadicVal.exists_addValuation (l : PadicAlgCl l) hl0 hl1
  refine ⟨v.comap LL.1.val.toRingHom, ?_, fun x => ?_⟩
  · have hcast : ((l : ↥LL.1) : PadicAlgCl l) = l := by simp
    show v ((l : ↥LL.1) : PadicAlgCl l) = 1
    rw [hcast]
    obtain ⟨q, hvq, hlog⟩ := hv _ (norm_pos_iff.1 hl0)
    have hq : q = 1 := Rat.cast_injective (by
      have := mul_right_cancel₀ hL.ne (hlog.symm.trans (one_mul _).symm)
      simpa using this)
    rw [hvq, hq]
    rfl
  · show 0 ≤ v (x : PadicAlgCl l) ↔ x ∈ integralClosure ℤ_[l] LL.1
    rw [_root_.GlobalTheory.mem_integralClosure_padicInt_iff]
    by_cases hx : (x : PadicAlgCl l) = 0
    · simp [hx]
    obtain ⟨q, hvq, hlog⟩ := hv _ hx
    rw [hvq, WithTop.coe_nonneg, ← Real.log_nonpos_iff (norm_nonneg _), hlog]
    constructor
    · intro h
      exact mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast h) hL.le
    · intro h
      have h' : (0 : ℝ) ≤ q := (mul_le_mul_right_of_neg hL).1 (by simpa using h)
      exact_mod_cast h'

end GlobalTheory.MemLoc
end

