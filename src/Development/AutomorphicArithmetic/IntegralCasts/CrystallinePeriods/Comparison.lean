module

public import Mathlib
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRham
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Action

@[expose] public section

noncomputable section

open Ideal
open scoped Nat

namespace Reformulated.AutPerF

universe u v

theorem isPrecomplete_of_bounded {A D : Type*} [CommRing A] [CommRing D] (p c : ℕ)
    [IsPrecomplete (span {(p : A)}) A] (ψ : A →+* D) (h : ∀ d : D, ∃ a, (p : D) ^ c * d = ψ a) :
    IsPrecomplete (span {(p : D)}) D := by
  refine ⟨fun f hf => ?_⟩
  simp only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hf ⊢
  have h1 : ∀ k, ∃ a, f (k + c + 1) - f (k + c) = ψ ((p : A) ^ k * a) := fun k => by
    obtain ⟨e, he⟩ := hf (Nat.le_succ (k + c))
    obtain ⟨a, ha⟩ := h (-e)
    exact ⟨a, by rw [map_mul, map_pow, map_natCast, ← ha, ← neg_sub, he]; ring⟩
  choose a ha using h1
  let s : ℕ → A := fun k => ∑ j ∈ Finset.range k, (p : A) ^ j * a j
  have hs : ∀ k, ψ (s k) = f (k + c) - f c := fun k => by
    induction k with
    | zero => simp [s]
    | succ k ih =>
      simp only [s, Finset.sum_range_succ, map_add (f := _)] at ih ⊢
      rw [ih, ← ha, Nat.add_right_comm k 1 c]; ring
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := span {(p : A)}) s (by
    intro m n hmn
    simp only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    rw [← dvd_neg, neg_sub, Finset.sum_range_sub_sum_range hmn]
    refine Finset.dvd_sum fun j hj => ?_
    exact (pow_dvd_pow _ (Finset.mem_filter.1 hj).2).mul_right _)
  simp only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hL
  refine ⟨f c + ψ L, fun n => ?_⟩
  have h2 := map_dvd ψ (hL n)
  rw [map_pow, map_natCast, map_sub, hs] at h2
  have h3 := dvd_add (hf (Nat.le_add_right n c)) h2
  convert h3 using 1
  ring

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
  [IsDomain R] [ValuationRing R] [CharZero R] [IsAlgClosed (FractionRing R)]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
  [IsDomain S] [ValuationRing S] [CharZero S] [IsAlgClosed (FractionRing S)]

namespace AcrisZero

theorem mem_span_gamma_xi (ϖ : PFlat p R) {x : AinfInv p R} (hx : x ∈ acrisZero p R) :
    x ∈ Submodule.span (Ainf p R)
      (Set.range fun m => AinfInv.gamma m (algebraMap _ (AinfInv p R) (Ainf.xi ϖ))) := by
  set M := Submodule.span (Ainf p R)
      (Set.range fun m => AinfInv.gamma m (algebraMap _ (AinfInv p R) (Ainf.xi ϖ)))
  have hg : ∀ m, AinfInv.gamma m (algebraMap _ (AinfInv p R) (Ainf.xi ϖ)) ∈ M := fun m =>
    Submodule.subset_span ⟨m, rfl⟩
  have hmul : M * M ≤ M := by
    rw [Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
    have : AinfInv.gamma a (algebraMap _ (AinfInv p R) (Ainf.xi ϖ)) *
        AinfInv.gamma b (algebraMap _ (AinfInv p R) (Ainf.xi ϖ)) =
        (a + b).choose a • AinfInv.gamma (a + b) (algebraMap _ (AinfInv p R) (Ainf.xi ϖ)) := by
      simp only [AinfInv.gamma]
      rw [smul_mul_smul_comm, ← pow_add, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
      congr 1
      rw [Nat.cast_add_choose]
      field_simp
    simp only [SetLike.mem_coe]
    rw [this]
    exact nsmul_mem (hg _) _
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨n, y, hy, rfl⟩ := hx
    have : y ∈ span {Ainf.xi ϖ} := by rw [← Ainf.ker_theta ϖ]; exact hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 this
    have : AinfInv.gamma n (algebraMap _ (AinfInv p R) (c * Ainf.xi ϖ)) =
        c ^ n • AinfInv.gamma n (algebraMap _ (AinfInv p R) (Ainf.xi ϖ)) := by
      simp only [AinfInv.gamma, Algebra.smul_def, map_mul, map_pow]; ring
    rw [this]
    exact M.smul_mem _ (hg n)
  | algebraMap r =>
    have := M.smul_mem r (hg 0)
    simpa [AinfInv.gamma, Algebra.smul_def] using this
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact hmul (Submodule.mul_mem_mul hx hy)

theorem exists_p_pow_mul_sub_mem (n : ℕ) {x : AinfInv p R} (hx : x ∈ acrisZero p R) :
    ∃ b : Ainf p R, (p : AinfInv p R) ^ n * x - algebraMap _ _ b ∈ AinfInv.kerTheta p R ^ n := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  have hx' := mem_span_gamma_xi ϖ hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    rcases le_total m n with h | h
    · obtain ⟨a, ha⟩ := exists_factorial_mul_eq_pow p m
      refine ⟨p ^ (n - m) * algebraMap ℤ_[p] _ a * Ainf.xi ϖ ^ m, ?_⟩
      have ha' := congrArg ((algebraMap (Ainf p R) (AinfInv p R)).comp (algebraMap ℤ_[p] _)) ha
      simp only [map_mul, map_natCast, map_pow, RingHom.comp_apply] at ha' ⊢
      rw [← AinfInv.factorial_mul_gamma m, ← pow_sub_mul_pow (p : AinfInv p R) h, ← ha']
      ring_nf
      simp
    · refine ⟨0, ?_⟩
      simp only [map_zero, sub_zero, AinfInv.gamma, Algebra.smul_def]
      refine Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right h ?_))
      rw [AinfInv.kerTheta_eq ϖ]
      exact Ideal.pow_mem_pow (mem_span_singleton_self _) _
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by convert add_mem ha hb using 1; rw [map_add (f := _)]; ring⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by
      convert Ideal.mul_mem_left _ (algebraMap _ _ c) ha using 1
      rw [map_mul, Algebra.smul_def]; ring⟩

variable (p R) in
def toQuot (n : ℕ) : AcrisZero p R →+* AinfInv p R ⧸ AinfInv.kerTheta p R ^ n :=
  (Ideal.Quotient.mk _).comp (acrisZero p R).val.toRingHom

theorem exists_p_pow_mul_eq (n : ℕ) (d : (toQuot (p := p) (R := R) n).range) : ∃ b : Ainf p R,
    (p : (toQuot (p := p) (R := R) n).range) ^ n * d = (toQuot (p := p) (R := R) n).rangeRestrict (algebraMap _ _ b) := by
  obtain ⟨_, x, rfl⟩ := d
  obtain ⟨b, hb⟩ := exists_p_pow_mul_sub_mem n x.2
  refine ⟨b, Subtype.ext ?_⟩
  have := Ideal.Quotient.eq.2 hb
  rw [map_mul, map_pow, map_natCast] at this
  push_cast
  exact this

instance isAdicComplete_range (n : ℕ) :
    IsAdicComplete (span {(p : (toQuot (p := p) (R := R) n).range)}) (toQuot (p := p) (R := R) n).range where
  toIsPrecomplete := isPrecomplete_of_bounded p n
    ((toQuot (p := p) (R := R) n).rangeRestrict.comp (algebraMap (Ainf p R) _)) (exists_p_pow_mul_eq n)
  haus' x hx := by
    obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
    simp only [smul_eq_mul, Ideal.mul_top, SModEq.zero, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hx
    obtain ⟨b, hb⟩ := exists_p_pow_mul_eq n x
    have key : ∀ b : Ainf p R, (toQuot (p := p) (R := R) n).rangeRestrict (algebraMap _ _ b) = 0 ↔
        Ainf.xi ϖ ^ n ∣ b := fun b => by
      rw [← AinfInv.algebraMap_mem_kerTheta_pow_iff, ← Ideal.Quotient.eq_zero_iff_mem,
        Subtype.ext_iff]
      rfl
    have h0 : Ainf.xi ϖ ^ n ∣ b := Ainf.xi_pow_dvd_of_forall ϖ fun k => by
      obtain ⟨e, he⟩ := hx k
      obtain ⟨a, ha⟩ := exists_p_pow_mul_eq n e
      obtain ⟨c, hc⟩ := (key (b - p ^ k * a)).1 (by
        let ψ := (toQuot (p := p) (R := R) n).rangeRestrict.comp (algebraMap (Ainf p R) _)
        change ψ (b - p ^ k * a) = 0
        change _ = ψ b at hb
        change _ = ψ a at ha
        rw [ψ.map_sub, ψ.map_mul, map_pow ψ, map_natCast ψ, ← hb, ← ha, he]
        ring)
      exact ⟨a, c, by rw [← hc]; ring⟩
    rw [← key, ← hb, Subtype.ext_iff] at h0
    have hu : IsUnit ((p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ n) := by
      simpa using ((AinfInv.isUnit_p p (R := R)).map (Ideal.Quotient.mk _)).pow n
    exact Subtype.ext (hu.mul_right_eq_zero.1 (by simpa using h0))

end AcrisZero

namespace Acris

variable (p R) in
def toRange (n : ℕ) : Acris p R →+* (AcrisZero.toQuot (p := p) (R := R) n).range :=
  (AdicCompletion.ofAlgEquiv (span {(p : (AcrisZero.toQuot (p := p) (R := R) n).range)})).symm.toRingHom.comp
    (adicMap _ _ (AcrisZero.toQuot (p := p) (R := R) n).rangeRestrict (span_natCast_le_comap p _))

theorem toRange_algebraMap (n : ℕ) (a : AcrisZero p R) :
    toRange (p := p) (R := R) n (algebraMap _ _ a) = (AcrisZero.toQuot (p := p) (R := R) n).rangeRestrict a := by
  have := adicMap_algebraMap _ _ (AcrisZero.toQuot (p := p) (R := R) n).rangeRestrict
    (span_natCast_le_comap p _) a
  refine (congrArg (AdicCompletion.ofAlgEquiv _).symm this).trans ?_
  exact (AdicCompletion.ofAlgEquiv _).symm.commutes _


omit [IsDomain R] [ValuationRing R] [CharZero R] [IsAlgClosed (FractionRing R)] in
def rangeMap {m n : ℕ} (g : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n →+*
      AinfInv p S ⧸ AinfInv.kerTheta p S ^ m) (e : AcrisZero p R →+* AcrisZero p S)
    (h : ∀ a, g (AcrisZero.toQuot (p := p) (R := R) n a) = AcrisZero.toQuot (p := p) (R := S) m (e a)) :
    (AcrisZero.toQuot (p := p) (R := R) n).range →+* (AcrisZero.toQuot (p := p) (R := S) m).range :=
  (g.comp (Subring.subtype _)).codRestrict _ (by rintro ⟨_, a, rfl⟩; exact ⟨e a, (h a).symm⟩)

theorem map_toRange {m n : ℕ} (g : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n →+*
      AinfInv p S ⧸ AinfInv.kerTheta p S ^ m) (e : AcrisZero p R →+* AcrisZero p S)
    (h : ∀ a, g (AcrisZero.toQuot (p := p) (R := R) n a) = AcrisZero.toQuot (p := p) (R := S) m (e a))
    (e' : Acris p R →+* Acris p S) (h' : ∀ a, e' (algebraMap _ _ a) = algebraMap _ _ (e a))
    (x : Acris p R) : g (toRange (p := p) (R := R) n x) = toRange (p := p) (R := S) m (e' x) :=
  congrArg Subtype.val (RingHom.congr_fun (hom_ext (f := (rangeMap g e h).comp (toRange (p := p) (R := R) n))
    (g := (toRange (p := p) (R := S) m).comp e') fun a => Subtype.ext (by
      rw [RingHom.comp_apply, RingHom.comp_apply, h', toRange_algebraMap, toRange_algebraMap]
      exact h a)) x)

variable (p R) in
def toBdRPlus : Acris p R →+* BdRPlus p R :=
  AdicCompletion.liftRingHom (AinfInv.kerTheta p R)
    (fun n => (Subring.subtype _).comp (toRange (p := p) (R := R) n))
    (fun {m n} hle => RingHom.ext fun x =>
      map_toRange (Ideal.Quotient.factorPow _ hle) (RingHom.id _) (fun _ => rfl) (RingHom.id _)
        (fun _ => rfl) x)

theorem eval_toBdRPlus (n : ℕ) (x : Acris p R) :
    BdRPlus.eval p R n (toBdRPlus p R x) = toRange (p := p) (R := R) n x := by
  unfold toBdRPlus BdRPlus.eval
  refine (AdicCompletion.evalₐ_liftRingHom _ _ ?_ n x).trans rfl
  exact fun {m n} hle => RingHom.ext fun x =>
      map_toRange (Ideal.Quotient.factorPow _ hle) (RingHom.id _) (fun _ => rfl) (RingHom.id _)
        (fun _ => rfl) x

@[simp] theorem toBdRPlus_algebraMap_zero (a : AcrisZero p R) :
    toBdRPlus p R (algebraMap _ _ a) = algebraMap (AinfInv p R) _ a :=
  BdRPlus.ext_eval fun n => by
    rw [eval_toBdRPlus, toRange_algebraMap, BdRPlus.eval_algebraMap]; rfl

@[simp] theorem toBdRPlus_algebraMap (a : Ainf p R) :
    toBdRPlus p R (algebraMap _ _ a) = algebraMap _ _ a :=
  toBdRPlus_algebraMap_zero _

omit [IsDomain R] [ValuationRing R] [CharZero R] [IsAlgClosed (FractionRing R)] in
theorem coe_logPartial (N : ℕ) (u : Ainf p R) (hu : Ainf.theta p R u = 1) :
    (logPartial N u hu : AinfInv p R) = truncLog N (algebraMap _ _ (u - 1)) := by
  rw [logPartial, truncLog, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : (((-1) ^ k * (k ! : AcrisZero p R) : AcrisZero p R) : AinfInv p R) =
      algebraMap ℚ _ ((-1) ^ k * k !) := by simp
  rw [MulMemClass.coe_mul, e, ← Algebra.smul_def]
  change _ • (_ • _) = _
  rw [smul_smul, Nat.factorial_succ]
  congr 1
  push_cast
  field_simp

theorem toBdRPlus_log (u : Ainf p R) (hu : Ainf.theta p R u = 1)
    (hu' : BdRPlus.theta p R (algebraMap _ _ u) = 1) :
    toBdRPlus p R (log u hu) = BdRPlus.log (algebraMap _ _ u) hu' := by
  refine BdRPlus.ext_eval fun n => ?_
  have hz : BdRPlus.eval p R n (algebraMap _ _ u - 1) ^ n = 0 :=
    BdRPlus.eval_pow_eq_zero (by simp [hu']) n
  have h1 : ∀ N, n ≤ N → (toRange (p := p) (R := R) n (algebraMap _ _ (logPartial N u hu)) :
      AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) =
      truncLog n (BdRPlus.eval p R n (algebraMap _ _ u - 1)) := fun N hN => by
    rw [← eval_toBdRPlus, toBdRPlus_algebraMap_zero, coe_logPartial, map_truncLog, map_truncLog,
      ← truncLog_eq_of_pow_eq_zero hz hN, ← IsScalarTower.algebraMap_apply,
      RingHom.map_sub (algebraMap (Ainf p R) (BdRPlus p R)), map_one]
  rw [eval_toBdRPlus, BdRPlus.eval_log, ← h1 n le_rfl]
  congr 1
  rw [IsHausdorff.eq_iff_smodEq (I := span {(p : (AcrisZero.toQuot (p := p) (R := R) n).range)})]
  intro k
  have h2 : toRange (p := p) (R := R) n (algebraMap _ _ (logPartial n u hu)) =
      toRange (p := p) (R := R) n (algebraMap _ _ (logPartial (max n (p ^ k)) u hu)) :=
    Subtype.ext (by rw [h1 _ le_rfl, h1 _ (le_max_left _ _)])
  have h3 := (eval_eq_zero_iff k (log u hu - algebraMap _ _ (logPartial (max n (p ^ k)) u hu))).1
    (by rw [RingHom.map_sub, eval_log u hu (le_max_right _ _), eval_algebraMap, sub_self])
  rw [h2, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, ← map_sub]
  simpa using map_dvd (toRange (p := p) (R := R) n) h3

@[simp] theorem toBdRPlus_logTeich (η : tateModule p R) :
    toBdRPlus p R (logTeich η) = BdRPlus.logTeich η := toBdRPlus_log _ _ _

end Acris

theorem BdRPlus.ker_theta_eq_span_logTeich {ε : tateModule p R} (hε : IsPrimitive ε) :
    RingHom.ker (BdRPlus.theta p R) = span {BdRPlus.logTeich ε} := by
  have h := BdRPlus.ker_theta_eq_span_teich_sub_one hε
  set x := algebraMap (Ainf p R) (BdRPlus p R) (Ainf.teich p ε.1 - 1) with hx
  have h2 : BdRPlus.logTeich ε - x ∈ BdRPlus.fil p R 2 := by
    rw [← BdRPlus.ker_eval, RingHom.mem_ker, map_sub, BdRPlus.logTeich, BdRPlus.eval_two_log, hx,
      RingHom.map_sub (algebraMap (Ainf p R) (BdRPlus p R)), map_one, sub_self]
  rw [BdRPlus.fil, h, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2
  obtain ⟨c, hc⟩ := h2
  have hx0 : BdRPlus.theta p R x = 0 := by
    rw [← RingHom.mem_ker, h]; exact mem_span_singleton_self _
  have := (isField_away p R).nontrivial
  have hu : IsUnit (1 + x * c) := (BdRPlus.isUnit_iff_theta_ne_zero _).2 (by simp [hx0])
  rw [h, show BdRPlus.logTeich ε = x * (1 + x * c) by linear_combination hc,
    Ideal.span_singleton_mul_right_unit hu]

theorem BdRPlus.logTeich_ne_zero {ε : tateModule p R} (hε : IsPrimitive ε) :
    BdRPlus.logTeich ε ≠ 0 :=
  ((BdRPlus.irreducible_iff _).2 (BdRPlus.ker_theta_eq_span_logTeich hε)).ne_zero

namespace BcrisPlus

variable (p R) in
def toBdRPlus : BcrisPlus p R →+* BdRPlus p R :=
  lift (Acris.toBdRPlus p R) (IsUnit.of_mul_eq_one _ BdRPlus.p_mul_inv)

@[simp] theorem toBdRPlus_algebraMap (x : Acris p R) :
    toBdRPlus p R (algebraMap _ _ x) = Acris.toBdRPlus p R x := lift_algebraMap _ _ x

@[simp] theorem toBdRPlus_algebraMap_padic (a : ℚ_[p]) :
    toBdRPlus p R (algebraMap _ _ a) = algebraMap _ _ a := by
  refine RingHom.congr_fun (padic_hom_ext (f := (toBdRPlus p R).comp (algebraMap ℚ_[p] _))
    (g := algebraMap ℚ_[p] (BdRPlus p R)) fun b => ?_) a
  rw [RingHom.comp_apply, algebraMap_padicInt, toBdRPlus_algebraMap,
    IsScalarTower.algebraMap_apply ℤ_[p] (Ainf p R) (Acris p R), Acris.toBdRPlus_algebraMap,
    IsScalarTower.algebraMap_apply ℚ_[p] (AinfInv p R) (BdRPlus p R),
    ← IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (AinfInv p R)]
  rfl

end BcrisPlus

namespace Bcris

variable (p R) in
def toBdR : Bcris p R →+* BdR p R :=
  lift ((algebraMap (BdRPlus p R) (BdR p R)).comp (BcrisPlus.toBdRPlus p R)) (fun ε hε => by
    simpa using (map_ne_zero_iff _ BdR.algebraMap_injective).2 (BdRPlus.logTeich_ne_zero hε))

@[simp] theorem toBdR_algebraMap (x : BcrisPlus p R) :
    toBdR p R (algebraMap _ _ x) = algebraMap _ _ (BcrisPlus.toBdRPlus p R x) :=
  lift_algebraMap _ _ x

@[simp] theorem toBdR_algebraMap_acris (x : Acris p R) :
    toBdR p R (algebraMap _ _ x) = algebraMap _ _ (Acris.toBdRPlus p R x) := by
  rw [IsScalarTower.algebraMap_apply _ (BcrisPlus p R), toBdR_algebraMap,
    BcrisPlus.toBdRPlus_algebraMap]

@[simp] theorem toBdR_algebraMap_padic (a : ℚ_[p]) :
    toBdR p R (algebraMap _ _ a) = algebraMap _ _ a := by
  rw [IsScalarTower.algebraMap_apply _ (BcrisPlus p R), toBdR_algebraMap,
    BcrisPlus.toBdRPlus_algebraMap_padic, ← IsScalarTower.algebraMap_apply]

@[simp] theorem toBdR_logTeich (η : tateModule p R) :
    toBdR p R (logTeich η) = algebraMap _ _ (BdRPlus.logTeich η) := by
  rw [logTeich, toBdR_algebraMap_acris, Acris.toBdRPlus_logTeich]

variable (p R) in
def fil (i : ℤ) : AddSubgroup (Bcris p R) :=
  (BdR.fil p R i).toAddSubgroup.comap (toBdR p R).toAddMonoidHom

end Bcris

namespace Bst

variable (p R) in
def toBdR : Bst p R →+* BdR p R :=
  lift (Bcris.toBdR p R) (fun ϖ => algebraMap _ _ (BdRPlus.logFlat ϖ)) (fun η ϖ => by
    rw [BdRPlus.logFlat_twist, map_add (f := _), Bcris.toBdR_logTeich])

@[simp] theorem toBdR_algebraMap (x : Bcris p R) :
    toBdR p R (algebraMap _ _ x) = Bcris.toBdR p R x := lift_algebraMap _ _ _ x

@[simp] theorem toBdR_algebraMap_padic (a : ℚ_[p]) :
    toBdR p R (algebraMap _ _ a) = algebraMap _ _ a := by
  rw [IsScalarTower.algebraMap_apply _ (Bcris p R), toBdR_algebraMap, Bcris.toBdR_algebraMap_padic]

variable (p R) in
def fil (i : ℤ) : AddSubgroup (Bst p R) :=
  (BdR.fil p R i).toAddSubgroup.comap (toBdR p R).toAddMonoidHom

end Bst

variable {G : Type*} [Group G] [MulSemiringAction G R]

end Reformulated.AutPerF
