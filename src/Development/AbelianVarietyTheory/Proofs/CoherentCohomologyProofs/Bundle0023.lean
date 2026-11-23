module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.TwistedSectionsLocaliseToChartsStatement
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0017

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsResMEqMulSecOfEqZpowSec
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self)

namespace GlobalTheory

namespace Twist

variable {X : Scheme.{0}} {F : X.Modules} {L : LB X} {m n : ℤ}

def zpowSec (σ : LB.Sec (lbZPow L m)) (k : ℕ) : LB.Sec (lbZPow L (k * m)) :=
  zmkGlobal (fun i => zfun σ i ^ k) fun i j => by
    have e : res (le_refl (L.U i ⊓ L.U j)) (L.g i j) = L.g i j := Units.ext (resG_self _ _)
    rw [map_pow, map_pow, zfun_rel σ i j _ inf_le_right le_rfl, e, mul_pow, mul_comm (k : ℤ),
      zpow_mul, zpow_natCast, Units.val_pow_eq_pow_val]

@[simp] theorem zfun_zpowSec (σ : LB.Sec (lbZPow L m)) (k : ℕ) (i : L.ι) :
    zfun (zpowSec σ k) i = zfun σ i ^ k := zfun_zmkGlobal _ _ i

theorem basicOpen_resG_zfun (σ : LB.Sec (lbZPow L m)) (i : L.ι) {W : X.Opens} (h : W ≤ L.U i) :
    X.basicOpen (resG X h (zfun σ i)) = W ⊓ Out.nonzeroLocus σ := by
  rw [zfun, resG_resG]
  refine (X.basicOpen_res _ (homOfLE (h.trans (le_zidx_U m i))).op).trans ?_
  rw [← nonzeroLocus_inf_chart σ (zidx L m i), inf_comm (Out.nonzeroLocus σ), ← inf_assoc]
  exact congrArg (· ⊓ _) (inf_eq_left.2 (h.trans (le_zidx_U m i)))

theorem basicOpen_zfun (σ : LB.Sec (lbZPow L m)) (i : L.ι) :
    X.basicOpen (zfun σ i) = L.U i ⊓ Out.nonzeroLocus σ := by
  rw [← basicOpen_resG_zfun σ i le_rfl, resG_self]

theorem nonzeroLocus_eq_of_zfun (hL : L.IsLB) (σ : LB.Sec (lbZPow L m)) {V : X.Opens}
    (h : ∀ i, X.basicOpen (zfun σ i) = L.U i ⊓ V) : Out.nonzeroLocus σ = V := by
  ext x
  obtain ⟨i, hi⟩ := exists_chart hL x
  have e := (basicOpen_zfun σ i).symm.trans (h i)
  exact ⟨fun hx => (e.le ⟨hi, hx⟩).2, fun hx => (e.ge ⟨hi, hx⟩).2⟩

theorem nonzeroLocus_zofSec (hL : L.IsLB) (s : LB.Sec L) :
    Out.nonzeroLocus (zofSec s) = Out.nonzeroLocus s :=
  nonzeroLocus_eq_of_zfun hL _ fun i => by rw [zfun_zofSec, ← nonzeroLocus_inf_chart, inf_comm]

theorem nonzeroLocus_le_zpowSec (hL : L.IsLB) (σ : LB.Sec (lbZPow L m)) (k : ℕ) :
    Out.nonzeroLocus σ ≤ Out.nonzeroLocus (zpowSec σ k) := fun x hx => by
  obtain ⟨i, hi⟩ := exists_chart hL x
  refine ((basicOpen_zfun (zpowSec σ k) i).le ?_).2
  rw [zfun_zpowSec]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero, Scheme.basicOpen_one]
    exact hi
  · rw [Scheme.basicOpen_pow _ _ hk, basicOpen_zfun]
    exact ⟨hi, hx⟩

theorem exists_finite_affine_chart_cover (hL : L.IsLB) {W : X.Opens} (hW : IsCompact (W : Set X)) :
    ∃ (κ : Type) (_ : Finite κ) (T : κ → X.Opens) (c : κ → L.ι),
      (∀ a, IsAffineOpen (T a)) ∧ (∀ a, T a ≤ W) ∧ (∀ a, T a ≤ L.U (c a)) ∧ W ≤ iSup T := by
  have h : ∀ x : W, ∃ (T : X.Opens) (c : L.ι), IsAffineOpen T ∧ x.1 ∈ T ∧ T ≤ W ⊓ L.U c := fun x => by
    obtain ⟨i, hi⟩ := exists_chart hL x.1
    obtain ⟨T, hT, hx, hle⟩ := exists_isAffineOpen_mem_and_subset (U := W ⊓ L.U i) (x := x.1) ⟨x.2, hi⟩
    exact ⟨T, i, hT, hx, hle⟩
  choose T c hT hx hle using h
  obtain ⟨S, hS⟩ := hW.elim_finite_subcover (fun x => (T x : Set X)) (fun x => (T x).isOpen)
    fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hx _⟩
  refine ⟨S, inferInstance, fun a => T a, fun a => c a, fun a => hT a,
    fun a => (hle a).trans inf_le_left, fun a => (hle a).trans inf_le_right, fun y hy => ?_⟩
  obtain ⟨a, ha, h⟩ := Set.mem_iUnion₂.1 (hS hy)
  exact Opens.mem_iSup.2 ⟨⟨a, ha⟩, h⟩

theorem mulSecOfEq_zpowSec_app (σ : LB.Sec (lbZPow L m)) {a b c : ℕ} (hc : c = a + b) {d e : ℤ}
    (h₁ : n + a * m = d) (h₂ : d + b * m = e) (h₃ : n + c * m = e) {V : X.Opens}
    (t : Γ(twistZ F L n, V)) :
    (mulSecOfEq F (zpowSec σ b) h₂).app V ((mulSecOfEq F (zpowSec σ a) h₁).app V t) =
      (mulSecOfEq F (zpowSec σ c) h₃).app V t :=
  zsec_ext fun i => by
    simp only [zcoord_mulSecOfEq_app, zfun_zpowSec, hc, smul_smul, pow_add, map_mul, mul_comm]

variable [F.IsQuasicoherent]

theorem eventually_mulSecOfEq_zpowSec_eq_zero (hL : L.IsLB) (σ : LB.Sec (lbZPow L m))
    {W V : X.Opens} (hW : IsCompact (W : Set X)) (h : V ≤ W) (hV : W ⊓ Out.nonzeroLocus σ ≤ V)
    (a : Γ(twistZ F L n, W)) (ha : resM _ h a = 0) :
    ∀ᶠ k : ℕ in atTop, ∀ (d : ℤ) (hd : n + k * m = d),
      (mulSecOfEq F (zpowSec σ k) hd).app W a = 0 := by
  obtain ⟨κ, _, T, c, hT, hTW, hTc, hc⟩ := exists_finite_affine_chart_cover hL hW
  have key : ∀ α, ∀ᶠ k : ℕ in atTop,
      resG X (hTc α) (zfun σ (c α)) ^ k • zchartEquiv hL n (c α) (hTc α) (resM _ (hTW α) a) = 0 := by
    intro α
    obtain ⟨k, hk⟩ := QCoh.Qcqs.exists_pow_smul_eq_zero_of_isCompact F (hT α).isCompact
      (resG X (hTc α) (zfun σ (c α))) inf_le_left (basicOpen_resG_zfun σ _ (hTc α)).symm
      (zchartEquiv hL n (c α) (hTc α) (resM _ (hTW α) a)) (by
        have hle : T α ⊓ Out.nonzeroLocus σ ≤ V := (inf_le_inf_right _ (hTW α)).trans hV
        refine (zchartEquiv_resM hL (c α) (hTc α) inf_le_left _).symm.trans ?_
        rw [resM_resM, ← resM_resM h hle, ha, map_zero, map_zero])
    refine eventually_atTop.2 ⟨k, fun j hj => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hj
    rw [pow_add, mul_smul, hk, smul_zero]
  refine (eventually_all.2 key).mono fun k hk d hd => sec_ext_of_cover T hTW hc fun α => ?_
  apply (zchartEquiv hL d (c α) (hTc α)).injective
  rw [← app_resM, zchartEquiv_mulSecOfEq_app, zfun_zpowSec, map_pow, hk, map_zero, map_zero]

theorem eventually_exists_resM_eq_mulSecOfEq_zpowSec (hL : L.IsLB) (σ : LB.Sec (lbZPow L m))
    {W V : X.Opens} (hW : IsCompact (W : Set X)) (hW' : IsQuasiSeparated (W : Set X)) (h : V ≤ W)
    (hV : V = W ⊓ Out.nonzeroLocus σ) (b : Γ(twistZ F L n, V)) :
    ∀ᶠ k : ℕ in atTop, ∀ (d : ℤ) (hd : n + k * m = d), ∃ a : Γ(twistZ F L d, W),
      resM _ h a = (mulSecOfEq F (zpowSec σ k) hd).app V b := by
  obtain ⟨κ, _, T, c, hT, hTW, hTc, hc⟩ := exists_finite_affine_chart_cover hL hW
  have hTV : ∀ α, T α ⊓ V = T α ⊓ Out.nonzeroLocus σ := fun α => by
    rw [hV, ← inf_assoc, inf_eq_left.2 (hTW α)]
  have key : ∀ α, ∀ᶠ k : ℕ in atTop, ∃ a : Γ(twistZ F L (n + k * m), T α),
      resM _ (inf_le_left : T α ⊓ V ≤ T α) a =
        (mulSec F (zpowSec σ k) n).app _ (resM _ inf_le_right b) := by
    intro α
    have hc' : T α ⊓ V ≤ L.U (c α) := inf_le_left.trans (hTc α)
    obtain ⟨k, t, hk⟩ := QCoh.Qcqs.exists_pow_smul_eq_res_of_qcqs F (hT α).isCompact
      (hT α).isQuasiSeparated (resG X (hTc α) (zfun σ (c α))) (V := T α ⊓ V) inf_le_left
      ((hTV α).trans (basicOpen_resG_zfun σ _ (hTc α)).symm)
      (zchartEquiv hL n (c α) hc' (resM _ inf_le_right b))
    have hk' : resG X hc' (zfun σ (c α)) ^ k • zchartEquiv hL n (c α) hc' (resM _ inf_le_right b) =
        resM F inf_le_left t := by
      rw [← resG_resG (hTc α) inf_le_left]
      exact hk
    refine eventually_atTop.2 ⟨k, fun j hj => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hj
    refine ⟨(zchartEquiv hL _ (c α) (hTc α)).symm (resG X (hTc α) (zfun σ (c α)) ^ j • t), ?_⟩
    apply (zchartEquiv hL _ (c α) hc').injective
    rw [zchartEquiv_resM hL (c α) (hTc α), LinearEquiv.apply_symm_apply, zchartEquiv_mulSecOfEq_app,
      zfun_zpowSec, resM_smul, map_pow, map_pow, resG_resG, pow_add, mul_smul, hk']
  obtain ⟨k, hk⟩ := (eventually_all.2 key).exists
  choose a ha using hk
  have key₂ : ∀ p : κ × κ, ∀ᶠ j : ℕ in atTop, ∀ (d : ℤ) (hd : n + k * m + j * m = d),
      (mulSecOfEq F (zpowSec σ j) hd).app (T p.1 ⊓ T p.2)
        (resM _ inf_le_left (a p.1) - resM _ inf_le_right (a p.2)) = 0 := fun p => by
    refine eventually_mulSecOfEq_zpowSec_eq_zero hL σ
      (hW' _ _ (hTW p.1) (T p.1).isOpen (hT p.1).isCompact (hTW p.2) (T p.2).isOpen
        (hT p.2).isCompact) (V := T p.1 ⊓ T p.2 ⊓ V) inf_le_left
      (le_inf inf_le_left (hV.ge.trans' (inf_le_inf_right _ (inf_le_left.trans (hTW p.1))))) _ ?_
    have h₁ : T p.1 ⊓ T p.2 ⊓ V ≤ T p.1 ⊓ V := inf_le_inf_right _ inf_le_left
    have h₂ : T p.1 ⊓ T p.2 ⊓ V ≤ T p.2 ⊓ V := inf_le_inf_right _ inf_le_right
    rw [map_sub, resM_resM, resM_resM, ← resM_resM inf_le_left h₁, ← resM_resM inf_le_left h₂,
      ha, ha, ← app_resM, ← app_resM, resM_resM, resM_resM, sub_self]
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 (eventually_all.2 key₂)
  refine eventually_atTop.2 ⟨k + j₀, fun l hl d hd => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (le_of_add_le_left hl)
  have hd' : n + k * m + j * m = d := by rw [← hd]; push_cast; ring
  obtain ⟨t, ht⟩ := exists_sec_of_cover T hTW hc
    (fun α => (mulSecOfEq F (zpowSec σ j) hd').app _ (a α)) fun α β => by
      have := hj₀ j (by omega) (α, β) d hd'
      rw [map_sub, sub_eq_zero] at this
      rw [← app_resM, ← app_resM]
      exact this
  refine ⟨t, sec_ext_of_cover (fun α => T α ⊓ V) (fun _ => inf_le_right)
    ((le_inf (h.trans hc) le_rfl).trans (iSup_inf_eq _ _).le) fun α => ?_⟩
  rw [resM_resM, ← resM_resM (hTW α) inf_le_left, ht, ← app_resM, ha, ← app_resM,
    mulSecOfEq_zpowSec_app σ rfl]

end Twist

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsDehomogenisationTwistedChart
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.AbLaw.Dehom

open SecOn

variable {Y : Scheme.{0}} {M H : LB Y} {V : Y.Opens}

def secUnit (σ : LB.Sec H) (k : H.ι) {O : Y.Opens} (hk : O ≤ H.U k) (h : O ≤ nonzeroLocus σ) :
    Γ(Y, O)ˣ := (isUnit_rs_of_le_nonzeroLocus σ k hk h).unit

theorem val_secUnit (σ : LB.Sec H) (k : H.ι) {O : Y.Opens} (hk : O ≤ H.U k)
    (h : O ≤ nonzeroLocus σ) : (secUnit σ k hk h).val = rs Y hk (σ.f k) := rfl

theorem rs_secUnit_zpow (σ : LB.Sec H) (k : H.ι) {O O' : Y.Opens} (hk : O ≤ H.U k)
    (h : O ≤ nonzeroLocus σ) (e : O' ≤ O) (t : ℤ) :
    rs Y e (secUnit σ k hk h ^ t).val = (secUnit σ k (e.trans hk) (e.trans h) ^ t).val := by
  have : secUnit σ k (e.trans hk) (e.trans h) =
      Units.map (rs Y e).toMonoidHom (secUnit σ k hk h) :=
    Units.ext (rs_rs _ _ _).symm
  rw [this, ← map_zpow]
  rfl

theorem secUnit_compat (σ : LB.Sec H) (k l : H.ι) {O : Y.Opens} (hH : O ≤ H.U k ⊓ H.U l)
    (h : O ≤ nonzeroLocus σ) :
    secUnit σ k (hH.trans inf_le_left) h =
      res hH (H.g k l) * secUnit σ l (hH.trans inf_le_right) h :=
  Units.ext (GlobalTheory.LB.sec_rel σ k l _ (hH.trans inf_le_right) hH)


variable (M) in
def divPow (σ : LB.Sec H) (h : V ≤ nonzeroLocus σ) (t : ℤ) :
    SecOn (tw M H t) V →ₗ[Γ(Y, V)] SecOn (tw M H 0) V where
  toFun x := twMk 0
    (fun p k => (secUnit σ k (inf_le_right.trans inf_le_right) (inf_le_left.trans h) ^ (-t)).val *
      twCoord x p k)
    fun p q k l O hp hq hM hH => by
      rw [map_mul, map_mul, rs_secUnit_zpow, rs_secUnit_zpow, twCoord_compat x p q k l hp hq hM hH,
        secUnit_compat σ k l hH, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul,
        ← Units.val_mul]
      congr 2
      rw [mul_zpow, zpow_zero, _root_.mul_one, zpow_neg (res hH (H.g k l)), mul_mul_mul_comm,
        mul_comm _ (res hM (M.g p q)), mul_mul_mul_comm, inv_mul_cancel, _root_.mul_one]
  map_add' x y := tw_ext fun p k => by simp only [twCoord_twMk, twCoord_add, mul_add]
  map_smul' a x := tw_ext fun p k => mul_left_comm _ _ _

theorem twCoord_divPow (σ : LB.Sec H) (h : V ≤ nonzeroLocus σ) (t : ℤ) (x : SecOn (tw M H t) V)
    (p : M.ι) (k : H.ι) : twCoord (divPow M σ h t x) p k =
      (secUnit σ k (inf_le_right.trans inf_le_right) (inf_le_left.trans h) ^ (-t)).val *
        twCoord x p k := rfl

theorem divPow_zero (σ : LB.Sec H) (h : V ≤ nonzeroLocus σ) (x : SecOn (tw M H 0) V) :
    divPow M σ h 0 x = x :=
  tw_ext fun p k => by rw [twCoord_divPow, neg_zero, zpow_zero, Units.val_one, _root_.one_mul]

theorem divPow_injective (σ : LB.Sec H) (h : V ≤ nonzeroLocus σ) (t : ℤ) :
    Function.Injective (divPow M σ h t) := fun _ _ e =>
  tw_ext fun p k => (Units.isUnit _).mul_left_cancel (congrArg (twCoord · p k) e)

theorem divPow_mulSec (σ : LB.Sec H) (h : V ≤ nonzeroLocus σ) (t : ℤ) (x : SecOn (tw M H t) V) :
    divPow M σ h (t + 1) (mulSec M t σ V x) = divPow M σ h t x :=
  tw_ext fun p k => by
    rw [twCoord_divPow, twCoord_divPow, twCoord_mulSec, ← _root_.mul_assoc,
      ← val_secUnit σ k _ (inf_le_left.trans h), ← Units.val_mul, ← zpow_add_one]
    congr 3
    ring

variable {R : Type} [CommRing R] (f : Y ⟶ Spec (CommRingCat.of R)) {ι : Type} (s : ι → LB.Sec H)
  (hx : OperatorsCommute (ι := ι) (A := fun t => SecOnR f (tw M H t) V)
    fun i t => SecOnR.mulSec f M t (s i) V)
  (i : ι) (h : V ≤ nonzeroLocus (s i)) (r : ι → Γ(Y, V))
  (hr : ∀ j k, rs Y (inf_le_right : V ⊓ H.U k ≤ H.U k) ((s j).f k) =
    rs Y (inf_le_left : V ⊓ H.U k ≤ V) (r j) * rs Y (inf_le_right : V ⊓ H.U k ≤ H.U k) ((s i).f k))

def dehom : GrSum hx →ₛₗ[MvPolynomial.eval₂Hom (cst f V) r] SecOnR f (tw M H 0) V where
  toFun := GrSum.desc hx fun t => SecOnR.lin f (divPow M (s i) h t)
  map_add' := map_add _
  map_smul' p m := by
    have hX (j : ι) (m : GrSum hx) :
        GrSum.desc hx (fun t => SecOnR.lin f (divPow M (s i) h t))
          ((MvPolynomial.X j : MvPolynomial ι R) • m) =
        r j • GrSum.desc hx (fun t => SecOnR.lin f (divPow M (s i) h t)) m := by
      induction m using DirectSum.Decomposition.inductionOn (GrSum.grading hx) with
      | zero => simp
      | add a b ha hb => rw [smul_add, map_add (f := _), map_add (f := _), smul_add, ha, hb]
      | @homogeneous n a =>
        obtain ⟨_, a, rfl⟩ := a
        rw [GrSum.X_smul_of, GrSum.desc_of, GrSum.desc_of]
        have e (b : SecOn (tw M H n) V) :
            divPow M (s i) h (n + 1) (mulSec M n (s j) V b) = r j • divPow M (s i) h n b := by
          rw [mulSec_eq_smul (s i) (s j) (r j) (hr j), map_smul, divPow_mulSec]
        exact e a
    induction p using MvPolynomial.induction_on generalizing m with
    | C a =>
      rw [MvPolynomial.eval₂Hom_C, ← MvPolynomial.algebraMap_eq, algebraMap_smul, map_smul]
      rfl
    | add p q hp hq => rw [add_smul, map_add (f := _), map_add (f := _), add_smul, hp, hq]
    | mul_X p j hp => rw [mul_smul, hp, hX, map_mul, MvPolynomial.eval₂Hom_X', mul_smul]

theorem dehom_of (t : ℤ) (a : SecOnR f (tw M H t) V) :
    dehom f s hx i h r hr (GrSum.of hx t a) = SecOnR.lin f (divPow M (s i) h t) a :=
  GrSum.desc_of hx _ t a


include h hr in
theorem ratio_self : r i = 1 := by
  refine Y.sheaf.eq_of_locally_eq' (fun k : H.ι => V ⊓ H.U k) V
    (fun k => homOfLE inf_le_left) (fun x hx => ?_) _ _ fun k => ?_
  · obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 (h hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨l, hx, Y.basicOpen_le _ hl⟩
  · change rs Y inf_le_left (r i) = rs Y inf_le_left 1
    rw [map_one]
    exact (isUnit_rs_of_le_nonzeroLocus (s i) k inf_le_right
      (inf_le_left.trans h)).mul_right_cancel ((hr i k).symm.trans (_root_.one_mul _).symm)

theorem exists_dehom_top
    (hx : ∀ V : Y.Opens, OperatorsCommute (ι := ι) (A := fun t => SecOnR f (tw M H t) V)
      fun i t => SecOnR.mulSec f M t (s i) V)
    (i : ι) (h : V ≤ nonzeroLocus (s i)) (r : ι → Γ(Y, V))
    (hr : ∀ j k, rs Y (inf_le_right : V ⊓ H.U k ≤ H.U k) ((s j).f k) =
      rs Y (inf_le_left : V ⊓ H.U k ≤ V) (r j) *
        rs Y (inf_le_right : V ⊓ H.U k ≤ H.U k) ((s i).f k))
    (h₁ : ∀ (t : ℤ) (a : SecOnR f (tw M H t) ⊤), SecOnR.restrict f _ (le_top : V ≤ ⊤) a = 0 →
      ∃ k : ℕ, xProd R {i} ^ k • GrSum.of (hx ⊤) t a = 0)
    (h₂ : ∀ (t : ℤ) (y : SecOnR f (tw M H t) V), ∃ (k : ℕ) (t' : ℤ) (a : SecOnR f (tw M H t') ⊤),
      GrSum.of (hx V) t' (SecOnR.restrict f _ le_top a) = xProd R {i} ^ k • GrSum.of (hx V) t y) :
    ∃ ε : GrSum (hx ⊤) →ₛₗ[MvPolynomial.eval₂Hom (cst f V) r] SecOn (tw M H 0) V,
      Function.Surjective ε ∧
      (∀ n, ∀ y ∈ GrSum.grading (hx ⊤) n, ε y = 0 →
        ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0) ∧
      ∀ a : SecOn (tw M H 0) ⊤,
        ε (GrSum.of (hx ⊤) 0 (SecOnR.of f _ ⊤ a)) = SecOn.restrict _ le_top a := by
  have hp : xProd R {i} = MvPolynomial.X i := Finset.prod_singleton _ _
  rw [hp] at h₁ h₂
  have hi := ratio_self s i h r hr
  obtain ⟨ρ, hρ⟩ : ∃ ρ : GrSum (hx ⊤) →ₗ[MvPolynomial ι R] GrSum (hx V), ∀ t a,
      ρ (GrSum.of (hx ⊤) t a) = GrSum.of (hx V) t (SecOnR.restrict f _ le_top a) :=
    ⟨_, GrSum.map_of (hx ⊤) (hx V) (fun t => SecOnR.restrict f (tw M H t) le_top) fun j t a =>
      (SecOn.mulSec_restrict (s j) le_top a).symm⟩
  let ε : GrSum (hx ⊤) →ₛₗ[MvPolynomial.eval₂Hom (cst f V) r] SecOnR f (tw M H 0) V :=
    (dehom f s (hx V) i h r hr).comp ρ
  have hε (t : ℤ) (a : SecOnR f (tw M H t) ⊤) : ε (GrSum.of (hx ⊤) t a) =
      dehom f s (hx V) i h r hr (GrSum.of (hx V) t (SecOnR.restrict f _ le_top a)) := by
    rw [← hρ]
    exact LinearMap.comp_apply _ _ _
  have s₁ : Function.Surjective ε := fun y => by
    obtain ⟨k, t, a, e⟩ := h₂ 0 y
    refine ⟨GrSum.of (hx ⊤) t a, (hε t a).trans ?_⟩
    rw [e, map_smulₛₗ, map_pow, MvPolynomial.eval₂Hom_X', hi, one_pow, one_smul, dehom_of]
    exact divPow_zero (s i) h y
  have s₂ : ∀ n, ∀ y ∈ GrSum.grading (hx ⊤) n, ε y = 0 →
      ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0 := by
    rintro n _ ⟨a, rfl⟩ ha
    rw [hε, dehom_of] at ha
    exact h₁ n a ((map_eq_zero_iff _ (divPow_injective (s i) h n)).1 ha)
  have s₃ (a : SecOnR f (tw M H 0) ⊤) :
      ε (GrSum.of (hx ⊤) 0 a) = SecOnR.restrict f _ le_top a := by
    rw [hε, dehom_of]
    exact divPow_zero (s i) h _
  exact ⟨ε, s₁, s₂, s₃⟩

end GlobalTheory.AbLaw.Dehom

namespace GlobalTheory.AbLaw

open Dehom

theorem exists_dehom_chart : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∀ (hx : ∀ V : Y.Opens, OperatorsCommute (ι := Fin (m + 1)) (A := fun t => SecOnR f (tw M H t) V) fun i t => SecOnR.mulSec f M t (s i) V) (i : Fin (m + 1)) (r : Fin (m + 1) → Γ(Y, nonzeroLocus (s i))), (∀ j k, rs Y (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s j).f k) = rs Y (inf_le_left : nonzeroLocus (s i) ⊓ H.U k ≤ nonzeroLocus (s i)) (r j) * rs Y (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s i).f k)) → r i = 1 ∧ ∃ ε : GrSum (hx ⊤) →ₛₗ[MvPolynomial.eval₂Hom (cst f (nonzeroLocus (s i))) r] SecOn (tw M H 0) (nonzeroLocus (s i)), Function.Surjective ε ∧ (∀ n, ∀ y ∈ GrSum.grading (hx ⊤) n, ε y = 0 → ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) R) ^ k • y = 0) ∧ ∀ a : SecOn (tw M H 0) ⊤, ε (GrSum.of (hx ⊤) 0 (SecOnR.of f _ ⊤ a)) = SecOn.restrict _ le_top a := by
  intro R _ Y f H m s M hH hM hs hx i r hr
  have key : ∀ V : Y.Opens, (⨅ j ∈ ({i} : Finset (Fin (m + 1))), nonzeroLocus (s j)) = V →
      (∀ (t : ℤ) (a : SecOnR f (tw M H t) ⊤), SecOnR.restrict f _ (le_top : V ≤ ⊤) a = 0 →
        ∃ k : ℕ, xProd R {i} ^ k • GrSum.of (hx ⊤) t a = 0) ∧
      ∀ (t : ℤ) (y : SecOnR f (tw M H t) V), ∃ (k : ℕ) (t' : ℤ) (a : SecOnR f (tw M H t') ⊤),
        GrSum.of (hx V) t' (SecOnR.restrict f _ le_top a) = xProd R {i} ^ k • GrSum.of (hx V) t y := by
    rintro _ rfl
    exact GlobalTheory.T.twistedSections_localise_to_charts R Y f H m s M hH hM hs hx {i}
  obtain ⟨h₁, h₂⟩ := key (nonzeroLocus (s i)) (by simp)
  exact ⟨ratio_self s i le_rfl r hr, exists_dehom_top f s hx i le_rfl r hr h₁ h₂⟩

end GlobalTheory.AbLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsTwistedSectionsCubeBijective
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory

section

variable {R : Type} [CommRing R] {Y : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of R)} {H : LB Y}
  {ι : Type} {s : ι → LB.Sec H} {M : LB Y}
  (hx : ∀ V : Y.Opens, OperatorsCommute (ι := ι) (A := fun t => SecOnR f (tw M H t) V)
    fun i t => SecOnR.mulSec f M t (s i) V)

noncomputable def twistedSumRestrict {V W : Y.Opens} (h : W ≤ V) :
    GrSum (hx V) →ₗ[MvPolynomial ι R] GrSum (hx W) :=
  GrSum.map (hx V) (hx W) (fun t => SecOnR.restrict f (tw M H t) h)
    fun i _ a => (SecOn.mulSec_restrict (s i) h a).symm

theorem twistedSumRestrict_of {V W : Y.Opens} (h : W ≤ V) (t : ℤ) (a : SecOnR f (tw M H t) V) :
    twistedSumRestrict hx h (GrSum.of (hx V) t a) =
      GrSum.of (hx W) t (SecOnR.restrict f (tw M H t) h a) :=
  GrSum.map_of (hx V) (hx W) (fun t => SecOnR.restrict f (tw M H t) h)
    (fun i _ a => (SecOn.mulSec_restrict (s i) h a).symm) t a

theorem twistedSumRestrict_comp {U V W : Y.Opens} (h : V ≤ U) (h' : W ≤ V) (y : GrSum (hx U)) :
    twistedSumRestrict hx h' (twistedSumRestrict hx h y) =
      twistedSumRestrict hx (h'.trans h) y := by
  have e : ((twistedSumRestrict hx h' ∘ₗ twistedSumRestrict hx h).restrictScalars R) =
      (twistedSumRestrict hx (h'.trans h)).restrictScalars R :=
    GrSum.lhom_ext _ fun n a => by
      simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, twistedSumRestrict_of,
        SecOnR.restrict_restrict]
  exact congr($e y)

end

theorem exists_grCube_twistedSections_hom_secCube_bijective :
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∀ (hx : ∀ V : Y.Opens, OperatorsCommute (ι := Fin (m + 1)) (A := fun t => SecOnR f (tw M H t) V) fun i t => SecOnR.mulSec f M t (s i) V) (t : ℤ), ∃ φ : grCube (Fin (m + 1)) (GrSum.grading (hx ⊤)) t ⟶ secCube f (tw M H t) (fun i => nonzeroLocus (s i)), ∀ I, Function.Bijective (φ.app I).hom := by
  intro R _ Y f H m s M hH hM hva hx
  have hloc := GlobalTheory.T.twistedSections_localise_to_charts R Y f H m s M hH hM hva hx
  refine GlobalTheory.exists_grCube_hom_bijective (Fin (m + 1)) R (GrSum (hx ⊤)) (GrSum.grading (hx ⊤))
    (fun t => secCube f (tw M H t) fun i => nonzeroLocus (s i))
    (fun i t => secCubeMul f M _ t (s i)) (fun I => hx (⨅ i ∈ I, nonzeroLocus (s i)))
    (fun I => twistedSumRestrict hx (le_top : (⨅ i ∈ I, nonzeroLocus (s i)) ≤ ⊤))
    (fun I => GrSum.isGradedMap_map _ _ _ _) (fun I J h n y a e => ?_)
    (fun I i hi t => SecOnR.mulSec_bijective f t (s i) (biInf_le (fun i => nonzeroLocus (s i)) hi))
    (fun I n y hy e => ?_) (fun I t a => ?_)
  · have h' := iInf_le_iInf_of_subset (fun i => nonzeroLocus (s i)) h
    exact (twistedSumRestrict_comp hx le_top h' y).symm.trans
      ((congrArg (twistedSumRestrict hx h') e).trans (twistedSumRestrict_of hx h' n a))
  · obtain ⟨a, rfl⟩ := hy
    refine (hloc I).1 n a (GrSum.of_injective (hx _) n ?_)
    exact ((twistedSumRestrict_of hx le_top n a).symm.trans e).trans (map_zero _).symm
  · obtain ⟨k, t', b, hb⟩ := (hloc I).2 t a
    exact ⟨k, GrSum.of (hx ⊤) t' b, (twistedSumRestrict_of hx le_top t' b).trans hb⟩

end GlobalTheory
end

