module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormFactorizationClause
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormByPlaces

@[expose] public section

set_option linter.style.haveILetI false

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

namespace LocAt

variable {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F] [IsFractionRing R F]

def IntAt (p : Ideal R) (x : F) : Prop :=
  ∃ a s : R, s ∉ p ∧ x * algebraMap R F s = algebraMap R F a

def UnitAt (p : Ideal R) (x : F) : Prop :=
  ∃ a s : R, a ∉ p ∧ s ∉ p ∧ x * algebraMap R F s = algebraMap R F a

variable {p : Ideal R} [hP : p.IsPrime]
include hP

omit [IsDomain R] [IsFractionRing R F] in
theorem intAt_mul {x y : F} (hx : IntAt p x) (hy : IntAt p y) : IntAt p (x * y) := by
  obtain ⟨a, s, hs, hxs⟩ := hx
  obtain ⟨b, t, ht, hyt⟩ := hy
  refine ⟨a * b, s * t, fun h => (hP.mem_or_mem h).elim hs ht, ?_⟩
  rw [map_mul, map_mul, ← hxs, ← hyt]
  ring

omit [IsDomain R] [IsFractionRing R F] in
theorem unitAt_mul {x y : F} (hx : UnitAt p x) (hy : UnitAt p y) : UnitAt p (x * y) := by
  obtain ⟨a, s, ha, hs, hxs⟩ := hx
  obtain ⟨b, t, hb, ht, hyt⟩ := hy
  refine ⟨a * b, s * t, fun h => (hP.mem_or_mem h).elim ha hb,
    fun h => (hP.mem_or_mem h).elim hs ht, ?_⟩
  rw [map_mul, map_mul, ← hxs, ← hyt]
  ring

omit [IsDomain R] [IsFractionRing R F] in
theorem unitAt_one : UnitAt p (1 : F) := by
  have h1 : (1 : R) ∉ p := fun h => hP.ne_top ((Ideal.eq_top_iff_one p).mpr h)
  exact ⟨1, 1, h1, h1, by simp⟩

omit [IsDomain R] [IsFractionRing R F] in
theorem unitAt_intAt {x : F} (hx : UnitAt p x) : IntAt p x := by
  obtain ⟨a, s, _, hs, h⟩ := hx
  exact ⟨a, s, hs, h⟩

omit [IsDomain R] [IsFractionRing R F] in
theorem unitAt_alg {r : R} (hr : r ∉ p) : UnitAt p (algebraMap R F r) := by
  have h1 : (1 : R) ∉ p := fun h => hP.ne_top ((Ideal.eq_top_iff_one p).mpr h)
  exact ⟨r, 1, hr, h1, by simp⟩

theorem unitAt_inv {x : F} (hx : UnitAt p x) : UnitAt p x⁻¹ := by
  obtain ⟨a, s, ha, hs, h⟩ := hx
  refine ⟨s, a, hs, ha, ?_⟩
  have ha0 : algebraMap R F a ≠ 0 := by
    intro h0
    apply ha
    have h00 : a = 0 := IsFractionRing.injective R F (by rw [h0, map_zero])
    rw [h00]
    exact p.zero_mem
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply ha0
    rw [← h, zero_mul]
  rw [← h, ← mul_assoc, inv_mul_cancel₀ hx0, one_mul]

omit [IsDomain R] [IsFractionRing R F] in
theorem unitAt_pow {x : F} (hx : UnitAt p x) (n : ℕ) : UnitAt p (x ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact unitAt_one
  | succ n ih => rw [pow_succ]; exact unitAt_mul ih hx

theorem unitAt_zpow {x : F} (hx : UnitAt p x) (n : ℤ) : UnitAt p (x ^ n) := by
  cases n with
  | ofNat n =>
    show UnitAt p (x ^ (n : ℤ))
    rw [zpow_natCast]
    exact unitAt_pow hx n
  | negSucc n =>
    rw [zpow_negSucc]
    exact unitAt_inv (unitAt_pow hx (n + 1))

omit [IsDomain R] [IsFractionRing R F] in
theorem unitAt_prod {κ : Type*} (s : Finset κ) (f : κ → F) (hf : ∀ i ∈ s, UnitAt p (f i)) :
    UnitAt p (∏ i ∈ s, f i) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.prod_empty]
    exact unitAt_one
  · intro i s hi ih hf
    rw [Finset.prod_insert hi]
    exact unitAt_mul (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

end LocAt

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem gen_prime' {q : Ideal (KTp K d.D d.N)} (hq : q ∈ d.HtOne) : Prime (d.gen q) :=
  ValUFD.gen_prime (fun p hp hh => d.gen_span ⟨hp, hh⟩) hq

theorem gen_not_mem {p q : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) (hq : q ∈ d.HtOne)
    (hqp : q ≠ p) : d.gen q ∉ p := by
  intro hm
  rw [d.gen_span hp, Ideal.mem_span_singleton] at hm
  have e := (ValUFD.gen_dvd_iff (fun p hp hh => d.gen_span ⟨hp, hh⟩) hp (d.gen_prime' hq)).mp hm
  exact hqp (by rw [e, ← d.gen_span hq])

theorem split_at (E : Ideal (KTp K d.D d.N) → ℤ) (hE : {q | q ∈ d.HtOne ∧ E q ≠ 0}.Finite)
    {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    ∃ V : KTf K d.D d.N, LocAt.UnitAt p V ∧
      (∏ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q) =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ E p * V := by
  haveI := hp.1
  have hfin : ((d.HtOne \ {p}) ∩ Function.mulSupport
      (fun q => algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q)).Finite := by
    refine hE.subset ?_
    rintro q ⟨⟨hq, _⟩, hq1⟩
    refine ⟨hq, fun h0 => (Function.mem_mulSupport.mp hq1) ?_⟩
    simp [h0]
  refine ⟨∏ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne \ {p}), algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q, ?_, ?_⟩
  · rw [← finprod_mem_inter_mulSupport, finprod_mem_eq_finite_toFinset_prod _ hfin]
    apply LocAt.unitAt_prod
    intro q hq
    rw [Set.Finite.mem_toFinset] at hq
    obtain ⟨⟨hq1, hq2⟩, _⟩ := hq
    exact LocAt.unitAt_zpow
      (LocAt.unitAt_alg (d.gen_not_mem hp hq1 (fun h => hq2 (Set.mem_singleton_iff.mpr h)))) _
  · have hins : d.HtOne = insert p (d.HtOne \ {p}) := by
      ext x
      by_cases hx : x = p
      · subst hx
        simp [hp]
      · simp [hx]
    conv_lhs => rw [hins]
    rw [finprod_mem_insert' _ (by simp) hfin]

theorem b_mem_p (hd : d.AxH 𝒜) (h : d.S1) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    (k : Fin d.del) (c : ι) (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ))
    (hw : w ∈ d.GoodP c p) :
    0 ≤ w (d.bvecG hd.sel hd.a4.choose k c) +
      ((d.ord c (d.Wres c w) d.wF (hd.a4.choose c) : ℤ) : WithTop ℤ) := by
  classical
  obtain ⟨he, -, -⟩ := hd.a4.choose_spec
  obtain ⟨heF, he0⟩ := he c
  have hadm := d.good_adm hd h c hp hw
  have hthpF : d.thp (hd.sel k) c ∈ 𝒜 c d.wF := hd.thp_mem _ c
  obtain ⟨a, ha⟩ : ∃ a : Ω c, d.thp (hd.sel k) c = a • hd.a4.choose c := by
    have he0' : (⟨hd.a4.choose c, heF⟩ : 𝒜 c d.wF) ≠ 0 := by
      intro h0; exact he0 (congrArg Subtype.val h0)
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ he0').mp (hd.finrank_one c d.wF)
      ⟨_, hthpF⟩
    exact ⟨a, (congrArg Subtype.val ha).symm⟩
  have hb : d.bvecG hd.sel hd.a4.choose k c = algebraMap (Ω c) (OmS (Ω c) d.D d.N) a := by
    simp only [bvecG]
    rw [ValuationResidueLemmas.ratio_eq he0 ha]
  rw [hb]
  change 0 ≤ d.Wres c w a + _
  by_cases ha0 : a = 0
  · rw [ha0, AddValuation.map_zero, top_add]
    exact le_top
  have hth0 : d.thp (hd.sel k) c ≠ 0 := by
    rw [ha]; exact smul_ne_zero ha0 he0
  rw [← hd.ord_smul c _ hadm a heF he0 ha0, ← ha]
  have hmem : d.thp (hd.sel k) ∈ d.Thp := by
    rw [hd.Thp_span]; exact Submodule.subset_span ⟨_, rfl⟩
  exact_mod_cast hd.ord_nonneg_Thp c _ hadm _ hmem hth0

theorem de_local (hd : d.AxH 𝒜) (h : d.S1) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    LocAt.IntAt p (d.De hd h * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
      (2 * ∑ c, d.nP h c d.wF (hd.a4.choose c) p)) := by
  classical
  letI : ∀ c, Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.KTtoS h c).toAlgebra
  haveI : ∀ c, FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => by
    haveI := d.KT_finiteDimensional hd c
    let e : KTf K d.D d.N ≃+* d.KT c :=
      (d.KTtoS h c).rangeRestrictFieldEquiv.trans (RingEquiv.subfieldCongr (d.KTtoS_fieldRange h c))
    apply Module.Finite.of_equiv_equiv e.symm (RingEquiv.refl (OmS (Ω c) d.D d.N))
    refine RingHom.ext fun x => ?_
    change d.KTtoS h c (e.symm x) = (x : OmS (Ω c) d.D d.N)
    exact congrArg (fun y : d.KT c => (y : OmS (Ω c) d.D d.N)) (e.apply_symm_apply x)
  haveI : CharZero (KTf K d.D d.N) :=
    charZero_of_injective_algebraMap (algebraMap K (KTf K d.D d.N)).injective
  haveI : ∀ c, Algebra.IsSeparable (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c =>
    Algebra.IsSeparable.of_integral _ _
  haveI := hp.1
  have hsH : ∀ c x, d.sH c x = algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) x) := fun c x =>
    (IsFractionRing.lift_algebraMap (A := KTp K d.D d.N) (g := (d.sH c).toRingHom) (h c) x).symm
  have hOver : ∀ c, d.OverP c p =
      HNm.OverR (R := KTp K d.D d.N) (F := KTf K d.D d.N)
        (L := OmS (Ω c) d.D d.N) p := by
    intro c; ext w; simp only [OverP, HNm.OverR, Set.mem_ofPred_eq, hsH]
  let n : ∀ c, AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ) → ℤ := fun c w =>
    if w ∈ d.GoodP c p then d.ord c (d.Wres c w) d.wF (hd.a4.choose c) else 0
  have hb : ∀ k c, ∀ w ∈ HNm.OverR (R := KTp K d.D d.N) (F := KTf K d.D d.N)
      (L := OmS (Ω c) d.D d.N) p,
      0 ≤ w (d.bvecG hd.sel hd.a4.choose k c) + (n c w : WithTop ℤ) := by
    intro k c w hw
    rw [← hOver c] at hw
    by_cases hg : w ∈ d.GoodP c p
    · simp only [n, if_pos hg]
      exact d.b_mem_p hd h hp k c w hg
    · simp only [n, if_neg hg, WithTop.coe_zero, add_zero]
      have hz : ∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0 := fun a ha =>
        by_contra fun hne => hg ⟨hw, a, ha, hne⟩
      change 0 ≤ d.Wres c w _
      by_cases hr : ratio (Ω := Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c) = 0
      · rw [hr, AddValuation.map_zero]; exact le_top
      · rw [hz _ hr]
  have hexp : ∀ c, (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ))
      (_ : w ∈ HNm.OverR (R := KTp K d.D d.N) (F := KTf K d.D d.N)
        (L := OmS (Ω c) d.D d.N) p),
        (HNm.fz (F := KTf K d.D d.N) w : ℤ) * n c w) = d.nP h c d.wF (hd.a4.choose c) p := by
    intro c
    rw [← hOver c]
    simp only [nP]
    rw [finsum_mem_def, finsum_mem_def]
    refine finsum_congr fun w => ?_
    simp only [Set.indicator_apply, n]
    by_cases hg : w ∈ d.GoodP c p
    · have hg1 : w ∈ d.OverP c p := hg.1
      simp only [hg, hg1, if_true]
      rfl
    · simp only [hg, if_false, mul_zero, ite_self]
  open IsDedekindDomain IsLocalRing Module in
  have disc_local {R F : Type} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field F]
        [Algebra R F] [IsFractionRing R F] {ι : Type} [Fintype ι] [DecidableEq ι]
        {L : ι → Type} [∀ c, Field (L c)] [∀ c, Algebra F (L c)]
        [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)] (p : Ideal R) [p.IsPrime] (hp : p.height = 1) (g : R) (hg : p = Ideal.span {g})
      (n : ∀ c, AddValuation (L c) (WithTop ℤ) → ℤ)
      {m : ℕ} (hm : m = ∑ c, finrank F (L c)) (b : Fin m → ∀ c, L c) (hli : LinearIndependent F b)
      (hb : ∀ k c, ∀ w ∈ HNm.OverR (R := R) (F := F) (L := L c) p,
        0 ≤ w (b k c) + (n c w : WithTop ℤ)) :
      ∃ a s : R, s ∉ p ∧
        (Matrix.of fun k l : Fin m => ∑ c, Algebra.trace F (L c) (b k c * b l c)).det *
          algebraMap R F g ^ (2 * ∑ c, ∑ᶠ (w : AddValuation (L c) (WithTop ℤ))
            (_ : w ∈ HNm.OverR (R := R) (F := F) (L := L c) p), (HNm.fz (F := F) w : ℤ) * n c w) *
          algebraMap R F s =
          algebraMap R F a := by
    classical
    let O := Localization.AtPrime p
    letI : Algebra O F := IsLocalization.localizationAlgebraOfSubmonoidLe O F p.primeCompl
      (nonZeroDivisors R) (Ideal.primeCompl_le_nonZeroDivisors p)
    haveI : IsScalarTower R O F := IsLocalization.localization_isScalarTower_of_submonoid_le O F
      p.primeCompl (nonZeroDivisors R) (Ideal.primeCompl_le_nonZeroDivisors p)
    haveI : IsFractionRing O F :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl O F
    obtain ⟨hdvr, hirr⟩ := ValUFD.loc_dvr p hp g hg
    haveI := hdvr
    letI : ∀ c, Algebra O (L c) := fun c => ((algebraMap F (L c)).comp (algebraMap O F)).toAlgebra
    haveI : ∀ c, IsScalarTower O F (L c) := fun c => IsScalarTower.of_algebraMap_eq' rfl
    letI : ∀ c, Algebra R (L c) := fun c => ((algebraMap F (L c)).comp (algebraMap R F)).toAlgebra
    haveI : ∀ c, IsScalarTower R O (L c) := fun c => IsScalarTower.of_algebraMap_eq (fun x => by
      show algebraMap F (L c) (algebraMap R F x) =
        algebraMap F (L c) (algebraMap O F (algebraMap R O x))
      rw [IsScalarTower.algebraMap_apply R O F x])
    have hded : ∀ c, IsDedekindDomain (integralClosure O (L c)) := fun c =>
      (ReciprocityTheory.MultiplicativeHeights.Closed.dedekindRank O F (L c)).1
    have hfr : ∀ c, IsFractionRing (integralClosure O (L c)) (L c) := fun c =>
      integralClosure.isFractionRing_of_finite_extension F (L c)
    have hset : ∀ c, ValPl.PlacesOver O (L c) = HNm.OverR (R := R) (F := F) (L := L c) p := fun c => by
      ext w
      simp only [ValPl.PlacesOver, HNm.OverR, Set.mem_ofPred_eq]
      rw [← ValPl.placesOver_iff_loc (R := R) p w]
      rfl
    have hG : ∀ c, ∃ gc : L c, gc ≠ 0 ∧ (∀ w ∈ ValPl.PlacesOver O (L c), w gc = n c w) ∧
        ∀ y, (∀ w ∈ ValPl.PlacesOver O (L c), 0 ≤ w y + (n c w : WithTop ℤ)) ↔
          gc * y ∈ integralClosure O (L c) := fun c => by
      haveI := hded c
      haveI := hfr c
      obtain ⟨gc, hg0, hgv⟩ := HDiscVal.exists_val_eq O F (n c)
      refine ⟨gc, hg0, hgv, fun y => ?_⟩
      rw [HDiscVal.mem_integralClosure_iff O F]
      refine forall₂_congr fun w hw => ?_
      rw [AddValuation.map_mul, hgv w hw, add_comm]
    choose gc hgc0 hgcv hgciff using hG
    have hbI : ∀ k c, gc c * b k c ∈ integralClosure O (L c) := fun k c =>
      (hgciff c _).mp (fun w hw => hb k c w (hset c ▸ hw))
    obtain ⟨nn, t, u, -, hdisc⟩ := HDiscLat.lattice_main (R := O) (F := F) hirr gc hgc0 hm b hbI hli
    set Nc : ι → ℤ := fun c => ∑ᶠ (w : AddValuation (L c) (WithTop ℤ))
      (_ : w ∈ HNm.OverR (R := R) (F := F) (L := L c) p), (HNm.fz (F := F) w : ℤ) * n c w with hNc
    have hN : ∀ c, ∃ uc : O, IsUnit uc ∧ Algebra.norm F (gc c) =
        algebraMap R F g ^ Nc c * algebraMap O F uc := fun c => by
      haveI := hded c
      haveI := hfr c
      obtain ⟨uc, huc, hn⟩ := ValPl.norm_eq_places (O := O) (F := F) (gc c) (hgc0 c) hirr
      refine ⟨uc, huc, ?_⟩
      rw [hn, ← IsScalarTower.algebraMap_apply R O F g, hset c]
      congr 2
      refine finsum_congr fun w => finsum_congr fun hw => ?_
      rw [← hset c] at hw
      rw [hgcv c w hw, WithTop.untopD_coe]
      rfl
    choose uc huc hNe using hN
    set X := algebraMap R F g with hX
    have hX0 : X ≠ 0 := by
      rw [hX, map_ne_zero_iff _ (IsFractionRing.injective R F)]
      rintro rfl
      have : p = ⊥ := by rw [hg, Ideal.span_singleton_eq_bot]
      subst this
      simp at hp
    let U : Oˣ := ∏ c, (huc c).unit
    have hprod : ∏ c, Algebra.norm F (gc c) = X ^ (∑ c, Nc c) * algebraMap O F (U : O) := by
      rw [Finset.prod_congr rfl fun c _ => hNe c, Finset.prod_mul_distrib, HDiscOmL.prod_zpow hX0,
        ← map_prod]
      congr 2
      simp only [U, Units.coe_prod, IsUnit.unit_spec]
    rw [hprod] at hdisc
    set Dt := (Matrix.of fun k l : Fin m => ∑ c, Algebra.trace F (L c) (b k c * b l c)).det with hDt
    obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.mk'_surjective p.primeCompl
      ((u : O) * ((algebraMap R O g) ^ (2 * nn + t)) * ((U⁻¹ : Oˣ) : O) * ((U⁻¹ : Oˣ) : O))
    refine ⟨a, s, s.2, ?_⟩
    have hsF : algebraMap O F (IsLocalization.mk' O a s) * algebraMap R F s = algebraMap R F a := by
      rw [IsScalarTower.algebraMap_apply R O F s, IsScalarTower.algebraMap_apply R O F a, ← map_mul,
        IsLocalization.mk'_spec]
    simp only at has
    rw [← hsF, has]
    congr 1
    set V := algebraMap O F (U : O)
    set V' := algebraMap O F ((U⁻¹ : Oˣ) : O)
    have hU : V * V' = 1 := by
      simp only [V, V']
      rw [← map_mul, Units.mul_inv, map_one]
    have h2 : X ^ (2 * ∑ c, Nc c) = (X ^ (∑ c, Nc c)) ^ 2 := by
      rw [mul_comm, zpow_mul]
      norm_cast
    have e1 : algebraMap O F ((u : O) * (algebraMap R O g) ^ (2 * nn + t) * ((U⁻¹ : Oˣ) : O) *
        ((U⁻¹ : Oˣ) : O)) = algebraMap O F ((u : O) * (algebraMap R O g) ^ (2 * nn + t)) * V' * V' := by
      simp only [V', map_mul]
    rw [h2, e1, ← hdisc]
    calc Dt * (X ^ ∑ c, Nc c) ^ 2 = Dt * (X ^ ∑ c, Nc c) ^ 2 * (V * V') * (V * V') := by
          rw [hU]; ring
      _ = Dt * ((X ^ ∑ c, Nc c) * V) ^ 2 * V' * V' := by ring
  obtain ⟨a, s, hs, he⟩ := disc_local (R := KTp K d.D d.N) (F := KTf K d.D d.N)
    (L := fun c => OmS (Ω c) d.D d.N) p hp.2 (d.gen p) (d.gen_span hp) n (d.del_eq hd h)
    (d.bvecG hd.sel hd.a4.choose) (d.b_linIndep hd h) hb
  refine ⟨a, s, hs, ?_⟩
  rw [← he]
  simp only [hexp]
  rfl

end Data

end ReciprocityTheory.ChartRestriction.G.T0
