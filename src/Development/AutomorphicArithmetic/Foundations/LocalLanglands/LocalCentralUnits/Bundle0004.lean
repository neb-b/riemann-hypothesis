module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
public import Mathlib
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0005
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0017
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0002
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0015
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.FinrankK
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TameRecAll

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ResBase
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil Module ValuativeRel DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

private theorem base_cong {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E']
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    (g : ℕ) [Fact g.Prime] (n : ℕ) (hn : 0 < n) (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (hgv : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal) (hgv2 : ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2)
    (hgw : ((g : ℕ) : 𝓞 E') ∈ w'.asIdeal) (hgw2 : ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2)
    (hvN : normV w = g) (hwN : normV w' = g ^ n)
    (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a')
    (π : Ω) (hπ : π ^ (g ^ n - 1) = (g : Ω))
    (s : Ine (F := E) A) (t' : Ine (F := E') A) (htt : ∀ z : Ω, (s : G E Ω) z = (t' : G E' Ω) z)
    (y : 𝓞 E) (hy : Valued.v ((a (ineIncl h s) : w.adicCompletion E) - algebraMap E (w.adicCompletion E) (y : E)) < 1)
    (x : 𝓞 E') (hx : Valued.v ((a' (ineIncl h' t') : w'.adicCompletion E') -
      algebraMap E' (w'.adicCompletion E') (x : E')) < 1) :
    A.valuation (algebraMap E Ω (y : E) - algebraMap E' Ω (x : E') ^ ((g ^ n - 1) / (g - 1))) < 1 := by
  have hTR := tameRecAll
  have hg1 : 1 < g := (Fact.out : g.Prime).one_lt
  have hdvd : (g - 1) ∣ (g ^ n - 1) := by
    simpa using Nat.sub_dvd_pow_sub_pow g 1 n
  set e := (g ^ n - 1) / (g - 1) with he
  have hπE : (π ^ e) ^ (normV w - 1) = (g : Ω) := by
    rw [hvN, ← pow_mul, he, Nat.div_mul_cancel hdvd, hπ]
  have h1 := hTR E Ω g A w h hgv hgv2 a ha (π ^ e) hπE s y hy
  have h2 := hTR E' Ω g A w' h' hgw hgw2 a' ha' π (by rw [hwN]; exact hπ) t' x hx
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by have := Nat.one_lt_pow hn.ne' hg1; omega)] at hπ
    exact (Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero) hπ.symm
  have e1 : (s : G E Ω) (π ^ e) / π ^ e = ((t' : G E' Ω) π / π) ^ e := by
    rw [map_pow, htt, div_pow]
  rw [e1] at h1
  have hr1 : A.valuation ((t' : G E' Ω) π / π) ≤ 1 := by
    have hd : ((t' : G E' Ω) : G E' Ω) ∈ Dec (F := E') A := Ine_le_Dec A t'.2
    exact (val_ratio hd hπ0).le
  have hx1 : A.valuation (algebraMap E' Ω (x : E')) ≤ 1 := by
    rw [A.valuation_le_one_iff]
    have h3 : IsIntegral ℤ (algebraMap E' Ω (x : E')) := x.2.map (algebraMap E' Ω).toIntAlgHom
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 (h3.tower_top (A := A))
    exact hz ▸ z.2
  have h3 := cong_pow hr1 hx1 h2 e
  have e2 : algebraMap E Ω (y : E) - algebraMap E' Ω (x : E') ^ e =
      (((t' : G E' Ω) π / π) ^ e - algebraMap E' Ω (x : E') ^ e) - (((t' : G E' Ω) π / π) ^ e - algebraMap E Ω (y : E)) := by
    ring
  rw [e2]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h3 h1)

theorem resBase : ResBase := by
  intro E Ω _ _ _ _ _ A w h a ha g _ i hi n hn D R hR t
  classical
  have hg1 : 1 < g := (Fact.out : g.Prime).one_lt
  have hq : normV w = g := normV_eq_of_padic w g i hi
  have hgw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal := natCast_mem_of_normV w g 1 one_pos (by rw [hq, pow_one])
  have hgw2 : ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 := g_not_mem_sq w g i hi
  have hgw' : ((g : ℕ) : 𝓞 D.E') ∈ D.w'.asIdeal := natCast_mem_of_normV D.w' g n hn D.card
  obtain ⟨t'0, ht'0, hres⟩ := ine_lift g A w h D.w' D.h' n hn D.unr D.card (t : G E Ω) t.2
  let t' : Ine (F := D.E') A := ⟨t'0, ht'0⟩
  have htt : ∀ z : Ω, (t : G E Ω) z = (t' : G D.E' Ω) z := fun z => by
    show (t : G E Ω) z = t'0 z
    rw [← hres]; rfl
  obtain ⟨x', hx'⟩ := exists_int_approx_compl D.w' _ (val_artin_ine D.ha' t').le
  have hx0 : D.red x' ≠ 0 := red_ne_zero_of_approx D.ha' D.ker hx'
  have hRt : R t = Units.mk0 (D.red x') hx0 := hR t t' x' _ hres.symm rfl hx'

  have hva : Valued.v ((a (ineIncl h t) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := val_artin_ine ha t
  obtain ⟨xq, hixq⟩ : ∃ xq, i xq = ((a (ineIncl h t) : (w.adicCompletion E)ˣ) : w.adicCompletion E) :=
    ⟨_, RingEquiv.apply_symm_apply i _⟩
  have hnorm1 : ‖xq‖ = 1 := by
    have h1 : ‖i xq‖ ≤ 1 := by rw [hixq, Valued.toNormedField.norm_le_one_iff, hva]
    have h2 : ¬ ‖i xq‖ < 1 := by rw [hixq, Valued.toNormedField.norm_lt_one_iff, hva]; exact lt_irrefl _
    rw [DiscreteGroups.sglob.DzIso.norm_le_iff i hi] at h1
    rw [DiscreteGroups.sglob.DzIso.norm_lt_iff i hi] at h2
    exact le_antisymm h1 (not_lt.mp h2)
  have huqv : (((PadicInt.mkUnits hnorm1 : ℤ_[g]ˣ) : ℤ_[g]) : ℚ_[g]) = xq := PadicInt.mkUnits_eq hnorm1
  refine ⟨PadicInt.mkUnits hnorm1, by rw [huqv, hixq], ?_⟩
  generalize (PadicInt.mkUnits hnorm1 : ℤ_[g]ˣ) = uq at huqv

  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℕ, (a₀ : ZMod g) = PadicInt.toZMod (uq : ℤ_[g]) := ⟨_, ZMod.natCast_zmod_val _⟩
  have happ : Valued.v (((a (ineIncl h t)) : w.adicCompletion E) -
      algebraMap E (w.adicCompletion E) (((a₀ : 𝓞 E)) : E)) < 1 := by
    have hmem : (uq : ℤ_[g]) - (a₀ : ℤ_[g]) ∈ IsLocalRing.maximalIdeal ℤ_[g] := by
      rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_natCast, ha₀, sub_self]
    have h5 : ‖xq - (a₀ : ℚ_[g])‖ < 1 := by
      have h := (PadicInt.mem_nonunits).mp hmem
      rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast, huqv] at h
      exact h
    have h6 := val_lt_one_of_norm_lt_one w g i hi _ h5
    rw [map_sub, hixq, map_natCast] at h6
    rw [show algebraMap E (w.adicCompletion E) (((a₀ : 𝓞 E)) : E) = (a₀ : w.adicCompletion E) by simp]
    exact h6

  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hpos : 0 < g ^ n - 1 := by have := Nat.one_lt_pow hn.ne' hg1; omega
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (g : Ω) hpos
  have hb := base_cong g n hn A w h D.w' D.h' hgw hgw2 hgw' D.unr hq D.card a ha D.a' D.ha' π hπ t t' htt
    (a₀ : 𝓞 E) happ x' hx'
  set e := (g ^ n - 1) / (g - 1) with he
  have hmem' : ((a₀ : 𝓞 D.E') - x' ^ e) ∈ D.w'.asIdeal := by
    rw [← D.h']
    have e1 : algebraMap D.E' Ω ((((a₀ : 𝓞 D.E') - x' ^ e : 𝓞 D.E')) : D.E') =
        algebraMap E Ω (((a₀ : 𝓞 E)) : E) - algebraMap D.E' Ω (x' : D.E') ^ e := by
      rw [show ((((a₀ : 𝓞 D.E') - x' ^ e : 𝓞 D.E')) : D.E') = (a₀ : D.E') - (x' : D.E') ^ e by push_cast; ring,
        map_sub, map_pow, map_natCast, show (((a₀ : 𝓞 E)) : E) = (a₀ : E) by push_cast; rfl, map_natCast]
    rw [e1]; exact hb
  have hred : ((a₀ : D.K)) = D.red x' ^ e := by
    have h7 : D.red ((a₀ : 𝓞 D.E') - x' ^ e) = 0 := by rw [← RingHom.mem_ker, D.ker]; exact hmem'
    rw [map_sub, map_pow, map_natCast, sub_eq_zero] at h7
    exact h7
  have hprod : ∏ j ∈ Finset.range n, ((R t ^ g ^ j : D.Kˣ) : D.K) = D.red x' ^ e := by
    rw [hRt]
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [Finset.prod_pow_eq_pow_sum, he, Nat.geomSum_eq (Fact.out : g.Prime).two_le]
  rw [hprod, ← hred, ← ha₀, map_natCast]

end UpperTheory.Zero.LLC

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ResIndep
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Polynomial

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

section Res

variable {Ω : Type} [Field Ω]

private def toRes (A : ValuationSubring Ω) (F : Type) [Field F] [NumberField F] [Algebra F Ω] :
    𝓞 F →+* IsLocalRing.ResidueField A :=
  (IsLocalRing.residue A).comp
    { toFun := fun x => ⟨algebraMap F Ω (x : F), ReciprocityTheory.Gal.mem_of_isIntegral_int A (x.2.map (algebraMap F Ω).toIntAlgHom)⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }

private theorem toRes_eq_zero_iff (A : ValuationSubring Ω) {F : Type} [Field F] [NumberField F] [Algebra F Ω] (x : 𝓞 F) :
    toRes A F x = 0 ↔ A.valuation (algebraMap F Ω (x : F)) < 1 := by
  unfold toRes
  rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
  exact A.valuation_lt_one_iff _

private theorem toRes_eq_of_val {A : ValuationSubring Ω} {F F' : Type} [Field F] [NumberField F] [Algebra F Ω]
    [Field F'] [NumberField F'] [Algebra F' Ω] (x : 𝓞 F) (y : 𝓞 F')
    (hxy : A.valuation (algebraMap F Ω (x : F) - algebraMap F' Ω (y : F')) < 1) : toRes A F x = toRes A F' y := by
  unfold toRes
  rw [RingHom.comp_apply, RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact (A.valuation_lt_one_iff _).2 hxy

private theorem exists_emb {A : ValuationSubring Ω} {F : Type} [Field F] [NumberField F] [Algebra F Ω]
    {v : HeightOneSpectrum (𝓞 F)} (hv : IsPlaceOver A v) {K : Type} [Field K] (red : 𝓞 F →+* K)
    (hs : Function.Surjective red) (hk : RingHom.ker red = v.asIdeal) :
    ∃ ι : K →+* IsLocalRing.ResidueField A, ∀ x, ι (red x) = toRes A F x := by
  refine ⟨RingHom.liftOfSurjective red hs ⟨toRes A F, fun x hx => ?_⟩, fun x => ?_⟩
  · rw [hk] at hx
    rw [RingHom.mem_ker, toRes_eq_zero_iff]
    exact (hv x).2 hx
  · exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

private theorem card_K {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {K : Type} [Field K]
    (red : 𝓞 F →+* K) (hs : Function.Surjective red) (hk : RingHom.ker red = v.asIdeal) :
    Nat.card K = normV v := by
  have e := (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hs)
  exact (Nat.card_congr e.toEquiv).symm

open Classical in
private theorem range_sub {κ K : Type} [Field κ] [Field K] (ι : K →+* κ) (q : ℕ) (hq : 1 < q) (hc : Nat.card K = q) :
    (ι.range : Set κ) = ((X ^ q - X : κ[X]).roots.toFinset : Set κ) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite K
  have hne : (X ^ q - X : κ[X]) ≠ 0 := Polynomial.X_pow_sub_X_ne_zero hq
  have hsub : (ι.range : Set κ) ⊆ ((X ^ q - X : κ[X]).roots.toFinset : Set κ) := by
    rintro _ ⟨y, rfl⟩
    simp only [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hne, IsRoot.def, eval_sub, eval_pow, eval_X]
    rw [← map_pow, ← hc, Nat.card_eq_fintype_card, FiniteField.pow_card, sub_self]
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Finset.finite_toSet _)
  have h1 : (ι.range : Set κ).ncard = q := by
    rw [RingHom.coe_range, ← Set.image_univ, Set.ncard_image_of_injective _ ι.injective, Set.ncard_univ, hc]
  rw [h1, Set.ncard_coe_finset]
  refine (Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)
  rw [Polynomial.natDegree_X_pow_sub_X (R := κ) hq]

private theorem exists_equiv {κ K K' : Type} [Field κ] [Field K] [Field K'] (ι : K →+* κ) (ι' : K' →+* κ) (q : ℕ) (hq : 1 < q)
    (hc : Nat.card K = q) (hc' : Nat.card K' = q) : ∃ e : K ≃+* K', ∀ y, ι' (e y) = ι y := by
  have hr : ι.range = ι'.range := by
    apply SetLike.coe_injective
    rw [range_sub ι q hq hc, range_sub ι' q hq hc']
  let e1 : K ≃+* ι.range := RingEquiv.ofBijective ι.rangeRestrict ⟨ι.rangeRestrict.injective, ι.rangeRestrict_surjective⟩
  let e2 : K' ≃+* ι'.range := RingEquiv.ofBijective ι'.rangeRestrict ⟨ι'.rangeRestrict.injective, ι'.rangeRestrict_surjective⟩
  refine ⟨(e1.trans (RingEquiv.subringCongr hr)).trans e2.symm, fun y => ?_⟩
  have h2 : ∀ z : ι'.range, ι' (e2.symm z) = z := fun z => by
    have : (e2 (e2.symm z) : κ) = z := by rw [RingEquiv.apply_symm_apply]
    exact this
  exact h2 (RingEquiv.subringCongr hr (e1 y))

end Res

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem res_read {g n : ℕ} [Fact g.Prime] (hn : 0 < n) (D : Ext h g n) (R : Ine (F := E) A →* D.Kˣ) (hR : D.Res R)
    (t : Ine (F := E) A) : ∃ (t' : Ine (F := D.E') A) (x : 𝓞 D.E'),
      (∀ z : Ω, (t : G E Ω) z = (t' : G D.E' Ω) z) ∧
      Valued.v ((D.a' (ineIncl D.h' t') : D.w'.adicCompletion D.E') - algebraMap D.E' (D.w'.adicCompletion D.E') (x : D.E')) < 1 ∧
      ((R t : D.Kˣ) : D.K) = D.red x := by
  obtain ⟨t', ht', e⟩ := DiscreteGroups.sglob.DzType.ine_lift g A w h D.w' D.h' n hn D.unr D.card (t : G E Ω) t.2
  obtain ⟨x, hx⟩ := DiscreteGroups.sglob.DzType.exists_int_approx_compl D.w' _ (DiscreteGroups.sglob.DzType.val_artin_ine D.ha' ⟨t', ht'⟩).le
  have hne := DiscreteGroups.sglob.DzType.red_ne_zero_of_approx D.ha' D.ker hx
  refine ⟨⟨t', ht'⟩, x, fun z => by rw [← e]; rfl, hx, ?_⟩
  have := hR t ⟨t', ht'⟩ x (Units.mk0 _ hne) e.symm rfl hx
  rw [this]; rfl

private theorem core {g n : ℕ} [Fact g.Prime] (hn : 0 < n) (D D' : Ext h g n)
    (R : Ine (F := E) A →* D.Kˣ) (R' : Ine (F := E) A →* D'.Kˣ) (hR : D.Res R) (hR' : D'.Res R')
    (hm : ∀ (t : Ine (F := D.E') A) (t' : Ine (F := D'.E') A), (∀ z : Ω, (t : G D.E' Ω) z = (t' : G D'.E' Ω) z) →
      ∀ (x : 𝓞 D.E') (y : 𝓞 D'.E'),
      Valued.v ((D.a' (ineIncl D.h' t) : D.w'.adicCompletion D.E') - algebraMap D.E' (D.w'.adicCompletion D.E') (x : D.E')) < 1 →
      Valued.v ((D'.a' (ineIncl D'.h' t') : D'.w'.adicCompletion D'.E') - algebraMap D'.E' (D'.w'.adicCompletion D'.E') (y : D'.E')) < 1 →
      A.valuation (algebraMap D.E' Ω (x : D.E') - algebraMap D'.E' Ω (y : D'.E')) < 1) :
    ∃ e : D.K ≃+* D'.K, ∀ t, ((R' t : D'.Kˣ) : D'.K) = e (R t : D.Kˣ) := by
  obtain ⟨ι, hι⟩ := exists_emb D.h' D.red D.surj D.ker
  obtain ⟨ι', hι'⟩ := exists_emb D'.h' D'.red D'.surj D'.ker
  have hq : 1 < g ^ n := Nat.one_lt_pow hn.ne' (Fact.out : g.Prime).one_lt
  obtain ⟨e, he⟩ := exists_equiv ι ι' (g ^ n) hq ((card_K D.red D.surj D.ker).trans D.card)
    ((card_K D'.red D'.surj D'.ker).trans D'.card)
  refine ⟨e, fun t => ι'.injective ?_⟩
  obtain ⟨t1, x, h1, a1, r1⟩ := res_read hn D R hR t
  obtain ⟨t2, y, h2, a2, r2⟩ := res_read hn D' R' hR' t
  rw [he, r1, r2, hι, hι']
  exact (toRes_eq_of_val x y (hm t1 t2 (fun z => by rw [← h1, h2]) x y a1 a2)).symm

theorem resIndep : ResIndep := by
  intro E Ω _ _ _ _ _ A w h g _ i hi n hn D D' R R' hR hR'
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hq : 1 < g ^ n := Nat.one_lt_pow hn.ne' (Fact.out : g.Prime).one_lt
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (g : Ω) (show 0 < g ^ n - 1 by omega)
  refine core hn D D' R R' hR hR' fun t t' htt x y hx hy => ?_
  have hg := DiscreteGroups.sglob.DzType.natCast_mem_of_normV D.w' g n hn D.card
  have hg' := DiscreteGroups.sglob.DzType.natCast_mem_of_normV D'.w' g n hn D'.card
  have h1 := tameRecAll D.E' Ω g A D.w' D.h' hg D.unr D.a' D.ha' π (by rw [D.card]; exact hπ) t x hx
  have h2 := tameRecAll D'.E' Ω g A D'.w' D'.h' hg' D'.unr D'.a' D'.ha' π (by rw [D'.card]; exact hπ) t' y hy
  rw [← htt] at h2
  have e : algebraMap D.E' Ω (x : D.E') - algebraMap D'.E' Ω (y : D'.E') =
      ((t : G D.E' Ω) π / π - algebraMap D'.E' Ω (y : D'.E')) - ((t : G D.E' Ω) π / π - algebraMap D.E' Ω (x : D.E')) := by ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h2 h1)

end UpperTheory.Zero.LLC

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TypeIff
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped Pointwise

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

private theorem restrict_mem_ine {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω]
    [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω]
    (A : ValuationSubring Ω) (t : G E' Ω) (ht : t ∈ Ine (F := E') A) :
    AlgEquiv.restrictScalars E t ∈ Ine (F := E) A := by
  refine ⟨?_, fun x hx => ht.2 x hx⟩
  show AlgEquiv.restrictScalars E t • A = A
  have hd : t • A = A := ht.1
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  conv_rhs => rw [← hd]
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact Iff.rfl

end UpperTheory.Zero.LLC

theorem UpperTheory.Zero.LLC.typeIff :
    UpperTheory.Zero.LLC.TypeIff := by
  intro E Ω _ _ _ _ _ A w h rc
  constructor
  · intro H x g _ i hi n hn D R hR θ hθ τ hτ hNm σ hσ hinf
    subst hσ
    have main := H D.E' g D.w' D.h' i hi n hn D.unr D.card D.a' D.ha' D.K D.red D.surj D.ker θ hθ τ hτ hNm σ hinf
    refine ⟨main.1, fun t => ?_⟩
    obtain ⟨t', ht', e⟩ := DiscreteGroups.sglob.DzType.ine_lift g A w h D.w' D.h' n hn D.unr D.card (t : G E Ω) t.2
    obtain ⟨x, hx⟩ := DiscreteGroups.sglob.DzType.exists_int_approx_compl D.w' _
      (DiscreteGroups.sglob.DzType.val_artin_ine D.ha' (⟨t', ht'⟩ : Ine (F := D.E') A)).le
    have hne := DiscreteGroups.sglob.DzType.red_ne_zero_of_approx D.ha' D.ker hx
    have hz : R t = Units.mk0 (D.red x) hne := hR t ⟨t', ht'⟩ x _ e.symm rfl hx
    have key := main.2 ⟨t', ht'⟩ x (Units.mk0 _ hne) rfl hx
    rw [hz, ← e]
    exact key
  · intro H E' _ _ _ _ _ _ g _ w' h' i hi n hn unr card a' ha' K _ _ red surj ker θ hθ τ hτ hNm σ hinf
    let D : Ext h g n :=
      { E' := E', w' := w', h' := h', unr := unr, card := card, a' := a', ha' := ha', K := K, red := red,
        surj := surj, ker := ker }
    obtain ⟨R, hR⟩ := (UpperTheory.Zero.LLC.resEx E Ω A w h g i hi n hn D).1
    have main := H (cls σ) g i hi n hn D R hR θ hθ τ hτ hNm σ rfl hinf
    refine ⟨main.1, fun t x z hz hx => ?_⟩
    have hm := restrict_mem_ine (E := E) A (t : G E' Ω) t.2
    have e : R ⟨_, hm⟩ = z := hR ⟨_, hm⟩ t x z rfl hz hx
    have key := main.2 ⟨_, hm⟩
    rw [e] at key
    exact key

end
end

