module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.MemRangeOfForallHeightOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2052
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2053
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallHeightOneExistsDvdMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem dvd_of_forall_height_one_exists_dvd_mul {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] {h z : A} (hh : h ≠ 0)
    (H : ∀ P : Ideal A, P.IsPrime → P.height = 1 → ∃ s ∉ P, h ∣ s * z) : h ∣ z := by
  let K := FractionRing A
  have hhK : algebraMap A K h ≠ 0 := fun h0 =>
    hh (IsFractionRing.injective A K (by rw [h0, map_zero]))
  have hmem : algebraMap A K z / algebraMap A K h ∈ (algebraMap A K).range := by
    refine ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.mem_range_of_forall_height_one (A := A) _ ?_
    intro P hP h1
    obtain ⟨s, hs, t, ht⟩ := H P hP h1
    refine ⟨s, hs, t, ?_⟩
    rw [← mul_div_assoc, eq_div_iff hhK, ← map_mul, ← map_mul, ht, mul_comm]
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, IsFractionRing.injective A K ?_⟩
  rw [map_mul, hc, mul_div_assoc', eq_div_iff hhK, mul_comm]

section SquareIdeal

variable {A : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]

theorem dvd_mul_of_dvd_sq_of_dvd_sq {h x y : A} (hx : h ∣ x ^ 2) (hy : h ∣ y ^ 2) : h ∣ x * y := by
  have : h ^ 2 ∣ (x * y) ^ 2 := by
    rw [mul_pow, sq h]; exact mul_dvd_mul hx hy
  exact (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 this

def sqDvdIdeal (h : A) : Ideal A where
  carrier := {x | h ∣ x ^ 2}
  add_mem' := by
    intro x y hx hy
    have hxy := dvd_mul_of_dvd_sq_of_dvd_sq hx hy
    show h ∣ (x + y) ^ 2
    have e : (x + y) ^ 2 = x ^ 2 + 2 * (x * y) + y ^ 2 := by ring
    rw [e]
    exact dvd_add (dvd_add hx (dvd_mul_of_dvd_right hxy _)) hy
  zero_mem' := by show h ∣ (0 : A) ^ 2; simp
  smul_mem' := by
    intro c x hx
    show h ∣ (c * x) ^ 2
    rw [mul_pow]; exact dvd_mul_of_dvd_right hx _

theorem mem_sqDvdIdeal {h x : A} : x ∈ sqDvdIdeal h ↔ h ∣ x ^ 2 := Iff.rfl

end SquareIdeal

theorem isUnit_mul_sq_of_faithfullyFlat : ∀ (C C' : Type) [CommRing C] [IsDomain C] [IsLocalRing C] [IsNoetherianRing C] [IsIntegrallyClosed C] [CommRing C'] [IsDomain C'] [IsNoetherianRing C'] [IsIntegrallyClosed C'] [Algebra C C'] [Module.FaithfullyFlat C C'] (h : C), h ≠ 0 → (∃ (u : C'ˣ) (f : C'), algebraMap C C' h = u * f ^ 2) → (∀ p : Ideal C, p.IsPrime → p.height = 1 → ∃ a b c : C, b ∉ p ∧ c ∉ p ∧ b * h = c * a ^ 2) → ∃ (u : Cˣ) (a : C), h = u * a ^ 2 := by
  intro C C' _ _ _ _ _ _ _ _ _ _ _ h hh hsq Hp
  obtain ⟨u, f, hf⟩ := hsq
  have hflat : (algebraMap C C').Flat := RingHom.flat_algebraMap_iff.2 inferInstance
  let J := sqDvdIdeal h

  have hJf : J.map (algebraMap C C') ≤ Ideal.span {f} := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    obtain ⟨z, hz⟩ := mem_sqDvdIdeal.1 hx
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    apply (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1
    refine ⟨(u : C') * algebraMap C C' z, ?_⟩
    rw [← map_pow, hz, map_mul, hf]; ring

  have hcol : (Ideal.span {h}).colon (J : Set C) ≤ J := by
    intro y hy
    rw [Submodule.mem_colon] at hy
    apply mem_sqDvdIdeal.2
    apply dvd_of_forall_height_one_exists_dvd_mul hh
    intro P hP h1
    obtain ⟨a, b, c, hb, hc, habc⟩ := Hp P hP h1
    have hac : a * c ∈ J := mem_sqDvdIdeal.2 ⟨b * c, by linear_combination (-c) * habc⟩
    have hy' := hy (a * c) hac
    rw [smul_eq_mul, Ideal.mem_span_singleton] at hy'
    obtain ⟨t, ht⟩ := hy'
    refine ⟨b * c, fun hm => (hP.mem_or_mem hm).elim hb hc, t ^ 2, ?_⟩
    have e : h * (b * c * y ^ 2) = h * (h * t ^ 2) := by
      linear_combination (c * y ^ 2) * habc + (y * (a * c) + h * t) * ht
    exact mul_left_cancel₀ hh e

  have hfJ : f ∈ J.map (algebraMap C C') := by
    have hm : f ∈ ((Ideal.span {h}).colon (J : Set C)).map (algebraMap C C') := by
      rw [GlobalTheory.ideal_map_colon_eq_of_flat _ hflat, Ideal.map_span, Set.image_singleton,
        Submodule.mem_colon]
      intro p hp
      obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton.1 (hJf hp)
      rw [smul_eq_mul, Ideal.mem_span_singleton, hf]
      exact ⟨((u⁻¹ : C'ˣ) : C') * w, by linear_combination (-(f ^ 2 * w)) * u.mul_inv⟩
    exact Ideal.map_mono hcol hm
  have hJeq : J.map (algebraMap C C') = Ideal.span {f} :=
    le_antisymm hJf ((Ideal.span_singleton_le_iff_mem _).2 hfJ)

  have hY : ((J * J).colon (Ideal.span {h} : Set C)).map (algebraMap C C') = ⊤ := by
    rw [GlobalTheory.ideal_map_colon_eq_of_flat _ hflat, Ideal.map_mul, hJeq, Ideal.map_span,
      Set.image_singleton, Ideal.span_singleton_mul_span_singleton, Ideal.eq_top_iff_one,
      Submodule.mem_colon]
    intro p hp
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton.1 hp
    rw [smul_eq_mul, _root_.one_mul, Ideal.mem_span_singleton, hf]
    exact ⟨(u : C') * w, by ring⟩
  have hhJJ : h ∈ J * J := by
    have e := Ideal.comap_map_eq_self_of_faithfullyFlat (B := C')
      ((J * J).colon (Ideal.span {h} : Set C))
    rw [hY, Ideal.comap_top] at e
    have h1 : (1 : C) ∈ (J * J).colon (Ideal.span {h} : Set C) := e ▸ Submodule.mem_top
    rw [Submodule.mem_colon] at h1
    simpa using h1 h (Ideal.mem_span_singleton_self h)

  by_contra hne
  have hle : J * J ≤ Ideal.span {h} * maximalIdeal C := by
    refine Ideal.mul_le.2 fun x hx y hy => ?_
    obtain ⟨e, he⟩ := dvd_mul_of_dvd_sq_of_dvd_sq (mem_sqDvdIdeal.1 hx) (mem_sqDvdIdeal.1 hy)
    by_cases hem : e ∈ maximalIdeal C
    · rw [he]; exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self h) hem
    · exfalso
      have heu : IsUnit e := by
        rw [mem_maximalIdeal, mem_nonunits_iff, not_not] at hem; exact hem
      obtain ⟨a, ha⟩ := mem_sqDvdIdeal.1 hx
      obtain ⟨b, hb⟩ := mem_sqDvdIdeal.1 hy
      have hab : a * b = e ^ 2 := by
        have e2 : h ^ 2 * (a * b) = h ^ 2 * e ^ 2 := by
          linear_combination (-(h * b)) * ha - x ^ 2 * hb + (x * y + h * e) * he
        exact mul_left_cancel₀ (pow_ne_zero 2 hh) e2
      have hau : IsUnit a := isUnit_of_mul_isUnit_left (hab ▸ heu.pow 2)
      exact hne ⟨hau.unit⁻¹, x, by rw [ha]; linear_combination (-h) * hau.val_inv_mul⟩
  obtain ⟨z, hz, hz'⟩ := Ideal.mem_span_singleton_mul.1 (hle hhJJ)
  have hz1 : z = 1 := mul_left_cancel₀ hh (by rw [hz', _root_.mul_one])
  exact (maximalIdeal.isMaximal C).ne_top ((Ideal.eq_top_iff_one _).2 (hz1 ▸ hz))

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffectiveCartierIdealSheafLeOfClosedPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.effectiveCartier_idealSheaf_le_of_closedPoints : ∀ (X : Scheme.{0}) [CompactSpace X] (D : EffCartierData X) (K : X.IdealSheafData), (∀ x : X, IsClosed ({x} : Set X) → ∃ (W : X.affineOpens) (i : D.ι) (h : W.1 ≤ D.U i), x ∈ W.1 ∧ resG X h (D.f i) ∈ K.ideal W) → D.idealSheaf ≤ K := by
  intro X _ D K hK
  have hc : ∀ y : X, ∃ x : X, IsClosed ({x} : Set X) ∧ y ⤳ x := fun y => by
    obtain ⟨x, hx, hxc⟩ := (isClosed_closure (s := ({y} : Set X))).exists_closed_singleton
      ⟨y, subset_closure rfl⟩
    exact ⟨x, hxc, specializes_iff_mem_closure.2 hx⟩
  choose x hxc hyx using hc
  choose W i h hxW hmem using fun y => hK (x y) (hxc y)
  refine Scheme.IdealSheafData.le_of_iSup_eq_top W
    (eq_top_iff.2 fun y _ =>
      TopologicalSpace.Opens.mem_iSup.2 ⟨y, (hyx y).mem_open (W y).1.isOpen (hxW y)⟩)
    fun y => ?_
  rw [D.ideal_idealSheaf (W y) (i y) (h y), Ideal.span_singleton_le_iff_mem]
  exact hmem y
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffectiveCartierLocalEquation
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.IdealDiv

theorem unitAt_div_of_ideal_eq {Y : Scheme.{0}} [IsIntegral Y] (J : Y.IdealSheafData) {y : Y}
    {U V : Y.affineOpens} {f : Γ(Y, U.1)} {f' : Γ(Y, V.1)} (hU : y ∈ U.1) (hV : y ∈ V.1)
    (hf : J.ideal U = Ideal.span {f}) (hf' : J.ideal V = Ideal.span {f'})
    (h0 : fnOf U.1 (gen_mem hU) f ≠ 0) :
    UnitAt y (fnOf V.1 (gen_mem hV) f' / fnOf U.1 (gen_mem hU) f) := by
  obtain ⟨h, hhW, hxh⟩ := U.2.exists_basicOpen_le (V := U.1 ⊓ V.1) ⟨_, ⟨hU, hV⟩⟩ hU
  let Wa : Y.affineOpens := ⟨Y.basicOpen h, U.2.basicOpen h⟩
  have hWU : Wa.1 ≤ U.1 := hhW.trans inf_le_left
  have hWV : Wa.1 ≤ V.1 := hhW.trans inf_le_right
  haveI : Nonempty Wa.1 := ⟨⟨_, hxh⟩⟩
  have e1 : J.ideal Wa = Ideal.span {resG Y hWU f} := by
    rw [← Scheme.IdealSheafData.map_ideal _ (U := Wa) (V := U) hWU, hf, Ideal.map_span, Set.image_singleton]
    rfl
  have e2 : J.ideal Wa = Ideal.span {resG Y hWV f'} := by
    rw [← Scheme.IdealSheafData.map_ideal _ (U := Wa) (V := V) hWV, hf', Ideal.map_span, Set.image_singleton]
    rfl
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 (e1.symm.trans e2)
  have hg := gen_mem (U := Wa.1) hxh
  have e := congrArg (fnOf Wa.1 hg) hu
  rw [map_mul, fnOf_resG, fnOf_resG] at e
  rw [← e, mul_div_cancel_left₀ _ h0]
  exact unitAt_fnOf hxh hg u

theorem exists_cartierDiv_of_effCartier : ∀ (Y : Scheme.{0}) [IsIntegral Y] (J : Y.IdealSheafData),
    FinalTheorems.EffCartier J → ∃ E : CartierDiv Y, E.Eff ∧ E.supp = J.support ∧
      ∀ (y : Y) (U : Y.affineOpens) (f : Γ(Y, U.1)) (hy : y ∈ U.1) (hf : fnOf U.1 (gen_mem hy) f ≠ 0),
        J.ideal U = Ideal.span {f} → E.IsEqn y (Units.mk0 _ hf) := by
  intro Y _ J hJ
  choose U f hyU hnzd hid using hJ
  have hne : ∀ y, fnOf (U y).1 (gen_mem (hyU y)) (f y) ≠ 0 := by
    intro y h
    haveI : Nonempty (U y).1 := ⟨⟨y, hyU y⟩⟩
    have h0 : f y = 0 := fnOf_injective _ _ (h.trans (map_zero _).symm)
    exact nonZeroDivisors.ne_zero (hnzd y) h0
  let v : ∀ y : Y, Y.functionFieldˣ := fun y => Units.mk0 _ (hne y)
  let E : CartierDiv Y := show cartierGroup Y from ⟨fun y => germOf y (v y), fun x =>
    ⟨(U x).1, hyU x, v x, fun y hy =>
      germOf_eq_iff.2 (unitAt_div_of_ideal_eq J (hyU y) hy (hid y) (hid x) (hne y))⟩⟩
  have hE : ∀ y, E.IsEqn y (v y) := fun y => rfl
  refine ⟨E, fun x => ⟨v x, hE x, by rw [one_mul]; exact regAt_fnOf (hyU x) _ _⟩, ?_, ?_⟩
  · ext x
    rw [SetLike.mem_coe, SetLike.mem_coe, (hE x).mem_supp_iff, Units.val_mk0, unitAt_fnOf_iff (hyU x),
      Scheme.IdealSheafData.mem_support_iff_of_mem (U := U x) (hyU x), hid x, Scheme.zeroLocus_span,
      Scheme.zeroLocus_singleton]
    rfl
  · intro y V g hy hg hV
    exact (hE y).iff_unitAt.2 (unitAt_div_of_ideal_eq J (hyU y) hy (hid y) hV (hne y))

end GlobalTheory.Cartier.IdealDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerIsoDiagonalOfLPowerTorsionAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowerDiagonal

section General

variable {C : Type*} [Category C] [CartesianMonoidalCategory C]

theorem isMonHom_of_points {X Y : C} [MonObj X] [MonObj Y] (f : X ⟶ Y)
    (h1 : ∀ T : C, (1 : T ⟶ X) ≫ f = 1)
    (hm : ∀ (T : C) (x y : T ⟶ X), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f := by
  refine ⟨?_, ?_⟩
  · simpa only [MonObj.one_eq_one] using h1 (𝟙_ C)
  · simpa only [MonObj.mul_eq_mul, MonObj.comp_mul, tensorHom_fst, tensorHom_snd] using
      hm (X ⊗ X) (fst X X) (snd X X)

theorem exists_sections {G H : C} [MonObj G] [MonObj H] {n : Type} [DecidableEq n]
    (p : n → (G ⟶ H)) (hp : ∀ a, IsMonHom (p a))
    (hu : ∀ (T : C) (y : n → (T ⟶ H)), ∃! x : T ⟶ G, ∀ a, x ≫ p a = y a) :
    ∃ j : n → (H ⟶ G), (∀ b, IsMonHom (j b)) ∧ (∀ b, j b ≫ p b = 𝟙 H) ∧
      ∀ b c, c ≠ b → j b ≫ p c = 1 := by
  classical
  have hex := fun b => (hu H (fun c => if c = b then 𝟙 H else 1)).exists
  choose j hj using hex
  have key : ∀ {T : C} (x : T ⟶ H) (b c : n), x ≫ j b ≫ p c = if c = b then x else 1 := by
    intro T x b c
    rw [hj b c]
    split_ifs <;> simp
  have ext : ∀ {T : C} (x y : T ⟶ G), (∀ a, x ≫ p a = y ≫ p a) → x = y := fun {T} x y h =>
    (hu T fun a => y ≫ p a).unique h (fun _ => rfl)
  refine ⟨j, fun b => ?_, fun b => by simpa using key (𝟙 H) b b,
    fun b c hcb => by simpa [hcb] using key (𝟙 H) b c⟩
  apply isMonHom_of_points
  · intro T
    apply ext
    intro a
    haveI := hp a
    rw [Category.assoc, key, MonObj.one_comp]
    split_ifs <;> rfl
  · intro T x y
    apply ext
    intro a
    haveI := hp a
    simp only [Category.assoc, key, MonObj.mul_comp]
    split_ifs <;> simp

theorem hom_ext_sections {G H H' : C} [MonObj G] [MonObj H] [MonObj H']
    {n : Type} [Finite n] [DecidableEq n]
    (p : n → (G ⟶ H)) (hp : ∀ a, IsMonHom (p a))
    (hu : ∀ (T : C) (y : n → (T ⟶ H)), ∃! x : T ⟶ G, ∀ a, x ≫ p a = y a)
    (j : n → (H ⟶ G)) (h1 : ∀ b, j b ≫ p b = 𝟙 H) (h2 : ∀ b c, c ≠ b → j b ≫ p c = 1)
    (f g : G ⟶ H') [IsMonHom f] [IsMonHom g] (h : ∀ b, j b ≫ f = j b ≫ g) : f = g := by
  classical
  haveI := Fintype.ofFinite n
  have ext : ∀ {T : C} (x y : T ⟶ G), (∀ a, x ≫ p a = y ≫ p a) → x = y := fun {T} x y h =>
    (hu T fun a => y ≫ p a).unique h (fun _ => rfl)
  have hcomp : ∀ {K : C} [MonObj K] (k : G ⟶ K) [IsMonHom k] (l : List n),
      (l.map fun b => p b ≫ j b).prod ≫ k = (l.map fun b => p b ≫ j b ≫ k).prod := by
    intro K _ k _ l
    induction l with
    | nil => simp
    | cons b l ih => simp [MonObj.mul_comp, ih]
  have hlist : ∀ (c : n) (l : List n), l.Nodup →
      (l.map fun b => p b ≫ j b ≫ p c).prod = if c ∈ l then p c else 1 := by
    intro c l hl
    induction l with
    | nil => simp
    | cons b l ih =>
      rw [List.map_cons, List.prod_cons, ih (List.nodup_cons.mp hl).2]
      by_cases hbc : b = c
      · subst hbc
        have hnot : b ∉ l := (List.nodup_cons.mp hl).1
        simp [h1, hnot]
      · simp [h2 b c (Ne.symm hbc), Ne.symm hbc]
  have hs : (Finset.univ.toList.map fun b => p b ≫ j b).prod = 𝟙 G := by
    apply ext
    intro c
    haveI := hp c
    rw [hcomp (p c), hlist c _ (Finset.nodup_toList _)]
    simp
  calc f = (Finset.univ.toList.map fun b => p b ≫ j b).prod ≫ f := by rw [hs, Category.id_comp]
    _ = (Finset.univ.toList.map fun b => p b ≫ j b ≫ f).prod := hcomp f _
    _ = (Finset.univ.toList.map fun b => p b ≫ j b ≫ g).prod := by simp only [h]
    _ = (Finset.univ.toList.map fun b => p b ≫ j b).prod ≫ g := (hcomp g _).symm
    _ = g := by rw [hs, Category.id_comp]

end General

theorem exists_diagonal : ∀ (K : Type) [Field K] [IsAlgClosed K] (G₀ G₁ H₀ H₁ : Over (Sp K)) [GrpObj G₀] [GrpObj G₁] [GrpObj H₀] [GrpObj H₁] [IsCommMonObj H₀] [IsCommMonObj H₁], IsSemiAbelian H₀ → IsSemiAbelian H₁ → ∀ (l : ℕ), l.Prime → (l : K) ≠ 0 → ∀ (p₀ : Fin 8 → (G₀ ⟶ H₀)) (p₁ : Fin 8 → (G₁ ⟶ H₁)), (∀ a, IsMonHom (p₀ a)) → (∀ a, IsMonHom (p₁ a)) → (∀ (T : Over (Sp K)) (y : Fin 8 → (T ⟶ H₀)), ∃! x : T ⟶ G₀, ∀ a, x ≫ p₀ a = y a) → (∀ (T : Over (Sp K)) (y : Fin 8 → (T ⟶ H₁)), ∃! x : T ⟶ G₁, ∀ a, x ≫ p₁ a = y a) → ∀ (F : G₀ ⟶ G₁), IsMonHom F → IsIso F → (∀ (z z' : 𝟙_ (Over (Sp K)) ⟶ G₀), (∃ k : ℕ, z ^ (l ^ k) = 1) → (∃ k : ℕ, z' ^ (l ^ k) = 1) → ∀ a a', z ≫ p₀ a = z' ≫ p₀ a' → z ≫ F ≫ p₁ a = z' ≫ F ≫ p₁ a') → ∃ f₁ : H₀ ⟶ H₁, IsMonHom f₁ ∧ IsIso f₁ ∧ ∀ a, F ≫ p₁ a = p₀ a ≫ f₁ := by
  intro K _ _ G₀ G₁ H₀ H₁ _ _ _ _ _ _ hH₀ hH₁ l hl hlK p₀ p₁ hp₀ hp₁ hu₀ hu₁ F hF hFi htor
  classical
  obtain ⟨j₀, hj₀m, hj₀1, hj₀2⟩ := exists_sections p₀ hp₀ hu₀
  obtain ⟨j₁, hj₁m, hj₁1, hj₁2⟩ := exists_sections p₁ hp₁ hu₁
  haveI := hF
  haveI := hFi
  haveI := fun a => hp₀ a
  haveI := fun a => hp₁ a
  haveI := fun b => hj₀m b
  have hpj : ∀ b a : Fin 8, j₀ b ≫ p₀ a = if a = b then 𝟙 H₀ else 1 := by
    intro b a
    split_ifs with h
    · subst h; exact hj₀1 a
    · exact hj₀2 b a h
  have hpj₁ : ∀ b a : Fin 8, j₁ b ≫ p₁ a = if a = b then 𝟙 H₁ else 1 := by
    intro b a
    split_ifs with h
    · subst h; exact hj₁1 a
    · exact hj₁2 b a h

  have htors : ∀ (b : Fin 8) (y : 𝟙_ (Over (Sp K)) ⟶ H₀) (k : ℕ), y ^ (l ^ k) = 1 →
      ∃ k : ℕ, (y ≫ j₀ b) ^ (l ^ k) = 1 := by
    intro b y k hy
    haveI := hj₀m b
    exact ⟨k, by rw [← MonObj.pow_comp, hy, MonObj.one_comp]⟩

  have hoff : ∀ b a : Fin 8, a ≠ b → j₀ b ≫ F ≫ p₁ a = 1 := by
    intro b a hab
    haveI := hj₀m b
    haveI := hp₁ a
    refine GlobalTheory.TorsionDense.eq_one_of_torsion_comp_eq_one K H₀ H₁ hH₀ hH₁ l hl hlK _ inferInstance
      (fun _ _ y k hy => ?_)
    have := htor (y ≫ j₀ b) 1 (htors b y k hy) ⟨0, _root_.one_pow _⟩ a a
      (by rw [Category.assoc, hpj, if_neg hab, MonObj.comp_one, MonObj.one_comp])
    rw [MonObj.one_comp (F ≫ p₁ a)] at this
    simpa [Category.assoc] using this

  have hdiag : ∀ a : Fin 8, j₀ a ≫ F ≫ p₁ a = j₀ 0 ≫ F ≫ p₁ 0 := by
    intro a
    haveI := hj₀m a
    haveI := hj₀m 0
    haveI := hp₁ a
    haveI := hp₁ 0
    have hpt : ∀ (T : Over (Sp K)) (x : T ⟶ H₀),
        x ≫ ((j₀ a ≫ F ≫ p₁ a) * (j₀ 0 ≫ F ≫ p₁ 0)⁻¹) =
          (x ≫ j₀ a ≫ F ≫ p₁ a) * (x ≫ j₀ 0 ≫ F ≫ p₁ 0)⁻¹ := by
      intro T x
      rw [MonObj.comp_mul, GrpObj.comp_inv]
    have hmon : IsMonHom ((j₀ a ≫ F ≫ p₁ a) * (j₀ 0 ≫ F ≫ p₁ 0)⁻¹) := by
      apply isMonHom_of_points
      · intro T
        rw [hpt, MonObj.one_comp, MonObj.one_comp, _root_.inv_one, _root_.mul_one]
      · intro T x y
        rw [hpt, hpt, hpt, MonObj.mul_comp, MonObj.mul_comp, _root_.mul_inv, _root_.mul_mul_mul_comm]
    have h1 := GlobalTheory.TorsionDense.eq_one_of_torsion_comp_eq_one K H₀ H₁ hH₀ hH₁ l hl hlK _ hmon
      (fun _ _ y k hy => by
        have := htor (y ≫ j₀ a) (y ≫ j₀ 0) (htors a y k hy) (htors 0 y k hy) a 0
          (by rw [Category.assoc, Category.assoc, hpj, hpj, if_pos rfl, if_pos rfl])
        rw [hpt, _root_.mul_inv_eq_one]
        simpa [Category.assoc] using this)
    exact _root_.mul_inv_eq_one.mp h1
  let f₁ : H₀ ⟶ H₁ := j₀ 0 ≫ F ≫ p₁ 0
  haveI : IsMonHom f₁ := by
    haveI := hj₀m 0
    haveI := hp₁ 0
    dsimp [f₁]
    infer_instance
  have hcomm : ∀ a, F ≫ p₁ a = p₀ a ≫ f₁ := by
    intro a
    haveI := hp₁ a
    haveI := hp₀ a
    refine hom_ext_sections p₀ hp₀ hu₀ j₀ hj₀1 hj₀2 _ _ (fun b => ?_)
    rw [← Category.assoc (j₀ b) (p₀ a), hpj]
    split_ifs with hab
    · subst hab
      rw [Category.id_comp, hdiag]
    · rw [hoff b a hab, MonObj.one_comp]
  have hsec : j₀ 0 ≫ F = f₁ ≫ j₁ 0 := by
    refine (hu₁ H₀ fun a => (f₁ ≫ j₁ 0) ≫ p₁ a).unique (fun a => ?_) (fun _ => rfl)
    rw [Category.assoc, hcomm, ← Category.assoc, hpj, Category.assoc, hpj₁]
    split_ifs
    · simp
    · rw [MonObj.one_comp, MonObj.comp_one]
  refine ⟨f₁, inferInstance, ⟨⟨j₁ 0 ≫ inv F ≫ p₀ 0, ?_, ?_⟩⟩, hcomm⟩
  · rw [← Category.assoc, ← hsec, Category.assoc, IsIso.hom_inv_id_assoc, hj₀1]
  · rw [Category.assoc, Category.assoc, ← hcomm, IsIso.inv_hom_id_assoc, hj₁1]

end GlobalTheory.PowerDiagonal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFormallyUnramifiedOfEqAtClosedPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TorsSpec

theorem eq_of_unramified_of_closedPoint : ∀ {S T : Scheme.{0}} (f : T ⟶ S) [FormallyUnramified f]
    [LocallyOfFiniteType f] (R : CommRingCat.{0}) [IsLocalRing R] (u₁ u₂ : Spec R ⟶ T) (h : u₁ ≫ f = u₂ ≫ f)
    (K : Type) [Field K] (k : Sp K ⟶ Spec R) (hk : ∀ x, k x = IsLocalRing.closedPoint R)
    (hku : k ≫ u₁ = k ≫ u₂), u₁ = u₂ := by
  intro S T f _ _ R _ u₁ u₂ h K _ k hk hku
  let g : Spec R ⟶ pullback f f := pullback.lift u₁ u₂ h
  have hkg : k ≫ g = (k ≫ u₁) ≫ pullback.diagonal f := by
    apply pullback.hom_ext
    · simp [g, pullback.lift_fst]
    · simp [g, hku, pullback.lift_snd]
  obtain ⟨x⟩ : Nonempty (Sp K) := (inferInstance : Nonempty (PrimeSpectrum K))
  have hc : g (IsLocalRing.closedPoint R) ∈ Set.range (pullback.diagonal f) := by
    refine ⟨(k ≫ u₁) x, ?_⟩
    rw [← hk x, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hkg]
  have hopen : IsOpen (Set.range (pullback.diagonal f)) :=
    (pullback.diagonal f).isOpenEmbedding.isOpen_range
  have hr : Set.range g ⊆ Set.range (pullback.diagonal f) := by
    rintro _ ⟨y, rfl⟩
    have hs : y ⤳ IsLocalRing.closedPoint R := IsLocalRing.specializes_closedPoint y
    exact (hs.map g.continuous).mem_open hopen hc
  have hl := IsOpenImmersion.lift_fac (pullback.diagonal f) g hr
  have h1 : u₁ = IsOpenImmersion.lift (pullback.diagonal f) g hr := by
    have e : (IsOpenImmersion.lift (pullback.diagonal f) g hr ≫ pullback.diagonal f) ≫ pullback.fst f f
        = g ≫ pullback.fst f f := by rw [hl]
    rw [Category.assoc, pullback.diagonal_fst, Category.comp_id, pullback.lift_fst] at e
    exact e.symm
  have h2 : u₂ = IsOpenImmersion.lift (pullback.diagonal f) g hr := by
    have e : (IsOpenImmersion.lift (pullback.diagonal f) g hr ≫ pullback.diagonal f) ≫ pullback.snd f f
        = g ≫ pullback.snd f f := by rw [hl]
    rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, pullback.lift_snd] at e
    exact e.symm
  exact h1.trans h2.symm

end GlobalTheory.TorsSpec
end

