module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.TaylorComp

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigDirInt
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD

open MvPolynomial CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Formalism.L2.Pj
  ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj.SaturatedCharts NumberField

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

set_option maxHeartbeats 1000000 in
open ReciprocityTheory.ChartRestriction.G.Chart (tcoord tan_ext prodPts prodPts_tan) in
theorem eigDir_int (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y)
    (ℓ : Lt1 Dw) (a : 𝓞 E) (z : T.V) (hz : algebraMap T.V T.Fr z = io (embK c ℓ.1 a)) :
    (Matrix.of fun m j => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (C.actT a m)).mulVec (C.uvecT ℓ) =
      z • C.uvecT ℓ := by
  have hsm : Smooth C.I.G.G.hom := C.I.G.semi.smooth
  have hb := C.I.G.act.hom a
  obtain ⟨n, x, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc (R := T.V) C.I.G.G

  let D : Fin (chD C.ch) → (Sp (DualNumber T.V) ⟶ C.I.G.G.left) := fun j =>
    (_root_.Formalism.L2.Pj.homAt (𝟙 (Sp T.V)) (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin (chD C.ch)) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫
      C.xT 1).left
  have hDo : ∀ j, D j ≫ C.I.G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) := fun j =>
    (Over.w (_root_.Formalism.L2.Pj.homAt (𝟙 (Sp T.V)) (jetTan ((0 : Fin 1), j) :
      Jet T.V (Fin 1 × Fin (chD C.ch)) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ C.xT 1)).trans (Category.comp_id _)
  have hz0 : spMap ((jetAug : Jet T.V (Fin 1 × Fin (chD C.ch)) (0 + 1) →ₐ[T.V] T.V) :
      Jet T.V (Fin 1 × Fin (chD C.ch)) (0 + 1) →+* T.V) ≫ (C.xT 1).left = (1 : overAt (𝟙 (Sp T.V)) T.V ⟶ C.I.G.G).left :=
    congrArg CommaMorphism.left (C.chartT.zero 1)
  have hDt : ∀ j, ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT C.I.G (D j) (hDo j)) := by
    intro j
    apply Over.OverMorphism.ext
    show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom) ≫
        (spMap ((jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin (chD C.ch)) (0 + 1) →ₐ[T.V] DualNumber T.V) :
          Jet T.V (Fin 1 × Fin (chD C.ch)) (0 + 1) →+* DualNumber T.V) ≫ (C.xT 1).left) =
      Spec.map (CommRingCat.ofHom (algebraMap T.V T.V)) ≫ η[C.I.G.G].left
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have e1 : ((TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom).comp
        ((jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin (chD C.ch)) (0 + 1) →ₐ[T.V] DualNumber T.V) :
          Jet T.V (Fin 1 × Fin (chD C.ch)) (0 + 1) →+* DualNumber T.V) = ((jetAug (m := 0 + 1) : Jet T.V (Fin 1 × Fin (chD C.ch)) (0 + 1) →ₐ[T.V] T.V) :
          _ →+* T.V) := by
      rw [← fst_comp_jetTan]
      rfl
    rw [e1]
    refine hz0.trans ?_
    show (spMap (algebraMap T.V T.V) ≫ 𝟙 _) ≫ η[C.I.G.G].left = _
    rw [Category.comp_id]
  let Mv : Fin (chD C.ch) → (Fin n → T.V) := fun j => tcoord hx _ (hDt j)
  let L : (Fin (chD C.ch) → T.V) →ₗ[T.V] (Fin n → T.V) :=
    { toFun := fun a => ∑ j, a j • Mv j
      map_add' := fun a b => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r a => by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hL : ∀ a, L a = ∑ j, a j • Mv j := fun _ => rfl
  have hcomb : ∀ (a : Fin (chD C.ch) → T.V) (w : Sp (DualNumber T.V) ⟶ C.I.G.G.left)
      (hw : w ≫ C.I.G.G.hom = spMap (algebraMap T.V (DualNumber T.V))),
      IsCombAtG C.I.G (𝟙 (Sp T.V)) D a w →
      ∃ h : ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT C.I.G w hw), tcoord hx _ h = L a := by
    intro a w hw hc
    have e := prodPts_of_combAt C.I.G D hDo a w hw hc
    obtain ⟨h, hh⟩ := prodPts_tan hx a _ hDt
    exact ⟨e ▸ h, (ReciprocityTheory.ChartRestriction.G.Chart.tcoord_congr hx e _ h).trans hh⟩
  have htgo : ∀ k, C.tgT k ≫ C.I.G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) := fun k =>
    ((C.tgBasis.1 k).1).trans (Category.comp_id _)
  have htgt : ∀ k, ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT C.I.G (C.tgT k) (htgo k)) := fun k =>
    chartTan_of C.I.G (C.tgT k) (C.tgBasis.1 k)
  have htgc : ∀ k, tcoord hx _ (htgt k) = Mv k := by
    intro k
    obtain ⟨h, hh⟩ := hcomb (Pi.single k (1 : T.V)) (C.tgT k) (htgo k) (C.chartT.tan k)
    rw [ReciprocityTheory.ChartRestriction.G.Chart.tcoord_congr hx rfl (htgt k) h, hh, hL]
    simp [Pi.single_apply]
  have hLinj : Function.Injective L := by
    intro a b hab
    let tg' : Fin (chD C.ch) → (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := T.V) (DualNumber T.V) ⟶ C.I.G.G) :=
      fun k => toT C.I.G (C.tgT k) (htgo k)
    obtain ⟨ha, ea⟩ := prodPts_tan hx a tg' htgt
    obtain ⟨hb, eb⟩ := prodPts_tan hx b tg' htgt
    have heq : prodPts a tg' = prodPts b tg' := by
      apply tan_ext hx ha hb
      rw [ea, eb]
      simp only [tg', htgc]
      simpa only [hL] using hab
    have hwo : (prodPts a tg').left ≫ C.I.G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) := Over.w _
    have hwT : IsTanAtG C.I.G (𝟙 (Sp T.V)) (prodPts a tg').left :=
      tanAt_of C.I.G _ hwo (by
        have : toT C.I.G (prodPts a tg').left hwo = prodPts a tg' := Over.OverMorphism.ext rfl
        rw [this]; exact ha)
    obtain ⟨a0, _, huniq⟩ := C.tgBasis.2 _ hwT
    have hA : IsCombAtG C.I.G (𝟙 (Sp T.V)) C.tgT a (prodPts a tg').left :=
      combAt_of_prodPts C.I.G C.tgT htgo a _ hwo (Over.OverMorphism.ext rfl)
    have hB : IsCombAtG C.I.G (𝟙 (Sp T.V)) C.tgT b (prodPts a tg').left :=
      combAt_of_prodPts C.I.G C.tgT htgo b _ hwo
        ((Over.OverMorphism.ext rfl : toT C.I.G _ hwo = prodPts a tg').trans heq)
    exact (huniq a hA).trans (huniq b hB).symm

  let y' : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := T.V) (Jet T.V (Fin 1 × Fin (chD C.ch)) 1) ⟶ C.I.G.G :=
    Over.homMk (C.xT 1).left ((Over.w (C.xT 1)).trans (Category.comp_id _))
  have hy' : ReciprocityTheory.ChartRestriction.G.Chart.spMap (jetAug : Jet T.V (Fin 1 × Fin (chD C.ch)) 1 →ₐ[T.V] T.V) ≫ y' = 1 := by
    apply Over.OverMorphism.ext
    show Spec.map (CommRingCat.ofHom ((jetAug : Jet T.V (Fin 1 × Fin (chD C.ch)) 1 →ₐ[T.V] T.V) :
        Jet T.V (Fin 1 × Fin (chD C.ch)) 1 →+* T.V)) ≫ (C.xT 1).left =
      Spec.map (CommRingCat.ofHom (algebraMap T.V T.V)) ≫ η[C.I.G.G].left
    refine hz0.trans ?_
    show (spMap (algebraMap T.V T.V) ≫ 𝟙 _) ≫ η[C.I.G.G].left = _
    rw [Category.comp_id]
  have eD : ∀ k, ReciprocityTheory.ChartRestriction.G.Chart.spMap (jetTan (R := T.V) (m := 0) ((0 : Fin 1), k)) ≫ y' =
      toT C.I.G (D k) (hDo k) := fun k => Over.OverMorphism.ext rfl
  have hk : ∀ k, ReciprocityTheory.ChartRestriction.G.Chart.IsTan
      (ReciprocityTheory.ChartRestriction.G.Chart.spMap (jetTan (R := T.V) (m := 0) ((0 : Fin 1), k)) ≫ y') := fun k => (eD k) ▸ hDt k
  have hkc : ∀ k, tcoord hx _ (hk k) = Mv k := fun k => ReciprocityTheory.ChartRestriction.G.Chart.tcoord_congr hx (eD k) _ _

  let φ : Fin (chD C.ch) → (Jet T.V (Fin 1 × Fin (chD C.ch)) 1 →ₐ[T.V] DualNumber T.V) := fun j =>
    (jetTan (R := T.V) (m := 0) ((0 : Fin 1), j)).comp
      (jetSubstP 1 fun p : Fin 1 × Fin (chD C.ch) => psTrunc 1 (C.actT a p.2))
  have eA : ∀ j, toT C.I.G (D j) (hDo j) ≫ C.I.G.act.act a = ReciprocityTheory.ChartRestriction.G.Chart.spMap (φ j) ≫ y' := by
    intro j
    apply Over.OverMorphism.ext
    have hact := congrArg CommaMorphism.left (C.chartT.act 1 a)
    simp only [Over.comp_left] at hact
    show (_root_.Formalism.L2.Pj.homAt (𝟙 (Sp T.V)) (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin (chD C.ch)) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫
      C.xT 1).left ≫ (C.I.G.act.act a).left = Spec.map (CommRingCat.ofHom (φ j).toRingHom) ≫ (C.xT 1).left
    rw [Over.comp_left, Category.assoc, hact, ← Category.assoc]
    congr 1
    simp only [_root_.Formalism.L2.Pj.homAt, Over.homMk_left, spMap]
    rw [← Spec.map_comp]
    rfl
  have hAt : ∀ j, ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT C.I.G (D j) (hDo j) ≫ C.I.G.act.act a) := fun j =>
    ReciprocityTheory.ChartRestriction.G.Chart.isTan_comp (hDt j) _
  have hAc : ∀ j, tcoord hx _ (hAt j) = ∑ m, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (C.actT a m) • Mv m := by
    intro j
    have hφt : ReciprocityTheory.ChartRestriction.G.Chart.IsTan (ReciprocityTheory.ChartRestriction.G.Chart.spMap (φ j) ≫ y') := (eA j) ▸ hAt j
    rw [ReciprocityTheory.ChartRestriction.G.Chart.tcoord_congr hx (eA j) _ hφt,
      tcoord_jet_lin hx y' hy' (φ j) (fun w => substTan_fst _ j w) hφt hk]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [substTan_snd, hkc]

  let ub : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := T.V) (DualNumber T.V) ⟶ C.I.G.G := C.I.ub ℓ.1 ℓ.2
  have hubt : ReciprocityTheory.ChartRestriction.G.Chart.IsTan ub := (isTan_iff' C.I.G _).1 (C.I.tan ℓ.1 ℓ.2)
  have hubp : ub = prodPts (C.uvecT ℓ) (fun j => toT C.I.G (D j) (hDo j)) :=
    (Over.OverMorphism.ext rfl : ub = toT C.I.G (C.I.ub ℓ.1 ℓ.2).left (Over.w _)).trans
      (prodPts_of_combAt C.I.G D hDo (C.uvecT ℓ) _ (Over.w _) (C.dirT ℓ))
  have hubc : tcoord hx _ hubt = L (C.uvecT ℓ) := by
    obtain ⟨h, hh⟩ := hcomb (C.uvecT ℓ) (C.I.ub ℓ.1 ℓ.2).left (Over.w _) (C.dirT ℓ)
    exact (ReciprocityTheory.ChartRestriction.G.Chart.tcoord_congr hx (Over.OverMorphism.ext rfl) hubt h).trans hh
  have hube : ub ≫ C.I.G.act.act a = ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.scaleD z) ≫ ub :=
    Over.OverMorphism.ext (C.I.eig ℓ.1 ℓ.2 a z hz)
  have hubet : ReciprocityTheory.ChartRestriction.G.Chart.IsTan (ub ≫ C.I.G.act.act a) := ReciprocityTheory.ChartRestriction.G.Chart.isTan_comp hubt _
  have c1 : tcoord hx _ hubet = z • L (C.uvecT ℓ) := by
    rw [ReciprocityTheory.ChartRestriction.G.Chart.tcoord_congr hx hube hubet (ReciprocityTheory.ChartRestriction.G.Chart.isTan_scale z hubt),
      ReciprocityTheory.ChartRestriction.G.Chart.tcoord_scale hx z hubt, hubc]
  have hpb : ub ≫ C.I.G.act.act a = prodPts (C.uvecT ℓ) (fun j => toT C.I.G (D j) (hDo j) ≫ C.I.G.act.act a) := by
    rw [hubp]
    unfold prodPts
    rw [listProd_comp]
    simp only [Category.assoc]
  obtain ⟨hq, eq⟩ := prodPts_tan hx (C.uvecT ℓ) (fun j => toT C.I.G (D j) (hDo j) ≫ C.I.G.act.act a) hAt
  have c2 : tcoord hx _ hubet = L ((Matrix.of fun m j =>
      MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (C.actT a m)).mulVec (C.uvecT ℓ)) := by
    rw [ReciprocityTheory.ChartRestriction.G.Chart.tcoord_congr hx hpb hubet hq, eq, hL]
    simp only [hAc, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  apply hLinj
  rw [← c2, c1, map_smul]

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetD
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff

section JetAlg

variable {K : Type} [Field K] {ι : Type} {m : ℕ}

theorem jetAug_mk (p : MvPolynomial ι K) :
    (jetAug : Jet K ι m →ₐ[K] K) (Ideal.Quotient.mk _ p) = MvPolynomial.constantCoeff p := by
  show (MvPolynomial.aeval fun _ : ι => (0 : K)) p = MvPolynomial.constantCoeff p
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.constantCoeff_X]

theorem constantCoeff_of_mem_orig {p : MvPolynomial ι K} (hp : p ∈ orig K ι) : MvPolynomial.constantCoeff p = 0 := by
  have hle : orig K ι ≤ RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial ι K →+* K) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    simp
  exact (RingHom.mem_ker).1 (hle hp)

theorem isUnit_of_jetAug (a : Jet K ι m) (h : (jetAug : Jet K ι m →ₐ[K] K) a ≠ 0) : IsUnit a := by
  classical
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [jetAug_mk] at h
  set c := MvPolynomial.constantCoeff p with hc

  have hq : p - MvPolynomial.C c ∈ orig K ι := by
    rw [orig, ← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro mo hmo
    have hmo0 : mo ≠ 0 := by
      intro h0
      subst h0
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_pos rfl,
        ← MvPolynomial.constantCoeff_eq, ← hc, sub_self] at hmo
      exact hmo rfl
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hmo0
    exact ⟨i, Set.mem_univ _, hi⟩
  have hnil : IsNilpotent (Ideal.Quotient.mk (orig K ι ^ (m + 1)) (p - MvPolynomial.C c)) := by
    refine ⟨m + 1, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hq _
  have hu : IsUnit (Ideal.Quotient.mk (orig K ι ^ (m + 1)) (MvPolynomial.C c)) :=
    (isUnit_iff_ne_zero.2 h).map (Ideal.Quotient.mk (orig K ι ^ (m + 1)) |>.comp MvPolynomial.C)
  have hsplit : Ideal.Quotient.mk (orig K ι ^ (m + 1)) p =
      Ideal.Quotient.mk (orig K ι ^ (m + 1)) (MvPolynomial.C c) +
        Ideal.Quotient.mk (orig K ι ^ (m + 1)) (p - MvPolynomial.C c) := by
    rw [← map_add (f := _), add_sub_cancel]
  rw [hsplit]
  exact hnil.isUnit_add_left_of_commute hu (Commute.all _ _)

theorem jetAug_jetMap {ι' : Type} (φ : ι → MvPolynomial ι' K) (hφ : ∀ i, φ i ∈ orig K ι') (a : Jet K ι m) :
    (jetAug : Jet K ι' m →ₐ[K] K) (jetMap φ hφ a) = (jetAug : Jet K ι m →ₐ[K] K) a := by
  have hcc : ∀ {ι' : Type} (φ : ι → MvPolynomial ι' K), (∀ i, φ i ∈ orig K ι') →
      ∀ q : MvPolynomial ι K, MvPolynomial.constantCoeff (MvPolynomial.aeval φ q) = MvPolynomial.constantCoeff q := by
    intro ι' φ hφ q
    induction q using MvPolynomial.induction_on with
    | C c => simp [MvPolynomial.aeval_C]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.aeval_X, hp, MvPolynomial.constantCoeff_X, mul_zero,
        constantCoeff_of_mem_orig (hφ i)]
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hmap : jetMap (m := m) φ hφ (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPolynomial.aeval φ p) := rfl
  rw [hmap, jetAug_mk, jetAug_mk, hcc φ hφ p]

theorem jetMap_congr {ι' : Type} (φ φ' : ι → MvPolynomial ι' K) (hφ : ∀ i, φ i ∈ orig K ι')
    (hφ' : ∀ i, φ' i ∈ orig K ι')
    (h : ∀ i, Ideal.Quotient.mk (orig K ι' ^ (m + 1)) (φ i) = Ideal.Quotient.mk (orig K ι' ^ (m + 1)) (φ' i))
    (a : Jet K ι m) : jetMap φ hφ a = jetMap φ' hφ' a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hext : (Ideal.Quotient.mkₐ K (orig K ι' ^ (m + 1))).comp (MvPolynomial.aeval φ) =
      (Ideal.Quotient.mkₐ K (orig K ι' ^ (m + 1))).comp (MvPolynomial.aeval φ') := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa using h i
  show Ideal.Quotient.mk _ (MvPolynomial.aeval φ p) = Ideal.Quotient.mk _ (MvPolynomial.aeval φ' p)
  exact DFunLike.congr_fun hext p

theorem isLocalHom_jetMap {ι' : Type} (φ : ι → MvPolynomial ι' K) (hφ : ∀ i, φ i ∈ orig K ι') :
    IsLocalHom ((jetMap (m := m) φ hφ : Jet K ι m →ₐ[K] Jet K ι' m) : Jet K ι m →+* Jet K ι' m) := by
  refine ⟨fun a ha => isUnit_of_jetAug a ?_⟩
  rw [← jetAug_jetMap φ hφ a]
  exact (ha.map (jetAug : Jet K ι' m →ₐ[K] K)).ne_zero

end JetAlg

variable {g : ℕ} {Y : Scheme.{0}}


set_option backward.isDefEq.respectTransparency false in
theorem jetPt_precomp (e e' : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (hol' : IsHolFam e')
    (h0 : e' 0 = e 0) (m : ℕ) (χ : Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) m) [hχl : IsLocalHom χ]
    (hχ : ∀ (U : Y.Opens) (_ : e 0 cpt ∈ U) (f : Γ(Y, U)),
      χ (jetOf m (fun z => valAt' (e z) U f)) = jetOf m (fun z => valAt' (e' z) U f)) :
    spMap χ ≫ jetPt e hol m = jetPt e' hol' m := by
  unfold jetPt
  rw [spMap, spec_comp_nbhdPt]
  have hres : ∀ (U V : Y.Opens) (hU : e 0 cpt ∈ U) (hV : e 0 cpt ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ (jetψ e hol m V hV ≫ CommRingCat.ofHom χ) =
      jetψ e hol m U hU ≫ CommRingCat.ofHom χ :=
    fun U V hU hV h => by rw [← Category.assoc, jetψ_res]
  have hloc : ∀ (U : Y.Opens) (hU : e 0 cpt ∈ U) (f : Γ(Y, U)),
      IsUnit ((jetψ e hol m U hU ≫ CommRingCat.ofHom χ) f) → e 0 cpt ∈ Y.basicOpen f := by
    intro U hU f hf
    rw [CommRingCat.comp_apply] at hf
    exact jetψ_loc e hol m U hU f (hχl.map_nonunit _ hf)
  have hpt := nbhdPt_closedPoint _ hres hloc
  have hpt' := nbhdPt_closedPoint (y₀ := e' 0 cpt) _ (jetψ_res e' hol' m) (jetψ_loc e' hol' m)
  refine hom_ext_of_local (hpt.trans (by rw [hpt', h0])) fun U h₁ h₂ => ?_
  have hU : e 0 cpt ∈ U := by
    have : nbhdPt _ hres (IsLocalRing.closedPoint _) ∈ U :=
      h₁ (show IsLocalRing.closedPoint _ ∈ (⊤ : (Spec _).Opens) from trivial)
    rwa [hpt] at this
  have hU' : e' 0 cpt ∈ U := by rw [h0]; exact hU
  rw [nbhdPt_appLE _ hres hloc U hU h₁, nbhdPt_appLE _ (jetψ_res e' hol' m) (jetψ_loc e' hol' m) U hU' h₂]
  congr 1
  ext f
  rw [CommRingCat.comp_apply, jetψ_apply, jetψ_apply]
  exact hχ U hU f

def jetScaleP (m : ℕ) (c : Fin g → ℂ) : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m :=
  jetMap (fun p => MvPolynomial.C (c p.2) * MvPolynomial.X p)
    fun p => Ideal.mul_mem_left _ _ (X_mem_orig p)

theorem jetOf_scale (m : ℕ) (c : Fin g → ℂ) {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) :
    jetOf m (fun z => θ fun i => c i * z i) = jetScaleP m c (jetOf m θ) := by
  have ha : ∀ p : Fin 1 × Fin g, MvPowerSeries.constantCoeff
      (MvPowerSeries.C (c p.2) * MvPowerSeries.X p : MvPowerSeries (Fin 1 × Fin g) ℂ) = 0 := by
    intro p
    simp
  unfold jetOf jetScaleP
  rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.partA θ hθ c, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psJet_subst m _ ha]
  refine jetMap_congr _ _ _ _ (fun p => ?_) _
  have hco : (MvPowerSeries.C (c p.2) * MvPowerSeries.X p : MvPowerSeries (Fin 1 × Fin g) ℂ) =
      ((MvPolynomial.C (c p.2) * MvPolynomial.X p : MvPolynomial (Fin 1 × Fin g) ℂ) :
        MvPowerSeries (Fin 1 × Fin g) ℂ) := by
    simp
  rw [hco, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.mk_trunc_coe]

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPairA
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Opposite ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem isHolTo_comp {Y Y' : Scheme.{0}} {B : Set V} {y : V → (Sp ℂ ⟶ Y)} (hy : IsHolTo B y) (φ : Y ⟶ Y') :
    IsHolTo B (fun b => y b ≫ φ) := by
  intro U f
  have hpre : ∀ b, (y b ≫ φ) ⁻¹ᵁ U = y b ⁻¹ᵁ (φ ⁻¹ᵁ U) := fun b => by
    first
      | rfl
      | simp
  obtain ⟨h1, h2⟩ := hy (φ ⁻¹ᵁ U) (φ.app U f)
  simp only [hpre]
  refine ⟨h1, ?_⟩
  refine h2.congr (fun b hb => ?_)
  have hb2 : ⊤ ≤ (y b ≫ φ) ⁻¹ᵁ U := by
    rw [hpre]
    exact hb.2
  unfold valAt'
  rw [dite_eq_left hb2, dite_eq_left hb.2]
  first
    | rfl
    | simp [Scheme.comp_app]
    | (simp only [Scheme.comp_app]; done)

theorem isHolTo_of_local {Y : Scheme.{0}} {B : Set V} {y : V → (Sp ℂ ⟶ Y)}
    (h : ∀ (U : Y.Opens) (f : Γ(Y, U)) (b₀ : V), b₀ ∈ B → ⊤ ≤ y b₀ ⁻¹ᵁ U →
      ∃ N ∈ nhds b₀, N ⊆ {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun b => valAt' (y b) U f) N) :
    IsHolTo B y := by
  unfold IsHolTo
  intro U f
  have hS : IsOpen {b | b ∈ B ∧ ⊤ ≤ y b ⁻¹ᵁ U} := by
    rw [isOpen_iff_mem_nhds]
    intro b hb
    obtain ⟨N, hN, hNS, -⟩ := h U f b hb.1 hb.2
    exact Filter.mem_of_superset hN hNS
  refine ⟨hS, fun b hb => ?_⟩
  obtain ⟨N, hN, -, hd⟩ := h U f b hb.1 hb.2
  exact (hd.differentiableAt hN).differentiableWithinAt

theorem isHolTo_of_affine {T : Scheme.{0}} [IsAffine T] {B : Set V} (hB : IsOpen B) {z : V → (Sp ℂ ⟶ T)}
    (hz : ∀ r : Γ(T, ⊤), DifferentiableOn ℂ (fun b => valAt' (z b) ⊤ r) B) : IsHolTo B z := by
  refine isHolTo_of_local fun U f b₀ hb₀ hU => ?_
  have hmem : (z b₀) cpt ∈ U := hU (Set.mem_univ _)
  obtain ⟨r, hrU, hr0⟩ := (isAffineOpen_top T).exists_basicOpen_le (V := U) ⟨(z b₀) cpt, hmem⟩ trivial
  have htop : ∀ b, ⊤ ≤ z b ⁻¹ᵁ (⊤ : T.Opens) := fun b p _ => trivial

  set N := {b ∈ B | valAt' (z b) ⊤ r ≠ 0} with hNdef
  have hNo : IsOpen N := (hz r).continuousOn.isOpen_inter_preimage hB isOpen_ne
  have hmemD : ∀ b, valAt' (z b) ⊤ r ≠ 0 → ⊤ ≤ z b ⁻¹ᵁ T.basicOpen r := fun b hb =>
    top_le_of_mem ((valAt'_ne_zero_iff (z b) ⊤ (htop b) r cpt).1 hb)
  have hb0N : b₀ ∈ N := ⟨hb₀, (valAt'_ne_zero_iff (z b₀) ⊤ (htop b₀) r cpt).2 hr0⟩

  obtain ⟨⟨hh, s⟩, hk⟩ := IsLocalization.surj (Submonoid.powers r)
    (T.presheaf.map (homOfLE hrU).op f)
  obtain ⟨k, hks⟩ := s.2
  dsimp only at hk
  have hval : ∀ b ∈ N, valAt' (z b) U f * valAt' (z b) ⊤ r ^ k = valAt' (z b) ⊤ hh := by
    intro b hb
    have hD := hmemD b hb.2
    have e := congrArg (valAt' (z b) (T.basicOpen r)) hk
    rw [valAt'_mul, valAt'_res (z b) hrU hD] at e
    have e2 : ∀ x : Γ(T, ⊤), valAt' (z b) (T.basicOpen r) (algebraMap Γ(T, ⊤) Γ(T, T.basicOpen r) x) =
        valAt' (z b) ⊤ x := fun x => valAt'_res (z b) le_top hD x
    rw [e2, e2, ← hks] at e
    have e3 : valAt' (z b) ⊤ (r ^ k) = valAt' (z b) ⊤ r ^ k := map_pow (valHom (z b) ⊤ (htop b)) r k
    rw [e3] at e
    exact e
  refine ⟨N, hNo.mem_nhds hb0N, fun b hb => ⟨hb.1, (hmemD b hb.2).trans (Scheme.Hom.preimage_mono _ hrU)⟩, ?_⟩
  have h1 : DifferentiableOn ℂ (fun b => valAt' (z b) ⊤ hh) N := (hz hh).mono fun b (hb : b ∈ N) => hb.1
  have h2 : DifferentiableOn ℂ ((fun b => valAt' (z b) ⊤ r) ^ k) N :=
    ((hz r).mono fun b (hb : b ∈ N) => hb.1).pow k
  have h3 : DifferentiableOn ℂ ((fun b => valAt' (z b) ⊤ r) ^ k)⁻¹ N :=
    h2.inv fun b (hb : b ∈ N) => by simp only [Pi.pow_apply]; exact pow_ne_zero _ hb.2
  have h4 := h1.mul h3
  refine h4.congr fun b hb => ?_
  simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply]
  rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hb.2)]
  exact hval b hb

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

