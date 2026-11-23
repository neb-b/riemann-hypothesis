module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0005
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdAd
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Comp1IdentityLeft
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifBijectiveOfParam
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.BasicOpenEqBotOfField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace PositivityTheory.HtPt.Cf

theorem basicOpen_eq_bot_of_field {K : Type} [Field K] {Y : Scheme.{0}} (π : Y ⟶ Sp K) [UniversallyClosed π]
    [ConnectedSpace Y] (f : Γ(Y, ⊤)) (y₀ : Y) (h₀ : y₀ ∉ Y.basicOpen f) : Y.basicOpen f = ⊥ := by
  let φ : K →+* Γ(Y, ⊤) := π.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have hφ : φ.IsIntegral := RingHom.IsIntegral.trans _ _
    (RingHom.isIntegral_of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.surjective)
    (isIntegral_appTop_of_universallyClosed π)
  obtain ⟨p, hp, hpf⟩ := hφ f
  obtain ⟨q, hq, hn⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp.ne_zero 0
  have hc : q.coeff 0 ≠ 0 := fun h => hn (by simpa using Polynomial.X_dvd_iff.2 h)
  let g := Polynomial.eval₂ φ f q
  have h1 : f ^ p.rootMultiplicity 0 * g = 0 := by
    rw [hq, Polynomial.eval₂_mul, Polynomial.eval₂_pow] at hpf
    simpa using hpf
  have h2 : g = f * Polynomial.eval₂ φ f q.divX + φ (q.coeff 0) := by
    show Polynomial.eval₂ φ f q = _
    conv_lhs => rw [← Polynomial.X_mul_divX_add q]
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C]
  have key : ∀ y : Y, y ∉ Y.basicOpen f ↔ y ∈ Y.basicOpen g := fun y => by
    rw [← Y.evaluation_eq_zero_iff_notMem_basicOpen (U := ⊤) y trivial,
      ← Y.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) y trivial]
    let v := (Y.evaluation ⊤ y trivial).hom
    show v f = 0 ↔ v g ≠ 0
    constructor
    · intro h
      rw [h2, map_add (f := _), map_mul, h, zero_mul, zero_add]
      exact (map_ne_zero (v.comp φ)).2 hc
    · intro h
      have := congrArg v h1
      rw [map_mul, map_pow, map_zero] at this
      exact eq_zero_of_pow_eq_zero ((mul_eq_zero.1 this).resolve_right h)
  have hcl : IsClopen (Y.basicOpen f : Set Y) := by
    refine ⟨⟨?_⟩, (Y.basicOpen f).isOpen⟩
    have : (Y.basicOpen f : Set Y)ᶜ = Y.basicOpen g := Set.ext key
    rw [this]; exact (Y.basicOpen g).isOpen
  rcases isClopen_iff.1 hcl with h | h
  · exact TopologicalSpace.Opens.ext h
  · exact absurd (show y₀ ∈ (Y.basicOpen f : Set Y) from h ▸ trivial) h₀

theorem geomReduced_of_smooth {X S : Scheme.{0}} (π : X ⟶ S) [Smooth π] : GeometricallyReduced π :=
  ⟨fun K _ y Z fst snd h => by
    have : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) h ‹_›
    exact isReduced_of_smooth snd⟩

theorem exists_generic {S : Scheme.{0}} (s : S) : ∃ z : S, z ⤳ s ∧ ∀ z' : S, z' ⤳ z → z' = z := by
  have hi := isIrreducible_irreducibleComponent (x := s)
  have hg := hi.isGenericPoint_genericPoint isClosed_irreducibleComponent
  refine ⟨_, hg.specializes mem_irreducibleComponent, fun z' hz => ?_⟩
  have hsub : irreducibleComponent s ⊆ closure {z'} := by
    rw [← hg.def]
    exact closure_minimal (Set.singleton_subset_iff.2 hz.mem_closure) isClosed_closure
  have he : closure {z'} = irreducibleComponent s :=
    eq_irreducibleComponent isIrreducible_singleton.closure.isPreirreducible hsub
  exact (IsGenericPoint.eq (show IsGenericPoint z' _ from he) hg)

theorem bijective_of_generic {X S : Scheme.{0}} (π : X ⟶ S) (e : S ⟶ X) (he : e ≫ π = 𝟙 S) [Smooth π]
    [GeometricallyConnected π] [IsReduced S] [IsLocallyNoetherian S]
    (h : ∀ z : S, (∀ z' : S, z' ⤳ z → z' = z) →
      ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ S), z ∈ Set.range t ∧ IsProper (pullback.snd π t)) :
    Function.Bijective π.appTop.hom := by
  have hret : ∀ a, e.appTop (π.appTop a) = a := fun a => by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, he, Scheme.Hom.id_appTop]; rfl
  refine ⟨Function.LeftInverse.injective hret, fun f => ⟨e.appTop f, ?_⟩⟩
  have := geomReduced_of_smooth π
  have : IsReduced X := GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian π
  symm
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  set f' := f - π.appTop.hom (e.appTop f) with hf'
  have h0 : e.appTop f' = 0 := by
    rw [hf', map_sub]; exact sub_eq_zero.2 (hret _).symm
  have hout : ∀ s, e s ∉ X.basicOpen f' := fun s hs => by
    have : s ∈ e ⁻¹ᵁ X.basicOpen f' := hs
    rw [Scheme.preimage_basicOpen_top, h0, Scheme.basicOpen_zero] at this
    exact this
  by_contra hne
  obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
  obtain ⟨z, hz, hgen⟩ := exists_generic (π x)
  obtain ⟨x', hx', hxz⟩ : z ∈ π '' (X.basicOpen f' : Set X) :=
    hz.mem_open (π.isOpenMap _ (X.basicOpen f').isOpen) ⟨x, hx, rfl⟩
  obtain ⟨K, _, t, ⟨w, hw⟩, hp⟩ := h z hgen
  have : ConnectedSpace ↥(pullback π t) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback π t)
  obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := t) x' w (hxz.trans hw.symm)
  obtain ⟨y₀, hy₀, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := t) (e z) w
    (((Scheme.Hom.comp_apply e π z).symm.trans (by rw [he]; rfl)).trans hw.symm)
  have hb := basicOpen_eq_bot_of_field (pullback.snd π t) ((pullback.fst π t).appTop f') y₀ (by
    rw [← Scheme.preimage_basicOpen_top]
    show pullback.fst π t y₀ ∉ X.basicOpen f'
    rw [hy₀]; exact hout z)
  have : y ∈ pullback.fst π t ⁻¹ᵁ X.basicOpen f' := by
    show pullback.fst π t y ∈ X.basicOpen f'
    rw [hy]; exact hx'
  rw [Scheme.preimage_basicOpen_top, hb] at this
  exact this

theorem pow_smooth_conn {S : Scheme.{0}} (G : Over S) [Smooth G.hom] [GeometricallyConnected G.hom] :
    ∀ n : ℕ, Smooth (Out.powObj G n).hom ∧ GeometricallyConnected (Out.powObj G n).hom := by
  intro n
  induction n with
  | zero =>
    exact ⟨inferInstanceAs (Smooth (𝟙 S)), ⟨fun K _ y Z fst snd h => by
      have : IsIso snd := h.isIso_snd_of_isIso (f := 𝟙 S)
      have : ConnectedSpace (Spec (CommRingCat.of K)) := inferInstanceAs (ConnectedSpace (PrimeSpectrum K))
      exact snd.homeomorph.connectedSpace_iff.2 this⟩⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [show Out.powObj G (n + 1) = G ⊗ Out.powObj G n from rfl, Over.tensorObj_hom, pullback.condition]
    exact ⟨inferInstance, GeometricallyConnected.comp _ _⟩

theorem pow_proper {S : Scheme.{0}} (G : Over S) [IsProper G.hom] : ∀ n : ℕ, IsProper (Out.powObj G n).hom
  | 0 => inferInstanceAs (IsProper (𝟙 S))
  | n + 1 => by
    have := pow_proper G n
    rw [show Out.powObj G (n + 1) = G ⊗ Out.powObj G n from rfl, Over.tensorObj_hom, pullback.condition]
    infer_instance

theorem pow_fns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0), IsReduced X0 → IsLocallyNoetherian X0 → (∀ z : X0, (∀ z' : X0, z' ⤳ z → z' = z) → z ∈ abLocus t.G) → PowFns t := by
  intro E _ _ _ H X0 t _ _ h n
  have := t.semi.smooth
  have := t.semi.geomConnected
  obtain ⟨h1, h2⟩ := pow_smooth_conn t.G n
  refine bijective_of_generic (Out.powObj t.G n).hom (η[Out.powObj t.G n]).left (Over.w (η[Out.powObj t.G n]))
    fun z hz => ?_
  let K := AlgebraicClosure (X0.residueField z)
  let x : Sp K ⟶ X0 := spMap (algebraMap (X0.residueField z) K) ≫ X0.fromSpecResidueField z
  have hx : z ∈ Set.range x := ⟨IsLocalRing.closedPoint K, Scheme.fromSpecResidueField_apply z _⟩
  refine ⟨K, inferInstance, x, hx, ?_⟩
  have : IsProper ((Over.pullback x).obj t.G).hom := h z hz K x hx
  have := pow_proper ((Over.pullback x).obj t.G) n
  let e := GlobalFunctionsDvrPowers.pullPowIso x t.G n
  have : IsIso e.hom.left := isIso_inv_left e.symm
  show IsProper ((Over.pullback x).obj (Out.powObj t.G n)).hom
  rw [← Over.w e.hom]
  infer_instance

end PositivityTheory.HtPt.Cf
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.CaNfold
section
noncomputable section

namespace PositivityTheory.HtPt.Ca

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

section SlopeTestRemainingChoices

open ReciprocityTheory.ChartRestriction.G.TB.Canon Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdAd ReciprocityTheory.ChartRestriction.G.DVR

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}

theorem exists_kappa (t : SAB H X0) (n : ℕ) :
    ∃ κ : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G ^ n, snd t.G t.G]) (cφG t ![fst t.G t.G, snd t.G t.G]))
      (Sum.elim (cε 2) fun I => -((n : ℤ) * cε 2 I))), κ.IsGen ∧
      ∀ (T : Over X0) (p q : T ⟶ t.G) (z : T.left) (J), Good t.PP.L z J →
        val κ (lift p q).left z J = cubN (cubV t.cub z J) n 1 p q := by
  obtain ⟨t₀, ht₀, hv₀⟩ := exists_cubN t.cub (1 : t.G ⊗ t.G ⟶ t.G) (fst t.G t.G) (snd t.G t.G) n
  obtain ⟨κ, hκ, hv⟩ := exists_gen t.PP.isLB
    (φ' := Sum.elim (cφG t ![fst t.G t.G ^ n, snd t.G t.G]) (cφG t ![fst t.G t.G, snd t.G t.G]))
    (ε' := Sum.elim (cε 2) fun I => -((n : ℤ) * cε 2 I)) (fun U _ h => by
      have a := prod_cube₂ (fst t.G t.G ^ n) (snd t.G t.G) h
      have b := prod_cube₂ (fst t.G t.G) (snd t.G t.G) h
      have b' : ∏ I, h (cφG t ![fst t.G t.G, snd t.G t.G] I) ^ (-((n : ℤ) * cε 2 I)) =
          (∏ I, h (cφG t ![fst t.G t.G, snd t.G t.G] I) ^ (cε 2 I)) ^ (-(n : ℤ)) := by
        rw [← Finset.prod_zpow]
        exact Finset.prod_congr rfl fun I _ => by rw [← zpow_mul]; congr 1; ring
      refine Eq.trans ?_ ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) a
        (b'.trans (congrArg (· ^ (-(n : ℤ))) b)))).symm
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_pow]
      module) t₀ ht₀
  refine ⟨κ, hκ, fun T p q z J hJ => (hv _ _ z J hJ).trans ((hv₀ T (lift p q) z J hJ).trans ?_)⟩
  rw [MonObj.comp_one, lift_fst, lift_snd]

variable [StarRing (𝓞 E)] {t : SAB H X0} {S : Type} [CommRing S] {x : Sp S ⟶ X0} {d : ℕ} (g : GermAt t x d) {m k : ℕ}

theorem ac_zero (u : Q S d k) : ac (AQ g.B.A 0) u = 0 :=
  (congrArg (sq ![u]) (show AQ g.B.A 0 = 0 from Subtype.ext (act_zero_eq g.B))).trans (map_zero _)

theorem ac_succ (n : ℕ) (u : Q S d k) :
    ac (AQ g.B.A ((n + 1 : ℕ) : 𝓞 E)) u = op (FQ g.B.G) (ac (AQ g.B.A (n : 𝓞 E)) u) u := by
  rw [Nat.cast_succ, ac_add, ac_one]

theorem PP_nat (n : ℕ) (u : Q S d k) : PP m g.x (ac (AQ g.B.A (n : 𝓞 E)) u) = PP m g.x u ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, ac_zero, PP_zero g.chart, pow_zero]
  | succ n ih => rw [ac_succ, PP_op g.chart, ih, pow_succ]

theorem value_first_power {y : (jOG x d m 2).left} {J : ((jOG x d m 2).left ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L y J)
    (n : ℕ) : VV m y (pow1 g.B n) = (cubN (cubV t.cub y J) n 1 (PP m g.x (gen 0)) (PP m g.x (gen 1)) *
      (ee g.x g.e y J (ac (AQ g.B.A (n : 𝓞 E)) (gen 0)) (gen 1))⁻¹ * ee g.x g.e y J (gen 0) (gen 1) ^ n).val := by
  induction n with
  | zero =>
    rw [pow1, Finset.prod_range_zero, VV_one, Nat.cast_zero, ac_zero, (dict_ax hJ g.axes _).1]
    simp [cubN]
  | succ n ih =>
    have e : pow1 g.B (n + 1) = pow1 g.B n * E3 g.B.ph1 (ac (AQ g.B.A (n : 𝓞 E)) (gen 0)) (gen 0) (gen 1) := by
      simp only [formalSeriesValueAtThreePoints_eq_ev, ac_val, gen_val]
      exact Finset.prod_range_succ _ _
    rw [e, VV_mul, ih, frame_biext_dictionary_first_partial_law hJ g.frame, ← Units.val_mul, ac_succ, PP_nat]
    refine congrArg Units.val (Additive.ofMul.injective ?_)
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul, pow_succ, ofMul_mul, ofMul_inv]
    abel

theorem homAt_gen : (homAt x (jQ m ![(gen 0 : Q S d 2), gen 1])).left = 𝟙 _ := by
  have e : jQ m ![(gen 0 : Q S d 2), gen 1] = AlgHom.id S _ := GermD.jet_hom_ext fun s => by
    obtain ⟨j, s⟩ := s
    rw [jQ_X]
    fin_cases j <;> exact psJet_X m _
  rw [e]
  exact Spec.map_id _

end SlopeTestRemainingChoices


open ReciprocityTheory.ChartRestriction.G.TB.Canon Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdAd in
theorem nfold_law : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (n : ℕ), ∃ κ : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G ^ n, snd t.G t.G]) (cφG t ![fst t.G t.G, snd t.G t.G])) (Sum.elim (cε 2) fun I => -((n : ℤ) * cε 2 I))), κ.IsGen ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ κ (lift (1 : t.G ⟶ t.G) (𝟙 t.G)).left) (LB.oneGen t.PP.L) ∧ ∀ (S : Type) [CommRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d) (m : ℕ), ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (pow1 g.B n) ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ κ (lift (jptG t x d g.x m (0 : Fin 2)) (jptG t x d g.x m (1 : Fin 2))).left) (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x d g.x g.e m ![fun j => psIn d m ![0] (g.B.A.act (n : 𝓞 E) j), fun j => MvPolynomial.X ((1 : Fin 2), j)]) (LB.invGen t.PP.L _ _ (genPowG t _ _ (g.e m) n)))) := by
  intro E _ _ _ H _ _ X0 t n
  obtain ⟨κ, hκ, hv⟩ := exists_kappa t n
  refine ⟨κ, hκ, corr_of_val t.PP.isLB fun y J hJ => ?_, fun S _ x d g m => ?_⟩
  · refine (val_pull hJ _ _ _).trans ?_
    rw [Category.id_comp, val_one, hv _ _ _ y J hJ]
    exact Finset.prod_eq_one fun i _ => (isCub_cubV t.cub hJ).face₂ _ _
  · have hc : MvPowerSeries.constantCoeff (pow1 g.B n) = 1 := by
      rw [← cc_ev ZZa, ((act_zero S d _ g.B).2.2.2 n).1.1, map_one]
    obtain ⟨w, hw⟩ : IsUnit (pow1 g.B n) := MvPowerSeries.isUnit_iff_constantCoeff.2 (hc ▸ isUnit_one)
    let u : (Jet S (Fin 2 × Fin d) m)ˣ := ⟨psJet m w.val, psJet m w.inv,
      by rw [← FBIdJet.psJet_mul, w.val_inv, FBIdJet.psJet_one], by rw [← FBIdJet.psJet_mul, w.inv_val, FBIdJet.psJet_one]⟩
    have hu : (u : Jet S (Fin 2 × Fin d) m) = psJet m (pow1 g.B n) := congrArg (psJet m) hw
    refine ⟨u, hu, corr_of_val t.PP.isLB fun y J hJ => ?_⟩
    refine (val_pull hJ _ _ _).trans ?_
    rw [Category.id_comp, hv _ _ _ y J hJ]
    have h0 := gm_unit (x0 := x) (y := y) u ![gen 0, gen 1] _ hu
    have h1 := val_peG g.x hJ g.e ![gen 0, gen 1]
      ![fun j => psIn d m ![0] (g.B.A.act (n : 𝓞 E) j), fun j => MvPolynomial.X ((1 : Fin 2), j)]
      (ac (AQ g.B.A (n : 𝓞 E)) (gen 0)) (gen 1)
      (by rintro ⟨l, j⟩; fin_cases l; exacts [hA _ 0 j, hX 1 j])
      (by rintro ⟨l, j⟩; fin_cases l; exacts [(FBIdPh.cc_psIn d m _ _).trans (g.B.A.const _ j),
        MvPolynomial.constantCoeff_X _ _])
    rw [sq_ac, sq_gen, sq_gen, homAt_gen] at h1
    have h2 : val (genPowG t _ _ (g.e m) n) (𝟙 _) y J = ee g.x g.e y J (gen 0) (gen 1) ^ n := by
      rw [ee, homAt_gen]; exact map_pow _ _ _
    have h3 : sb ![(gen 0 : Q S d 2), gen 1] (pow1 g.B n) = pow1 g.B n := formalSeriesValueAtTwoPoints_genericPoints _
    rw [h3, value_first_power g hJ, homAt_gen] at h0
    refine Eq.trans ?_ ((val_scale hJ _ _ _).trans (congrArg₂ (· * ·) (Units.ext h0) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) h1 ((val_inv _ _).trans (congrArg (·⁻¹) h2)))))).symm
    rw [PP_gen, PP_gen]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, Matrix.cons_val]
    abel

end PositivityTheory.HtPt.Ca
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.CdUniv
section
noncomputable section
namespace PositivityTheory.HtPt.Cd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.ChartCompare GlobalTheory.FrameTangent GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws

section Gen
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {X0 : Scheme.{0}}
  {t : SAB H X0} {S : Type} [CommRing S] {x : Sp S ⟶ X0} {d : ℕ} (g : GermAt t x d)

def jp : JetPts t.G x d := (famEquiv x t.G d).symm g.x

theorem fam_jp : famEquiv x t.G d (jp g) = g.x := Equiv.apply_symm_apply _ _

theorem x_eq (m : ℕ) : g.x m = homAt x (jIn S d m) ≫ jp g m := (congrFun (fam_jp g) m).symm

theorem jp_eq (m : ℕ) : jp g m = homAt x (jOut S d m) ≫ g.x m := rfl

theorem jp_zero (m : ℕ) : algMap x (jetAug : Jet S (Fin d) m →ₐ[S] S) ≫ jp g m = 1 :=
  (zero_iff t x (jp g) m).1 (by rw [fam_jp]; exact g.chart.zero m)

def gd : (Fin d → S) →ₗ[S] TanM x t.G := dif x (jp g 1) (jp_zero g 1)

theorem tg_eq (l : Fin d) : g.tg l = (tv (gd g (Pi.single l 1))).left := by
  have h := (tan_iff t x (jp g) (jp_zero g 1) (g.tg l) (fun j => if l = j then 1 else 0)).2
    (by rw [fam_jp]; exact g.chart.tan l)
  have e : (fun j => if l = j then (1 : S) else 0) = Pi.single l 1 := by
    funext j; simp [Pi.single_apply, eq_comm]
  rw [e] at h
  exact h

theorem comb_iff (a : Fin d → S) (w : Sp (DualNumber S) ⟶ t.G.left) :
    IsCombAtG t x g.tg a w ↔ (tv (gd g a)).left = w := by
  have e : g.tg = fun i => (tv (gd g (Pi.single ((Equiv.refl (Fin d)) i) 1))).left := funext (tg_eq g)
  have e₂ : ∑ i, a i • gd g (Pi.single i 1) = gd g a := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_smul, ← map_sum]
    congr 1
    funext k; simp [Pi.single_apply]
  rw [e, ← e₂]
  exact comb_iff_sum t x (Equiv.refl _) (fun i => gd g (Pi.single i 1)) a w

theorem gd_bij : Function.Bijective (gd g) := by
  rw [Function.bijective_iff_existsUnique]
  intro W
  refine (existsUnique_congr fun a => ?_).1 (g.basis _ (isTanAtG_of _ (tv_zero' W)))
  rw [comb_iff]
  exact ⟨fun h => tv_injective (Over.OverMorphism.ext h), fun h => by rw [h]⟩

theorem jp_param : IsFormalParam t.G x (jp g) :=
  param_of_dif_bijective t.semi.smooth
    (fun m => (trunc_iff t x (jp g) m).1 (by rw [fam_jp]; exact g.chart.trunc m)) (jp_zero g) (gd_bij g)

theorem coord_unique {m : ℕ} {B : Type} [CommRing B] [Algebra S B] (I : Ideal B) (hI : I ^ (m + 1) = ⊥)
    (y : overAt x B ⟶ t.G) (hy : homAt x (Ideal.Quotient.mkₐ S I) ≫ y = 1) :
    ∃! χ : Jet S (Fin 1 × Fin d) m →ₐ[S] B, y = homAt x χ ≫ g.x m := by
  obtain ⟨f, hf, hu⟩ := (jp_param g).2.2 m B I hI y hy
  refine ⟨f.comp (jOut S d m), ?_, fun χ hχ => ?_⟩
  · beta_reduce
    rw [← hcomp, ← jp_eq]; exact hf.symm
  · have := hu (χ.comp (jIn S d m)) (by
      beta_reduce
      rw [algMap_eq, ← hcomp, ← x_eq]; exact hχ.symm)
    rw [← this, AlgHom.comp_assoc, jIn_jOut, AlgHom.comp_id]

theorem coord_aug {m : ℕ} {B : Type} [CommRing B] [Algebra S B] (aug : B →ₐ[S] S)
    (hI : RingHom.ker aug ^ (m + 1) = ⊥) (y : overAt x B ⟶ t.G) (hy : homAt x aug ≫ y = 1) :
    ∃! χ : Jet S (Fin 1 × Fin d) m →ₐ[S] B, aug.comp χ = jetAug ∧ y = homAt x χ ≫ g.x m := by
  have e : Ideal.Quotient.mkₐ S (RingHom.ker aug) = (Algebra.ofId S _).comp aug := by
    refine AlgHom.ext fun r => ?_
    show Ideal.Quotient.mk _ r = Ideal.Quotient.mk _ (algebraMap S B (aug r))
    rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, AlgHom.commutes]
    simp
  obtain ⟨χ, hχ, hu⟩ := coord_unique g _ hI y (by rw [e, ← hcomp, hy, MonObj.comp_one])
  refine ⟨χ, ⟨?_, hχ⟩, fun χ' h => hu χ' h.2⟩
  exact (coord_unique g (m := m) (B := S) ⊥ (Ideal.bot_pow (by omega)) 1 (MonObj.comp_one _)).unique
    (by rw [← hcomp, ← hχ, hy]) (g.chart.zero m).symm

theorem ker_aug_pow (J : Type) (m : ℕ) : RingHom.ker (jetAug : Jet S J m →ₐ[S] S) ^ (m + 1) = ⊥ :=
  Chart.ker_jetAug_pow (R := S) J m

theorem coord_jet (J : Type) (m : ℕ) (y : overAt x (Jet S J m) ⟶ t.G)
    (hy : homAt x (jetAug : Jet S J m →ₐ[S] S) ≫ y = 1) :
    ∃! χ : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S J m,
      (∀ q, (jetAug : Jet S J m →ₐ[S] S) (χ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) ∧ y = homAt x χ ≫ g.x m := by
  refine (existsUnique_congr fun χ => and_congr_left fun _ => ?_).1 (coord_aug g jetAug (ker_aug_pow J m) y hy)
  exact ⟨fun h q => (AlgHom.congr_fun h (z m q)).trans (jetAug_z m q),
    fun h => jext fun q => (h q).trans (jetAug_z m q).symm⟩

theorem aeval_inr {κ : Type} [Fintype κ] [DecidableEq κ] (c : κ → S) (P : MvPolynomial κ S) :
    MvPolynomial.aeval (fun s => (TrivSqZeroExt.inr (c s) : DualNumber S)) P =
      TrivSqZeroExt.inl (MvPolynomial.constantCoeff P) +
        TrivSqZeroExt.inr (∑ s, P.coeff (Finsupp.single s 1) * c s) := by
  induction P using MvPolynomial.induction_on with
  | C r =>
    have : ∀ s : κ, (MvPolynomial.C r : MvPolynomial κ S).coeff (Finsupp.single s 1) = 0 := fun s => by
      rw [MvPolynomial.coeff_C, if_neg (Finsupp.single_ne_zero.2 one_ne_zero).symm]
    simp [this, TrivSqZeroExt.algebraMap_eq_inl]
  | add p q hp hq =>
    rw [map_add (f := _), hp, hq]
    ext <;> simp [add_mul, Finset.sum_add_distrib]
  | mul_X p n hp =>
    have : ∀ s : κ, (p * MvPolynomial.X n).coeff (Finsupp.single s 1) =
        if s = n then MvPolynomial.constantCoeff p else 0 := fun s => by
      rw [MvPolynomial.coeff_mul_X']
      by_cases h : s = n
      · subst h; simp [MvPolynomial.constantCoeff_eq]
      · simp [h, Ne.symm h]
    rw [map_mul, hp, MvPolynomial.aeval_X]
    ext <;> simp [this, mul_comm]

theorem vec_subst (φ : Germ.Pt S 1 d) (c : Fin d → S) :
    ((jetVec c).comp (jOut S d 1)).comp (jetSubstP 1 fun p : Fin 1 × Fin d => psTrunc 1 (φ p.2)) =
      (jetVec ((lin φ 1).mulVec c)).comp (jOut S d 1) := by
  have hT : ∀ (c : Fin d → S) (P : MvPolynomial (Fin 1 × Fin d) S),
      ((jetVec c).comp (jOut S d 1)) (Ideal.Quotient.mk _ P) =
        MvPolynomial.aeval (fun s : Fin 1 × Fin d => (TrivSqZeroExt.inr (c s.2) : DualNumber S)) P := fun c P => by
    have : ((jetVec c).comp (jOut S d 1)).comp (Ideal.Quotient.mkₐ S _) =
        MvPolynomial.aeval (fun s : Fin 1 × Fin d => (TrivSqZeroExt.inr (c s.2) : DualNumber S)) :=
      MvPolynomial.algHom_ext fun s => by
        rw [MvPolynomial.aeval_X]
        refine Eq.trans ?_ (jetVec_z_one c s.2)
        exact congrArg (jetVec c) (jetMap_z (S := S) 1 (fun p : Fin 1 × Fin d => MvPolynomial.X p.2)
          (fun _ => X_mem_orig _) s)
    exact AlgHom.congr_fun this P
  refine jext fun p => ?_
  rw [AlgHom.comp_apply, jetSubstP, jetMap_z, hT, hT, map_sub, aeval_inr, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  have : ∀ s : Fin 1 × Fin d, (psTrunc 1 (φ p.2)).coeff (Finsupp.single s 1) =
      MvPowerSeries.coeff (Finsupp.single s 1) (φ p.2) := fun s => by
    rw [FBIdJet.psTrunc_eq, MvPowerSeries.coeff_truncTotal _ (by simp)]
  simp only [this, Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton]
  ext
  · simp [TrivSqZeroExt.algebraMap_eq_inl]
  · simp [lin, Matrix.mulVec, dotProduct, TrivSqZeroExt.algebraMap_eq_inl]

theorem tv_gd (c : Fin d → S) : tv (gd g c) = homAt x ((jetVec c).comp (jOut S d 1)) ≫ g.x 1 := by
  rw [← hcomp]; rfl

theorem gd_act (a : 𝓞 E) (c : Fin d → S) :
    tv (gd g c) ≫ t.act.act a = tv (gd g ((rho g.B a).mulVec c)) := by
  rw [tv_gd, tv_gd, Category.assoc, g.chart.act 1 a, hcomp, vec_subst]
  rfl

end Gen

theorem germ_univ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] [IsLocalRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d), (∀ (d₂ : ℕ) (_ : GermAt t x d₂), d = d₂) ∧ ∀ (J : Type) [Finite J] (m : ℕ) (y : overAt x (Jet S J m) ⟶ t.G), homAt x (jetAug : Jet S J m →ₐ[S] S) ≫ y = 1 → ∃! χ : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S J m, (∀ q, (jetAug : Jet S J m →ₐ[S] S) (χ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) ∧ y = homAt x χ ≫ g.x m := by
  intro E _ _ _ H _ _ X0 t S _ _ x d g
  refine ⟨fun d₂ g₂ => ?_, fun J _ m y hy => coord_jet g J m y hy⟩
  have e := ((LinearEquiv.ofBijective _ (gd_bij g)).trans (LinearEquiv.ofBijective _ (gd_bij g₂)).symm).finrank_eq
  simpa using e

theorem germ_lie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d) (V : Type) [AddCommGroup V] [Module S V] (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G x V), ∃ e : V ≃ₗ[S] (Fin d → S), (∀ v, IsCombAtG t x g.tg (e v) (M.pt v).left) ∧ ∀ r : 𝓞 E →+* Module.End S V, M.IsActOf t.act.act r → ∀ a v, e (r a v) = (rho g.B a).mulVec (e v) := by
  intro E _ _ _ H _ _ X0 t S _ x d g V _ _ M
  have ht : ∀ v, IsTanAtG t x (M.pt v).left := fun v => ⟨Over.w (M.pt v), M.tan v⟩
  let L : V →ₗ[S] TanM x t.G :=
    { toFun := fun v => mkT (ovT (ht v)) (smT_zero_ovT (ht v))
      map_add' := fun v w => tv_injective (M.add v w)
      map_smul' := fun c v => tv_injective (Over.OverMorphism.ext (M.smul c v)) }
  have hL : ∀ v, tv (L v) = M.pt v := fun v => rfl
  have hb : Function.Bijective L := by
    refine ⟨fun v w h => M.inj ((hL v).symm.trans ((congrArg tv h).trans (hL w))), fun W => ?_⟩
    obtain ⟨v, hv⟩ := M.onto (tv W) (isTanAtG_of _ (tv_zero' W)).2
    exact ⟨v, tv_injective hv⟩
  let e : V ≃ₗ[S] (Fin d → S) := (LinearEquiv.ofBijective L hb).trans (LinearEquiv.ofBijective _ (gd_bij g)).symm
  have he : ∀ v, gd g (e v) = L v := fun v => (LinearEquiv.ofBijective _ (gd_bij g)).apply_symm_apply _
  refine ⟨e, fun v => (comb_iff g _ _).2 (by rw [he, hL]), fun r hr a v => (gd_bij g).1 (tv_injective ?_)⟩
  rw [← gd_act, he, he, hL, hL]
  exact hr a v

end PositivityTheory.HtPt.Cd
end
end

