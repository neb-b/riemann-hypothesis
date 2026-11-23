module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvalOneStandardPointSelf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsRingHomValuationRingOfEmbOK
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem embOK_exists_ringHom :
    ∀ (T : CDVR) (C : Type) [Field C] [CharZero C] (V : VF C) (ι' : T.Fr →+* C), EmbOK T V ι' → ∃ j : T.V →+* V.RR, (∀ x, (j x : C) = ι' (algebraMap T.V T.Fr x)) ∧ ∀ x ∈ maximalIdeal T.V, V.MM (j x : C) := by
  intro T C _ _ V ι' h
  have hnn : ∀ a : T.V, 0 ≤ vV T.V (algebraMap T.V T.Fr a) := by
    intro a
    unfold vV
    by_cases ha : valV T.V (algebraMap T.V T.Fr a) = 0
    · simp [ha]
    have h1 : valV T.V (algebraMap T.V T.Fr a) ≤ 1 :=
      IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a
    have := (WithZero.log_le_log ha one_ne_zero).2 h1
    simp at this
    omega
  have hl0 : vV T.V ((V.l : ℕ) : T.Fr) ≠ 0 := by
    intro h0
    have hl : ((V.l : ℕ) : T.Fr) ≠ 0 := Nat.cast_ne_zero.2 V.l_prime.ne_zero
    have := h _ hl
    rw [map_natCast, V.v_l, h0] at this
    simp at this
  have hl : (0 : ℝ) < (vV T.V ((V.l : ℕ) : T.Fr) : ℝ) := by
    have h0 := hnn (V.l : T.V)
    rw [map_natCast] at h0
    exact_mod_cast lt_of_le_of_ne h0 hl0.symm
  have hR : ∀ x : T.V, (ι'.comp (algebraMap T.V T.Fr)) x ∈ V.RR := by
    intro x
    show V.Ge 0 (ι' (algebraMap T.V T.Fr x))
    by_cases h0 : algebraMap T.V T.Fr x = 0
    · rw [h0, map_zero]; exact VF.Ge.zero 0
    unfold VF.Ge
    rw [h _ h0]
    exact WithTop.coe_le_coe.2 (div_nonneg (by exact_mod_cast hnn x) hl.le)
  refine ⟨(ι'.comp (algebraMap T.V T.Fr)).codRestrict V.RR hR, fun x => rfl, fun x hx => ?_⟩
  have key : ((0 : ℝ) : WithTop ℝ) < V.v (ι' (algebraMap T.V T.Fr x)) := by
    by_cases h0 : algebraMap T.V T.Fr x = 0
    · rw [h0, map_zero, V.v.map_zero]; exact WithTop.coe_lt_top _
    rw [h _ h0]
    have h2 : valV T.V (algebraMap T.V T.Fr x) < 1 := by
      unfold valV
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
      exact hx
    have h3 := (WithZero.log_lt_log (valV_ne_zero h0) one_ne_zero).2 h2
    have h4 : 0 < vV T.V (algebraMap T.V T.Fr x) := by
      simp at h3
      unfold vV
      omega
    exact WithTop.coe_lt_coe.2 (div_pos (by exact_mod_cast h4) hl)
  exact key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTorusExtensionPointsPullbackFieldPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair

theorem exists_pullEquiv {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {f : S' ⟶ S} {t : SAB H S} {t' : SAB H S'} (m : SABMap t' t f) (n : ℕ) {Y : Scheme.{0}} (a : Y ⟶ S')
    (u : Y ⟶ S) (hu : a ≫ f = u) :
    ∃ e : (Over.mk u ⟶ t.G) ≃* (Over.mk a ⟶ t'.G), (∀ x, (e x).left ≫ m.cm.F = x.left) ∧
      ∀ x y, CubWeil t.cub n x y 1 → CubWeil t'.cub n (e x) (e y) 1 := by
  subst hu
  have hw : m.cm.F ≫ t.G.hom = t'.G.hom ≫ f := m.cart.1.w
  have mul : ∀ (T : Over S') (x y : T ⟶ t'.G), Out.toBase hw (x * y) = Out.toBase hw x * Out.toBase hw y :=
    fun T x y => Over.OverMorphism.ext (m.cart.2 T x y (Out.toBase hw x) (Out.toBase hw y) rfl rfl).symm
  let β : (Over.mk a ⟶ t'.G) →* (Over.mk (a ≫ f) ⟶ t.G) := GlobalTheory.UU.toBaseHom mul (Over.mk a)
  have hβ : Function.Bijective β := by
    refine ⟨fun x y e => Over.OverMorphism.ext
      (m.cart.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun x => ?_⟩
    exact ⟨Over.homMk (m.cart.1.lift x.left a (Over.w x)) (m.cart.1.lift_snd _ _ _),
      Over.OverMorphism.ext (m.cart.1.lift_fst _ _ _)⟩
  let e := (MulEquiv.ofBijective β hβ).symm
  have he : ∀ x, β (e x) = x := fun x => (MulEquiv.ofBijective β hβ).apply_symm_apply x
  refine ⟨e, fun x => congrArg (fun q => q.left) (he x), fun x y h => ?_⟩
  obtain ⟨ζ, hζ, -⟩ := GlobalTheory.UU.existsUnique_cubWeil t'.cub (N := n) (x := e x) (y := e y)
    (by rw [← map_pow, h.1, map_one]) (by rw [← map_pow, h.2.1, map_one])
  have h' : CubWeil t.cub n (β (e x)) (β (e y)) ζ :=
    GlobalTheory.UU.cubWeil_of_isPullCubical S S' f t.G t'.G m.cm hw mul _ _ t.cub t'.cub m.lin n _ _ _ ζ hζ
  rw [he, he] at h'
  obtain rfl : ζ = 1 := h'.unique h
  exact hζ

theorem exists_isTorExt_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (f : S' ⟶ S) (t : SAB H S) (t' : SAB H S') (_ : SABMap t' t f) (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (s' : Sp Ω ⟶ S'), s' ≫ f = s → ∀ n : ℕ, ∃ (τ : PtHom s s' t.G t'.G) (io : TorHom s t.G PUnit), IsTorExt s s' t.G t'.G PUnit τ io ∧ Transfer n t.cub t'.cub τ := by
  intro E _ _ _ H S S' f t t' m Ω _ s s' hs n
  have key : ∀ (A : Type) [CommRing A] [Algebra Ω A], ∃ e : (overAt s A ⟶ t.G) ≃* (overAt s' A ⟶ t'.G),
      (∀ x, (e x).left ≫ m.cm.F = x.left) ∧ ∀ x y, CubWeil t.cub n x y 1 → CubWeil t'.cub n (e x) (e y) 1 :=
    fun A _ _ => exists_pullEquiv m n _ _ (by rw [Category.assoc, hs])
  choose e he hc using key
  have nat : ∀ (A A' : Type) [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A'] (g : A →ₐ[Ω] A')
      (x : overAt s A ⟶ t.G), e A' (homAt s g ≫ x) = homAt s' g ≫ e A x := by
    intro A A' _ _ _ _ g x
    refine Over.OverMorphism.ext (m.cart.1.hom_ext ?_ (by rw [Over.w, Over.w]))
    rw [he, Over.comp_left, Over.comp_left, Category.assoc, he]
    rfl
  refine ⟨fun A _ _ => (e A).toMonoidHom, fun A _ _ => 1, ⟨nat, ?_, ?_, ?_, ?_⟩, fun A _ _ => hc A⟩
  · intro A A' _ _ _ _ g χ
    exact (MonObj.comp_one _).symm
  · intro A _ _ χ χ' _
    exact MonoidHom.ext fun x => by rw [Subsingleton.elim x 1, map_one, map_one]
  · intro A _ _ x
    exact (e A).map_eq_one_iff.trans ⟨fun h => ⟨1, h.symm⟩, fun ⟨_, h⟩ => h.symm⟩
  · intro A _ _ π _ y hy
    refine ⟨(e A).symm y, (e Ω).map_eq_one_iff.1 ?_, (e A).apply_symm_apply y⟩
    rw [nat, (e A).apply_symm_apply, hy]

end GlobalTheory.AlphaPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JetRingHomExistsUniqueSpec
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair.JetEv

theorem prod_pow_mem_span_pow {A κ : Type} [CommRing A] [Fintype κ] (a : κ → A) (e : κ → ℕ) :
    ∏ i, a i ^ e i ∈ Ideal.span (Set.range a) ^ (∑ i, e i) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _

theorem jet_hom_spec : ∀ (V Ω A : Type) [CommRing V] [CommRing Ω] [CommRing A] [Algebra Ω A] (β : V →+* Ω) (κ : Type) [Fintype κ] [DecidableEq κ] (m : ℕ), (∀ a : κ → A, Ideal.span (Set.range a) ^ (m + 1) = ⊥ → ∃! ψ : Jet V κ m →+* A, (∀ v : V, ψ (algebraMap V _ v) = algebraMap Ω A (β v)) ∧ ∀ i, ψ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = a i) ∧ ∀ ψ : Jet V κ m →+* A, (∀ v : V, ψ (algebraMap V _ v) = algebraMap Ω A (β v)) → Ideal.span (Set.range fun i => ψ (Ideal.Quotient.mk _ (MvPolynomial.X i))) ^ (m + 1) = ⊥ ∧ (∀ i, IsNilpotent (ψ (Ideal.Quotient.mk _ (MvPolynomial.X i)))) ∧ ∀ f : MvPowerSeries κ V, ψ (psJet m f) = nEval (MvPowerSeries.map β f) (fun i => ψ (Ideal.Quotient.mk _ (MvPolynomial.X i))) := by
  intro V Ω A _ _ _ _ β κ _ _ m
  refine ⟨fun a ha => ?_, fun ψ hψ => ?_⟩
  · letI : Algebra V A := ((algebraMap Ω A).comp β).toAlgebra
    let φ : Jet V κ m →ₐ[V] A := liftJet (MvPolynomial.aeval a) (by simpa using ha)
    have hφ : ∀ i, φ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = a i := fun i =>
      MvPolynomial.aeval_X a i
    refine ⟨(φ : Jet V κ m →+* A), ⟨fun v => φ.commutes v, hφ⟩, ?_⟩
    rintro ψ ⟨h1, h2⟩
    refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun v => ?_) fun i => ?_)
    · exact (h1 v).trans (φ.commutes v).symm
    · exact (h2 i).trans (hφ i).symm
  · set a : κ → A := fun i => ψ (Ideal.Quotient.mk _ (MvPolynomial.X i)) with ha
    have h0 : Ideal.span (Set.range a) ^ (m + 1) = ⊥ := by
      have := map_orig_pow (ψ.comp (Ideal.Quotient.mk (orig V κ ^ (m + 1)))) (m + 1)
      rw [← Ideal.map_map, Ideal.map_quotient_self, Ideal.map_bot] at this
      exact this.symm
    have h1 : ∀ i, a i ^ (m + 1) = 0 := fun i => by
      have := Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i) : a i ∈ Ideal.span (Set.range a)) (m + 1)
      rwa [h0, Ideal.mem_bot] at this
    refine ⟨h0, fun i => ⟨m + 1, h1 i⟩, fun f => ?_⟩
    have hm : ∀ (e : κ →₀ ℕ) (c : V), ψ (Ideal.Quotient.mk _ (MvPolynomial.monomial e c)) =
        algebraMap Ω A (β c) * ∏ i, a i ^ e i := fun e c => by
      rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), ← hψ]
      simp only [map_mul, map_prod, map_pow]
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [GlobalTheory.evBasic_nEval_eq_tEval _ a (m + 1) h1, psJet, psTrunc, map_sum, map_sum]
    simp only [hm]
    rw [degLE, Finset.sum_filter, Finset.sum_image, ReciprocityTheory.PGsh.Be2.tEval]
    · refine Finset.sum_congr rfl fun e _ => ?_
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), MvPowerSeries.coeff_map]
      split_ifs with h
      · rfl
      · have h2 := prod_pow_mem_span_pow a fun i => (e i : ℕ)
        have h3 : m + 1 ≤ ∑ i, (e i : ℕ) := Nat.lt_of_not_le h
        have h4 := Ideal.pow_le_pow_right h3 h2
        rw [h0, Ideal.mem_bot] at h4
        rw [h4, mul_zero]
    · intro e _ e' _ h
      funext i
      exact Fin.ext (congrFun (Finsupp.equivFunOnFinite.symm.injective h) i)

end GlobalTheory.AlphaPair.JetEv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.UniversalChartPointsOverFieldPoint
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair.JetUniv

open GlobalTheory.ChartBaseChange (fib fibLift fibFst fibSnd fib_cond fib_ker exists_pt_of_aug pt_eps_self)

def unitSec {S : Scheme.{0}} (G : Over S) [GrpObj G] : S ⟶ G.left := (η[G]).left

def lft {S T : Scheme.{0}} {G : Over S} {f : T ⟶ S} (y : Over.mk f ⟶ G) : T ⟶ G.left := y.left

theorem lft_w {S T : Scheme.{0}} {G : Over S} {f : T ⟶ S} (y : Over.mk f ⟶ G) : lft y ≫ G.hom = f := Over.w y

theorem lft_inj {S T : Scheme.{0}} {G : Over S} {f : T ⟶ S} {y z : Over.mk f ⟶ G} (h : lft y = lft z) : y = z :=
  Over.OverMorphism.ext h

theorem unitSec_w {S : Scheme.{0}} (G : Over S) [GrpObj G] : unitSec G ≫ G.hom = 𝟙 S := Over.w (η[G])

theorem eq_one_iff {S T : Scheme.{0}} {G : Over S} [GrpObj G] {f : T ⟶ S} (y : Over.mk f ⟶ G) :
    y = 1 ↔ lft y = f ≫ unitSec G := by
  have e : lft (1 : Over.mk f ⟶ G) = f ≫ unitSec G := by
    show (toUnit (Over.mk f) ≫ η[G]).left = _
    rw [Over.comp_left, Over.toUnit_left]
    rfl
  exact ⟨fun h => h ▸ e, fun h => lft_inj (h.trans e.symm)⟩

variable {V : Type} [CommRing V] {G : Over (Sp V)} [GrpObj G] {κ : Type}

theorem aug_X (m : ℕ) (i : κ) :
    (jetAug : Jet V κ m →ₐ[V] V) (Ideal.Quotient.mk _ (MvPolynomial.X i)) = 0 := by
  show MvPolynomial.aeval (fun _ : κ => (0 : V)) (MvPolynomial.X i) = 0
  simp

theorem ker_aug_pow (m : ℕ) : RingHom.ker (jetAug : Jet V κ m →ₐ[V] V) ^ (m + 1) = ⊥ := by
  have hle : RingHom.ker (jetAug : Jet V κ m →ₐ[V] V) ≤ (orig V κ).map (Ideal.Quotient.mk _) := fun z hz => by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    have h0 : MvPolynomial.aeval (fun _ : κ => (0 : V)) p = 0 := hz
    have h1 : MvPolynomial.constantCoeff p = 0 := by simpa using h0
    have h2 := sub_const_mem_orig p
    rw [h1, map_zero, sub_zero] at h2
    exact Ideal.mem_map_of_mem _ h2
  rw [eq_bot_iff]
  refine (Ideal.pow_right_mono hle _).trans ?_
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

def toSp {A : Type} [CommRing A] [Algebra V A] (y : overAt (𝟙 (Sp V)) A ⟶ G) : Chart.sp (R₀ := V) A ⟶ G :=
  Over.homMk y.left ((Over.w y).trans (Category.comp_id _))

def ofSp {A : Type} [CommRing A] [Algebra V A] (y : Chart.sp (R₀ := V) A ⟶ G) : overAt (𝟙 (Sp V)) A ⟶ G :=
  Over.homMk y.left ((Over.w y).trans (Category.comp_id _).symm)

theorem one_at_iff {A B : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] (f : A →ₐ[V] B)
    (y : overAt (𝟙 (Sp V)) A ⟶ G) : homAt (𝟙 (Sp V)) f ≫ y = 1 ↔ Chart.spMap f ≫ toSp y = 1 := by
  rw [eq_one_iff, eq_one_iff]
  have e : (spMap (algebraMap V B) ≫ 𝟙 (Sp V)) ≫ unitSec G = spMap (algebraMap V B) ≫ unitSec G := by
    rw [Category.comp_id]
  rw [e]
  rfl

theorem univ_over [IsLocalRing V] {x : GlobalTheory.PowGerm.JetPts G κ} (hx : GlobalTheory.PowGerm.IsUnivJ G κ x)
    {A Ω : Type} [CommRing A] [Algebra V A] [CommRing Ω] [Algebra V Ω] (q : A →ₐ[V] Ω) (hq : Function.Surjective q)
    {m : ℕ} (hJ : RingHom.ker q ^ (m + 1) = ⊥) (y : Chart.sp (R₀ := V) A ⟶ G) (hy : Chart.spMap q ≫ y = 1) :
    ∃! ψ : Jet V κ m →ₐ[V] A, (∀ i, q (ψ (Ideal.Quotient.mk _ (MvPolynomial.X i))) = 0) ∧
      y.left = spMap (ψ : Jet V κ m →+* A) ≫ (x m).left := by
  obtain ⟨C⟩ := Chart.exists_chart G
  obtain ⟨h, hh, hqh⟩ := exists_pt_of_aug C q hq hJ y hy
  obtain ⟨k, hk, hqk⟩ := exists_pt_of_aug C (jetAug : Jet V κ m →ₐ[V] V)
    (fun r => ⟨algebraMap _ _ r, AlgHom.commutes _ r⟩) (ker_aug_pow m) (toSp (x m)) ((one_at_iff _ _).1 (hx.2.1 m))
  have hk' : (x m).left = (Chart.pt C k).left := congrArg CommaMorphism.left hk
  have mv : ∀ {B : Type} [CommRing B] [Algebra V B] (v : Jet V κ m →ₐ[V] B),
      spMap (v : Jet V κ m →+* B) ≫ (x m).left = (Chart.pt C (v.comp k)).left := by
    intro B _ _ v
    rw [hk', ← Chart.spMap_pt]
    rfl
  let h₀ := fibLift q (Chart.eps C) h hqh
  obtain ⟨ψ₀, ⟨ha, hψ₀⟩, hu⟩ := hx.2.2 (fib q) (fibFst q) m (fib_ker q hJ) (ofSp (Chart.pt C h₀)) (by
    rw [one_at_iff]
    show Chart.spMap _ ≫ Chart.pt C h₀ = 1
    rw [Chart.spMap_pt]
    exact pt_eps_self C)
  have h0 : h₀ = ψ₀.comp k :=
    Chart.pt_injective C (Over.OverMorphism.ext ((congrArg CommaMorphism.left hψ₀).trans (mv ψ₀)))
  refine ⟨(fibSnd q).comp ψ₀, ⟨fun i => ?_, ?_⟩, ?_⟩
  · rw [AlgHom.comp_apply, fib_cond, ← AlgHom.comp_apply (fibFst q), ha, aug_X, map_zero]
  · rw [mv, AlgHom.comp_assoc, ← h0, hh]
    rfl
  · rintro v ⟨hv0, hv1⟩
    have hv : q.comp v = (Algebra.ofId V Ω).comp jetAug :=
      Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jet_hom_ext fun i => by
        rw [AlgHom.comp_apply, AlgHom.comp_apply, hv0, aug_X, map_zero]
    have hvk : h = v.comp k :=
      Chart.pt_injective C (Over.OverMorphism.ext ((congrArg CommaMorphism.left hh).symm.trans (hv1.trans (mv v))))
    have e := hu (fibLift q jetAug v hv) ⟨rfl, Over.OverMorphism.ext (by
      refine Eq.trans ?_ (mv _).symm
      show (Chart.pt C h₀).left = _
      congr 2
      refine AlgHom.ext fun s => Subtype.ext (Prod.ext ?_ ?_)
      · exact (AlgHom.congr_fun hqk s).symm
      · exact AlgHom.congr_fun hvk s)⟩
    rw [← e]
    rfl

theorem univ_left [IsLocalRing V] {x : GlobalTheory.PowGerm.JetPts G κ} (hx : GlobalTheory.PowGerm.IsUnivJ G κ x)
    {A Ω : Type} [CommRing A] [Algebra V A] [CommRing Ω] [Algebra V Ω] (q : A →ₐ[V] Ω) (hq : Function.Surjective q)
    {m : ℕ} (hJ : RingHom.ker q ^ (m + 1) = ⊥) (y : Sp A ⟶ G.left) (hw : y ≫ G.hom = spMap (algebraMap V A))
    (hy : spMap (q : A →+* Ω) ≫ y = spMap (algebraMap V Ω) ≫ unitSec G) :
    ∃! ψ : Jet V κ m →ₐ[V] A, (∀ i, q (ψ (Ideal.Quotient.mk _ (MvPolynomial.X i))) = 0) ∧
      y = spMap (ψ : Jet V κ m →+* A) ≫ lft (x m) :=
  univ_over hx q hq hJ (Over.homMk y hw) ((eq_one_iff _).2 hy)

theorem aug_left {x : GlobalTheory.PowGerm.JetPts G κ} (hx : GlobalTheory.PowGerm.IsUnivJ G κ x) (A : Type) [CommRing A] [Algebra V A]
    (m : ℕ) : spMap (algebraMap V A) ≫ unitSec G =
      spMap (((Algebra.ofId V A).comp jetAug : Jet V κ m →ₐ[V] A) : Jet V κ m →+* A) ≫ lft (x m) := by
  have h2 : Chart.spMap ((Algebra.ofId V A).comp jetAug) ≫ toSp (x m) = 1 := by
    rw [← Chart.spMap_comp, Category.assoc, (one_at_iff _ _).1 (hx.2.1 m), MonObj.comp_one]
  exact ((eq_one_iff _).1 h2).symm

section Field

variable {Ω : Type} [Field Ω] [Algebra V Ω] {A : Type} [CommRing A] [Algebra Ω A] [Algebra V A] [IsScalarTower V Ω A]

theorem hom_eq : spMap (algebraMap Ω A) ≫ spMap (algebraMap V Ω) = spMap (algebraMap V A) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

theorem exists_jetHom {B : Type} [CommRing B] [Algebra V B] {m : ℕ} {I : Ideal B} (hI : I ^ (m + 1) = ⊥) (a : κ → B)
    (ha : ∀ i, a i ∈ I) : ∃ ψ : Jet V κ m →ₐ[V] B, ∀ i, ψ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = a i :=
  ⟨liftJet (MvPolynomial.aeval a) (by
      rw [eq_bot_iff, ← hI]
      refine Ideal.pow_right_mono (Ideal.span_le.2 ?_) _
      rintro _ ⟨i, rfl⟩
      simpa using ha i), fun i => MvPolynomial.aeval_X a i⟩

theorem universalJetCoordinates_points_over_field [IsLocalRing V] {d : ℕ} {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G}
    (hx : GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x) {P : PtFam (spMap (algebraMap V Ω)) G d}
    (hP : IsJetPt (algebraMap V Ω) x P) (π : A →ₐ[Ω] Ω) (hπ : IsNilpotent (RingHom.ker π)) :
    (∀ a : Fin d → A, (∀ j, IsNilpotent (a j)) → P A a = 1 → a = 0) ∧
    ∀ z : overAt (spMap (algebraMap V Ω)) A ⟶ G, homAt _ π ≫ z = 1 →
      ∃ a : Fin d → A, (∀ j, IsNilpotent (a j)) ∧ P A a = z := by
  have hq : Function.Surjective (π.restrictScalars V) := fun r => ⟨algebraMap Ω A r, π.commutes r⟩
  obtain ⟨m, hm⟩ := hπ
  have hJ : RingHom.ker (π.restrictScalars V) ^ (m + 1) = ⊥ := by
    show RingHom.ker π ^ (m + 1) = ⊥
    rw [pow_succ, hm, zero_mul]
    rfl
  have hP' : ∀ ψ : Jet V (Fin 1 × Fin d) m →ₐ[V] A,
      lft (P A fun j => ψ (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j)))) =
        spMap (ψ : Jet V (Fin 1 × Fin d) m →+* A) ≫ lft (x m) := fun ψ =>
    hP A m (ψ : Jet V (Fin 1 × Fin d) m →+* A) fun v =>
      (ψ.commutes v).trans (IsScalarTower.algebraMap_apply V Ω A v)
  refine ⟨fun a ha h1 => ?_, fun z hz => ?_⟩
  · have ha0 : ∀ j, π.restrictScalars V (a j) = 0 := fun j => ((ha j).map (π.restrictScalars V)).eq_zero
    obtain ⟨ψ, hψ⟩ := exists_jetHom (V := V) hJ (fun p : Fin 1 × Fin d => a p.2) fun p => ha0 p.2
    have hl := hP' ψ
    rw [show (fun j => ψ (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j)))) = a from funext fun j => hψ _,
      (eq_one_iff _).1 h1, hom_eq] at hl
    have e := (univ_left hx _ hq hJ (spMap (algebraMap V A) ≫ unitSec G)
      (by rw [Category.assoc, unitSec_w, Category.comp_id])
      (by rw [← Category.assoc, spMap_comp_alg])).unique (y₁ := ψ)
      (y₂ := (Algebra.ofId V A).comp jetAug) ⟨fun i => by rw [hψ, ha0], hl⟩
      ⟨fun i => by rw [AlgHom.comp_apply, aug_X, map_zero, map_zero], aug_left hx A m⟩
    funext j
    have h3 := hψ (0, j)
    rw [e, AlgHom.comp_apply, aug_X, map_zero] at h3
    exact h3.symm
  · obtain ⟨ψ, ⟨h0, h1⟩, -⟩ := univ_left hx _ hq hJ (lft z) ((lft_w z).trans hom_eq) (by
      have h3 : spMap (π : A →+* Ω) ≫ lft z = _ := (eq_one_iff _).1 hz
      rw [hom_eq (A := Ω)] at h3
      exact h3)
    refine ⟨fun j => ψ (Ideal.Quotient.mk _ (MvPolynomial.X (0, j))), fun j => ⟨m + 1, ?_⟩,
      lft_inj ((hP' ψ).trans h1.symm)⟩
    have := Ideal.pow_mem_pow (RingHom.mem_ker.2 (h0 (0, j))) (m + 1)
    rwa [hJ, Ideal.mem_bot] at this

end Field

end GlobalTheory.AlphaPair.JetUniv

namespace GlobalTheory.AlphaPair

theorem jetUniv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G), GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → ∀ (Ω : Type) [Field Ω] (β : V →+* Ω) (P : PtFam (spMap β) t.G d), IsJetPt β x P → IsPtUniv (spMap β) t.G P := by
  intro E _ _ _ H V _ _ t d x hx Ω _ β P hP A _ _ π hπ
  letI : Algebra V Ω := β.toAlgebra
  letI : Algebra V A := ((algebraMap Ω A).comp β).toAlgebra
  haveI : IsScalarTower V Ω A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact JetUniv.universalJetCoordinates_points_over_field hx hP π hπ

end GlobalTheory.AlphaPair
end
end

