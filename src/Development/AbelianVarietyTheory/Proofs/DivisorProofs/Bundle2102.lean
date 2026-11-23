module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1884
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1998

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogRatioUpperBound
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.MeasUp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem le_exp_of_log_le {y L : ℝ} (hy : 0 ≤ y) (h : Real.log y ≤ L) : y ≤ Real.exp L := by
  rcases hy.eq_or_lt with h0 | h0
  · rw [← h0]; exact (Real.exp_pos L).le
  · exact (Real.log_le_iff_le_exp h0).1 h

theorem kapQ_inl (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) {p q : ℕ} (hp : p = D.R.k + i)
    (hq : q = D.R.m - ((i : ℕ) + 1)) (a : Fin p) :
    Formalism.L2.NTheta.kapQ (D.hc t) p q (Sum.inl a) + (D.hc t).e i = GlobalTheory.CovTop.WtShape.ent D i t a := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hi := i.2
  have ha := a.2
  have e0 : Formalism.L2.NTheta.lamAt (D.hc t) a = DV.sigPar D t a := rfl
  unfold Formalism.L2.NTheta.kapQ GlobalTheory.CovTop.WtShape.ent
  simp only [Sum.elim_inl]
  rw [if_pos (by omega), e0]
  subst hp hq
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  rw [hr, Nat.cast_sub (by omega : 1 ≤ D.R.k + D.R.m), Nat.cast_sub (by omega : (i : ℕ) + 1 ≤ D.R.m)]
  push_cast
  ring

theorem kapQ_inr (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) {p q : ℕ} (hp : p = D.R.k + i)
    (hq : q = D.R.m - ((i : ℕ) + 1)) (c : Fin q) :
    Formalism.L2.NTheta.kapQ (D.hc t) p q (Sum.inr c) + (D.hc t).e i = GlobalTheory.CovTop.WtShape.ent D i t (p + c) := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hi := i.2
  have hc := c.2
  have e0 : Formalism.L2.NTheta.lamAt (D.hc t) (p + c) = DV.sigPar D t (p + c) := rfl
  unfold Formalism.L2.NTheta.kapQ GlobalTheory.CovTop.WtShape.ent
  simp only [Sum.elim_inr]
  rw [if_neg (by omega), e0]
  subst hp hq
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  rw [hr, Nat.cast_sub (by omega : 1 ≤ D.R.k + D.R.m), Nat.cast_sub (by omega : (i : ℕ) + 1 ≤ D.R.m)]
  push_cast
  ring

theorem abs_wt_le (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) {p q : ℕ} (hp : p = D.R.k + i)
    (hq : q = D.R.m - ((i : ℕ) + 1)) {B : ℝ}
    (hB : ∀ n, n < D.R.r → |((GlobalTheory.CovTop.WtShape.ent D i t n : ℚ) : ℝ)| ≤ B) (a : Fin p ⊕ Fin q) :
    |((Formalism.L2.NTheta.kapW (D.hc t) p q a : ℤ) : ℝ) + (((D.hc t).e i : ℚ) : ℝ)| ≤ B + 1 := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hi := i.2
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  obtain ⟨n, hn, hx⟩ : ∃ n, n < D.R.r ∧
      Formalism.L2.NTheta.kapQ (D.hc t) p q a + (D.hc t).e i = GlobalTheory.CovTop.WtShape.ent D i t n := by
    cases a with
    | inl a => exact ⟨a, by have := a.2; omega, kapQ_inl D i t hp hq a⟩
    | inr c => exact ⟨p + c, by have := c.2; omega, kapQ_inr D i t hp hq c⟩
  have h1 : ((Formalism.L2.NTheta.kapW (D.hc t) p q a : ℤ) : ℝ) ≤ (Formalism.L2.NTheta.kapQ (D.hc t) p q a : ℝ) := by
    unfold Formalism.L2.NTheta.kapW
    exact_mod_cast Int.floor_le _
  have h2 : (Formalism.L2.NTheta.kapQ (D.hc t) p q a : ℝ) < ((Formalism.L2.NTheta.kapW (D.hc t) p q a : ℤ) : ℝ) + 1 := by
    have h := Int.lt_floor_add_one (Formalism.L2.NTheta.kapQ (D.hc t) p q a)
    have h' : ((Formalism.L2.NTheta.kapQ (D.hc t) p q a : ℚ) : ℝ) <
        (((⌊Formalism.L2.NTheta.kapQ (D.hc t) p q a⌋ : ℤ) : ℚ) : ℝ) + 1 := by
      have := (Rat.cast_lt (K := ℝ)).2 h
      rw [Rat.cast_add, Rat.cast_one] at this
      exact this
    rw [Rat.cast_intCast] at h'
    exact h'
  have h3 : (Formalism.L2.NTheta.kapQ (D.hc t) p q a : ℝ) + (((D.hc t).e i : ℚ) : ℝ) =
      ((GlobalTheory.CovTop.WtShape.ent D i t n : ℚ) : ℝ) := by
    rw [← hx]; push_cast; ring
  obtain ⟨b1, b2⟩ := abs_le.1 (hB n hn)
  rw [abs_le]
  constructor <;> linarith

theorem wtSize_le (D : D7) (i : Fin D.R.m) {B : ℝ}
    (hB : ∀ t n, n < D.R.r → |((GlobalTheory.CovTop.WtShape.ent D i t n : ℚ) : ℝ)| ≤ B) :
    GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize D i ≤ D.R.f * D.R.r * (B + 1) := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hi := i.2
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize
  calc _ ≤ ∑ _τ : D.what₂.Tau, (D.R.r : ℝ) * (B + 1) := Finset.sum_le_sum fun τ _ => ?_
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul]; ring
  have hs : (Wc D i).sig (TH.tauE D τ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _
  have s1 : ((Wc D i).sig (TH.tauE D τ)).1 = D.R.k + i := by rw [hs]; rfl
  have s2 : ((Wc D i).sig (TH.tauE D τ)).2 = D.R.m - ((i : ℕ) + 1) := by rw [hs]; rfl
  calc _ ≤ ∑ _a : Fin ((Wc D i).sig (TH.tauE D τ)).1 ⊕ Fin ((Wc D i).sig (TH.tauE D τ)).2, (B + 1) :=
        Finset.sum_le_sum fun a _ => abs_wt_le D i τ s1 s2 (hB τ) a
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, s1, s2]
      congr 1
      rw [hr]; push_cast [show (i : ℕ) + 1 ≤ D.R.m by omega, show 1 ≤ D.R.k + D.R.m by omega]; ring

end GlobalTheory.CovTop.MeasUp

namespace GlobalTheory.CovTop.MeasUp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem abs_ent_le {PP : ℝ} (hW : WtNum p i PP) (t : D.what₂.Tau) (n : ℕ) (hn : n < D.R.r) :
    |((GlobalTheory.CovTop.WtShape.ent D i t n : ℚ) : ℝ)| ≤ 4 * L.sc.b := by
  have hp := p.fw.laws.pins.1
  let τ : Psi p.T.Q.H := ⟨DV.tauEmb D t, hp.2.2.2 t⟩
  let k : Fin ((dat p i).p + (dat p i).q) := ⟨n, by rw [GlobalTheory.CovTop.WtShape.dat_rank p i]; exact hn⟩
  have e := GlobalTheory.CovTop.WtShape.laOf_read p i τ t rfl k
  have h := hW.up τ k
  rw [← e, Rat.cast_intCast]
  exact h

theorem sizes_two {PP A PP' : ℝ} (P : ParameterChoice' D L) (hH : HostNum D L PP A 2) (hW : ∀ j, WtNum p j PP') :
    GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D (2 * L.sc.L) := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; omega
  have hrR : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr1
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
  have hnV : (0 : ℝ) ≤ D.R.nV := Nat.cast_nonneg _
  obtain ⟨hL10, -⟩ := hH.big.2
  obtain ⟨hlfr, hlnV⟩ := hH.logfr
  set Lc := L.sc.L with hLc
  have hb : L.sc.b = Real.exp Lc := rfl
  have hfr : (D.R.f : ℝ) * D.R.r ≤ Real.exp Lc := le_exp_of_log_le (by positivity) hlfr
  have hnVe : (D.R.nV : ℝ) ≤ Real.exp Lc := le_exp_of_log_le hnV hlnV
  have hE0 : 0 < Real.exp Lc := Real.exp_pos _
  have hE1 : Lc + 1 ≤ Real.exp Lc := Real.add_one_le_exp _
  have e2 : Real.exp (2 * Lc) = Real.exp Lc * Real.exp Lc := by rw [two_mul, Real.exp_add]
  refine ⟨?_, fun j => ?_, ?_, ?_⟩
  · rw [e2]
    exact mul_le_mul hfr hnVe hnV hE0.le
  · have hw := wtSize_le D j (abs_ent_le p j (hW j))
    rw [e2, ← hb]
    rw [← hb] at hE1 hfr
    have h1 : (D.R.f : ℝ) * D.R.r * (4 * L.sc.b + 1) ≤ L.sc.b * (5 * L.sc.b) :=
      mul_le_mul hfr (by linarith) (by linarith) (by linarith)
    have h5 : 5 ≤ L.sc.b * L.sc.b := by nlinarith
    have h6 : L.sc.b * (5 * L.sc.b) ≤ (L.sc.b * L.sc.b) ^ 2 := by nlinarith
    linarith
  · have g0 : (0 : ℝ) < (D.host.g 0 : ℝ) := by exact_mod_cast (D.host.g_prime 0).pos
    have g1 : (0 : ℝ) < (D.host.g 1 : ℝ) := by exact_mod_cast (D.host.g_prime 1).pos
    rw [Real.log_mul g0.ne' g1.ne']
    linarith [hH.logg 0, hH.logg 1]
  · have h1 := Formalism.BasicNotions.log_rdE_le_scL P
    have h2 : |dlogL D 1| ≤ Lc := by
      rw [← L.logDerivative_at_one_eq]; exact P.logDerivative_le_power
    linarith

theorem ratAt_pos_le (hOM : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.OneMeasure D) {PP A PP' : ℝ} (P : ParameterChoice' D L)
    (hH : HostNum D L PP A 2) (hW : ∀ j, WtNum p j PP') :
    0 < ratAt p i ∧ Real.log (ratAt p i) ≤ 244 * unitE p := by
  obtain ⟨-, hd, h2⟩ := hOM D _ p.R.toLevCh _ p.charW.base.lev i p.R.triv
  obtain ⟨h0, ht, -, hb⟩ := h2 _ _ (p.charW.base.models.νW i)
  have hr : 0 < ratAt p i :=
    mul_pos (ENNReal.toReal_pos h0 ht) (Finset.prod_pos fun τ _ => zero_lt_one.trans_le (hd τ))
  refine ⟨hr, ?_⟩
  have hB := (hb _ (sizes_two p P hH hW)).2.2
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; omega
  have hrR : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr1
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
  have hmR : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have hnV1 : (1 : ℝ) ≤ D.R.nV := by
    have : 1 ≤ D.R.nV := by unfold Ranks.nV; omega
    exact_mod_cast this
  obtain ⟨-, hL10, -, hll⟩ := hH.big
  obtain ⟨-, -, hpoly⟩ := hH.poly
  have hroom := hH.room
  rw [Real.rpow_two] at hroom

  have hr_le : (D.R.r : ℝ) ≤ L.sc.x ^ A := by
    refine le_trans ?_ hpoly
    have a1 : (D.R.r : ℝ) ≤ (D.R.f : ℝ) * D.R.r := le_mul_of_one_le_left (by linarith) (by linarith)
    have a2 : (D.R.f : ℝ) * D.R.r ≤ (D.R.f : ℝ) * D.R.r * D.R.nV := le_mul_of_one_le_right (by positivity) hnV1
    have a3 : (D.R.f : ℝ) * D.R.r * D.R.nV ≤ (D.R.f : ℝ) * D.R.r * D.R.nV * L.sc.L :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    linarith
  have hr2 : (D.R.r : ℝ) ^ 2 ≤ L.sc.b := (pow_le_pow_left₀ (by linarith) hr_le 2).trans hroom
  have hu : unitE p = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) := (hW i).unit
  rw [hu]
  have hL0 : 0 ≤ L.sc.L := by linarith
  have hfL : 0 ≤ (D.R.f : ℝ) * L.sc.L := by positivity
  have c1 : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L.sc.L ≤ (D.R.f : ℝ) * L.sc.b * L.sc.L := by
    have := mul_le_mul_of_nonneg_left hr2 hfL
    nlinarith
  have hb1 : 0 ≤ (D.R.f : ℝ) * L.sc.b * L.sc.L := by
    have : 0 < L.sc.b := Real.exp_pos _
    positivity
  have c2 : (D.R.f : ℝ) * L.sc.b * L.sc.L ≤ (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) := by
    have h1 : (1 : ℝ) ≤ D.R.m * Real.log (Real.log L.sc.x) := by nlinarith
    have := mul_le_mul_of_nonneg_left h1 hb1
    nlinarith
  have e3 : (122 : ℝ) * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (2 * L.sc.L)) = 244 * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L.sc.L) := by
    ring
  have e4 : ratAt p i = GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio D i (p.R.νW i) (p.R.fdW i) := rfl
  rw [e4]
  linarith

end GlobalTheory.CovTop.MeasUp

namespace GlobalTheory.CovTop.MeasRd

end GlobalTheory.CovTop.MeasRd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLiftSystemFiltrationSupIffHodgeFiltration
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

namespace Sys

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {X₀ : Scheme.{0}} {π : R →+* R₀}
  {s₀ : X₀ ⟶ Sp R₀}

def viaDR (hI : I ^ 2 = 0) (hk : RingHom.ker π = I) (s₀ : X₀ ⟶ Sp R₀) :
    CoefMap (((RingHom.id R₀).comp (RingHom.id R₀)).comp π) (O (divided₂ hI) (s₀ ≫ spMap π)) (OAff s₀) :=
  ((redMor hI hk s₀).coef.comp (CoefMap.restrict (O (dp0 R₀) s₀) (IsTriv s₀).ι)).comp
    (ptCoef (F := OAff s₀) (fun U ↦ affPt s₀ U.unop) (fun U ↦ affPt_w s₀ U.unop)
      fun _ _ a ↦ affPt_res s₀ (leOfHom a.unop))

variable (S : Sys I π s₀) (hI : I ^ 2 = 0) (hk : RingHom.ker π = I)

def redTrans : ((S.coef hI).comp S.redO).G ⟶ (viaDR hI hk s₀).G where
  app U :=
    { φ := { (S.p U : S.F.obj U →+* Sec s₀ U.unop.1) with
        commutes' := fun r ↦ (S.semi U).map_algebraMap r }
      φ₀ := RingHom.id _
      comm := fun _ ↦ rfl
      dp := by
        refine (isDPMorphism_iff _ _ _).2 ⟨Ideal.map_le_iff_le_comap.2 fun a ha ↦ ?_, fun n hn a ha ↦ ?_⟩
        · exact Ideal.mem_comap.2 (Ideal.mem_bot.2 ((S.ker U a).2 ha))
        · change (dp0 _).dpow n (S.p U a) = S.p U _
          rw [(S.ker U a).2 ha, dpow_eval_zero _ hn]
          exact ((S.ker U _).2 ((divided₂ (map_sq hI _)).dpow_mem hn ha)).symm
      pt := by
        change spMap (RingHom.id _) ≫ affPt s₀ U.unop = affPt s₀ U.unop ≫ 𝟙 X₀
        rw [Cris.spMap_id, Category.id_comp, Category.comp_id] }
  naturality U V a := Thick.hom_ext fun b ↦ S.nat a b

theorem redO_r (c : Cr hI π s₀) :
    S.redO.pull1 (S.r hI c) = cmpO s₀ (toH1O s₀ (rho hI hk s₀ c)) := by
  refine (CoefMap.pullCohomologyOne_comp _ _ c).symm.trans
    ((CoefMap.pullCohomologyOne_eq_of_natTrans _ (viaDR hI hk s₀) (S.redTrans hI hk) (fun _ _ ↦ rfl) c).trans ?_)
  rw [viaDR, CoefMap.pullCohomologyOne_comp, CoefMap.pullCohomologyOne_comp]
  rfl

end Sys

end GlobalTheory.LiftSys

namespace GlobalTheory.LiftSys

theorem Sys.mem_K_sup_iff : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀)
    (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀),
    ∀ S : Sys I π s₀, RhoBC hI hk s₀ → S.Full hI → ∀ c : Cr hI π s₀,
      c ∈ S.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) ↔ rho hI hk s₀ c ∈ F1 s₀ := by
  intro R R₀ _ _ I hI π _ hk X₀ s₀ S hBC hF c
  have key : ∀ c, rho hI hk s₀ c ∈ F1 s₀ ↔ S.redO.pull1 (S.r hI c) = 0 := fun c ↦ by
    rw [Sys.redO_r S hI hk c]
    change toH1O s₀ (rho hI hk s₀ c) = 0 ↔ _
    exact ⟨fun h ↦ by rw [h, map_zero],
      fun h ↦ GlobalTheory.CechDR.cmpO_injective R₀ X₀ s₀ (h.trans (map_zero _).symm)⟩
  rw [key]
  constructor
  · intro h
    obtain ⟨k, hk', i, hi, rfl⟩ := Submodule.mem_sup.1 h
    have h0 : S.r hI k = 0 := hk'
    rw [map_add (f := _), h0, zero_add]
    refine (key i).1 ?_
    rw [(hBC.2 i).2 hi]
    exact Submodule.zero_mem _
  · intro h
    obtain ⟨z, hz⟩ := H1.mk_surjective _ (S.r hI c)
    rw [← hz, CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at h
    obtain ⟨g₀, hg₀⟩ := h
    choose g hg using fun U ↦ S.surj U (g₀ U)
    let z' : Z1 S.F := z - ⟨d0 _ g, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g⟩
    have hz' : S.IsIdealValuedLiftSystemCocycle z' := by
      intro U V a
      rw [← S.ker]
      have e := congrFun (congrFun (congrFun hg₀ U) V) a
      rw [amitsur_d0_apply, CoefMap.pullCocycleOne_apply] at e
      change g₀ V - mp (OAff s₀) a (g₀ U) = S.p V (z.1 U V a) at e
      change S.p V (z.1 U V a - (g V - mp S.F a (g U))) = 0
      rw [map_sub, map_sub, S.nat, hg, hg, ← e, sub_self]
    obtain ⟨c', hc', hrc'⟩ := hF z' hz'
    have hr : S.r hI (c - c') = 0 := by
      rw [map_sub, hrc', ← hz, map_sub, sub_sub_cancel]
      exact H1.mk_eq_zero.2 ⟨g, rfl⟩
    exact Submodule.mem_sup.2 ⟨c - c', hr, c', hc', sub_add_cancel c c'⟩

end GlobalTheory.LiftSys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMapIdealSheafOfForallDivLocalEquation
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.Poinc

theorem mem_map_idealSheaf_of_forall_div :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → IsProper π → ∀ (D : EffCartierData M.Z) (V : M₁.Z.affineOpens) (g : Γ(M₁.Z, V.1)), (∀ x' : M.Z, π x' ∈ V.1 → ∀ f', EqAt M D x' f' → valF M₁.pt V.1 g / f' ∈ M.O x') → g ∈ (D.idealSheaf.map π).ideal V := by
  intro o Ω _ _ _ M₁ M π hπ hprop D V g hg
  haveI : QuasiCompact π := inferInstance
  rw [Scheme.IdealSheafData.map, Scheme.Hom.ker_apply, RingHom.mem_ker]
  change (D.idealSheaf.subschemeι.app (π ⁻¹ᵁ V.1)).hom ((π.app V.1).hom g) = 0
  rw [GlobalTheory.Cartier.app_subschemeι_eq_zero_iff]
  intro W hW
  show _ ∈ (EffCartierData.locIdeal D.U D.f D.exists_mem D.associated_germ).ideal W
  rw [EffCartierData.mem_locIdeal_iff]
  intro i x hx hi
  have hxV : x ∈ π ⁻¹ᵁ V.1 := hW hx
  have hV : (V.1 : Set M₁.Z).Nonempty := ⟨π x, hxV⟩
  rw [GlobalTheory.Cartier.germ_resG]
  have hval : valF M.pt (π ⁻¹ᵁ V.1) ((π.app V.1).hom g) = valF M₁.pt V.1 g := hπ.valF_app hV g
  have hq := hg x hxV _ ⟨i, hi, rfl⟩
  have hne : valF M.pt (D.U i) (D.f i) ≠ 0 := by
    intro h0
    have hnz := GlobalTheory.Cartier.isRegularFn_iff_germ.1 (D.regular i) x hi
    have : (M.Z.presheaf.germ (D.U i) x hi).hom (D.f i) = 0 := by
      apply M.stalkHom_injective x
      rw [map_zero]
      exact (RatModel.stalkHom_germ hi (D.f i)).trans h0
    rw [this] at hnz
    exact zero_notMem_nonZeroDivisors hnz
  rw [← map_dvd_iff (M.stalkEquiv x)]
  have e1 := RatModel.stalkEquiv_germ hi (D.f i)
  have e2 := RatModel.stalkEquiv_germ hxV ((π.app V.1).hom g)
  refine ⟨⟨_, hq⟩, ?_⟩
  apply Subtype.ext
  change (M.stalkEquiv x ((M.Z.presheaf.germ _ x hxV) ((π.app V.1).hom g)) : Ω) =
    (M.stalkEquiv x ((M.Z.presheaf.germ _ x hi) (D.f i)) : Ω) * (valF M₁.pt V.1 g / valF M.pt (D.U i) (D.f i))
  rw [e1, e2]
  simp only
  rw [hval, mul_div_cancel₀ _ hne]

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRealLieIffTraceFreeSkewSigns
section
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox

private theorem conj_zero_iff' {R : Type} [Ring R] (a b c d S : R) (hba : b * a = 1) (hcd : c * d = 1) :
    S = 0 ↔ a * S * c = 0 := by
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  have e : S = b * (a * S * c) * d := by
    simp only [← mul_assoc, hba, one_mul]; rw [mul_assoc, hcd, mul_one]
  rw [e, h]; simp

private theorem expand' {R : Type} [Ring R] (a b c d y z g : R) (hab : a * b = 1) (hdc : d * c = 1) :
    a * (b * (y * a) * g + g * (c * z * d)) * c = y * (a * g * c) + (a * g * c) * z := by
  have : a * (b * (y * a) * g + g * (c * z * d)) * c = (a * b) * y * (a * g * c) + (a * g * c) * z * (d * c) := by
    simp only [mul_add, add_mul, mul_assoc]
  rw [this, hab, hdc, one_mul, mul_one]

private theorem permJ' {r : ℕ} (p q : ℕ) (e : Fin p ⊕ Fin q ≃ Fin r) :
    (permM e)ᵀ * Formalism.UG.Jpq p q * permM e = diagonal (fun a => if (e.symm a).isLeft then (1:ℂ) else -1) := by
  ext a b
  simp [Matrix.mul_apply, permM, Equiv.apply_eq_iff_eq_symm_apply, diagonal_apply, Formalism.UG.Jpq]
  by_cases hab : a = b
  · subst hab; rw [if_pos rfl]; rcases e.symm a with i | i <;> simp
  · rw [if_neg hab]
    have h := e.symm.injective.ne hab
    revert h
    generalize e.symm a = i
    generalize e.symm b = j
    rcases i with i | i <;> rcases j with j | j <;> intro h <;> simp_all [one_apply]

namespace GlobalTheory.CovTop.VolUp.FrameBox

theorem mem_comap_realLie_iff_skewCond : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type)
    (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ)
    (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r),
    IsIdent p q Ψ G x σ A e → ∀ Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r),
      Y ∈ (realLie Ψ G).comap (fromFrame x) ↔ SkewCond (sgnR σ e) Y := by
  intro E _ _ _ r κ p q Ψ G x σ A e hI Y
  rw [Submodule.mem_comap, GlobalTheory.SUVol.DensOne.mem_realLie_iff]
  refine forall_congr' fun τ => ?_
  have hdet := (det_ne_zero_of_isIdent hI τ).1
  obtain ⟨h1, h2⟩ := hI (σ.symm τ)
  rw [Equiv.apply_symm_apply] at h1 h2
  set P := permM (e (σ.symm τ)) with hP
  set J := Formalism.UG.Jpq (p (σ.symm τ)) (q (σ.symm τ)) with hJdef
  set M := mat x τ with hMdef
  set B := A (σ.symm τ) with hBdef
  set Gt := G.map τ.1 with hGt
  set Yt : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => Y (τ, a, b) with hYt
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  set N := M⁻¹ with hN
  have hMN : M * N = 1 := Matrix.mul_nonsing_inv M hu
  have hNM : N * M = 1 := Matrix.nonsing_inv_mul M hu
  have hX : Matrix.of (fromFrame x Y τ) = M * Yt * N := rfl
  rw [hX]
  set D : Matrix (Fin r) (Fin r) ℂ := diagonal (fun a => ((sgnR σ e τ a : ℝ) : ℂ)) with hD
  have hPJP : Pᵀ * J * P = D := by
    rw [hP, hJdef, permJ', hD]
    congr 1; funext a; simp only [sgnR]; split_ifs <;> simp
  have hPc : Pᴴ = Pᵀ := by
    ext i j; simp only [hP, permM, conjTranspose_apply, transpose_apply, of_apply]; split_ifs <;> simp
  have hMt : (Mᴴ)ᵀ = M.map (starRingEnd ℂ) := by ext i j; simp
  have hG' : Gt = -(Bᴴ * J * B)ᵀ := by rw [h1, transpose_neg, transpose_transpose, neg_neg]
  have hH : Mᵀ * Gt * M.map (starRingEnd ℂ) = -D := by
    rw [hG', ← hMt, Matrix.mul_neg, Matrix.neg_mul]
    rw [show Mᵀ * (Bᴴ * J * B)ᵀ * (Mᴴ)ᵀ = (Mᴴ * (Bᴴ * J * B) * M)ᵀ by simp only [transpose_mul, Matrix.mul_assoc]]
    have : Mᴴ * (Bᴴ * J * B) * M = Pᵀ * J * P := by
      rw [← hPc, ← h2, conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [this, hPJP, hD, diagonal_transpose]
  have hc1 : M.map (starRingEnd ℂ) * N.map (starRingEnd ℂ) = 1 := by
    rw [← Matrix.map_mul, hMN, Matrix.map_one _ (map_zero _) (map_one _)]
  have hc2 : N.map (starRingEnd ℂ) * M.map (starRingEnd ℂ) = 1 := by
    rw [← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero _) (map_one _)]
  have ht1 : Mᵀ * Nᵀ = 1 := by rw [← transpose_mul, hNM, transpose_one]
  have ht2 : Nᵀ * Mᵀ = 1 := by rw [← transpose_mul, hMN, transpose_one]
  have htr : (M * Yt * N).trace = ∑ a, Y (τ, a, a) := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, hNM, Matrix.one_mul]; rfl
  rw [htr, and_comm]
  refine and_congr_right fun _ => ?_
  rw [conj_zero_iff' Mᵀ Nᵀ (M.map (starRingEnd ℂ)) (N.map (starRingEnd ℂ)) _ ht2 hc1]
  rw [transpose_mul, transpose_mul, Matrix.map_mul, Matrix.map_mul]
  rw [expand' _ _ _ _ _ _ _ ht1 hc2, hH]
  rw [Matrix.mul_neg, Matrix.neg_mul, ← neg_add, neg_eq_zero, ← Matrix.ext_iff]
  refine forall_congr' fun a => forall_congr' fun b => ?_
  rw [eq_comm (b := (0 : Matrix (Fin r) (Fin r) ℂ) a b)]
  simp [hD, hYt, Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact eq_comm

end GlobalTheory.CovTop.VolUp.FrameBox
end

