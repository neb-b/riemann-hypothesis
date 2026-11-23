module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0025
public import Formalism.SharpRestriction.LevelLetterCocycles.EvaluationAtUniformizerPower
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0038
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0037
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0019
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVNonneg

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.EvalZeroXEqUniformizer
section
noncomputable section

open Classical PowerSeries

namespace Formalism.MainNotions.UnusedSlot80.UGen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def WF {O : Type} [CommRing O] (p : O) (F : PowerSeries O) (N : ℕ) : Prop :=
  ∃ g h : PowerSeries O, IsUnit (constantCoeff g) ∧ F = g * X ^ N + C p * h

theorem WF.mul {O : Type} [CommRing O] {p : O} {F F' : PowerSeries O} {N N' : ℕ} (h1 : WF p F N)
    (h2 : WF p F' N') : WF p (F * F') (N + N') := by
  obtain ⟨g, h, hg, rfl⟩ := h1
  obtain ⟨g', h', hg', rfl⟩ := h2
  refine ⟨g * g', g * X ^ N * h' + h * (g' * X ^ N' + C p * h'), by rw [map_mul]; exact hg.mul hg', ?_⟩
  rw [pow_add]; ring

theorem WF.one {O : Type} [CommRing O] (p : O) : WF p 1 0 :=
  ⟨1, 0, by simp, by simp⟩

theorem WF.X {O : Type} [CommRing O] (p : O) : WF p X 1 :=
  ⟨1, 0, by simp, by simp⟩

theorem WF.pow {O : Type} [CommRing O] {p : O} {F : PowerSeries O} {N : ℕ} (h : WF p F N) (k : ℕ) :
    WF p (F ^ k) (N * k) := by
  induction k with
  | zero => simpa using WF.one p
  | succ k ih => rw [pow_succ, Nat.mul_succ]; exact ih.mul h

theorem WF.prod {O : Type} [CommRing O] {p : O} (F : ℕ → PowerSeries O) (N : ℕ → ℕ)
    (h : ∀ t, WF p (F t) (N t)) (e : ℕ) :
    WF p (∏ t ∈ Finset.range e, F t) (∑ t ∈ Finset.range e, N t) := by
  induction e with
  | zero => simpa using WF.one p
  | succ e ih => rw [Finset.prod_range_succ, Finset.sum_range_succ]; exact ih.mul (h e)

section Idem

variable {A : Type} [CommRing A] {E : A}

theorem idem_mul (_hE : E * E = E) {x y : A} (h : x * E = y * E) (z : A) : (z * x) * E = (z * y) * E := by
  rw [mul_assoc, h, ← mul_assoc]

theorem idem_pow (hE : E * E = E) {x y : A} (h : x * E = y * E) (k : ℕ) : x ^ k * E = y ^ k * E := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc x ^ (k + 1) * E = (x ^ k * E) * (x * E) := by rw [pow_succ]; linear_combination (-(x ^ k * x)) * hE
      _ = (y ^ k * E) * (y * E) := by rw [ih, h]
      _ = y ^ (k + 1) * E := by rw [pow_succ]; linear_combination (y ^ k * y) * hE

theorem idem_prod (hE : E * E = E) (x y : ℕ → A) (h : ∀ t, x t * E = y t * E) (e : ℕ) :
    (∏ t ∈ Finset.range e, x t) * E = (∏ t ∈ Finset.range e, y t) * E := by
  induction e with
  | zero => simp
  | succ e ih =>
    calc (∏ t ∈ Finset.range (e + 1), x t) * E = ((∏ t ∈ Finset.range e, x t) * E) * (x e * E) := by
          rw [Finset.prod_range_succ]; linear_combination (-((∏ t ∈ Finset.range e, x t) * x e)) * hE
      _ = ((∏ t ∈ Finset.range e, y t) * E) * (y e * E) := by rw [ih, h]
      _ = (∏ t ∈ Finset.range (e + 1), y t) * E := by
          rw [Finset.prod_range_succ]; linear_combination ((∏ t ∈ Finset.range e, y t) * y e) * hE

end Idem

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem evalZero_X_eq_uniformizer (W : LocWach PD LL O v n) (hR : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.Ring9 W) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W X = W.π₀ := by
  funext j
  rw [Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_apply, subst_X (Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.hasSubst W hR)]
  rfl

theorem ps_letter [IsDomain O] (W : LocWach PD LL O v n) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (hp0 : ((PD.p : ℕ) : O) ≠ 0) (a : ZMod n) (t : ℕ) :
    ∃ F : PowerSeries O, WF ((PD.p : ℕ) : O) F (PD.p ^ t) ∧
      Formalism.MainNotions.ArcLiftingSetup.ps W t * letE a = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W F * letE a := by
  obtain ⟨v, hvΔ, hvu, r, hr⟩ := Formalism.MainNotions.UnusedSlot80.ToolsR.modp hR hp0 t
  have hps : Formalism.MainNotions.ArcLiftingSetup.ps W t = v * W.π₀ ^ (PD.p ^ t) + ((PD.p : ℕ) : LetA O n) * (r + 1) := by
    have := Formalism.MainNotions.UnusedSlot80.ToolsR.pS_sub (W := W) t
    rw [hr] at this
    change Formalism.MainNotions.WachCoordinates.pS W t = _
    linear_combination this
  have hpsΔ : Formalism.MainNotions.ArcLiftingSetup.ps W t ∈ W.AΔ :=
    Formalism.MainNotions.UnusedSlot80.ToolsR.φpow_AΔ t (Formalism.MainNotions.UnusedSlot80.ToolsR.qP_AΔ hR)
  have hpΔ : ((PD.p : ℕ) : LetA O n) ∈ W.AΔ := Subalgebra.natCast_mem _ _
  have hr1 : r + 1 ∈ W.AΔ := by
    refine Formalism.MainNotions.UnusedSlot80.ToolsR.cancel_AΔ hpΔ (fun i => ?_) ?_
    · simp only [Pi.natCast_apply]
      exact_mod_cast (by
        intro h
        have := congrArg constantCoeff h
        simp only [map_natCast, map_zero] at this
        exact hp0 this : ((PD.p : ℕ) : PowerSeries O) ≠ 0)
    · have : ((PD.p : ℕ) : LetA O n) * (r + 1) = Formalism.MainNotions.ArcLiftingSetup.ps W t - v * W.π₀ ^ (PD.p ^ t) := by
        rw [hps]; ring
      rw [this]
      exact W.AΔ.sub_mem hpsΔ (W.AΔ.mul_mem hvΔ (W.AΔ.pow_mem hR.1 _))
  obtain ⟨gv, hgv⟩ := Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.invariant_letter_eq_evaluation W hR hvΔ a
  obtain ⟨gr, hgr⟩ := Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.invariant_letter_eq_evaluation W hR hr1 a
  have hE := Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.letE_mul_self' (O := O) a
  refine ⟨gv * X ^ (PD.p ^ t) + C ((PD.p : ℕ) : O) * gr, ⟨gv, gr, ?_, rfl⟩, ?_⟩
  · have h1 := congrFun hgv a
    simp only [Pi.mul_apply, letE, Pi.single_eq_same, mul_one, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_apply] at h1
    have hva : IsUnit (v a) := hvu.map (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) a)
    rw [h1] at hva
    have := hva.map constantCoeff
    rwa [Formalism.MainNotions.UnusedSlot80.ToolsR.cc_subst (Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR)] at this
  · have hC : Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (C ((PD.p : ℕ) : O)) = ((PD.p : ℕ) : LetA O n) := by
      rw [map_natCast, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR, map_natCast]
    have hX : Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (X ^ (PD.p ^ t)) = W.π₀ ^ (PD.p ^ t) := by
      rw [Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR, map_pow, ← Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR, evalZero_X_eq_uniformizer W hR]
    rw [Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_add W hR, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evalZero_mul W hR, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evalZero_mul W hR, hX, hC,
      hps]
    linear_combination (W.π₀ ^ (PD.p ^ t)) * hgv + ((PD.p : ℕ) : LetA O n) * hgr

theorem finLev_of [IsDomain O] (W : LocWach PD LL O v n) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (hp0 : ((PD.p : ℕ) : O) ≠ 0) [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) : FinLev W := by
  intro a e H
  set pO : O := ((PD.p : ℕ) : O) with hpO
  set I : Ideal O := Ideal.span {pO} with hI
  have hE := Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.letE_mul_self' (O := O) a
  choose Fs hFs hFe using fun t => ps_letter W hR hp0 a t
  set Gall : PowerSeries O := X * (∏ t ∈ Finset.range e, Fs t ^ H t) ^ 2 with hGall
  have hWF : WF pO Gall (1 + (∑ t ∈ Finset.range e, PD.p ^ t * H t) * 2) :=
    (WF.X pO).mul ((WF.prod (fun t => Fs t ^ H t) (fun t => PD.p ^ t * H t)
      (fun t => (hFs t).pow (H t)) e).pow 2)
  set D := 1 + (∑ t ∈ Finset.range e, PD.p ^ t * H t) * 2 with hD
  have hlet : W.π₀ * (∏ t ∈ Finset.range e, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ H t) ^ 2 * letE a =
      Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W Gall * letE a := by
    have h1 : (∏ t ∈ Finset.range e, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ H t) * letE a =
        (∏ t ∈ Finset.range e, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (Fs t) ^ H t) * letE a :=
      idem_prod hE _ _ (fun t => idem_pow hE (hFe t) (H t)) e
    have h2 := idem_mul hE (idem_pow hE h1 2) W.π₀
    rw [h2, hGall, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR, map_mul, map_pow, map_prod, ← Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR,
      evalZero_X_eq_uniformizer W hR]
    simp only [Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR, map_pow]
  obtain ⟨g, h, hgu, hGe⟩ := hWF
  obtain ⟨P, uu, huu, hPm, hPd, hPc, hGP⟩ := Formalism.MainNotions.UnusedSlot80.ToolsR.weierP pO hpu D g h hgu
  have hmapP : (P : PowerSeries O).map (Ideal.Quotient.mk I) = X ^ D := by
    ext k
    rw [coeff_map, Polynomial.coeff_coe, coeff_X_pow]
    split_ifs with hk
    · subst hk; rw [← hPd, hPm.coeff_natDegree, map_one]
    · rcases lt_or_gt_of_ne hk with hlt | hgt
      · exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 (hPc k hlt))
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
  haveI : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr (by
    rw [Ne, hI, Ideal.span_singleton_eq_top]; exact hpu)
  have hord : ((P : PowerSeries O).map (Ideal.Quotient.mk I)).order.toNat = D := by
    rw [hmapP, order_X_pow]; rfl
  have hdiv : (P : PowerSeries O).IsWeierstrassDivisorAt I := by
    unfold PowerSeries.IsWeierstrassDivisorAt
    rw [hord, Polynomial.coeff_coe, ← hPd, hPm.coeff_natDegree]
    exact isUnit_one
  refine ⟨D, fun u hu => ?_⟩
  obtain ⟨f, hf⟩ := Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.invariant_letter_eq_evaluation W hR hu a
  have HD := hdiv.isWeierstrassDivisionAt_div_mod f
  set q := hdiv.div f
  set r := hdiv.mod f
  have hdeg : r.degree < (D : WithBot ℕ) := by
    have := HD.degree_lt
    rw [hord] at this
    exact this
  have heq : f = (P : PowerSeries O) * q + (r : PowerSeries O) := HD.eq_mul_add
  have hfG : f = Gall * (↑huu.unit⁻¹ * q) + (r : PowerSeries O) := by
    rw [heq, hGe, hGP, mul_assoc, ← mul_assoc uu, IsUnit.mul_val_inv, one_mul]
  refine ⟨fun j => r.coeff j, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (↑huu.unit⁻¹ * q),
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_mem_invariants W hR _, ?_⟩
  have hr : Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (r : PowerSeries O) =
      ∑ j : Fin D, algebraMap O (LetA O n) (r.coeff j) * W.π₀ ^ (j : ℕ) := by
    rw [Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR, Formalism.MainNotions.RamifiedCoefficientChains.S9.Ring.algHom_coe, ← Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR,
      evalZero_X_eq_uniformizer W hR]
    have hnd : r.natDegree < D := by
      by_cases hr0 : r = 0
      · rw [hr0, Polynomial.natDegree_zero]; omega
      · exact (Polynomial.natDegree_lt_iff_degree_lt hr0).2 hdeg
    rw [Polynomial.aeval_eq_sum_range' hnd, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def]
  have hu' : (letE a : LetA O n) * u = letE a * Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f := by
    rw [mul_comm, hf, mul_comm]
  rw [hu', hfG, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_add W hR, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evalZero_mul W hR, hr]
  have h3 : (letE a : LetA O n) * Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W Gall =
      W.π₀ * (∏ t ∈ Finset.range e, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ H t) ^ 2 * letE a := by
    rw [hlet, mul_comm]
  linear_combination (Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (↑huu.unit⁻¹ * q)) * h3

end Formalism.MainNotions.UnusedSlot80.UGen
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.ExistsDvdPowOfNotIsUnitDvr
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80.InvW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

section LevRatPf

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem exists_dvd_pow_of_not_isUnit_dvr [IsDomain O] [IsDiscreteValuationRing O] (p : O) (hp0 : p ≠ 0) (hpu : ¬ IsUnit p)
    {y : O} (hy : y ≠ 0) : ∃ (κ : ℕ) (z : O), p ^ κ = y * z := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, u, hyu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  obtain ⟨e, u', hpe⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · exact absurd (by rw [hpe, h, pow_zero, mul_one]; exact u'.isUnit) hpu
    · exact h
  refine ⟨m, ((u⁻¹ : Oˣ) : O) * (u' : O) ^ m * ϖ ^ (e * m - m), ?_⟩
  have hm : m ≤ e * m := Nat.le_mul_of_pos_left m he
  rw [hpe, hyu, mul_pow, ← pow_mul]
  have e1 : ϖ ^ (e * m) = ϖ ^ m * ϖ ^ (e * m - m) := by rw [← pow_add, Nat.add_sub_cancel' hm]
  rw [e1]
  have e2 : ((u : O) * ((u⁻¹ : Oˣ) : O)) = 1 := Units.mul_inv u
  linear_combination (-((u' : O) ^ m * ϖ ^ m * ϖ ^ (e * m - m))) * e2

variable [IsDomain O] [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]

theorem levRatPf_ev (W : LocWach PD LL O v n) (hR : ToolsR.RingP W) (hT : Formalism.MainNotions.WachCoordinates.ToolsAlg W)
    (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) (a : ZMod n) (s : ℕ) (hB : LevBasics W a s) (g : LetA O n) :
    ∃ r : Polynomial O, r.degree < ((PD.p - 1) * PD.p ^ s : ℕ) ∧
      ∀ ζ : Rs hB.F PD.p s, hB.ev ζ g = Polynomial.aeval ((ζ : hB.F) - 1) r := by
  obtain ⟨H, r, hdeg, heq⟩ := wdiv_ps W hR hT hpu a s (g a)
  refine ⟨r, hdeg, fun ζ => ?_⟩
  set wH : LetA O n := Pi.single a H with hwH
  have hRr : (fun _ : ZMod n => (r : PowerSeries O)) = Polynomial.aeval (letπ : LetA O n) r := by
    funext i
    show (r : PowerSeries O) = Pi.evalAlgHom O (fun _ : ZMod n => PowerSeries O) i (Polynomial.aeval letπ r)
    rw [← Polynomial.aeval_algHom_apply]
    exact (aeval_X_coe r).symm
  have key : (letE a : LetA O n) * g = ps W s * wH + letE a * Polynomial.aeval (letπ : LetA O n) r := by
    rw [← hRr]
    funext i
    by_cases hi : i = a
    · subst hi
      simp only [Pi.mul_apply, Pi.add_apply, hwH, letE, Pi.single_eq_same, one_mul, heq]
    · simp [Pi.mul_apply, Pi.add_apply, hwH, letE, Pi.single_eq_of_ne hi]
  have h1 := congrArg (hB.ev ζ) key
  rw [map_mul, hB.ev_letE, one_mul, map_add (f := _), map_mul, hB.ev_ps, zero_mul, zero_add, map_mul,
    hB.ev_letE, one_mul, ev_aeval hB] at h1
  exact h1

theorem levRat_of [IsDiscreteValuationRing O] (W : LocWach PD LL O v n) (hR : ToolsR.RingP W)
    (hT : Formalism.MainNotions.WachCoordinates.ToolsAlg W) (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) (a : ZMod n) (s : ℕ)
    (hB : LevBasics W a s) : LevRat W a s hB.F hB.ev := by
  intro g _ d _ hd c hc
  obtain ⟨rg, hgdeg, hg⟩ := levRatPf_ev W hR hT hpu a s hB g
  obtain ⟨rd, hddeg, hdv⟩ := levRatPf_ev W hR hT hpu a s hB d
  have hN : ∀ r : Polynomial O, r.degree < ((PD.p - 1) * PD.p ^ s : ℕ) →
      (r.map (algebraMap O hB.F)).natDegree < (PD.p - 1) * PD.p ^ s := by
    intro r hr
    have hNpos : 0 < (PD.p - 1) * PD.p ^ s :=
      Nat.mul_pos (by have := PD.hp.two_le; omega) (pow_pos PD.hp.pos _)
    refine lt_of_le_of_lt Polynomial.natDegree_map_le ?_
    by_cases h0 : r = 0
    · rw [h0, Polynomial.natDegree_zero]; exact hNpos
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).2 hr
  set R : Polynomial hB.F := rg.map (algebraMap O hB.F) - Polynomial.C c * rd.map (algebraMap O hB.F) with hRdef
  have hR0 : R = 0 := by
    refine poly_eq_zero hB R ?_ ?_
    · refine lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt (hN rg hgdeg) ?_)
      exact lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) (hN rd hddeg)
    · intro ζ
      rw [hRdef, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map,
        Polynomial.eval_map, ← Polynomial.aeval_def, ← Polynomial.aeval_def, ← hg ζ, ← hdv ζ, hc ζ, sub_self]
  have hne : Nonempty (Rs hB.F PD.p s) := by
    rw [← Fintype.card_pos_iff, card_Rs hB]
    exact Nat.mul_pos (by have := PD.hp.two_le; omega) (pow_pos PD.hp.pos _)
  obtain ⟨ζ₀⟩ := hne
  have hrd : rd ≠ 0 := by
    intro h
    apply hd ζ₀
    rw [hdv ζ₀, h, map_zero]
  obtain ⟨k, hk⟩ : ∃ k, rd.coeff k ≠ 0 := by
    by_contra h
    push Not at h
    exact hrd (Polynomial.ext fun k => by simpa using h k)
  have hck : algebraMap O hB.F (rg.coeff k) = c * algebraMap O hB.F (rd.coeff k) := by
    have := congrArg (fun P : Polynomial hB.F => P.coeff k) hR0
    simp only [hRdef, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_map,
      Polynomial.coeff_zero] at this
    exact sub_eq_zero.1 this
  have hp0 : ((PD.p : ℕ) : O) ≠ 0 := by
    intro h
    apply hB.hp
    rw [← map_natCast (algebraMap O hB.F), h, map_zero]
  obtain ⟨κ, z, hz⟩ := exists_dvd_pow_of_not_isUnit_dvr ((PD.p : ℕ) : O) hp0 hpu hk
  refine ⟨κ, z * rg.coeff k, ?_⟩
  rw [map_mul, hck, ← map_natCast (algebraMap O hB.F), ← map_pow, hz, map_mul]
  ring

end LevRatPf

end Formalism.MainNotions.UnusedSlot80.InvW
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusDifferenceIdentity
section
noncomputable section

open Classical

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2A

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains
open Formalism.MainNotions.CrystallineLiftingInputs (DL InPN pullJ fMX)
open Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2L Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2I

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem sigma_bound_le (l h η : ℕ) (hl : 11 ≤ l) :
    ((2 * S9.sigC l h η : ℕ) : ℝ) ≤ S9.ExtensionLemmaAlt.B2 l h η := by
  have hl' : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hx : 0 ≤ (((Formalism.MainNotions.CrystallineLiftingInputs.Mpar l h : ℕ) : ℝ) + (η : ℝ)) / ((l : ℝ) - 1) + 1 := by
    have : 0 ≤ (((Formalism.MainNotions.CrystallineLiftingInputs.Mpar l h : ℕ) : ℝ) + (η : ℝ)) / ((l : ℝ) - 1) :=
      div_nonneg (by positivity) (by linarith)
    linarith
  have hc := Nat.ceil_lt_add_one hx
  unfold S9.ExtensionLemmaAlt.B2 Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig
  unfold S9.sigC
  unfold Formalism.MainNotions.CrystallineLiftingInputs.Mpar
  push_cast
  unfold Formalism.MainNotions.CrystallineLiftingInputs.Mpar at hc
  push_cast at hc
  linarith

theorem eta_le_parameter (l h η : ℕ) (hl : 2 ≤ l) (hη : η ≤ h) : η ≤ (l - 1) * Formalism.MainNotions.CrystallineLiftingInputs.Mpar l h := by
  unfold Formalism.MainNotions.CrystallineLiftingInputs.Mpar
  have := Nat.lt_mul_div_succ h (by omega : 0 < l - 1)
  omega

theorem jumps_bounds_of_set [NeZero n] (W : LocWach PD LL O v n) {d : ℕ} {T₁ T₂ : LocLat G Qp LL O}
    {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ} {S η m : ℕ} (hEx : DcrisExactStrict PD LL)
    (hCs : CrysSubQuot PD LL) (hDq : DdREqDcris PD LL) (hS : SetCS W d T₁ T₂ F b S η m) :
    (∀ i τ, Formalism.MainNotions.LiftingTheory.Over W τ i → JumpsInV PD T₂.ρ τ (Set.Ici (-((hpar n b S : ℕ) : ℤ)))) ∧
    ∀ (c' : ZMod n) τ, (c'.val + d) % 2 = 0 → Formalism.MainNotions.LiftingTheory.Over W τ (c' + 1) →
      JumpsInV PD T₂.ρ τ (Set.Ici (-(η : ℤ))) := by
  have hn : Even n := hS.2.2.1
  have hwin : ∀ i a, a ∈ Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS d b S η i → -((hpar n b S : ℕ) : ℤ) ≤ a := by
    intro i a ha
    have hbi : b i ≤ Finset.univ.sup b := Finset.le_sup (Finset.mem_univ i)
    have hη := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_eta_lt W hS i
    unfold Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS at ha
    unfold hpar
    split_ifs at ha <;> simp only [Set.mem_union, Set.mem_Icc] at ha <;> push_cast at ha ⊢ <;> omega
  have hwinU : ∀ c' : ZMod n, (c'.val + d) % 2 = 0 → ∀ a,
      a ∈ Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS d b S η (c' + 1) → -(η : ℤ) ≤ a := by
    intro c' hc' a ha
    have hpar' := S9.parity_succ hn d c'
    unfold Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS at ha
    rw [if_neg (by omega)] at ha
    simp only [Set.mem_union, Set.mem_Icc] at ha
    push_cast at ha
    omega
  exact ⟨fun i τ hτ a ha => hwin i a (Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jumps₂ W hEx hCs hDq hS i τ hτ a ha),
    fun c' τ hc' hτ a ha => hwinU c' hc' a (Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jumps₂ W hEx hCs hDq hS (c' + 1) τ hτ a ha)⟩

theorem difference_of_factorisations {M' : Type} [AddCommGroup M'] [Module O M'] {R : Type} [CommRing R] [Module R M']
    [SMulCommClass O R M'] (f0 : R) (l : O) (φw tw t₁ t' t p₁ p₂ p₃ : M')
    (etw : tw - ((1 : O) • t₁ + (-l) • t') = f0 • p₁) (e₂ : t₁ = f0 • p₂) (e₃ : t - t' = f0 • p₃) :
    (l • φw - tw) - l • (φw + t) = f0 • (-(p₁ + p₂ + l • p₃)) := by
  have et' : t' = t - f0 • p₃ := by rw [← e₃]; abel
  have etw' : tw = f0 • p₁ + ((1 : O) • t₁ + (-l) • t') := by rw [← etw]; abel
  rw [etw', e₂, et']
  simp only [one_smul, neg_smul, smul_sub, smul_add, smul_neg]
  rw [smul_comm l f0 p₃]
  abel

theorem pow_smul_cocycle_sub_sum_mem_latticeCoboundaries (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (ev : Finset (ZMod n))
    (xc : ZMod n → ↥(W.wachCocyclesDelta T)) (κ : ZMod n → G → T.V) (hκ : ∀ c, κ c ∈ latticeCocycles T.L)
    (hP : ∀ c ∈ ev, W.clK T (xc c) = Submodule.Quotient.mk ⟨κ c, hκ c⟩)
    (x0 : ↥(W.wachCocyclesDelta T)) (gf : G → T.V) (hgf : gf ∈ latticeCocycles T.L)
    (hcl0 : W.clK T x0 = Submodule.Quotient.mk ⟨gf, hgf⟩) (e : ℕ)
    (hcls : ∑ c ∈ ev, W.clK T (xc c) = ((PD.p : ℕ) : O) ^ e • W.clK T x0) :
    (PD.p : O) ^ e • gf - ∑ c ∈ ev, κ c ∈ latticeCoboundaries T.L := by
  let Ks : ↥(latticeCocycles T.L) := ∑ c ∈ ev, ⟨κ c, hκ c⟩
  have hK : (Submodule.Quotient.mk Ks : LatticeCohomology T.L) = ∑ c ∈ ev, W.clK T (xc c) := by
    calc (Submodule.Quotient.mk Ks : LatticeCohomology T.L)
        = ((latticeCoboundaries T.L).comap (latticeCocycles T.L).subtype).mkQ Ks := rfl
      _ = ∑ c ∈ ev, ((latticeCoboundaries T.L).comap (latticeCocycles T.L).subtype).mkQ ⟨κ c, hκ c⟩ := map_sum _ _ _
      _ = ∑ c ∈ ev, W.clK T (xc c) := Finset.sum_congr rfl fun c hc => (hP c hc).symm
  have hgf0 : (Submodule.Quotient.mk (((PD.p : ℕ) : O) ^ e • (⟨gf, hgf⟩ : ↥(latticeCocycles T.L)) - Ks) :
      LatticeCohomology T.L) = 0 := by
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, hK, hcls, hcl0, sub_self]
  have hmem := (Submodule.Quotient.mk_eq_zero _).1 hgf0
  rw [Submodule.mem_comap] at hmem
  simpa [Ks, Submodule.coe_sum] using hmem

section Fam

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def letterIdempotentMap (i : ZMod n) : W.DD T →ₗ[O] W.DD T where
  toFun x := (letE i : LetA O n) • x
  map_add' x y := smul_add _ x y
  map_smul' r x := Formalism.MainNotions.N.Pv.LocalLengthBound.osmul_comm W T (letE i) r x

variable {W T}

theorem frobenius_lift_identity (N s₁ σ : ℕ) (yv : W.DD T) (ms t μ : ZMod n → W.DD T) (c : ZMod n) :
    ((PD.p : ℕ) : O) ^ N • liftCorrection W T s₁ σ yv ms t c - ((PD.p : ℕ) : O) ^ (s₁ + σ) • μ (c + 1) =
      ((PD.p : ℕ) : O) ^ σ • W.φD T (((PD.p : ℕ) : O) ^ N • ms c - ((PD.p : ℕ) : O) ^ s₁ • μ c) +
        ((PD.p : ℕ) : O) ^ (s₁ + σ) • (((PD.p : ℕ) : O) ^ N • ((letE (c + 1) : LetA O n) • yv) +
          W.φD T (μ c) - μ (c + 1)) - ((PD.p : ℕ) : O) ^ N • t c := by
  unfold liftCorrection
  simp only [map_sub, map_smul, smul_add, smul_sub, smul_smul, ← pow_add]
  simp only [add_comm, add_left_comm, add_assoc]
  abel

theorem gamma_difference_identity (N s₁ σ : ℕ) (yv zv : W.DD T) (ms t μ : ZMod n → W.DD T) (c : ZMod n) :
    W.γ T (((PD.p : ℕ) : O) ^ N • liftCorrection W T s₁ σ yv ms t c -
        ((PD.p : ℕ) : O) ^ (s₁ + σ) • μ (c + 1)) -
      (((PD.p : ℕ) : O) ^ N • liftCorrection W T s₁ σ yv ms t c - ((PD.p : ℕ) : O) ^ (s₁ + σ) • μ (c + 1)) =
      ((PD.p : ℕ) : O) ^ N • gammaDefectOfLiftCorrection W T s₁ σ yv zv ms t c -
        ((PD.p : ℕ) : O) ^ (s₁ + σ) • (((PD.p : ℕ) : O) ^ N • ((letE (c + 1) : LetA O n) • zv) +
          (W.γ T (μ (c + 1)) - μ (c + 1))) := by
  unfold gammaDefectOfLiftCorrection
  simp only [map_sub, map_smul, smul_add, smul_sub, smul_smul, ← pow_add]
  simp only [add_comm, add_left_comm, add_assoc]
  abel

theorem frobenius_difference_identity (N s₁ σ : ℕ) (yv : W.DD T) (ms t μ : ZMod n → W.DD T) (c : ZMod n) :
    ((PD.p : ℕ) : O) ^ N • frobeniusShiftDefectOfLiftCorrection W T s₁ σ yv ms t c =
      W.φD T (((PD.p : ℕ) : O) ^ N • liftCorrection W T s₁ σ yv ms t (c - 2) -
          ((PD.p : ℕ) : O) ^ (s₁ + σ) • μ (c - 1)) -
        ((PD.p : ℕ) : O) ^ σ • (((PD.p : ℕ) : O) ^ N • ms c - ((PD.p : ℕ) : O) ^ s₁ • μ c) +
        ((PD.p : ℕ) : O) ^ (s₁ + σ) • (((PD.p : ℕ) : O) ^ N • ((letE c : LetA O n) • yv) +
          W.φD T (μ (c - 1)) - μ c) := by
  unfold frobeniusShiftDefectOfLiftCorrection
  simp only [map_sub, map_add (f := _), map_smul, smul_add, smul_sub, smul_smul, ← pow_add]
  simp only [add_comm, add_left_comm, add_assoc]
  abel

end Fam

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2A

end
end

