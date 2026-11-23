module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PublishedIntClosHolds
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ModelAt
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def PartIAt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → l.GoodAt p →
    ∃ Y : Model Xo c (c.V W).subtype, Y.N3 ∧ PushInvertible Y.t.G Y.t.PP.L

theorem exists_lieElement_middleBlockPart (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) :
    ∃ W : ValuationSubring ℂ, (∀ x : 𝓞 c.F, x ∈ la.asIdeal → (((algebraMap (𝓞 c.F) c.F x : c.F) : ℂ)) ∈ W.nonunits) ∧
      ∀ x : c.F, (x : ℂ) ∈ W → la.valuation c.F x ≤ 1 := by
  set V := (la.valuation c.F).valuationSubring with hVdef
  let g : V →+* ℂ := c.F.val.toRingHom.comp V.subtype
  have hg : Function.Injective g := fun a b h => Subtype.ext (c.F.val.injective h)
  let e : V ≃+* g.range := RingEquiv.ofBijective g.rangeRestrict ⟨fun a b h => hg (congrArg (fun z : g.range => (z : ℂ)) h),
    g.rangeRestrict_surjective⟩
  have hmax : ((IsLocalRing.maximalIdeal V).map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
  obtain ⟨W, hAW, hIW⟩ := Ideal.image_subset_nonunits_valuationSubring _ hmax.ne_top
  have hnon : ∀ y : V, y ∈ IsLocalRing.maximalIdeal V → g y ∈ W.nonunits := fun y hy =>
    hIW ⟨e y, Ideal.mem_map_of_mem _ hy, rfl⟩
  refine ⟨W, fun x hx => ?_, fun x hx => ?_⟩
  · have hxV : algebraMap (𝓞 c.F) c.F x ∈ V := by
      rw [hVdef, Valuation.mem_valuationSubring_iff, HeightOneSpectrum.valuation_of_algebraMap]
      exact la.intValuation_le_one x
    have hxm : (⟨_, hxV⟩ : V) ∈ IsLocalRing.maximalIdeal V := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 hu
      have h1 : la.valuation c.F (algebraMap (𝓞 c.F) c.F x) < 1 := by
        rw [HeightOneSpectrum.valuation_of_algebraMap]; exact (la.intValuation_lt_one_iff_mem x).2 hx
      have h2 : la.valuation c.F ((w : V) : c.F) ≤ 1 := w.2
      have h3 := congrArg (fun z : V => la.valuation c.F (z : c.F)) hw
      simp only [MulMemClass.coe_mul, OneMemClass.coe_one, map_mul, map_one] at h3
      have h4 : la.valuation c.F (algebraMap (𝓞 c.F) c.F x) * la.valuation c.F ((w : V) : c.F) < 1 :=
        lt_of_lt_of_le (mul_lt_one_of_nonneg_of_lt_one_left zero_le h1 h2) le_rfl
      rw [h3] at h4
      exact lt_irrefl _ h4
    exact hnon _ hxm
  · by_contra hv
    push_neg at hv
    have hx0 : x ≠ 0 := by rintro rfl; simp at hv
    have hiV : x⁻¹ ∈ V := by
      rw [hVdef, Valuation.mem_valuationSubring_iff, map_inv₀]
      exact (inv_lt_one_of_one_lt₀ hv).le
    have him : (⟨x⁻¹, hiV⟩ : V) ∈ IsLocalRing.maximalIdeal V := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 hu
      have h1 : (w : c.F) = x := by
        have := congrArg (fun z : V => (z : c.F)) hw
        simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
        field_simp at this
        exact this
      have h2 : la.valuation c.F ((w : V) : c.F) ≤ 1 := w.2
      rw [h1] at h2
      exact absurd h2 (not_le.2 hv)
    have h5 := hnon _ him
    rw [ValuationSubring.mem_nonunits_iff] at h5
    have h6 := (ValuationSubring.valuation_le_one_iff W _).2 hx
    have h7 : g ⟨x⁻¹, hiV⟩ = ((x : ℂ))⁻¹ := by
      show ((x⁻¹ : c.F) : ℂ) = _
      exact map_inv₀ c.F.val x
    rw [h7, map_inv₀] at h5
    have hW0 : W.valuation (x : ℂ) ≠ 0 := by
      rw [Valuation.ne_zero_iff]; exact_mod_cast hx0
    exact absurd ((inv_lt_one₀ (zero_lt_iff.2 hW0)).1 h5) (not_lt.2 h6)

theorem modelAtSt_of {Xo : Moduli Dw l} {c : Coeff l} (hI : PartIAt Xo c) (hgood : ∀ p : ℕ, p.Prime → l.GoodAt p)
    (la : HeightOneSpectrum (𝓞 c.F)) : ModelAtSt Xo c la := by
  obtain ⟨W, hWnon, hWkey⟩ := exists_lieElement_middleBlockPart c la
  have hp : (Formalism.MainNotions.WeightAlgebra.resCh la).Prime := resCh_prime la
  have hmem : ((Formalism.MainNotions.WeightAlgebra.resCh la : ℕ) : 𝓞 c.F) ∈ la.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact ringChar.Nat.cast_ringChar
  have hpW : ((Formalism.MainNotions.WeightAlgebra.resCh la : ℕ) : ℂ) ∈ W.nonunits := by
    have := hWnon _ hmem
    simpa using this
  obtain ⟨Y, hN3, hPI⟩ := hI _ W hp hpW (hgood _ hp)
  refine ⟨c.V W, inferInstance, (c.V W).subtype, Y, hN3, hPI, fun Tc io e ho => ?_⟩
  have hint : ∀ x : c.V W, io (x : c.F) ∈ (algebraMap Tc.V Tc.Fr).range := by
    intro x
    have hx : la.valuation c.F (x : c.F) ≤ 1 := hWkey _ x.2
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro v
    have hv : v = IsDiscreteValuationRing.maximalIdeal Tc.V :=
      HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal v.isMaximal)
    subst hv
    by_cases hx0 : (x : c.F) = 0
    · rw [hx0, map_zero, map_zero]; exact zero_le
    have hvx0 : la.valuation c.F (x : c.F) ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
    have hla : 0 ≤ vLa la (x : c.F) := by
      unfold vLa
      rw [← WithZero.exp_log hvx0, ← WithZero.exp_zero, WithZero.exp_le_exp] at hx
      linarith
    have hvV : 0 ≤ vV Tc.V (io (x : c.F)) := by
      rw [ho.2 (x : c.F)]
      positivity
    have hio0 : io (x : c.F) ≠ 0 := (map_ne_zero io).2 hx0
    have hval0 : valV Tc.V (io (x : c.F)) ≠ 0 := valV_ne_zero hio0
    show valV Tc.V (io (x : c.F)) ≤ 1
    unfold vV at hvV
    rw [← WithZero.exp_log hval0, ← WithZero.exp_zero, WithZero.exp_le_exp]
    linarith
  let f : c.V W →+* (algebraMap Tc.V Tc.Fr).range := (io.comp (c.V W).subtype).codRestrict _ hint
  let eq : Tc.V ≃+* (algebraMap Tc.V Tc.Fr).range := RingEquiv.ofBijective (algebraMap Tc.V Tc.Fr).rangeRestrict
    ⟨fun a b h => IsFractionRing.injective Tc.V Tc.Fr (congrArg (fun z : (algebraMap Tc.V Tc.Fr).range => (z : Tc.Fr)) h),
      (algebraMap Tc.V Tc.Fr).rangeRestrict_surjective⟩
  refine ⟨eq.symm.toRingHom.comp f, ?_⟩
  ext x
  have := congrArg (fun z : (algebraMap Tc.V Tc.Fr).range => (z : Tc.Fr)) (eq.apply_symm_apply (f x))
  exact this

theorem goodAt_of_two_primes {g0 g1 : ℕ} (hM : l.M = g0 * g1) (h0 : g0.Prime) (h1 : g1.Prime)
    (hne : g0 ≠ g1) (p : ℕ) (hp : p.Prime) : l.GoodAt p := by
  unfold Level.GoodAt
  have hodd : Odd (g0 * g1) := hM ▸ l.odd
  have h3 : 3 ≤ g0 * g1 := hM ▸ l.three_le
  have o0 : Odd g0 := (Nat.odd_mul.1 hodd).1
  have o1 : Odd g1 := (Nat.odd_mul.1 hodd).2
  have t0 : 3 ≤ g0 := by
    have := h0.two_le
    have := Nat.odd_iff.1 o0
    omega
  have t1 : 3 ≤ g1 := by
    have := h1.two_le
    have := Nat.odd_iff.1 o1
    omega
  rw [hM, Nat.factorization_mul h0.ne_zero h1.ne_zero, Finsupp.add_apply, h0.factorization, h1.factorization]
  by_cases e0 : p = g0
  · have e : (Finsupp.single g0 1 : ℕ →₀ ℕ) p + (Finsupp.single g1 1 : ℕ →₀ ℕ) p = 1 := by
      simp [Finsupp.single_apply, e0, hne, hne.symm]
    rw [e, pow_one, e0, Nat.mul_div_cancel_left g1 h0.pos]
    exact t1
  · by_cases e1 : p = g1
    · have e : (Finsupp.single g0 1 : ℕ →₀ ℕ) p + (Finsupp.single g1 1 : ℕ →₀ ℕ) p = 1 := by
        simp [Finsupp.single_apply, e1, hne, hne.symm]
      rw [e, pow_one, e1, Nat.mul_div_cancel g0 h1.pos]
      exact t0
    · have e : (Finsupp.single g0 1 : ℕ →₀ ℕ) p + (Finsupp.single g1 1 : ℕ →₀ ℕ) p = 0 := by
        simp [Finsupp.single_apply, e0, e1, Ne.symm e0, Ne.symm e1]
      rw [e, pow_zero, Nat.div_one]
      exact h3

theorem partIAt_of (hP : PartI) (hN : N1ab) (Xo : Moduli Dw l) (c : Coeff l) (hpq : 1 ≤ Dw.p + Dw.q) : PartIAt Xo c := by
  classical
  obtain ⟨-, hI⟩ := hP
  let Xf : ∀ l' : Level H, Moduli Dw l' := fun l' =>
    if h : l' = l then h ▸ Xo else Classical.choice (hN E H Dw l' hpq)
  obtain ⟨Y, hY, -⟩ := hI E H Dw hpq Xf
  intro p W hp hW hg
  obtain ⟨hN2, hrest⟩ := hY p W hp hW
  let i : Idx H p := ⟨l, c, hg⟩
  have hPIi := (hN2.1 i).2.2.1
  have hN3 := (hrest i).2.1
  have hX : Xf l = Xo := by simp [Xf]
  have key : ∀ (X' : Moduli Dw l), X' = Xo → ∀ Y' : Model X' c (c.V W).subtype, Y'.N3 →
      PushInvertible Y'.t.G Y'.t.PP.L → ∃ Y : Model Xo c (c.V W).subtype, Y.N3 ∧ PushInvertible Y.t.G Y.t.PP.L := by
    rintro X' rfl Y' h1 h2
    exact ⟨Y', h1, h2⟩
  exact key (Xf l) hX (Y p W hp hW i) hN3 hPIi

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
section
noncomputable section

namespace Formalism.L2.Pj

open scoped TensorProduct
open MeasureTheory
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem pnorm_of_eq_zero (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) (h : P x = 0) :
    X.pnorm la P x = 0 := by
  unfold Data.pnorm
  rw [h, norm_zero, zero_mul]

end Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

variable {Xo c}

variable {D : D7} (σ : c.F →+* ℂ) (V : HSp D) (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r) (mu : GA D V → ℂ)

def AdelMeas : Prop :=
  ∀ (la : ∀ k, Wt ((U σ).X k).Ψ r) (P : FDSec (U σ).X), IsHolCusp (U σ).X la P →
    AEStronglyMeasurable (onQ V (adel V dict mu P)) (muQ1 V)

def AeDom : Prop :=
  ∀ (la : ∀ k, Wt ((U σ).X k).Ψ r) (P : FDSec (U σ).X), P ∈ holSub (U σ).X la →
    onQ V (adel V dict mu P) =ᵐ[muQ1 V] 0 → ∀ k, ∀ x ∈ ((U σ).X k).dom, P k x = 0

variable {U σ V dict mu}

theorem aesm_of_holSub (hm : AdelMeas U σ V dict mu) (la : ∀ k, Wt ((U σ).X k).Ψ r) {P : FDSec (U σ).X}
    (hP : P ∈ holSub (U σ).X la) : AEStronglyMeasurable (onQ V (adel V dict mu P)) (muQ1 V) := by
  induction hP using Submodule.span_induction with
  | mem P hP => exact hm la P hP
  | zero => rw [map_zero, map_zero]; exact aestronglyMeasurable_const
  | add P Q _ _ h1 h2 => rw [map_add (f := _), map_add (f := _)]; exact h1.add h2
  | smul a P _ h1 => rw [map_smul, map_smul]; exact h1.const_smul a

theorem cusp_L2_of_measurable (hσ : GoodEmb c σ) (hd : ∀ g, (dict g).2 ∈ ((U σ).X (dict g).1).dom)
    (hmu : MuUnit V dict mu) (hm : AdelMeas U σ V dict mu) : CuspL2 U σ V dict mu := by
  intro a n _ f
  have hhol : rdU (U σ) (f : Rul Xo c) ∈ holSub (U σ).X (laU (U σ) a n) :=
    ((mem_cusp Xo c U a n f).1 f.2).2 σ hσ
  have hfin := supE_cusp_ne_top hσ f.2
  show MemLp (onQ V (adel V dict mu (rdU (U σ) (f : Rul Xo c)))) 2 (muQ1 V)
  refine MemLp.of_bound (aesm_of_holSub hm _ hhol) (supN (U σ).X (laU (U σ) a n) (rdU (U σ) (f : Rul Xo c)))
    (Filter.Eventually.of_forall fun q => ?_)
  set g := q.out
  show ‖mu g * rdU (U σ) (f : Rul Xo c) (dict g).1 (dict g).2‖ ≤ _
  rw [norm_mul, hmu.2.1 g, one_mul, ← pnorm_eq_of_unit ((U σ).X (dict g).1) (laU (U σ) a n (dict g).1)
    (rdU (U σ) (f : Rul Xo c) (dict g).1) (dict g).2 (hmu.2.2.2 g)]
  show _ ≤ (supE (U σ).X (laU (U σ) a n) (rdU (U σ) (f : Rul Xo c))).toReal
  rw [← ENNReal.ofReal_le_iff_le_toReal hfin]
  exact le_iSup (fun p : FPt (U σ).X => ENNReal.ofReal (((U σ).X p.1).pnorm (laU (U σ) a n p.1)
    (rdU (U σ) (f : Rul Xo c) p.1) p.2)) ⟨(dict g).1, ⟨(dict g).2, hd g⟩⟩

theorem l2Def_of_cusp (hσ : GoodEmb c σ) (hsup : SupDef Xo c U) (hae : AeDom U σ V dict mu)
    (h : CuspL2 U σ V dict mu) : L2DefiniteCuspForms U σ V dict mu h := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro a n hdom f h0
    have hhol : rdU (U σ) (f : Rul Xo c) ∈ holSub (U σ).X (laU (U σ) a n) :=
      ((mem_cusp Xo c U a n f).1 f.2).2 σ hσ
    have hz : (h a n hdom f).toLp _ = 0 := norm_eq_zero.1 h0
    have hz' : jFn V σ (rdC U σ a n) dict mu f =ᵐ[muQ1 V] 0 :=
      (MemLp.coeFn_toLp (h a n hdom f)).symm.trans (Lp.eq_zero_iff_ae_eq_zero.1 hz)
    have hv := hae (laU (U σ) a n) (rdU (U σ) (f : Rul Xo c)) hhol hz'
    have hE : supE (U σ).X (laU (U σ) a n) (rdU (U σ) (f : Rul Xo c)) = 0 := by
      refine le_antisymm (iSup_le fun p => ?_) zero_le
      rw [pnorm_of_eq_zero _ _ _ _ (hv p.1 p.2 p.2.2), ENNReal.ofReal_zero]
    have hN : supN (U σ).X (laU (U σ) a n) (rdU (U σ) (f : Rul Xo c)) = 0 := by
      unfold supN
      rw [hE, ENNReal.toReal_zero]
    exact Subtype.ext (hsup a n hdom σ hσ f f.2 hN)

theorem dict_dom_of {Comp : Type} {X : Comp → Data E r} {V : HSp D} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {Kf : Subgroup (GA D V)} {th} {hr}
    (h : DictIsUnif V dict Kf th hr) : ∀ g, (dict g).2 ∈ (X (dict g).1).dom :=
  h.2.2.2.1

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.NormalizedValuationMul
section
noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}

structure SecPt (ζ : PtsG G la) (y : E.Pt' la) where

  T : CDVR

  ep_pos : 0 < ep (unifO (xplus X E hM) la G.N) ζ

  ev : Rp (xplus X E hM) la G.N →+* T.Fr

  hv : ∀ (w : WeightFamilies.Wt D j) (F : B.Cusp j w), E.vAt' la y (X.inc w F) =
    nval T.V (ep (unifO (xplus X E hM) la G.N) ζ) (ev (emb (xplus X E hM) la G.N (X.inc w F)))

  onS : ∀ i : Fin (WeightFamilies.dimY D j), ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w i.succ) = 0

  s0 : IsUnit (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0))

  ord : ∀ x : ↥(Frac0 (xplus X E hM) la G.w),
    toE (ord (unifO (xplus X E hM) la G.N) ζ (toOsK (xplus X E hM) la G.w x)) =
      nval T.V 1 (IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0) s0 (x : Lw (xplus X E hM) la G.w))

structure FromW (ζ : PtsG G la) (y : E.Pt' la) extends SecPt ζ y where

  ι : Loc ζ →+* T.V

  loc : IsLocalHom ι
  unr : ∃ ϖ : Loc ζ, Irreducible ϖ ∧ Irreducible (ι ϖ)

  evW : ∀ (x : ↥(Frac0 (xplus X E hM) la G.w)) (a : ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))),
    toOsK (xplus X E hM) la G.w x = (a : OsK (xplus X E hM) la G.w) →
    IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0) toSecPt.s0 (x : Lw (xplus X E hM) la G.w) =
      algebraMap T.V T.Fr (ι (algebraMap _ (Loc ζ) a))

def secQ (y : PtsG G la → E.Pt' la) (hs : ∀ ζ, SecPt ζ (y ζ)) (g0 : B.Cusp j wF) : LocalPointData G la where
  y ζ := .inr (y ζ)
  g0 := g0
  c ζ := vV (hs ζ).T.V ((hs ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0)))

def InTieSecSt : Prop :=
  ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E)
    (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (S : Scal B)
    (y : PtsG G la → E.Pt' la) (hs : ∀ ζ, SecPt ζ (y ζ)) (g0 : B.Cusp j wF),
    (∀ ζ, (xplus X E hM).depth S.sW wL la (.inr (y ζ)) =
      nval (hs ζ).T.V (ep (unifO (xplus X E hM) la G.N) ζ) ((hs ζ).ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0))) →
    (j < D.R.m → ∀ ζ, (hs ζ).ev (emb (xplus X E hM) la G.N (X.inc _ G.et)) ≠ 0) →
    (∀ ζ, (hs ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0)) ≠ 0) →
    IsGen (OsK (xplus X E hM) la G.w) (resF G la g0) →
    (secQ y hs g0).InTie S

section Nval

variable {T : CDVR}

lemma vV_one' : vV T.V (1 : T.Fr) = 0 := by simp [vV]

lemma vV_inv' {b : T.Fr} (hb : b ≠ 0) : vV T.V b⁻¹ = - vV T.V b := by
  have h := vV_mul (V := T.V) hb (inv_ne_zero hb)
  rw [mul_inv_cancel₀ hb, vV_one'] at h
  omega

lemma vV_pow' {b : T.Fr} (hb : b ≠ 0) (k : ℕ) : vV T.V (b ^ k) = k * vV T.V b := by
  induction k with
  | zero => simp [vV_one']
  | succ n ih => rw [pow_succ, vV_mul (pow_ne_zero n hb) hb, ih]; push_cast; ring

lemma nval_frac {e : ℕ} (he : 0 < e) (a b : T.Fr) (hb : b ≠ 0) (k : ℕ) :
    nval T.V 1 (a * (b⁻¹) ^ k) = (e : EReal) * (nval T.V e a - (k : EReal) * nval T.V e b) := by
  rw [nval_of_ne hb]
  by_cases ha : a = 0
  · subst ha
    rw [zero_mul, nval_zero, nval_zero]
    have hk : (k : EReal) * (((vV T.V b : ℝ) / e : ℝ) : EReal) = ((k * ((vV T.V b : ℝ) / e) : ℝ) : EReal) := by
      norm_cast
    rw [hk, EReal.top_sub_coe, EReal.mul_top_of_pos (by exact_mod_cast he)]
  · have hab : a * (b⁻¹) ^ k ≠ 0 := mul_ne_zero ha (pow_ne_zero k (inv_ne_zero hb))
    rw [nval_of_ne hab, nval_of_ne ha, vV_mul ha (pow_ne_zero k (inv_ne_zero hb)), vV_pow' (inv_ne_zero hb),
      vV_inv' hb]
    have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    have : (((vV T.V a : ℤ) + (k : ℤ) * -vV T.V b : ℤ) : ℝ) / ((1 : ℕ) : ℝ) =
        (e : ℝ) * ((vV T.V a : ℝ) / e - k * ((vV T.V b : ℝ) / e)) := by
      push_cast; field_simp; ring
    rw [this]
    norm_cast

lemma e_mul_nval {e : ℕ} (he : 0 < e) (x : T.Fr) : (e : EReal) * nval T.V e x = nval T.V 1 x := by
  by_cases hx : x = 0
  · subst hx; rw [nval_zero, nval_zero, EReal.mul_top_of_pos (by exact_mod_cast he)]
  · rw [nval_of_ne hx, nval_of_ne hx]
    have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    have : (e : ℝ) * ((vV T.V x : ℝ) / e) = (vV T.V x : ℝ) / ((1 : ℕ) : ℝ) := by
      rw [Nat.cast_one, div_one]; field_simp
    rw [← this]; norm_cast

end Nval

lemma normalized_valuation_mul {T : CDVR} {e : ℕ} (he : 0 < e) (b : T.Fr) (hb : b ≠ 0) :
    (e : ℝ) * (nval T.V e b).toReal = (vV T.V b : ℝ) := by
  rw [nval_of_ne hb, EReal.toReal_coe]
  have : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  field_simp

lemma toE_add_coe (a : WithTop ℤ) (n : ℤ) : toE (a + (n : WithTop ℤ)) = toE a + ((n : ℝ) : EReal) := by
  cases a with
  | top => simp [toE]
  | coe m =>
    show toE ((m + n : ℤ) : WithTop ℤ) = toE (m : WithTop ℤ) + ((n : ℝ) : EReal)
    simp only [toE]; push_cast; rfl

section Lift

variable {ζ : PtsG G la} {y₀ : E.Pt' la} (h : SecPt ζ y₀)

abbrev SecPt.lift : Lw (xplus X E hM) la G.w →+* h.T.Fr :=
  IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0) h.s0

lemma SecPt.lift_alg (r : Rp (xplus X E hM) la G.N) : h.lift (algebraMap _ _ r) = h.ev r :=
  IsLocalization.lift_eq _ r

lemma SecPt.lift_w0inv : h.lift (w0inv (xplus X E hM) la G.w) = (h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0))⁻¹ := by
  have := congrArg h.lift (section_mul_inverse_eq_one (xplus X E hM) la G.w)
  rw [map_mul, h.lift_alg, map_one] at this
  exact eq_inv_of_mul_eq_one_right this

lemma SecPt.lift_frac (k : ℕ) (g : Rp (xplus X E hM) la G.N) :
    h.lift (frac (xplus X E hM) la G.w k g) = h.ev g * (h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0))⁻¹ ^ k := by
  rw [frac_apply, map_mul, map_pow, h.lift_alg, h.lift_w0inv]

lemma SecPt.lift_Jid {r : ↥(Frac0 (xplus X E hM) la G.w)} (hr : r ∈ Jid (xplus X E hM) la G.w) :
    h.lift (r : Lw (xplus X E hM) la G.w) = 0 := by
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [coe_sfr, h.lift_frac, h.onS i, zero_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [Subalgebra.coe_add, map_add (f := _), hx, hy, add_zero]
  | smul a x _ hx => rw [smul_eq_mul, Subalgebra.coe_mul, map_mul, hx, mul_zero]

lemma SecPt.lift_JHK {u : WeightFamilies.Wt D j} {z : ↥(HK (xplus X E hM) la G.w u)}
    (hz : z ∈ Jid (xplus X E hM) la G.w • (⊤ : Submodule ↥(Frac0 (xplus X E hM) la G.w) ↥(HK (xplus X E hM) la G.w u))) :
    h.lift (z : Lw (xplus X E hM) la G.w) = 0 := by
  refine Submodule.smul_induction_on
    (p := fun z : ↥(HK (xplus X E hM) la G.w u) => h.lift (z : Lw (xplus X E hM) la G.w) = 0) hz ?_ ?_
  · intro r hr m _
    rw [Submodule.coe_smul, Algebra.smul_def, map_mul]
    have : h.lift (algebraMap ↥(Frac0 (xplus X E hM) la G.w) (Lw (xplus X E hM) la G.w) r) = 0 := h.lift_Jid hr
    rw [this, zero_mul]
  · intro x y hx hy
    rw [Submodule.coe_add, map_add (f := _), hx, hy, add_zero]

end Lift

theorem inTieSec : InTieSecSt := by
  intro D B P j X E hM ka wL wF G la S y hs g0 hdep het hg0 hgen ζ
  have hd := hdep ζ
  have hg0' := hg0 ζ
  have het' : j < D.R.m → (hs ζ).ev (emb (xplus X E hM) la G.N (X.inc _ G.et)) ≠ 0 := fun hj => het hj ζ
  set h := hs ζ with hh
  have hb : h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0) ≠ 0 := h.s0.ne_zero
  have he := h.ep_pos
  have hvat : ∀ (w : WeightFamilies.Wt D j) (F : B.Cusp j w), (xplus X E hM).vAt la (.inr (y ζ)) ((xplus X E hM).inc w F) =
      nval h.T.V (ep (unifO (xplus X E hM) la G.N) ζ) (h.ev (emb (xplus X E hM) la G.N (X.inc w F))) :=
    fun w F => h.hv w F
  have hQy : (secQ y hs g0).y ζ = .inr (y ζ) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hQy, hd, nval_of_ne hb]; exact EReal.coe_ne_top _
  · rw [hQy, hd, nval_of_ne hb]; exact EReal.coe_ne_bot _
  · intro hj
    rw [hQy, hvat, nval_of_ne (het' hj)]; exact EReal.coe_ne_top _
  · refine ⟨vV h.T.V (h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0)), ?_⟩
    simp only [LocalPointData.nu, hQy, hd]
    exact normalized_valuation_mul he _ (hs ζ).s0.ne_zero
  · change (((vV h.T.V (h.ev (emb (xplus X E hM) la G.N (X.inc wF g0))) : ℤ) : ℝ) : EReal) =
      (ep (unifO (xplus X E hM) la G.N) ζ : EReal) * (xplus X E hM).vAt la (.inr (y ζ)) ((xplus X E hM).inc wF g0)
    rw [hvat, e_mul_nval he, nval_of_ne hg0']
    simp
  · intro k g
    rw [h.ord, coe_weightZeroFraction, h.lift_frac, nval_frac he _ _ hb, hQy, hvat, hd]
    rfl
  · intro k g
    have hgen' : IsGen (OsK (xplus X E hM) la G.w) ((secQ y hs g0).e) := hgen
    set a := toA0K (xplus X E hM) la G.w wF (toHK (xplus X E hM) la G.w wF k
      ⟨emb (xplus X E hM) la G.N ((xplus X E hM).inc _ g), emb_mem_Vw (xplus X E hM) la G.N _ g⟩) with ha
    obtain ⟨x, hx⟩ := toOsK_surjective (xplus X E hM) la G.w (coord ((secQ y hs g0).e) a)
    have hca : coord ((secQ y hs g0).e) a • (secQ y hs g0).e = a := coord_smul_self hgen' a
    have h1 : toA0K (xplus X E hM) la G.w wF (x • toHK0 (xplus X E hM) la G.w wF
        ⟨emb (xplus X E hM) la G.N (X.inc wF g0), emb_mem_Vw (xplus X E hM) la G.N wF g0⟩) = a := by
      rw [map_smul, ← restriction_apply_eq_reduction, ← hca, ← hx]
      exact (algebraMap_smul (OsK (xplus X E hM) la G.w) x _).symm
    have h2 := (Submodule.Quotient.eq _).1 h1
    have h3 := h.lift_JHK h2
    rw [Submodule.coe_sub, map_sub, sub_eq_zero, Submodule.coe_smul, Algebra.smul_def, map_mul, coe_toHK0,
      coe_toHK, h.lift_alg] at h3
    have h3' : h.lift (x : Lw (xplus X E hM) la G.w) * h.ev (emb (xplus X E hM) la G.N (X.inc wF g0)) =
        h.lift (frac (xplus X E hM) la G.w k (emb (xplus X E hM) la G.N ((xplus X E hM).inc _ g))) := h3
    have hord := h.ord x
    rw [hx] at hord
    simp only [LocalPointData.ordA, ordV]
    rw [toE_add_coe, hord]
    change nval h.T.V 1 (h.lift (x : Lw (xplus X E hM) la G.w)) +
      (((vV h.T.V (h.ev (emb (xplus X E hM) la G.N (X.inc wF g0))) : ℤ) : ℝ) : EReal) = _
    have hm := nval_mul (V := h.T.V) 1 (h.lift (x : Lw (xplus X E hM) la G.w))
      (h.ev (emb (xplus X E hM) la G.N (X.inc wF g0)))
    rw [h3', nval_of_ne hg0'] at hm
    have hc : (((vV h.T.V (h.ev (emb (xplus X E hM) la G.N (X.inc wF g0))) : ℤ) : ℝ) : EReal) =
        (((vV h.T.V (h.ev (emb (xplus X E hM) la G.N (X.inc wF g0))) : ℝ) / ((1 : ℕ) : ℝ) : ℝ) : EReal) := by simp
    rw [hc, ← hm, h.lift_frac, nval_frac he _ _ hb, hQy, hvat, hd]
    rfl

end Formalism.L2.Pj
end
end

