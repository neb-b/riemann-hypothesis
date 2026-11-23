module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsMvPolynomialOfPolyBoundOffHypersurface
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IntegralAndRationalOfPolynomialGrowth
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1140
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1144
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermPairSectionsChangeOfIsometricCombinati
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSNef.ChangePair
open GlobalTheory.VolBr.NuEq
variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem exists_chart (M : HermLB p) (x : X) : ∃ c, x ∈ M.B.U c := by
  have h : x ∈ (⨆ c, M.B.U c) := by rw [M.isLB.cover]; trivial
  exact TopologicalSpace.Opens.mem_iSup.1 h

theorem loc_eq (P : Pair p) (a b a' b' i j : ℤ) (f : X.functionField) (ρ ρ' : X.functionFieldˣ) (e g) :
    f * (ρ : X.functionField) ^ i * (ρ' : X.functionField) ^ j =
      P.loc (i * a + j * a') (i * b + j * b') f e g *
        (((ρ : X.functionField) / P.loc a b 1 e g) ^ i * ((ρ' : X.functionField) / P.loc a' b' 1 e g) ^ j) := by
  have hs : (P.r e : X.functionField) ≠ 0 := (P.r e).ne_zero
  have ht : (P.r' g : X.functionField) ≠ 0 := (P.r' g).ne_zero
  simp only [Pair.loc, one_mul]
  rw [div_zpow, div_zpow, mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul,
    zpow_add₀ hs, zpow_add₀ ht, mul_comm a i, mul_comm b i, mul_comm a' j, mul_comm b' j]
  have h1 := zpow_ne_zero (i * a) hs
  have h2 := zpow_ne_zero (i * b) ht
  have h3 := zpow_ne_zero (j * a') hs
  have h4 := zpow_ne_zero (j * b') ht
  field_simp

end GlobalTheory.HSNef.ChangePair

namespace GlobalTheory.HSNef


open GlobalTheory.VolBr.NuEq ChangePair in
theorem change_pair : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (a b a' b' : ℤ) (M N : HermLB p), P.Rep a b M → P.Rep a' b' N → ∃ Q : Pair p, Q.L = M ∧ Q.A = N ∧ ∀ (i j : ℤ) (R : ℝ), Q.Bl i j R = P.Bl (i * a + j * a') (i * b + j * b') R := by
  intro k _ X _ p P a b a' b' M N ⟨ρ, hρ, hu, hn⟩ ⟨ρ', hρ', hu', hn'⟩
  let Q : Pair p := ⟨M, N, ρ, ρ', hρ, hρ'⟩
  have hw : ∀ (i j : ℤ) (x : X) c d e g, x ∈ M.B.U c → x ∈ N.B.U d → x ∈ P.L.B.U e → x ∈ P.A.B.U g →
      UnitAt x (((ρ c : X.functionField) / P.loc a b 1 e g) ^ i *
        ((ρ' d : X.functionField) / P.loc a' b' 1 e g) ^ j) :=
    fun i j x c d e g hc hd he hg =>
      (NuEq.unitAt_zpow (hu x c e g hc he hg) i).mul (NuEq.unitAt_zpow (hu' x d e g hd he hg) j)
  have hH : ∀ i j : ℤ, Q.H i j = P.H (i * a + j * a') (i * b + j * b') := by
    intro i j
    ext f
    constructor
    · intro hf x e g he hg
      obtain ⟨c, hc⟩ := exists_chart M x
      obtain ⟨d, hd⟩ := exists_chart N x
      have hW := hw i j x c d e g hc hd he hg
      have h := hf x c d hc hd
      change RegAt x (f * _ ^ i * _ ^ j) at h
      rw [loc_eq P a b a' b' i j f (ρ c) (ρ' d) e g] at h
      have h' := h.mul hW.inv.regAt
      rwa [mul_assoc, mul_inv_cancel₀ hW.ne_zero, mul_one] at h'
    · intro hf x c d hc hd
      obtain ⟨e, he⟩ := exists_chart P.L x
      obtain ⟨g, hg⟩ := exists_chart P.A x
      change RegAt x (f * _ ^ i * _ ^ j)
      rw [loc_eq P a b a' b' i j f (ρ c) (ρ' d) e g]
      exact (hf x e g he hg).mul (hw i j x c d e g hc hd he hg).regAt
  have hnu : ∀ (i j : ℤ) (f : X.functionField), f ∈ P.H (i * a + j * a') (i * b + j * b') →
      ∀ (σ : k →+* ℂ) (y : CxPts p σ), Q.nu i j σ y f = P.nu (i * a + j * a') (i * b + j * b') σ y f := by
    intro i j f hf σ y
    have hc := mem_pick (M.φ σ).isLB y
    have hd := mem_pick (N.φ σ).isLB y
    have he := mem_pick (P.L.φ σ).isLB y
    have hg := mem_pick (P.A.φ σ).isLB y
    set c := pick (M.φ σ).isLB y
    set d := pick (N.φ σ).isLB y
    set e := pick (P.L.φ σ).isLB y
    set g := pick (P.A.φ σ).isLB y
    have hfQ : f ∈ Q.H i j := (hH i j).symm ▸ hf
    rw [nu_eq k X p Q i j f hfQ σ y c d hc hd, nu_eq k X p P _ _ f hf σ y e g he hg]
    have hU := hu _ c e g (mem_ptsIn.1 hc) (mem_ptsIn.1 he) (mem_ptsIn.1 hg)
    have hU' := hu' _ d e g (mem_ptsIn.1 hd) (mem_ptsIn.1 he) (mem_ptsIn.1 hg)
    have hreg : RegAt (under y) (P.loc (i * a + j * a') (i * b + j * b') f e g) :=
      hf _ e g (mem_ptsIn.1 he) (mem_ptsIn.1 hg)
    have eU : ‖ratVal ((ρ c : X.functionField) / P.loc a b 1 e g) y‖ =
        Real.exp ((M.φ σ).φ c y / 2 - (a * (P.L.φ σ).φ e y + b * (P.A.φ σ).φ g y) / 2) := by
      rw [← Real.exp_log (norm_pos_iff.2 (ratVal_ne_zero hU))]
      congr 1
      linarith [hn σ y c e g hc he hg]
    have eU' : ‖ratVal ((ρ' d : X.functionField) / P.loc a' b' 1 e g) y‖ =
        Real.exp ((N.φ σ).φ d y / 2 - (a' * (P.L.φ σ).φ e y + b' * (P.A.φ σ).φ g y) / 2) := by
      rw [← Real.exp_log (norm_pos_iff.2 (ratVal_ne_zero hU'))]
      congr 1
      linarith [hn' σ y d e g hd he hg]
    change ‖ratVal (f * _ ^ i * _ ^ j) y‖ * _ = _
    rw [loc_eq P a b a' b' i j f (ρ c) (ρ' d) e g,
      ratVal_mul hreg ((NuEq.unitAt_zpow hU i).mul (NuEq.unitAt_zpow hU' j)).regAt,
      ratVal_mul (NuEq.unitAt_zpow hU i).regAt (NuEq.unitAt_zpow hU' j).regAt,
      ratVal_zpow' hU, ratVal_zpow' hU', norm_mul, norm_mul, norm_zpow, norm_zpow, eU, eU',
      ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.exp_mul, ← Real.exp_mul, mul_assoc,
      ← Real.exp_add, ← Real.exp_add]
    congr 2
    push_cast
    ring
  refine ⟨Q, rfl, rfl, fun i j R => ?_⟩
  ext f
  constructor
  · rintro ⟨hf, hR⟩
    have hf' : f ∈ P.H (i * a + j * a') (i * b + j * b') := hH i j ▸ hf
    exact ⟨hf', fun σ y => hnu i j f hf' σ y ▸ hR σ y⟩
  · rintro ⟨hf, hR⟩
    exact ⟨(hH i j).symm ▸ hf, fun σ y => (hnu i j f hf σ y).symm ▸ hR σ y⟩

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEqOfPolynomialGrowth
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.CxPts

namespace GlobalTheory.SerreSections

theorem exists_ringHom_of_denominator {P A : Type*} [CommRing P] [CommRing A] (α : P →+* A) (e : P →+* ℂ) (q : P)
    (hq : e q ≠ 0) (hk : ∀ s, α s = 0 → e s = 0) (r : A → P) (hr : ∀ b, α q * b = α (r b)) :
    ∃ χ : A →+* ℂ, (∀ b, χ b = e (r b) / e q) ∧ ∀ s, χ (α s) = e s := by
  have hk' (s s' : P) (h : α s = α s') : e s = e s' :=
    sub_eq_zero.1 ((map_sub e s s').symm.trans (hk _ (by rw [map_sub, h, sub_self])))
  have h1 (s : P) : e (r (α s)) / e q = e s := by
    rw [div_eq_iff hq, ← map_mul]
    exact hk' _ _ (by rw [← hr, map_mul, mul_comm])
  refine ⟨{ toFun := fun b => e (r b) / e q, map_one' := ?_, map_mul' := fun a b => ?_,
            map_zero' := ?_, map_add' := fun a b => ?_ }, fun _ => rfl, h1⟩
  · simpa using h1 1
  · have := hk' (q * r (a * b)) (r a * r b) (by simp only [map_mul, ← hr]; ring)
    simp only [map_mul] at this
    field_simp
    linear_combination this
  · simpa using h1 0
  · rw [← add_div, ← map_add (f := _)]
    congr 1
    exact hk' _ _ (by simp only [map_add (f := _), ← hr]; ring)

section Along

variable {Y : Scheme.{0}} {p : Y ⟶ Sp ℂ} {σ : ℂ →+* ℂ} {D : ℕ} {E : Type} [NormedAddCommGroup E]
  [NormedSpace ℂ E] {U : Y.Opens} {Z : Set E} {z : E} {s : E → CxPts p σ}

theorem exists_analyticAt_ev (hU : IsAffineOpen U) (hz : z ∈ Z) (hs : ∀ w ∈ Z, s w ∈ ptsIn p σ U)
    (hc : ContinuousWithinAt s Z z)
    (hd : ∀ a : Γ(Y, U), ∃ F : E → ℂ, AnalyticAt ℂ F z ∧ ∀ w ∈ Z, ev p σ U a (s w) = F w)
    {W : Y.Opens} (hW : s z ∈ ptsIn p σ W) (f : Γ(Y, W)) :
    ∃ F : E → ℂ, AnalyticAt ℂ F z ∧ ∀ᶠ w in 𝓝[Z] z, ev p σ W f (s w) = F w := by
  obtain ⟨h, hhW, hh⟩ := hU.exists_basicOpen_le (V := W) ⟨_, mem_ptsIn.1 hW⟩ (mem_ptsIn.1 (hs z hz))
  have hB : s z ∈ ptsIn p σ (Y.basicOpen h) := mem_ptsIn.2 hh
  have := hU.isLocalization_basicOpen h
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj h (resG Y hhW f)
  obtain ⟨Fa, hFa, ea⟩ := hd a
  obtain ⟨Fh, hFh, eh⟩ := hd h
  refine ⟨fun w => Fa w * (Fh w ^ n)⁻¹, hFa.mul ((hFh.pow n).inv (pow_ne_zero n
    (eh z hz ▸ (mem_ptsIn_basicOpen (hs z hz) h).1 hB))), ?_⟩
  filter_upwards [hc.preimage_mem_nhdsWithin ((isOpen_ptsIn _).mem_nhds hB), self_mem_nhdsWithin] with w hw hwZ
  have ha' : resG Y hhW f * resG Y (Y.basicOpen_le h) h ^ n = resG Y (Y.basicOpen_le h) a := ha
  have e := congrArg (evHom hw) ha'
  rw [map_mul, map_pow, ← ev_eq, ← ev_eq, ← ev_eq, ev_res _ hw, ev_res _ hw, ev_res _ hw] at e
  rw [← ea w hwZ, ← eh w hwZ]
  exact (eq_mul_inv_iff_mul_eq₀
    (pow_ne_zero n ((mem_ptsIn_basicOpen (ptsIn_mono (Y.basicOpen_le h) hw) h).1 hw))).2 e

theorem exists_analyticAt_holo (R : AnRead p σ D) (hU : IsAffineOpen U) (hz : z ∈ Z)
    (hs : ∀ w ∈ Z, s w ∈ ptsIn p σ U)
    (hd : ∀ a : Γ(Y, U), ∃ F : E → ℂ, AnalyticAt ℂ F z ∧ ∀ w ∈ Z, ev p σ U a (s w) = F w)
    {φ : CxPts p σ → ℂ} (hφ : R.HoloOn (ptsIn p σ U) φ) :
    ∃ F : E → ℂ, AnalyticAt ℂ F z ∧ ∀ᶠ w in 𝓝[Z] z, φ (s w) = F w := by
  have hc : ContinuousWithinAt s Z z := tendsto_subtype_rng.2
    (Points.tendsto_of_isAffineOpen hU (hs z hz) (eventually_of_mem self_mem_nhdsWithin hs) fun a => by
      obtain ⟨F, hF, e⟩ := hd a
      exact hF.continuousAt.continuousWithinAt.congr e (e z hz))
  obtain ⟨i, hi⟩ := R.cover (s z)
  set c := R.chart i
  choose F hF e using fun a => exists_analyticAt_ev hU hz hs hc hd (c.source_subset hi) (c.x a)
  let X : E → ReciprocityTheory.L2DbarEstimates.V D := fun w => (EuclideanSpace.equiv (Fin D) ℂ).symm fun a => F a w
  have hX : AnalyticAt ℂ X z :=
    ((EuclideanSpace.equiv (Fin D) ℂ).symm.analyticAt _).comp (analyticAt_pi_iff.2 hF)
  have hev : ∀ᶠ w in 𝓝[Z] z, s w ∈ c.e.source ∧ X w = c.e (s w) := by
    filter_upwards [eventually_all.2 e, hc.preimage_mem_nhdsWithin (c.e.open_source.mem_nhds hi)] with w h₁ h₂
    refine ⟨h₂, ?_⟩
    ext a
    exact (h₁ a).symm.trans (c.apply_eq _ h₂ a).symm
  have hG : AnalyticAt ℂ (φ ∘ c.e.symm) (X z) := by
    rw [(hev.self_of_nhdsWithin hz).2]
    exact SCV.analyticAt_of_differentiableOn (hφ i)
      ((ChartGlue.isOpen_over _ (isOpen_ptsIn U)).mem_nhds (ChartGlue.mem_over _ hi (hs z hz)))
  refine ⟨(φ ∘ c.e.symm) ∘ X, hG.comp hX, hev.mono fun w hw => ?_⟩
  simp only [Function.comp_apply, hw.2, c.e.left_inv hw.1]

end Along

theorem analyticAt_eval_map {d : ℕ} (r : Polynomial (MvPolynomial (Fin d) ℂ)) (z : (Fin d → ℂ) × ℂ) :
    AnalyticAt ℂ (fun w : (Fin d → ℂ) × ℂ => (r.map (MvPolynomial.eval w.1)).eval w.2) z :=
  SCV.analyticOnNhd_of_differentiable ((FiniteCoverGrowth.contDiff_eval_map r).differentiable one_ne_zero)
    univ z trivial

theorem exists_sum_norm_le {A : Type*} [CommRing A] {d n : ℕ} (j : MvPolynomial (Fin d) ℂ →+* A)
    (hj : j.IsIntegral) (u : Fin n → A) : ∃ (K : ℝ) (M : ℕ), ∀ (x : Fin d → ℂ) (χ : A →+* ℂ),
      χ.comp j = MvPolynomial.eval x → 1 + ∑ l, ‖χ (u l)‖ ≤ K * (1 + ‖x‖) ^ M := by
  choose s hs hs' using fun l => hj (u l)
  choose K M hK h using fun l => FiniteCoverGrowth.exists_norm_root_le (s l) (hs l)
  refine ⟨1 + ∑ l, K l, ∑ l, M l, fun x χ hχ => ?_⟩
  have h0 : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  rw [add_mul, one_mul, Finset.sum_mul]
  refine add_le_add (one_le_pow₀ h0) (Finset.sum_le_sum fun l _ => (h l x _ ?_).trans ?_)
  · rw [Polynomial.eval_map, ← hχ, ← Polynomial.hom_eval₂, hs', map_zero]
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h0
      (Finset.single_le_sum (f := M) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l))) (hK l)

theorem exists_mul_eq_of_polynomial_growth : ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ) (D : ℕ), SmoothOfRelativeDimension D p → ∀ (R : AnRead p (RingHom.id ℂ) D) (V : Y.Opens), IsAffineOpen V → IsDomain Γ(Y, V) → ∀ φ : CxPts p (RingHom.id ℂ) → ℂ, R.HoloOn (ptsIn p (RingHom.id ℂ) V) φ → ∀ (n : ℕ) (u : Fin n → Γ(Y, V)) (C : ℝ) (m : ℕ), (∀ y ∈ ptsIn p (RingHom.id ℂ) V, ‖φ y‖ ≤ C * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m) → ∃ a b : Γ(Y, V), b ≠ 0 ∧ ∀ y ∈ ptsIn p (RingHom.id ℂ) V, ev p (RingHom.id ℂ) V b y * φ y = ev p (RingHom.id ℂ) V a y := by
  intro Y p D hs R V hV hd φ hφ n u C m hb
  classical
  have hsm : Smooth p := SmoothOfRelativeDimension.smooth D p
  have hc : (algX p V).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ _).comp
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
  letI : Algebra ℂ Γ(Y, V) := (algX p V).toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(Y, V) := hc
  obtain ⟨d, j, a, P, q, -, hinj, hfin, hP, -, hdvd, hq, hqP, hr⟩ := noetherNormalization_primitive Γ(Y, V)
  choose r hr using hr
  let α := Polynomial.eval₂RingHom j.toRingHom a
  let e (z : (Fin d → ℂ) × ℂ) := Polynomial.eval₂RingHom (MvPolynomial.eval z.1) z.2
  have he (z) (s) : e z s = (s.map (MvPolynomial.eval z.1)).eval z.2 := (Polynomial.eval_map _ _).symm
  have hα (f) : α (Polynomial.C f) = j f := Polynomial.eval₂_C _ _
  have heC (z) (f) : e z (Polynomial.C f) = MvPolynomial.eval z.1 f := Polynomial.eval₂_C _ _
  set Z : Set ((Fin d → ℂ) × ℂ) := {z | MvPolynomial.eval z.1 q ≠ 0 ∧
    (P.map (MvPolynomial.eval z.1)).eval z.2 = 0}
  have hχ (z) (hz : z ∈ Z) := exists_ringHom_of_denominator α (e z) (Polynomial.C q) (heC z q ▸ hz.1)
    (fun s h => by
      obtain ⟨t, rfl⟩ := (hdvd s).1 h
      rw [map_mul, he, hz.2, zero_mul]) r fun b => by rw [hα]; exact hr b
  choose χ hχ hχ' using hχ
  have hχj (z) (hz : z ∈ Z) (f) : χ z hz (j f) = MvPolynomial.eval z.1 f := by rw [← hα, hχ', heC]
  have hχc (z) (hz : z ∈ Z) (c : ℂ) : χ z hz (algX p V c) = RingHom.id ℂ c :=
    (congrArg _ (j.commutes c).symm).trans ((hχj z hz _).trans (MvPolynomial.eval_C _))
  have hb0 : j q * α P.derivative ≠ 0 := by
    have h0 : j q ≠ 0 := (map_ne_zero_iff _ hinj).2 hq
    refine mul_ne_zero h0 fun h => h0 ?_
    obtain ⟨v, w, hvw⟩ := Ideal.mem_span_pair.1 hqP
    rw [← hα, ← hvw, map_add (f := _), map_mul, map_mul, h, show α P = 0 from (hdvd P).2 dvd_rfl]
    simp
  rcases (ptsIn p (RingHom.id ℂ) V).eq_empty_or_nonempty with hE | ⟨y₀, -⟩
  · exact ⟨0, 1, one_ne_zero, by simp [hE]⟩
  let s (z : (Fin d → ℂ) × ℂ) : CxPts p (RingHom.id ℂ) :=
    if hz : z ∈ Z then ofHom hV (χ z hz) (hχc z hz) else y₀
  have hsV (z) (hz : z ∈ Z) : s z ∈ ptsIn p (RingHom.id ℂ) V := by
    simp only [s, dif_pos hz]; exact ofHom_mem _ _ _
  have hsv (z) (hz : z ∈ Z) (b) : ev p (RingHom.id ℂ) V b (s z) = χ z hz b := by
    simp only [s, dif_pos hz]; exact ev_ofHom _ _ _ b
  obtain ⟨K, M, hK⟩ := exists_sum_norm_le j.toRingHom hfin.to_isIntegral u
  obtain ⟨-, t, ht⟩ := FiniteCoverGrowth.integral_and_rational_of_polynomial_growth
    isConnected_and_dense_compl_hypersurface exists_mvPolynomial_of_poly_bound_off_hypersurface
    d (M * m) P q (fun z => φ (s z)) (|C| * K ^ m) hP hq hqP
    (fun z hz => exists_analyticAt_holo R hV hz hsV (fun b => ⟨fun w => e w (r b) / e w (Polynomial.C q), by
      simp only [he]
      exact (analyticAt_eval_map _ z).div (analyticAt_eval_map _ z) (by rw [← he, heC]; exact hz.1),
      fun w hw => (hsv w hw b).trans (hχ w hw b)⟩) hφ)
    fun z hz => by
      refine (hb _ (hsV z hz)).trans ?_
      simp only [hsv z hz]
      rw [mul_assoc, pow_mul, ← mul_pow]
      exact mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (by positivity)
        (hK z.1 _ (RingHom.ext (hχj z hz))) m) (by positivity) (abs_nonneg C)
  refine ⟨j q * α t, j q * α P.derivative, hb0, fun y hy => ?_⟩
  simp only [ev_eq hy, map_mul]
  by_cases h0 : evHom hy (j q) = 0
  · simp [h0]
  let z : (Fin d → ℂ) × ℂ := (fun k => evHom hy (j (MvPolynomial.X k)), evHom hy a)
  have hj : (evHom hy).comp j.toRingHom = MvPolynomial.eval z.1 :=
    MvPolynomial.ringHom_ext (fun c => by
      rw [MvPolynomial.eval_C]
      exact (congrArg _ (j.commutes c)).trans ((ev_eq hy _).symm.trans (ev_algX hy c))) fun k => by simp [z]
  have hez (f) : evHom hy (α f) = e z f := by
    change _ = Polynomial.eval₂ _ _ _
    rw [← hj]
    exact Polynomial.hom_eval₂ _ _ _ _
  have hz : z ∈ Z := ⟨by rwa [← heC, ← hez, hα], by
    rw [← he, ← hez, show α P = 0 from (hdvd P).2 dvd_rfl, map_zero]⟩
  have hsz : s z = y := Subtype.ext (Points.ext_of_valR hV (hsV z hz) hy fun b => by
    refine (hsv z hz b).trans (Eq.trans ?_ (ev_eq hy b).symm)
    rw [hχ, ← hez, ← hez, hα, div_eq_iff h0, ← map_mul, mul_comm, hr]
    rfl)
  rw [mul_assoc, hez, hez, he, he, ← ht z hz, hsz]

end GlobalTheory.SerreSections
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupsIntegers
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.SBBox

theorem exists_nhds_zero_add_eq {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] {Y : Type}
    [Zero Y] {g : X → Y} (hg : IsLocallyConstant g) (hc : HasCompactSupport g) :
    ∃ N ∈ nhds (0 : X), ∀ y, ∀ u ∈ N, g (y + u) = g y := by
  classical
  have hW : ∀ x : X, ∃ W ∈ nhds (0 : X), ∀ a ∈ W, ∀ b ∈ W, g (x + (a + b)) = g x := by
    intro x
    have h1 : (fun u => x + u) ⁻¹' {y | g y = g x} ∈ nhds (0 : X) := by
      refine (hg.isOpen_fiber (g x)).preimage (continuous_const.add continuous_id) |>.mem_nhds ?_
      simp
    obtain ⟨W, hW, hWW⟩ := exists_nhds_zero_half h1
    exact ⟨W, hW, fun a ha b hb => hWW a ha b hb⟩
  choose W hW0 hWg using hW
  let V : X → Set X := fun x => W x ∩ Neg.neg ⁻¹' W x
  have hV0 : ∀ x, V x ∈ nhds (0 : X) := fun x => Filter.inter_mem (hW0 x) (neg_mem_nhds_zero X (hW0 x))
  have hcov : tsupport g ⊆ ⋃ x : X, (fun y => y - x) ⁻¹' interior (V x) := by
    intro x _
    refine Set.mem_iUnion.2 ⟨x, ?_⟩
    simp only [Set.mem_preimage, sub_self]
    exact mem_interior_iff_mem_nhds.2 (hV0 x)
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (fun x => (fun y => y - x) ⁻¹' interior (V x))
    (fun x => isOpen_interior.preimage (continuous_id.sub continuous_const)) hcov
  refine ⟨⋂ x ∈ t, V x, (Filter.biInter_finset_mem t).2 fun x _ => hV0 x, fun y u hu => ?_⟩
  have hu' : ∀ x ∈ t, u ∈ W x ∧ -u ∈ W x := fun x hx => by
    have := Set.mem_iInter₂.1 hu x hx
    exact ⟨this.1, this.2⟩
  have h0 : ∀ x, (0 : X) ∈ W x := fun x => mem_of_mem_nhds (hW0 x)
  by_cases hy : y ∈ tsupport g
  · obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hy)
    have hyx' : y - x ∈ W x := (interior_subset hyx : y - x ∈ V x).1
    have e1 : g (y + u) = g x := by
      have := hWg x (y - x) hyx' u (hu' x hx).1
      rwa [show x + (y - x + u) = y + u by abel] at this
    have e2 : g y = g x := by
      have := hWg x (y - x) hyx' 0 (h0 x)
      rwa [show x + (y - x + 0) = y by abel] at this
    rw [e1, e2]
  · by_cases hyu : y + u ∈ tsupport g
    · obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hyu)
      have hyx' : y + u - x ∈ W x := (interior_subset hyx : y + u - x ∈ V x).1
      have e1 : g y = g x := by
        have := hWg x (y + u - x) hyx' (-u) (hu' x hx).2
        rwa [show x + (y + u - x + -u) = y by abel] at this
      have e2 : g (y + u) = g x := by
        have := hWg x (y + u - x) hyx' 0 (h0 x)
        rwa [show x + (y + u - x + 0) = y + u by abel] at this
      rw [e1, e2]
    · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyu]

variable {F : Type} [Field F] [NumberField F]

def ballR (r : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) : AddSubgroup (v.adicCompletion F) :=
  Valued.v.leAddSubgroup (v.intValuation r)

theorem mem_ballR {r : 𝓞 F} {v : HeightOneSpectrum (𝓞 F)} {x : v.adicCompletion F} :
    x ∈ ballR r v ↔ Valued.v x ≤ v.intValuation r := Iff.rfl

theorem isOpen_ballR {r : 𝓞 F} (hr : r ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (ballR r v : Set (v.adicCompletion F)) := by
  set c : v.adicCompletion F := algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r)
  have hcv : Valued.v c = v.intValuation r := PI.UnipApproxD.IntegersDenseFiniteAdeles.val_R v r
  have hc : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hcv
    exact (v.intValuation_ne_zero r hr) hcv.symm
  have e : (ballR r v : Set (v.adicCompletion F)) =
      (fun x => x / c) ⁻¹' (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    ext x
    change Valued.v x ≤ v.intValuation r ↔ Valued.v (x / c) ≤ 1
    rw [map_div₀, ← hcv, div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hc))]
  rw [e]
  exact (Valued.isOpen_valuationSubring _).preimage (continuous_id.div_const c)

theorem ballR_subset (r : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    (ballR r v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F := fun x hx => by
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
  exact (mem_ballR.1 hx).trans (v.intValuation_le_one r)

theorem eventually_ballR_eq {r : 𝓞 F} (hr : r ≠ 0) :
    ∀ᶠ v in Filter.cofinite, (ballR r v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F := by
  have h : (Ideal.span {r} : Ideal (𝓞 F)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hr
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h).subset fun v hv => ?_)
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [← HeightOneSpectrum.intValuation_lt_one_iff_dvd]
  refine lt_of_le_of_ne (v.intValuation_le_one r) fun h1 => hv ?_
  ext x
  rw [SetLike.mem_coe, SetLike.mem_coe, mem_ballR, h1, HeightOneSpectrum.mem_adicCompletionIntegers]

end GlobalTheory.SBBox

namespace GlobalTheory.SBBox

theorem exists_box_invariant : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
    g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
    ∃ B : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F),
      (∀ v, IsOpen (B v : Set (v.adicCompletion F))) ∧
      (∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F) ∧
      (∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) ∧
      ∀ y u : κ → FiniteAdeleRing (𝓞 F) F, (∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v) → g (y + u) = g y := by
  intro F _ _ κ _ g hg
  classical
  obtain ⟨N, hN, hNg⟩ := exists_nhds_zero_add_eq hg.1 hg.2
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, -, t, ht, hIt⟩ := hN
  have hr : ∀ i, ∃ r : 𝓞 F, r ≠ 0 ∧ ∀ y : FiniteAdeleRing (𝓞 F) F,
      (∀ v : HeightOneSpectrum (𝓞 F), Valued.v (y v) ≤ v.intValuation r) → y ∈ t i :=
    fun i => GlobalTheory.OpenSubAdele.exists_small_of_mem_nhds (ht i)
  choose r hr0 hrt using hr
  set R : 𝓞 F := ∏ i, r i
  have hR0 : R ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hr0 i
  have hle : ∀ i (v : HeightOneSpectrum (𝓞 F)), v.intValuation R ≤ v.intValuation (r i) := by
    intro i v
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem r (Finset.mem_univ i)
    rw [show R = r i * c from hc, map_mul]
    exact mul_le_of_le_one_right' (v.intValuation_le_one c)
  refine ⟨ballR R, isOpen_ballR hR0, ballR_subset R, eventually_ballR_eq hR0, fun y u hu => ?_⟩
  refine hNg y u (hIt fun i _ => hrt i (u i) fun v => ?_)
  exact (mem_ballR.1 (hu i v)).trans (hle i v)

end GlobalTheory.SBBox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueCoordinatesOfLocalModelBelowPlaceStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residue_coordinates_of_localModel_below_place : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q),
    letI := hQ.isLocalRing; ∀ (N r : ℕ) (V : Place c) (hC : V.Contains Q) (u : Fin r → V.ring),
    (∃ x : Fin N → L, TrBasis c x) →
    (∀ q ∈ IsLocalRing.maximalIdeal Q,
      (⟨q, hC _ q.2⟩ : V.ring) ∈ IsLocalRing.maximalIdeal V.ring) →
    (∀ P : MvPolynomial (Fin r) Q, (∃ α, P.coeff α ∉ IsLocalRing.maximalIdeal Q) →
      IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P)) →
    (∀ f : V.ring, ∃ P R : MvPolynomial (Fin r) Q,
      IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R) ∧
      f * MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R =
        MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P) →
    ∃ (j : ℕ) (s : Fin j → Q), r + j + 1 = N ∧
      ∀ P : MvPolynomial (Fin (r + j)) ℂ, P ≠ 0 →
        IsUnit (MvPolynomial.eval₂ V.const
          (Fin.append u fun i => (⟨s i, hC _ (s i).2⟩ : V.ring)) P) := by
  first | exact @GlobalTheory.FieldPair.exists_residue_coords_of_locModel | exact GlobalTheory.FieldPair.exists_residue_coords_of_locModel | (intros; apply GlobalTheory.FieldPair.exists_residue_coords_of_locModel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteParabolicDoubleCosetsOrbitalIntegralStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_parabolicDoubleCosets_orbitalIntegral : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw b w, (m.1.val.charpoly * m.2.val.charpoly).Separable → ∀ hγ : blk h w m 0 ∈ GlobalTheory.LeviDesc.parP a n w, {d : DoubleCoset.Quotient (twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) : Set (GlobalTheory.LeviDesc.parP a n w)) (((GlobalTheory.LFun.KGL w (n := n)).subgroupOf (GlobalTheory.LeviDesc.parP a n w) : Subgroup _) : Set (GlobalTheory.LeviDesc.parP a n w)) | GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (((Quotient.out d)⁻¹ * ⟨blk h w m 0, hγ⟩ * Quotient.out d : GlobalTheory.LeviDesc.parP a n w) : GLw n w) ≠ 0}.Finite := by
  first | exact @GlobalTheory.LeviDesc.OrbFin.fin_doubleCosets | exact GlobalTheory.LeviDesc.OrbFin.fin_doubleCosets | (intros; apply GlobalTheory.LeviDesc.OrbFin.fin_doubleCosets <;> assumption)
end

