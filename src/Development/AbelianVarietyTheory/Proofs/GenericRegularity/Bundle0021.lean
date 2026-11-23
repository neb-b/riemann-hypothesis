module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0060

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.PinNum

theorem goodAt_of_two_primes {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (l : Level H) {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b)
    (hM : l.M = a * b) (p : ℕ) : l.GoodAt p := by
  have hodd := l.odd
  rw [hM, Nat.odd_mul] at hodd
  have ha3 : 3 ≤ a := by
    have := ha.two_le
    obtain ⟨k, hk⟩ := hodd.1
    omega
  have hb3 : 3 ≤ b := by
    have := hb.two_le
    obtain ⟨k, hk⟩ := hodd.2
    omega
  unfold Level.GoodAt
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  by_cases hp : p.Prime
  swap
  · simpa [Nat.factorization_eq_zero_of_not_prime _ hp] using l.three_le
  have key : ∀ c, 3 ≤ c → c ∣ l.M → ¬ p ∣ c → 3 ≤ l.M / p ^ l.M.factorization p := fun c hc hd hn =>
    hc.trans (Nat.le_of_dvd (Nat.ordCompl_pos p hM0) (Nat.dvd_ordCompl_of_dvd_not_dvd hd hn))
  by_cases h : p ∣ a
  · refine key b hb3 (hM ▸ dvd_mul_left _ _) fun h' => hp.one_lt.ne' ?_
    exact Nat.eq_one_of_dvd_coprimes ((Nat.coprime_primes ha hb).2 hab) h h'
  · exact key a ha3 (hM ▸ dvd_mul_right _ _) h

theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  have h : (Module.finrank ℚ D.host.E : ℝ) = 2 * (D.R.f : ℝ) := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    push_cast
    ring
  exact_mod_cast h

theorem xiR_pos_le_one (D : D7) (Q : Par D) (h : Q.PinHost) : 0 < xiR D ∧ xiR D ≤ 1 := by
  obtain ⟨-, -, h3, -⟩ := h
  have hsq := Q.H.sqrt_neg_disc_sq
  rw [h3] at hsq
  have hd : (1 : ℝ) ≤ Q.H.d := by exact_mod_cast Q.H.d_prime.one_le
  have hn : ‖D.host.φ₀ D.host.sqrtMinusD‖ ^ 2 = Q.H.d := by
    rw [← norm_pow, hsq, norm_neg, Complex.norm_natCast]
  have h1 : 1 ≤ ‖D.host.φ₀ D.host.sqrtMinusD‖ := by
    by_contra hc
    push Not at hc
    nlinarith [norm_nonneg (D.host.φ₀ D.host.sqrtMinusD)]
  have hN : (1 : ℝ) ≤ (Ideal.absNorm D.host.ccK : ℝ) := by
    have : Ideal.absNorm D.host.ccK ≠ 0 := fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have hx : xiR D = 1 / ((Ideal.absNorm D.host.ccK : ℝ) * ‖D.host.φ₀ D.host.sqrtMinusD‖) := by
    unfold xiR Formalism.BasicNotions.Host.xi0
    rw [map_div₀, map_mul, map_natCast, map_neg, map_one, norm_div, norm_neg, norm_one, norm_mul,
      Complex.norm_natCast]
  have h2 : (1 : ℝ) ≤ (Ideal.absNorm D.host.ccK : ℝ) * ‖D.host.φ₀ D.host.sqrtMinusD‖ :=
    one_le_mul_of_one_le_of_one_le hN h1
  rw [hx]
  exact ⟨by positivity, (div_le_one (by positivity)).2 h2⟩

theorem numerics_of_pins : ∀ (D : D7) (Q : Par D), Q.Pins → (∀ p : ℕ, p.Prime → Q.l.GoodAt p) ∧ Q.l.A = 1 ∧ Q.l.M' = Q.l.M ∧ 0 < xiR D ∧ xiR D ≤ 1 ∧ Module.finrank ℚ D.host.E = 2 * D.R.f ∧ ∀ j, InR D j → (Q.Dw j).p + (Q.Dw j).q = D.R.r ∧ 1 ≤ D.R.r ∧ (Q.Dw j).dim + Nat.card (FlagVar (Q.Dw j)) = WeightFamilies.dimY D j := by
  intro D Q ⟨hH, ⟨hM, hA⟩, _, hD⟩
  have hx := xiR_pos_le_one D Q hH
  refine ⟨fun p _ => goodAt_of_two_primes Q.l (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne hM p, hA, ?_,
    hx.1, hx.2, finrank_host D, fun j hj => ?_⟩
  · rw [Level.M', hA, Nat.lcm_one_right]
  · obtain ⟨hp, hq, -⟩ := hD j hj
    have hk := D.R.m_add_three_le_k
    obtain ⟨hj1, hj2⟩ := hj
    refine ⟨?_, ?_, ?_⟩
    · rw [hp, hq]
      simp only [Ranks.sigW, Ranks.r]
      omega
    · unfold Ranks.r
      omega
    · rw [GlobalTheory.FlagDim.dim_add_card_flagVar, finrank_host, Nat.mul_div_cancel_left _ two_pos, hp, hq]
      rfl

end GlobalTheory.PinNum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.TieIntegral
section
noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem tie_integral : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), PushInvertible Y.t.G Y.t.PP.L → ∀ (T : CDVR) (io : c.F →+* T.Fr) (f₀ : Γ(Y.X, M.U) →+* T.V) (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin M.n) (u₀ : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) T.V), (∀ τ, InCell (ix τ) (u₀ τ)) → letI := io.toAlgebra; ∀ z : FrPt Xo c T.Fr, M.Comparison₂ ((algebraMap T.V T.Fr).comp f₀) (fun τ => (u₀ τ).map (algebraMap T.V T.Fr)) z → Integral T io z := by
  intro hS E _ _ _ H Dw l Xo c O _ β Y M hP T io f₀ ix u₀ hu
  letI := io.toAlgebra
  intro z ⟨Λ, hL, hT⟩
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap f₀ ≫ M.hU.fromSpec) Y.t
  have e : spMap ((algebraMap T.V T.Fr).comp f₀) ≫ M.hU.fromSpec =
      spMap (algebraMap T.V T.Fr) ≫ spMap f₀ ≫ M.hU.fromSpec := by
    rw [← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp]
    rfl
  have key : ∀ (g : Sp T.Fr ⟶ Y.X) (n : SABMap Λ.t' Y.t g),
      g = spMap (algebraMap T.V T.Fr) ≫ spMap f₀ ≫ M.hU.fromSpec →
      ∃ m2 : SABMap Λ.t' _ (spMap (algebraMap T.V T.Fr)), m2.φ ≫ m.φ = n.φ := by
    intro g n hg
    subst hg
    obtain ⟨m2, h⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m n
    exact ⟨m2, h.symm⟩
  obtain ⟨m2, h2⟩ := key _ Λ.m2 e
  exact ⟨_, Λ.t', Λ.m1, m2,
    GlobalTheory.T.framedPoint_vectors_integral_in_cell E H Dw l Xo c O β Y M T io f₀ ix u₀ hu z Λ hL _ m m2 h2,
    GlobalTheory.T.exists_integralGenerator_of_chartPoint_cdvr hS E H Dw l Xo c O β Y M hP T io f₀ z.x z.s Λ hT _ m m2 h2⟩

end GlobalTheory.Reg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.TriangularReframeCompBaseChangeBorel
section
noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S]

theorem reframe_scal_mul (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a * b) i = scal x a i * scal x b i := by
  unfold scal Out.liftFun
  simp only [map_mul]

theorem reframe_scal_one (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x (1 : S) i = 1 := by
  unfold scal Out.liftFun
  simp only [map_one]

theorem generators_unit {x : Sp S ⟶ Xo.X} (s s' : LB.Sec (PPx x))
    (hs : ∀ r : LB.Sec (PPx x), ∃! a : S, ∀ i, r.f i = scal x a i * s.f i)
    (hs' : ∀ r : LB.Sec (PPx x), ∃! a : S, ∀ i, r.f i = scal x a i * s'.f i) :
    ∃ a : Sˣ, ∀ i, s'.f i = scal x (a : S) i * s.f i := by
  obtain ⟨a, ha, -⟩ := hs s'
  obtain ⟨b, hb, -⟩ := hs' s
  obtain ⟨c, -, hc⟩ := hs s
  have h1 : b * a = c := hc _ fun i => by rw [reframe_scal_mul, _root_.mul_assoc, ← ha i, ← hb i]
  have h2 : (1 : S) = c := hc _ fun i => by rw [reframe_scal_one, _root_.one_mul]
  exact ⟨⟨a, b, by rw [mul_comm, h1, ← h2], by rw [h1, ← h2]⟩, ha⟩

variable [Algebra c.F S]

theorem Reframe.trans {g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S} {y y' y'' : FrPt Xo c S}
    (h : Reframe g y y') (h' : Reframe g' y' y'') : Reframe (fun τ => g τ * g' τ) y y'' := by
  obtain ⟨hx, hc⟩ := h
  obtain ⟨hx', hc'⟩ := h'
  refine ⟨hx'.trans hx, fun τ i => ?_⟩
  have h2 := hc' τ i
  rw [hx] at h2
  exact GlobalTheory.TangentLinear.isCombAt_mulVec _ _ _ _ _ _ _ (y.u τ) (y.tan τ) (y'.u τ) (g τ) (fun j => g' τ j i)
    (y''.u τ i) (hc τ) h2

theorem Reframe.baseChange {T : Type} [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    {g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S} {y y' : FrPt Xo c S} {z z' : FrPt Xo c T}
    (h : Reframe g y y') (hz : FrMap φ y z) (hz' : FrMap φ y' z') : Reframe (fun τ => (g τ).map φ) z z' := by
  obtain ⟨hx, hc⟩ := h
  obtain ⟨hzx, hzu, -⟩ := hz
  obtain ⟨hzx', hzu', -⟩ := hz'
  refine ⟨by rw [hzx', hzx, hx], fun τ i => ?_⟩
  exact isCombAt_pull φ.toRingHom hzx (hzu τ) (hzu' τ i) (hc τ i)

private theorem appLE_id_apply' {X : Scheme} (U : X.Opens) (e : U ≤ (𝟙 X) ⁻¹ᵁ U) (r : Γ(X, U)) :
    (Scheme.Hom.appLE (𝟙 X) U U e).hom r = r := by
  change (X.presheaf.map (𝟙 (Opposite.op U))).hom r = r
  rw [X.presheaf.map_id]
  rfl

theorem frBor_iff_reframe (y y' : FrPt Xo c S) : (∃ t : Ix Dw → Sˣ, FrBor t y y') ↔
    ∃ b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S,
      (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, IsUnit (b τ i i)) ∧ Reframe b y y' := by
  constructor
  · rintro ⟨t, hx, hcomb, -⟩
    choose cf hcf1 hcf2 hcf3 using hcomb
    refine ⟨fun τ j i => cf τ i j, fun τ => ⟨fun p q hpq => hcf2 τ q p hpq, fun p => ?_⟩, hx, fun τ i => hcf3 τ i⟩
    show IsUnit (cf τ p p)
    rw [hcf1 τ p]
    exact Units.isUnit _
  · rintro ⟨b, hb, hx, hcomb⟩
    cases y'
    dsimp only at hx hcomb ⊢
    subst hx
    obtain ⟨a, ha⟩ := generators_unit y.s _ y.gen ‹_›
    obtain ⟨t, ht0, ht1⟩ : ∃ t : Ix Dw → Sˣ, t none = a ∧ ∀ τ i, (t (some ⟨τ, i⟩) : S) = b τ i i :=
      ⟨fun o => o.elim a fun p => ((hb p.1).2 p.2).unit, rfl, fun τ i => ((hb τ).2 i).unit_spec⟩
    refine ⟨t, rfl, fun τ i => ⟨fun j => b τ j i, (ht1 τ i).symm, fun j hij => (hb τ).1 hij, hcomb τ i⟩,
      𝟙 _, Category.id_comp _, Category.id_comp _, fun i h => ?_⟩
    rw [ht0, ← ha i]
    exact appLE_id_apply' _ _ _

end

theorem reframe_calculus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (S : Type) [CommRing S] [Algebra c.F S], (∀ (g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (y y' y'' : FrPt Xo c S), Reframe g y y' → Reframe g' y' y'' → Reframe (fun τ => g τ * g' τ) y y'') ∧ (∀ (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (y y' : FrPt Xo c S) (z z' : FrPt Xo c T), Reframe g y y' → FrMap φ y z → FrMap φ y' z' → Reframe (fun τ => (g τ).map φ) z z') ∧ ∀ y y' : FrPt Xo c S, (∃ t : Ix Dw → Sˣ, FrBor t y y') ↔ ∃ b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S, (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, IsUnit (b τ i i)) ∧ Reframe b y y' := by
  intro E _ _ _ H Dw l Xo c S _ _
  exact ⟨fun g g' y y' y'' h h' => Reframe.trans h h',
    fun T _ _ φ g y y' z z' h hz hz' => Reframe.baseChange φ h hz hz', fun y y' => frBor_iff_reframe y y'⟩

end GlobalTheory.Reg
end
end

