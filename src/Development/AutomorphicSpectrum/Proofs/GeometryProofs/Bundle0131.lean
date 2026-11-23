module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0009
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0060
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0115
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerI5OfReference

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OverlappingAnalyticChartsRatio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GagaC.Compare

theorem eq_val_mul : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (W U U' : X.Opens) (F : (Sp ℂ ⟶ X) → ℂ) (T T' : Ω) (d d' : ℕ) (B : Set (Fin d → ℂ)) (B' : Set (Fin d' → ℂ)) (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (Y' : (Fin d' → ℂ) → (Sp ℂ ⟶ X)) (H : (Fin d → ℂ) → ℂ) (H' : (Fin d' → ℂ) → ℂ) (b₁ : Fin d → ℂ) (b₂ : Fin d' → ℂ) (r : ℂ), IsCptGen ξ → HChart s ξ W U F T B Y H → HChart s ξ W U' F T' B' Y' H' → (∀ (q : X) (hq : genPt ξ ⤳ q), q ∈ U → q ∈ W → unitAt ξ ⟨q, hq⟩ T) → (∀ (q : X) (hq : genPt ξ ⤳ q), q ∈ U' → q ∈ W → unitAt ξ ⟨q, hq⟩ T') → b₁ ∈ B → b₂ ∈ B' → Y b₁ = Y' b₂ → ValAt ξ (Y b₁) (T' / T) r → H b₁ = r * H' b₂ := by
  intro X s Ω _ ξ W U U' F T T' d d' B B' Y Y' H H' b₁ b₂ r hξ hC hC' hT hT' hb₁ hb₂ hY hval
  obtain ⟨hsp, st, hst1, -⟩ := id hval
  have hreg : T' / T ∈ GlobalTheory.CompanionTheory.Ar.regAt ξ ⟨GlobalTheory.CompanionTheory.Ar.centre (Y b₁), hsp⟩ := by
    unfold GlobalTheory.CompanionTheory.Ar.regAt
    exact RingHom.mem_range.mpr ⟨st, hst1⟩
  obtain ⟨N, hqN, v, -, hv⟩ := GlobalTheory.CompanionTheory.Ar.Flat.GagaC.exists_section hsp hreg ⊤ (by simp)
  have hgN : GlobalTheory.CompanionTheory.Ar.genPt ξ ∈ N := GlobalTheory.CompanionTheory.Ar.Flat.GagaC.genPt_mem hsp hqN
  have hvg : GlobalTheory.CompanionTheory.Ar.Flat.GagaC.genV ξ N hgN v = T' / T := by
    rw [← GlobalTheory.CompanionTheory.Ar.Flat.GagaC.genMap_germ N hsp hqN hgN v]
    exact hv
  have hvalg : ∀ b ∈ B, ∀ hbN : GlobalTheory.CompanionTheory.Ar.centre (Y b) ∈ N,
      GlobalTheory.CompanionTheory.Ar.ValAt ξ (Y b) (T' / T) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (Y b) N v) := by
    intro b hb hbN
    apply GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ValAt.of_section hbN (hC.cpt b hb)
    rw [GlobalTheory.CompanionTheory.Ar.Flat.GagaC.genMap_germ N (hC.cpt b hb) hbN hgN v]
    exact hvg
  have hr : ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (Y b₁) N v = r :=
    GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ValAt.unique hξ (hvalg b₁ hb₁ hqN) hval
  obtain ⟨ε, κ, hε, -, hκd, hκ1, hκ⟩ :=
    hC'.chart.factor d B Y hC.chart.isOpen hC.chart.hol hC.chart.isOver b₁ hb₁ b₂ hb₂ hY
  obtain ⟨hOopen, hgd⟩ := hC.chart.hol N v
  obtain ⟨S, hSdef⟩ : ∃ S : Set (Fin d → ℂ),
      S = {b | b ∈ B ∧ ⊤ ≤ (TopologicalSpace.Opens.map (Y b).base).obj N} := ⟨_, rfl⟩
  have hmemS : ∀ b, b ∈ S ↔ b ∈ B ∧ GlobalTheory.CompanionTheory.Ar.centre (Y b) ∈ N := by
    intro b
    rw [hSdef, Set.mem_ofPred_eq, GlobalTheory.CompanionTheory.Ar.Flat.GagaC.top_le_iff_centre]
  have hSo : IsOpen S := by
    rw [hSdef]
    exact hOopen
  have hSg : DifferentiableOn ℂ (fun b => ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (Y b) N v) S := by
    rw [hSdef]
    exact hgd
  have hOo : IsOpen (S ∩ Metric.ball b₁ ε) := hSo.inter Metric.isOpen_ball
  have h1 : ContinuousOn H (S ∩ Metric.ball b₁ ε) :=
    (hC.hol.mono fun b (hb : b ∈ S ∩ Metric.ball b₁ ε) => ((hmemS b).mp hb.1).1).continuousOn
  have h2 : ContinuousOn (fun b => ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (Y b) N v) (S ∩ Metric.ball b₁ ε) :=
    (hSg.mono fun b (hb : b ∈ S ∩ Metric.ball b₁ ε) => hb.1).continuousOn
  have h3 : ContinuousOn (fun b => H' (κ b)) (S ∩ Metric.ball b₁ ε) := by
    have hc : DifferentiableOn ℂ (H' ∘ κ) (Metric.ball b₁ ε) :=
      hC'.hol.comp hκd (fun b hb => (hκ b hb).1)
    exact (hc.mono fun b (hb : b ∈ S ∩ Metric.ball b₁ ε) => hb.2).continuousOn
  have hcont : ContinuousOn (fun b => H b - ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (Y b) N v * H' (κ b))
      (S ∩ Metric.ball b₁ ε) := h1.sub (h2.mul h3)
  have hzero : ∀ b ∈ S ∩ Metric.ball b₁ ε, GlobalTheory.CompanionTheory.Ar.centre (Y b) ∈ W →
      H b - ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (Y b) N v * H' (κ b) = 0 := by
    intro b hbO hbW
    obtain ⟨hbB, hbN⟩ := (hmemS b).mp hbO.1
    obtain ⟨hκB, hYκ⟩ := hκ b hbO.2
    have hcb := hC.cpt b hbB
    have hTu := hT (GlobalTheory.CompanionTheory.Ar.centre (Y b)) hcb (hC.inU b hbB) hbW
    obtain ⟨r₁, hr₁, e₁⟩ := GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ValAt.exists_ne_zero hξ hcb hTu
    have hcb' := hC'.cpt (κ b) hκB
    have hW' : GlobalTheory.CompanionTheory.Ar.centre (Y' (κ b)) ∈ W := by
      rw [← hYκ]
      exact hbW
    have hT'u := hT' (GlobalTheory.CompanionTheory.Ar.centre (Y' (κ b))) hcb' (hC'.inU (κ b) hκB) hW'
    obtain ⟨r₂, -, e₂⟩ := GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ValAt.exists_ne_zero hξ hcb' hT'u
    have f₁ := hC.rel b hbB hbW r₁ e₁
    have f₂ := hC'.rel (κ b) hκB hW' r₂ e₂
    have hm := GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ValAt.mul (hvalg b hbB hbN) e₁
    have hTT : T' / T * T = T' := by
      rw [div_mul_eq_mul_div, mul_div_assoc, div_self hTu.1, _root_.mul_one]
    rw [hTT] at hm
    have e₂' : GlobalTheory.CompanionTheory.Ar.ValAt ξ (Y b) T' r₂ := by
      rw [hYκ]
      exact e₂
    have hu := GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ValAt.unique hξ hm e₂'
    rw [hYκ] at f₁
    rw [f₁, ← hu] at f₂
    have hH : H b = ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (Y b) N v * H' (κ b) := by
      apply mul_right_cancel₀ hr₁
      rw [f₂]
      ring
    rw [hH, sub_self]
  have hb1O : b₁ ∈ S ∩ Metric.ball b₁ ε := ⟨(hmemS b₁).mpr ⟨hb₁, hqN⟩, Metric.mem_ball_self hε⟩
  have hφ : H b₁ - ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (Y b₁) N v * H' (κ b₁) = 0 := by
    by_contra hne
    have hopen := hcont.isOpen_inter_preimage hOo (isOpen_compl_singleton (x := (0 : ℂ)))
    obtain ⟨b, hb, hbW⟩ := hC.dense _ hopen (fun b hb => ((hmemS b).mp hb.1.1).1) ⟨b₁, hb1O, hne⟩
    exact hb.2 (hzero b hb.1 hbW)
  rw [hr, hκ1] at hφ
  exact sub_eq_zero.mp hφ

end GlobalTheory.CompanionTheory.Ar.Flat.GagaC.Compare
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothAlgebraEqZeroOfVanishOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC

namespace GlobalTheory.CompanionTheory.Ar.Flat.GagaC

theorem mvPolynomial_eq_zero_of_eval_eq_zero_on_open {D : ℕ} {O : Set (Fin D → ℂ)}
    (hO : IsOpen O) (hne : O.Nonempty) (p : MvPolynomial (Fin D) ℂ)
    (h : ∀ b ∈ O, MvPolynomial.eval b p = 0) : p = 0 := by
  obtain ⟨b₀, hb₀⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO b₀ hb₀
  refine MvPolynomial.funext_set (fun i => Metric.ball (b₀ i) ε)
    (fun i => infinite_of_mem_nhds (b₀ i) (Metric.ball_mem_nhds _ hε)) fun x hx => ?_
  rw [map_zero]
  exact h x (hball (by rw [ball_pi _ hε]; exact hx))

theorem eq_zero_of_forall_points_eq_zero :
    ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] (D : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension D ℂ A] (O : Set (Fin D → ℂ)) (Ψ : (Fin D → ℂ) → (A →+* ℂ)) (f : Fin D → A) (a : A), IsOpen O → O.Nonempty → (∀ b ∈ O, (Ψ b).comp (algebraMap ℂ A) = RingHom.id ℂ ∧ ∀ i, Ψ b (f i) = b i) → (∀ b ∈ O, Ψ b a = 0) → a = 0 := by
  intro A _ _ _ D _ O Ψ f a hO hne hΨ ha
  by_contra ha0
  have key : ∀ b ∈ O, ∀ p : MvPolynomial (Fin D) ℂ,
      Ψ b (MvPolynomial.aeval f p) = MvPolynomial.eval b p := by
    intro b hb p
    let φ : A →ₐ[ℂ] ℂ :=
      { Ψ b with commutes' := fun r => DFunLike.congr_fun (hΨ b hb).1 r }
    have h1 : φ.comp (MvPolynomial.aeval f) = MvPolynomial.aeval b := by
      ext i
      simpa [φ] using (hΨ b hb).2 i
    have h2 := DFunLike.congr_fun h1 p
    exact h2.trans (DFunLike.congr_fun (MvPolynomial.coe_aeval_eq_eval b) p)
  have hind : AlgebraicIndependent ℂ f := by
    rw [algebraicIndependent_iff]
    intro p hp
    refine mvPolynomial_eq_zero_of_eval_eq_zero_on_open hO hne p fun b hb => ?_
    rw [← key b hb p, hp, map_zero]
  obtain ⟨e, he⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial D ℂ A
  have htr : Algebra.trdeg ℂ A = D := GlobalTheory.AffinePoints.trdeg_eq_of_etale e he
  have hbasis : IsTranscendenceBasis ℂ f :=
    hind.isTranscendenceBasis_of_trdeg_le_of_finite (by simp [htr])
  haveI := hbasis.isAlgebraic
  obtain ⟨r, hr, c, hc⟩ := (Algebra.IsAlgebraic.isAlgebraic
    (R := Algebra.adjoin ℂ (Set.range f)) a).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero ha0)
  have hmem : (r : A) ∈ (MvPolynomial.aeval f : MvPolynomial (Fin D) ℂ →ₐ[ℂ] A).range := by
    rw [← Algebra.adjoin_range_eq_range_aeval]
    exact r.2
  obtain ⟨p, hp⟩ := hmem
  have hp' : MvPolynomial.aeval f p = (r : A) := hp
  have hp0 : p = 0 := by
    refine mvPolynomial_eq_zero_of_eval_eq_zero_on_open hO hne p fun b hb => ?_
    have hrc : (r : A) = a * c := hc
    rw [← key b hb p, hp', hrc, map_mul, ha b hb, zero_mul]
  apply hr
  apply Subtype.ext
  rw [← hp', hp0, map_zero]
  rfl

end GlobalTheory.CompanionTheory.Ar.Flat.GagaC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPointsTransferDominating
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PatchIso

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem unitAt_congr {X' : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'}
    {p : Cpt ξ} {p' : Cpt ξ'} (h : regAt ξ' p' = regAt ξ p) (a : Ω) : unitAt ξ' p' a ↔ unitAt ξ p a := by
  unfold unitAt
  rw [h]

theorem char_zero_congr {X' : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'}
    {p : Cpt ξ} {p' : Cpt ξ'} (h : regAt ξ' p' = regAt ξ p) (hp : Char0 ξ p) : Char0 ξ' p' := fun r hr hf =>
  hp r hr fun hu => hf ((unitAt_congr h _).2 hu)

theorem mem_genFib_of_char0 [CharZero Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ} (hp : Char0 ξ p) :
    p ∈ genFib ξ := by
  have key : ∀ n : ℕ, 0 < n → ((n : Ω))⁻¹ ∈ regAt ξ p := by
    intro n
    induction n using induction_on_primes with
    | zero => exact fun h => absurd h (lt_irrefl 0)
    | one => intro _; simpa using (regAt ξ p).one_mem
    | prime_mul r a hr ih =>
      intro h
      have ha : 0 < a := Nat.pos_of_mul_pos_left h
      have hu : unitAt ξ p (r : Ω) := not_not.1 (hp r hr)
      rw [Nat.cast_mul, mul_inv]
      exact mul_mem hu.2.2 (ih ha)
  exact fun n hn => ⟨Nat.cast_ne_zero.2 hn.ne', natCast_mem _ n, key n hn⟩

theorem exists_below [CharZero Ω] {X₁ X₂ : Scheme.{0}} {ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁}
    {ξ₂ : Spec (CommRingCat.of Ω) ⟶ X₂} {g : X₂ ⟶ X₁} (hg : IsCptGen ξ₂)
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ₂ ξ₁ g (RingHom.id Ω))
    (hi : ∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) (p : Cpt ξ₂) (hp : Char0 ξ₂ p) :
    ∃ p₁ : Cpt ξ₁, p₁.1 = g p.1 ∧ Char0 ξ₁ p₁ ∧ regAt ξ₂ p = regAt ξ₁ p₁ := by
  obtain ⟨h, -, hu⟩ := RegAtDom.regAt_dominates X₁ Ω ξ₁ X₂ Ω ξ₂ g (RingHom.id Ω) hd p
  have c : Char0 ξ₁ ⟨g p.1, h⟩ := fun r hr hf =>
    hf (hu hg (r : Ω) (natCast_mem _ r) (not_not.1 (hp r hr)))
  refine ⟨⟨g p.1, h⟩, rfl, c, ?_⟩
  rw [(hi _ (mem_genFib_of_char0 c)).regAt_eq p rfl, Subring.map_id]

theorem exists_above [CharZero Ω] {X₁ X₂ : Scheme.{0}} {ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁}
    {ξ₂ : Spec (CommRingCat.of Ω) ⟶ X₂} {g : X₂ ⟶ X₁}
    (hi : ∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) (p₁ : Cpt ξ₁) (hp : Char0 ξ₁ p₁) :
    ∃ p : Cpt ξ₂, g p.1 = p₁.1 ∧ Char0 ξ₂ p ∧ regAt ξ₂ p = regAt ξ₁ p₁ := by
  have I := hi p₁ (mem_genFib_of_char0 hp)
  obtain ⟨p, hp', -⟩ := I.existsUnique
  have e : regAt ξ₂ p = regAt ξ₁ p₁ := by rw [I.regAt_eq p hp', Subring.map_id]
  exact ⟨p, hp', char_zero_congr e hp, e⟩

theorem sncPts_of_isoAt :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ₁ κ₂ : Type) (x₁ : κ₁ → Ω) (x₂ : κ₂ → Ω) (X₁ X₂ : Scheme.{0}) (ξ₁ : Sp Ω ⟶ X₁) (ξ₂ : Sp Ω ⟶ X₂) (g : X₂ ⟶ X₁) (e : ℕ) (Ab : Set X₁), (∀ q : X₁, genPt ξ₁ ⤳ q) → (∀ q : X₂, genPt ξ₂ ⤳ q) → CoordTie ℤ ξ₁ x₁ → CoordTie ℤ ξ₂ x₂ → GlobalTheory.CompanionTheory.Ar.Dominates ξ₂ ξ₁ g (RingHom.id Ω) → (∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) → SncPts ξ₁ e {p | Char0 ξ₁ p ∧ p.1 ∉ Ab} → SncPts ξ₂ e {p | Char0 ξ₂ p ∧ g p.1 ∉ Ab} := by
  intro Ω _ _ κ₁ κ₂ x₁ x₂ X₁ X₂ ξ₁ ξ₂ g e Ab _ _ _ t₂ hd hi hs p hp
  have ePts : Pts ξ₂ = Pts ξ₁ := by
    ext R
    constructor
    · rintro ⟨p₂, c, rfl⟩
      obtain ⟨p₁, -, c₁, r⟩ := exists_below t₂.gen hd hi p₂ c
      exact ⟨p₁, c₁, r⟩
    · rintro ⟨p₁, c, rfl⟩
      obtain ⟨p₂, -, c₂, r⟩ := exists_above hi p₁ c
      exact ⟨p₂, c₂, r.symm⟩
  have eB : regAt ξ₂ '' {p | Char0 ξ₂ p ∧ g p.1 ∉ Ab} = regAt ξ₁ '' {p | Char0 ξ₁ p ∧ p.1 ∉ Ab} := by
    ext R
    constructor
    · rintro ⟨p₂, ⟨c, ha⟩, rfl⟩
      obtain ⟨p₁, e₁, c₁, r⟩ := exists_below t₂.gen hd hi p₂ c
      exact ⟨p₁, ⟨c₁, e₁ ▸ ha⟩, r.symm⟩
    · rintro ⟨p₁, ⟨c, ha⟩, rfl⟩
      obtain ⟨p₂, e₂, c₂, r⟩ := exists_above hi p₁ c
      exact ⟨p₂, ⟨c₂, by rwa [e₂]⟩, r⟩
  obtain ⟨p₁, -, c₁, r⟩ := exists_below t₂.gen hd hi p hp
  obtain ⟨A, z, n, q, hP, hq, hl⟩ := hs p₁ c₁
  refine ⟨A, z, n, q, ?_, hq, ?_⟩
  · rw [ePts, eB]
    exact hP
  · rw [r]
    exact hl

end GlobalTheory.CompanionTheory.Ar.PatchIso
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TensorEquivOfBasisExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

namespace GlobalTheory.CompanionTheory.Ar.FlagStep

theorem exists_tensor_equiv_of_semilinear :
    ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (V V' : Type) [AddCommGroup V]
    [Module Ω₀ V] [AddCommGroup V'] [Module Ω V'] (j : V →+ V'),
    (∀ (a : Ω₀) e, j (a • e) = algebraMap Ω₀ Ω a • j e) →
    (∀ (n : ℕ) (b : Fin n → V), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) →
    Submodule.span Ω (Set.range j) = ⊤ →
    ∃ Φ : TensorProduct Ω₀ Ω V ≃ₗ[Ω] V', ∀ e, Φ (TensorProduct.mk Ω₀ Ω V 1 e) = j e := by
  intro Ω₀ Ω _ _ _ V V' _ _ _ _ j hsemi hind hspan
  letI : Module Ω₀ V' := Module.compHom V' (algebraMap Ω₀ Ω)
  haveI : IsScalarTower Ω₀ Ω V' := ⟨fun a b x => by
    change (a • b) • x = algebraMap Ω₀ Ω a • (b • x)
    rw [Algebra.smul_def, mul_smul]⟩
  let jl : V →ₗ[Ω₀] V' :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun a e => hsemi a e }
  let L : TensorProduct Ω₀ Ω V →ₗ[Ω] V' := jl.liftBaseChange Ω
  have hL : ∀ e, L (TensorProduct.mk Ω₀ Ω V 1 e) = j e := by
    intro e
    change jl.liftBaseChange Ω (1 ⊗ₜ[Ω₀] e) = j e
    rw [LinearMap.liftBaseChange_tmul, one_smul]
    rfl
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨e, rfl⟩
    exact ⟨_, hL e⟩
  let B := Module.Basis.ofVectorSpace Ω₀ V
  let C := Algebra.TensorProduct.basis Ω B
  have hC : ∀ i, L (C i) = j (B i) := by
    intro i
    rw [Algebra.TensorProduct.basis_apply]
    exact hL (B i)
  have hli : LinearIndependent Ω (fun i => j (B i)) := by
    rw [linearIndependent_iff_finset_linearIndependent]
    intro s
    let e := s.equivFin
    have h1 : LinearIndependent Ω₀ (fun k : Fin s.card => B (e.symm k).1) :=
      B.linearIndependent.comp _ (Subtype.val_injective.comp e.symm.injective)
    have h2 := (hind _ _ h1).comp e e.injective
    convert h2 using 1
    funext i
    simp
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : Finsupp.linearCombination Ω (fun i => j (B i)) (C.repr x) = 0 := by
      rw [← hx]
      conv_rhs => rw [← C.linearCombination_repr x]
      rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, map_finsuppSum]
      simp [hC]
    have h1 : C.repr x = 0 := hli (h0.trans (map_zero _).symm)
    simpa using h1
  exact ⟨LinearEquiv.ofBijective L ⟨hinj, hsurj⟩, fun e => hL e⟩

end GlobalTheory.CompanionTheory.Ar.FlagStep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionSectionEqOfConnected
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat


open GlobalTheory.HolTorsion in
theorem cubWeil_const_of_isHolTo_family : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (m N : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ G) (ζ : ℂˣ) (b₀ : Fin m → ℂ), 0 < N → IsOpen B → IsPreconnected B → b₀ ∈ B → IsHolTo B (fun b => (x b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ N = 1 ∧ x' b ^ N = 1 ∧ (x b).left ≫ G.hom = (x' b).left ≫ G.hom) → GlobalTheory.UU.CubWeil c N (x b₀) (x' b₀) (unitOn ζ) → ∀ b ∈ B, GlobalTheory.UU.CubWeil c N (x b) (x' b) (unitOn ζ) := by
  intro X G _ _ L c m N B y x x' ζ b₀ hN _ hB hb₀ hx hx' htor h₀ b₁ hb₁
  let o : X ⟶ G.left := (η[G] : 𝟙_ (Over X) ⟶ G).left
  have ho : o ≫ G.hom = 𝟙 X := Over.w (η[G] : 𝟙_ (Over X) ⟶ G)
  let mk : G ⟶ G := (𝟙 G) ^ N
  have hkill : ∀ (T : Over X) (u : T ⟶ G), u ^ N = 1 ↔ u.left ≫ mk.left = T.hom ≫ o := by
    intro T u
    have e₁ : u.left ≫ mk.left = (u ^ N).left := by
      rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
    have e₂ : T.hom ≫ o = (1 : T ⟶ G).left := by
      rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    rw [e₁, e₂]
    exact ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h⟩
  let p := pullback.fst mk.left o
  let q := pullback.snd mk.left o
  have H : IsPullback p q mk.left o := IsPullback.of_hasPullback _ _
  have hpq : p ≫ G.hom = q := by
    rw [← Over.w mk, ← Category.assoc, H.w, Category.assoc, ho, Category.comp_id]
  have hy : IsHolTo B y := isHolTo_congr (isHolTo_comp hx G.hom) fun b _ => (Over.w (x b)).symm
  obtain ⟨a, ha, hab⟩ := exists_isHolTo_lift H hx hy (fun b hb => (hkill _ _).1 (htor b hb).1) hb₀
  obtain ⟨a', ha', hab'⟩ := exists_isHolTo_lift H hx' hy (fun b hb => (hkill _ _).1 (htor b hb).2.1) hb₀
  obtain ⟨z, hz, hzb⟩ := exists_isHolTo_lift (IsPullback.of_hasPullback q q) ha ha'
    (fun b hb => (hab b hb).2.trans (hab' b hb).2.symm) hb₀
  let T : Over X := Over.mk (pullback.fst q q ≫ q)
  let u : T ⟶ G := Over.homMk (pullback.fst q q ≫ p) (by
    show (pullback.fst q q ≫ p) ≫ G.hom = pullback.fst q q ≫ q
    rw [Category.assoc, hpq])
  let v : T ⟶ G := Over.homMk (pullback.snd q q ≫ p) (by
    show (pullback.snd q q ≫ p) ≫ G.hom = pullback.fst q q ≫ q
    rw [Category.assoc, hpq, pullback.condition])
  have hu : u ^ N = 1 := (hkill T u).2 (by
    show (pullback.fst q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
    rw [Category.assoc, H.w, Category.assoc])
  have hv : v ^ N = 1 := (hkill T v).2 (by
    show (pullback.snd q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
    rw [Category.assoc, H.w, pullback.condition, Category.assoc])
  obtain ⟨e, he, -⟩ := GlobalTheory.UU.existsUnique_cubWeil c hu hv
  have hek : e.val ^ N = 1 := congrArg Units.val he.pow_eq_one
  have hpull : ∀ w ∈ B, GlobalTheory.UU.CubWeil c N (x w) (x' w) (Units.map (z w).appTop.hom.toMonoidHom e) := by
    intro w hw
    let h : Over.mk (y w) ⟶ T := Over.homMk (z w) (by
      show z w ≫ pullback.fst q q ≫ q = y w
      rw [← Category.assoc, (hzb w hw).1, (hab w hw).2])
    have e₁ : h ≫ u = x w := Over.OverMorphism.ext (by
      show z w ≫ pullback.fst q q ≫ p = _
      rw [← Category.assoc, (hzb w hw).1, (hab w hw).1])
    have e₂ : h ≫ v = x' w := Over.OverMorphism.ext (by
      show z w ≫ pullback.snd q q ≫ p = _
      rw [← Category.assoc, (hzb w hw).2, (hab' w hw).1])
    have := he.comp h
    rw [e₁, e₂] at this
    exact this
  have e₀ : Units.map (z b₀).appTop.hom.toMonoidHom e = unitOn ζ := (hpull b₀ hb₀).unique h₀
  have e₁ : Units.map (z b₁).appTop.hom.toMonoidHom e = Units.map (z b₀).appTop.hom.toMonoidHom e :=
    Units.ext ((val_map_appTop (z b₁) e.val).trans
      ((congrArg _ (valAt'_eq_of_pow_eq_one hz hB hN hek hb₀ hb₁)).trans (val_map_appTop (z b₀) e.val).symm))
  have := hpull b₁ hb₁
  rw [e₁, e₀] at this
  exact this

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerI5OfFibreInput
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.Ht.TopLower

theorem i5_of_hasRef_of_fibreInput : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (j k : ℕ) (T : RootTower Ψ (j + 1 + (k + 1)))
    (II : IntersectionSystem) (R : T.Comp → RootModel Ψ (j + 1 + (k + 1))), IsIntersectionSystem II → HasRef T R →
    (∀ c, AmpleQ (R c).y (R c).A.a ∧ FlatUnit (R c) ∧ FibreInput (R c)) → T.I5 II := by
  intro Ψ _ _ j k T II R hII hR h
  exact _root_.GlobalTheory.CompanionTheory.Ar.Ht.RefTower.i5_of_hasRef_of_refLower Ψ _ T II R hII hR fun c =>
    GlobalTheory.T.ref_lower_of_fibre_input Ψ j k (R c) (h c).1 (h c).2.1 (h c).2.2

end GlobalTheory.CompanionTheory.Ar.Ht.TopLower
end

