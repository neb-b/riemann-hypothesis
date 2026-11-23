module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0008
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0097
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsIsKroneckerCharOfDiscr
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0006

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.FlatSat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace LevelTowerAlt

def FlatSat : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L]
    (t' : SAB H (Sp (𝓞 L))) (tB : SAB H (Sp L)) (_ : SABMap tB t' (spMap (algebraMap (𝓞 L) L)))
    (B : HermitianBundle.{0} L) (MB : LieModel t'.G (𝟙 _) B.carrier) (ρM : 𝓞 E →+* Module.End (𝓞 L) B.carrier)
    (s₁ s₂ : 𝓞 E →+* 𝓞 L), IsPrincipal tB → IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B MB → MB.IsActOf t'.act.act ρM →
    (∃ (ρ : L) (p' q' : ℕ), ρ ^ 2 = -(H.d : L) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k),
      (τ H.rt = g ρ → LieMult tB.act (spMap g) τ p') ∧ (τ H.rt ≠ g ρ → LieMult tB.act (spMap g) τ q')) →
    Function.Injective s₁ → (∀ (e : L →+* ℂ) (a : 𝓞 E), e (s₂ a : L) = starRingEnd ℂ (e (s₁ a : L))) →
    |B.normDegree (eigSp ρM s₁) - B.normDegree (eigSp ρM s₂)| ≤
      C * ((B.rank (eigSp ρM s₁) : ℝ) + B.rank (eigSp ρM s₂)) * (1 + Real.log (hostRd E) + |hostLval H|)

end LevelTowerAlt
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.GenOfUnit
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace LevelTowerAlt

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ}

theorem uZpow {a : Ω} (ha : unitAt ξ p a) (n : ℤ) : unitAt ξ p (a ^ n) := by
  obtain ⟨h0, h1, h2⟩ := ha
  refine ⟨zpow_ne_zero n h0, ?_, ?_⟩
  · rcases n with m | m
    · simpa using pow_mem h1 m
    · simpa [zpow_negSucc] using pow_mem h2 (m + 1)
  · rcases n with m | m
    · simpa using pow_mem h2 m
    · simpa [zpow_negSucc] using pow_mem h1 (m + 1)

theorem gen_unit {Λ : Lat ξ Ω} {s t : Ω} (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) : unitAt ξ p (s / t) := by
  obtain ⟨hs0, hs⟩ := hs
  obtain ⟨ht0, ht⟩ := ht
  have h1 : s ∈ Submodule.span (regAt ξ p) {t} := by
    rw [← ht, hs]
    exact Submodule.mem_span_singleton_self s
  have h2 : t ∈ Submodule.span (regAt ξ p) {s} := by
    rw [← hs, ht]
    exact Submodule.mem_span_singleton_self t
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp h1
  obtain ⟨w, hw⟩ := Submodule.mem_span_singleton.mp h2
  refine ⟨div_ne_zero hs0 ht0, ?_, ?_⟩
  · have e : s / t = (u : Ω) := by
      rw [← hu, Subring.smul_def, smul_eq_mul, mul_div_assoc, div_self ht0, mul_one]
    rw [e]
    exact u.2
  · have e : (s / t)⁻¹ = (w : Ω) := by
      rw [inv_div, ← hw, Subring.smul_def, smul_eq_mul, mul_div_assoc, div_self hs0, mul_one]
    rw [e]
    exact w.2

theorem gen_of_unit {Λ : Lat ξ Ω} {s t : Ω} (ht : Λ.IsGenAt p t) (hu : unitAt ξ p (s / t)) : Λ.IsGenAt p s := by
  obtain ⟨ht0, ht⟩ := ht
  obtain ⟨hu0, hu1, hu2⟩ := hu
  have hs0 : s ≠ 0 := by
    intro h
    apply hu0
    rw [h, zero_div]
  refine ⟨hs0, ?_⟩
  have hunit : IsUnit (⟨s / t, hu1⟩ : regAt ξ p) :=
    ⟨⟨⟨s / t, hu1⟩, ⟨(s / t)⁻¹, hu2⟩, Subtype.ext (mul_inv_cancel₀ hu0),
      Subtype.ext (inv_mul_cancel₀ hu0)⟩, rfl⟩
  have hst : (⟨s / t, hu1⟩ : regAt ξ p) • t = s := by
    rw [Subring.smul_def, smul_eq_mul]
    exact div_mul_cancel₀ s ht0
  rw [ht, ← hst, Submodule.span_singleton_smul_eq hunit]

theorem gen_untens {Λ : Lat ξ Ω} {σ : ℤ} (hσ : σ * σ = 1) {t : Ω}
    (h : (Lat.tens (fun _ : Unit => Λ) fun _ => σ).IsGenAt p t) : Λ.IsGenAt p (t ^ σ) := by
  obtain ⟨ht0, htl⟩ := h
  have hg : ∃ g, Λ.IsGenAt p g := by
    by_contra hno
    push_neg at hno
    have hmem : t ∈ (Lat.tens (fun _ : Unit => Λ) fun _ => σ) p := by
      rw [htl]
      exact Submodule.mem_span_singleton_self t
    have hbot : (Lat.tens (fun _ : Unit => Λ) fun _ => σ) p = ⊥ := by
      unfold Lat.tens
      rw [Submodule.span_eq_bot]
      rintro x ⟨s, hs, -⟩
      exact absurd (hs ()) (hno (s ()))
    rw [hbot, Submodule.mem_bot] at hmem
    exact ht0 hmem
  obtain ⟨g, hg⟩ := hg
  have hg0 : g ≠ 0 := hg.1
  have hT : (Lat.tens (fun _ : Unit => Λ) fun _ => σ).IsGenAt p (g ^ σ) := by
    refine ⟨zpow_ne_zero σ hg0, ?_⟩
    unfold Lat.tens
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro x ⟨s, hs, rfl⟩
      have hu := uZpow (gen_unit (hs ()) hg) σ
      have e : ∏ i : Unit, s i ^ σ = (⟨(s () / g) ^ σ, hu.2.1⟩ : regAt ξ p) • g ^ σ := by
        rw [Subring.smul_def, smul_eq_mul, Fintype.prod_unique]
        show s () ^ σ = (s () / g) ^ σ * g ^ σ
        rw [div_zpow, div_mul_cancel₀ _ (zpow_ne_zero σ hg0)]
      rw [SetLike.mem_coe, e]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_singleton_le_iff_mem]
      apply Submodule.subset_span
      exact ⟨fun _ => g, fun _ => hg, by simp⟩
  have hu := gen_unit ⟨ht0, htl⟩ hT
  have hu2 := uZpow hu σ
  have heq : (t / g ^ σ) ^ σ = t ^ σ / g := by
    rw [div_zpow, ← zpow_mul, hσ, zpow_one]
  rw [heq] at hu2
  exact gen_of_unit hg hu2

variable {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem chart_ne {c : (k : K) → J k} (h : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) :
    y ⟨k, c k⟩ ≠ 0 := by
  have h0 : ∏ k, y ⟨k, c k⟩ ≠ 0 := h.1
  rw [Finset.prod_ne_zero_iff] at h0
  exact h0 k (Finset.mem_univ k)

theorem deg_gen {Λ : Lat ξ Ω} {a : K → ℤ} {e : Ω} (h : Λ.IsDegOn Set.univ y a e) {c : (k : K) → J k}
    (hc : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) :
    Λ.IsGenAt p ((∏ k, y ⟨k, c k⟩ ^ a k) * e) :=
  ⟨mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (chart_ne hc k)) h.1, h.2 p trivial c hc⟩

variable {V : Type} [AddCommGroup V] [Module Ω V] {X' : Scheme.{0}} {Ω' : Type} [Field Ω']
  {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'} {V' : Type} [AddCommGroup V'] [Module Ω' V']
  {j : V →+ V'}

theorem uMap {q : Cpt ξ'} (hreg : ∀ a ∈ regAt ξ p, i a ∈ regAt ξ' q) {a : Ω} (h : unitAt ξ p a) :
    unitAt ξ' q (i a) := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨(map_ne_zero i).mpr h0, hreg a h1, ?_⟩
  rw [← map_inv₀]
  exact hreg _ h2

theorem exists_mat {r m : ℕ} {b : Fin r → V} {s : Fin m → V} (h : ∀ k, b k ∈ Submodule.span Ω (Set.range s)) :
    ∃ T : Matrix (Fin m) (Fin r) Ω, ∀ k, b k = ∑ k', T k' k • s k' := by
  choose c hc using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (h k)
  exact ⟨fun k' k => c k k', fun k => (hc k).symm⟩

end LevelTowerAlt
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.LevelFree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp
open scoped ComplexOrder

noncomputable section

namespace LevelTowerAlt.Comparison₂

def LevelFree : Prop :=
  HT.FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H)
    (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type)
    [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ), p ∈ S →
    0 < D.p + D.q → HT.HTFree 𝔐 p → ∀ q : Cpt 𝔐.ξ, InFibre 𝔐.ξ p q →
      𝔐.M.htOm 𝔐.t.PP.L (p ^ 4) q = 𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p) q

def MuHodge : Prop :=
  Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H)
    (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
    (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W)
    (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B : ℕ) (bb : ∀ τ, Fin Dc.N → W τ)
    (s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li) (lam : Ω),
    (∀ τ k, s τ k ∈ Or.𝔐.Vgen (Or.sm τ) ∧ Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - s τ k ∈ Or.𝔐.Vgen (Or.bg τ)) →
    Hd.Λ = lam • PiTensorProduct.tprod Ω (fun τ => quotWedge (Hd.F τ) Dc.j_le_N (bb τ)) →
    ∀ (z : Sp ℂ ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Or.𝔐.Interior z →
    ∃ (h : genPt Or.𝔐.ξ ⤳ centre z) (b : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li)
      (T : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) Ω)
      (Γ : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ),
      (∀ τ, (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)).IsFrameAt (b τ) ⟨centre z, h⟩ ∧ (∀ k, b τ k = ∑ k', T τ k' k • s τ k') ∧
        Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (b τ) (Γ τ) ∧ (Γ τ).PosDef) ∧
      SecNorm Or.𝔐.ξ Dc.y (muVert Hd B)
        (lam⁻¹ * ∏ p ∈ Dc.SB B, MvPolynomial.aeval Dc.y (Dc.vden p) / MvPolynomial.aeval Dc.y (Dc.vnum p)) z w
        (∏ τ, (T τ).det)⁻¹ (∏ τ, Real.sqrt (Γ τ).det.re)⁻¹

def muExp {Ψ : Type} {N : ℕ} (p : ℕ) (r : Ψ × Fin N) : ℤ := if p ≤ (r.2 : ℕ) then 1 else 0

def Common : Prop :=
  Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H)
    (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
    (S : Finset ℕ) (RM : Top.RootModel (CMType H) (D.p + D.q))
    (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (oR : RootOrigin Y S RM Fx)
    (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W)
    (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B : ℕ),
    S = S₀ ∪ Dc.SB B → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S₀) → oR.𝔐.OmVB → (∀ p ∈ S, oR.𝔐.R p = 4) →
    1 ≤ D.p → Or.bg = Sum.inl → Or.sm = Sum.inr → Or.Good → genPt Or.𝔐.ξ₀ = genPt Fx.ξf →
    ∃ (K₃ : Type) (_ : Fintype K₃) (ρ : K₃ → Type) (_ : ∀ k, Fintype (ρ k)) (κ₁ : RM.K → K₃)
      (v₁ : (Σ k, RM.ι k) → Σ k, ρ k) (κ : K → K₃) (v : (Σ k, J k) → Σ k, ρ k) (Ω₃ : Type) (_ : Field Ω₃) (_ : CharZero Ω₃)
      (y : (Σ k, ρ k) → Ω₃) (β : MRing ρ) (d : K₃ → ℕ),
      IsBlockMap κ₁ v₁ ∧ IsBlockMap κ v ∧ mCoordIdeal (y ∘ v₁) = RM.P ∧ mCoordIdeal (y ∘ v) = mCoordIdeal Dc.y ∧
      IsArithVar (mCoordIdeal y) (Top.dimFl (CMType H) (D.p + D.q) + 1) ∧ IsMultiHomog β d ∧ β ∉ mCoordIdeal y ∧
      IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) ≠ 0 ∧
      (∀ z ∈ mcPts (mCoordIdeal y), evC z β ≠ 0 → (fun p => z (v p)) ∉ Dc.Bd) ∧
      ∀ L L' : HermLine ρ, IsPullHerm κ₁ v₁ (Top.combLine oR.sing (muExp D.p)) L → IsPullHerm κ v (muVert Hd B) L' →
        IsoLineOn (mCoordIdeal y) {z | z ∈ mcPts (mCoordIdeal y) ∧ evC z β ≠ 0} L L'

section Tame

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P B : Ideal (MRing J)} {e : ℕ}

def Tame (R : AnLogRes P B e) (Θ L : LocPot R.X) (s : R.X → R.X → ℂ) (A : ℝ → HermLine J) : Prop :=
  ∃ (ref : HermLine J) (C : ℝ), IsSmoothHerm ref ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (A t) ∧ (A t).a = ref.a ∧
    IsPsh R.A (potOf R (A t) + Θ.rsmul C) ∧ ∀ x ∉ bdry s,
      -C * Real.log (rW L s x) ≤ Real.log ((A t).h (R.lift x x)) - Real.log (ref.h (R.lift x x)) ∧
        Real.log ((A t).h (R.lift x x)) - Real.log (ref.h (R.lift x x)) ≤ C

end Tame

def Replace : Prop :=
  PB.Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (P B : Ideal (MRing J)) (e a b : ℕ) (R : AnLogRes P B e) (Θ L : LocPot R.X) (s : R.X → R.X → ℂ)
    (nb : ℕ) (mb : Fin nb → ℕ) (Wb : Fin nb → Set R.X) (σ : Type) [Fintype σ] (A : ℝ → σ → HermLine J) (M : ℝ → HermLine J)
    (m : σ → ℤ) (n : Fin b → σ → ℤ) (f g : MRing J) (w : ℝ → ((Σ k, J k) → ℂ) → ℝ) (C : ℝ),
    a + b = e + 1 → IsArithVar P (e + 1) → IsPotential R.A Θ → IsPosPot R.A Θ → IsPotential R.A L → IsSection R.A L s →
    IsSNC R.A L s mb Wb → (∀ x, logNormSec L s x ≤ 0) → (∀ i, Tame R Θ L s fun t => A t i) → Tame R Θ L s M →
    (∀ᶠ t in 𝓝[>] (0 : ℝ), IsLineIso P (Top.combLine (A t) m).a (M t).a f g ∧
      IsDefectOn P (mcPts P) f g (Top.combLine (A t) m) (M t) (w t) ∧
      ∀ x ∉ bdry s, |w t (R.lift x x)| ≤ C * Real.log (rW L s x)) →
    (∀ K' ⊆ (bdry s)ᶜ, IsCompact K' → TendstoUniformlyOn (fun t x => w t (R.lift x x)) (fun _ => 0) (𝓝[>] 0) K') →
    Tendsto (fun t => II K J P (a + b) (Fin.append (fun _ : Fin a => M t) fun j => Top.combLine (A t) (n j)) -
      II K J P (a + b) (Fin.append (fun _ : Fin a => Top.combLine (A t) m) fun j => Top.combLine (A t) (n j)))
      (𝓝[>] 0) (𝓝 0)

def RegUnif : Prop :=
  ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (n : ℕ) (M : CxModel P n)
    (Xo : Set ((Σ k, J k) → ℂ)) (A : HermLine J) (S : LogLogRegularisationSetting M Xo A) (V : Set M.Xc) (g : M.Xc → ℝ), S.IsTied →
    IsOpen V → ContinuousOn g V → (∀ x ∈ V ∩ S.R.Yo, g x = S.R.ph x) →
    (∃ C : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ x, S.regWeight t x ≤ C) ∧ ∀ x ∈ V, g x ≤ S.regWeight t x) ∧
      ∀ K' ⊆ V, IsCompact K' → TendstoUniformlyOn S.regWeight g (𝓝[>] 0) K'

def BaseSide : Prop :=
  ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type)
    [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W)
    (Hd : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (B : ℕ) (K' : Type) [Fintype K'] (J' : K' → Type)
    [∀ k, Fintype (J' k)] (P' B' : Ideal (MRing J')) (e : ℕ) (R : AnLogRes P' B' e) (κ : K → K') (v : (Σ k, J k) → Σ k, J' k)
    (Θ : LocPot R.X) (Mt : ℝ → HermLine J'), S.IsTied → IsBlockMap κ v → imageZ v P' = mCoordIdeal D.y →
    IsPotential R.A Θ → IsPosPot R.A Θ → (∀ t, IsPullHerm κ v (muReg Hd S B t) (Mt t)) →
    ∃ (ref : HermLine J') (C : ℝ), IsSmoothHerm ref ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (Mt t) ∧ (Mt t).a = ref.a ∧ IsPsh R.A (potOf R (Mt t) + Θ.rsmul C) ∧
        (∀ x, Real.log ((Mt t).h (R.lift x x)) - Real.log (ref.h (R.lift x x)) ≤ C) ∧
        ∀ x, (fun p => R.lift x x (v p)) ∉ D.Bd →
          Real.log ((muVert Hd B).h fun p => R.lift x x (v p)) ≤ Real.log ((Mt t).h (R.lift x x))) ∧
      ∀ K₀ ⊆ {x | (fun p => R.lift x x (v p)) ∉ D.Bd}, IsCompact K₀ → TendstoUniformlyOn
        (fun t x => Real.log ((Mt t).h (R.lift x x)) - Real.log ((muVert Hd B).h fun p => R.lift x x (v p)))
        (fun _ => 0) (𝓝[>] 0) K₀

end LevelTowerAlt.Comparison₂
end
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.LogOmBound
section
open NumberField GlobalTheory.CompanionTheory.Ar

namespace LevelTowerAlt

theorem logOm_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), ∃ (_ : NeZero H.d) (χ : DirichletCharacter ℂ H.d),
      GlobalTheory.IsKroneckerChar χ ∧ |(GlobalTheory.CM.logOm E χ).re| ≤ C * (1 + Real.log (hostRd E) + |hostLval H|) := by
  have hγ : 0 < Real.eulerMascheroniConstant :=
    lt_trans (by norm_num) Real.one_half_lt_eulerMascheroniConstant
  refine ⟨1 + Real.eulerMascheroniConstant + |Real.log (2 * Real.pi)|, by positivity, ?_⟩
  intro E _ _ _ H
  haveI : Fact (Nat.Prime H.d) := ⟨H.d_prime⟩
  refine ⟨⟨H.d_prime.ne_zero⟩, (quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ),
    GlobalTheory.isKroneckerChar_quadraticChar (by have := H.d_mod; omega), ?_⟩
  have hL : (GlobalTheory.CM.logOm E ((quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ))).re =
      Real.eulerMascheroniConstant + Real.log (2 * Real.pi / rootDiscr E) - hostLval H := by
    simp only [GlobalTheory.CM.logOm, Complex.sub_re, Complex.ofReal_re]
    rfl
  have hrd : rootDiscr E = hostRd E := by
    unfold hostRd
    rw [NumberField.rootDiscr_def, Int.cast_abs, one_div]
  have h1 : 1 ≤ hostRd E := by
    unfold hostRd
    apply Real.one_le_rpow
    · have := Int.one_le_abs (NumberField.discr_ne_zero E)
      rw [← Int.cast_abs]
      exact_mod_cast this
    · positivity
  have hb0 : 0 ≤ Real.log (hostRd E) := Real.log_nonneg h1
  have hlogdiv : Real.log (2 * Real.pi / rootDiscr E) = Real.log (2 * Real.pi) - Real.log (hostRd E) := by
    rw [hrd, Real.log_div (by positivity) (by linarith)]
  rw [hL, hlogdiv]
  have ha1 := le_abs_self (Real.log (2 * Real.pi))
  have ha2 := neg_abs_le (Real.log (2 * Real.pi))
  have hl1 := le_abs_self (hostLval H)
  have hl2 := neg_abs_le (hostLval H)
  have hb : |Real.eulerMascheroniConstant + (Real.log (2 * Real.pi) - Real.log (hostRd E)) - hostLval H| ≤
      Real.eulerMascheroniConstant + |Real.log (2 * Real.pi)| + Real.log (hostRd E) + |hostLval H| :=
    abs_le.2 ⟨by linarith, by linarith⟩
  have hm : 0 ≤ (Real.eulerMascheroniConstant + |Real.log (2 * Real.pi)|) *
      (Real.log (hostRd E) + |hostLval H|) := by positivity
  nlinarith

end LevelTowerAlt
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.NefFibresBlockEmbedding
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

open GroundTheory.Heights₂.Heights ReciprocityTheory.ChartRestriction.G.AI.I1 MvPolynomial in
theorem LevelTowerAlt.nef_fibres_block_embedding : PB.Inputs → ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (a : K → ℤ) (a' : K' → ℤ), Function.Injective bk → (∀ k x, y' ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) → (∀ k, ∃ x, y' ⟨k, x⟩ ≠ 0) → (∀ k, a' (bk k) = a k) → (∀ k', k' ∉ Set.range bk → a' k' = 0) → NefOnFibres (mCoordIdeal y') a' → NefOnFibres (mCoordIdeal y) a := by
  classical
  intro _ Ω Ω' _ _ _ i K K' _ _ J J' _ _ y y' bk bx a a' hbk hy hy' ha ha' hnef W hW hle hchar hdim
  have hp : (charOf W).Prime := PB.prime_charOf_of_ne_zero hW.1 hchar
  have hpW := Inter.C_charOf_mem W
  generalize charOf W = p at hp hpW
  have : Fact p.Prime := ⟨hp⟩
  let v : (Σ k, J k) → Σ k, J' k := fun x => ⟨bk x.1, bx x.1 x.2⟩
  have hv : IsBlockMap bk v := by
    refine ⟨hbk, ?_, fun _ => rfl, ?_⟩
    · rintro ⟨k, x⟩ ⟨k₁, x₁⟩ h
      obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.1 h
      obtain rfl := hbk h1
      obtain rfl := (bx k).injective (eq_of_heq h2)
      rfl
    · rintro ⟨_, x⟩ ⟨k, rfl⟩
      exact ⟨⟨k, (bx k).symm x⟩, by simp [v]⟩
  obtain ⟨L, _, _, w, c, hL, hc, hw⟩ := LevelTowerAlt.exists_curve_point p hW hpW hdim
  have hle' : mCoordIdeal (fun x : Σ k, J k => y' ⟨bk x.1, bx x.1 x.2⟩) ≤ mCoordIdeal w := by
    simp only [hy]
    rw [hw, CoordinateConeArithVar.mCoordIdeal_comp i y]
    exact hle
  obtain ⟨k₀, L₁, _, _, σ, _, _, w₀, w', h1, h2, h3, h4⟩ := LevelTowerAlt.exists_lift_blk y' bk bx hbk hy' w c hc hle'
  have : CharP L p := charP_of_injective_algebraMap (algebraMap (ZMod p) L).injective p
  have : CharP k₀ p := σ.charP σ.injective p
  have : CharP L₁ p := charP_of_injective_algebraMap (algebraMap k₀ L₁).injective p
  let _ : Algebra (ZMod p) k₀ := ZMod.algebra k₀ p
  let _ : Algebra (ZMod p) L₁ := ZMod.algebra L₁ p
  have : IsScalarTower (ZMod p) k₀ L₁ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hL₁ : Algebra.trdeg (ZMod p) L₁ ≤ 1 := by
    rw [← trdeg_add_eq (ZMod p) k₀, trdeg_eq_zero (R := k₀), add_zero, ← hL]
    exact trdeg_le_of_injective ⟨σ, fun r => RingHom.congr_fun
      (Subsingleton.elim (σ.comp (algebraMap (ZMod p) k₀)) (algebraMap (ZMod p) L)) r⟩ σ.injective
  obtain ⟨hpW', m, hm, hmd⟩ := LevelTowerAlt.dim_le p hL₁ w'
  choose c' hc' using h3
  have hW' : IsMultiProjPrime (mCoordIdeal w') := ⟨RingHom.ker_isPrime _, CoordinateConeArithVar.isMultiHomogIdeal w',
    CoordinateConeArithVar.relevant w' c' hc'⟩
  have himg : AI.I4.imageZ v (mCoordIdeal w') = W := by
    rw [← Inter.BlockRatioAlgebraic.mCoordIdeal_comp_v hv, ← hw, ← funext h1,
      CoordinateConeArithVar.mCoordIdeal_comp σ w₀, ← CoordinateConeArithVar.mCoordIdeal_comp (algebraMap k₀ L₁) w₀]
    exact congrArg _ (funext h2)
  have hQ' := LevelTowerAlt.map_red_prime p hW' hpW'
  have hcm' := Bridge.GeoNum.comap_map_eq p (LevelTowerAlt.ker_red_le p hpW')
  have hcm := Bridge.GeoNum.comap_map_eq p (LevelTowerAlt.ker_red_le p hpW)
  set Q' := (mCoordIdeal w').map (Bridge.GeoNum.red p) with hQ'_def
  set Q := W.map (Bridge.GeoNum.red p) with hQ_def
  have hiv : imageVar (ZMod p) v Q' = Q := by
    ext f
    obtain ⟨g, rfl⟩ := Bridge.GeoNum.red_surjective p f
    change rename v (Bridge.GeoNum.red p g) ∈ Q' ↔ g ∈ Q.comap (Bridge.GeoNum.red p)
    rw [hcm, ← himg, Bridge.GeoNum.red, ← map_rename]
    change rename v g ∈ Q'.comap (Bridge.GeoNum.red p) ↔ _
    rw [hcm']
    rfl
  have hQd : ringKrullDim (MRingOver (ZMod p) J ⧸ Q) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [← ringKrullDim_eq_of_ringEquiv (Bridge.GeoNum.quotEquiv p Q), hcm]
    exact hdim
  have hcd : FieldNumbers.relDim (FieldNumbers.contractPrime (Targets.ProjContract.emb hv) Q') =
      ((1 : ℕ) : WithBot (WithTop ℤ)) := by
    rw [FieldNumbers.CutRegular.relDim_eq_natCast_iff, ← Targets.ProjContract.ringKrullDim_imageVar hv, hiv]
    exact hQd
  have hge := FieldNumbers.ContractRelDimLe.proof (ZMod p) K K' (Targets.ProjContract.emb hv) J' Q' hQ'
  have hrel : FieldNumbers.relDim Q' = ((((m : ℤ) - Fintype.card K' : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := by
    unfold FieldNumbers.relDim
    rw [hmd]
    rfl
  have hm' : m = 1 + Fintype.card K' := by
    rw [hcd, hrel] at hge
    have h5 : ((1 : ℕ) : ℤ) ≤ (m : ℤ) - Fintype.card K' :=
      WithTop.coe_le_coe.1 (WithBot.coe_le_coe.1 hge)
    omega
  subst hm'
  have hQ'd := (FieldNumbers.CutRegular.relDim_eq_natCast_iff Q' 1).2 hmd
  have hdim' : ringKrullDim (MRing J' ⧸ mCoordIdeal w') = ((1 + Fintype.card K' : ℕ) : WithBot ℕ∞) := by
    rw [← hcm', ringKrullDim_eq_of_ringEquiv (Bridge.GeoNum.quotEquiv p Q')]
    exact hmd
  have h6 := hnef _ hW' h4 (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.charOf_ne_zero_of_mem hp.ne_zero (by simpa using hpW')) hdim'
  rw [← Bridge.intNum_map_eq_geoNum p 1 _ hW' hpW' hdim'] at h6
  rw [← Bridge.intNum_map_eq_geoNum p 1 _ hW hpW hdim]
  have := hQ'.isPrime
  have h7 := (GlobalTheory.CompanionTheory.FieldNumbers.projectionFormulaDegree (ZMod p) K K' (Targets.ProjContract.emb hv) J' Q' hQ' 1
    hQ'd hcd fun _ => a).2
  have h8 := FieldNumbers.FunctionFieldFinite.proof FieldNumbers.MChartDehomog.proof
    (FieldNumbers.MChartTrdeg.proof FieldNumbers.MChartHomog.proof) (ZMod p) K K' (Targets.ProjContract.emb hv) J' Q'
    hQ' (hcd.trans hQ'd.symm)
  have h9 : FieldNumbers.pullDeg (Targets.ProjContract.emb hv) a = a' := by
    funext k'
    by_cases hk : k' ∈ Set.range bk
    · obtain ⟨k, rfl⟩ := hk
      rw [ha]
      exact hbk.extend_apply _ _ k
    · rw [ha' k' hk]
      exact Function.extend_apply' _ _ _ hk
  have h10 := FieldNumbers.RenameIntNum.full (ZMod p) K K J (fun k => J' (Targets.ProjContract.emb hv k))
    (Equiv.refl K) (Targets.ProjContract.blockEquiv hv)
    (fun x => hbk ((congrArg Sigma.fst (Targets.ProjContract.blockIncl_blockEquiv hv x))))
    (FieldNumbers.contractPrime (Targets.ProjContract.emb hv) Q') 1 fun _ => a
  have h11 : NumbersDVR.intNum (ZMod p) Q (fun _ : Fin 1 => a) =
      NumbersDVR.intNum (ZMod p) (FieldNumbers.contractPrime (Targets.ProjContract.emb hv) Q') (fun _ : Fin 1 => a) := by
    rw [← hiv, Targets.ProjContract.imageVar_eq hv]
    exact h10
  rw [h9, ← h11] at h7
  change 0 ≤ NumbersDVR.intNum (ZMod p) Q' (fun _ : Fin 1 => a') at h6
  rw [h7] at h6
  exact nonneg_of_mul_nonneg_right h6 (by exact_mod_cast Nat.pos_of_ne_zero h8)
end

