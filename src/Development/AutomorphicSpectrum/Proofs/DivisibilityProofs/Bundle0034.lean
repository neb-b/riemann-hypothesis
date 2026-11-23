module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0249
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0033
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTiesDistinctGeneric
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0151
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0071

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerM2
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem m2_of_good_tower : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.M2 := by
  intro _ E _ _ _ _ H D Xo l c Y _ T o II hglob _ hp hq
  obtain ⟨Yl, hg, hloc, -, -, hdom⟩ := hglob
  intro B a p hpr hnS mu hmu hnef
  have hpbad : p ∉ T.bad := fun hb =>
    hnS (show Nat.Prime p ∧ (p ≤ B ∨ p ∈ T.bad) from ⟨hpr, Or.inr hb⟩)
  have h2 : 2 < p := lt_of_le_of_ne hpr.two_le (fun h => hpbad (by rw [← h]; exact T.two_mem))
  have hdisc : ¬ ((p : ℤ) ∣ NumberField.discr E) := fun hd =>
    hpbad ((o.toTowerOrigin.bad_iff p).2 ⟨hpr, dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd 2) _⟩)
  have hpS : p ∉ o.toTowerOrigin.S B := fun h => hnS ((o.toTowerOrigin.S_iff B p).1 h)
  rw [o.toTowerOrigin.j_eq] at hnef
  exact _root_.GlobalTheory.CompanionTheory.Ar.Conj.hodge_cpt_global_nefness E H D Xo Yl
    (fun p W hp hW i => ⟨((hloc p W hp hW).2 i).1, ((hloc p W hp hW).2 i).2.1⟩)
    l c hg Y hdom hp hq (o.toTowerOrigin.S B) (T.M B a) (o.toTowerOrigin.Or B a).𝔐
    (o.toTowerOrigin.Or B a).Fl (o.toTowerOrigin.Or B a).e (o.toTowerOrigin.Or B a).lines
    p hpr h2 hpS hdisc mu hmu hnef

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.NvalLeOfMul
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace GlobalTheory.CompanionTheory.SmallFin

theorem le_of_mem_span {K R : Type} [Field K] [NumberField K] [CommRing R] [Algebra K R] [Algebra (𝓞 K) R]
    [IsScalarTower (𝓞 K) K R] {la : HeightOneSpectrum (𝓞 K)} {v : R → EReal} (hv : IsVal la v) {C : Submodule K R}
    {n : ℕ} (w : Fin n → C) {d : EReal} (hd : ∀ i, d ≤ v (w i : R)) {x : C}
    (hx : x ∈ Submodule.span (𝓞 K) (Set.range w)) : d ≤ v (x : R) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hd i
  | zero =>
    show d ≤ v 0
    rw [hv.zero]
    exact le_top
  | add x y _ _ hx hy => exact (le_min hx hy).trans (hv.add _ _)
  | smul a x _ hx =>
    have h1 : ((a • x : C) : R) = (a : K) • (x : R) := (algebraMap_smul K a (x : R)).symm
    rw [h1]
    by_cases ha : (a : K) = 0
    · rw [ha, zero_smul, hv.zero]
      exact le_top
    · rw [hv.smul _ _ ha]
      have h2 : (0 : EReal) ≤ (((vAdd la (a : K) : ℤ) : ℝ) : EReal) := by
        exact_mod_cast vAdd_int_nonneg la ha
      exact hx.trans (le_add_of_nonneg_left h2)

theorem adjoin_ratios {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω)
    (hB : GlobalTheory.DegVal.ratioField ev = ⊤) {n : ℕ} (w : Fin n → V) (hs : Submodule.span K (Set.range w) = ⊤) (i₀ : Fin n)
    (h0 : ev (w i₀) ≠ 0) : IntermediateField.adjoin K (Set.range fun i => ev (w i) / ev (w i₀)) = ⊤ := by
  set F := IntermediateField.adjoin K (Set.range fun i => ev (w i) / ev (w i₀)) with hF
  have key : ∀ v, ev v / ev (w i₀) ∈ F := fun v => by
    have hv : v ∈ Submodule.span K (Set.range w) := hs ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _), add_div]
      exact F.add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul, Algebra.smul_def, mul_div_assoc]
      exact F.mul_mem (F.algebraMap_mem a) hx
  rw [eq_top_iff, ← hB, GlobalTheory.DegVal.ratioField, IntermediateField.adjoin_le_iff]
  rintro _ ⟨v, v', rfl⟩
  by_cases h : ev v' = 0
  · rw [h, div_zero]
    exact F.zero_mem
  · have : ev v / ev v' = (ev v / ev (w i₀)) / (ev v' / ev (w i₀)) := by field_simp
    rw [this]
    exact F.div_mem (key v) (key v')

theorem vV_pow {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
    [IsFractionRing V K'] {x : K'} (hx : x ≠ 0) (n : ℕ) : vV V (x ^ n) = (n : ℤ) * vV V x := by
  induction n with
  | zero => simp [vV]
  | succ n ih =>
    rw [pow_succ, vV_mul (pow_ne_zero _ hx) hx, ih]
    push_cast
    ring

theorem nval_le_of_mul {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
    [IsFractionRing V K'] (e : ℕ) {x y : K'} (hx : x ≠ 0) (hy : 0 ≤ vV V y) : nval V e x ≤ nval V e (y * x) := by
  by_cases h : y = 0
  · rw [h, zero_mul, nval_zero]
    exact le_top
  · rw [nval_of_ne hx, nval_of_ne (mul_ne_zero h hx), vV_mul h hx]
    refine EReal.coe_le_coe_iff.2 (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg e))
    have : vV V x ≤ vV V y + vV V x := by omega
    exact_mod_cast this

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem intAll_all (Xo : Moduli Dw l) (c : Coeff l) : Formalism.L2.PjFree.IntAll Xo c := by
  obtain ⟨⟨-, -, -, -, hA, hBC⟩, -⟩ := GlobalTheory.Exist.frame_laws_of_moduli E H Dw l Xo c
  have hE : IntFrExt Xo c := by
    rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with h | h
    · exact GlobalTheory.RankZeroFrames.intFrExt_of_rank_zero E H Dw l Xo c h
    · exact GlobalTheory.AnyLevelFrame.intFrExt E H Dw l Xo c h
  have hB : FrBaseChg Xo c := fun S S' _ _ _ _ φ y =>
    GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c S S' φ y
  exact intAll_of_allTest hE hB hA

theorem evR_test {g : Rul Xo c}
    (hg : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) g) {L : Type} [CommRing L]
    [Algebra c.F L] (p : TRing c.F) (χ : p.R →ₐ[c.F] L) (u : FrPt Xo c p.R) (z : FrPt Xo c L) (hz : FrMap χ u z) :
    evR Xo c g z = χ (g p u) := by
  obtain ⟨⟨-, hC, -, -, -, -⟩, -⟩ := GlobalTheory.Exist.frame_laws_of_moduli E H Dw l Xo c
  have hWD := evalWD_fr hC
  have hft : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨p, χ, u, hz⟩
  unfold evR evalAt
  rw [dite_eq_left hft]
  exact hWD g hg L _ p _ χ _ u z hft.choose_spec.choose_spec.choose_spec hz

theorem evR_bor {e : Ix Dw → ℤ} {g : Rul Xo c} (hg : g ∈ secZ Xo c e) {L : Type} [Field L] [Algebra c.F L]
    (p : TRing c.F) (χ : p.R →ₐ[c.F] L) (u : FrPt Xo c p.R) (z w : FrPt Xo c L) (hz : FrMap χ u z)
    (t : Ix Dw → Lˣ) (hb : FrBor t z w) :
    evR Xo c g w = ((∏ i, t i ^ e i : Lˣ) : L) * χ (g p u) := by
  obtain ⟨⟨-, -, hB, -, hA, -⟩, -⟩ := GlobalTheory.Exist.frame_laws_of_moduli E H Dw l Xo c
  rw [← evR_test hg.1 p χ u z hz]
  exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.evalAt_bor_zpow hB e hg.1 hg.2 L t z w (hA L z) (hA L w) hb

theorem prod_exZ_nsmul {M : Type} [CommGroup M] (t : Ix Dw → M) (G : WTZ E) (n : ℕ) :
    ∏ i, t i ^ exZ Dw (n • G) i = (∏ i, t i ^ exZ Dw G i) ^ n := by
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  have : exZ Dw (n • G) i = exZ Dw G i * n := by
    cases i <;> simp [exZ, mul_comm]
  rw [this, zpow_mul, zpow_natCast]


end Main

end GlobalTheory.CompanionTheory.SmallFin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerOriginVectorBundle
section
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TowerPropA

theorem mono_spMap_ringOfIntegers (F : Type) [Field F] [NumberField F] :
    Mono (spMap (algebraMap (𝓞 F) F)) := by
  have := IsPreimmersion.of_isLocalization (S := F) (nonZeroDivisors (𝓞 F))
  exact inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 F) F))))

theorem genPt_eq_of_factor {X : Scheme.{0}} {Ω Ω₁ Ω₂ : Type} [Field Ω] [Field Ω₁] [Field Ω₂]
    {a : Spec (CommRingCat.of Ω) ⟶ X} {ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X} {ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X}
    {g₁ : Ω₁ →+* Ω} {g₂ : Ω₂ →+* Ω}
    (h₁ : a = Spec.map (CommRingCat.ofHom g₁) ≫ ξ₁) (h₂ : a = Spec.map (CommRingCat.ofHom g₂) ≫ ξ₂) :
    genPt ξ₁ = genPt ξ₂ := by
  have e₁ : ∀ w : Spec (CommRingCat.of Ω), genPt ξ₁ = a w := by
    intro w
    rw [h₁, Scheme.Hom.comp_apply]
    exact congrArg ξ₁ (Subsingleton.elim (α := PrimeSpectrum Ω₁) _ _)
  have e₂ : ∀ w : Spec (CommRingCat.of Ω), genPt ξ₂ = a w := by
    intro w
    rw [h₂, Scheme.Hom.comp_apply]
    exact congrArg ξ₂ (Subsingleton.elim (α := PrimeSpectrum Ω₂) _ _)
  exact (e₁ (IsLocalRing.closedPoint Ω)).trans (e₂ (IsLocalRing.closedPoint Ω)).symm

theorem propA_of_origin : CmpPair → TwistAut → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : TowerOrigin Y T), IsGalois ℚ E → (∀ B a, (o.Or B a).𝔐.OmVB) → (∀ a, (∀ x : (o.Sys a).X, ∃ (U : Set (o.Sys a).X) (lam : (o.Sys a).X → Fin ((o.Fx a).m + 1) → ℂ), IsOpen U ∧ x ∈ U ∧ (∀ i, (o.Sys a).A.HoloOn U fun y => lam y i) ∧ (∀ y ∈ U, ∃ a₀ : ℂ, a₀ ≠ 0 ∧ lam y = a₀ • (o.Fx a).pt y) ∧ ∀ p, lam x p ≠ 0 → ∀ j, x ∈ ((o.Sys a).A.chart j).source → (fderiv ℂ (fun z i => lam (((o.Sys a).A.chart j).symm z) i / lam (((o.Sys a).A.chart j).symm z) p) ((o.Sys a).A.chart j x)).ker = ⊥)) → (∀ B a a', ∀ p ∈ o.S B, (o.Or B a').𝔐.R p = (o.Or B a).𝔐.R p) → T.Conv II → T.PropA II := by
  intro hpair htw II hII E _ _ _ H D l Xo c Y _ T o hgal hOm hhol hR hconv
  have : FiniteDimensional ℚ c.F := c.fin
  have : NumberField c.F := ⟨⟩
  have hmono : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := mono_spMap_ringOfIntegers c.F
  have hinj : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  have hdisc : ∀ B, ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ o.S B := by
    intro B p hp hd
    rw [o.S_iff]
    refine ⟨hp, Or.inr ?_⟩
    rw [o.bad_iff]
    exact ⟨hp, Dvd.dvd.mul_right (Dvd.dvd.mul_left hd 2) _⟩
  have hex : ∀ B a, ∃ t : HodgeTie Y (o.S B) (Module.finrank ℚ c.F) (T.M B a), t.A = (o.Or B a).𝔐 := by
    intro B a
    obtain ⟨-, ⟨x, hx⟩, -⟩ := HodgeCpt.basic _ _ _ _ _ _ _ _ Y _ _ _ _ _ (o.Or B a).𝔐 hinj
    exact _root_.GlobalTheory.CompanionTheory.Ar.hodgeTie_of_rootOrigin E H D l Xo c (𝓞 c.F) _ Y (o.S B) (T.M B a) (o.Sys a) (o.Fx a) (o.Or B a) (hOm B a)
      (hdisc B) (_root_.GlobalTheory.CompanionTheory.Ar.RootAlg.algOver_of_immersion E H D l Xo c (𝓞 c.F) _ Y (o.S B) (T.M B a) (o.Sys a) (o.Fx a) (o.Or B a) x hx
        hmono (hhol a))
  choose tie htie using hex
  have hgen : ∀ B a, genPt (tie B a).A.ξ₀ = genPt (o.Fx a).ξf := by
    intro B a
    rw [htie B a]
    exact genPt_eq_of_factor (o.Or B a).𝔐.fn_over (o.Or B a).g_over
  refine _root_.GlobalTheory.CompanionTheory.Ar.Cmp.HodgeA.propA_of_hodgeTower hpair htw II hII E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y T o.S
    (Module.finrank ℚ c.F) tie hgal hmono hconv ?_ ?_
  · intro B k k' p hp
    rw [htie B k', htie B k]
    exact hR B k k' p hp
  · intro B Φ hΦ
    refine _root_.GlobalTheory.CompanionTheory.Ar.Cmp.PermCpt.exists_perm_isImageCpt E H D l Xo c (𝓞 c.F) _ Y (o.S B) _ T.Comp (T.M B) (tie B) hmono ?_ ?_ Φ hΦ
    · intro k k' h
      apply o.comp_inj
      simpa only [hgen] using h
    · intro q hq
      obtain ⟨a, ha⟩ := o.comp_onto q hq
      exact ⟨a, (hgen B a).trans ha⟩

end GlobalTheory.CompanionTheory.Ar.TowerPropA
end
end

