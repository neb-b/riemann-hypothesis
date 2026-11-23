module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TorusAlgebraicHolds
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelFamilyNearbyPeriodsSameComponent
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInClassicalFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.KeyOfPeriod

theorem exists_keyIn_classicalFrame :
    ∀ (g : ℕ) (τ₀ : Matrix (Fin g) (Fin g) ℂ) (a₀ b₀ : Fin g → ℂ), 1 ≤ g → τ₀.IsSymm → (τ₀.map Complex.im).PosDef → (∀ i, a₀ i = 0 ∨ a₀ i = 1 / 2) → (∀ i, b₀ i = 0 ∨ b₀ i = 1 / 2) → ∃ (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L x.P.g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ), τ = τ₀.submatrix (Fin.cast h) (Fin.cast h) ∧ (a = fun i => a₀ (i.cast h)) ∧ (b = fun i => b₀ (i.cast h)) ∧ τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, b i = 0 ∨ b i = 1 / 2) ∧ (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin x.P.g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧ u.IsRig x.rig ∧ u.IsFn x.th (thetaChar τ a b) ∧ (∀ i, u.IsDiff (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (x.v i)) := by
  intro g τ₀ a₀ b₀ hg hs hp ha hb
  obtain ⟨x, h, hx⟩ := exists_keyIn_normalAt GlobalTheory.thetaUnifAV_all GlobalTheory.torusAlgebraic_holds g τ₀ a₀ b₀ hg hs hp
    ⟨ha, hb⟩
  obtain ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩ := (GlobalTheory.KeyPow.normalAt_one_iff x _ _ _).1 hx
  exact ⟨x, h, u, _, _, _, rfl, rfl, rfl, h₁, h₂, fun i => ha _, fun i => hb _, h₃, h₄, h₅, h₆⟩

end GlobalTheory.KeyOfPeriod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelFamilyStandardLevelPointsSameComponent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.SiegelConnected

theorem convex_siegel (h : ℕ) :
    Convex ℝ {τ : Matrix (Fin h) (Fin h) ℂ | τ.IsSymm ∧ (τ.map Complex.im).PosDef} := by
  rintro x ⟨hx, hx'⟩ y ⟨hy, hy'⟩ a b ha hb hab
  refine ⟨(hx.smul a).add (hy.smul b), ?_⟩
  have e : (a • x + b • y).map Complex.im = a • x.map Complex.im + b • y.map Complex.im := by
    ext i j
    simp
  rw [e]
  rcases ha.eq_or_lt with rfl | ha'
  · have : b = 1 := by simpa using hab
    subst this
    simpa using hy'
  · exact (hx'.smul ha').add_posSemidef (hy'.posSemidef.smul hb)

variable {o : Type} [CommRing o] {S : Scheme.{0}} {s : S ⟶ Sp o} {σ : o →+* ℂ}

theorem sameComp_symm {p q : Sp ℂ ⟶ S} (h : SameComp s σ p q) : SameComp s σ q p := by
  obtain ⟨hp, hq, H⟩ := h
  refine ⟨hq, hp, fun z => ?_⟩
  rw [← connectedComponent_eq (H z)]
  exact mem_connectedComponent

theorem sameComp_trans {p q r : Sp ℂ ⟶ S} (h : SameComp s σ p q) (h' : SameComp s σ q r) :
    SameComp s σ p r := by
  obtain ⟨hp, hq, H⟩ := h
  obtain ⟨hq', hr, H'⟩ := h'
  refine ⟨hp, hr, fun z => ?_⟩
  rw [connectedComponent_eq (H' z)]
  exact H z

theorem mem_siegel_of_ptAt {h k : ℕ} {ζ : o} {c : SiegPre h k ζ s} {p : Sp ℂ ⟶ S}
    {τ : Matrix (Fin h) (Fin h) ℂ} (H : PtAt c p τ) : τ.IsSymm ∧ (τ.map Complex.im).PosDef := by
  obtain ⟨P, lev, φ, hP, -⟩ := H
  exact ⟨hP.2.1, hP.2.2.1⟩

theorem sameComp_of_ptAt : Out.Laws → Out.Laws2 → ThetaUnifAV → GlobalTheory.TorusAlgebraic → ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ), 1 ≤ h → 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → ∀ (τ τ' : Matrix (Fin h) (Fin h) ℂ) (p q : Sp ℂ ⟶ F.X), p ≫ F.s = spMap σ → q ≫ F.s = spMap σ → PtAt F.univ p τ → PtAt F.univ q τ' → SameComp F.s σ p q := by
  intro hL hL2 hT hA h k K _ ζ σ F hh hk hodd hζ τ τ' p q hp hq hpτ hqτ
  have hopen := _root_.GlobalTheory.SiegelNearby.exists_nhds_sameComp hL hL2 hT h k K ζ σ F hh hk hodd hζ
  have hex : ∀ t : Matrix (Fin h) (Fin h) ℂ, t.IsSymm ∧ (t.map Complex.im).PosDef →
      ∃ r : Sp ℂ ⟶ F.X, r ≫ F.s = spMap σ ∧ PtAt F.univ r t := by
    rintro t ⟨ht, ht'⟩
    obtain ⟨P, lev, hP⟩ := _root_.GlobalTheory.SiegelObject.exists_perLev_of_siegel hT hA h k t ht ht'
    obtain ⟨r, φ, hr, hsq, hlev⟩ := GlobalTheory.KeyFam.exists_point_of_perLev hL h k K ζ σ F hh hk hodd hζ P t lev hP
    exact ⟨r, hr, P, lev, φ, hP, hsq, hlev⟩
  have key := (convex_siegel h).isPreconnected.induction₂'
    (fun t t' => ∀ r : Sp ℂ ⟶ F.X, r ≫ F.s = spMap σ → PtAt F.univ r t →
      ∃ r' : Sp ℂ ⟶ F.X, r' ≫ F.s = spMap σ ∧ PtAt F.univ r' t' ∧ SameComp F.s σ r r')
    (by
      intro x hx
      obtain ⟨r₀, hr₀, hr₀x⟩ := hex x hx
      obtain ⟨N, hN, HN⟩ := hopen x r₀ hr₀ hr₀x
      filter_upwards [mem_nhdsWithin_of_mem_nhds hN, self_mem_nhdsWithin] with y hyN hy
      refine ⟨fun r hr hrx => ?_, fun r hr hry => ⟨r₀, hr₀, hr₀x, HN y hyN r hr hry⟩⟩
      obtain ⟨r', hr', hr'y⟩ := hex y hy
      exact ⟨r', hr', hr'y, sameComp_trans (HN x (mem_of_mem_nhds hN) r hr hrx)
        (sameComp_symm (HN y hyN r' hr' hr'y))⟩)
    (by
      intro x y z _ _ _ hxy hyz r hr hrx
      obtain ⟨r', hr', hr'y, h₁⟩ := hxy r hr hrx
      obtain ⟨r'', hr'', hr''z, h₂⟩ := hyz r' hr' hr'y
      exact ⟨r'', hr'', hr''z, sameComp_trans h₁ h₂⟩)
    (mem_siegel_of_ptAt hpτ) (mem_siegel_of_ptAt hqτ)
  obtain ⟨q', hq', hq'τ, h₁⟩ := key p hp hpτ
  obtain ⟨N, hN, HN⟩ := hopen τ' q hq hqτ
  exact sameComp_trans h₁ (HN τ' (mem_of_mem_nhds hN) q' hq' hq'τ)

end GlobalTheory.SiegelConnected
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRulePowComplex
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

namespace GlobalTheory.KeyCl

theorem value_of_normalAt {κ : Rule} (hH : Homog (fun _ => 1) κ) (hT : ThetaOne κ) (x : KeyIn ℂ)
    {τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ} {a b : Fin x.P.g → ℂ} {c : ℂ} (hab : KeyPow.charHalf x.P.g a b)
    (hc : c ≠ 0) (hM : M.det ≠ 0) (h : KeyPow.NormalAt x τ M a b c) : (κ ℂ x : ℂ) = M.det ^ 4 / c ^ 8 := by
  have key := KeyPow.value_at_normalForm (fun _ => 1) 0 (κ ℂ) x.P.g a b (Nat.zero_le _)
    (fun P hg rig hr th hth v hv th' hth' v' hv' a M _ h₁ h₂ =>
      hH ℂ P hg rig hr th hth v hv th' hth' v' hv' a M h₁ h₂)
    (fun z hz σ hN => by
      obtain ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩ := (KeyPow.normalAt_one_iff z σ _ _).1 hN
      exact hT z u σ _ _ h₁ h₂ (fun i => hab.1 _) (fun i => hab.2 _) h₃ h₄ h₅ h₆)
    x rfl τ M c hc hM h
  simpa only [_root_.pow_one] using key

theorem value_pow_complex : ∀ κ : Rule, Homog (fun _ => 1) κ → ThetaOne κ →
    ∀ (x y : KeyIn ℂ) (j : ℕ), GlobalTheory.KeyPow.IsKeyPow y x j → κ ℂ y = κ ℂ x ^ j := by
  intro κ hH hT x y j hp
  obtain ⟨⟨τ, M, a, b, c, hab, hc, hM, hN⟩, -⟩ := KeyNormalExists.exists_normalAt GlobalTheory.thetaUnifAV_all x
  have hre : ∀ f : Fin x.P.g → ℂ, (∀ i, f i = 0 ∨ f i = 1 / 2) → (fun k => ((f k).re : ℂ)) = f := by
    intro f hf
    funext k
    rcases hf k with h | h <;> rw [h] <;> norm_num
  have ha := hre a hab.1
  have hb := hre b hab.2
  obtain ⟨e, τ', M', hdet, hN'⟩ := KeyPow.normalAt_pow x y j τ M (fun k => (a k).re) (fun k => (b k).re) c hp
    (by rw [ha, hb]; exact hN)
  have hx := value_of_normalAt hH hT x hab hc hM hN
  have hy := value_of_normalAt hH hT y
    ⟨fun p => by rw [congrFun ha (e.symm p).2]; exact hab.1 _,
      fun p => by rw [congrFun hb (e.symm p).2]; exact hab.2 _⟩
    (pow_ne_zero j hc) (by rw [hdet]; exact pow_ne_zero j hM) hN'
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hy, hx, hdet, div_pow, ← _root_.pow_mul, ← _root_.pow_mul, ← _root_.pow_mul,
    ← _root_.pow_mul, mul_comm j 4, mul_comm j 8]

end GlobalTheory.KeyCl
end

