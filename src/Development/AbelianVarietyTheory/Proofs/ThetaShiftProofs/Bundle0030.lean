module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentVectorPowScaleInvEqStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentVector_pow_scale_inv_eq : ∀ (P : Out.PolAV (Sp ℂ)) (v : epsR ℂ ⟶ P.A) (n : ℕ), 0 < n → IsTangent v → spMap (epsScaleR ((n : ℂ)⁻¹)) ≫ (v ^ n).left = v.left := by
  first | exact @GlobalTheory.AbelianLetters.scale_tangent_pow | exact GlobalTheory.AbelianLetters.scale_tangent_pow | (intros; apply GlobalTheory.AbelianLetters.scale_tangent_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaCharOffNeZeroDifferentiableQuasiPeriodicStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaCharOff_ne_zero_differentiable_quasiPeriodic' : ∀ (g : ℕ) (S : Finset (Fin g)) (τ : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) → (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) → (∀ k ∈ S, c₁ k = 0) → thetaCharOff S τ c₁ c₂ ≠ 0 ∧ Differentiable ℂ (thetaCharOff S τ c₁ c₂) ∧ ∀ m n : Fin g → ℤ, (∀ k ∈ S, n k = 0) → ∃ a : ℂ, a ≠ 0 ∧ ∀ z, thetaCharOff S τ c₁ c₂ (z + ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))) = a * Complex.exp (-(2 * Real.pi * Complex.I) * ((fun i => (n i : ℂ)) ⬝ᵥ z)) * thetaCharOff S τ c₁ c₂ z := by
  first | exact @GlobalTheory.ThetaBlock.thetaCharOff_ne_zero_differentiable_quasiPeriodic | exact GlobalTheory.ThetaBlock.thetaCharOff_ne_zero_differentiable_quasiPeriodic | (intros; apply GlobalTheory.ThetaBlock.thetaCharOff_ne_zero_differentiable_quasiPeriodic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ToUnitCompLeft
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ConstTerm

section Values

variable {A : Type} [CommRing A] {B B₀ : Scheme.{0}}

theorem valR_zpow (x : Sp A ⟶ B) (U : B.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (t : Γ(B, U)ˣ) (u : Aˣ)
    (hu : (u : A) = valR x U t.val) (n : ℤ) : valR x U (t ^ n).val = ((u ^ n : Aˣ) : A) := by
  have e : u = Units.map (HolHom.evalHom x U h).toMonoidHom t := Units.ext (hu.trans (HolHom.valR_eq x U h _))
  rw [e, ← map_zpow, HolHom.valR_eq x U h]
  rfl

theorem le_div {M : LB B} {M₀ : LB B₀} {φ : B ⟶ B₀} (x : Sp A ⟶ B) {k : M₀.ι} {m : M.ι}
    (h₀ : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ M₀.U k) (h : ⊤ ≤ x ⁻¹ᵁ M.U m) :
    ⊤ ≤ x ⁻¹ᵁ (LB.div (M₀.pull φ) M).U (fun _ => k, m) :=
  fun _ hz => ⟨Set.mem_iInter.2 fun _ => h₀ hz, h hz⟩

theorem valR_pullGen {A₀ : Type} [CommRing A₀] (ρ : A₀ →+* A) {M₀ : LB B₀} {K : Type} [Fintype K]
    {ψ : K → (Sp A₀ ⟶ B₀)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M₀ ψ ε)) (k : K → M₀.ι)
    (h : ⊤ ≤ (𝟙 (Sp A₀)) ⁻¹ᵁ LB.wchart M₀ ψ k) :
    valR (𝟙 (Sp A)) _ ((LB.pullGen M₀ ψ ε t (spMap ρ)).s k).val = ρ (valR (𝟙 (Sp A₀)) _ (t.s k).val) := by
  have h' : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ LB.wchart M₀ (fun i => spMap ρ ≫ ψ i) k :=
    fun z _ => Set.mem_iInter.2 fun i => Set.mem_iInter.1 (h (show spMap ρ z ∈ (⊤ : (Sp A₀).Opens) from trivial)) i
  refine (HolHom.valR_res (𝟙 (Sp A)) _ _ h').trans ((HolHom.valR_comp (𝟙 (Sp A)) (spMap ρ) _ _).symm.trans ?_)
  refine Eq.trans ?_ (HolHom.valR_spMap ρ (𝟙 (Sp A₀)) _ h _)
  rw [Category.id_comp, Category.comp_id]
  rfl

theorem prod_factors {G : Type} [CommGroup G] (u : Fin 4 → G) (j : ℕ) :
    (∏ i, u i ^ Out.DegPre.famε j i) * ∏ i, ![u 1, u 2, u 0, u 3] i ^ Out.DegPre.gtε i = u 0 ^ j := by
  simp only [Fin.prod_univ_four, Out.DegPre.famε, Out.DegPre.gtε, Matrix.cons_val, zpow_sub, zpow_neg, zpow_one,
    zpow_natCast]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

end Values

section Points

variable {R : Type} [CommRing R] [IsDomain R] (D : Out.DegPre R) {T : Over (Sp R)} (b : T ⟶ D.P.A) (α : D.X)

theorem comp_famφB (i : Fin 4) : b.left ≫ D.famφB α i = D.gtφT T b α (![2, 0, 1, 3] i) := by
  have h : ∀ p : 𝟙_ (Over (Sp R)) ⟶ D.P.A, b ≫ toUnit D.P.A ≫ p = toUnit T ≫ p := fun p => by
    rw [← Category.assoc, comp_toUnit]
  fin_cases i
  · exact Category.comp_id _
  · change (b ≫ (𝟙 D.P.A * toUnit _ ≫ D.c α)).left = ((toUnit _ ≫ D.c α) * b).left
    rw [MonObj.comp_mul, h, Category.comp_id, mul_comm]
  · exact congrArg (·.left) (h _)
  · exact congrArg (·.left) (h _)

end Points

section Core

open FrameValue

variable [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] {D₀ : Out.DegPre ℂ} {n : ℕ}
  (u : HolUnif D₀.P.A D₀.P.L n) {α₀ : D₀.X} {c : Fin n → ℂ}

theorem toUnit_comp_left {B : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ B) :
    (show Sp ℂ ⟶ _ from (toUnit (Out.TF (R := ℂ) ℂ) ≫ p).left) = p.left := by
  have e : Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ = 𝟙 (Sp ℂ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    exact Spec.map_id _
  change (Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ) ≫ p.left = _
  rw [e]
  exact Category.id_comp _

theorem gtφ_eq (hc : u.ex c = D₀.c α₀) {b₀ : Out.TF (R := ℂ) ℂ ⟶ D₀.P.A} {z : Fin n → ℂ}
    (hb : (show Sp ℂ ⟶ _ from b₀.left) = (u.ex z).left) (k : Fin 4) :
    (show Sp ℂ ⟶ _ from Out.DegPre.gtφ D₀ ℂ b₀ α₀ k) = (u.ex (![c + z, c, z, 0] k)).left := by
  have hb' : b₀ = toUnit _ ≫ u.ex z := Over.OverMorphism.ext (hb.trans (toUnit_comp_left _).symm)
  have h0 : u.ex 0 = η[D₀.P.A] := by
    rw [(u.ker 0).2 (zero_mem _), Hom.one_def, toUnit_unit, Category.id_comp]
  fin_cases k
  · refine Eq.trans ?_ (toUnit_comp_left _)
    change (toUnit _ ≫ D₀.c α₀ * b₀).left = (toUnit _ ≫ u.ex (c + z)).left
    rw [hb', u.ex_add, MonObj.comp_mul, hc]
  · exact (toUnit_comp_left _).trans (congrArg (·.left) hc.symm)
  · exact hb
  · exact (toUnit_comp_left _).trans (congrArg (·.left) h0.symm)


omit [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] in
theorem isLift_famφB (hc : u.ex c = D₀.c α₀) (z : Fin n → ℂ) :
    IsLift u (D₀.famφB α₀) (u.ex z).left ![z, z + c, c, 0] := fun k => by
  have h : ∀ p : 𝟙_ (Over (Sp ℂ)) ⟶ D₀.P.A, u.ex z ≫ toUnit D₀.P.A ≫ p = p := fun p => by
    rw [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
  fin_cases k
  · exact Category.comp_id _
  · change (u.ex z ≫ (𝟙 D₀.P.A * toUnit _ ≫ D₀.c α₀)).left = (u.ex (z + c)).left
    rw [MonObj.comp_mul, h, Category.comp_id, u.ex_add, hc]
  · change (u.ex z ≫ toUnit _ ≫ D₀.c α₀).left = (u.ex c).left
    rw [h, hc]
  · change (u.ex z ≫ toUnit _ ≫ η[D₀.P.A]).left = (u.ex 0).left
    rw [h, (u.ker 0).2 (zero_mem _), Hom.one_def, toUnit_unit, Category.id_comp]

theorem core {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I} {S : Type} [CommRing S]
    [IsLocalRing S] (κ : R →+* S) (ρ : ℂ →+* S) {φ : D.toPre.P.A.left ⟶ D₀.P.A.left}
    (w : LB.Iso D.toPre.P.L (D₀.P.L.pull φ)) (g : Out.GtPt D.toPre (Over.mk (spMap κ))) (g₀ : Out.GtPtF D₀ ℂ)
    {α : D.toPre.X} {z : Fin n → ℂ} (hc : u.ex c = D₀.c α₀) (hb : (show Sp ℂ ⟶ _ from g₀.b.left) = (u.ex z).left)
    (hg : GenRelR (A := S) w (g.s α) (LB.pullGen _ _ _ (g₀.s α₀) (spMap ρ))) {j : ℕ} (s₀ : D₀.SecB j α₀)
    (f : D.toPre.SecB j α) (r : R)
    (hf : ∀ (p : Sp S ⟶ D.toPre.P.A.left) (jf : Fin 4 → D.toPre.P.L.ι) (j₀ : Fin 4 → D₀.P.L.ι),
      p ≫ D.toPre.P.A.hom = spMap κ →
      (∀ i, ⊤ ≤ (p ≫ D.toPre.famφB α i) ⁻¹ᵁ (LB.div (D₀.P.L.pull φ) D.toPre.P.L).U (fun _ => j₀ i, jf i)) →
      ∃ t : Fin 4 → Sˣ, (∀ i, (t i : S) = valR (p ≫ D.toPre.famφB α i) _ (w.s (fun _ => j₀ i, jf i)).val) ∧
        (∏ i, t i ^ Out.DegPre.famε j i : Sˣ) * valR p (LB.wchart D.toPre.P.L (D.toPre.famφB α) jf) (f.f jf) =
          κ r * valR (p ≫ φ) (LB.wchart D₀.P.L (D₀.famφB α₀) j₀) (s₀.f j₀))
    (jM : D.toPre.P.L.ι) (j₀ : D₀.P.L.ι) (jf jt : Fin 4 → D.toPre.P.L.ι) (hj : FormalValue.CohCharts g α jM jf jt)
    (hM : ⊤ ≤ (show Sp S ⟶ _ from g.b.left) ⁻¹ᵁ (LB.div (D₀.P.L.pull φ) D.toPre.P.L).U (fun _ => j₀, jM)) :
    valR (A := S) g.b.left _ (w.s (fun _ => j₀, jM)).val ^ j *
        (FormalValue.famVal g f jf * FormalValue.coordVal g α jt) =
      κ r * ρ (secVal u D₀.P.isLB s₀ (u.ex z).left ![z, z + c, c, 0] *
        genVal u D₀.P.isLB (g₀.s α₀) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![c + z, c, z, 0] * u.fr j₀ z ^ j) := by
  have hφ : ∀ k, FormalValue.coordφ g α k ≫ φ = spMap ρ ≫ (u.ex (![c + z, c, z, 0] k)).left := fun k =>
    (hg.1 k).trans (congrArg (spMap ρ ≫ ·) (gtφ_eq u hc hb k))
  have hq : ∀ i, FormalValue.basePt g ≫ D.toPre.famφB α i = FormalValue.coordφ g α (![2, 0, 1, 3] i) :=
    comp_famφB D.toPre g.b α
  have ejf : ∀ i, jf i = jt (![2, 0, 1, 3] i) := fun i => hj.2.2 (.inr (.inl i)) (.inr (.inr _)) (hq i)
  have ejM : jM = jt 2 := hj.2.2 (.inl PUnit.unit) (.inr (.inr 2)) rfl
  have h₀ : ⊤ ≤ (u.ex z).left ⁻¹ᵁ D₀.P.L.U j₀ := by
    intro y _
    obtain rfl : y = spMap ρ (cpt S) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    exact (congrArg (fun q => q (cpt S) ∈ D₀.P.L.U j₀) (hφ 2)).mp (mem_pull.1 (hM trivial).1)
  obtain ⟨k, hk, ek⟩ : ∃ k : Fin 4 → D₀.P.L.ι,
      (∀ i, ⊤ ≤ (u.ex (![c + z, c, z, 0] i)).left ⁻¹ᵁ D₀.P.L.U (k i)) ∧ k 2 = j₀ := by
    refine ⟨![chartAt D₀.P.isLB (u.ex (c + z)).left, chartAt D₀.P.isLB (u.ex c).left, j₀,
      chartAt D₀.P.isLB (u.ex 0).left], fun i => ?_, rfl⟩
    fin_cases i
    exacts [le_chartAt D₀.P.isLB _, le_chartAt D₀.P.isLB _, h₀, le_chartAt D₀.P.isLB _]
  subst ek ejM
  obtain rfl : jf = fun i => jt (![2, 0, 1, 3] i) := funext ejf
  have hd : ∀ i, ⊤ ≤ FormalValue.coordφ g α i ⁻¹ᵁ (LB.div (D₀.P.L.pull φ) D.toPre.P.L).U (fun _ => k i, jt i) :=
    fun i => le_div _ (hφ i ▸ FormalValue.top_le_comp (hk i) _) (hj.2.1.trans (LB.wchart_le _ _ _ i))
  obtain ⟨t, ht, e₁⟩ := hf (FormalValue.basePt g) (fun i => jt (![2, 0, 1, 3] i)) (fun i => k (![2, 0, 1, 3] i))
    (Over.w g.b) (fun i => by rw [hq i]; exact hd _)
  simp only [hq] at ht
  have lf := isLift_famφB u hc z
  have lg : IsLift u (Out.DegPre.gtφ D₀ ℂ g₀.b α₀) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![c + z, c, z, 0] :=
    fun i => (Category.id_comp _).trans (gtφ_eq u hc hb i)
  have cf : ⊤ ≤ (u.ex z).left ⁻¹ᵁ D₀.P.L.wchart (D₀.famφB α₀) (fun i => k (![2, 0, 1, 3] i)) := by
    refine (lf.le_iff _).2 fun i => ?_
    fin_cases i
    exacts [hk 2, add_comm c z ▸ hk 0, hk 1, hk 3]
  have cg := (lg.le_iff k).2 hk
  have e₂ : valR (FormalValue.basePt g ≫ φ) _ (s₀.f fun i => k (![2, 0, 1, 3] i)) = _ :=
    (congrArg (fun q => valR q _ (s₀.f fun i => k (![2, 0, 1, 3] i))) (hφ 2)).trans
      ((HolHom.valR_spMap ρ (u.ex z).left _ cf _).trans (congrArg ρ (valAt'_sec D₀.P.isLB s₀ lf cf)))
  have e₃ : FormalValue.coordVal g α jt = _ := (hg.2 jt k hd).trans (congrArg₂ (· * ·)
    (Finset.prod_congr rfl fun i _ => valR_zpow _ _ (hd i) _ (![t 1, t 2, t 0, t 3] i)
      (by fin_cases i; exacts [ht 1, ht 2, ht 0, ht 3]) _)
    ((valR_pullGen ρ (g₀.s α₀) k cg).trans (congrArg ρ (valAt'_gen D₀.P.isLB (g₀.isGen α₀) lg cg))))
  have e₄ : frameProd u (Out.DegPre.famε j) ![z, z + c, c, 0] (fun i => k (![2, 0, 1, 3] i)) *
      frameProd u Out.DegPre.gtε ![c + z, c, z, 0] k = u.fr (k 2) z ^ j := by
    have n₀ : u.fr (k 0) (c + z) ≠ 0 := u.fr_ne _ _ (hk 0)
    have n₁ : u.fr (k 1) c ≠ 0 := u.fr_ne _ _ (hk 1)
    have n₂ : u.fr (k 2) z ≠ 0 := u.fr_ne _ _ (hk 2)
    have n₃ : u.fr (k 3) 0 ≠ 0 := u.fr_ne _ _ (hk 3)
    simp only [frameProd, Fin.prod_univ_four, Out.DegPre.famε, Out.DegPre.gtε, Matrix.cons_val, zpow_sub₀ n₂,
      zpow_neg, zpow_one, zpow_natCast, add_comm z c]
    field_simp
  have e₅ : (t 0 : S) ^ j * ∏ i, ((![t 1, t 2, t 0, t 3] i ^ (-Out.DegPre.gtε i) : Sˣ) : S) =
      ((∏ i, t i ^ Out.DegPre.famε j i : Sˣ) : S) := by
    rw [← Units.coe_prod, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← prod_factors t j]
    simp only [zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel_right]
  replace e₁ := e₁.trans (congrArg (κ r * ·) e₂)
  refine (congrArg₂ (fun a b => a ^ j * (_ * b)) (ht 0).symm e₃).trans ?_
  rw [← e₄]
  simp only [map_mul] at e₁ ⊢
  rw [← e₅] at e₁
  unfold FormalValue.famVal
  linear_combination (ρ (genVal u D₀.P.isLB (g₀.s α₀) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![c + z, c, z, 0]) *
    ρ (frameProd u Out.DegPre.gtε ![c + z, c, z, 0] k)) * e₁

end Core

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (j : ℕ) (α : Λ.A.X) (s₀ : a.D₀.SecB j (Λ.ε α)) (f : W.P.D.toPre.SecB j (W.e (Λ.ε α))) (r : ℂ⟦X⟧), (∀ (Z : Type) [CommRing Z] [IsLocalRing Z] (p : Sp Z ⟶ W.P.D.toPre.P.A.left) (κ : ℂ⟦X⟧ →+* Z) (jf : Fin 4 → W.P.D.toPre.P.L.ι) (j₀ : Fin 4 → a.D₀.P.L.ι), p ≫ W.P.D.toPre.P.A.hom = spMap κ → (∀ i, ⊤ ≤ (p ≫ W.P.D.toPre.famφB (W.e (Λ.ε α)) i) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀ i, jf i)) → ∃ u : Fin 4 → Zˣ, (∀ i, (u i : Z) = valR (p ≫ W.P.D.toPre.famφB (W.e (Λ.ε α)) i) _ (W.w.s (fun _ => j₀ i, jf i)).val) ∧ (∏ i, u i ^ Out.DegPre.famε j i : Zˣ) * valR p (LB.wchart W.P.D.toPre.P.L (W.P.D.toPre.famφB (W.e (Λ.ε α))) jf) (f.f jf) = κ r * valR (p ≫ W.φ) (LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) j₀) (s₀.f j₀)) → ∀ v jM j₀ jf jt, FormalValue.CohCharts (Ξ.g v) (W.e (Λ.ε α)) jM jf jt → ⊤ ≤ (Ξ.g v).b.left ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) → valR (A := ℂ⟦X⟧) (Ξ.g v).b.left _ (W.w.s (fun _ => j₀, jM)).val ^ j * (FormalValue.famVal (Ξ.g v) f jf * FormalValue.coordVal (Ξ.g v) (W.e (Λ.ε α)) jt) = r * PowerSeries.C (Λ.fn j α s₀ v.2 * eTwoPi (v.1 α) * Λ.u.fr j₀ v.2 ^ j) := by
  intro _ _ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ j α s₀ f r hf v jM j₀ jf jt hj hM
  have h := core Λ.u (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) (PowerSeries.C (R := ℂ)) W.w (Ξ.g v) (Λ.ex0 v) (Λ.ct α) (Λ.ex0_b v)
    (Ξ.g_rel v (Λ.ε α)) s₀ f r (fun p => hf _ p _) jM j₀ jf jt hj hM
  rw [Λ.arcDict_expZero_section v α] at h
  exact h

end GlobalTheory.ConstTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusCoordinateRatioEqTorusCoordOverOriginStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusCoordinateRatio_eq_torusCoord_over_origin : ∀ [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ) (g n : ℕ) (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (sB : ∀ Tt : Over (Sp ℂ), (Tt ⟶ D.P.A) → Out.GtPt D Tt), (∀ Tt b, (sB Tt b).b = b ^ n) → (∀ Tt b b', Out.GtPt.IsAdd (sB Tt b) (sB Tt b') (sB Tt (b * b'))) → (∀ (Tt Tt' : Over (Sp ℂ)) (h : Tt' ⟶ Tt) b, Out.GtPt.IsPull h.left (sB Tt b) (sB Tt' (h ≫ b))) → (∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) → (∀ p : Out.GtPtF D ℂ, p.IsZero → IsTorusPt p (fun _ => 1)) ∧ ∀ u : D.X → (Fin g → ℂ) → ℂ, IsRatio ex n (sB D.P.A (𝟙 _)) u → ∀ (z : Fin g → ℂ) (xv : D.X → ℂ), (ex z).b = Out.DegPre.zeroF D ℂ → IsTorusPt (ex ((n : ℂ) • z)) xv → ∀ x, u x z = xv x := by
  first | exact @GlobalTheory.AbelianLetters.TorusRatio.ratio_eq_torus_coord | exact GlobalTheory.AbelianLetters.TorusRatio.ratio_eq_torus_coord | (intros; apply GlobalTheory.AbelianLetters.TorusRatio.ratio_eq_torus_coord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TwoRigidifiedThetaFramesOnFibre
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.TwoFrames

theorem valR_eq_valAt' {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : valR x U f = valAt' x U f := by
  unfold valR valAt' valAt
  congr

theorem map_map {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) (f : Γ(X, U)) :
    (X.presheaf.map (homOfLE k).op).hom ((X.presheaf.map (homOfLE h).op).hom f) =
      (X.presheaf.map (homOfLE (k.trans h)).op).hom f := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem exists_sec_of_pow_one {Z Z' : Scheme.{0}} {L : LB Z} {p : Z' ⟶ Z} (σ : SecP L p 1) :
    ∃ s : (L.pull p).Sec, ∀ (j : L.ι) (x : Sp ℂ ⟶ Z'), ⊤ ≤ (x ≫ p) ⁻¹ᵁ L.U j →
      valAt' x ((L.pull p).U (fun _ => j)) (s.f (fun _ => j)) = ArcPts.sval σ x j := by
  have le : ∀ J : PUnit → L.ι, (L.pull p).U J ≤ LB.wchart L (fun _ : Fin 1 => p) (fun _ => J PUnit.unit) :=
    fun J y hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy PUnit.unit
  refine ⟨⟨fun J => (Z'.presheaf.map (homOfLE (le J)).op).hom (σ.f (fun _ => J PUnit.unit)), fun J J' => ?_⟩,
    fun j x hx => ?_⟩
  · have h := congrArg (Z'.presheaf.map (homOfLE (inf_le_inf (le J) (le J'))).op).hom
      (σ.compat (fun _ => J PUnit.unit) (fun _ => J' PUnit.unit))
    refine ((map_map _ _ _).trans (map_map _ _ _).symm).trans (h.trans ((map_mul _ _ _).trans ?_))
    refine congrArg₂ (· * ·) ?_ ((map_map _ _ _).trans (map_map _ _ _).symm)
    simp only [LB.LinComb, Finset.univ_unique, Finset.prod_singleton, Nat.cast_one, zpow_one]
    refine (map_map _ _ _).trans ?_
    symm
    refine Eq.trans (congrArg Units.val (?_ : (L.pull p).g J J' = res (le_inf (inf_le_left.trans
      (LB.wchart_le L _ J PUnit.unit)) (inf_le_right.trans (LB.wchart_le L _ J' PUnit.unit)))
      (pullU p _ (L.g (J PUnit.unit) (J' PUnit.unit))))) rfl
    show ∏ k : PUnit, _ = _
    have hp : ∀ {G : Type} [CommGroup G] (x : G), ∏ _k : PUnit.{1}, x ^ (1 : ℤ) = x := fun x => by simp
    exact hp _
  · refine Eq.trans ?_ (valR_eq_valAt' x _ _).symm
    exact GlobalTheory.valAt'_map x _ _ (fun q hq => mem_pull.2 ((top_le_preimage_comp _ _ _).1 hx hq))

theorem two_frames : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (A : AnArc (𝓞 E)) lin cst (w : ℂ) (y₀ : Sp ℂ ⟶ Xo.X) (π : A.V → (Over.mk y₀ ⟶ Xo.univ.t.G)) fr (g : ℕ) (h : A.V ≃L[ℂ] (Fin g → ℂ)) (e : (Fin g → ℂ) → (Sp ℂ ⟶ Xo.univ.t.G.left)) (ϑ : (Fin g → ℂ) → ℂ) fr', IsFibAt A Xo.univ.t lin cst w y₀ π fr → (∀ v, e (h v) = (π v).left) → IsThetaFrameAt Xo.univ.t.PP y₀ e ϑ fr' → (∃ z, ϑ z ≠ 0) → ∀ th ∈ A.Theta 1 0, (∃ v, A.Sum 1 0 th w v ≠ 0) → ∃ (lam : ℂ) (f : A.V → ℂ), lam ≠ 0 ∧ Differentiable ℂ f ∧ (∀ v, f v ≠ 0) ∧ f 0 = 1 ∧ (∀ v j, ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr' j (h v) = f v * fr j v) ∧ ∀ v, A.Sum 1 0 th w v = lam * ϑ (h v) * f v := by
  intro hL _ E _ _ _ H _ D l Xo A lin cst w y₀ π fr g h e ϑ fr' hF he hT hϑ th hth hS
  obtain ⟨d', n', c', r', s', hs'⟩ := hT
  have ch : ∀ v, ∃ j, ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun v => by
    obtain ⟨j, hj⟩ := exists_chart Xo.univ.t.PP.isLB ((π v).left (default : PrimeSpectrum ℂ))
    exact ⟨j, (top_le_preimage_iff_mem _ _).2 hj⟩
  choose J hJ using ch
  have n : ∀ v j, ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j v ≠ 0 := fun v j hj => ((hF.frm v).1 j hj).ne_zero
  have key : ∀ v j, ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr' j (h v) = fr' (J v) (h v) / fr (J v) v * fr j v := by
    intro v j hj
    have hi := (top_le_preimage_inf _ _ _).2 ⟨hj, hJ v⟩
    have a := (hF.frm v).2 j (J v) hi
    have b := c' j (J v) (h v) (by rw [he]; exact hi)
    rw [he] at b
    rw [valR_eq_valAt'] at a
    beta_reduce at a
    have := n v _ (hJ v)
    rw [b, a]
    field_simp
  obtain ⟨σ, hσ⟩ := hF.sec th hth
  obtain ⟨s, hs⟩ := exists_sec_of_pow_one σ
  obtain ⟨u, hu⟩ := ThetaFamily.exists_values_line_fibre hL.globalSectionsRank Xo.univ y₀
  obtain ⟨a, ha⟩ := hu s
  obtain ⟨a', ha'⟩ := hu s'
  have f1 : ∀ v, fib (π v) ≫ pullback.fst _ _ = (π v).left := fun v => pullback.lift_fst _ _ _
  have f2 : ∀ v, fib (π v) ≫ pullback.snd _ _ = 𝟙 _ := fun v => pullback.lift_snd _ _ _
  have m : ∀ v, ⊤ ≤ (fib (π v) ≫ pullback.fst _ _) ⁻¹ᵁ Xo.univ.t.PP.L.U (J v) := fun v => by
    rw [f1]; exact hJ v
  have m' : ∀ v, ⊤ ≤ fib (π v) ⁻¹ᵁ (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom y₀)).U (fun _ => J v) :=
    fun v q hq => mem_pull.2 ((top_le_preimage_comp _ _ _).1 (m v) hq)
  have e1 : ∀ v, A.Sum 1 0 th w v * fr (J v) v = a * u (fun _ => J v) (fib (π v)) := fun v => by
    rw [← ha _ _ (f2 v) (m' v), hs _ _ (m v), hσ v _ (m v), pow_one]
  have e2 : ∀ v, ϑ (h v) * fr' (J v) (h v) = a' * u (fun _ => J v) (fib (π v)) := fun v => by
    rw [← ha' _ _ (f2 v) (m' v),
      hs' _ (h v) _ ((f1 v).trans (he v).symm) (f2 v) (by rw [he]; exact hJ v)]
  have n'' : ∀ v, fr' (J v) (h v) ≠ 0 := fun v => n' _ _ (by rw [he]; exact hJ v)
  have a0 : a ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := hS
    exact mul_ne_zero hv (n v _ (hJ v)) ((e1 v).trans (zero_mul _))
  have a0' : a' ≠ 0 := by
    rintro rfl
    obtain ⟨z, hz⟩ := hϑ
    obtain ⟨v, rfl⟩ := h.surjective z
    exact mul_ne_zero hz (n'' v) ((e2 v).trans (zero_mul _))
  refine ⟨a / a', fun v => fr' (J v) (h v) / fr (J v) v, div_ne_zero a0 a0', fun v₀ => ?_,
    fun v => div_ne_zero (n'' v) (n v _ (hJ v)), ?_, key, fun v => ?_⟩
  · have op : IsOpen {v | ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U (J v₀)} := by
      simpa using (hF.hol (Xo.univ.t.PP.L.U (J v₀)) 0).1
    have nh := op.mem_nhds (hJ v₀)
    have d1 : DifferentiableOn ℂ (fun v => fr' (J v₀) (h v))
        {v | ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U (J v₀)} :=
      (d' (J v₀)).comp h.differentiable.differentiableOn fun v hv => by
        show ⊤ ≤ e (h v) ⁻¹ᵁ _
        rw [he]; exact hv
    have d2 := ((d1.mul ((hF.fr_hol (J v₀)).inv fun v hv => n v _ hv)).differentiableAt nh)
    refine d2.congr_of_eventuallyEq (Filter.mem_of_superset nh fun v hv => ?_)
    show fr' (J v) (h v) / fr (J v) v = fr' (J v₀) (h v) * (fr (J v₀) v)⁻¹
    rw [key v _ hv, mul_inv_cancel_right₀ (n v _ hv)]
  · show fr' (J 0) (h 0) / fr (J 0) 0 = 1
    have h0 : e 0 = (π 0).left := by rw [← he, map_zero]
    rw [div_eq_one_iff_eq (n 0 _ (hJ 0)), map_zero, r' _ (by rw [h0]; exact hJ 0), hF.rig _ (hJ 0)]
  · have := n v _ (hJ v)
    have b1 := e1 v
    have b2 := e2 v
    field_simp
    linear_combination a' * b1 - a * b2

end GlobalTheory.TwoFrames
end
end

