module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0539
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0553
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0444
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0544

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalTwoGroupsRules
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.SubstCalc

variable {R : Type} [CommRing R]

theorem constantCoeff_subst_of_zero {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have h1 : f = (f - C (constantCoeff f)) + C (constantCoeff f) := by ring
  conv_lhs => rw [h1]
  rw [subst_add hs, map_add (f := _), constantCoeff_subst_eq_zero hs ha (by simp), subst_C, zero_add]
  simp

theorem hasSubst_elim {d : ℕ} {τ : Type} {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hu, hv]

theorem subst_powerSeriesEvalTwoGroups {d : ℕ} {τ τ' : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    {a : τ → MvPowerSeries τ' R} (ha : ∀ t, constantCoeff (a t) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    subst a (at2 c u v) = at2 c (fun i => subst a (u i)) (fun i => subst a (v i)) := by
  unfold at2
  rw [subst_comp_subst_apply (hasSubst_elim hu hv) (hasSubst_of_constantCoeff_zero ha)]
  congr 1
  funext s
  cases s <;> rfl

theorem powerSeriesEvalTwoGroups_rules_alt : ∀ (R : Type) [CommRing R] (d : ℕ) (τ τ' : Type) [Finite τ] (u v : Fin d → MvPowerSeries τ R), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ f, at2 (inL f) u v = subst u f) ∧ (∀ f, at2 (inR f) u v = subst v f) ∧ (∀ c c', at2 (c + c') u v = at2 c u v + at2 c' u v ∧ at2 (c - c') u v = at2 c u v - at2 c' u v) ∧ (∀ c, constantCoeff (at2 c u v) = constantCoeff c) ∧ (∀ c, at2 (swap c) u v = at2 c v u) ∧ (∀ (e : ℕ) (μ : Fin e → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ f : MvPowerSeries (Fin e) R, at2 (subst μ f) u v = subst (fun i => at2 (μ i) u v) f) ∧ (∀ a : τ → MvPowerSeries τ' R, (∀ t, constantCoeff (a t) = 0) → ∀ c, subst a (at2 c u v) = at2 c (fun i => subst a (u i)) (fun i => subst a (v i))) ∧ ∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, cob2 (addLaw R d) c = 0 → at2 c u v - at2 c (u + u) v + at2 c u (u + v) - at2 c u u = 0 := by
  intro R _ d τ τ' _ u v hu hv
  have hs := hasSubst_elim hu hv
  have hX : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hY : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    unfold at2 inL
    rw [subst_comp_subst_apply hX hs]
    congr 1
    funext i
    rw [subst_X hs]; rfl
  · intro f
    unfold at2 inR
    rw [subst_comp_subst_apply hY hs]
    congr 1
    funext i
    rw [subst_X hs]; rfl
  · intro c c'
    unfold at2
    exact ⟨subst_add hs _ _, subst_sub hs _ _⟩
  · intro c
    unfold at2
    exact constantCoeff_subst_of_zero (fun s => by cases s <;> simp [hu, hv]) c
  · intro c
    have hW : HasSubst (Sum.elim (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (fun i => X (Sum.inl i))) :=
      hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp
    unfold swap at2
    rw [subst_comp_subst_apply hW hs]
    congr 1
    funext s
    cases s <;> simp [subst_X hs]
  · intro e μ hμ f
    unfold at2
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hμ) hs]
  · intro a ha c
    exact subst_powerSeriesEvalTwoGroups hu hv ha c
  · intro c hc
    set w : Fin d ⊕ (Fin d ⊕ Fin d) → MvPowerSeries τ R := Sum.elim u (Sum.elim u v) with hw
    have hw0 : ∀ t, constantCoeff (w t) = 0 := fun t => by
      rcases t with t | t | t <;> simp [hw, hu, hv]
    have hsw : HasSubst w := hasSubst_of_constantCoeff_zero hw0
    have h1 : ∀ i, subst w (x1 (R := R) (d := d) i) = u i := fun i => by
      unfold x1; rw [subst_X hsw]; rfl
    have h2 : ∀ i, subst w (x2 (R := R) (d := d) i) = u i := fun i => by
      unfold x2; rw [subst_X hsw]; rfl
    have h3 : ∀ i, subst w (x3 (R := R) (d := d) i) = v i := fun i => by
      unfold x3; rw [subst_X hsw]; rfl
    have hx0 : ∀ i, constantCoeff (x1 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
    have hx20 : ∀ i, constantCoeff (x2 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
    have hx30 : ∀ i, constantCoeff (x3 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
    have hop : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
        (∀ i, constantCoeff (a i) = 0) → (∀ i, constantCoeff (b i) = 0) →
        op (addLaw R d) a b = a + b := by
      intro a b ha hb
      funext i
      unfold op addLaw at2
      have := hasSubst_elim ha hb
      rw [subst_add this, subst_X this, subst_X this]
      rfl
    have hop0 : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
        (∀ i, constantCoeff (a i) = 0) → (∀ i, constantCoeff (b i) = 0) →
        ∀ i, constantCoeff ((a + b) i) = 0 := by
      intro a b ha hb i; simp [ha, hb]
    have key := congrArg (subst w) hc
    unfold cob2 at key
    rw [hop _ _ hx0 hx20, hop _ _ hx20 hx30] at key
    rw [subst_sub hsw, subst_add hsw, subst_sub hsw,
      subst_powerSeriesEvalTwoGroups hx20 hx30 hw0, subst_powerSeriesEvalTwoGroups (hop0 _ _ hx0 hx20) hx30 hw0,
      subst_powerSeriesEvalTwoGroups hx0 (hop0 _ _ hx20 hx30) hw0, subst_powerSeriesEvalTwoGroups hx0 hx20 hw0] at key
    have e : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
        (fun i => subst w ((a + b) i)) = (fun i => subst w (a i)) + (fun i => subst w (b i)) := by
      intro a b; funext i; simp only [Pi.add_apply]; exact subst_add hsw _ _
    rw [e, e] at key
    simp only [h1, h2, h3] at key
    have e0 : subst w (0 : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 := by
      simpa using (subst_sub hsw (0 : MvPowerSeries _ R) 0)
    rw [e0] at key
    convert key using 2

end GlobalTheory.Katz.SubstCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionValuationBoundRingClosure
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)

namespace GlobalTheory.QFam.QSz

section

variable {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} {N : ℕ}

theorem qAll_const {r : ℝ} {c : ℂ} (hc : Sz l lam r c) : QAll (Sz l lam r) N fun _ => c := by
  refine ⟨_, (_root_.GlobalTheory.QFam.hasQ_linear N).2.2.2.1 c, fun n => ?_⟩
  by_cases h : n = 0
  · simpa only [h, if_true] using hc
  · simpa only [h, if_false] using (_root_.GlobalTheory.QFam.SzSum.sz_ring l lam).1 r

theorem qAll_mono {r s : ℝ} {f : ℍ → ℂ} (h : r ≤ s) (hf : QAll (Sz l lam r) N f) : QAll (Sz l lam s) N f := by
  obtain ⟨a, ha, hs⟩ := hf
  exact ⟨a, ha, fun n => (_root_.GlobalTheory.QFam.SzSum.sz_ring l lam).2.2.2.1 r s _ h (hs n)⟩

theorem qAll_add {r : ℝ} {f g : ℍ → ℂ} (hf : QAll (Sz l lam r) N f) (hg : QAll (Sz l lam r) N g) :
    QAll (Sz l lam r) N fun τ => f τ + g τ := by
  obtain ⟨a, ha, hs⟩ := hf
  obtain ⟨b, hb, ht⟩ := hg
  exact ⟨_, (_root_.GlobalTheory.QFam.hasQ_linear N).1 f g a b ha hb, fun n => ((_root_.GlobalTheory.QFam.SzSum.sz_ring l lam).2.1 r _ _ (hs n) (ht n)).1⟩

theorem qAll_sub {r : ℝ} {f g : ℍ → ℂ} (hf : QAll (Sz l lam r) N f) (hg : QAll (Sz l lam r) N g) :
    QAll (Sz l lam r) N fun τ => f τ - g τ := by
  obtain ⟨a, ha, hs⟩ := hf
  obtain ⟨b, hb, ht⟩ := hg
  exact ⟨_, (_root_.GlobalTheory.QFam.hasQ_linear N).2.1 f g a b ha hb, fun n => ((_root_.GlobalTheory.QFam.SzSum.sz_ring l lam).2.1 r _ _ (hs n) (ht n)).2⟩

theorem qAll_mul (hN : 0 < N) {r s : ℝ} {f g : ℍ → ℂ} (hf : QAll (Sz l lam r) N f) (hg : QAll (Sz l lam s) N g) :
    QAll (Sz l lam (r + s)) N fun τ => f τ * g τ := by
  obtain ⟨a, ha, hs⟩ := hf
  obtain ⟨b, hb, ht⟩ := hg
  refine ⟨_, _root_.GlobalTheory.QFam.hasQ_mul_conv N f g a b hN ha hb, fun n => ?_⟩
  exact (_root_.GlobalTheory.QFam.SzSum.sz_ring l lam).2.2.2.2.2 _ _ _ (fun p : ℕ × ℕ => a p.1 * b p.2)
    fun p _ => (_root_.GlobalTheory.QFam.SzSum.sz_ring l lam).2.2.1 r s _ _ (hs _) (ht _)

theorem qAll_one : QAll (Sz l lam 0) N fun _ => 1 :=
  qAll_const (by simpa using (_root_.GlobalTheory.QFam.SzSum.sz_ring l lam).2.2.2.2.1 1)

theorem qAll_pow (hN : 0 < N) {r : ℝ} {f : ℍ → ℂ} (k : ℕ) (hf : QAll (Sz l lam r) N f) :
    QAll (Sz l lam (k * r)) N fun τ => f τ ^ k := by
  induction k with
  | zero => simpa using (qAll_one : QAll (Sz l lam 0) N fun _ => 1)
  | succ k ih =>
    have h := qAll_mul hN ih hf
    have e : ((k + 1 : ℕ) : ℝ) * r = k * r + r := by push_cast; ring
    rw [e]
    simpa only [pow_succ] using h

theorem qAll_sum {κ : Type} (t : Finset κ) {r : ℝ} {f : κ → ℍ → ℂ} (hf : ∀ k ∈ t, QAll (Sz l lam r) N (f k)) :
    QAll (Sz l lam r) N fun τ => ∑ k ∈ t, f k τ := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (qAll_const ((_root_.GlobalTheory.QFam.SzSum.sz_ring l lam).1 r) : QAll (Sz l lam r) N fun _ => 0)
  | insert k t hk ih =>
    simp only [Finset.sum_insert hk]
    exact qAll_add (hf k (Finset.mem_insert_self k t)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem qAll_prod (hN : 0 < N) {κ : Type} (t : Finset κ) {r : κ → ℝ} {f : κ → ℍ → ℂ}
    (hf : ∀ k ∈ t, QAll (Sz l lam (r k)) N (f k)) :
    QAll (Sz l lam (∑ k ∈ t, r k)) N fun τ => ∏ k ∈ t, f k τ := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (qAll_one : QAll (Sz l lam 0) N fun _ => 1)
  | insert k t hk ih =>
    simp only [Finset.sum_insert hk, Finset.prod_insert hk]
    exact qAll_mul hN (hf k (Finset.mem_insert_self k t)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

end

theorem qAll_sz_ring : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ (N : ℕ), 0 < N → (∀ (r : ℝ) (c : ℂ), Sz l lam r c → QAll (Sz l lam r) N fun _ => c) ∧ (∀ (r s : ℝ) f, r ≤ s → QAll (Sz l lam r) N f → QAll (Sz l lam s) N f) ∧ (∀ (r : ℝ) f g, QAll (Sz l lam r) N f → QAll (Sz l lam r) N g → (QAll (Sz l lam r) N fun τ => f τ + g τ) ∧ QAll (Sz l lam r) N fun τ => f τ - g τ) ∧ (∀ (r s : ℝ) f g, QAll (Sz l lam r) N f → QAll (Sz l lam s) N g → QAll (Sz l lam (r + s)) N fun τ => f τ * g τ) ∧ (∀ (r : ℝ) f (k : ℕ), QAll (Sz l lam r) N f → QAll (Sz l lam (k * r)) N fun τ => f τ ^ k) ∧ (∀ (κ : Type) (t : Finset κ) (r : ℝ) (f : κ → ℍ → ℂ), (∀ k ∈ t, QAll (Sz l lam r) N (f k)) → QAll (Sz l lam r) N fun τ => ∑ k ∈ t, f k τ) ∧ (∀ (κ : Type) (t : Finset κ) (r : κ → ℝ) (f : κ → ℍ → ℂ), (∀ k ∈ t, QAll (Sz l lam (r k)) N (f k)) → QAll (Sz l lam (∑ k ∈ t, r k)) N fun τ => ∏ k ∈ t, f k τ) :=
  fun _ _ _ _ hN => ⟨fun _ _ h => qAll_const h, fun _ _ _ h hf => qAll_mono h hf,
    fun _ _ _ hf hg => ⟨qAll_add hf hg, qAll_sub hf hg⟩, fun _ _ _ _ hf hg => qAll_mul hN hf hg,
    fun _ _ k hf => qAll_pow hN k hf, fun _ t _ _ hf => qAll_sum t hf, fun _ t _ _ hf => qAll_prod hN t hf⟩

end GlobalTheory.QFam.QSz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLevelSectionsSpreadToSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem siegel_levels_spread_to_subring : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (ψ : d₀.A.left ⟶ u.A.left) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE) (j : e.A.left ⟶ d₀.A.left), IsPullback ψ d₀.A.hom u.A.hom h₀ → (∀ a, (e.lev a).left ≫ j = spMap R₀.subtype ≫ (d₀.lev a).left) → (∀ a, (e.lev a).left ≫ (j ≫ ψ) = (spMap R₀.subtype ≫ h₀) ≫ (u.lev a).left) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (s₁ : Sp R₁ ⟶ Sp B) (d₁ : SiegPre g n ζ s₁) (φ₁ : d₁.A.left ⟶ d₀.A.left), IsGrpPullback d₁.A u.A (spMap (Subring.inclusion hle) ≫ h₀) (φ₁ ≫ ψ) → (∀ a, (d₁.lev a).left ≫ φ₁ = spMap (Subring.inclusion hle) ≫ (d₀.lev a).left) → ∀ a, (d₁.lev a).left ≫ (φ₁ ≫ ψ) = (spMap (Subring.inclusion hle) ≫ h₀) ≫ (u.lev a).left := by
  intro g n B _ ζ S _ R₀ s₀ d₀ Y sY u h₀ ψ sE e j hψ hj hjψ
  classical
  haveI : Smooth u.A.hom := u.ab.smooth
  have hsec₀ : ∀ a, (d₀.lev a).left ≫ d₀.A.hom = 𝟙 (Sp R₀) := fun a => Over.w (d₀.lev a)
  have hsecu : ∀ a, (u.lev a).left ≫ u.A.hom = 𝟙 Y := fun a => Over.w (u.lev a)
  have key : ∀ i : Fin g ⊕ Fin g, ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ →
      spMap (Subring.inclusion hle) ≫ (d₀.lev (Pi.single i 1)).left ≫ ψ =
        spMap (Subring.inclusion hle) ≫ h₀ ≫ (u.lev (Pi.single i 1)).left := by
    intro i
    let x : Sp R₀ ⟶ pullback u.A.hom h₀ := pullback.lift ((d₀.lev (Pi.single i 1)).left ≫ ψ) (𝟙 _) (by
      rw [Category.assoc, hψ.w, ← Category.assoc, hsec₀, Category.id_comp])
    let y : Sp R₀ ⟶ pullback u.A.hom h₀ := pullback.lift (h₀ ≫ (u.lev (Pi.single i 1)).left) (𝟙 _) (by
      rw [Category.assoc, hsecu, Category.comp_id, Category.id_comp])
    have hx : x ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have hy : y ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have hxy : spMap R₀.subtype ≫ x = spMap R₀.subtype ≫ y := by
      apply pullback.hom_ext
      · simp only [x, y, Category.assoc, pullback.lift_fst]
        rw [← Category.assoc, ← hj, Category.assoc, hjψ, Category.assoc]
      · simp only [x, y, Category.assoc, pullback.lift_snd]
    obtain ⟨F, hF⟩ := morphisms_eq_spread_to_subring S R₀ (Sp S) (Sp R₀) (pullback u.A.hom h₀) (𝟙 _) (𝟙 _)
      (pullback.snd _ _) (spMap R₀.subtype) x y (IsPullback.id_vert _) hx hy hxy
    refine ⟨F, fun R₁ hle hF₁ => ?_⟩
    have := congrArg (· ≫ pullback.fst u.A.hom h₀)
      (hF R₁ hle hF₁ (Sp R₁) (𝟙 _) (spMap (Subring.inclusion hle)) (IsPullback.id_vert _))
    simpa only [x, y, Category.assoc, pullback.lift_fst] using this
  choose F hF using key
  refine ⟨Finset.univ.biUnion F, fun R₁ hle hsub s₁ d₁ φ₁ hgp hlev₁ a => ?_⟩
  have hbasis : ∀ i : Fin g ⊕ Fin g, (d₁.lev (Pi.single i 1)).left ≫ (φ₁ ≫ ψ) =
      (spMap (Subring.inclusion hle) ≫ h₀) ≫ (u.lev (Pi.single i 1)).left := by
    intro i
    have hFi : (F i : Set S) ⊆ R₁ := fun x hx => hsub (by
      simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion]
      exact ⟨i, hx⟩)
    rw [← Category.assoc, hlev₁, Category.assoc, hF i R₁ hle hFi, Category.assoc]
  let f : Sp R₁ ⟶ Y := spMap (Subring.inclusion hle) ≫ h₀
  let M : Over Y := Over.mk ((𝟙_ (Over (Sp R₁))).hom ≫ f)
  have hunit : (toUnit M).left = f := by
    have := Over.w (toUnit M)
    exact (Category.comp_id _).symm.trans (this.trans (Category.id_comp _))
  have w : ∀ a, ((d₁.lev a).left ≫ (φ₁ ≫ ψ)) ≫ u.A.hom = M.hom := by
    intro a
    rw [Category.assoc, hgp.1.w, ← Category.assoc, Over.w (d₁.lev a)]
    rfl
  let Ψ₁ : (Fin g ⊕ Fin g → ℤ) →+ Additive (M ⟶ u.A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (toUnit M ≫ u.lev a)) (by
      intro a b
      rw [u.lev_add, comp_mul]
      rfl)
  let Ψ₂ : (Fin g ⊕ Fin g → ℤ) →+ Additive (M ⟶ u.A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (Over.homMk ((d₁.lev a).left ≫ (φ₁ ≫ ψ)) (w a) : M ⟶ u.A)) (by
      intro a b
      show Additive.ofMul _ = Additive.ofMul (_ * _)
      congr 1
      apply Over.OverMorphism.ext
      rw [hgp.2 (𝟙_ _) (d₁.lev a) (d₁.lev b) _ _ rfl rfl, ← d₁.lev_add]
      rfl)
  have hΨ : Ψ₁ = Ψ₂ := by
    refine AddMonoidHom.functions_ext' _ _ _ (fun i => AddMonoidHom.ext_int ?_)
    show Additive.ofMul (toUnit M ≫ u.lev (Pi.single i 1)) =
      Additive.ofMul (Over.homMk ((d₁.lev (Pi.single i 1)).left ≫ (φ₁ ≫ ψ)) (w (Pi.single i 1)) : M ⟶ u.A)
    refine congrArg Additive.ofMul (Over.OverMorphism.ext ?_)
    rw [Over.comp_left, hunit]
    exact (hbasis i).symm
  have := congrArg (fun φ => (Additive.toMul (φ a)).left) hΨ
  simp only [Ψ₁, Ψ₂, AddMonoidHom.mk'_apply, toMul_ofMul, Over.comp_left, Over.homMk_left] at this
  rw [← this, hunit]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheafStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf : GlobalTheory.EtC.B2 := by
  first | (exact @GlobalTheory.EtC.b2) | (exact GlobalTheory.EtC.b2) | (intros; apply GlobalTheory.EtC.b2  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonSecOfSubsingleton
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex
open GlobalTheory.EtC

namespace GlobalTheory.EtC

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
private lemma isEmpty_of_isUnit_zero (U : Scheme) (h : IsUnit (0 : Γ(U, ⊤))) : IsEmpty U := by
  constructor
  intro x
  have h01 : (0 : Γ(U, ⊤)) = 1 := isUnit_zero_iff.1 h
  have := congrArg (U.presheaf.germ ⊤ x trivial).hom h01
  rw [map_zero, map_one] at this
  exact zero_ne_one this

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
private lemma isEmpty_of_prim_zero (U : Scheme)
    (ζ : _root_.GlobalTheory.EtC.Prim 0 Γ(U, ⊤)) : IsEmpty U :=
  isEmpty_of_isUnit_zero U (by simpa using ζ.2.1)

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
private lemma sec_eq_of_isEmpty' {R : Type} [CommRing R] (F : _root_.GlobalTheory.EtC.Shv R) (U : Scheme)
    [IsEmpty U] (a b : _root_.GlobalTheory.EtC.Sec F U) : a = b :=
  (_root_.GlobalTheory.EtC.sec_ext_glue R F U).1 a b
    ⟨⊥, Scheme.bot_mem_grothendieckTopology U, fun _ _ h => h.elim⟩

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.twPair_spec (q : ℕ) (i j : ℤ) :
    _root_.GlobalTheory.EtC.IsTwPair (_root_.GlobalTheory.EtC.twPair q i j) := by
  by_cases hq : q = 0
  · subst hq
    unfold _root_.GlobalTheory.EtC.IsTwPair
    intro U ζ
    haveI := isEmpty_of_prim_zero U ζ
    exact sec_eq_of_isEmpty' _ _ _ _
  · haveI : NeZero q := ⟨hq⟩
    exact (_root_.GlobalTheory.EtC.TwPairUniq.main q i j).1

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.kumT_spec (q : ℕ) : _root_.GlobalTheory.EtC.IsKum q (_root_.GlobalTheory.EtC.kumT q) := by
  by_cases hq : q = 0
  · subst hq
    unfold _root_.GlobalTheory.EtC.IsKum
    refine ⟨fun V U g v h => ?_, fun U ζ v w _ => ?_⟩
    · haveI := isEmpty_of_isUnit_zero U (by simpa using h)
      haveI : IsEmpty V := ⟨fun x => IsEmpty.false (g.base x)⟩
      exact sec_eq_of_isEmpty' _ _ _ _
    · haveI := isEmpty_of_prim_zero U ζ
      exact sec_eq_of_isEmpty' _ _ _ _
  · haveI : NeZero q := ⟨hq⟩
    exact _root_.GlobalTheory.EtC.KummerSplit.isKum_kumT q

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.restrMap_spec {S R : Type} [CommRing S] [CommRing R] (φ : R →+* S)
    (F : _root_.GlobalTheory.EtC.Shv S) (U : Scheme.{0}) (a : _root_.GlobalTheory.EtC.Sec F U) :
    (_root_.GlobalTheory.EtC.restrMap φ F).app U 0
        (_root_.GlobalTheory.EtC.Sec.map (_root_.GlobalTheory.EtC.resι S F) a) =
      _root_.GlobalTheory.EtC.Sec.map (_root_.GlobalTheory.EtC.resι R ((_root_.GlobalTheory.EtC.restr φ).obj F))
        (show _root_.GlobalTheory.EtC.Sec ((_root_.GlobalTheory.EtC.restr φ).obj F) U from a) :=
  _root_.GlobalTheory.EtC.restrMap_spec' R S φ F U a

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumCupOneFormsZeroImpCoordinatesZero
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem sum_toO_eq_zero_of_sum_cup : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ hc : Closed1 F = ⊤, Function.Surjective (toO F) → ∀ (n : ℕ) (a : Fin n → Hyp1 F) (w : Fin n → Glob1 F), ∑ k, cupHyp F (a k) (clAll F hc (w k)) = 0 → ∀ l : Glob1 F →ₗ[R] R, ∑ k, l (w k) • toO F (a k) = 0 := by
  intro R _ C _ F hF hH hc hsurj n a w hsum l
  obtain ⟨δ, hδnat, hδw⟩ := _root_.GlobalTheory.AbCoh.exists_vectorField_of_functional R C F hF hH l
  choose c hcA using fun k => Hyp1.mk_surjective F (a k)
  have hmem : ∀ v : Glob1 F, v ∈ Closed1 F := fun v => hc ▸ Submodule.mem_top
  have hcl : ∀ v : Glob1 F, clAll F hc v = Hyp1.mk F (formZZ F ⟨v, hmem v⟩) := fun v => rfl
  have hf : ∀ v : Glob1 F, (formZZ F ⟨v, hmem v⟩).1 = (0, v.1) := fun v => rfl
  have h2 : Hyp2.mk F (∑ k, cupZZ F (c k) (formZZ F ⟨w k, hmem (w k)⟩)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← hsum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcl, ← hcA k, cupHyp_mk]
  obtain ⟨e, he⟩ := Hyp2.mk_eq_zero.1 h2
  have hsumv : (∑ k, cupZZ F (c k) (formZZ F ⟨w k, hmem (w k)⟩)).1 =
      ∑ k, cupTot F (c k).1 (0, (w k).1) := by
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coe_cupZZ, hf]
  rw [hsumv] at he
  have hz : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''), d1 F e.1 T T' T'' φ ψ = 0 := by
    intro T T' T'' φ ψ
    have := congrArg (fun x : Tot2 F => x.1 T T' T'' φ ψ) he
    simp only [Prod.fst_sum, Finset.sum_apply, cupTot_apply, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero] at this
    exact this
  have ha : ∀ T T' (φ : T ⟶ T'), e.2 T' - p1 F φ (e.2 T) - D R _ (e.1 T T' φ) =
      ∑ k, (c k).1.1 T T' φ • (w k).1 T' := by
    intro T T' φ
    have := congrArg (fun x : Tot2 F => x.2.1 T T' φ) he
    simp only [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, cupTot_a, Pi.zero_apply, zero_smul,
      sub_zero] at this
    exact this
  have he1 : e.1 ∈ Z1 F := by
    rw [commAlgFunctorCocyclesOne_eq_ker, LinearMap.mem_ker]
    funext T T' T'' φ ψ
    exact hz T T' T'' φ ψ
  obtain ⟨b, hb⟩ := hsurj (H1.mk F ⟨e.1, he1⟩)
  obtain ⟨c', rfl⟩ := Hyp1.mk_surjective F b
  rw [toO_mk, H1.mk_eq_mk] at hb
  obtain ⟨g, hg⟩ := hb
  have hfn : ∀ x : cechDeRhamTotalCocyclesOne F, ((cechDeRhamTotalCocyclesOne.fn F x : Z1 F) : C1 F) = x.1.1 := fun x => rfl
  rw [hfn] at hg
  have hg' : ∀ T T' (φ : T ⟶ T'), e.1 T T' φ = c'.1.1 T T' φ - (g T' - mp F φ (g T)) := by
    intro T T' φ
    have := congrFun (congrFun (congrFun hg T) T') φ
    simp only [amitsur_d0_apply, Pi.sub_apply] at this
    rw [this]; abel
  have hD : ∀ T T' (φ : T ⟶ T'), D R _ (e.1 T T' φ) =
      (c'.1.2 T' - D R _ (g T')) - p1 F φ (c'.1.2 T - D R _ (g T)) := by
    intro T T' φ
    rw [hg', cechDeRhamTotalCocyclesOne.conn c' φ]
    simp only [map_sub, ← p1_D]
    abel
  have hgoal : ∑ k, l (w k) • toO F (a k) = H1.mk F (∑ k, l (w k) • cechDeRhamTotalCocyclesOne.fn F (c k)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, ← hcA k, toO_mk]
  rw [hgoal, H1.mk_eq_zero]
  refine ⟨fun T => δ T (e.2 T - (c'.1.2 T - D R _ (g T))), ?_⟩
  funext T T' φ
  rw [amitsur_d0_apply, ← hδnat, ← map_sub]
  have key : e.2 T' - (c'.1.2 T' - D R _ (g T')) - p1 F φ (e.2 T - (c'.1.2 T - D R _ (g T))) =
      ∑ k, (c k).1.1 T T' φ • (w k).1 T' := by
    rw [← ha, hD]
    simp only [map_sub]
    abel
  set_option synthInstance.maxHeartbeats 100000 in
    rw [key, map_sum]
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, hfn,
    LinearMap.map_smul, hδw, smul_eq_mul, Algebra.smul_def]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]
  rfl

end GlobalTheory.AbCoh
end

