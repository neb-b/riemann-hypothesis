module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.RegUnifCut
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepsXSt

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpansionNonnegRegular
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm

private lemma coh_lemma {X Y : Scheme} (L : LB X) (φ : Fin 1 ⊕ Fin 1 → (Y ⟶ X))
    (j : Fin 1 → L.ι) : LB.Coh L φ (Sum.elim j j) := by
  intro k₁ k₂ _
  rcases k₁ with a | a <;> rcases k₂ with b | b <;> exact congrArg j (Subsingleton.elim a b)

private lemma res_inj_lemma_2 {X : Scheme} {W V : X.Opens} (h : W ≤ V) {a b : Γ(X, V)}
    {c : Γ(X, W)} (hc : c = 1)
    (hab : c * (X.presheaf.map (homOfLE h).op).hom a = c * (X.presheaf.map (homOfLE h).op).hom b)
    (h' : V ≤ W) : a = b := by
  subst hc
  rw [_root_.one_mul, _root_.one_mul] at hab
  have hWV : W = V := le_antisymm h h'
  subst hWV
  have e : homOfLE h = 𝟙 W := Subsingleton.elim _ _
  rw [e] at hab
  simpa using hab

theorem expansion_nonneg_regular : RegularSectionNonneg := by
  unfold RegularSectionNonneg
  intro V _ _ _ ϖ hϖ D Q hQ vK hvK A G _ _ _ _ _ U k hk σ s hs E hE
  subst hk
  obtain ⟨F, g', hF, -, hFg⟩ := TG.integral_exp (U := U) rfl σ

  have hsK : s = TG.secK U.toUnifPre σ := by
    apply SecOps.sec_ext
    intro j
    have h1 := hs j j (coh_lemma _ _ j)
    have h2 := TG.secK_rel U.toUnifPre σ j j (coh_lemma _ _ j)
    have h3 := h1.symm.trans h2
    refine res_inj_lemma_2 _ (by exact _root_.map_one _) h3 ?_
    refine le_inf le_rfl ?_
    first
      | exact le_rfl
      | (simp only [Category.comp_id]; exact le_rfl)
      | exact fun x hx => hx
      | (intro x hx; simpa [LB.wchart] using hx)
  subst hsK

  have hEF : E = F := ((U.expand 1 le_rfl).1 _).unique hE hF
  rw [hEF]
  refine (n1a V ϖ hϖ D Q hQ (FractionRing V) vK hvK 1 le_rfl {0}
    (fun χ => ⟨0, Finset.mem_singleton_self 0, χ, by simp⟩) F 0).2 ?_
  intro α hα
  rw [Finset.mem_singleton] at hα
  subst hα
  rw [Q_zero hϖ (hQ := hQ)]
  unfold VGe
  refine ⟨1, fun _ => 1, fun _ => g' 0, fun _ => F.s 0, fun _ => hFg 0, fun _ => ?_, fun j => ?_⟩
  · first
      | simp
      | (rw [AddValuation.map_one]; simp)
  · first
      | simp [DegPre.constBF]
      | (simp only [DegPre.constBF, Fin.sum_univ_one, _root_.map_one, _root_.one_mul])

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.RegUnifC
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.RegC

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.UUA
open ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation

variable {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]

variable (D : DegPre R)

section Descent

open IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem exists_hasVal {ϖ : V} (hϖ : Irreducible ϖ) (x : FractionRing V) (hx : x ≠ 0) : ∃ n : ℤ, HasVal ϖ x n := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) x
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨m1, u1, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  obtain ⟨m2, u2, rfl⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hϖ
  refine ⟨(m1 : ℤ) - m2, u1 * u2⁻¹, ?_⟩
  have hp : algebraMap V (FractionRing V) ϖ ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap V (FractionRing V))]
    exact fun h => hϖ.ne_zero (IsFractionRing.injective V (FractionRing V) h)
  have hu2 : algebraMap V (FractionRing V) (u2 : V) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap V (FractionRing V))]
    exact fun h => u2.ne_zero (IsFractionRing.injective V (FractionRing V) h)
  have hinv : algebraMap V (FractionRing V) ((u2⁻¹ : Vˣ) : V) =
      (algebraMap V (FractionRing V) (u2 : V))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  simp only [Units.val_mul, map_mul, map_pow, hinv]
  rw [zpow_sub₀ hp, zpow_natCast, zpow_natCast]
  field_simp

variable {D : DegData V (maximalIdeal V)} (F : Type) [Field F] [Algebra (FractionRing V) F]

end Descent

end ReciprocityTheory.ChartRestriction.G.PullbackSections.RegC
end
end

