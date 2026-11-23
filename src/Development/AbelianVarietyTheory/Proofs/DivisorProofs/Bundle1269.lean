module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianEndomorphismSpreadSpecialise
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtalePointOfExt
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.AlgClosedDescent

theorem finiteEtale_point_of_ext : ∀ (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K] (X : Scheme.{0}) (p : X ⟶ Sp k₀), IsFinite p → Etale p → ∀ x : Sp K ⟶ X, x ≫ p = spMap (algebraMap k₀ K) → ∃ x₀ : Sp k₀ ⟶ X, x₀ ≫ p = 𝟙 _ ∧ spMap (algebraMap k₀ K) ≫ x₀ = x := _root_.GlobalTheory.FinEtPoints.exists_point_of_finite_etale

theorem exists_spread_specialise : ∀ (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K] (B : Over (Sp k₀)) [GrpObj B], IsAbelianScheme B → ∀ f : (Over.pullback (spMap (algebraMap k₀ K))).obj B ⟶ (Over.pullback (spMap (algebraMap k₀ K))).obj B, IsMonHom f → ∃ (R : Subalgebra k₀ K) (g : R →ₐ[k₀] k₀) (Ψ : (Over.pullback (spMap (algebraMap k₀ R))).obj B ⟶ (Over.pullback (spMap (algebraMap k₀ R))).obj B) (f₀ : B ⟶ B) (σ : B.left ⟶ pullback B.hom (spMap (algebraMap k₀ R))), IsMonHom Ψ ∧ IsMonHom f₀ ∧ GlobalTheory.Spread.bcMap B.hom R.val ≫ Ψ.left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _ ∧ σ ≫ pullback.fst _ _ = 𝟙 _ ∧ σ ≫ pullback.snd _ _ = B.hom ≫ spMap g.toRingHom ∧ f₀.left = σ ≫ Ψ.left ≫ pullback.fst _ _ := _root_.GlobalTheory.Spread.exists_endo_spread_specialise

theorem torsion_section_comp_eq : ∀ (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K] (B : Over (Sp k₀)) [GrpObj B], IsAbelianScheme B → ∀ (R : Subalgebra k₀ K) (g : R →ₐ[k₀] k₀) (Ψ : (Over.pullback (spMap (algebraMap k₀ R))).obj B ⟶ (Over.pullback (spMap (algebraMap k₀ R))).obj B) (f₀ : B ⟶ B) (σ : B.left ⟶ pullback B.hom (spMap (algebraMap k₀ R))), IsMonHom Ψ → IsMonHom f₀ → σ ≫ pullback.fst _ _ = 𝟙 _ → σ ≫ pullback.snd _ _ = B.hom ≫ spMap g.toRingHom → f₀.left = σ ≫ Ψ.left ≫ pullback.fst _ _ → ∀ (N : ℕ), (N : k₀) ≠ 0 → ∀ y₀ : 𝟙_ (Over (Sp k₀)) ⟶ B, y₀ ^ N = 1 → ∀ c : Sp R ⟶ pullback B.hom (spMap (algebraMap k₀ R)), c ≫ pullback.fst _ _ = spMap (algebraMap k₀ R) ≫ y₀.left → c ≫ pullback.snd _ _ = 𝟙 _ → c ≫ Ψ.left ≫ pullback.fst _ _ = spMap (algebraMap k₀ R) ≫ y₀.left ≫ f₀.left := _root_.GlobalTheory.TorsCmp.torsion_section_eq

variable {k₀ K : Type} [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K]

theorem isUnit_natCast_gamma {k : Type} [Field k] {N : ℕ} (hN : (N : k) ≠ 0) :
    IsUnit (N : Γ(Sp k, ⊤)) := by
  have h : IsUnit (N : k) := hN.isUnit
  simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

theorem torsion_descent (B : Over (Sp k₀)) [GrpObj B] (hB : IsAbelianScheme B) (N : ℕ)
    (hN : (N : k₀) ≠ 0) {t : Sp K ⟶ Sp k₀} (ht : t = spMap (algebraMap k₀ K))
    (u : Over.mk t ⟶ B) (hu : u ^ N = 1) :
    ∃ y₀ : 𝟙_ (Over (Sp k₀)) ⟶ B, y₀ ^ N = 1 ∧ u.left = t ≫ y₀.left := by
  subst ht
  haveI : IsAbelianScheme B := hB
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion B (isUnit_natCast_gamma hN)
  obtain ⟨x, hx, -⟩ := LatticeTorsion.existsUnique_torsion B N u hu
  obtain ⟨x₀, hx₀, hjx⟩ := finiteEtale_point_of_ext k₀ K _ (torsion B N).hom hfin het x.left (Over.w x)
  let y₀' : 𝟙_ (Over (Sp k₀)) ⟶ torsion B N := Over.homMk x₀ hx₀
  refine ⟨y₀' ≫ torsion.ι B N, ?_, ?_⟩
  · rw [← MonObj.comp_pow, LatticeTorsion.torsionι_pow_eq_one, MonObj.comp_one]
  · rw [← hx, Over.comp_left, ← hjx, Over.comp_left, Category.assoc]
    rfl

theorem hom_eq_of_lTorsion {Ω : Type} [Field Ω] [IsAlgClosed Ω] {A : Over (Sp Ω)} [GrpObj A]
    (hA : IsAbelianScheme A) (F₁ F₂ : A ⟶ A) [IsMonHom F₁] [IsMonHom F₂] {l : ℕ} (hl : l.Prime)
    (hlk : (l : Ω) ≠ 0)
    (h : ∀ (y : 𝟙_ (Over (Sp Ω)) ⟶ A) (a : ℕ), y ^ (l ^ a) = 1 → y ≫ F₁ = y ≫ F₂) : F₁ = F₂ := by
  have := hA.comm
  have hS := isSemiAbelian_of_isAbelianScheme A hA
  have hm : IsMonHom (F₁ * F₂⁻¹) :=
    { one_hom := by
        rw [MonObj.comp_mul, GrpObj.comp_inv, IsMonHom.one_hom, IsMonHom.one_hom, mul_inv_cancel,
          one_eq_one]
      mul_hom := by
        have e (z : A ⊗ A ⟶ A) : z ≫ (F₁ * F₂⁻¹) = z ≫ F₁ * (z ≫ F₂)⁻¹ := by
          rw [MonObj.comp_mul, GrpObj.comp_inv]
        rw [mul_eq_mul, e, MonObj.mul_comp, MonObj.mul_comp, MonObj.comp_mul,
          tensorHom_fst, tensorHom_snd, e, e, mul_inv, _root_.mul_mul_mul_comm] }
  have h1 := GlobalTheory.TorsionDense.eq_one_of_torsion_comp_eq_one Ω A A hS hS l hl hlk (F₁ * F₂⁻¹) hm
    (fun _ _ y a hy ↦ by
      rw [MonObj.comp_mul, GrpObj.comp_inv]
      exact mul_inv_eq_one.mpr (h y a hy))
  exact mul_inv_eq_one.mp h1

theorem exists_prime_ne_zero (k : Type) [Field k] : ∃ l : ℕ, l.Prime ∧ (l : k) ≠ 0 := by
  obtain ⟨p, hp⟩ := CharP.exists k
  by_cases h2 : p = 2
  · subst h2
    refine ⟨3, Nat.prime_three, fun h3 ↦ ?_⟩
    have := (CharP.cast_eq_zero_iff k 2 3).mp (by exact_mod_cast h3)
    omega
  · refine ⟨2, Nat.prime_two, fun h3 ↦ ?_⟩
    have h4 := (CharP.cast_eq_zero_iff k p 2).mp (by exact_mod_cast h3)
    rcases (Nat.dvd_prime Nat.prime_two).mp h4 with h5 | h5
    · exact CharP.char_ne_one k p h5
    · exact h2 h5

theorem endo_descent (B : Over (Sp k₀)) [GrpObj B] (hB : IsAbelianScheme B)
    (f : (Over.pullback (spMap (algebraMap k₀ K))).obj B ⟶
      (Over.pullback (spMap (algebraMap k₀ K))).obj B) (hf : IsMonHom f) :
    ∃! f₀ : B ⟶ B, IsMonHom f₀ ∧ (Over.pullback (spMap (algebraMap k₀ K))).map f₀ = f := by
  obtain ⟨R, g, Ψ, f₀, σ, hΨ, hf₀, hbc, hσ₁, hσ₂, hf₀σ⟩ := exists_spread_specialise k₀ K B hB f hf
  have key : (Over.pullback (spMap (algebraMap k₀ K))).map f₀ = f := by
    let Ω := AlgebraicClosure K
    let qΩ : Sp Ω ⟶ Sp K := spMap (algebraMap K Ω)
    letI : Algebra k₀ Ω := ((algebraMap K Ω).comp (algebraMap k₀ K)).toAlgebra
    have hιj : qΩ ≫ spMap (algebraMap k₀ K) = spMap (algebraMap k₀ Ω) := by
      simp only [qΩ, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      try rfl
    haveI := hf₀
    haveI := hΨ
    apply ActDescent.pullback_map_injective qΩ
    have hBK := isAbelianScheme_pullback_obj (spMap (algebraMap k₀ K)) B hB
    have hA := isAbelianScheme_pullback_obj qΩ _ hBK
    obtain ⟨l, hl, hlk⟩ := exists_prime_ne_zero k₀
    have hlΩ : (l : Ω) ≠ 0 := by
      intro h
      apply hlk
      apply (algebraMap k₀ Ω).injective
      rw [map_natCast, h, map_zero]
    refine hom_eq_of_lTorsion hA _ _ hl hlΩ fun y a hy => ?_
    have h₁ := isGrpPullback_pullback B (spMap (algebraMap k₀ K))
    have h₂ := isGrpPullback_pullback ((Over.pullback (spMap (algebraMap k₀ K))).obj B) qΩ
    have h₁₂ := h₂.comp h₁
    let u := pushHom h₁₂ (𝟙_ _) y
    have hu : u ^ (l ^ a) = 1 := by rw [← map_pow, hy, map_one]
    obtain ⟨y₀, hy₀, huy⟩ := torsion_descent (K := Ω) B hB (l ^ a)
      (by rw [Nat.cast_pow]; exact pow_ne_zero _ hlk)
      (t := (𝟙_ (Over (Sp Ω))).hom ≫ qΩ ≫ spMap (algebraMap k₀ K))
      (by rw [hιj]; exact Category.id_comp _) u hu
    have hu' : y.left ≫ pullback.fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B).hom qΩ ≫ pullback.fst B.hom (spMap (algebraMap k₀ K)) =
        qΩ ≫ spMap (algebraMap k₀ K) ≫ y₀.left := by
      have e : u.left = y.left ≫ pullback.fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B).hom qΩ ≫ pullback.fst B.hom (spMap (algebraMap k₀ K)) := rfl
      rw [← e, huy]
      simp
    have hy0 : y₀.left ≫ B.hom = 𝟙 _ := Over.w y₀
    let w : Sp K ⟶ pullback B.hom (spMap (algebraMap k₀ K)) :=
      pullback.lift (spMap (algebraMap k₀ K) ≫ y₀.left) (𝟙 _)
        (by rw [Category.assoc, hy0]; exact (Category.comp_id _).trans (Category.id_comp _).symm)
    have e2 : y.left ≫ pullback.snd (pullback.snd B.hom (spMap (algebraMap k₀ K))) qΩ = 𝟙 _ := Over.w y
    have hv : y.left ≫ pullback.fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B).hom qΩ = qΩ ≫ w := by
      apply pullback.hom_ext
      · rw [Category.assoc, hu', Category.assoc, pullback.lift_fst]
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, Category.comp_id]
        have e1 : pullback.fst (pullback.snd B.hom (spMap (algebraMap k₀ K))) qΩ ≫
            pullback.snd B.hom (spMap (algebraMap k₀ K)) =
            pullback.snd (pullback.snd B.hom (spMap (algebraMap k₀ K))) qΩ ≫ qΩ := pullback.condition
        erw [e1]
        rw [← Category.assoc, e2, Category.id_comp]
    let c : Sp R ⟶ pullback B.hom (spMap (algebraMap k₀ R)) :=
      pullback.lift (spMap (algebraMap k₀ R) ≫ y₀.left) (𝟙 _)
        (by rw [Category.assoc, hy0]; exact (Category.comp_id _).trans (Category.id_comp _).symm)
    have hwc : w ≫ Spread.bcMap B.hom R.val = spMap R.val.toRingHom ≫ c := by
      apply pullback.hom_ext
      · rw [Category.assoc, Spread.bcMap_fst, pullback.lift_fst, Category.assoc, pullback.lift_fst,
          ← Category.assoc, Spread.spMap_algHom_comp]
      · rw [Category.assoc, Spread.bcMap_snd, pullback.lift_snd_assoc, Category.assoc, pullback.lift_snd,
          Category.id_comp, Category.comp_id]
    have hC := torsion_section_comp_eq k₀ K B hB R g Ψ f₀ σ hΨ hf₀ hσ₁ hσ₂ hf₀σ (l ^ a)
      (by rw [Nat.cast_pow]; exact pow_ne_zero _ hlk) y₀ hy₀ c (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _)
    have m1 : ((Over.pullback qΩ).map ((Over.pullback (spMap (algebraMap k₀ K))).map f₀)).left ≫
        pullback.fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B).hom qΩ = pullback.fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B).hom qΩ ≫ ((Over.pullback (spMap (algebraMap k₀ K))).map f₀).left :=
      ActDescent.pullback_map_left_fst _
    have m3 : ((Over.pullback (spMap (algebraMap k₀ K))).map f₀).left ≫
        pullback.fst B.hom (spMap (algebraMap k₀ K)) = pullback.fst B.hom (spMap (algebraMap k₀ K)) ≫ f₀.left :=
      ActDescent.pullback_map_left_fst _
    have m4 : ((Over.pullback qΩ).map f).left ≫ pullback.fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B).hom qΩ = pullback.fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B).hom qΩ ≫ f.left :=
      ActDescent.pullback_map_left_fst _
    have hL : y.left ≫ ((Over.pullback qΩ).map ((Over.pullback (spMap (algebraMap k₀ K))).map f₀)).left ≫
        pullback.fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B).hom qΩ ≫ pullback.fst B.hom (spMap (algebraMap k₀ K)) =
        qΩ ≫ spMap (algebraMap k₀ K) ≫ y₀.left ≫ f₀.left := by
      rw [reassoc_of% m1, m3, reassoc_of% hu']
    have hR : y.left ≫ ((Over.pullback qΩ).map f).left ≫
        pullback.fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B).hom qΩ ≫ pullback.fst B.hom (spMap (algebraMap k₀ K)) =
        qΩ ≫ spMap (algebraMap k₀ K) ≫ y₀.left ≫ f₀.left := by
      rw [reassoc_of% m4, ← hbc]
      erw [reassoc_of% hv]
      rw [reassoc_of% hwc, hC, ← Spread.spMap_algHom_comp R.val]
      simp only [Category.assoc]
    apply Over.OverMorphism.ext
    apply h₁₂.1.hom_ext
    · simp only [Over.comp_left, Category.assoc]
      exact hL.trans hR.symm
    · simp only [Over.comp_left, Category.assoc, Over.w]

  exact ⟨f₀, ⟨hf₀, key⟩, fun f₁ hf₁ =>
    ActDescent.pullback_map_injective (spMap (algebraMap k₀ K)) B B (hf₁.2.trans key.symm)⟩

theorem point_descent (B : Over (Sp k₀)) [GrpObj B] (hB : IsAbelianScheme B) (n : ℕ)
    (hn : (n : k₀) ≠ 0) (y : 𝟙_ (Over (Sp K)) ⟶ (Over.pullback (spMap (algebraMap k₀ K))).obj B)
    (z₀ : 𝟙_ (Over (Sp k₀)) ⟶ B)
    (hz : (y ^ n).left ≫ pullback.fst B.hom (spMap (algebraMap k₀ K)) = spMap (algebraMap k₀ K) ≫ z₀.left) :
    ∃! y₀ : 𝟙_ (Over (Sp k₀)) ⟶ B, y₀ ^ n = z₀ ∧
      y.left ≫ pullback.fst B.hom (spMap (algebraMap k₀ K)) = spMap (algebraMap k₀ K) ≫ y₀.left := by
  have := hB.comm
  have := hB.smooth
  have := hB.proper
  have hnu := isUnit_natCast_gamma hn
  have := GrpTangent.isFinite_mulN B hnu
  have := GrpTangent.etale_mulN B hnu
  have h₁ := isGrpPullback_pullback B (spMap (algebraMap k₀ K))
  have hw : (y.left ≫ pullback.fst B.hom (spMap (algebraMap k₀ K))) ≫ (mulN B n).left =
      spMap (algebraMap k₀ K) ≫ z₀.left := by
    have e1 : (pushHom h₁ (𝟙_ _) y ≫ mulN B n) = pushHom h₁ (𝟙_ _) (y ^ n) := by
      rw [GrpTangent.comp_mulN, map_pow]
    have e2 := congrArg (fun z => z.left) e1
    simp only [Over.comp_left] at e2
    exact e2.trans hz
  let x : Sp K ⟶ pullback (mulN B n).left z₀.left :=
    pullback.lift (y.left ≫ pullback.fst B.hom (spMap (algebraMap k₀ K))) (spMap (algebraMap k₀ K)) hw
  obtain ⟨x₀, hx₀, hjx⟩ := finiteEtale_point_of_ext k₀ K _ (pullback.snd (mulN B n).left z₀.left) inferInstance inferInstance x
    (pullback.lift_snd _ _ _)
  have hz0 : z₀.left ≫ B.hom = 𝟙 _ := Over.w z₀
  have hfB : pullback.fst (mulN B n).left z₀.left ≫ B.hom = pullback.snd (mulN B n).left z₀.left := by
    rw [← Over.w (mulN B n), ← Category.assoc, pullback.condition, Category.assoc, hz0, Category.comp_id]
  let y₀ : 𝟙_ (Over (Sp k₀)) ⟶ B := Over.homMk (x₀ ≫ pullback.fst _ _)
    (by rw [Category.assoc, hfB, hx₀]; rfl)
  have hepi : Epi (spMap (algebraMap k₀ K)) := Flat.epi_of_flat_of_surjective _
  have hy₀ : y.left ≫ pullback.fst B.hom (spMap (algebraMap k₀ K)) = spMap (algebraMap k₀ K) ≫ y₀.left := by
    change _ = spMap (algebraMap k₀ K) ≫ x₀ ≫ pullback.fst _ _
    rw [← Category.assoc, hjx, pullback.lift_fst]
  refine ⟨y₀, ⟨?_, hy₀⟩, fun y₁ hy₁ => ?_⟩
  · rw [← GrpTangent.comp_mulN]
    apply Over.OverMorphism.ext
    change (x₀ ≫ pullback.fst _ _) ≫ (mulN B n).left = z₀.left
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx₀, Category.id_comp]
  · apply Over.OverMorphism.ext
    rw [← cancel_epi (spMap (algebraMap k₀ K)), ← hy₁.2, hy₀]

end GlobalTheory.AlgClosedDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLogGaussAbsLeFractionalIdealIndex
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.GaussFrac

variable {F : Type} [Field F] [NumberField F]

private theorem gaussAbs_eq_iSup_local {K ι : Type} [Field K] [NumberField K]
    (v : FinitePlace K) (g : MvPolynomial ι K) (s : Finset (ι →₀ ℕ))
    (hs : g.support ⊆ s) (hne : s.Nonempty) :
    gaussAbs v g = ⨆ k : s, v (AddMonoidAlgebra.coeff g (k : ι →₀ ℕ)) := by
  classical
  have : Nonempty s := hne.to_subtype
  have hsup : (g.support.sup fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal) =
      s.sup fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal := by
    refine le_antisymm (Finset.sup_mono hs) (Finset.sup_le fun m hm => ?_)
    by_cases hm' : m ∈ g.support
    · exact Finset.le_sup (f := fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal) hm'
    · rw [MvPolynomial.notMem_support_iff.1 hm', map_zero, Real.toNNReal_zero]
      exact bot_le
  unfold gaussAbs
  rw [hsup]
  obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup s hne fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal
  rw [hkeq, Real.coe_toNNReal _ (apply_nonneg _ _)]
  refine le_antisymm (le_ciSup (f := fun k : s => v (AddMonoidAlgebra.coeff g (k : ι →₀ ℕ)))
    (Set.finite_range _).bddAbove ⟨k, hk⟩) (ciSup_le fun m => ?_)
  have h1 : (v (AddMonoidAlgebra.coeff g (m : ι →₀ ℕ))).toNNReal ≤ (v (AddMonoidAlgebra.coeff g k)).toNNReal := by
    rw [← hkeq]
    exact Finset.le_sup (f := fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal) m.2
  exact (Real.toNNReal_le_toNNReal_iff (apply_nonneg _ _)).1 h1

def scaledIdeal (c : 𝓞 F) (I : Submodule (𝓞 F) F) : Ideal (𝓞 F) :=
  (I.map (LinearMap.lsmul (𝓞 F) F c)).comap (Algebra.linearMap (𝓞 F) F)

theorem absNorm_span_eq (c : 𝓞 F) (hc : c ≠ 0) (I : Submodule (𝓞 F) F) (h1I : 1 ≤ I)
    (hcI : ∀ y ∈ I, c • y ∈ (1 : Submodule (𝓞 F) F)) :
    Ideal.absNorm (Ideal.span {c}) =
      (1 : Submodule (𝓞 F) F).toAddSubgroup.relIndex I.toAddSubgroup * Ideal.absNorm (scaledIdeal c I) := by
  set ι : 𝓞 F →+ F := (Algebra.linearMap (𝓞 F) F).toAddMonoidHom
  set φ : F →+ F := (LinearMap.lsmul (𝓞 F) F c).toAddMonoidHom
  set A := (1 : Submodule (𝓞 F) F).toAddSubgroup
  set B := I.toAddSubgroup
  have hc' : (c : F) ≠ 0 := by exact_mod_cast hc
  have hφ : Function.Injective φ := fun x y h => by
    simp only [φ, LinearMap.toAddMonoidHom_coe, LinearMap.lsmul_apply] at h
    have h' : (c : F) * x = (c : F) * y := by simpa [Algebra.smul_def] using h
    exact mul_left_cancel₀ hc' h'
  have hA : (⊤ : AddSubgroup (𝓞 F)).map ι = A := by
    ext x; simp [ι, A, Submodule.mem_one]
  have hAB : A ≤ B := h1I
  have hBA : B.map φ ≤ A := by
    rintro _ ⟨y, hy, rfl⟩; exact hcI y hy
  have hAA : A.map φ ≤ B.map φ := AddSubgroup.map_mono hAB
  have e1 : (A.map φ).comap ι = (Ideal.span {c}).toAddSubgroup := by
    ext a
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, A, Submodule.mem_one, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, h⟩
      refine ⟨y, ?_⟩
      apply FaithfulSMul.algebraMap_injective (𝓞 F) F
      simp only [φ, ι, LinearMap.toAddMonoidHom_coe, LinearMap.lsmul_apply, Algebra.linearMap_apply, Algebra.smul_def] at h
      rw [map_mul, ← h, mul_comm]
    · rintro ⟨y, rfl⟩
      refine ⟨_, ⟨y, rfl⟩, ?_⟩
      simp only [φ, ι, LinearMap.toAddMonoidHom_coe, LinearMap.lsmul_apply, Algebra.linearMap_apply, Algebra.smul_def]
      rw [map_mul, mul_comm]
  have e2 : (B.map φ).comap ι = (scaledIdeal c I).toAddSubgroup := by
    ext a; rfl
  have k := AddSubgroup.relIndex_mul_relIndex _ _ _ hAA hBA
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hφ] at k
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot, Submodule.cardQuot, ← e1, ← e2,
    ← AddSubgroup.relIndex_top_right, ← AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_comap,
    AddSubgroup.relIndex_comap, hA, ← k]

theorem finsum_log_gaussAbs_le : ∀ (F : Type) [Field F] [NumberField F] (τ : Type) (g : MvPolynomial τ F), g ≠ 0 →
    ∀ (I : Submodule (𝓞 F) F) (δ : F), δ ≠ 0 → 1 ≤ I →
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ y ∈ I, c • y ∈ (1 : Submodule (𝓞 F) F)) → (∀ m, AddMonoidAlgebra.coeff g m / δ ∈ I) →
    ∑ᶠ q : FinitePlace F, Real.log (gaussAbs q g) ≤
      Real.log ((1 : Submodule (𝓞 F) F).toAddSubgroup.relIndex I.toAddSubgroup) +
        ∑ᶠ q : FinitePlace F, Real.log (q δ) := by
  intro F _ _ τ g hg I δ hδ h1I ⟨c, hc, hcI⟩ hcoef
  classical
  have hne : g.support.Nonempty := MvPolynomial.support_nonempty.2 hg
  set n := g.support.card
  set e := g.support.equivFin
  have hz : ∀ i : Fin n, ∃ z : 𝓞 F, algebraMap (𝓞 F) F z = c • (AddMonoidAlgebra.coeff g (e.symm i : τ →₀ ℕ) / δ) :=
    fun i => Submodule.mem_one.1 (hcI _ (hcoef _))
  choose b hb using hz
  have hc' : (c : F) ≠ 0 := by exact_mod_cast hc
  have hb' : ∀ i, (b i : F) = (c : F) * (AddMonoidAlgebra.coeff g (e.symm i : τ →₀ ℕ) / δ) := fun i => by
    simpa [Algebra.smul_def] using hb i
  have hcoeff : ∀ i : Fin n, AddMonoidAlgebra.coeff g (e.symm i : τ →₀ ℕ) = δ * ((b i : F) / c) := by
    intro i
    rw [hb' i]
    field_simp
  obtain ⟨m₀, hm₀⟩ := hne
  set i₀ := e ⟨m₀, hm₀⟩
  have hbi₀ : (b i₀ : F) ≠ 0 := by
    rw [hb' i₀]
    refine mul_ne_zero hc' (div_ne_zero ?_ hδ)
    simpa [i₀] using MvPolynomial.mem_support_iff.1 hm₀
  have hb0 : b ≠ 0 := Function.ne_iff.2 ⟨i₀, fun h => hbi₀ (by rw [h]; rfl)⟩
  have hz0 : (fun i => (b i : F) / c) ≠ 0 := Function.ne_iff.2 ⟨i₀, div_ne_zero hbi₀ hc'⟩
  have hloc : ∀ q : FinitePlace F, Real.log (gaussAbs q g) =
      Real.log (q δ) + Real.log (⨆ i, q ((b i : F) / c)) := by
    intro q
    have hpos : 0 < ⨆ i, q ((b i : F) / c) :=
      lt_of_lt_of_le (FinitePlace.pos_iff.2 (div_ne_zero hbi₀ hc'))
        (le_ciSup (f := fun i => q ((b i : F) / c)) (Set.finite_range _).bddAbove i₀)
    have hqδ : 0 < q δ := FinitePlace.pos_iff.2 hδ
    rw [← Real.log_mul hqδ.ne' hpos.ne', gaussAbs_eq_iSup_local q g g.support subset_rfl ⟨m₀, hm₀⟩,
      ← e.symm.iSup_comp, Real.mul_iSup_of_nonneg hqδ.le]
    congr 1
    refine iSup_congr fun i => ?_
    rw [hcoeff i, map_mul]
  have hs1 : (Function.support fun q : FinitePlace F => Real.log (q δ)).Finite :=
    (FinitePlace.hasFiniteMulSupport hδ).subset (by
      intro v hv h1; apply hv; simp only at h1 ⊢; rw [h1, Real.log_one])
  have hs2 := GlobalTheory.Adelic.HeightExt.finite_support_log_iSup hz0
  rw [finsum_congr hloc, finsum_add_distrib hs1 hs2, GlobalTheory.HSCore.RankOne.finsum_log_iSup_div hb0 hc,
    GlobalTheory.GaussFrac.absNorm_span_eq c hc I h1I hcI]
  have hcN : Ideal.absNorm (Ideal.span {c}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hc
  rw [GlobalTheory.GaussFrac.absNorm_span_eq c hc I h1I hcI] at hcN
  have hR : (1 : Submodule (𝓞 F) F).toAddSubgroup.relIndex I.toAddSubgroup ≠ 0 := left_ne_zero_of_mul hcN
  have hJ : Ideal.absNorm (GlobalTheory.GaussFrac.scaledIdeal c I) ≠ 0 := right_ne_zero_of_mul hcN
  have hle : Ideal.span (Set.range b) ≤ GlobalTheory.GaussFrac.scaledIdeal c I := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    show algebraMap (𝓞 F) F (b i) ∈ I.map (LinearMap.lsmul (𝓞 F) F c)
    exact ⟨_, hcoef _, (hb i).symm⟩
  have hN : Ideal.absNorm (Ideal.span (Set.range b)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_eq_bot]
    intro h
    exact hbi₀ (by rw [h _ ⟨i₀, rfl⟩]; rfl)
  have hdvd := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (Ideal.absNorm_dvd_absNorm_of_le hle)
  push_cast
  rw [Real.log_mul (by exact_mod_cast hR) (by exact_mod_cast hJ)]
  have := Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hJ) (show (Ideal.absNorm (GlobalTheory.GaussFrac.scaledIdeal c I) : ℝ) ≤ Ideal.absNorm (Ideal.span (Set.range b)) by exact_mod_cast hdvd)
  linarith

end GlobalTheory.GaussFrac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderPointIffRingHomAffineOpenSections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.SchRing

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_inj {R S : Type} [CommRing R] [CommRing S] {a b : R →+* S} (h : spMap a = spMap b) : a = b := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

theorem subsingleton_primeSpectrum_trivSqZeroExt (k : Type) [Field k] (M : Type) [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M] [IsCentralScalar k M] :
    Subsingleton (PrimeSpectrum (TrivSqZeroExt k M)) := by
  have key : ∀ (P : PrimeSpectrum (TrivSqZeroExt k M)) (a : TrivSqZeroExt k M), a ∈ P.asIdeal ↔ a.fst = 0 := by
    intro P a
    constructor
    · intro ha
      by_contra h
      have hu : IsUnit a := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr h)
      exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)
    · intro h
      have ha : a = TrivSqZeroExt.inr a.snd := TrivSqZeroExt.ext (by simp [h]) (by simp)
      apply P.isPrime.mem_of_pow_mem 2
      rw [ha, pow_two, TrivSqZeroExt.inr_mul_inr]
      exact P.asIdeal.zero_mem
  exact ⟨fun P Q => PrimeSpectrum.ext (Ideal.ext fun a => (key P a).trans (key Q a).symm)⟩

theorem range_subset_of_fst {X : Scheme.{0}} (k : Type) [Field k] (M : Type) [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M] [IsCentralScalar k M]
    (x : Sp k ⟶ X) (u : Sp (TrivSqZeroExt k M) ⟶ X)
    (h : spMap (TrivSqZeroExt.fstHom k k M).toRingHom ≫ u = x) : Set.range u.base ⊆ Set.range x.base := by
  rintro _ ⟨y, rfl⟩
  haveI := subsingleton_primeSpectrum_trivSqZeroExt k M
  let z : PrimeSpectrum k := ⟨⊥, Ideal.isPrime_bot⟩
  refine ⟨z, ?_⟩
  have hy : (spMap (TrivSqZeroExt.fstHom k k M).toRingHom).base z = y := Subsingleton.elim (α := PrimeSpectrum (TrivSqZeroExt k M)) _ _
  rw [← h, ← hy]
  rfl

theorem exists_ringHom_of_range {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) (D : Type) [CommRing D]
    (g : Sp D ⟶ X) (hg : Set.range g.base ⊆ (V : Set X)) : ∃ r : Γ(X, V) →+* D, g = spMap r ≫ hV.fromSpec := by
  have h' : Set.range g ⊆ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hg
  refine ⟨(Spec.preimage (IsOpenImmersion.lift hV.fromSpec g h')).hom, ?_⟩
  have e1 : spMap (Spec.preimage (IsOpenImmersion.lift hV.fromSpec g h')).hom = IsOpenImmersion.lift hV.fromSpec g h' := by
    simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]
  rw [e1, IsOpenImmersion.lift_fac]

theorem spMap_cancel {R D : Type} [CommRing R] [CommRing D] {Y : Scheme.{0}} (G : Sp R ⟶ Y) [Mono G]
    {a b : R →+* D} (h : spMap a ≫ G = spMap b ≫ G) : a = b :=
  spMap_inj (cancel_mono G |>.mp h)

end GlobalTheory.SchRing

namespace GlobalTheory.SchRing

theorem deformation_on_sections : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (s : X ⟶ Sp B) (U : (Sp B).Opens) (V : X.Opens),
    IsAffineOpen U → IsAffineOpen V → ∀ (e : V ≤ s ⁻¹ᵁ U) (d : ℕ) (k : Type) [Field k] (x : Sp k ⟶ X),
    Set.range x.base ⊆ (V : Set X) → (∃ u : Sp (TrivSqZeroExt k (Fin d → k)) ⟶ X, spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ u = x ∧ u ≫ s = spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ x ≫ s ∧ ∀ v : Sp (DualNumber k) ⟶ X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ s → ∃! c : (Fin d → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u) →
    ∃ (φ : Γ(X, V) →+* k) (ψ : Γ(X, V) →+* TrivSqZeroExt k (Fin d → k)),
      (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom.comp ψ = φ ∧
      ψ.comp (s.appLE U V e).hom = (algebraMap k (TrivSqZeroExt k (Fin d → k))).comp (φ.comp (s.appLE U V e).hom) ∧
      ∀ v : Γ(X, V) →+* DualNumber k, (TrivSqZeroExt.fstHom k k k).toRingHom.comp v = φ →
        v.comp (s.appLE U V e).hom = (algebraMap k (DualNumber k)).comp (φ.comp (s.appLE U V e).hom) →
        ∃! c : (Fin d → k) →ₗ[k] k, v = (TrivSqZeroExt.map c).toRingHom.comp ψ := by
  intro B _ X s U V hU hV e d k _ x hx hyp
  obtain ⟨u, hux, hus, huniq⟩ := hyp
  obtain ⟨φ, hφ⟩ := exists_ringHom_of_range hV k x hx
  obtain ⟨ψ, hψ⟩ := exists_ringHom_of_range hV _ u ((range_subset_of_fst k _ x u hux).trans hx)
  have key := IsAffineOpen.SpecMap_appLE_fromSpec s hU hV e
  have hs : ∀ (D : Type) [CommRing D] (r : Γ(X, V) →+* D),
      spMap r ≫ hV.fromSpec ≫ s = spMap (r.comp (s.appLE U V e).hom) ≫ hU.fromSpec := by
    intro D _ r
    rw [← key, spMap_comp']
    rfl
  have hbase : ∀ (D : Type) [CommRing D] (alg : k →+* D) (r : Γ(X, V) →+* D),
      (spMap r ≫ hV.fromSpec) ≫ s = spMap alg ≫ x ≫ s ↔
        r.comp (s.appLE U V e).hom = alg.comp (φ.comp (s.appLE U V e).hom) := by
    intro D _ alg r
    rw [hφ]
    simp only [Category.assoc]
    rw [hs, ← Category.assoc (spMap alg) (spMap φ), ← spMap_comp', hs]
    constructor
    · intro h; exact spMap_inj ((cancel_mono hU.fromSpec).mp h)
    · intro h; rw [h]
  have hfst : ∀ (D : Type) [CommRing D] (f : D →+* k) (r : Γ(X, V) →+* D),
      spMap f ≫ spMap r ≫ hV.fromSpec = x ↔ f.comp r = φ := by
    intro D _ f r
    rw [hφ, ← Category.assoc, ← spMap_comp']
    constructor
    · intro h; exact spMap_cancel hV.fromSpec h
    · intro h; rw [h]
  refine ⟨φ, ψ, ?_, ?_, ?_⟩
  · rw [hψ] at hux; exact (hfst _ _ _).mp hux
  · rw [hψ] at hus; exact (hbase _ _ _).mp hus
  · intro v hv1 hv2
    have h1 : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (spMap v ≫ hV.fromSpec) = x := (hfst _ _ _).mpr hv1
    have h2 := (hbase _ _ _).mpr hv2
    obtain ⟨c, hc, hcu⟩ := huniq _ h1 h2
    refine ⟨c, ?_, ?_⟩
    · rw [hψ, ← Category.assoc, ← spMap_comp'] at hc
      exact spMap_cancel hV.fromSpec hc
    · intro c' hc'
      apply hcu
      rw [hψ, ← Category.assoc, ← spMap_comp', ← hc']

end GlobalTheory.SchRing
end
end

