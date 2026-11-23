module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0351
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0099
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0325
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FlatHermRootLineDegree
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PD.PullMap

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ]

theorem prod_prod_erase (g : κ → κ → ℤ) {t : Finset κ} {i : κ} (hi : i ∈ t) (hg : g i i = 1) :
    ∏ a ∈ t, ∏ b ∈ t, g a b =
      (∏ a ∈ t.erase i, ∏ b ∈ t.erase i, g a b) * ∏ a ∈ t.erase i, (g a i * g i a) := by
  have row : ∀ a, ∏ b ∈ t, g a b = g a i * ∏ b ∈ t.erase i, g a b :=
    fun a => (Finset.mul_prod_erase t (g a) hi).symm
  have h1 := Finset.mul_prod_erase t (fun a => ∏ b ∈ t, g a b) hi
  rw [← h1, row i, hg, one_mul, Finset.prod_congr rfl (fun a _ => row a)]
  simp only [Finset.prod_mul_distrib]
  ring

theorem cubeSign_eq_prod (t : Finset κ) (i : κ) :
    cubeSign t i = ∏ a ∈ t, (if a < i then (-1 : ℤ) else 1) := by
  rw [cubeSign, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

theorem cubeSign_image {τ : κ → ι} {t : Finset κ} (h : Set.InjOn τ t) (i : κ) :
    cubeSign (t.image τ) (τ i) = ∏ a ∈ t, (if τ a < τ i then (-1 : ℤ) else 1) := by
  rw [cubeSign_eq_prod, Finset.prod_image (by intro x hx y hy hxy; exact h hx hy hxy)]

theorem pair_sign {τ : κ → ι} {x i : κ} (hx : x ≠ i) (hτ : τ x ≠ τ i) :
    (if x < i ∧ τ i < τ x then (-1 : ℤ) else 1) * (if i < x ∧ τ x < τ i then (-1 : ℤ) else 1) =
      (if x < i then (-1 : ℤ) else 1) * (if τ x < τ i then (-1 : ℤ) else 1) := by
  rcases lt_or_gt_of_ne hx with h | h <;> rcases lt_or_gt_of_ne hτ with h' | h' <;>
    simp [h, h', lt_asymm h, lt_asymm h']

theorem sortSign_eq_erase {τ : κ → ι} {s : Finset κ} {i : κ} (hi : i ∈ s)
    (hne : ∀ x ∈ s.erase i, τ x ≠ τ i) :
    sortSign τ s = sortSign τ (s.erase i) *
      ∏ x ∈ s.erase i, ((if x < i then (-1 : ℤ) else 1) * (if τ x < τ i then (-1 : ℤ) else 1)) := by
  have := prod_prod_erase (fun x y => if x < y ∧ τ y < τ x then (-1 : ℤ) else 1) hi (by simp)
  beta_reduce at this
  unfold sortSign
  rw [this]
  congr 1
  exact Finset.prod_congr rfl fun x hx => pair_sign (Finset.ne_of_mem_erase hx) (hne x hx)

theorem sign_inj {τ : κ → ι} {t : Finset κ} (h : Set.InjOn τ t) {i : κ} (hi : i ∈ t) :
    sortSign τ t * cubeSign (t.image τ) (τ i) = cubeSign t i * sortSign τ (t.erase i) := by
  have e1 := sortSign_eq_erase (τ := τ) hi (fun x hx e =>
    Finset.ne_of_mem_erase hx (h (Finset.mem_of_mem_erase hx) hi e))
  rw [Finset.prod_mul_distrib] at e1
  have e2 : cubeSign t i = ∏ a ∈ t.erase i, (if a < i then (-1 : ℤ) else 1) := by
    rw [cubeSign_eq_prod, ← Finset.mul_prod_erase t _ hi]
    simp
  have e3 : cubeSign (t.image τ) (τ i) = ∏ a ∈ t.erase i, (if τ a < τ i then (-1 : ℤ) else 1) := by
    rw [cubeSign_image h, ← Finset.mul_prod_erase t _ hi]
    simp
  have hQ : (∏ a ∈ t.erase i, (if τ a < τ i then (-1 : ℤ) else 1)) *
      ∏ a ∈ t.erase i, (if τ a < τ i then (-1 : ℤ) else 1) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun a _ => by split_ifs <;> norm_num
  rw [e1, e2, e3]
  linear_combination (sortSign τ (t.erase i) * ∏ a ∈ t.erase i, (if a < i then (-1 : ℤ) else 1)) * hQ

theorem sign_pair {τ : κ → ι} {t : Finset κ} {a b : κ} (ha : a ∈ t) (hb : b ∈ t) (hab : a ≠ b)
    (he : τ a = τ b) (h : Set.InjOn τ (t.erase a)) :
    cubeSign t a * sortSign τ (t.erase a) = -(cubeSign t b * sortSign τ (t.erase b)) := by
  have hb' : b ∈ t.erase a := Finset.mem_erase.2 ⟨hab.symm, hb⟩
  have ha' : a ∈ t.erase b := Finset.mem_erase.2 ⟨hab, ha⟩
  have hu' : (t.erase b).erase a = (t.erase a).erase b := Finset.erase_right_comm
  have mem : ∀ x ∈ (t.erase a).erase b, τ x ≠ τ b := by
    intro x hx e
    have hx1 := Finset.mem_erase.1 hx
    exact hx1.1 (h hx1.2 hb' e)
  have e1 := sortSign_eq_erase (τ := τ) hb' mem
  have e2 := sortSign_eq_erase (τ := τ) ha' (by rw [hu', he]; exact mem)
  rw [hu', he] at e2
  have c1 : cubeSign t a = (if b < a then (-1 : ℤ) else 1) *
      ∏ x ∈ (t.erase a).erase b, (if x < a then (-1 : ℤ) else 1) := by
    rw [cubeSign_eq_prod, ← Finset.mul_prod_erase t _ hb, ← Finset.mul_prod_erase (t.erase b) _ ha', hu']
    simp only [lt_self_iff_false, if_false, one_mul]
  have c2 : cubeSign t b = (if a < b then (-1 : ℤ) else 1) *
      ∏ x ∈ (t.erase a).erase b, (if x < b then (-1 : ℤ) else 1) := by
    rw [cubeSign_eq_prod, ← Finset.mul_prod_erase t _ ha, ← Finset.mul_prod_erase (t.erase a) _ hb']
    simp only [lt_self_iff_false, if_false, one_mul]
  have hs : (if b < a then (-1 : ℤ) else 1) = -(if a < b then (-1 : ℤ) else 1) := by
    rcases lt_or_gt_of_ne hab with h' | h' <;> simp [h', lt_asymm h']
  rw [e1, e2, c1, c2, Finset.prod_mul_distrib, Finset.prod_mul_distrib, hs]
  ring

theorem image_erase_of_injOn {τ : κ → ι} {t : Finset κ} (h : Set.InjOn τ t) {i : κ} (hi : i ∈ t) :
    (t.image τ).erase (τ i) = (t.erase i).image τ := by
  ext y
  simp only [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hy, x, hx, rfl⟩
    exact ⟨x, ⟨fun e => hy (congrArg τ e), hx⟩, rfl⟩
  · rintro ⟨x, ⟨hxi, hx⟩, rfl⟩
    exact ⟨fun e => hxi (h hx hi e), x, hx, rfl⟩

theorem image_erase_eq {τ : κ → ι} {t : Finset κ} {a b : κ} (hb : b ∈ t) (hab : a ≠ b) (he : τ a = τ b) :
    (t.erase a).image τ = t.image τ := by
  ext y
  simp only [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨x, ⟨_, hx⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    by_cases hxa : x = a
    · exact ⟨b, ⟨hab.symm, hb⟩, by rw [hxa]; exact he.symm⟩
    · exact ⟨x, ⟨hxa, hx⟩, rfl⟩

theorem injOn_erase_swap {τ : κ → ι} {t : Finset κ} {a b : κ} (hb : b ∈ t) (hab : a ≠ b)
    (he : τ a = τ b) (h : Set.InjOn τ (t.erase a)) : Set.InjOn τ (t.erase b) := by
  intro x hx y hy hxy
  simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff] at hx hy
  have hb' : b ∈ (↑(t.erase a) : Set κ) := by simp [hab.symm, hb]
  by_cases hxa : x = a <;> by_cases hya : y = a
  · rw [hxa, hya]
  · exact absurd (h (by simp [hya, hy.1]) hb' (by rw [← hxy, hxa, he])) hy.2
  · exact absurd (h (by simp [hxa, hx.1]) hb' (by rw [hxy, hya, he])) hx.2
  · exact h (by simp [hxa, hx.1]) (by simp [hya, hy.1]) hxy

variable {k : Type} [Field k] {E E' : Type} [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E']


open Classical in
theorem pullC_apply (τ : κ → ι) (φ : E →ₗ[k] E') (c : Finset ι → E) (s : Finset κ) :
    pullC τ φ c s = if Set.InjOn τ s then sortSign τ s • φ (c (s.image τ)) else 0 := rfl

theorem pullC_delta (τ : κ → ι) (φ : E →ₗ[k] E') (c : Finset ι → E) :
    pullC τ φ (GlobalTheory.DI.delta c) = GlobalTheory.DI.delta (pullC τ φ c) := by
  funext t
  rw [pullC_apply]
  simp only [GlobalTheory.DI.delta]
  by_cases h : Set.InjOn τ t
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [if_pos h, Finset.sum_image (by intro x hx y hy hxy; exact h hx hy hxy), map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [pullC_apply, if_pos (h.mono (Finset.coe_subset.2 (Finset.erase_subset i t))), map_zsmul,
        ← image_erase_of_injOn h hi, smul_smul, smul_smul, sign_inj h hi]
  · rw [if_neg h]
    have h' : ∃ a ∈ t, ∃ b ∈ t, τ a = τ b ∧ a ≠ b := by
      by_contra hc
      push_neg at hc
      exact h (by intro x hx y hy hxy; exact hc x hx y hy hxy)
    obtain ⟨a, ha, b, hb, he, hab⟩ := h'
    have zero_of : ∀ s : Finset κ, a ∈ s → b ∈ s → pullC τ φ c s = 0 := fun s has hbs => by
      rw [pullC_apply, if_neg]
      intro hs
      exact hab (hs has hbs he)
    rw [Finset.sum_eq_add_of_mem a b ha hb hab (fun x _ hne => by
      rw [zero_of _ (Finset.mem_erase.2 ⟨hne.1.symm, ha⟩) (Finset.mem_erase.2 ⟨hne.2.symm, hb⟩), smul_zero])]
    by_cases hia : Set.InjOn τ (t.erase a)
    · have hib := injOn_erase_swap hb hab he hia
      rw [pullC_apply, pullC_apply, if_pos hia, if_pos hib, image_erase_eq hb hab he,
        image_erase_eq ha hab.symm he.symm, smul_smul, smul_smul, ← add_smul, sign_pair ha hb hab he hia,
        neg_add_cancel, zero_smul]
    · have hib : ¬ Set.InjOn τ (t.erase b) := fun hib => hia (injOn_erase_swap ha hab.symm he.symm hib)
      rw [pullC_apply, pullC_apply, if_neg hia, if_neg hib, smul_zero, smul_zero, add_zero]

theorem pullC_mem (A : Finset ι → Submodule k E) (B : Finset κ → Submodule k E') (τ : κ → ι) (φ : E →ₗ[k] E')
    (hφ : ∀ s : Finset κ, s.Nonempty → ∀ y ∈ A (s.image τ), φ y ∈ B s) (n : ℤ) (c : Finset ι → E)
    (hc : c ∈ cechC A n) : pullC τ φ c ∈ cechC B n := by
  simp only [cechC, Submodule.mem_pi, Set.mem_univ, true_implies, forall_const] at hc ⊢
  intro s
  rw [pullC_apply]
  split_ifs with hs hinj
  · have hcard := Finset.card_image_of_injOn hinj
    have hc' := hc (s.image τ)
    rw [if_pos ⟨hs.1.image τ, by rw [hcard]; exact hs.2⟩] at hc'
    exact zsmul_mem (hφ s hs.1 _ hc') _
  · exact Submodule.zero_mem _
  · rename_i hinj
    have hc' := hc (s.image τ)
    rw [if_neg (fun h' => hs ⟨Finset.image_nonempty.1 h'.1, by
      rw [← Finset.card_image_of_injOn hinj]; exact h'.2⟩), Submodule.mem_bot] at hc'
    rw [hc', map_zero, smul_zero]
    exact Submodule.zero_mem _
  · exact Submodule.zero_mem _

end GlobalTheory.PD.PullMap

namespace GlobalTheory.PD

theorem pullC_isMap : ∀ (k : Type) [Field k] (ι κ : Type) [LinearOrder ι] [LinearOrder κ] (E E' : Type)
    [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E'] (A : Finset ι → Submodule k E)
    (B : Finset κ → Submodule k E') (τ : κ → ι) (φ : E →ₗ[k] E'),
    (∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t) → (∀ s t, s.Nonempty → s ⊆ t → B s ≤ B t) →
    (∀ s : Finset κ, s.Nonempty → ∀ y ∈ A (s.image τ), φ y ∈ B s) →
    IsMap (GlobalTheory.PD.cech A) (GlobalTheory.PD.cech B) (pullC τ φ) := by
  intro k _ ι κ _ _ E E' _ _ _ _ A B τ φ _ _ hφ n c hc
  exact ⟨PullMap.pullC_mem A B τ φ hφ n c hc, PullMap.pullC_delta τ φ c⟩

end GlobalTheory.PD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GermSecRestrictGlobalAlgebraMap
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HodgeCoh

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (s : X ⟶ Sp k)

def germSec {V : X.Opens} (hη : genericPoint X ∈ V) : Sec s V →+* X.functionField :=
  (X.presheaf.germ V (genericPoint X) hη).hom

theorem semiHom_germSec {V : X.Opens} (hη : genericPoint X ∈ V) :
    letI := ffAlg s; SemiHom (RingHom.id k) (germSec s hη) := by
  letI := ffAlg s
  intro r b
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, RingHom.id_apply]
  congr 1
  change (X.presheaf.germ V (genericPoint X) hη).hom ((secMap s V).hom r) =
    (X.presheaf.germ ⊤ (genericPoint X) trivial).hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r))
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  congr 2
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ s.appLE ⊤ V le_top) ≫ _ = _
  simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  rfl

theorem germSec_restrictGlobal_algebraMap {V : X.Opens} (hη : genericPoint X ∈ V) (r : k) :
    letI := algΓ s; letI := ffAlg s
    germSec s hη (restrictGlobal X V (algebraMap k Γ(X, ⊤) r)) = algebraMap k X.functionField r := by
  letI := algΓ s; letI := ffAlg s
  change (X.presheaf.germ V (genericPoint X) hη).hom ((X.presheaf.map (homOfLE le_top).op).hom _) = _
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]
  rfl

def formGerm (j : ℕ) {V : X.Opens} (hV : IsAffineOpen V) (hη : genericPoint X ∈ V) :
    letI := algΓ s; letI := ffAlg s
    sectionsOn (Omega s j) V →ₗ[k] DR k X.functionField :=
  letI := algΓ s; letI := ffAlg s
  { toFun := fun x ↦ (semiHom_germSec s hη).mDR
      ((toOmEquiv s j hV).symm (sectionsOn.toΓ _ _ x) : DR k (Sec s V))
    map_add' := fun x y ↦ by
      rw [map_add (f := _), map_add (f := _), Submodule.coe_add, map_add (f := _)]
    map_smul' := fun r x ↦ by
      rw [sectionsOn.toΓ_smul]
      have h1 : (toOmEquiv s j hV).symm (restrictGlobal X V (algebraMap k Γ(X, ⊤) r) •
          sectionsOn.toΓ _ _ x) = (show Sec s V from restrictGlobal X V (algebraMap k Γ(X, ⊤) r)) •
          (toOmEquiv s j hV).symm (sectionsOn.toΓ _ _ x) :=
        (toOmEquiv s j hV).symm.map_smul _ _
      rw [h1, Submodule.coe_smul, SemiHom.mDR_smul]
      change germSec s hη (restrictGlobal X V (algebraMap k Γ(X, ⊤) r)) • _ = _
      rw [germSec_restrictGlobal_algebraMap, algebraMap_smul]
      rfl }

def formGermI (j : ℕ) {V : X.Opens} (hV : IsAffineOpen V) (hη : genericPoint X ∈ V)
    [inst : Algebra k X.functionField] (hinst : inst = ffAlg s) :
    letI := algΓ s; sectionsOn (Omega s j) V →ₗ[k] DR k X.functionField := by
  subst hinst; exact formGerm s j hV hη

theorem formGermI_ffAlg (j : ℕ) {V : X.Opens} (hV : IsAffineOpen V) (hη : genericPoint X ∈ V) :
    formGermI (inst := ffAlg s) s j hV hη rfl = formGerm s j hV hη := rfl

end GlobalTheory.HodgeCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralClosureOfFiniteMapIntegrallyClosedSubrinStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_of_finite_map_integrallyClosed_subrings : ∀ (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] (B : Subalgebra k K) (B' : Subalgebra k L) (φ : B →+* B'), (∀ x : B, (φ x : L) = algebraMap K L x) → φ.Finite → IsIntegrallyClosed B → IsIntegrallyClosed B' → (∀ x : K, ∃ a ∈ B, ∃ b ∈ B, b ≠ 0 ∧ x * b = a) → (∀ y : L, ∃ a ∈ B', ∃ b ∈ B', b ≠ 0 ∧ y * b = a) → (∀ y ∈ B', IsIntegral B (y : L)) ∧ (∀ x : K, IsIntegral B x → x ∈ B) ∧ (∀ y : L, IsIntegral B y → y ∈ B') := by
  first | (exact @GlobalTheory.W1.integralClosure_of_finite_map) | (exact GlobalTheory.W1.integralClosure_of_finite_map) | (intros; apply GlobalTheory.W1.integralClosure_of_finite_map  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntegrallyClosedSectionsOfSmoothComplexStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegrallyClosed_sections_of_smooth_complex' : ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℂ) [Smooth s] (U : Z.Opens), IsAffineOpen U → genericPoint Z ∈ U → IsIntegrallyClosed Γ(Z, U) := by
  first | (exact @GlobalTheory.isIntegrallyClosed_sections_of_smooth_complex) | (exact GlobalTheory.isIntegrallyClosed_sections_of_smooth_complex) | (intros; apply GlobalTheory.isIntegrallyClosed_sections_of_smooth_complex  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerEvalComplexPointLeSpanJacobian
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.JacSpan

theorem ker_le_span_sup {A : Type} [CommRing A] [Algebra ℂ A] (e : A →+* ℂ)
    (he : ∀ c : ℂ, e (algebraMap ℂ A c) = c) {d : ℕ} (δ : Fin d → A →+ ℂ)
    (hmul : ∀ b f g, δ b (f * g) = e f * δ b g + e g * δ b f)
    (hc : ∀ b (c : ℂ), δ b (algebraMap ℂ A c) = 0) (g : Fin d → A)
    (hgs : ∀ a : A, e a = 0 → ∃ c : Fin d → ℂ, a - ∑ j, c j • g j ∈ RingHom.ker e ^ 2)
    (φ : Fin d → A) (hdet : (Matrix.of fun a b => δ b (φ a)).det ≠ 0) :
    RingHom.ker e ≤ Ideal.span (Set.range fun j => φ j - algebraMap ℂ A (e (φ j))) ⊔
      RingHom.ker e ^ 2 := by
  classical
  have hsq : ∀ b, ∀ x ∈ RingHom.ker e ^ 2, δ b x = 0 := by
    intro b x hx
    rw [pow_two] at hx
    refine Submodule.mul_induction_on hx (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · rw [hmul, RingHom.mem_ker.1 hx, RingHom.mem_ker.1 hy, zero_mul, zero_mul, add_zero]
    · rw [map_add (f := _), hx, hy, add_zero]
  have hsmul : ∀ b (c : ℂ) (x : A), δ b (c • x) = c * δ b x := by
    intro b c x
    rw [Algebra.smul_def, hmul, hc, he, mul_zero, add_zero]
  set φ' : Fin d → A := fun j => φ j - algebraMap ℂ A (e (φ j)) with hφ'
  have hφ'e : ∀ j, e (φ' j) = 0 := fun j => by simp only [hφ', map_sub, he, sub_self]
  choose C hC using fun j => hgs (φ' j) (hφ'e j)
  let M : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun k b => δ b (g k)
  have hJ : (Matrix.of fun a b => δ b (φ a)) = Matrix.of C * M := by
    ext a b
    have h1 := hsq b _ (hC a)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum] at h1
    simp only [hsmul] at h1
    have h2 : δ b (φ' a) = δ b (φ a) := by simp only [hφ', map_sub, hc, sub_zero]
    rw [Matrix.of_apply, Matrix.mul_apply, ← h2]
    simp only [M, Matrix.of_apply]
    linear_combination h1
  have hdetC : (Matrix.of C).det ≠ 0 := by
    rw [hJ, Matrix.det_mul] at hdet
    exact left_ne_zero_of_mul hdet
  have hu : IsUnit (Matrix.of C).det := isUnit_iff_ne_zero.2 hdetC
  intro a ha
  obtain ⟨β, hβ⟩ := hgs a (RingHom.mem_ker.1 ha)
  set γ := Matrix.vecMul β (Matrix.of C)⁻¹ with hγdef
  have hγ : Matrix.vecMul γ (Matrix.of C) = β := by
    rw [hγdef, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
  have hsum : ∑ j, γ j • ∑ k, C j k • g k = ∑ k, β k • g k := by
    rw [← hγ]
    simp only [Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul,
      Matrix.of_apply]
    exact Finset.sum_comm
  have hspan : ∑ j, γ j • φ' j ∈ Ideal.span (Set.range φ') :=
    Ideal.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ _ (Ideal.subset_span ⟨j, rfl⟩)
  have hrest : a - ∑ j, γ j • φ' j ∈ RingHom.ker e ^ 2 := by
    have h3 : a - ∑ j, γ j • φ' j =
        (a - ∑ k, β k • g k) - ∑ j, γ j • (φ' j - ∑ k, C j k • g k) := by
      rw [← hsum]
      simp only [smul_sub, Finset.sum_sub_distrib]
      abel
    rw [h3]
    exact sub_mem hβ (Ideal.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ _ (hC j))
  have h4 : a = (a - ∑ j, γ j • φ' j) + ∑ j, γ j • φ' j := by abel
  rw [h4]
  exact add_mem (Ideal.mem_sup_right hrest) (Ideal.mem_sup_left hspan)

end GlobalTheory.JacSpan


open GlobalTheory.ChartGlue in
theorem GlobalTheory.JacSpan.ker_le_span_jac : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] (U : X.Opens), IsAffineOpen U →
    ∀ (ch : GlobalTheory.AlgChart p (RingHom.id ℂ) d) (φ : Fin d → Γ(X, U)) (z : GlobalTheory.CxPts p (RingHom.id ℂ))
      (_hzc : z ∈ ch.e.source) (hz : z ∈ GlobalTheory.CxPts.ptsIn p (RingHom.id ℂ) U), (ch.jacMat φ z).det ≠ 0 →
      RingHom.ker (GlobalTheory.CxPts.evHom hz) ≤
        Ideal.span (Set.range fun j => φ j - ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U (GlobalTheory.CxPts.evHom hz (φ j))) ⊔
          RingHom.ker (GlobalTheory.CxPts.evHom hz) ^ 2 := by
  intro X p d _ U hU ch φ z hzc hz hdet
  obtain ⟨g, _, hgs, _⟩ := GlobalTheory.CotDim.exists_cotangent_basis X p d U hU z hz
  have hd : ∀ f : Γ(X, U), DifferentiableAt ℂ (CxPts.ev p (RingHom.id ℂ) U f ∘ ch.e.symm) (ch.e z) :=
    fun f => ch.differentiableAt_ev f hzc hz
  have hn : ∀ᶠ v in nhds (ch.e z), ch.e.symm v ∈ CxPts.ptsIn p (RingHom.id ℂ) U :=
    Filter.eventually_of_mem ((isOpen_over ch.e (CxPts.isOpen_ptsIn U)).mem_nhds
      (mem_over ch.e hzc hz)) fun _ h => h.2
  let δ : Fin d → Γ(X, U) →+ ℂ := fun b => AddMonoidHom.mk' (fun f =>
      fderiv ℂ (CxPts.ev p (RingHom.id ℂ) U f ∘ ch.e.symm) (ch.e z) (EuclideanSpace.single b 1))
    (fun f g => by
      have e : CxPts.ev p (RingHom.id ℂ) U (f + g) ∘ ch.e.symm =
          (CxPts.ev p (RingHom.id ℂ) U f ∘ ch.e.symm) + (CxPts.ev p (RingHom.id ℂ) U g ∘ ch.e.symm) :=
        funext fun v => CxPts.ev_add _ _ _
      simp only [e, fderiv_add (hd f) (hd g), ContinuousLinearMap.add_apply])
  have hmul : ∀ b (f g : Γ(X, U)), δ b (f * g) =
      CxPts.evHom hz f * δ b g + CxPts.evHom hz g * δ b f := by
    intro b f g
    have e : CxPts.ev p (RingHom.id ℂ) U (f * g) ∘ ch.e.symm =
        (CxPts.ev p (RingHom.id ℂ) U f ∘ ch.e.symm) * (CxPts.ev p (RingHom.id ℂ) U g ∘ ch.e.symm) :=
      funext fun v => CxPts.ev_mul _ _ _
    simp only [δ, AddMonoidHom.mk'_apply, e, fderiv_mul (hd f) (hd g), Function.comp_apply,
      ch.e.left_inv hzc, CxPts.ev_eq hz, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hc : ∀ b (c : ℂ), δ b (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U c) = 0 := by
    intro b c
    have e : CxPts.ev p (RingHom.id ℂ) U (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U c) ∘ ch.e.symm
        =ᶠ[nhds (ch.e z)] fun _ => c := hn.mono fun v hv => CxPts.ev_algX hv c
    simp only [δ, AddMonoidHom.mk'_apply]
    rw [e.fderiv_eq]
    simp
  exact GlobalTheory.JacSpan.ker_le_span_sup (A := GlobalTheory.CechDR.Sec p U) (CxPts.evHom hz)
    (fun c => (CxPts.ev_eq hz _).symm.trans (CxPts.ev_algX hz c)) δ hmul hc g hgs φ hdet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteSeriesIndependentAwayFromPlaceOverP
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV

theorem away_of_dict : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    J.Dict std → S.Away) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD
  exact _root_.GlobalTheory.TwV.Xc.AwayInd.away_of_pos_pair S hD ⟨J.alg0, J.alg⟩ J.kin (_root_.GlobalTheory.TwV.pos_at_site S) (_root_.GlobalTheory.pairOK_allSites S hD)

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorPolynomialOfRealisingValueStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operatorPolynomial_of_realising_value : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (r : ℂ) (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) (r • Q) Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → ∀ (s : D.what₂.Tau → ℂ), (∀ τ, s τ ≠ 0) → GoodG X Kc j G ∧ OddDeg X j G ∧ ∀ n, AddMonoidAlgebra.coeff (polDel X Kc j G) n = ι (r * cOp X D pos j s) • AddMonoidAlgebra.coeff (trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) n := by
  first | exact @GlobalTheory.TwV.DelA.polDel_realises | exact GlobalTheory.TwV.DelA.polDel_realises | (intros; apply GlobalTheory.TwV.DelA.polDel_realises <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RatioSpanCotangentChangeDenominatorStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratio_span_cotangent_change_denominator : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (N : ℕ) (ι : X ⟶ PSpace ℂ N), IsClosedImmersion ι → ∀ (n : ℕ), 0 < n →
    ∀ (k : ℕ) (f : Fin k → MvPolynomial (Fin (N + 1)) ℂ) (a b : MvPolynomial (Fin (N + 1)) ℂ)
      (hf : ∀ j, f j ∈ GlobalTheory.ProjSpace.grading ℂ N n) (ha : a ∈ GlobalTheory.ProjSpace.grading ℂ N n)
      (hb : b ∈ GlobalTheory.ProjSpace.grading ℂ N n) (z : CxPts p (RingHom.id ℂ))
      (hza : z ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι a))
      (hzb : z ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι b)),
      RingHom.ker (CxPts.evHom hza) ≤ Ideal.span (Set.range fun j => GlobalTheory.EtProj.fRatio ι (f j) a (hf j) ha) ⊔
          RingHom.ker (CxPts.evHom hza) ^ 2 →
      RingHom.ker (CxPts.evHom hzb) ≤ Ideal.span (Set.range fun j => GlobalTheory.EtProj.fRatio ι (f j) b (hf j) hb) ⊔
          RingHom.ker (CxPts.evHom hzb) ^ 2 := by
  first | (exact @GlobalTheory.EtProj.span_ratio_of_span_ratio) | (exact GlobalTheory.EtProj.span_ratio_of_span_ratio) | (intros; apply GlobalTheory.EtProj.span_ratio_of_span_ratio  <;> assumption)
end

