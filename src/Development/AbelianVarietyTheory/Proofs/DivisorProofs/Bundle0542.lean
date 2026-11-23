module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDescentPicardGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0533
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0532

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDescentPicardGroupStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_descent_picard_group : GlobalTheory.EtC.DivisorPicardCompatibility := by
  first | (exact @GlobalTheory.EtC.b6pic_holds) | (exact GlobalTheory.EtC.b6pic_holds) | (intros; apply GlobalTheory.EtC.b6pic_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleExcisionVanishingUnderRefinement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem mvRefine (L1 : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ), ∃ δ : Ht q (sp (Localization.Away (algebraMap A A' f))) n i →+ Ht q (sp A) (n + 1) i, Function.Exact δ (fun x : Ht q (sp A) (n + 1) i => (pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x, pull _ (spMap (algebraMap A A')) _ _ x)) ∧ ∀ (A₂ : Type) [CommRing A₂] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂], IsExcisionNbhd A A₂ f → ∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ∀ (w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i) (b : Ht q (sp (Localization.Away f)) n i), pull _ (spMap φ) _ _ w = pull _ (spMap (Localization.awayMap (algebraMap A A₂) f)) _ _ b → δ w = 0) (L2 : ∀ (q : ℕ) (A C : Type) [CommRing A] [CommRing C] [Algebra A C] (f g : A), IsCoprime f g → IsExcisionNbhd A C g → ∀ (n i : ℤ) (a : Ht q (sp (Localization.Away (f * g))) n i), pull _ (spMap (Localization.awayMap (algebraMap A C) (f * g))) _ _ a = 0 → ∃ b : Ht q (sp (Localization.Away f)) n i, ∀ ρ : Localization.Away f →+* Localization.Away (f * g), ρ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap ρ) _ _ b = a) : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ) (x : Ht q (sp A) (n + 1) i), pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x = 0 → pull _ (spMap (algebraMap A A')) _ _ x = 0 → ∃ w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i, ∀ (g : A), IsCoprime f g → ∀ (A₂ C : Type) [CommRing A₂] [CommRing C] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂] [Algebra A C], IsExcisionNbhd A A₂ f → IsUnit (algebraMap A A₂ g) → IsExcisionNbhd A C g → ∀ a : Ht q (sp (Localization.Away (f * g))) n i, pull _ (spMap (Localization.awayMap (algebraMap A C) (f * g))) _ _ a = 0 → (∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap A _) = (algebraMap A₂ _).comp (algebraMap A A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a) → x = 0 := by
  intro q A A' _ _ _ f hA' n i x hx1 hx2
  obtain ⟨δ, hδex, hδref⟩ := L1 q A A' f hA' n i
  obtain ⟨w, rfl⟩ := (hδex x).1 (by simp [hx1, hx2])
  refine ⟨w, ?_⟩
  intro g hfg A₂ C _ _ _ _ _ _ hA₂ hg hC a ha hcomp
  obtain ⟨b, hb⟩ := L2 q A C f g hfg hC n i a ha
  have hf2 : IsUnit (algebraMap A₂ (Localization.Away (algebraMap A A₂ f)) (algebraMap A A₂ f)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hg2 : IsUnit (algebraMap A₂ (Localization.Away (algebraMap A A₂ f)) (algebraMap A A₂ g)) := hg.map _
  let φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f) :=
    IsLocalization.Away.lift (algebraMap A A' f)
      (g := (algebraMap A₂ (Localization.Away (algebraMap A A₂ f))).comp (algebraMap A' A₂))
      (by simpa [← IsScalarTower.algebraMap_apply] using hf2)
  let ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap A A₂ f) :=
    IsLocalization.Away.lift (f * g)
      (g := (algebraMap A₂ (Localization.Away (algebraMap A A₂ f))).comp (algebraMap A A₂))
      (by simpa using hf2.mul hg2)
  have hfg' : IsUnit (algebraMap A (Localization.Away (f * g)) f) :=
    isUnit_of_mul_isUnit_left (by simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (f * g)) (f * g))
  let ρ : Localization.Away f →+* Localization.Away (f * g) :=
    IsLocalization.Away.lift f (g := algebraMap A (Localization.Away (f * g))) hfg'
  have hφ : φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) := IsLocalization.Away.lift_comp _ _
  have hψ : ψ.comp (algebraMap A _) = (algebraMap A₂ _).comp (algebraMap A A₂) := IsLocalization.Away.lift_comp _ _
  have hρ : ρ.comp (algebraMap A _) = algebraMap A _ := IsLocalization.Away.lift_comp _ _
  have hψρ : ψ.comp ρ = Localization.awayMap (algebraMap A A₂) f := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    rw [RingHom.comp_assoc, hρ, hψ]
    exact (IsLocalization.map_comp _).symm
  refine hδref A₂ hA₂ φ hφ w b ?_
  rw [hcomp φ ψ hφ hψ, ← hb ρ hρ, ← pull_comp, ← spMap_comp_ring, hψρ]

theorem mvRefine_main : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ) (x : Ht q (sp A) (n + 1) i), pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x = 0 → pull _ (spMap (algebraMap A A')) _ _ x = 0 → ∃ w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i, ∀ (g : A), IsCoprime f g → ∀ (A₂ C : Type) [CommRing A₂] [CommRing C] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂] [Algebra A C], IsExcisionNbhd A A₂ f → IsUnit (algebraMap A A₂ g) → IsExcisionNbhd A C g → ∀ a : Ht q (sp (Localization.Away (f * g))) n i, pull _ (spMap (Localization.awayMap (algebraMap A C) (f * g))) _ _ a = 0 → (∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap A _) = (algebraMap A₂ _).comp (algebraMap A A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a) → x = 0 := mvRefine GlobalTheory.T.exists_natural_excision_boundary_etaleNbhd GlobalTheory.T.mayerVietoris_extend_class_coprime_etaleExcision

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicOfRationalValuation
section
noncomputable section

open GlobalTheory.LatVal (Sz)

namespace GlobalTheory.QFam

theorem exists_algebraic_norm_eq_rpow (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (q : ℚ) :
    ∃ x : algebraicClosure ℚ ℂ, x ≠ 0 ∧ ‖lam x‖ = (l : ℝ) ^ (-(q : ℝ)) := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hlc : (l : algebraicClosure ℚ ℂ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
    have h1 := PadicComplex.norm_extends' l (l : ℚ_[l])
    rw [Padic.norm_p] at h1
    simpa using h1
  haveI : IsAlgClosed (algebraicClosure ℚ ℂ) := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq ((l : algebraicClosure ℚ ℂ) ^ q.num) q.den_pos
  refine ⟨x, ?_, ?_⟩
  · rintro rfl
    rw [zero_pow q.den_ne_zero] at hx
    exact zpow_ne_zero _ hlc hx.symm
  · have h1 : ‖lam x‖ ^ q.den = ((l : ℝ) ^ (-(q : ℝ))) ^ q.den := by
      rw [← norm_pow, ← map_pow, hx, map_zpow₀, map_natCast, norm_zpow, hl, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le,
        inv_zpow', ← Real.rpow_intCast]
      congr 1
      have h2 : (q : ℝ) * (q.den : ℝ) = (q.num : ℝ) := by exact_mod_cast q.mul_den_eq_num
      push_cast
      rw [neg_mul, h2]
    exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg hl0.le _) q.den_ne_zero).1 h1

theorem sz_of_norm_eq {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} {r : ℝ} {x : algebraicClosure ℚ ℂ}
    (hx : ‖lam x‖ = (l : ℝ) ^ (-r)) : Sz l lam (-r) (x : ℂ) :=
  ⟨x.2, hx.le⟩

theorem sz_inv_of_norm_eq {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} {r : ℝ} {x : algebraicClosure ℚ ℂ}
    (hx : ‖lam x‖ = (l : ℝ) ^ (-r)) : Sz l lam r (x : ℂ)⁻¹ := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  refine ⟨inv_mem x.2, ?_⟩
  have e : (⟨(x : ℂ)⁻¹, inv_mem x.2⟩ : algebraicClosure ℚ ℂ) = x⁻¹ := rfl
  rw [e, map_inv₀, norm_inv, hx, Real.rpow_neg hl0.le, inv_inv]

theorem exists_sz_scale : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ q : ℚ,
    ∃ c : ℂ, c ≠ 0 ∧ Sz l lam (-(q : ℝ)) c ∧ Sz l lam q c⁻¹ := by
  intro l _ lam q
  obtain ⟨x, hx0, hx⟩ := exists_algebraic_norm_eq_rpow l lam q
  exact ⟨x, fun h => hx0 (Subtype.ext h), sz_of_norm_eq hx, sz_inv_of_norm_eq hx⟩

end GlobalTheory.QFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechCoboundaryOfDegreeTwoImageCoboundaryAl
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

private theorem mn_ne (s : Finset κ) (h : s.Nonempty) : mn (ne s h) = s.min' h := rfl

private theorem min'_eq_of {s : Finset κ} (h : s.Nonempty) {m : κ} (hm : m ∈ s) (hle : ∀ x ∈ s, m ≤ x) :
    s.min' h = m :=
  le_antisymm (Finset.min'_le _ _ hm) (Finset.le_min' _ _ _ hle)

private theorem max'_eq_of {s : Finset κ} (h : s.Nonempty) {m : κ} (hm : m ∈ s) (hle : ∀ x ∈ s, x ≤ m) :
    s.max' h = m :=
  le_antisymm (Finset.max'_le _ _ _ hle) (Finset.le_max' _ _ hm)

private theorem mp_homOf_eq {p : ℕ} (y : CC F p) (s t : {s : Finset κ // s.card = p + 1}) (e : s.1 = t.1)
    (h : s.1 ⊆ t.1) :
    mp F (homOf (a := ne s.1 (card_nonempty s)) (b := ne t.1 (card_nonempty t)) h) (y s) = y t := by
  obtain ⟨s, hs⟩ := s
  obtain ⟨t, ht⟩ := t
  simp only at e
  subst e
  exact mp_id F _ _

private theorem e2_of_not (y : CC F 2) {a b d : (NE κ)ᵒᵖ} (φ : a ⟶ b) (ψ : b ⟶ d)
    (h : ¬ (mn d < mn b ∧ mn b < mn a)) : e2 F y a b d φ ψ = 0 := by
  simp [e2, h]

private theorem e2_of_lt (y : CC F 2) (t : {s : Finset κ // s.card = 2 + 1}) {a b : (NE κ)ᵒᵖ} (φ : a ⟶ b)
    (ψ : b ⟶ ne t.1 (card_nonempty t)) (h₁ : mn (ne t.1 (card_nonempty t)) < mn b) (h₂ : mn b < mn a) :
    e2 F y a b _ φ ψ = - y t := by
  simp only [e2, LinearMap.pi_apply, dif_pos (And.intro h₁ h₂), LinearMap.neg_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply]
  congr 1
  exact mp_homOf_eq F y ⟨_, card_three h₁ h₂⟩ t
    (Finset.eq_of_subset_of_card_le (triple_subset φ ψ) (by rw [t.2, card_three h₁ h₂]))
    (triple_subset φ ψ)

private theorem f_single (f : C1 F) {m x : κ} (e : m = x) {T : (NE κ)ᵒᵖ}
    (φ : ne {m} (Finset.singleton_nonempty m) ⟶ T) (hx : ({x} : Finset κ) ⊆ sub T) :
    f _ T φ = f (ne {x} (Finset.singleton_nonempty x)) T (homOf hx) := by
  subst e; rfl

def cechOfPosetOne (f : C1 F) : CC F 1 := fun P =>
  f (ne {P.1.min' (card_nonempty P)} (Finset.singleton_nonempty _)) (ne P.1 (card_nonempty P))
      (homOf (Finset.singleton_subset_iff.2 (Finset.min'_mem _ _))) -
    f (ne {P.1.max' (card_nonempty P)} (Finset.singleton_nonempty _)) (ne P.1 (card_nonempty P))
      (homOf (Finset.singleton_subset_iff.2 (Finset.max'_mem _ _)))

variable {F}

private theorem restrict_of_d1 {y : CC F 2} {f : C1 F} (hf : e2 F y = d1 F f) {a P T : (NE κ)ᵒᵖ}
    (φ : a ⟶ P) (ψ : P ⟶ T) :
    mp F ψ (f a P φ) = f a T (φ ≫ ψ) - f P T ψ + e2 F y a P T φ ψ := by
  have := congrFun (congrFun (congrFun (congrFun (congrFun hf a) P) T) φ) ψ
  rw [d1_apply] at this
  rw [this]; abel

theorem restrict_cechOfPosetOne {y : CC F 2} {f : C1 F} (hf : e2 F y = d1 F f)
    (P : {s : Finset κ // s.card = 1 + 1}) (T : (NE κ)ᵒᵖ) (h : P.1 ⊆ sub T) :
    mp F (homOf (a := ne P.1 (card_nonempty P)) (b := T) h) (cechOfPosetOne F f P) =
      f (ne {P.1.min' (card_nonempty P)} (Finset.singleton_nonempty _)) T
        (homOf (b := ne P.1 (card_nonempty P)) (Finset.singleton_subset_iff.2 (Finset.min'_mem _ _)) ≫ homOf h) -
      f (ne {P.1.max' (card_nonempty P)} (Finset.singleton_nonempty _)) T
        (homOf (b := ne P.1 (card_nonempty P)) (Finset.singleton_subset_iff.2 (Finset.max'_mem _ _)) ≫ homOf h) +
      e2 F y (ne {P.1.min' (card_nonempty P)} (Finset.singleton_nonempty _)) (ne P.1 (card_nonempty P)) T
        (homOf (Finset.singleton_subset_iff.2 (Finset.min'_mem _ _))) (homOf h) -
      e2 F y (ne {P.1.max' (card_nonempty P)} (Finset.singleton_nonempty _)) (ne P.1 (card_nonempty P)) T
        (homOf (Finset.singleton_subset_iff.2 (Finset.max'_mem _ _))) (homOf h) := by
  simp only [cechOfPosetOne, map_sub]
  rw [restrict_of_d1 hf, restrict_of_d1 hf]
  abel

private theorem e2_min_single (y : CC F 2) (P : {s : Finset κ // s.card = 1 + 1}) (T : (NE κ)ᵒᵖ)
    (φ : ne {P.1.min' (card_nonempty P)} (Finset.singleton_nonempty _) ⟶ ne P.1 (card_nonempty P))
    (ψ : ne P.1 (card_nonempty P) ⟶ T) :
    e2 F y _ _ T φ ψ = 0 :=
  e2_of_not F y φ ψ (fun h => (lt_irrefl _) (h.2.trans_eq (Finset.min'_singleton _).symm))

private theorem e2_max_single_of_le (y : CC F 2) (P : {s : Finset κ // s.card = 1 + 1}) (T : (NE κ)ᵒᵖ)
    (φ : ne {P.1.max' (card_nonempty P)} (Finset.singleton_nonempty _) ⟶ ne P.1 (card_nonempty P))
    (ψ : ne P.1 (card_nonempty P) ⟶ T) (h : ¬ mn T < P.1.min' (card_nonempty P)) :
    e2 F y _ _ T φ ψ = 0 :=
  e2_of_not F y φ ψ (fun h' => h h'.1)

private theorem e2_max_single_of_lt (y : CC F 2) (P : {s : Finset κ // s.card = 1 + 1})
    (t : {s : Finset κ // s.card = 2 + 1})
    (φ : ne {P.1.max' (card_nonempty P)} (Finset.singleton_nonempty _) ⟶ ne P.1 (card_nonempty P))
    (ψ : ne P.1 (card_nonempty P) ⟶ ne t.1 (card_nonempty t))
    (h : mn (ne t.1 (card_nonempty t)) < P.1.min' (card_nonempty P)) :
    e2 F y _ _ _ φ ψ = - y t :=
  e2_of_lt F y t φ ψ h (by
    rw [mn_ne, mn_ne, Finset.min'_singleton]
    exact Finset.min'_lt_max'_of_card _ (by rw [P.2]; omega))

theorem delta_cechOfPosetOne_of_eq {y : CC F 2} {f : C1 F} (hf : e2 F y = d1 F f)
    (t : {s : Finset κ // s.card = 2 + 1}) {i j k : κ} (hij : i < j) (hjk : j < k)
    (ht : t.1 = {i, j, k}) : δ F 1 (cechOfPosetOne F f) t = y t := by
  have hik := hij.trans hjk
  have hi : i ∈ t.1 := by rw [ht]; simp
  have hj : j ∈ t.1 := by rw [ht]; simp
  have hk : k ∈ t.1 := by rw [ht]; simp
  have huniv : (Finset.univ : Finset t.1) = {⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩} := by
    ext ⟨x, hx⟩
    have hx' := hx
    rw [ht] at hx'
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, true_iff]
    simpa using hx'
  rw [δ_apply, huniv, Finset.sum_insert (by simp [hij.ne, hik.ne]), Finset.sum_insert (by simp [hjk.ne]),
    Finset.sum_singleton]
  erw [restrict_cechOfPosetOne hf, restrict_cechOfPosetOne hf, restrict_cechOfPosetOne hf]
  all_goals first | exact Finset.erase_subset _ _ | skip
  have hle : ∀ x ∈ t.1, i ≤ x := by
    intro x hx
    rw [ht] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    exacts [le_rfl, hij.le, hik.le]
  have tmin : mn (ne t.1 (card_nonempty t)) = i := min'_eq_of _ hi hle
  have mem3 : ∀ {x z : κ}, z ∈ t.1.erase x ↔ z ≠ x ∧ (z = i ∨ z = j ∨ z = k) := by
    intro x z; rw [ht]; simp
  have iMin : ∀ h, (Cube.eraseIdx t ⟨i, hi⟩).1.min' h = j := fun h =>
    min'_eq_of h (mem3.2 ⟨hij.ne', by simp⟩) (fun z hz => by
      obtain ⟨hne, rfl | rfl | rfl⟩ := mem3.1 hz
      exacts [absurd rfl hne, le_rfl, hjk.le])
  have iMax : ∀ h, (Cube.eraseIdx t ⟨i, hi⟩).1.max' h = k := fun h =>
    max'_eq_of h (mem3.2 ⟨hik.ne', by simp⟩) (fun z hz => by
      obtain ⟨hne, rfl | rfl | rfl⟩ := mem3.1 hz
      exacts [absurd rfl hne, hjk.le, le_rfl])
  have jMin : ∀ h, (Cube.eraseIdx t ⟨j, hj⟩).1.min' h = i := fun h =>
    min'_eq_of h (mem3.2 ⟨hij.ne, by simp⟩) (fun z hz => by
      obtain ⟨hne, rfl | rfl | rfl⟩ := mem3.1 hz
      exacts [le_rfl, absurd rfl hne, hik.le])
  have jMax : ∀ h, (Cube.eraseIdx t ⟨j, hj⟩).1.max' h = k := fun h =>
    max'_eq_of h (mem3.2 ⟨hjk.ne', by simp⟩) (fun z hz => by
      obtain ⟨hne, rfl | rfl | rfl⟩ := mem3.1 hz
      exacts [hik.le, absurd rfl hne, le_rfl])
  have kMin : ∀ h, (Cube.eraseIdx t ⟨k, hk⟩).1.min' h = i := fun h =>
    min'_eq_of h (mem3.2 ⟨hik.ne, by simp⟩) (fun z hz => by
      obtain ⟨hne, rfl | rfl | rfl⟩ := mem3.1 hz
      exacts [le_rfl, hij.le, absurd rfl hne])
  have kMax : ∀ h, (Cube.eraseIdx t ⟨k, hk⟩).1.max' h = j := fun h =>
    max'_eq_of h (mem3.2 ⟨hjk.ne, by simp⟩) (fun z hz => by
      obtain ⟨hne, rfl | rfl | rfl⟩ := mem3.1 hz
      exacts [hij.le, le_rfl, absurd rfl hne])
  have hiT : ({i} : Finset κ) ⊆ sub (ne t.1 (card_nonempty t)) := Finset.singleton_subset_iff.2 hi
  have hjT : ({j} : Finset κ) ⊆ sub (ne t.1 (card_nonempty t)) := Finset.singleton_subset_iff.2 hj
  have hkT : ({k} : Finset κ) ⊆ sub (ne t.1 (card_nonempty t)) := Finset.singleton_subset_iff.2 hk
  have lI : mn (ne t.1 (card_nonempty t)) <
      (Cube.eraseIdx t ⟨i, hi⟩).1.min' (card_nonempty (Cube.eraseIdx t ⟨i, hi⟩)) := by
    rw [tmin, iMin]; exact hij
  have lJ : ¬ mn (ne t.1 (card_nonempty t)) <
      (Cube.eraseIdx t ⟨j, hj⟩).1.min' (card_nonempty (Cube.eraseIdx t ⟨j, hj⟩)) := by
    rw [tmin, jMin]; exact lt_irrefl _
  have lK : ¬ mn (ne t.1 (card_nonempty t)) <
      (Cube.eraseIdx t ⟨k, hk⟩).1.min' (card_nonempty (Cube.eraseIdx t ⟨k, hk⟩)) := by
    rw [tmin, kMin]; exact lt_irrefl _
  have sI : cubeSign t.1 i = 1 := cubeSign_eq_one_of_forall_le hle
  have sJ : cubeSign t.1 j = -1 := by
    rw [cubeSign, ht, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
    simp [hij, hjk.not_gt, lt_irrefl]
  have sK : cubeSign t.1 k = 1 := by
    rw [cubeSign, ht, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
    simp [hik, hjk, lt_irrefl, Finset.card_pair hij.ne]
  erw [e2_min_single y (Cube.eraseIdx t ⟨i, hi⟩) (ne t.1 (card_nonempty t)),
    e2_min_single y (Cube.eraseIdx t ⟨j, hj⟩) (ne t.1 (card_nonempty t)),
    e2_min_single y (Cube.eraseIdx t ⟨k, hk⟩) (ne t.1 (card_nonempty t)),
    e2_max_single_of_lt y (Cube.eraseIdx t ⟨i, hi⟩) t _ _ lI,
    e2_max_single_of_le y (Cube.eraseIdx t ⟨j, hj⟩) _ _ _ lJ,
    e2_max_single_of_le y (Cube.eraseIdx t ⟨k, hk⟩) _ _ _ lK,
    f_single F f (iMin _) _ hjT, f_single F f (iMax _) _ hkT,
    f_single F f (jMin _) _ hiT, f_single F f (jMax _) _ hkT,
    f_single F f (kMin _) _ hiT, f_single F f (kMax _) _ hjT]
  erw [sI, sJ, sK]
  simp only [one_smul, neg_smul, sub_zero, add_zero, sub_neg_eq_add]
  abel

end GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

theorem exists_cech_coboundary_of_degreeTwo_image_coboundary : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R]
    (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (y : CC F 2), δ F 2 y = 0 → ∀ f : C1 F, e2 F y = d1 F f →
      ∃ c : CC F 1, δ F 1 c = y := by
  intro κ _ R _ F y _ f hf
  refine ⟨cechOfPosetOne F f, funext fun (t : {s : Finset κ // s.card = 2 + 1}) => ?_⟩
  obtain ⟨a, b, d, hab, had, hbd, ht⟩ := Finset.card_eq_three.1 t.2
  rcases lt_or_gt_of_ne hab with h₁ | h₁ <;> rcases lt_or_gt_of_ne had with h₂ | h₂ <;>
    rcases lt_or_gt_of_ne hbd with h₃ | h₃
  all_goals first
    | exact delta_cechOfPosetOne_of_eq hf t (by assumption : a < b) (by assumption : b < d)
        (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))
    | exact delta_cechOfPosetOne_of_eq hf t (by assumption : a < d) (by assumption : d < b)
        (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))
    | exact delta_cechOfPosetOne_of_eq hf t (by assumption : b < a) (by assumption : a < d)
        (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))
    | exact delta_cechOfPosetOne_of_eq hf t (by assumption : b < d) (by assumption : d < a)
        (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))
    | exact delta_cechOfPosetOne_of_eq hf t (by assumption : d < a) (by assumption : a < b)
        (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))
    | exact delta_cechOfPosetOne_of_eq hf t (by assumption : d < b) (by assumption : b < a)
        (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))
    | exact (lt_irrefl _ ((h₁.trans h₃).trans h₂)).elim
    | exact (lt_irrefl _ ((h₁.trans h₂).trans h₃)).elim

end GlobalTheory.CechPoset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechPrimitiveOfImageCoboundary
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

namespace GlobalTheory.CechHOneInj

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

theorem hom_eq {a b : (NE κ)ᵒᵖ} (f f' : a ⟶ b) : f = f' :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem mp_transport0 (g : C0 F) {a a' b : (NE κ)ᵒᵖ} (e : a = a') (f : a ⟶ b) (f' : a' ⟶ b) :
    mp F f (g a) = mp F f' (g a') := by
  subst e; rw [hom_eq f f']

theorem mp_transport1 {p : ℕ} (x : CC F p) {s s' : {s : Finset κ // s.card = p + 1}} (e : s = s')
    {b : (NE κ)ᵒᵖ} (f : ne s.1 (card_nonempty s) ⟶ b) (f' : ne s'.1 (card_nonempty s') ⟶ b) :
    mp F f (x s) = mp F f' (x s') := by
  subst e; rw [hom_eq f f']

theorem ne_eq_ne {s s' : Finset κ} (hs : s.Nonempty) (hs' : s'.Nonempty) (e : s = s') :
    ne s hs = ne s' hs' := by
  subst e; rfl

theorem min'_pair {i j : κ} (h : i < j) : ({i, j} : Finset κ).min' (Finset.insert_nonempty _ _) = i :=
  le_antisymm (Finset.min'_le _ _ (Finset.mem_insert_self _ _))
    (Finset.le_min' _ _ _ (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> [exact le_rfl; exact h.le]))

theorem orderedCechToCatCochainsOne_apply_valueAtSubset (z : CC F 1) {a b : (NE κ)ᵒᵖ} (f : a ⟶ b) :
    e1 F z a b f = if h : mn b < mn a then
      -(mp F (homOf (a := ne {mn b, mn a} (Finset.insert_nonempty _ _)) (b := b) (pair_subset f))
        (z ⟨{mn b, mn a}, Finset.card_pair h.ne⟩)) else 0 := by
  simp only [e1, LinearMap.pi_apply]; split_ifs <;> simp

end GlobalTheory.CechHOneInj

namespace GlobalTheory.CechHOneInj

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

theorem δ_pair (z : CC F 1) (g : C0 F) (hg : e1 F z = d0 F g) {i j : κ} (h : i < j)
    (hs : ({i, j} : Finset κ).card = 1 + 1) :
    δ F 0 (fun s => g (ne s.1 (card_nonempty s))) ⟨{i, j}, hs⟩ = z ⟨{i, j}, hs⟩ := by
  have hi : i ∈ ({i, j} : Finset κ) := Finset.mem_insert_self _ _
  have hj : j ∈ ({i, j} : Finset κ) := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have sij : ({i} : Finset κ) ⊆ {i, j} := Finset.singleton_subset_iff.2 hi
  have sji : ({j} : Finset κ) ⊆ {i, j} := Finset.singleton_subset_iff.2 hj
  have ei : ({i, j} : Finset κ).erase i = {j} := Finset.erase_insert (by simp [h.ne])
  have ej : ({i, j} : Finset κ).erase j = {i} := by
    ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, rfl | rfl⟩
      · rfl
      · exact absurd rfl hx
    · rintro rfl; exact ⟨h.ne, Or.inl rfl⟩
  have h1 := congrFun (congrFun (congrFun hg (ne {i} (Finset.singleton_nonempty _)))
    (ne {i, j} (Finset.insert_nonempty _ _))) (homOf sij)
  have h2 := congrFun (congrFun (congrFun hg (ne {j} (Finset.singleton_nonempty _)))
    (ne {i, j} (Finset.insert_nonempty _ _))) (homOf sji)
  have mi : mn (ne ({i} : Finset κ) (Finset.singleton_nonempty _)) = i := Finset.min'_singleton i
  have mj : mn (ne ({j} : Finset κ) (Finset.singleton_nonempty _)) = j := Finset.min'_singleton j
  have mij : mn (ne ({i, j} : Finset κ) (Finset.insert_nonempty _ _)) = i := min'_pair h
  rw [orderedCechToCatCochainsOne_apply_valueAtSubset, amitsur_d0_apply, dite_eq_right (by rw [mi, mij]; exact lt_irrefl i)] at h1
  rw [orderedCechToCatCochainsOne_apply_valueAtSubset, amitsur_d0_apply, dite_eq_left (by rw [mj, mij]; exact h)] at h2
  have key := mp_transport1 F z
    (s := ⟨{mn (ne {i, j} (Finset.insert_nonempty _ _)), mn (ne {j} (Finset.singleton_nonempty _))},
      Finset.card_pair (by rw [mj, mij]; exact h.ne)⟩) (s' := ⟨{i, j}, hs⟩)
    (Subtype.ext (by simp only [mj, mij])) (homOf (pair_subset (homOf sji))) (𝟙 _)
  rw [mp_id] at key
  have si : GlobalTheory.cubeSign ({i, j} : Finset κ) i = 1 :=
    GlobalTheory.cubeSign_eq_one_of_forall_le (by
      intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact le_rfl
      · exact h.le)
  have sj : GlobalTheory.cubeSign ({i, j} : Finset κ) j = -1 := by
    have := GlobalTheory.cubeSign_erase_of_lt hi h (t := ({i, j} : Finset κ))
    rw [ei, GlobalTheory.cubeSign_singleton] at this
    linarith
  rw [δ_apply, Fintype.sum_eq_add ⟨i, hi⟩ ⟨j, hj⟩ (by simp [h.ne]) (by
    rintro ⟨x, hx⟩ ⟨ha, hb⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact absurd rfl ha
    · exact absurd rfl hb)]
  dsimp only
  have tj := mp_transport0 F g (ne_eq_ne _ (Finset.singleton_nonempty j) ei)
    (homOf (a := ne _ (card_nonempty (GlobalTheory.Cube.eraseIdx (⟨{i, j}, hs⟩ : {s : Finset κ // s.card = 1 + 1}) ⟨i, hi⟩)))
      (b := ne {i, j} (Finset.insert_nonempty _ _)) (Finset.erase_subset _ _))
    (homOf (a := ne {j} (Finset.singleton_nonempty j)) (b := ne {i, j} (Finset.insert_nonempty _ _)) sji)
  have ti := mp_transport0 F g (ne_eq_ne _ (Finset.singleton_nonempty i) ej)
    (homOf (a := ne _ (card_nonempty (GlobalTheory.Cube.eraseIdx (⟨{i, j}, hs⟩ : {s : Finset κ // s.card = 1 + 1}) ⟨j, hj⟩)))
      (b := ne {i, j} (Finset.insert_nonempty _ _)) (Finset.erase_subset _ _))
    (homOf (a := ne {i} (Finset.singleton_nonempty i)) (b := ne {i, j} (Finset.insert_nonempty _ _)) sij)
  rw [si, sj, one_smul, neg_smul, one_smul]
  linear_combination h2 - h1 + key + tj - ti

theorem exists_cech_primitive : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R]
    (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (z : CC F 1), δ F 1 z = 0 →
    ∀ g : C0 F, e1 F z = d0 F g → ∃ c : CC F 0, δ F 0 c = z := by
  intro κ _ R _ F z _ g hg
  refine ⟨fun s => g (ne s.1 (card_nonempty s)), ?_⟩
  funext t
  obtain ⟨s, hs⟩ := t
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 hs
  rcases lt_or_gt_of_ne hij with h | h
  · exact δ_pair F z g hg h hs
  · revert hs
    rw [Finset.pair_comm i j]
    exact δ_pair F z g hg h

end GlobalTheory.CechHOneInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorDerivGlobalOneFormEqSumWedge
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem dOne_glob_eq_wsum : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    HasFrame F → CohomZeroIsConstants F → ∀ w : Glob1 F, ∃ (n : ℕ) (u v : Fin n → Glob1 F), ClRel F w u v := by
  intro R _ C _ F hF hH w
  obtain ⟨n, u, v, h⟩ := twoForm_eq_wsum R C F hF hH (fun T ↦ dOne R (F.obj T) (w.1 T))
    (fun T T' φ ↦ by rw [pOm_dOne, ← w.2 φ])
  exact ⟨n, u, v, fun T ↦ congrFun h T⟩

end GlobalTheory.AbCoh
end

