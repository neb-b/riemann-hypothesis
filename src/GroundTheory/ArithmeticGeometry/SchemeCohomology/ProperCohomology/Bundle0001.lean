module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalAlgebra
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open Polynomial

universe u

noncomputable section

section ReesFiltration

variable {A : Type u} [CommRing A] (I : Ideal A) {H : Type u} [AddCommGroup H] [Module A H]

lemma pow_smul_le_of_smul_le {K : ℕ → Submodule A H} (hK : ∀ n, I • K n ≤ K (n + 1))
    (i j : ℕ) : I ^ i • K j ≤ K (j + i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', Submodule.mul_smul, ← add_assoc]
    exact (Submodule.smul_mono le_rfl ih).trans (hK _)

def reesFiltration {K : ℕ → Submodule A H} (hK : ∀ n, I • K n ≤ K (n + 1)) :
    Submodule (reesAlgebra I) (PolynomialModule A H) where
  carrier := {p | ∀ n, p.coeff n ∈ K n}
  add_mem' {p q} hp hq n := by
    have : (p + q).coeff n = p.coeff n + q.coeff n := rfl
    rw [this]
    exact add_mem (hp n) (hq n)
  zero_mem' n := by
    change (0 : PolynomialModule A H).coeff n ∈ K n
    exact (K n).zero_mem
  smul_mem' r p hp n := by
    change ((r : A[X]) • p).coeff n ∈ K n
    rw [PolynomialModule.smul_apply]
    refine Submodule.sum_mem _ fun x hx => ?_
    have hx' : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    have hr : (r : A[X]).coeff x.1 ∈ I ^ x.1 := (mem_reesAlgebra_iff I _).1 r.2 x.1
    have := pow_smul_le_of_smul_le I hK x.1 x.2 (Submodule.smul_mem_smul hr (hp x.2))
    rwa [add_comm, hx'] at this

theorem exists_eq_pow_smul_of_fg {K : ℕ → Submodule A H} (hK : ∀ n, I • K n ≤ K (n + 1))
    (hfg : (reesFiltration I hK).FG) : ∃ c, ∀ n, K (n + c) = I ^ n • K c := by
  classical
  obtain ⟨s, hs⟩ := hfg
  set c := s.sup fun p => p.coeff.support.sup id
  have hdeg : ∀ p ∈ s, ∀ j, c < j → p.coeff j = 0 := by
    intro p hp j hj
    by_contra h
    have h1 : j ≤ p.coeff.support.sup id :=
      Finset.le_sup (f := id) (Finsupp.mem_support_iff.2 h)
    have h2 : p.coeff.support.sup id ≤ c := Finset.le_sup (f := fun p => p.coeff.support.sup id) hp
    omega
  refine ⟨c, fun n => le_antisymm ?_ ?_⟩
  · intro x hx
    have hmem : PolynomialModule.single A (n + c) x ∈ reesFiltration I hK := by
      intro m
      rw [PolynomialModule.coeff_single, Finsupp.single_apply]
      split_ifs with h
      · exact h ▸ hx
      · exact (K m).zero_mem
    rw [← hs, Submodule.mem_span_finset] at hmem
    obtain ⟨f, -, hf⟩ := hmem
    have hx' : x = (∑ p ∈ s, f p • p).coeff (n + c) := by
      rw [hf, PolynomialModule.coeff_single, Finsupp.single_eq_same]
    rw [hx']
    have hsum : (∑ p ∈ s, f p • p).coeff = ∑ p ∈ s, (f p • p).coeff :=
      map_sum (PolynomialModule.coeffAddEquiv (R := A) (M := H)) _ s
    rw [hsum, Finsupp.finsetSum_apply]
    refine Submodule.sum_mem _ fun p hp => ?_
    change (((f p : reesAlgebra I) : A[X]) • p).coeff (n + c) ∈ _
    rw [PolynomialModule.smul_apply]
    refine Submodule.sum_mem _ fun y hy => ?_
    have hy' : y.1 + y.2 = n + c := Finset.HasAntidiagonal.mem_antidiagonal.1 hy
    by_cases hj : c < y.2
    · rw [hdeg p hp y.2 hj, smul_zero]
      exact Submodule.zero_mem _
    · replace hj := not_lt.1 hj
      have hr : ((f p : reesAlgebra I) : A[X]).coeff y.1 ∈ I ^ y.1 :=
        (mem_reesAlgebra_iff I _).1 (f p).2 y.1
      have hp' : p.coeff y.2 ∈ K y.2 := by
        have : p ∈ reesFiltration I hK := hs ▸ Submodule.subset_span hp
        exact this y.2
      have hy1 : y.1 = n + (c - y.2) := by omega
      rw [hy1, pow_add] at hr
      have h1 : ((f p : reesAlgebra I) : A[X]).coeff y.1 • p.coeff y.2 ∈
          (I ^ n * I ^ (c - y.2)) • K y.2 := hy1 ▸ Submodule.smul_mem_smul hr hp'
      rw [Submodule.mul_smul] at h1
      refine Submodule.smul_mono le_rfl ?_ h1
      have := pow_smul_le_of_smul_le I hK (c - y.2) y.2
      rwa [show y.2 + (c - y.2) = c by omega] at this
  · have := pow_smul_le_of_smul_le I hK n c
    rwa [add_comm] at this

end ReesFiltration

end

end GroundTheory.Arith.SchemeCoh
end

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalLimit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

universe u

noncomputable section

section Tower

variable {A : Type u} [CommRing A] {E : ℕ → Type u} [∀ n, AddCommGroup (E n)]
  [∀ n, Module A (E n)] (τ : ∀ n, E (n + 1) →ₗ[A] E n)

def towerLimit : Submodule A (∀ n, E n) where
  carrier := {x | ∀ n, τ n (x (n + 1)) = x n}
  add_mem' {x y} hx hy n := by
    change τ n (x (n + 1) + y (n + 1)) = x n + y n
    rw [map_add (f := _), hx n, hy n]
  zero_mem' n := by
    change τ n 0 = 0
    exact map_zero _
  smul_mem' a x hx n := by
    change τ n (a • x (n + 1)) = a • x n
    rw [map_smul, hx n]

def towerComp (n : ℕ) : (k : ℕ) → E (n + k) →ₗ[A] E n
  | 0 => LinearMap.id
  | k + 1 => (towerComp n k).comp (τ (n + k))

lemma towerComp_apply_of_mem {x : ∀ n, E n} (hx : x ∈ towerLimit τ) (n k : ℕ) :
    towerComp τ n k (x (n + k)) = x n := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change towerComp τ n k (τ (n + k) (x (n + k + 1))) = x n
    rw [hx (n + k)]
    exact ih

theorem towerLimit_eq_bot {c : ℕ} (hc : ∀ n, towerComp τ n c = 0) : towerLimit τ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  funext n
  rw [← towerComp_apply_of_mem τ hx n c, hc n, LinearMap.zero_apply]
  rfl

end Tower

section Exact

variable {A : Type u} [CommRing A]
  {P E Q : ℕ → Type u} [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)]
  [∀ n, AddCommGroup (E n)] [∀ n, Module A (E n)] [∀ n, AddCommGroup (Q n)]
  [∀ n, Module A (Q n)]
  (τP : ∀ n, P (n + 1) →ₗ[A] P n) (τE : ∀ n, E (n + 1) →ₗ[A] E n) (τQ : ∀ n, Q (n + 1) →ₗ[A] Q n)
  (ι : ∀ n, P n →ₗ[A] E n) (π : ∀ n, E n →ₗ[A] Q n)
  (hι : ∀ n, (τE n).comp (ι (n + 1)) = (ι n).comp (τP n))
  (hπ : ∀ n, (τQ n).comp (π (n + 1)) = (π n).comp (τE n))



variable (hinj : ∀ n, Function.Injective (ι n))
  (hex : ∀ n, LinearMap.range (ι n) = LinearMap.ker (π n))

def towerLimitMap : towerLimit τP →ₗ[A] towerLimit τE where
  toFun x := ⟨fun n => ι n (x.1 n), fun n => by
    have := congrArg (fun f => f (x.1 (n + 1))) (hι n)
    simp only [LinearMap.comp_apply] at this
    rw [this, x.2 n]⟩
  map_add' x y := by
    ext n
    exact map_add (ι n) _ _
  map_smul' a x := by
    ext n
    exact map_smul (ι n) _ _


include hι hπ hinj hex in
theorem bijective_towerLimitMap (hinj : ∀ n, Function.Injective (ι n))
    (hex : ∀ n, LinearMap.range (ι n) = LinearMap.ker (π n))
    (hπ : ∀ n, (τQ n).comp (π (n + 1)) = (π n).comp (τE n))
    {c : ℕ} (hc : ∀ n, towerComp τQ n c = 0) :
    Function.Bijective (towerLimitMap τP τE ι hι) := by
  constructor
  · intro x y hxy
    ext n
    exact hinj n (congrArg (fun z : towerLimit τE => z.1 n) hxy)
  · intro e
    have hQ : ∀ n, π n (e.1 n) = 0 := by
      have hmem : (fun n => π n (e.1 n)) ∈ towerLimit τQ := fun n => by
        have := congrArg (fun f => f (e.1 (n + 1))) (hπ n)
        simp only [LinearMap.comp_apply] at this
        rw [this, e.2 n]
      rw [towerLimit_eq_bot τQ hc] at hmem
      intro n
      exact congrFun ((Submodule.mem_bot A).1 hmem) n
    have hp : ∀ n, ∃ p, ι n p = e.1 n := fun n => by
      have : e.1 n ∈ LinearMap.range (ι n) := by
        rw [hex n]
        exact hQ n
      exact this
    choose p hp using hp
    refine ⟨⟨p, fun n => hinj n ?_⟩, ?_⟩
    · have := congrArg (fun f => f (p (n + 1))) (hι n)
      simp only [LinearMap.comp_apply] at this
      rw [← this, hp, hp, e.2 n]
    · ext n
      exact hp n

end Exact

section Adic

variable {A : Type u} [CommRing A] (I : Ideal A) {H : Type u} [AddCommGroup H] [Module A H]
  (K : ℕ → Submodule A H) (hK : Antitone K)

def quotTower : ∀ n, (H ⧸ K (n + 1)) →ₗ[A] (H ⧸ K n) :=
  fun n => Submodule.factor (hK (Nat.le_succ n))

variable {I K}

end Adic

end

end GroundTheory.Arith.SchemeCoh
end

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.PullbackGamma
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

noncomputable section

variable {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

theorem isPushout_app_of_isPullback (H : IsPullback fst snd f g) [IsAffine Y] [IsAffine Z]
    {V : X.Opens} (hV : IsAffineOpen V) :
    IsPushout (f.appLE ⊤ V le_top) g.appTop (fst.app V) (snd.appLE ⊤ (fst ⁻¹ᵁ V) le_top) := by
  have : IsAffine V.toScheme := hV
  have hP := (isPullback_morphismRestrict fst V).paste_vert H
  have hA := isPushout_appTop_of_isPullback hP
  refine hA.of_iso (Iso.refl _) (Scheme.Opens.topIso V) (Iso.refl _)
    (Scheme.Opens.topIso (fst ⁻¹ᵁ V)) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp, Scheme.Hom.comp_appTop, Scheme.Opens.topIso_hom,
      Scheme.Opens.ι_appTop, Scheme.Hom.appLE]
    erw [Category.assoc, ← Functor.map_comp]
    rfl
  · simp
  · simp only [Scheme.Opens.topIso_hom, morphismRestrict_appTop]
    erw [Category.assoc, ← Functor.map_comp, ← Scheme.Hom.naturality]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Scheme.Hom.comp_appTop, Scheme.Opens.topIso_hom,
      Scheme.Opens.ι_appTop, Scheme.Hom.appLE]
    erw [Category.assoc, ← Functor.map_comp]
    rfl

end

end GroundTheory.Arith.SchemeCoh
end

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ReesSubmodule
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open Polynomial

universe u v w

variable {A : Type u} [CommRing A] (I : Ideal A)

section

variable (M : Type v) [AddCommGroup M] [Module A M]

def reesSubmodule : Submodule (reesAlgebra I) (PolynomialModule A M) where
  carrier := {p | ∀ n, p.coeff n ∈ I ^ n • (⊤ : Submodule A M)}
  zero_mem' := fun n => by simp
  add_mem' := fun {p q} hp hq n => by
    simp only [Set.mem_ofPred_eq, PolynomialModule.coeff_add, Finsupp.add_apply] at hp hq ⊢
    exact add_mem (hp n) (hq n)
  smul_mem' := fun r p hp n => by
    simp only [Set.mem_ofPred_eq] at hp ⊢
    change ((r : A[X]) • p).coeff n ∈ _
    rw [PolynomialModule.smul_apply]
    refine Submodule.sum_mem _ fun x hx => ?_
    have hx : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    have hr : (r : A[X]).coeff x.1 ∈ I ^ x.1 := (mem_reesAlgebra_iff I _).1 r.2 x.1
    have h := Submodule.smul_mem_smul hr (hp x.2)
    rw [smul_smul, ← pow_add, hx] at h
    · exact h

variable {I M}

lemma mem_reesSubmodule_iff {p : PolynomialModule A M} :
    p ∈ reesSubmodule I M ↔ ∀ n, p.coeff n ∈ I ^ n • (⊤ : Submodule A M) := Iff.rfl

variable (I M)

lemma single_zero_mem_reesSubmodule (m : M) :
    PolynomialModule.single A 0 m ∈ reesSubmodule I M := by
  intro n
  rw [PolynomialModule.coeff_single, Finsupp.single_apply]
  split_ifs with h
  · subst h
    simp
  · exact zero_mem _

theorem reesSubmodule_eq_span :
    reesSubmodule I M =
      Submodule.span (reesAlgebra I) (Set.range (PolynomialModule.single A 0 : M → _)) := by
  apply le_antisymm
  · intro p hp
    have key : ∀ n, ∀ x ∈ I ^ n • (⊤ : Submodule A M), PolynomialModule.single A n x ∈
        Submodule.span (reesAlgebra I) (Set.range (PolynomialModule.single A 0 : M → _)) := by
      intro n x hx
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro a ha m _
        have hmem : monomial n a ∈ reesAlgebra I := reesAlgebra.monomial_mem.2 ha
        have : PolynomialModule.single A n (a • m) =
            (⟨monomial n a, hmem⟩ : reesAlgebra I) • PolynomialModule.single A 0 m := by
          change _ = monomial n a • PolynomialModule.single A 0 m
          rw [PolynomialModule.monomial_smul_single, add_zero]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
      · intro x y hx hy
        rw [PolynomialModule.single_add]
        exact add_mem hx hy
    have hp' : p = ∑ n ∈ p.coeff.support, PolynomialModule.single A n (p.coeff n) := by
      apply PolynomialModule.coeff_injective
      ext k
      rw [PolynomialModule.coeff_sum, Finsupp.finsetSum_apply]
      simp only [PolynomialModule.coeff_single, Finsupp.single_apply]
      rw [Finset.sum_ite_eq']
      split_ifs with h
      · rfl
      · exact Finsupp.notMem_support_iff.1 h
    rw [hp']
    exact Submodule.sum_mem _ fun n _ => key n _ (hp n)
  · rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    exact single_zero_mem_reesSubmodule I M m

end

section Map

variable {M : Type v} [AddCommGroup M] [Module A M] {N : Type w} [AddCommGroup N] [Module A N]

end Map

end GroundTheory.Arith.SchemeCoh
end

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RestrictIso
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits

universe u

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

lemma isIso_morphismRestrict_of_le {U U' : Y.Opens} (h : U' ≤ U) [IsIso (f ∣_ U)] :
    IsIso (f ∣_ U') := by
  have h1 : IsPullback (f ∣_ U') (f ⁻¹ᵁ U').ι U'.ι f := isPullback_morphismRestrict f U'
  have h2 : IsPullback (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι f := isPullback_morphismRestrict f U
  have hU : Y.homOfLE h ≫ U.ι = U'.ι := Y.homOfLE_ι h
  have hX : X.homOfLE (f.preimage_mono h) ≫ (f ⁻¹ᵁ U).ι = (f ⁻¹ᵁ U').ι := X.homOfLE_ι _
  have hsq : X.homOfLE (f.preimage_mono h) ≫ f ∣_ U = f ∣_ U' ≫ Y.homOfLE h := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, Category.assoc, hU,
      morphismRestrict_ι, ← Category.assoc, hX]
  have h3 : IsPullback (X.homOfLE (f.preimage_mono h)) (f ∣_ U') (f ∣_ U) (Y.homOfLE h) := by
    refine IsPullback.of_right ?_ hsq h2.flip
    rw [hX, hU]
    exact h1.flip
  exact h3.isIso_snd_of_isIso

lemma bijective_app_of_isIso_morphismRestrict {U : Y.Opens} [IsIso (f ∣_ U)] {V : Y.Opens}
    (hV : V ≤ U) : Function.Bijective (f.app V) := by
  have := isIso_morphismRestrict_of_le f hV
  have h0 : IsIso ((f ∣_ V).app ⊤) := inferInstance
  have h1 : IsIso (f.app (V.ι ''ᵁ ⊤) ≫
      X.presheaf.map (eqToHom (image_morphismRestrict_preimage f V ⊤)).op) := by
    rw [← morphismRestrict_app]
    exact h0
  have h2 : IsIso (f.app (V.ι ''ᵁ ⊤)) := IsIso.of_isIso_comp_right _
    (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f V ⊤)).op)
  have e : V.ι ''ᵁ ⊤ = V := V.ι_image_top
  rw [e] at h2
  exact ConcreteCategory.bijective_of_isIso _

lemma injOn_of_isIso_morphismRestrict {U : Y.Opens} [IsIso (f ∣_ U)] :
    Set.InjOn f.base (f ⁻¹ᵁ U : Set X) := by
  intro a ha b hb hab
  have hinj : Function.Injective (f ∣_ U).base :=
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso (f ∣_ U)))).injective
  have := @hinj ⟨a, ha⟩ ⟨b, hb⟩ (Subtype.ext
    ((morphismRestrict_base_coe f U ⟨a, ha⟩).trans (hab.trans
      (morphismRestrict_base_coe f U ⟨b, hb⟩).symm)))
  exact congrArg Subtype.val this

lemma exists_preimage_of_isIso_morphismRestrict {U : Y.Opens} [IsIso (f ∣_ U)] {y : Y}
    (hy : y ∈ U) : ∃ x : X, x ∈ f ⁻¹ᵁ U ∧ f.base x = y := by
  have hsurj : Function.Surjective (f ∣_ U).base :=
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso (f ∣_ U)))).surjective
  obtain ⟨⟨x, hx⟩, hxy⟩ := hsurj ⟨y, hy⟩
  refine ⟨x, hx, ?_⟩
  exact (morphismRestrict_base_coe f U ⟨x, hx⟩).symm.trans (congrArg Subtype.val hxy)

end

end GroundTheory.Arith.SchemeCoh
end

