module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0005
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.RadicalAwayRabinowitsch
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {R : Type*} [CommRing R] {ι : Type*}

def rabinowitschIdeal (K : Ideal (MvPolynomial ι R)) (g : MvPolynomial ι R) :
    Ideal (MvPolynomial (Option ι) R) :=
  K.map (rename (R := R) some).toRingHom ⊔ Ideal.span {X none * rename some g - 1}

theorem rabinowitschIdeal_map {R' : Type*} [CommRing R'] (φ : R →+* R')
    (K : Ideal (MvPolynomial ι R)) (g : MvPolynomial ι R) :
    (rabinowitschIdeal K g).map (MvPolynomial.map φ) =
      rabinowitschIdeal (K.map (MvPolynomial.map φ)) (MvPolynomial.map φ g) := by
  have h : (MvPolynomial.map φ).comp (rename (R := R) (some : ι → Option ι)).toRingHom =
      (rename (R := R') (some : ι → Option ι)).toRingHom.comp (MvPolynomial.map φ) :=
    RingHom.ext fun p => by simp [map_rename]
  simp only [rabinowitschIdeal, Ideal.map_sup, Ideal.map_span, Ideal.map_map, Set.image_singleton,
    map_sub, map_mul, map_one, map_X, h]
  simp [map_rename]

theorem pow_sub_one_mem_span (g : MvPolynomial ι R) (k : ℕ) :
    (X none * rename some g) ^ k - 1 ∈
      (Ideal.span {X none * rename some g - 1} : Ideal (MvPolynomial (Option ι) R)) := by
  rw [Ideal.mem_span_singleton]
  simpa using sub_dvd_pow_sub_pow (X none * rename some g : MvPolynomial (Option ι) R) 1 k

def rabinowitschEval (K : Ideal (MvPolynomial ι R)) (g : MvPolynomial ι R) :
    MvPolynomial (Option ι) R →+* Localization.Away (Ideal.Quotient.mk K g) :=
  eval₂Hom ((algebraMap (MvPolynomial ι R ⧸ K) _).comp ((Ideal.Quotient.mk K).comp C))
    fun o => Option.elim o (IsLocalization.Away.invSelf (Ideal.Quotient.mk K g))
      fun i => algebraMap (MvPolynomial ι R ⧸ K) _ (Ideal.Quotient.mk K (X i))

theorem rabinowitschEval_rename (K : Ideal (MvPolynomial ι R)) (g p : MvPolynomial ι R) :
    rabinowitschEval K g (rename some p) =
      algebraMap (MvPolynomial ι R ⧸ K) _ (Ideal.Quotient.mk K p) := by
  have h : (rabinowitschEval K g).comp (rename (R := R) (some : ι → Option ι)).toRingHom =
      (algebraMap (MvPolynomial ι R ⧸ K) (Localization.Away (Ideal.Quotient.mk K g))).comp
        (Ideal.Quotient.mk K) :=
    MvPolynomial.ringHom_ext (fun r => by simp [rabinowitschEval]) (fun i => by simp [rabinowitschEval])
  exact congrArg (fun f => f p) h

theorem rabinowitschIdeal_le_ker (K : Ideal (MvPolynomial ι R)) (g : MvPolynomial ι R) :
    rabinowitschIdeal K g ≤ RingHom.ker (rabinowitschEval K g) := by
  refine sup_le ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    simp [RingHom.mem_ker, rabinowitschEval_rename, Ideal.Quotient.eq_zero_iff_mem.2 hp]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, map_one, rabinowitschEval_rename]
    rw [show rabinowitschEval K g (X none) = IsLocalization.Away.invSelf (Ideal.Quotient.mk K g) by
      simp [rabinowitschEval], mul_comm, IsLocalization.Away.mul_invSelf, sub_self]

theorem rename_mem_rabinowitschIdeal_iff (K : Ideal (MvPolynomial ι R)) (g f : MvPolynomial ι R) :
    rename some f ∈ rabinowitschIdeal K g ↔ ∃ k : ℕ, g ^ k * f ∈ K := by
  constructor
  · intro hf
    have h0 := rabinowitschIdeal_le_ker K g hf
    rw [RingHom.mem_ker, rabinowitschEval_rename,
      IsLocalization.map_eq_zero_iff (Submonoid.powers (Ideal.Quotient.mk K g))] at h0
    obtain ⟨⟨m, k, rfl⟩, hm⟩ := h0
    refine ⟨k, Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩
    simpa using hm
  · rintro ⟨k, hk⟩
    have e : (rename some f : MvPolynomial (Option ι) R) =
        X none ^ k * rename some (g ^ k * f) -
          rename some f * ((X none * rename some g) ^ k - 1) := by
      simp only [map_mul, map_pow]; ring
    rw [e]
    refine Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_sup_left ?_))
      (Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (pow_sub_one_mem_span g k)))
    exact Ideal.mem_map_of_mem _ hk

theorem exists_pow_mul_sub_rename_mem (g : MvPolynomial ι R) (h : MvPolynomial (Option ι) R) :
    ∃ (N : ℕ) (f : MvPolynomial ι R), rename some g ^ N * h - rename some f ∈
      (Ideal.span {X none * rename some g - 1} : Ideal (MvPolynomial (Option ι) R)) := by
  induction h using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, by simp⟩
  | add p q hp hq =>
    obtain ⟨N₁, f₁, h₁⟩ := hp
    obtain ⟨N₂, f₂, h₂⟩ := hq
    refine ⟨N₁ + N₂, g ^ N₂ * f₁ + g ^ N₁ * f₂, ?_⟩
    have e : rename some g ^ (N₁ + N₂) * (p + q) - rename some (g ^ N₂ * f₁ + g ^ N₁ * f₂) =
        rename some g ^ N₂ * (rename some g ^ N₁ * p - rename some f₁) +
          rename some g ^ N₁ * (rename some g ^ N₂ * q - rename some f₂) := by
      simp only [map_add (f := _), map_mul, map_pow]; ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h₁) (Ideal.mul_mem_left _ _ h₂)
  | mul_X p j hp =>
    obtain ⟨N, f, hf⟩ := hp
    cases j with
    | none =>
      refine ⟨N + 1, f, ?_⟩
      have e : rename some g ^ (N + 1) * (p * X none) - rename some f =
          (rename some g ^ N * p - rename some f) +
            rename some g ^ N * p * (X none * rename some g - 1) := by ring
      rw [e]
      exact Ideal.add_mem _ hf (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))
    | some i =>
      refine ⟨N, f * X i, ?_⟩
      have e : rename some g ^ N * (p * X (some i)) - rename some (f * X i) =
          (rename some g ^ N * p - rename some f) * X (some i) := by
        simp only [map_mul, rename_X]; ring
      rw [e]
      exact Ideal.mul_mem_right _ _ hf

theorem isRadicalAway_iff_isRadical_rabinowitschIdeal (K : Ideal (MvPolynomial ι R))
    (g : MvPolynomial ι R) : IsRadicalAway K g ↔ (rabinowitschIdeal K g).IsRadical := by
  constructor
  · intro hK h ⟨m, hm⟩
    obtain ⟨N, f, hf⟩ := exists_pow_mul_sub_rename_mem g h
    have hf' : rename some g ^ N * h - rename some f ∈ rabinowitschIdeal K g := Ideal.mem_sup_right hf

    have hfm : rename some (f ^ m) ∈ rabinowitschIdeal K g := by
      have hd : (rename some g ^ N * h) ^ m - rename some f ^ m ∈ rabinowitschIdeal K g := by
        obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (rename some g ^ N * h) (rename some f) m
        rw [hc]
        exact Ideal.mul_mem_right _ _ hf'
      have hp : (rename some g ^ N * h) ^ m ∈ rabinowitschIdeal K g := by
        rw [mul_pow]
        exact Ideal.mul_mem_left _ _ hm
      rw [map_pow]
      simpa using Ideal.sub_mem _ hp hd
    obtain ⟨k, hk⟩ := (rename_mem_rabinowitschIdeal_iff K g _).1 hfm

    have hrad : g ^ k * f ∈ K.radical := by
      refine ⟨m + 1, ?_⟩
      have e : (g ^ k * f) ^ (m + 1) = (g ^ (k * m) * f) * (g ^ k * f ^ m) := by ring
      rw [e]
      exact Ideal.mul_mem_left _ _ hk
    obtain ⟨j, hj⟩ := hK _ hrad
    have hfK : rename some f ∈ rabinowitschIdeal K g :=
      (rename_mem_rabinowitschIdeal_iff K g f).2 ⟨j + k, by rw [pow_add, mul_assoc]; exact hj⟩
    have hgh : rename some g ^ N * h ∈ rabinowitschIdeal K g := by
      simpa using Ideal.add_mem _ hf' hfK
    have e : h = X none ^ N * (rename some g ^ N * h) -
        h * ((X none * rename some g) ^ N - 1) := by ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hgh)
      (Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (pow_sub_one_mem_span g N)))
  · intro hR f ⟨m, hm⟩
    have h1 : rename some f ∈ rabinowitschIdeal K g := by
      refine hR ⟨m, ?_⟩
      rw [← map_pow]
      exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hm)
    exact (rename_mem_rabinowitschIdeal_iff K g f).1 h1

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.RegularQuotientGenerators
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing Ideal

universe u

theorem spanFinrank_maximalIdeal_le_quotient_of_le_sq {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {I : Ideal R} (hI : I ≤ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ I)] :
    (maximalIdeal R).spanFinrank ≤ (maximalIdeal (R ⧸ I)).spanFinrank := by
  classical
  obtain ⟨t, htc, hts⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (IsNoetherian.noetherian (maximalIdeal (R ⧸ I)))
  choose g hg using fun y : R ⧸ I => Ideal.Quotient.mk_surjective y
  set s : Finset R := t.image g with hs
  have hmk : ∀ a ∈ maximalIdeal R, Ideal.Quotient.mk I a ∈ maximalIdeal (R ⧸ I) := by
    intro a ha
    have h := Ideal.mem_map_of_mem (Ideal.Quotient.mk I) ha
    rwa [map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective] at h
  have hsm : (s : Set R) ⊆ maximalIdeal R := by
    intro a ha
    simp only [hs, Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha
    obtain ⟨y, hy, rfl⟩ := ha
    have hy' : y ∈ maximalIdeal (R ⧸ I) := hts ▸ Submodule.subset_span hy
    by_contra hn
    have hu : IsUnit (g y) := not_not.mp fun h => hn ((mem_maximalIdeal _).mpr h)
    exact (mem_maximalIdeal _).mp hy' (hg y ▸ hu.map (Ideal.Quotient.mk I))
  have hmap : (Ideal.span (s : Set R)).map (Ideal.Quotient.mk I) = maximalIdeal (R ⧸ I) := by
    rw [Ideal.map_span, hs, Finset.coe_image, ← Set.image_comp,
      show (Ideal.Quotient.mk I) ∘ g = id from funext hg, Set.image_id]
    exact hts
  have hle : maximalIdeal R ≤ Ideal.span (s : Set R) ⊔ maximalIdeal R • maximalIdeal R := by
    intro a ha
    have h1 : Ideal.Quotient.mk I a ∈ (Ideal.span (s : Set R)).map (Ideal.Quotient.mk I) :=
      hmap ▸ hmk a ha
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker] at h1
    exact sup_le_sup_left (hI.trans (le_of_eq (by rw [pow_two, Ideal.smul_eq_mul]))) _ h1
  have hm : maximalIdeal R = Ideal.span (s : Set R) :=
    le_antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle) (Ideal.span_le.mpr hsm)
  rw [hm, ← htc]
  refine (Submodule.spanFinrank_span_le_ncard_of_finite s.finite_toSet).trans ?_
  rw [Set.ncard_coe_finset]
  exact Finset.card_image_le

theorem exists_span_eq_of_isRegularLocalRing_quotient (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] (I : Ideal R) [IsRegularLocalRing (R ⧸ I)],
      ringKrullDim R = ringKrullDim (R ⧸ I) + n →
        ∃ f : Fin n → R, (∀ j, f j ∈ I) ∧ I = Ideal.span (Set.range f) := by
  induction n with
  | zero =>
    intro R _ _ I _ hd
    refine ⟨Fin.elim0, fun j => j.elim0, ?_⟩
    rw [Set.range_eq_empty, Ideal.span_empty]
    have := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain (R := R)
    by_contra hI
    obtain ⟨y, hyI, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hy0)
    have h2 : ringKrullDim (R ⧸ I) ≤ ringKrullDim (R ⧸ Ideal.span {y}) :=
      ringKrullDim_le_of_surjective (Ideal.Quotient.factor ((Ideal.span_singleton_le_iff_mem I).mpr hyI))
        (Ideal.Quotient.factor_surjective _)
    have hR : ringKrullDim R = ((maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
      ((isRegularLocalRing_iff R).mp inferInstance).symm
    rw [Nat.cast_zero, add_zero] at hd
    have h3 : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) + 1 ≤ (maximalIdeal R).spanFinrank := by
      rw [← hR]
      calc ringKrullDim R + 1 = ringKrullDim (R ⧸ I) + 1 := by rw [hd]
        _ ≤ ringKrullDim (R ⧸ Ideal.span {y}) + 1 := by gcongr
        _ ≤ ringKrullDim R := h1
    have h4 : (maximalIdeal R).spanFinrank + 1 ≤ (maximalIdeal R).spanFinrank := by exact_mod_cast h3
    omega
  | succ n ih =>
    intro R _ _ I _ hd
    have hR : ringKrullDim R = ((maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
      ((isRegularLocalRing_iff R).mp inferInstance).symm
    have hRI : ringKrullDim (R ⧸ I) = ((maximalIdeal (R ⧸ I)).spanFinrank : WithBot ℕ∞) :=
      ((isRegularLocalRing_iff (R ⧸ I)).mp inferInstance).symm
    have hdd : (maximalIdeal R).spanFinrank = (maximalIdeal (R ⧸ I)).spanFinrank + (n + 1) := by
      rw [hR, hRI] at hd
      exact_mod_cast hd
    have hItop : I ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
    have hIm : I ≤ maximalIdeal R := le_maximalIdeal hItop
    obtain ⟨x, hxI, hx2⟩ : ∃ x ∈ I, x ∉ maximalIdeal R ^ 2 := by
      by_contra h
      push Not at h
      have := spanFinrank_maximalIdeal_le_quotient_of_le_sq (I := I) h
      omega
    have hxm : x ∈ maximalIdeal R := hIm hxI
    have hxI' : Ideal.span {x} ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr hxI
    have hne : Ideal.span {x} ≠ ⊤ := fun h => hItop (top_le_iff.mp (h ▸ hxI'))
    have : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing (R ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    obtain ⟨hreg, hdim⟩ := GroundTheory.Arith.SchemeCoh.isRegularLocalRing_quotient hxm hx2
    have := hreg
    let e := DoubleQuot.quotQuotEquivQuotOfLE hxI'
    have : IsRegularLocalRing ((R ⧸ Ideal.span {x}) ⧸ I.map (Ideal.Quotient.mk (Ideal.span {x}))) :=
      IsRegularLocalRing.of_ringEquiv e.symm
    have hR' : ringKrullDim (R ⧸ Ideal.span {x}) =
        ((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞) :=
      ((isRegularLocalRing_iff _).mp inferInstance).symm
    have hd' : ringKrullDim (R ⧸ Ideal.span {x}) =
        ringKrullDim ((R ⧸ Ideal.span {x}) ⧸ I.map (Ideal.Quotient.mk (Ideal.span {x}))) + n := by
      rw [ringKrullDim_eq_of_ringEquiv e, hRI, hR']
      rw [hR, hR'] at hdim
      have h5 : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 = (maximalIdeal R).spanFinrank := by
        exact_mod_cast hdim
      have h6 : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank = (maximalIdeal (R ⧸ I)).spanFinrank + n := by
        omega
      rw [h6]
      push_cast
      rfl
    obtain ⟨f', hf'I, hf'⟩ := ih _ _ hd'
    have hlift : ∀ j, ∃ a ∈ I, Ideal.Quotient.mk (Ideal.span {x}) a = f' j := fun j =>
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp (hf'I j)
    choose g hgI hg using hlift
    refine ⟨(Fin.cons x g : Fin (n + 1) → R), Fin.forall_fin_succ.mpr ⟨by simpa using hxI, fun i => by simpa using hgI i⟩, ?_⟩
    rw [Fin.range_cons, Ideal.span_insert]
    have hcomap : I = (I.map (Ideal.Quotient.mk (Ideal.span {x}))).comap (Ideal.Quotient.mk (Ideal.span {x})) := by
      rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_eq_left.mpr hxI']
    have hrange : Set.range f' = Ideal.Quotient.mk (Ideal.span {x}) '' Set.range g := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext hg).symm
    rw [hcomap, hf', hrange, ← Ideal.map_span, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, sup_comm]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFibreDiscriminantHolomorphic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def FibreDiscriminantHolomorphic.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ))
    (N : ℕ) (l : (σ → ℂ) →L[ℂ] ℂ),
    IsOpen D → Set.MapsTo A Y D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K}) →
    (∀ x ∈ Y, ∀ V ∈ 𝓝 x, A '' (Y ∩ V) ∈ 𝓝 (A x)) →
    IsGenericCountCover Y A D N →
    AnalyticOnNhd ℂ (fibreDiscr Y A l N) D

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteGermProjectionOpenAt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def FiniteGermProjectionOpenAt.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X x →
    (∃ W ∈ 𝓝 x, ∀ x' ∈ X ∩ W, A x' = A x → x' = x) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A x) → (∀ᶠ z in 𝓝 x, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A x), h y = 0) →
    ∀ V ∈ 𝓝 x, A '' (X ∩ V) ∈ 𝓝 (A x)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteModuloEliminate
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable def zeroCoordinate {τ : Type} [DecidableEq τ] (c : τ) : (τ → ℂ) →L[ℂ] (τ → ℂ) :=
  ContinuousLinearMap.pi fun c' => if c' = c then 0 else ContinuousLinearMap.proj c'

theorem zeroCoordinate_apply {τ : Type} [DecidableEq τ] (c : τ) (y : τ → ℂ) (c' : τ) :
    zeroCoordinate c y c' = if c' = c then 0 else y c' := by
  by_cases h : c' = c <;> simp [zeroCoordinate, h]

def FiniteModuloEliminate.Statement : Prop :=
  ∀ (σ τ : Type) [Fintype σ] [Fintype τ] [DecidableEq τ] (x : σ → ℂ) (k : ℕ)
    (f : Fin k → (σ → ℂ) → ℂ) (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) (c : τ),
    (∀ i, AnalyticAt ℂ (f i) x) → IsFiniteModuloOver x f L →
    (∃ (r : ℕ) (h : Fin k → (σ → ℂ) → ℂ) (h' : τ → (σ → ℂ) → ℂ),
      (∀ i, AnalyticAt ℂ (h i) x) ∧ (∀ c', AnalyticAt ℂ (h' c') x) ∧
      ∀ᶠ z in 𝓝 x, (L z c - L x c) ^ r =
        ∑ i, h i z * f i z + ∑ c', h' c' z * (zeroCoordinate c (L z) c' - zeroCoordinate c (L x) c')) →
    IsFiniteModuloOver x f ((zeroCoordinate c).comp L)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionCluster
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial Topology

noncomputable section

def FiniteProjectionCluster.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (w : Fin n → ℂ)
    (U : Set (Fin n → ℂ)),
    IsFiniteProjection J A → w ∈ zeroSet J → U ∈ 𝓝 w →
      ∃ (r : ℝ) (N M : Set (Fin n → ℂ)), 0 < r ∧ IsOpen N ∧ IsOpen M ∧ w ∈ N ∧ N ⊆ U ∧
        Disjoint N M ∧
        zeroSet J ∩ {x | A.mulVec x ∈ Metric.ball (A.mulVec w) r} ⊆ N ∪ M ∧
        Bornology.IsBounded (zeroSet J ∩ {x | A.mulVec x ∈ Metric.ball (A.mulVec w) r})

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionProperBall
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def FiniteProjectionProperBall.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    ∀ U ∈ 𝓝 w, ∃ ρ : ℝ, 0 < ρ ∧ ∃ r : ℝ, 0 < r ∧ Metric.ball w ρ ⊆ U ∧
      ∀ K ⊆ Metric.ball (A w) r, IsCompact K →
        IsCompact {x | x ∈ X ∩ Metric.ball w ρ ∧ A x ∈ K}

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionsGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def FiniteProjectionsContainOpen.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
      ∃ W : Set (Matrix (Fin d) (Fin n) ℂ), IsZariskiOpen W ∧ W.Nonempty ∧
        W ⊆ {A | IsFiniteProjection J A}

def FiniteProjectionsGeneric.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
      (∃ W : Set (Matrix (Fin d) (Fin n) ℂ), IsZariskiOpen W ∧ W.Nonempty ∧
        W ⊆ {A | IsFiniteProjection J A}) ∧
      (∀ D : Set (Matrix (Fin d) (Fin n) ℂ), D ⊆ orthoRows d n → orthoRows d n ⊆ closure D →
        ∃ A ∈ D, IsFiniteProjection J A) ∧
      (∀ (m : ℕ) (F : Fin m → Matrix.unitaryGroup (Fin n) ℂ),
        ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ (k : Fin m) (s : Fin d ↪ Fin n),
          IsFiniteProjection J (((F k : Matrix (Fin n) (Fin n) ℂ) * U).submatrix s id))

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFlatLocalRegularElement
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

def FlatLocalRegularElement.Statement : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B],
    IsNoetherianRing A → IsNoetherianRing B → IsLocalHom (algebraMap A B) →
    ∀ (M : Type) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M],
      Module.Finite B M → Module.Flat A M →
      ∀ y ∈ maximalIdeal B,
        IsSMulRegular (M ⧸ ((maximalIdeal A).map (algebraMap A B) • (⊤ : Submodule B M))) y →
        IsSMulRegular M y ∧ Module.Flat A (QuotSMulTop y M)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

