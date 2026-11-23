module

public import Mathlib
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal
public import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.Bundle0001

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealEtaleBaseChange
section
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

private def derivationCompAlgebraMap (k : Type*) [CommRing k] (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T] (D : Derivation k T T) :
    Derivation k S T :=
  Derivation.mk' (D.toLinearMap.comp (IsScalarTower.toAlgHom k S T).toLinearMap) (by
    intro a b
    show D (algebraMap S T (a * b)) = a • D (algebraMap S T b) + b • D (algebraMap S T a)
    rw [map_mul, D.leibniz, smul_eq_mul, smul_eq_mul, Algebra.smul_def, Algebra.smul_def])

private theorem derivation_comp_algebraMap_apply (k : Type*) [CommRing k] (S : Type*) [CommRing S]
    (T : Type*) [CommRing T] [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    (D : Derivation k T T) (s : S) :
    derivationCompAlgebraMap k S T D s = D (algebraMap S T s) := rfl

private def algebraMapCompDerivation (k : Type*) [CommRing k] (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T] (D : Derivation k S S) :
    Derivation k S T :=
  Derivation.mk' ((IsScalarTower.toAlgHom k S T).toLinearMap.comp D.toLinearMap) (by
    intro a b
    show algebraMap S T (D (a * b)) = a • algebraMap S T (D b) + b • algebraMap S T (D a)
    rw [D.leibniz, map_add (f := _), smul_eq_mul, smul_eq_mul, map_mul, map_mul, Algebra.smul_def,
      Algebra.smul_def])

private theorem algebraMap_comp_derivation_apply (k : Type*) [CommRing k] (S : Type*) [CommRing S]
    (T : Type*) [CommRing T] [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    (D : Derivation k S S) (s : S) :
    algebraMapCompDerivation k S T D s = algebraMap S T (D s) := rfl

theorem derivation_ext_of_coord (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
    [Algebra (MvPolynomial ι k) S] [Algebra k S] [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    (M : Type*) [AddCommGroup M] [Module k M] [Module S M] [IsScalarTower k S M]
    (D₁ D₂ : Derivation k S M)
    (h : ∀ i : ι, D₁ (coord k ι S i) = D₂ (coord k ι S i)) : D₁ = D₂ := by
  have key : D₁.liftKaehlerDifferential = D₂.liftKaehlerDifferential := by
    refine (basisKaehler k ι S).ext ?_
    intro i
    rw [basisKaehler_apply, Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D]
    exact h i
  refine Derivation.ext fun x => ?_
  rw [← Derivation.liftKaehlerDifferential_comp_D D₁ x,
    ← Derivation.liftKaehlerDifferential_comp_D D₂ x, key]

theorem partialDeriv_inr_algebraMap (k : Type*) [CommRing k] (ι : Type*) (κ : Type*)
    (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    [Algebra k T] [Algebra (MvPolynomial (ι ⊕ κ) k) T]
    [IsScalarTower k (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra S T] [IsScalarTower k S T]
    (hcoord : ∀ i : ι, algebraMap S T (coord k ι S i) = coord k (ι ⊕ κ) T (Sum.inl i))
    (j : κ) (s : S) :
    partialDeriv k (ι ⊕ κ) T (Sum.inr j) (algebraMap S T s) = 0 := by
  have key : derivationCompAlgebraMap k S T (partialDeriv k (ι ⊕ κ) T (Sum.inr j)) = 0 := by
    refine derivation_ext_of_coord k ι S T _ _ ?_
    intro i
    rw [derivation_comp_algebraMap_apply, hcoord i,
      partialDeriv_coord_of_ne k (ι ⊕ κ) T (Sum.inr j) (Sum.inl i) (by simp)]
    have h0 : ((0 : Derivation k S T)) (coord k ι S i) = 0 := rfl
    rw [h0]
  have h2 := DFunLike.congr_fun key s
  rw [derivation_comp_algebraMap_apply] at h2
  have h0 : ((0 : Derivation k S T)) s = 0 := rfl
  rw [h0] at h2
  exact h2

theorem partialDeriv_inl_algebraMap (k : Type*) [CommRing k] (ι : Type*) (κ : Type*)
    [DecidableEq ι] [DecidableEq κ]
    (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    [Algebra k T] [Algebra (MvPolynomial (ι ⊕ κ) k) T]
    [IsScalarTower k (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra S T] [IsScalarTower k S T]
    (hcoord : ∀ i : ι, algebraMap S T (coord k ι S i) = coord k (ι ⊕ κ) T (Sum.inl i))
    (i : ι) (s : S) :
    partialDeriv k (ι ⊕ κ) T (Sum.inl i) (algebraMap S T s)
      = algebraMap S T (partialDeriv k ι S i s) := by
  have key : derivationCompAlgebraMap k S T (partialDeriv k (ι ⊕ κ) T (Sum.inl i))
      = algebraMapCompDerivation k S T (partialDeriv k ι S i) := by
    refine derivation_ext_of_coord k ι S T _ _ ?_
    intro j
    rw [derivation_comp_algebraMap_apply, algebraMap_comp_derivation_apply, hcoord j]
    by_cases hij : i = j
    · subst hij
      rw [partialDeriv_coord_self, partialDeriv_coord_self, map_one]
    · rw [partialDeriv_coord_of_ne k (ι ⊕ κ) T (Sum.inl i) (Sum.inl j) (by simpa using hij),
        partialDeriv_coord_of_ne k ι S i j hij, map_zero]
  have h2 := DFunLike.congr_fun key s
  rw [derivation_comp_algebraMap_apply, algebraMap_comp_derivation_apply] at h2
  exact h2

theorem map_derivIdeal_sum (k : Type*) [CommRing k] (ι : Type*) (κ : Type*)
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    [Algebra k T] [Algebra (MvPolynomial (ι ⊕ κ) k) T]
    [IsScalarTower k (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra S T] [IsScalarTower k S T]
    (hcoord : ∀ i : ι, algebraMap S T (coord k ι S i) = coord k (ι ⊕ κ) T (Sum.inl i))
    (J : Ideal S) :
    Ideal.map (algebraMap S T) (derivIdeal k J) = derivIdeal k (Ideal.map (algebraMap S T) J) := by
  have key1 : ∀ (D : Derivation k S S) (y : S), y ∈ J →
      algebraMap S T (D y) ∈ derivIdeal k (Ideal.map (algebraMap S T) J) := by
    intro D y hy
    have hsp : D ∈ Submodule.span S (Set.range (partialDeriv k ι S)) := by
      rw [span_range_partialDeriv]
      exact Submodule.mem_top
    induction hsp using Submodule.span_induction with
    | mem D hD =>
        obtain ⟨i, rfl⟩ := hD
        rw [← partialDeriv_inl_algebraMap k ι κ S T hcoord i y]
        exact derivation_apply_mem_derivIdeal k _ _ (Ideal.mem_map_of_mem _ hy)
    | zero =>
        have h0 : ((0 : Derivation k S S)) y = 0 := rfl
        rw [h0, map_zero]
        exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
        have h0 : (a + b) y = a y + b y := rfl
        rw [h0, map_add (f := _)]
        exact Ideal.add_mem _ ha hb
    | smul c a _ ha =>
        have h0 : (c • a) y = c * a y := rfl
        rw [h0, map_mul]
        exact Ideal.mul_mem_left _ _ ha
  have key2 : ∀ (D' : Derivation k T T) (y : S), y ∈ J →
      D' (algebraMap S T y) ∈ Ideal.map (algebraMap S T) (derivIdeal k J) := by
    intro D' y hy
    have hsp : D' ∈ Submodule.span T (Set.range (partialDeriv k (ι ⊕ κ) T)) := by
      rw [span_range_partialDeriv]
      exact Submodule.mem_top
    induction hsp using Submodule.span_induction with
    | mem D hD =>
        obtain ⟨x, rfl⟩ := hD
        cases x with
        | inl i =>
            rw [partialDeriv_inl_algebraMap k ι κ S T hcoord i y]
            exact Ideal.mem_map_of_mem _
              (derivation_apply_mem_derivIdeal k J (partialDeriv k ι S i) hy)
        | inr j =>
            rw [partialDeriv_inr_algebraMap k ι κ S T hcoord j y]
            exact Submodule.zero_mem _
    | zero =>
        have h0 : ((0 : Derivation k T T)) (algebraMap S T y) = 0 := rfl
        rw [h0]
        exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
        have h0 : (a + b) (algebraMap S T y)
            = a (algebraMap S T y) + b (algebraMap S T y) := rfl
        rw [h0]
        exact Ideal.add_mem _ ha hb
    | smul c a _ ha =>
        have h0 : (c • a) (algebraMap S T y) = c * a (algebraMap S T y) := rfl
        rw [h0]
        exact Ideal.mul_mem_left _ _ ha
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap, derivIdeal_le_iff]
    refine ⟨fun y hy => Ideal.mem_comap.mpr (le_derivIdeal k _ (Ideal.mem_map_of_mem _ hy)), ?_⟩
    intro D y hy
    exact Ideal.mem_comap.mpr (key1 D y hy)
  · rw [derivIdeal_le_iff]
    refine ⟨Ideal.map_mono (le_derivIdeal k J), ?_⟩
    intro D' z hz
    have hspan : Ideal.map (algebraMap S T) J
        = Ideal.span ((algebraMap S T) '' (J : Set S)) := by
      rw [← Ideal.map_span, Ideal.span_eq]
    rw [hspan] at hz
    refine derivation_apply_mem_of_mem_span D' ?_ ?_ hz
    · rw [← hspan]
      exact Ideal.map_mono (le_derivIdeal k J)
    · rintro g ⟨y, hy, rfl⟩
      exact key2 D' y hy

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealLocalization
section
universe u v w

namespace FunctorialResolution.EmbeddedResolution

variable {k : Type u} {S : Type v} {S' : Type w}

theorem map_derivIdeal_le [CommRing k] [CommRing S] [CommRing S'] [Algebra k S] [Algebra S S']
    [Algebra k S'] [IsScalarTower k S S'] (M : Submonoid S) [IsLocalization M S']
    (J : Ideal S) :
    Ideal.map (algebraMap S S') (derivIdeal k J) ≤
      derivIdeal k (Ideal.map (algebraMap S S') J) := by
  rw [Ideal.map_le_iff_le_comap, derivIdeal_le_iff]
  constructor
  · intro x hx
    refine Ideal.mem_comap.mpr ?_
    exact le_derivIdeal k _ (Ideal.mem_map_of_mem (algebraMap S S') hx)
  · intro D x hx
    refine Ideal.mem_comap.mpr ?_
    have h := derivation_apply_mem_derivIdeal k (Ideal.map (algebraMap S S') J)
      (D.mapToLocalization (S' := S') M) (Ideal.mem_map_of_mem (algebraMap S S') hx)
    rwa [Derivation.mapToLocalization_algebraMap] at h

private theorem derivation_algebraMap_mem_map_derivIdeal [CommRing k] [CommRing S] [CommRing S'] [Algebra k S]
    [Algebra S S'] [Algebra k S'] [IsScalarTower k S S'] (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)] (J : Ideal S)
    (D : Derivation k S' S') {a : S} (ha : a ∈ J) :
    D (algebraMap S S' a) ∈ Ideal.map (algebraMap S S') (derivIdeal k J) := by
  obtain ⟨m, D₀, hm⟩ := Derivation.exists_derivation_mul_eq_of_isLocalization (R := k) M D
  refine (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S' m)).mp ?_
  rw [hm a]
  exact Ideal.mem_map_of_mem _ (derivation_apply_mem_derivIdeal k J D₀ ha)

theorem derivIdeal_map_le [CommRing k] [CommRing S] [CommRing S'] [Algebra k S] [Algebra S S']
    [Algebra k S'] [IsScalarTower k S S'] (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)] (J : Ideal S) :
    derivIdeal k (Ideal.map (algebraMap S S') J) ≤
      Ideal.map (algebraMap S S') (derivIdeal k J) := by
  rw [derivIdeal_le_iff]
  refine ⟨Ideal.map_mono (le_derivIdeal k J), ?_⟩
  intro D x hx
  rw [IsLocalization.mem_map_algebraMap_iff M S'] at hx
  obtain ⟨⟨a, m⟩, hax⟩ := hx
  have h1 : D (x * algebraMap S S' (m : S)) = D (algebraMap S S' (a : S)) := by rw [hax]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h1
  have hA : D (algebraMap S S' (a : S)) ∈ Ideal.map (algebraMap S S') (derivIdeal k J) :=
    derivation_algebraMap_mem_map_derivIdeal M J D a.2
  have hmem1 : algebraMap S S' (m : S) * D (algebraMap S S' (a : S)) ∈
      Ideal.map (algebraMap S S') (derivIdeal k J) := Ideal.mul_mem_left _ _ hA
  have hmem2 : algebraMap S S' (a : S) * D (algebraMap S S' (m : S)) ∈
      Ideal.map (algebraMap S S') (derivIdeal k J) :=
    Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (le_derivIdeal k J a.2))
  have h3 : algebraMap S S' (m : S) * (algebraMap S S' (m : S) * D x) ∈
      Ideal.map (algebraMap S S') (derivIdeal k J) := by
    have h2 : algebraMap S S' (m : S) * (algebraMap S S' (m : S) * D x) =
        algebraMap S S' (m : S) * D (algebraMap S S' (a : S)) -
          algebraMap S S' (a : S) * D (algebraMap S S' (m : S)) := by
      linear_combination (algebraMap S S' (m : S)) * h1 - (D (algebraMap S S' (m : S))) * hax
    rw [h2]
    exact sub_mem hmem1 hmem2
  exact (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S' m)).mp
    ((Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S' m)).mp h3)

theorem map_derivIdeal [CommRing k] [CommRing S] [CommRing S'] [Algebra k S] [Algebra S S']
    [Algebra k S'] [IsScalarTower k S S'] (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)] (J : Ideal S) :
    Ideal.map (algebraMap S S') (derivIdeal k J) = derivIdeal k (Ideal.map (algebraMap S S') J) :=
  le_antisymm (map_derivIdeal_le M J) (derivIdeal_map_le M J)

theorem map_derivIdeal_away [CommRing k] [CommRing S] [CommRing S'] [Algebra k S] [Algebra S S']
    [Algebra k S'] [IsScalarTower k S S'] (g : S) [IsLocalization.Away g S']
    [Module.FinitePresentation S (KaehlerDifferential k S)] (J : Ideal S) :
    Ideal.map (algebraMap S S') (derivIdeal k J) = derivIdeal k (Ideal.map (algebraMap S S') J) :=
  map_derivIdeal (Submonoid.powers g) J

end FunctorialResolution.EmbeddedResolution
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdeal
section
namespace FunctorialResolution.EmbeddedResolution

variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]

def tangentDerivations (P : Ideal S) : Submodule S (Derivation k S S) where
  carrier := {D : Derivation k S S | ∀ x ∈ P, D x ∈ P}
  add_mem' := by
    intro D D' hD hD' x hx
    have h := P.add_mem (hD x hx) (hD' x hx)
    simpa using h
  zero_mem' := by
    intro x _
    simp
  smul_mem' := by
    intro a D hD x hx
    have h := Ideal.mul_mem_left P a (hD x hx)
    simpa [smul_eq_mul] using h

theorem mem_tangentDerivations (P : Ideal S) (D : Derivation k S S) :
    D ∈ tangentDerivations k P ↔ ∀ x ∈ P, D x ∈ P := Iff.rfl

theorem smul_mem_tangentDerivations (P : Ideal S) {p : S} (hp : p ∈ P)
    (D : Derivation k S S) : p • D ∈ tangentDerivations k P := by
  rw [mem_tangentDerivations]
  intro x _
  have h := Ideal.mul_mem_right (D x) P hp
  simpa [smul_eq_mul] using h

theorem mem_tangentDerivations_span_singleton (x : S) (D : Derivation k S S) :
    D ∈ tangentDerivations k (Ideal.span ({x} : Set S)) ↔
      D x ∈ Ideal.span ({x} : Set S) := by
  rw [mem_tangentDerivations]
  constructor
  · intro hD
    exact hD x (Ideal.subset_span (Set.mem_singleton x))
  · intro hD y hy
    refine derivation_apply_mem_of_mem_span D le_rfl ?_ hy
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hD

def logDerivIdeal (P J : Ideal S) : Ideal S :=
  J ⊔ Ideal.span {x : S | ∃ D ∈ tangentDerivations k P, ∃ y ∈ J, D y = x}

private theorem logDerivIdeal_eq_sup_span (P J : Ideal S) :
    logDerivIdeal k P J =
      J ⊔ Ideal.span {x : S | ∃ D ∈ tangentDerivations k P, ∃ y ∈ J, D y = x} := rfl

theorem le_logDerivIdeal (P J : Ideal S) : J ≤ logDerivIdeal k P J := by
  rw [logDerivIdeal_eq_sup_span]
  exact le_sup_left

theorem derivation_apply_mem_logDerivIdeal (P J : Ideal S) (D : Derivation k S S)
    (hD : D ∈ tangentDerivations k P) {x : S} (hx : x ∈ J) :
    D x ∈ logDerivIdeal k P J := by
  rw [logDerivIdeal_eq_sup_span]
  exact Submodule.mem_sup_right (Ideal.subset_span ⟨D, hD, x, hx, rfl⟩)

theorem logDerivIdeal_le_iff (P J K : Ideal S) :
    logDerivIdeal k P J ≤ K ↔
      J ≤ K ∧ ∀ D ∈ tangentDerivations k P, ∀ x ∈ J, D x ∈ K := by
  rw [logDerivIdeal_eq_sup_span, sup_le_iff, Ideal.span_le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun D hD x hx => h2 ⟨D, hD, x, hx, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro x ⟨D, hD, y, hy, rfl⟩
    exact h2 D hD y hy

theorem logDerivIdeal_mono (P : Ideal S) : Monotone (logDerivIdeal k P : Ideal S → Ideal S) := by
  intro I J h
  rw [logDerivIdeal_le_iff]
  refine ⟨h.trans (le_logDerivIdeal k P J), fun D hD x hx => ?_⟩
  exact derivation_apply_mem_logDerivIdeal k P J D hD (h hx)

theorem logDerivIdeal_le_logDerivIdeal (P : Ideal S) {I J : Ideal S} (h : I ≤ J) :
    logDerivIdeal k P I ≤ logDerivIdeal k P J :=
  logDerivIdeal_mono k P h

theorem logDerivIdeal_le_derivIdeal (P J : Ideal S) :
    logDerivIdeal k P J ≤ derivIdeal k J := by
  rw [logDerivIdeal_le_iff]
  refine ⟨le_derivIdeal k J, fun D _ x hx => ?_⟩
  exact derivation_apply_mem_derivIdeal k J D hx

theorem logDerivIdeal_top_eq_derivIdeal (J : Ideal S) :
    logDerivIdeal k (⊤ : Ideal S) J = derivIdeal k J := by
  refine le_antisymm (logDerivIdeal_le_derivIdeal k ⊤ J) ?_
  rw [derivIdeal_le_iff]
  refine ⟨le_logDerivIdeal k ⊤ J, fun D x hx => ?_⟩
  refine derivation_apply_mem_logDerivIdeal k ⊤ J D ?_ hx
  rw [mem_tangentDerivations]
  intro y _
  exact Submodule.mem_top

theorem logDerivIdeal_iSup_le {ι : Sort*} (P : Ideal S) (J : ι → Ideal S) :
    logDerivIdeal k P (⨆ i, J i) ≤ ⨆ i, logDerivIdeal k P (J i) := by
  rw [logDerivIdeal_le_iff]
  refine ⟨iSup_mono fun i => le_logDerivIdeal k P (J i), ?_⟩
  intro D hD x hx
  refine Submodule.iSup_induction
    (motive := fun z : S => D z ∈ ⨆ i, logDerivIdeal k P (J i)) J hx ?_ ?_ ?_
  · intro i y hy
    exact le_iSup (fun i => logDerivIdeal k P (J i)) i
      (derivation_apply_mem_logDerivIdeal k P (J i) D hD hy)
  · simpa only [map_zero] using Submodule.zero_mem (⨆ i, logDerivIdeal k P (J i))
  · intro a b ha hb
    simpa only [map_add (f := _)] using Submodule.add_mem (⨆ i, logDerivIdeal k P (J i)) ha hb

def logDerivIdealIterate (P : Ideal S) : ℕ → Ideal S → Ideal S
  | 0, J => J
  | r + 1, J => logDerivIdeal k P (logDerivIdealIterate P r J)

theorem logDerivIdealIterate_zero (P J : Ideal S) : logDerivIdealIterate k P 0 J = J := rfl

theorem logDerivIdealIterate_succ (P : Ideal S) (r : ℕ) (J : Ideal S) :
    logDerivIdealIterate k P (r + 1) J = logDerivIdeal k P (logDerivIdealIterate k P r J) := rfl

theorem logDerivIdealIterate_add (P : Ideal S) (r s : ℕ) (J : Ideal S) :
    logDerivIdealIterate k P (r + s) J =
      logDerivIdealIterate k P r (logDerivIdealIterate k P s J) := by
  induction r with
  | zero => rw [Nat.zero_add, logDerivIdealIterate_zero]
  | succ r ih => rw [Nat.succ_add, logDerivIdealIterate_succ, logDerivIdealIterate_succ, ih]

theorem le_logDerivIdealIterate (P : Ideal S) (r : ℕ) (J : Ideal S) :
    J ≤ logDerivIdealIterate k P r J := by
  induction r with
  | zero => exact (logDerivIdealIterate_zero k P J).ge
  | succ r ih =>
      rw [logDerivIdealIterate_succ]
      exact ih.trans (le_logDerivIdeal k P _)

theorem logDerivIdealIterate_mono (P : Ideal S) (r : ℕ) :
    Monotone (logDerivIdealIterate k P r : Ideal S → Ideal S) := by
  induction r with
  | zero =>
      intro I J h
      rw [logDerivIdealIterate_zero, logDerivIdealIterate_zero]
      exact h
  | succ r ih =>
      intro I J h
      rw [logDerivIdealIterate_succ, logDerivIdealIterate_succ]
      exact logDerivIdeal_mono k P (ih h)

theorem logDerivIdealIterate_le_of_le (P : Ideal S) {r r' : ℕ} (h : r ≤ r') (J : Ideal S) :
    logDerivIdealIterate k P r J ≤ logDerivIdealIterate k P r' J := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm r d, logDerivIdealIterate_add]
  exact le_logDerivIdealIterate k P d _

theorem logDerivIdealIterate_top_eq_derivIdealIterate (r : ℕ) (J : Ideal S) :
    logDerivIdealIterate k (⊤ : Ideal S) r J = derivIdealIterate k r J := by
  induction r with
  | zero => rw [logDerivIdealIterate_zero, derivIdealIterate_zero]
  | succ r ih =>
      rw [logDerivIdealIterate_succ, derivIdealIterate_succ, ih, logDerivIdeal_top_eq_derivIdeal]

theorem logDerivIdealIterate_iSup_le {ι : Sort*} (P : Ideal S) (r : ℕ) (J : ι → Ideal S) :
    logDerivIdealIterate k P r (⨆ i, J i) ≤ ⨆ i, logDerivIdealIterate k P r (J i) := by
  induction r with
  | zero => exact le_rfl
  | succ r ih =>
      rw [logDerivIdealIterate_succ]
      refine le_trans (logDerivIdeal_mono k P ih) ?_
      refine le_trans (logDerivIdeal_iSup_le k P fun i => logDerivIdealIterate k P r (J i)) ?_
      exact iSup_mono fun i => le_of_eq (logDerivIdealIterate_succ k P r (J i)).symm

end FunctorialResolution.EmbeddedResolution
end

