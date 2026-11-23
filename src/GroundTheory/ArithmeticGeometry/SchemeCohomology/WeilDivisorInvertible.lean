module

public import Mathlib
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisorSheaf
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.InvertibleSheaf

@[expose] public section

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite MonoidalCategory

universe u

variable {X : Scheme.{u}}

lemma nonempty_inf_of_mem [IsIntegral X] {V W : X.Opens} (y : V) (w : W) : Nonempty (V ⊓ W : X.Opens) := by
  obtain ⟨z, hz⟩ := nonempty_preirreducible_inter V.isOpen W.isOpen ⟨y.1, y.2⟩ ⟨w.1, w.2⟩
  exact ⟨⟨z, hz⟩⟩

section RatVal

variable {P : PMod X} {U₀ : X.Opens} {s₀ : P.obj (op U₀)} (hs₀ : IsBasisOn P U₀ s₀)

noncomputable def coeffOn {V : X.Opens} (l : P.obj (op V)) : ringOn X (V ⊓ U₀) :=
  (Equiv.ofBijective _ (hs₀ (V ⊓ U₀) inf_le_right)).symm (resM P inf_le_left l)

lemma coeffOn_spec {V : X.Opens} (l : P.obj (op V)) :
    coeffOn hs₀ l • resM P inf_le_right s₀ = resM P inf_le_left l :=
  (Equiv.ofBijective _ (hs₀ (V ⊓ U₀) inf_le_right)).apply_symm_apply _

variable [IsIntegral X] [Nonempty U₀]

noncomputable def ratVal {V : X.Opens} (l : P.obj (op V)) (y : V) : X.functionField :=
  haveI := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  X.germToFunctionField (V ⊓ U₀) (coeffOn hs₀ l)

theorem ratVal_eq {V W : X.Opens} (hWV : W ≤ V) (hWU : W ≤ U₀) [Nonempty W]
    (l : P.obj (op V)) (a : ringOn X W) (ha : a • resM P hWU s₀ = resM P hWV l) (y : V) :
    ratVal hs₀ l y = X.germToFunctionField W a := by
  have hW' : W ≤ V ⊓ U₀ := le_inf hWV hWU
  have h1 := congrArg (resM P hW') (coeffOn_spec hs₀ l)
  rw [resM_smul_res, resM_resM] at h1
  have h2 : a = resR hW' (coeffOn hs₀ l) := (hs₀ W hWU).1 (ha.trans h1.symm)
  have := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  rw [h2]
  exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm

lemma ratVal_const {V : X.Opens} (l : P.obj (op V)) (y z : V) :
    ratVal hs₀ l y = ratVal hs₀ l z := by
  have := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  rw [ratVal_eq hs₀ inf_le_left inf_le_right l _ (coeffOn_spec hs₀ l) y,
    ratVal_eq hs₀ inf_le_left inf_le_right l _ (coeffOn_spec hs₀ l) z]

lemma ratVal_res {V W : X.Opens} (h : W ≤ V) (l : P.obj (op V)) (y : W) :
    ratVal hs₀ (resM P h l) y = ratVal hs₀ l ⟨y.1, h y.2⟩ := by
  have := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  have e := coeffOn_spec hs₀ (resM P h l)
  rw [resM_resM] at e
  rw [ratVal_eq hs₀ inf_le_left inf_le_right _ _ (coeffOn_spec hs₀ (resM P h l)) y,
    ratVal_eq hs₀ ((inf_le_left : W ⊓ U₀ ≤ W).trans h) inf_le_right l _ e]

lemma ratVal_smul {V : X.Opens} (a : ringOn X V) (l : P.obj (op V)) (y : V) :
    ratVal hs₀ (a • l) y = sectionValue V y a * ratVal hs₀ l y := by
  have := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  have e : (resR inf_le_left a * coeffOn hs₀ l) • resM P (inf_le_right : V ⊓ U₀ ≤ U₀) s₀ =
      resM P inf_le_left (a • l) := by
    rw [mul_smul, coeffOn_spec, resM_smul]
  rw [ratVal_eq hs₀ inf_le_left inf_le_right _ _ e y,
    ratVal_eq hs₀ inf_le_left inf_le_right l _ (coeffOn_spec hs₀ l) y]
  refine (map_mul (X.germToFunctionField (V ⊓ U₀)).hom
    (show Γ(X, V ⊓ U₀) from resR inf_le_left a) (show Γ(X, V ⊓ U₀) from coeffOn hs₀ l)).trans ?_
  congr 1
  refine Eq.trans ?_ (sectionValue_eq V y (show Γ(X, V) from a)).symm
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

end RatVal

section Invertible

variable [IsIntegral X]
  {P : PMod X} {U₀ : X.Opens} {s₀ : P.obj (op U₀)} (hs₀ : IsBasisOn P U₀ s₀) [Nonempty U₀]

lemma ratVal_ne_zero_of_isBasisOn {U : X.Opens} {s : P.obj (op U)} (hs : IsBasisOn P U s)
    (y : U) : ratVal hs₀ s y ≠ 0 := by
  intro h
  have := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  rw [ratVal_eq hs₀ inf_le_left inf_le_right s _ (coeffOn_spec hs₀ s) y] at h
  have hr : coeffOn hs₀ s = 0 := Scheme.germToFunctionField_injective X (U ⊓ U₀)
    (h.trans (map_zero _).symm)
  have hz : resM P (inf_le_left : U ⊓ U₀ ≤ U) s = 0 := by
    rw [← coeffOn_spec hs₀ s, hr, zero_smul]
  have hb := (hs (U ⊓ U₀) inf_le_left).1
  have h10 : (1 : ringOn X (U ⊓ U₀)) = 0 := hb (by simp only [hz, smul_zero])
  exact one_ne_zero (α := Γ(X, U ⊓ U₀)) h10


variable {L : X.Modules} (hL : IsInvertibleSheaf L)

noncomputable def basisOpen (x : X) : X.Opens := (hL x).choose

omit [IsIntegral X] in
lemma mem_basisOpen (x : X) : x ∈ basisOpen hL x := (hL x).choose_spec.choose

noncomputable def basisSec (x : X) : ((preMod X).obj L).obj (op (basisOpen hL x)) :=
  (hL x).choose_spec.choose_spec.choose

omit [IsIntegral X] in
lemma isBasisOn_basisSec (x : X) :
    IsBasisOn ((preMod X).obj L) (basisOpen hL x) (basisSec hL x) :=
  (hL x).choose_spec.choose_spec.choose_spec

instance (x : X) : Nonempty (basisOpen hL x) := ⟨⟨x, mem_basisOpen hL x⟩⟩

noncomputable def secVal {V : X.Opens} (l : ((preMod X).obj L).obj (op V)) (y : V) :
    X.functionField :=
  ratVal (isBasisOn_basisSec hL (Classical.arbitrary X)) l y

lemma secVal_basisSec_ne_zero (x : X) (y : basisOpen hL x) :
    secVal hL (basisSec hL x) y ≠ 0 :=
  ratVal_ne_zero_of_isBasisOn _ (isBasisOn_basisSec hL x) y

variable [IsNoetherian X] [IsLocallyFactorial X]

lemma ord_secVal_basisSec (Z : PrimeDivisor X) (x : X) (hZ : Z.point ∈ basisOpen hL x) :
    Z.ord (secVal hL (basisSec hL x) ⟨Z.point, hZ⟩) =
      Z.ord (secVal hL (basisSec hL Z.point) ⟨Z.point, mem_basisOpen hL Z.point⟩) := by
  set W := basisOpen hL x ⊓ basisOpen hL Z.point
  have hZW : Z.point ∈ W := ⟨hZ, mem_basisOpen hL Z.point⟩
  have : Nonempty W := ⟨⟨Z.point, hZW⟩⟩
  obtain ⟨u, hu⟩ := (isBasisOn_basisSec hL Z.point W inf_le_right).2
    (resM _ inf_le_left (basisSec hL x))
  obtain ⟨v, hv⟩ := (isBasisOn_basisSec hL x W inf_le_left).2
    (resM _ inf_le_right (basisSec hL Z.point))
  have hu' : u • resM _ inf_le_right (basisSec hL Z.point) = resM _ inf_le_left (basisSec hL x) :=
    hu
  have hv' : v • resM _ inf_le_left (basisSec hL x) = resM _ inf_le_right (basisSec hL Z.point) :=
    hv
  have huv : u * v = 1 := (isBasisOn_basisSec hL x W inf_le_left).1 (by
    change (u * v) • resM _ inf_le_left (basisSec hL x) = (1 : ringOn X W) • _
    rw [mul_smul, hv', hu', one_smul])
  have hunit : IsUnit (M := Γ(X, W)) u := isUnit_iff_exists_inv.mpr ⟨v, huv⟩
  have h1 := ratVal_smul (isBasisOn_basisSec hL (Classical.arbitrary X)) u
    (resM _ inf_le_right (basisSec hL Z.point)) ⟨Z.point, hZW⟩
  rw [hu', ratVal_res, ratVal_res] at h1
  change secVal hL (basisSec hL x) ⟨Z.point, hZ⟩ = sectionValue W ⟨Z.point, hZW⟩ u *
    secVal hL (basisSec hL Z.point) ⟨Z.point, mem_basisOpen hL Z.point⟩ at h1
  have hsv : sectionValue W ⟨Z.point, hZW⟩ u ≠ 0 := by
    intro h0
    apply hunit.ne_zero
    exact Scheme.germToFunctionField_injective X W
      ((sectionValue_eq _ _ _).symm.trans (h0.trans (map_zero _).symm))
  have h0 : Z.ord (sectionValue W ⟨Z.point, hZW⟩ u) = 0 :=
    (congrArg Z.ord (sectionValue_eq _ _ _)).trans (Z.ord_germToFunctionField_of_isUnit hZW hunit)
  rw [h1, Z.ord_mul hsv (secVal_basisSec_ne_zero hL _ _), h0, zero_add]

noncomputable def divisorOfInvertible : WeilDivisor X :=
  Finsupp.ofSupportFinite
    (fun Z => - Z.ord (secVal hL (basisSec hL Z.point) ⟨Z.point, mem_basisOpen hL Z.point⟩)) (by
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (basisOpen hL x : Set X))
      (fun x => (basisOpen hL x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, mem_basisOpen hL x⟩)
    refine (t.finite_toSet.biUnion fun x _ => PrimeDivisor.finite_ord_ne_zero
      (secVal_basisSec_ne_zero hL x ⟨x, mem_basisOpen hL x⟩)).subset ?_
    intro Z hZ
    obtain ⟨x, hx, hZx⟩ : ∃ x ∈ t, Z.point ∈ basisOpen hL x := by
      have := ht (Set.mem_univ Z.point)
      simpa using this
    refine Set.mem_biUnion hx ?_
    simp only [Function.mem_support, ne_eq, neg_eq_zero] at hZ
    change Z.ord (ratVal _ (basisSec hL x) ⟨x, mem_basisOpen hL x⟩) ≠ 0
    rw [ratVal_const _ (basisSec hL x) ⟨x, mem_basisOpen hL x⟩ ⟨Z.point, hZx⟩]
    change Z.ord (secVal hL (basisSec hL x) ⟨Z.point, hZx⟩) ≠ 0
    rwa [ord_secVal_basisSec hL Z x hZx])

end Invertible

end GroundTheory.Arith.SchemeCoh
