module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0061
public import Formalism.LocalToGlobal.Columns.Bundle0001
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0057
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0063
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrCharMemClosurePrimitiveRootCardStatement
section
open Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absIrrChar_mem_closure_primitiveRoot_card : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] {K : Type} [inst_2 : Field K] [inst_3 : CharZero K] (z : K), IsPrimitiveRoot z (Fintype.card G) → ∀ (χ : G → K), IsAbsIrrChar χ → ∀ g : G, χ g ∈ Subring.closure ({z} : Set K) := by
  first | exact @GlobalTheory.absIrrChar_mem_closure_primitiveRoot | exact GlobalTheory.absIrrChar_mem_closure_primitiveRoot | (intros; apply GlobalTheory.absIrrChar_mem_closure_primitiveRoot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrCharRealiseOfPrimitiveRootCardStatement
section
open Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absIrrChar_realise_of_primitiveRoot_card : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] {K : Type} [inst_2 : Field K] (σ : K →+* ℂ) (z : K), IsPrimitiveRoot z (Fintype.card G) → ∀ (ψ : G → ℂ), ψ ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ → ∃ χ : G → K, IsAbsIrrChar χ ∧ ∀ g, σ (χ g) = ψ g := by
  first | exact @GlobalTheory.BrauerRealise.absIrr_realise_of_isPrimitiveRoot | exact GlobalTheory.BrauerRealise.absIrr_realise_of_isPrimitiveRoot | (intros; apply GlobalTheory.BrauerRealise.absIrr_realise_of_isPrimitiveRoot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisToBdRPlusInjective
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris

theorem crisP_ker_dvd (l : ℕ) [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l) (hj : IsCrisP j)
    (x : Per.Acris l) (hx : j x = 0) : ∃ y : Per.Acris l, j y = 0 ∧ x = (l : Per.Acris l) * y := by
  obtain ⟨-, -, hd, hdv⟩ := acris_basic l
  obtain ⟨s, z, hs⟩ := hd x 1
  have h1 : (l : Per.Acris0 l) ∣ s := by
    refine _root_.GlobalTheory.MemLoc.dvd_of_forall_fil_add l s fun n => ?_
    obtain ⟨u, z', hu, e⟩ := _root_.GlobalTheory.MemLoc.fil_dense l j hj n x (by rw [hx]; exact zero_mem _)
    obtain ⟨w, hw⟩ := (hdv (s - u) 1).1 ⟨z' - z, by rw [map_sub]; linear_combination e - hs⟩
    exact ⟨u, w, by linear_combination hw, hu⟩
  obtain ⟨w, hw⟩ := h1
  have e : x = (l : Per.Acris l) * (algebraMap (Per.Acris0 l) (Per.Acris l) w + z) := by
    rw [hs, hw, map_mul, map_natCast]
    ring
  refine ⟨_, ?_, e⟩
  have hu : IsUnit (l : Per.BdRp l) := by
    have := (GlobalTheory.RingBasics.isUnit_l l).map (algebraMap (Per.AinfP l) (Per.BdRp l))
    rwa [map_natCast] at this
  rw [e, map_mul, map_natCast] at hx
  exact hu.mul_right_eq_zero.1 hx

theorem crisP_injective : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → Function.Injective j := by
  intro l _ j hj
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have h : ∀ n : ℕ, ∃ y : Per.Acris l, j y = 0 ∧ x = (l : Per.Acris l) ^ n * y := by
    intro n
    induction n with
    | zero => exact ⟨x, hx, by rw [pow_zero, one_mul]⟩
    | succ n ih =>
      obtain ⟨y, hy, e⟩ := ih
      obtain ⟨y', hy', e'⟩ := crisP_ker_dvd l j hj y hy
      exact ⟨y', hy', by rw [e, e', pow_succ, mul_assoc]⟩
  have hc := (acris_basic l).1
  refine hc.toIsHausdorff.haus x fun n => ?_
  obtain ⟨y, -, e⟩ := h n
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨y, e⟩

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.BdRField

theorem eq_pow_mul_unit {R : Type} [CommRing R] (π : R) (hsep : ∀ y : R, (∀ n : ℕ, π ^ n ∣ y) → y = 0)
    (hu : ∀ y : R, ¬ π ∣ y → IsUnit y) (y : R) (hy : y ≠ 0) : ∃ (n : ℕ) (u : R), IsUnit u ∧ y = π ^ n * u := by
  classical
  have h : ∃ n : ℕ, ¬ π ^ n ∣ y := by
    by_contra h
    push Not at h
    exact hy (hsep y h)
  have h0 : Nat.find h ≠ 0 := by
    intro e
    have := Nat.find_spec h
    rw [e] at this
    exact this (by simp)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h0
  have h1 : π ^ n ∣ y := by
    by_contra hc
    have := Nat.find_min' h hc
    omega
  obtain ⟨u, rfl⟩ := h1
  refine ⟨n, u, hu u ?_, rfl⟩
  intro hd
  have := Nat.find_spec h
  rw [hn] at this
  exact this (by rw [pow_succ]; exact mul_dvd_mul_left _ hd)

theorem general {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Nontrivial R] (M : Submonoid R)
    [IsLocalization M S] (π : R) (hreg : ∀ y : R, π * y = 0 → y = 0)
    (hsep : ∀ y : R, (∀ n : ℕ, π ^ n ∣ y) → y = 0)
    (hu : ∀ y : R, ¬ π ∣ y → IsUnit y) (hπ : π ∈ M) (hM : ∀ m ∈ M, ∃ n : ℕ, m ∣ π ^ n) :
    IsDomain R ∧ Function.Injective (algebraMap R S) ∧ IsField S ∧
      ∀ x : S, ∃ (n : ℕ) (y : R), x * algebraMap R S π ^ n = algebraMap R S y := by
  have hregn : ∀ (n : ℕ) (y : R), π ^ n * y = 0 → y = 0 := by
    intro n
    induction n with
    | zero => intro y h; simpa using h
    | succ n ih => intro y h; exact ih y (hreg _ (by rw [← h]; ring))
  have : NoZeroDivisors R := ⟨fun {a b} h => by
    by_cases ha : a = 0
    · exact Or.inl ha
    obtain ⟨n, u, hu', rfl⟩ := eq_pow_mul_unit π hsep hu a ha
    right
    rw [mul_assoc] at h
    exact (hu'.mul_right_eq_zero).1 (hregn n _ h)⟩
  have hD : IsDomain R := NoZeroDivisors.to_isDomain R
  have hle : M ≤ nonZeroDivisors R := by
    intro m hm
    obtain ⟨n, c, hc⟩ := hM m hm
    refine mem_nonZeroDivisors_of_ne_zero ?_
    rintro rfl
    have := hregn n 1 (by rw [hc]; ring)
    exact one_ne_zero this
  have hinj : Function.Injective (algebraMap R S) := IsLocalization.injective S hle
  have : Nontrivial S := hinj.nontrivial
  refine ⟨hD, hinj, ⟨exists_pair_ne S, mul_comm, ?_⟩, ?_⟩
  · intro a ha
    obtain ⟨⟨y, m⟩, hy⟩ := IsLocalization.surj M a
    have hm : IsUnit (algebraMap R S m) := IsLocalization.map_units S m
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp only [map_zero] at hy
      exact ha (hm.mul_left_eq_zero.1 hy)
    obtain ⟨n, u, hu', rfl⟩ := eq_pow_mul_unit π hsep hu y hy0
    have hyu : IsUnit (algebraMap R S (π ^ n * u)) := by
      rw [map_mul, map_pow]
      exact ((IsLocalization.map_units S (⟨π, hπ⟩ : M)).pow n).mul (hu'.map _)
    simp only at hy
    rw [← hy] at hyu
    exact (isUnit_of_mul_isUnit_left hyu).exists_right_inv
  · intro x
    obtain ⟨⟨y, m⟩, hy⟩ := IsLocalization.surj M x
    obtain ⟨n, c, hc⟩ := hM m m.2
    refine ⟨n, y * c, ?_⟩
    simp only at hy
    rw [← map_pow, hc, map_mul, map_mul, ← mul_assoc, hy]

theorem exists_isEps (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, ε, h0, -, h1, h⟩ := GlobalTheory.T.exists_compatible_rootsOfUnity_and_tilt_padic l
  refine ⟨ε, ?_, ?_⟩
  · have := h 0
    rw [h0, map_one] at this
    exact Subtype.ext this
  · intro e
    have := h 1
    apply h1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← this, map_one]
    exact congrArg Subtype.val e

theorem of_isEps (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (he : IsEps e) :
    IsDomain (Per.BdRp l) ∧ Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) ∧ IsField (Per.BdR l) ∧
      ∀ x : Per.BdR l, ∃ (n : ℕ) (y : Per.BdRp l), x * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) ^ n =
        algebraMap (Per.BdRp l) (Per.BdR l) y := by
  obtain ⟨hF, hreg, hc, -⟩ := _root_.GlobalTheory.MemLoc.filtration_eq_xi_pow l e he
  have hk := _root_.GlobalTheory.MemLoc.ker_localizedTheta_eq_span_xi l e he
  obtain ⟨-, hθ, hu, -, -⟩ := _root_.GlobalTheory.MemLoc.thetaD_props l
  have : Nontrivial (Per.BdRp l) := (Per.θD l).domain_nontrivial
  haveI : IsLocalization.Away (aDp l (xi e)) (Per.BdR l) := GlobalTheory.CrisLoc.bdR_away l _ hk
  refine general (Submonoid.powers (aDp l (xi e))) (aDp l (xi e)) hreg ?_ ?_ ?_ ?_
  · intro y hy
    refine hc.toIsHausdorff.haus y fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hy n
  · intro y hy
    refine hu y fun h => hy ?_
    have := (hF 1 y).1 ((hθ y).1 h)
    rwa [pow_one] at this
  · exact Submonoid.mem_powers _
  · rintro _ ⟨k, rfl⟩
    exact ⟨k, dvd_rfl⟩

theorem bdR_isField : ∀ (l : ℕ) [Fact l.Prime], IsDomain (Per.BdRp l) ∧ Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) ∧ IsField (Per.BdR l) ∧ ∀ e : Per.Fl l, IsEps e → ∀ x : Per.BdR l, ∃ (n : ℕ) (y : Per.BdRp l), x * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) ^ n = algebraMap (Per.BdRp l) (Per.BdR l) y := by
  intro l _
  obtain ⟨e, he⟩ := exists_isEps l
  obtain ⟨h1, h2, h3, -⟩ := of_isEps l e he
  exact ⟨h1, h2, h3, fun e' he' => (of_isEps l e' he').2.2.2⟩

end GlobalTheory.MemLoc.BdRField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralGroupAlgebraOpPreservesIntegralLevelForms
section
set_option autoImplicit false

noncomputable section

open NumberField
open scoped Matrix ComplexOrder

namespace GlobalTheory.CentralLevelOp

open Formalism.DivisionValues Formalism.L2.DIV

theorem lvlOp_mem_lvlNab : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : NumberField.InfinitePlace K), Formalism.DivisionValues.IsConjAt v0 →
    ∀ (S : Formalism.L2.DIV.CSD K), (S.H.map v0.embedding).PosDef →
    ∀ (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms), S.ActGood r →
    ∀ (P : Subgroup G) (ψ : P →* Kˣ) (a : MonoidAlgebra K G), (∀ b, a * b = b * a) → (∀ t : G, ∃ n : ℤ, a.coeff t = n) →
    ∀ x ∈ S.lvlNab r P ψ, (S.lvlOp r P ψ a).mulVec x ∈ S.lvlNab r P ψ := by
  intro K _ _ _ v0 h0 S hH G _ _ r hr P ψ a hc hz x hx
  have hE := (level_operator_spec K v0 h0 S hH G r hr P ψ a (hc _)).1
  change (S.lvlE r P ψ).mulVec x ∈ S.nabLat at hx
  change (S.lvlE r P ψ).mulVec ((S.lvlOp r P ψ a).mulVec x) ∈ S.nabLat
  rw [Matrix.mulVec_mulVec, hE, ← Matrix.mulVec_mulVec, CSD.gaMat, Matrix.sum_mulVec]
  refine Submodule.sum_mem _ fun t _ => ?_
  obtain ⟨n, hn⟩ := hz t
  rw [Matrix.smul_mulVec, hn, Int.cast_smul_eq_zsmul]
  exact Submodule.smul_of_tower_mem _ n ((action_preserves_lattice K S G r hr t).1 _ hx)

end GlobalTheory.CentralLevelOp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassFunctionActsByScalarOnIrrCharStatement
section
open Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classFunction_acts_by_scalar_on_irrChar : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] (e : MonoidAlgebra ℂ G), (∀ x y : G, e.coeff (y * x * y⁻¹) = e.coeff x) → ∀ (ψ : G → ℂ), ψ ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ → ∀ x : G, ψ 1 * ∑ g, e.coeff g * ψ (g * x) = (∑ g, e.coeff g * ψ g) * ψ x := by
  first | exact @GlobalTheory.classFun_char_scalar | exact GlobalTheory.classFun_char_scalar | (intros; apply GlobalTheory.classFun_char_scalar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarUpqHasOmegaDensity
section
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

noncomputable section

namespace GlobalTheory.HaarDensityUpq

def toL1 (P Q : ℕ) : lieU P Q →ₗ[ℝ] PiLp 1 (fun _ : (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) => ℂ) where
  toFun X := WithLp.toLp 1 (entries (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem toL1_injective (P Q : ℕ) : Function.Injective (toL1 P Q) := by
  intro X Y h
  ext i j
  exact congrFun (congrArg WithLp.ofLp h) (i, j)

theorem isInducing_toL1 (P Q : ℕ) : IsInducing (toL1 P Q) := by
  have h1 : IsInducing (entries : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ → _) :=
    (Homeomorph.piCurry (X := Fin P ⊕ Fin Q) (Y := Fin P ⊕ Fin Q) (Z := ℂ)).symm.isInducing
  exact (PiLp.homeomorph 1 (fun _ : (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) => ℂ)).symm.isInducing.comp
    (h1.comp IsInducing.subtypeVal)

@[reducible] def sumNorm (P Q : ℕ) : NormedAddCommGroup (lieU P Q) :=
  let N := NormedAddCommGroup.induced (lieU P Q) _ (toL1 P Q) (toL1_injective P Q)
  { toNorm := N.toNorm
    toAddCommGroup := inferInstance
    toMetricSpace := N.toMetricSpace.replaceTopology (isInducing_toL1 P Q).eq_induced
    dist_eq := N.dist_eq }

theorem mat_mul {P Q : ℕ} (g h : UpqT P Q) : (g * h).mat = g.mat * h.mat := rfl

end GlobalTheory.HaarDensityUpq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAbsIrrCharMapRingHom
section
open Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.AbsIrrMap

theorem isAbsIrrChar_map : ∀ {K K' G : Type} [Field K] [Field K'] [CharZero K] [CharZero K'] [Group G] [Fintype G]
    (φ : K →+* K') (χ : G → K), IsAbsIrrChar χ → IsAbsIrrChar (fun g => φ (χ g)) := by
  intro K K' G _ _ _ _ _ _ φ χ h
  classical
  obtain ⟨n, ρ, hi, hρ⟩ := h
  let A := AlgebraicClosure K
  let A' := AlgebraicClosure K'
  letI : Algebra K A' := ((algebraMap K' A').comp φ).toAlgebra
  let ψ : A →ₐ[K] A' := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hψ : ∀ x : K, ψ (algebraMap K A x) = algebraMap K' A' (φ x) := fun x => by
    rw [AlgHom.commutes]; rfl
  let ρ' : Representation A' G (Fin n → A') := GlobalTheory.BrauerRealise.mapScalars (ψ : A →+* A') ρ
  have hch : ∀ g, ρ'.character g = ψ (ρ.character g) :=
    GlobalTheory.BrauerRealise.character_mapScalars (ψ : A →+* A') ρ
  refine ⟨n, ρ', GlobalTheory.BrauerRealise.isIrreducible_of_sum_char_mul_char_inv ρ' ?_, fun t => ?_⟩
  · have : Invertible ((Nat.card G : ℕ) : A) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    have hcard : ((Nat.card G : ℕ) : A) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have ho := Representation.char_orthonormal ρ ρ
    rw [if_pos ⟨Representation.Equiv.refl ρ⟩] at ho
    have hsum : ∑ g, ρ.character g * ρ.character g⁻¹ = (Nat.card G : A) := by
      field_simp at ho
      simpa using ho
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hch, ← map_mul, ← map_sum, hsum]
    exact map_natCast ψ _
  · rw [hch, hρ, hψ]

end GlobalTheory.AbsIrrMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemDeRhamFiltrationIffXiPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem mem_FilD_iff_xi_pow : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a ↔ ∃ y : Per.BdRp l, x * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) ^ (-a).toNat = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e) ^ a.toNat * y) := by
  intro l _ e he a x
  have h := (_root_.GlobalTheory.MemLoc.filtration_eq_xi_pow l e he).1
  have hg : ∀ (n : ℕ) (x : Per.BdR l), x ∈ Per.FilD l (-(n : ℤ)) ↔ ∃ y : Per.BdRp l,
      x * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) ^ n = algebraMap (Per.BdRp l) (Per.BdR l) y :=
    GlobalTheory.CrisLoc.mem_fil_neg l _ (_root_.GlobalTheory.MemLoc.ker_localizedTheta_eq_span_xi l e he)
  generalize aDp l (xi e) = ξ at h hg ⊢
  have hn : ∀ (n : ℕ) (w : Per.BdR l), w ∈ Per.FilD l (n : ℤ) ↔
      ∃ y : Per.BdRp l, w = algebraMap (Per.BdRp l) (Per.BdR l) (ξ ^ n * y) := by
    intro n w
    constructor
    · intro hw
      obtain ⟨z, hz, ez⟩ := GlobalTheory.RingIface.exists_of_mem_FilD_nat l hw
      obtain ⟨y, rfl⟩ := (h _ _).1 hz
      exact ⟨y, ez.symm⟩
    · rintro ⟨y, rfl⟩
      exact GlobalTheory.RingIface.alg_mem_FilD_nat l ((h _ _).2 (dvd_mul_right _ _))
  rcases le_total 0 a with ha | ha
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha
    rw [hn, Int.toNat_neg_natCast, Int.toNat_natCast, pow_zero, mul_one]
  · obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat ha
    rw [hg, neg_neg, Int.toNat_neg_natCast, Int.toNat_natCast]
    simp only [pow_zero, one_mul]

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumIrrCharOneMulIrrCharColumnOrthogonalityStatement
section
open Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_irrChar_one_mul_irrChar_column_orthogonality : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] [inst_2 : DecidableEq G] (A : Finset (G → ℂ)), (∀ ψ, ψ ∈ A ↔ ψ ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ) → ∀ g : G, ∑ ψ ∈ A, ψ 1 * ψ g = if g = 1 then (Fintype.card G : ℂ) else 0 := by
  first | exact @GlobalTheory.ColumnOrth.sum_char_one_mul_char | exact GlobalTheory.ColumnOrth.sum_char_one_mul_char | (intros; apply GlobalTheory.ColumnOrth.sum_char_one_mul_char <;> assumption)
end

