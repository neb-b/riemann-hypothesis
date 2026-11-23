module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0486

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOne
section
set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

namespace Katz

namespace CobCob

variable {R : Type} [CommRing R] {d : ℕ} {τ : Type}

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
theorem _root_.GlobalTheory.Katz.CobCob.elim_has {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero (by rintro (i | i) <;> simp [hu, hv])

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
theorem _root_.GlobalTheory.Katz.CobCob.op_const
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (h : ∀ i, constantCoeff (μ i) = 0)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    constantCoeff (_root_.GlobalTheory.Katz.op μ u v i) = 0 := by
  unfold _root_.GlobalTheory.Katz.op _root_.GlobalTheory.Katz.at2
  exact constantCoeff_subst_eq_zero (_root_.GlobalTheory.Katz.CobCob.elim_has hu hv)
    (by rintro (j | j) <;> simp [hu, hv]) (h i)

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
theorem _root_.GlobalTheory.Katz.CobCob.constantCoeff_threeGroupsFirstVariables (i : Fin d) :
    constantCoeff (_root_.GlobalTheory.Katz.x1 (R := R) i) = 0 := by
  unfold _root_.GlobalTheory.Katz.x1
  exact constantCoeff_X _

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
theorem _root_.GlobalTheory.Katz.CobCob.constantCoeff_threeGroupsSecondVariables (i : Fin d) :
    constantCoeff (_root_.GlobalTheory.Katz.x2 (R := R) i) = 0 := by
  unfold _root_.GlobalTheory.Katz.x2
  exact constantCoeff_X _

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
theorem _root_.GlobalTheory.Katz.CobCob.constantCoeff_threeGroupsThirdVariables (i : Fin d) :
    constantCoeff (_root_.GlobalTheory.Katz.x3 (R := R) i) = 0 := by
  unfold _root_.GlobalTheory.Katz.x3
  exact constantCoeff_X _

end CobCob

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
private theorem at2_sub_of_hasSubst {u v : Fin d → MvPowerSeries τ R}
    (h : HasSubst (Sum.elim u v)) (c c' : MvPowerSeries (Fin d ⊕ Fin d) R) :
    _root_.GlobalTheory.Katz.at2 (c - c') u v =
      _root_.GlobalTheory.Katz.at2 c u v - _root_.GlobalTheory.Katz.at2 c' u v := by
  unfold _root_.GlobalTheory.Katz.at2
  exact subst_sub h c c'

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
private theorem at2_subst_of_hasSubst {u v : Fin d → MvPowerSeries τ R}
    (h : HasSubst (Sum.elim u v)) {a : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries (Fin d) R) :
    _root_.GlobalTheory.Katz.at2 (subst a f) u v =
      subst (fun i => _root_.GlobalTheory.Katz.at2 (a i) u v) f := by
  unfold _root_.GlobalTheory.Katz.at2
  exact subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha) h f

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
private theorem at2_X_of_hasSubst {u v : Fin d → MvPowerSeries τ R}
    (h : HasSubst (Sum.elim u v)) (s : Fin d ⊕ Fin d) :
    _root_.GlobalTheory.Katz.at2 (X s) u v = Sum.elim u v s := by
  unfold _root_.GlobalTheory.Katz.at2
  exact subst_X h s

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
private theorem at2_cob1_eq_subst_op_sub {u v : Fin d → MvPowerSeries τ R}
    (h : HasSubst (Sum.elim u v)) {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (f : MvPowerSeries (Fin d) R) :
    _root_.GlobalTheory.Katz.at2 (_root_.GlobalTheory.Katz.cob1 μ f) u v =
      subst (_root_.GlobalTheory.Katz.op μ u v) f - subst u f - subst v f := by
  unfold _root_.GlobalTheory.Katz.cob1 _root_.GlobalTheory.Katz.inL _root_.GlobalTheory.Katz.inR
  rw [at2_sub_of_hasSubst h, at2_sub_of_hasSubst h,
    at2_subst_of_hasSubst h hμ,
    at2_subst_of_hasSubst h (fun i => constantCoeff_X _),
    at2_subst_of_hasSubst h (fun i => constantCoeff_X _)]
  simp only [at2_X_of_hasSubst h, Sum.elim_inl, Sum.elim_inr]
  rfl

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
private theorem at2_add_of_hasSubst {u v : Fin d → MvPowerSeries τ R}
    (h : HasSubst (Sum.elim u v)) (c c' : MvPowerSeries (Fin d ⊕ Fin d) R) :
    _root_.GlobalTheory.Katz.at2 (c + c') u v =
      _root_.GlobalTheory.Katz.at2 c u v + _root_.GlobalTheory.Katz.at2 c' u v := by
  unfold _root_.GlobalTheory.Katz.at2
  exact subst_add h c c'

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
private theorem at2_smul_of_hasSubst {u v : Fin d → MvPowerSeries τ R}
    (h : HasSubst (Sum.elim u v)) (r : R) (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    _root_.GlobalTheory.Katz.at2 (r • c) u v = r • _root_.GlobalTheory.Katz.at2 c u v := by
  unfold _root_.GlobalTheory.Katz.at2
  exact subst_smul h r c

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
private theorem op_addLaw_eq_add_of_hasSubst {u v : Fin d → MvPowerSeries τ R}
    (h : HasSubst (Sum.elim u v)) :
    _root_.GlobalTheory.Katz.op (_root_.GlobalTheory.Katz.addLaw R d) u v = fun i => u i + v i := by
  funext i
  unfold _root_.GlobalTheory.Katz.op _root_.GlobalTheory.Katz.addLaw
  rw [at2_add_of_hasSubst h, at2_X_of_hasSubst h,
    at2_X_of_hasSubst h]
  rfl


set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
theorem _root_.GlobalTheory.Katz.formalGroupLawCoboundaryTwo_coboundaryOne_alt : ∀ (R : Type) [CommRing R] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) →
    ∀ f : MvPowerSeries (Fin d) R,
    _root_.GlobalTheory.Katz.cob2 μ (_root_.GlobalTheory.Katz.cob1 μ f) =
      subst (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x1
        (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x2 _root_.GlobalTheory.Katz.x3)) f -
      subst (_root_.GlobalTheory.Katz.op μ
        (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x1 _root_.GlobalTheory.Katz.x2)
        _root_.GlobalTheory.Katz.x3) f ∧
    _root_.GlobalTheory.Katz.swap (_root_.GlobalTheory.Katz.cob1 μ f) -
      _root_.GlobalTheory.Katz.cob1 μ f =
      subst (fun i => _root_.GlobalTheory.Katz.swap (μ i)) f - subst μ f ∧
    (∀ c c', _root_.GlobalTheory.Katz.cob2 μ (c + c') =
      _root_.GlobalTheory.Katz.cob2 μ c + _root_.GlobalTheory.Katz.cob2 μ c' ∧
      _root_.GlobalTheory.Katz.cob2 μ (c - c') =
      _root_.GlobalTheory.Katz.cob2 μ c - _root_.GlobalTheory.Katz.cob2 μ c' ∧
      _root_.GlobalTheory.Katz.swap (c - c') =
      _root_.GlobalTheory.Katz.swap c - _root_.GlobalTheory.Katz.swap c') ∧
    (∀ (r : R) c, _root_.GlobalTheory.Katz.cob2 μ (r • c) = r • _root_.GlobalTheory.Katz.cob2 μ c ∧
      _root_.GlobalTheory.Katz.swap (r • c) = r • _root_.GlobalTheory.Katz.swap c) ∧
    _root_.GlobalTheory.Katz.IsLaw (_root_.GlobalTheory.Katz.addLaw R d) ∧
    (_root_.GlobalTheory.Katz.IsLaw μ →
      _root_.GlobalTheory.Katz.IsCoc μ (_root_.GlobalTheory.Katz.cob1 μ f)) := by
  intro R _ d μ hμ f
  have h1 := _root_.GlobalTheory.Katz.CobCob.constantCoeff_threeGroupsFirstVariables (R := R) (d := d)
  have h2 := _root_.GlobalTheory.Katz.CobCob.constantCoeff_threeGroupsSecondVariables (R := R) (d := d)
  have h3 := _root_.GlobalTheory.Katz.CobCob.constantCoeff_threeGroupsThirdVariables (R := R) (d := d)
  have h23 := _root_.GlobalTheory.Katz.CobCob.elim_has h2 h3
  have h12 := _root_.GlobalTheory.Katz.CobCob.elim_has h1 h2
  have h12_3 := _root_.GlobalTheory.Katz.CobCob.elim_has (_root_.GlobalTheory.Katz.CobCob.op_const hμ h1 h2) h3
  have h1_23 := _root_.GlobalTheory.Katz.CobCob.elim_has h1 (_root_.GlobalTheory.Katz.CobCob.op_const hμ h2 h3)
  have hs : HasSubst (Sum.elim (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (fun i => X (Sum.inl i))) :=
    _root_.GlobalTheory.Katz.CobCob.elim_has (fun i => constantCoeff_X _) (fun i => constantCoeff_X _)
  have part1 : _root_.GlobalTheory.Katz.cob2 μ (_root_.GlobalTheory.Katz.cob1 μ f) =
      subst (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x1
        (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x2 _root_.GlobalTheory.Katz.x3)) f -
      subst (_root_.GlobalTheory.Katz.op μ
        (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x1 _root_.GlobalTheory.Katz.x2)
        _root_.GlobalTheory.Katz.x3) f := by
    unfold _root_.GlobalTheory.Katz.cob2
    rw [at2_cob1_eq_subst_op_sub h23 hμ, at2_cob1_eq_subst_op_sub h12_3 hμ,
      at2_cob1_eq_subst_op_sub h1_23 hμ, at2_cob1_eq_subst_op_sub h12 hμ]
    abel
  have part2 : _root_.GlobalTheory.Katz.swap (_root_.GlobalTheory.Katz.cob1 μ f) -
      _root_.GlobalTheory.Katz.cob1 μ f =
      subst (fun i => _root_.GlobalTheory.Katz.swap (μ i)) f - subst μ f := by
    have e : _root_.GlobalTheory.Katz.swap (_root_.GlobalTheory.Katz.cob1 μ f) =
        subst (fun i => _root_.GlobalTheory.Katz.swap (μ i)) f -
          _root_.GlobalTheory.Katz.inR f - _root_.GlobalTheory.Katz.inL f :=
      at2_cob1_eq_subst_op_sub hs hμ f
    rw [e]
    unfold _root_.GlobalTheory.Katz.cob1
    abel
  refine ⟨part1, part2, fun c c' => ⟨?_, ?_, ?_⟩, fun r c => ⟨?_, ?_⟩, ?_, fun hl => ?_⟩
  · unfold _root_.GlobalTheory.Katz.cob2
    rw [at2_add_of_hasSubst h23, at2_add_of_hasSubst h12_3,
      at2_add_of_hasSubst h1_23, at2_add_of_hasSubst h12]
    abel
  · unfold _root_.GlobalTheory.Katz.cob2
    rw [at2_sub_of_hasSubst h23, at2_sub_of_hasSubst h12_3,
      at2_sub_of_hasSubst h1_23, at2_sub_of_hasSubst h12]
    abel
  · unfold _root_.GlobalTheory.Katz.swap
    exact at2_sub_of_hasSubst hs c c'
  · unfold _root_.GlobalTheory.Katz.cob2
    rw [at2_smul_of_hasSubst h23, at2_smul_of_hasSubst h12_3,
      at2_smul_of_hasSubst h1_23, at2_smul_of_hasSubst h12]
    simp only [smul_sub, smul_add]
  · unfold _root_.GlobalTheory.Katz.swap
    exact at2_smul_of_hasSubst hs r c
  · have hc : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.addLaw R d i) = 0 := by
      intro i
      simp [_root_.GlobalTheory.Katz.addLaw]
    refine ⟨hc, ?_, ?_, ?_⟩
    · rw [op_addLaw_eq_add_of_hasSubst
        (_root_.GlobalTheory.Katz.CobCob.elim_has (fun i => constantCoeff_X i) (fun _ => by simp))]
      funext i
      simp
    · intro i
      unfold _root_.GlobalTheory.Katz.swap _root_.GlobalTheory.Katz.addLaw
      rw [at2_add_of_hasSubst hs, at2_X_of_hasSubst hs,
        at2_X_of_hasSubst hs]
      simp [add_comm]
    · rw [op_addLaw_eq_add_of_hasSubst
          (_root_.GlobalTheory.Katz.CobCob.elim_has (_root_.GlobalTheory.Katz.CobCob.op_const hc h1 h2) h3),
        op_addLaw_eq_add_of_hasSubst h12,
        op_addLaw_eq_add_of_hasSubst
          (_root_.GlobalTheory.Katz.CobCob.elim_has h1 (_root_.GlobalTheory.Katz.CobCob.op_const hc h2 h3)),
        op_addLaw_eq_add_of_hasSubst h23]
      funext i
      exact add_assoc _ _ _
  · unfold _root_.GlobalTheory.Katz.IsCoc
    constructor
    · rw [part1, hl.assoc, sub_self]
    · rw [← sub_eq_zero, part2]
      simp [hl.comm]

end Katz

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericMultOneDimOf
section
noncomputable section

namespace GlobalTheory.GenericProduct

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne NumberField Module

def OneGenericVector : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 →
    ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ)
      (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → whDim ψ (parInd b σ) = 1

section Twist

variable {K P V : Type} [Field K] [Group P] [AddCommGroup V] [Module K V]

def twistInv (τ : Representation K P V) (c : P →* Kˣ) : Representation K P V where
  toFun h := (((c h)⁻¹ : Kˣ) : K) • τ h
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul, map_mul, mul_inv, Units.val_mul, smul_mul_smul_comm]

theorem twistInv_apply (τ : Representation K P V) (c : P →* Kˣ) (h : P) :
    twistInv τ c h = (((c h)⁻¹ : Kˣ) : K) • τ h := rfl

theorem sum_trace_mul_inv [Fintype P] [CharZero K] [FiniteDimensional K V] (τ : Representation K P V) (c : P →* Kˣ) :
    ∑ h : P, LinearMap.trace K V (τ h) * (((c h)⁻¹ : Kˣ) : K) =
      (Nat.card P : K) * (finrank K (twistInv τ c).invariants : K) := by
  have hc : (Nat.card P : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  letI : Invertible (Nat.card P : K) := invertibleOfNonzero hc
  letI : Invertible (Fintype.card P : K) := invertibleOfNonzero (by rw [← Nat.card_eq_fintype_card]; exact hc)
  have h := Representation.card_inv_mul_sum_char_eq_finrank (twistInv τ c)
  rw [← h, mul_inv_cancel_left₀ hc]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Representation.character, twistInv_apply, map_smul, smul_eq_mul, mul_comm]

end Twist

theorem sum_unip_eq {F : Type} [Field F] {r : ℕ} [Fintype (unip F r)] {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ψ : AddChar F ℂ) (τ : Representation ℂ (GL (Fin r) F) V) :
    ∑ h : unip F r, LinearMap.trace ℂ V (τ h) * (((addCharHom ψ (supHom F r) h)⁻¹ : ℂˣ) : ℂ) =
      (Nat.card (unip F r) : ℂ) * (whDim ψ τ : ℂ) := by
  have h := sum_trace_mul_inv (τ.comp (unip F r).subtype) (addCharHom ψ (supHom F r))
  have e : (twistInv (τ.comp (unip F r).subtype) (addCharHom ψ (supHom F r))).invariants =
      eig τ (unip F r : Set (GL (Fin r) F)) fun g => ψ (edgeSum supEdge g) := by
    ext v
    simp only [Representation.mem_invariants, eig, Submodule.mem_iInf, LinearMap.mem_ker, twistInv_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    have key : ∀ g : unip F r, ((((addCharHom ψ (supHom F r) g)⁻¹ : ℂˣ) : ℂ) • (τ.comp (unip F r).subtype g) v = v ↔
        τ g v = ψ (edgeSum supEdge (g : GL (Fin r) F)) • v) := by
      intro g
      have hv : ψ (edgeSum supEdge (g : GL (Fin r) F)) = ((addCharHom ψ (supHom F r) g : ℂˣ) : ℂ) := rfl
      rw [hv, Units.val_inv_eq_inv_val, inv_smul_eq_iff₀ (Units.ne_zero _)]
      rfl
    exact ⟨fun H g hg => (key ⟨g, hg⟩).1 (H ⟨g, hg⟩), fun H g => (key g).2 (H g.1 g.2)⟩
  rw [e] at h
  exact h

def piEquiv {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H) ≃ ∀ i, H i where
  toFun x i := ⟨x.1 i, x.2 i (Set.mem_univ _)⟩
  invFun y := ⟨fun i => (y i).1, fun i _ => (y i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

attribute [local instance] resField finite_res

theorem genericMultOne (hL : OneGenericVector) : GenericMultOne := by
  classical
  intro E _ _ Pg r K _ _ s ψ hψ χ hχ
  obtain ⟨b, V, i1, i2, i3, σ, hσ, hs⟩ := hχ
  letI : Fintype (P0 Pg r ψ).H := Fintype.ofFinite _
  letI : ∀ PP : ↥Pg, Fintype (unip (kP PP.1) r) := fun PP => Fintype.ofFinite _
  apply s.injective
  let ψ' : ∀ PP : ↥Pg, AddChar (kP PP.1) ℂ := fun PP => s.toMonoidHom.compAddChar (ψ PP.1)
  have hψ' : ∀ PP : ↥Pg, ψ' PP ≠ 1 := by
    intro PP h
    refine hψ PP.1 PP.2 ?_
    ext x
    apply s.injective
    have := DFunLike.congr_fun h x
    simpa [ψ'] using this
  let e : (P0 Pg r ψ).H ≃ ∀ PP : ↥Pg, unip (kP PP.1) r := piEquiv fun PP : ↥Pg => unip (kP PP.1) r
  let f : ∀ PP : ↥Pg, unip (kP PP.1) r → ℂ := fun PP h =>
    LinearMap.trace ℂ _ (parInd (F := kP PP.1) (b PP) (σ PP) h) *
      (((addCharHom (ψ' PP) (supHom (kP PP.1) r) h)⁻¹ : ℂˣ) : ℂ)
  have hf : ∀ PP : ↥Pg, ∑ h, f PP h = (Nat.card (unip (kP PP.1) r) : ℂ) := by
    intro PP
    letI : Fintype (kP PP.1) := Fintype.ofFinite _
    haveI := finite_parInd (b PP) (σ PP)
    have h1 := sum_unip_eq (ψ' PP) (parInd (F := kP PP.1) (b PP) (σ PP))
    rw [hL (kP PP.1) (ψ' PP) (hψ' PP) r (V PP) (b PP) (σ PP) (hσ PP), Nat.cast_one, mul_one] at h1
    exact h1
  have hterm : ∀ h : (P0 Pg r ψ).H, s (χ (h : G0 Pg r) * ((((P0 Pg r ψ).chi h)⁻¹ : Kˣ) : K)) = ∏ PP, f PP (e h PP) := by
    intro h
    have hchi : (P0 Pg r ψ).chi h = ∏ PP : ↥Pg, addCharHom (ψ PP.1) (supHom (kP PP.1) r) (e h PP) := by
      exact MonoidHom.finsetProd_apply (fun PP : ↥Pg => (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp
        (LevelP.prj (fun PP : ↥Pg => unip (kP PP.1) r) PP)) Finset.univ h
    rw [map_mul, hs, hchi, Units.val_inv_eq_inv_val, map_inv₀, Units.coe_prod, map_prod, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun PP _ => ?_
    simp only [f, Units.val_inv_eq_inv_val]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_congr rfl fun h _ => hterm h, map_natCast, Nat.card_congr e, Nat.card_pi, Nat.cast_prod,
    ← Finset.prod_congr rfl fun PP _ => hf PP, Fintype.prod_sum]
  exact Fintype.sum_equiv e _ _ fun _ => rfl

end GlobalTheory.GenericProduct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTjCosetsFiniteCardLe
section
open NumberField IsDedekindDomain

namespace GlobalTheory.TjCount

theorem Tj_complex_ne_zero_iff {L : Type} [Field L] (n : ℕ) (O : Subring L) (ϖ : L) (j : ℕ)
    (g : GL (Fin n) L) : Formalism.UG.Tj ℂ n O ϖ j g ≠ 0 ↔ Formalism.UG.Tj ℤ n O ϖ j g ≠ 0 := by
  unfold Formalism.UG.Tj
  rw [Set.indicator_apply_ne_zero, Set.indicator_apply_ne_zero]
  simp

theorem prod_le_pow (q n j : ℕ) (hq : 2 ≤ q) (hj : j ≤ n) :
    0 < ∏ i ∈ Finset.range j, ((q : ℤ) ^ (n - i) - 1) ∧
    ∏ i ∈ Finset.range j, ((q : ℤ) ^ (n - i) - 1) ≤ (q : ℤ) ^ (n * j) := by
  have hq1 : (1 : ℤ) < q := by exact_mod_cast (by omega : 1 < q)
  have hpos : ∀ i ∈ Finset.range j, (0 : ℤ) < (q : ℤ) ^ (n - i) - 1 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have : (1 : ℤ) < (q : ℤ) ^ (n - i) := one_lt_pow₀ hq1 (by omega)
    linarith
  refine ⟨Finset.prod_pos hpos, ?_⟩
  calc ∏ i ∈ Finset.range j, ((q : ℤ) ^ (n - i) - 1)
      ≤ ∏ _i ∈ Finset.range j, (q : ℤ) ^ n := by
        apply Finset.prod_le_prod₀ (fun i hi => (hpos i hi).le)
        intro i hi
        have : (q : ℤ) ^ (n - i) ≤ (q : ℤ) ^ n := pow_le_pow_right₀ hq1.le (Nat.sub_le n i)
        linarith
    _ = (q : ℤ) ^ (n * j) := by rw [Finset.prod_const, Finset.card_range, ← pow_mul]

theorem one_le_prod (q j : ℕ) (hq : 2 ≤ q) : 1 ≤ ∏ i ∈ Finset.range j, ((q : ℤ) ^ (i + 1) - 1) := by
  have hq1 : (1 : ℤ) < q := by exact_mod_cast (by omega : 1 < q)
  have h1 : ∀ i ∈ Finset.range j, (1 : ℤ) ≤ (q : ℤ) ^ (i + 1) - 1 := by
    intro i _
    have : (q : ℤ) ≤ (q : ℤ) ^ (i + 1) := by
      calc (q : ℤ) = (q : ℤ) ^ 1 := (pow_one _).symm
        _ ≤ (q : ℤ) ^ (i + 1) := pow_le_pow_right₀ hq1.le (by omega)
    linarith
  calc (1 : ℤ) = ∏ _i ∈ Finset.range j, (1 : ℤ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) h1

end GlobalTheory.TjCount


open GlobalTheory.TjCount in
theorem GlobalTheory.TjCount.tj_cosets_finite_card_le : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), Formalism.UG.IsUnifV E w ϖ → ∀ j ≤ n, {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n) | Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0}.Finite ∧ Nat.card {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n) // Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0} ≤ Formalism.UG.qV E w ^ (n * j) := by
  intro E _ _ w n ϖ hϖ j hj
  have h := Formalism.UG.P.Tj_double_coset_decomposition E w n ϖ (GlobalTheory.LFun.mem_Ov_of_isUnifV hϖ) hϖ j hj
  have hq : 2 ≤ Formalism.UG.qV E w := GlobalTheory.LFun.one_lt_absNorm w
  have hcard : Nat.card {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n) //
      Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0} =
      Nat.card {x : GL (Fin n) (w.adicCompletion E) ⧸ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E w) |
        Formalism.UG.Tj ℤ n (Formalism.UG.Ov E w) ϖ j x.out ≠ 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => Tj_complex_ne_zero_iff _ _ _ _ _)
  obtain ⟨hP, hB⟩ := prod_le_pow (Formalism.UG.qV E w) n j hq hj
  have hA := one_le_prod (Formalism.UG.qV E w) j hq
  rw [← hcard] at h
  set C := Nat.card {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n) //
      Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0} with hC
  have hCpos : 0 < C := by
    rcases Nat.eq_zero_or_pos C with h0 | h0
    · rw [h0] at h; simp at h; linarith
    · exact h0
  have hle : (C : ℤ) ≤ (Formalism.UG.qV E w : ℤ) ^ (n * j) := by
    have : (C : ℤ) ≤ (C : ℤ) * ∏ i ∈ Finset.range j, ((Formalism.UG.qV E w : ℤ) ^ (i + 1) - 1) :=
      le_mul_of_one_le_right (by positivity) hA
    linarith
  refine ⟨?_, by exact_mod_cast hle⟩
  have : Finite {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n) //
      Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0} := Nat.finite_of_card_ne_zero hCpos.ne'
  exact Set.finite_coe_iff.mp (by exact this)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeJetSplitDirectionAdd
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma piFinset_range_succ_eq_Iic {ι : Type} [Fintype ι] [DecidableEq ι] (κ : ι → ℕ) :
    Fintype.piFinset (fun i => Finset.range (κ i + 1)) = Finset.Iic κ := by
  ext μ
  simp [Fintype.mem_piFinset, Finset.mem_range, Finset.mem_Iic, Pi.le_def, Nat.lt_succ_iff]


open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
theorem _root_.GlobalTheory.HilbFam.jet_split_add : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t v : ℂ) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ), Even k → _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → _root_.GlobalTheory.HilbFam.jet k (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) κ τ (c + v) t = ∑ μ ∈ Finset.Iic κ, ((∏ i, _root_.GlobalTheory.HilbFam.rco k (κ i) (μ i) : ℤ) : ℂ) * v ^ (∑ i, (κ i - μ i)) * _root_.GlobalTheory.HilbFam.jet k (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) μ τ c t := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t v κ hk ha hτ
  have hμ := fun μ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ =>
    ((_root_.GlobalTheory.HilbFam.hasSum_jet_split F k 𝔞 𝔟 a₀ a x τ c t μ hk ha hτ).mul_left
      (((∏ i, _root_.GlobalTheory.HilbFam.rco k (κ i) (μ i) : ℤ) : ℂ) * v ^ (∑ i, (κ i - μ i))))
  have hs := hasSum_sum (s := Finset.Iic κ) fun μ _ => hμ μ
  refine (_root_.GlobalTheory.HilbFam.hasSum_jet_split F k 𝔞 𝔟 a₀ a x τ (c + v) t κ hk ha hτ).unique
    (hs.congr_fun fun ξ => ?_)
  simp_rw [_root_.GlobalTheory.HilbFam.lag_add, Finset.prod_univ_sum, piFinset_range_succ_eq_Iic,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  push_cast
  ring

end GlobalTheory.HilbFam
end

