module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwistBaseCoefficientRingResidueFieldFinite
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0082
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBasisCoordLattice
section
noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial

theorem exists_basis_coord_lattice {O V : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
    (B : Submodule O V) (hfg : B.FG)
    (hsp : Submodule.span (FractionRing O) (B : Set V) = ⊤) :
    ∃ (n : ℕ) (e : Module.Basis (Fin n) (FractionRing O) V),
      ∀ f : V, f ∈ B ↔ ∀ t, e.repr f t ∈ (algebraMap O (FractionRing O)).range := by
  classical
  have hfin : Module.Finite O B := Module.Finite.iff_fg.2 hfg
  have htf : Module.IsTorsionFree O V := Module.IsTorsionFree.trans_faithfulSMul O (FractionRing O) V
  have hfree : Module.Free O B := inferInstance
  let bO := Module.finBasis O B
  let v : Fin (Module.finrank O B) → V := fun t => (bO t : V)
  have hliO : LinearIndependent O v := bO.linearIndependent.map' B.subtype (Submodule.ker_subtype B)
  have hliK : LinearIndependent (FractionRing O) v :=
    (LinearIndependent.iff_fractionRing O (FractionRing O)).1 hliO
  have hBspan : B = Submodule.span O (Set.range v) := by
    have h1 : Submodule.map B.subtype (Submodule.span O (Set.range bO)) = B := by
      rw [bO.span_eq, Submodule.map_top, Submodule.range_subtype]
    rw [Submodule.map_span, ← Set.range_comp] at h1
    exact h1.symm
  have hle : (⊤ : Submodule (FractionRing O) V) ≤ Submodule.span (FractionRing O) (Set.range v) := by
    rw [← hsp, Submodule.span_le]
    intro x hx
    have hx' : x ∈ Submodule.span O (Set.range v) := hBspan ▸ hx
    exact Submodule.span_subset_span O (FractionRing O) (Set.range v) hx'
  let e := Module.Basis.mk hliK hle
  have he : ∀ t, e t = v t := fun t => by simp [e]
  refine ⟨_, e, fun f => ⟨fun hf => ?_, fun hf => ?_⟩⟩
  · rw [hBspan] at hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      intro s
      rw [← he, e.repr_self]
      by_cases h : t = s
      · subst h; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [h]⟩
    | zero => intro s; exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro s
      rw [map_add (f := _), Finsupp.add_apply]
      exact add_mem (hx s) (hy s)
    | smul a x _ hx =>
      intro s
      rw [← algebraMap_smul (FractionRing O) a x, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact mul_mem ⟨a, rfl⟩ (hx s)
  · choose c hc using hf
    rw [← e.sum_repr f]
    refine sum_mem fun t _ => ?_
    rw [← hc t, algebraMap_smul, he]
    exact B.smul_mem _ (hBspan ▸ Submodule.subset_span ⟨t, rfl⟩)

section SideCoord

variable {K C : Type} [Field K] [Field C] (iC : K →+* C) {V : Bool → Type}
  [∀ b, AddCommGroup (V b)] [∀ b, Module K (V b)] {n : Bool → ℕ}
  (e : ∀ b, Module.Basis (Fin (n b)) K (V b))

def sideEv (b : Bool) : V b →+ ((Σ b', Fin (n b')) → C) where
  toFun f y := if h : y.1 = b then iC ((e b).repr f (h ▸ y.2)) else 0
  map_zero' := by
    funext y
    by_cases h : y.1 = b <;> simp [h]
  map_add' f g := by
    funext y
    by_cases h : y.1 = b <;> simp [h]

@[simp] theorem sideEv_same (b : Bool) (f : V b) (t : Fin (n b)) :
    sideEv iC e b f ⟨b, t⟩ = iC ((e b).repr f t) := by
  simp [sideEv]

theorem sideEv_other {b b' : Bool} (h : b' ≠ b) (f : V b) (t : Fin (n b')) :
    sideEv iC e b f ⟨b', t⟩ = 0 := by
  simp [sideEv, h]

theorem sideEv_smul (b : Bool) (a : K) (f : V b) (y : Σ b', Fin (n b')) :
    sideEv iC e b (a • f) y = iC a * sideEv iC e b f y := by
  obtain ⟨b', t⟩ := y
  by_cases h : b' = b
  · subst h; simp
  · simp [sideEv_other iC e h]

theorem sideEv_inj (b : Bool) : Function.Injective (sideEv iC e b) := by
  intro f g hfg
  apply (e b).repr.injective
  ext t
  have := congrFun hfg ⟨b, t⟩
  exact iC.injective (by simpa using this)

def sideU (b : Bool) (T : Module.End K (V b)) (c y : Σ b', Fin (n b')) : C :=
  if h : c.1 = b then sideEv iC e b (T (e b (h ▸ c.2))) y else 0

theorem sideEv_end (b : Bool) (T : Module.End K (V b)) (f : V b) (y : Σ b', Fin (n b')) :
    sideEv iC e b (T f) y = ∑ c, sideU iC e b T c y * sideEv iC e b f c := by
  classical
  have h0 : T f = ∑ t, (e b).repr f t • T (e b t) := by
    conv_lhs => rw [← (e b).sum_repr f]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  have h1 : sideEv iC e b (T f) y =
      ∑ t, iC ((e b).repr f t) * sideEv iC e b (T (e b t)) y := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h0, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun t _ => sideEv_smul iC e b _ _ y
  rw [h1, Fintype.sum_sigma, Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp [sideU, mul_comm]
  · intro b' _ hb
    refine Finset.sum_eq_zero fun t _ => ?_
    simp [sideEv_other iC e hb]
  · simp

end SideCoord

theorem exists_nth_of_fg_full : ∀ (D : D7) (tw : NTw D.R D.host D.what₂ D.LL0 D.nd)
    (ex : NExp D.R D.host D.what₂ D.LL0 D.nd tw),
    (∀ i : tw.Tw, ∃ iC : FractionRing (tw.O i) →+* ℂ_[tw.l i], ∀ x, ‖iC x‖ ≤ 1 ↔
      x ∈ (algebraMap (tw.O i) (FractionRing (tw.O i))).range) →
    (∀ i j b, (ex.Bsup i j b).FG ∧
      Submodule.span (FractionRing (tw.O i)) (ex.Bsup i j b : Set (ex.Fm i j b)) = ⊤) →
    Nonempty (NTh D.R D.host D.what₂ D.LL0 D.nd tw ex) := by
  classical
  intro D tw ex hi hB
  choose iC hiC using hi
  have hex := fun i j b =>
    exists_basis_coord_lattice (ex.Bsup i j b) (hB i j b).1 (hB i j b).2
  choose n e he using hex
  have hsup : ∀ i j b, {f : ex.Fm i j b | f ∈ (⊤ : AddSubgroup (ex.Fm i j b)) ∧
      ∀ y, ‖sideEv (iC i) (e i j) b f y‖ ≤ 1} = (ex.Bsup i j b : Set (ex.Fm i j b)) := by
    intro i j b
    ext f
    simp only [Set.mem_ofPred_eq, AddSubgroup.mem_top, true_and, SetLike.mem_coe]
    rw [he i j b f]
    constructor
    · intro h t
      have := h ⟨b, t⟩
      rw [sideEv_same] at this
      exact (hiC i _).1 this
    · intro h y
      obtain ⟨b', t⟩ := y
      by_cases hb : b' = b
      · subst hb
        rw [sideEv_same]
        exact (hiC i _).2 (h t)
      · rw [sideEv_other _ _ hb]
        simp
  exact ⟨{
    iC := iC
    iC_int := hiC
    aL := fun i => if ∃ k, tw.l i = D.host.g k then 1 else 0
    aL_g := fun i k h => if_pos ⟨k, h⟩
    aL_off := fun i h => if_neg (not_exists.2 h)
    Pt := fun i j => Σ b, Fin (n i j b)
    ev := fun i j b => sideEv (iC i) (e i j) b
    ev_smul := fun i j b a f y => sideEv_smul _ _ b a f y
    ev_inj := fun i j b => sideEv_inj _ _ b
    Lt := fun _ _ => PUnit
    acgLt := fun _ _ => inferInstance
    modLt := fun _ _ => inferInstance
    freeLt := fun _ _ => inferInstance
    finLt := fun _ _ => inferInstance
    Let := fun _ _ => PEmpty
    finLet := fun _ _ => inferInstance
    Harm := fun _ _ => Set.univ
    Ctr := fun _ _ => PEmpty
    ctrC := fun _ _ κ => κ.elim
    Harm_def := fun i j P => ⟨fun _ κ => κ.elim, fun _ => Set.mem_univ _⟩
    thV := fun _ _ _ _ _ => 0
    thV_add := fun _ _ _ _ _ _ => by simp
    thV_smul := fun _ _ _ _ _ _ => by simp
    thV_addP := fun _ _ _ _ _ _ => by simp
    thV_smulP := fun _ _ _ _ _ _ => by simp
    datPhi := fun _ _ _ _ => 0
    datP := fun _ _ _ _ => 0
    recDet := fun _ _ _ => 1
    Kq := fun _ _ _ => PUnit
    grpKq := fun _ _ _ => inferInstance
    actK := fun _ _ _ _ y => y
    actK_one := fun _ _ _ _ => rfl
    actK_mul := fun _ _ _ _ _ _ => rfl
    recDetq := fun _ _ _ _ => 1
    recDetq_mem := fun _ _ _ _ => one_mem _
    recDet_act := fun _ _ _ _ _ _ _ _ _ _ => rfl
    recDetq_act := fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    hkIdx := fun i j _ _ => Σ b, Fin (n i j b)
    finHk := fun _ _ _ _ => inferInstance
    hkMove := fun _ _ _ _ c _ => c
    hkU := fun i j b k P c y => sideU (iC i) (e i j) b (ex.hkF i j b k P) c y
    hk_ev := fun i j b k P _ _ _ _ f y => sideEv_end _ _ b _ f y
    MaximalUnramifiedExtension := fun _ => ⊤
    FmUr := fun _ _ _ => ⊤
    FmUr_smul := fun _ _ _ _ _ _ _ => AddSubgroup.mem_top _
    FmUr_span := fun i j b => by
      rw [AddSubgroup.coe_top, Submodule.span_univ]
    Bsup_def := fun i j b => by
      rw [hsup i j b, Submodule.span_eq] }⟩

end GlobalTheory.HeightCounting

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexificationOfDefiniteGroupForms
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw.SpOfMat

open MonoidAlgebra

variable {G : Type} [Group G] [Fintype G]

theorem eq_sum_single {R : Type} [Semiring R] (a : MonoidAlgebra R G) : a = ∑ g, single g (a.coeff g) := by
  classical
  apply MonoidAlgebra.ext
  ext g
  simp [MonoidAlgebra.coeff_sum, Finsupp.single_apply]

noncomputable def conjSum (R : Type) [Semiring R] (g : G) : MonoidAlgebra R G := ∑ h, single (h * g * h⁻¹) 1

theorem conjSum_mem_center (R : Type) [CommSemiring R] (g : G) : conjSum R g ∈ Subalgebra.center R (MonoidAlgebra R G) := by
  rw [Subalgebra.mem_center_iff]
  intro b
  induction b using MonoidAlgebra.induction_on with
  | of k =>
    simp only [conjSum, MonoidAlgebra.of_apply, Finset.mul_sum, Finset.sum_mul, single_mul_single, one_mul, mul_one]
    refine Fintype.sum_equiv (Equiv.mulLeft k) _ _ fun h => ?_
    simp only [Equiv.coe_mulLeft]
    congr 1
    group
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

theorem mapRange_conjSum {R S : Type} [Semiring R] [Semiring S] (f : R →+* S) (g : G) :
    mapRingHom G f (conjSum R g) = conjSum S g := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [conjSum, map_sum, MonoidAlgebra.mapRingHom_single]

theorem card_smul_eq {R : Type} [CommSemiring R] (z : MonoidAlgebra R G) (hz : z ∈ Subalgebra.center R (MonoidAlgebra R G)) :
    (Fintype.card G : R) • z = ∑ g, z.coeff g • conjSum R g := by
  rw [Subalgebra.mem_center_iff] at hz
  have h1 : ∀ h : G, single h (1 : R) * z * single h⁻¹ 1 = z := fun h => by
    rw [hz, mul_assoc, single_mul_single, mul_inv_cancel, one_mul, ← one_def, mul_one]
  have h2 : ∀ h : G, single h (1 : R) * z * single h⁻¹ 1 = ∑ g, single (h * g * h⁻¹) (z.coeff g) := fun h => by
    conv_lhs => rw [eq_sum_single z]
    simp only [Finset.mul_sum, Finset.sum_mul, single_mul_single, one_mul, mul_one]
  calc (Fintype.card G : R) • z = ∑ h : G, z := by rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    _ = ∑ h : G, ∑ g, single (h * g * h⁻¹) (z.coeff g) := Finset.sum_congr rfl fun h _ => (h1 h).symm.trans (h2 h)
    _ = ∑ g, z.coeff g • conjSum R g := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [conjSum, Finset.smul_sum, smul_single, smul_eq_mul, mul_one]

end GlobalTheory.Mem.R3.Rw.SpOfMat

namespace GlobalTheory.Mem.R3.Rw.SpOfMat

open MonoidAlgebra

variable {G : Type} [Group G] [Fintype G]

theorem coeff_mapRingHom {R S : Type} [Semiring R] [Semiring S] (f : R →+* S) (a : MonoidAlgebra R G) (g : G) :
    (mapRingHom G f a).coeff g = f (a.coeff g) := by
  classical
  conv_lhs => rw [eq_sum_single a]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.coeff_sum, Finsupp.single_apply, apply_ite f]

section Act

variable {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} {σ : K →+* ℂ}
  {j : (Fin n → K) →ₛₗ[σ] EuclideanSpace ℂ (Fin n)} {H : Matrix (Fin n) (Fin n) K}
  {ρ : Matrix (Fin n) (Fin n) K →+* Module.End ℂ (EuclideanSpace ℂ (Fin n))}

theorem rho_smul (hρ : ∀ E, FormsTie σ j H E (ρ E)) (c : K) (E : Matrix (Fin n) (Fin n) K) :
    ρ (c • E) = σ c • ρ E := by
  refine LinearMap.ext_on_range (hρ E).span fun i => ?_
  rw [(hρ _).op_eq, LinearMap.smul_apply, (hρ E).op_eq, Matrix.smul_mulVec, map_smulₛₗ]

theorem rho_symm (hρ : ∀ E, FormsTie σ j H E (ρ E)) (E : Matrix (Fin n) (Fin n) K)
    (hsa : ∀ x y, Formalism.DivisionValues.hform H (E.mulVec x) y = Formalism.DivisionValues.hform H x (E.mulVec y)) : (ρ E).IsSymmetric := by
  let b := Module.Basis.mk (hρ E).li (hρ E).span.ge
  have hB : (innerₛₗ ℂ).comp (ρ E) = (innerₛₗ ℂ).compl₂ (ρ E) := by
    refine LinearMap.ext_basis b b fun i k => ?_
    simp only [b, Module.Basis.mk_apply, LinearMap.comp_apply, LinearMap.compl₂_apply, (hρ E).op_eq]
    change inner ℂ (j _) (j _) = inner ℂ (j _) (j _)
    rw [(hρ E).inner, (hρ E).inner, hsa]
  intro x y
  have := DFunLike.congr_fun (DFunLike.congr_fun hB x) y
  exact this

noncomputable def lin (ρ : Matrix (Fin n) (Fin n) K →+* Module.End ℂ (EuclideanSpace ℂ (Fin n)))
    (op : MonoidAlgebra K G → Matrix (Fin n) (Fin n) K) :
    MonoidAlgebra ℂ G →ₗ[ℂ] Module.End ℂ (EuclideanSpace ℂ (Fin n)) where
  toFun a := ∑ g, a.coeff g • ρ (op (single g 1))
  map_add' a b := by simp [MonoidAlgebra.coeff_add, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [MonoidAlgebra.coeff_smul, Finset.smul_sum, smul_smul]

theorem lin_map (hρ : ∀ E, FormsTie σ j H E (ρ E)) (op : MonoidAlgebra K G → Matrix (Fin n) (Fin n) K)
    (hadd : ∀ a b, op (a + b) = op a + op b) (hsmul : ∀ (c : K) a, op (c • a) = c • op a) (a : MonoidAlgebra K G) :
    lin ρ op (mapRingHom G σ a) = ρ (op a) := by
  let opL : MonoidAlgebra K G →ₗ[K] Matrix (Fin n) (Fin n) K := ⟨⟨op, hadd⟩, hsmul⟩
  change _ = ρ (opL a)
  conv_rhs => rw [eq_sum_single a]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  have h1 : single g (a.coeff g) = a.coeff g • single g (1 : K) := by rw [smul_single, smul_eq_mul, mul_one]
  rw [h1, map_smul, rho_smul hρ, coeff_mapRingHom]
  rfl

theorem lin_mul (hρ : ∀ E, FormsTie σ j H E (ρ E)) (op : MonoidAlgebra K G → Matrix (Fin n) (Fin n) K)
    (hadd : ∀ a b, op (a + b) = op a + op b) (hsmul : ∀ (c : K) a, op (c • a) = c • op a)
    (hmul : ∀ a ∈ Subalgebra.center K (MonoidAlgebra K G), ∀ b ∈ Subalgebra.center K (MonoidAlgebra K G),
      op (a * b) = op a * op b)
    (z w : MonoidAlgebra ℂ G) (hz : z ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G))
    (hw : w ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G)) : lin ρ op (z * w) = lin ρ op z * lin ρ op w := by
  have hone : ∀ α : G → ℂ, lin ρ op (∑ g, α g • conjSum ℂ g) = ∑ g, α g • ρ (op (conjSum K g)) := fun α => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, ← mapRange_conjSum σ, lin_map hρ op hadd hsmul]
  have key : ∀ α β : G → ℂ, lin ρ op ((∑ g, α g • conjSum ℂ g) * ∑ h, β h • conjSum ℂ h) =
      lin ρ op (∑ g, α g • conjSum ℂ g) * lin ρ op (∑ h, β h • conjSum ℂ h) := fun α β => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hone, hone, Finset.sum_mul_sum, Finset.sum_mul_sum, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [smul_mul_smul_comm, smul_mul_smul_comm, map_smul, ← mapRange_conjSum σ, ← mapRange_conjSum σ, ← map_mul,
      lin_map hρ op hadd hsmul, hmul _ (conjSum_mem_center K g) _ (conjSum_mem_center K h), map_mul]
  have h := key z.coeff w.coeff
  rw [← card_smul_eq z hz, ← card_smul_eq w hw, smul_mul_smul_comm, map_smul, map_smul, map_smul,
    smul_mul_smul_comm] at h
  have hc : ((Fintype.card G : ℂ) * (Fintype.card G : ℂ)) ≠ 0 := by
    have : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    exact mul_ne_zero this this
  exact smul_right_injective _ hc h

noncomputable def actC (hρ : ∀ E, FormsTie σ j H E (ρ E)) (op : MonoidAlgebra K G → Matrix (Fin n) (Fin n) K)
    (hadd : ∀ a b, op (a + b) = op a + op b) (hsmul : ∀ (c : K) a, op (c • a) = c • op a)
    (hmul : ∀ a ∈ Subalgebra.center K (MonoidAlgebra K G), ∀ b ∈ Subalgebra.center K (MonoidAlgebra K G),
      op (a * b) = op a * op b) (hone : op 1 = 1) :
    Subalgebra.center ℂ (MonoidAlgebra ℂ G) →ₐ[ℂ] Module.End ℂ (EuclideanSpace ℂ (Fin n)) where
  toFun z := lin ρ op z
  map_one' := by
    change lin ρ op 1 = 1
    rw [← map_one (mapRingHom G σ), lin_map hρ op hadd hsmul, hone, map_one]
  map_mul' z w := lin_mul hρ op hadd hsmul hmul z w z.2 w.2
  map_zero' := map_zero _
  map_add' z w := map_add _ _ _
  commutes' c := by
    change lin ρ op (algebraMap ℂ (MonoidAlgebra ℂ G) c) = _
    rw [Algebra.algebraMap_eq_smul_one, map_smul, ← map_one (mapRingHom G σ), lin_map hρ op hadd hsmul, hone, map_one,
      Algebra.algebraMap_eq_smul_one]

end Act

end GlobalTheory.Mem.R3.Rw.SpOfMat

namespace GlobalTheory.Mem.R3.Rw.SpOfMat

open MonoidAlgebra

theorem exists_complexification_of_definiteGroupForms : ∀ (K O : Type) [Field K] [NumberField K] [StarRing K] [CommRing O] (o : O →+* K) (σ : K →+* ℂ) (G : Type) [Group G] [Fintype G] (m : Mat1 K G) (e : MonoidAlgebra K G), (∀ x, σ (star x) = starRingEnd ℂ (σ x)) → (∀ y, IsIntegral ℤ (o y)) → m.Laws σ e → ∃ s : Sp1 O (σ.comp o) G, Nonempty (Tie1 σ m s) := by
  intro K O _ _ _ _ o σ G _ _ m e hσ ho hm
  obtain ⟨j, M, ρ, hρ, hM, hcar⟩ :=
    GlobalTheory.Mem.CoordForms.exists_formsTie_oLatTie K O o σ m.n m.H m.N hσ hm.pos hm.lat
  have hcar' := hcar ho
  have hEE : m.E * m.E = m.E := by
    rw [hm.E_eq, ← hm.mul e hm.cen e hm.cen, hm.idem.eq]
  let s : Sp1 O (σ.comp o) G :=
    { A := Hs.mk (EuclideanSpace ℂ (Fin m.n))
      lat := M
      e := ρ m.E
      idem := by rw [← Module.End.mul_eq_comp, ← map_mul, hEE]
      sa := rho_symm hρ m.E hm.sa
      act := actC hρ m.op hm.add hm.smul hm.mul hm.one }
  refine ⟨s, ⟨{ j := j, forms := hρ m.E, latT := hM, stable := ?_, cen := ?_ }⟩⟩
  · intro a y hy
    change y ∈ (M.carrier : Set (EuclideanSpace ℂ (Fin m.n))) at hy
    change σ (a : K) • y ∈ (M.carrier : Set (EuclideanSpace ℂ (Fin m.n)))
    rw [hcar'] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨(a : K) • x, ?_, by rw [map_smulₛₗ]⟩
    have := m.N.smul_mem a hx
    rwa [← algebraMap_smul K] at this
  · intro z a hza x
    have hz : (z : MonoidAlgebra ℂ G) = mapRingHom G σ a := by
      apply MonoidAlgebra.ext
      ext g
      rw [coeff_mapRingHom]
      exact (hza g).symm
    change lin ρ m.op z (j x) = _
    rw [hz, lin_map hρ m.op hm.add hm.smul, (hρ _).op_eq]

end GlobalTheory.Mem.R3.Rw.SpOfMat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsJW
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.Mem.CoordW


set_option maxHeartbeats 2000000 in
theorem exists_jW : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ mj : GlobalTheory.RealGeo.MjTie R.toRealDat F.lv2, ∃ jW : ∀ i : Fin D.R.m, (Fin (((R.toCx3 F).data F.cr false).dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1), ∀ (i : Fin D.R.m) v, mj.eW i (jW i v) = (R.FW i).j (sg0 D A3.A) (Fintype.linearCombination D.what₂.LL (R.toRealDat.bL F.lv2 false i) v) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH mj
  have key : ∀ i : Fin D.R.m, ∃ g : (Fin (((R.toCx3 F).data F.cr false).dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL]
      D.what₂.Mj ((i : ℕ) + 1), ∀ v, mj.eW i (g v) = GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i v := by
    intro i
    have he : Function.Injective (mj.eW i) :=
      GlobalTheory.Mem.LiftForms.inj_of_norm_sq _ (RealDat.nP_pos (F := F.lv2) false) (mj.eW_norm i)
    have hspan : Submodule.span ℂ (Set.range fun k =>
        GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i (Pi.single k 1)) = LinearMap.range (mj.eW i) :=
      (GlobalTheory.Mem.LiftTheta.goodForm_span R.toRealDat F.lv2 false i).trans
        ((hH.aux.levelW false i _).trans (mj.eW_range i).symm)
    have hmem : ∀ v, GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i v ∈ LinearMap.range (mj.eW i) := by
      intro v
      rw [← hspan, GlobalTheory.Mem.LiftTheta.semi_expand]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    choose s hs using fun v => LinearMap.mem_range.1 (hmem v)
    exact ⟨{ toFun := s
             map_add' := fun a b => he ((hs (a + b)).trans (((map_add _ a b).trans
               (congrArg₂ (· + ·) (hs a).symm (hs b).symm)).trans (map_add (mj.eW i) (s a) (s b)).symm))
             map_smul' := fun c a => he ((hs (c • a)).trans (((LinearMap.map_smulₛₗ _ c a).trans
               (congrArg (D.what₂.embLL c • ·) (hs a).symm)).trans (LinearMap.map_smul (mj.eW i) _ (s a)).symm)) }, hs⟩
  choose jW hjW using key
  exact ⟨jW, fun i v => (hjW i v).trans
    (congrArg ((R.FW i).j (sg0 D A3.A)) (Fintype.linearCombination_apply _ _ _).symm)⟩

end GlobalTheory.Mem.CoordW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HdExists
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw.HdExist

theorem hd_exists : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → D.host.F = maximalRealSubfield D.host.E → Seed.FrmC.StdLat (Yc D 0) → (∀ i, Seed.FrmC.StdLat (Wc D i)) → ∀ (tup : T → D.what₂.Tup) (tupT : D.what₂.Tup → T), (∀ t, tupT (tup t) = t) → tup A3.A.μ0 = D.what₂.mu0 → ∃ y : Hd R.toRealDat, y.tup = tup ∧ y.tupT = tupT := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hF hY hW tup tupT htt ht0
  have hB : R.toRealDat.BaseW F.lv2 := hP.char.base
  obtain ⟨hTop, hinj⟩ := GlobalTheory.DefiniteMult.topMult_and_extV_injective D G Pl0 T A3.A Ks R.toRealDat F.lv2 hB
  obtain ⟨PY, PW, ιW, hPY, hPW, hiso, hmatch⟩ := GlobalTheory.StdFrameExist.frames_std_matched D hF hY hW
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  exact ⟨⟨tup, tupT, htt, ht0, hm, hTop, hinj, PY, PW, ιW, hiso, hmatch, hF, hPY, hPW⟩, rfl, rfl⟩

end GlobalTheory.Mem.R3.Rw.HdExist
end

