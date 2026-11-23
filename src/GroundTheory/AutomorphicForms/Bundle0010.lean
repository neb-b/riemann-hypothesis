module

public import Mathlib
public import GroundTheory.GlobalFields.IdeleGroups.Restricted
public import GroundTheory.AutomorphicForms.SmoothRep

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.RestrictedProductMatrix
section
namespace GroundTheory.Automorphic

open Filter Topology Set
open scoped RestrictedProduct

noncomputable section

section Units

variable {A B : Type*} [Monoid A] [Monoid B] [TopologicalSpace A] [TopologicalSpace B]

def unitsCongr (e : A ≃* B) (he : Continuous e) (he' : Continuous e.symm) : Aˣ ≃ₜ* Bˣ where
  toMulEquiv := Units.mapEquiv e
  continuous_toFun :=
    Units.continuous_iff.2 ⟨he.comp Units.continuous_val, he.comp Units.continuous_coe_inv⟩
  continuous_invFun :=
    Units.continuous_iff.2 ⟨he'.comp Units.continuous_val, he'.comp Units.continuous_coe_inv⟩

end Units

section Prod

variable (m : Type*) [Fintype m] (R₁ R₂ : Type*) [Ring R₁] [Ring R₂]

def matrixProdRingEquiv : Matrix m m (R₁ × R₂) ≃+* Matrix m m R₁ × Matrix m m R₂ where
  toFun M := (M.map Prod.fst, M.map Prod.snd)
  invFun p := Matrix.of fun a b => (p.1 a b, p.2 a b)
  left_inv M := rfl
  right_inv p := rfl
  map_mul' M N := by
    ext a b
    · change ((M * N) a b).1 = (M.map Prod.fst * N.map Prod.fst) a b
      simp [Matrix.mul_apply, Prod.fst_sum]
    · change ((M * N) a b).2 = (M.map Prod.snd * N.map Prod.snd) a b
      simp [Matrix.mul_apply, Prod.snd_sum]
  map_add' M N := rfl

variable [TopologicalSpace R₁] [TopologicalSpace R₂]

theorem continuous_matrixProdRingEquiv : Continuous (matrixProdRingEquiv m R₁ R₂) :=
  (continuous_pi fun a => continuous_pi fun b =>
      continuous_fst.comp ((continuous_apply b).comp (continuous_apply a))).prodMk
    (continuous_pi fun a => continuous_pi fun b =>
      continuous_snd.comp ((continuous_apply b).comp (continuous_apply a)))

theorem continuous_matrixProdRingEquiv_symm : Continuous (matrixProdRingEquiv m R₁ R₂).symm :=
  continuous_pi fun a => continuous_pi fun b =>
    ((continuous_apply_apply a b).comp continuous_fst).prodMk
      ((continuous_apply_apply a b).comp continuous_snd)

variable [DecidableEq m]

def glProdEquiv : GL m (R₁ × R₂) ≃ₜ* GL m R₁ × GL m R₂ :=
  (unitsCongr (matrixProdRingEquiv m R₁ R₂).toMulEquiv (continuous_matrixProdRingEquiv m R₁ R₂)
    (continuous_matrixProdRingEquiv_symm m R₁ R₂)).trans
    { toMulEquiv := MulEquiv.prodUnits
      continuous_toFun := (Homeomorph.prodUnits (α := Matrix m m R₁)
        (β := Matrix m m R₂)).continuous_toFun
      continuous_invFun := (Homeomorph.prodUnits (α := Matrix m m R₁)
        (β := Matrix m m R₂)).continuous_invFun }

end Prod

section Pi

variable (m : Type*) [Fintype m] {ι : Type*} (R : ι → Type*) [∀ j, Ring (R j)]

def matrixPiRingEquiv : Matrix m m (Π j, R j) ≃+* Π j, Matrix m m (R j) where
  toFun M j := Matrix.of fun a b => M a b j
  invFun p := Matrix.of fun a b j => p j a b
  left_inv M := rfl
  right_inv p := rfl
  map_mul' M N := by
    ext j a b
    simp [Matrix.mul_apply, Finset.sum_apply]
  map_add' M N := rfl

variable [∀ j, TopologicalSpace (R j)]

theorem continuous_matrixPiRingEquiv : Continuous (matrixPiRingEquiv m R) :=
  continuous_pi fun j => continuous_pi fun a => continuous_pi fun b =>
    (continuous_apply j).comp ((continuous_apply b).comp (continuous_apply a))

theorem continuous_matrixPiRingEquiv_symm : Continuous (matrixPiRingEquiv m R).symm :=
  continuous_pi fun a => continuous_pi fun b => continuous_pi fun j =>
    (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply j))

variable [DecidableEq m]

def glPiEquiv : GL m (Π j, R j) ≃ₜ* Π j, GL m (R j) :=
  (unitsCongr (matrixPiRingEquiv m R).toMulEquiv (continuous_matrixPiRingEquiv m R)
    (continuous_matrixPiRingEquiv_symm m R)).trans ContinuousMulEquiv.piUnits

end Pi

namespace RestrictedProduct

variable {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)]

def congrSets {A A' : (i : ι) → Set (R i)} (h : ∀ i, A i = A' i) :
    Πʳ i, [R i, A i] ≃ₜ Πʳ i, [R i, A' i] where
  toFun x := _root_.RestrictedProduct.mk x.1 (x.2.mono fun i hi =>
    (congrArg (x.1 i ∈ ·) (h i)).mp hi)
  invFun x := _root_.RestrictedProduct.mk x.1 (x.2.mono fun i hi =>
    (congrArg (x.1 i ∈ ·) (h i)).mpr hi)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    _root_.RestrictedProduct.mapAlong_continuous R R id tendsto_id (A₁ := A) (A₂ := A')
      (fun _ x => x) (.of_forall fun i x hx => (congrArg (x ∈ ·) (h i)).mp hx)
      fun _ => continuous_id
  continuous_invFun :=
    _root_.RestrictedProduct.mapAlong_continuous R R id tendsto_id (A₁ := A') (A₂ := A)
      (fun _ x => x) (.of_forall fun i x hx => (congrArg (x ∈ ·) (h i)).mpr hx)
      fun _ => continuous_id

def congrSetsMul [∀ i, Monoid (R i)] {S S' : ι → Type*} [∀ i, SetLike (S i) (R i)]
    [∀ i, SubmonoidClass (S i) (R i)] [∀ i, SetLike (S' i) (R i)]
    [∀ i, SubmonoidClass (S' i) (R i)] {B : Π i, S i} {B' : Π i, S' i}
    (h : ∀ i, (B i : Set (R i)) = B' i) :
    Πʳ i, [R i, B i] ≃ₜ* Πʳ i, [R i, B' i] where
  toEquiv := (congrSets h).toEquiv
  map_mul' _ _ := rfl
  continuous_toFun := (congrSets h).continuous
  continuous_invFun := (congrSets h).symm.continuous

section Pi

variable (m : Type*) [Finite m] {A : (i : ι) → Set (R i)}

def piEquiv (hA : ∀ i, IsOpen (A i)) :
    (m → Πʳ i, [R i, A i]) ≃ₜ Πʳ i, [m → R i, Set.pi univ fun _ => A i] where
  toFun x := _root_.RestrictedProduct.mk (A := fun i => Set.pi univ fun _ => A i)
    (fun i a => x a i)
    (((eventually_all (ι := m)).2 fun a => (x a).2).mono fun _ hi a _ => hi a)
  invFun y a := _root_.RestrictedProduct.mk (A := A) (fun i => y i a)
    (y.2.mono fun _ hi => hi a (mem_univ a))
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    refine (_root_.RestrictedProduct.continuous_dom_pi (A := fun _ i => R i)
      (C := fun _ i => A i) fun _ => hA).2 fun S hS => ?_
    exact (_root_.RestrictedProduct.continuous_inclusion hS).comp
      (f := fun x : (m → Πʳ i, [R i, A i]_[𝓟 S]) =>
        _root_.RestrictedProduct.mk (A := fun i => Set.pi univ fun _ => A i) (𝓕 := 𝓟 S)
          (fun i a => x a i) (eventually_principal.2 fun i hi a _ =>
            eventually_principal.1 (x a).2 i hi))
      (_root_.RestrictedProduct.continuous_rng_of_principal.2
        (continuous_pi fun i => continuous_pi fun a =>
          (_root_.RestrictedProduct.continuous_eval i).comp (continuous_apply a)))
  continuous_invFun := continuous_pi fun a =>
    _root_.RestrictedProduct.mapAlong_continuous (fun i => m → R i) R id tendsto_id
      (A₁ := fun i => Set.pi univ fun _ => A i) (A₂ := A)
      (fun _ y => y a) (.of_forall fun _ _ hy => hy a (mem_univ a)) fun _ => continuous_apply a

end Pi

section Matrix

variable (m : Type*) [Fintype m] [DecidableEq m]

def matrixHomeomorphSets {A : (i : ι) → Set (R i)} (hA : ∀ i, IsOpen (A i)) :
    Matrix m m (Πʳ i, [R i, A i]) ≃ₜ Πʳ i, [Matrix m m (R i), {M | ∀ a b, M a b ∈ A i}] :=
  ((Homeomorph.piCongrRight fun _ : m => piEquiv m hA).trans
    (piEquiv m fun i => isOpen_set_pi finite_univ fun _ _ => hA i)).trans
    (congrSets fun _ => Set.ext fun _ =>
      ⟨fun h a b => h a (mem_univ a) b (mem_univ b), fun h a _ b _ => h a b⟩)

variable [∀ i, Ring (R i)] {S : ι → Type*} [∀ i, SetLike (S i) (R i)]
  [∀ i, SubringClass (S i) (R i)] {B : Π i, S i} {C : Π i, Subring (Matrix m m (R i))}

def matrixRingEquiv (hC : ∀ i (M : Matrix m m (R i)), M ∈ C i ↔ ∀ a b, M a b ∈ B i) :
    Matrix m m (Πʳ i, [R i, B i]) ≃+* Πʳ i, [Matrix m m (R i), C i] where
  toFun M := _root_.RestrictedProduct.mk (A := fun i => (C i : Set (Matrix m m (R i))))
    (fun i => Matrix.of fun a b => M a b i)
    (((eventually_all (ι := m)).2 fun a => (eventually_all (ι := m)).2 fun b =>
      (M a b).2).mono fun i hi => (hC i _).2 fun a b => hi a b)
  invFun x := Matrix.of fun a b =>
    _root_.RestrictedProduct.mk (A := fun i => (B i : Set (R i))) (fun i => x i a b)
      (x.2.mono fun i hi => (hC i _).1 hi a b)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' M N := by
    ext i a b
    change (M * N) a b i = ((Matrix.of fun a b => M a b i) * Matrix.of fun a b => N a b i) a b
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact map_sum (_root_.RestrictedProduct.evalRingHom R i) _ _
  map_add' _ _ := rfl


omit [∀ i, TopologicalSpace (R i)] [∀ i, SubringClass (S i) (R i)] in
theorem coe_eq_setOf (hC : ∀ i (M : Matrix m m (R i)), M ∈ C i ↔ ∀ a b, M a b ∈ B i) (i : ι) :
    (C i : Set (Matrix m m (R i))) = {M | ∀ a b, M a b ∈ B i} :=
  Set.ext fun M => hC i M

def matrixHomeomorph (hC : ∀ i (M : Matrix m m (R i)), M ∈ C i ↔ ∀ a b, M a b ∈ B i)
    (hB : ∀ i, IsOpen (B i : Set (R i))) :
    Matrix m m (Πʳ i, [R i, B i]) ≃ₜ Πʳ i, [Matrix m m (R i), C i] :=
  (matrixHomeomorphSets m hB).trans (congrSets fun i => (coe_eq_setOf m hC i).symm)


omit [∀ i, SubringClass (S i) (R i)] in
theorem isOpen_coe_of_forall (hC : ∀ i (M : Matrix m m (R i)), M ∈ C i ↔ ∀ a b, M a b ∈ B i)
    (hB : ∀ i, IsOpen (B i : Set (R i))) (i : ι) : IsOpen (C i : Set (Matrix m m (R i))) := by
  rw [coe_eq_setOf m hC i]
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
    (hB i).preimage (continuous_apply_apply a b)

def matrixUnitsEquiv (hC : ∀ i (M : Matrix m m (R i)), M ∈ C i ↔ ∀ a b, M a b ∈ B i)
    (hB : ∀ i, IsOpen (B i : Set (R i))) :
    GL m (Πʳ i, [R i, B i]) ≃ₜ* Πʳ i, [GL m (R i), (Submonoid.ofClass (C i)).units] :=
  (unitsCongr (matrixRingEquiv m hC).toMulEquiv (matrixHomeomorph m hC hB).continuous
    (matrixHomeomorph m hC hB).symm.continuous).trans
    (GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv (isOpen_coe_of_forall m hC hB))

end Matrix

end RestrictedProduct

end

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.SmoothRepContragredient
section
noncomputable section

namespace GroundTheory.Automorphic

open Set Filter Topology

section General

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V)

theorem dual_apply_apply (g : G) (f : Module.Dual ℂ V) (v : V) :
    Representation.dual ρ g f v = f (ρ g⁻¹ v) := rfl


variable {ρ} in
theorem mem_fixedVectors_dual {H : Subgroup G} {f : Module.Dual ℂ V} :
    f ∈ fixedVectors (Representation.dual ρ) H ↔ ∀ h ∈ H, ∀ v, f (ρ h v) = f v := by
  constructor
  · intro hf h hh v
    have := LinearMap.congr_fun (hf h⁻¹ (inv_mem hh)) v
    rwa [dual_apply_apply, inv_inv] at this
  · intro hf h hh
    ext v
    rw [dual_apply_apply]
    exact hf _ (inv_mem hh) v

variable [TopologicalSpace G] [IsTopologicalGroup G]


variable {ρ} in
theorem mem_smoothVectors_of_mem_fixedVectors {H : Subgroup G} (hH : IsOpen (H : Set G))
    {v : V} (hv : v ∈ fixedVectors ρ H) : v ∈ smoothVectors ρ :=
  Subgroup.isOpen_mono (mem_fixedVectors_iff_le.1 hv) hH

variable {ρ} in
theorem mem_fixedVectors_smoothPart {H : Subgroup G} {x : smoothVectors ρ} :
    x ∈ fixedVectors (smoothPart ρ) H ↔ (x : V) ∈ fixedVectors ρ H := by
  simp only [mem_fixedVectors, Subtype.ext_iff, coe_smoothPart_apply]

def contragredient : Representation ℂ G (smoothVectors (Representation.dual ρ)) :=
  smoothPart (Representation.dual ρ)

theorem contragredient_apply_apply (g : G) (x : smoothVectors (Representation.dual ρ)) (v : V) :
    ((contragredient ρ g x : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) v =
      (x : Module.Dual ℂ V) (ρ g⁻¹ v) := rfl

theorem isSmooth_contragredient : IsSmooth (contragredient ρ) :=
  isSmooth_smoothPart _

variable {ρ} in
theorem mem_fixedVectors_contragredient {H : Subgroup G}
    {x : smoothVectors (Representation.dual ρ)} :
    x ∈ fixedVectors (contragredient ρ) H ↔
      ∀ h ∈ H, ∀ v, (x : Module.Dual ℂ V) (ρ h v) = (x : Module.Dual ℂ V) v :=
  mem_fixedVectors_smoothPart.trans mem_fixedVectors_dual

def restrictFixed (H : Subgroup G) :
    fixedVectors (contragredient ρ) H →ₗ[ℂ] Module.Dual ℂ (fixedVectors ρ H) :=
  (fixedVectors ρ H).subtype.dualMap ∘ₗ (smoothVectors (Representation.dual ρ)).subtype ∘ₗ
    (fixedVectors (contragredient ρ) H).subtype

theorem restrictFixed_apply (H : Subgroup G) (x : fixedVectors (contragredient ρ) H)
    (v : fixedVectors ρ H) :
    restrictFixed ρ H x v =
      ((x : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) v := rfl

def evalSmooth : V →ₗ[ℂ] Module.Dual ℂ (smoothVectors (Representation.dual ρ)) :=
  (smoothVectors (Representation.dual ρ)).subtype.dualMap ∘ₗ Module.Dual.eval ℂ V

theorem evalSmooth_apply (v : V) (x : smoothVectors (Representation.dual ρ)) :
    evalSmooth ρ v x = (x : Module.Dual ℂ V) v := rfl


variable {ρ} in
theorem evalSmooth_mem {v : V} (hv : v ∈ smoothVectors ρ) :
    evalSmooth ρ v ∈ smoothVectors (Representation.dual (contragredient ρ)) := by
  refine Subgroup.isOpen_mono (H₁ := stabilizerOf ρ v) (fun g hg => ?_) hv
  rw [mem_stabilizerOf] at hg ⊢
  ext x
  rw [dual_apply_apply, evalSmooth_apply, evalSmooth_apply, contragredient_apply_apply, inv_inv,
    hg]


variable {ρ} in
def toDoubleContragredient (hρ : IsSmooth ρ) :
    Representation.IntertwiningMap ρ (contragredient (contragredient ρ)) where
  toLinearMap := (evalSmooth ρ).codRestrict _ fun v => evalSmooth_mem (hρ v)
  isIntertwining' g := by
    refine LinearMap.ext fun v => Subtype.ext (LinearMap.ext fun x => ?_)
    change (x : Module.Dual ℂ V) (ρ g v) = (x : Module.Dual ℂ V) (ρ g⁻¹⁻¹ v)
    rw [inv_inv]

end General

section LocallyProfinite

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}

def extendFixed (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    (μ : Module.Dual ℂ (fixedVectors ρ K)) : fixedVectors (contragredient ρ) K :=
  have hinv : ∀ k ∈ K, ∀ v, (μ ∘ₗ fixedProj ρ hρ hKc hKo) (ρ k v) =
      (μ ∘ₗ fixedProj ρ hρ hKc hKo) v := fun k hk v => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, fixedProj_apply_act hρ hKc hKo hk]
  ⟨⟨μ ∘ₗ fixedProj ρ hρ hKc hKo,
    mem_smoothVectors_of_mem_fixedVectors hKo (mem_fixedVectors_dual.2 hinv)⟩,
    mem_fixedVectors_contragredient.2 hinv⟩

variable (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
include hρ hKc hKo

theorem restrictFixed_bijective : Function.Bijective (restrictFixed ρ K) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hx' : ((x : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) = 0 :=
      eq_of_invariant_of_eqOn hρ hKc hKo (mem_fixedVectors_contragredient.1 x.2)
        (fun _ _ _ => rfl) fun v hv => LinearMap.congr_fun hx ⟨v, hv⟩
    exact Subtype.ext (Subtype.ext hx')
  · intro μ
    refine ⟨extendFixed hρ hKc hKo μ, LinearMap.ext fun v => ?_⟩
    change μ (fixedProj ρ hρ hKc hKo v) = μ v
    rw [Subtype.ext (fixedProj_apply_of_mem hρ hKc hKo v.2)]

def fixedContragredientEquiv :
    fixedVectors (contragredient ρ) K ≃ₗ[ℂ] Module.Dual ℂ (fixedVectors ρ K) :=
  LinearEquiv.ofBijective (restrictFixed ρ K) (restrictFixed_bijective hρ hKc hKo)

theorem fixedContragredientEquiv_apply (x : fixedVectors (contragredient ρ) K) :
    fixedContragredientEquiv hρ hKc hKo x = restrictFixed ρ K x := rfl

end LocallyProfinite

section Admissible

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

theorem isAdmissible_contragredient (h : IsAdmissible ρ) : IsAdmissible (contragredient ρ) := by
  refine ⟨isSmooth_contragredient ρ, fun K hKc hKo => ?_⟩
  have := h.2 K hKc hKo
  exact LinearEquiv.finiteDimensional (fixedContragredientEquiv h.1 hKc hKo).symm

theorem toDoubleContragredient_bijective (h : IsAdmissible ρ) :
    Function.Bijective (toDoubleContragredient h.1) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro v hv
    obtain ⟨K, hKc, hKo, hvK⟩ := (isSmooth_iff_forall_exists ρ).1 h.1 v
    set e := fixedContragredientEquiv h.1 hKc hKo
    have hzero : (⟨v, hvK⟩ : fixedVectors ρ K) = 0 := by
      refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun μ => ?_
      have h1 : (((e.symm μ : fixedVectors (contragredient ρ) K) :
          smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) v = 0 := by
        have := congrArg (fun Φ : smoothVectors (Representation.dual (contragredient ρ)) =>
          (Φ : Module.Dual ℂ (smoothVectors (Representation.dual ρ)))
            (e.symm μ : fixedVectors (contragredient ρ) K)) hv
        exact this
      have h2 : e (e.symm μ) = μ := e.apply_symm_apply μ
      rw [← h2, fixedContragredientEquiv_apply, restrictFixed_apply]
      exact h1
    simpa using congrArg Subtype.val hzero
  · intro Φ
    obtain ⟨K, hKc, hKo, hΦK⟩ := (mem_smoothVectors_iff _).1 Φ.2
    set e := fixedContragredientEquiv h.1 hKc hKo
    have := h.2 K hKc hKo
    let ψ : Module.Dual ℂ (Module.Dual ℂ (fixedVectors ρ K)) :=
      (Φ : Module.Dual ℂ (smoothVectors (Representation.dual ρ))) ∘ₗ
        (fixedVectors (contragredient ρ) K).subtype ∘ₗ e.symm.toLinearMap
    set w := (Module.evalEquiv ℂ (fixedVectors ρ K)).symm ψ
    have hw : ∀ μ : Module.Dual ℂ (fixedVectors ρ K), μ w = ψ μ := fun μ =>
      LinearMap.congr_fun ((Module.evalEquiv ℂ (fixedVectors ρ K)).apply_symm_apply ψ) μ
    refine ⟨(w : V), Subtype.ext ?_⟩
    refine eq_of_invariant_of_eqOn (isSmooth_contragredient ρ) hKc hKo (fun k hk x => ?_)
      (mem_fixedVectors_dual.1 hΦK) fun x hx => ?_
    · change (x : Module.Dual ℂ V) (ρ k⁻¹ w) = (x : Module.Dual ℂ V) w
      rw [w.2 _ (inv_mem hk)]
    · have h1 : (Φ : Module.Dual ℂ (smoothVectors (Representation.dual ρ))) x =
          ψ (e ⟨x, hx⟩) := by
        simp [ψ]
      rw [h1, ← hw]
      rfl

end Admissible

end GroundTheory.Automorphic
end
end

