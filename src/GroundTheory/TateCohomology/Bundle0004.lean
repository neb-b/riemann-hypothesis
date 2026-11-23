module

public import Mathlib
public import GroundTheory.TateCohomology.Bundle0003
public import GroundTheory.TateCohomology.TateLow
public import GroundTheory.TateCohomology.Bundle0001

@[expose] public section

-- bundled from GroundTheory.TateCohomology.CupConnecting
section
set_option maxSynthPendingDepth 1

noncomputable section

universe u

open CategoryTheory MonoidalCategory TensorProduct groupCohomology Limits

namespace GroundTheory.GroupCoh

variable {k G : Type u} [CommRing k] [Group G]

section Whisker

variable {A A' B B' : Rep k G} {p q n : ℕ}

theorem whiskerRight_tmul (φ : A ⟶ A') (a : A) (b : B) :
    (φ ▷ B).hom (a ⊗ₜ[k] b : (A ⊗ B : Rep k G)) = φ.hom a ⊗ₜ[k] b :=
  rfl

theorem whiskerLeft_tmul (ψ : B ⟶ B') (a : A) (b : B) :
    (A ◁ ψ).hom (a ⊗ₜ[k] b : (A ⊗ B : Rep k G)) = a ⊗ₜ[k] ψ.hom b :=
  rfl

theorem whiskerRight_cupCochain (φ : A ⟶ A') (h : p + q = n) (f : (Fin p → G) → A)
    (g : (Fin q → G) → B) (x : Fin n → G) :
    (φ ▷ B).hom (cupCochain h f g x) = cupCochain h (fun v => φ.hom (f v)) g x := by
  rw [cupCochain_apply, whiskerRight_tmul, cupCochain_apply]

theorem whiskerLeft_cupCochain (ψ : B ⟶ B') (h : p + q = n) (f : (Fin p → G) → A)
    (g : (Fin q → G) → B) (x : Fin n → G) :
    (A ◁ ψ).hom (cupCochain h f g x) = cupCochain h f (fun v => ψ.hom (g v)) x := by
  rw [cupCochain_apply, whiskerLeft_tmul, cupCochain_apply, Rep.hom_comm_apply]

end Whisker

section Connecting

variable {X : ShortComplex (Rep k G)} (hX : X.ShortExact)

theorem comp_d_apply {A A' : Rep k G} (φ : A ⟶ A') (i : ℕ) (y : (Fin i → G) → A)
    (v : Fin (i + 1) → G) :
    φ.hom ((inhomogeneousCochains.d A i).hom y v) =
      (inhomogeneousCochains.d A' i).hom (fun u => φ.hom (y u)) v := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [inhomogeneousCochains.d_hom_apply, map_add (f := _), map_sum, map_smul, Rep.hom_comm_apply]


include hX in
theorem δ_π_eq {p : ℕ} (z : cocycles X.X₃ p) (y : (Fin p → G) → X.X₂)
    (hy : ∀ v, X.g.hom (y v) = iCocycles X.X₃ p z v) (x : cocycles X.X₁ (p + 1))
    (hx : ∀ v, X.f.hom (iCocycles X.X₁ (p + 1) x v) = (inhomogeneousCochains.d X.X₂ p).hom y v) :
    δ hX p (p + 1) rfl (π X.X₃ p z) = π X.X₁ (p + 1) x := by
  have h1 := δ_apply hX rfl (iCocycles X.X₃ p z) (by simpa using d_iCocycles z) y
    (funext hy) (iCocycles X.X₁ (p + 1) x) (funext fun v => by simpa using hx v)
  have e1 : cocyclesMk (iCocycles X.X₃ p z) (d_iCocycles z) = z := cocycles_ext (iCocycles_mk _ _)
  rw [e1] at h1
  rw [h1]
  congr 1
  exact cocycles_ext (iCocycles_mk _ _)


include hX in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem exists_f_eq_of_g_eq_zero (e : X.X₂) (he : X.g.hom e = 0) : ∃ a : X.X₁, X.f.hom a = e := by
  have : LinearMap.range X.f.hom.toLinearMap = LinearMap.ker X.g.hom.toLinearMap :=
    (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
  have hmem : e ∈ LinearMap.range X.f.hom.toLinearMap := this ▸ LinearMap.mem_ker.2 he
  obtain ⟨a, ha⟩ := hmem
  exact ⟨a, ha⟩


include hX in
theorem exists_lift_of_cocycle {p : ℕ} (z : cocycles X.X₃ p) :
    ∃ (y : (Fin p → G) → X.X₂) (x : cocycles X.X₁ (p + 1)),
      (∀ v, X.g.hom (y v) = iCocycles X.X₃ p z v) ∧
        ∀ v, X.f.hom (iCocycles X.X₁ (p + 1) x v) =
          (inhomogeneousCochains.d X.X₂ p).hom y v := by
  have hg : Function.Surjective X.g.hom := (Rep.epi_iff_surjective X.g).1 hX.epi_g
  have hf : Function.Injective X.f.hom := (Rep.mono_iff_injective X.f).1 hX.mono_f
  choose y hy using fun v => hg (iCocycles X.X₃ p z v)
  have hdy : ∀ v, X.g.hom ((inhomogeneousCochains.d X.X₂ p).hom y v) = 0 := fun v => by
    rw [comp_d_apply, show (fun u => X.g.hom (y u)) = iCocycles X.X₃ p z from funext hy,
      d_iCocycles]
    rfl
  choose x hx using fun v => exists_f_eq_of_g_eq_zero hX _ (hdy v)
  have hdx : (inhomogeneousCochains.d X.X₁ (p + 1)).hom x = 0 := by
    funext v
    apply hf
    rw [comp_d_apply, show (fun u => X.f.hom (x u)) = (inhomogeneousCochains.d X.X₂ p).hom y
      from funext hx, Pi.zero_apply, map_zero]
    exact congr(($(inhomogeneousCochains.d_comp_d (n := p) (A := X.X₂))).hom y v)
  exact ⟨y, cocyclesMk x hdx, hy, fun v => by rw [iCocycles_mk]; exact hx v⟩

variable (B : Rep k G)

theorem δ_cupH_left (hXB : (X.map (tensorRight B)).ShortExact) {p q n : ℕ} (h : p + q = n)
    (h' : p + 1 + q = n + 1) (a : groupCohomology X.X₃ p) (b : groupCohomology B q) :
    δ hXB n (n + 1) rfl (cupH h a b) = cupH h' (δ hX p (p + 1) rfl a) b := by
  refine groupCohomology_induction_on a fun z => ?_
  refine groupCohomology_induction_on b fun w => ?_
  obtain ⟨y, x, hy, hx⟩ := exists_lift_of_cocycle hX z
  rw [δ_π_eq hX z y hy x hx, cupH_π, cupH_π]
  subst h
  refine δ_π_eq hXB (cupCocycles rfl z w) (cupCochain rfl y (iCocycles B q w)) (fun v => ?_)
    (cupCocycles h' x w) (fun v => ?_)
  · change (X.g ▷ B).hom (cupCochain rfl y (iCocycles B q w) v) =
      iCocycles (X.X₃ ⊗ B) (p + q) (cupCocycles rfl z w) v
    rw [iCocycles_cupCocycles, whiskerRight_cupCochain]
    exact congrArg (fun f => cupCochain rfl f (iCocycles B q w) v) (funext hy)
  · change (X.f ▷ B).hom (iCocycles (X.X₁ ⊗ B) (p + q + 1) (cupCocycles h' x w) v) =
      (inhomogeneousCochains.d (X.X₂ ⊗ B) (p + q)).hom (cupCochain rfl y (iCocycles B q w)) v
    rw [iCocycles_cupCocycles, whiskerRight_cupCochain, d_cupCochain, d_iCocycles,
      cupCochain_zero_right, smul_zero, add_zero]
    exact congrArg (fun f => cupCochain h' f (iCocycles B q w) v) (funext hx)

theorem δ_cupH_right (hBX : (X.map (tensorLeft B)).ShortExact) {p q n : ℕ} (h : q + p = n)
    (h' : q + (p + 1) = n + 1) (b : groupCohomology B q) (a : groupCohomology X.X₃ p) :
    δ hBX n (n + 1) rfl (cupH h b a) = (-1 : k) ^ q • cupH h' b (δ hX p (p + 1) rfl a) := by
  refine groupCohomology_induction_on a fun z => ?_
  refine groupCohomology_induction_on b fun w => ?_
  obtain ⟨y, x, hy, hx⟩ := exists_lift_of_cocycle hX z
  rw [δ_π_eq hX z y hy x hx, cupH_π, cupH_π, ← map_smul]
  subst h
  refine δ_π_eq hBX (cupCocycles rfl w z) (cupCochain rfl (iCocycles B q w) y) (fun v => ?_)
    ((-1 : k) ^ q • cupCocycles h' w x) (fun v => ?_)
  · change (B ◁ X.g).hom (cupCochain rfl (iCocycles B q w) y v) =
      iCocycles (B ⊗ X.X₃) (q + p) (cupCocycles rfl w z) v
    rw [iCocycles_cupCocycles, whiskerLeft_cupCochain]
    exact congrArg (fun f => cupCochain rfl (iCocycles B q w) f v) (funext hy)
  · change (B ◁ X.f).hom
        (iCocycles (B ⊗ X.X₁) (q + p + 1) ((-1 : k) ^ q • cupCocycles h' w x) v) =
      (inhomogeneousCochains.d (B ⊗ X.X₂) (q + p)).hom (cupCochain rfl (iCocycles B q w) y) v
    rw [map_smul, Pi.smul_apply, map_smul, iCocycles_cupCocycles, whiskerLeft_cupCochain,
      d_cupCochain, d_iCocycles, cupCochain_zero_left, zero_add, Pi.smul_apply]
    exact congrArg (fun f => (-1 : k) ^ q • cupCochain h' (iCocycles B q w) f v) (funext hx)

theorem δ_cupH_left' (hXB : (X.map (tensorRight B)).ShortExact) {p q n p' m : ℕ}
    (hp : p + 1 = p') (hm : n + 1 = m) (h : p + q = n) (h' : p' + q = m)
    (a : groupCohomology X.X₃ p) (b : groupCohomology B q) :
    δ hXB n m hm (cupH h a b) = cupH h' (δ hX p p' hp a) b := by
  subst hp hm
  exact δ_cupH_left hX B hXB h h' a b

theorem δ_cupH_right' (hBX : (X.map (tensorLeft B)).ShortExact) {p q n p' m : ℕ}
    (hp : p + 1 = p') (hm : n + 1 = m) (h : q + p = n) (h' : q + p' = m)
    (b : groupCohomology B q) (a : groupCohomology X.X₃ p) :
    δ hBX n m hm (cupH h b a) = (-1 : k) ^ q • cupH h' b (δ hX p p' hp a) := by
  subst hp hm
  exact δ_cupH_right hX B hBX h h' b a

end Connecting

end GroundTheory.GroupCoh
end
end

-- bundled from GroundTheory.TateCohomology.CupFunctorial
section
set_option maxSynthPendingDepth 1

noncomputable section

universe u

open CategoryTheory MonoidalCategory TensorProduct groupCohomology Rep

namespace GroundTheory.GroupCoh

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

theorem partialProd_comp {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) {m : ℕ}
    (x : Fin m → M) (i : Fin (m + 1)) :
    Fin.partialProd (f ∘ x) i = f (Fin.partialProd x i) := by
  simp [Fin.partialProd, ← List.map_ofFn, ← List.map_take, map_list_prod]

variable (f : G →* H) {A₁ A₂ : Rep k H} {B₁ B₂ : Rep k G} {p q n : ℕ}

def resTensorHom (φ₁ : res f A₁ ⟶ B₁) (φ₂ : res f A₂ ⟶ B₂) : res f (A₁ ⊗ A₂) ⟶ B₁ ⊗ B₂ :=
  ConcreteCategory.ofHom (C := Rep k G)
    { toLinearMap := TensorProduct.map φ₁.hom.toLinearMap φ₂.hom.toLinearMap
      isIntertwining' := fun g => TensorProduct.ext' fun a b => by
        change φ₁.hom (A₁.ρ (f g) a) ⊗ₜ[k] φ₂.hom (A₂.ρ (f g) b) =
          B₁.ρ g (φ₁.hom a) ⊗ₜ[k] B₂.ρ g (φ₂.hom b)
        rw [← Rep.hom_comm_apply φ₁, ← Rep.hom_comm_apply φ₂]
        rfl }

theorem resTensorHom_tmul (φ₁ : res f A₁ ⟶ B₁) (φ₂ : res f A₂ ⟶ B₂) (a : A₁) (b : A₂) :
    (resTensorHom f φ₁ φ₂).hom (a ⊗ₜ[k] b : (A₁ ⊗ A₂ : Rep k H)) = φ₁.hom a ⊗ₜ[k] φ₂.hom b :=
  rfl

theorem resTensorHom_cupCochain (φ₁ : res f A₁ ⟶ B₁) (φ₂ : res f A₂ ⟶ B₂) (h : p + q = n)
    (x : (Fin p → H) → A₁) (y : (Fin q → H) → A₂) (g : Fin n → G) :
    (resTensorHom f φ₁ φ₂).hom (cupCochain h x y (f ∘ g)) =
      cupCochain h (fun v => φ₁.hom (x (f ∘ v))) (fun v => φ₂.hom (y (f ∘ v))) g := by
  rw [cupCochain_apply, resTensorHom_tmul, cupCochain_apply, partialProd_comp]
  exact congrArg _ (Rep.hom_comm_apply φ₂ _ _)

theorem map_π_apply' {A : Rep k H} {B : Rep k G} (φ : res f A ⟶ B) (z : cocycles A n) :
    map f φ n (π A n z) = π B n (cocyclesMap f φ n z) := by
  change (π A n ≫ map f φ n).hom z = (cocyclesMap f φ n ≫ π B n).hom z
  rw [π_map]

theorem iCocycles_cocyclesMap' {A : Rep k H} {B : Rep k G} (φ : res f A ⟶ B)
    (z : cocycles A n) :
    iCocycles B n (cocyclesMap f φ n z) = fun g => φ.hom (iCocycles A n z (f ∘ g)) := by
  change (cocyclesMap f φ n ≫ iCocycles B n).hom z = _
  rw [HomologicalComplex.cyclesMap_i]
  rfl

theorem map_resTensorHom_cupH (φ₁ : res f A₁ ⟶ B₁) (φ₂ : res f A₂ ⟶ B₂) (h : p + q = n)
    (a : groupCohomology A₁ p) (b : groupCohomology A₂ q) :
    map f (resTensorHom f φ₁ φ₂) n (cupH h a b) = cupH h (map f φ₁ p a) (map f φ₂ q b) := by
  refine groupCohomology_induction_on a fun z => ?_
  refine groupCohomology_induction_on b fun w => ?_
  have key : cocyclesMap (A := A₁ ⊗ A₂) f (resTensorHom f φ₁ φ₂) n (cupCocycles h z w) =
      cupCocycles h (cocyclesMap f φ₁ p z) (cocyclesMap f φ₂ q w) := by
    refine cocycles_ext ?_
    rw [iCocycles_cocyclesMap', iCocycles_cupCocycles, iCocycles_cupCocycles,
      iCocycles_cocyclesMap', iCocycles_cocyclesMap']
    funext g
    exact resTensorHom_cupCochain f φ₁ φ₂ h _ _ g
  rw [cupH_π, map_π_apply', map_π_apply', map_π_apply', cupH_π, key]

end GroundTheory.GroupCoh
end
end

-- bundled from GroundTheory.TateCohomology.HerbrandTate
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

universe u

open CategoryTheory

theorem natCard_kerModRange_eq_relIndex {A : Type*} [AddCommGroup A] (f g : A →+ A) :
    Nat.card (KerModRange f g) = g.range.relIndex f.ker :=
  rfl

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]


omit [Fintype G] in
theorem ker_repSubOne (A : Rep.{u} R G) {σ : G} (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    (repSubOne A σ).ker = A.ρ.invariants.toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_ker, repSubOne_apply, sub_eq_zero, Submodule.mem_toAddSubgroup,
    Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ σ hσ]

theorem range_repSubOne (A : Rep.{u} R G) {σ : G} (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    (repSubOne A σ).range = (Representation.Coinvariants.ker A.ρ).toAddSubgroup := by
  rw [Representation.FiniteCyclicGroup.coinvariantsKer_eq_range A.ρ σ hσ]
  ext x
  rw [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, LinearMap.mem_range]
  rfl

theorem ker_repNorm (A : Rep.{u} R G) :
    (repNorm A).ker = (LinearMap.ker A.ρ.norm).toAddSubgroup :=
  rfl

theorem range_repNorm (A : Rep.{u} R G) :
    (repNorm A).range = (LinearMap.range A.ρ.norm).toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, LinearMap.mem_range]
  rfl

theorem natCard_tateCohomology_zero (A : Rep.{u} R G) {σ : G}
    (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    Nat.card (tateCohomology A 0) = Nat.card (KerModRange (repSubOne A σ) (repNorm A)) := by
  rw [natCard_kerModRange_eq_relIndex, ker_repSubOne A hσ, range_repNorm]
  exact Nat.card_congr ((tateCohomologyZeroIso (R := R) (G := G)).app A).toLinearEquiv.toEquiv

theorem natCard_tateCohomology_neg_one (A : Rep.{u} R G) {σ : G}
    (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    Nat.card (tateCohomology A (-1)) = Nat.card (KerModRange (repNorm A) (repSubOne A σ)) := by
  rw [natCard_kerModRange_eq_relIndex, ker_repNorm, range_repSubOne A hσ]
  exact Nat.card_congr ((tateCohomologyNegOneIso (R := R) (G := G)).app A).toLinearEquiv.toEquiv

end GroundTheory.GroupCoh
end

-- bundled from GroundTheory.TateCohomology.UniquelyDivisible
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

section UniquelyDivisible

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem tateAcyclic_of_bijective_nsmul (M : Rep.{u} k G)
    (h : Function.Bijective fun m : M => Fintype.card G • m) : TateAcyclic M := by
  let f : M.V →ₗ[k] M.V := Fintype.card G • LinearMap.id
  have hf : ∀ m : M, f m = Fintype.card G • m := fun m => rfl
  have hb : Function.Bijective f := by
    have : (f : M → M) = fun m : M => Fintype.card G • m := funext hf
    rw [this]; exact h
  let e := LinearEquiv.ofBijective f hb
  have he : ∀ m : M, Fintype.card G • e.symm m = m := fun m => by
    rw [← hf]; exact e.apply_symm_apply m
  have hc : ∀ (g : G) (x : M), M.ρ g (e.symm x) = e.symm (M.ρ g x) := by
    intro g x
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    change f (M.ρ g (e.symm x)) = M.ρ g x
    rw [hf, ← map_nsmul, he]
  refine tateAcyclic_of_sum_eq M e.symm.toLinearMap fun m => ?_
  have hg : ∀ g : G, M.ρ g (e.symm.toLinearMap (M.ρ g⁻¹ m)) = e.symm m := fun g => by
    rw [LinearEquiv.coe_coe, hc, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]
  rw [Finset.sum_congr rfl fun g _ => hg g, Finset.sum_const, Finset.card_univ, he]

theorem isZero_groupCohomology_of_bijective_nsmul (M : Rep.{u} k G)
    (h : Function.Bijective fun m : M => Fintype.card G • m) (n : ℕ) [NeZero n] :
    IsZero (groupCohomology M n) :=
  (tateAcyclic_of_bijective_nsmul M h n).of_iso
    ((TateCohomology.isoGroupCohomology (R := k) (G := G) n).app M).symm

end UniquelyDivisible

section Rat

variable {G : Type} [Group G] [Fintype G]

theorem bijective_nsmul_of_module_rat {V : Type*} [AddCommGroup V] [Module ℚ V] {n : ℕ}
    (hn : n ≠ 0) : Function.Bijective fun v : V => n • v := by
  have : (fun v : V => n • v) = LinearEquiv.smulOfUnit (M := V)
      (IsUnit.unit (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hn) : IsUnit (n : ℚ))) := by
    funext v
    change _ = IsUnit.unit (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hn) : IsUnit (n : ℚ)) • v
    rw [Units.smul_def, IsUnit.unit_spec, Nat.cast_smul_eq_nsmul]
  rw [this]
  exact LinearEquiv.bijective _

theorem isZero_groupCohomology_trivial_rat (n : ℕ) [NeZero n] :
    IsZero (groupCohomology (Rep.trivial ℤ G ℚ) n) :=
  isZero_groupCohomology_of_bijective_nsmul _
    (bijective_nsmul_of_module_rat (V := ℚ) Fintype.card_ne_zero) n

end Rat

end GroundTheory.GroupCoh
end

