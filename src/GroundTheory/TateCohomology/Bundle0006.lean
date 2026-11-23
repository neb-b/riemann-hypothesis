module

public import Mathlib
public import GroundTheory.TateCohomology.Bundle0003
public import GroundTheory.TateCohomology.CochainReverse
public import GroundTheory.TateCohomology.Bundle0005
public import GroundTheory.TateCohomology.PGroupFree
public import GroundTheory.TateCohomology.TateShapiro
public import GroundTheory.TateCohomology.TateConnecting
public import GroundTheory.TateCohomology.TateLow

@[expose] public section

-- bundled from GroundTheory.TateCohomology.CupGraded
section
set_option maxSynthPendingDepth 1

noncomputable section

universe u

open CategoryTheory MonoidalCategory TensorProduct groupCohomology

namespace GroundTheory.GroupCoh

variable {k G : Type u} [CommRing k] [Group G] {A B : Rep k G} {p q n : ℕ}

theorem braiding_hom_tmul (X Y : Rep k G) (a : X) (b : Y) :
    (β_ X Y).hom.hom ((a ⊗ₜ[k] b : (X ⊗ Y : Rep k G))) = b ⊗ₜ[k] a :=
  rfl

theorem revCochain_cupCochain (h : p + q = n) (h' : q + p = n) (f : (Fin p → G) → A)
    (g : (Fin q → G) → B) (x : Fin n → G) :
    revCochain n (cupCochain h f g) x =
      (-1 : k) ^ (p * q) • (β_ B A).hom.hom (cupCochain h' (revCochain q g) (revCochain p f) x) := by
  subst h'
  have hpre : (fun i : Fin p => revInv x ⟨i, by omega⟩) =
      revInv (fun j : Fin p => x ⟨q + j, by omega⟩) := by
    funext i
    simp only [revInv_apply]
    congr 2
    ext
    simp only [Fin.val_rev]
    omega
  have hsuf : (fun j : Fin q => revInv x ⟨p + j, by omega⟩) =
      revInv (fun i : Fin q => x ⟨i, by omega⟩) := by
    funext j
    simp only [revInv_apply]
    congr 2
    ext
    simp only [Fin.val_rev]
    omega
  have hP₁ : Fin.partialProd (revInv x) ⟨p, by omega⟩ =
      (Fin.partialProd (fun j : Fin p => x ⟨q + j, by omega⟩) (Fin.last p))⁻¹ := by
    rw [← partialProd_prefix (revInv x) (m := p) (by omega) le_rfl, hpre, ← partialProd_last_revInv]
    rfl
  have hP : Fin.partialProd x (Fin.last (q + p)) =
      Fin.partialProd (fun i : Fin q => x ⟨i, by omega⟩) (Fin.last q) *
        Fin.partialProd (fun j : Fin p => x ⟨q + j, by omega⟩) (Fin.last p) := by
    have := partialProd_add x (fun j : Fin p => x ⟨q + j, by omega⟩) (p := q) (q := p)
      le_rfl (fun _ => rfl) le_rfl
    rw [← partialProd_prefix x (m := q) (by omega) le_rfl] at this
    exact this
  have hP₂ : Fin.partialProd x ⟨q, by omega⟩ =
      Fin.partialProd (fun i : Fin q => x ⟨i, by omega⟩) (Fin.last q) :=
    (partialProd_prefix x (m := q) (by omega) le_rfl).symm
  rw [revCochain_apply, cupCochain_apply, cupCochain_apply, revCochain_apply, revCochain_apply,
    hpre, hsuf, hP₁, hP₂, map_smul, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul,
    map_smul, braiding_hom_tmul, tensor_ρ_tmul, ← Module.End.mul_apply, ← map_mul,
    ← Module.End.mul_apply, ← map_mul, hP, mul_inv_cancel_right, smul_smul, ← pow_add, ← pow_add,
    triangle_add]
  congr 2
  ring

theorem cupH_eq_neg_one_pow_smul_map_braiding (h : p + q = n) (h' : q + p = n)
    (x : groupCohomology A p) (y : groupCohomology B q) :
    cupH h x y = (-1 : k) ^ (p * q) • map (MonoidHom.id G) (β_ B A).hom n (cupH h' y x) := by
  refine groupCohomology_induction_on x fun z => ?_
  refine groupCohomology_induction_on y fun w => ?_
  have key : HomologicalComplex.cyclesMap (revHom (A ⊗ B)) n (cupCocycles h z w) =
      (-1 : k) ^ (p * q) • cocyclesMap (MonoidHom.id G) (β_ B A).hom n
        (cupCocycles h' (HomologicalComplex.cyclesMap (revHom B) q w)
          (HomologicalComplex.cyclesMap (revHom A) p z)) := by
    refine cocycles_ext ?_
    rw [iCocycles_cyclesMap_revHom, map_smul, iCocycles_cocyclesMap, iCocycles_cupCocycles]
    erw [iCocycles_cupCocycles]
    rw [iCocycles_cyclesMap_revHom, iCocycles_cyclesMap_revHom]
    funext x
    exact revCochain_cupCochain h h' _ _ x
  rw [cupH_π, ← π_cyclesMap_revHom (cupCocycles h z w), key, map_smul, ← map_π_apply]
  erw [← cupH_π]
  rw [π_cyclesMap_revHom, π_cyclesMap_revHom]

theorem map_braiding_cupH (h : p + q = n) (h' : q + p = n) (x : groupCohomology A p)
    (y : groupCohomology B q) :
    map (MonoidHom.id G) (β_ A B).hom n (cupH h x y) = (-1 : k) ^ (p * q) • cupH h' y x := by
  rw [cupH_eq_neg_one_pow_smul_map_braiding h' h y x, smul_smul, ← pow_add, mul_comm q p,
    ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]

end GroundTheory.GroupCoh
end
end

-- bundled from GroundTheory.TateCohomology.PGroupCohTrivial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep
open scoped MonoidAlgebra

universe u

section Shift

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem tateAcyclic_cohTrivial_of_isZero_of_shift (P : Rep.{u} k G → Prop)
    (hcoind : ∀ M, P M → P (coindShift M)) (hind : ∀ M, P M → P (indShift M))
    (hbase : ∀ M, P M → IsZero (tateCohomology M (-2)) → TateAcyclic M ∧ CohTrivial M)
    (q : ℤ) (M : Rep.{u} k G) (hM : P M) (hq : IsZero (tateCohomology M q)) :
    TateAcyclic M ∧ CohTrivial M := by
  refine Int.inductionOn' (motive := fun q => ∀ M : Rep.{u} k G, P M →
    IsZero (tateCohomology M q) → TateAcyclic M ∧ CohTrivial M) q (-2) hbase ?_ ?_ M hM hq
  · intro n _ ih M hM hq
    have h1 : IsZero (tateCohomology (coindShift M) n) := hq.of_iso (coindShiftIso M n)
    obtain ⟨t, c⟩ := ih (coindShift M) (hcoind M hM) h1
    have hS := coindSES_shortExact M
    have t2 : TateAcyclic (coindSES.obj M).X₂ := tateAcyclic_coindSES_X₂ M
    have c2 : CohTrivial (coindSES.obj M).X₂ := by
      rw [coindSES_obj_X₂]; exact cohTrivial_coind_bot _
    have t1 := TateAcyclic.of_shortExact_X₃ hS t2 t
    have c1 := CohTrivial.of_shortExact_X₃ hS c2 c
    rw [coindSES_obj_X₁] at t1 c1
    exact ⟨t1, c1⟩
  · intro n _ ih M hM hq
    have h1 : IsZero (tateCohomology (indShift M) n) := by
      have h := hq.of_iso (indShiftIso M (n - 1)).symm
      rwa [sub_add_cancel] at h
    obtain ⟨t, c⟩ := ih (indShift M) (hind M hM) h1
    have hS := indSES_shortExact M
    have t2 : TateAcyclic (indSES.obj M).X₂ := tateAcyclic_indSES_X₂ M
    have c2 : CohTrivial (indSES.obj M).X₂ := by
      rw [indSES_obj_X₂]; exact cohTrivial_ind_bot _
    have t3 := TateAcyclic.of_shortExact_X₁ hS t2 t
    have c3 := CohTrivial.of_shortExact_X₁ hS c2 c
    rw [indSES_obj_X₃] at t3 c3
    exact ⟨t3, c3⟩

end Shift

section Field

variable {k G : Type u} [Field k] [Group G] [Fintype G] {p : ℕ} [Fact p.Prime] [CharP k p]

end Field

end GroundTheory.GroupCoh
end

-- bundled from GroundTheory.TateCohomology.ResCores
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (S : Subgroup G) [Fintype S]


section Res

noncomputable def tateRes (n : ℤ) :
    tateCohomologyFunctor (R := k) (G := G) n ⟶
      resFunctor S.subtype ⋙ tateCohomologyFunctor (R := k) (G := S) n :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (Rep.resCoindAdjunction.{u, u} k S.subtype).unit _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (resFunctor S.subtype) (tateCoindNatIso S n).hom

lemma tateRes_app (n : ℤ) (A : Rep.{u} k G) :
    (tateRes S n).app A =
      (tateCohomologyFunctor n).map ((Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app A) ≫
        (tateCoindIso S (res S.subtype A) n).hom := by
  simp only [tateRes, NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Category.id_comp]
  rfl

end Res

section Cores


open scoped Classical in
noncomputable def tateCores (n : ℤ) :
    resFunctor S.subtype ⋙ tateCohomologyFunctor (R := k) (G := S) n ⟶
      tateCohomologyFunctor (R := k) (G := G) n :=
  Functor.whiskerLeft (resFunctor S.subtype) (tateIndNatIso S n).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Rep.indResAdjunction.{u} k S.subtype).counit _ ≫
    (Functor.leftUnitor _).hom

lemma tateCores_app (n : ℤ) (A : Rep.{u} k G) :
    (tateCores S n).app A =
      (tateIndIso S (res S.subtype A) n).inv ≫
        (tateCohomologyFunctor n).map ((Rep.indResAdjunction.{u} k S.subtype).counit.app A) := by
  simp only [tateCores, NatTrans.comp_app, Functor.leftUnitor_hom_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Category.id_comp]
  rfl

end Cores

end GroundTheory.GroupCoh
end

-- bundled from GroundTheory.TateCohomology.TateDeltaZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] {X : ShortComplex (Rep.{u} k G)}
  (hX : X.ShortExact)

theorem tateIsoH_δ_zero_apply (z : X.X₃.ρ.invariants) (y : X.X₂) (hy : X.g.hom y = z)
    (x : G → X.X₁) (hx : X.f.hom ∘ x = d₀₁ X.X₂ y) (c : (tateComplex X.X₃).cycles 0)
    (hc : ((tateComplex X.X₃).iCycles 0).hom c = (cochainsIso₀ X.X₃).inv.hom z) :
    (tateIsoH X.X₁ (0 + 1) 1 (by norm_num)).hom.hom
      ((TateCohomology.δ hX 0).hom (((tateComplex X.X₃).homologyπ 0).hom c)) =
      H1π X.X₁ ⟨x, mem_cocycles₁_of_comp_eq_d₀₁ hX hx⟩ := by
  have hxc : x ∈ cocycles₁ X.X₁ := mem_cocycles₁_of_comp_eq_d₀₁ hX hx
  let x₁ : (tateComplex X.X₁).X (0 + 1) := (cochainsIso₁ X.X₁).inv.hom x
  let x₂ : (tateComplex X.X₂).X 0 := (cochainsIso₀ X.X₂).inv.hom y
  have hd : ((tateComplex X.X₁).d (0 + 1) (0 + 1 + 1)).hom x₁ = 0 := by
    have e := congr(($(eq_d₁₂_comp_inv X.X₁)).hom x)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    have h0 : d₁₂ X.X₁ x = 0 := LinearMap.mem_ker.1 hxc
    rw [h0, map_zero] at e
    exact e
  have hx₂ : ((tateComplex.map X.g).f 0).hom x₂ = ((tateComplex X.X₃).iCycles 0).hom c := by
    rw [hc]
    funext v
    exact hy
  have hx₁ : ((tateComplex.map X.f).f (0 + 1)).hom x₁ = ((tateComplex X.X₂).d 0 (0 + 1)).hom x₂ := by
    have e := congr(($(eq_d₀₁_comp_inv X.X₂)).hom y)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    refine Eq.trans ?_ e.symm
    funext v
    exact congrFun hx (v 0)
  have h1 := tδ_apply hX 0 (((tateComplex X.X₃).iCycles 0).hom c)
    (tate_d_iCycles_int _ 0 c) x₂ hx₂ x₁ hx₁ hd
  rw [tateCyclesMk_iCycles] at h1
  have h2 := tateIsoH_homologyπ X.X₁ 1 (tateCyclesMk X.X₁ (0 + 1) x₁ hd)
  refine (congrArg (tateIsoH X.X₁ (0 + 1) 1 (by norm_num)).hom.hom h1).trans (h2.trans ?_)
  have h3 := cocyclesMk₁_eq X.X₁ ⟨x, hxc⟩
  refine Eq.trans ?_ (congrArg (π X.X₁ 1).hom h3)
  congr 1
  apply cocycles_ext
  exact (iCocycles_mk _ _).trans ((iCycles_tateCyclesMk _ _ _ _).trans (iCocycles_mk _ _).symm)

end GroundTheory.GroupCoh
end

-- bundled from GroundTheory.TateCohomology.TateGroupIso
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

section Bijective

variable {k H K : Type u} [CommRing k] [Group H] [Group K] [Fintype H] [Fintype K]
  (f : H →* K) (hf : Function.Bijective f)

include hf

theorem norm_res_of_bijective (B : Rep.{u} k K) (m : B) :
    (res f B).ρ.norm m = B.ρ.norm m := by
  rw [Representation.norm, Representation.norm, LinearMap.sum_apply, LinearMap.sum_apply]
  exact Fintype.sum_bijective f hf _ _ fun _ => rfl

theorem isZero_tateCohomology_zero_res_iff (B : Rep.{u} k K) :
    IsZero (tateCohomology (res f B) 0) ↔ IsZero (tateCohomology B 0) := by
  rw [isZero_tateCohomology_zero_iff_forall, isZero_tateCohomology_zero_iff_forall]
  have hinv : ∀ x : B, x ∈ (res f B).ρ.invariants ↔ x ∈ B.ρ.invariants := fun x => by
    simp only [Representation.mem_invariants]
    constructor
    · intro h g
      obtain ⟨h', rfl⟩ := hf.2 g
      exact h h'
    · intro h h'
      exact h (f h')
  constructor
  · intro h x hx
    obtain ⟨m, hm⟩ := h x ((hinv x).2 hx)
    exact ⟨m, by rw [← norm_res_of_bijective f hf]; exact hm⟩
  · intro h x hx
    obtain ⟨m, hm⟩ := h x ((hinv x).1 hx)
    exact ⟨m, by rw [norm_res_of_bijective f hf]; exact hm⟩

theorem tateAcyclic_res_of_sum_eq (B : Rep.{u} k K) (φ : B.V →ₗ[k] B.V)
    (hφ : ∀ m : B, ∑ g : K, B.ρ g (φ (B.ρ g⁻¹ m)) = m) : TateAcyclic (res f B) :=
  tateAcyclic_of_sum_eq (res f B) φ fun m => by
    conv_rhs => rw [← hφ m]
    exact Fintype.sum_bijective f hf _ _ fun h => by
      simp only [MonoidHom.comp_apply, map_inv]

theorem isZero_tateCohomology_res_iff (n : ℤ) (B : Rep.{u} k K) :
    IsZero (tateCohomology (res f B) n) ↔ IsZero (tateCohomology B n) := by
  refine Int.inductionOn' (motive := fun n => ∀ B : Rep.{u} k K,
    IsZero (tateCohomology (res f B) n) ↔ IsZero (tateCohomology B n)) n 0
    (fun B => isZero_tateCohomology_zero_res_iff f hf B) ?_ ?_ B
  · intro n _ ih B
    have hX' : ((coindSES.obj B).map (resFunctor f)).ShortExact :=
      (shortExact_res f).2 (coindSES_shortExact B)
    have h2 : TateAcyclic ((coindSES.obj B).map (resFunctor f)).X₂ := by
      rw [ShortComplex.map_X₂, coindSES_obj_X₂]
      exact tateAcyclic_res_of_sum_eq f hf _ (coindBotProj _) (sum_coindBotProj _)
    have e1 := @asIso _ _ _ _ (TateCohomology.δ hX' n) (isIso_δ_of_tateAcyclic hX' h2 n)
    rw [ShortComplex.map_X₃, ShortComplex.map_X₁, coindSES_obj_X₁] at e1
    rw [← e1.isZero_iff, ← (coindShiftIso B n).isZero_iff]
    exact ih _
  · intro n _ ih B
    have hX' : ((indSES.obj B).map (resFunctor f)).ShortExact :=
      (shortExact_res f).2 (indSES_shortExact B)
    have h2 : TateAcyclic ((indSES.obj B).map (resFunctor f)).X₂ := by
      classical
      rw [ShortComplex.map_X₂, indSES_obj_X₂]
      exact (tateAcyclic_res_of_sum_eq f hf _ (coindBotProj _) (sum_coindBotProj _)).of_iso
        ((resFunctor f).mapIso (indCoindIso _))
    have e1 := @asIso _ _ _ _ (TateCohomology.δ hX' (n - 1))
      (isIso_δ_of_tateAcyclic hX' h2 (n - 1))
    rw [ShortComplex.map_X₃, ShortComplex.map_X₁, indSES_obj_X₃] at e1
    rw [e1.isZero_iff, (indShiftIso B (n - 1)).isZero_iff, sub_add_cancel]
    exact ih _

theorem tateAcyclic_res_iff (B : Rep.{u} k K) : TateAcyclic (res f B) ↔ TateAcyclic B :=
  forall_congr' fun n => isZero_tateCohomology_res_iff f hf n B

end Bijective

section Consequences

variable {k G : Type u} [CommRing k] [Group G]


omit [Group G] in
theorem res_res {H K : Type u} [Group H] [Group K] [Group G] (f : H →* K) (g : K →* G)
    (A : Rep.{u} k G) : res f (res g A) = res (g.comp f) A :=
  rfl

theorem CohTrivial.tateAcyclic [Fintype G] {A : Rep.{u} k G} (h : CohTrivial A) :
    TateAcyclic A := by
  let _ : Fintype (⊤ : Subgroup G) := Fintype.ofFinite _
  have hbij : Function.Bijective (⊤ : Subgroup G).subtype :=
    ⟨Subgroup.subtype_injective _, fun g => ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩⟩
  have h1 : TateAcyclic (res (⊤ : Subgroup G).subtype A) := h ⊤
  exact (tateAcyclic_res_iff _ hbij A).1 h1

theorem tateAcyclic_res_conj {A : Rep.{u} k G} (U V : Subgroup G) [Fintype U] [Fintype V] (g : G)
    (hUV : ∀ x, x ∈ U ↔ g⁻¹ * x * g ∈ V) (hV : TateAcyclic (res V.subtype A)) :
    TateAcyclic (res U.subtype A) := by
  let c : U →* V :=
    { toFun := fun u => ⟨g⁻¹ * u * g, (hUV u).1 u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hinj : Function.Injective c := fun a b hab => by
    have h := congrArg (fun x : V => (x : G)) hab
    simp only [c, MonoidHom.coe_mk, OneHom.coe_mk, mul_left_inj, mul_right_inj] at h
    exact Subtype.ext h
  have hsurj : Function.Surjective c := fun v =>
    ⟨⟨g * v * g⁻¹, (hUV _).2 (by simp [mul_assoc])⟩, Subtype.ext (by simp [c, mul_assoc])⟩
  have hc := (tateAcyclic_res_iff c ⟨hinj, hsurj⟩ (res V.subtype A)).2 hV
  let e : A.V ≃ₗ[k] A.V := LinearEquiv.ofLinearMap (A.ρ g⁻¹) (A.ρ g)
    (LinearMap.ext fun a => by simp) (LinearMap.ext fun a => by simp)
  let eqv : (res U.subtype A).ρ.Equiv (res c (res V.subtype A)).ρ :=
    Representation.Equiv.mk e fun u => LinearMap.ext fun a => by
      change A.ρ g⁻¹ (A.ρ u a) = A.ρ (g⁻¹ * u * g) (A.ρ g⁻¹ a)
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, mul_assoc,
        mul_inv_cancel, mul_one]
  exact hc.of_iso (Rep.mkIso eqv)

end Consequences

end GroundTheory.GroupCoh
end

