module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.TateCohomology.ConjAction
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory groupCohomology Rep

universe u

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal]

def conjHom (g : G) : S →* S where
  toFun s := ⟨g⁻¹ * s * g, ‹S.Normal›.conj_mem' (s : G) s.2 g⟩
  map_one' := by ext; simp
  map_mul' s t := by ext; simp only [Subgroup.coe_mul]; group

@[simp]
lemma coe_conjHom_apply (g : G) (s : S) : (conjHom S g s : G) = g⁻¹ * s * g := rfl

noncomputable def conjMor (g : G) : res (conjHom S g) (res S.subtype A) ⟶ res S.subtype A :=
  ofHom ⟨A.ρ g, fun s => by
    ext a
    simp only [LinearMap.comp_apply, MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.coe_subtype, coe_conjHom_apply]
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group⟩


end GroundTheory.GroupCoh
end

-- bundled from GroundTheory.TateCohomology.DeltaMap
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory groupCohomology Rep

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

noncomputable def cochainsMapShortComplex (f : G →* H) {X : ShortComplex (Rep k H)}
    {Y : ShortComplex (Rep k G)} (F : X.map (resFunctor f) ⟶ Y) :
    X.map (cochainsFunctor k H) ⟶ Y.map (cochainsFunctor k G) where
  τ₁ := cochainsMap f F.τ₁
  τ₂ := cochainsMap f F.τ₂
  τ₃ := cochainsMap f F.τ₃
  comm₁₂ := by
    ext n x
    refine funext fun g => ?_
    exact congrArg (fun φ => φ.hom (x (f ∘ g))) F.comm₁₂
  comm₂₃ := by
    ext n x
    refine funext fun g => ?_
    exact congrArg (fun φ => φ.hom (x (f ∘ g))) F.comm₂₃

theorem δ_comp_map (f : G →* H) {X : ShortComplex (Rep k H)} {Y : ShortComplex (Rep k G)}
    (hX : X.ShortExact) (hY : Y.ShortExact) (F : X.map (resFunctor f) ⟶ Y)
    (i j : ℕ) (hij : i + 1 = j) :
    δ hX i j hij ≫ map f F.τ₁ j = map f F.τ₃ i ≫ δ hY i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality (cochainsMapShortComplex f F)
    (map_cochainsFunctor_shortExact hX) (map_cochainsFunctor_shortExact hY) i j hij

theorem δ_comp_map_res (f : G →* H) {X : ShortComplex (Rep k H)} (hX : X.ShortExact)
    (i j : ℕ) (hij : i + 1 = j) :
    δ hX i j hij ≫ map f (𝟙 (res f X.X₁)) j =
      map f (𝟙 (res f X.X₃)) i ≫ δ ((shortExact_res f).2 hX) i j hij :=
  δ_comp_map f hX ((shortExact_res f).2 hX) (𝟙 _) i j hij

end GroundTheory.GroupCoh
end

-- bundled from GroundTheory.TateCohomology.DiagonalSuccIsoFreeInvSingle
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits groupCohomology Rep

universe v w u

section HomComplex

variable {R : Type w} [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]

noncomputable def linearYonedaObjMap {X Y : ChainComplex C ℕ} (f : X ⟶ Y) (B : C) :
    Y.linearYonedaObj R B ⟶ X.linearYonedaObj R B :=
  (HomologicalComplex.unopFunctor (ModuleCat R) (ComplexShape.down ℕ)).map
    ((((linearYoneda R C).obj B).rightOp.mapHomologicalComplex _).map f).op

lemma linearYonedaObjMap_comp {X Y Z : ChainComplex C ℕ} (f : X ⟶ Y) (g : Y ⟶ Z) (B : C) :
    linearYonedaObjMap (R := R) (f ≫ g) B = linearYonedaObjMap g B ≫ linearYonedaObjMap f B := by
  ext n x
  change (f ≫ g).f n ≫ x = f.f n ≫ g.f n ≫ x
  rw [HomologicalComplex.comp_f]
  exact Category.assoc _ _ _

lemma linearYonedaObjMap_id (X : ChainComplex C ℕ) (B : C) :
    linearYonedaObjMap (R := R) (𝟙 X) B = 𝟙 _ := by
  ext n x
  change (𝟙 X : X ⟶ X).f n ≫ x = x
  rw [HomologicalComplex.id_f]
  exact Category.id_comp _

noncomputable def linearYonedaObjHomotopy {X Y : ChainComplex C ℕ} {f g : X ⟶ Y}
    (h : Homotopy f g) (B : C) :
    Homotopy (linearYonedaObjMap (R := R) f B) (linearYonedaObjMap g B) :=
  ((((linearYoneda R C).obj B).rightOp).mapHomotopy h).unop

noncomputable def linearYonedaObjHomotopyEquiv {X Y : ChainComplex C ℕ} (e : HomotopyEquiv X Y)
    (B : C) : HomotopyEquiv (Y.linearYonedaObj R B) (X.linearYonedaObj R B) where
  hom := linearYonedaObjMap e.hom B
  inv := linearYonedaObjMap e.inv B
  homotopyHomInvId := (Homotopy.ofEq (linearYonedaObjMap_comp _ _ _).symm).trans
    ((linearYonedaObjHomotopy e.homotopyInvHomId B).trans
      (Homotopy.ofEq (linearYonedaObjMap_id _ _)))
  homotopyInvHomId := (Homotopy.ofEq (linearYonedaObjMap_comp _ _ _).symm).trans
    ((linearYonedaObjHomotopy e.homotopyHomInvId B).trans
      (Homotopy.ofEq (linearYonedaObjMap_id _ _)))

end HomComplex

section Bar

variable {k G : Type u} [CommRing k] [Group G]


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma diagonalSuccIsoFree_inv_single (m : ℕ) (f : Fin m → G) (g : G) (r : k) :
    (diagonalSuccIsoFree k G m).inv.hom (Finsupp.single f (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single (g • Fin.partialProd f) r := by
  simp only [diagonalSuccIsoFree, diagonalSuccIsoTensorTrivial, Iso.trans_inv, Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply]
  have step1 : (Hom.hom (leftRegularTensorTrivialIsoFree k G (Fin m → G)).inv)
      (Finsupp.single f (.single g r)) = .single g 1 ⊗ₜ[k] .single f r :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single f g r
  rw [step1]
  simp only [mkIso_inv, Representation.linearizeOfMulActionIso, Representation.Equiv.mk_symm,
    LinearEquiv.refl_symm, ConcreteCategory.hom_ofHom, Action.tensorObj_V, Action.trivial_V,
    Functor.mapIso_inv, tensor_V, tensor_ρ, Iso.symm_inv, Functor.Monoidal.μIso_hom, μ_hom,
    MonoidalCategory.tensorIso_inv, Representation.linearizeTrivialIso, hom_tensorHom,
    Representation.IntertwiningMap.tensor_apply, Representation.Equiv.coe_toIntertwiningMap,
    Representation.Equiv.mk_apply, LinearEquiv.refl_apply]
  have key₁ := Representation.linearizeMap_single (k := k)
    (Action.diagonalSuccIsoTensorTrivial G m).inv (g, f) ((1 : k) * r)
  have key₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := k)
    (X := Action.leftRegular G) (Y := Action.trivial G (Fin m → G)) g f 1 r
  exact ((congrArg (fun z => (Representation.linearizeMap
    (Action.diagonalSuccIsoTensorTrivial G m).inv) z) key₂).trans key₁).trans (by
      rw [one_mul]
      exact congrArg (fun h => MonoidAlgebra.single h r)
        (Action.diagonalSuccIsoTensorTrivial_inv_hom_apply g f))

lemma barResolution_π_f_zero_single (v : Fin 0 → G) (g : G) (r : k) :
    ((barResolution k G).π.f 0).hom (Finsupp.single v (MonoidAlgebra.single g r)) = r := by
  change (standardComplex.ε k G).hom ((diagonalSuccIsoFree k G 0).inv.hom
    (Finsupp.single v (MonoidAlgebra.single g r))) = r
  rw [diagonalSuccIsoFree_inv_single]
  simp [standardComplex.ε]

end Bar

section Norm

variable {k H : Type u} [CommRing k] [Group H] [Fintype H]

lemma ρ_apply_norm (B : Rep.{u} k H) (b : B) (s : H) : B.ρ s (B.ρ.norm b) = B.ρ.norm b := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Representation.norm, LinearMap.sum_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft s) _ _ fun t => ?_
  simp [← Module.End.mul_apply, ← map_mul]

end Norm

end GroundTheory.GroupCoh
end

-- bundled from GroundTheory.TateCohomology.Induced
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits groupCohomology groupHomology Rep

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

def TateAcyclic (M : Rep.{u} k G) : Prop := ∀ n : ℤ, IsZero (tateCohomology M n)

theorem TateAcyclic.of_retract {M N : Rep.{u} k G} (i : M ⟶ N) (r : N ⟶ M) (h : i ≫ r = 𝟙 M)
    (hN : TateAcyclic N) : TateAcyclic M := fun n => by
  rw [IsZero.iff_id_eq_zero]
  change 𝟙 ((tateCohomologyFunctor n).obj M) = 0
  rw [← (tateCohomologyFunctor n).map_id, ← h, Functor.map_comp,
    (hN n).eq_of_tgt ((tateCohomologyFunctor n).map i) 0, zero_comp]

theorem TateAcyclic.of_iso {M N : Rep.{u} k G} (e : M ≅ N) (hN : TateAcyclic N) :
    TateAcyclic M :=
  hN.of_retract e.hom e.inv e.hom_inv_id

theorem isZero_tateCohomology_zero_of_forall (M : Rep.{u} k G)
    (h : ∀ m : M, (∀ g : G, M.ρ g m = m) → ∃ y : M, M.ρ.norm y = m) :
    IsZero (tateCohomology M 0) := by
  rw [tateCohomology, tateCohomologyFunctor, Functor.comp_obj,
    HomologicalComplex.homologyFunctor_obj, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (-1) 0 1 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  change ∀ x₂ : (inhomogeneousCochains M).X 0, (inhomogeneousCochains M).d 0 1 x₂ = 0 →
    ∃ x₁ : (inhomogeneousChains M).X 0, M.tateNorm x₁ = x₂
  intro x₂ hd
  have hinv : ∀ g : G, M.ρ g ((cochainsIso₀ M).hom x₂) = (cochainsIso₀ M).hom x₂ := by
    intro g
    have key : (d₀₁ M).hom ((cochainsIso₀ M).hom.hom x₂) =
        (cochainsIso₁ M).hom.hom (((inhomogeneousCochains M).d 0 1).hom x₂) := by
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, comp_d₀₁_eq]; rfl
    rw [show ((inhomogeneousCochains M).d 0 1).hom x₂ = 0 from hd, map_zero] at key
    have := congr_fun key g
    exact sub_eq_zero.mp this
  obtain ⟨y, hy⟩ := h _ hinv
  refine ⟨(chainsIso₀ M).inv y, ?_⟩
  simp only [Rep.tateNorm, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  change (cochainsIso₀ M).inv (M.ρ.norm y) = x₂
  rw [hy, Iso.hom_inv_id_apply]

theorem isZero_tateCohomology_neg_one_of_forall (M : Rep.{u} k G)
    (h : ∀ m : M, M.ρ.norm m = 0 → ∃ z : G →₀ M, d₁₀ M z = m) :
    IsZero (tateCohomology M (-1)) := by
  rw [tateCohomology, tateCohomologyFunctor, Functor.comp_obj,
    HomologicalComplex.homologyFunctor_obj, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (-2) (-1) 0 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  change ∀ x₂ : (inhomogeneousChains M).X 0, M.tateNorm x₂ = 0 →
    ∃ x₁ : (inhomogeneousChains M).X 1, (inhomogeneousChains M).d 1 0 x₁ = x₂
  intro x₂ hx
  have hn : M.ρ.norm ((chainsIso₀ M).hom x₂) = 0 := by
    have := congr_arg (fun x => (cochainsIso₀ M).hom x) hx
    simp only [Rep.tateNorm, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply, map_zero] at this
    exact this
  obtain ⟨z, hz⟩ := h _ hn
  refine ⟨(chainsIso₁ M).inv z, ?_⟩
  rw [eq_d₁₀_comp_inv_apply, hz, Iso.hom_inv_id_apply]

theorem isZero_tateCohomology_zero_of_sum_eq (M : Rep.{u} k G) (φ : M.V →ₗ[k] M.V)
    (hφ : ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m) :
    IsZero (tateCohomology M 0) := by
  refine isZero_tateCohomology_zero_of_forall M fun m hm => ⟨φ m, ?_⟩
  rw [Representation.norm, LinearMap.sum_apply]
  conv_rhs => rw [← hφ m]
  simp only [hm]

theorem isZero_tateCohomology_neg_one_of_sum_eq (M : Rep.{u} k G) (φ : M.V →ₗ[k] M.V)
    (hφ : ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m) :
    IsZero (tateCohomology M (-1)) := by
  refine isZero_tateCohomology_neg_one_of_forall M fun m hm =>
    ⟨∑ g : G, Finsupp.single g⁻¹ (φ (M.ρ g⁻¹ m)), ?_⟩
  have hsum : ∑ g : G, M.ρ g⁻¹ m = M.ρ.norm m := by
    rw [Representation.norm, LinearMap.sum_apply]
    exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun _ => rfl)
  show (Finsupp.lsum k fun g : G => M.ρ g⁻¹ - LinearMap.id)
    (∑ g : G, Finsupp.single g⁻¹ (φ (M.ρ g⁻¹ m))) = m
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finsupp.lsum_single, LinearMap.sub_apply, LinearMap.id_apply, inv_inv]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_sub_distrib, ← map_sum, hsum, hm, map_zero, sub_zero, hφ]

section Coind

variable (B : Rep.{u} k (⊥ : Subgroup G))


open scoped Classical in
noncomputable def coindBotProj :
    (coind (⊥ : Subgroup G).subtype B).V →ₗ[k] (coind (⊥ : Subgroup G).subtype B).V := by
  classical
  exact LinearMap.codRestrict _ ((LinearMap.single k (fun _ : G => B.V) 1) ∘ₗ LinearMap.proj 1 ∘ₗ
    (Representation.coindV (⊥ : Subgroup G).subtype B.ρ).subtype) fun f => by
      rw [Representation.mem_coindV]
      intro s x
      obtain rfl : s = 1 := Subsingleton.elim _ _
      simp


open scoped Classical in
theorem sum_coindBotProj (f : coind (⊥ : Subgroup G).subtype B) :
    ∑ g : G, (coind (⊥ : Subgroup G).subtype B).ρ g
      (coindBotProj B ((coind (⊥ : Subgroup G).subtype B).ρ g⁻¹ f)) = f := by
  classical
  apply Subtype.ext
  funext x
  rw [Submodule.coe_sum, Finset.sum_apply]
  change ∑ g : G, (Pi.single (M := fun _ : G => B.V) (1 : G) (f.1 (1 * g⁻¹)) (x * g)) = f.1 x
  rw [Fintype.sum_eq_single x⁻¹]
  · simp
  · intro g hg
    rw [Pi.single_apply, if_neg]
    exact fun h => hg (eq_inv_of_mul_eq_one_right h)

theorem isZero_tateCohomology_coind_bot (n : ℤ) :
    IsZero (tateCohomology (coind (⊥ : Subgroup G).subtype B) n) := by
  classical
  rcases n with (_ | n) | (_ | n)
  · exact isZero_tateCohomology_zero_of_sum_eq _ (coindBotProj B) (sum_coindBotProj B)
  · exact ((isZero_groupCohomology_succ_of_subsingleton B n).of_iso (coindIso B (n + 1))).of_iso
      ((TateCohomology.isoGroupCohomology (n + 1)).app _)
  · exact isZero_tateCohomology_neg_one_of_sum_eq _ (coindBotProj B) (sum_coindBotProj B)
  · have e := (TateCohomology.isoGroupHomology (Int.negSucc (n + 1)) (n + 1)
      (by simp [Int.negSucc_eq])).app (coind (⊥ : Subgroup G).subtype B)
    refine (((isZero_groupHomology_succ_of_subsingleton B n).of_iso
      (indIso (⊥ : Subgroup G) B (n + 1))).of_iso ?_).of_iso e
    exact (groupHomology.functor k G (n + 1)).mapIso (indCoindIso B).symm

theorem isZero_tateCohomology_ind_bot (n : ℤ) :
    IsZero (tateCohomology (ind (⊥ : Subgroup G).subtype B) n) := by
  classical
  exact (isZero_tateCohomology_coind_bot B n).of_iso
    ((tateCohomologyFunctor n).mapIso (indCoindIso B))

theorem tateAcyclic_coind_bot : TateAcyclic (coind (⊥ : Subgroup G).subtype B) :=
  isZero_tateCohomology_coind_bot B

theorem tateAcyclic_ind_bot : TateAcyclic (ind (⊥ : Subgroup G).subtype B) :=
  isZero_tateCohomology_ind_bot B

end Coind

end GroundTheory.GroupCoh
end

-- bundled from GroundTheory.TateCohomology.PGroupFixed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open Representation

section Fixed

variable {k G V : Type*} [CommRing k] [Group G] [Fintype G] {p : ℕ} [Fact p.Prime] [CharP k p]
  [AddCommGroup V] [Module k V]

theorem exists_fixed_mem_span_orbit (hG : IsPGroup p G) (ρ : Representation k G V) {m : V}
    (hm : m ≠ 0) :
    ∃ v ∈ Submodule.span k (Set.range fun g : G => ρ g m), v ≠ 0 ∧ ∀ g : G, ρ g v = v := by
  classical
  have hp : ∀ x : V, p • x = 0 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
  let cast : ZMod p →+* k := ZMod.castHom (dvd_refl p) k
  let f : (G → ZMod p) →+ V :=
    { toFun := fun c => ∑ g, cast (c g) • ρ g m
      map_zero' := by simp
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib] }
  have hf : ∀ c, f c = ∑ g, cast (c g) • ρ g m := fun _ => rfl
  have hstab : ∀ (h : G) (c : G → ZMod p), ρ h (f c) = f (fun g => c (h⁻¹ * g)) := by
    intro h c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hf, hf, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
    simp [map_mul, Module.End.mul_apply]
  have hmem : ∀ (h : G) (x : V), x ∈ f.range → ρ h x ∈ f.range := by
    rintro h x ⟨c, rfl⟩
    exact ⟨fun g => c (h⁻¹ * g), (hstab h c).symm⟩
  have : Finite f.range :=
    Finite.of_injective (fun x : f.range => (⟨x.1, AddMonoidHom.mem_range.mp x.2⟩ : Set.range f))
      fun a b h => Subtype.ext (congrArg Subtype.val h)
  let : MulAction G f.range :=
    { smul := fun h x => ⟨ρ h x, hmem h x x.2⟩
      one_smul := fun x => Subtype.ext (by
        change ρ 1 (x : V) = x
        simp)
      mul_smul := fun a b x => Subtype.ext (by
        change ρ (a * b) (x : V) = ρ a (ρ b x)
        rw [map_mul, Module.End.mul_apply]) }
  have hm' : m ∈ f.range := ⟨Pi.single 1 1, by
    rw [hf, Fintype.sum_eq_single (1 : G) (fun g hg => by simp [hg])]
    simp⟩
  have horder : addOrderOf (⟨m, hm'⟩ : f.range) = p :=
    addOrderOf_eq_prime (Subtype.ext (by simpa using hp m))
      (fun h => hm (congrArg Subtype.val h))
  have hdvd : p ∣ Nat.card f.range := by
    have := addOrderOf_dvd_natCard (⟨m, hm'⟩ : f.range)
    rwa [horder] at this
  have h0 : (0 : f.range) ∈ MulAction.fixedPoints G f.range := fun g => Subtype.ext (by
    change ρ g 0 = 0
    simp)
  obtain ⟨b, hb, hb0⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point f.range hdvd h0
  refine ⟨b.1, ?_, fun h => hb0 (Subtype.ext h.symm), fun g => congrArg Subtype.val (hb g)⟩
  obtain ⟨c, hc⟩ := AddMonoidHom.mem_range.mp b.2
  rw [← hc, hf]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

end Fixed

section Nakayama

variable {k G V : Type*} [Field k] [Group G] [Fintype G] {p : ℕ} [Fact p.Prime] [CharP k p]
  [AddCommGroup V] [Module k V]

theorem eq_top_of_sup_coinvariantsKer_eq_top (hG : IsPGroup p G) (ρ : Representation k G V)
    (W : Submodule k V) (hW : ∀ g : G, W ≤ W.comap (ρ g)) (h : W ⊔ Coinvariants.ker ρ = ⊤) :
    W = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hWf⟩ := Submodule.exists_le_ker_of_lt_top W (lt_top_iff_ne_top.mpr hne)
  obtain ⟨v, hvspan, hv0, hvfix⟩ := exists_fixed_mem_span_orbit hG ρ.dual hf0
  have hd : ∀ (g : G) (φ : Module.Dual k V) (x : V), ρ.dual g φ x = φ (ρ g⁻¹ x) :=
    fun _ _ _ => rfl

  have hvW : W ≤ LinearMap.ker v := by
    have hle : Submodule.span k (Set.range fun g : G => ρ.dual g f) ≤ W.dualAnnihilator := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_dualAnnihilator]
      intro w hw
      rw [hd]
      exact hWf (hW g⁻¹ hw)
    intro w hw
    exact (Submodule.mem_dualAnnihilator v).mp (hle hvspan) w hw

  have hvI : Coinvariants.ker ρ ≤ LinearMap.ker v := by
    rw [Coinvariants.ker, Submodule.span_le]
    rintro _ ⟨⟨g, x⟩, rfl⟩
    have := congrArg (fun φ : Module.Dual k V => φ x) (hvfix g⁻¹)
    simp only [hd, inv_inv] at this
    simp [this]
  apply hv0
  ext x
  have hx : x ∈ W ⊔ Coinvariants.ker ρ := h ▸ Submodule.mem_top
  exact (sup_le hvW hvI) hx

theorem subsingleton_of_coinvariantsKer_eq_top (hG : IsPGroup p G) (ρ : Representation k G V)
    (h : Coinvariants.ker ρ = ⊤) : Subsingleton V := by
  have hbot := eq_top_of_sup_coinvariantsKer_eq_top hG ρ ⊥ (fun _ => bot_le) (by rw [bot_sup_eq, h])
  refine ⟨fun x y => ?_⟩
  have hx : x ∈ (⊥ : Submodule k V) := hbot ▸ Submodule.mem_top
  have hy : y ∈ (⊥ : Submodule k V) := hbot ▸ Submodule.mem_top
  rw [Submodule.mem_bot] at hx hy
  rw [hx, hy]

end Nakayama

end GroundTheory.GroupCoh
end

