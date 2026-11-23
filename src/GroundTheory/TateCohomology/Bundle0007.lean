module

public import Mathlib
public import GroundTheory.TateCohomology.AugmentationSES
public import GroundTheory.TateCohomology.Bundle0005
public import GroundTheory.TateCohomology.Bundle0006
public import GroundTheory.TateCohomology.Bundle0002

@[expose] public section

-- bundled from GroundTheory.TateCohomology.AugTrivial
section
set_option maxSynthPendingDepth 1

open CategoryTheory groupCohomology Rep

namespace GroundTheory.GroupCoh

universe u

variable (k G : Type u) [CommRing k] [Group G]

noncomputable def augHom : Rep.leftRegular k G ⟶ Rep.trivial k G k :=
  Rep.ofHom ⟨augmentation k G, fun g => LinearMap.ext fun x => by
    change augmentation k G ((Rep.leftRegular k G).ρ g x) = augmentation k G x
    exact augmentation_ρ g x⟩

theorem augIdealι_augHom : augIdealι k G ≫ augHom k G = 0 := by
  ext x
  exact LinearMap.mem_ker.1 x.2

noncomputable def augTrivSES : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (augIdealι k G) (augHom k G) (augIdealι_augHom k G)

theorem augTrivSES_shortExact : (augTrivSES k G).ShortExact := by
  refine shortExact_of_linear (fun a b h => Subtype.ext h)
    (fun r => ⟨MonoidAlgebra.single (1 : G) (show k from r), ?_⟩)
    (fun y hy => ⟨⟨y, LinearMap.mem_ker.2 hy⟩, rfl⟩)
  exact augmentation_single (k := k) (1 : G) (show k from r)

theorem cohTrivial_leftRegular [Fintype G] : CohTrivial (Rep.leftRegular k G) := by
  refine cohTrivial_of_sum_eq _ coeffOneProj fun m => ?_
  induction m using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), Finset.sum_add_distrib, hx, hy]
  | single h c =>
    rw [Fintype.sum_eq_single h]
    · simp [coeffOneProj_apply]
    · intro g hg
      have : g⁻¹ * h ≠ 1 := fun e => hg (inv_mul_eq_one.mp e)
      simp [coeffOneProj_apply, this]

variable {k G}

noncomputable def augIdealSubOne (g : G) : augIdeal k G :=
  ⟨MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 1, by
    rw [LinearMap.mem_ker, map_sub, augmentation_single, augmentation_single, sub_self]⟩

@[simp] theorem augIdealSubOne_val (g : G) :
    ((augIdealSubOne g : augIdeal k G) : MonoidAlgebra k G) =
      MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 1 := rfl

section Cocycle

variable {A : Rep.{u} k G}

noncomputable def cocycleLinear (f : cocycles₁ A) : MonoidAlgebra k G →ₗ[k] A.V :=
  Finsupp.linearCombination k (fun g => f g) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

theorem cocycleLinear_single (f : cocycles₁ A) (g : G) (r : k) :
    cocycleLinear f (MonoidAlgebra.single g r) = r • f g := by
  simp [cocycleLinear]

theorem cocycleLinear_ρ (f : cocycles₁ A) (s : G) (x : MonoidAlgebra k G) :
    cocycleLinear f ((Rep.leftRegular k G).ρ s x) =
      A.ρ s (cocycleLinear f x) + augmentation k G x • f s := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_smul]; abel
  | single g r =>
    have hf : f (s * g) = A.ρ s (f g) + f s := (mem_cocycles₁_iff _).1 f.2 s g
    rw [Representation.ofMulAction_single, smul_eq_mul, cocycleLinear_single, cocycleLinear_single,
      augmentation_single, map_smul, hf, smul_add]

noncomputable def cocycleHom (f : cocycles₁ A) : augIdeal k G ⟶ A :=
  Rep.ofHom ⟨cocycleLinear f ∘ₗ (LinearMap.ker (augmentation k G)).subtype, fun s =>
    LinearMap.ext fun x => by
      have hx : augmentation k G x.1 = 0 := LinearMap.mem_ker.1 x.2
      change cocycleLinear f ((Rep.leftRegular k G).ρ s x.1) = A.ρ s (cocycleLinear f x.1)
      rw [cocycleLinear_ρ, hx, zero_smul, add_zero]⟩

theorem cocycleHom_apply (f : cocycles₁ A) (x : augIdeal k G) :
    (cocycleHom f).hom x = cocycleLinear f x.1 := rfl

theorem cocycleHom_augIdealSubOne (f : cocycles₁ A) (g : G) :
    (cocycleHom f).hom (augIdealSubOne g) = f g := by
  rw [cocycleHom_apply, augIdealSubOne_val, map_sub, cocycleLinear_single, cocycleLinear_single,
    cocycles₁_map_one, smul_zero, sub_zero, one_smul]

end Cocycle

section Restrict

variable (k) {H : Type u} [Group H] (φ : H →* G)

noncomputable def augCocycle : cocycles₁ (Rep.res φ (augIdeal k G)) :=
  ⟨fun h => augIdealSubOne (φ h), (mem_cocycles₁_iff _).2 fun a b => by
    apply Subtype.ext
    change MonoidAlgebra.single (φ (a * b)) (1 : k) - MonoidAlgebra.single 1 1 =
      (Rep.leftRegular k G).ρ (φ a) (MonoidAlgebra.single (φ b) 1 - MonoidAlgebra.single 1 1) +
        (MonoidAlgebra.single (φ a) 1 - MonoidAlgebra.single 1 1)
    rw [map_sub, Representation.ofMulAction_single, Representation.ofMulAction_single, smul_eq_mul,
      smul_eq_mul, mul_one, map_mul]
    abel⟩

theorem augTrivSES_res_shortExact : ((augTrivSES k G).map (resFunctor φ)).ShortExact :=
  (shortExact_res φ).2 (augTrivSES_shortExact k G)

def oneInvariant : (Rep.res φ (Rep.trivial k G k)).ρ.invariants :=
  ⟨(1 : k), fun _ => rfl⟩

theorem δ₀_augTrivSES_res :
    δ (augTrivSES_res_shortExact k φ) 0 1 rfl ((H0Iso _).inv (oneInvariant k φ)) =
      H1π _ (augCocycle k φ) := by
  have hx : ((augTrivSES k G).map (resFunctor φ)).f.hom ∘ (fun h => augIdealSubOne (φ h)) =
      d₀₁ ((augTrivSES k G).map (resFunctor φ)).X₂ (MonoidAlgebra.single (1 : G) (1 : k)) := by
    funext h
    change MonoidAlgebra.single (φ h) (1 : k) - MonoidAlgebra.single 1 1 =
      (Rep.leftRegular k G).ρ (φ h) (MonoidAlgebra.single 1 1) - MonoidAlgebra.single 1 1
    rw [Representation.ofMulAction_single, smul_eq_mul, mul_one]
  exact δ₀_apply (augTrivSES_res_shortExact k φ) (oneInvariant k φ)
    (MonoidAlgebra.single (1 : G) (1 : k)) (by exact augmentation_single (k := k) (1 : G) (1 : k)) _ hx

end Restrict

end GroundTheory.GroupCoh
end

-- bundled from GroundTheory.TateCohomology.PGroupCohTrivialInt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep groupHomology

universe u

section H1

variable {k k' G : Type u} [CommRing k] [CommRing k'] [Group G]

theorem isZero_groupHomology_one_iff (A : Rep.{u} k G) :
    IsZero (groupHomology A 1) ↔ ∀ y : G →₀ A, d₁₀ A y = 0 → ∃ c : G × G →₀ A, d₂₁ A c = y := by
  constructor
  · intro h y hy
    have h0 : H1π A ⟨y, LinearMap.mem_ker.mpr hy⟩ = 0 :=
      @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero h) _ _
    exact LinearMap.mem_range.mp ((H1π_eq_zero_iff _).mp h0)
  · intro h
    have : Subsingleton (groupHomology A 1) := by
      suffices hz : ∀ z : groupHomology A 1, z = 0 from ⟨fun x y => by rw [hz x, hz y]⟩
      intro z
      induction z using H1_induction_on with
      | h z =>
        apply (H1π_eq_zero_iff z).mpr
        exact LinearMap.mem_range.mpr (h z.1 (LinearMap.mem_ker.mp z.2))
    exact ModuleCat.isZero_of_subsingleton _

variable {A : Rep.{u} k G} {B : Rep.{u} k' G}

theorem d₁₀_mapRange_addEquiv (e : A.V ≃+ B.V) (he : ∀ g a, e (A.ρ g a) = B.ρ g (e a))
    (y : G →₀ A) : d₁₀ B (Finsupp.mapRange e (map_zero e) y) = e (d₁₀ A y) := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y₁ y₂ h₁ h₂ => simp only [Finsupp.mapRange_add (map_add e), map_add (f := _), h₁, h₂]
  | single g a => rw [Finsupp.mapRange_single, d₁₀_single, d₁₀_single, map_sub, he]

theorem d₂₁_mapRange_addEquiv (e : A.V ≃+ B.V) (he : ∀ g a, e (A.ρ g a) = B.ρ g (e a))
    (c : G × G →₀ A) :
    d₂₁ B (Finsupp.mapRange e (map_zero e) c) = Finsupp.mapRange e (map_zero e) (d₂₁ A c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp only [Finsupp.mapRange_add (map_add e), map_add (f := _), h₁, h₂]
  | single g a =>
    rw [Finsupp.mapRange_single, d₂₁_single, d₂₁_single, Finsupp.mapRange_add (map_add e),
      Finsupp.mapRange_sub (map_sub e), Finsupp.mapRange_single, Finsupp.mapRange_single,
      Finsupp.mapRange_single, he]

theorem isZero_groupHomology_one_of_addEquiv (e : A.V ≃+ B.V)
    (he : ∀ g a, e (A.ρ g a) = B.ρ g (e a)) (h : IsZero (groupHomology A 1)) :
    IsZero (groupHomology B 1) := by
  rw [isZero_groupHomology_one_iff] at h ⊢
  intro y hy
  have hyy : Finsupp.mapRange e (map_zero e) (Finsupp.mapRange e.symm (map_zero e.symm) y) = y := by
    ext g; simp
  have hy' : d₁₀ A (Finsupp.mapRange e.symm (map_zero e.symm) y) = 0 := by
    apply e.injective
    rw [← d₁₀_mapRange_addEquiv e he, hyy, hy, map_zero]
  obtain ⟨c, hc⟩ := h _ hy'
  exact ⟨Finsupp.mapRange e (map_zero e) c, by rw [d₂₁_mapRange_addEquiv e he, hc, hyy]⟩

end H1

section Torsion

variable {k G : Type u} [CommRing k] [Group G]

theorem nsmul_id_hom_apply (M : Rep.{u} k G) (n : ℕ) (x : M) : (n • 𝟙 M).hom x = n • x := by
  rw [Rep.nsmul_hom]; rfl

theorem nsmul_eq_zero_of_surjective {A B : Rep.{u} k G} (f : A ⟶ B)
    (hf : Function.Surjective f.hom) {n : ℕ} (hA : ∀ x : A, n • x = 0) (y : B) : n • y = 0 := by
  obtain ⟨x, rfl⟩ := hf y
  change n • f.hom.toLinearMap x = 0
  rw [← map_nsmul, hA, map_zero]

theorem nsmul_eq_zero_of_injective {A B : Rep.{u} k G} (f : A ⟶ B)
    (hf : Function.Injective f.hom) {n : ℕ} (hB : ∀ y : B, n • y = 0) (x : A) : n • x = 0 := by
  apply hf
  change f.hom.toLinearMap (n • x) = f.hom.toLinearMap 0
  rw [map_nsmul, map_zero]
  exact hB _

theorem nsmul_eq_zero_coind (M : Rep.{u} k G) {n : ℕ} (hM : ∀ x : M, n • x = 0)
    (x : coind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype M)) : n • x = 0 :=
  Subtype.ext (funext fun g => hM (x.1 g))

theorem nsmul_eq_zero_coindShift (M : Rep.{u} k G) {n : ℕ} (hM : ∀ x : M, n • x = 0) :
    ∀ y : coindShift M, n • y = 0 :=
  nsmul_eq_zero_of_surjective (coindSES.obj M).g
    ((Rep.epi_iff_surjective _).1 (coindSES_shortExact M).epi_g) (nsmul_eq_zero_coind M hM)

theorem nsmul_eq_zero_indShift [Fintype G] (M : Rep.{u} k G) {n : ℕ} (hM : ∀ x : M, n • x = 0) :
    ∀ y : indShift M, n • y = 0 := by
  classical
  let e := indCoindIso (G := G) (res (⊥ : Subgroup G).subtype M)
  have he : Function.Injective e.hom.hom := (Rep.mono_iff_injective e.hom).1 inferInstance
  have h₂ := nsmul_eq_zero_of_injective e.hom he (nsmul_eq_zero_coind M hM)
  exact nsmul_eq_zero_of_injective (indSES.obj M).f
    ((Rep.mono_iff_injective _).1 (indSES_shortExact M).mono_f) h₂

end Torsion

section ZMod

variable {G : Type} [Group G] (p : ℕ) [Fact p.Prime]

noncomputable def zmodRep (M : Rep ℤ G) (hM : ∀ x : M, p • x = 0) : Rep (ZMod p) G :=
  letI : Module (ZMod p) M := AddCommGroup.zmodModule hM
  Rep.of (X := M)
    { toFun := fun g => AddMonoidHom.toZModLinearMap p (M.ρ g).toAddMonoidHom
      map_one' := by ext x; simp
      map_mul' := fun g h => by ext x; simp }

variable [Fintype G]

theorem tateAcyclic_cohTrivial_of_isZero_neg_two_of_nsmul_eq_zero {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) (M : Rep ℤ G) (hM : ∀ x : M, p • x = 0)
    (h : IsZero (tateCohomology M (-2))) : TateAcyclic M ∧ CohTrivial M := by
  have h1 : IsZero (groupHomology M 1) := h.of_iso (tateNegTwoIsoH1 M).symm
  have h1' : IsZero (groupHomology (zmodRep p M hM) 1) :=
    isZero_groupHomology_one_of_addEquiv (AddEquiv.refl M.V) (fun _ _ => rfl) h1
  obtain ⟨ι, ⟨e⟩⟩ := exists_iso_free_of_isZero_groupHomology_one hG _ h1'
  have := free_asModule_of_iso_free e
  obtain ⟨φ, hφ⟩ := exists_sum_eq_of_basis (zmodRep p M hM) (Module.Free.chooseBasis _ _)
  refine ⟨tateAcyclic_of_sum_eq M
      (@LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) M.V M.V _ _ M.hV2 M.hV2 ⟨φ, map_add φ⟩ ?_) hφ,
    cohTrivial_of_sum_eq M
      (@LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) M.V M.V _ _ M.hV2 M.hV2 ⟨φ, map_add φ⟩ ?_) hφ⟩
  all_goals
    intro n x
    have hmod : M.hV2 = AddCommGroup.toIntModule M.V := Subsingleton.elim _ _
    rw [hmod]
    exact map_zsmul φ n x

theorem tateAcyclic_cohTrivial_of_isZero_of_nsmul_eq_zero {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) (M : Rep ℤ G) (hM : ∀ x : M, p • x = 0) (q : ℤ)
    (hq : IsZero (tateCohomology M q)) : TateAcyclic M ∧ CohTrivial M :=
  tateAcyclic_cohTrivial_of_isZero_of_shift (fun M => ∀ x : M, p • x = 0)
    (fun M hM => nsmul_eq_zero_coindShift M hM) (fun M hM => nsmul_eq_zero_indShift M hM)
    (fun M hM h => tateAcyclic_cohTrivial_of_isZero_neg_two_of_nsmul_eq_zero hG M hM h) q M hM hq

end ZMod

end GroundTheory.GroupCoh
end

-- bundled from GroundTheory.TateCohomology.PullbackExtension
section
set_option maxSynthPendingDepth 1

open CategoryTheory

namespace GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable (S : ShortComplex (Rep.{u} k G)) {Y : Rep.{u} k G} (β : Y ⟶ S.X₃)

def pullbackSubmodule : Submodule k (S.X₂.V × Y.V) :=
  LinearMap.ker (S.g.hom.toLinearMap ∘ₗ LinearMap.fst k S.X₂.V Y.V -
    β.hom.toLinearMap ∘ₗ LinearMap.snd k S.X₂.V Y.V)

variable {S β} in
theorem mem_pullbackSubmodule {p : S.X₂.V × Y.V} :
    p ∈ pullbackSubmodule S β ↔ S.g.hom p.1 = β.hom p.2 := by
  simp [pullbackSubmodule, sub_eq_zero]

theorem pullbackSubmodule_le_comap (g : G) :
    pullbackSubmodule S β ≤ (pullbackSubmodule S β).comap ((S.X₂.ρ.prod Y.ρ) g) := by
  intro p hp
  rw [Submodule.mem_comap, mem_pullbackSubmodule]
  rw [mem_pullbackSubmodule] at hp
  simp [Rep.hom_comm_apply, hp]

noncomputable abbrev pullbackRep : Rep.{u} k G :=
  Rep.subrepresentation (Rep.of (S.X₂.ρ.prod Y.ρ)) (pullbackSubmodule S β)
    (pullbackSubmodule_le_comap S β)

noncomputable def pullbackFst : pullbackRep S β ⟶ S.X₂ :=
  Rep.ofHom ⟨LinearMap.fst k S.X₂.V Y.V ∘ₗ (pullbackSubmodule S β).subtype, fun _ => rfl⟩

noncomputable def pullbackSnd : pullbackRep S β ⟶ Y :=
  Rep.ofHom ⟨LinearMap.snd k S.X₂.V Y.V ∘ₗ (pullbackSubmodule S β).subtype, fun _ => rfl⟩

theorem g_apply_f_apply (x : S.X₁) : S.g.hom (S.f.hom x) = 0 := by
  change (S.f ≫ S.g).hom x = 0
  rw [S.zero]
  rfl

noncomputable def pullbackιLinear : S.X₁.V →ₗ[k] pullbackSubmodule S β :=
  LinearMap.codRestrict (pullbackSubmodule S β)
    (LinearMap.prod S.f.hom.toLinearMap 0) fun x => by
      rw [mem_pullbackSubmodule]
      simp [g_apply_f_apply]

noncomputable def pullbackι : S.X₁ ⟶ pullbackRep S β :=
  Rep.ofHom ⟨pullbackιLinear S β, fun g => by
    refine LinearMap.ext fun x => Subtype.ext (Prod.ext ?_ ?_)
    · simp [pullbackιLinear, Rep.hom_comm_apply]
    · simp [pullbackιLinear]⟩

theorem pullbackι_pullbackSnd : pullbackι S β ≫ pullbackSnd S β = 0 := by
  ext x
  rfl

noncomputable def pullbackSES : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (pullbackι S β) (pullbackSnd S β) (pullbackι_pullbackSnd S β)


variable {S} in
theorem pullbackSES_shortExact (hS : S.ShortExact) : (pullbackSES S β).ShortExact := by
  have hex := function_exact_of_shortExact hS
  have hinj : Function.Injective S.f.hom := (Rep.mono_iff_injective _).1 hS.mono_f
  have hsurj : Function.Surjective S.g.hom := (Rep.epi_iff_surjective _).1 hS.epi_g
  refine shortExact_of_linear ?_ ?_ ?_
  · intro a b hab
    exact hinj (congrArg (fun p : pullbackRep S β => p.1.1) hab)
  · intro y
    obtain ⟨x, hx⟩ := hsurj (β.hom y)
    exact ⟨⟨(x, y), mem_pullbackSubmodule.2 hx⟩, rfl⟩
  · intro p hp
    have hp2 : p.1.2 = 0 := hp
    have hg : S.g.hom p.1.1 = 0 := by
      rw [(mem_pullbackSubmodule.1 p.2), hp2, map_zero]
    obtain ⟨x, hx⟩ := (hex p.1.1).1 hg
    refine ⟨x, Subtype.ext (Prod.ext hx hp2.symm)⟩

end GroundTheory.GroupCoh
end

