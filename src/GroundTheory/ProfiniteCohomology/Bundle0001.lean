module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.ProfiniteCohomology.AdditiveHilbert
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory CategoryTheory.Limits

universe u

section NormalBasis

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem normalBasis_repr_apply_smul (σ τ : Gal(L/K)) (y : L) :
    (IsGalois.normalBasis K L).repr (σ y) τ = (IsGalois.normalBasis K L).repr y (σ⁻¹ * τ) := by
  have hb (ρ : Gal(L/K)) :
      σ (IsGalois.normalBasis K L ρ) = IsGalois.normalBasis K L (σ * ρ) := by
    rw [IsGalois.normalBasis_apply (σ * ρ), IsGalois.normalBasis_apply ρ, AlgEquiv.mul_apply]
  have key : (Finsupp.lapply τ ∘ₗ (IsGalois.normalBasis K L).repr.toLinearMap ∘ₗ σ.toLinearMap :
      L →ₗ[K] K) = Finsupp.lapply (σ⁻¹ * τ) ∘ₗ (IsGalois.normalBasis K L).repr.toLinearMap := by
    refine (IsGalois.normalBasis K L).ext fun ρ => ?_
    change (IsGalois.normalBasis K L).repr (σ (IsGalois.normalBasis K L ρ)) τ =
      (IsGalois.normalBasis K L).repr (IsGalois.normalBasis K L ρ) (σ⁻¹ * τ)
    classical
    rw [hb, Module.Basis.repr_self, Module.Basis.repr_self]
    simp only [Finsupp.single_apply, eq_inv_mul_iff_mul_eq]
  exact LinearMap.congr_fun key y

end NormalBasis

section Coinduced

variable (k : Type u) (K L : Type u) [CommRing k] [Field K] [Field L] [Algebra K L]
  [Algebra k K] [Algebra k L] [IsScalarTower k K L] [FiniteDimensional K L] [IsGalois K L]

noncomputable def galoisCoindIso :
    Rep.ofDistribMulAction k Gal(L/K) L ≅
      Rep.coind (⊥ : Subgroup Gal(L/K)).subtype (Rep.trivial k (⊥ : Subgroup Gal(L/K)) K) := by
  have htop : (Representation.trivial k (⊥ : Subgroup Gal(L/K)) K).coindV
      (⊥ : Subgroup Gal(L/K)).subtype = ⊤ := by
    ext f
    simp only [Representation.mem_coindV, Submodule.mem_top, iff_true]
    rintro ⟨g, hg⟩ h
    rw [Subgroup.mem_bot] at hg
    subst hg
    simp
  let e : L ≃ₗ[k] _ :=
    ((IsGalois.normalBasis K L).equivFun.restrictScalars k).trans
      ((LinearEquiv.funCongrLeft k K (Equiv.inv Gal(L/K))).trans (LinearEquiv.ofTop _ htop).symm)
  refine Rep.mkIso (Representation.Equiv.mk e fun σ => ?_)
  refine LinearMap.ext fun y => Subtype.ext (funext fun h => ?_)
  change (IsGalois.normalBasis K L).repr (σ y) h⁻¹ =
    (IsGalois.normalBasis K L).repr y (h * σ)⁻¹
  rw [normalBasis_repr_apply_smul, mul_inv_rev]

end Coinduced

section Vanishing

open groupCohomology

variable (k : Type u) (K L : Type u) [CommRing k] [Field K] [Field L] [Algebra K L]
  [Algebra k K] [Algebra k L] [IsScalarTower k K L] [FiniteDimensional K L] [IsGalois K L]

theorem isZero_groupCohomology_succ (n : ℕ) :
    IsZero (groupCohomology (Rep.ofDistribMulAction k Gal(L/K) L) (n + 1)) :=
  (isZero_groupCohomology_succ_of_subsingleton
      (Rep.trivial k (⊥ : Subgroup Gal(L/K)) K) n).of_iso
    ((groupCohomology.functor k Gal(L/K) (n + 1)).mapIso (galoisCoindIso k K L) ≪≫
      groupCohomology.coindIso _ (n + 1))

theorem isZero_groupCohomology {n : ℕ} (hn : n ≠ 0) :
    IsZero (groupCohomology (Rep.ofDistribMulAction k Gal(L/K) L) n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact isZero_groupCohomology_succ k K L m

theorem isZero_groupCohomology_galois {n : ℕ} (hn : n ≠ 0) :
    IsZero (groupCohomology (Rep.ofDistribMulAction K Gal(L/K) L) n) :=
  isZero_groupCohomology K K L hn

end Vanishing

section Integral

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

end Integral

end GroundTheory.ProfCoh
end

-- bundled from GroundTheory.ProfiniteCohomology.DiscreteModules
section
namespace GroundTheory.ProfCoh

open CategoryTheory

universe w u v

variable {k : Type u} {G : Type v} [CommRing k] [Group G]

def stabilizer {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V) (v : V) :
    Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha]
      _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply]

@[simp]
theorem mem_stabilizer {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (v : V) (g : G) : g ∈ stabilizer ρ v ↔ ρ g v = v :=
  Iff.rfl

variable [TopologicalSpace G]

class IsDiscreteRep (A : Rep.{w} k G) : Prop where
  isOpen_stabilizer : ∀ a : A, IsOpen (stabilizer A.ρ a : Set G)

theorem isOpen_stabilizer (A : Rep.{w} k G) [IsDiscreteRep A] (a : A) :
    IsOpen (stabilizer A.ρ a : Set G) :=
  IsDiscreteRep.isOpen_stabilizer a

theorem isDiscreteRep_iff (A : Rep.{w} k G) :
    IsDiscreteRep A ↔ ∀ a : A, IsOpen (stabilizer A.ρ a : Set G) :=
  ⟨fun h => h.isOpen_stabilizer, fun h => ⟨h⟩⟩


variable (k G) in
def isDiscreteRep : ObjectProperty (Rep.{w} k G) := fun A => IsDiscreteRep A


end GroundTheory.ProfCoh
end

-- bundled from GroundTheory.ProfiniteCohomology.FilteredHomology
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

section Elements

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat.{u} R) c)

theorem exists_iCycles_eq {i : ι} (x : K.X i) (hx : (K.d i (c.next i)).hom x = 0) :
    ∃ z : K.cycles i, (K.iCycles i).hom z = x := by
  refine ⟨(K.sc i).moduleCatCyclesIso.inv ⟨x, hx⟩, ?_⟩
  have := ShortComplex.moduleCatCyclesIso_inv_iCycles_apply (K.sc i) ⟨x, hx⟩
  exact this

theorem shortComplex_homologyπ_eq_zero_iff (S : ShortComplex (ModuleCat.{u} R)) (z : S.cycles) :
    S.homologyπ.hom z = 0 ↔ ∃ w : S.X₁, S.f.hom w = S.iCycles.hom z := by
  have hinj : Function.Injective S.moduleCatHomologyIso.hom.hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have h1 : S.moduleCatHomologyIso.hom.hom (S.homologyπ.hom z) =
      S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom.hom z) :=
    ShortComplex.π_moduleCatCyclesIso_hom_apply S z
  have h2 : S.moduleCatLeftHomologyData.i.hom (S.moduleCatCyclesIso.hom.hom z) =
      S.iCycles.hom z :=
    ShortComplex.moduleCatCyclesIso_hom_i_apply S z
  have h0 : S.homologyπ.hom z = 0 ↔ S.moduleCatHomologyIso.hom.hom (S.homologyπ.hom z) = 0 :=
    ⟨fun h => by rw [h, map_zero], fun h => hinj (h.trans (map_zero _).symm)⟩
  rw [h0, h1]
  change Submodule.Quotient.mk (p := LinearMap.range S.moduleCatToCycles)
    (S.moduleCatCyclesIso.hom.hom z) = 0 ↔ _
  refine (Submodule.Quotient.mk_eq_zero (LinearMap.range S.moduleCatToCycles)
    (x := (S.moduleCatCyclesIso.hom.hom z : LinearMap.ker S.g.hom))).trans ?_
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, (congrArg S.moduleCatLeftHomologyData.i.hom hw).trans h2⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, (ModuleCat.mono_iff_injective S.moduleCatLeftHomologyData.i).1 inferInstance
      (hw.trans h2.symm)⟩

theorem homologyπ_eq_zero_iff {i : ι} (z : K.cycles i) :
    (K.homologyπ i).hom z = 0 ↔
      ∃ w : K.X (c.prev i), (K.d (c.prev i) i).hom w = (K.iCycles i).hom z :=
  shortComplex_homologyπ_eq_zero_iff (K.sc i) z

end Elements

section Apply

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat.{u} R) c}

theorem hom_f_d_apply (φ : K ⟶ L) (i j : ι) (x : K.X i) :
    (φ.f j).hom ((K.d i j).hom x) = (L.d i j).hom ((φ.f i).hom x) :=
  (congrArg (fun g => ModuleCat.Hom.hom g x) (φ.comm i j)).symm

theorem iCycles_d_apply (K : HomologicalComplex (ModuleCat.{u} R) c) (i j : ι) (z : K.cycles i) :
    (K.d i j).hom ((K.iCycles i).hom z) = 0 := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, K.iCycles_d, ModuleCat.hom_zero,
    LinearMap.zero_apply]

theorem iCycles_cyclesMap_apply (φ : K ⟶ L) (i : ι) (z : K.cycles i) :
    (L.iCycles i).hom ((HomologicalComplex.cyclesMap φ i).hom z) =
      (φ.f i).hom ((K.iCycles i).hom z) :=
  congrArg (fun g => ModuleCat.Hom.hom g z) (HomologicalComplex.cyclesMap_i φ i)

theorem homologyMap_homologyπ_apply (φ : K ⟶ L) (i : ι) (z : K.cycles i) :
    (HomologicalComplex.homologyMap φ i).hom ((K.homologyπ i).hom z) =
      (L.homologyπ i).hom ((HomologicalComplex.cyclesMap φ i).hom z) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.homologyπ_naturality]
  rfl

end Apply

section Filtered

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  {J : Type u} [SmallCategory J] [IsFiltered J]
  {F : J ⥤ HomologicalComplex (ModuleCat.{u} R) c} (t : Cocone F)

omit [IsFiltered J] in
theorem cocone_w_apply {j j' : J} (f : j ⟶ j') (i : ι) (y : (F.obj j).X i) :
    ((t.ι.app j').f i).hom (((F.map f).f i).hom y) = ((t.ι.app j).f i).hom y :=
  congrArg (fun φ : F.obj j ⟶ t.pt => (φ.f i).hom y) (t.w f)


omit [IsFiltered J] in
theorem exists_homologyMap_eq_of_cocone (i : ι)
    (hsurj : ∀ x : t.pt.X i, ∃ (j : J) (y : (F.obj j).X i), ((t.ι.app j).f i).hom y = x)
    (hinj : ∀ (j : J) (y : (F.obj j).X (c.next i)), ((t.ι.app j).f (c.next i)).hom y = 0 →
      ∃ (j' : J) (f : j ⟶ j'), ((F.map f).f (c.next i)).hom y = 0)
    (z : t.pt.homology i) :
    ∃ (j : J) (y : (F.obj j).homology i),
      (HomologicalComplex.homologyMap (t.ι.app j) i).hom y = z := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (t.pt.homologyπ i)).1 inferInstance z
  obtain ⟨j, y, hy⟩ := hsurj ((t.pt.iCycles i).hom z)
  have hdy : ((t.ι.app j).f (c.next i)).hom (((F.obj j).d i (c.next i)).hom y) = 0 := by
    rw [hom_f_d_apply, hy]
    exact iCycles_d_apply t.pt i _ z
  obtain ⟨j', f, hf⟩ := hinj j _ hdy
  rw [hom_f_d_apply] at hf
  obtain ⟨z', hz'⟩ := exists_iCycles_eq (F.obj j') (((F.map f).f i).hom y) hf
  refine ⟨j', (HomologicalComplex.homologyπ (F.obj j') i).hom z', ?_⟩
  rw [homologyMap_homologyπ_apply]
  congr 1
  apply (ModuleCat.mono_iff_injective (t.pt.iCycles i)).1 inferInstance
  rw [iCycles_cyclesMap_apply, hz', cocone_w_apply, hy]

theorem exists_homologyMap_map_eq_zero_of_cocone (i : ι)
    (hsurj : ∀ x : t.pt.X (c.prev i),
      ∃ (j : J) (y : (F.obj j).X (c.prev i)), ((t.ι.app j).f (c.prev i)).hom y = x)
    (hinj : ∀ (j : J) (y : (F.obj j).X i), ((t.ι.app j).f i).hom y = 0 →
      ∃ (j' : J) (f : j ⟶ j'), ((F.map f).f i).hom y = 0)
    (j : J) (y : (F.obj j).homology i)
    (hy : (HomologicalComplex.homologyMap (t.ι.app j) i).hom y = 0) :
    ∃ (j' : J) (f : j ⟶ j'), (HomologicalComplex.homologyMap (F.map f) i).hom y = 0 := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective ((F.obj j).homologyπ i)).1 inferInstance y
  rw [homologyMap_homologyπ_apply, homologyπ_eq_zero_iff, iCycles_cyclesMap_apply] at hy
  obtain ⟨w, hw⟩ := hy
  obtain ⟨j₁, v, hv⟩ := hsurj w
  let m := IsFiltered.max j j₁
  let a : j ⟶ m := IsFiltered.leftToMax j j₁
  let b : j₁ ⟶ m := IsFiltered.rightToMax j j₁
  let e : (F.obj m).X i := ((F.map a).f i).hom (((F.obj j).iCycles i).hom z) -
    ((F.obj m).d (c.prev i) i).hom (((F.map b).f (c.prev i)).hom v)
  have he : ((t.ι.app m).f i).hom e = 0 := by
    simp only [e, map_sub]
    rw [cocone_w_apply, hom_f_d_apply, cocone_w_apply, hv]
    exact sub_eq_zero.2 hw.symm
  obtain ⟨j', g, hg⟩ := hinj m e he
  refine ⟨j', a ≫ g, ?_⟩
  rw [homologyMap_homologyπ_apply, homologyπ_eq_zero_iff, iCycles_cyclesMap_apply]
  refine ⟨((F.map (b ≫ g)).f (c.prev i)).hom v, ?_⟩
  simp only [e, map_sub, sub_eq_zero] at hg
  rw [F.map_comp, F.map_comp, HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [← hom_f_d_apply]
  exact hg.symm

end Filtered

end GroundTheory.ProfCoh
end

-- bundled from GroundTheory.ProfiniteCohomology.ProcyclicDefs
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

variable {G : Type*} [Group G] [TopologicalSpace G]

def IsTopologicalGenerator (σ : G) : Prop :=
  Dense (Subgroup.zpowers σ : Set G)

theorem _root_.IsLocallyConstant.eq_of_eqOn_dense {X Y : Type*} [TopologicalSpace X] {f g : X → Y}
    (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) {s : Set X} (hs : Dense s)
    (h : Set.EqOn f g s) : f = g := by
  let _ : TopologicalSpace Y := ⊥
  have : DiscreteTopology Y := ⟨rfl⟩
  exact Continuous.ext_on hs hf.continuous hg.continuous h

namespace IsTopologicalGenerator

variable {σ : G}

theorem eq_of_forall_zpow (hσ : IsTopologicalGenerator σ) {Y : Type*} {f g : G → Y}
    (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) (h : ∀ n : ℤ, f (σ ^ n) = g (σ ^ n)) :
    f = g :=
  hf.eq_of_eqOn_dense hg hσ fun _ ⟨n, hn⟩ => hn ▸ h n

theorem eq_of_forall_zpow_pi (hσ : IsTopologicalGenerator σ) {n : ℕ} {Y : Type*}
    {f g : (Fin n → G) → Y} (hf : IsLocallyConstant f) (hg : IsLocallyConstant g)
    (h : ∀ m : Fin n → ℤ, f (fun i => σ ^ m i) = g (fun i => σ ^ m i)) : f = g := by
  refine hf.eq_of_eqOn_dense hg (s := Set.univ.pi fun _ => (Subgroup.zpowers σ : Set G))
    (dense_pi Set.univ fun _ _ => hσ) fun x hx => ?_
  choose m hm using fun i => hx i (Set.mem_univ i)
  have hx' : x = fun i => σ ^ m i := funext fun i => (hm i).symm
  rw [hx']
  exact h m

end IsTopologicalGenerator

end GroundTheory.ProfCoh
end

