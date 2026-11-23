module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.CupProducts
public import GroundTheory.ProfiniteCohomology.CupProducts.Cocycles
public import GroundTheory.ProfiniteCohomology.ContinuousCochains.LongExactSequence

@[expose] public section

-- bundled from GroundTheory.ProfiniteCohomology.CupProducts.CohomologyMapRightUnitorCupUnitClass
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory groupCohomology GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Associativity

variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]

end Associativity

section Unit


omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem d_oneCochain :
    (inhomogeneousCochains.d (𝟙_ (Rep.{u} k G)) 0).hom (oneCochain (k := k) (G := G)) = 0 := by
  funext g
  simp [inhomogeneousCochains.d_hom_apply, oneCochain]
  rfl

def unitCocycle : cocycles (𝟙_ (Rep.{u} k G)) 0 :=
  (cochainsComplex (𝟙_ (Rep.{u} k G))).cyclesMk
    (mkCochain (A := 𝟙_ (Rep.{u} k G)) oneCochain (IsLocallyConstant.const _)) 1 (by simp) (by
      apply cochainOf_injective (A := 𝟙_ (Rep.{u} k G))
      exact (cochainOf_d (A := 𝟙_ (Rep.{u} k G)) _).trans d_oneCochain)

@[simp]
theorem cochainOf_cocycleι_unitCocycle :
    cochainOf (A := 𝟙_ (Rep.{u} k G))
      (cocycleι (A := 𝟙_ (Rep.{u} k G)) (p := 0) unitCocycle) = oneCochain :=
  congrArg (cochainOf (A := 𝟙_ (Rep.{u} k G)))
    ((cochainsComplex (𝟙_ (Rep.{u} k G))).i_cyclesMk _ _ _ _)

def unitClass : cohomology (𝟙_ (Rep.{u} k G)) 0 :=
  cohomologyπ _ 0 unitCocycle

variable {A : Rep.{u} k G} [IsDiscreteRep A]

theorem cohomologyMap_leftUnitor_unitClass_cup {q : ℕ} (x : cohomology A q) :
    cohomologyMap (λ_ A).hom q (cup (zero_add q) unitClass x) = x := by
  refine cohomology_induction_on x fun x => ?_
  rw [unitClass, cup_cohomologyπ, cohomologyMap_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cyclesMap]
  simp only [cocycleι_cupCocycles, cochainOf_cupLocallyConstant, cochainOf_cocycleι_unitCocycle]
  funext g
  exact leftUnitor_oneCochain_cupCochain _ g

theorem cohomologyMap_rightUnitor_cup_unitClass {p : ℕ} (x : cohomology A p) :
    cohomologyMap (ρ_ A).hom p (cup (add_zero p) x unitClass) = x := by
  refine cohomology_induction_on x fun x => ?_
  rw [unitClass, cup_cohomologyπ, cohomologyMap_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cyclesMap]
  simp only [cocycleι_cupCocycles, cochainOf_cupLocallyConstant, cochainOf_cocycleι_unitCocycle]
  funext g
  exact rightUnitor_cupCochain_oneCochain _ g

end Unit

end GroundTheory.ProfCoh
end
end

-- bundled from GroundTheory.ProfiniteCohomology.CupProducts.ExistsCocycleMapFEqD
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory groupCohomology GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Cochains

variable {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B]

theorem cochainOf_cochainsMap_f (f : A ⟶ B) {i : ℕ} (a : (cochainsComplex A).X i) :
    cochainOf (A := B) ((cochainsMap f).f i a) = fun σ => f.hom (cochainOf (A := A) a σ) :=
  rfl

end Cochains

section Connecting

variable {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
  [IsDiscreteRep S.X₃]

theorem δ_cohomologyπ_of_lift (hS : S.ShortExact) {i j : ℕ} (hij : i + 1 = j)
    (x₃ : cocycles S.X₃ i) (x₂ : (cochainsComplex S.X₂).X i)
    (hx₂ : (cochainsMap S.g).f i x₂ = cocycleι (A := S.X₃) (p := i) x₃) (x₁ : cocycles S.X₁ j)
    (hx₁ : (cochainsMap S.f).f j (cocycleι (A := S.X₁) (p := j) x₁) =
      (cochainsComplex S.X₂).d i j x₂) :
    δ hS i j hij (cohomologyπ S.X₃ i x₃) = cohomologyπ S.X₁ j x₁ := by
  have hx₃ : (cochainsComplex S.X₃).d i j (cocycleι (A := S.X₃) (p := i) x₃) = 0 :=
    ConcreteCategory.congr_hom ((cochainsComplex S.X₃).iCycles_d i j) x₃
  have key := (cochainsShortComplex_shortExact hS).δ_apply i j hij
    (cocycleι (A := S.X₃) (p := i) x₃) hx₃ x₂ hx₂ (cocycleι (A := S.X₁) (p := j) x₁) hx₁
    (j + 1) (by simp)
  have e3 : (cochainsComplex S.X₃).cyclesMk (cocycleι (A := S.X₃) (p := i) x₃) j
      ((ComplexShape.up ℕ).next_eq' hij) hx₃ = x₃ :=
    cocycleι_injective ((cochainsComplex S.X₃).i_cyclesMk _ _ _ _)
  have e1 : (cochainsComplex S.X₁).cyclesMk (cocycleι (A := S.X₁) (p := j) x₁) (j + 1) (by simp)
      ((cochainsShortComplex_shortExact hS).d_eq_zero_of_f_eq_d_apply i j x₂
        (cocycleι (A := S.X₁) (p := j) x₁) hx₁ (j + 1)) = x₁ :=
    cocycleι_injective ((cochainsComplex S.X₁).i_cyclesMk _ _ _ _)
  calc δ hS i j hij (cohomologyπ S.X₃ i x₃)
      = δ hS i j hij (cohomologyπ S.X₃ i ((cochainsComplex S.X₃).cyclesMk
          (cocycleι (A := S.X₃) (p := i) x₃) j ((ComplexShape.up ℕ).next_eq' hij) hx₃)) := by rw [e3]
    _ = cohomologyπ S.X₁ j ((cochainsComplex S.X₁).cyclesMk (cocycleι (A := S.X₁) (p := j) x₁) (j + 1)
          (by simp) ((cochainsShortComplex_shortExact hS).d_eq_zero_of_f_eq_d_apply i j x₂
            (cocycleι (A := S.X₁) (p := j) x₁) hx₁ (j + 1))) := key
    _ = cohomologyπ S.X₁ j x₁ := by rw [e1]

theorem exists_cocycle_map_f_eq_d (hS : S.ShortExact) {i : ℕ} (j : ℕ)
    (x₃ : cocycles S.X₃ i) (x₂ : (cochainsComplex S.X₂).X i)
    (hx₂ : (cochainsMap S.g).f i x₂ = cocycleι (A := S.X₃) (p := i) x₃) :
    ∃ x₁ : cocycles S.X₁ j, (cochainsMap S.f).f j (cocycleι (A := S.X₁) (p := j) x₁) =
      (cochainsComplex S.X₂).d i j x₂ := by
  have hex := (HomologicalComplex.exact_iff_degreewise_exact _).1
    (cochainsShortComplex_shortExact hS).exact j
  rw [ShortComplex.moduleCat_exact_iff] at hex
  have hz : ((cochainsMap S.g).f j).hom ((cochainsComplex S.X₂).d i j x₂) = 0 := by
    have hc := ConcreteCategory.congr_hom ((cochainsMap S.g).comm i j) x₂
    have hd := ConcreteCategory.congr_hom ((cochainsComplex S.X₃).iCycles_d i j) x₃
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hc
    rw [ConcreteCategory.comp_apply] at hd
    rw [← hc, hx₂]
    exact hd
  obtain ⟨x₁, hx₁⟩ := hex _ hz
  have hx₁' : (cochainsMap S.f).f j x₁ = (cochainsComplex S.X₂).d i j x₂ := hx₁
  refine ⟨(cochainsComplex S.X₁).cyclesMk x₁ (j + 1) (by simp)
    ((cochainsShortComplex_shortExact hS).d_eq_zero_of_f_eq_d_apply i j x₂ x₁ hx₁' (j + 1)), ?_⟩
  have e : cocycleι (A := S.X₁) (p := j) ((cochainsComplex S.X₁).cyclesMk x₁ (j + 1) (by simp)
      ((cochainsShortComplex_shortExact hS).d_eq_zero_of_f_eq_d_apply i j x₂ x₁ hx₁'
        (j + 1))) = x₁ :=
    (cochainsComplex S.X₁).i_cyclesMk _ _ _ _
  rw [e]
  exact hx₁'

end Connecting

section TensorRight

variable {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
  [IsDiscreteRep S.X₃] (B : Rep.{u} k G) [IsDiscreteRep B]

variable {B}

end TensorRight

section TensorLeft

variable {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
  [IsDiscreteRep S.X₃] (B : Rep.{u} k G) [IsDiscreteRep B]

variable {B}

end TensorLeft

end GroundTheory.ProfCoh
end
end

-- bundled from GroundTheory.ProfiniteCohomology.CupProducts.Functoriality
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory TensorProduct groupCohomology GroundTheory.GroupCoh

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

theorem partialProd_comp_monoidHom {M N : Type*} [Monoid M] [Monoid N] {m : ℕ} (φ : M →* N)
    (x : Fin m → M) (j : Fin (m + 1)) :
    Fin.partialProd (⇑φ ∘ x) j = φ (Fin.partialProd x j) := by
  induction j using Fin.induction with
  | zero => simp
  | succ j ih =>
    rw [Fin.partialProd_succ, Fin.partialProd_succ, ih, map_mul]
    rfl

section Tensor

variable (φ : H →* G)

def resTensorHom {A B : Rep.{u} k G} {A' B' : Rep.{u} k H} (f : Rep.res φ A ⟶ A')
    (g : Rep.res φ B ⟶ B') : Rep.res φ (A ⊗ B) ⟶ A' ⊗ B' :=
  (f ⊗ₘ g : Rep.res φ A ⊗ Rep.res φ B ⟶ A' ⊗ B')

@[simp]
theorem resTensorHom_tmul {A B : Rep.{u} k G} {A' B' : Rep.{u} k H} (f : Rep.res φ A ⟶ A')
    (g : Rep.res φ B ⟶ B') (a : A) (b : B) :
    (resTensorHom φ f g).hom (a ⊗ₜ[k] b : (A ⊗ B : Rep k G)) = f.hom a ⊗ₜ[k] g.hom b :=
  rfl

def resTensorIso (A B : Rep.{u} k G) : Rep.res φ (A ⊗ B) ≅ Rep.res φ A ⊗ Rep.res φ B :=
  Iso.refl (Rep.res φ A ⊗ Rep.res φ B)

end Tensor

variable [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]

section Naturality

variable {A A' B B' : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep A'] [IsDiscreteRep B]
  [IsDiscreteRep B'] {p q n : ℕ}


omit [TopologicalSpace H] [IsTopologicalGroup H] in
theorem cohomologyMap_tensorHom_cup (f : A ⟶ A') (g : B ⟶ B') (h : p + q = n)
    (x : cohomology A p) (y : cohomology B q) :
    cohomologyMap (f ⊗ₘ g) n (cup h x y) = cup h (cohomologyMap f p x) (cohomologyMap g q y) := by
  induction x using cohomology_induction_on with | h x => ?_
  induction y using cohomology_induction_on with | h y => ?_
  rw [cup_cohomologyπ, cohomologyMap_cohomologyπ, cohomologyMap_cohomologyπ,
    cohomologyMap_cohomologyπ, cup_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cyclesMap, cocycleι_cupCocycles, cocycleι_cupCocycles,
    cochainOf_cupLocallyConstant, cochainOf_cupLocallyConstant, cochainOf_cocycleι_cyclesMap,
    cochainOf_cocycleι_cyclesMap]
  funext s
  exact tensorHom_cupCochain f g h _ _ s


omit [TopologicalSpace H] [IsTopologicalGroup H] in
theorem cohomologyMap_whiskerRight_cup (f : A ⟶ A') (h : p + q = n) (x : cohomology A p)
    (y : cohomology B q) :
    cohomologyMap (f ▷ B) n (cup h x y) = cup h (cohomologyMap f p x) y := by
  have := cohomologyMap_tensorHom_cup f (𝟙 B) h x y
  rwa [cohomologyMap_id, tensorHom_id] at this

end Naturality

section MapAlong

variable (φ : H →* G) (hφ : Continuous φ) {A B : Rep.{u} k G} {A' B' : Rep.{u} k H}
  [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep A'] [IsDiscreteRep B'] {p q n : ℕ}

theorem cohomologyMapAlong_resTensorHom_cup (f : Rep.res φ A ⟶ A') (g : Rep.res φ B ⟶ B')
    (h : p + q = n) (x : cohomology A p) (y : cohomology B q) :
    cohomologyMapAlong φ hφ (resTensorHom φ f g) n (cup h x y) =
      cup h (cohomologyMapAlong φ hφ f p x) (cohomologyMapAlong φ hφ g q y) := by
  induction x using cohomology_induction_on with | h x => ?_
  induction y using cohomology_induction_on with | h y => ?_
  rw [cup_cohomologyπ, cohomologyMapAlong_cohomologyπ, cohomologyMapAlong_cohomologyπ,
    cohomologyMapAlong_cohomologyπ, cup_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cocyclesMapAlong, cocycleι_cupCocycles, cocycleι_cupCocycles,
    cochainOf_cupLocallyConstant, cochainOf_cupLocallyConstant,
    cochainOf_cocycleι_cocyclesMapAlong, cochainOf_cocycleι_cocyclesMapAlong]
  funext s
  rw [cupCochain_apply, cupCochain_apply, resTensorHom_tmul, partialProd_comp_monoidHom]
  exact congrArg (TensorProduct.tmul k _) (Rep.hom_comm_apply g _ _)

end MapAlong

section Restriction

variable {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] {p q n : ℕ}

theorem cohomologyMap_resTensorIso_cohomologyRes_cup (S : Subgroup G) (h : p + q = n)
    (x : cohomology A p) (y : cohomology B q) :
    cohomologyMap (resTensorIso S.subtype A B).hom n (cohomologyRes (A ⊗ B) S n (cup h x y)) =
      cup h (cohomologyRes A S p x) (cohomologyRes B S q y) := by
  induction x using cohomology_induction_on with | h x => ?_
  induction y using cohomology_induction_on with | h y => ?_
  rw [cohomologyRes_eq, cohomologyRes_eq, cohomologyRes_eq, cup_cohomologyπ,
    cohomologyMapAlong_cohomologyπ, cohomologyMap_cohomologyπ, cohomologyMapAlong_cohomologyπ,
    cohomologyMapAlong_cohomologyπ, cup_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cyclesMap, cochainOf_cocycleι_cocyclesMapAlong, cocycleι_cupCocycles,
    cocycleι_cupCocycles, cochainOf_cupLocallyConstant, cochainOf_cupLocallyConstant,
    cochainOf_cocycleι_cocyclesMapAlong, cochainOf_cocycleι_cocyclesMapAlong]
  funext s
  simp only [cupCochain_apply]
  rw [partialProd_comp_monoidHom]
  rfl

end Restriction

section Inflation

variable (A B : Rep.{u} k G) (N : Subgroup G) [N.Normal]

def invariantsTensorLinearMap :
    (A.quotientToInvariants N ⊗ B.quotientToInvariants N : Rep k (G ⧸ N)) →ₗ[k]
      (A ⊗ B).quotientToInvariants N :=
  (TensorProduct.map (Submodule.subtype _) (Submodule.subtype _)).codRestrict _ fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      intro s
      exact congrArg₂ (TensorProduct.tmul k) (a.2 s) (b.2 s)
    | add x y hx hy =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hx hy


def invariantsTensorHom :
    A.quotientToInvariants N ⊗ B.quotientToInvariants N ⟶ (A ⊗ B).quotientToInvariants N :=
  Rep.ofHom ⟨invariantsTensorLinearMap A B N, fun g => by
    induction g using QuotientGroup.induction_on with | H g => ?_
    apply TensorProduct.ext'
    intro a b
    exact Subtype.ext rfl⟩


variable {A B} [IsDiscreteRep A] [IsDiscreteRep B] {p q n : ℕ}

end Inflation

end GroundTheory.ProfCoh
end
end

