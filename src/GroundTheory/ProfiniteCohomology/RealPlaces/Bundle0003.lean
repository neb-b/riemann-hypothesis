module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.RealPlaces.HomologyMapProdFstProdLeftHomology
public import GroundTheory.ProfiniteCohomology.RealPlaces.Bundle0002
public import GroundTheory.ProfiniteCohomology.RealPlaces.ConeMap
public import GroundTheory.ProfiniteCohomology.MackeyFormula
public import GroundTheory.ProfiniteCohomology.MackeyFormula.CompactSupport
public import GroundTheory.ProfiniteCohomology.PoincarePairs.IsDiscreteRepResHomCoindRes
public import GroundTheory.ProfiniteCohomology.CoinducedModules.Acyclic

@[expose] public section

-- bundled from GroundTheory.ProfiniteCohomology.RealPlaces.CupSequence
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits MonoidalCategory GroundTheory.GroupCoh

universe u

section Compat

variable {k F : Type u} [CommRing k] [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
  [Fintype F]

theorem normHomotopy_compat_left {X₁ X₂ Y₁ Y₂ Z : Rep.{u} k F} [IsDiscreteRep Y₁] [IsDiscreteRep Y₂]
    [IsDiscreteRep Z] (μ₁ : X₁ ⊗ Y₁ ⟶ Z) (μ₂ : X₂ ⊗ Y₂ ⟶ Z) (f : X₁ ⟶ X₂) (g : Y₂ ⟶ Y₁)
    (hc : (f ⊗ₘ 𝟙 Y₂) ≫ μ₂ = (𝟙 X₁ ⊗ₘ g) ≫ μ₁) {s m : ℕ} (h : s = m + 1) (e : X₁)
    (y : (cochainsComplex Y₂).X s) :
    normHomotopy μ₂ h (f.hom e) y = normHomotopy μ₁ h e (((cochainsMap g).f s).hom y) := by
  apply cochainOf_injective
  funext σ
  rw [cochainOf_normHomotopy, cochainOf_normHomotopy]
  refine Finset.sum_congr rfl fun a _ => congrArg (Z.ρ a) ?_
  exact congrArg (fun φ : X₁ ⊗ Y₂ ⟶ Z => φ.hom ((e ⊗ₜ[k] cochainOf Y₂ y (consTuple h a⁻¹ σ) :
    (X₁ ⊗ Y₂ : Rep k F)))) hc

theorem normHomotopy_compat_right {X₂ X₃ Y₁ Y₂ Z : Rep.{u} k F} [IsDiscreteRep Y₁]
    [IsDiscreteRep Y₂] [IsDiscreteRep Z] (μ₂ : X₂ ⊗ Y₂ ⟶ Z) (μ₃ : X₃ ⊗ Y₁ ⟶ Z) (f : Y₁ ⟶ Y₂)
    (g : X₂ ⟶ X₃) (hc : (𝟙 X₂ ⊗ₘ f) ≫ μ₂ = (g ⊗ₘ 𝟙 Y₁) ≫ μ₃) {s m : ℕ} (h : s = m + 1) (e : X₂)
    (y : (cochainsComplex Y₁).X s) :
    normHomotopy μ₂ h e (((cochainsMap f).f s).hom y) = normHomotopy μ₃ h (g.hom e) y := by
  apply cochainOf_injective
  funext σ
  rw [cochainOf_normHomotopy, cochainOf_normHomotopy]
  refine Finset.sum_congr rfl fun a _ => congrArg (Z.ρ a) ?_
  exact congrArg (fun φ : X₂ ⊗ Y₁ ⟶ Z => φ.hom ((e ⊗ₜ[k] cochainOf Y₁ y (consTuple h a⁻¹ σ) :
    (X₂ ⊗ Y₁ : Rep k F)))) hc

end Compat

section TwoSequences

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  {SA : ShortComplex (Rep.{u} k G)} [IsDiscreteRep SA.X₁] [IsDiscreteRep SA.X₂]
  [IsDiscreteRep SA.X₃] {SAᵥ : ∀ v, ShortComplex (Rep.{u} k (H v))}
  [∀ v, IsDiscreteRep (SAᵥ v).X₁] [∀ v, IsDiscreteRep (SAᵥ v).X₂] [∀ v, IsDiscreteRep (SAᵥ v).X₃]
  (sA : ∀ v, SA.map (Rep.resFunctor (φ v).toMonoidHom) ⟶ SAᵥ v)
  {SAᵣ : ∀ w, ShortComplex (Rep.{u} k (F w))}
  [∀ w, IsDiscreteRep (SAᵣ w).X₁] [∀ w, IsDiscreteRep (SAᵣ w).X₂] [∀ w, IsDiscreteRep (SAᵣ w).X₃]
  (sAr : ∀ w, SA.map (Rep.resFunctor (ψ w).toMonoidHom) ⟶ SAᵣ w)
  {SB : ShortComplex (Rep.{u} k G)} [IsDiscreteRep SB.X₁] [IsDiscreteRep SB.X₂]
  [IsDiscreteRep SB.X₃] {C : Rep.{u} k G} [IsDiscreteRep C] {Cᵥ : ∀ v, Rep.{u} k (H v)}
  [∀ v, IsDiscreteRep (Cᵥ v)] {c : ∀ v, Rep.res (φ v).toMonoidHom C ⟶ Cᵥ v}
  {Cᵣ : ∀ w, Rep.{u} k (F w)} [∀ w, IsDiscreteRep (Cᵣ w)]
  {cr : ∀ w, Rep.res (ψ w).toMonoidHom C ⟶ Cᵣ w}
  (μ₁ : SA.X₁ ⊗ SB.X₃ ⟶ C) (μ₂ : SA.X₂ ⊗ SB.X₂ ⟶ C) (μ₃ : SA.X₃ ⊗ SB.X₁ ⟶ C)
  (μ₁ᵥ : ∀ v, (SAᵥ v).X₁ ⊗ Rep.res (φ v).toMonoidHom SB.X₃ ⟶ Cᵥ v)
  (μ₂ᵥ : ∀ v, (SAᵥ v).X₂ ⊗ Rep.res (φ v).toMonoidHom SB.X₂ ⟶ Cᵥ v)
  (μ₃ᵥ : ∀ v, (SAᵥ v).X₃ ⊗ Rep.res (φ v).toMonoidHom SB.X₁ ⟶ Cᵥ v)
  (μ₁ᵣ : ∀ w, (SAᵣ w).X₁ ⊗ Rep.res (ψ w).toMonoidHom SB.X₃ ⟶ Cᵣ w)
  (μ₂ᵣ : ∀ w, (SAᵣ w).X₂ ⊗ Rep.res (ψ w).toMonoidHom SB.X₂ ⟶ Cᵣ w)
  (μ₃ᵣ : ∀ w, (SAᵣ w).X₃ ⊗ Rep.res (ψ w).toMonoidHom SB.X₁ ⟶ Cᵣ w)
  (hμ₁ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ₁ ≫ c v =
    resTensorHom (φ v).toMonoidHom (sA v).τ₁ (𝟙 _) ≫ μ₁ᵥ v)
  (hμ₂ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ₂ ≫ c v =
    resTensorHom (φ v).toMonoidHom (sA v).τ₂ (𝟙 _) ≫ μ₂ᵥ v)
  (hμ₃ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ₃ ≫ c v =
    resTensorHom (φ v).toMonoidHom (sA v).τ₃ (𝟙 _) ≫ μ₃ᵥ v)
  (hμ₁ᵣ : ∀ w, (Rep.resFunctor (ψ w).toMonoidHom).map μ₁ ≫ cr w =
    resTensorHom (ψ w).toMonoidHom (sAr w).τ₁ (𝟙 _) ≫ μ₁ᵣ w)
  (hμ₂ᵣ : ∀ w, (Rep.resFunctor (ψ w).toMonoidHom).map μ₂ ≫ cr w =
    resTensorHom (ψ w).toMonoidHom (sAr w).τ₂ (𝟙 _) ≫ μ₂ᵣ w)
  (hμ₃ᵣ : ∀ w, (Rep.resFunctor (ψ w).toMonoidHom).map μ₃ ≫ cr w =
    resTensorHom (ψ w).toMonoidHom (sAr w).τ₃ (𝟙 _) ≫ μ₃ᵣ w)


include hμ₂ hμ₂ᵣ in
theorem tateCompactCup_tateCompactδ_add_tateCompactCup_δ
    (h₁₂ : (SA.f ⊗ₘ 𝟙 SB.X₂) ≫ μ₂ = (𝟙 SA.X₁ ⊗ₘ SB.g) ≫ μ₁)
    (h₂₃ : (𝟙 SA.X₂ ⊗ₘ SB.f) ≫ μ₂ = (SA.g ⊗ₘ 𝟙 SB.X₁) ≫ μ₃)
    (h₁₂ᵥ : ∀ v, ((SAᵥ v).f ⊗ₘ 𝟙 _) ≫ μ₂ᵥ v =
      (𝟙 _ ⊗ₘ (Rep.resFunctor (φ v).toMonoidHom).map SB.g) ≫ μ₁ᵥ v)
    (h₂₃ᵥ : ∀ v, (𝟙 _ ⊗ₘ (Rep.resFunctor (φ v).toMonoidHom).map SB.f) ≫ μ₂ᵥ v =
      ((SAᵥ v).g ⊗ₘ 𝟙 _) ≫ μ₃ᵥ v)
    (h₁₂ᵣ : ∀ w, ((SAᵣ w).f ⊗ₘ 𝟙 _) ≫ μ₂ᵣ w =
      (𝟙 _ ⊗ₘ (Rep.resFunctor (ψ w).toMonoidHom).map SB.g) ≫ μ₁ᵣ w)
    (h₂₃ᵣ : ∀ w, (𝟙 _ ⊗ₘ (Rep.resFunctor (ψ w).toMonoidHom).map SB.f) ≫ μ₂ᵣ w =
      ((SAᵣ w).g ⊗ₘ 𝟙 _) ≫ μ₃ᵣ w)
    (hSA : SA.ShortExact) (hSAᵥ : ∀ v, (SAᵥ v).ShortExact) (hSAᵣ : ∀ w, (SAᵣ w).ShortExact)
    (hSB : SB.ShortExact) {r s n : ℕ} (h₁ : r + 1 + s = n + 1) (h₃ : r + (s + 1) = n + 1)
    (x : tateCompactCohomology φ ψ SA.X₃ (fun v => (SAᵥ v).X₃) (fun v => (sA v).τ₃)
      (fun w => (SAᵣ w).X₃) (fun w => (sAr w).τ₃) r)
    (y : cohomology SB.X₃ s) :
    tateCompactCup φ ψ μ₁ μ₁ᵥ μ₁ᵣ hμ₁ hμ₁ᵣ h₁ ((tateCompactδ φ ψ sA sAr hSA hSAᵥ hSAᵣ r).hom x) y +
      (-1 : k) ^ r • tateCompactCup φ ψ μ₃ μ₃ᵥ μ₃ᵣ hμ₃ hμ₃ᵣ h₃ x ((δ hSB s (s + 1) rfl).hom y) = 0 := by
  refine LeibnizPairing.homology_δ_add_homology_δ
    (SM := mappingCoconeNat.mapShortComplex (tateResShortComplex φ ψ SA SAᵥ sA SAᵣ sAr))
    (SN := cochainsShortComplex SB) (tateCompactCupLeibniz φ ψ μ₂ μ₂ᵥ μ₂ᵣ hμ₂ hμ₂ᵣ)
    (tateCompactCupLeibniz φ ψ μ₁ μ₁ᵥ μ₁ᵣ hμ₁ hμ₁ᵣ) (tateCompactCupLeibniz φ ψ μ₃ μ₃ᵥ μ₃ᵣ hμ₃ hμ₃ᵣ)
    ?_ ?_ (tateCompactCochains_shortExact φ ψ sA sAr hSA hSAᵥ hSAᵣ)
    (cochainsShortComplex_shortExact hSB) h₁ h₃ x y
  · intro r s n h p y
    revert p
    intro (p : (tateGlobalComplex SA.X₁ fun w => (SAᵣ w).X₁).X r ×
      shiftNegOneX (tateLocalComplex (fun v => (SAᵥ v).X₁) fun w => (SAᵣ w).X₁) r)
    obtain ⟨⟨x0, e⟩, b⟩ := p
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · apply cochainOf_injective
      funext σ
      exact cupCochain_pairing_left μ₁ μ₂ h₁₂ h (cochainOf _ x0) (cochainOf _ y) σ
    · rcases r with _ | r
      · rcases s with _ | s
        · obtain rfl : n = 0 := by omega
          funext w
          exact congrArg (fun φ' => Rep.Hom.hom φ' ((e w ⊗ₜ[k] cochainOf SB.X₂ y (fun i => i.elim0) :
            ((SAᵣ w).X₁ ⊗ Rep.res (ψ w).toMonoidHom SB.X₂ : Rep k (F w))))) (h₁₂ᵣ w)
        · rfl
      · rfl
    · rcases r with _ | r
      · rcases s with _ | t
        · obtain rfl : n = 0 := by omega
          exact Subsingleton.elim (α := PUnit) _ _
        · obtain rfl : n = t + 1 := by omega
          change (0 : (tateLocalComplex Cᵥ Cᵣ).X t) +
              tateCupHomotopyL ψ μ₂ᵣ (Cᵥ := Cᵥ) (rfl : t + 1 = t + 1)
                ((piRepHom fun w => (SAᵣ w).f).hom e) y =
            (0 : (tateLocalComplex Cᵥ Cᵣ).X t) +
              tateCupHomotopyL ψ μ₁ᵣ (Cᵥ := Cᵥ) (rfl : t + 1 = t + 1) e
                (((cochainsMap SB.g).f (t + 1)).hom y)
          erw [tateCupHomotopyL_apply, tateCupHomotopyL_apply]
          refine congrArg _ (Prod.ext rfl (funext fun w => congrArg Neg.neg ?_))
          exact normHomotopy_compat_left (μ₁ᵣ w) (μ₂ᵣ w) (SAᵣ w).f _ (h₁₂ᵣ w) rfl (e w) _
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨r + s, by omega⟩
        change (tateLocalCup φ ψ μ₂ᵥ μ₂ᵣ).μ (show r + s = m by omega)
              ((tateLocalMap (fun v => (SAᵥ v).f) fun w => (SAᵣ w).f).f r |>.hom b)
              (((tateLocalResB φ ψ SB.X₂).f s).hom y) + 0 =
            (tateLocalCup φ ψ μ₁ᵥ μ₁ᵣ).μ (show r + s = m by omega) b
              (((tateLocalResB φ ψ SB.X₃).f s).hom (((cochainsMap SB.g).f s).hom y)) + 0
        rw [add_zero, add_zero]
        refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
        · apply cochainOf_injective
          funext σ
          exact cupCochain_pairing_left (S := SAᵥ v)
            (T := SB.map (Rep.resFunctor (φ v).toMonoidHom)) (μ₁ᵥ v) (μ₂ᵥ v) (h₁₂ᵥ v)
            (show r + s = m by omega) (cochainOf _ (b.1 v))
            (fun τ => cochainOf SB.X₂ y (⇑(φ v).toMonoidHom ∘ τ)) σ
        · apply cochainOf_injective
          funext σ
          exact cupCochain_pairing_left (S := SAᵣ w)
            (T := SB.map (Rep.resFunctor (ψ w).toMonoidHom)) (μ₁ᵣ w) (μ₂ᵣ w) (h₁₂ᵣ w)
            (show r + s = m by omega) (cochainOf _ (b.2 w))
            (fun τ => cochainOf SB.X₂ y (⇑(ψ w).toMonoidHom ∘ τ)) σ
  · intro r s n h p y
    revert p
    intro (p : (tateGlobalComplex SA.X₂ fun w => (SAᵣ w).X₂).X r ×
      shiftNegOneX (tateLocalComplex (fun v => (SAᵥ v).X₂) fun w => (SAᵣ w).X₂) r)
    obtain ⟨⟨x0, e⟩, b⟩ := p
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · apply cochainOf_injective
      funext σ
      exact cupCochain_pairing_right μ₂ μ₃ h₂₃ h (cochainOf _ x0) (cochainOf _ y) σ
    · rcases r with _ | r
      · rcases s with _ | s
        · obtain rfl : n = 0 := by omega
          funext w
          exact congrArg (fun φ' => Rep.Hom.hom φ' ((e w ⊗ₜ[k] cochainOf SB.X₁ y (fun i => i.elim0) :
            ((SAᵣ w).X₂ ⊗ Rep.res (ψ w).toMonoidHom SB.X₁ : Rep k (F w))))) (h₂₃ᵣ w)
        · rfl
      · rfl
    · rcases r with _ | r
      · rcases s with _ | t
        · obtain rfl : n = 0 := by omega
          exact Subsingleton.elim (α := PUnit) _ _
        · obtain rfl : n = t + 1 := by omega
          change (0 : (tateLocalComplex Cᵥ Cᵣ).X t) +
              tateCupHomotopyL ψ μ₂ᵣ (Cᵥ := Cᵥ) (rfl : t + 1 = t + 1) e
                (((cochainsMap SB.f).f (t + 1)).hom y) =
            (0 : (tateLocalComplex Cᵥ Cᵣ).X t) +
              tateCupHomotopyL ψ μ₃ᵣ (Cᵥ := Cᵥ) (rfl : t + 1 = t + 1)
                ((piRepHom fun w => (SAᵣ w).g).hom e) y
          erw [tateCupHomotopyL_apply, tateCupHomotopyL_apply]
          refine congrArg _ (Prod.ext rfl (funext fun w => congrArg Neg.neg ?_))
          exact normHomotopy_compat_right (μ₂ᵣ w) (μ₃ᵣ w)
            ((Rep.resFunctor (ψ w).toMonoidHom).map SB.f) (SAᵣ w).g (h₂₃ᵣ w) rfl (e w)
            (((localRes ψ SB.X₁ (fun w => Rep.res (ψ w).toMonoidHom SB.X₁) fun _ => 𝟙 _).f
              (t + 1)).hom y w)
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨r + s, by omega⟩
        change (tateLocalCup φ ψ μ₂ᵥ μ₂ᵣ).μ (show r + s = m by omega) b
              (((tateLocalResB φ ψ SB.X₂).f s).hom (((cochainsMap SB.f).f s).hom y)) + 0 =
            (tateLocalCup φ ψ μ₃ᵥ μ₃ᵣ).μ (show r + s = m by omega)
              ((tateLocalMap (fun v => (SAᵥ v).g) fun w => (SAᵣ w).g).f r |>.hom b)
              (((tateLocalResB φ ψ SB.X₁).f s).hom y) + 0
        rw [add_zero, add_zero]
        refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
        · apply cochainOf_injective
          funext σ
          exact cupCochain_pairing_right (S := SAᵥ v)
            (T := SB.map (Rep.resFunctor (φ v).toMonoidHom)) (μ₂ᵥ v) (μ₃ᵥ v) (h₂₃ᵥ v)
            (show r + s = m by omega) (cochainOf _ (b.1 v))
            (fun τ => cochainOf SB.X₁ y (⇑(φ v).toMonoidHom ∘ τ)) σ
        · apply cochainOf_injective
          funext σ
          exact cupCochain_pairing_right (S := SAᵣ w)
            (T := SB.map (Rep.resFunctor (ψ w).toMonoidHom)) (μ₂ᵣ w) (μ₃ᵣ w) (h₂₃ᵣ w)
            (show r + s = m by omega) (cochainOf _ (b.2 w))
            (fun τ => cochainOf SB.X₁ y (⇑(ψ w).toMonoidHom ∘ τ)) σ

end TwoSequences

end GroundTheory.ProfCoh
end

-- bundled from GroundTheory.ProfiniteCohomology.RealPlaces.Induced
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

section TrivialGroup

variable {k K : Type u} [CommRing k] [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [Subsingleton K]

noncomputable def subsingletonCoindIso (M : Rep.{u} k K) : M ≅ discreteCoind k K M where
  hom := Rep.ofHom ⟨{ toFun := fun m => LocallyConstant.const K m
                      map_add' := fun _ _ => rfl
                      map_smul' := fun _ _ => rfl }, fun g =>
    LinearMap.ext fun m => LocallyConstant.ext fun x => by
      change M.ρ g m = m
      rw [Subsingleton.elim g 1, map_one]
      rfl⟩
  inv := Rep.ofHom ⟨{ toFun := fun f => f 1
                      map_add' := fun _ _ => rfl
                      map_smul' := fun _ _ => rfl }, fun g =>
    LinearMap.ext fun f => by
      change f (1 * g) = M.ρ g (f 1)
      rw [Subsingleton.elim g 1, map_one, mul_one]
      rfl⟩
  hom_inv_id := Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))
  inv_hom_id := Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun f =>
    LocallyConstant.ext fun x => by
      change f 1 = f x
      rw [Subsingleton.elim x 1]))

theorem isZero_cohomology_succ_of_subsingleton (M : Rep.{u} k K) [IsDiscreteRep M] (n : ℕ) :
    IsZero (cohomology M (n + 1)) :=
  (isZero_cohomology_discreteCoind k K M n).of_iso
    { hom := cohomologyMap (subsingletonCoindIso M).hom (n + 1)
      inv := cohomologyMap (subsingletonCoindIso M).inv (n + 1)
      hom_inv_id := by rw [← cohomologyMap_comp, Iso.hom_inv_id, cohomologyMap_id]
      inv_hom_id := by rw [← cohomologyMap_comp, Iso.inv_hom_id, cohomologyMap_id] }

end TrivialGroup

section FreeAction

variable {k G H : Type u} [CommRing k] [Group G] [Group H] (U : Subgroup G) (ι : H →* G)

def InOutCoset (y : G) : Prop :=
  ∃ u : U, y = (u : G) * (DoubleCoset.mk U ι.range y).out

theorem doubleCosetMk_mul_left (u : U) (y : G) :
    DoubleCoset.mk U ι.range ((u : G) * y) = DoubleCoset.mk U ι.range y := by
  simpa using doubleCosetMk_mul_mul U ι y u 1

theorem inOutCoset_mul_left_iff (u : U) (y : G) : InOutCoset U ι ((u : G) * y) ↔ InOutCoset U ι y := by
  unfold InOutCoset
  rw [doubleCosetMk_mul_left]
  constructor
  · rintro ⟨u', hu'⟩
    refine ⟨u⁻¹ * u', ?_⟩
    calc y = (u : G)⁻¹ * ((u : G) * y) := by group
      _ = (u : G)⁻¹ * ((u' : G) * (DoubleCoset.mk U ι.range y).out) := by rw [hu']
      _ = ((u⁻¹ * u' : U) : G) * (DoubleCoset.mk U ι.range y).out := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
  · rintro ⟨u', hu'⟩
    refine ⟨u * u', ?_⟩
    nth_rewrite 1 [hu']
    rw [Subgroup.coe_mul, mul_assoc]

variable [Fintype H] (N : Rep.{u} k U)

theorem exists_norm_eq_res_coind (hfree : ∀ (x : G) (h : H), x * ι h * x⁻¹ ∈ U → h = 1)
    (f : Rep.res ι (Rep.coind U.subtype N))
    (hf : f ∈ (Rep.res ι (Rep.coind U.subtype N)).ρ.invariants) :
    ∃ m, (Rep.res ι (Rep.coind U.subtype N)).ρ.norm m = f := by
  classical
  have hmem : (fun y => if InOutCoset U ι y then f.1 y else 0) ∈
      Representation.coindV U.subtype N.ρ := by
    intro u y
    change (if InOutCoset U ι ((u : G) * y) then f.1 ((u : G) * y) else 0) =
      N.ρ u (if InOutCoset U ι y then f.1 y else 0)
    by_cases hy : InOutCoset U ι y
    · rw [if_pos ((inOutCoset_mul_left_iff U ι u y).2 hy), if_pos hy]
      exact f.2 u y
    · rw [if_neg (mt (inOutCoset_mul_left_iff U ι u y).1 hy), if_neg hy, map_zero]
  refine ⟨⟨_, hmem⟩, Subtype.ext (funext fun y => ?_)⟩
  have hnorm : ((Rep.res ι (Rep.coind U.subtype N)).ρ.norm ⟨_, hmem⟩).1 y =
      ∑ h : H, (if InOutCoset U ι (y * ι h) then f.1 (y * ι h) else 0) := by
    rw [Representation.norm, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    rfl
  rw [hnorm]
  obtain ⟨u₀, h₀, e₀⟩ := exists_eq_mul_out_mul U ι y
  set x := (DoubleCoset.mk U ι.range y).out with hx
  have hD : ∀ h : H, DoubleCoset.mk U ι.range (y * ι h) = DoubleCoset.mk U ι.range y := fun h => by
    have := doubleCosetMk_mul_mul U ι y 1 h
    simpa using this
  have hinv : ∀ h : H, f.1 (y * ι h) = f.1 y := fun h =>
    congrArg (fun g : Rep.res ι (Rep.coind U.subtype N) => g.1 y) (hf h)
  rw [Finset.sum_eq_single h₀⁻¹]
  · rw [if_pos, hinv]
    refine ⟨u₀, ?_⟩
    rw [hD, ← hx, e₀, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  · intro h _ hne
    rw [if_neg]
    rintro ⟨u, hu⟩
    rw [hD, ← hx] at hu
    apply hne
    have key : x * ι (h₀ * h) * x⁻¹ = ((u₀⁻¹ * u : U) : G) := by
      calc x * ι (h₀ * h) * x⁻¹ = (u₀ : G)⁻¹ * ((u₀ : G) * x * ι h₀ * ι h) * x⁻¹ := by
            rw [map_mul]; group
        _ = (u₀ : G)⁻¹ * (y * ι h) * x⁻¹ := by rw [← e₀]
        _ = (u₀ : G)⁻¹ * ((u : G) * x) * x⁻¹ := by rw [hu]
        _ = ((u₀⁻¹ * u : U) : G) := by rw [Subgroup.coe_mul, Subgroup.coe_inv]; group
    exact eq_inv_of_mul_eq_one_right (hfree x _ (key ▸ (u₀⁻¹ * u).2))
  · intro h
    exact absurd (Finset.mem_univ _) h

end FreeAction

section Naturality

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B]
  {Aᵥ Bᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsDiscreteRep (Aᵥ v)] [∀ v, IsDiscreteRep (Bᵥ v)]
  {a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v} {b : ∀ v, Rep.res (φ v).toMonoidHom B ⟶ Bᵥ v}
  {Aᵣ Bᵣ : ∀ w, Rep.{u} k (F w)} [∀ w, IsDiscreteRep (Aᵣ w)] [∀ w, IsDiscreteRep (Bᵣ w)]
  {ar : ∀ w, Rep.res (ψ w).toMonoidHom A ⟶ Aᵣ w} {br : ∀ w, Rep.res (ψ w).toMonoidHom B ⟶ Bᵣ w}
  (g : A ⟶ B) (gᵥ : ∀ v, Aᵥ v ⟶ Bᵥ v) (gᵣ : ∀ w, Aᵣ w ⟶ Bᵣ w)
  (hg : ∀ v, a v ≫ gᵥ v = (Rep.resFunctor (φ v).toMonoidHom).map g ≫ b v)
  (hgr : ∀ w, ar w ≫ gᵣ w = (Rep.resFunctor (ψ w).toMonoidHom).map g ≫ br w)

end Naturality

section LocalClasses

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  (A : Rep.{u} k G) [IsDiscreteRep A] (Aᵥ : ∀ v, Rep.{u} k (H v))
  [∀ v, IsDiscreteRep (Aᵥ v)] (a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v)
  (Aᵣ : ∀ w, Rep.{u} k (F w)) [∀ w, IsDiscreteRep (Aᵣ w)]
  (ar : ∀ w, Rep.res (ψ w).toMonoidHom A ⟶ Aᵣ w)

end LocalClasses

section Tate

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] [∀ v, CompactSpace (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)

def FreeOnCosets (U : Subgroup G) : Prop :=
  ∀ w (x : G) (h : F w), x * ψ w h * x⁻¹ ∈ U → h = 1

variable (U : OpenSubgroup G) (N : Rep.{u} k (U : Subgroup G)) [IsDiscreteRep N]

theorem isZero_cohomology_res_coind (hU : FreeOnCosets ψ (U : Subgroup G)) (w : κ) (n : ℕ) :
    IsZero (cohomology (Rep.res (ψ w).toMonoidHom (Rep.coind (U : Subgroup G).subtype N)) (n + 1)) := by
  have hb := mackeyCohomology_bijective U (ψ w) N (n + 1)
  have hsub : ∀ d : MackeyDoubleCoset (U : Subgroup G) (ψ w).toMonoidHom,
      Subsingleton (cohomology (mackeyRep (U : Subgroup G) (ψ w).toMonoidHom N d.out) (n + 1)) :=
    fun d => by
      have : Subsingleton (mackeySubgroup (U : Subgroup G) (ψ w).toMonoidHom d.out) :=
        ⟨fun a b => Subtype.ext ((hU w d.out a ((mem_mackeySubgroup _ _ _ _).1 a.2)).trans
          (hU w d.out b ((mem_mackeySubgroup _ _ _ _).1 b.2)).symm)⟩
      exact ModuleCat.isZero_iff_subsingleton.1 (isZero_cohomology_succ_of_subsingleton _ n)
  have : Subsingleton (cohomology (Rep.res (ψ w).toMonoidHom
      (Rep.coind (U : Subgroup G).subtype N)) (n + 1)) :=
    ⟨fun c c' => hb.1 (funext fun d => Subsingleton.elim _ _)⟩
  exact ModuleCat.isZero_of_subsingleton _


omit [IsTopologicalGroup G] [CompactSpace G] [∀ w, IsTopologicalGroup (F w)] [IsDiscreteRep N] in
theorem exists_norm_eq_res_coind' (hU : FreeOnCosets ψ (U : Subgroup G)) (w : κ)
    (f : Rep.res (ψ w).toMonoidHom (Rep.coind (U : Subgroup G).subtype N))
    (hf : f ∈ (Rep.res (ψ w).toMonoidHom (Rep.coind (U : Subgroup G).subtype N)).ρ.invariants) :
    ∃ m, (Rep.res (ψ w).toMonoidHom (Rep.coind (U : Subgroup G).subtype N)).ρ.norm m = f :=
  exists_norm_eq_res_coind (U : Subgroup G) (ψ w).toMonoidHom N (hU w) f hf

noncomputable def tateCoindIso (hU : FreeOnCosets ψ (U : Subgroup G)) (n : ℕ) :
    tateCompactCohomologyRes φ ψ (Rep.coind (U : Subgroup G).subtype N) (n + 1) ≅
      compactCohomology (mackeyFamily U φ) N (mackeyCoeff U φ N) (fun _ => 𝟙 _) (n + 1) :=
  tateForgetIso φ ψ _ _ _ _ _ (fun w n => isZero_cohomology_res_coind ψ U N hU w n)
      (fun w f hf => exists_norm_eq_res_coind' ψ U N hU w f hf) n ≪≫
    mackeyCompactCohomologyIso U φ N (n + 1)

theorem tateCoindIso_hom (hU : FreeOnCosets ψ (U : Subgroup G)) (n : ℕ) :
    (tateCoindIso φ ψ U N hU n).hom =
      tateForget φ ψ _ _ _ _ _ (n + 1) ≫ (mackeyCompactCohomologyIso U φ N (n + 1)).hom :=
  rfl

noncomputable def tateCompactCores (hU : FreeOnCosets ψ (U : Subgroup G)) (A : Rep.{u} k G)
    [IsDiscreteRep A] (n : ℕ) :
    compactCohomologyRes (mackeyFamily U φ) (Rep.res (U : Subgroup G).subtype A) (n + 1) ⟶
      tateCompactCohomologyRes φ ψ A (n + 1) :=
  (tateCoindIso φ ψ U (Rep.res (U : Subgroup G).subtype A) hU n).inv ≫
    tateCompactCohomologyMap φ ψ
      (Aᵥ := fun v => Rep.res (φ v).toMonoidHom
        (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)))
      (Bᵥ := fun v => Rep.res (φ v).toMonoidHom A)
      (Aᵣ := fun w => Rep.res (ψ w).toMonoidHom
        (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)))
      (Bᵣ := fun w => Rep.res (ψ w).toMonoidHom A)
      (coindTrace (U : Subgroup G) A)
      (fun v => (Rep.resFunctor (φ v).toMonoidHom).map (coindTrace (U : Subgroup G) A))
      (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map (coindTrace (U : Subgroup G) A))
      (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)
      (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm) (n + 1)

end Tate

end GroundTheory.ProfCoh
end

