module

public import Mathlib
public import GroundTheory.AutomorphicForms.TensorProductTheorem.Bundle0003
public import GroundTheory.AutomorphicForms.TensorProductTheorem.Bundle0001
public import GroundTheory.AutomorphicForms.TensorProductTheorem.Irreducible
public import GroundTheory.AutomorphicForms.TensorProductTheorem.LocalComponent

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.TensorProductTheorem.KFinite
section
noncomputable section

namespace GroundTheory.Automorphic

namespace CompactRep

open Module Set

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K] {X : Type*} [AddCommGroup X] [Module ℂ X]

structure IsKFinite (σ : Representation ℂ K X) : Prop where
  locallyFinite : ∀ v, FiniteDimensional ℂ (Submodule.span ℂ (range fun k => σ k v))
  continuous : Representation.HasContinuousCoeff σ

variable {σ : Representation ℂ K X}

theorem hasContinuousCoeff_subrep (hσ : Representation.HasContinuousCoeff σ)
    (P : Subrepresentation σ) : Representation.HasContinuousCoeff P.toRepresentation := by
  intro φ w
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend φ
  have : ∀ k, φ (P.toRepresentation k w) = ψ (σ k w) := fun k => by
    rw [← hψ]
    rfl
  simp only [this]
  exact hσ ψ w

theorem exists_subrep_compl (h : IsKFinite σ) (v : X) {Y : Subrepresentation σ}
    (hY : Y ≤ RestrictedTensor.orbitSpan σ v) :
    ∃ C : Subrepresentation σ, C ≤ RestrictedTensor.orbitSpan σ v ∧ Y ⊓ C = ⊥ ∧
      Y ⊔ C = RestrictedTensor.orbitSpan σ v := by
  set F := RestrictedTensor.orbitSpan σ v
  have hFd : FiniteDimensional ℂ F.toSubmodule := h.locallyFinite v
  have hFc := hasContinuousCoeff_subrep h.continuous F
  set U : Submodule ℂ F.toSubmodule := Y.toSubmodule.comap F.toSubmodule.subtype
  obtain ⟨C', hC', hC's⟩ := exists_isCompl_stable hFc U fun k u hu =>
    Y.apply_mem_toSubmodule k hu
  refine ⟨⟨C'.map F.toSubmodule.subtype, ?_⟩, ?_, ?_, ?_⟩
  · rintro k _ ⟨c, hc, rfl⟩
    exact ⟨_, hC's k c hc, rfl⟩
  · rintro _ ⟨c, -, rfl⟩
    exact c.2
  · apply Subrepresentation.toSubmodule_injective
    rw [Subrepresentation.toSubmodule_inf]
    change _ = (⊥ : Submodule ℂ X)
    rw [eq_bot_iff]
    rintro _ ⟨hxY, ⟨c, hc, rfl⟩⟩
    have hcU : c ∈ U := hxY
    have : c ∈ U ⊓ C' := ⟨hcU, hc⟩
    rw [disjoint_iff.1 hC'.1, Submodule.mem_bot] at this
    rw [this]
    exact Submodule.zero_mem _
  · apply Subrepresentation.toSubmodule_injective
    rw [Subrepresentation.toSubmodule_sup]
    refine le_antisymm (sup_le hY ?_) fun x hx => ?_
    · rintro _ ⟨c, -, rfl⟩
      exact c.2
    · have hxtop : (⟨x, hx⟩ : F.toSubmodule) ∈ U ⊔ C' := by
        rw [codisjoint_iff.1 hC'.2]; trivial
      obtain ⟨u, hu, c, hc, huc⟩ := Submodule.mem_sup.1 hxtop
      rw [Submodule.mem_sup]
      refine ⟨u, hu, c, ⟨c, hc, rfl⟩, ?_⟩
      have := congrArg Subtype.val huc
      simpa using this


theorem isSemisimpleModule_asModule (h : IsKFinite σ) :
    IsSemisimpleModule (MonoidAlgebra ℂ K) σ.asModule := by
  set e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := σ)
  rw [isSemisimpleModule_iff]
  refine complementedLattice_of_complementedLattice_Iic (s := univ)
    (f := fun v : X => e (RestrictedTensor.orbitSpan σ v)) (fun v _ => ?_) ?_
  · refine ⟨fun ⟨N, hN⟩ => ?_⟩
    have hY : e.symm N ≤ RestrictedTensor.orbitSpan σ v := by
      have := e.symm.monotone hN
      simpa using this
    obtain ⟨C, hCle, hinf, hsup⟩ := exists_subrep_compl h v hY
    refine ⟨⟨e C, e.monotone hCle⟩, ⟨disjoint_iff.2 ?_, codisjoint_iff.2 ?_⟩⟩
    · apply Subtype.ext
      show N ⊓ e C = ⊥
      have := congrArg e hinf
      rwa [e.map_inf, e.apply_symm_apply, e.map_bot] at this
    · apply Subtype.ext
      show N ⊔ e C = e (RestrictedTensor.orbitSpan σ v)
      have := congrArg e hsup
      rwa [e.map_sup, e.apply_symm_apply] at this
  · refine eq_top_iff.2 fun x _ => ?_
    refine Submodule.mem_iSup_of_mem x (Submodule.mem_iSup_of_mem (mem_univ x) ?_)
    exact RestrictedTensor.mem_orbitSpan_self σ x

section Isotypic

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [IsSemisimpleModule R M]

theorem isFullyInvariant_sSup {s : Set (Submodule R M)} (h : ∀ m ∈ s, m.IsFullyInvariant) :
    (sSup s).IsFullyInvariant := fun f =>
  sSup_le fun m hm => (h m hm f).trans (Submodule.comap_mono (le_sSup hm))

theorem isCompl_isotypicComponent {c : Submodule R M} (hc : c ∈ isotypicComponents R M) :
    IsCompl c (sSup (isotypicComponents R M \ {c})) := by
  refine ⟨sSupIndep_isotypicComponents R M hc, codisjoint_iff.2 ?_⟩
  rw [eq_top_iff, ← sSup_isotypicComponents (R := R) (M := M)]
  refine sSup_le fun m hm => ?_
  by_cases hmc : m = c
  · exact hmc ▸ le_sup_left
  · exact le_sup_of_le_right (le_sSup ⟨hm, hmc⟩)

def isoProj {c : Submodule R M} (hc : c ∈ isotypicComponents R M) : Module.End R M :=
  c.subtype ∘ₗ Submodule.projectionOnto c _ (isCompl_isotypicComponent hc)

theorem isoProj_apply_of_mem {c : Submodule R M} (hc : c ∈ isotypicComponents R M) {x : M}
    (hx : x ∈ c) : isoProj hc x = x := by
  simp [isoProj, Submodule.projectionOnto_apply_of_mem_left _ hx]

theorem isoProj_mem_isotypicComponent {c : Submodule R M} (hc : c ∈ isotypicComponents R M)
    (x : M) : isoProj hc x ∈ c :=
  Subtype.prop _

theorem isoProj_apply_of_mem_compl {c : Submodule R M} (hc : c ∈ isotypicComponents R M) {x : M}
    (hx : x ∈ sSup (isotypicComponents R M \ {c})) : isoProj hc x = 0 := by
  simp [isoProj, (Submodule.projectionOnto_apply_eq_zero_iff _).2 hx]

theorem isoProj_comm {c : Submodule R M} (hc : c ∈ isotypicComponents R M) (f : Module.End R M)
    (x : M) : isoProj hc (f x) = f (isoProj hc x) := by
  have hcompl := isCompl_isotypicComponent hc
  have hfc : c.IsFullyInvariant := Submodule.IsFullyInvariant.of_mem_isotypicComponents hc
  have hfr : (sSup (isotypicComponents R M \ {c})).IsFullyInvariant :=
    isFullyInvariant_sSup fun m hm => Submodule.IsFullyInvariant.of_mem_isotypicComponents hm.1
  have hx : x ∈ c ⊔ sSup (isotypicComponents R M \ {c}) := by
    rw [codisjoint_iff.1 hcompl.2]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add f, map_add (isoProj hc), map_add (isoProj hc), isoProj_apply_of_mem hc (hfc f ha),
    isoProj_apply_of_mem_compl hc (hfr f hb), isoProj_apply_of_mem hc ha,
    isoProj_apply_of_mem_compl hc hb, add_zero, add_zero]

theorem isoProj_mem {c : Submodule R M} (hc : c ∈ isotypicComponents R M) (Y : Submodule R M)
    {y : M} (hy : y ∈ Y) : isoProj hc y ∈ Y := by
  obtain ⟨Y', hY'⟩ := exists_isCompl Y
  set f : Module.End R M := Y.subtype ∘ₗ Submodule.projectionOnto Y Y' hY'
  have hfy : f y = y := by simp [f, Submodule.projectionOnto_apply_of_mem_left _ hy]
  rw [← hfy, isoProj_comm hc f]
  exact Subtype.prop _

end Isotypic

end CompactRep

end GroundTheory.Automorphic
end
end

-- bundled from GroundTheory.AutomorphicForms.TensorProductTheorem.Places
section
noncomputable section

namespace GroundTheory.Automorphic

namespace RestrictedTensor

open Filter Function Module Set

open scoped RestrictedProduct

variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] {K : ∀ v, Subgroup (G v)}

section Group

variable [DecidableEq ι]


variable (K) in
def singleHom (K : ∀ w, Subgroup (G w)) (v : ι) : G v →* Πʳ w, [G w, K w] where
  toFun := RestrictedProduct.mulSingle K v
  map_one' := RestrictedProduct.mulSingle_one K v
  map_mul' x y := RestrictedProduct.mulSingle_mul K v x y

theorem singleHom_apply_self (v : ι) (x : G v) : singleHom K v x v = x :=
  RestrictedProduct.mulSingle_eq_same K v x

theorem singleHom_apply_of_ne {v w : ι} (x : G v) (h : w ≠ v) : singleHom K v x w = 1 :=
  RestrictedProduct.mulSingle_eq_of_ne K x h

theorem commute_of_forall {a b : Πʳ w, [G w, K w]} (h : ∀ w, a w = 1 ∨ b w = 1) :
    a * b = b * a := by
  ext w
  simp only [RestrictedProduct.mul_apply]
  rcases h w with h | h <;> simp [h]

def eraseAt (v : ι) (g : Πʳ w, [G w, K w]) : Πʳ w, [G w, K w] :=
  (singleHom K v (g v))⁻¹ * g

theorem eraseAt_apply_self (v : ι) (g : Πʳ w, [G w, K w]) : eraseAt v g v = 1 := by
  simp [eraseAt, RestrictedProduct.mul_apply, RestrictedProduct.inv_apply, singleHom_apply_self]

theorem eraseAt_apply_of_ne {v w : ι} (g : Πʳ w, [G w, K w]) (h : w ≠ v) :
    eraseAt v g w = g w := by
  simp [eraseAt, RestrictedProduct.mul_apply, RestrictedProduct.inv_apply,
    singleHom_apply_of_ne _ h]

theorem single_mul_eraseAt (v : ι) (g : Πʳ w, [G w, K w]) :
    singleHom K v (g v) * eraseAt v g = g := by
  simp [eraseAt]

theorem eraseAt_mem_boxSubgroup {K' : ∀ v, Subgroup (G v)} (v : ι) {g : Πʳ w, [G w, K w]}
    (hg : g ∈ boxSubgroup K K') : eraseAt v g ∈ boxSubgroup K K' := by
  intro w
  by_cases hw : w = v
  · subst hw
    rw [eraseAt_apply_self]
    exact (K' w).one_mem
  · rw [eraseAt_apply_of_ne _ hw]
    exact hg w

theorem singleHom_mem_boxSubgroup {K' : ∀ v, Subgroup (G v)} {v : ι} {x : G v}
    (hx : x ∈ K' v) : singleHom K v x ∈ boxSubgroup K K' := by
  intro w
  by_cases hw : w = v
  · subst hw
    rw [singleHom_apply_self]
    exact hx
  · rw [singleHom_apply_of_ne _ hw]
    exact (K' w).one_mem

theorem commute_singleHom {v : ι} (x : G v) {b : Πʳ w, [G w, K w]} (hb : b v = 1) :
    singleHom K v x * b = b * singleHom K v x :=
  commute_of_forall fun w => by
    by_cases hw : w = v
    · subst hw; exact Or.inr hb
    · exact Or.inl (singleHom_apply_of_ne _ hw)

end Group

variable [∀ v, TopologicalSpace (G v)] [∀ v, IsTopologicalGroup (G v)]
  [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)] [∀ v, TotallyDisconnectedSpace (G v)]
  [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))] [hKc : ∀ v, CompactSpace (K v)]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (Πʳ v, [G v, K v]) V}
  (hρ : IsSmooth ρ) {K' : ∀ v, Subgroup (G v)} (hK'c : ∀ v, IsCompact (K' v : Set (G v)))
  (hK'o : ∀ v, IsOpen (K' v : Set (G v))) (hK'e : ∀ᶠ v in cofinite, K' v = K v)

section Window

variable [DecidableEq ι]


omit hK'c hK'o hK'e in
theorem apply_eq_apply_single (v : ι) {u : V}
    (hu : ∀ h ∈ boxSubgroup K K', h v = 1 → ρ h u = u) {h : Πʳ w, [G w, K w]}
    (hh : h ∈ boxSubgroup K K') : ρ h u = ρ (singleHom K v (h v)) u := by
  conv_lhs => rw [← single_mul_eraseAt v h]
  rw [map_mul, Module.End.mul_apply, hu _ (eraseAt_mem_boxSubgroup v hh) (eraseAt_apply_self v h)]


omit hK'c hK'o hK'e in
theorem apply_single_fixed (v : ι) (x : G v) {m : V} (hm : m ∈ fixedVectors ρ (boxSubgroup K K'))
    {h : Πʳ w, [G w, K w]} (hh : h ∈ boxSubgroup K K') (hv : h v = 1) :
    ρ h (ρ (singleHom K v x) m) = ρ (singleHom K v x) m := by
  rw [← Module.End.mul_apply, ← map_mul, ← commute_singleHom x hv, map_mul, Module.End.mul_apply,
    hm h hh]


include hK'c hK'o hK'e in
theorem heckeOp_single_mul (v : ι) (x : G v) {b : Πʳ w, [G w, K w]} (hb : b v = 1) :
    heckeOp hρ (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e)
        (singleHom K v x * b) =
      heckeOp hρ (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e)
          (singleHom K v x) *
        heckeOp hρ (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e) b := by
  ext m
  rw [Module.End.mul_apply, heckeOp_mul_apply]
  intro h hh
  refine ⟨eraseAt v h, eraseAt_mem_boxSubgroup v hh, ?_, ?_⟩
  · exact (commute_singleHom x (eraseAt_apply_self v h)).symm
  · have h1 : (eraseAt v h)⁻¹ * h = singleHom K v (h v) := by
      have hc := commute_singleHom (K := K) (h v) (eraseAt_apply_self v h)
      calc (eraseAt v h)⁻¹ * h = (eraseAt v h)⁻¹ * (singleHom K v (h v) * eraseAt v h) := by
            rw [single_mul_eraseAt]
        _ = singleHom K v (h v) := by rw [hc, inv_mul_cancel_left]
    rw [h1]
    exact commute_singleHom (h v) hb

def placeOps (v : ι) : Set (End ℂ (fixedVectors ρ (boxSubgroup K K'))) :=
  range fun x : G v => heckeOp hρ (isCompact_boxSubgroup_of_eq hK'c hK'e)
    (isOpen_boxSubgroup hK'o hK'e) (singleHom K v x)

theorem commute_placeOps {v w : ι} (hvw : v ≠ w) :
    ∀ a ∈ placeOps hρ hK'c hK'o hK'e v, ∀ b ∈ placeOps hρ hK'c hK'o hK'e w, Commute a b := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  have h1 := heckeOp_single_mul hρ hK'c hK'o hK'e v x (b := singleHom K w y)
    (singleHom_apply_of_ne y hvw)
  have h2 := heckeOp_single_mul hρ hK'c hK'o hK'e w y (b := singleHom K v x)
    (singleHom_apply_of_ne x hvw.symm)
  show _ * _ = _ * _
  rw [← h1, ← h2, commute_singleHom x (singleHom_apply_of_ne y hvw)]

theorem heckeOp_mem_adjoin (s : Finset ι) {g : Πʳ w, [G w, K w]} (hg : ∀ v ∉ s, g v ∈ K' v) :
    heckeOp hρ (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e) g ∈
      Algebra.adjoin ℂ (⋃ v ∈ s, placeOps hρ hK'c hK'o hK'e v) := by
  induction s using Finset.induction_on generalizing g with
  | empty =>
    rw [heckeOp_of_mem _ _ _ (show g ∈ boxSubgroup K K' from fun v => hg v (Finset.notMem_empty v))]
    exact Subalgebra.one_mem _
  | insert a s has ih =>
    have herase : ∀ v ∉ s, eraseAt a g v ∈ K' v := by
      intro v hv
      by_cases hva : v = a
      · subst hva; rw [eraseAt_apply_self]; exact (K' v).one_mem
      · rw [eraseAt_apply_of_ne _ hva]
        exact hg v (by simp [hva, hv])
    have hmono : Algebra.adjoin ℂ (⋃ v ∈ s, placeOps hρ hK'c hK'o hK'e v) ≤
        Algebra.adjoin ℂ (⋃ v ∈ insert a s, placeOps hρ hK'c hK'o hK'e v) :=
      Algebra.adjoin_mono (biUnion_subset_biUnion_left (by simp))
    rw [← single_mul_eraseAt a g, heckeOp_single_mul hρ hK'c hK'o hK'e a (g a)
      (eraseAt_apply_self a g)]
    refine Subalgebra.mul_mem _ (Algebra.subset_adjoin ?_) (hmono (ih herase))
    exact mem_biUnion (Finset.mem_insert_self a s) ⟨g a, rfl⟩

theorem fixedProj_single_eq (v : ι) (hρv : IsSmooth (ρ.comp (singleHom K v))) {u : V}
    (hu : ∀ h ∈ boxSubgroup K K', h v = 1 → ρ h u = u) :
    (fixedProj (ρ.comp (singleHom K v)) hρv (hK'c v) (hK'o v) u : V) =
      fixedProj ρ hρ (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e) u :=
  fixedProj_comp_eq (singleHom K v) hρ hρv _ _ (hK'c v) (hK'o v)
    (fun k hk => singleHom_mem_boxSubgroup hk)
    (fun h hh => ⟨h v, hh v, apply_eq_apply_single v hu hh⟩)

end Window

end RestrictedTensor

end GroundTheory.Automorphic
end
end

