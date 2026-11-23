module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndKerBaseChangeOfForallResidueField
section
open TensorProduct Function

namespace GlobalTheory

section LinearAlgebra

variable {R : Type*} [CommRing R] {A B C : Type*}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]

theorem exact_lTensor_iff_of_faithfullyFlat (k L : Type*) [CommRing k] [CommRing L] [Algebra R k]
    [Algebra R L] [Algebra k L] [IsScalarTower R k L] [Module.FaithfullyFlat k L]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) :
    Exact (f.lTensor L) (g.lTensor L) ↔ Exact (f.lTensor k) (g.lTensor k) := by
  have h1 := Module.FaithfullyFlat.lTensor_exact_iff_exact k L (f.baseChange k) (g.baseChange k)
  have h2 : Exact (AlgebraTensorModule.lTensor k L f) (AlgebraTensorModule.lTensor k L g) ↔
      Exact ((f.baseChange k).lTensor L) ((g.baseChange k).lTensor L) :=
    Function.Exact.iff_of_ladder_linearEquiv
      (e₁ := AlgebraTensorModule.cancelBaseChange R k k L A)
      (e₂ := AlgebraTensorModule.cancelBaseChange R k k L B)
      (e₃ := AlgebraTensorModule.cancelBaseChange R k k L C)
      (by ext; simp) (by ext; simp)
  exact h2.trans h1

theorem exact_lTensor_iff_residueField (p : Ideal R) [p.IsPrime] (L : Type*) [Field L]
    [Algebra R L] (hL : RingHom.ker (algebraMap R L) = p) (f : A →ₗ[R] B) (g : B →ₗ[R] C) :
    Exact (f.lTensor L) (g.lTensor L) ↔
      Exact (f.lTensor p.ResidueField) (g.lTensor p.ResidueField) := by
  let φ : p.ResidueField →ₐ[R] L := Ideal.ResidueField.liftₐ p (Algebra.ofId R L) hL.ge (by
    intro x hx
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    intro h0
    exact hx (hL ▸ h0))
  letI : Algebra p.ResidueField L := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R p.ResidueField L :=
    IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  exact exact_lTensor_iff_of_faithfullyFlat p.ResidueField L f g

theorem split_injective_of_forall_lTensor_residueField_injective [Module.Finite R B]
    [Module.Finite R C] [Module.Projective R C] (l : B →ₗ[R] C)
    (h : ∀ (m : Ideal R) [m.IsMaximal], Injective (l.lTensor m.ResidueField)) :
    ∃ r : C →ₗ[R] B, r ∘ₗ l = LinearMap.id := by
  have hloc : ∀ (m : Ideal R) [m.IsMaximal], Injective ((l.baseChange (Localization.AtPrime m)).lTensor
      (IsLocalRing.ResidueField (Localization.AtPrime m))) := by
    intro m _
    have e : (AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime m)
          (Localization.AtPrime m) m.ResidueField C) ∘
          ((l.baseChange (Localization.AtPrime m)).lTensor m.ResidueField) =
        (l.lTensor m.ResidueField) ∘ (AlgebraTensorModule.cancelBaseChange R
          (Localization.AtPrime m) (Localization.AtPrime m) m.ResidueField B) := by
      funext x
      exact (LinearMap.congr_fun (AlgebraTensorModule.lTensor_comp_cancelBaseChange R
        (Localization.AtPrime m) (Localization.AtPrime m) (M := m.ResidueField) l) x).symm
    exact Injective.of_comp (e ▸ (h m).comp (LinearEquiv.injective _))
  have hfree : ∀ (m : Ideal R) [m.IsMaximal],
      Module.Free (Localization.AtPrime m) (Localization.AtPrime m ⊗[R] C) := fun m _ =>
    Module.free_of_flat_of_isLocalRing
  have hinj : Injective l := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
    refine Module.subsingleton_of_localization_maximal (R := R)
      (fun m _ => Localization.AtPrime m ⊗[R] LinearMap.ker l)
      (fun m _ => TensorProduct.mk R (Localization.AtPrime m) _ 1) (fun m _ => ?_)
    obtain ⟨r, hr⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective _).2 (hloc m)
    have h1 : Injective (l.lTensor (Localization.AtPrime m)) :=
      HasLeftInverse.injective ⟨r, LinearMap.congr_fun hr⟩
    have h2 : Injective ((LinearMap.ker l).subtype.lTensor (Localization.AtPrime m)) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    refine (subsingleton_iff_forall_eq 0).2 fun y => h2 (h1 ?_)
    rw [map_zero, map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      l.exact_subtype_ker_map.linearMap_comp_eq_zero, LinearMap.lTensor_zero,
      LinearMap.zero_apply]
  have : Module.FinitePresentation R C := Module.finitePresentation_of_projective R C
  have : Module.FinitePresentation R (C ⧸ LinearMap.range l) :=
    Module.finitePresentation_of_surjective (LinearMap.range l).mkQ (Submodule.mkQ_surjective _)
      (by rw [Submodule.ker_mkQ, LinearMap.range_eq_map]; exact Module.Finite.fg_top.map l)
  have : Module.Projective R (C ⧸ LinearMap.range l) := by
    refine Module.projective_of_localization_maximal' (fun m _ => Localization.AtPrime m)
      (fun m _ => Localization.AtPrime m ⊗[R] (C ⧸ LinearMap.range l))
      (fun m _ => TensorProduct.mk R (Localization.AtPrime m) _ 1) (fun m _ => ?_)
    have := Module.free_of_lTensor_residueField_injective
      (l.baseChange (Localization.AtPrime m))
      ((LinearMap.range l).mkQ.baseChange (Localization.AtPrime m))
      (LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _))
      (lTensor_exact _ l.exact_map_mkQ_range (Submodule.mkQ_surjective _)) (hloc m)
    infer_instance
  have := (Exact.split_tfae l.exact_map_mkQ_range hinj (Submodule.mkQ_surjective _)).out 1 2
  rw [← this]
  exact Module.projective_lifting_property _ _ (Submodule.mkQ_surjective _)

theorem lTensor_liftQ_injective_of_exact (N : Type*) [AddCommGroup N] [Module R N]
    {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hfg : LinearMap.range f ≤ LinearMap.ker g)
    (h : Exact (f.lTensor N) (g.lTensor N)) :
    Injective (((LinearMap.range f).liftQ g hfg).lTensor N) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective N (Submodule.mkQ_surjective _) x
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, Submodule.liftQ_mkQ] at hx
  obtain ⟨z, rfl⟩ := (h y).1 hx
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
    f.exact_map_mkQ_range.linearMap_comp_eq_zero, LinearMap.lTensor_zero, LinearMap.zero_apply]

theorem exists_homotopy_of_forall_exact_residueField [Module.Finite R B] [Module.Projective R B]
    [Module.Finite R C] [Module.Projective R C] {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hfg : g ∘ₗ f = 0)
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      Exact (f.lTensor m.ResidueField) (g.lTensor m.ResidueField)) :
    ∃ (s : B →ₗ[R] A) (t : C →ₗ[R] B), f ∘ₗ s + t ∘ₗ g = LinearMap.id := by
  have hle : LinearMap.range f ≤ LinearMap.ker g := LinearMap.range_le_ker_iff.2 hfg
  obtain ⟨r, hr⟩ := split_injective_of_forall_lTensor_residueField_injective
    ((LinearMap.range f).liftQ g hle) fun m _ => lTensor_liftQ_injective_of_exact _ hle (h m)
  obtain ⟨t, ht⟩ := Module.projective_lifting_property (LinearMap.range f).mkQ r
    (Submodule.mkQ_surjective _)
  have hmem : ∀ b, (LinearMap.id - t ∘ₗ g : B →ₗ[R] B) b ∈ LinearMap.range f := by
    intro b
    have h1 := LinearMap.congr_fun ht (g b)
    have h2 := LinearMap.congr_fun hr (Submodule.Quotient.mk b)
    simp only [LinearMap.comp_apply, Submodule.liftQ_apply, Submodule.mkQ_apply,
      LinearMap.id_apply] at h1 h2
    rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, ← Submodule.Quotient.eq,
      h1, h2]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f.rangeRestrict
    (LinearMap.codRestrict _ _ hmem) f.surjective_rangeRestrict
  refine ⟨s, t, LinearMap.ext fun b => ?_⟩
  have := congrArg Subtype.val (LinearMap.congr_fun hs b)
  simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply, LinearMap.sub_apply,
    LinearMap.id_apply, LinearMap.rangeRestrict] at this
  simp [this]

theorem forall_exact_residueField_of_isLocalRing [IsLocalRing R] {f : A →ₗ[R] B} {g : B →ₗ[R] C}
    (h : Exact (f.lTensor (IsLocalRing.ResidueField R)) (g.lTensor (IsLocalRing.ResidueField R)))
    (m : Ideal R) [m.IsMaximal] :
    Exact (f.lTensor m.ResidueField) (g.lTensor m.ResidueField) :=
  (exact_lTensor_iff_residueField m (IsLocalRing.ResidueField R)
    (IsLocalRing.ker_residue.trans (IsLocalRing.eq_maximalIdeal ‹_›).symm) f g).1 h

theorem exact_of_homotopy {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hfg : g ∘ₗ f = 0)
    {s : B →ₗ[R] A} {t : C →ₗ[R] B} (h : f ∘ₗ s + t ∘ₗ g = LinearMap.id) : Exact f g := by
  intro x
  constructor
  · intro hx
    refine ⟨s x, ?_⟩
    simpa [hx] using LinearMap.congr_fun h x
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun hfg y

end LinearAlgebra

section Comparison

open CategoryTheory Category Limits

set_option backward.isDefEq.respectTransparency false

variable {C D : Type*} [Category* C] [Category* D]

section ShortComplex

variable [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms]

variable [PreservesColimitsOfShape WalkingParallelPair F]

end ShortComplex

section Complex

variable [HasZeroMorphisms C] [HasZeroMorphisms D] [CategoryWithHomology C]
  [CategoryWithHomology D] (F : C ⥤ D) [F.PreservesZeroMorphisms] {ι : Type*} {c : ComplexShape ι}

variable [PreservesColimitsOfShape WalkingParallelPair F]

end Complex

end Comparison

section Homotopy

open CategoryTheory Category Limits

set_option backward.isDefEq.respectTransparency false

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [CategoryWithHomology C] [CategoryWithHomology D] {ι : Type*} {c : ComplexShape ι}

end Homotopy

section Modules

open CategoryTheory Category Limits

universe u w

variable {R : Type u} [CommRing R] {ι : Type*} {c : ComplexShape ι}

theorem isZero_homology_extendScalars_iff (S : Type w) [CommRing S] [inst : Algebra R S]
    (K : HomologicalComplex (ModuleCat.{u} R) c) {p q r : ι} (hp : c.prev q = p)
    (hr : c.next q = r) :
    IsZero ((((ModuleCat.extendScalars.{u, w, u} (algebraMap R S)).mapHomologicalComplex c).obj
        K).homology q) ↔
      Exact ((K.d p q).hom.lTensor S) ((K.d q r).hom.lTensor S) := by
  obtain ⟨φ, rfl⟩ : ∃ φ : R →+* S, φ.toAlgebra = inst := ⟨_, toAlgebra_algebraMap⟩
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ p q r hp hr,
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  rfl

end Modules

section Explicit

open CategoryTheory Category Limits ChangeOfRings

universe u

variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
  {ι : Type*} {c : ComplexShape ι}

end Explicit

section Main

open CategoryTheory Category Limits

universe u

variable {R : Type u} [CommRing R]

end Main

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

noncomputable section

namespace GlobalTheory.QCoh.Qcqs

section Glue

variable {X : Scheme.{u}} {R : Type*} [CommRing R] (S : Submonoid R) (U : X.Opens)
  {A B : Set.Iic U → Type*} [∀ V, AddCommGroup (A V)] [∀ V, Module R (A V)]
  [∀ V, AddCommGroup (B V)] [∀ V, Module R (B V)]
  (rA : ∀ {V W : Set.Iic U}, V ≤ W → A W →ₗ[R] A V)
  (rB : ∀ {V W : Set.Iic U}, V ≤ W → B W →ₗ[R] B V)
  (φ : ∀ V, A V →ₗ[R] B V)

theorem exists_smul_eq_zero_of_isCompact
    (hφ : ∀ {V W} (h : V ≤ W) (a : A W), φ V (rA h a) = rB h (φ W a))
    (hbot : ∀ V : Set.Iic U, V.1 = ⊥ → Subsingleton (A V))
    (sepA : ∀ {V₁ V₂ W : Set.Iic U} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W), W.1 ≤ V₁.1 ⊔ V₂.1 →
      ∀ a : A W, rA h₁ a = 0 → rA h₂ a = 0 → a = 0)
    (hker : ∀ V : Set.Iic U, IsAffineOpen V.1 → ∀ a : A V, φ V a = 0 → ∃ s ∈ S, s • a = 0)
    (W : Set.Iic U) (hW : IsCompact (W.1 : Set X)) (a : A W) (ha : φ W a = 0) :
    ∃ s ∈ S, s • a = 0 := by
  obtain ⟨W, hWU⟩ := W
  refine compact_open_induction_on
    (P := fun W ↦ ∀ (h : W ∈ Set.Iic U), IsCompact (W : Set X) → ∀ a : A ⟨W, h⟩,
      φ ⟨W, h⟩ a = 0 → ∃ s ∈ S, s • a = 0) W hW ?_ ?_ hWU hW a ha
  · intro h _ a _
    have := hbot ⟨⊥, h⟩ rfl
    exact ⟨1, S.one_mem, Subsingleton.elim _ _⟩
  · intro T hT V ih h _ a ha
    let T' : Set.Iic U := ⟨T, (le_sup_left.trans h : T ≤ U)⟩
    let V' : Set.Iic U := ⟨V.1, (le_sup_right.trans h : V.1 ≤ U)⟩
    have h₁ : T' ≤ ⟨T ⊔ V.1, h⟩ := le_sup_left (a := T)
    have h₂ : V' ≤ ⟨T ⊔ V.1, h⟩ := le_sup_right (a := T)
    obtain ⟨s₁, hs₁, e₁⟩ := ih T'.2 hT (rA h₁ a) (by rw [hφ, ha, map_zero])
    obtain ⟨s₂, hs₂, e₂⟩ := hker V' V.2 (rA h₂ a) (by rw [hφ, ha, map_zero])
    refine ⟨s₁ * s₂, mul_mem hs₁ hs₂, sepA h₁ h₂ le_rfl _ ?_ ?_⟩
    · rw [map_smul, mul_comm, mul_smul, e₁, smul_zero]
    · rw [map_smul, mul_smul, e₂, smul_zero]

theorem exists_smul_eq_map_of_isCompact_of_isQuasiSeparated
    (hφ : ∀ {V W} (h : V ≤ W) (a : A W), φ V (rA h a) = rB h (φ W a))
    (hrB : ∀ {V₁ V₂ V₃} (h : V₁ ≤ V₂) (h' : V₂ ≤ V₃) (b : B V₃),
      rB h (rB h' b) = rB (h.trans h') b)
    (hbotA : ∀ V : Set.Iic U, V.1 = ⊥ → Subsingleton (A V))
    (hbotB : ∀ V : Set.Iic U, V.1 = ⊥ → Subsingleton (B V))
    (sepA : ∀ {V₁ V₂ W : Set.Iic U} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W), W.1 ≤ V₁.1 ⊔ V₂.1 →
      ∀ a : A W, rA h₁ a = 0 → rA h₂ a = 0 → a = 0)
    (sepB : ∀ {V₁ V₂ W : Set.Iic U} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W), W.1 ≤ V₁.1 ⊔ V₂.1 →
      ∀ b : B W, rB h₁ b = 0 → rB h₂ b = 0 → b = 0)
    (glueA : ∀ {V₁ V₂ W : Set.Iic U} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W), W.1 ≤ V₁.1 ⊔ V₂.1 →
      ∀ (a₁ : A V₁) (a₂ : A V₂), rA (inf_le_left : V₁ ⊓ V₂ ≤ V₁) a₁ = rA inf_le_right a₂ →
        ∃ a : A W, rA h₁ a = a₁ ∧ rA h₂ a = a₂)
    (hker : ∀ V : Set.Iic U, IsAffineOpen V.1 → ∀ a : A V, φ V a = 0 → ∃ s ∈ S, s • a = 0)
    (hsurj : ∀ V : Set.Iic U, IsAffineOpen V.1 → ∀ b : B V, ∃ s ∈ S, ∃ a : A V, s • b = φ V a)
    (W : Set.Iic U) (hW : IsCompact (W.1 : Set X)) (hW' : IsQuasiSeparated (W.1 : Set X))
    (b : B W) : ∃ s ∈ S, ∃ a : A W, s • b = φ W a := by
  obtain ⟨W, hWU⟩ := W
  refine compact_open_induction_on
    (P := fun W ↦ ∀ (h : W ∈ Set.Iic U), IsCompact (W : Set X) → IsQuasiSeparated (W : Set X) →
      ∀ b : B ⟨W, h⟩, ∃ s ∈ S, ∃ a : A ⟨W, h⟩, s • b = φ ⟨W, h⟩ a) W hW ?_ ?_ hWU hW hW' b
  · intro h _ _ b
    have := hbotB ⟨⊥, h⟩ rfl
    exact ⟨1, S.one_mem, 0, Subsingleton.elim _ _⟩
  · intro T hT V ih h _ hqs b
    let T' : Set.Iic U := ⟨T, (le_sup_left.trans h : T ≤ U)⟩
    let V' : Set.Iic U := ⟨V.1, (le_sup_right.trans h : V.1 ≤ U)⟩
    have h₁ : T' ≤ ⟨T ⊔ V.1, h⟩ := le_sup_left (a := T)
    have h₂ : V' ≤ ⟨T ⊔ V.1, h⟩ := le_sup_right (a := T)
    obtain ⟨s₁, hs₁, a₁, e₁⟩ := ih T'.2 hT (hqs.of_subset Set.subset_union_left) (rB h₁ b)
    obtain ⟨s₂, hs₂, a₂, e₂⟩ := hsurj V' V.2 (rB h₂ b)
    have hc : IsCompact ((T' ⊓ V').1 : Set X) :=
      hqs _ _ Set.subset_union_left T.2 hT Set.subset_union_right V.1.2 V.2.isCompact
    obtain ⟨s, hs, e⟩ := exists_smul_eq_zero_of_isCompact S U rA rB φ hφ hbotA sepA hker
      (T' ⊓ V') hc (s₂ • rA inf_le_left a₁ - s₁ • rA inf_le_right a₂) (by
        rw [map_sub, map_smul, map_smul, hφ, hφ, ← e₁, ← e₂, map_smul, map_smul, hrB, hrB,
          smul_comm, sub_self])
    obtain ⟨a, ha₁, ha₂⟩ := glueA h₁ h₂ le_rfl (s • s₂ • a₁) (s • s₁ • a₂) (by
      rw [smul_sub, sub_eq_zero] at e
      simpa only [map_smul] using e)
    refine ⟨s * (s₁ * s₂), mul_mem hs (mul_mem hs₁ hs₂), a, ?_⟩
    rw [← sub_eq_zero]
    refine sepB h₁ h₂ le_rfl _ ?_ ?_
    · rw [map_sub, ← hφ, ha₁, map_smul, map_smul, map_smul, ← e₁, mul_comm s₁, mul_smul, mul_smul,
        sub_self]
    · rw [map_sub, ← hφ, ha₂, map_smul, map_smul, map_smul, ← e₂, mul_smul, mul_smul, sub_self]

end Glue

section Sheaf

variable {X : Scheme.{u}} (F : X.Modules) {V₁ V₂ W : X.Opens}

theorem subsingleton_sections_of_eq_bot (h : W = ⊥) : Subsingleton Γ(F, W) := by
  refine ⟨fun s t ↦ ?_⟩
  exact TopCat.Sheaf.eq_of_locally_eq' (C := Ab.{u}) ⟨F.presheaf, F.isSheaf⟩
    (fun i : PEmpty.{u + 1} ↦ i.elim) W (fun i ↦ i.elim) (by simp [h]) s t (fun i ↦ i.elim)

theorem section_eq_zero_of_res₂ (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : W ≤ V₁ ⊔ V₂) (s : Γ(F, W))
    (e₁ : F.presheaf.map (homOfLE h₁).op s = 0) (e₂ : F.presheaf.map (homOfLE h₂).op s = 0) :
    s = 0 :=
  TopCat.Sheaf.eq_of_locally_eq₂ (C := Ab.{u}) ⟨F.presheaf, F.isSheaf⟩ (homOfLE h₁) (homOfLE h₂)
    h s 0 (e₁.trans (map_zero _).symm) (e₂.trans (map_zero _).symm)

theorem exists_section_glue₂ (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : W ≤ V₁ ⊔ V₂) (s₁ : Γ(F, V₁))
    (s₂ : Γ(F, V₂))
    (e : F.presheaf.map (homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)).op s₁ =
      F.presheaf.map (homOfLE inf_le_right).op s₂) :
    ∃ s : Γ(F, W), F.presheaf.map (homOfLE h₁).op s = s₁ ∧
      F.presheaf.map (homOfLE h₂).op s = s₂ := by
  let 𝒰 : Bool → X.Opens := fun b ↦ Bool.rec V₁ V₂ b
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (C := Ab.{u}) ⟨F.presheaf, F.isSheaf⟩
    𝒰 W (fun b ↦ Bool.rec (homOfLE h₁) (homOfLE h₂) b)
    (h.trans (sup_le (le_iSup 𝒰 false) (le_iSup 𝒰 true)))
    (fun b ↦ Bool.rec s₁ s₂ b) (by
      rintro (_ | _) (_ | _)
      · rfl
      · exact e
      · have := congr(F.presheaf.map (homOfLE (inf_comm V₂ V₁).le).op $e)
        rw [res_res, res_res] at this
        exact this.symm
      · rfl)
  exact ⟨s, hs false, hs true⟩

end Sheaf

section BasicOpen

variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}

def resLinearOver (hW : W ≤ U) (hV : V ≤ U) (h : V ≤ W) :
    letI := resModule F hW
    letI := resModule F hV
    Γ(F, W) →ₗ[Γ(X, U)] Γ(F, V) :=
  letI := resModule F hW
  letI := resModule F hV
  { toFun := F.presheaf.map (homOfLE h).op
    map_add' := map_add _
    map_smul' := fun r s ↦ by
      change F.presheaf.map (homOfLE h).op (X.presheaf.map (homOfLE hW).op r • s) =
        X.presheaf.map (homOfLE hV).op r • F.presheaf.map (homOfLE h).op s
      rw [F.map_smul, res_res_ring hW h] }

variable [F.IsQuasicoherent]

theorem exists_pow_smul_eq_zero_of_isCompact (hU : IsCompact (U : Set X)) (f : Γ(X, U))
    (h : V ≤ U) (hV : V = X.basicOpen f) (t : Γ(F, U))
    (ht : F.presheaf.map (homOfLE h).op t = 0) : ∃ n : ℕ, f ^ n • t = 0 := by
  letI (W : Set.Iic U) : Module Γ(X, U) Γ(F, W.1) := resModule F W.2
  letI (W : Set.Iic U) : Module Γ(X, U) Γ(F, W.1 ⊓ V) := resModule F (inf_le_right.trans h)
  obtain ⟨_, ⟨n, rfl⟩, e⟩ := exists_smul_eq_zero_of_isCompact (.powers f) U
    (A := fun W ↦ Γ(F, W.1)) (B := fun W ↦ Γ(F, W.1 ⊓ V))
    (fun {W₁ W₂} h' ↦ resLinearOver F W₂.2 W₁.2 h')
    (fun {W₁ W₂} h' ↦ resLinearOver F _ _ (inf_le_inf_right V h'))
    (fun W ↦ resLinearOver F W.2 _ inf_le_left)
    (fun h' a ↦ (res_res F _ _ a).trans (res_res F _ _ a).symm)
    (fun W hW ↦ subsingleton_sections_of_eq_bot F hW)
    (fun h₁ h₂ h₃ ↦ section_eq_zero_of_res₂ F h₁ h₂ h₃)
    (fun W hW a ha ↦ by
      obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero F hW (X.presheaf.map (homOfLE (W.2 : W.1 ≤ U)).op f)
        inf_le_left (by rw [X.basicOpen_res, hV]) a ha
      exact ⟨f ^ n, ⟨n, rfl⟩, by rw [← map_pow] at hn; exact hn⟩)
    ⟨U, Set.self_mem_Iic⟩ hU t (by
      change F.presheaf.map (homOfLE inf_le_left).op t = 0
      rw [← res_res F h inf_le_right, ht, map_zero])
  refine ⟨n, ?_⟩
  rw [← res_self_ring le_rfl (f ^ n)]
  exact e

theorem exists_pow_smul_eq_res_of_qcqs (hU : IsCompact (U : Set X))
    (hU' : IsQuasiSeparated (U : Set X)) (f : Γ(X, U)) (h : V ≤ U) (hV : V = X.basicOpen f)
    (s : Γ(F, V)) : ∃ (n : ℕ) (t : Γ(F, U)),
      X.presheaf.map (homOfLE h).op f ^ n • s = F.presheaf.map (homOfLE h).op t := by
  letI (W : Set.Iic U) : Module Γ(X, U) Γ(F, W.1) := resModule F W.2
  letI (W : Set.Iic U) : Module Γ(X, U) Γ(F, W.1 ⊓ V) := resModule F (inf_le_right.trans h)
  obtain ⟨_, ⟨n, rfl⟩, t, e⟩ := exists_smul_eq_map_of_isCompact_of_isQuasiSeparated (.powers f) U
    (A := fun W ↦ Γ(F, W.1)) (B := fun W ↦ Γ(F, W.1 ⊓ V))
    (fun {W₁ W₂} h' ↦ resLinearOver F W₂.2 W₁.2 h')
    (fun {W₁ W₂} h' ↦ resLinearOver F _ _ (inf_le_inf_right V h'))
    (fun W ↦ resLinearOver F W.2 _ inf_le_left)
    (fun h' a ↦ (res_res F _ _ a).trans (res_res F _ _ a).symm)
    (fun h₁ h₂ b ↦ res_res F _ _ b)
    (fun W hW ↦ subsingleton_sections_of_eq_bot F hW)
    (fun W hW ↦ subsingleton_sections_of_eq_bot F (by simp [hW]))
    (fun h₁ h₂ h₃ ↦ section_eq_zero_of_res₂ F h₁ h₂ h₃)
    (fun h₁ h₂ h₃ ↦ section_eq_zero_of_res₂ F (inf_le_inf_right V h₁) (inf_le_inf_right V h₂)
      ((inf_le_inf_right V h₃).trans (inf_sup_right _ _ _).le))
    (fun h₁ h₂ h₃ ↦ exists_section_glue₂ F h₁ h₂ h₃)
    (fun W hW a ha ↦ by
      obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero F hW (X.presheaf.map (homOfLE (W.2 : W.1 ≤ U)).op f)
        inf_le_left (by rw [X.basicOpen_res, hV]) a ha
      exact ⟨f ^ n, ⟨n, rfl⟩, by rw [← map_pow] at hn; exact hn⟩)
    (fun W hW b ↦ by
      obtain ⟨n, a, hn⟩ := exists_pow_smul_eq_res F hW (X.presheaf.map (homOfLE (W.2 : W.1 ≤ U)).op f)
        (V := W.1 ⊓ V) inf_le_left (by rw [X.basicOpen_res, hV]) b
      exact ⟨f ^ n, ⟨n, rfl⟩, a, by rw [res_res_ring (show W.1 ≤ U from W.2), ← map_pow] at hn; exact hn⟩)
    ⟨U, Set.self_mem_Iic⟩ hU hU' (F.presheaf.map (homOfLE inf_le_right).op s)
  refine ⟨n, t, ?_⟩
  have e' : X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op (f ^ n) •
      F.presheaf.map (homOfLE inf_le_right).op s =
      F.presheaf.map (homOfLE inf_le_left).op t := e
  have := congr(F.presheaf.map (homOfLE (le_inf h le_rfl)).op $e')
  rwa [F.map_smul, res_res, res_res, res_res_ring, res_self, map_pow] at this

theorem isLocalizedModule_resBasicOpen_of_qcqs (hU : IsCompact (U : Set X))
    (hU' : IsQuasiSeparated (U : Set X)) (f : Γ(X, U)) :
    IsLocalizedModule.Away f (resBasicOpen F f) :=
  (isLocalizedModule_resBasicOpen_iff F f).mpr
    ⟨exists_pow_smul_eq_res_of_qcqs F hU hU' f _ rfl,
      exists_pow_smul_eq_zero_of_isCompact F hU f _ rfl⟩

end BasicOpen

section Hom

variable {X : Scheme.{u}} {F G : X.Modules} (φ : F ⟶ G) {U V W : X.Opens}

end Hom

end GlobalTheory.QCoh.Qcqs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthQuotRangeEqAddValDet
section
namespace GlobalTheory

open IsDiscreteValuationRing

section CokernelLength

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem length_quot_range_eq_addVal_det {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] M) :
    Module.length R (M ⧸ LinearMap.range f) = addVal R (LinearMap.det f) := by
  first
  | exact @_root_.GlobalTheory.LengthCokernelFinrank.length_coker_eq_addVal_det
  | exact _root_.GlobalTheory.LengthCokernelFinrank.length_coker_eq_addVal_det
  | (apply _root_.GlobalTheory.LengthCokernelFinrank.length_coker_eq_addVal_det <;> assumption)
  | (intros; apply _root_.GlobalTheory.LengthCokernelFinrank.length_coker_eq_addVal_det <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LengthCokernelFinrank.length_coker_eq_addVal_det <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LengthCokernelFinrank.length_coker_eq_addVal_det ..)

end CokernelLength

end GlobalTheory
end

