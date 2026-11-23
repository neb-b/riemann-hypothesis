module

public import Mathlib
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0011
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0010
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0003
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperFiniteness

@[expose] public section

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalCompare
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe c236Ext c236Scheme

private noncomputable def H.linearMapV436 {X : Scheme.{c236Scheme}}
    [HasExt.{c236Ext} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{c236Scheme})]
    (A : Type*) [CommRing A] [Algebra A Γ(X, ⊤)]
    {F G : X.Modules} (φ : F ⟶ G) (n : ℕ) :
    Sheaf.H.{c236Ext} (modulesAb F) n →ₗ[A] Sheaf.H.{c236Ext} (modulesAb G) n where
  toFun := Sheaf.H.map.{c236Ext} (modulesAbMap φ) n
  map_add' := map_add _
  map_smul' a x := by
    change Sheaf.H.map.{c236Ext} (modulesAbMap φ) n (a • x) =
      a • Sheaf.H.map.{c236Ext} (modulesAbMap φ) n x
    rw [H.smul_def, H.smul_def, ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply,
      ← modulesAbMap_comp, ← modulesAbMap_comp, smulHom_comp]

end

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

attribute [local instance] algebraOfOver

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  [X.Over (Spec (.of A))] (F : X.Modules) (q : ℕ)

lemma formalτ_mem_formalQ (n : ℕ) (y : Sheaf.H.{u} (modulesAb (idealPow I F (n + 2))) (q + 1))
    (hy : y ∈ formalQ I F q (n + 1)) :
    H.linearMap A (idealPowSucc I F (n + 1)) (q + 1) y ∈ formalQ I F q n := by
  obtain ⟨x, rfl⟩ := hy
  exact ⟨formalτE I F q n x, formalδ_naturality I F q n x⟩

def formalτQ (n : ℕ) : formalQ I F q (n + 1) →ₗ[A] formalQ I F q n :=
  (H.linearMap A (idealPowSucc I F (n + 1)) (q + 1)).restrict (formalτ_mem_formalQ I F q n)

abbrev formalτP : ∀ n, (Sheaf.H.{u} (modulesAb F) q ⧸ formalK I F q (n + 1)) →ₗ[A]
    (Sheaf.H.{u} (modulesAb F) q ⧸ formalK I F q n) :=
  quotTower (formalK I F q) (formalK_antitone I F q)

lemma formalι_comm (n : ℕ) :
    (formalτE I F q n).comp (formalι I F q (n + 1)) = (formalι I F q n).comp (formalτP I F q n) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Sheaf.H.map.{u} (modulesAbMap (quotPowMap I F n)) q
      (Sheaf.H.map.{u} (modulesAbMap (quotPowπ I F (n + 1))) q h) =
    Sheaf.H.map.{u} (modulesAbMap (quotPowπ I F n)) q h
  rw [← Sheaf.H.map_comp_apply, ← modulesAbMap_comp, quotPowπ_map]

lemma formalπ_comm (n : ℕ) :
    (formalτQ I F q n).comp (formalπ I F q (n + 1)) = (formalπ I F q n).comp (formalτE I F q n) := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  exact (formalδ_naturality I F q n x).symm

variable {I F q}

theorem mem_range_formalβ_of_mem_towerLimit {c : ℕ}
    (hQ : ∀ n, towerComp (E := fun m => formalQ I F q m) (formalτQ I F q) n c = 0)
    {x : ∀ n, Sheaf.H.{u} (modulesAb (quotPow I F n)) q} (hx : x ∈ towerLimit (E := fun m => Sheaf.H.{u} (modulesAb (quotPow I F m)) q) (formalτE I F q))
    (n : ℕ) : x n ∈ LinearMap.range (formalβ I F q n) := by
  obtain ⟨p, hp⟩ := (bijective_towerLimitMap (formalτP I F q) (formalτE I F q) (formalτQ I F q)
    (formalι I F q) (formalπ I F q) (formalι_comm I F q) (formalπ_comm I F q)
    (formalι_injective I F q) (range_formalι I F q)
    (formalι_injective I F q) (range_formalι I F q) (formalπ_comm I F q) hQ).2 ⟨x, hx⟩
  obtain ⟨h, hh⟩ := Submodule.Quotient.mk_surjective _ (p.1 n)
  refine ⟨h, ?_⟩
  have := congrArg (fun y => y.1 n) hp
  simp only at this
  rw [← this]
  change formalβ I F q n h = formalι I F q n (p.1 n)
  rw [← hh]
  rfl

end

end GroundTheory.Arith.SchemeCoh
end

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  [X.Over (Spec (.of A))] {F : X.Modules}

omit [IsNoetherianRing A] in
lemma algV_eq_toFunctions (V : X.Opens) (a : A) : algV X V a = toFunctions V a := rfl

def powSmulTopΓ (V : X.Opens) (n : ℕ) : Submodule Γ(X, V) Γ(F, V) where
  carrier := (I ^ n • ⊤ : Submodule A Γ(F, V))
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' c x hx := by
    refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun y z hy hz => ?_)
    · change c • (a • y) ∈ (I ^ n • ⊤ : Submodule A Γ(F, V))
      rw [sectionsModuleA_smul, smul_smul, mul_comm, ← smul_smul, ← sectionsModuleA_smul]
      exact Submodule.smul_mem_smul ha trivial
    · rw [smul_add]
      exact add_mem hy hz

lemma mem_pow_smul_top_iff {V : X.Opens} (n : ℕ) (m : Γ(F, V)) :
    m ∈ (I ^ n • ⊤ : Submodule A Γ(F, V)) ↔
      m ∈ (Ideal.map (toFunctions V) (I ^ n) • ⊤ : Submodule Γ(X, V) Γ(F, V)) := by
  constructor
  · intro hm
    refine Submodule.smul_induction_on hm (fun a ha x _ => ?_) (fun x y hx hy => add_mem hx hy)
    rw [sectionsModuleA_smul, algV_eq_toFunctions]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) trivial
  · intro hm
    have h : I ^ n ≤ ((powSmulTopΓ (F := F) I V n).colon (Set.univ)).comap (toFunctions V) := by
      intro a ha
      rw [Ideal.mem_comap, Submodule.mem_colon]
      intro x _
      change toFunctions V a • x ∈ (I ^ n • ⊤ : Submodule A Γ(F, V))
      rw [← algV_eq_toFunctions, ← sectionsModuleA_smul]
      exact Submodule.smul_mem_smul ha trivial
    have h' := Ideal.map_le_iff_le_comap.2 h
    have : (Ideal.map (toFunctions V) (I ^ n) • ⊤ : Submodule Γ(X, V) Γ(F, V)) ≤
        powSmulTopΓ I V n :=
      Submodule.smul_le.2 fun c hc x _ => Submodule.mem_colon.1 (h' hc) x trivial
    exact this hm

variable [F.IsQuasicoherent]

lemma mem_range_idealPowι_iff {V : X.Opens} (hV : IsAffineOpen V) (n : ℕ) (m : Γ(F, V)) :
    m ∈ Set.range ((idealPowι I F n).app V) ↔ m ∈ (I ^ n • ⊤ : Submodule A Γ(F, V)) := by
  rw [range_idealPowι_app I F hV n, mem_pow_smul_top_iff]
  rfl

variable (hF : IsCoherent F)

section Sections

variable {V : X.Opens} (hV : IsAffineOpen V)

def reesCoef (n : ℕ) : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V) →+ Γ(F, V) where
  toFun s := (reesSectionsMap I hF hV s).coeff n
  map_zero' := by rw [reesSectionsMap_zero]; rfl
  map_add' s s' := by rw [reesSectionsMap_add]; rfl

lemma reesCoef_mem (n : ℕ) (s : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    reesCoef I hF hV n s ∈ Set.range ((idealPowι I F n).app V) :=
  (mem_range_idealPowι_iff I hV n _).2 ((mem_reesSubmodule_iff.1 (reesSectionsMap_mem hF hV s)) n)

lemma idealPowι_app_injective (n : ℕ) : Function.Injective ((idealPowι I F n).app V) :=
  kernel_ι_app_injective _ V

def reesDeg (n : ℕ) : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V) →+ Γ(idealPow I F n, V) where
  toFun s := (Equiv.ofInjective _ (idealPowι_app_injective I n)).symm
    ⟨reesCoef I hF hV n s, reesCoef_mem I hF hV n s⟩
  map_zero' := by
    apply idealPowι_app_injective I n
    refine (Equiv.apply_ofInjective_symm (idealPowι_app_injective (F := F) (V := V) I n) _).trans ?_
    change reesCoef I hF hV n 0 = _
    rw [map_zero, map_zero]
  map_add' s s' := by
    apply idealPowι_app_injective I n
    refine (Equiv.apply_ofInjective_symm (idealPowι_app_injective (F := F) (V := V) I n) _).trans ?_
    change reesCoef I hF hV n (s + s') = _
    rw [map_add (f := _), map_add (f := _)]
    congr 1
    · exact (Equiv.apply_ofInjective_symm (idealPowι_app_injective (F := F) (V := V) I n)
        ⟨reesCoef I hF hV n s, reesCoef_mem I hF hV n s⟩).symm
    · exact (Equiv.apply_ofInjective_symm (idealPowι_app_injective (F := F) (V := V) I n)
        ⟨reesCoef I hF hV n s', reesCoef_mem I hF hV n s'⟩).symm

lemma idealPowι_reesDeg (n : ℕ) (s : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    (idealPowι I F n).app V (reesDeg I hF hV n s) = reesCoef I hF hV n s :=
  Equiv.apply_ofInjective_symm (idealPowι_app_injective I n)
    ⟨reesCoef I hF hV n s, reesCoef_mem I hF hV n s⟩

include hV in
lemma lsingle_mem_reesSubmodule (n : ℕ) (g : Γ(idealPow I F n, V)) :
    PolynomialModule.lsingle A n ((idealPowι I F n).app V g) ∈ reesSubmodule I Γ(F, V) := by
  rw [mem_reesSubmodule_iff]
  intro k
  rw [PolynomialModule.lsingle_apply]
  split_ifs with h
  · subst h
    exact (mem_range_idealPowι_iff I hV n _).1 ⟨g, rfl⟩
  · exact zero_mem _


include hF hV in
def reesInc (n : ℕ) : Γ(idealPow I F n, V) →+ Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V) :=
  (reesSectionsEquiv I hF hV).symm.toAddMonoidHom.comp
    (AddMonoidHom.codRestrict
      ((PolynomialModule.lsingle A n).toAddMonoidHom.comp ((idealPowι I F n).app V).hom)
      (reesSubmodule I Γ(F, V)).toAddSubmonoid (lsingle_mem_reesSubmodule I hV n))

lemma reesSectionsMap_reesInc (n : ℕ) (g : Γ(idealPow I F n, V)) :
    reesSectionsMap I hF hV (reesInc I hF hV n g) =
      PolynomialModule.lsingle A n ((idealPowι I F n).app V g) := by
  rw [← reesSectionsEquiv_apply]
  change ((reesSectionsEquiv I hF hV ((reesSectionsEquiv I hF hV).symm _)) :
    PolynomialModule A Γ(F, V)) = _
  rw [AddEquiv.apply_symm_apply]
  rfl

lemma reesCoef_reesInc (n k : ℕ) (g : Γ(idealPow I F n, V)) :
    reesCoef I hF hV k (reesInc I hF hV n g) = if n = k then (idealPowι I F n).app V g else 0 := by
  change (reesSectionsMap I hF hV (reesInc I hF hV n g)).coeff k = _
  rw [reesSectionsMap_reesInc, PolynomialModule.lsingle_apply]

lemma reesDeg_reesInc (n : ℕ) (g : Γ(idealPow I F n, V)) :
    reesDeg I hF hV n (reesInc I hF hV n g) = g := by
  apply idealPowι_app_injective I n
  rw [idealPowι_reesDeg, reesCoef_reesInc, if_pos rfl]

lemma reesDeg_reesInc_of_ne {n k : ℕ} (h : n ≠ k) (g : Γ(idealPow I F n, V)) :
    reesDeg I hF hV k (reesInc I hF hV n g) = 0 := by
  apply idealPowι_app_injective I k
  rw [idealPowι_reesDeg, reesCoef_reesInc, if_neg h, map_zero]

end Sections

end

end GroundTheory.Arith.SchemeCoh
end

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ReesCech
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe w u

noncomputable section

attribute [local instance] algebraOfOver

variable {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}} [X.Over (Spec (.of A))]
  (F : X.Modules)

abbrev reesPush : X.Modules := (Scheme.Modules.pushforward (reesPr I X)).obj (reesSheaf I F)

def reesMul (r : reesAlgebra I) : reesPush I F ⟶ reesPush I F :=
  (Scheme.Modules.pushforward (reesPr I X)).map
    (smulHom (reesSheaf I F) (algebraMap (reesAlgebra I) Γ(reesScheme I X, ⊤) r))

lemma reesMul_one : reesMul I F 1 = 𝟙 _ := by
  rw [reesMul, map_one, ← smulRingHom_apply, map_one]
  exact (Scheme.Modules.pushforward (reesPr I X)).map_id _

lemma reesMul_mul (r s : reesAlgebra I) : reesMul I F (r * s) = reesMul I F s ≫ reesMul I F r := by
  rw [reesMul, reesMul, reesMul, map_mul, ← smulRingHom_apply, map_mul, ← Functor.map_comp]
  rfl

lemma reesMul_zero : reesMul I F 0 = 0 := by
  rw [reesMul, map_zero, ← smulRingHom_apply, map_zero]
  exact (Scheme.Modules.pushforward (reesPr I X)).map_zero _ _

lemma reesMul_add (r s : reesAlgebra I) : reesMul I F (r + s) = reesMul I F r + reesMul I F s := by
  rw [reesMul, reesMul, reesMul, map_add (f := _), ← smulRingHom_apply, map_add (f := _)]
  exact (Scheme.Modules.pushforward (reesPr I X)).map_add

variable {ι : Type w} (𝔘 : ι → X.Opens) (p : ℕ)

abbrev reesPre : (Opens X.toTopCat)ᵒᵖ ⥤ AddCommGrpCat.{u} := (modulesAb (reesPush I F)).obj

def reesCechRingHom : reesAlgebra I →+* AddMonoid.End (cechH (reesPre I F) 𝔘 p) where
  toFun r := cechHMap 𝔘 (modulesAbMap (reesMul I F r)).hom p
  map_one' := by
    ext x
    change cechHMap 𝔘 (modulesAbMap (reesMul I F 1)).hom p x = x
    rw [reesMul_one, modulesAbMap_id]
    exact cechHMap_id 𝔘 p x
  map_mul' r s := by
    ext x
    change cechHMap 𝔘 (modulesAbMap (reesMul I F (r * s))).hom p x =
      cechHMap 𝔘 (modulesAbMap (reesMul I F r)).hom p (cechHMap 𝔘 (modulesAbMap (reesMul I F s)).hom p x)
    rw [reesMul_mul, modulesAbMap_comp, ← cechHMap_comp]
    rfl
  map_zero' := by
    ext x
    change cechHMap 𝔘 (modulesAbMap (reesMul I F 0)).hom p x = 0
    rw [reesMul_zero]
    exact cechHMap_zero 𝔘 p x
  map_add' r s := by
    ext x
    change cechHMap 𝔘 (modulesAbMap (reesMul I F (r + s))).hom p x =
      cechHMap 𝔘 (modulesAbMap (reesMul I F r)).hom p x +
        cechHMap 𝔘 (modulesAbMap (reesMul I F s)).hom p x
    rw [reesMul_add, modulesAbMap_add]
    exact cechHMap_add 𝔘 _ _ p x

@[instance_reducible]
def reesCechModule : Module (reesAlgebra I) (cechH (reesPre I F) 𝔘 p) :=
  Module.compHom _ (reesCechRingHom I F 𝔘 p)

variable [IsNoetherianRing A] [IsProper (X ↘ Spec (.of A))] {F} (hF : IsCoherent F)
  (hU : iSup 𝔘 = ⊤) (hUaff : ∀ (m : ℕ) (t : Fin (m + 1) → ι), IsAffineOpen (⨅ a, 𝔘 (t a)))


omit [IsNoetherianRing A] [IsProper (X ↘ Spec (.of A))] in
include hF hU hUaff in
theorem exists_reesCech_addEquiv :
    ∃ e : cechH (reesPre I F) 𝔘 p ≃+ Sheaf.H.{u} (modulesAb (reesSheaf I F)) p,
      ∀ (r : reesAlgebra I) x, e (cechHMap 𝔘 (modulesAbMap (reesMul I F r)).hom p x) = r • e x := by
  have : (reesSheaf I F).IsQuasicoherent := (isCoherent_reesSheaf hF).1
  set pr := reesPr I X
  have hUr : ⨆ k, pr ⁻¹ᵁ 𝔘 k = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hU]
    rfl
  have hUraff : ∀ (m : ℕ) (t : Fin (m + 1) → ι), IsAffineOpen (⨅ a, pr ⁻¹ᵁ 𝔘 (t a)) := fun m t => by
    have h := preimage_inter pr 𝔘 t
    rw [← inter_eq_iInf (fun k => pr ⁻¹ᵁ 𝔘 k) t, ← h, inter_eq_iInf]
    exact (hUaff m t).preimage pr
  refine ⟨(cechHPushforwardEquiv pr (reesSheaf I F) 𝔘 p).trans
    (cechHAddEquivH (fun k => pr ⁻¹ᵁ 𝔘 k) hUr hUraff (reesSheaf I F) p), fun r x => ?_⟩
  simp only [AddEquiv.trans_apply]
  rw [cechHPushforwardEquiv_naturality pr (reesSheaf I F) 𝔘 p _
    (modulesAbMap (smulHom (reesSheaf I F)
      (algebraMap (reesAlgebra I) Γ(reesScheme I X, ⊤) r))).hom (fun W y => rfl) x,
    cechHAddEquivH_naturality]
  rfl


include hF hU hUaff in
theorem finite_reesCech :
    @Module.Finite (reesAlgebra I) (cechH (reesPre I F) 𝔘 p) _ _ (reesCechModule I F 𝔘 p) := by
  let := reesCechModule I F 𝔘 p
  obtain ⟨e, he⟩ := exists_reesCech_addEquiv I 𝔘 p hF hU hUaff
  have := finite_H_of_isProper (A := reesAlgebra I) (reesSheaf I F) (isCoherent_reesSheaf hF) p
  exact Module.Finite.equiv (e.toLinearEquiv fun r x => he r x).symm

end

end GroundTheory.Arith.SchemeCoh
end

