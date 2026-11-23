module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1966
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAbelianSchemeOfAbelianThickenings
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SndSectionValueTranslateProdFirstOrderLinear
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KSLin

theorem valR_eq_evAt {A : Type} [CommRing A] {Y : Scheme.{0}} (x : Sp A ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(Y, U)) : valR x U f = GlobalTheory.TanDeriv.evAt x U h f := dif_pos h

theorem valR_spMap_comp {R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) {Y : Scheme.{0}} (x : Sp R ⟶ Y)
    (U : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(Y, U)) : valR (spMap φ ≫ x) U f = φ (valR x U f) := by
  rw [valR_eq_evAt x U h, valR_eq_evAt _ U (GlobalTheory.TanDeriv.comp_top_le φ x U h)]
  exact GlobalTheory.TanDeriv.evAt_comp φ x U h _ f

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* B) (ψ : B →+* C) :
    spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {G : Over X0} [GrpObj G]

theorem top_le_of_fst (z : overAt x0 (DualNumber S) ⟶ G) (O : G.left.Opens)
    (h : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ z.left) ⁻¹ᵁ O) :
    ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from z.left) ⁻¹ᵁ O := by
  refine GlobalTheory.TanDeriv.top_le_of_comp (TrivSqZeroExt.fstHom S S S).toRingHom ?_ ?_ _ O h
  · intro y
    exact ⟨TrivSqZeroExt.inl y, rfl⟩
  · intro x hx
    have h1 : x.fst = 0 := hx
    ext <;> simp [h1]

theorem fst_comp_of_smT_zero (g₀ : Sp S ⟶ G.left) (g' : overAt x0 (DualNumber S) ⟶ G)
    (hg : g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀) (z : overAt x0 (DualNumber S) ⟶ G)
    (hz : smT x0 0 z = g') : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ z.left = g₀ := by
  have h1 : (smT x0 0 z).left = spMap (epsMul 0) ≫ z.left := rfl
  have h2 := congrArg (fun φ => spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ φ) (hz ▸ h1)
  rw [hg, ← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap] at h2
  have e1 : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
    ext; simp
  have e2 : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (epsMul (0 : S)) =
      (TrivSqZeroExt.fstHom S S S).toRingHom :=
    RingHom.ext fun x => by simp [epsMul]
  rw [e1, e2] at h2
  rw [← h2]
  simp [spMap]

theorem smT_const (g₀ : Sp S ⟶ G.left) (g' : overAt x0 (DualNumber S) ⟶ G)
    (hg : g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀) (a : S) : smT x0 a g' = g' := by
  apply Over.OverMorphism.ext
  have h1 : (smT x0 a g').left = spMap (epsMul a) ≫ g'.left := rfl
  rw [h1, hg, ← Category.assoc, spMap_comp_spMap]
  congr 2
  exact RingHom.ext fun x => by simp [epsMul]

theorem valR_smT (a : S) (w : overAt x0 (DualNumber S) ⟶ G) (O : G.left.Opens)
    (hw : ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from w.left) ⁻¹ᵁ O) (f : Γ(G.left, O)) :
    (valR (smT x0 a w).left O f).snd = a * (valR w.left O f).snd := by
  have h1 : (smT x0 a w).left = spMap (epsMul a) ≫ w.left := rfl
  rw [h1, valR_spMap_comp _ _ O hw f]
  simp [epsMul]

theorem valR_const_snd (g₀ : Sp S ⟶ G.left) (g' : overAt x0 (DualNumber S) ⟶ G)
    (hg : g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀) (O : G.left.Opens) (hO : ⊤ ≤ g₀ ⁻¹ᵁ O)
    (f : Γ(G.left, O)) : (valR g'.left O f).snd = 0 := by
  rw [hg, valR_spMap_comp _ _ O hO f]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem snd_valR_mul (u v : overAt x0 (DualNumber S) ⟶ G) (hv0 : smT x0 0 v = 1) (O : G.left.Opens)
    (hu : ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from u.left) ⁻¹ᵁ O) (f : Γ(G.left, O)) :
    (valR (u * v).left O f).snd = (valR u.left O f).snd + (valR (smT x0 0 u * v).left O f).snd := by
  have hz : (0 : S →ₗ[S] S) = (0 : S) • (LinearMap.id : S →ₗ[S] S) := by simp
  let P : overAt x0 (TrivSqZeroExt S (S × S)) ⟶ G :=
    (homAt x0 (tm (LinearMap.inl S S S)) ≫ u) * (homAt x0 (tm (LinearMap.inr S S S)) ≫ v)
  have e1 : homAt x0 (tm (LinearMap.fst S S S)) ≫ P = u := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map,
      LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, hz, TrivSqZeroExt.map_id, homAt_id, Category.id_comp]
    change _ * smT x0 0 v = _
    rw [hv0, _root_.mul_one]
  have e2 : homAt x0 (tm (LinearMap.snd S S S)) ≫ P = smT x0 0 u * v := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map,
      LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, hz, TrivSqZeroExt.map_id, homAt_id, Category.id_comp]
    rfl
  have e3 : homAt x0 (tm (LinearMap.coprod LinearMap.id LinearMap.id : S × S →ₗ[S] S)) ≫ P = u * v := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map,
      LinearMap.coprod_inl, LinearMap.coprod_inr, TrivSqZeroExt.map_id, homAt_id, Category.id_comp,
      Category.id_comp]
  have f1 : spMap (tm (LinearMap.fst S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S) ≫ P.left = u.left :=
    congrArg (fun φ => φ.left) e1
  have f2 : spMap (tm (LinearMap.snd S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S) ≫ P.left =
      (smT x0 0 u * v).left :=
    congrArg (fun φ => φ.left) e2
  have f3 : spMap (tm (LinearMap.coprod LinearMap.id LinearMap.id : S × S →ₗ[S] S) :
      TrivSqZeroExt S (S × S) →+* DualNumber S) ≫ P.left = (u * v).left :=
    congrArg (fun φ => φ.left) e3
  have hP : ⊤ ≤ (show Sp (TrivSqZeroExt S (S × S)) ⟶ G.left from P.left) ⁻¹ᵁ O := by
    refine GlobalTheory.TanDeriv.top_le_of_comp
      (tm (LinearMap.fst S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S) ?_ ?_ _ O ?_
    · intro y
      refine ⟨tm (LinearMap.inl S S S) y, ?_⟩
      ext <;> simp
    · intro x hx
      have h1 : x.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hx
      ext <;> simp [h1]
    · exact f1 ▸ hu
  have k1 := valR_spMap_comp (tm (LinearMap.fst S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S) P.left O hP f
  have k2 := valR_spMap_comp (tm (LinearMap.snd S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S) P.left O hP f
  have k3 := valR_spMap_comp (tm (LinearMap.coprod LinearMap.id LinearMap.id : S × S →ₗ[S] S) :
      TrivSqZeroExt S (S × S) →+* DualNumber S) P.left O hP f
  rw [f1] at k1
  rw [f2] at k2
  rw [f3] at k3
  rw [k1, k2, k3]
  simp

theorem top_le_of_smT_zero (g₀ : Sp S ⟶ G.left) (g' : overAt x0 (DualNumber S) ⟶ G)
    (hg : g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀) (O : G.left.Opens) (hO : ⊤ ≤ g₀ ⁻¹ᵁ O)
    (z : overAt x0 (DualNumber S) ⟶ G) (hz : smT x0 0 z = g') :
    ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from z.left) ⁻¹ᵁ O := by
  refine top_le_of_fst z O ?_
  rw [fst_comp_of_smT_zero g₀ g' hg z hz]
  exact hO

theorem snd_sectionValue_translate_list_prod_induction (g₀ : Sp S ⟶ G.left) (g' : overAt x0 (DualNumber S) ⟶ G)
    (hg : g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀) (O : G.left.Opens) (hO : ⊤ ≤ g₀ ⁻¹ᵁ O)
    (f : Γ(G.left, O)) : ∀ (m : ℕ) (y : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (r : Fin m → S),
    (∀ c, smT x0 0 (y c) = 1) →
    smT x0 0 (List.ofFn fun c => smT x0 (r c) (y c)).prod = 1 ∧
    (valR (g' * (List.ofFn fun c => smT x0 (r c) (y c)).prod).left O f).snd =
      ∑ c, r c * (valR (g' * y c).left O f).snd := by
  have hg0 : smT x0 0 g' = g' := smT_const g₀ g' hg 0
  intro m
  induction m with
  | zero =>
    intro y r _
    rw [List.ofFn_zero, List.prod_nil, smT_one', _root_.mul_one, valR_const_snd g₀ g' hg O hO f]
    simp
  | succ n ih =>
    intro y r hy
    obtain ⟨h0, hs⟩ := ih (fun c => y c.succ) (fun c => r c.succ) (fun c => hy c.succ)
    have ha : smT x0 0 (smT x0 (r 0) (y 0)) = 1 := by rw [smT_smT, zero_mul, hy 0]
    rw [List.ofFn_succ, List.prod_cons]
    refine ⟨by rw [smT_mul, ha, h0, _root_.mul_one], ?_⟩
    have hu : smT x0 0 (g' * smT x0 (r 0) (y 0)) = g' := by rw [smT_mul, hg0, ha, _root_.mul_one]
    have hy0 : smT x0 0 (g' * y 0) = g' := by rw [smT_mul, hg0, hy 0, _root_.mul_one]
    have hgy : g' * smT x0 (r 0) (y 0) = smT x0 (r 0) (g' * y 0) := by
      rw [smT_mul, smT_const g₀ g' hg]
    rw [← _root_.mul_assoc, snd_valR_mul _ _ h0 O (top_le_of_smT_zero g₀ g' hg O hO _ hu) f, hu, hs, hgy,
      valR_smT _ _ O (top_le_of_smT_zero g₀ g' hg O hO _ hy0) f, Fin.sum_univ_succ]

theorem snd_valR_translate_prod : ∀ {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (G : Over X0) [GrpObj G]
    (g₀ : Sp S ⟶ G.left) (g' : overAt x0 (DualNumber S) ⟶ G),
    g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀ →
    ∀ {m : ℕ} (y : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (r : Fin m → S), (∀ c, smT x0 0 (y c) = 1) →
    ∀ (O : G.left.Opens) (f : Γ(G.left, O)), ⊤ ≤ g₀ ⁻¹ᵁ O →
    (valR (g' * (List.ofFn fun c => smT x0 (r c) (y c)).prod).left O f).snd =
      ∑ c, r c * (valR (g' * y c).left O f).snd := by
  intro X0 S _ x0 G _ g₀ g' hg m y r hy O f hO
  exact (snd_sectionValue_translate_list_prod_induction g₀ g' hg O hO f m y r hy).2

end GlobalTheory.KSLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanLogDerGerms
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

namespace GlobalTheory.LogKSDiv.LocSpan

theorem deriv_ext {k R A : Type} [CommRing k] [CommRing R] [CommRing A] [Algebra k A] (φ : R →+* A)
    (M : Submonoid R) (hloc : letI := φ.toAlgebra; IsLocalization M A) (D₁ D₂ : Derivation k A A)
    (h : ∀ r, D₁ (φ r) = D₂ (φ r)) : D₁ = D₂ := by
  letI := φ.toAlgebra
  ext y
  obtain ⟨⟨r, t⟩, e⟩ := IsLocalization.surj M y
  have hu : IsUnit (φ t) := IsLocalization.map_units A t
  have e' : y * φ t = φ r := e
  have h1 := congrArg D₁ e'
  have h2 := congrArg D₂ e'
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h1 h2
  rw [h r, h t] at h1
  have : φ t * D₁ y = φ t * D₂ y := by linear_combination h1 - h2
  exact hu.mul_left_cancel this

end GlobalTheory.LogKSDiv.LocSpan

namespace GlobalTheory.LogKSDiv.LocSpan

theorem sum_apply {k R M : Type} [CommRing k] [CommRing R] [AddCommGroup M] [Algebra k R] [Module R M] [Module k M]
    {n : ℕ} (f : Fin n → Derivation k R M) (x : R) : (∑ j, f j) x = ∑ j, f j x := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  rfl

theorem span_eq_top {k R A : Type} [Field k] [CommRing R] [CommRing A] [Algebra k R] [Algebra k A]
    [Algebra.FiniteType k R] (φ : R →+* A) (hk : φ.comp (algebraMap k R) = algebraMap k A)
    (M : Submonoid R) (hloc : letI := φ.toAlgebra; IsLocalization M A) (a : R) (ha : IsUnit (φ a)) {n : ℕ}
    (v : Fin n → Derivation ℤ R R)
    (hlog : ∀ D : Derivation k R R, a • D.restrictScalars ℤ ∈ Submodule.span R (Set.range v))
    (δ : Fin n → Derivation k A A) (hδ : ∀ j r, δ j (φ r) = φ (v j r)) :
    Submodule.span A (Set.range δ) = ⊤ := by
  letI := φ.toAlgebra
  haveI : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq fun c => (congrArg (· c) hk).symm
  haveI : Algebra.FinitePresentation k R := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  rw [Submodule.eq_top_iff']
  intro d
  let g : Derivation k R A := d.compAlgebraMap R
  obtain ⟨h, s, hs⟩ :=
    Module.FinitePresentation.exists_lift_of_isLocalizedModule M (Algebra.linearMap R A) g.liftKaehlerDifferential
  let D' : Derivation k R R := h.compDer (KaehlerDifferential.D k R)
  have hD' : ∀ r, φ (D' r) = φ s * d (φ r) := by
    intro r
    have := congrArg (fun L : Ω[R⁄k] →ₗ[R] A => L (KaehlerDifferential.D k R r)) hs
    simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply, LinearMap.smul_apply,
      Derivation.liftKaehlerDifferential_comp_D] at this
    rw [Submonoid.smul_def, Algebra.smul_def] at this
    exact this
  obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (hlog D')
  have hsu : IsUnit (φ s) := IsLocalization.map_units A s
  have hu : IsUnit (φ a * φ s) := ha.mul hsu
  have key : (φ a * φ s) • d = ∑ j, φ (cf j) • δ j := by
    refine deriv_ext φ M hloc _ _ fun r => ?_
    have e1 := congrArg (fun D : Derivation ℤ R R => φ (D r)) hcf
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [sum_apply, Derivation.coe_smul, Pi.smul_apply, smul_eq_mul, map_sum,
      map_mul, Derivation.coe_restrictScalars] at e1
    simp only [sum_apply, Derivation.coe_smul, Pi.smul_apply, smul_eq_mul, hδ]
    rw [e1, hD']
    ring
  have hmem : (φ a * φ s) • d ∈ Submodule.span A (Set.range δ) := by
    rw [key]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hmem' : ((hu.unit : Aˣ) : A) • d ∈ Submodule.span A (Set.range δ) := by
    rw [hu.unit_spec]
    exact hmem
  have := Submodule.smul_mem _ ((hu.unit⁻¹ : Aˣ) : A) hmem'
  rwa [smul_smul, Units.inv_mul, one_smul] at this

end GlobalTheory.LogKSDiv.LocSpan

namespace GlobalTheory.LogKSDiv.LocSpan

theorem appLE_germ {X S : Scheme.{0}} (f : X ⟶ S) (W : S.Opens) (V T : X.Opens) (hV : V ≤ f ⁻¹ᵁ W)
    (hT : T ≤ f ⁻¹ᵁ W) (x : X) (hxV : x ∈ V) (hxT : x ∈ T) :
    f.appLE W V hV ≫ X.presheaf.germ V x hxV = f.appLE W T hT ≫ X.presheaf.germ T x hxT := by
  rw [← X.presheaf.germ_res (homOfLE (inf_le_left : V ⊓ T ≤ V)) x ⟨hxV, hxT⟩,
    ← X.presheaf.germ_res (homOfLE (inf_le_right : V ⊓ T ≤ T)) x ⟨hxV, hxT⟩,
    Scheme.Hom.appLE_map_assoc, Scheme.Hom.appLE_map_assoc]

theorem appLE_appLE_germ {X Y S : Scheme.{0}} (ι : X ⟶ Y) (s : Y ⟶ S) (W : S.Opens) (U : Y.Opens) (V T : X.Opens)
    (h1 : U ≤ s ⁻¹ᵁ W) (hV : V ≤ ι ⁻¹ᵁ U) (h2 : T ≤ (ι ≫ s) ⁻¹ᵁ W) (x : X) (hxV : x ∈ V) (hxT : x ∈ T) :
    s.appLE W U h1 ≫ ι.appLE U V hV ≫ X.presheaf.germ V x hxV = (ι ≫ s).appLE W T h2 ≫ X.presheaf.germ T x hxT := by
  rw [Scheme.Hom.appLE_comp_appLE_assoc]
  exact appLE_germ _ _ _ _ _ _ _ _ _

end GlobalTheory.LogKSDiv.LocSpan

namespace GlobalTheory.LogKSDiv.LocSpan

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem stalkHom_comp_algX (TF : TorFlag Xo c) (Z : Comp Xo c) (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens)
    (hx : (barComp TF.Y Z).ι x ∈ U.1) :
    (stalkHom TF Z x U hx).comp (algX TF.Y.s U.1) = stalkAlg TF Z x := by
  ext a
  simp only [stalkHom, stalkAlg, algX, RingHom.comp_apply]
  have key : TF.Y.s.appLE ⊤ U.1 (by simp) ≫ (barComp TF.Y Z).ι.app U.1 ≫
      (X₀ TF.Y Z).presheaf.germ ((barComp TF.Y Z).ι ⁻¹ᵁ U.1) x hx =
      (s₀ TF.Y Z).appLE ⊤ ⊤ (by simp) ≫ (X₀ TF.Y Z).presheaf.germ ⊤ x trivial := by
    rw [Scheme.Hom.app_eq_appLE]
    exact appLE_appLE_germ _ _ _ _ _ _ _ _ _ _ _ _
  exact congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom a)) key

end GlobalTheory.LogKSDiv.LocSpan

namespace GlobalTheory.LogKSDiv.LocSpan

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem finiteType_algX (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) : (algX TF.Y.s U.1).FiniteType := by
  haveI := TF.smooth
  haveI : Smooth TF.Y.s := SmoothOfRelativeDimension.smooth Dw.dim _
  have h1 : (TF.Y.s.appLE ⊤ U.1 (by simp)).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType TF.Y.s inferInstance ⟨⊤, isAffineOpen_top _⟩ U _
  exact h1.comp (RingHom.FiniteType.of_surjective _
    (Scheme.ΓSpecIso (CommRingCat.of c.F)).symm.commRingCatIsoToRingEquiv.surjective)

theorem isLocalization_stalkHom (TF : TorFlag Xo c) (Z : Comp Xo c) (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens)
    (hx : (barComp TF.Y Z).ι x ∈ U.1) :
    letI := (stalkHom TF Z x U hx).toAlgebra
    IsLocalization.AtPrime ((X₀ TF.Y Z).presheaf.stalk x) (U.2.primeIdealOf ⟨_, hx⟩).asIdeal := by
  letI := TopCat.Presheaf.algebra_section_stalk TF.Y.X.presheaf (⟨_, hx⟩ : U.1)
  have h1 := U.2.isLocalization_stalk ⟨_, hx⟩
  let e := (asIso ((barComp TF.Y Z).ι.stalkMap x)).commRingCatIsoToRingEquiv
  have h2 := (IsLocalization.isLocalization_iff_of_ringEquiv _ e).1 h1
  have heq : stalkHom TF Z x U hx = e.toRingHom.comp (TF.Y.X.presheaf.germ U.1 _ hx).hom :=
    RingHom.ext fun y => (Scheme.Hom.germ_stalkMap_apply _ _ _ hx y).symm
  rw [heq]
  convert h2

theorem exists_unit (TF : TorFlag Xo c) (Z : Comp Xo c) (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens)
    (hx : (barComp TF.Y Z).ι x ∈ U.1) (hint : x ∈ (j₀ TF.Y Z).opensRange) :
    ∃ a ∈ (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl).ideal U,
      IsUnit (stalkHom TF Z x U hx a) := by
  have hin : (barComp TF.Y Z).ι x ∈ LogKS.interior TF.Y := by
    obtain ⟨y, rfl⟩ := hint
    refine ⟨i₀ TF.Y Z y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← j₀_ι, Scheme.Hom.comp_apply]
  obtain ⟨a, hle, hxa⟩ := U.2.exists_basicOpen_le (V := U.1 ⊓ LogKS.interior TF.Y) ⟨_, hx, hin⟩ hx
  refine ⟨a, ?_, ?_⟩
  · rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
    intro p hp
    by_contra hpa
    have h3 : p ∈ PrimeSpectrum.basicOpen a := hpa
    rw [← U.2.fromSpec_preimage_basicOpen] at h3
    exact hp (hle h3).2
  · have h4 : x ∈ (barComp TF.Y Z).ι ⁻¹ᵁ TF.Y.X.basicOpen a := hxa
    rw [Scheme.preimage_basicOpen] at h4
    exact ((X₀ TF.Y Z).mem_basicOpen _ x hx).1 h4

end GlobalTheory.LogKSDiv.LocSpan

theorem GlobalTheory.LogKSDiv.span_logDer_germs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1) (b : Module.Basis (Fin Dw.dim) Γ(TF.Y.X, U.1) (LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)), letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra; ∀ δ : Fin Dw.dim → Derivation c.F ((X₀ TF.Y Z).presheaf.stalk x) ((X₀ TF.Y Z).presheaf.stalk x), (∀ j r, δ j (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r) = GlobalTheory.LogKSDiv.stalkHom TF Z x U hx ((b j).1 r)) → x ∈ (j₀ TF.Y Z).opensRange → Submodule.span ((X₀ TF.Y Z).presheaf.stalk x) (Set.range δ) = ⊤ := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U _ hx b
  intro δ hδ hint
  letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra
  letI : Algebra c.F Γ(TF.Y.X, U.1) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX TF.Y.s U.1).toAlgebra
  haveI : Algebra.FiniteType c.F Γ(TF.Y.X, U.1) := LocSpan.finiteType_algX TF U
  obtain ⟨a, haI, hau⟩ := LocSpan.exists_unit TF Z x U hx hint
  refine LocSpan.span_eq_top (stalkHom TF Z x U hx) (LocSpan.stalkHom_comp_algX TF Z x U hx) _
    (LocSpan.isLocalization_stalkHom TF Z x U hx) a hau (fun j => (b j).1) ?_ δ hδ
  intro D
  have hmem : a • D.restrictScalars ℤ ∈
      LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U := by
    refine ⟨fun a' => ?_, fun f _ => ?_⟩
    · show a * D (constFn TF.Y.s U.1 a') = 0
      rw [show constFn TF.Y.s U.1 a' = algebraMap c.F _ a' from rfl, D.map_algebraMap, mul_zero]
    · show a * D f ∈ _
      exact Ideal.mul_mem_right _ _ haI
  have h7 := congrArg Subtype.val (b.sum_repr ⟨_, hmem⟩)
  rw [Submodule.coe_sum] at h7
  simp only [Submodule.coe_smul] at h7
  rw [← h7]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecPiDisjointOpenCoverFactors
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SpecPi

theorem specPi_cover : ∀ (R : Type) [CommRing R] (n : ℕ) (D : Fin n → Type) [∀ i, CommRing (D i)] [∀ i, Algebra R (D i)], ∃ V : Fin n → (Sp (∀ i, D i)).Opens, (⨆ i, V i = ⊤) ∧ (Pairwise fun i i' => Disjoint (V i) (V i')) ∧ ∀ i, Nonempty (Over.mk ((V i).ι ≫ spMap (algebraMap R (∀ i, D i))) ≅ Over.mk (spMap (algebraMap R (D i)))) := by
  intro R _ n D _ _
  let S := sigmaSpec (fun i => CommRingCat.of (D i))
  have hS : ∀ i, Sigma.ι (fun i => Spec (CommRingCat.of (D i))) i ≫ S = spMap (Pi.evalRingHom D i) :=
    fun i => ι_sigmaSpec _ i
  have hinv : ∀ y, (inv S) (S y) = y := fun y => by
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
  have hsurj : ∀ x, S ((inv S) x) = x := fun x => by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
  refine ⟨fun i => (spMap (Pi.evalRingHom D i)).opensRange, ?_, ?_, ?_⟩
  · rw [eq_top_iff]
    rintro x -
    have hcov : ∀ y : ↥(∐ fun i => Spec (CommRingCat.of (D i))), ∃ k, ∃ z : Sp (D k),
        (Sigma.ι (fun i => Spec (CommRingCat.of (D i))) k) z = y :=
      fun y => ⟨_, (sigmaOpenCover (fun i => Spec (CommRingCat.of (D i)))).covers y⟩
    obtain ⟨k, z, hz⟩ := hcov ((inv S) x)
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨k, z, ?_⟩
    rw [← hS k, Scheme.Hom.comp_apply, hz, hsurj]
  · intro i j hij
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    rw [← hS, Scheme.Hom.comp_apply] at ha hb
    have e := congrArg (inv S) (ha.trans hb.symm)
    rw [hinv, hinv] at e
    obtain ⟨rfl⟩ := (sigmaι_eq_iff _ _ _ _ _).mp e
    exact absurd rfl hij
  · intro i
    refine ⟨Over.isoMk (spMap (Pi.evalRingHom D i)).isoOpensRange.symm ?_⟩
    simp only [Over.mk_hom, Iso.symm_hom]
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc]
    congr 1
    rw [← Spec.map_comp]
    rfl

end GlobalTheory.SpecPi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreConnected
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits

noncomputable section

namespace GlobalTheory.SpecialConn

theorem range_spec_map_eq {O S : Type} [CommRing O] [IsLocalRing O] [CommRing S] [Nontrivial S] (φ : O →+* S)
    (hφ : ∀ Q : Ideal S, Q.IsPrime → IsLocalRing.maximalIdeal O ≤ Q.comap φ) :
    Set.range (Spec.map (CommRingCat.ofHom φ)) = {IsLocalRing.closedPoint O} := by
  have key : ∀ Q : PrimeSpectrum S, Spec.map (CommRingCat.ofHom φ) Q = IsLocalRing.closedPoint O := by
    intro Q
    refine PrimeSpectrum.ext ?_
    change Q.asIdeal.comap φ = IsLocalRing.maximalIdeal O
    exact le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.comap φ).ne_top) (hφ _ Q.2)
  ext x
  constructor
  · rintro ⟨Q, rfl⟩
    exact key Q
  · rintro rfl
    obtain ⟨M, hM⟩ := Ideal.exists_maximal S
    exact ⟨⟨M, hM.isPrime⟩, key _⟩

theorem range_thickQ (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    Set.range (Spec.map (CommRingCat.ofHom (thickQ O n))) = {IsLocalRing.closedPoint O} := by
  haveI : Nontrivial (O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1)) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal O).ne_top
      (Ideal.pow_le_self (Nat.succ_ne_zero n)))
  refine range_spec_map_eq _ fun Q hQ => ?_
  have h : IsLocalRing.maximalIdeal O ^ (n + 1) ≤ Q.comap (thickQ O n) := fun a ha => by
    change Ideal.Quotient.mk _ a ∈ Q
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha]
    exact Q.zero_mem
  exact (Ideal.IsPrime.comap (thickQ O n)).le_of_pow_le h

theorem range_residue (O : Type) [CommRing O] [IsLocalRing O] :
    Set.range (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) = {IsLocalRing.closedPoint O} := by
  refine range_spec_map_eq _ fun Q hQ a ha => ?_
  change IsLocalRing.residue O a ∈ Q
  rw [(IsLocalRing.residue_eq_zero_iff a).2 ha]
  exact Q.zero_mem

end GlobalTheory.SpecialConn
end
end

