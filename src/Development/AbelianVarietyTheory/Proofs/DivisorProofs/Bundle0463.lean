module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0451
public import GroundTheory.AutomorphicForms.GKModules.Casimir
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
public import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
public import GroundTheory.AutomorphicForms.Bundle0015
public import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberSectionsUniqueDecomposition
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.RelConstThickening

theorem existsUnique_of_isPushout {K : Type} [CommRing K] {A A' : CommRingCat.{0}} (c : K →+* A) (p : A ⟶ A')
    (s : DualNumber K →+* A')
    (H : IsPushout (CommRingCat.ofHom c) (CommRingCat.ofHom (algebraMap K (DualNumber K))) p (CommRingCat.ofHom s))
    (F : A') : ∃! ab : A × A, F = p.hom ab.1 + s DualNumber.eps * p.hom ab.2 := by
  let _ : Algebra K A := c.toAlgebra
  let _ : Algebra A A' := p.hom.toAlgebra
  let _ : Algebra (DualNumber K) A' := s.toAlgebra
  let _ : Algebra K A' := (s.comp (algebraMap K (DualNumber K))).toAlgebra
  have : IsScalarTower K (DualNumber K) A' := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower K A A' := .of_algebraMap_eq fun r => (congrArg (fun q => q.hom r) H.w).symm
  have h : Algebra.IsPushout K A (DualNumber K) A' := CommRingCat.isPushout_iff_isPushout.mp H
  let b : Module.Basis (Fin 2) K (DualNumber K) := Module.Basis.finTwoProd K
  have b0 : b 0 = 1 := Module.Basis.finTwoProd_zero K
  have b1 : b 1 = DualNumber.eps := Module.Basis.finTwoProd_one K
  let B := h.out.basis b
  have B0 : B 0 = 1 := by
    rw [h.out.basis_apply, b0]; exact map_one s
  have B1 : B 1 = s DualNumber.eps := by
    rw [h.out.basis_apply, b1]; rfl
  have key : ∀ x y : A, p.hom x + s DualNumber.eps * p.hom y = B.equivFun.symm ![x, y] := fun x y => by
    rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two, B0, B1, Algebra.smul_def, Algebra.smul_def, _root_.mul_one,
      _root_.mul_comm (s _)]
    rfl
  refine ⟨(B.equivFun F 0, B.equivFun F 1), ?_, fun ab hab => ?_⟩
  · change F = _
    rw [key, LinearEquiv.eq_symm_apply]
    ext i; fin_cases i <;> rfl
  · replace hab : F = _ := hab
    rw [key, LinearEquiv.eq_symm_apply] at hab
    rw [hab]; rfl

def constHom {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  (f.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem res_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (constFn f U a) = constFn f V a := by
  exact congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (f.appLE_map (U := ⊤) (fun _ _ => trivial) (homOfLE h).op)

theorem res_app {X X' : Scheme.{0}} (f : X' ⟶ X) {U V : X.Opens} (h : V ≤ U) (h' : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) (a : Γ(X, U)) :
    (X'.presheaf.map (homOfLE h').op).hom ((f.app U).hom a) = (f.app V).hom ((X.presheaf.map (homOfLE h).op).hom a) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)) :
    (X.presheaf.map (homOfLE h').op).hom ((X.presheaf.map (homOfLE h).op).hom a) =
      (X.presheaf.map (homOfLE (h'.trans h)).op).hom a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem fromSpec_appLE_top {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    (e : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ e = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  exact (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)

theorem existsUnique_affine {X Z P : Scheme.{0}} (U : X.affineOpens) (h : Z ⟶ X)
    (p₁ : P ⟶ Sp (DualNumber Γ(X, U.1))) (p₂ : P ⟶ Z)
    (H : IsPullback p₂ p₁ h (spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) ≫ GlobalTheory.LogKS.chart U))
    {V : Z.Opens} (hV : IsAffineOpen V) (hVU : V ≤ h ⁻¹ᵁ U.1) (F : Γ(P, p₂ ⁻¹ᵁ V)) : ∃! ab : Γ(Z, V) × Γ(Z, V),
      F = (p₂.app V).hom ab.1 + constFn p₁ _ DualNumber.eps * (p₂.app V).hom ab.2 := by
  refine existsUnique_of_isPushout (K := Γ(X, U.1)) (h.appLE U.1 V hVU).hom (p₂.app V) (constHom p₁ (p₂ ⁻¹ᵁ V)) ?_ F
  have e0 : (⊤ : (Spec Γ(X, U.1)).Opens) ≤ U.2.fromSpec ⁻¹ᵁ U.1 := U.2.fromSpec_preimage_self.ge
  have e : (⊤ : (Sp (DualNumber Γ(X, U.1))).Opens) ≤
      (spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) ≫ GlobalTheory.LogKS.chart U) ⁻¹ᵁ U.1 := fun x _ =>
    e0 (Set.mem_univ (spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) x))
  have po := (isIso_pushoutSection_iff H (US := U.1) (UT := ⊤) (UX := V) (UY := p₂ ⁻¹ᵁ V) e hVU
    (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ U.2
      (isAffineOpen_top _) hV)
  refine po.of_iso (Iso.refl _) (Iso.refl _) (Scheme.ΓSpecIso (.of (DualNumber Γ(X, U.1)))) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp
  · have e1 : (spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) ≫ GlobalTheory.LogKS.chart U).appLE U.1 ⊤ e =
        U.2.fromSpec.appLE U.1 ⊤ e0 ≫ (spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1)))).appLE ⊤ ⊤ le_top :=
      (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    have e2 : (spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1)))).appLE ⊤ ⊤ le_top ≫
        (Scheme.ΓSpecIso (.of (DualNumber Γ(X, U.1)))).hom =
        (Scheme.ΓSpecIso (.of Γ(X, U.1))).hom ≫ CommRingCat.ofHom (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) := by
      rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    have e3 := fromSpec_appLE_top U.2 e0
    rw [e1, e3]
    exact (Category.assoc _ _ _).trans
      ((congrArg ((Scheme.ΓSpecIso Γ(X, U.1)).inv ≫ ·) e2).trans (Iso.inv_hom_id_assoc _ _))
  · simp [Scheme.Hom.app_eq_appLE]
  · ext x; simp [constHom]

section Glue

variable {R : Type} [CommRing R] {Y Y' : Scheme.{0}} {π : Y' ⟶ Sp R} {ρ : Y' ⟶ Y} {ε : R}

theorem res_comb {U V : Y.Opens} (h : V ≤ U) (h' : ρ ⁻¹ᵁ V ≤ ρ ⁻¹ᵁ U) (a b : Γ(Y, U)) :
    (Y'.presheaf.map (homOfLE h').op).hom ((ρ.app U).hom a + constFn π _ ε * (ρ.app U).hom b) =
      (ρ.app V).hom ((Y.presheaf.map (homOfLE h).op).hom a) +
        constFn π _ ε * (ρ.app V).hom ((Y.presheaf.map (homOfLE h).op).hom b) := by
  rw [map_add (f := _), map_mul, res_app ρ h, res_app ρ h, res_constFn]

theorem le_iSup_affine (O : Y.Opens) : O ≤ ⨆ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O}, U.1 := fun x hx => by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUO⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx O.isOpen
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hUO⟩, hxU⟩

theorem unique_comb {W : Y.Opens}
    (H : ∀ V : Y.Opens, IsAffineOpen V → V ≤ W → ∀ F : Γ(Y', ρ ⁻¹ᵁ V), ∃! ab : Γ(Y, V) × Γ(Y, V),
      F = (ρ.app V).hom ab.1 + constFn π _ ε * (ρ.app V).hom ab.2)
    {O : Y.Opens} (hO : O ≤ W) {a b a' b' : Γ(Y, O)}
    (h : (ρ.app O).hom a + constFn π _ ε * (ρ.app O).hom b =
      (ρ.app O).hom a' + constFn π _ ε * (ρ.app O).hom b') : a = a' ∧ b = b' := by
  have loc : ∀ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O},
      ((Y.presheaf.map (homOfLE U.2.2).op).hom a, (Y.presheaf.map (homOfLE U.2.2).op).hom b) =
      ((Y.presheaf.map (homOfLE U.2.2).op).hom a', (Y.presheaf.map (homOfLE U.2.2).op).hom b') := fun U => by
    have h' : ρ ⁻¹ᵁ U.1 ≤ ρ ⁻¹ᵁ O := fun x hx => U.2.2 hx
    have e := congrArg (Y'.presheaf.map (homOfLE h').op).hom h
    rw [res_comb U.2.2, res_comb U.2.2] at e
    exact (H _ U.2.1 (U.2.2.trans hO) _).unique rfl e
  exact ⟨Y.sheaf.eq_of_locally_eq' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) a a'
      fun U => congrArg Prod.fst (loc U),
    Y.sheaf.eq_of_locally_eq' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) b b'
      fun U => congrArg Prod.snd (loc U)⟩

theorem existsUnique_comb {W : Y.Opens}
    (H : ∀ V : Y.Opens, IsAffineOpen V → V ≤ W → ∀ F : Γ(Y', ρ ⁻¹ᵁ V), ∃! ab : Γ(Y, V) × Γ(Y, V),
      F = (ρ.app V).hom ab.1 + constFn π _ ε * (ρ.app V).hom ab.2)
    (O : Y.Opens) (hO : O ≤ W)
    (F : Γ(Y', ρ ⁻¹ᵁ O)) : ∃! ab : Γ(Y, O) × Γ(Y, O),
      F = (ρ.app O).hom ab.1 + constFn π _ ε * (ρ.app O).hom ab.2 := by
  have hle : ∀ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O}, ρ ⁻¹ᵁ U.1 ≤ ρ ⁻¹ᵁ O := fun U x hx => U.2.2 hx
  choose ab hab using fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O} =>
    (H _ U.2.1 (U.2.2.trans hO) ((Y'.presheaf.map (homOfLE (hle U)).op).hom F)).exists
  have comp : ∀ U V : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O},
      (Y.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1)).op).hom (ab U).1 =
        (Y.presheaf.map (homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1)).op).hom (ab V).1 ∧
      (Y.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1)).op).hom (ab U).2 =
        (Y.presheaf.map (homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1)).op).hom (ab V).2 := fun U V => by
    apply unique_comb H ((inf_le_left.trans U.2.2).trans hO)
    rw [← res_comb inf_le_left (fun x hx => hx.1), ← res_comb inf_le_right (fun x hx => hx.2), ← hab, ← hab]
    exact (res_res _ _ F).trans (res_res _ _ F).symm
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O)
    (fun U => (ab U).1) (fun U V => (comp U V).1)
  obtain ⟨b, hb, -⟩ := Y.sheaf.existsUnique_gluing' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O)
    (fun U => (ab U).2) (fun U V => (comp U V).2)
  have hF : F = (ρ.app O).hom a + constFn π _ ε * (ρ.app O).hom b := by
    refine Y'.sheaf.eq_of_locally_eq' (fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O} => ρ ⁻¹ᵁ U.1) _
      (fun U => homOfLE (hle U)) (fun x hx => ?_) _ _ fun U => ?_
    · obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 (le_iSup_affine O hx)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨U, hU⟩
    · refine (hab U).trans (Eq.trans ?_ (res_comb U.2.2 (hle U) a b).symm)
      rw [← ha U, ← hb U]
      rfl
  refine ⟨(a, b), hF, fun c hc => ?_⟩
  have := unique_comb H hO (hc.symm.trans hF)
  exact Prod.ext this.1 this.2

end Glue

theorem existsUnique_decomp : ∀ {X Z P : Scheme.{0}} (U : X.affineOpens) (h : Z ⟶ X) (p₁ : P ⟶ Sp (DualNumber Γ(X, U.1))) (p₂ : P ⟶ Z), IsPullback p₂ p₁ h (spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) ≫ GlobalTheory.LogKS.chart U) → ∀ (O : Z.Opens), O ≤ h ⁻¹ᵁ U.1 → ∀ F : Γ(P, p₂ ⁻¹ᵁ O), ∃! ab : Γ(Z, O) × Γ(Z, O), F = (p₂.app O).hom ab.1 + constFn p₁ _ DualNumber.eps * (p₂.app O).hom ab.2 :=
  fun U h p₁ p₂ H O hO F =>
    existsUnique_comb (fun _ hV hVU F => existsUnique_affine U h p₁ p₂ H hV hVU F) O hO F

end GlobalTheory.RelConstThickening
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceFormSkewHermitian
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory.TraceSkew

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

noncomputable abbrev ccHom (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E :=
  (IsCMField.complexConj E).toAlgHom.toRingHom

lemma map_cc_mul {r : ℕ} (A B : Matrix (Fin r) (Fin r) E) :
    (A * B).map cc = A.map cc * B.map cc :=
  Matrix.map_mul (f := ccHom E)

lemma exists_ne_zero_cc_eq_neg : ∃ β : E, β ≠ 0 ∧ cc β = -β := by
  by_contra h
  push_neg at h
  apply IsCMField.complexConj_ne_one E
  refine AlgEquiv.ext fun x => ?_
  have h1 : cc (x - cc x) = -(x - cc x) := by
    simp only [cc, map_sub, IsCMField.complexConj_apply_apply]; ring
  have h2 := h (x - cc x)
  have h3 : x - cc x = 0 := by
    by_contra hne
    exact h2 hne h1
  have : cc x = x := by linear_combination -h3
  simpa [cc] using this

lemma herm_eq_dot {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G x y = x ⬝ᵥ (G *ᵥ fun b => cc (y b)) := by
  simp [herm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

lemma form_skew_of_matrix {r : ℕ} (G Y : Matrix (Fin r) (Fin r) E)
    (h : Yᵀ * G + G * Y.map cc = 0) (u w : Fin r → E) :
    herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0 := by
  have hc : (fun b => cc ((Y *ᵥ w) b)) = Y.map cc *ᵥ (fun b => cc (w b)) := by
    funext b
    set_option synthInstance.maxHeartbeats 100000 in
      simp [mulVec, dotProduct, cc, map_sum, map_mul]
  rw [herm_eq_dot, herm_eq_dot, hc, mulVec_mulVec, ← vecMul_transpose, ← dotProduct_mulVec,
    mulVec_mulVec, ← dotProduct_add, ← add_mulVec, h, zero_mulVec, dotProduct_zero]

end GlobalTheory.TraceSkew

namespace GlobalTheory.TraceSkew

theorem traceForm_nondegenerate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (X : Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → X.trace = 0 → (∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) → (∀ Y : Matrix (Fin r) (Fin r) E, Y.trace = 0 → (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) → (X * Y).trace = 0) → X = 0 := by
  intro E _ _ _ r G X hG hdet htr _hX hY
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  · subst hr0
    ext i
    exact i.elim0
  have hr : (r : E) ≠ 0 := Nat.cast_ne_zero.mpr hr0.ne'
  have hGu : IsUnit G.det := isUnit_iff_ne_zero.mpr hdet
  have hGTu : IsUnit Gᵀ.det := by rw [det_transpose]; exact hGu
  set Q : Matrix (Fin r) (Fin r) E := (Gᵀ)⁻¹ with hQdef
  have hQT : Qᵀ * G = 1 := by
    rw [hQdef, transpose_nonsing_inv, transpose_transpose]
    exact nonsing_inv_mul G hGu
  have hQG : Q * Gᵀ = 1 := nonsing_inv_mul _ hGTu
  have hGmap : Gᵀ.map cc = G := by
    ext a b
    simp only [map_apply, transpose_apply]
    exact hG b a
  have hQmap : G * Q.map cc = 1 := by
    have h1 : Q.map cc * G = 1 := by
      rw [← hGmap, ← map_cc_mul, hQG]
      ext a b
      simp [map_apply, Matrix.one_apply, cc]
    exact mul_eq_one_comm.mp h1

  have hskew : ∀ K : Matrix (Fin r) (Fin r) E, Kᵀ + K.map cc = 0 →
      (Q * K)ᵀ * G + G * (Q * K).map cc = 0 := by
    intro K hK
    rw [transpose_mul, map_cc_mul, Matrix.mul_assoc, hQT, Matrix.mul_one, ← Matrix.mul_assoc,
      hQmap, Matrix.one_mul]
    exact hK

  have htrskew : ∀ Y : Matrix (Fin r) (Fin r) E, Yᵀ * G + G * Y.map cc = 0 →
      cc Y.trace = -Y.trace := by
    intro Y hY'
    have h0 : G * Y.map cc = -(Yᵀ * G) := eq_neg_of_add_eq_zero_right hY'
    have h1 : Y.map cc = -(G⁻¹ * (Yᵀ * G)) := by
      calc Y.map cc = G⁻¹ * (G * Y.map cc) := by
            rw [← Matrix.mul_assoc, nonsing_inv_mul G hGu, Matrix.one_mul]
        _ = -(G⁻¹ * (Yᵀ * G)) := by rw [h0, Matrix.mul_neg]
    have h2 : (Y.map cc).trace = cc Y.trace := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [trace, cc, map_sum]
    rw [← h2, h1, trace_neg, trace_mul_comm, Matrix.mul_assoc, mul_nonsing_inv G hGu,
      Matrix.mul_one, trace_transpose]

  have hXY : ∀ Y : Matrix (Fin r) (Fin r) E, Yᵀ * G + G * Y.map cc = 0 → (X * Y).trace = 0 := by
    intro Y hY'
    set c : E := Y.trace / r with hcdef
    have hc : cc c = -c := by
      have : cc (r : E) = r := map_natCast (ccHom E) r
      rw [hcdef, show cc (Y.trace / r) = cc Y.trace / cc (r : E) from map_div₀ (ccHom E) _ _,
        this, htrskew Y hY', neg_div]
    have hmap1 : (c • (1 : Matrix (Fin r) (Fin r) E)).map cc = -(c • 1) := by
      ext a b
      by_cases hab : a = b
      · subst b
        simp [Matrix.one_apply, hc]
      · simp [Matrix.one_apply, hab, cc]
    have hmapY : (Y - c • (1 : Matrix (Fin r) (Fin r) E)).map cc = Y.map cc - (c • (1 : Matrix (Fin r) (Fin r) E)).map cc := by
      ext a b
      simp [cc]
    have hs : (Y - c • (1 : Matrix (Fin r) (Fin r) E))ᵀ * G + G * (Y - c • (1 : Matrix (Fin r) (Fin r) E)).map cc = 0 := by
      rw [hmapY, hmap1, transpose_sub, transpose_smul, transpose_one, Matrix.sub_mul,
        Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_neg, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one, ← hY']
      abel
    have ht : (Y - c • (1 : Matrix (Fin r) (Fin r) E)).trace = 0 := by
      rw [trace_sub, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul, hcdef,
        div_mul_cancel₀ _ hr, sub_self]
    have h := hY (Y - c • (1 : Matrix (Fin r) (Fin r) E)) ht (form_skew_of_matrix G _ hs)
    rw [Matrix.mul_sub, trace_sub, Matrix.mul_smul, Matrix.mul_one, trace_smul, htr,
      smul_zero, sub_zero] at h
    exact h

  obtain ⟨β, hβ0, hβ⟩ := exists_ne_zero_cc_eq_neg (E := E)
  have hβ' : IsCMField.complexConj E β = -β := hβ
  have hall : ∀ K : Matrix (Fin r) (Fin r) E, (X * Q * K).trace = 0 := by
    intro K
    let A : Matrix (Fin r) (Fin r) E := of fun i j => (K i j - cc (K j i)) / 2
    let B : Matrix (Fin r) (Fin r) E := of fun i j => (K i j + cc (K j i)) / (2 * β)
    have hA : Aᵀ + A.map cc = 0 := by
      ext i j
      simp only [A, Matrix.add_apply, transpose_apply, map_apply, of_apply, Matrix.zero_apply, cc, map_sub,
        map_div₀, map_ofNat, IsCMField.complexConj_apply_apply]
      ring
    have hB : Bᵀ + B.map cc = 0 := by
      ext i j
      simp only [B, Matrix.add_apply, transpose_apply, map_apply, of_apply, Matrix.zero_apply, cc, map_add (f := _),
        map_div₀, map_mul, map_ofNat, IsCMField.complexConj_apply_apply, hβ']
      field_simp
      ring
    have hK : K = A + β • B := by
      ext i j
      simp only [A, B, Matrix.add_apply, Matrix.smul_apply, of_apply, smul_eq_mul]
      field_simp
      ring
    rw [Matrix.mul_assoc, hK, Matrix.mul_add, Matrix.mul_add, trace_add, Matrix.mul_smul,
      Matrix.mul_smul, trace_smul, hXY _ (hskew A hA), hXY _ (hskew B hB), smul_zero, add_zero]
  have hXQ : X * Q = 0 := by
    rw [ext_iff_trace_mul_right]
    intro K
    rw [hall K, Matrix.zero_mul, trace_zero]
  calc X = X * Q * Gᵀ := by rw [Matrix.mul_assoc, hQG, Matrix.mul_one]
    _ = 0 := by rw [hXQ, Matrix.zero_mul]

end GlobalTheory.TraceSkew
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalencePullbackIntegralAffine
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem eqv_pullback_integral_affine : ∀ (R : Type) [CommRing R] (F : Shv R) (A C : Type) [CommRing A] [CommRing C] [Algebra A C],
    (∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B],
      Eqv R (spMap (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B).toRingHom) F) →
    ∀ (Z Z' : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of A)) (h' : Z' ⟶ Spec (CommRingCat.of C)) (φ : Z' ⟶ Z),
    IsIntegralHom h → IsPullback φ h' h (Spec.map (CommRingCat.ofHom (algebraMap A C))) → Eqv R (sch.map φ) F := by
  intro R _ F A C _ _ _ hB Z Z' h h' φ hh hP
  have E := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  haveI : IsAffine Z := isAffine_of_isAffineHom h

  set f : CommRingCat.of A ⟶ Γ(Z, ⊤) := Spec.preimage (Z.isoSpec.inv ≫ h) with hf
  have hfh : Z.isoSpec.hom ≫ Spec.map f = h := by
    rw [hf, Spec.map_preimage, Iso.hom_inv_id_assoc]
  have hint : IsIntegralHom (Spec.map f) := by
    have : Spec.map f = Z.isoSpec.inv ≫ h := by rw [hf, Spec.map_preimage]
    rw [this]; infer_instance
  letI : Algebra A Γ(Z, ⊤) := f.hom.toAlgebra
  haveI : Algebra.IsIntegral A Γ(Z, ⊤) := ⟨IsIntegralHom.SpecMap_iff.mp hint⟩
  have hsq := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct A C Γ(Z, ⊤))).flip
  have hsq' : IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : Γ(Z, ⊤) →ₐ[A] C ⊗[A] Γ(Z, ⊤)).toRingHom) ≫ Z.isoSpec.inv)
      (Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)) h
      (Spec.map (CommRingCat.ofHom (algebraMap A C))) := by
    have hr : IsPullback Z.isoSpec.inv (Spec.map f) h (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [← hfh, Iso.inv_hom_id_assoc, Category.comp_id]⟩
    simpa using IsPullback.paste_horiz hsq hr
  let e := IsPullback.isoIsPullback _ _ hP hsq'
  have he : φ = e.hom ≫ (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : Γ(Z, ⊤) →ₐ[A] C ⊗[A] Γ(Z, ⊤)).toRingHom) ≫ Z.isoSpec.inv) :=
    (IsPullback.isoIsPullback_hom_fst _ _ hP hsq').symm
  rw [he, Functor.map_comp, Functor.map_comp]
  refine (E.2.1 _ _ _ _ _).1 (E.1 _ _ _ inferInstance) ((E.2.1 _ _ _ _ _).1 (hB Γ(Z, ⊤)) (E.1 _ _ _ inferInstance))

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyCoprodSchemesBijectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSpaceCohomology_coprod_schemes_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U j) → ∀ n : ℤ, Function.Bijective (fun (x : H R (sch.obj U) F n) (i : ι) => pull R (sch.map (j i)) F n x) := by
  first | (exact @GlobalTheory.coh_coprod_bijective) | (exact GlobalTheory.coh_coprod_bijective) | (intros; apply GlobalTheory.coh_coprod_bijective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalRingPointDualNumberSndLinearDerivationStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TangentOrigin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evalRingPoint_dualNumber_snd_linear_derivation : ∀ {X : Scheme.{0}} {S K : Type} [CommRing S] [Field K] (G : Sp S ⟶ X) (ψ : S →+* K) {ι : Type} [Fintype ι] (θc : ι → (S →+* DualNumber K)) (θ : S →+* DualNumber K) (m : ι → K), (∀ a s, (θc a s).fst = ψ s) → (∀ s, (θ s).fst = ψ s) → (∀ s, (θ s).snd = ∑ a, m a * (θc a s).snd) → ∀ (O : X.Opens) (f : Γ(X, O)) (h : ⊤ ≤ (spMap θ ≫ G) ⁻¹ᵁ O) (h' : ∀ a, ⊤ ≤ (spMap (θc a) ≫ G) ⁻¹ᵁ O), (evalPt (spMap θ ≫ G) O h f).snd = ∑ a, m a * (evalPt (spMap (θc a) ≫ G) O (h' a) f).snd := by
  first | exact @GlobalTheory.DualEval.evalPt_snd_sum | exact GlobalTheory.DualEval.evalPt_snd_sum | (intros; apply GlobalTheory.DualEval.evalPt_snd_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomLiftResiduePointFiniteFlat
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.ResiduePointLift

theorem exists_algHom_lift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O →
    ∀ (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Flat O A]
    (c : A →ₐ[O] IsLocalRing.ResidueField O), ∃ x : A →ₐ[O] O, ∀ a, IsLocalRing.residue O (x a) = c a := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ hv A _ _ _ _ c
  haveI : IsFractionRing O C := hv.isFractionRing
  haveI : IsIntegrallyClosed O := hv.isIntegrallyClosed
  obtain ⟨ψ, h1, h2⟩ := GlobalTheory.UT.ExactTerm.exists_ringHom_lift C (c : A →+* IsLocalRing.ResidueField O)
    (RingHom.ext fun o => by simp [IsLocalRing.ResidueField.algebraMap_eq])
  refine ⟨{ ψ with commutes' := fun o => RingHom.congr_fun h1 o }, fun a => RingHom.congr_fun h2 a⟩

end GlobalTheory.ResiduePointLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoinducedSheafInjectiveResolutionFreeExactStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coinducedSheaf_injectiveResolution_freeExact : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (J : Shv R) [Injective J], (∀ P : PSh, Module.Injective (ULift.{1} R) ((free R).obj P ⟶ J)) → ∃ (C : Cx R) (ε : sgl ((restr φ).obj ((coind φ).obj J)) ⟶ C), C.IsStrictlyGE 0 ∧ (∀ t, Injective (C.X t)) ∧ QuasiIso ε ∧ ∀ (P : PSh) (n : ℤ), 0 < n → Subsingleton (CohomologyClass (sgl ((free R).obj P)) C n) := by
  first | (exact @GlobalTheory.EtC.coindRes_exists) | (exact GlobalTheory.EtC.coindRes_exists) | (intros; apply GlobalTheory.EtC.coindRes_exists  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInteriorEstimateDerivWordPolyLaplacianStatement
section
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_interior_estimate_deriv_word_polyLaplacian : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∃ Kc : Set G, IsCompact Kc ∧ ∀ l : List 𝔤, ∃ C : ℝ, 0 ≤ C ∧ ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P f = 0 → ∀ (g : G) (M : ℝ), (∀ y ∈ Kc, ‖(f : G → ℂ) (g * y)‖ ≤ M) → ‖l.foldr h.rightDeriv (f : G → ℂ) g‖ ≤ C * M := by
  first | exact @GlobalTheory.interior_word_bound | exact GlobalTheory.interior_word_bound | (intros; apply GlobalTheory.interior_word_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRadiusMoebiusPerturbationUpperHalfPlane
section
namespace GlobalTheory.HilbFam

theorem exists_radius_moebius_perturbation :
    ∀ (τ c t : ℂ), 0 < τ.im → ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r →
      1 / 2 ≤ ‖1 + z * c‖ ∧ τ.im / 2 ≤ (τ + t * z / (1 + z * c)).im := by
  intro τ c t hτ
  have h1 : ContinuousAt (fun z : ℂ => ‖1 + z * c‖) 0 := by fun_prop
  have h2' : ContinuousAt (fun z : ℂ => τ + t * z / (1 + z * c)) 0 := by
    refine continuousAt_const.add (ContinuousAt.div₀ (by fun_prop) (by fun_prop) (by simp))
  have h2 : ContinuousAt (fun z : ℂ => (τ + t * z / (1 + z * c)).im) 0 :=
    Complex.continuous_im.continuousAt.comp h2'
  have e1 : ∀ᶠ z in nhds (0 : ℂ), (1 / 2 : ℝ) < ‖1 + z * c‖ :=
    h1.eventually (lt_mem_nhds (by norm_num))
  have e2 : ∀ᶠ z in nhds (0 : ℂ), τ.im / 2 < (τ + t * z / (1 + z * c)).im :=
    h2.eventually (lt_mem_nhds (by simp; linarith))
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff.1 (e1.and e2)
  refine ⟨r, hr, fun z hz => ?_⟩
  have := h (y := z) (by simpa using hz)
  exact ⟨this.1.le, this.2.le⟩

end GlobalTheory.HilbFam
end

