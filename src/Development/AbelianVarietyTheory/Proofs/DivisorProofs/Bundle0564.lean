module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0541
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0548
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0546

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCommOfIrreducibleMultiplicityLeOne
section
noncomputable section

namespace GlobalTheory.FinGL.LeviWh

open GlobalTheory.FinGL Formalism.L2.DIV Module

section
variable {H : Type} [Group H] (U : Subgroup H) [Fintype U] (χ : H → ℂ)

def heckeIdem {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ H V) : Module.End ℂ V :=
  ((Fintype.card U : ℂ))⁻¹ • ∑ u : U, χ (u : H)⁻¹ • τ (u : H)

theorem heckeIdem_apply {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ H V) (v : V) :
    heckeIdem U χ τ v = ((Fintype.card U : ℂ))⁻¹ • ∑ u : U, χ (u : H)⁻¹ • τ (u : H) v := by
  simp [heckeIdem, LinearMap.sum_apply]

theorem heckeIdem_mem (hm : ∀ x ∈ U, ∀ y ∈ U, χ (x * y) = χ x * χ y)
    {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ H V) (v : V) :
    heckeIdem U χ τ v ∈ eig τ (U : Set H) χ := by
  rw [heckeIdem_apply]
  refine Submodule.smul_mem _ _ ?_
  rw [mem_eig]
  intro g hg
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨g, hg⟩ : U)) _ _ ?_
  intro u
  have h1 : χ (u : H)⁻¹ = χ g * χ (g * u)⁻¹ := by
    rw [← hm (g) hg _ (U.inv_mem (U.mul_mem hg u.2))]
    have h2 := hm _ (U.inv_mem (U.mul_mem hg u.2)) g hg
    have h3 := hm (g) hg _ (U.inv_mem (U.mul_mem hg u.2))
    rw [h3, mul_comm (χ g), ← h2]
    simp
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_smul, smul_smul, map_mul, h1]
  rfl

theorem heckeIdem_of_mem (hm : ∀ x ∈ U, ∀ y ∈ U, χ (x * y) = χ x * χ y) (h1 : χ 1 = 1)
    {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ H V) (v : V)
    (hv : v ∈ eig τ (U : Set H) χ) : heckeIdem U χ τ v = v := by
  rw [heckeIdem_apply]
  rw [mem_eig] at hv
  have : ∀ u : U, χ (u : H)⁻¹ • τ (u : H) v = v := by
    intro u
    rw [hv u u.2, smul_smul, ← hm _ (U.inv_mem u.2) _ u.2, inv_mul_cancel, h1, one_smul]
  simp only [this, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_smul]

theorem heckeIdem_sub {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ H V)
    (W : Subrepresentation τ) (w : W.toSubmodule) :
    ((heckeIdem U χ W.toRepresentation w : W.toSubmodule) : V) = heckeIdem U χ τ w := by
  rw [heckeIdem_apply, heckeIdem_apply]
  simp [Subrepresentation.toRepresentation]

theorem heckeIdem_comm_of_le_one (hm : ∀ x ∈ U, ∀ y ∈ U, χ (x * y) = χ x * χ y)
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ H V)
    (hr : finrank ℂ (eig τ (U : Set H) χ) ≤ 1) (g h : H) (v : V) :
    heckeIdem U χ τ (τ g (heckeIdem U χ τ (τ h (heckeIdem U χ τ v)))) =
      heckeIdem U χ τ (τ h (heckeIdem U χ τ (τ g (heckeIdem U χ τ v)))) := by
  obtain ⟨w0, hw0⟩ := finrank_le_one_iff.mp hr
  have key : ∀ x, ∃ c : ℂ, heckeIdem U χ τ x = c • (w0 : V) := by
    intro x
    obtain ⟨c, hc⟩ := hw0 ⟨_, heckeIdem_mem U χ hm τ x⟩
    exact ⟨c, by simpa using (congrArg Subtype.val hc).symm⟩
  obtain ⟨c, hc⟩ := key v
  obtain ⟨a, ha⟩ := key (τ g w0)
  obtain ⟨b, hb⟩ := key (τ h w0)
  simp only [hc, map_smul, ha, hb, smul_smul]
  congr 1
  ring

theorem heckeIdem_comm [Finite H] (hm : ∀ x ∈ U, ∀ y ∈ U, χ (x * y) = χ x * χ y)
    (hirr : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ H W),
      τ.IsIrreducible → finrank ℂ (eig τ (U : Set H) χ) ≤ 1) (g h : H) (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ H V),
      finrank ℂ V = n → ∀ v : V,
    heckeIdem U χ τ (τ g (heckeIdem U χ τ (τ h (heckeIdem U χ τ v)))) =
      heckeIdem U χ τ (τ h (heckeIdem U χ τ (τ g (heckeIdem U χ τ v)))) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ τ hn v
    by_cases hi : τ.IsIrreducible
    · exact heckeIdem_comm_of_le_one U χ hm τ (hirr V τ hi) g h v
    rcases subsingleton_or_nontrivial V with hs | hs
    · exact Subsingleton.elim _ _
    have hex : ∃ W : Subrepresentation τ, W ≠ ⊥ ∧ W ≠ ⊤ := by
      by_contra hc
      push Not at hc
      apply hi
      haveI : Nontrivial (Subrepresentation τ) := ⟨⊥, ⊤, fun e => by
        have := congrArg Subrepresentation.toSubmodule e
        exact (bot_ne_top : (⊥ : Submodule ℂ V) ≠ ⊤) this⟩
      exact ⟨fun W => by
        by_cases hW : W = ⊥
        · exact Or.inl hW
        · exact Or.inr (hc W hW)⟩
    obtain ⟨W, hb, ht⟩ := hex
    haveI : NeZero (Nat.card H : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
    have hss : τ.IsSemisimpleRepresentation := inferInstance
    obtain ⟨W', hW'⟩ := hss.exists_isCompl W
    have ht' : W' ≠ ⊤ := by
      rintro rfl
      exact hb (by simpa using hW'.disjoint)
    have sub : ∀ X : Subrepresentation τ, X ≠ ⊤ → ∀ v ∈ X.toSubmodule,
        heckeIdem U χ τ (τ g (heckeIdem U χ τ (τ h (heckeIdem U χ τ v)))) =
      heckeIdem U χ τ (τ h (heckeIdem U χ τ (τ g (heckeIdem U χ τ v)))) := by
      intro X hX v hv
      have hlt : finrank ℂ X.toSubmodule < n := by
        rw [← hn]
        refine Submodule.finrank_lt ?_
        intro e
        exact hX (Subrepresentation.toSubmodule_injective e)
      have := congrArg Subtype.val (ih _ hlt X.toSubmodule X.toRepresentation rfl ⟨v, hv⟩)
      have hτ : ∀ (k : H) (x : X.toSubmodule), ((X.toRepresentation k x : X.toSubmodule) : V) = τ k x :=
        fun _ _ => rfl
      simpa only [heckeIdem_sub, hτ] using this
    have hsup : W.toSubmodule ⊔ W'.toSubmodule = ⊤ :=
      congrArg Subrepresentation.toSubmodule hW'.sup_eq_top
    have hv : v ∈ W.toSubmodule ⊔ W'.toSubmodule := hsup ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb', rfl⟩ := Submodule.mem_sup.mp hv
    simp only [map_add (f := _), sub W ht a ha, sub W' ht' b hb']

end

theorem exists_idem_hecke_comm : ∀ (H : Type) [Group H] [Finite H] (U : Subgroup H) (χ : H → ℂ), (∀ x ∈ U, ∀ y ∈ U, χ (x * y) = χ x * χ y) → χ 1 = 1 → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ H W), τ.IsIrreducible → finrank ℂ (eig τ (U : Set H) χ) ≤ 1) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ H V), ∃ e : Module.End ℂ V, e * e = e ∧ (∀ v ∈ eig τ (U : Set H) χ, e v = v) ∧ (∀ T : Module.End ℂ V, (∀ g, Commute T (τ g)) → Commute T e) ∧ ∀ g h : H, e * τ g * e * τ h * e = e * τ h * e * τ g * e := by
  intro H _ _ U χ hm h1 hirr V _ _ _ τ
  letI : Fintype U := Fintype.ofFinite U
  refine ⟨heckeIdem U χ τ, ?_, heckeIdem_of_mem U χ hm h1 τ, ?_, ?_⟩
  · ext v
    exact heckeIdem_of_mem U χ hm h1 τ _ (heckeIdem_mem U χ hm τ v)
  · intro T hT
    exact Commute.smul_right (Commute.sum_right _ _ _ fun u _ => Commute.smul_right (hT _) _) _
  · intro g h
    ext v
    exact heckeIdem_comm U χ hm hirr g h _ V τ rfl v

end GlobalTheory.FinGL.LeviWh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTnScalarUniformiserSingleTranslation
section
open NumberField IsDedekindDomain

namespace GlobalTheory.LFun

theorem tn_single (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V)
    (ϖ : w.adicCompletion E) (hϖ : Formalism.UG.IsUnifV E w ϖ) :
    ∀ x ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL w (n := n)), ∃ g,
      GlobalTheory.LFun.heckeVec ρ (GlobalTheory.LFun.KGL w (n := n)) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ n) x = ρ g x := by
  classical
  intro x hx
  have h0 : ϖ ≠ 0 := Formalism.UG.P.tjcosets_ne_zero w ϖ hϖ
  set g := Formalism.UG.P.tjcosets_dG n n ϖ h0 with hg
  have hdiag : Formalism.UG.diagJ n ϖ n = ϖ • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    unfold Formalism.UG.diagJ
    ext i j
    by_cases h : i = j
    · subst h; simp [i.2]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  have hcomm : ∀ a : GL (Fin n) (w.adicCompletion E), g * a = a * g := fun a => by
    ext : 1
    rw [Units.val_mul, Units.val_mul, hg, Formalism.UG.P.tjcosets_dG_val, hdiag]
    simp
  have hT : Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ n = Formalism.UG.dosetInd ℂ (GlobalTheory.LFun.KGL w (n := n)) g := by
    unfold Formalism.UG.Tj Formalism.UG.dosetInd
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
    constructor
    · rintro ⟨a, ha, b, hb, e⟩
      exact ⟨a, ha, b, hb, Units.ext (by rw [Units.val_mul, Units.val_mul, hg, Formalism.UG.P.tjcosets_dG_val]; exact e)⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b, hb, by rw [Units.val_mul, Units.val_mul, hg, Formalism.UG.P.tjcosets_dG_val]⟩
  refine ⟨g, ?_⟩
  rw [hT, GlobalTheory.LFun.heckeVec_dosetInd hx (R := {g})]
  · simp
  · intro γ hγ
    rw [Finset.mem_singleton.1 hγ]
    exact DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, 1, one_mem _, by simp⟩
  · intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hy
    refine ⟨g, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
    have : g⁻¹ * (a * g * b) = a * b := by
      rw [← hcomm a]; group
    rw [this]
    exact (GlobalTheory.LFun.KGL w (n := n)).mul_mem ha hb

end GlobalTheory.LFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomDiffUnitSpecialises
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem hom_diff_unit_specialises : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (u v : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → IsMonHom u → IsMonHom v → ∀ t s : S, s ∈ closure {t} → (∀ x : A.left, A.hom x = t → (u * v⁻¹).left x = (η[B]).left t) → ∀ x : A.left, A.hom x = s → (u * v⁻¹).left x = (η[B]).left s := by
  intro S A B _ _ _ _ u v hA hB hu hv t s hst H x hx
  haveI := hA.smooth
  haveI := hB.proper
  have hη : (η[B]).left ≫ B.hom = 𝟙 S := by simpa using Over.w (η[B])
  have hid : IsClosedImmersion (𝟙 S) := inferInstance
  haveI : IsClosedImmersion ((η[B]).left ≫ B.hom) := by rw [hη]; exact hid
  haveI : IsClosedImmersion (η[B]).left := IsClosedImmersion.of_comp _ B.hom
  have hF : IsClosed ((u * v⁻¹).left ⁻¹' Set.range (η[B]).left) :=
    (η[B]).left.isClosedEmbedding.isClosed_range.preimage (u * v⁻¹).left.continuous
  have hcl : x ∈ closure (A.hom ⁻¹' {t}) := by
    rw [mem_closure_iff]
    intro U hU hxU
    have hO : IsOpen (A.hom '' U) := A.hom.isOpenMap U hU
    obtain ⟨_, ⟨y, hyU, rfl⟩, hyt⟩ := mem_closure_iff.mp hst _ hO ⟨x, hxU, hx⟩
    exact ⟨y, hyU, hyt⟩
  have hmem : x ∈ (u * v⁻¹).left ⁻¹' Set.range (η[B]).left :=
    closure_minimal (fun z (hz : z ∈ A.hom ⁻¹' {t}) =>
      (⟨t, (H z hz).symm⟩ : (u * v⁻¹).left z ∈ Set.range (η[B]).left)) hF hcl
  obtain ⟨y, hy⟩ := hmem
  have hys : y = s := by
    have e1 := congrArg B.hom hy
    rw [← Scheme.Hom.comp_apply, hη, ← Scheme.Hom.comp_apply, Over.w] at e1
    simpa [hx] using e1
  subst hys
  exact hy.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperH2GeneratedByCups
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh.SpanCup

theorem sum_append {R M N P : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (B : M →ₗ[R] N →ₗ[R] P) {n m : ℕ} (a : Fin n → M) (b : Fin n → N)
    (a' : Fin m → M) (b' : Fin m → N) :
    ∑ k, B (a k) (b k) + ∑ k, B (a' k) (b' k) = ∑ k, B (Fin.append a a' k) (Fin.append b b' k) := by
  rw [Fin.sum_univ_add]; simp [Fin.append_left, Fin.append_right]

theorem exists_sum_ιMulti {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (w : ⋀[R]^2 M) :
    ∃ (n : ℕ) (x y : Fin n → M), w = ∑ k, exteriorPower.ιMulti R 2 ![x k, y k] := by
  have hw : w ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2 (M := M))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hw using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨v, rfl⟩ := hv
    refine ⟨1, fun _ ↦ v 0, fun _ ↦ v 1, ?_⟩
    rw [Fin.sum_univ_one]
    congr 1
    ext i; fin_cases i <;> rfl
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨n, x, y, rfl⟩ := hu
    obtain ⟨m, x', y', rfl⟩ := hv
    refine ⟨n + m, Fin.append x x', Fin.append y y', ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
  | smul r v _ hv =>
    obtain ⟨n, x, y, rfl⟩ := hv
    refine ⟨n, fun k ↦ r • x k, y, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have e : (![r • x k, y k] : Fin 2 → M) = Function.update ![x k, y k] 0 (r • ![x k, y k] 0) := by
      ext i; fin_cases i <;> simp
    rw [e, AlternatingMap.map_update_smul, Function.update_eq_self]

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def fn2 : cechDeRhamTotalCocyclesTwo F →ₗ[R] Z2 F where
  toFun c := ⟨c.1.1, (mem_cechDeRhamTotalCocyclesTwo_iff.1 c.2).1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cechDeRhamFunctionPart_cup_eq_cup (a b : cechDeRhamTotalCocyclesOne F) : fn2 F (cupZZ F a b) = cupZ F (cechDeRhamTotalCocyclesOne.fn F a) (cechDeRhamTotalCocyclesOne.fn F b) := rfl

end GlobalTheory.AbCoh.SpanCup


open GlobalTheory.AbCoh.SpanCup in
theorem GlobalTheory.AbCoh.hyp2_eq_sum_cupHyp : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → Closed1 F = ⊤ → Function.Surjective (toO F) →
    WedgeO F → ∀ z : Hyp2 F, ∃ (n : ℕ) (a b : Fin n → Hyp1 F), z = ∑ k, cupHyp F (a k) (b k) := by
  intro R _ C _ F hfr h0 hc hsurj hw z
  obtain ⟨c, rfl⟩ := Hyp2.mk_surjective F z
  obtain ⟨e, he⟩ := hw
  obtain ⟨n, x, y, hxy⟩ := exists_sum_ιMulti (e.symm (H2.mk F (fn2 F c)))
  have hrep : ∀ u : H1 F, ∃ p : cechDeRhamTotalCocyclesOne F, toO F (Hyp1.mk F p) = u := fun u ↦ by
    obtain ⟨q, hq⟩ := hsurj u
    obtain ⟨p, rfl⟩ := Hyp1.mk_surjective F q
    exact ⟨p, hq⟩
  choose p hp using hrep
  have hcls : H2.mk F (fn2 F c) = ∑ k, cup F (x k) (y k) := by
    have h := congrArg e hxy
    rw [LinearEquiv.apply_symm_apply] at h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h, map_sum]
    simp only [he]
  obtain ⟨c', hc'⟩ : ∃ c' : cechDeRhamTotalCocyclesTwo F, c' = c - ∑ k, cupZZ F (p (x k)) (p (y k)) := ⟨_, rfl⟩
  have hfn : ∃ f, d1 F f = c'.1.1 := by
    have h : H2.mk F (fn2 F c') = 0 := by
      rw [hc']
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sub, map_sum]
      rw [hcls, sub_eq_zero]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [cechDeRhamFunctionPart_cup_eq_cup, ← cup_mk, ← toO_mk, ← toO_mk, hp, hp]
    exact H2.mk_eq_zero.1 h
  obtain ⟨m, a, w, hm⟩ := _root_.GlobalTheory.AbCoh.hyp2_eq_sum_cup_of_fn_exact R C F hfr h0 hc hsurj c' hfn
  refine ⟨m + n, Fin.append a (fun k ↦ Hyp1.mk F (p (x k))),
    Fin.append (fun k ↦ clAll F hc (w k)) (fun k ↦ Hyp1.mk F (p (y k))), ?_⟩
  rw [← sum_append, ← hm, hc']
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_sum, cupHyp_mk, sub_add_cancel]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImagQuadIntegerLatticeMulStableISqrt
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.IntLatMul

theorem main : ∀ (d : ℕ) (Λ : PeriodPair), 0 < d → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    MulStable Λ (Complex.I * (Real.sqrt d : ℝ)) ∧ (Complex.I * (Real.sqrt d : ℝ)).im ≠ 0 := by
  intro d Λ hd hΛ
  set w : ℂ := Complex.I * (Real.sqrt d : ℝ) with hw
  have hw2 : w ^ 2 = -(d : ℂ) := by
    rw [hw, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    simp
  have hwi : IsIntegral ℤ w := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), by monicity!, ?_⟩
    rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C,
      algebraMap_int_eq, eq_intCast, Int.cast_natCast, hw2]
    ring
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨hxi, a, b, hab⟩ := (hΛ x).1 hx
    refine (hΛ _).2 ⟨hwi.mul hxi, -(b * d), a, ?_⟩
    rw [hab]
    push_cast
    linear_combination (b : ℂ) * hw2
  · have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
    simp [hw, hs.ne']

end GlobalTheory.IntLatMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureTorsorEtaleHeightOneAbhyankar
section
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginBC

theorem comap_map_C_mapRingHom {A A₁ : Type} [CommRing A] [CommRing A₁] (f : A →+* A₁) (p₁ : Ideal A₁) :
    (p₁.map (Polynomial.C : A₁ →+* A₁[X])).comap (Polynomial.mapRingHom f) =
      (p₁.comap f).map (Polynomial.C : A →+* A[X]) := by
  ext g
  simp only [Ideal.mem_comap, Ideal.mem_map_C_iff, Polynomial.coe_mapRingHom, Polynomial.coeff_map]

theorem atPrime_isDomain_injective (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
    (QA : Ideal EA) [QA.IsPrime] :
    IsDomain (Localization.AtPrime QA) ∧
      Function.Injective (algebraMap A (Localization.AtPrime QA)) := by
  obtain ⟨hd, -⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale (Polynomial A) QA
    (Localization.AtPrime QA)
  refine ⟨hd, ?_⟩
  haveI := hd
  haveI : Module.Flat (Polynomial A) (Localization.AtPrime QA) :=
    Module.Flat.trans (Polynomial A) EA (Localization.AtPrime QA)
  have h1 : Function.Injective (algebraMap (Polynomial A) (Localization.AtPrime QA)) :=
    FaithfulSMul.algebraMap_injective (Polynomial A) (Localization.AtPrime QA)
  have h2 : algebraMap A (Localization.AtPrime QA) =
      (algebraMap (Polynomial A) (Localization.AtPrime QA)).comp (algebraMap A (Polynomial A)) :=
    IsScalarTower.algebraMap_eq _ _ _
  rw [h2]
  exact h1.comp Polynomial.C_injective

theorem closureEtaleAt_of_mem_height_le_one : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra.EssFiniteType ℤ A] [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁]
    [IsIntegrallyClosed A₁] [Algebra.EssFiniteType ℤ A₁] (f : A →+* A₁) (i : A →+* T)
    (i₁ : A₁ →+* T) (hf : Function.Injective f)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    [Algebra.Etale A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA] (q : ℕ)
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → IsUnit (q : A) →
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∀ a : A, a ≠ 0 →
    (∀ (p₁ : Ideal A₁) [p₁.IsPrime], p₁.height = 1 → f a ∈ p₁ →
        (p₁.comap f).height = 1 ∧
        ∃ π : A, Irreducible (algebraMap A (Localization.AtPrime (p₁.comap f)) π) ∧
          ∃ y : A₁, y ^ q = f π) →
    ∀ (P₁ : Ideal (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj)) [P₁.IsPrime], P₁.height ≤ 1 → algebraMap A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (f a) ∈ P₁ →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (GlobalTheory.KeyOriginBC.BC (GlobalTheory.KeyOriginBC.fibBC f i i₁ EA QA jA hcomp hj hf) DA) P₁ := by
  intro T O _ _ _ _ _ _ A A₁ _ _ _ _ _ _ _ _ _ _ _ _ f i i₁ hf EA _ _ _ _ _ QA _ jA hcomp hj DA _ _ q actA
    hq hqu htor a ha hhyp P₁ _ hP₁ hfa
  obtain ⟨hRd, hRi⟩ := atPrime_isDomain_injective A EA QA
  obtain ⟨hR₁d, hR₁i⟩ := atPrime_isDomain_injective A₁ (Ext f EA) (ideal₁ f i i₁ EA QA jA hcomp hj)
  have hfa0 : f a ≠ 0 := fun h => ha (hf (by rw [h, map_zero]))
  obtain ⟨hp₁h, hX₁⟩ := GlobalTheory.T.height_one_contraction_of_etale_prime A₁ (Ext f EA) (ideal₁ f i i₁ EA QA jA hcomp hj) P₁ (f a)
    hfa0 hfa hP₁
  obtain ⟨hph, π, hπ, y, hy⟩ := hhyp _ hp₁h (by rw [Ideal.mem_comap]; exact hfa)
  obtain ⟨⟨_, hdvr₁⟩, -⟩ := GlobalTheory.T.height_one_prime_over_constant_ideal A₁ (Ext f EA) (ideal₁ f i i₁ EA QA jA hcomp hj) P₁ _
    hp₁h hX₁
  have hsq : (locBC f i i₁ EA QA jA hcomp hj).comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap A₁[X] (Loc₁ f i i₁ EA QA jA hcomp hj)).comp (Polynomial.mapRingHom f) := by
    apply RingHom.ext; intro p
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A[X] EA (Localization.AtPrime QA),
      locBC_algebraMap, RingHom.comp_apply, IsScalarTower.algebraMap_apply A₁[X] (Ext f EA)]
    congr 1
    rw [inclE_apply, Algebra.TensorProduct.algebraMap_apply]
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    rfl
  have hPX : (P₁.comap (locBC f i i₁ EA QA jA hcomp hj)).comap
      (algebraMap A[X] (Localization.AtPrime QA)) =
      ((P₁.comap (algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj))).comap f).map
        (Polynomial.C : A →+* A[X]) := by
    rw [Ideal.comap_comap, hsq, ← Ideal.comap_comap, hX₁, comap_map_C_mapRingHom]
  obtain ⟨⟨_, hdvr⟩, hirr⟩ := GlobalTheory.T.height_one_prime_over_constant_ideal A EA QA (P₁.comap (locBC f i i₁ EA QA jA hcomp hj)) _
    hph hPX
  have hsqA : (locBC f i i₁ EA QA jA hcomp hj).comp (algebraMap A (Localization.AtPrime QA)) =
      (algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)).comp f := by
    apply RingHom.ext; intro x
    exact locBC_algebraMap_base f i i₁ EA QA jA hcomp hj x
  have hsqF : (fibBC f i i₁ EA QA jA hcomp hj hf).comp
      (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
      (algebraMap (Loc₁ f i i₁ EA QA jA hcomp hj)
        (GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj))).comp
        (locBC f i i₁ EA QA jA hcomp hj) := by
    apply RingHom.ext; intro x
    exact fibBC_algebraMap f i i₁ EA QA jA hcomp hj hf x
  exact GlobalTheory.T.generic_fibre_base_change_injective A (Localization.AtPrime QA) hRi A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) hR₁i
    f hf _ hsqA _ hsqF DA q actA hq hqu htor P₁ hdvr₁ hdvr π (hirr π hπ)
    (algebraMap A₁ _ y) (by rw [← map_pow, hy, ← RingHom.comp_apply, ← hsqA, RingHom.comp_apply])

end GlobalTheory.KeyOriginBC
end
end

