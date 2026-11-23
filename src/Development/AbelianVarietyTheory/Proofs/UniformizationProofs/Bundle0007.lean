module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSMulRegularCokerDualMapOfExactFibres
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExactDualMapOfExactFibresOfIsRegularLocalRing
section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function

namespace GlobalTheory
namespace DualCokernel

theorem extZero_of_isRegularLocalRing (R : Type) [CommRing R] [IsRegularLocalRing R] (g : ℕ)
    (hg : ringKrullDim R = g) (j : ℕ) (hj : j < g) : ExtZero (R := R) R j := by
  obtain ⟨xs, h, hd⟩ := exists_ofList_eq_maximalIdeal_length_eq R
  have hreg := isRegular_of_ofList_eq_maximalIdeal h hd.le
  have hlen : xs.length = g := by
    rw [hg] at hd
    exact_mod_cast hd
  refine ModuleCat.subsingleton_ext_of_exists_isRegular (maximalIdeal R) _ ?_ _ ?_ _ ?_ hreg j
    (by simpa [hlen] using hj)
  · rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  · rw [smul_eq_mul, Ideal.mul_top]
    exact (maximalIdeal.isMaximal R).ne_top.lt_top
  · intro r hr
    exact h ▸ Ideal.subset_span hr

end DualCokernel


open DualCokernel in
theorem exact_dualMap_of_exact_fibres_of_isRegularLocalRing :
    ∀ (A : Type) [CommRing A] [IsRegularLocalRing A] (g : ℕ), ringKrullDim A = g →
      ∀ C : CochainComplex (ModuleCat.{0} A) ℕ,
      (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) → (∃ n, ∀ i, n < i → IsZero (C.X i)) →
      (∀ p : PrimeSpectrum A, ∃ (K : Type) (_ : Field K) (φ : A →+* K),
        RingHom.ker φ = p.asIdeal ∧ ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal A ∨ g < i) →
          (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) →
      ∀ i, Function.Exact (C.d (i + 1) (i + 2)).hom.dualMap (C.d i (i + 1)).hom.dualMap := by
  intro A _ _ g hg C hF ⟨n, hn⟩ hex
  have hfree := fun i => (hF i).1
  have hfin := fun i => (hF i).2
  have hDext : ∀ i, ∀ j < g, ExtZero (R := A) (Module.Dual A (C.X i)) j := fun i j hj =>
    FiniteLengthComplex.subsingleton_ext_free _ j (extZero_of_isRegularLocalRing A g hg j hj) _
  have hdd : ∀ i j k f, (C.d i j).hom.dualMap ((C.d j k).hom.dualMap f) = 0 := fun i j k f => by
    ext x
    simp [d_d_apply]

  have hloc : ∀ i, ∀ p : Ideal A, p.IsPrime → p ≠ maximalIdeal A → ∃ s, s ∉ p ∧
      ∀ f, (C.d (i - 1) i).hom.dualMap f = 0 →
        s • f ∈ LinearMap.range (C.d i (i + 1)).hom.dualMap := by
    intro i p hp hpm
    obtain ⟨K, _, φ, hφ, hK⟩ := hex ⟨p, hp⟩
    obtain ⟨t, ht, k₀, k₁, hk⟩ := exists_homotopy C hF n hn p
      (fun j => exact_fibre C p φ hφ j (hK j (Or.inl hpm))) i
    refine ⟨t, ht, fun f hf => ⟨k₁.dualMap f, LinearMap.ext fun x => ?_⟩⟩
    have h1 : f ((C.d (i - 1) i).hom (k₀ x)) = 0 := LinearMap.congr_fun hf (k₀ x)
    have h2 := congrArg f (hk x)
    rw [map_add (f := _), h1, zero_add, map_smul] at h2
    exact h2

  have hhom : ∀ i, g ≤ i → ∃ (s : C.X (i + 1) →ₗ[A] C.X i) (t : C.X (i + 1 + 1) →ₗ[A] C.X (i + 1)),
      ∀ x, (C.d i (i + 1)).hom (s x) + t ((C.d (i + 1) (i + 1 + 1)).hom x) = x := by
    intro i hi
    obtain ⟨K, _, φ, hφ, hK⟩ := hex ⟨maximalIdeal A, inferInstance⟩
    obtain ⟨s, t, hst⟩ := exists_homotopy_of_forall_exact_residueField
      (f := (C.d i (i + 1)).hom) (g := (C.d (i + 1) (i + 1 + 1)).hom)
      (LinearMap.ext (d_d_apply C _ _ _)) fun m hm' => by
        exact exact_fibre C m φ (hφ.trans (eq_maximalIdeal hm').symm) (i + 1)
          (hK _ (Or.inr (by omega)))
    exact ⟨s, t, fun x => by simpa using LinearMap.congr_fun hst x⟩

  have hstep : ∀ i, ExtZero (R := A)
      (Module.Dual A (C.X (i + 1)) ⧸ LinearMap.range (C.d (i + 1) (i + 1 + 1)).hom.dualMap) 0 →
      LinearMap.ker (C.d i (i + 1)).hom.dualMap ≤
        LinearMap.range (C.d (i + 1) (i + 1 + 1)).hom.dualMap := by
    intro i h0 f hf
    refine (Submodule.Quotient.mk_eq_zero _).1 (eq_zero_of_extZero h0 _ fun p hp hpm => ?_)
    obtain ⟨s, hs, hs'⟩ := hloc (i + 1) p hp hpm
    exact ⟨s, hs, (Submodule.Quotient.mk_eq_zero _).2 (hs' f hf)⟩
  have hle : ∀ i, LinearMap.range (C.d (i + 1) (i + 1 + 1)).hom.dualMap ≤
      LinearMap.ker (C.d i (i + 1)).hom.dualMap := by
    rintro i _ ⟨y, rfl⟩
    exact hdd _ _ _ y
  have key : ∀ k i, i + k = g → ∀ j < i, ExtZero (R := A)
      (Module.Dual A (C.X i) ⧸ LinearMap.range (C.d i (i + 1)).hom.dualMap) j := by
    intro k
    induction k with
    | zero =>
      rintro i rfl
      obtain ⟨s, t, hst⟩ := hhom i le_rfl
      have hds : ∀ x, (C.d i (i + 1)).hom (s ((C.d i (i + 1)).hom x)) = (C.d i (i + 1)).hom x :=
        fun x => by simpa [d_d_apply] using hst ((C.d i (i + 1)).hom x)
      let ι := (LinearMap.range (C.d i (i + 1)).hom.dualMap).liftQ
        (LinearMap.id - (C.d i (i + 1)).hom.dualMap ∘ₗ s.dualMap) (by
          rintro _ ⟨f, rfl⟩
          ext x
          simp [hds])
      have hι : (LinearMap.range (C.d i (i + 1)).hom.dualMap).mkQ ∘ₗ ι = LinearMap.id := by
        refine Submodule.linearMap_qext _ (LinearMap.ext fun f => ?_)
        refine (Submodule.Quotient.eq _).2 ⟨-s.dualMap f, ?_⟩
        simp [ι]
      exact fun j hj => extZero_retract ι _ hι j (hDext i j hj)
    | succ k ih =>
      intro i hi j hj
      have h := ih (i + 1) (by omega)
      exact extZero_coker ((LinearMap.range _).liftQ _ (hle i))
        (LinearMap.range (C.d i (i + 1)).hom.dualMap).mkQ
        (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ (hstep i (h 0 (by omega)))))
        (Submodule.mkQ_surjective _)
        (by rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_liftQ]) j
        (h _ (by omega)) (hDext i j (by omega))
  intro i
  refine LinearMap.exact_iff.2 (le_antisymm ?_ (hle i))
  rcases lt_or_ge i g with hi | hi
  · exact hstep i (key (g - (i + 1)) (i + 1) (by omega) 0 (by omega))
  · intro f hf
    obtain ⟨s, t, hst⟩ := hhom i hi
    refine ⟨t.dualMap f, LinearMap.ext fun x => ?_⟩
    have h1 : f ((C.d i (i + 1)).hom (s x)) = 0 := LinearMap.congr_fun hf (s x)
    have h2 := congrArg f (hst x)
    rw [map_add (f := _), h1, zero_add] at h2
    exact h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecValEqIff
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.FiniteCover

variable {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']

abbrev toField {U : X.Opens} (h : genericPoint X ∈ U) : Γ(X, U) →+* X.functionField :=
  (X.presheaf.germ U (genericPoint X) h).hom

theorem generic_mem {U : X.Opens} {x : X} (h : x ∈ U) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, h⟩

theorem generic_inf {U V : X.Opens} (hU : genericPoint X ∈ U) (hV : genericPoint X ∈ V) :
    genericPoint X ∈ U ⊓ V := ⟨hU, hV⟩

theorem generic_top : genericPoint X ∈ (⊤ : X.Opens) := trivial

theorem toField_rs {U V : X.Opens} (h : V ≤ U) (hV : genericPoint X ∈ V) (a : Γ(X, U)) :
    toField hV (rs X h a) = toField (h hV) a :=
  X.presheaf.germ_res_apply (homOfLE h) _ hV a

theorem toField_injective {U : X.Opens} (h : genericPoint X ∈ U) :
    Function.Injective (toField h) := germ_injective_of_isIntegral X _ h

theorem exists_toField_eq {D : X.Opens} (hD : genericPoint X ∈ D) {I : Type} (O : I → X.Opens)
    (hO : ∀ a, O a ≤ D) (hc : D ≤ ⨆ a, O a) (hη : ∀ a, genericPoint X ∈ O a) (x : X.functionField)
    (hx : ∀ a, ∃ y, toField (hη a) y = x) : ∃ y, toField hD y = x := by
  choose y hy using hx
  obtain ⟨z, hz, -⟩ := X.sheaf.existsUnique_gluing' O D (fun a => homOfLE (hO a)) hc y
    fun a b => toField_injective (U := O a ⊓ O b) (generic_inf (hη a) (hη b))
      (((toField_rs inf_le_left _ _).trans (hy a)).trans ((toField_rs inf_le_right _ _).trans (hy b)).symm)
  obtain ⟨a, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc hD)
  exact ⟨z, (toField_rs (hO a) (hη a) z).symm.trans ((congrArg _ (hz a)).trans (hy a))⟩

theorem toField_appLE (φ : X' ⟶ X) [IsDominant φ] {U : X.Opens} {V : X'.Opens} (e : V ≤ φ ⁻¹ᵁ U)
    (hU : genericPoint X ∈ U) (hV : genericPoint X' ∈ V) (a : Γ(X, U)) :
    toField hV ((φ.appLE U V e).hom a) = functionFieldMap φ (toField hU a) := by
  have h₁ : toField hV ((φ.appLE U V e).hom a) = toField (e hV) ((φ.app U).hom a) :=
    toField_rs e hV _
  rw [h₁, functionFieldMap, CommRingCat.hom_comp, RingHom.comp_apply]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  exact (Scheme.Hom.germ_stalkMap_apply φ U (genericPoint X') (e hV) a).symm

variable {M : LB X} {k₀ : M.ι} (h₀ : genericPoint X ∈ M.U k₀)

def secVal {V : X.Opens} (hV : genericPoint X ∈ V) (σ : SecOn M V) : X.functionField :=
  toField (U := V ⊓ M.U k₀) (generic_inf (hV) (h₀)) (GlobalTheory.LB.coord σ k₀)

theorem toField_coord {V : X.Opens} (hV : genericPoint X ∈ V) (σ : SecOn M V) {k : M.ι}
    (hk : genericPoint X ∈ M.U k) :
    toField (U := V ⊓ M.U k) (generic_inf (hV) (hk)) (GlobalTheory.LB.coord σ k) =
      toField (U := M.U k ⊓ M.U k₀) (generic_inf (hk) (h₀)) (M.g k k₀).val * secVal h₀ hV σ := by
  have e := congrArg (toField (U := V ⊓ M.U k ⊓ M.U k₀) (generic_inf (generic_inf hV hk) h₀))
    (SecOn.compat σ k k₀ (O := V ⊓ M.U k ⊓ M.U k₀) inf_le_left (inf_le_inf_right _ inf_le_left)
      (inf_le_inf_right _ inf_le_right))
  rw [map_mul, toField_rs, toField_rs, toField_rs] at e
  exact e

theorem secVal_injective {V : X.Opens} (hV : genericPoint X ∈ V) :
    Function.Injective (secVal h₀ hV) := fun σ τ h => GlobalTheory.LB.sec_ext fun k => by
  by_cases hk : genericPoint X ∈ M.U k
  · refine toField_injective (U := V ⊓ M.U k) (generic_inf (hV) (hk)) ?_
    rw [toField_coord h₀ hV σ hk, toField_coord h₀ hV τ hk, h]
  · have : V ⊓ M.U k = ⊥ := eq_bot_iff.2 fun x hx => (hk (generic_mem hx.2)).elim
    have : Subsingleton Γ(X, V ⊓ M.U k) := this ▸ inferInstance
    exact Subsingleton.elim _ _

theorem secVal_restrict {V W : X.Opens} (h : W ≤ V) (hW : genericPoint X ∈ W) (σ : SecOn M V) :
    secVal h₀ hW (SecOn.restrict M h σ) = secVal h₀ (h hW) σ :=
  toField_rs (inf_le_inf_right _ h) _ _

theorem secVal_smul {V : X.Opens} (hV : genericPoint X ∈ V) (a : Γ(X, V)) (σ : SecOn M V) :
    secVal h₀ hV (a • σ) = toField hV a * secVal h₀ hV σ :=
  (map_mul (toField (U := V ⊓ M.U k₀) (generic_inf (hV) (h₀))) (rs X inf_le_left a) _).trans
    (congrArg (· * secVal h₀ hV σ) (toField_rs _ _ _))

theorem secVal_add {V : X.Opens} (hV : genericPoint X ∈ V) (σ τ : SecOn M V) :
    secVal h₀ hV (σ + τ) = secVal h₀ hV σ + secVal h₀ hV τ :=
  map_add (toField (U := V ⊓ M.U k₀) (generic_inf (hV) (h₀))) _ _

theorem exists_secVal_eq_iff (hM : M.IsLB) {I : Type} (D : I → X.Opens) (hc : ⊤ ≤ ⨆ i, D i)
    (hη : ∀ i, genericPoint X ∈ D i) (τ : ∀ i, SecOn M (D i))
    (hτ : ∀ i k, IsUnit (GlobalTheory.LB.coord (τ i) k)) (x : X.functionField) :
    (∃ σ : SecOn M ⊤, secVal h₀ generic_top σ = x) ↔
      ∀ i, ∃ a ∈ (toField (hη i)).range, x = a * secVal h₀ (hη i) (τ i) := by
  constructor
  · rintro ⟨σ, rfl⟩ i
    have hne : secVal h₀ (hη i) (τ i) ≠ 0 := ((hτ i k₀).map _).ne_zero
    refine ⟨secVal h₀ generic_top σ / secVal h₀ (hη i) (τ i), ?_, (div_mul_cancel₀ _ hne).symm⟩
    refine exists_toField_eq (hη i) (fun k : {k // genericPoint X ∈ M.U k} => D i ⊓ M.U k.1)
      (fun _ => inf_le_left) (fun y hy => ?_) (fun k => (generic_inf (hη i) (k.2))) _ fun k => ?_
    · obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (trivial : y ∈ ⊤))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨k, generic_mem hk⟩, hy, hk⟩
    · obtain ⟨u, hu⟩ := hτ i k.1
      refine ⟨GlobalTheory.LB.coord (SecOn.restrict M le_top σ) k.1 * u⁻¹.val, ?_⟩
      have e₁ := toField_coord h₀ (hη i) (τ i) k.2
      have e₂ := toField_coord h₀ (hη i) (SecOn.restrict M le_top σ) k.2
      have hg : toField (U := M.U k.1 ⊓ M.U k₀) (generic_inf (k.2) (h₀)) (M.g k.1 k₀).val ≠ 0 :=
        ((M.g k.1 k₀).isUnit.map _).ne_zero
      rw [map_mul, map_units_inv, hu, e₁, e₂, secVal_restrict]
      field_simp
  · intro h
    choose a ha hx using h
    choose b hb using ha
    have hv : ∀ i, secVal h₀ (hη i) (b i • τ i) = x := fun i => by
      rw [secVal_smul, hb, hx i]
    obtain ⟨σ, hσ, -⟩ := SecOn.existsUnique_glue D (fun _ => le_top) hc (fun i => b i • τ i)
      fun i j => secVal_injective h₀ (V := D i ⊓ D j) (generic_inf (hη i) (hη j)) (by
        rw [secVal_restrict, secVal_restrict, hv, hv])
    obtain ⟨i, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc generic_top)
    exact ⟨σ, by rw [← hv i, ← hσ i, secVal_restrict]⟩

def secValLin {K : Type} [Field K] (f : X ⟶ Spec (CommRingCat.of K)) [Algebra K X.functionField]
    (hK : ∀ r, algebraMap K X.functionField r = toField generic_top (cst f ⊤ r)) :
    SecOnR f M ⊤ →ₗ[K] X.functionField where
  toFun σ := secVal h₀ generic_top σ
  map_add' σ τ := secVal_add h₀ generic_top σ τ
  map_smul' r σ := (secVal_smul h₀ generic_top (cst f ⊤ r) σ).trans (by
    rw [RingHom.id_apply, Algebra.smul_def, hK])

theorem secVal_pull (φ : X' ⟶ X) [IsDominant φ] {V : X.Opens} (hV : genericPoint X ∈ V)
    (h₀' : genericPoint X' ∈ (M.pull φ).U fun _ => k₀) (hV' : genericPoint X' ∈ φ ⁻¹ᵁ V)
    (σ : SecOn M V) :
    secVal h₀' hV' (SecOn.pull M φ V σ) = functionFieldMap φ (secVal h₀ hV σ) :=
  toField_appLE φ _ _ _ _

end GlobalTheory.FiniteCover
end
end

