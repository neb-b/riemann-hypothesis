module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1178
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1268
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1258
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0019

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueAdmissibleLocalComponentDefiniteUnit
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.LocCompU

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isIrreducible_comp_of_surjective {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ H X) (φ : H' →* H) (hφ : Function.Surjective φ) (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp φ) := by
  obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 h
  refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h1 W fun g v hv => ?_⟩
  obtain ⟨g', rfl⟩ := hφ g
  exact hW g' v hv

theorem isClosed_UL (hU : Unr E) (n : ℕ) (w : Pl E) : IsClosed (UL n w : Set (GLw n w)) := by
  unfold UL
  split_ifs
  · exact isClosed_univ
  · have hc := (GlobalTheory.ConjAtPlace.main E hU w).1
    have : Continuous fun g : GLw n w =>
        cT (cj w) (g : Matrix (Fin n) (Fin n) _) * 1 * (g : Matrix (Fin n) (Fin n) _) := by
      refine Continuous.mul (Continuous.mul ?_ continuous_const) Units.continuous_val
      exact continuous_matrix fun i j => hc.comp (Units.continuous_val.matrix_elem _ _)
    exact isClosed_singleton.preimage this

theorem isOpen_isCompact_KL (hU : Unr E) (n : ℕ) (w : Pl E) :
    IsOpen (KL n w : Set (UL n w)) ∧ IsCompact (KL n w : Set (UL n w)) := by
  have hK := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
  rw [KL, Subgroup.coe_subgroupOf]
  exact ⟨hK.1.preimage continuous_subtype_val,
    (isClosed_UL hU n w).isClosedEmbedding_subtypeVal.isCompact_preimage hK.2⟩

theorem exists_equiv (hU : Unr E) (n : ℕ) (w : Pl E) :
    ∃ e : locU n w ≃ₜ* UL n w, ∀ x : locU n w, ((e x : UL n w) : GLw n w) = cLoc w (x : UA E n) := by
  by_cases hs : IsSplitAt w
  · obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E n w hs
    have h : UL n w = ⊤ := if_pos hs
    have hm : ∀ g : GLw n w, g ∈ UL n w := fun g => by rw [h]; exact Subgroup.mem_top _
    refine ⟨{ toFun := fun x => ⟨e x, hm _⟩
              invFun := fun g => e.symm g.1
              left_inv := fun x => by simp
              right_inv := fun g => Subtype.ext (by simp)
              map_mul' := fun x y => Subtype.ext (by simp)
              continuous_toFun := e.continuous.subtype_mk _
              continuous_invFun := e.symm.continuous.comp continuous_subtype_val }, fun x => he x⟩
  · obtain ⟨-, -, hv, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
    obtain ⟨e, he⟩ := GlobalTheory.DefU.Inert.locU_equiv E n w (cj w) (hns hs).1 hv
    have h : UL n w = UJ (cj w) 1 := if_neg hs
    rw [h]
    exact ⟨e, he⟩

theorem exists_unique_locComp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ w : Pl E,
    (∃ σ : SmIrr (UL n w), IsCompU π w σ ∧
      ∀ U : Subgroup (UL n w), IsOpen (U : Set (UL n w)) → FiniteDimensional ℂ (fixed σ.ρ U)) ∧
    ∀ σ σ' : SmIrr (UL n w), IsCompU π w σ → IsCompU π w σ' → Nonempty (σ.ρ.Equiv σ'.ρ) := by
  intro E _ _ _ hU n _ π hπ w
  obtain ⟨e, he⟩ := exists_equiv hU n w
  obtain ⟨hKo, hKc⟩ := isOpen_isCompact_KL hU n w
  have hesurj : Function.Surjective (e.toMulEquiv.symm.toMonoidHom) := e.symm.surjective
  refine ⟨?_, ?_⟩
  · obtain ⟨σ₀, hadm, hirr, f, hf0, hfm, hf⟩ := GlobalTheory.DefU.LocAdm.exists_admissible_comp E n ⟨π, hπ⟩ w
    let ρ : Representation ℂ (UL n w) σ₀.V := σ₀.ρ.comp e.toMulEquiv.symm.toMonoidHom
    have hρ : ∀ g v, ρ g v = σ₀.ρ (e.symm g) v := fun _ _ => rfl
    let σ : SmIrr (UL n w) :=
      { V := σ₀.V
        ρ := ρ
        smooth := fun v => (σ₀.smooth v).preimage e.symm.continuous
        irred := isIrreducible_comp_of_surjective σ₀.ρ _ hesurj σ₀.irred }
    refine ⟨σ, ⟨e.toMulEquiv.toMonoidHom, fun x => he x, σ.irred, f, hf0, hfm, fun x v => ?_⟩, fun U hUo => ?_⟩
    · change f (σ₀.ρ (e.symm (e x)) v) = _
      rw [e.symm_apply_apply]
      exact hf x v
    · let K' : Subgroup (locU n w) := (U ⊓ KL n w).comap e.toMulEquiv.toMonoidHom
      have hK'o : IsOpen (K' : Set (locU n w)) := by
        change IsOpen (e ⁻¹' ((U : Set (UL n w)) ∩ (KL n w : Set (UL n w))))
        exact (hUo.inter hKo).preimage e.continuous
      have hK'c : IsCompact (K' : Set (locU n w)) := by
        change IsCompact (e ⁻¹' ((U : Set (UL n w)) ∩ (KL n w : Set (UL n w))))
        exact e.toHomeomorph.isCompact_preimage.2 (hKc.inter_left (U.isClosed_of_isOpen hUo))
      haveI := hadm.2 K' hK'o hK'c
      have hle : fixed σ.ρ U ≤ fixed σ₀.ρ K' := by
        intro v hv k
        have h1 := hv ⟨e k, k.2.1⟩
        simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1 ⊢
        change σ₀.ρ (e.symm (e k)) v = v at h1
        rwa [e.symm_apply_apply] at h1
      exact Submodule.finiteDimensional_of_le hle
  · rintro σ σ' ⟨p, hp, -, f, hf0, hfm, hf⟩ ⟨p', hp', -, f', hf0', hfm', hf'⟩
    have hpe : ∀ x, p x = e x := fun x => Subtype.ext ((hp x).trans (he x).symm)
    have hpe' : ∀ x, p' x = e x := fun x => Subtype.ext ((hp' x).trans (he x).symm)
    have hps : Function.Surjective p := fun g => ⟨e.symm g, by rw [hpe, e.apply_symm_apply]⟩
    have hps' : Function.Surjective p' := fun g => ⟨e.symm g, by rw [hpe', e.apply_symm_apply]⟩
    obtain ⟨r, -, -, hr2⟩ := GlobalTheory.DefU.LocRet.exists_ret E n w
    let π' : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
    let F : Representation.IntertwiningMap (σ.ρ.comp p) (π'.rep.comp (locU n w).subtype) :=
      ⟨f.codRestrict π hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
    let F' : Representation.IntertwiningMap (σ'.ρ.comp p') (π'.rep.comp (locU n w).subtype) :=
      ⟨f'.codRestrict π hfm', fun x => LinearMap.ext fun v => Subtype.ext (hf' x v)⟩
    have hF0 : F ≠ 0 := fun h =>
      hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
    have hF0' : F' ≠ 0 := fun h =>
      hf0' (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
    obtain ⟨-, h2⟩ := GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) π σ.V σ'.V π'.rep (locU n w).subtype
      (σ.ρ.comp p) (σ'.ρ.comp p') π'.isIrreducible_rep
      (isIrreducible_comp_of_surjective σ.ρ p hps σ.irred)
      (isIrreducible_comp_of_surjective σ'.ρ p' hps' σ'.irred)
      (fun g => ⟨r g, fun y => hr2 g y⟩) F hF0
    obtain ⟨T⟩ := h2 F' hF0'
    refine ⟨{ toLinearEquiv := T.toLinearEquiv, isIntertwining' := fun g => ?_ }⟩
    have h1 : p (e.symm g) = g := by rw [hpe, e.apply_symm_apply]
    have h1' : p' (e.symm g) = g := by rw [hpe', e.apply_symm_apply]
    have := T.isIntertwining' (e.symm g)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h1, h1'] at this
    exact this

end GlobalTheory.BCT.LocCompU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCentreAnnihilatorCompatibleMaps
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

namespace GlobalTheory.AutGrowth.KilledFin

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem cap_commute_Zalg (τ : E →+* ℂ) (u : ℂ) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    Commute (cap τ u) z :=
  commute_Zalg (fun X => GlobalTheory.SpehInfChar.cap_commute_act τ u (.lie X)) hz

theorem Zalg_commute {z z' : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (hz' : z' ∈ Zalg E a) :
    Commute z z' := by
  have hle : Zalg E a ≤ Subalgebra.centralizer ℂ {z'} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, u, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact (cap_commute_Zalg τ u hz').eq.symm
  have h := hle hz
  rw [Subalgebra.mem_centralizer_iff] at h
  exact (h z' rfl).symm

variable (φ : Sm E a) (L : Subgroup (GL (Fin a) (Af E)))

def postZ (z : Module.End ℂ (Sm E a)) (hz : z ∈ Zalg E a) : Module.End ℂ (mapsJ φ L) where
  toFun T := ⟨z ∘ₗ T.1, by
    have hT : T.1 ∈ maps L (spanK E a φ) (spanK_stable φ) ∧
        ∀ z ∈ Zalg E a, z φ = 0 → ∀ w, z (T.1 w) = 0 := T.2
    show _ ∧ _
    refine ⟨GlobalTheory.T.centre_comp_mem_kinfEquivariantAutomorphicMaps E a L (spanK E a φ) (spanK_stable φ) T.1 hT.1 z hz, fun z' hz' h0 w => ?_⟩
    show z' (z (T.1 w)) = 0
    rw [← Module.End.mul_apply, ← (Zalg_commute hz hz').eq, Module.End.mul_apply, hT.2 z' hz' h0 w, map_zero]⟩
  map_add' T T' := by ext; simp
  map_smul' c T := by ext; simp

def postZAlg : Zalg E a →ₐ[ℂ] Module.End ℂ (mapsJ φ L) where
  toFun z := postZ φ L z.1 z.2
  map_one' := LinearMap.ext fun _ => Subtype.ext (LinearMap.ext fun _ => rfl)
  map_mul' _ _ := LinearMap.ext fun _ => Subtype.ext (LinearMap.ext fun _ => rfl)
  map_zero' := LinearMap.ext fun _ => Subtype.ext (LinearMap.ext fun _ => rfl)
  map_add' _ _ := LinearMap.ext fun _ => Subtype.ext (LinearMap.ext fun _ => rfl)
  commutes' _ := LinearMap.ext fun _ => Subtype.ext (LinearMap.ext fun _ => rfl)

end GlobalTheory.AutGrowth.KilledFin

namespace GlobalTheory.AutGrowth.KilledFin

theorem fd_adjoin_of_ker_le (M : Type) [AddCommGroup M] [Module ℂ M] (A : Type) [Ring A] [Algebra ℂ A]
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ M) (ev : A →ₗ[ℂ] V)
    (hev : FiniteDimensional ℂ (LinearMap.range ev)) (hker : LinearMap.ker ev ≤ LinearMap.ker ρ.toLinearMap)
    (S : Set (Module.End ℂ M)) (hS : S ⊆ ρ.range) : FiniteDimensional ℂ (Algebra.adjoin ℂ S) := by
  haveI : FiniteDimensional ℂ (A ⧸ LinearMap.ker ev) :=
    LinearEquiv.finiteDimensional (ev.quotKerEquivRange).symm
  have hR : FiniteDimensional ℂ (LinearMap.range ρ.toLinearMap) := by
    rw [← Submodule.range_liftQ (LinearMap.ker ev) ρ.toLinearMap hker]
    infer_instance
  have hle : Subalgebra.toSubmodule (Algebra.adjoin ℂ S) ≤ LinearMap.range ρ.toLinearMap := by
    intro x hx
    obtain ⟨y, rfl⟩ := Algebra.adjoin_le hS hx
    exact ⟨y, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.AutGrowth.KilledFin

namespace GlobalTheory.AutGrowth.KilledFin

theorem finiteDimensional_mapsJ : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → ∀ L : Subgroup (GL (Fin a) (Af E)),
    IsOpen (L : Set (GL (Fin a) (Af E))) → FiniteDimensional ℂ (mapsJ φ L) := by
  intro hP E _ _ _ a φ hφ L hL
  have hcap : ∀ (τ : E →+* ℂ) (u : ℂ), cap (a := a) τ u ∈ Zalg E a := fun τ u =>
    Algebra.subset_adjoin ⟨τ, u, rfl⟩
  let S : Set (Module.End ℂ (mapsJ φ L)) := {s | ∃ τ u, s = postZ φ L (cap τ u) (hcap τ u)}
  refine _root_.GlobalTheory.AutGrowth.finiteDimensional_of_commuting_finite_eigen (mapsJ φ L) S ?_ ?_ ?_
  · rintro _ ⟨τ, u, rfl⟩ _ ⟨τ', u', rfl⟩
    refine LinearMap.ext fun T => Subtype.ext (LinearMap.ext fun w => ?_)
    show cap τ u (cap τ' u' (T.1 w)) = cap τ' u' (cap τ u (T.1 w))
    rw [← Module.End.mul_apply, (Zalg_commute (hcap τ u) (hcap τ' u')).eq, Module.End.mul_apply]
  · let ev : Zalg E a →ₗ[ℂ] Sm E a := (LinearMap.applyₗ φ).comp (Zalg E a).val.toLinearMap
    have hker : LinearMap.ker ev ≤ LinearMap.ker (postZAlg φ L).toLinearMap := by
      intro z hz
      rw [LinearMap.mem_ker] at hz ⊢
      refine LinearMap.ext fun T => Subtype.ext (LinearMap.ext fun w => ?_)
      have hT : T.1 ∈ maps L (spanK E a φ) (spanK_stable φ) ∧
          ∀ z ∈ Zalg E a, z φ = 0 → ∀ w, z (T.1 w) = 0 := T.2
      exact hT.2 z.1 z.2 hz w
    have hev : FiniteDimensional ℂ (LinearMap.range ev) := by
      have h1 : LinearMap.range ev ≤
          Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) := by
        rintro _ ⟨z, rfl⟩
        exact Submodule.subset_span ⟨z.1, z.2, rfl⟩
      haveI := hφ.zfin
      exact Submodule.finiteDimensional_of_le h1
    refine fd_adjoin_of_ker_le (mapsJ φ L) (Zalg E a) (Sm E a) (postZAlg φ L) ev hev hker S ?_
    rintro _ ⟨τ, u, rfl⟩
    exact ⟨⟨cap τ u, hcap τ u⟩, rfl⟩
  · intro c
    let J := ⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ (mapsJ φ L)) (c s))
    let N : Submodule ℂ (spanK E a φ →ₗ[ℂ] Sm E a) := J.map (mapsJ φ L).subtype
    have hNle : N ≤ maps L (spanK E a φ) (spanK_stable φ) := by
      rintro _ ⟨T, _, rfl⟩
      have hT : T.1 ∈ maps L (spanK E a φ) (spanK_stable φ) ∧
          ∀ z ∈ Zalg E a, z φ = 0 → ∀ w, z (T.1 w) = 0 := T.2
      exact hT.1
    have hNe : ∀ T ∈ N, ∀ (τ : E →+* ℂ) (u : ℂ),
        cap τ u ∘ₗ T = c (postZ φ L (cap τ u) (hcap τ u)) • T := by
      rintro _ ⟨T, hT, rfl⟩ τ u
      have hT' : T ∈ ⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ (mapsJ φ L)) (c s)) := hT
      have h := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hT' (postZ φ L (cap τ u) (hcap τ u))) ⟨τ, u, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.algebraMap_end_apply] at h
      exact congrArg Subtype.val h
    have hN : FiniteDimensional ℂ N :=
      _root_.GlobalTheory.AutGrowth.finiteDimensional_capEigen_maps hP E a L hL (spanK E a φ) (spanK_stable φ) hφ.kfin
        (fun τ u => c (postZ φ L (cap τ u) (hcap τ u))) N hNle hNe
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective (mapsJ φ L).subtype Subtype.val_injective J).symm

end GlobalTheory.AutGrowth.KilledFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDeepestFiltrationStepEqRational
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSShort.DeepStep

theorem ofFn_prod_induct {M : Type} [Monoid M] (p : M → ℕ → Prop) (h1 : p 1 0)
    (hmul : ∀ a b k l, p a k → p b l → p (a * b) (k + l)) :
    ∀ (n : ℕ) (g : Fin n → M) (k : Fin n → ℕ), (∀ i, p (g i) (k i)) → p (List.ofFn g).prod (∑ i, k i) := by
  intro n
  induction n with
  | zero => intro g k _; simpa using h1
  | succ n ih =>
    intro g k hg
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact hmul _ _ _ _ (hg 0) (ih _ _ fun i => hg i.succ)

theorem pow_induct {M : Type} [Monoid M] (p : M → ℕ → Prop) (h1 : p 1 0)
    (hmul : ∀ a b k l, p a k → p b l → p (a * b) (k + l)) (a : M) (ha : p a 1) : ∀ n, p (a ^ n) n := by
  intro n
  induction n with
  | zero => simpa using h1
  | succ n ih => rw [pow_succ]; exact hmul _ _ _ _ ih ha

section Inter

variable {F E A A' : Type} [Field F] [Field E] [Algebra F E] [AddCommGroup A] [Module F A] [AddCommGroup A'] [Module E A']
  (ι : A →ₛₗ[algebraMap F E] A')

theorem ofFn_prod_comm : ∀ (n : ℕ) (g' : Fin n → Module.End E A') (g : Fin n → Module.End F A),
    (∀ i x, g' i (ι x) = ι (g i x)) → ∀ x, (List.ofFn g').prod (ι x) = ι ((List.ofFn g).prod x) := by
  intro n
  induction n with
  | zero => intro g' g _ x; simp
  | succ n ih =>
    intro g' g hg x
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons, mul_apply_eq_comp, mul_apply_eq_comp,
      ih _ _ (fun i => hg i.succ), hg 0]

theorem pow_comm (f' : Module.End E A') (f : Module.End F A) (h : ∀ x, f' (ι x) = ι (f x)) :
    ∀ (n : ℕ) x, (f' ^ n) (ι x) = ι ((f ^ n) x) := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih => intro x; rw [pow_succ, pow_succ, mul_apply_eq_comp, mul_apply_eq_comp, h, ih]

theorem mem_span_image (Y : Set A) : ∀ y ∈ Submodule.span F Y, ι y ∈ Submodule.span E (ι '' Y) := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

end Inter

variable {F A : Type} [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A]

def Up (S : Sys F A) (f : Module.End F A) (k : ℕ) : Prop := ∀ j, j + k ≤ S.T → ∀ x ∈ S.V j, f x ∈ S.V (j + k)

theorem up_one (S : Sys F A) : Up S 1 0 := fun j _ x hx => by simpa using hx

theorem up_mul (S : Sys F A) : ∀ a b k l, Up S a k → Up S b l → Up S (a * b) (k + l) := by
  intro a b k l ha hb j hj x hx
  have h1 := hb j (by omega) x hx
  have h2 := ha (j + l) (by omega) _ h1
  rw [mul_apply_eq_comp]
  have e : j + (k + l) = j + l + k := by omega
  rw [e]; exact h2

theorem up_mul_gen (S : Sys F A) (hS : S.Hyp) (u : Fin S.N → F) : Up S (S.mul u) 1 := by
  intro j hj x hx
  have := (_root_.GlobalTheory.HSShort.wordMem F A S hS j 1 hj).1 (fun _ => u) x hx
  simpa [word] using this

theorem up_pw (S : Sys F A) (hS : S.Hyp) (s : Fin S.D → Fin S.N → F) (α : Fin S.D →₀ ℕ) :
    Up S (pw S.mul s α) α.degree := by
  rw [Finsupp.degree_eq_sum]
  exact ofFn_prod_induct (Up S) (up_one S) (up_mul S) S.D _ _
    fun i => pow_induct (Up S) (up_one S) (up_mul S) _ (up_mul_gen S hS (s i)) (α i)

end GlobalTheory.HSShort.DeepStep


open GlobalTheory.HSShort.DeepStep in
theorem GlobalTheory.HSShort.deepStep_finrank : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → F) (δ : ℕ) (Φ : S.Flat E A' (fun i k => algebraMap F E (s i k)) δ), FiniteDimensional E (Φ.U (S.T - S.D)) ∧ Module.finrank E (Φ.U (S.T - S.D)) = S.deepRank s ∧ S.deepRank s ≤ Module.finrank F (S.V S.T) := by
  intro F A _ _ _ _ _ _ S hS E A' _ _ _ _ s δ Φ
  set P : Submodule F A := ⨆ α : MonoDeg (Fin S.D) (S.T - S.D), (S.V S.D).map (pw S.mul s α.1) with hP
  have hle := hS.le_T
  have hPT : P ≤ S.V S.T := iSup_le fun α => by
    rintro _ ⟨x, hx, rfl⟩
    have h := up_pw S hS s α.1 S.D (by rw [α.2]; omega) x hx
    have e : S.D + α.1.degree = S.T := by rw [α.2]; omega
    rw [e] at h
    exact h
  haveI : FiniteDimensional F (S.V S.T) := by
    obtain ⟨r, b, -⟩ := hS.shortT
    exact Module.Finite.of_basis b
  haveI : FiniteDimensional F P := Submodule.finiteDimensional_of_le hPT
  have hdeep : S.deepRank s = Module.finrank F P := rfl
  let b := Module.finBasis F P
  let v : Fin (Module.finrank F P) → A := fun i => (b i : A)
  have hv : Submodule.span F (Set.range v) = P := by
    have : Set.range v = (P.subtype) '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hli : LinearIndependent E (fun i => Φ.ι (v i)) := by
    refine Φ.indep _ (fun i => (⟨v i, hPT (b i).2⟩ : S.V S.T)) ?_
    refine LinearIndependent.of_comp (S.V S.T).subtype ?_
    exact b.linearIndependent.map' P.subtype (Submodule.ker_subtype P)
  have hcomm : ∀ (α : Fin S.D →₀ ℕ) (x : A),
      pw Φ.mul (fun i k => algebraMap F E (s i k)) α (Φ.ι x) = Φ.ι (pw S.mul s α x) := fun α x =>
    ofFn_prod_comm Φ.ι _ _ _ (fun i y => pow_comm Φ.ι _ _ (fun z => Φ.mul_ι (s i) z) (α i) y) x
  have hU : Φ.U (S.T - S.D) = Submodule.span E (Set.range fun i => Φ.ι (v i)) := by
    rw [Φ.div]
    apply le_antisymm
    · refine iSup_le fun α => ?_
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rw [SetLike.mem_coe, hcomm]
      have h1 : pw S.mul s α.1 x ∈ P := Submodule.mem_iSup_of_mem α ⟨x, hx, rfl⟩
      rw [← hv] at h1
      have h2 := mem_span_image Φ.ι _ _ h1
      rwa [← Set.range_comp] at h2
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have hvi : v i ∈ P := (b i).2
      exact Submodule.iSup_induction (fun α : MonoDeg (Fin S.D) (S.T - S.D) => (S.V S.D).map (pw S.mul s α.1))
        (motive := fun y => Φ.ι y ∈ ⨆ α : MonoDeg (Fin S.D) (S.T - S.D),
          (Submodule.span E (Φ.ι '' S.V S.D)).map (pw Φ.mul (fun i k => algebraMap F E (s i k)) α.1)) hvi
        (fun α y hy => by
          obtain ⟨x, hx, rfl⟩ := hy
          rw [← hcomm]
          exact Submodule.mem_iSup_of_mem α (Submodule.mem_map_of_mem (Submodule.subset_span ⟨x, hx, rfl⟩)))
        (by simp only [map_zero]; exact zero_mem _)
        (fun y z hy hz => by simp only [map_add (f := _)]; exact add_mem hy hz)
  refine ⟨?_, ?_, ?_⟩
  · rw [hU]; exact FiniteDimensional.span_of_finite E (Set.finite_range _)
  · rw [hU, finrank_span_eq_card hli, Fintype.card_fin, hdeep]
  · rw [hdeep]; exact Submodule.finrank_mono hPT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierCoefficientFamilyPullbackFractionField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Poinc.Tors.CoefPull

open GlobalTheory.FieldBaseChange GlobalTheory.TorusExt GlobalTheory.UT.CoefBasic GlobalTheory.UT.EvalZero

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {E F : Type} [Field F] [Algebra (FractionRing R) F]
  [Field E] [Algebra (FractionRing R) E] [Algebra E F] [IsScalarTower (FractionRing R) E F]

theorem cst_map (z : (TF (R := R) F).left) (a : E) :
    cst (R := R) F z (algebraMap E F a) =
      ((baseMap (R := R) E F).left.stalkMap z).hom (cst (R := R) E ((baseMap (R := R) E F).left z) a) := by
  refine Eq.trans ?_ (gs_comp_stalkMap (𝟙 _) (baseMap (R := R) E F).left z ⊤ trivial _)
  rw [Category.comp_id]
  refine Eq.trans ?_ ((gs_pull (𝟙 _) (baseMap (R := R) E F).left z ⊤ trivial _).trans (by rw [Category.id_comp]))
  refine congrArg (gs (𝟙 _) z ⊤) ?_
  exact congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap E F)))

theorem coef_famPull (hf : (algebraMap E F).comp (algebraMap (FractionRing R) E) = algebraMap (FractionRing R) F)
    (hG : GlobalFnsSt) (k : ℕ) (s : Fam D E k) (g : GtPtF D E) (w : Frm D E k g.b)
    (w' : Frm D F k (gtExt D (algebraMap E F) hf g).b) (hw : w.IsGen)
    (hv : ∀ z J, Good D.P.L z J → val w' (𝟙 _) z J = val w (spMap (algebraMap E F)) z J) (χ : D.X) :
    coef (famPull D E F hG k s) (gtExt D (algebraMap E F) hf g) w' χ = algebraMap E F (coef s g w χ) := by
  refine coef_eq fun z J hJ => ?_
  let p := baseMap (R := R) E F
  have hJ' : Good D.P.L (p.left z) (fun ψ => J (p.left ≫ ψ)) := fun ψ => hJ (p.left ≫ ψ)
  have a := congrArg (p.left.stalkMap z).hom (isCoef_coef g hw χ s (p.left z) _ hJ')
  rw [map_mul, map_mul, map_mul, map_pow] at a
  have hb : (gtExt D (algebraMap E F) hf g).b = p ≫ g.b := gtExt_b _ hf g
  have e : lift (𝟙 (TF (R := R) F)) (gtExt D (algebraMap E F) hf g).b ≫ famMap D E F = p ≫ lift (𝟙 _) g.b := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, famMap_fst, lift_fst_assoc, Category.assoc, lift_fst, Category.id_comp, Category.comp_id]
    · rw [Category.assoc, Category.assoc, lift_snd, ← hb]
      exact (congrArg _ (famMap_snd D E F)).trans (lift_snd _ _)
  have e' : (lift (𝟙 (TF (R := R) F)) (gtExt D (algebraMap E F) hf g).b).left ≫ (famMap D E F).left =
      p.left ≫ (lift (𝟙 _) g.b).left := congrArg (fun q => q.left) e
  refine (congrArg₂ (· * ·) (cst_map z _) (congrArg (· ^ k) ?_)).trans (a.trans
    (congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ ?_) ?_).symm)
  · exact val_comp_map (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig p.left
      (TF (R := R) E).hom _ (Over.w p) z hJ
  · refine (sval_pullOver _ _ _ _ hJ).trans ?_
    refine Eq.trans (by rw [e']) ?_
    exact (values_natural _ _ _ _ D.P.L _ _ _ _ p.left z J hJ).2.1 (s.s χ)
  · exact (congrArg Units.val (gtExt_val _ hf g χ hJ)).trans (val_comp_map _ p.left (𝟙 _) _ (Category.comp_id _) z hJ)
  · exact (congrArg Units.val (hv z J hJ)).trans (val_comp_map _ p.left (𝟙 _) _ (Category.comp_id _) z hJ)

theorem coef_famPull_frac : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (hG : GlobalFnsSt) (k : ℕ) (s : Fam D (FractionRing R) k) (g : GtPtF D (FractionRing R)) (w : Frm D (FractionRing R) k g.b) (w' : Frm D F k (GlobalTheory.TorusExt.gtExt D (algebraMap (FractionRing R) F) (RingHom.comp_id _) g).b), w.IsGen → w'.IsGen → (∀ z J, Good D.P.L z J → val w' (𝟙 _) z J = val w (spMap (algebraMap (FractionRing R) F)) z J) → ∀ χ : D.X, coef (GlobalTheory.FieldBaseChange.famPull D (FractionRing R) F hG k s) (GlobalTheory.TorusExt.gtExt D (algebraMap (FractionRing R) F) (RingHom.comp_id _) g) w' χ = algebraMap (FractionRing R) F (coef s g w χ) :=
  fun _ _ _ _ _ _ _ hG k s g w w' hw _ hv χ => coef_famPull _ hG k s g w w' hw hv χ

end GlobalTheory.Poinc.Tors.CoefPull
end
end

