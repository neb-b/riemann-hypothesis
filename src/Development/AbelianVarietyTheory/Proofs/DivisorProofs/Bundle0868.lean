module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ColumnDataLaws
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VacuumCharacterDeterminant
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibrePrincipalBundleSignEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnFrameA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0837
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0857

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsPowOfRealInjective
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped TensorProduct

namespace GlobalTheory.TypeTwo

theorem absPow_ofReal_injective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (x y : ℝ), absPow k (x : ℂ) = absPow k (y : ℂ) → x = y := by
  intro k _ _ _ _ x y h
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LocGL.exists_uniformizer k
  have h1 : nabs k ϖ ≠ 1 := fun e => ValuativeRel.uniformizer_lt_one.ne (hϖ.symm.trans ((nabs_eq_one_iff ϖ).1 e))
  have h2 : nabs k ϖ ^ x = nabs k ϖ ^ y := by
    have hx := val_absPow_ofReal k x ϖ
    have hy := val_absPow_ofReal k y ϖ
    rw [h] at hx
    exact_mod_cast hx.symm.trans hy
  have h3 := congrArg Real.log h2
  rw [Real.log_rpow (nabs_pos' k ϖ), Real.log_rpow (nabs_pos' k ϖ)] at h3
  exact mul_right_cancel₀ (Real.log_ne_zero_of_pos_of_ne_one (nabs_pos' k ϖ) h1) h3

end GlobalTheory.TypeTwo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicConjugateOfTrivialisation
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem mul_triv_star {S A : Type*} [Ring S] [CommRing A] [Algebra A S] (σ : S →+* Sᵐᵒᵖ) (b h x : S) (t d : A)
    (hx : x * b * (σ x).unop = algebraMap A S t) (hh : h * (σ h).unop = algebraMap A S d) :
    h * x * b * (σ (h * x)).unop = algebraMap A S (t * d) := by
  calc h * x * b * (σ (h * x)).unop = h * (x * b * (σ x).unop) * (σ h).unop := by
        simp only [map_mul, MulOpposite.unop_mul, mul_assoc]
    _ = algebraMap A S t * (h * (σ h).unop) := by rw [hx, ← Algebra.commutes, mul_assoc]
    _ = _ := by rw [hh, map_mul]

end GlobalTheory.LKMid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFormsFiniteStabilisers
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InnerClassSum


open MeasureTheory IsDedekindDomain NumberField Matrix in
open scoped TensorProduct InnerProductSpace Pointwise in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.InnerClassSum.finite_stab_of_measure {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant] (Γ K : Subgroup G) [Countable Γ] {𝓖 : Set G}
    (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) (h0 : ν K ≠ 0) (h1 : ν K ≠ ⊤) (a : G) :
    {γ : Γ | a⁻¹ * (γ : G) * a ∈ K}.Finite := by
  set S := {γ : Γ | a⁻¹ * (γ : G) * a ∈ K} with hS_def
  set T : Set G := (fun y => a⁻¹ * y) ⁻¹' (K : Set G) with hT_def
  have hT : ν T = ν K := measure_preimage_mul ν a⁻¹ K
  have hsum := h𝓖.measure_eq_tsum' T
  have hδT : ∀ δ ∈ S, δ • T = T := by
    intro δ hδ
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [hT_def, Set.mem_preimage, SetLike.mem_coe, Subgroup.smul_def, smul_eq_mul,
      Subgroup.coe_inv]
    have hk : a⁻¹ * (δ : G)⁻¹ * a ∈ K := by
      have := K.inv_mem hδ
      simpa [mul_assoc] using this
    constructor
    · intro hx
      have := K.mul_mem (K.inv_mem hk) hx
      simpa [mul_assoc] using this
    · intro hx
      have := K.mul_mem hk hx
      simpa [mul_assoc] using this
  have hinv : ∀ δ ∈ S, ∀ γ : Γ, ν (T ∩ (δ * γ) • 𝓖) = ν (T ∩ γ • 𝓖) := by
    intro δ hδ γ
    rw [← measure_smul ν δ (T ∩ γ • 𝓖), Set.smul_set_inter, hδT δ hδ, mul_smul]
  by_contra hinf
  obtain ⟨γ0, hγ0⟩ : ∃ γ0 : Γ, ν (T ∩ γ0 • 𝓖) ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply h0
    rw [← hT, hsum]
    simp [hall]
  have hle := ENNReal.tsum_comp_le_tsum_of_injective (f := fun δ : S => (δ : Γ) * γ0)
    (fun x y hxy => Subtype.ext (mul_right_cancel hxy)) (fun γ : Γ => ν (T ∩ γ • 𝓖))
  have : Infinite S := Set.infinite_coe_iff.2 hinf
  have htop : ∑' δ : S, ν (T ∩ ((δ : Γ) * γ0) • 𝓖) = ⊤ := by
    rw [tsum_congr (fun δ : S => hinv δ δ.2 γ0)]
    exact ENNReal.tsum_const_eq_top_of_ne_zero hγ0
  rw [htop, ← hsum, hT] at hle
  exact h1 (top_le_iff.1 hle)


open MeasureTheory IsDedekindDomain NumberField Matrix in
open scoped TensorProduct InnerProductSpace Pointwise in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.InnerClassSum.integral_inner_eq_adInner {G H W : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ν : Measure G)
    [ν.IsMulLeftInvariant]
    (π : G →* H) (hπ : Function.Surjective π) (Γ : Subgroup G) [Countable Γ] {𝓖 : Set G}
    (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) (J : Subgroup H) (ho : IsOpen (J.comap π : Set G))
    (h1 : ν (J.comap π) = 1)
    (ρ : G →* Module.End ℂ W) (hρ : ∀ h x y, inner ℂ (ρ h x) (ρ h y) = inner ℂ x y) (χ : J →* ℂˣ)
    (hχ : ∀ k, ‖(χ k : ℂ)‖ = 1) {I : Type} [Fintype I] (y : I → H)
    (hy : _root_.Formalism.IndefR.Bridge.IsReps (π.comp Γ.subtype) J y) :
    (∀ i, Finite (_root_.Formalism.IndefR.Bridge.stab (π.comp Γ.subtype) J (y i))) ∧
      ∀ f ∈ _root_.Formalism.IndefR.Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ,
      ∀ f' ∈ _root_.Formalism.IndefR.Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ,
        IntegrableOn (fun h => inner ℂ (ρ h⁻¹ (f (π h))) (ρ h⁻¹ (f' (π h)))) 𝓖 ν ∧
        ∫ h in 𝓖, inner ℂ (ρ h⁻¹ (f (π h))) (ρ h⁻¹ (f' (π h))) ∂ν =
          _root_.Formalism.IndefR.Bridge.adInner (π.comp Γ.subtype) J y f f' := by
  set K : Subgroup G := J.comap π with hK_def
  choose a ha using fun i => hπ (y i)
  have hmem : ∀ i (γ : Γ), γ ∈ _root_.Formalism.IndefR.Bridge.stab (π.comp Γ.subtype) J (y i) ↔ (a i)⁻¹ * (γ : G) * a i ∈ K := by
    intro i γ
    unfold _root_.Formalism.IndefR.Bridge.stab
    simp [hK_def, Subgroup.mem_comap, MulAut.conj_apply, ← ha i, map_mul, map_inv]
  have hK0 : ν K ≠ 0 := by rw [h1]; exact one_ne_zero
  have hKt : ν K ≠ ⊤ := by rw [h1]; exact ENNReal.one_ne_top
  have hfin : ∀ i, {γ : Γ | (a i)⁻¹ * (γ : G) * a i ∈ K}.Finite := fun i =>
    _root_.GlobalTheory.InnerClassSum.finite_stab_of_measure ν Γ K h𝓖 hK0 hKt (a i)
  refine ⟨fun i => ((hfin i).subset fun γ hγ => (hmem i γ).1 hγ).to_subtype, ?_⟩
  intro f hf f' hf'
  have hf0 : ∀ (γ : Γ) (h : H) (k : J), f (π γ * h * k) = (χ k : ℂ) • ρ γ (f h) := by
    unfold _root_.Formalism.IndefR.Bridge.AdForms at hf
    exact hf
  have hf0' : ∀ (γ : Γ) (h : H) (k : J), f' (π γ * h * k) = (χ k : ℂ) • ρ γ (f' h) := by
    unfold _root_.Formalism.IndefR.Bridge.AdForms at hf'
    exact hf'
  set Fψ : G → ℂ := fun h => inner ℂ (ρ h⁻¹ (f (π h))) (ρ h⁻¹ (f' (π h))) with hFψ
  have hFψ' : ∀ h, Fψ h = inner ℂ (f (π h)) (f' (π h)) := fun h => hρ _ _ _
  have hleft : ∀ γ ∈ Γ, ∀ x : G, Fψ (γ * x) = Fψ x := by
    intro γ hγ x
    have e := hf0 ⟨γ, hγ⟩ (π x) 1
    have e' := hf0' ⟨γ, hγ⟩ (π x) 1
    simp only [OneMemClass.coe_one, mul_one, map_one, Units.val_one, one_smul] at e e'
    rw [hFψ', hFψ', map_mul, e, e', hρ]
  have hright : ∀ k ∈ K, ∀ x : G, Fψ (x * k) = Fψ x := by
    intro k hk x
    have e := hf0 1 (π x) ⟨π k, hk⟩
    have e' := hf0' 1 (π x) ⟨π k, hk⟩
    simp only [OneMemClass.coe_one, map_one, one_mul, Module.End.one_apply] at e e'
    rw [hFψ', hFψ', map_mul, e, e', inner_smul_left, inner_smul_right, ← mul_assoc,
      Complex.conj_mul', hχ, Complex.ofReal_one, one_pow, one_mul]
  have hreps : ∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a i * k := by
    intro x
    obtain ⟨i, ⟨γ, k, hk⟩, huniq⟩ := hy (π x)
    refine ⟨i, ⟨γ, γ.2, (a i)⁻¹ * (γ : G)⁻¹ * x, ?_, by group⟩, ?_⟩
    · change π ((a i)⁻¹ * (γ : G)⁻¹ * x) ∈ J
      have hk' : π x = π γ * y i * k := hk
      rw [map_mul, map_mul, map_inv, map_inv, ha i, hk']
      simpa [mul_assoc] using k.2
    · rintro j ⟨γ', hγ', k', hk', hx⟩
      refine huniq j ⟨⟨γ', hγ'⟩, ⟨π k', hk'⟩, ?_⟩
      change π x = π γ' * y j * π k'
      rw [hx, map_mul, map_mul, ha j]
  have hmain := _root_.GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset G ν Γ K 𝓖 h𝓖 ho hKt I a hreps
    (fun i => by
      have := (hfin i).image (fun γ : Γ => (γ : G))
      refine this.subset ?_
      rintro z ⟨hz, hzK⟩
      exact ⟨⟨z, hz⟩, hzK, rfl⟩) Fψ hleft hright
  obtain ⟨-, hint, heq⟩ := hmain
  refine ⟨hint, ?_⟩
  change ∫ h in 𝓖, Fψ h ∂ν = _
  rw [heq, h1]
  unfold _root_.Formalism.IndefR.Bridge.adInner
  simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcard : {γ | γ ∈ Γ ∧ (a i)⁻¹ * γ * a i ∈ K}.ncard =
      Nat.card (_root_.Formalism.IndefR.Bridge.stab (π.comp Γ.subtype) J (y i)) := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr
      { toFun := fun z => ⟨⟨z.1, z.2.1⟩, (hmem i _).2 z.2.2⟩
        invFun := fun γ => ⟨γ.1.1, γ.1.2, (hmem i _).1 γ.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [hFψ', ha i, hcard]

open MeasureTheory IsDedekindDomain NumberField Matrix in
open scoped TensorProduct InnerProductSpace Pointwise in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
private lemma norm_character_eq_one_of_finite {A : Type} [Group A] [Finite A] (φ : A →* ℂˣ) (a : A) :
    ‖((φ a : ℂˣ) : ℂ)‖ = 1 := by
  apply Complex.norm_eq_one_of_pow_eq_one (n := Nat.card A) _ Nat.card_pos.ne'
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]


open MeasureTheory IsDedekindDomain NumberField Matrix in
open scoped TensorProduct InnerProductSpace Pointwise in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.InnerClassSum.norm_levFn {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] _root_.Formalism.L2.Herm.Af F)) (L : _root_.Formalism.L2.DIV.LevDat E ℂ n) (x : GL (Fin n) (E ⊗[F] _root_.Formalism.L2.Herm.Af F)) :
    ‖(_root_.Formalism.L2.DIV.levFn β L x : ℂ)‖ = 1 := by
  unfold _root_.Formalism.L2.DIV.levFn _root_.Formalism.L2.DIV.ext1
  simp only [Units.val_mul, Units.coe_prod, norm_mul, norm_prod, norm_character_eq_one_of_finite,
    Finset.prod_const_one, mul_one]
  split_ifs
  · exact norm_character_eq_one_of_finite _ _
  · simp

end GlobalTheory.InnerClassSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicGLComplementarySupportsCommuteStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicGL_complementary_supports_commute : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (h t : GA E a), h ∈ GlobalTheory.JSW.supS (E := E) (a := a) S → GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → h * t = t * h := by
  first | exact @GlobalTheory.JSW.MirSemi.supS_mul_comm | exact GlobalTheory.JSW.MirSemi.supS_mul_comm | (intros; apply GlobalTheory.JSW.MirSemi.supS_mul_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicRealisationHolomorphicMap
section
open MeasureTheory Matrix
open scoped Classical

namespace GlobalTheory.CentSep

theorem apply_basis_eq_smul {L V κ : Type} [Field L] [AddCommGroup V] [Module L V]
    (b : Module.Basis κ L V) (μ : κ → L) (hμ : Function.Injective μ)
    (f g : Module.End L V) (hf : ∀ k, f (b k) = μ k • b k) (hg : g ∘ₗ f = f ∘ₗ g) (k : κ) :
    ∃ c : L, g (b k) = c • b k := by
  refine ⟨b.repr (g (b k)) k, ?_⟩
  set x := g (b k) with hx
  have hfx : f x = μ k • x := by
    have := congrArg (fun φ : Module.End L V => φ (b k)) hg
    simp only [LinearMap.comp_apply, hf] at this
    rw [hx, ← this, map_smul]
  have hrep : ∀ y : V, ∀ j, b.repr (f y) j = μ j * b.repr y j := by
    intro y j
    have key : (b.coord j).comp f = μ j • b.coord j := by
      refine b.ext fun i => ?_
      simp only [LinearMap.comp_apply, hf, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
        LinearMap.smul_apply, smul_eq_mul, Finsupp.single_apply]
      split_ifs with h
      · subst h; rfl
      · simp
    exact congrArg (fun φ : V →ₗ[L] L => φ y) key
  apply b.ext_elem
  intro j
  by_cases hj : j = k
  · subst hj; simp
  · have h1 := hrep x j
    rw [hfx, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
    have h0 : b.repr x j = 0 := by
      have h2 : (μ j - μ k) * b.repr x j = 0 := by linear_combination -h1
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd (hμ (sub_eq_zero.mp h)) hj
      · exact h
    rw [h0, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hj),
      smul_zero]

theorem comm_of_eigenbasis {L V κ : Type} [Field L] [AddCommGroup V] [Module L V]
    (b : Module.Basis κ L V) (μ : κ → L) (hμ : Function.Injective μ)
    (f g h : Module.End L V) (hf : ∀ k, f (b k) = μ k • b k) (hg : g ∘ₗ f = f ∘ₗ g)
    (hh : h ∘ₗ f = f ∘ₗ h) : g ∘ₗ h = h ∘ₗ g := by
  refine b.ext fun k => ?_
  obtain ⟨c, hc⟩ := apply_basis_eq_smul b μ hμ f g hf hg k
  obtain ⟨d, hd⟩ := apply_basis_eq_smul b μ hμ f h hf hh k
  simp only [LinearMap.comp_apply]
  rw [hd, map_smul, hc, map_smul, hd, smul_smul, smul_smul, mul_comm]

theorem comm_of_separable_algClosed {L ι : Type} [Field L] [IsAlgClosed L] [Fintype ι] [DecidableEq ι]
    (A G H : Matrix ι ι L) (hs : A.charpoly.Separable) (hG : G * A = A * G) (hH : H * A = A * H) :
    G * H = H * G := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact Subsingleton.elim _ _
  set f := Matrix.toLin' A with hfdef
  set s : Finset L := A.charpoly.roots.toFinset with hsdef
  have hcard : s.card = Fintype.card ι := by
    rw [hsdef, Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hs),
      IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim]
  have hev : ∀ μ : (s : Set L), Module.End.HasEigenvalue f μ := by
    intro μ
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hfdef, Matrix.charpoly_toLin']
    have hμ := μ.2
    simp only [Finset.mem_coe, hsdef, Multiset.mem_toFinset] at hμ
    exact Polynomial.isRoot_of_mem_roots hμ
  choose v hv using fun μ : (s : Set L) => (hev μ).exists_hasEigenvector
  have hli := Module.End.eigenvectors_linearIndependent f (s : Set L) v hv
  have hc : Fintype.card (s : Set L) = Module.finrank L (ι → L) := by
    simp [hcard]
  haveI : Nonempty (s : Set L) := by
    rw [← Fintype.card_pos_iff, hc, Module.finrank_fintype_fun_eq_card]; exact Fintype.card_pos
  let b := basisOfLinearIndependentOfCardEqFinrank hli hc
  have hb : ∀ k, f (b k) = (k : L) • b k := fun k => by
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank]
    exact (hv k).apply_eq_smul
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
  exact comm_of_eigenbasis b (fun k => (k : L)) Subtype.coe_injective f _ _ hb
    (by rw [← Matrix.toLin'_mul, hG, Matrix.toLin'_mul])
    (by rw [← Matrix.toLin'_mul, hH, Matrix.toLin'_mul])

theorem centraliser_comm_of_separable : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (γ g h : GL ι K),
  (γ : Matrix ι ι K).charpoly.Separable → g * γ = γ * g → h * γ = γ * h → g * h = h * g := by
  intro K _ ι _ _ γ g h hs hg hh
  apply Units.ext
  have hg' := congrArg Units.val hg
  have hh' := congrArg Units.val hh
  simp only [Units.val_mul] at hg' hh' ⊢
  let φ := algebraMap K (AlgebraicClosure K)
  apply Matrix.map_injective φ.injective
  simp only [Matrix.map_mul]
  apply comm_of_separable_algClosed ((γ : Matrix ι ι K).map φ)
  · rw [Matrix.charpoly_map]; exact hs.map
  · rw [← Matrix.map_mul, hg', Matrix.map_mul]
  · rw [← Matrix.map_mul, hh', Matrix.map_mul]

end GlobalTheory.CentSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnFibFrEqOfExLeftEq
section
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.FrameEquiv.anFib_fr_eq_of_ex_left_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y y' : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y) (A' : AnFib X bas idx e x L y'), IsSympl X bas → x ∈ X.dom → SelfD X L → (∀ z, (A'.ex z).left = (A.ex z).left) → ∀ j z, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → A'.fr j z = A.fr j z := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y y' A A' hs hx hL he j z hj
  have hch : ∀ z, ∃ i, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U i := fun z => by
    have h : (A.ex z).left (default : PrimeSpectrum ℂ) ∈ ⨆ i, Xo.univ.t.PP.L.U i := by
      rw [Xo.univ.t.PP.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    exact ⟨i, (GlobalTheory.top_le_preimage_iff_mem _ _).2 hi⟩
  choose ch hc using hch
  have hyx : y'.x = y.x := by
    have h1 : (A.ex 0).left ≫ Xo.univ.t.G.hom = y.x := Over.w (A.ex 0)
    have h2 : (A'.ex 0).left ≫ Xo.univ.t.G.hom = y'.x := Over.w (A'.ex 0)
    rw [← h1, ← h2, he]
  have ne' : ∀ j z, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → A'.fr j z ≠ 0 :=
    fun j z h => A'.fr_ne j z (by rw [he]; exact h)
  let q : (Fin g → ℂ) → ℂ := fun z => A.fr (ch z) z / A'.fr (ch z) z
  have key : ∀ j z, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → q z = A.fr j z / A'.fr j z := fun j z h => by
    have hz : ⊤ ≤ (A.ex z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U (ch z)) := fun p hp => ⟨h hp, hc z hp⟩
    have h1 := A.fr_g j (ch z) z hz
    have h2 := A'.fr_g j (ch z) z (by rw [he]; exact hz)
    rw [he] at h2
    rw [h1, h2, mul_div_mul_left _ _ (left_ne_zero_of_mul (h1 ▸ A.fr_ne j z h))]
  have hq : Differentiable ℂ q := fun z0 => by
    have hO : IsOpen {z | ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z0)} := by
      simpa using (A.hol (Xo.univ.t.PP.L.U (ch z0)) 0).1
    have h' : DifferentiableOn ℂ (A'.fr (ch z0)) {z | ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z0)} := by
      simpa only [he] using A'.fr_hol (ch z0)
    have hd : DifferentiableOn ℂ q {z | ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z0)} :=
      ((A.fr_hol (ch z0)).mul (h'.inv fun z hz => ne' _ z hz)).congr fun z hz =>
        (key _ z hz).trans (div_eq_mul_inv _ _)
    exact hd.differentiableAt (hO.mem_nhds (hc z0))
  let pvh : (Fin r → E) →+ (Fin g → ℂ) := AddMonoidHom.mk' (pv X idx x) GlobalTheory.Dict.FrameSign.pv_add
  let P : L →+ (Fin g → ℂ) := pvh.comp L.subtype.toAddMonoidHom
  have hP : Submodule.span ℝ (Set.range P) = ⊤ := by
    rw [← span_image_pv idx hs hx L (TensLat.span_of_selfD X hL)]
    congr 1
    ext w
    exact ⟨fun ⟨a, ha⟩ => ⟨a.1, a.2, ha⟩, fun ⟨a, ha, h⟩ => ⟨⟨a, ha⟩, h⟩⟩
  have hper : ∀ z (a : L), ‖q (z + P a)‖ = ‖q z‖ := fun z a => by
    have h : ⊤ ≤ (A.ex (z + pv X idx x a)).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z) := by
      rw [GlobalTheory.Dict.FrameSign.ex_add_pv A z a.2]; exact hc z
    have h1 := A.fr_per a a.2 (ch z) z (hc z)
    have h2 := A'.fr_per a a.2 (ch z) z (by rw [he]; exact hc z)
    change ‖q (z + pv X idx x a)‖ = _
    rw [key _ _ h, key _ _ (hc z), h1, h2, norm_div, norm_div, norm_mul, norm_mul, norm_mul, norm_mul,
      A.χ_norm _ a.2, A'.χ_norm _ a.2,
      mul_div_mul_left _ _ (mul_ne_zero one_ne_zero (norm_ne_zero_iff.2 (Complex.exp_ne_zero _)))]
  have hc0 := ReciprocityTheory.ChartRestriction.G.PullbackSections.norm_periodic_const_range P hP q hq hper z 0
  have h0 : q 0 = 1 := by
    have := A'.fr_0 (ch 0) (by rw [he]; exact hc 0)
    rw [hyx, ← A.fr_0 (ch 0) (hc 0)] at this
    change A.fr (ch 0) 0 / A'.fr (ch 0) 0 = 1
    rw [this, div_self (A.fr_ne _ _ (hc 0))]
  rw [h0, key j z hj] at hc0
  exact ((div_eq_one_iff_eq (ne' j z hj)).1 hc0).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMatrixSmoothingModerateGrowth
section
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem smoothMatInf_keeps_modGrowth : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ)
    (α : (Fin n → Fin n → Cinf E) → ℂ), Continuous α → HasCompactSupport α →
    tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W →
    IsModGrowthInf (smoothMatInf α W) :=
  isModGrowthInf_smoothMatInf

end GlobalTheory.JSW.MirCinf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSectionMatrixInvertibleLevelReductionStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanSectionMatrix_invertible_level_reduction : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ρ : Fin n) (j : InfinitePlace E → Fin n), (∀ w, j w ≤ ρ) → (∀ v : Fin n → Cinf E, (∀ w, v (j w) w ≠ 0) → IsUnit (Matrix.of (secMatInf ρ j v)) ∧ toGLInf (Matrix.of (secMatInf ρ j v)) ∈ levSetInf E n (ρ + 1)) ∧ (∀ g ∈ levSetInf E n (ρ + 1), (∀ w, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) (j w) w ≠ 0) → g * (toGLInf (Matrix.of (secMatInf ρ j (rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))))))⁻¹ ∈ levSetInf E n ρ) ∧ ∃ L : (Fin n → Cinf E) →L[ℝ] (Fin n → Fin n → Cinf E), ∀ v, secMatInf ρ j v = secMatInf ρ j 0 + L v := by
  first | (exact @GlobalTheory.JSW.MirCinf.secMatInf_main) | (exact GlobalTheory.JSW.MirCinf.secMatInf_main) | (intros; apply GlobalTheory.JSW.MirCinf.secMatInf_main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardRootsMapPol
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

theorem card_roots_map_pol (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (φ : G.F →+* ℂ) :
    ((P.pol.map φ).roots.toFinset).card = G.n ∧ P.pol.Monic := by
  have hint : IsIntegral G.F (P.γ : G.C) := Algebra.IsIntegral.isIntegral _
  have hmon : P.pol.Monic := minpoly.monic hint
  refine ⟨?_, hmon⟩
  have hsep : (P.pol.map φ).Separable := P.reg.2.map
  have hdeg : (P.pol.map φ).natDegree = G.n := by
    rw [Polynomial.natDegree_map]; exact P.reg.1
  rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep), ← hdeg]
  exact IsAlgClosed.card_roots_eq_natDegree

end GlobalTheory.LKMid.Pair
end

