module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0081
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionTranslateZerosLt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0074

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDVRResidueGaloisAutomorphisms
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory

namespace ResidueGalois

theorem galois_of_isInvariant (A B G : Type) [CommRing A] [CommRing B] [Algebra A B] [Group G]
    [Finite G] [MulSemiringAction G B] [Algebra.IsInvariant A B G] [SMulCommClass G A B]
    (k K : Type) [Field k] [Field K] [Algebra k K] [CharZero k] (p : A →+* k) (q : B →+* K)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (h : ∀ x, algebraMap k K (p x) = q (algebraMap A B x)) :
    FiniteDimensional k K ∧ IsGalois k K ∧
      ∀ τ : K ≃ₐ[k] K, ∃ σ : G, ∀ x, q (σ • x) = τ (q x) := by
  let P : Ideal A := RingHom.ker p
  let Q : Ideal B := RingHom.ker q
  have : P.IsPrime := RingHom.ker_isPrime p
  have : Q.IsPrime := RingHom.ker_isPrime q
  have : Q.LiesOver P := ⟨by
    ext x
    simp only [P, Q, Ideal.under, Ideal.mem_comap, RingHom.mem_ker, ← h, map_eq_zero]⟩
  let _ : Algebra (A ⧸ P) k := (RingHom.kerLift p).toAlgebra
  let _ : Algebra (B ⧸ Q) K := (RingHom.kerLift q).toAlgebra
  let _ : Algebra (A ⧸ P) K := ((algebraMap k K).comp (RingHom.kerLift p)).toAlgebra
  have : IsScalarTower (A ⧸ P) k K := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (A ⧸ P) (B ⧸ Q) K := .of_algebraMap_eq fun x => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact h x
  have : FaithfulSMul (A ⧸ P) k :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective p)
  have : FaithfulSMul (B ⧸ Q) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective q)
  have : IsFractionRing (A ⧸ P) k := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨x, rfl⟩ := hp z
    exact ⟨Ideal.Quotient.mk P x, 1, by rw [map_one, div_one]; rfl⟩
  have : IsFractionRing (B ⧸ Q) K := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨x, rfl⟩ := hq z
    exact ⟨Ideal.Quotient.mk Q x, 1, by rw [map_one, div_one]; rfl⟩
  have hn : Normal k K := Ideal.IsFractionRing.normal G P Q k K
  have hs : Algebra.IsSeparable k K := inferInstance
  refine ⟨Ideal.IsFractionRing.finite_of_isInvariant G P Q k K, { }, fun τ => ?_⟩
  obtain ⟨σ, rfl⟩ := IsFractionRing.stabilizerHom_surjective G P Q k K τ
  exact ⟨σ.1, fun x => (IsFractionRing.stabilizerHom_apply_apply_mk G P Q k K σ x).symm⟩

theorem map_maximalIdeal_le {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (f : A →+* B) (hf : f.IsIntegral) :
    (IsLocalRing.maximalIdeal A).map f ≤ IsLocalRing.maximalIdeal B := by
  have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hf (IsLocalRing.maximalIdeal B)
  rw [Ideal.map_le_iff_le_comap, IsLocalRing.eq_maximalIdeal this]

end ResidueGalois

theorem exists_cDvr_residue_galois : ∀ (V V' : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'], CDvr V → CDvr V' → (∀ n : ℕ, n ≠ 0 → IsUnit (n : V)) → ∀ g : V →+* V', Function.Injective g → g.Finite → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (j : V' →+* W), CDvr W ∧ Function.Injective j ∧ (IsLocalRing.maximalIdeal V').map j ≤ IsLocalRing.maximalIdeal W ∧ (IsLocalRing.maximalIdeal V).map (j.comp g) ≤ IsLocalRing.maximalIdeal W ∧ ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (p : V →+* k) (q : W →+* K), Function.Surjective p → Function.Surjective q → (∀ x, algebraMap k K (p x) = q (j (g x))) → FiniteDimensional k K ∧ IsGalois k K ∧ ∀ τ : K ≃ₐ[k] K, ∃ σ : W ≃+* W, (∀ x, σ (j (g x)) = j (g x)) ∧ ∀ x, q (σ x) = τ (q x) := by
  intro V V' _ _ _ _ _ _ hV _ hu g hg hfin
  obtain ⟨hd, hc, h0⟩ := (cDvr_iff V).1 hV
  let _ : Algebra V V' := g.toAlgebra
  have : Module.Finite V V' := hfin
  have : FaithfulSMul V V' := (faithfulSMul_iff_algebraMap_injective _ _).2 hg
  let K := FractionRing V
  let K' := FractionRing V'
  let _ : Algebra K K' := FractionRing.liftAlgebra V K'
  have : IsScalarTower V K K' := FractionRing.isScalarTower_liftAlgebra V K'
  have : FiniteDimensional K K' := inferInstance
  have : CharZero K := IsFractionRing.charZero_of_isFractionRing V
  let L := IntermediateField.normalClosure K K' (AlgebraicClosure K')
  have : FiniteDimensional K L := inferInstance
  have : IsGalois K L := inferInstance
  let W := integralClosure V L
  have hB : Module.Finite V W := IsIntegralClosure.finite V K L _
  have hBd : IsDiscreteValuationRing W := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr V K L
  have : IsFractionRing W L := IsIntegralClosure.isFractionRing_of_finite_extension V K L W
  let i : V' →ₐ[V] L :=
    ((IsScalarTower.toAlgHom K K' L).restrictScalars V).comp (IsScalarTower.toAlgHom V V' K')
  have hi : Function.Injective i :=
    (algebraMap K' L).injective.comp (IsFractionRing.injective V' K')
  let j : V' →ₐ[V] W := i.codRestrict W fun x => (Algebra.IsIntegral.isIntegral x).map i
  have hj : Function.Injective j := fun x y h => hi (congrArg Subtype.val h)
  have hjg : ∀ x, j (g x) = algebraMap V W x := fun x => j.commutes x
  have hjg' : (j : V' →+* W).comp g = algebraMap V W := RingHom.ext hjg
  have hint : ((j : V' →+* W).comp g).IsIntegral := by
    rw [hjg']
    exact fun x => Algebra.IsIntegral.isIntegral x
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  refine ⟨W, inferInstance, inferInstance, inferInstance, (j : V' →+* W),
    (cDvr_iff W).2 ⟨hBd, CompleteFiniteExtension.isAdicComplete_of_finite_local V W,
      inferInstance⟩, hj,
    ResidueGalois.map_maximalIdeal_le _ (RingHom.IsIntegral.tower_top g _ hint),
    ResidueGalois.map_maximalIdeal_le _ hint, ?_⟩
  intro k K₁ _ _ _ p q hp hq h
  have : CharZero k := ⟨fun m n hmn => by
    by_contra hne
    wlog hlt : m < n generalizing m n
    · exact this n m hmn.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
    have := ((hu (n - m) (by omega)).map p).ne_zero
    rw [map_natCast, Nat.cast_sub hlt.le, hmn, sub_self] at this
    exact this rfl⟩
  have : Algebra.IsInvariant V W (W ≃ₐ[V] W) := Algebra.isInvariant_of_isGalois' V K L W
  have : Finite (W ≃ₐ[V] W) := Finite.of_equiv _ (galRestrict V K L W).toEquiv
  obtain ⟨h₁, h₂, h₃⟩ := ResidueGalois.galois_of_isInvariant V W (W ≃ₐ[V] W) k K₁ p q hp hq
    fun x => (h x).trans (congrArg q (hjg x))
  refine ⟨h₁, h₂, fun τ => ?_⟩
  obtain ⟨σ, hσ⟩ := h₃ τ
  refine ⟨σ.toRingEquiv, fun x => ?_, hσ⟩
  change σ (j (g x)) = j (g x)
  rw [hjg, AlgEquiv.commutes]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInvertibleMatrixChangeOfSpanEq
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.ZH

theorem mul_inv_apply_mem_of_span_le {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    {J : Type} [Fintype J] [DecidableEq J] {b B c : Matrix J J Ω}
    (h : Submodule.span R (Set.range b) ≤ Submodule.span R (Set.range B)) (hc : B * c = 1) (i j : J) :
    (b * c) i j ∈ R := by
  have h1 : ∀ i, ∃ n : J → R, ∑ k, n k • B k = b i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun R).1 (h (Submodule.subset_span ⟨i, rfl⟩))
  choose n hn using h1
  have e : b = (Matrix.of fun i k => (n i k : Ω)) * B := by
    ext i k
    rw [← hn i, Matrix.mul_apply, Finset.sum_apply]
    rfl
  rw [e, Matrix.mul_assoc, hc, Matrix.mul_one]
  exact (n i j).2

theorem exists_mul_eq_one_of_span_le {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    {J : Type} [Fintype J] [DecidableEq J] {b B c : Matrix J J Ω}
    (h : Submodule.span R (Set.range B) ≤ Submodule.span R (Set.range b)) (hc : c * B = 1) :
    ∃ d : Matrix J J Ω, b * d = 1 := by
  have h1 : ∀ i, ∃ n : J → R, ∑ k, n k • b k = B i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun R).1 (h (Submodule.subset_span ⟨i, rfl⟩))
  choose n hn using h1
  have e : B = (Matrix.of fun i k => (n i k : Ω)) * b := by
    ext i k
    rw [← hn i, Matrix.mul_apply, Finset.sum_apply]
    rfl
  refine ⟨c * Matrix.of fun i k => (n i k : Ω), mul_eq_one_comm.1 ?_⟩
  rw [Matrix.mul_assoc, ← e, hc]

theorem RatModel.exists_matrix_map_valF {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    {J : Type} {U : M.Z.Opens} (hU : (U : Set M.Z).Nonempty) (n : Matrix J J Ω)
    (h : ∀ z ∈ U, ∀ i j, n i j ∈ M.O z) : ∃ m : Matrix J J Γ(M.Z, U), m.map (M.res U hU) = n := by
  choose m hm using fun i j =>
    (RatModel.mem_ringOn_iff_exists hU).1 (RatModel.mem_ringOn.2 fun z hz => h z hz i j)
  refine ⟨Matrix.of m, ?_⟩
  ext i j
  exact (M.res_apply U hU _).trans (hm i j)

theorem exists_matrix_mul_eq_one_of_span_eq : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (J : Type) [Fintype J] [DecidableEq J] (W W' : M.Z.Opens) (b B : Matrix J J Ω) (c : Matrix J J Γ(M.Z, W')), (∀ z ∈ W ⊓ W', Submodule.span (M.O z) (Set.range b) = Submodule.span (M.O z) (Set.range B)) → c.map (valF M.pt W') * B = 1 → ∃ m m' : Matrix J J Γ(M.Z, W ⊓ W'), m * m' = 1 ∧ (((W ⊓ W' : M.Z.Opens) : Set M.Z).Nonempty → m.map (valF M.pt (W ⊓ W')) = b * c.map (valF M.pt W')) := by
  intro o Ω _ _ _ M J _ _ W W' b B c h hc
  by_cases hne : ((W ⊓ W' : M.Z.Opens) : Set M.Z).Nonempty
  swap
  · exact ⟨1, 1, Matrix.mul_one _, fun h' => absurd h' hne⟩
  obtain ⟨z₀, hz₀⟩ := id hne
  have hc' : B * c.map (valF M.pt W') = 1 := mul_eq_one_comm.1 hc
  obtain ⟨d, hd⟩ := exists_mul_eq_one_of_span_le (M.O z₀) (h z₀ hz₀).ge hc
  obtain ⟨m, hm⟩ := M.exists_matrix_map_valF hne (b * c.map (valF M.pt W')) fun z hz =>
    mul_inv_apply_mem_of_span_le (M.O z) (h z hz).le hc'
  obtain ⟨m', hm'⟩ := M.exists_matrix_map_valF hne (B * d) fun z hz =>
    mul_inv_apply_mem_of_span_le (M.O z) (h z hz).ge hd
  refine ⟨m, m', ?_, fun _ => ?_⟩
  · apply Matrix.map_injective (M.res_injective _ hne)
    dsimp only
    rw [Matrix.map_mul, hm, hm', Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_assoc,
      ← Matrix.mul_assoc _ B, hc, Matrix.one_mul, hd]
  · rw [← hm]
    ext i j
    exact (M.res_apply _ hne _).symm

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLineBundleSectionsOfUnimodularTuples
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.TupleGlue

private theorem rr {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    resG X h₂ (resG X h₁ s) = resG X (h₂.trans h₁) s := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

variable {X : Scheme.{0}} {N : X.Opens} {J : Type}

private theorem isUnit_res (s : Γ(X, N)) {W : X.Opens} (h : W ≤ X.basicOpen s) :
    IsUnit (resG X (h.trans (X.basicOpen_le s)) s) := by
  have hu : IsUnit (resG X (X.basicOpen_le s) s) := X.toRingedSpace.isUnit_res_basicOpen s
  have := hu.map (resG X h)
  rwa [rr] at this

theorem eq_of_mul_eq (v : J → Γ(X, N)) (hv : N ≤ ⨆ i, X.basicOpen (v i)) {a b : Γ(X, N)}
    (h : ∀ i, a * v i = b * v i) : a = b := by
  refine X.sheaf.eq_of_locally_eq' (fun i => X.basicOpen (v i)) N
    (fun i => homOfLE (X.basicOpen_le _)) hv a b fun i => ?_
  change resG X (X.basicOpen_le (v i)) a = resG X (X.basicOpen_le (v i)) b
  apply (isUnit_res (v i) le_rfl).mul_right_cancel
  have := congrArg (resG X (X.basicOpen_le (v i))) (h i)
  rwa [map_mul, map_mul] at this

theorem exists_mul (u v : J → Γ(X, N)) (hv : N ≤ ⨆ i, X.basicOpen (v i))
    (h : ∀ i j, u i * v j = u j * v i) : ∃ r : Γ(X, N), ∀ j, u j = r * v j := by
  have hq : ∀ i, ∃ q : Γ(X, X.basicOpen (v i)), resG X (X.basicOpen_le (v i)) (u i) =
      q * resG X (X.basicOpen_le (v i)) (v i) := fun i =>
    ⟨resG X (X.basicOpen_le (v i)) (u i) * ↑(isUnit_res (v i) le_rfl).unit⁻¹, by
      rw [_root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]⟩
  choose q hq using hq
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun i => X.basicOpen (v i)) q := by
    intro i j
    change resG X (inf_le_left : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _) (q i) =
      resG X (inf_le_right : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _) (q j)
    have e1 := congrArg (resG X (inf_le_left : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _)) (hq i)
    have e2 := congrArg (resG X (inf_le_right : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _)) (hq j)
    rw [map_mul, rr, rr] at e1 e2
    have e3 := congrArg (resG X ((inf_le_left : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _).trans
      (X.basicOpen_le (v i)))) (h i j)
    rw [map_mul, map_mul, e1, e2] at e3
    have ui := isUnit_res (v i) (inf_le_left : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _)
    have uj := isUnit_res (v j) (inf_le_right : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _)
    apply (ui.mul uj).mul_right_cancel
    linear_combination e3
  obtain ⟨r₀, hr, -⟩ := X.sheaf.existsUnique_gluing' (fun i => X.basicOpen (v i)) N
    (fun i => homOfLE (X.basicOpen_le _)) hv q hcomp
  let r : Γ(X, N) := r₀
  refine ⟨r, fun j => ?_⟩
  refine X.sheaf.eq_of_locally_eq' (fun i => X.basicOpen (v i)) N
    (fun i => homOfLE (X.basicOpen_le _)) hv (u j) (r * v j) fun i => ?_
  change resG X (X.basicOpen_le (v i)) (u j) = resG X (X.basicOpen_le (v i)) (r * v j)
  have hri : resG X (X.basicOpen_le (v i)) r = q i := hr i
  rw [map_mul, hri]
  apply (isUnit_res (v i) le_rfl).mul_right_cancel
  have e3 := congrArg (resG X (X.basicOpen_le (v i))) (h i j)
  rw [map_mul, map_mul, hq i] at e3
  linear_combination -e3

theorem exists_unit_mul (u v : J → Γ(X, N)) (hu : N ≤ ⨆ i, X.basicOpen (u i))
    (hv : N ≤ ⨆ i, X.basicOpen (v i))
    (h : ∀ i j, u i * v j = u j * v i) : ∃ r : Γ(X, N)ˣ, ∀ j, u j = r * v j := by
  obtain ⟨r, hr⟩ := exists_mul u v hv h
  obtain ⟨r', hr'⟩ := exists_mul v u hu fun i j => by linear_combination h j i
  have h1 : r * r' = 1 := eq_of_mul_eq u hu fun i => by
    rw [_root_.mul_assoc, ← hr', ← hr, _root_.one_mul]
  exact ⟨⟨r, r', h1, by rw [_root_.mul_comm, h1]⟩, hr⟩

private theorem cover_res {U : X.Opens} (e : N ≤ U) (v : J → Γ(X, U))
    (hv : U ≤ ⨆ i, X.basicOpen (v i)) : N ≤ ⨆ i, X.basicOpen (resG X e (v i)) := by
  intro x hx
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hv (e hx))
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
  erw [Scheme.basicOpen_res]
  exact ⟨hx, hi⟩

theorem exists_sections : ∀ (X : Scheme.{0}) (A J : Type) (V : A → X.Opens) (t : ∀ a, J → Γ(X, V a)), (∀ a, V a ≤ ⨆ i, X.basicOpen (t a i)) → (∀ a a' i j, resG X (inf_le_left : V a ⊓ V a' ≤ V a) (t a i) * resG X (inf_le_right : V a ⊓ V a' ≤ V a') (t a' j) = resG X (inf_le_left : V a ⊓ V a' ≤ V a) (t a j) * resG X (inf_le_right : V a ⊓ V a' ≤ V a') (t a' i)) → ∃ (g : ∀ a a', Γ(X, V a ⊓ V a')ˣ) (T : J → LB.Sec (⟨A, V, g⟩ : LB X)), ∀ i a, (T i).f a = t a i := by
  intro X A J V t hV h
  choose g hg using fun a a' => exists_unit_mul
    (fun i => resG X (inf_le_left : V a ⊓ V a' ≤ V a) (t a i))
    (fun i => resG X (inf_le_right : V a ⊓ V a' ≤ V a') (t a' i))
    (cover_res _ _ (hV a)) (cover_res _ _ (hV a')) (h a a')
  exact ⟨g, fun i => ⟨fun a => t a i, fun a a' => hg a a' i⟩, fun _ _ => rfl⟩

end GlobalTheory.TupleGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalBasisAlong
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LN.PolFrames

variable {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ) {T T' : Over S} (h : T' ⟶ T)

theorem exists_pullSec [GrpObj G] (s : LB.Sec (LPow G L (N : ℤ) T)) : ∃ s' : LB.Sec (LPow G L (N : ℤ) T'),
    IsPullSec G L N (h ▷ G) (whiskerRight_snd h G) s s' ∧
    ∀ (z : (T' ⊗ G).left) (J), Good L z J →
      sval (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) s' (𝟙 _) z J =
        sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) s (h ▷ G).left z J := by
  obtain ⟨s', h0, h1⟩ := SectionLimit.exists_pull (K := Fin 1) s (h ▷ G).left (fun _ => (snd T' G).left)
    (fun _ => congrArg CommaMorphism.left (whiskerRight_snd h G))
  exact ⟨s', fun j => h0 j _, fun z J hJ => (h1 _ _ z J hJ).trans (by rw [Category.id_comp])⟩

theorem sval_of_isPullSec [GrpObj G] {s : LB.Sec (LPow G L (N : ℤ) T)} {s' : LB.Sec (LPow G L (N : ℤ) T')}
    (hs : IsPullSec G L N (h ▷ G) (whiskerRight_snd h G) s s') (z : (T' ⊗ G).left) (J) (hJ : Good L z J) :
    sval (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) s' (𝟙 _) z J =
      sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) s (h ▷ G).left z J := by
  obtain ⟨s'', h0, h1⟩ := exists_pullSec G L N h s
  obtain rfl : s' = s'' := SecOps.sec_ext fun j => (hs j).trans (h0 j).symm
  exact h1 z J hJ

theorem lin_iff [GrpObj G] (hL : L.IsLB) {n : ℕ} {b : Fin n → LB.Sec (LPow G L (N : ℤ) T)}
    {b' : Fin n → LB.Sec (LPow G L (N : ℤ) T')} (hb : ∀ i, IsPullSec G L N (h ▷ G) (whiskerRight_snd h G) (b i) (b' i))
    (c : Fin n → Γ(T'.left, ⊤)) (s : LB.Sec (LPow G L (N : ℤ) T')) :
    Lin G L N h b c s ↔ ∑ i, c i • (SecM.ofSec G (b' i) : SecM G L N T') = SecM.ofSec G s := by
  let σ := SectionLimit.linSec (fun i => (fst T' G).left.appTop.hom (c i)) b'
  have ev : ∀ j, (∑ i, c i • (SecM.ofSec G (b' i) : SecM G L N T')).1 j = σ.f j := fun j => by
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  have hv : Lin G L N h b c σ := fun z J hJ => by
    rw [SectionScalarValuation.sval_lin (s := σ) (fun i => (fst T' G).left.appTop.hom (c i)) b' (fun _ => rfl) (𝟙 _) z hJ]
    refine Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ?_ (sval_of_isPullSec G L N h (hb i) z J hJ)
    exact (gs_pull (𝟙 _) (fst T' G).left z ⊤ trivial (c i)).trans (by rw [Category.id_comp])
  constructor
  · intro H
    refine Subtype.ext (funext fun j => (ev j).trans ?_)
    exact sec_ext_val hL (fun y J hJ => (hv y J hJ).trans (H y J hJ).symm) j
  · intro H
    obtain rfl : s = σ := SecOps.sec_ext fun j => (congrFun (congrArg Subtype.val H) j).symm.trans (ev j)
    exact hv

theorem basisAlong_iff [GrpObj G] (hL : L.IsLB) {n : ℕ} {b : Fin n → LB.Sec (LPow G L (N : ℤ) T)}
    {b' : Fin n → LB.Sec (LPow G L (N : ℤ) T')} (hb : ∀ i, IsPullSec G L N (h ▷ G) (whiskerRight_snd h G) (b i) (b' i)) :
    BasisAlong G L N h b ↔
      LinearIndependent Γ(T'.left, ⊤) (fun i => (SecM.ofSec G (b' i) : SecM G L N T')) ∧
        Submodule.span Γ(T'.left, ⊤) (Set.range fun i => (SecM.ofSec G (b' i) : SecM G L N T')) = ⊤ := by
  unfold BasisAlong
  simp only [lin_iff G L N h hL hb]
  constructor
  · intro H
    refine ⟨Fintype.linearIndependent_iffₛ.2 fun c c' e i => ?_, eq_top_iff.2 fun x _ => ?_⟩
    · exact congrFun ((H (SecM.toSec G (∑ i, c' i • (SecM.ofSec G (b' i) : SecM G L N T')))).unique e rfl) i
    · exact (Submodule.mem_span_range_iff_exists_fun _).2 (H (SecM.toSec G x)).exists
  · rintro ⟨hli, hsp⟩ s
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hsp.ge (Submodule.mem_top : SecM.ofSec G s ∈ ⊤))
    exact ⟨r, hr, fun r' hr' => funext fun i => Fintype.linearIndependent_iffₛ.1 hli _ _ (hr'.trans hr.symm) i⟩

theorem exists_local_basisAlong (hS : SecBaseChangeSt) [IsLocallyNoetherian S] (P : PolAV S) (hN : 1 ≤ N) (p : S) :
    ∃ V : S.Opens, p ∈ V ∧ ∃ b : Fin (N ^ P.g) → LB.Sec (LPow P.A P.L (N : ℤ) (Over.mk V.ι)),
      ∀ (R : Type) [CommRing R] (χ : Sp R ⟶ V.toScheme),
        BasisAlong P.A P.L N (Over.homMk χ rfl : Over.mk (χ ≫ V.ι) ⟶ Over.mk V.ι) b := by
  obtain ⟨V, hV, b, hb⟩ := hS S P N hN p
  have key : ∀ f : V.toScheme ⟶ S, (overRes (T := baseOver S) V).hom = f →
      ∃ b : Fin (N ^ P.g) → LB.Sec (LPow P.A P.L (N : ℤ) (Over.mk f)), ∀ (R : Type) [CommRing R] (χ : Sp R ⟶ V.toScheme),
        BasisAlong P.A P.L N (Over.homMk χ rfl : Over.mk (χ ≫ f) ⟶ Over.mk f) b := by
    rintro _ rfl
    refine ⟨b, fun R _ χ => ?_⟩
    choose b' hb' _ using fun i => exists_pullSec P.A P.L N (homAt χ) (b i)
    exact (basisAlong_iff P.A P.L N (homAt χ) P.isLB hb').2 (hb R χ b' hb')
  exact ⟨V, hV, key V.ι (Category.comp_id _)⟩

end GlobalTheory.LN.PolFrames
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSectionNonzeroLocusSpecialFibreIff
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SpecialFibreLocus

theorem exists_sec_nonzeroLocus_iff : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : Unif (IsLocalRing.maximalIdeal V) D A G) (ϑ : H0 U.LG.L 1), ∃ θ : LB.Sec D.toPre.P.L, ∀ y : (thickObj V (IsLocalRing.maximalIdeal V) 0 G).left, (fstG (IsLocalRing.maximalIdeal V) 0 G).left y ∈ nonzeroLocus ϑ ↔ (U.gt 0).pG.left y ∈ nonzeroLocus θ := by
  intro hG V _ _ _ D A G _ _ U ϑ
  obtain ⟨f, hf⟩ := GlobalTheory.FewZeros.exists_weight_zero hG U ϑ
  obtain ⟨s, hs⟩ := GlobalTheory.FewZeros.exists_sec_of_formEq_id D.toPre.P.isLB (fun U _ k => by
    have e : toUnit D.toPre.P.A ≫ D.toPre.c 0 = 1 := cPoint_zero (D := D.toPre) _
    have e₁ : padd D.toPre.P.A (𝟙 D.toPre.P.A) 1 = 𝟙 D.toPre.P.A := _root_.mul_one (𝟙 D.toPre.P.A)
    have e₂ : toUnit D.toPre.P.A ≫ η[D.toPre.P.A] = 1 := rfl
    simp [Out.DegPre.famφB, Out.DegPre.famε, Fin.prod_univ_four, e, e₁, e₂]) f
  exact ⟨s, fun y => hs ▸ hf y⟩

end GlobalTheory.SpecialFibreLocus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsValuationSubringIntegralClosureCompleteDVR
section
namespace GlobalTheory.LN

open IsLocalRing

theorem isIntegral_or_isIntegral_inv (O : Type) [CommRing O] [IsDomain O] [CharZero O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    (F : Type) [Field F] [Algebra (FractionRing O) F] [Algebra O F]
    [IsScalarTower O (FractionRing O) F] [Algebra.IsAlgebraic (FractionRing O) F] (x : F) :
    IsIntegral O x ∨ IsIntegral O x⁻¹ := by
  let K := FractionRing O
  let L : IntermediateField K F := IntermediateField.adjoin K {x}
  haveI : FiniteDimensional K L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  haveI : CharZero K := inferInstance
  haveI : Module.Finite O (integralClosure O L) := IsIntegralClosure.finite O K L _
  haveI : IsDiscreteValuationRing (integralClosure O L) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr O K L
  haveI : IsFractionRing (integralClosure O L) L :=
    integralClosure.isFractionRing_of_finite_extension K L
  let y : L := ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩
  let f : L →ₐ[O] F := (IntermediateField.val L).restrictScalars O
  rcases ValuationRing.isInteger_or_isInteger (integralClosure O L) y with ⟨z, hz⟩ | ⟨z, hz⟩
  · left
    have h : IsIntegral O y := hz ▸ z.2
    exact h.map f
  · right
    have h : IsIntegral O y⁻¹ := hz ▸ z.2
    have h' := h.map f
    rwa [map_inv₀] at h'

theorem exists_valuationSubring_isIntegral : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (ϖ : O), GlobalTheory.LN.ArcBase O ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing O) F] [Algebra O F] [IsScalarTower O (FractionRing O) F] [Algebra.IsAlgebraic (FractionRing O) F], ∃ S : ValuationSubring F, ∀ x, x ∈ S ↔ IsIntegral O x := by
  intro O _ _ _ ϖ h F _ _ _ _ _
  rcases h with ⟨hF, -⟩ | ⟨hd, hirr, hc⟩
  · refine ⟨⊤, fun x => ⟨fun _ => ?_, fun _ => trivial⟩⟩
    have ha : IsAlgebraic O x :=
      (IsFractionRing.isAlgebraic_iff O (FractionRing O) F).2 (Algebra.IsAlgebraic.isAlgebraic x)
    letI := hF.toField
    exact ha.isIntegral
  · haveI : IsAdicComplete (maximalIdeal O) O := hirr.maximalIdeal_eq ▸ hc
    exact ⟨⟨(integralClosure O F).toSubring, fun x => isIntegral_or_isIntegral_inv O F x⟩,
      fun x => Iff.rfl⟩

end GlobalTheory.LN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LinearIndependentThetaBasisGeometricFibreStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_thetaBasis_geometric_fibre : LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (w : LB.Iso u.A.L (ρ.P.L.pull u.φ)), w.IsGen → ∀ t : S.J → SecA u.A (PadicAlgCl p) S.N, (∀ i, Moved u w (t i) (ρ.s i)) → LinearIndependent Γ((TFK (R := u.V) (PadicAlgCl p)).left, ⊤) (fun i => SecM.ofSec u.A.A (t i)) := by
  first | exact @GlobalTheory.ZH.FibreIndep.linearIndependent_moved | exact GlobalTheory.ZH.FibreIndep.linearIndependent_moved | (intros; apply GlobalTheory.ZH.FibreIndep.linearIndependent_moved <;> assumption)
end

