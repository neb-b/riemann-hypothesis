module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Formalism.HarderNarasimhan.StatementPl
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0893
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0890
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0933
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEigenvaluesClasses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0927
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0996
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0872
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormOutsideFiniteSet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0969
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0947
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormEqOfCsq
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

noncomputable section

namespace GlobalTheory.IsoDeg

open Module
open scoped ComplexConjugate

variable {K V W : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]

theorem form_eq_of_csq (n : HermFam K V) (n' : HermFam K W) (e : V ≃ₗ[K] W)
    (hc : ∀ σ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → V), csq n σ c g = csq n' σ c fun i => e (g i))
    (σ : K →+* ℂ) (x y : V) : n'.form σ (e x) (e y) = n.form σ x y := by
  have h1 := hc σ 2 ![1, 1] ![x, y]
  have h2 := hc σ 2 ![1, Complex.I] ![x, y]
  have hx := hc σ 1 ![1] ![x]
  have hy := hc σ 1 ![1] ![y]
  simp only [csq, Fin.sum_univ_two, Fin.sum_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.head_cons, map_one, one_mul, mul_one, Complex.add_re] at h1 h2 hx hy
  rw [← n.conj_symm σ x y, ← n'.conj_symm σ (e x) (e y)] at h1 h2
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
    Complex.conj_I, Complex.neg_re, Complex.neg_im, Complex.mul_im] at h1 h2
  apply Complex.ext
  · linarith
  · nlinarith

theorem deg_map_eq : ∀ (K V W : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (n : HermFam K V) (n' : HermFam K W) (e : V ≃ₗ[K] W), (∀ σ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → V), csq n σ c g = csq n' σ c fun i => e (g i)) → ∀ L : Submodule (𝓞 K) V, L.FG → deg n' (L.map (e.toLinearMap.restrictScalars (𝓞 K))) = deg n L := by
  intro K V W _ _ _ _ _ _ _ _ _ _ n n' e hc L hL
  set f := e.toLinearMap.restrictScalars (𝓞 K) with hf
  have hfi : Function.Injective f := e.injective
  obtain ⟨v, hv⟩ := exists_isFrame L hL
  have hfv : IsFrame K (L.map f) (fun i => e (v i)) := by
    refine ⟨fun i => ⟨v i, hv.1 i, rfl⟩, hv.2.1.map' e.toLinearMap e.ker, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have h0 : e x ∈ (Submodule.span K (Set.range v)).map e.toLinearMap := ⟨x, hv.2.2 hx, rfl⟩
    rw [Submodule.map_span, ← Set.range_comp] at h0
    exact h0
  rw [arakelovDegree_eq_degreeOfFamily n' (hL.map f) hfv, arakelovDegree_eq_degreeOfFamily n hL hv]
  unfold degreeOfFamily
  have hs : Submodule.span (𝓞 K) (Set.range fun i => e (v i)) =
      (Submodule.span (𝓞 K) (Set.range v)).map f := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hidx : (Submodule.span (𝓞 K) (Set.range fun i => e (v i))).toAddSubgroup.relIndex
      (L.map f).toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex L.toAddSubgroup := by
    have key : ∀ P : Submodule (𝓞 K) V, (P.map f).toAddSubgroup = P.toAddSubgroup.map f.toAddMonoidHom :=
      fun P => by
        ext y
        simp only [Submodule.mem_toAddSubgroup, Submodule.mem_map, AddSubgroup.mem_map,
          LinearMap.toAddMonoidHom_coe]
    rw [hs, key, key]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hfi
  have hg : ∀ σ, n'.gram σ (fun i => e (v i)) = n.gram σ v := fun σ => by
    ext i j
    simp only [HermFam.gram, Matrix.of_apply]
    exact GlobalTheory.IsoDeg.form_eq_of_csq n n' e hc σ (v i) (v j)
  simp only [hidx, hg]

end GlobalTheory.IsoDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertDbl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev UD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) : Type := UG (cA σ) (dbl (incM F W.J))

def matD {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g : UD σ W) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  g.1.1

def latAtD {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : Set (Fin d ⊕ Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  {z | (fun i => z (Sum.inl i)) ∈ GlobalTheory.InertSph.latAt W v ∧ (fun i => z (Sum.inr i)) ∈ GlobalTheory.InertSph.latAt W v}

def KAtD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : Set (UD σ W) :=
  {g | At (evFin F v) (matD g - 1) ∧
    ∀ z ∈ latAtD W v, matD g *ᵥ z ∈ latAtD W v ∧ matD g⁻¹ *ᵥ z ∈ latAtD W v}

def antiCols (d : ℕ) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := Matrix.fromRows 1 (-1)

def ParD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : Set (UD σ W) :=
  {p | p ∈ KAtD σ W v ∧ ∃ t : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), matD p * diagCols (Fin d) = diagCols (Fin d) * (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))}

def NabD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : Set (UD σ W) :=
  {n | n ∈ KAtD σ W v ∧ matD n * antiCols d = antiCols d ∧
    ∃ b : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), matD n * diagCols (Fin d) = diagCols (Fin d) + antiCols d * b}

theorem fromBlocks_mem {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (k : UA σ W.J) :
    ((Matrix.fromBlocks (mat k) 0 0 1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))ᵀ * dbl (incM F W.J) *
      (Matrix.fromBlocks (mat k) 0 0 1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).map (cA σ) = dbl (incM F W.J) := by
  have hk : (mat k)ᵀ * incM F W.J * (mat k).map (cA σ) = incM F W.J := k.2
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, dbl, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hk, Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ))]

def inlD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) : UA σ W.J →* UD σ W where
  toFun k := ⟨⟨Matrix.fromBlocks (mat k) 0 0 1, Matrix.fromBlocks (mat k⁻¹) 0 0 1,
      by rw [Matrix.fromBlocks_multiply]; simp [mat, ← Matrix.GeneralLinearGroup.coe_mul, Matrix.fromBlocks_one],
      by rw [Matrix.fromBlocks_multiply]; simp [mat, ← Matrix.GeneralLinearGroup.coe_mul, Matrix.fromBlocks_one]⟩,
    fromBlocks_mem k⟩
  map_one' := by
    apply Subtype.ext; apply Units.ext
    show Matrix.fromBlocks (mat (1 : UA σ W.J)) 0 0 1 = 1
    simp [mat, Matrix.fromBlocks_one]
  map_mul' a b := by
    apply Subtype.ext; apply Units.ext
    show Matrix.fromBlocks (mat (a * b)) 0 0 1 = Matrix.fromBlocks (mat a) 0 0 1 * Matrix.fromBlocks (mat b) 0 0 1
    rw [Matrix.fromBlocks_multiply]; simp [mat]

theorem matD_inlD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (k : UA σ W.J) :
    matD (inlD σ W k) = Matrix.fromBlocks (mat k) 0 0 1 := rfl

def dblFun {κ : Type} (Ψ : (κ → AF F) → ℂ) : (κ ⊕ κ → AF F) → ℂ := boxFun Ψ fun x => star (Ψ x)

end GlobalTheory.InertDbl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullSumRegroup
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.Regroup

variable {p : ℕ} [Fact p.Prime]

def formOf {G : HTGroup p} (P : Pair G) : Form G := ⟨P.β, P.sym, P.trivAf, P.trivR⟩

def ofGrp {G : HTGroup p} (F : Form G) (r : grp G F.β)
    (h : (minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧
      (minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) : Pair G :=
  ⟨F.β, (r : G.Cˣ × ℚˣ).1, (r : G.Cˣ × ℚˣ).2, F.sym, r.2.1, h, F.trivAf, F.trivR⟩

def phi {G : HTGroup p} (q : FCls G) (Q : Cls G) : ConjClasses (grp G (Quot.out q).β) :=
  if h : ∃ y : G.Cˣ, (∃ s : ℚ, 0 < s ∧
      ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s * (y * (Quot.out q).β * sh G y)) ∧
      ((y⁻¹ * (Quot.out Q).γ * y, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β
  then ConjClasses.mk ⟨_, h.choose_spec.2⟩ else ConjClasses.mk 1

theorem phi_spec {G : HTGroup p} (q : FCls G) (Q : Cls G) (y : G.Cˣ) (s : ℚ) (hs : 0 < s)
    (hβ : ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s * (y * (Quot.out q).β * sh G y))
    (hm : ((y⁻¹ * (Quot.out Q).γ * y, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β) :
    ∃ y₁ : G.Cˣ, ∃ s₁ : ℚ, 0 < s₁ ∧
      ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s₁ * (y₁ * (Quot.out q).β * sh G y₁) ∧
      ∃ hm₁ : ((y₁⁻¹ * (Quot.out Q).γ * y₁, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β,
        phi q Q = ConjClasses.mk ⟨_, hm₁⟩ := by
  have h : ∃ y : G.Cˣ, (∃ s : ℚ, 0 < s ∧
      ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s * (y * (Quot.out q).β * sh G y)) ∧
      ((y⁻¹ * (Quot.out Q).γ * y, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β := ⟨y, ⟨s, hs, hβ⟩, hm⟩
  obtain ⟨⟨s₁, hs₁, hβ₁⟩, hm₁⟩ := h.choose_spec
  exact ⟨h.choose, s₁, hs₁, hβ₁, hm₁, by rw [phi, dite_eq_left h]⟩

end GlobalTheory.LKCx.Regroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussAbsProdLeOne
section
set_option autoImplicit false

open NumberField MvPolynomial

namespace GlobalTheory.GaussSubst

variable {E : Type} [Field E] [NumberField E] (v : FinitePlace E)

theorem gaussAbs_nonneg {τ : Type} (f : MvPolynomial τ E) : 0 ≤ ReciprocityTheory.MultiplicativeHeights.gaussAbs v f := by
  unfold ReciprocityTheory.MultiplicativeHeights.gaussAbs
  exact NNReal.coe_nonneg _

theorem gaussAbs_mul_le {τ : Type} (f g : MvPolynomial τ E) :
    ReciprocityTheory.MultiplicativeHeights.gaussAbs v (f * g) ≤ ReciprocityTheory.MultiplicativeHeights.gaussAbs v f * ReciprocityTheory.MultiplicativeHeights.gaussAbs v g := by
  classical
  have hf := gaussAbs_nonneg v f
  have hg := gaussAbs_nonneg v g
  refine ReciprocityTheory.MultiplicativeHeights.gauss_abs_le_of_coeff_le v _ (mul_nonneg hf hg) fun u => ?_
  rw [MvPolynomial.coeff_mul]
  refine ReciprocityTheory.MultiplicativeHeights.finite_place_sum_le v _ _ (mul_nonneg hf hg) fun x _ => ?_
  rw [map_mul]
  exact mul_le_mul (ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs v f _) (ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs v g _)
    (apply_nonneg v _) hf

theorem gaussAbs_one_le {τ : Type} : ReciprocityTheory.MultiplicativeHeights.gaussAbs v (1 : MvPolynomial τ E) ≤ 1 := by
  classical
  refine ReciprocityTheory.MultiplicativeHeights.gauss_abs_le_of_coeff_le v _ zero_le_one fun s => ?_
  rw [MvPolynomial.coeff_one]
  split_ifs <;> simp

theorem gaussAbs_pow_le_one {τ : Type} (f : MvPolynomial τ E)
    (hf : ReciprocityTheory.MultiplicativeHeights.gaussAbs v f ≤ 1) (n : ℕ) : ReciprocityTheory.MultiplicativeHeights.gaussAbs v (f ^ n) ≤ 1 := by
  induction n with
  | zero => simpa using gaussAbs_one_le v
  | succ n ih =>
    rw [pow_succ]
    exact (gaussAbs_mul_le v _ _).trans
      (mul_le_one₀ ih (gaussAbs_nonneg v f) hf)

theorem gaussAbs_prod_le_one {τ ι : Type} (t : Finset ι) (F : ι → MvPolynomial τ E)
    (hF : ∀ i ∈ t, ReciprocityTheory.MultiplicativeHeights.gaussAbs v (F i) ≤ 1) :
    ReciprocityTheory.MultiplicativeHeights.gaussAbs v (∏ i ∈ t, F i) ≤ 1 := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using gaussAbs_one_le v
  | insert a t ha ih =>
    rw [Finset.prod_insert ha]
    exact (gaussAbs_mul_le v _ _).trans
      (mul_le_one₀ (hF a (Finset.mem_insert_self a t)) (gaussAbs_nonneg v _)
        (ih fun i hi => hF i (Finset.mem_insert_of_mem hi)))

theorem gaussAbs_C_mul_le {τ : Type} (a : E) (f : MvPolynomial τ E)
    (hf : ReciprocityTheory.MultiplicativeHeights.gaussAbs v f ≤ 1) : ReciprocityTheory.MultiplicativeHeights.gaussAbs v (C a * f) ≤ v a := by
  refine ReciprocityTheory.MultiplicativeHeights.gauss_abs_le_of_coeff_le v _ (apply_nonneg v _) fun s => ?_
  rw [MvPolynomial.coeff_C_mul, map_mul]
  exact mul_le_of_le_one_right (apply_nonneg v _)
    ((ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs v f s).trans hf)

theorem gaussAbs_aeval_le : ∀ (E : Type) [Field E] [NumberField E] (v : FinitePlace E) (σ τ : Type)
    (φ : σ → MvPolynomial τ E) (g : MvPolynomial σ E),
    (∀ i, ReciprocityTheory.MultiplicativeHeights.gaussAbs v (φ i) ≤ 1) →
      ReciprocityTheory.MultiplicativeHeights.gaussAbs v (aeval φ g) ≤ ReciprocityTheory.MultiplicativeHeights.gaussAbs v g := by
  intro E _ _ v σ τ φ g h
  have h0 := gaussAbs_nonneg v g
  refine ReciprocityTheory.MultiplicativeHeights.gauss_abs_le_of_coeff_le v _ h0 fun t => ?_
  rw [aeval_def, eval₂_eq, coeff_sum]
  refine ReciprocityTheory.MultiplicativeHeights.finite_place_sum_le v _ _ h0 fun s _ => ?_
  have hprod : ReciprocityTheory.MultiplicativeHeights.gaussAbs v (∏ i ∈ s.support, φ i ^ s i) ≤ 1 :=
    gaussAbs_prod_le_one v _ _ fun i _ => gaussAbs_pow_le_one v _ (h i) _
  have hC := gaussAbs_C_mul_le v (AddMonoidAlgebra.coeff g s) _ hprod
  rw [MvPolynomial.algebraMap_eq]
  exact (ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs v _ t).trans
    (hC.trans (ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs v g s))

end GlobalTheory.GaussSubst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalSectionsPolynomialGrowth
section
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem hdim_twist_zero_le_of_cls_eq_add_nsmul (k : Type) [Field k] [Infinite k] (X : Scheme.{0})
    [Algebra k Γ(X, ⊤)] (hX : IsProjOver (strHom k (X := X))) (F : X.Modules) [IsFiniteQC F]
    (B : LB X) (hB : B.IsLB) (s : B.Sec) (hs : Mono (cutHom F hB s)) (j : ℕ) :
    ∀ (M M' : LB X) (hM : M.IsLB) (hM' : M'.IsLB), cls M hM = cls M' hM' + j • cls B hB →
      hdim k (twist F M') 0 ≤ hdim k (twist F M) 0 := by
  induction j with
  | zero =>
    intro M M' hM hM' e
    obtain ⟨e⟩ := nonempty_twist_iso_of_cls_eq F hM hM' (by simpa using e)
    exact (hdim_congr k 0 e).ge
  | succ j ih =>
    intro M M' hM hM' e
    obtain ⟨N, hN, eN⟩ := cls_surj (cls M' hM' + j • cls B hB)
    exact (ih N M' hN hM' eN).trans
      (GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hX F B M N hB hM hN s hs (by rw [e, eN, succ_nsmul, add_assoc])).2.2

theorem exists_hdim_twist_lbPow_zero_le :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), L.IsLB → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) 0 ≤ C * (m + 1) ^ d := by
  intro k _ _ X _ hX d L hL F _ hF
  have := isNoetherian_of_isProjOver hX
  obtain ⟨-, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hX
  obtain ⟨D, hD, eD⟩ := cls_surj (-cls L hL)
  obtain ⟨n, hn, hn1⟩ := ((tendsto_natCast_atTop_atTop (R := ℤ).eventually
    (hA.eventually_exists_mono_cutHom hD F)).and (eventually_ge_atTop 1)).exists
  obtain ⟨B, hB, eB⟩ := cls_surj (cls D hD + (n : ℤ) • cls A hA.isLB)
  obtain ⟨s, hs⟩ := hn B hB eB
  have hH : IsAmpleLB (lbPow A n) := (isAmpleLB_pow_iff hA.isLB hn1).2 hA
  have h₁ : ∀ m : ℕ, hdim k (twist F (lbPow L m)) 0 ≤ hdim k (twist F (lbPow (lbPow A n) m)) 0 :=
    fun m => hdim_twist_zero_le_of_cls_eq_add_nsmul k X hX F B hB s hs m _ _
      (isLB_lbPow hH.isLB m) (isLB_lbPow hL m) (by
        rw [cls_lbPow hH.isLB, cls_lbPow hA.isLB, cls_lbPow hL, eB, eD, natCast_zsmul, ← nsmul_add,
          add_neg_cancel_left])
  obtain ⟨C, m₀, hC⟩ := GlobalTheory.T.asymptotic_riemannRoch_ample_coherent k X hX d F hF _ hH
  set a := interNum k F (fun _ : Fin d => lbPow A n)
  set h : ℕ → ℕ := fun m => hdim k (twist F (lbPow (lbPow A n) m)) 0 with hh
  refine ⟨a.natAbs + C * d + ∑ i ∈ Finset.range m₀, h i, fun m => (h₁ m).trans ?_⟩
  change h m ≤ _
  have hp : 1 ≤ (m + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos m)
  rcases lt_or_ge m m₀ with hm | hm
  · have : h m ≤ ∑ i ∈ Finset.range m₀, h i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hm)
    exact (this.trans (Nat.le_add_left _ _)).trans (Nat.le_mul_of_pos_right _ hp)
  · have h₂ : (d.factorial : ℤ) * (h m : ℤ) - a * (m : ℤ) ^ d ≤
        C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) := (abs_le.1 (hC m hm)).2
    have h₃ : (h m : ℤ) ≤ (d.factorial : ℤ) * (h m : ℤ) :=
      le_mul_of_one_le_left (by positivity) (by exact_mod_cast d.factorial_pos)
    have h₄ : a * (m : ℤ) ^ d ≤ |a| * ((m : ℤ) + 1) ^ d :=
      (mul_le_mul_of_nonneg_right (le_abs_self a) (by positivity)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) d) (abs_nonneg a))
    have h₅ : (C : ℤ) * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ d) := by
      gcongr
      · have : (0 : ℤ) ≤ m := by positivity
        linarith
      · exact Nat.sub_le _ _
    have h₆ : (h m : ℤ) ≤ ((a.natAbs + C * d) * (m + 1) ^ d : ℕ) := by
      push_cast
      linarith
    exact (by exact_mod_cast h₆ : h m ≤ _).trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchDerivativeOnPureTensorUniqueAdelicOperato
section
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn

namespace GlobalTheory.SDUnique

theorem proj_mem_adm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (x₀ : κ → AF F) :
    (LinearMap.proj x₀ : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x₀ i).2) • ((BoundedContinuousFunction.evalCLM ℂ
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x₀ i).1)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => ?_⟩
  simp [pureA, mul_comm]

theorem sd_unique : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ f₂ : SInf F κ}, SD T f f₁ → SD T f f₂ → f₁ = f₂ := by
  intro F _ _ κ _ T f f₁ f₂ h₁ h₂
  have hg := GlobalTheory.SchANonzero.indicator_intPts_mem_SB F κ
  refine SchwartzMap.ext fun x => ?_
  let x₀ : κ → AF F := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), 0)
  have h := (h₁ _ hg _ (proj_mem_adm x₀)).unique (h₂ _ hg _ (proj_mem_adm x₀))
  have h0 : (fun _ : κ => (0 : Af F)) ∈ GlobalTheory.SchANonzero.intPts F κ := fun i _ v =>
    zero_mem (v.adicCompletionIntegers F)
  have e : ∀ φ : SInf F κ, pureA F φ ((GlobalTheory.SchANonzero.intPts F κ).indicator 1) x₀ = φ x := fun φ => by
    have hx : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x₀ i).1) = x :=
      funext fun i => RingEquiv.apply_symm_apply _ _
    have h1 : (GlobalTheory.SchANonzero.intPts F κ).indicator (1 : (κ → Af F) → ℂ) (fun i => (x₀ i).2) = 1 :=
      Set.indicator_of_mem h0 _
    unfold pureA
    rw [hx]
    exact (congrArg (φ x * ·) h1).trans (mul_one _)
  exact (e f₁).symm.trans (h.trans (e f₂))

end GlobalTheory.SDUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightPositiveDiagonalLeSumAddInv
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem height_diagonal_le_sum (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (r : Fin a → ℝ)
    (d : GL (Fin a) (Cinf E)) (hr : ∀ i, 0 < r i)
    (hd : d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ))) :
    height d ≤ 1 + ∑ i, r i + ∑ i, (r i)⁻¹ := by
  classical
  have hinv : (d⁻¹).val = Matrix.diagonal (fun i => fun _ => (((r i)⁻¹ : ℝ) : ℂ)) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hd, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i w
    have : (r i : ℂ) ≠ 0 := by exact_mod_cast (hr i).ne'
    simp [this]
  have key : ∀ s : Fin a → ℝ, (∀ i, 0 < s i) →
      ‖toL (Matrix.diagonal (fun i => fun (_ : InfinitePlace E) => ((s i : ℝ) : ℂ)))‖ ≤ ∑ i, s i := by
    intro s hs
    have h0 : 0 ≤ ∑ i, s i := Finset.sum_nonneg fun i _ => (hs i).le
    refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j =>
      (pi_norm_le_iff_of_nonneg h0).2 fun w => ?_
    change ‖(Matrix.diagonal (fun i => fun (_ : InfinitePlace E) => ((s i : ℝ) : ℂ))) i j w‖ ≤ _
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hs i)]
      exact Finset.single_le_sum (fun k _ => (hs k).le) (Finset.mem_univ i)
    · rw [Matrix.diagonal_apply_ne _ hij]
      simpa using h0
  have h1 := key r hr
  have h2 := key (fun i => (r i)⁻¹) (fun i => inv_pos.2 (hr i))
  unfold GlobalTheory.CuspRep.height
  rw [hd, hinv]
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergRhoArchimedeanAdelicPureTensorStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergRho_archimedean_adelicPureTensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ),
    IsStd ψ → ∀ u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u → ∀ f : SInf F κ,
      ∃ f₁ : SInf F κ, ∀ h : (κ → Af F) → ℂ, d.rho ψ u (pureA F f h) = pureA F f₁ h := by
  first | exact @GlobalTheory.ArchHeisPure.rho_pureA | exact GlobalTheory.ArchHeisPure.rho_pureA | (intros; apply GlobalTheory.ArchHeisPure.rho_pureA <;> assumption)
end

