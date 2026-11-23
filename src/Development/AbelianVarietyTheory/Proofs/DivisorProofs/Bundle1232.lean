module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0284
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1123
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorIrreducibleModules
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.TensIrr

open Formalism.BasicNotions.TH GlobalTheory.RealLift

section Lin

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem atPl_add (w : ι) (a b : Module.End ℂ (V w)) : atPl w (a + b) = atPl w a + atPl w b :=
  PiTensorProduct.map_update_add _ w a b

theorem atPl_smul (w : ι) (c : ℂ) (a : Module.End ℂ (V w)) : atPl w (c • a) = c • atPl w a :=
  PiTensorProduct.map_update_smul _ w c a

theorem atPl_mul (w : ι) (a b : Module.End ℂ (V w)) : atPl w (a * b) = atPl w a * atPl w b := by
  unfold atPl
  rw [← PiTensorProduct.map_mul]
  congr 1
  funext j
  by_cases h : j = w
  · subst h; simp
  · simp [Function.update_of_ne h]; rfl

theorem atPl_one (w : ι) : atPl (V := V) w 1 = 1 := by
  unfold atPl
  show PiTensorProduct.map (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w LinearMap.id) = 1
  rw [Function.update_eq_self]
  exact PiTensorProduct.map_id

theorem atPl_tprod (w : ι) (L : Module.End ℂ (V w)) (v : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v w (L (v w))) := by
  unfold atPl
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext j
  by_cases h : j = w
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem atPl_local (w : ι) (y : ⨂[ℂ] i, V i) : ∃ s : Finset (V w), ∀ f g : Module.End ℂ (V w),
    (∀ m ∈ s, f m = g m) → atPl w f y = atPl w g y := by
  classical
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    refine ⟨{v w}, fun f g h => ?_⟩
    rw [map_smul, map_smul, atPl_tprod, atPl_tprod, h (v w) (Finset.mem_singleton_self _)]
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    refine ⟨s ∪ t, fun f g h => ?_⟩
    rw [map_add (f := _), map_add (f := _), hs f g (fun m hm => h m (Finset.mem_union_left _ hm)),
      ht f g (fun m hm => h m (Finset.mem_union_right _ hm))]

theorem stable_all (w : ι) {Z : Type} (A : Z → Module.End ℂ (V w)) [Nontrivial (V w)]
    (hirr : ∀ N : Submodule ℂ (V w), (∀ z, ∀ y ∈ N, A z y ∈ N) → N = ⊥ ∨ N = ⊤)
    (hsch : ∀ T : V w →ₗ[ℂ] V w, (∀ z, T ∘ₗ A z = A z ∘ₗ T) → ∃ c : ℂ, T = c • LinearMap.id)
    (N : Submodule ℂ (⨂[ℂ] i, V i)) (hN : ∀ z, ∀ y ∈ N, atPl w (A z) y ∈ N) :
    ∀ f : Module.End ℂ (V w), ∀ y ∈ N, atPl w f y ∈ N := by
  have hadj : ∀ r ∈ Algebra.adjoin ℂ (Set.range A), ∀ y ∈ N, atPl w r y ∈ N := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨z, rfl⟩ := hx; exact hN z
    | algebraMap c =>
      intro y hy
      rw [Algebra.algebraMap_eq_smul_one, atPl_smul, atPl_one]
      exact N.smul_mem c hy
    | add x y _ _ hx hy =>
      intro z hz
      rw [atPl_add]
      exact N.add_mem (hx z hz) (hy z hz)
    | mul x y _ _ hx hy =>
      intro z hz
      rw [atPl_mul]
      exact hx _ (hy z hz)
  intro f y hy
  obtain ⟨s, hs⟩ := atPl_local w y
  obtain ⟨r, hr, hf⟩ := GlobalTheory.IrrTensor.density A hirr hsch f s
  rw [hs f r hf]
  exact hadj r hr y hy

theorem stable_map (N : Submodule ℂ (⨂[ℂ] i, V i))
    (hN : ∀ w (f : Module.End ℂ (V w)), ∀ y ∈ N, atPl w f y ∈ N) (g : ∀ i, Module.End ℂ (V i)) :
    ∀ y ∈ N, PiTensorProduct.map g y ∈ N := by
  classical
  have key : ∀ s : Finset ι, ∀ y ∈ N,
      PiTensorProduct.map (fun i => if i ∈ s then g i else LinearMap.id) y ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro y hy; simpa using hy
    | insert a s ha ih =>
      intro y hy
      have e : PiTensorProduct.map (fun i => if i ∈ insert a s then g i else LinearMap.id) =
          atPl a (g a) ∘ₗ PiTensorProduct.map (fun i => if i ∈ s then g i else LinearMap.id) := by
        unfold atPl
        rw [← PiTensorProduct.map_comp]
        congr 1
        funext j
        by_cases h : j = a
        · subst h; simp [ha]
        · simp [Function.update_of_ne h, Finset.mem_insert, h]
      rw [e]
      exact hN a _ _ (ih y hy)
  intro y hy
  simpa using key Finset.univ y hy

def prodForm (ℓ : ∀ i, Module.Dual ℂ (V i)) : (⨂[ℂ] i, V i) →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap ℓ)

theorem prodForm_tprod (ℓ : ∀ i, Module.Dual ℂ (V i)) (v : ∀ i, V i) :
    prodForm ℓ (PiTensorProduct.tprod ℂ v) = ∏ i, ℓ i (v i) := by
  simp [prodForm]

theorem map_rankOne (ℓ : ∀ i, Module.Dual ℂ (V i)) (u : ∀ i, V i) (y : ⨂[ℂ] i, V i) :
    PiTensorProduct.map (fun i => (ℓ i).smulRight (u i)) y = prodForm ℓ y • PiTensorProduct.tprod ℂ u := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    rw [map_smul, map_smul, PiTensorProduct.map_tprod, prodForm_tprod, smul_assoc]
    congr 1
    simp only [LinearMap.smulRight_apply]
    exact MultilinearMap.map_smul_univ _ _ _
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_smul]

end Lin

end GlobalTheory.TensIrr

namespace GlobalTheory.TensIrr

open Formalism.BasicNotions.TH GlobalTheory.RealLift
open scoped Matrix

section Lin2

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem exists_prodForm_ne (y : ⨂[ℂ] i, V i) (hy : y ≠ 0) : ∃ ℓ : ∀ i, Module.Dual ℂ (V i), prodForm ℓ y ≠ 0 := by
  classical
  let b := fun i => Module.Basis.ofVectorSpace ℂ (V i)
  let B := Basis.piTensorProduct b
  obtain ⟨α, hα⟩ : ∃ α, B.repr y α ≠ 0 := by
    by_contra h
    push_neg at h
    apply hy
    apply B.repr.injective
    ext α
    simp [h α]
  refine ⟨fun i => (b i).coord (α i), ?_⟩
  have e : (Finsupp.lapply α ∘ₗ B.repr.toLinearMap) = prodForm (fun i => (b i).coord (α i)) := by
    refine B.ext fun β => ?_
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply,
      show B β = _ from Basis.piTensorProduct_apply b β, prodForm_tprod]
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self]
    by_cases h : β = α
    · subst h; simp
    · obtain ⟨i, hi⟩ := Function.ne_iff.1 h
      rw [Finsupp.single_apply, if_neg h]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [Finsupp.single_apply, if_neg hi])
  rw [← e]
  simpa using hα

theorem tensor_nontrivial [∀ i, Nontrivial (V i)] : Nontrivial (⨂[ℂ] i, V i) := by
  choose v hv using fun i => exists_ne (0 : V i)
  choose ℓ hℓ using fun i => Module.Projective.exists_dual_eq_one ℂ (hv i)
  refine nontrivial_of_ne (PiTensorProduct.tprod ℂ v) 0 fun h => ?_
  have := congrArg (prodForm ℓ) h
  rw [prodForm_tprod, map_zero] at this
  simp [hℓ] at this

theorem irr_of_stable (N : Submodule ℂ (⨂[ℂ] i, V i))
    (hN : ∀ w (f : Module.End ℂ (V w)), ∀ y ∈ N, atPl w f y ∈ N) : N = ⊥ ∨ N = ⊤ := by
  by_cases h : N = ⊥
  · exact Or.inl h
  right
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨ℓ, hℓ⟩ := exists_prodForm_ne y hy0
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨u, rfl⟩
  have h1 := stable_map N hN (fun i => (ℓ i).smulRight (u i)) y hy
  rw [map_rankOne] at h1
  have h2 := N.smul_mem (prodForm ℓ y)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hℓ, one_smul] at h2

end Lin2

theorem Jm_conjTranspose (R S : ℕ) : (Jm R S)ᴴ = Jm R S := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

theorem Jm_mul_self (R S : ℕ) : Jm R S * Jm R S = 1 := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem mem_upq_comb {R S : ℕ} (Z : Mat R S) (a b : ℂ) (h : star a + b = 0) :
    a • Z + b • (Jm R S * Zᴴ * Jm R S) ∈ upq R S := by
  have hJh := Jm_conjTranspose R S
  have hJJ := Jm_mul_self R S
  set J := Jm R S
  have e1 : J * (Z * J) * J = J * Z := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have e2 : J * (J * Zᴴ * J) = Zᴴ * J := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hb : b = -star a := by linear_combination h
  show (a • Z + b • (J * Zᴴ * J))ᴴ * J + J * (a • Z + b • (J * Zᴴ * J)) = 0
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, hJh, Matrix.conjTranspose_conjTranspose, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, e1, e2, hb]
  simp only [star_neg, star_star, neg_smul]
  abel

theorem upq_decomp {R S : ℕ} (Z : Mat R S) : ∃ X₁ ∈ upq R S, ∃ X₂ ∈ upq R S, Z = X₁ + Complex.I • X₂ := by
  refine ⟨(1 / 2 : ℂ) • Z + (-(1 / 2) : ℂ) • (Jm R S * Zᴴ * Jm R S), mem_upq_comb Z _ _ (by simp),
    (-(Complex.I / 2)) • Z + (-(Complex.I / 2)) • (Jm R S * Zᴴ * Jm R S), mem_upq_comb Z _ _ ?_, ?_⟩
  · simp [Complex.conj_I]; ring
  · rw [smul_add, smul_smul, smul_smul]
    have : Complex.I * -(Complex.I / 2) = 1 / 2 := by ring_nf; simp; ring
    rw [this]
    module

theorem tensor_irr : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (R S : ℕ) (M : ι → Formalism.BasicNotions.TH.GKMod R S),
    (∀ i, Formalism.MainNotions.SchurIrreducible.IrrGK (M i) ∧ GlobalTheory.RealLift.ScalarEnd (M i)) →
    Nontrivial (PiTensorProduct ℂ fun i => (M i).V) ∧
    ∀ N : Submodule ℂ (PiTensorProduct ℂ fun i => (M i).V),
      (∀ i, ∀ Z ∈ Formalism.BasicNotions.TH.upq R S, ∀ y ∈ N, GlobalTheory.RealLift.atPl i ((M i).act Z) y ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro ι _ _ R S M hM
  haveI : ∀ i, Nontrivial (M i).V := fun i => (hM i).1.1
  refine ⟨tensor_nontrivial, fun N hN => irr_of_stable N ?_⟩
  have hgl : ∀ i (Z : Mat R S), ∀ y ∈ N, atPl i ((M i).act Z) y ∈ N := by
    intro i Z y hy
    obtain ⟨X₁, h₁, X₂, h₂, rfl⟩ := upq_decomp Z
    rw [map_add (f := _), map_smul, atPl_add, atPl_smul, LinearMap.add_apply, LinearMap.smul_apply]
    exact N.add_mem (hN i X₁ h₁ y hy) (N.smul_mem _ (hN i X₂ h₂ y hy))
  intro w f y hy
  exact stable_all (V := fun i => (M i).V) w (fun Z => (M w).act Z) (hM w).1.2 (hM w).2 N (hgl w) f y hy

end GlobalTheory.TensIrr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestFunctionsTransportLocalLatticeIsometries
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatTransport

section General

variable {G G' : Type} [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G']
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace G'] [BorelSpace G']

theorem conv_map (j : G ≃ₜ* G') (μ : Measure G) (f g : G → ℂ) :
    GlobalTheory.AutomorphicL2Unitary.conv (μ.map j) (f ∘ j.symm) (g ∘ j.symm) = GlobalTheory.AutomorphicL2Unitary.conv μ f g ∘ j.symm := by
  funext y
  rw [show (μ.map j) = μ.map j.toHomeomorph.toMeasurableEquiv from rfl]
  simp only [GlobalTheory.AutomorphicL2Unitary.conv, Function.comp_apply]
  rw [integral_map_equiv]
  congr 1
  funext x
  change f (j.symm (j x)) * g (j.symm ((j x)⁻¹ * y)) = _
  rw [map_mul, map_inv, j.symm_apply_apply]

theorem typeIdem_map {Q Q' W : Type} [Group Q] [Group Q'] [AddCommGroup W] [Module ℂ W]
    (j : G ≃ₜ* G') (μ : Measure G) {K : Subgroup G} {K' : Subgroup G'} (hK : ∀ g, j g ∈ K' ↔ g ∈ K)
    (r : K →* Q) (r' : K' →* Q') (φ : Q' →* Q) (τ : Representation ℂ Q W)
    (hr : ∀ (k : K) (k' : K'), (k' : G') = j k → φ (r' k') = r k) :
    GlobalTheory.Orb.typeIdem (μ.map j) r' (τ.comp φ) = GlobalTheory.Orb.typeIdem μ r τ ∘ j.symm := by
  funext y
  have hv : (μ.map j).real K' = μ.real K := by
    rw [Measure.real, Measure.real, show (μ.map j) = μ.map j.toHomeomorph.toMeasurableEquiv from rfl,
      MeasurableEquiv.map_apply]
    congr 2
    ext x
    exact hK x
  have hy : ∀ y, y ∈ K' ↔ j.symm y ∈ K := fun y => by
    rw [← hK, j.apply_symm_apply]
  simp only [GlobalTheory.Orb.typeIdem, Function.comp_apply]
  by_cases hg : j.symm y ∈ K
  · rw [dite_eq_left ((hy y).2 hg), dite_eq_left hg, hv]
    simp only [Representation.character, MonoidHom.comp_apply,
      hr ⟨j.symm y, hg⟩ ⟨y, (hy y).2 hg⟩ (j.apply_symm_apply y).symm]
  · rw [dite_eq_right (mt (hy y).1 hg), dite_eq_right hg]

theorem isIrreducible_comp_mulEquiv {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ H' X) (φ : H ≃* H') (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp φ.toMonoidHom : Representation ℂ H X) := by
  haveI : IsSimpleOrder (Subrepresentation ρ) := h
  let e : Subrepresentation (ρ.comp φ.toMonoidHom : Representation ℂ H X) ≃o Subrepresentation ρ :=
    { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
        have h := U.apply_mem_toSubmodule (φ.symm g) hv
        simpa using h⟩
      invFun := fun U => ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (φ g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact e.isSimpleOrder

end General

def glCast {n n' : ℕ} (hr : n' = n) (k : Type) [CommRing k] : GL (Fin n') k ≃* GL (Fin n) k :=
  Units.mapEquiv (Matrix.reindexAlgEquiv k k (finCongr hr)).toMulEquiv

theorem glCast_apply {n n' : ℕ} (hr : n' = n) (k : Type) [CommRing k] (g : GL (Fin n') k) (a b : Fin n) :
    (glCast hr k g : Matrix (Fin n) (Fin n) k) a b = (g : Matrix (Fin n') (Fin n') k) (Fin.cast hr.symm a) (Fin.cast hr.symm b) :=
  rfl

theorem glCast_symm_apply {n n' : ℕ} (hr : n' = n) (k : Type) [CommRing k] (g : GL (Fin n) k) (a b : Fin n') :
    ((glCast hr k).symm g : Matrix (Fin n') (Fin n') k) a b = (g : Matrix (Fin n) (Fin n) k) (Fin.cast hr a) (Fin.cast hr b) :=
  rfl

end GlobalTheory.LatTransport

namespace GlobalTheory.LatTransport

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n n' : ℕ} {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin n') (Fin n') E}
  {L : Submodule (𝓞 E) (Fin n → E)} {L' : Submodule (𝓞 E) (Fin n' → E)} {v : HeightOneSpectrum (𝓞 F)}
  (hr : n' = n) (j : GLoc σ J v ≃ₜ* GLoc σ J' v) (hK : ∀ g, j g ∈ stabLoc σ J' L' v ↔ g ∈ stabLoc σ J L v)
  (s : SplitAt σ J L v) (s' : SplitAt σ J' L' v)
  (he : ∀ g (a b : Fin n'), (s'.equiv (j g)).1 a b = (s.equiv g).1 (a.cast hr) (b.cast hr))
include he


include hK in
theorem mem_iwahori_iff (g : GLoc σ J v) : j g ∈ s'.iwahori ↔ g ∈ s.iwahori := by
  rw [s'.mem_iwahori, s.mem_iwahori, hK]
  refine and_congr_right fun _ => ⟨fun h a b hab => ?_, fun h a b hab => ?_⟩
  · have := h (a.cast hr.symm) (b.cast hr.symm) hab
    rwa [he, Fin.cast_cast, Fin.cast_cast, Fin.cast_eq_self, Fin.cast_eq_self] at this
  · rw [he]
    exact h _ _ hab

theorem map_diag (t : Fin n → (Fv F v)ˣ) : j (s.diag t) = s'.diag fun i => t (i.cast hr) := by
  apply s'.equiv.injective
  ext a b
  rw [he]
  simp only [SplitAt.diag, ContinuousMulEquiv.apply_symm_apply, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply,
    Fin.cast_inj]


include hK in
theorem mem_iwahoriCoset_iff (t : Fin n → (Fv F v)ˣ) (g : GLoc σ J v) :
    j g ∈ s'.iwahoriCoset (fun i => t (i.cast hr)) ↔ g ∈ s.iwahoriCoset t := by
  simp only [SplitAt.iwahoriCoset, DoubleCoset.mem_doubleCoset, ← map_diag hr j s s' he]
  constructor
  · rintro ⟨a, ha, b, hb, e⟩
    refine ⟨j.symm a, (mem_iwahori_iff hr j hK s s' he _).1 (by simpa using ha), j.symm b,
      (mem_iwahori_iff hr j hK s s' he _).1 (by simpa using hb), j.injective ?_⟩
    simp [e, map_mul]
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨j a, (mem_iwahori_iff hr j hK s s' he _).2 ha, j b, (mem_iwahori_iff hr j hK s s' he _).2 hb, by
      simp [map_mul]⟩

include hK in
theorem cosetFn_transfer (t : Fin n → (Fv F v)ˣ) :
    s'.cosetFn (fun i => t (i.cast hr)) = s.cosetFn t ∘ j.symm := by
  funext y
  obtain ⟨g, rfl⟩ := j.surjective y
  change (s'.iwahoriCoset _).indicator 1 (j g) = (s.iwahoriCoset t).indicator 1 (j.symm (j g))
  rw [j.symm_apply_apply]
  by_cases h : g ∈ s.iwahoriCoset t
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((mem_iwahoriCoset_iff hr j hK s s' he t g).2 h)]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt (mem_iwahoriCoset_iff hr j hK s s' he t g).1 h)]

end Local

end GlobalTheory.LatTransport

namespace GlobalTheory.LatTransport

section Types

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n n' : ℕ} {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin n') (Fin n') E}
  {L : Submodule (𝓞 E) (Fin n → E)} {L' : Submodule (𝓞 E) (Fin n' → E)} (hr : n' = n)

def moveTypes (T : TypeData σ J L) (fr : ∀ v : T.S, SplitAt σ J' L' v) : TypeData σ J' L' where
  S := T.S
  frame := fr
  W := T.W
  τ := fun v => (T.τ v).comp (glCast hr (ResF v.1)).toMonoidHom
  irred := fun v => isIrreducible_comp_mulEquiv _ _ (T.irred v)

theorem noFixed_moveTypes (T : TypeData σ J L) (fr : ∀ v : T.S, SplitAt σ J' L' v) (h : NoFixed T) :
    NoFixed (moveTypes hr T fr) := by
  refine ⟨h.1, fun a ha0 han => ?_⟩
  obtain ⟨v, hv⟩ := h.2 a ha0 (by omega)
  refine ⟨v, fun y hy => hv y fun g hg => ?_⟩
  have := hy ((glCast hr (ResF v.1)).symm g) (fun i k hik => ?_)
  · change T.τ v (glCast hr _ ((glCast hr _).symm g)) y = y at this
    rwa [MulEquiv.apply_symm_apply] at this
  · rw [glCast_symm_apply, hg _ _ hik]
    simp [Matrix.one_apply, Fin.cast_inj]

end Types


set_option maxHeartbeats 1000000 in
theorem isTestFin_transport : ∀ (D : D7) (V V' : HSp D), V'.rank = V.rank → ∀ j : ∀ v, GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v, (∀ v, IsLatticeConj (frameLat V) (frameLat V') (j v)) → (∀ v g, j v g ∈ Kv V' v ↔ g ∈ Kv V v) ∧ ∀ (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), ∃ (T' : TypeDataG V') (U' : AuxiliaryPlaceHermitianSpace V'), (NoFixed T → NoFixed T') ∧ ∀ (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) ff, IsTestFin T U μf ff → IsTestFin T' U' (fun v => (μf v).map (j v)) (transfer j ff) := by
  intro D V V' hr j hj
  have h := fun v => _root_.GlobalTheory.LatConjSplit.splitAt_of_isLatticeConj D V V' hr v (j v) (hj v)
  refine ⟨fun v g => (h v).1 g, fun T U => ?_⟩
  choose fr hfr1 hfr2 using fun v => (h v).2
  refine ⟨moveTypes hr T (fun v => fr v (T.frame v)), ⟨U.u, fr U.u U.frame, U.ϖ, U.unif⟩,
    noFixed_moveTypes hr T _, fun μf ff hf => ?_⟩
  obtain ⟨hu, h1, ⟨t, ht, h2⟩, h3, h4⟩ := hf
  have hid : ∀ v : T.S, (moveTypes hr T fun v => fr v (T.frame v)).idem (fun v => (μf v).map (j v)) v =
      T.idem μf v ∘ (j v).symm := fun v =>
    typeIdem_map (j v) (μf v) ((h v).1 ·) (T.frame v).red (fr v (T.frame v)).red (glCast hr (ResF v.1)).toMonoidHom
      (T.τ v) fun k k' e => Units.ext (Matrix.ext fun a b => by
        show (glCast hr (ResF v.1) ((fr v (T.frame v)).red k')).1 a b = ((T.frame v).red k).1 a b
        rw [glCast_apply, hfr2 v (T.frame v) k k' e]
        simp)
  refine ⟨hu, fun v => ?_, ⟨fun i => t (i.cast hr), ?_, ?_⟩,
    fun v hv hv' => comp_mem_SB (h3 v hv hv') (j v).symm.toHomeomorph, ?_⟩
  · obtain ⟨φ, hφ, e⟩ := h1 v
    refine ⟨φ ∘ (j v).symm, comp_mem_SB hφ (j v).symm.toHomeomorph, ?_⟩
    have e1 := conv_map (j v) (μf v) (conv (μf v) (T.idem μf v) φ) (T.idem μf v)
    have e2 := conv_map (j v) (μf v) (T.idem μf v) φ
    have e3 := (congrArg (fun X => conv ((μf v).map (j v)) X (T.idem μf v ∘ (j v).symm)) e2).trans e1
    rewrite [hid v]
    exact (congrArg (· ∘ (j v).symm) e).trans e3.symm
  · obtain ⟨a, ha, rfl⟩ := ht
    exact ⟨fun i => a (i.cast hr), fun x y hxy => ha hxy, rfl⟩
  · show ff U.u ∘ (j U.u).symm = _
    rw [h2]
    exact (cosetFn_transfer hr (j U.u) ((h U.u).1 ·) U.frame _ (hfr1 U.u U.frame) t).symm
  · exact ((IsTestFin.isFinFamily ⟨hu, h1, ⟨t, ht, h2⟩, h3, h4⟩).transfer j (.of_forall fun v g => (h v).1 g)).2

end GlobalTheory.LatTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralRestrictedProductFinprod
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EulerAbs

theorem twOrb_restr_eq_finprod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] [∀ v, IsTopologicalGroup (Y v)] [∀ v, T2Space (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (θ : X →* X) (θv : ∀ v, Y v →* Y v), (∀ v x, pf v (θ x) = θv v (pf v x)) → (∀ v, ∀ k ∈ K v, θv v k ∈ K v) → ∀ (δ : X) (f : X → ℂ) (fv : ∀ v, Y v → ℂ), (∀ x, f x = ∏ᶠ v, fv v (pf v x)) → (∀ v, ∀ a ∈ twCent (θv v) (pf v δ), ∀ b ∈ twCent (θv v) (pf v δ), a * b = b * a) → (∀ v (y : Y v), (rStab fun k : K v => fv v ((y * k)⁻¹ * pf v δ * θv v (y * k))).index ≠ 0) → (∀ v, {q : DoubleCoset.Quotient (twCent (θv v) (pf v δ) : Set (Y v)) (K v : Set (Y v)) | ∃ k ∈ K v, fv v ((Quotient.out q * k)⁻¹ * pf v δ * θv v (Quotient.out q * k)) ≠ 0}.Finite) → (∀ v (y : Y v), twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent (θv v) (pf v δ)) ∧ (twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent (θv v) (pf v δ))) ≠ 0) → (∀ᶠ v in cofinite, fv v = (K v : Set (Y v)).indicator 1 ∧ pf v δ ∈ K v ∧ cptPart (twCent (θv v) (pf v δ)) ≤ K v ∧ ∀ y, y⁻¹ * pf v δ * θv v y ∈ K v → ∃ t ∈ twCent (θv v) (pf v δ), ∃ k ∈ K v, y = t * k) → twOrb θ (⨅ v, (K v).comap (pf v)) δ f = ∏ᶠ v, twOrb (θv v) (K v) (pf v δ) (fv v) := by
  intro X V Y _ _ _ _ _ _ _ _ pf K hX θ θv hθ hθK δ f fv hf hcomm hidx hfin hcpt hev
  rw [GlobalTheory.EulerAbs.twOrb_eq_finsum_twTerm]
  simp only [GlobalTheory.EulerAbs.twOrb_eq_finsum_twTerm]
  exact GlobalTheory.T.finsum_doubleCoset_restrictedProduct_eq_prod pf K hX (twCent θ δ) (fun v => twCent (θv v) (pf v δ)) (_root_.GlobalTheory.EulerAbs.mem_twCent_iff_forall_comp pf K hX θ θv hθ δ) _ _
    (_root_.GlobalTheory.EulerAbs.twTerm_eq_finprod pf K hX θ θv hθ hθK δ f fv hf hcomm hidx hcpt (hev.mono fun v h => ⟨h.1, h.2.1, h.2.2.1⟩))
    (fun v t ht y k hk => _root_.GlobalTheory.EulerAbs.twTerm_inv _ _ _ _ (hcomm v) (hidx v) t ht y k hk)
    (fun v => (hfin v).subset fun q hq => GlobalTheory.T.exists_ne_zero_of_twistedOrbitalPointTerm_ne_zero _ _ _ _ _ hq)
    (hev.mono fun v h => ⟨by rw [h.1]; exact GlobalTheory.T.twistedOrbitalIntegralPointTerm_one_unramified _ _ _ (hθK v) h.2.1 h.2.2.1, fun y hy => by
        obtain ⟨k, hk, hne⟩ := GlobalTheory.T.exists_ne_zero_of_twistedOrbitalPointTerm_ne_zero _ _ _ _ _ hy
        rw [h.1] at hne
        have hm : (y * k)⁻¹ * pf v δ * θv v (y * k) ∈ K v := by
          by_contra hc; exact hne (Set.indicator_of_notMem hc _)
        obtain ⟨t, ht, k', hk', he⟩ := h.2.2.2 (y * k) hm
        exact ⟨t, ht, k' * k⁻¹, mul_mem hk' (inv_mem hk), by rw [← mul_assoc, ← he, mul_inv_cancel_right]⟩⟩)

end GlobalTheory.EulerAbs
end

