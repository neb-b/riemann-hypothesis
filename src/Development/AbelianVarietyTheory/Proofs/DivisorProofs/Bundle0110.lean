module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanEqTopIffDense
section
namespace GlobalTheory.Morita

structure MatrixUnits (R : Type*) [CommRing R] (N : Type*) [AddCommGroup N] [Module R N]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where

  E : ι → ι → Module.End R N
  mul_eq : ∀ i j k l, E i j * E k l = if j = k then E i l else 0
  sum_diag : ∑ i, E i i = 1

variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace MatrixUnits

variable (U : MatrixUnits R N ι)

theorem apply_apply (i j k l : ι) (x : N) : U.E i j (U.E k l x) = if j = k then U.E i l x else 0 := by
  have h := LinearMap.congr_fun (U.mul_eq i j k l) x
  rw [Module.End.mul_apply] at h
  rw [h]; split_ifs <;> simp

theorem sum_apply (x : N) : ∑ i, U.E i i x = x := by
  have h := LinearMap.congr_fun U.sum_diag x
  simpa [LinearMap.sum_apply] using h

def corner (a : ι) : Submodule R N := LinearMap.range (U.E a a)

theorem mem_corner_iff (a : ι) (x : N) : x ∈ U.corner a ↔ U.E a a x = x := by
  constructor
  · rintro ⟨y, rfl⟩; rw [U.apply_apply]; simp
  · intro h; exact ⟨x, h⟩

theorem apply_mem_corner (a i : ι) (x : N) : U.E a i x ∈ U.corner a := ⟨U.E a i x, by rw [U.apply_apply]; simp⟩

def toPi (a : ι) : N ≃ₗ[R] (ι → U.corner a) where
  toFun x i := ⟨U.E a i x, U.apply_mem_corner a i x⟩
  map_add' x y := by ext i; simp
  map_smul' r x := by ext i; simp
  invFun v := ∑ i, U.E i a (v i)
  left_inv x := by
    simp only
    conv_rhs => rw [← U.sum_apply x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [U.apply_apply]; simp
  right_inv v := by
    ext j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, U.apply_apply]
    simp [(U.mem_corner_iff a _).1 (v j).2]

theorem toPi_apply (a : ι) (x : N) (i : ι) : ((U.toPi a x) i : N) = U.E a i x := rfl

theorem toPi_E (a i j : ι) (x : N) : U.toPi a (U.E i j x) = Pi.single i (U.toPi a x j) := by
  ext k
  rw [toPi_apply, U.apply_apply]
  by_cases h : k = i
  · subst h; simp [toPi_apply]
  · simp [h, Pi.single_apply]

end MatrixUnits

def stdUnits (M : Type*) [AddCommGroup M] [Module R M] : MatrixUnits R (ι → M) ι where
  E i j := LinearMap.single R (fun _ => M) i ∘ₗ LinearMap.proj j
  mul_eq i j k l := by
    ext x m
    by_cases h : j = k
    · subst h; simp [Pi.single_apply]
    · simp [h, Pi.single_apply]
  sum_diag := by
    ext x m
    simp [LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply]

end GlobalTheory.Morita

namespace GlobalTheory.Morita
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

end GlobalTheory.Morita

namespace GlobalTheory.Morita.MatrixUnits
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (U : MatrixUnits R N ι)

end GlobalTheory.Morita.MatrixUnits

namespace GlobalTheory.Morita.MatrixUnits
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (U : MatrixUnits R N ι)

section semilinear

variable {σ : R →+* R} (F : N →ₛₗ[σ] N)

end semilinear

end GlobalTheory.Morita.MatrixUnits

namespace GlobalTheory.Morita.MatrixUnits
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (U : MatrixUnits R N ι)

end GlobalTheory.Morita.MatrixUnits

namespace GlobalTheory.Morita.MatrixUnits
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (U : MatrixUnits R N ι)

section extend

variable {σ : R →+* R}

def extend (a : ι) (F₀ : U.corner a →ₛₗ[σ] U.corner a) : N →ₛₗ[σ] N where
  toFun x := ∑ i, U.E i a (F₀ (U.toPi a x i))
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.smul_sum]

end extend

end GlobalTheory.Morita.MatrixUnits

namespace GlobalTheory.Morita
variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

end GlobalTheory.Morita

namespace GlobalTheory.Morita
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]

end GlobalTheory.Morita

universe w

namespace GlobalTheory.Morita

variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι]


end GlobalTheory.Morita
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanFiniteDimensionalOfBoundedForms
section
open Topology Filter

namespace GlobalTheory

theorem span_finiteDimensional_of_bounded_forms {V : Type} [AddCommGroup V] [Module ℂ V]
    (s : Set V) (hs : ∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C) :
    FiniteDimensional ℂ (Submodule.span ℂ s) := by
  classical
  obtain ⟨t, hts, hspan, hli⟩ := exists_linearIndependent ℂ s
  have ht : t.Finite := by
    by_contra hinf
    have hinf' : t.Infinite := hinf
    let e : ℕ ↪ t := hinf'.natEmbedding
    have hli' : LinearIndepOn ℂ id t := hli
    let b := Module.Basis.extend hli'
    let v : (hli'.extend (Set.subset_univ t)) → ℂ := fun i =>
      if h : ∃ k : ℕ, ((e k : t) : V) = (i : V) then (h.choose : ℂ) else 0
    obtain ⟨C, hC⟩ := hs (b.constr ℂ v)
    have key : ∀ k : ℕ, b.constr ℂ v ((e k : t) : V) = (k : ℂ) := by
      intro k
      have hmem : ((e k : t) : V) ∈ hli'.extend (Set.subset_univ t) :=
        hli'.subset_extend _ (e k).2
      have hb : b ⟨_, hmem⟩ = ((e k : t) : V) := by simp [b, Module.Basis.coe_extend]
      rw [← hb, Module.Basis.constr_basis]
      have h : ∃ j : ℕ, ((e j : t) : V) = ((⟨_, hmem⟩ : hli'.extend (Set.subset_univ t)) : V) :=
        ⟨k, rfl⟩
      simp only [v, dif_pos h]
      have hj : h.choose = k := e.injective (Subtype.ext h.choose_spec)
      rw [hj]
    obtain ⟨k, hk⟩ := exists_nat_gt C
    have hle := hC _ (hts (e k).2)
    rw [key, Complex.norm_natCast] at hle
    linarith
  have hfd : FiniteDimensional ℂ (Submodule.span ℂ t) := FiniteDimensional.span_of_finite ℂ ht
  rw [hspan] at hfd
  exact hfd

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanOneTmulEqTop
section
namespace GlobalTheory.TensorUnitSpanTop

open TensorProduct

theorem span_one_tmul_eq_top {R M : Type} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    {ι : Type} (f : ι → M) (hf : Submodule.span R (Set.range f) = ⊤) :
    Submodule.span (IsLocalRing.ResidueField R)
      (Set.range fun (i : ι) ↦ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] f i) = ⊤ := by
  set N := Submodule.span (IsLocalRing.ResidueField R)
      (Set.range fun (i : ι) ↦ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] f i) with hN
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul a m =>
    have hm : m ∈ Submodule.span R (Set.range f) := hf ▸ Submodule.mem_top
    have h1 : (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] m ∈ N.restrictScalars R := by
      induction hm using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact Submodule.subset_span ⟨i, rfl⟩
      | zero => simp
      | add y z _ _ hy hz => rw [tmul_add]; exact add_mem hy hz
      | smul r y _ hy => rw [tmul_smul]; exact Submodule.smul_mem _ r hy
    have h2 : a ⊗ₜ[R] m = a • ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] m) := by
      rw [smul_tmul', smul_eq_mul, mul_one]
    rw [h2]
    exact N.smul_mem a h1
  | add x y hx hy => exact add_mem hx hy

theorem main : ∀ {R M : Type} [inst : CommRing R] [inst_1 : IsLocalRing R] [inst_2 : AddCommGroup M] [inst_3 : Module R M] {ι : Type} (f : ι → M), Submodule.span R (Set.range f) = ⊤ → Submodule.span (IsLocalRing.ResidueField R) (Set.range fun (i : ι) ↦ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] f i) = ⊤ :=
  fun f hf => span_one_tmul_eq_top f hf

end GlobalTheory.TensorUnitSpanTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRangeEmbeddingEqTop
section
namespace GlobalTheory.EmbeddingRangeSpanTop

open NumberField

theorem span_range_embedding_eq_top (F : Type) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] :
    Submodule.span ℝ (Set.range fun (a : F) (v : NumberField.InfinitePlace F) ↦
      (NumberField.InfinitePlace.embedding v : F → ℂ) a) = ⊤ := by
  classical
  let L : NumberField.mixedEmbedding.mixedSpace F →ₗ[ℝ] (NumberField.InfinitePlace F → ℂ) :=
    { toFun := fun x v => x.2 ⟨v, NumberField.IsTotallyComplex.isComplex v⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hL : Function.Surjective L := fun z => ⟨(0, fun w => z w.1), rfl⟩
  have hcomp : (fun (a : F) (v : NumberField.InfinitePlace F) ↦
      (NumberField.InfinitePlace.embedding v : F → ℂ) a) = L ∘ (NumberField.mixedEmbedding F) := by
    funext a v
    simp [L, NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex]
  have hspan : Submodule.span ℝ (Set.range (NumberField.mixedEmbedding F)) = ⊤ := by
    rw [eq_top_iff, ← (NumberField.mixedEmbedding.latticeBasis F).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨_, (NumberField.mixedEmbedding.latticeBasis_apply F i).symm⟩
  rw [hcomp, Set.range_comp, Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]
  exact hL

end GlobalTheory.EmbeddingRangeSpanTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRangeInfKerEqSpanRationalKer
section
open Module

namespace GlobalTheory

theorem semilinear_pi_eq_sum_single {K : Type} [Field K] (σ : K →+* ℂ) {W : Type} [AddCommGroup W]
    [Module ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (x : Fin n → K) :
    j x = ∑ k, σ (x k) • j (Pi.single k 1) := by
  have hx : x = ∑ k, x k • (Pi.single k 1 : Fin n → K) := by
    ext l
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [LinearMap.map_smulₛₗ]

theorem span_range_inf_ker_eq_span_rational_ker {K : Type} [Field K] (σ : K →+* ℂ) {W E : Type}
    [AddCommGroup W] [Module ℂ W] [AddCommGroup E] [Module ℂ E] {n d : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] W) (j' : (Fin d → K) →ₛₗ[σ] E) (f : W →ₗ[ℂ] E)
    (M : Matrix (Fin d) (Fin n) K)
    (hli : LinearIndependent ℂ (fun l => j' (Pi.single l 1)))
    (hf : ∀ x, f (j x) = j' (M.mulVec x)) :
    Submodule.span ℂ (Set.range j) ⊓ LinearMap.ker f
      = Submodule.span ℂ (j '' {x | M.mulVec x = 0}) := by
  classical
  apply le_antisymm
  · rintro w ⟨hw, hw0⟩
    have hle : Submodule.span ℂ (Set.range j)
        ≤ Submodule.span ℂ (Set.range fun k => j (Pi.single k 1)) := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      rw [semilinear_pi_eq_sum_single σ j x]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hle hw)
    have h0 : f (∑ k, c k • j (Pi.single k 1)) = 0 := hw0
    have h1 : ∑ l, (∑ k, σ (M l k) * c k) • j' (Pi.single l 1) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← h0, map_sum]
      simp only [map_smul, hf, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [semilinear_pi_eq_sum_single σ j' (M.mulVec _), Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_smul, mul_comm]
      simp
    have h2 : ∀ l, ∑ k, σ (M l k) * c k = 0 := Fintype.linearIndependent_iff.1 hli _ h1
    letI : Algebra K ℂ := σ.toAlgebra
    let b := Basis.ofVectorSpace K ℂ
    let s := Finset.univ.biUnion fun k => (b.repr (c k)).support
    have hc : ∀ k, c k = ∑ i ∈ s, σ (b.repr (c k) i) * b i := by
      intro k
      have h3 := b.linearCombination_repr (c k)
      rw [Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ (s := s)
          (Finset.subset_biUnion_of_mem (fun k => (b.repr (c k)).support) (Finset.mem_univ k))
          _ (by simp)] at h3
      exact h3.symm
    have hw' : ∑ k, c k • j (Pi.single k 1) = ∑ i ∈ s, b i • j (fun k => b.repr (c k) i) := by
      have h5 : ∀ i, b i • j (fun k => b.repr (c k) i)
          = ∑ k, b i • σ (b.repr (c k) i) • j (Pi.single k 1) := fun i => by
        rw [semilinear_pi_eq_sum_single σ j (fun k => b.repr (c k) i), Finset.smul_sum]
      rw [Finset.sum_congr rfl fun i _ => h5 i, Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      conv_lhs => rw [hc k, Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, mul_comm]
    rw [hw']
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
    ext l
    have h4 : b.repr (∑ k, M l k • c k) i = 0 := by
      have : ∑ k, M l k • c k = 0 := h2 l
      rw [this]; simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finsupp.finsetSum_apply] at h4
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h4
    exact h4
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨Submodule.subset_span ⟨x, rfl⟩, ?_⟩
    have hx' : M.mulVec x = 0 := hx
    change f (j x) = 0
    rw [hf, hx', map_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecLocalHomFactorsAffineOpen
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem spec_local_hom_factors_affineOpen : ∀ (X : Scheme.{0}) (V : X.Opens) (hV : IsAffineOpen V)
    (A : Type) [CommRing A] [IsLocalRing A]
    (f : Spec (CommRingCat.of A) ⟶ X), f (IsLocalRing.closedPoint A) ∈ V →
    ∃ g : Γ(X, V) →+* A, f = Spec.map (CommRingCat.ofHom g) ≫ hV.fromSpec := by
  intro X V hV A _ _ f hf
  have H : Set.range f ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    have hs : x ⤳ IsLocalRing.closedPoint A := IsLocalRing.specializes_closedPoint x
    exact (hs.map f.continuous).mem_open V.isOpen hf
  refine ⟨(Spec.preimage (IsOpenImmersion.lift hV.fromSpec f H)).hom, ?_⟩
  simp [IsOpenImmersion.lift_fac]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecWidePushoutIsoWidePullbackYoneda
section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.SpecWidePullback

noncomputable def specHomEquiv (X : Scheme.{0}) (R : CommRingCat.{0}) :
    (R ⟶ Γ(X, ⊤)) ≃ (X ⟶ Spec R) where
  toFun φ := ΓSpec.adjunction.homEquiv X (op R) (show Scheme.Γ.rightOp.obj X ⟶ op R from φ.op)
  invFun y := ((ΓSpec.adjunction.homEquiv X (op R)).symm y).unop
  left_inv φ := congrArg Quiver.Hom.unop (Equiv.symm_apply_apply (ΓSpec.adjunction.homEquiv X (op R))
    (show Scheme.Γ.rightOp.obj X ⟶ op R from φ.op))
  right_inv y := Equiv.apply_symm_apply (ΓSpec.adjunction.homEquiv X (op R)) y

theorem specHomEquiv_comp (X : Scheme.{0}) {R R' : CommRingCat.{0}} (ψ : R' ⟶ R) (φ : R ⟶ Γ(X, ⊤)) :
    specHomEquiv X R' (ψ ≫ φ) = specHomEquiv X R φ ≫ Spec.map ψ := by
  exact ΓSpec.adjunction.homEquiv_naturality_right (show Scheme.Γ.rightOp.obj X ⟶ op R from φ.op) ψ.op

theorem specHomEquiv_symm_comp (X : Scheme.{0}) {R R' : CommRingCat.{0}} (y : X ⟶ Spec R) (ψ : R' ⟶ R) :
    (specHomEquiv X R').symm (y ≫ Spec.map ψ) = ψ ≫ (specHomEquiv X R).symm y := by
  rw [Equiv.symm_apply_eq, specHomEquiv_comp, Equiv.apply_symm_apply]

theorem existsUnique_lift {A B T : Type} [CommRing A] [CommRing B] [CommRing T] (a : A →+* B) {k : ℕ}
    (ι : Fin (k + 1) → (B →+* T))
    (hu : ∀ (R : Type) [CommRing R] (g : Fin (k + 1) → (B →+* R)),
      (∀ j, (g j).comp a = (g 0).comp a) → ∃! φ : T →+* R, ∀ j, φ.comp (ι j) = g j)
    (X : Scheme.{0}) (y : Fin (k + 1) → (X ⟶ Spec (CommRingCat.of B)))
    (hy : ∀ j, y j ≫ Spec.map (CommRingCat.ofHom a) = y 0 ≫ Spec.map (CommRingCat.ofHom a)) :
    ∃! m : X ⟶ Spec (CommRingCat.of T), ∀ j, m ≫ Spec.map (CommRingCat.ofHom (ι j)) = y j := by
  let g : Fin (k + 1) → (B →+* Γ(X, ⊤)) := fun j => ((specHomEquiv X _).symm (y j)).hom
  have hg : ∀ j, (g j).comp a = (g 0).comp a := fun j => by
    have := congrArg (fun z => ((specHomEquiv X (CommRingCat.of A)).symm z).hom) (hy j)
    simpa [g, specHomEquiv_symm_comp] using this
  obtain ⟨φ, hφ, huniq⟩ := hu Γ(X, ⊤) g hg
  refine ⟨specHomEquiv X _ (CommRingCat.ofHom φ), fun j => ?_, fun m hm => ?_⟩
  · rw [← specHomEquiv_comp, Equiv.apply_eq_iff_eq_symm_apply]
    exact CommRingCat.hom_ext (hφ j)
  · have h1 : ((specHomEquiv X _).symm m).hom = φ := huniq _ fun j => by
      have := congrArg (fun z => ((specHomEquiv X (CommRingCat.of B)).symm z).hom) (hm j)
      simpa [g, specHomEquiv_symm_comp] using this
    rw [← h1]
    simp

end GlobalTheory.SpecWidePullback

namespace GlobalTheory.SpecWidePullback

theorem yoneda_spec_isoWidePullback (A B T : Type) [CommRing A] [CommRing B] [CommRing T] (a : A →+* B)
    (k : ℕ) (ι : Fin (k + 1) → (B →+* T)) (hι : ∀ j, (ι j).comp a = (ι 0).comp a)
    (hu : ∀ (R : Type) [CommRing R] (g : Fin (k + 1) → (B →+* R)),
      (∀ j, (g j).comp a = (g 0).comp a) → ∃! φ : T →+* R, ∀ j, φ.comp (ι j) = g j) :
    ∃ e : yoneda.obj (Spec (CommRingCat.of T)) ≅ widePullback (yoneda.obj (Spec (CommRingCat.of A)))
        (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B)))
        (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom a))),
      ∀ j, e.hom ≫ WidePullback.π _ j = yoneda.map (Spec.map (CommRingCat.ofHom (ι j))) := by
  have hleg : ∀ j, Spec.map (CommRingCat.ofHom (ι j)) ≫ Spec.map (CommRingCat.ofHom a) =
      Spec.map (CommRingCat.ofHom ((ι 0).comp a)) := fun j => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hι j]
  let c : Cone (WidePullbackShape.wideCospan (yoneda.obj (Spec (CommRingCat.of A)))
      (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B)))
      (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom a)))) :=
    WidePullbackShape.mkCone (yoneda.map (Spec.map (CommRingCat.ofHom ((ι 0).comp a))))
      (fun j => yoneda.map (Spec.map (CommRingCat.ofHom (ι j))))
      (fun j => by
        change yoneda.map (Spec.map (CommRingCat.ofHom (ι j))) ≫ yoneda.map (Spec.map (CommRingCat.ofHom a)) = _
        rw [← yoneda.map_comp, hleg j])
  have hc : IsLimit c := by
    apply evaluationJointlyReflectsLimits
    intro U
    have hw : ∀ (s : Cone (WidePullbackShape.wideCospan (yoneda.obj (Spec (CommRingCat.of A)))
        (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B)))
        (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom a))) ⋙ (evaluation _ _).obj U)) (x : s.pt) j,
        s.π.app (some j) x ≫ Spec.map (CommRingCat.ofHom a) = s.π.app none x := fun s x j =>
      ConcreteCategory.congr_hom (s.w (WidePullbackShape.Hom.term j)) x
    have H := fun (s : Cone (WidePullbackShape.wideCospan (yoneda.obj (Spec (CommRingCat.of A)))
        (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B)))
        (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom a))) ⋙ (evaluation _ _).obj U)) (x : s.pt) =>
      existsUnique_lift a ι hu (unop U) (fun j => s.π.app (some j) x)
        (fun j => (hw s x j).trans (hw s x 0).symm)
    refine IsLimit.mk (fun s => TypeCat.ofHom (fun x => (H s x).exists.choose)) (fun s j => ?_) (fun s m hm => ?_)
    · ext x
      rcases j with _ | j
      · change (H s x).exists.choose ≫ Spec.map (CommRingCat.ofHom ((ι 0).comp a)) = s.π.app none x
        rw [← hleg 0, ← Category.assoc, (H s x).exists.choose_spec 0, hw]
      · exact (H s x).exists.choose_spec j
    · ext x
      refine (H s x).unique (fun j => ?_) (H s x).exists.choose_spec
      have h := ConcreteCategory.congr_hom (hm (some j)) x
      rw [ConcreteCategory.comp_apply] at h
      exact h
  exact ⟨hc.conePointUniqueUpToIso (limit.isLimit _), fun j =>
    hc.conePointUniqueUpToIso_hom_comp (limit.isLimit _) (some j)⟩

end GlobalTheory.SpecWidePullback
end

