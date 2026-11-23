module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BlockGLSupportedMemMirabolicSupported
section
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

private theorem eq_of_forall_trace_mul_eq_trace_mul {E : Type} [Field E] [NumberField E] {b c : E}
    (h : ∀ a : E, Algebra.trace ℚ E (a * b) = Algebra.trace ℚ E (a * c)) : b = c := by
  apply ((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).injective
  ext a
  rw [LinearMap.BilinForm.toDual_def, LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply,
    Algebra.traceForm_apply, mul_comm b, mul_comm c]
  exact h a

theorem existsUnique_sesq_of_trace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (V : Type) [AddCommGroup V] [Module E V] [Module ℚ V] [IsScalarTower ℚ E V] (B : LinearMap.BilinForm ℚ V), (∀ (a : E) x y, B (a • x) y = B x (IsCMField.complexConj E a • y)) → ∃! h : V → V → E, (∀ x y (a : E), Algebra.trace ℚ E (a * h x y) = B (a • x) y) ∧ (∀ x x' y, h (x + x') y = h x y + h x' y) ∧ (∀ x y y', h x (y + y') = h x y + h x y') ∧ (∀ (a : E) x y, h (a • x) y = a * h x y) ∧ (∀ (a : E) x y, h x (a • y) = IsCMField.complexConj E a * h x y) := by
  intro E _ _ _ V _ _ _ _ B hB
  obtain ⟨h, htr⟩ : ∃ h : V → V → E,
      ∀ x y (a : E), Algebra.trace ℚ E (a * h x y) = B (a • x) y := by
    refine ⟨fun x y => ((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).symm
      { toFun := fun a => B (a • x) y
        map_add' := fun a b => by simp only [add_smul, map_add (f := _), LinearMap.add_apply]
        map_smul' := fun q a => by
          simp only [smul_assoc, map_smul, LinearMap.smul_apply, RingHom.id_apply] }, ?_⟩
    intro x y a
    dsimp only
    rw [mul_comm, ← Algebra.traceForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]
    rfl
  refine ⟨h, ⟨htr, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x x' y
    apply eq_of_forall_trace_mul_eq_trace_mul
    intro a
    rw [mul_add, map_add (f := _), htr, htr, htr, smul_add, map_add (f := _), LinearMap.add_apply]
  · intro x y y'
    apply eq_of_forall_trace_mul_eq_trace_mul
    intro a
    rw [mul_add, map_add (f := _), htr, htr, htr, map_add (f := _)]
  · intro b x y
    apply eq_of_forall_trace_mul_eq_trace_mul
    intro a
    rw [htr, ← mul_assoc, htr, mul_smul]
  · intro b x y
    apply eq_of_forall_trace_mul_eq_trace_mul
    intro a
    rw [htr, ← mul_assoc, htr, mul_comm a, mul_smul, hB (IsCMField.complexConj E b) (a • x) y,
      IsCMField.complexConj_apply_apply]
  · rintro h' ⟨htr', -⟩
    funext x y
    apply eq_of_forall_trace_mul_eq_trace_mul
    intro a
    rw [htr', htr]

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CentralizerCmFieldInvolution
section
open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.DualFlag

theorem abel_sum_rev : ∀ (n : ℕ) (b : Fin (n + 1) → ℝ) (e : Fin (n + 2) → ℝ), e 0 = 0 →
    (∑ i : Fin (n + 1), b i * (e i.rev.succ - e i.rev.castSucc)) =
      (∑ i : Fin n, (b i.castSucc - b i.succ) * (-e i.rev.succ.castSucc)) +
        b 0 * e (Fin.last (n + 1)) := by
  intro n
  induction n with
  | zero =>
    intro b e h0
    simp [h0]
  | succ n ih =>
    intro b e h0
    have h := ih (fun i => b i.succ) (fun i => e i.castSucc) (by simpa using h0)
    have hL := Fin.sum_univ_succ (fun i : Fin (n + 2) => b i * (e i.rev.succ - e i.rev.castSucc))
    have hR := Fin.sum_univ_succ
      (fun i : Fin (n + 1) => (b i.castSucc - b i.succ) * (-e i.rev.succ.castSucc))
    simp only [Fin.rev_succ, Fin.rev_zero, Fin.succ_last, Fin.castSucc_zero,
      Fin.succ_zero_eq_one, Fin.succ_castSucc] at h hL hR
    rw [hL, hR]
    linear_combination h

end GlobalTheory.CompanionTheory.DualFlag
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ComapFgOfValuationRing
section
open scoped Matrix TensorProduct
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem comap_fg_of_valuationRing (R : Type) [CommRing R] [IsDomain R] [ValuationRing R]
    (ι κ : Type) [Fintype ι] [Fintype κ] (φ : (ι → R) →ₗ[R] (κ → R)) (W : Submodule R (κ → R))
    (hW : W.FG) : (W.comap φ).FG := by
  obtain ⟨c, w, hw⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hW
  let ψ : ((ι → R) × (Fin c → R)) →ₗ[R] (κ → R) := φ.coprod (Fintype.linearCombination R w)
  have hflat : Module.Flat R (LinearMap.range ψ) := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
    exact Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance
  have hfree : Module.Free R (LinearMap.range ψ) := Module.free_of_flat_of_isLocalRing
  have hfp : Module.FinitePresentation R (LinearMap.range ψ) :=
    Module.finitePresentation_of_projective _ _
  have hsurj : Function.Surjective ψ.rangeRestrict := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  have hker : (LinearMap.ker ψ.rangeRestrict).FG :=
    Module.FinitePresentation.fg_ker _ hsurj
  have heq : W.comap φ = (LinearMap.ker ψ.rangeRestrict).map (LinearMap.fst R (ι → R) (Fin c → R)) := by
    ext l
    simp only [Submodule.mem_comap, Submodule.mem_map, LinearMap.mem_ker, LinearMap.fst_apply]
    constructor
    · intro hl
      rw [← hw, ← Fintype.range_linearCombination] at hl
      obtain ⟨a, ha⟩ := hl
      refine ⟨(l, -a), ?_, rfl⟩
      apply Subtype.ext
      simp [ψ, ha]
    · rintro ⟨⟨l', a⟩, h, rfl⟩
      have h' : φ l' + Fintype.linearCombination R w a = 0 := by
        simpa [ψ] using congrArg Subtype.val h
      have hm : Fintype.linearCombination R w a ∈ W := by
        rw [← hw, ← Fintype.range_linearCombination]
        exact ⟨a, rfl⟩
      rw [eq_neg_of_add_eq_zero_left h']
      exact W.neg_mem hm
  rw [heq]
  exact hker.map _

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CompactCentralizerTranslate
section
open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.CommAlg


open AddMonoidAlgebra in
theorem ker_eq_span_single_sub_one :
    ∀ (k X A : Type) [Field k] [AddCommGroup X] [CommRing A] [Nontrivial A] [Bialgebra k A]
      (φ : AddMonoidAlgebra k X →ₐc[k] A), Function.Surjective φ →
      ∃ Y : AddSubgroup X, RingHom.ker (φ : AddMonoidAlgebra k X →+* A) =
        Ideal.span {f | ∃ y ∈ Y, f = AddMonoidAlgebra.single y (1 : k) - 1} := by
  intro k X A _ _ _ _ _ φ _
  classical
  obtain ⟨u, hu⟩ : ∃ u : X → A, ∀ x, u x = φ (AddMonoidAlgebra.single x 1) := ⟨_, fun _ => rfl⟩
  have hmul : ∀ x y, u (x + y) = u x * u y := by
    intro x y
    rw [hu, hu, hu, ← map_mul, AddMonoidAlgebra.single_mul_single, one_mul]
  have hzero : u 0 = 1 := by
    rw [hu, ← AddMonoidAlgebra.one_def, map_one]
  have hinv : ∀ x, u x * u (-x) = 1 := by
    intro x
    rw [← hmul, add_neg_cancel, hzero]
  have hgl : ∀ x, IsGroupLikeElem k (u x) := fun x => by
    rw [hu]
    exact (AddMonoidAlgebra.isGroupLikeElem_single_one (R := k) (A := k) x).map φ
  let Y : AddSubgroup X :=
    { carrier := {x | u x = 1}
      zero_mem' := hzero
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [hmul, ha, hb, one_mul]
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        simpa [ha] using hinv a }
  have hY : ∀ x, x ∈ Y ↔ u x = 1 := fun _ => Iff.rfl
  refine ⟨Y, ?_⟩
  have hker : ∀ f, f ∈ RingHom.ker (φ : AddMonoidAlgebra k X →+* A) ↔ φ f = 0 :=
    fun f => RingHom.mem_ker
  have hle : Ideal.span {f | ∃ y ∈ Y, f = AddMonoidAlgebra.single y (1 : k) - 1} ≤
      RingHom.ker (φ : AddMonoidAlgebra k X →+* A) := by
    rw [Ideal.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, hker, map_sub, map_one, ← hu, (hY y).mp hy, sub_self]
  refine le_antisymm ?_ hle
  intro f hf
  rw [hker] at hf
  let r : X → X := fun x => (QuotientAddGroup.mk x : X ⧸ Y).out
  have hr : ∀ x, (QuotientAddGroup.mk (r x) : X ⧸ Y) = QuotientAddGroup.mk x :=
    fun x => Quotient.out_eq _
  have hcoset : ∀ x (c : k), AddMonoidAlgebra.single x c - AddMonoidAlgebra.single (r x) c ∈
      Ideal.span {f | ∃ y ∈ Y, f = AddMonoidAlgebra.single y (1 : k) - 1} := by
    intro x c
    have e : AddMonoidAlgebra.single x c - AddMonoidAlgebra.single (r x) c =
        AddMonoidAlgebra.single (r x) c * (AddMonoidAlgebra.single (-(r x) + x) 1 - 1) := by
      rw [mul_sub, mul_one, AddMonoidAlgebra.single_mul_single, mul_one, add_neg_cancel_left]
    rw [e]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, QuotientAddGroup.eq.mp (hr x), rfl⟩)
  obtain ⟨G, hG⟩ : ∃ G : AddMonoidAlgebra k X,
      G = f.coeff.sum (fun x c => AddMonoidAlgebra.single (r x) c) := ⟨_, rfl⟩
  have hfG : f - G ∈ Ideal.span {f | ∃ y ∈ Y, f = AddMonoidAlgebra.single y (1 : k) - 1} := by
    have e : f - G = f.coeff.sum
        (fun x c => AddMonoidAlgebra.single x c - AddMonoidAlgebra.single (r x) c) := by
      rw [Finsupp.sum_sub, AddMonoidAlgebra.sum_coeff_single, hG]
    rw [e]
    unfold Finsupp.sum
    exact Ideal.sum_mem _ (fun x _ => hcoset x _)
  have hφ : ∀ g : AddMonoidAlgebra k X, φ g = Finsupp.linearCombination k u g.coeff := by
    intro g
    conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single g]
    rw [map_finsuppSum, Finsupp.linearCombination_apply]
    refine Finsupp.sum_congr (fun x _ => ?_)
    rw [hu, show AddMonoidAlgebra.single x (g.coeff x) =
      g.coeff x • AddMonoidAlgebra.single x (1 : k) by rw [AddMonoidAlgebra.smul_single', mul_one],
      map_smul]
  have hG0 : φ G = 0 := by
    have h1 : φ (f - G) = 0 := (hker _).mp (hle hfG)
    rw [map_sub, hf, zero_sub, neg_eq_zero] at h1
    exact h1
  have hinj : Set.InjOn u (Set.range r) := by
    rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩ h
    have hm : -(r x) + r x' ∈ Y := by
      rw [hY, hmul]
      have h2 : u (-(r x)) * u (r x) = 1 := by
        rw [mul_comm]
        exact hinv _
      rw [← h]
      exact h2
    have e1 : (QuotientAddGroup.mk (r x) : X ⧸ Y) = QuotientAddGroup.mk (r x') :=
      QuotientAddGroup.eq.mpr hm
    have e2 : (QuotientAddGroup.mk x : X ⧸ Y) = QuotientAddGroup.mk x' :=
      (hr x).symm.trans (e1.trans (hr x'))
    show (QuotientAddGroup.mk x : X ⧸ Y).out = (QuotientAddGroup.mk x' : X ⧸ Y).out
    rw [e2]
  have hli : LinearIndepOn k u (Set.range r) := by
    rw [linearIndepOn_iff_image hinj]
    refine (linearIndepOn_isGroupLikeElem (R := k) (A := A)).mono ?_
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact hgl (r x)
  have hsupp : G.coeff ∈ Finsupp.supported k k (Set.range r) := by
    rw [hG, AddMonoidAlgebra.coeff_finsuppSum]
    unfold Finsupp.sum
    exact Submodule.sum_mem _ (fun x _ => Finsupp.single_mem_supported k _ (Set.mem_range_self x))
  have hGc : G.coeff = 0 := by
    rw [linearIndepOn_iff] at hli
    exact hli _ hsupp (by rw [← hφ]; exact hG0)
  have hGz : G = 0 := AddMonoidAlgebra.coeff_injective hGc
  simpa [hGz] using hfG

end GlobalTheory.CompanionTheory.CommAlg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DetFromColsFrameChange
section
namespace GlobalTheory.CompanionTheory.Ar.Flat

open Matrix

theorem det_fromCols_frame_change : ∀ (R : Type) [CommRing R] (p q : ℕ) (J J₂ : Matrix (Fin p ⊕ Fin q) (Fin p) R) (S S₂ : Matrix (Fin q) (Fin p ⊕ Fin q) R) (T T₂ : Matrix (Fin p ⊕ Fin q) (Fin q) R) (A : Matrix (Fin p) (Fin p) R) (B : Matrix (Fin q) (Fin q) R), S * J = 0 → S * T = 1 → IsUnit (Matrix.fromCols J T).det → S₂ * T₂ = 1 → J₂ = J * A → S = B * S₂ → (Matrix.fromCols J₂ T₂).det = (Matrix.fromCols J T).det * A.det * B.det := by
  intro R _ p q J J₂ S S₂ T T₂ A B hSJ hST hU hST₂ hJ hS
  set W : Matrix (Fin p ⊕ Fin q) (Fin q) R := (Matrix.fromCols J T)⁻¹ * T₂ with hW
  have h1 : Matrix.fromCols J T * W = T₂ := by
    rw [hW, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU, Matrix.one_mul]
  have h2 : J * W.toRows₁ + T * W.toRows₂ = T₂ := by
    rw [← Matrix.fromCols_mul_fromRows, Matrix.fromRows_toRows, h1]
  have h3 : W.toRows₂ = B := by
    have h := congrArg (fun X => S * X) h2
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, hSJ, hST, Matrix.zero_mul, Matrix.one_mul,
      zero_add] at h
    rw [h, hS, Matrix.mul_assoc, hST₂, Matrix.mul_one]
  have h4 : Matrix.fromCols J₂ T₂ =
      Matrix.fromCols J T * Matrix.fromBlocks A W.toRows₁ 0 B := by
    rw [Matrix.fromCols_mul_fromBlocks, Matrix.mul_zero, add_zero, ← hJ, ← h3, h2]
  rw [h4, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, mul_assoc]

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DetMulMapDetEqOneOfSesq
section
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem det_mul_map_det_eq_one_of_sesq {E : Type*} [Field E] {V : Type*} [AddCommGroup V]
    [Module E V] [FiniteDimensional E V] (σ : E →+* E) (H : V →ₗ[E] V →ₛₗ[σ] E)
    (hH : ∀ x, (∀ y, H x y = 0) → x = 0) (g : V →ₗ[E] V)
    (hg : ∀ x y, H (g x) (g y) = H x y) :
    LinearMap.det g * σ (LinearMap.det g) = 1 := by
  classical
  let b := Module.finBasis E V
  let S : Matrix _ _ E := Matrix.of fun i j => H (b i) (b j)
  let G := LinearMap.toMatrix b b g
  have hgb : ∀ j, g (b j) = ∑ i, G i j • b i := by
    intro j
    simp only [G, LinearMap.toMatrix_apply]
    exact (b.sum_repr (g (b j))).symm
  have hS : G.transpose * S * σ.mapMatrix G = S := by
    ext i j
    have h1 : S i j = H (g (b i)) (g (b j)) := (hg _ _).symm
    rw [h1, hgb, hgb]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      LinearMap.map_smulₛₗ, smul_eq_mul, S, Matrix.of_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
  have hdet : S.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hvS⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    apply hv
    have hx : ∑ i, v i • b i = 0 := by
      apply hH
      have : H (∑ i, v i • b i) = 0 := by
        apply b.ext
        intro j
        have := congrFun hvS j
        set_option synthInstance.maxHeartbeats 100000 in
          simpa [Matrix.vecMul, dotProduct, S, map_sum, LinearMap.sum_apply] using this
      intro y
      rw [this]; rfl
    funext i
    exact Fintype.linearIndependent_iff.mp b.linearIndependent v hx i
  have hd := congrArg Matrix.det hS
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det] at hd
  have hG : G.det = LinearMap.det g := LinearMap.det_toMatrix b g
  rw [hG] at hd
  apply mul_left_cancel₀ hdet
  linear_combination hd

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DetOneAddCompCommField
section
open NumberField TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem det_one_add_comp_comm_field {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Module.Finite K V] [Module.Finite K W]
    (A : V →ₗ[K] W) (B : W →ₗ[K] V) :
    LinearMap.det (1 + A ∘ₗ B) = LinearMap.det (1 + B ∘ₗ A) := by
  classical
  let bV := Module.finBasis K V
  let bW := Module.finBasis K W
  rw [← LinearMap.det_toMatrix bW, ← LinearMap.det_toMatrix bV, map_add (f := _), map_add (f := _),
    LinearMap.toMatrix_comp bW bV bW, LinearMap.toMatrix_comp bV bW bV,
    LinearMap.toMatrix_one, LinearMap.toMatrix_one, Matrix.det_one_add_mul_comm]

theorem exists_det_congr_one : ∀ (E : Type) [Field E] [NumberField E] (La : Type) [AddCommGroup La] [Module (𝓞 E) La] [Module.Finite (𝓞 E) La] [Module.Projective (𝓞 E) La] (I : Ideal (𝓞 E)) (g : La →ₗ[𝓞 E] La), (∀ a, g a - a ∈ I • (⊤ : Submodule (𝓞 E) La)) → ∃ u : 𝓞 E, u - 1 ∈ I ∧ (u : E) = LinearMap.det (g.baseChange E) := by
  intro E _ _ La _ _ _ _ I g hg
  classical
  obtain ⟨n, p, i, -, -, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 E) La
  set N : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin n → 𝓞 E) := i ∘ₗ ((g - 1) ∘ₗ p) with hN
  have key : ∀ (x : La), x ∈ I • (⊤ : Submodule (𝓞 E) La) → ∀ k, i x k ∈ I := by
    intro x hx k
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y _
      rw [map_smul, Pi.smul_apply, smul_eq_mul]
      exact I.mul_mem_right _ hr
    · intro x y hx hy
      rw [map_add (f := _), Pi.add_apply]
      exact I.add_mem hx hy
  refine ⟨LinearMap.det (1 + N), ?_, ?_⟩
  · rw [← Ideal.Quotient.eq, ← LinearMap.det_toMatrix', RingHom.map_det, map_one]
    have : (Ideal.Quotient.mk I).mapMatrix (LinearMap.toMatrix' (1 + N)) = 1 := by
      rw [map_add (f := _), map_add (f := _), LinearMap.toMatrix'_one, map_one, add_eq_left]
      ext a b
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
        LinearMap.toMatrix'_apply]
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact key _ (hg _) _
    rw [this, Matrix.det_one]
  · have h1 : ((LinearMap.det (1 + N) : 𝓞 E) : E) = LinearMap.det ((1 + N).baseChange E) :=
      (LinearMap.det_baseChange (A := E) (1 + N)).symm
    rw [h1, LinearMap.baseChange_add, LinearMap.baseChange_one, hN, LinearMap.baseChange_comp,
      det_one_add_comp_comm_field, ← LinearMap.baseChange_comp, LinearMap.comp_assoc, hpi,
      LinearMap.comp_id, LinearMap.baseChange_sub, LinearMap.baseChange_one, add_sub_cancel]

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EqZeroOfMemMapPow
section
open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.KrullGroupAlg

theorem coeff_mem_of_mem_map {R M : Type} [CommRing R] [AddCommGroup M] (I : Ideal R)
    (x : AddMonoidAlgebra R M) (hx : x ∈ Ideal.map (algebraMap R (AddMonoidAlgebra R M)) I)
    (φ : AddMonoidAlgebra R M →ₗ[R] R) : φ x ∈ I := by
  have hx' : x ∈ Submodule.span (AddMonoidAlgebra R M) (algebraMap R (AddMonoidAlgebra R M) '' I) := hx
  clear hx
  revert φ
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    intro φ
    rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
    exact I.mul_mem_right _ ha
  | zero =>
    intro φ
    rw [map_zero]
    exact I.zero_mem
  | add y z _ _ hy hz =>
    intro φ
    rw [map_add (f := _)]
    exact I.add_mem (hy φ) (hz φ)
  | smul r y _ hy =>
    intro φ
    have := hy (φ ∘ₗ LinearMap.mulLeft R r)
    simpa [smul_eq_mul] using this

theorem eq_zero_of_mem_map_pow : ∀ (R M : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup M] (x : AddMonoidAlgebra R M), (∀ n : ℕ, x ∈ Ideal.map (algebraMap R (AddMonoidAlgebra R M)) (IsLocalRing.maximalIdeal R ^ n)) → x = 0 := by
  intro R M _ _ _ _ x hx
  ext m
  have hm : (Finsupp.lapply m ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap) x ∈ ⨅ n : ℕ, IsLocalRing.maximalIdeal R ^ n :=
    Ideal.mem_iInf.2 fun n =>
      coeff_mem_of_mem_map _ x (hx n) (Finsupp.lapply m ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap)
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal R).ne_top,
    Ideal.mem_bot] at hm
  simpa using hm

end GlobalTheory.CompanionTheory.KrullGroupAlg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsMaxRatioCleared
section
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_max_ratio_cleared :
    ∀ (ι : Type) [Fintype ι] [Nonempty ι] (n : ι → ℤ) (m : ι → ℕ), (∀ i, 0 < m i) →
      ∃ (M : ℕ) (a : ℤ) (i₀ : ι), 0 < M ∧ (∀ i, (M : ℤ) * n i ≤ a * m i) ∧
        (M : ℤ) * n i₀ = a * m i₀ := by
  intro ι _ _ n m hm
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => (n i : ℚ) / m i) Finset.univ_nonempty
  refine ⟨m i₀, n i₀, i₀, hm i₀, fun i => ?_, mul_comm _ _⟩
  have h := hi₀ i (Finset.mem_univ i)
  have hmi : (0 : ℚ) < m i := by exact_mod_cast hm i
  have hm0 : (0 : ℚ) < m i₀ := by exact_mod_cast hm i₀
  rw [div_le_div_iff₀ hmi hm0] at h
  have hq : (m i₀ : ℚ) * n i ≤ n i₀ * (m i : ℚ) := by linarith
  exact_mod_cast hq

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FibrePowerMapOfTotalSpacesIsPullback
section
open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.AbelFlag

theorem abel_summation_flag : ∀ (n : ℕ) (a : Fin (n + 1) → ℝ) (d : Fin (n + 2) → ℝ), d 0 = 0 →
    -(∑ i : Fin (n + 1), a i * (d i.succ - d i.castSucc)) =
      (∑ i : Fin n, (a i.castSucc - a i.succ) * (-d i.succ.castSucc))
        + a (Fin.last n) * (-d (Fin.last (n + 1))) := by
  intro n
  induction n with
  | zero =>
    intro a d h
    simp [h]
  | succ n ih =>
    intro a d h
    have key := ih (fun i => a i.castSucc) (fun i => d i.castSucc) (by simpa using h)
    rw [Fin.sum_univ_castSucc (n := n + 1), Fin.sum_univ_castSucc (n := n)
      (f := fun i : Fin (n + 1) => (a i.castSucc - a i.succ) * (-d i.succ.castSucc))]
    simp only [Fin.succ_castSucc, Fin.succ_last] at key ⊢
    linear_combination key

end GlobalTheory.CompanionTheory.AbelFlag
end

