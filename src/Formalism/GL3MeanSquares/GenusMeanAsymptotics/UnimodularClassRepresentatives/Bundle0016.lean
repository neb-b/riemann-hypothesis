module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0015
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0009
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0007
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0013
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0014

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormEqProdOfMem
section
open NumberField Module Filter Topology
open scoped Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BoxSum

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

def rEmb (w : {w : InfinitePlace F // w.IsReal}) : 𝓞 F →+* ℝ :=
  (InfinitePlace.embedding_of_isReal w.2).comp (algebraMap (𝓞 F) F)

theorem rEmb_apply (w : {w : InfinitePlace F // w.IsReal}) (n : 𝓞 F) :
    rEmb w n = InfinitePlace.embedding_of_isReal w.2 (n : F) := rfl

theorem mem_boxSet_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {T : ℝ} {n : 𝓞 F} :
    n ∈ boxSet K F T ↔ ∀ w : {w : InfinitePlace F // w.IsReal}, 0 < rEmb w n ∧ rEmb w n ≤ T := by
  have hR : IsTotallyReal F := QuadraticExtensionConjugation.isTotallyReal hK hF
  constructor
  · intro h w
    let _ : Algebra F ℂ := w.1.embedding.toAlgebra
    let φ : K →ₐ[F] ℂ := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    have h1 : φ (algebraMap F K (n : F)) = w.1.embedding (n : F) := φ.commutes _
    have h2 := h φ.toRingHom
    have h3 : (φ.toRingHom (algebraMap F K (n : F))).re = rEmb w n := by
      show (φ (algebraMap F K (n : F))).re = _
      rw [h1, rEmb_apply, ← InfinitePlace.embedding_of_isReal_apply w.2, Complex.ofReal_re]
    rwa [h3] at h2
  · intro h φ
    have hw : (InfinitePlace.mk (φ.comp (algebraMap F K))).IsReal := IsTotallyReal.isReal _
    have h1 := InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hw)
    have h3 : (φ (algebraMap F K (n : F))).re = rEmb ⟨_, hw⟩ n := by
      rw [rEmb_apply, ← Complex.ofReal_re (InfinitePlace.embedding_of_isReal _ _),
        InfinitePlace.embedding_of_isReal_apply hw, h1]
      rfl
    rw [h3]
    exact h _

theorem absNorm_eq_prod [IsTotallyReal F] (n : 𝓞 F) :
    (Ideal.absNorm (Ideal.span {n}) : ℝ) = ∏ w : {w : InfinitePlace F // w.IsReal}, |rEmb w n| := by
  have h1 : (Ideal.absNorm (Ideal.span {n}) : ℝ) = |((Algebra.norm ℚ (n : F) : ℚ) : ℝ)| := by
    rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, ← Algebra.coe_norm_int]
    push_cast
    rfl
  rw [h1, ← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm]
  have h2 : ∀ w : InfinitePlace F, w.IsReal := fun w => IsTotallyReal.isReal w
  rw [Finset.prod_subtype (p := fun w : InfinitePlace F => w.IsReal) Finset.univ (by simp [h2])
    (fun w => w (n : F) ^ w.mult)]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [w.2.mult_eq_one, pow_one, rEmb_apply, ← Real.norm_eq_abs,
    InfinitePlace.norm_embedding_of_isReal]

theorem absNorm_eq_prod_of_mem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {T : ℝ} {n : 𝓞 F}
    (hn : n ∈ boxSet K F T) :
    (Ideal.absNorm (Ideal.span {n}) : ℝ) = ∏ w : {w : InfinitePlace F // w.IsReal}, rEmb w n := by
  have hR : IsTotallyReal F := QuadraticExtensionConjugation.isTotallyReal hK hF
  rw [absNorm_eq_prod]
  exact Finset.prod_congr rfl fun w _ => abs_of_pos (((mem_boxSet_iff hK hF).1 hn) w).1

theorem card_real (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) :
    Fintype.card {w : InfinitePlace F // w.IsReal} = Formalism.HermitianLatticesTheory.fDeg K := by
  have hR : IsTotallyReal F := QuadraticExtensionConjugation.isTotallyReal hK hF
  have h1 := (discrTower K F hK hF).2.1
  rw [← h1, IsTotallyReal.finrank]

theorem finite_boxSet (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ) :
    (boxSet K F T).Finite := by
  have hR : IsTotallyReal F := QuadraticExtensionConjugation.isTotallyReal hK hF
  have h0 := Embeddings.finite_of_norm_le F ℂ T
  refine Set.Finite.of_finite_image (f := fun n : 𝓞 F => (n : F)) (h0.subset ?_)
    (RingOfIntegers.coe_injective.injOn)
  rintro _ ⟨n, hn, rfl⟩
  refine ⟨n.2, fun ψ => ?_⟩
  have hw : (InfinitePlace.mk ψ).IsReal := IsTotallyReal.isReal _
  have h1 := ((mem_boxSet_iff hK hF).1 hn) ⟨_, hw⟩
  have h2 : ‖ψ (n : F)‖ = |rEmb ⟨_, hw⟩ n| := by
    rw [rEmb_apply, ← Real.norm_eq_abs, InfinitePlace.norm_embedding_of_isReal]
    rfl
  rw [h2, abs_of_pos h1.1]
  exact h1.2

theorem ne_zero_of_mem_boxSet {T : ℝ} {n : 𝓞 F} (hn : n ∈ boxSet K F T) : n ≠ 0 := by
  rintro rfl
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have := (hn φ).1
  simp at this

theorem absNorm_le_of_mem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {T : ℝ} {n : 𝓞 F}
    (hn : n ∈ boxSet K F T) :
    (Ideal.absNorm (Ideal.span {n}) : ℝ) ≤ T ^ Formalism.HermitianLatticesTheory.fDeg K := by
  rw [absNorm_eq_prod_of_mem hK hF hn, ← card_real hK hF, ← Finset.card_univ, ← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun w _ => (((mem_boxSet_iff hK hF).1 hn) w).1.le)
    fun w _ => (((mem_boxSet_iff hK hF).1 hn) w).2

end Formalism.HermitianLattices.Ext.L3.BoxSum
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapConjO
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallB

section Gram

variable {K V ι : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [Fintype ι]
  [DecidableEq ι]

theorem gram_det_eq (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis ι K V) (u w : ι → V) :
    (Matrix.of fun i j => h (u i) (w j)).det =
      star (b.det u) * (Matrix.of fun i j => h (b i) (b j)).det * b.det w := by
  have hm : (Matrix.of fun i j => h (u i) (w j)) =
      (b.toMatrix u).conjTranspose * (Matrix.of fun i j => h (b i) (b j)) * b.toMatrix w := by
    ext i j
    rw [Matrix.of_apply]
    conv_lhs => rw [← b.sum_repr (u i), ← b.sum_repr (w j)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Basis.toMatrix_apply, Matrix.of_apply, smul_eq_mul,
      Finset.sum_mul, Finset.mul_sum, starRingEnd_apply, RingHom.id_apply]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hm, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Basis.det_apply,
    Basis.det_apply]

end Gram

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def gdet (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis (Fin (finrank K V)) K V) : K :=
  (Matrix.of fun i j => h (b i) (b j)).det

theorem mem_discrIdeal {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (b : Basis (Fin (finrank K V)) K V) {x : Fin (finrank K V) → V} (hx : ∀ i, x i ∈ L) {z : 𝓞 K}
    (hz : algebraMap (𝓞 K) K z = star (b.det x) * gdet h b * b.det x) : z ∈ discrIdeal h L :=
  Ideal.subset_span ⟨x, hx, by rw [hz, gram_det_eq h b]; rfl⟩

theorem discrIdeal_le {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (b : Basis (Fin (finrank K V)) K V) {I : Ideal (𝓞 K)}
    (hI : ∀ x : Fin (finrank K V) → V, (∀ i, x i ∈ L) → ∀ z : 𝓞 K,
      algebraMap (𝓞 K) K z = star (b.det x) * gdet h b * b.det x → z ∈ I) : discrIdeal h L ≤ I := by
  refine Ideal.span_le.2 ?_
  rintro z ⟨x, hx, hz⟩
  exact hI x hx z (by rw [hz, gram_det_eq h b]; rfl)

theorem exists_mixed {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (b : Basis (Fin (finrank K V)) K V)
    {u w : Fin (finrank K V) → V} (hu : ∀ i, u i ∈ L) (hw : ∀ i, w i ∈ L) :
    ∃ z : 𝓞 K, algebraMap (𝓞 K) K z = star (b.det u) * gdet h b * b.det w := by
  choose g hg using fun i j => Submodule.mem_one.mp (hLi (u i) (hu i) (w j) (hw j))
  refine ⟨(Matrix.of g).det, ?_⟩
  rw [RingHom.map_det, gdet, ← gram_det_eq h b]
  congr 1
  ext i j
  exact hg i j

theorem update_mem {L : Submodule (𝓞 K) V} {n : ℕ} {x : Fin n → V} {i : Fin n}
    (hx : ∀ k, k ≠ i → x k ∈ L) {y : V} (hy : y ∈ L) : ∀ k, Function.update x i y k ∈ L := by
  intro k
  by_cases hk : k = i
  · subst hk; rwa [Function.update_self]
  · rw [Function.update_of_ne hk]; exact hx k hk

theorem algebraMap_conjO (x : 𝓞 K) :
    algebraMap (𝓞 K) K (conjO K x) = star (algebraMap (𝓞 K) K x) := rfl

theorem mem_of_unram (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {I : Ideal (𝓞 K)} {z : 𝓞 K}
    (hz : ∀ θ : 𝓞 K, (θ - conjO K θ) * z ∈ I) : z ∈ I := by
  by_contra hn
  let J : Ideal (𝓞 K) :=
    { carrier := {c | c * z ∈ I}
      add_mem' := fun {a c} ha hc => by
        change (a + c) * z ∈ I
        rw [add_mul]; exact I.add_mem ha hc
      zero_mem' := by change (0 : 𝓞 K) * z ∈ I; rw [zero_mul]; exact I.zero_mem
      smul_mem' := fun c a ha => by
        change (c • a) * z ∈ I
        rw [smul_eq_mul, mul_assoc]; exact I.mul_mem_left c ha }
  have hJ : J ≠ ⊤ := by
    intro hJ
    have h1 : (1 : 𝓞 K) ∈ J := hJ ▸ Submodule.mem_top
    have h2 : (1 : 𝓞 K) * z ∈ I := h1
    rw [one_mul] at h2
    exact hn h2
  obtain ⟨P, hP, hJP⟩ := Ideal.exists_le_maximal J hJ
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
  exact hθ (hJP (hz θ))

theorem mixed_mem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (b : Basis (Fin (finrank K V)) K V)
    {x : Fin (finrank K V) → V} {i : Fin (finrank K V)} (hx : ∀ k, k ≠ i → x k ∈ L) {y y' : V}
    (hy : y ∈ L) (hy' : y' ∈ L) {z : 𝓞 K}
    (hz : algebraMap (𝓞 K) K z = star (b.det (Function.update x i y)) * gdet h b *
      b.det (Function.update x i y')) : z ∈ discrIdeal h L := by
  have hu := update_mem hx hy
  have hu' := update_mem hx hy'
  obtain ⟨z11, h11⟩ := exists_mixed hLi b hu hu
  obtain ⟨z22, h22⟩ := exists_mixed hLi b hu' hu'
  obtain ⟨z21, h21⟩ := exists_mixed hLi b hu' hu
  have m11 := mem_discrIdeal b hu h11
  have m22 := mem_discrIdeal b hu' h22
  have key : ∀ θ : 𝓞 K, θ * z + conjO K θ * z21 ∈ discrIdeal h L := by
    intro θ
    have hd : b.det (Function.update x i (y + θ • y')) =
        b.det (Function.update x i y) + algebraMap (𝓞 K) K θ * b.det (Function.update x i y') := by
      rw [← algebraMap_smul K θ y', AlternatingMap.map_update_add, AlternatingMap.map_update_smul,
        smul_eq_mul]
    have hw : z11 + conjO K θ * θ * z22 + θ * z + conjO K θ * z21 ∈ discrIdeal h L := by
      refine mem_discrIdeal b (update_mem hx (L.add_mem hy (L.smul_mem θ hy'))) ?_
      rw [hd]
      simp only [map_add (f := _), map_mul, h11, h22, h21, hz, algebraMap_conjO, star_add, star_mul']
      ring
    have he : θ * z + conjO K θ * z21 =
        (z11 + conjO K θ * θ * z22 + θ * z + conjO K θ * z21) - z11 - conjO K θ * θ * z22 := by
      ring
    rw [he]
    exact Ideal.sub_mem _ (Ideal.sub_mem _ hw m11) (Ideal.mul_mem_left _ _ m22)
  refine mem_of_unram hK fun θ => ?_
  have h1 := key 1
  rw [map_one, one_mul, one_mul] at h1
  have he : (θ - conjO K θ) * z = (θ * z + conjO K θ * z21) - conjO K θ * (z + z21) := by ring
  rw [he]
  exact Ideal.sub_mem _ (key θ) (Ideal.mul_mem_left _ _ h1)


omit [StarRing K] in
theorem exists_prim {J : Type*} [Finite J] (a : J → K) {j₀ : J} (ha : a j₀ ≠ 0) {P : Ideal (𝓞 K)}
    (hP : P ≠ ⊤) :
    ∃ (t : K) (c : J → 𝓞 K), (∀ j, algebraMap (𝓞 K) K (c j) = t * a j) ∧ ∃ j, c j ∉ P := by
  obtain ⟨N, hN⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K)) a
  choose e he using hN
  have hN0 : algebraMap (𝓞 K) K (N : 𝓞 K) ≠ 0 := by
    rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
    exact nonZeroDivisors.coe_ne_zero N
  have he' : ∀ j, algebraMap (𝓞 K) K (e j) = algebraMap (𝓞 K) K (N : 𝓞 K) * a j := by
    intro j
    rw [he j, Algebra.smul_def]
  have hβ : e j₀ ≠ 0 := by
    intro h0
    have := he' j₀
    rw [h0, map_zero] at this
    exact (mul_ne_zero hN0 ha) this.symm
  have hβK : algebraMap (𝓞 K) K (e j₀) ≠ 0 := by
    rwa [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
  obtain ⟨C, hC⟩ : Ideal.span (Set.range e) ∣ Ideal.span {e j₀} :=
    Ideal.dvd_iff_le.2 (Ideal.span_le.2 (by
      rintro _ rfl
      exact Ideal.subset_span ⟨j₀, rfl⟩))
  have hex : ∃ γ ∈ C, ∃ j, γ * e j ∉ P * Ideal.span {e j₀} := by
    by_contra hcon
    push Not at hcon
    have hle : Ideal.span {e j₀} ≤ P * Ideal.span {e j₀} := by
      conv_lhs => rw [hC]
      rw [mul_comm, Ideal.mul_le]
      intro γ hγ r hr
      induction hr using Submodule.span_induction with
      | mem r hr => obtain ⟨j, rfl⟩ := hr; exact hcon γ hγ j
      | zero => rw [mul_zero]; exact Ideal.zero_mem _
      | add r s _ _ hr hs => rw [mul_add]; exact Ideal.add_mem _ hr hs
      | smul c r _ hr => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ hr
    have heq : P * Ideal.span {e j₀} = 1 * Ideal.span {e j₀} := by
      rw [one_mul]; exact le_antisymm Ideal.mul_le_right hle
    have hs0 : Ideal.span {e j₀} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hβ
    exact hP (by rw [mul_right_cancel₀ hs0 heq, Ideal.one_eq_top])
  obtain ⟨γ, hγ, j₁, hj₁⟩ := hex
  have hmem : ∀ j, γ * e j ∈ Ideal.span {e j₀} := by
    intro j
    rw [hC, mul_comm γ]
    exact Ideal.mul_mem_mul (Ideal.subset_span ⟨j, rfl⟩) hγ
  choose c hc using fun j => Ideal.mem_span_singleton'.1 (hmem j)
  refine ⟨algebraMap (𝓞 K) K γ * algebraMap (𝓞 K) K (N : 𝓞 K) / algebraMap (𝓞 K) K (e j₀), c,
    fun j => ?_, j₁, fun hcP => hj₁ ?_⟩
  · have := congrArg (algebraMap (𝓞 K) K) (hc j)
    rw [map_mul, map_mul, he' j] at this
    field_simp
    rw [this]; ring
  · rw [← hc j₁]
    exact Ideal.mul_mem_mul hcP (Ideal.mem_span_singleton_self _)

end Formalism.HermitianLattices.Ext.L3.BallB
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardStabilizerAutSub
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace OrbitRepresentatives

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem gmap_mem_genus {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {I L : Submodule (𝓞 K) V}
    (hL : L ∈ Formalism.HermitianLatticesTheory.genus h I) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) :
    Formalism.HermitianLatticesTheory.gmap g L ∈ Formalism.HermitianLatticesTheory.genus h I := by
  obtain ⟨hLat, hG⟩ := hL
  have hiso : ∀ x y, h (g x) (g y) = h x y := hg
  show Submodule.IsFullLattice K (Formalism.HermitianLatticesTheory.gmap g L) ∧ Formalism.HermitianLatticesTheory.SameGenus h I (Formalism.HermitianLatticesTheory.gmap g L)
  refine ⟨?_, ?_⟩
  · refine { toIsLattice := ?_, span_eq_top := ?_ }
    · unfold Formalism.HermitianLatticesTheory.gmap
      exact Submodule.IsLattice.of_fg K (hLat.fg.map _)
    · change Submodule.span K ((g : V →ₗ[K] V) '' (L : Set V)) = ⊤
      rw [Submodule.span_image, hLat.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
      exact g.surjective
  · unfold Formalism.HermitianLatticesTheory.SameGenus
    intro p hp
    obtain ⟨g', hg', he⟩ := hG p hp
    refine ⟨g * g', mul_mem hg hg', ?_⟩
    rw [autSub_gmap_mul, he, Formalism.HermitianLattices.Ext.L3.loc_gmap]

end OrbitRepresentatives

end Formalism.HermitianLattices.Ext.L3
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsBasisLocF
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LocalSpans

variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

abbrev sF (K : Type) {F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] : Submonoid (𝓞 K) :=
  Algebra.algebraMapSubmonoid (𝓞 K) 𝔭.primeCompl

theorem closure_eq (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] :
    Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s} = sF K 𝔭 := by
  have : {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s} = (sF K 𝔭 : Set (𝓞 K)) := by
    ext s
    rfl
  rw [this, Submonoid.closure_eq]

theorem mem_locF {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime]
    (L : Submodule (𝓞 K) W) (x : W) :
    x ∈ locF 𝔭 L ↔ ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t • x ∈ L := by
  unfold locF
  rw [closure_eq]
  constructor
  · rintro ⟨s, ⟨t, ht, rfl⟩, h⟩
    exact ⟨t, ht, h⟩
  · rintro ⟨t, ht, h⟩
    exact ⟨_, ⟨t, ht, rfl⟩, h⟩

theorem sF_le (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] : sF K 𝔭 ≤ nonZeroDivisors (𝓞 K) :=
  algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ 𝔭.primeCompl_le_nonZeroDivisors

abbrev RP (K : Type) {F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K (sF K 𝔭) (sF_le 𝔭)

theorem mem_span_RP (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (N : Submodule (𝓞 K) V) (x : V) :
    x ∈ Submodule.span (RP K 𝔭) (N : Set V) ↔ x ∈ locF 𝔭 N := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact (mem_locF 𝔭 N x).2 ⟨1, fun h => (Ideal.ne_top_iff_one 𝔭).1 (Ideal.IsPrime.ne_top inferInstance) h, by simpa using hx⟩
    | zero => exact (locF 𝔭 N).zero_mem
    | add x y _ _ hx hy => exact (locF 𝔭 N).add_mem hx hy
    | smul c x _ hx =>
      obtain ⟨a, s, ⟨t, ht, rfl⟩, hc⟩ := c.2
      obtain ⟨u, hu, hx⟩ := (mem_locF 𝔭 N x).1 hx
      refine (mem_locF 𝔭 N _).2 ⟨t * u, fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim ht hu, ?_⟩
      have ht0 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
        intro h0
        have h1 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (h0.trans (map_zero _).symm)
        have h2 := (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (h1.trans (map_zero _).symm)
        exact ht (h2 ▸ 𝔭.zero_mem)
      have : algebraMap (𝓞 F) (𝓞 K) (t * u) • c • x = a • (algebraMap (𝓞 F) (𝓞 K) u • x) := by
        rw [Subalgebra.smul_def, hc, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) (t * u)),
          ← algebraMap_smul K a, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) u), smul_smul, smul_smul,
          map_mul, map_mul]
        congr 1
        field_simp
      rw [this]
      exact N.smul_mem _ hx
  · intro hx
    obtain ⟨t, ht, hx⟩ := (mem_locF 𝔭 N x).1 hx
    have ht0 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
      intro h0
      have h1 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (h0.trans (map_zero _).symm)
      have h2 := (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (h1.trans (map_zero _).symm)
      exact ht (h2 ▸ 𝔭.zero_mem)
    let c : RP K 𝔭 := ⟨(algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹,
      ⟨1, _, ⟨t, ht, rfl⟩, by simp⟩⟩
    have : x = c • (algebraMap (𝓞 F) (𝓞 K) t • x) := by
      rw [Subalgebra.smul_def, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t), smul_smul,
        inv_mul_cancel₀ ht0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)

theorem exists_basis_locF {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : ∃ b : Basis (Fin (finrank K V)) K V, (∀ i, b i ∈ L) ∧
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L := by
  have : 𝔭.IsPrime := h𝔭.isPrime
  have hp0 : 𝔭 ≠ ⊥ := fun h => RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.2 (h ▸ h𝔭))
  have : IsDedekindDomain (RP K 𝔭) := IsLocalization.isDedekindDomain (𝓞 K) (sF_le 𝔭) _
  have : IsPrincipalIdealRing (RP K 𝔭) :=
    IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 K) 𝔭 hp0
  let M : Submodule (RP K 𝔭) V := Submodule.span (RP K 𝔭) (L : Set V)
  have hMfg : M.FG := by
    obtain ⟨s, hs⟩ := hL.fg
    refine ⟨s, ?_⟩
    show _ = Submodule.span (RP K 𝔭) (L : Set V)
    rw [← hs, Submodule.span_span_of_tower]
  have : Submodule.IsFullLattice K M :=
    { toIsLattice := Submodule.IsLattice.of_fg K hMfg
      span_eq_top := by
        rw [eq_top_iff, ← hL.span_eq_top]
        exact Submodule.span_mono Submodule.subset_span }
  have : Module.Free (RP K 𝔭) M := Submodule.IsLattice.free K M
  have : Module.Finite (RP K 𝔭) M := Submodule.IsLattice.finite K M
  let b0 := Module.Free.chooseBasis (RP K 𝔭) M
  let b1 := b0.extendOfIsFullLattice K
  have hb1 : ∀ i, b1 i = (b0 i : V) := fun i => Basis.extendOfIsFullLattice_apply K b0 i
  have hmem : ∀ i, ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t • b1 i ∈ L := fun i => by
    rw [← mem_locF, ← mem_span_RP, hb1]
    exact (b0 i).2
  choose t ht htL using hmem
  have ht0 : ∀ i, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (t i)) ≠ 0 := by
    intro i h0
    have h1 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (h0.trans (map_zero _).symm)
    have h2 := (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (h1.trans (map_zero _).symm)
    exact ht i (h2 ▸ 𝔭.zero_mem)
  let b2 := b1.unitsSMul fun i => Units.mk0 _ (ht0 i)
  have hb2 : ∀ i, b2 i = algebraMap (𝓞 F) (𝓞 K) (t i) • b1 i := fun i => by
    rw [Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0, algebraMap_smul]
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b2).symm
  refine ⟨b2.reindex e, fun i => ?_, ?_⟩
  · rw [Basis.reindex_apply, hb2]
    exact htL _
  · ext x
    rw [← mem_span_RP, ← mem_span_RP, Submodule.span_span_of_tower, Basis.range_reindex]
    have : Submodule.span (RP K 𝔭) (Set.range b2) = M := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        rw [hb2]
        exact Submodule.subset_span (htL i)
      · have h1 : M = Submodule.map M.subtype (Submodule.span (RP K 𝔭) (Set.range b0)) := by
          rw [b0.span_eq, Submodule.map_top, Submodule.range_subtype]
        refine h1.le.trans ?_
        rw [Submodule.map_span, Submodule.span_le]
        rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
        let c : RP K 𝔭 := ⟨(algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (t i)))⁻¹,
          ⟨1, _, ⟨t i, ht i, rfl⟩, by simp⟩⟩
        have : M.subtype (b0 i) = c • b2 i := by
          rw [hb2, Subalgebra.smul_def, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) (t i)), smul_smul,
            inv_mul_cancel₀ (ht0 i), one_smul, hb1]
          rfl
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [this]

end Formalism.HermitianLattices.Ext.L3.LocalSpans
end
end

