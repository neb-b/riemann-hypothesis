module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0013
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0074
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0019

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementArchCocompact
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

namespace ComplementArchCocompact

section Lattice

variable {E : Type*} [Field E] [NumberField E] {W : Type*} [AddCommGroup W] [Module E W]

theorem exists_zsmul_mem {La : AddSubgroup W} (hL : IsLattice E La) (x : W) :
    ∃ d : ℤ, d ≠ 0 ∧ d • x ∈ La :=
  _root_.UpperTheory.Reformulated.B.ExistsZsmulMem.exists_zsmul_mem hL x

end Lattice

end ComplementArchCocompact

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace ComplementArchCocompact

def formAt (h : HermitianForm F E W) (v : Basis ι E W) (w : InfinitePlace E) (u : ι → ℂ) :
    (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun z := star u ⬝ᵥ (gramAt h v w *ᵥ z)
  map_add' x y := by simp [Matrix.mulVec_add, dotProduct_add]
  map_smul' c x := by simp [Matrix.mulVec_smul, dotProduct_smul]

def projAt (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) :
    (InfinitePlace E → ι → ℂ) →ₗ[ℂ] (InfinitePlace E → ι → ℂ) :=
  LinearMap.pi fun w => (LinearMap.id - (formAt h v w (vecAt v w₀ w)).smulRight (vecAt v x₀ w) -
    (formAt h v w (vecAt v x₀ w)).smulRight (vecAt v w₀ w)) ∘ₗ LinearMap.proj w

omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] [DecidableEq ι] in
theorem projAt_apply (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W)
    (Y : InfinitePlace E → ι → ℂ) (w : InfinitePlace E) :
    projAt h v x₀ w₀ Y w = Y w - (star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w)) • vecAt v x₀ w -
      (star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w)) • vecAt v w₀ w := rfl

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Fintype ι] [DecidableEq ι] in
theorem vecAt_smul_apply (v : Basis ι E W) (a : E) (x : W) (w : InfinitePlace E) :
    vecAt v (a • x) w = w.embedding a • vecAt v x w := by
  funext i; simp [vecAt]

theorem projAt_vecAt (h : HermitianForm F E W) (v : Basis ι E W) {x₀ w₀ : W}
    (hp : IsHyperbolicPair h x₀ w₀) (e : W) :
    projAt h v x₀ w₀ (vecAt v e) = vecAt v (ComplementExtension.proj hp e : W) := by
  funext w
  rw [projAt_apply, ← HermAtPlace.proof h v w w₀, ← HermAtPlace.proof h v w x₀,
    ComplementExtension.proj_apply]
  simp only [← vecAtHom_apply, map_sub, Pi.sub_apply]
  simp only [vecAtHom_apply, vecAt_smul_apply]

end ComplementArchCocompact


open ComplementArchCocompact in
theorem ComplementArchCocompact.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    ComplementArchCocompact.Statement h v := by
  classical
  intro La x₀ w₀ m hLa hp hm
  obtain ⟨hli, hdim⟩ := CoordEmbedBasis.proof E ι
  let b₀ := Pi.basis fun _ : ι => integralBasis E
  let Bs := basisOfLinearIndependentOfCardEqFinrank' _ hli
    (by rw [hdim, finrank_eq_card_basis b₀])
  let e : _ → W := fun k => v.equivFun.symm (b₀ k)
  have hBe : ∀ k, Bs k = vecAt v (e k) := by
    intro k
    rw [coe_basisOfLinearIndependentOfCardEqFinrank']
    funext w i
    rw [vecAt, coordEmbed_apply, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  let p : _ → W := fun k => (ComplementExtension.proj hp (e k) : W)
  choose d hd hdL using fun k => exists_zsmul_mem hLa (p k)
  let f : _ → W := fun k => m • d k • p k
  let D : _ → ℝ := fun k => (m : ℝ) * d k
  have hD : ∀ k, D k ≠ 0 := fun k =>
    mul_ne_zero (by exact_mod_cast hm.ne') (by exact_mod_cast hd k)
  have hf : ∀ k, vecAt v (f k) = D k • vecAt v (p k) := by
    intro k
    simp only [f, D, ← vecAtHom_apply, map_nsmul, map_zsmul]
    rw [mul_smul, Nat.cast_smul_eq_nsmul, Int.cast_smul_eq_zsmul]
  refine ⟨(fun t : _ → ℝ => ∑ k, t k • vecAt v (f k)) '' Set.Icc 0 1,
    isCompact_Icc.image (continuous_finsetSum _ fun k _ =>
      (continuous_apply k).smul continuous_const), fun Y hY => ?_⟩
  have hPY : projAt h v x₀ w₀ Y = Y := by
    funext w
    rw [projAt_apply, (hY w).1, (hY w).2, zero_smul, zero_smul, sub_zero, sub_zero]
  set s : _ → ℝ := fun k => Bs.repr Y k * (D k)⁻¹ with hs
  have hYs : Y = ∑ k, s k • vecAt v (f k) := by
    calc Y = (projAt h v x₀ w₀).restrictScalars ℝ (∑ k, Bs.repr Y k • Bs k) := by
          rw [Bs.sum_repr]; exact hPY.symm
      _ = ∑ k, Bs.repr Y k • vecAt v (p k) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, map_smul, LinearMap.restrictScalars_apply, hBe]
          exact Finset.sum_congr rfl fun k _ => by rw [projAt_vecAt]
      _ = _ := Finset.sum_congr rfl fun k _ => by
          rw [hf, smul_smul, hs, mul_assoc, inv_mul_cancel₀ (hD k), mul_one]
  refine ⟨∑ k, ⌊s k⌋ • f k, ?_, ⟨∑ k, ⌊s k⌋ • d k • p k, ?_, ?_⟩,
    ⟨fun k => Int.fract (s k), ⟨fun k => Int.fract_nonneg _, fun k => (Int.fract_lt_one _).le⟩, ?_⟩⟩
  · exact Submodule.sum_mem _ fun k _ =>
      zsmul_mem (nsmul_mem (zsmul_mem (ComplementExtension.proj hp (e k)).2 _) _) _
  · exact La.sum_mem fun k _ => La.zsmul_mem (hdL k) _
  · rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
  · show ∑ k, Int.fract (s k) • vecAt v (f k) = Y - vecAt v (∑ k, ⌊s k⌋ • f k)
    conv_rhs => rw [hYs]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← vecAtHom_apply, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, vecAtHom_apply, ← Int.cast_smul_eq_zsmul ℝ, ← sub_smul, Int.self_sub_floor]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementLattice
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

theorem isAddTorsionFree_of_module (K V : Type*) [Field K] [CharZero K] [AddCommGroup V]
    [Module K V] : IsAddTorsionFree V := by
  letI : HasUniqueDiv V := HasUniqueDiv.of_isTorsionFree K V
  infer_instance

theorem fg_of_fg_map_of_injective {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {H : AddSubgroup A} (φ : A →+ B) (hφ : Function.Injective φ) (hH : (H.map φ).FG) : H.FG := by
  have h2 : H.toIntSubmodule.FG := by
    refine Submodule.fg_of_fg_map_injective φ.toIntLinearMap hφ ?_
    have : H.toIntSubmodule.map φ.toIntLinearMap = (H.map φ).toIntSubmodule := by
      ext x
      simp
    rw [this]
    exact (Submodule.fg_iff_addSubgroup_fg _).2 hH
  exact (Submodule.fg_iff_addSubgroup_fg _).1 h2

section Complement

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]


omit [NumberField E] in
theorem factorial_nsmul_mem_of_mem_dual {h : HermitianForm F E W} {D : ℕ} {La : AddSubgroup W}
    (hLa : IsDIntegral h D La) {y : W} (hy : y ∈ dualLattice h La) : D.factorial • y ∈ La := by
  have hk : La.relIndex (dualLattice h La) • y ∈ La := by
    have := AddSubgroup.nsmul_index_mem (La.addSubgroupOf (dualLattice h La)) ⟨y, hy⟩
    exact AddSubgroup.mem_addSubgroupOf.1 this
  obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero hLa.index_ne_zero) hLa.index_le
  rw [hc, mul_comm, ← smul_smul]
  exact La.nsmul_mem hk c

theorem ComplementLattice.proof (h : HermitianForm F E W) [FiniteDimensional E W] :
    ComplementLattice.Statement h := by
  intro v₀ w₀ hvw h' hh' D n hn
  refine ⟨(D.factorial * n) ^ (finrank ℚ E * finrank E W), ?_⟩
  intro La hLa hdec
  set P : AddSubgroup (hypComplement h v₀ w₀) := La.comap (hypComplement h v₀ w₀).subtype.toAddMonoidHom with hP
  obtain ⟨hvv, hww, hvw1⟩ := hvw
  have hwv1 : h.toSesq w₀ v₀ = 1 := by
    rw [← h.isSymm.eq v₀ w₀, hvw1, map_one]
  have hsymm0 : ∀ x y : W, h.toSesq x y = 0 → h.toSesq y x = 0 := fun x y hxy => by
    rw [← h.isSymm.eq x y, hxy, map_zero]
  have memP : ∀ x : (hypComplement h v₀ w₀), x ∈ P ↔ (x : W) ∈ La := fun x => Iff.rfl

  let π₀ : W →ₗ[E] W :=
    LinearMap.id - (h.toSesq w₀).smulRight v₀ - (h.toSesq v₀).smulRight w₀
  have hπ₀ : ∀ x, π₀ x = x - h.toSesq w₀ x • v₀ - h.toSesq v₀ x • w₀ := fun x => rfl
  have hπ₀mem : ∀ x, π₀ x ∈ (hypComplement h v₀ w₀) := by
    intro x
    rw [hπ₀, mem_hypComplement]
    constructor <;> simp only [map_sub, map_smul, smul_eq_mul, hvv, hww, hvw1, hwv1] <;> ring
  have hfix : ∀ y ∈ (hypComplement h v₀ w₀), π₀ y = y := fun y hy => by
    rw [mem_hypComplement] at hy
    rw [hπ₀, hy.1, hy.2]
    simp
  have hπv : π₀ v₀ = 0 := by
    rw [hπ₀, hwv1, hvv]
    simp
  have hπw : π₀ w₀ = 0 := by
    rw [hπ₀, hww, hvw1]
    simp

  have hz : ∀ x ∈ La, ∃ a b : E, a • v₀ ∈ La ∧ b • w₀ ∈ La ∧
      n • x - a • v₀ - b • w₀ ∈ (hypComplement h v₀ w₀) ∧ n • x - a • v₀ - b • w₀ ∈ La ∧
      n • π₀ x = n • x - a • v₀ - b • w₀ := by
    intro x hx
    obtain ⟨a, ha, b, hb, hmem⟩ := hdec x hx
    change a • v₀ ∈ La at ha
    change b • w₀ ∈ La at hb
    refine ⟨a, b, ha, hb, hmem, La.sub_mem (La.sub_mem (La.nsmul_mem hx n) ha) hb, ?_⟩
    rw [← hfix _ hmem, map_sub, map_sub, map_nsmul, map_smul, map_smul, hπv, hπw]
    simp

  have hPlat : IsLattice E P := by
    refine ⟨fun a x hx => ?_, ?_, ?_⟩
    · rw [memP] at hx ⊢
      exact hLa.isLattice.smul_mem a _ hx
    · refine fg_of_fg_map_of_injective (hypComplement h v₀ w₀).subtype.toAddMonoidHom Subtype.val_injective ?_
      exact fg_of_le_fg (AddSubgroup.map_comap_le _ _) hLa.isLattice.fg
    · let π : W →ₗ[E] (hypComplement h v₀ w₀) := π₀.codRestrict (hypComplement h v₀ w₀) hπ₀mem
      have hrange : LinearMap.range π = ⊤ :=
        LinearMap.range_eq_top.2 fun y => ⟨y, Subtype.ext (hfix y y.2)⟩
      rw [eq_top_iff, ← hrange, LinearMap.range_eq_map, ← hLa.isLattice.span_eq_top,
        Submodule.map_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨a, b, -, -, -, hzLa, hkey⟩ := hz x hx
      have hnE : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
      have hnx : (n : E) • π x ∈ P := by
        rw [memP, Submodule.coe_smul_of_tower, Nat.cast_smul_eq_nsmul]
        change n • π₀ x ∈ La
        rw [hkey]
        exact hzLa
      have : π x = (n : E)⁻¹ • ((n : E) • π x) := by
        rw [smul_smul, inv_mul_cancel₀ hnE, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hnx)

  have hPint : IsIntegralOn h' P := fun x hx y hy => by
    rw [hh']
    exact hLa.integral _ hx _ hy
  set N := D.factorial * n with hN
  have hNpos : 0 < N := Nat.mul_pos (Nat.factorial_pos D) hn
  set G := dualLattice h' P with hG
  have hPG : P ≤ G := fun x hx y hy => hPint x hx y hy

  have hNG : G.map (nsmulAddMonoidHom N) ≤ P := by
    rintro _ ⟨y', hy', rfl⟩
    have hdual : n • (y' : W) ∈ dualLattice h La := by
      intro x hx
      obtain ⟨a, b, -, -, hmem, hzLa, -⟩ := hz x hx
      have hy0 := (mem_hypComplement.1 y'.2)
      have e1 : h.toSesq (y' : W) v₀ = 0 := hsymm0 _ _ hy0.1
      have e2 : h.toSesq (y' : W) w₀ = 0 := hsymm0 _ _ hy0.2
      have hnx : n • x = (n • x - a • v₀ - b • w₀) + a • v₀ + b • w₀ := by abel
      have key : h.toSesq (n • (y' : W)) x = h.toSesq (y' : W) (n • x - a • v₀ - b • w₀) := by
        rw [map_nsmul, LinearMap.smul_apply, ← map_nsmul]
        conv_lhs => rw [hnx]
        rw [map_add (f := _), map_add (f := _), map_smul, map_smul, e1, e2]
        simp
      rw [key]
      have := hy' ⟨_, hmem⟩ hzLa
      rwa [hh'] at this
    have h2 := factorial_nsmul_mem_of_mem_dual hLa hdual
    rw [nsmulAddMonoidHom_apply, memP, Submodule.coe_smul_of_tower, hN, ← smul_smul]
    exact h2

  have : IsAddTorsionFree (hypComplement h v₀ w₀) := isAddTorsionFree_of_module E (hypComplement h v₀ w₀)
  have : HasUniqueDiv (hypComplement h v₀ w₀) := HasUniqueDiv.of_isTorsionFree E _
  have hGfg : G.FG := fg_of_fg_map_of_injective (nsmulAddMonoidHom N)
    (AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree hNpos.ne')
    (fg_of_le_fg hNG hPlat.fg)
  have : Module.Finite ℤ G.toIntSubmodule :=
    Module.Finite.iff_fg.2 ((Submodule.fg_iff_addSubgroup_fg _).2 hGfg)
  have : Module.Finite ℤ G := inferInstanceAs (Module.Finite ℤ G.toIntSubmodule)
  have hrank : finrank ℤ G ≤ finrank ℚ E * finrank E W := by
    letI : Module ℚ W := Module.compHom W (algebraMap ℚ E)
    have : IsScalarTower ℚ E W := ⟨fun q e w => by
      change (q • e) • w = algebraMap ℚ E q • e • w
      rw [Algebra.smul_def, mul_smul]⟩
    have : Module.Finite ℚ W := Module.Finite.trans E W
    let b := Module.finBasis ℤ G
    let f : G →ₗ[ℤ] W := ((hypComplement h v₀ w₀).subtype.toAddMonoidHom.comp G.subtype).toIntLinearMap
    have hf : Function.Injective f := Subtype.val_injective.comp Subtype.val_injective
    have hliZ : LinearIndependent ℤ (f ∘ b) :=
      b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
    have hliQ : LinearIndependent ℚ (f ∘ b) := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ
    have := hliQ.fintype_card_le_finrank
    rw [Fintype.card_fin, ← Module.finrank_mul_finrank ℚ E W] at this
    exact this
  have hidx : P.relIndex G ≤ N ^ finrank ℤ G := by
    rw [← AddSubgroup.relIndex_map_nsmul N G]
    refine AddSubgroup.relIndex_le_of_le_left hNG ?_
    rw [AddSubgroup.relIndex_map_nsmul]
    positivity
  refine ⟨hPlat, hPint, fun h0 => ?_, ?_⟩
  · have := AddSubgroup.relIndex_eq_zero_of_le_left hNG h0
    rw [AddSubgroup.relIndex_map_nsmul] at this
    exact (pow_ne_zero _ hNpos.ne') this
  · exact hidx.trans (Nat.pow_le_pow_right hNpos hrank)

end Complement

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PImaginaryLatticeCocompact
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

theorem im_embedding_algebraMap (σ : E →+* ℂ) (c : F) : (σ (algebraMap F E c)).im = 0 := by
  have h := embedding_conj (F := F) σ (algebraMap F E c)
  rw [conj_algebraMap] at h
  exact Complex.conj_eq_iff_im.mp h.symm


omit [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
variable (F E) in
theorem exists_imaginary_integer : ∃ t : 𝓞 E, (t : E) ≠ 0 ∧ conj F E (t : E) = -(t : E) := by
  obtain ⟨ζ, hζ⟩ := exists_not_mem_range (F := F) (E := E)
  obtain ⟨y, hy0, hyi⟩ := (IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ ζ)).exists_integral_multiple
  have hθF : y • ζ ∉ Set.range (algebraMap F E) := by
    rintro ⟨c, hc⟩
    apply hζ
    refine ⟨(y : F)⁻¹ * c, ?_⟩
    have hy : (y : E) ≠ 0 := by exact_mod_cast hy0
    rw [map_mul, hc, map_inv₀, map_intCast, zsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hy, one_mul]
  have hcθ : IsIntegral ℤ (conj F E (y • ζ)) :=
    map_isIntegral_int ((conj F E : E ≃ₐ[F] E) : E →+* E) hyi
  refine ⟨⟨y • ζ - conj F E (y • ζ), hyi.sub hcθ⟩, ?_, ?_⟩
  · change y • ζ - conj F E (y • ζ) ≠ 0
    intro h
    apply hθF
    rw [← conj_eq_self_iff]
    exact (sub_eq_zero.mp h).symm
  · change conj F E (y • ζ - conj F E (y • ζ)) = -(y • ζ - conj F E (y • ζ))
    rw [map_sub, conj_conj]
    ring


omit [IsTotallyReal F] in
variable (F E) in
theorem card_infinitePlace_eq : Fintype.card (InfinitePlace E) = finrank ℚ F := by
  have h1 := IsTotallyComplex.finrank (K := E)
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
  have h3 := IsTotallyComplex.nrRealPlaces_eq_zero (K := E)
  have h4 := Module.finrank_mul_finrank ℚ F E
  rw [Algebra.IsQuadraticExtension.finrank_eq_two F E] at h4
  omega

theorem ImaginaryLatticeCocompact.proof : ImaginaryLatticeCocompact.Statement F E := by
  classical
  intro m hm
  obtain ⟨t, ht0, htc⟩ := exists_imaginary_integer F E
  let L : Free.ChooseBasisIndex ℤ (𝓞 F) → InfinitePlace E → ℝ := fun i w =>
    (w.embedding ((m : E) * algebraMap F E (integralBasis F i) * (t : E))).im
  let T : (Free.ChooseBasisIndex ℤ (𝓞 F) → ℝ) →ₗ[ℝ] (InfinitePlace E → ℝ) :=
    { toFun := fun c w => ∑ i, c i * L i w
      map_add' := by
        intro c d; ext w; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro r c; ext w; simp [Finset.mul_sum, mul_assoc] }

  have hr : ∀ w : InfinitePlace E, (w.embedding (t : E)).im ≠ 0 := by
    intro w h
    have hre : (w.embedding (t : E)).re = 0 := by
      have h1 := embedding_conj (F := F) w.embedding (t : E)
      rw [htc, map_neg] at h1
      have h2 := congrArg Complex.re h1
      simp only [Complex.neg_re, Complex.conj_re] at h2
      linarith
    exact ht0 ((map_eq_zero _).mp (Complex.ext hre h))
  have hL : ∀ i w, L i w =
      m * (w.embedding (algebraMap F E (integralBasis F i))).re * (w.embedding (t : E)).im := by
    intro i w
    simp only [L, map_mul, map_natCast, Complex.mul_im, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, im_embedding_algebraMap]
    ring
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hw : ∀ w : InfinitePlace E,
        ∑ i, c i * (w.embedding (algebraMap F E (integralBasis F i))).re = 0 := by
      intro w
      have h1 : ∑ i, c i * L i w = 0 := congrFun hc w
      have h2 : (∑ i, c i * (w.embedding (algebraMap F E (integralBasis F i))).re) *
          ((m : ℝ) * (w.embedding (t : E)).im) = 0 := by
        rw [Finset.sum_mul, ← h1]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hL]; ring
      exact (mul_eq_zero.mp h2).resolve_right
        (mul_ne_zero (by exact_mod_cast hm.ne') (hr w))
    have hτ : ∀ τ : F →+* ℂ, ∑ i, (c i : ℂ) * τ (integralBasis F i) = 0 := by
      intro τ
      let _ : Algebra F ℂ := τ.toAlgebra
      let σ : E →ₐ[F] ℂ := (by
        refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
        solve_by_elim* (maxDepth := 2) only [*,
          @_root_.DivisionSemiring.to_moduleIsTorsionFree,
          @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
      have hστ : ∀ x : F, (σ : E →+* ℂ) (algebraMap F E x) = τ x := fun x => σ.commutes x
      have hre : ∀ x : F,
          ((InfinitePlace.mk (σ : E →+* ℂ)).embedding (algebraMap F E x)).re = (τ x).re := by
        intro x
        rcases InfinitePlace.embedding_mk_eq (σ : E →+* ℂ) with h | h
        · rw [h, hστ]
        · rw [h, ComplexEmbedding.conjugate_coe_eq, hστ, Complex.conj_re]
      have him : ∀ x : F, (τ x).im = 0 := by
        intro x
        rw [← hστ]
        exact im_embedding_algebraMap (F := F) (σ : E →+* ℂ) x
      apply Complex.ext
      · rw [Complex.re_sum, Complex.zero_re, ← hw (InfinitePlace.mk (σ : E →+* ℂ))]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.re_ofReal_mul, hre]
      · rw [Complex.im_sum, Complex.zero_im]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [Complex.im_ofReal_mul, him, mul_zero]
    have hli := (canonicalEmbedding.latticeBasis F).linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    funext i
    have h0 := hli (fun i => (c i : ℂ)) (by
      funext τ
      simp only [Finset.sum_apply, Pi.smul_apply, canonicalEmbedding.latticeBasis_apply,
        canonicalEmbedding.apply_at, smul_eq_mul, Pi.zero_apply]
      exact hτ τ) i
    exact_mod_cast h0
  have hsurj : Function.Surjective T := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      card_infinitePlace_eq F E, finrank_eq_card_basis (integralBasis F)]
  refine ⟨∑ i, ∑ w, |L i w|, fun s => ?_⟩
  obtain ⟨c, hc⟩ := hsurj s
  have hint : ∀ i, IsIntegral ℤ (algebraMap F E (integralBasis F i)) := by
    intro i
    rw [integralBasis_apply]
    exact map_isIntegral_int (algebraMap F E) (RingOfIntegers.basis F i).2
  have hk : ∀ k : ℤ, IsIntegral ℤ (k : E) := fun k => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := k)
  let x : E := ∑ i, (⌊c i⌋ : E) * algebraMap F E (integralBasis F i) * (t : E)
  have hx : IsIntegral ℤ x :=
    IsIntegral.sum _ fun i _ => ((hk _).mul (hint i)).mul t.2
  refine ⟨⟨x, hx⟩, ?_, fun w => ?_⟩
  · change (m : E) * x + conj F E ((m : E) * x) = 0
    have : conj F E x = -x := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [x, map_sum, map_mul, map_intCast, conj_algebraMap, htc]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [map_mul, map_natCast, this]
    ring
  · change |(w.embedding ((m : E) * x)).im - s w| ≤ ∑ i, ∑ w, |L i w|
    have key : (w.embedding ((m : E) * x)).im = ∑ i, (⌊c i⌋ : ℝ) * L i w := by
      have e : (m : E) * x = ∑ i, (⌊c i⌋ : E) * ((m : E) * algebraMap F E (integralBasis F i) * (t : E)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e, map_sum, Complex.im_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_intCast]
      simp [Complex.mul_im, L]
    have hs : s w = ∑ i, c i * L i w := by rw [← hc]; rfl
    rw [key, hs, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    have h1 : |(⌊c i⌋ : ℝ) * L i w - c i * L i w| ≤ |L i w| := by
      rw [← sub_mul, abs_mul]
      have : |(⌊c i⌋ : ℝ) - c i| ≤ 1 := by
        rw [abs_sub_comm, abs_le]
        constructor <;> linarith [Int.floor_le (c i), Int.lt_floor_add_one (c i)]
      exact mul_le_of_le_one_left (abs_nonneg _) this
    exact h1.trans (Finset.single_le_sum (f := fun w' => |L i w'|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ w))

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

