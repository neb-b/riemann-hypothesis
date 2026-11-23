module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulOriginSec
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0017

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsogenyOfSurjectivePolAV
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory

namespace SurjIsogeny

theorem eq_bot_of_comap_eq_bot {K R S : Type} [Field K] [CommRing R] [CommRing S] [IsDomain R]
    [IsDomain S] [Algebra K R] [Algebra K S] (φ : R →+* S)
    (hφ : φ.comp (algebraMap K R) = algebraMap K S) {g : ℕ}
    (hR : Algebra.trdeg K R = g) (hS : Algebra.trdeg K S = g) {p : Ideal S}
    (hp : p.comap φ = ⊥) : p = ⊥ := by
  algebraize [φ]
  have : IsScalarTower K R S := IsScalarTower.of_algebraMap_eq' hφ.symm
  have : FaithfulSMul R S := by
    rw [faithfulSMul_iff_algebraMap_injective, RingHom.injective_iff_ker_eq_bot, eq_bot_iff, ← hp]
    exact Ideal.comap_mono bot_le
  have h := trdeg_add_eq K R (A := S)
  rw [hR, hS] at h
  have h0 : Algebra.trdeg R S = 0 := by
    have h1 : Algebra.trdeg R S + g = 0 + g := by rw [add_comm, h, zero_add]
    exact (Cardinal.add_right_inj_of_lt_aleph0 Cardinal.natCast_lt_aleph0).1 h1
  have halg := trdeg_eq_zero_iff.1 h0
  by_contra hne
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact Ideal.comap_ne_bot_of_algebraic_mem hx0 hx (halg.1 x) hp

theorem eq_genericPoint_iff {X : Scheme.{0}} [IsIntegral X] {R : CommRingCat.{0}} [IsDomain R]
    (j : Spec R ⟶ X) [IsOpenImmersion j] (p : Spec R) :
    j p = genericPoint X ↔ p.asIdeal = ⊥ := by
  rw [← genericPoint_eq_of_isOpenImmersion j, j.isOpenEmbedding.injective.eq_iff,
    genericPoint_eq_bot_of_affine]
  exact ⟨fun h => h ▸ rfl, fun h => PrimeSpectrum.ext h⟩

theorem eq_genericPoint_of_apply_eq {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) (s : Y ⟶ Spec (CommRingCat.of K)) {g : ℕ}
    (hY : SmoothOfRelativeDimension g s) (hX : SmoothOfRelativeDimension g (f ≫ s)) {x : X}
    (hx : f x = genericPoint Y) : x = genericPoint X := by
  obtain ⟨R, j, hj, y, hy⟩ := Scheme.exists_Spec_apply_eq (f x)
  obtain ⟨S, k, hk, ⟨p, rfl⟩, hsub⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := x) (U := f ⁻¹ᵁ j.opensRange) ⟨y, hy⟩
  have hr : Set.range (k ≫ f) ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    exact hsub ⟨z, rfl⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift j (k ≫ f) hr)
  have hw : Spec.map φ ≫ j = k ≫ f := by rw [hφ, IsOpenImmersion.lift_fac]
  obtain ⟨α, hα⟩ := Spec.map_surjective (j ≫ s)
  have : Nonempty (Spec R) := ⟨y⟩
  have : Nonempty (Spec S) := ⟨p⟩
  have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion j
  have : IsIntegral (Spec S) := isIntegral_of_isOpenImmersion k
  have : IsDomain R := (affine_isIntegral_iff R).1 inferInstance
  have : IsDomain S := (affine_isIntegral_iff S).1 inferInstance
  letI : Algebra K R := α.hom.toAlgebra
  letI : Algebra K S := (α ≫ φ).hom.toAlgebra
  have hR := trdeg_eq_of_smoothOfRelativeDimension K Y s g hY R j hj hα.symm
  have hS := trdeg_eq_of_smoothOfRelativeDimension K X (f ≫ s) g hX S k hk (by
    rw [← reassoc_of% hw, ← hα, ← Spec.map_comp]; rfl)
  rw [eq_genericPoint_iff]
  refine eq_bot_of_comap_eq_bot φ.hom rfl hR hS ?_
  refine (eq_genericPoint_iff j (Spec.map φ p)).1 ?_
  rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply, hx]

theorem isPullback_kernel_mul {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {Z A B : C} [GrpObj A] [GrpObj B] {i : Z ⟶ A} {ψ : A ⟶ B} [IsMonHom ψ]
    (hp : IsPullback i (toUnit Z) ψ η[B]) :
    IsPullback ((fst Z A ≫ i) * snd Z A) (snd Z A) ψ ψ := by
  have hi : i ≫ ψ = 1 := hp.w
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => lift (hp.lift (s.fst * s.snd⁻¹) (toUnit _) ?_) s.snd) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · rw [MonObj.mul_comp, Category.assoc, hi, MonObj.comp_one, _root_.one_mul]
  · rw [MonObj.mul_comp, GrpObj.inv_comp, s.condition, mul_inv_cancel, Hom.one_def]
  · rw [MonObj.comp_mul, lift_fst_assoc, hp.lift_fst, lift_snd, inv_mul_cancel_right]
  · exact lift_snd _ _
  · refine CartesianMonoidalCategory.hom_ext _ _ ?_ (by rw [lift_snd, h2])
    refine hp.hom_ext ?_ (toUnit_unique _ _)
    rw [lift_fst, hp.lift_fst, ← h1, ← h2, MonObj.comp_mul, mul_inv_cancel_right, Category.assoc]

theorem locallyQuasiFinite_of_finite_fibre {S : Scheme.{0}} [Subsingleton S] {A B : Over S}
    [GrpObj A] [GrpObj B] (ψ : A ⟶ B) [IsMonHom ψ] [Surjective ψ.left]
    [LocallyOfFiniteType ψ.left] [QuasiCompact ψ.left] (a : A.left)
    (h : (ψ.left ⁻¹' {ψ.left a}).Finite) : LocallyQuasiFinite ψ.left := by
  have hp : IsPullback (pullback.fst ψ η[B]) (toUnit _) ψ η[B] := by
    have := IsPullback.of_hasPullback ψ η[B]
    rwa [toUnit_unique (pullback.snd ψ η[B]) (toUnit _)] at this
  generalize pullback.fst ψ η[B] = i at hp
  generalize pullback ψ η[B] = Z at i hp
  have hl := hp.map (Over.forget S)
  have hZ1 : LocallyOfFiniteType Z.hom := by
    simpa using MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hl ‹_›
  have hZ2 : QuasiCompact Z.hom := by
    simpa using MorphismProperty.of_isPullback (P := @QuasiCompact) hl ‹_›
  have h1 : IsPullback ((fst Z A ≫ i) * snd Z A).left (pullback.snd Z.hom A.hom) ψ.left ψ.left :=
    (isPullback_kernel_mul hp).map (Over.forget S)
  let j := A.left.fromSpecResidueField a
  have h2 := IsPullback.of_hasPullback (pullback.snd Z.hom A.hom) j
  have h3 := h2.paste_horiz h1
  have h4 := h2.paste_horiz (IsPullback.of_hasPullback Z.hom A.hom)
  have hF : LocallyQuasiFinite (ψ.left.fiberToSpecResidueField (ψ.left a)) := by
    have : Finite (ψ.left.fiber (ψ.left a)) :=
      (ψ.left.fiberHomeo (ψ.left a)).toEquiv.finite_iff.2 h.to_subtype
    have : LocallyOfFiniteType (ψ.left.fiberToSpecResidueField (ψ.left a)) :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
    exact LocallyQuasiFinite.of_finite_preimage_singleton _ fun _ => Set.toFinite _
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField] at h3
  have h5 := h3.of_right' (IsPullback.of_hasPullback ψ.left
    (B.left.fromSpecResidueField (ψ.left a)))
  have h6 : LocallyQuasiFinite (pullback.snd (pullback.snd Z.hom A.hom) j) :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) h5 hF
  have h7 : LocallyQuasiFinite Z.hom :=
    Unif.locallyQuasiFinite_of_isPullback_surjective _ _ _ _ _ _ _ _ h4
      ⟨fun _ => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩ hZ1 hZ2 h6
  exact Unif.locallyQuasiFinite_of_isPullback_surjective _ _ _ _ _ _ _ _ h1 ‹_› ‹_› ‹_›
    inferInstance

end SurjIsogeny


open SurjIsogeny IsogenyModel in
theorem isogeny_of_surjective_of_dim_eq : Out.Laws → ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (B : Over (Sp K)) [GrpObj B] (ψ : P.A ⟶ B), IsAbelianScheme B → SmoothOfRelativeDimension P.g B.hom → IsMonHom ψ → Surjective ψ.left → IsFinite ψ.left ∧ Flat ψ.left ∧ ∃ n : ℕ, 1 ≤ n ∧ ∀ (T : Over (Sp K)) (x : T ⟶ P.A), x ≫ ψ = 1 → x ^ n = 1 := by
  intro hL K _ P B _ ψ hB hg _ _
  have := hB.proper
  have := P.isAb.proper
  have := P.isAb.comm
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ B.hom hB.smooth
    hB.geomConnected
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ P.A.hom
    P.isAb.smooth P.isAb.geomConnected
  have : IsIntegral P.A.left := GeometricallyIntegral.isIntegral_of_subsingleton P.A.hom
  have : IsProper (ψ.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper ψ.left := IsProper.of_comp ψ.left B.hom
  have hA : SmoothOfRelativeDimension P.g (ψ.left ≫ B.hom) := by rw [Over.w]; exact P.smoothDim
  obtain ⟨a, ha⟩ := ψ.left.surjective (genericPoint B.left)
  have : LocallyQuasiFinite ψ.left := by
    refine locallyQuasiFinite_of_finite_fibre ψ a ((Set.finite_singleton (genericPoint _)).subset ?_)
    intro x hx
    exact eq_genericPoint_of_apply_eq ψ.left B.hom hg hA (ha ▸ hx)
  have hf : IsFinite ψ.left := .of_isProper_of_locallyQuasiFinite _
  obtain ⟨Z, _, i, _, hi, hZ, hk⟩ := exists_kernel ψ
  have hm : Mono i := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono i.left))
  have := isCommMonObj_of_mono i
  obtain ⟨N, hN, hZN⟩ := FiniteFlatKilled.main K Z hZ inferInstance
  obtain ⟨A, _, hA', q, _, _, _, _, hq⟩ := hL.quotient K P Z i ‹_› hm hZ inferInstance
  have := hA'.proper
  obtain ⟨e, -, he⟩ := exists_iso_of_same_kernel q ψ i hq hk
  refine ⟨hf, ?_, N, hN, fun T x hx => ?_⟩
  · have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    rw [← he, Over.comp_left]
    infer_instance
  · have h1 : i ^ N = 1 := by
      rw [← Category.id_comp i, ← MonObj.pow_comp, hZN, MonObj.one_comp]
    rw [← hk.lift_fst x (toUnit _) hx, ← MonObj.comp_pow, h1, MonObj.comp_one]

theorem isogeny_of_surjective_polAV : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] (σ : K →+* ℂ) (P P' : Out.PolAV (Sp K)) (ψ : P.A ⟶ P'.A), P.g = P'.g → IsMonHom ψ → Surjective ψ.left → IsFinite ψ.left ∧ Flat ψ.left ∧ ∃ n : ℕ, 1 ≤ n ∧ ∀ (T : Over (Sp K)) (x : T ⟶ P.A), x ≫ ψ = 1 → x ^ n = 1 :=
  fun _ hL K _ _ P P' ψ hg => isogeny_of_surjective_of_dim_eq hL K P P'.A ψ P'.isAb
    (hg ▸ P'.smoothDim)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LbIsoCubeLBMulRightOf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.LamCalc

open GlobalTheory.PrimNorm

section Tensor

variable {X X' Y : Scheme.{0}}

theorem exists_gen_tensor {C A B : LB Y} (a : C.ι → A.ι) (b : C.ι → B.ι) (la : ∀ i, C.U i ≤ A.U (a i))
    (lb : ∀ i, C.U i ≤ B.U (b i))
    (hg : ∀ (y : Y) i j, y ∈ C.U i → y ∈ C.U j → gm (𝟙 Y) y (C.U i ⊓ C.U j) (C.g i j) =
      gm (𝟙 Y) y (A.U (a i) ⊓ A.U (a j)) (A.g (a i) (a j)) * gm (𝟙 Y) y (B.U (b i) ⊓ B.U (b j)) (B.g (b i) (b j)))
    (s : LB.Gen A) (hs : s.IsGen) (t : LB.Gen B) (ht : t.IsGen) : ∃ u : LB.Gen C, u.IsGen := by
  refine ⟨⟨fun i => res (la i) (s.s (a i)) * res (lb i) (t.s (b i))⟩, fun i j => unit_ext fun y hy => ?_⟩
  have ma : (𝟙 Y : Y ⟶ Y) y ∈ A.U (a i) ⊓ A.U (a j) := ⟨la i hy.1, la j hy.2⟩
  have mb : (𝟙 Y : Y ⟶ Y) y ∈ B.U (b i) ⊓ B.U (b j) := ⟨lb i hy.1, lb j hy.2⟩
  have ea := (gm_res _ y _ ma _).symm.trans ((congrArg (gm (𝟙 Y) y _) (hs (a i) (a j))).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) rfl (gm_res _ y _ ma _))))
  have eb := (gm_res _ y _ mb _).symm.trans ((congrArg (gm (𝟙 Y) y _) (ht (b i) (b j))).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) rfl (gm_res _ y _ mb _))))
  have v : ∀ i, y ∈ C.U i → gm (𝟙 Y) y (C.U i) (res (la i) (s.s (a i)) * res (lb i) (t.s (b i))) =
      gm (𝟙 Y) y (A.U (a i)) (s.s (a i)) * gm (𝟙 Y) y (B.U (b i)) (t.s (b i)) := fun i hi =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y _ hi _) (gm_res _ y _ hi _))
  refine ((gm_res _ y _ hy _).trans ((v i hy.1).trans (congrArg₂ (· * ·) ea eb))).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (hg y i j hy.1 hy.2)
    ((gm_res _ y _ hy _).trans (v j hy.2)))).trans ?_
  exact mul_mul_mul_comm _ _ _ _

theorem lbIso_sum {L : LB X} {M : LB X'} {K K' J J' : Type} [Fintype K] [Fintype K'] [Fintype J] [Fintype J']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {ψ : J → (Y ⟶ X')} {δ : J → ℤ} {ψ' : J' → (Y ⟶ X')} {δ' : J' → ℤ}
    (h : LBIso (LB.LinComb L φ ε) (LB.LinComb M ψ δ)) (h' : LBIso (LB.LinComb L φ' ε') (LB.LinComb M ψ' δ')) :
    LBIso (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')) (LB.LinComb M (Sum.elim ψ ψ') (Sum.elim δ δ')) := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨w', hw'⟩ := h'
  have l₁ : ∀ p : (J ⊕ J' → M.ι) × (K ⊕ K' → L.ι),
      LB.wchart M (Sum.elim ψ ψ') p.1 ⊓ LB.wchart L (Sum.elim φ φ') p.2 ≤
        LB.wchart M ψ (p.1 ∘ Sum.inl) ⊓ LB.wchart L φ (p.2 ∘ Sum.inl) := fun p y hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (.inl k), Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 (.inl k)⟩
  have l₂ : ∀ p : (J ⊕ J' → M.ι) × (K ⊕ K' → L.ι),
      LB.wchart M (Sum.elim ψ ψ') p.1 ⊓ LB.wchart L (Sum.elim φ φ') p.2 ≤
        LB.wchart M ψ' (p.1 ∘ Sum.inr) ⊓ LB.wchart L φ' (p.2 ∘ Sum.inr) := fun p y hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (.inr k), Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 (.inr k)⟩
  refine exists_gen_tensor (C := LB.div (LB.LinComb M (Sum.elim ψ ψ') (Sum.elim δ δ'))
    (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε'))) (A := LB.div (LB.LinComb M ψ δ) (LB.LinComb L φ ε))
    (B := LB.div (LB.LinComb M ψ' δ') (LB.LinComb L φ' ε')) (fun p => (p.1 ∘ Sum.inl, p.2 ∘ Sum.inl))
    (fun p => (p.1 ∘ Sum.inr, p.2 ∘ Sum.inr)) l₁ l₂ (fun y p q hp hq => ?_) w hw w' hw'
  refine ((gm_div _ _ (𝟙 Y) y p q ⟨hp, hq⟩).trans (congrArg₂ (fun a b => a * b⁻¹)
    (gm_linComb M _ _ (𝟙 Y) y p.1 q.1 hp.1 hq.1) (gm_linComb L _ _ (𝟙 Y) y p.2 q.2 hp.2 hq.2))).trans (Eq.symm ?_)
  refine (congrArg₂ (· * ·)
    ((gm_div (LB.LinComb L φ ε) (LB.LinComb M ψ δ) (𝟙 Y) y (p.1 ∘ Sum.inl, p.2 ∘ Sum.inl) (q.1 ∘ Sum.inl, q.2 ∘ Sum.inl)
      ⟨l₁ p hp, l₁ q hq⟩).trans (congrArg₂ (fun a b => a * b⁻¹)
      (gm_linComb M ψ δ (𝟙 Y) y _ _ (l₁ p hp).1 (l₁ q hq).1) (gm_linComb L φ ε (𝟙 Y) y _ _ (l₁ p hp).2 (l₁ q hq).2)))
    ((gm_div (LB.LinComb L φ' ε') (LB.LinComb M ψ' δ') (𝟙 Y) y (p.1 ∘ Sum.inr, p.2 ∘ Sum.inr)
      (q.1 ∘ Sum.inr, q.2 ∘ Sum.inr) ⟨l₂ p hp, l₂ q hq⟩).trans (congrArg₂ (fun a b => a * b⁻¹)
      (gm_linComb M ψ' δ' (𝟙 Y) y _ _ (l₂ p hp).1 (l₂ q hq).1)
      (gm_linComb L φ' ε' (𝟙 Y) y _ _ (l₂ p hp).2 (l₂ q hq).2)))).trans ?_
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

end Tensor

section Cube

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  {L : LB A.left} {M : LB B.left} {T : Over S}

omit [IsCommMonObj A] in
theorem cubeLB_isLB (hL : L.IsLB) {n : ℕ} (x : Fin n → (T ⟶ A)) : (cubeLB A x L).IsLB :=
  DVR.linComb_isLB _ hL _ _

theorem class_cubeLB {U : Type*} [CommGroup U] (cl : LB T.left → U) (m : (T.left ⟶ A.left) → U)
    (h : ∀ (I : Type) [Fintype I] (φ : I → (T.left ⟶ A.left)) (ε : I → ℤ), cl (LB.LinComb L φ ε) = ∏ k, m (φ k) ^ ε k)
    (x y : T ⟶ A) :
    cl (cubeLB A ![x, y] L) = m (x * y).left * (m x.left)⁻¹ * (m y.left)⁻¹ * m (1 : T ⟶ A).left := by
  have e := congrArg (FreeGroup.lift m |> Abelianization.lift)
    (prod_square_id x y (fun q => Abelianization.of (FreeGroup.of q)))
  have hm (q : T.left ⟶ A.left) :
      (Abelianization.lift (FreeGroup.lift m)) (Abelianization.of (FreeGroup.of q)) = m q := by
    exact (Group.Abelianization.lift_apply_of _ _).trans FreeGroup.lift_apply_of
  simp only [diff₂, map_prod, map_zpow, map_mul, map_inv, hm] at e
  exact (h _ _ _).trans e

theorem lbIso_cubeLB_swap (hL : L.IsLB) (x y : T ⟶ A) : LBIso (cubeLB A ![x, y] L) (cubeLB A ![y, x] L) :=
  (lbIso_iff hL _ _ _ _).2 ((prod_square_id x y (cls L)).trans ((diff₂_comm _ _).trans
    (prod_square_id y x (cls L)).symm))

def cubeProd (L : LB A.left) (x y x' y' : T ⟶ A) : LB T.left :=
  LB.LinComb L (K := ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2)))
    (Sum.elim (fun I => (psum A ![x, y] I.down).left) (fun I => (psum A ![x', y'] I.down).left))
    (Sum.elim (fun I => (-1) ^ (2 - I.down.card)) (fun I => (-1) ^ (2 - I.down.card)))

theorem lbIso_cubeLB_mul_left (hL : L.IsLB) (hT : ∃ t : LB.Gen (Theta A L), t.IsGen) (x x' y : T ⟶ A) :
    LBIso (cubeLB A ![x * x', y] L) (cubeProd L x y x' y) := by
  refine (lbIso_iff hL _ _ _ _).2 ((prod_square_id _ _ (cls L)).trans ?_)
  rw [Fintype.prod_sum_type]
  exact (diff₂_mul_left (diff₃_ptCls hL hT) x x' y).trans
    (congrArg₂ (· * ·) (prod_square_id x y (cls L)).symm (prod_square_id x' y (cls L)).symm)

theorem lbIso_cubeLB_mul_right (hL : L.IsLB) (hT : ∃ t : LB.Gen (Theta A L), t.IsGen) (x y y' : T ⟶ A) :
    LBIso (cubeLB A ![x, y * y'] L) (cubeProd L x y x y') := by
  refine (lbIso_iff hL _ _ _ _).2 ((prod_square_id _ _ (cls L)).trans ?_)
  rw [Fintype.prod_sum_type]
  exact (diff₂_mul_right (diff₃_ptCls hL hT) x y y').trans
    (congrArg₂ (· * ·) (prod_square_id x y (cls L)).symm (prod_square_id x y' (cls L)).symm)

theorem lbIso_cubeLB_mul_left_of (hL : L.IsLB) (hM : M.IsLB) (hT : ∃ t : LB.Gen (Theta A L), t.IsGen)
    (hT' : ∃ t : LB.Gen (Theta B M), t.IsGen) {x x' y : T ⟶ A} {u u' v : T ⟶ B}
    (h : LBIso (cubeLB A ![x, y] L) (cubeLB B ![u, v] M)) (h' : LBIso (cubeLB A ![x', y] L) (cubeLB B ![u', v] M)) :
    LBIso (cubeLB A ![x * x', y] L) (cubeLB B ![u * u', v] M) :=
  have a : (cubeProd L x y x' y).IsLB := DVR.linComb_isLB _ hL _ _
  have b : (cubeProd M u v u' v).IsLB := DVR.linComb_isLB _ hM _ _
  LBIso.trans (cubeLB_isLB hL _) a (cubeLB_isLB hM _) (lbIso_cubeLB_mul_left hL hT x x' y)
    (LBIso.trans a b (cubeLB_isLB hM _) (lbIso_sum h h') (lbIso_cubeLB_mul_left hM hT' u u' v).symm)

theorem lbIso_cubeLB_mul_right_of (hL : L.IsLB) (hM : M.IsLB) (hT : ∃ t : LB.Gen (Theta A L), t.IsGen)
    (hT' : ∃ t : LB.Gen (Theta B M), t.IsGen) {x y y' : T ⟶ A} {u v v' : T ⟶ B}
    (h : LBIso (cubeLB A ![x, y] L) (cubeLB B ![u, v] M)) (h' : LBIso (cubeLB A ![x, y'] L) (cubeLB B ![u, v'] M)) :
    LBIso (cubeLB A ![x, y * y'] L) (cubeLB B ![u, v * v'] M) :=
  have a : (cubeProd L x y x y').IsLB := DVR.linComb_isLB _ hL _ _
  have b : (cubeProd M u v u v').IsLB := DVR.linComb_isLB _ hM _ _
  LBIso.trans (cubeLB_isLB hL _) a (cubeLB_isLB hM _) (lbIso_cubeLB_mul_right hL hT x y y')
    (LBIso.trans a b (cubeLB_isLB hM _) (lbIso_sum h h') (lbIso_cubeLB_mul_right hM hT' u v v').symm)

theorem lbIso_cubeLB_hom (ψ : A ⟶ B) [IsMonHom ψ] (h : LBIso L (M.pull ψ.left)) (x y : T ⟶ A) :
    LBIso (cubeLB A ![x, y] L) (cubeLB B ![x ≫ ψ, y ≫ ψ] M) := by
  obtain ⟨w, hw⟩ := h
  let ρ : (T ⟶ A) →* (T ⟶ B) := MonoidHom.mk' (· ≫ ψ) fun x y => MonObj.mul_comp x y ψ
  refine (iso_linComb ((isGen_iff w).1 hw) _ _).chartPull (chartPullId _)
    (chartPullSame M _ _ _ (𝟙 _) fun I => ?_)
  have e : (fun i => ρ (![x, y] i)) = ![x ≫ ψ, y ≫ ψ] := funext fun i => by fin_cases i <;> rfl
  rw [Category.id_comp, ← e, ← psum_hom ρ]
  rfl

variable {X Y : Over S} {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B} {g₂ : Y ⟶ B}

theorem lbIso_of_lamEq (h : LamEq L f₁ f₂ M g₁ g₂) (x : T ⟶ X) (y : T ⟶ Y) :
    LBIso (cubeLB A ![x ≫ f₁, y ≫ f₂] L) (cubeLB B ![x ≫ g₁, y ≫ g₂] M) :=
  LBIso.chartPull (chartSquare L (lift x y) (by simp) (by simp)) (chartSquare M (lift x y) (by simp) (by simp)) h

end Cube

theorem lamEq_calculus : ∀ (S : Scheme.{0}) (X Y A B C : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] [GrpObj C] [IsCommMonObj C] (L : LB A.left) (M : LB B.left) (N : LB C.left), L.IsLB → M.IsLB → N.IsLB →
  ∀ (f₁ f₁' : X ⟶ A) (f₂ f₂' : Y ⟶ A) (g₁ g₁' : X ⟶ B) (g₂ g₂' : Y ⟶ B) (k₁ : X ⟶ C) (k₂ : Y ⟶ C),
  LamEq L f₁ f₂ L f₁ f₂ ∧ (LamEq L f₁ f₂ M g₁ g₂ → LamEq M g₁ g₂ L f₁ f₂ ∧ LamEq L f₂ f₁ M g₂ g₁ ∧ (LamEq M g₁ g₂ N k₁ k₂ → LamEq L f₁ f₂ N k₁ k₂) ∧
    (∀ (X' Y' : Over S) (a : X' ⟶ X) (b : Y' ⟶ Y), LamEq L (a ≫ f₁) (b ≫ f₂) M (a ≫ g₁) (b ≫ g₂)) ∧
    ∀ (T : Over S) (x : T ⟶ X) (y : T ⟶ Y), LBIso (cubeLB A ![x ≫ f₁, y ≫ f₂] L) (cubeLB B ![x ≫ g₁, y ≫ g₂] M)) ∧
  ((∃ t : LB.Gen (Theta A L), t.IsGen) → (∃ t : LB.Gen (Theta B M), t.IsGen) → LamEq L f₁ f₂ M g₁ g₂ → (LamEq L f₁' f₂ M g₁' g₂ → LamEq L (f₁ * f₁') f₂ M (g₁ * g₁') g₂) ∧ (LamEq L f₁ f₂' M g₁ g₂' → LamEq L f₁ (f₂ * f₂') M g₁ (g₂ * g₂'))) ∧
  ∀ ψ : A ⟶ B, IsMonHom ψ → LBIso L (M.pull ψ.left) → LamEq L f₁ f₂ M (f₁ ≫ ψ) (f₂ ≫ ψ) := by
  intro S X Y A B C _ _ _ _ _ _ L M N hL hM hN f₁ f₁' f₂ f₂' g₁ g₁' g₂ g₂' k₁ k₂
  refine ⟨(lbIso_iff hL _ _ _ _).2 rfl, fun h => ⟨LBIso.symm h, ?_, fun h' => ?_, fun X' Y' a b => ?_,
    fun T x y => lbIso_of_lamEq h x y⟩, fun hT hT' h => ⟨fun h' => ?_, fun h' => ?_⟩, fun ψ hψ h => ?_⟩
  · exact LBIso.trans (cubeLB_isLB hL _) (cubeLB_isLB hL _) (cubeLB_isLB hM _) (lbIso_cubeLB_swap hL _ _)
      (LBIso.trans (cubeLB_isLB hL _) (cubeLB_isLB hM _) (cubeLB_isLB hM _)
        (lbIso_of_lamEq h (snd Y X) (fst Y X)) (lbIso_cubeLB_swap hM _ _))
  · exact LBIso.trans (cubeLB_isLB hL _) (cubeLB_isLB hM _) (cubeLB_isLB hN _) h h'
  · have e := lbIso_of_lamEq h (fst X' Y' ≫ a) (snd X' Y' ≫ b)
    simp only [Category.assoc] at e
    exact e
  · unfold LamEq
    rw [MonObj.comp_mul, MonObj.comp_mul]
    exact lbIso_cubeLB_mul_left_of hL hM hT hT' h h'
  · unfold LamEq
    rw [MonObj.comp_mul, MonObj.comp_mul]
    exact lbIso_cubeLB_mul_right_of hL hM hT hT' h h'
  · have e := lbIso_cubeLB_hom ψ h (fst X Y ≫ f₁) (snd X Y ≫ f₂)
    simp only [Category.assoc] at e
    exact e

end GlobalTheory.LamCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MapRtEqNegIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem map_rt_eq_neg_iff {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {R : Type} [CommRing R]
    [CharZero R] {ρ : R} (hρ : ρ ^ 2 = -(H.d : R)) {k : Type} [Field k] (β : R →+* k) (hβ : Function.Injective β)
    (τ : 𝓞 E →+* k) : τ H.rt = β (-ρ) ↔ τ H.rt ≠ β ρ := by
  have h1 : (τ H.rt) ^ 2 = (β ρ) ^ 2 := by
    rw [← map_pow, ← map_pow, H.rt_sq, hρ]; simp
  have h2 : β (-ρ) ≠ β ρ := by
    intro h
    have h3 : -ρ = ρ := hβ h
    have h4 : ((2 * H.d : ℕ) : R) = 0 := by
      push_cast
      linear_combination 2 * hρ + ρ * h3
    have h5 : 2 * H.d = 0 := Nat.cast_eq_zero.mp h4
    have := H.d_prime.pos
    omega
  constructor
  · intro h h'
    exact h2 (h.symm.trans h')
  · intro h
    rw [map_neg]
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp h1).resolve_left h

theorem hasType_neg_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [CharZero R] (G : Over (Sp R)) [GrpObj G] (act : OAct (𝓞 E) G) (ρ : R) (p q : ℕ), ρ ^ 2 = -(H.d : R) → (HasType H act ρ p q ↔ HasType H act (-ρ) q p) := by
  intro E _ _ _ H R _ _ G _ act ρ p q hρ
  unfold HasType
  refine forall_congr' fun k => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun β =>
    forall_congr' fun hβ => forall_congr' fun τ => ?_
  have h := map_rt_eq_neg_iff H hρ β hβ τ
  rw [ne_eq (τ H.rt) (β (-ρ)), h, not_not]
  exact and_comm

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OriginLineBundlePolarisationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.originLineBundle_polarisation : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R) [GrpObj (schemeOver W)], IsCommMonObj (schemeOver W) → η[schemeOver W].left = zero W → Out.Rigidified (schemeOver W) (originLB W) ∧ Out.Sym (schemeOver W) (originLB W) ∧ Out.RelAmple (schemeOver W) (originLB W) ∧ Out.KTriv (schemeOver W) (originLB W) := by
  first | exact @GlobalTheory.WeierstrassCurve.originLB_polarisation | exact GlobalTheory.WeierstrassCurve.originLB_polarisation | (intros; apply GlobalTheory.WeierstrassCurve.originLB_polarisation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.QuadraticEquationOfDerivative
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.LieMultiple

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem isLieComb_natCast_pow {v : epsR R ⟶ G} (hv : IsTangent v) (n : ℕ) :
    IsLieComb ![(n : R)] ![v] (v ^ n) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, pow_zero]
    exact (lieMultiple_calculus R G G v v v 0 0).2.2.2.2.2 hv
  | succ n ih =>
    rw [Nat.cast_succ, pow_succ]
    exact (lieMultiple_calculus R G G v _ v n 1).2.1 hv ih
      (lieMultiple_calculus R G G v v v 0 0).2.2.2.2.1

theorem isMonHom_id_pow [IsCommMonObj G] (n : ℕ) : IsMonHom ((𝟙 G) ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact inferInstanceAs (IsMonHom (toUnit G ≫ η[G]))
  | succ n ih =>
    rw [pow_succ]
    exact inferInstanceAs (IsMonHom (lift ((𝟙 G) ^ n) (𝟙 G) ≫ μ[G]))

theorem quadratic_equation_of_derivative : ThetaUnifAV → Out.PolBaseChangeSt → ∀ (k : Type) [Field k] (s : k →+* ℂ) (P : Out.PolAV (Sp k)) (v : epsR k ⟶ P.A) (W : P.A ⟶ P.A) (w : k) (n : ℕ), IsTangent v → (∀ (R' : Type) [CommRing R'] (f' : k →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) → IsMonHom W → IsLieComb ![w] ![v] (v ≫ W) → w * w + n = w → (W ≫ W) * (𝟙 P.A) ^ n = W := by
  intro hT hB k _ s P v W w n hv hb hW hw heq
  have hc := P.isAb.comm
  have h1 := isMonHom_id_pow (G := P.A) n
  have h2 : IsMonHom ((W ≫ W) * (𝟙 P.A) ^ n) :=
    inferInstanceAs (IsMonHom (lift (W ≫ W) ((𝟙 P.A) ^ n) ≫ μ[P.A]))
  refine _root_.GlobalTheory.HomUnique.hom_ext_of_lieBasis hT hB k s P P v _ _ hb h2 hW ?_
  have h3 : IsLieComb ![w] ![v ≫ W] ((v ≫ W) ≫ W) :=
    (lieMultiple_calculus k P.A P.A v _ v w w).2.2.2.1 W hw
  have h4 : IsLieComb ![w * w] ![v] ((v ≫ W) ≫ W) :=
    (lieMultiple_calculus k P.A P.A v _ _ w w).2.2.1 hw h3
  have h5 : IsLieComb ![w * w + n] ![v] (((v ≫ W) ≫ W) * v ^ n) :=
    (lieMultiple_calculus k P.A P.A v _ _ (w * w) n).2.1 hv h4 (isLieComb_natCast_pow hv n)
  rw [heq, isLieComb_one_iff_comp] at h5
  rw [isLieComb_one_iff_comp] at hw
  rw [MonObj.comp_mul, MonObj.comp_pow, Category.comp_id, ← Category.assoc, h5, ← hw]

end GlobalTheory.LieMultiple
end
end

