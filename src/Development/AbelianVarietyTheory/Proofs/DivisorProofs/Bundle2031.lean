module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1963
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosDefMapIntOfPos
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc Matrix

namespace GlobalTheory.Poinc

theorem posDef_map_int_of_pos {n : ℕ} (L : Matrix (Fin n) (Fin n) ℤ) (hs : L.IsSymm)
    (hp : ∀ ξ : Fin n → ℤ, ξ ≠ 0 → 0 < ξ ⬝ᵥ (L *ᵥ ξ)) : (L.map (Int.cast : ℤ → ℝ)).PosDef := by
  set M := L.map (Int.cast : ℤ → ℝ) with hM
  have hH : M.IsHermitian := by
    refine Matrix.IsHermitian.ext fun i j => ?_
    simp [M, hs.apply]
  have hdet : L.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hLv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have := hp v hv
    rw [hLv, dotProduct_zero] at this
    exact lt_irrefl _ this
  have hint : ∀ z : Fin n → ℤ, (fun i => (z i : ℝ)) ⬝ᵥ (M *ᵥ fun i => (z i : ℝ)) = ((z ⬝ᵥ (L *ᵥ z) : ℤ) : ℝ) := by
    intro z
    simp [M, dotProduct, mulVec]
  have hrat : ∀ t : Fin n → ℚ, 0 ≤ (fun i => (t i : ℝ)) ⬝ᵥ (M *ᵥ fun i => (t i : ℝ)) := by
    intro t
    obtain ⟨⟨D, hD⟩, hn⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) t
    choose z hz using hn
    have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hD
    have hz' : (fun i => (z i : ℝ)) = (D : ℝ) • fun i => (t i : ℝ) := by
      funext i
      have h1 : (z i : ℚ) = D * t i := by simpa [Submonoid.smul_def] using hz i
      have h2 := congrArg (Rat.cast : ℚ → ℝ) h1
      push_cast at h2
      simpa using h2
    have h0 : 0 ≤ z ⬝ᵥ (L *ᵥ z) := by
      rcases eq_or_ne z 0 with h | h
      · simp [h]
      · exact (hp z h).le
    have h3 := hint z
    rw [hz', mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at h3
    have h4 : 0 ≤ ((D : ℝ) * D) * ((fun i => (t i : ℝ)) ⬝ᵥ (M *ᵥ fun i => (t i : ℝ))) := by
      rw [mul_assoc, h3]; exact_mod_cast h0
    exact (mul_nonneg_iff_of_pos_left (mul_self_pos.2 hD')).1 h4
  have hpsd : M.PosSemidef := by
    refine posSemidef_iff_dotProduct_mulVec.2 ⟨hH, fun y => ?_⟩
    rw [star_trivial]
    have hcl : IsClosed {y : Fin n → ℝ | 0 ≤ y ⬝ᵥ (M *ᵥ y)} :=
      isClosed_le continuous_const
        (Continuous.dotProduct continuous_id (Continuous.matrix_mulVec continuous_const continuous_id))
    exact (DenseRange.piMap fun _ => Rat.denseRange_cast).induction_on y hcl fun t => hrat t
  have hdetM : M.det = (L.det : ℝ) := by
    rw [hM]
    exact ((Int.castRingHom ℝ).map_det L).symm
  refine posDef_iff_dotProduct_mulVec.2 ⟨hH, fun x hx => ?_⟩
  refine lt_of_le_of_ne ((posSemidef_iff_dotProduct_mulVec.1 hpsd).2 x) fun h0 => hdet ?_
  have hk : M *ᵥ x = 0 := hpsd.dotProduct_mulVec_zero_iff.1 (by simpa using h0.symm)
  have : M.det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨x, hx, hk⟩
  rw [hdetM] at this
  exact_mod_cast this

end GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem exists_supports_int : ∀ (φ : InvFun ℤ) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X],
    IsPolFanOn id φ X → ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X), IsCone id φ γ →
      ∃ (d m : ℕ) (a : Fin m → X), 1 ≤ d ∧ Supports id φ d γ a := by
  intro φ X _ _ _ hφ r γ hγ
  classical
  have hstrict := hγ.strict
  unfold IsStrict at hstrict
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hstrict
  let b := Module.finBasis ℤ X
  let S : Fin (Module.finrank ℤ X) → Fin (Module.finrank ℤ X) → LinearMap.BilinForm ℤ X := fun i j =>
    (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord i) (b.coord j) + (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord j) (b.coord i)
  have hS : ∀ i j x y, S i j x y = b.repr x i * b.repr y j + b.repr x j * b.repr y i := by
    intro i j x y; simp [S]
  let L : Matrix (Fin (Module.finrank ℤ X)) (Fin (Module.finrank ℤ X)) ℤ := Matrix.of fun i j => ℓ (S i j)
  have hL : ∀ i j, L i j = ℓ (S i j) := fun _ _ => rfl
  have hexp : ∀ (β : LinearMap.BilinForm ℤ X) x y,
      β x y = ∑ i, ∑ j, b.repr x i * b.repr y j * β (b i) (b j) := by
    intro β x y
    conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hA : ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) →
      ∑ i, ∑ j, β (b i) (b j) * L i j = 2 * ℓ β := by
    intro β hβ
    have hsum : ∑ i, ∑ j, β (b i) (b j) • S i j = (2 : ℤ) • β := by
      refine LinearMap.ext₂ fun x y => ?_
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hS]
      have e : (2 : ℤ) * β x y = β x y + β y x := by rw [hβ y x]; ring
      rw [e, hexp β x y, hexp β y x, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have := congrArg ℓ hsum
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul] at this
    simpa only [hL] using this
  have hsym : L.IsSymm := Matrix.IsSymm.ext fun i j => by simp only [hL, S, add_comm]
  have hpos : ∀ ξ : Fin (Module.finrank ℤ X) → ℤ, ξ ≠ 0 → 0 < ξ ⬝ᵥ (L *ᵥ ξ) := by
    intro ξ hξ
    let l : X →ₗ[ℤ] ℤ := ∑ i, ξ i • b.coord i
    have hl : ∀ i, l (b i) = ξ i := by
      intro i
      simp [l, Finsupp.single_apply]
    have hsymm : ∀ y z, sqForm l y z = sqForm l z y := fun y z => by simp [mul_comm]
    have hmem : sqForm l ∈ balForms id X := mem_balForms_int.2 hsymm
    have hnn : ∀ y, 0 ≤ sqForm l y y := fun y => by simpa using mul_self_nonneg (l y)
    have hne : sqForm l ≠ 0 := by
      intro h0
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hξ
      have := LinearMap.congr_fun₂ h0 (b i) (b i)
      simp [hl] at this
      exact hi this
    have hφp := hφ.pos _ hmem hnn hne
    have hℓ := h2 _ hmem hnn
    have hℓpos : 0 < ℓ (sqForm l) := by
      have : (0 : ℝ) < ℓ (sqForm l) := lt_of_lt_of_le (mul_pos (by exact_mod_cast hN) hφp) hℓ
      exact_mod_cast this
    have h5 := hA (sqForm l) hsymm
    simp only [sqForm_apply, hl] at h5
    have e : ξ ⬝ᵥ (L *ᵥ ξ) = ∑ i, ∑ j, ξ i * ξ j * L i j := by
      simp only [dotProduct, mulVec, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e, h5]
    omega
  obtain ⟨D, m, a, hD, hspan, hsum⟩ := _root_.GlobalTheory.Poinc.SumSq.exists_smul_eq_sum_vecMulVec_span _ L (posDef_map_int_of_pos L hsym hpos)
  let x : Fin m → X := fun k => b.equivFun.symm (a k)
  have hx : ∀ k i, b.repr (x k) i = a k i := fun k i => by
    show b.equivFun (b.equivFun.symm (a k)) i = a k i
    rw [b.equivFun.apply_symm_apply]
  have hB : ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) →
      ∑ k, β (x k) (x k) = 2 * D * ℓ β := by
    intro β hβ
    have hsum' : ∀ i j, (D : ℤ) * L i j = ∑ k, a k i * a k j := by
      intro i j
      have := congrFun (congrFun hsum i) j
      simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
    calc ∑ k, β (x k) (x k) = ∑ k, ∑ i, ∑ j, a k i * a k j * β (b i) (b j) :=
          Finset.sum_congr rfl fun k _ => by rw [hexp β]; simp only [hx]
      _ = ∑ i, ∑ j, β (b i) (b j) * ((D : ℤ) * L i j) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hsum' i j, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = D * (2 * ℓ β) := by
          rw [← hA β hβ, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = 2 * D * ℓ β := by ring
  have hspanX : Submodule.span ℤ (Set.range x) = ⊤ := by
    have e : Set.range x = (b.equivFun.symm.toLinearMap : (Fin (Module.finrank ℤ X) → ℤ) →ₗ[ℤ] X) '' Set.range a :=
      Set.range_comp _ _
    rw [e, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  have hD0 : (0 : ℝ) < 2 * D := by have : (1 : ℝ) ≤ D := by exact_mod_cast hD
                                   linarith
  refine ⟨2 * D * N, m, x, Nat.one_le_iff_ne_zero.2 (by positivity), ⟨hspanX, ?_, ?_, ?_⟩⟩
  · intro β hβ hp
    rw [hB β (mem_balForms_int.1 hβ)]
    have := h2 β hβ hp
    push_cast
    nlinarith
  · intro j
    rw [hB (γ j) (mem_balForms_int.1 (hγ.mem j))]
    push_cast
    rw [h1 j]
    ring
  · intro β hβ hp he
    rw [hB β (mem_balForms_int.1 hβ)] at he
    push_cast at he
    refine h3 β hβ hp (mul_left_cancel₀ hD0.ne' ?_)
    linear_combination he

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullEqZeroOfChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KTrivOfLam

open GlobalTheory.CechPic

theorem cls_cube_pair {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB)
    (x y : T ⟶ A) (h : (cubeLB A ![x, y] L).IsLB) :
    cls _ h = pull (x * y).left (cls L hL) - pull x.left (cls L hL) - pull y.left (cls L hL) +
      pull (1 : T ⟶ A).left (cls L hL) := by
  refine (cls_linComb hL _ _ h).trans ?_
  rw [← Equiv.ulift.symm.sum_comp]
  have hu : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  have p₀ : psum A ![x, y] ∅ = 1 := rfl
  have p₁ : psum A ![x, y] {0} = x := mul_one x
  have p₂ : psum A ![x, y] {1} = y := mul_one y
  have p₃ : psum A ![x, y] {0, 1} = x * y := congrArg (x * ·) (mul_one y)
  rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [Equiv.ulift_symm_apply, p₀, p₁, p₂, p₃]
  rw [Finset.card_pair (by decide)]
  simp
  abel

theorem pull_eq_zero_of_chart {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (i : L.ι)
    (hf : ∀ y, f y ∈ L.U i) : pull f (cls L hL) = 0 :=
  (cls_eq_zero_iff (pull_isLB hL f)).2 (GlobalTheory.IsoExtend.exists_gen_of_chart hL f i hf)

theorem exists_chart {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (z : X) : ∃ i, z ∈ L.U i := by
  have : z ∈ (⊤ : X.Opens) := trivial
  rw [← hL.cover] at this
  exact TopologicalSpace.Opens.mem_iSup.1 this

theorem kTriv_of_lam_iso : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B →
    ∀ (P : LB (G2 B).left), P.IsLB →
    (∀ (T : Over S) (x : T ⟶ B), (∃ t : (P.pull (lift (snd B T ≫ x) (fst B T)).left).Gen, t.IsGen) → x = 1) →
    ∀ (L : LB B.left), L.IsLB → LBIso (abelian₂ B L) P → KTriv B L := by
  intro S B _ _ _ P hP H L hL hiso R _ t x hx
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall x.left (1 : Over.mk t ⟶ B).left fun p => ?_)
  obtain ⟨V, hpV, c₀, hc₀⟩ := hx p
  obtain ⟨i, hi⟩ := exists_chart hL (x.left p)
  obtain ⟨j, hj⟩ := exists_chart hL ((1 : Over.mk t ⟶ B).left p)
  let W : (Spec (CommRingCat.of R)).Opens := V ⊓ x.left ⁻¹ᵁ L.U i ⊓ (1 : Over.mk t ⟶ B).left ⁻¹ᵁ L.U j
  refine ⟨W, ⟨⟨hpV, hi⟩, hj⟩, ?_⟩
  let T₀ : Over S := Over.mk t
  let TW : Over S := Over.mk (W.ι ≫ t)
  let ιW : TW ⟶ T₀ := Over.homMk W.ι rfl
  suffices key : ιW ≫ x = 1 by
    have := congrArg (fun q => q.left) (key.trans (MonObj.comp_one ιW).symm)
    exact this
  refine H TW (ιW ≫ x) ?_
  let c := cls L hL
  have hLam : (abelian₂ B L).IsLB := LB.isLB_linComb hL _ _
  have hTD : (translDiff B L x).IsLB := LB.isLB_linComb hL _ _

  let O : (T₀ ⊗ B).left.Opens := (fst T₀ B).left ⁻¹ᵁ V
  have h₀ : pull O.ι (cls _ hTD) = 0 := (cls_eq_zero_iff (pull_isLB hTD _)).2 ⟨c₀, hc₀⟩
  let N : B ⊗ TW ⟶ T₀ ⊗ B := lift (snd B TW ≫ ιW) (fst B TW)
  have hN : Set.range N.left.base ⊆ Set.range O.ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    show (fst T₀ B).left (N.left z) ∈ V
    have k : N.left ≫ (fst T₀ B).left = (snd B TW).left ≫ W.ι := by rw [← Over.comp_left, lift_fst]; rfl
    rw [← Scheme.Hom.comp_apply, k, Scheme.Hom.comp_apply]
    exact ((snd B TW).left z).2.1.1
  have h₁ : pull N.left (cls _ hTD) = 0 := by
    rw [← IsOpenImmersion.lift_fac O.ι N.left hN, pull_comp, h₀, map_zero]
  have e₁ : cls _ hTD = pull (lift (fst T₀ B ≫ x) (snd T₀ B) ≫ μ[B]).left c - pull (snd T₀ B).left c := by
    refine (cls_linComb hL _ _ hTD).trans ?_
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_smul, neg_smul, c]
    exact (sub_eq_add_neg _ _).symm
  have e₂ : pull ((snd B TW ≫ ιW ≫ x) * fst B TW).left c = pull (fst B TW).left c := by
    have k₁ : N ≫ lift (fst T₀ B ≫ x) (snd T₀ B) ≫ μ[B] = (snd B TW ≫ ιW ≫ x) * fst B TW := by
      rw [← Category.assoc, comp_lift, ← Category.assoc, lift_fst, lift_snd, Category.assoc]; rfl
    have k₂ : N ≫ snd T₀ B = fst B TW := lift_snd _ _
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, k₁, k₂] at h₁
    exact sub_eq_zero.1 h₁
  have hcP : cls _ hP = cls _ hLam := ((cls_eq_iff hLam hP).2 hiso).symm
  have hC : cls _ hLam = pull (fst B B * snd B B).left c - pull (fst B B).left c - pull (snd B B).left c +
      pull (1 : G2 B ⟶ B).left c := cls_cube_pair hL (fst B B) (snd B B) hLam
  have e₃ : pull (snd B TW ≫ ιW ≫ x).left c = 0 := by
    rw [Over.comp_left, pull_comp, pull_eq_zero_of_chart hL (ιW ≫ x).left i ?_, map_zero]
    intro y
    exact y.2.1.2
  have e₄ : pull (1 : B ⊗ TW ⟶ B).left c = 0 := by
    have k : (1 : B ⊗ TW ⟶ B) = snd B TW ≫ ιW ≫ (1 : T₀ ⟶ B) := by rw [MonObj.comp_one, MonObj.comp_one]
    rw [k, Over.comp_left, pull_comp, pull_eq_zero_of_chart hL (ιW ≫ (1 : T₀ ⟶ B)).left j ?_, map_zero]
    intro y
    exact y.2.2
  refine (cls_eq_zero_iff (pull_isLB hP _)).1 ?_
  show pull _ (cls _ hP) = 0
  rw [hcP, hC, map_add (f := _), map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, ← Over.comp_left,
    ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd, MonObj.comp_one,
    e₂, e₃, e₄]
  abel

end GlobalTheory.KTrivOfLam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedEquationPullbackEtaleOverAffineSpace
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaleReducedEq

theorem isRadical_map_of_etale {Q C : Type} [CommRing Q] [CommRing C] [Algebra Q C]
    [Algebra.Etale Q C] (I : Ideal Q) (hI : I.IsRadical) :
    (I.map (algebraMap Q C)).IsRadical := by
  rw [Ideal.isRadical_iff_quotient_reduced] at hI ⊢
  have : _root_.IsReduced (TensorProduct Q (Q ⧸ I) C) :=
    GlobalTheory.isReduced_algebra_of_smooth_of_isReduced (Q ⧸ I) _
  have : _root_.IsReduced (TensorProduct Q C (Q ⧸ I)) :=
    isReduced_of_injective (Algebra.TensorProduct.comm Q C (Q ⧸ I)).toRingEquiv (RingEquiv.injective _)
  exact isReduced_of_injective (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C I).toRingEquiv
    (RingEquiv.injective _)

theorem etale_eval₂Hom_of_away {R A C ι : Type} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] (g : R) [IsLocalization.Away g A] (ψ : A →+* C) (N : ι → C)
    (hE : (MvPolynomial.eval₂Hom (ψ.comp (algebraMap R A)) N).Etale) :
    (MvPolynomial.eval₂Hom ψ N).Etale := by
  have : Algebra.Etale R A := Algebra.Etale.of_isLocalizationAway g
  letI : Algebra (MvPolynomial ι R) (MvPolynomial ι A) := MvPolynomial.algebraMvPolynomial
  have : Algebra.Etale (MvPolynomial ι R) (MvPolynomial ι A) :=
    Algebra.Etale.of_equiv (Algebra.IsPushout.equiv R (MvPolynomial ι R) A (MvPolynomial ι A))
  letI : Algebra (MvPolynomial ι A) C := (MvPolynomial.eval₂Hom ψ N).toAlgebra
  letI : Algebra (MvPolynomial ι R) C :=
    (MvPolynomial.eval₂Hom (ψ.comp (algebraMap R A)) N).toAlgebra
  have : IsScalarTower (MvPolynomial ι R) (MvPolynomial ι A) C :=
    IsScalarTower.of_algebraMap_eq fun p => by
      rw [MvPolynomial.algebraMap_def, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
        MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map]
  have : Algebra.Etale (MvPolynomial ι R) C := hE
  exact Algebra.Etale.of_restrictScalars (MvPolynomial ι R) (MvPolynomial ι A) C

theorem isRadical_span_of_away {R A C ι : Type} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] (g δ : R) [IsLocalization.Away g A] (ψ : A →+* C) (N : ι → C)
    (hE : (MvPolynomial.eval₂Hom (ψ.comp (algebraMap R A)) N).Etale)
    (hδ : (Ideal.span {algebraMap R A δ}).IsRadical) :
    (Ideal.span {ψ (algebraMap R A δ)}).IsRadical := by
  have he := etale_eval₂Hom_of_away g ψ N hE
  letI : Algebra (MvPolynomial ι A) C := (MvPolynomial.eval₂Hom ψ N).toAlgebra
  have : Algebra.Etale (MvPolynomial ι A) C := he
  have hI : (Ideal.map (MvPolynomial.C (σ := ι)) (Ideal.span {algebraMap R A δ})).IsRadical := by
    rw [Ideal.isRadical_iff_quotient_reduced] at hδ ⊢
    exact isReduced_of_injective
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := ι) (Ideal.span {algebraMap R A δ})).symm.toRingEquiv
      (RingEquiv.injective _)
  have h2 := isRadical_map_of_etale (C := C) _ hI
  rw [Ideal.map_map, Ideal.map_span, Set.image_singleton, RingHom.algebraMap_toAlgebra,
    RingHom.comp_apply, MvPolynomial.eval₂Hom_C] at h2
  exact h2

theorem resG_resG {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)) :
    resG X h' (resG X h a) = resG X (h'.trans h) a := by
  change (X.presheaf.map _ ≫ X.presheaf.map _).hom a = _
  rw [← Functor.map_comp]
  rfl

theorem isUnit_ger_iff_not_mem {X : Scheme.{0}} (Z : Closeds X) (U' : X.affineOpens)
    (δ : Γ(X, U'.1)) (h : (Scheme.IdealSheafData.vanishingIdeal Z).ideal U' = Ideal.span {δ})
    (x : X) (hx : x ∈ U'.1) : IsUnit (ger x hx δ) ↔ x ∉ Z := by
  obtain ⟨P, rfl⟩ : x ∈ Set.range U'.2.fromSpec := by rw [U'.2.range_fromSpec]; exact hx
  have hS : IsClosed (X := PrimeSpectrum Γ(X, U'.1)) (U'.2.fromSpec ⁻¹' (Z : Set X)) :=
    Z.isClosed.preimage U'.2.fromSpec.continuous
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal] at h
  rw [← Scheme.mem_basicOpen, ← Scheme.Hom.mem_preimage, U'.2.fromSpec_preimage_basicOpen]
  change δ ∉ P.asIdeal ↔ _
  rw [not_iff_not]
  have e := congrArg (P ∈ ·)
    (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure (U'.2.fromSpec ⁻¹' (Z : Set X)))
  rw [hS.closure_eq, h, PrimeSpectrum.zeroLocus_span] at e
  have e3 : (δ ∈ P.asIdeal) = (P ∈ PrimeSpectrum.zeroLocus {δ}) :=
    propext ((PrimeSpectrum.mem_zeroLocus (P : PrimeSpectrum Γ(X, U'.1)) {δ}).trans
      Set.singleton_subset_iff).symm
  exact (e3.trans e).to_iff

theorem mem_iff_not_isUnit_ger {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W)
    (P : Spec Γ(Y, W)) (hP : hW.fromSpec P ∈ W) (c : Γ(Y, W)) :
    c ∈ P.asIdeal ↔ ¬ IsUnit (ger (hW.fromSpec P) hP c) := by
  rw [← Scheme.mem_basicOpen, ← Scheme.Hom.mem_preimage, hW.fromSpec_preimage_basicOpen]
  change _ ↔ ¬ ¬ c ∈ P.asIdeal
  rw [not_not]

theorem reducedEq_pullback_etale : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian X] (q : Y ⟶ X) (ι : Type) [Finite ι] (Vo : X.Opens) (U U' : X.affineOpens) (hU' : U'.1 ≤ U.1) (W : Y.Opens), IsAffineOpen W → ∀ (hWU : W ≤ q ⁻¹ᵁ U.1) (N : ι → Γ(Y, W)), (MvPolynomial.eval₂Hom (q.appLE U.1 W hWU).hom N).Etale → ∀ (δ : Γ(X, U.1)), (Scheme.IdealSheafData.vanishingIdeal Vo.compl).ideal U' = Ideal.span {resG X hU' δ} → (∀ (z : Y) (hz : z ∈ W), q z ∈ U'.1 → (IsUnit (ger z hz ((q.appLE U.1 W hWU).hom δ)) ↔ q z ∈ Vo)) ∧ ∀ (W' : Y.Opens) (hW' : W' ≤ W), W' ≤ q ⁻¹ᵁ U'.1 → ∀ f : Γ(Y, W'), (∀ (z : Y) (hz : z ∈ W'), q z ∉ Vo → ger z hz f ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk z)) → ∀ (z : Y) (hz : z ∈ W'), ger z (hW' hz) ((q.appLE U.1 W hWU).hom δ) ∣ ger z hz f := by
  intro X Y _ q ι _ Vo U U' hU' W hW hWU N hEt δ hδ
  have part1 : ∀ (z : Y) (hz : z ∈ W), q z ∈ U'.1 →
      (IsUnit (ger z hz ((q.appLE U.1 W hWU).hom δ)) ↔ q z ∈ Vo) := by
    intro z hz hzU'
    rw [ger_appLE q hWU z hz δ, isUnit_map_iff, ← ger_resG hU' (q z) hzU' δ,
      isUnit_ger_iff_not_mem _ U' _ hδ]
    exact not_not
  refine ⟨part1, ?_⟩
  intro W' hW' hW'U' f hf z hz
  obtain ⟨g, hgU', hzg⟩ := U.2.exists_basicOpen_le (V := U'.1) ⟨q z, hW'U' hz⟩ (hWU (hW' hz))
  set g' := resG X hU' g
  set V := X.basicOpen g'
  have hV' : V = X.basicOpen g := by
    simp only [V, g', resG, Scheme.basicOpen_res]
    exact inf_eq_right.2 hgU'
  have hVU' : V ≤ U'.1 := X.basicOpen_le g'
  have hVU : V ≤ U.1 := hVU'.trans hU'
  letI : Algebra Γ(X, U.1) Γ(X, V) := (resG X hVU).toAlgebra
  haveI : IsLocalization.Away g Γ(X, V) := U.2.isLocalization_of_eq_basicOpen g (homOfLE hVU) hV'
  have hδV : (Ideal.span {algebraMap Γ(X, U.1) Γ(X, V) δ}).IsRadical := by
    have e := (Scheme.IdealSheafData.vanishingIdeal Vo.compl).map_ideal_basicOpen U' g'
    rw [hδ, Ideal.map_span, Set.image_singleton] at e
    have hrad : ((Scheme.IdealSheafData.vanishingIdeal Vo.compl).ideal
        (X.affineBasicOpen g')).IsRadical := by
      rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
      exact PrimeSpectrum.isRadical_vanishingIdeal _
    rw [← e] at hrad
    have e2 : algebraMap Γ(X, U.1) Γ(X, V) δ =
        (X.presheaf.map (homOfLE (X.basicOpen_le g')).op).hom (resG X hU' δ) :=
      (resG_resG hU' hVU' δ).symm
    rw [e2]
    exact hrad
  have hzV : q z ∈ V := hV' ▸ hzg
  obtain ⟨h, hhle, hzh⟩ := hW.exists_basicOpen_le (V := W' ⊓ q ⁻¹ᵁ V) ⟨z, hz, hzV⟩ (hW' hz)
  set W1 := Y.basicOpen h
  have hW1W : W1 ≤ W := Y.basicOpen_le h
  have hW1V : W1 ≤ q ⁻¹ᵁ V := hhle.trans inf_le_right
  have hW1W' : W1 ≤ W' := hhle.trans inf_le_left
  have hW1 : IsAffineOpen W1 := hW.basicOpen h
  let ψ : Γ(X, V) →+* Γ(Y, W1) := (q.appLE V W1 hW1V).hom
  have hcomp : MvPolynomial.eval₂Hom (ψ.comp (algebraMap Γ(X, U.1) Γ(X, V)))
      (fun i => resG Y hW1W (N i)) =
      (resG Y hW1W).comp (MvPolynomial.eval₂Hom (q.appLE U.1 W hWU).hom N) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, RingHom.algebraMap_toAlgebra, ψ, resG]
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
        Scheme.Hom.appLE_map]
    · intro i
      simp
  have hE : (MvPolynomial.eval₂Hom (ψ.comp (algebraMap Γ(X, U.1) Γ(X, V)))
      (fun i => resG Y hW1W (N i))).Etale := by
    rw [hcomp]
    have h2 : (resG Y hW1W).Etale := by
      letI : Algebra Γ(Y, W) Γ(Y, W1) := (resG Y hW1W).toAlgebra
      haveI : IsLocalization.Away h Γ(Y, W1) := hW.isLocalization_basicOpen h
      exact Algebra.Etale.of_isLocalizationAway h
    exact RingHom.Etale.stableUnderComposition _ _ hEt h2
  have rad := isRadical_span_of_away g δ ψ (fun i => resG Y hW1W (N i)) hE hδV
  have hd : ψ (algebraMap Γ(X, U.1) Γ(X, V) δ) = resG Y hW1W ((q.appLE U.1 W hWU).hom δ) := by
    have := congrArg (fun F => F (MvPolynomial.C δ)) hcomp
    simpa using this
  set d := ψ (algebraMap Γ(X, U.1) Γ(X, V) δ)
  set b := resG Y hW1W' f
  have hb : b ∈ (Ideal.span {d}).radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro P ⟨hdP, hP⟩
    let P' : Spec Γ(Y, W1) := ⟨P, hP⟩
    have hz' : hW1.fromSpec P' ∈ W1 := by
      rw [← SetLike.mem_coe, ← hW1.range_fromSpec]; exact Set.mem_range_self _
    have hdP' : d ∈ P'.asIdeal := hdP (Ideal.mem_span_singleton_self d)
    rw [mem_iff_not_isUnit_ger hW1 P' hz', hd, ger_resG] at hdP'
    have hq : q (hW1.fromSpec P') ∉ Vo := by
      rw [← part1 _ (hW1W hz') (hVU' (hW1V hz'))]
      exact hdP'
    have hm := hf _ (hW1W' hz') hq
    change b ∈ P'.asIdeal
    rw [mem_iff_not_isUnit_ger hW1 P' hz', ger_resG]
    exact (IsLocalRing.mem_maximalIdeal _).1 hm
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (rad hb)
  refine ⟨ger z hzh c, ?_⟩
  rw [← ger_resG hW1W' z hzh f, ← ger_resG hW1W z hzh, ← hd]
  change ger z hzh b = _
  rw [← hc, map_mul, mul_comm]

end GlobalTheory.EtaleReducedEq
end
end

