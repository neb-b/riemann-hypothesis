module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0410
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Formalism.MeanHeightDescent.AverageDegreeBounds.GlobalBoundRefinements
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeSlopeSqSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxSlopeExtendedLatticeGaloisLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0786

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultIffFinrankSimultaneousEigenSubmodule
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin

noncomputable section
namespace GlobalTheory.UPel.HT.LieLin.LieAlgebraMultiplication
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {k : Type} [Field k] (t : Sp k ⟶ S)

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : C →+* A) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem left_iff (c : k) (u v : epsPt t ⟶ G) :
    u.left = spMap (epsScale c) ≫ v.left ↔ u = smT t c v := by
  constructor
  · intro h; apply Over.OverMorphism.ext; rw [h, smT_left]; rfl
  · rintro rfl; rw [smT_left]; rfl

theorem tang_iff (v : epsPt t ⟶ G) :
    spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk t ⟶ G).left ↔ smT t 0 v = 1 := by
  have e0 : (epsMul (0 : k)) = (algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom := by
    refine RingHom.ext fun x => ?_
    ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  constructor
  · intro h
    apply Over.OverMorphism.ext
    have h1 : (1 : epsPt t ⟶ G) = (Over.homMk (spMap (algebraMap k (DualNumber k))) rfl : epsPt t ⟶ Over.mk t) ≫ 1 :=
      (MonObj.comp_one _).symm
    rw [smT_left, e0, ← spMap_comp', Category.assoc, h, h1]
    rfl
  · intro h
    have hw : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) ≫ t = t := by
      rw [← Category.assoc, spMap_comp']
      have : ((TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k))) = RingHom.id k := by
        refine RingHom.ext fun x => ?_; simp
      rw [this]
      simp [spMap]
    let s : Over.mk t ⟶ epsPt t := Over.homMk (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) hw
    have h2 := congrArg (fun φ => (s ≫ φ).left) h
    simp only [MonObj.comp_one] at h2
    rw [← h2]
    change _ = s.left ≫ (smT t 0 v).left
    rw [smT_left, ← Category.assoc]
    change _ = (spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (epsMul 0)) ≫ v.left
    rw [spMap_comp']
    congr 2
    refine RingHom.ext fun x => ?_
    simp [epsMul, s]

end GlobalTheory.UPel.HT.LieLin.LieAlgebraMultiplication

namespace GlobalTheory.UPel.HT.LieLin.LieAlgebraMultiplication
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {k : Type} [Field k] (t : Sp k ⟶ S)
variable {O : Type} [CommRing O] (act : OAct O G) (τ : O →+* k)

theorem lieEigen_tan {w : epsPt t ⟶ G} (h : IsLieEigen act t τ w) : smT t 0 w = 1 := (tang_iff t w).1 h.1

theorem mem_iff (x : TanM t G) :
    x ∈ eigSub (actR (x0 := t) (S := k) act) τ ↔ IsLieEigen act t τ (tv x) := by
  rw [mem_eigSub]
  refine ⟨fun h => ⟨(tang_iff t _).2 (tv_mem x), fun a => ?_⟩, fun h a => ?_⟩
  · rw [left_iff]
    have := congrArg tv (h a)
    rw [tv_actR, tv_smul] at this
    exact this
  · apply tanM_ext
    rw [tv_actR, tv_smul]
    exact (left_iff t _ _ _).1 (h.2 a)

theorem prod_eq {m : ℕ} (x : Fin m → TanM t G) (c : Fin m → k) :
    (List.ofFn (fun i => smT t (c i) (tv (x i)))).prod = tv (∑ i, c i • x i) := by
  rw [List.prod_ofFn]
  show _ = ((Additive.toMul (∑ i, c i • x i) : tanSub t G) : overAt t (DualNumber k) ⟶ G)
  rw [toMul_sum]
  change _ = (tanSub t G).subtype (∏ i, Additive.toMul (c i • x i))
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact (tv_smul (c i) (x i)).symm

end GlobalTheory.UPel.HT.LieLin.LieAlgebraMultiplication

namespace GlobalTheory.UPel.HT.LieLin
open ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj LieAlgebraMultiplication

theorem lieMult_iff_finrank : ∀ (O : Type) [CommRing O] (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G]
  (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G) (k : Type) [Field k] (t : Sp k ⟶ S) (τ : O →+* k) (m : ℕ),
    Module.Finite k (ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM t G) →
      (LieMult act t τ m ↔ Module.finrank k (eigSub (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR (x0 := t) (S := k) act) τ) = m) := by
  intro O _ S G _ _ act k _ t τ m hfin
  haveI := hfin
  constructor
  · rintro ⟨v, hv, huniq⟩
    let b : Fin m → eigSub (actR (x0 := t) (S := k) act) τ := fun i =>
      ⟨mkT (v i) (lieEigen_tan t act τ (hv i)), (mem_iff t act τ _).2 (hv i)⟩
    have key : ∀ (y : eigSub (actR (x0 := t) (S := k) act) τ) (e : Fin m → k),
        (y : TanM t G) = ∑ i, e i • (b i : TanM t G) →
        ∃ u : Fin m → (epsPt t ⟶ G), (∀ i, (u i).left = spMap (epsScale (e i)) ≫ (v i).left) ∧
          tv (y : TanM t G) = (List.ofFn u).prod := by
      intro y e he
      refine ⟨fun i => smT t (e i) (tv (b i : TanM t G)), fun i => (left_iff t _ _ _).2 rfl, ?_⟩
      rw [prod_eq t (fun i => (b i : TanM t G)) e, he]
    have hb : Function.Bijective (Fintype.linearCombination k b) := by
      constructor
      · intro c c' hcc
        rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply] at hcc
        let y : eigSub (actR (x0 := t) (S := k) act) τ := ∑ i, c i • b i
        have hy : IsLieEigen act t τ (tv (y : TanM t G)) := (mem_iff t act τ _).1 y.2
        obtain ⟨d, _, hd⟩ := huniq _ hy
        have h1 := hd c (key y c (by simp [y, Submodule.coe_sum]))
        have h2 := hd c' (key y c' (by rw [show y = ∑ i, c' i • b i from hcc]; simp [Submodule.coe_sum]))
        exact h1.trans h2.symm
      · intro y
        have hy : IsLieEigen act t τ (tv (y : TanM t G)) := (mem_iff t act τ _).1 y.2
        obtain ⟨c, ⟨u, hu, hw⟩, _⟩ := huniq _ hy
        refine ⟨c, ?_⟩
        have hu' : u = fun i => smT t (c i) (tv (b i : TanM t G)) :=
          funext fun i => (left_iff t _ _ _).1 (hu i)
        rw [hu', prod_eq] at hw
        rw [Fintype.linearCombination_apply]
        apply Subtype.ext
        apply tanM_ext
        rw [hw]
        simp [Submodule.coe_sum]
    rw [← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_fin_fun]
  · intro h
    let B := Module.finBasisOfFinrankEq k (eigSub (actR (x0 := t) (S := k) act) τ) h
    refine ⟨fun i => tv (B i : TanM t G), fun i => (mem_iff t act τ _).1 (B i).2, fun w hw => ?_⟩
    have h0 := lieEigen_tan t act τ hw
    let y : eigSub (actR (x0 := t) (S := k) act) τ := ⟨mkT w h0, (mem_iff t act τ _).2 hw⟩
    refine ⟨B.equivFun y, ⟨fun i => smT t (B.equivFun y i) (tv (B i : TanM t G)),
      fun i => (left_iff t _ _ _).2 rfl, ?_⟩, ?_⟩
    · rw [prod_eq]
      show tv (y : TanM t G) = _
      congr 1
      have hs : ((∑ i, B.repr y i • B i : eigSub (actR (x0 := t) (S := k) act) τ) : TanM t G) = y :=
        congrArg Subtype.val (B.sum_repr y)
      refine hs.symm.trans ?_
      rw [Submodule.coe_sum]
      rfl
    · rintro c ⟨u, hu, hwu⟩
      have hu' : u = fun i => smT t (c i) (tv (B i : TanM t G)) :=
        funext fun i => (left_iff t _ _ _).1 (hu i)
      rw [hu', prod_eq] at hwu
      have hy : y = ∑ i, c i • B i := by
        apply Subtype.ext
        apply tanM_ext
        show w = _
        rw [hwu]
        simp [Submodule.coe_sum]
      rw [hy, ← B.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

end GlobalTheory.UPel.HT.LieLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxSlopeSqFieldExtensionLeComparableNorms
section
open NumberField GlobalTheory.AllWt

noncomputable section

namespace GlobalTheory.SlopeMaxExt

open Module Matrix

section One

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] {N : (K →+* ℂ) → V → ℝ} {L : Submodule (𝓞 K) V}


omit [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem fg_of_le (hL : L.FG) {M : Submodule (𝓞 K) V} (hM : M ≤ L) : M.FG := by
  haveI : IsNoetherian (𝓞 K) L := isNoetherian_of_fg_of_noetherian L hL
  exact isNoetherian_submodule.1 inferInstance M hM

theorem exists_slope_eq (hN : HasGram N) (hL : L.FG) (h0 : L ≠ ⊥) :
    ∃ M : Submodule (𝓞 K) V, M ≤ L ∧ M ≠ ⊥ ∧ slope_sq N M = slopeMax_sq N L := by
  letI : StarRing K := starRingOfComm
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hN
  obtain ⟨hLat, -, -⟩ := Formalism.HN.plLat K V _ b X (fun v => (hG v).1) L hL
  obtain ⟨-, -, ⟨M, hM, hM0, hMs⟩, -, -⟩ := Formalism.HN.muChar _ _ _ _ L hLat h0
  refine ⟨M, hM.1, hM0, ?_⟩
  rw [slope_sq_eq hG (fg_of_le hL hM.1), (slopeMax_slopeMin_eq hG hL h0).1]
  simp only [Formalism.HN.muDef, Formalism.HN.muMaxDef, hMs]

theorem slope_le_slopeMax (hN : HasGram N) (hL : L.FG) {M : Submodule (𝓞 K) V} (hM : M ≤ L) (hM0 : M ≠ ⊥) :
    slope_sq N M ≤ slopeMax_sq N L := by
  letI : StarRing K := starRingOfComm
  have h0 : L ≠ ⊥ := fun h => hM0 (eq_bot_iff.2 (h ▸ hM))
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hN
  have l1 := (Formalism.HN.plLat K V _ b X (fun v => (hG v).1) M (fg_of_le hL hM)).1
  have l2 := (Formalism.HN.plLat K V _ b X (fun v => (hG v).1) L hL).1
  have m1 := Formalism.HN.muChar _ _ _ _ _ l1 hM0
  have m2 := (Formalism.HN.muChar _ _ _ _ _ l2 h0).1
  have key := (m1.1 _).2 fun P hP => (m2 _).1 le_rfl P (hP.trans hM)
  have := m1.2.2.2.2
  rw [slope_sq_eq hG (fg_of_le hL hM), (slopeMax_slopeMin_eq hG hL h0).1]
  unfold Formalism.HN.muDef Formalism.HN.muMaxDef
  linarith

end One

section Two

variable {K K' V V' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K' V'] [Module (𝓞 K') V'] [IsScalarTower (𝓞 K') K' V']
  (ι : V →ₛₗ[algebraMap K K'] V')


omit [NumberField K] [NumberField K'] in
theorem map_mem_of_mem_span {s : Set V} {P : Submodule (𝓞 K') V'} (hs : ∀ x ∈ s, ι x ∈ P) {x : V}
    (hx : x ∈ Submodule.span (𝓞 K) s) : ι x ∈ P := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => rw [map_zero]; exact P.zero_mem
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact P.add_mem hx hy
  | smul a x _ hx =>
    have : ι (a • x) = algebraMap (𝓞 K) (𝓞 K') a • ι x := by
      rw [← algebraMap_smul K a, map_smulₛₗ, ← algebraMap_smul K' (algebraMap (𝓞 K) (𝓞 K') a)]
      rfl
    rw [this]; exact P.smul_mem _ hx


omit [NumberField K] [NumberField K'] in
theorem fg_span_image {L : Submodule (𝓞 K) V} (hL : L.FG) :
    (Submodule.span (𝓞 K') (ι '' (L : Set V))).FG := by
  obtain ⟨s, rfl⟩ := hL
  refine Submodule.fg_def.2 ⟨ι '' s, s.finite_toSet.image _, le_antisymm ?_ ?_⟩
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact map_mem_of_mem_span ι (fun y hy => Submodule.subset_span (Set.mem_image_of_mem _ hy)) hx


omit [NumberField K] [NumberField K'] [IsScalarTower (𝓞 K) K V] [IsScalarTower (𝓞 K') K' V'] in
theorem span_image_ne_bot
    (hli : ∀ (n : ℕ) (b : Fin n → V), LinearIndependent K b → LinearIndependent K' (fun k => ι (b k)))
    {L : Submodule (𝓞 K) V} (h0 : L ≠ ⊥) : Submodule.span (𝓞 K') (ι '' (L : Set V)) ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have h1 := (hli 1 (fun _ => x) (linearIndependent_unique_iff.2 hx0)).ne_zero 0
  intro h
  exact h1 (Submodule.span_eq_bot.1 h _ ⟨x, hx, rfl⟩)

end Two

theorem exists_frame {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] {n : ℕ}
    (b : Basis (Fin n) K V) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : ∀ v, IsUnit (X v).det)
    (τ : K →+* ℂ) {t : ℝ} (ht : 0 < t) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, IsUnit Y.det ∧ ∀ x, Formalism.HermitianLatticesTheory.cnorm (Y⁻¹ *ᵥ fun i => τ (b.repr x i)) =
      t * Formalism.HermitianLatticesTheory.normAt b X (InfinitePlace.mk τ) x := by
  have hs : ∀ u : Fin n → ℂ, Formalism.HermitianLatticesTheory.cnorm ((t : ℂ) • u) = t * Formalism.HermitianLatticesTheory.cnorm u := fun u => by
    unfold Formalism.HermitianLatticesTheory.cnorm
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ht.le]
  have key : ∀ Z : Matrix (Fin n) (Fin n) ℂ, IsUnit Z.det →
      (∀ x, Formalism.HermitianLatticesTheory.cnorm (Z *ᵥ fun i => τ (b.repr x i)) = Formalism.HermitianLatticesTheory.normAt b X (InfinitePlace.mk τ) x) →
      ∃ Y : Matrix (Fin n) (Fin n) ℂ, IsUnit Y.det ∧ ∀ x, Formalism.HermitianLatticesTheory.cnorm (Y⁻¹ *ᵥ fun i => τ (b.repr x i)) =
        t * Formalism.HermitianLatticesTheory.normAt b X (InfinitePlace.mk τ) x := fun Z hZ h => by
    have hu : IsUnit ((t : ℂ) • Z).det := by
      rw [det_smul]
      exact (IsUnit.pow _ (Ne.isUnit (by exact_mod_cast ht.ne'))).mul hZ
    refine ⟨((t : ℂ) • Z)⁻¹, isUnit_nonsing_inv_det _ hu, fun x => ?_⟩
    rw [nonsing_inv_nonsing_inv _ hu, smul_mulVec, hs, h]
  have hi := isUnit_nonsing_inv_det _ (hX (InfinitePlace.mk τ))
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · refine key _ hi fun x => ?_
    unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
    rw [h]
  · refine key ((starRingEnd ℂ).mapMatrix (X (InfinitePlace.mk τ))⁻¹) ?_ fun x => ?_
    · rw [← RingHom.map_det]; exact hi.map _
    · unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt Formalism.HermitianLatticesTheory.cnorm
      rw [h]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Complex.norm_conj]
      simp [Matrix.mulVec, dotProduct]

def coordExt {K V : Type} (F : Type) [Field K] [Field F] [Algebra K F] [AddCommGroup V] [Module K V] {n : ℕ}
    (b : Basis (Fin n) K V) : V →ₛₗ[algebraMap K F] (Fin n → F) where
  toFun x i := algebraMap K F (b.repr x i)
  map_add' x y := by funext i; simp
  map_smul' a x := by funext i; simp

theorem coordExt_li {K V : Type} (F : Type) [Field K] [Field F] [Algebra K F] [AddCommGroup V] [Module K V] {n : ℕ}
    (b : Basis (Fin n) K V) (m : ℕ) (e : Fin m → V) (he : LinearIndependent K e) :
    LinearIndependent F fun k => coordExt F b (e k) :=
  (linearIndependent_algebraMap_comp_iff (S := F) (v := fun k => b.equivFun (e k))).2
    (he.map' b.equivFun.toLinearMap b.equivFun.ker)

theorem slopeMax_sq_span_le : ∀ (K K' V V' : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field K'] [NumberField K'] [Algebra K K'] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K' V'] [Module (𝓞 K') V'] [IsScalarTower (𝓞 K') K' V'] (N : (K →+* ℂ) → V → ℝ) (N' : (K' →+* ℂ) → V' → ℝ) (ι : V →ₛₗ[algebraMap K K'] V') (L : Submodule (𝓞 K) V) (c : (K' →+* ℂ) → ℝ) (B : ℝ), HasGram N → HasGram N' → (∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x) → (∀ (n : ℕ) (b : Fin n → V), LinearIndependent K b → LinearIndependent K' (fun k => ι (b k))) → L.FG → L ≠ ⊥ → (∀ σ', 0 < c σ' ∧ |Real.log (c σ')| ≤ B) → (∀ σ' x, N' σ' (ι x) = c σ' * N (σ'.comp (algebraMap K K')) x) → slopeMax_sq N' (Submodule.span (𝓞 K') (ι '' (L : Set V))) ≤ slopeMax_sq N L + 2 * B := by
  intro K K' V V' _ _ _ _ _ _ _ _ _ _ _ _ _ _ N N' ι L c B hN hN' hc hli hL h0 hcB hι
  haveI : IsTotallyComplex K' := isTotallyComplex_of_algebra K K'
  haveI : Module.Finite K K' := Module.Finite.of_restrictScalars_finite ℚ K K'
  haveI : IsAlgClosure K (AlgebraicClosure K') := ⟨inferInstance, Algebra.IsAlgebraic.trans K K' _⟩
  let F : Type := IntermediateField.normalClosure K K' (AlgebraicClosure K')
  haveI : IsGalois K F := inferInstance
  haveI : NumberField F := NumberField.of_module_finite K F
  have hL' := fg_span_image ι hL
  obtain ⟨M, hM, hM0, hMs⟩ := exists_slope_eq hN' hL' (span_image_ne_bot ι hli h0)
  have hMfg := fg_of_le hL' hM
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hN'
  letI : StarRing K' := starRingOfComm
  let N₁ : (K' →+* ℂ) → V' → ℝ := fun σ x => N' (InfinitePlace.mk σ).embedding x
  have hG₁ : IsGram b X N₁ := fun v => ⟨(hG v).1, fun x => by
    simp only [N₁, InfinitePlace.mk_embedding]; exact (hG v).2 x⟩
  have hc₁ : ∀ σ x, N₁ ((starRingEnd ℂ).comp σ) x = N₁ σ x := fun σ x => by
    have : InfinitePlace.mk ((starRingEnd ℂ).comp σ) = InfinitePlace.mk σ := InfinitePlace.mk_conjugate_eq σ
    simp only [N₁, this]
  choose Y hY hYn using fun τ : K' →+* ℂ => exists_frame b X (fun v => (hG v).1) τ
    (inv_pos.2 (hcB (InfinitePlace.mk τ).embedding).1)
  let N₂ : (F →+* ℂ) → (Fin n → F) → ℝ := fun σ y =>
    Formalism.HermitianLatticesTheory.cnorm ((Y (σ.comp (algebraMap K' F)))⁻¹ *ᵥ fun i => σ (y i))
  have hG₂ : IsGram (Pi.basisFun F (Fin n)) (fun u => Y (u.embedding.comp (algebraMap K' F))) N₂ :=
    fun u => ⟨hY _, fun y => by
      unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
      simp only [N₂, Pi.basisFun_repr]⟩
  have hN₂ : HasGram N₂ := ⟨⟨n, ⟨(_, _), hG₂⟩⟩⟩
  let φ := coordExt F b
  have hφ : ∀ (σ : F →+* ℂ) x, N₂ σ (φ x) = (c (InfinitePlace.mk (σ.comp (algebraMap K' F))).embedding)⁻¹ *
      N₁ (σ.comp (algebraMap K' F)) x := fun σ x => (hYn _ x).trans (by rw [(hG _).2])
  let ψ : V →ₛₗ[algebraMap K F] (Fin n → F) :=
    { toFun := fun x => φ (ι x)
      map_add' := fun x y => by simp
      map_smul' := fun a x => by
        rw [map_smulₛₗ, map_smulₛₗ, ← IsScalarTower.algebraMap_apply] }
  have h1 := GlobalTheory.SlopeExt.slope_sq_sub_le_slope_sq_span K' F V' (Fin n → F) N₁ N₂ φ M B ⟨⟨n, ⟨(b, X), hG₁⟩⟩⟩ hN₂ hc₁
    (coordExt_li F b) hMfg hM0 (fun σ x => by
      rw [hφ]
      refine mul_le_mul_of_nonneg_right ?_ ?_
      · obtain ⟨h1, h2⟩ := hcB (InfinitePlace.mk (σ.comp (algebraMap K' F))).embedding
        rw [← Real.exp_log h1, ← Real.exp_neg]
        exact Real.exp_le_exp.2 ((neg_le_abs _).trans h2)
      · show 0 ≤ N' _ x
        rw [← (hG _).2]; exact Real.sqrt_nonneg _)
  have h2 := _root_.GlobalTheory.SlopeGal.slopeMax_sq_span_le K F V (Fin n → F) N N₂ ψ L hN hN₂ hc
    (fun m e he => coordExt_li F b m _ (hli m e he)) hL h0 (fun σ x => by
      show N₂ σ (φ (ι x)) = _
      rw [hφ]
      show _ * N' _ (ι x) = _
      rw [hι, inv_mul_cancel_left₀ (hcB _).1.ne', IsScalarTower.algebraMap_eq K K' F, ← RingHom.comp_assoc]
      rcases InfinitePlace.embedding_mk_eq (σ.comp (algebraMap K' F)) with h | h
      · rw [h]
      · rw [h]; exact hc ((σ.comp (algebraMap K' F)).comp (algebraMap K K')) x)
  have h3 : slope_sq N₂ (Submodule.span (𝓞 F) (φ '' (M : Set V'))) ≤
      slopeMax_sq N₂ (Submodule.span (𝓞 F) (ψ '' (L : Set V))) := by
    refine slope_le_slopeMax hN₂ (fg_span_image ψ hL) (Submodule.span_le.2 ?_)
      (span_image_ne_bot φ (coordExt_li F b) hM0)
    rintro _ ⟨x, hx, rfl⟩
    refine map_mem_of_mem_span φ ?_ (hM hx)
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨y, hy, rfl⟩
  have h4 : slope_sq N₁ M = slope_sq N' M := by rw [slope_sq_eq hG₁ hMfg, slope_sq_eq hG hMfg]
  linarith

end GlobalTheory.SlopeMaxExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemRangeNorm
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp.NormIndex

open Neutral.B1

theorem mul_eq_one_of_card_two {G : Type} [Group G] [Finite G] (h : Nat.card G = 2) {a b : G}
    (ha : a ≠ 1) (hb : b ≠ 1) : a * b = 1 := by
  classical
  have hab : b = a := by
    by_contra hne
    haveI := Fintype.ofFinite G
    have : ({1, a, b} : Finset G).card ≤ Nat.card G := by
      rw [Nat.card_eq_fintype_card]; exact Finset.card_le_univ _
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm ha, Ne.symm hb]),
      Finset.card_pair (Ne.symm hne), h] at this
    omega
  subst hab
  have := pow_card_eq_one' (G := G) (x := b)
  rw [h, pow_two] at this
  exact this

theorem mul_mem_range_norm (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (x y : Fˣ)
    (hx : x ∉ (Units.map (Algebra.norm F : E →* F)).range)
    (hy : y ∉ (Units.map (Algebra.norm F : E →* F)).range) :
    x * y ∈ (Units.map (Algebra.norm F : E →* F)).range := by
  obtain ⟨b, -, -⟩ := hE.basis
  have h2 : Module.finrank F E = 2 := by rw [Module.finrank_eq_card_basis b]; simp
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  haveI : IsGalois F E := Algebra.IsQuadraticExtension.isGalois F E
  let φ : E →ₐ[F] AlgebraicClosure F := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let L : IntermediateField F (AlgebraicClosure F) := φ.fieldRange
  let e : E ≃ₐ[F] L := AlgEquiv.ofInjectiveField φ
  haveI : FiniteDimensional F L := LinearEquiv.finiteDimensional e.toLinearEquiv
  haveI : IsGalois F L := IsGalois.of_algEquiv e
  have hL2 : Module.finrank F L = 2 := e.toLinearEquiv.finrank_eq.symm.trans h2
  have hcard : Nat.card (L ≃ₐ[F] L) = 2 := by
    rw [← hL2, ← IsGalois.card_aut_eq_finrank]
  have hab : IsFiniteAbelian F L :=
    { finiteDimensional := inferInstance
      isGalois := inferInstance
      comm := fun a b' => by
        haveI : Fact (Nat.card (L ≃ₐ[F] L)).Prime := ⟨hcard ▸ Nat.prime_two⟩
        haveI := isCyclic_of_prime_card (α := L ≃ₐ[F] L) (p := Nat.card (L ≃ₐ[F] L)) rfl
        exact IsCyclic.commGroup.mul_comm a b' }
  obtain ⟨Art, hArt⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.artin_reciprocity_char_zero F
  obtain ⟨-, hker⟩ := hArt.2.2.2.2 L hab
  have hN : (Units.map (Algebra.norm F : E →* F)).range = normGroup F L := by
    ext z
    simp only [normGroup, MonoidHom.mem_range]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨Units.map (e : E →* L) w, Units.ext (Algebra.norm_eq_of_algEquiv e (w : E))⟩
    · rintro ⟨w, rfl⟩
      exact ⟨Units.map (e.symm : L →* E) w, Units.ext (Algebra.norm_eq_of_algEquiv e.symm (w : L))⟩
  rw [hN, ← hker] at hx hy ⊢
  rw [MonoidHom.mem_ker] at hx hy ⊢
  rw [map_mul]
  haveI : Finite (L ≃ₐ[F] L) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact mul_eq_one_of_card_two hcard hx hy

end GlobalTheory.KSp.NormIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentDoubleCosetCellFiniteDisjointIUnionStatement
section
open Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentDoubleCosetCell_finite_disjoint_iUnion : ∀ {F : Type} [NormedField F] {n : ℕ} (B B' : Subgroup (GL (Fin n) F)), IsCompact (B : Set (GL (Fin n) F)) → IsOpen (B' : Set (GL (Fin n) F)) → B' ≤ B → ∀ h₀ : GL (Fin n) F, ∃ s : Finset (GL (Fin n) F), (∀ x ∈ s, x ∈ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin n) F))) ∧ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin n) F)) = (⋃ x ∈ s, GlobalTheory.JSW.Cut.cell x (B' : Set (GL (Fin n) F))) ∧ (s : Set (GL (Fin n) F)).PairwiseDisjoint fun x => GlobalTheory.JSW.Cut.cell x (B' : Set (GL (Fin n) F)) := by
  first | (exact @GlobalTheory.JSW.Cut.cell_finite_disjoint_union') | (exact GlobalTheory.JSW.Cut.cell_finite_disjoint_union') | (intros; apply GlobalTheory.JSW.Cut.cell_finite_disjoint_union'  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerIndicatorCutMulOpenSubgroupStatement
section
open Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittakerIndicatorCut_mul_open_subgroup : ∀ {F : Type} [NormedField F] (ψ : AddChar F ℂ) {n : ℕ} (U : Subgroup (GL (Fin n) F)), IsOpen (U : Set (GL (Fin n) F)) → ∀ X A : Set (GL (Fin n) F), (∀ x ∈ X, ∀ u ∈ U, x * u ∈ X) → GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin n) F)) X A → ∃ U₁ : Subgroup (GL (Fin n) F), U₁ ≤ U ∧ IsOpen (U₁ : Set (GL (Fin n) F)) ∧ GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin n) F)) X {g | ∃ a ∈ A, ∃ u ∈ U₁, g = a * u} := by
  first | exact @GlobalTheory.JSW.Cut.cuts_mul_open_subgroup | exact GlobalTheory.JSW.Cut.cuts_mul_open_subgroup | (intros; apply GlobalTheory.JSW.Cut.cuts_mul_open_subgroup <;> assumption)
end

