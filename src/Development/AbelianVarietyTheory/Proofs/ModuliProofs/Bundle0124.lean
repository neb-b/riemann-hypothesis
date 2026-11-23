module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GoodPtOfIrredOfMulPull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TwoMulEqOfIsTypeFn
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueThetaCharAtPoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinrankSectionsPullbackMulByNTwists

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsogenyPullbackHeckeModuliObject
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

noncomputable section

namespace GlobalTheory.HkFam

theorem lbIso_pow_pull_square {B B' G G' : Scheme.{0}} {β : B' ⟶ B} {π : G' ⟶ G} {φ : B ⟶ G} {φ' : B' ⟶ G'}
    (h : φ' ≫ π = β ≫ φ) {P : LB G} {P' : LB G'} {M : LB B} {M' : LB B'} (hP : P.IsLB) (hP' : P'.IsLB)
    (hM : M.IsLB) (hM' : M'.IsLB) (eP : LBIso P' (P.pull π)) (eM : LBIso M' (M.pull β)) {n : ℕ}
    (hI : LBIso (lbPow M n) (P.pull φ)) : LBIso (lbPow M' n) (P'.pull φ') := by
  obtain ⟨w, hw⟩ := eP
  have e₁ : LBIso (P'.pull φ') (P.pull (φ' ≫ π)) :=
    iso_linComb ((isGen_iff w).1 hw) (fun _ : PUnit => φ') (fun _ => 1)
  have e₂ : LBIso (P.pull (φ' ≫ π)) ((P.pull φ).pull β) :=
    LBIso.chartPull (chartPullSame P _ _ _ β fun _ => h) (chartPullPull _ β) (lbIso_refl (pull_isLB hP φ))
  have e₃ := LBIso.trans (pull_isLB hP' _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e₁ e₂
  refine LBIso.trans (isLB_lbPow hM' _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hP' _) ?_ e₃.symm
  exact LBIso.trans (isLB_lbPow hM' _) (isLB_lbPow (pull_isLB hM _) _) (pull_isLB (pull_isLB hP _) _)
    (lbIso_lbPow eM _) (LBIso.chartPull (chartPullPowPull M β _) (chartPullPull _ β) hI)

theorem KerSet.pull {S S' : Scheme.{0}} {f : S' ⟶ S} {B G : Over S} {B' G' : Over S'} [GrpObj G] [GrpObj G']
    {β : B'.left ⟶ B.left} {π : G'.left ⟶ G.left} (hβ : β ≫ B.hom = B'.hom ≫ f) (hπ : IsGrpPullback G' G f π)
    {ψ : B ⟶ G} {ψ' : B' ⟶ G'} (h : ψ'.left ≫ π = β ≫ ψ.left) {K : Set B.left} (hK : KerSet ψ K) :
    KerSet ψ' (β ⁻¹' K) := by
  intro k _ _ x z
  have e : pushHom hπ (Over.mk x) (z ≫ ψ') = pushPt hβ z ≫ ψ := Over.OverMorphism.ext (by
    show (z.left ≫ ψ'.left) ≫ π = (z.left ≫ β) ≫ ψ.left
    rw [Category.assoc, Category.assoc, h])
  have e₁ : z ≫ ψ' = 1 ↔ pushPt hβ z ≫ ψ = 1 := by
    rw [← e]
    refine ⟨fun q => by rw [q, map_one], fun q => PureType.eq_of_comp_eq hπ.1 ?_⟩
    exact congrArg (fun u => u.left) (q.trans (map_one (pushHom hπ (Over.mk x))).symm)
  refine e₁.trans ((hK k (x ≫ f) (pushPt hβ z)).trans ?_)
  show Set.range (z.left ≫ β) ⊆ K ↔ _
  simp only [Set.range_subset_iff, Set.mem_preimage, Scheme.Hom.comp_apply]

theorem isog_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (p : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp (KA l)) (s' : S' ⟶ Sp (KA l)) (f : S' ⟶ S) (o₁ o₂ : Ob D l s) (o₁' o₂' : Ob D l s') (n₁ : ObjMap o₁' o₁ f) (n₂ : ObjMap o₂' o₂ f) (ψ : o₁.t.G ⟶ o₂.t.G), (∃! ψ' : o₁'.t.G ⟶ o₂'.t.G, ψ'.left ≫ n₂.toSABMap.φ = n₁.toSABMap.φ ≫ ψ.left) ∧ ∀ ψ' : o₁'.t.G ⟶ o₂'.t.G, ψ'.left ≫ n₂.toSABMap.φ = n₁.toSABMap.φ ≫ ψ.left → (IsIsog o₁ o₂ p ψ → IsIsog o₁' o₂' p ψ') ∧ ∀ K, IsMonHom ψ → KerSet ψ K → KerSet ψ' (n₁.toSABMap.φ ⁻¹' K) := by
  intro E _ _ _ H D l p S S' s s' f o₁ o₂ o₁' o₂' n₁ n₂ ψ
  have c₁ := n₁.toSABMap.cart
  have c₂ := n₂.toSABMap.cart
  refine ⟨?_, fun ψ' h => ⟨?_, fun K _ hK => KerSet.pull c₁.1.w c₂ h hK⟩⟩
  · obtain ⟨ψ', h⟩ := PureType.exists_hom_over c₁.1.w c₂.1 ψ
    exact ⟨ψ', h, fun χ hχ => PureType.eq_of_comp_eq c₂.1 (hχ.trans h.symm)⟩
  rintro ⟨⟨h₁, h₂, h₃, h₄, h₅, h₆⟩, h₇⟩
  have sq : IsPullback n₁.toSABMap.φ ψ'.left ψ.left n₂.toSABMap.φ :=
    IsPullback.of_bot (by rw [Over.w, Over.w]; exact c₁.1) h.symm c₂.1
  have lev : ∀ {u : 𝟙_ (Over S) ⟶ o₁.t.G} {v : 𝟙_ (Over S) ⟶ o₂.t.G} {u' : 𝟙_ (Over S') ⟶ o₁'.t.G}
      {v' : 𝟙_ (Over S') ⟶ o₂'.t.G}, u'.left ≫ n₁.toSABMap.φ = f ≫ u.left → v'.left ≫ n₂.toSABMap.φ = f ≫ v.left →
      u ≫ ψ = v → u' ≫ ψ' = v' := fun {u v u' v'} hu hv e => PureType.eq_of_comp_eq c₂.1 (by
    refine Eq.trans ?_ hv.symm
    rw [← e, Over.comp_left, Over.comp_left, Category.assoc]
    exact (congrArg (u'.left ≫ ·) h).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ ψ.left) hu).trans (Category.assoc _ _ _))))
  refine ⟨⟨PureType.isMonHom_over c₁ c₂ h, MorphismProperty.of_isPullback (P := @IsFinite) sq h₂,
    MorphismProperty.of_isPullback (P := @Etale) sq h₃, MorphismProperty.of_isPullback (P := @Surjective) sq h₄,
    fun a => PureType.eq_of_comp_eq c₂.1 ?_, ?_⟩, fun p' hp a =>
    ⟨lev (n₁.eta _) (n₂.eta _) (h₇ p' hp a).1, lev (n₁.etaA _) (n₂.etaA _) (h₇ p' hp a).2⟩⟩
  · have e : (o₁.t.act.act a).left ≫ ψ.left = ψ.left ≫ (o₂.t.act.act a).left := congrArg (fun u => u.left) (h₅ a)
    have h' : ψ'.left ≫ n₂.cm.F = n₁.cm.F ≫ ψ.left := h
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, n₂.act, h', reassoc_of% h',
      reassoc_of% (n₁.act a), e]
  · exact lbIso_pow_pull_square h o₂.t.PP.isLB o₂'.t.PP.isLB o₁.t.PP.isLB o₁'.t.PP.isLB
      (n₂.lin.imp fun _ q => q.1) (n₁.lin.imp fun _ q => q.1) h₆

end GlobalTheory.HkFam

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsKsMatrixOf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KSField

section Linear
variable {K : Type} [Field K] {Y : Scheme.{0}} {I : Type} {U : I → Y.Opens} {g : ℕ}

theorem isCob_const_mul (q : Y ⟶ Sp K) (a : K) {c : C1 U} (h : IsCob U c) :
    IsCob U (fun i j => constFn q (U i ⊓ U j) a * c i j) := by
  have := isCob_lc q (g := 1) (fun _ => a) (fun _ => c) fun _ => h
  convert this using 1
  funext i j
  simp [lc]

theorem matrix_comb (q : Y ⟶ Sp K) {φ θ θ' θ'' : Fin g → C1 U} (hφ : ∀ c, IsCob U (lc q c φ) → c = 0)
    {Θ Θ' Θ'' : Matrix (Fin g) (Fin g) K} (c : K) (h : ∀ b, IsCob U (θ b - lc q (Θ b) φ))
    (h' : ∀ b, IsCob U (θ' b - lc q (Θ' b) φ)) (h'' : ∀ b, IsCob U (θ'' b - lc q (Θ'' b) φ))
    (e : ∀ a, IsCob U (fun i j => θ'' a i j - constFn q _ c * θ a i j - θ' a i j)) : Θ'' = c • Θ + Θ' := by
  rw [← sub_eq_zero]
  funext b
  refine hφ _ ?_
  convert (((e b).sub (h'' b)).add (isCob_const_mul q c (h b))).add (h' b) using 1
  funext i j
  have : ∀ a, constFn q (U i ⊓ U j) ((Θ'' - (c • Θ + Θ')) b a) = constFn q (U i ⊓ U j) (Θ'' b a) -
      (constFn q (U i ⊓ U j) c * constFn q (U i ⊓ U j) (Θ b a) + constFn q (U i ⊓ U j) (Θ' b a)) := fun a => by
    simp [constFn]
  simp only [lc, Pi.add_apply, Pi.sub_apply, this, sub_mul, add_mul, mul_sub, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.mul_sum, _root_.mul_assoc]
  ring

end Linear

def linearOfComb {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (f : V → W)
    (h : ∀ (c : K) x y, f (c • x + y) = c • f x + f y) : V →ₗ[K] W where
  toFun := f
  map_add' x y := by simpa using h 1 x y
  map_smul' c x := by
    have h0 : f 0 = 0 := by simpa using h 1 0 0
    simpa [h0] using h c x 0

theorem lbIso_cube_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {s : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G s φ) {L : LB G.left} {L' : LB G'.left}
    (hL : L.IsLB) (hL' : L'.IsLB) (e : LBIso L' (L.pull φ)) {f f' : G ⟶ G} {f₀ f₀' : G' ⟶ G'}
    (hf : f₀.left ≫ φ = φ ≫ f.left) (hf' : f₀'.left ≫ φ = φ ≫ f'.left)
    (H : LBIso (cubeLB G ![fst G G ≫ f, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ f'] L)) :
    LBIso (cubeLB G' ![fst G' G' ≫ f₀, snd G' G'] L') (cubeLB G' ![fst G' G', snd G' G' ≫ f₀'] L') := by
  obtain ⟨w, hw⟩ := e
  have pa : ∀ {a : G ⟶ G} {a₀ : G' ⟶ G'}, a₀.left ≫ φ = φ ≫ a.left → ∀ {T : Over S'} (x : T ⟶ G'),
      pushPt h.1.w (x ≫ a₀) = pushPt h.1.w x ≫ a := fun ha _ x => Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, ha, Category.assoc])
  let U := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))
  have M : LBIso (L.LinComb (fun I : ULift (Finset (Fin 2)) => (psum G' ![fst G' G' ≫ f₀, snd G' G'] I.down).left ≫ φ)
        fun I => (-1) ^ (2 - I.down.card))
      (L.LinComb (fun I : ULift (Finset (Fin 2)) => (psum G' ![fst G' G', snd G' G' ≫ f₀'] I.down).left ≫ φ)
        fun I => (-1) ^ (2 - I.down.card)) := by
    refine LBIso.chartPull (chartPullSame L _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
      (chartPullSame L _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) H
    · fin_cases i
      · exact (pa hf _).trans (by simp [U])
      · simp [U]
    · fin_cases i
      · simp [U]
      · exact (pa hf' _).trans (by simp [U])
  exact LBIso.trans (DVR.linComb_isLB _ hL' _ _) (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _)
    (iso_linComb ((isGen_iff w).1 hw) _ _)
    (LBIso.trans (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _) M
      (iso_linComb ((isGen_iff w).1 hw) _ _).symm)

theorem isDerK_snd {K : Type} [Field K] {r : ℕ} (lam : (Fin r → K) →ₗ[K] K) :
    IsDerK (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom (fun x => lam x.snd) := by
  refine ⟨fun a b => by simp, fun a b => ?_⟩
  simp [TrivSqZeroExt.snd_mul]

theorem spMap_fst_dirMap {K : Type} [Field K] {r : ℕ} (lam : (Fin r → K) →ₗ[K] K) :
    spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (dirMap lam) =
      spMap (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x <;> simp [dirMap]

theorem exists_ksMatrix_of
    (href : ∀ (X : Scheme.{0}) (L : LB X), CompactSpace X → L.IsLB → ∃ L' : LB X, Finite L'.ι ∧ L'.IsLB ∧ (∀ i, IsAffineOpen (L'.U i)) ∧ LBIso L L')
    (hinv : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (v : epsR K ⟶ A₀), IsTangent v → (∃ dd, IsInvDer v dd) ∧ ∀ dd, IsInvDer v dd → (∀ W f f', dd W (f + f') = dd W f + dd W f') ∧ (∀ W f f', dd W (f * f') = f * dd W f' + f' * dd W f) ∧ (∀ W W' (f : Γ(A₀.left, W)), W' ≤ W → dd W' (rsT f W') = rsT (dd W f) W') ∧ (∀ W a, dd W (constFn A₀.hom W a) = 0) ∧ ∀ dd', IsInvDer v dd' → dd' = dd)
    (hphi : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (X : Scheme.{0}) (m : P₀.A.left ⟶ X) (L : LB X), L.IsLB → LBIso P₀.L (L.pull m) → (∃ φ, IsDlog m L dd φ) ∧ ∀ φ, IsDlog m L dd φ → (∀ a, IsCoc _ (φ a)) ∧ ∀ c, IsCob _ (lc P₀.A.hom c φ) → c = 0)
    (hcoc : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → Smooth p → ∀ (D : R → K) (I : Type) (W : I → X.Opens), IsDerK x₀ D → (∀ i, IsAffineOpen (W i)) → ∃ d θ, KSCoc A₀.hom p m D W dd d θ ∧ ∀ a, IsCoc _ (θ a))
    (hlin : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → ∀ (I : Type) (W : I → X.Opens) (D D' : R → K) (c : K) d d' d'' θ θ' θ'', KSCoc A₀.hom p m D W dd d θ → KSCoc A₀.hom p m D' W dd d' θ' → KSCoc A₀.hom p m (fun r => c * D r + D' r) W dd d'' θ'' → ∀ a, IsCob _ (fun i j => θ'' a i j - constFn A₀.hom _ c * θ a i j - θ' a i j))
    (hsym : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) (m : P₀.A.left ⟶ P.A.left) (L : LB P.A.left) [Finite L.ι] (D : R → K) (d : L.ι → ∀ O : P.A.left.Opens, Γ(P.A.left, O) → Γ(P₀.A.left, m ⁻¹ᵁ O)) (θ φ : Fin g → C1 (fun i => m ⁻¹ᵁ L.U i)), IsGrpPullback P₀.A P.A (spMap x₀) m → L.IsLB → (∀ i, IsAffineOpen (L.U i)) → LBIso P₀.L (L.pull m) → KSCoc P₀.A.hom P.A.hom m D L.U dd d θ → IsDlog m L dd φ → ∃ Θ : Matrix (Fin g) (Fin g) K, Θ.IsSymm ∧ ∀ b, IsCob (fun i => m ⁻¹ᵁ L.U i) (θ b - lc P₀.A.hom (Θ b) φ))
    (hend : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) (m : P₀.A.left ⟶ P.A.left) (L : LB P.A.left) [Finite L.ι] (D : R → K) (d : L.ι → ∀ O : P.A.left.Opens, Γ(P.A.left, O) → Γ(P₀.A.left, m ⁻¹ᵁ O)) (θ φ : Fin g → C1 (fun i => m ⁻¹ᵁ L.U i)), IsGrpPullback P₀.A P.A (spMap x₀) m → L.IsLB → (∀ i, IsAffineOpen (L.U i)) → LBIso P₀.L (L.pull m) → KSCoc P₀.A.hom P.A.hom m D L.U dd d θ → IsDlog m L dd φ → ∀ (Θ : Matrix (Fin g) (Fin g) K) (f : P.A ⟶ P.A) (f₀ f₀' : P₀.A ⟶ P₀.A) (F F' : Matrix (Fin g) (Fin g) K), (∀ b, IsCob (fun i => m ⁻¹ᵁ L.U i) (θ b - lc P₀.A.hom (Θ b) φ)) → IsMonHom f₀ → IsMonHom f₀' → f₀.left ≫ m = m ≫ f.left → LBIso (cubeLB P₀.A ![fst P₀.A P₀.A ≫ f₀, snd P₀.A P₀.A] P₀.L) (cubeLB P₀.A ![fst P₀.A P₀.A, snd P₀.A P₀.A ≫ f₀'] P₀.L) → (∀ j, IsLieComb (fun i => F i j) v (v j ≫ f₀)) → (∀ j, IsLieComb (fun i => F' i j) v (v j ≫ f₀')) → F * Θ = Θ * F'.transpose)
    (hzero : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → ∀ (I : Type) (W : I → X.Opens) (D : R → K) d θ, ⨆ i, W i = ⊤ → KSCoc A₀.hom p m D W dd d θ → (∀ a, IsCob _ (θ a)) → ∃ d₁, LocDerK A₀.hom p m D ⊤ d₁)
    (htriv : Out.Laws → ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (R : Type) [CommRing R] (xD : R →+* DualNumber K) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (ψ : A'.left ⟶ A.left) (j : A₀.left ⟶ A'.left) (d : ∀ W : A.left.Opens, Γ(A.left, W) → Γ(A₀.left, (j ≫ ψ) ⁻¹ᵁ W)), IsAbelianScheme A₀ → IsAbelianScheme A' → IsGrpPullback A' A (spMap xD) ψ → IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) j → LocDerK A₀.hom A.hom (j ≫ ψ) (fun r => (xD r).snd) ⊤ d → ∃ ρ, IsConstK A' A₀ ρ j) :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (P : Out.PolAV (Sp (TrivSqZeroExt K (Fin r → K)))) (P₀ : Out.PolAV (Sp K)) (φ₀ : P₀.A.left ⟶ P.A.left) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)), IsGrpPullback P₀.A P.A (spMap (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom) φ₀ → LBIso P₀.L (P.L.pull φ₀) → IsLieBasis v → ∃ Θ : ((Fin r → K) →ₗ[K] K) →ₗ[K] Matrix (Fin g) (Fin g) K, (∀ lam, (Θ lam).IsSymm) ∧ (∀ (f f' : P.A ⟶ P.A) (f₀ f₀' : P₀.A ⟶ P₀.A) (F F' : Matrix (Fin g) (Fin g) K), IsMonHom f → IsMonHom f' → f₀.left ≫ φ₀ = φ₀ ≫ f.left → f₀'.left ≫ φ₀ = φ₀ ≫ f'.left → LBIso (cubeLB P.A ![fst P.A P.A ≫ f, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ f'] P.L) → (∀ j, IsLieComb (fun i => F i j) v (v j ≫ f₀)) → (∀ j, IsLieComb (fun i => F' i j) v (v j ≫ f₀')) → ∀ lam, F * Θ lam = Θ lam * F'.transpose) ∧ ∀ lam, Θ lam = 0 → ∀ (G : Over (Sp (DualNumber K))) [GrpObj G] (ψ : G.left ⟶ P.A.left), IsGrpPullback G P.A (spMap (dirMap lam)) ψ → ∃ ψ₀ : G.left ⟶ P₀.A.left, IsGrpPullback G P₀.A (spMap (algebraMap K (DualNumber K))) ψ₀ ∧ ∀ io : P₀.A.left ⟶ G.left, io ≫ ψ = φ₀ → io ≫ G.hom = P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom → io ≫ ψ₀ = 𝟙 _ := by
  intro hL hL2 hC K _ _ r P P₀ φ₀ g v hp hI hv
  have hc : CompactSpace P.A.left := by
    have := P.isAb.proper
    exact QuasiCompact.compactSpace_of_compactSpace P.A.hom
  obtain ⟨L, hfin, hLB, haff, hiso⟩ := href _ P.L hc P.isLB
  have hI' : LBIso P₀.L (L.pull φ₀) := LBIso.trans P₀.isLB (pull_isLB P.isLB _) (pull_isLB hLB _) hI
    (hiso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (Geo.Tor.chartPullPull _ _ _ rfl))
  choose dd hdd using fun a => (hinv K P₀.A (v a) (hv.1 a)).1
  obtain ⟨⟨φ, hφ⟩, hφ'⟩ := hphi K P₀ g v dd hv hdd _ φ₀ L hLB hI'
  have hind := (hφ' φ hφ).2
  choose d θ hks _ using fun lam : (Fin r → K) →ₗ[K] K =>
    hcoc K P₀.A g v dd P₀.isAb.smooth hv hdd _ _ _ P.A.hom φ₀ hp.1 P.isAb.smooth _ L.ι L.U (isDerK_snd lam) haff
  choose Θ hΘ hΘ' using fun lam : (Fin r → K) →ₗ[K] K =>
    hsym hL hL2 hC K P₀ g v dd hv hdd _ _ P φ₀ L _ (d lam) (θ lam) φ hp hLB haff hI' (hks lam) hφ
  refine ⟨linearOfComb Θ fun c x y => matrix_comb P₀.A.hom hind c (hΘ' x) (hΘ' y) (hΘ' _)
    (hlin K P₀.A g v dd P₀.isAb.smooth hv hdd _ _ _ P.A.hom φ₀ hp.1 L.ι L.U _ _ c _ _ _ _ _ _ (hks x) (hks y)
      (hks (c • x + y))), hΘ, fun f f' f₀ f₀' F F' hf hf' e e' H hF hF' lam => ?_, fun lam h0 G _ ψ hψ => ?_⟩
  · exact hend K P₀ g v dd hv hdd _ _ P φ₀ L _ (d lam) (θ lam) φ hp hLB haff hI' (hks lam) hφ (Θ lam) f f₀ f₀' F F'
      (hΘ' lam) (PureType.isMonHom_over hp hp e) (PureType.isMonHom_over hp hp e') e
      (lbIso_cube_pull hp P.isLB P₀.isLB hI e e' H) hF hF'
  · have h0' : Θ lam = 0 := h0
    have hcob : ∀ a, IsCob _ (θ lam a) := fun a => by
      convert hΘ' lam a using 1
      funext i j
      simp [h0', lc, constFn]
    obtain ⟨d₁, hd₁⟩ := hzero K P₀.A g v dd P₀.isAb.smooth hv hdd _ _ _ P.A.hom φ₀ hp.1 L.ι L.U _ _ _ hLB.cover
      (hks lam) hcob
    have w : φ₀ ≫ P.A.hom = (P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ spMap (dirMap lam) := by
      rw [Category.assoc, spMap_fst_dirMap, hp.1.w]
    obtain ⟨j, hj, hj'⟩ : ∃ j : P₀.A.left ⟶ G.left, j ≫ ψ = φ₀ ∧
        j ≫ G.hom = P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom :=
      ⟨hψ.1.lift _ _ w, hψ.1.lift_fst _ _ w, hψ.1.lift_snd _ _ w⟩
    have hD : (fun x : TrivSqZeroExt K (Fin r → K) => (dirMap lam x).snd) = fun x => lam x.snd :=
      funext fun x => TrivSqZeroExt.snd_map lam x
    obtain ⟨d₂, hd₂⟩ : ∃ d₂, LocDerK P₀.A.hom P.A.hom (j ≫ ψ) (fun x => (dirMap lam x).snd) ⊤ d₂ := by
      rw [hj, hD]
      exact ⟨d₁, hd₁⟩
    obtain ⟨ρ, hρ, -, hρ'⟩ := htriv hL K P₀.A _ (dirMap lam) P.A G ψ j d₂ P₀.isAb
      (PolPull.isAbelianScheme_of_isGrpPullback P.isAb hψ) hψ
      (hψ.cancel (hp.congr (spMap_fst_dirMap lam).symm hj.symm) hj') hd₂
    refine ⟨ρ, hρ, fun io h₁ h₂ => ?_⟩
    rw [hψ.1.hom_ext (h₁.trans hj.symm) (h₂.trans hj'.symm), hρ']

end GlobalTheory.KSField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocLoc
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

theorem concl_map (hL : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ} {R R' : Type} [CommRing R] [CommRing R']
    {β : o →+* R} {v : Ix g (N' ^ 2) → R} (h : Concl b Mat κ β v) (ρ : R →+* R') :
    Concl b Mat κ (ρ.comp β) (fun a => ρ (v a)) := by
  obtain ⟨t, hth, hall⟩ := h
  have hs : spMap ρ ≫ spMap β = spMap (ρ.comp β) := (spMap_comp ρ β).symm
  obtain ⟨t₂, h₂⟩ := _root_.GlobalTheory.tObj_pull o g (N' ^ 2) J b (Sp R) (Sp R') (spMap β) (spMap (ρ.comp β)) (spMap ρ) t hs
  refine ⟨t₂, ?_, ?_⟩
  · rw [_root_.GlobalTheory.hasTh_iff_of_tmap o g N' J b (Sp R) (spMap β) t (Sp R') (spMap (ρ.comp β)) t₂ (spMap ρ) R' (𝟙 _) _ h₂,
      Category.id_comp]
    have hpush := _root_.GlobalTheory.hasTh_baseChange hL o g N' J b (Sp R) (spMap β) t R R' ρ (𝟙 _) v hth
    rwa [Category.comp_id] at hpush
  · intro K _ _ x s t' hg
    rw [good_comp] at hg
    have h3 := hall K (x.comp ρ) s t' hg
    rw [spMap_comp] at h3
    exact ((_root_.GlobalTheory.ZM.tmap_id_comp_cancel o g (N' ^ 2) J b (Sp R) (Sp R') (Sp K) (spMap β) (spMap (ρ.comp β)) s t t₂ t').2
      (spMap ρ) (spMap x) h₂).2 h3

theorem exists_loc_loc {R : Type} [CommRing R] (f : R) (q₁ : Ideal (Localization.Away f)) (hq : q₁.IsPrime)
    (f' : Localization.Away f) (hf' : f' ∉ q₁) :
    ∃ F : R, F ∉ q₁.comap (loc f) ∧ ∃ ρ : Localization.Away f' →+* Localization.Away F,
      (ρ.comp (loc f')).comp (loc f) = loc F := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj f f'
  have hunit : IsUnit (loc f f) := IsLocalization.Away.algebraMap_isUnit f
  have hfq : loc f f ∉ q₁ := fun hm => hq.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hunit)
  refine ⟨f * a, ?_, ?_⟩
  · intro hm
    rw [Ideal.mem_comap, map_mul] at hm
    rcases hq.mem_or_mem hm with h1 | h1
    · exact hfq h1
    · have h2 : f' * algebraMap R (Localization.Away f) f ^ n ∈ q₁ := by rw [ha]; exact h1
      rcases hq.mem_or_mem h2 with h3 | h3
      · exact hf' h3
      · exact hfq (hq.mem_of_pow_mem n h3)
  · have hF : IsUnit (loc (f * a) (f * a)) := IsLocalization.Away.algebraMap_isUnit (f * a)
    rw [map_mul] at hF
    have hf1 : IsUnit (loc (f * a) f) := isUnit_of_mul_isUnit_left hF
    have ha1 : IsUnit (loc (f * a) a) := isUnit_of_mul_isUnit_right hF
    have hσ : (IsLocalization.Away.lift f hf1).comp (loc f) = loc (f * a) := IsLocalization.Away.lift_comp f hf1
    have e : IsLocalization.Away.lift f hf1 f' * IsLocalization.Away.lift f hf1 (loc f f) ^ n = loc (f * a) a := by
      rw [← map_pow, ← map_mul, ha]
      exact RingHom.congr_fun hσ a
    rw [← e] at ha1
    have hu : IsUnit (IsLocalization.Away.lift f hf1 f') := isUnit_of_mul_isUnit_left ha1
    refine ⟨IsLocalization.Away.lift f' hu, ?_⟩
    rw [IsLocalization.Away.lift_comp f' hu]
    exact hσ

theorem nearC_of_loc : Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (f : R) (q₁ : Ideal (Localization.Away f)), q₁.IsPrime → NearC b Mat κ ((loc f).comp β) (fun a => loc f (v a)) q₁ → NearC b Mat κ β v (q₁.comap (loc f)) := by
  intro hL o _ g N' J b Mat κ R _ β v f q₁ hq h
  obtain ⟨f', hf', hc⟩ := h
  obtain ⟨F, hF, ρ, hρ⟩ := exists_loc_loc f q₁ hq f' hf'
  refine ⟨F, hF, ?_⟩
  have key : ∀ r : R, ρ (loc f' (loc f r)) = loc F r := fun r => RingHom.congr_fun hρ r
  have hc2 : Concl b Mat κ (ρ.comp ((loc f').comp ((loc f).comp β))) (fun a => ρ (loc f' (loc f (v a)))) :=
    concl_map hL hc ρ
  have e1 : ρ.comp ((loc f').comp ((loc f).comp β)) = (loc F).comp β := RingHom.ext fun r => key (β r)
  have e2 : (fun a => ρ (loc f' (loc f (v a)))) = fun a => loc F (v a) := funext fun a => key (v a)
  rw [e1, e2] at hc2
  exact hc2

end GlobalTheory.ZM.NearBuild
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsMemNonzeroLocus
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionDense

open GoodPoint

theorem exists_sec_lPow {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (T : Over S) (k : ℕ)
    (s : (lbPow L k).Sec) : ∃ s' : LB.Sec (LPow A L k T), ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J),
      Good L z J → (IsUnit (powVal s' r z J) ↔ (r ≫ (snd T A).left) z ∈ nonzeroLocus s) := by
  obtain ⟨s', hs'⟩ := exists_sec hL (φ' := fun _ : Fin 1 => (snd T A).left) (ε' := fun _ => (k : ℤ))
    (fun U _ h => by simp [Fintype.prod_sum_type, -Over.snd_left])
    (pullMulSec (L := L) (φ := fun _ : PUnit => 𝟙 A.left) (ε := fun _ => (k : ℤ)) s (snd T A).left
      (LB.oneGen L (Y := (T ⊗ A).left))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
        (_root_.mul_one _)).symm))
  refine ⟨s', fun Z r z J hJ => ?_⟩
  have e := (hs' Z r z J hJ).trans (sval_pullMulSec _ _ _ _ r z hJ)
  refine (iff_of_eq (congrArg IsUnit e)).trans ?_
  rw [Units.isUnit_mul_units]
  exact (mem_nonzeroLocus_iff_pull s _ z (hJ.mem (fun _ : PUnit => 𝟙 A.left) _)).symm

variable {K : Type} [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K)))

theorem exists_mem_nonzeroLocus (hI : IrredSt) (hK : KerPowSt) (k : ℕ) (hk : 4 ≤ k) (hkK : (k : K) ≠ 0)
    (B : Set (baseOver (Spec (CommRingCat.of K)) ⟶ P.A)) (hB : ∀ w, w ^ k = 1 → ∀ b ∈ B, w * b ∈ B)
    (s t : (lbPow P.L k).Sec) (x : P.A.left) (hx : x ∈ nonzeroLocus s)
    (b : baseOver (Spec (CommRingCat.of K)) ⟶ P.A) (hb : b ∈ B)
    (p : (baseOver (Spec (CommRingCat.of K))).left) (ht : b.left p ∈ nonzeroLocus t) :
    ∃ b' ∈ B, ∃ p', b'.left p' ∈ nonzeroLocus s := by
  by_contra hcon
  obtain ⟨s', hs'⟩ := exists_sec_lPow P.isLB (baseOver _) k s
  obtain ⟨t', ht'⟩ := exists_sec_lPow P.isLB (baseOver _) k t
  rcases hI K P k (Or.inr hk) hkK (vanishing P.L _ B)
    (fun θ s s' h hsB q hq y J hJ => by
      obtain ⟨c, hc⟩ := powVal_act h (ptSecT P.A q).left hJ
      rw [← Over.comp_left, ptSecT_translT] at hc
      refine (congrArg (· ∈ IsLocalRing.maximalIdeal _) hc).mpr
        (Ideal.mul_mem_left _ _ (hsB _ (hB _ ?_ q hq) y J hJ))
      exact (hK _ P k (by omega) _ θ.pt).1 fun p => ⟨⊤, trivial, exists_isGen_pull _ θ.φ θ.isGen _⟩) with h | h
  · have hm : SecM.ofSec P.A s' ∈ vanishing P.L _ B := fun q hq y J hJ hu => by
      have := (hs' _ _ y J hJ).1 hu
      rw [← Over.comp_left, ptSecT_snd] at this
      exact hcon ⟨q, hq, y, this⟩
    rw [h, Submodule.mem_bot] at hm
    choose J hJ using fun χ : P.A.left ⟶ P.A.left => exists_chart P.isLB (χ x)
    have hu := (hs' _ (unitInv P.A).left x J hJ).2 (by rw [← Over.comp_left, unitInv_snd]; exact hx)
    have e : powVal s' (unitInv P.A).left x J = 0 :=
      (congrArg (gs _ x _) (congrFun (congrArg Subtype.val hm) _)).trans (gs_zero _ x _)
    rw [e] at hu
    exact not_isUnit_zero hu
  · choose J hJ using fun χ : (baseOver (Spec (CommRingCat.of K))).left ⟶ P.A.left => exists_chart P.isLB (χ p)
    have hm : SecM.ofSec P.A t' ∈ vanishing P.L _ B := by rw [h]; trivial
    exact hm b hb p J hJ ((ht' _ _ p J hJ).2 (by rw [← Over.comp_left, ptSecT_snd]; exact ht))

theorem dense_torsion [CharZero K] (hI : IrredSt) (hK : KerPowSt) :
    Dense (⋃ x ∈ {x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A | ∃ n : ℕ, 0 < n ∧ x ^ n = 1}, Set.range x.left) := by
  have := P.isAb.comm
  have hA := isAmpleLB_of_relAmple_of_isAffine P.A P.isLB P.ample
  refine dense_iff_inter_open.2 fun U hU ⟨x, hx⟩ => ?_
  obtain ⟨n, hn, s, hs, hle, -⟩ := hA.exists_affine_le (x := x) (U := ⟨U, hU⟩) hx
  let p : (baseOver (Spec (CommRingCat.of K))).left := IsLocalRing.closedPoint K
  obtain ⟨m, hm, t, ht, -⟩ := hA.exists_affine ((1 : baseOver (Spec (CommRingCat.of K)) ⟶ P.A).left p)
  have e₁ := nonzeroLocus_secPow s (k := m * 4) (by omega)
  have e₂ := nonzeroLocus_secPow t (k := n * 4) (by omega)
  have hk : 4 ≤ n * (m * 4) := by nlinarith [Nat.mul_pos hn hm]
  obtain ⟨b, hb, q, hq⟩ := exists_mem_nonzeroLocus P hI hK (n * (m * 4)) hk (Nat.cast_ne_zero.2 (by omega))
    {x | ∃ n : ℕ, 0 < n ∧ x ^ n = 1} (fun w hw b ⟨l, hl, hb⟩ => ⟨n * (m * 4) * l, Nat.mul_pos (by omega) hl, by
      rw [mul_pow, pow_mul w, hw, one_pow, mul_comm _ l, pow_mul, hb, one_pow, _root_.one_mul]⟩)
    (secPow s (m * 4)) (secCast (by ring) (secPow t (n * 4))) x (e₁.ge hs) 1 ⟨1, one_pos, one_pow _⟩ p (e₂.ge ht)
  exact ⟨b.left q, hle (e₁.le hq), Set.mem_iUnion₂.2 ⟨b, hb, q, rfl⟩⟩

end GlobalTheory.TorsionDense
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationAtPointClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PointUnif

theorem exists_uniformisation_at_point_closed : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ y : Sp ℂ ⟶ Xo.X, y ≫ Xo.s = spMap σ → ∃ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (P : D'.La →+ (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)), (D'.p = D.p ∧ D'.q = D.q ∧ ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧ σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν l.A : ℂ) / l.A) ∧ t = f l.M') ∧ (y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧ ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧ (∀ z, e z = 1 ↔ z ∈ (P).range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a))) :=
  fun hT hL => exists_uniformisation_at_point hT hL GlobalTheory.LiePull.lieMult_pull GlobalTheory.obj_pull
    GlobalTheory.obj_isAbelianScheme_dim_rigidified_sym GlobalTheory.PeriodDatum.exists_datum

end GlobalTheory.PointUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueThetaCharOfUnif
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem GlobalTheory.existsUnique_thetaChar_of_unif : ThetaUnifAV → Out.Laws → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap o' o f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ Xo.univ.t.G)) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D'.La) (sgn : ℤˣ) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ b ∈ B, ((y b) ≫ Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b) 0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ • (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a)))) → (∀ a b, D'.EF (bas a) (bas b) = sgn * omegaStd a b) → (∀ b ∈ B, ((τ b).map Complex.im).PosDef ∧ ∀ k, (h b).mulVec (P b (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧ (h b).mulVec (P b (bas (Pi.single (.inr k) 1))) = (τ b).mulVec (Pi.single k 1)) → ∀ b₀ ∈ B, ∃! cc : (Fin g → ℂ) × (Fin g → ℂ), ∃ c₁ c₂, cc = (c₁, c₂) ∧ (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) ∧ (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) ∧ IsThetaFrame Xo.univ.t.PP {b₀} y (fun b z => (e b z).left) (fun b z => thetaChar (τ b) c₁ c₂ ((h b).mulVec z)) :=
  fun hT hLaws _ _ => GlobalTheory.existsUnique_thetaChar_at_point' hT hLaws
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinrankSectionsPullbackMulByNTwistsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionsHaveFiniteDimension_lbDiv_linComb : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (k r : ℕ), M.IsLB → (k : K) ≠ 0 → (∀ y : 𝟙_ (Over (Sp K)) ⟶ P.A, y ^ k = 1 → SectionsHaveFiniteDimension P.A.hom (LB.div M (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, ((toUnit P.A ≫ y) * 𝟙 P.A).left] ![1, -1])) r) → SectionsHaveFiniteDimension P.A.hom (M.pull (Out.mulA P.A k).left) (k ^ (2 * P.g) * r) := by
  first | exact @GlobalTheory.TwistSplit.finrank_sections_pullback_mulByN_twists | exact GlobalTheory.TwistSplit.finrank_sections_pullback_mulByN_twists | (intros; apply GlobalTheory.TwistSplit.finrank_sections_pullback_mulByN_twists <;> assumption)
end

