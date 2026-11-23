module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2094
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2125
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackLineBundleGeneratorAdditivityDefect
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

namespace GlobalTheory.CharKer

theorem gm_of_isPullGen {X Y Z : Scheme.{0}} {p : X ⟶ Y} {M : LB Y} {e : ∀ k, Γ(X, p ⁻¹ᵁ M.U k)ˣ}
    (he : IsPullGen p M e) (ψ : Z ⟶ X) (z : Z) (k l : M.ι) (hk : p (ψ z) ∈ M.U k) (hl : p (ψ z) ∈ M.U l) :
    gm ψ z (p ⁻¹ᵁ M.U k) (e k) = gm (ψ ≫ p) z (M.U k ⊓ M.U l) (M.g k l) * gm ψ z (p ⁻¹ᵁ M.U l) (e l) := by
  have hm : ψ z ∈ p ⁻¹ᵁ (M.U k ⊓ M.U l) := ⟨hk, hl⟩
  have h := congrArg (gm ψ z (p ⁻¹ᵁ (M.U k ⊓ M.U l)))
    (he k l (p ⁻¹ᵁ (M.U k ⊓ M.U l)) (fun _ hy => hy.1) (fun _ hy => hy.2) le_rfl)
  exact (gm_res _ _ _ hm _).symm.trans (h.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ((gm_res _ _ _ hm _).trans (gm_pull ψ p z _ hm _)) (gm_res _ _ _ hm _))))

theorem gm_pull_of_isPullGen {X Y X₂ Y₂ : Scheme.{0}} {p : X ⟶ Y} {M : LB Y} {e : ∀ k, Γ(X, p ⁻¹ᵁ M.U k)ˣ}
    (he : IsPullGen p M e) {P : X₂ ⟶ Y₂} {φ : Y₂ ⟶ Y} {ψ : X₂ ⟶ X} (h : P ≫ φ = ψ ≫ p) (x : X₂)
    (J J' : PUnit → M.ι) (hJ : P x ∈ (M.pull φ).U J) (hJ' : P x ∈ (M.pull φ).U J') :
    gm ψ x (p ⁻¹ᵁ M.U (J PUnit.unit)) (e (J PUnit.unit)) =
      gm P x ((M.pull φ).U J ⊓ (M.pull φ).U J') ((M.pull φ).g J J') *
        gm ψ x (p ⁻¹ᵁ M.U (J' PUnit.unit)) (e (J' PUnit.unit)) := by
  rw [gm_pull_g M φ P x J J' hJ hJ', h]
  exact gm_of_isPullGen he ψ x _ _ (preimage_le_of_comp h _ (mem_pull.1 hJ)) (preimage_le_of_comp h _ (mem_pull.1 hJ'))

theorem gm_res_pullU {X Z : Scheme.{0}} (ψ : Z ⟶ X) (z : Z) (U : X.Opens) {V : Z.Opens} (hle : V ≤ ψ ⁻¹ᵁ U)
    (hz : z ∈ V) (a : Γ(X, U)ˣ) : gm (𝟙 Z) z V (res hle (pullU ψ U a)) = gm ψ z U a :=
  (gm_res (𝟙 Z) z hle hz _).trans ((gm_pull (𝟙 Z) ψ z U (hle hz) a).trans (by rw [Category.id_comp]))

theorem germ_addGen_pullGen {S : Scheme.{0}} {A A' T : Over S} [MonObj A] [MonObj A'] (q : A ⟶ A') [IsMonHom q]
    (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ) (k : (addBundle M).ι)
    (x : (A ⊗ (A ⊗ T)).left) (hx : x ∈ (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k) :
    gm (𝟙 _) x _ (addGen q M e k) =
      gm (ptFst A T).left x _ (e (k.1.1 PUnit.unit)) * gm (ptSnd A T).left x _ (e (k.1.2 PUnit.unit)) *
        (gm (ptMul A T).left x _ (e (k.2 PUnit.unit)))⁻¹ := by
  rw [addGen, map_mul, map_mul, map_inv, gm_res_pullU _ _ _ _ hx, gm_res_pullU _ _ _ _ hx, gm_res_pullU _ _ _ _ hx]

theorem isPullGen_addGen : ∀ (S : Scheme.{0}) (A A' T : Over S) [MonObj A] [MonObj A'] (q : A ⟶ A') [IsMonHom q] (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), IsPullGen (pmap q T).left M e → IsPullGen (pmap2 q T).left (addBundle M) (addGen q M e) := by
  intro S A A' T _ _ q _ M e he k l W h₁ h₂ h₃
  refine unit_ext fun x hx => ?_
  have hk := h₁ hx
  have hl := h₂ hx
  have e₁ := gm_pull_of_isPullGen he (prodMapPairTimesIdentity_fst q T) x k.1.1 l.1.1 hk.1.1 hl.1.1
  have e₂ := gm_pull_of_isPullGen he (prodMapPairTimesIdentity_snd q T) x k.1.2 l.1.2 hk.1.2 hl.1.2
  have e₃ := gm_pull_of_isPullGen he (prodMapPairTimesIdentity_mul q T) x k.2 l.2 hk.2 hl.2
  have g := (gm_div _ _ (pmap2 q T).left x k l ⟨hk, hl⟩).trans
    (congrArg (· * _) (gm_tens _ _ (pmap2 q T).left x k.1 l.1 hk.1 hl.1))
  refine ((gm_res (𝟙 _) x h₁ hx _).trans (germ_addGen_pullGen q M e k x hk)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res_pullU _ x _ h₃ hx _).trans g)
    ((gm_res (𝟙 _) x h₂ hx _).trans (germ_addGen_pullGen q M e l x hl)))).trans ?_
  rw [e₁, e₂, e₃, mul_inv]
  have alg : ∀ {G : Type} [CommGroup G] (a b c u v w : G),
      a * b * c⁻¹ * (u * v * w⁻¹) = a * u * (b * v) * (c⁻¹ * w⁻¹) := by
    intro G _ a b c u v w
    ac_rfl
  exact alg _ _ _ _ _ _

end GlobalTheory.CharKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularFibreOfJacobianDerivations
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem regular_fibre_of_jacobian : ∀ (S T K : Type) [CommRing S] [CommRing T] [Algebra S T] [IsRegularRing T] [Field K] [Algebra S K] (Q : Ideal S), RingHom.ker (algebraMap S K) = Q → (∀ y : K, ∃ a b : S, b ∉ Q ∧ y * algebraMap S K b = algebraMap S K a) → ∀ (h : ℕ) (f : Fin h → S) (g : S) (d : Fin h → Derivation ℤ S S) (D : Fin h → Derivation ℤ T T), (∀ i x, D i (algebraMap S T x) = algebraMap S T (d i x)) → g ∉ Q → (∀ j, f j ∈ Q) → (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) → (Matrix.of fun i j => d i (f j)).det ∉ Q → IsRegularRing (T ⊗[S] K) := by
  intro S T K _ _ _ _ _ _ Q hker hfrac h f g d D hD hg hf hgQ hdet
  refine _root_.GlobalTheory.isRegularRing_tensor_of_fibre_localRings S T K Q hker hfrac ?_
  intro n _ hn
  set F : Fin h → T := fun j => algebraMap S T (f j) with hFdef
  have hFn : ∀ j, F j ∈ n := by
    intro j
    have : f j ∈ n.comap (algebraMap S T) := by rw [hn]; exact hf j
    exact this
  have hdetn : (Matrix.of fun i j => D i (F j)).det ∉ n := by
    intro hmem
    have hm : (Matrix.of fun i j => D i (F j)) = (Matrix.of fun i j => d i (f j)).map (algebraMap S T) := by
      ext i j; simp [hFdef, hD]
    rw [hm, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hmem
    have : (Matrix.of fun i j => d i (f j)).det ∈ n.comap (algebraMap S T) := hmem
    rw [hn] at this
    exact hdet this
  have hreg := _root_.GlobalTheory.JacobianDerivation.isRegularLocalRing_quotient T h F D n hFn hdetn
  have heq : (Ideal.span (Set.range F)).map (algebraMap T (Localization.AtPrime n)) =
      (Q.map (algebraMap S T)).map (algebraMap T (Localization.AtPrime n)) := by
    have hspan : Ideal.span (Set.range F) = (Ideal.span (Set.range f)).map (algebraMap S T) := by
      rw [Ideal.map_span, ← Set.range_comp]; rfl
    rw [hspan, Ideal.map_map, Ideal.map_map]
    apply le_antisymm
    · apply Ideal.map_mono
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact hf j
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap]
      have hu : IsUnit ((algebraMap T (Localization.AtPrime n)).comp (algebraMap S T) g) := by
        rw [RingHom.comp_apply]
        apply IsLocalization.map_units (M := n.primeCompl) (Localization.AtPrime n) (⟨algebraMap S T g, ?_⟩ : n.primeCompl)
        intro hgn
        have : g ∈ n.comap (algebraMap S T) := hgn
        rw [hn] at this
        exact hg this
      have hm : (algebraMap T (Localization.AtPrime n)).comp (algebraMap S T) (g * x) ∈
          (Ideal.span (Set.range f)).map ((algebraMap T (Localization.AtPrime n)).comp (algebraMap S T)) :=
        Ideal.mem_map_of_mem _ (hgQ x hx)
      rw [map_mul] at hm
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp hm
  rw [← heq]
  exact hreg

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianOfIsGrpPullbackSquare
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isSemiAbelian_of_isGrpPullback_square : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] (G' : Over S')
    [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G f F → IsSemiAbelian G → IsSemiAbelian G' := by
  intro S S' f G _ G' _ F h hG
  have := hG.comm
  have : IsCommMonObj G' := GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback h
  obtain ⟨bc, mbc, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback f G hG)

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSncAdaptedCoordinatesOfMemNhds
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_nbhd_specializes_of_isClosed {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (F : Set Y) (hF : IsClosed F) (hη : genericPoint Y ∉ F) {y : Y} {O : Y.Opens} (hy : y ∈ O) :
    ∃ V : Y.Opens, y ∈ V ∧ V ≤ O ∧
      ∀ y' ∈ V, ∀ v, v ⤳ y' → Order.coheight v = 1 → v ∈ F → v ⤳ y := by
  classical
  obtain ⟨W, hW, hyW, hWO⟩ := exists_isAffineOpen_mem_and_subset hy
  haveI := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hN : NoetherianSpace W := by
    have := NoetherianSpace.range hW.fromSpec hW.fromSpec.continuous
    rw [hW.range_fromSpec] at this
    exact this
  have hC : IsClosed ((Subtype.val : W → Y) ⁻¹' F) := hF.preimage continuous_subtype_val
  obtain ⟨S, hS, hc, hi, hU⟩ := @NoetherianSpace.exists_finite_set_isClosed_irreducible _ _ hN _ hC
  let y₀ : W := ⟨y, hyW⟩
  let bad : Set W := ⋃₀ {T ∈ S | y₀ ∉ T}
  have hS' : {T ∈ S | y₀ ∉ T}.Finite := hS.subset fun T hT => hT.1
  have hbad : IsClosed bad := by
    change IsClosed (⋃₀ {T ∈ S | y₀ ∉ T})
    rw [Set.sUnion_eq_biUnion]
    exact hS'.isClosed_biUnion fun T hT => hc T hT.1
  refine ⟨⟨Subtype.val '' badᶜ, W.isOpen.isOpenMap_subtype_val _ hbad.isOpen_compl⟩,
    ⟨y₀, ?_, rfl⟩, ?_, ?_⟩
  · rintro ⟨T, ⟨-, hyT⟩, hyT'⟩
    exact hyT hyT'
  · rintro _ ⟨x, -, rfl⟩
    exact hWO x.2
  · rintro _ ⟨x, hx, rfl⟩ v hv hcv hvF
    have hvW : v ∈ W := hv.mem_open W.isOpen x.2
    let v' : W := ⟨v, hvW⟩
    have hv' : v' ⤳ x := Topology.IsInducing.subtypeVal.specializes_iff.1 hv
    have hvS : v' ∈ ⋃₀ S := hU ▸ hvF
    obtain ⟨T, hT, hvT⟩ := hvS
    have hxT : x ∈ T := hv'.mem_closed (hc T hT) hvT
    have hyT : y₀ ∈ T := by
      by_contra h
      exact hx ⟨T, ⟨hT, h⟩, hxT⟩
    obtain ⟨g, hg⟩ := QuasiSober.sober (hi T hT) (hc T hT)
    have hgF : g.1 ∈ F := by
      have : g ∈ ⋃₀ S := ⟨T, hT, hg.mem⟩
      rw [← hU] at this
      exact this
    have hgv : g.1 ⤳ v := Topology.IsInducing.subtypeVal.specializes_iff.2 (hg.specializes hvT)
    have hgy : g.1 ⤳ y := Topology.IsInducing.subtypeVal.specializes_iff.2 (hg.specializes hyT)
    have hgη : g.1 < genericPoint Y := by
      refine lt_of_le_not_ge (genericPoint_specializes _) fun e => ?_
      have e' : g.1 = genericPoint Y := (Specializes.antisymm e (genericPoint_specializes _)).eq
      exact hη (e' ▸ hgF)
    have hvg : v = g.1 := by
      by_contra hne
      have h₃ := Order.coheight_add_one_le (show v < g.1 from lt_of_le_not_ge hgv fun e =>
        hne (Specializes.antisymm e hgv).eq)
      have h₄ := Order.coheight_add_one_le hgη
      rw [hcv] at h₃
      have h₅ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₄) 1).trans h₃
      exact absurd h₅ (by decide)
    rw [hvg]
    exact hgy

theorem isSncChart_spread : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ)
    (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U)
    (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ),
    genericPoint Y ∉ B → IsSncChart q n B y U hy z J w u → ∃ V : Y.Opens, y ∈ V ∧ ∀ y' ∈ V,
      ∃ (hy' : y' ∈ U) (J' : Finset (Fin n)), J' ⊆ J ∧ IsSncChart q n B y' U hy' z J' w u ∧
        ∀ j ∈ J', y' ∉ Y.basicOpen (z j) := by
  intro Y _ _ q n _ B y U hy z J w u hη hc
  classical
  have hηb : ∀ j ∈ J, genericPoint Y ∈ Y.basicOpen (z j) := fun j hj =>
    (Y.mem_basicOpen (z j) _ (gen_mem hy)).2 (by
      have : IsUnit (u j : Y.functionField) := (u j).isUnit
      rw [hc.val j hj] at this
      exact this)
  have hord0 : ∀ j ∈ J, ∀ v ∈ Y.basicOpen (z j), Scheme.ord (u j : Y.functionField) v = 0 := by
    intro j hj v hv
    haveI : Nonempty (Y.basicOpen (z j)) := ⟨⟨v, hv⟩⟩
    have h1 := Scheme.ord_of_isUnit (U := Y.basicOpen (z j))
      (Y.toRingedSpace.isUnit_res_basicOpen (z j)) hv
    rw [hc.val j hj, ← h1]
    congr 1
    exact (Y.presheaf.germ_res_apply (homOfLE (Y.basicOpen_le (z j))) _ _ (z j)).symm
  let F : Set Y := (B : Set Y) ∪ ⋃ j ∈ J, ((Y.basicOpen (z j) : Set Y))ᶜ
  have hF : IsClosed F := B.isClosed.union
    (isClosed_biUnion_finset fun j _ => (Y.basicOpen (z j)).isOpen.isClosed_compl)
  have hηF : genericPoint Y ∉ F := by
    rintro (h | h)
    · exact hη h
    · obtain ⟨j, hj, h⟩ := Set.mem_iUnion₂.1 h
      exact h (hηb j hj)
  obtain ⟨V, hyV, hVU, hV⟩ := exists_nbhd_specializes_of_isClosed F hF hηF hy
  refine ⟨V, hyV, fun y' hy' => ?_⟩
  have hy'U : y' ∈ U := hVU hy'
  refine ⟨hy'U, J.filter (fun j => w j ⤳ y'), Finset.filter_subset _ _,
    ⟨hc.frame, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j hj
    exact hc.val j (Finset.mem_filter.1 hj).1
  · intro j hj
    exact (Finset.mem_filter.1 hj).2
  · intro j hj
    exact hc.coheight j (Finset.mem_filter.1 hj).1
  · exact hc.inj.mono fun j hj => (Finset.mem_filter.1 hj).1
  · intro j hj
    exact hc.ord_self j (Finset.mem_filter.1 hj).1
  · intro j hj v hv hne
    have hjJ := (Finset.mem_filter.1 hj).1
    by_cases hb : v ∈ Y.basicOpen (z j)
    · exact hord0 j hjJ v hb
    by_cases hcv : Order.coheight v = 1
    · exact hc.ord_other j hjJ v (hV y' hy' v hv hcv (Or.inr (Set.mem_iUnion₂.2 ⟨j, hjJ, hb⟩))) hne
    · exact Scheme.ord_eq_zero_of_coheight_neq_one hcv _
  · intro v hv hcv
    constructor
    · intro hvB
      obtain ⟨j, hj, rfl⟩ := (hc.mem v (hV y' hy' v hv hcv (Or.inl hvB)) hcv).1 hvB
      exact ⟨j, Finset.mem_filter.2 ⟨hj, hv⟩, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      have hjJ := (Finset.mem_filter.1 hj).1
      exact (hc.mem _ (hc.spec j hjJ) hcv).2 ⟨j, hjJ, rfl⟩
  · intro j hj hb
    have hjJ := (Finset.mem_filter.1 hj).1
    have h0 := hord0 j hjJ (w j) ((Finset.mem_filter.1 hj).2.mem_open (Y.basicOpen (z j)).isOpen hb)
    rw [hc.ord_self j hjJ] at h0
    exact one_ne_zero h0

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymplecticLevelOfPulledBackObject
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

namespace GlobalTheory.HTSympCover

theorem isSympLev_of_sympCond_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ)
  (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (T : Over S) (t₁ : T.left ⟶ Sp (cycAway M))
  (o' : Obj b N (T.hom ≫ t)) (m : ObjMap o' o T.hom)
  (lv' : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T.left) ⟶ o'.A)) (lv : (Fin h ⊕ Fin h → ℤ) → (T ⟶ o.A)),
    (∀ a, (lv' a).left ≫ m.φ = (lv a).left) → SympCond o h M T t₁ lv →
      IsSympLev o'.P h M (zetaAway M) t₁ lv' := by
  intro p _ D R _ b N h M S t o T t₁ o' m lv' lv hα hlv
  obtain ⟨hadd, hkill, hgeo⟩ := hlv
  obtain ⟨ρ, eρ⟩ := GlobalTheory.HkSetPull.exists_equiv m.cart (𝟙_ (Over T.left))
  let j : Over.mk ((𝟙_ (Over T.left)).hom ≫ T.hom) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have key : ∀ a, ρ (lv' a) = j ≫ lv a := fun a => Over.OverMorphism.ext (by simp [eρ, hα, j])
  have dg := GlobalTheory.SiegelPull.diag_iso m.sq m.pol
  refine ⟨fun a c => ρ.injective ?_, fun a => ρ.injective ?_, fun k _ _ x β z hx hz => ?_⟩
  · rw [map_mul, key, key, key, hadd, MonObj.comp_mul]
  · rw [map_pow, key, ← MonObj.comp_pow, hkill, MonObj.comp_one, map_one]
  obtain ⟨hker, honto, hw⟩ := hgeo k x β z hx hz
  obtain ⟨σ, eσ⟩ := GlobalTheory.HkSetPull.exists_equiv m.cart (Over.mk x)
  have key' : ∀ a, σ (toUnit (Over.mk x) ≫ lv' a) = (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv a :=
    fun a => Over.OverMorphism.ext (by
      rw [eσ, Over.comp_left, Category.assoc, hα, Over.comp_left]
      congr 1)
  refine ⟨fun a => ?_, fun g hg => ?_, fun a c => ?_⟩
  · rw [← hker a, ← key', map_eq_one_iff _ σ.injective]
  · obtain ⟨a, ha⟩ := honto (σ g) (by rw [← map_pow, hg, map_one])
    exact ⟨a, σ.injective (by rw [key', ha])⟩
  · exact (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ o.A o'.A T.hom m.φ _ _ (pull_isLB o.isLB _)
      (pull_isLB o'.isLB _) m.cart dg (Over.mk x) M _ _ _ _ _ (eσ _) (eσ _)).2 (by rw [key', key']; exact hw a c)

end GlobalTheory.HTSympCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymplecticOfSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

open GlobalTheory.EighthPower GlobalTheory.CechPic GlobalTheory.MatrixBundle GlobalTheory.ZM

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SympDescent

theorem translFixed_of_pair {S : Scheme.{0}} {h M : ℕ} (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left)
    (H : IsSymmetricPair h A P) (ha : Out.RelAmple A (diagPull A P)) (x : 𝟙_ (Over S) ⟶ A) (hx : x ^ M = 1) :
    (M : ℤ) • cls (diagPull A P) (pull_isLB H.2.2.1 _) =
      (M : ℤ) • pull ((toUnit A ≫ x) * 𝟙 A).left (cls (diagPull A P) (pull_isLB H.2.2.1 _)) := by
  haveI := H.1.comm
  have hP := H.2.2.1
  have hb : IsSymBilin (cls P hP) := isSymBilin_of_gen hP (fun T x x' y =>
    (Biadditive.biadditive_of_triv_axes globalFns_holds S A (diagPull A P) H.1 (pull_isLB hP _) ha P hP
      H.2.2.2.1 H.2.2.2.2.1 T x x' y).1) H.2.2.2.2.2
  have d : ∀ f : A ⟶ A, pull f.left (cls (diagPull A P) (pull_isLB hP _)) = pairCls (cls P hP) f f := fun f =>
    (pull_pairCls (cls P hP) f (𝟙 _) (𝟙 _)).trans (by rw [Category.comp_id])
  have z : ∀ y : A ⟶ A, (M : ℤ) • pairCls (cls P hP) (toUnit A ≫ x) y = 0 := fun y => by
    have e := BilinCalc.map_prod_zpow (fun z => pairCls (cls P hP) z y) (fun a b => hb.mul _ a b y)
      (fun _ : Fin 1 => toUnit A ≫ x) fun _ => (M : ℤ)
    simp only [Finset.univ_unique, Finset.prod_const, Finset.card_singleton, pow_one, Finset.sum_const, one_smul,
      zpow_natCast] at e
    rw [← e, ← MonObj.comp_pow, hx, MonObj.comp_one]
    exact one_left (hb.mul _) y
  rw [d, hb.mul, hb.symm _ (𝟙 A) (_ * _), hb.mul, smul_add, smul_add, z, z, zero_add, zero_add]
  rfl

theorem units_map_comp_appTop {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (u : Γ(Z, ⊤)ˣ) :
    Units.map (f ≫ g).appTop.hom.toMonoidHom u =
      Units.map f.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom u) :=
  Units.ext (by simp [Scheme.Hom.comp_appTop]; rfl)

theorem isSymplectic_of_subring : ∀ (h M : ℕ) (B R : Type) [CommRing B] [CommRing R] (ζ : Bˣ) (R₁ : Subring R) (s₁ : Sp R₁ ⟶ Sp B) (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (lv : Std h M → (𝟙_ (Over (Sp R)) ⟶ A)) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (lv₁ : Std h M → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), 0 < M → ζ ^ M = 1 → IsUnit (M : R₁) → IsSymmetricPair h A₁ P₁ → IsPrincipal A₁ P₁ → IsLevel A₁ lv₁ → P.IsLB → IsPullbackTriple A P lv A₁ P₁ lv₁ (spMap R₁.subtype) → IsSymplectic ζ (spMap R₁.subtype ≫ s₁) A P lv → IsSymplectic ζ s₁ A₁ P₁ lv₁ := by
  intro h M B R _ _ ζ R₁ s₁ A _ P lv A₁ _ P₁ lv₁ hM hζ hu H₁ H₂ H₃ hPR Hpb Hs
  haveI := H₁.1.comm
  have hP := H₁.2.2.1
  have hD : (diagPull A₁ P₁).IsLB := pull_isLB hP _
  have z₀ : lv₁ 0 = 1 := by
    have e := H₃.1 0 0
    rw [add_zero] at e
    exact left_eq_mul.1 e
  have tors : ∀ a, lv₁ a ^ M = 1 := fun a => by
    have e : ∀ n : ℕ, lv₁ (n • a) = lv₁ a ^ n := fun n => by
      induction n with
      | zero => rw [zero_smul, pow_zero, z₀]
      | succ n ih => rw [succ_nsmul, H₃.1, ih, pow_succ]
    rw [← e, show M • a = 0 by ext i <;> simp, z₀]
  have th : ∀ a (p : (𝟙_ (Over (Sp R₁))).left), ∃ V : (𝟙_ (Over (Sp R₁))).left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp A₁ (diagPull A₁ P₁) M (Out.overRes V), θ.pt = Out.overResι V ≫ lv₁ a := fun a p => by
    let T := Out.overRes (T := 𝟙_ (Over (Sp R₁))) ⊤
    have hT : (Out.thetaLB A₁ (diagPull A₁ P₁) M (Out.overResι ⊤ ≫ lv₁ a)).IsLB := LB.isLB_linComb hD _ _
    obtain ⟨t, ht⟩ := (cls_eq_zero_iff hT).1 (by
      unfold Out.thetaLB at hT ⊢
      rw [cls_linComb hD, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_smul]
      have e : Out.translPt A₁ (Out.overResι ⊤ ≫ lv₁ a) = snd T A₁ ≫ ((toUnit A₁ ≫ lv₁ a) * 𝟙 A₁) := by
        rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc, Out.translPt, ← Hom.mul_def, ← Category.assoc,
          toUnit_unique (fst _ _ ≫ _) (toUnit _)]
      rw [e, Over.comp_left, pull_comp, ← map_zsmul, ← map_zsmul,
        ← GlobalTheory.SympDescent.translFixed_of_pair A₁ P₁ H₁ H₂.1 (lv₁ a) (tors a), add_neg_cancel])
    exact ⟨⊤, trivial, ⟨_, t, ht⟩, rfl⟩
  obtain ⟨φ, φ₂, pb, s₁', s₂', iso, hl⟩ := Hpb
  have hdi : LBIso (diagPull A P) ((diagPull A₁ P₁).pull φ) := GlobalTheory.SiegelPull.diag_iso ⟨s₁', s₂'⟩ iso
  have hL : (diagPull A P).IsLB := pull_isLB hPR _

  have inj : Function.Injective ((𝟙_ (Over (Sp R))).hom ≫ spMap R₁.subtype).appTop.hom := by
    have u₁ : (𝟙_ (Over (Sp R))).hom = 𝟙 _ := rfl
    rw [u₁, Category.id_comp]
    have k : ∀ z, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((spMap R₁.subtype).appTop.hom z) =
        ((Scheme.ΓSpecIso (CommRingCat.of R₁)).hom.hom z : R) := fun z => by
      have e := congrArg (fun q => q.hom z) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom R₁.subtype))
      first
        | exact e
        | (simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, Subring.subtype_apply] at e; exact e)
    intro x y hxy
    have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom hxy
    rw [k, k] at h2
    have h3 := congrArg (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (Subtype.val_injective h2)
    simpa using h3
  intro a b
  obtain ⟨c, hc⟩ := CommutatorPairing.exists_weilIs globalFns_holds H₁.1 hD (th a) (th b)
  let X' : Over (Sp R₁) := Over.mk ((𝟙_ (Over (Sp R))).hom ≫ spMap R₁.subtype)
  have ex : ∀ a, (toUnit X' ≫ lv₁ a).left = (lv a).left ≫ φ := fun a => by
    rw [Over.comp_left, Over.toUnit_left, hl a]
    exact Category.assoc _ _ _
  have w := (weilIs_grpPullback_of_comm (Sp R₁) (Sp R) A₁ A (spMap R₁.subtype) φ (diagPull A₁ P₁) (diagPull A P)
    hD hL pb hdi (𝟙_ (Over (Sp R))) M (lv a) (lv b) (toUnit X' ≫ lv₁ a) (toUnit X' ≫ lv₁ b) _ (ex a) (ex b)).1 (Hs a b)
  have w' := CommPairing.weilIs_pull globalFns_holds H₁.1 hD (toUnit X') hc
  have q := CommutatorPairing.weilIs_unique globalFns_holds H₁.1 hD w' w
  have u₂ : (𝟙_ (Over (Sp R₁))).hom = 𝟙 _ := rfl
  have hinj : Function.Injective (Units.map (toUnit X').left.appTop.hom.toMonoidHom) := fun u v huv =>
    Units.ext (inj (by
      have := congrArg Units.val huv
      simp only [Units.coe_map, MonoidHom.coe_coe, Over.toUnit_left] at this
      exact this))
  have q₂ : Units.map (toUnit X').left.appTop.hom.toMonoidHom
      (Units.map ((𝟙_ (Over (Sp R₁))).hom ≫ s₁).appTop.hom.toMonoidHom (unitOn (ζ ^ (2 * stdForm a b).val))) =
      Units.map ((𝟙_ (Over (Sp R))).hom ≫ spMap R₁.subtype ≫ s₁).appTop.hom.toMonoidHom
        (unitOn (ζ ^ (2 * stdForm a b).val)) := by
    rw [← GlobalTheory.SympDescent.units_map_comp_appTop, Over.toUnit_left, u₂, Category.id_comp]
    rfl
  rw [← hinj (q.trans q₂.symm)]
  exact hc

end GlobalTheory.SympDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetCalculusStatement
section
set_option autoImplicit false
noncomputable section
open GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical

namespace GlobalTheory.JetCalcPf

end GlobalTheory.JetCalcPf

namespace GlobalTheory.JetCalcPf

variable {I : Type} [Fintype I] {n : ℕ}

end GlobalTheory.JetCalcPf
end
end

