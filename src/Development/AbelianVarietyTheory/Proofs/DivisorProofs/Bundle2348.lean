module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0117
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2263
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianSchemeAway
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureStalkFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0095

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisConjugateGenericBundleIso
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem exists_inv (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (ρ : R →+* R') (hρ : Function.Injective ρ) (D : DegData R (maximalIdeal R))
    (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R')))
    (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U')
    (G : Over (Sp R)) [GrpObj G] (β : G'.left ⟶ G.left) (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ) :
    (∀ σ, a.act σ ≫ β = β) → ∀ σ : Gal ρ, ∃ ψ : pullback G'.hom (jK R') ⟶ pullback G'.hom (jK R'),
      ψ ≫ genMap hρ β hβ = genMap hρ β hβ ∧
      ψ ≫ pullback.snd G'.hom (jK R') = pullback.snd G'.hom (jK R') ≫ spMap (fracAut σ.1).toRingHom ∧
      LBIso (U'.LG.L.pull (pullback.fst G'.hom (jK R'))) ((U'.LG.L.pull (pullback.fst G'.hom (jK R'))).pull ψ) := by
  intro hinv σ
  have h₁ : G'.hom ≫ spMap (Gal.hom σ) = a.act σ ≫ G'.hom := ((a.cart σ).1.w).symm
  have h₂ : jK R' ≫ spMap (Gal.hom σ) = spMap (fracAut σ.1).toRingHom ≫ jK R' := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact (fracAut_algebraMap σ.1 x).symm
  let ψ := pullback.map G'.hom (jK R') G'.hom (jK R') (a.act σ) (spMap (fracAut σ.1).toRingHom) (spMap (Gal.hom σ)) h₁ h₂
  have hψ₁ : ψ ≫ pullback.fst G'.hom (jK R') = pullback.fst G'.hom (jK R') ≫ a.act σ := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ pullback.snd G'.hom (jK R') = pullback.snd G'.hom (jK R') ≫ spMap (fracAut σ.1).toRingHom :=
    pullback.lift_snd _ _ _
  have hfr : spMap (fracAut σ.1).toRingHom ≫ spMap (fracMap ρ hρ) = spMap (fracMap ρ hρ) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact fracAut_fracMap hρ σ x
  refine ⟨ψ, ?_, hψ₂, ?_⟩
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, genMap_fst, ← Category.assoc, hψ₁, Category.assoc, hinv σ]
    · rw [Category.assoc, genMap_snd, ← Category.assoc, hψ₂, Category.assoc, hfr]
  · obtain ⟨h, bc, hbc, hU, -⟩ := a.unif σ
    obtain ⟨wL, hwL, -⟩ := hU.lg
    have hL : LBIso U'.LG.L (U'.LG.L.pull (a.act σ)) := by
      rw [← hbc]
      exact ⟨wL, hwL⟩
    have hL₀ := U'.LG.isLB
    refine LBIso.trans (pull_isLB hL₀ _) (pull_isLB hL₀ _) (pull_isLB (pull_isLB hL₀ _) _)
      (GlobalTheory.GenSpread.lbIso_pull_of_lbIso hL (pullback.fst G'.hom (jK R')) rfl) ?_
    exact GlobalTheory.GenSpread.lbIso_pull_pull hL₀ ψ hψ₁.symm

end GlobalTheory.Mum.GenDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorOfTheoremOfCubeTenPoints
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.CubeGen

section
variable {X Y Z : Scheme.{0}} {L : LB X}

def Triv (L : LB X) (Y : Scheme.{0}) (F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = F U h

theorem Triv.mul {F F' : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : Triv L Y F) (h' : Triv L Y F') :
    Triv L Y (fun U _ g => F U g * F' U g) := by
  obtain ⟨K, _, φ, ε, t, ht, e⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', e'⟩ := h'
  exact ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L φ ε φ' ε' t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun U _ g => (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (e U g) (e' U g))⟩

theorem Triv.inv {F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : Triv L Y F) :
    Triv L Y (fun U _ g => (F U g)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, e⟩ := h
  refine ⟨K, inferInstance, _, _, LB.invGen L φ ε t, DVR.invGen_isGen _ _ _ _ ht, fun U _ g => ?_⟩
  simp only [zpow_neg, Finset.prod_inv_distrib, e U g]

theorem Triv.pull {F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : Triv L Y F) (r : Z ⟶ Y) :
    Triv L Z (fun U _ g => F U (fun ψ => g (r ≫ ψ))) := by
  obtain ⟨K, _, φ, ε, t, ht, e⟩ := h
  exact ⟨K, inferInstance, _, _, LB.pullGen L φ ε t r, DVR.pullGen_isGen _ _ _ _ ht _,
    fun U _ g => e U (fun ψ => g (r ≫ ψ))⟩

theorem Triv.exists_gen (hL : L.IsLB) {F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : Triv L Y F)
    (f : Y ⟶ X) (hf : ∀ (U : Type) [CommGroup U] (g : (Y ⟶ X) → U), F U g = g f) :
    ∃ t : LB.Gen (L.pull f), t.IsGen := by
  obtain ⟨K, _, φ, ε, t, ht, e⟩ := h
  obtain ⟨t', ht', -⟩ := Geo.Tor.exists_gen hL (φ' := fun _ : PUnit => f) (ε' := fun _ => 1)
    (fun U _ g => by rw [e, hf]; simp) t ht
  exact ⟨t', ht'⟩

theorem triv_of_sec (θ : L.Sec) (f : Y ⟶ X) (hf : ∀ y, f y ∈ secNz θ) : Triv L Y (fun _ _ g => g f) := by
  have hu : ∀ j, IsUnit ((SpecialFibreGenerator.secAlong θ f).f j) := fun j =>
    Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hf y)
      obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (SpecialFibreGenerator.mem_nonzeroLocus_secAlong θ f hi)
      exact (Y.mem_basicOpen _ y hy).1 (SpecialFibreGenerator.mem_basicOpen_of_chart _ hy hk)
  exact ⟨Fin 1, inferInstance, _, _, ⟨fun j => (hu j).unit⟩,
    fun i j => Units.ext ((SpecialFibreGenerator.secAlong θ f).compat i j), fun U _ g => by simp⟩

end

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {T : Over S}

theorem triv_cub (c : CubicalStr G L) (x x' y : T ⟶ G) : Triv L.L T.left (fun _ _ h =>
    h (x * x' * y).left * (h (x * x').left)⁻¹ * (h (x * y).left)⁻¹ * (h (x' * y).left)⁻¹ * h x.left * h x'.left *
        h y.left * (h (1 : T ⟶ G).left)⁻¹) :=
  ⟨thK, inferInstance, _, _, LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift x (lift x' y)).left,
    DVR.pullGen_isGen _ _ _ _ c.isGen _, fun _ _ h => prod_cub x x' y h⟩

theorem triv_one (L : RigLB G) (T : Over S) : Triv L.L T.left (fun _ _ h => h (1 : T ⟶ G).left) :=
  ⟨PUnit, inferInstance, _, _, LB.pullGen L.L (fun _ => eSec G) (fun _ => 1) L.rig T.hom,
    DVR.pullGen_isGen _ _ _ _ L.rigGen _, fun _ _ h => by rw [GlobalTheory.UU.one_left]; simp⟩

end GlobalTheory.Mum.CubeGen

namespace GlobalTheory.Mum

open CubeGen

theorem exists_gen_of_cubeTen (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G)
    (θ : P.L.L.Sec) (T : Over S) (x a b c : T ⟶ G) (W : T.left.Opens)
    (hW : ∀ f ∈ cubeTen x a b c, W ≤ f.left ⁻¹ᵁ secNz θ) :
    ∃ t : LB.Gen (P.L.L.pull (W.ι ≫ x.left)), t.IsGen := by
  have s : ∀ f ∈ cubeTen x a b c, Triv P.L.L W (fun _ _ g => g (W.ι ≫ f.left)) := fun f hf =>
    triv_of_sec θ _ fun y => hW f hf y.2
  have s₁ := s (x * a) (by simp [cubeTen])
  have s₂ := s (x * a⁻¹) (by simp [cubeTen])
  have s₃ := s a (by simp [cubeTen])
  have s₄ := s a⁻¹ (by simp [cubeTen])
  have s₅ := s (x * b) (by simp [cubeTen])
  have s₆ := s (x * c) (by simp [cubeTen])
  have s₇ := s (x * (b * c)⁻¹) (by simp [cubeTen])
  have s₈ := s b (by simp [cubeTen])
  have s₉ := s c (by simp [cubeTen])
  have s₀ := s (b * c)⁻¹ (by simp [cubeTen])
  have e := (triv_one P.L T).pull W.ι
  have c₁ := (triv_cub P.c x a a⁻¹).pull W.ι
  have c₂ := (triv_cub P.c x b c).pull W.ι
  have c₃ := (triv_cub P.c x (b * c) (b * c)⁻¹).pull W.ι
  have t₂ := ((((c₁.mul s₁).mul s₂).mul s₃.inv).mul s₄.inv)
  have t₃ := (((((((c₂.mul c₃).mul s₅).mul s₆).mul s₇).mul s₈.inv).mul s₉.inv).mul s₀.inv)
  refine ((t₃.mul t₂.inv).mul e).exists_gen P.L.isLB _ fun U _ g => ?_
  simp only [mul_inv_cancel_right, mul_inv_cancel, _root_.mul_assoc x b c]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransferThroughTensorIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.TensGen

theorem exists_flat {X X' Y : Scheme.{0}} (M : LB X) {I K : Type} [Fintype I] [Fintype K] (F : I → (X' ⟶ X))
    (e : I → ℤ) (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb M (fun p : K × I => φ' p.1 ≫ F p.2) (fun p => ε p.1 * e p.2))) (ht : t.IsGen) :
    ∃ t₂ : LB.Gen (LB.LinComb (LB.LinComb M F e) φ' ε), t₂.IsGen ∧
      ∀ (jj : K → I → M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ LB.wchart (LB.LinComb M F e) φ' jj →
        gm r z _ (t₂.s jj) = gm r z (LB.wchart M (fun p : K × I => φ' p.1 ≫ F p.2) (fun p => jj p.1 p.2))
          (t.s (fun p => jj p.1 p.2)) := by
  have le : ∀ jj : K → I → M.ι, LB.wchart (LB.LinComb M F e) φ' jj ≤
      LB.wchart M (fun p : K × I => φ' p.1 ≫ F p.2) (fun p => jj p.1 p.2) := fun jj y hy =>
    Set.mem_iInter.2 fun p => by
      have h₁ : (F p.2) ((φ' p.1) y) ∈ M.U (jj p.1 p.2) := Set.mem_iInter.1 (Set.mem_iInter.1 hy p.1) p.2
      exact h₁
  have v : ∀ (jj : K → I → M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ LB.wchart (LB.LinComb M F e) φ' jj →
      gm r z _ (res (le jj) (t.s (fun p => jj p.1 p.2))) =
        gm r z (LB.wchart M (fun p : K × I => φ' p.1 ≫ F p.2) (fun p => jj p.1 p.2)) (t.s (fun p => jj p.1 p.2)) :=
    fun jj Z r z hz => gm_res r z _ hz _
  refine ⟨⟨fun jj => res (le jj) (t.s (fun p => jj p.1 p.2))⟩, fun i j => unit_ext fun y hy => ?_, v⟩
  rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy]
  change gm (𝟙 Y) y _ (res (le i) _) = _ * gm (𝟙 Y) y _ (res (le j) _)
  rw [v i _ (𝟙 Y) y hy.1, v j _ (𝟙 Y) y hy.2, gen_trans ht (𝟙 Y) y (le i hy.1) (le j hy.2)]
  congr 1
  refine Eq.trans ?_ (gm_linComb (LB.LinComb M F e) φ' ε (𝟙 Y) y i j hy.1 hy.2).symm
  have b : ∀ a, gm (𝟙 Y ≫ φ' a) y ((LB.LinComb M F e).U (i a) ⊓ (LB.LinComb M F e).U (j a))
      ((LB.LinComb M F e).g (i a) (j a)) = ∏ k, gm ((𝟙 Y ≫ φ' a) ≫ F k) y (M.U (i a k) ⊓ M.U (j a k)) (M.g (i a k) (j a k)) ^ e k :=
    fun a => gm_linComb M F e (𝟙 Y ≫ φ' a) y (i a) (j a) (Set.mem_iInter.1 hy.1 a) (Set.mem_iInter.1 hy.2 a)
  simp only [b, trF, Fintype.prod_prod_type, ← Finset.prod_zpow, ← zpow_mul, Category.assoc]
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun k _ => ?_
  rw [mul_comm]

theorem exists_gen_transfer : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) {Y : Scheme.{0}} {K : Type} [Fintype K] (φ' : K → (Y ⟶ D'.P.A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb D.P.L (fun p : K × ((Fin r × Fin r) × Fin 4) => φ' p.1 ≫ tensφ T.pr p.2) (fun p => ε p.1 * tensε W p.2))), t.IsGen → ∃ t' : LB.Gen (LB.LinComb D'.P.L φ' ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → (∏ a, gm (q ≫ φ' a) z _ (T.w.s (fun k => J ((q ≫ φ' a) ≫ tensφ T.pr k), J' (q ≫ φ' a))) ^ ε a) * val t' q z J' = val t q z J := by
  intro R _ _ D D' r W T Y K _ φ' ε t ht
  obtain ⟨t₂, ht₂, h₂⟩ := exists_flat D.P.L (tensφ T.pr) (tensε W) φ' ε t ht
  have hA : (LB.LinComb (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) φ' ε).IsLB :=
    LB.isLB_linComb (LB.isLB_linComb D.P.isLB _ _) _ _
  have hB : (LB.LinComb D'.P.L φ' ε).IsLB := LB.isLB_linComb D'.P.isLB _ _
  obtain ⟨t', ht', hv⟩ := GlobalTheory.WtTower.exists_gen_of_iso hA hB (isoInv (LB.linCombIso T.w φ' ε))
    (isoInv_isGen (DVR.linCombIso_isGen T.w T.w_gen φ' ε)) t₂ ht₂
  refine ⟨t', ht', fun Z q z J J' hJ hJ' => ?_⟩
  let i : K → (Fin r × Fin r) × Fin 4 → D.P.L.ι := fun a k => J ((q ≫ φ' a) ≫ tensφ T.pr k)
  let j : K → D'.P.L.ι := fun a => J' (q ≫ φ' a)
  have hi : q z ∈ LB.wchart (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) φ' i :=
    Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun k => hJ ((q ≫ φ' a) ≫ tensφ T.pr k)
  have hj : q z ∈ LB.wchart D'.P.L φ' j := hJ'.mem φ' q
  have e1 := hv Z q z j i hj hi
  have hm : q z ∈ (LB.LinComb D'.P.L φ' ε).U j ⊓ (LB.LinComb (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) φ' ε).U i :=
    ⟨hj, hi⟩
  have hm' : q z ∈ (LB.div (LB.LinComb (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) φ' ε) (LB.LinComb D'.P.L φ' ε)).U (i, j) :=
    ⟨hi, hj⟩
  have e2 : gm q z ((LB.LinComb D'.P.L φ' ε).U j ⊓ (LB.LinComb (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) φ' ε).U i)
      ((isoInv (LB.linCombIso T.w φ' ε)).s (j, i)) =
      (∏ a, gm (q ≫ φ' a) z _ (T.w.s (i a, j a)) ^ ε a)⁻¹ :=
    (map_inv _ _).trans (congrArg (·⁻¹) ((gm_res q z _ hm _).trans
      (GlobalTheory.WtTower.gm_linCombIso T.w φ' ε (i, j) q z hm')))
  have e3 : gm q z _ (t₂.s i) = val t q z J :=
    (h₂ i Z q z hi).trans (val_of t q z J _ fun p => by simp only [i, Category.assoc]).symm
  change _ * gm q z _ (t'.s j) = _
  rw [e1, e2, e3]
  exact mul_inv_cancel_left _ _

end GlobalTheory.TensGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointFactorOfInjectiveBaseMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_fractionRing_map_comp_eq {R W B : Type} [CommRing R] [IsDomain R] [CommRing W] [IsDomain W] [CommRing B]
    (φ : R →+* W) (hφ : Function.Injective φ) (c : R →+* B) (a : B →+* FractionRing R) (b : B →+* FractionRing W)
    (ha : Function.Injective a) (hac : a.comp c = algebraMap R (FractionRing R))
    (hbc : b.comp c = (algebraMap W (FractionRing W)).comp φ) :
    ∃ ψ : FractionRing R →+* FractionRing W,
      ψ.comp (algebraMap R (FractionRing R)) = (algebraMap W (FractionRing W)).comp φ ∧ ψ.comp a = b := by
  have hinj : Function.Injective ((algebraMap W (FractionRing W)).comp φ) :=
    (IsFractionRing.injective W (FractionRing W)).comp hφ
  refine ⟨IsFractionRing.lift hinj, ?_, ?_⟩
  · ext r
    simp only [RingHom.comp_apply, IsFractionRing.lift_algebraMap]
  · ext x
    obtain ⟨r, r', hr', h⟩ := IsFractionRing.div_surjective (A := R) (a x)
    have h0 : algebraMap R (FractionRing R) r' ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hr'
    have hac' : ∀ y, a (c y) = algebraMap R (FractionRing R) y := fun y => RingHom.congr_fun hac y
    have hbc' : ∀ y, b (c y) = ((algebraMap W (FractionRing W)).comp φ) y := fun y => RingHom.congr_fun hbc y
    have h1 : x * c r' = c r := by
      apply ha
      rw [map_mul, hac', hac', ← h, div_mul_cancel₀ _ h0]
    have h2 : ((algebraMap W (FractionRing W)).comp φ) r' ≠ 0 := by
      intro h3
      exact nonZeroDivisors.ne_zero hr' (hinj (h3.trans (map_zero _).symm))
    rw [RingHom.comp_apply, ← h, map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap,
      div_eq_iff h2, ← hbc', ← hbc', ← map_mul, h1]

theorem Modif.exists_generic_factor : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W), Function.Injective φ → ∀ ξ : Sp W ⟶ M.S, ξ ≫ M.π = spMap φ → ∃ ψ : FractionRing R →+* FractionRing W, ψ.comp (algebraMap R (FractionRing R)) = (algebraMap W (FractionRing W)).comp φ ∧ spMap ψ ≫ M.gp = jK W ≫ ξ := by
  intro R _ _ M W _ _ φ hφ ξ hξ
  haveI := M.integral
  haveI := M.dominant
  let s : M.S := (jK W ≫ ξ) (IsLocalRing.closedPoint (FractionRing W))
  obtain ⟨B, f, hf, hs, -⟩ := M.S.exists_affine_mem_range_and_range_subset (x := s) (U := ⊤) trivial
  have hb : Set.range (jK W ≫ ξ) ⊆ Set.range f := by
    rintro _ ⟨y, rfl⟩
    have : y = IsLocalRing.closedPoint (FractionRing W) := Subsingleton.elim (α := PrimeSpectrum (FractionRing W)) _ _
    rw [this]; exact hs
  have ha : Set.range M.gp ⊆ Set.range f := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := M.gp.denseRange.exists_mem_open f.isOpenEmbedding.isOpen_range ⟨s, hs⟩
    have : y = z := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
    rw [this]; exact hz
  obtain ⟨a, ha'⟩ := Spec.map_surjective (IsOpenImmersion.lift f M.gp ha)
  obtain ⟨b, hb'⟩ := Spec.map_surjective (IsOpenImmersion.lift f (jK W ≫ ξ) hb)
  obtain ⟨c, hc'⟩ := Spec.map_surjective (f ≫ M.π)
  have e1 : Spec.map a ≫ f = M.gp := by rw [ha', IsOpenImmersion.lift_fac]
  have e2 : Spec.map b ≫ f = jK W ≫ ξ := by rw [hb', IsOpenImmersion.lift_fac]
  have hac : c ≫ a = CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hc', ← Category.assoc, e1, M.gp_π]
  have hbc : c ≫ b = CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap W (FractionRing W)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hc', ← Category.assoc, e2, Category.assoc, hξ, Spec.map_comp]
  have hred : IsReduced (Spec B) := isReduced_of_isOpenImmersion f
  have hred' : _root_.IsReduced B := (affine_isReduced_iff B).1 hred
  have hdom : IsDominant (Spec.map a) := by
    haveI : IsDominant (Spec.map a ≫ f) := e1 ▸ M.dominant
    exact IsDominant.of_comp_of_isOpenImmersion _ f
  have hainj : Function.Injective a.hom := by
    have := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical a.hom).1 hdom.1
    rw [nilradical_eq_zero] at this
    exact (RingHom.injective_iff_ker_eq_bot _).2 (le_bot_iff.1 this)
  obtain ⟨ψ, h1, h2⟩ := exists_fractionRing_map_comp_eq φ hφ c.hom a.hom b.hom hainj
    (congrArg CommRingCat.Hom.hom hac) (congrArg CommRingCat.Hom.hom hbc)
  refine ⟨ψ, h1, ?_⟩
  have h3 : a ≫ CommRingCat.ofHom ψ = b := by
    ext1; exact h2
  rw [← e1, ← e2, ← h3, Spec.map_comp, Category.assoc]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointOfLiesOverGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

namespace GlobalTheory.Mum

theorem eq_gp_of_lies_over_bot {R : Type} [CommRing R] [IsDomain R] {S : Scheme.{0}} [IsReduced S] (π : S ⟶ Sp R)
    (gp : Sp (FractionRing R) ⟶ S) (hgp : gp ≫ π = jK R) (hd : IsDominant gp)
    {B : CommRingCat} (e₀ : Spec B ⟶ S) [he₀ : IsOpenImmersion e₀] (P : Spec B)
    (hP : π (e₀ P) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)) (k : Sp (FractionRing R)) : e₀ P = gp k := by
  have hsub : Set.range gp ⊆ Set.range e₀ := by
    obtain ⟨a, ha⟩ := hd.denseRange.exists_mem_open e₀.isOpenEmbedding.isOpen_range ⟨e₀ P, P, rfl⟩
    rintro _ ⟨x, rfl⟩
    rwa [Subsingleton.elim x a]
  set g' := IsOpenImmersion.lift e₀ gp hsub with hg'
  have hfac : g' ≫ e₀ = gp := IsOpenImmersion.lift_fac _ _ _
  set g := Spec.preimage g' with hg
  set ρ := Spec.preimage (e₀ ≫ π) with hρ
  have hgg : Spec.map g = g' := Spec.map_preimage _
  have hρρ : Spec.map ρ = e₀ ≫ π := Spec.map_preimage _
  have hcomp : ρ ≫ g = CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hgg, hρρ, ← Category.assoc, hfac, hgp]
  have hcomp' : ∀ r, g.hom (ρ.hom r) = algebraMap R (FractionRing R) r := fun r => by
    have := congrArg (fun f => f.hom r) hcomp
    simpa using this
  have hden : DenseRange g' := by
    rw [denseRange_iff_closure_range, e₀.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
      ← Set.range_comp]
    have : (e₀ ∘ g') = gp := by funext x; rw [← hfac]; rfl
    rw [this, hd.denseRange.closure_range, Set.preimage_univ]
  have hred : _root_.IsReduced B := by
    have : IsReduced (Spec B) := isReduced_of_isOpenImmersion e₀
    exact (affine_isReduced_iff B).1 this
  have hinj : Function.Injective g.hom := by
    have h1 : DenseRange (PrimeSpectrum.comap g.hom) := by rw [← hgg] at hden; exact hden
    have h2 := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical g.hom).1 h1
    rw [nilradical_eq_zero] at h2
    exact (RingHom.injective_iff_ker_eq_bot _).2 (le_bot_iff.1 h2)
  have hPρ : Ideal.comap ρ.hom P.asIdeal = ⊥ := by
    have h2 : (Spec.map ρ) P = π (e₀ P) := by rw [hρρ]; rfl
    rw [hP] at h2
    exact congrArg PrimeSpectrum.asIdeal h2
  have hPb : P.asIdeal = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, s, hs, hxs⟩ := IsFractionRing.div_surjective (A := R) (g.hom x)
    have hs0 : algebraMap R (FractionRing R) s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    have h0 : ρ.hom s * x - ρ.hom a = 0 := by
      apply hinj
      rw [map_sub, map_mul, hcomp', hcomp', ← hxs, map_zero, mul_div_cancel₀ _ hs0, sub_self]
    have ha : a ∈ Ideal.comap ρ.hom P.asIdeal := by
      rw [Ideal.mem_comap, ← sub_eq_zero.1 h0]
      exact P.asIdeal.mul_mem_left _ hx
    rw [hPρ, Ideal.mem_bot] at ha
    have hx0 : g.hom x = 0 := by rw [← hxs, ha, map_zero, zero_div]
    rw [Ideal.mem_bot]
    exact hinj (by rw [hx0, map_zero])
  rw [← hfac]
  show e₀ P = e₀ (g' k)
  congr 1
  rw [← hgg]
  apply PrimeSpectrum.ext
  show P.asIdeal = Ideal.comap g.hom k.asIdeal
  have hk : k.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ k.isPrime
  rw [hPb, hk, Ideal.comap_bot_of_injective _ hinj]

theorem modif_pt_over_gen : ∀ (R : Type) [CommRing R] [IsDomain R] (M' : Modif R) (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W) (ξ : Sp W ⟶ M'.S), Function.Injective φ → ξ ≫ M'.π = spMap φ → ∃ (w : Sp W) (k : Sp (FractionRing R)), ξ w = M'.gp k := by
  intro R _ _ M' W _ _ φ ξ hφ hξ
  have : IsReduced M'.S := by have := M'.integral; infer_instance
  let w : Sp W := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W)
  let k : Sp (FractionRing R) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
  refine ⟨w, k, ?_⟩
  let j := M'.S.affineCover.idx (ξ w)
  have hoi : IsOpenImmersion (M'.S.affineCover.f j) := M'.S.affineCover.map_prop j
  obtain ⟨P, hP⟩ := M'.S.affineCover.covers (ξ w)
  rw [← hP]
  refine eq_gp_of_lies_over_bot (he₀ := hoi) M'.π M'.gp M'.gp_π M'.dominant (M'.S.affineCover.f j) P ?_ k
  refine (congrArg M'.π hP).trans ?_
  have h1 : M'.π (ξ w) = (spMap φ) w := by rw [← hξ]; rfl
  rw [h1]
  apply PrimeSpectrum.ext
  show Ideal.comap φ ⊥ = ⊥
  exact Ideal.comap_bot_of_injective _ hφ

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralClosureFractionFiniteNormalCover
section
open AlgebraicGeometry CategoryTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Geo.Tor


open GlobalTheory.Poinc.FinPts in
theorem GlobalTheory.Poinc.exists_div_integralClosure_of_mem_O : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₂.Z → IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ (z₁ : M₁.Z) (z₂ : M₂.Z), q z₂ = z₁ → letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra; ∀ x ∈ M₂.O z₂, ∃ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, ∃ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 ∧ s⁻¹ ∈ M₂.O z₂ ∧ x = b / s := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ M₁ M₂ q _ hF hg z₁ z₂ hq x hx
  letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra
  have halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x) := fun _ => rfl
  haveI := hF
  obtain ⟨U, hU, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : M₁.Z.Opens)) (x := z₁) trivial
  have hz₂ : z₂ ∈ q ⁻¹ᵁ U := show q z₂ ∈ U by rw [hq]; exact hz
  obtain ⟨c, hc, d, hd, hd0, hdinv, e⟩ := _root_.GlobalTheory.Poinc.exists_eq_div_of_mem_O_affine _ _ M₂ _ (hU.preimage q) z₂ hz₂ x hx
  exact ⟨c, (mem_integralClosure_iff _ _).2 (isIntegral_of_mem_ringOn hF hg halg hU hz hc), d,
    (mem_integralClosure_iff _ _).2 (isIntegral_of_mem_ringOn hF hg halg hU hz hd), hd0, hdinv, e⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLocalHomAdicCompletionExtendStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isLocalHom_adicCompletion_extension_apply : ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (V : Type) [CommRing V] [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V] (ψ : O →+* V), IsLocalHom ψ → ∃ ev₀ : AdicCompletion (maximalIdeal O) O →+* V, IsLocalHom ev₀ ∧ ∀ a, ev₀ (algebraMap O _ a) = ψ a := by
  first | exact @GlobalTheory.exists_isLocalHom_adicCompletion_extend | exact GlobalTheory.exists_isLocalHom_adicCompletion_extend | (intros; apply GlobalTheory.exists_isLocalHom_adicCompletion_extend <;> assumption)
end

