module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdAd
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0158
public import Development.WeilBound.CoreStatements.HodgeTatePoints.GermCompOneAssocOfConstantCoeffZero

@[expose] public section

namespace PositivityTheory.Xgn.JetKernelRank

section Weyl
open Module

variable {k C : Type} [Field k] [CommRing C] [Algebra k C]

end Weyl

section Hopf
open Module TensorProduct Coalgebra Bialgebra WithConv

variable {k H : Type} [Field k] [CommRing H] [HopfAlgebra k H]

noncomputable def inv (D : H →ₗ[k] k) : H →ₗ[k] H :=
  (TensorProduct.rid k H).toLinearMap ∘ₗ D.lTensor H ∘ₗ comul


end Hopf

section Coef
open TensorProduct TrivSqZeroExt

variable {k : Type} [Field k] {r : ℕ} {B : Type} [CommRing B] [Algebra k B]

abbrev Sq (k : Type) [Field k] (r : ℕ) : Type := TrivSqZeroExt k (Fin r → k)


variable (k r B) in
noncomputable def c0 : B ⊗[k] Sq k r →ₐ[k] B :=
  (Algebra.TensorProduct.rid k k B).toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id k B) (fstHom k k _))

noncomputable def co (i : Fin r) : B ⊗[k] Sq k r →ₗ[k] B :=
  (TensorProduct.rid k B).toLinearMap ∘ₗ (LinearMap.proj i ∘ₗ sndHom k (Fin r → k)).lTensor B

@[simp] theorem constant_term_tensor (b : B) (x : Sq k r) : c0 k r B (b ⊗ₜ[k] x) = x.fst • b := by simp [c0]

@[simp] theorem co_tmul (i : Fin r) (b : B) (x : Sq k r) : co i (b ⊗ₜ[k] x) = x.snd i • b := by simp [co]

theorem co_mul (i : Fin r) (s t : B ⊗[k] Sq k r) : co i (s * t) = c0 k r B s * co i t + co i s * c0 k r B t := by
  induction s with
  | add x y hx hy => simp only [add_mul, map_add (f := _), hx, hy]; ring
  | tmul a a' =>
    induction t with
    | add x y hx hy => simp only [mul_add, map_add (f := _), hx, hy]; ring
    | tmul b b' => simp [snd_mul, Algebra.smul_def]; ring

theorem co_map {B' : Type} [CommRing B'] [Algebra k B'] (θ : B →ₐ[k] B') (i : Fin r) (s : B ⊗[k] Sq k r) :
    co i (Algebra.TensorProduct.map θ (AlgHom.id k _) s) = θ (co i s) := by
  induction s with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a a' => simp

theorem map_lineCoeffConst {B' : Type} [CommRing B'] [Algebra k B'] (θ : B →ₐ[k] B') (s : B ⊗[k] Sq k r) :
    c0 k r B' (Algebra.TensorProduct.map θ (AlgHom.id k _) s) = θ (c0 k r B s) := by
  induction s with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a a' => simp

noncomputable def dir (l : Fin r → k) : Sq k r →ₐ[k] DualNumber k := TrivSqZeroExt.map (dotProductBilin k k l)

theorem map_dir (l : Fin r → k) (s : B ⊗[k] Sq k r) :
    Algebra.TensorProduct.map (AlgHom.id k B) (dir l) s =
      c0 k r B s ⊗ₜ[k] 1 + (∑ i, l i • co i s) ⊗ₜ[k] (DualNumber.eps : DualNumber k) := by
  induction s with
  | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add, Finset.sum_add_distrib, add_tmul]; abel
  | tmul a x =>
    have : dir l x = x.fst • 1 + (∑ i, l i * x.snd i) • (DualNumber.eps : DualNumber k) := by
      ext <;> simp [dir, dotProduct]
    rw [Algebra.TensorProduct.map_tmul, this]
    simp [tmul_add, smul_smul, ← Finset.sum_smul, smul_tmul]

end Coef

end PositivityTheory.Xgn.JetKernelRank

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.Xgn.JetKernelRank

noncomputable section

local notation "hm" φ:max => Formalism.L2.Pj.homAt (𝟙 (Sp _)) φ

section Pair
open ReciprocityTheory.ChartRestriction.G.DVR

def AdSum {S : Scheme.{0}} {G : Over S} [GrpObj G] (f g : G ⟶ G) {K : Type} [Fintype K]
    (φ : K → ((G ⊗ G).left ⟶ G.left)) (ε : K → ℤ) : Prop :=
  ∀ {T : Over S} (x y : T ⟶ G) (U : Type) [CommGroup U] (h : (T.left ⟶ G.left) → U),
    ∏ i, h ((lift x y).left ≫ φ i) ^ ε i = h (x * (y ≫ g)).left * (h x.left)⁻¹ *
      (h (y ≫ g).left)⁻¹ * ((h ((x ≫ f) * y).left)⁻¹ * h (x ≫ f).left * h y.left)

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (hA : IsAbelianScheme G) {L : LB G.left}
  (hL : L.IsLB) {f g : G ⟶ G} [IsMonHom f] [IsMonHom g] {K : Type} [Fintype K]
  {φ : K → ((G ⊗ G).left ⟶ G.left)} {ε : K → ℤ} {w : LB.Gen (LB.LinComb L φ ε)} (hw : w.IsGen) (hW : AdSum f g φ ε)
include hA hL hw hW

theorem pair_ax {T : Over S} (x : T ⟶ G) {z : T.left} {J} (hJ : Good L z J) :
    val₂ w z J x 1 = val₂ w z J 1 1 ∧ val₂ w z J 1 x = val₂ w z J 1 1 := by
  have hp := (GlobalTheory.globalFns_holds _ _ hA).2
  constructor
  · have := GlobalTheory.CubeDescent.val_eq_of_section hL hw (toUnit G) η[G] (toUnit_unique _ _) hp
      (lift (𝟙 G) 1) (lift 1 1) (fun U _ h => by
        rw [hW, hW]
        simp only [MonObj.one_comp, _root_.mul_one]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel) (fun y J _ => by congr 2; simp [Hom.one_def]) x z J hJ
    simpa only [val₂, comp_lift, Category.comp_id, MonObj.comp_one] using this
  · have := GlobalTheory.CubeDescent.val_eq_of_section hL hw (toUnit G) η[G] (toUnit_unique _ _) hp
      (lift 1 (𝟙 G)) (lift 1 1) (fun U _ h => by
        rw [hW, hW]
        simp only [MonObj.one_comp, _root_.one_mul]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel) (fun y J _ => by congr 2; simp [Hom.one_def]) x z J hJ
    simpa only [val₂, comp_lift, Category.comp_id, MonObj.comp_one] using this

omit [IsMonHom g] in
theorem pair_mul {T : Over S} (x y v : T ⟶ G) (hx : x ≫ f = 1) (hv : v ≫ g = 1) {z : T.left} {J} (hJ : Good L z J) :
    val₂ w z J (y * x) v * val₂ w z J 1 v = val₂ w z J y v * val₂ w z J x v := by
  have := ratio_const GlobalTheory.globalFns_holds hA hL (fun U _ h => by
      refine (hW _ _ U h).trans (Eq.trans ?_ (hW _ _ U h).symm)
      simp only [MonObj.mul_comp, Category.assoc, hx, hv, MonObj.comp_one, _root_.mul_one, mul_inv_cancel])
    (pullGen_isGen _ _ _ _ hw (lift (snd T G * (fst T G ≫ x)) (fst T G ≫ v)).left)
    (pullGen_isGen _ _ _ _ hw (lift (snd T G) (fst T G ≫ v)).left) (𝟙 T) y hJ
  simpa only [val_ros _ _ hJ, MonObj.comp_mul, lift_snd, lift_fst_assoc, Category.id_comp, _root_.one_mul] using this

theorem pair_nondeg [Flat f.left] [Surjective f.left] [QuasiCompact f.left] (hK : Out.KTriv G L)
    {R : Type} [CommRing R] [IsLocalRing R] (s : Sp R ⟶ S) (v : Over.mk s ⟶ G) (hv : v ≫ g = 1)
    (h : ∀ (T : Over S) (ρ : T ⟶ Over.mk s) (x : T ⟶ G), x ≫ f = 1 → ∀ z J, Good L z J →
      val₂ w z J x (ρ ≫ v) = val₂ w z J 1 (ρ ≫ v)) : v = 1 := by
  let T : Over S := Over.mk s
  let π : T ⊗ G ⟶ T ⊗ G := 𝟙 T ⊗ₘ f
  have : IsIso (𝟙 T : T ⟶ T).left := inferInstanceAs (IsIso (𝟙 T.left))
  have : Flat π.left := GlobalTheory.AbelianQuotient.flat_tensorHom _ _
  have : Surjective π.left := GlobalTheory.AbelianQuotient.surjective_tensorHom _ _
  have : QuasiCompact π.left := GlobalTheory.AbelianQuotient.quasiCompact_tensorHom _ _
  have p₁ : π ≫ fst T G = fst T G := by simp [π]
  have p₂ : π ≫ snd T G = snd T G ≫ f := by simp [π]
  let ψ : Fin 4 → ((T ⊗ G).left ⟶ G.left) :=
    ![(snd T G * (fst T G ≫ v)).left, (snd T G).left, (fst T G ≫ v).left, (1 : T ⊗ G ⟶ G).left]
  obtain ⟨σ, hσ, vσ⟩ := exists_gen hL (φ' := fun k => π.left ≫ ψ k) (ε' := ![1, -1, -1, 1]) (fun U _ h => by
      refine (prod_neg _ _ (hW (snd T G) (fst T G ≫ v) U h)).trans ?_
      rw [Fin.prod_univ_four]
      show _ = h (π ≫ (snd T G * (fst T G ≫ v))).left ^ (1 : ℤ) * h (π ≫ snd T G).left ^ (-1 : ℤ) *
        h (π ≫ fst T G ≫ v).left ^ (-1 : ℤ) * h (π ≫ (1 : T ⊗ G ⟶ G)).left ^ (1 : ℤ)
      rw [MonObj.comp_mul, MonObj.comp_one, ← Category.assoc π, p₁, p₂, Category.assoc, hv, MonObj.comp_one,
        _root_.mul_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      module)
    (LB.invGen L _ _ (LB.pullGen L _ _ w (lift (snd T G) (fst T G ≫ v)).left))
    (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hw _))
  obtain ⟨u, hu⟩ := GlobalTheory.CubeDescent.exists_gen_descend hL π.left ψ _ σ hσ fun Z g₁ g₂ z J hJ e => by
    let T' : Over S := Over.mk (g₂ ≫ (T ⊗ G).hom)
    let k₂ : T' ⟶ T ⊗ G := Over.homMk g₂ rfl
    let k₁ : T' ⟶ T ⊗ G := Over.homMk g₁ (by
      change g₁ ≫ (T ⊗ G).hom = g₂ ≫ (T ⊗ G).hom
      rw [← Over.w π, reassoc_of% e])
    have e' : k₁ ≫ π = k₂ ≫ π := Over.OverMorphism.ext e
    have e₁ : k₁ ≫ fst T G = k₂ ≫ fst T G := by simpa only [Category.assoc, p₁] using e' =≫ fst _ _
    have e₂ : (k₁ ≫ snd T G) ≫ f = (k₂ ≫ snd T G) ≫ f := by simpa only [Category.assoc, p₂] using e' =≫ snd _ _
    rw [vσ _ _ z J hJ, vσ _ _ z J hJ, val_inv, val_inv]
    refine congrArg (·⁻¹) ((val_ros w k₁ hJ _ _).trans (Eq.trans ?_ (val_ros w k₂ hJ _ _).symm))
    have hx : ((k₂ ≫ snd T G)⁻¹ * (k₁ ≫ snd T G)) ≫ f = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, e₂, inv_mul_cancel]
    have a := pair_mul hA hL hw hW _ (k₂ ≫ snd T G) ((k₂ ≫ fst T G) ≫ v) hx
      (by rw [Category.assoc, hv, MonObj.comp_one]) hJ
    rw [mul_inv_cancel_left, h T' _ _ hx z J hJ] at a
    rw [← Category.assoc, ← Category.assoc, e₁]
    exact mul_right_cancel a
  obtain ⟨c, hc⟩ := DVR.exists_gen_of_local (V := R) L hL (![v.left, (1 : T ⟶ G).left] : Fin 2 → _) ![1, -1]
  have s₀ : ψ 0 = (lift (fst T G ≫ v) (snd T G) ≫ μ[G]).left := by
    show (snd T G * (fst T G ≫ v)).left = ((fst T G ≫ v) * snd T G).left
    rw [mul_comm]
  have s₃ : ψ 3 = (fst T G).left ≫ (1 : T ⟶ G).left :=
    congrArg (fun q : T ⊗ G ⟶ G => q.left) (MonObj.comp_one (fst T G)).symm
  obtain ⟨w', hw', -⟩ := exists_gen hL
    (φ' := (![(lift (fst T G ≫ v) (snd T G) ≫ μ[G]).left, (snd T G).left] : Fin 2 → _)) (ε' := ![1, -1])
    (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two]
      show h (ψ 0) ^ (1 : ℤ) * h (snd T G).left ^ (-1 : ℤ) * h ((fst T G).left ≫ v.left) ^ (-1 : ℤ) *
        h (ψ 3) ^ (1 : ℤ) * (h ((fst T G).left ≫ v.left) ^ (1 : ℤ) *
        h ((fst T G).left ≫ (1 : T ⟶ G).left) ^ (-1 : ℤ)) =
        h (lift (fst T G ≫ v) (snd T G) ≫ μ[G]).left ^ (1 : ℤ) * h (snd T G).left ^ (-1 : ℤ)
      rw [s₀, s₃]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L _ _ _ _ u (LB.pullGen L _ _ c (fst T G).left))
    (mulGen_isGen _ _ _ _ _ _ _ hu (pullGen_isGen _ _ _ _ hc _))
  exact hK R s v fun _ => ⟨⊤, trivial, gen_chartPull (chartPullPull _ _ _ rfl) w' hw'⟩

omit hA in
theorem pair_exists {T : Over S} (x v : T ⟶ G) (hx : x ≫ f = 1) (hv : v ≫ g = 1) :
    ∃ u : Γ(T.left, ⊤)ˣ, ∀ (T' : Over S) (ρ : T' ⟶ T) z J, Good L z J →
      val₂ w z J (ρ ≫ x) (ρ ≫ v) = gm ρ.left z ⊤ u := by
  obtain ⟨u, hu⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.exists_ratio L hL (fun U _ h => by
      refine (hW x v U h).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      rw [hx, hv, _root_.mul_one, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel) _ (pullGen_isGen _ _ _ _ hw (lift x v).left) (LB.oneGen L) (LB.isGen_oneGen L)
  refine ⟨u, fun T' ρ z J hJ => ?_⟩
  have := hu _ ρ.left z J hJ
  rwa [val_ros _ _ hJ, val_one, _root_.mul_one] at this

end Pair

section Ker
open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD TensorProduct

variable {k : Type} [Field k]

abbrev Ov (k : Type) [Field k] (R : Type) [CommRing R] [Algebra k R] : Over (Sp k) := overAt (𝟙 (Sp k)) R

theorem hm_inj {A B : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] {φ ψ : A →ₐ[k] B}
    (h : hm φ = hm ψ) : φ = ψ := by
  have e : Spec.map (CommRingCat.ofHom (φ : A →+* B)) = Spec.map (CommRingCat.ofHom (ψ : A →+* B)) :=
    congrArg (fun q => q.left) h
  exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom (Spec.map_injective e))

theorem hm_surj {A B : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (y : Ov k B ⟶ Ov k A) :
    ∃ φ : A →ₐ[k] B, hm φ = y := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (R := CommRingCat.of A) (S := CommRingCat.of B) y.left
  have e : y.left ≫ spMap (algebraMap k A) ≫ 𝟙 _ = spMap (algebraMap k B) ≫ 𝟙 _ := Over.w y
  rw [Category.comp_id, Category.comp_id, ← hφ, spMap, ← Spec.map_comp] at e
  have e' := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  exact ⟨⟨φ.hom, fun c => DFunLike.congr_fun e' c⟩, Over.OverMorphism.ext hφ⟩

theorem exists_tensor {A B : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] {T : Over (Sp k)}
    (y : T ⟶ Ov k A) (ρ : T ⟶ Ov k B) : ∃ τ : T ⟶ Ov k (A ⊗[k] B),
      τ ≫ hm Algebra.TensorProduct.includeLeft = y ∧ τ ≫ hm Algebra.TensorProduct.includeRight = ρ := by
  have e₁ : y.left ≫ spMap (algebraMap k A) ≫ 𝟙 _ = T.hom := Over.w y
  have e₂ : ρ.left ≫ spMap (algebraMap k B) ≫ 𝟙 _ = T.hom := Over.w ρ
  rw [Category.comp_id] at e₁ e₂
  let l := pullback.lift y.left ρ.left (e₁.trans e₂.symm) ≫ (pullbackSpecIso k A B).hom
  have l₁ : l ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = y.left := by
    rw [Category.assoc, pullbackSpecIso_hom_fst, pullback.lift_fst]
  have l₂ : l ≫ Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B))) = ρ.left := by
    rw [Category.assoc, pullbackSpecIso_hom_snd, pullback.lift_snd]
  refine ⟨Over.homMk l ?_, Over.OverMorphism.ext l₁, Over.OverMorphism.ext l₂⟩
  refine Eq.trans ?_ ((congrArg (· ≫ spMap (algebraMap k A)) l₁).trans e₁)
  have := Over.w (hm (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B))
  change _ ≫ _ ≫ 𝟙 _ = _ at this
  rw [Category.comp_id] at this
  exact (congrArg (l ≫ ·) this.symm).trans (Category.assoc _ _ _).symm

variable {G : Over (Sp k)} [GrpObj G] {f : G ⟶ G} {A : Type} [CommRing A] [Algebra k A]

theorem exists_ker (i : Sp A ⟶ G.left) (hp : IsPullback i (spMap (algebraMap k A)) f.left (η[G]).left) :
    ∃ κ : Ov k A ⟶ G, κ ≫ f = 1 ∧ ∀ (T : Over (Sp k)) (x : T ⟶ G), x ≫ f = 1 → ∃! y : T ⟶ Ov k A, y ≫ κ = x := by
  have e : (η[G]).left ≫ G.hom = 𝟙 _ := Over.w _
  have hi : i ≫ G.hom = spMap (algebraMap k A) ≫ 𝟙 _ := by
    rw [← Over.w f, ← Category.assoc, hp.w, Category.assoc, e]; rfl
  have one : ∀ T : Over (Sp k), (1 : T ⟶ G).left = T.hom ≫ (η[G]).left := fun T => by
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  refine ⟨Over.homMk i hi, Over.OverMorphism.ext ?_, fun T x hx => ?_⟩
  · rw [one]
    exact hp.w.trans (congrArg (· ≫ _) (Category.comp_id _).symm)
  · have hx' : x.left ≫ f.left = T.hom ≫ (η[G]).left := (congrArg (fun q => q.left) hx).trans (one T)
    refine ⟨Over.homMk (hp.lift _ _ hx') ((Category.assoc _ _ _).symm.trans
      ((Category.comp_id _).trans (hp.lift_snd _ _ _))), Over.OverMorphism.ext (hp.lift_fst _ _ _), fun y hy => ?_⟩
    refine Over.OverMorphism.ext (hp.hom_ext ((congrArg (fun q => q.left) hy).trans (hp.lift_fst _ _ _).symm) ?_)
    have := Over.w y
    change _ ≫ _ ≫ 𝟙 _ = _ at this
    rw [Category.comp_id] at this
    exact this.trans (hp.lift_snd _ _ _).symm

variable {κ : Ov k A ⟶ G} (h₁ : κ ≫ f = 1)
  (h₂ : ∀ (T : Over (Sp k)) (x : T ⟶ G), x ≫ f = 1 → ∃! y : T ⟶ Ov k A, y ≫ κ = x)
include h₁ h₂

theorem pt_inj {R : Type} [CommRing R] [Algebra k R] {φ ψ : A →ₐ[k] R} (h : hm φ ≫ κ = hm ψ ≫ κ) : φ = ψ :=
  hm_inj ((h₂ _ (hm ψ ≫ κ) (by rw [Category.assoc, h₁, MonObj.comp_one])).unique h rfl)

omit h₁ in
theorem pt_surj {R : Type} [CommRing R] [Algebra k R] (x : Ov k R ⟶ G) (h : x ≫ f = 1) :
    ∃ φ : A →ₐ[k] R, hm φ ≫ κ = x := by
  obtain ⟨y, hy, -⟩ := h₂ _ x h
  obtain ⟨φ, rfl⟩ := hm_surj y
  exact ⟨φ, hy⟩

omit h₁ in
theorem flat_surj [IsAlgClosed k] [Module.Finite k A] [IsMonHom f] (hA : IsAbelianScheme G) :
    Flat f.left ∧ Surjective f.left ∧ QuasiCompact f.left := by
  have := hA.proper
  have := hA.smooth
  have := hA.geomConnected
  have : IsProper (f.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : IsProper f.left := .of_comp _ G.hom
  have : LocallyQuasiFinite f.left := GlobalTheory.locallyQuasiFinite_of_finite_geometric_ker _ G G f inferInstance
    inferInstance inferInstance fun Ω _ _ t => by
      obtain ⟨β, rfl⟩ : ∃ β : k →+* Ω, t = spMap β ≫ 𝟙 _ := by
        obtain ⟨β, rfl⟩ := Spec.map_surjective (R := CommRingCat.of k) (S := CommRingCat.of Ω) t
        exact ⟨β.hom, (Category.comp_id _).symm⟩
      let _ := β.toAlgebra
      choose φ hφ using fun x : {x : Ov k Ω ⟶ G // x ≫ f = 1} => pt_surj h₂ x.1 x.2
      exact Finite.of_injective φ fun a b e => Subtype.ext ((hφ a).symm.trans (e ▸ hφ b))
  have : IsFinite f.left := .of_isProper_of_locallyQuasiFinite _
  have := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ G
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_subsingleton G.hom
  have := GlobalTheory.flat_and_surjective_of_isFinite_grpEnd k G f
  exact ⟨this.1, this.2, inferInstance⟩


end Ker

section Eval
open MvPolynomial Formalism.L2.Pj

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R]

theorem aeval_one {I : Type} [Fintype I] [DecidableEq I] (c : I → R) (hc : ∀ i j, c i * c j = 0) (P : MvPolynomial I k) :
    aeval c P = algebraMap k R (AddMonoidAlgebra.coeff P 0) + ∑ i, AddMonoidAlgebra.coeff P (Finsupp.single i 1) • c i := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [coeff_C, (Finsupp.single_ne_zero.2 one_ne_zero).symm]
  | add P Q hP hQ => simp only [map_add (f := _), hP, hQ, MvPolynomial.coeff_add, add_smul, Finset.sum_add_distrib]; abel
  | mul_X P n hP =>
    rw [map_mul, hP, aeval_X, add_mul, Finset.sum_mul]
    simp only [smul_mul_assoc, hc, smul_zero, Finset.sum_const_zero, add_zero, coeff_mul_X']
    rw [Finset.sum_eq_single n]
    · simp [Algebra.smul_def]
    · intro b _ hb; simp [Finsupp.single_apply, hb, hb.symm]
    · simp

theorem aeval_two {d : ℕ} (a b : Fin d → R) (ha : ∀ i j, a i * a j = 0) (hb : ∀ i j, b i * b j = 0)
    (P : MvPolynomial (Fin 2 × Fin d) k) :
    aeval (fun q : Fin 2 × Fin d => ![a, b] q.1 q.2) P = algebraMap k R (AddMonoidAlgebra.coeff P 0) +
      ∑ i, AddMonoidAlgebra.coeff P (Finsupp.single (0, i) 1) • a i + ∑ j, AddMonoidAlgebra.coeff P (Finsupp.single (1, j) 1) • b j +
      ∑ i, ∑ j, AddMonoidAlgebra.coeff P (Finsupp.single (0, i) 1 + Finsupp.single (1, j) 1) • (a i * b j) := by
  have h3 : ∀ i j l, a i * b j * a l = 0 := fun i j l => by rw [mul_right_comm, ha, zero_mul]
  have h4 : ∀ i j l, a i * b j * b l = 0 := fun i j l => by rw [_root_.mul_assoc, hb, mul_zero]
  induction P using MvPolynomial.induction_on with
  | C a =>
    have : ∀ i j : Fin d, ¬ (0 : Fin 2 × Fin d →₀ ℕ) = Finsupp.single (0, i) 1 + Finsupp.single (1, j) 1 := fun i j h => by
      simpa using DFunLike.congr_fun h (0, i)
    simp [coeff_C, (Finsupp.single_ne_zero.2 one_ne_zero).symm, this]
  | add P Q hP hQ => simp only [map_add (f := _), hP, hQ, MvPolynomial.coeff_add, add_smul, Finset.sum_add_distrib]; abel
  | mul_X P n hP =>
    rw [map_mul, hP, aeval_X]
    obtain ⟨l, n⟩ := n
    fin_cases l
    · simp only [add_mul, Finset.sum_mul, smul_mul_assoc, ha, h3, smul_zero, Finset.sum_const_zero, add_zero,
        coeff_mul_X', Fin.zero_eta, Matrix.cons_val_zero]
      rw [Finset.sum_eq_single n (f := fun i => _ • a i), Finset.sum_eq_single n (f := fun i => ∑ j, _ • (a i * b j))]
      · simp [Algebra.smul_def, Finsupp.single_apply, mul_comm]
      · intro b _ hb; simp [Finsupp.single_apply, hb, hb.symm]
      · simp
      · intro b _ hb; simp [Finsupp.single_apply, hb, hb.symm]
      · simp
    · simp only [add_mul, Finset.sum_mul, smul_mul_assoc, hb, h4, smul_zero, Finset.sum_const_zero, add_zero,
        coeff_mul_X', Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [Finset.sum_comm, Finset.sum_eq_single n (f := fun i => _ • b i),
        Finset.sum_eq_single n (f := fun j => ∑ i, _ • (a i * b j))]
      · simp [Algebra.smul_def, Finsupp.single_apply, mul_comm]
      · intro b _ hb; simp [Finsupp.single_apply, hb, hb.symm]
      · simp
      · intro b _ hb; simp [Finsupp.single_apply, hb, hb.symm]
      · simp

theorem span_sq {I : Type} (c : I → R) (hc : ∀ i j, c i * c j = 0) : Ideal.span (Set.range c) ^ 2 = ⊥ := by
  rw [pow_two, Ideal.span_mul_span', Ideal.span_eq_bot]
  rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
  exact hc i j


variable (k) in
def th1 {d : ℕ} (m : ℕ) (a : Fin d → R) (ha : ∀ i j, a i * a j = 0) : Jet k (Fin 1 × Fin d) (m + 1) →ₐ[k] R :=
  liftJet (aeval fun q => a q.2) (by
    simp only [aeval_X]
    exact le_bot_iff.1 ((Ideal.pow_le_pow_right (by omega)).trans (span_sq _ fun i j => ha _ _).le))


variable (k) in
def th2 {d : ℕ} (a b : Fin d → R) (ha : ∀ i j, a i * a j = 0) (hb : ∀ i j, b i * b j = 0) :
    Jet k (Fin 2 × Fin d) 3 →ₐ[k] R :=
  liftJet (aeval fun q => ![a, b] q.1 q.2) (by
    simp only [aeval_X]
    have : Ideal.span (Set.range fun q : Fin 2 × Fin d => ![a, b] q.1 q.2) ≤
        Ideal.span (Set.range a) ⊔ Ideal.span (Set.range b) := Ideal.span_le.2 (by
      rintro _ ⟨⟨l, i⟩, rfl⟩
      fin_cases l
      · exact Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)
      · exact Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
    refine le_bot_iff.1 ((Ideal.pow_right_mono this _).trans
      ((Ideal.sup_pow_add_le_pow_sup_pow (n := 2) (m := 2)).trans ?_))
    rw [span_sq _ ha, span_sq _ hb, bot_sup_eq])

theorem first_jet_mk {d : ℕ} (m : ℕ) (a : Fin d → R) (ha : ∀ i j, a i * a j = 0) (P) :
    th1 k m a ha (Ideal.Quotient.mk _ P) = aeval (fun q => a q.2) P := rfl

theorem second_jet_mk {d : ℕ} (a b : Fin d → R) (ha : ∀ i j, a i * a j = 0) (hb : ∀ i j, b i * b j = 0) (P) :
    th2 k a b ha hb (Ideal.Quotient.mk _ P) = aeval (fun q => ![a, b] q.1 q.2) P := rfl

theorem subst_X {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' k) (s : κ) (h : constantCoeff (φ s) = 0) :
    jetSubstP m φ (Ideal.Quotient.mk _ (X s)) = Ideal.Quotient.mk _ (φ s) := by
  rw [jetSubstP, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jetMap_mk, aeval_X, h, map_zero, sub_zero]

theorem aeval_trunc {d : ℕ} (m : ℕ) (a : Fin d → R) (ha : ∀ i j, a i * a j = 0) (φ : Germ.Pt k 1 d)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (j : Fin d) :
    aeval (fun q : Fin 1 × Fin d => a q.2) (psTrunc (m + 1) (φ j)) = ∑ i, lin φ 1 j i • a i := by
  rw [aeval_one _ (fun i j => ha _ _), Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.coeff_psTrunc _ _ _ (by simp),
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ, map_zero, zero_add, Fintype.sum_prod_type, Fin.sum_univ_one]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.coeff_psTrunc _ _ _ (by simp)]
  rfl

theorem second_jet_expansion {d : ℕ} (a b : Fin d → R) (ha : ∀ i j, a i * a j = 0) (hb : ∀ i j, b i * b j = 0)
    (f : Germ.PS k 2 d) : ∃ α β : Fin d → k, th2 k a b ha hb (psJet 3 f) =
      algebraMap k R (MvPowerSeries.constantCoeff f) + ∑ i, α i • a i + ∑ j, β j • b j +
      ∑ i, ∑ j, bil f 1 1 i j • (a i * b j) := by
  refine ⟨fun i => AddMonoidAlgebra.coeff (psTrunc 3 f) (Finsupp.single (0, i) 1), fun i => AddMonoidAlgebra.coeff (psTrunc 3 f) (Finsupp.single (1, i) 1),
    (aeval_two a b ha hb _).trans ?_⟩
  rw [Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.coeff_psTrunc _ _ _ (by simp), MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.coeff_psTrunc _ _ _ (by simp)]
  rfl

end Eval

section Chart
open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermD ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {k : Type} [Field k]
  {t : SAB H (Sp k)} {d : ℕ} (g : GermAt t (𝟙 (Sp k)) d) {R : Type} [CommRing R] [Algebra k R]

def cp (a : Fin d → R) (ha : ∀ i j, a i * a j = 0) : Ov k R ⟶ t.G := hm (th1 k 2 a ha) ≫ g.x 3

theorem cp_nat {R' : Type} [CommRing R'] [Algebra k R'] (θ : R →ₐ[k] R') (a : Fin d → R) (ha : ∀ i j, a i * a j = 0)
    (b : Fin d → R') (hb : ∀ i j, b i * b j = 0) (h : ∀ i, θ (a i) = b i) : hm θ ≫ cp g a ha = cp g b hb := by
  rw [cp, cp, ← Category.assoc, homAt_comp]
  congr 2
  exact jet_hom_ext fun s => by simp [first_jet_mk, h]

theorem first_jet_zero (m : ℕ) (a : Fin d → R) (ha : ∀ i j, a i * a j = 0) (h : a = 0) :
    hm (th1 k m a ha) ≫ g.x (m + 1) = 1 := by
  have : th1 k m a ha = (Algebra.ofId k R).comp jetAug := jet_hom_ext fun s => by
    rw [AlgHom.comp_apply, GermB.jetAug_X]; simp [first_jet_mk, h]
  rw [this, ← homAt_comp, Category.assoc, g.chart.zero, MonObj.comp_one]

theorem cp_zero (a : Fin d → R) (ha : ∀ i j, a i * a j = 0) (h : a = 0) : cp g a ha = 1 := first_jet_zero g 2 a ha h

theorem cp_act (c : 𝓞 E) (a : Fin d → R) (ha : ∀ i j, a i * a j = 0) (h : ∀ j, ∑ i, rho g.B c j i • a i = 0) :
    cp g a ha ≫ t.act.act c = 1 := by
  rw [cp, Category.assoc, g.chart.act, ← Category.assoc, homAt_comp, ← cp_zero g (0 : Fin d → R) (by simp) rfl, cp]
  congr 2
  refine jet_hom_ext fun s => ?_
  rw [AlgHom.comp_apply, subst_X, first_jet_mk, aeval_trunc 2 a ha _ (g.B.A.const c), first_jet_mk]
  · exact (h s.2).trans (MvPolynomial.aeval_X (fun q : Fin 1 × Fin d => (0 : Fin d → R) q.2) s).symm
  · exact (FBIdPh.cc_psTrunc _ _).trans (g.B.A.const _ _)

theorem first_jet_truncate (m : ℕ) (a : Fin d → R) (ha : ∀ i j, a i * a j = 0) :
    hm (th1 k (m + 1) a ha) ≫ g.x (m + 1 + 1) = hm (th1 k m a ha) ≫ g.x (m + 1) := by
  have : th1 k (m + 1) a ha = (th1 k m a ha).comp jetTrunc := jet_hom_ext fun s => by
    rw [AlgHom.comp_apply, jetTrunc_mk, first_jet_mk, first_jet_mk]
  rw [this, ← homAt_comp, Category.assoc, g.chart.trunc]

theorem cp_eq (a : Fin d → R) (ha : ∀ i j, a i * a j = 0) : cp g a ha = hm (th1 k 0 a ha) ≫ g.x 1 :=
  (first_jet_truncate g 1 a ha).trans (first_jet_truncate g 0 a ha)

theorem jet_inj (hs : ∀ a : 𝓞 E, star a = H.bar a) (a : Fin d → Jet k Unit 1) (ha : ∀ i j, a i * a j = 0)
    (h0 : ∀ i, (jetAug : Jet k Unit 1 →ₐ[k] k) (a i) = 0) (h : cp g a ha = 1) : a = 0 := by
  have h3 := ((GlobalTheory.CompanionTheory.Ar.GermUniv.germ_chart_universal E H hs _ t k _ d g).2 Unit 1 1 (MonObj.comp_one _)).unique
    (y₁ := th1 k 0 a ha) (y₂ := th1 k 0 0 (by simp))
    ⟨fun q => by rw [first_jet_mk, MvPolynomial.aeval_X, h0], h.symm.trans (cp_eq g a ha)⟩
    ⟨fun q => by rw [first_jet_mk, MvPolynomial.aeval_X]; exact map_zero _, (first_jet_zero g 0 _ _ rfl).symm⟩
  funext i
  have h4 := DFunLike.congr_fun h3 (Ideal.Quotient.mk _ (MvPolynomial.X (0, i)))
  rwa [first_jet_mk, first_jet_mk, MvPolynomial.aeval_X, MvPolynomial.aeval_X] at h4

theorem exists_dual (k : Type) [Field k] : ∃ (x : Jet k Unit 1) (θ : DualNumber k →ₐ[k] Jet k Unit 1),
    x * x = 0 ∧ (∀ c : k, θ (TrivSqZeroExt.inr c) = c • x) ∧ (jetAug : Jet k Unit 1 →ₐ[k] k) x = 0 ∧
      ∀ c : k, c • x = 0 → c = 0 := by
  have hx : (Ideal.Quotient.mk _ (MvPolynomial.X ()) : Jet k Unit 1) * Ideal.Quotient.mk _ (MvPolynomial.X ()) = 0 := by
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← pow_two]
    exact Ideal.pow_mem_pow (X_mem_orig _) 2
  refine ⟨_, DualNumber.lift ⟨(Algebra.ofId _ _, _), hx, fun _ => Commute.all _ _⟩, hx, fun c => ?_,
    GermB.jetAug_X _ _, fun c hc => ?_⟩
  · rw [DualNumber.lift_apply_apply, TrivSqZeroExt.fst_inr, map_zero, zero_add, TrivSqZeroExt.snd_inr,
      Algebra.smul_def, Algebra.ofId_apply]
  · have h5 : (jetTan () : Jet k Unit (0 + 1) →ₐ[k] DualNumber k) (Ideal.Quotient.mk _ (MvPolynomial.X ())) =
        DualNumber.eps := (MvPolynomial.aeval_X _ _).trans (if_pos rfl)
    have h4 := congrArg (jetTan () : Jet k Unit (0 + 1) →ₐ[k] DualNumber k) hc
    rw [map_smul, h5, map_zero] at h4
    simpa using congrArg TrivSqZeroExt.snd h4

theorem cp_inj (hs : ∀ a : 𝓞 E, star a = H.bar a) (w : Fin d → k) (ha)
    (h : cp g (fun i => (TrivSqZeroExt.inr (w i) : DualNumber k)) ha = 1) : w = 0 := by
  obtain ⟨x, θ, hx, hθ, h0, hi⟩ := exists_dual k
  have hb : ∀ i j, (w i • x) * (w j • x) = 0 := fun i j => by rw [smul_mul_smul_comm, hx, smul_zero]
  have h1 := cp_nat g θ _ ha _ hb fun i => hθ _
  rw [h, MonObj.comp_one] at h1
  have := jet_inj g hs _ hb (fun i => by rw [map_smul, h0, smul_zero]) h1.symm
  exact funext fun i => hi _ (congrFun this i)

variable {K : Type} [Fintype K] {φ : K → ((t.G ⊗ t.G).left ⟶ t.G.left)} {ε : K → ℤ}
  (w : LB.Gen (LB.LinComb t.PP.L φ ε))

def Chi (x v : Ov k R ⟶ t.G) (c : R) : Prop :=
  ∀ (T : Over (Sp k)) (ρ : T ⟶ Ov k R) z J, Good t.PP.L z J →
    (val₂ w z J (ρ ≫ x) (ρ ≫ v)).val = cst (V := R) ρ.left z c

theorem second_jet_rename (a b : Fin d → R) (ha : ∀ i j, a i * a j = 0) (hb : ∀ i j, b i * b j = 0) (l : Fin 2)
    (f : Germ.PS k 1 d) : th2 k a b ha hb (Ideal.Quotient.mk _ (psIn d 3 ![l] f)) =
      MvPolynomial.aeval (fun q => ![a, b] l q.2) (psTrunc (2 + 1) f) := by
  rw [second_jet_mk, psIn, MvPolynomial.aeval_rename]
  refine congrArg (fun q : Fin 1 × Fin d → R => MvPolynomial.aeval q (psTrunc 3 f)) (funext fun ⟨q, i⟩ => ?_)
  obtain rfl := Subsingleton.elim q 0
  rfl

theorem second_jet_left_substitution (a b : Fin d → R) (ha : ∀ i j, a i * a j = 0) (hb : ∀ i j, b i * b j = 0) (f : Germ.Pt k 1 d)
    (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (h : ∀ j, ∑ i, lin f 1 j i • a i = 0) :
    (th2 k a b ha hb).comp (jetSubstP 3 fun p : Fin 2 × Fin d =>
      (![fun j => psIn d 3 ![0] (f j), fun j => MvPolynomial.X ((1 : Fin 2), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) k) p.1 p.2) =
    (th1 k 2 b hb).comp (jetSubstP 3 fun p : Fin 2 × Fin d =>
      (![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) k) p.1 p.2) := by
  refine jet_hom_ext (Prod.forall.2 (Fin.forall_fin_two.2 ⟨fun j => ?_, fun j => ?_⟩))
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, subst_X, subst_X]
    · simp only [Matrix.cons_val_zero]
      rw [second_jet_rename, Matrix.cons_val_zero, aeval_trunc 2 a ha _ hf j, h, map_zero, map_zero]
    · simp
    · simp only [Matrix.cons_val_zero]
      rw [FBIdPh.cc_psIn, hf]
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, subst_X, subst_X] <;> simp [first_jet_mk, second_jet_mk]

theorem second_jet_right_substitution (a b : Fin d → R) (ha : ∀ i j, a i * a j = 0) (hb : ∀ i j, b i * b j = 0) (f : Germ.Pt k 1 d)
    (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (h : ∀ j, ∑ i, lin f 1 j i • b i = 0) :
    (th2 k a b ha hb).comp (jetSubstP 3 fun p : Fin 2 × Fin d =>
      (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d 3 ![1] (f j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) k) p.1 p.2) =
    (th1 k 2 a ha).comp (jetSubstP 3 fun p : Fin 2 × Fin d =>
      (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun _ => 0] :
        Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) k) p.1 p.2) := by
  refine jet_hom_ext (Prod.forall.2 (Fin.forall_fin_two.2 ⟨fun j => ?_, fun j => ?_⟩))
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, subst_X, subst_X] <;> simp [first_jet_mk, second_jet_mk]
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, subst_X, subst_X]
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [second_jet_rename, Matrix.cons_val_one, Matrix.cons_val_zero, aeval_trunc 2 b hb _ hf j, h, map_zero, map_zero]
    · simp
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [FBIdPh.cc_psIn, hf]

theorem second_jet_point (a b : Fin d → R) (ha : ∀ i j, a i * a j = 0) (hb : ∀ i j, b i * b j = 0) :
    hm (th2 k a b ha hb) ≫ jptG t _ d g.x 3 (0 : Fin 2) = cp g a ha ∧
      hm (th2 k a b ha hb) ≫ jptG t _ d g.x 3 (1 : Fin 2) = cp g b hb := by
  have e₀ : (th2 k a b ha hb).comp (jetCopy d 3 (0 : Fin 2)) = th1 k 2 a ha :=
    jet_hom_ext fun s => by simp [jetCopy, jetMap_mk, first_jet_mk, second_jet_mk]
  have e₁ : (th2 k a b ha hb).comp (jetCopy d 3 (1 : Fin 2)) = th1 k 2 b hb :=
    jet_hom_ext fun s => by simp [jetCopy, jetMap_mk, first_jet_mk, second_jet_mk]
  constructor
  · rw [jptG, cp, ← Category.assoc, homAt_comp, e₀]
  · rw [jptG, cp, ← Category.assoc, homAt_comp, e₁]

theorem val_pe {n : ℕ} (ψ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) k) (θ : Jet k (Fin n × Fin d) 3 →ₐ[k] R)
    {T : Over (Sp k)} (ρ : T ⟶ Ov k R) {z} {J} (hJ : Good t.PP.L z J) :
    val (peG t _ d g.x g.e 3 ψ) (ρ ≫ hm θ).left z J =
      val (L := t.PP.L) (φ := cφG t ![jptG t _ d g.x 3 (0 : Fin 2), jptG t _ d g.x 3 (1 : Fin 2)]) (ε := cε 2) (g.e 3)
        (ρ ≫ hm (θ.comp (jetSubstP 3 fun p : Fin 2 × Fin d => ψ p.1 p.2))).left z J := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [← Over.comp_left, Category.assoc, homAt_comp]

theorem val_ax {Z : Scheme.{0}} (r : Z ⟶ (jOG (𝟙 (Sp k)) d 3 1).left) {z} {J} (hJ : Good t.PP.L z J) :
    val (peG t _ d g.x g.e 3 ![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)]) r z J = 1 ∧
    val (peG t _ d g.x g.e 3 ![fun j => MvPolynomial.X ((0 : Fin 1), j), fun _ => 0]) r z J = 1 :=
  ⟨(val_corr hJ (g.axes 3).1 r).trans (val_one _), (val_corr hJ (g.axes 3).2 r).trans (val_one _)⟩

theorem val_left (a b : Fin d → R) (ha : ∀ i j, a i * a j = 0) (hb : ∀ i j, b i * b j = 0) (f : Germ.Pt k 1 d)
    (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (h : ∀ j, ∑ i, lin f 1 j i • a i = 0)
    {T : Over (Sp k)} (ρ : T ⟶ Ov k R) {z} {J} (hJ : Good t.PP.L z J) :
    val (peG t _ d g.x g.e 3 ![fun j => psIn d 3 ![0] (f j), fun j => MvPolynomial.X ((1 : Fin 2), j)])
      (ρ ≫ hm (th2 k a b ha hb)).left z J = 1 := by
  rw [val_pe g _ _ ρ hJ, second_jet_left_substitution a b ha hb f hf h]
  exact (val_pe g _ _ ρ hJ).symm.trans (val_ax g (ρ ≫ hm (th1 k 2 b hb)).left hJ).1

theorem val_right (a b : Fin d → R) (ha : ∀ i j, a i * a j = 0) (hb : ∀ i j, b i * b j = 0) (f : Germ.Pt k 1 d)
    (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (h : ∀ j, ∑ i, lin f 1 j i • b i = 0)
    {T : Over (Sp k)} (ρ : T ⟶ Ov k R) {z} {J} (hJ : Good t.PP.L z J) :
    val (peG t _ d g.x g.e 3 ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d 3 ![1] (f j)])
      (ρ ≫ hm (th2 k a b ha hb)).left z J = 1 := by
  rw [val_pe g _ _ ρ hJ, second_jet_right_substitution a b ha hb f hf h]
  exact (val_pe g _ _ ρ hJ).symm.trans (val_ax g (ρ ≫ hm (th1 k 2 a ha)).left hJ).2

theorem gm_unit {B : Type} [CommRing B] [Algebra k B] (U : Bˣ) (θ : B →ₐ[k] R) {T : Over (Sp k)} (ρ : T ⟶ Ov k R) (z) :
    (gm (ρ ≫ hm θ).left z ⊤ (unitΓ U)).val = cst (V := R) ρ.left z (θ U) :=
  (gs_unit _ z ⊤ trivial (unitΓ U)).symm.trans (cst_comp ρ.left (θ : B →+* R) z U.val)

theorem chi_chart (c : 𝓞 E) (U : (Jet k (Fin 2 × Fin d) 3)ˣ)
    (h : LB.Gen.Corr t.PP.L _ _ _ _ (LB.mulGen t.PP.L _ _ _ _
      (LB.pullGen t.PP.L _ _ w (lift (jptG t _ d g.x 3 (0 : Fin 2)) (jptG t _ d g.x 3 (1 : Fin 2))).left)
      (peG t _ d g.x g.e 3 ![fun j => psIn d 3 ![0] (g.B.A.act c j), fun j => MvPolynomial.X ((1 : Fin 2), j)]))
      (scaleGenG t _ _ (unitΓ U) (peG t _ d g.x g.e 3
        ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d 3 ![1] (g.B.A.act (H.bar c) j)])))
    (a b : Fin d → R) (ha : ∀ i j, a i * a j = 0) (hb : ∀ i j, b i * b j = 0)
    (h₁ : ∀ j, ∑ i, rho g.B c j i • a i = 0) (h₂ : ∀ j, ∑ i, rho g.B (H.bar c) j i • b i = 0) :
    Chi w (cp g a ha) (cp g b hb) (th2 k a b ha hb U) := by
  intro T ρ z J hJ
  obtain ⟨j₀, j₁⟩ := second_jet_point g a b ha hb
  have e₀ := val_left g a b ha hb _ (g.B.A.const c) h₁ ρ hJ
  have e₁ := val_right g a b ha hb _ (g.B.A.const _) h₂ ρ hJ
  have e₂ := val_ros w (ρ ≫ hm (th2 k a b ha hb)) hJ (jptG t _ d g.x 3 (0 : Fin 2)) (jptG t _ d g.x 3 (1 : Fin 2))
  rw [Category.assoc, Category.assoc, j₀, j₁] at e₂
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) e₂ e₀)).symm.trans
    ((val_corr hJ h (ρ ≫ hm (th2 k a b ha hb)).left).trans
      ((GermB.val_scale t _ _ _ _ _ _ _ hJ).trans (congrArg₂ (· * ·) rfl e₁)))
  exact (congrArg Units.val (mul_right_cancel e)).trans (gm_unit U _ ρ z)

variable {w}

theorem Chi.unique {x v : Ov k R ⟶ t.G} {c c' : R} (h : Chi w x v c) (h' : Chi w x v c') : c = c' :=
  cst_ext fun z => by
    choose J hJ using fun ψ : Sp R ⟶ t.G.left => exists_chart t.PP.isLB (ψ z)
    exact (h _ (𝟙 _) z J hJ).symm.trans (h' _ (𝟙 _) z J hJ)

theorem Chi.nat {x v : Ov k R ⟶ t.G} {c : R} (h : Chi w x v c) {R' : Type} [CommRing R'] [Algebra k R']
    (θ : R →ₐ[k] R') : Chi w (hm θ ≫ x) (hm θ ≫ v) (θ c) := fun T ρ z J hJ => by
  rw [← Category.assoc, ← Category.assoc, h T _ z J hJ]
  exact cst_comp ρ.left (θ : R →+* R') z c

variable {f f' : t.G ⟶ t.G} [IsMonHom f] [IsMonHom f'] (hA : IsAbelianScheme t.G) (hw : w.IsGen)
  (hW : AdSum f f' φ ε)
include hw hW

theorem chi_exists (x v : Ov k R ⟶ t.G) (hx : x ≫ f = 1) (hv : v ≫ f' = 1) : ∃ c, Chi w x v c := by
  obtain ⟨u, hu⟩ := pair_exists t.PP.isLB hw hW x v hx hv
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom u.val, fun T ρ z J hJ => ?_⟩
  rw [hu T ρ z J hJ, ← gs_unit _ z ⊤ trivial, cst]
  congr 1
  exact (congrArg (fun q => CommRingCat.Hom.hom q u.val) (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id).symm

include hA

theorem chi_one (h : Chi w (1 : Ov k R ⟶ t.G) 1 1) (x : Ov k R ⟶ t.G) : Chi w x 1 1 ∧ Chi w 1 x 1 := by
  constructor <;> intro T ρ z J hJ <;> have := h T ρ z J hJ <;> rw [MonObj.comp_one] at this ⊢
  · rw [(pair_ax hA t.PP.isLB hw hW _ hJ).1, this]
  · rw [(pair_ax hA t.PP.isLB hw hW _ hJ).2, this]

theorem chi_mul (h : Chi w (1 : Ov k R ⟶ t.G) 1 1) {x y v : Ov k R ⟶ t.G} (hx : x ≫ f = 1) (hv : v ≫ f' = 1)
    {c c' : R} (h₁ : Chi w y v c) (h₂ : Chi w x v c') : Chi w (y * x) v (c * c') := fun T ρ z J hJ => by
  have e := congrArg Units.val (pair_mul hA t.PP.isLB hw hW (ρ ≫ x) (ρ ≫ y) (ρ ≫ v)
    (by rw [Category.assoc, hx, MonObj.comp_one]) (by rw [Category.assoc, hv, MonObj.comp_one]) hJ)
  have e' := (chi_one hA hw hW h v).2 T ρ z J hJ
  rw [MonObj.comp_one, cst_one] at e'
  rw [Units.val_mul, Units.val_mul, e', h₁ T ρ z J hJ, h₂ T ρ z J hJ, _root_.mul_one] at e
  rw [MonObj.comp_mul, e, cst_mul]

end Chart

end

end PositivityTheory.Xgn.JetKernelRank

