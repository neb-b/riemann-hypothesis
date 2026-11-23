module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1912
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0615
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantsJetsLocalDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.JetEx

open TrivSqZeroExt

variable {W : Type} [CommRing W]

theorem dual_isLocalRing [IsLocalRing W] : IsLocalRing (DualNumber W) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
  exact IsLocalRing.isUnit_or_isUnit_one_sub_self a.fst

theorem fstHom_isLocalHom : IsLocalHom (TrivSqZeroExt.fstHom W W W).toRingHom :=
  ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩

abbrev red (W : Type) [CommRing W] : Sp W ⟶ Sp (DualNumber W) := spMap (TrivSqZeroExt.fstHom W W W).toRingHom

theorem red_closedPoint [IsLocalRing W] :
    letI := dual_isLocalRing (W := W)
    (red W).base (IsLocalRing.closedPoint W) = IsLocalRing.closedPoint (DualNumber W) := by
  letI := dual_isLocalRing (W := W)
  haveI := fstHom_isLocalHom (W := W)
  rw [Spec.map_base]
  exact IsLocalRing.comap_closedPoint _

theorem top_le_of_red [IsLocalRing W] {X : Scheme.{0}} (y : Sp (DualNumber W) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ (red W ≫ y) ⁻¹ᵁ U) : ⊤ ≤ y ⁻¹ᵁ U := by
  letI := dual_isLocalRing (W := W)
  rw [Scheme.preimage_eq_top_of_closedPoint_mem y (U := U) ?_]
  have := h (show IsLocalRing.closedPoint W ∈ (⊤ : (Sp W).Opens) from trivial)
  rw [← red_closedPoint]
  exact this

theorem valR_fst {X : Scheme.{0}} (y : Sp (DualNumber W) ⟶ X) (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) (f : Γ(X, U)) :
    (valR y U f).fst = valR (red W ≫ y) U f := by
  have h' : ⊤ ≤ (red W ≫ y) ⁻¹ᵁ U := by
    rw [Scheme.Hom.comp_preimage]; exact fun p _ => h trivial
  unfold valR
  rw [dif_pos h, dif_pos h', ← Scheme.Hom.appLE_comp_appLE (red W) y U ⊤ ⊤ h le_top]
  have n := congrArg (fun q => q.hom ((y.appLE U ⊤ h).hom f))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (TrivSqZeroExt.fstHom W W W).toRingHom))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n
  rw [CommRingCat.hom_comp, RingHom.comp_apply]
  rw [show (red W).appLE ⊤ ⊤ le_top = (red W).appTop from (Scheme.Hom.app_eq_appLE _).symm]
  exact n.symm

end GlobalTheory.MBLow.JetEx

namespace GlobalTheory.MBLow.JetEx

open TrivSqZeroExt

variable {W : Type} [CommRing W]

theorem epsLift_fst {A : Over (Sp W)} [GrpObj A] (u : epsR W ⟶ A) :
    epsLift u ≫ (fst (baseOver (Sp W)) A).left = (epsR W).hom := by
  rw [epsLift, ← Over.comp_left, lift_fst]; rfl

theorem epsLift_snd {A : Over (Sp W)} [GrpObj A] (u : epsR W ⟶ A) :
    epsLift u ≫ (snd (baseOver (Sp W)) A).left = u.left := by
  rw [epsLift, ← Over.comp_left, lift_snd]

theorem red_epsLift {A : Over (Sp W)} [GrpObj A] (v v' : epsR W ⟶ A) (hv : IsTangent v) (hv' : IsTangent v') :
    red W ≫ epsLift v = red W ≫ epsLift v' := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, ← Over.fst_left, epsLift_fst, epsLift_fst]
  · rw [Category.assoc, Category.assoc, ← Over.snd_left, epsLift_snd, epsLift_snd]
    exact hv.trans hv'.symm

theorem red_epsLift_snd {A : Over (Sp W)} [GrpObj A] (v : epsR W ⟶ A) (hv : IsTangent v) :
    (red W ≫ epsLift v) ≫ (snd (baseOver (Sp W)) A).left = 𝟙 (Sp W) ≫ eSec A := by
  rw [Category.assoc, epsLift_snd, Category.id_comp]
  exact hv

open Classical in
theorem exists_jets [IsLocalRing W] (P : PolAV (Sp W)) (ρ : LB.Gen (P.L.pull (eSec P.A))) (k : ℕ) {I : Type}
    (t : I → LB.Sec (LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W))))) {g : ℕ} (v : Fin g → (epsR W ⟶ P.A))
    (hv : ∀ j, IsTangent (v j)) :
    ∃ (i₀ : P.L.ι) (c : Fin g → W) (ϑ : I → W) (J : I → Fin g → W),
      ⊤ ≤ (𝟙 (Sp W) ≫ eSec P.A) ⁻¹ᵁ P.L.U i₀ ∧
      ∀ i j, valR (epsLift (v j)) ((LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W)))).U fun _ => i₀) ((t i).f fun _ => i₀) =
        TrivSqZeroExt.inl (valR (𝟙 (Sp W)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) *
          (TrivSqZeroExt.inl (ϑ i) + TrivSqZeroExt.inr (J i j + c j * ϑ i)) := by
  have hL := P.isLB
  obtain ⟨i₀, hi₀⟩ := exists_chart hL ((eSec P.A : Sp W ⟶ P.A.left).base (IsLocalRing.closedPoint W))
  have htop : ⊤ ≤ (𝟙 (Sp W) ≫ eSec P.A) ⁻¹ᵁ P.L.U i₀ := by
    rw [Category.id_comp, Scheme.preimage_eq_top_of_closedPoint_mem (eSec P.A : Sp W ⟶ P.A.left) hi₀]
  have hρt : ⊤ ≤ (𝟙 (Sp W)) ⁻¹ᵁ ((P.L.pull (eSec P.A)).U fun _ => i₀) := fun p _ =>
    Set.mem_iInter.2 fun _ => by
      have := htop (show p ∈ (⊤ : (Sp W).Opens) from trivial)
      exact this
  set u := valR (𝟙 (Sp W)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val with hu_def
  have hu : IsUnit u := by
    rw [hu_def, valR, dif_pos hρt]
    exact ((ρ.s _).isUnit.map _).map _
  set ui := Ring.inverse (u ^ k)
  have hui : u ^ k * ui = 1 := Ring.mul_inverse_cancel _ (hu.pow k)
  have hch : ∀ j, ⊤ ≤ (epsLift (v j)) ⁻¹ᵁ ((LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W)))).U fun _ => i₀) := fun j =>
    top_le_of_red _ _ fun p _ => Set.mem_iInter.2 fun _ => by
      have := htop (show p ∈ (⊤ : (Sp W).Opens) from trivial)
      rw [← red_epsLift_snd (v j) (hv j)] at this
      exact this
  refine ⟨i₀, 0, fun i => if hn : Nonempty (Fin g) then
      ui * (valR (epsLift (v hn.some)) ((LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W)))).U fun _ => i₀)
        ((t i).f fun _ => i₀)).fst else 0,
    fun i j => ui * (valR (epsLift (v j)) ((LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W)))).U fun _ => i₀)
        ((t i).f fun _ => i₀)).snd, htop, fun i j => ?_⟩
  have hn : Nonempty (Fin g) := ⟨j⟩
  simp only [dif_pos hn]
  have hf : (valR (epsLift (v hn.some)) ((LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W)))).U fun _ => i₀)
        ((t i).f fun _ => i₀)).fst =
      (valR (epsLift (v j)) ((LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W)))).U fun _ => i₀) ((t i).f fun _ => i₀)).fst := by
    rw [valR_fst _ _ (hch _), valR_fst _ _ (hch _), red_epsLift _ _ (hv _) (hv j)]
  rw [hf]
  ext
  · simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inr, add_zero]
    rw [← _root_.mul_assoc, hui, _root_.one_mul]
  · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_add,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, add_zero, Pi.zero_apply, zero_mul,
      smul_eq_mul, MulOpposite.smul_eq_mul_unop, zero_add, MulOpposite.unop_op]
    rw [← _root_.mul_assoc, hui, _root_.one_mul]

end GlobalTheory.MBLow.JetEx

namespace GlobalTheory.MBLow.JetEx

variable {W : Type} [CommRing W]

theorem exists_symLift_tr [IsNoetherianRing W] [IsLocalRing W] (P : PolAV (Sp W)) (ρ : LB.Gen (P.L.pull (eSec P.A)))
    (hρ : ρ.IsGen) (m : ℕ) (hm : Odd m) (hmu : IsUnit (m : W))
    (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (Over.mk (𝟙 (Sp W))))) (x : Over.mk (𝟙 (Sp W)) ⟶ P.A)
    (hx : x ^ (m ^ 2) = 1) :
    ∃ (U : ThetaGrp P.A P.L ((m ^ 2 : ℕ) : ℤ) (Over.mk (𝟙 (Sp W))))
      (t : LB.Sec (LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) (Over.mk (𝟙 (Sp W))))),
      SymLift P.A P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x U ∧ Tr P ρ m th U t := by
  have hLaw : Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hL := P.isLB
  let T : Over (Sp W) := Over.mk (𝟙 (Sp W))
  have hu : IsUnit ((m ^ 2 : ℕ) : Γ(Sp W, ⊤)) := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of W)).commRingCatIsoToRingEquiv.symm
    rw [← map_natCast e]
    exact (by rw [Nat.cast_pow]; exact hmu.pow 2 : IsUnit ((m ^ 2 : ℕ) : W)).map e
  obtain ⟨hex, -⟩ := hLaw.symLift _ P (m ^ 2) hm.pow hu T x hx
  obtain ⟨V, hV, θ₀, hθ₀⟩ := hex (IsLocalRing.closedPoint W)
  have hVt : V = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem (𝟙 (Sp W)) hV
  subst hVt
  let h : T ⟶ overRes (T := T) ⊤ := Over.homMk T.left.topIso.inv (by
    show T.left.topIso.inv ≫ (⊤ : T.left.Opens).ι ≫ T.hom = T.hom
    rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp])
  have hh : h ≫ overResι (T := T) ⊤ = 𝟙 T := Over.OverMorphism.ext T.left.toIso_inv_ι
  obtain ⟨θ, hθ⟩ := GlobalLift.exists_symLift_pull hL h hθ₀
  rw [← Category.assoc, hh, Category.id_comp] at hθ
  obtain ⟨α₀, hα₀⟩ := hLaw.mulPull _ P m
  have e₁ : (snd T P.A).left ≫ (mulA P.A m).left = (snd T P.A ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α₁, hα₁, -⟩ := exists_gen hL (φ' := ![(snd T P.A).left, (snd T P.A ^ m).left])
    (ε' := ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg₂ (fun q n => f q ^ n) (Category.comp_id _) (Nat.cast_pow m 2).symm
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen P.L ![𝟙 P.A.left, (mulA P.A m).left] ![(m : ℤ) ^ 2, -1] α₀ (snd T P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  obtain ⟨α, hα, hn⟩ := GlobalTheory.NormTheta.exists_normalised hL hρ m _ _ (((m ^ 2 : ℕ) : ℤ) - 1) (by simp) α₁ hα₁
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL (mulT P.A T m) (snd T P.A ^ m) (lift_snd _ _)
    ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α hα th
  obtain ⟨t, ht⟩ := ThetaPtExist.exists_isTwistPull hL (translT P.A θ.pt) (translPt P.A θ.pt) (lift_snd _ _)
    ((m ^ 2 : ℕ) : ℤ) ((m ^ 2 : ℕ) : ℤ) θ.φ θ.isGen s₁
  exact ⟨θ, t, hθ, α, s₁, hα, hn, hs₁, ht⟩

end GlobalTheory.MBLow.JetEx

namespace GlobalTheory.MBLow

theorem exists_thJet_local : ∀ (W : Type) [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W] (x : KeyIn W)
    (g : ℕ) (hg : x.P.g = g) (m : ℕ), Odd m → IsUnit (m : W) → ∀ (I : Type) (pt : I → (baseOver (Sp W) ⟶ x.P.A)),
    (∀ i, pt i ^ (m ^ 2) = 1) → ∃ ϑ J, ThJet x hg m pt ϑ J := by
  intro W _ _ _ _ x g hg m hm hmu I pt hpt
  choose U t hUt using fun i =>
    JetEx.exists_symLift_tr x.P x.rig x.rig_gen m hm hmu (TrSec.thSec x.P x.th) (pt i) (hpt i)
  obtain ⟨i₀, c, ϑ, J, htop, hval⟩ :=
    JetEx.exists_jets x.P x.rig (m ^ 2) t (fun j => x.v (j.cast hg.symm)) (fun j => x.basis.1 _)
  exact ⟨ϑ, J, TrSec.thSec x.P x.th, TrSec.projectionPullbackSectionBaseProduct_isInverseImage x.P x.th, U, t, i₀, c, fun i => hUt i, htop, hval⟩

end GlobalTheory.MBLow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueNthRoots
section
open GlobalTheory.MonoHom

noncomputable section

namespace GlobalTheory.PerRoot

variable {X : Type} [AddCommGroup X]

def halfForm {r : ℕ} (e : Module.Basis (Fin r) ℤ X) (i j : Fin r) : LinearMap.BilinForm ℤ X :=
  if i < j then pform e i j + pform e j i else if i = j then pform e i i else 0

theorem halfForm_symm {r : ℕ} (e : Module.Basis (Fin r) ℤ X) (i j : Fin r) (x y : X) :
    halfForm e i j x y = halfForm e i j y x := by
  unfold halfForm; split_ifs <;> simp [pform_apply] <;> ring

theorem halfForm_basis {r : ℕ} (e : Module.Basis (Fin r) ℤ X) (i j i₀ j₀ : Fin r) :
    halfForm e i j (e i₀) (e j₀) = if i = min i₀ j₀ ∧ j = max i₀ j₀ then 1 else 0 := by
  unfold halfForm
  rcases lt_trichotomy i₀ j₀ with h | rfl | h
  · rw [min_eq_left h.le, max_eq_right h.le]
    split_ifs <;> simp [pform_apply, Module.Basis.coord_apply, Finsupp.single_apply] <;> (try split_ifs) <;> (try subst_vars) <;> omega
  · simp only [min_self, max_self]
    split_ifs <;> simp [pform_apply, Module.Basis.coord_apply, Finsupp.single_apply] <;> (try split_ifs) <;> (try subst_vars) <;> omega
  · rw [min_eq_right h.le, max_eq_left h.le]
    split_ifs <;> simp [pform_apply, Module.Basis.coord_apply, Finsupp.single_apply] <;> (try split_ifs) <;> (try subst_vars) <;> omega

theorem eq_sum_halfForm {r : ℕ} (e : Module.Basis (Fin r) ℤ X) (β : LinearMap.BilinForm ℤ X)
    (hβ : ∀ x y, β x y = β y x) :
    β = ∑ p : Fin r × Fin r, β (e p.1) (e p.2) • halfForm e p.1 p.2 := by
  refine LinearMap.ext_basis e e fun i₀ j₀ => ?_
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, halfForm_basis, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (min i₀ j₀, max i₀ j₀)]
  · simp only [and_self, if_true]
    rcases le_total i₀ j₀ with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h, hβ]
  · intro p _ hp; rw [if_neg]; rintro ⟨h1, h2⟩; exact hp (Prod.ext h1 h2)
  · intro h; exact absurd (Finset.mem_univ _) h

theorem bimul_ext {G : Type} [CommGroup G] {r : ℕ} (e : Module.Basis (Fin r) ℤ X) (f g : X → X → G)
    (hf : ∀ a a' b, f (a + a') b = f a b * f a' b) (hf' : ∀ a b b', f a (b + b') = f a b * f a b')
    (hg : ∀ a a' b, g (a + a') b = g a b * g a' b) (hg' : ∀ a b b', g a (b + b') = g a b * g a b')
    (h : ∀ i j, f (e i) (e j) = g (e i) (e j)) : f = g := by
  have key : ∀ (φ ψ : X → G), (∀ a a', φ (a + a') = φ a * φ a') → (∀ a a', ψ (a + a') = ψ a * ψ a') →
      (∀ i, φ (e i) = ψ (e i)) → φ = ψ := by
    intro φ ψ hφ hψ hi
    let Φ : X →+ Additive G := AddMonoidHom.mk' (fun a => Additive.ofMul (φ a)) (fun a a' => by simp [hφ])
    let Ψ : X →+ Additive G := AddMonoidHom.mk' (fun a => Additive.ofMul (ψ a)) (fun a a' => by simp [hψ])
    have hL : Φ.toIntLinearMap = Ψ.toIntLinearMap := e.ext fun i => by simp [Φ, Ψ, hi]
    funext a
    have := congrArg (fun L : X →ₗ[ℤ] Additive G => Additive.toMul (L a)) hL
    simpa [Φ, Ψ] using this
  have h1 : ∀ j a, f a (e j) = g a (e j) := fun j => congrFun
    (key (fun a => f a (e j)) (fun a => g a (e j)) (fun a a' => hf a a' _) (fun a a' => hg a a' _) (fun i => h i j))
  funext a
  exact key (f a) (g a) (hf' a) (hg' a) (fun j => h1 j a)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def IsSymBasis (ε : ι → LinearMap.BilinForm ℤ X) : Prop :=
  (∀ k x y, ε k x y = ε k y x) ∧ LinearIndependent ℤ ε ∧
    ∀ β : LinearMap.BilinForm ℤ X, (∀ x y, β x y = β y x) → β ∈ Submodule.span ℤ (Set.range ε)

theorem exists_coords {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) {r : ℕ} (e : Module.Basis (Fin r) ℤ X) :
    ∃ c : Fin r × Fin r → ι → ℤ, ∀ p, ∑ k, c p k • ε k = halfForm e p.1 p.2 := by
  have : ∀ p : Fin r × Fin r, ∃ c : ι → ℤ, ∑ k, c k • ε k = halfForm e p.1 p.2 := fun p =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).1 (hε.2.2 _ (halfForm_symm e p.1 p.2))
  choose c hc using this
  exact ⟨c, hc⟩

theorem dual_coords {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) {r : ℕ} (e : Module.Basis (Fin r) ℤ X)
    {c : Fin r × Fin r → ι → ℤ} (hc : ∀ p, ∑ k, c p k • ε k = halfForm e p.1 p.2) (k' k : ι) :
    ∑ p, ε k' (e p.1) (e p.2) * c p k = if k' = k then 1 else 0 := by
  have h1 : ε k' = ∑ k, (∑ p, ε k' (e p.1) (e p.2) * c p k) • ε k := by
    conv_lhs => rw [eq_sum_halfForm e (ε k') (hε.1 k')]
    simp_rw [← hc, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have h2 : ε k' = ∑ k, (if k' = k then (1 : ℤ) else 0) • ε k := by simp
  have h3 : ∑ k, ((∑ p, ε k' (e p.1) (e p.2) * c p k) - (if k' = k then 1 else 0)) • ε k = 0 := by
    simp_rw [sub_smul, Finset.sum_sub_distrib, ← h1, ← h2, sub_self]
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hε.2.1 _ h3 k)

variable {G : Type} [CommGroup G]

theorem zpow_sumF {κ : Type} (s : Finset κ) (a : G) (f : κ → ℤ) : a ^ (∑ p ∈ s, f p) = ∏ p ∈ s, a ^ f p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add, ih]

theorem eq_one_of_prod_zpow {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) [Module.Free ℤ X] [Module.Finite ℤ X]
    (u : ι → G) (h : ∀ x y, ∏ k, u k ^ ε k x y = 1) (k : ι) : u k = 1 := by
  let e := Module.finBasis ℤ X
  obtain ⟨c, hc⟩ := exists_coords hε e
  calc u k = ∏ k', u k' ^ (if k' = k then (1 : ℤ) else 0) := by simp
    _ = ∏ k', u k' ^ (∑ p, ε k' (e p.1) (e p.2) * c p k) := by simp_rw [dual_coords hε e hc]
    _ = ∏ p, (∏ k', u k' ^ ε k' (e p.1) (e p.2)) ^ c p k := by
      simp_rw [← Finset.prod_zpow, zpow_sumF, ← zpow_mul]
      exact Finset.prod_comm
    _ = 1 := by simp [h]

theorem existsUnique_coeff {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) [Module.Free ℤ X] [Module.Finite ℤ X]
    (q : X → X → G) (hsym : ∀ x y, q x y = q y x) (hadd : ∀ x x' y, q (x + x') y = q x y * q x' y) :
    ∃! σ : ι → G, ∀ x y, q x y = ∏ k, σ k ^ ε k x y := by
  let e := Module.finBasis ℤ X
  obtain ⟨c, hc⟩ := exists_coords hε e
  have hadd' : ∀ x y y', q x (y + y') = q x y * q x y' := fun x y y' => by
    rw [hsym, hadd, hsym y, hsym y']
  have hF : ∀ x y, ∏ k, (∏ p, q (e p.1) (e p.2) ^ c p k) ^ ε k x y =
      ∏ p : Fin (Module.finrank ℤ X) × Fin (Module.finrank ℤ X), q (e p.1) (e p.2) ^ halfForm e p.1 p.2 x y := by
    intro x y
    simp_rw [← Finset.prod_zpow, ← zpow_mul]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← zpow_sumF, ← hc p]
    simp [LinearMap.sum_apply, mul_comm]
  refine ⟨fun k => ∏ p, q (e p.1) (e p.2) ^ c p k, fun x y => ?_, fun σ hσ => funext fun k => ?_⟩
  · rw [hF]
    have := bimul_ext e q (fun x y => ∏ p : Fin (Module.finrank ℤ X) × Fin (Module.finrank ℤ X),
        q (e p.1) (e p.2) ^ halfForm e p.1 p.2 x y) hadd hadd'
      (fun a a' b => by simp only [map_add (f := _), LinearMap.add_apply, zpow_add, Finset.prod_mul_distrib])
      (fun a b b' => by simp only [map_add (f := _), zpow_add, Finset.prod_mul_distrib])
      (fun i j => by
        simp only [halfForm_basis]
        rw [Finset.prod_eq_single (min i j, max i j)]
        · simp only [and_self, if_true, zpow_one]
          rcases le_total i j with h | h
          · rw [min_eq_left h, max_eq_right h]
          · rw [min_eq_right h, max_eq_left h, hsym]
        · intro p _ hp; rw [if_neg, zpow_zero]; rintro ⟨h1, h2⟩; exact hp (Prod.ext h1 h2)
        · intro h; exact absurd (Finset.mem_univ _) h)
    exact congrFun (congrFun this x) y
  · have h0 : ∀ x y, ∏ k, (σ k / ∏ p, q (e p.1) (e p.2) ^ c p k) ^ ε k x y = 1 := fun x y => by
      simp_rw [div_zpow, Finset.prod_div_distrib, ← hσ, hF]
      rw [div_eq_one]
      have := bimul_ext e q (fun x y => ∏ p : Fin (Module.finrank ℤ X) × Fin (Module.finrank ℤ X),
          q (e p.1) (e p.2) ^ halfForm e p.1 p.2 x y) hadd hadd'
        (fun a a' b => by simp only [map_add (f := _), LinearMap.add_apply, zpow_add, Finset.prod_mul_distrib])
        (fun a b b' => by simp only [map_add (f := _), zpow_add, Finset.prod_mul_distrib])
        (fun i j => by
          simp only [halfForm_basis]
          rw [Finset.prod_eq_single (min i j, max i j)]
          · simp only [and_self, if_true, zpow_one]
            rcases le_total i j with h | h
            · rw [min_eq_left h, max_eq_right h]
            · rw [min_eq_right h, max_eq_left h, hsym]
          · intro p _ hp; rw [if_neg, zpow_zero]; rintro ⟨h1, h2⟩; exact hp (Prod.ext h1 h2)
          · intro h; exact absurd (Finset.mem_univ _) h)
      exact congrFun (congrFun this x) y
    exact div_eq_one.1 (eq_one_of_prod_zpow hε _ h0 k)

theorem eq_of_prod_zpow {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) [Module.Free ℤ X] [Module.Finite ℤ X]
    (s s' : ι → G) (h : ∀ x y, ∏ k, s k ^ ε k x y = ∏ k, s' k ^ ε k x y) : s = s' := by
  funext k
  refine div_eq_one.1 (eq_one_of_prod_zpow hε (fun k => s k / s' k) (fun x y => ?_) k)
  simp_rw [div_zpow, Finset.prod_div_distrib, h, div_self']

theorem pow_eq_pow_of_prod {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) [Module.Free ℤ X] [Module.Finite ℤ X]
    (n : ℕ) (s s' : ι → G) (h : ∀ x y, ∏ k, s k ^ ((n : ℤ) * ε k x y) = ∏ k, s' k ^ ((n : ℤ) * ε k x y)) (k : ι) :
    s k ^ n = s' k ^ n := by
  have := congrFun (eq_of_prod_zpow hε (fun k => s k ^ n) (fun k => s' k ^ n) fun x y => by
    simp_rw [← zpow_natCast, ← zpow_mul]; exact h x y) k
  exact this

theorem isSymBasis_mul : IsSymBasis (fun _ : Fin 1 => (LinearMap.mul ℤ ℤ : LinearMap.BilinForm ℤ ℤ)) := by
  refine ⟨fun _ x y => mul_comm x y, ?_, fun β _ => ?_⟩
  · rw [linearIndependent_unique_iff]
    intro h
    have := LinearMap.congr_fun₂ h 1 1
    simp at this
  · refine (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨fun _ => β 1 1, ?_⟩
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    simp only [Finset.univ_unique, Finset.sum_singleton, LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
    have hx : x = x • (1 : ℤ) := by simp
    have hy : y = y • (1 : ℤ) := by simp
    rw [hx, hy, LinearMap.map_smul₂, LinearMap.map_smul]
    simp only [smul_eq_mul]; ring

end GlobalTheory.PerRoot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FerrandGlueFlatArtinianFibreProduct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

set_option autoImplicit false

namespace GlobalTheory.FerrandGlue

theorem kernel_nilpotent : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₂ → Nontrivial R₀ → IsNilpotent (RingHom.ker g₁.hom) := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hg₂ hR₀
  have hT := (Types.isPullback_iff _ _ _ _).1 (hP.map (forget CommRingCat))
  have hf₁ : Function.Surjective f₁ := by
    intro r
    obtain ⟨s, hs⟩ := hg₂ (g₁ r)
    obtain ⟨p, hp, -⟩ := hT.2.2 r s hs.symm
    exact ⟨p, hp⟩
  let J : Ideal P := (RingHom.ker g₁.hom).comap f₁.hom
  have hJ : J ≤ IsLocalRing.maximalIdeal P := IsLocalRing.le_maximalIdeal (by
    intro h
    have h1 : (1 : P) ∈ J := h ▸ Submodule.mem_top
    simp [J] at h1)
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := P)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
  refine ⟨n, ?_⟩
  have hmap : RingHom.ker g₁.hom = J.map f₁.hom := (Ideal.map_comap_of_surjective _ hf₁ _).symm
  rw [hmap, ← Ideal.map_pow, Ideal.zero_eq_bot, eq_bot_iff]
  calc (J ^ n).map f₁.hom ≤ ((IsLocalRing.maximalIdeal P) ^ n).map f₁.hom := Ideal.map_mono (Ideal.pow_right_mono hJ n)
    _ = ⊥ := by rw [hn, Ideal.zero_eq_bot, Ideal.map_bot]

theorem thickening_of_isPullback : ∀ (R₁ R₀ : CommRingCat.{0}) (g : R₁ ⟶ R₀) (Y₁ Y₀ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec R₁) (p₀ : Y₀ ⟶ Spec R₀) (i : Y₀ ⟶ Y₁), IsPullback i p₀ p₁ (Spec.map g) → Function.Surjective g → IsNilpotent (RingHom.ker g.hom) → IsClosedImmersion i ∧ Surjective i := by
  intro R₁ R₀ g Y₁ Y₀ p₁ p₀ i h hg hn
  have hc : IsClosedImmersion (Spec.map g) := IsClosedImmersion.spec_of_surjective g hg
  have hs : Surjective (Spec.map g) := by
    constructor
    intro x
    obtain ⟨n, hn⟩ := hn
    have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker g.hom : Set R₁) := fun a ha => by
      refine x.isPrime.mem_of_pow_mem n ?_
      have := Ideal.pow_mem_pow ha n
      rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
      rw [this]
      exact zero_mem _
    rw [← range_comap_of_surjective _ g.hom hg] at hx
    exact hx
  exact ⟨MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip hc,
    MorphismProperty.of_isPullback (P := @Surjective) h.flip hs⟩

theorem ferrand_glue_artinian : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (Y₁ : Over (Spec R₁)) (Y₂ : Over (Spec R₂)) (Y₀ : Over (Spec R₀)) (i₁ : Y₀.left ⟶ Y₁.left) (i₂ : Y₀.left ⟶ Y₂.left), IsPullback i₁ Y₀.hom Y₁.hom (Spec.map g₁) → IsPullback i₂ Y₀.hom Y₂.hom (Spec.map g₂) → Flat Y₁.hom → Flat Y₂.hom → ∃ (Y : Over (Spec P)) (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left), IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) ∧ IsPullback j₂ Y₂.hom Y.hom (Spec.map f₂) ∧ Flat Y.hom ∧ IsPushout i₁ i₂ j₁ j₂ := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hg₁ hg₂ Y₁ Y₂ Y₀ i₁ i₂ h₁ h₂ hf₁ hf₂
  by_cases hR₀ : Subsingleton R₀
  · exact _root_.GlobalTheory.PinchDeg.glue_of_subsingleton P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hR₀ hloc hart hg₁ hg₂ Y₁ Y₂ Y₀ i₁ i₂ h₁ h₂ hf₁ hf₂
  rw [not_subsingleton_iff_nontrivial] at hR₀
  have hn₁ := kernel_nilpotent P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hg₂ hR₀
  have hn₂ := kernel_nilpotent P R₂ R₁ R₀ f₂ f₁ g₂ g₁ hP.flip hloc hart hg₁ hR₀
  obtain ⟨hc₁, hs₁⟩ := thickening_of_isPullback R₁ R₀ g₁ Y₁.left Y₀.left Y₁.hom Y₀.hom i₁ h₁ hg₁ hn₁
  obtain ⟨hc₂, hs₂⟩ := thickening_of_isPullback R₂ R₀ g₂ Y₂.left Y₀.left Y₂.hom Y₀.hom i₂ h₂ hg₂ hn₂
  obtain ⟨Y, j₁, j₂, hw, hpo, hj₁, hj₂, hV⟩ := _root_.GlobalTheory.exists_pushout_of_nilpotent_thickenings Y₀.left Y₁.left Y₂.left i₁ i₂ hc₁ hc₂ hs₁ hs₂
    (_root_.GlobalTheory.NilThicken.isNilpotent_ker_app R₁ R₀ g₁ Y₁.left Y₀.left Y₁.hom Y₀.hom i₁ h₁ hg₁ hn₁)
    (_root_.GlobalTheory.NilThicken.isNilpotent_ker_app R₂ R₀ g₂ Y₂.left Y₀.left Y₂.hom Y₀.hom i₂ h₂ hg₂ hn₂)
  have hcomm : i₁ ≫ Y₁.hom ≫ Spec.map f₁ = i₂ ≫ Y₂.hom ≫ Spec.map f₂ := by
    rw [← Category.assoc, h₁.w, ← Category.assoc, h₂.w, Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hP.w]
  let y : Y ⟶ Spec P := hpo.desc (Y₁.hom ≫ Spec.map f₁) (Y₂.hom ≫ Spec.map f₂) hcomm
  obtain ⟨k₁, k₂, kf⟩ := _root_.GlobalTheory.FerrandFlat.flat_pushout P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hg₁ hg₂ hn₁ hn₂ Y₁.left Y₂.left Y₀.left Y₁.hom Y₂.hom Y₀.hom i₁ i₂ h₁ h₂ hf₁ hf₂ Y j₁ j₂ hw hj₁ hj₂ hV y (hpo.inl_desc _ _ _) (hpo.inr_desc _ _ _)
  exact ⟨Over.mk y, j₁, j₂, k₁, k₂, kf, hpo⟩

end GlobalTheory.FerrandGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatToSpecField
section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

namespace GlobalTheory

theorem flat_to_spec_field : ∀ (K : Type) [Field K] (Z : Scheme.{0}) (f : Z ⟶ Sp K), Flat f := by
  intro K _ Z f
  haveI : IsIntegral (Sp K) := by unfold Sp; infer_instance
  haveI : Subsingleton (Sp K) := by unfold Sp; infer_instance
  infer_instance

end GlobalTheory
end

