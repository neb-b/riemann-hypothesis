module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2336
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelatingConstantMemTraitFractionField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.RatConst

open scoped TensorProduct

theorem mem_range_of_tmul_eq {K F O : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup O] [Module K O]
    {t u : O} {c : F} (ht : t ≠ 0) (h : (1 : F) ⊗ₜ[K] t = c ⊗ₜ[K] u) : ∃ x : K, algebraMap K F x = c := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one K ht
  have e := congrArg (fun v => TensorProduct.rid K F (LinearMap.lTensor F l v)) h
  simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, hl, one_smul, Algebra.smul_def] at e
  refine ⟨(l u)⁻¹, ?_⟩
  rw [map_inv₀]
  exact inv_eq_of_mul_eq_one_right (by simpa using e.symm)

theorem gs_spec {A B : CommRingCat.{0}} (h : A ⟶ B) (y : Spec B) (x : A) :
    gs (Spec.map h) y ⊤ ((Scheme.ΓSpecIso A).inv.hom x) = gs (𝟙 _) y ⊤ ((Scheme.ΓSpecIso B).inv.hom (h.hom x)) := by
  have e := congrArg (fun q => q.hom x) (Scheme.ΓSpecIso_inv_naturality h)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [e]
  exact ((gs_pull (𝟙 _) (Spec.map h) y ⊤ trivial _).trans (by rw [Category.id_comp])).symm

theorem mem_of_stalk {X Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (U : X.Opens) (hz : f z ∈ U) (y : Spec (Z.presheaf.stalk z)) :
    f (Z.fromSpecStalk z y) ∈ U := by
  have : Z.fromSpecStalk z y ⤳ z := by
    have := Set.mem_range_self (f := Z.fromSpecStalk z) y
    rwa [Scheme.range_fromSpecStalk] at this
  exact (this.map f.continuous).mem_open U.isOpen hz

theorem gs_stalk {X Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (U : X.Opens) (hz : f z ∈ U) (a : Γ(X, U)) {B : CommRingCat.{0}}
    (h : Z.presheaf.stalk z ⟶ B) (y : Spec B) :
    gs (Spec.map h ≫ Z.fromSpecStalk z ≫ f) y U a = gs (𝟙 _) y ⊤ ((Scheme.ΓSpecIso B).inv.hom (h.hom (gs f z U a))) := by
  have m := mem_of_stalk f z U hz (Spec.map h y)
  rw [← gs_spec, ← Category.assoc, ← gs_pull _ f y U m, ← gs_pull _ (Z.fromSpecStalk z) y _ m,
    Scheme.fromSpecStalk_app (U := f ⁻¹ᵁ U) hz, gs_eq f z U hz]
  exact gs_res (Spec.map h) y le_top m _

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (c : F), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval s (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → (∃ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (_ : p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α) (_ : p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _))) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J ∧ sval σ p z J ≠ 0) → ∃ x : FractionRing W, algebraMap (FractionRing W) F x = c := by
  intro R _ _ _ _ D C k W _ _ _ T F _ _ _ hF σ s c H ⟨Z, p, p', h₁, h₂, z, J, hJ, hne⟩
  let O := Z.presheaf.stalk z
  obtain ⟨ρ, hρ⟩ : ∃ ρ : CommRingCat.of F ⟶ O,
      Spec.map ρ = Z.fromSpecStalk z ≫ p' ≫ (fst (TFK (R := R) F) C.A.A).left := ⟨Spec.preimage _, Spec.map_preimage _⟩
  letI : Algebra (FractionRing W) O := (ρ.hom.comp (algebraMap (FractionRing W) F)).toAlgebra
  let B := CommRingCat.of (F ⊗[FractionRing W] O)
  let iL : CommRingCat.of F ⟶ B := CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let iR : O ⟶ B := CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := FractionRing W) (A := F) (B := O)).toRingHom
  have hK : ∀ x : FractionRing W, iR.hom (ρ.hom (algebraMap _ F x)) = iL.hom (algebraMap _ F x) := fun x =>
    ((Algebra.TensorProduct.includeRight (R := FractionRing W) (A := F) (B := O)).commutes x).trans rfl
  let g : Spec B ⟶ Z := Spec.map iR ≫ Z.fromSpecStalk z
  have hg : g ≫ p' ≫ (fst (TFK (R := R) F) C.A.A).left = Spec.map (ρ ≫ iR) := by
    rw [Spec.map_comp, hρ, Category.assoc]
  have w : (g ≫ p' ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.A.A.hom = Spec.map iL ≫ jFK (R := R) F := by
    have e : (snd (TFK (R := R) F) C.A.A).left ≫ C.A.A.hom = (fst (TFK (R := R) F) C.A.A).left ≫ jFK (R := R) F :=
      (Over.w _).trans (Over.w (fst (TFK (R := R) F) C.A.A)).symm
    have e' : (g ≫ p' ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.A.A.hom =
        (g ≫ p' ≫ (fst (TFK (R := R) F) C.A.A).left) ≫ jFK (R := R) F := by simp only [Category.assoc, e]
    rw [e', hg]
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_comp _ _))
    refine CommRingCat.hom_ext (IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_))
    exact (congrArg (fun q => iR.hom (ρ.hom q)) (hF r)).trans ((hK _).trans (congrArg iL.hom (hF r).symm))
  obtain ⟨q, q₁, q₂⟩ : ∃ q : Spec B ⟶ (TFK (R := R) F ⊗ C.A.A).left,
      q ≫ (fst (TFK (R := R) F) C.A.A).left = Spec.map iL ∧
      q ≫ (snd (TFK (R := R) F) C.A.A).left = g ≫ p' ≫ (snd (TFK (R := R) F) C.A.A).left := by
    let T' : Over (Sp (FractionRing R)) := Over.mk (Spec.map iL ≫ jFK (R := R) F)
    let a : T' ⟶ TFK (R := R) F := Over.homMk (Spec.map iL) rfl
    let b : T' ⟶ C.A.A := Over.homMk (g ≫ p' ≫ (snd (TFK (R := R) F) C.A.A).left) w
    exact ⟨(lift a b).left, congrArg (·.left) (lift_fst a b), congrArg (·.left) (lift_snd a b)⟩
  have k₁ : (g ≫ p) ≫ T.β = q ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α := by
    rw [← Category.assoc q, q₂, Category.assoc, h₁]; simp only [Category.assoc]
  have k₂ : (g ≫ p) ≫ T.G.hom = q ≫ (fst (TFK (R := R) F) C.A.A).left ≫
      spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) := by
    rw [← Category.assoc q, q₁, Category.assoc, h₂, ← Category.assoc p', ← Category.assoc g, hg]
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_comp _ _))
    exact CommRingCat.hom_ext (RingHom.ext fun r => hK _)
  let u : O := sval s (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J
  let t : O := sval σ p z J
  have key : iR.hom t = iL.hom c * iR.hom u := by
    apply (Scheme.ΓSpecIso B).symm.commRingCatIsoToRingEquiv.injective
    refine fn_ext (V := ⊤) fun y _ => ?_
    obtain ⟨J', hJ', e⟩ := exists_good C.P.L.L C.P.L.isLB y (K := Unit) (fun _ => (g ≫ p) ≫ T.β) (fun _ => J (p ≫ T.β))
      (fun _ _ _ => rfl) (fun _ => mem_of_stalk (p ≫ T.β) z _ (hJ _) (Spec.map iR y))
    have e := e ()
    have := H _ (g ≫ p) q k₁ k₂ y J' hJ'
    rw [sval_of σ _ y J' (fun _ => J (p ≫ T.β)) (fun _ => e),
      sval_of s _ y J' (fun _ => J ((p' ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.α)) (fun _ => by
        rw [Category.assoc, ← k₁, Category.assoc p', ← h₁]; exact e), q₁, q₂] at this
    have a₁ := gs_stalk p z _ (hJ.mem (fun _ : Fin 1 => T.β) p) (σ.f fun _ => J (p ≫ T.β)) iR y
    have a₂ := gs_stalk (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z _
      (hJ.mem (fun _ : Fin 1 => C.α) (p' ≫ (snd (TFK (R := R) F) C.A.A).left))
      (s.f fun _ => J ((p' ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.α)) iR y
    have a₃ := gs_spec iL y c
    simp only [g, Category.assoc] at this a₁ a₂
    refine a₁.symm.trans (this.trans (Eq.trans (congrArg₂ (· * ·) a₃ a₂) ?_))
    refine (gs_mul _ y ⊤ trivial _ _).symm.trans (congrArg _ ?_)
    simp only [u, sval, Category.assoc]
    exact (map_mul _ _ _).symm
  refine mem_range_of_tmul_eq (O := O) (t := t) (u := u) hne (key.trans ?_)
  exact (Algebra.TensorProduct.tmul_mul_tmul c 1 1 u).trans (by rw [_root_.mul_one, _root_.one_mul])

end GlobalTheory.Mum.RatConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprEqZeroOfCardNe
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.LineForm

namespace GlobalTheory.PullTop

theorem repr_eq_zero_of_card_ne {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M] [LinearOrder I]
    (b : Module.Basis I R M) {k : ℕ} (x : ⋀[R]^k M) {S : Finset I} (hS : S.card ≠ k) :
    b.ExteriorAlgebra.repr (x : ExteriorAlgebra R M) S = 0 := by
  have h : (Finsupp.lapply S ∘ₗ b.ExteriorAlgebra.repr.toLinearMap ∘ₗ (⋀[R]^k M).subtype) = 0 := by
    refine (b.exteriorPower k).ext fun s => ?_
    have hs : (s : Finset I) ≠ S := fun e => hS (e ▸ s.2)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, ← ExteriorAlgebra.basis_eq_coe_basis,
      LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply, LinearMap.zero_apply]
    exact Finsupp.single_eq_of_ne' hs
  exact LinearMap.congr_fun h x

end GlobalTheory.PullTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedPresentationCocycleMemBialgebraSymmetr
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

open Algebra.TensorProduct in
theorem coc_mem_symCocycles (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (hg : IsSymCoc d.g) (n : ℕ) :
    d.coc n ∈ symCocycles R (G.A n) := by
  set H := G.A n

  have V : ∀ (D : Type) [CommRing D] [Algebra R D] (φ ψ : H →ₐ[R] D),
      lift φ ψ (fun _ _ ↦ Commute.all _ _) (d.coc n) = d.g D (spOver φ ≫ t.y n) (spOver ψ ≫ t.y n) -
        ((fv d.f H D (toConv φ * toConv ψ).ofConv (t.y n) + (toConv φ * toConv ψ).ofConv (d.h n)) -
          (fv d.f H D φ (t.y n) + φ (d.h n)) - (fv d.f H D ψ (t.y n) + ψ (d.h n))) :=
    fun D _ _ φ ψ ↦ GlobalTheory.T.cocycle_tensorLift_apply_eq_twoPointValue R A p G t c d n D φ ψ
  have M : ∀ (D : Type) [CommRing D] [Algebra R D] (φ ψ : H →ₐ[R] D),
      spOver (toConv φ * toConv ψ).ofConv ≫ t.y n = (spOver φ ≫ t.y n) * (spOver ψ ≫ t.y n) :=
    fun D _ _ φ ψ ↦ t.mul n D (toConv φ) (toConv ψ)
  rw [mem_symCocycles]
  constructor
  · let i1 : H →ₐ[R] H ⊗[R] (H ⊗[R] H) := includeLeft
    let i2 : H →ₐ[R] H ⊗[R] (H ⊗[R] H) := (includeRight : H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H)).comp includeLeft
    let i3 : H →ₐ[R] H ⊗[R] (H ⊗[R] H) := (includeRight : H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H)).comp includeRight
    let i12 := (toConv i1 * toConv i2).ofConv
    let i23 := (toConv i2 * toConv i3).ofConv
    have e1 : ∀ x : H ⊗[R] H, (1 : H) ⊗ₜ[R] x = lift i2 i3 (fun _ _ ↦ Commute.all _ _) x := by
      intro x
      induction x with
      | add x y hx hy => rw [tmul_add, map_add (f := _), hx, hy]
      | tmul a b => simp [i2, i3, Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]
    have e2 : ∀ x : H ⊗[R] H, TensorProduct.assoc R H H H ((Coalgebra.comul (R := R) (A := H)).rTensor H x) =
        lift i12 i3 (fun _ _ ↦ Commute.all _ _) x := by
      intro x
      induction x with
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
      | tmul a b =>
        rw [LinearMap.rTensor_tmul, lift_tmul]
        simp only [i12, AlgHom.convMul_apply]
        induction (Coalgebra.comul (R := R) a : H ⊗[R] H) with
        | add x y hx hy => simp only [add_tmul, map_add (f := _), hx, hy, add_mul]
        | tmul a1 a2 => simp [i1, i2, i3, Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]
    have e3 : ∀ x : H ⊗[R] H, (Coalgebra.comul (R := R) (A := H)).lTensor H x = lift i1 i23 (fun _ _ ↦ Commute.all _ _) x := by
      intro x
      induction x with
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
      | tmul a b =>
        rw [LinearMap.lTensor_tmul, lift_tmul]
        simp only [i23, AlgHom.convMul_apply]
        induction (Coalgebra.comul (R := R) b : H ⊗[R] H) with
        | add x y hx hy => simp only [tmul_add, map_add (f := _), hx, hy, mul_add]
        | tmul b1 b2 => simp [i1, i2, i3, Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]
    have e4 : ∀ x : H ⊗[R] H, ((TensorProduct.mk R H H).flip 1).lTensor H x =
        lift i1 i2 (fun _ _ ↦ Commute.all _ _) x := by
      intro x
      induction x with
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
      | tmul a b => simp [i1, i2, Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]
    rw [cobTwo_apply, e1, e2, e3, e4, V, V, V, V]
    simp only [i12, i23, toConv_ofConv, M]
    rw [_root_.mul_assoc (toConv i1) (toConv i2) (toConv i3)]
    have hc := (hg (H ⊗[R] (H ⊗[R] H))).2 (spOver i1 ≫ t.y n) (spOver i2 ≫ t.y n) (spOver i3 ≫ t.y n)
    linear_combination hc
  · have e : ∀ x : H ⊗[R] H, TensorProduct.comm R H H x =
        lift (includeRight : H →ₐ[R] H ⊗[R] H) (includeLeft : H →ₐ[R] H ⊗[R] H) (fun _ _ ↦ Commute.all _ _) x := by
      intro x
      induction x with
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
      | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]
    have e' : d.coc n = lift (includeLeft : H →ₐ[R] H ⊗[R] H) includeRight (fun _ _ ↦ Commute.all _ _) (d.coc n) := by
      exact (DFunLike.congr_fun (lift_includeLeft_includeRight (R := R) (S := R) (A := H) (B := H)) (d.coc n)).symm
    rw [e, V]
    conv_rhs => rw [e', V]
    rw [mul_comm (toConv (includeRight : H →ₐ[R] H ⊗[R] H)), (hg _).1]
    ring

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingInvolutionActionGivesPolarisedAdjointPair
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.ActAdj

section Iso

variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}

theorem chart_le (j' : K' → L.ι) (j : K → L.ι) :
    LB.wchart L φ' j' ⊓ LB.wchart L φ j ≤ LB.wchart L (Sum.elim φ' φ) (Sum.elim j' j) := fun _ hy =>
  Set.mem_iInter.2 fun k => match k with
    | Sum.inl k => Set.mem_iInter.1 hy.1 k
    | Sum.inr k => Set.mem_iInter.1 hy.2 k

def genIso (t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k)))) :
    LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε') :=
  ⟨fun p => res (chart_le p.1 p.2) (t.s (Sum.elim p.1 p.2))⟩

theorem gm_genIso (t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k)))) {Z : Scheme.{0}}
    (r : Z ⟶ Y) (z : Z) (p : (K' → L.ι) × (K → L.ι)) (hp : r z ∈ LB.wchart L φ' p.1 ⊓ LB.wchart L φ p.2) :
    gm r z _ ((genIso t).s p) = gm r z _ (t.s (Sum.elim p.1 p.2)) :=
  gm_res r z (chart_le p.1 p.2) hp _

theorem genIso_isGen {t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k)))} (ht : t.IsGen) :
    (genIso t).IsGen := by
  intro p q
  refine unit_ext fun y hy => ?_
  have hp := chart_le (φ := φ) (φ' := φ') p.1 p.2 hy.1
  have hq := chart_le (φ := φ) (φ' := φ') q.1 q.2 hy.2
  have e := gen_trans ht (𝟙 Y) y hp hq
  refine ((gm_res (𝟙 Y) y _ hy _).trans ((gm_genIso t (𝟙 Y) y p hy.1).trans e)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div (LB.LinComb L φ ε) (LB.LinComb L φ' ε') (𝟙 Y) y p q hy)
    ((gm_res (𝟙 Y) y _ hy _).trans (gm_genIso t (𝟙 Y) y q hy.2)))).trans ?_
  congr 1
  refine (congrArg₂ (· * ·) (gm_linComb L φ' ε' (𝟙 Y) y _ _ hy.1.1 hy.2.1)
    (congrArg (·⁻¹) (gm_linComb L φ ε (𝟙 Y) y _ _ hy.1.2 hy.2.2))).trans ?_
  simp only [trF, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rfl

end Iso

end GlobalTheory.MumFam.ActAdj

namespace GlobalTheory.MumFam


open ActAdj in
theorem adj_act : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (a : O), Adj (pol D) (pol D) (o.onB.act a) (o.onB.act (Star.star a)) (DistribSMul.toAddMonoidHom D.toPre.X a) (DistribSMul.toAddMonoidHom D.toPre.X (Star.star a)) := by
  intro R _ _ I D O _ _ _ o a
  have hL := D.toPre.P.isLB
  let B := D.toPre.P.A
  let f := o.onB.act a
  let g := o.onB.act (star a)
  haveI hf : IsMonHom f := o.onB.hom a
  haveI hg : IsMonHom g := o.onB.hom (star a)
  let φ₀ : ULift.{0} (Finset (Fin 2)) → ((B ⊗ B).left ⟶ B.left) :=
    fun I => (psum B ![fst B B ≫ f, snd B B] I.down).left
  let φ₁ : ULift.{0} (Finset (Fin 2)) → ((B ⊗ B).left ⟶ B.left) :=
    fun I => (psum B ![fst B B, snd B B ≫ g] I.down).left
  let e₂ : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)
  obtain ⟨u, hu, h0⟩ := exists_ros GlobalTheory.globalFns_holds D.toPre.P.isAb hL f g (o.onB.rosati a)
  have hF : FormEq (rosatiφ B f g) (fun i => - rosatiε i) (Sum.elim φ₁ φ₀) (Sum.elim e₂ (fun k => - e₂ k)) := by
    intro U _ k
    have p := prod_ros f g (fst B B) (snd B B) k
    rw [lift_fst_snd] at p
    have p' : ∏ i, k (rosatiφ B f g i) ^ rosatiε i = _ :=
      (Finset.prod_congr rfl fun i _ => by erw [Over.id_left, Category.id_comp]).trans p
    have s1 : ∏ I, k (φ₁ I) ^ e₂ I = _ := GlobalTheory.NormRos.prod_square (fst B B) (snd B B ≫ g) k
    have s0 : ∏ I, k (φ₀ I) ^ e₂ I = _ := GlobalTheory.NormRos.prod_square (fst B B ≫ f) (snd B B) k
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
    rw [p', s1, s0]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨t, ht, htv⟩ := exists_gen hL hF (LB.invGen _ _ _ u) (DVR.invGen_isGen _ _ _ _ hu)
  let w : LB.Iso (cubeLB B ![fst B B ≫ f, snd B B] D.toPre.P.L) (cubeLB B ![fst B B, snd B B ≫ g] D.toPre.P.L) :=
    ActAdj.genIso t
  refine ⟨hf, hg, fun y => o.c_lin a y, fun y => o.c_lin (star a) y, w, ActAdj.genIso_isGen ht,
    fun y y' z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  let P := (lift (toUnit (TK R) ≫ D.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left
  have hp : ∀ b b' J, Good D.toPre.P.L z J → val ((pol D).tau b b') (𝟙 _) z J = val (D.toPre.tau b b') (𝟙 _) z J :=
    fun b b' J hJ => (Wit.exists_tau D.toPre b b').choose_spec.2 _ _ z J hJ
  have hK₁ : Good D.toPre.P.L z J₁ := hJ₁
  have hK₂ : Good D.toPre.P.L z J₂ := hJ₂

  have bal := val_corr hK₁ (o.tau_bal a u hu h0 y y') (𝟙 _)
  rw [val_mul hK₁, val_pull hK₁, Category.id_comp] at bal
  have hut : val t P z J₁ = (val u P z J₁)⁻¹ := (htv _ P z J₁ hK₁).trans (val_inv _ _)
  let h := DistribSMul.toAddMonoidHom D.toPre.X a
  let h' := DistribSMul.toAddMonoidHom D.toPre.X (star a)
  have single : val ((pol D).tau (h y) y') (𝟙 _) z J₁ =
      val t P z J₁ * val ((pol D).tau y (h' y')) (𝟙 _) z J₁ := by
    exact (hp _ _ _ hK₁).trans ((eq_inv_mul_of_mul_eq ((mul_comm _ _).trans bal)).trans
      (congrArg₂ (· * ·) hut.symm (hp _ _ _ hK₁).symm))

  let j₁ : ULift.{0} (Finset (Fin 2)) → D.toPre.P.L.ι := fun I => J₁ (P ≫ φ₁ I)
  let j₂ : ULift.{0} (Finset (Fin 2)) → D.toPre.P.L.ι := fun I => J₂ (P ≫ φ₀ I)
  let j₁' : ULift.{0} (Finset (Fin 2)) → D.toPre.P.L.ι := fun I => J₁ (P ≫ φ₀ I)
  have m₁ : P z ∈ LB.wchart D.toPre.P.L φ₁ j₁ := hK₁.mem φ₁ P
  have m₂ : P z ∈ LB.wchart D.toPre.P.L φ₀ j₂ := hK₂.mem φ₀ P
  have m₁' : P z ∈ LB.wchart D.toPre.P.L φ₀ j₁' := hK₁.mem φ₀ P
  have eA : adjVal w P z J₁ J₂ = gm P z _ (t.s (Sum.elim j₁ j₂)) := ActAdj.gm_genIso t P z (j₁, j₂) ⟨m₁, m₂⟩
  have eT : val t P z J₁ = gm P z _ (t.s (Sum.elim j₁ j₁')) := val_of t P z J₁ _ (by rintro (k | k) <;> rfl)
  have tr := gen_trans ht P z (ActAdj.chart_le j₁ j₂ ⟨m₁, m₂⟩) (ActAdj.chart_le j₁ j₁' ⟨m₁, m₁'⟩)
  have trτ := gen_trans ((pol D).tau_gen (h y) y') (𝟙 _) z (hK₂.mem _ (𝟙 _)) (hK₁.mem _ (𝟙 _))
  let H : ((TK R).left ⟶ B.left) → ((TK R).left.presheaf.stalk z)ˣ :=
    fun ψ => gm ψ z (D.toPre.P.L.U (J₂ ψ) ⊓ D.toPre.P.L.U (J₁ ψ)) (D.toPre.P.L.g (J₂ ψ) (J₁ ψ))
  have kt : trF (Sum.elim φ₁ φ₀) (Sum.elim e₂ fun k => -e₂ k) P z (Sum.elim j₁ j₂) (Sum.elim j₁ j₁') =
      (∏ I, H (P ≫ φ₀ I) ^ e₂ I)⁻¹ := by
    unfold trF
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [Finset.prod_eq_one (fun I _ => by erw [gm_self hL (P ≫ φ₁ I) z (hK₁ (P ≫ φ₁ I)), one_zpow]), _root_.one_mul]
    simp only [zpow_neg, Finset.prod_inv_distrib]
    rfl
  have cx : (toUnit (TK R) ≫ D.toPre.c y) ≫ f = toUnit (TK R) ≫ (pol D).c (h y) :=
    (Category.assoc _ _ _).trans (congrArg (toUnit (TK R) ≫ ·) (o.c_lin a y)).symm
  let X : TK R ⟶ B := toUnit (TK R) ≫ (pol D).c (h y)
  let Y : TK R ⟶ B := toUnit (TK R) ≫ (pol D).c y'
  have q1 : P ≫ ((fst B B ≫ f) * snd B B).left = (X * Y).left := by
    show (lift (toUnit (TK R) ≫ D.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left ≫ _ = _
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst_assoc, lift_snd, cx]
    rfl
  have q2 : P ≫ (fst B B ≫ f).left = X.left := by
    show (lift (toUnit (TK R) ≫ D.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left ≫ _ = _
    rw [← Over.comp_left, lift_fst_assoc, cx]
    rfl
  have q3 : P ≫ (snd B B).left = Y.left := by
    show (lift (toUnit (TK R) ≫ D.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left ≫ _ = _
    rw [← Over.comp_left, lift_snd]
    rfl
  have q4 : P ≫ (1 : B ⊗ B ⟶ B).left = (1 : TK R ⟶ B).left := by
    show (lift (toUnit (TK R) ≫ D.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left ≫ _ = _
    rw [← Over.comp_left, MonObj.comp_one]
  have s0 : ∏ I, H (P ≫ φ₀ I) ^ e₂ I = H (P ≫ ((fst B B ≫ f) * snd B B).left) * (H (P ≫ (fst B B ≫ f).left))⁻¹ *
      (H (P ≫ (snd B B).left))⁻¹ * H (P ≫ (1 : B ⊗ B ⟶ B).left) :=
    GlobalTheory.NormRos.prod_square (fst B B ≫ f) (snd B B) (fun ψ => H (P ≫ ψ))
  have l4 : ∀ X Y : TK R ⟶ B, ∏ k, H (𝟙 _ ≫ lamPts X Y k) ^ negε k =
      (H (X * Y).left)⁻¹ * H X.left * H Y.left * (H (1 : TK R ⟶ B).left)⁻¹ := fun X Y => by
    have e := Wit.prod_neg_lamPts X Y (fun ψ => (H ψ)⁻¹)
    simpa only [inv_inv] using e
  have kτ : ∏ k, H (𝟙 _ ≫ lamPts X Y k) ^ negε k = (∏ I, H (P ≫ φ₀ I) ^ e₂ I)⁻¹ := by
    rw [l4 X Y, s0, q1, q2, q3, q4]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  refine (trτ.trans (congrArg (_ * ·) single)).trans (Eq.trans ?_
    (congrArg (· * _) (eA.trans (tr.trans (congrArg (_ * ·) eT.symm)))).symm)
  rw [_root_.mul_assoc]
  congr 1
  exact kτ.trans kt.symm

end GlobalTheory.MumFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiBalanceFormalSumPsiValuesEqTauProduct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensBalLat

open GlobalTheory.TensBal

section Calc

variable {M : Type} [CommGroup M] {α : Type}

def logHom (f : α → M) : (α →₀ ℤ) →+ Additive M :=
  Finsupp.liftAddHom fun v => zmultiplesHom (Additive M) (Additive.ofMul (f v)⁻¹)

theorem logHom_single (f : α → M) (v : α) : logHom f (Finsupp.single v 1) = Additive.ofMul (f v)⁻¹ := by
  simp [logHom]

theorem prod_eq_logHom (f : α → M) (c : α →₀ ℤ) :
    ∏ v ∈ c.support, f v ^ (-(c v)) = Additive.toMul (logHom f c) := by
  simp [logHom, Finsupp.liftAddHom_apply, Finsupp.sum, toMul_sum, toMul_zsmul, inv_zpow']

end Calc

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem vecLat_add (T : Tens D D' W) (u v : Vec r) (y y' : D'.X) :
    vecLat T (u + v) y y' = vecLat T u y y' + vecLat T v y y' := by
  simp only [vecLat, Pi.add_apply, add_smul, Finset.sum_add_distrib]; abel

theorem vecLat_zero (T : Tens D D' W) (y y' : D'.X) : vecLat T 0 y y' = 0 := by
  simp [vecLat]

theorem vecLat_rosVec (T : Tens D D' W) (A A' : Matrix (Fin r) (Fin r) ℤ) (y y' : D'.X) (a : Fin 6) (i : Fin r) :
    vecLat T (rosVec A A' a i) y y' = T.xe (rosLat T A A' y y' a) i := by
  fin_cases a <;>
    simp [vecLat, rosVec, rosLat, axv, azv, xv, zv, GlobalTheory.TensAct.xe_latAct, map_add (f := _), Pi.single_apply,
      Finset.sum_add_distrib, add_smul, ite_smul]

theorem logHom_lam (T : Tens D D' W) (hB : D.TauBimult) {z : (TK R).left} {J} (hJ : Good D.P.L z J)
    (y y' : D'.X) (u v : Vec r) :
    logHom (fun w => val (D.psi (vecLat T w y y')) (𝟙 _) z J) (lam u v) =
      Additive.ofMul (val (D.tau (vecLat T u y y') (vecLat T v y y')) (𝟙 _) z J)⁻¹ := by
  have hk : val (D.psi 0) (𝟙 _) z J = (val D.rigK (𝟙 _) z J)⁻¹ := by
    have e := (GlobalTheory.TauBalBox.tau_val D hJ 0 0 (𝟙 _)).symm.trans (GlobalTheory.TauBalElem.tau_zero_left hB hJ 0)
    rw [add_zero, mul_inv_cancel, _root_.one_mul] at e
    exact inv_mul_eq_one.mp e
  have h0 : vecLat T (0 : Vec r) y y' = 0 := vecLat_zero T y y'
  simp only [lam, map_add (f := _), map_sub, logHom_single, vecLat_add]
  rw [h0, vecLat_add]
  rw [GlobalTheory.TauBalBox.tau_val D hJ, hk]
  simp only [ofMul_mul, ofMul_inv, inv_inv]
  abel

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W), D.TauBimult → ∀ (A A' : Matrix (Fin r) (Fin r) ℤ) (z : (TK R).left)
    (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → ∀ y y' : D'.X,
    ∏ v ∈ (GlobalTheory.TensBal.sig W A A').support,
        val (D.psi (GlobalTheory.TensBal.vecLat T v y y')) (𝟙 _) z J ^ (-(GlobalTheory.TensBal.sig W A A' v)) =
      ∏ a, GlobalTheory.TensBal.qv T z J (GlobalTheory.TensBal.rosLat T A A' y y' a) ^ (-(rosatiε a)) := by
  intro R _ _ D D' r W T hB A A' z J hJ y y'
  rw [prod_eq_logHom (fun w => val (D.psi (vecLat T w y y')) (𝟙 _) z J)]
  apply Additive.ofMul.injective
  rw [ofMul_toMul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [sig, map_sum, map_zsmul, logHom_lam T hB hJ, vecLat_rosVec, qv, ofMul_prod, ofMul_zpow,
    Finset.smul_sum, ofMul_inv, smul_neg, smul_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← neg_smul, neg_mul, vecLat_rosVec, vecLat_rosVec]

end GlobalTheory.TensBalLat
end
end

