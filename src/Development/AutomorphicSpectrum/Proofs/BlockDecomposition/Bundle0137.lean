module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0129

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionMulLeftRightAndOne
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC.ConMul

theorem con_mul_left {I : Type} [Finite I] {R : Type} [CommRing R] (V : I → Type) [∀ i, CommRing (V i)]
    [∀ i, Algebra R (V i)] (M : Type) [CommRing M] [Algebra R M] (Ξ : (∀ i, V i) →ₗ[R] R) (x : ∀ i, V i)
    (u : ∀ i, V i ⊗[R] M) :
    con V M Ξ (fun i ↦ (x i ⊗ₜ[R] (1 : M)) * u i) = con V M (Ξ ∘ₗ LinearMap.mulLeft R x) u := by
  revert u
  refine GlobalTheory.CompanionTheory.HopfC.pure_induction V M ?_ ?_ ?_
  · have h : (fun i ↦ (x i ⊗ₜ[R] (1 : M)) * (0 : ∀ i, V i ⊗[R] M) i) = 0 := by
      funext i
      simp
    rw [h, map_zero, map_zero]
  · intro f m
    have h : (fun i ↦ (x i ⊗ₜ[R] (1 : M)) * (f i ⊗ₜ[R] m)) = fun i ↦ (x * f) i ⊗ₜ[R] m := by
      funext i
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [h, GlobalTheory.CompanionTheory.HopfC.con_pure, GlobalTheory.CompanionTheory.HopfC.con_pure]
    rfl
  · intro u v hu hv
    have h : (fun i ↦ (x i ⊗ₜ[R] (1 : M)) * (u + v) i) =
        (fun i ↦ (x i ⊗ₜ[R] (1 : M)) * u i) + fun i ↦ (x i ⊗ₜ[R] (1 : M)) * v i := by
      funext i
      simp [mul_add]
    rw [h, map_add (f := _), map_add (f := _), hu, hv]

theorem con_mul_right {I : Type} [Finite I] {R : Type} [CommRing R] (V : I → Type) [∀ i, CommRing (V i)]
    [∀ i, Algebra R (V i)] (M : Type) [CommRing M] [Algebra R M] (Ξ : (∀ i, V i) →ₗ[R] R) (y : M)
    (u : ∀ i, V i ⊗[R] M) :
    con V M Ξ (fun i ↦ ((1 : V i) ⊗ₜ[R] y) * u i) = y * con V M Ξ u := by
  induction u using pure_induction with
  | h0 =>
    have h : (fun i ↦ ((1 : V i) ⊗ₜ[R] y) * (0 : ∀ i, V i ⊗[R] M) i) = 0 := by
      funext i; simp
    rw [h, map_zero, mul_zero]
  | hp f m =>
    have h : (fun i ↦ ((1 : V i) ⊗ₜ[R] y) * (f i ⊗ₜ[R] m)) = fun i ↦ f i ⊗ₜ[R] (y * m) := by
      funext i; simp
    rw [h, con_pure, con_pure, mul_smul_comm]
  | ha u v hu hv =>
    have h : (fun i ↦ ((1 : V i) ⊗ₜ[R] y) * (u + v) i) =
        (fun i ↦ ((1 : V i) ⊗ₜ[R] y) * u i) + (fun i ↦ ((1 : V i) ⊗ₜ[R] y) * v i) := by
      funext i; simp [mul_add]
    rw [h, map_add (f := _), map_add (f := _), hu, hv, mul_add]

theorem con_products {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p q : ℕ}
    [Finite (Fin (p + 1) ⥤ C)] (Ξ : Cn F p →ₗ[R] R) (x : Cn F p) (y : Cn F q) (B : Bi F p q) :
    Con F Ξ q ((fun a _ ↦ x a ⊗ₜ[R] 1 : Bi F p q) * B) = Con F (Ξ ∘ₗ LinearMap.mulLeft R x) q B ∧
    Con F Ξ q ((fun _ b ↦ 1 ⊗ₜ[R] y b : Bi F p q) * B) = y * Con F Ξ q B ∧
    Con F Ξ q (1 : Bi F p q) = Ξ 1 • (1 : Cn F q) := by
  refine ⟨?_, ?_, ?_⟩
  · funext b
    exact GlobalTheory.CompanionTheory.HopfC.ConMul.con_mul_left (fun a : Fin (p + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p)))
      (F.obj (b.obj (Fin.last q))) Ξ x (fun a ↦ B a b)
  · funext b
    exact GlobalTheory.CompanionTheory.HopfC.ConMul.con_mul_right (fun a : Fin (p + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p)))
      (F.obj (b.obj (Fin.last q))) Ξ (y b) (fun a ↦ B a b)
  · funext b
    exact GlobalTheory.CompanionTheory.HopfC.con_pure (fun a : Fin (p + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p)))
      (F.obj (b.obj (Fin.last q))) Ξ 1 1

end GlobalTheory.CompanionTheory.HopfC.ConMul
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionNaturalInFaceMaps
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.HopfC.ConPr

theorem Con_apply {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p : ℕ}
    [Finite (Fin (p + 1) ⥤ C)] (Ξ : Cn F p →ₗ[R] R) (q : ℕ) (B : Bi F p q) (b : Fin (q + 1) ⥤ C) :
    Con F Ξ q B b = con (fun a : Fin (p + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p))) (F.obj (b.obj (Fin.last q))) Ξ
      (fun a ↦ B a b) := rfl

theorem con_lTensor {R : Type} [CommRing R] {I : Type} [Finite I] (V : I → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module R (V i)] {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (Ξ : (∀ i, V i) →ₗ[R] R) (φ : M →ₗ[R] M') (u : ∀ i, V i ⊗[R] M) :
    con V M' Ξ (fun i ↦ LinearMap.lTensor (V i) φ (u i)) = φ (con V M Ξ u) := by
  induction u using pure_induction with
  | h0 =>
    have h : (fun i ↦ LinearMap.lTensor (V i) φ ((0 : ∀ i, V i ⊗[R] M) i)) = 0 := by
      funext i; simp
    rw [h]; simp
  | hp f m =>
    simp only [LinearMap.lTensor_tmul]
    rw [con_pure, con_pure, map_smul]
  | ha u v hu hv =>
    have h : (fun i ↦ LinearMap.lTensor (V i) φ ((u + v) i)) =
        (fun i ↦ LinearMap.lTensor (V i) φ (u i)) + (fun i ↦ LinearMap.lTensor (V i) φ (v i)) := by
      funext i; simp
    rw [h, map_add (f := _), map_add (f := _), map_add (f := _), hu, hv]

theorem tmap_id_eq {R : Type} [CommRing R] {A B B' : Type} [CommRing A] [CommRing B] [CommRing B']
    [Algebra R A] [Algebra R B] [Algebra R B'] (g : B →ₐ[R] B') (t : A ⊗[R] B) :
    Algebra.TensorProduct.map (AlgHom.id R A) g t = LinearMap.lTensor A g.toLinearMap t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem Con_prB {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p q q' : ℕ}
    [Finite (Fin (p + 1) ⥤ C)] (Ξ : Cn F p →ₗ[R] R) (e : Fin (q + 1) →o Fin (q' + 1)) (B : Bi F p q) :
    Con F Ξ q' (prB F e B) = pr F e (Con F Ξ q B) := by
  funext b
  rw [pr_apply, Con_apply, Con_apply]
  simp only [prB_apply, tmap_id_eq]
  exact con_lTensor (fun a : Fin (p + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p))) Ξ _ _

theorem con_prA {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p p' : ℕ}
    [Finite (Fin (p + 1) ⥤ C)] [Finite (Fin (p' + 1) ⥤ C)] (Ξ' : Cn F p' →ₗ[R] R)
    (e : Fin (p + 1) →o Fin (p' + 1)) (M : Type) [AddCommGroup M] [Module R M]
    (u : ∀ a : Fin (p + 1) ⥤ C, F.obj (a.obj (Fin.last p)) ⊗[R] M) :
    con (fun a : Fin (p' + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p'))) M Ξ'
      (fun a ↦ LinearMap.rTensor M (mp F (a.map (homOfLE (Fin.le_last (e (Fin.last p)))))).toLinearMap
        (u (e.monotone.functor ⋙ a))) =
    con (fun a : Fin (p + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p))) M (Ξ' ∘ₗ (pr F e).toLinearMap) u := by
  induction u using pure_induction with
  | h0 =>
    have h : (fun a : Fin (p' + 1) ⥤ C ↦ LinearMap.rTensor M (mp F (a.map (homOfLE (Fin.le_last (e (Fin.last p)))))).toLinearMap
        ((0 : ∀ a : Fin (p + 1) ⥤ C, F.obj (a.obj (Fin.last p)) ⊗[R] M) (e.monotone.functor ⋙ a))) = 0 := by
      funext a; exact map_zero _
    rw [h]; simp
  | hp f m =>
    simp only [LinearMap.rTensor_tmul]
    rw [con_pure (V := fun a : Fin (p + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p)))]
    exact con_pure (fun a : Fin (p' + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p'))) M Ξ' (pr F e f) m
  | ha u v hu hv =>
    rw [map_add (f := _), ← hu, ← hv, ← map_add (f := _)]
    congr 1
    funext a
    exact map_add _ _ _

theorem tmap_id_eq' {R : Type} [CommRing R] {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B]
    [Algebra R A] [Algebra R A'] [Algebra R B] (g : A →ₐ[R] A') (t : A ⊗[R] B) :
    Algebra.TensorProduct.map g (AlgHom.id R B) t = LinearMap.rTensor B g.toLinearMap t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem Con_prA {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p p' q : ℕ}
    [Finite (Fin (p + 1) ⥤ C)] [Finite (Fin (p' + 1) ⥤ C)] (Ξ' : Cn F p' →ₗ[R] R)
    (e : Fin (p + 1) →o Fin (p' + 1)) (B : Bi F p q) :
    Con F Ξ' q (prA F e B) = Con F (Ξ' ∘ₗ (pr F e).toLinearMap) q B := by
  funext b
  rw [Con_apply, Con_apply]
  simp only [prA_apply, tmap_id_eq']
  exact con_prA F Ξ' e _ (fun a ↦ B a b)

theorem con_pr : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p p' q q' : ℕ} [Finite (Fin (p + 1) ⥤ C)] [Finite (Fin (p' + 1) ⥤ C)] (Ξ : Cn F p →ₗ[R] R) (Ξ' : Cn F p' →ₗ[R] R) (e : Fin (q + 1) →o Fin (q' + 1)) (e' : Fin (p + 1) →o Fin (p' + 1)), (∀ B : Bi F p q, Con F Ξ q' (prB F e B) = pr F e (Con F Ξ q B)) ∧ (∀ B : Bi F p q, Con F Ξ' q (prA F e' B) = Con F (Ξ' ∘ₗ (pr F e').toLinearMap) q B) :=
  fun F _ _ _ _ _ _ Ξ Ξ' e e' ↦ ⟨Con_prB F Ξ e, Con_prA F Ξ' e'⟩

end GlobalTheory.CompanionTheory.HopfC.ConPr
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrossProductKernelQuotientVanishing
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf

namespace GlobalTheory.CompanionTheory.WedgeOf.Shuffle

theorem exists_tensorPi (R : Type) [CommRing R] (I J : Type) [Finite I] [Finite J] (A : I → Type) (B : J → Type)
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] [∀ j, AddCommGroup (B j)] [∀ j, Module R (B j)] :
    ∃ Φ : (∀ i, A i) ⊗[R] (∀ j, B j) ≃ₗ[R] ∀ x : I × J, A x.1 ⊗[R] B x.2,
      ∀ (f : ∀ i, A i) (g : ∀ j, B j) (x : I × J), Φ (f ⊗ₜ g) x = f x.1 ⊗ₜ g x.2 := by
  classical
  haveI := Fintype.ofFinite I
  haveI := Fintype.ofFinite J
  let e : (∀ j, ∀ i, A i ⊗[R] B j) ≃ₗ[R] ∀ x : I × J, A x.1 ⊗[R] B x.2 :=
    { toFun := fun g x ↦ g x.2 x.1
      invFun := fun h j i ↦ h (i, j)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  refine ⟨(TensorProduct.piRight R R (∀ i, A i) B) ≪≫ₗ
    (LinearEquiv.piCongrRight fun j ↦ (TensorProduct.comm R _ _) ≪≫ₗ (TensorProduct.piRight R R (B j) A) ≪≫ₗ
      (LinearEquiv.piCongrRight fun i ↦ TensorProduct.comm R _ _)) ≪≫ₗ e, fun f g x ↦ ?_⟩
  simp [e]

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

abbrev Ar (C : Type) [Category.{0} C] : Type := Σ T : C, Σ T' : C, (T ⟶ T')

theorem finite_ar [Finite C] [Quiver.IsThin C] : Finite (Ar C) := by
  haveI : ∀ T T' : C, Finite (T ⟶ T') := fun _ _ ↦ Finite.of_subsingleton
  infer_instance

def oneCochainsPiArrowsEquiv : C1 F ≃ₗ[R] ∀ x : Ar C, F.obj x.2.1 where
  toFun f x := f x.1 x.2.1 x.2.2
  invFun g T T' φ := g ⟨T, T', φ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

abbrev E : Type := ∀ x : Ar C × Ar C, F.obj x.1.2.1 ⊗[R] F.obj x.2.2.1

def shuffle : C2 (box F) →ₗ[R] E F where
  toFun z x := z (x.1.1, x.2.1) (x.1.2.1, x.2.1) (x.1.2.1, x.2.2.1) (x.1.2.2, 𝟙 _) (𝟙 _, x.2.2.2)
    - z (x.1.1, x.2.1) (x.1.1, x.2.2.1) (x.1.2.1, x.2.2.1) (𝟙 _, x.2.2.2) (x.1.2.2, 𝟙 _)
  map_add' z z' := by
    funext x
    simp only [Pi.add_apply]
    abel
  map_smul' r z := by
    funext x
    simp only [Pi.smul_apply, RingHom.id_apply, smul_sub]

theorem mp_box {a a' b b' : C} (φ : a ⟶ a') (ψ : b ⟶ b') (t : F.obj a ⊗[R] F.obj b) :
    (mp (box F) (T := (a, b)) (T' := (a', b')) (φ, ψ)) t =
      TensorProduct.map (mp F φ).toLinearMap (mp F ψ).toLinearMap t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add u v hu hv => simp only [map_add (f := _), hu, hv]

theorem shuffle_cup (f h : Z1 F) (x : Ar C × Ar C) :
    shuffle F (cupZ (box F) ((boxL F).pullbackOneCocycle f) ((boxR F).pullbackOneCocycle h)).1 x =
      f.1 _ _ x.1.2.2 ⊗ₜ h.1 _ _ x.2.2.2 := by
  obtain ⟨⟨a, a', φ⟩, ⟨b, b', ψ⟩⟩ := x
  change (mp (box F) (T := (a', b)) (T' := (a', b')) (𝟙 a', ψ)) (f.1 a a' φ ⊗ₜ 1) * (1 ⊗ₜ h.1 b b' ψ) -
    (mp (box F) (T := (a, b')) (T' := (a', b')) (φ, 𝟙 b')) (f.1 a a (𝟙 a) ⊗ₜ 1) * (1 ⊗ₜ h.1 b' b' (𝟙 b')) = _
  rw [Z1.id f a, mp_box]
  simp [mp_id]

theorem shuffle_mk (z : C2 (box F)) {a a' b b' : C} (φ : a ⟶ a') (ψ : b ⟶ b') :
    shuffle F z (⟨a, a', φ⟩, ⟨b, b', ψ⟩) =
      z (a, b) (a', b) (a', b') (φ, 𝟙 b) (𝟙 a', ψ) - z (a, b) (a, b') (a', b') (𝟙 a, ψ) (φ, 𝟙 b') := rfl

theorem shuffle_coboundary_one (w : C1 (box F)) {a a' b b' : C} (φ : a ⟶ a') (ψ : b ⟶ b') :
    shuffle F (d1 (box F) w) (⟨a, a', φ⟩, ⟨b, b', ψ⟩) =
      (TensorProduct.map LinearMap.id (mp F ψ).toLinearMap (w (a, b) (a', b) (φ, 𝟙 b)) - w (a, b') (a', b') (φ, 𝟙 b')) +
      (w (a', b) (a', b') (𝟙 a', ψ) -
        TensorProduct.map (mp F φ).toLinearMap LinearMap.id (w (a, b) (a, b') (𝟙 a, ψ))) := by
  have e : CategoryStruct.comp (X := ((a, b) : C × C)) (Y := (a', b)) (Z := (a', b')) (φ, 𝟙 b) (𝟙 a', ψ) =
      CategoryStruct.comp (X := ((a, b) : C × C)) (Y := (a, b')) (Z := (a', b')) (𝟙 a, ψ) (φ, 𝟙 b') := by
    simp
  have i1 : (mp F (𝟙 a')).toLinearMap = LinearMap.id := by ext u; exact mp_id F a' u
  have i2 : (mp F (𝟙 b')).toLinearMap = LinearMap.id := by ext u; exact mp_id F b' u
  rw [shuffle_mk, d1_apply, d1_apply, e, mp_box, mp_box, i1, i2]
  abel

theorem exists_one_one_cochain_tensor_equiv [Finite C] [Quiver.IsThin C] :
    ∃ Φ : C1 F ⊗[R] C1 F ≃ₗ[R] E F, ∀ f g x, Φ (f ⊗ₜ g) x = f _ _ x.1.2.2 ⊗ₜ g _ _ x.2.2.2 := by
  haveI := finite_ar (C := C)
  obtain ⟨Φ, h⟩ := exists_tensorPi R (Ar C) (Ar C) (fun x ↦ F.obj x.2.1) (fun x ↦ F.obj x.2.1)
  exact ⟨TensorProduct.congr (oneCochainsPiArrowsEquiv F) (oneCochainsPiArrowsEquiv F) ≪≫ₗ Φ, fun f g x ↦ h _ _ x⟩

theorem exists_one_zero_cochain_tensor_equiv [Finite C] [Quiver.IsThin C] :
    ∃ Φ : C1 F ⊗[R] C0 F ≃ₗ[R] ∀ x : Ar C × C, F.obj x.1.2.1 ⊗[R] F.obj x.2,
      ∀ f g x, Φ (f ⊗ₜ g) x = f _ _ x.1.2.2 ⊗ₜ g x.2 := by
  haveI := finite_ar (C := C)
  obtain ⟨Φ, h⟩ := exists_tensorPi R (Ar C) C (fun x ↦ F.obj x.2.1) (fun x ↦ F.obj x)
  exact ⟨TensorProduct.congr (oneCochainsPiArrowsEquiv F) (LinearEquiv.refl R _) ≪≫ₗ Φ, fun f g x ↦ h _ _ x⟩

theorem exists_zero_one_cochain_tensor_equiv [Finite C] [Quiver.IsThin C] :
    ∃ Φ : C0 F ⊗[R] C1 F ≃ₗ[R] ∀ x : C × Ar C, F.obj x.1 ⊗[R] F.obj x.2.2.1,
      ∀ f g x, Φ (f ⊗ₜ g) x = f x.1 ⊗ₜ g _ _ x.2.2.2 := by
  haveI := finite_ar (C := C)
  obtain ⟨Φ, h⟩ := exists_tensorPi R C (Ar C) (fun x ↦ F.obj x) (fun x ↦ F.obj x.2.1)
  exact ⟨TensorProduct.congr (LinearEquiv.refl R _) (oneCochainsPiArrowsEquiv F) ≪≫ₗ Φ, fun f g x ↦ h _ _ x⟩

variable {F}

theorem phi_right (Φ : C1 F ⊗[R] C1 F ≃ₗ[R] E F)
    (hΦ : ∀ f g x, Φ (f ⊗ₜ g) x = f _ _ x.1.2.2 ⊗ₜ g _ _ x.2.2.2)
    (Φ₁ : C1 F ⊗[R] C0 F ≃ₗ[R] ∀ x : Ar C × C, F.obj x.1.2.1 ⊗[R] F.obj x.2)
    (hΦ₁ : ∀ f g x, Φ₁ (f ⊗ₜ g) x = f _ _ x.1.2.2 ⊗ₜ g x.2) (u : C1 F ⊗[R] C0 F) (x y : Ar C) :
    Φ (TensorProduct.map LinearMap.id (d0 F) u) (x, y) =
      Φ₁ u (x, y.2.1) - TensorProduct.map LinearMap.id (mp F y.2.2).toLinearMap (Φ₁ u (x, y.1)) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, hΦ, hΦ₁, amitsur_d0_apply, TensorProduct.tmul_sub]
    rfl
  | add u v hu hv =>
    simp only [map_add (f := _), Pi.add_apply, hu, hv]
    abel

theorem phi_left (Φ : C1 F ⊗[R] C1 F ≃ₗ[R] E F)
    (hΦ : ∀ f g x, Φ (f ⊗ₜ g) x = f _ _ x.1.2.2 ⊗ₜ g _ _ x.2.2.2)
    (Φ₂ : C0 F ⊗[R] C1 F ≃ₗ[R] ∀ x : C × Ar C, F.obj x.1 ⊗[R] F.obj x.2.2.1)
    (hΦ₂ : ∀ f g x, Φ₂ (f ⊗ₜ g) x = f x.1 ⊗ₜ g _ _ x.2.2.2) (v : C0 F ⊗[R] C1 F) (x y : Ar C) :
    Φ (TensorProduct.map (d0 F) LinearMap.id v) (x, y) =
      Φ₂ v (x.2.1, y) - TensorProduct.map (mp F x.2.2).toLinearMap LinearMap.id (Φ₂ v (x.1, y)) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, hΦ, hΦ₂, amitsur_d0_apply, TensorProduct.sub_tmul]
    rfl
  | add u v hu hv =>
    simp only [map_add (f := _), Pi.add_apply, hu, hv]
    abel

variable (F)

def crossZ : Z1 F ⊗[R] Z1 F →ₗ[R] Z2 (box F) :=
  TensorProduct.lift ((cupZ (box F)).compl₁₂ (boxL F).pullbackOneCocycle (boxR F).pullbackOneCocycle)

theorem crossZ_tmul (f h : Z1 F) :
    crossZ F (f ⊗ₜ h) = cupZ (box F) ((boxL F).pullbackOneCocycle f) ((boxR F).pullbackOneCocycle h) := rfl

theorem mk_crossZ (s : Z1 F ⊗[R] Z1 F) :
    H2.mk (box F) (crossZ F s) = TensorProduct.lift (crossB F) (TensorProduct.map (H1.mk F) (H1.mk F) s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul f h => rfl
  | add u v hu hv => simp only [map_add (f := _), hu, hv]

theorem shuffle_crossZ (Φ : C1 F ⊗[R] C1 F ≃ₗ[R] E F)
    (hΦ : ∀ f g x, Φ (f ⊗ₜ g) x = f _ _ x.1.2.2 ⊗ₜ g _ _ x.2.2.2) (s : Z1 F ⊗[R] Z1 F) :
    shuffle F (crossZ F s).1 = Φ (TensorProduct.map (Z1 F).subtype (Z1 F).subtype s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul f h =>
    funext x
    rw [crossZ_tmul, shuffle_cup, TensorProduct.map_tmul, hΦ]
    rfl
  | add u v hu hv =>
    simp only [map_add (f := _), Submodule.coe_add, hu, hv]

theorem exists_boundary [Finite C] [Quiver.IsThin C] (s : Z1 F ⊗[R] Z1 F) (w : C1 (box F))
    (hw : d1 (box F) w = (crossZ F s).1) :
    ∃ (u : C1 F ⊗[R] C0 F) (v : C0 F ⊗[R] C1 F), TensorProduct.map (Z1 F).subtype (Z1 F).subtype s =
      TensorProduct.map (d0 F) LinearMap.id v - TensorProduct.map LinearMap.id (d0 F) u := by
  obtain ⟨Φ, hΦ⟩ := exists_one_one_cochain_tensor_equiv F
  obtain ⟨Φ₁, hΦ₁⟩ := exists_one_zero_cochain_tensor_equiv F
  obtain ⟨Φ₂, hΦ₂⟩ := exists_zero_one_cochain_tensor_equiv F
  refine ⟨Φ₁.symm fun x ↦ w (x.1.1, x.2) (x.1.2.1, x.2) (x.1.2.2, 𝟙 _),
    Φ₂.symm fun x ↦ w (x.1, x.2.1) (x.1, x.2.2.1) (𝟙 _, x.2.2.2), Φ.injective ?_⟩
  rw [← shuffle_crossZ F Φ hΦ, ← hw]
  funext ⟨⟨a, a', φ⟩, ⟨b, b', ψ⟩⟩
  rw [shuffle_coboundary_one, map_sub, Pi.sub_apply, phi_right Φ hΦ Φ₁ hΦ₁, phi_left Φ hΦ Φ₂ hΦ₂]
  simp only [LinearEquiv.apply_symm_apply]
  abel

theorem map_iotaQ_eq_zero (R : Type) [CommRing R] (C : Type) [Category.{0} C] [Finite C] [Quiver.IsThin C]
    (F : C ⥤ CommAlgCat.{0} R) (t : H1 F ⊗[R] H1 F) (ht : TensorProduct.lift (crossB F) t = 0) :
    TensorProduct.map (iotaQ F) (iotaQ F) t = 0 := by
  obtain ⟨s, rfl⟩ := TensorProduct.map_surjective (H1.mk_surjective F) (H1.mk_surjective F) t
  rw [← mk_crossZ] at ht
  obtain ⟨w, hw⟩ := H2.mk_eq_zero.1 ht
  obtain ⟨u, v, huv⟩ := exists_boundary F s w hw
  let q := (LinearMap.range (d0 F)).mkQ
  have hq : ∀ g, q (d0 F g) = 0 := fun g ↦ (Submodule.Quotient.mk_eq_zero _).2 ⟨g, rfl⟩
  have h1 : ∀ s : Z1 F ⊗[R] Z1 F, TensorProduct.map (iotaQ F) (iotaQ F) (TensorProduct.map (H1.mk F) (H1.mk F) s) =
      TensorProduct.map q q (TensorProduct.map (Z1 F).subtype (Z1 F).subtype s) := fun s ↦ by
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul f h => rfl
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have h2 : ∀ v : C0 F ⊗[R] C1 F, TensorProduct.map q q (TensorProduct.map (d0 F) LinearMap.id v) = 0 := fun v ↦ by
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul f h => simp [hq]
    | add a b ha hb => simp only [map_add (f := _), ha, hb, add_zero]
  have h3 : ∀ u : C1 F ⊗[R] C0 F, TensorProduct.map q q (TensorProduct.map LinearMap.id (d0 F) u) = 0 := fun u ↦ by
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul f h => simp [hq]
    | add a b ha hb => simp only [map_add (f := _), ha, hb, add_zero]
  rw [h1, huv, map_sub, h2, h3, sub_zero]

end GlobalTheory.CompanionTheory.WedgeOf.Shuffle
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupProductCompatibleWithComparison
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC.DictCup

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}

theorem mp_val_congr (x : Cn F 1) {c c' : Fin (1 + 1) ⥤ C} (hc : c = c') {T : C}
    (g : c.obj (Fin.last 1) ⟶ T) (g' : c'.obj (Fin.last 1) ⟶ T) (hg : HEq g g') :
    mp F g (x c) = mp F g' (x c') := by
  subst hc
  obtain rfl := eq_of_heq hg
  rfl

theorem blockDecomposition_mk₂_fact {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (h : (0 : Fin 3) ⟶ 1) :
    (ComposableArrows.mk₂ φ ψ).map h = φ := by
  rw [show h = homOfLE (by decide) from Subsingleton.elim _ _]
  rfl

theorem composableArrows_mk₂_map_one_two {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (h : (1 : Fin 3) ⟶ 2) :
    (ComposableArrows.mk₂ φ ψ).map h = ψ := by
  rw [show h = homOfLE (by decide) from Subsingleton.elim _ _]
  rfl

theorem front_chain {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    (fr 1).monotone.functor ⋙ ComposableArrows.mk₂ φ ψ = ComposableArrows.mk₁ φ := by
  refine ComposableArrows.ext₁ rfl rfl ?_
  show _ = 𝟙 _ ≫ φ ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]
  exact blockDecomposition_mk₂_fact φ ψ (homOfLE (by decide))

theorem face_chain {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    (dl (0 : Fin (1 + 1 + 1))).monotone.functor ⋙ ComposableArrows.mk₂ φ ψ = ComposableArrows.mk₁ ψ := by
  refine ComposableArrows.ext₁ rfl rfl ?_
  show _ = 𝟙 _ ≫ ψ ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]
  exact composableArrows_mk₂_map_one_two φ ψ (homOfLE (by decide))

theorem cup1_mk₂_eq_mp_mul (x x' : Cn F 1) {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'')
    (y : F.obj T') (y' : F.obj T'') (hy : x (ComposableArrows.mk₁ φ) = y)
    (hy' : x' (ComposableArrows.mk₁ ψ) = y') :
    cup1 F 1 x x' (ComposableArrows.mk₂ φ ψ) = mp F ψ y * y' := by
  have e₁ : pr F (fr 1) x (ComposableArrows.mk₂ φ ψ) = mp F ψ y := by
    rw [pr_apply, ← hy]
    refine mp_val_congr x (front_chain φ ψ) _ ψ (heq_of_eq (composableArrows_mk₂_map_one_two φ ψ _))
  have e₂ : pr F (dl 0) x' (ComposableArrows.mk₂ φ ψ) = y' := by
    rw [pr_apply, ← hy']
    refine (mp_val_congr x' (face_chain φ ψ) _ (𝟙 T'') (heq_of_eq ?_)).trans (mp_id F _ _)
    exact (ComposableArrows.mk₂ φ ψ).map_id _
  rw [cup1_apply]
  exact congrArg₂ (· * ·) e₁ e₂

end GlobalTheory.CompanionTheory.HopfC.DictCup

namespace GlobalTheory.CompanionTheory.HopfC

theorem dict_cup : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (u₁ : H1 F →ₗ[R] HH F 1) (u₂ : H2 F →ₗ[R] HH F 2), IsIdealValuedLiftSystemCocycle F u₁ → IsDegreeTwoComparison F u₂ → (∀ f : Z1 F, ∃ x : Zc F 1, ∀ (T T' : C) (φ : T ⟶ T'), x.1 (ComposableArrows.mk₁ φ) = f.1 T T' φ) → ∀ a b, u₂ (cup F a b) = Lc F 1 (u₁ a) (u₁ b) := by
  intro R _ C _ F u₁ u₂ h₁ h₂ hx a b
  obtain ⟨f, rfl⟩ := H1.mk_surjective F a
  obtain ⟨f', rfl⟩ := H1.mk_surjective F b
  obtain ⟨x, hf⟩ := hx f
  obtain ⟨x', hf'⟩ := hx f'
  rw [h₁ f x hf, h₁ f' x' hf', Lc_mk, cup_mk]
  refine h₂ (cupZ F f f') (cz F 1 x x') fun T T' T'' φ ψ ↦ ?_
  rw [cz_val, cupZ_apply]
  exact DictCup.cup1_mk₂_eq_mp_mul x.1 x'.1 φ ψ _ _ (hf T T' φ) (hf' T' T'' ψ)

end GlobalTheory.CompanionTheory.HopfC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteFunctorCategoryOfMeetLattice
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem finite_chains_semilattice : ∀ {P : Type} [SemilatticeInf P] [Finite P] (p : ℕ),
    Finite (Fin (p + 1) ⥤ Pᵒᵖ) := by
  intro P _ _ p
  haveI : Finite Pᵒᵖ := Finite.of_equiv P Opposite.equivToOpposite
  refine Finite.of_injective (fun F : Fin (p + 1) ⥤ Pᵒᵖ => F.obj) ?_
  intro F G h
  exact CategoryTheory.Functor.ext (fun i => congrFun h i)
    (fun i j f => Quiver.Hom.unop_inj (Subsingleton.elim _ _))

end GlobalTheory.CompanionTheory.HopfC
end

