module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0349
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgebraPullbackTwoConvMulSymmetricCocycle
section
set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv

namespace GlobalTheory

namespace PDiv

namespace CocycleSum

theorem four {M N : Type} [CommMonoid M] [AddCommGroup N] (c : M → M → N)
    (h : ∀ x y z, c y z - c (x * y) z + c x (y * z) - c x y = 0) (hs : ∀ x y, c x y = c y x)
    (a b a' b' : M) :
    c (a * b) (a' * b') = c a a' + c b b' + (c (a * a') (b * b') - c a b - c a' b') := by
  have h1 := h a b (a' * b')
  have h2 := h a a' (b * b')
  have h3 := h a' b' b
  rw [show b * (a' * b') = a' * (b * b') from mul_left_comm _ _ _] at h1
  rw [show b' * b = b * b' from mul_comm _ _, hs (a' * b') b, hs b' b] at h3
  rw [← sub_eq_zero]
  have e : c (a * b) (a' * b') - (c a a' + c b b' + (c (a * a') (b * b') - c a b - c a' b')) =
      -(c b (a' * b') - c (a * b) (a' * b') + c a (a' * (b * b')) - c a b) +
      (c a' (b * b') - c (a * a') (b * b') + c a (a' * (b * b')) - c a a') -
      (c b b' - c b (a' * b') + c a' (b * b') - c a' b') := by abel
  rw [e, h1, h2, h3]
  simp

variable {R A X : Type} [CommRing R] [CommRing A] [CommRing X] [Bialgebra R A] [Algebra R X]

def val (x y : WithConv (A →ₐ[R] X)) : A ⊗[R] A →ₐ[R] X :=
  Algebra.TensorProduct.lift x.ofConv y.ofConv fun _ _ => .all ..

@[simp] theorem val_tmul (x y : WithConv (A →ₐ[R] X)) (a b : A) :
    val x y (a ⊗ₜ b) = x.ofConv a * y.ofConv b := rfl

theorem mul_apply (x y : WithConv (A →ₐ[R] X)) (a : A) :
    (x * y).ofConv a = val x y (comul a) := by
  rw [val]
  exact AlgHom.convMul_apply x y a

theorem lift_cobTwo (x y z : WithConv (A →ₐ[R] X)) (c : A ⊗[R] A) :
    Algebra.TensorProduct.lift x.ofConv (val y z) (fun _ _ => .all ..) (cobTwo R A c) =
      val y z c - val (x * y) z c + val x (y * z) c - val x y c := by
  have hA : ∀ (t : A ⊗[R] A) (b : A),
      Algebra.TensorProduct.lift x.ofConv (val y z) (fun _ _ => .all ..)
        (TensorProduct.assoc R A A A (t ⊗ₜ b)) = val x y t * z.ofConv b := by
    intro t b
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a a' => simp [mul_assoc]
    | add u v hu hv => simp only [TensorProduct.add_tmul, map_add (f := _), hu, hv, add_mul]
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [cobTwo_apply]
    simp only [map_sub, map_add (f := _), TensorProduct.mk_apply, LinearMap.rTensor_tmul,
      LinearMap.lTensor_tmul, LinearMap.flip_apply, Algebra.TensorProduct.lift_tmul, val_tmul, hA,
      mul_apply, map_one, one_mul, mul_one]
  | add u v hu hv =>
    simp only [map_add (f := _), hu, hv]
    abel

theorem val_comm (x y : WithConv (A →ₐ[R] X)) (c : A ⊗[R] A) :
    val x y (TensorProduct.comm R A A c) = val y x c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [TensorProduct.comm_tmul, val_tmul, val_tmul, mul_comm]
  | add u v hu hv => simp only [map_add (f := _), hu, hv]

theorem val_push {Y : Type} [CommRing Y] [Algebra R Y] (u : X →ₐ[R] Y)
    (x y : WithConv (A →ₐ[R] X)) (c : A ⊗[R] A) :
    val (ptsPush A u x) (ptsPush A u y) c = u (val x y c) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp only [val_tmul, ptsPush_ofConv, AlgHom.comp_apply, map_mul]
  | add u v hu hv => simp only [map_add (f := _), hu, hv]

variable {B : Type} [CommRing B] [Bialgebra R B]

theorem val_include (x y : WithConv (A →ₐ[R] B)) (c : A ⊗[R] A) :
    val (ptsPush A (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B) x)
      (ptsPush A (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B) y) c =
      TensorProduct.map x.ofConv.toLinearMap y.ofConv.toLinearMap c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [val_tmul, ptsPush_ofConv, AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul, TensorProduct.map_tmul, AlgHom.toLinearMap_apply]
  | add u v hu hv => simp only [map_add (f := _), hu, hv]

theorem include_mul (f : A →ₐc[R] B) :
    ptsPush A (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B) (toConv (f : A →ₐ[R] B)) *
      ptsPush A (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B) (toConv (f : A →ₐ[R] B)) =
      ptsPush A (comulAlgHom R B) (toConv (f : A →ₐ[R] B)) := by
  apply WithConv.ext
  ext a
  rw [mul_apply, val_include]
  simp only [ptsPush_ofConv, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
  exact CoalgHomClass.map_comp_comul_apply f a

end CocycleSum


open CocycleSum in
theorem pullTwo_convMul {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A]
    [Bialgebra R B] [IsCocomm R A] (f g : A →ₐc[R] B) (c : A ⊗[R] A) (hc : c ∈ symCocycles R A) :
    pullbackTwo (toConv f * toConv g).ofConv c = pullbackTwo f c + pullbackTwo g c +
      cobOne R B (LinearMap.mul' R B
        (TensorProduct.map (f : A →ₗ[R] B) (g : A →ₗ[R] B) c)) := by
  obtain ⟨hc2, hcs⟩ := mem_symCocycles.1 hc
  have hv : ∀ (x y : WithConv (A →ₐ[R] B)) (t : A ⊗[R] A), val x y t =
      LinearMap.mul' R B (TensorProduct.map x.ofConv.toLinearMap y.ofConv.toLinearMap t) := by
    intro x y t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add u v hu hv => simp only [map_add (f := _), hu, hv]
  have key := four (M := WithConv (A →ₐ[R] B ⊗[R] B)) (fun x y => val x y c)
    (fun x y z => (lift_cobTwo x y z c).symm.trans (by rw [hc2, map_zero]))
    (fun x y => by rw [← val_comm, hcs])
    (ptsPush A (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B) (toConv (f : A →ₐ[R] B)))
    (ptsPush A (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B) (toConv (g : A →ₐ[R] B)))
    (ptsPush A (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B) (toConv (f : A →ₐ[R] B)))
    (ptsPush A (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B) (toConv (g : A →ₐ[R] B)))
  rw [← map_mul (ptsPush A (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B)),
    ← map_mul (ptsPush A (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B)),
    include_mul f, include_mul g, val_include, val_include, val_include, val_push, val_push,
    val_push] at key
  have hl : ∀ h : A →ₐc[R] B, (h : A →ₗ[R] B) = (h : A →ₐ[R] B).toLinearMap := fun _ => rfl
  have hfg : ((toConv f * toConv g).ofConv : A →ₐ[R] B) =
      (toConv (f : A →ₐ[R] B) * toConv (g : A →ₐ[R] B)).ofConv :=
    congrArg WithConv.ofConv (BialgHom.toAlgHom_convMul (toConv f) (toConv g))
  have hv' : LinearMap.mul' R B (TensorProduct.map (f : A →ₗ[R] B) (g : A →ₗ[R] B) c) =
      val (toConv (f : A →ₐ[R] B)) (toConv (g : A →ₐ[R] B)) c := by
    rw [hv, hl, hl]
  unfold pullbackTwo
  rw [hl, hfg, key, cobOne_apply, hv', Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, hl, hl]
  rfl

end PDiv

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveBaseChangeDescendsFilteredColimit
section
open CategoryTheory Limits TensorProduct

namespace GlobalTheory.BijDescent

theorem exists_stage_isIso {K : Type} [SmallCategory K] [IsFiltered K]
    {R₀ A B : CommRingCat.{0}} (P EA EB : K ⥤ CommRingCat.{0}) (β : ∀ k, R₀ ⟶ P.obj k)
    (fA : R₀ ⟶ A) (fB : R₀ ⟶ B) (hA : fA.hom.FinitePresentation)
    (hB : fB.hom.FinitePresentation) (g : A ⟶ B) (hg : fA ≫ g = fB)
    (uA : P ⟶ EA) (vA : (Functor.const K).obj A ⟶ EA) (uB : P ⟶ EB)
    (vB : (Functor.const K).obj B ⟶ EB)
    (hpoA : ∀ k, IsPushout fA (β k) (vA.app k) (uA.app k))
    (hpoB : ∀ k, IsPushout fB (β k) (vB.app k) (uB.app k))
    (cA : Cocone EA) (hcA : IsColimit cA) (cB : Cocone EB) (hcB : IsColimit cB)
    (iA : A ⟶ cA.pt) (iB : B ⟶ cB.pt) (hiA : ∀ k, vA.app k ≫ cA.ι.app k = iA)
    (hiB : ∀ k, vB.app k ≫ cB.ι.app k = iB) (G : cA.pt ⟶ cB.pt) [IsIso G]
    (hG : ∀ k, (hpoA k).desc (g ≫ vB.app k) (uB.app k)
      (by rw [reassoc_of% hg, (hpoB k).w]) ≫ cB.ι.app k = cA.ι.app k ≫ G) :
    ∃ m : K, ∀ (l : K) (_ : m ⟶ l), IsIso ((hpoA l).desc (g ≫ vB.app l) (uB.app l)
      (by rw [reassoc_of% hg, (hpoB l).w])) := by
  let gs : ∀ k, EA.obj k ⟶ EB.obj k := fun k =>
    (hpoA k).desc (g ≫ vB.app k) (uB.app k) (by rw [reassoc_of% hg, (hpoB k).w])
  have gv : ∀ k, vA.app k ≫ gs k = g ≫ vB.app k := fun k => (hpoA k).inl_desc _ _ _
  have gu : ∀ k, uA.app k ≫ gs k = uB.app k := fun k => (hpoA k).inr_desc _ _ _
  have vAn : ∀ {k l} (f : k ⟶ l), vA.app k ≫ EA.map f = vA.app l := fun f =>
    (vA.naturality f).symm.trans (Category.id_comp _)
  have vBn : ∀ {k l} (f : k ⟶ l), vB.app k ≫ EB.map f = vB.app l := fun f =>
    (vB.naturality f).symm.trans (Category.id_comp _)
  have gnat : ∀ {k l} (f : k ⟶ l), EA.map f ≫ gs l = gs k ≫ EB.map f := by
    intro k l f
    apply (hpoA k).hom_ext
    · rw [reassoc_of% (vAn f), gv, reassoc_of% (gv k), vBn]
    · rw [← uA.naturality_assoc, gu, reassoc_of% (gu k), uB.naturality]
  obtain ⟨k₀⟩ := IsFiltered.nonempty (C := K)
  have hAG : iA ≫ G = g ≫ iB := by
    rw [← hiA k₀, Category.assoc, ← hG, reassoc_of% (gv k₀), hiB]
  let αA : (Functor.const K).obj R₀ ⟶ EA := (Functor.const K).map fA ≫ vA
  let αB : (Functor.const K).obj R₀ ⟶ EB := (Functor.const K).map fB ≫ vB
  obtain ⟨m, s, hs⟩ := GlobalTheory.TorsorColim.exists_stage_factor (I := Unit) EA αA fB cA hcA hB
    (fun _ => iB ≫ inv G) (fun _ k => by
      change fB ≫ iB ≫ inv G = (fA ≫ vA.app k) ≫ cA.ι.app k
      rw [Category.assoc, hiA, ← hg, Category.assoc, ← reassoc_of% hAG, IsIso.hom_inv_id,
        Category.comp_id])
  have hs1 : fB ≫ s () = fA ≫ vA.app m := (hs ()).1
  have hs2 : s () ≫ cA.ι.app m = iB ≫ inv G := (hs ()).2
  obtain ⟨m₁, p₁, hp₁⟩ := GlobalTheory.TorsorColim.exists_stage_eq (I := Unit) EA αA fA cA hcA
    (RingHom.FiniteType.essFiniteType (RingHom.FiniteType.of_finitePresentation hA)) (k := m)
    (fun _ => g ≫ s ()) (fun _ => vA.app m) (fun _ => by rw [reassoc_of% hg, hs1]; rfl)
    (fun _ => rfl) (fun _ => by
      rw [Category.assoc, hs2, hiA, ← reassoc_of% hAG, IsIso.hom_inv_id, Category.comp_id])
  obtain ⟨m₂, p₂, hp₂⟩ := GlobalTheory.TorsorColim.exists_stage_eq (I := Unit) EB αB fB cB hcB
    (RingHom.FiniteType.essFiniteType (RingHom.FiniteType.of_finitePresentation hB)) (k := m)
    (fun _ => s () ≫ gs m) (fun _ => vB.app m)
    (fun _ => by
      change fB ≫ s () ≫ gs m = fB ≫ vB.app m
      rw [reassoc_of% hs1, gv, reassoc_of% hg])
    (fun _ => rfl) (fun _ => by
      rw [Category.assoc, hG, reassoc_of% hs2, IsIso.inv_hom_id, Category.comp_id, hiB])
  let a := IsFiltered.leftToMax m₁ m₂
  let b := IsFiltered.rightToMax m₁ m₂
  let e := IsFiltered.coeqHom (p₁ ≫ a) (p₂ ≫ b)
  have he : (p₁ ≫ a) ≫ e = (p₂ ≫ b) ≫ e := IsFiltered.coeq_condition _ _
  refine ⟨IsFiltered.coeq (p₁ ≫ a) (p₂ ≫ b), fun l f => ?_⟩
  obtain ⟨F', hF'⟩ : ∃ F' : m ⟶ l, F' = (p₁ ≫ a) ≫ e ≫ f := ⟨_, rfl⟩
  have h₁ : g ≫ s () ≫ EA.map F' = vA.app l := by
    subst hF'
    have := hp₁ ()
    simp only [Category.assoc] at this
    rw [← vAn ((p₁ ≫ a) ≫ e ≫ f)]
    simp only [EA.map_comp, Category.assoc]
    rw [reassoc_of% this]
  have h₂ : s () ≫ gs m ≫ EB.map F' = vB.app l := by
    subst hF'
    have := hp₂ ()
    simp only [Category.assoc] at this
    rw [← Category.assoc (p₁ ≫ a), he, ← vBn ((p₂ ≫ b) ≫ e ≫ f)]
    simp only [EB.map_comp, Category.assoc]
    rw [reassoc_of% this]
  let σ : EB.obj l ⟶ EA.obj l := (hpoB l).desc (s () ≫ EA.map F') (uA.app l)
    (by rw [reassoc_of% hs1, vAn, (hpoA l).w])
  have σv : vB.app l ≫ σ = s () ≫ EA.map F' := (hpoB l).inl_desc _ _ _
  have σu : uB.app l ≫ σ = uA.app l := (hpoB l).inr_desc _ _ _
  refine ⟨σ, ?_, ?_⟩
  · apply (hpoA l).hom_ext
    · change vA.app l ≫ gs l ≫ σ = _
      rw [reassoc_of% (gv l), σv, h₁, Category.comp_id]
    · change uA.app l ≫ gs l ≫ σ = _
      rw [reassoc_of% (gu l), σu, Category.comp_id]
  · apply (hpoB l).hom_ext
    · change vB.app l ≫ σ ≫ gs l = _
      rw [reassoc_of% σv, gnat, h₂, Category.comp_id]
    · change uB.app l ≫ σ ≫ gs l = _
      rw [reassoc_of% σu, gu, Category.comp_id]

end GlobalTheory.BijDescent

namespace GlobalTheory.BijDescent

theorem bijective_of_isColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (R S : Type) [CommRing R] [CommRing S]
    [Algebra (F.obj j) R] [Algebra (F.obj j) S] [Algebra.FinitePresentation (F.obj j) R]
    [Algebra.FinitePresentation (F.obj j) S] (φ : R →ₐ[F.obj j] S), φ.toRingHom.Finite →
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id c.pt c.pt) φ)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id (F.obj k) (F.obj k)) φ) := by
  intro J _ _ F c hc j R S _ _ _ _ _ _ φ _ hbij
  letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  let fR : F.obj j ⟶ CommRingCat.of R := CommRingCat.ofHom (algebraMap (F.obj j) R)
  let fS : F.obj j ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap (F.obj j) S)
  have hfR : fR.hom.FinitePresentation := RingHom.finitePresentation_algebraMap.2 inferInstance
  have hfS : fS.hom.FinitePresentation := RingHom.finitePresentation_algebraMap.2 inferInstance
  let g : CommRingCat.of R ⟶ CommRingCat.of S := CommRingCat.ofHom φ.toRingHom
  have hg : fR ≫ g = fS := by ext x; exact φ.commutes x
  have sqR := (CommRingCat.isPushout_tensorProduct (F.obj j) c.pt R).flip
  have sqS := (CommRingCat.isPushout_tensorProduct (F.obj j) c.pt S).flip
  obtain ⟨ER, ιR, uR, vR, ⟨hER⟩, hkR⟩ :=
    GlobalTheory.BaseChangeColim.exists_isColimit_pushout_under J F c hc j _ _ fR _ _ sqR
  obtain ⟨ES, ιS, uS, vS, ⟨hES⟩, hkS⟩ :=
    GlobalTheory.BaseChangeColim.exists_isColimit_pushout_under J F c hc j _ _ fS _ _ sqS
  let G : CommRingCat.of (c.pt ⊗[F.obj j] R) ⟶ CommRingCat.of (c.pt ⊗[F.obj j] S) :=
    CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id c.pt c.pt) φ).toRingHom
  haveI : IsIso G := (ConcreteCategory.isIso_iff_bijective G).2 hbij
  have hGr : g ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := F.obj j) (A := c.pt) (B := S)).toRingHom =
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := F.obj j) (A := c.pt) (B := R)).toRingHom ≫ G := by
    ext x; simp [g, G]
  obtain ⟨m, hm⟩ := exists_stage_isIso (K := Under j) (Under.forget j ⋙ F) ER ES
    (fun k => F.map k.hom) fR fS hfR hfS g hg uR vR uS vS (fun k => (hkR k).1) (fun k => (hkS k).1)
    (Cocone.mk _ ιR) hER (Cocone.mk _ ιS) hES _ _ (fun k => (hkR k).2.1) (fun k => (hkS k).2.1) G
    (fun k => by
      have key : ∀ d : ER.obj k ⟶ ES.obj k, vR.app k ≫ d = g ≫ vS.app k →
          uR.app k ≫ d = uS.app k → d ≫ ιS.app k = ιR.app k ≫ G := by
        intro d hd1 hd2
        apply (hkR k).1.hom_ext
        · rw [reassoc_of% hd1, (hkS k).2.1, reassoc_of% (hkR k).2.1, hGr]
        · change uR.app k ≫ d ≫ ιS.app k = uR.app k ≫ ιR.app k ≫ G
          erw [reassoc_of% hd2, (hkS k).2.2, reassoc_of% (hkR k).2.2]
          ext x
          simp [G]
      exact key _ ((hkR k).1.inl_desc _ _ _) ((hkR k).1.inr_desc _ _ _))
  refine ⟨m.right, m.hom, fun k f => ?_⟩
  let l : Under j := Under.mk (m.hom ≫ f)
  obtain ⟨d, hd1, hd2, hdiso⟩ : ∃ d : ER.obj l ⟶ ES.obj l, vR.app l ≫ d = g ≫ vS.app l ∧
      uR.app l ≫ d = uS.app l ∧ IsIso d :=
    ⟨_, (hkR l).1.inl_desc _ _ _, (hkR l).1.inr_desc _ _ _, hm l (Under.homMk f rfl)⟩
  letI : Algebra (F.obj j) (F.obj k) := (F.map (m.hom ≫ f)).hom.toAlgebra
  have tR := (CommRingCat.isPushout_tensorProduct (F.obj j) (F.obj k) R).flip
  have tS := (CommRingCat.isPushout_tensorProduct (F.obj j) (F.obj k) S).flip
  let M : CommRingCat.of (F.obj k ⊗[F.obj j] R) ⟶ CommRingCat.of (F.obj k ⊗[F.obj j] S) :=
    CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id (F.obj k) (F.obj k)) φ).toRingHom
  have hM : M = ((hkR l).1.isoIsPushout _ _ tR).inv ≫ d ≫ ((hkS l).1.isoIsPushout _ _ tS).hom := by
    apply tR.hom_ext
    · erw [IsPushout.inl_isoIsPushout_inv_assoc _ _ (hkR l).1 tR, reassoc_of% hd1,
        IsPushout.inl_isoIsPushout_hom _ _ (hkS l).1 tS]
      ext x
      simp [M, g]
    · erw [IsPushout.inr_isoIsPushout_inv_assoc _ _ (hkR l).1 tR, reassoc_of% hd2,
        IsPushout.inr_isoIsPushout_hom _ _ (hkS l).1 tS]
      ext x
      simp [M]
  haveI : IsIso M := by rw [hM]; infer_instance
  exact (ConcreteCategory.isIso_iff_bijective M).1 this

end GlobalTheory.BijDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUpperTwistedConjIffDefinedOverBase
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.FlagDesc

def parAlg (K : Type) [Field K] (a n : ℕ) : Subalgebra K (Matrix (Fin n) (Fin n) K) where
  carrier := {M | ∀ i j : Fin n, (j : ℕ) < a → a ≤ (i : ℕ) → M i j = 0}
  mul_mem' {M N} hM hN i j hj hi := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : (k : ℕ) < a
    · rw [hM i k hk hi, zero_mul]
    · rw [hN k j hj (not_lt.1 hk), mul_zero]
  add_mem' {M N} hM hN i j hj hi := by
    rw [Matrix.add_apply, hM i j hj hi, hN i j hj hi, add_zero]
  algebraMap_mem' c i j hj hi := by
    have hij : i ≠ j := fun h => by subst h; omega
    simp [Matrix.algebraMap_matrix_apply, hij]

theorem inPar_iff_mem {K : Type} [Field K] {a n : ℕ} (x : GL (Fin n) K) :
    InPar a x ↔ (x : Matrix (Fin n) (Fin n) K) ∈ parAlg K a n := Iff.rfl

theorem inPar_one {K : Type} [Field K] (a n : ℕ) : InPar a (1 : GL (Fin n) K) := by
  intro i j hj hi
  have hij : i ≠ j := fun h => by subst h; omega
  simp [Matrix.one_apply_ne hij]

theorem inPar_mul {K : Type} [Field K] {a n : ℕ} {x z : GL (Fin n) K} (hx : InPar a x) (hz : InPar a z) :
    InPar a (x * z) := by
  rw [inPar_iff_mem, Units.val_mul]
  exact (parAlg K a n).mul_mem hx hz

theorem inPar_inv {K : Type} [Field K] {a n : ℕ} {x : GL (Fin n) K} (h : InPar a x) : InPar a x⁻¹ := by
  have hb : (x : Matrix (Fin n) (Fin n) K).BlockTriangular
      (fun i : Fin n => if a ≤ (i : ℕ) then (1 : ℕ) else 0) := by
    intro i j hij
    apply h i j
    · by_contra hc
      simp only at hij
      split_ifs at hij <;> omega
    · by_contra hc
      simp only at hij
      split_ifs at hij <;> omega
  intro i j hj hi
  rw [Matrix.coe_units_inv]
  apply Matrix.blockTriangular_inv_of_blockTriangular hb
  simp [hi, not_le.2 hj]

theorem conj_adjoin_mem {K : Type} [Field K] {n : ℕ} (B : Subalgebra K (Matrix (Fin n) (Fin n) K))
    (u : GL (Fin n) K) (M X : Matrix (Fin n) (Fin n) K) (hX : X ∈ Algebra.adjoin K {M})
    (hM : ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * u ∈ B) :
    ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * X * u ∈ B := by
  induction hX using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hM
  | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, Units.inv_mul]
      exact B.smul_mem B.one_mem r
  | add x y _ _ hx hy => rw [mul_add, add_mul]; exact B.add_mem hx hy
  | mul x y _ _ hx hy =>
      have e : ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (x * y) * u =
          (((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * x * u) *
          (((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * y * u) := by
        simp only [mul_assoc, Units.mul_inv_cancel_left]
      rw [e]; exact B.mul_mem hx hy

variable {F F' : Type} [Field F] [Field F'] [Algebra F F']

theorem galAct_coe (n : ℕ) (t : F' ≃ₐ[F] F') (x : GL (Fin n) F') (i j : Fin n) :
    (galAct F F' n t x : Matrix (Fin n) (Fin n) F') i j = t ((x : Matrix (Fin n) (Fin n) F') i j) := by
  simp [galAct_apply, gal]

theorem incl_coe (n : ℕ) (x : GL (Fin n) F) (i j : Fin n) :
    (incl F F' n x : Matrix (Fin n) (Fin n) F') i j = algebraMap F F' ((x : Matrix (Fin n) (Fin n) F) i j) := by
  simp [incl, gal]

theorem inPar_galAct {a n : ℕ} (t : F' ≃ₐ[F] F') {x : GL (Fin n) F'} (h : InPar a x) :
    InPar a (galAct F F' n t x) := by
  intro i j hj hi
  rw [galAct_coe, h i j hj hi, map_zero]

theorem inPar_incl {a n : ℕ} (x : GL (Fin n) F) : InPar a (incl F F' n x) ↔ InPar a x := by
  constructor
  · intro h i j hj hi
    have := h i j hj hi
    rw [incl_coe] at this
    exact (FaithfulSMul.algebraMap_injective F F') (by rw [this, map_zero])
  · intro h i j hj hi
    rw [incl_coe, h i j hj hi, map_zero]

theorem inPar_nrm {a n : ℕ} (s : F' ≃ₐ[F] F') {x : GL (Fin n) F'} (h : InPar a x) : InPar a (nrm s x) := by
  unfold nrm nrmG
  apply List.prod_induction (fun z => InPar a z)
  · intro u v hu hv; exact inPar_mul hu hv
  · exact inPar_one a n
  · intro z hz
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz
    exact inPar_galAct _ h

theorem nrm_one' (s : F' ≃ₐ[F] F') (n : ℕ) : nrm s (1 : GL (Fin n) F') = 1 := by
  unfold nrm nrmG
  apply List.prod_eq_one
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact map_one _

end GlobalTheory.Shin.FlagDesc


open GlobalTheory.Shin.FlagDesc in
theorem GlobalTheory.Shin.inPar_twistedConj_iff : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (a n : ℕ), a ≤ n → ∀ (γ : GL (Fin n) F) (δ y : GL (Fin n) F'), (δ : Matrix (Fin n) (Fin n) F') ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} → nrm s δ = incl F F' n γ → (InPar a (y⁻¹ * δ * galAct F F' n s y) ↔ ∃ (y₀ : GL (Fin n) F) (p : GL (Fin n) F'), InPar a p ∧ y = incl F F' n y₀ * p ∧ InPar a (y₀⁻¹ * γ * y₀)) := by
  intro F F' _ _ _ _ s hs a n _ γ δ y hδ hN
  obtain ⟨hfix, -, hconj, -, -⟩ := GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n
  have hB : ∀ x ∈ parAlg F' a n, x.map s ∈ parAlg F' a n := by
    intro M hM i j hj hi
    simp only [Matrix.map_apply]
    rw [hM i j hj hi, map_zero]
  constructor
  · intro hq
    have hγP : InPar a (y⁻¹ * incl F F' n γ * y) := by
      rw [← hN, ← hconj]; exact inPar_nrm s hq
    have hδP : InPar a (y⁻¹ * δ * y) := by
      rw [inPar_iff_mem, Units.val_mul, Units.val_mul]
      apply conj_adjoin_mem _ y _ _ hδ
      have := (inPar_iff_mem _).1 hγP
      rwa [Units.val_mul, Units.val_mul] at this
    have hεP : InPar a (y⁻¹ * galAct F F' n s y) := by
      have e : y⁻¹ * galAct F F' n s y = (y⁻¹ * δ * y)⁻¹ * (y⁻¹ * δ * galAct F F' n s y) := by group
      rw [e]; exact inPar_mul (inPar_inv hδP) hq
    have hεN : nrm s (y⁻¹ * galAct F F' n s y) = 1 := by
      have := hconj 1 y
      rw [nrm_one', mul_one, inv_mul_cancel] at this
      exact this
    obtain ⟨x, hxB, hε⟩ := GlobalTheory.T.exists_coboundary_of_norm_one_in_subalgebra F F' s hs n (parAlg F' a n) hB _ hεP hεN
    have hfx : galAct F F' n s (y * x⁻¹) = y * x⁻¹ := by
      rw [map_mul, map_inv]
      calc galAct F F' n s y * (galAct F F' n s x)⁻¹
          = y * (y⁻¹ * galAct F F' n s y) * (galAct F F' n s x)⁻¹ := by group
        _ = y * (x⁻¹ * galAct F F' n s x) * (galAct F F' n s x)⁻¹ := by rw [hε]
        _ = y * x⁻¹ := by group
    obtain ⟨y₀, hy₀⟩ := (hfix _).1 hfx
    refine ⟨y₀, x, hxB, by rw [hy₀]; group, ?_⟩
    rw [← inPar_incl (F' := F'), map_mul, map_mul, map_inv, hy₀]
    have e : (y * x⁻¹)⁻¹ * incl F F' n γ * (y * x⁻¹) = x * (y⁻¹ * incl F F' n γ * y) * x⁻¹ := by group
    rw [e]
    exact inPar_mul (inPar_mul hxB hγP) (inPar_inv hxB)
  · rintro ⟨y₀, p, hp, rfl, hγ0⟩
    have hs0 : galAct F F' n s (incl F F' n y₀) = incl F F' n y₀ := (hfix _).2 ⟨y₀, rfl⟩
    have e : (incl F F' n y₀ * p)⁻¹ * δ * galAct F F' n s (incl F F' n y₀ * p) =
        p⁻¹ * ((incl F F' n y₀)⁻¹ * δ * incl F F' n y₀) * galAct F F' n s p := by
      rw [map_mul, hs0]; group
    rw [e]
    have hmid : InPar a ((incl F F' n y₀)⁻¹ * δ * incl F F' n y₀) := by
      rw [inPar_iff_mem, Units.val_mul, Units.val_mul]
      apply conj_adjoin_mem _ _ _ _ hδ
      have := (inPar_iff_mem _).1 ((inPar_incl (F' := F') _).2 hγ0)
      rwa [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul] at this
    exact inPar_mul (inPar_mul (inPar_inv hp) hmid) (inPar_galAct s hp)
end

