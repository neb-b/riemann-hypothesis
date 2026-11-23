module

public import Development.EtaleCohomology.TateTwists.Bundle0030
public import Development.EtaleCohomology.TateTwists.TensorVanishing.TensZero
public import Development.EtaleCohomology.TateTwists.Bundle0029

@[expose] public section

-- bundled from Development.EtaleCohomology.TateTwists.MapMapEq
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleFoundations.columnPf

def kerLoc : Prop :=
  ∀ (R : Type) [CommRing R] (M : Shv R) (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ M.obj),
    (∀ (U : Scheme.{0}) (y : Sec M U), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = Sec.res g y) →
    (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) →
    ∀ (G : Shv R) (V : Scheme.{0}) (u : Sec G V ⊗[ULift.{1} R] P.obj (op V)),
      TensorProduct.map LinearMap.id (φ.app (op V)).hom u = 0 →
      Loc V fun _ k => TensorProduct.map (G.obj.map k.op).hom (P.map k.op).hom u = 0

theorem map_map_eq {S : Type*} [CommRing S] {A B C D A' B' C' D' : Type*} [AddCommGroup A] [Module S A]
    [AddCommGroup B] [Module S B] [AddCommGroup C] [Module S C] [AddCommGroup D] [Module S D]
    [AddCommGroup A'] [Module S A'] [AddCommGroup B'] [Module S B'] [AddCommGroup C'] [Module S C']
    [AddCommGroup D'] [Module S D']
    (f1 : A →ₗ[S] A') (f2 : A' →ₗ[S] C) (f1' : A →ₗ[S] C') (f2' : C' →ₗ[S] C)
    (g1 : B →ₗ[S] B') (g2 : B' →ₗ[S] D) (g1' : B →ₗ[S] D') (g2' : D' →ₗ[S] D)
    (hf : f2 ∘ₗ f1 = f2' ∘ₗ f1') (hg : g2 ∘ₗ g1 = g2' ∘ₗ g1') (x : A ⊗[S] B) :
    TensorProduct.map f2 g2 (TensorProduct.map f1 g1 x) = TensorProduct.map f2' g2' (TensorProduct.map f1' g1' x) := by
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, hf, hg, TensorProduct.map_comp, LinearMap.comp_apply]

end LateralTheory.EtaleFoundations.columnPf

open LateralTheory.EtaleFoundations.columnPf in
theorem LateralTheory.EtaleFoundations.columnPf.lift_of (hK : kerLoc) : lift := by
  classical
  intro R _ M P φ hsurj hker F G δ U x hx
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset x
  refine loc_bind (loc_finset S fun i _ => hsurj U i.2) ?_
  intro V g hV
  choose p hp using hV
  let x' : Sec F V ⊗[ULift.{1} R] P.obj (op V) := ∑ i ∈ S.attach, (F.obj.map g.op).hom i.1.1 ⊗ₜ p i.1 i.2
  have h1 : TensorProduct.map LinearMap.id (φ.app (op V)).hom x' =
      TensorProduct.map (F.obj.map g.op).hom (M.obj.map g.op).hom x := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hS, map_sum, map_sum, ← Finset.sum_attach S]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [TensorProduct.map_tmul, LinearMap.id_apply]
    rw [hp i.1 i.2]
  have nat : ∀ {V' V : Scheme.{0}} (k : V' ⟶ V), (G.obj.map k.op).hom ∘ₗ (δ.hom.app (op V)).hom =
      (δ.hom.app (op V')).hom ∘ₗ (F.obj.map k.op).hom := fun k => by
    rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, δ.hom.naturality]
  have h2 : TensorProduct.map LinearMap.id (φ.app (op V)).hom
      (TensorProduct.map (δ.hom.app (op V)).hom LinearMap.id x') = 0 := by
    rw [map_map_eq (f1 := (δ.hom.app (op V)).hom) (f2 := LinearMap.id) (g1 := LinearMap.id) (g2 := (φ.app (op V)).hom)
      (f1' := LinearMap.id) (f2' := (δ.hom.app (op V)).hom) (g1' := (φ.app (op V)).hom) (g2' := LinearMap.id)
      (by simp) (by simp), h1,
      map_map_eq (f1 := (F.obj.map g.op).hom) (f2 := (δ.hom.app (op V)).hom) (g1 := (M.obj.map g.op).hom)
      (g2 := LinearMap.id) (f1' := (δ.hom.app (op U)).hom) (f2' := (G.obj.map g.op).hom) (g1' := LinearMap.id)
      (g2' := (M.obj.map g.op).hom) (nat g).symm (by simp), hx, map_zero]
  refine loc_mono (hK R M P φ hsurj hker G V _ h2) ?_
  intro W k hk
  refine ⟨TensorProduct.map (F.obj.map k.op).hom (P.map k.op).hom x', ?_, ?_⟩
  · rw [map_map_eq (f1 := (F.obj.map k.op).hom) (f2 := (δ.hom.app (op W)).hom) (g1 := (P.map k.op).hom)
      (g2 := LinearMap.id) (f1' := (δ.hom.app (op V)).hom) (f2' := (G.obj.map k.op).hom) (g1' := LinearMap.id)
      (g2' := (P.map k.op).hom) (nat k).symm (by simp), hk]
  · have hφ : (φ.app (op W)).hom ∘ₗ (P.map k.op).hom = (M.obj.map k.op).hom ∘ₗ (φ.app (op V)).hom := by
      rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, φ.naturality]
    rw [map_map_eq (f1 := (F.obj.map k.op).hom) (f2 := LinearMap.id) (g1 := (P.map k.op).hom)
      (g2 := (φ.app (op W)).hom) (f1' := LinearMap.id) (f2' := (F.obj.map k.op).hom) (g1' := (φ.app (op V)).hom)
      (g2' := (M.obj.map k.op).hom) (by simp) hφ, h1, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
    simp only [op_comp, Functor.map_comp, ModuleCat.hom_comp]

open LateralTheory.EtaleFoundations.columnPf in
theorem LateralTheory.EtaleFoundations.columnPf.column_of' (hK : kerLoc) : LateralTheory.EtaleFoundations.acyc.column :=
  LateralTheory.EtaleFoundations.acyc.column_of_cut (lift_of hK) kill_of
end

-- bundled from Development.EtaleCohomology.TateTwists.TensorVanishing
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

noncomputable section
namespace LateralTheory.EtaleFoundations.stairPf
variable {R : Type} [CommRing R] {C J T : Cx R}

theorem tens_zero' {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module (ULift.{1} R) M]
    [Module (ULift.{1} R) N] (hN : ∀ m : N, m = 0) (x : M ⊗[ULift.{1} R] N) : x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul m n => rw [hN n, TensorProduct.tmul_zero]
  | add a b ha hb => rw [ha, hb, add_zero]

theorem res_apply {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens C J U w) (p : Ix w) :
    (Tens.res g w x) p = TensorProduct.map ((C.X p.1.1).obj.map g.op).hom ((J.X p.1.2).obj.map g.op).hom (x p) := by
  unfold Tens.res; rw [DirectSum.lmap_apply]

theorem nat_tens {V U : Scheme.{0}} (g : V ⟶ U) (s s' t : ℤ) (v : Sec (C.X s) U ⊗[ULift.{1} R] Sec (J.X t) U) :
    TensorProduct.map ((C.d s s').hom.app (op V)).hom LinearMap.id
        (TensorProduct.map ((C.X s).obj.map g.op).hom ((J.X t).obj.map g.op).hom v) =
      TensorProduct.map ((C.X s').obj.map g.op).hom ((J.X t).obj.map g.op).hom
        (TensorProduct.map ((C.d s s').hom.app (op U)).hom LinearMap.id v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply]
    congr 1; exact map_res (C.d s s') g a
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem lift_Dm' (τ : Pair C J T) (U : Scheme.{0}) (w w' : ℤ) (hw : w + 1 = w') (x : Tens C J U w) :
    τ.lift U w' (Dm U w w' hw x) = Sec.map (T.d w w') (τ.lift U w x) := by
  subst hw; exact lift_Dm τ U w x

theorem lof_shift (U : Scheme.{0}) (n s s' t : ℤ) (hs : s + 1 = s') (h1 : (s + 1) + t = n) (h2 : s' + t = n)
    (y : Sec (C.X s) U ⊗[ULift.{1} R] Sec (J.X t) U) :
    DirectSum.lof (ULift.{1} R) (Ix n) (Cmp C J U n) ⟨(s + 1, t), h1⟩
        (TensorProduct.map ((C.d s (s + 1)).hom.app (op U)).hom LinearMap.id y) =
      DirectSum.lof (ULift.{1} R) (Ix n) (Cmp C J U n) ⟨(s', t), h2⟩
        (TensorProduct.map ((C.d s s').hom.app (op U)).hom LinearMap.id y) := by
  subst hs; rfl

theorem lof_ne (U : Scheme.{0}) (n : ℤ) (i j : Ix n) (h : i.1.2 ≠ j.1.2) (v : Cmp C J U n i) :
    (DirectSum.lof (ULift.{1} R) (Ix n) (Cmp C J U n) i v) j = 0 := by
  classical
  rw [DirectSum.lof_eq_of]
  exact DirectSum.of_eq_of_ne _ _ _ (fun e => h (by rw [e]))

theorem lof_same (U : Scheme.{0}) (n : ℤ) (i : Ix n) (v : Cmp C J U n i) :
    (DirectSum.lof (ULift.{1} R) (Ix n) (Cmp C J U n) i v) i = v := by
  classical
  rw [DirectSum.lof_eq_of]
  exact DirectSum.of_eq_same _ _

theorem smap_add {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y := map_add _ _ _
theorem smap_sub {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x - y) = Sec.map φ x - Sec.map φ y := map_sub _ _ _
theorem smap_zero {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 := map_zero _
theorem sres_sub {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x - y) = Sec.res g x - Sec.res g y := map_sub _ _ _
theorem sres_zero {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 := map_zero _

def Step : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (τ : Pair C J T), τ.IsTensor → LateralTheory.EtaleFoundations.acyc.ColExact C J →
    ∀ (n t0 : ℤ) (V : Scheme.{0}) (x : Tens C J V n), (∀ p : Ix n, p.1.2 < t0 → x p = 0) →
      Sec.map (T.d n (n + 1)) (τ.lift V n x) = 0 →
      Loc V fun W h => ∃ (x' : Tens C J W n) (Y : Tens C J W (n - 1)),
        (∀ p : Ix n, p.1.2 < t0 + 1 → x' p = 0) ∧ Tens.res h n x = x' + Dm W (n - 1) n (by ring) Y

theorem main (hS : Step) (τ : Pair C J T) (a : ℤ) [C.IsStrictlyGE a] (hτ : τ.IsTensor)
    (hc : LateralTheory.EtaleFoundations.acyc.ColExact C J) (n : ℤ) :
    ∀ k : ℕ, ∀ (V : Scheme.{0}) (x : Tens C J V n), (∀ p : Ix n, p.1.2 < n - a + 1 - k → x p = 0) →
      Sec.map (T.d n (n + 1)) (τ.lift V n x) = 0 →
      Loc V fun W h => ∃ y : Sec (T.X (n - 1)) W, Sec.map (T.d (n - 1) n) y = Sec.res h (τ.lift V n x) := by
  intro k
  induction k with
  | zero =>
    intro V x hx _
    obtain rfl : x = 0 := DFinsupp.ext fun p => by
      by_cases hp : p.1.2 < n - a + 1 - ((0 : ℕ) : ℤ)
      · exact hx p hp
      · exact tens_zero (fun m => sec_zero a (by have := p.2; push_cast at hp; omega) m) (x p)
    exact loc_all fun W h => ⟨0, by rw [smap_zero, map_zero, sres_zero]⟩
  | succ k ih =>
    intro V x hx hd
    refine loc_bind (hS R τ hτ hc n (n - a + 1 - ((k + 1 : ℕ) : ℤ)) V x hx hd) fun W h hW => ?_
    obtain ⟨x', Y, hv, he⟩ := hW
    have hl : τ.lift W n x' = Sec.res h (τ.lift V n x) - Sec.map (T.d (n - 1) n) (τ.lift W (n - 1) Y) := by
      rw [← lift_res, he, map_add (f := _), lift_Dm']; abel
    have hd' : Sec.map (T.d n (n + 1)) (τ.lift W n x') = 0 := by
      rw [hl, smap_sub, map_res, hd, sres_zero, map_dd, sub_zero]
    refine loc_mono (ih W x' (fun p hp => hv p (by push_cast at hp ⊢; omega)) hd') fun W' h' hy => ?_
    obtain ⟨y, hy⟩ := hy
    refine ⟨y + Sec.res h' (τ.lift W (n - 1) Y), ?_⟩
    rw [smap_add, map_res, hy, hl, sres_sub, res_comp]; abel

end LateralTheory.EtaleFoundations.stairPf

open LateralTheory.EtaleFoundations.acyc LateralTheory.EtaleFoundations.stairPf in
theorem LateralTheory.EtaleFoundations.acyc.stair_of (hS : Step) : LateralTheory.EtaleFoundations.acyc.stair := by
  intro R _ C J T a b _ _ τ hτ hc U n z hz
  refine loc_bind (hτ.1 U n z) fun V g hV => ?_
  obtain ⟨x, hx⟩ := hV
  have key := main hS τ a hτ hc n ((n - a + 1 - b).toNat) V x
    (fun p hp => tens_zero' (fun m => sec_zero (C := J) b
      (by have := Int.self_le_toNat (n - a + 1 - b); have := p.2; omega) m) (x p))
    (by rw [hx, map_res, hz, sres_zero])
  exact loc_mono key fun W h hy => by
    obtain ⟨y, hy⟩ := hy
    exact ⟨y, by rw [hy, hx, res_comp]⟩
end
end

-- bundled from Development.EtaleCohomology.TateTwists.TtTensExPfSh
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations

variable {R : Type} [CommRing R]

noncomputable section

abbrev shK {I J : Cx R} (T : TensPre I J) : Cx R :=
  ((presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj T.P

abbrev tS {I J : Cx R} (T : TensPre I J) (U : Scheme.{0}) (w : ℤ) :
    Tens I J U w →ₗ[ULift.{1} R] Sec ((shK T).X w) U :=
  ((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).app (op U)).hom ∘ₗ (T.e U w).toLinearMap

theorem tS_nat {I J : Cx R} (T : TensPre I J) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    Sec.res g (tS T U w x) = tS T V w (Tens.res g w x) := by
  have h1 := ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).naturality g.op) (T.e U w x)
  simp only [ConcreteCategory.comp_apply] at h1
  show Sec.res g (((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).app (op U)).hom (T.e U w x)) =
    ((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).app (op V)).hom (T.e V w (Tens.res g w x))
  rw [T.nat]
  exact h1.symm

theorem tS_d {I J : Cx R} (T : TensPre I J) (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    Sec.map ((shK T).d w (w + 1)) (tS T U w x) =
      ((toSheafify Scheme.etaleTopology.{0} (T.P.X (w + 1))).app (op U)).hom
        (((T.P.d w (w + 1)).app (op U)).hom (T.e U w x)) := by
  simp only [tS, LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact (ConcreteCategory.congr_hom (congrArg (fun f => NatTrans.app f (op U))
    (toSheafify_naturality Scheme.etaleTopology.{0} (T.P.d w (w + 1)))) _).symm

def shPair {I J : Cx R} (T : TensPre I J) : Pair I J (shK T) where
  mul U s t w h := (TensorProduct.mk _ _ _).compr₂ (tS T U w ∘ₗ DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w} (fun p => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(s, t), h⟩)
  nat {V} {U} g s t w h a b := by
    change Sec.res g (tS T U w (DirectSum.of _ ⟨(s, t), h⟩ (a ⊗ₜ b))) =
      tS T V w (DirectSum.of _ ⟨(s, t), h⟩ (Sec.res g a ⊗ₜ Sec.res g b))
    rw [tS_nat, Tens.res, DirectSum.lmap_of, TensorProduct.map_tmul]
  leibniz U s t w h a b := by
    change Sec.map ((shK T).d w (w + 1))
      (tS T U w (DirectSum.of _ ⟨(s, t), h⟩ (a ⊗ₜ b))) = _
    rw [tS_d, T.leibniz]
    simp only [map_add, Units.smul_def, map_zsmul]
    rfl

theorem shPair_lift {I J : Cx R} (T : TensPre I J) (U : Scheme.{0}) (w : ℤ) :
    (shPair T).lift U w = tS T U w := by
  classical
  apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
  simp [Pair.lift, shPair, DirectSum.toModule_lof]

theorem shPair_isTensor {I J : Cx R} (T : TensPre I J) : (shPair T).IsTensor := by
  refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
  · obtain ⟨S, hS, hP⟩ := tt_sheafify_locSurj (T.P.X w) U y
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := hP V g hg
    refine ⟨(T.e V w).symm x, ?_⟩
    rw [shPair_lift]
    show ((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).app (op V)).hom (T.e V w ((T.e V w).symm x)) = _
    rw [LinearEquiv.apply_symm_apply]
    exact hx
  · rw [shPair_lift] at hx
    obtain ⟨S, hS, hP⟩ := tt_sheafify_locInj (T.P.X w) U (T.e U w x) hx
    refine ⟨S, hS, fun V g hg => ?_⟩
    have h2 := hP V g hg
    simp only at h2 ⊢
    rw [← T.nat] at h2
    exact (LinearEquiv.map_eq_zero_iff _).mp h2

theorem etale_presheaf_tensor_data_sheafification_is_tensor_complex : tt_tens_sheafify := fun _ _ _ _ T => ⟨_, shPair T, shPair_isTensor T⟩

end

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.TwpairTensUnivExdegPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ExDeg

variable {R : Type} [CommRing R]

noncomputable def tmap {I J I' J' : Cx R} (f : I ⟶ I') (g : J ⟶ J') (V : Scheme.{0}) (w : ℤ) :
    Tens I J V w →ₗ[ULift.{1} R] Tens I' J' V w :=
  DirectSum.lmap fun p => TensorProduct.map ((f.f p.1.1).hom.app (op V)).hom ((g.f p.1.2).hom.app (op V)).hom

theorem lift_res {I J K : Cx R} (τ : Pair I J K) {V U : Scheme.{0}} (k : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    τ.lift V w (Tens.res k w x) = Sec.res k (τ.lift U w x) := by
  classical
  have key : τ.lift V w ∘ₗ Tens.res k w = ((K.X w).obj.map k.op).hom ∘ₗ τ.lift U w := by
    apply DirectSum.linearMap_ext
    intro p
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, Tens.res, DirectSum.lmap_lof, TensorProduct.map_tmul, Pair.lift,
      DirectSum.toModule_lof, TensorProduct.lift.tmul]
    exact (τ.nat k p.1.1 p.1.2 w p.2 a b).symm
  exact congrArg (fun m => m x) key

theorem lam_res {I J I' J' K : Cx R} (ν : Pair I' J' K) (f : I ⟶ I') (g : J ⟶ J') {V U : Scheme.{0}} (k : V ⟶ U)
    (w : ℤ) (x : Tens I J U w) :
    ν.lift V w (tmap f g V w (Tens.res k w x)) = Sec.res k (ν.lift U w (tmap f g U w x)) := by
  classical
  have key : (ν.lift V w ∘ₗ tmap f g V w) ∘ₗ Tens.res k w =
      ((K.X w).obj.map k.op).hom ∘ₗ (ν.lift U w ∘ₗ tmap f g U w) := by
    apply DirectSum.linearMap_ext
    intro p
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, Tens.res, tmap, DirectSum.lmap_lof, TensorProduct.map_tmul, Pair.lift,
      DirectSum.toModule_lof, TensorProduct.lift.tmul]
    have e := ν.nat k p.1.1 p.1.2 w p.2 (Sec.map (f.f p.1.1) a) (Sec.map (g.f p.1.2) b)
    rw [secmap_res, secmap_res] at e
    exact e.symm
  exact congrArg (fun m => m x) key

theorem lam_zero {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') (V : Scheme.{0}) (w : ℤ) (x : Tens I J V w) (hx : τ.lift V w x = 0) :
    ν.lift V w (tmap f g V w x) = 0 := by
  apply etale_sheaf_sections_separated_holds R (K'.X w) V
  refine TensLocbij.loc_mono (hτ.2 V w x hx) ?_
  intro W k hk
  rw [← lam_res, hk, map_zero, map_zero]
  exact (map_zero _).symm

theorem lam_eq {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') (V : Scheme.{0}) (w : ℤ) (x x' : Tens I J V w) (hx : τ.lift V w x = τ.lift V w x') :
    ν.lift V w (tmap f g V w x) = ν.lift V w (tmap f g V w x') := by
  have := lam_zero τ hτ ν f g V w (x - x') (by rw [map_sub, hx, sub_self])
  rw [map_sub, map_sub, sub_eq_zero] at this
  exact this

end LateralTheory.EtaleFoundations.ExDeg

namespace LateralTheory.EtaleFoundations.ExDeg
variable {R : Type} [CommRing R]

theorem sheafT (F : Shv R) :
    Presieve.IsSheaf Scheme.etaleTopology.{0} (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 (Presheaf.isSheaf_comp_of_isSheaf _ _ _ F.property)

theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res k (Sec.res g y) = Sec.res (k ≫ g) y :=
  (TensLocbij.map_comp_apply' R F.obj k g y).symm

def sv {I J K : Cx R} (τ : Pair I J K) {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) : Sieve U where
  arrows V g := ∃ x, τ.lift V w x = Sec.res g y
  downward_closed := by
    rintro V W g ⟨x, hx⟩ k
    exact ⟨Tens.res k w x, by rw [lift_res, hx, res_comp]⟩

theorem sv_cov {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) :
    sv τ w y ∈ Scheme.etaleTopology.{0} U := by
  obtain ⟨S, hS, hP⟩ := hτ.1 U w y
  exact Scheme.etaleTopology.superset_covering (fun V g hg => hP V g hg) hS

noncomputable def fam {I J K I' J' K' : Cx R} (τ : Pair I J K) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) :
    Presieve.FamilyOfElements ((K'.X w).obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) (sv τ w y).arrows :=
  fun V _ hk => (ν.lift V w (tmap f g V w hk.choose) : Sec (K'.X w) V)

theorem fam_compat {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) :
    (fam τ ν f g w y).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ heq
  show Sec.res g₁ (ν.lift Y₁ w (tmap f g Y₁ w h₁.choose)) = Sec.res g₂ (ν.lift Y₂ w (tmap f g Y₂ w h₂.choose))
  rw [← lam_res, ← lam_res]
  apply lam_eq τ hτ
  rw [lift_res, lift_res, h₁.choose_spec, h₂.choose_spec, res_comp, res_comp, heq]

noncomputable def glue {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) : Sec (K'.X w) U :=
  (sheafT (K'.X w) _ (sv_cov τ hτ w y)).amalgamate _ (fam_compat τ hτ ν f g w y)

theorem glue_spec {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) {V : Scheme.{0}} (k : V ⟶ U)
    (x : Tens I J V w) (hx : τ.lift V w x = Sec.res k y) :
    Sec.res k (glue τ hτ ν f g w y) = ν.lift V w (tmap f g V w x) := by
  have hk : (sv τ w y).arrows k := ⟨x, hx⟩
  have := (sheafT (K'.X w) _ (sv_cov τ hτ w y)).valid_glue (fam_compat τ hτ ν f g w y) k hk
  refine this.trans ?_
  show ν.lift V w (tmap f g V w hk.choose) = _
  exact lam_eq τ hτ ν f g V w _ _ (hk.choose_spec.trans hx.symm)

end LateralTheory.EtaleFoundations.ExDeg

namespace LateralTheory.EtaleFoundations.ExDeg
variable {R : Type} [CommRing R]

theorem sv_loc {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) :
    Loc U fun V k => (sv τ w y).arrows k :=
  ⟨sv τ w y, sv_cov τ hτ w y, fun _ _ h => h⟩

theorem glue_add {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (y₁ y₂ : Sec (K.X w) U) :
    glue τ hτ ν f g w (y₁ + y₂) = glue τ hτ ν f g w y₁ + glue τ hτ ν f g w y₂ := by
  apply etale_sheaf_sections_separated_holds R (K'.X w) U
  refine TensLocbij.loc_mono (TensLocbij.loc_and (sv_loc τ hτ w y₁) (sv_loc τ hτ w y₂)) ?_
  rintro V k ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
  rw [glue_spec τ hτ ν f g w _ k (x₁ + x₂) (by rw [map_add (f := _), hx₁, hx₂]; exact (map_add _ _ _).symm)]
  have e : Sec.res k (glue τ hτ ν f g w y₁ + glue τ hτ ν f g w y₂) =
      Sec.res k (glue τ hτ ν f g w y₁) + Sec.res k (glue τ hτ ν f g w y₂) := map_add _ _ _
  rw [e, glue_spec τ hτ ν f g w _ k x₁ hx₁, glue_spec τ hτ ν f g w _ k x₂ hx₂, map_add (f := _), map_add (f := _)]

theorem glue_smul {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (c : ULift.{1} R) (y : Sec (K.X w) U) :
    glue τ hτ ν f g w (c • y) = c • glue τ hτ ν f g w y := by
  apply etale_sheaf_sections_separated_holds R (K'.X w) U
  refine TensLocbij.loc_mono (sv_loc τ hτ w y) ?_
  rintro V k ⟨x, hx⟩
  rw [glue_spec τ hτ ν f g w _ k (c • x) (by rw [map_smul, hx]; exact (map_smul _ _ _).symm)]
  have e : Sec.res k (c • glue τ hτ ν f g w y) = c • Sec.res k (glue τ hτ ν f g w y) := map_smul _ _ _
  rw [e, glue_spec τ hτ ν f g w _ k x hx, map_smul, map_smul]

theorem glue_res {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U U' : Scheme.{0}} (w : ℤ) (h : U' ⟶ U) (y : Sec (K.X w) U) :
    glue τ hτ ν f g w (Sec.res h y) = Sec.res h (glue τ hτ ν f g w y) := by
  apply etale_sheaf_sections_separated_holds R (K'.X w) U'
  refine TensLocbij.loc_mono (sv_loc τ hτ w (Sec.res h y)) ?_
  rintro _ k ⟨x, hx⟩
  rw [glue_spec τ hτ ν f g w _ k x hx, res_comp]
  rw [res_comp] at hx
  rw [glue_spec τ hτ ν f g w _ (k ≫ h) x hx]

noncomputable def phi {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') (w : ℤ) : K.X w ⟶ K'.X w :=
  ⟨{ app := fun U => ModuleCat.ofHom
        { toFun := fun y => glue τ hτ ν f g w (U := U.unop) y
          map_add' := fun y₁ y₂ => glue_add τ hτ ν f g w y₁ y₂
          map_smul' := fun c y => glue_smul τ hτ ν f g w c y }
     naturality := by
       intro U U' h
       ext y
       exact glue_res τ hτ ν f g w h.unop y }⟩

theorem res_id {F : Shv R} {U : Scheme.{0}} (y : Sec F U) : Sec.res (𝟙 U) y = y := by
  simp [Sec.res]

end LateralTheory.EtaleFoundations.ExDeg

open LateralTheory.EtaleFoundations.ExDeg in
theorem LateralTheory.EtaleFoundations.twpair_tens_univ_exdeg_of : LateralTheory.EtaleFoundations.twpair_tens_univ_exdeg := by
  intro R _ I J K τ hτ I' J' K' ν f g w
  refine ⟨phi τ hτ ν f g w, ?_⟩
  intro U s t h a b
  classical
  have hx : τ.lift U w (DirectSum.lof (ULift.{1} R) _ _ ⟨(s, t), h⟩ (a ⊗ₜ b)) =
      Sec.res (𝟙 U) (τ.mul U s t w h a b) := by
    rw [res_id]
    simp only [Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul]
  have e := glue_spec τ hτ ν f g w _ (𝟙 U) _ hx
  rw [res_id] at e
  refine e.trans ?_
  simp only [tmap, DirectSum.lmap_lof, TensorProduct.map_tmul, Pair.lift, DirectSum.toModule_lof,
    TensorProduct.lift.tmul]
end

